import sys
import os
import json
import time
import argparse
import resource

from loguru import logger
import subprocess
from pydantic import BaseModel
from openai import OpenAI
import concurrent.futures

def set_stack_size():
    try:
        resource.setrlimit(resource.RLIMIT_STACK, (64 * 1024 * 1024, resource.RLIM_INFINITY))
    except (ValueError, OSError) as e:
        logger.warning(f"Failed to set stack size limit: {e}")
    except AttributeError:
        logger.warning("Stack size limit setting not available on this platform")

WORKDIR = '../mathlib4'
proc = subprocess.Popen(
    ['stdbuf', '-oL', '-eL', '/root/.elan/bin/lake', 'env', '../repl/.lake/build/bin/repl'],
    cwd=WORKDIR,
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    stderr=subprocess.STDOUT,
    encoding="utf-8",
    text=True,
    bufsize=1,
    preexec_fn=set_stack_size,
)

def send_reql(s : str, env = None, timeout = 100.):
    global proc
    req = {"cmd": s}

    if env != None:
        req.update({"env": env})
    
    assert proc.poll() is None
    proc.stdin.write(json.dumps(req)+"\n\n")
    proc.stdin.flush()
    output = ""
    while True:
        if proc.poll() is not None:
            logger.error(f"Lean process has terminated: input: {s}, output: {output}")
            raise Exception("Lean process has terminated")
        try:
            with concurrent.futures.ThreadPoolExecutor() as executor:
                future = executor.submit(proc.stdout.readline)
                output += future.result(timeout=timeout)
        except concurrent.futures.TimeoutError:
            logger.error(f"Timeout waiting for response to command: {s}")
            raise Exception("Timeout waiting for response to command")
        try:
            data = json.loads(output)
            logger.info(data)
            return data
        except json.JSONDecodeError:
            continue

client = OpenAI(
)

def _generate_theorems_by_llm(prompt: str, content: str, model: str = "o3") -> list[str]:
    class Theorems(BaseModel):
        theorems: list[str]

    max_retries = 3
    retry_delay = 2  # 秒
    
    for attempt in range(max_retries):
        try:
            start_time = time.time()
            completion = client.beta.chat.completions.parse(
                model=model,
                messages=[
                    {
                        "role": "system",
                        "content": prompt,
                    },
                    {"role": "user", "content": content},
                ],
                response_format=Theorems,
            )
            used_time = time.time() - start_time
            theorems: Theorems = completion.choices[0].message.parsed
            return theorems.theorems, {"time": used_time,
                                       "api_usage": completion.usage.model_dump(),
                                       }
        except Exception as e:
            logger.warning(f"API call failed (attempt {attempt + 1}/{max_retries}): {e}")
            if attempt < max_retries - 1:
                logger.info(f"Retrying in {retry_delay} seconds...")
                time.sleep(retry_delay)
                retry_delay *= 2
            else:
                logger.error(f"All retry attempts failed for theorem generation")
                raise

def generate_by_notion(content: str, model : str = "o3") -> str:
    #prompt = "You are a writer of mathlib4 library. Please generate conjectures of new theorems in Lean 4 format, which do not need to be definitely true, following a given library. Do not generate statements that are already on the list. Do not include proofs, annotations, or imports. The new theorems begin with 'theorem', not any annotions. They should end with ':= sorry'. Additionally, please use standard mathematical symbols (e.g., ∀, ∃, √) instead of Unicode escape sequences (e.g., \u2200)."
    prompt = "You are a contributor to the mathlib4 library. Based on a given library, please generate conjectural new theorems in Lean 4 format; they do not need to be true. Do not generate statements that already appear in the list. Do not include proofs, annotations, or imports. Each new statement should begin with 'theorem' (with no annotations) and end with ':= sorry'. Additionally, use standard mathematical symbols (e.g., ∀, ∃, √) rather than Unicode escape sequences (e.g., \u2200)."
    theorems, stats = _generate_theorems_by_llm(prompt, content, model)
    return theorems, stats

def check_validity(env, theorem):
    result = send_reql(theorem + " \n  sorry\n\n", env)
    if result is None:
        return False, None
    if "messages" in result:
        for message in result["messages"]:
            if message["severity"] == "error":
                logger.info(f"Validity error: {message}")
                return False, None
    return True, result["env"]

def check_provability(env, theorem):
    result = send_reql(theorem + " by exact?", env)
    if result is None:
        return False
    assert "messages" in result
    for message in result["messages"]:
        if message["severity"] == "error":
            if not message["data"].startswith("`exact?` could not close the goal."):
                logger.error(f"Error: {message['data']}")
            return False
        if message["severity"] == "info" and message["data"].startswith("Try this:"):
            logger.info(f"The conjecture can be proved by {message['data'].split('Try this:')[1].strip()}")
            return True
    assert False

def conjecture_loop(content : str, env : int, iterations : int = 100, model : str = "o3-mini") -> list[str]:
    generated_theorems = []
    stats = []
    for i in range(iterations):
        # Add delay to avoid API rate limits
        if i > 0:
            time.sleep(1)  # Wait 1 second
        theorems, api_stats = generate_by_notion(content, model)
        stats.append(api_stats)
        for theorem in theorems:
            theorem = theorem[:theorem.rfind(":= sorry")] + ":="
            logger.info(f"generated theorem: {theorem}")
            validity, _env = check_validity(env, theorem)
            if not validity:
                logger.info("generated theorem is invalid")
                continue
            provability = check_provability(env, theorem)
            if provability:
                logger.info("generated theorem is provable by exact?")
                continue
            logger.info("generated theorem is valid but not provable by exact?")
            env = _env
            content += theorem + "\n  sorry\n\n"
            generated_theorems.append(theorem)
    return generated_theorems, stats

def prover_loop(content : str, env : int, theorem : str, iterations : int = 100, model : str = "o3-mini") -> list[str]:
    #prompt = "You are a prover of mathlib4 library. Please prove the last theorem in the given content in Lean 4 format. You should write the Lean4 code which directly follows \":=\" in the last theorem. It should begin with 'by' or represent a term directly. You can use the theorems in the given content as lemmas. Do not use sorry in the proof. If you judge that the theorem is not provable, please return empty string instead of the proof. Do not include any other text."
    prompt = "You are a contributor to the mathlib4 library. Please prove the final theorem in the given content using Lean 4. Write the Lean 4 code that directly follows ':=' in the final theorem. The code should either begin with 'by' or be a term expression. You may use the theorems in the given content as lemmas. Do not use 'sorry' in the proof. If you determine that the theorem is not provable, return an empty string instead of a proof. Do not include any additional text."
    ite = 0
    messages=[
        {
            "role": "system",
            "content": prompt,
        },
        {"role": "user", "content": content + theorem},
    ]
    logger.info(f"prover loop: {theorem}")
    times = []
    api_usages = []
    while ite < iterations:
        ite += 1
        
        # Add retry functionality for API calls
        max_retries = 100
        retry_delay = 2
        
        for attempt in range(max_retries):
            try:
                start_time = time.time()
                completion = client.beta.chat.completions.parse(
                    model=model,
                    messages=messages,
                )
                proof = completion.choices[0].message.content
                used_time = time.time() - start_time
                times.append(used_time)
                api_usages.append(completion.usage.model_dump())
                break  # Exit loop on success
            except Exception as e:
                logger.warning(f"API call failed in prover loop (attempt {attempt + 1}/{max_retries}): {e}")
                if attempt < max_retries - 1:
                    logger.info(f"Retrying in {retry_delay} seconds...")
                    time.sleep(retry_delay)
                    retry_delay += 2
                else:
                    logger.error(f"All retry attempts failed in prover loop")
                    raise e
        if proof == "":
            logger.info("The theorem is judged to be not provable")
            return False, None, None, {"times": times,
                                       "api_usages": api_usages,
                                       }
        logger.info(f"generated proof: {theorem + proof}")
        result = send_reql(theorem + proof, env)
        if result is None:
            continue
        if "messages" in result:
            errors = [message for message in result["messages"] if message["severity"] == "error"]
        else:
            errors = []
        if "sorries" in result:
            sorries = result["sorries"]
        else:
            sorries = []
        if len(errors) == 0 and len(sorries) == 0:
            content += '\n\n' + theorem + ' ' + proof
            return True, content, result["env"], {"times": times,
                                                  "api_usages": api_usages,
                                                  }
        messages.append({"role": "assistant", "content": proof})
        response = "Please fix errors and/or sorries and try again.\n"
        if len(errors) > 0:
            response += f"The following errors occurred: {errors}\n"
        if len(sorries) > 0:
            response += f"The following sorries remain: {sorries}\n"
        messages.append({"role": "user", "content": response})
    return False, None, None, {"times": times,
                               "api_usages": api_usages,
                               }

def prove_theorems(
        content : str,
    env : int,
    theorems : list[str],
    iterations : int = 100,
    model : str = "o3-mini") -> tuple[str, int]:
    stats = {}
    for theorem in theorems:
        proved, _content, _env, api_stats = prover_loop(content, env, theorem, iterations, model)
        api_stats["proved"] = proved
        stats[theorem] = api_stats
        if proved:
            logger.info(f"proved theorem: {theorem}")
            content = _content
            env = _env
        else:
            logger.info(f"failed to prove theorem: {theorem}")
    return content, env, stats

def conjecture_and_prove_theorems(
    content : str,
    env : int,
    conjecture_iterations : int = 16,
    prove_iterations : int = 16,
    conjecture_model : str = "o3",
    prover_model : str = "o3",
    ) -> tuple[str, int]:
    theorems, conjecture_stats = conjecture_loop(content, env, iterations = conjecture_iterations, model = conjecture_model)
    content, env, prove_stats = prove_theorems(content, env, theorems, prove_iterations, prover_model)
    return theorems, content, env, {"conjecture_stats": conjecture_stats,
                                   "prove_stats": prove_stats,
                                   }

if __name__ == "__main__":
    # Parse command line arguments
    parser = argparse.ArgumentParser(description='AI Mathematician - Theorem Generation and Proof System')
    parser.add_argument('--seed_file', '-s', required=True, help='Path to the initial file')
    parser.add_argument('--save_dir', '-d', required=True, help='Directory to save results')
    parser.add_argument('--conjecture_iterations', '-c', type=int, default=1, help='Number of conjecture generation iterations (default: 16)')
    parser.add_argument('--prove_iterations', '-p', type=int, default=16, help='Number of proof iterations (default: 16)')
    parser.add_argument('--conjecture_model', '-cm', default='o3', help='Model to use for conjecture generation (default: o3)')
    parser.add_argument('--prover_model', '-pm', default='o3', help='Model to use for proof (default: o3)')
    parser.add_argument('--max_api_usages', '-ma', type=int, default=14000000, help='Max API usages (default: 14000000)')
    parser.add_argument('--timeout', '-t', type=float, default=1000.0, help='Timeout for Lean process (default: 1000.0)')
    
    args = parser.parse_args()
    
    # Create save directory
    os.makedirs(args.save_dir, exist_ok=True)
    os.makedirs(f"{args.save_dir}/conjectures", exist_ok=True)
    os.makedirs(f"{args.save_dir}/generated", exist_ok=True)
    os.makedirs(f"{args.save_dir}/stats", exist_ok=True)
    
    # Load initial file
    with open(args.seed_file, "r") as f:
        content = f.read()
    
    theorem_count = content.count("\ntheorem")
    # Main loop
    i=0
    all_api_usages = 0
    all_stats = []
    while os.path.exists(f"{args.save_dir}/stats/{i}.json"):
        stats = json.load(open(f"{args.save_dir}/stats/{i}.json", "r", encoding="utf-8"))
        all_api_usages += sum([usage["api_usage"]["total_tokens"] for usage in stats["conjecture_stats"]])
        all_api_usages += sum([sum([d["total_tokens"] for d in s["api_usages"]]) for s in stats["prove_stats"].values()])
        theorem_count += sum([stats["prove_stats"][theorem]["proved"] for theorem in stats["prove_stats"]])
        all_stats.append(json.load(open(f"{args.save_dir}/stats/{i}.json", "r", encoding="utf-8")))
        with open(f"{args.save_dir}/generated/{i}.lean", "r", encoding="utf-8") as f:
            generated_content = f.read()
            content += generated_content

        i += 1
    logger.info(f"content: {content}")
    logger.info(f"theorem_count: {theorem_count}")
    logger.info(f"all_api_usages: {all_api_usages}")
    logger.info(f"start iteration: {i}")
    
    # Initialize Lean process
    result = send_reql(content, timeout=args.timeout)
    logger.info(f"result: {result}")
    assert result is not None
    if "messages" in result:
        for message in result["messages"]:
            assert message["severity"] != "error"
    env = result["env"]
    
    while all_api_usages < args.max_api_usages:
        conjectures, new_content, env, stats = conjecture_and_prove_theorems(
            content,
            env,
            conjecture_iterations=args.conjecture_iterations,
            prove_iterations=args.prove_iterations,
            conjecture_model=args.conjecture_model,
            prover_model=args.prover_model
        )        
        # Save results
        with open(f"{args.save_dir}/conjectures/{i}.txt", "w", encoding="utf-8") as f:
            for conjecture in conjectures:
                f.write(conjecture + "\n")
        
        with open(f"{args.save_dir}/generated/{i}.lean", "w", encoding="utf-8") as f:
            f.write(new_content[len(content):])
        content = new_content
        
        with open(f"{args.save_dir}/stats/{i}.json", "w", encoding="utf-8") as f:
            json.dump(stats, f, indent=2, ensure_ascii=False)
        all_stats.append(stats)
        conjecture_api_usages = sum([usage["api_usage"]["total_tokens"] for usage in stats["conjecture_stats"]])
        prove_api_usages = sum([sum([d["total_tokens"] for d in s["api_usages"]]) for s in stats["prove_stats"].values()])
        all_api_usages += conjecture_api_usages + prove_api_usages
        logger.info(f"All API usages: {all_api_usages}")

        logger.info(f"Iteration {i} completed")
        theorem_count += sum([stats["prove_stats"][theorem]["proved"] for theorem in stats["prove_stats"]])
        logger.info(f"Total theorems: {theorem_count}")
        i += 1
    
    with open(f"{args.save_dir}/{args.max_api_usages}_generated.lean", "w", encoding="utf-8") as f:
        f.write(content)
    with open(f"{args.save_dir}/{args.max_api_usages}_stats.json", "w", encoding="utf-8") as f:
        json.dump(all_stats, f, indent=2, ensure_ascii=False)