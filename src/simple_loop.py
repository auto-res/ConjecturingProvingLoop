from loguru import logger
import time
import cmd_loop
from cmd_loop import send_reql, client, WORKDIR, set_stack_size

import argparse
import os
import json
import subprocess

def generate_theorem(content : str, env : int, iterations : int = 16, model : str = "o3") -> tuple[str, int]:
    prompt = "You are a contributor to the mathlib4 library. Based on a given library, please generate a new theorem together with its proof in Lean 4 format. Do not output anything other than the Lean 4 code. The generated code must follow the given library and contain only the theorem statement and its proof. Do not output declarations other than theorem, such as variable, section, or namespace. Do not generate a theorem that already exists in the library. The new theorem should begin with 'theorem' (with no annotations). You may use the theorems in the given library as lemmas in the proof. Do not use 'sorry' in the proof. Additionally, use standard mathematical symbols (e.g., ∀, ∃, √) rather than Unicode escape sequences (e.g., \u2200)."
    ite = 0
    messages=[
        {
            "role": "system",
            "content": prompt,
        },
        {"role": "user", "content": content},
    ]
    times = []
    api_usages = []
    responses = []
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
                theorem = completion.choices[0].message.content
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
        logger.info(f"generated theorem: {theorem}")
        responses.append(theorem)
        retry_count = 0
        max_process_retries = 3
        while True:
            try:
               result = send_reql(theorem, env)
               assert result is not None
               break
            except Exception as e:
                retry_count += 1
                if retry_count > max_process_retries:
                    logger.error(f"Lean process terminated {max_process_retries} times for theorem, skipping this theorem. This may indicate a stack overflow or other critical error.")
                    result = None
                    break
                logger.warning(f"Lean process has terminated (retry {retry_count}/{max_process_retries}), retrying...")
                time.sleep(1)
                if cmd_loop.proc.poll() is None:
                    cmd_loop.proc.terminate()
                cmd_loop.proc = subprocess.Popen(
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
                result = send_reql(content, timeout=1000)
                assert result is not None
                env = result["env"]
                continue
        if result is None:
            response = "The Lean process terminated multiple times when processing this theorem. Please generate a different theorem."
            messages.append({"role": "user", "content": response})
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
            content += '\n\n' + theorem
            return True, content, result["env"], {"times": times,
                                                  "api_usages": api_usages,
                                                  "responses": responses,
                                                  }
        response = "Please fix errors and/or sorries and try again.\n"
        if len(errors) > 0:
            response += f"The following errors occurred: {errors}\n"
        if len(sorries) > 0:
            response += f"The following sorries remain: {sorries}\n"
        messages.append({"role": "user", "content": response})
    return False, content, env, {"times": times, "api_usages": api_usages, "responses": responses}

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='AI Mathematician - Theorem Generation and Proof System')
    parser.add_argument('--seed_file', '-s', required=True, help='Path to the initial file')
    parser.add_argument('--save_dir', '-d', required=True, help='Directory to save results')
    parser.add_argument('--prove_iterations', '-p', type=int, default=16, help='Number of proof iterations (default: 16)')
    parser.add_argument('--model', '-pm', default='o3', help='Model to use for proof (default: o3)')
    parser.add_argument('--max_api_usages', '-ma', type=int, default=14000000, help='Max API usages (default: 14000000)')
    parser.add_argument('--timeout', type=int, default=1000, help='Timeout for Lean process (default: 1000)')
    
    args = parser.parse_args()
    
    # Create save directory
    os.makedirs(args.save_dir, exist_ok=True)
    os.makedirs(f"{args.save_dir}/generated", exist_ok=True)
    os.makedirs(f"{args.save_dir}/stats", exist_ok=True)
    
    # Load initial file
    with open(args.seed_file, "r") as f:
        content = f.read()
    
    # Main loop
    theorem_count = content.count("\ntheorem")
    i = 0
    all_stats = []
    all_api_usages = 0
    while os.path.exists(f"{args.save_dir}/stats/{i}.json"):
        stats = json.load(open(f"{args.save_dir}/stats/{i}.json", "r", encoding="utf-8"))
        all_api_usages += sum([usage["total_tokens"] for usage in stats["api_usages"]])
        theorem_count += 1
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
        success, new_content, env, stats = generate_theorem(
            content,
            env,
            iterations=args.prove_iterations,
            model=args.model
        )
        if success:
            logger.info(f"New theorem discovered")
        else:
            logger.info(f"No new theorem discovered")
        
        stats["success"] = success
        all_stats.append(stats)
        # Save results
        with open(f"{args.save_dir}/generated/{i}.lean", "w", encoding="utf-8") as f:
            f.write(new_content[len(content):])
    
        with open(f"{args.save_dir}/stats/{i}.json", "w", encoding="utf-8") as f:
            json.dump(stats, f, indent=2, ensure_ascii=False)
        
        logger.info(f"Iteration {i} completed")
        content = new_content
        all_api_usages += sum([usage["total_tokens"] for usage in stats["api_usages"]])
        logger.info(f"All API usages: {all_api_usages}")
        theorem_count += 1
        i += 1
    
    with open(f"{args.save_dir}/{args.max_api_usages}_generated.lean", "w", encoding="utf-8") as f:
        f.write(content)
    with open(f"{args.save_dir}/{args.max_api_usages}_stats.json", "w", encoding="utf-8") as f:
        json.dump(all_stats, f, indent=2, ensure_ascii=False)