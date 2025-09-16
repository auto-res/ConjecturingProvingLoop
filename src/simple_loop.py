from loguru import logger
import time
from cmd_loop import send_reql, client, proc, WORKDIR

import argparse
import os
import json
import subprocess

def generate_theorem(content : str, env : int, iterations : int = 16, model : str = "o3") -> tuple[str, int]:
    prompt = (
        "Your are a writer of mathlib4 library. "
        "Please generate a new theorem with a proof in Lean 4 format, following a given library. "
        "Do not return anything else than the Lean 4 code. "
        "The generated code should follow the given library. "
        "The generated code should contain only the theorem and the proof. "
        "Do not generate a theorem that are already on the library. "
        "The new theorem should begin with 'theorem', not any annotions. "
        "You can use the theorems in the given library as lemmas in the proof. "
        "Do not use sorry in the proof. "
        "Additionally, please use standard mathematical symbols (e.g., ∀, ∃, √) instead of Unicode escape sequences (e.g., \u2200).\n\n"
    )
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
        max_retries = 3
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
                    retry_delay *= 2
                else:
                    logger.error(f"All retry attempts failed in prover loop")
                    raise e
        logger.info(f"generated theorem: {theorem}")
        responses.append(theorem)
        while True:
            try:
               result = send_reql(theorem, env)
               assert result is not None
               break
            except Exception as e:
                logger.warning(f"Lean process has terminated, retrying...")
                time.sleep(1)
                global proc
                proc.terminate()
                proc = subprocess.Popen(
                    ['stdbuf', '-oL', '-eL', '/root/.elan/bin/lake', 'env', '../repl/.lake/build/bin/repl'],
                    cwd=WORKDIR,
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    encoding="utf-8",
                    text=True,
                    bufsize=1,
                )
                result = send_reql(content, timeout=1000)
                assert result is not None
                env = result["env"]
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
    parser.add_argument('--start_iteration', '-i', type=int, default=0, help='Starting iteration number (default: 0)')
    parser.add_argument('--prover_iterations', '-p', type=int, default=16, help='Number of proof iterations (default: 16)')
    parser.add_argument('--num_loops', '-n', type=int, default=400, help='Number of main loops (default: 30)')
    parser.add_argument('--model', '-pm', default='o3', help='Model to use for proof (default: o3)')
    parser.add_argument('--save_interval', type=int, default=10, help='Interval to save results (default: 10)')
    parser.add_argument('--timeout', type=int, default=1000, help='Timeout for Lean process (default: 1000)')
    
    args = parser.parse_args()
    
    # Create save directory
    os.makedirs(args.save_dir, exist_ok=True)
    
    # Load initial file
    with open(args.seed_file, "r") as f:
        content = f.read()
    
    # Initialize Lean process
    result = send_reql(content, timeout=args.timeout)
    assert result is not None
    if "messages" in result:
        for message in result["messages"]:
            assert message["severity"] != "error"
    env = result["env"]

    # Main loop
    for i in range(args.num_loops):
        success, content, env, stats = generate_theorem(
            content,
            env,
            iterations=args.prover_iterations,
            model=args.model
        )
        if success:
            logger.info(f"New theorem discovered")
        else:
            logger.info(f"No new theorem discovered")
        
        stats["success"] = success

        # Save results
        if (args.start_iteration+i) % args.save_interval == 0:
            with open(f"{args.save_dir}/generated_{args.start_iteration+i}.lean", "w", encoding="utf-8") as f:
                f.write(content)
        
            with open(f"{args.save_dir}/stats_{args.start_iteration+i}.json", "w", encoding="utf-8") as f:
                json.dump(stats, f, indent=2, ensure_ascii=False)
        
        logger.info(f"Iteration {args.start_iteration+i} completed")
    
    with open(f"{args.save_dir}/final_generated.lean", "w", encoding="utf-8") as f:
        f.write(content)
    with open(f"{args.save_dir}/final_stats.json", "w", encoding="utf-8") as f:
        json.dump(stats, f, indent=2, ensure_ascii=False)