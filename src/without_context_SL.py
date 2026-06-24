from loguru import logger
import time
from cmd_loop import send_reql
from simple_loop import generate_theorem

import argparse
import os
import json
import subprocess

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='AI Mathematician - Theorem Generation and Proof System')
    parser.add_argument('--seed_file', '-s', required=True, help='Path to the initial file')
    parser.add_argument('--save_dir', '-d', required=True, help='Directory to save results')
    parser.add_argument('--prove_iterations', '-p', type=int, default=16, help='Number of proof iterations (default: 16)')
    parser.add_argument('--model', '-pm', default='o3', help='Model to use for proof (default: o3)')
    parser.add_argument('--max_api_usages', '-ma', type=int, default=1000000, help='Max API usages (default: 14000000)')
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
    theorem_count = 0
    all_theorems = []

    # Initialize Lean process
    result = send_reql(content, timeout=args.timeout)
    logger.info(f"result: {result}")
    assert result is not None
    if "messages" in result:
        for message in result["messages"]:
            assert message["severity"] != "error"
    env = result["env"]

    while os.path.exists(f"{args.save_dir}/stats/{i}.json"):
        stats = json.load(open(f"{args.save_dir}/stats/{i}.json", "r", encoding="utf-8"))
        all_api_usages += sum([usage["total_tokens"] for usage in stats["api_usages"]])
        theorem_count += 1
        all_stats.append(json.load(open(f"{args.save_dir}/stats/{i}.json", "r", encoding="utf-8")))
        with open(f"{args.save_dir}/generated/{i}.lean", "r", encoding="utf-8") as f:
            all_theorems.append(f.read().split("\ntheorem")[1])
        assert len(all_theorems) == theorem_count
        i += 1
    
    while all_api_usages < args.max_api_usages:
        success, new_content, _, stats = generate_theorem(
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
        all_api_usages += sum([usage["total_tokens"] for usage in stats["api_usages"]])
        logger.info(f"All API usages: {all_api_usages}")
        all_theorems.append(new_content.split("\ntheorem")[1])
        theorem_count += 1
        i += 1
    
    with open(f"{args.save_dir}/{args.max_api_usages}_theorems.json", "w", encoding="utf-8") as f:
        json.dump(all_theorems, f, indent=2, ensure_ascii=False)
    with open(f"{args.save_dir}/{args.max_api_usages}_stats.json", "w", encoding="utf-8") as f:
        json.dump(all_stats, f, indent=2, ensure_ascii=False)