from loguru import logger
import time
from cmd_loop import send_reql, conjecture_and_prove_theorems

import argparse
import os
import json
import subprocess

if __name__ == "__main__":
    # Parse command line arguments
    parser = argparse.ArgumentParser(description='AI Mathematician - Theorem Generation and Proof System')
    parser.add_argument('--seed_file', '-s', required=True, help='Path to the initial file')
    parser.add_argument('--save_dir', '-d', required=True, help='Directory to save results')
    parser.add_argument('--conjecture_iterations', '-c', type=int, default=1, help='Number of conjecture generation iterations (default: 16)')
    parser.add_argument('--prove_iterations', '-p', type=int, default=16, help='Number of proof iterations (default: 16)')
    parser.add_argument('--conjecture_model', '-cm', default='o3', help='Model to use for conjecture generation (default: o3)')
    parser.add_argument('--prover_model', '-pm', default='o3', help='Model to use for proof (default: o3)')
    parser.add_argument('--max_api_usages', '-ma', type=int, default=1000000, help='Max API usages (default: 14000000)')
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
    theorem_count = 0
    
    # Initialize Lean process
    result = send_reql(content, timeout=args.timeout)
    logger.info(f"result: {result}")
    assert result is not None
    if "messages" in result:
        for message in result["messages"]:
            assert message["severity"] != "error"
    env = result["env"]

    all_theorems = []
    all_stats = []
    all_api_usages = 0
    i = 0

    while os.path.exists(f"{args.save_dir}/stats/{i}.json"):
        stats = json.load(open(f"{args.save_dir}/stats/{i}.json", "r", encoding="utf-8"))
        all_api_usages += sum([usage["api_usage"]["total_tokens"] for usage in stats["conjecture_stats"]])
        all_api_usages += sum([sum([d["total_tokens"] for d in s["api_usages"]]) for s in stats["prove_stats"].values()])
        theorem_count += sum([stats["prove_stats"][theorem]["proved"] for theorem in stats["prove_stats"]])
        all_stats.append(json.load(open(f"{args.save_dir}/stats/{i}.json", "r", encoding="utf-8")))
        with open(f"{args.save_dir}/generated/{i}.lean", "r", encoding="utf-8") as f:
            for theorem in f.read().split("\ntheorem")[1:]:
                all_theorems.append(theorem)
        assert len(all_theorems) == theorem_count
        i += 1



    while all_api_usages < args.max_api_usages:
        conjectures, new_content, _, stats = conjecture_and_prove_theorems(
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
        
        with open(f"{args.save_dir}/stats/{i}.json", "w", encoding="utf-8") as f:
            json.dump(stats, f, indent=2, ensure_ascii=False)
        all_stats.append(stats)
        conjecture_api_usages = sum([usage["api_usage"]["total_tokens"] for usage in stats["conjecture_stats"]])
        prove_api_usages = sum([sum([d["total_tokens"] for d in s["api_usages"]]) for s in stats["prove_stats"].values()])
        all_api_usages += conjecture_api_usages + prove_api_usages
        logger.info(f"All API usages: {all_api_usages}")

        logger.info(f"Iteration {i} completed")
        theorem_count += sum([stats["prove_stats"][theorem]["proved"] for theorem in stats["prove_stats"]])
        for theorem in new_content.split("\ntheorem")[1:]:
            all_theorems.append(theorem)
        assert len(all_theorems) == theorem_count
        logger.info(f"Total theorems: {theorem_count}")
        i += 1
    
    with open(f"{args.save_dir}/{args.max_api_usages}_theorems.json", "w", encoding="utf-8") as f:
        json.dump(all_theorems, f, indent=2, ensure_ascii=False)
    with open(f"{args.save_dir}/{args.max_api_usages}_stats.json", "w", encoding="utf-8") as f:
        json.dump(all_stats, f, indent=2, ensure_ascii=False)