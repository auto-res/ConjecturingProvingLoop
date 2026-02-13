import sys
import os
import json
import time

from loguru import logger
import subprocess
from pydantic import BaseModel
from openai import OpenAI
import concurrent.futures
import argparse

from cmd_loop import send_reql, prover_loop


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--context_file", type=str, required=True)
    parser.add_argument("--target_file", type=str, required=True)
    parser.add_argument("--output_dir", type=str, required=True)
    parser.add_argument("--max_theorems", type=int, default=100)
    args = parser.parse_args()

    max_theorems = args.max_theorems

    context_file = args.context_file
    target_file = args.target_file
    output_dir = args.output_dir
    os.makedirs(output_dir, exist_ok=True)
    with open(context_file, "r") as f:
        content = f.read()
    context = "theorem".join(content.split("theorem")[:max_theorems+1])
    logger.info(f"context: {context}")
    logger.info(f"context length: {len(context)}")
    exit()
    result = send_reql(content)
    assert result is not None
    if "messages" in result:
        for message in result["messages"]:
            assert message["severity"] != "error"
    env = result["env"]

    with open(target_file, "r") as f:
        target_content = f.read()
    theorems = target_content.split("theorem")[1:max_theorems+1]

    all_stats = []

    for i, theorem in enumerate(theorems):
        # remame theorem name for avoiding conflict
        theorem = theorem.strip()
        theorem_name = theorem.split()[0]
        theorem = 'tmp_theorem' + theorem[len(theorem_name):]

        theorem = 'theorem ' + theorem
        statement = theorem.split(":=")[0] + ":="
        logger.info(f"theorem: {statement}")
        proved, _, _, stats = prover_loop(context, env, statement, 16, "o3")
        if proved:
            logger.info(f"theorem is proved with context")
        else:
            logger.info(f"theorem is not proved with context")
        stats = {
            "statement": statement,
            "proved": proved,
            "stats": stats,
        }
        all_stats.append(stats)
    
    logger.info(f"total {sum([stats['proved'] for stats in all_stats])}/{len(theorems)} theorems are solved")
    with open(f"{output_dir}/all_stats.json", "w", encoding = "utf-8") as f:
        json.dump(all_stats, f, indent=4, ensure_ascii=False)
