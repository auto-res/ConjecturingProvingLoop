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
    parser.add_argument("--input_file", type=str, required=True)
    parser.add_argument("--output_dir", type=str, required=True)
    args = parser.parse_args()

    input_file = args.input_file
    output_dir = args.output_dir
    os.makedirs(output_dir, exist_ok=True)
    with open(input_file, "r") as f:
        content = f.read()
    header = content.split("theorem")[0]
    result = send_reql(header)
    assert result is not None
    if "messages" in result:
        for message in result["messages"]:
            assert message["severity"] != "error"
    head_env = result["env"]

    theorems = content.split("theorem")[1:]
    solved_with_context = []
    solved_without_context = []

    current_env = head_env
    context = header

    all_stats = []

    for i, theorem in enumerate(theorems):
        theorem = 'theorem' + theorem
        statement = theorem.split(":=")[0] + ":="
        logger.info(f"theorem: {statement}")
        proved_w, _, _, stats_w = prover_loop(context, current_env, statement, 16, "o3")
        if proved_w:
            solved_with_context.append(statement)
            logger.info(f"theorem is proved with context")
        else:
            logger.info(f"theorem is not proved with context")
        proved_wo, _, _, stats_wo = prover_loop(header, head_env, statement, 16, "o3")
        if proved_wo:
            solved_without_context.append(statement)
            logger.info(f"theorem is proved without context")
        else:
            logger.info(f"theorem is not proved without context")
        stats = {
            "statement": statement,
            "proved_with_context": proved_w,
            "proved_without_context": proved_wo,
            "stats_with_context": stats_w,
            "stats_without_context": stats_wo,
        }
        all_stats.append(stats)
        result = send_reql(theorem, current_env)
        current_env = result["env"]

        context += theorem

        if i % 10 == 0:
            logger.info(f"save all_stats_{i+1}.json")
            with open(f"{output_dir}/all_stats_{i+1}.json", "w", encoding = "utf-8") as f:
                json.dump(all_stats, f, indent=4, ensure_ascii=False)
    
    logger.info(f"solved_with_context: {len(solved_with_context)}")
    logger.info(f"solved_without_context: {len(solved_without_context)}")
    with open(f"{output_dir}/all_stats.json", "w", encoding = "utf-8") as f:
        json.dump(all_stats, f, indent=4, ensure_ascii=False)
