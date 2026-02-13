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

from cmd_loop import send_reql, prover_loop, check_validity


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--input_file", type=str, required=True)
    parser.add_argument("--output_dir", type=str, required=True)
    args = parser.parse_args()

    input_file = args.input_file
    output_dir = args.output_dir
    os.makedirs(output_dir, exist_ok=True)
    os.makedirs(os.path.join(output_dir, "reproving_stats"), exist_ok=True)
    with open(input_file, "r") as f:
        content = f.read()
    header = content.split("theorem")[0]
    result = send_reql(header)
    assert result is not None
    if "messages" in result:
        for message in result["messages"]:
            assert message["severity"] != "error"
    head_env = result["env"]

    theorems = content.split("\ntheorem")[1:]
    solved_with_context = []
    solved_without_context = []

    current_env = head_env
    context = header
    logger.info(f"header: {context}")

    all_stats = []

    start_i = 0
    n_theorems = len(theorems)

    while os.path.exists(f"{output_dir}/reproving_stats/fixed_{start_i+10}.json"):
        start_i += 10
        with open(f"{output_dir}/reproving_stats/fixed_{start_i}.json", "r", encoding = "utf-8") as f:
            stats = json.load(f)
            all_stats.extend(stats)

    logger.info(f"start_i: {start_i}")
    logger.info(f"n_theorems: {n_theorems}")

    def find_outer_colon_eq(text):
        depth = 0
        i = 0
        while i < len(text) - 1:
            if text[i] == '(':
                depth += 1
            elif text[i] == ')':
                depth -= 1
            elif text[i] == ':' and text[i+1] == '=' and depth == 0:
                return i
            i += 1
        return -1
    
    for i in range(n_theorems):
        theorem = theorems[i]
        theorem = 'theorem' + theorem
        colon_eq_pos = find_outer_colon_eq(theorem)
        assert colon_eq_pos != -1, f"no := found in {theorem}"
        statement = theorem[:colon_eq_pos] + ":="
        if i < start_i and statement == all_stats[i]["statement"]:
            logger.info(f"theorem is already judged: {statement}")
        else:
            if i < start_i:
                logger.info(f"rejudging theorem: {all_stats[i]['statement']}")
            validity, _ = check_validity(current_env, statement)
            assert validity, f"theorem is invalid: {statement}"
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
            if i < start_i:
                all_stats[i] = stats
            else:
                all_stats.append(stats)
        result = send_reql(theorem, current_env)
        current_env = result["env"]

        context += theorem

        if i % 10 == 9:
            with open(f"{output_dir}/reproving_stats/fixed_{i+1}.json", "w", encoding = "utf-8") as f:
                json.dump(all_stats[-10:], f, indent=4, ensure_ascii=False)
    
    logger.info(f"solved_with_context: {len(solved_with_context)}/{len(theorems)}")
    logger.info(f"solved_without_context: {len(solved_without_context)}/{len(theorems)}")
    with open(f"{output_dir}/all_reproving_stats_fixed.json", "w", encoding = "utf-8") as f:
        json.dump(all_stats, f, indent=4, ensure_ascii=False)
