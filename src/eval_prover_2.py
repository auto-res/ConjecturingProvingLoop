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

from cmd_loop import send_reql, client

def judge_and_prove_loop(content : str, env : int, theorem : str, iterations : int = 100, model : str = "o3-mini") -> list[str]:
    prompt = "You are a prover of mathlib4 library. Please prove the last theorem in the given content in Lean 4 format. You should write the Lean4 code which directly follows \":=\" in the last theorem. It should begin with 'by' or represent a term directly. You can use the theorems in the given content as lemmas. Do not use sorry in the proof. If you judge that the theorem is false, please return empty string instead of the proof. Do not include any other text."
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
        max_retries = 3
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
                    retry_delay *= 2
                else:
                    logger.error(f"All retry attempts failed in prover loop")
                    raise e
        if proof == "":
            logger.info("The theorem is judged to be not provable")
            return "Rejected", {"times": times, "api_usages": api_usages}
        else:
            logger.info(f"generated proof: {theorem + proof}")
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
            return "Proved", {"times": times, "api_usages": api_usages}
        messages.append({"role": "assistant", "content": proof})
        response = "Please fix errors and/or sorries and try again.\n"
        if len(errors) > 0:
            response += f"The following errors occurred: {errors}\n"
        if len(sorries) > 0:
            response += f"The following sorries remain: {sorries}\n"
        messages.append({"role": "user", "content": response})
    return "Failed", {"times": times, "api_usages": api_usages}

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--input_file", type=str, default = "./results/with_stats/4ogen/generated_29.lean")
    parser.add_argument("--target_theorem", type=str, default = "intersection_of_alpha_open_sets_is_alpha_open")
    parser.add_argument("--output_dir", type=str, default = "./results/with_stats/4ogen/eval_2_result")
    parser.add_argument("--iterations", type=int, default = 16)
    parser.add_argument("--model", type=str, default = "o3")
    args = parser.parse_args()

    input_file = args.input_file
    output_dir = args.output_dir
    os.makedirs(output_dir, exist_ok=True)
    with open(input_file, "r") as f:
        content = f.read()
    header = content.split("theorem")[0]
    context = content[len(header):].split("theorem " + args.target_theorem)[0]
    statement = "theorem " + args.target_theorem + content[len(header):].split("theorem " + args.target_theorem)[1].split(":=")[0] + ":="

    result = send_reql(header)
    assert result is not None
    if "messages" in result:
        for message in result["messages"]:
            assert message["severity"] != "error"
    head_env = result["env"]

    result = send_reql(context, env = head_env)
    assert result is not None
    if "messages" in result:
        for message in result["messages"]:
            assert message["severity"] != "error"
    context_env = result["env"]

    all_stats = []
    for i in range(args.iterations):
        proved_w, stats_w = judge_and_prove_loop(context, context_env, statement, 16, args.model)
        logger.info(f"proved_w: {proved_w}")
        proved_wo, stats_wo = judge_and_prove_loop(header, head_env, statement, 16, args.model)
        logger.info(f"proved_wo: {proved_wo}")
        all_stats.append(
            {
                "proved_w": proved_w,
                "proved_wo": proved_wo,
                "stats_w": stats_w,
                "stats_wo": stats_wo,
            }
        )

    with open(os.path.join(output_dir, f"stats_{args.model}.json"), "w") as f:
        json.dump(all_stats, f)