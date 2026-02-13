import sys
import os
import json
import time
import argparse

from loguru import logger

from cmd_loop import send_reql, prover_loop

def check_provability_modified(env, theorem, timeout=2000.):
    result = send_reql(theorem + " by exact?", env, timeout=2000.)
    if result is None:
        return False
    assert "messages" in result
    for message in result["messages"]:
        if message["severity"] == "error":
            if message["data"].startswith("found a proof, but the corresponding tactic failed:"):
                return True
            if not message["data"].startswith("`exact?` could not close the goal."):
                logger.error(f"Error: {message['data']}")
            return False
        if message["severity"] == "info" and message["data"].startswith("Try this:"):
            logger.info(f"The conjecture can be proved by {message['data'].split('Try this:')[1].strip()}")
            return True
    assert False


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed_file", type=str, required=True)
    parser.add_argument("--input_dir", type=str, required=True)
    parser.add_argument("--benchmark_file", type=str, required=True)
    parser.add_argument("--max_api_usages", type=int, default=14000000)
    parser.add_argument("--output_file", type=str, default="")
    parser.add_argument("--eval_mode", type=str, default="exact", choices=["exact", "IC", "conjecture"])

    args = parser.parse_args()

    with open(args.seed_file, "r") as f:
        content = f.read()

    api_usages = 0
    i=0
    while os.path.exists(os.path.join(args.input_dir, f"generated/{i}.lean")):
        if args.eval_mode == "conjecture":
            with open(os.path.join(args.input_dir, f"conjectures/{i}.txt"), "r") as f:
                conjecutures = f.read()
                for conjecture in conjecutures.split("theorem")[1:]:
                    conjecture = conjecture.strip()
                    conjecture_name = conjecture.split()[0]
                    tmp_name = f"conjecuture_{i}_{conjecture_name}" 
                    conjecture = "\ntheorem " + tmp_name + conjecture[len(conjecture_name):] + " sorry\n"
                    content += conjecture
            i += 1
            continue
        with open(os.path.join(args.input_dir, f"generated/{i}.lean"), "r") as f, \
             open(os.path.join(args.input_dir, f"stats/{i}.json"), "r") as stat:
            stats = json.load(stat)
            if "conjecture_stats" in stats:
                api_usages += sum([usage["api_usage"]["total_tokens"] for usage in stats["conjecture_stats"]])
                api_usages += sum([sum([d["total_tokens"] for d in s["api_usages"]]) for s in stats["prove_stats"].values()])
            else:
                api_usages += sum([usage["total_tokens"] for usage in stats["api_usages"]])
            if api_usages > args.max_api_usages:
                logger.info(f"api usages exceeded: {api_usages}")
                break
            content += f.read()
        i += 1
    if api_usages <= args.max_api_usages:
        logger.info(f"api usages: {api_usages}")
    count = content.count('\ntheorem ')
    logger.info(f"total theorems: {count}")
    
    with open(args.benchmark_file, "r") as f:
        benchmark = f.read()
    theorems = benchmark.split("theorem")[1:]

    #content += "\n\nset_option maxHeartbeats 2000000\n"

    result = send_reql(content, timeout=2000.)
    assert result is not None
    if "messages" in result:
        for message in result["messages"]:
            assert message["severity"] != "error", f"Lean error: {message}"
    env = result["env"]

    solved = {}
    for theorem in theorems:
        theorem = theorem.strip()
        theorem_name = theorem.split()[0]
        theorem = 'tmp_theorem' + theorem[len(theorem_name):]
        theorem = 'theorem ' + theorem
        theorem = theorem.split(":=")[0] + ":="
        if args.eval_mode == "exact" or args.eval_mode == "conjecture":
          result = check_provability_modified(env, theorem, timeout=2000.)
        else:
            result, _, _, _ = prover_loop(content, env, theorem, 16, "o3")
        if result:
            solved[theorem] = True
            logger.info(f"theorem is proved: {theorem}")
        else:
            solved[theorem] = False
            logger.info(f"theorem is not proved: {theorem}")
    if args.output_file != "":
        with open(args.output_file, "w") as f:
            json.dump(solved, f, indent=4, ensure_ascii=False)
    else:
        logger.info(json.dumps(solved, indent=4, ensure_ascii=False))
        print(json.dumps(solved, indent=4, ensure_ascii=False))
    logger.info(f"solved: {sum(solved.values())}/{len(theorems)}")
