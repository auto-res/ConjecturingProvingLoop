import json

import logging, os

logger = logging.getLogger(__name__)

def find_assign_outside_parens(text):
    depth = 0
    i = 0
    while i < len(text):
        if text[i] == '(':
            depth += 1
            i += 1
        elif text[i] == ')':
            depth = max(0, depth - 1)
            i += 1
        elif depth == 0 and text[i:i+2] == ':=':
            return i
        else:
            i += 1
    return -1

def count_proof_lengths(dir_path, max_api_usages = 14000000):
    api_usages = 0
    i=0
    content = ""
    while os.path.exists(os.path.join(dir_path, f"generated/{i}.lean")):
        with open(os.path.join(dir_path, f"generated/{i}.lean"), "r") as f, \
             open(os.path.join(dir_path, f"stats/{i}.json"), "r") as stat:
            stats = json.load(stat)
            if "conjecture_stats" in stats:
                api_usages += sum([usage["api_usage"]["total_tokens"] for usage in stats["conjecture_stats"]])
                api_usages += sum([sum([d["total_tokens"] for d in s["api_usages"]]) for s in stats["prove_stats"].values()])
            else:
                api_usages += sum([usage["total_tokens"] for usage in stats["api_usages"]])
            if api_usages > max_api_usages:
                logger.info(f"api usages exceeded: {api_usages}")
                break
            content += f.read()
        i += 1
    if api_usages <= max_api_usages:
        logger.info(f"api usages: {api_usages}")
    count = content.count('\ntheorem ')
    logger.info(f"total theorems: {count}")
    proof_lengths = []
    for theorem in content.split("theorem")[1:]:
        assign_idx = find_assign_outside_parens(theorem)
        proof = theorem[assign_idx:].strip() if assign_idx != -1 else ""
        proof_lengths.append(len(proof))
    return proof_lengths

if __name__ == "__main__":
    CPL_dir = "results/P/CPL/"
    SL_dir = "results/P/SL/"

    nseeds = 20

    CPL_proof_lengths = []
    SL_proof_lengths = []
    for seed in range(nseeds):
        CPL_proof_lengths.extend(count_proof_lengths(os.path.join(CPL_dir, str(seed))))
        SL_proof_lengths.extend(count_proof_lengths(os.path.join(SL_dir, str(seed))))

    with open("results/proof_lengths.json", "w") as f:
        json.dump({"CPL": CPL_proof_lengths, "SL": SL_proof_lengths}, f)

    print(f"CPL: {len(CPL_proof_lengths) / nseeds}, SL: {len(SL_proof_lengths) / nseeds}")

