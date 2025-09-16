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

from cmd_loop import client

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output_dir", type=str, default = "./results/eval_NL_result")
    parser.add_argument("--iterations", type=int, default = 16)
    parser.add_argument("--model", type=str, default = "o3")
    args = parser.parse_args()

    output_dir = args.output_dir
    os.makedirs(os.path.join(output_dir, f"proofs_{args.model}"), exist_ok=True)

    all_stats = []
    prompt = "Please prove the following theorem. If you judge that the theorem is false, please return \"False\" instead of the proof."
    content = "In a topological space, a set is alpha-open if it is a subset of the interior of the closure of its interior. The intersection of any two alpha-open sets is alpha-open."
    messages=[
        {
            "role": "system",
            "content": prompt,
        },
        {"role": "user", "content": content},
    ]
    for i in range(args.iterations):
        response = client.beta.chat.completions.parse(
            model=args.model,
            messages=messages,
        )
        proof = response.choices[0].message.content
        logger.info(f"proof: {proof}")
        with open(os.path.join(output_dir, f"proofs_{args.model}", f"proof_{i}.txt"), "w") as f:
            f.write(proof)
        all_stats.append(
            {
                "proof": proof,
                "api_usage": response.usage.model_dump(),
            }
        )


    with open(os.path.join(output_dir, f"stats_{args.model}.json"), "w") as f:
        json.dump(all_stats, f)