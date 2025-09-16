import sys
import argparse
import json
import time

from loguru import logger
import subprocess
from pydantic import BaseModel
from openai import OpenAI
import concurrent.futures

WORKDIR = '/var/mathlib4'
proc = subprocess.Popen(
    ['stdbuf', '-oL', '-eL', '/root/.elan/bin/lake', 'exe', 'repl'],
    cwd=WORKDIR,
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    stderr=subprocess.STDOUT,
    encoding="utf-8",
    text=True,
    bufsize=1,
)

client = OpenAI()

def send_reql(s : str, env = None, timeout = 100.):
    global proc
    req = {"cmd": s}

    if env != None:
        req.update({"env": env})
    
    assert proc.poll() is None
    proc.stdin.write(json.dumps(req)+"\n\n")
    proc.stdin.flush()
    output = ""
    while True:
        if proc.poll() is not None:
            logger.error(f"Lean process has terminated: input: {s}, output: {output}")
            raise Exception("Lean process has terminated")
            return None
        try:
            with concurrent.futures.ThreadPoolExecutor() as executor:
                future = executor.submit(proc.stdout.readline)
                output += future.result(timeout=timeout)
        except concurrent.futures.TimeoutError:
            logger.error(f"Timeout waiting for response to command: {s}")
            raise Exception("Timeout waiting for response to command")
            return None
        try:
            data = json.loads(output)
            logger.info(data)
            return data
        except json.JSONDecodeError:
            continue

def solve_theorems(theorems : list[str], context : str, env : int, iterations : int = 16, model : str = "o3"):
    class Results(BaseModel):
        correctness: bool
        proof: str
        conjectures: list[str]

    prompt = "You are a prover of mathlib4 library. "
    prompt += "Please prove the last theorem in the given content in Lean 4 format. "
    prompt += "If you can prove that the theorem is false, please return False in 'correctness' field. "
    prompt += "Otherwise, if you can prove the theorem, please return True in 'correctness' field and return the proof code in Lean 4 format in 'proof' field. "
    prompt += "The Lean4 code you have to write directly follows \":=\" in the last theorem. "
    prompt += "Thus, it should begin with 'by' or represent a term directly. "
    prompt += "You can use the theorems in the given content as lemmas. "
    prompt += "Do not use sorry in the proof. "
    prompt += "Do not include any other text. "
    prompt += "If you cannot prove the theorem directly, please return True in 'correctness' field and return empty string in 'proof' field and return as many conjectures of lemmas which can be used for the proof as possible in Lean 4 format in 'conjectures' field. "
    prompt += "The conjectures do not need to be definitely true. "
    prompt += "Each conjecture should begin with 'theorem' and end with ':= sorry'. "
    prompt += "Additionally, please use standard mathematical symbols (e.g., ∀, ∃, √) instead of Unicode escape sequences (e.g., \u2200)."

    next_theorems = []
    for theorem in theorems:
        messages = [
            {"role": "system", "content": prompt},
            {"role": "user", "content": context + "\n\n" + theorem},
        ]
        for ite in range(iterations):
            completion = client.beta.chat.completions.parse(
                model=model,
                messages=messages,
                response_format=Results,
            )
            result = completion.choices[0].message.parsed
            if not result.correctness:
                logger.info(f"{theorem} is judged as false by the LLM.")
                break
            elif result.proof != "":
                proof = result.proof
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
                    context += "\n\n" + theorem + proof
                    env = result["env"]
                    break
                messages.append({"role": "assistant", "content": proof})
                response = "Please fix errors and/or sorries and try again.\n"
                if len(errors) > 0:
                    response += f"The following errors occurred: {errors}\n"
                if len(sorries) > 0:
                    response += f"The following sorries remain: {sorries}\n"
                messages.append({"role": "user", "content": response})
            else:
                logger.info(f"{theorem} is judged as true by the LLM.")
                for conjecture in result.conjectures:
                    logger.info(f"{conjecture} is added to the conjectures.")
                    next_theorems.append(conjecture.split(":= sorry")[0] + ":=")
                next_theorems.append(theorem)
    return next_theorems, context, env

def solve_theorem_loop(context : str, theorem : str, iterations : int = 16, model : str = "o3"):
    result = send_reql(context)
    assert result is not None
    if "messages" in result:
        for message in result["messages"]:
            assert message["severity"] != "error"
    env = result["env"]
    theorems = [theorem]
    i = 0
    while theorem in theorems:
        theorems, context, env = solve_theorems(theorems, context, env, iterations, model)
        with open(f"generated_lemmas/context_{i}.lean", "w") as f:
            f.write(context)
        i += 1

def simple_prove(content : str, env : int, theorem : str, iterations : int = 16, model : str = "o3-mini") -> list[str]:
    prompt = "You are a prover of mathlib4 library. Please prove the last theorem in the given content in Lean 4 format. You should write the Lean4 code which directly follows \":=\" in the last theorem. It should begin with 'by' or represent a term directly. You can use the theorems in the given content as lemmas. Do not use sorry in the proof. If you judge that the theorem is not provable, please return empty string instead of the proof. Do not include any other text."
    ite = 0
    messages=[
        {
            "role": "system",
            "content": prompt,
        },
        {"role": "user", "content": content + theorem},
    ]
    while ite < iterations:
        completion = client.beta.chat.completions.parse(
            model=model,
            messages=messages,
        )
        proof = completion.choices[0].message.content
        logger.info(f"generated proof: {theorem + proof}")
        if proof == "":
            logger.info(f"The theorem is judged to be not provable after {ite} iterations")
            return False, ite
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
            content += theorem + proof + "\n\n"
            logger.info(f"The theorem is proved after {ite} iterations")
            return True, ite
        messages.append({"role": "assistant", "content": proof})
        response = "Please fix errors and/or sorries and try again.\n"
        if len(errors) > 0:
            response += f"The following errors occurred: {errors}\n"
        if len(sorries) > 0:
            response += f"The following sorries remain: {sorries}\n"
        messages.append({"role": "user", "content": response})
        ite += 1
    return False, ite

if __name__ == "__main__":
    seed_file = sys.argv[1]
    with open(seed_file, "r") as f:
        content = f.read()
    context = content[:content.rfind("theorem")]
    theorem = "theorem" + content.split("theorem")[-1].split(":= sorry")[0] + ":="
    logger.info(f"context: {context}")
    result = send_reql(context)
    assert result is not None
    if "messages" in result:
        for message in result["messages"]:
            assert message["severity"] != "error"
    env = result["env"]
    logger.info(f"theorem: {theorem}")
    res = []
    for _ in range(16):
        res.append(simple_prove(context, env, theorem, 16, "o3"))
    logger.info(f"total result: {res}")
    print(res)