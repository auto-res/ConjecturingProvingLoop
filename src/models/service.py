import os
import re
import json
from datetime import datetime
import subprocess
import collections
import uuid

import requests
from loguru import logger
from openai import OpenAI
from pydantic import BaseModel

from .entity import Conjecture, Seed, ConjectureEvalResult


GRAPH_FILE_PATH = "./import_graph.dot"

def _get_temp_file_path() -> str:
    """実行ごとに一意のファイルパスを生成する"""
    return f"/data/Verify_{uuid.uuid4().hex[:8]}.lean"

def get_seeds(src_seed: Seed) -> list[Seed]:
    """Perform BFS to find the shortest path from src_seed to all reachable nodes.
    input: src_seed: Seed
    return: dict of {seed: distance} where distance is the shortest path from src_seed to seed
    """
    distances: dict[Seed, int] = collections.defaultdict(
        lambda: -1
    )  # Default distance is -1
    queue = collections.deque([(src_seed, 0)])  # Queue of (node, distance)
    distances[src_seed] = 0  # Distance to itself is 0

    def _parse_dot_file() -> dict:
        """Parse the .dot file to create a graph in adjacency list format."""
        graph = collections.defaultdict(list)
        with open(GRAPH_FILE_PATH, "r") as file:
            for line in file:
                if "->" in line:
                    # Remove unnecessary characters and split by '->' to extract nodes
                    target, source = line.strip().replace(";", "").split("->")
                    source = source.strip().strip('"')
                    target = target.strip().strip('"')
                    graph[Seed(pp=source)].append(Seed(pp=target))
        return graph
    graph = _parse_dot_file()

    while queue:
        node, distance = queue.popleft()
        for neighbor in graph[node]:
            if distances[neighbor] == -1:  # Only visit unvisited nodes
                distances[neighbor] = distance + 1
                queue.append((neighbor, distance + 1))

    return [s for s in distances.keys()]

def get_file_paths(directory='/var/mathlib4/Mathlib') -> list[Seed]:
    file_paths = []
    for root, _, files in os.walk(directory):

        for file in files:
            file_paths.append(os.path.join(root, file))

    def parse_seed(file_path: str) -> Seed:
        pp = file_path.replace('/var/mathlib4/', '').replace('.lean', '').replace('/', '.')
        return Seed(pp=pp)

    return [parse_seed(file_path) for file_path in file_paths]

def _is_generated_seed(seed: Seed) -> bool:
    return re.match(r"^Mathlib.A\d+", seed.pp) is not None

def get_generated_seeds() -> list[Seed]:
    return list(filter(_is_generated_seed, get_file_paths()))

def _make_header(context: str, namespace: str) -> str:
    return "\n\n".join(["import Mathlib\nimport Aesop", namespace, context]) + "\n\n"

def parse_conjecture(conj_id: str, header: str, conjecture_str: str, skip_check: bool = False) -> Conjecture | None:
    try:
        conjecture_str = conjecture_str.strip()
        conjecture_str = "theorem" + re.split(r"(theorem|lemma)", conjecture_str)[2]
    
    except Exception as e:
        logger.warning(f"Invalid statement is generated: {e}")
        logger.warning(f"Generated statement: {conjecture_str}")
        return None

    # rename the theorem so that it is unique
    # returns the renamed theorem and the theorem name
    def rename(conjecture : str) -> tuple[str, str]:
        dot_split_theorem = conjecture.split("theorem ")[1].split(" ")[0].split(".")
        if dot_split_theorem[-1].startswith("{"):
            theorem_name = ".".join(dot_split_theorem[:-1])
        else:
            theorem_name = ".".join(dot_split_theorem) 

        return ("theorem " + theorem_name + " " + " ".join(conjecture.split()[2:])), theorem_name
    
    conjecture_str, theorem_name = rename(conjecture_str)

    content = "\n\n".join(
        [
            header,
            conjecture_str.split(":=")[0] + ":= by sorry",
            "#print " + theorem_name + "\n"
        ]
    )

    if skip_check:
        return Conjecture(
            conjecture_id=conj_id,
            header=header,
            name=theorem_name,
            statement=conjecture_str.split(":=")[0] + ":= by",
            grammatical=True,
        )

    logger.info(conjecture_str)
    # logger.debug(f"Transforming conjecture with Lean format:\n{content}")
    temp_file_path = _get_temp_file_path()
    with open(temp_file_path, "w") as f:
        f.write(content)

    command = f'echo \'{{"path": "{temp_file_path}", "allTactics": true}}\' | /root/.elan/bin/lake exe repl'
    work_dir = "/var/mathlib4"
    result = subprocess.run(command, cwd=work_dir, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    
    # 一時ファイルを削除
    try:
        os.remove(temp_file_path)
    except FileNotFoundError:
        pass  # ファイルが既に削除されている場合は無視
    
    if result.returncode != 0:
        raise ValueError("Verification failed.")

    verification_result = json.loads(result.stdout)

    # Print verification result
    logger.debug(f"Verification result")
    if "tactics" in verification_result:
        logger.debug(f"tactics:")
        for tactic in verification_result["tactics"]:
            logger.debug(f"\n{tactic}")
    if "sorries" in verification_result:
        logger.debug(f"sorries:")
        for sorry in verification_result["sorries"]:
            logger.debug(f"\n{sorry}")
    if "messages" in verification_result:
        logger.debug(f"messages:")
        for message in verification_result["messages"]:
            logger.debug(f"\n{message}")

    for message in verification_result["messages"]:
        if message["severity"] == "error":
            statement = conjecture_str.split(":=")[0] + ":= by"
            logger.info(f"not grammatical statement generated: {statement}")
            return Conjecture(
                conjecture_id=conj_id,
                header=header,
                name=theorem_name,
                statement=statement,
                grammatical=False
            )

    for message in reversed(verification_result["messages"]):
        if message["severity"] == "info" and message["data"].startswith("theorem "):
            #statement = message["data"].split(":=")[0] + ":= by"
            #statement = rename(statement)[0]
            statement = conjecture_str.split(":=")[0] + ":= by"
            if "sorry" not in statement and "sorries" in verification_result:
                logger.info(f"grammatical statement generated: {statement}")
                conjecture = Conjecture(
                    conjecture_id=conj_id,
                    header=header,
                    name=theorem_name,
                    statement=statement,
                    grammatical=True,
                    goal=verification_result["sorries"][0]["goal"]
                )
                if _is_valid(conjecture):
                    return conjecture
                else:
                    return Conjecture(
                        conjecture_id=conj_id,
                        header=header,
                        name=theorem_name,
                        statement=conjecture_str.split(":=")[0] + ":= by",
                        grammatical=True,
                        goal=verification_result["sorries"][0]["goal"]
                    )
                    
    statement = conjecture_str.split(":=")[0] + ":= by"
    logger.info(f"not grammatical statement generated: {statement}")
    return Conjecture(
        conjecture_id=conj_id,
        header=header,
        name=theorem_name,
        statement=statement,
        grammatical=False
    )


class ConjectureGenerator(object):
    def __init__(self):
        self.client = OpenAI()

    def generate(self, notion_file_path: str) -> list[ConjectureEvalResult]:
        with open(notion_file_path, "r") as f:
            notion = f.read()
        

        prompt = 'Please generate new theorems in Lean 4 format with a given notion. Do not include proofs, annotations, or imports. The new theorems begin with "theorem", not any annotions. They should end with ":= by". Additionally, please use standard mathematical symbols (e.g., ∀, ∃, √) instead of Unicode escape sequences (e.g., \u2200).'
            
        theorems = self._generate_theorems_by_llm(prompt, notion)
        return _parse_eval_results(theorems, notion + "\n\n")

    def generated_by_idea_and_file(self, idea: str, seed: Seed) -> list[ConjectureEvalResult]:
        prompt = "Please generate new theorems in Lean 4 format with a given idea and a relevant Lean4 file. Do not include proofs, annotations, or imports. The new theorems begin with 'theorem', not any annotions. They should end with ':= by'. Additionally, please use standard mathematical symbols (e.g., ∀, ∃, √) instead of Unicode escape sequences (e.g., \u2200).\n\n"
        prompt += f"## Idea:\n{idea}\n\n"
        prompt += "## Lean4 file:\n\n"
        try:
            with open(seed.path, "r") as f:
                content= f.read()
            prompt += content
        except FileNotFoundError:
            logger.warning(f"File not found: {seed.path}")
            return []
        
        theorems = self._generate_theorems_by_llm(prompt, "")
        header = _get_header(content)
        return _parse_eval_results(theorems, header)

    def generate_by_notion(self, notion_file_path: str, use_get_header : bool = False) -> list[ConjectureEvalResult]:
        if use_get_header:
            prompt = "Your are a writer of excercise propositions in Lean4. Please generate new theorems in Lean 4 format, following a given list of statements. Do not generate statements that are already on the list. Do not include proofs, annotations, or imports. The new theorems begin with 'theorem', not any annotions. They should end with ':= by'. Additionally, please use standard mathematical symbols (e.g., ∀, ∃, √) instead of Unicode escape sequences (e.g., \u2200).\n\n"
        else:
            prompt = "Your are a writer of mathlib4 library. Please generate new theorems in Lean 4 format, following a given library. Do not include proofs, annotations, or imports. The new theorems begin with 'theorem', not any annotions. They should end with ':= by'. Additionally, please use standard mathematical symbols (e.g., ∀, ∃, √) instead of Unicode escape sequences (e.g., \u2200).\n\n"
        #prompt += "## Lean4 file:\n\n"
        try:
            with open(notion_file_path, "r") as f:
                content= f.read()
        except FileNotFoundError:
            logger.warning(f"File not found: {seed.path}")
            return []
        
        theorems = self._generate_theorems_by_llm(prompt, content)
        if use_get_header:
            header = _get_header2(content)
        else:
            header = content
        return _parse_eval_results2(theorems, header, context = content)

    def generate_by_seed(self, seed: Seed) -> list[ConjectureEvalResult]:
        prompt = "Please generate new theorems in Lean 4 format that are similar but not identical to each theorem provided in the text. For each theorem in the text, generate a corresponding new theorem with slight variations in content. Do not include proofs, annotations, or imports. The new theorems begin with 'theorem', not any annotions. They should end with ':= by'. Additionally, please use standard mathematical symbols (e.g., ∀, ∃, √) instead of Unicode escape sequences (e.g., \u2200)."

        try:
            with open(seed.path, "r") as f:
                file_content = f.read()
            
        except FileNotFoundError:
            logger.warning(f"File not found: {seed.path}")
            return []

        theorems = self._generate_theorems_by_llm(prompt, file_content)
        header = _get_header(file_content)
        return _parse_eval_results(theorems, header)


    def _generate_theorems_by_llm(self, prompt: str, content: str, model: str = "gpt-4o-2024-08-06") -> list[str]:
        class Theorems(BaseModel):
            theorems: list[str]

        completion = self.client.beta.chat.completions.parse(
            model=model,
            messages=[
                {
                    "role": "system",
                    "content": prompt,
                },
                {"role": "user", "content": content[:2000]},
            ],
            response_format=Theorems,
        )
        theorems: Theorems = completion.choices[0].message.parsed
        return theorems.theorems


def _parse_eval_results(theorems: list[str], header: str) -> list[ConjectureEvalResult]:
    id_head = datetime.now().strftime("%Y%m%d_%H%M%S")
    conjectures = list(
        filter(
            lambda x: x is not None,
            (parse_conjecture(f"{id_head}_{i}", header, statement)
            for i, statement in enumerate(theorems))
        )
    )
    return evaluate(conjectures)

def _parse_eval_results2(theorems: list[str], header: str, context: str) -> list[ConjectureEvalResult]:
    id_head = datetime.now().strftime("%Y%m%d_%H%M%S")
    conjectures = list(
        filter(
            lambda x: x[0] is not None and x[1] is not None,
            ((parse_conjecture(f"{id_head}_{i}", header, statement, skip_check = True),
              parse_conjecture(f"{id_head}_{i}", context, statement))
            for i, statement in enumerate(theorems))
        )
    )
    return evaluate2(conjectures)

def _get_header(file_content: str) -> str:
    context_set = set()
    context_list = []
    namespace_set = set()
    for line in file_content.split("\n"):
        if line.startswith("variable"):
            if line not in context_set:
                context_list.append(line)
                context_set.add(line)
        elif line.startswith("namespace"):
            namespaces = line.split(" ")[1:]
            for namespace in namespaces:
                namespace_set.add(namespace)
    namespace_str = "open " + " ".join(namespace_set) if namespace_set else ""
    context_str = "\n".join(context_list)
    return "\n\n".join(["import Mathlib\nimport Aesop", context_str, namespace_str]) + "\n\n"

def _get_header2(file_content: str) -> str:
    context_set = set()
    context_list = []
    namespace_set = set()
    for line in file_content.split("\n"):
        if line.startswith("variable") or line.startswith("universe"):
            if line not in context_set:
                context_list.append(line)
                context_set.add(line)
        elif line.startswith("open"):
            namespaces = line.split(" ")[1:]
            for namespace in namespaces:
                namespace_set.add(namespace)
    namespace_str = "open " + " ".join(namespace_set) if namespace_set else ""
    context_str = "\n".join(context_list)
    return "\n\n".join(["import Mathlib\nimport Aesop", context_str, namespace_str]) + "\n\n"


def evaluate(conjectures: list[Conjecture]) -> list[ConjectureEvalResult]:
    eval_results = []
    for conjecture in conjectures:
        if not conjecture.grammatical:
            eval_results.append(
                ConjectureEvalResult(
                    conjecture=conjecture,
                    already_exists=False,
                    aesop_provable=False,
                    interestingness=0.0,
                    proof=None
                )
            )
            continue
        if not _is_valid(conjecture):
            logger.warning(f"Invalid statement: {str(conjecture)}")
            conjecture.grammatical = False
            eval_results.append(
                ConjectureEvalResult(
                    conjecture=conjecture,
                    already_exists=False,
                    aesop_provable=False,
                    interestingness=-1.0,
                    proof=None
                )
            )
            continue
        exact_proof = _proved_by_exact(conjecture)
        if exact_proof is not None:
            logger.info(f"{str(conjecture)} {exact_proof}")
            eval_results.append(
                ConjectureEvalResult(
                    conjecture=conjecture,
                    already_exists=True,
                    aesop_provable=False,
                    interestingness=0.0,
                    proof=exact_proof
                )
            )
            continue
        aesop_proof = _proved_by_aesop(conjecture)
        if aesop_proof is not None:
            eval_results.append(
                ConjectureEvalResult(
                    conjecture=conjecture,
                    already_exists=True,
                    aesop_provable=True,
                    interestingness=0.1,
                    proof=aesop_proof
                )
            )
            continue

        else:
            eval_results.append(
                ConjectureEvalResult(
                    conjecture=conjecture,
                    already_exists=False,
                    aesop_provable=False,
                    interestingness=_interestingness(conjecture),
                    proof=None
                )
            )
    return eval_results
    
def evaluate2(conjectures: list[tuple[Conjecture, Conjecture]]) -> list[ConjectureEvalResult]:
    eval_results = []
    for conjecture, context in conjectures:
        if not context.grammatical:
            continue
        if not _is_valid(context):
            logger.warning(f"Invalid statement: {str(context)}")
            context.grammatical = False
            eval_results.append(
                ConjectureEvalResult(
                    conjecture=conjecture,
                    already_exists=False,
                    aesop_provable=False,
                    interestingness=-1.0,
                    proof=None
                )
            )
            continue
        exact_proof = _proved_by_exact(context)
        if exact_proof is not None:
            eval_results.append(
                ConjectureEvalResult(
                    conjecture=conjecture,
                    already_exists=True,
                    aesop_provable=False,
                    interestingness=0.0,
                    proof=exact_proof
                )
            )
            continue
        aesop_proof = _proved_by_aesop(context)
        if aesop_proof is not None:
            eval_results.append(
                ConjectureEvalResult(
                    conjecture=conjecture,
                    already_exists=True,
                    aesop_provable=True,
                    interestingness=0.1,
                    proof=aesop_proof
                )
            )
            continue

        else:
            eval_results.append(
                ConjectureEvalResult(
                    conjecture=conjecture,
                    already_exists=False,
                    aesop_provable=False,
                    interestingness=_interestingness(conjecture),
                    proof=None
                )
            )
    return eval_results
    
def _exec(file_path: str = None) -> dict:
    if file_path is None:
        file_path = _get_temp_file_path()
    command = f'echo \'{{"path": "{file_path}", "allTactics": true}}\' | /root/.elan/bin/lake exe repl'
    work_dir = "/var/mathlib4"
    result = subprocess.run(command, cwd=work_dir, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    
    # 一時ファイルを削除
    try:
        os.remove(file_path)
    except FileNotFoundError:
        pass  # ファイルが既に削除されている場合は無視
    
    if result.returncode != 0:
        raise ValueError("Verification failed.")

    return json.loads(result.stdout)

def _is_valid(conjecture: Conjecture) -> bool:
    """
    If the conjecture is valid, return True.
    Else return False.
    """
    temp_file_path = _get_temp_file_path()
    with open(temp_file_path, "w") as f:
        f.write(conjecture.sorry_str)
    result = _exec(temp_file_path)
    for message in result["messages"]:
        if message["severity"] == "warning" and message["data"] == "declaration uses 'sorry'":
            return True

    return False

def _proved_by_exact(conjecture: Conjecture) -> str | None:
    """
    If a proof of the conjecture can be found by "exact?", return the proof.
    Else return None.
    Novelty means a proof of the conjecture cannot be found by "exact?".
    """
    #logger.info(f"Proving by exact: {conjecture.exactmode}")
    temp_file_path = _get_temp_file_path()
    with open(temp_file_path, "w") as f:
        f.write(conjecture.exactmode)

    result = _exec(temp_file_path)
    for message in result["messages"]:
        if message["severity"] == "error":
            if not message["data"].startswith("`exact?` could not close the goal."):
                logger.error(f"Error: {message['data']}")
            return None
        if message["severity"] == "info" and message["data"].startswith("Try this:"):
            logger.info("The conjecture can be proved by exact!")
            return message["data"].split("Try this:")[1].strip()
    
    logger.info("The conjecture cannot be proved by exact.")
    return None

def _proved_by_aesop(conjecture: Conjecture) -> str | None:
    """
    If a proof of the conjecture can be found by "aesop?", return the proof.
    Else return None.
    """
    temp_file_path = _get_temp_file_path()
    with open(temp_file_path, "w") as f:
        f.write(conjecture.aesopmode)

    result = _exec(temp_file_path)
    for message in result["messages"]:
        if message["severity"] == "info" and message["data"].startswith("Try this:")\
            and "sorry" not in message["data"]:
            logger.info("The conjecture can be proved by aesop!")
            return message["data"].split("Try this:")[1].strip()

    logger.info("The conjecture cannot be proved by aesop.")
    return None

def _interestingness(conjecture: Conjecture) -> float:
    """
    Score the conjecture by LLM in term of interestingness
    """
    # TODO: Implement
    return 0.5

def run_command(command):
    """シェルコマンドを実行して出力を返す"""
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if result.returncode != 0:
        print("コマンド実行エラー:", ' '.join(command))
        print(result.stderr)
        exit(1)
    return result.stdout.strip()

class Mathlib(object):

    def __init__(self):
        # 設定項目（必要に応じて書き換えてください）
        self.REPO_OWNER = "auto-res"    # GitHub ユーザ名または組織名
        self.REPO_NAME = "mathlib4"     # リポジトリ名
        self.BASE_BRANCH = "main"              # ベースブランチ（例: main または master）
        self.HEAD_BRANCH = f"feature/{datetime.now()}"      # 作業用ブランチ名
        self.FILE_PATH = "."         # 変更対象のファイルパス
        self.COMMIT_MESSAGE = "new theorems"  # コミットメッセージ
        self.PR_TITLE = "Add new theorems"  # PR タイトル
        self.PR_BODY = "Please review the new theorems."  # PR 本文
        self.MATHLIB_PATH = "/var/mathlib4"  # Mathlib ディレクトリのパス\

        # GitHub トークンの取得（環境変数などから）
        self.GITHUB_TOKEN = os.environ.get("GITHUB_TOKEN")
        if not self.GITHUB_TOKEN:
            print("GITHUB_TOKEN が設定されていません。環境変数にトークンを設定してください。")
            exit(1)

    def cd(self) -> None:
        os.chdir(self.MATHLIB_PATH)


    def create_branch(self):
        self.cd()
        # ベースブランチに切り替えた後、新規ブランチを作成
        run_command(['git', 'switch', self.BASE_BRANCH])
        run_command(['git', 'switch', '-c', self.HEAD_BRANCH])
        print(f"ブランチ '{self.BASE_BRANCH}' を {self.HEAD_BRANCH} から作成しました。")

    def commit_and_push(self):
        self.cd()
        # 変更ファイルをステージングしてコミット、リモートにプッシュ
        run_command(['git', 'add', self.FILE_PATH])
        run_command(['git', 'commit', '-m', self.COMMIT_MESSAGE])
        run_command(['git', 'push', '-u', 'origin', self.HEAD_BRANCH])
        print(f"ブランチ '{self.HEAD_BRANCH}' に変更をコミット＆プッシュしました。")

    def create_pull_request(self):
        # GitHub API を利用して PR を作成（組織リポジトリの場合）
        url = f"https://api.github.com/repos/{self.REPO_OWNER}/{self.REPO_NAME}/pulls"
        headers = {
            "Authorization": f"token {self.GITHUB_TOKEN}",
            "Accept": "application/vnd.github.v3+json"
        }
        data = {
            "title": self.PR_TITLE,
            "head": self.HEAD_BRANCH,
            "base": self.BASE_BRANCH,
            "body": self.PR_BODY
        }
        response = requests.post(url, headers=headers, json=data)
        if response.status_code == 201:
            pr_url = response.json().get("html_url")
            print("Pull Request が正常に作成されました:", pr_url)
        else:
            print("Pull Request の作成に失敗しました。レスポンス内容:")
            print(response.json())
    
    def run_workflow(self):
        self.create_branch()
        self.commit_and_push()
        self.create_pull_request()

if __name__ == "__main__":
    with open("./notions/inter_closure_excercise_output.lean", "r") as f:
        content = f.read()
    conjectore = parse_conjecture("tmp", content, "theorem interior_closure_subset_ai : interior (closure s) ⊆ interior s := by")
    exact_proof = _proved_by_exact(conjectore)
    print(exact_proof)