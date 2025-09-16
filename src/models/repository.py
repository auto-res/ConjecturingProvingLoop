import os
import json
import pickle

from loguru import logger

from .entity import Conjecture, ConjectureEvalResult

CONJECTURE_DATA_PATH = "/data/conjectures.jsonl"
CONJECTURE_EVAL_PATH = "/data/eval_conjecture_result.jsonl"
SUCCESSFUL_CONJECTURES_PATH = "/data/successful_conjectures.jsonl"
PROOF_DATA_PATH = "/data/proofs.jsonl"
NONTRIVIAL_CONJECTURES_PATH = "/data/nontrivial_conjectures.jsonl"
    

class ConjectureEvalResultRepository(object):
    def save(method_name: str, eval_results : list[tuple[str, ConjectureEvalResult]]) -> None:
        """
        save evaluation results
        method_name: str
        eval_results: list[ConjectureEvalResult]
        each eval result consists of an input hint and a ConjectureEvalResult object
        """
        with open(CONJECTURE_EVAL_PATH, "a") as f:
            for hint, eval_result in eval_results:
                f.write(
                    json.dumps({
                        "conjecture_id" : eval_result.conjecture.conjecture_id,
                        "grammatical" : eval_result.conjecture.grammatical,
                        "already_exists" : eval_result.already_exists,
                        "aesop_provable" : eval_result.aesop_provable,
                        "interestingness" : eval_result.interestingness,
                        "method_name" : method_name,
                        "input" : hint,
                        "conjecture" : str(eval_result.conjecture),
                        "proof" : eval_result.proof,
                    }) + "\n"
                )
    
    def save_nontrivial_conjectures(eval_results: list[ConjectureEvalResult]) -> None:
        with open(NONTRIVIAL_CONJECTURES_PATH, "w") as f:
            for eval_result in eval_results:
                if eval_result.conjecture.grammatical and not eval_result.already_exists:
                    f.write(
                        json.dumps({
                            "conjecture_id" : eval_result.conjecture.conjecture_id,
                            "name" : eval_result.name,
                            "informal_prefix" : eval_result.conjecture.informal_prefix,
                            "formal_statement": eval_result.statement,
                            "goal" : eval_result.conjecture.goal,
                            "header" : eval_result.header,
                            "aesop_provable" : eval_result.aesop_provable,
                            "interestingness" : eval_result.interestingness,
                            "conjecture" : str(eval_result.conjecture),
                            "proof" : eval_result.proof,
                        }) + "\n"
                    )
    
    def get_nontrivial_conjectures(self) ->  list[Conjecture]:
        with open(CONJECTURE_EVAL_PATH, "r") as f:
            eval_results = [json.loads(line) for line in f]
        
        return [
            Conjecture(
                conjecture_id=eval_result["conjecture_id"],
                statement=eval_result["conjecture"],
                grammatical=eval_result["grammatical"]
            )
            for eval_result in eval_results
            if eval_result["grammatical"] and \
                (not eval_result["already_exists"]) and \
                (not eval_result["aesop_provable"])
        ]

class ProofRepository(object):
    def _get_success_filepaths(self, dirpath: str) -> list[str]:
        """
        ディレクトリ内を再帰的に探索し，"success"で始まる.pklファイルのファイルパスのリストを取得
        """
        verified_files = []
        # os.walkを使って、指定されたディレクトリ以下の全ファイル・ディレクトリを再帰的に探索
        for root, dirs, files in os.walk(dirpath):
            for file in files:
                # ファイル名が"success"で始まり、".pickle"で終わるかをチェック
                if file.startswith("success") and file.endswith(".pkl"):
                    # 絶対パスを作成してリストに追加
                    verified_files.append(os.path.join(root, file))
        return verified_files
    
    def _get_verified_code(self, filepath: str) -> str:
        with open(filepath, "rb") as f:
            result = pickle.load(f)[-1]
        
        return result["result"]["verified_code"]

    def _get_verified_codes(self, dirpath: str) -> list[str]:
        verified_files = self._get_success_filepaths(dirpath)
        return [self._get_verified_code(filepath) for filepath in verified_files]

    def _get_file_content(self, dirpath: str) -> str:
        verified_codes = self._get_verified_codes(dirpath)
        content = concat_codes(verified_codes)

        return content
    
    def commit_succeeded_properties(self, dirpath: str) -> None:
        save_filepath = get_save_filepath(dirpath)
        contents = self._get_file_content(dirpath)

        with open(save_filepath, "w") as f:
            f.write(contents)

def _header_theorem_split(code: str) -> tuple[str, str]:
    """
    codeをヘッダと定理に分割
    """
    split_codes = code.split("theorem")
    header = "theorem".join(split_codes[:-1])
    theorem = "theorem" + split_codes[-1]
    return header, theorem

def concat_codes(codes: list[str]) -> str:
    """
    codesを結合して返す
    """
    theorems = []
    header=""
    for code in codes:
        header, theorem = _header_theorem_split(code)
        theorems.append(theorem)
    
    return header + "\n\n".join(theorems)

def get_save_filepath(dirpath: str) -> str:
    """
    Generate save filepath from dirpath
    If the input `dirpath` is not like /data/logs/regularopen, raise error
    For example, /data/logs/regularopen -> notions/Regularopen.lean
    """
    # 各ディレクトリ名をCamelCaseに変換
    dirnames = dirpath.split("/")
    if dirnames[1] != "data" or dirnames[2] != "logs" or len(dirnames) != 4:
        raise ValueError("invalid dirpath")
    # ファイル名を生成
    filename = dirnames[-1] + ".lean"
    return os.path.join("notions", filename)