import argparse

from models import ConjectureGenerator, ConjectureEvalResultRepository

def main(filepath: str):
    generator = ConjectureGenerator()
    eval_results = generator.generate(filepath)
    contents = [(filepath, eval_result) for eval_result in eval_results]

    ConjectureEvalResultRepository.save("generate", contents)
    ConjectureEvalResultRepository.save_nontrivial_conjectures(eval_results)

if __name__ == "__main__":
    args = argparse.ArgumentParser()
    args.add_argument("--filepath", type=str, default="./notions/RegularOpen.lean")

    filepath = args.parse_args().filepath

    main(filepath)
