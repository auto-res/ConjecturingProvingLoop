import sys
import argparse

from loguru import logger

from models import ConjectureGenerator, ConjectureEvalResult
from models import ConjectureEvalResultRepository
from models import Seed
from models import get_seeds
from models.service import get_file_paths, get_generated_seeds


def main(start: str, is_all: bool, recursive: bool, generated_only: bool, reverse: bool):
    generator = ConjectureGenerator()
    src_seed = Seed(pp=start)

    seeds = []
    if is_all:
        seeds = get_file_paths()
    elif generated_only:
        seeds = get_generated_seeds()
    elif recursive:
        seeds = get_seeds(src_seed)
        if reverse:
            seeds = seeds[::-1]
    else:
        seeds = [src_seed]

    input_result: list[tuple[str, ConjectureEvalResult]] = []
    try:
        for seed in seeds:
            input_result.extend([
                (str(seed), conjecture) for conjecture in generator.generate_by_seed(seed)
            ])
    except KeyboardInterrupt:
        logger.info("Interrupted by user. Generating conjecture process stopped.")

    logger.info(f"Generated {len(input_result)} conjectures")
    eval_results = list(map(lambda x: x[1], input_result))
    ConjectureEvalResultRepository.save("generated_by_seed", input_result)
    ConjectureEvalResultRepository.save_nontrivial_conjectures(eval_results)


if __name__ == "__main__":
    args = argparse.ArgumentParser()
    args.add_argument(
        "--start_seed", type=str, default="Mathlib.InformationTheory.Hamming"
    )
    args.add_argument("--all", action="store_true")
    args.add_argument("--recursive", action="store_true")
    args.add_argument("--generated_only", action="store_true")
    args.add_argument("--reverse", action="store_true")
    args.add_argument("--log_level", type=str, default="DEBUG")
    log_level = args.parse_args().log_level
    logger.remove()
    logger.add(sink=sys.stderr, level=log_level)
    start = args.parse_args().start_seed
    is_all = args.parse_args().all
    generated_only = args.parse_args().generated_only
    recursive = args.parse_args().recursive
    reverse = args.parse_args().reverse
    main(start, is_all, recursive, generated_only, reverse)
