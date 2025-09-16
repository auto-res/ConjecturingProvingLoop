import argparse
import os


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--input_file", type=str, default = "./results/with_stats/4ogen/generated_29.lean")
    parser.add_argument("--target_theorem", type=str, default = "intersection_of_alpha_open_sets_is_alpha_open")
    args = parser.parse_args()

    input_file = args.input_file
    with open(input_file, "r") as f:
        content = f.read()
    header = content.split("theorem")[0]
    context = content[len(header):].split("theorem " + args.target_theorem)[0]
    statement = "theorem " + args.target_theorem + content[len(header):].split("theorem " + args.target_theorem)[1].split(":=")[0] + ":="

    for i,theorem in enumerate(content.split("theorem")[1:]):
        print(i, theorem.split(":=")[0])