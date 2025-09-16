# Conjecturing-Proving Loop

This directory contains the experimental scripts and results for the following paper.

- Kazumi Kasaura, Naoto Onda, Yuta Oriike, Masaya Taniguchi, Akiyoshi Sannai, Sho Sonoda. 2025, "Discovering New Theorems via LLMs with In-Context Proof Learning in Lean."

## Setup

0. Clone the repository with submodules
   ```bash
   git clone --recursive git@github.com:auto-res/ConjecturingProvingLoop.git
   cd ConjecturingProvingLoop
   ```
   
   If you've already cloned without submodules:
   ```bash
   git submodule update --init --recursive
   ```

1. Copy the following files so that you can set your own settings.
```bash
cp .env.example .env
```
2. Edit your `.env` file.

## Docker setup
0. Build the docker container with `docker-compose.yaml`.
```bash
docker compose up -d --build
```
1. Enter the container.
If you want to enter the container by a command, run:
```bash
docker exec -it $APPCONTAINER /bin/bash
```
If you want to enter the container by VSCode, see [this page](https://code.visualstudio.com/docs/devcontainers/attach-container).

2. Lake build
In the docker container $APPCONTAINER, first run
```
export PATH=/root/.elan/bin/:$PATH
cd /workplace/mathlib4
lake exe cache get
lake build
cd /workplace/repl
lake build
cd /workplace/src
```

## How to use
### Conjecturing-Proving Loop
```bash
uv run python cmd_loop.py --seed_file notions/SemiOpen.lean --save_dir results/with_stats/4ogen
```
The generated library in our experiment is stored in `results/with_stats/4ogen/generated_29.lean`.

### Baseline Simple Loop
```bash
uv run python simple_loop.py --seed_file notions/SemiOpen.lean --save_dir results/simple_loop/o3
```
The generated library in our experiment is stored in `results/simple_loop/o3/final_generated.lean`.

### Evaluation of Prover

#### Reproving Generated Theorems
```bash
uv run python eval_prover.py --input_file results/with_stats/4ogen/generated_29.lean --output_dir results/with_stats/4ogen/eval_result
```
#### Proof Ability for Alpha-Open Intersection
```bash
uv run python eval_prover_2.py
```
For natural language proof generation:
```bash
uv run python eval_NL.py --model gpt-4o
uv run python eval_NL.py --model 3o
```
### View Results
Please run `proof_lengths.py`.
