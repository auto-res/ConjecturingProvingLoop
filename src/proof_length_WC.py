import os, json
import numpy as np
import matplotlib.pyplot as plt
from proof_lengths import find_assign_outside_parens

CPL_dir = "results/P_without_context/CPL/"
SL_dir = "results/P_without_context/SL/"

CPL_theorems = json.load(open(os.path.join(CPL_dir, "3000000_theorems.json"), "r", encoding="utf-8"))
SL_theorems = json.load(open(os.path.join(SL_dir, "3000000_theorems.json"), "r", encoding="utf-8"))

CPL_proof_lengths = [len(theorem[find_assign_outside_parens(theorem):].strip()) for theorem in CPL_theorems]
SL_proof_lengths = [len(theorem[find_assign_outside_parens(theorem):].strip()) for theorem in SL_theorems]

print(f"CPL: {len(CPL_proof_lengths)}, SL: {len(SL_proof_lengths)}")
print(f"CPL: {sum(CPL_proof_lengths) / len(CPL_proof_lengths)}, SL: {sum(SL_proof_lengths) / len(SL_proof_lengths)}")

proof_lengths = {"CPL": CPL_proof_lengths, "SL": SL_proof_lengths}

from scipy.stats import ks_2samp

result = ks_2samp(proof_lengths['CPL'], proof_lengths['SL'], mode = "auto", alternative = "less")
print(f"CPL vs SL (less): D = {result.statistic}, p = {result.pvalue}")

max_length = max(max(proof_lengths["CPL"]), max(proof_lengths["SL"])) + 1

fontsize = 30

fig, ax = plt.subplots(figsize=(10, 6))

# 統一されたbinの範囲を計算
all_data = proof_lengths["CPL"] + proof_lengths["SL"]
min_val = min(all_data)
max_val = max(all_data)
bins = np.linspace(min_val, max_val, 21)  # 20個のbinを作るため、21個の境界点が必要

# パーセンテージで表示するため、weightsを使用
ax.hist(proof_lengths["CPL"], bins=bins, label="CPL", alpha=0.5, 
        weights=np.ones(len(proof_lengths["CPL"])) * 100 / len(proof_lengths["CPL"]))
ax.hist(proof_lengths["SL"], bins=bins, label="SL", alpha=0.5, 
        weights=np.ones(len(proof_lengths["SL"])) * 100 / len(proof_lengths["SL"]))
ax.legend(fontsize=fontsize)
ax.set_xlabel("Length of proofs", fontsize=fontsize)
ax.set_ylabel("Percentage (%)", fontsize=fontsize)
ax.set_title("Proof length distribution", fontsize=fontsize)
ax.tick_params(axis='both', which='major', labelsize=fontsize)
plt.tight_layout()
plt.savefig("../figures/proof_lengths_WC.pdf")
plt.show()