import json
import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import ks_2samp, mannwhitneyu

def to_cumulative_distribution(proof_lengths, max_length):
    commutative_proof_lengths = [0 for _ in range(max_length)]
    for proof_length in proof_lengths:
        assert proof_length < max_length
        commutative_proof_lengths[proof_length] += 1
    for i in range(1, max_length):
        commutative_proof_lengths[i] += commutative_proof_lengths[i-1]
    return [100 *count / len(proof_lengths) for count in commutative_proof_lengths]

with open("results/proof_lengths.json", "r") as f:
    proof_lengths = json.load(f)

result = ks_2samp(proof_lengths['CPL'], proof_lengths['SL'], mode = "auto", alternative = "less")
print(f"CPL vs SL (less): D = {result.statistic}, p = {result.pvalue}")
result = mannwhitneyu(proof_lengths['CPL'], proof_lengths['SL'], alternative = "less")
print(f"CPL vs SL (less): U = {result.statistic}, p = {result.pvalue}")

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
plt.savefig("../figures/proof_lengths.pdf")
plt.show()