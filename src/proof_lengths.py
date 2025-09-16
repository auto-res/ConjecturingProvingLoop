import json

with open("results/with_stats/4ogen/eval_result/all_stats.json", "r") as f:
    results = json.load(f)
print(len(results))

proved_with_context = []
proved_without_context = []
for result in results:
    if result["proved_with_context"]:
        proved_with_context.append(result)
    if result["proved_without_context"]:
        proved_without_context.append(result)

print(len(proved_with_context), len(proved_with_context) / len(results))
print(len(proved_without_context), len(proved_without_context) / len(results))

import matplotlib.pyplot as plt

fontsize = 30

fig, ax = plt.subplots(figsize=(10, 6))

files = ["results/with_stats/4ogen/generated_29.lean", "results/simple_loop/o3/final_generated.lean"]
labels = ["CPL", "Simple loop"]
for i, file in enumerate(files):
    with open(file, "r") as f:
        content = f.read()

    theorems = content.split("theorem")[1:]
    print(len(theorems))
    proof_lengths = []

    for theorem in theorems:
        proof = theorem[theorem.find(":="):].split("\n\n")[0]
        proof_lengths.append(len(proof.split("\n")))

    ax.hist(proof_lengths, bins=11, density=True, alpha=0.5, range=(0, 110), label=labels[i])

ax = plt.gca()
ax.yaxis.set_major_formatter(plt.FuncFormatter(lambda y, _: '{:.0f}'.format(y * 100)))

plt.legend(fontsize=fontsize)
plt.xlabel("Number of lines in proofs", fontsize=fontsize)
plt.ylabel("Percentage (%)", fontsize=fontsize)
plt.title("Proof length distribution", fontsize=fontsize)
plt.xticks(fontsize=fontsize)
plt.yticks(fontsize=fontsize)
plt.tight_layout()
plt.savefig("proof_lengths.pdf")
plt.show()