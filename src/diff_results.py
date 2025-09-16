with open("solved_with_context.txt", "r") as f:
    solved_with_context = f.read()

theorems = [theorem.split()[0] for theorem in solved_with_context.split("theorem")[1:]]

print(f"solved_with_context: {len(theorems)} theorems")

with open("solved_without_context.txt", "r") as f:
    solved_without_context = f.read()

theorems_without_context = [theorem.split()[0] for theorem in solved_without_context.split("theorem")[1:]]

print(f"solved_without_context: {len(theorems_without_context)} theorems")

for theorem in theorems:
    if theorem not in theorems_without_context:
        print(theorem)
