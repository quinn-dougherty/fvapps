import tomllib

with open("src/baselines/baselines_config.toml", "rb") as f:
    cfg = tomllib.load(f)

batteries_imports = open("src/baselines/prompt_imports/Batteries.lean", "r").read()

lean4_palindromes_example = open(
    "src/baselines/prompt_imports/palindromes.Lean", "r"
).read()

lean4_bintree_example = open("src/baselines/prompt_imports/bintree.Lean", "r").read()

# Copied from https://github.com/paulcadman/lean4-leetcode
leetcode_examples = open("src/baselines/prompt_imports/leetcode_examples.txt", "r").read()
baselinecfg = {
    **{
        "system_prompt": lambda _: f"""
You are an expert Lean 4 developer. Your task is to fill in definitions and prove theorems in the provided specification. Follow these guidelines:
- You will be provided with an original English language description of the problem for context.
- You will iteratively be provided with a Lean 4 file with some definitions and theorems already written, some of which have sorrys instead of proofs or implementations.
- Your goal is to fill in the sorrys with proofs or implementations.
- You may adjust the existing definitions and theorems, but try not to add additional definitions or theorems.
- You may use inline comments to explain your code and proofs.
- DO NOT COMMENT ON THE PROBLEM OR CODE OUTSIDE OF INLINE COMMENTS.
- Start your generation with 3 backticks, and end it with 3 backticks.
- PROVIDE ONLY ONE BLOCK OF CODE WITHIN THE 3 BACKTICKS.
- THE BLOCK OF CODE SHOULD INCLUDE ALL THE CODE YOU WANT TO SUBMIT.
- We are now using Lean 4.12. There may be some functions or imports that have moved or changed, but you can try to fix them based on the result of your attempts.
- You may use mathlib4 if absolutely necessary, for example using "import Mathlib.Data.List.Basic".
- Most of mathlib imports do not use Init anymore, so you can use "import Mathlib.Data.List" instead of "import Mathlib.Init.Data.List".
- You may add sorrys for subexpressions if it gets you closer to a solution. Be sure to comment on this, you may return to it later.
- Once a solution is found including sorrys, your goal is to complete the proof of those sorrys.

- Some commonly used imports for Lean 4 are now in the batteries package, here are their imports:

{batteries_imports}


# Examples

Here are some syntax and proof examples.

For checking if a list is a palindrome:

```
{lean4_palindromes_example}
```

For implementing a binary tree:

```
{lean4_bintree_example}
```

Here are some additional examples of some typical LeetCode style problems.
These provide some context for the types of problems you may encounter, with a problem description and a Lean 4 solution.

{leetcode_examples}
""",
        "first_prompt": lambda x, y: f"""
Here is the original question in English:

{x}

Please implement the sorrys in the definitions and theorems in this Lean 4 file:

```
{y}
```
""",
        "continuous_prompt": lambda stdout, stderr: f"""
Running the code produced the following output:

Standard out:
```
{stdout}
```

Standard error:
```
{stderr}
```

Please fix your original output, keeping in mind the strong guidelines above. If the current code is correct and you have another shot, try to address the sorrys that were added as intermediate steps.
""",
    },
    **cfg["common"],
}

sonnet_cfg = {**cfg["sonnet"], **baselinecfg}
gpt4o_cfg = {**cfg["gpt-4o"], **baselinecfg}
gemini_cfg = {**cfg["gemini"], **baselinecfg}
prover_rl_cfg = {**cfg["prover_rl"], **baselinecfg}
llama_cfg = {**cfg["llama"], **baselinecfg}
testhf_cfg = {**cfg["testhf"], **baselinecfg}
