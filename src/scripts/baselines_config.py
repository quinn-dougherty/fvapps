import tomllib

with open("src/scripts/baselines_config.toml", "rb") as f:
    cfg = tomllib.load(f)

lean4_palindromes_example = open(
    "src/scripts/prompt_imports/palindromes.Lean", "r"
).read()

lean4_bintree_example = open("src/scripts/prompt_imports/bintree.Lean", "r").read()

baselinecfg = {
    **{
        "system_prompt": lambda _: f"""
You are an expert Lean 4 developer. Your task is to fill in definitions and prove theorems in the provided specification. Follow these guidelines:
- You will be provided with an original English language description of the problem for context.
- Do not comment on the problem or the code itself, only generate code that can be directly exported into a file and ran.
- Start your generation with 3 backticks, and end it with 3 backticks.
- Use mathlib using "import Mathlib.Data.List.Basic".
- We are now using Lean 4.12. There may be some functions or imports that have moved or changed, but you can try to fix them based on the result of your attempts.

# Examples

Here is an example of a fully specified Lean 4 file with a definition and theorems for checking if a list is a palindrome:

{lean4_palindromes_example}

Here is an example of a fully specified Lean 4 file with a definition and theorems for a binary tree:

{lean4_bintree_example}
""",
        "first_prompt": lambda x, y: f"""
Here is the original question in English:

{x}

Please prove these Lean 4 theorems:

{y}
""",
        "continuous_prompt": lambda stdout, stderr: f"""
Running the code produced the following output:

Standard out:
{stdout}

Standard error:
{stderr}

Please fix your original output, again only generating code within the 3 backticks.
""",
    },
    **cfg["common"],
}

sonnet_cfg = {**cfg["sonnet"], **baselinecfg}
o1_cfg = {**cfg["o1"], **baselinecfg}
prover_rl_cfg = {**cfg["prover_rl"], **baselinecfg}
llama_cfg = {**cfg["llama"], **baselinecfg}
testhf_cfg = {**cfg["testhf"], **baselinecfg}
