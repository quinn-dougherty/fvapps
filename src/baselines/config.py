import tomllib

with open("src/baselines/config.toml", "rb") as f:
    cfg = tomllib.load(f)

baselinecfg = {
    **{
        "system_prompt": lambda x: """
    You are a senior Lean 4 developer with expertise in proving theorems.
    Your task is to prove the theorems in the provided specification, using the original English-language question as a guide.
    Each theorem is currently proven by "sorry".
    Do not import, assume you cannot access any existing libraries.
    Do not comment on the problem or the code itself, only generate code that can be directly exported into a file and ran.
    Start your generation with 3 backticks, and end it with 3 backticks.
    """,
        "first_prompt": lambda x, y: f"""Here is the original question in English:\n\n{x}\n\nPlease prove these Lean 4 theorems:\n\n{y}""",
        "continuous_prompt": lambda stdout, stderr: f"""
    Running the code produced the following output:\n\nStandard out:\n{stdout}\n\nStandard error:\n{stderr}\n\n.
    Please fix your original output, again only generating code within the 3 backticks and without imports.
    """,
    },
    **cfg["lean_agent_sonnet35_baseline"],
}
