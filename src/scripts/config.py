import tomllib

with open("src/scripts/config.toml", "rb") as f:
    cfg = tomllib.load(f)

pythoncfg = {
    **{
        "system_prompt": lambda x: """
    You are a senior Python developer with expertise in generating property tests. You excel at
    completely covering edge cases and possible inputs using pytest and hypothesis. Be as concise as possible,
    only generating code with no surrounding commentary that can be directly exported into a file and ran.
    Start your generation with 3 backticks, and end it with 3 backticks.
    """,
        "first_prompt": lambda x: f"""Please write property tests for this function. You can assume this file is in "solution_clean.py" and the tests will be in a file called "test_solution.py":\n\n{x}""",
        "continuous_prompt": lambda stdout, stderr: f"""Running the code produced the following output:\n\nStandard out:\n{stdout}\n\nStandard error:\n{stderr}\n\n.
    Please fix your original output, again only generating code within the 3 backticks.""",
    },
    **cfg["python_agent"],
}
leancfg = {
    **{
        "system_prompt": lambda x: """You are a senior Lean 4 developer with expertise in declaring theorems.
    Your task is only to state the theorems based on the property tests given, but not to prove them.
    Instead, ensure the lean typechecker is happy by writing "sorry".
    Do not import Mathlib.
    If needed, declare the function signature and "sorry" its definition.
    Do not comment on the problem or the code itself, only generate code that can be directly exported into a file and ran.
    Start your generation with 3 backticks, and end it with 3 backticks.
    """,
        "first_prompt": lambda x: f"""Please convert these property tests to theorems:\n\n{x}""",
        "continuous_prompt": lambda stdout, stderr: f"""Running the code produced the following output:\n\nStandard out:\n{stdout}\n\nStandard error:\n{stderr}\n\n.
    Please fix your original output, again only generating code within the 3 backticks.""",
    },
    **cfg["lean_agent"],
}
preproc = {
    **{
        "system_prompt": lambda x: """
    You are a senior Python developer with expertise in formatting code. Be as concise as possible,
    only generating code with no surrounding commentary that can be directly exported into a file and ran.
    Start your generation with 3 backticks, and end it with 3 backticks.
    """,
        "first_prompt": lambda x, y, z: f"""Here is a coding problem statement, a proposed solution, and some test cases formatted
        with newlines for calls to input(). Please rewrite the solution as standalone python file that has a single function
        which takes inputs as defined by the problem, implements the same solution, and returns
        the correct type of output. The file should be runnable, with the main() function running the test cases
        and asserting that they are correct.\n\nProblem Statement:\n{x}\n\nProposed Solution:\n{y}\n\nTest Cases:\n{z}""",
        "continuous_prompt": lambda stdout, stderr: f"""Running the code produced the following output:\n\nStandard out:\n{stdout}\n\nStandard error:\n{stderr}\n\n.
    Please fix your original output, again only generating code within the 3 backticks.""",
    },
    **cfg["preproc"],
}
