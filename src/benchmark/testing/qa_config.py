import tomllib
from benchmark.testing.convert_units import convert_tests

with open("src/benchmark/testing/qa_config.toml", "rb") as f:
    cfg = tomllib.load(f)

qa_cfg = {
    **{
        "system_prompt": lambda _: f"""
You are an expert Lean 4 developer. Your task is to take a python solution and translate it into lean 4. Follow these guidelines:
- You will be provided with an original English language description of the problem for context.
- You may use inline comments to explain your code and proofs.
- DO NOT COMMENT ON THE PROBLEM OR CODE OUTSIDE OF INLINE COMMENTS.
- Start your generation with 3 backticks, and end it with 3 backticks.
- PROVIDE ONLY ONE BLOCK OF CODE WITHIN THE 3 BACKTICKS.
- THE BLOCK OF CODE SHOULD INCLUDE ALL THE CODE YOU WANT TO SUBMIT.
- We are now using Lean 4.13. There may be some functions or imports that have moved or changed, but you can try to fix them based on the result of your attempts.
""",
        "first_prompt": lambda soln: f"""
Please translate the following solution into lean 4, skipping the "main" runner and test cases:

```
{soln}
```

Append the following lean 4 tests to your solution:

```
{convert_tests(soln)}
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

sonnet_cfg = {**cfg["sonnet"], **qa_cfg}
