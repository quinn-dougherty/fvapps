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
- Lean 4 strings are in double quotes, not single quotes
""",
        "first_prompt": lambda soln: f"""
Please translate the following solution into lean 4, skipping the "main" runner and test cases:

```
{soln}
```

We'll convert the test cases to lean unit tests with the following format:
```lean
/--
 info: <expected>
-/
#guard_msgs in
#eval <function_name> <args>
```

Make sure the function name in your autoformalization matches the function name in the original code.
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

Please fix your original output, keeping in mind the strong guidelines above.

Do not copy the `#guard_msgs in #eval` block from the lean output. We will add that for you.

If you see a `#` in front of any list argument (`["foo"]`) in the lean 4 `#guard_msgs in` block, make the corresponding argument type is `Array` not `List`.
If there is no `#` in front of the square bracket, then make sure the argument type is `List` not `Array`.
""",
    },
    **cfg["common"],
}

sonnet_cfg = {**cfg["sonnet"], **qa_cfg}
