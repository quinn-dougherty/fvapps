# FV-APPS

Lifting [APPS](https://github.com/hendrycks/apps) to Lean with LLM-generated property tests and theorem statements.

## Setup

```
rye sync
```

Create a `.env` file with the following:
```
ANTHROPIC_API_KEY="YOUR_KEY_HERE"
```

## Basic Run

``` sh
rye run hypothesis_gen_test
rye run lean_gen_test
```

## APPS

## Setup/Download
Set up and download the apps dataset with
```
sh scripts/setup_apps.sh
```
## Preprocess/Cleanup
Then preprocess the dataset to format the solutions nicely. You can choose a problem and run it by: TODO
```python
rye run src/scripts/populate_apps_sols.py problem_id=PROBLEM_ID
```
(TODO argparse impl for that script)
This will use the Claude API to create a proper function that can be used for property testing.

## Generate Python Property Tests
You can then generate property tests using a similar Claude agent loop.
```
# TODO add argparse, currently just runs up to 5
rye run python src/scripts/apps_gen_hyp_tests.py
```

## Generate LEAN
TODO doc here


## Methodology
- ask llm to generate property tests for apps problems
- subject corresponding apps solutions to those property tests
- ask llm to generate sorry'd out lean theorems from property tests
- output task: original task plus sorry'd out lean theorems.
