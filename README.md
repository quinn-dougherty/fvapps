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
Then preprocess the dataset to format the solutions nicely. You can choose a problem and run it by:
```python
rye run preprocess_app_problem problem_id=PROBLEM_ID
```
This will use the Claude API to create a proper function that can be used for property testing.

## Generate Python Property Tests
You can then generate property tests using a similar Claude agent loop.
```
TODO
```

## Generate LEAN
TODO doc here


## Methodology
- ask llm to generate property tests for apps problems
- subject corresponding apps solutions to those property tests
- ask llm to generate sorry'd out lean theorems from property tests
- output task: original task plus sorry'd out lean theorems.
