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

## Methodology
- ask llm to generate property tests for apps problems
- subject corresponding apps solutions to those property tests
- ask llm to generate sorry'd out lean theorems from property tests
- output task: original task plus sorry'd out lean theorems.
