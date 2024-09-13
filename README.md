# LLM-FV: Toward Scaling Formal Verification Schemes via LLMs

Describe your project here.


# Setup

```
rye sync
```

Create a `.env` file in `nb/` next to this README with the following:
```
ANTHROPIC_API_KEY="YOUR_KEY_HERE"
```


# Basic Run
You can try to run `python example_agent_run.py`. This will attempt to create tests using claude for the example function in `test/example_func.py`.

Once it completes (successfully), you can re-test the final output with `pytest test/test_example_func.py`. 
# Formally Verified APPS

## Conceptually 1
- llm-solve an apps subset in imp, at least in slow versions
- Provided in benchmark:
  - write slow imp programs
  - write hoare triples
  - prove hoare triples
- Task;
  - ask llm to write faster versions
  - proof of hoare agreement

### value prop
- challenging LLMs to write formally verified code.

### TODO
- [ ] some array story in Imp
- [ ] strings in imp?

## Conceptually 2
- find two implementations of the same problem
- quantify over all inputs that they agree

### Question
- mathlib free or mathlib

### Value prop
challenging LLMs to write dependently typed _and_ formally verified code

### TODO
- [ ] trawl aoc of the ones we have lean4 solutions for some nontriviality:
  - meaning a way to beat the dumb way on O()

## Conceptually 3
- ask llm to generate property tests for apps problems
- subject corresponding apps solutions to those property tests
- ask llm to generate sorry'd out lean theorems from property tests
- output task: original task plus sorry'd out lean theorems.

## TODO
- [ ] read dafny benchmark paper
- [ ] read the APPS easies.
- [ ] remember that we should show baselines from openai, anthropic, and deepseek, and llama
