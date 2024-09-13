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

# Direction
- ask llm to generate property tests for apps problems
- subject corresponding apps solutions to those property tests
- ask llm to generate sorry'd out lean theorems from property tests
- output task: original task plus sorry'd out lean theorems.

# TODO
- [ ] read dafny benchmark paper
- [ ] read the APPS easies.
- [ ] remember that we should show baselines from openai, anthropic, and deepseek, and llama
