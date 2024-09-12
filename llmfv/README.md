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
