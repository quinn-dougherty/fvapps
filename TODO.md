# TODOs

## 2024-11-04 Notes
- current loops around the agent for metadata tracking only collect after 10 or success, this is not great
- are we going to store 10's of thousands of model chat history to "pick up where we left off?"
- No. This is complicated and I don't think it will help the model that meaningfully. Starting fresh is more likely
to lead to a new/fresh solution that might work, rather than getting stuck, especially in Lean.
- We might need an LLM judge or something to check if proofs are complete (exit code 0 might not be good enough)
- When you choose a sample that has already been 

- For a single example (index 0 appsid 2459):
- definitions completed after 9 attempts
- 100k tokens in, 10k out (roughly, probably underestimate) (per 10 claude loops)
- theorems 1 and 2 failed to converge after 10 loops
- this cost $2.31 

- restarting will correctly track additional loops in metadata but won't in the terminal output/logs
- easy fix, just need to pass loop() a start idx that defaults to 0.