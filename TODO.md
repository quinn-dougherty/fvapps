# TODOs

## 2024-31-10
- Ronak will add/clean up logging in baselines
- Ronak will make sure that defs+thms are correctly parsed/proved separately
- Ronak will add restart run from checkpoint functionality
- Ronak refactor baseline script to accept apps indices and theorem/def indices

## 2024-11-04
- current loops around the agent for metadata tracking only collect after 10 or success, this is not great
- are we going to store 10's of thousands of model chat history to "pick up where we left off?"
- No. This is complicated and I don't think it will help the model that meaningfully. Starting fresh is more likely
to lead to a new/fresh solution that might work, rather than getting stuck, especially in Lean.