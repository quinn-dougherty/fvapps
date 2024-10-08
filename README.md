# FV-APPS

Lifting [APPS](https://github.com/hendrycks/apps) to Lean with LLM-generated property tests and theorem statements.

## Setup

install `elan` and install/update to a nightly toolchain. Install `rye`.

```
rye sync
. .venv/bin/activate
```

Sourcing the `.venv` will make sure we're not relying on `pytest` executable to have been installed in the global machine.

Create a `.env` file with the following:
```
ANTHROPIC_API_KEY="YOUR_KEY_HERE"
```

On the linux server you'll need to install `parallel`, maybe `screen`.

## How to generate the benchmark

First, we preprocess `apps` solutions

```
$ rye run preprocess --help
usage: preprocess [-h] [--split SPLIT] [--start_idx START_IDX] [--end_idx END_IDX]

options:
  -h, --help            show this help message and exit
  --split SPLIT         Train or test split. Default: train.
  --start_idx START_IDX
                        Start index for the dataset.
  --end_idx END_IDX     End index for the dataset.
```

They'll populate in `artefacts/apps/train/{i}`

Then, two agents will generate property tests and sorry'd out lean theorems, respectively.

```
$ rye run fvapps --help
usage: FV-APPS full generation run [-h] [--split SPLIT] [--start_idx START_IDX] [--end_idx END_IDX]
                                   [--skip_lean] [--skip_python]

options:
  -h, --help            show this help message and exit
  --split SPLIT         train or test (default: train)
  --start_idx START_IDX
                        index to start pulling from apps
  --end_idx END_IDX     index to end pulling from apps
  --skip_lean           skips lean when present
  --skip_python         skips python when present
```

`rye run fvapps --skip_lean` depends on `rye run preprocess` to have been run before, and `rye run fvapps --skip_python` depends on both the preprocessing step and the fvapps python step to have been run before. (`FileNotFoundError` will guide you toward this understanding regardless)

# TODO weekend of 20th
get it set up to do the big run, in general. not listing out what all those tasks are in advance
- [x] track metadata in csv or json about how the run is going (for resets/checkpoints) including last exit code
- [x] refactor apps preproc agent to use base class
- [x] logging (this is semi checked off cuz it's not as thorough as we want and there's still some prints)
- [x] check if haiku is viable for core agent loop (more likely for lean)
- [x] don't forget to record question.txt inherited from `apps` in the output dirs
- [ ] consider this weekend learning about huggingface and set up traversing the filesystem to turn outputs into huggingface dataset
- [ ] embarassing parallel (this should be done at shell level with `parallel` linux tool. ask claude)
- [ ] make indices fill, like 00001, 00020 instead of 1, 20
- [ ] need to put initial question in system prompt for caching (epistemic status: not 100% sure this is even cheaper)
- [x] resumes
- [ ] email zac for nepotism

# TODO from 27 Sep
- [ ] 2048 is necessary
- [ ] ask hypothesizer to only generate strategy tests, ignore unit test cases
- [ ] refactor restart, loops, indexing
- [ ] fix logging/conversation json overwriting


# Notes from 50/50 Generation
Running 50 examples (0-49) through preproc, then fvapps
Preproc
- 1 fail train, 3 fail test
- almost exactly $3.00 for total Sonnet 3.5 use
- about 625K tokens in, 77K tokens out
Fvapps
- train python 4 fail
- train lean 5 fail, broke on index 40 because no test_solution because preproc failed (TODO complete)
- test python hanging at 14 right now
- test lean TODO

- lots of hanging, some pytest hypotheses take forever
- we should maybe add timing to the pytests
- maybe also prompt eng for "fast" tests
- probably want to parallelize because of this
