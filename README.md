# FV-APPS

Lifting [APPS](https://github.com/hendrycks/apps) to Lean with LLM-generated theorem statements.

[HuggingFace](https://huggingface.co/datasets/quinn-dougherty/fvapps):
``` python
datasets.load_dataset("quinn-dougherty/fvapps")
```

## How to regenerate the benchmark

### Setup

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

### Preprocess

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

### Spec generation

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

### Postprocess

The last thing is to trim up the artefacts to their huggingface form.
```
rye run postprocess
```

## Reproducing our baselines

```
$ rye run baselines

TODO : insert `--help` here
```

# Notes/misc

## Notes from 50/50 Generation
Running 50 examples (0-49) through preproc, then fvapps
**Preproc**
- 1 fail train, 3 fail test
- almost exactly $3.00 for total Sonnet 3.5 use
- about 625K tokens in, 77K tokens out
**Fvapps**
- train python 4 fail
- train lean 5 fail, broke on index 40 because no test_solution because preproc failed (TODO complete)
- test python hanging at 14 right now
- test lean TODO
- lots of hanging, some pytest hypotheses take forever
- we should maybe add timing to the pytests
- maybe also prompt eng for "fast" tests
- probably want to parallelize because of this
