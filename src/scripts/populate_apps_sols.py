# run through and populate the solutions for the apps dataset
from pathlib import Path

from benchmark.apps_utils import load_hf_apps_dataset
from scripts.apps_preproc import run_AppsPreprocAgent

for split in ["train", "test"]:
    ds = load_hf_apps_dataset(split=split)
    for i in range(len(ds)):
        run_AppsPreprocAgent(ds[i], split=split)
        if i > 3:
            break
