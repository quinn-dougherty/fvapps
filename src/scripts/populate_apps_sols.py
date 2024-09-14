# run through and populate the solutions for the apps dataset
from pathlib import Path

from benchmark.apps_utils import load_hf_apps_dataset, write_solution_to_file

for split in ["train", "test"]:
    ds = load_hf_apps_dataset(split=split)
    for i in range(len(ds)):
        write_solution_to_file(ds, split, i, Path("."))
        if i > 3:
            break
