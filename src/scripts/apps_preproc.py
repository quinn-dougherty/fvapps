import pathlib
from benchmark.utils.apps import (
    construct_apps_paths,
    get_succinct_apps_datarow,
    load_hf_apps_dataset,
    setup_apps_directories,
)
from benchmark.agent.types import AgentConfig
from benchmark.agent.preprocesser import AppsPreprocAgent
from scripts.config import preproc


def run_AppsPreprocAgent(orig_apps_row, split: str):

    # get a sample succint row
    sample = get_succinct_apps_datarow(orig_apps_row)

    config = AgentConfig(**preproc, sample_idx=sample["problem_id"])

    problem_path = construct_apps_paths(
        root_path=pathlib.Path("."),
        apps_row=orig_apps_row,
        split=split,
    )

    test_path = pathlib.Path(problem_path / "solution_clean.py")

    agent = AppsPreprocAgent(
        inp="",  # not used in this agent,
        config=config,
        out=str(test_path),
        sample=sample,
    )

    final_exit_code = agent.loop()

    print(agent.dump_full_chat_history())
    print("Was the final generation successful?", final_exit_code)
    return


def test():
    split = "train"
    ds = load_hf_apps_dataset(split=split)
    setup_apps_directories(pathlib.Path("."))
    run_AppsPreprocAgent(ds[0], split=split)


def main_all():
    for split in ["train", "test"]:
        ds = load_hf_apps_dataset(split=split)
        for i in range(len(ds)):
            run_AppsPreprocAgent(ds[i], split=split)
