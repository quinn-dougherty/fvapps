import pathlib
import tomllib
from benchmark.apps_utils import (
    AppsPreprocAgent,
    construct_apps_paths,
    get_succinct_apps_datarow,
    load_hf_apps_dataset,
    setup_apps_directories,
)
from benchmark.prompting import AgentConfig
from scripts.config import preproc

with open("src/config.toml", "rb") as f:
    cfg = tomllib.load(f)


def run_AppsPreprocAgent(orig_apps_row, split: str):

    # get a sample succint row
    sample = get_succinct_apps_datarow(orig_apps_row)

    config = AgentConfig(**cfg["preproc"], **preproc)

    problem_path = construct_apps_paths(
        root_path=pathlib.Path("."),
        apps_row=orig_apps_row,
        split=split,
    )

    test_path = pathlib.Path(problem_path / "solution_clean.py")

    agent = AppsPreprocAgent(
        inp=sample,
        config=config,
        out=str(test_path),
    )

    final_exit_code = agent.loop_until_condition()

    print(agent.dump_full_chat_history())
    print("Was the final generation successful?", final_exit_code)
    return


def main():
    split = "train"
    ds = load_hf_apps_dataset(split=split)
    setup_apps_directories(pathlib.Path("."))
    run_AppsPreprocAgent(ds[0], split=split)
