import pathlib
from argparse import ArgumentParser

from benchmark.agent.agents import AppsPreprocAgent
from benchmark.agent.types import AgentConfig
from benchmark.utils.apps import (
    construct_apps_paths,
    get_succinct_apps_datarow,
    load_hf_apps_dataset,
    setup_apps_directories,
)
from scripts.config import preproc


def mk_parser():
    parser = ArgumentParser()
    parser.add_argument(
        "--split",
        help="Train or test split. Default: train.",
        type=str,
        choices=["train", "test"],
        default="train",
    )
    parser.add_argument(
        "--start_idx", help="Start index for the dataset.", type=int, default=0
    )
    parser.add_argument(
        "--end_idx",
        help="End index for the dataset (inclusive).",
        type=int,
        default=int(1e4 / 2),
    )
    return parser


def run_AppsPreprocAgent(orig_apps_row, split: str):

    # get a sample succint row
    sample = get_succinct_apps_datarow(orig_apps_row)

    config = AgentConfig(**preproc, sample_idx=sample["problem_id"])

    problem_path = construct_apps_paths(
        root_path=pathlib.Path("."),
        apps_row=orig_apps_row,
        split=split,
    )
    # Write the sample question to a file
    with open(problem_path / "question.txt", "w") as f:
        f.write(sample["problem_statement"])

    with open(problem_path / "difficulty.txt", "w") as f:
        f.write(sample["difficulty"])

    test_path = problem_path / "solution_clean.py"

    agent = AppsPreprocAgent(
        input_context="",  # not used in this agent
        output_path=test_path,
        config=config,
        sample=sample,
    )

    final_exit_code = agent.loop()

    # print(agent.dump_full_chat_history())
    print("Was the final generation successful?", final_exit_code)
    return


def main():
    parser = mk_parser()
    args = parser.parse_args()
    split = args.split
    ds = load_hf_apps_dataset(split=split)
    print("Loaded APPS dataset to memory...")
    setup_apps_directories(pathlib.Path("."))
    for i in range(args.start_idx, args.end_idx + 1):
        print("Processing sample", i)
        run_AppsPreprocAgent(ds[i], split=split)  # type: ignore


if __name__ == "__main__":
    main()
