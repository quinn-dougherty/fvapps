"""The generation of the benchmark."""

import pathlib
from argparse import ArgumentParser

from benchmark.agent.agents import LeanAgent, PythonAgent
from benchmark.agent.types import AgentConfig
from scripts.config import leancfg, pythoncfg

EXAMPLE = "string"


def mk_parser() -> ArgumentParser:
    parser = ArgumentParser("FV-APPS full generation run")
    parser.add_argument(
        "--split",
        help="train or test (default: train)",
        type=str,
        choices=["train", "test"],
        default="train",
    )
    parser.add_argument(
        "--start_idx", help="index to start pulling from apps", type=int, default=0
    )
    parser.add_argument(
        "--end_idx",
        help="index to end pulling from apps (inclusive)",
        type=int,
        default=int(1e4 / 2),
    )
    parser.add_argument(
        "--skip_lean", action="store_false", help="skips lean when present"
    )
    parser.add_argument(
        "--skip_python", action="store_false", help="skips python when present"
    )
    return parser


def python_main(in_path, out_path, sample_idx):

    with open(in_path, "r") as f:
        content = f.read()

    agent = PythonAgent(
        input_context=content,
        output_path=out_path,
        config=AgentConfig(**pythoncfg, sample_idx=sample_idx),
    )
    final_exit_code = agent.loop()

    print(
        f"Was the final PYTHON generation for sample {sample_idx} successful? {final_exit_code}"
    )
    return


def lean_main(in_path, out_path, sample_idx):

    try:
        with open(in_path, "r") as f:
            content = f.read()
    except FileNotFoundError as e:
        print(
            f"Python generation failed, unable to find test_solution.py for sample {sample_idx}"
        )
        print(
            f"Was the final LEAN generation for sample {sample_idx} successful? False"
        )
        return

    agent = LeanAgent(
        input_context=content,
        output_path=out_path,
        config=AgentConfig(**leancfg, sample_idx=sample_idx),
    )
    final_exit_code = agent.loop()

    print(
        f"Was the final LEAN generation for sample {sample_idx} successful? {final_exit_code}"
    )
    return


def main():
    """assumes you ran scripts/apps_preproc on all samples"""
    # get path to artefacts/apps data, after choosing a split
    parser = mk_parser()
    args = parser.parse_args()
    root_path = pathlib.Path("artefacts") / "apps" / args.split

    if args.skip_python:
        for i in range(args.start_idx, args.end_idx + 1):
            idx = f"{i:04d}"
            inp_python_path = root_path / idx / "solution_clean.py"
            out_hyp_path = root_path / idx / "test_solution.py"

            python_main(inp_python_path, out_hyp_path, i)

    if args.skip_lean:
        for i in range(args.start_idx, args.end_idx + 1):
            idx = f"{i:04d}"
            out_hyp_path = root_path / idx / "test_solution.py"
            out_lean_path = root_path / idx / "Spec.lean"

            lean_main(out_hyp_path, out_lean_path, i)


if __name__ == "__main__":
    main()
