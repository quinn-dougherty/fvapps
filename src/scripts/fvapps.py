"""The generation of the benchmark."""

import pathlib
from argparse import ArgumentParser
from benchmark.agent.types import AgentConfig
from benchmark.agent.hypothesizer import PythonAgent
from benchmark.agent.sorryer import LeanAgent
from scripts.config import leancfg, pythoncfg

EXAMPLE = "string"


def mk_parser() -> ArgumentParser:
    parser = ArgumentParser("FV-APPS full generation run")
    parser.add_argument(
        "--split",
        help="train or test (default: train)",
        type=lambda s: s if s == "train" or s == "test" else None,
        default="train",
    )
    parser.add_argument(
        "--start_idx", help="index to start pulling from apps", type=int, default=0
    )
    parser.add_argument(
        "--end_idx",
        help="index to end pulling from apps",
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
        inp=content,
        out=out_path,
        config=AgentConfig(**pythoncfg, sample_idx=sample_idx),
    )
    final_exit_code = agent.loop()

    # print(agent.dump_full_chat_history())
    print(
        f"Was the final PYTHON generation for sample {sample_idx} successful? {final_exit_code}"
    )
    return


def lean_main(in_path, out_path, sample_idx):

    with open(in_path, "r") as f:
        content = f.read()

    agent = LeanAgent(
        inp=content, out=out_path, config=AgentConfig(**leancfg, sample_idx=sample_idx)
    )
    final_exit_code = agent.loop()

    # print(agent.dump_full_chat_history())
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
        for i in range(args.start_idx, args.end_idx):
            inp_python_path = root_path / str(i) / "solution_clean.py"
            out_hyp_path = root_path / str(i) / "test_solution.py"

            python_main(inp_python_path, out_hyp_path, i)

    if args.skip_lean:
        for i in range(args.start_idx, args.end_idx):
            out_hyp_path = root_path / str(i) / "test_solution.py"
            out_lean_path = root_path / str(i) / "Spec.lean"

            lean_main(out_hyp_path, out_lean_path, i)
