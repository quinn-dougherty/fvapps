from pathlib import Path
from argparse import ArgumentParser
from benchmark.agent.types import AgentConfig
from benchmark.testing.qa_config import sonnet_cfg as sonnet_qa_cfg
from benchmark.testing.agent import QaAgent


def mk_parser() -> ArgumentParser:
    parser = ArgumentParser("FVAPPS QA with autoformalization")
    parser.add_argument(
        "--split",
        help="train or test from apps",
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
    return parser


# TODO: handle resets
def autoformalize(py_soln_clean: str, out_path: Path, sample_idx: int):

    with open(py_soln_clean, "r") as f:
        content = f.read()

    agent = QaAgent(
        input_context=content,
        output_path=out_path,
        config=AgentConfig(**sonnet_qa_cfg, sample_idx=sample_idx),
        check_previous_stage=False,
    )
    final_exit_code = agent.loop()
    print(
        f"Was the final QA generation for sample {sample_idx} successful? {final_exit_code}"
    )
    return


def one():
    """Assumes `solution_clean.py` exists for all samples"""
    args = mk_parser().parse_args()
    root_path = Path("artefacts") / "apps" / args.split
    for sample_idx in range(args.start_idx, args.end_idx + 1):
        idx = f"{sample_idx:04d}"
        py_soln_clean = root_path / idx / "solution_clean.py"
        out_path = root_path / idx / "SpecQA.lean"
        autoformalize(py_soln_clean, out_path, sample_idx)


def two():
    pass
