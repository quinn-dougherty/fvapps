from pathlib import Path
from argparse import ArgumentParser
from benchmark.agent.types import AgentConfig
from benchmark.testing.qa_config import sonnet_cfg as sonnet_qa_cfg
from benchmark.testing.agent import QaAgentUnit
from benchmark.testing.plausibility import QaPlausibility


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
def autoformalize(py_soln_clean: Path, out_path: Path, sample_idx: int) -> bool:
    with open(py_soln_clean, "r") as f:
        content = f.read()

    # First stage: Unit testing QA
    unit_agent = QaAgentUnit(
        input_context=content,
        output_path=out_path,
        config=AgentConfig(**sonnet_qa_cfg, sample_idx=sample_idx),
        check_previous_stage=False,
    )
    unit_success = unit_agent.loop()
    print(
        f"Was the unit QA generation for sample {sample_idx} successful? {unit_success}"
    )

    return unit_success


def plausibilize(spec_path: Path, out_path: Path, sample_idx: int) -> bool:
    with open(spec_path / "SpecQA.lean", "r") as f:
        spec_qa = f.read()
    with open(spec_path / "Spec.lean", "r") as f:
        spec = f.read()
    # Second stage: Plausibility testing QA
    plausibility = QaPlausibility(
        spec=spec,
        spec_qa=spec_qa,
        output_path=out_path,
    )
    plausible_success = plausibility.loop()
    print(
        f"Was the plausibility QA for sample {sample_idx} successful? {plausible_success}"
    )
    return plausible_success


def one():
    """Assumes `solution_clean.py` exists for all samples"""
    args = mk_parser().parse_args()
    root_path = Path("artefacts") / "apps" / args.split
    for sample_idx in range(args.start_idx, args.end_idx + 1):
        idx = f"{sample_idx:04d}"
        py_soln_clean = root_path / idx / "solution_clean.py"
        out_path = root_path / idx / "SpecQA.lean"
        try:
            success = autoformalize(py_soln_clean, out_path, sample_idx)
        except Exception as e:
            print(e)
            continue
        if not success:
            with open(root_path / idx / "keep.txt", "w") as f:
                f.write("0")


def two():
    """Assumes `SpecQA.lean` exists for all samples"""
    args = mk_parser().parse_args()
    root_path = Path("artefacts") / "apps" / args.split
    for sample_idx in range(args.start_idx, args.end_idx + 1):
        idx = f"{sample_idx:04d}"
        spec_path = root_path / idx
        out_path = root_path / idx / "SpecQAPlsbl.lean"
        try:
            success = plausibilize(spec_path, out_path, sample_idx)
        except Exception as e:
            print(e)
            continue
        if not success:
            with open(root_path / idx / "keep.txt", "w") as f:
                f.write("0")
