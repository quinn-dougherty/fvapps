"""A basic baseline using Claude 3.5 Sonnet."""

import pathlib
from argparse import ArgumentParser

from baselines.agents import AgentConfig, BaselineAgent
from scripts.config import baselinecfg


def mk_parser() -> ArgumentParser:
    parser = ArgumentParser("Baseline Claude 3.5 Sonnet")
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
    return parser


def lean_main(in_path, out_path, sample_idx):

    try:
        with open(in_path, "r") as f:
            content = f.read()
    except FileNotFoundError as e:
        print(
            f"Baseline generation failed, unable to find Spec.lean for sample {sample_idx} at {in_path}"
        )
        print(
            f"Was the final proof generation for sample {sample_idx} successful? False"
        )
        return

    agent = BaselineAgent(
        input_context=content,
        output_path=out_path,
        config=AgentConfig(**baselinecfg, sample_idx=sample_idx),
    )
    final_exit_code = agent.loop()

    print(
        f"Was the final LEAN generation for sample {sample_idx} successful? {final_exit_code}"
    )
    return


def main():
    parser = mk_parser()
    args = parser.parse_args()
    root_path = pathlib.Path("artefacts") / "apps" / args.split

    for i in range(args.start_idx, args.end_idx + 1):
        idx = f"{i:04d}"
        in_spec_path = root_path / idx / "Spec.lean"
        out_proof_path = root_path / idx / "Proof.lean"

        lean_main(in_spec_path, out_proof_path, i)


if __name__ == "__main__":
    main()
