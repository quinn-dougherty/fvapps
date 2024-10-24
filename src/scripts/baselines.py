import pathlib
from argparse import ArgumentParser

from datasets import load_dataset

from baselines.types import AgentConfig
from baselines.anthropic_agent import ClaudeAgent
from baselines.openai_agent import OpenAIAgent
from baselines.huggingface_agent import HuggingFaceAgent
from scripts.baselines_config import (
    sonnet_cfg,
    o1_cfg,
    prover_rl_cfg,
    llama_cfg,
    testhf_cfg,
)


def mk_parser() -> ArgumentParser:
    parser = ArgumentParser("FVApps Baselines")
    parser.add_argument(
        "--model",
        help="model name (default: sonnet)",
        type=str,
        default="sonnet",
        choices=["sonnet", "o1-mini", "prover-rl", "llama", "testhf"],
    )
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


def lean_main(
    output_path: pathlib.Path,
    question: str,
    spec: str,
    apps_sample_idx: int,
    model: str,
):

    print(
        f"Running LEAN proof for APPS sample {apps_sample_idx} and outputting to {output_path}..."
    )
    match model:
        case "sonnet":
            agent = ClaudeAgent(
                input_context=(question, spec),
                output_path=output_path,
                config=AgentConfig(**sonnet_cfg, sample_idx=apps_sample_idx),
            )
        case "o1-mini":
            agent = OpenAIAgent(
                input_context=(question, spec),
                output_path=output_path,
                config=AgentConfig(**o1_cfg, sample_idx=apps_sample_idx),
            )
        case "prover-rl":
            agent = HuggingFaceAgent(
                input_context=(question, spec),
                output_path=output_path,
                config=AgentConfig(**prover_rl_cfg, sample_idx=apps_sample_idx),
            )
        case "llama":
            agent = HuggingFaceAgent(
                input_context=(question, spec),
                output_path=output_path,
                config=AgentConfig(**llama_cfg, sample_idx=apps_sample_idx),
            )
        case "testhf":
            agent = HuggingFaceAgent(
                input_context=(question, spec),
                output_path=output_path,
                config=AgentConfig(**testhf_cfg, sample_idx=apps_sample_idx),
            )
        case _:
            raise ValueError(f"Model argument {model} incorrect")
    final_exit_code = agent.loop()

    print(
        f"Was the final LEAN proof from {model} for sample {apps_sample_idx} successful? {final_exit_code}"
    )
    return


def main():
    parser = mk_parser()
    args = parser.parse_args()

    ds = load_dataset("quinn-dougherty/fvapps")
    output_folder = pathlib.Path("artefacts") / "baselines" / args.model / args.split
    output_folder.mkdir(parents=True, exist_ok=True)

    for i in range(args.start_idx, args.end_idx + 1):
        sample = ds[args.split][i]  # type: ignore
        apps_idx = sample["apps_id"]
        output_path = output_folder / f"Proof_{apps_idx}.Lean"

        lean_main(
            output_path, sample["apps_question"], sample["spec"], apps_idx, args.model
        )
