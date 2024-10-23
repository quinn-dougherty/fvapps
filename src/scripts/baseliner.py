import pathlib
from argparse import ArgumentParser

from datasets import load_dataset

from baselines.agents import AgentConfig
from baselines.anthropic_agent import ClaudeAgent
from baselines.config import claudebaselinecfg, o4_minibaselinecfg
from baselines.openai_agent import OpenAIAgent


def mk_parser() -> ArgumentParser:
    parser = ArgumentParser("FVApps Baseliner")
    parser.add_argument(
        "--model",
        help="model name (default: claude-3.5-sonnet)",
        type=str,
        default="claude-3.5-sonnet",
        choices=["claude-3.5-sonnet", "o1-mini"],
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


def lean_main(output_path, question, spec, apps_sample_idx, model):

    print(
        f"Running LEAN proof for APPS sample {apps_sample_idx} and outputting to {output_path}..."
    )
    if model == "claude-3.5-sonnet":
        agent = ClaudeAgent(
            input_context=(question, spec),
            output_path=output_path,
            config=AgentConfig(**claudebaselinecfg, sample_idx=apps_sample_idx),
        )
    elif model == "o1-mini":
        agent = OpenAIAgent(
            input_context=(question, spec),
            output_path=output_path,
            config=AgentConfig(**o4_minibaselinecfg, sample_idx=apps_sample_idx),
        )
    final_exit_code = agent.loop()

    print(
        f"Was the final LEAN proof from Sonnet 3.5 for sample {apps_sample_idx} successful? {final_exit_code}"
    )
    return


def main():
    parser = mk_parser()
    args = parser.parse_args()

    ds = load_dataset("quinn-dougherty/fvapps")
    output_folder = pathlib.Path("artefacts") / "baselines" / args.model / args.split
    output_folder.mkdir(parents=True, exist_ok=True)

    for i in range(args.start_idx, args.end_idx + 1):
        sample = ds[args.split][i]
        apps_idx = sample["apps_id"]
        output_path = output_folder / f"Proof_{apps_idx}.Lean"

        lean_main(
            output_path, sample["apps_question"], sample["spec"], apps_idx, args.model
        )


if __name__ == "__main__":
    main()
