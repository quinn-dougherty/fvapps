import pathlib
from argparse import ArgumentParser

from datasets import load_dataset

from baselines.anthropic_agent import ClaudeAgent
from baselines.google_agent import GoogleAgent
from baselines.huggingface_agent import HuggingFaceAgent
from baselines.openai_agent import OpenAIAgent
from baselines.types import AgentConfig, BaselineAgent
from scripts.baselines_config import (
    gemini_cfg,
    llama_cfg,
    o1_cfg,
    prover_rl_cfg,
    sonnet_cfg,
    testhf_cfg,
)


def mk_parser() -> ArgumentParser:
    parser = ArgumentParser("FVApps Baselines")
    parser.add_argument(
        "--model",
        help="model name (default: sonnet)",
        type=str,
        default="sonnet",
        choices=["sonnet", "o1-mini", "gemini", "prover-rl", "llama", "testhf"],
    )
    parser.add_argument(
        "--split",
        help="train (default: train)",
        type=str,
        choices=["train"],
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
        "--use_apps_ids",
        help="use apps ids instead of indices",
        action="store_true",
    )
    return parser


def lean_main(
    output_path: pathlib.Path,
    question: str,
    spec: str,
    debug_string: str,
    model: str,
):

    agent: BaselineAgent

    config_dict = {
        "debug_string": debug_string,
        "custom_stopping_condition": lambda stdout, returncode: "sorry" not in stdout,
        # "custom_stopping_condition": lambda stdout, returncode: True,
    }

    match model:
        case "sonnet":
            agent = ClaudeAgent(
                input_context=(question, spec),
                output_path=output_path,
                config=AgentConfig(**(sonnet_cfg | config_dict)),
            )
        case "o1-mini":
            agent = OpenAIAgent(
                input_context=(question, spec),
                output_path=output_path,
                config=AgentConfig(**(o1_cfg | config_dict)),
            )
        case "gemini":
            agent = GoogleAgent(
                input_context=(question, spec),
                output_path=output_path,
                config=AgentConfig(**(gemini_cfg | config_dict)),
            )
        case "prover-rl":
            agent = HuggingFaceAgent(
                input_context=(question, spec),
                output_path=output_path,
                config=AgentConfig(**(prover_rl_cfg | config_dict)),
            )
        case "llama":
            agent = HuggingFaceAgent(
                input_context=(question, spec),
                output_path=output_path,
                config=AgentConfig(**(llama_cfg | config_dict)),
            )
        case "testhf":
            agent = HuggingFaceAgent(
                input_context=(question, spec),
                output_path=output_path,
                config=AgentConfig(**(testhf_cfg | config_dict)),
            )
        case _:
            raise ValueError(f"Model argument {model} incorrect")
    final_exit_code, code = agent.loop()

    return final_exit_code, code


def def_extractor(spec: str) -> str:
    """
    This function extracts all definitions in the spec (assumes defs are at the start and first theorem statements ends defs)
    """
    first_theorem_pos = spec.find("theorem")
    return spec[:first_theorem_pos]


def theorem_extractor(spec: str, theorem_idx: int) -> str:
    """
    This function extracts all definitions alongside the theorem at the given index
    """
    lines = spec.split("\n\n")

    theorem_starts = [
        lines[i] for i, statement in enumerate(lines) if statement.startswith("theorem")
    ]

    thm_lines = [theorem_starts[theorem_idx]]
    for line in lines[lines.index(theorem_starts[theorem_idx]) + 1 :]:
        if line.startswith("theorem"):
            break
        thm_lines.append(line)
    theorem = "\n".join(thm_lines)

    return theorem


def update_code(code: str, theorem_spec: str) -> str:
    return code + "\n\n" + theorem_spec


def main():
    parser = mk_parser()
    args = parser.parse_args()

    ds = load_dataset("quinn-dougherty/fvapps", split=args.split)
    output_folder = pathlib.Path("artefacts") / "baselines" / args.model / args.split
    output_folder.mkdir(parents=True, exist_ok=True)

    for i in range(args.start_idx, args.end_idx + 1):

        if args.use_apps_ids:
            sample = ds.to_pandas()
            sample.set_index("apps_id", inplace=True)
            sample = sample.loc[f"{i:04d}"]
            apps_idx = i
        else:
            sample = ds[i]  # type: ignore
            apps_idx = sample["apps_id"]

        def_spec = def_extractor(sample["spec"])

        output_path = output_folder / f"Defs_{apps_idx}.Lean"

        debug_string = f"sample {apps_idx} (defs)"
        print(
            f"Running LEAN proof for APPS sample {debug_string} and outputting to {output_path}..."
        )
        final_exit_code, code = lean_main(
            output_path, sample["apps_question"], def_spec, debug_string, args.model
        )
        print(
            f"Was the final LEAN proof from {args.model} for {debug_string} successful? {final_exit_code}"
        )

        code = output_path.read_text()

        # wipe any theorems added previously
        code = def_extractor(code)

        total_theorem_count = sample["spec"].count("theorem")

        for theorem_idx in range(total_theorem_count):
            theorem_spec = theorem_extractor(sample["spec"], theorem_idx)
            code = update_code(code, theorem_spec)

            output_path = output_folder / f"Proof_{apps_idx}_Theorem_{theorem_idx}.Lean"

            debug_string = f"sample {apps_idx} (theorem {theorem_idx})"
            print(
                f"Running LEAN proof for APPS sample {debug_string} and outputting to {output_path}..."
            )

            final_exit_code, code = lean_main(
                output_path,
                sample["apps_question"],
                code,
                debug_string,
                args.model,
            )

            print(
                f"Was the final LEAN proof from {args.model} for {debug_string} successful? {final_exit_code}"
            )
