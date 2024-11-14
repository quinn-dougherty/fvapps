import json
import jsonlines
import pathlib
from argparse import ArgumentParser

from datasets import load_dataset

from baselines import build_agent


def mk_parser() -> ArgumentParser:
    parser = ArgumentParser("FVApps Baselines")
    parser.add_argument(
        "--model",
        help="model name (default: sonnet)",
        type=str,
        default="sonnet",
        choices=["sonnet", "gpt-4o", "gemini", "prover-rl", "llama", "testhf"],
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
    parser.add_argument(
        "--theorem_start_idx",
        help="index to start proving theorems from",
        type=int,
        default=0,
    )
    parser.add_argument(
        "--max_theorems",
        help="maximum number of theorems to prove on top of defs",
        type=int,
        default=100,
    )
    parser.add_argument(
        "--dry_run",
        help="dry run",
        action="store_true",
    )
    return parser


def get_or_setup_metadata(output_folder: pathlib.Path, sample: dict) -> dict:

    output_folder.mkdir(parents=True, exist_ok=True)

    metadata_path = output_folder / "metadata.json"

    if metadata_path.exists():
        with open(metadata_path, "r") as f:
            metadata = json.load(f)
    else:
        metadata = {}
        metadata["total_attempts_made"] = 0

        lines = sample["spec"].split("\n\n")

        theorem_count = len(
            [
                lines[i]
                for i, statement in enumerate(lines)
                if statement.startswith("theorem")
            ]
        )
        def_count = len(
            [
                lines[i]
                for i, statement in enumerate(lines)
                if statement.startswith("def")
            ]
        )

        metadata["total_theorems_plus_defs"] = theorem_count + def_count
        metadata["total_theorems"] = theorem_count
        metadata["all_defs_proven"] = False
        metadata["defs_attempts"] = 0
        metadata["theorems_proven"] = 0

        for i in range(theorem_count):
            metadata[f"theorem_{i}_proven"] = False
            metadata[f"theorem_{i}_attempts"] = 0

        with open(metadata_path, "w") as f:
            json.dump(metadata, f, indent=4)

    return metadata


def lean_main(
    output_path: pathlib.Path,
    question: str,
    spec: str,
    debug_string: str,
    model: str,
):

    config_dict = {
        "debug_string": debug_string,
        "custom_stopping_condition": lambda stdout, returncode: "sorry" not in stdout,
        # "custom_stopping_condition": lambda stdout, returncode: True,
    }

    agent = build_agent(model, (question, spec), output_path, config_dict)

    result_flag, code, n_attempts = agent.loop()

    return result_flag, code, n_attempts


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
    output_folder_trunk = (
        pathlib.Path("artefacts") / "baselines" / args.model / args.split
    )

    for i in range(args.start_idx, args.end_idx + 1):
        if args.use_apps_ids:
            apps_idx = f"{i:04d}"
            try:
                samples = ds.to_pandas()
                samples.set_index("apps_id", inplace=True)
                sample = samples.loc[apps_idx]
            except KeyError:
                print(f"Apps ID {apps_idx} not found")
                continue
        else:
            try:
                sample = ds[i]  # type: ignore
                apps_idx = sample["apps_id"]
            except IndexError:
                print(f"Index {i} out of bounds for {args.split} split")
                continue

        if args.dry_run:
            print(f"Dry run for {apps_idx}")
            continue

        output_folder = output_folder_trunk / f"apps_id_{apps_idx}"
        metadata = get_or_setup_metadata(output_folder, sample)

        def_output_path = output_folder / f"Defs.lean"
        def_output_path_final = output_folder / f"Defs_final.lean"
        def_output_path_last = output_folder / f"{def_output_path.stem}_last.lean"

        # If not all defs have been proven, we need to run the proof for the defs
        if not metadata["all_defs_proven"]:
            if def_output_path_final.exists():
                with open(def_output_path_final, "r") as f:
                    code = f.read()
            elif def_output_path_last.exists():
                with open(def_output_path_last, "r") as f:
                    code = f.read()
            else:
                # we have never done anything with this app idx before
                code = def_extractor(sample["spec"])

            debug_string = f"sample {apps_idx} (all defs)"
            print(
                f"Running LEAN proof for APPS {debug_string} and outputting to {def_output_path}..."
            )
            result_flag, code, n_attempts = lean_main(
                def_output_path,
                sample["apps_question"],
                code,
                debug_string,
                args.model,
            )
            print(
                f"Was the final LEAN proof from {args.model} for {debug_string} successful? {result_flag}"
            )

            metadata["defs_attempts"] += n_attempts

            if result_flag:
                metadata["all_defs_proven"] = True

            with open(output_folder / "metadata.json", "w") as f:
                json.dump(metadata, f, indent=4)

        defs_final_output_path = output_folder / f"{def_output_path.stem}_final.lean"
        try:
            with open(defs_final_output_path, "r") as f:
                def_code = f.read()
        except FileNotFoundError:
            print(f"No Defs_final.lean found for {apps_idx}.")
            continue # move on to next apps id if range was specified in CLI args

        total_theorem_count = metadata["total_theorems"]

        for theorem_idx in range(
            args.theorem_start_idx, min(total_theorem_count, args.max_theorems)
        ):
            output_path = output_folder / f"Theorem_{theorem_idx}.lean"
            output_path_final = output_folder / f"Theorem_{theorem_idx}_final.lean"
            if output_path_final.exists() and metadata[f"theorem_{theorem_idx}_proven"]:
                continue

            output_last_path = output_folder / f"Theorem_{theorem_idx}_last.lean"
            if output_last_path.exists():
                with open(output_last_path, "r") as f:
                    code = f.read()
            else:
                theorem_spec = theorem_extractor(sample["spec"], theorem_idx)
                code = update_code(def_code, theorem_spec)

            debug_string = f"sample {apps_idx} (theorem {theorem_idx})"
            print(
                f"Running LEAN proof for APPS {debug_string} and outputting to {output_path}..."
            )

            result_flag, code, n_attempts = lean_main(
                output_path,
                sample["apps_question"],
                code,
                debug_string,
                args.model,
            )

            print(
                f"Was the final LEAN proof from {args.model} for {debug_string} successful? {result_flag}"
            )

            metadata[f"theorem_{theorem_idx}_attempts"] += n_attempts

            if result_flag:
                metadata[f"theorem_{theorem_idx}_proven"] = True
                metadata["theorems_proven"] += 1

            with open(output_folder / "metadata.json", "w") as f:
                json.dump(metadata, f, indent=4)
