"""Turning the output artefacts into a huggingface form"""

import jsonlines
from pathlib import Path
from typing import Any
from benchmark.testing.convert_units import convert_tests_file
from benchmark.utils.logger_setup import logging
from benchmark.utils.metadata import read_lean, read_unit, read_qa_plausible_theorems
from benchmark.postprocessing.metadata import count_sorries

ARTEFACTS = Path("artefacts")

ASSURED_NAME = "guarded_and_plausible"
SEMIASSURED_NAME = "guarded"
UNASSURED_NAME = "unguarded"
SPLIT = "train"


def read_file_content(file_path: Path) -> str:
    """Read and return the content of a file."""
    with open(file_path, "r") as f:
        return f.read()


def _process_benchmark_item(
    name: str,
    apps_question: str,
    spec: str,
    soln_py: Path,
    sorries: int,
    apps_difficulty: str,
    assurance_level: str,
) -> dict[str, str | int]:
    try:
        units = convert_tests_file(soln_py)
    except Exception as e:
        logging.error(f"Error converting tests for {name}: {e}")
        units = ""
    return {
        "apps_id": name,
        "apps_question": apps_question,
        "spec": spec,
        "units": units,
        "sorries": sorries,
        "apps_difficulty": apps_difficulty,
        "assurance_level": assurance_level,
    }


def process_benchmark_assured_item(idx_dir: Path) -> dict[str, str | int]:
    """
    Process a single benchmark item and return its data as a dictionary.
    Assumes corresponding keep.txt = 1
    """
    spec_file = idx_dir / "Spec.lean"
    question_file = idx_dir / "question.txt"
    difficulty_file = idx_dir / "difficulty.txt"
    sorries = count_sorries(idx_dir)
    return _process_benchmark_item(
        idx_dir.name,
        read_file_content(question_file),
        read_file_content(spec_file),
        idx_dir / "solution_clean.py",
        sorries,
        read_file_content(difficulty_file),
        ASSURED_NAME,
    )


def process_benchmark_semiassured_item(idx_dir: Path) -> dict[str, str | int]:
    """
    Process a single benchmark item and return its data as a dictionary.
    Assumes corresponding metadata["lean"]["latest_run_success"] = True
    """
    spec_file = idx_dir / "Spec.lean"
    question_file = idx_dir / "question.txt"
    difficulty_file = idx_dir / "difficulty.txt"
    sorries = count_sorries(idx_dir)

    return _process_benchmark_item(
        idx_dir.name,
        read_file_content(question_file),
        read_file_content(spec_file),
        idx_dir / "solution_clean.py",
        sorries,
        read_file_content(difficulty_file),
        SEMIASSURED_NAME,
    )


def process_benchmark_unassured_item(idx_dir: Path) -> dict[str, str | int] | None:
    """
    Process a single benchmark item and return its data as a dictionary.
    Assumes corresponding keep.txt = 0
    """
    if not read_lean(idx_dir)["latest_run_success"]:
        return None
    spec_file = idx_dir / "Spec.lean"
    question_file = idx_dir / "question.txt"
    difficulty_file = idx_dir / "difficulty.txt"
    sorries = count_sorries(idx_dir)

    return _process_benchmark_item(
        idx_dir.name,
        read_file_content(question_file),
        read_file_content(spec_file),
        idx_dir / "solution_clean.py",
        sorries,
        read_file_content(difficulty_file),
        UNASSURED_NAME,
    )


def process_benchmark_item(idx_dir: Path) -> dict[str, str | int] | None:
    """Process a single benchmark item and return its data as a dictionary."""
    keep = read_file_content(idx_dir / "keep.txt")
    plausible_theorems = read_qa_plausible_theorems(idx_dir)
    unit_success = read_unit(idx_dir)["latest_run_success"]
    if keep and plausible_theorems and unit_success:
        return process_benchmark_assured_item(idx_dir)
    if unit_success:
        return process_benchmark_semiassured_item(idx_dir)
    return process_benchmark_unassured_item(idx_dir)


def process_split(split_dir: Path) -> list[dict[str, str]]:
    """Process all items in a split directory."""
    dirs = sorted(split_dir.iterdir(), key=lambda x: int(x.name))
    return [
        item
        for idx_dir in dirs
        if idx_dir.is_dir() and (item := process_benchmark_item(idx_dir)) is not None
    ]


def process_benchmark(base_dir: Path) -> dict[str, list[dict[str, Any]]]:
    """Process the entire benchmark dataset."""
    return {SPLIT: process_split(base_dir / "apps" / SPLIT)}


def write_jsonl(output_file: Path, data: list[dict[str, Any]]) -> None:
    """Write data to a JSONLines file."""
    with jsonlines.open(output_file, mode="w") as writer:
        writer.write_all(data)


def copy_readme(output_dir: Path) -> None:
    """Copy README.fvapps.md to the output directory as README.md."""
    source_file = Path("./src") / "benchmark" / "postprocessing" / "README.fvapps.md"
    dest_file = output_dir / "README.md"
    dest_file.write_text(source_file.read_text())


def convert_to_jsonl(
    base_dir: str | Path = ARTEFACTS, verbose_stdout: bool = True
) -> None:
    """Convert benchmark data to JSONLines format."""
    base_path = Path(base_dir) if isinstance(base_dir, str) else base_dir
    output_dir = base_path / "fvapps"
    output_dir.mkdir(parents=True, exist_ok=True)

    data = process_benchmark(base_path)

    write_jsonl(output_dir / f"{SPLIT}.jsonl", data[SPLIT])
    copy_readme(output_dir)

    if verbose_stdout:
        print(f"Conversion complete. Output saved to {output_dir}")
