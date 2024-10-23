"""Turning the output artefacts into a huggingface form"""

import jsonlines
from pathlib import Path
from typing import Any
from benchmark.utils.logger_setup import logging
from benchmark.utils.metadata import read_lean

ARTEFACTS = Path("artefacts")


def read_file_content(file_path: Path) -> str:
    """Read and return the content of a file."""
    with open(file_path, "r") as f:
        return f.read()


def process_benchmark_item(idx_dir: Path, split: str) -> dict[str, str] | None:
    """Process a single benchmark item and return its data as a dictionary."""
    if not read_lean(idx_dir)["latest_run_success"]:
        return None
    spec_file = idx_dir / "Spec.lean"
    question_file = idx_dir / "question.txt"
    difficulty_file = idx_dir / "difficulty.txt"
    keep_file = idx_dir / "keep.txt"

    with open(keep_file, "r") as f:
        if not int(f.read()):
            return None

    return {
        "apps_id": idx_dir.name,
        "apps_question": read_file_content(question_file),
        "spec": read_file_content(spec_file),
        "apps_difficulty": read_file_content(difficulty_file),
        "split": split,
    }


def process_split(split: str, split_dir: Path) -> list[dict[str, str]]:
    """Process all items in a split directory."""
    return [
        item
        for idx_dir in split_dir.iterdir()
        if idx_dir.is_dir()
        and (item := process_benchmark_item(idx_dir, split)) is not None
    ]


def process_benchmark(base_dir: Path) -> dict[str, list[dict[str, Any]]]:
    """Process the entire benchmark dataset."""
    return {
        split: process_split(split, base_dir / "apps" / split)
        for split in ["train", "test"]
    }


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

    write_jsonl(output_dir / "train.jsonl", data["train"])
    write_jsonl(output_dir / "test.jsonl", data["test"])

    copy_readme(output_dir)

    if verbose_stdout:
        print(f"Conversion complete. Output saved to {output_dir}")
