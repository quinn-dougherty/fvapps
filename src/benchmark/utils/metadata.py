import json
from pathlib import Path
from benchmark.utils.logger_setup import logging

METADATA_FILENAME = "metadata.json"


def write_metadata(path: Path, metadata: dict):
    with open(path / METADATA_FILENAME, "w") as f:
        json.dump(metadata, f, indent=4)


def read_metadata(path: Path) -> dict:
    with open(path / METADATA_FILENAME, "r") as f:
        return json.load(f)


def increment_preproc_loops(path: Path):
    metadata = read_metadata(path / METADATA_FILENAME)
    metadata["preproc_loops"] += 1
    write_metadata(path / METADATA_FILENAME, metadata)


def increment_python_loops(path: Path):
    metadata = read_metadata(path / METADATA_FILENAME)
    metadata["python_loops"] += 1
    write_metadata(path / METADATA_FILENAME, metadata)


def increment_lean_loops(path: Path):
    metadata = read_metadata(path / METADATA_FILENAME)
    metadata["lean_loops"] += 1
    write_metadata(path / METADATA_FILENAME, metadata)


def initialize_metadata(path: Path):
    logging.info(f"Initalizing metadata for {path}")
    metadata = {
        "preproc_loops": 0,
        "python_loops": 0,
        "lean_loops": 0,
    }
    write_metadata(path / METADATA_FILENAME, metadata)
