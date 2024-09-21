import json
from typing import Callable
from pathlib import Path
from benchmark.utils.logger_setup import logging

METADATA_FILENAME = "metadata.json"


def write_metadata(path: Path, metadata: dict):
    with open(path, "w") as f:
        json.dump(metadata, f, indent=4)


def read_metadata(path: Path) -> dict:
    with open(path, "r") as f:
        return json.load(f)


def mk_incrementor(item: str) -> Callable[[Path], None]:
    def increment(path: Path):
        metadata = read_metadata(path / METADATA_FILENAME)
        metadata[item]["loops"] += 1
        write_metadata(path / METADATA_FILENAME, metadata)

    return increment


increment_preproc_loops = mk_incrementor("preproc")
increment_python_loops = mk_incrementor("python")
increment_lean_loops = mk_incrementor("lean")


def mk_reader(item: str) -> Callable[[Path], dict]:
    def read(path: Path) -> dict:
        metadata = read_metadata(path / METADATA_FILENAME)
        return metadata[item]

    return read


read_preproc = mk_reader("preproc")
read_python = mk_reader("python")
read_lean = mk_reader("lean")


def mk_successfuler(item: str) -> Callable[[Path], None]:
    def successful(path: Path) -> None:
        metadata = read_metadata(path / METADATA_FILENAME)
        metadata[item]["latest_run_success"] = True
        write_metadata(path / METADATA_FILENAME, metadata)

    return successful


successfuler_preproc = mk_successfuler("preproc")
successfuler_python = mk_successfuler("python")
successfuler_lean = mk_successfuler("lean")


def initialize_metadata(path: Path):
    """Writes fresh metadata object to file, does nothing if already exists."""
    metadata = {
        "preproc": {"loops": 0, "latest_run_success": False},
        "python": {"loops": 0, "latest_run_success": False},
        "lean": {"loops": 0, "latest_run_success": False},
    }
    if not (path / METADATA_FILENAME).exists():
        logging.info(f"Initalizing metadata for {path}")
        write_metadata(path / METADATA_FILENAME, metadata)
