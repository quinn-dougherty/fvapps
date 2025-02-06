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


def initialize_metadata(path: Path):
    """
    Writes fresh metadata object to file, does nothing if already exists. This does not initialize QA features.
    """
    metadata = {
        "preproc": {"loops": 0, "latest_run_success": False},
        "python": {"loops": 0, "latest_run_success": False},
        "lean": {"loops": 0, "latest_run_success": False},
        "unit": {"loops": -1, "latest_run_success": False},
        "plausible_theorems": [],
    }
    if not (path / METADATA_FILENAME).exists():
        logging.info(f"Initalizing metadata for {path}")
        write_metadata(path / METADATA_FILENAME, metadata)


def unit_reinitialize_metadata(path: Path):
    """
    since all the metadata files were initialized without unit object, this function will add the unit object to the metadata file
    """
    if not (path / METADATA_FILENAME).exists():
        initialize_metadata(path)
    else:
        metadata = read_metadata(path / METADATA_FILENAME)
        if "unit" not in metadata:
            metadata["unit"] = {"loops": 0, "latest_run_success": False}
            write_metadata(path / METADATA_FILENAME, metadata)


def mk_incrementor(item: str) -> Callable[[Path], None]:
    def increment(path: Path):
        metadata = read_metadata(path / METADATA_FILENAME)
        metadata[item]["loops"] += 1
        write_metadata(path / METADATA_FILENAME, metadata)

    return increment


increment_preproc_loops = mk_incrementor("preproc")
increment_python_loops = mk_incrementor("python")
increment_lean_loops = mk_incrementor("lean")
increment_unit_loops = mk_incrementor("unit")


def mk_reader(item: str) -> Callable[[Path], dict]:
    def read(path: Path) -> dict:
        metadata = read_metadata(path / METADATA_FILENAME)
        return metadata[item]

    return read


read_preproc = mk_reader("preproc")
read_python = mk_reader("python")
read_lean = mk_reader("lean")
read_unit = mk_reader("unit")


def mk_successfuler(item: str) -> Callable[[Path], None]:
    def successful(path: Path) -> None:
        metadata = read_metadata(path / METADATA_FILENAME)
        metadata[item]["latest_run_success"] = True
        write_metadata(path / METADATA_FILENAME, metadata)

    return successful


successfuler_preproc = mk_successfuler("preproc")
successfuler_python = mk_successfuler("python")
successfuler_lean = mk_successfuler("lean")
successfuler_unit = mk_successfuler("unit")


def set_qa_unit_success(path: Path, success: bool):
    metadata = read_metadata(path / METADATA_FILENAME)
    metadata["qa_unit_success"] = success
    write_metadata(path / METADATA_FILENAME, metadata)


def set_qa_plausible_theorems(path: Path, theorems: list):
    metadata = read_metadata(path / METADATA_FILENAME)
    metadata["plausible_theorems"] = theorems
    write_metadata(path / METADATA_FILENAME, metadata)


def read_qa_plausible_theorems(path: Path):
    metadata = read_metadata(path / METADATA_FILENAME)
    try:
        return metadata["plausible_theorems"]
    except KeyError:
        return []


def read_keep(path: Path) -> bool:
    with open(path / "keep.txt", "r") as f:
        return bool(int(f.read()))


def set_keep(path: Path, keep: bool):
    with open(path / "keep.txt", "w") as f:
        f.write(str(int(keep)))
