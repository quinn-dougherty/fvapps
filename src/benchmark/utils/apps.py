from ast import literal_eval
from pathlib import Path
from datasets import Dataset, load_dataset  # type: ignore


HF_DATASET_PATH = "codeparrot/apps"

ALL_DIFFICULTIES = ["introductory", "interview", "competition"]

# Maximum number of characters to include in the test cases
# Some of the test cases are too long to be included in context windows
MAX_CHAR_TEST_CASES = 100_000


def load_hf_apps_dataset(split: str = "train", difficulties: list = ALL_DIFFICULTIES):
    return load_dataset(HF_DATASET_PATH, split=split, difficulties=difficulties)


def get_single_apps_solution(apps_row: dict) -> str:
    sols = literal_eval(apps_row["solutions"])
    if isinstance(sols, list):
        return sols[0]
    else:
        return sols


def get_succinct_apps_datarow(apps_row: dict) -> dict:
    return {
        "problem_id": apps_row["problem_id"],
        "problem_statement": apps_row["question"],
        "solution": get_single_apps_solution(apps_row),
        "test_cases": apps_row["input_output"][:MAX_CHAR_TEST_CASES],
        "difficulty": apps_row["difficulty"],
    }


def dump_solution_to_file(solution: str, path: Path):
    """Write a solution to a file."""
    with open(path, "w") as f:
        f.write(solution)
    return path


def setup_apps_directories(root_path: Path):
    """Set up the directories for the apps."""
    for split in ["train", "test"]:
        split_path = Path(root_path / "artefacts" / "apps" / split)
        split_path.mkdir(parents=True, exist_ok=True)


def construct_apps_paths(root_path: Path, apps_row: dict, split: str) -> Path:
    """Effect: makes directory, but does nothing if directory already exists"""
    problem_id = apps_row["problem_id"]
    problem_id = f"{problem_id:04d}"
    split_path = Path(root_path) / "artefacts" / "apps" / split
    problem_path = split_path / str(problem_id)
    problem_path.mkdir(parents=True, exist_ok=True)
    return problem_path


def write_solution_to_file(ds: Dataset, split: str, index: int, root_path: Path):
    row = ds[index]
    problem_path = construct_apps_paths(root_path, row, split)
    solution = get_single_apps_solution(row)
    dump_solution_to_file(solution, problem_path / "python_solution.py")
