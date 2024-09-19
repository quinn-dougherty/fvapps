import os
import subprocess
from ast import literal_eval
from pathlib import Path
from typing import Any, Callable

from datasets import Dataset, load_dataset  # type: ignore

from benchmark.prompting import DebuggingAgent

HF_DATASET_PATH = "codeparrot/apps"

ALL_DIFFICULTIES = ["introductory", "interview", "competition"]


def load_hf_apps_dataset(split: str = "train", difficulties: list = ALL_DIFFICULTIES):
    return load_dataset(HF_DATASET_PATH, split=split, difficulties=difficulties)


def get_single_apps_solution(apps_row: dict) -> str:
    sols = literal_eval(apps_row["solutions"])
    if isinstance(sols, list):
        return sols[0]
    else:
        return sols


def get_single_apps_test_cases(apps_row: dict) -> str:
    return literal_eval(apps_row["input_output"])


def get_succinct_apps_datarow(apps_row: dict) -> dict:
    return {
        "problem_id": apps_row["problem_id"],
        "problem_statement": apps_row["question"],
        "solution": get_single_apps_solution(apps_row),
        "test_cases": get_single_apps_test_cases(apps_row),
    }


def dump_solution_to_file(solution: str, path: Path):
    """Write a solution to a file."""
    with open(path, "w") as f:
        f.write(solution)
    return path


def setup_apps_directories(root_path: Path):
    """Set up the directories for the apps."""
    for split in ["train", "test"]:
        split_path = Path(root_path / f"artefacts/apps/{split}")
        split_path.mkdir(parents=True, exist_ok=True)

        # create hypothesis and lean subdirectories
        Path(split_path / "python").mkdir(parents=True, exist_ok=True)
        Path(split_path / "lean").mkdir(parents=True, exist_ok=True)


def construct_apps_paths(root_path: Path, apps_row: dict, split: str) -> Path:
    problem_id = apps_row["problem_id"]

    split_path = Path(root_path / f"artefacts/apps/{split}/")

    problem_path = Path(split_path / str(problem_id))

    problem_path.mkdir(parents=True, exist_ok=True)

    return problem_path


def write_solution_to_file(ds: Dataset, split: str, index: int, root_path: Path):
    row = ds[index]
    problem_path = construct_apps_paths(root_path, row, split)
    solution = get_single_apps_solution(row)
    dump_solution_to_file(solution, problem_path / "python_solution.py")


class AppsPreprocAgent(DebuggingAgent):
    LANGUAGE = "python"
    SYSTEM_PROMPT = """
    You are a senior Python developer with expertise in formatting code. Be as concise as possible,
    only generating code with no surrounding commentary that can be directly exported into a file and ran.
    Start your generation with 3 backticks, and end it with 3 backticks.
    """

    FIRST_PROMPT = (
        lambda _, x, y, z: f"""Here is a coding problem statement, a proposed solution, and some test cases formatted
        with newlines for calls to input(). Please rewrite the solution as standalone python file that has a single function
        which takes inputs as defined by the problem, implements the same solution, and returns
        the correct type of output. The file should be runnable, with the main() function running the test cases
        and asserting that they are correct.\n\nProblem Statement:\n{x}\n\nProposed Solution:\n{y}\n\nTest Cases:\n{z}"""
    )

    CONTINUOUS_PROMPT: Callable[[Any, Any, Any], str] = (
        lambda _, stdout, stderr: f"""Running the code produced the following output:\n\nStandard out:\n{stdout}\n\nStandard error:\n{stderr}\n\n.
    Please fix your original output, again only generating code within the 3 backticks."""
    )

    def run_code(self, code: str):

        with open(self.out, "w") as f:
            f.write(code)

        result = subprocess.run(
            ["python", self.out], capture_output=True, text=True, env=os.environ
        )

        return result.stdout, result.stderr, result.returncode

    def stopping_condition(self, returncode: int):
        return returncode == 0


if __name__ == "__main__":
    ds = load_hf_apps_dataset()
    setup_apps_directories(Path("."))

    # for split in ["train", "test"]:
    #     for i, row in enumerate(ds[split]):
    #         construct_apps_paths(row, split)
    #         solution = get_single_apps_solution(ds, i)
    #         dump_solution_to_file(solution, Path(f"artefacts/apps/{split}/{row['problem_id']}/hypothesis/solution.py"))
    #         dump_solution_to_file(solution, Path(f"artefacts/apps/{split}/{row['problem_id']}/lean/solution.lean"))
