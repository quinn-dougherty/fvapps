import os
import subprocess
from ast import literal_eval
from pathlib import Path
from typing import Any, Callable

from anthropic import Anthropic
from datasets import Dataset, load_dataset  # type: ignore
from dotenv import load_dotenv

from benchmark.prompting import AgentConfig
from benchmark.utils import extract_code_block

load_dotenv()
ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY")  # config

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


class AppsPreprocAgent:
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

    def __init__(self, inp: dict, out: str, config: AgentConfig):

        self.model_name = config.model_name
        self.max_tokens_per_completion = config.max_tokens_per_completion
        self.max_iterations = config.max_iterations

        self.client = Anthropic(api_key=ANTHROPIC_API_KEY)

        self.inp = inp
        self.out = out
        self.conversation: list = []

    def run_code(self, code: str):

        with open(self.out, "w") as f:
            f.write(code)

        result = subprocess.run(
            ["python", self.out], capture_output=True, text=True, env=os.environ
        )

        return result.stdout, result.stderr, result.returncode

    def stopping_condition(self, returncode: int):
        return returncode == 0

    def send_appended_user_message(self, message: str):
        self.conversation.append({"role": "user", "content": message})

        response = self.client.messages.create(
            model=self.model_name,
            max_tokens=self.max_tokens_per_completion,
            system=self.SYSTEM_PROMPT,
            messages=self.conversation,
        )
        return response.content[0].text  # type: ignore

    def query_base_case(self, function: str):
        return self.send_appended_user_message(self.FIRST_PROMPT(function))  # type: ignore

    def extract_code(self, response: str):
        return extract_code_block(response, language=self.LANGUAGE)

    def format_first_prompt(self, apps_succinct_rowdict: dict) -> str:
        return self.FIRST_PROMPT(
            apps_succinct_rowdict["problem_statement"],
            apps_succinct_rowdict["solution"],
            apps_succinct_rowdict["test_cases"],
        )

    def loop_until_condition(self) -> bool:

        print(f"Loop 1/{self.max_iterations}")
        # run the first pass and get some code
        response = self.send_appended_user_message(self.format_first_prompt(self.inp))  # type: ignore
        self.conversation.append({"role": "assistant", "content": response})
        # breakpoint()
        code = self.extract_code(response)

        # subprocess call to run it and track outputs and exit codes
        stdout, stderr, returncode = self.run_code(code)

        loops = 1
        while not self.stopping_condition(returncode) and loops < self.max_iterations:
            loops += 1
            print(f"Loop {loops}/{self.max_iterations}")

            # if not done, append the response to the conversation and get a new response
            # with secondary prompt scaffold
            response = self.send_appended_user_message(self.CONTINUOUS_PROMPT(stdout, stderr))  # type: ignore
            # breakpoint()
            self.conversation.append({"role": "assistant", "content": response})
            code = self.extract_code(response)

            # subprocess call to run it and track outputs and exit codes
            stdout, stderr, returncode = self.run_code(code)

        return self.stopping_condition(returncode)

    def dump_full_chat_history(self):
        return self.conversation


if __name__ == "__main__":
    ds = load_hf_apps_dataset()
    setup_apps_directories(Path("."))
