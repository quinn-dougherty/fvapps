import os
import subprocess

from benchmark.agent.types import DebuggingAgent
from benchmark.utils.logger_setup import logging


class AppsPreprocAgent(DebuggingAgent):

    def __init__(self, sample, *args, check_previous_stage=False, **kwargs):
        super().__init__(*args, check_previous_stage=check_previous_stage, **kwargs)
        self.sample = sample

    def format_first_prompt(self) -> str:
        return self.first_prompt(
            self.sample["problem_statement"],
            self.sample["solution"],
            self.sample["test_cases"],
        )


class LeanAgent(DebuggingAgent):
    pass


class PythonAgent(DebuggingAgent):
    def run_code(self, code: str) -> tuple[str, str, int]:
        if not code:
            warning = "Code is the empty string"
            logging.warning(warning)
            return "", warning, 1
        if "input()" in code or "sys.stdin" in code:
            warning = "user interaction is not allowed"
            logging.warning(warning)
            return "", warning, 1
        logging.info(f"Writing code to {self.output_path}")
        logging.debug(f"Code:\n{code}")
        with open(self.output_path, "w") as f:
            f.write(code)
        logging.info(f"Running code with {self.executable}")
        result = subprocess.run(
            [
                self.executable,
                "--tb=short",
                "--hypothesis-verbosity=quiet",
                self.output_path,
            ],
            capture_output=True,
            text=True,
            env=os.environ,
        )
        logging.info(f"returncode: {result.returncode}")
        logging.info(f"stderr:\n{result.stderr}")
        logging.info(f"stdout:\n{result.stdout}")
        return result.stdout, result.stderr, result.returncode
