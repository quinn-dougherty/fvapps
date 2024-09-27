import os
import subprocess

from benchmark.agent.types import DebuggingAgent
from benchmark.utils.logger_setup import logging


class AppsPreprocAgent(DebuggingAgent):

    def __init__(self, inp, out, config, sample):
        super().__init__(inp, out, config)
        self.sample = sample

    def format_first_prompt(self) -> str:
        return self.first_prompt(
            self.sample["problem_statement"],
            self.sample["solution"],
            self.sample["test_cases"],
        )

    def run_code(self, code: str) -> tuple[str, str, int]:
        if not code:
            warning = "Code is the empty string"
            logging.warning(warning)
            return "", warning, 1
        if "input(" in code or "sys.stdin" in code:
            warning = "user interaction is not allowed"
            logging.warning(warning)
            return "", warning, 1
        logging.info(f"Writing code to {self.out}")
        logging.debug(f"Code:\n{code}")
        with open(self.out, "w") as f:
            f.write(code)
        logging.info(f"Running code with {self.executable}")
        result = subprocess.run(
            [self.executable, self.out], capture_output=True, text=True, env=os.environ
        )
        return result.stdout, result.stderr, result.returncode

    def loop_init(self) -> tuple[str, str, int]:
        if self.out.exists():
            with open(self.out, "r") as f:
                code = f.read()
            return self.run_code(code)
        msg = f"Preprocessing:: sample {self.sample_idx} - Loop 0/{self.max_iterations} (initial)"
        print(msg)
        logging.info(msg)
        response = self.send_appended_user_message(self.format_first_prompt())
        self.conversation.append({"role": "assistant", "content": response})
        code = self.extract_code(response)
        stdout, stderr, returncode = self.run_code(code)
        return stdout, stderr, returncode
