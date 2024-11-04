import json
import os
import subprocess
from abc import ABC, abstractmethod
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Literal, Optional, Union

from benchmark.utils.code_blocks import extract_code_block
from benchmark.utils.logger_setup import logging


@dataclass
class AgentConfig:
    model_name: str
    max_tokens_per_completion: int
    max_iterations: int
    language: Union[Literal["python"], Literal["lean"]]
    executable: str
    system_prompt: Callable[..., str]
    first_prompt: Callable[..., str]
    continuous_prompt: Callable[..., str]
    debug_string: Optional[str] = None
    custom_stopping_condition: Optional[Callable[[str, int], bool]] = None
    overwrite: bool = False


class BaselineAgent(ABC):

    def __init__(
        self,
        input_context: str | tuple[str, str],
        output_path: Path,
        config: AgentConfig,
        check_previous_stage: bool = True,
    ):
        self.model_name = config.model_name
        self.max_tokens_per_completion = config.max_tokens_per_completion
        self.max_iterations = config.max_iterations
        self.language = config.language
        self.executable = config.executable
        self.system_prompt = config.system_prompt
        self.first_prompt = config.first_prompt
        self.continuous_prompt = config.continuous_prompt
        self.debug_string = config.debug_string

        self.custom_stopping_condition: Callable[[str, int], bool] = (
            config.custom_stopping_condition
            if config.custom_stopping_condition
            else lambda _: True  # type: ignore
        )
        self.compress_build_output = True
        self.client = self.setup_client()
        self.input = input_context
        self.output_path = output_path
        self.overwrite = config.overwrite
        self.conversation: list = []

        self.solve_fvapps = Path("artefacts") / "baselines" / "solve-fvapps"
        self.basic = self.solve_fvapps / "SolveFvapps" / "Basic.lean"

        self.check_previous_stage = check_previous_stage

    @abstractmethod
    def setup_client(self):
        pass

    def append_user_message(self, message: str):
        entry = {"role": "user", "content": message}
        self.conversation.append(entry)

    def append_assistant_message(self, response: str):
        entry = {"role": "assistant", "content": response}
        self.conversation.append(entry)

    @abstractmethod
    def send_appended_user_message(self, message: str) -> str:
        pass

    def run_code(self, code: str) -> tuple[str, str, int]:
        if not code:
            warning = "Code is the empty string"
            logging.warning(warning)
            return "", warning, 1
        logging.info(f"Writing code to {self.solve_fvapps}")
        logging.debug(f"Code:\n{code}")
        with open(self.basic, "w") as f:
            f.write(code)
        logging.info(f"Running code with lake build in {self.solve_fvapps}")
        try:
            result = subprocess.run(
                ["lake", "build"],
                capture_output=True,
                text=True,
                env=os.environ,
                timeout=5 * 60,
                cwd=self.solve_fvapps,
            )
        except subprocess.TimeoutExpired:
            logging.warning("Timeout expired")
            return "", "Timeout expired", 1
        logging.info(f"returncode: {result.returncode}")
        logging.info(f"stderr:\n{result.stderr}")
        logging.info(f"stdout:\n{result.stdout}")

        if self.compress_build_output and result.returncode != 0:
            # remove the first few lines of the output until we find "error"
            # this is to remove the lake build header and any other cruft
            result.stdout = result.stdout[result.stdout.find("error") :]

        return result.stdout, result.stderr, result.returncode

    def extract_code(self, response: str):
        return extract_code_block(response, language=self.language)

    def format_first_prompt(self) -> str:
        if isinstance(self.input, tuple):
            return self.first_prompt(*self.input)
        else:
            return self.first_prompt(self.input)

    def loop_init(self) -> tuple[str, str, int]:
        if self.output_path.exists() and not self.overwrite:
            with open(self.output_path, "r") as f:
                code = f.read()
            return self.run_code(code)

        logging.info(
            f"{self.__class__.__name__} {self.model_name} {self.debug_string} - Loop 0/{self.max_iterations} (initial)"
        )
        response = self.send_appended_user_message(self.format_first_prompt())
        self.append_assistant_message(response)
        try:
            code = self.extract_code(response)
        except ValueError:
            msg = "No code block found in the response"
            logging.warning(msg)
            return "", msg, 1
        stdout, stderr, returncode = self.run_code(code)
        return stdout, stderr, returncode

    def copy_basic_to_output(self):
        with open(self.basic, "r") as f:
            code = f.read()
        with open(self.output_path, "w") as f:
            f.write(code)

    def loop(self) -> tuple[bool, str, int]:
        """
        Returns a tuple of a boolean and a string.
        The boolean is True if the stopping condition is met, False otherwise.
        The string is the code that was produced if the stopping condition is met,
        or an empty string otherwise.
        """
        stdout, stderr, returncode = self.loop_init()
        if self.stopping_condition(stdout, returncode):
            self.save_conversation()
            self.copy_basic_to_output()
            return True, "", 1
        loops_so_far = 1
        for i in range(loops_so_far, self.max_iterations + loops_so_far):
            msg = f"{self.executable} {self.model_name} {self.debug_string} - Loop {i}/{self.max_iterations}"
            print(msg)
            logging.info(msg)
            # if not done, append the response to the conversation and get a new response
            # with secondary prompt scaffold
            response = self.send_appended_user_message(self.continuous_prompt(stdout, stderr))  # type: ignore
            self.append_assistant_message(response)

            try:
                code = self.extract_code(response)
            except ValueError:
                msg = "No code block found in the response"
                logging.warning("No code block found in the response")
                stdout, stderr, returncode = "", msg, 1
            else:
                # subprocess call to run it and track outputs and exit codes
                stdout, stderr, returncode = self.run_code(code)
            if self.stopping_condition(stdout, returncode):
                self.copy_basic_to_output()
                break

        self.save_conversation()
        logging.info(f"Final return code: {returncode}")
        self.copy_basic_to_output()
        return self.stopping_condition(stdout, returncode), code, i

    def dump_full_chat_history(self):
        return self.conversation

    def save_conversation(self, filename: Optional[str] = None):
        if filename:
            with open(filename, "w") as f:
                json.dump(self.conversation, f, indent=4)
        else:
            with open(
                self.output_path.parent / f"{self.__class__.__name__}_conversation.json",
                "w",
            ) as f:
                json.dump(self.conversation, f, indent=4)

    def stopping_condition(self, stdout: str, returncode: int) -> bool:
        return self.custom_stopping_condition(stdout, returncode) and returncode == 0
