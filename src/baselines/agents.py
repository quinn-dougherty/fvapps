import json
import os
import signal
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Literal, Union

from anthropic import Anthropic
from dotenv import load_dotenv

from benchmark.utils.code_blocks import extract_code_block
from benchmark.utils.logger_setup import logging

load_dotenv()
ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY")  # config


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
    sample_idx: int | None = None


class BaselineAgent:

    def __init__(
        self,
        input_context: str,
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
        self.sample_idx = config.sample_idx

        self.client = Anthropic(api_key=ANTHROPIC_API_KEY)
        self.input = input_context
        self.output_path = output_path
        self.conversation: list = []

        self.check_previous_stage = check_previous_stage

    def append_user_message(self, message: str):
        entry = {"role": "user", "content": message}
        self.conversation.append(entry)

    def append_assistant_message(self, response: str):
        entry = {"role": "assistant", "content": response}
        self.conversation.append(entry)

    def send_appended_user_message(self, message: str, cache: bool = False):
        self.append_user_message(message)
        sysprompt = {"type": "text", "text": self.system_prompt("")}
        if cache:
            sysprompt["cache-control"] = "ephemeral"
        response = self.client.beta.prompt_caching.messages.create(
            model=self.model_name,
            max_tokens=self.max_tokens_per_completion,
            system=[sysprompt],  # type: ignore
            messages=self.conversation,
        )
        return response.content[0].text  # type: ignore

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
        try:
            result = subprocess.run(
                [self.executable, self.output_path],
                capture_output=True,
                text=True,
                env=os.environ,
                timeout=5 * 60,
            )
        except subprocess.TimeoutExpired:
            logging.warning("Timeout expired")
            return "", "Timeout expired", 1
        logging.info(f"returncode: {result.returncode}")
        logging.info(f"stderr:\n{result.stderr}")
        logging.info(f"stdout:\n{result.stdout}")
        return result.stdout, result.stderr, result.returncode

    def extract_code(self, response: str):
        return extract_code_block(response, language=self.language)

    def format_first_prompt(self) -> str:
        return self.first_prompt(self.input)

    def loop_init(self) -> tuple[str, str, int]:
        if self.output_path.exists():
            with open(self.output_path, "r") as f:
                code = f.read()
            return self.run_code(code)

        logging.info(
            f"{self.__class__.__name__} sample {self.sample_idx} - Loop 0/{self.max_iterations} (initial)"
        )
        response = self.send_appended_user_message(self.format_first_prompt())
        self.conversation.append({"role": "assistant", "content": response})
        code = self.extract_code(response)
        stdout, stderr, returncode = self.run_code(code)
        return stdout, stderr, returncode

    def loop(self) -> bool:
        stdout, stderr, returncode = self.loop_init()
        if self.stopping_condition(returncode):
            return True
        loops_so_far = 1
        for i in range(loops_so_far, self.max_iterations + loops_so_far):
            msg = f"{self.executable} sample {self.sample_idx} - Loop {i}/{self.max_iterations}"
            print(msg)
            logging.info(msg)
            # if not done, append the response to the conversation and get a new response
            # with secondary prompt scaffold
            response = self.send_appended_user_message(self.continuous_prompt(stdout, stderr))  # type: ignore
            self.append_assistant_message(response)
            code = self.extract_code(response)

            # subprocess call to run it and track outputs and exit codes
            stdout, stderr, returncode = self.run_code(code)
            if self.stopping_condition(returncode):
                break

        self.save_conversation()
        logging.info(f"Final return code: {returncode}")
        return self.stopping_condition(returncode)

    def dump_full_chat_history(self):
        return self.conversation

    def save_conversation(self):
        with open(
            self.output_path.parent / f"{self.__class__.__name__}_conversation.json",
            "w",
        ) as f:
            json.dump(self.conversation, f, indent=4)

    def stopping_condition(self, returncode: int) -> bool:
        return returncode == 0
