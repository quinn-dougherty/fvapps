import os
import shutil
import subprocess
from abc import ABC, abstractmethod
from typing import Any, Callable, Union, Literal
from dataclasses import dataclass
from typing import Any, Callable

from anthropic import Anthropic
from dotenv import load_dotenv

from benchmark.utils import extract_code_block

load_dotenv()
ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY")  # config


@dataclass
class AgentConfig:
    model_name: str
    max_tokens_per_completion: int
    max_iterations: int
    language: Union[Literal["python"], Literal["lean"]]
    system_prompt: Callable[[Any], str]
    first_prompt: Callable[[Any], str]
    continuous_prompt: Callable[[Any, Any], str]


class DebuggingAgent(ABC):  # TODO: put in `agent/abc.py`

    def __init__(self, inp: str, out: str, config: AgentConfig):
        self.model_name = config.model_name
        self.max_tokens_per_completion = config.max_tokens_per_completion
        self.max_iterations = config.max_iterations
        self.language = config.language
        self.system_prompt = config.system_prompt
        self.first_prompt = config.first_prompt
        self.continuous_prompt = config.continuous_prompt

        self.client = Anthropic(api_key=ANTHROPIC_API_KEY)

        self.inp = inp
        self.out = out
        self.conversation: list = []

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
        response = self.client.messages.create(
            model=self.model_name,
            max_tokens=self.max_tokens_per_completion,
            system=[sysprompt],
            messages=self.conversation,
        )
        return response.content[0].text  # type: ignore

    def query_base_case(self, function: str):
        return self.send_appended_user_message(self.FIRST_PROMPT(function))  # type: ignore

    @abstractmethod
    def run_code(self, code: str) -> tuple[str, str, int]:
        pass

    def extract_code(self, response: str):
        return extract_code_block(response, language=self.language)

    def loop_until_condition(self) -> bool:

        print(f"Loop 1/{self.max_iterations}")
        # run the first pass and get some code
        response = self.send_appended_user_message(self.first_prompt(self.inp))  # type: ignore
        self.conversation.append({"role": "assistant", "content": response})
        code = self.extract_code(response)

        # subprocess call to run it and track outputs and exit codes
        stdout, stderr, returncode = self.run_code(code)

        loops = 1
        while not self.stopping_condition(returncode) and loops < self.max_iterations:
            loops += 1
            print(f"Loop {loops}/{self.max_iterations}")

            # if not done, append the response to the conversation and get a new response
            # with secondary prompt scaffold
            response = self.send_appended_user_message(self.continuous_prompt(stdout, stderr))  # type: ignore
            self.append_assistant_message(response)
            code = self.extract_code(response)

            # subprocess call to run it and track outputs and exit codes
            stdout, stderr, returncode = self.run_code(code)

        return self.stopping_condition(returncode)

    def dump_full_chat_history(self):
        return self.conversation

    def stopping_condition(self, returncode: int) -> bool:
        return returncode == 0


class PythonAgent(DebuggingAgent):
    def run_code(self, code: str) -> tuple[str, str, int]:

        with open(self.out, "w") as f:
            f.write(code)

        result = subprocess.run(
            ["pytest", self.out], capture_output=True, text=True, env=os.environ
        )

        return result.stdout, result.stderr, result.returncode


class LeanAgent(DebuggingAgent):
    def run_code(self, code: str) -> tuple[str, str, int]:

        with open(self.out, "w") as f:
            f.write(code)

        result = subprocess.run(
            ["lean", self.out], capture_output=True, text=True, env=os.environ
        )

        return result.stdout, result.stderr, result.returncode
