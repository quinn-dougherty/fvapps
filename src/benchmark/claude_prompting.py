import os
import shutil
import subprocess
from abc import ABC, abstractmethod
from os import environ, getenv
from typing import Any, Callable

from anthropic import Anthropic
from dotenv import load_dotenv

from benchmark.utils import extract_code_block

load_dotenv()
ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY")  # config

lean_exe = shutil.which("lean")
env = os.environ.copy()
env["PATH"] = f"{os.path.dirname(os.path.abspath('lean'))}:{env.get('PATH', '')}"


class DebuggingAgent(ABC):  # TODO: put in `agent/abc.py`
    LANGUAGE: str
    SYSTEM_PROMPT: str
    FIRST_PROMPT: Callable[[Any, Any], str]
    CONTINUOUS_PROMPT: Callable[[Any, Any, Any], str]

    def __init__(
        self,
        inp: str,
        scratchpad: str,
        model_name: str = "claude-3-5-sonnet-20240620",  # TODO: make cli arg
        max_tokens_per_message: int = 512,
        max_iterations: int = 2,  # TODO: make cli arg
    ):
        self.model_name = model_name
        self.max_tokens_per_message = max_tokens_per_message
        self.max_iterations = max_iterations

        self.client = Anthropic(api_key=ANTHROPIC_API_KEY)

        self.inp = inp
        self.scratchpad = scratchpad
        self.conversation: list = []

    def send_appended_user_message(self, message: str):
        self.conversation.append({"role": "user", "content": message})

        response = self.client.messages.create(
            model=self.model_name,
            max_tokens=self.max_tokens_per_message,
            system=self.SYSTEM_PROMPT,
            messages=self.conversation,
        )
        return response.content[0].text  # type: ignore

    def query_base_case(self, function: str):
        return self.send_appended_user_message(self.FIRST_PROMPT(function))  # type: ignore

    @abstractmethod
    def run_code(self, code: str) -> tuple:
        pass

    @abstractmethod
    def stopping_condition(self, *args, **kwargs) -> bool:
        pass

    def extract_code(self, response: str):
        return extract_code_block(response, language=self.LANGUAGE)

    def loop_until_condition(self) -> bool:

        # run the first pass and get some code
        response = self.send_appended_user_message(self.FIRST_PROMPT(self.inp))  # type: ignore
        self.conversation.append({"role": "assistant", "content": response})

        returncode = 1
        loops = 0
        while not self.stopping_condition(returncode) and loops < self.max_iterations:
            loops += 1
            print(f"Loop {loops}/{self.max_iterations}")

            code = self.extract_code(response)

            # subprocess call to run it and track outputs and exit codes
            stdout, stderr, returncode = self.run_code(code)

            # if not done, append the response to the conversation and get a new response
            # with secondary prompt scaffold
            response = self.send_appended_user_message(self.CONTINUOUS_PROMPT(stdout, stderr))  # type: ignore
            self.conversation.append({"role": "assistant", "content": response})

        # Final Code Try
        code = self.extract_code(response)

        # subprocess call to run it and track outputs and exit codes
        stdout, stderr, returncode = self.run_code(code)

        return self.stopping_condition(returncode)

    def dump_full_chat_history(self):
        return self.conversation


class PythonAgent(DebuggingAgent):
    LANGUAGE = "python"
    SYSTEM_PROMPT = """
    You are a senior Python developer with expertise in generating property tests. You excel at
    completely covering edge cases and possible inputs using pytest and hypothesis. Be as concise as possible,
    only generating code with no surrounding commentary that can be directly exported into a file and ran.
    Start your generation with 3 backticks, and end it with 3 backticks.
    """

    FIRST_PROMPT: Callable[[Any, Any], str] = (
        lambda _, x: f"""Please write property tests for this function:\n\n{x}"""
    )

    CONTINUOUS_PROMPT: Callable[[Any, Any, Any], str] = (
        lambda _, stdout, stderr: f"""Running the code produced the following output:\n\nStandard out:\n{stdout}\n\nStandard error:\n{stderr}\n\n.
    Please fix your original output, again only generating code within the 3 backticks."""
    )

    def run_code(self, code: str):

        with open(self.scratchpad, "w") as f:
            f.write(code)

        result = subprocess.run(
            ["pytest", self.scratchpad], capture_output=True, text=True, env=os.environ
        )

        return result.stdout, result.stderr, result.returncode

    def stopping_condition(self, returncode: int):
        return returncode == 0


class LeanAgent(DebuggingAgent):
    LANGUAGE = "lean"
    SYSTEM_PROMPT = """
    You are a senior Lean 4 developer with expertise in declaring theorems.
    Your task is only to state the theorems based on the property tests given, but not to prove them.
    Instead, ensure the lean typechecker is happy by writing "sorry".
    Do not import Mathlib.
    If needed, declare the function signature and "sorry" its definition.
    Do not comment on the problem or the code itself, only generate code that can be directly exported into a file and ran.
    Start your generation with 3 backticks, and end it with 3 backticks.
    """
    FIRST_PROMPT = lambda _, x: f"""Please write theorems for this function:\n\n{x}"""
    CONTINUOUS_PROMPT = (
        lambda _, stdout, stderr: f"""
        Running the code produced the following output:

        Standard out:\n{stdout}

        Standard error:\n{stderr}

        Please fix your original output, again only generating code within the 3 backticks.
        """
    )

    def verify_output_type(self, response: str):
        """Check that the model output is only code by looking for the backticks at the start and end."""
        return response.startswith("```") and response.endswith("```")

    def run_code(self, code: str):

        with open(self.scratchpad, "w") as f:
            f.write(code)

        result = subprocess.run(
            ["lean", self.scratchpad], capture_output=True, text=True, env=os.environ
        )

        return result.stdout, result.stderr, result.returncode

    def stopping_condition(self, returncode: int):
        return returncode == 0
