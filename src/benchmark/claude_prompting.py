from abc import ABC, abstractmethod
from anthropic import Anthropic
from dotenv import load_dotenv
from os import getenv, environ
import subprocess

load_dotenv()
ANTHROPIC_API_KEY = getenv("ANTHROPIC_API_KEY")  # config


class DebuggingAgent(ABC):  # TODO: put in `agent/abc.py`
    SYSTEM_PROMPT = ""
    FIRST_PROMPT = lambda _: f""
    CONTINUOUS_PROMPT = lambda _: f""

    def __init__(
        self,
        input: str,
        scratchpad: str,
        model_name: str = "claude-3-opus-20240229",  # TODO: make cli arg
        max_tokens_per_message: int = 512,
        max_iterations: int = 2,  # TODO: make cli arg
    ):
        self.model_name = model_name
        self.max_tokens_per_message = max_tokens_per_message
        self.max_iterations = max_iterations

        self.client = Anthropic(api_key=ANTHROPIC_API_KEY)

        self.input = input
        self.scratchpad = scratchpad
        self.conversation = []

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
    def verify_output_type(self, response: str) -> bool:
        pass

    @abstractmethod
    def run_code(self, code: str) -> tuple:
        pass

    @abstractmethod
    def stopping_condition(self, *args, **kwargs) -> bool:
        pass

    def loop_until_condition(self):

        # run the first pass and get some code
        response = self.send_appended_user_message(self.FIRST_PROMPT(self.input))  # type: ignore
        self.conversation.append({"role": "assistant", "content": response})

        returncode = 1
        loops = 0
        while not self.stopping_condition(returncode) and loops < self.max_iterations:
            loops += 1
            print(f"Loop {loops}/{self.max_iterations}")

            # check that the code is valid
            if not self.verify_output_type(response):
                print(response)
                raise ValueError("The output from the model is not code.")

            # subprocess call to run it and track outputs and exit codes
            stdout, stderr, returncode = self.run_code(response)

            # if not done, append the response to the conversation and get a new response
            # with secondary prompt scaffold
            response = self.send_appended_user_message(self.CONTINUOUS_PROMPT(stdout, stderr))  # type: ignore
            self.conversation.append({"role": "assistant", "content": response})

        return

    def dump_full_chat_history(self):
        return self.conversation


class PythonAgent(DebuggingAgent):
    SYSTEM_PROMPT = """
    You are a senior Python developer with expertise in generating property tests. You excel at 
    completely covering edge cases and possible inputs using pytest and hypothesis. Do not comment on the problem
    or the code itself, only generate code that can be directly exported into a file and ran.
    Start your generation with 3 backticks, and end it with 3 backticks.
    """

    FIRST_PROMPT = (
        lambda _, x: f"""Please write property tests for this function:\n\n{x}"""
    )

    CONTINUOUS_PROMPT = (
        lambda _, stdout, stderr: f"""Running the code produced the following output:\n\nStandard out:\n{stdout}\n\nStandard error:\n{stderr}\n\n.
    Please fix your original output, again only generating code within the 3 backticks."""
    )

    def verify_output_type(self, response: str):
        """Check that the model output is only code by looking for the backticks at the start and end."""
        return response.startswith("```") and response.endswith("```")

    def run_code(self, code: str):
        # strip the backticks
        code = code[3:-3]
        if code.startswith("python"):
            code = code[6:]

        with open(self.scratchpad, "w") as f:
            f.write(code)

        result = subprocess.run(
            ["pytest", self.scratchpad], capture_output=True, text=True, env=environ
        )

        return result.stdout, result.stderr, result.returncode

    def stopping_condition(self, returncode: int):
        return returncode == 0


class LeanAgent(DebuggingAgent):
    pass
