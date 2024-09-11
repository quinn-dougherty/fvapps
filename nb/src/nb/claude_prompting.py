from abc import ABC, abstractmethod
from anthropic import Anthropic
from dotenv import load_dotenv
from os import getenv

load_dotenv()
ANTHROPIC_API_KEY = getenv("ANTHROPIC_API_KEY")

class DebuggingAgent(ABC):
    def __init__(
        self,
        model_name: str = "claude-3-opus-20240229",
        max_tokens_per_message: int = 512,
    ):
        self.model_name = model_name
        self.max_tokens_per_message = max_tokens_per_message

        self.client = Anthropic(api_key=ANTHROPIC_API_KEY)

        self.system_prompt = self.SYSTEM_PROMPT
        self.first_prompt = self.FIRST_PROMPT

        self.conversation = []

    def send_appended_user_message(self, message: str):
        self.conversation.append({"role": "user", "content": message})

        response = self.client.messages.create(
            model=self.model_name,
            max_tokens=self.max_tokens_per_message,
            system=self.system_prompt,
            messages=self.conversation,
        )
        return response.content[0].text
    
    def query_base_case(self, function: str):
        return self.send_appended_user_message(self.first_prompt(function))


class PythonAgent(DebuggingAgent):
    SYSTEM_PROMPT = """
    Your are a senior Python developer with expertise in generating property tests. You excel at 
    completely covering edge cases and possible inputs using pytest and hypothesis.
    """

    FIRST_PROMPT = lambda x: f"""Please write property tests for this function:\n\n{x}"""
    pass

class LeanAgent(DebuggingAgent):
    pass