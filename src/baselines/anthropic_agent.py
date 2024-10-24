import os

from anthropic import Anthropic
from dotenv import load_dotenv

from baselines.types import BaselineAgent

load_dotenv()
ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY")  # config


class ClaudeAgent(BaselineAgent):

    def setup_client(self):
        return Anthropic(api_key=ANTHROPIC_API_KEY)

    def send_appended_user_message(self, message: str) -> str:
        self.append_user_message(message)
        sysprompt = {"type": "text", "text": self.system_prompt("")}
        response = self.client.beta.prompt_caching.messages.create(
            model=self.model_name,
            max_tokens=self.max_tokens_per_completion,
            system=[sysprompt],  # type: ignore
            messages=self.conversation,
        )
        return response.content[0].text  # type: ignore
