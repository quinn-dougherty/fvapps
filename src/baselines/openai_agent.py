import os

from dotenv import load_dotenv
from openai import OpenAI

from baselines.types import BaselineAgent

load_dotenv()
OPENAI_API_KEY = os.getenv("OPENAI_API_KEY")  # config


class OpenAIAgent(BaselineAgent):

    def setup_client(self):
        return OpenAI(api_key=OPENAI_API_KEY)

    def send_appended_user_message(self, message: str) -> str:
        self.append_user_message(message)
        sysprompt = {"role": "system", "content": self.system_prompt("")}
        response = self.client.chat.completions.create(
            model=self.model_name,
            max_completion_tokens=self.max_tokens_per_completion,
            messages=[sysprompt, *self.conversation],
        )
        return response.choices[0].message.content  # type: ignore
