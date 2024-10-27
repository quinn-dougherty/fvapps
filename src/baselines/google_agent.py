import os

import google.generativeai as genai
from dotenv import load_dotenv

from baselines.types import BaselineAgent

load_dotenv()
GOOGLE_API_KEY = os.getenv("GOOGLE_API_KEY")  # config


class ClaudeAgent(BaselineAgent):

    def setup_client(self):
        genai.configure(api_key=GOOGLE_API_KEY)
        return genai.GenerativeModel(self.model_name)

    def send_appended_user_message(self, message: str) -> str:
        self.append_user_message(message)
        response = self.client.generate_content(
            f"{self.system_prompt('')}\n\n{message}"
        )
        return response.text  # type: ignore
