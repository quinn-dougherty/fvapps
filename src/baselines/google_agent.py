import os

import google.generativeai as genai
from dotenv import load_dotenv

from baselines.types import BaselineAgent

load_dotenv()
GOOGLE_API_KEY = os.getenv("GOOGLE_API_KEY")  # config


class GoogleAgent(BaselineAgent):

    def setup_client(self):
        genai.configure(api_key=GOOGLE_API_KEY)
        return genai.GenerativeModel(
            self.model_name, system_instruction=self.system_prompt("")
        )

    def send_appended_user_message(self, message: str) -> str:
        self.append_user_message(message)
        chat = self.client.start_chat(history=self.conversation)
        response = chat.send_message(message)
        return response.text  # type: ignore

    def append_assistant_message(self, response: str):
        self.conversation.append({"role": "model", "parts": response})

    def append_user_message(self, message: str):
        self.conversation.append({"role": "user", "parts": message})
