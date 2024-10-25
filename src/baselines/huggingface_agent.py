from transformers import AutoTokenizer, AutoModelForCausalLM
import torch

from baselines.types import BaselineAgent


class HuggingFaceAgent(BaselineAgent):
    def setup_client(self):
        self.device = "cuda" if torch.cuda.is_available() else "cpu"
        self.model = AutoModelForCausalLM.from_pretrained(self.model_name).to(
            self.device
        )
        self.tokenizer = AutoTokenizer.from_pretrained(self.model_name)

        if self.tokenizer.pad_token is None:
            self.tokenizer.pad_token = self.tokenizer.eos_token

        return self

    def _format_messages(self, messages):
        formatted = ""
        for msg in messages:
            role = (
                "System"
                if msg["role"] == "system"
                else "Human" if msg["role"] == "user" else "Assistant"
            )
            formatted += f"{role}: {msg['content']}\n\n"
        return formatted.strip()

    def send_appended_user_message(self, message: str) -> str:
        self.append_user_message(message)

        sysprompt = {"role": "system", "content": self.system_prompt("")}
        prompt = self._format_messages([sysprompt, *self.conversation])

        inputs = self.tokenizer(prompt, return_tensors="pt", padding=True).to(
            self.device
        )

        with torch.no_grad():
            output_ids = self.model.generate(
                **inputs,
                max_new_tokens=self.max_tokens_per_completion,
                temperature=0.0,
                # top_p=0.95,
                pad_token_id=self.tokenizer.pad_token_id,
                eos_token_id=self.tokenizer.eos_token_id,
            )

        new_tokens = output_ids[0][inputs["input_ids"].shape[1] :]
        response_text = self.tokenizer.decode(new_tokens, skip_special_tokens=True)

        self.append_assistant_message(response_text)
        return response_text
