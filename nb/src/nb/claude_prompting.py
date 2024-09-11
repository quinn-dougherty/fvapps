from anthropic import Anthropic
from dotenv import load_dotenv
from os import getenv

load_dotenv()
ANTHROPIC_API_KEY = getenv("ANTHROPIC_API_KEY")

client = Anthropic(api_key=ANTHROPIC_API_KEY)
MODEL_NAME = "claude-3-opus-20240229"

message = client.messages.create(
    model=MODEL_NAME,
    max_tokens=512,
    messages=[
        {
            "role": "user", 
            "content": "Give me a JSON dict with names of famous athletes & their sports."
        },
    ]
).content[0].text
print(message)
