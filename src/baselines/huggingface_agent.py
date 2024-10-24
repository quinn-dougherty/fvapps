from transformers import AutoTokenizer, AutoModelForCausalLM
import torch

from baselines.agents import BenchmarkAgent

# Set the model name
model_name = "deepseek-ai/DeepSeek-Prover-V1.5-RL"

# Load the tokenizer
tokenizer = AutoTokenizer.from_pretrained(model_name)

# Load the model
model = AutoModelForCausalLM.from_pretrained(
    model_name, torch_dtype=torch.float16, device_map="auto"
)

# Example usage
input_text = "Prove that the sum of two even numbers is even."
input_ids = tokenizer.encode(input_text, return_tensors="pt").to(model.device)

# Generate output
with torch.no_grad():
    output = model.generate(
        input_ids, max_length=200, num_return_sequences=1, temperature=0.7
    )

# Decode and print the output
generated_text = tokenizer.decode(output[0], skip_special_tokens=True)
print(generated_text)
