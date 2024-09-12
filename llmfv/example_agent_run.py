from llmfv.claude_prompting import PythonAgent


with open('test/example_func.py', 'r') as file:
    content = file.read()

agent = PythonAgent(
    input=content,
    scratchpad="test/test_example_func.py",
)
agent.loop_until_condition()


print(agent.dump_full_chat_history())