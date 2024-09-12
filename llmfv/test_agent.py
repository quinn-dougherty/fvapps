from llmfv.claude_prompting import PythonAgent


def simple_python_agent():
    with open('example_func.py', 'r') as file:
        content = file.read()

    agent = PythonAgent(
        input=content,
    )
    agent.loop_until_condition()


    print(agent.dump_full_chat_history())