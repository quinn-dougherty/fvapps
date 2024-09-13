from benchmark.claude_prompting import PythonAgent


def main():
    with open("artefacts/hypothesis/example_func.py", "r") as file:
        content = file.read()

    agent = PythonAgent(
        input=content,
        scratchpad="artefacts/hypothesis/test_example_func.py",
    )
    agent.loop_until_condition()

    print(agent.dump_full_chat_history())
