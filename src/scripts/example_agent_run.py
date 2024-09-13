from benchmark.claude_prompting import PythonAgent, LeanAgent


def python_main():

    # TODO: use pathlib
    with open("artefacts/examples/circle.py", "r") as file:
        content = file.read()

    agent = PythonAgent(
        inp=content,
        scratchpad="artefacts/examples/test_circle.py",
    )
    agent.loop_until_condition()

    print(agent.dump_full_chat_history())


def lean_main():

    with open("artefacts/examples/test_circle.py", "r") as file:
        content = file.read()

    agent = LeanAgent(
        inp=content,
        scratchpad="artefacts/examples/Spec.lean",
    )
    agent.loop_until_condition()

    print(agent.dump_full_chat_history())


if __name__ == "__main__":
    lean_main()
