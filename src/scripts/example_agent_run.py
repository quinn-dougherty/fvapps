from benchmark.claude_prompting import PythonAgent


def main():

    # TODO: make artefacts hypothesis
    with open("artefacts/examples/circle.py", "r") as file:
        content = file.read()

    agent = PythonAgent(
        input=content,
        scratchpad="artefacts/examples/test_circle.py",
    )
    final_exit_code = agent.loop_until_condition()

    print(agent.dump_full_chat_history())

    print("Was the final generation successful?", final_exit_code)


if __name__ == "__main__":
    main()
