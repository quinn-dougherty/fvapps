from benchmark.claude_prompting import PythonAgent, LeanAgent

EXAMPLE = "string"


def python_main():

    # TODO: use pathlib
    with open(f"artefacts/examples/{EXAMPLE}.py", "r") as f:
        content = f.read()

    agent = PythonAgent(
        inp=content,
        scratchpad=f"artefacts/examples/test_{EXAMPLE}.py",
    )
    final_exit_code = agent.loop_until_condition()

    print(agent.dump_full_chat_history())

    print("Was the final generation successful?", final_exit_code)


def lean_main():

    with open(f"artefacts/examples/test_{EXAMPLE}.py", "r") as f:
        content = f.read()

    agent = LeanAgent(
        inp=content,
        scratchpad="artefacts/examples/Spec.lean",
    )
    agent.loop_until_condition()

    print(agent.dump_full_chat_history())


if __name__ == "__main__":
    lean_main()
