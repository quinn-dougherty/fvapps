from benchmark.claude_prompting import LeanAgent


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
