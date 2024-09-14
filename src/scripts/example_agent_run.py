from benchmark.prompting import PythonAgent, LeanAgent, AgentConfig
import tomllib
import pathlib

EXAMPLE = "string"

with open("src/config.toml", "rb") as f:
    cfg = tomllib.load(f)

artefacts = pathlib.Path("artefacts")
examples = artefacts / "examples"


def python_main():

    with open(examples / f"{EXAMPLE}.py", "r") as f:
        content = f.read()

    agent = PythonAgent(
        inp=content,
        out=str(examples / f"test_{EXAMPLE}.py"),
        config=AgentConfig(
            model_name=cfg["model_name_python"],
            max_tokens_per_completion=cfg["max_tokens_per_completion_python"],
            max_iterations=cfg["max_iterations_python"],
        ),
    )
    final_exit_code = agent.loop_until_condition()

    print(agent.dump_full_chat_history())
    print("Was the final generation successful?", final_exit_code)
    return


def lean_main():

    with open(examples / f"test_{EXAMPLE}.py", "r") as f:
        content = f.read()

    agent = LeanAgent(
        inp=content,
        out=str(examples / "Spec.lean"),
        config=AgentConfig(
            model_name=cfg["model_name_lean"],
            max_tokens_per_completion=cfg["max_tokens_per_completion_lean"],
            max_iterations=cfg["max_iterations_lean"],
        ),
    )
    final_exit_code = agent.loop_until_condition()

    print(agent.dump_full_chat_history())
    print("Was the final generation successful?", final_exit_code)
    return
