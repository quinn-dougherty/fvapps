from benchmark.prompting import PythonAgent, LeanAgent, AgentConfig
from scripts.config import leancfg, pythoncfg
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
        config=AgentConfig(**cfg["python"], **pythoncfg),
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
        config=AgentConfig(**cfg["lean"], **leancfg),
    )
    final_exit_code = agent.loop_until_condition()

    print(agent.dump_full_chat_history())
    print("Was the final generation successful?", final_exit_code)
    return
