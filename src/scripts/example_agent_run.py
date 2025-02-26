import pathlib

from benchmark.agent.agents import LeanAgent, PythonAgent
from benchmark.agent.types import AgentConfig
from scripts.config import leancfg, pythoncfg

EXAMPLE = "string"  # "string" or "circle"

artefacts = pathlib.Path("artefacts")
examples = artefacts / "examples"

example_path = examples / EXAMPLE

clean_func_path = example_path / f"solution_clean.py"
py_hyp_path = example_path / f"hypotheses.py"
lean_path = example_path / f"Spec.lean"


def python_main():

    with open(clean_func_path, "r") as f:
        content = f.read()

    agent = PythonAgent(
        input_context=content,
        output_path=py_hyp_path,
        config=AgentConfig(**pythoncfg),
        check_previous_stage=False,  # examples don't run through the cleanup part of the pipeline
    )
    final_exit_code = agent.loop()

    print(agent.dump_full_chat_history())
    print("Was the final generation successful?", final_exit_code)
    return


def lean_main():

    with open(py_hyp_path, "r") as f:
        content = f.read()

    agent = LeanAgent(
        input_context=content,
        output_path=lean_path,
        config=AgentConfig(**leancfg),
    )
    final_exit_code = agent.loop()

    print(agent.dump_full_chat_history())
    print("Was the final generation successful?", final_exit_code)
    return


def main():
    python_main()
    lean_main()
