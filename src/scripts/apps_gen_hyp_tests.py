import pathlib
import tomllib

from benchmark.prompting import AgentConfig, LeanAgent, PythonAgent
from scripts.config import lean, python

EXAMPLE = "string"

with open("src/config.toml", "rb") as f:
    cfg = tomllib.load(f)


def python_main(in_path, out_path):

    with open(in_path, "r") as f:
        content = f.read()

    agent = PythonAgent(
        inp=content,
        out=out_path,
        config=AgentConfig(**cfg["python"], **python),
    )
    final_exit_code = agent.loop_until_condition()

    print(agent.dump_full_chat_history())
    print("Was the final generation successful?", final_exit_code)
    return


def lean_main(in_path, out_path):

    with open(in_path, "r") as f:
        content = f.read()

    agent = LeanAgent(
        inp=content, out=out_path, config=AgentConfig(**cfg["lean"], **lean)
    )
    final_exit_code = agent.loop_until_condition()

    print(agent.dump_full_chat_history())
    print("Was the final generation successful?", final_exit_code)
    return


if __name__ == "__main__":
    # get path to artefacts/apps data, after choosing a split
    split = "train"
    root_path = pathlib.Path("artefacts") / "apps" / split

    n_samps = 2

    for i in range(n_samps):
        inp_python_path = root_path / f"{i}/solution_clean.py"
        out_hyp_path = root_path / f"{i}/test_solution.py"

        python_main(inp_python_path, out_hyp_path)

    for i in range(n_samps):
        out_hyp_path = root_path / f"{i}/test_solution.py"
        out_lean_path = root_path / f"{i}/Spec.lean"

        lean_main(out_hyp_path, out_lean_path)
