import os
import subprocess
from benchmark.agent.types import DebuggingAgent


class PythonAgent(DebuggingAgent):
    def run_code(self, code: str) -> tuple[str, str, int]:

        with open(self.out, "w") as f:
            f.write(code)

        result = subprocess.run(
            ["pytest", self.out], capture_output=True, text=True, env=os.environ
        )

        return result.stdout, result.stderr, result.returncode
