import os
import subprocess
from datasets import Dataset
from benchmark.utils.apps import load_hf_apps_dataset, get_succinct_apps_datarow
from benchmark.agent.types import DebuggingAgent


class AppsPreprocAgent(DebuggingAgent):

    def __init__(self, inp, out, config, sample):
        super().__init__(inp, out, config)
        self.sample = sample

    def format_first_prompt(self) -> str:
        return self.first_prompt(
            self.sample["problem_statement"],
            self.sample["solution"],
            self.sample["test_cases"],
        )

    def run_code(self, code: str) -> tuple[str, str, int]:
        with open(self.out, "w") as f:
            f.write(code)
        result = subprocess.run(
            ["python", self.out], capture_output=True, text=True, env=os.environ
        )
        return result.stdout, result.stderr, result.returncode

    def loop(self) -> bool:
        print(f"Loop 1/{self.max_iterations}")
        # run the first pass and get some code
        response = self.send_appended_user_message(self.format_first_prompt())
        self.conversation.append({"role": "assistant", "content": response})
        code = self.extract_code(response)

        # subprocess call to run it and track outputs and exit codes
        stdout, stderr, returncode = self.run_code(code)

        for i in range(self.max_iterations):
            print(f"Loop {i+1}/{self.max_iterations}")
            # if not done, append the response to the conversation and get a new response
            # with secondary prompt scaffold
            response = self.send_appended_user_message(
                self.continuous_prompt(stdout, stderr)
            )
            self.conversation.append({"role": "assistant", "content": response})
            code = self.extract_code(response)

            # subprocess call to run it and track outputs and exit codes
            stdout, stderr, returncode = self.run_code(code)

            if self.stopping_condition(returncode):
                break
        return self.stopping_condition(returncode)
