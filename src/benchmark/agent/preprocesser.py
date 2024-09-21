from benchmark.utils.metadata import initialize_metadata
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

    def loop_init(self) -> tuple[str, str, int]:
        if self.out.exists():
            with open(self.out, "r") as f:
                code = f.read()
            return self.run_code(code)
        print(
            f"Preprocessing:: sample {self.sample_idx} - Loop 0/{self.max_iterations} (initial)"
        )
        response = self.send_appended_user_message(self.format_first_prompt())
        self.conversation.append({"role": "assistant", "content": response})
        code = self.extract_code(response)
        stdout, stderr, returncode = self.run_code(code)
        return stdout, stderr, returncode
