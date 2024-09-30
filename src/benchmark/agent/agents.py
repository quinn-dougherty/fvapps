from benchmark.agent.types import DebuggingAgent


class AppsPreprocAgent(DebuggingAgent):

    def __init__(self, input_context, output_path, config, sample):
        super().__init__(
            input_context=input_context, output_path=output_path, config=config
        )
        self.sample = sample

    def format_first_prompt(self) -> str:
        return self.first_prompt(
            self.sample["problem_statement"],
            self.sample["solution"],
            self.sample["test_cases"],
        )


class LeanAgent(DebuggingAgent):
    pass


class PythonAgent(DebuggingAgent):
    pass
