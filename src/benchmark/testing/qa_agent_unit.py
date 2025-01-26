import os
import subprocess
from pathlib import Path

from benchmark.utils.logger_setup import logging
from benchmark.agent.types import AgentConfig
from benchmark.agent.agents import LeanAgent


class QaAgentUnit(LeanAgent):
    def __init__(
        self,
        input_context: str,
        output_path: Path,
        config: AgentConfig,
        check_previous_stage: bool = False,
    ):
        super().__init__(input_context, output_path, config, check_previous_stage)
        self.qa_lake = Path("artefacts") / "qa"
        self.basic = self.qa_lake / "Qa" / "Basic.lean"
        self.metadata_path = self.output_path.parent / "metadata.json"

    def run_code(self, code: str) -> tuple[str, str, int]:
        if not code:
            warning = "Code is the empty string"
            logging.warning(warning)
            return "", warning, 1
        logging.info(f"Writing code to {self.qa_lake}")
        logging.debug(f"Code:\n{code}")
        with open(self.basic, "w") as f:
            f.write(code)
        with open(self.output_path, "w") as f:
            f.write(code)
        logging.info(f"Running code with lake build in {self.qa_lake}")
        try:
            result = subprocess.run(
                ["lake", "build"],
                capture_output=True,
                text=True,
                env=os.environ,
                timeout=5 * 60,
                cwd=self.qa_lake,
            )
        except subprocess.TimeoutExpired:
            logging.warning("Timeout expired")
            return "", "Timeout expired", 1
        logging.info(f"returncode: {result.returncode}")
        logging.debug(f"stderr:\n{result.stderr}")
        logging.debug(f"stdout:\n{result.stdout}")

        if result.returncode != 0:
            # remove the first few lines of the output until we find "error"
            # this is to remove the lake build header and any other cruft
            result.stdout = result.stdout[result.stdout.find("error") :]

        return result.stdout, result.stderr, result.returncode

    def loop_init(self) -> tuple[str, str, int]:
        if self.output_path.exists():
            with open(self.output_path, "r") as f:
                code = f.read()
            return self.run_code(code)

        logging.info(
            f"{self.__class__.__name__} sample {self.sample_idx} - Loop 0/{self.max_iterations} (initial)"
        )
        response = self.send_appended_user_message(self.format_first_prompt())
        self.conversation.append({"role": "assistant", "content": response})
        code = self.extract_code(response)
        stdout, stderr, returncode = self.run_code(code)
        return stdout, stderr, returncode

    def loop(self) -> bool:
        if not self.speclean_exited_zero(self.output_path.parent):
            logging.warning("Preceding stage did not exit with 0")
            return False
        stdout, stderr, returncode = self.loop_init()

        metadata = self.reader(self.output_path.parent) if self.metadata_path.exists() else {}

        if self.stopping_condition(returncode):
            metadata["qa_unit_success"] = True
            self.writer(metadata, self.output_path.parent)
            return True

        for i in range(self.max_iterations):
            msg = f"{self.executable} sample {self.sample_idx} - Loop {i+1}/{self.max_iterations}"
            print(msg)
            logging.info(msg)

            response = self.send_appended_user_message(self.continuous_prompt(stdout, stderr))
            self.append_assistant_message(response)
            code = self.extract_code(response)

            stdout, stderr, returncode = self.run_code(code)
            if self.stopping_condition(returncode):
                metadata["qa_unit_success"] = True
                self.writer(metadata, self.output_path.parent)
                break

        if not self.stopping_condition(returncode):
            metadata["qa_unit_success"] = False
            self.writer(metadata, self.output_path.parent)

        logging.info(f"Final QA Unit return code: {returncode}")
        return self.stopping_condition(returncode)
