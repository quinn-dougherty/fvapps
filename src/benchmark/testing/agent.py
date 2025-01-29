import os
import subprocess
from pathlib import Path
from typing import Callable

from benchmark.utils.logger_setup import logging
from benchmark.utils.metadata import (
    METADATA_FILENAME,
    increment_unit_loops,
    read_unit,
    successfuler_unit,
    unit_reinitialize_metadata,
    set_keep,
)
from benchmark.agent.types import AgentConfig
from benchmark.agent.agents import LeanAgent
from benchmark.testing.convert_units import convert_tests


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
        self.metadata_path = self.output_path.parent / METADATA_FILENAME
        unit_reinitialize_metadata(self.output_path.parent)
        with open(self.output_path.parent / "solution_clean.py") as f:
            self.soln_clean = f.read()

    @property
    def successfuler(self) -> Callable[[Path], None]:
        return successfuler_unit

    @property
    def incrementor(self) -> Callable[[Path], None]:
        return increment_unit_loops

    @property
    def reader(self) -> Callable[[Path], dict]:
        return read_unit

    def run_code(self, code: str) -> tuple[str, str, int]:
        if not code:
            warning = "Code is the empty string"
            logging.warning(warning)
            return "", warning, 1
        code = f"{code}\n\n{convert_tests(self.soln_clean, self.output_path.parent)}"
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

        msg = f"{self.__class__.__name__} sample {self.sample_idx} - Loop 0/{self.max_iterations} (initial)"
        logging.info(msg)
        print(msg)
        response = self.send_appended_user_message(self.format_first_prompt())
        self.append_assistant_message(response)
        code = self.extract_code(response)
        stdout, stderr, returncode = self.run_code(code)
        return stdout, stderr, returncode

    def loop(self) -> bool:
        if not self.speclean_exited_zero(self.output_path.parent):
            logging.warning("Preceding stage did not exit with 0")
            return False
        stdout, stderr, returncode = self.loop_init()
        loops_so_far = self.reader(self.output_path.parent)["loops"]

        if self.stopping_condition(returncode):
            self.successfuler(self.output_path.parent)
            return True

        # Note: we're not actually keeping track of number of loops
        for i in range(loops_so_far, self.max_iterations + loops_so_far):
            msg = f"{self.executable} sample {self.sample_idx} - Loop {i+1}/{self.max_iterations + loops_so_far}"
            print(msg)
            logging.info(msg)
            self.incrementor(self.output_path.parent)
            response = self.send_appended_user_message(
                self.continuous_prompt(stdout, stderr)
            )
            self.append_assistant_message(response)
            code = self.extract_code(response)

            stdout, stderr, returncode = self.run_code(code)
            if self.stopping_condition(returncode):
                self.successfuler(self.output_path.parent)
                break

        stopping_condition = self.stopping_condition(returncode)
        logging.info(f"Final QA Unit return code: {returncode}")
        if not stopping_condition:
            set_keep(self.output_path.parent, False)
        return stopping_condition
