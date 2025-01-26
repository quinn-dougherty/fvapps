import os
import re
import subprocess
from pathlib import Path

from benchmark.utils.logger_setup import logging
from benchmark.agent.types import AgentConfig
from benchmark.agent.agents import LeanAgent
from benchmark.utils.metadata import write_metadata

class QaAgentPlausible(LeanAgent):
    def __init__(
        self,
        input_context: str,
        output_path: Path,
        config: AgentConfig,
        check_previous_stage: bool = True,
    ):
        super().__init__(input_context, output_path, config, check_previous_stage)
        self.qa_lake = Path("artefacts") / "qa"
        self.basic = self.qa_lake / "Qa" / "Basic.lean"
        self.metadata_path = self.output_path.parent / "metadata.json"

    def writer(self, metadata: dict):
        # metadata here will be loaded from disk by reader, it should never be just this QA data.
        write_metadata(self.metadata_path, metadata)

    def extract_theorems(self, code: str) -> list[tuple[str, str]]:
        """Extract theorem names and bodies from the code."""
        theorem_pattern = r'theorem\s+([a-zA-Z0-9_]+)\s*[^:]*:\s*([^:]+?)\s*:=\s*(?:by\s+)?sorry'
        return re.findall(theorem_pattern, code)

    def replace_sorry_with_plausible(self, code: str, theorem_name: str) -> str:
        """Replace sorry with plausible for a specific theorem."""
        pattern = f'(theorem\\s+{theorem_name}[^:]*:[^:]+?:=\\s*(?:by\\s+)?)(sorry)'
        return re.sub(pattern, r'\1plausible', code)

    def run_code(self, code: str) -> tuple[str, str, int]:
        if not code:
            warning = "Code is the empty string"
            logging.warning(warning)
            return "", warning, 1

        logging.info(f"Writing code to {self.qa_lake}")
        logging.debug(f"Code:\n{code}")

        # Add plausible import at the top
        code_with_import = "import Plausible\n" + code

        with open(self.basic, "w") as f:
            f.write(code_with_import)
        with open(self.output_path, "w") as f:
            f.write(code_with_import)

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

        return result.stdout, result.stderr, result.returncode

    def loop(self) -> bool:
        # Check if the unit tests passed
        metadata = self.reader(self.output_path.parent) if self.metadata_path.exists() else {}
        if not metadata.get("qa_unit_success", False):
            logging.warning("Unit tests did not pass, skipping plausibility check")
            metadata["qa_plausible_success"] = False
            self.writer(metadata)
            return False

        # Read the original code
        with open(self.output_path, "r") as f:
            original_code = f.read()

        # Extract all theorems
        theorems = self.extract_theorems(original_code)
        if not theorems:
            logging.warning("No theorems found in the code")
            metadata["qa_plausible_success"] = False
            self.writer(metadata)
            return False

        # Test each theorem for plausibility
        plausible_theorems = []
        current_code = original_code

        for theorem_name, _ in theorems:
            test_code = self.replace_sorry_with_plausible(current_code, theorem_name)
            stdout, stderr, returncode = self.run_code(test_code)

            if returncode == 0:
                plausible_theorems.append(theorem_name)
                current_code = test_code  # Keep the plausible version for next iteration
                logging.info(f"Theorem {theorem_name} is plausible")
            else:
                logging.warning(f"Theorem {theorem_name} is not plausible")

        # Update metadata with results
        metadata["qa_plausible_success"] = len(plausible_theorems) > 0
        metadata["plausible_theorems"] = plausible_theorems
        self.writer(metadata)

        # Write the final version with all plausible theorems
        if plausible_theorems:
            with open(self.output_path, "w") as f:
                f.write(current_code)

        return metadata["qa_plausible_success"]