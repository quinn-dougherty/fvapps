import os
import re
import subprocess
from pathlib import Path
from typing import Callable

from benchmark.utils.logger_setup import logging
from benchmark.utils.metadata import (
    METADATA_FILENAME,
    set_qa_plausible_theorems,
    read_metadata,
    set_keep,
)


def theorem_name(theorem: str) -> str:
    return theorem.split(" ")[1]


def extract_theorems(code: str) -> list[str]:
    """Extract theorem names and bodies from the code."""
    split = code.split("\n\n")
    theorems = []
    for item in split:
        if item.startswith("theorem"):
            theorems.append(item.replace("sorry", "by plausible"))
        elif item.startswith("def"):
            continue
        continue

    return theorems


def replace_sorry_with_plausible(code: str, theorem_name: str) -> str:
    """Replace sorry with plausible for a specific theorem."""
    pattern = f"(theorem\\s+{theorem_name}[^:]*:[^:]+?:=\\s*(?:by\\s+)?)(sorry)"
    return re.sub(pattern, r"\1plausible", code)


class QaPlausibility:
    def __init__(self, spec: str, spec_qa: str, output_path: Path):
        self.spec = spec
        self.spec_qa = spec_qa
        self.output_path = output_path
        # self.sample_idx = sample_idx
        self.qa_lake = Path("artefacts") / "qa"
        self.basic = self.qa_lake / "Qa" / "Basic.lean"
        self.metadata_path = self.output_path.parent / METADATA_FILENAME
        self.implausible_theorems = []

    @property
    def successfuler(self) -> Callable[[list], None]:
        return lambda theorems: set_qa_plausible_theorems(
            self.output_path.parent, theorems
        )

    @property
    def reader(self):
        return read_metadata

    def run_code(self, code: str) -> tuple[str, str, int]:
        if not code:
            warning = "Code is the empty string"
            logging.warning(warning)
            return "", warning, 1

        logging.info(f"Writing code to {self.qa_lake}")
        logging.debug(f"Code:\n{code}")

        # Add plausible import at the top
        code_with_import = f"import Plausible\n\n{code}"

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

    def pruner(self) -> None:
        spec = self.spec
        for theorem in self.implausible_theorems:
            spec = spec.replace(theorem.replace("by plausible", "sorry"), "")
        with open(self.output_path.parent / "Spec.lean", "w") as f:
            f.write(spec.strip())

    def loop(self) -> bool:
        # Check if the unit tests passed
        metadata = self.reader(self.output_path.parent / METADATA_FILENAME)
        if not metadata["unit"]["latest_run_success"]:
            print("unit tests did not pass;", end="\t")
            logging.warning("Unit tests did not pass, skipping plausibility check")
            return False

        # Extract all theorems
        theorems = extract_theorems(self.spec)
        if not theorems:
            logging.warning("No theorems found in the code")
            self.successfuler([])
            return False

        # Test each theorem for plausibility
        plausible_theorems = []
        implausible_theorems = []
        current_code = f"import Plausible\n\n{self.spec_qa}"

        for theorem in theorems:
            test_code = f"{current_code}\n{theorem}"
            stdout, stderr, returncode = self.run_code(test_code)
            thm_name = theorem_name(theorem)
            if returncode == 0:
                plausible_theorems.append(thm_name)
                current_code = (
                    test_code  # Keep the plausible version for next iteration
                )
                logging.info(f"Theorem {thm_name} is plausible")
            else:
                implausible_theorems.append(theorem)
                logging.warning(f"Theorem {thm_name} is not plausible")

        self.implausible_theorems = implausible_theorems
        self.successfuler(plausible_theorems)

        # Write the final SpecQAPlsbl.lean version with all plausible theorems
        with open(self.output_path, "w") as f:
            f.write(current_code)
        if plausible_theorems:
            # remove implausible theorems from Spec.lean
            self.pruner()
            set_keep(self.output_path.parent, True)
            return True
        # set keep.txt to false
        set_keep(self.output_path.parent, False)
        return False
