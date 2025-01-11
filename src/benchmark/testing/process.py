from pathlib import Path
import os
from benchmark.testing.convert_units import convert_tests


def process_split(artefacts_dir: Path | str, split: str = "train") -> None:
    """take solution_clean.py and Spec.lean and write SpecQA.lean"""
    artefacts_dir = (
        Path(artefacts_dir) if isinstance(artefacts_dir, str) else artefacts_dir
    )
    for idx_dir in (artefacts_dir / "apps" / split).iterdir():
        with open(idx_dir / "solution_clean.py", "r") as f:
            solution_clean = f.read()
        with open(idx_dir / "Spec.lean", "r") as f:
            spec = f.read()
        guards = convert_tests(solution_clean)
        spec_qa = spec + guards
        with open(idx_dir / "SpecQA.lean", "w") as f:
            f.write(spec_qa)
