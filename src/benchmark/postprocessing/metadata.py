from pathlib import Path


def count_sorries(path: Path) -> int:
    """Count the number of 'sorry's in a file."""
    with open(path / "Spec.lean", "r") as f:
        return f.read().count("sorry")
