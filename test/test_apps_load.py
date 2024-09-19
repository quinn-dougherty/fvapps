import pytest

from src.benchmark.apps_utils import (
    get_single_apps_solution,
    get_single_apps_test_cases,
    get_succinct_apps_datarow,
    load_hf_apps_dataset,
)


@pytest.fixture
def ds():
    return load_hf_apps_dataset()


def test_load_hf_apps_dataset(ds):
    assert len(ds) > 0


def test_get_single_apps_solution(ds):
    solution = get_single_apps_solution(ds[0])
    assert isinstance(solution, str)
    assert len(solution) > 0


def test_get_single_apps_test_cases(ds):
    ds = load_hf_apps_dataset()
    test_cases = get_single_apps_test_cases(ds[0])
    assert isinstance(test_cases, dict)
    assert set(test_cases.keys()) == {"inputs", "outputs"}


def test_get_succinct_apps_datarow(ds):
    row = get_succinct_apps_datarow(ds[0])
    assert isinstance(row, dict)
    assert set(row.keys()) == {
        "problem_id",
        "problem_statement",
        "solution",
        "test_cases",
    }
