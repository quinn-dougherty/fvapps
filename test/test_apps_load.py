from src.benchmark.apps_utils import get_single_apps_solution, load_hf_apps_dataset


def test_load_hf_apps_dataset():
    ds = load_hf_apps_dataset()
    assert len(ds) > 0


def test_get_single_apps_solution():
    ds = load_hf_apps_dataset()
    solution = get_single_apps_solution(ds, 0)
    assert isinstance(solution, str)
    assert len(solution) > 0
