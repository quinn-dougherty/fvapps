
import pytest
from hypothesis import given, strategies as st
from math import isclose, sin, cos

def example_function(a: int):
    return sin(a) ** 2 + cos(a) ** 2

@given(st.integers())
def test_example_function_property(a):
    result = example_function(a)
    assert isinstance(result, float)
    assert 0 <= result <= 1
    assert isclose(result, 1, rel_tol=1e-09, abs_tol=0.0)

@pytest.mark.parametrize("a", [0, 1, -1, 42, -42, 1000000, -1000000])
def test_example_function_specific_values(a):
    result = example_function(a)
    assert isinstance(result, float)
    assert isclose(result, 1, rel_tol=1e-09, abs_tol=0.0)

@given(st.floats(allow_nan=False, allow_infinity=False))
def test_example_function_float_input(a):
    result = example_function(a)
    assert isinstance(result, float)
    assert 0 <= result <= 1 or isclose(result, 0, abs_tol=1e-09) or isclose(result, 1, rel_tol=1e-09, abs_tol=0.0)
