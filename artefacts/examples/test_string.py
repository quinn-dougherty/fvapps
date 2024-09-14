import string
from hypothesis import given, strategies as st
import pytest

def max_char(message: str) -> str:
    """return the char that appears the most"""
    return max(set(message), key=message.count)

@given(st.text(min_size=1))
def test_max_char_property(s):
    result = max_char(s)
    assert len(result) == 1
    assert result in s
    assert all(s.count(result) >= s.count(c) for c in s)

@given(st.text(alphabet=string.ascii_letters, min_size=1))
def test_max_char_letters_only(s):
    result = max_char(s)
    assert result.isalpha()

@given(st.text(alphabet=string.digits, min_size=1))
def test_max_char_digits_only(s):
    result = max_char(s)
    assert result.isdigit()

@pytest.mark.parametrize("input_str, expected", [
    ("aaa", "a"),
    ("abcba", "b"),
    ("122333", "3"),
    ("!@#$%^&*()", "!"),
    ("a1a1a2", "a"),
    ("AbCdEfG", "A"),  # First occurrence in case of tie
])
def test_max_char_specific_cases(input_str, expected):
    assert max_char(input_str) == expected

def test_max_char_empty_string():
    with pytest.raises(ValueError):
        max_char("")

@given(st.text(min_size=2))
def test_max_char_not_unique(s):
    result = max_char(s)
    assert s.count(result) > 1 or all(s.count(c) == 1 for c in s)