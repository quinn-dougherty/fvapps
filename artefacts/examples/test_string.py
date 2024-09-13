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
def test_max_char_ascii_letters(s):
    result = max_char(s)
    assert result.isalpha()

@given(st.text(alphabet=string.digits, min_size=1))
def test_max_char_digits(s):
    result = max_char(s)
    assert result.isdigit()

@pytest.mark.parametrize("input_str, expected", [
    ("aaa", "a"),
    ("abcabc", "a"),  # First occurrence when tied
    ("", ValueError),  # Empty string should raise ValueError
])
def test_max_char_specific_cases(input_str, expected):
    if expected == ValueError:
        with pytest.raises(ValueError):
            max_char(input_str)
    else:
        assert max_char(input_str) == expected

def test_max_char_unicode():
    assert max_char("🌟🌟🌟👍👍") == "🌟"

@given(st.text(min_size=2))
def test_max_char_not_first_or_last(s):
    result = max_char(s)
    assert (result != s[0] or s.count(result) > 1) and (result != s[-1] or s.count(result) > 1)