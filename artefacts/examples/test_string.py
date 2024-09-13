import string
from hypothesis import given, strategies as st
import pytest

def max_char(message: str) -> str:
    """return the char that appears the most"""
    if not message:
        raise ValueError("Empty string is not allowed")
    return max(set(message), key=lambda c: (message.count(c), -message.index(c)))

@given(st.text(min_size=1))
def test_max_char_property(s):
    result = max_char(s)
    assert result in s
    assert all(s.count(result) >= s.count(c) for c in s)

@pytest.mark.parametrize("input_str, expected", [
    ("a", "a"),
    ("aabbcc", "a"),
    ("aabbccdd", "a"),
    ("abcdef", "a"),
    ("  ", " "),
    ("\t\n\r", "\t"),
    ("123321", "1"),
    ("!@#$%^&*()", "!"),
])
def test_max_char_specific_cases(input_str, expected):
    assert max_char(input_str) == expected

def test_max_char_empty_string():
    with pytest.raises(ValueError):
        max_char("")

@given(st.text(alphabet=string.ascii_lowercase, min_size=1))
def test_max_char_lowercase(s):
    result = max_char(s)
    assert result.islower()

@given(st.text(alphabet=string.ascii_uppercase, min_size=1))
def test_max_char_uppercase(s):
    result = max_char(s)
    assert result.isupper()

@given(st.text(alphabet=string.digits, min_size=1))
def test_max_char_digits(s):
    result = max_char(s)
    assert result.isdigit()

@given(st.text(alphabet=string.punctuation, min_size=1))
def test_max_char_punctuation(s):
    result = max_char(s)
    assert result in string.punctuation

@given(st.text(min_size=1), st.characters())
def test_max_char_with_repeated_char(s, c):
    repeated_s = s + c * (len(s) + 1)
    assert max_char(repeated_s) == c

@given(st.text(min_size=1))
def test_max_char_tie_breaker(s):
    result = max_char(s)
    max_count = s.count(result)
    assert all(s.index(c) >= s.index(result) for c in s if s.count(c) == max_count)

@given(st.text(min_size=2))
def test_max_char_first_occurrence(s):
    result = max_char(s)
    max_count = s.count(result)
    first_index = s.index(result)
    assert all(s.index(c) > first_index for c in s if s.count(c) == max_count and c != result)