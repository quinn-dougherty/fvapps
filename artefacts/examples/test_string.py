import string
from hypothesis import given, strategies as st
import pytest
from collections import Counter

def max_char(message: str) -> str:
    """return the char that appears the most"""
    if not message:
        raise ValueError("Empty string is not allowed")
    return Counter(message).most_common(1)[0][0]

@given(st.text(min_size=1))
def test_max_char_in_string(s):
    result = max_char(s)
    assert result in s
    assert all(s.count(result) >= s.count(c) for c in s)

@given(st.text(min_size=1))
def test_max_char_consistent(s):
    assert max_char(s) == max_char(s)

@given(st.text(min_size=1), st.text(min_size=1))
def test_max_char_concatenation(s1, s2):
    result = max_char(s1 + s2)
    assert result in s1 or result in s2
    assert s1.count(result) + s2.count(result) == max(s1.count(c) + s2.count(c) for c in set(s1 + s2))

@given(st.text(min_size=1))
def test_max_char_reverse(s):
    assert s.count(max_char(s)) == s[::-1].count(max_char(s[::-1]))

@pytest.mark.parametrize("s, expected", [
    ("aaa", "a"),
    ("abcabc", "a"),  # First occurrence in case of tie
    ("", pytest.raises(ValueError)),
    (" ", " "),
])
def test_max_char_specific_cases(s, expected):
    if isinstance(expected, str):
        assert max_char(s) == expected
    else:
        with expected:
            max_char(s)

@given(st.text(alphabet=string.ascii_lowercase, min_size=1))
def test_max_char_lowercase(s):
    assert max_char(s) in string.ascii_lowercase

@given(st.text(alphabet=string.digits, min_size=1))
def test_max_char_digits(s):
    assert max_char(s) in string.digits

@given(st.text(min_size=2))
def test_max_char_not_unique(s):
    assert s.count(max_char(s)) > 1 or len(set(s)) == len(s)