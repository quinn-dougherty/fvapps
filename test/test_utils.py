from src.benchmark.utils import extract_code_block


def test_extract_code_block():
    text = "```python\nprint('hello, world!')\n```"
    assert extract_code_block(text) == "print('hello, world!')"

    text = (
        "```python\nprint('hello, world!')\n```\n```python\nprint('hello, world!')\n```"
    )
    assert extract_code_block(text) == "print('hello, world!')"

    text = "```python\nprint('hello, world!')\n```\n```python\nprint('hello, world!')\n```\n```python\nprint('hello, world!')\n```"
    assert extract_code_block(text) == "print('hello, world!')"

    text = "Here is a solution:\n```python\nprint('hello, world!')\n```\n\n This does a few things:\n 1. blah\n 2. blah\n 3. blah"
    assert extract_code_block(text) == "print('hello, world!')"
