import re


def extract_single_backticks(text) -> str | None:
    pattern = r"```(.*?)```"
    match = re.search(pattern, text, re.DOTALL)
    return match.group(1) if match else None


def check_and_strip_language_declaration(code: str, language: str = "python") -> str:
    """
    Checks if the code starts with a language declaration and removes it.
    Assumes that the language declaration is the first line of the code block.
    """
    if code.startswith(language):
        code = code[code.index("\n") + 1 :]

    return code


def extract_code_block(text: str, language: str = "python") -> str:
    """
    Extracts the first code block from the given text by:
    1. Removing surrounding text outside of backticks.
    2. Removing backticks and code block delimiters.
    """

    code_block = extract_single_backticks(text)
    if code_block is None:
        raise ValueError("No code block found in the given text.")

    code_block = check_and_strip_language_declaration(code_block, language=language)

    return code_block.strip()
