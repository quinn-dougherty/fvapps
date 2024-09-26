import re
from benchmark.utils.logger_setup import logging


def extract_single_backticks(text: str) -> str | None:
    pattern = r"```(.*?)```"
    mtch = re.search(pattern, text, re.DOTALL)
    if mtch:
        return mtch.group(1)
    pattern = r"```(.*?)"
    mtch = re.search(pattern, text, re.DOTALL)
    return mtch.group(1) if mtch else None


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
    logging.debug(f"Extracting code block from the given text:\n{text}")
    code_block = extract_single_backticks(text)
    if code_block is None:
        raise ValueError(f"No code block found in the given text: {text}")

    code_block = check_and_strip_language_declaration(code_block, language=language)
    logging.debug(f"Extracted code block:\n{code_block}")
    return code_block.strip()
