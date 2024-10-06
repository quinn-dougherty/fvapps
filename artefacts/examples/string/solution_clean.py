def max_char(message: str) -> str:
    """return the char that appears the most"""
    return max(set(message), key=message.count)
