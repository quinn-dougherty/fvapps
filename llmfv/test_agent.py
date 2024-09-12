from llmfv.claude_prompting import PythonAgent
from math import sin, cos

def example_function(a: int):
    return sin(a)**2 + cos(a)**2


def test_python_agent():
    agent = PythonAgent()

    example_function_code = """
def example_function(a: int):
    return sin(a)**2 + cos(a)**2
    """

    agent.loop_until_condition(example_function_code)

if __name__ == "__main__":
    test_python_agent()