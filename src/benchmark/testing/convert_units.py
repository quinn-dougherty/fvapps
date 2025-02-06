import ast
from pathlib import Path
from typing import Literal

LEAN_TEST_TEMPLATE = (
    lambda expected, func_name, args: f"""/--
info: {expected}
-/
#guard_msgs in
#eval {func_name} {args}
"""
)


def array_or_list(outpath: Path) -> Literal["array", "list"] | None:
    with open(outpath / "Spec.lean", "r") as f:
        content = f.read()
    if "Array" in content:
        return "array"
    if "List" in content:
        return "list"
    return None


class AssertVisitor(ast.NodeVisitor):
    def __init__(self, outpath: Path):
        self.outpath = outpath
        self.test_cases = []
        self.current_test_vars = {}
        self.collection = array_or_list(outpath)

    def visit_Assign(self, node):
        # Handle single assignments
        if len(node.targets) == 1:
            target = node.targets[0]
            if isinstance(target, ast.Name):
                self.current_test_vars[target.id] = ast.unparse(node.value)
            # Handle tuple unpacking
            elif isinstance(target, ast.Tuple):
                if isinstance(node.value, ast.Tuple):
                    for name, value in zip(target.elts, node.value.elts):
                        if isinstance(name, ast.Name):
                            self.current_test_vars[name.id] = ast.unparse(value)

    def visit_Assert(self, node):
        if isinstance(node.test, ast.Compare) and len(node.test.ops) == 1:
            if isinstance(node.test.ops[0], ast.Eq):
                call = node.test.left
                if isinstance(call, ast.Call):
                    func_name = call.func.id
                    args = []
                    for arg in call.args:
                        # Always inline the value, whether it's a name or direct value
                        if (
                            isinstance(arg, ast.Name)
                            and arg.id in self.current_test_vars
                        ):
                            arg_str = self.current_test_vars[arg.id]
                        else:
                            arg_str = ast.unparse(arg)

                        arg_str = arg_str.replace("'", '"')
                        # Convert single quotes to double quotes for string literals
                        if arg_str.startswith("'") and arg_str.endswith("'"):
                            arg_str = f'"{arg_str[1:-1]}"'

                        if arg_str.startswith("[") and self.collection == "array":
                            arg_str = f"#{arg_str}"
                        args.append(arg_str)

                    expected = ast.unparse(node.test.comparators[0])
                    lean_test = LEAN_TEST_TEMPLATE(
                        expected=expected, func_name=func_name, args=" ".join(args)
                    )
                    self.test_cases.append(lean_test)

        # Clear variables after each assert
        self.current_test_vars = {}


def convert_tests(python_code: str, outpath: Path) -> str:
    """Convert Python assert statements to Lean test cases. Takes an outpath to read Spec.lean and determine if the collection type is array or list"""
    tree = ast.parse(python_code)
    visitor = AssertVisitor(outpath=outpath)
    visitor.visit(tree)
    return "\n".join(visitor.test_cases)


def convert_tests_file(soln_py: Path) -> str:
    with open(soln_py, "r") as f:
        python_code = f.read()
    return convert_tests(python_code, outpath=soln_py.parent)
