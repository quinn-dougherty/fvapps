import ast


LEAN_TEST_TEMPLATE = (
    lambda expected, func_name, args: f"""/--
info: {expected}
-/
#guard_msgs in
#eval {func_name} {args}
"""
)


class AssertVisitor(ast.NodeVisitor):
    def __init__(self):
        self.test_cases = []
        self.current_test_vars = {}

    def visit_Assign(self, node):
        # Capture variable assignments before assert statements
        if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            name = node.targets[0].id
            self.current_test_vars[name] = ast.unparse(node.value)

    def visit_Assert(self, node):
        if isinstance(node.test, ast.Compare) and len(node.test.ops) == 1:
            if isinstance(node.test.ops[0], ast.Eq):
                call = node.test.left
                if isinstance(call, ast.Call):
                    func_name = call.func.id
                    args = []
                    for arg in call.args:
                        # If argument is a Name and exists in current_test_vars, use that
                        if (
                            isinstance(arg, ast.Name)
                            and arg.id in self.current_test_vars
                        ):
                            args.append(self.current_test_vars[arg.id])
                        else:
                            args.append(ast.unparse(arg))

                    expected = ast.unparse(node.test.comparators[0])

                    lean_test = LEAN_TEST_TEMPLATE(
                        expected=expected, func_name=func_name, args=" ".join(args)
                    )

                    self.test_cases.append(lean_test)

        # Clear variables after each assert
        self.current_test_vars = {}


def convert_tests(python_code: str) -> str:
    tree = ast.parse(python_code)
    visitor = AssertVisitor()
    visitor.visit(tree)
    return "\n\n".join(visitor.test_cases)
