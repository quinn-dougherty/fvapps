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


# Example usage
python_code = """
from collections import deque
INF = 10**9

def solve_subway_fare(n: int, m: int, edges: list) -> int:
    seen = set()
    for i in range(n):
        seen.add((i, 0))
    for p, q, c in edges:
        p -= 1; q -= 1
        seen.add((p, c))
        seen.add((q, c))

    comp = {node: i for i, node in enumerate(seen)}

    edge = [[] for _ in range(len(comp))]
    for key in comp.keys():
        v, c = key
        if c != 0:
            frm = comp[(v, c)]
            too = comp[(v, 0)]
            edge[frm].append((too, 0))
            edge[too].append((frm, 1))

    for p, q, c in edges:
        frm = comp[(p-1, c)]
        too = comp[(q-1, c)]
        edge[frm].append((too, 0))
        edge[too].append((frm, 0))

    # BFS
    dist = [INF] * len(edge)
    dist[comp[(0, 0)]] = 0
    q = deque([(0, comp[(0, 0)])])

    while q:
        prov_cost, src = q.popleft()
        if dist[src] < prov_cost:
            continue
        for dest, cost in edge[src]:
            if dist[dest] > dist[src] + cost:
                dist[dest] = dist[src] + cost
                if cost == 1:
                    q.append((dist[dest], dest))
                else:
                    q.appendleft((dist[dest], dest))

    ans = dist[comp[(n-1, 0)]]
    return -1 if ans == INF else ans

def main():
    # Test case 1
    n, m = 3, 3
    edges = [(1,2,1), (2,3,1), (3,1,2)]
    assert solve_subway_fare(n, m, edges) == 1

    # Test case 2
    n, m = 8, 11
    edges = [(1,3,1), (1,4,2), (2,3,1), (2,5,1), (3,4,3),
             (3,6,3), (3,7,3), (4,8,4), (5,6,1), (6,7,5), (7,8,5)]
    assert solve_subway_fare(n, m, edges) == 2

    # Test case 3
    n, m = 2, 0
    edges = []
    assert solve_subway_fare(n, m, edges) == -1

if __name__ == '__main__':
    main()
"""

print(convert_tests(python_code))
