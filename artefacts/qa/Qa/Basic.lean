import Lean

/-- Find all numbers between 1 and n that are multiples of 3 or 5 -/
def multiplesOf3Or5 (n : Nat) : List Nat :=
  -- Create list of numbers from 1 to n-1
  let range := List.range n 
  -- Filter numbers that are divisible by 3 or 5
  range.filter (fun x => x % 3 = 0 || x % 5 = 0)

def main : IO Unit := do
  let sum := (multiplesOf3Or5 1000).foldl (· + ·) 0
  IO.println s!"Sum: {sum}"

/--
info: [1, 3]
-/
#guard_msgs in
#eval solve 4 ["0001", "1000", "0011", "0111"]

/--
info: [-1]
-/
#guard_msgs in
#eval solve 3 ["010", "101", "0"]

/--
info: [0]
-/
#guard_msgs in
#eval solve 2 ["00000", "00001"]
