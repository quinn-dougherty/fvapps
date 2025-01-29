import Plausible

import Plausible

def abs (n : Int) : Int :=
  if n < 0 then -n else n

def myMax (x y : Int) : Int :=
  if x ≥ y then x else y

def myMin (x y : Int) : Int :=
  if x ≤ y then x else y

def solve_max_diagonal_moves (n m k : Int) : Int := 
  -- Store absolute values and organize x as max, y as min
  let x := abs n
  let y := abs m
  let x' := myMax x y
  let y' := myMin x y
  
  -- First stage: handle parity difference
  let (x'', y'', k') := 
    if x' % 2 ≠ k % 2 then
      (x', y' - 1, k - 1)
    else
      (x', y', k)

  -- Second stage: check if destination is reachable
  if x'' > k' then
    -1
  else
    -- Third stage: handle odd delta
    if (x'' - y'') % 2 = 1 then
      k' - 1
    else
      k'

theorem test1 : solve_max_diagonal_moves 2 2 3 = 1 := rfl
theorem test2 : solve_max_diagonal_moves 4 3 7 = 6 := rfl 
theorem test3 : solve_max_diagonal_moves 10 1 9 = -1 := rfl

/--
info: 1
-/
#guard_msgs in
#eval solve_max_diagonal_moves 2 2 3


/--
info: 6
-/
#guard_msgs in
#eval solve_max_diagonal_moves 4 3 7


/--
info: -1
-/
#guard_msgs in
#eval solve_max_diagonal_moves 10 1 9

theorem result_bound (n m k : Int) (h: -1000 <= n ∧ n <= 1000) (h2: -1000 <= m ∧ m <= 1000) (h3: 0 <= k ∧ k <= 2000) :
  let r := solve_max_diagonal_moves n m k
  r = -1 ∨ r ≤ k := by plausible
theorem result_parity (n m k : Int) (h: -1000 <= n ∧ n <= 1000) (h2: -1000 <= m ∧ m <= 1000) (h3: 0 <= k ∧ k <= 2000) :
  let r := solve_max_diagonal_moves n m k
  let max_dist := max (abs n) (abs m)
  r ≠ -1 → (r % 2 = max_dist % 2 ∨ r % 2 = (max_dist - 1) % 2) := by plausible
theorem insufficient_moves (n : Int) (h: 1 <= n ∧ n <= 1000) :
  let k := abs n - 1
  solve_max_diagonal_moves n n k = -1 := by plausible
theorem symmetry (n m : Int) (h: -1000 <= n ∧ n <= 1000) (h2: -1000 <= m ∧ m <= 1000) :
  let k := max (abs n) (abs m) * 2
  let r1 := solve_max_diagonal_moves n m k
  let r2 := solve_max_diagonal_moves (-n) m k
  let r3 := solve_max_diagonal_moves n (-m) k
  let r4 := solve_max_diagonal_moves (-n) (-m) k
  r1 = r2 ∧ r2 = r3 ∧ r3 = r4 := by plausible