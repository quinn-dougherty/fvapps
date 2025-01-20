def solve_max_diagonal_moves (n m k : Int) : Int := 
  -- Get absolute values and put larger in x
  let x := Int.natAbs n
  let y := Int.natAbs m
  let x' := if x ≥ y then x else y
  let y' := if x ≤ y then x else y
  
  -- Adjust k and y if k and x have different parity 
  if Int.mod x' 2 ≠ Int.mod k 2 then
    -- Can't reach with adjusted k
    if x' > (k - 1) then -1
    -- Check if delta between adjusted x,y is odd
    else if Int.mod (x' - (y' - 1)) 2 = 1 then (k - 1) - 1
    else k - 1
  -- Original parity ok
  else
    -- Can't reach with original k
    if x' > k then -1  
    -- Check if delta is odd
    else if Int.mod (x' - y') 2 = 1 then k - 1
    else k

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