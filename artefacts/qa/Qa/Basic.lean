import Plausible

import Plausible

import Lean

def count_alice_score (s : String) : Nat :=
  -- Split string on '0's and convert to array of string lengths
  let blocks := s.split (· == '0')
    |>.filter (fun p => p.length > 0)
    |>.map String.length
    |>.toArray
  
  -- Sort lengths in descending order  
  let sorted := blocks.insertionSort (· > ·)
  
  -- Calculate Alice's score by summing even-indexed values
  let indices := List.range sorted.size |>.filter (· % 2 == 0)
  indices.foldl (fun sum i => sum + sorted[i]!) 0

/--
info: 4
-/
#guard_msgs in
#eval count_alice_score "01111001"

/--
info: 6
-/
#guard_msgs in
#eval count_alice_score "111111"

/--
info: 3
-/
#guard_msgs in
#eval count_alice_score "101010101"

theorem result_not_exceed_input_length 
  (s : String) : 
  count_alice_score s ≤ s.length := 
  by plausible
theorem result_nonnegative
  (s : String) :
  count_alice_score s ≥ 0 :=
  by plausible
theorem empty_or_zeros_returns_zero
  (s : String) :
  (s.isEmpty ∨ s.all (· = '0')) → count_alice_score s = 0 :=
  by plausible
theorem all_ones_full_score
  (s : String) :
  s.all (· = '1') →
  s.length > 0 →
  count_alice_score s = s.length :=
  by plausible