def List.minHier (l : List (Nat × Nat)) : Option (Nat × Nat) :=
  l.foldl (λ o a =>
    match o with
    | none => some a
    | some b => if a.snd < b.snd then some (if a.fst < b.fst then a else b) else some b) none

def min_coins_for_votes (voters : List (Nat × Nat)) : Nat := Id.run do
  let mut expense := 0
  let mut conversions := 0
  let mut remainingVoters := voters
  while conversions < voters.length do
    let prev := remainingVoters.length
    remainingVoters := remainingVoters.filter (λ p => conversions < p.fst)
    conversions := conversions + prev - remainingVoters.length
    if remainingVoters.isEmpty then
      return expense
    let cheapest := remainingVoters.minHier |>.get!
    remainingVoters := remainingVoters.filter (. ≠ cheapest)
    expense := expense + cheapest.snd
    conversions := conversions + 1
  return expense

/--
info: 8 : Nat
-/
#guard_msgs in
#eval min_coins_for_votes [(1, 5), (2, 10), (2, 8)]

/--
info: 0 : Nat
-/
#guard_msgs in
#eval min_coins_for_votes [
  (0, 1),
  (3, 1),
  (1, 1),
  (6, 1),
  (1, 1),
  (4, 1),
  (4, 1)
]

/--
info: 7 : Nat
-/
#guard_msgs in
#eval min_coins_for_votes [
  (2, 6),
  (2, 3),
  (2, 8),
  (2, 7),
  (4, 4),
  (5, 5)
]

theorem min_coins_for_votes_non_negative (voters : List (Nat × Nat)) :
  min_coins_for_votes voters ≥ 0 := sorry

theorem min_coins_for_votes_upper_bound (voters : List (Nat × Nat)) :
  min_coins_for_votes voters ≤ List.foldl (· + ·) 0 (List.map (λ p => p.2) voters) := sorry

theorem min_coins_for_votes_zero_votes (voters : List (Nat × Nat)) :
  (∀ v ∈ voters, v.1 = 0) → min_coins_for_votes voters = 0 := sorry

theorem min_coins_for_votes_single_voter (v : Nat) (c : Nat) :
  min_coins_for_votes [(v, c)] = if v = 0 then 0 else c := sorry

theorem min_coins_for_votes_unit_cost (voters : List (Nat × Nat)) :
  (∀ v ∈ voters, v.2 = 1) →
  min_coins_for_votes voters ≤ List.length voters ∧
  min_coins_for_votes voters ≤ List.foldl Nat.max 0 (List.map (λ p => p.1) voters) := sorry

theorem min_coins_for_votes_sorted_input (voters : List (Nat × Nat)) :
  min_coins_for_votes voters = min_coins_for_votes (List.map id voters) := sorry

theorem min_coins_for_votes_no_votes_needed (voters : List (Nat × Nat)) :
  (∀ v ∈ voters, v.1 = 0) → min_coins_for_votes voters = 0 := sorry

theorem min_coins_for_votes_zero_cost (voters : List (Nat × Nat)) :
  (∀ v ∈ voters, v.2 = 0) → min_coins_for_votes voters = 0 := sorry
