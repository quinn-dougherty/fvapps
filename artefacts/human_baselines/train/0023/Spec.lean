def List.argmax? {α β : Type} [LT β] [DecidableRel fun (x1 x2 : β) => x1 < x2] (l : List α) (f : α → β) : Option α :=
  l.foldl (λ o a =>
    match o with
    | none => some a
    | some b => if f a > f b then some a else some b) none


def Float.sigmoid (x : Float) : Float := 1.0 / (1.0 + Float.exp (-x))

-- equivalent to any function which increases in fst and decreases in snd
def utility (voter : Nat × Nat) : Float := voter.fst.toFloat.sigmoid + 1.0 / voter.snd.toFloat

/--
Input format is a list of pairs of natural numbers,
where the first number is the number of preexisting votes needed to convert
and the second is the price in dollars
-/
def min_coins_for_votes' (voters : List (Nat × Nat)) : Nat := Id.run do
  let mut expense := 0
  let mut conversions := 0
  let mut holdouts := voters
  while conversions < voters.length do
    -- collect the votes you already got because conversions
    let mut prev := holdouts.length
    holdouts := holdouts.filter (λ p => conversions < p.fst)
    conversions := conversions + prev - holdouts.length
    while prev > holdouts.length do
      prev := holdouts.length
      holdouts := holdouts.filter (λ p => conversions < p.fst)
      conversions := conversions + prev - holdouts.length
    if holdouts.isEmpty then
      return expense
    -- buy the cheapest vote
    let bestValue := holdouts.argmax? utility |>.get!
    holdouts := holdouts.eraseP (. == bestValue)
    expense := expense + bestValue.snd
    -- increment conversions
    conversions := conversions + 1
  return expense

theorem Bool.bool_iff_false (b : Bool) : ¬ b = true ↔ b = false := by
  simp

def filter_cascade (voters : List (Nat × Nat)) (conversions : Nat) : List (Nat × Nat) :=
  if h : voters.all fun p => conversions < p.fst then
    voters.filter λ p => conversions < p.fst
  else
    filter_cascade (voters.filter λ p => conversions < p.fst) (conversions + voters.countP λ p => conversions <= p.fst)
  termination_by voters.length
  decreasing_by
    induction voters generalizing conversions with
    | nil => simp; contradiction
    | cons voter voters' ih =>
      simp
      simp at ih
      simp [List.filter] at h
      cases g : decide (conversions < voter.fst) with
      | true =>
        simp [List.filter]
        rw [g]; simp
        simp at g
        specialize (h g)
        obtain ⟨x1, ⟨⟨x2, h1⟩, h2⟩⟩ := h
        specialize (ih conversions x1 x2 h1 h2)
        apply ih
      | false =>
        rw [<- Bool.bool_iff_false] at g
        rw [List.filter_cons_of_neg] <;> try assumption
        simp at g
        have f : (voters'.filter λ p => conversions < p.fst).length <= voters'.length := by
          apply List.length_filter_le
        omega

def go (voters holdouts : List (Nat × Nat)) (expense conversions : Nat) : Nat :=
  if conversions ≥ voters.length then
    expense
  else
    let filtered := filter_cascade holdouts conversions
    if filtered.isEmpty then
      expense
    else
      let bestValue := filtered.argmax? utility |>.get!
      let holdouts' := filtered.eraseP (. == bestValue)
      go voters
         holdouts'
         (expense + bestValue.snd)
         (conversions + 1)
  termination_by (voters.length - conversions)
  decreasing_by omega

def solve_elections (n : Nat) (voters : List (Nat × Nat)) : Nat :=
  go voters voters 0 0

/--
info: 8
-/
#guard_msgs in
#eval solve_elections 3 [(1, 5), (2, 10), (2, 8)]

/--
info: 0
-/
#guard_msgs in
#eval solve_elections 7 [
  (0, 1),
  (3, 1),
  (1, 1),
  (6, 1),
  (1, 1),
  (4, 1),
  (4, 1)
]

/--
info: 7
-/
#guard_msgs in
#eval solve_elections 6 [
  (2, 6),
  (2, 3),
  (2, 8),
  (2, 7),
  (4, 4),
  (5, 5)
]

theorem solve_elections_nonnegative (n : Nat) (voters : List (Nat × Nat)) : solve_elections n voters >= 0 := by exact Nat.zero_le _

set_option maxRecDepth 1999
theorem solve_elections_upper_bound (n : Nat) (voters : List (Nat × Nat)) : solve_elections n voters <= List.foldl (λ acc (pair : Nat × Nat) => acc + pair.2) 0 voters := by
  simp [solve_elections]
  induction voters generalizing n with
  | nil => simp [go]
  | cons voter voters ih =>
    simp



theorem solve_elections_zero_votes (n : Nat) (voters : List (Nat × Nat)) : (List.all voters (fun pair => pair.1 = 0)) -> solve_elections n voters = 0 := sorry

theorem solve_elections_single_zero_vote : solve_elections 1 [(0, 5)] = 0 := sorry
