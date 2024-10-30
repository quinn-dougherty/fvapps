def List.minHier1 (l : List (Nat × Nat)) : Option (Nat × Nat) := l.foldl (λ o a =>
    match o with
    | none => some a
    | some b => if a.snd < b.snd then some (if a.fst < b.fst then a else b) else some b) none

def List.minHier2 (l : List (Nat × Nat)) : Option (Nat × Nat) :=
  l.foldl (λ o a =>
    match o with
    | none => some a
    | some b => if a.fst < b.fst then some (if a.snd < b.snd then a else b) else some b) none

def List.argmin? {α β : Type} [LT β] [DecidableRel fun (x1 x2 : β) => x1 < x2] (l : List α) (f : α → β) : Option α :=
  l.foldl (λ o a =>
    match o with
    | none => some a
    | some b => if f a < f b then some a else some b) none

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

#check List.filter_cons_of_neg

def filter_cascade' (voters : List (Nat × Nat)) (conversions : Nat) : List (Nat × Nat) :=
  let filtered := voters.filter (λ p => conversions < p.fst)
  if h : filtered.length = voters.length then
    filtered
  else
    filter_cascade' filtered (conversions + voters.length - filtered.length)
  termination_by (voters.length - conversions)
  decreasing_by
    induction voters generalizing conversions with
    | nil => simp; contradiction
    | cons voter voters' ih =>
      cases g : decide (filtered.length < voters'.length) with
      | true =>
        simp [List.filter]
        cases f : decide (conversions < voter.fst) with
        | true =>
          simp
          specialize (ih conversions)
          sorry
        | false =>
          simp
          sorry
      | false =>
        sorry

#check List.filter_cons_of_neg

def filter_cascade (voters : List (Nat × Nat)) (conversions : Nat) : List (Nat × Nat) :=
  if h : (voters.filter λ p => conversions < p.fst).length = voters.length then
    voters.filter λ p => conversions < p.fst
  else
    filter_cascade (voters.filter λ p => conversions < p.fst) (conversions + voters.length - (voters.filter λ p => conversions < p.fst).length)
  termination_by (voters.length - conversions)
  decreasing_by
    induction voters generalizing conversions with
    | nil => simp; contradiction
    | cons voter voters' ih =>
      simp
      simp at ih
      simp [List.filter] at h
      cases g : decide (conversions < voter.fst) with
      | true =>
        rw [g] at h; simp at h
        obtain ⟨x1, ⟨h1, h2⟩⟩ := h
        obtain ⟨x2, h1⟩ := h1
        specialize (ih conversions x1 x2 h1 h2)
        rw [List.filter_cons_of_pos]
        simp
        omega
        assumption
      | false =>
        rw [List.filter_cons_of_neg]
        -- rw [g] at h; simp at h
        have f : (voters'.filter λ p => conversions < p.fst).length ≤ voters'.length := by apply List.length_filter_le
        have e : conversions ≤ voters'.length := by sorry -- i think this is wrong
        omega
        rw [Bool.bool_iff_false]
        assumption

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
  termination_by sizeOf (voters.length - conversions)
  decreasing_by omega

def min_coins_for_votes (voters : List (Nat × Nat)) : Nat :=
  go voters voters 0 0

/--
info: 8
-/
#guard_msgs in
#eval min_coins_for_votes [(1, 5), (2, 10), (2, 8)]

/--
info: 0
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
info: 7
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
  min_coins_for_votes [(v, c)] = if v = 0 then 0 else c := by
    simp [min_coins_for_votes, go]
    sorry

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
