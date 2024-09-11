import Imp.Expr

import Imp.Stmt.Delab

namespace Imp

/--
Truthiness: the result of evaluating an expression is "truthy" if it's defined and non-zero.
-/
def Truthy (v : Option Value) : Prop :=
  match v with
  | some v => match v with
    | .int x => x ≠ 0
    | .str s => ¬ s.isEmpty
  | none => False

instance : Decidable (Truthy v) :=
  match v with
  | some v => match v with
    | .int x => if h : x ≠ 0 then .isTrue h else .isFalse h
    | .str s => if h : ¬ s.isEmpty then .isTrue h else .isFalse h
  | none => .isFalse id

@[simp]
theorem Truthy.some_nonzero : Truthy (some (.int v)) = (v ≠ 0) := by
  simp [Truthy]

@[simp]
theorem Truthy.not_none : Truthy none = False := by
  simp [Truthy]

@[simp]
theorem Truthy.eval_const_int : Truthy (Expr.eval σ (.constInt v)) = (v ≠ 0) := by
  simp [Truthy, Expr.eval]

@[simp]
theorem Truthy.eval_const_str : Truthy (Expr.eval σ (.constStr v)) = ¬ v.isEmpty := by
  simp [Truthy, Expr.eval]

/--
Falsiness: the result of evaluating an expression is "falsy" if it's 0
-/
def Falsy (v : Option Value) : Prop := match v with
  | some v => match v with
    | .int x => x = 0
    | .str s => s.isEmpty
  | none => False

@[simp]
theorem Falsy.eval_const_int : Falsy (Expr.eval σ (.constInt v)) = (v = 0) := by
  simp [Falsy, Expr.eval]

@[simp]
theorem Falsy.eval_const_str : Falsy (Expr.eval σ (.constStr v)) = v.isEmpty := by
  simp [Falsy, Expr.eval]

@[simp]
theorem Falsy.some_zero : Falsy (some (.int v)) = (v = 0) := by
  simp [Falsy]

@[simp]
theorem Falsy.not_none : Falsy none = False := by
  simp [Falsy]

def Value.truthy : Value → Prop
  | .int x => x ≠ 0
  | .str s => ¬ s.isEmpty

instance : Decidable (Falsy v) :=  -- inferInstanceAs (Decidable (v = 0))
  match v with
  | some v => match v with
    | .int x => if h : x = 0 then .isTrue h else .isFalse h
    | .str s => if h : s.isEmpty then .isTrue h else .isFalse h
  | none => .isFalse id

theorem Truthy.not_falsy : Truthy v → ¬Falsy v := by
  intro h1 h2
  simp [Truthy, Falsy] at *
  cases v <;> simp at *
  case some v =>
    cases v <;> simp at *
    case int x =>
      contradiction
    case str s =>
      rw [h2] at h1
      contradiction

namespace Stmt

/--
Big-step semantics: `BigStep σ s σ'` means that running the program `s` in the starting state `σ` is
termination with the final state `σ'`.
-/
inductive BigStep : Env → Stmt → Env → Prop where
  | skip :
    BigStep σ (imp {skip;}) σ
  | seq :
    BigStep σ s1 σ' → BigStep σ' s2 σ'' →
    BigStep σ (imp{ ~s1 ~s2}) σ''
  | assign :
    e.eval σ = some v →
    BigStep σ (imp {~x := ~e;}) (σ.set x v)
  | ifTrue :
    Truthy (c.eval σ) → BigStep σ s1 σ' →
    BigStep σ (imp {if (~c) {~s1} else {~s2}}) σ'
  | ifFalse :
    Falsy (c.eval σ) → BigStep σ s2 σ' →
    BigStep σ (imp {if (~c) {~s1} else {~s2}}) σ'
  | whileTrue :
    Truthy (c.eval σ) →
    BigStep σ body σ' →
    BigStep σ' (imp {while (~c) {~body}}) σ'' →
    BigStep σ (imp {while (~c) {~body}}) σ''
  | whileFalse :
    Falsy (c.eval σ) →
    BigStep σ (imp {while (~c) {~body}}) σ

attribute [simp] BigStep.skip

syntax term:60 " / " term:61 " ↓ " term:62 : term
macro_rules
  | `($s / $σ ↓ $σ') => `(BigStep $σ $s $σ')

/--
`swap` terminates, and the resulting environment contains swapped inputs.
-/
example : ∃σ', BigStep (Env.init 0 |>.set "x" 5 |>.set "y" 22) swap σ' ∧ σ'.get "x" = 22 ∧ σ'.get "y" = 5 := by
  unfold swap
  apply Exists.intro
  constructor
  . apply BigStep.seq
    . apply BigStep.assign
      simp [Expr.eval, Env.get, Env.set]
      rfl
    . apply BigStep.seq
      . apply BigStep.assign
        simp [Expr.eval, Env.get, Env.set]
        rfl
      . apply BigStep.assign
        simp [Expr.eval, Env.get, Env.set]
        rfl
  . simp [Env.get, Env.set]

/--
`swap` terminates, and the resulting environment contains swapped inputs. This proof is shorter.
-/
example : ∃σ', BigStep (Env.init 0 |>.set "x" 5 |>.set "y" 22) swap σ' ∧ σ'.get "x" = 22 ∧ σ'.get "y" = 5 := by
  repeat' constructor

/--
`swap` terminates, and the resulting environment contains swapped inputs. This version works no
matter what the input values are.
-/
example : ∃σ', BigStep (Env.init 0 |>.set "x" x |>.set "y" y) swap σ' ∧ σ'.get "x" = y ∧ σ'.get "y" = x  := by
  repeat' constructor

/--
`min` computes the minimum of its inputs.
-/
-- example : ∃σ', BigStep (Env.init 0 |>.set "x" x |>.set "y" y) min σ' ∧ if x < y then σ'.get "min" = x else σ'.get "min" = y := by
--   unfold min
--   by_cases h : x < y
--   . apply Exists.intro; constructor
--     . apply BigStep.ifTrue
--       . simp [Expr.eval, Expr.BinOp.apply, Env.get, Env.set, *]
--       . constructor; simp [Expr.eval, Env.get, Env.set]; rfl
--     . simp [Env.get, Env.set]
--       intro; contradiction
--   . apply Exists.intro; constructor
--     . apply BigStep.ifFalse
--       . simp [Expr.eval, Expr.BinOp.apply, Env.get, Env.set, *]
--       . constructor; simp [Expr.eval, Env.get, Env.set]; rfl
--     . simp [Env.get, Env.set]
--       intro; contradiction

def loop := imp {while (1) {skip;}}

/--
`loop` is really an infinite loop - there is no final state that it can result in.
-/
theorem infinite_loop : ¬ BigStep σ loop σ' := by
  generalize h' : loop = l
  intro h
  induction h <;> try (simp [loop, *] at *; done)
  case whileTrue =>
    simp [*]
  case whileFalse cFalse =>
    unfold loop at h'
    cases h'
    simp at cFalse

/--
Run a program, with the depth of the recursive calls limited by the `Nat` parameter. Returns `none`
if the program doesn't terminate fast enough or if some other problem means the result is undefined
(e.g. division by zero).
 -/
def run (σ : Env) (s : Stmt) : Nat → Option Env
  | 0 => none
  | n + 1 =>
    match s with
    | imp {skip;} =>
      some σ
    | imp {~s1 ~s2} => do
      let σ' ← run σ s1 n
      run σ' s2 n
    | imp {~x := ~e;} => do
      let v ← e.eval σ
      pure (σ.set x v)
    | imp {if (~c) {~s1} else {~s2}} => do
      let grd := Truthy $ c.eval σ
      if grd then
        run σ s2 n
      else
        run σ s1 n
    | imp {while (~c) {~s1}} => do
      let grd := Truthy $ c.eval σ
      if grd then
        pure σ
      else
        let σ' ← run σ s1 n
        run σ' (imp {while (~c) {~s1}}) n

/--
`run` is correct: if it returns an answer, then that final state can be reached by the big-step
semantics. This is not total correctness - `run` could always return `none` - but it does increase
confidence.
-/
theorem run_some_implies_big_step : run σ s n = some σ' → BigStep σ s σ' := by
  intro term
  induction σ, s, n using run.induct generalizing σ' <;> unfold run at term <;> simp_all
  case case3 σ n s1 s2 ih1 ih2 =>
    sorry
  sorry
  sorry
  sorry
  sorry
  sorry

--   let ⟨σ'', ⟨st1, st2⟩⟩ := term
--   constructor
--   . apply ih1
--     apply st1
--   . apply ih2
--     apply st2
-- case case4 =>
--   let ⟨σ'', ⟨evEq, setEq⟩⟩ := term
--   subst_eqs
--   constructor; assumption
-- case case5 ih1 ih2 =>
--   let ⟨v, ⟨evEq, step⟩⟩ := term
--   by_cases h : v = 0
--   . subst_eqs; simp at *
--     apply BigStep.ifFalse
--     . simp [Falsy, *]
--     . exact ih1 step
--   . subst_eqs; simp at *
--     apply BigStep.ifTrue
--     . simp [Truthy, *]
--     . simp [*] at step
--       apply ih2; assumption
-- case case6 ih1 ih2 =>
--   let ⟨v, ⟨evEq, step⟩⟩ := term
--   by_cases h : v = 0
--   . subst_eqs; simp at *
--     apply BigStep.whileFalse
--     simp [Falsy, *]
--   . subst_eqs; simp [*] at *
--     simp [h] at step
--     let ⟨σ', ⟨oneStep, loopStep⟩⟩ := step
--     apply BigStep.whileTrue
--     . rw [evEq]
--       simp [*]
--     . apply ih1
--       exact oneStep
--     . apply ih2
--       exact loopStep
