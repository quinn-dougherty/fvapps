import Imp.Expr.Eval
import Imp.Stmt.BigStep
import Imp.Stmt.Basic

open Imp Stmt

@[simp]
def ValidHoareTriple (P : Env → Prop) (c : Stmt) (Q : Env → Prop) : Prop :=
  forall (st st' : Env), P st -> c / st ↓ st' -> Q st'

syntax "{{" term:90 "}} " term:91 " {{" term:92 "}}" : term
macro_rules
  | `({{$P}}$c{{$Q}}) => `(ValidHoareTriple $P $c $Q)

theorem hoare_skip : forall P, {{P}}(imp { skip; }){{P}} := by
  intro P
  simp [ValidHoareTriple]
  intros st st' h1 h2
  cases h2; assumption

theorem hoare_seq : forall P Q R c1 c2, {{P}}c1{{Q}} -> {{Q}}c2{{R}} -> {{P}}(imp { ~c1 ~c2 }){{R}} := by
  intro P Q R c1 c2
  simp [ValidHoareTriple]
  intros h1 h2 st st' hP h3
  cases h3 with
  | seq h3 h4 =>
    apply h2
    apply h1
    apply hP
    apply h3
    apply h4

def assertionSubstitution (P : Env → Prop) (x : String) (a : Expr) : Env → Prop :=
  fun st => P (st.setOption x (Expr.eval st a))

syntax term " [ " ident " |-> " term "]" : term
macro_rules
  | `($P [$x |-> $a]) => `(assertionSubstitution $P $x $a)

theorem hoare_assign : forall P x a, {{P[x |-> a]}}(imp { ~x := a; }){{P}} := by
  intros P x a
  simp [ValidHoareTriple]
  intros st st' h1 h2
  cases h2 with
  | assign h3 =>
    simp [assertionSubstitution] at h1
    simp [Expr.eval, Env.get] at h3
    simp [Env.setOption] at h1
    sorry
