import Imp.Expr.Basic

open Lean

namespace Imp

inductive Value where
| str : String -> Value
| int : Int -> Value

instance : OfNat Value n := by
  constructor
  exact (Value.int n)

/-- An environment maps variables names to their values (no pointers) -/
def Env := String → Value

namespace Env

/-- Set a value in an environment -/
def set (x : String) (v : Value) (σ : Env) : Env :=
  fun y => if x == y then v else σ y

def setOption (x : String) (v : Option Value) (σ : Env) : Env :=
  match v with
  | some v => σ.set x v
  | none => σ

/-- Look up a value in an environment -/
def get (x : String) (σ : Env) : Value :=
  σ x

/-- Initialize an environment, setting all uninitialized memory to `i` -/
def init (i : Value) : Env := fun _ => i

@[simp]
theorem get_init : (Env.init v).get x = v := by rfl

@[simp]
theorem get_set_same {σ : Env} : (σ.set x v).get x = v := by
  simp [get, set]

@[simp]
theorem get_set_different {σ : Env} : x ≠ y → (σ.set x v).get y = σ.get y := by
  intros
  simp [get, set, *]

end Env

namespace Expr

/-- Helper that implements unary operators -/
def UnOp.apply : UnOp → Value → Option Value
  | .neg, .int i => (Value.int ∘ Int.neg) <$> some i
  | .not, .int b => if b == 0 then some (Value.int 1) else some (Value.int 0)
  | .not, .str s => some $ Value.int (if s.isEmpty then 1 else 0)
  | _, _ => none

/-- Helper that implements binary operators -/
def BinOp.apply : BinOp → Value → Value → Option Value
  | .plus, .int i, .int j => some $ Value.int (i + j)
  | .minus, .int i, .int j => some $ Value.int (i - j)
  | .times, .int i, .int j => some $ Value.int (i * j)
  | .div, .int i, .int j => if j == 0 then none else some $ Value.int (i / j)
  | .and, .int b, .int c => some $ Value.int (b * c)
  | .and, .str b, .str c => some $ Value.int (b ++ c).length
  | .or, .int b, .int c => some $ Value.int (b + c)
  | .or, .str s, .str t => some $ Value.str (s ++ t)
  | .eq, .int i, .int j => some $ if i == j then Value.int 1 else Value.int 0
  | .eq, .str s, .str t => some $ if s == t then (Value.int 1) else (Value.int 0)
  | .le, .int i, .int j => some (if i <= j then Value.int 1 else Value.int 0)
  | .lt, .int i, .int j => some $ if i < j then Value.int 1 else Value.int 0
  | .append, .str s, .str t => some $ Value.str (s ++ t)
  | _, _, _ => none

/--
Evaluates an expression, finding the value if it has one.

Expressions that divide by zero don't have values - the result is undefined.
-/
def eval (σ : Env) : Expr → Option Value
  | .constInt i => some $ .int i
  | .constStr s => some $ .str s
  | .var x => σ.get x
  | .un op e => do
    let v ← e.eval σ
    op.apply v
  | .bin op e1 e2 => do
    let v1 ← e1.eval σ
    let v2 ← e2.eval σ
    op.apply v1 v2
