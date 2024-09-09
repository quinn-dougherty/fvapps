import Imp.Expr.Basic

open Lean

namespace Imp

inductive Value where
| str : String -> Value
| int : Int -> Value
| bool : Bool -> Value

instance : OfNat Value n := by
  constructor
  exact (Value.int n)

/-- An environment maps variables names to their values (no pointers) -/
def Env := String → Value

namespace Env

/-- Set a value in an environment -/
def set (x : String) (v : Value) (σ : Env) : Env :=
  fun y => if x == y then v else σ y

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
  | .not, .bool b => (Value.bool ∘ Bool.not) <$> some b
  | _, _ => none

/-- Helper that implements binary operators -/
def BinOp.apply : BinOp → Value → Value → Option Value
  | .plus, .int i, .int j => some $ Value.int (i + j)
  | .minus, .int i, .int j => some $ Value.int (i - j)
  | .times, .int i, .int j => some $ Value.int (i * j)
  | .div, .int i, .int j => if j == 0 then none else some $ Value.int (i / j)
  | .and, .bool b, .bool c => some $ Value.bool (b && c)
  | .or, .bool b, .bool c => some $ Value.bool (b || c)
  | .eq, .int i, .int j => some $ Value.bool (i == j)
  | .eq, .bool b, .bool c => some $ Value.bool (b == c)
  | .eq, .str s, .str t => some $ Value.bool (s == t)
  | .le, .int i, .int j => some $ Value.bool (i <= j)
  | .lt, .int i, .int j => some $ Value.bool (i < j)
  |.append, .str s, .str t => some $ Value.str (s ++ t)
  | _, _, _ => none

/--
Evaluates an expression, finding the value if it has one.

Expressions that divide by zero don't have values - the result is undefined.
-/
def eval (σ : Env) : Expr → Option Value
  | .constInt i => some $ Value.int i
  | .constBool b => some $ .bool b
  | .constStr s => some $ .str s
  | .var x => σ.get x
  | .un op e => do
    let v ← e.eval σ
    op.apply v
  | .bin op e1 e2 => do
    let v1 ← e1.eval σ
    let v2 ← e2.eval σ
    op.apply v1 v2
