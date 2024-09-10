namespace Imp.Expr

/-- Unary operators -/
inductive UnOp where
  | neg
  | not
deriving Repr, DecidableEq

/-- Binary operators -/
inductive BinOp where
  | plus | minus | times | div
  | and | or
  | lt | le | eq
  | append
deriving Repr, DecidableEq

end Expr

/-- Expressions -/
inductive Expr where
  | constInt (i : Int)
  | constStr (x : String)
  | var (name : String)
  | un (op : Expr.UnOp) (e : Expr)
  | bin (op : Expr.BinOp) (e1 e2 : Expr)
deriving Repr, DecidableEq
