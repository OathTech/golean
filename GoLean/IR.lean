import GoLean.Runtime

namespace GoLean

inductive Ty where
  | unit
  | bool
  | int
  | ptr (to : Ty)
  deriving Repr, BEq

inductive Expr where
  | litUnit
  | litBool (value : Bool)
  | litInt (value : Int)
  | local (name : String)
  deriving Repr, BEq

inductive Stmt where
  | skip
  | seq (first second : Stmt)
  | unsupported (feature : String)
  deriving Repr, BEq

structure Func where
  name : String
  params : List (String × Ty)
  result : Ty
  body : Stmt
  deriving Repr

end GoLean
