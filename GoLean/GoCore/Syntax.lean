import GoLean.GoCore.Value

namespace GoLean.GoCore

inductive Ty where
  | bool
  | int (kind : IntKind := .int)
  | string
  | array (length : Nat) (elem : Ty)
  | slice (elem : Ty)
  | map (key value : Ty)
  | pointer (elem : Ty)
  | interface (name : String)
  | defined (name : String)
  | unsupported (feature : String)
  deriving Repr, BEq, Inhabited

structure Param where
  id : String
  typ : Ty
  deriving Repr, BEq

structure FieldDef where
  name : String
  typ : Ty
  deriving Repr, BEq

inductive TypeDef where
  | struct (fields : Array FieldDef)
  | alias (target : Ty)
  | unsupported (feature : String)
  deriving Repr, BEq

inductive Expr where
  | var (id : String)
  | nil (typ : Option Ty)
  | intLit (value : Int) (kind : IntKind := .unbounded "integer")
  | stringLit (value : GoString)
  | boolLit (value : Bool)
  | convert (typ : Ty) (operand : Expr)
  | bytesFromString (operand : Expr)
  | stringFromByteSlice (operand : Expr)
  | stringFromRune (operand : Expr)
  | add (left right : Expr)
  | sub (left right : Expr)
  | mul (left right : Expr)
  | div (left right : Expr)
  | mod (left right : Expr)
  | shiftLeft (left right : Expr)
  | shiftRight (left right : Expr)
  | bitAnd (left right : Expr)
  | bitOr (left right : Expr)
  | bitXor (left right : Expr)
  | bitClear (left right : Expr)
  | bitNeg (operand : Expr)
  | eqCmp (typ : Ty) (left right : Expr)
  | neqCmp (typ : Ty) (left right : Expr)
  | atMostCmp (left right : Expr)
  | atLeastCmp (left right : Expr)
  | lessCmp (left right : Expr)
  | greaterCmp (left right : Expr)
  | and (left right : Expr)
  | or (left right : Expr)
  | not (operand : Expr)
  | ref (id : String)
  | deref (ptr : Expr) (typ : Ty)
  | structLit (typ : Ty) (args : Array Expr)
  | fieldGet (recv : Expr) (typeName fieldName : String)
  | fieldAddr (base : Expr) (typeName fieldName : String)
  | arrayLit (length : Nat) (elem : Ty) (args : Array (Int × Expr))
  | defaultValue (typ : Ty)
  | toInterface (target dynamic : Ty) (operand : Expr)
  | typeAssert (operand : Expr) (target : Ty)
  | indexGet (base index : Expr)
  | indexAddr (base index : Expr)
  | mapGet (base index : Expr) (keyTy valueTy : Ty)
  | slice (base low high : Expr) (max : Option Expr)
  | length (operand : Expr) (typ : Option Ty := none)
  | capacity (operand : Expr) (typ : Option Ty := none)
  | unsupported (feature : String)
  deriving Repr, BEq, Inhabited

inductive Assignee where
  | var (id : String)
  | addr (loc : Expr)
  | unsupported (feature : String)
  deriving Repr, BEq, Inhabited

inductive Stmt where
  | seqn (stmts : Array Stmt)
  | block (decls : Array Param) (stmts : Array Stmt)
  | initialization (var : Param)
  | assign (left : Assignee) (right : Expr)
  | assignMany (left : Array Assignee) (right : Array Expr)
  | newValue (target : Assignee) (value : Expr)
  | makeSlice (target : Assignee) (elem : Ty) (len : Expr) (cap : Option Expr)
  | makeMap (target : Assignee) (key value : Ty) (initialSpace : Option Expr)
  | mapAssign (base index value : Expr) (keyTy valueTy : Ty)
  | mapLookup (target okTarget : Assignee) (base index : Expr) (keyTy valueTy : Ty)
  | typeAssert (target okTarget : Assignee) (expr : Expr) (targetTy : Ty)
  | appendSlice (target : Assignee) (elem : Ty) (slice elems : Expr)
  | copySlice (target : Assignee) (dst src : Expr)
  | call (targets : Array Assignee) (name : String) (args : Array Expr)
  | ifThenElse (cond : Expr) (thenBranch elseBranch : Stmt)
  | while (cond : Expr) (body : Stmt)
  | returnStmt
  | breakStmt
  | continueStmt
  | label (name : String)
  | unsupported (feature : String)
  deriving Repr, BEq, Inhabited

structure Func where
  name : String
  args : Array Param
  results : Array Param
  body : Stmt
  deriving Repr, BEq

structure MethodInfo where
  name : String
  uniqueName : String
  recv : Ty
  deriving Repr, BEq

structure Program where
  typeDefs : Array (String × TypeDef) := #[]
  funcs : Array Func
  methods : Array MethodInfo := #[]
  deriving Repr, BEq

def findFunctionIn? (funcs : Array Func) (name : String) : Option Func :=
  funcs.foldl
    (fun found func =>
      match found with
      | some f => some f
      | none => if func.name == name then some func else none)
    none
