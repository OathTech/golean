import GoLean.GoCore.Value

namespace GoLean.GoCore

-- `FuncId` now lives in `Value.lean` (beside `TypeId`) so `GoValue.funcVal`
-- can carry it; it is re-exported by this module's namespace.

inductive Ty where
  | bool
  | int (kind : IntKind := .int)
  | string
  | array (length : Nat) (elem : Ty)
  | slice (elem : Ty)
  | map (key value : Ty)
  | pointer (elem : Ty)
  /-- A function type. Structural detail is carried for zero values and
  typing only — dispatch is by `FuncId`, never by this. -/
  | funcType (params results : List Ty)
  | interface (id : TypeId)
  | defined (id : TypeId)
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
  /-- Build a **function value**: the lifted callee's identity plus the
  expressions producing its captured values (addresses — Go captures by
  reference; §8 of the coverage-scoping note). Operands evaluate left to
  right like any strict form. -/
  | funcVal (fid : FuncId) (captured : Array Expr)
  /-- A resolved location literal — evaluates to its address. Proof-facing:
  introduced only by the relation's name-resolution substitution (`substLoc`),
  never emitted by the frontend. The location-resolved core (Goose-aligned;
  `docs/2026-07-19_reshape-mechanics-design.md`) rewrites `var`/`ref` into this
  so the relation performs no runtime name lookup. -/
  | locLit (l : Loc)
  | deref (ptr : Expr) (typ : Ty)
  | structLit (typ : Ty) (args : Array Expr)
  | fieldGet (recv : Expr) (typeId : TypeId) (fieldName : String)
  | fieldAddr (base : Expr) (typeId : TypeId) (fieldName : String)
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
  /-- The `recover()` builtin. Not a strict operator: its value depends on
  the continuation (it recovers exactly when called directly by a deferred
  function invoked by a panic — the unwinding arc,
  `docs/2026-07-25_unwinding-arc.md` §A1). -/
  | recoverCall
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
  /-- A **breakable scope**: `break` inside `body` exits this statement;
  `continue`/`return` pass through to the enclosing loop/frame. Go's
  `switch` and `select` bodies are breakable scopes, so this is Go runtime
  semantics, not a frontend quirk (W2 slice 2,
  `docs/2026-07-24_sequential-coverage-scoping.md`): a frontend flag
  desugaring would be a shortcut that labeled break and `select` later
  have to undo, which the arc's defer-never-foreclose rule forbids. -/
  | breakable (body : Stmt)
  | initialization (var : Param)
  | assign (left : Assignee) (right : Expr)
  | assignMany (left : Array Assignee) (right : Array Expr)
  | newValue (target : Assignee) (value : Expr) (typ : Option Ty := none)
  | makeSlice (target : Assignee) (elem : Ty) (len : Expr) (cap : Option Expr)
  | makeMap (target : Assignee) (key value : Ty) (initialSpace : Option Expr)
  | mapAssign (base index value : Expr) (keyTy valueTy : Ty)
  | mapLookup (target okTarget : Assignee) (base index : Expr) (keyTy valueTy : Ty)
  | typeAssert (target okTarget : Assignee) (expr : Expr) (targetTy : Ty)
  | appendSlice (target : Assignee) (elem : Ty) (slice elems : Expr)
  | copySlice (target : Assignee) (dst src : Expr)
  | call (targets : Array Assignee) (func : FuncId) (args : Array Expr)
  /-- Call through a function VALUE (a closure, method value, or func-typed
  variable). The callee expression evaluates to a `GoValue.funcVal`, whose
  captured values are prepended to the arguments at frame entry — the
  lambda-lifting protocol of §8. Calling a `nil` func value panics. -/
  | callValue (targets : Array Assignee) (callee : Expr) (args : Array Expr)
  /-- `defer f(args)`: evaluate the callee and arguments NOW, and prepend
  the pending call to the innermost frame's defer chain, which runs at
  frame exit before the results are read (W3 §9). -/
  | deferCall (callee : Expr) (args : Array Expr)
  | ifThenElse (cond : Expr) (thenBranch elseBranch : Stmt)
  | while (cond : Expr) (body : Stmt)
  /-- Map iteration primitive (the one nondeterministic iteration form). The
  abstract map is an unordered finite map; the iteration order is drawn from
  the choice oracle, one choice per step (next key among those remaining).
  Index-able ranges (slice/array/string/int) desugar to `while` and are not
  represented here. See `docs/nondeterminism-design.md`. `keyVar`/`valVar` are
  `none` for blank or absent range variables. -/
  | mapRange (keyVar valVar : Option String) (mapExpr : Expr) (keyTy valTy : Ty) (body : Stmt)
  | returnStmt
  | breakStmt
  | continueStmt
  /-- The `panic(v)` builtin: evaluate the payload, then start unwinding
  with a fresh one-entry panic chain. The payload expression carries the
  Go `any`-conversion (lowering wraps non-interface arguments in
  `.toInterface`); a nil-interface payload stays nil — the oracle runs in
  GOPATH mode, where `panic(nil)` keeps its legacy semantics (`recover()`
  returns nil; see `panicPayload`). The unwinding arc,
  `docs/2026-07-25_unwinding-arc.md`. -/
  | panicStmt (payload : Expr)
  | label (name : String)
  | unsupported (feature : String)
  deriving Repr, BEq, Inhabited

structure Func where
  id : FuncId
  args : Array Param
  results : Array Param
  body : Stmt
  deriving Repr, BEq

structure MethodInfo where
  name : String
  funcId : FuncId
  recv : Ty
  deriving Repr, BEq

structure Program where
  typeDefs : Array (TypeId × TypeDef) := #[]
  funcs : Array Func
  methods : Array MethodInfo := #[]
  deriving Repr, BEq

def findFunctionIn? (funcs : Array Func) (id : FuncId) : Option Func :=
  funcs.foldl
    (fun found func =>
      match found with
      | some f => some f
      | none => if func.id == id then some func else none)
    none
