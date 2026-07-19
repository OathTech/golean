import GoLean.StrictJson
import GoLean.GoCore.Syntax

/-!
# Native frontend lowering

Decodes the native wire schema (`golean-native-v1`, emitted by
`tools/nativefrontend`) directly into a clean `GoCore.Program`, failing closed
on anything not yet modeled. This is the native analogue of `GobraToIR`, but
because `go/types` resolved names and types up front, the lowering is a direct
structural map with no recovery heuristics.

The wire is a typed Go AST (Go's grammar with resolved types attached). The
GoCore-specific desugaring lives here and is inspectable:

- `x := e` / `var x T = e`  →  `initialization` then `assign`
- `return e`                →  assign the result local, then `returnStmt`
- `for init; c; post {..}`  →  `block[init; while c (block[body; post])]`
- `if init; c {..} else ..` →  `block[init; ifThenElse c ..]`
- `x += e` / `x++`          →  `assign x (op x e)`

This module is intentionally incremental: each new Go construct adds one wire
tag and one lowering case. Unmodeled constructs are explicit adapter errors.
-/

namespace GoLean.NativeToIR

open Lean GoLean GoLean.GoCore
open GoLean.StrictJson

/-- A GoCore statement plus the result parameters of the enclosing function,
threaded so `return` can assign the named result locals. -/
private abbrev LowerM := Except String

private def fail {α} (msg : String) : LowerM α := .error s!"native lowering: {msg}"

/-! ## Types -/

private def intKindOfName (name : String) : LowerM IntKind :=
  match name with
  | "int" => pure .int
  | "uint" => pure .uint
  | "int8" => pure .int8
  | "uint8" => pure .uint8
  | "int16" => pure .int16
  | "uint16" => pure .uint16
  | "int32" => pure .int32
  | "uint32" => pure .uint32
  | "int64" => pure .int64
  | "uint64" => pure .uint64
  | "byte" => pure .uint8
  | "rune" => pure .int32
  | "uintptr" => pure .uint64
  | other => fail s!"unsupported integer kind {other}"

partial def decodeTy (path : String) (json : Json) : LowerM Ty := do
  let obj ← StrictJson.obj path json
  let kind ← StrictJson.string s!"{path}.kind" (← StrictJson.field path obj "kind")
  match kind with
  | "bool" => pure .bool
  | "string" => pure .string
  | "int" =>
      let name ← StrictJson.string s!"{path}.int" (← StrictJson.field path obj "int")
      pure (.int (← intKindOfName name))
  | "pointer" => pure (.pointer (← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")))
  | "slice" => pure (.slice (← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")))
  | "array" =>
      let len ← StrictJson.nat s!"{path}.len" (← StrictJson.field path obj "len")
      pure (.array len (← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")))
  | "map" =>
      let key ← decodeTy s!"{path}.key" (← StrictJson.field path obj "key")
      let value ← decodeTy s!"{path}.value" (← StrictJson.field path obj "value")
      pure (.map key value)
  | "named" =>
      pure (.defined ⟨← StrictJson.string s!"{path}.name" (← StrictJson.field path obj "name")⟩)
  | "interface" =>
      pure (.interface ⟨← StrictJson.string s!"{path}.name" (← StrictJson.field path obj "name")⟩)
  | other => fail s!"unsupported type kind {other} at {path}"

private def decodeParam (path : String) (json : Json) : LowerM Param := do
  let obj ← StrictJson.obj path json
  let id ← StrictJson.string s!"{path}.id" (← StrictJson.field path obj "id")
  let typ ← decodeTy s!"{path}.type" (← StrictJson.field path obj "type")
  pure { id, typ }

/-! ## Expressions

GoCore has no call expression (calls are statements), so calls are handled at
the statement layer. Any call reaching `decodeExpr` is a nested call in
expression position, which is not yet modeled. -/

private def optType (path : String) (obj : StrictJson.Obj) : LowerM (Option Ty) := do
  match obj.get? "type" with
  | some t => pure (some (← decodeTy s!"{path}.type" t))
  | none => pure none

private def intKindOfOptType : Option Ty → IntKind
  | some (.int k) => k
  | _ => .int

partial def decodeExpr (path : String) (json : Json) : LowerM Expr := do
  let obj ← StrictJson.obj path json
  let tag ← StrictJson.string s!"{path}.expr" (← StrictJson.field path obj "expr")
  match tag with
  | "ident" =>
      pure (.var (← StrictJson.string s!"{path}.name" (← StrictJson.field path obj "name")))
  | "int" =>
      let s ← StrictJson.string s!"{path}.value" (← StrictJson.field path obj "value")
      match s.toInt? with
      | some v => pure (.intLit v (intKindOfOptType (← optType path obj)))
      | none => fail s!"invalid integer literal {s} at {path}"
  | "bool" =>
      pure (.boolLit (← StrictJson.bool s!"{path}.value" (← StrictJson.field path obj "value")))
  | "string" =>
      let s ← StrictJson.string s!"{path}.value" (← StrictJson.field path obj "value")
      pure (.stringLit (GoString.fromLeanString s))
  | "nil" => pure (.nil (← optType path obj))
  | "ref" =>
      pure (.ref (← StrictJson.string s!"{path}.id" (← StrictJson.field path obj "id")))
  | "deref" =>
      let ptr ← decodeExpr s!"{path}.ptr" (← StrictJson.field path obj "ptr")
      let typ ← decodeTy s!"{path}.type" (← StrictJson.field path obj "type")
      pure (.deref ptr typ)
  | "field-get" =>
      let recv ← decodeExpr s!"{path}.recv" (← StrictJson.field path obj "recv")
      let typeId ← StrictJson.string s!"{path}.typeId" (← StrictJson.field path obj "typeId")
      let field ← StrictJson.string s!"{path}.field" (← StrictJson.field path obj "field")
      pure (.fieldGet recv ⟨typeId⟩ field)
  | "field-addr" =>
      let base ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let typeId ← StrictJson.string s!"{path}.typeId" (← StrictJson.field path obj "typeId")
      let field ← StrictJson.string s!"{path}.field" (← StrictJson.field path obj "field")
      pure (.fieldAddr base ⟨typeId⟩ field)
  | "index-get" =>
      let base ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let index ← decodeExpr s!"{path}.index" (← StrictJson.field path obj "index")
      pure (.indexGet base index)
  | "index-addr" =>
      let base ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let index ← decodeExpr s!"{path}.index" (← StrictJson.field path obj "index")
      pure (.indexAddr base index)
  | "builtin-len" =>
      let operand ← decodeExpr s!"{path}.operand" (← StrictJson.field path obj "operand")
      pure (.length operand (some (← decodeTy s!"{path}.operandType" (← StrictJson.field path obj "operandType"))))
  | "builtin-cap" =>
      let operand ← decodeExpr s!"{path}.operand" (← StrictJson.field path obj "operand")
      pure (.capacity operand (some (← decodeTy s!"{path}.operandType" (← StrictJson.field path obj "operandType"))))
  | "map-get" =>
      let base ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let index ← decodeExpr s!"{path}.index" (← StrictJson.field path obj "index")
      let keyTy ← decodeTy s!"{path}.keyType" (← StrictJson.field path obj "keyType")
      let valueTy ← decodeTy s!"{path}.valueType" (← StrictJson.field path obj "valueType")
      pure (.mapGet base index keyTy valueTy)
  | "slice" =>
      let base ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let low ← decodeExpr s!"{path}.low" (← StrictJson.field path obj "low")
      let high ← decodeExpr s!"{path}.high" (← StrictJson.field path obj "high")
      let max ← (match obj.get? "max" with
        | some m => do pure (some (← decodeExpr s!"{path}.max" m))
        | none => pure none)
      pure (.slice base low high max)
  | "convert" =>
      let target ← decodeTy s!"{path}.target" (← StrictJson.field path obj "target")
      let x ← decodeExpr s!"{path}.x" (← StrictJson.field path obj "x")
      pure (.convert target x)
  | "default" =>
      pure (.defaultValue (← decodeTy s!"{path}.type" (← StrictJson.field path obj "type")))
  | "struct-lit" =>
      let target ← decodeTy s!"{path}.target" (← StrictJson.field path obj "target")
      let args ← StrictJson.array s!"{path}.args" (← StrictJson.field path obj "args")
      pure (.structLit target (← args.mapIdxM (fun i a => decodeExpr s!"{path}.args[{i}]" a)))
  | "array-lit" =>
      let length ← StrictJson.nat s!"{path}.length" (← StrictJson.field path obj "length")
      let elem ← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")
      let elems ← StrictJson.array s!"{path}.elems" (← StrictJson.field path obj "elems")
      let pairs ← elems.mapIdxM (fun i el => do
        let eo ← StrictJson.obj s!"{path}.elems[{i}]" el
        let index ← StrictJson.int s!"{path}.elems[{i}].index" (← StrictJson.field s!"{path}.elems[{i}]" eo "index")
        let value ← decodeExpr s!"{path}.elems[{i}].value" (← StrictJson.field s!"{path}.elems[{i}]" eo "value")
        pure (index, value))
      pure (.arrayLit length elem pairs)
  | "unary" =>
      let op ← StrictJson.string s!"{path}.op" (← StrictJson.field path obj "op")
      let x ← decodeExpr s!"{path}.x" (← StrictJson.field path obj "x")
      match op with
      | "-" => pure (.sub (.intLit 0 (intKindOfOptType (← optType path obj))) x)
      | "!" => pure (.not x)
      | "^" => pure (.bitNeg x)
      | other => fail s!"unsupported unary operator {other}"
  | "binary" =>
      let op ← StrictJson.string s!"{path}.op" (← StrictJson.field path obj "op")
      let x ← decodeExpr s!"{path}.x" (← StrictJson.field path obj "x")
      let y ← decodeExpr s!"{path}.y" (← StrictJson.field path obj "y")
      decodeBinary path obj op x y
  | "call" => fail "call in expression position is not modeled (calls are statements)"
  | other => fail s!"unsupported expression {other} at {path}"
where
  decodeBinary (path : String) (obj : StrictJson.Obj) (op : String) (x y : Expr) : LowerM Expr := do
    let operandTy : LowerM Ty := do
      match obj.get? "operandType" with
      | some t => decodeTy s!"{path}.operandType" t
      | none => fail s!"comparison at {path} missing operandType"
    match op with
    | "+" => pure (.add x y)
    | "-" => pure (.sub x y)
    | "*" => pure (.mul x y)
    | "/" => pure (.div x y)
    | "%" => pure (.mod x y)
    | "&" => pure (.bitAnd x y)
    | "|" => pure (.bitOr x y)
    | "^" => pure (.bitXor x y)
    | "&^" => pure (.bitClear x y)
    | "<<" => pure (.shiftLeft x y)
    | ">>" => pure (.shiftRight x y)
    | "&&" => pure (.and x y)
    | "||" => pure (.or x y)
    | "==" => pure (.eqCmp (← operandTy) x y)
    | "!=" => pure (.neqCmp (← operandTy) x y)
    | "<" => pure (.lessCmp x y)
    | "<=" => pure (.atMostCmp x y)
    | ">" => pure (.greaterCmp x y)
    | ">=" => pure (.atLeastCmp x y)
    | other => fail s!"unsupported binary operator {other}"

/-- Turn an expression used as an lvalue into a GoCore assignee. Plain locals
map to `.var`; addressable forms (deref/field/index) are added incrementally. -/
private def exprAsAssignee (path : String) : Expr → LowerM Assignee
  | .var id => pure (.var id)
  | .deref e _ => pure (.addr e)
  | other => .error s!"native lowering: expression at {path} is not an assignable location ({repr other})"

/-- Combine a compound-assignment target and rhs (`x op= e` → `x op e`). Only
arithmetic/bitwise/shift operators are valid here. -/
private def decodeCompound (op : String) (lhs rhs : Expr) : LowerM Expr :=
  match op with
  | "+" => pure (.add lhs rhs)
  | "-" => pure (.sub lhs rhs)
  | "*" => pure (.mul lhs rhs)
  | "/" => pure (.div lhs rhs)
  | "%" => pure (.mod lhs rhs)
  | "&" => pure (.bitAnd lhs rhs)
  | "|" => pure (.bitOr lhs rhs)
  | "^" => pure (.bitXor lhs rhs)
  | "&^" => pure (.bitClear lhs rhs)
  | "<<" => pure (.shiftLeft lhs rhs)
  | ">>" => pure (.shiftRight lhs rhs)
  | other => .error s!"native lowering: unsupported compound operator {other}"

/-- A decoded assignment target and whether it introduces a fresh local. -/
private structure Target where
  assignee : Assignee
  declare : Option Param

private def decodeTarget (path : String) (json : Json) : LowerM Target := do
  let obj ← StrictJson.obj path json
  let tag ← StrictJson.string s!"{path}.target" (← StrictJson.field path obj "target")
  match tag with
  | "declare" =>
      let id ← StrictJson.string s!"{path}.id" (← StrictJson.field path obj "id")
      let typ ← decodeTy s!"{path}.type" (← StrictJson.field path obj "type")
      pure { assignee := .var id, declare := some { id, typ } }
  | "var" =>
      let id ← StrictJson.string s!"{path}.id" (← StrictJson.field path obj "id")
      pure { assignee := .var id, declare := none }
  | "blank" =>
      pure { assignee := .unsupported "blank assignment target", declare := none }
  | "addr" =>
      let e ← decodeExpr s!"{path}.expr" (← StrictJson.field path obj "expr")
      pure { assignee := .addr e, declare := none }
  | other => fail s!"unsupported assignment target {other} at {path}"

private def targetAssignee (t : Target) : LowerM Assignee := pure t.assignee

/-- The expression that reads a declared local target (used to index into a
freshly-built slice/map temp). -/
private def targetBaseExpr (t : Target) : Expr :=
  match t.assignee with
  | .var id => .var id
  | _ => .var "$lit"

private def declaresOf (targets : Array Target) : LowerM (Array Stmt) := do
  pure (targets.filterMap (fun t => t.declare.map Stmt.initialization))

/-- Whether a wire assignment target is the blank identifier `_`. -/
private def targetIsBlank (json : Json) : Bool :=
  match json.getObjVal? "target" with
  | .ok (.str "blank") => true
  | _ => false

/-- An optional string field: a JSON string, or `null`/absent → `none`. -/
private def optString (obj : StrictJson.Obj) (key : String) : Option String :=
  match obj.get? key with
  | some (.str s) => some s
  | _ => none

/-- The declared type carried on a wire expression node (fallback `int`). -/
private def exprTypeOf (path : String) (json : Json) : LowerM Ty := do
  let obj ← StrictJson.obj path json
  match obj.get? "type" with
  | some t => decodeTy s!"{path}.type" t
  | none => pure (.int .int)

/-! ## Statements -/

/-- Detect `m[k]` (a map index) as the RHS of a comma-ok lookup. -/
private def asMapGet? (json : Json) : LowerM (Option (Json × Json × Json × Json)) := do
  match json.getObjVal? "expr" with
  | .ok (.str "map-get") =>
      let obj ← StrictJson.obj "map-get" json
      pure (some (← StrictJson.field "map-get" obj "base", ← StrictJson.field "map-get" obj "index",
        ← StrictJson.field "map-get" obj "keyType", ← StrictJson.field "map-get" obj "valueType"))
  | _ => pure none

/-- Detect a call whose result feeds an assignment / return / expression
statement, so it can lower to a GoCore call statement. -/
private def asCall? (json : Json) : LowerM (Option (String × Array Json)) := do
  match json.getObjVal? "expr" with
  | .ok (.str "call") =>
      let obj ← StrictJson.obj "call" json
      let name ← StrictJson.string "call.func" (← StrictJson.field "call" obj "func")
      let args ← StrictJson.array "call.args" (← StrictJson.field "call" obj "args")
      pure (some (name, args))
  | _ => pure none

mutual

/-- Lower a statement. `results` are the enclosing function's result params. -/
partial def decodeStmt (results : Array Param) (path : String) (json : Json) : LowerM Stmt := do
  let obj ← StrictJson.obj path json
  let tag ← StrictJson.string s!"{path}.stmt" (← StrictJson.field path obj "stmt")
  match tag with
  | "block" =>
      let body ← StrictJson.array s!"{path}.body" (← StrictJson.field path obj "body")
      pure (.block #[] (← body.mapIdxM (fun i s => decodeStmt results s!"{path}.body[{i}]" s)))
  | "return" =>
      decodeReturn results path obj
  | "assign" =>
      decodeAssign results path obj
  | "var" =>
      decodeVar path obj
  | "if" =>
      decodeIf results path obj
  | "for" =>
      decodeFor results path obj
  | "incdec" =>
      let op ← StrictJson.string s!"{path}.op" (← StrictJson.field path obj "op")
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let read ← decodeExpr s!"{path}.read" (← StrictJson.field path obj "read")
      let one : Expr := .intLit 1 (intKindOfOptType (← optType path obj))
      let rhs := if op == "-" then Expr.sub read one else Expr.add read one
      pure (.assign t.assignee rhs)
  | "compound-assign" =>
      let op ← StrictJson.string s!"{path}.op" (← StrictJson.field path obj "op")
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let read ← decodeExpr s!"{path}.read" (← StrictJson.field path obj "read")
      let rhs ← decodeExpr s!"{path}.rhs" (← StrictJson.field path obj "rhs")
      let combined ← decodeCompound op read rhs
      pure (.assign t.assignee combined)
  | "expr" =>
      let e ← StrictJson.field path obj "expr"
      match ← asCall? e with
      | some (name, args) =>
          pure (.call #[] ⟨name⟩ (← args.mapIdxM (fun i a => decodeExpr s!"{path}.expr.args[{i}]" a)))
      | none => fail s!"expression statement is not a call at {path} (calls are the only effectful expressions modeled)"
  | "range" =>
      decodeRange results path obj
  | "new" =>
      -- &T{...}: allocate `value` and bind its address into `target`.
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let value ← decodeExpr s!"{path}.value" (← StrictJson.field path obj "value")
      let elemTy ← decodeTy s!"{path}.elemType" (← StrictJson.field path obj "elemType")
      pure (.seqn ((← declaresOf #[t]).push (.newValue t.assignee value (some elemTy))))
  | "make-slice" =>
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let elemTy ← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")
      let lenE ← decodeExpr s!"{path}.len" (← StrictJson.field path obj "len")
      let capE ← (match obj.get? "cap" with
        | some c => do pure (some (← decodeExpr s!"{path}.cap" c))
        | none => pure none)
      pure (.seqn ((← declaresOf #[t]).push (.makeSlice t.assignee elemTy lenE capE)))
  | "make-map" =>
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let keyTy ← decodeTy s!"{path}.keyType" (← StrictJson.field path obj "keyType")
      let valTy ← decodeTy s!"{path}.valueType" (← StrictJson.field path obj "valueType")
      pure (.seqn ((← declaresOf #[t]).push (.makeMap t.assignee keyTy valTy none)))
  | "map-assign" =>
      let base ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let index ← decodeExpr s!"{path}.index" (← StrictJson.field path obj "index")
      let value ← decodeExpr s!"{path}.value" (← StrictJson.field path obj "value")
      let keyTy ← decodeTy s!"{path}.keyType" (← StrictJson.field path obj "keyType")
      let valTy ← decodeTy s!"{path}.valueType" (← StrictJson.field path obj "valueType")
      pure (.mapAssign base index value keyTy valTy)
  | "slice-lit" =>
      -- slice literal: makeSlice into a temp, then assign each element.
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let elemTy ← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")
      let length ← StrictJson.nat s!"{path}.length" (← StrictJson.field path obj "length")
      let elems ← StrictJson.array s!"{path}.elems" (← StrictJson.field path obj "elems")
      let lenLit : Expr := .intLit (Int.ofNat length) .int
      let mut stmts ← declaresOf #[t]
      stmts := stmts.push (.makeSlice t.assignee elemTy lenLit (some lenLit))
      for i in [:elems.size] do
        match elems[i]? with
        | some el =>
            let eo ← StrictJson.obj s!"{path}.elems[{i}]" el
            let index ← StrictJson.int s!"{path}.elems[{i}].index" (← StrictJson.field s!"{path}.elems[{i}]" eo "index")
            let value ← decodeExpr s!"{path}.elems[{i}].value" (← StrictJson.field s!"{path}.elems[{i}]" eo "value")
            stmts := stmts.push (.assign (.addr (.indexAddr (targetBaseExpr t) (.intLit index .int))) value)
        | none => pure ()
      pure (.seqn stmts)
  | "map-lit" =>
      -- map literal: makeMap into a temp, then assign each entry.
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let keyTy ← decodeTy s!"{path}.keyType" (← StrictJson.field path obj "keyType")
      let valTy ← decodeTy s!"{path}.valueType" (← StrictJson.field path obj "valueType")
      let entries ← StrictJson.array s!"{path}.entries" (← StrictJson.field path obj "entries")
      let base : Expr :=
        match t.assignee with
        | .var id => .var id
        | _ => .var "$maplit"
      let mut stmts ← declaresOf #[t]
      stmts := stmts.push (.makeMap t.assignee keyTy valTy none)
      for i in [:entries.size] do
        match entries[i]? with
        | some e =>
            let eo ← StrictJson.obj s!"{path}.entries[{i}]" e
            let key ← decodeExpr s!"{path}.entries[{i}].key" (← StrictJson.field s!"{path}.entries[{i}]" eo "key")
            let value ← decodeExpr s!"{path}.entries[{i}].value" (← StrictJson.field s!"{path}.entries[{i}]" eo "value")
            stmts := stmts.push (.mapAssign base key value keyTy valTy)
        | none => pure ()
      pure (.seqn stmts)
  | "break" => pure .breakStmt
  | "continue" => pure .continueStmt
  | other => fail s!"unsupported statement {other} at {path}"

/-- Lower `for k, v := range X`. Map range is the `mapRange` primitive; index
ranges (slice/array/int) desugar to an index `while` loop. The index is
incremented at the top of the loop body (guarded by a first-iteration flag) so
`continue` still advances it, matching Go. -/
partial def decodeRange (results : Array Param) (path : String) (obj : StrictJson.Obj) : LowerM Stmt := do
  let kind ← StrictJson.string s!"{path}.kind" (← StrictJson.field path obj "kind")
  let keyVar := optString obj "keyVar"
  let valVar := optString obj "valVar"
  let collJson ← StrictJson.field path obj "collection"
  let coll ← decodeExpr s!"{path}.collection" collJson
  let body ← decodeStmt results s!"{path}.body" (← StrictJson.field path obj "body")
  match kind with
  | "map" =>
      let keyTy ← decodeTy s!"{path}.keyType" (← StrictJson.field path obj "keyType")
      let valTy ← decodeTy s!"{path}.valueType" (← StrictJson.field path obj "valueType")
      pure (.mapRange keyVar valVar coll keyTy valTy body)
  | "slice" | "array" | "int" =>
      let collTy ← exprTypeOf s!"{path}.collection" collJson
      let intTy : Ty := .int .int
      let ridx : Expr := .var "$ridx"
      -- Length: len(collection) for slice/array; the int itself for int range.
      let lenExpr : Expr := if kind == "int" then .var "$rcoll" else .length (.var "$rcoll") none
      -- Per-iteration loop-variable bindings.
      let mut iter : Array Stmt := #[
        -- increment index at top except on the first iteration
        .ifThenElse (.var "$rfirst")
          (.assign (.var "$rfirst") (.boolLit false))
          (.assign (.var "$ridx") (.add ridx (.intLit 1 .int))),
        -- exit when the index reaches the length
        .ifThenElse (.atLeastCmp ridx (.var "$rlen")) .breakStmt (.seqn #[])
      ]
      match keyVar with
      | some k => iter := iter ++ #[.initialization { id := k, typ := intTy }, .assign (.var k) ridx]
      | none => pure ()
      if kind != "int" then
        match valVar with
        | some v =>
            let elemTy ← decodeTy s!"{path}.elemType" (← StrictJson.field path obj "elemType")
            iter := iter ++ #[.initialization { id := v, typ := elemTy }, .assign (.var v) (.indexGet (.var "$rcoll") ridx)]
        | none => pure ()
      iter := iter.push body
      pure (.block #[] #[
        .initialization { id := "$rcoll", typ := collTy }, .assign (.var "$rcoll") coll,
        .initialization { id := "$rlen", typ := intTy }, .assign (.var "$rlen") lenExpr,
        .initialization { id := "$ridx", typ := intTy }, .assign (.var "$ridx") (.intLit 0 .int),
        .initialization { id := "$rfirst", typ := .bool }, .assign (.var "$rfirst") (.boolLit true),
        .while (.boolLit true) (.block #[] iter)
      ])
  | other => fail s!"unsupported range kind {other} at {path}"

partial def decodeReturn (results : Array Param) (path : String) (obj : StrictJson.Obj) : LowerM Stmt := do
  let rs ← StrictJson.array s!"{path}.results" (← StrictJson.field path obj "results")
  if rs.size == 0 then
    pure .returnStmt
  else if rs.size == results.size then
    -- return e1, .., en  →  assign each result local, then returnStmt.
    let mut stmts : Array Stmt := #[]
    for i in [:rs.size] do
      match rs[i]?, results[i]? with
      | some rj, some rp =>
          stmts := stmts.push (.assign (.var rp.id) (← decodeExpr s!"{path}.results[{i}]" rj))
      | _, _ => pure ()
    pure (.seqn (stmts.push .returnStmt))
  else
    fail s!"return arity {rs.size} does not match {results.size} results at {path}"

partial def decodeAssign (results : Array Param) (path : String) (obj : StrictJson.Obj) : LowerM Stmt := do
  let _ := results
  let lhs ← StrictJson.array s!"{path}.lhs" (← StrictJson.field path obj "lhs")
  let rhs ← StrictJson.array s!"{path}.rhs" (← StrictJson.field path obj "rhs")
  -- Single call on the RHS assigned to targets → GoCore call statement.
  if rhs.size == 1 then
    match ← asCall? rhs[0]! with
    | some (name, args) =>
        let targets ← lhs.mapIdxM (fun i t => decodeTarget s!"{path}.lhs[{i}]" t)
        let assignees ← targets.mapM (fun t => targetAssignee t)
        return .seqn ((← declaresOf targets) ++ #[.call assignees ⟨name⟩ (← args.mapIdxM (fun i a => decodeExpr s!"{path}.args[{i}]" a))])
    | none => pure ()
  -- Comma-ok map lookup: `v, ok := m[k]`.
  if lhs.size == 2 && rhs.size == 1 then
    match ← asMapGet? rhs[0]! with
    | some (baseJ, indexJ, keyTyJ, valTyJ) =>
        let t0 ← decodeTarget s!"{path}.lhs[0]" lhs[0]!
        let t1 ← decodeTarget s!"{path}.lhs[1]" lhs[1]!
        let base ← decodeExpr s!"{path}.rhs[0].base" baseJ
        let index ← decodeExpr s!"{path}.rhs[0].index" indexJ
        let keyTy ← decodeTy s!"{path}.rhs[0].keyType" keyTyJ
        let valTy ← decodeTy s!"{path}.rhs[0].valueType" valTyJ
        return .seqn ((← declaresOf #[t0, t1]).push (.mapLookup t0.assignee t1.assignee base index keyTy valTy))
    | none => pure ()
  if lhs.size != rhs.size then
    fail s!"assignment arity {lhs.size} != {rhs.size} at {path}"
  else if lhs.any targetIsBlank then
    -- Blank targets discard their value but must still evaluate the RHS (so a
    -- panic in `_ = a/b` fires). Evaluate every RHS left-to-right into a fresh
    -- temp, then write back the non-blank targets from their temps.
    let mut stmts : Array Stmt := #[]
    let mut i := 0
    for r in rhs do
      let ty ← exprTypeOf s!"{path}.rhs[{i}]" r
      let tmp := s!"$t{i}"
      stmts := stmts.push (.initialization { id := tmp, typ := ty })
      stmts := stmts.push (.assign (.var tmp) (← decodeExpr s!"{path}.rhs[{i}]" r))
      i := i + 1
    i := 0
    for l in lhs do
      if !targetIsBlank l then
        let t ← decodeTarget s!"{path}.lhs[{i}]" l
        stmts := stmts ++ (← declaresOf #[t])
        stmts := stmts.push (.assign t.assignee (.var s!"$t{i}"))
      i := i + 1
    pure (.seqn stmts)
  else
    -- No blanks: declarations first, then a simultaneous multi-assign so swaps
    -- are correct.
    let targets ← lhs.mapIdxM (fun i t => decodeTarget s!"{path}.lhs[{i}]" t)
    let exprs ← rhs.mapIdxM (fun i e => decodeExpr s!"{path}.rhs[{i}]" e)
    let assignees ← targets.mapM (fun t => targetAssignee t)
    let decls ← declaresOf targets
    if assignees.size == 1 then
      pure (.seqn (decls.push (.assign assignees[0]! exprs[0]!)))
    else
      pure (.seqn (decls.push (.assignMany assignees exprs)))

partial def decodeVar (path : String) (obj : StrictJson.Obj) : LowerM Stmt := do
  let decls ← StrictJson.array s!"{path}.decls" (← StrictJson.field path obj "decls")
  let mut stmts : Array Stmt := #[]
  for i in [:decls.size] do
    let d ← StrictJson.obj s!"{path}.decls[{i}]" decls[i]!
    let id ← StrictJson.string s!"{path}.decls[{i}].id" (← StrictJson.field path d "id")
    let typ ← decodeTy s!"{path}.decls[{i}].type" (← StrictJson.field path d "type")
    stmts := stmts.push (.initialization { id, typ })
    match d.get? "init" with
    | some initE => stmts := stmts.push (.assign (.var id) (← decodeExpr s!"{path}.decls[{i}].init" initE))
    | none => pure ()
  pure (.seqn stmts)

partial def decodeIf (results : Array Param) (path : String) (obj : StrictJson.Obj) : LowerM Stmt := do
  let cond ← decodeExpr s!"{path}.cond" (← StrictJson.field path obj "cond")
  let thenS ← decodeStmt results s!"{path}.then" (← StrictJson.field path obj "then")
  let elseS ← (match obj.get? "else" with
    | some e => decodeStmt results s!"{path}.else" e
    | none => pure (.seqn #[]))
  let core := Stmt.ifThenElse cond thenS elseS
  match obj.get? "init" with
  | some initE =>
      pure (.block #[] #[← decodeStmt results s!"{path}.init" initE, core])
  | none => pure core

partial def decodeFor (results : Array Param) (path : String) (obj : StrictJson.Obj) : LowerM Stmt := do
  let cond ← (match obj.get? "cond" with
    | some c => decodeExpr s!"{path}.cond" c
    | none => pure (.boolLit true))
  let body ← decodeStmt results s!"{path}.body" (← StrictJson.field path obj "body")
  let post ← (match obj.get? "post" with
    | some p => do pure #[← decodeStmt results s!"{path}.post" p]
    | none => pure #[])
  let loopBody := Stmt.block #[] (#[body] ++ post)
  let loop := Stmt.while cond loopBody
  match obj.get? "init" with
  | some initE => pure (.block #[] #[← decodeStmt results s!"{path}.init" initE, loop])
  | none => pure loop

end

/-! ## Program -/

private def decodeFieldDef (path : String) (json : Json) : LowerM FieldDef := do
  let obj ← StrictJson.obj path json
  let name ← StrictJson.string s!"{path}.name" (← StrictJson.field path obj "name")
  let typ ← decodeTy s!"{path}.type" (← StrictJson.field path obj "type")
  pure { name, typ }

private def decodeTypeDef (path : String) (json : Json) : LowerM (TypeId × TypeDef) := do
  let obj ← StrictJson.obj path json
  let name ← StrictJson.string s!"{path}.name" (← StrictJson.field path obj "name")
  let defObj ← StrictJson.obj s!"{path}.def" (← StrictJson.field path obj "def")
  let kind ← StrictJson.string s!"{path}.def.kind" (← StrictJson.field s!"{path}.def" defObj "kind")
  match kind with
  | "struct" =>
      let fields ← StrictJson.array s!"{path}.def.fields" (← StrictJson.field s!"{path}.def" defObj "fields")
      pure (⟨name⟩, .struct (← fields.mapIdxM (fun i f => decodeFieldDef s!"{path}.def.fields[{i}]" f)))
  | "alias" =>
      pure (⟨name⟩, .alias (← decodeTy s!"{path}.def.target" (← StrictJson.field s!"{path}.def" defObj "target")))
  | other => fail s!"unsupported type definition kind {other} at {path}"

private def decodeFunc (path : String) (json : Json) : LowerM Func := do
  let obj ← StrictJson.obj path json
  let name ← StrictJson.string s!"{path}.name" (← StrictJson.field path obj "name")
  let params ← StrictJson.array s!"{path}.params" (← StrictJson.field path obj "params")
  let results ← StrictJson.array s!"{path}.results" (← StrictJson.field path obj "results")
  let args ← params.mapIdxM (fun i p => decodeParam s!"{path}.params[{i}]" p)
  let res ← results.mapIdxM (fun i p => decodeParam s!"{path}.results[{i}]" p)
  let body ← decodeStmt res s!"{path}.body" (← StrictJson.field path obj "body")
  pure { id := ⟨name⟩, args, results := res, body }

/-- A method lowers to a receiver-scoped GoCore function (`RecvType.method`,
receiver as the first parameter) plus a `MethodInfo` dispatch-table entry. -/
private def decodeMethod (path : String) (json : Json) : LowerM (Func × MethodInfo) := do
  let obj ← StrictJson.obj path json
  let name ← StrictJson.string s!"{path}.name" (← StrictJson.field path obj "name")
  let recvType ← StrictJson.string s!"{path}.recvType" (← StrictJson.field path obj "recvType")
  let recv ← decodeParam s!"{path}.recv" (← StrictJson.field path obj "recv")
  let params ← StrictJson.array s!"{path}.params" (← StrictJson.field path obj "params")
  let results ← StrictJson.array s!"{path}.results" (← StrictJson.field path obj "results")
  let args ← params.mapIdxM (fun i p => decodeParam s!"{path}.params[{i}]" p)
  let res ← results.mapIdxM (fun i p => decodeParam s!"{path}.results[{i}]" p)
  let body ← decodeStmt res s!"{path}.body" (← StrictJson.field path obj "body")
  let funcId : FuncId := ⟨s!"{recvType}.{name}"⟩
  let func : Func := { id := funcId, args := #[recv] ++ args, results := res, body }
  let info : MethodInfo := { name, funcId, recv := recv.typ }
  pure (func, info)

partial def decodeProgram (json : Json) : LowerM Program := do
  let obj ← StrictJson.obj "program" json
  let schema ← StrictJson.string "program.schema" (← StrictJson.field "program" obj "schema")
  if schema != "golean-native-v1" then
    fail s!"unexpected schema {schema}"
  let funcsJson ← StrictJson.array "program.funcs" (← StrictJson.field "program" obj "funcs")
  let funcs ← funcsJson.mapIdxM (fun i f => decodeFunc s!"program.funcs[{i}]" f)
  let typesJson ← StrictJson.array "program.types" (← StrictJson.field "program" obj "types")
  let declaredDefs ← typesJson.mapIdxM (fun i t => decodeTypeDef s!"program.types[{i}]" t)
  -- The canonical empty struct (map[K]struct{} set idiom) is always available.
  let typeDefs := #[(⟨"struct{}"⟩, TypeDef.struct #[])] ++ declaredDefs
  let methodsJson ← StrictJson.array "program.methods" (← StrictJson.field "program" obj "methods")
  let methodPairs ← methodsJson.mapIdxM (fun i m => decodeMethod s!"program.methods[{i}]" m)
  -- Method bodies are executable functions (looked up by FuncId on call);
  -- MethodInfo is the dispatch table.
  pure { typeDefs, funcs := funcs ++ methodPairs.map Prod.fst, methods := methodPairs.map Prod.snd }

end GoLean.NativeToIR
