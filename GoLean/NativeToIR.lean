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

/-- The lowering monad: failure plus a reader carrying the PROGRAM's
package-level-variable count (audit response 2026-08-05, C1): every
`globaladdr` gid must be strictly below it, checked AT THE DECODE
BOUNDARY — the one-boundary-constructor collision-check rule. Without
the check a malformed wire's dangling gid did NOT go stuck as
originally claimed: `Heap.set` materializes cells for unseeded
locations, so an out-of-range gid aliased onto whatever the allocator
handed out next (e.g. the subject's result cell) and produced a silent
wrong answer. The driver-level `StateWf` assert after seeding
(`runProgramM`/`enumSetup`) is the defense-in-depth second net. -/
private abbrev LowerM := ReaderT Nat (Except String)

private def fail {α} (msg : String) : LowerM α :=
  fun _ => .error s!"native lowering: {msg}"

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
  | "float" =>
      let name ← StrictJson.string s!"{path}.float" (← StrictJson.field path obj "float")
      match name with
      | "float32" => pure (.float .float32)
      | "float64" => pure (.float .float64)
      | other => fail s!"unsupported float kind {other}"
  | "pointer" => pure (.pointer (← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")))
  | "slice" => pure (.slice (← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")))
  | "array" =>
      let len ← StrictJson.nat s!"{path}.len" (← StrictJson.field path obj "len")
      pure (.array len (← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")))
  | "chan" =>
      let dir ← StrictJson.string s!"{path}.dir" (← StrictJson.field path obj "dir")
      let elem ← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")
      match dir with
      | "both" => pure (.chan .both elem)
      | "send" => pure (.chan .send elem)
      | "recv" => pure (.chan .recv elem)
      | other => fail s!"unsupported channel direction {other} at {path}"
  | "map" =>
      let key ← decodeTy s!"{path}.key" (← StrictJson.field path obj "key")
      let value ← decodeTy s!"{path}.value" (← StrictJson.field path obj "value")
      pure (.map key value)
  | "named" =>
      pure (.defined ⟨← StrictJson.string s!"{path}.name" (← StrictJson.field path obj "name")⟩)
  | "interface" =>
      pure (.interface ⟨← StrictJson.string s!"{path}.name" (← StrictJson.field path obj "name")⟩)
  | "func" =>
      let params ← StrictJson.array s!"{path}.params" (← StrictJson.field path obj "params")
      let results ← StrictJson.array s!"{path}.results" (← StrictJson.field path obj "results")
      pure (.funcType
        (← params.toList.mapIdxM (fun i t => decodeTy s!"{path}.params[{i}]" t))
        (← results.toList.mapIdxM (fun i t => decodeTy s!"{path}.results[{i}]" t)))
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
  | "func-value" =>
      let fid ← StrictJson.string s!"{path}.func" (← StrictJson.field path obj "func")
      let captured ← StrictJson.array s!"{path}.captured" (← StrictJson.field path obj "captured")
      pure (.funcVal ⟨fid⟩
        (← captured.mapIdxM (fun i c => decodeExpr s!"{path}.captured[{i}]" c)))
  | "int" =>
      let s ← StrictJson.string s!"{path}.value" (← StrictJson.field path obj "value")
      match s.toInt? with
      | some v => pure (.intLit v (intKindOfOptType (← optType path obj)))
      | none => fail s!"invalid integer literal {s} at {path}"
  | "float" =>
      -- The EXACT RATIONAL of a float-typed constant (floats design note
      -- decision 5); the machine performs the single rounding. Fail
      -- closed on malformed rationals: non-integer strings, zero
      -- denominator, a missing/non-float kind.
      let numS ← StrictJson.string s!"{path}.num" (← StrictJson.field path obj "num")
      let denS ← StrictJson.string s!"{path}.den" (← StrictJson.field path obj "den")
      let kind ← match (← optType path obj) with
        | some (.float k) => pure k
        | some other => fail s!"float literal at {path} typed non-float ({repr other})"
        | none => fail s!"float literal at {path} carries no type"
      match numS.toInt?, denS.toNat? with
      | some num, some den =>
          if den == 0 then fail s!"float literal at {path} has zero denominator"
          else pure (.floatLit num den kind)
      | _, _ => fail s!"invalid float literal {numS}/{denS} at {path}"
  | "bool" =>
      pure (.boolLit (← StrictJson.bool s!"{path}.value" (← StrictJson.field path obj "value")))
  | "string" =>
      -- Literal VALUE as raw bytes: a Go string may be invalid UTF-8, which
      -- a JSON string cannot carry (wrong-answers slice 0b).
      let arr ← StrictJson.array s!"{path}.bytes" (← StrictJson.field path obj "bytes")
      let bytes ← arr.mapIdxM (fun i b => do
        let n ← StrictJson.nat s!"{path}.bytes[{i}]" b
        if n < 256 then pure (UInt8.ofNat n)
        else fail s!"string literal byte out of range at {path}.bytes[{i}]: {n}")
      pure (.stringLit { bytes })
  | "nil" => pure (.nil (← optType path obj))
  | "recover" => pure .recoverCall
  | "bytes-from-string" =>
      pure (.bytesFromString (← decodeExpr s!"{path}.x" (← StrictJson.field path obj "x")))
  | "min" =>
      let args ← StrictJson.array s!"{path}.args" (← StrictJson.field path obj "args")
      pure (.minOf (← args.mapIdxM (fun i a => decodeExpr s!"{path}.args[{i}]" a)))
  | "max" =>
      let args ← StrictJson.array s!"{path}.args" (← StrictJson.field path obj "args")
      pure (.maxOf (← args.mapIdxM (fun i a => decodeExpr s!"{path}.args[{i}]" a)))
  | "string-from-bytes" =>
      pure (.stringFromByteSlice (← decodeExpr s!"{path}.x" (← StrictJson.field path obj "x")))
  | "string-from-rune" =>
      pure (.stringFromRune (← decodeExpr s!"{path}.x" (← StrictJson.field path obj "x")))
  | "ref" =>
      pure (.ref (← StrictJson.string s!"{path}.id" (← StrictJson.field path obj "id")))
  | "globaladdr" =>
      -- A statically resolved package-level variable address (init slice,
      -- docs/2026-08-05_init-design.md §2): global `gid` (wire declaration
      -- order) lives at the driver-seeded cell `Loc.base ⟨gid⟩`. The gid
      -- assignment is the emitter's single collection loop (dense by
      -- construction), and the BOUND CHECK here is the decode-boundary
      -- collision check (audit response 2026-08-05, C1): a dangling gid
      -- does NOT go stuck at runtime — `Heap.set` materializes cells for
      -- unseeded locations, so it would alias the next allocation — a
      -- malformed wire refuses loud here instead.
      let gid ← StrictJson.nat s!"{path}.gid" (← StrictJson.field path obj "gid")
      let nGlobals ← read
      if gid < nGlobals then
        pure (.locLit (.base ⟨gid⟩))
      else
        fail s!"globaladdr gid {gid} out of range at {path} (program declares {nGlobals} global(s))"
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
      -- Proper negation (floats design note §4 rider): value-directed
      -- Expr.neg — int stays 0 - v at the OPERAND's kind, float is the
      -- IEEE sign-bit flip. The old `.sub (intLit 0) x` lowering was
      -- wrong at x = +0 (gave +0; Go gives -0 — floats/signed-zero).
      | "-" => pure (.neg x)
      | "!" => pure (.not x)
      | "^" => pure (.bitNeg x)
      | other => fail s!"unsupported unary operator {other}"
  | "binary" =>
      let op ← StrictJson.string s!"{path}.op" (← StrictJson.field path obj "op")
      let x ← decodeExpr s!"{path}.x" (← StrictJson.field path obj "x")
      let y ← decodeExpr s!"{path}.y" (← StrictJson.field path obj "y")
      decodeBinary path obj op x y
  | "to-interface" =>
      -- The interface-conversion wrap (interfaces campaign S3): the
      -- machine boxes the operand with the canonical dynamic type.
      let target ← decodeTy s!"{path}.target" (← StrictJson.field path obj "target")
      let dynamic ← decodeTy s!"{path}.dynamic" (← StrictJson.field path obj "dynamic")
      let operand ← decodeExpr s!"{path}.operand" (← StrictJson.field path obj "operand")
      pure (.toInterface target dynamic operand)
  | "type-assert" =>
      -- Single-result assert `x.(T)` — panics on mismatch.
      let operand ← decodeExpr s!"{path}.operand" (← StrictJson.field path obj "operand")
      let target ← decodeTy s!"{path}.target" (← StrictJson.field path obj "target")
      -- The operand's STATIC interface type, for Go's panic message.
      let source ← match obj.get? "source" with
        | some t => some <$> decodeTy s!"{path}.source" t
        | none => pure none
      pure (.typeAssert operand target source)
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
  | other => fail s!"expression at {path} is not an assignable location ({repr other})"

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
  | other => fail s!"unsupported compound operator {other}"

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
  | "map" =>
      -- A map-element delivery target (convergence round, BUG-030):
      -- consumed only by the channel-receive delivery plan; every other
      -- assignee position fails closed on it (`assigneeExpr` is `none`).
      let b ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let i ← decodeExpr s!"{path}.index" (← StrictJson.field path obj "index")
      let kt ← decodeTy s!"{path}.keyType" (← StrictJson.field path obj "keyType")
      let vt ← decodeTy s!"{path}.valueType" (← StrictJson.field path obj "valueType")
      pure { assignee := .mapElem b i kt vt, declare := none }
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

/-- Recognize a call through a func VALUE (a closure or func-typed
variable): the callee is an expression rather than a name (W5 §8). -/
private def asCallValue? (json : Json) : LowerM (Option (Json × Array Json)) := do
  match json.getObjVal? "expr" with
  | .ok (.str "call-value") =>
      let obj ← StrictJson.obj "call-value" json
      let callee ← StrictJson.field "call-value" obj "callee"
      let args ← StrictJson.array "call-value.args" (← StrictJson.field "call-value" obj "args")
      pure (some (callee, args))
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
  | "defer" =>
      let callee ← decodeExpr s!"{path}.callee" (← StrictJson.field path obj "callee")
      let args ← StrictJson.array s!"{path}.args" (← StrictJson.field path obj "args")
      pure (.deferCall callee
        (← args.mapIdxM (fun i a => decodeExpr s!"{path}.args[{i}]" a)))
  | "go" =>
      -- `go f(args)` (channels arc slice 2): the defer wire shape — the
      -- callee and arguments evaluate at the go statement, in the
      -- spawning goroutine; the spawn itself is the pool's step.
      let callee ← decodeExpr s!"{path}.callee" (← StrictJson.field path obj "callee")
      let args ← StrictJson.array s!"{path}.args" (← StrictJson.field path obj "args")
      pure (.goStmt callee
        (← args.mapIdxM (fun i a => decodeExpr s!"{path}.args[{i}]" a)))
  | "panic" =>
      -- The payload's `any`-conversion: a "wrap" type wraps via the
      -- machine's `toInterface` (its `dynamicTypeName?` fails closed on
      -- unsupported dynamics); no "wrap" means the argument is already an
      -- interface (or the untyped-nil payload).
      let value ← decodeExpr s!"{path}.value" (← StrictJson.field path obj "value")
      -- "runtimeError": the lowering SYNTHESIZED a Go runtime panic (today:
      -- the nil-interface method-value creation check, design note D6) —
      -- the payload boxes as the machine's `runtime.Error` sentinel so
      -- recover values, type asserts, and abort rendering all match Go's
      -- runtime errors, never a user string. A PRESENT key is decoded
      -- STRICTLY (audit F7: a malformed flag used to fall open to a
      -- user-string payload); `false` is well-formed and means "not a
      -- runtime error".
      let runtimeErr ← match obj.get? "runtimeError" with
        | some flag => StrictJson.bool s!"{path}.runtimeError" flag
        | none => pure false
      if runtimeErr then
        pure (.panicStmt (.toInterface (.interface ⟨"any"⟩)
          (.defined runtimeErrorTypeId) value))
      else
      match obj.get? "wrap" with
      | some t =>
          let ty ← decodeTy s!"{path}.wrap" t
          pure (.panicStmt (.toInterface (.interface ⟨"any"⟩) ty value))
      | none => pure (.panicStmt value)
  | "breakable" =>
      pure (.breakable (← decodeStmt results s!"{path}.body"
        (← StrictJson.field path obj "body")))
  | "return" =>
      decodeReturn results path obj
  | "assign" =>
      decodeAssign results path obj
  | "type-assert" =>
      -- Comma-ok assert `v, ok := x.(T)` (Stmt.typeAssert: never panics;
      -- blanks route to typed discard temps like decodeAssign's).
      let tJson ← StrictJson.field path obj "target"
      let okJson ← StrictJson.field path obj "okTarget"
      let e ← decodeExpr s!"{path}.expr" (← StrictJson.field path obj "expr")
      let ty ← decodeTy s!"{path}.targetType" (← StrictJson.field path obj "targetType")
      let mut decls : Array Stmt := #[]
      let mut vAssignee : Assignee := .unsupported "type-assert target"
      let mut okAssignee : Assignee := .unsupported "type-assert okTarget"
      if targetIsBlank tJson then
        decls := decls.push (.initialization { id := "$ta", typ := ty })
        vAssignee := .var "$ta"
      else
        let t ← decodeTarget s!"{path}.target" tJson
        decls := decls ++ (← declaresOf #[t])
        vAssignee := t.assignee
      if targetIsBlank okJson then
        decls := decls.push (.initialization { id := "$taok", typ := .bool })
        okAssignee := .var "$taok"
      else
        let okT ← decodeTarget s!"{path}.okTarget" okJson
        decls := decls ++ (← declaresOf #[okT])
        okAssignee := okT.assignee
      return .seqn (decls.push (.typeAssert vAssignee okAssignee e ty))
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
      -- The synthetic 1 takes the OPERAND's kind: float operands get a
      -- float-kinded literal (floats slice F3 — an int 1 would be a
      -- kind-mismatched operand in the machine; floats/incdec pins it).
      -- FAIL CLOSED on a non-numeric carried type (BUG-042: a named wire
      -- type silently defaulted to int here, producing a kind-mismatched
      -- add; the frontend now resolves defined types to the underlying
      -- basic kind, and a named type reaching this slot again is a
      -- frontend defect, never a default).
      let one : Expr ← match (← optType path obj) with
        | some (.float k) => pure (.floatLit 1 1 k)
        | some (.int k) => pure (.intLit 1 k)
        | none => pure (.intLit 1 .int)
        | some other => fail s!"incdec at {path} carries a non-numeric operand type ({repr other}) — the synthetic 1 has no kind to take"
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
      -- A bare statement-position call DISCARDS its results (spec
      -- §Expression statements: no `_ =` required). The machine's frame
      -- exit stores results into targets positionally and goes stuck on
      -- arity mismatch, so a value-returning callee needs typed discard
      -- temps — exactly decodeAssign's blank-target mechanism, driven by
      -- the call node's `resultTypes` (BUG-012 fix, arc-final audit F11,
      -- 2026-08-06). A wire without `resultTypes` keeps the old
      -- targetless lowering (fail-closed: stuck at frame exit if the
      -- callee returns values).
      let e ← StrictJson.field path obj "expr"
      let discardTemps (prefixName : String) (callJson : Json) :
          LowerM (Array Stmt × Array Assignee) := do
        let callObj ← StrictJson.obj s!"{path}.expr" callJson
        match callObj.get? "resultTypes" with
        | none => pure (#[], #[])
        | some rt => do
            let arr ← StrictJson.array s!"{path}.expr.resultTypes" rt
            let tys ← arr.mapIdxM (fun i t => decodeTy s!"{path}.expr.resultTypes[{i}]" t)
            let decls := tys.mapIdx (fun i ty =>
              Stmt.initialization { id := s!"{prefixName}{i}", typ := ty })
            let assignees := tys.mapIdx (fun i _ =>
              Assignee.var s!"{prefixName}{i}")
            pure (decls, assignees)
      match ← asCall? e with
      | some (name, args) =>
          let (decls, assignees) ← discardTemps "$cr" e
          let argsE ← args.mapIdxM (fun i a => decodeExpr s!"{path}.expr.args[{i}]" a)
          if decls.isEmpty then
            pure (.call #[] ⟨name⟩ argsE)
          else
            pure (.seqn (decls.push (.call assignees ⟨name⟩ argsE)))
      | none =>
          match ← asCallValue? e with
          | some (callee, args) =>
              let (decls, assignees) ← discardTemps "$cv" e
              let calleeE ← decodeExpr s!"{path}.expr.callee" callee
              let argsE ← args.mapIdxM (fun i a => decodeExpr s!"{path}.expr.args[{i}]" a)
              if decls.isEmpty then
                pure (.callValue #[] calleeE argsE)
              else
                pure (.seqn (decls.push (.callValue assignees calleeE argsE)))
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
  -- Channel statements (channels arc slice 1). All decode arms fail
  -- closed on malformed shapes (target counts, clause kinds, directions).
  | "make-chan" =>
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let elemTy ← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")
      let capE ← (match obj.get? "cap" with
        | some c => do pure (some (← decodeExpr s!"{path}.cap" c))
        | none => pure none)
      pure (.seqn ((← declaresOf #[t]).push (.makeChan t.assignee elemTy capE)))
  | "chan-send" =>
      let chE ← decodeExpr s!"{path}.ch" (← StrictJson.field path obj "ch")
      let value ← decodeExpr s!"{path}.value" (← StrictJson.field path obj "value")
      let elemTy ← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")
      pure (.chanSend chE value elemTy)
  | "chan-recv" =>
      let targetsJ ← StrictJson.array s!"{path}.targets" (← StrictJson.field path obj "targets")
      if targetsJ.size > 2 then
        fail s!"channel receive with {targetsJ.size} targets at {path}"
      let ts ← targetsJ.mapIdxM (fun i t => decodeTarget s!"{path}.targets[{i}]" t)
      let chE ← decodeExpr s!"{path}.ch" (← StrictJson.field path obj "ch")
      let elemTy ← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")
      pure (.seqn ((← declaresOf ts).push (.chanRecv (ts.map (·.assignee)) chE elemTy)))
  | "chan-close" =>
      pure (.closeChan (← decodeExpr s!"{path}.ch" (← StrictJson.field path obj "ch")))
  | "select" =>
      -- Receive-clause targets are the frontend's fresh temps; their
      -- declares lift OUT in front of the select (fresh names — the
      -- pre-declaration is unobservable), leaving plain var targets for
      -- the machine's post-selection stores.
      let clausesJ ← StrictJson.array s!"{path}.clauses" (← StrictJson.field path obj "clauses")
      let mut decls : Array Stmt := #[]
      let mut cls : Array (SelectClauseHead × Stmt) := #[]
      for i in [:clausesJ.size] do
        match clausesJ[i]? with
        | some cJ =>
            let cpath := s!"{path}.clauses[{i}]"
            let co ← StrictJson.obj cpath cJ
            let ckind ← StrictJson.string s!"{cpath}.clause" (← StrictJson.field cpath co "clause")
            let body ← decodeStmt results s!"{cpath}.body" (← StrictJson.field cpath co "body")
            match ckind with
            | "send" =>
                let chE ← decodeExpr s!"{cpath}.ch" (← StrictJson.field cpath co "ch")
                let value ← decodeExpr s!"{cpath}.value" (← StrictJson.field cpath co "value")
                let elemTy ← decodeTy s!"{cpath}.elem" (← StrictJson.field cpath co "elem")
                cls := cls.push (.send chE value elemTy, body)
            | "recv" =>
                let targetsJ ← StrictJson.array s!"{cpath}.targets" (← StrictJson.field cpath co "targets")
                if targetsJ.size > 2 then
                  fail s!"select receive with {targetsJ.size} targets at {cpath}"
                let ts ← targetsJ.mapIdxM (fun j t => decodeTarget s!"{cpath}.targets[{j}]" t)
                decls := decls ++ (← declaresOf ts)
                let chE ← decodeExpr s!"{cpath}.ch" (← StrictJson.field cpath co "ch")
                let elemTy ← decodeTy s!"{cpath}.elem" (← StrictJson.field cpath co "elem")
                cls := cls.push (.recv (ts.map (·.assignee)) chE elemTy, body)
            | other => fail s!"unsupported select clause kind {other} at {cpath}"
        | none => pure ()
      let default? ← (match obj.get? "default" with
        | some dJ => do pure (some (← decodeStmt results s!"{path}.default" dJ))
        | none => pure none)
      pure (.seqn (decls.push (.selectStmt cls default?)))
  | "map-delete" =>
      let base ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let index ← decodeExpr s!"{path}.index" (← StrictJson.field path obj "index")
      let keyTy ← decodeTy s!"{path}.keyType" (← StrictJson.field path obj "keyType")
      pure (.mapDelete base index keyTy)
  | "clear-map" =>
      pure (.clearMap (← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")))
  | "clear-slice" =>
      let base ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let elemTy ← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")
      pure (.clearSlice base elemTy)
  | "sort-slice" =>
      let base ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let elemTy ← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")
      pure (.sortSlice base elemTy)
  | "append" =>
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let elemTy ← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")
      let slice ← decodeExpr s!"{path}.slice" (← StrictJson.field path obj "slice")
      let elems ← decodeExpr s!"{path}.elems" (← StrictJson.field path obj "elems")
      pure (.seqn ((← declaresOf #[t]).push (.appendSlice t.assignee elemTy slice elems)))
  | "copy" =>
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let dst ← decodeExpr s!"{path}.dst" (← StrictJson.field path obj "dst")
      let src ← decodeExpr s!"{path}.src" (← StrictJson.field path obj "src")
      pure (.seqn ((← declaresOf #[t]).push (.copySlice t.assignee dst src)))
  | "map-compound-assign" =>
      -- m[k] op= v with base/key pre-hoisted by the frontend: read via
      -- mapGet, combine, store via mapAssign.
      let op ← StrictJson.string s!"{path}.op" (← StrictJson.field path obj "op")
      let base ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let index ← decodeExpr s!"{path}.index" (← StrictJson.field path obj "index")
      let read ← decodeExpr s!"{path}.read" (← StrictJson.field path obj "read")
      let rhs ← decodeExpr s!"{path}.rhs" (← StrictJson.field path obj "rhs")
      let keyTy ← decodeTy s!"{path}.keyType" (← StrictJson.field path obj "keyType")
      let valTy ← decodeTy s!"{path}.valueType" (← StrictJson.field path obj "valueType")
      let combined ← decodeCompound op read rhs
      pure (.mapAssign base index combined keyTy valTy)
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
  | "break-to" =>
      pure (.breakTo (← StrictJson.string s!"{path}.label" (← StrictJson.field path obj "label")))
  | "continue-to" =>
      pure (.continueTo (← StrictJson.string s!"{path}.label" (← StrictJson.field path obj "label")))
  | "labeled" =>
      -- A break/continue-targetable label. The machine label must sit
      -- DIRECTLY on the loop-forming statement (`contHeadLabel`'s
      -- placement invariant), so for/range push it inside their desugar;
      -- a switch's breakable is wrapped whole. Anything else fails
      -- closed (go/types only accepts these targets).
      let name ← StrictJson.string s!"{path}.label" (← StrictJson.field path obj "label")
      let bodyJson ← StrictJson.field path obj "body"
      let bobj ← StrictJson.obj s!"{path}.body" bodyJson
      let btag ← StrictJson.string s!"{path}.body.stmt"
        (← StrictJson.field s!"{path}.body" bobj "stmt")
      match btag with
      | "for" => decodeFor results s!"{path}.body" bobj (some name)
      | "range" => decodeRange results s!"{path}.body" bobj (some name)
      | "breakable" => pure (.labeled name (← decodeStmt results s!"{path}.body" bodyJson))
      | other => fail s!"labeled statement over unsupported form {other} at {path}"
  | other => fail s!"unsupported statement {other} at {path}"

/-- Lower `for k, v := range X`. Map range is the `mapRange` primitive; index
ranges (slice/array/int) desugar to an index `while` loop. The index is
incremented at the top of the loop body (guarded by a first-iteration flag) so
`continue` still advances it, matching Go. A `label` (from a wire "labeled"
wrapper) attaches DIRECTLY to the loop-forming statement — the machine's
`contHeadLabel` placement invariant. -/
partial def decodeRange (results : Array Param) (path : String) (obj : StrictJson.Obj)
    (label : Option String := none) : LowerM Stmt := do
  let kind ← StrictJson.string s!"{path}.kind" (← StrictJson.field path obj "kind")
  let keyVar := optString obj "keyVar"
  let valVar := optString obj "valVar"
  let collJson ← StrictJson.field path obj "collection"
  let coll ← decodeExpr s!"{path}.collection" collJson
  let body ← decodeStmt results s!"{path}.body" (← StrictJson.field path obj "body")
  let lab : Stmt → Stmt := fun st =>
    match label with
    | some l => .labeled l st
    | none => st
  match kind with
  | "map" =>
      let keyTy ← decodeTy s!"{path}.keyType" (← StrictJson.field path obj "keyType")
      let valTy ← decodeTy s!"{path}.valueType" (← StrictJson.field path obj "valueType")
      pure (lab (.mapRange keyVar valVar coll keyTy valTy body))
  | "chan" =>
      -- Range over a channel (channels arc slice 1): a comma-ok receive
      -- loop until closed-and-drained (spec §For statements; pinned by
      -- channels/range-closed and channels/range-edge/*). NON-snapshot —
      -- each iteration receives from the live channel; an open, drained
      -- channel blocks (the sequential slice's deadlocked run, probe
      -- p16). `keyVar` is the single iteration variable, freshly bound
      -- per iteration; the pattern follows the index-able ranges, which
      -- also desugar to `while` (only `mapRange` is primitive, for its
      -- nondeterministic order).
      let collTy ← exprTypeOf s!"{path}.collection" collJson
      let elemTy ← decodeTy s!"{path}.elemType" (← StrictJson.field path obj "elemType")
      let mut iter : Array Stmt := #[
        .chanRecv #[.var "$rrecv", .var "$rok"] (.var "$rcoll") elemTy,
        .ifThenElse (.not (.var "$rok")) .breakStmt (.seqn #[])
      ]
      match keyVar with
      | some k => iter := iter ++ #[.initialization { id := k, typ := elemTy }, .assign (.var k) (.var "$rrecv")]
      | none => pure ()
      iter := iter.push body
      pure (.block #[] #[
        .initialization { id := "$rcoll", typ := collTy }, .assign (.var "$rcoll") coll,
        .initialization { id := "$rrecv", typ := elemTy },
        .initialization { id := "$rok", typ := .bool },
        lab (.while (.boolLit true) (.block #[] iter))
      ])
  | "slice" | "array" | "int" | "array-pointer" =>
      let collTy ← exprTypeOf s!"{path}.collection" collJson
      let intTy : Ty := .int .int
      let ridx : Expr := .var "$ridx"
      -- Range over *[N]T (value form): the pointer binds once; each
      -- iteration reads the element THROUGH it, so writes to the array
      -- during the loop are observed and a nil pointer panics at the
      -- first read (pre-merge audit 2026-07-26). N is static.
      let arrPtrTy? ← (match obj.get? "arrType" with
        | some t => do pure (some (← decodeTy s!"{path}.arrType" t))
        | none => pure none)
      let arrPtrLen? ← (match obj.get? "len" with
        | some l => do pure (some (← StrictJson.nat s!"{path}.len" l))
        | none => pure none)
      -- Length: len(collection) for slice/array; the int itself for int
      -- range; the static N for array-pointer.
      let lenExpr : Expr :=
        if kind == "int" then .var "$rcoll"
        else match arrPtrLen? with
        | some n => .intLit (Int.ofNat n) .int
        | none => .length (.var "$rcoll") none
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
            let base : Expr :=
              match arrPtrTy? with
              | some arrTy => .deref (.var "$rcoll") arrTy
              | none => .var "$rcoll"
            iter := iter ++ #[.initialization { id := v, typ := elemTy }, .assign (.var v) (.indexGet base ridx)]
        | none => pure ()
      iter := iter.push body
      pure (.block #[] #[
        .initialization { id := "$rcoll", typ := collTy }, .assign (.var "$rcoll") coll,
        .initialization { id := "$rlen", typ := intTy }, .assign (.var "$rlen") lenExpr,
        .initialization { id := "$ridx", typ := intTy }, .assign (.var "$ridx") (.intLit 0 .int),
        .initialization { id := "$rfirst", typ := .bool }, .assign (.var "$rfirst") (.boolLit true),
        lab (.while (.boolLit true) (.block #[] iter))
      ])
  | "string" =>
      -- Rune iteration: the key is the rune's starting BYTE offset, the
      -- value the decoded rune (invalid encodings: U+FFFD, width 1 — the
      -- machine's decodeRuneAt). The next offset advances at the TOP of
      -- each iteration, before the body, so `continue` re-tests with the
      -- advance already applied.
      let intTy : Ty := .int .int
      let roff : Expr := .var "$roff"
      let mut iter : Array Stmt := #[
        .ifThenElse (.atLeastCmp (.var "$rnext") (.length (.var "$rcoll") none))
          .breakStmt (.seqn #[]),
        .initialization { id := "$roff", typ := intTy },
        .assign (.var "$roff") (.var "$rnext"),
        .assign (.var "$rnext") (.add roff (.runeSizeAt (.var "$rcoll") roff))
      ]
      match keyVar with
      | some k => iter := iter ++ #[.initialization { id := k, typ := intTy }, .assign (.var k) roff]
      | none => pure ()
      match valVar with
      | some v => iter := iter ++
          #[.initialization { id := v, typ := .int .int32 },
            .assign (.var v) (.runeAt (.var "$rcoll") roff)]
      | none => pure ()
      iter := iter.push body
      pure (.block #[] #[
        .initialization { id := "$rcoll", typ := .string }, .assign (.var "$rcoll") coll,
        .initialization { id := "$rnext", typ := intTy }, .assign (.var "$rnext") (.intLit 0 .int),
        lab (.while (.boolLit true) (.block #[] iter))
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
  -- Blank targets route to fresh discard temps.
  if rhs.size == 1 then
    match ← asCall? rhs[0]! with
    | some (name, args) =>
        -- Result types (when the frontend supplies them) type blank discard
        -- temps correctly; fall back to int only if absent.
        let callObj ← StrictJson.obj s!"{path}.rhs[0]" rhs[0]!
        let resultTypes ← (match callObj.get? "resultTypes" with
          | some rt => do
              let arr ← StrictJson.array s!"{path}.rhs[0].resultTypes" rt
              arr.mapIdxM (fun i t => decodeTy s!"{path}.rhs[0].resultTypes[{i}]" t)
          | none => pure #[])
        let mut decls : Array Stmt := #[]
        let mut assignees : Array Assignee := #[]
        for i in [:lhs.size] do
          let lj := lhs[i]!
          if targetIsBlank lj then
            let tmp := s!"$cr{i}"
            let ty := resultTypes[i]?.getD .int
            decls := decls.push (.initialization { id := tmp, typ := ty })
            assignees := assignees.push (.var tmp)
          else
            let t ← decodeTarget s!"{path}.lhs[{i}]" lj
            decls := decls ++ (← declaresOf #[t])
            assignees := assignees.push t.assignee
        return .seqn (decls.push (.call assignees ⟨name⟩ (← args.mapIdxM (fun i a => decodeExpr s!"{path}.args[{i}]" a))))
    | none => pure ()
  -- Same for a call through a func value.
  if rhs.size == 1 then
    match ← asCallValue? rhs[0]! with
    | some (calleeJ, args) =>
        let callObj ← StrictJson.obj s!"{path}.rhs[0]" rhs[0]!
        let resultTypes ← (match callObj.get? "resultTypes" with
          | some rt => do
              let arr ← StrictJson.array s!"{path}.rhs[0].resultTypes" rt
              arr.mapIdxM (fun i t => decodeTy s!"{path}.rhs[0].resultTypes[{i}]" t)
          | none => pure #[])
        let callee ← decodeExpr s!"{path}.rhs[0].callee" calleeJ
        let argEs ← args.mapIdxM (fun i a => decodeExpr s!"{path}.rhs[0].args[{i}]" a)
        let mut decls : Array Stmt := #[]
        let mut assignees : Array Assignee := #[]
        for i in [:lhs.size] do
          let lj := lhs[i]!
          if targetIsBlank lj then
            let tmp := s!"$cv{i}"
            let ty := resultTypes[i]?.getD .int
            decls := decls.push (.initialization { id := tmp, typ := ty })
            assignees := assignees.push (.var tmp)
          else
            let t ← decodeTarget s!"{path}.lhs[{i}]" lj
            decls := decls ++ (← declaresOf #[t])
            assignees := assignees.push t.assignee
        return .seqn (decls.push (.callValue assignees callee argEs))
    | none => pure ()
  -- Comma-ok map lookup: `v, ok := m[k]`. Blank targets route to fresh temps.
  if lhs.size == 2 && rhs.size == 1 then
    match ← asMapGet? rhs[0]! with
    | some (baseJ, indexJ, keyTyJ, valTyJ) =>
        let base ← decodeExpr s!"{path}.rhs[0].base" baseJ
        let index ← decodeExpr s!"{path}.rhs[0].index" indexJ
        let keyTy ← decodeTy s!"{path}.rhs[0].keyType" keyTyJ
        let valTy ← decodeTy s!"{path}.rhs[0].valueType" valTyJ
        let commaOkTarget (j : Json) (p : String) (ty : Ty) (tmp : String) : LowerM (Assignee × Array Stmt) :=
          if targetIsBlank j then
            pure (.var tmp, #[.initialization { id := tmp, typ := ty }])
          else do
            let t ← decodeTarget p j
            pure (t.assignee, ← declaresOf #[t])
        let (a0, d0) ← commaOkTarget lhs[0]! s!"{path}.lhs[0]" valTy "$mlv"
        let (a1, d1) ← commaOkTarget lhs[1]! s!"{path}.lhs[1]" .bool "$mlok"
        return .seqn (d0 ++ d1 ++ #[.mapLookup a0 a1 base index keyTy valTy])
    | none => pure ()
  if lhs.size != rhs.size then
    fail s!"assignment arity {lhs.size} != {rhs.size} at {path}"
  else if lhs.any targetIsBlank then
    -- Blank targets discard their value but must still evaluate the RHS (so a
    -- panic in `_ = a/b` fires). Round 4 (BUG-035): the old lowering
    -- (RHS temps + per-target single assigns) collapsed spec
    -- §Assignments' phase 1 — a later target's index operands read an
    -- EARLIER store (`i, _, a[i]` saw the post-store `i`). Blanks now
    -- become fresh DISCARD locals (typed from the matching RHS
    -- expression) inside ONE `.assignMany`, so the whole statement
    -- rides the phase-split spine.
    if lhs.size == 1 then
      -- `_ = e`: evaluate for effect into a discard local.
      let ty ← exprTypeOf s!"{path}.rhs[0]" rhs[0]!
      pure (.seqn #[.initialization { id := "$blank0", typ := ty },
        .assign (.var "$blank0") (← decodeExpr s!"{path}.rhs[0]" rhs[0]!)])
    else do
      let mut decls : Array Stmt := #[]
      let mut assignees : Array Assignee := #[]
      let mut i := 0
      for l in lhs do
        if targetIsBlank l then
          let ty ← exprTypeOf s!"{path}.rhs[{i}]" rhs[i]!
          let tmp := s!"$blank{i}"
          decls := decls.push (.initialization { id := tmp, typ := ty })
          assignees := assignees.push (.var tmp)
        else
          let t ← decodeTarget s!"{path}.lhs[{i}]" l
          decls := decls ++ (← declaresOf #[t])
          assignees := assignees.push t.assignee
        i := i + 1
      let exprs ← rhs.mapIdxM (fun i e => decodeExpr s!"{path}.rhs[{i}]" e)
      pure (.seqn (decls.push (.assignMany assignees exprs)))
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

partial def decodeFor (results : Array Param) (path : String) (obj : StrictJson.Obj)
    (label : Option String := none) : LowerM Stmt := do
  let cond ← (match obj.get? "cond" with
    | some c => decodeExpr s!"{path}.cond" c
    | none => pure (.boolLit true))
  let body ← decodeStmt results s!"{path}.body" (← StrictJson.field path obj "body")
  let post ← (match obj.get? "post" with
    | some p => decodeStmt results s!"{path}.post" p
    | none => pure (.seqn #[]))
  -- `condPre`: the condition's hoisted call/alloc temps, re-run before
  -- EVERY test (the test happens inside the loop body, so hoists are
  -- legal here — control-flow slice, docs/2026-08-04_control-flow-design.md).
  let condPre ← (match obj.get? "condPre" with
    | some cp => do
        let arr ← StrictJson.array s!"{path}.condPre" cp
        arr.mapIdxM (fun i s => decodeStmt results s!"{path}.condPre[{i}]" s)
    | none => pure #[])
  -- `continue` must still run the post statement, but GoCore's `while` re-runs
  -- its whole body on continue. So run post at the top of the body except on
  -- the first iteration (guarded by a flag), then re-check the condition; this
  -- makes `for init; cond; post` faithful under continue and break.
  let loopBody := Stmt.block #[] #[
    .ifThenElse (.var "$forFirst")
      (.assign (.var "$forFirst") (.boolLit false))
      post,
    .seqn condPre,
    .ifThenElse cond (.seqn #[]) .breakStmt,
    body
  ]
  -- A label (from a wire "labeled" wrapper) attaches DIRECTLY to the
  -- `.while` — the machine's `contHeadLabel` placement invariant.
  let whileStmt : Stmt :=
    match label with
    | some l => .labeled l (.while (.boolLit true) loopBody)
    | none => .while (.boolLit true) loopBody
  let loop := Stmt.block #[] #[
    .initialization { id := "$forFirst", typ := .bool },
    .assign (.var "$forFirst") (.boolLit true),
    whileStmt
  ]
  match obj.get? "init" with
  | some initE => pure (.block #[] #[← decodeStmt results s!"{path}.init" initE, loop])
  | none => pure loop

end

/-! ## Program -/

private def decodeFieldDef (path : String) (json : Json) : LowerM FieldDef := do
  let obj ← StrictJson.obj path json
  let name ← StrictJson.string s!"{path}.name" (← StrictJson.field path obj "name")
  let typ ← decodeTy s!"{path}.type" (← StrictJson.field path obj "type")
  let embedded ← StrictJson.bool s!"{path}.embedded" (← StrictJson.field path obj "embedded")
  pure { name, typ, embedded }

/-- One interface method REQUIREMENT: name plus the signature types and the
VARIADIC marker, receiver excluded. `variadic` is REQUIRED on the wire — a
missing marker would silently default a variadic requirement to
non-variadic and re-open finding 0's wrong `ok`. -/
private def decodeMethodSig (path : String) (json : Json) : LowerM MethodSig := do
  let obj ← StrictJson.obj path json
  let name ← StrictJson.string s!"{path}.name" (← StrictJson.field path obj "name")
  let paramsJson ← StrictJson.array s!"{path}.params" (← StrictJson.field path obj "params")
  let resultsJson ← StrictJson.array s!"{path}.results" (← StrictJson.field path obj "results")
  let variadic ← StrictJson.bool s!"{path}.variadic" (← StrictJson.field path obj "variadic")
  let params ← paramsJson.mapIdxM (fun i t => decodeTy s!"{path}.params[{i}]" t)
  let results ← resultsJson.mapIdxM (fun i t => decodeTy s!"{path}.results[{i}]" t)
  pure { name, params, results, variadic }

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
  | "defined" =>
      -- Identity-bearing named type over a non-struct underlying
      -- (interfaces campaign S2): resolution stops here for identity
      -- purposes; operations resolve through `target`.
      pure (⟨name⟩, .defined (← decodeTy s!"{path}.def.target" (← StrictJson.field s!"{path}.def" defObj "target")))
  | "interface" =>
      -- An interface DECLARATION: the full method set (embedded interfaces
      -- already flattened by the frontend). Satisfaction requirements come
      -- from here; an interface name with no declaration fails closed.
      let methods ← StrictJson.array s!"{path}.def.methods" (← StrictJson.field s!"{path}.def" defObj "methods")
      pure (⟨name⟩, .interfaceDef (← methods.mapIdxM
        (fun i m => decodeMethodSig s!"{path}.def.methods[{i}]" m)))
  | "unsupported" =>
      -- An EXISTENCE-only marker (imported named types, design note D5):
      -- the type is KNOWN to the wire — its method-set stubs make
      -- satisfaction answerable — while every structural use (defaults,
      -- normalization, conversion) keeps failing closed on the reason.
      let feature ← StrictJson.string s!"{path}.def.feature"
        (← StrictJson.field s!"{path}.def" defObj "feature")
      pure (⟨name⟩, .unsupported feature)
  | other => fail s!"unsupported type definition kind {other} at {path}"

private def decodeFunc (path : String) (json : Json) : LowerM Func := do
  let obj ← StrictJson.obj path json
  let name ← StrictJson.string s!"{path}.name" (← StrictJson.field path obj "name")
  -- A QUARANTINED declaration (per-decl fail-closed, slice 1 of arc
  -- wrong-answers-builtins): the frontend could not lower this function
  -- (e.g. generics, floats), but other declarations in the package can
  -- still run. The stub's params carry `Ty.unsupported`, so a CALL fails
  -- closed with the original reason at bind time (arity preserved); a
  -- nullary call hits the unsupported body. Merely being declared — or
  -- taken as a value — is fine.
  match obj.get? "unsupported" with
  | some r =>
      let reason ← StrictJson.string s!"{path}.unsupported" r
      -- The marker prefix lets the differential runner classify a call
      -- into a stub as the frontend coverage gap it is (stage
      -- frontend-export), keeping the fidelity ledger for machine gaps.
      let reason := s!"frontend-quarantined: {reason}"
      let arity ← StrictJson.nat s!"{path}.arity" (← StrictJson.field path obj "arity")
      let args := (Array.range arity).map
        (fun i => ({ id := s!"$stub{i}", typ := .unsupported reason } : Param))
      pure { id := ⟨name⟩, args, results := #[], body := .unsupported reason }
  | none =>
  let params ← StrictJson.array s!"{path}.params" (← StrictJson.field path obj "params")
  let results ← StrictJson.array s!"{path}.results" (← StrictJson.field path obj "results")
  -- REQUIRED: Go's variadic marker, the half of the signature interface
  -- satisfaction compares (audit finding 0). A wire without it fails
  -- closed rather than defaulting to non-variadic.
  let variadic ← StrictJson.bool s!"{path}.variadic" (← StrictJson.field path obj "variadic")
  let args ← params.mapIdxM (fun i p => decodeParam s!"{path}.params[{i}]" p)
  let res ← results.mapIdxM (fun i p => decodeParam s!"{path}.results[{i}]" p)
  let body ← decodeStmt res s!"{path}.body" (← StrictJson.field path obj "body")
  pure { id := ⟨name⟩, args, results := res, body, variadic }

/-- A method lowers to a receiver-scoped GoCore function (`RecvType.method`,
receiver as the first parameter) plus a `MethodInfo` dispatch-table entry. -/
private def decodeMethod (path : String) (json : Json) : LowerM (Func × MethodInfo) := do
  let obj ← StrictJson.obj path json
  let name ← StrictJson.string s!"{path}.name" (← StrictJson.field path obj "name")
  let recvType ← StrictJson.string s!"{path}.recvType" (← StrictJson.field path obj "recvType")
  let recv ← decodeParam s!"{path}.recv" (← StrictJson.field path obj "recv")
  let params ← StrictJson.array s!"{path}.params" (← StrictJson.field path obj "params")
  let results ← StrictJson.array s!"{path}.results" (← StrictJson.field path obj "results")
  let variadic ← StrictJson.bool s!"{path}.variadic" (← StrictJson.field path obj "variadic")
  let args ← params.mapIdxM (fun i p => decodeParam s!"{path}.params[{i}]" p)
  let res ← results.mapIdxM (fun i p => decodeParam s!"{path}.results[{i}]" p)
  let funcId : FuncId := ⟨s!"{recvType}.{name}"⟩
  let info : MethodInfo := { name, funcId, recv := recv.typ }
  -- Declared schema addition (arc-final audit F1 / BUG-015): the
  -- synthesized-promotion-wrapper marker. Decoded STRICTLY when present
  -- (bool or refuse); absent means a concrete non-wrapper method.
  let wrapper ← match obj.get? "wrapper" with
    | some flag => StrictJson.bool s!"{path}.wrapper" flag
    | none => pure false
  -- A declaration-only STUB (imported named types, design note D5): the
  -- REAL signature — `satisfiesMethodSig` compares it — over a fail-closed
  -- body, so satisfaction answers while a CALL refuses with the reason.
  match obj.get? "unsupported" with
  | some r =>
      let reason ← StrictJson.string s!"{path}.unsupported" r
      pure ({ id := funcId, args := #[recv] ++ args, results := res,
              body := .unsupported s!"frontend-quarantined: {reason}",
              variadic, wrapper }, info)
  | none =>
  -- A present `interface` key is decoded STRICTLY (delta-review R2,
  -- 2026-08-05 — same class as the F7 `runtimeError` fix; this presence-only
  -- match is 2026-07-30 vintage, surfaced by adjacency): bool or refuse;
  -- `false` is well-formed and means a concrete method.
  let ifaceFlag ← match obj.get? "interface" with
    | some flag => StrictJson.bool s!"{path}.interface" flag
    | none => pure false
  if ifaceFlag then
      -- An INTERFACE method: a signature-only dispatch anchor.
      -- `enterFrame` finds this Func, `dynamicDispatch?` redirects on the
      -- receiver box (or raises Go's nil-interface panic); the stub body
      -- is unreachable and fails STUCK (call to a nonexistent function)
      -- if a dispatch bug ever reaches it — never a silent zero return.
      let stub : Stmt := .call #[] ⟨"$interface-method-unreachable"⟩ #[]
      pure ({ id := funcId, args := #[recv] ++ args, results := res, body := stub,
              variadic, wrapper }, info)
  else
      let body ← decodeStmt res s!"{path}.body" (← StrictJson.field path obj "body")
      pure ({ id := funcId, args := #[recv] ++ args, results := res, body,
              variadic, wrapper }, info)

/-- Decode the whole wire program. Runs OUTSIDE `LowerM`: the globals
table decodes FIRST, and its size is the reader context every
body-decoding call runs under — that is what arms the `globaladdr`
bound check (audit response 2026-08-05, C1). -/
partial def decodeProgram (json : Json) : Except String Program := do
  let obj ← StrictJson.obj "program" json
  let schema ← StrictJson.string "program.schema" (← StrictJson.field "program" obj "schema")
  if schema != "golean-native-v1" then
    throw s!"native lowering: unexpected schema {schema}"
  -- Package-level variables (init slice): declaration order; the driver
  -- seeds cell i at `Loc.base ⟨i⟩`. Optional key — a globals-free wire
  -- decodes exactly as before. Duplicate names are impossible in a
  -- type-checked package; refuse anyway (boundary collision-check).
  let globals ←
    match obj.get? "globals" with
    | none => pure #[]
    | some gj => do
        let arr ← StrictJson.array "program.globals" gj
        arr.mapIdxM (fun i g => do
          let gobj ← StrictJson.obj s!"program.globals[{i}]" g
          let name ← StrictJson.string s!"program.globals[{i}].name"
            (← StrictJson.field s!"program.globals[{i}]" gobj "name")
          let typ ← (decodeTy s!"program.globals[{i}].type"
            (← StrictJson.field s!"program.globals[{i}]" gobj "type")).run 0
          pure ({ name, typ } : GlobalDef))
  let mut seenGlobals : Std.HashSet String := {}
  for g in globals do
    if seenGlobals.contains g.name then
      throw s!"native lowering: duplicate global {g.name} in program"
    seenGlobals := seenGlobals.insert g.name
  let ng := globals.size
  let funcsJson ← StrictJson.array "program.funcs" (← StrictJson.field "program" obj "funcs")
  let funcs ← funcsJson.mapIdxM (fun i f => (decodeFunc s!"program.funcs[{i}]" f).run ng)
  let typesJson ← StrictJson.array "program.types" (← StrictJson.field "program" obj "types")
  let declaredDefs ← typesJson.mapIdxM (fun i t => (decodeTypeDef s!"program.types[{i}]" t).run ng)
  -- The canonical empty struct (map[K]struct{} set idiom) is always available.
  let typeDefs := #[(⟨"struct{}"⟩, TypeDef.struct #[])] ++ declaredDefs
  let methodsJson ← StrictJson.array "program.methods" (← StrictJson.field "program" obj "methods")
  let methodPairs ← methodsJson.mapIdxM (fun i m => (decodeMethod s!"program.methods[{i}]" m).run ng)
  -- Method bodies are executable functions (looked up by FuncId on call);
  -- MethodInfo is the dispatch table.
  let allFuncs := funcs ++ methodPairs.map Prod.fst
  -- Collision check at the boundary (CLAUDE.md: every identity constructor
  -- collision-checks). Duplicate FuncIds would make findFunctionIn? silently
  -- run the FIRST body for BOTH callers — the 2026-07-25 pre-merge audit
  -- found exactly that via same-named methods' lifted literals.
  let mut seen : Std.HashSet String := {}
  for f in allFuncs do
    if seen.contains f.id.key then
      throw s!"native lowering: duplicate function id {f.id.key} in program"
    seen := seen.insert f.id.key
  pure { typeDefs, funcs := allFuncs, methods := methodPairs.map Prod.snd, globals }

end GoLean.NativeToIR
