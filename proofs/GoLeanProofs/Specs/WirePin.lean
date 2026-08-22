import Lean
import GoLean.GoCore.Syntax
import GoLean.NativeToIR

/-!
# The wire-pin mechanism — elaboration-time decode of a checked-in
frontend wire (campaign Arc 1, U-c3; design:
`docs/2026-08-22_campaign-arc1-statement-design.md` §3)

Large subjects (the choice-driven raft twin: a 9.3 MB wire — the
whole lowered library) cannot be pinned as source-text Lean literals
the way the gallery pins are (`FibProgram.lean`'s generated-repr
pattern). This module provides `goldenWire%`: a term elaborator that
reads the checked-in wire file at ELABORATION time, runs the very
decoder every machine run uses (`Lean.Json.parse` +
`GoLean.NativeToIR.decodeProgram` — the same fail-closed boundary),
and reflects the decoded `Program` into the environment as a concrete
term via derived `ToExpr` instances.

Trust story (statement-TCB): the def this produces IS a plain
`Program` literal — no meta machinery, no IO, and no decode call
appears in the pinned term or its type; the elaborator is scaffolding
that runs once, and a read or decode failure fails elaboration LOUD
(fail closed — no default, no option). What guards drift: the wire
file is tracked; `scripts/check-golden` guards
frontend(source) ↔ wire bytes (entry added with the pin); and the
term is byte-determined by the wire. This is the `FibProgram`
generated-literal story with the generation moved into elaboration —
"proof subject = decoded(frontend(source))", unchanged.

The `ToExpr` derives below are STANDALONE (GoCore untouched — they
live here, meta-side, outside the semantic core; constitution §4.1's
surgery threshold respected).
-/

namespace GoLean.WirePin


deriving instance Lean.ToExpr for GoLean.GoCore.IntKind
deriving instance Lean.ToExpr for GoLean.GoCore.FloatKind
deriving instance Lean.ToExpr for GoLean.GoCore.ChanDir
deriving instance Lean.ToExpr for GoLean.GoCore.SyncKind
deriving instance Lean.ToExpr for GoLean.GoString
deriving instance Lean.ToExpr for GoLean.TypeId
deriving instance Lean.ToExpr for GoLean.Addr
deriving instance Lean.ToExpr for GoLean.Loc
deriving instance Lean.ToExpr for GoLean.GoCore.Ty
deriving instance Lean.ToExpr for GoLean.GoCore.FuncId
deriving instance Lean.ToExpr for GoLean.GoCore.Param
deriving instance Lean.ToExpr for GoLean.GoCore.FieldDef
deriving instance Lean.ToExpr for GoLean.GoCore.MethodSig
deriving instance Lean.ToExpr for GoLean.GoCore.TypeDef
deriving instance Lean.ToExpr for GoLean.GoCore.Expr
deriving instance Lean.ToExpr for GoLean.GoCore.Assignee
deriving instance Lean.ToExpr for GoLean.GoCore.SelectClauseHead
deriving instance Lean.ToExpr for GoLean.GoCore.SyncStmtOp
deriving instance Lean.ToExpr for GoLean.GoCore.Stmt
deriving instance Lean.ToExpr for GoLean.GoCore.Func
deriving instance Lean.ToExpr for GoLean.GoCore.MethodInfo
deriving instance Lean.ToExpr for GoLean.GoCore.MethodSetCoverage
deriving instance Lean.ToExpr for GoLean.GoCore.MethodSetRecord
deriving instance Lean.ToExpr for GoLean.GoCore.GlobalDef
deriving instance Lean.ToExpr for GoLean.GoCore.Program

/-- `goldenWire% "relative/path.json"` — elaborates to the decoded
`Program` term of the checked-in wire at that path (relative to the
PACKAGE root's parent, i.e. the repo root, so pins read
`baselines/golden/...` like every other golden artifact). Fails
elaboration loudly on a missing file, a JSON parse error, or a
decoder refusal — a pin that cannot decode is a broken build, never
a default value. -/
elab "goldenWire% " path:str : term => do
  let rel := path.getString
  -- The proofs package elaborates with cwd = `proofs/`; golden
  -- artifacts live at the repo root. Try repo-root-relative first,
  -- then cwd-relative (so the elaborator also works if cwd is the
  -- repo root, e.g. under tooling that sets it so).
  let candidates : List System.FilePath := [⟨s!"../{rel}"⟩, ⟨rel⟩]
  let some found ← candidates.findM? (fun p => p.pathExists)
    | throwError "goldenWire%: wire file not found: {rel}"
  let contents ← IO.FS.readFile found
  match Lean.Json.parse contents with
  | .error err => throwError "goldenWire%: {rel}: JSON parse error: {err}"
  | .ok json =>
    match GoLean.NativeToIR.decodeProgram json with
    | .error err => throwError "goldenWire%: {rel}: decoder refused: {err}"
    | .ok program => return Lean.toExpr program

end GoLean.WirePin
