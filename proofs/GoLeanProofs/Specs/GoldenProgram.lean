import GoLean.GoCore.Syntax

/-!
# The golden-lowered program pins (extracted at reshape S4, 2026-07-23;
second program added in the proof-corpus catch-up arc, 2026-07-30)

`sliceLowered` is the native frontend's ACTUAL lowering of the slice source
(`Corpus/coverage/exec/pointers/inc-via-call/main.go`), checked in as a
Lean literal and pinned by `scripts/check-golden` (fresh frontend+decode
reproduces `baselines/golden/slice-lowered.repr`, and this term prints the
same repr — "proof subject = decoded(frontend(source))", fail closed).
`GoldenRecover.recoverLowered` is the same pin for the recover-direct
source (`Corpus/coverage/exec/panic-recover/recover-direct/main.go`,
baseline `baselines/golden/recover-lowered.repr`) — the defer/panic/
recover composition subject.

Extracted from `Specs/GoldenSlice.lean` so the pin is pure syntax with no
dependency on the semantics modules: the staleness guard stays LIVE while
the proof layer is pruned for the R3 rebuild, and stays honest afterwards
(a program pin should never have needed the relation). The namespace is
kept (`GoLean.Iris.GoldenSlice`) so every existing reference — including
`check-golden`'s term print — is unchanged; at R3, `GoldenSlice.lean`
imports this module instead of carrying its own copy.
-/

namespace GoLean.Iris.GoldenSlice

open GoLean GoLean.GoCore

/-- The frontend's lowering of the slice source, verbatim
(`scripts/check-golden` pins it). -/
def sliceLowered : Program :=
  { typeDefs := #[({ key := "struct{}" }, GoLean.GoCore.TypeDef.struct #[])],
    funcs := #[{ id := { key := "inc" },
                 args := #[{ id := "p",
                             typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) }],
                 results := #[],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr (GoLean.GoCore.Expr.var "p"))
                                   (GoLean.GoCore.Expr.add
                                     (GoLean.GoCore.Expr.deref
                                       (GoLean.GoCore.Expr.var "p")
                                       (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)))
                                     (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))]] },
               { id := { key := "incViaCall" },
                 args := #[],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "x", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "x")
                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
                             GoLean.GoCore.Stmt.call #[] { key := "inc" } #[GoLean.GoCore.Expr.ref "x"],
                             GoLean.GoCore.Stmt.call #[] { key := "inc" } #[GoLean.GoCore.Expr.ref "x"],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "x"),
                                 GoLean.GoCore.Stmt.returnStmt]] }],
    methods := #[],
    methodSets := #[{ key := "struct{}", coverage := GoLean.GoCore.MethodSetCoverage.full }] }

/-- The golden `inc` function as a named literal; `sliceLowered_funcs_eq`
kernel-checks the pair against the pinned lowering. -/
def incFunc : Func :=
  { id := ⟨"inc"⟩,
    args := #[⟨"p", .pointer (.int .int)⟩],
    results := #[],
    body := .block #[] #[.seqn #[.assign (.addr (.var "p"))
      (.add (.deref (.var "p") (.int .int)) (.intLit 1 .int))]] }

/-- The golden `incViaCall` function as a named literal (same bridge). -/
def incViaCallFunc : Func :=
  { id := ⟨"incViaCall"⟩,
    args := #[],
    results := #[⟨"$res0", .int .int⟩],
    body := .block #[] #[
      .seqn #[.initialization ⟨"x", .int .int⟩,
              .assign (.var "x") (.intLit 0 .int)],
      .call #[] ⟨"inc"⟩ #[.ref "x"],
      .call #[] ⟨"inc"⟩ #[.ref "x"],
      .seqn #[.assign (.var "$res0") (.var "x"), .returnStmt]] }

/-- Kernel bridge: the named literals ARE the pinned lowering's functions. -/
theorem sliceLowered_funcs_eq :
    sliceLowered.funcs = #[incFunc, incViaCallFunc] := rfl

end GoLean.Iris.GoldenSlice

namespace GoLean.Iris.GoldenRecover

open GoLean GoLean.GoCore

/-- The second pinned program (proof-corpus catch-up arc, 2026-07-30):
the native frontend's ACTUAL lowering of
`Corpus/coverage/exec/panic-recover/recover-direct/main.go`, pinned by
`scripts/check-golden` against `baselines/golden/recover-lowered.repr`.
The deferred closure is lambda-lifted (`recoverDirect$lit0`, the named
result captured by pointer), recover's value routed through the `$c0`
temporary — the composition subject for the recover `GoFuncSpec`. -/
def recoverLowered : Program :=
  { typeDefs := #[({ key := "struct{}" }, GoLean.GoCore.TypeDef.struct #[])],
    funcs := #[{ id := { key := "recoverDirect$lit0" },
                 args := #[{ id := "result$cap",
                             typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) }],
                 results := #[],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c0", typ := GoLean.GoCore.Ty.interface { key := "any" } },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$c0")
                                   (GoLean.GoCore.Expr.recoverCall)],
                             GoLean.GoCore.Stmt.ifThenElse
                               (GoLean.GoCore.Expr.neqCmp
                                 (GoLean.GoCore.Ty.interface { key := "any" })
                                 (GoLean.GoCore.Expr.var "$c0")
                                 (GoLean.GoCore.Expr.nil none))
                               (GoLean.GoCore.Stmt.block
                                 #[]
                                 #[GoLean.GoCore.Stmt.seqn
                                     #[GoLean.GoCore.Stmt.assign
                                         (GoLean.GoCore.Assignee.addr (GoLean.GoCore.Expr.var "result$cap"))
                                         (GoLean.GoCore.Expr.intLit 7 (GoLean.GoCore.IntKind.int))]])
                               (GoLean.GoCore.Stmt.seqn #[])] },
               { id := { key := "recoverDirect" },
                 args := #[],
                 results := #[{ id := "result", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.deferCall
                               (GoLean.GoCore.Expr.funcVal
                                 { key := "recoverDirect$lit0" }
                                 #[GoLean.GoCore.Expr.ref "result"])
                               #[],
                             GoLean.GoCore.Stmt.panicStmt
                               (GoLean.GoCore.Expr.toInterface
                                 (GoLean.GoCore.Ty.interface { key := "any" })
                                 (GoLean.GoCore.Ty.string)
                                 (GoLean.GoCore.Expr.stringLit
                                   { bytes := #[98, 111, 111, 109, 45, 100, 105, 114, 101, 99, 116] }))] }],
    methods := #[],
    methodSets := #[{ key := "struct{}", coverage := GoLean.GoCore.MethodSetCoverage.full }] }

/-- The lambda-lifted deferred closure as a named literal (bridge below). -/
def litFunc : Func :=
  { id := ⟨"recoverDirect$lit0"⟩,
    args := #[⟨"result$cap", .pointer (.int .int)⟩],
    results := #[],
    body := .block #[] #[
      .seqn #[.initialization ⟨"$c0", .interface ⟨"any"⟩⟩,
              .assign (.var "$c0") .recoverCall],
      .ifThenElse (.neqCmp (.interface ⟨"any"⟩) (.var "$c0") (.nil none))
        (.block #[] #[.seqn #[.assign (.addr (.var "result$cap"))
          (.intLit 7 .int)]])
        (.seqn #[])] }

/-- The golden `recoverDirect` as a named literal (same bridge). -/
def recoverDirectFunc : Func :=
  { id := ⟨"recoverDirect"⟩,
    args := #[],
    results := #[⟨"result", .int .int⟩],
    body := .block #[] #[
      .deferCall (.funcVal ⟨"recoverDirect$lit0"⟩ #[.ref "result"]) #[],
      .panicStmt (.toInterface (.interface ⟨"any"⟩) .string
        (.stringLit ⟨#[98, 111, 111, 109, 45, 100, 105, 114, 101, 99, 116]⟩))] }

/-- Kernel bridge: the named literals ARE the pinned lowering's functions. -/
theorem recoverLowered_funcs_eq :
    recoverLowered.funcs = #[litFunc, recoverDirectFunc] := rfl

end GoLean.Iris.GoldenRecover
