import GoLean.GoCore.Syntax

/-!
# The golden-lowered program pin (extracted at reshape S4, 2026-07-23)

`sliceLowered` is the native frontend's ACTUAL lowering of the slice source
(`Corpus/coverage/exec/pointers/inc-via-call/main.go`), checked in as a
Lean literal and pinned by `scripts/check-golden` (fresh frontend+decode
reproduces `baselines/golden/slice-lowered.repr`, and this term prints the
same repr — "proof subject = decoded(frontend(source))", fail closed).

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
    methods := #[] }

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
