import GoLean.GoCore.Syntax

/-!
# C-05 `callchain` — the frontend's lowering, pinned (G-BIND gate
instance, docs/2026-08-28_iris-corpus-plan.md §5.2)

`callchainLowered` is the native frontend's ACTUAL lowering of the
canonical corpus source
(`Corpus/coverage/exec/functions/callchain/main.go`, 3/3
differentially green against `go run`), pinned by
`scripts/check-golden` against
`baselines/golden/callchain-lowered.repr`. THIS DEF IS GENERATED from
that repr (the literal below IS the repr text, byte-identical under
`repr` — the same both-links story as the golden pins); regenerate
rather than hand-edit.

Pure syntax module: no Iris import, safe for statement-side use.
-/

namespace GoLean.Iris.Callchain

open GoLean GoLean.GoCore

/-- The frontend's lowering of the C-05 subject, verbatim
(`scripts/check-golden` pins it). -/
def callchainLowered : Program :=
  { typeDefs := #[({ key := "struct{}" }, GoLean.GoCore.TypeDef.struct #[])],
    funcs := #[{ id := { key := "ccDouble" },
                 args := #[{ id := "dst",
                             typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) },
                           { id := "x", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
                 results := #[],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr (GoLean.GoCore.Expr.var "dst"))
                                   (GoLean.GoCore.Expr.add (GoLean.GoCore.Expr.var "x") (GoLean.GoCore.Expr.var "x"))]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "ccBump" },
                 args := #[{ id := "dst",
                             typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) }],
                 results := #[],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr (GoLean.GoCore.Expr.var "dst"))
                                   (GoLean.GoCore.Expr.add
                                     (GoLean.GoCore.Expr.deref
                                       (GoLean.GoCore.Expr.var "dst")
                                       (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)))
                                     (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "ccWork" },
                 args := #[{ id := "dst",
                             typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) },
                           { id := "x", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
                 results := #[],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.deferCall
                               (GoLean.GoCore.Expr.funcVal { key := "ccBump" } #[])
                               #[GoLean.GoCore.Expr.var "dst"],
                             GoLean.GoCore.Stmt.call
                               #[]
                               { key := "ccDouble" }
                               #[GoLean.GoCore.Expr.var "dst", GoLean.GoCore.Expr.var "x"]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "ccCaller" },
                 args := #[{ id := "x", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "y", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "y")
                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
                             GoLean.GoCore.Stmt.call
                               #[]
                               { key := "ccWork" }
                               #[GoLean.GoCore.Expr.ref "y", GoLean.GoCore.Expr.var "x"],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.add
                                     (GoLean.GoCore.Expr.var "y")
                                     (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false }],
    methods := #[],
    globals := #[],
    methodSets := #[{ key := "struct{}", coverage := GoLean.GoCore.MethodSetCoverage.full }] }

end GoLean.Iris.Callchain
