import GoLean.GoCore.Syntax

/-!
# The `stein` example — the frontend's lowering, pinned
(gallery campaign G1, guardrails wave, 2026-08-15)

`steinLowered` is the native frontend's ACTUAL lowering of the
canonical corpus source (`Corpus/coverage/exec/examples/stein/main.go`,
differentially green against `go run`), pinned by `scripts/check-golden`
against `baselines/golden/stein-lowered.repr`. THIS DEF IS GENERATED from
that repr (the literal below IS the repr text, byte-identical under
`repr` — the same both-links story as the other golden pins);
regenerate rather than hand-edit.

Pure syntax module: no Iris import, safe for statement-side use.
-/

namespace GoLean.Examples.Stein

open GoLean GoLean.GoCore

/-- The frontend's lowering of the `stein` subject, verbatim
(`scripts/check-golden` pins it). -/
def steinLowered : Program :=
  { typeDefs := #[({ key := "struct{}" }, GoLean.GoCore.TypeDef.struct #[])],
    funcs := #[{ id := { key := "isEven" },
                 args := #[{ id := "x", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.bool }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.eqCmp
                                     (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                     (GoLean.GoCore.Expr.mod
                                       (GoLean.GoCore.Expr.var "x")
                                       (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint64)))
                                     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "steinGCD" },
                 args := #[{ id := "$stub0",
                             typ := GoLean.GoCore.Ty.unsupported
                                      "frontend-quarantined: call/allocation in short-circuit operand (would change evaluation order)" },
                           { id := "$stub1",
                             typ := GoLean.GoCore.Ty.unsupported
                                      "frontend-quarantined: call/allocation in short-circuit operand (would change evaluation order)" }],
                 results := #[],
                 body := GoLean.GoCore.Stmt.unsupported
                           "frontend-quarantined: call/allocation in short-circuit operand (would change evaluation order)",
                 variadic := false,
                 wrapper := false },
               { id := { key := "stein_harness" },
                 args := #[{ id := "a", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "b", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "r", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "r"]
                                   { key := "steinGCD" }
                                   #[GoLean.GoCore.Expr.var "a", GoLean.GoCore.Expr.var "b"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "r"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false }],
    methods := #[],
    globals := #[],
    methodSets := #[{ key := "struct{}", coverage := GoLean.GoCore.MethodSetCoverage.full }] }

end GoLean.Examples.Stein
