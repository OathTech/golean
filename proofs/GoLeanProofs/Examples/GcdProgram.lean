import GoLean.GoCore.Syntax

/-!
# The gcd example — the frontend's lowering, pinned
(verified-examples arc slice 2c, 2026-08-13)

`gcdLowered` is the native frontend's ACTUAL lowering of the
canonical corpus source (`Corpus/coverage/exec/examples/gcd/main.go`,
differentially green against `go run`), pinned by
`scripts/check-golden` against `baselines/golden/gcd-lowered.repr`.
THIS DEF IS GENERATED from that repr (the literal below IS the repr
text, byte-identical under `repr` — the same both-links story as the
golden pins); regenerate rather than hand-edit.

Pure syntax module: no Iris import, safe for statement-side use.
-/

namespace GoLean.Examples.Gcd

open GoLean GoLean.GoCore

/-- The frontend's lowering of the gcd subject, verbatim
(`scripts/check-golden` pins it). -/
def gcdLowered : Program :=
  { typeDefs := #[({ key := "struct{}" }, GoLean.GoCore.TypeDef.struct #[])],
    funcs := #[{ id := { key := "gcd" },
                 args := #[{ id := "a", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "b", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.block
                               #[]
                               #[GoLean.GoCore.Stmt.initialization { id := "$forFirst", typ := GoLean.GoCore.Ty.bool },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$forFirst")
                                   (GoLean.GoCore.Expr.boolLit true),
                                 GoLean.GoCore.Stmt.while
                                   (GoLean.GoCore.Expr.boolLit true)
                                   (GoLean.GoCore.Stmt.block
                                     #[]
                                     #[GoLean.GoCore.Stmt.ifThenElse
                                         (GoLean.GoCore.Expr.var "$forFirst")
                                         (GoLean.GoCore.Stmt.assign
                                           (GoLean.GoCore.Assignee.var "$forFirst")
                                           (GoLean.GoCore.Expr.boolLit false))
                                         (GoLean.GoCore.Stmt.seqn #[]),
                                       GoLean.GoCore.Stmt.seqn #[],
                                       GoLean.GoCore.Stmt.ifThenElse
                                         (GoLean.GoCore.Expr.neqCmp
                                           (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                           (GoLean.GoCore.Expr.var "b")
                                           (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64)))
                                         (GoLean.GoCore.Stmt.seqn #[])
                                         (GoLean.GoCore.Stmt.breakStmt),
                                       GoLean.GoCore.Stmt.block
                                         #[]
                                         #[GoLean.GoCore.Stmt.seqn
                                             #[GoLean.GoCore.Stmt.assignMany
                                                 #[GoLean.GoCore.Assignee.var "a", GoLean.GoCore.Assignee.var "b"]
                                                 #[GoLean.GoCore.Expr.var "b",
                                                   GoLean.GoCore.Expr.mod
                                                     (GoLean.GoCore.Expr.var "a")
                                                     (GoLean.GoCore.Expr.var "b")]]]])],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "a"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false }],
    methods := #[],
    globals := #[],
    methodSets := #[{ key := "struct{}", coverage := GoLean.GoCore.MethodSetCoverage.full }] }

end GoLean.Examples.Gcd
