import GoLean.GoCore.Syntax

/-!
# The fib example — the frontend's lowering, pinned (verified-examples
arc slice 1, 2026-08-12)

`fibLowered` is the native frontend's ACTUAL lowering of the canonical
corpus source (`Corpus/coverage/exec/examples/fib/main.go`, 6/6
differentially green against `go run`, including the n=94 mod-2^64
wrap row), pinned by `scripts/check-golden` against
`baselines/golden/fib-lowered.repr`. THIS DEF IS GENERATED from that
repr (the literal below IS the repr text, byte-identical under `repr`
— the same both-links story as the golden pins); regenerate rather
than hand-edit.

Pure syntax module: no Iris import, safe for statement-side use.
-/

namespace GoLean.Examples.Fib

open GoLean GoLean.GoCore

/-- The frontend's lowering of the fib subject, verbatim
(`scripts/check-golden` pins it). -/
def fibLowered : Program :=
  { typeDefs := #[({ key := "struct{}" }, GoLean.GoCore.TypeDef.struct #[])],
    funcs := #[{ id := { key := "fib" },
                 args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "a", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "a")
                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64)),
                                 GoLean.GoCore.Stmt.initialization
                                   { id := "b", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "b")
                                   (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64))],
                             GoLean.GoCore.Stmt.block
                               #[]
                               #[GoLean.GoCore.Stmt.seqn
                                   #[GoLean.GoCore.Stmt.initialization
                                       { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                     GoLean.GoCore.Stmt.assign
                                       (GoLean.GoCore.Assignee.var "i")
                                       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))],
                                 GoLean.GoCore.Stmt.block
                                   #[]
                                   #[GoLean.GoCore.Stmt.initialization
                                       { id := "$forFirst", typ := GoLean.GoCore.Ty.bool },
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
                                             (GoLean.GoCore.Stmt.assign
                                               (GoLean.GoCore.Assignee.var "i")
                                               (GoLean.GoCore.Expr.add
                                                 (GoLean.GoCore.Expr.var "i")
                                                 (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)))),
                                           GoLean.GoCore.Stmt.seqn #[],
                                           GoLean.GoCore.Stmt.ifThenElse
                                             (GoLean.GoCore.Expr.lessCmp
                                               (GoLean.GoCore.Expr.var "i")
                                               (GoLean.GoCore.Expr.var "n"))
                                             (GoLean.GoCore.Stmt.seqn #[])
                                             (GoLean.GoCore.Stmt.breakStmt),
                                           GoLean.GoCore.Stmt.block
                                             #[]
                                             #[GoLean.GoCore.Stmt.seqn
                                                 #[GoLean.GoCore.Stmt.assignMany
                                                     #[GoLean.GoCore.Assignee.var "a", GoLean.GoCore.Assignee.var "b"]
                                                     #[GoLean.GoCore.Expr.var "b",
                                                       GoLean.GoCore.Expr.add
                                                         (GoLean.GoCore.Expr.var "a")
                                                         (GoLean.GoCore.Expr.var "b")]]]])]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "a"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "fib_harness" },
                 args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "r", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "r"]
                                   { key := "fib" }
                                   #[GoLean.GoCore.Expr.var "n"]],
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

end GoLean.Examples.Fib
