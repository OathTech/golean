import GoLean.GoCore.Syntax

/-!
# The `powmod` example — the frontend's lowering, pinned
(gallery campaign G1, guardrails wave, 2026-08-15)

`powmodLowered` is the native frontend's ACTUAL lowering of the
canonical corpus source (`Corpus/coverage/exec/examples/powmod/main.go`,
differentially green against `go run`), pinned by `scripts/check-golden`
against `baselines/golden/powmod-lowered.repr`. THIS DEF IS GENERATED from
that repr (the literal below IS the repr text, byte-identical under
`repr` — the same both-links story as the other golden pins);
regenerate rather than hand-edit.

Pure syntax module: no Iris import, safe for statement-side use.
-/

namespace GoLean.Examples.PowMod

open GoLean GoLean.GoCore

/-- The frontend's lowering of the `powmod` subject, verbatim
(`scripts/check-golden` pins it). -/
def powmodLowered : Program :=
  { typeDefs := #[({ key := "struct{}" }, GoLean.GoCore.TypeDef.struct #[])],
    funcs := #[{ id := { key := "powMod" },
                 args := #[{ id := "base", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "exp", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "mod", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.ifThenElse
                               (GoLean.GoCore.Expr.eqCmp
                                 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                 (GoLean.GoCore.Expr.var "mod")
                                 (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64)))
                               (GoLean.GoCore.Stmt.block
                                 #[]
                                 #[GoLean.GoCore.Stmt.seqn
                                     #[GoLean.GoCore.Stmt.assign
                                         (GoLean.GoCore.Assignee.var "$res0")
                                         (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64)),
                                       GoLean.GoCore.Stmt.returnStmt]])
                               (GoLean.GoCore.Stmt.seqn #[]),
                             GoLean.GoCore.Stmt.ifThenElse
                               (GoLean.GoCore.Expr.eqCmp
                                 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                 (GoLean.GoCore.Expr.var "mod")
                                 (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)))
                               (GoLean.GoCore.Stmt.block
                                 #[]
                                 #[GoLean.GoCore.Stmt.seqn
                                     #[GoLean.GoCore.Stmt.assign
                                         (GoLean.GoCore.Assignee.var "$res0")
                                         (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64)),
                                       GoLean.GoCore.Stmt.returnStmt]])
                               (GoLean.GoCore.Stmt.seqn #[]),
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "result", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "result")
                                   (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64))],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "base")
                                   (GoLean.GoCore.Expr.mod
                                     (GoLean.GoCore.Expr.var "base")
                                     (GoLean.GoCore.Expr.var "mod"))],
                             GoLean.GoCore.Stmt.block
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
                                         (GoLean.GoCore.Expr.greaterCmp
                                           (GoLean.GoCore.Expr.var "exp")
                                           (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64)))
                                         (GoLean.GoCore.Stmt.seqn #[])
                                         (GoLean.GoCore.Stmt.breakStmt),
                                       GoLean.GoCore.Stmt.block
                                         #[]
                                         #[GoLean.GoCore.Stmt.ifThenElse
                                             (GoLean.GoCore.Expr.eqCmp
                                               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                               (GoLean.GoCore.Expr.mod
                                                 (GoLean.GoCore.Expr.var "exp")
                                                 (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint64)))
                                               (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)))
                                             (GoLean.GoCore.Stmt.block
                                               #[]
                                               #[GoLean.GoCore.Stmt.seqn
                                                   #[GoLean.GoCore.Stmt.assign
                                                       (GoLean.GoCore.Assignee.var "result")
                                                       (GoLean.GoCore.Expr.mod
                                                         (GoLean.GoCore.Expr.mul
                                                           (GoLean.GoCore.Expr.var "result")
                                                           (GoLean.GoCore.Expr.var "base"))
                                                         (GoLean.GoCore.Expr.var "mod"))]])
                                             (GoLean.GoCore.Stmt.seqn #[]),
                                           GoLean.GoCore.Stmt.seqn
                                             #[GoLean.GoCore.Stmt.assign
                                                 (GoLean.GoCore.Assignee.var "base")
                                                 (GoLean.GoCore.Expr.mod
                                                   (GoLean.GoCore.Expr.mul
                                                     (GoLean.GoCore.Expr.var "base")
                                                     (GoLean.GoCore.Expr.var "base"))
                                                   (GoLean.GoCore.Expr.var "mod"))],
                                           GoLean.GoCore.Stmt.seqn
                                             #[GoLean.GoCore.Stmt.assign
                                                 (GoLean.GoCore.Assignee.var "exp")
                                                 (GoLean.GoCore.Expr.div
                                                   (GoLean.GoCore.Expr.var "exp")
                                                   (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint64)))]]])],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "result"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "powTwo" },
                 args := #[{ id := "exp", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c0"]
                                   { key := "powMod" }
                                   #[GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint64),
                                     GoLean.GoCore.Expr.var "exp",
                                     GoLean.GoCore.Expr.intLit 1000000007 (GoLean.GoCore.IntKind.uint64)]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "$c0"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "powmod_harness" },
                 args := #[{ id := "base", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "exp", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "mod", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "r", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "r"]
                                   { key := "powMod" }
                                   #[GoLean.GoCore.Expr.var "base", GoLean.GoCore.Expr.var "exp",
                                     GoLean.GoCore.Expr.var "mod"]],
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

end GoLean.Examples.PowMod
