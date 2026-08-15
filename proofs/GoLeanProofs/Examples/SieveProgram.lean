import GoLean.GoCore.Syntax

/-!
# The `sieve` example — the frontend's lowering, pinned
(gallery campaign G1, guardrails wave, 2026-08-15)

`sieveLowered` is the native frontend's ACTUAL lowering of the
canonical corpus source (`Corpus/coverage/exec/examples/sieve/main.go`,
differentially green against `go run`), pinned by `scripts/check-golden`
against `baselines/golden/sieve-lowered.repr`. THIS DEF IS GENERATED from
that repr (the literal below IS the repr text, byte-identical under
`repr` — the same both-links story as the other golden pins);
regenerate rather than hand-edit.

Pure syntax module: no Iris import, safe for statement-side use.
-/

namespace GoLean.Examples.Sieve

open GoLean GoLean.GoCore

/-- The frontend's lowering of the `sieve` subject, verbatim
(`scripts/check-golden` pins it). -/
def sieveLowered : Program :=
  { typeDefs := #[({ key := "struct{}" }, GoLean.GoCore.TypeDef.struct #[])],
    funcs := #[{ id := { key := "countPrimes" },
                 args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.ifThenElse
                               (GoLean.GoCore.Expr.lessCmp
                                 (GoLean.GoCore.Expr.var "n")
                                 (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint64)))
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
                                   { id := "$c0", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool) },
                                 GoLean.GoCore.Stmt.makeSlice
                                   (GoLean.GoCore.Assignee.var "$c0")
                                   (GoLean.GoCore.Ty.bool)
                                   (GoLean.GoCore.Expr.add
                                     (GoLean.GoCore.Expr.var "n")
                                     (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)))
                                   none],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "composite", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "composite")
                                   (GoLean.GoCore.Expr.var "$c0")],
                             GoLean.GoCore.Stmt.block
                               #[]
                               #[GoLean.GoCore.Stmt.seqn
                                   #[GoLean.GoCore.Stmt.initialization
                                       { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                     GoLean.GoCore.Stmt.assign
                                       (GoLean.GoCore.Assignee.var "i")
                                       (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint64))],
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
                                             (GoLean.GoCore.Expr.atMostCmp
                                               (GoLean.GoCore.Expr.mul
                                                 (GoLean.GoCore.Expr.var "i")
                                                 (GoLean.GoCore.Expr.var "i"))
                                               (GoLean.GoCore.Expr.var "n"))
                                             (GoLean.GoCore.Stmt.seqn #[])
                                             (GoLean.GoCore.Stmt.breakStmt),
                                           GoLean.GoCore.Stmt.block
                                             #[]
                                             #[GoLean.GoCore.Stmt.ifThenElse
                                                 (GoLean.GoCore.Expr.not
                                                   (GoLean.GoCore.Expr.indexGet
                                                     (GoLean.GoCore.Expr.var "composite")
                                                     (GoLean.GoCore.Expr.var "i")))
                                                 (GoLean.GoCore.Stmt.block
                                                   #[]
                                                   #[GoLean.GoCore.Stmt.block
                                                       #[]
                                                       #[GoLean.GoCore.Stmt.seqn
                                                           #[GoLean.GoCore.Stmt.initialization
                                                               { id := "j",
                                                                 typ := GoLean.GoCore.Ty.int
                                                                          (GoLean.GoCore.IntKind.uint64) },
                                                             GoLean.GoCore.Stmt.assign
                                                               (GoLean.GoCore.Assignee.var "j")
                                                               (GoLean.GoCore.Expr.mul
                                                                 (GoLean.GoCore.Expr.var "i")
                                                                 (GoLean.GoCore.Expr.var "i"))],
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
                                                                       (GoLean.GoCore.Assignee.var "j")
                                                                       (GoLean.GoCore.Expr.add
                                                                         (GoLean.GoCore.Expr.var "j")
                                                                         (GoLean.GoCore.Expr.var "i"))),
                                                                   GoLean.GoCore.Stmt.seqn #[],
                                                                   GoLean.GoCore.Stmt.ifThenElse
                                                                     (GoLean.GoCore.Expr.atMostCmp
                                                                       (GoLean.GoCore.Expr.var "j")
                                                                       (GoLean.GoCore.Expr.var "n"))
                                                                     (GoLean.GoCore.Stmt.seqn #[])
                                                                     (GoLean.GoCore.Stmt.breakStmt),
                                                                   GoLean.GoCore.Stmt.block
                                                                     #[]
                                                                     #[GoLean.GoCore.Stmt.seqn
                                                                         #[GoLean.GoCore.Stmt.assign
                                                                             (GoLean.GoCore.Assignee.addr
                                                                               (GoLean.GoCore.Expr.indexAddr
                                                                                 (GoLean.GoCore.Expr.var "composite")
                                                                                 (GoLean.GoCore.Expr.var "j")))
                                                                             (GoLean.GoCore.Expr.boolLit true)]]])]]])
                                                 (GoLean.GoCore.Stmt.seqn #[])]])]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "count", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "count")
                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))],
                             GoLean.GoCore.Stmt.block
                               #[]
                               #[GoLean.GoCore.Stmt.seqn
                                   #[GoLean.GoCore.Stmt.initialization
                                       { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                     GoLean.GoCore.Stmt.assign
                                       (GoLean.GoCore.Assignee.var "i")
                                       (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint64))],
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
                                             (GoLean.GoCore.Expr.atMostCmp
                                               (GoLean.GoCore.Expr.var "i")
                                               (GoLean.GoCore.Expr.var "n"))
                                             (GoLean.GoCore.Stmt.seqn #[])
                                             (GoLean.GoCore.Stmt.breakStmt),
                                           GoLean.GoCore.Stmt.block
                                             #[]
                                             #[GoLean.GoCore.Stmt.ifThenElse
                                                 (GoLean.GoCore.Expr.not
                                                   (GoLean.GoCore.Expr.indexGet
                                                     (GoLean.GoCore.Expr.var "composite")
                                                     (GoLean.GoCore.Expr.var "i")))
                                                 (GoLean.GoCore.Stmt.block
                                                   #[]
                                                   #[GoLean.GoCore.Stmt.assign
                                                       (GoLean.GoCore.Assignee.var "count")
                                                       (GoLean.GoCore.Expr.add
                                                         (GoLean.GoCore.Expr.var "count")
                                                         (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)))])
                                                 (GoLean.GoCore.Stmt.seqn #[])]])]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "count"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "isPrimeSieved" },
                 args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "q", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.ifThenElse
                               (GoLean.GoCore.Expr.greaterCmp (GoLean.GoCore.Expr.var "q") (GoLean.GoCore.Expr.var "n"))
                               (GoLean.GoCore.Stmt.block
                                 #[]
                                 #[GoLean.GoCore.Stmt.seqn
                                     #[GoLean.GoCore.Stmt.assign
                                         (GoLean.GoCore.Assignee.var "$res0")
                                         (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64)),
                                       GoLean.GoCore.Stmt.returnStmt]])
                               (GoLean.GoCore.Stmt.seqn #[]),
                             GoLean.GoCore.Stmt.ifThenElse
                               (GoLean.GoCore.Expr.lessCmp
                                 (GoLean.GoCore.Expr.var "q")
                                 (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint64)))
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
                                   { id := "$c1", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool) },
                                 GoLean.GoCore.Stmt.makeSlice
                                   (GoLean.GoCore.Assignee.var "$c1")
                                   (GoLean.GoCore.Ty.bool)
                                   (GoLean.GoCore.Expr.add
                                     (GoLean.GoCore.Expr.var "n")
                                     (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)))
                                   none],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "composite", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "composite")
                                   (GoLean.GoCore.Expr.var "$c1")],
                             GoLean.GoCore.Stmt.block
                               #[]
                               #[GoLean.GoCore.Stmt.seqn
                                   #[GoLean.GoCore.Stmt.initialization
                                       { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                     GoLean.GoCore.Stmt.assign
                                       (GoLean.GoCore.Assignee.var "i")
                                       (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint64))],
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
                                             (GoLean.GoCore.Expr.atMostCmp
                                               (GoLean.GoCore.Expr.mul
                                                 (GoLean.GoCore.Expr.var "i")
                                                 (GoLean.GoCore.Expr.var "i"))
                                               (GoLean.GoCore.Expr.var "n"))
                                             (GoLean.GoCore.Stmt.seqn #[])
                                             (GoLean.GoCore.Stmt.breakStmt),
                                           GoLean.GoCore.Stmt.block
                                             #[]
                                             #[GoLean.GoCore.Stmt.ifThenElse
                                                 (GoLean.GoCore.Expr.not
                                                   (GoLean.GoCore.Expr.indexGet
                                                     (GoLean.GoCore.Expr.var "composite")
                                                     (GoLean.GoCore.Expr.var "i")))
                                                 (GoLean.GoCore.Stmt.block
                                                   #[]
                                                   #[GoLean.GoCore.Stmt.block
                                                       #[]
                                                       #[GoLean.GoCore.Stmt.seqn
                                                           #[GoLean.GoCore.Stmt.initialization
                                                               { id := "j",
                                                                 typ := GoLean.GoCore.Ty.int
                                                                          (GoLean.GoCore.IntKind.uint64) },
                                                             GoLean.GoCore.Stmt.assign
                                                               (GoLean.GoCore.Assignee.var "j")
                                                               (GoLean.GoCore.Expr.mul
                                                                 (GoLean.GoCore.Expr.var "i")
                                                                 (GoLean.GoCore.Expr.var "i"))],
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
                                                                       (GoLean.GoCore.Assignee.var "j")
                                                                       (GoLean.GoCore.Expr.add
                                                                         (GoLean.GoCore.Expr.var "j")
                                                                         (GoLean.GoCore.Expr.var "i"))),
                                                                   GoLean.GoCore.Stmt.seqn #[],
                                                                   GoLean.GoCore.Stmt.ifThenElse
                                                                     (GoLean.GoCore.Expr.atMostCmp
                                                                       (GoLean.GoCore.Expr.var "j")
                                                                       (GoLean.GoCore.Expr.var "n"))
                                                                     (GoLean.GoCore.Stmt.seqn #[])
                                                                     (GoLean.GoCore.Stmt.breakStmt),
                                                                   GoLean.GoCore.Stmt.block
                                                                     #[]
                                                                     #[GoLean.GoCore.Stmt.seqn
                                                                         #[GoLean.GoCore.Stmt.assign
                                                                             (GoLean.GoCore.Assignee.addr
                                                                               (GoLean.GoCore.Expr.indexAddr
                                                                                 (GoLean.GoCore.Expr.var "composite")
                                                                                 (GoLean.GoCore.Expr.var "j")))
                                                                             (GoLean.GoCore.Expr.boolLit true)]]])]]])
                                                 (GoLean.GoCore.Stmt.seqn #[])]])]],
                             GoLean.GoCore.Stmt.ifThenElse
                               (GoLean.GoCore.Expr.indexGet
                                 (GoLean.GoCore.Expr.var "composite")
                                 (GoLean.GoCore.Expr.var "q"))
                               (GoLean.GoCore.Stmt.block
                                 #[]
                                 #[GoLean.GoCore.Stmt.seqn
                                     #[GoLean.GoCore.Stmt.assign
                                         (GoLean.GoCore.Assignee.var "$res0")
                                         (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64)),
                                       GoLean.GoCore.Stmt.returnStmt]])
                               (GoLean.GoCore.Stmt.seqn #[]),
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "sieve_harness" },
                 args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c2", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c2"]
                                   { key := "countPrimes" }
                                   #[GoLean.GoCore.Expr.var "n"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "$c2"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false }],
    methods := #[],
    globals := #[],
    methodSets := #[{ key := "struct{}", coverage := GoLean.GoCore.MethodSetCoverage.full }] }

end GoLean.Examples.Sieve
