import GoLean.GoCore.Syntax

/-!
# The `rle` example — the frontend's lowering, pinned
(gallery campaign G1, guardrails wave, 2026-08-15)

`rleLowered` is the native frontend's ACTUAL lowering of the
canonical corpus source (`Corpus/coverage/exec/examples/rle/main.go`,
differentially green against `go run`), pinned by `scripts/check-golden`
against `baselines/golden/rle-lowered.repr`. THIS DEF IS GENERATED from
that repr (the literal below IS the repr text, byte-identical under
`repr` — the same both-links story as the other golden pins);
regenerate rather than hand-edit.

Pure syntax module: no Iris import, safe for statement-side use.
-/

namespace GoLean.Examples.RunLength

open GoLean GoLean.GoCore

/-- The frontend's lowering of the `rle` subject, verbatim
(`scripts/check-golden` pins it). -/
def rleLowered : Program :=
  { typeDefs := #[({ key := "struct{}" }, GoLean.GoCore.TypeDef.struct #[])],
    funcs := #[{ id := { key := "rle" },
                 args := #[{ id := "s",
                             typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) }],
                 results := #[{ id := "$res0",
                                typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                              { id := "$res1",
                                typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c0",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.makeSlice
                                   (GoLean.GoCore.Assignee.var "$c0")
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))
                                   (some (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "runVals",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "runVals")
                                   (GoLean.GoCore.Expr.var "$c0")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c1",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.makeSlice
                                   (GoLean.GoCore.Assignee.var "$c1")
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))
                                   (some (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "runCounts",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "runCounts")
                                   (GoLean.GoCore.Expr.var "$c1")],
                             GoLean.GoCore.Stmt.block
                               #[]
                               #[GoLean.GoCore.Stmt.seqn
                                   #[GoLean.GoCore.Stmt.initialization
                                       { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                                     GoLean.GoCore.Stmt.assign
                                       (GoLean.GoCore.Assignee.var "i")
                                       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
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
                                                 (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))),
                                           GoLean.GoCore.Stmt.seqn #[],
                                           GoLean.GoCore.Stmt.ifThenElse
                                             (GoLean.GoCore.Expr.lessCmp
                                               (GoLean.GoCore.Expr.var "i")
                                               (GoLean.GoCore.Expr.length
                                                 (GoLean.GoCore.Expr.var "s")
                                                 (some (GoLean.GoCore.Ty.slice
                                                    (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))))))
                                             (GoLean.GoCore.Stmt.seqn #[])
                                             (GoLean.GoCore.Stmt.breakStmt),
                                           GoLean.GoCore.Stmt.block
                                             #[]
                                             #[GoLean.GoCore.Stmt.seqn
                                                 #[GoLean.GoCore.Stmt.initialization
                                                     { id := "k",
                                                       typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                                                   GoLean.GoCore.Stmt.assign
                                                     (GoLean.GoCore.Assignee.var "k")
                                                     (GoLean.GoCore.Expr.length
                                                       (GoLean.GoCore.Expr.var "runVals")
                                                       (some (GoLean.GoCore.Ty.slice
                                                          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))))],
                                               GoLean.GoCore.Stmt.seqn
                                                 #[GoLean.GoCore.Stmt.initialization
                                                     { id := "extended", typ := GoLean.GoCore.Ty.bool },
                                                   GoLean.GoCore.Stmt.assign
                                                     (GoLean.GoCore.Assignee.var "extended")
                                                     (GoLean.GoCore.Expr.boolLit false)],
                                               GoLean.GoCore.Stmt.ifThenElse
                                                 (GoLean.GoCore.Expr.greaterCmp
                                                   (GoLean.GoCore.Expr.var "k")
                                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
                                                 (GoLean.GoCore.Stmt.block
                                                   #[]
                                                   #[GoLean.GoCore.Stmt.ifThenElse
                                                       (GoLean.GoCore.Expr.eqCmp
                                                         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                                         (GoLean.GoCore.Expr.indexGet
                                                           (GoLean.GoCore.Expr.var "runVals")
                                                           (GoLean.GoCore.Expr.sub
                                                             (GoLean.GoCore.Expr.var "k")
                                                             (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
                                                         (GoLean.GoCore.Expr.indexGet
                                                           (GoLean.GoCore.Expr.var "s")
                                                           (GoLean.GoCore.Expr.var "i")))
                                                       (GoLean.GoCore.Stmt.block
                                                         #[]
                                                         #[GoLean.GoCore.Stmt.assign
                                                             (GoLean.GoCore.Assignee.addr
                                                               (GoLean.GoCore.Expr.indexAddr
                                                                 (GoLean.GoCore.Expr.var "runCounts")
                                                                 (GoLean.GoCore.Expr.sub
                                                                   (GoLean.GoCore.Expr.var "k")
                                                                   (GoLean.GoCore.Expr.intLit
                                                                     1
                                                                     (GoLean.GoCore.IntKind.int)))))
                                                             (GoLean.GoCore.Expr.add
                                                               (GoLean.GoCore.Expr.indexGet
                                                                 (GoLean.GoCore.Expr.var "runCounts")
                                                                 (GoLean.GoCore.Expr.sub
                                                                   (GoLean.GoCore.Expr.var "k")
                                                                   (GoLean.GoCore.Expr.intLit
                                                                     1
                                                                     (GoLean.GoCore.IntKind.int))))
                                                               (GoLean.GoCore.Expr.intLit
                                                                 1
                                                                 (GoLean.GoCore.IntKind.uint64))),
                                                           GoLean.GoCore.Stmt.seqn
                                                             #[GoLean.GoCore.Stmt.assign
                                                                 (GoLean.GoCore.Assignee.var "extended")
                                                                 (GoLean.GoCore.Expr.boolLit true)]])
                                                       (GoLean.GoCore.Stmt.seqn #[])])
                                                 (GoLean.GoCore.Stmt.seqn #[]),
                                               GoLean.GoCore.Stmt.ifThenElse
                                                 (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "extended"))
                                                 (GoLean.GoCore.Stmt.block
                                                   #[]
                                                   #[GoLean.GoCore.Stmt.seqn
                                                       #[GoLean.GoCore.Stmt.initialization
                                                           { id := "$c2",
                                                             typ := GoLean.GoCore.Ty.slice
                                                                      (GoLean.GoCore.Ty.int
                                                                        (GoLean.GoCore.IntKind.uint64)) },
                                                         GoLean.GoCore.Stmt.makeSlice
                                                           (GoLean.GoCore.Assignee.var "$c2")
                                                           (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                                           (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                                                           (some (GoLean.GoCore.Expr.intLit
                                                              1
                                                              (GoLean.GoCore.IntKind.int))),
                                                         GoLean.GoCore.Stmt.assign
                                                           (GoLean.GoCore.Assignee.addr
                                                             (GoLean.GoCore.Expr.indexAddr
                                                               (GoLean.GoCore.Expr.var "$c2")
                                                               (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                                                           (GoLean.GoCore.Expr.indexGet
                                                             (GoLean.GoCore.Expr.var "s")
                                                             (GoLean.GoCore.Expr.var "i"))],
                                                     GoLean.GoCore.Stmt.seqn
                                                       #[GoLean.GoCore.Stmt.initialization
                                                           { id := "$c3",
                                                             typ := GoLean.GoCore.Ty.slice
                                                                      (GoLean.GoCore.Ty.int
                                                                        (GoLean.GoCore.IntKind.uint64)) },
                                                         GoLean.GoCore.Stmt.appendSlice
                                                           (GoLean.GoCore.Assignee.var "$c3")
                                                           (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                                           (GoLean.GoCore.Expr.var "runVals")
                                                           (GoLean.GoCore.Expr.var "$c2")],
                                                     GoLean.GoCore.Stmt.seqn
                                                       #[GoLean.GoCore.Stmt.assign
                                                           (GoLean.GoCore.Assignee.var "runVals")
                                                           (GoLean.GoCore.Expr.var "$c3")],
                                                     GoLean.GoCore.Stmt.seqn
                                                       #[GoLean.GoCore.Stmt.initialization
                                                           { id := "$c4",
                                                             typ := GoLean.GoCore.Ty.slice
                                                                      (GoLean.GoCore.Ty.int
                                                                        (GoLean.GoCore.IntKind.uint64)) },
                                                         GoLean.GoCore.Stmt.makeSlice
                                                           (GoLean.GoCore.Assignee.var "$c4")
                                                           (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                                           (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                                                           (some (GoLean.GoCore.Expr.intLit
                                                              1
                                                              (GoLean.GoCore.IntKind.int))),
                                                         GoLean.GoCore.Stmt.assign
                                                           (GoLean.GoCore.Assignee.addr
                                                             (GoLean.GoCore.Expr.indexAddr
                                                               (GoLean.GoCore.Expr.var "$c4")
                                                               (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                                                           (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64))],
                                                     GoLean.GoCore.Stmt.seqn
                                                       #[GoLean.GoCore.Stmt.initialization
                                                           { id := "$c5",
                                                             typ := GoLean.GoCore.Ty.slice
                                                                      (GoLean.GoCore.Ty.int
                                                                        (GoLean.GoCore.IntKind.uint64)) },
                                                         GoLean.GoCore.Stmt.appendSlice
                                                           (GoLean.GoCore.Assignee.var "$c5")
                                                           (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                                           (GoLean.GoCore.Expr.var "runCounts")
                                                           (GoLean.GoCore.Expr.var "$c4")],
                                                     GoLean.GoCore.Stmt.seqn
                                                       #[GoLean.GoCore.Stmt.assign
                                                           (GoLean.GoCore.Assignee.var "runCounts")
                                                           (GoLean.GoCore.Expr.var "$c5")]])
                                                 (GoLean.GoCore.Stmt.seqn #[])]])]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "runVals"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res1")
                                   (GoLean.GoCore.Expr.var "runCounts"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "rleFourCount" },
                 args := #[{ id := "a", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "b", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "c", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "d", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c6",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.makeSlice
                                   (GoLean.GoCore.Assignee.var "$c6")
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                   (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))
                                   (some (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c6")
                                       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "a"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c6")
                                       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "b"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c6")
                                       (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "c"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c6")
                                       (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "d")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "vals",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.initialization
                                   { id := "$cr1",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "vals", GoLean.GoCore.Assignee.var "$cr1"]
                                   { key := "rle" }
                                   #[GoLean.GoCore.Expr.var "$c6"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.convert
                                     (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                     (GoLean.GoCore.Expr.length
                                       (GoLean.GoCore.Expr.var "vals")
                                       (some (GoLean.GoCore.Ty.slice
                                          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))))),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "rleFourFirst" },
                 args := #[{ id := "a", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "b", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "c", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "d", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                              { id := "$res1", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c7",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.makeSlice
                                   (GoLean.GoCore.Assignee.var "$c7")
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                   (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))
                                   (some (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c7")
                                       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "a"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c7")
                                       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "b"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c7")
                                       (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "c"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c7")
                                       (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "d")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "vals",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.initialization
                                   { id := "counts",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "vals", GoLean.GoCore.Assignee.var "counts"]
                                   { key := "rle" }
                                   #[GoLean.GoCore.Expr.var "$c7"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.indexGet
                                     (GoLean.GoCore.Expr.var "vals")
                                     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res1")
                                   (GoLean.GoCore.Expr.indexGet
                                     (GoLean.GoCore.Expr.var "counts")
                                     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "rleOne" },
                 args := #[{ id := "a", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                              { id := "$res1", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c8",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.makeSlice
                                   (GoLean.GoCore.Assignee.var "$c8")
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                   (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                                   (some (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c8")
                                       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "a")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "vals",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.initialization
                                   { id := "counts",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "vals", GoLean.GoCore.Assignee.var "counts"]
                                   { key := "rle" }
                                   #[GoLean.GoCore.Expr.var "$c8"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.indexGet
                                     (GoLean.GoCore.Expr.var "vals")
                                     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res1")
                                   (GoLean.GoCore.Expr.indexGet
                                     (GoLean.GoCore.Expr.var "counts")
                                     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "rleEmpty" },
                 args := #[],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c9",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.makeSlice
                                   (GoLean.GoCore.Assignee.var "$c9")
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))
                                   (some (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "vals",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.initialization
                                   { id := "$cr1",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "vals", GoLean.GoCore.Assignee.var "$cr1"]
                                   { key := "rle" }
                                   #[GoLean.GoCore.Expr.var "$c9"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.convert
                                     (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                     (GoLean.GoCore.Expr.length
                                       (GoLean.GoCore.Expr.var "vals")
                                       (some (GoLean.GoCore.Ty.slice
                                          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))))),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "rle_harness_r" },
                 args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "seed", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0",
                                typ := GoLean.GoCore.Ty.array 8 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                              { id := "$res1",
                                typ := GoLean.GoCore.Ty.array 8 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                              { id := "$res2",
                                typ := GoLean.GoCore.Ty.array 8 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                              { id := "$res3", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c10",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.makeSlice
                                   (GoLean.GoCore.Assignee.var "$c10")
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                   (GoLean.GoCore.Expr.var "n")
                                   none],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "s",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "s")
                                   (GoLean.GoCore.Expr.var "$c10")],
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
                                                 #[GoLean.GoCore.Stmt.assign
                                                     (GoLean.GoCore.Assignee.addr
                                                       (GoLean.GoCore.Expr.indexAddr
                                                         (GoLean.GoCore.Expr.var "s")
                                                         (GoLean.GoCore.Expr.var "i")))
                                                     (GoLean.GoCore.Expr.add
                                                       (GoLean.GoCore.Expr.var "seed")
                                                       (GoLean.GoCore.Expr.div
                                                         (GoLean.GoCore.Expr.var "i")
                                                         (GoLean.GoCore.Expr.intLit
                                                           3
                                                           (GoLean.GoCore.IntKind.uint64))))]]])]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "pre",
                                     typ := GoLean.GoCore.Ty.array
                                              8
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) }],
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
                                                 #[GoLean.GoCore.Stmt.assign
                                                     (GoLean.GoCore.Assignee.addr
                                                       (GoLean.GoCore.Expr.indexAddr
                                                         (GoLean.GoCore.Expr.ref "pre")
                                                         (GoLean.GoCore.Expr.var "i")))
                                                     (GoLean.GoCore.Expr.indexGet
                                                       (GoLean.GoCore.Expr.var "s")
                                                       (GoLean.GoCore.Expr.var "i"))]]])]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "vals",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.initialization
                                   { id := "counts",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "vals", GoLean.GoCore.Assignee.var "counts"]
                                   { key := "rle" }
                                   #[GoLean.GoCore.Expr.var "s"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "runVals",
                                     typ := GoLean.GoCore.Ty.array
                                              8
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) }],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "runCounts",
                                     typ := GoLean.GoCore.Ty.array
                                              8
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) }],
                             GoLean.GoCore.Stmt.block
                               #[]
                               #[GoLean.GoCore.Stmt.seqn
                                   #[GoLean.GoCore.Stmt.initialization
                                       { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                                     GoLean.GoCore.Stmt.assign
                                       (GoLean.GoCore.Assignee.var "i")
                                       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
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
                                                 (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))),
                                           GoLean.GoCore.Stmt.seqn #[],
                                           GoLean.GoCore.Stmt.ifThenElse
                                             (GoLean.GoCore.Expr.lessCmp
                                               (GoLean.GoCore.Expr.var "i")
                                               (GoLean.GoCore.Expr.length
                                                 (GoLean.GoCore.Expr.var "vals")
                                                 (some (GoLean.GoCore.Ty.slice
                                                    (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))))))
                                             (GoLean.GoCore.Stmt.seqn #[])
                                             (GoLean.GoCore.Stmt.breakStmt),
                                           GoLean.GoCore.Stmt.block
                                             #[]
                                             #[GoLean.GoCore.Stmt.seqn
                                                 #[GoLean.GoCore.Stmt.assign
                                                     (GoLean.GoCore.Assignee.addr
                                                       (GoLean.GoCore.Expr.indexAddr
                                                         (GoLean.GoCore.Expr.ref "runVals")
                                                         (GoLean.GoCore.Expr.var "i")))
                                                     (GoLean.GoCore.Expr.indexGet
                                                       (GoLean.GoCore.Expr.var "vals")
                                                       (GoLean.GoCore.Expr.var "i"))],
                                               GoLean.GoCore.Stmt.seqn
                                                 #[GoLean.GoCore.Stmt.assign
                                                     (GoLean.GoCore.Assignee.addr
                                                       (GoLean.GoCore.Expr.indexAddr
                                                         (GoLean.GoCore.Expr.ref "runCounts")
                                                         (GoLean.GoCore.Expr.var "i")))
                                                     (GoLean.GoCore.Expr.indexGet
                                                       (GoLean.GoCore.Expr.var "counts")
                                                       (GoLean.GoCore.Expr.var "i"))]]])]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "pre"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res1")
                                   (GoLean.GoCore.Expr.var "runVals"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res2")
                                   (GoLean.GoCore.Expr.var "runCounts"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res3")
                                   (GoLean.GoCore.Expr.convert
                                     (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                     (GoLean.GoCore.Expr.length
                                       (GoLean.GoCore.Expr.var "vals")
                                       (some (GoLean.GoCore.Ty.slice
                                          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))))),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false }],
    methods := #[],
    globals := #[],
    methodSets := #[{ key := "struct{}", coverage := GoLean.GoCore.MethodSetCoverage.full }] }

end GoLean.Examples.RunLength
