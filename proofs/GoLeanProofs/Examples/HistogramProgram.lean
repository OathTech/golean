import GoLean.GoCore.Syntax

/-!
# The map histogram example — the frontend's lowering, pinned
(gallery campaign G1, flagship example, 2026-08-15)

`histogramLowered` is the native frontend's ACTUAL lowering of the
canonical corpus source (`Corpus/coverage/exec/examples/histogram/main.go`,
differentially green against `go run`), pinned by
`scripts/check-golden` against `baselines/golden/histogram-lowered.repr`.
THIS DEF IS GENERATED from that repr (the literal below IS the repr
text, byte-identical under `repr` — the same both-links story as the
golden pins); regenerate rather than hand-edit.

Pure syntax module: no Iris import, safe for statement-side use.
-/

namespace GoLean.Examples.Histogram

open GoLean GoLean.GoCore

/-- The frontend's lowering of the histogram subject, verbatim
(`scripts/check-golden` pins it). -/
def histogramLowered : Program :=
  { typeDefs := #[({ key := "struct{}" }, GoLean.GoCore.TypeDef.struct #[])],
    funcs := #[{ id := { key := "histogram" },
                 args := #[{ id := "vals",
                             typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                           { id := "q", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                              { id := "$res1", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c0",
                                     typ := GoLean.GoCore.Ty.map
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.makeMap
                                   (GoLean.GoCore.Assignee.var "$c0")
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                   none],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "counts",
                                     typ := GoLean.GoCore.Ty.map
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "counts")
                                   (GoLean.GoCore.Expr.var "$c0")],
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
                                                 #[GoLean.GoCore.Stmt.initialization
                                                     { id := "$c1",
                                                       typ := GoLean.GoCore.Ty.map
                                                                (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                                                (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                                   GoLean.GoCore.Stmt.assign
                                                     (GoLean.GoCore.Assignee.var "$c1")
                                                     (GoLean.GoCore.Expr.var "counts")],
                                               GoLean.GoCore.Stmt.seqn
                                                 #[GoLean.GoCore.Stmt.initialization
                                                     { id := "$c2",
                                                       typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                                   GoLean.GoCore.Stmt.assign
                                                     (GoLean.GoCore.Assignee.var "$c2")
                                                     (GoLean.GoCore.Expr.indexGet
                                                       (GoLean.GoCore.Expr.var "vals")
                                                       (GoLean.GoCore.Expr.var "i"))],
                                               GoLean.GoCore.Stmt.mapAssign
                                                 (GoLean.GoCore.Expr.var "$c1")
                                                 (GoLean.GoCore.Expr.var "$c2")
                                                 (GoLean.GoCore.Expr.add
                                                   (GoLean.GoCore.Expr.mapGet
                                                     (GoLean.GoCore.Expr.var "$c1")
                                                     (GoLean.GoCore.Expr.var "$c2")
                                                     (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                                     (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))
                                                   (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)))
                                                 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                                 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))]])]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "hits", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "hits")
                                   (GoLean.GoCore.Expr.mapGet
                                     (GoLean.GoCore.Expr.var "counts")
                                     (GoLean.GoCore.Expr.var "q")
                                     (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                     (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "distinct", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "distinct")
                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))],
                             GoLean.GoCore.Stmt.mapRange
                               none
                               none
                               (GoLean.GoCore.Expr.var "counts")
                               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                               (GoLean.GoCore.Stmt.block
                                 #[]
                                 #[GoLean.GoCore.Stmt.assign
                                     (GoLean.GoCore.Assignee.var "distinct")
                                     (GoLean.GoCore.Expr.add
                                       (GoLean.GoCore.Expr.var "distinct")
                                       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)))]),
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "hits"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res1")
                                   (GoLean.GoCore.Expr.var "distinct"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "histogramFour" },
                 args := #[{ id := "a", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "b", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "c", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "d", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "q", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                              { id := "$res1", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c3",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.makeSlice
                                   (GoLean.GoCore.Assignee.var "$c3")
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                   (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))
                                   (some (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c3")
                                       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "a"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c3")
                                       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "b"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c3")
                                       (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "c"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c3")
                                       (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "d")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c4", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.initialization
                                   { id := "$c5", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c4", GoLean.GoCore.Assignee.var "$c5"]
                                   { key := "histogram" }
                                   #[GoLean.GoCore.Expr.var "$c3", GoLean.GoCore.Expr.var "q"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "$c4"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res1")
                                   (GoLean.GoCore.Expr.var "$c5"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "histogramOne" },
                 args := #[{ id := "a", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "q", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                              { id := "$res1", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
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
                                   (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                                   (some (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c6")
                                       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "a")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c7", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.initialization
                                   { id := "$c8", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c7", GoLean.GoCore.Assignee.var "$c8"]
                                   { key := "histogram" }
                                   #[GoLean.GoCore.Expr.var "$c6", GoLean.GoCore.Expr.var "q"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "$c7"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res1")
                                   (GoLean.GoCore.Expr.var "$c8"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "histogramEmpty" },
                 args := #[{ id := "q", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                              { id := "$res1", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
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
                                   { id := "$c10", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.initialization
                                   { id := "$c11", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c10", GoLean.GoCore.Assignee.var "$c11"]
                                   { key := "histogram" }
                                   #[GoLean.GoCore.Expr.var "$c9", GoLean.GoCore.Expr.var "q"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "$c10"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res1")
                                   (GoLean.GoCore.Expr.var "$c11"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "histogram_harness_r" },
                 args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "seed", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "q", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0",
                                typ := GoLean.GoCore.Ty.array 8 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                              { id := "$res1", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                              { id := "$res2", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c12",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.makeSlice
                                   (GoLean.GoCore.Assignee.var "$c12")
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                   (GoLean.GoCore.Expr.var "n")
                                   none],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "v",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "v")
                                   (GoLean.GoCore.Expr.var "$c12")],
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
                                                         (GoLean.GoCore.Expr.var "v")
                                                         (GoLean.GoCore.Expr.var "i")))
                                                     (GoLean.GoCore.Expr.add
                                                       (GoLean.GoCore.Expr.var "seed")
                                                       (GoLean.GoCore.Expr.mod
                                                         (GoLean.GoCore.Expr.var "i")
                                                         (GoLean.GoCore.Expr.intLit
                                                           3
                                                           (GoLean.GoCore.IntKind.uint64))))]]])]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "vals",
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
                                                         (GoLean.GoCore.Expr.ref "vals")
                                                         (GoLean.GoCore.Expr.var "i")))
                                                     (GoLean.GoCore.Expr.indexGet
                                                       (GoLean.GoCore.Expr.var "v")
                                                       (GoLean.GoCore.Expr.var "i"))]]])]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "hits", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.initialization
                                   { id := "distinct", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "hits", GoLean.GoCore.Assignee.var "distinct"]
                                   { key := "histogram" }
                                   #[GoLean.GoCore.Expr.var "v", GoLean.GoCore.Expr.var "q"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "vals"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res1")
                                   (GoLean.GoCore.Expr.var "hits"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res2")
                                   (GoLean.GoCore.Expr.var "distinct"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false }],
    methods := #[],
    globals := #[],
    methodSets := #[{ key := "struct{}", coverage := GoLean.GoCore.MethodSetCoverage.full }] }

end GoLean.Examples.Histogram
