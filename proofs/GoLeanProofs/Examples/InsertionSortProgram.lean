import GoLean.GoCore.Syntax

/-!
# The insertion-sort example — the frontend's lowering, pinned
(verified-examples arc slice 2c, 2026-08-13)

`isortLowered` is the native frontend's ACTUAL lowering of the
canonical corpus source (`Corpus/coverage/exec/examples/isort/main.go`,
differentially green against `go run`), pinned by
`scripts/check-golden` against `baselines/golden/isort-lowered.repr`.
THIS DEF IS GENERATED from that repr (the literal below IS the repr
text, byte-identical under `repr` — the same both-links story as the
golden pins); regenerate rather than hand-edit.

Pure syntax module: no Iris import, safe for statement-side use.
-/

namespace GoLean.Examples.InsertionSort

open GoLean GoLean.GoCore

/-- The frontend's lowering of the isort subject, verbatim
(`scripts/check-golden` pins it). -/
def isortLowered : Program :=
  { typeDefs := #[({ key := "struct{}" }, GoLean.GoCore.TypeDef.struct #[])],
    funcs := #[{ id := { key := "insertionSort" },
                 args := #[{ id := "s",
                             typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) }],
                 results := #[],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.block
                               #[]
                               #[GoLean.GoCore.Stmt.seqn
                                   #[GoLean.GoCore.Stmt.initialization
                                       { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                                     GoLean.GoCore.Stmt.assign
                                       (GoLean.GoCore.Assignee.var "i")
                                       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))],
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
                                             #[GoLean.GoCore.Stmt.block
                                                 #[]
                                                 #[GoLean.GoCore.Stmt.seqn
                                                     #[GoLean.GoCore.Stmt.initialization
                                                         { id := "j",
                                                           typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                                                       GoLean.GoCore.Stmt.assign
                                                         (GoLean.GoCore.Assignee.var "j")
                                                         (GoLean.GoCore.Expr.var "i")],
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
                                                                 (GoLean.GoCore.Expr.sub
                                                                   (GoLean.GoCore.Expr.var "j")
                                                                   (GoLean.GoCore.Expr.intLit
                                                                     1
                                                                     (GoLean.GoCore.IntKind.int)))),
                                                             GoLean.GoCore.Stmt.seqn #[],
                                                             GoLean.GoCore.Stmt.ifThenElse
                                                               (GoLean.GoCore.Expr.and
                                                                 (GoLean.GoCore.Expr.greaterCmp
                                                                   (GoLean.GoCore.Expr.var "j")
                                                                   (GoLean.GoCore.Expr.intLit
                                                                     0
                                                                     (GoLean.GoCore.IntKind.int)))
                                                                 (GoLean.GoCore.Expr.greaterCmp
                                                                   (GoLean.GoCore.Expr.indexGet
                                                                     (GoLean.GoCore.Expr.var "s")
                                                                     (GoLean.GoCore.Expr.sub
                                                                       (GoLean.GoCore.Expr.var "j")
                                                                       (GoLean.GoCore.Expr.intLit
                                                                         1
                                                                         (GoLean.GoCore.IntKind.int))))
                                                                   (GoLean.GoCore.Expr.indexGet
                                                                     (GoLean.GoCore.Expr.var "s")
                                                                     (GoLean.GoCore.Expr.var "j"))))
                                                               (GoLean.GoCore.Stmt.seqn #[])
                                                               (GoLean.GoCore.Stmt.breakStmt),
                                                             GoLean.GoCore.Stmt.block
                                                               #[]
                                                               #[GoLean.GoCore.Stmt.seqn
                                                                   #[GoLean.GoCore.Stmt.assignMany
                                                                       #[GoLean.GoCore.Assignee.addr
                                                                           (GoLean.GoCore.Expr.indexAddr
                                                                             (GoLean.GoCore.Expr.var "s")
                                                                             (GoLean.GoCore.Expr.sub
                                                                               (GoLean.GoCore.Expr.var "j")
                                                                               (GoLean.GoCore.Expr.intLit
                                                                                 1
                                                                                 (GoLean.GoCore.IntKind.int)))),
                                                                         GoLean.GoCore.Assignee.addr
                                                                           (GoLean.GoCore.Expr.indexAddr
                                                                             (GoLean.GoCore.Expr.var "s")
                                                                             (GoLean.GoCore.Expr.var "j"))]
                                                                       #[GoLean.GoCore.Expr.indexGet
                                                                           (GoLean.GoCore.Expr.var "s")
                                                                           (GoLean.GoCore.Expr.var "j"),
                                                                         GoLean.GoCore.Expr.indexGet
                                                                           (GoLean.GoCore.Expr.var "s")
                                                                           (GoLean.GoCore.Expr.sub
                                                                             (GoLean.GoCore.Expr.var "j")
                                                                             (GoLean.GoCore.Expr.intLit
                                                                               1
                                                                               (GoLean.GoCore.IntKind.int)))]]]])]]]])]]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "sortFour" },
                 args := #[{ id := "a", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "b", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "c", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "d", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                              { id := "$res1", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                              { id := "$res2", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                              { id := "$res3", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
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
                                   (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))
                                   (some (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c0")
                                       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "a"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c0")
                                       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "b"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c0")
                                       (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "c"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c0")
                                       (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "d")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "s",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "s")
                                   (GoLean.GoCore.Expr.var "$c0")],
                             GoLean.GoCore.Stmt.call #[] { key := "insertionSort" } #[GoLean.GoCore.Expr.var "s"],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.indexGet
                                     (GoLean.GoCore.Expr.var "s")
                                     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res1")
                                   (GoLean.GoCore.Expr.indexGet
                                     (GoLean.GoCore.Expr.var "s")
                                     (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res2")
                                   (GoLean.GoCore.Expr.indexGet
                                     (GoLean.GoCore.Expr.var "s")
                                     (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res3")
                                   (GoLean.GoCore.Expr.indexGet
                                     (GoLean.GoCore.Expr.var "s")
                                     (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "sortThree" },
                 args := #[{ id := "a", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "b", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "c", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                              { id := "$res1", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                              { id := "$res2", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c1",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.makeSlice
                                   (GoLean.GoCore.Assignee.var "$c1")
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                   (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))
                                   (some (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c1")
                                       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "a"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c1")
                                       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "b"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c1")
                                       (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "c")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "s",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "s")
                                   (GoLean.GoCore.Expr.var "$c1")],
                             GoLean.GoCore.Stmt.call #[] { key := "insertionSort" } #[GoLean.GoCore.Expr.var "s"],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.indexGet
                                     (GoLean.GoCore.Expr.var "s")
                                     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res1")
                                   (GoLean.GoCore.Expr.indexGet
                                     (GoLean.GoCore.Expr.var "s")
                                     (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res2")
                                   (GoLean.GoCore.Expr.indexGet
                                     (GoLean.GoCore.Expr.var "s")
                                     (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "sortOne" },
                 args := #[{ id := "a", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c2",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.makeSlice
                                   (GoLean.GoCore.Assignee.var "$c2")
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                   (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                                   (some (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c2")
                                       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "a")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "s",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "s")
                                   (GoLean.GoCore.Expr.var "$c2")],
                             GoLean.GoCore.Stmt.call #[] { key := "insertionSort" } #[GoLean.GoCore.Expr.var "s"],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.indexGet
                                     (GoLean.GoCore.Expr.var "s")
                                     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "sortEmpty" },
                 args := #[],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
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
                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))
                                   (some (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "s",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "s")
                                   (GoLean.GoCore.Expr.var "$c3")],
                             GoLean.GoCore.Stmt.call #[] { key := "insertionSort" } #[GoLean.GoCore.Expr.var "s"],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.length
                                     (GoLean.GoCore.Expr.var "s")
                                     (some (GoLean.GoCore.Ty.slice
                                        (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))))),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "isort_harness" },
                 args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "seed", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c4",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.makeSlice
                                   (GoLean.GoCore.Assignee.var "$c4")
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
                                   (GoLean.GoCore.Expr.var "$c4")],
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
                                                     (GoLean.GoCore.Expr.mul
                                                       (GoLean.GoCore.Expr.var "seed")
                                                       (GoLean.GoCore.Expr.add
                                                         (GoLean.GoCore.Expr.var "i")
                                                         (GoLean.GoCore.Expr.intLit
                                                           1
                                                           (GoLean.GoCore.IntKind.uint64))))]]])]],
                             GoLean.GoCore.Stmt.call #[] { key := "insertionSort" } #[GoLean.GoCore.Expr.var "s"],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "ok", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "ok")
                                   (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64))],
                             GoLean.GoCore.Stmt.block
                               #[]
                               #[GoLean.GoCore.Stmt.seqn
                                   #[GoLean.GoCore.Stmt.initialization
                                       { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                     GoLean.GoCore.Stmt.assign
                                       (GoLean.GoCore.Assignee.var "i")
                                       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64))],
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
                                             #[GoLean.GoCore.Stmt.ifThenElse
                                                 (GoLean.GoCore.Expr.greaterCmp
                                                   (GoLean.GoCore.Expr.indexGet
                                                     (GoLean.GoCore.Expr.var "s")
                                                     (GoLean.GoCore.Expr.sub
                                                       (GoLean.GoCore.Expr.var "i")
                                                       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64))))
                                                   (GoLean.GoCore.Expr.indexGet
                                                     (GoLean.GoCore.Expr.var "s")
                                                     (GoLean.GoCore.Expr.var "i")))
                                                 (GoLean.GoCore.Stmt.block
                                                   #[]
                                                   #[GoLean.GoCore.Stmt.seqn
                                                       #[GoLean.GoCore.Stmt.assign
                                                           (GoLean.GoCore.Assignee.var "ok")
                                                           (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))]])
                                                 (GoLean.GoCore.Stmt.seqn #[])]])]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c5",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.makeSlice
                                   (GoLean.GoCore.Assignee.var "$c5")
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                   (GoLean.GoCore.Expr.var "n")
                                   none],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "t",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "t")
                                   (GoLean.GoCore.Expr.var "$c5")],
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
                                                         (GoLean.GoCore.Expr.var "t")
                                                         (GoLean.GoCore.Expr.var "i")))
                                                     (GoLean.GoCore.Expr.mul
                                                       (GoLean.GoCore.Expr.var "seed")
                                                       (GoLean.GoCore.Expr.add
                                                         (GoLean.GoCore.Expr.var "i")
                                                         (GoLean.GoCore.Expr.intLit
                                                           1
                                                           (GoLean.GoCore.IntKind.uint64))))]]])]],
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
                                                 #[GoLean.GoCore.Stmt.initialization
                                                     { id := "cs",
                                                       typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                                   GoLean.GoCore.Stmt.assign
                                                     (GoLean.GoCore.Assignee.var "cs")
                                                     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))],
                                               GoLean.GoCore.Stmt.seqn
                                                 #[GoLean.GoCore.Stmt.initialization
                                                     { id := "ct",
                                                       typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                                   GoLean.GoCore.Stmt.assign
                                                     (GoLean.GoCore.Assignee.var "ct")
                                                     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))],
                                               GoLean.GoCore.Stmt.block
                                                 #[]
                                                 #[GoLean.GoCore.Stmt.seqn
                                                     #[GoLean.GoCore.Stmt.initialization
                                                         { id := "j",
                                                           typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                                       GoLean.GoCore.Stmt.assign
                                                         (GoLean.GoCore.Assignee.var "j")
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
                                                                 (GoLean.GoCore.Assignee.var "j")
                                                                 (GoLean.GoCore.Expr.add
                                                                   (GoLean.GoCore.Expr.var "j")
                                                                   (GoLean.GoCore.Expr.intLit
                                                                     1
                                                                     (GoLean.GoCore.IntKind.uint64)))),
                                                             GoLean.GoCore.Stmt.seqn #[],
                                                             GoLean.GoCore.Stmt.ifThenElse
                                                               (GoLean.GoCore.Expr.lessCmp
                                                                 (GoLean.GoCore.Expr.var "j")
                                                                 (GoLean.GoCore.Expr.var "n"))
                                                               (GoLean.GoCore.Stmt.seqn #[])
                                                               (GoLean.GoCore.Stmt.breakStmt),
                                                             GoLean.GoCore.Stmt.block
                                                               #[]
                                                               #[GoLean.GoCore.Stmt.ifThenElse
                                                                   (GoLean.GoCore.Expr.eqCmp
                                                                     (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                                                     (GoLean.GoCore.Expr.indexGet
                                                                       (GoLean.GoCore.Expr.var "s")
                                                                       (GoLean.GoCore.Expr.var "j"))
                                                                     (GoLean.GoCore.Expr.indexGet
                                                                       (GoLean.GoCore.Expr.var "t")
                                                                       (GoLean.GoCore.Expr.var "i")))
                                                                   (GoLean.GoCore.Stmt.block
                                                                     #[]
                                                                     #[GoLean.GoCore.Stmt.assign
                                                                         (GoLean.GoCore.Assignee.var "cs")
                                                                         (GoLean.GoCore.Expr.add
                                                                           (GoLean.GoCore.Expr.var "cs")
                                                                           (GoLean.GoCore.Expr.intLit
                                                                             1
                                                                             (GoLean.GoCore.IntKind.uint64)))])
                                                                   (GoLean.GoCore.Stmt.seqn #[]),
                                                                 GoLean.GoCore.Stmt.ifThenElse
                                                                   (GoLean.GoCore.Expr.eqCmp
                                                                     (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                                                     (GoLean.GoCore.Expr.indexGet
                                                                       (GoLean.GoCore.Expr.var "t")
                                                                       (GoLean.GoCore.Expr.var "j"))
                                                                     (GoLean.GoCore.Expr.indexGet
                                                                       (GoLean.GoCore.Expr.var "t")
                                                                       (GoLean.GoCore.Expr.var "i")))
                                                                   (GoLean.GoCore.Stmt.block
                                                                     #[]
                                                                     #[GoLean.GoCore.Stmt.assign
                                                                         (GoLean.GoCore.Assignee.var "ct")
                                                                         (GoLean.GoCore.Expr.add
                                                                           (GoLean.GoCore.Expr.var "ct")
                                                                           (GoLean.GoCore.Expr.intLit
                                                                             1
                                                                             (GoLean.GoCore.IntKind.uint64)))])
                                                                   (GoLean.GoCore.Stmt.seqn #[])]])]],
                                               GoLean.GoCore.Stmt.ifThenElse
                                                 (GoLean.GoCore.Expr.neqCmp
                                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                                   (GoLean.GoCore.Expr.var "cs")
                                                   (GoLean.GoCore.Expr.var "ct"))
                                                 (GoLean.GoCore.Stmt.block
                                                   #[]
                                                   #[GoLean.GoCore.Stmt.seqn
                                                       #[GoLean.GoCore.Stmt.assign
                                                           (GoLean.GoCore.Assignee.var "ok")
                                                           (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))]])
                                                 (GoLean.GoCore.Stmt.seqn #[])]])]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "ok"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false }],
    methods := #[],
    globals := #[],
    methodSets := #[{ key := "struct{}", coverage := GoLean.GoCore.MethodSetCoverage.full }] }

end GoLean.Examples.InsertionSort
