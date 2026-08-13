import GoLean.GoCore.Syntax

/-!
# The min/max-of-a-slice example — the frontend's lowering, pinned
(verified-examples arc slice 2c, 2026-08-13)

`minMaxLowered` is the native frontend's ACTUAL lowering of the
canonical corpus source (`Corpus/coverage/exec/examples/minmax/main.go`,
differentially green against `go run`), pinned by
`scripts/check-golden` against `baselines/golden/minmax-lowered.repr`.
THIS DEF IS GENERATED from that repr (the literal below IS the repr
text, byte-identical under `repr` — the same both-links story as the
golden pins); regenerate rather than hand-edit.

Pure syntax module: no Iris import, safe for statement-side use.
-/

namespace GoLean.Examples.MinMax

open GoLean GoLean.GoCore

/-- The frontend's lowering of the minmax subject, verbatim
(`scripts/check-golden` pins it). -/
def minMaxLowered : Program :=
  { typeDefs := #[({ key := "struct{}" }, GoLean.GoCore.TypeDef.struct #[])],
    funcs := #[{ id := { key := "minMax" },
                 args := #[{ id := "s",
                             typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                              { id := "$res1", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "lo", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.initialization
                                   { id := "hi", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.assignMany
                                   #[GoLean.GoCore.Assignee.var "lo", GoLean.GoCore.Assignee.var "hi"]
                                   #[GoLean.GoCore.Expr.indexGet
                                       (GoLean.GoCore.Expr.var "s")
                                       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)),
                                     GoLean.GoCore.Expr.indexGet
                                       (GoLean.GoCore.Expr.var "s")
                                       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))]],
                             GoLean.GoCore.Stmt.block
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
                                             #[GoLean.GoCore.Stmt.ifThenElse
                                                 (GoLean.GoCore.Expr.lessCmp
                                                   (GoLean.GoCore.Expr.indexGet
                                                     (GoLean.GoCore.Expr.var "s")
                                                     (GoLean.GoCore.Expr.var "i"))
                                                   (GoLean.GoCore.Expr.var "lo"))
                                                 (GoLean.GoCore.Stmt.block
                                                   #[]
                                                   #[GoLean.GoCore.Stmt.seqn
                                                       #[GoLean.GoCore.Stmt.assign
                                                           (GoLean.GoCore.Assignee.var "lo")
                                                           (GoLean.GoCore.Expr.indexGet
                                                             (GoLean.GoCore.Expr.var "s")
                                                             (GoLean.GoCore.Expr.var "i"))]])
                                                 (GoLean.GoCore.Stmt.seqn #[]),
                                               GoLean.GoCore.Stmt.ifThenElse
                                                 (GoLean.GoCore.Expr.greaterCmp
                                                   (GoLean.GoCore.Expr.indexGet
                                                     (GoLean.GoCore.Expr.var "s")
                                                     (GoLean.GoCore.Expr.var "i"))
                                                   (GoLean.GoCore.Expr.var "hi"))
                                                 (GoLean.GoCore.Stmt.block
                                                   #[]
                                                   #[GoLean.GoCore.Stmt.seqn
                                                       #[GoLean.GoCore.Stmt.assign
                                                           (GoLean.GoCore.Assignee.var "hi")
                                                           (GoLean.GoCore.Expr.indexGet
                                                             (GoLean.GoCore.Expr.var "s")
                                                             (GoLean.GoCore.Expr.var "i"))]])
                                                 (GoLean.GoCore.Stmt.seqn #[])]])]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "lo"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res1")
                                   (GoLean.GoCore.Expr.var "hi"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "minMaxFour" },
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
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c1", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.initialization
                                   { id := "$c2", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c1", GoLean.GoCore.Assignee.var "$c2"]
                                   { key := "minMax" }
                                   #[GoLean.GoCore.Expr.var "s"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "$c1"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res1")
                                   (GoLean.GoCore.Expr.var "$c2"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "minMaxThree" },
                 args := #[{ id := "a", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "b", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "c", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
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
                                   (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))
                                   (some (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))),
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
                                   (GoLean.GoCore.Expr.var "c")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "s",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "s")
                                   (GoLean.GoCore.Expr.var "$c3")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c4", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.initialization
                                   { id := "$c5", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c4", GoLean.GoCore.Assignee.var "$c5"]
                                   { key := "minMax" }
                                   #[GoLean.GoCore.Expr.var "s"]],
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
               { id := { key := "minMaxOne" },
                 args := #[{ id := "a", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
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
                                   { id := "s",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "s")
                                   (GoLean.GoCore.Expr.var "$c6")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c7", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.initialization
                                   { id := "$c8", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c7", GoLean.GoCore.Assignee.var "$c8"]
                                   { key := "minMax" }
                                   #[GoLean.GoCore.Expr.var "s"]],
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
               { id := { key := "minMaxEmpty" },
                 args := #[],
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
                                   { id := "s",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "s")
                                   (GoLean.GoCore.Expr.var "$c9")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c10", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.initialization
                                   { id := "$c11", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c10", GoLean.GoCore.Assignee.var "$c11"]
                                   { key := "minMax" }
                                   #[GoLean.GoCore.Expr.var "s"]],
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
               { id := { key := "minmax_harness" },
                 args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "seed", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                              { id := "$res1", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
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
                                   { id := "s",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "s")
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
                                                         (GoLean.GoCore.Expr.var "s")
                                                         (GoLean.GoCore.Expr.var "i")))
                                                     (GoLean.GoCore.Expr.add
                                                       (GoLean.GoCore.Expr.var "seed")
                                                       (GoLean.GoCore.Expr.var "i"))]]])]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c13", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.initialization
                                   { id := "$c14", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c13", GoLean.GoCore.Assignee.var "$c14"]
                                   { key := "minMax" }
                                   #[GoLean.GoCore.Expr.var "s"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "$c13"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res1")
                                   (GoLean.GoCore.Expr.var "$c14"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false }],
    methods := #[],
    globals := #[],
    methodSets := #[{ key := "struct{}", coverage := GoLean.GoCore.MethodSetCoverage.full }] }

end GoLean.Examples.MinMax
