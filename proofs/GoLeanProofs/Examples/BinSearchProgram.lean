import GoLean.GoCore.Syntax

/-!
# The binary-search example — the frontend's lowering, pinned
(verified-examples arc slice 2c, 2026-08-13)

`searchLowered` is the native frontend's ACTUAL lowering of the
canonical corpus source (`Corpus/coverage/exec/examples/binsearch/main.go`,
differentially green against `go run`), pinned by
`scripts/check-golden` against `baselines/golden/binsearch-lowered.repr`.
THIS DEF IS GENERATED from that repr (the literal below IS the repr
text, byte-identical under `repr` — the same both-links story as the
golden pins); regenerate rather than hand-edit.

Pure syntax module: no Iris import, safe for statement-side use.
-/

namespace GoLean.Examples.BinSearch

open GoLean GoLean.GoCore

/-- The frontend's lowering of the binsearch subject, verbatim
(`scripts/check-golden` pins it). -/
def searchLowered : Program :=
  { typeDefs := #[({ key := "struct{}" }, GoLean.GoCore.TypeDef.struct #[])],
    funcs := #[{ id := { key := "search" },
                 args := #[{ id := "s",
                             typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                           { id := "target", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "lo", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                                 GoLean.GoCore.Stmt.initialization
                                   { id := "hi", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                                 GoLean.GoCore.Stmt.assignMany
                                   #[GoLean.GoCore.Assignee.var "lo", GoLean.GoCore.Assignee.var "hi"]
                                   #[GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int),
                                     GoLean.GoCore.Expr.length
                                       (GoLean.GoCore.Expr.var "s")
                                       (some (GoLean.GoCore.Ty.slice
                                          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))))]],
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
                                         (GoLean.GoCore.Expr.lessCmp
                                           (GoLean.GoCore.Expr.var "lo")
                                           (GoLean.GoCore.Expr.var "hi"))
                                         (GoLean.GoCore.Stmt.seqn #[])
                                         (GoLean.GoCore.Stmt.breakStmt),
                                       GoLean.GoCore.Stmt.block
                                         #[]
                                         #[GoLean.GoCore.Stmt.seqn
                                             #[GoLean.GoCore.Stmt.initialization
                                                 { id := "mid", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                                               GoLean.GoCore.Stmt.assign
                                                 (GoLean.GoCore.Assignee.var "mid")
                                                 (GoLean.GoCore.Expr.div
                                                   (GoLean.GoCore.Expr.add
                                                     (GoLean.GoCore.Expr.var "lo")
                                                     (GoLean.GoCore.Expr.var "hi"))
                                                   (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int)))],
                                           GoLean.GoCore.Stmt.ifThenElse
                                             (GoLean.GoCore.Expr.lessCmp
                                               (GoLean.GoCore.Expr.indexGet
                                                 (GoLean.GoCore.Expr.var "s")
                                                 (GoLean.GoCore.Expr.var "mid"))
                                               (GoLean.GoCore.Expr.var "target"))
                                             (GoLean.GoCore.Stmt.block
                                               #[]
                                               #[GoLean.GoCore.Stmt.seqn
                                                   #[GoLean.GoCore.Stmt.assign
                                                       (GoLean.GoCore.Assignee.var "lo")
                                                       (GoLean.GoCore.Expr.add
                                                         (GoLean.GoCore.Expr.var "mid")
                                                         (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))]])
                                             (GoLean.GoCore.Stmt.block
                                               #[]
                                               #[GoLean.GoCore.Stmt.seqn
                                                   #[GoLean.GoCore.Stmt.assign
                                                       (GoLean.GoCore.Assignee.var "hi")
                                                       (GoLean.GoCore.Expr.var "mid")]])]])],
                             GoLean.GoCore.Stmt.ifThenElse
                               (GoLean.GoCore.Expr.and
                                 (GoLean.GoCore.Expr.lessCmp
                                   (GoLean.GoCore.Expr.var "lo")
                                   (GoLean.GoCore.Expr.length
                                     (GoLean.GoCore.Expr.var "s")
                                     (some (GoLean.GoCore.Ty.slice
                                        (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))))))
                                 (GoLean.GoCore.Expr.eqCmp
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                   (GoLean.GoCore.Expr.indexGet
                                     (GoLean.GoCore.Expr.var "s")
                                     (GoLean.GoCore.Expr.var "lo"))
                                   (GoLean.GoCore.Expr.var "target")))
                               (GoLean.GoCore.Stmt.block
                                 #[]
                                 #[GoLean.GoCore.Stmt.seqn
                                     #[GoLean.GoCore.Stmt.assign
                                         (GoLean.GoCore.Assignee.var "$res0")
                                         (GoLean.GoCore.Expr.var "lo"),
                                       GoLean.GoCore.Stmt.returnStmt]])
                               (GoLean.GoCore.Stmt.seqn #[]),
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.intLit (-1) (GoLean.GoCore.IntKind.int)),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "searchFour" },
                 args := #[{ id := "a", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "b", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "c", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "d", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "target", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
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
                                   { id := "$c1", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c1"]
                                   { key := "search" }
                                   #[GoLean.GoCore.Expr.var "s", GoLean.GoCore.Expr.var "target"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "$c1"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "searchOne" },
                 args := #[{ id := "a", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "target", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
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
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c3", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c3"]
                                   { key := "search" }
                                   #[GoLean.GoCore.Expr.var "s", GoLean.GoCore.Expr.var "target"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "$c3"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "searchEmpty" },
                 args := #[{ id := "target", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
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
                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))
                                   (some (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "s",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "s")
                                   (GoLean.GoCore.Expr.var "$c4")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c5", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c5"]
                                   { key := "search" }
                                   #[GoLean.GoCore.Expr.var "s", GoLean.GoCore.Expr.var "target"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "$c5"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false }],
    methods := #[],
    globals := #[],
    methodSets := #[{ key := "struct{}", coverage := GoLean.GoCore.MethodSetCoverage.full }] }

end GoLean.Examples.BinSearch
