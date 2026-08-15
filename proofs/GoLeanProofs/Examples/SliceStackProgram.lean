import GoLean.GoCore.Syntax

/-!
# The `stack` example — the frontend's lowering, pinned
(gallery campaign G1, guardrails wave, 2026-08-15)

`stackLowered` is the native frontend's ACTUAL lowering of the
canonical corpus source (`Corpus/coverage/exec/examples/stack/main.go`,
differentially green against `go run`), pinned by `scripts/check-golden`
against `baselines/golden/stack-lowered.repr`. THIS DEF IS GENERATED from
that repr (the literal below IS the repr text, byte-identical under
`repr` — the same both-links story as the other golden pins);
regenerate rather than hand-edit.

Pure syntax module: no Iris import, safe for statement-side use.
-/

namespace GoLean.Examples.SliceStack

open GoLean GoLean.GoCore

/-- The frontend's lowering of the `stack` subject, verbatim
(`scripts/check-golden` pins it). -/
def stackLowered : Program :=
  { typeDefs := #[({ key := "struct{}" }, GoLean.GoCore.TypeDef.struct #[])],
    funcs := #[{ id := { key := "push" },
                 args := #[{ id := "s",
                             typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                           { id := "v", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0",
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
                                   (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                                   (some (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr
                                     (GoLean.GoCore.Expr.indexAddr
                                       (GoLean.GoCore.Expr.var "$c0")
                                       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                                   (GoLean.GoCore.Expr.var "v")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c1",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.appendSlice
                                   (GoLean.GoCore.Assignee.var "$c1")
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                   (GoLean.GoCore.Expr.var "s")
                                   (GoLean.GoCore.Expr.var "$c0")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "$c1"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "pop" },
                 args := #[{ id := "s",
                             typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) }],
                 results := #[{ id := "$res0",
                                typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                              { id := "$res1", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "v", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "v")
                                   (GoLean.GoCore.Expr.indexGet
                                     (GoLean.GoCore.Expr.var "s")
                                     (GoLean.GoCore.Expr.sub
                                       (GoLean.GoCore.Expr.length
                                         (GoLean.GoCore.Expr.var "s")
                                         (some (GoLean.GoCore.Ty.slice
                                            (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))))
                                       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.slice
                                     (GoLean.GoCore.Expr.var "s")
                                     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))
                                     (GoLean.GoCore.Expr.sub
                                       (GoLean.GoCore.Expr.length
                                         (GoLean.GoCore.Expr.var "s")
                                         (some (GoLean.GoCore.Ty.slice
                                            (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))))
                                       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))
                                     none),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res1")
                                   (GoLean.GoCore.Expr.var "v"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "peek" },
                 args := #[{ id := "s",
                             typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.indexGet
                                     (GoLean.GoCore.Expr.var "s")
                                     (GoLean.GoCore.Expr.sub
                                       (GoLean.GoCore.Expr.length
                                         (GoLean.GoCore.Expr.var "s")
                                         (some (GoLean.GoCore.Ty.slice
                                            (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))))
                                       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "size" },
                 args := #[{ id := "s",
                             typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.convert
                                     (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                     (GoLean.GoCore.Expr.length
                                       (GoLean.GoCore.Expr.var "s")
                                       (some (GoLean.GoCore.Ty.slice
                                          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))))),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "pushPopThree" },
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
                                   { id := "$c2",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.makeSlice
                                   (GoLean.GoCore.Assignee.var "$c2")
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
                                   (GoLean.GoCore.Expr.var "$c2")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "s"]
                                   { key := "push" }
                                   #[GoLean.GoCore.Expr.var "s", GoLean.GoCore.Expr.var "a"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "s"]
                                   { key := "push" }
                                   #[GoLean.GoCore.Expr.var "s", GoLean.GoCore.Expr.var "b"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "s"]
                                   { key := "push" }
                                   #[GoLean.GoCore.Expr.var "s", GoLean.GoCore.Expr.var "c"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "x", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.initialization
                                   { id := "y", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.initialization
                                   { id := "z", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "s", GoLean.GoCore.Assignee.var "x"]
                                   { key := "pop" }
                                   #[GoLean.GoCore.Expr.var "s"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "s", GoLean.GoCore.Assignee.var "y"]
                                   { key := "pop" }
                                   #[GoLean.GoCore.Expr.var "s"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$cr0",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$cr0", GoLean.GoCore.Assignee.var "z"]
                                   { key := "pop" }
                                   #[GoLean.GoCore.Expr.var "s"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "x"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res1")
                                   (GoLean.GoCore.Expr.var "y"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res2")
                                   (GoLean.GoCore.Expr.var "z"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "pushPeek" },
                 args := #[{ id := "a", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "b", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
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
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "s"]
                                   { key := "push" }
                                   #[GoLean.GoCore.Expr.var "s", GoLean.GoCore.Expr.var "a"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "s"]
                                   { key := "push" }
                                   #[GoLean.GoCore.Expr.var "s", GoLean.GoCore.Expr.var "b"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c4", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c4"]
                                   { key := "peek" }
                                   #[GoLean.GoCore.Expr.var "s"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "$c4"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "emptySize" },
                 args := #[],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c5",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.makeSlice
                                   (GoLean.GoCore.Assignee.var "$c5")
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
                                   (GoLean.GoCore.Expr.var "$c5")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c6", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c6"]
                                   { key := "size" }
                                   #[GoLean.GoCore.Expr.var "s"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "$c6"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "stack_harness_r" },
                 args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "seed", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                           { id := "k", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                 results := #[{ id := "$res0",
                                typ := GoLean.GoCore.Ty.array 8 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                              { id := "$res1",
                                typ := GoLean.GoCore.Ty.array 8 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                              { id := "$res2", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
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
                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))
                                   (some (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "s",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "s")
                                   (GoLean.GoCore.Expr.var "$c7")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "pushed",
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
                                                 #[GoLean.GoCore.Stmt.initialization
                                                     { id := "v",
                                                       typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                                   GoLean.GoCore.Stmt.assign
                                                     (GoLean.GoCore.Assignee.var "v")
                                                     (GoLean.GoCore.Expr.add
                                                       (GoLean.GoCore.Expr.var "seed")
                                                       (GoLean.GoCore.Expr.var "i"))],
                                               GoLean.GoCore.Stmt.seqn
                                                 #[GoLean.GoCore.Stmt.call
                                                     #[GoLean.GoCore.Assignee.var "s"]
                                                     { key := "push" }
                                                     #[GoLean.GoCore.Expr.var "s", GoLean.GoCore.Expr.var "v"]],
                                               GoLean.GoCore.Stmt.seqn
                                                 #[GoLean.GoCore.Stmt.assign
                                                     (GoLean.GoCore.Assignee.addr
                                                       (GoLean.GoCore.Expr.indexAddr
                                                         (GoLean.GoCore.Expr.ref "pushed")
                                                         (GoLean.GoCore.Expr.var "i")))
                                                     (GoLean.GoCore.Expr.var "v")]]])]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "m", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "m") (GoLean.GoCore.Expr.var "k")],
                             GoLean.GoCore.Stmt.ifThenElse
                               (GoLean.GoCore.Expr.lessCmp (GoLean.GoCore.Expr.var "n") (GoLean.GoCore.Expr.var "m"))
                               (GoLean.GoCore.Stmt.block
                                 #[]
                                 #[GoLean.GoCore.Stmt.seqn
                                     #[GoLean.GoCore.Stmt.assign
                                         (GoLean.GoCore.Assignee.var "m")
                                         (GoLean.GoCore.Expr.var "n")]])
                               (GoLean.GoCore.Stmt.seqn #[]),
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "popped",
                                     typ := GoLean.GoCore.Ty.array
                                              8
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) }],
                             GoLean.GoCore.Stmt.block
                               #[]
                               #[GoLean.GoCore.Stmt.seqn
                                   #[GoLean.GoCore.Stmt.initialization
                                       { id := "j", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
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
                                                 (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)))),
                                           GoLean.GoCore.Stmt.seqn #[],
                                           GoLean.GoCore.Stmt.ifThenElse
                                             (GoLean.GoCore.Expr.lessCmp
                                               (GoLean.GoCore.Expr.var "j")
                                               (GoLean.GoCore.Expr.var "m"))
                                             (GoLean.GoCore.Stmt.seqn #[])
                                             (GoLean.GoCore.Stmt.breakStmt),
                                           GoLean.GoCore.Stmt.block
                                             #[]
                                             #[GoLean.GoCore.Stmt.seqn
                                                 #[GoLean.GoCore.Stmt.initialization
                                                     { id := "v",
                                                       typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                                               GoLean.GoCore.Stmt.seqn
                                                 #[GoLean.GoCore.Stmt.call
                                                     #[GoLean.GoCore.Assignee.var "s", GoLean.GoCore.Assignee.var "v"]
                                                     { key := "pop" }
                                                     #[GoLean.GoCore.Expr.var "s"]],
                                               GoLean.GoCore.Stmt.seqn
                                                 #[GoLean.GoCore.Stmt.assign
                                                     (GoLean.GoCore.Assignee.addr
                                                       (GoLean.GoCore.Expr.indexAddr
                                                         (GoLean.GoCore.Expr.ref "popped")
                                                         (GoLean.GoCore.Expr.var "j")))
                                                     (GoLean.GoCore.Expr.var "v")]]])]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c8", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c8"]
                                   { key := "size" }
                                   #[GoLean.GoCore.Expr.var "s"]],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "pushed"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res1")
                                   (GoLean.GoCore.Expr.var "popped"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res2")
                                   (GoLean.GoCore.Expr.var "$c8"),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false }],
    methods := #[],
    globals := #[],
    methodSets := #[{ key := "struct{}", coverage := GoLean.GoCore.MethodSetCoverage.full }] }

end GoLean.Examples.SliceStack
