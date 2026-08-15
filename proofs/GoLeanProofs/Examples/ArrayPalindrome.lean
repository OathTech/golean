import GoLeanProofs.Examples.ArrayPalindromeProgram

/-!
# ArrayPalindrome — the `palin` example (Gallery Campaign G1, guardrails wave)

**STATUS: GUARDRAILS ONLY — no headline theorem yet.** This root carries
exactly the corpus half of the G1 checklist: the pinned lowering (via
`ArrayPalindromeProgram`, itself pinned by `scripts/check-golden` against
`baselines/golden/palin-lowered.repr`) and the named harness
transcription below, tied to that lowering by `rfl`. The proof lane that
adopts this example states its headline HERE, in this root, so the
aggregator's `import GoLeanProofs.Examples.ArrayPalindrome` reaches it by name
(the C-H4/C-H5 shape, adopted from birth).

Go source: `Corpus/coverage/exec/examples/palin/main.go`,
differentially green against `go run` — those rows are the guardrail
that pins the target BEFORE the proof exists.

The harness `Func` below is EXTRACTED from the pinned repr rather than
hand-written, so `palinHarnessRFunc_pin` checks a transcription that is
byte-derived from the lowering. A proof lane may restate it in the
readable dot-notation form; the pin must keep holding by `rfl`.
-/

namespace GoLean.Examples.ArrayPalindrome

open GoLean GoLean.GoCore

/-- The harness `Func`, verbatim from the pinned lowering (the pin below
ties it by `rfl`). -/
def palinHarnessRFunc : Func :=
{ id := { key := "palin_harness_r" },
  args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
            { id := "seed", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
  results := #[{ id := "$res0",
                 typ := GoLean.GoCore.Ty.array 8 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
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
                    (GoLean.GoCore.Expr.var "n")
                    none],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "s",
                      typ := GoLean.GoCore.Ty.slice
                               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "s")
                    (GoLean.GoCore.Expr.var "$c8")],
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
                                        (GoLean.GoCore.Expr.mod
                                          (GoLean.GoCore.Expr.var "i")
                                          (GoLean.GoCore.Expr.intLit
                                            2
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
                    { id := "v", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "v"]
                    { key := "isPalindrome" }
                    #[GoLean.GoCore.Expr.var "s"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res0")
                    (GoLean.GoCore.Expr.var "pre"),
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res1")
                    (GoLean.GoCore.Expr.var "v"),
                  GoLean.GoCore.Stmt.returnStmt]],
  variadic := false,
  wrapper := false }

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem palinHarnessRFunc_pin :
    findFunctionIn? palinLowered.funcs ⟨"palin_harness_r"⟩
    = some palinHarnessRFunc := rfl

end GoLean.Examples.ArrayPalindrome
