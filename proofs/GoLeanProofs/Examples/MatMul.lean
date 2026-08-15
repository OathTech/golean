import GoLeanProofs.Examples.MatMulProgram

/-!
# MatMul — the `matmul` example (Gallery Campaign G1, guardrails wave)

**STATUS: GUARDRAILS ONLY — no headline theorem yet.** This root carries
exactly the corpus half of the G1 checklist: the pinned lowering (via
`MatMulProgram`, itself pinned by `scripts/check-golden` against
`baselines/golden/matmul-lowered.repr`) and the named harness
transcription below, tied to that lowering by `rfl`. The proof lane that
adopts this example states its headline HERE, in this root, so the
aggregator's `import GoLeanProofs.Examples.MatMul` reaches it by name
(the C-H4/C-H5 shape, adopted from birth).

Go source: `Corpus/coverage/exec/examples/matmul/main.go`,
differentially green against `go run` — those rows are the guardrail
that pins the target BEFORE the proof exists.

The harness `Func` below is EXTRACTED from the pinned repr rather than
hand-written, so `matmulHarnessRFunc_pin` checks a transcription that is
byte-derived from the lowering. A proof lane may restate it in the
readable dot-notation form; the pin must keep holding by `rfl`.
-/

namespace GoLean.Examples.MatMul

open GoLean GoLean.GoCore

/-- The harness `Func`, verbatim from the pinned lowering (the pin below
ties it by `rfl`). -/
def matmulHarnessRFunc : Func :=
{ id := { key := "matmul_harness_r" },
  args := #[{ id := "seed", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
  results := #[{ id := "$res0",
                 typ := GoLean.GoCore.Ty.array
                          3
                          (GoLean.GoCore.Ty.array
                            3
                            (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) },
               { id := "$res1",
                 typ := GoLean.GoCore.Ty.array
                          3
                          (GoLean.GoCore.Ty.array
                            3
                            (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) },
               { id := "$res2",
                 typ := GoLean.GoCore.Ty.array
                          3
                          (GoLean.GoCore.Ty.array
                            3
                            (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) }],
  body := GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "a",
                      typ := GoLean.GoCore.Ty.array
                               3
                               (GoLean.GoCore.Ty.array
                                 3
                                 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "a"]
                    { key := "seedMat" }
                    #[GoLean.GoCore.Expr.var "seed"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "b",
                      typ := GoLean.GoCore.Ty.array
                               3
                               (GoLean.GoCore.Ty.array
                                 3
                                 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "b"]
                    { key := "seedMat" }
                    #[GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c8",
                      typ := GoLean.GoCore.Ty.array
                               3
                               (GoLean.GoCore.Ty.array
                                 3
                                 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c8"]
                    { key := "matMul" }
                    #[GoLean.GoCore.Expr.var "a", GoLean.GoCore.Expr.var "b"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res0")
                    (GoLean.GoCore.Expr.var "a"),
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res1")
                    (GoLean.GoCore.Expr.var "b"),
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res2")
                    (GoLean.GoCore.Expr.var "$c8"),
                  GoLean.GoCore.Stmt.returnStmt]],
  variadic := false,
  wrapper := false }

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem matmulHarnessRFunc_pin :
    findFunctionIn? matmulLowered.funcs ⟨"matmul_harness_r"⟩
    = some matmulHarnessRFunc := rfl

end GoLean.Examples.MatMul
