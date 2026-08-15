import GoLeanProofs.Examples.PowModProgram

/-!
# PowMod — the `powmod` example (Gallery Campaign G1, guardrails wave)

**STATUS: GUARDRAILS ONLY — no headline theorem yet.** This root carries
exactly the corpus half of the G1 checklist: the pinned lowering (via
`PowModProgram`, itself pinned by `scripts/check-golden` against
`baselines/golden/powmod-lowered.repr`) and the named harness
transcription below, tied to that lowering by `rfl`. The proof lane that
adopts this example states its headline HERE, in this root, so the
aggregator's `import GoLeanProofs.Examples.PowMod` reaches it by name
(the C-H4/C-H5 shape, adopted from birth).

Go source: `Corpus/coverage/exec/examples/powmod/main.go`,
differentially green against `go run` — those rows are the guardrail
that pins the target BEFORE the proof exists.

The harness `Func` below is EXTRACTED from the pinned repr rather than
hand-written, so `powmodHarnessFunc_pin` checks a transcription that is
byte-derived from the lowering. A proof lane may restate it in the
readable dot-notation form; the pin must keep holding by `rfl`.
-/

namespace GoLean.Examples.PowMod

open GoLean GoLean.GoCore

/-- The harness `Func`, verbatim from the pinned lowering (the pin below
ties it by `rfl`). -/
def powmodHarnessFunc : Func :=
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
  wrapper := false }

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem powmodHarnessFunc_pin :
    findFunctionIn? powmodLowered.funcs ⟨"powmod_harness"⟩
    = some powmodHarnessFunc := rfl

end GoLean.Examples.PowMod
