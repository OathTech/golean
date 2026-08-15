import GoLeanProofs.Examples.SteinProgram

/-!
# Stein — the `stein` example (Gallery Campaign G1 + G2 extension E3)

This root carries the pinned lowering (via `SteinProgram`, itself pinned
by `scripts/check-golden` against `baselines/golden/stein-lowered.repr`)
and the named harness transcription below, tied to that lowering by
`rfl`. The headline is stated HERE, in this root, so the aggregator's
`import GoLeanProofs.Examples.Stein` reaches it by name (the C-H4/C-H5
shape, adopted from birth).

Go source: `Corpus/coverage/exec/examples/stein/main.go`.

**HISTORY — this example existed BLOCKED, and the block was the point**
(guardrails wave, 2026-08-15): binary GCD in its natural Go form guards
the shared-factor loop with `for isEven(a) && isEven(b)`, a call in a
short-circuit operand, which the frontend quarantined fail-closed
(`steinGCD` lowered to `Stmt.unsupported` carrying the reason verbatim);
all nine corpus rows were RED at stage `frontend-export` as the pinned
guardrail for extension E3. **E3 is now BUILT** (same date; the fidelity
argument and the build record are in `docs/gallery-campaign-log/g2.md`):
the frontend normalizes an effectful short-circuit RHS to the spec's own
conditional rewrite, `steinGCD` lowers fully (see `SteinProgram`, whose
per-iteration `$c` machinery in each loop's condPre IS that
normalization), and all nine rows plus the 19 short-circuit guardrail
rows are differentially green against `go run`.

The harness `Func` below is EXTRACTED from the pinned repr rather than
hand-written, so `steinHarnessFunc_pin` checks a transcription that is
byte-derived from the lowering.
-/

namespace GoLean.Examples.Stein

open GoLean GoLean.GoCore

/-- The harness `Func`, verbatim from the pinned lowering (the pin below
ties it by `rfl`). -/
def steinHarnessFunc : Func :=
{ id := { key := "stein_harness" },
  args := #[{ id := "a", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
            { id := "b", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
  results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
  body := GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "r", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "r"]
                    { key := "steinGCD" }
                    #[GoLean.GoCore.Expr.var "a", GoLean.GoCore.Expr.var "b"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res0")
                    (GoLean.GoCore.Expr.var "r"),
                  GoLean.GoCore.Stmt.returnStmt]],
  variadic := false,
  wrapper := false }

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem steinHarnessFunc_pin :
    findFunctionIn? steinLowered.funcs ⟨"stein_harness"⟩
    = some steinHarnessFunc := rfl

end GoLean.Examples.Stein
