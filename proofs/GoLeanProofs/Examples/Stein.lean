import GoLeanProofs.Examples.SteinProgram

/-!
# Stein — the `stein` example (Gallery Campaign G1, guardrails wave)

**STATUS: GUARDRAILS ONLY — no headline theorem yet.** This root carries
exactly the corpus half of the G1 checklist: the pinned lowering (via
`SteinProgram`, itself pinned by `scripts/check-golden` against
`baselines/golden/stein-lowered.repr`) and the named harness
transcription below, tied to that lowering by `rfl`. The proof lane that
adopts this example states its headline HERE, in this root, so the
aggregator's `import GoLeanProofs.Examples.Stein` reaches it by name
(the C-H4/C-H5 shape, adopted from birth).

Go source: `Corpus/coverage/exec/examples/stein/main.go`.

**THIS EXAMPLE IS BLOCKED, AND THE BLOCK IS THE POINT.** All nine of its
corpus rows are RED at stage `frontend-export`, every one with the same
verbatim classification:

```
"status":"unsupported"
"normalizing frontend-quarantined: call/allocation in short-circuit
 operand (would change evaluation order)"
```

Stein's algorithm written in its NATURAL Go form guards the shared-factor
loop with `for isEven(a) && isEven(b)`, and a CALL inside a short-circuit
operand is exactly what the frontend quarantines. The Go oracle computes
the right answer on every row (cross-checked against the `gcd` example's
Euclid on all seven argument pairs plus a 100,000-pair sweep, zero
mismatches); the machine refuses, visibly.

The refusal is fail-closed, per-declaration, and legible in the pinned
lowering itself: `steinGCD` lowers to `Stmt.unsupported` with the reason
carried verbatim, and its parameters to `Ty.unsupported`. The harness
below is fully lowered and calls into that stub — which is why the rows
are red rather than quietly wrong.

**No headline is provable here until extension E3 lands** (calls in
short-circuit operands; see `docs/gallery-campaign-log/g2.md`, where this
example is E3's recorded consumer-to-be). The rows were landed anyway,
BEFORE the extension, because that is what guardrails-first means: E3's
target behaviour is now pinned by cases that fail for a stated reason, so
the extension cannot land and silently change what Stein computes. When it
lands, `baselines/golden/stein-lowered.repr` DRIFTS — deliberately, with
its reason, in the same commit.

The harness `Func` below is EXTRACTED from the pinned repr rather than
hand-written, so `steinHarnessFunc_pin` checks a transcription that is
byte-derived from the lowering. A proof lane may restate it in the
readable dot-notation form; the pin must keep holding by `rfl`.
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
