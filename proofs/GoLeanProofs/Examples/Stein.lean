import GoLeanProofs.Examples.SteinProgram
import GoLeanProofs.Examples.Stein.Run
import GoLeanProofs.EntryEq
import GoLeanProofs.FuelMeasure

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

open GoLean.GoCore.Machine GoLean.Surface GoLean.SliceMem

/-- The root's transcription and the run module's local copy are the
same `Func` (both are `rfl`-pinned to the one pinned lowering; the run
module cannot import this root, so it carries its own). -/
theorem steinHarnessFunc_eq_run : steinHarnessFunc = steinHarnessFuncRun := rfl

/-! ## The user-facing headline

Machine walk: `Examples/Stein/Run.lean` (`stein_runs` — footprint-style
segments, phase inductions pinned one-to-one against the pure branch
equations). Mathematics: `Examples/Stein/Pure.lean`
(`steinSpec_eq_gcd` — Stein's three phases as pure functions, proven
equal to `Nat.gcd` from core Lean, no Mathlib). They meet in
`stein_runs`'s delivered value; this root only folds the entry
equation. -/

/-- **THE HEADLINE (§11 harness form, S2 SCALAR)**: for every `a, b` in
the full uint64 × uint64 domain, running `stein_harness(a, b)` — binary
GCD in its NATURAL Go form, whose `for isEven(a) && isEven(b)` guard is
a call in a short-circuit operand riding extension E3's normalization —
through the machine's native function entry completes normally past ONE
fuel bound, at every nondeterminism-choice stream, and returns exactly
`Nat.gcd a b`.

Honesty clauses, recorded rather than hidden:

* **The value is EXACT on the full domain** — no wrapping clause exists
  to state (the `gcd` example's collapse): a gcd never exceeds its
  arguments, the subtract loop never wraps (`b - a` runs after the
  swap), and the final `a << shift` reassembles exactly the factors the
  first loop took apart, all below `2^64`.
* **The specification is `Nat.gcd`** — Lean's textbook gcd. The
  algorithm's own shape lives in the proof-side spec functions
  (`commonTwos`/`stripTwos`/`steinSub`/`steinSpec`, `Stein/Pure.lean`)
  and crosses into the statement through ONE theorem,
  `steinSpec_eq_gcd`.
* **The bound is a BOUND, not a measurement**: `steinFuel a b =
  600 + 480·(a + b)`, affine in the loops' shared strictly-decreasing
  measure `a + b`; the measured `(12, 18)` run takes 896 steps against
  a bound of 15,000, and the early exits measure 57/66 steps.
* **`∀ ch` is vacuous here and stated anyway.** The harness consumes no
  nondeterminism choice; the quantifier records that.
* **Machine idealization** as in the other entries: entry from an empty
  heap, an unbounded heap, allocation always succeeds — each loop
  iteration allocates fresh condPre temps and a 2-cell `isEven` frame
  that are never reclaimed, and nothing bounds that but the iteration
  count itself. -/
theorem stein_ok (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel steinLowered.typeDefs.toList
          steinLowered.funcs steinHarnessFunc
          #[.int (a : Int) .uint64, .int (b : Int) .uint64]
          steinLowered.methods ch
        = .ok { values := #[.int ((Nat.gcd a b : Nat) : Int) .uint64] } := by
  refine ⟨steinFuel a b, fun fuel hfuel ch => ?_⟩
  rw [steinHarnessFunc_eq_run, stein_entry_eq (a : Int) (b : Int) fuel ch,
    unorm_nat_of_lt ha, unorm_nat_of_lt hb]
  obtain ⟨k, σf, hk, hrun, hread⟩ := stein_runs a b ha hb ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [hfold, runConfig_next_stop]
  simp only [bind, Except.bind, pure, Except.pure, hread]

/-- **The D1 run-conditioned twin**: ANY successful completion of the
harness entry, at any fuel and any choice stream, returns exactly
`Nat.gcd a b` — derived from `stein_ok` through the shared
`harness_readout_of_total` bridge; nothing is re-proven. -/
theorem stein_readout (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ∀ (fuel : Nat) (ch : Choices) (r : Result),
      runFunctionWithContextM fuel steinLowered.typeDefs.toList
          steinLowered.funcs steinHarnessFunc
          #[.int (a : Int) .uint64, .int (b : Int) .uint64]
          steinLowered.methods ch
        = .ok r →
      r = { values := #[.int ((Nat.gcd a b : Nat) : Int) .uint64] } :=
  harness_readout_of_total (stein_ok a b ha hb)

end GoLean.Examples.Stein
