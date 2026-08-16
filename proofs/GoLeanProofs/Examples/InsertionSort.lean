import GoLeanProofs.Examples.InsertionSort.Pure
import GoLeanProofs.Examples.InsertionSort.Canon
import GoLeanProofs.Examples.InsertionSort.PassFrame
import GoLeanProofs.Examples.InsertionSort.Canonical
import GoLeanProofs.Examples.InsertionSort.Family
import GoLeanProofs.Examples.InsertionSort.Setup
import GoLeanProofs.Examples.InsertionSort.Subject
import GoLeanProofs.Examples.InsertionSort.Scan
import GoLeanProofs.Examples.InsertionSort.Rebuild
import GoLeanProofs.Examples.InsertionSort.Count
import GoLeanProofs.Examples.InsertionSort.Run


/-!
# Verified example: in-place insertion sort — NESTED loops
(verified-examples slice 2c, 2026-08-13)

The nested-loop exemplar of the §9 memory-input form (design note
`docs/2026-08-12_example-spec-form.md` §9): the Go program is the
canonical corpus source `Corpus/coverage/exec/examples/isort/main.go`
(differentially green against `go run`, 8 oracle rows incl. duplicates
and already/reverse-sorted inputs); `isortLowered` is its pinned
frontend lowering (`scripts/check-golden`).

**Harness-ruling status (2026-08-13, design note §11 — RESTATED,
COMPLETE).** `isort_ok` is now the §11 three-phase harness headline
over `runFunctionWithContextM` (`isort_harness(n, seed)`: setup builds
the wrapped multiplicative family `s[i] = seed*(i+1)`; the call under
test `insertionSort(s)`; the TEST PHASE — sortedness scan plus the
count-based permutation check against the rebuilt family, IN GO,
inside the verified footprint — folds into the returned verdict
`ok ∈ {0,1}`; headline: verdict = 1, `isort_readout` the D1 twin).
The former memory-quantified pair is RENAMED to
`isort_framed`/`isort_framed_readout` (the gcd/minmax/binsearch/
reverse precedent) and kept green as the proof-side supporting layer —
it remains the strongest ∀xs claim shipped. Fuel bound of the
headline: `N = (92·n+160)·n + (110·n+220)·n + 285·n + 505` (quadratic:
the count loops are O(n²)).

**Harness address layout (probe-verified against the full n=4 seed=3
trace, `.tmp/his-trace1.txt`, and re-checked by every `rfl` segment)**:
0 = `n`, 1 = `seed`, 2 = the harness `$res0` (the VERDICT cell),
3 = `$c4`, 4 = the `s` BACKING, 5 = `s`, 6/7 = the setup
`i`/`$forFirst`; the subject frame 8 = the `s` param, 9 = the subject
`i`, 10 = the outer `$forFirst`, per-pass `j`/`$forFirst` pairs from
11 (2 cells/pass); then the test phase: 11+2(n-1)… in TRUE addresses —
canonically (all subject passes rebased into the frame): 11 = `ok`,
12/13 = the scan `i`/flag, 14 = `$c5`, 15 = the `t` BACKING, 16 = `t`,
17/18 = the rebuild `i`/flag, 19/20 = the count `i`/flag, and the
count pass cells TIGHT at 21 = `cs`, 22 = `ct`, 23 = `j`, 24 = flag
(4 cells/pass, retired by the second rebase layer).

**How the restatement runs (the recipe as executed, deviations
recorded)**: the subject phase is re-derived concretely at the harness
placement under the harness continuation (Reverse's route (b); the
canonical segments' step counts carried over VERBATIM — same
statements, same machine paths), with the pass frame-rebase layer
re-instantiated at threshold 11 (`ρ11`/`rebaseSim11`, retire 2). The
remainder (scan → rebuild → count) is proven as ONE canonical run from
the post-subject 11-cell state and transferred to the true
(subject-garbage-laden) placement in a single `transfer_seg11`
application at the end — the scan and rebuild allocate only
per-phase, so their segments are address-concrete; the count loops
carry the SECOND frame-rebase layer at threshold 21
(`ρ21`/`rebaseSim21`, retire 4/pass), exactly as the pickup plan
predicted. One deviation from the plan's letter: the scan loop's exit
counter is existential (`mf`) rather than pinned to `n` — the scan
starts at `i = 1`, so at `n = 0` it exits at `1 ≠ n`; the parked value
is inert and every downstream state carries it as a parameter
(`sciv`). The rebuild loop re-instantiates the setup induction at the
`t` placement (the segments could not be shared across placements —
`rfl` segments need address-concrete envs — so they are re-derived;
flagged in the worker report as the expected cost). The count inner
loop's accumulator invariant bridges to `List.count` via the in-module
`cntSpec` and closes by `sortSpec_count`.

The support corollaries (`sortSpec_sorted`, `sortSpec_count`,
`sortSpec_length`) make the "sorted permutation" reading of the
Go-computed verdict a theorem, not a naming convention.

**The nested-loop composition (route of record, with one machine-forced
deviation from the arc design).** The design called for two plain
nested strong inductions on the direct machine-step route (the
fuel-measure RULE is not needed on this route — that sugar gap remains
the WP route's, none of which is consumed here). Both inductions are
below, exactly as designed: the INNER induction (`innerLoop`, measure
`j` descending, invariant `bubbleState`) and the OUTER induction
(`isortLoop`, measure `n - (m+1)`, invariant `sortPrefix`). The
deviation: **the outer induction composes its per-pass segments through
the executable frame theorem** (`stepFnIter_sim` at a per-pass shift
renaming `ρsh (2m)`, plus a frame-REBASE step) rather than by literal
state reuse, because the machine allocates a FRESH `j`/`$forFirst` cell
pair on every outer pass (the inner `for`'s declarations re-enter their
block each pass; `nextAddr` grows by 2 per pass and the dead cells stay
in the heap — probe-verified). Reverse-style fixed-address segments
therefore cannot describe the outer loop head at a single placement;
instead each pass is proven ONCE at a tight 6-cell canonical placement
and transferred to the true (garbage-laden) placement by the frame
theorem, with the retired `j`/`$forFirst` cells REBASED into the frame
between passes (`rebaseSim`). The garbage cells are semantically inert;
the frame theorem is precisely the tool that says so. Nothing is
re-run at any framed placement.

The `&&` lowering shape (probe finding, load-bearing for §9d honesty):
`Expr.and` evaluates the left conjunct into an `.andK` continuation;
`false` short-circuits — delivering `.bool false` straight to the `if`
continuation WITHOUT evaluating the right conjunct, so at `j = 0` the
`s[j-1]` read never happens (Go's laziness, exactly). The proof's inner
exit at `j = 0` goes through that short-circuit arm.

Statement deltas against the arc-design block: NONE beyond the deltas
already in the design (`hlen : xs.length < 2 ^ 63` — Go's own `int`
domain: with completion in the statement, the driver's `len` literal
wraps negative past `2^63` and the slice-expression bounds check
panics, so the claim as drafted would be false there).

Scope honesty (the charter's two-questions separation): usability
evidence only — never machine-hardening evidence.
-/

/-!
## Module layout (per-phase split, examples phase-2 slice 0 lever 2,
2026-08-14)

This file holds the user-facing §11 harness statements — `isort_ok` and
`isort_readout`, the designated headlines, are declared HERE, so
`import GoLeanProofs.Examples.InsertionSort` reaches them directly —
and aggregates every phase shard. The proof phases live in
`GoLeanProofs.Examples.InsertionSort.*`, imported above at their
MEASURED dependencies (G4.2 replaced the authoring-order chain; max
depth 11 → 8).

**On the split's "moved VERBATIM" claim** (C-M5, mechanized 2026-08-15
rather than left an assertion). The claim was made by `6256228d` and
**it was TRUE when made**: a comparison of every declaration BLOCK
(statement PLUS proof) in the pre-split module (`6256228d^`) against
the shards at `6256228d` finds **318 of 318 byte-identical, 0
differing, 0 absent**
(measured by the g4 verbatim-check script (a scratch artifact under `artifacts/`, gitignored and now gone; its method — compare every declaration BLOCK, statement plus proof, modifiers normalised, by name between two revisions — is described in `docs/gallery-campaign-log/g4.md` § C-M5 and is re-implementable from that description)). It is **no longer true
of the CURRENT tree**: measured against today, 311 of those 318 are
still byte-identical, 5 differ and 2 are absent (`isortHarnessFunc` and
`iharness_entry_eq` moved to `Examples/Targets.lean` in the designation
hoist). All of it is later, intended work — not drift from the split.

| shard | phase |
|---|---|
| `Pure` | the program-side statement vocabulary, the pure spec layer, `sortPrefix`, `bubbleState` |
| `Canon` | canonical-placement configurations, the raw run segments, the cleaned discharge facts, the inner induction and one composed pass |
| `PassFrame` | the per-pass frame layer (`ρsh`, `rebaseSim`) and the transfer plumbing |
| `Canonical` | the outer induction, the canonical end-to-end run, and the framed forms `isort_framed`/`isort_framed_readout` |
| `Family` | `isFamily`, the harness `Func` and its pin |
| `Setup` | the entry equation and the setup phase (the family materialized) |
| `Subject` | the subject phase at the harness placement: configurations, segments, both inductions, the threshold-11 frame layer |
| `Scan` | test phase 1 — the sortedness scan |
| `Rebuild` | test phase 2 — the rebuild loop |
| `Count` | test phase 3 — the O(n²) count loops, the pure counting layer and the threshold-21 frame layer |
| `Run` | the remainder run and `isortH_runs` — the full harness composition |

Declarations that were `private` and are referenced across a shard
boundary lost that modifier (Lean's `private` is per-module); nothing
else about them changed. The public API — every name `proofs/Audit.lean`
pins — is unchanged, and so are the recorded axiom sets.
-/

namespace GoLean.Examples.InsertionSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem
open GoLean.Frame

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-! ## The user-facing statement (§11) -/

/-- **THE HEADLINE (§11 harness form)**: for every `n < 2^63` (Go's
`int` domain for lengths — `make([]uint64, n)` panics past it) and
every `seed < 2^64` (the full uint64 domain), running the three-phase
Go harness `isort_harness(n, seed)` through the machine's native
function entry — empty-heap state, both arguments at the call
boundary — completes normally past one fuel bound
(`N = (92·n+160)·n + (110·n+220)·n + 285·n + 505` — quadratic: the
count loops are O(n²)), at every nondeterminism-choice stream, and
RETURNS the verdict 1: the test phase, IN GO and inside the verified
footprint, checked that `insertionSort` left the wrapped
multiplicative family `[seed·1, seed·2, …, seed·n] (mod 2^64)` sorted
AND a permutation of the rebuilt family (the count-based check, both
directions folded into `ok`).

INPUT-FAMILY HONESTY (§11, recorded): the quantification is over the
scalars `(n, seed)` — the input family `isFamily n seed`, honestly
weaker than ∀xs over arbitrary slice contents (the choice-consuming
input pick is designed, not built; `isort_framed` above keeps the ∀xs
claim proof-side). The wrapping family is deliberate: `seed·(i+1)`
wraps at `2^64`, so the family covers duplicates and non-monotone
orders — exactly the interesting sort inputs — and the corpus oracle
rows exercise the same harness at concrete arguments. -/
theorem isort_ok (n seed : Nat) (hn : n < 2 ^ 63) (hseed : seed < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel isortLowered.typeDefs.toList
          isortLowered.funcs isortHarnessFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
          isortLowered.methods ch
        = .ok { values := #[.int 1 .uint64] } := by
  refine ⟨(92 * n + 160) * n + (110 * n + 220) * n + 285 * n + 505,
    fun fuel hfuel ch => ?_⟩
  obtain ⟨k, σf, hk, hrun, hlook⟩ := isortH_runs n seed hn ch
  -- The macro-emitted σIH0 receives already-normalized values, so the
  -- unorm collapse moves from inside hσ to the rw chain (G0 item 3c).
  have hσ : σIH0 ((n : Nat) : Int) ((seed : Nat) : Int) = σIStart n seed := by
    simp only [σIH0, σIStart, ucell]
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [iharness_entry_eq,
    unorm_of_range (v := ((n : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((seed : Nat) : Int)) (by omega) (by omega),
    hσ, hfold, runConfig_next_stop]
  have hload : loadMany σf [.base ⟨2⟩] = .ok [.int 1 .uint64] := by
    simp [loadMany, loadLoc, hlook, ucell, pure, Except.pure, Bind.bind,
      Except.bind]
  simp [hload, Bind.bind, Except.bind, pure, Except.pure]

/-- **The D1 run-conditioned twin**: any successful completion of the
harness entry, at any fuel and any choice stream, returns the verdict
1 — derived from `isort_ok` via `harness_readout_of_total`. -/
theorem isort_readout (n seed : Nat) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) :
    ∀ (fuel : Nat) (ch : Choices) (r : Result),
      runFunctionWithContextM fuel isortLowered.typeDefs.toList
          isortLowered.funcs isortHarnessFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
          isortLowered.methods ch
        = .ok r →
      r = { values := #[.int 1 .uint64] } :=
  harness_readout_of_total (isort_ok n seed hn hseed)


end GoLean.Examples.InsertionSort
