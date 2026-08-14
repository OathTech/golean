import GoLeanProofs.Examples.Histogram.HarnessR

/-!
# Histogram — the map-histogram example (Gallery Campaign G1, flagship)

Go source: `Corpus/coverage/exec/examples/histogram/main.go`
(differentially green against `go run`, 13 rows). Lowering pinned by
`scripts/check-golden` against `baselines/golden/histogram-lowered.repr`
and carried in `GoLeanProofs.Examples.HistogramProgram`.

The subject builds a `map[uint64]uint64` of counts over a slice, reads
the count of a queried key, and then counts the map's entries with a
VARIABLE-FREE `for range counts {}`. The harness is the S3 RELATIONAL
style: it returns the values it counted (as a fixed-cap `[8]uint64`)
alongside both summaries, so the postcondition is a relation over the
RETURNED DATA — `hits = occurrences q vals` and
`distinct = distinctCount vals` — with no family function
re-describing the setup inside the claim.

**Why the `∀ ch` quantifier is load-bearing here.** `for range counts`
consumes one `Choices` pick per iteration, so the headline quantifies
over EVERY map-iteration order. `distinctCount` is a function of the
returned values alone, so it cannot see the order the machine chose —
and the claim holds at all of them precisely for that reason. A spec
naming "the first key visited" would be unprovable here, and that
unprovability would be the envelope working.

The per-phase shards:

* `Histogram.Pure` — the two statement functions (`occurrences`,
  `distinctCount`), the counting fold, and the bridges.
* `Histogram.Machine` — the two pinned `Func`s, the address layout, and
  the variable-free choice-pick step.
* `Histogram.CountLoop` — the counting loop.
* `Histogram.HarnessR` — everything else, and the end-to-end run.

THE HEADLINE is stated HERE, in the root, so that the aggregator's
`import GoLeanProofs.Examples.Histogram` reaches it by name — the
C-H4/C-H5 shape the 2026-08-15 audit asked for, adopted from birth
instead of retrofitted.
-/

namespace GoLean.Examples.Histogram

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-- **THE HEADLINE (§11 harness form, S3 RELATIONAL)**: for every
`n ≤ 8`, every `seed < 2^64` and every queried key `q < 2^64`, running
the Go harness `histogram_harness_r(n, seed, q)` through the machine's
native function entry — empty-heap state, all three arguments at the
call boundary — completes normally past one fuel bound, at every
nondeterminism-choice stream, and returns THREE values: a length-`n`
value list `vals` as the fixed-cap array the Go returns, the number of
times `q` occurs in it, and the number of distinct values it holds. The
postcondition is a relation over the RETURNED DATA — no family function
and no closed form appears in it.

Honesty clauses, all recorded rather than hidden:

* **ORDER-INVARIANCE is what makes the third value mean what it looks
  like.** The `for range counts` loop consumes one choice per
  iteration, so `∀ ch` ranges over EVERY map-iteration order; the
  equation holds at all of them BECAUSE `distinctCount` is a function
  of the returned values alone and cannot see the order. Read the
  statement with that in mind: it says "the third value is how many
  distinct values the returned array holds", full stop — a spec that
  named an order-dependent witness ("the first key visited") would be
  unprovable here, and that unprovability would be the envelope
  working.
* **The queried count is the map READ, zero value included.** Go's
  `counts[q]` on an absent key yields `0`, and `occurrences q vals` is
  `0` in exactly that case — the corpus rows `miss`, `one-miss` and
  `harness-r-miss` pin the behaviour on the oracle side.
* **The cap `n ≤ 8` is a toy bound.** Go's pass-by-value fragment
  cannot return unbounded data, so the harness returns
  `[histogramCapN]uint64` with `histogramCapN = 8` (visible in the
  corpus Go) and the copy loop plus zero-padding exist ONLY so the
  counted values can cross the observation boundary.
* **`∃ vals` is still family-determined.** The witness is
  `histFamily n seed`; the statement merely avoids SAYING so. Making
  the input genuine ∀-data needs the ghost rung-1 annotation, which is
  designed and not built.
* **Machine idealization** as in the other entries: entry from an empty
  heap, an unbounded heap, allocation always succeeds.

Fuel bound `N = 210·n + 344` — provable from the branch-UNIFORM loop
bounds (57 per setup iteration, 53 per copy iteration, 84 per counting
iteration, 16 per range iteration, and the range loop is charged `n`
iterations rather than the `distinctCount vals ≤ n` it actually runs).
The MEASURED step count is EXACTLY `194·n + 16·distinctCount vals + 344`
(probe-verified at `n = 0…8`, independent of the choice stream and of
`q`); that measurement is NOT affine in `n`, because the family
`v[i] = seed + i%3` stops adding map entries after the third value.
Neither number is presented as the other. -/
theorem histogram_ok (n seed q : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64)
    (hq : q < 2 ^ 64) :
    ∃ vals : List Int, vals.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel histogramLowered.typeDefs.toList
            histogramLowered.funcs histHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
              .int (q : Int) .uint64]
            histogramLowered.methods ch
          = .ok { values := #[histArr8 vals,
                              .int (occurrences (q : Int) vals : Nat) .uint64,
                              .int (distinctCount vals : Nat) .uint64] } := by
  refine ⟨histFamily n seed, histFamily_length n seed, 210 * n + 344,
    fun fuel hfuel ch => ?_⟩
  obtain ⟨k, ch', tail, na, hk, hrun⟩ :=
    hg_runs_generic hProg n seed q hcap hq
      (h_enterFrame_fact n seed q (unorm_nat_of_lt hq)) ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  -- the recorded show-bridge (structural: record updates of `hProg`)
  have hst : hHSeed ((n : Nat) : Int) ((seed : Nat) : Int) ((q : Nat) : Int)
      = hSt hProg (hHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)
        ((q : Nat) : Int)) 6 := rfl
  rw [hH_entry_eq, unorm_of_range (v := (n : Int)) (by omega) (by omega),
    unorm_of_range (v := (seed : Int)) (by omega) (by omega),
    unorm_of_range (v := (q : Int)) (by omega) (by omega),
    hst, hfold, runConfig_next_stop]
  show (Except.ok { values := #[.array _, .int _ .uint64, .int _ .uint64] } :
      Except GoError Result) = _
  rw [histArr8, ← histPre_full]

/-- **The D1 run-conditioned twin**: any successful completion of the
harness entry returns those three values. -/
theorem histogram_readout (n seed q : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) (hq : q < 2 ^ 64) :
    ∃ vals : List Int, vals.length = n ∧
      ∀ (fuel : Nat) (ch : Choices) (r : Result),
        runFunctionWithContextM fuel histogramLowered.typeDefs.toList
            histogramLowered.funcs histHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
              .int (q : Int) .uint64]
            histogramLowered.methods ch
          = .ok r →
        r = { values := #[histArr8 vals,
                          .int (occurrences (q : Int) vals : Nat) .uint64,
                          .int (distinctCount vals : Nat) .uint64] } := by
  obtain ⟨vals, hlen, htot⟩ := histogram_ok n seed q hcap hseed hq
  exact ⟨vals, hlen, harness_readout_of_total htot⟩

end GoLean.Examples.Histogram
