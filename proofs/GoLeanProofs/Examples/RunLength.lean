import GoLeanProofs.Examples.RunLength.HarnessR

/-!
# RunLength — the `rle` example (Gallery Campaign G1)

Go source: `Corpus/coverage/exec/examples/rle/main.go`
(differentially green against `go run`, 14 rows). Lowering pinned by
`scripts/check-golden` against `baselines/golden/rle-lowered.repr` and
carried in `GoLeanProofs.Examples.RunLengthProgram`.

The subject `rle` walks `s`, EXTENDING the current run while the value
repeats (`runCounts[k-1]++`) and opening a new run otherwise — the
new-run arm builds each output slice with **`append`**, Go's growable-
slice primitive. The harness is the S3 RELATIONAL style: it returns
the encoded input `pre`, BOTH parallel output arrays `runVals`/
`runCounts` (as fixed-cap `[8]uint64`s), and the run count `k`, so the
postcondition is a relation over the RETURNED DATA — the returned
`(runVals, runCounts, k)` ARE the projections of `rleSpec pre`, the
mathematician's run-length encoding, whose decode theorem
(`rleSpec_decode`) certifies it reproduces its input.

**Why `append` is this example's story.** The machine's `appendSlice`
spill draws its fresh backing's CAPACITY from the nondeterminism-choice
stream — the envelope `[newLen, max 32 (2·growth)]`, per spec
§Appending ("a new, sufficiently large underlying array"). The
headline's `∀ ch` therefore ranges over every capacity the envelope
admits: both spills' capacities are carried SYMBOLICALLY through every
downstream heap front, and nothing the harness returns depends on
them. That is a REAL nondeterminism-envelope statement, not a
fixed-schedule replay.

**Scope honesty — the `n ≤ 3` cap is a RECORDED GAP, not the harness's
own bound.** The harness caps at `n ≤ 8`; this headline proves the
SINGLE-RUN regime `n ≤ 3` (the family `seed + i/3` is constant there,
so exactly one new-run event fires and both its appends spill from
cap 0). For `n ∈ [4, 8]` a SECOND new-run event fires at `i = 3`, and
whether ITS appends spill or extend in place depends on the FIRST
spill's choice-drawn capacity — so the machine's allocation layout
(every later heap address) is choice-dependent, which the current
raw-segment proof technology (literal addresses) cannot follow without
either per-spill-history segment sets or new kit machinery (an
address-shift frame lemma / a symbolic-`nextAddr` micro-step library).
See the campaign log's kit-gap entry; the claim below simply does not
speak about `n > 3` — nothing is weakened silently.

The per-phase shards:

* `RunLength.Pure` — `rleSpec`, its DECODE theorem, and the setup
  family `seed + i/3` (a kit-gap witness: `familyMod` cannot express
  `/`).
* `RunLength.Machine` — the two pinned `Func`s, the address layout,
  the continuations and the heap fronts (spill capacities symbolic).
* `RunLength.HarnessR` — the append-spill executable facts, the raw
  segments, the composed iterations and the per-`n` end-to-end runs.

THE HEADLINE is stated HERE, in the root, so the aggregator's
`import GoLeanProofs.Examples.RunLength` reaches it by name (C-H4/C-H5
shape, adopted from birth).
-/

namespace GoLean.Examples.RunLength

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-- **THE HEADLINE (§11 harness form, S3 RELATIONAL)**: for every
`n ≤ 3` and every `seed < 2^64`, running the Go harness
`rle_harness_r(n, seed)` through the machine's native function entry —
empty-heap state, both arguments at the call boundary — completes
normally past one fuel bound, at EVERY nondeterminism-choice stream
(this includes every append-spill capacity the machine's envelope
admits), and returns FOUR values: the length-`n` encoded input `pre`
(as the fixed-cap array the Go returns), `runVals` and `runCounts`
holding exactly the value/count projections of `rleSpec pre`
zero-padded to cap, and the run count `k = (rleSpec pre).length`.
`rleSpec` is the mathematician's run-length encoding — grouped maximal
runs, with `rleSpec_decode : (rleSpec l).flatMap (replicate ∘ swap) =
l` proven in `RunLength.Pure`.

Honesty clauses, all recorded rather than hidden:

* **The cap `n ≤ 3` is NOT the harness's own bound (`n ≤ 8`).** It is
  the single-run regime — the recorded honest gap for `n ∈ [4, 8]` is
  the choice-dependent spill/in-place branching at the second new-run
  event (module docstring above, and the campaign log's kit-gap
  entry). Within `n ≤ 3` the claim is complete: both `append` spills,
  the extend path, and all four returns are covered.
* **The postcondition is a relation over RETURNED data** — no family
  function, no heap/cell/seed vocabulary. `rleSpec pre` on a constant
  `pre` is `[(v, n)]` (or `[]` at `n = 0`); the theorem's content at
  this domain is that the machine's append/extend path REALIZES that
  encoding, zero-pads the fixed-cap arrays past `k`, and reports `k`.
* **`∃ pre` is still family-determined.** The witness is the setup
  family `s[i] = seed + i/3` (constant on `n ≤ 3`); the statement
  merely avoids SAYING so. Genuine ∀-data needs ghost rung 1.
* **The fixed cap `8` is a toy bound**: Go's pass-by-value fragment
  cannot return unbounded data, so the harness returns `[8]uint64`s
  and zero-pads — the arrays exist ONLY so the data can cross the
  observation boundary.
* **`n = 0` is included**: no run event fires, both output slices stay
  empty, `k = 0`, all arrays all-zero (row `harness-r-empty` pins this
  against `go run`).
* **Machine idealization** as in the other entries: entry from an
  empty heap, an unbounded heap, allocation always succeeds.

Fuel bound `N = 253·n + 527` — a BOUND, not a measurement: it dominates
the per-`n` exact counts (front `238 + 110·n`, the head test `27`, the
new-run event `148`, `143` per extend iteration, exit-through-epilogue
`257`). The MEASURED counts, recorded separately and NOT presented as
the bound: `419` at `n = 0`, `780` at `n = 1`, `1033` at `n = 2`,
`1286` at `n = 3` (probe-measured, then re-derived exactly by the
segment sums; the step count is choice-independent — spill and
in-place appends cost the same steps). -/
theorem rle_ok (n seed : Nat) (hcap : n ≤ 3) (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel rleLowered.typeDefs.toList
            rleLowered.funcs rleHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            rleLowered.methods ch
          = .ok { values :=
              #[rleArr8 pre,
                rleArr8 ((rleSpec pre).map Prod.fst),
                rleArr8 ((rleSpec pre).map (fun p => ((p.2 : Nat) : Int))),
                .int (((rleSpec pre).length : Nat) : Int) .uint64] } := by
  refine ⟨rleFamily n seed, rleFamily_length n seed, 253 * n + 527,
    fun fuel hfuel ch => ?_⟩
  have hc : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  · -- n = 0
    obtain ⟨k, ch', hk, hrun⟩ := q_runs0 qProg seed
      (q_enterFrame_fact 0 seed) ch
    have hfold := runConfig_of_stepFnIter hrun (fuel - k)
    rw [show k + (fuel - k) = fuel from by omega] at hfold
    have hst : qHSeed ((0 : Nat) : Int) ((seed : Nat) : Int)
        = qSt qProg (qHeap0 ((0 : Nat) : Int) ((seed : Nat) : Int)) 6 := rfl
    rw [q_entry_eq,
      unorm_of_range (v := ((0 : Nat) : Int)) (by omega) (by omega),
      unorm_of_range (v := ((seed : Nat) : Int)) (by omega) (by omega),
      hst, hfold, runConfig_next_stop]
    show (Except.ok { values := #[.array _, .array _, .array _,
        .int _ .uint64] } : Except GoError Result) = _
    rw [rleArr8, rlePre_full, rleSpec_const_form (by omega)]
    rfl
  · -- n = 1
    obtain ⟨k, capV, capC, ch', hk, hrun⟩ := q_runs1 qProg seed
      (q_enterFrame_fact 1 seed) ch
    have hfold := runConfig_of_stepFnIter hrun (fuel - k)
    rw [show k + (fuel - k) = fuel from by omega] at hfold
    have hst : qHSeed ((1 : Nat) : Int) ((seed : Nat) : Int)
        = qSt qProg (qHeap0 ((1 : Nat) : Int) ((seed : Nat) : Int)) 6 := rfl
    rw [q_entry_eq,
      unorm_of_range (v := ((1 : Nat) : Int)) (by omega) (by omega),
      unorm_of_range (v := ((seed : Nat) : Int)) (by omega) (by omega),
      hst, hfold, runConfig_next_stop]
    show (Except.ok { values := #[.array _, .array _, .array _,
        .int _ .uint64] } : Except GoError Result) = _
    rw [rleArr8, rlePre_full, rleSpec_const_form (by omega)]
    rfl
  · -- n = 2
    obtain ⟨k, capV, capC, ch', hk, hrun⟩ := q_runs2 qProg seed
      (q_enterFrame_fact 2 seed) ch
    have hfold := runConfig_of_stepFnIter hrun (fuel - k)
    rw [show k + (fuel - k) = fuel from by omega] at hfold
    have hst : qHSeed ((2 : Nat) : Int) ((seed : Nat) : Int)
        = qSt qProg (qHeap0 ((2 : Nat) : Int) ((seed : Nat) : Int)) 6 := rfl
    rw [q_entry_eq,
      unorm_of_range (v := ((2 : Nat) : Int)) (by omega) (by omega),
      unorm_of_range (v := ((seed : Nat) : Int)) (by omega) (by omega),
      hst, hfold, runConfig_next_stop]
    show (Except.ok { values := #[.array _, .array _, .array _,
        .int _ .uint64] } : Except GoError Result) = _
    rw [rleArr8, rlePre_full, rleSpec_const_form (by omega)]
    rfl
  · -- n = 3
    obtain ⟨k, capV, capC, ch', hk, hrun⟩ := q_runs3 qProg seed
      (q_enterFrame_fact 3 seed) ch
    have hfold := runConfig_of_stepFnIter hrun (fuel - k)
    rw [show k + (fuel - k) = fuel from by omega] at hfold
    have hst : qHSeed ((3 : Nat) : Int) ((seed : Nat) : Int)
        = qSt qProg (qHeap0 ((3 : Nat) : Int) ((seed : Nat) : Int)) 6 := rfl
    rw [q_entry_eq,
      unorm_of_range (v := ((3 : Nat) : Int)) (by omega) (by omega),
      unorm_of_range (v := ((seed : Nat) : Int)) (by omega) (by omega),
      hst, hfold, runConfig_next_stop]
    show (Except.ok { values := #[.array _, .array _, .array _,
        .int _ .uint64] } : Except GoError Result) = _
    rw [rleArr8, rlePre_full, rleSpec_const_form (by omega)]
    rfl

/-- **The D1 run-conditioned twin**: any successful completion of the
harness entry returns those four values. -/
theorem rle_readout (n seed : Nat) (hcap : n ≤ 3) (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∀ (fuel : Nat) (ch : Choices) (r : Result),
        runFunctionWithContextM fuel rleLowered.typeDefs.toList
            rleLowered.funcs rleHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            rleLowered.methods ch
          = .ok r →
        r = { values :=
            #[rleArr8 pre,
              rleArr8 ((rleSpec pre).map Prod.fst),
              rleArr8 ((rleSpec pre).map (fun p => ((p.2 : Nat) : Int))),
              .int (((rleSpec pre).length : Nat) : Int) .uint64] } := by
  obtain ⟨pre, hlen, htot⟩ := rle_ok n seed hcap hseed
  exact ⟨pre, hlen, harness_readout_of_total htot⟩

/-- Zipping the two projections back together and expanding each run
reproduces the encoded list — the pure half of the decode corollary. -/
theorem zip_proj_decode (L : List (Int × Nat)) :
    (List.zip (L.map Prod.fst) (L.map (fun p => ((p.2 : Nat) : Int)))).flatMap
        (fun p => List.replicate p.2.toNat p.1)
      = L.flatMap (fun p => List.replicate p.2 p.1) := by
  induction L with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨v, c⟩ := p
    simp only [List.map_cons, List.zip_cons_cons, List.flatMap_cons, ih,
      Int.toNat_natCast]

/-- **The first-order readout — the DECODE relation** (statement-TCB
doctrine: a headline ships a corollary a reader can check against the
Go without unfolding `rleSpec`): the machine returns lists
`vals`/`counts` of equal length `k` such that expanding each
`(vals[j], counts[j])` pair back into a run REPRODUCES the returned
input `pre` exactly. -/
theorem rle_decode (n seed : Nat) (hcap : n ≤ 3) (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        ∃ (vals counts : List Int),
          runFunctionWithContextM fuel rleLowered.typeDefs.toList
              rleLowered.funcs rleHarnessRFunc
              #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
              rleLowered.methods ch
            = .ok { values :=
                #[rleArr8 pre, rleArr8 vals, rleArr8 counts,
                  .int ((vals.length : Nat) : Int) .uint64] }
          ∧ vals.length = counts.length
          ∧ (List.zip vals counts).flatMap
              (fun p => List.replicate p.2.toNat p.1) = pre := by
  obtain ⟨pre, hlen, N, htot⟩ := rle_ok n seed hcap hseed
  refine ⟨pre, hlen, N, fun fuel hfuel ch =>
    ⟨(rleSpec pre).map Prod.fst,
     (rleSpec pre).map (fun p => ((p.2 : Nat) : Int)), ?_, by simp, ?_⟩⟩
  · have := htot fuel hfuel ch
    rw [this]
    simp
  · rw [zip_proj_decode, rleSpec_decode]

end GoLean.Examples.RunLength

