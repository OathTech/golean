import Lean
import GoLeanProofs.Examples.InsertionSort

/-!
# In-build axiom gate — the InsertionSort example

Per-example shard of `proofs/Audit.lean` (examples phase-2 slice 0,
lever 3, 2026-08-14; the per-file dependency shape of `deps/brick-wp`'s
2026-08-14 sharded audit). The `example :=` witness references and the
`#guard_msgs #print axioms` pins below are VERBATIM from the
pre-shard `Audit.lean`.

The shard imports ONLY this example's module, so a change to another
example does not re-elaborate it. It is built because the root
`Audit.lean` imports it — and `scripts/ci`'s proofs-file audit-coverage
step FAILS if any `proofs/**/*.lean` leaves the audited import closure,
so dropping that import cannot silently retire these pins.
-/

namespace GoLean.Iris.Audit

/-! ## The insertion-sort example (scale-out slice 2c, 2026-08-13)

HARNESS STATUS (§11): **GAP CLOSED 2026-08-13** — the recorded gap
(subject-phase port + the Go-side test-phase inductions: sortedness
scan, rebuild, the O(n²) count loops with a second frame-rebase layer)
is now proven, so `isort_ok` IS the §11 harness headline over
`runFunctionWithContextM`, exactly as the never-a-weakened-statement
rule required. The memory-quantified pair is renamed
`isort_framed`/`isort_framed_readout` and kept green as the proof-side
supporting layer (the gcd/minmax/binsearch/reverse `_framed`
precedent) — it remains the STRONGER input claim (∀xs over arbitrary
slice contents vs the harness's scalar-parameterized family), which is
the recorded input-family honesty of the harness form.

`✓` **`isort_ok` — the nested-loop HARNESS headline** (§11 form,
`Examples/InsertionSort.lean` over the pinned `isortLowered`): for
every `n < 2^63` and every `seed < 2^64`, the three-phase Go harness
`isort_harness(n, seed)` — observed ONLY through the machine's native
function entry, empty-heap state, both arguments at the call boundary,
no Lean-side heap readback anywhere in the statement — completes
normally past `N = (92·n+160)·n + (110·n+220)·n + 285·n + 505`
(quadratic: the count loops are O(n²)) at EVERY nondeterminism-choice
stream and RETURNS THE VERDICT 1. The verdict is computed IN GO inside
the verified footprint: setup materializes the wrapped multiplicative
family `seed·(i+1) mod 2^64` (duplicates and non-monotone orders —
exactly the interesting sort inputs; `seed = 0` is the all-equal
case, an oracle row), `insertionSort` runs, then the test phase checks
sortedness pairwise AND permutation by the count-based check against
the rebuilt family. Route findings (recorded): the scan/rebuild/count
remainder is proven as ONE canonical run from the post-subject 11-cell
state and transferred to the true subject-garbage placement in a
SINGLE frame-theorem application — that is what keeps those segments
address-concrete despite sitting behind n-dependent garbage; the
predicted second frame-rebase layer (threshold 21, 4 cells retired per
pass) is exactly what the count loops needed. D1 twin: `isort_readout`
via `harness_readout_of_total`. Grounding: corpus rows
`examples/isort/harness-five` (5,37), `harness-dups` (6,0),
`harness-empty` (0,5), differentially green against `go run`.

`✓` **`isort_framed` — the nested-loop memory-input form** (proof-side
supporting layer per §11)
(`Examples/InsertionSort.lean` over the pinned `isortLowered`). For
any `[]uint64` input list, at ANY placement, beside ANY disjoint
frame: execution completes normally past one fuel bound at every
choice stream, the backing cell holds `sortSpec xs` — a SORTED
PERMUTATION (`sortSpec_sorted` / `sortSpec_count` /
`sortSpec_length`, same module; `Sorted` is the shared
`SliceMem.Sorted` vocabulary, this commit its first committed
consumer) — and every frame cell is preserved verbatim. Statement
delta: `hlen : xs.length < 2^63` (Go's `int` domain, the reverse
precedent). Proof route (recorded): TWO PLAIN NESTED strong
inductions over direct machine-step segments — no fuel-measure-rule
variant needed (that sugar gap is the WP route's only) — with the
arc's principal nested-loop finding: the machine RE-ALLOCATES the
inner `j`/`$forFirst` pair every outer pass, so each pass is proven
once at a tight canonical placement and transferred through the
executable frame theorem at the accumulated-garbage shift, retired
cells REBASED into the frame between passes — the frame theorem is
load-bearing INSIDE the canonical run, then consumed again at the
input-relocating renaming for the ∀-placement form. Short-circuit
`&&` is realized as the model's one-step false delivery: at `j = 0`
the machine provably never reads `s[j-1]`. D1 twin:
`isort_framed_readout` via `normal_readout_of_total`. -/
example := @GoLean.SliceMem.Sorted
example := @GoLean.Examples.InsertionSort.isort_ok
example := @GoLean.Examples.InsertionSort.isort_readout
example := @GoLean.Examples.InsertionSort.isort_framed
example := @GoLean.Examples.InsertionSort.isort_framed_readout
example := @GoLean.Examples.InsertionSort.isFamily
example := @GoLean.Examples.InsertionSort.sortSpec_sorted
example := @GoLean.Examples.InsertionSort.sortSpec_count
example := @GoLean.Examples.InsertionSort.sortSpec_length
/-- info: 'GoLean.Examples.InsertionSort.isort_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.InsertionSort.isort_ok
/-- info: 'GoLean.Examples.InsertionSort.isort_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.InsertionSort.isort_readout
/-- info: 'GoLean.Examples.InsertionSort.isort_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.InsertionSort.isort_framed
/-- info: 'GoLean.Examples.InsertionSort.isort_framed_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.InsertionSort.isort_framed_readout
/-- info: 'GoLean.Examples.InsertionSort.sortSpec_sorted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.InsertionSort.sortSpec_sorted

end GoLean.Iris.Audit
