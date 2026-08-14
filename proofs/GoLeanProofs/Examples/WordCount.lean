import GoLeanProofs.Examples.WordCount.Pure
import GoLeanProofs.Examples.WordCount.Machine
import GoLeanProofs.Examples.WordCount.CountGeneric
import GoLeanProofs.Examples.WordCount.CanonCount
import GoLeanProofs.Examples.WordCount.RangeGeneric
import GoLeanProofs.Examples.WordCount.CanonRange
import GoLeanProofs.Examples.WordCount.Return
import GoLeanProofs.Examples.WordCount.CanonRun
import GoLeanProofs.Examples.WordCount.EmptyRun
import GoLeanProofs.Examples.WordCount.Empty
import GoLeanProofs.Examples.WordCount.Family
import GoLeanProofs.Examples.WordCount.HarnessSetup
import GoLeanProofs.Examples.WordCount.HarnessSubject
import GoLeanProofs.Examples.WordCount.HarnessRun


/-!
# Verified example: word count over a Go map (verified-examples slice 2c,
2026-08-13)

The map scale-out example over the settled memory-quantified form
(design note `docs/2026-08-12_example-spec-form.md` §10): the Go program
is the canonical corpus source
`Corpus/coverage/exec/examples/wordcount/main.go` (6/6 differentially
green against `go run`); `wordCountLowered` is its pinned frontend
lowering (`scripts/check-golden`, both links). The subject `maxCount`
builds `counts : map[uint64]uint64` from a `[]uint64` and takes the max
count with `for _, c := range counts`.

**WHERE THE HEADLINE LIVES — read this first** (examples phase-2 slice
1 swap, 2026-08-14; recorded here in the audit response, 2026-08-15,
which found this module described as the headline module while the
designated headline sits elsewhere). The DESIGNATED gallery headline
`wordcount_ok` is the S3 RELATIONAL form over `wordcount_harness_r` —
the Go returns the counted words alongside the answer, so the
postcondition relates RETURNED DATA — and it is declared in the swap
shard `GoLeanProofs.Examples.WordCount.HarnessR`, not here. What THIS
module declares is the demoted `wordcount_ok_v1` /
`wordcount_readout_v1` (the solved-value form, kept unweakened).

The shard IMPORTS this module, so the reach is one-way: importing
`GoLeanProofs.Examples.WordCount` does not give you `wordcount_ok`,
while importing `GoLeanProofs.Examples.WordCount.HarnessR` gives you
both. Import the shard. The re-export that would make this module the
single entry point is not expressible while the shard imports it —
Lean's import graph is acyclic — so it waits on the shard being
re-pointed at the phase modules it actually uses, recorded as a
post-merge follow-up in `docs/2026-08-15_phase2-premerge-audit.md`
(C-H4/C-H5). The aggregator `GoLeanProofs.lean` imports both, so
nothing is outside the audited build.

**Statement form of record (harness ruling 2026-08-13, form note §11)**:
user-facing headlines are three-phase Go HARNESSES stated over
`runFunctionWithContextM` — termination + returned values only, no
Lean-side heap vocabulary. What THIS module ships against that form:

* `maxCount_total_canonical` — the SUPPORTING inner-run theorem
  (fallback rung 2): for EVERY uint64 word list, the `maxCount` run at
  the canonical placement completes past the explicit fuel bound
  `132 + 108·len`, at EVERY nondeterminism-choice stream, with exactly
  `maxMultiplicity ws` delivered and the input backing untouched. All
  the semantic content (the ∀-choices range induction included) lives
  here; it is ∀-ws (STRONGER than any scalar-parameterized harness
  family).
* `wordcount_empty_ok` — the harness FORM, witnessed end to end at the
  pinned `maxCountEmpty` harness (the zero-parameter instance).
* `wordcount_ok_v1` (named `wordcount_ok` when this was written, and
  demoted by the slice-1 swap without being weakened) — **gap G1
  CLOSED (consolidation slice, 2026-08-14)**: the
  `(n, seed)`-parameterized §11 harness headline
  over `wordcount_harness`, hypotheses just `n < 2^63` and
  `seed < 2^64` (the seed-wrap caveat stays refuted), returned value
  EXACTLY `(n+2)/3` via `wcFamily_maxMult`; `wordcount_readout_v1` is
  the derived D1 twin. Closed as the FIRST CONSUMER of the
  placement-generic composition layer (`wcIter_generic`/
  `wcLoop_generic`/`wcRange_generic` below): the compositions are
  stated once over an abstract state family and instantiated at both
  the canonical and harness placements — the 2026-08-13 elaborator
  storm (diagnosed as exponential delta-fallback unification over
  concrete fronts, `docs/2026-08-13_consolidation-slice.md` §1) is
  structurally impossible in this form.

**The teaching point (§10b): the ∀-choices quantifier does REAL work
here.** `for … range m` consumes one `Choices` pick per iteration
(`stepFn`'s `mapIterK` arm), so the headline quantifies over every
ITERATION ORDER of the map — the claim holds at all of them, which is
exactly why the specification function `maxMultiplicity` must be an
order-independent fold (max is commutative-idempotent). A spec that
named "the first key with maximal count" would be unprovable — different
orders yield different firsts — and that unprovability is the envelope
working, not failing. The proof's range half is the §10b choice-pick
induction: destructure `Choices.consume` (its `% bound` contract gives
`idx < size`), erase the picked index, re-establish the max-fold
invariant.

**The §10c obstruction, realized**: `bindIterVars` allocates a fresh
value cell per range iteration, so in-loop addresses are symbolic in
the iteration count and `with_unfolding_all rfl` segments cannot carry
the range body — its heap-touching steps are HAND-GLUED conditioned
steps (`stepFn` unfoldings + `Heap.lookup`/`storeLoc` facts at symbolic
addresses, closed by `beq`-disequality simp, not `rfl`). RECORDED
DEVIATION from the §10 plan (a finding, per the slice instructions):
the plan expected phase C (the counting loop) to be address-concrete
with `nextAddr` first moving at the range loop; in fact the frontend
lowers `counts[words[i]]++` through per-iteration temporaries `$c1`/
`$c2` whose `initialization` ALLOCATES two fresh cells per counting
iteration, so phase C is in the symbolic-address regime too and is
glued the same way. (Probe: `xs = [7,3,7]` runs 432 steps, `nextAddr`
2 → 18 — 7 entry cells, 2 per counting iteration, 1 per range
iteration.) The `best` cell is likewise at the length-dependent address
`9 + 2·len`, not a concrete one.

Scope honesty (the charter's two-questions separation): usability
evidence only — never machine-hardening evidence.
-/

/-!
## Module layout (per-phase split, examples phase-2 slice 0 lever 2,
2026-08-14)

This file is the THIN HEADLINE module: it holds the user-facing §11
harness statements this module owns — since the slice-1 swap that is
the demoted `wordcount_ok_v1` / `wordcount_readout_v1` pair, the
current headline being the `HarnessR` shard's (see the note at the top
of this file) — and nothing else. The proof phases live in
`GoLeanProofs.Examples.WordCount.*`, imported above in dependency
order, and were moved VERBATIM — every statement and proof is
byte-identical to the pre-split module:

| shard | phase |
|---|---|
| `Pure` | the spec layer, the map-in-memory vocabulary, the counts algebra and the max fold |
| `Machine` | canonical-placement machine configurations, `stepFn_pick`, `DeadFrom` |
| `CountGeneric` | the placement-generic counting layer (`wcIter_generic`, `wcLoop_generic`) |
| `CanonCount` | the canonical placement's counting segments and discharges |
| `RangeGeneric` | the placement-generic range layer (`wcRange_generic`) |
| `CanonRange` | the canonical placement's range discharges and `wc_range_loop` |
| `Return` | the canonical return path (range exit → the driver terminal) |
| `CanonRun` | `wc_runs` and `maxCount_total_canonical` — the canonical end-to-end run |
| `EmptyRun` | the empty-input harness `Func`, its terminal state and the 158-step run |
| `Empty` | `wordcount_empty_ok` — the empty-input headline |
| `Family` | `wcFamily` and its closed form `wcFamily_maxMult` |
| `HarnessSetup` | the harness `Func`, its pin, the entry equation and the setup loop |
| `HarnessSubject` | the subject phase's configurations and segments at the harness placement |
| `HarnessRun` | the harness discharges, both loops, the exit family and `wcH_runs` |
| `HarnessR` | the S3 relational harness `wordcount_harness_r` — its `Func` pin, glue, discharges and the DESIGNATED headline `wordcount_ok` (added to this table in the 2026-08-15 audit response; it is a phase-2 slice-1 shard, not part of the lever-2 split, and it imports this module rather than the other way round — so `import GoLeanProofs.Examples.WordCount` does NOT reach it) |

Declarations that were `private` and are referenced across a shard
boundary lost that modifier (Lean's `private` is per-module); nothing
else about them changed. The public API — every name `proofs/Audit.lean`
pins — is unchanged, and so are the recorded axiom sets.

COST NOTE (updated for slice 1.5, 2026-08-14): `EmptyRun` WAS the
whole repo's memory ceiling — 81 s at a 50.8 GiB peak for ONE
declaration, `wc_empty_run`'s 158-step `with_unfolding_all rfl` over a
concrete configuration embedding the whole pinned program, growing
superlinearly with the corpus program (+1 function → ~77 GiB). Slice
1.5 restated the proof PROGRAM-generically (statement unchanged; see
`EmptyRun`'s module docstring): measured 86 s at a 1.9 GiB peak, and
the cost no longer tracks the corpus program's size.
-/

namespace GoLean.Examples.WordCount

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- **The v1 parameterized-harness headline (gap G1 CLOSED,
consolidation slice 2026-08-13; DEMOTED to `_v1` by the phase-2 slice-1
spec-style swap, 2026-08-14).** Kept unweakened, with its corpus rows
and its axiom pin: the S3 relational headline
(`Examples/WordCount/HarnessR.lean`'s `wordcount_ok`) states the same
program family through a DIFFERENT harness, so neither supersedes the
other. The difference is what the postcondition may mention — this one
names the family's SOLVED value `⌈n/3⌉` via `wcFamily_maxMult`, the S3
one relates `maxMultiplicity` to the words the program returned and
never uses the closed form.

The §11 harness form over `wordcount_harness`:
for every `n < 2^63` and every uint64 `seed`, past fuel `229 + 165·n`,
at EVERY nondeterminism-choice stream (every map-iteration order), the
harness run completes with EXACTLY `⌈n/3⌉ = (n+2)/3` as its returned
value — the closed form `wcFamily_maxMult` proves for the setup family
`w[i] = seed + i%3` at every seed (the refuted seed-wrap caveat,
finding 20). -/
theorem wordcount_ok_v1 (n seed : Nat) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel wordCountLowered.typeDefs.toList
          wordCountLowered.funcs wordcountHarnessFunc
          #[.int ((n : Nat) : Int) .uint64, .int ((seed : Nat) : Int) .uint64]
          wordCountLowered.methods ch
        = .ok ⟨#[.int (((n + 2) / 3 : Nat) : Int) .uint64]⟩ := by
  refine ⟨229 + 165 * n, fun fuel hfuel ch => ?_⟩
  obtain ⟨k, ch', tail, na, hk, hrun⟩ := wcH_runs n seed hn ch
  have hentry := wcH_entry_eq ((n : Nat) : Int) ((seed : Nat) : Int) fuel ch
  rw [unorm_nat_of_lt (show n < 2 ^ 64 by omega),
    unorm_nat_of_lt hseed] at hentry
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  have hfull : runConfig fuel
      (σWH0 ((n : Nat) : Int) ((seed : Nat) : Int))
      (.exec wordcountHarnessFunc.body [hWScope0] hWFrame0) ch
      = .ok (σXH n ((seed : Nat) : Int) ((n : Nat) : Int)
          (wcFamily n seed) (countsList (wcFamily n seed))
          (((n + 2) / 3 : Nat) : Int) (((n + 2) / 3 : Nat) : Int)
          (((n + 2) / 3 : Nat) : Int) tail na, ch') := by
    rw [hfold, runConfig_next_stop]
  rw [hentry, hfull]
  with_unfolding_all rfl

/-- The D1 run-conditioned twin, derived (`harness_readout_of_total`):
ANY successful completion, at any fuel and any choice stream, returns
exactly `⌈n/3⌉`. -/
theorem wordcount_readout_v1 (n seed : Nat) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) :
    ∀ (fuel : Nat) (ch : Choices) (r : Result),
      runFunctionWithContextM fuel wordCountLowered.typeDefs.toList
          wordCountLowered.funcs wordcountHarnessFunc
          #[.int ((n : Nat) : Int) .uint64, .int ((seed : Nat) : Int) .uint64]
          wordCountLowered.methods ch
        = .ok r →
      r = ⟨#[.int (((n + 2) / 3 : Nat) : Int) .uint64]⟩ :=
  harness_readout_of_total (wordcount_ok_v1 n seed hn hseed)


end GoLean.Examples.WordCount
