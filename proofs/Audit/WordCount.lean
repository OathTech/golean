import Lean
import GoLeanProofs.Examples.WordCount
import GoLeanProofs.Examples.WordCount.HarnessR

/-!
# In-build axiom gate — the WordCount example

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

/-! ## The word-count example (scale-out slice 2c, 2026-08-13)

`✓` **`maxCount_total_canonical` — the map example's canonical TOTAL,
∀ arbitrary word lists, EVERY choice stream doing real work**
(`Examples/WordCount.lean` over the pinned `wordCountLowered`): for
any `[]uint64` list below Go's int length domain, execution of the
canonical-placement driver completes normally past fuel `132 + 108·n`
at EVERY nondeterminism-choice stream — the map range consumes one
pick per iteration, so the ∀ch quantifier is doing genuine work here
(the §10b teaching point: the spec `maxMultiplicity` is
order-independent BY NECESSITY; an order-dependent claim would be
unprovable against the enveloped iteration) — with the max
multiplicity in the result cell and the input backing unchanged.
Proof: the §10 design executed — countsList assoc-invariant counting
induction + the choice-pick strong induction (`Choices.consume`
destructured, erase-and-max-fold invariant), both halves in the
symbolic-address regime (finding 12). `wordcount_empty_ok` is the §11
HARNESS form at the zero-parameter degenerate (runFunctionWithContextM
of `maxCountEmpty`, `[propext, Quot.sound]` — the Classical.choice-free
pattern again).

`✓` **G1 CLOSED (consolidation slice, 2026-08-13/14) —
`wordcount_ok`, the parameterized §11 harness headline over
`wordcount_harness(n, seed)`.** For every `n < 2^63` and EVERY uint64
`seed` (the refuted seed-wrap caveat — no collision hypothesis), past
fuel `229 + 165·n`, at EVERY nondeterminism-choice stream (the map
range consumes one pick per iteration — the ∀ch quantifier is doing
real work), the harness run over `runFunctionWithContextM` returns
EXACTLY `⌈n/3⌉ = (n+2)/3` — the closed form `wcFamily_maxMult` proves
for the setup family `w[i] = seed + i%3`. `wordcount_readout` is the
derived D1 twin (`harness_readout_of_total`). The former blocker — the
2026-08-13 elaborator isDefEq/whnf storm on the harness composition
proofs — was DIAGNOSED (postponed-elaboration metas inside big state
arguments defeat structural unification; the delta fallback compares
`Heap.lookup` over the concrete front at a symbolic address,
exponential in front length: 2^9 canonical vs 2^16 harness; record:
`docs/2026-08-13_consolidation-slice.md` §1) and REMOVED structurally:
the counting and range compositions are stated ONCE over an abstract
state family (`wcIter_generic`/`wcLoop_generic`/`wcRange_generic`)
with per-segment transition facts as hypotheses whose types pin every
intermediate state; both the canonical and harness placements are
instantiations. Statement closure: interpreter/native-entry vocabulary
(`runFunctionWithContextM`, `Choices`, `Result`) + the pinned
`wordcountHarnessFunc` (`rfl`-linked to the lowering) + `Nat`/`Int`
arithmetic — no heap vocabulary, no Iris, no Frame names; deletion-test
clean by construction (the statement elaborates from
`WordCountProgram` + `FuelMeasure` alone).

**SEED-WRAP CAVEAT REFUTED (correction of this file's own earlier
text).** The previous record claimed the `i%3` family "collides at
`seed ≥ 2^64 − 2`" and that G1 would need `hseed : seed < 2^64 − 2`.
That is WRONG: family values are `(seed + r) mod 2^64` for
`r ∈ {0,1,2}`, equal only when `r ≡ r' (mod 2^64)` — impossible for
distinct `r, r' ≤ 2`. No collision exists at ANY seed; the wrap belongs
in the family definition, and the returned max count is `(n+2)/3`
UNCONDITIONALLY. Now a theorem (`wcFamily_maxMult`, no seed hypothesis
at all) — this is where the no-collision analysis is actually
consumed — and independently cross-checked against `go run` at seeds
including `2^64−3/−2/−1`. -/
-- SPEC-STYLE SWAP (examples phase-2 slice 1 swap 3, 2026-08-14):
-- `wordcount_ok` is now the S3 RELATIONAL harness `wordcount_harness_r`
-- (`Examples/WordCount/HarnessR.lean`) — the Go returns the WORDS it
-- counted alongside the subject's answer, so the postcondition relates
-- RETURNED DATA (`best = maxMultiplicity words`) and BOTH `wcFamily`
-- and its closed form `wcFamily_maxMult` leave the statement entirely.
-- Honesty carried IN the statement: the fixed-cap `hcap : n ≤ 8` (Go's
-- pass-by-value fragment cannot return unbounded data), and `∃ words`
-- is still family-DETERMINED — the statement merely avoids saying so.
-- The teaching point survives the swap and is now load-bearing for
-- READING it: the claim holds at every choice stream (every map
-- iteration order) precisely because `maxMultiplicity` is
-- order-invariant. Fuel bound shipped `218·n + 302` (branch-uniform);
-- the measured counts are bounded by `206·n + 314` but are NOT affine
-- (first differences 206, 206, 194 — the family stops adding map
-- entries after the third word). The previous closed-form headline is
-- KEPT unweakened as `wordcount_ok_v1` / `wordcount_readout_v1`.
example := @GoLean.Examples.WordCount.multiplicity
example := @GoLean.Examples.WordCount.maxMultiplicity
example := @GoLean.Examples.WordCount.wcFamily
example := @GoLean.Examples.WordCount.wcFamily_maxMult
example := @GoLean.Examples.WordCount.wordcountHarnessFunc
example := @GoLean.Examples.WordCount.maxCount_total_canonical
example := @GoLean.Examples.WordCount.wordcount_empty_ok
example := @GoLean.Examples.WordCount.wordcount_ok
example := @GoLean.Examples.WordCount.wordcount_readout
example := @GoLean.Examples.WordCount.goArr8
example := @GoLean.Examples.WordCount.wcHarnessRFunc
example := @GoLean.Examples.WordCount.wordcountHarnessR_pin
example := @GoLean.Examples.WordCount.wordcount_ok_v1
example := @GoLean.Examples.WordCount.wordcount_readout_v1
/-- info: 'GoLean.Examples.WordCount.wcFamily_maxMult' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.WordCount.wcFamily_maxMult
/-- info: 'GoLean.Examples.WordCount.maxCount_total_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.WordCount.maxCount_total_canonical
/-- info: 'GoLean.Examples.WordCount.wordcount_empty_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.WordCount.wordcount_empty_ok
/-- info: 'GoLean.Examples.WordCount.wordcount_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.WordCount.wordcount_ok
/-- info: 'GoLean.Examples.WordCount.wordcount_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.WordCount.wordcount_readout
/-- info: 'GoLean.Examples.WordCount.wordcount_ok_v1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.WordCount.wordcount_ok_v1
/-- info: 'GoLean.Examples.WordCount.wordcount_readout_v1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.WordCount.wordcount_readout_v1

end GoLean.Iris.Audit
