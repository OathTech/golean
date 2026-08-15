import Lean
import GoLeanProofs.Examples.DotProduct

/-!
# In-build axiom gate — the DotProduct example

Per-example shard of `proofs/Audit.lean` (Gallery Campaign G1, proof
lane A, 2026-08-15), in the shape the phase-2 shards use. The shard
imports ONLY this example's root — which reaches the HEADLINE, because
the headline is stated in the root rather than in a leaf shard (the
C-H4/C-H5 shape, adopted from birth).

It is built because the root `Audit.lean` imports it — and
`scripts/ci`'s proofs-file audit-coverage step FAILS if any
`proofs/**/*.lean` leaves the audited import closure, so dropping that
import cannot silently retire these pins.

`✓` **`dotprod_ok` — the S3 RELATIONAL headline over
`dotprod_harness_r(n, seed)`** (`Examples/DotProduct.lean` over the
pinned `dotprodLowered`): for every `n ≤ 8` and EVERY `seed < 2^64`,
past the fuel bound `237·n + 398`, at EVERY nondeterminism-choice
stream, the harness run over `runFunctionWithContextM` returns three
values — the length-`n` lists `av`/`bv` as zero-padded `[8]uint64`
arrays, and `dotSpec av bv = (Σ avᵢ·bvᵢ) % 2^64`, a relation over the
RETURNED data.

**THE ARITHMETIC WRAPS, AND THE CLAIM SAYS SO — the headline honesty
clause.** The uint64 multiply and accumulation genuinely reduce mod
2^64; `dotSpec` is the mathematical dot product with ONE final modular
reduction, and the theorem covers the FULL `seed < 2^64` domain — no
hypothesis excludes the wrap region (the corpus rows `four-wrap`,
`one-wrap`, `harness-r-wrap-max`, `harness-r-wrap-62` pin it
differentially; probe-checked at `seed = 2^64−1` and `2^64−2`). The
single final reduction equals the machine's per-step wrapping because
mod distributes over the sum — `dpAcc_eq`, proved, not assumed. This is
the WRAPPED-claim shape (`Fib`'s choice); `PowMod` makes the opposite
choice (excludes its wrap region) with its own disclosure.

**`dotSpec` is mathematics, not a loop restatement**: the loop-shaped
per-step accumulator `dpAcc` is proof-side only, bridged by
`dotSpec_fam`, and does not appear in the statement.

**`∃ av bv` is family-determined**: the witnesses are
`dpFamA n seed = [seed, seed+1, …]` (wrapped) and `dpFamB n = [1…n]`;
the statement avoids saying so, exactly as Histogram's headline does.
The cap `n ≤ 8` is the pass-by-value observation bound. The subject's
min-length guard is NOT exercised by this harness (both slices have
length `n`); the `uneven` corpus row pins that branch differentially.

**The fuel bound `237·n + 398` is EXACT for this harness** — every
iteration is branch-free, so the composed count is an equality, and the
probe-measured counts coincide at `n = 0…8` (398, 635, 872, 1109, 1346,
1583, 1820, 2057, 2294). Bound and measurement agree here; neither is
presented as the other. **`∀ ch` is vacuous and stated anyway** — the
subject consumes no choice.

Deletion test RUN (`lean_minimal_hypotheses`, lane owner, 2026-08-15 —
re-run rather than inherited from the proof author, who had asserted it
by inspection): all THREE explicit binders — `n seed`, `hcap`, `hseed`
— are LOAD-BEARING; dropping any one breaks the proof. `hcap` feeds
every `n ≤ 8` prefix-length fact and the counter normalizations;
`hseed` discharges the seed argument's uint64 normal form at the entry
equation.

Statement closure: interpreter/native-entry vocabulary
(`runFunctionWithContextM`, `Choices`, `Result`) + the pinned
`dotprodHarnessRFunc` (`rfl`-linked to the lowering by
`dotprodHarnessRFunc_pin`) + `dpArr8` + `dotSpec` + `List`/`Int`
arithmetic — no heap vocabulary, no Iris, no frame names, no `dpAcc`
and no family function.

NOT DESIGNATED: this example is deliberately absent from
`Examples/Targets.lean`, from `scripts/ci`'s Targets allowlist, from
`Audit.lean`'s designated-name list and from the Comparator Challenge's
trusted closure (gallery-campaign charter §HARD BOUNDARIES —
designation is arc-end work under user sign-off).
-/

namespace GoLean.Iris.Audit

/-! ## The dotprod example (Gallery Campaign G1, lane A) -/

-- Statement vocabulary
example := @GoLean.Examples.DotProduct.dotSpec
example := @GoLean.Examples.DotProduct.dpArr8
example := @GoLean.Examples.DotProduct.dotprodHarnessRFunc
example := @GoLean.Examples.DotProduct.dotProductFunc
-- The two lowering pins (the third link of the golden chain)
example := @GoLean.Examples.DotProduct.dotprodHarnessRFunc_pin
example := @GoLean.Examples.DotProduct.dotProduct_pin
-- Proof vocabulary the honesty clauses name
example := @GoLean.Examples.DotProduct.dpFamA
example := @GoLean.Examples.DotProduct.dpFamB
example := @GoLean.Examples.DotProduct.dpAcc
example := @GoLean.Examples.DotProduct.dpAcc_eq
example := @GoLean.Examples.DotProduct.dotSpec_fam
example := @GoLean.Examples.DotProduct.unorm_mul_nat
-- The headlines
example := @GoLean.Examples.DotProduct.dotprod_ok
example := @GoLean.Examples.DotProduct.dotprod_readout

/-- info: 'GoLean.Examples.DotProduct.dotprod_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.DotProduct.dotprod_ok
/-- info: 'GoLean.Examples.DotProduct.dotprod_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.DotProduct.dotprod_readout
/-- info: 'GoLean.Examples.DotProduct.dotSpec_fam' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.DotProduct.dotSpec_fam
/-- info: 'GoLean.Examples.DotProduct.dpAcc_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Examples.DotProduct.dpAcc_eq
/-- info: 'GoLean.Examples.DotProduct.unorm_mul_nat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.DotProduct.unorm_mul_nat
/-- info: 'GoLean.Examples.DotProduct.dotprodHarnessRFunc_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.DotProduct.dotprodHarnessRFunc_pin
/-- info: 'GoLean.Examples.DotProduct.dotProduct_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.DotProduct.dotProduct_pin

end GoLean.Iris.Audit
