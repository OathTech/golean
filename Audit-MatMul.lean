import Lean
import GoLeanProofs.Examples.MatMul

/-!
# In-build axiom gate — the MatMul example

Per-example shard of `proofs/Audit.lean` (Gallery Campaign G1, unit
G1.9, proof lane A2, 2026-08-15), in the shape the phase-2 shards use.
The shard imports ONLY this example's root — which reaches the
HEADLINE, because the headline is stated in the root rather than in a
leaf shard (the C-H4/C-H5 shape, adopted from birth).

`✓` **`matmul_ok` — the S3 RELATIONAL headline over
`matmul_harness_r(seed)`** (`Examples/MatMul.lean` over the pinned
`matmulLowered`): for EVERY `seed < 2^64`, past the fuel bound `5247`,
at EVERY nondeterminism-choice stream, the harness run over
`runFunctionWithContextM` returns three `[3][3]uint64` values
`(a, b, c)` with `c = matSpec a b` — each entry of `c` the mathematical
sum `Σₖ aᵢₖ·bₖⱼ` reduced ONCE mod 2^64, a relation over the RETURNED
data. This is the gallery's FIRST 2-D (nested-aggregate) example; Go
arrays are VALUES, so the `[3][3]uint64` results cross the call/return
boundary by copy with no fixed-cap workaround.

**THE ARITHMETIC WRAPS, AND THE CLAIM SAYS SO — the headline honesty
clause.** Every uint64 multiply and accumulation genuinely reduces mod
2^64; `matSpec` performs ONE final reduction per entry, and the theorem
covers the FULL `seed < 2^64` domain — no hypothesis excludes the wrap
region. The per-step wrapping equals the single reduction because
normalization is idempotent and mod distributes over sum and product —
`mm_c_final`, proved, not assumed (the wrapped-claim shape: `dotprod`'s
stance, not `powmod`'s). The corpus wrap rows (`scalar-diag-wrap`,
`seed-trace-wrap`, `harness-wrap`, computed against `cases.tsv`) pin
the wrap differentially but only up to `seed = 2^63−1` — the
differential driver's arguments are int64-limited — so the region
`2^63 ≤ seed < 2^64` is claimed by the theorem and was probe-checked by
`#eval` (at `2^64−1`, `2^64−2`, `2^64−6`), not oracle-pinned.

**`matSpec` is mathematics, not a loop restatement**: the machine's
per-step accumulator shape (`mmAcc` — multiply wrapped, sum wrapped,
cell store wrapped) is proof-side only, bridged by `mm_c_final`, and
does not appear in the statement.

**`∃ a b` is family-determined**: the witnesses are `aClean seed`
(`a[i][j] = seed + (3i+j)`, wrapped) and the CONSTANT
`b = [[1,2,3],[4,5,6],[7,8,9]]` (`seedMat 1` — `b` IS a constant
matrix, stated plainly here); the statement merely avoids saying so.
Genuinely ∀-quantified input matrices need the ghost rung-1 annotation,
which is designed and not built.

**The fuel bound `5247` is EXACT and constant** — `matN = 3` is a
compile-time constant, so the control flow is fully concrete; the
constant is cubic in the fixed dimension (`matN³ = 27` inner
iterations). Bound and probe measurement COINCIDE (both 5247, at
`seed = 0`, `5`, `2^63−1`); the proof's 82 chained segment counts sum
to it. Neither is presented as the other. **`∀ ch` is vacuous and
stated anyway** — the run consumes no choice.

Deletion test NOT yet run by the lane owner (the proof author believes
`hseed` is load-bearing — it discharges the seed argument's uint64
normal form at the entry equation and every `omega` bridge — and that
`seed` is trivially load-bearing; the lane owner re-runs the deletion
test rather than inheriting this).

Statement closure: interpreter/native-entry vocabulary
(`runFunctionWithContextM`, `Choices`, `Result`) + the pinned
`matmulHarnessRFunc` (`rfl`-linked to the lowering by
`matmulHarnessRFunc_pin`) + `mmArr3` + `matSpec`/`mmGet` +
`List`/`Int` arithmetic — no heap vocabulary, no Iris, no frame names,
no `mmAcc`, no `unn`, and no family function.

NOT DESIGNATED: this example is deliberately absent from
`Examples/Targets.lean`, from `scripts/ci`'s Targets allowlist, from
`Audit.lean`'s designated-name list and from the Comparator Challenge's
trusted closure (gallery-campaign charter §HARD BOUNDARIES —
designation is arc-end work under user sign-off).
-/

namespace GoLean.Iris.Audit

/-! ## The matmul example (Gallery Campaign G1, lane A2) -/

-- Statement vocabulary
example := @GoLean.Examples.MatMul.mmGet
example := @GoLean.Examples.MatMul.matSpec
example := @GoLean.Examples.MatMul.mmArr3
example := @GoLean.Examples.MatMul.matmulHarnessRFunc
example := @GoLean.Examples.MatMul.seedMatFunc
example := @GoLean.Examples.MatMul.matMulFunc
-- The three lowering pins (the golden chain's third link)
example := @GoLean.Examples.MatMul.matmulHarnessRFunc_pin
example := @GoLean.Examples.MatMul.seedMat_pin
example := @GoLean.Examples.MatMul.matMul_pin
-- Proof vocabulary the honesty clauses name
example := @GoLean.Examples.MatMul.aClean
example := @GoLean.Examples.MatMul.mmAcc
example := @GoLean.Examples.MatMul.mmSet
example := @GoLean.Examples.MatMul.mmNorm
example := @GoLean.Examples.MatMul.un_idem
example := @GoLean.Examples.MatMul.unn_collapse
example := @GoLean.Examples.MatMul.mm_a_final
example := @GoLean.Examples.MatMul.mm_c_final
example := @GoLean.Examples.MatMul.unorm_mul_nat
-- The headlines
example := @GoLean.Examples.MatMul.matmul_ok
example := @GoLean.Examples.MatMul.matmul_readout

/-- info: 'GoLean.Examples.MatMul.matmul_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.MatMul.matmul_ok
/-- info: 'GoLean.Examples.MatMul.matmul_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.MatMul.matmul_readout
/-- info: 'GoLean.Examples.MatMul.mm_c_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.MatMul.mm_c_final
/-- info: 'GoLean.Examples.MatMul.mm_a_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.MatMul.mm_a_final
/-- info: 'GoLean.Examples.MatMul.un_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.MatMul.un_idem
/-- info: 'GoLean.Examples.MatMul.unorm_mul_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.MatMul.unorm_mul_nat
/-- info: 'GoLean.Examples.MatMul.matmulHarnessRFunc_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.MatMul.matmulHarnessRFunc_pin
/-- info: 'GoLean.Examples.MatMul.seedMat_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.MatMul.seedMat_pin
/-- info: 'GoLean.Examples.MatMul.matMul_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.MatMul.matMul_pin

end GoLean.Iris.Audit
