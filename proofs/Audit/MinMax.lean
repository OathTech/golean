import Lean
import GoLeanProofs.Examples.MinMax

/-!
# In-build axiom gate — the MinMax example

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

/-! ## The min/max example (scale-out slice 2c, 2026-08-13)

`✓` **`minmax_ok` — the §9 memory-quantified headline, reverse shape,
read-only input** (`Examples/MinMax.lean` over the pinned
`minMaxLowered`): for any NONEMPTY `[]uint64` input list, at ANY
placement (`base ∉ {0, 1}` — the harness result cells sit there),
beside ANY disjoint frame: execution completes normally past one fuel
bound at every choice stream, the result cells hold exactly
`minSpec xs` / `maxSpec xs`, the input's backing cell is UNCHANGED
(the read-only story pinned IN the statement — total-heap
preservation), and every frame cell is preserved verbatim. `hne` is
Go's own boundary — the empty slice PANICS at `s[0]` (corpus row
`examples/minmax/empty-panics` pins it against `go run`);
`hlen : xs.length < 2^63` is the reverse precedent. Route (recorded):
direct machine-step segments + ONE strong induction on `len − m`
carrying value and completion; frame transfer through the
input-relocating renaming with cells 0/1 ρ-fixed. D1 twin:
`minmax_readout` via `normal_readout_of_total`. -/
-- HARNESS RESTATEMENT (form note §11): `minmax_ok` is now the harness
-- headline (minmax_harness: setup family s[i] = seed + i, returned
-- min/max pair = minSpec/maxSpec of `mmFamily n seed` — the recorded
-- input-family honesty vs the designed-not-built ∀xs input pick);
-- memory-quantified forms kept proof-side as `minmax_framed` /
-- `minmax_framed_readout`.
example := @GoLean.Examples.MinMax.minmax_ok
example := @GoLean.Examples.MinMax.minmax_readout
example := @GoLean.Examples.MinMax.minmax_framed
example := @GoLean.Examples.MinMax.minmax_framed_readout
/-- info: 'GoLean.Examples.MinMax.minmax_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.MinMax.minmax_ok
/-- info: 'GoLean.Examples.MinMax.minmax_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.MinMax.minmax_framed

end GoLean.Iris.Audit
