import Lean
import GoLeanProofs.Examples.MinMax
import GoLeanProofs.Examples.MinMax.HarnessR

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
--
-- SPEC-STYLE SWAP (examples phase-2 slice 1, 2026-08-14): `minmax_ok`
-- is now the S3 RELATIONAL harness `minmax_harness_r`
-- (`Examples/MinMax/HarnessR.lean`) — the Go returns the PRE-STATE
-- alongside `(lo, hi)`, so the postcondition relates RETURNED DATA
-- (`lo = minSpec pre`, `hi = maxSpec pre`) and `mmFamily` leaves the
-- statement entirely. Honesty carried IN the statement: the fixed-cap
-- `hcap : n ≤ 8` (Go's pass-by-value fragment cannot return unbounded
-- data), and `∃ pre` is still family-DETERMINED — the statement merely
-- avoids saying so. The previous family-in-the-statement headline is
-- KEPT unweakened as `minmax_ok_v1` / `minmax_readout_v1`.
example := @GoLean.Examples.MinMax.minmax_ok
example := @GoLean.Examples.MinMax.minmax_readout
example := @GoLean.Examples.MinMax.goArr8
example := @GoLean.Examples.MinMax.mmHarnessRFunc
example := @GoLean.Examples.MinMax.minmaxHarnessR_pin
example := @GoLean.Examples.MinMax.minmax_ok_v1
example := @GoLean.Examples.MinMax.minmax_readout_v1
example := @GoLean.Examples.MinMax.minmax_framed
example := @GoLean.Examples.MinMax.minmax_framed_readout
/-- info: 'GoLean.Examples.MinMax.minmax_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.MinMax.minmax_ok
/-- info: 'GoLean.Examples.MinMax.minmax_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.MinMax.minmax_readout
/-- info: 'GoLean.Examples.MinMax.minmax_ok_v1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.MinMax.minmax_ok_v1
/-- info: 'GoLean.Examples.MinMax.minmax_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.MinMax.minmax_framed
-- The two derived twins' pins, ADDED in the 2026-08-15 audit response:
-- `minmax_readout_v1` and `minmax_framed_readout` were referenced as
-- `example :=` witnesses (so they are built) but never axiom-pinned,
-- while their headlines were — a gap on the "everything the gallery
-- names is pinned" story, not on the proofs themselves.
/-- info: 'GoLean.Examples.MinMax.minmax_readout_v1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.MinMax.minmax_readout_v1
/-- info: 'GoLean.Examples.MinMax.minmax_framed_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.MinMax.minmax_framed_readout

end GoLean.Iris.Audit
