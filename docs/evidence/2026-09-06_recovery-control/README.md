# Recovery structural control evidence

Bounded increment on reviewed setup source `63769964`. Source and regression
definitions are in the accompanying commit; `source.sha256` pins all 21
semantic/test/audit/gate/build inputs. Every hash was checked again after CI.

The dedicated gate passed: 17 fresh source elaborations, 124 required
theorem exports, 13,824 declarations across all imported local GoLean/Tests
origins, classical trio only. All 17 compiled poisons were rejected: unused
private axioms in each of fifteen core modules and the audit module, plus
a trailing test `sorry`. `poison-logs/` preserves their compile and rejection
logs. `gate-inventory-failure.log` retains an earlier gate failure caused by
the generated inventory selecting the prose words “theorem goal”; the fix
removed that nonexistent export and changed no semantic source.

Ordinary CI passed with exit 0, including all interface/admission/Boolean/
recovery gates, frontend pins/unit checks and 202 evaluator tests. The 3,607
executable and 394 negative differential records were reused from the sealed
renderer integration. Their original dirty source provenance is explicit
in `ci.log` and the metadata. `runtime-reuse.json` verifies every sealed
input checksum and the four cached record files; differences from the
original source inventory are proof, facade, test or gate wiring. This is
not a fresh full corpus run and does not assert rebuilt binary identity.

Independent bounded review PASS is sealed in commits `9e6c4234` and
`ba930ba2`, under `docs/evidence/2026-09-06_recovery-control-independent/`.
The reviewer rebuilt all 17 exact source modules against independently
compiled committed dependencies without borrowing author control oleans.
Fourteen additional kernel probes passed, and their full imported/local
closure audit covered 13,855 declarations. The reviewer checked all 21
frozen input hashes against this source.

The result is generic admitted setup-to-invariant, arbitrary-successor
preservation, terminal/abort-sensitive progress, and typed readout with
unchanged choices for successful actual sequential drivers. The contract
and limitations are described in
[the control contract](../../2026-09-06_recovery-control-contract.md).
The remaining abort renderer/observer and unconditional driver classification
work is explicit; the shared functional Iris customer is not completed by
this increment.
