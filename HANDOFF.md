# A2 Iris customer handoff

[AGENT], 2026-09-05. User authorized planning and implementing a minimal
Iris test customer plus an independent known-issues fix thread. Branch
`gate-a2-iris`, base `8db2d6da`. Main remains untouched.

Status: bounded implementation complete; dedicated gate PASS. Independent
adversarial review and integration are OWED. No merge/push authorized.

Plan and completed assessment: `docs/2026-09-05_iris-customer-design.md`.
Package: `spikes/iris-customer/` (separate Lake package, outside default core
build). Evidence: `docs/evidence/2026-09-05_iris-customer/README.md`.

Implemented current-heap `gen_heap` ownership, all-context pinning, a
concrete Iris resource bundle, read/write/allocation lifting, explicit
recovery and frame rules, WP proofs for native-lowered normal/recovered
named results, initialized adequacy and whole-program readout. The main
theorem is `GoLean.IrisCustomer.recovered_program`: actual
`runProgramPoolOutM 60` returns `[true]` with empty output. Its value passes
through Iris adequacy; bounded termination and silence have separate kernel
checks. There is also a whole-program uncaught-panic control and an arbitrary
preserved frame-cell adequacy example.

Gate: core and package builds, ten fresh module elaborations plus aggregate,
18 required exports, 941 constants audited against the classical trio,
three compiled poisoned imports rejected, freshly lowered native artifact
matched, and 3/3 differential cases passed on go1.26.5. Fingerprint:
`defdc809abf9e1ecc019c25454e4a0993d0e85ce82b09e4fa6abac54d023b043`.
Dependency pins are exact and tracked-clean; clean network bootstrap was
not tested. No semantics runtime, frontend or baseline edits in this lane.

Next: pose the charter's unconditional pre-merge adversarial audit ask; do
not merge without explicit sign-off. Review ownership non-vacuity, the Iris
dependency of the result, source/artifact provenance, exact pool/output
scope and the gate. Then promote semantics-owned A1 bridges/facade, specify
A3's admission slice, and exercise this customer across B7/C1. General
composition and concurrent adequacy remain open; A2 does not close all Gate A.

Parallel agent completed `bug103-array-conversion` in a separate worktree,
commit `7b7bc42c3f77154099ccbb3c6f6a302a8d1987d4`, clean and unmerged.
Full differential: 3,598 cases, 3,353 PASS / 245 FAIL; one prior failure fixed
plus five new passing cases and no other drift. Final capped CI passed;
394 negative oracle checks passed; one slow-tier cached certificate was
retained, not re-certified. Its own note/evidence are on that branch.
All Lean/Lake invocations must use `scripts/capped`; independent copied
build caches only. Leave scratch directories in place.
