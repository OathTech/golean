# Recovery runtime supporting lemmas

[AGENT] 2026-09-06. Bounded supporting increment on `typed-recovery-runtime`,
base `212842a9`: reviewed public O1 source plus reviewed static recovery
admission `e8a665e9`. This is not a complete recovery invariant or O2 contract.
The design and remaining obligations are recorded in
`docs/2026-09-06_recovery-runtime-design.md`.

The six modules establish structural mixed heap/environment typing, actual
load/store/allocation/binding helper contracts, typed strict operators,
compatible first-match context inclusion and source-to-runtime statement
typing erasure. `World` is an explicit address type map, not a future-safety
certificate. A live root-reference value must point to an actual Boolean
cell; all hidden bindings are separately bounded. Actual stores preserve the
schema, so captured aliases retain their pointee types. Statement weakening
does not claim old heterogeneous types survive new declarations.

The complete focused command exited 0:

```text
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/check-recovery-storage
```

`gate.log` records the source SHA-256 values, eight fresh source elaborations,
32 required theorem exports and 6,789 imported/local declarations checked
against the classical trio only. Eight adversarial poisons each compiled
before rejection by a fresh importing audit: unused private declarations in
all six new helper modules, the audit's own private tail, and a trailing
test theorem using `sorry`. The source checkout and cache were not mutated
for these controls; each poison used a private retained scratch tree.

Twelve kernel regressions challenge dangling/wrong-type/nil root references,
hidden dangling bindings, actual mixed shadowing, incompatible declaration
effects, shared alias retention through actual stores, arbitrary payload-byte
comparability and zero initialization. They do not replace whole-program
runtime obligations. `static-source-rebuild.log` records the preceding
29-job rebuild of the committed static dependency sources after temporary
development copies were replaced by the actual source merge.

`sources.sha256` binds this bounded implementation and its gate inputs.
Ordinary CI exited 0 against these unchanged hashes:

```text
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped scripts/ci
```

`ci.log` records all proof gates, 202 eval tests and comparison against the
explicitly cached renderer-integration records: 3,607 full and 394 negative
cases without baseline regression; three report-only findings, zero HIGH.
These records describe the sealed dirty renderer worktree at `c7eeaf578`,
not a fresh corpus run at this helper tip. Before copying, every hash in that
record's `SHA256SUMS` was verified. `runtime-reuse.json` checks its entire
source inventory and records the nine expected proof/API/gate differences;
interpreter, frontend and differential harness inventory members are unchanged.
The copied records preserve their original metadata and are named `cached-*`.

Independent source review PASS is sealed at parent `efc2712c`, under
`docs/evidence/2026-09-06_recovery-storage-independent`. The reviewer read all
six modules, tests and gates, then freshly concatenated and elaborated their
complete source bodies without author helper oleans. Eleven independent
kernel challenges passed, and all 6,780 imported/local declarations in that
review were audited against the classical trio. The reviewer inspected this
gate and ordinary CI evidence and verified all twelve frozen source hashes.
This accepts only the bounded supporting increment. It does not accept the
in-progress control invariant or parent-owned generic setup. No executable
frontend/stepFn behavior is changed.

Ownership: this agent owns these supporting modules and control preservation;
the parent owns generic actual program/call setup in its separate worktree.
`RecoveryStore`, `RecoveryEnvironment` and `RecoveryAllocation` are frozen
at this evidence's hashes while the parent proves setup against exact copies.
Final committed-source integration and rebuild remain mandatory in both lanes.
