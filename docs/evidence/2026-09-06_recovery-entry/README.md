# Recovery actual entry evidence

[AGENT] coordinator, 2026-09-06. Seven new semantic modules on reviewed
helper base `4f7aedef`, together with tests and gate/audit integration.
Independent source review `997d74ed` accepts this bounded setup/call-entry
increment; it does not accept its author's own independent helper review as
a substitute for entry review.

The final dedicated gate (session 14984) completed with exit 0: nine fresh
module elaborations, 37 required exports, 11,241 imported/local declarations,
all nine compiled poison controls, and fourteen kernel regression theorems.
The actual program driver is instantiated for all three A2 entries and both
`Shared` inputs. Further cases cover mixed result zeros and exact inputs,
invalid external pointer arguments and colliding keys, empty setup at zero
fuel, captured-root call entry and real heterogeneous block shadowing.

Ordinary CI (session 38639) subsequently completed with exit 0, including
the warning-free default build, all standing proof/frontend/pin gates, the
new entry gate and 202 evals. The thirteen source/gate inputs remained
byte-identical throughout the run and independent review. The two script
files' executable mode was set after validation; CI invokes them through
bash/Python, so this did not change tested source or behavior.

The 3,607-case executable record (3,363 PASS / 244 known FAIL) and 394-case
negative record are explicitly cached renderer integration evidence. All
original evidence hashes were checked before copying, and the entire
source inventory was compared. Nine recorded differences affect earlier
proof/API/gate files only; interpreter, frontend and differential harness
source remain unchanged. `runtime-reuse.json` records them and makes no
rebuilt-binary identity claim. Original source/dirty labels remain intact.
Three report-only MEDIUM reconciler findings and no HIGH finding remain.

All Lean/Lake commands ran through `scripts/capped` with
`GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3`, at the unchanged toolchain pins.
`sources.sha256` binds the full relevant source inventory relative to this
worktree; `frozen-source.sha256` is the exact thirteen-input review/CI seal.
Earlier failed proof elaborations are retained as debugging evidence and
are not passing checks. `SHA256SUMS` seals the evidence files.

The exact statements, premises, profile and remaining obligations are in
`docs/2026-09-06_recovery-entry-contract.md`. Public promotion, complete
recovery control/preservation, reusable Iris rules, B7/I1 and final sprint
gates remain required. This increment makes no main-merge or stable-pin claim.
