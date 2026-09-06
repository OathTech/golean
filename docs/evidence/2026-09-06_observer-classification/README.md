# BUG-106 observer evidence index

2026-09-06. The production hybrid candidate has bounded independent
implementation PASS (`1bd2022b`). Its fresh full differential is complete:
3,627 rows = 3,382 PASS / 245 FAIL. Initial CI exited 1 for raw baseline
drift, BUG metadata punctuation, and stale registration-free success mocks.
The initial result remains intact; final ordinary CI exits 0 after the narrow
bookkeeping/test corrections. No partial or stopped run is a full baseline.

| Evidence group | Meaning |
| --- | --- |
| `default-draft-*`, `glued-real.json`, `glued-classifier-red.json` | Rejected default-trace classifier and actual glued-prefix fatal counterexample |
| `system-draft-before-printed-panic.go.txt`, `interrupted-*`, `ci-interrupted-known-unsound.log` | Rejected system-only source, initial forgery and full run stopped at exit 143 after 256 finalized rows |
| `runtime-sources.json`, `crash-channel-design-probes.json` | Installed Go 1.26.5 source pins and bounded crash-copy timing evidence |
| `hybrid-prototype.py`, `hybrid-probes.py`, `hybrid-current-rows.json`, `hybrid-challenges.json`, `hook-source-boundary.json` | Design-only prototypes and native evidence; not production or Go/Lean acceptance |
| `hybrid-row-inventory.json` | Early preliminary inventory; superseded by `hybrid-current-rows.json`, which correctly handles singleton `-` IDs and init tags |
| `minimal-red.log` | Fresh failing minimal printed-continuation regression on the old helper |
| `hybrid-production-sources.json`, `hybrid-gate-final.log` | Exact frozen production source hashes and final capped source-bound helper/shell/native/mutation gate |
| `hybrid-native-records.json` | Full raw source/descriptor/crash/ack bytes in hex for all 28 native and two setup-IO cases from that production gate |
| `focused-hybrid.tsv`, `focused-hybrid.meta.tsv`, `focused-hybrid.log` | Complete 23-case fresh focused Go/Lean run: 22 PASS and the one explicitly justified sync-unwind FAIL/go-observation |
| `hybrid-baseline-before.tsv`, `hybrid-full-initial.tsv`, `hybrid-full-initial.meta.tsv`, `hybrid-full-initial-delta.json` | Original baseline and complete fresh 3,627-row result; exactly eleven new PASS rows and the one named PASS-to-refusal correction, all reviewed source hashes rechecked |
| `ci-hybrid-initial.log` | Complete initial CI, exit 1; preserves all three failure causes before correction |
| `lane-validation-fixed.log`, `ci-hybrid-final.log`, `hybrid-final-source-addendum.json` | Affected harness half and final ordinary CI exit 0; source manifest binds unchanged production code plus exact mock/bookkeeping corrections |
| `string-member-probes.py`, `string-member-probes.json` | Separate R-1 native source/report assessment; no semantic or observer policy implemented |

The earlier `candidate-sources.sha256`, `focused.tsv`, `focused-native.log`
and helper-test logs bind historical system-only checkpoints. They are
retained as history and do not certify the repaired hybrid source.

The live production narrative is
[`docs/2026-09-06_observer-classifier-repair.md`](../../2026-09-06_observer-classifier-repair.md).
Independent review source and adversarial probes live in the separate
reviewer commits `aafe225b` (design), `ab2ad4d5` (exact failed-observation
disposition) and `1bd2022b` (bounded production implementation).
