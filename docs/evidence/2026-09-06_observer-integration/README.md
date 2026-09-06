# Reviewed observer integration, 2026-09-06

Root integration parent `99e0225d`, reviewed feature tip `2b679404`.
The pending merge contains the authenticated oracle terminal classifier and
the diagnostic-tool adapter. Three original reviewed input manifests match
this integration except for `scripts/ci`: the archived diff is additive and
retains all existing interface/admission/Boolean/recovery hooks.

Fresh integration command:

```
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 GOLEAN_COVERAGE_JOBS=2 scripts/capped scripts/ci --diff
```

Session 74005 completed with exit 0. The raw log includes the warning-free
default build, existing proof/audit gates, both observer gates, frontend
units/pins, lowering diagnostics, 202 eval cases, lane negative controls,
oracle artifact regeneration and baseline/re-pin checks. The executable
runner itself exits 1 for its known reds, as expected; CI compares that
complete result to the declared baseline rather than treating reds as passes.

The full executable result is 3,627 cases = 3,382 PASS / 245 FAIL. All 394
negative rows match their baseline. This is ordinary `--diff`, with its
existing explicitly cached slow certification, not fresh slow enumeration.
Original metadata is unchanged: it names dirty parent `99e0225d` and direct
runner fields `full_run/total_corpus_cases/filters=unknown`. The source
manifest binds the actual worktree; no clean-commit provenance is invented.

The harness cleaned up its temporary manifests. I regenerated the complete
manifests using `scripts/coverage-manifest --artifact-root artifacts/coverage`
and `scripts/coverage-negative-manifest`; their bytes match the SHA-256
values in the original run metadata. `verify.py` checks unique inventories,
all result/stage rows (including declared stage alternations), exact manifest
hashes and reviewed baseline movement. It passes against these archived
records: exactly eleven new marker PASS cases, no removed cases, and only
`sync/mutex-unlock-fatal/during-panic-unwind` PASS→FAIL/go-observation.
BUG-106 records that deliberate refusal of an unauthenticated fatal outcome.

The pre-run source inventory contains 3,844 files. The build-configuration
addendum records `lakefile.toml` and `lake-manifest.json`, both unchanged
from the parent. Revalidation after terminal CI found no source drift.
The only later edits before integration sealing are documentation/evidence.

The original report-only reconciliation found two HIGH arithmetic findings:
the ledger still named 3,616/3,372/244 and omitted the additional BUG-106
refusal from its bucket count. The ledger correction preserves historical
movements, updates current arithmetic to 3,627/3,382/245 and post-vintage
65→66, and names the exact case/stage/cause. Fresh `reconciler-final.json`
has no HIGH findings; its remaining MEDIUM historical-toolchain and frontier
citation observations remain visible. No checker or baseline was weakened.

Replay `python3 docs/evidence/2026-09-06_observer-integration/verify.py` at
this integrated source to recheck the archived evidence; use the full CI
command above for a fresh run. `SHA256SUMS` seals this evidence directory.
These checks approve this observer integration only. Full O2, R1 fidelity,
B7/I1 migration and final sprint validation/closing decisions remain owed.
