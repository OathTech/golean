# Final A3/interface combined-tree evidence

[AGENT], 2026-09-05. Reviewed/tested branch tip `7c5e2971` plus the facade
and audit integration edits, over main `4919b05a`. The exact final code is
bound by `integrated-source-bindings.json` (81 inputs). Documentation is
outside that source inventory. `SHA256SUMS` binds this evidence directory;
check it from this directory. All implementation bindings were rechecked
after validation and remain unchanged at the final commit.

The independent report is preserved unchanged as `review.md`.
`check-integration-bindings.log`, `binding-comparison.json` and the checker
record preservation of all A3 inputs: five differences in the older broad
manifest are exactly the landed BUG-103/interface code and the two merged
configuration additions. `facade-import-graph.json` confirms the 20-module
local facade closure has no Iris/customer/frontend dependency.

`coordinator-ci.log`: ordinary capped CI PASS, 202 eval checks, interface
audit 19 exports / 526 constants, admission audit 14 / 375 and all compiled
poison controls. Full executable and negative comparisons are explicitly
cached at `8d8f5487` (3598 and 394 records); the fresh full runtime run is
preserved in `../2026-09-05_bug103-integration/`. Its one cached slow-tier
certificate and two existing report-only record findings remain visible.

`admission-gate.log`, `a1-gate.log`, `a2-gate.log`: independent complete
gates, each exit 0. All relevant modules freshly elaborate. A1 audits 862
constants and A2 audits 1274, retaining their 12/18 required exports and
three poison controls each. Admission audits 375 constants with 14 required
exports and three poison controls. Both complete native artifact comparisons
pass; `a3-latest.tsv` and `a2-latest.tsv` record fresh 1/1 and 3/3 differential
PASS results with their original metadata. No additional full-corpus run is
claimed. Builds used independent existing caches at exact pins, not a clean
network bootstrap or full upstream re-elaboration.

`admission-audit-probe.py` is the exact extra mutation reproducer: the unused
private Admission axiom compiled successfully and all four audits rejected
it. The textual compile/rejection logs are retained; copied compiled trees
are excluded. The reproduction scripts retain their original `.tmp/<lane>`
layout assumptions. Copy them into a fresh directory one level below the
worktree's `.tmp` before running; do not run them directly in this evidence
directory. `integration.diff` is a verbatim diff artifact, including its
context-line spaces. The raw diff is preserved byte-for-byte.
The landing whitespace check excludes only that verbatim diff, whose six
context-only lines are intentionally single spaces; all source edits pass.

Normal gate reproduction from the repository root:

```sh
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped scripts/ci
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 bash scripts/check-admission
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 bash spikes/gate-a1/check
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 bash spikes/iris-customer/check
```
