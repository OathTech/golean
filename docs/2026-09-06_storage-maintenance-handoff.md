# Storage maintenance — completion and resume handoff

[USER] authorized this maintenance arc on 2026-09-06. The semantics sprint
remains **user-paused**. Read [its pause state](2026-09-06_typed-sprint-pause-state.md)
and [the maintenance charter](2026-09-06_storage-maintenance-charter.md).
No merge to main, push, or semantic sprint resumption occurred.

## Result and preserved material

The two scoped, journaled cleanup applications completed with exit 0 and
no skips: **1,658,145 generated files, 715,915,902,976 allocated bytes
(666.7486 GiB)** removed. Every prepared file was subsequently checked absent.
Project size after cleanup was 372,291,313,664 bytes (346.72 GiB); after the
remaining validation/builds it was 373,735,301,120 bytes (about 348 GiB).
Free-space changes can include other
projects; reclaimed bytes come from the per-file manifests, not that delta.

Historical audit compiler output and helper binaries had uncertain source
provenance. Their exact bytes were preserved in SHA-addressed compressed
recovery objects (784,802,412 bytes) before unlink, with hash checks before
each deletion. Eight deterministic sample files restored byte-for-byte into
a separate owned probe directory. Rebuildable Go cache entries were pruned
separately. Source, logs, dependencies, registered/nested worktrees and Git
state were preserved. Sources and logs remain at their original paths;
empty directories were left in place.

Recovery packets in primary artifacts:

- `storage-maintenance-recovery-20260906-v2`: 1,597,827 files, 561.3262 GiB;
  includes compressed historical compiler/helper objects.
- `storage-maintenance-cache-executables-20260906`: 60,318 Go cache executable
  entries, 105.4224 GiB. The pinned Go cache implementation's PutExecutable
  layout, cache README and ELF signature establish their generated role.

Keep both packets and their manifests/journals. The earlier packet without
`-v2` is an interrupted read-only planning attempt; no deletion came from it.
Restoration and retention procedures are in [storage operations](storage-operations.md).
`cleanup-verification.json` and `recovery-roundtrip.json` in the evidence
packet record the actual results and exclusions.

The retirement archive (about 137 GiB), `side/gofuzz` (about 84 GiB), primary
shared Go cache, referenced lower-diagnose/sampling-budget caches, protected
I1 scratch and nested original-reference worktrees were excluded. Further
archive/experiment retirement needs a separate disposition. The private
`/proc` inspection denied by nono was not bypassed: scoped preflight used
the unchanged pause snapshot, stopped process groups, agents' idle reports
and public process trees. Complete host file-descriptor visibility is not
claimed.

## Durable producer fixes

Thirteen integration audit producers now keep one complete independently
copied package fixture at a time. Byte's additional producer is included in
its paused-lane overlay. Actual commands/exits, source bytes/hashes, resolved
Lean executable hash, package inventories, mutation/harness/logs and exact
rejection expectations are preserved before owned compiled copies are
released. Compiler success and each original named audit rejection remain
required. Preservation/cleanup failure is an infrastructure failure.

All maintained Go callers use the common cache resolver. The existing primary
cache is shared; mutable Lean builds, native wire output and observations are
worktree-specific. Fixed the overwritten helper-cleanup EXIT trap in
`check-imported-goose`.

Shared admission and whole-gate monitoring enforce cooperative limits:
20 GiB managed scratch, 10 GiB compact evidence, 50 GiB retained registered
outputs, 8 GiB growth per gate, cache warning/stop at 50/75 GiB and 100 GiB
free reserve. Completed campaign outputs remain counted. Four paused lanes'
existing outputs are registered without starting their jobs. Limits are not
OS quotas: finite scan intervals permit overshoot; uninstrumented/detached
work is outside the guarantee. No hidden evidence eviction or cap increase.

## Validation and its scope

Integration-based maintenance validation:

- Fresh core/test-library builds: 194 and 127 jobs, exit 0. Fresh independent
  Iris dependency/customer build: 329 jobs, exit 0.
- Final ordinary CI: exit 0, all audit families and 202 eval tests. Its full
  3,635 / negative 394 comparisons use explicitly identified historical R1
  cached observations, not a fresh full maintenance corpus run.
- Final expanded interface audit in CI plus runs 6 and 7: three passes,
  35 compiled named mutations each; peak scratch 279,826,432–280,682,496 bytes
  (about 267 MiB), no retained compiled fixtures, live source/build hashes
  checked unchanged by each run.
- Nine fresh member cases: 9 PASS / 0 FAIL. Only apparatus-source bindings
  changed; every native wire/control/observation/policy field is unchanged.
  `source-only-pins-verified.json` verifies all 178 current input hashes.
- Two fresh focused cases: 2 PASS / 0 FAIL. Full final Iris customer and
  Gate A1 checks: exit 0, including compiled poison audits and customer
  differential/native controls where present on this branch.

Main-based maintenance validation: ordinary CI exit 0, fresh builds and
202 eval tests, two fresh focused cases PASS. Its full 3,598 / negative 394
comparison inputs are explicitly historical cached observations. Gate A1
and the full Iris customer check both passed with exit 0.
Both worktrees resolve and actually use the same primary Go cache.

Thirteen storage tests pass, covering success, failed compile, preservation
and cleanup failure, timeout/SIGTERM, owned paths, competing reservations,
shared/explicit caches, retained-output budgets, fast writers and a child
in a new process session. Seven string-member unit tests pass. Changed
Python/shell syntax and diff whitespace checks pass.

Early failed attempts are retained and are not counted as success: the
first real interface run exposed a disappearing compiler-temporary-file
scan race (fixed); an Iris bootstrap invocation used the wrong relative
capped path, and an initial customer invocation omitted `bash`.

Full final logs, source-bound sealed audit packets and a compact verification
summary accompany `docs/evidence/2026-09-06_storage-maintenance/`. A fresh
full/slow semantic corpus is not claimed and the paused lanes' unfinished
certification is not discharged by these maintenance checks.

## Branches, overlays and resumption

`storage-maintenance-20260906` starts at accepted integration `7edc298f`;
`storage-maintenance-main-20260906` starts at main `47195683` and carries
only maintenance tooling/docs. The latter permits independent main landing
without bringing in unfinished semantic work. Final named commits will be
listed in the delivery message; main itself remains unchanged.

Tooling-only unstaged overlays are installed in `typed-consumer-sprint`,
`typed-context-store`, `typed-i1-envelope` and `typed-byte-runtime`. Their
original HEADs, exact index bytes, semantic inputs and baseline files are
unchanged. All seven original lane HEADs/indexes/open merges were checked
again in `preservation-final.json`. Original handoffs remain intact; each
active lane now has `docs/2026-09-06_storage-overlay-resume.md`.

When the user explicitly resumes the sprint: read the pause/overlay notes,
check storage admission, verify preserved state, re-freeze each lane's actual
source inputs, review justified source-only apparatus binding changes, and
execute the fresh gates already owed. No paused lane's member pin or old
certificate was silently refreshed. I1's stale native wire findings remain
separate. Start with pending uintptr integration and independent B7 V2
review, coordinating I1/byte from their recorded state. Do not restart old
process handles or treat interrupted output as certification.

Before any main merge, follow CLAUDE.md's adversarial-audit and explicit
user-approval protocol. This maintenance implementation has self-review and
adversarial lifecycle tests; an independent pre-merge review is not claimed.

## Follow-up retirement disposition

The user subsequently ruled that retired worktrees merged to main need no
payload retention and prioritized their disposal over fine-grained space
optimization. The previously excluded 70-worktree archive has now been
removed after verifying all archived tips are in main and there are no
incoming live symlinks. This supersedes this document's earlier archive
preservation requirement. Git commits/branches remain. Active/paused/unmerged
or dirty work is still protected, and the semantics sprint remains paused.
The current retirement record is
`docs/evidence/2026-09-06_worktree-retirement/`; AGENTS.md and storage operations
now require disposal of finished merged lanes without replacement archives.

Retirement is complete: six additional clean merged worktrees and six obsolete
review fixtures were disposed of with the archive, reclaiming 166.708 GiB
more. The project is now about 181.46 GiB. The new policy overlay is bound by
`policy-rollout.json` in that retirement packet; earlier overlay hashes remain
historical records. All seven protected lane HEADs/indexes, the open merge,
and captured semantic/baseline inputs remain unchanged.
