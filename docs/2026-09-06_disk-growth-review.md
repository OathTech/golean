> Landing note ([AGENT] coordinator, 2026-09-10): this document was left untracked in the primary checkout by its author; landed on `main` on the [USER]'s instruction («Yeah, let's land the review doc.», Mike 2026-09-10, relayed), content unmodified below. While untracked it made the primary checkout's `ci --slow` run records `git_dirty=true` (rounds 29–30), which is why it lands as a records commit now. Its recommendations remain [AGENT] proposals, not rulings.

# Disk growth review and proposed recovery plan

[AGENT], 2026-09-06. Prepared for the main build coordinator at the user's
request, following a read-only investigation of `/home/dev/projects/golean`.
The user authorized this document; implementation, deletion, policy changes,
worktree removal, merge and push are not authorized by this document.
Other agents' worktrees and sessions were left in place. No builds or cleanup
were run for the investigation. The only deliverable of this follow-up is
this review document.

Read alongside the [charter](../CLAUDE.md), [master plan](2026-09-05_master-plan.md),
[scratch policy](../AGENTS.md), and [sandbox notes](agent-sandbox.md).
All recommendations below are [AGENT] proposals for review, not [USER] rulings.

**Recommendation: repair audit scratch retention before resuming repeated
full gates, then reclaim completed generated fixtures through an approved
path manifest.** The dominant growth mechanism is repeated copying and
permanent retention of compiled Lean packages inside mutation tests. Shared
Go caching and bounded experiment retention are the next priorities.
The semantic tests and their rejection requirements should remain intact.

**Measured footprint.** The investigation found approximately 1,011 GiB
(1.09 decimal TB) allocated beneath the project. The filesystem reported
about 368 GiB available during that investigation and 366 GiB during document
preparation. These are observations at different times, not an atomic
snapshot or a measured project growth rate. Filesystem-wide changes can
include activity outside this project.

| Disjoint location | Allocated space, rounded | Main contents |
|---|---:|---|
| `.claude/worktrees/` | 508 GiB | 309 GiB scratch, 137 GiB direct Go caches, 19 GiB Lake builds, other artifacts/dependencies |
| Root `.tmp/` | 257 GiB | 239 GiB audit directories, 10 GiB temporary helper binaries, other scratch |
| `.claude/worktree-archive/` | 137 GiB | Preserved material from retired worktrees |
| `side/gofuzz/` | 84 GiB | 81 GiB in `.tmp`, including a 42 GiB Go cache and experiments |
| Root `artifacts/` | 18 GiB | 15 GiB Go cache and other artifacts |
| Everything else | About 7 GiB | Mostly root dependencies; source and Git metadata are small |

There were 49 registered worktrees, including the primary checkout and
nested worktrees, and 47 immediate lane directories under `.claude/worktrees`.
The primary `.lake` occupied about 470 MiB; `.git` occupied about 399 MiB.
Inodes were about 11% used: allocated bytes are the immediate capacity issue.
The filesystem is ext4. Measurements used `du -x` without following
symlinks; ordinary hard links are counted once per traversal.

**Finding 1: audit fixture retention explains most of the rapid growth.**
Root and live-worktree scratch together occupy approximately 566 GiB.
About 545 GiB is in the identified audit directory families. This is the
size of those directories, not a claim that every byte is disposable.

| Observed audit family and scope | Runs/directories | Total |
|---|---:|---:|
| Worktree `interface-audit-*` | 68 | 256.5 GiB |
| Root `recovery-control-audit-*` | 22 | 75.8 GiB |
| Root `recovery-setup-audit-*` | 25 | 40.2 GiB |
| Root `recovery-storage-audit-*` | 26 | 36.0 GiB |
| Root `boolean-runtime-audit-*` | 39 | 23.8 GiB |
| Root `recovery-typing-audit-*` | 35 | 23.0 GiB |

For example, `typed-consumer-sprint/.tmp` contains 20 interface audit runs
occupying 83.6 GiB. `typed-string-members/.tmp` contains 10 occupying
48.5 GiB. A sampled recovery-control audit occupied 3.3 GiB: fifteen
fixtures each contained roughly 224 MiB of compiled `GoLean`, with two
additional test-package fixtures. Sampled unchanged `StateWf.olean` copies
were byte-identical by SHA-256, each separately allocated with link count 1.
These are actual duplicated files.

The code directly explains this pattern:

- [scripts/check-interface.py](../scripts/check-interface.py), lines 30–32,
  59–61 and 72: create a new root-local scratch directory, copy both complete
  compiled package trees for each mutation, and retain scratch on success.
- [tools/admission-check.py](../tools/admission-check.py), lines 33–38 and
  71–91: new retained scratch and a complete compiled package copy per poison.
- The expanded [interface audit in typed-consumer-sprint](../.claude/worktrees/typed-consumer-sprint/scripts/check-interface.py),
  lines 99–184, applies the same pattern to many more mutations.
- The [recovery-control audit in typed-recovery-terminal](../.claude/worktrees/typed-recovery-terminal/tools/recovery-control-audit.py),
  lines 22–59, copies a complete compiled package for each mutation and has
  no cleanup. Related Boolean, recovery, declaration and observation audits
  follow the same pattern. That lane's `scripts/ci` invokes these checks.

Accumulated storage scales with **runs × mutations × compiled package size**,
summed across lanes. Increasing proof/package size and adding mutation tests
both increase storage per gate. Repeated successful gates accumulate too.
The observed directories do not all certify completed or passing runs.

The environment inspected had `TMPDIR=/home/dev/projects/golean/.tmp`.
Some audits honor `TMPDIR`; others explicitly use their worktree's `.tmp`.
Consequently, changing `TMPDIR` alone will not fix all producers. The current
guidance to leave scratch for OS cleanup also needs an explicit lifecycle
when scratch is inside the project. Host-specific cleanup configuration was
not fully inspected because `/etc/tmpfiles.d` was outside the nono read grant;
no host cleanup policy is assumed here.

**Finding 2: cache isolation multiplies Go storage.** The direct caches
measured were 137.2 GiB across 31 live worktrees, 15.3 GiB in the primary
checkout, and 42.0 GiB in `side/gofuzz/.tmp/go-build`: approximately 194.5 GiB
combined. This excludes nested campaign caches that were not fully totaled.
It is not a measured estimate of unique cache content or deduplication savings.

[scripts/diff-coverage](../scripts/diff-coverage), line 12, overrides the
cache with `$ROOT/artifacts/go-build-cache`. `scripts/ci`,
`scripts/membership-sampling`, and Python helpers also contain explicit
worktree-local settings. [scripts/grossmith-run](../scripts/grossmith-run),
lines 109–133, places scratch and a cache inside the campaign output root.
Exporting `GOCACHE` at session startup does not override all these sites.

Go documents concurrent use of its build cache and fingerprints source,
compiler and options; see [the Go command documentation](https://go.dev/src/cmd/go/alldocs.go)
and the local pinned source `deps/go/src/cmd/go/alldocs.go`, lines 2322–2339.
The pinned `internal/cache/cache.go`, lines 341–350, describes age-based
trimming, approximately daily with a five-day reuse window. This is not a
byte quota, and abandoned worktree caches have no continuing Go invocations
to perform that trimming.

**Finding 3: past cleanup preserved other substantial material.** The
[existing cleanup record](../.claude/worktree-archive/2026-09-06/README.md)
reports that 70 merged clean worktrees were removed earlier on September 6,
with a filesystem-wide gain of 503.46 GiB. That operation preserved 808
entries and verified existing symlinks. Its authorization covered direct Go
caches and Lake build directories; it deliberately preserved other ignored
material, dependency repositories, scratch and evidence.

The remaining archive contains approximately 81 GiB of artifacts, 42 GiB of
dependencies and 10 GiB of scratch, plus other preserved material. Examples
include 28 GiB of grossmith artifacts and 13 GiB of oracle experiment output.
The archive is not a disposable cache, and the earlier cleanup authorization
must not be broadened by inference. Moving files into an archive on the same
filesystem preserves them but frees no data blocks.

There are also 3,557 root `.tmp/golean-lsimports.*` helper binaries occupying
10.3 GiB. `scripts/import-goose` already installs cleanup traps at lines 133
and 207. Their persistence warrants a separate investigation; this review
does not claim the trap is absent or establish why those executions left files.

**Proposed implementation, in priority order.**

| Priority | Change | Reviewable result |
|---|---|---|
| P0 | Give test-owned scratch an explicit lifecycle | Successful audits retain compact evidence and release compiled fixture copies; failures are preserved within an explicit budget |
| P0 | Apply the fix to the coordinator's actual integration tree and active audit families | A fix only on today's primary checkout does not leave the expanded lane scripts producing gigabytes |
| P1 | Reduce simultaneously materialized fixture copies | One isolated complete package copy at a time; reuse within a run only after restoration checks pass |
| P1 | Centralize Go cache selection | All ordinary build/test runners honor one explicitly configured shared cache inside the permitted project area |
| P2 | Report disk usage and enforce admission/retention budgets | Gates expose incremental and retained bytes; campaign outputs and abandoned scratch have owners and expiry |
| P2 | Review archive and gofuzz retention separately | Evidence/dependency repositories remain protected while individually approved generated output can be retired |

For P0, introduce one common scratch helper for Python audits and a compatible
shell convention. Allocate unique run directories in a dedicated generated
scratch subtree, separate from agent notes and ad hoc probes. Record the
creating worktree, script, source fingerprint, run identity and lifecycle
state. Publish evidence before removing any fixture. A cleanup failure is a
visible infrastructure failure, not a silent success. Interrupted runs remain
discoverable; a later sweep must establish inactivity before acting.

The smallest first fix can still copy each complete package independently,
but dispose of each completed fixture after saving its evidence. This bounds
peak storage to roughly one fixture per running audit instead of one per
mutation, and prevents accumulation between successful runs. A second change
may reuse one complete isolated package tree, restoring every changed or
generated output between mutations and launching fresh Lean subprocesses.
Retain immutable input build files for the duration of the audit.

Keep complete package resolution: `tools/admission-check.py` explicitly
records why partial `LEAN_PATH` overlays failed to import siblings. Do not
replace the isolation with writable symlinks or hard links to live `.lake`
files. Mutations deliberately overwrite compiled modules. Copy-on-write
cloning is an optional later optimization on a supporting filesystem, not a
prerequisite or an assumed saving on this ext4 workspace.

Compact evidence should include the source revision and relevant dirty
changes/untracked inputs, toolchain, source/build hashes, mutation source,
harness, command arguments and relevant environment, exit statuses, stdout,
stderr, expected marker, and final disposition. Avoid recording unrelated
environment secrets. For existing runs whose provenance cannot be recovered,
preserve the unresolved evidence rather than claiming a source hash alone
makes the run reproducible. Save manifests atomically and check their integrity.

For P1 caching, let the coordinator supply a canonical absolute shared cache
path, for example the primary checkout's `artifacts/go-build-cache`, to all
participating worktrees. Use a common resolver that honors an explicit cache
setting and has a documented standalone fallback. Update every producer,
including helpers and campaign wrappers, and record the resolved path in
provenance. Intentionally cold-cache tests may retain explicit isolated caches
with the same cleanup lifecycle. Confirm the shared path is already granted
to each sandbox before rollout; do not silently fall back to an external path.

This shares compiled Go artifacts, not differential observations, evidence,
mutable Lean build outputs or worktree result directories. Keep oracle pins,
fresh execution requirements and observation comparison unchanged. Do not
clear caches while participating builds are running. Prefer one existing
cache or a bounded cold start to copying all old caches into a new location;
the union of their content has not been measured.

Proposed initial storage settings for coordinator review are a 50 GiB warning
and 75 GiB maintenance threshold for the shared Go cache, a 20 GiB aggregate
generated-scratch budget, and a seven-day/10 GiB budget for unpinned failed-run
fixtures. The failure budget is part of the scratch budget. These are starting
operating choices, not measured minimum requirements or existing Go options.
Never silently evict a pinned failure or an active run to meet them; refuse
new heavy work and request disposition when no eligible space remains.
Small sealed evidence bundles need a separate retention policy.

Disk admission should account for concurrent reservations plus expected run
growth and a filesystem free-space reserve; a single `df` check is only a
guard, not enforcement. Start with a proposed 100 GiB free-space reserve and
revisit it using measured peak usage. Coordinate maintenance and reservations
across worktrees under one owner. Report bytes before/after each full gate and
each campaign, including paths outside the current worktree used through
`TMPDIR`. Memory caps in `scripts/capped` do not impose a disk budget.

**Proposed remedy for the current blow-up.** The coordinator should prepare
one concrete cleanup manifest and obtain approval for that manifest and the
narrow ongoing lifecycle policy. Existing `AGENTS.md` requires explicit
approval for removal. Do not interpret the request to write this review, or
the earlier worktree cleanup, as authorization to delete the candidates below.

1. **Establish the preservation baseline while heavy work remains paused.**
   Confirm that audit/build child processes and background jobs using candidate
   paths have finished; an idle agent alone does not establish this. Record
   registered worktrees, refs, and relevant tracked/untracked/ignored state
   with Git optional locks disabled. Inventory candidate paths, allocated
   bytes, ownership, canonical location, device/inode identity, run completion
   evidence and incoming symlink/dependency references. Existing nested
   worktrees, repositories, notes and handoffs remain outside automatic scope.

2. **Prioritize completed generated audit fixtures.** The approximately
   545 GiB audit-directory pool is the first candidate set. Start with the
   256.5 GiB worktree interface-audit family and the large root recovery
   families. Preserve each needed evidence bundle before approving removal of
   its duplicated compiled package trees. Incomplete, active, referenced or
   unclassified runs stay on an exception list. Directory names and ages alone
   are insufficient. Aim to reclaim several hundred GiB in this pass, with
   the actual target determined by the eligible manifest rather than promising
   the entire measured pool.

3. **Fix the producers before unrestricted gating resumes.** After any small
   initial reclaim needed for implementation, review and validate the P0
   lifecycle change in the integration tree. Retain every audit and required
   gate. Use the project's focused iteration workflow and capped build rules;
   storage pressure is not a reason to report skipped tests as passing.

4. **Consolidate Go caches during a maintenance window.** Select and validate
   the shared cache, update participating runners, then approve deletion of
   the exact obsolete cache paths after checking references and inactivity.
   The measured direct cache pool is 194.5 GiB, including the selected cache
   and the separate gofuzz cache; future retained capacity must be subtracted
   before estimating savings. Gofuzz participation needs its own owner review.
   No second copy of the whole cache pool should be created for migration.

5. **Review remaining generated experiments and helper binaries separately.**
   Classify the 10.3 GiB of `golean-lsimports.*` files and gofuzz's experiment
   directories, preserving sources, seeds, failures and any embedded repository
   state as needed. Treat the 137 GiB worktree archive as an evidence archive:
   propose exact generated subsets for retirement, and preserve its metadata,
   repositories, unique notes and link targets. It is not part of the first
   blanket cleanup scope. No `.tmp` tree is approved wholesale.

6. **Execute only the reviewed manifest and verify preservation.** Recheck
   candidate identity and inactivity immediately before removal; refuse paths
   that changed, escape the approved roots, or traverse unexpected links.
   Keep an execution journal with per-path outcomes, measure both allocated
   directory bytes and filesystem free-space change, and compare worktree/ref
   and preservation checks with the baseline. Report excluded paths and any
   new dangling references. Renaming a directory into same-volume quarantine
   may simplify review but must not be counted as reclaimed space.

Stages 2, 4 and 5 are separate inventories; their headline numbers must not
be added to parent directory totals. The archive, source, active builds and
unknown scratch remain protected throughout. There is no proposed branch
deletion, history rewrite, forced worktree removal or reset of an agent's tree.

**Acceptance criteria for the implementation review.**

- Every clean audit still passes; every mutation compiles successfully and
  then fails the external audit with its required status and named forbidden
  axiom. Missing imports, compilation failures, timeouts and budget refusals
  cannot count as negative-test success.
- Repeating a successful audit three times leaves no compiled fixture copies
  from completed runs. Growth is confined to measured compact evidence;
  peak generated scratch is bounded by the active fixtures. Measure an
  expanded interface/recovery audit, not only a tiny synthetic example.
- Test failure, interruption, evidence-write failure and cleanup failure paths.
  Active/pinned runs survive maintenance; abandoned runs are reported and
  handled only under the approved policy. Cross-worktree runs cannot collide
  or clean one another's active files.
- If a reusable fixture tree is introduced, reorder mutations and compare
  outcomes; prove restoration by comparing files with the immutable input
  manifest. Hash relevant live `.lake` files before/after the audit to confirm
  they were not modified by the fixture mechanism.
- Exercise two worktrees using the chosen Go cache and confirm that helpers
  actually use it. Run focused Go-vs-Lean cases with unchanged oracle pins and
  comparison behavior. Record cold/warm build and cache sizes rather than
  assuming a particular deduplication ratio.
- Run the applicable project CI and customer/audit gates through
  `scripts/capped`; retain `lake build` for Lean changes and the required
  differential checks. Any deferred validation is an explicit review gap.

**Decisions requested from the coordinator's review.** Accept or revise the
P0 lifecycle design, identify the integration owner and participating lanes,
choose the shared-cache path and initial budgets, and prepare the eligible
cleanup manifest. Present that concrete manifest and a narrowly scoped
test-owned cleanup policy for approval. Keep the existing protection of agent
notes, unclassified scratch and archived evidence. This document itself does
not change `AGENTS.md`, scripts, caches or gate behavior.

**Source binding and limits of this review.** Primary HEAD was
`471956831251e428df3a64c5b8fc7fb79cbebbfc`; the primary tracked checkout was
clean before this document was added. The inspected lane HEADs were
`typed-consumer-sprint`: `7edc298f257519652646b7a59bca959671d33063`, and
`typed-recovery-terminal`: `f397119011a51b7b21a750e34c17f38015683bf8`.
Lane links above refer to local working files, which may later move; the
following hashes bind the inspected content independently of branch names.

| File | SHA-256 |
|---|---|
| Primary `scripts/check-interface.py` | `84c3cccb5c540215b24051ba8c94900bc6123ed24f0918edad208d31c442105d` |
| Primary `tools/admission-check.py` | `c9d0fdd66d020abe44e50f54715715d5685173c957912c29890e19196c450b21` |
| Primary `scripts/diff-coverage` | `74c916bbd6be5da97b3503cc32dcfe5c714e0c33ce709272ea9d915e5fb94b77` |
| `typed-consumer-sprint/scripts/check-interface.py` | `b16917103ce7da417bc40240c32ecafc7f04cd626b76b9347587364f15249d3a` |
| `typed-recovery-terminal/tools/recovery-control-audit.py` | `7ed106818c2fad382c3af193b9278e5402771bcbd6e98e8720889f6fa28f0b1f` |

Measurements came from read-only directory traversals, file metadata, sampled
file hashes, Git registration/status queries and source inspection. They are
summarized here from the investigation transcript; no sealed per-file deletion
manifest was produced, and no fix was implemented or exercised. No exhaustive
cache-content deduplication, audit-completion certification, dependency-link
audit or host-quota inspection was performed. Those omissions constrain
cleanup eligibility and projected savings, not the directly observed copying
and retention mechanism.
