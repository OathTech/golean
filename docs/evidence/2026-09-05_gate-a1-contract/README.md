# Gate A1 validation evidence

Source base: `79019a74c1e1c1418293d380d1fcfbd9ae489980`.
Worktree: `.claude/worktrees/gate-a1-contract`, branch `gate-a1-contract`.
Changes are the separate spike package, its decision/review notes and these records;
no core/frontend/corpus/baseline changes.

Landing preparation moved the lane handoff to
`docs/2026-09-05_gate-a1-handoff.md` and added README/master-plan pointers.
Those documentation changes leave the reviewed code fingerprint below
unchanged. The handoff records the user's merge authorization; next-phase
recommendations retain their proposal status.

`check.txt` is the complete successful output of:

```sh
bash spikes/gate-a1/check
```

Exit 0. The normal core build completed (62 jobs); the separate package
completed (228 jobs); every spike module and the aggregate were then freshly
elaborated. An external harness imported the complete package before
checking all 12 required exports and 529 constants (including generated/private
declarations) against the classical trio.
Counts are informational; the gate checks the dependencies, not the counts.
Compiled probes printed nil, the recovered payload, the expected panic,
the print-before-panic result with its byte prefix, and successful completion
of the recovery check. These evaluations supplement the theorems.

The printed source/dependency-manifest fingerprint is:

```text
4d8757824d6b6962187908a4a39e8c528fedf679f17fcbf661d333bbfb3d7555
```

The check script defines the hash's scope. It includes all `GoLean/**/*.lean`,
the root Lake configuration/toolchain, spike modules/configuration/manifest,
and the check script/Python harness. Documentation and these transcripts are not part of
that code fingerprint. `artifact-hashes.json` separately hashes the new
package source and records, excluding itself.

`check.txt` also records the repaired gate's three mandatory negative tests:
trailing private axiom in the audit module, private axiom in the aggregate,
and trailing private theorem using a proof hole. The fixtures compile to
real imported modules in isolated copies of the package's object tree; the
same external harness then rejects each with exit 1 and the expected axiom
name. Compilation errors cannot count as audit rejections. The independent
reviewer inspected the repair and the successful transcript and approved it.

`check-initial.txt` preserves the pre-review successful transcript and its
original source fingerprint. Its in-module audit missed trailing declarations
and the aggregate; it is historical evidence, not the final gate result.
The defect and repair are recorded in
`docs/2026-09-05_gate-a1-review-and-next-phase.md`.

`audit-negative.txt` records the original, narrower negative test: a private theorem of
`False` with a proof hole was inserted into a temporary copy of the audit
module under the worktree's ignored `.tmp/` directory. The unchanged audit
code rejected its `sorryAx` dependency, exit 1. That declaration appeared
BEFORE the audit, so the test did not catch the later-discovered omission.
The test checked both the exit
code and the named rejection. No proof hole was added to the live package.
All temporary directories were left in place; no scratch deletion was performed.

Environment: Linux, Lean 4.32.2. Core and dependency build caches were copied
into this worktree. Iris/Batteries/Qq sources are at the package manifest's
exact revisions and unmodified. The initial `lake update` tried to contact
GitHub and received proxy HTTP 403; the archived local revisions were used
instead, with their upstream URLs retained in the portable manifest. This
was **incremental build plus fresh spike elaboration**, not a clean-room
bootstrap or network-fetch test.

No differential run, slow-tier recertification, detector campaign, or archived
reasoning-product rebuild was required or performed for this isolated proof
experiment. The original whole-project audit's differential results have not
been relabelled as a run of this worktree.
