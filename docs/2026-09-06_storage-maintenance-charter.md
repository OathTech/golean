# Storage maintenance charter

**Authorized for execution by [USER], 2026-09-06:** “please write a short
charter for this work, then execute on this”, following the disk-growth
review and coordinator's proposed remedy. The semantics sprint stays paused.
Work starts from integration commit `7edc298f` on
`storage-maintenance-20260906`; main and the integration tree's open merge
remain untouched. [AGENT] operating choices below implement that authority.

**Outcome:** make repeated verification gates use bounded generated storage,
reclaim verified disposable material, and preserve enough evidence and sprint
state to resume without losing work or overstating validation.

1. Record the paused sprint's lane tips, dirty state, open merge, stopped
   jobs, accepted evidence and outstanding obligations in the
   [pause state](2026-09-06_typed-sprint-pause-state.md).
2. Give compiled mutation fixtures an owned lifecycle: one complete isolated
   copy at a time, compact sealed evidence before release, actual subprocess
   results, and visible infrastructure failure on preservation/cleanup errors.
   Keep every existing negative control and its exact rejection requirements.
3. Resolve Go build caches consistently across worktrees; repair helper
   cleanup; provide shared storage admission, reporting and maintenance
   controls. Initial limits: 20 GiB managed scratch, 100 GiB free reserve,
   shared cache warning/stop at 50/75 GiB, 10 GiB compact evidence and 50 GiB
   retained registered outputs. Whole gates reserve 8 GiB growth. These are
   cooperative admission/monitoring limits, not OS quotas; pinned, active and
   unknown material cannot be evicted silently.
4. Prepare and execute a revalidated, journaled manifest for obsolete generated
   copies/caches/binaries. Preserve source, logs, unique evidence, Git state,
   registered/nested worktrees, dependencies and the retirement archive.
   Unresolved provenance/references go on an exception list.
5. Exercise successful, failing and interrupted lifecycles, ownership and
   concurrent admission; repeat the expanded audit three times and verify live
   build hashes and rejection results. Check shared cache use across trees and
   focused conformance. Record measured reclaimed bytes and remaining risks.

The user-authorized cleanup is narrow: tool-created fixtures and the exact
reviewed maintenance manifest. It does not grant arbitrary scratch deletion,
automatic worktree retirement, evidence expiry, gate weakening, resource-cap
increases, semantic changes, main merges, pushes or semantic sprint resumption.
Use the existing 16 GiB / 3 Lean threads / 2 coverage jobs limits. Apparatus
changes invalidate affected source bindings; never relabel old or interrupted
gates as fresh success. Deliver a named branch, durable evidence and a safe
rollout/resume procedure. Critical deviations are reported for user decision;
routine implementation choices are delegated by this charter.

## Follow-up user disposition: merged worktrees are disposable

The user subsequently directed effort toward retired worktrees, explicitly
assuming merged worktrees contain no useful information to retain and asking
to avoid excessive growth rather than hyper-optimize the remaining footprint.
This expands cleanup authority to the retired archive and finished, clean
worktrees whose tips are in main, including their disposable ignored payloads
and associated obsolete review fixtures. No replacement archive is required.
Preserve active/paused/unmerged or dirty work and actual continuing dependencies;
keep Git history and compact retirement records. The semantics sprint remains
paused and the main merge/push approval rules are unchanged.
