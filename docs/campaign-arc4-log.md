# Campaign Arc 4 log — the interpreter⇄invariant seam

Branch `campaign-arc4`, worktree `.claude/worktrees/campaign-arc4`,
opened from the campaign branch @ 03a91c2d (Arc-3 units 1–3
integrated). Governing: `docs/2026-08-21_raft-proof-constitution.md`
(§3 inviolables, §4.1 surgery threshold, §5 latitude);
design of record: `docs/2026-08-22_campaign-arc4-seam-design.md`
(three layers; OQ-A..OQ-D are this unit's to answer from contact).
One writer: this lane's worker. Unit in flight: **A4-U1, the pilot**
— `absState` v1 + the smallest handler interpreter-run equation +
the GO/NO-GO verdict (`docs/2026-08-22_campaign-arc4-pilot-verdict.md`).

Conventions: `[AGENT]` = judgment call under §5 latitude, logged not
pre-approved; checkpoints every ≤5 slices, numbers recomputed; kit
gaps that are GENERAL (≥2 plausible future consumers) go on the
PROMOTION LEDGER section below, target-specific ones stay local.

## Entries

- 2026-08-22 Lane verified: tip 03a91c2d, clean tree, branch
  `campaign-arc4`. Required reading done in order (constitution §3,
  seam design, Arc-1 statement design + TwinProgram/RaftAgreement,
  Arc-3 invariant index + RefinedProofStructure handlers, kit guide).
  Fresh worktree had no build; capped core `lake build`
  (GOLEAN_MEM_MAX=24G) started before instrumentation.
- 2026-08-22 [AGENT] Handler choice contact datum: the charter's
  candidate `advanceCurrentTerm` DOES NOT EXIST in the lowered
  subject — it is Verdi-side vocabulary (VerdiCompat/Raft.lean:135);
  the wire (`baselines/golden/twin-chdriver.wire.json`) has
  `raft.raft.becomeFollower` and no advanceCurrentTerm (grep over the
  9.3 MB wire: the only matches are becomeFollower). **The pilot
  handler is `becomeFollower`.**
- 2026-08-22 Static contact (wire walk, python, pre-Lean): the
  DYNAMIC call closure of the lowered `raft.raft.becomeFollower` is
  10 functions: itself → {raft.raft.reset, raft.Logger.Infof
  (interface dispatch → the harness logger's EMPTY body),
  raft.traceBecomeFollower (empty)}; reset → {raft.newReadOnly,
  raft.raft.abortLeaderTransfer,
  raft.raft.resetRandomizedElectionTimeout → raft.lockedRand.Intn,
  tracker.ProgressTracker.ResetVotes, tracker.ProgressTracker.Visit}
  + the lifted closure `raft.raft.reset$lit0` (via Visit's
  call-value) → {tracker.NewInflights, raft.raftLog.lastIndex}.
  Choice-consuming constructs INSIDE the handler: `lockedRand.Intn`
  (D-11 delta: builds an n-entry map, one `range` pick, break — ONE
  mapIter choice at n = electionTimeout = 10) and `Visit`'s `range`
  over `trk.Progress` (3 entries at n=3 — mapIter choices), then
  `sort-slice` canonicalizes order. So OQ-C's expected answer
  ("none") is ALREADY REFUTED at the smallest handler: handler
  equations must quantify over a consumed choice prefix; the
  post-state is choice-independent (sort + first-key-only uses).
  `stepFollower`/`tickElection` appear as `func-value` stores
  (assigned, not called). Mutex Lock/Unlock lower as `sync-op`.
- 2026-08-22 Dynamic contact (probe `artifacts/probe/Arc4Probe.lean`,
  compiled interpreter over the pinned wire, ch = zeros; output
  `artifacts/probe/probe2.out`): first `becomeFollower` entry (from
  `newRaft`, node 1) at subject step 21,757; the call runs
  **3,233 machine steps**, consumes **4 choices** (1 Intn pick +
  3 Visit range picks over trk.Progress), allocates **164 fresh
  cells** (locals/temporaries/param cells — nextAddr 1442→1606), and
  its persistent footprint beyond the fresh region is 5 cells:
  raft cell (base 389: .trk.Votes fresh handle, .readOnly fresh ptr,
  .randomizedElectionTimeout, .tick/.step funcVals; Term/Vote/lead/
  state unchanged at this t=Term call), MemoryStorage cell
  (.callStats — the subject's instrumented call counters increment on
  lastIndex, a REAL persistent side effect of a "read"), and the
  three tracker.Progress cells (Next/Match/RecentActive/Inflights).
  Mutex lock/unlock pairs leave NO net syncData change. Heap shape
  for absState: one raft node = ONE `.struct raft.raft` cell (~33
  named fields); scalars (Term/Vote/lead/state uint64) direct;
  raftLog behind a pointer (committed/applied/applying scalars on
  that cell; entries deeper behind unstable/storage + interface).
- 2026-08-22 [AGENT] Contact verdict on the seam design's cost
  assumption: "few-line bodies" is FALSE at machine level for
  becomeFollower — the 8-statement body drags reset → {Intn's
  10-iteration map build + mutex, tracker.Visit's choice-driven
  range + sort-slice + 3 closure calls each doing
  raftLog.lastIndex → interface dispatch → MemoryStorage + mutex},
  plus logger interface dispatch. Pilot plan adjusted WITHIN the
  charter: absState v1 + the equation built bottom-up as per-callee
  run equations (the composition shape (B) prescribes anyway),
  starting from the leaf `abortLeaderTransfer` to validate the
  equation FORM end-to-end and measure per-ingredient proof cost;
  full becomeFollower composition attempted only if measured leaf
  costs make it feasible in-unit; otherwise the pilot ends at the
  honest gap + NO-GO verdict with the measured numbers (exactly the
  seam design's "anything else → re-design here" branch).
