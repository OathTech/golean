# THE RAFT PROOF CAMPAIGN — log

Governing instrument: `docs/2026-08-21_raft-proof-constitution.md`
(ratified 2026-08-22). Launched: **2026-08-22, [USER]** — Mike's
launch sign-off given as the autonomous-goal charter pointing at the
constitution ("complete the WHOLE remainder... don't stop to solicit
feedback... log every call [AGENT]/[USER]; do not merge to main until
the user signs off"). Base: `main` @ `f64d9b21` (the launch-audit fix
round, merged on [USER] sign-off). Lane: `campaign` branch, worktree
`.claude/worktrees/campaign`; sub-branches per arc as needed.

Conventions (constitution §4.3, binding): one writer per worktree;
checkpoints every ≤5 units, numbers recomputed not restated; every
judgment call one line here, tagged **[AGENT]** or **[USER]** — a
mis-tagged decision is a critical trust failure; successors re-verify
predecessors' top claims; snapshot refs before risky git ops.

Standing [USER] decisions inherited at launch (all ruled 2026-08-22,
recorded in the constitution): ends = T1+T2, T3 headline-as-proved,
T4 stretch; reliable-first envelope; harvest narrowing + phase
tolerance; applied-entry projection (S2 comparison only); liveness =
successor; Plan A = Verdi structure port; surgery threshold (§4.1);
milestone cadence; supervision seam (statement re-pins + semantic-core
surgery = supervised arcs — operative reading below).

**[AGENT] Operative reading of the Q7 seam under the autonomous goal**
(logged for review, 2026-08-22): "supervised" arcs and Mike-only acts
(designation §3.2, envelope rulings §3.4, merge/push §4.1) are
executed as: the work proceeds on branches; every Mike-gate item is
QUEUED in the "Awaiting [USER]" section below rather than blocking the
campaign; no merge to main, no designation, no envelope change happens
by agent act. If every open line of work ever blocks on the queue, that
is the §4.4 park-and-report condition, not an emergency.

---

## The arc ladder (initial plan — revised as discovered, revisions logged)

- **ARC 1 — the statement (M5).** The twin program pinned as a golden
  lowering; `Agreement`/S1–S4 defined first-order over the interpreter;
  T1 stated (`∀ ch fuel, run = .ok r → Agreement …`) + the completion
  witness stated; both POSED for designation ([USER] queue). Exit
  artifact: the statements elaborate, the golden pin is gated, the
  vacuity direction is argued in the file.
- **ARC 2 — the completion witness (non-vacuity).** One stream + fuel
  under which the twin completes and passes with the exercise floor —
  the kernel-checked witness. Route question (logged when decided):
  WP walk over the twin (the quorum-flagship mechanism at scale) vs a
  certified-execution route. This is the first genuinely novel proof
  shape; Fable-tier.
- **ARC 3 — the invariant network (Plan A).** Port
  `refined_raft_net_invariant`'s shape; re-ground Verdi's invariant
  decomposition (election safety first) in harness vocabulary per the
  compat note §4c/§4e; build the per-event preservation lemma library
  over `stepFn`.
- **ARC 4 — T1 assembly.** The induction over runs: every completing
  run maintained the invariant network; S1–S3 read off it. Then the
  first-order readout corollaries.
- **ARC 5 — T2.** Pool-size induction (n-generic harness, statement
  quantified).
- Consolidation slices interleave per §5 (promotion ledger; ≥2-consumer
  patterns lifted).

## Units — log

(unit numbering U-c1, U-c2, …; checkpoint every ≤5 units)

- **U-c1** (2026-08-22): the choice-driven twin driver
  (`tools/raftsubject/twin-chdriver.go` + thin main) — the T1
  subject. [AGENT] design calls in
  `docs/2026-08-22_campaign-arc1-statement-design.md` §1–§2 (∀ch via
  mapIter over the live multiset; deterministic client; verdict
  quintuple as the observable; honest-stop discipline). Go-side
  validated: 8 sampled runs → 8 distinct delivery orders, all
  `viol=0 claims=1 committed=6 complete=1 floor=1 rounds=30`; builds
  clean. Machine-side smoke IN FLIGHT (detached,
  `artifacts/campaign-u1-chdriver-machine.txt`; runprobe's strict
  compare is the WRONG mode for this program — go samples orders —
  so the smoke reads the machine trace, not the compare verdict).
- **U-c2** (2026-08-22): the Arc-1 design note (above) — the
  statement shape, the aboutness seam stated plainly, the pin route
  (elaboration-time wire decode), the Arc-2 witness route question.

## Awaiting [USER] — the queue

- Designation of T1 + the completion-witness statement (constitution
  §3.2) — posed when Arc 1 is branch-complete.
- Arc 1 merge (audit ask to be posed at branch-complete).

## Judgment calls

- **[USER]** 2026-08-22: campaign launched; constitution is the scope.
- **[AGENT]** 2026-08-22: Q7 operative reading (above).
- **[AGENT]** 2026-08-22: Arc ladder as above; Arc 1 opens
  immediately on the `campaign` branch (statement work is
  supervised-class — it stays on-branch, merge-gated, so supervision
  is preserved by the merge gate itself).
