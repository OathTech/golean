# Typed-consumer sprint handoff

## Authority and state

[USER], 2026-09-05: K1–K5 approved, with K4 clarified: merges to main
always require user approval; agents may integrate feature branches under
standing user approval. The [charter](2026-09-05_typed-consumer-sprint-charter.md)
records the exact ruling. This sprint has standing internal integration and
independent-review approval, but no approval to merge to main or push.

[AGENT] Status: **IN PROGRESS — PREFLIGHT**. No new semantic/proof outcome
is complete. Source baseline is main `47195683`; drafting commit `5a4aca9e`
changes documentation only. Main is parked clean. The coordinator will use
a dedicated sprint integration worktree and separate one-writer lanes.

## Required outcomes

| Outcome | Status | Next evidence |
|---|---|---|
| O1 typed Boolean contract | Pending | Constructor/profile matrix, candidate theorem statements and adversarial statement review |
| O2 typed recovery customer | Pending | O1 foundations, shared recovery/call contracts and second fixture |
| O3 evidence/reviews | Preflight | Fresh baseline and existing admission/interface/A1/A2 gates |
| O4 B7/I1 | Pending | Reviewed O1 contract; pure representation correspondence kept separate from I1 |
| O5 closing branch/packet | Pending | All mandatory outcomes, final gates, final independent review |

## Decision ledger

- K1–K5: [USER] APPROVED, 2026-09-05, recorded in charter §2.
- [AGENT] Start with independent statement review in parallel with executable
  preflight and local study of Boolean environments/setup. Do not begin B7
  edits until the initial typed contract has a concrete reviewed shape.
- No critical issue has yet been identified. No additional user decision is
  required to begin the authorized work.

## Evidence and continuation

The draft's link/anchor and whitespace checks passed; no Lean sources changed
in drafting. Runtime results in the prior A3 handoff are historical and must
not be reported as fresh sprint preflight. Record commands, exact tested
sources, toolchain pins, logs, failures and evidence hashes here as they run.

## Live lane state (2026-09-05)

- Integration: `.claude/worktrees/typed-consumer-sprint`, branch
  `typed-consumer-sprint`, base `10fefeb3`; coordinator owns BooleanStore,
  generic setup and integration documents. New BooleanStore helper proofs
  compile under the cap; this is not yet a complete O1 runtime invariant.
- Static typing: `.claude/worktrees/typed-boolean`, branch `typed-boolean`;
  independent judgments/checkers compile; tests and ordinary CI pending.
- Preflight: `.claude/worktrees/typed-preflight`; full CI differential is
  running. A1/A2 gates passed fresh, including A2 native artifact and 3/3
  differentials. Full admission gate and corpus baseline remain pending.
- Statement review: `.claude/worktrees/typed-contract-review`; kernel/Go
  counterexamples and candidate-contract review, no implementation signoff.

The [runtime design](2026-09-05_boolean-runtime-contract-design.md) records
candidate statements, constructor obligations and actual-vs-static context
issues. `seqCont` declaration splicing was found during review and corrected
in the static design before its checker proof was finalized.

## New decision candidates (not yet ruled)

- O2 abort rendering: valid Unicode/newline/invalid-UTF8 string payloads can
  reach abort but be refused by the current renderer. The reviewer preserved
  kernel and Go witnesses. Determine repairs justified by the current
  first-line observation policy; invalid bytes exceed the current String
  terminal representation and may require a critical decision.
- O2 equal recovered/repanicked string payloads: rendering refuses the
  unresolved boxing-identity case (existing BUG-004). Preserve the witness;
  no equality-implies-same-box assumption and no silent profile narrowing.

These are open investigations, not permission to weaken O2 or stop independent
O1 work. Next: finish generic Boolean setup helpers, review the concrete
runtime statement matrix, complete static tests and preflight evidence.
