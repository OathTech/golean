# tools/stage — the coordinator's restack helpers (untrusted tooling)

Used when several lanes' branches are cherry-picked onto one stage branch and the
same append-only files conflict. Run from the stage worktree during a cherry-pick:

- `pick.sh <commit>…` — cherry-picks each commit; on a conflict it resolves
  `docs/BUGS.md`, `docs/changelog/20d3946d-WINDOW.md`, `docs/defect-shapes.md`
  and `docs/spec-divergence-ledger.md` by KEEPING BOTH sides in order
  (`keep-both.py`), the two baselines by a three-way row merge
  (`baseline-union3.py`: ours' body with its reason blocks in place, theirs' row
  deltas relative to its base applied, theirs' header blocks added, the counts
  recomputed), `Tests/GoCoreEval.lean` by taking theirs; anything else stops.
- After the restack: dedupe `docs/defect-shapes.md` (keep-both duplicates the
  §2 rows and §3 items both sides touched — keep the swept/longer copy) and
  recount its totals; then the stage's own records commit and the merge gate.

The baselines' reason blocks must stay immediately above the rows they annotate:
`scripts/coverage-baseline-diff` refuses a record whose blocks are detached
(the coordinator's lesson of 2026-10-27, train 25).
