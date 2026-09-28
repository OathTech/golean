# Method promotion (G-P, window row 3) — lane handoff

Lane `core/method-promotion-0928`, worktree `.claude/worktrees/method-promotion`, off main `89792db1` (train r53 close).
Specification: `docs/2026-09-28_gp-method-promotion-design.md` (G-P PASSED, all ten §6 decisions as recommended — [USER] Mike
2026-09-28 «Go ahead and land, and approve the decisions as proposed», relayed by the [AGENT] coordinator; rulings ledger
«G-P (native method promotion) passed»). Writer: [AGENT] worker. Any deviation from a ruled decision is a new design gate:
posed in §3 below, that item STOPPED.

## 1. State per slice

| Slice | Tip | Gate | Rows born / moved | Status |
|---|---|---|---|---|
| S0 born pins | (this commit) | `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` RESULT: PASS, 788 s, 3784/3784 FULL no regression (dirty-tree note: the run preceded the commit; the committed tree differs from the gated tree by one ledger citation re-spelling, see §4) | 16 born (13 PASS, 3 FAIL by design); 0 moved | DONE |
| S1 records + cross-check | — | — | — | next |
| S2 the switch | — | — | — | — |
| S3 equations + records | — | — | — | — |

### S0 — the born pins

Every expected value observed under go1.26.5, plain and `-race`, before the row was written; `scripts/diff-one` on the 16 rows at
the S0 tree (main's code — S0 changes no code), then the full gate.

- `embedding/promoted-dynamic-surface/` (11 rows, all PASS on main): `go-nil-ptr-embed`, `go-nil-iface-embed` (PASS/confluent —
  the path is walked in the CHILD, the parent's recover never fires, gc aborts with the nil-dereference text); `defer-nil-path`
  (107 — walked at the drain), `defer-box-mutated` (2), `defer-static-control` (1 — the static control), `defer-ptr-hop-replaced`
  (3), `iface-method-value-late` (25), `iface-method-value-ptr-hop` (4), `defer-method-expr-recover` (0 — `defer S.M(s)` recovers
  in the promoted method), `defer-method-expr-recover-status` (ok 0), `nil-box-ptr-method-value-embed` (100 — `&nil.f` panics).
- `embedding/promoted-ptr-method-expression/{recover,promoted-value}` FAIL/frontend-export by design (the `(*S).M` deref-adapter
  refusal over a PROMOTED value method; gc 0 and 2) — on the ledger's FR-3 line; the refusal retires for promoted entries at S2
  (design §2 S7, decision 5). Not wrong answers: fail-closed refusals, rowed at detection.
- `race/free/promoted-ptr-hop` FAIL/confluent by design (BUG-041's Cases: line — the S3 addendum's predicted embedded-pointer-hop
  over-refusal; gc `-race` green 5/5) and its must-stay-racy guards `race/negative/{promoted-ptr-hop-target,
  promoted-ptr-hop-field}` PASS/racy (gc `-race` reports both). The free row is expected to flip at S2 (decision 6).
- No wrong answer found on main: no BUGS entry filed; BUG-041 gained the born row and a dated paragraph.
- Records: baseline header entry + 16 rows (3768 → 3784 = 3545 / 239); `docs/language-coverage-ledger.md` FR-3 row (2 → 4),
  queue row 3, Q-RACEPATH row (1 → 2), §8 tally, reds table (frontier 128 → 130, Q-* 9 → 10, total 239), movement §8an.

## 2. Changelog lines owed (`docs/changelog/61958f2e-WINDOW.md`)

None at S0 (no code). The migration table and entries land with S2/S3.

## 3. PENDING [USER] items

None posed so far.

## 4. Operational notes

- Warmed `.lake` from the primary checkout's `.lake/build` (lake rebuilt only the stale modules; `lake build golean` 106 jobs).
- The box-wide lock is taken by `.tmp/locked-gate.sh` (atomic `mkdir`, owner file, trap release, 120 s wait-retry).
- Post-gate edit disclosed: after the S0 gate the reconciler's report-only C5 finding named the ledger's FR-3 cell (a lane name
  in backticks read as a case citation); the backticks were removed — a records-only one-token change, reconciler re-run clean
  of C5; not re-gated.
- `TMPDIR=.tmp` for every harness run (the coverage scripts `mktemp` under `$TMPDIR`).
