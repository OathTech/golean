# W3.2 re-envelope arc — log

Worktree `.claude/worktrees/w32`, branch `w32-re-envelope`. Charter:
`docs/2026-08-20_w32-re-envelope-charter.md` (signed off with defaults,
2026-08-20). One writer per worktree. Entries newest-last; one-line
judgment calls recorded as they are made; checkpoints every ≤5 units.

## Slice 0 — the semantics design audit (2026-08-20)

- Base: `f78138d7` (charter sign-off), tree clean. `deps/` bootstrapped
  via `scripts/setup-deps --from /home/dev/projects/golean` (offline).
- Inputs read in full: charter §Slice 0, essence-of-Go doctrine,
  nondeterminism doctrine, reshape note §1 (granularity ledger), then
  the code itself — `GoLean/GoCore/{Syntax,Machine,StepFn,Ops,Multi,
  Race}.lean` (9,664 lines) as a PL-theorist read, plus targeted
  `Ops.lean`/`State.lean` sections (Choices, append envelope,
  dynamicDispatch) and the proof layer where it grounds a finding
  (`Laws/Init.lean:71` — the stmtOpNullary refutation).
- Judgment call: READ-ONLY on the semantic core honored — zero code
  changes; two suspected findings were verified against the proof layer
  by grep, not by builds.
- Judgment call: the charter's two named suspects (`addrOfDeref`, the
  19-arm round) audited to CLEARED verdicts rather than forced into the
  queue — honest negatives count (charter §Slice 0 output spec).
- Judgment call: `Cont` as `List Frame` (the deep continuation reshape)
  recorded as out of this arc's budget in §4/K-1 rung 2, not queued —
  its blast radius is the whole rule set and nothing in slices 1–6
  needs it.
- Output: `docs/2026-08-20_semantics-design-audit.md` — 7 dimensions,
  ~25 file:line-grounded findings each with a sketched better shape,
  an 11-item graded refactor queue (Q1 tagged choice sites and Q2
  step-event channel ride slice 1; Q3 bundling staged before; Q10→
  slice 5, Q11→slice 4; Q6 signal unification is a G0 decision against
  S6a), and §9's honest positives as the S6a evidence base.
- CHECKPOINT slice-0: audit note written; gate run below; G0 ask posed
  in the audit note §10. Awaiting Mike's queue review before any code
  moves (user gate G0 — the arc does not proceed to slice-1 surgery
  past it).

### Gate (slice 0, docs-only)

- `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` — docs-only
  slice: no runtime change owes a differential; the no-diff hatch is
  set explicitly with its visible note per the validation-gate contract
  (fresh lane worktree, docs-only arc).
- Bootstrap note: the first run failed at the proofs-side steps because
  the fresh worktree had no `proofs/.lake/packages` and the sandbox
  denies the network clone (403) — the fail-closed direction working as
  designed. Seeded `proofs/.lake` OFFLINE from the primary checkout
  (the established lane pattern: `channel-logic` and `raft-w4` carry
  the same seeded packages; the Verdi note budgets `proofs/.lake` per
  lane) and verified all three package revs against
  `proofs/lake-manifest.json` before re-running (iris `3877dbeccd1b`,
  batteries `fa08db58b30e`, Qq `f46324995fca` — exact matches). One
  cleanup `rm -rf proofs/.lake` was needed to undo my own botched
  nested copy (a directory this session created minutes earlier, not a
  pre-existing scratch dir).
- Result: **PASS** (exit 0) — all steps ok (surface purity, TCB
  closure, import-direction, core build warning-free, proofs + Audit
  gate, verdi compat, import-goose fixtures, golden lowering, R2 pins,
  frontend unit tests, eval tests 136 ok); the two baseline-diff steps
  report the visible `note … NOT RUN (no record; explicitly allowed
  here)` — the docs-only hatch working as specified. Log:
  `artifacts/w32-s0-ci2.log` (untracked).
