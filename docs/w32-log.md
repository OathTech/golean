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

## Slice 1 phase A — the boundary-set design note (G1 artifact, 2026-08-20)

- Base: `10aad750` (G0 ruled + slice 5b added), tree clean. NO SURGERY
  — this phase writes the G1 gate artifact only; the charter gates
  implementation on Mike's approval of the note.
- Wedge reproduced FRESH at this tip (not quoted from the 2026-08-12
  record): gc send-then-spin exit0-and-prints-42 60/60 (+20/20 at
  GOMAXPROCS=1); machine fuel-out on the default stream and 511/511
  fuel-out on the exhaustive mod-2 depth-8 sweep (--fuel 100000; the
  probe record's closed reachable-set argument re-applies). Control
  probe (b) re-run: ok/7 on default/[0]/[2]/[0,1]/[0,0,0,0], fuel-out
  on [1]/[1,0] — matches the record exactly.
- U-1's owed directed probe RUN (new this session): wake-then-abort
  (cap-1 send wakes main, worker panics in its private segment). gc
  200 runs: 0 exit-0, 189 exit-2-with-"42"-printed, 11 exit-2-silent.
  Machine 127/127 panic on the mod-2 depth-6 sweep. The DOMINANT gc
  member (partner progress between wake and abort) is observed ∉
  modeled — U-1 moves from (d) UNKNOWN to a measured datum; probe
  source is inline in the note (evidence-dir + corpus rows land with
  stage C — this lane's writes are the note + this log only).
- Judgment call: probe artifacts kept under `artifacts/w32-probes/`
  (gitignored) per the lane brief — raft-w4 concurrently owns
  `Corpus/` + `baselines/`; nothing under either was touched.
- Judgment call: the U-1 probe's finding (gc dominant member is
  print-THEN-abort, exit-0 never observed in 200) reshaped the note's
  B3 stance — the abort window is proposed DEFERRED to slice 5
  because no OBSERVED member needs it (B1+L5 admit both observed
  members); the probe is recorded as B3's trigger baseline.
- Judgment call: canonical-slot convention for the new sites (slot 0
  = issuer/current continues) chosen over uniform goroutine-order —
  it is what makes "default stream = old schedule" literal, the
  zero-strict-flips prediction falsifiable, and the non-preclusion
  argument structural; posed as decision question 4, not buried.
- Output: `docs/2026-08-20_w32-boundary-set.md` — §1 wedge fresh
  reproduction + file:line mechanism; §2 the set (B1 post-op markers
  at ALL registry-op completions via `.opDone` unifying `.spawned`;
  B2 back-edge boundaries; B3 considered-and-deferred), each with
  spec-anchored envelope argument + admitted members + granularity
  footprint (incl. one owed correction to the inventory's C2/C3
  "segments shrink" cost prose); §3 the G0-ruled Q1/Q2 designs with
  signatures; §4 fairness non-preclusion (4-point argument; B2 is
  what makes Fair non-vacuous); §5 cost surface (proof blast radius
  by file, corpus prediction "new ids only" stated falsifiably, both
  tier=slow rows scoped, the enumerator's per-site modes +
  allow-nonterm accounting); §6 U-1 pinned; §7 staged plan A–E each
  gate-green; §8 decision block (6 questions, per-strike
  consequences).
- CHECKPOINT slice-1-A: note written; gate run below; **G1 ask POSED
  — awaiting Mike's ruling on §8 before any surgery.**

### Gate (slice 1 phase A, docs-only)

- `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` — **PASS**
  (exit 0): all steps ok (escape hatches, purity/TCB/import-direction,
  core build warning-free, proofs + Audit gate, verdi compat, goose
  fixtures/pins, golden lowering, frontend unit tests, eval tests 136
  ok); the two baseline-diff steps report the visible
  `note … NOT RUN (no record; explicitly allowed here)` — the
  docs-only hatch as specified (this phase changed no runtime code;
  probes are gitignored under `artifacts/w32-probes/`). Log:
  `artifacts/w32-s1a-ci.log` (untracked). Cap 24G honored (raft-w4
  lane concurrent).
