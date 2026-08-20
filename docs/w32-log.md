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

## Slice 1 stage A — Q1, tagged choice sites (behavior-identical, 2026-08-20)

- Base: `f2e2ee28` (G1 note), tree clean. G0-ruled rider only — NO new
  scheduling points (G1 pending); the acceptance test is the existing
  baseline holding exactly.
- Mechanism: `ChoiceSite` (7 constructors = the census as code) +
  `SitePolicy` (consumeAtOne + canonicalSlot0 docstring) +
  `Choices.consumeAt` in State.lean; every interpreter consume site
  converted to `consumeAt` with its tag; `Choices.consume` demoted to
  the raw primitive (public only because proofs unfold through it —
  the note's "private" implemented as a documented discipline, since a
  Lean-`private` def would be unnameable in the proof layer's simp
  sets; greppable: zero bare `.consume` calls remain in interpreter
  code).
- Judgment call (policy flags vs the note's sketch): the note's Q1
  sketch said "mapIter: true; every other site: false". Shipped table:
  mapIter/appendSpill/l2Entry/l2Arrival = true (these sites' code pops
  UNCONDITIONALLY wherever it consults the stream — their width-1
  protection is structural upstream: spill width ≥ 2 always,
  `.picks`/`.multi` carry ≥ 2 ready), l4Waiter/l1Sched/l5ExitWindow =
  false. Rationale: `true` transcribes the current text exactly (byte-
  identical even under a hypothetical width-1 reach), and keeps the
  proof bridges rfl-simp (`consumeAt_pop` family) instead of needing
  bound-≥-2 arithmetic at every unfolding.
- The C-1 payoff landed: the L1 `[i]`-singleton and L4 `[cand]`-
  singleton caller-side special cases in `stepMulti`/`stepThread`
  collapsed into `consumeAt` (the non-consumption is now the table's
  `consumeAtOne := false` row) — same behavior on every stream, at
  every bound, by the policy.
- raceUpdate's three consumption replicas converted in lockstep
  (l1Sched/l2Arrival/l2Entry tags); CLI: enumPoolRun's L5 mirror
  converted; the accountant-inventory prose now names `consumeAt` +
  the constructor obligation. stepNeeds/stepNeedsSeq unchanged (they
  mirror decisions by `%`-indexing, never call consume; the sentinel
  eval-test pins still pass).
- Census-doc retirement: nondeterminism-doctrine preamble +
  latitude-inventory §0 now point at `ChoiceSite` as the census of
  record (their lists demoted to reader's mirrors).
- Proofs re-aligned (bridge lemmas `consumeAt_mapIter/appendSpill/
  l2Entry/l2Arrival`, `consumeAt_le_one`, `consumeAt_of_lt`):
  MachineSound (6 simp sets + the applySelect picks case), MultiSound
  (arrivalPlan_of_multi, stepThreadInto_sound single/multi unified
  arms, stepMulti_sound, stepMulti_of_inner, stepM_complete pair/
  pickPair realizations), MultiWfSound (stepThread_wf/stepMulti_wf
  arms), MultiStreams (stepThread_oblivious singleton-pair case,
  stepAllBranchesOk_sound L1 rewrites), StateWf (spill arm), proofs/
  MapMem, SliceMem, Frame/ChanSync, Frame/Ops2, Frame/StepSim,
  Examples/WordFreq/Count. Zero statement-strength changes; no
  witness stream shifted (consumeAt consumes at exactly the old
  positions).
- Gate: `GOLEAN_MEM_MAX=24G scripts/ci --diff` — **PASS**: core build
  warning-free, proofs + Audit gate ok, eval tests 136 ok, negative
  lane no regression, **baseline diff FULL 2226/2226, no regression —
  the predicted ZERO drift, confirmed**. Log:
  `artifacts/w32-s1A-ci.log` (untracked). Cap 24G honored.

## Slice 1 stage B — Q2, the step-event channel (behavior-identical, 2026-08-20)

- Base: `8e1c7b12` (stage A), tree clean. G0-ruled rider only — NO new
  scheduling points (G1 pending); acceptance = the existing baseline
  holding exactly, race verdicts included (the racy/negative lanes).
- Mechanism: `PickRecord` + `Choices.consumeAtE` (State.lean — the
  labeled consumption atom, emitted BY the site); `StepAction` +
  `StepEvent` (Multi.lean); `stepThread`/`stepThreadInto`/`stepMulti`
  return the step's event; `arrivalPlan` returns its L2 pick record;
  **`raceUpdate` is now a FOLD over the event** — signature
  `sPre tsPre ev m' r`, NO stream argument — dispatching on
  spawned/woke/paired/selectCommit/selectPass/opDoneStrip/privateStep.
- Deleted (audit O-2's kill list): `wokenPartner` (pre/post pool
  diffing — the partner now arrives in `.paired`); the detector's
  THREE-way stream replication (the L1 replay, the `arrivalCases`+
  L2-arrival replay, the `applySelect` L2-entry replay + its
  `readyClauses` re-derivation — the committed clause now arrives in
  `.selectCommit`); `raceUpdate_oblivious` + `poolThreadOblivious_sel`
  (MultiStreams — the detector takes no stream, so verdict
  stream-independence holds BY SIGNATURE; net −88 lines in that file).
  `enumPoolRun`/`poolStepDFS` (CLI) fold events too — the enumerator's
  detector replication concern dies with the machine's.
- THE SELECT INTERCEPTION: `SelectOutcome`/`applySelect` now EMIT the
  committed clause (`.done` carries `committed? : Option EvClause`;
  `.picks` pairs each pre-commit with its clause); the sequential
  `stepFn` arm projects it away (behavior byte-identical); the pool's
  cell path intercepts the select-apply shape (`selectApplyPlan`, the
  `spawnPlan` extraction mold) and calls the SAME `applySelect` —
  one consuming definition, the identity kept only where the event
  needs it.
- SCOPE DEVIATION from the boundary note §3, recorded: the note's
  `stepFn : … × List PickRecord` reshape is NOT taken this stage. The
  sequential proof surface pins stepFn's 3-tuple in hundreds of
  statements (MachineSound's correspondence, StepKit's ~200-use-site
  kit, ~40 gallery example files, the Sym mirror's transcription) —
  re-stating it is far beyond this stage's re-proof budget (the
  brief's ~a-day stop rule), and NO stage-B consumer needs apply-layer
  picks: the detector gets the commit identity from `applySelect`'s
  emitted component, fairness quantifies SCHEDULING picks (all
  pool-layer, in `StepEvent.picks`: l1Sched/l2Arrival/l4Waiter; C/D
  add postOp/backEdge), and the enumerator's widths ride `stepNeeds`.
  `StepEvent.picks` therefore carries pool-layer consumption only;
  apply-layer data picks (mapIter/appendSpill/l2Entry) are not in the
  event stream. Re-open trigger (docstring'd at `StepEvent`): a
  consumer needing the full labeled sequential trace (e.g. S6a's rule
  labels) — then the stepFn reshape lands with its own budget.
  Second recorded residual: `raceWakeEvent`'s blockedSelect arm still
  re-derives `resumeThread`'s deterministic head-commit from the cell
  (shape-derived, stream-free, lockstep-by-construction; would fold
  too if `resumeThread` ever emits its commit identity — kept out of
  scope because `resumeThread` appears in `StepM.wake`'s premise, so
  its signature is relation-statement surface).
- Relation: `Step.selectApply` quantifies the emitted identity
  existentially (instrumentation, not semantics — the rule relates
  configurations exactly as before); `StepM` otherwise untouched.
- Proofs re-aligned, ALL green (no stopped pieces): MachineSound
  (select realization/completeness arms over the 4-tuple), StateWf
  (`applySelect_wf`/`_itersNormalized` + the Step case), MultiSound
  (arrivalPlan lemmas carry records; `stepThread_single`/
  `stepMulti_single` become ∃-event forms; `stepThreadInto_sound`/
  `stepMulti_sound` gain the interception case via
  `Step.selectApply/Panic`; `stepM_complete` realizes through the
  interception with `stepFn_selectApply_inv`, the new bridge;
  `execProg_single_eq_execStmt` re-proved — sequential conservation
  holds verbatim), MultiWfSound (`stepThread_wf` gains the
  interception case via `applySelect_wf`), MultiStreams
  (`stepThread_oblivious` STRENGTHENED: same successor AND same event
  under every stream — what replaces the deleted detector-oblivious
  lemma in `stepAllBranchesOk_sound`; checker + unfold/mono/le chain
  event-threaded), proofs/: Frame/ChanSync (SelectOutSim/PickRel over
  the clause-carrying payloads), Frame/StepSim (select arm), Audit
  (deletion anchors updated). NPDRF: untouched (statement-level,
  relation-only). Sym mirror: NO re-transcription needed (stepFn's
  signature unchanged; the select arm's re-text is outside the spike
  fragment's gated arms — concurrency arms still quit `.q7Concurrency`,
  obligations unwidened, default build green).
- Census docs: CLI accountant inventory + latitude-inventory §0
  detector sentences updated (raceUpdate consumes/replays NOTHING).
- Gates: `GOLEAN_MEM_MAX=24G scripts/ci --slow` — **PASS**: core build
  warning-free, proofs + Audit gate ok, eval tests 136 ok (incl. the
  two sentinel pins re-stated over the event triple), differential +
  negative lanes, **baseline diff FULL 2226/2226, no regression — the
  predicted ZERO drift, confirmed; race verdicts unchanged** (the
  membership rows' enumerated sets stable, incl. both tier=slow rows
  re-certified under --slow: google-search enumerated=6,
  rwmutex-order enumerated=2). Logs: `artifacts/w32-s1B-ci2.log`
  (--slow PASS), `artifacts/w32-s1B-ci3.log` (fast re-run at the
  exact final tree after a docstring-only follow-up). Cap 24G honored
  (raft-w4 lane concurrent).
- CHECKPOINT slice-1-B: stages A+B landed; the machine is tagged and
  evented, behavior-identical; stages C/D (the observable-set changes)
  remain gated on Mike's G1 ruling on the boundary-set note §8.
