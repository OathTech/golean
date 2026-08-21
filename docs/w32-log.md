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

## Slice 1 stage C — B1: the `.opDone` post-op boundaries (2026-08-20/21)

- Base: `e9954282` (stage B) REBASED onto main `d332434d` (the
  scheduling-semantics dossier landed there; snapshot
  `refs/snapshots/w32-pre-rebase-20260820` taken first, clean rebase,
  5 commits replayed). Mike's G1 ruling recorded verbatim-in-substance
  as the dated USER RULING block in the boundary-set note §8
  (commit `1c4e5f07`) BEFORE any surgery: B1+B2 approved as proposed,
  B3 deferred with the evidence door open; the governing
  pessimistic-model principle quoted; dossier §§1.1/3.1/4.3 cited into
  the envelope statements.
- MECHANISM (the note §2 B1, all-ops scope): `Config.spawned` replaced
  in place by `Config.opDone (sched : ChoiceSite) (inner : Config)` —
  the site-tagged completion marker, envelope statement in situ at the
  constructor (dossier-cited). Emitters: `applyChanOp` /
  `applySyncOp` / `commitClause` wrap every PROCEEDING outcome in
  `.opDone .postOp` (blocked outcomes are boundaries already;
  panicking outcomes unwrapped — B3 deferred); `resumeThread` wraps
  its non-select resumes (the select wake rides `commitClause`);
  `applyPairing` wraps the ISSUER's successor only (the passive
  partner is schedulable at the issuer's next boundary — no-op step
  avoided, per the note); `spawnStep` emits
  `.opDone .l1Sched (.next k)` — BUG-040's boundary default preserved
  bit-for-bit by the tag. `ChoiceSite.postOp` (consumeAtOne=false,
  slot 0 = issuer) appended to the census; `Config.boundarySite`
  (CLAMPED: non-scheduling tags consult L1 — makes the non-popping
  policy provable for arbitrary configs) + `schedSlots` (issuer-first
  menu at postOp) carry the consultation in `stepMulti`. The strip is
  `stepFn`'s new `.opDone` arm on BOTH drivers + rule
  `Step.opDoneStrip` (appended last, tags stable); `StepM.spawned`
  RETIRED — the strip is an ordinary `.thread` lift now.
- Judgment call (wrap-inside-the-applies vs at stepFn's arm): wrapped
  INSIDE `applyChanOp`/`applySyncOp`/`commitClause`, so
  `Step.chanStApply`/`syncStApply`/`selectApply` and `stepFn`'s arms
  keep their exact statements (the correspondence holds verbatim);
  the cost moved to the `*_wf` outcome-shape proofs (bind+wrap
  destructuring at each enterRecvTargets site) — paid.
- Judgment call (marker tag type): kept `ChoiceSite` per the note, with
  `Config.boundarySite` clamping junk tags to `.l1Sched` (the
  pre-widening universal behavior) rather than a fresh 2-value type —
  the sequential-conservation lemmas quantify arbitrary configs and
  need the non-popping policy unconditionally
  (`Config.boundarySite_consumeAtOne`).
- DETECTOR: `raceUpdate`'s outcome-shape SUCCESS checks
  (`some (.next _)`) moved to the marker (`some (.opDone _ _)`) — found
  by eval pins going red (BUG-045/046 races vanishing, U5 false race:
  lost HB edges), not by the build; the `.opDoneStrip` event arm was
  already no-access. The marker strip emits `.opDoneStrip` at the pool
  (dedicated arm kept: clean event + no waiter scan on markers).
- PROOFS re-aligned, ALL green (no stopped pieces): StateWf
  (`.opDone` locSup/itersNormalized arms + rfl simp lemmas; the three
  `*_itersNormalized` walk proofs replaced by the vacuity lemma
  `Config.itersNormalized_true` — the walks broke on the wrap shapes
  and carried nothing the retained-component lemma doesn't);
  MachineSound untouched (statement-preserving wraps); MultiSound
  (`opDoneInner_shape`/`opDoneInner_stepFn_strip`/`step_opDone_inv`;
  `stepThread_single`/`stepMulti_single` now COVER the marker — the
  hsc hypothesis dropped, `schedSlots_singleton`; `stepMulti_sound` /
  `stepMulti_of_inner` over the slot menu with `schedSlots_mem` /
  `mem_schedSlots_of_runnable` — `schedPick`'s membership statement
  unchanged, the menu's set = the runnable set; `stepM_complete`'s
  marker case via `Step.opDoneStrip`; the `spawned` completeness case
  deleted with the rule; `execProgLoop_single`'s marker special-case
  DELETED — the strip is now transferable, both drivers step it
  identically); MultiWfSound (marker case via `opDoneInner_shape`;
  wrapped-outcome destructuring; `stepMulti_wf` over `schedSlots`);
  MultiStreams (`poolThreadOblivious` marker flag; `stepAllBranchesOk`
  branches over the SLOT MENU — the probe `[j]` prefix indexes exactly
  the machine's slot; soundness + mono chains re-pointed); NPDRF
  (`StepMFine.spawned` retired with `StepM.spawned`); proofs/: Rename
  + Sym/Conc + Sym/Walk `.opDone` arms (recursive renames/reflects);
  Sym/Mirror: mirror `Config.opDone` + the arm QUITS `.q7Concurrency`
  (obligations unwidened, drift gate green); LangC/LangD: `StepEC`/
  `StepDC`'s thread-local `strip` rules RETIRED (the lift covers the
  marker), `wpC/wpD_spawned_strip` → `wpC/wpD_opDone_strip` (now
  `wp*_pure_det` instances), `wpC/wpD_fork` restated over
  `.opDone .l1Sched (.next k)`, witnesses re-walked; Audit anchors
  renamed.
- EVAL pins re-derived (the budgeted witness class): poller min fuel
  165→166 / 309→310 (one marker strip on the realized path);
  wake-multi head-commit stream [0,0,1,1,1] → [0,0,0,1,1,1]
  (re-derived by machine search; comment updated). 136/136 ok.
- **THE WEDGE FLIPS (register #1's definitional bug dies here).**
  send-then-spin on the stage-C machine: default stream → fuel-out
  (the unfair member, in the envelope BY RIGHT — dossier §3.1);
  `--choices 0,0,1` → **ok, 42** — the note §2 B1's predicted trace,
  realized (postOp pick 1 = main after the worker's send). gc's
  60/60 observation is a member again: observed ∈ modeled restored.
  Dossier §4.3's verdict ("the completing execution and an unfair
  execution") implemented exactly. Record:
  `docs/evidence/2026-08-20_w32-postop-probes/README.md` §1. (The
  register/inventory text rewrite lands with the wedge corpus row at
  stage D per the note's staging; C3+U-1 inventory rows updated in
  THIS commit.)
- U-1 ADMITTED: wake-then-abort probe re-run (gc 200: 0 exit-0, 60
  printed-42-then-abort, 140 silent — dominance load-varying vs phase
  A's 189/11); machine: default = panic (old sole member, canonical),
  `[0,0,1]` = ok 42 (partner progress between wake and abort),
  enumerator certifies {panic, ok 42} (obs=2, 373 steps, depth 15).
  Corpus row `goroutines/wake-then-abort` (membership, members=2,
  statuses=ok+panic) + evidence README §2. Inventory: C3 → (a)
  ENVELOPED (with the owed C2-cost-prose correction recorded), U-1 →
  probed-and-admitted, counts re-tallied; B3's trigger baseline
  recorded.
- **THE ENUMERATION-COST FINDING (the §5b prediction, half right).**
  Zero STRICT-lane flips — confirmed exactly. But the enumeration
  lanes' trees grew 3x–300x+ (postOp branches at every op completion
  in a ≥2-runnable window — roughly squaring interleaving counts):
  22 existing enumeration rows tripped their caps (sites= mostly).
  Re-measured every one (sets: UNCHANGED in all 19 that completed —
  the §5b set-stability prediction held everywhere measurable):
  - 16 rows: caps re-measured in place (biggest: ping-pong/alternate
    16.2M work, depth 60), fast lane.
  - 3 rows moved tier=slow with fresh certified records + measured
    stats: buffered-wake/fifo (114.4M, singleton), free-sync/
    rw-writers (87.3M, singleton), sched-dependent/first-come (84.8M,
    {12,21}; member 21 witnessed at stream [0,0,2,2]). This WIDENED
    tier=slow to the confluent lane in scripts/diff-coverage — same
    cached-record discipline (record + wire-sha + params guards,
    --slow re-certifies exhaustively, fail-closed): a caching-cadence
    change, NOT a claim change. LEAN_ENUM_SLOW_TIMEOUT default
    1200→3600 with the post-mortem's headroom arithmetic recorded.
  - **5 rows are EXHAUSTIVELY INTRACTABLE at B1 granularity** (the
    note's §5c contingency, hit harder than predicted):
    imported-goose/channel/google-search (>900M steps, unfinished;
    pre-B1 40.0M), sync/rwmutex-order (>~900M, unfinished; pre-B1
    2.2M), goroutines/worker-pool/sum (>400M; pre-B1 ≤15M),
    goroutines/pipeline/request-reply (>400M; pre-B1 ≤1.2M),
    race/litmus/sb-chan (>400M; pre-B1 ≤5M). These go HONESTLY RED at
    their existing caps (fail-loud cap breaches, seconds-to-minutes
    each) — recorded as explained regressions in the re-pin, never
    laundered. THE RULING IS MIKE'S (posed in the stage report): the
    note §5c's sampled fallback (witness-replay machinery was drafted;
    the auto-mode classifier flagged it as a claim-standard change, so
    it was REVERTED — the prepared witness streams for google-search's
    6 members are in this entry for the decision: 123=default,
    132=[1,1,0,0,0,2,2], 213=[0,0,2,2], 231=[2,1,2,3,2,0,0,3,2,0,0,2,1,2,1],
    312=[0,0,0,0,3,3], 321=[2,0,3,0,3,2,1,3,0,2,1]) vs budget raises
    vs waiting for the reduction/DPOR lane (NPDRF, slice 5 — the
    principled fix: sound schedule reduction re-shrinks these trees).
    Note the fast lane: google-search/rwmutex-order stay
    CERTIFIED-CACHED green per the tiering design (records pre-B1;
    the staleness is exactly what the --slow red surfaces); sum/
    request-reply/sb-chan red in the fast lane too (they re-enumerate
    per run).
- Gate mechanics of the finding (recorded for the audit): the widened
  tier validation touched THREE gate surfaces, each updated in
  lockstep — scripts/diff-coverage (the confluent cached path + slow
  re-cert), scripts/coverage-manifest (param validation), and
  scripts/test-lane-validation (the "tier on a confluent row" REJECT
  fixture became an ACCEPT fixture; the reject direction moved to a
  racy-row shape). ping-pong/alternate additionally moved tier=slow
  AFTER the first --slow run showed its 16.2M-work tree is PROBE-heavy
  (depth 60; each probe replays a run) and broke the 300 s fast wall
  despite fitting its work cap.
- BASELINE POLICY for the intractable five (decided, recorded): the
  tracked baseline is pinned from the FAST view — worker-pool/sum,
  pipeline/request-reply, race/litmus/sb-chan pinned FAIL (they
  re-enumerate per run and breach their caps in seconds; explained
  regressions, the honest-red protocol); google-search and
  rwmutex-order stay PASS (CERTIFIED-CACHED per the tiering design —
  records are pre-B1) so every `--slow` run reports EXACTLY those two
  drifts as the standing, recorded re-envelope alarm until Mike rules
  on the §5c fallback (options + prepared witnesses in the entry
  above). Never a silent skip: the alarm is the design surfacing the
  staleness.

### Gates (slice 1 stage C)

- `GOLEAN_MEM_MAX=24G scripts/ci --slow` (artifacts/w32-sC-ci3.log,
  untracked): all build/proof/eval steps ok (core warning-free, proofs
  + Audit gate, eval 136 ok); the --slow differential's drift list was
  EXACTLY the designed set — the 5 intractable rows FAIL + the new
  wake-then-abort PASS — plus two stage-C fix-round items it caught:
  the "tier on a confluent row" fixture (updated with the widening)
  and ping-pong/alternate's probe-heavy 300 s wall breach (moved
  tier=slow). fifo / rw-writers / first-come re-certified EXHAUSTIVELY
  under GOLEAN_SLOW=1 against their fresh records in that run.
- `GOLEAN_MEM_MAX=24G scripts/ci --diff` after the fix round
  (artifacts/w32-sC-ci4.log, untracked): every step ok; drift =
  exactly {3 explained FAILs, 1 NEW PASS} — the re-pin set, nothing
  else. **Baseline re-pin #1** recorded in `baselines/native-full.tsv`
  (2254 cases, PASS 2111 / FAIL 143) with the full reason in its
  header; `scripts/coverage-baseline-diff` = no regression at the
  pinned tree. The standing `--slow` alarm (google-search,
  rwmutex-order — stale pre-B1 records, fallback ruling Mike's) is
  recorded above and in the baseline header.
- CHECKPOINT slice-1-C: B1 landed end-to-end (machine, relation,
  metatheory, detector, mirror, Iris layers, witnesses, corpus,
  baseline); THE WEDGE FLIPS on stream [0,0,1]; U-1 admitted with its
  membership row green. Stage D (B2 back-edges + enumerator modes +
  allow-nonterm + the wedge corpus row) next.

## Slice 1 stage D — B2: the back-edge boundaries + the §5d enumerator modes (2026-08-21)

- Base: `f005588d` (stage C), tree with stage-D work. MECHANISM (the
  note §2 B2): `Config.atBoundary` gains the loop re-entry shapes
  (`.next/.continuing (.loop …)`, `.next (.mapIterK …)`) — no new
  configuration, no new step, no new relation rule; the envelope
  statement lives at the new `atBoundary` arms (dossier-cited: §1.1
  spec silence, gc 1.14 async preemption, mem#badsync, §3.1
  starvation-by-right). `ChoiceSite.backEdge` (consumeAtOne=false,
  slot 0 = current-continues; THE FAIRNESS-EXPRESSIBILITY NOTE at its
  policy docstring per the note's stage-D bullet) + `boundarySite` /
  `schedSlots` arms. Proof cost was ABSORBED by stage C's
  generalizations: only `boundarySite_postOp_shape`'s split, a new
  `boundarySite_backEdge_runnable`, and the two menu lemmas' extra
  case — everything else (singleton conservation, soundness,
  completeness, wf, streams, NPDRF, Iris layers, mirror) compiled
  UNCHANGED. Eval: the poller family's deferral witnesses re-derived
  ([2]*n no longer defers under the widened site sequence; [1]*n
  does — min fuel 74/90 at n=16/32, still monotone in stream length,
  the family's point preserved); 136/136 ok.
- §5d ENUMERATOR (G1 question 6, as ruled): per-site modes —
  `--backedge full|k` (k may be 0 = canonical slot only), applied
  exactly at ≥2-menu backEdge consults (a first-attempt shape bug
  misclassified single-goroutine mapIter picks as backEdge consults —
  caught by the maps rows going red in the sweep, fixed by requiring
  menu ≥ 2); fail-loud when a row hits such a consult undeclared;
  capped occurrences SKIP the alias ladder (a capped site's width is
  deliberately un-certified) and are counted + printed
  (`backedgeCapped=`) so the record states the tree. `--allow-nonterm
  N`: per-branch fuel N with fuel-exhausted branches counted
  (`nonterm=`), never members, never green-contributing; probe rungs
  landing on divergent branches tolerated under the flag; the
  driver-coupling pin tolerates fuel-out coupling streams on declared
  rows (terminating ones still must be members — noted: driver drift
  that MISREPORTS a terminating stream as fuel-out on a declared row
  would hide there; the enumeration's own tree still couples).
  Params `backedge=`/`nonterm=` wired through
  diff-coverage/coverage-manifest validation (enumerating-lanes /
  membership-only respectively); the membership singleton refusal
  keeps its teeth except on declared-nonterm rows (terminating
  singleton + counted bucket is the wedge's honest shape).
- **THE WEDGE ROW LANDS GREEN END-TO-END**:
  `goroutines/send-then-spin` (membership, width=4, sites=200,
  members=1, nonterm=200, backedge=1 — exhaustive at this program's
  bound-2 menus, backedgeCapped=0): certified terminating set {42}
  with nonterm=216 counted spin branches; oracle 42 ∈ set; the
  DONE's "exit-0 on an enumerable stream" is the row + the [0,0,1]
  exhibition. SAME-COMMIT: register #1 rewritten to its DISCHARGED
  state (+ #5's incompleteness note closed), inventory C2 → (a)
  ENVELOPED with the cost-prose correction, the known-≠-oracle list
  drops the wedge, tallies re-counted; the fairness non-preclusion
  argument recorded as a STATED PROPERTY
  (docs/2026-08-07_fairness-precision-note.md §5 — argued, anchored,
  no proof obligations per the note).
- Stage-D corpus sweep: 4 rows hit genuine ≥2-menu backEdge consults —
  fork-join/compute, muxer/client, race/negative/map-range-iter
  (all THREE fit backedge=full: 23k/18k/3.7k work — full claims kept)
  and buffered-wake/cap-one (full = 29.1M work → tier=slow with a
  fresh record, claim kept FULL). The tier=slow loopy rows re-measured
  under stage D: fifo (backedge=0 declared: identical
  steps/leaves/set, depth 27→37, 623,830 capped occurrences —
  back-edge anti-progress schedules NOT in its certification,
  recorded in the record header) and alternate (backedge=0, 98,640
  occurrences, same singleton); rw-writers and first-come measured
  ZERO ≥2-menu backEdge consults (identical trees) — no declaration,
  claims unchanged. BUG-065 filed for the five intractable rows
  (the honest-red record; sb-chan's Cases-line credit needed the
  one-line format — check-bugs parses a single line).

### Gates (slice 1 stage D)

- `GOLEAN_MEM_MAX=24G scripts/ci --diff` (artifacts/w32-sD-ci2.log,
  untracked): every step ok incl. bug-index (BUG-065 credits the three
  honest reds) and the re-pin guard (3 flips, all on the Cases line);
  drift = EXACTLY the one new id (send-then-spin PASS/membership).
  **Baseline re-pin #2** with the reason in the header;
  coverage-baseline-diff green at the pinned tree. The stage-D `--slow`
  re-certification is FOLDED into stage E's exit gate (one ~90-min
  --slow run validates the D-touched records + the E closure together;
  the C gate ran its own --slow) — recorded here as the deliberate
  economy.

## Slice 1 stage E — closure (2026-08-21)

- NPDRF: obstruction-3 note updated — `StepM`/`StepMFine` and the
  DRAFT statement now range over the WIDENED boundary set
  automatically (`StepMFine` already relaxed all boundaries), so the
  coarse-vs-fine residual the draft measures SHRANK; the weakening
  ruling + proof effort stay slice 5's, over the new point set.
- Doctrine sweep to the discharged state: nondeterminism doctrine's
  ∀-stream illustration re-scoped as the historical warning shape and
  the granularity-position bullet marked landed (history kept in
  place, discharge noted inline); inventory §7 queue item 1 → DONE
  with residual pointers; register #1/#5, C2, C3, U-1, the tallies
  and the known-≠-oracle list were updated at stages C/D.
- Fairness non-preclusion: recorded as the STATED PROPERTY at
  `docs/2026-08-07_fairness-precision-note.md` §5 (stage D) — four
  clauses, each with its mechanical anchor (`schedSlots_mem` /
  `mem_schedSlots_of_runnable` are the proved menu-set facts); no
  proof obligations, per the note's own commitments.
- Mirror: unwidened throughout — `.opDone` quits `.q7Concurrency`
  like every concurrency shape; default build + drift gate green at
  every landing commit.

### Gates (slice 1 stage E — the slice exit gate)

- `GOLEAN_MEM_MAX=24G scripts/ci --slow` (artifacts/w32-sE-ci.log,
  untracked; ~65 min wall): EVERY step ok — escape hatches,
  purity/TCB/import-direction, core build warning-free, proofs +
  Audit gate, verdi compat, goose fixtures/pins, golden lowering,
  frontend units, eval 136 ok, lane fixtures both halves, negative
  lane no-regression, re-pin guard — with the differential
  baseline-diff step reporting EXACTLY the two RECORDED standing
  alarms and nothing else:
      imported-goose/channel/google-search  PASS→FAIL (--slow only)
      sync/rwmutex-order/acquisition       PASS→FAIL (--slow only)
  — the stale pre-B1 certified records surfacing exactly as the
  tiering design intends (stage-C log: BUG-065; the §5c-fallback
  ruling is Mike's, posed in the stage report). All five re-tiered
  rows (fifo, cap-one, alternate, rw-writers, first-come)
  RE-CERTIFIED exhaustively under GOLEAN_SLOW=1 against their fresh
  records — no drift. The wedge row green under --slow.
- §5b prediction, checked line-by-line across the slice: ZERO
  strict-lane flips at every landing (confirmed at C, D, E); new ids
  exactly {goroutines/wake-then-abort, goroutines/send-then-spin};
  membership/confluent sets UNCHANGED everywhere measurable; the
  UNPREDICTED residue is the enumeration-tractability fallout
  (BUG-065 + the cap/tier re-measurements), recorded honestly at
  stage C.
- CHECKPOINT slice-1-E: stages C-D-E COMPLETE on the lane. The
  boundary set is B1+B2 as ruled; the wedge is flipped and
  corpus-exhibited; register #1 discharged; C2/C3/U-1 enveloped;
  fairness non-preclusion stated; NPDRF restated over the widened
  set. OPEN for Mike (posed in the stage report): (1) the BUG-065
  five — §5c sampled fallback (machinery drafted+reverted; witnesses
  recorded at stage C) vs budgets vs the reduction lane; (2) the
  confluent-lane tier=slow widening + the slow-timeout 3600 default —
  gate-surface changes made in lockstep, flagged for the pre-merge
  audit's gates dimension.

## POR slice — the dedup certifier (2026-08-21)

- Base: stage E rebased onto main `065edaec` (snapshot
  `refs/snapshots/w32-pre-rebase-20260821`; ONE conflicted file,
  `baselines/native-full.tsv` — main's W4.1 audit-fix re-pin composed
  with the stage-C/D deltas by applying the recorded per-stage row
  deltas to main's row set; counts restated in its header, 2324 rows).
  Charter for this slice: the POR-slice brief; THE BINDING CONSTRAINT
  (Mike 2026-08-20) recorded at the top of
  `docs/2026-08-21_w32-por-design.md` BEFORE any building.
- REDUCTION CHOSEN (design note §2, argued from the machine's shape):
  a certified STATE-IDENTITY QUOTIENT — not sleep sets/DPOR/movers —
  because (1) the B1/B2 blowup is path-multiplicity over a small state
  grid, (2) dedup has no independence relation to be wrong about (the
  binding constraint's dangerous direction cannot arise), (3) the
  exhaustiveness assets existed (`stepThread_oblivious`,
  `stepAllBranchesOk_sound`), (4) the mover lane composes later.
  Judgment logged: audit Q11 (entry-identity stamps) NOT consumed —
  no footprint lemmas anywhere in this slice; Q11 stays slice-4-routed.
- THE SPEC (trust surface, ~40 lines): `EnumSpec.lean` — `Obs`,
  `obsOf?`, and `SlowObs resultLocs m₀ r₀ o :=
  ∃ fuel ch, obsOf? resultLocs (execProgLoop fuel m₀ r₀ ch) = some o`.
  The certified records' meaning restated over it: "certified set S" =
  `∀ o, o ∈ S ↔ SlowObs …` — same substance as the lane's claim
  (wording change flagged in the design note §1: stated over the
  interpreter, not the CLI tree; the ∃-fuel form makes "terminating
  members" literal).
- THE THEOREM (proven, axiom-clean [propext, Classical.choice,
  Quot.sound]):

      checkCertM_slowObs :
        checkCert dedupNodeEqb resultLocs m₀ r₀ cert = true →
        ∀ o, o ∈ cert.obsSet ↔ SlowObs resultLocs m₀ r₀ o

  Architecture (Sym mold + comparator mold): UNTRUSTED engine
  (`GoLean/EnumDedup.lean`, partial, deletable — worklist search,
  hand-rolled hash, witness streams from discovery paths) emits a
  `DedupCert` (nodes + per-vector successor hints + members with
  witnesses); the TOTAL fail-closed checker (`EnumDedupCheck.lean`)
  re-derives every branch vector, re-runs the REAL
  `stepMulti`/`raceUpdate` per edge, matches successors via the SOUND
  equality, and replays every member's witness through the unmodified
  `execProgLoop`. Soundness = the replays; completeness = fuel
  induction + TOTAL coverage (`stepMulti_total_covered`, stated
  vec→run so no "stepFn never throws .panic" walk is ever needed:
  the checker's vector successes DETERMINE every stream's step).
- The certified fragment: N-OBL (`poolThreadOblivious` targets —
  `stepThread_oblivious`), N-L4 (single-arrival multi-candidate
  pairings — NEW `stepThread_l4_run`, the one-pick determinization),
  N-APP (NON-spilling append applies — NEW
  `applyStmtOp_append_nospill`/`stepFn_append_nospill`/
  `stepThread_append_oblivious`; added when google-search's refusal
  diagnosed as a non-spill append). Refused, fail closed: L2 `.multi`
  arrivals, consuming (multi-ready) selects, `mapIterK`, genuine
  spills, `$pkginit` rows. Fail-closed DEMONSTRATED: a diagnostic
  detector-blind certificate was REFUSED by the checker.
- The sound-equality tower (`StateEqb`/`SyntaxEqb`/`MachineEqb`, the
  last two worker-built to the established pattern and verified):
  fuel-structural `eqb → =` over Ty/GoValue (existing eqbs, new
  soundness) and Expr(58)/Stmt(40)/Assignee/SelectClauseHead/Func/
  StrictOp(48)/StmtOp/Cont(30)/Config(16)/ExecState/RaceState/
  MultiConfig — soundness ONLY (fuel exhaustion ⇒ checker refusal,
  never unsoundness). `deriving DecidableEq` verified to fail on the
  nested inductives, hence the hand tower.
- CLI: `coverage-observations --engine dedup` — cert → THE VERIFIED
  CHECKER → only then print; the DFS's accountant/sentinel/
  alias-ladder guards do not apply on this path (replaced by the
  theorem); status discipline unchanged. Gate surfaces in lockstep:
  `engine=dedup` row param (diff-coverage + coverage-manifest;
  test-lane-validation green).
- Deletion test RUN: with `GoLean/EnumDedup.lean` deleted,
  `lake build GoLean.GoCore` is green (the checker + theorem stand);
  `import GoLean.EnumDedup` occurs ONLY in `CLI.lean` (grep-verified —
  the intended dependency direction; the proofs package never sees
  it). Restored, full build green.
- RE-CERTIFICATION RESULTS (the iteration-loop payoff — before/after,
  dev box, all "after" runs CHECKER-ACCEPTED with the set equal to the
  recorded claim):

  | row | DFS (post-B1/B2) | dedup | wall |
  |---|---|---|---|
  | pipeline/request-reply (confluent) | >400M steps, INTRACTABLE (honest-red) | 17.6k nodes / 18.4k edges | 0.3 s |
  | race/litmus/sb-chan (membership {1,10,11}) | >400M, INTRACTABLE (honest-red) | 350.5k / 385.8k | 5.7 s |
  | sync/rwmutex-order ({10,20}) | >~900M, tier=slow stale record (standing alarm) | 95.2k / 111.4k | 0.9 s |
  | imported-goose/google-search (6 members) | >900M, tier=slow stale record (standing alarm) | 6.19M / 6.57M | ~157 s |
  | buffered-wake/fifo (confluent) | 114.4M steps (tier=slow) | 14.9k / 15.5k | <1 s |
  | buffered-wake/cap-one (confluent, was backedge=full) | 29.1M (tier=slow) | 4.5k / 4.8k | <1 s |
  | ping-pong/alternate (confluent, was backedge=0) | 16.2M + probe-heavy (tier=slow) | 7.0k / 7.3k | <1 s |
  | free-sync/rw-writers (confluent) | 87.3M (tier=slow) | 10.5k / 13.2k | <1 s |
  | sched-dependent/first-come ({12,21}) | 84.8M (tier=slow) | 98.7k / 114.2k | <1 s |

  Both standing `--slow` alarms RESOLVED (google-search: fresh
  theorem-backed record, stage-C witnesses cross-check; rwmutex-order:
  tier dropped — 0.9 s in the fast lane). The five stage-C/D
  re-tierings REVERSED (records deleted); fifo/alternate's backedge=0
  narrowings LIFTED — dedup explores back-edges exhaustively at
  state-graph cost, so those claims STRENGTHEN to the full tree.
  Bonus measurements (not switched, recorded): wake-then-abort
  certifies at 221 nodes; send-then-spin (THE WEDGE) certifies {42}
  EXHAUSTIVELY at 760 nodes — the spin's divergent branches collapse
  into graph cycles, no nonterm counting, no backedge cap; switching
  its row awaits a small ruling on what nonterm= means under
  engine=dedup (the membership singleton-guard exemption rides it).
- RESIDUAL, honest: goroutines/worker-pool/sum does NOT close —
  >9.5M nodes / 10.5M edges on the first probe; the strong-hash run
  did not reach closure within an 80M node+edge budget / ~20 min
  wall. Its (pool × detector) state graph is genuinely large (4
  goroutines × loops × clock states). BUG-065 NARROWED to this one
  row (Cases line updated in the same commit as the baseline re-pin);
  the principled fix remains the mover/reduction lane (slice 5),
  which now COMPOSES with dedup (ample-set restriction of the
  checker's per-node vectors, its own completeness lemma).
- Fragment-extension judgment calls, logged: (1) N-APP added when
  google-search's refusal diagnosed as a NON-spilling append (the
  conservative `consumesAppendSlice` refusal was wider than the
  consumption reality); the spill branch still refuses. (2)
  poolThreadOblivious itself NOT widened (the ∀-streams checker's
  trust surface stays untouched this slice; promoting N-APP there is
  recorded follow-through). (3) The engine's dedup equality is the
  SOUND tower eqb (a false-negative only duplicates nodes); its hash
  needed race-state structure (shadow/chan clocks) before sb-chan
  closed — 47k-nodes-at-2267-hashes was the diagnostic.
