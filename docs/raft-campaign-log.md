# THE RAFT PROOF CAMPAIGN — log

Governing instrument: `docs/2026-08-21_raft-proof-constitution.md`
(ratified 2026-08-22). Launched: **2026-08-22, [USER]** — Mike's
launch sign-off given as the autonomous-goal charter pointing at the
constitution ("complete the WHOLE remainder... don't stop to solicit
feedback... log every call [AGENT]/[USER]; do not merge to main until
the user signs off"). Base: `main` @ `f64d9b21` (the launch-audit fix
round, merged on [USER] sign-off). Lane: `raft-proof-campaign` branch (RENAMED from `campaign` 2026-08-24, [USER] request; the worktree DIR stays `.claude/worktrees/campaign` — it is the live probe run's cwd, deliberately not moved), worktree
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
- **U-c3** (2026-08-22): the wire-pin mechanism —
  `proofs/GoLeanProofs/Specs/WirePin.lean` (`goldenWire%` term elab:
  read + `Json.parse` + `NativeToIR.decodeProgram` at elaboration,
  fail-loud; standalone `ToExpr` derives, GoCore untouched) + the
  pinned wire `baselines/golden/twin-chdriver.wire.json` (sha256
  f353c3b2…, 9,310,086 bytes; emission DETERMINISTIC — two frontend
  runs, one sha) + `TwinProgram.lean`'s `twinLowered`. [AGENT]
  maxRecDepth 4,000,000 for the pin def only (the elab runs
  interpreted; parse depth scales with the wire). MEASURED: the pin
  builds in 65 s / 2.5 GB peak (per clean build; olean-cached after).
  Machine smoke: the machine executed the choice-driven twin clean —
  end line `viol=0 claims=1 committed=6 complete=1 floor=1 rounds=30`
  identical to go-side (`artifacts/campaign-u1-chdriver-machine.txt`,
  both sections).
- **U-c4** (2026-08-22): THE STATEMENTS —
  `proofs/GoLeanProofs/Specs/RaftAgreement.lean`: `twinRun`
  (runProgramM wiring, exactly native-json-run's), `AgreementT1`
  (∀ fuel ch, completing ⇒ violations = 0), `CompletionWitness`
  (∃ stream/fuel completing with floor met), the aboutness sentence
  in the docstring. Elaborates (778 ms on the cached pin).
- **CHECKPOINT 1** (recomputed): 4 units landed; Arc 1 remaining =
  check-golden wire entry (gate-additive) + arc gate + the
  designation/merge asks. Arc 3 worker in flight.
- **U-c5** (2026-08-22): check-golden twin-wire entry (frontend↔bytes
  link; term↔bytes holds by mechanism). Two self-inflicted lessons,
  both [AGENT]-logged: (i) edited the gate script WHILE a gate run was
  in flight — the race read as a spurious FAIL (one writer includes
  not racing your own gate); (ii) the section's scratch DIRECTORY
  broke the script's files-only EXIT trap — every entry green, exit 1
  (fixed: the section cleans itself).
- **U-c6** (2026-08-22): the three Specs modules imported from the
  GoLeanProofs aggregator (the 1b2 sweep flagged them un-swept —
  the gate working); full proofs build green incl. Audit.
  **ARC 1 GATE: RESULT: PASS** (GOLEAN_ALLOW_NO_DIFF=1 — fresh lane,
  no runtime change, the sanctioned hatch with visible notes;
  artifacts/campaign-arc1-gate2.log). **ARC 1 BRANCH-COMPLETE** @
  this tip. Note for later: the gate printed "Challenge.lean
  elaborates (0 sorry warnings)" where main's runs printed 56 —
  investigate before any merge ask (possible count-extraction
  difference in this lane; the step itself is green). **RESOLVED
  (U-c8)**: the counter grepped straight quotes, Lean prints
  backticks — the count was cosmetic-zero on every gate everywhere
  (main included, unnoticed); pattern made quote-agnostic, 56
  verified with it; pass/fail was exit-code-based throughout, never
  affected.
- **Arc 3, unit 1 — LANDED on `campaign-arc3`** @ 4bbcf5fc (worker
  report, top claims to be re-verified by its successor per §4.3):
  `RefinedProofStructure.lean` (1341 lines, zero hatches) — the ghost
  vocabulary, the 11 obligation shapes, `refined_raft_net_invariant`
  re-proved, the deghost/simulation/`lower_prop` transfer chain, a
  discharge witness; AxCheck 987 decls in [propext, Quot.sound];
  lane gate PASS. Design note + arc log + unit-2 charter on the lane.
  [AGENT] calls D1–D5 in the arc log.

- **U-c7** (2026-08-22, Arc 2 opens): THE WITNESS PROBE — the
  statement's own `twinRun` evaluated compiled (`#eval`, lake env):
  `twinRun 8000000000 [] = .ok #[int 0, int 1, int 6, int 1, int 1]`
  — 14:00 wall, 1.7 GB peak. The CompletionWitness is TRUE and
  executably confirmed at the statement's own definition; the
  AgreementT1 shape is exercised (violations = 0 at the observable).
  [AGENT] route consequence: raw kernel evaluation presumed
  infeasible at compiled:kernel ratios but NOT assumed — the Arc-2
  route study (worker, lane `campaign-arc2`) measures the kernel cost
  curve at K ∈ {10,100,1k,10k} and decides among raw-rfl / WP
  completion walk / certified-run checker, memo + unit-2 charter as
  its deliverable. Arc-3 unit 2 (election-safety chain) running in
  parallel on its lane.

- **Arc 3, unit 2 — LANDED on `campaign-arc3`** @ 1dbd15a6 (worker
  report; successor re-verification of unit 1 done and recorded
  first): **ELECTION SAFETY PROVED** — the chain
  votes_le_currentTerm → votes_correct → candidates_vote_for_selves
  → cronies_correct → constructive quorum pigeonhole →
  `one_leader_per_term_ghost` → **`one_leader_per_term_invariant`**
  (base-reachable, ghost-free) + `oneLeaderPerTermStatement_holds`
  (Properties.lean's P1 transfer target discharged natively).
  ElectionSpecLemmas.lean 730 lines + ElectionSafety.lean 1766 lines;
  AxCheck 1173 decls in [propext, Quot.sound]; lane gate PASS.
  Notable [AGENT] call: the sweep fired on Classical.choice (core
  List.erase lemmas) — fixed CONSTRUCTIVELY (local eraseOne), never
  by widening the axiom set (GAP-4 records the doctrine question).
  [AGENT] next: worker continues the lattice (unit 3:
  cronies_term/term_sanity → candidate_entries toward T3 leader
  completeness) while the Arc-4 interpreter seam waits on Arc-2's
  route memo — T1 and T3 progress in parallel, the seam design is
  mine when the memo lands.

- **Cross-lane record events** (2026-08-22 evening, [AGENT]):
  (1) The launch-fixes 27-trace machine re-run FINISHED: **27/27
  traces AGREE byte-for-byte at the fix-round tip** — 280/484
  supported-prefix blocks executed, every ok-tier and rendered
  expectation green, zero disagreements
  (artifacts/launch-fixes-rerun/machine-tier-full.txt). D5-F3's
  disposition discharged: the machine tier is no longer quoted from
  a stale tip. (2) The 95145bc3 p2 rescue resolved HONESTLY AS A
  LOSS: the rescued output shows the 25-hour run CRASHED at its
  comparison step (FileNotFoundError — its go-trace comparison file
  died with the pruned worktree), so no machine verdict for
  probe_and_replicate exists at 95145bc3; the holders worked, the
  truth they caught is the crash. (3) probe_and_replicate RELAUNCHED
  at the fix-round-tip frontend from the CAMPAIGN worktree (stable
  for the campaign's life), durable output
  (artifacts/launch-fixes-rerun/probe-and-replicate-campaign-tip.txt)
  — verdict in ~1 day; until then the trace family's honest number is
  27-of-27-attempted AGREE, 1 trace unmeasured.

- **Arc 3, unit 3 — LANDED** @ d07c5382: the candidate_entries ring
  (CandidateEntries.lean, 1199 lines) — cronies_term,
  no_entries_past_current_term (second BASE-principle instantiation),
  candidate_entries_invariant (every entry, logged or in flight,
  created under an election winner of its term). AxCheck 1244 decls
  clean; lane gate PASS; INVARIANT INDEX opened (10 rows — the Arc-4
  seam's consumption interface). [AGENT]: worker ROTATED — the
  original (3 units, ~819k tokens) is fenced complete; a fresh
  successor took the lane for unit 4 (leaderLogs ring →
  leader_completeness) with successor re-verification first — the
  gallery rotation pattern, one writer preserved.

- **Arc 2, unit 1 — LANDED on `campaign-arc2`** @ 18cb0b25 (route
  study; gate PASS): minimal completing fuel MEASURED = 711,616
  subject steps + 1,382 init; kernel ladder K∈{0,10,100,1000,10000}
  — K=10k DNF at 63.4GB/50min, kernel:compiled ≥300×, monolithic rfl
  refuted at ≥3.1TB extrapolated; heap append-only 103→36,376 cells.
  ROUTE DECIDED [AGENT]: (c) checkpointed segment walk (states
  reflected WirePin-style, rfl segments sized by measured retention,
  kit composition, ~57 CPU-h projected, segment-parallel); fallback
  (d) verified fast-twin evaluator; WP walk refuted FOR THE WITNESS
  (stays T1's ∀-side instrument). Unit 2 dispatched: the go/no-go —
  one reflected MID-RUN checkpoint + measured segments at heap scale,
  parallelism-costed projection, GO/NO-GO in the memo.

- **U-c9** (2026-08-22): the Arc-4 seam design of record
  (`docs/2026-08-22_campaign-arc4-seam-design.md`) — three layers:
  absState at round boundaries (proof infra, never statement
  vocabulary), ~20 per-handler interpreter-run equations (WP/kit
  walks, §4c/§4e's translation-validation shape; W7/SpecTec
  convergence recorded), the round induction + checker-implication
  lemmas consuming Arc 3's network. Unit ladder A4-U1..U10; the
  pilot (smallest handler equation end-to-end) is the go-signal
  before scaling. [AGENT] alternatives-considered recorded (direct
  induction refused, segment-rfl scoped to the witness only).

- **U-c10** (2026-08-22): internal integration — campaign-arc3 (tip
  d07c5382, units 1-3) merged INTO the campaign branch ([AGENT]: lane
  composition, not a main landing; proofs build green post-merge at
  466 jobs); lane `campaign-arc4` opened off the integrated tip and
  **A4-U1 (the pilot) DISPATCHED**: absState v1 grounded in the
  instrumented heap shape + the smallest handler equation
  (becomeFollower/advanceCurrentTerm) via the kit + the GO/NO-GO
  verdict against the gallery-example cost bar. Three workers now in
  flight: Arc-2 go/no-go, Arc-3 unit 4 (leaderLogs), Arc-4 pilot.
- **CHECKPOINT 2** (recomputed from `git log --oneline f64d9b21..`
  on this branch: 12 commits; lanes: arc2 5 commits @18cb0b25, arc3
  19 @d07c5382 integrated, arc4 opened): Arc 1 branch-complete
  (statements pinned, gate PASS); Arc 2 route decided by measurement;
  Arc 3 election safety + candidate_entries PROVED (1244 decls
  clean); Arc 4 designed + pilot running. The [USER] queue below is
  the campaign's only external dependency.

- **Arc 3, unit 4 — LANDED** @ 84711394 (successor worker;
  re-verification of unit 3 done first, all held): the leaderLogs
  ring (LeaderLogs.lean, 3908 lines) — term-sanity trio (first real
  `lift_prop` consumer), leaders_have_leaderLogs,
  **one_leaderLog_per_term**, + the votes-with-log closure the chain
  forced; **`leader_completeness` STATEMENT pinned** (proof = units
  5-7, dependency list = GAP-6, honest). Sweep 1403 decls in
  [propext, Quot.sound]; lane gate PASS; index 23 rows. Four new
  Lean gotchas recorded for successors (the Classical.choice-via-
  LawfulBEq drag being the sharpest). Unit 5 dispatched: the
  creation ring (every_entry_was_created → … → leaderLogs_preserved).

- **Arc 4, pilot (A4-U1) — LANDED on `campaign-arc4`** @ 21f0cd51,
  gate PASS: **architecture GO, hand-walk cost NO-GO** — the
  equation form PROVED end-to-end at the smallest callee
  (alt_call_span + witness + live projection readout; absState v1
  grounded in instrumented heap contact — one 32-field raft struct
  cell), but becomeFollower measures 3,233 steps / 4 consumed
  choices / ~9 proof-lines-per-step at leaf granularity, five
  ingredient classes have no kit form INSIDE the smallest handler,
  and 20 handlers ≈ 20-60 gallery-units by hand. OQ-A both-layered;
  OQ-B call-enter covers fid+interface, not closure call-values;
  **OQ-C REFUTED** (handlers consume choices — jitter + mapIter —
  equations quantify over consumed prefixes); charter's
  advanceCurrentTerm doesn't exist in the lowered subject (Verdi
  name) — becomeFollower substituted, logged. [AGENT] maxim-(a)
  moment taken as designed: the pilot priced the grind BEFORE
  scaling; re-design = **A4-U2, the handler-fragment Sym-evaluator
  extension** (primary; W7 SpecTec convergence the alternative; kit
  lifts regardless — promotion ledger opened). Seam design note to
  be amended with the pilot's answers.

- **Arc 3, unit 5 — LANDED** @ 2d93b2f0: the creation ring's
  feasible slice (CreationRing.lean, 2511 lines) —
  every_entry_was_created, base logs_sorted + constructive sorted
  machinery, votesWithLog_sorted + term_sanity,
  terms_and_indices_from_one, three new lift_prop consumers; sweep
  **1528 decls clean**; index 34 rows; GAP-7 recorded WITH
  import-closure evidence instead of silently attempted (the
  log-matching heavies block two members — exactly unit 6); GAP-2
  zero contact (ring is plain rri). Integration-readiness paragraph
  delivered (compat/verdi self-contained, merge-tip-never-cherry-pick).
- **Arc 2, unit 2 — LANDED** @ c7b35e8a: **NO-GO for the segment
  walk, honestly measured** — reflector built and cheap (350k-step
  checkpoint: 3:47/2.7GB/101MB olean), but mid-run kernel cost is
  HEAP-LINEAR (2.22 s/step, 157 MB/step at 19k cells; seg-500 OOM at
  48G) → 440-800 CPU-h projected, no fitting parallelism on the box.
  Unit 3 re-chartered as fallback (d): the verified fast-twin
  evaluator, OPENING with a trie kernel microbenchmark before any
  build; if the microbench misses, the witness reports honestly
  blocked at kernel scale. Census completed: 243 functions (+8 defer
  callees resolved).
- **[AGENT] CONVERGENCE NOTE** (structural, feeds prioritization):
  the ∀-side (Arc 4's handler equations) and the ∃-witness (Arc 2's
  last computational fallback pending) now both point at the SAME
  missing instrument — the handler-fragment Sym extension (A4-U2, in
  flight). If it lands, the witness's WP-completion route (refuted
  only on hand-walk cost) reopens with automation. The Sym extension
  is therefore the campaign's critical path; Arc-2's (d) proceeds in
  parallel as the cheaper-if-it-works alternative.

- **Arc 2, unit 3 — LANDED** @ 885204f8: **microbench GO** — trie
  heap at 36,376 entries measures 9.4 ms/op / 0.44 MB/op in the
  kernel (targets ≤25/≤2 pre-stated; >2× headroom; ~240×/~360×
  better than the naive heap) → (d) projects the witness at 4-60
  CPU-h over ~14 fast segments. Convergence carry-forward written
  (§6.6) + the untrusted-method guardrail (§6.7.5). Unit 4
  dispatched: FastEval build (exemplar arms → the ~50-arm wave →
  the MID-BUILD gate → staged assembly; the long kernel run may be
  a staged detached follow-on rather than in-unit).

- **Arc 3, unit 6 — LANDED** @ 86d372c0 (3rd-gen worker;
  re-verification held; the unit-5 lesson executed — full 23-file/
  9,760-line closure derived and POSTED before proving, scoped to
  the self-contained 7-file prefix): **LOG MATCHING PROVED** — base
  `log_matching` + `logMatchingStatement_holds` (the second T3-named
  invariant discharged natively), GAP-5 closed
  (leaderLogs_sorted/contiguous), base leader_sublog with the ghost
  chain's first base-level payoff, the ten-field lifted bridge both
  GAP-7 subtrees consume. LogMatching.lean 2565 lines; sweep **1652**
  clean; index 41 rows (self-correction recorded: was misstated 43);
  lane gate PASS. Units 7-8 chartered (~6,800 lines remaining to
  leader_completeness's proof).

- **Arc 4, A4-U2 slice 1 — LANDED** @ 8c1f5d9e: the Sym extension's
  design note (five classes = quit-site lifts, not domain work;
  sortSlice needs NOTHING; call-entry one lever for fid/closure/
  interface; choice story = composition-level canonicalization, pick-
  prefix threading rejected; channel-logic salvage honestly NEGATIVE)
  + class 1 (struct-store normalization) end-to-end with ZERO edits
  to the 8,193 existing Sym lines (delegating stepFnT, Sym/TableExt
  652 lines). **THE RE-MEASURE**: the pilot leaf's ~105 span lines +
  helper lemma → ONE transported window (3-line rfl + 6-line
  refinement application), ∀ρ ∀σ-extending ∀ch; two measured gotchas
  recorded (smartUnfolding reversal 671s↔7.3s; decide +kernel for
  γ-projections). Gate PASS, 471 jobs green. Slice ladder: 2 =
  sync-ops, 3 = call entry, 4 = choice-crossing composition.

- **Arc 4, A4-U2 slices 2+3 — LANDED** @ 785a3461: sync-ops
  census-scoped (Mutex lock/unlock only — no Once on the path,
  checked; the tabled storeLocT fix caught by an honest probe-quit at
  step 102) + the one-lever call entry (enterFrameT running the
  MACHINE'S OWN table helpers — zero re-implementation; Agrees =
  equality not sub-table, with the soundness reasoning recorded;
  delegation preserved a THIRD time — layered stepFnTB→stepFnT→
  stepFn', shipped statements untouched). Interface-receiver dispatch
  honestly scoped OUT (residual 2b — one logger call on the path).
  RE-MEASURE: becomeFollower = ONE 189-step window to the designed Q3
  boundary (51 s build); **projection now INSIDE the gallery bar**
  (≈600-1,000 lines/handler vs 3,000-6,000 hand). Worker
  recommendation adopted [AGENT]: slice 4 (choice-crossing
  composition, smallest instance = Intn's single pick) BEFORE A4-U3
  — U3 becomes assembly after it. 13 Audit/Kit pins paid (slice-1
  debt noticed and settled by the worker unprompted).

- **Arc 3, unit 7 — LANDED** @ 44b0794b: the AppendEntries feeder
  chain, all ten targets (AppendEntriesChain.lean 3206 lines) — incl.
  append_entries_request_reply_correspondence (the campaign's first
  real dup/drop fault-model use, subset_reachable machinery),
  leaderLogs_sublog, leaderLogs_entries_match (the exit). Sweep
  **1805** clean; index 51 rows; GAP-1 kept untriggered by a
  pre-state closure ([AGENT] call, promotion-ledger payoff). Two new
  successor gotchas recorded. [AGENT]: worker ROTATED at 819k tokens
  (risk asymmetry over its no-strain self-report) — 4th-gen
  successor dispatched on unit 8, the GAP-7 assembly (~3,566 lines;
  leader_completeness's last prerequisites; split point permitted).
  A4 slice 4 (choice-crossing composition, full-span becomeFollower)
  dispatched to the Arc-4 worker with the stop-at-boundary rule
  ACTIVE.

- **Arc 4, A4-U2 slice 4 — LANDED** @ dab1163d (clean-boundary stop
  per the active rule): **THE HANDLER SPINE EXISTS** —
  `stepFn_pick_generic` (type-generic map-range pick) +
  `stepFnIter_window_pick_window` (pre-window + quantified pick +
  post-window), with §4(ii)'s valuation-absorption REALIZED (the
  picked key symbolic in the fixture: ONE post-window serves every
  pick; canonicalization as design rule). becomeFollower's 945-step
  prefix-quantified span at ~130 lines (vs ~8,500 at the pilot's
  hand rate); pre-window grew 189→642 steps quitting EXACTLY at the
  designed Q3 pick; two same-lever Q4 lifts found by honest window
  quits. Full span (3,233) deliberately NOT claimed — the four-item
  U3 checklist posted. [AGENT]: worker rotated at 820k; fresh
  successor dispatched on A4-U3 (the first FULL handler equation +
  the A4 scale verdict re-projecting U4..U9).

- **Arc 2, unit 4 — LANDED** @ 0c462c7c: **THE VERIFIED FAST-TWIN
  EVALUATOR IS PROVED** — trie heap + γ (range dump; append-only
  made WF-free), stepFast arm-for-arm (~170 fun_cases + 29 manual),
  the loop-transport bridge, and the ANCHOR: seed + StateWf + all
  1,382 init steps kernel-re-run against reflected literals in one
  8:18/36.7GB equation. Worker ran its own 3-fork wave with a
  written template + its own re-verification (a census-classifier
  blind spot caught and mirrored). Mid-build gate MARGINAL GO
  (fast-500 2:28/21.6GB vs slow OOM; heap-size dependence REMOVED;
  35-80 CPU-h projected, levers named). Assembly COSTED AND STAGED
  as unit 5 (charter §6.8) per directive. FLAG for the operator's
  merge step: `import Audit.FastEval` touches Challenge's trusted
  closure → the comparator-judge landmark is owed at merge.
- **Arc 3, unit 8 — LANDED** @ becfe284 (4th-gen; re-verification
  held; closure recomputed to 3,519 lines catching the charter's
  stale sum): **GAP-7 CLOSED, BOTH HALVES** —
  LeaderLogsAssembly.lean 3,965 lines; the allEntries_log summit
  (upstream's ~500-line Ltac splice re-derived through two
  containment lemmas, §9 guided re-proof); sweep **1985** decls
  clean; index 55 rows; GAP-2 still zero contact (re-verified at
  the closure incl. AllEntriesLog, the predicted first contact).
  **GAP-6 is now the ONLY named gap on the leader-completeness
  path** — unit 9 chartered (6 files, ~3,428 lines, split point
  recorded).

- **Arc 3, unit 9 — LANDED** @ d5efc9e8 (context-rule stop taken at
  PrefixWithinTerm's edge, exactly as flagged): 4 of 6 GAP-6 feeder
  files proved (LeaderCompleteness.lean 1,426 lines —
  allEntries_candidateEntries/leader_sublog/log_matching + the AE
  term-sanity lift; 1,134/3,428 closure lines); sweep **2029**
  clean; index 60 rows. **Leader completeness is two files away**:
  prefix_within_term (1,915L, all deps ported) +
  LeaderCompletenessProof (379L) = the unit-10 charter. [AGENT]:
  5th-gen rotation (worker at 816k).

- **Arc 3, unit 10 — LANDED** @ d7e3cfc8 (5th-gen): **LEADER
  COMPLETENESS PROVED — GAP-6 CLOSED** (PrefixWithinTerm's ~590-line
  upstream summit collapsed to ~170 Lean lines via one extracted
  positioning lemma; leader_completeness_invariant +
  _directly_committed + _committed, ghost-layer landing point exactly
  as upstream — no base projection exists there, checked). Sweep
  **2138** decls in [propext, Quot.sound]; 80 commits on the lane;
  gate PASS. **THE T3 LADDER: election safety ✓ · log matching ✓ ·
  leader completeness ✓ · state-machine safety = the remaining
  head** — and GAP-2's msg-ghost contact is CONFIRMED there (unit-11
  charter posted: SMS 3,199L + SMSPrime 518L + the msg-ghost layer,
  multiple units expected). Designation of any of these as headline
  remains [USER] (§3.2), queued with the rest.

- **Arc 3, unit 11 — LANDED** @ 24dbbf97: **THE MSG-GHOST
  FOUNDATION (GAP-2 consumed)** — MsgRefinement.lean 1,133 lines:
  the vocabulary, the eleven obligation shapes,
  msg_refined_raft_net_invariant (the new proof step = ghost-stage
  reconciliation), the erasure transfer through all seven
  step_failure legs, msg_lift_prop(_all_the_way), and a real
  discharged witness. Sweep **2213** clean; SMS closure re-derived
  fresh (20 files/9,612 lines, waved W-A..W-F; two no-proof-file
  findings recorded); GAP-8 (reghosting direction, SMS-only) newly
  censused; the primed msg set deferred with per-site census
  (GAP-1's msg-side instance). Gate PASS. Unit-12 charter: the W-B
  plain leaves (~1,695 lines) then W-C as budget allows.

- **Arc 3, unit 12 — LANDED** @ 4a37aebb: six of eight W-B leaves
  (SafetyLeaves.lean 1,082 lines — the joint log/allEntries movement
  lemmas, transitive_commit, all_entries_leader_logs,
  in_log_in_all_entries, log_all_entries, lastApplied_le_commitIndex
  BASE, no_append_entries_to_self BASE); sweep **2287** clean; index
  69 rows. **The context rule honestly exercised**: the worker
  detected its own strain signature mid-draft (guessed signatures,
  placeholder hatches), REVERTED UNCOMMITTED at the clean boundary,
  and recorded the recon for the two remainder files — the exact
  behavior the conventions exist to produce. [AGENT]: 6th-gen
  rotation; unit 13 = the W-B remainder (match_index_sanity,
  prevLog_candidateEntriesTerm, recon recorded) then W-C's first
  msg-ghost consumers.

- **Arc 3, unit 13 — LANDED** @ d14bfd6a (6th-gen): FULL charter —
  **W-B 8/8 complete** (match_index_sanity BASE,
  prevLog_candidateEntriesTerm via the term-level twin), **the
  primed msg obligation set ported on genuine first need** (the
  pre-state route structurally unavailable at
  GhostLogsLogProperties — the honest trigger; the primed principle
  DERIVED from the unprimed at Q := reachable → Pr, ~60 lines vs
  upstream's 290-line staged induction, §9 call), and **W-C's first
  two msg-ghost consumers** (GhostLogs.lean; slices 71-74 compiled
  first-attempt). Sweep **2362**; index 71 rows; 101 lane commits;
  gate PASS. One consolidation candidate flagged (unit-3
  entry-level preserves derivable from term-level). NOTE → [USER]
  queue: the comparator-landmark note CROSSED ITS THRESHOLD (104 >
  100 commits, report-only) — the judge run is owed at the first
  lane merge, as flagged every unit.

- **Arc 2, unit 5 — PARKED IN FLIGHT** @ 7e120182: the witness wave
  is EXECUTING (detached, session-independent; 62/757 at the park;
  ~44 CPU-h ≈ 15-20h wall remaining; manifest-driven,
  continue-on-failure + solo-retry, resume commands verbatim in the
  log). Emission COMPLETE 45/45 groups at 184 MB (the ~30-60 GB
  projection was ~200× pessimistic — olean compaction); the 48G
  lever REFUTED by measurement (SEG=1000@36G adopted, central ~53-55
  CPU-h GO); composition fully GENERATED with the endgame de-risked
  live (literal-heavy simp/rfl measured-OOM → generic glue lemma);
  three honest kill points + a masked-OOM lesson recorded.
  CompletionWitness NOT yet proved — stated plainly; the four-step
  completion recipe is in the log. [AGENT] next dispatch on this
  lane = when the wave's manifest reads done: retry pass →
  composition build → the witness.

- **Arc 3, unit 14 — LANDED** @ 88deb524 (6th-gen, second full
  charter): W-C remainder + W-D, all seven files —
  no_AE_replies_to_self, no_AE_to_leader, match_index_leader,
  prevLog_leader_sublog (unit 13's PLCET paying off), the two
  ghost-log invariants (the handleAppendEntries_ghost_log engine),
  and **state_machine_safety' — THE SMS-PRIME STATEMENT** (~250-line
  upstream nw' soup factored to two shared cores, §9 call); the
  msg-side primed layer COMPLETE (all ten bridges). Sweep **2439**;
  index 78 rows; 110 lane commits; gate PASS. Unit 15 = the FINAL
  STRETCH: MatchIndexAllEntries (last pre-cap file, every dep
  PROVED) → the W-F cap (GAP-8 reghosting +
  StateMachineSafetyProof's interior). [AGENT]: 7th-gen rotation.

- **Arc 3, unit 15 — LANDED @ 708773ff: THE T3 SAFETY LATTICE IS
  CLOSED.** Election safety ✓ (u2) · Log matching ✓ (u6) · Leader
  completeness ✓ (u10) · **State-machine safety ✓ (u15)** — with all
  three Properties.lean transfer targets discharged natively, the
  full fifteen-probe axiom transcript verbatim in the arc log, sweep
  **2617** declarations within [propext, Quot.sound], zero hatches,
  gate PASS. En route this unit: GAP-1's state-side primed set on
  its first genuine trigger (the Q-route again — compiled first
  attempt), GAP-8 closed (reghosting via the packet-subset
  constructors, upstream's 200-line detour never entered), and the
  3,199-line SMS interior (the `everything` induction). **GAPs
  1/2/5/6/7/8 ALL CLOSED**; GAP-4 never fired in fifteen units. The
  unit-11 census — 20 files, 9,612 upstream lines — is ENTIRELY
  PORTED. This is a §4.2 MILESTONE-CLASS claim (a T3 tier's
  spec-level lattice complete): the milestone AUDIT and any
  designation are [USER] acts, queued below; the lattice's evidence
  is the lane itself (110+ commits, per-unit gates, seven
  generations of successor re-verification, every claim
  derivation-anchored). Unit-16 wrap chartered (consolidation
  candidates, the closing design section, end-state
  re-verification).

- **Arc 4, A4-U3 — LANDED** @ 5e7834a9: **THE FIRST FULL HANDLER
  EQUATION IS PROVED** — `becomeFollower_handler_eq`: from any
  γ-extending state with projection `some n`, over EVERY consumed
  choice prefix, exactly 3,234 steps to `.stop` with projection
  `specBecomeFollower n 0 lead`; witness at the concrete stream;
  1,307 target-layer lines / ~50 min builds (the extension's 3-5×
  win over the NO-GO projection, realized). [AGENT] deviation
  accepted: class-2b completed properly in enterFrameT instead of
  hand splits (kills the recurring cost for ~20 handlers; 12→7
  windows). One summary-layer count correction recorded (14 pins,
  not 15). Scale verdict: waves 1-3 ≈ 15-25 U3-shaped sessions;
  binding constraints = state literalization (U4 slice 0) + the
  absState entries/outboxes extension (the spec-side obligation
  before message handlers).
- **Arc 3, unit 16 — THE LANE ENDS BRANCH-COMPLETE, PERMANENTLY** @
  c131f278: end-state re-verification from a CLEAN build (sweep 2615
  post-consolidation, fifteen-headliner probe verbatim, hatch grep
  zero across all sixteen files, index span-verified 84 rows);
  consolidation done (~220 duplicated lines deleted, statements
  unchanged; one candidate SKIPPED with reason); GAP-4 closed moot;
  the design note's closing section + refreshed integration
  readiness. Sixteen units, ~95 slices, 129 commits. The [USER]
  queue carries the milestone audit, the merge, and the owed
  comparator-judge run (133 commits).

- **THE MILESTONE AUDIT — COMPLETE, AND THE LANDING IS DONE**
  (2026-08-24): R1 statement fidelity = **FAITHFUL everywhere** (the
  whole spec base diffed — zero drift; refutability witnesses
  compiled; 24 fresh axiom probes; "statement laundering was
  structurally impossible on this lane"). R2 proof shapes = **every
  §9 call EQUIVALENT or strictly stronger** (six majors + the three
  route calls verified against Coq primary source; re-verification
  chain spot-checked EXACT). R3 records = quantitative record
  re-derives exactly (84/84 index rows exist and elaborate; the
  9,612-line census exact; sweep 2615 fresh-derived twice) with ONE
  HIGH: **S1 — units 2-3's gate artifacts came from the wrong
  worktree** (a record defect, not code — mitigations verified:
  unit 4's in-lane gate + the audit's own fresh tip build; corrected
  in place, not re-staged) + S2-S6 causal/cite/arithmetic items.
  FIX ROUND applied on the lane (e88b153c: the record corrections,
  ten new curated pins making the coverage sentence true by
  construction, R1's eleven cite fixes, R2's provenance notes);
  re-gate PASS; **comparator-judge PASS (56 theorems, 393s) at the
  audited tip**; [AGENT] verifier-step call: replaced by coordinator
  spot-verification of S1 (three independent probes confirmed) under
  the wrap directive. **LANDED ON MAIN ff-only @ df8a9141** per the
  [USER] conditional authorization — the T3 safety lattice is on the
  mainline.

## Awaiting [USER] — the queue

- **POSED — designation of `AgreementT1` + `CompletionWitness`**
  (`proofs/GoLeanProofs/Specs/RaftAgreement.lean`; constitution §3.2 —
  the walker list is Mike's act; the aboutness sentence is the file's
  docstring).
- **POSED — Arc 1 merge + its audit ask** (branch-complete, gate
  PASS; proposal on Mike's return: a focused statement-adequacy
  review — the D3-dimension — over the Arc-1 diff, Opus, plus the
  standing semantics dimension; scale ~2 reviewers).
- **[USER] 2026-08-24: the milestone audit APPROVED as proposed
  (RUNNING: 3 Opus reviewers, verifier to follow); the Arc-3 → main
  merge PRE-AUTHORIZED conditional on the audit coming back green**
  ("agree, you can land campaign-arc3 on main, once the audit comes
  back green") — execution order on green: findings fixed if any →
  the owed comparator-judge run → ff-only merge to main → report.
  Designation deferred to the statement layer's own main landing
  ([USER]-acknowledged: no input needed now).
- **DISCHARGED (was POSED) — the Arc-3 milestone audit ask** (constitution §4.2: a
  tier's lattice proved = milestone = adversarial audit before the
  claim is built on): proposal — 3 Opus reviewers (statement fidelity
  vs verdi-raft 1:1 at the pin; proof-shape/§9-call review of the
  guided re-proofs; records/index honesty) + 1 verifier, over the
  campaign-arc3 lane's final state. [USER] may waive/trim; the ask
  is unconditional.
- **DISCHARGED — Arc 3 merge**: landed on main @ df8a9141 with the
  judge run (56 theorems PASS at e88b153c).

## Coordinator incident (2026-08-24, [AGENT], recorded before repair)

My shell's working directory drifted to the campaign-arc4 worktree at
its creation and STAYED there: 16 coordinator log commits (U-c10
through the T3-milestone entry) landed on `campaign-arc4` instead of
`campaign` — a one-writer-per-worktree violation by the coordinator,
file-disjoint (this log file only; both arc-4 workers flagged the
interleaving and I misread their flags as history-visibility). Repair:
this commit consolidates the complete log onto `campaign` (the arc-4
copy was the up-to-date lineage); arc-4's history keeps the
interleaved commits (rewriting under a worker is worse); at arc-4's
integration the file contents converge. Rule adopted: coordinator
commits use absolute -C paths, never cwd.

## CALIBRATION — timeline predictions (logged at [USER] request)

**P-2026-08-24 (the standing prediction, made with T3 closed, 5
handler equations proved, the witness wave ~1/3 through):** to the
constitution's ends (T1+T2) — CompletionWitness ~1-2 days from the
wave's resume; T1 ∀-side ~2-4 weeks (remaining ~15 handler equations
at 15-25 sessions with wave-1 velocity favoring the low end; the
round-induction/checker-implication assembly is the no-precedent
soft spot); T2 ~1-2 weeks after T1 (lattice already node-set-generic).
**Total: ~4-7 weeks of campaign time at current velocity**, tracking
~2× ahead of the launch-era "months" framing. Assumptions: box and
worker cadence hold; audit/merge cycles add calendar time not
counted here. Score this against actuals as the experiment proceeds.
(For the record, the launch-era implicit estimate had the Verdi
lattice as the long middle; it took ~2 days — the two structural
bets, the lattice port and the Sym extension, both beat projection.)

## PAUSE (2026-08-24, [USER]): compute re-planning

Mike is pausing the campaign to figure out compute; the goal will be
unset; instruction: wrap coherently, land everything on ONE campaign
branch, prepare for a remote push. Wrap plan [AGENT]: (1) integrate
campaign-arc3 @ c131f278, campaign-arc2 @ 7e120182, campaign-arc4 @
14f37f20 into `campaign` (internal composition; the arc-4 merge
resolves the log-file conflict by taking this branch's consolidated
copy); (2) fast gate on the integrated branch; (3) the witness wave
KEEPS RUNNING through the wrap ([USER] 2026-08-24: "not urgent to
pause, don't kill the long-running shell") — manifest-driven,
detached, resumable if it ever dies; done-segment oleans in the
arc-2 worktree's .lake; resume commands in the arc-2 log; (4) the
probe_and_replicate re-run left running (1 core, ~135MB — kill
`pgrep -f 'traces probe_and_replicate'` if compute needs it; restart
command in this log); (5) the milestone audit reviewers run to
completion (they read the frozen arc-3 tip; reports inform the
post-pause main landing under the standing [USER] conditional
authorization). Push: prepared, offered, not executed (sign-off at
the moment per protocol).

## [USER] guidance (2026-08-24 mid-campaign checkin): clever tricks, not stupid tricks

Mike's principle, recorded verbatim-in-substance: agents drift toward
'stupid tricks' — grinding on representation-level properties we
cannot control, or specialized tactics against ACCIDENTAL features of
a proof. What this proof needs is 'clever tricks': the PL community's
classics — separation logic / Iris, symbolic execution, process
calculi, refinement / simulation, plus the optimizing tricks around
them (clever IRs, certificate replay). New tricks are permitted (and
may be genuinely new), but any trick that does NOT map to a classic
concept is SUSPICIOUS and takes extra scrutiny. When a scalability or
proof problem appears: reach for the classics FIRST; wilderness only
when they fail.

**[AGENT] adoption + classification audit (same date):**
- Convention adopted: every new proof mechanism's design note carries
  a LINEAGE line naming its classic ancestor; unmappable ⇒ flagged
  for scrutiny before shipping. Operating rule: classics first,
  measurement as the referee BETWEEN classics, wilderness only with a
  named reason and a lineage note.
- Audit of standing machinery: Arc 3 = Verdi ghost-refinement
  (classic); the Arc-4 seam = refinement mapping + translation
  validation (classics; the design note to be restated explicitly in
  forward-simulation vocabulary); Sym extension = symbolic execution
  via conservative extension (classic); Arc-2 evaluator + segments =
  data refinement + certificate replay (classics); kernel_rfl =
  computational reflection, no trust change (classic, scrutinized,
  passes); exec-slow = the de Bruijn criterion (classic).
- WATCH-LIST (the honest 'stupid trick' risk): (1) representation-
  level accommodations (maxRecDepth, smartUnfolding, decide +kernel,
  generated literals) — tolerated scaffolds, one already retired by
  kernel_rfl; must not accrete; (2) **the address-concrete handler
  fixtures — the top classic-ward refactor candidate**: make the
  handler equations allocation-symbolic via the kit's own
  separation-logic framing BEFORE the message-handler waves scale on
  the concrete-address pattern.

## RELAUNCH (2026-08-24, [USER]): the campaign resumes

Same goal charter, same constitution. State at relaunch: main @
66d62eac (T3 lattice + clever-tricks doctrine); this branch synced;
wave first-pass at ~batch 663/712 (531/757 done, 97 failure-file
lines awaiting the solo retry); p2 machine run ~18h in with the
go-side stage durably recorded. [AGENT] resume plan: (1) wave
first-pass → retry pass → composition → CompletionWitness; (2)
A4-U5 dispatched NOW: the ALLOCATION-SYMBOLIC refactor (the
clever-tricks watch-list's top classic-ward item — handler equations
re-based on the kit's separation-logic framing, replacing the
address-concrete fixtures) + the seam design restated in
forward-simulation vocabulary with lineage lines; (3) then the
message-handler waves on the symbolic pattern.

**[USER] addendum (2026-08-24), the Iris sharpening of
clever-tricks:** much of the needed machinery is embodied in
iris-lean or built by other Iris projects (the ported lit review +
papers). Therefore: (1) USE that machinery where it exists; (2) build
Iris-COMPATIBLE machinery where it's missing; (3) reuse ideas freely
where they solve our problem; (4) NOTICE where our custom solutions
converge on Iris ideas and map them into reusable proof infra.
Innovation stays permitted — the rule is against duplication where
reuse exists. **[AGENT] adoption:** (a) the A4-U5 frame-refactor
directive extended: prefer iris-lean's own frame/ghost forms over
kit-local reinventions, log convergences; (b) an IRIS REUSE SURVEY
dispatched (Opus, read-only): map the campaign's custom machinery
(TableExt transport, FastEval γ-simulation, the seam's layer C,
checker-implication shapes) against iris-lean + the ported lit review
— naming duplications, Iris-compatible re-basings, and honest
no-Iris-analog items; feeds the standing iris-lean refresh backlog
(pin update pre-approved [USER] 2026-08-20, match-not-latest).

- **Arc 4, A4-U5 — LANDED** @ f4d0a10e: **THE ALLOCATION-SYMBOLIC
  REFACTOR, GO** — becomePreCandidate re-proved at ANY injective
  placement + disjoint frame (one FrameSim premise), with the shipped
  concrete theorem RE-DERIVED AS A COROLLARY at the identity seed
  (strict generalization machine-checked); projection
  rename-invariance one-time; witness discharges everything. Cost
  DOWN (28s vs 110s); zero Sym/Frame edits (fifth time); composition
  via the kit's stepFnIter_sim at machine level. Iris-ladder answer
  honest: rung 3 (Yang-O'Hearn operational locality) — iris-lean's
  wp_frame binds to an IProp Language instance GoCore lacks, and
  exact-fuel equations need credit-style bookkeeping; the FrameSim ≈
  big-sep convergence recorded for the reuse survey. Key strategic
  ground: layer (C) NEEDS the relocation quantifier anyway (leaf
  fixtures vs the twin's real base-389 layout). [USER] left the
  campaign to run autonomously (2026-08-24, "Have fun"). A4-U6
  dispatched: re-base the remaining four equations + the
  frameSim_relocate promotion.

- **The Iris reuse survey — LANDED** @ d97d9f40
  (docs/2026-08-24_campaign-iris-reuse-map.md): the strategic
  finding — the campaign's zero-Iris proof wing is DELIBERATE AND
  CORRECT for a sequential seam (Iris's leverage is
  concurrency-mediated resource sharing; the bridge back is proved,
  so rebasing is a cost question never feasibility). Verdicts:
  Sym/TableExt NO-ANALOG-import (perennial's two attempts are dead
  code missing exactly our soundness theorem); FastEval no-analog
  for the role; layer C REBASE-COMPATIBLE post-T1 (the
  dsp_ghost_theory pattern, flips high-priority under real
  concurrency); handler equations = the wp-implies-spec-step idiom
  with our exact-step form STRONGER (R14: TotalWeakestPre); frame
  layer correctly UPSTREAM of Iris. Highest-value actionable:
  **Perennial's Access-lens field pattern for the layout-shape gap**
  — routed to the wave-2 charter (U6 worker briefed). XS items done
  by coordinator: seam design §4c forward-simulation restatement +
  lineage lines + the Frame-name disambiguation note. Honest limits
  recorded (shallow perennial clone; no local RefinedC/Diaframe).

- **Arc 4, A4-U6 — LANDED** @ b1135520: all four remaining handler
  equations re-based allocation-symbolic (AllocEqWave1.lean, 536
  lines/20s; shipped modules UNTOUCHED — identity corollaries
  statement-identical; zero-edits held a SIXTH time) +
  frameSim_relocate taken (Frame/Relocate.lean, additive, lineage +
  the Frame-name disambiguation). **THE U6 FINDING (probe-decisive):
  the 0-based fixtures collide with the static locLit range
  (funcListSup=31) — bodies_inv + Agrees provably FORCE r=identity
  there, so no FrameSim could carry U1-U5's fixtures to the twin's
  real base-389 layout; the U5 layer-C bridge did not go through as
  claimed.** Fix demonstrated, not asserted: BPC re-sited +31 above
  the static range, the LIVE _alloc31 equation, and a witness with
  the raft cell genuinely moved (31↦32). Wave-2 charter binding:
  symbolic-from-birth, fixtures born re-sited (0-based re-siting
  owed at a consolidation slice before layer-C consumption),
  absState extension lens-shaped from birth (Perennial Access
  lineage). 488 jobs green; gate PASS.

- **Arc 4, A4-U7 — LANDED** @ c649061b (docs-only): THE LENS DESIGN
  SLICE (docs/2026-08-24_campaign-arc4-lens-design.md) — Perennial
  Access lineage read at primary source; simp-set-searched law
  instances (search-failure preserves the footprint-error property;
  typeclasses rejected with the reason); L1-L4 law families with L2
  (store-miss framing) named as the cost center and kill-point;
  generated instances costed (instrument, not proof code); absState
  v2 lens-consuming from birth so placement transport is free by
  construction. Contact-probed: raftLog.unstable embedded-value hop;
  raftpb.Message = 14 fields with a RECURSIVE Responses slice
  (GAP-V2-1, designated-if-unread). Deliverables 2-3 split forward
  honestly under the stop rule. [AGENT]: worker rotated (~910k);
  5th-gen dispatched on the lens build (slices A-D) + the fixture
  re-siting. Wave retry pass grinding (~S0077, solo ~6-10 min/seg,
  ~180 remaining ≈ up to a day).

- **Arc 4, A4-U8 — LANDED** @ 4880a22b: THE LENS BUILD COMPLETE
  (slices A-D) — **L2's named kill-point did NOT fire**
  (normalizeFieldsWith_lookup proves normalization field-pointwise →
  store-miss general across all field shapes); the instance
  GENERATOR DISSOLVED by the fdsOf projection trick (every instance
  a one-line kernel fact re-checked per build — generated-trust,
  zero instrument code, [AGENT] call of the unit); absState v2
  (absRaftLog closes GAP-V1-1b; absMessage; absOutbox) lens-consuming
  from birth, transports BY COMPOSITION; GAP-V2-1 resolved by read
  census (Responses deliberately unprojected). **AND the fixture
  re-siting CLOSED**: all five handler families re-sited above the
  static range, probe-validated placement-transparent, the Bf
  flagship's NON-IDENTITY witness at the real layout (cell at base
  32 via frameSim_relocate, no re-evaluation). 496 jobs green; gate
  PASS; 7 new pins. Every handler family is now
  layer-(C)-consumable. Promotion note: stepFn_pick_transport lift
  awaits a coordinator-authorized Sym touch (the U6 Relocate
  precedent). A4-U9 dispatched: handleHeartbeat — THE FIRST MESSAGE
  HANDLER, symbolic-from-birth on the full new machinery.

- **Arc 4, A4-U9 — LANDED** @ 55be64c6 (clean-boundary stop):
  handleHeartbeat's probe census — **appendSpill answered AGAINST
  expectation** (1,325 steps, exactly ONE choice: `r.msgs = append`
  fires the spill choice even on the NIL outbox — the transport is
  required, not deferrable; now triply motivated); the footprint
  field census; commitTo's two branches mapped (no-op branch this
  fixture; commit-advance = second family); **absState v2 exact
  end-to-end on its first real handler contact** (the post-state
  MsgHeartbeatResp record exact); the fixture recipe born re-sited.
  The authorized stepFn_pick_transport lift taken
  (Sym/PickTransport.lean, additive, pinned; 497 jobs green).
  [AGENT]: 6th-gen rotation (~1.02M); A4-U10 dispatched = the
  appendSpill transport + THE handleHeartbeat equation with the lens
  payoff measured.

- **[USER] 2026-08-24 — giant-builds-as-smell guidance:** Mike flags
  that giant builds over huge terms (the witness wave) are a mildly
  suspicious signal of a missing abstraction — e.g. a 'verified
  verifier' layer doing symbolic execution over such terms with a
  simpler cert plus a once-proved convergence theorem. [AGENT]
  response, logged: the wave already HAS the verified-verifier layer
  (FastEval = certified computation; the wave = certificate replay),
  but the CERT IS AT THE WRONG GRANULARITY — it re-materializes full
  heap-state literals per checkpoint; the 712-segmentation is memory
  scaffolding, a tolerated scaffold per the clever-tricks doctrine,
  now carrying an EXPLICIT RETIREMENT CONDITION: when Arc 4's round
  induction (layer C) lands, prove a ROUND-REPLAY COROLLARY — the
  ∃-witness as ~100 applications of the round lemma at the recorded
  choice stream (cert = choices, granularity = rounds) — and DELETE
  the segment wave rather than maintain two mechanisms. [AGENT]: the
  in-flight wave runs to completion (T1's ∃-side does not idle weeks
  on layer C); delta-encoded checkpoints NOT built (fallback only,
  recorded, if the retirement path slips). Same smell noted at the
  goldenWire% 9.3 MB literal pin — tolerated generated-literal
  scaffold, retirement only via a principled pin route (SpecTec).

- **[USER] 2026-08-24 — witness wave PARKED:** Mike: 21 h of
  remaining retry grind is too long to block on if it's not providing
  value. Wave stopped same-hour; 549/712 segment oleans kept, resume
  reversible (arc-2 log, park entry). Consequence, [AGENT]-executed:
  the RETIREMENT PATH IS PROMOTED TO PRIMARY — CompletionWitness will
  be proved as the Arc-4 round-replay corollary (cert = the recorded
  choice stream, granularity = rounds), not by segment replay. The
  ∃-side now DEPENDS ON layer C; sequencing unchanged (layer C was
  already on the critical path for the ∀-side). Calibration note for
  P-2026-08-24: this removes ~21 h of grind and one interim artifact,
  adds no new proof obligation that layer C did not already carry.

- **[USER] 2026-08-24 — THE ONE-HOUR DOCTRINE:** prioritize methods
  that SCALE; never grind out results. Anything taking more than ~1 h
  to build is a candidate for killing — such a runtime demands
  extraordinary justification; it can be worthy, but it is inherently
  suspicious and THE BIAS IS AGAINST IT. Campaign-operational from
  this entry forward; goes into every worker brief. Candidate
  CLAUDE.md amendment queued for user sign-off (main edit).
  Applications, [AGENT]-executed under the doctrine:
  - The witness wave: already parked (previous entry) — the doctrine
    retroactively confirms the park.
  - **p2 KILLED** (~21 h into an opaque machine stage): no progress
    signal, no checkpoints, remainder unboundable, fuel 40e9 a guess.
    This SUPERSEDES the earlier [USER] "don't kill the long-running
    shell" (which was scoped to the pause discussion); supersession
    flagged to the user for reversal. Sunk: the machine stage (go-side
    record durable, reused on any resume). Replacement plan (follow-up
    task, doctrine-shaped): right-size fuel FROM the go-side record's
    step count, add progress emission + periodic machine-state
    checkpoints to the replay path, run as bounded chunks — the
    fidelity evidence per hour goes UP under this shape.
  - Forward rule for arc units: proof mechanisms are designed so no
    single build exceeds ~1 h; a unit that finds itself needing one
    STOPS and redesigns (that is a clean boundary, not a failure).

- **[USER] 2026-08-24 — doctrine CLARIFIED:** the ban on grinding is
  NOT a ban on long build-out — it is a ban on "dumbly throwing a
  bazillion terms at the kernel." Long campaigns of many small,
  well-abstracted units are fine; brute kernel reduction of giant
  terms as a SUBSTITUTE for abstraction is what is banned ("pointless
  and stupid"). The ~1 h line is the smell threshold for that failure
  mode, not a schedule constraint on total work.
- **[USER] 2026-08-24 — p2 kill confirmed; roadmap reassessed under
  the grinding ban.** User's framing, recorded: "your main skill is
  iteration. Such campaigns are poison to iteration" — long grinds
  lock the box, defer feedback, and hide failure until the end.
  [AGENT] reassessment of everything remaining to T1+T2:
  - **Arc 4 layer B (per-handler equations): PASSES** — the Sym-driven
    loop is probe → equation → minutes-scale build → next; per-unit
    full-proofs builds are minutes (U8: 496 jobs). Watch item: a big
    handler whose single kernel_rfl approaches the hour mark triggers
    the forward rule (stop, decompose into lemma-level composition).
  - **Layer C (round induction, checker-implication, T1 assembly):
    PASSES** — proof-shaped, small builds.
  - **CompletionWitness via round-replay corollary: PASSES** — the
    grind route (segment wave) is parked; cert-replay at round
    granularity is kernel-cheap.
  - **T2: PASSES** — statement generalization + lattice reuse.
  - **Dead grinds:** the wave (parked) and p2 (killed) were the only
    two >1 h jobs; nothing else on the roadmap is grind-shaped. The
    gate (~minutes) and judge (393 s) are within doctrine.
  - **Queued small task (not critical-path):** p2's replacement —
    instrument the replay path (progress emission, periodic machine
    checkpoints, fuel right-sized from the go-side record), run as
    bounded chunks. Fidelity evidence per hour goes up; scheduled
    after the current arc-4 units, own small branch.
  - **Calibration:** P-2026-08-24 (~4-7 weeks) unchanged, if anything
    improved — no day-scale waits remain on the critical path.

- **[USER] 2026-08-24 — p2 → verified-verifier pattern:** "It
  shouldn't take 30 hours to replay something in Lean. Build a more
  performant abstraction then prove the theorem." [AGENT]: unit
  **P2R** chartered on the arc-2 lane (charter text in
  campaign-arc2-log): measure first (true step count from the go-side
  record, never guessed fuel) → extend FastEval arm-coverage to the
  replay path → transfer theorem via the γ-simulation composition →
  wire the verified fast engine into tracereplay's machine stage with
  progress + checkpoints → acceptance: minutes-scale replay, ≤1 h
  ceiling. Worker dispatched to campaign-arc2 (lane writer handed
  over). Escape clause: if even the fast engine misses the ceiling,
  stop with numbers — next rung (batched/big-step replay converging
  with arc-4's equation layer) is a design decision.

- **[USER] 2026-08-24 — THE GENERAL FORM (insight doctrine):** "your
  main resource is iteration, and work should generate insight.
  'Generalized grind' is work without insight." This subsumes the
  kernel-grinding ban: the test is not build time but INSIGHT PER
  ITERATION, and it applies to every work-shape — proofs, agent
  units, measurement, audits. [AGENT] operational reading, in force:
  - Every unit log entry carries an explicit WHAT-THIS-TAUGHT-US
    line; a unit that can't fill it honestly was grind.
  - Two consecutive insight-free units on a track = stop and redesign
    the track, even if the units are "succeeding."
  - Retrospective, owned: the witness wave stopped generating insight
    after its first few segments validated the composition — segments
    ~4..712 were generalized grind, and the redesign signal was
    available WEEKS before the [USER] park. The probe-first
    convention exists precisely because probes are the highest
    insight-per-iteration work-shape; this doctrine makes that the
    universal test, not just a proof-unit habit.
  - Goes into every worker brief alongside the anti-grinding rule.

- **[USER] 2026-08-24 — cost-model calibration on the waste
  accounting:** box compute waste is FINE (cheap resource); worker
  attention is THE scarce resource, and its waste (~10% of units)
  "seems minimized." Forward: [AGENT] applies the insight test to
  ATTENTION allocation first — compute may be spent speculatively;
  iterations may not. Campaign proceeds: U10 (handleHeartbeat
  equation) and P2R (verified fast replay) in flight in parallel.

- **Arc 4, A4-U10 — LANDED** @ 91b7dc04, gate PASS (22 ok), 500
  jobs green: THE APPEND-SPILL TRANSPORT (SpillTransport.lean,
  lineage-lined, pinned, witnessed) + **THE FIRST MESSAGE-HANDLER
  EQUATION** — handleHeartbeat, symbolic-from-birth, two windows
  [1299,25] + one spill crossing (U9's census exact), the choice
  absorbed into valuation atoms so ONE literal serves all 32
  capacities; nine absState-v2 conclusions incl. absOutbox =
  [specHeartbeatResp]. **THE MEASURE: ~70× (41 s vs ~49 min
  projected per-conjunct baseline)** — the lens design's payoff
  formula met. WHAT THIS TAUGHT US: (1) the cell-atom mechanism
  collapses choice-dependence exactly as designed (zero per-choice
  splits); (2) From-symbolism is blocked by the subject's
  self-addressed panic guard — real side condition m.From ≠ r.id
  recorded; (3) L2 store-miss was NOT needed on this handler (spill
  targets a temp cell) — the lens's L2 case awaits a field-writing
  handler; (4) handleAppendEntries census: 2,828 steps/one choice,
  mirror runs clean — ITS EQUATION IS PURE ASSEMBLY. Comparator
  landmark STALE at 112 commits — [USER]-queue: judge owed at this
  branch's merge. [AGENT]: U11 dispatched to the same worker
  (~500k, assembly-shaped unit): the handleAppendEntries equation
  (success/empty family) + stale family; third slot = the
  NON-EMPTY-ENTRIES LOG-APPEND family over becomeLeader (insight
  test: it probes GAP-V1-1b's unstable overlay — the open risk —
  while becomeLeader is settled machinery).

- **Arc 2, unit P2R — LANDED** @ 4701915d, gate PASS: the verified
  fast replay engine. **True step count 11,995,825 (exact); slow
  engine wall ≈ F^2.5 — p2's >20 h DNF fully explained; fast engine:
  full replay 26.6 s, trace == go trace BYTE-FOR-BYTE (20,924 B),
  74/74 blocks, MACHINE 1/1 AGREE.** Transfer theorems pinned
  (fastRun_transfer + _eqb + non-vacuity witness; classical trio, no
  new axiom). WHAT THIS TAUGHT US (the unit's core discovery): the
  "lazy γF view" was kernel-lazy but COMPILED-STRICT — every pure-
  helper call materialized an O(cells) heap dump, giving the fast
  engine slow asymptotics when compiled; fixed by ctxF (O(1) context
  image) + a types-only Congr library, ~45 sites; `implemented_by`
  REJECTED as a fail-open trust hole. The 20 h grind was not just
  slow — its opacity was HIDING an asymptotic defect the 26 s
  instrument found in one iteration. Consequences recorded: the ctx
  refactor INVALIDATES the parked wave's 549 oleans (round-replay
  route unaffected — the park's sunk value drops to ~zero, consistent
  with its scheduled deletion); the parked untracked TwinSegs tree
  moved (not deleted) to artifacts/p2r-parked-wave/. Comparator
  landmark now owed by BOTH lanes at merge ([USER] queue). [AGENT]:
  P2R-2 dispatched to the same worker — the full deps/raft/testdata
  machine-tier differential sweep on the fast engine (hour-scale
  now), stubs surfacing as enumerable fail-closed arms.

- **Arc 2, unit P2R-2 — LANDED** @ 76361232, gate PASS: the
  full-corpus fast machine-tier sweep. **27/27 traces AGREE
  byte-for-byte with go run across the entire deps/raft/testdata
  corpus** (558 blocks, 354 supported-prefix; 37.7M fast steps in
  237 s, peak 216 MB); zero divergences; the 8 first-sweep failures
  were ONE fail-closed arm (mapDelete), closed with the U-discipline
  + a types-only cont delegation; verdicts transfer by the pinned
  fastRun_transfer_eqb. WHAT THIS TAUGHT US: (1) zero divergences IS
  the finding — the whole upstream corpus replays byte-identically
  on the model; (2) fail-closed classification worked exactly as
  designed (8 failures → 1 enumerable arm, no silent laundering);
  (3) the next perf constant lives in value representation (30×
  per-trace rate variance recorded, not chased — no ceiling
  threatened). [AGENT] ALLOCATION CALL: the arc-2 lane PARKS at this
  clean boundary — its two proposed follow-ons (replay-vocabulary
  frontier; value-rep measurement) are insight-positive but OFF the
  T1 critical path, and attention is the scarce resource ([USER]
  calibration): all worker attention now goes to the arc-4 seam.
  Both queued in the arc-2 log for post-T1. [USER] queue: the
  campaign-arc2 branch (P2R + P2R-2) is a coherent, gate-green,
  branch-complete segment — AUDIT ASK POSED for its landing on main
  (see the operator report), comparator-judge owed at that step.

- **[USER] 2026-08-24 — audit APPROVED as proposed** for the
  campaign-arc2 landing (P2R+P2R-2 delta): 3 Opus reviewers
  (semantics/correspondence mandatory; claim-strength/vacuity;
  gate-honesty) + verification passes + comparator-judge run.
  [AGENT]: judge launched (capped, background) from the arc-2
  worktree @ 76361232; audit workflow launched same-hour.
  Coordinator reclaims arc-2 lane writership (worker retired at the
  park). Merge sign-off remains a separate [USER] moment.

- **comparator-judge PASS at the arc-2 tip** (2026-08-24): 56
  theorems kernel-certified, 815 s, fresh clone @ 76361232; landmark
  marker committed on the branch @ 48e35a5b. First attempt failed
  CLOSED on the worktree's missing deps/comparator (as designed);
  deps seeded offline from the primary checkout (the sanctioned
  --from pattern; the judge verifies pin fd2e25de + pristine state
  itself). The parked-wave dirty manifest files remain untouched as
  found. The staleness debt both lanes flagged is now cleared for
  arc-2; arc-4 still owes a judge run at ITS merge. Delta-audit
  workflow still in flight.

- **P2R delta-audit RETURNED** (2026-08-24; 24 agents, 3 Opus
  reviewers + default-refute verification; 20 findings → 13
  CONFIRMED, 4 DOWNGRADED-but-real, 3 REFUTED). The two substantive
  survivors, both TRUST-SURFACE CLAIM defects (no reachable wrong
  answer — stepFast fail-closes every divergence construct — but the
  records overstate): (1) HIGH→MEDIUM: the transfer theorem certifies
  runProgramM (SEQUENTIAL entry) while the replaced slow engine
  computed runProgramPoolIntsM (POOL entry) — no bridge lemma, the
  "trust class IDENTICAL" docstring and tracereplay comment literally
  false, the semantics swap unrecorded; (2) MEDIUM→LOW: premise 3 of
  fastRun_transfer_eqb is never evaluated by the driver (runLoop ≠
  iterF, no connecting lemma) — "every premise was checked" literally
  false. Confirmed MEDIUMs: the landmark-OWED note misattribution
  (real trigger = proofs/lakefile.toml's new fastreplay exe, NOT
  Audit/FastEval.lean); a self-contradictory slice-1 extrapolation.
  Plus 8 confirmed LOW record corrections. WHAT THIS TAUGHT US: the
  audit dimension that fires is always claims-vs-artifacts — the
  proofs were sound, the PROSE around them drifted; and the reviewers
  caught a watched-set subtlety (lakefile in the judge's trust
  statement) that the lane worker glossed. [AGENT]: fix-round worker
  dispatched on campaign-arc2 (F1 claim corrections + bridge-argument
  record + queued bridge lemma; F2 premise-3 honest check; F3-F5
  record corrections); delta-review of the fix diff to follow (it
  touches trust-surface claims — user policy 2026-08-01).

- **P2R audit fix round LANDED** @ 352b1276, gate PASS (2026-08-25):
  F1 claim corrections + the entry-point-swap [AGENT] record + queued
  runProgram_pool_seq_bridge lemma (judged not-small, correctly not
  attempted); **F2 by direct re-evaluation — the driver now evaluates
  the theorem's literal premise-3 expression and feeds ITS result
  state to premise 4, demoting the discovery loop to untrusted
  machinery** (26.6 s → 44.3 s, ~80× under ceiling); F3-F5 record
  corrections all applied with re-derived numbers. The worker closed
  an honesty gap the fix order missed: the 27/27 record predated the
  driver change, so it RE-SWEPT the corpus under the fixed driver —
  27/27 AGREE, steps identical, premise3-ok in all records (388.7 s).
  WHAT THIS TAUGHT US: the right fix for a claims-vs-machinery gap is
  usually to move the MACHINERY under the claim (evaluate the premise
  itself) rather than weaken the claim to fit. Delta-review of the
  fix diff dispatched (trust-surface touch, user policy 2026-08-01).

- **Fix-round delta-review RETURNED** (2026-08-25): the F2 premise-3
  mechanism SURVIVED all attack dimensions (verbatim premise match;
  fail-closed both directions; the untrusted loop cannot flip a
  verdict); all re-derived numbers reproduce. Six findings, one
  substantive: **F-A (MEDIUM) — "no bridge lemma exists" is FALSE as
  stated**: the loop-level pool↔sequential conservation
  execProgLoop_single ALREADY EXISTS Audit-pinned, and the entry
  bridge is likely ~5 lines of glue mirroring fastRun_transfer's own
  proof — the fix round's "NOT small" deferral judgment was wrong.
  Also F-C: the recorded stub enumeration was incomplete (mutex ops
  ARE supported, not stubbed) — the operative bridge argument is "no
  spawn ⇒ singleton pool ⇒ conservation via transferable", exactly
  what the existing lemma formalizes. WHAT THIS TAUGHT US: the
  reviewer knew the repo's own theorem inventory better than the
  fix-round worker — deferral-effort judgments need a search of
  existing correspondence lemmas, not just a look at the gap. [AGENT]:
  round 2 dispatched to the same worker — attempt the entry bridge
  TIMEBOXED (pin it and upgrade the claims if it typechecks; record
  the obstruction and correct claims if not), plus the 4 mechanical
  corrections (stale 27 s; 1.76× like-for-like; premise3-ok record
  citation; step-index docstring).

- **Fix round 2 LANDED @ 7ae40db7 — THE BRIDGE IS PROVED** (2026-08-25):
  `fastRun_transfer_pool(+_eqb)` and `runProgram_pool_seq_bridge(+_eqb)`
  typechecked on the reviewer's sketch at first attempt, all four
  Audit-pinned [propext, Classical.choice, Quot.sound]; the fast
  engine's ok verdict now certifies BOTH whole-program entries BY
  THEOREM (the audit's HIGH-class concern fully retired, not
  documented); claim sites rewritten to lead with the conservation
  argument; mechanical corrections (stale 27 s, 1.76×, premise3-ok
  citation, step-index in error paths) all in; gate PASS. Coordinator
  spot-check of the pinned statements: premises are exactly the
  driver's five evaluated checks — no quantifier slack. [AGENT]
  merge-prep executed per protocol's refusal path: park-state manifest
  files committed (the flagged operator obligation), snapshot ref
  taken, campaign-arc2 REBASED onto main @ 66d62eac (one conflict —
  dual landmark markers, resolved chronologically), tip 5d6395df;
  re-gate running, judge re-run at the rebased tip to follow, then
  the merge ask.

- **ARC-2 MERGE PACKAGE COMPLETE** (2026-08-25): campaign-arc2 @
  118d31aa — rebased onto main (66d62eac), gate PASS at the rebased
  tip, **comparator-judge PASS at the rebased tip (56 theorems,
  742 s, fresh clone @ 5d6395df)**, landmark committed, tree clean.
  Full audit trail: delta-audit (24 agents) → fix round 1 → Opus
  delta-review → fix round 2 (bridge PROVED) → coordinator
  spot-check. MERGE SIGN-OFF ASK POSED to the user; merge is exactly
  `git checkout main && git merge --ff-only campaign-arc2` on
  approval, given at that moment. Nothing merged until then.

- **[USER] 2026-08-25 — MERGE APPROVED AND EXECUTED**: "go ahead and
  merge as proposed". main fast-forwarded to 118d31aa (the arc-2
  package: verified fast replay engine + pool/sequential bridge
  theorems + corpus differential record + tracereplay fast engine +
  park state + audit corrections). ff-only, tree clean, primary
  checkout back parked on main. Push NOT executed (separate
  sign-off, unrequested). The arc-4 lane now owes a rebase onto the
  new main at its own merge step; its U11 work is unaffected
  meanwhile (disjoint trees).

- **P-2026-08-25 (calibration revision, [USER]-prompted challenge,
  [AGENT] numbers):** P-2026-08-24's ~4-7 weeks to T1+T2 is revised
  to **~2.5-4 weeks (T1 in ~1.5-2)**. Basis: the original predated
  the anti-grinding doctrine, the verified fast engine, and the
  measured ~70× lens payoff; layer B's marginal handler cost has
  collapsed (handleHeartbeat = half a unit; handleAppendEntries
  censused as assembly). Variance now concentrates in layer C's
  first contact (the U1 precedent: pilots refute cost models) and
  the hard handler tail. Named accelerator, decision at U11's
  boundary: a parallel lane for the checker-implication lemmas
  (lattice on main + stable absState interface, file-disjoint from
  handler equations). Original prediction retained beside this one.

- **[USER] 2026-08-25 — the hard tail as FURTHER CONSUMERS:** the
  difficult customers ahead (the hard handlers, layer C) are treated
  as further consumers of the machinery — classics first, innovate
  only if need be; "we aren't anywhere near where we run out of road
  doing clever tricks to scale more." [AGENT] operational reading,
  into every brief from U11 on:
  - When a hard customer resists, the FIRST move is a machinery
    extension in the established general patterns (a new TableExt
    arm, a transport, a lens law — Go-general, lineage-lined,
    witnessed), NEVER a handler-specific workaround. The U3
    consume-on-demand process is the template.
  - Layer C consumes the classics by construction: simulation
    induction over the landed equations; checker-implication as
    property transfer through the refinement mapping. Any genuinely
    new mechanism there gets its lineage line and extra scrutiny.
  - The named risk window: T1-assembly milestone pressure is when
    bespoke hacks look cheapest — that is the over-specialization
    audit dimension's home ground; the closing audits weight it
    accordingly.
  - Scaling pressure ⇒ the next classic (IR, certificate replay,
    reflection), never grind and never wilderness without a named
    reason.

- **Arc 4, A4-U11 — LANDED** @ eeceef6f, gate PASS, 502 jobs: THE
  handleAppendEntries EQUATION (success/empty family; the spill
  transport's SECOND consumer exactly as censused; ten absState-v2
  conclusions incl. the msgsAfterAppend routing; 66 s module) +
  span_relocate (sim plumbing packaged once, promotion row) + two
  censuses. WHAT THIS TAUGHT US: (1) THE RISK FINDING — log-append
  goes stuck at static cell 25: the blocker is the STATIC-CELL
  COMPLEMENT ([20,31) from $pkginit — the ErrCompacted-family error
  vars the leaf fixtures don't carry), NOT GAP-V1-1b's overlay,
  which was never reached; same debt blocks U4's Ms error branches —
  one shared fixture block retires it for every error-path consumer
  (the further-consumers doctrine's exact shape). (2) THE
  ELABORATOR-MISMATCH PATHOLOGY: a single stale numeric arg in a sim
  application sent Lean into 37 min/14.5 GB of WHNF spine-unfolding
  instead of a unification error — convention: on any hang, check
  numeric args of sim/window applications FIRST; span_relocate
  shares n by construction so the class can't recur. (3) stale
  family = pure assembly (fixture values distinct so records differ
  observably). [AGENT]: honest boundary call endorsed (solid 1 +
  censuses over a rushed 2); 7th-gen rotation at ~750k; U12
  dispatched = stale equation + THE static-cell complement as shared
  machinery + third slot by censused cost.

- **Arc 4, A4-U12 — LANDED** @ 96723532, gate PASS, 507 jobs: the
  span_relocate lift (promotion row taken) + THE STALE-FAMILY
  EQUATION + **THE STATIC-CELL COMPLEMENT as shared machinery**
  (payloads at $pkginit's true addresses, zero renaming; trust via
  staticComplement_link kernel-replaying the 1,382-step init against
  the pin every build) + **THE LOG-APPEND EQUATION** — landed same
  unit, not just censused. THE SEAM VERDICT, plainly: **GAP-V1-1b's
  overlay does NOT bite at the projection layer** — absRaftLog
  projects the grown overlay exactly on first exercise; what bit
  instead was an atom-absorption assumption on the in-window
  re-read of the spilled handle, discharged with ZERO new machinery
  (choice-independence via existing lemmas). handleAppendEntries now
  has THREE proved families — every branch but REJECT. WHAT THIS
  TAUGHT US: (1) the overlay risk retires at projection granularity;
  the residual watch-item is a cap-consuming re-read BETWEEN spills
  (would not be choice-independent — becomeLeader's census must
  check); (2) the further-consumers pattern held under pressure —
  the complement shipped general (link-pinned) and the overlay
  surprise was absorbed by existing lemmas, no bespoke anything.
  Equation ledger: 5 handler families proved (bF pilot, Hh no-op,
  Hae success/stale/log-append). [AGENT]: U13 dispatched to the same
  worker (~403k): becomeLeader census-first (the watch-item is the
  point), Hh commit-advance, third slot by censused cost. Landmark
  staleness 120 commits — stands for the arc-4 merge step.

- **Arc 4, A4-U13 — LANDED** @ b143c56d, gate PASS, 512 jobs: THE
  becomeLeader CENSUS + EQUATION (the largest chain yet — 10
  windows/9 crossings/6 choices, green on the FIRST full check at
  190 s; three Go-general TableExt arms consumed on demand en route)
  + THE handleHeartbeat COMMIT-ADVANCE EQUATION (that handler now
  COMPLETE) + THE Ms ERROR-BRANCH EQUATIONS (the static-cell
  complement's second consumer — generality validated by its design
  test: append-only composition on a disjoint path). WHAT THIS
  TAUGHT US: (1) the census verdict, plainly — NO cap-consuming
  re-read exists on the becomeLeader path; the watch-item is RETIRED
  for len-shaped reads (two clean instances) and stays open per
  census for cap-consuming ones (no instance yet); (2) the largest
  chain landing first-check green at 190 s says the machinery has
  reached its scaling regime — the marginal equation is now
  assembly even at 10-window size; (3) the numeric-mismatch
  pathology recurred once and the U11 convention caught it in ONE
  probe run (printer improvement noted). Equation ledger: **13
  families; every censused wave-2 family proved except Hae REJECT.**
  [AGENT]: U14 to a FRESH 8th-gen worker (U13's at ~667k): REJECT
  census-first (split at loop boundaries — largest window risk),
  the m.From ≠ r.id branch-crossing transport, then wave-3 dispatch
  censuses. Landmark staleness 126 commits — stands for the arc-4
  merge step.

- **Arc 4, A4-U14 — LANDED** @ 24458fdd, gate PASS, 517 jobs:
  **handleAppendEntries CLOSED — the first fully-complete message
  handler** (REJECT family: 6,951 steps, largest window yet, the
  anti-grinding contingency checked by measurement and NOT triggered
  — 107 s, first-check green) + `stepFn_branch_transport`
  (path-condition splitting, King 1976 lineage; the transport
  family's third member) demonstrated by the From-symbolic Hh
  equation (dst proved for EVERY non-self-addressed sender — the U10
  residual closed) + **THE DISPATCH COMPOSITION MAP** (probe-only):
  sF/sC arms consume the landed equations exactly as layer C needs;
  sC×MsgHeartbeat measured as the first two-equation composition
  (4,969 steps = bf spine + Hh span + glue). WHAT THIS TAUGHT US:
  (1) the drop arms stick at static cells 16/17 (ErrProposalDropped)
  — OUTSIDE the U12 complement's [20,31): the dispatch-layer
  complement extension is a named debt with a verbatim recipe;
  (2) wave-2 pricing held to the end — the largest window was still
  assembly; (3) the U13 printer improvement makes the
  numeric-mismatch class unrepresentable in new generators.
  Equation ledger: **15 families + the first From-symbolic form.**
  [AGENT]: U15 to a fresh 9th-gen worker (dispatch complement
  extension → first dispatch-arm equations, sF then the sC
  composition arm); COORDINATOR OPENS THE LAYER-C DESIGN in
  parallel (the composition map is its input; note drafted on the
  campaign worktree, to be contact-tested by the layer-C unit per
  the U1 lesson). Landmark staleness 130 — stands for the merge
  step.

- **Arc 4, A4-U15 — LANDED** @ d6f0286e, gate PASS, 520 jobs: the
  dispatch-complement extension (cells 16/17 + payloads, kernel-
  linked; drop arm completes, fail-closed control verified) + THE
  FIRST DISPATCH-ARM EQUATION (sF×MsgHeartbeat, eleven conclusions)
  + **THE COMPOSITION-MECHANICS VERDICT** — the layer-C design's A1
  contact test: statement forms COMPOSE (all dimensions measured
  clean; window links continuation-bottom parametric); the wall is
  the INSTRUMENT (FrameSim is lossy — no heap-completeness — so a
  relational sub-span cannot hand back a literal window; three
  repair routes named). WHAT THIS TAUGHT US: the pilot lesson
  repeats one level down — designs survive contact at the statement
  layer and get refuted in the instrument layer; U15 stopped at the
  measured wall instead of forcing a fake composition (the boundary
  rule working). [AGENT] ROUTE POLICY (folded into the layer-C note
  §5-A1): wave 3 + round lemmas proceed on literal bounded chains
  (round spans are fixed code; the induction composes lemmas at
  absState level — no mid-walk resume needed); the FrameSim
  completeness strengthening (Yang-O'Hearn lineage) commissioned as
  a probe-first slice with a measured ≤2-unit go/no-go. Ledger: 16
  families + first dispatch arm. U16 to the same worker (~340k):
  the design slice per the route policy, sC×MsgHeartbeat as a
  walked chain, the drop-arm equation, stepLeader census.

- **Arc 4, A4-U16 — LANDED** @ 5f731c17, gate PASS, 524 jobs, both
  new equations first-check green: the seam-note §4c design slice +
  the FrameSim probe (honest borderline-over verdict → STAY LITERAL;
  the C1-insufficiency finding — needs a second, insertion-point
  clause — reported against the worker's OWN earlier sketch) + the
  DROP-ARM equation (choice-free; the extension's first proved
  consumer) + **THE DEPTH-2 EQUATION sC×MsgHeartbeat — the round
  lemma's dress rehearsal: PURE ASSEMBLY, ~linear cost** + the
  stepLeader census (Beat completes 3,362/4 zero statics; Prop =
  the subject's own empty-Entries panic, non-empty fixture needed;
  leader-side fixture pack = named ledger row). WHAT THIS TAUGHT
  US: (1) the depth-2 verdict de-risks A2's outer ring — the round
  lemma is one more ring of a measured shape; (2) the R-FORM FLAG:
  the literal route's honest premise is fixture-family membership
  with absState as readout — folded into the layer-C note §2 as the
  binding C1 form (simulation over an inductive invariant, still
  the classic); (3) the go/no-go pattern produced an honest
  self-refutation (the probe found the worker's own route sketch
  insufficient). Ledger: 4 arm equations over 15 handler families.
  [AGENT]: U17 to a FRESH 10th-gen worker (U16's at ~560k):
  sL×Beat equation (closes the heartbeat arm triple across all
  three roles → C1 opens), the leader-side fixture pack, budget:
  Step() top-level census. Landmark staleness 139 — stands.

- **Arc 4, A4-U17 — LANDED** @ 5d3e70ae, gate PASS, 526 jobs:
  **THE HEARTBEAT ARM TRIPLE CLOSED** (sL×MsgBeat: census-exact to
  the step, four raft scalars symbolic, the first choice-VALUE side
  condition; sF/sC/sL = the complete arm set for the first round
  lemma) + the in-place append transport (the U12 atom-re-read
  watch-item FIRED and was closed as general machinery, stronger
  than the ledgered wrapper) + the leader-side fixture pack (ALL
  FOUR remaining leader arms census to STOP — Prop's first
  non-empty msgsAfterAppend; both pack pieces provably needed) +
  **THE Step() ROUTING MAP**: on every local default route the glue
  is a CONSTANT 453 steps / zero choices / role-independent, and
  each landed arm equation is consumed EXACTLY (pops offset +420) —
  verified arithmetically on four arms. Non-default routes mapped
  (term-bump, term-down ignore, nil-panic fail-closed, MsgHup
  10,709/12 = the campaign spine, C4 territory). WHAT THIS TAUGHT
  US: (1) the dispatch layer is as compositional as the design
  hoped — constant glue means the round lemma's outer ring is
  arithmetic, not discovery; (2) the watch-item lifecycle worked
  end-to-end (censused open → fired → closed as a transport);
  (3) anti-grinding fired once (a 28-min whnf divergence killed and
  bisected; lesson: unification-determining premises must be
  pre-stated haves). Ledger: 5 arm equations + 15 handler families;
  C1's inputs COMPLETE. [AGENT]: U18 = C1 dispatched to a fresh
  11th-gen worker — the layer-C design gate (driver-span census /
  R-form round-lemma statement witnessed on heartbeat / the A4
  adapter probe). Landmark staleness 144 — stands for the merge
  step.

- **Arc 4, A4-U18 = C1 — LANDED, THE DESIGN GATE FIRED** @ 3bbb0f10,
  gate PASS, 528 jobs: the driver-span census, the A4 adapter probe
  (mismatch theorems), the R-form statement + witness, absTwinRead
  v0. VERDICTS: A1 PASS + cost trigger FIRED (41 GB naive-replay
  wall measured; anti-grinding stopped the replay and shipped the
  measurement); A2 REFINE (checker fine; the balloons are the
  |net|-dependent driver glue, the un-equationed 9-14k-step harvest
  ring, and the 81k-step init seed); A3 PASS; **A4 KILL — the
  Verdi-lattice adapter has theorem-grounded mismatches on real
  etcd behavior** (commit-advance sans entries has no lattice
  image; election noop exits Verdi's reachable set). **CENSUS
  HEADLINE: the wave-3 heartbeat/Prop arms are UNREACHABLE in the
  twin — all four dispatch-arm equations are T1-vacuous** (machinery
  and validation value retained, honestly docstringed). WHAT THIS
  TAUGHT US: (1) the gate design worked — every refutation arrived
  pre-C2 with evidence anchors instead of mid-assembly; (2) the
  wave-3 mis-target is a process lesson now encoded: REACHABILITY
  IS PART OF THE CENSUS — arm/round units state reachability
  evidence before building (the composition map priced cost but
  nobody checked the driver's actual message vocabulary); (3) the
  U1 pattern at layer scale: designs survive at the statement layer
  and get refuted in instruments and reachability. [AGENT]
  DECISIONS (design note v2, §8): D1 the FrameSim completeness
  instrument COMMISSIONED (trigger fired; ≤3-unit stop); D2 the S1
  leaf goes NATIVE re-derivation over specRound with T3's structure
  as template (route (b); moots the package seam); D3 the arm
  ladder re-targets to the reachable set (votes/appends/storage/
  campaign/propose). Ladder replaced (C2a-C6). Calibration: T1
  moves toward the upper bound of ~2 weeks; the 2.5-4-week T1+T2
  window stands. C2a dispatched to the C1 worker.

- **[USER] 2026-08-26 — sequencing review prompted** ("Do we need to
  pull back and redesign? ... consider sequencing"). [AGENT]
  assessment + call: NO full pull-back (v2 absorbed C1's forced
  redesign; C2a is route-independent and bounded) but ONE real
  correction — the v2 ladder deferred the two scope unknowns whose
  answers could move the timeline by weeks: (1) the S2/S3 route
  question sits ON the A4 commit-axis mismatch and is NON-OPTIONAL
  for T1 (all three checks must never fire) — deferring its route
  decision "to their wave" was backwards; (2) D2's native-S1 sizing
  was asserted, not measured; plus the harvest-granularity question
  (choice-free storage sub-rounds may want one batched per-cycle
  lemma, not per-arm equations). EXECUTED: scoping lane
  campaign-arc4b opened (worktree off the arc-4 tip, NEW-FILES-ONLY
  discipline so it lands conflict-free at a wave boundary), worker
  SC1 dispatched on the three probes (S2/S3 checker census → needed
  invariants → mismatch-axis check → sized route skeleton; native-S1
  proof skeleton with PORTS/ADAPTS/NEW classification + calibrated
  cheap links; harvest-ring choice-freedom census + batched-vs-
  per-arm pricing). DECISION POINT: C2a's boundary — C2b-C4
  re-sequenced with both lanes' results in hand. Worst case
  pre-stated: commit-axis derivation at arc-3 scale moves the T1
  estimate materially and is surfaced the moment measured.

- **[USER] 2026-08-26 — the A4 route discussion (mid-pause):**
  Mike's reading confirmed (Verdi and etcd are legitimately
  different Raft dialects — theorem-grounded, not a porting error).
  Two [USER] contributions: (1) the FAMILY GENERALIZATION — prove
  the Verdi result for a family of algorithms, "generalizing Verdi
  along all the degrees of freedom that are available" — ENDORSED
  as the primary route (design note v2 §8 D2 revised: the
  obligation-signature route b′, converging with the
  reuse-T3-structure recommendation stated theorem-side; amortizes
  over S2/S3, T2, prevote/learners); (2) the PATCHED-SUBJECT
  stepping stone (bank current state; prove T1 for a Verdi-dialect
  etcd variant) — recorded as the NAMED FALLBACK with the
  subject-exactness caveat ([AGENT]): literal-chain artifacts fork
  under a patched subject, so it is a fallback on signature-factor
  failure, not a parallel track. SC1's probe re-targeted to
  organize its skeleton around the obligation signature; its
  measurements (does the lattice factor?) unchanged.

- **[USER] 2026-08-26 — the second grind-smell (mid-pause):**
  subject-exact equations flagged — "there must be opportunities to
  generalize surely?" [AGENT] concurrence + D4 added to the design
  note: the literal-chain mode is a tolerated scaffold; post-C2a the
  equation layer shifts to STRUCTURAL COMPOSITION (size-scaled
  symbolic execution on the existing pieces; symbolic preconditions;
  bounded-completion statements), with the landed literal equations
  re-roled as the compositional prover's validation corpus. Timing
  note: the reachability re-target means the big wave is unbuilt —
  the mode shifts BEFORE it. Calibration honesty: this is the second
  [USER] grind-smell that located a real abstraction gap (wave →
  round-replay; literal chains → compositional prover); the
  coordinator's own insight-test missed both while unit-level
  insight stayed high — pattern logged: LOCAL insight per iteration
  does not certify the METHOD's shape; method-level review belongs
  at every wave boundary.

- **[USER] 2026-08-26 — goal unset; exec redesign pass directed**
  ("build the most flexible pieces and then there's the best chance
  they fit together — implementation, proof, automation"; goal
  over-focus named as the propensity). [AGENT]: the flexibility
  redesign written as the design of record
  (docs/2026-08-26_campaign-flexibility-redesign.md): interfaces
  not chains — I1 obligation signature (SC1 = gate), I2
  compositional prover (C2a = gate; literal-mode manufacture STOPS
  effective now), I3 configuration-parameterized statements (T1/T2
  as instances; reachability becomes computed), I4 abstract checker
  interface; probe-gated α/β/γ sequencing with estimates SUSPENDED
  until the α gates' numbers land (both prior estimates broke on
  unmeasured assumptions); §6 makes the method review a standing
  coordinator function at every wave boundary. The layer-C note's
  D1-D4 stand, absorbed as interface instances; its ladder is
  superseded.

- **[USER] 2026-08-26 (closing the redesign pause):** "building
  general clean machinery isn't just an aesthetic, it's actually
  the only thing that will scale to other examples." Appended to
  the redesign note's rationale: generality IS the scaling
  mechanism — the inventory's general rows survive the next target;
  the subject-exact rows die with this one. Reconvene when the α
  gates (SC1, C2a) report; the T1 meeting-point decision is HELD
  for that reconvene ([USER] present for it; goal remains unset).

- **SC1 (scoping lane) — LANDED** @ 740c719e on campaign-arc4b
  (2026-08-26). GATE: honest FAIL (exit 1) — the un-swept-proof-file
  tamper check fired on the lane's own no-edit rule (the two new
  modules can't import into the aggregator without touching a
  tracked file); compensating verification on the record (both
  modules kernel-checked green as explicit capped targets, AxNative
  [propext, Quot.sound] on all eight proved lemmas, hatch 0);
  LANDING ACTION = two import lines in GoLeanProofs.lean at the
  wave boundary. THE THREE VERDICTS: (1) **I1 FACTORS, measured
  strongly**: zero handler-unfold residue in 5,005 chain lines;
  **the A4 kill DISSOLVES at obligation level — both discharge
  halves PROVED** (etcd_emptyAccept_discharges /
  verdi_frozen_discharges inhabit one followerCommitOk envelope);
  S2/S3 consume commit only through three obligation members
  (statement-verified). (2) Native S1 ≈ 2.5-3 units, calibrated by
  three end-to-end links (minutes each, axiom-clean); measured
  ADAPTS driver: etcd's becomeLeader clears the tally ⇒
  transition-scoped + victory-ghost-carried leader-quorum. T1's
  S2/S3 leaf ≈ 1.5-2 units (ghost-history chain); family SMS
  superstructure 4-8 units post-T1. (3) Harvest ring:
  choice-consuming but value-deterministic (345 draws fully
  classified; third step-exact replication of the pinned run) →
  per-arm sub-ring equations, no new choice machinery. **RECORD
  CORRECTION, owned by the coordinator**: T3's proved core is the
  election-safety ring up to one_leaderLog_per_term; log-matching/
  leader-completeness/SMS are ported STATEMENTS (the arc-3 modules'
  own docstrings say so — LeaderLogs.lean:31-33); prior campaign-log
  summaries calling the lattice "complete" across all four
  properties overstated — route (a) is DEAD for the upper
  properties because there is nothing to transfer, and the family
  route builds them over the signature. Patched-subject fallback:
  LESS attractive (its hedged risk measured small). Ops note:
  cold worktree full builds need 64G (silent OOM in the Raft tail
  at 48G). C2a still running; the meeting-point decision remains
  HELD for the [USER] reconvene.

- **Arc 4, A4-U19 = C2a — LANDED, THE INSTRUMENT EXISTS** @
  33e07325, gate PASS, 537 jobs: FrameSimS (the insertion-point
  shape clause; C1 completeness derivable), the full S-transport
  stack, **span_consume — the mid-walk consumption theorem** (a
  landed equation consumed at any placement hands back a LITERAL
  framed post-state), and the discharge witness performing exactly
  the operation U15's wall blocked (nine-step literal resume
  writing a frame cell after a relational sub-span, non-identity
  placement, abstract readout intact). Audit-pinned, lineage-lined
  (Yang-O'Hearn completeness half). WHAT THIS TAUGHT US: (1) the
  U16 sizing was corrected by measurement — in-place strengthening
  is BLOCKED at rebaseSimT (∃-split vs set-append freedom;
  attempts exhausted, not asserted), so the instrument landed
  ADDITIVE with copy-threaded S-induction; copies = scaffold with
  a retirement condition; (2) two probe ceilings rerouted to a
  generated mechanical mirror that elaborated first-pass green —
  boundary-stop-and-reroute working; (3) named residual: ∃-split
  extraction (cheap follow-up). The U15/U16/U18 reuse-instrument
  ledger row is CONSUMED. **BOTH α GATES NOW REPORTED (SC1 + C2a,
  both positive). The meeting-point decision is presented at the
  [USER] reconvene — nothing dispatched beyond this log until
  then.**

- **[USER] 2026-08-26 — the middle path (binding calibration):**
  slices have value; fragile expensive one-offs don't; don't build
  generality we won't need. Encoded as redesign note §7: the
  two-axis test (cost × consumer count), generality only against
  demonstrated demand, I3/I4 scoped down, family SMS deferred
  post-T1, consolidation demand-driven. [AGENT]: cadence resumed
  under these criteria — C2b dispatched (arc-4 lane, fresh worker:
  driver-loop symbolic-net lemmas + storage-resp arms,
  instrument-consuming) and C3 dispatched in parallel (arc4b lane,
  fresh worker: native S1 over NativeObligations, 2.5-3 units
  sized); lanes stay file-disjoint, arc4b lands as one merge at its
  completion boundary.

- **C3 (arc4b lane) — LANDED** @ 33a0b423 (2026-08-27), one session
  vs the 2.5-3-unit sizing: **native one_leader_per_term PROVED over
  the obligation signature** (n-generic — `voters` a parameter;
  `invariance` axiom-free; the FullInv.step preservation lemma
  replaces T3's six votes_ok_*), the COMPLETE etcd discharge (all
  seven members; two guards proved redundant on the reachable set),
  the I4-scoped S1 leaf, and the cross-time theorem (the twin's
  leaderOf check is cross-harvest — covered by starred vote
  monotonicity, NO signature extension per §7). Gate: the same
  single known structural red (un-swept lane modules; landing = six
  import lines), compensating kernel checks verbatim-clean. WHAT
  THIS TAUGHT US — the unit's crown find: **the non-vacuity WITNESS
  RUN caught a real fidelity bug** — the ghost `campaign` pushed no
  self-vote, making etcd's self-response-counting elections
  unsimulable (a silent under-approximation that would have VOIDED
  theorem transfer); fixed in-unit with the verdi own-vote rule.
  Lesson now standing: the witness is a FIDELITY INSTRUMENT, not
  paperwork — every spec-side fragment ships its witness run in the
  SAME slice. Cost note: b′-frame porting of a zero-residue chain
  ran 2-3× under port-anchored pricing; the residual risk lives in
  statement-side fidelity, exactly where the witness looks. [AGENT]:
  same worker (~277k) continues onto the T1-scoped S2/S3
  ghost-history leaf (SC1's 1.5-2 units, likely low end), witness-
  in-same-slice discipline explicit. C2b still in flight.

- **[USER] 2026-08-27 — trust-story clarification (the ghost-vote
  bug):** confirmed on discussion: the bug class CANNOT produce a
  false T1 — the statement never mentions the model, and the
  simulation direction (concrete ⇒ abstract) turns model
  under-approximation into UNPROVABILITY at the round lemma, never
  a wrong theorem. The witness discipline therefore protects two
  things, not soundness: (1) SCHEDULE — same-slice pointed failure
  vs a stuck goal deep in layer-C assembly weeks later plus
  invalidated intermediate work; (2) INTERIM CLAIM HONESTY —
  spec-side theorems (e.g. etcd_one_leader_per_term) are about the
  MODEL until the seam closes; an unsimulable model leaves them
  kernel-true but about nothing real, so the witness is what keeps
  pre-seam results meaningful. Doctrine line: in this architecture
  model bugs make us slow and interim-hollow, never wrong — the
  witness attacks both.

- **C4 (arc4b lane) — LANDED @ 76e63bba; THE LANE'S PROGRAM IS
  COMPLETE** (SC1 → C3 → C4, ~3 sessions vs ~5-7 units sized;
  2026-08-27): the S2/S3 ghost-history chain (HStep with SC1's
  commit-axis obligations as VERBATIM constructor premises —
  grep-checkable scoping), H1-H4 with H4 in its strongest T1 form,
  **s2_of_histInv / s3_of_histInv / s23_leaf**, the final-net
  checker interface with its justification lemma, six-step
  same-slice witness end-to-end. Gate: exactly the one known
  structural red (eight un-swept lane modules); compensating checks
  verbatim-clean; Classical.choice bisect-traced to stdlib list
  lemmas and accepted with derivation ([AGENT] — purging would be
  representation grinding). WHAT THIS TAUGHT US: (1) two
  statement-side findings pre-empted by SC1's census discipline
  (SNet cannot carry apply data → HNet; the two-net comparability
  form is falsifiable — along-one-trace is what is true); (2) the
  worker's own caution logged: do NOT discount the family-SMS 4-8u
  estimate by this velocity (T1-scoped structure admits
  equation-strength invariants; the family case does not). LANDING
  MANIFEST recorded (eight import lines + optional cleanups +
  judge-at-merge). [AGENT]: the landing belongs to the arc-4 lane
  at C2b's boundary (the aggregator is arc-4-owned; one-writer);
  queued for that boundary; the arc4b worktree retires after the
  merge. SPEC SIDE OF T1: DONE pending the seam — remaining T1 work
  is interpreter-side only (C2b in flight; reachable round arms;
  the two checker-interface I2 proofs; the seed pin; assembly).

- **Arc 4, A4-U20 = C2b — LANDED** @ f94c225a, gate PASS, 541 jobs:
  the SliceWalk loop-invariant schema (Floyd/Hoare lineage) +
  DriverNet instances symbolic in net length/payload/placement +
  witnesses + 9 pins, with kernel shape pins tying the proved
  statements verbatim to the pinned lowering. **THE COMPOSITIONAL
  MODE'S FIRST NUMBERS: ≥200× on the span class** (≈22 s elaborated
  once vs ≈70-85 min mirror kernel per replay, re-paid each
  re-derivation) — and the deeper win is KIND, not degree: the
  spans are symbolic where literal chains were an unbounded family
  under the ∀-stream; composed per-iteration bounds and witness
  runs land on census predictions EXACTLY. Mode price honestly
  stated: ~one unit for schema + 2 instances; marginal instance
  ≈ body facts only. Deliverable 2 redirected honestly: the
  heartbeat fixture never reaches the storage arms — the MsgApp
  round fixture is the shared C2c/C2d prerequisite. WHAT THIS
  TAUGHT US: (1) the mode shift is vindicated by measurement on its
  first real span class; (2) **the masked-kill convention** —
  piping compiler output through grep|head swallows cgroup
  SIGTERMs (several mid-unit "greens" were 48G kills); judge by
  captured exit codes, never absence of grepped errors — briefed
  verbatim into all future units; (3) `decide` on a TRUE Bool over
  the pinned program is still a 50 GB runaway — kernel_rfl remains
  the rule. LANDMARK NOW DUAL-TRIGGER (stale 151 + owed-on-scope:
  the Audit.lean import) — judge owed at the arc-4 merge, standing.
  [AGENT]: C2c to a fresh 13th-gen worker, opening with THE ARC4B
  LANDING (the boundary is now): merge 76e63bba + the eight import
  lines + gate expected fully green, then the MsgApp fixture,
  sub-ring census, and the payload-parametric storage statements.

- **P-2026-08-27 (calibration, third in series):** T1 ≈ 1-1.5 weeks
  from today (6-8 units remaining at measured 2-3 units/day + the
  milestone ceremony: mega-branch merge, dual-trigger judge,
  milestone audit); T2 ≈ +1 week; **T1+T2 ≈ 2-2.5 weeks** — inside
  the 2.5-4 window, trending under the revised P-2026-08-25. Basis:
  spec side DONE at 2-3× under sizing; compositional mode measured
  ≥200×; every remaining item has measured precedent EXCEPT two
  named risks (the seed pin — undemonstrated reflection route; the
  assembly — treated as a probe per the walls-below-clean-designs
  pattern). T2 design caveat, flagged for a [USER] gate: what
  "quantified num_parties" requires at the HARNESS level (abstract
  quantification with the n=3 harness as instance vs a parameterized
  wire family) — touches what the theorem says, so it is the user's
  call, not the coordinator's.

- **[USER] 2026-08-27 — the CHOICE-INVARIANCE LEMMA (design
  contribution):** "for this abstraction, and these operations,
  choices don't matter... the literal heap is isomorphic to all
  other heaps constructed via these commands" — a lemma, not an
  axiom. [AGENT] analysis, adopted: self-simulation up to
  ~ := relocation × capacity-slack (both components EXIST — the
  ρ/FrameSimS layer and the valuation atoms), with absRead/Fam
  ~-invariant; lineage: bisimulation up-to / data independence /
  the project's own quotient-theorem note. THE FACTORING: choices
  split into latitude draws (quotiented by the lemma — spill
  capacities, canonicalized mapIter) vs semantic draws (the 28
  delivery picks — the nondeterminism T1 is ABOUT); the two-bounds
  doctrine's latitude-vs-semantics distinction surfacing as proof
  structure. FIRST CONSUMER: the seed pin (named risk #1) — SC1
  classified all 171 init draws as absorbed-class, so invariance +
  ONE literal init run replaces the ∀-over-choices 81k-step
  reflection; the undemonstrated reflection route may be
  unnecessary. Middle-path: built INSIDE the seed-pin unit (≥4
  prior ad hoc instances + a waiting consumer = demonstrated
  demand); charter caution: probe the operation census against ~
  first — a draw-dependent LAYOUT the atoms don't capture is the
  hidden-wall candidate.

- **[USER] 2026-08-27 — the representation-engineering principle:**
  "sometimes we can trade proof effort for representation
  engineering. If we know that a representation has nice laws over
  it, we can compute over this representation and scale... really
  just Cousot-Cousot abstract interpretation in core insight."
  [AGENT] mapping, recorded: the campaign's four instances of the
  trade (FastEval+transfer; lens/absState; atoms+the ~ quotient;
  reflection/pins) are one pattern — proof budget buys LAWS once,
  instances become evaluation. Precise AI reading: absRead = α,
  specRound = the abstract transfer functions, round lemmas = their
  soundness, Fam = domain well-formedness; deliberately at the
  EXACT end of the Galois spectrum (the theorem needs equalities).
  Community-stress-tested form: certified abstract interpretation
  (Pichardie/Verasco lineage) with per-program soundness via
  translation validation. FORWARD HEURISTIC, adopted into unit
  chartering: when a new obligation family appears, first ask
  "what representation makes these evaluable," not "how do we
  prove these."

- **[USER] 2026-08-27 — the SYMBOLIC SEMANTICS proposal:** a third
  layer between the relational semantics and future Iris reasoning —
  `opsem ↔ relational ← symbolic-with-choice-erasure` — erasing
  choices without easily-observable effects (allocation etc.).
  [AGENT] analysis, adopted with sequencing: flagship precedent =
  CompCert's memory model (block IDs = allocation-choice erasure);
  ours adds capacity slack + canonicalized iteration draws; the
  correspondence needed is bisimulation-up-to-~ (concrete projects
  down for invariant transfer; erased choices realizable for
  ∃-transfer) — the choice-invariance lemma is its erased half.
  Payoffs: invariance proved ONCE as the refinement; statement
  hygiene (no atom/ρ threading); the natural Iris seat for the
  concurrency era. SEQUENCING ([AGENT], middle-path): NOT
  mid-endgame — T1 finishes on the lemma form, with the seed-pin
  unit building ~/canonical forms FORWARD-COMPATIBLE as the future
  semantics' state space; the symbolic semantics is the POST-T1
  consolidation centerpiece — three consumers waiting at the right
  time (scaffold retirement; the W3.2 opsem write-up; W7/SpecTec
  adjacency) vs zero that T1 needs early.

- **[USER] 2026-08-27 — doc consistency + the coherence audit:**
  directed: keep planning docs consistent; backlog an overall
  design-audit coherence pass (the half-built-mechanisms risk from
  heavy semantics engineering). [AGENT] executed same-hour: the
  layer-C note gained its supersession banner + the seed-pin route
  correction (choice-invariance, not reflection); the flexibility
  redesign gained §8 — the doc-of-record HIERARCHY (one design of
  record per layer; seam-note reconciliation queued to the arc-4
  lane boundary), the four post-α design contributions
  cross-referenced, and **the COHERENCE AUDIT chartered as a
  backlog item**: a dedicated design-coherence dimension of the T1
  milestone audit, deliverable = ONE mechanism registry (completion
  state, scaffold tags, retirement conditions, design-of-record
  pointer, orphan/duplicate detection) replacing scattered
  docstring tags — seven known scaffolds already enumerated in its
  scope.

- **Arc 4, A4-U21 = C2c — LANDED** @ 4a158041, both gates PASS, 559
  jobs: THE ARC4B LANDING fully green (two green-in-isolation/
  red-in-composition findings fixed honestly: the witness-module
  joint-import collision; the spec-anchors xargs 128KiB false-death
  — a real gate bug fixed fail-closed, both directions re-tested) +
  THE MsgApp ROUND FIXTURE (23,488 steps/8 choices; first probe
  decoded the twin's snapshot-boot log) + the sub-ring census
  (SC1's classification re-verified at MsgApp scale; ring footprint
  27 cells) + **FIVE payload-parametric storage-resp spans incl.
  the choice-free storage-resp span W4, with the span_consume
  composition demonstrated at a non-identity placement** + the
  MsgVote census (vote rounds write hard state but produce NO
  storage arms — the round-kind matrix now spans three ring
  depths). WHAT THIS TAUGHT US — **THE THIRD KERNEL WALL:
  representation ASYMMETRY, not size** — open-term comparison of
  γ-images across two representations is effectively unbounded
  (>46 min/crossing) while the same content with SHARED terms is
  subsecond; fix = tree-propagation crossings + parallel window
  modules (RingEqW2: >46 min → 135 s); now a ledger template. Also:
  the >46-min crossing was STOPPED AND BISECTED, not waited out —
  the doctrine functioning as reflex. Cost: SC1's sizing held
  (~6 min window kernel vs 4-5 predicted); the overrun was the
  route detour, amortized as the template. [AGENT]: C2d to the same
  worker (the first reachable ROUND-KIND LEMMA at the MsgApp
  fixture — the R-form's first proved instance); the SEED-PIN unit
  dispatched in parallel on a fresh new-files-only scoping lane
  (arc4c) carrying the choice-invariance lemma, forward-compatible
  with the symbolic semantics per the standing decisions. Landmark
  dual-trigger at 159 — stands.

- **Arc 4, A4-U22 = C2d — LANDED** @ dcbffa0c, gate PASS, 571 jobs:
  **`roundMa_lemma` — THE R-FORM'S FIRST PROVED INSTANCE**, end to
  end at the reachable MsgApp append round: any weak-placement of
  the canonical loop-head state runs the full round (arm + harvest
  ring + both storage-resp arms + driver suffix), consumes exactly
  the censused 8-draw prefix, re-establishes family membership
  (roundMa_closure); the delivery pick is the named semantic
  crossing (roundMa_pick), positions 1-7 identified latitude — the
  factoring's input prepared, ∀-latitude one rewrite when ~ lands.
  Marginal round-kind cost measured: the lemma layer elaborates in
  2.2 s — the next kind costs its windows only. WHAT THIS TAUGHT
  US: (1) the coordination stop-condition did NOT fire — R-form
  states cleanly pre-~; (2) **DESIGN FINDING (read-first, not
  shimmed): single-splice FrameSimS cannot place a pruned
  sub-fixture into an interleaved outer frame — sub-span reuse
  inside bigger walks needs multi-splice OR the heap-permutation
  quotient, i.e. THE ~ CLASS, state edition. The ~ quotient now has
  THREE demanded consumers** (seed pin; sub-span multi-splice; the
  successor-canon question the round INDUCTION needs answered) —
  the symbolic-semantics trajectory re-derived from below, again;
  (3) self-return proved at the γ level closed — the third-wall
  lesson applied at design time; (4) ops note: four lake-build
  SIGTERMs under sibling scope churn (lake env lean untouched;
  quiet-box retries clean) — logged for the wave-boundary
  build-stagger review. [AGENT]: U23 to a fresh 14th-gen worker
  (the MsgVote round instance — template-stamping on U21's ready
  fixture — + the two checker-interface I2 proofs); THE ROUND
  INDUCTION HOLDS for SP1's ~ landing (its canon question is ~'s to
  answer). Landmark dual-trigger at 163 — stands.

- **Arc 4, A4-U23 — LANDED** @ 5778bcb3, gate PASS, 585 jobs:
  **`roundVote_lemma` — the R-form's SECOND instance** (first
  election-kind round; Term/Vote persistence + net delta +
  violations 0→0 read out) — **U22's "windows only" marginal-cost
  claim CONFIRMED at a second kind**: 578 s window kernel + 3.3 s
  lemma layer; two one-time template payments bisect-measured and
  folded (auto-discovery of choice-free mirror quit sites; the
  γS_pin table-footprint premise on defined-type mapIter
  crossings). Checker interfaces: **delivered as model bridges,
  honestly NOT claimed closed** — s1_viol_delta proved,
  S23's both sound fields proved given the projection premise, the
  composed corollaries run the arc4b leaves end-to-end, four
  violation guards pinned VERBATIM against the lowering; the
  priced residual = the span-computes-model theorem (≈1 unit,
  utoa digit-loop kit + two span lemmas). WHAT THIS TAUGHT US:
  (1) the template holds across round-kind families — the
  induction's per-kind cost is now a measured constant; (2) the
  honest-residual pattern beats in-budget overreach (the worker
  priced the byte-level closure instead of rushing it). Zero
  SIGTERM interference this session. [AGENT]: U24 to the same
  worker (~412k): the span-computes-model slice (closing the
  bridges to the bytes) + the MsgAppResp maybeCommit round kind
  (the matrix's untested commit-without-append row). Landmark
  dual-trigger at 166 — stands. SP1 (~) still in flight.

- **Arc 4, A4-U24 — LANDED (gate re-run in flight)** @ e11b6a19:
  **`roundMar_lemma` — the R-form's THIRD instance, the
  commit-without-append row**: committed AND applied advance 1→2
  on the leader with NO append — the interpreter-level half of the
  etcd commit dialect, meeting the followerCommitOk discharge at
  assembly; shipped with ZERO hand-written window theorems (the
  manifest-driven Eq emitter — the template is now a generator).
  Span-computes-model: BOUNDARY-STOPPED at the measurement (the
  chartered trigger fired — plain-for has no head schema; anatomy
  banked; re-priced 1.5-2-unit arc; nothing half-built shipped).
  The γS_pin promotion's ≥2-consumer trigger fired and was taken
  (SymTables.Agrees.concS_eq). The unit could NOT gate in-session
  (GATE_EXIT=143) — recorded, not skipped, with exit-code-captured
  compensating verification. **OPS DIAGNOSIS ([AGENT], correcting
  two worker theories): there is NO reaper.** The arc-2 "dying
  builds" were STALE failed-unit entries from the parked wave
  (Aug 23, Result=oom-kill); the live kills are CGROUP OOM AT OUR
  OWN CAPS — the coordinator's own charter briefs propagated
  GOLEAN_MEM_MAX=24G for gates while the tree grew past 585 jobs;
  kernel SIGKILLs a lean worker, systemd SIGTERMs the scope
  (exit 143 mimicking an external kill); lulls = incremental
  retries shrinking the job set under the cap. WHAT THIS TAUGHT
  US: a wrong-but-vivid theory (the reaper) survived two units
  because the mundane check (scope Result= + timestamps) was never
  run — the async-diagnosis rule (judge by artifacts) applies to
  INFRASTRUCTURE too. FIX (lane-local, no global change): gates at
  GOLEAN_MEM_MAX=64G henceforth (all future briefs); stale failed
  units left for the operator (reset-failed is machine-global
  hygiene — Mike's call). U24 gate re-running at 64G now.

- **OPS INCIDENT (2026-08-26, [AGENT] fault, owned): the box OOM'd
  the session** — the coordinator launched the U24 gate at a 96G
  cap while the SP1 sibling held standing 64G-build instructions;
  the gate started at 70G available (SP1 mid-build); the OOM killer
  took the multiplexer (the documented badness-score failure mode).
  Casualties: the session (recovered), the gate attempt (no
  result), SP1's worker (stopped; its partial work SAFE — five
  untracked modules + log in arc4c, no commits lost, transcript on
  disk). **THE SERIALIZATION RULE, now standing: FULL builds/gates
  are EXCLUSIVE box-wide — one at a time, enforced by coordinator
  dispatch ordering, never by per-worker free-memory guesswork**
  (the guard checks a snapshot; two ramping builds pass it
  simultaneously). Recovery: gate re-running SOLO at 96G/6-threads;
  SP1 resumes after it lands. [USER] flagged the OOM risk on
  reconnect — correct call.

- **[USER] 2026-08-26 — grind classification challenge on the warm
  loop:** [AGENT] split verdict, adopted: the warm loop = allowed
  (one-time bounded cache repair); the EXPOSED PATTERN = a
  structural tax failing the doctrine — (1) interface-hot edits
  (which further-consumers ENCOURAGES) invalidate the heavy tail
  for hours; (2) the dominant cost is the retired literal-mode
  corpus (8-27G elaboration per generated module) still sitting in
  the DEFAULT build target; (3) the promotion rule lacked a
  build-cost dimension (statement-additive in-place edits are
  build-explosive). THREE CORRECTIONS, each with this incident as
  its demonstrated consumer: (a) SPLIT THE VALIDATION CORPUS into a
  separate non-default lake target built at landmarks only —
  chartered as the next arc-4 unit's opening slice; (b) promotion
  convention amended: interface-adjacent lemmas land in NEW
  downstream-invisible modules unless in-place is semantically
  forced; (c) the coherence audit gains a build-cost-topology
  dimension (import-hot files + invalidation footprints). Also
  standing from this incident: interface-touching edits owe a
  cache-producing sequential warm before any full gate; lake env
  lean verification produces NO artifacts — never treat it as
  having warmed anything.

- **SP1 (arc4c lane) — LANDED @ 8e23af6e; the lane's program
  complete** (2026-08-26): THE PROBE VERDICT — strict ~ REFUTED at
  exactly 3/171 init draws (randomizedElectionTimeout: a PERSISTED
  value draw through mapIter — the charter's named hidden-wall
  class realized as a scalar, not a layout) and held at 168;
  answered by the VISIBLE one-field mask ~ₘ (sole reader =
  tick-path, structurally unreachable; the strict refusal
  kernel-pinned). Landed: ChoiceCanon/ChoiceInv + the seed pin —
  Seed N₀ DISCHARGED (C3's hypothesis), SeedFam (the induction
  base), absRead pinned at the all-zeros abstract seed, the
  ~ₘ-witness (a genuinely different init run landing equal), the
  closed 120 s setup link, computed-vs-literal adopted as standing
  rule (measured 10 min → 40-120 s). Gate: the known structural
  red + compensating checks verbatim (7× EXIT=0, 559 jobs, AxSeed
  clean). **THE HONEST OPEN ITEM, [AGENT]-flagged by the worker
  and now on T1's critical path: `SeedChoiceInvariance` is a NAMED
  PREMISE, not a theorem** — the ∀-init-stream discharge was
  deferred (§7 call: the general transports belong to the symbolic
  semantics). T1 CANNOT ship conditional on it; [AGENT] decision:
  the discharge lands in the C-wave as mirror windows over the
  init span at ~ₘ (the U22 template at ~3-4 rounds' one-time cost;
  the 168/3 census + mask make every window's draw-site treatment
  known in advance) — chartered into the round-induction unit.
  WHAT THIS TAUGHT US: the probe-first pattern caught a REAL
  narrow refutation that a bulk proof attempt would have hit as an
  unexplained failure deep in a 81k-step derivation; and the mask
  is the honest form of "choices don't matter" — they mostly
  don't, and where they do, the form SAYS SO. Landing manifest
  (seven imports) queued to the next arc-4 boundary; arc4c retires
  after. U25 still in flight.

- **Arc 4, A4-U25 — LANDED** @ eee6b43b, gate PASS 230.44 s (was
  927 s — the corpus split's −75%; durable form: 96 modules off the
  gate path, corpus swept at landmarks — 22,538 declarations
  axiom-clean; coverage check now fail-closed TWO-closure) +
  **`roundVr_lemma` — the FOURTH R-form instance, the first fully
  HANDS-OFF** (emitter v5; 30 crossings γ-valid first try; the S1
  leadership claim born in the readouts). **THE STRUCTURAL
  ROUND-KIND MATRIX IS COMPLETE** (heartbeat/hardstate/
  storage-append/commit/election rings; no-op row censused: zero
  state movement). Honest ops: this unit's kills systemctl-PROVEN
  plain OOM (unscaled threads at 48G; the U22/U24 signature left
  open as possibly different — decoy experiment run); a generator
  fail-open panic! fixed fail-noisy; the ci diff flagged for
  delta-review at the audit (gate-adjacent — correct per policy);
  build-lock removed externally once while held (owner-file
  proposal logged). WHAT THIS TAUGHT US: the emitter pipeline has
  crossed the hands-off threshold — round instances are now
  generator products, which is what makes the remaining shape-reuse
  rows (MsgProp etc.) near-free. [AGENT]: U26 dispatched — THE
  SUMMIT-PUSH UNIT (arc4c landing + the successor-canon slice on
  the coordinator's design: round-post ~ₘ-canonical pins composing
  via the shared-pin rule + THE ROUND INDUCTION with SeedFam base
  and the init-span ∀-stream discharge); SM1 dispatched in
  parallel (arc4d, new-files-only: the span-computes-model arc
  from U24's banked map). Landmark STALE(170)+OWED — stands, the
  merge approaches.

- **Arc 4, A4-U26 — LANDED, THE ROUND INDUCTION IS PROVED** @
  772a295b, both gates PASS (241 s): arc4c landed (SP1's red
  closed); **`round_induction` + FamTrace + the safety/fullInv/
  flat/seeded corollaries, LIVE in the default target, witnessed by
  a genuine seedN₀ election chain ending in a non-vacuous leader**;
  corpus sweep 23,278 decls axiom-clean. THE DESIGN VERDICTS:
  (1) the coordinator's successor-canon design REFUTED at both
  stop points (fixtures resist canonicalization; ~ₘ cannot
  transport RoundFam through FrameSim's vocabulary) — the probe
  found the simpler truth: the kinds' loop-head configs are
  LITERALLY EQUAL, so the induction chains literal canon steps
  with zero frame algebra; (2) the ∀-stream discharge
  boundary-stopped with the mispricing NAMED: the mirror-window
  estimate priced the canonical init completion (O7, ≈35-60 min,
  separable), not the ∀-stream lift, which requires the per-class
  ~ₘ transports — the symbolic semantics' erased half; enumeration
  impossible in principle. The induction lands UNCONDITIONAL at
  censused canonical prefixes; SeedChoiceInvariance stays a
  visible named premise at exactly one consumer (T1's ∀-stream
  form). THE ASSEMBLY PROBE: agreementT1_skeleton typechecks;
  open obligations O1-O7 enumerated (adapters, ~28 replay
  instances, the prune seam, the abstract dialect's commit/append
  members, the checker seam [SM1 in flight], the ∀-stream lift
  [the scoping item], init completion). WHAT THIS TAUGHT US: the
  probe discipline caught the coordinator's own design twice in
  one unit — the summit push behaved exactly as chartered.
  [AGENT]: MERGE PREP OPENS (the bank point is now — ~26 units,
  landmark dual-trigger at 176): snapshot, rebase onto main,
  warm+gate, judge + AuditCorpus landmark, then THE AUDIT ASK +
  the O6 scoping recommendation go to the user together. Lane
  building pauses for the ceremony; SM1 continues (separate lane).

- **SM1 (arc4d lane) — LANDED @ 365f4502** (2026-08-26): the
  CondFor plain-for head schema (the one missing kit piece,
  Floyd/Hoare lineage, witnessed) + the utoa weak span (∃-string
  form as banked) + **`s1_span_computes` — THE S1 BRIDGE
  BYTE-CLOSED** (three branches, the violations counter literally
  `wN + if s1Fires then 1 else 0` in the machine readout;
  fire/clean witnesses; composed count matches the compiled walk
  exactly) + the four pb-getters; the apply walk BOUNDARY-STOPPED
  at measurement (two unbanked map fragments ≥2× banked price —
  the stop clause taken before sinking budget; S23 residue ≈1-1.5
  units, route mapped). Gate: the known new-files-only red +
  compensating checks verbatim (30 pins in place, 7 byte-pins
  axiom-free). O5's first half is DONE. WHAT THIS TAUGHT US: the
  banked-anatomy pattern priced three of four items within budget
  and caught the fourth's mispricing at measurement — banking
  beats re-discovery. [AGENT]: SM2 dispatched (fresh worker,
  arc4d — s23_span_computes from the banked route; new-files-only,
  does not move the frozen audit target); arc-4 lane and the
  ceremony HOLD for the user's three calls (landing shape, audit
  scope, O6 route).

- **[USER] 2026-08-26 — the milestone audit's shape (directed):**
  top priority = COHERENCE AND DIRECTION OF TRAVEL — "the big issue
  in this buildout is the potential for a messy accreted build,
  rather than something coherent" — plus a detail-oriented
  technical auditor. [AGENT] audit plan (revised from the earlier
  proposal): reviewer 1+2 (the priority pair): (a) ARCHITECTURAL
  COHERENCE — is the stack one design or an accretion: the
  mechanism census (every layer: transports, frame/shape, lens,
  choice-inv, SliceWalk, emitters, the corpus split), half-built/
  orphaned/duplicated machinery, scaffold tags vs reality,
  doc-of-record consistency (the §8 hierarchy), naming/layering
  sanity — DELIVERABLE: the mechanism registry (the backlogged
  coherence-audit item, produced BY this audit); (b) DIRECTION OF
  TRAVEL — does the built structure converge on T1+T2 and the
  reusable stack: the O1-O7 list vs what exists, the interface
  stack's vacuity checks re-examined against the landed instances,
  what the next target would actually reuse, where drift is
  accumulating. Reviewer 3: the DETAIL TECHNICAL auditor —
  semantics/correspondence (mandatory per standing doctrine) +
  claim strength: the R-form statements' honesty, the visible
  SeedChoiceInvariance premise, the ~ₘ mask's justification chain,
  the round-induction statement vs its docstrings, the ci/corpus-
  split changes (U25's flagged delta), axiom/pin integrity.
  Verification passes default-refute as always; Opus throughout.
  Launch AFTER gate+judge at the merged tip (audit the final
  state). Ceremony order: gate (running) → judge + AuditCorpus
  landmark → audit → fix round → [USER] ff sign-off.

- **THE LANDING AUDIT RETURNED** (2026-08-26; 33 agents, 3 Opus
  reviewers per the [USER] shape, default-refute verify): 29
  findings — **21 CONFIRMED, 7 DOWNGRADED, 0 REFUTED** (one verify
  pass lost to an API error; treated confirmed-unverified). THE
  REGISTRY delivered (docs/2026-08-26_mechanism-registry.md).
  Coherence verdict: "much closer to one design than an accretion"
  — lineage lines everywhere, the Go-general/raft boundary holds,
  the corpus split fail-closed — with the failures AT THE SEAMS
  (unconsumed duplicate, five superseded Props one FALSIFIED,
  stale scaffold tags, the gitignored evidentiary base, the broken
  doc-of-record chain). Direction verdict — the big one:
  **round_induction couples NOTHING between concrete and abstract
  chains** (correctly proved, but the pairing = O5's open half
  while docstrings/log claim the paired form); the O-census
  incomplete (12 viol sites, the S2/S3 assembly, the I1 vacuity
  debt unlisted); the C2a instrument consumer-less after its one
  real use bypassed it; the literal-mode stop overrun (3 chains +
  ~28 planned — the mode decision for the replay wave is now a
  PENDING COORDINATOR DECISION); reuse mass 0.9% of branch lines
  (though the mechanism:instance structure itself audited clean).
  Technical verdict: the induction/R-form/census arithmetic all
  CHECK (hypothesis-by-hypothesis); one REAL fail-open found
  (collectFix's length-stability vs in-place widening) + the
  absTwinRead fail-closed gap + the witness-placement weakening of
  the non-vacuity gate. WHAT THIS TAUGHT US: (1) the summary-layer
  drift pattern (P2R's lesson) recurred at arc scale — proofs
  sound, prose overclaiming, now twice; the fix-round rewrites and
  the census completion are the response; (2) the [USER] coherence
  priority found what neither prior audit shape would have (the
  consumer-less instrument, the evidentiary-base hole). [AGENT]:
  fix round dispatched (F1-F7; the abs-pairing, the Verdi
  instance, and the replay-mode decision recorded as next-charter,
  not fix-round, items); delta-review after; then the ff ask.

- **SM2 (arc4d lane) — LANDED @ 7fa0e04d; THE LANE COMPLETES —
  S23 BYTE-CLOSED** (2026-08-26): `s23_span_computes` (the whole
  apply call from symbolic checker state; cursors exact, the
  violations arithmetic literal in the readout) + `s23_abs_step`
  (projection commutation; injective data coding closes the
  model-Nat/machine-string gap the banked route left unpriced) +
  fire/clean witnesses at the bridge's own events; 11 modules, 31
  pins, zero warnings; ≈1.2 units vs the 1-1.5 price (two lifted
  engines absorbed the overrun risk). O5's interpreter half is
  FULLY DONE; the residue is assembly-time seams by design
  (ClaimTrace-class). WHAT THIS TAUGHT US: the anomaly branch was
  deliberately NOT walked (it computes no model predicate — the
  walk proves it untaken): scoping by what the model consumes, not
  by what the code contains. [AGENT] LANDING DISCIPLINE: arc4d's
  19 modules were NOT in the landing audit's scope — the lane does
  NOT land before the ff; the audited merge covers b4977d05 + the
  fix round only, and arc4d lands as the next lane merge with its
  own (small) ceremony. Promotion targets (StrMapMem, the spine
  evaluator) recorded for a consolidation slice.

- **[USER] 2026-08-26 — THE BASECAMP DESIGN REVIEW (directed):**
  reach a reasonable point, then a design review — "can we steal
  ideas from RefinedC / Brick and turn our proof into sensible
  abstractions rather than ad-hoc grind-output"; "value in a
  'basecamp' before we climb the summit." [AGENT] plan, adopted:
  BASECAMP = main at the landed arc-4 merge (audited, judged,
  registry in hand). THE REVIEW runs there, BEFORE any summit
  unit: inputs = the mechanism registry + the honest O-census +
  RefinedC (spec-as-refinement-type, verification-as-typing,
  automation-as-subsumption, manual lemmas as escape hatch) +
  Brick (the promotion-ledger lineage; the framework-vs-parts-bin
  test). THE SHARP QUESTION: recast the equation/arm/round layers
  as a TYPING JUDGMENT — do the ~28 replay instances become typing
  derivations (dissolving the pending replay-mode decision), and
  are the O1/O2b adapters subsumption rules? Output = a per-layer
  recast proposal under the two-axis test — recast ONLY where it
  changes summit cost or second-target reuse; explicitly NOT a
  rewrite of landed proofs. The symbolic-semantics design folds in
  as the type layer's semantic companion. Sequencing: fix round →
  delta-review → [USER] ff → THE REVIEW → the summit waves under
  whatever shape it chooses.

- **[USER] 2026-08-26 — basecamp review calibrated + sources
  landed:** deps/ now holds the FULL BRiCk clone (@ eee838e7 — note
  ltac2-llm + AGENTS.md in its tree: agent-integrated automation in
  an industrial Iris stack), deps/refinedc (with Lithium), and
  deps/brick-wp (our own earlier library). Calibration ([USER]): do
  NOT clone RefinedC's approach — our toolkit's consumer is an
  AGENT OPERATOR, not a human annotator; steal DESIGN, and aim for
  coherent abstractions precisely because BRiCk/RefinedC already
  paid the design-debugging cost we should not replicate. [AGENT]
  steal-candidate list for the review: (1) Lithium's
  NO-BACKTRACKING deterministic proof search — predictable
  automation is agent-debuggable automation (our emitter/prover
  should have its determinism discipline, stated); (2) RefinedC's
  separation of the type-RULE layer from the automation layer +
  escape hatches that do not poison composition (our manual-lemma
  seams need that discipline named); (3) BRiCk's industrial
  layering + its agent-facing conventions (ltac2-llm, AGENTS.md —
  read for how they charter automation for agents); (4) brick-wp's
  own retrospective (what we already learned once). The review
  evaluates each against the agent-operator axis: chartable units,
  machine-checkable acceptance, honest failure surfacing,
  budget-awareness — not annotation ergonomics.

- **THE LANDING FIX ROUND — COMPLETE** @ 07d06139, gate PASS 255 s
  (2026-08-26): 22/29 FIXED (collectFix fail-open closed with a
  kernel regression witness; absTwinRead fail-closed with TypeId
  checks; the falsified Skel props DELETED with deletion tests; the
  PickTransport duplicate deleted, ledger closed-unconsumed;
  Star/ReachRel unified; every induction overclaim rewritten to the
  truth with O5b as the named open pairing; the witness-return
  corrects the non-vacuity weakening — corpus criterion amended:
  A WITNESS SHIPS WITH ITS LAW; 33 generator/census tools TRACKED
  under tools/campaign/ with provenance; the design of record +
  registry + findings pack now ON THE BRANCH; the complete T1
  census committed; the first tracked CORPUS-LANDMARK-RUN marker),
  4 RECORDED-OPEN (un-laundered), 3 NEXT-CHARTER (O5b; the Verdi
  instance; the O2 mode decision — now folded into the basecamp
  review). F2 re-verification: NO pinned number moved — the bug
  was real (probe-reproduced) but the seed never entered its path;
  the deliberate deltas measured and explained (627 jobs, 256 s
  gate — the witness-return price). Ops: this round's kills =
  cgroup oom from window-module CONCURRENCY (per-module peaks
  modest); measured remedy recorded (warm at 2 threads, full at 8).
  [AGENT]: judge re-run launched (Audit.lean is watched — the
  trigger applies; Challenge closure verified disjoint but the
  milestone merge takes no shortcuts) + the policy delta-review of
  the fix diff, in parallel; the ff ask follows both.

- **THE LANDING CEREMONY — COMPLETE; FF SIGN-OFF POSED** (2026-08-26):
  tip c4986b29, tree clean, main verified ancestor (ff-only will
  succeed). The chain, end to end: the 146-commit lane + the main
  merge (two union conflicts) + the milestone audit (29 findings,
  registry delivered) + the fix round (22 fixed, no numbers moved)
  + the delta-review (8 residuals, operator-applied same-day, one
  deferral reasoned) + judge PASS at-tip (56 theorems, 118 s replay
  — after the wrapper's Solution pre-build fixed the cold-clone
  breach the delta-review predicted; runs 1-2 documented, the
  wrapper edit delta-flagged for the basecamp review) + the tracked
  corpus landmark + final gate PASS. WHAT THIS CEREMONY TAUGHT US:
  (1) the delta-review's cold-build finding was vindicated against
  the JUDGE within hours — reviews that predict failures are the
  cheap kind; (2) the witness-with-its-law rule and the judge's
  cold clone interact — now handled in the wrapper's own
  trust-neutral pre-build pattern. Merge sign-off is the user's, at
  this moment, for this merge; push separate as always.

- **[USER] 2026-08-26 — MERGE APPROVED AND EXECUTED: main @
  c4986b29** (ff-only, clean; the arc-4 stack — 150+ commits of
  equation machinery, signature + native chains, seed/choice
  carrier, round lemmas + induction, checker bridges, corpus
  split, tracked tooling — is on the trunk). Push not executed
  (separate sign-off, unrequested). BASECAMP REACHED. **THE
  MID-EXECUTION DESIGN REVIEW is chartered with the [USER]
  four-goal frame**: (1) a proof that achieves the goal; (2)
  reusable machinery solid for further proofs; (3) machinery
  LEGIBLY understandable — not a ball of mud; (4) reuse of
  tried-and-true design from BRiCk / RefinedC / anywhere.
  Explicit mandates: pay down debt; coherent design; identify
  KILLS (retired mechanisms). [AGENT] structure: phase 1 = three
  parallel readers (BRiCk architecture+agent-conventions;
  RefinedC/Lithium type-rule-vs-automation separation; brick-wp
  retrospective) + the coordinator's own frame from the registry/
  census/design docs; phase 2 = the synthesis — per-layer
  keep/recast/kill verdicts, the debt list, the legibility plan,
  the summit plan reshaped; phase 3 = [USER] reviews the proposal
  before anything builds.

- **[USER] 2026-08-26 — the compositionality test (review
  calibration):** separation logic is not the final word; the
  principle is COMPOSITIONALITY — "check something is true in the
  local environment, then establish it can operate in a set of
  contexts without disturbing them." Adopted for the synthesis as
  the replacement for BRiCk's Rule 0: every spec form names its
  FRAME STORY (context set + non-disturbance promise) in its
  layer's native vocabulary; a spec usable only with global
  knowledge is the suspicious object regardless of logic. Noted:
  our frame layer is already this position implemented (semantic
  locality upstream of any BI); rely-guarantee is the interference
  version for the concurrency era. Honest self-application: the
  equations/round lemmas/quotient PASS; the seed pin is
  legitimately global (a base case); the two FAILURES are already
  named debts — the missing abs-pairing (under-coupled = also
  non-compositional) and Fam-as-global-well-formedness (a typing
  context's job, likely the professor's call).

- **[USER] 2026-08-27 — B1 CORRECTED (a coordinator error fixed):**
  the synthesis proposed designating T1-replay as a milestone
  theorem — [USER]: "it emphatically IS NOT in the TCB. The TCB
  claim quantifies over all choices on the concrete interpreter.
  The lift is untrusted machinery for making our reasoning nicer."
  ADOPTED: the designated layer stays the harness contract ONLY —
  (1) always-emits-correct-value (AgreementT1 as pinned, untouched)
  and (2) **NEVER-FAULTS** (∀ fuel ch: no error/stuck/panic outcome;
  fuel-out excluded) — the second is the [USER]-described end-state
  statement, currently missing; draft to be prepared for [USER]
  designation (it absorbs much of the T1-V guard census into one
  theorem). T1-replay is DEMOTED to an internal stepping-stone
  lemma (proof-side, log-tracked, never designated, never in
  Challenge); the lift arc unchanged (cequiv_iff_spanIso →
  per-class transports → bisim-up-to → verdict invariance), now
  correctly classed as untrusted machinery end to end — no
  designation ceremony anywhere in it. B2 confirmed [USER] same
  session: untrusted abstractions verified w.r.t. the trusted
  semantics, useful-not-complete. The synthesis doc's §2-B1 is
  superseded by this entry.

## Judgment calls

- **[USER]** 2026-08-22: campaign launched; constitution is the scope.
- **[AGENT]** 2026-08-22: Q7 operative reading (above).
- **[AGENT]** 2026-08-22: Arc ladder as above; Arc 1 opens
  immediately on the `campaign` branch (statement work is
  supervised-class — it stays on-branch, merge-gated, so supervision
  is preserved by the merge gate itself).
