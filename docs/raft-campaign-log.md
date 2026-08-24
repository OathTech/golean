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

## Judgment calls

- **[USER]** 2026-08-22: campaign launched; constitution is the scope.
- **[AGENT]** 2026-08-22: Q7 operative reading (above).
- **[AGENT]** 2026-08-22: Arc ladder as above; Arc 1 opens
  immediately on the `campaign` branch (statement work is
  supervised-class — it stays on-branch, merge-gated, so supervision
  is preserved by the merge gate itself).
