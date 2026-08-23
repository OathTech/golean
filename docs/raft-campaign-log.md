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

## Awaiting [USER] — the queue

- **POSED — designation of `AgreementT1` + `CompletionWitness`**
  (`proofs/GoLeanProofs/Specs/RaftAgreement.lean`; constitution §3.2 —
  the walker list is Mike's act; the aboutness sentence is the file's
  docstring).
- **POSED — Arc 1 merge + its audit ask** (branch-complete, gate
  PASS; proposal on Mike's return: a focused statement-adequacy
  review — the D3-dimension — over the Arc-1 diff, Opus, plus the
  standing semantics dimension; scale ~2 reviewers).
- Arc 3 merge (will be posed at its branch-complete; the ci
  comparator-landmark staleness note on that lane is flagged for the
  operator's merge step).

## Judgment calls

- **[USER]** 2026-08-22: campaign launched; constitution is the scope.
- **[AGENT]** 2026-08-22: Q7 operative reading (above).
- **[AGENT]** 2026-08-22: Arc ladder as above; Arc 1 opens
  immediately on the `campaign` branch (statement work is
  supervised-class — it stays on-branch, merge-gated, so supervision
  is preserved by the merge gate itself).
