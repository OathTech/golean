# Stage B handoff — the `unseq` scheduler on hand-built graphs (lane `core/unseq-scheduler-b-0916`, 2026-09-16)

[AGENT] Lane handoff (worker), branch `core/unseq-scheduler-b-0916` off main
`32398203`, worktree `.claude/worktrees/unseq-stage-b`. Design of record:
`docs/2026-09-16_evaluation-order-model-v2.md` (v2.1) — §3 the construct,
§7 row B this stage's exit evidence; second review
`docs/2026-09-16_evaluation-order-model-v2-review.md` (R1–R6, §2 row B, §4
proof obligations). Authority: [USER] Mike 2026-09-16, verbatim, relayed by
the [AGENT] coordinator — cite as relayed: «Great, merge it, then execute on
the planned work» (of the v2.1 plan); the reading that Stage B proceeds now,
before B7 (the note's N4 recommendation), is the coordinator's [AGENT]. The
mechanism ruling: [USER] 2026-09-16 «I think the Cerberus model is the
correct one» (`docs/2026-08-31_qrow-rulings.md`, «The evaluation-order
mechanism ruling record (2026-09-16)»). No [USER] gate was ruled by this
lane; the three PENDING items (width of P, N1 read granularity, N3 budget
refusal) stay PENDING — the design keeps both N1 shapes expressible (a header
read is an ordinary occurrence node: R6's SPLIT and FUSED graphs are both
tests). Evidence: `docs/evidence/2026-09-16_unseq-stage-b/README.md`.

## 1. What landed, per commit (each gated; the gate lines are in the evidence README)

1. `306fb3ef` — **the core** [TRUST-SURFACE]. Syntax (`GoLean/GoCore/
   Syntax.lean`): `UnseqBody` (eval / load-through-frozen-target / invoke
   0–2 results / target plan / guard entry), `UnseqOcc` (name, body, ORDER
   prerequisites `after`, `region`), `UnseqGraph` (typed binder cells,
   occurrences in canonical rank order, phase-2 stores), `Stmt.unseq g
   thenB`. Scheduler (`GoLean/GoCore/Unseq.lean`, pure): `Expr.names`
   (value dependencies IMPLIED by slot mentions), THE one `ready`
   (`UnseqGraph.ready`), `skippedDep?`, `skipRegion`, `wellFormed?`, the
   readiness lemmas. Machine (`Machine.lean`/`StepFn.lean`): `Cont.unseqK g
   thenB status targets env phase k` (`FrameClass.exprGlue`), the helpers
   (`unseqAtom`, `unseqCellLoc`, `unseqLookupTarget`, `unseqReadTarget`,
   `unseqLoad`, `unseqAtoms`, `unseqTargetPlan`, `unseqGuard`,
   `unseqStorePlan`, `unseqInvokeStmt`), `consumesUnseqNext`, the
   `seqConsumption` arm, TEN `Step` rules (`unseqEnter`, `unseqPick`,
   `unseqComplete`, `unseqRunEval/Invoke/Load/Target/Guard`, `unseqValue`,
   `unseqStmtDone` — «eleven» in the first version of this handoff counted
   the legacy `unseqProbe`; audit R3) and the three `stepFn` arms (`stepUnseqEnter`,
   `stepUnseqNext`, `stepUnseqValue`). `ChoiceSite.unseqNext` + its
   `canonicalSlot0` row + the census entry (`State.lean`). Coherence:
   `stepFn_sound`, `step_complete`, `step_complete_any_wf`,
   `step_preserves_wf` (StateWf: sup arms + loc lemmas for every helper),
   `stepFn_consumption_none/some`, `seqConsumption_none_of_flags`,
   `stepFn_oblivious`, `allStreamsOk` (all extended, all green); structural
   equality (`UnseqGraph.eqbF`, `Cont.eqbF` + soundness), `AdmissionIndices`,
   race footprint (`Race.unseqRunAccesses`), `ChoiceTrace` (`siteName`,
   `allSites`, `unseqNextFacts`), the CLI lockstep row 10; the dedup engine
   REJECTS the new site by name (`EnumDedupCheck.innerVecs`,
   `MultiStreams.poolThreadOblivious`, `EnumDedup.refusalReason`). Legacy
   `Stmt.unseqProbe`/`Cont.probeK`/`ChoiceSite.unseqPanic` untouched
   (coexistence; removal is Stage E). No wire, no decoder, no baseline.
2. `c770c59c` — **the tests, the gate step, the mechanism theorem's lemmas,
   the census records**. `Tests/UnseqScheduler.lean` (47 checks; 64 after
   the audit fix round, §9; library
   `UnseqSchedulerTests`, registry key `unseq-scheduler`, named `scripts/ci`
   step via `scripts/check-unseq-scheduler`, per the typed-test-gates
   landing pattern), `Tests/UnseqSchedulerAudit.lean` (24 required theorems;
   the whole local import closure on the classical trio only),
   `GoLean/GoCore/UnseqSound.lean` (T1–T6, §3 below), `UnseqGraph.wellFormed?`
   gains the «unknown slot» check (`$`-prefixed names are slots by the
   frontend's reservation), the latitude inventory §0 census row and the
   nondeterminism doctrine's reader's-mirror entry for `unseqNext` (the
   reconciler's C12 is green again).
3. the records commit that follows `c770c59c` — **records**: this handoff and the evidence README (docs only;
   the records checks `check-evidence-size`, `check-agents-alias`, `git diff
   --check` run at that commit).

## 2. Representation choices taken ([AGENT]) and the alternatives named

| choice | taken | alternative (not taken) | why |
|---|---|---|---|
| «produced» | DERIVED: a binder is produced iff its producing occurrence is DONE (`UnseqGraph.produced`); ONE status array | an explicit assignment bitmap beside the statuses (v2.1 §3.3's prototype text) | one array, one invariant; the guard's skip sets the completion cell and marks its occurrence DONE, so the join is still the only producer |
| cell scope | the cells are declared into the SOURCE scope at ENTER by the `.initialization` idiom (the enclosing `.seq` frame's env is extended in place, `allocDecls`); `thenB` runs in that scope; the cells fall out of scope with the enclosing block (C4 reclaims) | a pushed disposable cell scope with a SLOT-FREE `thenB` (stores driven by the scheduler only) | v2.1 §3.3's `x := a + f()` lowers to `thenB = .initialization x; x = $u`, which must SEE the binders and extend the source scope — only the shared-scope idiom gives both; consequence: `Stmt.unseq` requires the statement-sequence position `.initialization` requires (refused by name otherwise) |
| phases | three: `.pick` (schedule), `.run i` (the picked occurrence starts — its race footprint is known from the configuration), `.wait i` (value / statement completion awaited); ONE frame constructor | a two-frame shape (`unseqK` + `unseqOccK i`) or a one-phase pick-and-run step | one constructor = one arm in every walk/sup/eqb; the run step's footprint (`Race.stepAccesses`) must not depend on the stream |
| target operands | ATOMS only (`unseqAtom`: a slot `.var`, an admitted local `.var`, `.ref` of a local, an int/bool constant), resolved in ONE step through the machine's own `targetPlan`/`completeTargetRef`; a `TargetRef` whose anchor is the frozen header VALUE never re-reads the variable (R4) | operand evaluation through an evaluation frame (`tgtOpK` cannot be reused: its completion routes to `rhsK`/`storeK`) | the normal form (§3.1) says operands are constants/admitted reads/slots; the atom evaluator is 12 lines with a locSup lemma |
| phase 2 | REUSES the existing `storeK` spine (one store per step, each store's check at the store) from `unseqStorePlan` | a scheduler-driven store loop | X1's «first store persists when the second panics» is the spine's existing pinned behaviour |
| invocation body | `Stmt.callValue` with the binder cells as TARGETS (`unseqInvokeStmt`): the results are WRITTEN into predeclared destinations by the call's own phase-2 stores; completion = `.next` at `.wait i` | a value-returning invocation frame | «event bodies write predeclared result destinations, never `.initialization`» (§3.3), no new frame |
| receive occurrences | NOT a body kind in Stage B: X3's `<-ch` is an invocation of a closure whose body receives; a blocked receive is the callee frame's `blockedRecv` → the pool's deadlock → `explore` REFUSES by name («deadlock member … fail loud») — `blocked` stays a refusal apart from the members (X3e) | a `recv` body kind | the fragment as briefed (invocation of a function value); comma-ok receive is deferred to E by the matrix |
| map-element target plans | REFUSED by name in `unseqReadTarget` («frozen map-element plan (Stage E)») | frozen `mapElem` reads | the acceptance matrix defers map/pointer to E; pointer redirection IS covered (a frozen `.addr` anchor) |
| frozen state readout | X3's `len(ch)` is read by a DEFERRED `println` on the panic path | a state-carrying observation | the observation projection is (output, status, panic text); the defer makes the reference's frozen state observable without a new observable |
| unknown slot | a `$`-prefixed mention that is neither a cell nor a target binder is refused by name | treat every non-cell as an admitted source local (run-time `.stuck` at the unbound name) | the frontend reserves `$` for temps/binders; fail closed at ENTER, by name |
| positional proof cases | the three new `stepFn` arms are TAIL CALLS to `stepUnseqEnter/Next/Value`, each proved by its own lemma (`stepFrameExit_sound`'s pattern); the shifted positional tags of `stepFn_sound` and the two consumption theorems were REMAPPED (+1 at ≥ 66, +2 at ≥ 137, +3 at ≥ 152) from a `fun_cases` probe, not guessed | inline arms (many new positional cases) | keeps the fragile tags' churn to a computed renumbering; no proof refactor bundled |
| `Step` rule inventory (audit R4) | TEN rules (the list in §1 item 1); NO malformed rule — refusals are not steps: case (iii), `skippedDep?`, `unproducedConsumer?` (fix round F1), `unseqUnfrozenPlan?` (fix round F2) and `wellFormed?` are `stepFn`'s named refusals with no `Step` | the design §3.7's `unseqTargetDone` (a separate done rule) and `unseqMalformed` (a refusal as a step) | a target plan is ONE step (`unseqRunTarget` resolves and marks DONE together); a refusal that were a `Step` would make a malformed graph's «execution» a legal trace; the design §3.7 carries a dated addendum withdrawing the two names |

## 3. The mechanism theorem — statements, what is proved, what is owed

The wire scheduler theorem (v2.1 §7(b), review §4): SOUNDNESS over the
executed occurrence TRACE — a successful trace completes the active graph in
an order respecting every edge; an escaping panic is a legal prefix ending at
that failure with no later effect — and COMPLETENESS — every legal finite
execution, the occurrences' own nondeterminism and choice consumption
included, is some tape's `stepFn` trajectory.

PROVED in Stage B (`GoLean/GoCore/UnseqSound.lean`, all audited: no sorry,
no axiom beyond the classical trio, no native decision). WHAT THESE ARE
(audit R1, worded honestly): T1–T6 are INVERSION LEMMAS over the rules'
own premises — each pins what one scheduler step's shape guarantees. None
constrains `UnseqGraph.ready` against §1's edge table: a wrong `ready`
(one ignoring `after`, say) would leave T1–T6 provable unchanged. That
weight is TEST-BORNE — the exact-set reference tests
(`Tests/UnseqScheduler.lean`, every witness of `outcomes.txt` plus the
audit's twelve graphs and this fix round's) — pending a machine-checked
statement of «trace» (owed below); Stage C's check (b) is the other
independent leg.

- T1 `unseq_pick_ready` — a pick transition selects an element of
  `UnseqGraph.ready` (the inversion of `unseqPick` over its own premise;
  true BY DEFINITION of `readyAt`). That `readyAt` encodes §1's two edge
  sorts — value dependencies produced (producer DONE), order prerequisites
  discharged (DONE or SKIPPED), region enabled (guard DONE) — is not a
  theorem here; it is what the reference-set tests check.
- T2 `unseq_pick_active` — a picked occurrence is ACTIVE and in range (no
  double execution: completed occurrences are DONE or SKIPPED, never ready).
- T3 `unseq_panic_drops_frame` — a panic reaching the sweep frame continues
  below it over the UNCHANGED state (frame, binders, pending work dropped;
  the effect prefix stands) — the failure prefix half.
- T4 `unseq_complete_settled` — the completion step fires only with every
  occurrence settled, with every binder its stores and its completion
  statement consume PRODUCED (`UnseqGraph.unproducedConsumer? st thenB =
  none` — the conjunct added by the fix round, F1), and hands EXACTLY the
  graph's stores to the phase-2 spine — the «completes the active graph»
  half.
- T5 `unseq_record_stable` — graph, completion statement, scope and tail are
  invariant along the scheduler's own steps (freshness: cells allocated
  once at ENTER).
- T6 `unseq_done_permanent` — DONE is permanent along the scheduler's own
  steps, the guard's region skip included (with T2: an occurrence runs at
  most once per sweep).
- Step-level completeness at every stream: `step_complete` (the pick for
  EVERY ready `j` realized by the tape `[j]` — at bound ≥ 2 the slot `j`,
  at bound 1 the forced slot) and `step_complete_any_wf`; the consumption
  theorems: the pick DRAWS `unseqNext` at bound `|ready|` exactly and
  depends on the stream only through the pick; ENTER, run, wait and the
  value delivery are stream-oblivious.
- The readiness interfaces: `UnseqGraph.ready_active`, `allSettled_false`,
  `ready_nil_of_allSettled`.

OWED (recorded, not claimed):

- The MULTI-STEP composition: every `Steps` execution of a sweep from ENTER
  to the `storeK` hand-off projects to a legal run (the occurrence bodies'
  internal steps — an `.evalE` head, a callee's frames — pass through
  non-sweep configurations and must be shown to preserve the frame's record
  and return to the pick position; T5/T6 are stated over the scheduler's
  own steps only).
- Multi-step completeness: a legal finite run's tape is the CONCATENATION of
  the per-step tapes; MachineSound has no stream-composition lemma over
  `Steps` yet (each step's witness is separate).
- A machine-checked statement of «trace» itself (the per-sweep projection of
  `Steps`) — the T-lemmas are its interfaces; the definition is prose here.
- The source-to-wire translation certificate (v2.1 §7(a)) — separate,
  Stage C's.

## 4. Budgets (route β; the certified dedup engine is not extended)

Headline (evidence README tables): a loop of N sweeps with ONE width-2 pick
each explores exactly 2^N paths on the default DFS explorer; with SILENT
events the member set is a singleton while paths still double (N=8: 256
paths, 36 503 steps, 2.8 s in-process, ~760 MB RSS dominated by olean
loading); with printing events every path is a distinct member. The
recursion witness (four nested activations, three-way-unordered sweeps): 10
000 leaves for one outcome. Unique-state counts are route α's metric; the
dedup engine refuses `unseqNext` by name today
(`GoLean/GoCore/EnumDedupCheck.lean` `innerVecs`, `EnumDedupSound.lean`'s
matching case, `GoLean/EnumDedup.lean:refusalReason`,
`MultiStreams.poolThreadOblivious`). [AGENT] reading for Stage D: the
outcome-equivalent product is real and exponential in the number of sweeps
on the DFS path; route α (branch-vector construction for the pick + its
checker/soundness arms) is the lever, per v2.1 §3.6.

## 5. Stage C's entry point

- FRAGMENT to lower first: exactly `UnseqBody`'s five kinds over int/bool
  locals and globals, slices of ints, closures/top-level functions with 0–2
  results; `&&`/`||` as guard + completion nodes; `+=` on `a[i]` as header
  producer + index producer + target plan + load + op + store; `x := e` as
  `thenB = .initialization x; x = $u`; `println` in `thenB`. Receives,
  comma-ok, map-element targets, `recover` inside a sweep: refuse at the
  boundary (Stage E), as the tests already do for the map plan.
- ADAPTERS = the decoder (`GoLean/NativeToIR.lean`): a wire node
  `{"stmt":"unseq", "cells":[…], "occ":[…], "stores":[…], "then":…}` →
  `Stmt.unseq`; the v2.1 §3.1 decoder checks are `UnseqGraph.wellFormed?`
  (already: duplicate result, sort mismatch, unknown reference/slot, guard
  completion outside its region, unproduced cell, >2 results) PLUS the
  decoder's own: hidden read in a pure node (operands of a head are atoms —
  `unseqAtom`'s grammar for targets; for heads the decoder must check the
  operand shape), invalid branch join STATICALLY — for occurrence bodies
  AND for `thenB`/the stores: «`thenB` and the stores mention only cells
  whose producer is outside every region, or a guard's completion binder
  visible at that level» (the machine refuses the DYNAMIC form by name:
  `skippedDep?` for bodies, `unproducedConsumer?` for the completion's
  consumers — fix round F1; the static check is defence in depth, not a
  substitute), the frozen-anchor shape («never emit `&a` as the anchor of a
  slice-element plan; the header comes through a binder or a read at the
  plan step» — the machine refuses the unfrozen shape dynamically,
  `unseqUnfrozenPlan?`, fix round F2), the `$` reservation on every binder
  (machine: `wellFormed?`, fix round F3), list order a linear extension,
  nested `unseq`, `recover` in a head. The emitter (`tools/nativefrontend`):
  one sweep → one `unseq` node or the legacy probe lowering, never a mixture
  (§3.7) — the machine does NOT enforce this boundary (audit N2: a legacy
  `unseqProbe` inside `thenB` is accepted); the emitter is the enforcing
  side (§9).
- The machine-side seams Stage C will touch: `unseqAtom` (if constants
  beyond int/bool are needed), `unseqReadTarget` (map plans, Stage E),
  `Race.unseqRunAccesses` (any new head kind must report its footprint).
- Exit check (b): the lowered machine's `explore` set = the reference set,
  EXACTLY, on the same witnesses — `Tests/UnseqScheduler.lean`'s harness
  (`expectSet`) is reusable on decoded programs.

## 6. PENDING [USER] (not decided here)

- Width of P (v2.1 §5 item 2) — [AGENT] recommends (ii); Stage B's graphs
  are hand-built, so W1/W6/R1/R6 are exercised without deciding it.
- N1 read granularity (§5 item 5) — both shapes are expressible and tested
  (R6 SPLIT {10, 20} vs FUSED {20}); a FUSED choice would be a NARROWING to
  be recorded everywhere.
- N3 enumeration budget refusal (§5 item 7) — the DFS product measured above
  is the input; [AGENT] recommends refuse + measure.
- Ratification at the merge ask: §5 items 1/4/6 (value axis, E3/E4, canonical
  order = today's emission order — slot 0 = lowest rank).

## 7. The merge train's next command

The branch is complete at the records commit that follows the fix round's
runtime commit `920a11c6` (Stage B: `306fb3ef` core, `c770c59c` tests +
wiring, `ba8767da` records; audit fix round, §9: `920a11c6` runtime + the
records commit that follows it). At the merge:

    git checkout main && git merge --ff-only core/unseq-scheduler-b-0916

5a IS OWED: compiled semantic inputs changed (the certificate provenance
step reports STALE — «changed dependency build/files/GoLean/CLI.lean», and
every GoCore module), so at the merged tip the train runs
`scripts/build-certified`, `python3 tools/certification.py release-check
--base refs/snapshots/<round>/main`, then `scripts/capped scripts/ci --slow`
and installs the reviewed `certification-candidate.json` as
`baselines/certified/<case>.certified.json` (the round's 5a records commit).
Gate 2 (`ci --slow`) re-enumerated the one tier=slow row on this branch —
see the evidence README for whether the certified SET was identical (then
the 5a step is a header/inventory refresh) or moved (then it is a FINDING,
not a re-pin). No wire file changed on this branch.

## 8. Audit ask (posed 2026-09-16; ANSWERED — FIX-FIRST, `docs/2026-09-16_unseq-stage-b-audit.md`; the fix round is §9; the RE-VERIFICATION ask is §9.6)

- The `ready` definition against v2.1 §1's edge sorts: value deps produced
  (producer DONE), order prerequisites discharged by DONE or SKIPPED, region
  enabled by its guard's DONE; the guard's skip protocol (`unseqGuard` +
  `skipRegion`: nested regions, the completion set DONE, never SKIPPED).
- The cell-scope idiom (source-scope declaration by env rewrite) against
  the `.initialization` rule it copies; binder lifetime (W5, recursion).
- The atom evaluator's grammar vs the §3.1 normal form; the frozen target
  identity (R4/pointer/cell tests) vs `resolveChain`'s replay.
- The renumbering of the positional proof cases (the probe's mapping).
- The consumption arm's EXACT bound (`(g.ready st).length` at ≥ 2) vs the
  scheduler's consult; the dedup-engine refusal path.

## 9. Audit fix round (2026-09-16)

[AGENT] Fix-round worker, same branch, worktree `.claude/worktrees/unseq-
stage-b`, base = the records commit `ba8767da`. Authority: the adversarial
audit ordered by [USER] Mike 2026-09-16 («Great, send off an auditor as
proposed», verbatim, relayed by the [AGENT] coordinator — cite as relayed)
returned **FIX-FIRST** (`docs/2026-09-16_unseq-stage-b-audit.md`, branch
`review/unseq-stage-b-0916` @ `2440278d`; its scratch graphs under
`docs/evidence/2026-09-16_unseq-stage-b-audit/` there). No [USER] gate was
ruled in this round; the PENDING list (§6) is unchanged.

### 9.1 Disposition of the auditor's «may instead be recorded as Stage C obligations — PENDING [USER]» ([AGENT] coordinator; the charter answers it)

The auditor offered, for F1 and F2, the alternative of RECORDING them as
Stage C decoder checks and merging as-is. The coordinator's [AGENT]
disposition, recorded here: F1/F2/F3 are FAIL-OPEN paths in the trusted core
(`GoLean/GoCore/`), and the charter's doctrine («Fail closed, always … an
explicit refusal that NAMES ITS CAUSE at the point of failure, never a silent
default, never an absorbing fallback») requires the refusal IN THE MACHINE:
hand-built graphs — the tests', the auditor's, any future spike's — bypass
the decoder entirely, so a decoder check cannot be the enforcement; it is
defence in depth (recorded in §5 as such). The auditor's PENDING [USER] item
is therefore answered by the charter, not by a new ruling; nothing is
adjudicated here that is the user's.

### 9.2 F1–F3 — what changed, where, the refusal texts (each landed with its `Step` premise, its `stepFn` arm and the coherence cases in ONE commit)

- **F1 — a SKIPPED producer's VALUE binder is never consumed as a value.**
  `UnseqGraph.unproducedConsumer? g st thenB` (`GoLean/GoCore/Unseq.lean`):
  at completion every VALUE binder a phase-2 store reads and every binder
  cell `thenB` mentions must be PRODUCED (`produced` = producer DONE). The
  `thenB` mentions come from a NEW total walk `Stmt.names` (with
  `stmtListNames`/`selectNames`/`optStmtNames`, `assigneeListNames`,
  `selectHeadNames`, `unseqGraphNames` — the constructor list mirrors
  `Admission.stmtIndices`, no catch-all); before it the machine had no `Stmt`
  name walk, which is why the audit's A5 read the zero silently. NEW premise
  `g.unproducedConsumer? st thenB = none` on `Step.unseqComplete`
  (`Machine.lean`); `stepUnseqNext`'s case (i) checks it BEFORE
  `unseqStorePlan` and throws `.stuck msg` (`StepFn.lean`). Coherence:
  `stepUnseqNext_sound`, `stepUnseqNext_consumption_none` (an extra `split`
  each), `step_complete`, `step_complete_any_wf_aux`, `step_preserves_wf`'s
  `unseqComplete` case (`hprod` named), T4 `unseq_complete_settled` gains the
  conjunct. Texts (captured on the canonical tape,
  `docs/evidence/2026-09-16_unseq-stage-b/fix-round-refusals.txt`):
  «`unseq: the phase-2 store into '$t' reads binder '$h', which was not
  produced — its producer 'E_h' was SKIPPED (confined to a disabled region);
  the completion binder is the only join — malformed graph`» (A4) and
  «`unseq: the completion statement reads binder '$h', which was not produced
  — …`» (A5). Tests: A4/A5 refuse by name (z=true), their z=false controls
  give `h ran / out 42` and `h ran / h 42`, and the LEGITIMATE join —
  `thenB` reading the skipped region's completion binder `$cor` — still
  works (`c true`); A8 (target binder from a skipped region) still refuses
  («has not been produced»). The STATIC form of §1 G stays the decoder's
  (§5): the machine refuses the dynamic instance at the point of failure.
- **F2 — a target plan anchored at the ADDRESS of a slice variable is
  refused (the header is not frozen).** `unseqUnfrozenAnchor? s anchor steps
  idxs` / `unseqUnfrozenPlan? s r` (`Machine.lean`, before
  `unseqTargetPlan`): a dry walk of the completed chain's SHAPE at plan time
  — an `.index` step on an `.addr loc` whose cell holds a `.slice` is refused
  by name (the header would be re-read by `indexTargetLoc` at the checked
  load AND at the phase-2 store — the reference's forbidden hybrid); the walk
  continues through `.field` steps and through array elements (`.array` →
  `.index loc n`) and frozen headers (`.slice` → `sliceIndexLoc`) so nested
  shapes (`s.f[i]`, `a[i][j]`) are covered; a step it cannot see through
  ends the walk with NO refusal (a plan checks nothing — bounds/nil stay in
  phase 2). Wired into `unseqTargetPlan` after `completeTargetRef`; the rule
  premise `unseqTargetPlan s env lhs = .ok r` carries it for free;
  `unseqTargetPlan_locSup` (StateWf) gains one `split`. Text: «`unseq: target
  plan indexes a SLICE VARIABLE through its address (GoLean.Loc.base { id :=
  0 }) — the header would be re-read at the load and again at the store, not
  frozen; freeze the header VALUE through a binder`». Tests: the audit's C1
  (`.ref "a"` anchor) refuses; C1b (the header READ at the plan step, `.var
  "a"`) gives R4's exact set {`old 11 20 / a 100 200`, `old 10 20 / a 101
  200`}; the R4 witness itself stays exact; an ARRAY variable's address
  (`.ref "arr"`, arrays do not rebind) is accepted (`arr 11 20`); the pointer-
  redirection and cell-mutation tests are unchanged (both writes observable,
  no hybrid); the map plan stays Stage E's refusal.
- **F3 — every binder carries the `$` reservation.** `wellFormed?` refuses,
  right after the distinctness checks, any cell or target binder not
  starting with `$`: «`unseq: malformed graph — binder 'a' is not a reserved
  `$` slot name (every binder cell and target binder is `$`-prefixed — the
  frontend's reservation; a bare name would shadow the source local 'a' for
  the rest of the block)`». Refusals produce no step: no proof change.
  Tests: the audit's B4 (cell `a` shadowing the source local `a`) and a bare
  target binder `t` both refuse by name; every pre-existing test already
  used `$` names (all 47 stay green).

### 9.3 N2 / N3

- **N3 (done):** `wellFormed?` checks the guard's test AND completion cells
  are `bool` cells (the skip STORES the short-circuit constant, a bool):
  «`guard 'G' completion '$cor' is a cell of type GoLean.GoCore.Ty.int
  (GoLean.GoCore.IntKind.int), not a bool cell (the skip stores the
  short-circuit constant, a bool)`» and «`guard 'G' tests '$z', a cell of type
  …, not a bool cell`» — at ENTER, by name, instead of the run-time generic
  `stuck: expected int value, got …bool true`. Tests: the audit's K4 and the
  test-cell variant.
- **N2 (OWED, not done):** the whole-sweep migration boundary (§3.7 — one
  sweep is either one `unseq` node or the legacy probe lowering, never a
  mixture) is NOT machine-enforced: a `.unseqProbe` inside `thenB` is
  accepted (audit K1). A `wellFormed?`-level refusal would need a second
  total `Stmt` traversal («contains a probe») beside `Stmt.names` — not a
  few lines; the ENFORCING side is the emitter (`tools/nativefrontend`, one
  lowering per sweep), with the decoder's nested-`unseq` check as its
  neighbour (§5). Recorded here and in §5; Stage C's brief inherits it.

### 9.4 R1–R6 (records)

- R1: §3 reworded — T1–T6 are inversion lemmas over the rules' own
  premises; T1 is true by definition of `readyAt`; `ready`'s fidelity to §1
  is test-borne (the exact-set tests), not a theorem.
- R2: the TRACKED reference enumerator
  (`docs/evidence/2026-09-16_eval-order-v2-spike/enumerate.py`) now walks
  EVERY unsettled occurrence for the invalid-join check (§1 G is static) and
  carries the A3 witness as a named refusal; re-run EXIT=0; `outcomes.txt`
  regenerated — one line added, every other line byte-identical; its README
  has the dated amendment. The machine-side regression is this file's A3
  check («confined to a skipped region»).
- R3: TEN `Step` rules everywhere (§1 item 1, the evidence README); «eleven»
  had counted the legacy `unseqProbe`.
- R4: the design §3.7 carries a dated addendum mapping its `unseqTargetDone`/
  `unseqMalformed` to the candidate's ten rules (no separate done rule; no
  malformed rule — refusals are not steps); mirrored in §2's inventory row.
- R5: the headline lowering `x := e ↦ .initialization x; x = $op` in `thenB`
  is now tested — K2 (mid-block, two sweeps, `x 3 / x y 3 12`) and K3 (loop
  body, fresh `x` per iteration, `x 3 / x 4`).
- R6: this round's gate tail of record INCLUDES the drift block
  (`docs/evidence/2026-09-16_unseq-stage-b/gate3-tail.txt`).

### 9.5 Proved vs owed — what moved

- T4 `unseq_complete_settled`'s statement gained the conjunct
  `g.unproducedConsumer? st thenB = none` (an inversion of the new premise);
  no other theorem's statement changed; the 24 required theorems of
  `Tests/UnseqSchedulerAudit.lean` are unchanged by name and the post-import
  audit is still the classical trio only (14 444 declarations after the
  round, from 14 376).
- Nothing moved from OWED to PROVED: the multi-step composition, the
  stream-composition lemma, the machine-checked «trace», the translation
  certificate stay owed (§3). NEW owed (records): N2 above (emitter-side).
- Positional proof tags: unchanged — the three arms are tail calls, so the
  new `split`s live inside `stepUnseqNext_sound`/`_consumption_none`; no
  `fun_cases` probe was needed and no tag was remapped.

### 9.6 Gate and the re-verification ask

Gate lines (captured exits; details and the drift block in the evidence
README's `gate3-tail.txt`, `fix-round-unseq-gate-tail.txt`,
`fix-round-refusals.txt`): sequential warm build of the six edited modules,
every module EXIT=0 (Unseq; Machine 4 s; StepFn 17 s incl. StateWf 16 s;
MachineSound 57 s; UnseqSound); `scripts/capped scripts/check-unseq-scheduler`
EXIT=0, 94 s, 64 checks ok / 0 FAIL, audit classical trio only; `scripts/
capped scripts/ci --diff` under the box-wide lock EXIT=1, 1176 s — 3676 rows
3427 PASS / 249 expected FAIL, 394 negatives, 211 eval tests, the `unseq
scheduler (Stage B)` step ok, red = EXACTLY the two 5a-class items
(`certificate provenance` STALE — «changed dependency
build/files/GoLean/CLI.lean», compiled inputs changed — and, in consequence,
the one certified row `imported-goose/channel/google-search`
PASS→FAIL/membership, the single drift line); no other row moved;
reconciler C9 (the same stale certification) + C13 (pre-existing doc
Go-version sites), report-only. Records checks: `check-bugs.sh` 0,
`check-spec-anchors` 0, `check-evidence-size` 0, `check-agents-alias` 0,
`git diff --check` 0. 5a stays OWED to the train as §7 says.
Re-verification ask for the auditor
(scope and waiver the user's): re-run its A4, A5 (both z), A3, B4, C1, C1b,
K4 graphs and K1 (unchanged: accepted — N2 owed) against this branch's tip
— each of A4/A5/B4/C1/K4 must now be a NAMED refusal with the texts in
§9.2/§9.3, C1b must give R4's exact set, A5's `$cor` variant must print `c
true`; plus its `enum_audit.py` against the amended `enumerate.py` (A3 now
refuses on both sides; A1/I1–I4b unchanged).
