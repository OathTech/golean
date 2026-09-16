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
   `seqConsumption` arm, eleven `Step` rules (`unseqEnter`, `unseqPick`,
   `unseqComplete`, `unseqRunEval/Invoke/Load/Target/Guard`, `unseqValue`,
   `unseqStmtDone`) and the three `stepFn` arms (`stepUnseqEnter`,
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
   the census records**. `Tests/UnseqScheduler.lean` (47 checks; library
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

## 3. The mechanism theorem — statements, what is proved, what is owed

The wire scheduler theorem (v2.1 §7(b), review §4): SOUNDNESS over the
executed occurrence TRACE — a successful trace completes the active graph in
an order respecting every edge; an escaping panic is a legal prefix ending at
that failure with no later effect — and COMPLETENESS — every legal finite
execution, the occurrences' own nondeterminism and choice consumption
included, is some tape's `stepFn` trajectory.

PROVED in Stage B (`GoLean/GoCore/UnseqSound.lean`, all audited: no sorry,
no axiom beyond the classical trio, no native decision):

- T1 `unseq_pick_ready` — a pick transition selects an element of
  `UnseqGraph.ready` (every edge respected at the pick: value dependencies
  produced, order prerequisites discharged, region enabled).
- T2 `unseq_pick_active` — a picked occurrence is ACTIVE and in range (no
  double execution: completed occurrences are DONE or SKIPPED, never ready).
- T3 `unseq_panic_drops_frame` — a panic reaching the sweep frame continues
  below it over the UNCHANGED state (frame, binders, pending work dropped;
  the effect prefix stands) — the failure prefix half.
- T4 `unseq_complete_settled` — the completion step fires only with every
  occurrence settled and hands EXACTLY the graph's stores to the phase-2
  spine — the «completes the active graph» half.
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
  operand shape), invalid branch join STATICALLY (the machine refuses it
  dynamically, `skippedDep?`), list order a linear extension, nested `unseq`,
  `recover` in a head. The emitter (`tools/nativefrontend`): one sweep →
  one `unseq` node or the legacy probe lowering, never a mixture (§3.7).
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

The branch is complete at the records commit that follows `c770c59c` (records). At the merge:

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

## 8. Audit ask (posed; scope and waiver are the user's)

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
