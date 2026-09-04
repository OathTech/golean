# Wave (iii) — B2 + B3 + B8: design note and preservation arguments (2026-09-04)

Status: BRANCH-COMPLETE on `hygiene-wave3` (2026-09-04; not merged — audit-ask pending) (design-hygiene arc step (iii);
plan `docs/2026-09-03_design-hygiene-arc.md`; source proposals
`docs/2026-09-03_grumpy-professor-review.md` §3(b) B2, B3, B8 and §3(a)
A7 (folded in here per the A-series note §A7)). Provenance: [AGENT]
execution inside the [USER]-ratified arc (Mike, 2026-09-03, relayed by
the [AGENT] coordinator, not firsthand: «Great, let's do it as you
propose … our aim is to get the *nicest* faithful go semantics»); every
design choice below is [AGENT] unless marked. Evidence dir:
`docs/evidence/2026-09-04_hygiene-wave3/`. Template: the A-series note.

Conventions (review §3): "preserving" = for every program, stream and
fuel the same `Except Stop Readout` (constructor, message, readout), and
the choice tape consumed at the same sites with the same bounds in the
same order. Each item is ONE checkpoint commit gated by the full
`scripts/capped scripts/ci --diff` at ZERO baseline drift (3365 rows) and
by the whole-corpus labeled-consumption trace at ZERO delta against the
pre-wave snapshot — since this wave the trace is compared PER
CONSUMPTION (the tracer's new `--dump`: id, stream, idx, phase, site,
bound, streamValue, pick), not only per (row, stream) aggregate.

## The theorem shape downstream quantifies (A1 + B2 together)

A run of either driver ends in exactly one of: `.ok (readout)`, `.error
(.terminal t)` for `t : Terminal` (panic / fatal / deadlock /
raceDetected), `.error (.refusal r)`, or `.error .fuelOut`. Inside the
machine a Go panic has ONE intermediate carrier — `Result.panic msg` at
the apply boundary (`toResult`) — and ONE control form — `.panicking
chain k`, entered only through `deliver`; the terminal `.panicked msg`
is what the driver reports as `.terminal (.panic msg)`. A downstream
`to_val`-style projection is therefore `Result`/`Terminal`-typed with no
hand-picked `Stop` subset, and `Obs := ok values | terminal Terminal` is
the enumeration lane's whole vocabulary.

## B2 — `Result` at the apply boundary; ONE `deliver`; the twins gone

**Recorded deviation from the review's sketch (cost-driven, [AGENT]).**
The review routed `Result` THROUGH the helpers (`Except Refusal (Result
α)` everywhere). Measured before deciding: `Except Stop` occurrences —
Ops 79, Machine 38, MachineSound 34, Multi 23, StepFn 15, StateWf 12,
State 11 — i.e. every helper signature and every helper lemma
(`exceptCong`-family, the `applyStmtOp_*_any_ch` kit, the `*_wf`
lemmas) would move for the same ONE classification. So the boundary is
where `Result` lives: helpers keep `Except Stop` and raise `.panic` as
before; the apply/entry site classifies once.

**What changed.**
- `Result α := ok a | panic msg` and `toResult : Except Stop α → Except
  Stop (Result α)` (Value.lean, beside the stop grammar): `.ok ↦ .ok
  (.ok)`, `.error (.panic m) ↦ .ok (.panic m)`, every other stop
  unchanged. Simp/inversion family: `toResult_ok/_panic/_refusal/…`,
  `toResult_eq_ok_ok`, `toResult_eq_ok_panic`, `toResult_eq_error`,
  `toResult_cases`.
- `panicEntry msg := ⟨runtimeErrorValue msg, false⟩` (Machine.lean) —
  the one spelling of a fresh runtime-panic chain entry (formerly 41
  inline `⟨runtimeErrorValue msg, false⟩` sites: StepFn 15, Machine 25,
  Multi 3 → 0 inline; the in-helper channel panics, `commitClause`,
  `resumeThread`, the five nil-callee sites and the select
  interception spell `panicEntry`; `nilDerefPanicText` names gc's
  nil-dereference text once, Ops.lean).
- `deliver s k next r (chain := [])` (Machine.lean, after `Config`):
  `.ok a ↦ next a`; `.panic msg ↦ (.panicking (chain ++ [panicEntry
  msg]) k, s)` — the pre-apply state, exactly what every former
  conversion site built; `chain` is the suspended chain a PANIC-PATH
  deferred entry joins (audit F1+F5). The executable's `deliverS`
  (StepFn.lean) is the same delivery carrying the stream: success keeps
  the apply's own post-stream, a panic the pre-apply stream — today's
  every-site convention (`deliverS_deliver` projects it onto
  `deliver`). Recorded: TWO definitions for one delivery, because the
  relation is stream-free and the executable is not; the review's own
  sketch had the same pair (`deliver`/`deliverS`).
- `enterFramePick s fid args ch : Except Stop (Result (Func × LocalEnv ×
  List Loc × ExecState) × Choices)` — THE one stream-touching frame-entry
  funnel: classifies `enterFrame`, and on the panic path ONLY consults
  `nilValueMethodText` at `nilValueMethodWidth` (BUG-087: the two-member
  text set on the wrapper family; a bound-1 no-op elsewhere). It replaces
  `enterFrameStep` and `enterFrameDeferPanicking` (StepFn.lean) AND
  `spawnStep`'s hand copy of the pick (Multi.lean) — three funnels → one;
  the tape is consumed identically (`enterFramePick_cases`,
  `enterFramePick_of_none`, `_any_ch`).
- **The relation**: every apply/entry rule is ONE rule of the shape
  `toResult (apply …) = .ok r → deliver s k next r = (c', s') → Step c s
  c' s'` ("apply, then deliver"); the entry rules quantify the stream
  (`enterFramePick … ch = .ok (r, ch')`, the `stmtOpApply` idiom — the
  former free `pick` is the pick the quantified stream draws: on the
  family width 2, `{0, 1}` = the same two-member set). The 17 `*Panic`
  twins are DELETED: `evalStrictNullaryPanic`, `strictApplyPanic`,
  `stmtOpTargetPanic` (folded into `stmtOpShiftTarget`), `stmtOpApplyPanic`,
  `chanStApplyPanic`, `selectApplyPanic`, `syncStApplyPanic`,
  `atomicStApplyPanic`, `rhsStoresPanic`, `storeStepPanic`,
  `callImmediatePanic`, `callArgsDoneEnterPanic`, `callValCalleeEnterPanic`,
  `callValArgsEnterPanic`, `frameDeferFallEnterPanic`,
  `frameDeferReturnEnterPanic`, `panicFrameDeferEnterPanic` — 159 → 142
  rules. The five nil-callee rules stay (genuine behaviours). The
  `entryPanicStream`/`entryPanicText_entryPanicStream` witness pair is
  deleted with the twins (the rule's own `ch` is the witness now).
- `Obs := ok values | terminal Terminal` (EnumSpec.lean); `obsOf?` maps
  every `.error (.terminal t)` to `some (.terminal t)`. So `Obs.fatal`
  and deadlock are STATABLE (A1's owed payoff — closed). The ENGINE
  (`EnumDedup.nodeObs`) and the CHECKER (`checkEdge`/`checkNode`) are
  UNCHANGED in what they admit: panic and race members only; a fatal or
  deadlock member still refuses loudly (no lane behaviour change — a
  lane decision, not a type change). The completeness proof
  (`checkCert_complete_aux`) needed NO edit: every `.error` case was
  already refuted through the node check, never through `obsOf? =
  none`. `Terminal` derives `DecidableEq` (for `Obs.eqb`); the CLI's
  member status/JSON words are `Terminal.status`/`errorJson` on the
  terminal — byte-identical to the former per-constructor table.
- The driver readout `GoCore.Result` → `Readout` (State.lean; 13 refs:
  StepFn 5, Multi 2, CLI 2, Tests 3, State 1).

**Why nicer.** One panic representation on the helper side, one on the
control side, one function between them; the relation reads "apply,
then deliver" and every rule-indexed downstream lemma is written once.
Every frame entry in the machine — the seven `stepFn` positions and the
spawn — goes through one funnel with the one pick.

**Preservation.** `deliver` (and `deliverS`) is exactly what each of the
41 conversion sites did (`.panicking [⟨runtimeErrorValue msg, false⟩] k`
over the pre-apply state and pre-apply stream); `toResult` is a total
classification with `.ok`/`.panic` the two former arms and every other
stop propagated as before; `enterFramePick` performs the same
`consumeAt` on the same branch with the same width. Extensional equality
of `stepFn`; the relation's rule set is the same set of steps (the panic
twin's conclusion is the new rule's `.panic` case). Evidence: `ci --diff`
PASS 3365 = 3165/200, FULL 3365/3365 no regression, 0 flips
(`transcripts/gate-b2.txt`); whole-corpus trace vs the pre-wave snapshot:
aggregate DELTA 0 on 19963 (row, stream) lines and the per-consumption dump
byte-identical, 23665 records (`choice-trace/b2-diff.txt`).

**Proof deltas (arm for arm).** `step_preserves_wf_loc` (StateWf): the
16 apply/entry cases split on `toResult_cases`/`enterFramePick_cases`,
the panic branch closed by one macro (`wf_loc_panic`); `stepFn_sound`,
`step_complete`, `step_complete_any_wf_aux`, `stepFn_oblivious`
(MachineSound): re-tagged (positional `fun_cases` tags: 75 → 75 across
`stepFn_sound` + `stepFn_oblivious` at the B2 tip — the collapsed arms are
one `fun_cases` branch each instead of three, so `stepFn` has FEWER cases;
after B8 the count is 102 across `stepFn_sound` + the two consumption
sweeps that replace `stepFn_oblivious`'s body), the B2 arms closed by four macros (`deliver_arm`,
`entry_arm`, `oblivious_apply`, `oblivious_entry`) and two completeness
macros; `stepFn_selectApply_inv` and the select interception in
`stepMulti_sound`/`stepThread_single` (MultiSound), `spawnStep_wf` and
the select interception in `stepMulti_wf` (MultiWfSound),
`spawnStep_oblivious` (Multi) restated over `toResult`/`deliver`;
`Obs.eqb_sound` (EnumDedupSound) over `Terminal`'s `DecidableEq`. New
lemmas: `enterFramePick_ok/_panic/_error/_cases/_any_ch/_of_none/
_of_isSome_false`, `deliver_ok/_panic/_panic_eq`, `deliverS_ok/_panic/
_deliver`, `panicEntry_locSup`, `panicChainSup_panicEntry`. Deleted:
`entryPanicStream`, `entryPanicText_entryPanicStream`. No lemma weakened.

**Deferred, with reasons.** The helper-internal `Result` monad (above);
`GoValue.unit` removal (`atomicCompute`'s result plumbing — B4-adjacent,
A8's record stands); `Refusal.at`/a driver error type (A9's record).

## B3 — the `Cont` algebra (+ the A7 accessor)

**What changed** (Machine.lean, after `Cont`).
- `Cont.tail : Cont → Option Cont` (every frame but `.stop` has exactly
  one) and `Cont.withTail`; laws `sizeOf_tail_lt`, `withTail_tail`,
  `tail_withTail`.
- `FrameClass := stmtGlue | exprGlue | callFrame | resumeMarker | stop`
  and `Cont.class`; `Cont.isGlue`.
- `Cont.rebuild descend act k` — THE one continuation walk, well-founded
  on `sizeOf`: descend through the frames `descend` admits, act at the
  first it does not (or at `.stop`), rebuild the spine (`withTail`).
  Unfolding lemmas `rebuild_descend/_act/_stop`.
- The walks as instances: `pushDefer d` = rebuild through `stmtGlue`,
  act at a call frame (push); `recoverThroughWrappers` = rebuild through
  `recoverTransparent` (glue + wrapper frames), act at the marker
  (`markNewestRecovered`); `recoverResult` = rebuild through
  `recoverTransparent`, act at the first NON-wrapper frame (the inner
  walk) or answer `.nil`; `panicPassthrough k := if k.isGlue then k.tail
  else none`. Four 30-arm definitions (≈110 lines) → four 3–8-line
  instances.
- `Config.isTerminal` — the five terminal shapes named once; `threadDone
  c := c.isTerminal`; `Config.atBoundary c := c.isTerminal || …`; and
  (audit fix F4) NPDRF's `threadDone_atBoundary` proof goes through
  `isTerminal` instead of re-enumerating the shapes — THREE of the six
  terminal-shape enumeration sites (the first draft of this note said
  "two of eight"; the audit's census is six). The three that keep their
  own arms, each for its own reason: `execStmtLoop` and `mainOutcome?`
  need the OUTCOME behind the shape (which terminal, with what payload);
  `allStreamsOk` EXCLUDES `.panicked`, a shape `isTerminal` admits — not a
  shape/outcome distinction but a different predicate. `Config.terminal`
  (Prop) is unchanged: its only consumer is prose.
- A7: `Config.applyPos : Config → Option (ApplyHead × List GoValue ×
  LocalEnv × Cont)` — an ACCESSOR that decodes the `(v :: done).reverse`
  operand encoding for its ONE consumer, B8's `seqConsumption`. It does
  NOT make the encoding "spelled once" (the first draft of this note said
  it did — corrected by audit fix F3): the raw spelling stays at every
  executable and proof site (counts under "Not done" below), and
  `applyPos` ADDED eight spellings (its arms) plus three encoding
  theorems (`applyPos_stmt/_select/_sync`).

**Preservation (definitional, PROVED).** Each instance was proved EQUAL
to the retired 30-arm definition BEFORE the swap — `pushDefer'_eq`,
`recoverThroughWrappers'_eq`, `recoverResult'_eq` in
`b3-prototype/Proto.lean`, elaborated at `main` @ `aceb0dcb` (the walks
are unchanged between there and the B2 tip `91c57c9e`; transcript
`b3-prototype/proto-run.txt`); `panicPassthrough`'s 30 arms are the
class table by inspection (glue → `some tail`, the three non-glue heads
→ `none`). `threadDone`/`atBoundary` are the same Boolean functions
(the five arms moved into `isTerminal`). `applyPos` is additive.

**Proof deltas.** StateWf: `Cont.ownSup`, `locSup_withTail`,
`locSup_eq_own_tail`, `tail_locSup_le`, and the GENERIC
`Cont.rebuild_locSup` (strong induction on `sizeOf`; bounds the action's
payload and the rebuilt continuation at once) replace three per-walk
30-case inductions (`pushDefer_locSup`, `recoverThroughWrappers_locSup`,
`recoverResult_locSup` — same statements, ≈120 lines → ≈60 including the
generic lemma); `panicPassthrough_locSup` is `tail_locSup_le`. The five
`_itersNormalized` walk lemmas are `Cont.itersNormalized_true`
one-liners (the component is vacuous since B1 — A8's owed deletion
stands, see below). MachineSound: two `simp` sets gained `Cont.isGlue,
Cont.class, Cont.tail`; MultiSound: two `threadDone` unfoldings gained
`Config.isTerminal`. No statement changed.

**Not done, with reasons [AGENT].**
- `Cont.eqbF` as own-payload + tail: the per-constructor PAYLOAD
  comparison is irreducible (30 arms stay); factoring only the tail
  recursion saves one conjunct per arm and restructures a 100-line
  soundness proof — cost over gain. `andSplit11` stays.
- Field bundling (`FrameSpec`/`RangeSpec`+`IterState`/`SpineState`):
  every pattern match on `frame`/`mapIterK`/`tgtOpK` in every proof file
  (hundreds of sites) — outside this wave's budget after B2's re-proof
  wave; the algebra above is what makes it cheap later (a bundled frame
  is one `tail`/`withTail` arm).
- The accumulator flip (`vals ++ [v]` → reversed) and spelling every
  `(v :: done).reverse` through `applyOperands`: MEASURED (audit fix F3,
  correcting the draft's "~85 incl. 24 in proofs"): at the B8 tip the
  raw `(v :: done).reverse` spelling stands at 64 sites — 35 executable,
  29 in proofs — and `applyPos` added 8 more spellings + 3 encoding
  theorems, so the flip's TRUE cost is ≈110 sites + 3 theorem
  restatements (the proofs' `List.reverse_cons` normalisations all move
  with it). Re-measured at the fix-round tip with
  `grep -c '(v :: done).reverse'` over `GoLean/`: 73 lines — 44 in
  executable files (Machine 16 incl. the new `appendTargetLocal`, StepFn
  7, Multi 10, MultiStreams 2, Race 3, EnumDedupCheck 1, ChoiceTrace 5)
  and 29 in proof files (MachineSound 10, MultiSound 5, MultiWfSound 5,
  StateWf 6, EnumDedupSound 3); the audit's 64 counts sites, the grep
  counts lines and includes the tracer. `applyPos` has ONE consumer
  (`seqConsumption`); the consumer half (routing the executable sites
  through it) was NOT landed in the fix round — cost recorded here for
  B4/C3, which is where the flip belongs.
- `itersNormalized` deletion (A8 owed): 216 refs (StateWf 113,
  MultiWfSound 103) — a positional re-proof over two files that B8's
  budget did not leave room for; STILL OWED (its five walk lemmas are now
  one-liners, so the deletion is cheaper than it was).

## B8 — consumption from the machine

**What changed.**
- `seqConsumption σ c : Option (ChoiceSite × Nat)` (Machine.lean) — WHERE
  the next `stepFn` step consults the stream and at what bound, from the
  machine's own functions, one consult per site: `mapIterConsult?`
  (`mapIterCandidates`/`mapIterMandatoryRemains`), `stmtConsult?` →
  `appendSpill?` (the arm's own tests in the arm's order: fits in
  capacity → none; the R16 `growslice` refusal, raised BEFORE the consult
  → none; else `appendSpillWidth`), `selectConsult?` (`applySelectCore`'s
  `.picks`), `syncConsult?` → `tryLockConsult?` (`syncCell` +
  `tryLockWidth`), `entryConsult?` (the family's width 2 AND a panicking
  `enterFrame` — the pick is drawn on the panic path only). `some` ⇔ the
  consult POPS.
- `poolConsumption m picks` (Multi.lean) — the pool step's projection:
  the boundary consult (`boundarySite`/`schedSlots`, ≥ 2 slots), the
  spawn's child-entry pick, the arrival analysis (`arrivalCases`: L4 at
  ≥ 2 candidates, L2 at `.multi`), and on the cell path `seqConsumption`.
- `CLI.stepNeeds := (poolConsumption m picks).map (·.2)` and
  `CLI.stepNeedsSeq := (seqConsumption σ c).map (·.2)` — the 110-line
  dispatch mirror and its sequential twin are gone (−140 lines);
  `ChoiceTrace.seqSite`/`poolSite` are the projections plus the
  VALIDATOR's per-site menu-fact recomputation (`seqFacts`/`poolFacts`);
  the tracer's three-way self-check (a) "mirror = accountant" is now
  definitionally true and stays as a no-op alarm channel.
- **The theorem** (MachineSound): `stepFn_consumption_none` — a `none`
  step succeeds under EVERY stream with the same successor and the
  stream untouched; `stepFn_consumption_some` — a `some (site, b)` step
  DRAWS `(consumeAt site b ch).1` and depends on the stream only through
  it: any stream with the same pick yields the same successor with its own
  popped tail (first disjunct) — or, when the delivery AFTER the pop is a
  recoverable panic, the same successor with the PRE-apply stream (second
  disjunct; see the finding below). Both by `fun_cases` over `stepFn`,
  with per-site lemmas: `applyStmtOp_appendSlice_nospill` / `_spill`
  (the spilling apply is a function `g` of the pick, its stream the pop),
  `applySelect_done/_picks/_error_stream`, `applySyncOp_try_stream` /
  `_try_nopop`, `stepFn_mapIter_done/_pick/_stop` (existing),
  `enterFramePick_*`. The former hand-flag theorem `stepFn_oblivious`
  keeps its statement and is DERIVED (`seqConsumption_none_of_flags`);
  its 380-line positional body is deleted.
- NOT done, recorded: the `stepFn` 3-tuple → 4-tuple reshape
  (`× List PickRecord`) — "hundreds of pinned equations" (MachineSound,
  MultiSound, the drivers' unfoldings); the theorem is the substitute
  guarantee. `EnumDedupCheck`'s fragment flags (`consumesSelect`,
  `consumesAppendSlice`, `consumesTryLock`, `consumesNilValueMethod`) are
  UNTOUCHED: replacing them by `seqConsumption` would WIDEN the certified
  fragment (single-ready selects, non-spilling appends) = baseline PASS
  additions = drift, not this wave. No `stepMulti`-level theorem (the
  tracer's sentinel discipline is the pool projection's executable check).

**Preservation.** The projections are analysis functions — no execution
path reads them; the machine is unchanged. The executable check of the
theorem's claim is the tracer: with `seqSite`/`poolSite` now the
projections, the NEW tracer reproduced the OLD tracer's per-consumption
records byte for byte over the whole corpus (23665 records, 19962
(row, stream) lines; `choice-trace/b8-diff.txt`), and the sentinel /
pick-record cross-checks stayed at 0 alarms. `ci --diff`: PASS 3365 =
3165/200, FULL 3365/3365, 0 flips (`transcripts/gate-b8.txt`).

**THE FINDING — a PROOF ARTIFACT, refuted (audit fix F1, 2026-09-04).**
The first statement of the `some` half carried a second disjunct: "or
the delivery after the pop is a recoverable panic, and the step returns
the PRE-apply stream (the pop undone)". It was filed as BUG-092 (design
class) with two supposedly reachable shapes — a spilling `appendSlice`
whose grown-header STORE panics (`a[i] = append(b, 1, 2, 3, 4, 5)` with
`b` nil and `i` out of range), and a TRY head whose result delivery
panics. The pre-merge audit judged both UNREACHABLE, and the disjunct an
artifact of stating the theorem over ARBITRARY configurations rather
than the ones the machine and frontend produce. The audit's probes
(coordinator, relayed; [AGENT]):

| probe | expectation if the disjunct were real | observed |
|---|---|---|
| spilling append into an out-of-range `a[i]` | the `appendSpill` pop undone; slot re-read | the panic is raised by the ASSIGNMENT step, not the append: emit.go hoists every `append` into a fresh temp, so the append's target `tloc` is a plain local (a root cell) and its store cannot panic; the cap tracks stream slot 1 — the pop sticks |
| `TryLock` whose result delivery panics | the `tryLock` pop undone | `applyTryLock` cannot return `.error (.panic _)`: its stores go through cells the machine has just loaded; the mutex stays locked, in-place writes persist |

The refutation is now PROVED, not probed. MachineSound gains a
`NoPanic` predicate family (`NoPanic x := ∀ msg, x ≠ .error (.panic
msg)`, closed under `bind`/`map`/`ite`) and the lemmas
`normalizeValueForTy_noPanic`, `defaultValue_noPanic`,
`buildAppendBackingValue_noPanic`, `StructFields.set_noPanic`,
`storeLoc_base_noPanic` (a ROOT-cell store never panics),
`storeLoc_noPanic_of_loadLoc_ok` (a store through a path the machine can
load never panics — `arraySet_ok_of_arrayGet_ok`), `tryAcquire_noPanic`,
`enterRecvTargets_noPanic`, `tryDeliver_noPanic`, and
`applyTryLock_noPanic`. `appendSpill?` (Machine.lean) was REWRITTEN to
mirror every test the arm performs BEFORE its consult, in the arm's
order (both `valueAsSlice`, both `validateSlice`, `sliceVisibleValues` of
the elements, `valueAsLoc` of the target, the cap test, `tySizeBytes`,
the R16 bound, `sliceVisibleValues` of the slice) — so `some w` holds
exactly when the consult happens, and a pre-consult panic (a nil target,
an index panic in the element read) projects to `none`, where the
oblivious half applies. The one hypothesis the refutation needs is the
frontend's lowering contract, reified as `Config.appendTargetLocal :
Config → Prop` (at an `appendSlice` apply the target operand is `.addr
(.base a)` — the hoisted temp; `True` elsewhere); under it
`applyStmtOp_appendSlice_spill`'s new third conjunct gives `NoPanic (g
pick)` for the post-consult tail (`buildAppendBackingValue_noPanic` then
`storeLoc_base_noPanic`), `stepFn_stmtOp_spill` takes that as `hnp` and
its panic branch is closed by `absurd`, and the sync arm's panic branch is
closed by `applyTryLock_noPanic`. `stepFn_consumption_some` now takes
`(hloc : c.appendTargetLocal)` and states the SINGLE conclusion "the
stream is the site's pop, and any stream with the same pick yields the
same successor with its own popped tail". Honest scope: the hypothesis
is discharged by the frontend's construction (emit.go's hoisting), which
this repo validates differentially, not by a Lean proof about the
frontend — the frontend was not touched. BUG-092 is RETIRED: the entry is
deleted from `docs/BUGS.md` (the number is not reused); no [USER] ruling
was needed, because nothing was ever wrong with the machine — only with
the theorem's first statement. The tracer's byte-identity and the 0
sentinel alarms were consistent with this all along.

Also in the fix round (F4, records): `except_bind_ok` and
`bind_pair_stream` MOVED from `GoLean/GoCore/EnumDedupSound.lean` (where
they were `private`, formerly lines 103 and 109) to MachineSound.lean and
are public there — B8's select/sync stream lemmas needed them; the note's
first draft omitted the move.

## Obs

`Obs := ok values | terminal Terminal` (B2, above): every Go terminal is
statable, so the enumeration lane's vocabulary is the outcome grammar's
own. `obsOf?` maps every `.error (.terminal t)`; `fuelOut` and the
refusals stay `none`. The engine and checker still refuse fatal and
deadlock MEMBERS (a certified set never contains one silently); admitting
them is a lane decision the [USER] takes, not a type change — the type
now permits it. `Obs.eqb` compares terminals by `Terminal`'s
`DecidableEq`.

Because the type no longer guards the member vocabulary, the guard moved
to the EMIT site (audit fix F5): `CLI.memberVocabularyRefusal? : Obs →
Option String` names the refused members (`fatal` and `deadlock` — every
`Terminal` but `panic` and `raceDetected`), and the CLI's certified-set
emit loop refuses BY NAME before the status-discipline check. Red-first:
`Tests/GoCoreEval.lean` fakes a `.terminal (.fatal …)` and a `.terminal
.deadlock` member and checks both are refused, and that `ok`/`panic`/
`raceDetected` pass.


## Summary — what landed, what moved, what is owed

| item | commit | core effect | proof side |
|---|---|---|---|
| B2 `Result` at the apply boundary | `91c57c9e` | `Result`/`toResult` (Value.lean); `panicEntry`, `deliver`, `enterFramePick` (Machine.lean); `deliverS` (StepFn.lean); 17 twin rules deleted (159 → 142); 41 inline conversion sites → 0 (`panicEntry` at the 12 in-helper/nil-callee sites, `deliver`/`deliverS` at every apply/entry); 3 entry funnels → 1; `Obs := ok ∣ terminal Terminal`; `Result` → `Readout` | `step_preserves_wf_loc` 17 cases restated (one macro for the panic branch); `stepFn_sound`/`step_complete`/`step_complete_any_wf_aux`/`stepFn_oblivious` re-tagged (75 → 75 tags) with 4+2 macros; MultiSound/MultiWfSound select-interception and spawn lemmas restated; `entryPanicStream` + its lemma deleted; `Obs.eqb_sound` over `DecidableEq`; the enumeration completeness proof unchanged |
| B3 the `Cont` algebra + A7 accessor | `cd2a3474` | `Cont.tail`/`withTail`/`class`/`isGlue`/`rebuild` + 6 laws; `pushDefer`/`recoverThroughWrappers`/`recoverResult`/`panicPassthrough` = instances (4 × 30 arms → 4 short defs); `Config.isTerminal` (`threadDone`, `atBoundary`); `Config.applyPos` + `ApplyHead` | generic `Cont.rebuild_locSup` (+ `ownSup`, `locSup_withTail`, `locSup_eq_own_tail`, `tail_locSup_le`) replaces 3 walk inductions; 5 `_itersNormalized` walk lemmas → one-liners; `isTerminal` in 2 MultiSound unfoldings; prototype equivalence proofs in the evidence dir |
| B8 consumption from the machine | `2e69fde0` | `mapIterConsult?`/`stmtConsult?`(`appendSpill?`)/`selectConsult?`/`syncConsult?`(`tryLockConsult?`)/`entryConsult?` + `seqConsumption` (Machine.lean), `poolConsumption` (Multi.lean); `CLI.stepNeeds`/`stepNeedsSeq` (−140 lines) and the tracer's `seqSite`/`poolSite` are projections | `stepFn_consumption_none`/`_some` (two `fun_cases` sweeps, 102 tags total with `stepFn_sound`), 12 per-site stream lemmas, `seqConsumption_none_of_flags`, `applyPos_stmt/_select/_sync`; `stepFn_oblivious` DERIVED (−380 lines); the `some` half's first-draft second disjunct (filed as BUG-092) REFUTED by lemma and removed in the audit fix round — `NoPanic` family, `applyTryLock_noPanic`, `appendTargetLocal` + `storeLoc_base_noPanic`; `appendSpill?` mirrors every pre-consult test; `Cont.class` exhaustive (F2) |

Net `git diff --shortstat main..HEAD -- GoLean Tests` at the B8 tip: 17 files,
+3141 / −2092 (+1049 net; `GoLean/GoCore/` alone +2970 / −1747). The wave
is net POSITIVE in lines: B8 ADDS a theorem family (the two sweeps + twelve
per-site lemmas ≈ +900 in MachineSound) that did not exist — the deletions
are the 17 rules, the 41 conversion sites, the two entry helpers, the four
30-arm walks and their three inductions, the two CLI mirrors and the
380-line positional obliviousness body. Lines are not the point; the
per-item "what got shorter or vanished" lists are.

Every gate: `ci --diff` PASS `3365 = 3165/200`, FULL 3365/3365 no
regression, 0 flips (`transcripts/gate-{b2,b3,b8}.txt`); every trace: 0
delta on 19963 aggregate lines AND on all 23665 per-consumption records.

**Owed onward (recorded, not silently dropped):** `itersNormalized`
deletion (A8; cheaper now); the program-text `locSup` deletion (A4); the
helper-internal `Result` monad, if ever wanted (B2's deviation);
`Cont.eqbF`/bundling/accumulator flip (B3's skips); the `stepFn` 4-tuple
reshape (B8's deferral — the theorem is the substitute); the accumulator
flip's consumer half (F3: ≈110 sites + 3 restatements, for B4/C3);
`RaceState.chans/.syncs/.atomics` canonical order
(A6's residual — did NOT fall out of B3/B8: neither touched the detector's
assoc lists; still owed engine-side). `Obs.fatal`/deadlock: DELIVERED as a
statable type (B2), the lanes' refusal of those members unchanged.

## Audit fix round F1–F6 (2026-09-04, [AGENT] executing the coordinator's FIX-FIRST verdict)

| item | verdict | what changed |
|---|---|---|
| F1 (HIGH) BUG-092 is a proof artifact | DONE | refutation proved (`NoPanic` family, `applyTryLock_noPanic`, `Config.appendTargetLocal`, `storeLoc_base_noPanic`, `buildAppendBackingValue_noPanic`; `appendSpill?` mirrors every pre-consult test); `stepFn_consumption_some` single conclusion under `hloc`; BUG-092 deleted from BUGS.md (number retired) — §B8 above |
| F2 (MEDIUM) `Cont.class` absorbing default | DONE | the 23 `exprGlue` constructors spelled explicitly (31 `Cont` constructors: 1 stop, 1 call frame, 1 resume marker, 5 statement glue, 23 expression glue); no `_ =>` arm (a new constructor is a compile error, not a silent glue) |
| F3 (MEDIUM) A7 "spelled once" false | RECORDS corrected (consumer half NOT landed) | one consumer; 64 raw sites (35/29) + 8 added spellings + 3 theorems; true flip cost ≈110 + 3 recorded for B4/C3 — §B3 above and the review's A7 line |
| F4 (LOW) note omissions | DONE | `except_bind_ok`/`bind_pair_stream` move listed; `allStreamsOk`'s real reason (excludes `.panicked`); NPDRF `threadDone_atBoundary` converted (tally 3/6); EnumSpec.lean "six-arm" → five |
| F5 (LOW) Obs vocabulary guard | DONE | `CLI.memberVocabularyRefusal?` + emit-site refusal by name; red-first unit checks — §Obs above |
| F6 clean-tip gate | PASS | `scripts/capped scripts/ci --diff` at the fix-round tip: PASS, 3365 = 3165/200, FULL 3365/3365 no regression, negative 394/394, 0 flips (`transcripts/gate-fix.txt`); the TWO tracer exclusions recorded in the evidence README; tracer spot-check 8 rows / 156 records identical (`choice-trace/fix-spot.txt`) |

No frontend, decoder or wire change; no new `ChoiceSite`; no baseline,
gate or corpus change. The tape is consumed identically (the projections
are unchanged in value: `appendSpill?`'s rewrite returns `some` in exactly
the cases the old one did on reachable configurations — the old body
returned `some` also on pre-consult-panicking shapes, which the arm never
consults; spot-checked with `choice-trace --dump`, see the README).
