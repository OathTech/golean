# The step label — `StepLabel := { trace, picks, out }` (window row 2a)

[AGENT worker, lane `core/step-label-0928`] 2026-09-28. Authority: [USER] Mike 2026-09-22/23 «the sequential step
label becomes the full event label (access ⊕ pick ⊕ out)», «we should make the model as regular as possible»
(relayed); the batched window charter rev. 2 row 2 (RULED 2026-09-24); the logic team's response §3. Base `main` @
`84f0a9e4`. Handoff: `docs/2026-09-28_step-label-handoff.md`. Changelog row: `docs/changelog/61958f2e-WINDOW.md`.

## 1. The shape (as ruled; no deviation)

`structure StepLabel where trace : AccessTrace; picks : List PickRecord; out : List GoString` (`Ops.lean`).
`Step : Config → Store → Config → Store → StepLabel → Prop`; `stepFn : … → Except Stop (Config × Store × Choices ×
StepLabel)`; `StepEvent := { who, action, label : StepLabel }`. Three channels, each ORDERED within the step:

- `trace` — unchanged content (C1's memory-model events, gc's instrumentation order).
- `picks` — every tape consultation of bound > 1 the step KEEPS, exactly as `Choices.consumeAtE` returns it, in
  consultation order. Bound ≤ 1 records nothing (and pops nothing); the empty tape records pick 0. The record is
  EMITTED BY THE CONSULTING SITE (each consulting helper switched `consumeAt` → `consumeAtE` and returns its records
  beside the stream it returns), never reconstructed from `seqConsumption` or the tape.
- `out` — a `print`/`println` apply's bytes (`stmtOpOut op vals`, the same `renderPrint` the apply validates
  through), `[]` for every other step.

The relation states picks per rule: the helper-consulting rules take the helper's records (entry, stmt apply,
sync apply, select apply); the index-choosing rules state them with `PickRecord.ofPick site bound idx`
(`mapIterNext`/`mapIterStop`, `unseqPick`), the probe's two rules name `⟨unseqPanic, 2, 0⟩` / `⟨…, 1⟩`.
`Choices.consumeAtE_eq` (`consumeAtE` = `consumeAt` + `ofPick` of its pick) is the bridge the proofs use.

**Records ride with the stream.** A delivered panic that RESTORES the pre-apply tape (`deliverS`/`deliverV`'s
convention) drops its consultation's record with the stream advance; a consultation whose advance the step keeps on
its panic path — the frame entry's `nilValueMethodText` text pick — is recorded (`deliver`/`deliverV`'s new
optional `panicPicks`). So replaying a label's records reproduces exactly the stream the step consumed.

## 2. The silent projection

The label is a FIELD of the step, not an element appended to a stream: every pure rule carries `⟨[], [], []⟩`, and
an observation is the per-field FOLD (`StepLabel.fold`: concatenation per channel — the `AccessTrace` flatten, the
picks concatenation, `execProgLoopOut`'s output fold). `⟨[], [], []⟩` is the fold's unit in each channel, so a pure
step contributes nothing and no `[emptyLabel]` element ever appears where there was none —
`StepLabel.fold_silent : fold (ls₁ ++ ⟨[], [], []⟩ :: ls₂) = fold (ls₁ ++ ls₂)` (proved; pinned; required by the
core audit). An adapter projecting a silent label to `[]` is exactly this lemma.

## 3. The pool unification (one label type, no double accounting)

`stepThread`'s goroutine step now takes the step's label wholesale: trace and output verbatim, picks = the pool's
own arrival-plan picks FOLLOWED by the step's (`{ l with picks := ps₁ ++ l.picks }`). The former re-derivation of
the output from the pre-configuration (`(printOut? c).toList`) is gone from the pool; `printOut?` survives only as
the init phase's refusal test, with `printOut?_toList` proving it agrees with the step's own `out`. The select
interception, the spawn and the abort build their labels from the helpers' records (`applySelect`'s L2 record;
`spawnStep`'s child-entry record — previously an unrecorded consultation; the tombstone's `repanicCollapse`);
`stepMulti` prepends the boundary pick. Projection theorem: `stepThread_privateStep_label` — a `privateStep` event's
label IS `⟨l.trace, ps₁ ++ l.picks, l.out⟩` for the `stepFn` step `l` of the goroutine (pinned, audited). The
terminal events: `stepMulti_abort_single` (label `⟨[], repanicCollapse record, []⟩`); attribution: `StepE.spawn`'s
label `⟨edge :: child reads attributed, entry records, []⟩`. Consequence, disclosed: the event's `picks` channel now
carries the sequential sites too (it carried pool-layer sites only, the stage-B scope note — its re-open trigger
fired). `StepM`/`StepMFine` keep their `AccessTrace` label (`l.trace` at the `thread` rule): the labelled POOL
relation (attribution and terminal events as relation labels) is after the window (charter §2).

## 4. The documented limitation — no cross-channel interleaving

Within one step the three channels are ordered separately; the label does NOT say whether a pick preceded an
access or a write preceded an output byte. No step mixes channels in a way the machine orders today (a `print`
apply has no trace and no pick; a consulting apply's trace follows its validate-phase pick by construction), but the
label does not state it, and consumers must not assume an interleaving (logic team §3: «document that limitation
rather than invent an instrumentation order»). Across steps, labels are ordered by the step sequence.

## 5. `initPrintRefusal?` — RETAINED

[USER] 2026-09-24 ruling 10. The init driver folds no label into the program output, so a `print` during package
initialization still REFUSES by name (text unchanged); the step itself carries `out` there too, unused. Lifting it
(connecting setup's output to the program trace) is a later item.

## 6. What packet B inherits

- The reshaped shapes (handoff §3 lists signatures and line numbers). `ExecutionStatement.lean` is re-stated:
  `Prefix`/`LRun`/classification over `List StepLabel`; `replays : List PickRecord → Choices → Choices → Prop`
  (replay BY RECORD: each record re-drawn by `consumeAtE r.site r.bound`, same pick, same record);
  `replay_coverage_stmt` over `l.picks`; `silent_projection_stmt` over `StepLabel.fold` (already provable by
  `StepLabel.fold_silent`).
- Question 1 (flagged, not decided): `replay_coverage_stmt` is premise-free; `stepFn_consumption_some` still carries
  `c.appendTargetLocal`. With records dropped on a tape-restoring panic, coverage at `appendSpill` rests on the
  post-consult tail being panic-free — `applyStmtOp_plan_appendSlice_spill` proves `NoPanic (g pick)` for the
  validate tail and `applyStmtOp_commit_noPanic` for the commit, so the premise looks dischargeable; B confirms.
- The pool half (`program_run_iff`/`observation_iff` relabelled over `StepLabel`, a labelled `StepM`) waits (charter
  §2); `single_embedding` over the pool fold can use `stepThread_privateStep_label`.
