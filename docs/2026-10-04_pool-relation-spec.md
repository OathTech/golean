# The pool/registry half — the SPEC PACKET (a named design gate)

[AGENT design worker, lane `design/pool-relation-spec-1004`] 2026-10-04. Authority: [USER] Mike 2026-10-04 «Great,
launch it» (relayed by the [AGENT] coordinator — cite as relayed), approving: a spec packet — frozen definitions,
exact statements, a `sorry`'d skeleton outside the build, this note — as a NAMED DESIGN GATE (a HARD STOP for
[USER] review), then a Codex grind under a tight brief («Codex is good at tightly specified difficult 'grinds' on
hard theorems. We would want to give enough flex it could build successfully, without giving too much space for
drift» — [USER], same day). **Nothing here is proved and no grind has started.** Every decision below was [AGENT];
the gate was RATIFIED by the [USER] on 2026-10-04 (§9) and the statements then passed an adversarial statement
review whose findings are applied (§10).

Files (all on this branch): `GoLean/GoCore/PoolStep.lean` (the FROZEN DEFINITIONS; compiles, no `sorry`, total),
`GoLean/GoCore/PoolStatement.lean` (the 48 target statements as `def <name>_stmt : Prop`, plus `rfl` controls;
compiles), `docs/specs/pool-relation/Skeleton.lean` (`theorem <name> : <name>_stmt := by sorry` × 48; OUTSIDE every
build target and gate scan; elaborates: exit 0, 48 `sorry` warnings, nothing else), `scripts/check-pool-spec` +
`docs/specs/pool-relation/FROZEN.sha256` (the statement-hash check), `docs/2026-10-04_pool-relation-grind-brief.md`
(the grind brief, draft). Both modules are wired into `GoLean.lean` (the core audit's two-way closure requires it);
`scripts/capped lake build GoLean` is warning-free and `scripts/check-core-audit` passes at this tip.

## 1. What exists vs what is owed

| | Exists (`main` @ `450412a7`) | Owed (`CLAUDE.md` item (2); window plan §2) |
|---|---|---|
| Pool relation | `StepM : MultiConfig → MultiConfig → AccessTrace → Prop` (`Multi.lean:2146`) — 7 rule classes, labelled by the memory TRACE only; `schedPick` = membership in `runnableIdxs` | the relation over the FULL `StepLabel` with ATTRIBUTION (who), the pool's picks and its output — «one label type at both layers» (`docs/2026-09-28_step-label.md` §3 deferred it) |
| Correspondence | `stepMulti_sound` / `stepM_complete` (`MultiSound.lean:1192`, `:1338`) — agree on the trace | the same two, agreeing on the EVENT |
| Registry boundaries | `Thread.atBoundary`, `Thread.boundarySite`, `schedSlots` (executable); the relation's `schedPick` consults them | boundaries as THEOREMS: a context switch only at a boundary; the scheduling consultation as a RECORD in the label |
| Deadlock | the drivers' `throw .deadlock` at `runnableIdxs = []`; `poolResult?` (`NPDRF.lean`); the relation is deadlock-silent | «the pool deadlock's own condition» as a predicate, its driver characterisation, its relation to sequential `Blocked` |
| Run carriers | `PoolTrace.Run`/`front`/`run_iff`; `ProgramRun`/`program_run_iff`/`observation_iff`; `PoolSteps` | the pool twin of `Prefix`/`Finish`: arbitrary endpoints, terminal priority, the fuel bridges, the four-way classification, the program seam over the labelled carrier |
| Single goroutine | `execProgLoop_single`, the output agreement and terminal projection (`PoolProjection.lean`), the equal-fuel embedding | the single-goroutine case as a COROLLARY of the pool relation: step level (to `Step`), finish level (to `Finish`), prefix level (to `Prefix`) |

## 2. The chosen shape — decisions ([AGENT], pending ratification)

**D1 — the label IS the executable event.** `StepML ctx m m' ev` with `ev : StepEvent := { who, action, label :
StepLabel }`, the SAME type `stepMulti` returns. Attribution = `who`; the pool's classification of the step
(`action`: the spawned child's index, the pairing partner's index, the committed clause, the clear, the abort, the
wake, the private step) stays in the label; `label` is the full `StepLabel`. Soundness and completeness then state
EVENT equality, exactly as `stepFn_sound`/`step_complete` state label equality. The existing `StepM` becomes the
trace PROJECTION (`stepML_erase_stmt`, `stepM_lift_stmt`): nothing restated, nothing weakened.

**D2 — scheduling is latitude, reified as a pick.** The rule premise `SchedSlot ctx m i slot`: at a boundary of the
running goroutine, `slot` indexes the boundary's slot menu (`schedSlots` at `Thread.boundarySite`) and names `i`;
off a boundary `i = m.cur`, slot 0. The event's picks BEGIN with `schedRecord ctx m slot = PickRecord.ofPick site
|menu| slot` — `[]` at a singleton menu (the uniform bound-≤-1 rule, sequential conservation's hinge), the one
record otherwise — exactly what `stepMulti` prepends (`Choices.consumeAtE_eq`). Nothing is baked into recursion:
every pool consultation (`l1Sched`/`postOp`/`backEdge`, `l2Arrival`, `l4Waiter`, `repanicCollapse`) is stated with
`PickRecord.ofPick`, the sequential rules' idiom; the sequential step's own picks follow. `MultiConfig.schedMenu?`
exposes the consultation (site, menu) a boundary makes.

**D3 — ten rules, one per executable arm.** `strip`, `abort`, `spawn`, `thread` (a `Step` at a non-select cell-path
position), `selectApply`/`selectApplyPanic` (the select interception — the pool runs `applySelect` itself so the
emitted commit identity reaches the event; the panic path is `deliver`'s unwinding configuration), `pair`,
`pickPair`, `pickCommit`, `wake`. Premises are `StepM`'s and `stepThread`'s own; successors are `stepThread`'s
literally (`setIfInBounds`, `push`, `Thread.afterStep`, `Thread.completed`); `cur := i`.

**D4 — the deadlock gets its own predicate.** `PoolDeadlock ctx m := m.threads.isEmpty = false ∧ m.panicMsg? = none
∧ m.mainOutcome? = none ∧ runnableIdxs ctx m.shared m.threads = []` — the driver's third classification over a
NON-EMPTY pool (the empty pool is the driver's `.internal` refusal, never a deadlock). The relation stays SILENT
there (`asleep_silent_stmt`); the sequential `Blocked` differs by the wake condition (`singleton_deadlock_stmt`:
alone, a blocked goroutine is the pool deadlock iff `wakeReady … = false`) — the logic team's «different
environmental conditions», made exact.

**D5 — the driver's own carriers, with terminal priority.** `Continue ctx m ch ch₁ rec` (the pre-step gate =
`front`'s continue arm, the main-exit window's `l5ExitWindow` draw RECORDED); `DriverEvent := { window : List
PickRecord, event : StepEvent }` (one loop iteration's label: the window record beside the step's event — the draw
belongs to the DRIVER, so the event stays `stepMulti`'s verbatim); `PoolPrefix n m r ch des mf rf chf` (the
counted, choice-threaded, detector-threaded closure of the driver's iterations; `stepMulti`-defined like `Prefix`
is `stepFn`-defined, erased to `StepsML`/`PoolSteps`); `PoolFinish m r ch rec o cost` with `PoolOutcome :=
normal σ ch | deadlock ch | aborted msg ch | fatal msg ch | raced ev ch` — the TOMBSTONE first, then MAIN'S EXIT
(`normal`; `exitWindow` with the draw's record), then the DEADLOCK, all at cost 0 before the fuel; a `fatal` pool
step and a detected RACE (the racing step's EVENT kept — the terminal event) at cost 1. Priority is a theorem:
the classification is a FUNCTION of `(m, r, ch)` (`poolFinish_functional_stmt`).

**D6 — the single-goroutine case is a corollary.** Step level: `stepML_single_sound/complete_stmt` reduce a lone
goroutine's `StepML` to `Step` (attribution 0, label equal). Finish level: each sequential `Finish` constructor
maps to its pool counterpart (`singleton_finish_*_stmt`; the abort = one pool STEP to the tombstone with the same
record, then the cost-0 finish; the deadlock under `wakeReady = false`). Prefix level: `singleton_prefix_embedding_stmt`
— a `Prefix` of `n` steps is a `PoolPrefix` of `n + seqOpCount …` iterations (the PROVED cost relation: one clear
per completed registry op; never «equal fuel»), no window draw, every event attributed to 0, labels FOLD-EQUAL.
`PoolProjection`'s `execProgLoopOut_single_wide` is pinned as the base case (`singleton_run_stmt`, definitional).

**D7 — the error classes are stated, not assumed.** `stepMulti_error_cases_stmt` (a refusal, the `fatal`, or the
empty-menu deadlock throw — NEVER the `panic` terminal: the pool twin of `stepFn_no_stray_panic`),
`stepMulti_deadlock_elim_stmt` (the throw is unreachable after the gate), `raceUpdate_error_stmt`. Inspected by
reading every throw site (`commitClause` RETURNS the send-on-closed `.panicking`; `applySelect` is `toResult`-wrapped;
`runCommit` turns a commit panic into `.internal`; the child's entry panic is delivered in the child) — the
classification theorems NEED them, and if any helper surfaced `.panic` through `Except` that would be a FIDELITY
BUG (the pool analogue of packet A's audit F1), not a proof obstacle: HARD STOP with the witness.

## 3. Alternatives considered and rejected

- *Label `{who, label}` only, `action` dropped* — loses the pairing partner and the spawned child as label data
  (both are what the logic side's attribution needs) and would make the event a projection of the executable's,
  weakening the «one label type at both layers» discipline. Rejected; `action` is in the executable's event today.
- *Fold the window draw into the event's picks* — would make the relational label differ from `stepMulti`'s event
  (soundness would state `∃ ev', ev' = {ev with picks := w ++ …}`), and misattribute a DRIVER draw to a step.
  Rejected; `DriverEvent.window` keeps it beside.
- *Define `StepML` as `StepM ∧ laws over (m, m', ev)`* — not an inductive, no case analysis for consumers, the laws
  re-derive the step's structure. Rejected.
- *Change `stepMulti` to return a richer event (boundary flag, site)* — an interpreter signature change (BridgeSet
  row 29 pins `StepEvent.mk`), outside this packet's authority; also unnecessary: the boundary is `m.schedMenu?`,
  a function of the pre-state. Rejected.
- *`PoolPrefix` over `StepML` (relational) instead of `stepMulti`* — the window plan's choice 1 defines `Prefix` by
  executable steps and erases to the relation; mirrored. (The relational closure is `StepsML`.)
- *`PoolDeadlock` admitting the empty pool* — `front` refuses it (`.internal "thread pool without a main goroutine"`);
  admitting it would make `front_finish_stmt`'s deadlock clause false. Rejected.
- *A new `ProgramLRun` inductive* — glue over `Run`; `run_ok_prefix_stmt`/`program_prefix_stmt` + the `_iff`s give
  the relabelling without a third carrier. Deferred to the grind's free zone if a consumer wants it.

## 4. Composition with what is proved

`StepM`-level results stay as they are and become corollaries: `stepMulti_sound = stepML_erase ∘ stepML_sound`,
`stepM_complete` from `stepM_lift` + `stepML_complete`. `PoolTrace.Run` is `PoolPrefix` + `PoolFinish`
(`run_ok_prefix_stmt`; `Run.step`'s premises are `PoolPrefix.step`'s, `front` is `Continue`/`PoolFinish` by
`front_continue/finish/refusal_stmt`). `PoolProjection`'s singleton theorems are the base case of the reduction
(`singleton_run_stmt`); `singleton_prefix_embedding_stmt` generalizes `execProgLoopOut_single_prefix` to arbitrary
endpoints and full labels. `NPDRF`'s `StepsM`/`poolResult?` are untouched (`PoolSteps` is the erasure target used).

## 5. What the logic side can consume (their 2026-09-23 §3 and 2026-09-28 asks)

Attribution as data (`ev.who`; the partner/child in `ev.action` and in the trace: `stepML_paired_trace_stmt`,
`stepML_spawn_stmt`); the FRAME law (`stepML_frame_stmt`: a step rewrites `who` and, on a pairing, its named
partner, nothing else; the pool never shrinks); context switches only at registry boundaries, with the scheduling
record first in the picks; terminal events (`PoolOutcome.raced ev`, the tombstone's text, the window's record);
replay BY RECORD (every consultation recorded with site/bound/pick, bound ≤ 1 silent — the sequential
`replays` applies verbatim: `stepMulti_replay_stmt`, `continue_replay_stmt`, `poolPrefix_replay_stmt`, added by
the statement review, §10); the exact fuel bridges and the refusal-separate classification over the pool; the
program seam under setup (`program_prefix_stmt`); the single-goroutine reduction to `Step`/`Finish`/`Prefix`.
NOT provided (unchanged limits): setup is a premise; init-time printing refused; `NoRefusal` sequential-only (no
pool domain premise is introduced here — the classification is unconditional, refusal reported); the access
granularity reduction (`NPDRF`) untouched. Also NOT provided, and FALSE as a bare statement: the run-level
converse «every `StepsML` run is some tape's `PoolPrefix`» — `StepML` steps a pool holding a TOMBSTONE (an aborted
goroutine does not stop the others relationally), while the driver's gate `Continue` refuses to step it (the
tombstone is classified first, `PoolFinish.aborted`). The converse holds only per step (`stepML_complete_stmt`) and for runs that pass the gate at every step.

## 6. The 48 statements and why each is true (one line each; proofs are the grind's)

(A) `stepML_sound` — `stepMulti ∘ stepThread`'s arms are the ten rules; the sched record is `consumeAtE`'s (`consumeAtE_eq`); the existing proof's case tree with label equalities. `stepML_complete` — realize the slot by the tape `slot :: ch` at bound ≥ 2 (`consume (slot :: ch) b = (slot, ch)`), nothing at bound 1; the inner tape as `stepM_complete` builds it (`step_complete`, singleton tapes for L2/L4/`repanicCollapse`, `applySelect`'s own tape); the helpers are deterministic. `stepML_erase` — rule by rule (`thread` → `StepE.lift`; `spawn` → `StepE.spawn` with `push_eq_append_running`; the select arms → `Step.selectApply` via `toResult_ok`/`toResult_panic` + `deliver`). `stepM_lift` — the converse by cases on `selectApplyPlan`; the slot from `schedSlot_iff`. `stepsML_erase` — induction. `stepMulti_replay` — every `stepMulti` consultation is a record-emitting `consumeAtE` (bound ≤ 1 pops nothing and records nothing), so a replaying tape re-draws the same picks; the rest of the step is tape-independent (`stepFn`'s own replay, `finish_replay`/`replay_coverage`'s pattern).
(B) `stepML_who_runnable` — at a boundary the menu ⊆ runnable (`schedSlots_mem`); off it `i = cur` with a live, unflagged, non-terminal (`step_terminal_elim`; the other arms' shapes are `.retV`/abort) goroutine. `stepML_sched` — `schedSlot_iff` →; `cur := i` by construction. `stepML_switch_boundary` — off a boundary `SchedSlot` forces `i = cur`. `stepML_sched_record` — `ofPick` at bound > 1 is the one record; every rule's picks start with it. `schedSlot_iff` — `schedSlots_mem`/`mem_schedSlots_of_runnable` + `List.mem_iff_getElem?`. `stepML_frame` — `setIfInBounds` touches `i`; `push` keeps `j < size`; `applyPairing` writes `i` and `cs[idx].2.partnerIdx` only (each arm's two `setIfInBounds`). `stepML_paired_trace` — `pairSendEvents`/`pairRecvEvents` name `j` by `rendezvous` or `attributed`. `stepML_spawn` — the `spawn` rule's trace head and `push`; every other rule keeps the size.
(C) `asleep_silent` — from `stepML_who_runnable`. `singleton_deadlock` — no tombstone, blocked ≠ `.next .stop`, `threadRunnable = wakeReady` on a blocked thread (`isBlockedConfig_ne_terminal`). `mainOutcome_not_deadlock` — the predicate's third conjunct.
(D) `stepMulti_error_cases` — every throw site (`stepThread`, `spawnStep`, `resumeThread`, `applyPairing`, `arrivalPlan`, `commitClause`, `enterRecvTargets`, the cell/sync helpers) is a refusal or `fatal`; `stepFn` runs only off the abort (`stepFn_no_stray_panic`); the one `.deadlock` throw is the empty menu. `stepMulti_deadlock_elim` — `Continue` gives `runnableIdxs ≠ []`, `mem_schedSlots_of_runnable` fills the menu. `raceUpdate_error` — `accessKey`'s only throw.
(E) `front_continue`/`front_finish`/`front_refusal` — unfold `front`: its arms are these cases (`consumeAtE_eq` for the window; the pick is `< 2`). `poolFinish_functional` — the discriminating premises are exclusive pairwise; `Continue`, `consumeAtE`, `stepMulti`, `raceUpdate` are functions. `poolFinish_zero_not_continue` — tombstone/none, `[]`/`≠ []`, pick 0/1, `mainOutcome?` none/some.
(F) `poolPrefix_comp/split` — as `prefix_comp/split`. `poolPrefix_labelled/erase` — `stepML_sound` per step. `poolPrefix_run` — induction with `unfold_driver` + `front_continue` ←, `outFold_cons`. `pool_run_ok/terminal/fuelOut/refusal_iff` — the pool twin of `execStmtLoop_error` (`unfold_driver` per fuel; `front` classifies or steps; the step's error classes by (D)); ← by `poolPrefix_run` then the finish. `pool_classification` — case on the result shape. `run_ok_prefix` — `run_iff` + `pool_run_ok_iff`. `continue_replay` — `running`: `rec = []`, `replays [] ch₂ ch₂'` forces `ch₂' = ch₂`; `window`: the one record re-draws pick 1. `poolPrefix_replay` — induction, splitting the replay at each iteration's `window ++ picks` (`replays` over an append), `continue_replay` then `stepMulti_replay`; `raceUpdate` reads no tape.
(G) `program_prefix` — `runProgramPoolOutM` unfolded under setup (`program_bridge`'s equation) + `pool_run_ok_iff`; `Array.toList_toArray`.
(H) `stepML_single_sound` — `arrivalCases_singleton` kills the pairing arms; the premises kill `strip`/`abort`/`spawn`/`wake`; `schedSlots_singleton` makes the record `[]`; structure eta gives `ev.label = l`. `stepML_single_complete` — by `selectApplyPlan`: `thread` or the inverted `Step.selectApply`. `singleton_finish_normal` — `runnableIdxs_singleton_none`. `singleton_finish_aborted/refused` — `finish_aborted_stepFn`/`abortLeftover` shape + `stepMulti_abort_single`. `singleton_finish_fatal` — `stepMulti_single` maps the error through; `Continue.running` from the singleton facts. `singleton_finish_deadlock` — `singleton_deadlock` →. `singleton_prefix_embedding` — `execProgLoopOut_single_wide`'s induction over `Prefix` (`stepMulti_single`, `stepMulti_flagged_single`, `raceUpdate_single`, `front_single_step/_flagged`), the fold by `fold_silent`. `singleton_run` — `run_iff.mp (execProgLoopOut_single_wide …)`.

## 7. Gates and wiring at this tip

`PoolStep`/`PoolStatement` imported from `GoLean.lean` (default build; core audit closure). `scripts/ci`'s
escape-hatch pipeline over `GoLean/` reports none found (prose mentions are backticked). The skeleton and the
freeze file live under `docs/specs/pool-relation/` — no glob, import or scan reaches them. `scripts/check-pool-spec`
is a PROPOSAL (not a `ci` step): `--freeze` wrote `FROZEN.sha256`; without flags it fails closed until
`PoolSound.lean` exists (`--statements-only` for the spec phase). No interpreter behaviour, no pinned statement, no
baseline touched; the differential was not run (records and Prop definitions only).

## 8. Open questions for the [USER] (the gate) — RATIFIED 2026-10-04, §9

1. **D1** — ratify the label as the executable `StepEvent` verbatim (incl. `action`)?
2. **D5** — ratify `DriverEvent.window` beside the event (the driver's draw not folded into the step's picks)?
3. **D4** — ratify the non-empty-pool conjunct of `PoolDeadlock`?
4. **Scope** — 45 statements (48 after the statement review, §10) in 5 milestones (grind brief §7); ratify milestone-by-milestone landing (each
   milestone's theorems depend only on earlier ones)?
5. **`StepM`'s future** — keep the trace-labelled relation as the proved projection (recommended until the logic
   repo re-pins), or retire it after the grind?
6. **Relabelling** — `program_run_iff`/`observation_iff` are relabelled through `run_ok_prefix`/`program_prefix` +
   the `_iff`s; no third `ProgramLRun` carrier. Sufficient, or add it?
7. **The brief's tool** — the ruling names Codex; the brief is written for a tightly specified grind by any
   worker. Confirm Codex and the Fable/Opus review assignment at its close.

## 9. Ratification

[USER] Mike, 2026-10-04 (verbatim, relayed by the [AGENT] coordinator — cite as relayed): «Approved» — ratifying
§8's questions 1–7 as recommended, and ordering an adversarial statement review before the grind (§10). Outcomes:

1. **Label** — `StepEvent` verbatim (`who`, `action`, the full `StepLabel`), as D1.
2. **Driver draw** — `DriverEvent.window` beside the event; the window draw is not folded into the step's picks (D5).
3. **Deadlock** — `PoolDeadlock` keeps the non-empty-pool conjunct (D4).
4. **Scope** — milestone-by-milestone landing (grind brief §7).
5. **`StepM`** — kept, as a proved projection of `StepML` (`stepML_erase_stmt`, `stepM_lift_stmt`).
6. **Relabelling** — no third `ProgramLRun` carrier.
7. **Tool** — the grind is a Codex worker under the brief.

## 10. Statement review (adversarial, before the grind)

Verdict **NEEDS-FIX → fixed** on this branch ([AGENT] fix worker, 2026-10-04). Findings:

- **B1** (blocking) — the freeze covered only the `_stmt` bodies: the glue definitions they call (`poolOut`,
  `DriverEvent.events`, `PoolClassOk`/`Terminal`/`FuelOut`/`Refusal`) could drift unseen (e.g. `PoolClassOk … :=
  True` made `pool_classification_stmt` trivial). Fixed: `scripts/check-pool-spec` adds the whole-file key
  `stmts-file` (`PoolStatement.lean`, comment-stripped, whitespace-normalised like `defs`), keeping the per-`_stmt`
  keys for naming; a self-test (negative control on a scratch copy) proves `PoolClassOk … := True` FAILS.
- **B2** (blocking) — a `_stmt` body ended at the first blank line, so `∨ True` after a blank line escaped its key.
  Fixed: a body runs to the next column-0 command token (an unrecognised column-0 line FAILS); a self-test proves the
  appended `∨ True` FAILS on both the file key and the statement's own key.
- **B3** (blocking) — §5 claimed replay by record was provided, and the logic team's 2026-09-23 §2(4) requires it,
  but no statement carried it. [AGENT] coordinator decision: ADD the replay statements rather than scope replay
  out. Added: `stepMulti_replay_stmt` (milestone 1), `continue_replay_stmt` and `poolPrefix_replay_stmt` (milestone
  4), elaborated as given, with `rfl` controls (7)–(8) in `PoolStatement.lean` (one instance of the step's replay on
  a two-goroutine boundary pool; the window draw's record).
- **M1** — `stepMulti_sound_stmt` collided in name with the existing trace-level `stepMulti_sound`; renamed
  `stepML_sound_stmt` everywhere.
- **M2** — §5 now says the run-level converse (`StepsML` → ∃ tape, `PoolPrefix`) is false as a bare statement.
- **M3** — `program_prefix_stmt`'s docstring now says it is one-directional and ok-only; the terminal/refusal program
  cases and the converse derive from `program_bridge` + the `pool_run_*_iff_stmt`s.
- **M4** — the comment stripper treated `--` inside a string literal as a comment; string and char literals are now
  copied verbatim (self-tested).
- **M5** — grind brief §6's edit list gains `docs/specs/pool-relation/Skeleton.lean`; §8 requires `git diff <input>
  -- GoLean/GoCore/PoolStatement.lean` EMPTY unless a §5 bounded adjustment is reported, its hunks confined to the
  named `_stmt` body.

`FROZEN.sha256` re-frozen after the fixes (48 statements + `defs` + `stmts-file`).
