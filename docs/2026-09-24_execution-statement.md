# The execution statement, made exact (window charter §2; packet A deliverable ii-b)

[AGENT packet A worker] 2026-09-27. Brief: `docs/codex-briefs/2026-09-24_packet-A-contract.md` §5; charter
`docs/2026-09-23_batched-window-charter.md` §2 (rev. 2); the response's corrections (1)–(5)
(`docs/2026-09-23_response-from-logic-team.md` §2); the review's F2 (`docs/2026-09-23_batched-window-charter-review.md`).
Lean: `GoLean/GoCore/ExecutionStatement.lean` (statements only). `file:line` at input `5946adfa` (under `GoLean/GoCore/`;
`git diff --stat 3fb4a0d1 5946adfa -- GoLean/GoCore` is empty, so = the brief's `3fb4a0d1`). Nothing here is a decision.

**The label device.** Today's `stepFn` returns `Except Stop (Config × Store × Choices × AccessTrace)`
(`StepFn.lean:326`) and `Step` is 5-ary (`Machine.lean:5315`); the per-step label is an `AccessTrace`. Charter
row 2 replaces it by `StepLabel := { trace, picks, out }`; packet B re-states the file over it. LIMITATION,
documented not invented (response §3): the label is per-channel ordered, ordered across steps, with NO total
interleaving of the three channels inside one step.

## Definitions

**`ZeroCost` / `Blocked`** — the five arms `execStmtLoop` matches BEFORE `fuel` (`StepFn.lean:1016`–`1020`):
`.next .stop` and the four blocked forms (`Machine.lean:3839`–`3856`). Discharges F2 (a predicate for the zero-cost
classification, used negated in fuel-out) and part of (3).

**`Prefix ctx n s c ch ls sf cf chf`** — `n` executable steps, one `AccessTrace` per step, the tape threaded as
`stepFn` threads it; the labelled twin of `Trace` (`Trace.lean:15`). The PRIMARY carrier (response §2 opening);
arbitrary endpoints, so it holds independent of termination — (3)'s «earlier observations survive fuel-out and
divergence».

**`FinishOutcome`** — `normal`/`deadlock`/`aborted t`/`refused r`/`fatal m`, each carrying the endpoint store and residual
tape: discharges (1) (the proposal's `.aborted (Terminal)` lost both). `execStmtLoop`'s result is a projection.

**`Finish ctx s c ch rec o cost`** — FIVE constructors: `normal` (cost 0), `blocked` (cost 0, the sequential
deadlock: single goroutine, no partner), `aborted`, `abortRefused` and `fatal` (cost 1; `fatal` below). The abort constructors replay
`stepFn`'s `.panicking chain .stop` arm (`StepFn.lean:368`–`387`): the consult `abortConsult first rest ch =
Choices.consumeAt .repanicCollapse (repanicCollapseWidth first rest) ch` (`Machine.lean:3203`, width
`:3193`), then the fallible `abortMsg` (`Machine.lean:3908`). The Lean uses the record-emitting
`Choices.consumeAtE` (`State.lean:467`), linked by `Choices.consumeAtE_fst_snd` (`State.lean:475`) — cited, not
proved. `abortMsg`'s error is always a refusal (`throw (.unsupported …)`, `Machine.lean:3912`), so
`abortRefused` matches `.error (.refusal r)`. Discharges (2): a terminal transition with the final pick and
the rendering premise; a renderer refusal is REPORTED, never a silent stuck. **`fatal`** ([AGENT] coordinator
disposition 2026-09-27, Reading A — the brief's four constructors missed it): a `stepFn` call raising
`.terminal (.fatal m)` (sync misuse, `Machine.lean:4392`/`:4416`/`:4443`; `toResult`, `Value.lean:394`), cost 1,
endpoint store and tape, record `[]` ([AGENT packet A worker] reading: no consult precedes those throws).

**`LRun`** — `∃ n sf cf chf cost, Prefix … ∧ Finish …`: DERIVED, not the carrier (response §2).
**`replays ctx s c ch ch₂ ch₂'`** — by the step's consumption projection `seqConsumption`
(`Machine.lean:5190`): `none` → the tape is untouched; `some (site, b)` → equal pick records and `ch₂'` the
replayed residual. At `b ≤ 1` both records are `[]` and nothing is popped (`Choices.consumeAtE_le_one`, `State.lean:485`); an empty tape
picks 0 (`Choices.consume`). Discharges (4)'s «replay by record».

**`NoRefusal ctx s c`** — no `Prefix`-reachable NON-`ZeroCost` endpoint, from any initial tape, has `stepFn … =
.error (.refusal _)`, and no reachable abort's renderer errs under the pick its consult draws. The domain premise of
(5). ZeroCost excluded (audit F2): `stepFn` refuses at `.next .stop` (`StepFn.lean:850`), so the first form failed
on EVERY completing run; a positive control (`example`, a one-step completing run) now shows it holds there.

## Statements owed (packet B proves each `<name>_stmt` as `<name>`)

`prefix_refl_stmt`, `prefix_comp_stmt` (`n + m`, `ls ++ ls'`), `prefix_split_stmt`, `prefix_erase_steps_stmt`
(→ `Steps`, `Machine.lean:6157`), `prefix_erase_trace_stmt` (→ `Trace`), `prefix_iter_stmt` (↔ `stepFnIter`,
`StepFn.lean:1042`) — response §2's refl / composition / splitting / erasure / exact iteration agreement.
`finish_abort_step_stmt`, `finish_refused_step_stmt` — `Finish`'s abort constructors ARE `stepFn`'s abort
outcomes (2); `finish_replay_stmt` — the TERMINAL draw replays by record (audit F3; (4), response §6). `run_ok_iff_stmt` (today's `run_ok_iff`, `Trace.lean:60`, labelled), `run_panic_iff_stmt`,
`run_deadlock_iff_stmt`, `run_fuelOut_iff_stmt` — (3). `replay_coverage_stmt` — (4): no unrecorded
consultation affects a step; its pieces are `stepFn_consumption_none` (`MachineSound.lean:5785`) and
`stepFn_consumption_some` (`:6175`). `silent_projection_stmt` — a `[]` label contributes `[]` to the flatten
(post-reshape: `⟨[], [], []⟩` → `[]` per channel, response §3). `single_embedding_stmt` —
`execProgLoop_single` restated (`MultiSound.lean:666`) and `program_bridge_stmt` — both DEFINITIONAL (audit F5:
literally `execProgLoop_single`; `runProgramPoolOutM` unfolded) — pinned, NOT counted as bridges.
`classification_stmt` — (5), unconditional: exactly one of `ClassOk` / `ClassTerminal` (a `Finish` over the FIVE
constructors, `n + cost ≤ fuel`, `FinishOutcome.terminal? = some t`) / `ClassFuelOut` / `ClassRefusal` (a prefix of
`n + 1 ≤ fuel` to a refusing `stepFn` call, or `Finish.abortRefused`); exclusive by result shape.
`classification_wf_stmt` — under `StateWf ctx s ∧ NoRefusal ctx s c`, the first three only. Four boundary `_stmt`s.

`replay_coverage_stmt` omits `stepFn_consumption_some`'s `c.appendTargetLocal` premise (`MachineSound.lean:6177`);
the proof already drops it («`hloc` is no longer needed here», `:6243`; audit F4) — expected TRUE, unproven.

## The F2 cost accounting and the fuel convention (KEPT)

A `ZeroCost` endpoint is classified before the `fuel` match (cost 0); the abort is thrown INSIDE `stepFn`
(`StepFn.lean:386`), so it needs one more unit (cost 1). Completed-run bridges bound PREFIX LENGTH + FINISHING
COST (`n ≤ fuel` for normal/deadlock, `n + 1 ≤ fuel` for the panic and the fatal); fuel-out is the fixed tape's actual prefix of
length exactly `fuel` ending at a NON-zero-cost configuration.

| Configuration | fuel 0 | fuel 1 | Lean |
|---|---|---|---|
| `.next .stop` | `.ok (s, ch)` | `.ok (s, ch)` | `example … := rfl` (witness) |
| blocked form | `.terminal .deadlock` | same | `boundary_blocked_zero_stmt` |
| abort, renderable | `.fuelOut` | `.terminal (.panic t)` | `example … := rfl` at 0 (witness); `boundary_abort_one_stmt` |
| abort, renderer refuses | `.fuelOut` | `.refusal r` | `boundary_refused_zero_stmt`, `boundary_refused_one_stmt` |
| `Unlock` of an unlocked mutex | `.fuelOut` | `.terminal (.fatal …)` | two `example … := rfl` (a one-cell witness) |

The `rfl` controls are the review witness's (`…/2026-09-23_batched-window-review/FuelBoundary.lean`), copied as
`example`s, `ctx`/`abortConfig` inlined; the four boundary names are [AGENT packet A worker] choices (the brief names none).

## Program level, and the RETAINED limitation

`program_bridge_stmt` (stated per the [AGENT] coordinator disposition 2026-09-27; its `loadMany` mention recorded
in `scripts/mem-callsites.tsv` as «NO EXECUTION», like `ProgramRun`'s row): under `runProgramSetupM fuel p name args ch = .ok (pctx, c₀, s₀, locs, ch₁)`
(`StepFn.lean:1181`) — setup's tape `ch → ch₁` INCLUDED — `runProgramPoolOutM` (`Multi.lean:2055`) is the
`execProgLoopOut pctx fuel ⟨#[.running c₀ none], s₀, 0⟩ {} ch₁ GoString.empty` fold (`Multi.lean:1923`) with the
`loadMany pctx sf locs` readout (`Machine.lean:771`), exactly `ProgramRun`'s `runError`/`readError`/`done`
(`ProgramTrace.lean:14`). Init OUTPUT is empty BY REFUSAL: `runInitConfig` refuses a print position
(`initPrintRefusal?`, `StepFn.lean:1118`; `:1133`) — RETAINED per decision 10 (response §3: «otherwise retain the
named limitation»). The single-goroutine embedding's cost relation IS `seqOpCount` (`MultiSound.lean:640`), one
extra pool step per completed registry op — never «equal fuel». The pool half waits (charter §2).

**THE LIMITS, stated in the offer and in any CLAUDE.md edit** (review): the program bridge ASSUMES successful
setup, RETAINS the init-print refusal, DEFERS pool/registry coverage; the restricted sequential result does NOT
discharge the whole owed simulation.

## Dispositions ([AGENT] coordinator, 2026-09-27; disclosed at the merge ask)
Two items packet A had STOPPED: (1) the four-constructor `Finish` missed `.terminal (.fatal m)` — Reading A (a fifth
constructor, cost 1: «a fatal is a classified terminal, not a refusal») over B (a fifth disjunct); (2)
`program_bridge_stmt` — Reading A (the inventory row; `scripts/` lifted for it) over B (via `ProgramRun`).
Audit round (2026-09-27): F2, F3 fixed; F4, F5, F6 recorded; F1 resolved (below). Packet B proves every `_stmt`
as `<name>` after row 2's reshape (over `StepLabel`).
**Audit F1 — resolved by `core/stray-panic-refusal-0927`** (disposition (b), [AGENT] coordinator, disclosed at the
merge ask; `docs/2026-09-27_stray-panic-refusal.md`): `stepFn` raised the Go PANIC terminal at a NON-abort
configuration (a binding-cell read, `Mem.loadFor` → `arrayGet`), unclassified by `Finish`, refuting
`finish_abort_step_stmt`, `run_panic_iff_stmt`, `classification_stmt`, `classification_wf_stmt`. The core lane's
root-only reader `loadRoot` refuses a non-root binding location as `.internal "binding cell is not a root location: …"`.
The statements are UNCHANGED; the auditor's witness now evaluates to that refusal and is PROVED `ClassRefusal`, not
`ClassTerminal` (`docs/evidence/2026-09-24_packet-a/F1Witness.lean`). (Rejected: (a) widen `Finish`; (c) unwind.)
