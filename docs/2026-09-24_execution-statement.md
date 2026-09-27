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

**`FinishOutcome`** — `normal`/`deadlock`/`aborted t`/`refused r`, each carrying the endpoint store and residual
tape: discharges (1) (the proposal's `.aborted (Terminal)` lost both). `execStmtLoop`'s result is a projection.

**`Finish ctx s c ch rec o cost`** — four constructors: `normal` (cost 0), `blocked` (cost 0, the sequential
deadlock: single goroutine, no partner), `aborted` and `abortRefused` (cost 1). The abort constructors replay
`stepFn`'s `.panicking chain .stop` arm (`StepFn.lean:368`–`387`): the consult `abortConsult first rest ch =
Choices.consumeAt .repanicCollapse (repanicCollapseWidth first rest) ch` (`Machine.lean:3203`, width
`:3193`), then the fallible `abortMsg` (`Machine.lean:3908`). The Lean uses the record-emitting
`Choices.consumeAtE` (`State.lean:467`), linked by `Choices.consumeAtE_fst_snd` (`State.lean:475`) — cited, not
proved. `abortMsg`'s error is always a refusal (`throw (.unsupported …)`, `Machine.lean:3912`), so
`abortRefused` matches `.error (.refusal r)`. Discharges (2): a terminal transition with the final pick and
the rendering premise; a renderer refusal is REPORTED, never a silent stuck.

**`LRun`** — `∃ n sf cf chf cost, Prefix … ∧ Finish …`: DERIVED, not the carrier (response §2).
**`replays ctx s c ch ch₂ ch₂'`** — by the step's consumption projection `seqConsumption`
(`Machine.lean:5190`): `none` → the tape is untouched; `some (site, b)` → equal pick records and `ch₂'` the
replayed residual. At `b ≤ 1` both records are `[]` and nothing is popped (`Choices.consumeAtE_le_one`, `State.lean:485`); an empty tape
picks 0 (`Choices.consume`). Discharges (4)'s «replay by record».

**`NoRefusal ctx s c`** — no `Prefix`-reachable endpoint, from any initial tape, has `stepFn … = .error
(.refusal _)`, and no reachable abort's renderer errs under the pick its consult draws from the residual. The
domain premise of the corollary (5).

## Statements owed (packet B proves each `<name>_stmt` as `<name>`)

`prefix_refl_stmt`, `prefix_comp_stmt` (`n + m`, `ls ++ ls'`), `prefix_split_stmt`, `prefix_erase_steps_stmt`
(→ `Steps`, `Machine.lean:6157`), `prefix_erase_trace_stmt` (→ `Trace`), `prefix_iter_stmt` (↔ `stepFnIter`,
`StepFn.lean:1042`) — response §2's refl / composition / splitting / erasure / exact iteration agreement.
`finish_abort_step_stmt`, `finish_refused_step_stmt` — `Finish`'s abort constructors ARE `stepFn`'s abort
outcomes (2). `run_ok_iff_stmt` (today's `run_ok_iff`, `Trace.lean:60`, labelled), `run_panic_iff_stmt`,
`run_deadlock_iff_stmt`, `run_fuelOut_iff_stmt` — (3). `replay_coverage_stmt` — (4): no unrecorded
consultation affects a step; its pieces are `stepFn_consumption_none` (`MachineSound.lean:5785`) and
`stepFn_consumption_some` (`:6175`). `silent_projection_stmt` — a `[]` label contributes `[]` to the flatten
(post-reshape: `⟨[], [], []⟩` → `[]` per channel, response §3). `single_embedding_stmt` —
`execProgLoop_single` restated (`MultiSound.lean:666`). `program_bridge_stmt` — the program level (HELD, below).
Plus four boundary `_stmt`s (below).

**Packet B's first question.** `replay_coverage_stmt` omits the `c.appendTargetLocal` premise of
`stepFn_consumption_some` (`MachineSound.lean:6177`; `Machine.lean:4085`): whether it holds without it is B's to answer.

## The F2 cost accounting and the fuel convention (KEPT)

A `ZeroCost` endpoint is classified before the `fuel` match (cost 0); the abort is thrown INSIDE `stepFn`
(`StepFn.lean:386`), so it needs one more unit (cost 1). Completed-run bridges bound PREFIX LENGTH + FINISHING
COST (`n ≤ fuel` for normal/deadlock, `n + 1 ≤ fuel` for the panic); fuel-out is the fixed tape's actual prefix of
length exactly `fuel` ending at a NON-zero-cost configuration.

| Configuration | fuel 0 | fuel 1 | Lean |
|---|---|---|---|
| `.next .stop` | `.ok (s, ch)` | `.ok (s, ch)` | `example … := rfl` (witness) |
| blocked form | `.terminal .deadlock` | same | `boundary_blocked_zero_stmt` |
| abort, renderable | `.fuelOut` | `.terminal (.panic t)` | `example … := rfl` at 0 (witness); `boundary_abort_one_stmt` |
| abort, renderer refuses | `.fuelOut` | `.refusal r` | `boundary_refused_zero_stmt`, `boundary_refused_one_stmt` |

The `rfl` controls are the review witness's (`…/2026-09-23_batched-window-review/FuelBoundary.lean`), copied as
`example`s, `ctx`/`abortConfig` inlined; the four boundary names are [AGENT packet A worker] choices (the brief names none).

## Program level, and the RETAINED limitation

`program_bridge_stmt` (HELD — the last section): under `runProgramSetupM fuel p name args ch = .ok (pctx, c₀, s₀, locs, ch₁)`
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

## NOT stated — the ambiguity policy (flagged, not decided)

`classification_stmt` and `classification_wf_stmt` are OMITTED from the Lean file. The brief makes the
`.terminal` case «a `Finish` at `n + cost ≤ fuel`», but `Finish` has four constructors and none classifies the
UNRECOVERABLE terminal `.terminal (.fatal m)`, which `stepFn` raises at a NON-zero-cost configuration: the sync
apply throws `.fatal "sync: unlock of unlocked mutex"` (`Machine.lean:4392`; also `:4416`, `:4443`) and `toResult`
propagates every non-panic stop (`Value.lean:394`), so `execStmtLoop` returns `.error (.terminal (.fatal m))`
(corpus row family `sync/mutex-unlock-fatal`). Stated as briefed, both statements would be FALSE. Two readings,
materially different for the contract: **(A)** a fifth `Finish` constructor `fatal` (a `stepFn` call at the
endpoint raising `.terminal (.fatal m)`; outcome `fatal m s ch`; cost 1) — contradicts «FOUR constructors» and
the fixed name list; **(B)** keep `Finish` at four and add to the classification a fifth disjunct shaped like the
refusal case (a `Prefix` of length `n + 1 ≤ fuel` to a configuration whose `stepFn` raises a non-panic terminal).
The `[USER]`/coordinator chooses; packet B states the chosen form.

`program_bridge_stmt` is HELD (text elaborated, EXIT=0, kept verbatim in
`docs/evidence/2026-09-24_packet-a/held-program-bridge-stmt.lean.txt`): its `loadMany` mention is a NEW row for
`scripts/check-mem-callsites` (fast `ci` FAIL), and the brief forbids editing `scripts/`. Resolutions: **(A)** add
the row `GoLean/GoCore/ExecutionStatement.lean · program_bridge_stmt · loadMany · 1 · NO EXECUTION — …` to
`scripts/mem-callsites.tsv`, as `ProgramRun`'s own row (line 74) does; **(B)** restate the bridge through
`ProgramRun` (weaker: it hides the fold). Coordinator's call.

**What packet B proves:** every `_stmt` as `<name>` after row 2's reshape (re-stated over `StepLabel`), the held
items in the forms chosen, and the relabelled `stepFn_sound`/`step_complete`/`run_ok_iff`/`program_run_iff`/`observation_iff`.
