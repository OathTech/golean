import GoLean.GoCore.Trace
import GoLean.GoCore.ProgramTrace
import GoLean.GoCore.MultiSound
import GoLean.GoCore.Prefix
import GoLean.GoCore.Locals
import GoLean.GoCore.StringPanic
import GoLean.GoCore.Equations
import GoLean.GoCore.PoolProjection
import GoLean.GoCore.PoolSound
import GoLean.GoCore.SetupSound

/-!
# The stable bridge set — pinned statements (window charter row 0)

[AGENT packet A worker] 2026-09-27, under «The window charter (rev. 2) and the Codex
packaging — RULED (2026-09-24)» (decision 2) and the execution-model ruling of 2026-09-27
(`docs/2026-08-31_qrow-rulings.md`); charter `docs/2026-09-23_batched-window-charter.md`
row 0; the proposal's §4-i (`docs/2026-09-23_proposal-to-logic-team.md`).

ONE `example` per member pins the member's TYPE, binders written out: if a pinned
statement drifts, THIS FILE FAILS THE DEFAULT BUILD (it is imported by `GoLean.lean`).
Rows 1–21 are the proposal §4-i's 21 names; rows 22–24 (`stepFn`, `stepFnIter`,
`iter_iff_trace`) are the logic team's response §6 bullet 1's settled names — an [AGENT]
addition (window plan §3.2). Each type was confirmed with `#check @<name>` at `main` @
`5946adfa` before it was written here.

RE-PIN 1 — the row-2 label reshape ([AGENT worker, lane core/step-label-0928], 2026-09-28;
design note `docs/2026-09-28_step-label.md`): rows 1, 2, 13, 15, 22 re-pinned over the full
event label `StepLabel` (the step's label was `AccessTrace`; `enterFramePick` now also
returns its kept pick records); rows 25–34 ADDED — the label type, its fold and silent
projection, the pool event over the same label, the record helper, and the pool
projection theorem. Line numbers refreshed at the reshape tip.

RE-PIN 2 — packet B, the execution bridges ([AGENT packet B worker], 2026-09-28; handoff
`docs/2026-09-28_packet-b-handoff.md`): row 34 strengthened (label-reshape audit F1); rows
35–64 ADDED — the 23 proved `_stmt` theorems (statements written out) and seven supporting facts.

RE-PIN 3 — G-P S2, native method promotion ([AGENT worker, lane core/method-promotion-0928],
2026-09-28; design note `docs/2026-09-28_gp-method-promotion-design.md` §5 S2 — decisions 4 and 9
ruled [USER] 2026-09-28, relayed; handoff `docs/2026-09-28_method-promotion-handoff.md`): rows 11
and 15 re-pinned over the entry OUTCOME `Entry` (`run func frameEnv resultLocs | again fid args`
— a promotion path ending in an embedded interface field re-dispatches as a SEPARATE step, design
§2 S5; the five-tuple `Func × LocalEnv × List Loc × Store × AccessTrace` became
`Entry × Store × AccessTrace`); row 13 re-pinned: `Cont.frame`'s trailing `wrapper : Bool` field
was DELETED and the frame's callee `FuncId` ADDED in its place ([USER] Mike 2026-09-28 «Agree on
(1)», the logic team's request 6 option 1, relayed), so `stepFrameExit`'s `Bool` binder is a
`FuncId`. Rows 65–67 ADDED — `Entry.callConfig_run` (the frame a call position pushes names the
resolved callee), `frame_exit_returns` (a frame exit reads «`fid` returned `vs`») and
`enterFrame_declared` (a declared callee's entry IS the function-call rule: design §3, charter row 3).

RE-PIN 4 — G-P S3, the equation lemmas ([AGENT] S3 sub-worker, lane core/method-promotion-0928,
2026-09-29; design note §3 «the named set below, delivered with P»; handoff §1 S3): rows 68–89 ADDED,
nothing re-pinned — the lookup characterizations (`methodDecl?_some`, `promotion?_some`), the
resolution equations (`resolveMethod?_declared` / `_ptrDeclared` / `_promoted` / `_promotedPtr`),
the path-walk equations (`receiverAt_nil_path` and its `deref` half, `receiverAt_nil_panic`,
`receiverAt_field` and its projection/`addr` forms, `receiverAt_ptr` and its `deref`/nil forms), the
recover rule (`recoverResult_eq`, `_frame`, `_glue`) and the domain-narrowing bridge for a client's
`findFunctionIn?` premise (`findFunctionIn?_filter`, `_filter_none` — the logic team's request 5 of
2026-09-28, relayed; [AGENT] coordinator disposition). Row 67 (`enterFrame_declared`) confirmed.

RE-PIN 5 — G-C3, `Cont := List Frame` ([AGENT packet C worker], lane core/continuations-0929,
2026-09-29; G-C3 passed [USER] Mike 2026-09-29 «Agree with 1-4», relayed; design note
`docs/2026-09-29_gc3-continuations-design.md` D5/D6): rows 1–89 elaborate BYTE-IDENTICAL — every
pinned statement mentions `Cont` and its constructors only through the type name and the
`@[match_pattern]` views (`.stop`, `.frame …`, `.panicResumeK …`), which keep their names and
argument order, so no row was re-pinned. Rows 90–107 ADDED: the shape (`Cont = List Frame`) and the
walks as list laws — `Cont.rebuild` (cons/nil), `pushDefer` («map at the first call frame» and its
converse, plus the per-head cases), `seqCont`, `panicPassthrough`, `recoverResult` over `[]` and a
glue head, frame exit at `.next` and at an empty frame, and the sup's cons law.

The set is RE-PINNED per window row; every change to this file is a changelog line
(`docs/changelog/61958f2e-WINDOW.md`), so the file's diff between two pins IS the
interface diff.

THE DEVICE'S LIMIT: definitional equality ignores binder annotations, so a drift between
an implicit `{x}` and an explicit `(x)` binder is NOT caught; nor is a changed definition
with an unchanged type (that is the semantic-equation file's job, charter row 7).

`Trace.lean` is imported explicitly: neither `ProgramTrace` nor `MultiSound` reaches it.

RE-PIN 6 — B6, numeric locals ([AGENT worker, lane core/numeric-locals-0930], 2026-09-30; design
note `docs/2026-09-30_numeric-locals-design.md`; the logic team's request 3 of 2026-09-28): rows 1–107
BYTE-IDENTICAL (no pinned statement spells a local — `LocalEnv`, `Param`, `Expr` keep their names;
their local positions are now `VarId := Nat`); rows 108–125 ADDED — the local id and the binder
positions that became numeric (`Param.id`, `Expr.var`/`ref`, `Assignee.var`, `Scope`), the name table
(`LocalKind`, `LocalName`, `Func.locals`, `Func.localName?`), the decoder's checked predicate
`Func.localsOk` with its two lemmas, the env-lookup laws, and the activation-slot lemmas
(`bindParams_lookup`, `allocDecls_lookup`, `enterFrame_lookup_arg`/`_result`). FIX ROUND
(2026-09-30, the audit's F1/F3; [USER] Mike «Agree, go ahead and fix, agree on all 6», relayed):
row 116 re-pinned over the two-way check (`tableCovers && tableNamed && sigDistinct && argKinds &&
resultKinds && recvFirst && bodyKinds`) with its three part equations; rows 126–132 ADDED — table ⊆
tree, the kind lookup, the four kind lemmas, and the `unseqEnter` rule with its id-level entry
premise (`unseqEntryCheck?`).

RE-PIN 7 — window unit 5b, the native `Intn`-style pick site ([AGENT worker, lane core/intn-pick-0930],
2026-09-30; [USER] Mike, item 2 of «The raft-proofs team's subject-delta note (2026-09-30) — RULED», relayed;
design note `docs/2026-09-30_intn-pick-design.md`, D7): rows 1–132 BYTE-IDENTICAL (no pinned statement
enumerates `ChoiceSite`, `Stmt` or `StmtOp` — the new constructors `ChoiceSite.intn`, `Stmt.randIntn`,
`StmtOp.randIntn` widen the types without moving a row); rows 133–135 ADDED — the draw's apply EQUATION
(`applyStmtOp_randIntn_eq`: the tape's `intn` pick at bound `n` is stored, the record is
`PickRecord.ofPick .intn n.toNat pick`), the draw's STEP RULE derived from `stmtOpApply`
(`Step_randIntn_draw`: every `i < n` is realized by the singleton tape, its label's picks = its replay
record), and the pick-lifted plan at a popping bound (`applyStmtOp_plan_randIntn_draw`, the form the
coverage proofs consume). The site records exactly like the others: `replay_coverage` (row 48),
`stepFn_picks_none` / `_some` (rows 62–63) hold unchanged.

RE-PIN 8 — window row 6, C4 block-entry allocation ([AGENT worker, lane core/block-allocation-1001],
2026-10-01; G-C4 PASSED [USER] Mike 2026-10-01 «Those costs seem fine to me. Go ahead with these decisions. You
can work on block allocation on the basis of approving all of your recommendations.», relayed; design note
`docs/2026-10-01_gc4-block-allocation-design.md` §4 D8; handoff `docs/2026-10-01_block-allocation-handoff.md`):
rows 1–131 and 133–135 BYTE-IDENTICAL (`Stmt.initialization` / `Step.initialization` were pinned nowhere; no
pinned statement enumerates `Stmt`); row 132 RE-PINNED — decision 3, D3 (b): the `unseqEnter` rule allocates the
binder cells over `env.pushScope` (a sweep-private scope) and its continuation keeps the source environment
(`.seq rest env k`, was `.seq rest env' k`), so a `Frame.seq`'s environment is fixed from creation to pop with no
exception. Rows 136–154 ADDED — the D8 acceptance list: the layout function `entrySlot s i = .base ⟨s.heap.size + i⟩`
for BOTH entries, the block-entry rule `Step.block`, `blockEntry_shift` / `_lookup` / `_lookup_outer` /
`_zero`, the two freshness halves (`entrySlot_not_allocated`, `blockEntry_fresh`), block exit as the rule
`Step.seqDone` and the executable equation `blockExit_store_eq`, `heap_size_mono` (the wf_loc conjunct, named),
`enterFrame_shift`, `frameEntry_lookup_arg` / `_result` (rows 124–125 restated through `entrySlot`),
`frameEntry_fresh`, and the D7 pair `pushDefer_saves_values` / `funcVal_captures_locs` beside `Step.evalRef`.

RE-PIN 9 — window unit 6b, BUG-004 item 4: the PREPRINT PHASE ([AGENT worker, lane core/panic-preprint-1003],
2026-10-03; RULED [USER] Mike 2026-09-30 «Yes, agree, do the fix inside this window», relayed — design note
`docs/2026-09-30_bug004-item4-design.md` §2 (i), all §5 decisions as recommended; handoff
`docs/2026-10-03_panic-preprint-handoff.md`): NO pinned STATEMENT changes text — rows 1–154 BYTE-IDENTICAL; row 19
(`Config.abort?`) keeps its type, its EQUATION gains the settled conjunct (`Config.abort?_some_iff`, row 155).
SHAPE changes a client's exhaustive case split meets: `PanicEntry` gains `rewrite : Rewrite` and `repanicked : Bool`
(both defaulted — `{ value, recovered }` instances elaborate; the anonymous `⟨v, false⟩` does not), `Frame` gains
`preprintK older entry newer` (33 frames), `Step` gains seven rules (`preprintCollapse`/`preprintDistinct`/
`preprintSelect`/`preprintResolve`/`preprintReturn`/`preprintFall`/`preprintStore`, 127 → 134), `FrameClass` gains
`preprint`. Rows 155–173 ADDED: the abort's characterization over the SETTLED chain, the split's two facts, the
rendering equations the logic side asked for (`renderPanicHead_text`/`abortMsg_text`/`stepFn_text_abort`/
`runConfig_text_abort` and the refusal twins — the `StringPanic` string lemmas' shape with `first.rewrite = .done text`
as the payload premise), the seven rules' types, and the relation-side elimination facts (`step_abort_elim` now takes
the settled premise; `step_stop_unsettled`).

RE-PIN 10 — window packet D, the semantic EQUATIONS and the pool PROJECTIONS ([AGENT packet D worker],
branch `window/packet-d-equations-1003`, 2026-10-03; brief `docs/codex-briefs/2026-09-24_packet-D-equations.md`
as amended 2026-09-28/30; handoff `docs/2026-10-03_packet-d-handoff.md`): rows 1–173 BYTE-IDENTICAL; row 62
RE-TARGETED (its statement unchanged) from the deleted `PrefixFacts.stepFn_consumption_some'` to
`MachineSound.stepFn_consumption_some`, now itself premise-free (packet B audit F3 folded back). Rows 174–402
ADDED — every theorem of `GoLean/GoCore/Equations.lean` (the per-arm `stepFn` equations over a symbolic store,
environment, continuation and tape with explicit operation premises; the `stepFn_eqns` rewrite set; the root-cell
read/write laws; the unwinding equations of the logic team's request 7 over the preprint phase's arms; the
frame-exit equations of the continuations audit's F4; the pinned SETUP EQUATION of request 2 with the
argument/result layout). Rows 403–436 ADDED — `GoLean/GoCore/PoolProjection.lean` (packet B audit F5): the
single-goroutine OUTPUT AGREEMENT (`execProgLoopOut_single`, over `Prefix` labels `execProgLoopOut_single_prefix`),
the SEQUENTIAL-TO-POOL TERMINAL PROJECTION (`execProgLoop_single_terminal`, `execProgLoop_single_wide` over
`transferableWide`), and the embedding without the `seqOpCount = 0` premise (request 9:
`execProgLoop_single_noBoundary`). The rows of this re-pin are GENERATED from the two files' theorem headers
(binders written out, `∀ {ctx : ProgramCtx}` first where the statement mentions the context); the client
`Tests/EquationClient.lean` pins every equation statement a second time and checks the set exhaustive.
PRE-LANDING ROUND (packet D audit, MERGE-CLEAN with follow-ups; [AGENT] coordinator dispositions 2026-10-03):
rows 1–436 BYTE-IDENTICAL; rows 437–499 ADDED — `Equations.lean`'s appended section (audit F3: the sync
apply's panic twin `retV_syncStK_apply_panic`; the composed applies' and entries' NON-PANIC `Stop` pass-throughs
`*_apply_error`/`*_enter_error`/`next_storeK_error`/…; the refusal arms stated by shape — the `valueAsBool`
refusals, the non-deferrable callees, the drains' non-function callees, the preprint non-string result, `storeK`'s
arity breaches; the `signalStep` table completed, labelled `brkTo`/`contTo` and the `mapIterK` rows; the helpers
`bind_eq_error`, `runCommit_error`, `enterFramePickV_of_plan_error`, `enterFrame_inv_error`, `valueAsBool_nonbool`,
`deferrableCallee_false`, `contHeadLabel_*`); rows 500–501 ADDED — `PoolProjection.lean`'s
`execProgLoop_single_noBoundary_wide`/`execProgLoopOut_single_noBoundary_wide` (audit F4: the equal-fuel embedding
over `transferableWide`). The arm equations are now PROPOSITIONAL (`defn_eq`, no `rfl`-proof) so a client's proof
term records them (audit F2); their STATEMENTS are unchanged.
WINDOW-REVIEW ROUND (`docs/2026-10-03_window-review.md` F1; [AGENT packet D worker] 2026-10-03): rows 1–501
BYTE-IDENTICAL; row 502 ADDED — the boxing law `applyStrictOp_toInterface_string` (`any("…")` is the interface
value at the canonical dynamic type `string`, read-only, trace-free), the law the client's rewritten FACT 3
(a callee's BOXED string panic unwinding past the caller's write) bottoms out in.

RE-PIN 11 — pool grind M1 (Codex, `844e9393`, train r66; [AGENT train worker] 2026-10-05, merge sign-off
[USER] Mike 2026-10-05 «(1) Go ahead, (2) merge once ready», relayed): rows 1–502 BYTE-IDENTICAL; rows 503–511
ADDED (the nine M1 statements of `PoolStatement.lean`, proved in `PoolSound.lean`).

RE-PIN 12 — the SETUP EQUATIONS, the logic team's G-R1–G-R3 ([AGENT worker, lane
`core/setup-equations-1005`], 2026-10-05; [USER] Mike 2026-10-05 «(1) Go ahead», relayed; the request
verbatim `docs/2026-10-05_note-from-logic-team-setup-equations.md`; the lane's note
`docs/2026-10-05_setup-equations.md`): rows 1–511 BYTE-IDENTICAL; rows 512–520 ADDED — the nine
`_stmt`s of `SetupStatement.lean` proved in `SetupSound.lean`, written out: G-R2 `seedGlobals_cells`
(the seeded heap IS the zero cells in order, one `Except` equation), `seedGlobals_cell` (global `i` at
`.base ⟨i⟩`), `seedGlobals_heap_size`, `seedGlobals_wf` (unconditional); G-R1 `runProgramSetup_init`
(seeding, init and the entry bind as one rewrite — no `StateWf` premise, discharged by `seedGlobals_wf`);
G-R3 `setup_lookup_arg_from` / `setup_lookup_result_from` / `setup_resultLocs_from` /
`setup_heap_size_from` (the `{}`-store lemmas over an arbitrary pre-bind store, at `entrySlot s₁`).
Rows 397 and 399–402 (`runProgramSetup_noInit`, the `{}` forms) are UNCHANGED — their instances.
G-R4 (`SetupStatement.runInitConfig_eq_execStmtLoop_stmt`) is a STATEMENT ONLY, not pinned here: its
text is out for the logic team's review before it is proved (superseded by RE-PIN 13: G-R4 proved and
pinned, rows 521–527).

RE-PIN 13 — G-R4 APPROVED and proved, with the logic team's four answers ([AGENT worker, lane
`core/setup-equations-1005`], 2026-10-05; the golean-logic coordinator's reply of 2026-10-05, by
cross-session message, relayed by the [AGENT] coordinator — verbatim in `docs/2026-10-05_setup-equations.md`
§3): rows 1–520 BYTE-IDENTICAL; rows 521–527 ADDED — row 521 `runInitConfig_eq_execStmtLoop` (G-R4 with the
no-blocked premise DROPPED, answer (a); the guard spelling `initPrintRefusal? c' = none` and the bound
`n ≤ fuel` kept, answer (b)); rows 522–525 the `run_*_iff` corollaries for the init loop under the no-print
premise — `runInitConfig_ok_iff` / `_panic_iff` / `_deadlock_iff` / `_fuelOut_iff`, the same right-hand sides
as rows 44–47's sequential statements (answer (c)); rows 526–527 the `runPkgInitM` wrapper — `runPkgInitM_some`
(`runPkgInitM` with `$pkginit` present IS `runInitConfig` on the init configuration under
`Except.mapError markInitPhase`) and its success link `runPkgInitM_ok_iff`, the form G-R1's premise composes
with (answer (d)). All proved in `SetupSound.lean`; statements in `SetupStatement.lean`.

RE-PIN 14 — pool grind M2–M5 (Codex, `7626aa73`, train r70; [USER] «Agree on 1 / 2», relayed): rows 1–527
BYTE-IDENTICAL; rows 528–566 ADDED (the 39 M2–M5 statements of `PoolStatement.lean`, proved in
`PoolSound.lean`); all 48 pool statements now pinned (503–511, 528–566).

RE-PIN 15 — exported struct field offsets, the gc-verified team's request (a1) ([AGENT worker, lane
`lane/field-offsets-inittask-1007`], 2026-10-07; [USER] Mike 2026-10-07 «1-4 approved as proposed»,
relayed): rows 1–566 BYTE-IDENTICAL; rows 567–572 ADDED (`Ops.lean`, pure addition — no existing
definition's body or statement changed): row 567 `structLayoutWith_sizeAlign` (the layout loop's
`(size, align)` projection IS `structSizeAlignWith`, error included); row 568 `structLayoutWith_fields`
(one offset per field; each aligned to its field's alignment, at or after the start, ending within the
struct size); row 569 `structLayoutWith_disjoint` (non-overlap in field order); row 570
`tyStructLayoutAt_sizeAlign` (the struct arm of `tySizeAlignAt` is the layout's projection); row 571
`tyStructLayout_ok_sizeAlign` (the entry point's size/alignment are `tySizeAlign`'s); row 572
`tyStructLayout_fields` (the entry point's per-field facts against `tySizeAlign` of each field's type).

RE-PIN 16 — the r72 audit's layout follow-ups (f1)/(f2) ([AGENT worker, lane `lane/argbool-layout-1007`],
2026-10-07; [USER] Mike 2026-10-07 «Agree», relayed): rows 1–572 BYTE-IDENTICAL; rows 573–579 ADDED
(`Ops.lean`, pure addition): row 573 `tyStructLayout_disjoint` (non-overlap at the entry point, against
`tySizeAlign` of each field's type; (f1)); row 574 `structLayoutWith_align_ge` (the struct alignment is at
least the seed and every field's oracle alignment — unconditional); row 575 `structLayoutWith_align_dvd`
(field alignment ∣ struct alignment, under a power-of-two field oracle and seed); row 576
`structLayoutWith_size_dvd` (from a positive seed, the struct alignment is positive and divides the size);
row 577 `tyStructLayout_size_dvd` (alignment ∣ size at the entry point, EVERY platform — zero-size final
field and `struct{}` = `(0, 1)` included); row 578 `tyStructLayout_align_dvd` (field alignment ∣ struct
alignment at the entry point, under `Platform.PowTwoAligns`); row 579 `gcAmd64_powTwoAligns` (gc's platform
satisfies it). «field alignment ∣ struct alignment» is FALSE without the power-of-two premise (a 48-bit-`int`
platform: `struct{a int32; b int}` aligns at 6; the `Ops.lean` control), hence the premise in rows 575/578.
-/

namespace GoLean.GoCore.BridgeSet

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Semantics GoLean.Semantics.Pool
open GoLean.GoCore.ExecutionStatement (Prefix Finish FinishOutcome Blocked ZeroCost NoRefusal replays
  ClassOk ClassTerminal ClassFuelOut ClassRefusal)

-- 1. `MachineSound.lean:1685`
example : ∀ {ctx : ProgramCtx} {s : Store} {c : Config} {ch : Choices} {c' : Config} {s' : Store}
    {ch' : Choices} {tr : StepLabel},
    stepFn ctx s c ch = .ok (c', s', ch', tr) → Step ctx c s c' s' tr :=
  @GoLean.GoCore.Machine.stepFn_sound

-- 2. `MachineSound.lean:2103`
example : ∀ {ctx : ProgramCtx} {c : Config} {s : Store} {c' : Config} {s' : Store}
    {tr : StepLabel},
    Step ctx c s c' s' tr → ∃ ch ch' : Choices, stepFn ctx s c ch = .ok (c', s', ch', tr) :=
  @GoLean.GoCore.Machine.step_complete

-- 3. `Trace.lean:60`
example : ∀ {ctx : ProgramCtx} {fuel : Nat} {s : Store} {c : Config} {ch : Choices} {sf : Store}
    {chf : Choices},
    execStmtLoop ctx fuel s c ch = .ok (sf, chf) ↔
      ∃ n, n ≤ fuel ∧ Trace ctx n s c ch sf (.next .stop) chf :=
  @GoLean.Semantics.run_ok_iff

-- 4. `Trace.lean:42`
example : ∀ {ctx : ProgramCtx} {n : Nat} {s : Store} {c : Config} {ch : Choices} {sf : Store}
    {cf : Config} {chf : Choices},
    Trace ctx n s c ch sf cf chf → Steps ctx c s cf sf :=
  @GoLean.Semantics.Trace.erase

-- 5. `MultiSound.lean:666`
example : ∀ {ctx : ProgramCtx} {fuel : Nat} {σ : Store} {c : Config} {ch : Choices}
    {rs : RaceState} {r : Except Stop (Store × Choices)},
    execStmtLoop ctx fuel σ c ch = r → transferable r →
      execProgLoop ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch = r :=
  @GoLean.GoCore.Machine.execProgLoop_single

-- 6. `Multi.lean:1980`
example : ∀ {ctx : ProgramCtx} (fuel : Nat) (m : MultiConfig) (r : RaceState) (choices : Choices)
    (acc : GoString),
    (execProgLoopOut ctx fuel m r choices acc).2 = execProgLoop ctx fuel m r choices :=
  @GoLean.GoCore.Machine.execProgLoopOut_snd

-- 7. `ProgramTrace.lean:30`
example : ∀ {fuel : Nat} {p : Program} {name : String} {args : Array GoValue} {ch : Choices}
    {result : RunResult},
    runProgramPoolOutM fuel p name args ch = result ↔ ProgramRun fuel p name args ch result :=
  @GoLean.Semantics.Pool.program_run_iff

-- 8. `ProgramTrace.lean:79`
example : ∀ {p : Program} {name : String} {args : Array GoValue} {obs : Observation},
    (∃ fuel ch, observationOf (runProgramPoolOutM fuel p name args ch) = some obs) ↔
      ∃ fuel ch result, ProgramRun fuel p name args ch result ∧ observationOf result = some obs :=
  @GoLean.Semantics.Pool.observation_iff

-- 9. `StepFn.lean:1194`
example : Nat → Program → String → Array GoValue → optParam Choices [] →
    Except Stop (ProgramCtx × Config × Store × List Loc × Choices) :=
  @GoLean.GoCore.Machine.runProgramSetupM

-- 10. `Machine.lean:771`
example : ProgramCtx → Store → List Loc → Except Stop (List GoValue) :=
  @GoLean.GoCore.Machine.loadMany

-- 11. `Machine.lean` `enterFrame` (RE-PIN 3: the outcome is `Entry`)
example : ProgramCtx → Store → FuncId → List GoValue →
    Except Stop (Entry × Store × AccessTrace) :=
  @GoLean.GoCore.Machine.enterFrame

-- 12. `Machine.lean:3700`
example : List Stmt → LocalEnv → Cont → Cont :=
  @GoLean.GoCore.Machine.seqCont

-- 13. `StepFn.lean` `stepFrameExit` (RE-PIN 3: the frame's `FuncId`, not a wrapper `Bool`)
example : ProgramCtx → Store → List (TargetShape × List Expr) → LocalEnv → List Loc →
    List (GoValue × List GoValue) → Cont → FuncId → Choices →
    Except Stop (Config × Store × Choices × StepLabel) :=
  @GoLean.GoCore.Machine.stepFrameExit

-- 14. `Machine.lean:3781`
example : Cont → GoValue × Cont :=
  @GoLean.GoCore.Machine.recoverResult

-- 15. `Machine.lean` `enterFramePick` (RE-PIN 3: the outcome is `Entry`)
example : ProgramCtx → Store → FuncId → List GoValue → Choices →
    Except Stop (Result (Entry × Store × AccessTrace) × Choices ×
      List PickRecord) :=
  @GoLean.GoCore.Machine.enterFramePick

-- 16. `Machine.lean:3725`
example : GoValue × List GoValue → Cont → Option Cont :=
  @GoLean.GoCore.Machine.pushDefer

-- 17. `StepFn.lean:1018`
example : ProgramCtx → Nat → Store → Config → Choices → Except Stop (Store × Choices) :=
  @GoLean.GoCore.Machine.execStmtLoop

-- 18. `Machine.lean:6220`
example : ProgramCtx → Config → Store → Config → Store → Prop :=
  @GoLean.GoCore.Machine.Steps

-- 19. `Machine.lean:3895`
example : Config → Option (PanicEntry × List PanicEntry) :=
  @GoLean.GoCore.Machine.Config.abort?

-- 20. `Syntax.lean:1003`
example : Array Func → FuncId → Option Func :=
  @GoLean.GoCore.findFunctionIn?

-- 21. `Ops.lean:837`
example : ProgramCtx → FuncId → Option MethodInfo :=
  @GoLean.GoCore.methodInfoByFuncId?

-- 22. `StepFn.lean:329` (response §6 bullet 1)
example : ProgramCtx → Store → Config → Choices →
    Except Stop (Config × Store × Choices × StepLabel) :=
  @GoLean.GoCore.Machine.stepFn

-- 23. `StepFn.lean:1048` (response §6 bullet 1)
example : ProgramCtx → Nat → Store → Config → Choices → Except Stop (Config × Store × Choices) :=
  @GoLean.GoCore.Machine.stepFnIter

-- 24. `Trace.lean:22` (response §6 bullet 1)
example : ∀ {ctx : ProgramCtx} {n : Nat} {s : Store} {c : Config} {ch : Choices} {sf : Store}
    {cf : Config} {chf : Choices},
    stepFnIter ctx n s c ch = .ok (cf, sf, chf) ↔ Trace ctx n s c ch sf cf chf :=
  @GoLean.Semantics.iter_iff_trace

/-! ## Re-pin 1 additions — the step label (rows 25–34) -/

-- 25. `Ops.lean:1878` — the full event label: three ordered channels, no interleaving
example : AccessTrace → List PickRecord → List GoString → StepLabel :=
  @GoLean.GoCore.StepLabel.mk

-- 26. `Ops.lean:1889` — the observation: the per-field fold
example : List StepLabel → StepLabel :=
  @GoLean.GoCore.StepLabel.fold

-- 27. `Ops.lean:1895` — the silent projection (a pure step contributes nothing)
example : ∀ (ls₁ ls₂ : List StepLabel),
    StepLabel.fold (ls₁ ++ ⟨[], [], []⟩ :: ls₂) = StepLabel.fold (ls₁ ++ ls₂) :=
  @GoLean.GoCore.StepLabel.fold_silent

-- 28. `Machine.lean:5374` — the relation over the label
example : ProgramCtx → Config → Store → Config → Store → StepLabel → Prop :=
  @GoLean.GoCore.Machine.Step

-- 29. `Multi.lean:1029` — the pool event over the SAME label
example : Nat → StepAction → StepLabel → StepEvent :=
  @GoLean.GoCore.Machine.StepEvent.mk

-- 30. `State.lean:478` — the records a consultation emits (none at bound ≤ 1)
example : ChoiceSite → Nat → Nat → List PickRecord :=
  @GoLean.GoCore.PickRecord.ofPick

-- 31. `State.lean:482` — `consumeAtE` is `consumeAt` plus the pick's records
example : ∀ {site : ChoiceSite} {bound : Nat} {ch : Choices},
    Choices.consumeAtE site bound ch
      = ((Choices.consumeAt site bound ch).1, (Choices.consumeAt site bound ch).2,
         PickRecord.ofPick site bound (Choices.consumeAt site bound ch).1) :=
  @GoLean.GoCore.Choices.consumeAtE_eq

-- 32. `Machine.lean:4105` — a wide statement's output (`print`/`println` bytes)
example : StmtOp → List GoValue → List GoString :=
  @GoLean.GoCore.Machine.stmtOpOut

-- 33. `Machine.lean:4114` — the step's own output agrees with the init-refusal reading
example : ∀ {v : GoValue} {op : StmtOp} {nt : Nat} {done : List GoValue} {env : LocalEnv}
    {k : Cont},
    (printOut? (.retV v (.stmtOpK op nt done [] env k))).toList
      = stmtOpOut op (v :: done).reverse :=
  @GoLean.GoCore.Machine.printOut?_toList

-- 34. `MultiSound.lean:1710` — RE-PIN 2 (packet B, label-reshape audit F1): `ps₁` are the
-- arrival plan's picks, `ch₁` its residual, no select interception — the pool projection: a goroutine step's event label IS
-- `stepFn`'s (trace and output verbatim; the pool's arrival picks, then the step's)
example : ∀ {ctx : ProgramCtx} {s : Store} {threads : Array Thread} {i : Nat} {ch : Choices}
    {ts' : Array Thread} {s' : Store} {ch' : Choices} {ev : StepEvent},
    stepThread ctx s threads i ch = .ok (ts', s', ch', ev) → ev.action = .privateStep →
      ev.who = i ∧ ∃ c ch₁ ps₁ c' l, threads[i]? = some (.running c none) ∧
        arrivalPlan ctx s threads i c ch = .ok (none, ch₁, ps₁) ∧ selectApplyPlan c = none ∧
        stepFn ctx s c ch₁ = .ok (c', s', ch', l) ∧
        ev.label = ⟨l.trace, ps₁ ++ l.picks, l.out⟩ :=
  @GoLean.GoCore.Machine.stepThread_privateStep_label

/-! ## Re-pin 2 additions — packet B, the execution bridges (rows 35–64)

[AGENT packet B worker] 2026-09-28. Rows 35–57: every `<name>_stmt` of `ExecutionStatement.lean`
discharged as `theorem <name>` in `Prefix.lean`, its statement WRITTEN OUT (packet B audit F1,
[AGENT] coordinator disposition: an edit to a `_stmt` body changes a line here, so this file's
diff stays the interface diff). Rows 58–64: the supporting facts the bridges rest on, types written out. -/

-- 35. `Prefix.lean:70` — `prefix_refl_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (s : Store) (c : Config) (ch : Choices), Prefix ctx 0 s c ch [] s c ch :=
  @GoLean.GoCore.ExecutionStatement.prefix_refl

-- 36. `Prefix.lean:72` — `prefix_comp_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (n m : Nat) (s s₁ sf : Store) (c c₁ cf : Config)
    (ch ch₁ chf : Choices) (ls ls' : List StepLabel),
    Prefix ctx n s c ch ls s₁ c₁ ch₁ → Prefix ctx m s₁ c₁ ch₁ ls' sf cf chf →
    Prefix ctx (n + m) s c ch (ls ++ ls') sf cf chf :=
  @GoLean.GoCore.ExecutionStatement.prefix_comp

-- 37. `Prefix.lean:80` — `prefix_split_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (n m : Nat) (s sf : Store) (c cf : Config) (ch chf : Choices)
    (ls : List StepLabel),
    Prefix ctx (n + m) s c ch ls sf cf chf →
    ∃ (ls₁ ls₂ : List StepLabel) (s₁ : Store) (c₁ : Config) (ch₁ : Choices),
      ls = ls₁ ++ ls₂ ∧ Prefix ctx n s c ch ls₁ s₁ c₁ ch₁ ∧ Prefix ctx m s₁ c₁ ch₁ ls₂ sf cf chf :=
  @GoLean.GoCore.ExecutionStatement.prefix_split

-- 38. `Prefix.lean:100` — `prefix_erase_steps_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (n : Nat) (s sf : Store) (c cf : Config) (ch chf : Choices)
    (ls : List StepLabel),
    Prefix ctx n s c ch ls sf cf chf → Steps ctx c s cf sf :=
  @GoLean.GoCore.ExecutionStatement.prefix_erase_steps

-- 39. `Prefix.lean:94` — `prefix_erase_trace_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (n : Nat) (s sf : Store) (c cf : Config) (ch chf : Choices)
    (ls : List StepLabel),
    Prefix ctx n s c ch ls sf cf chf → Trace ctx n s c ch sf cf chf :=
  @GoLean.GoCore.ExecutionStatement.prefix_erase_trace

-- 40. `Prefix.lean:113` — `prefix_iter_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (n : Nat) (s sf : Store) (c cf : Config) (ch chf : Choices),
    stepFnIter ctx n s c ch = .ok (cf, sf, chf) ↔ ∃ ls, Prefix ctx n s c ch ls sf cf chf :=
  @GoLean.GoCore.ExecutionStatement.prefix_iter

-- 41. `Prefix.lean:385` — `finish_abort_step_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (s : Store) (c : Config) (ch : Choices) (t : String),
    (∃ (rec : List PickRecord) (ch'' : Choices), Finish ctx s c ch rec (.aborted t s ch'') 1) ↔
      stepFn ctx s c ch = .error (.terminal (.panic t)) :=
  @GoLean.GoCore.ExecutionStatement.finish_abort_step

-- 42. `Prefix.lean:165` — `finish_refused_step_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (s : Store) (c : Config) (ch : Choices) (first : PanicEntry)
    (rest : List PanicEntry) (r : Refusal),
    c.abort? = some (first, rest) →
    ((∃ (rec : List PickRecord) (ch'' : Choices), Finish ctx s c ch rec (.refused r s ch'') 1) ↔
      stepFn ctx s c ch = .error (.refusal r)) :=
  @GoLean.GoCore.ExecutionStatement.finish_refused_step

-- 43. `Prefix.lean:250` — `finish_replay_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (s : Store) (c : Config) (ch ch₂ : Choices) (first : PanicEntry)
    (rest : List PanicEntry) (rec : List PickRecord),
    c.abort? = some (first, rest) →
    (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch₂).2.2 = rec →
    (∀ (t : String) (ch'' : Choices), Finish ctx s c ch rec (.aborted t s ch'') 1 →
      Finish ctx s c ch₂ rec
        (.aborted t s (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch₂).2.1)
        1) ∧
    (∀ (r : Refusal) (ch'' : Choices), Finish ctx s c ch rec (.refused r s ch'') 1 →
      Finish ctx s c ch₂ rec
        (.refused r s (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch₂).2.1)
        1) :=
  @GoLean.GoCore.ExecutionStatement.finish_replay

-- 44. `Prefix.lean:445` — `run_ok_iff_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s sf : Store) (c : Config) (ch chf : Choices),
    execStmtLoop ctx fuel s c ch = .ok (sf, chf) ↔
      ∃ n, n ≤ fuel ∧ ∃ ls, Prefix ctx n s c ch ls sf (.next .stop) chf :=
  @GoLean.GoCore.ExecutionStatement.run_ok_iff

-- 45. `Prefix.lean:454` — `run_panic_iff_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices) (t : String),
    execStmtLoop ctx fuel s c ch = .error (.terminal (.panic t)) ↔
      ∃ (n : Nat) (ls : List StepLabel) (sf : Store) (cf : Config) (chf ch'' : Choices)
        (rec : List PickRecord),
        n + 1 ≤ fuel ∧ Prefix ctx n s c ch ls sf cf chf ∧
          Finish ctx sf cf chf rec (.aborted t sf ch'') 1 :=
  @GoLean.GoCore.ExecutionStatement.run_panic_iff

-- 46. `Prefix.lean:478` — `run_deadlock_iff_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices),
    execStmtLoop ctx fuel s c ch = .error (.terminal .deadlock) ↔
      ∃ n, n ≤ fuel ∧ ∃ (ls : List StepLabel) (sf : Store) (cf : Config) (chf : Choices),
        Prefix ctx n s c ch ls sf cf chf ∧ Finish ctx sf cf chf [] (.deadlock sf chf) 0 :=
  @GoLean.GoCore.ExecutionStatement.run_deadlock_iff

-- 47. `Prefix.lean:492` — `run_fuelOut_iff_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices),
    execStmtLoop ctx fuel s c ch = .error .fuelOut ↔
      ∃ (ls : List StepLabel) (sf : Store) (cf : Config) (chf : Choices),
        Prefix ctx fuel s c ch ls sf cf chf ∧ ¬ ZeroCost cf :=
  @GoLean.GoCore.ExecutionStatement.run_fuelOut_iff

-- 48. `Prefix.lean:309` — `replay_coverage_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (s s' : Store) (c c' : Config) (ch ch' : Choices) (l : StepLabel),
    stepFn ctx s c ch = .ok (c', s', ch', l) →
    ∀ ch₂ ch₂', replays l.picks ch₂ ch₂' → stepFn ctx s c ch₂ = .ok (c', s', ch₂', l) :=
  @GoLean.GoCore.ExecutionStatement.replay_coverage

-- 49. `Prefix.lean:587` — `silent_projection_stmt`, written out
example :
  ∀ (ls₁ ls₂ : List StepLabel),
    StepLabel.fold (ls₁ ++ ⟨[], [], []⟩ :: ls₂) = StepLabel.fold (ls₁ ++ ls₂) :=
  @GoLean.GoCore.ExecutionStatement.silent_projection

-- 50. `Prefix.lean:589` — `single_embedding_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (fuel : Nat) (σ : Store) (c : Config) (ch : Choices) (rs : RaceState)
    (r : Except Stop (Store × Choices)),
    execStmtLoop ctx fuel σ c ch = r → transferable r →
    execProgLoop ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch = r :=
  @GoLean.GoCore.ExecutionStatement.single_embedding

-- 51. `Prefix.lean:592` — `program_bridge_stmt`, written out
example :
  ∀ (fuel : Nat) (p : Program) (name : String) (args : Array GoValue) (ch : Choices)
    (pctx : ProgramCtx) (c₀ : Config) (s₀ : Store) (locs : List Loc) (ch₁ : Choices),
    runProgramSetupM fuel p name args ch = .ok (pctx, c₀, s₀, locs, ch₁) →
    runProgramPoolOutM fuel p name args ch =
      (match execProgLoopOut pctx fuel ⟨#[Thread.running c₀ none], s₀, 0⟩ {} ch₁
          GoString.empty with
        | (out, .error e) => .error (e, out)
        | (out, .ok (sf, _)) =>
            match loadMany pctx sf locs with
            | .ok vs => .ok { values := vs.toArray, output := out }
            | .error e => .error (e, out)) :=
  @GoLean.GoCore.ExecutionStatement.program_bridge

-- 52. `Prefix.lean:534` — `classification_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices),
    ClassOk ctx fuel s c ch ∨ ClassTerminal ctx fuel s c ch ∨ ClassFuelOut ctx fuel s c ch ∨
      ClassRefusal ctx fuel s c ch :=
  @GoLean.GoCore.ExecutionStatement.classification

-- 53. `Prefix.lean:544` — `classification_wf_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices),
    StateWf ctx s → NoRefusal ctx s c →
      ClassOk ctx fuel s c ch ∨ ClassTerminal ctx fuel s c ch ∨ ClassFuelOut ctx fuel s c ch :=
  @GoLean.GoCore.ExecutionStatement.classification_wf

-- 54. `Prefix.lean:280` — `boundary_abort_one_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (s : Store) (c : Config) (ch : Choices) (first : PanicEntry)
    (rest : List PanicEntry) (t : String),
    c.abort? = some (first, rest) →
    abortMsg ctx first rest
      (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1 = .ok t →
    execStmtLoop ctx 1 s c ch = .error (.terminal (.panic t)) :=
  @GoLean.GoCore.ExecutionStatement.boundary_abort_one

-- 55. `Prefix.lean:287` — `boundary_blocked_zero_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (s : Store) (c : Config) (ch : Choices),
    Blocked c → execStmtLoop ctx 0 s c ch = .error (.terminal .deadlock) :=
  @GoLean.GoCore.ExecutionStatement.boundary_blocked_zero

-- 56. `Prefix.lean:290` — `boundary_refused_one_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (s : Store) (c : Config) (ch : Choices) (first : PanicEntry)
    (rest : List PanicEntry) (r : Refusal),
    c.abort? = some (first, rest) →
    abortMsg ctx first rest
      (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1
        = .error (.refusal r) →
    execStmtLoop ctx 1 s c ch = .error (.refusal r) :=
  @GoLean.GoCore.ExecutionStatement.boundary_refused_one

-- 57. `Prefix.lean:297` — `boundary_refused_zero_stmt`, written out
example :
  ∀ (ctx : ProgramCtx) (s : Store) (c : Config) (ch : Choices) (first : PanicEntry)
    (rest : List PanicEntry) (r : Refusal),
    c.abort? = some (first, rest) →
    abortMsg ctx first rest
      (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1
        = .error (.refusal r) →
    execStmtLoop ctx 0 s c ch = .error .fuelOut :=
  @GoLean.GoCore.ExecutionStatement.boundary_refused_zero

-- 58. `Prefix.lean:373` — NO STRAY PANIC (audit F1, machine-checked)
example : ∀ {ctx : ProgramCtx} {s : Store} {c : Config} {ch : Choices} {t : String},
    c.abort? = none → stepFn ctx s c ch ≠ .error (.terminal (.panic t)) :=
  @GoLean.GoCore.ExecutionStatement.stepFn_no_stray_panic

-- 59. `StepErrors.lean` — what `stepFn` raises away from the abort and the blocked forms
example : ∀ {ctx : ProgramCtx} {σ : Store} {c : Config} {ch : Choices},
    c.abort? = none → c.blockedB = false → ErrP Stop.Strict (stepFn ctx σ c ch) :=
  @GoLean.GoCore.Machine.stepFn_strict

-- 60. `PrefixFacts.lean` — no record without a consultation
example : ∀ {ctx : ProgramCtx} {σ : Store} {c : Config} {ch₀ : Choices},
    seqConsumption ctx σ c = none →
      OkP (fun r : Config × Store × Choices × StepLabel => r.2.2.2.picks = [])
        (stepFn ctx σ c ch₀) :=
  @GoLean.GoCore.Machine.stepFn_picks_none

-- 61. `PrefixFacts.lean` — the record IS the consultation's
example : ∀ {ctx : ProgramCtx} {σ : Store} {c : Config} {ch₀ : Choices} {site : ChoiceSite}
    {b : Nat}, seqConsumption ctx σ c = some (site, b) →
      OkP (fun r : Config × Store × Choices × StepLabel =>
          r.2.2.2.picks = PickRecord.ofPick site b (Choices.consumeAt site b ch₀).1)
        (stepFn ctx σ c ch₀) :=
  @GoLean.GoCore.Machine.stepFn_picks_some

-- 62. `MachineSound.lean` — the consumption theorem's `some` half WITHOUT `appendTargetLocal` (RE-TARGETED at
-- RE-PIN 10, packet D: the PrefixFacts copy folded back; the statement is unchanged)
example : ∀ {ctx : ProgramCtx} {σ : Store} {c : Config} {ch₀ : Choices} {c' : Config} {σ' : Store}
    {ch₀' : Choices} {site : ChoiceSite} {b : Nat} {tr : StepLabel},
    seqConsumption ctx σ c = some (site, b) →
    stepFn ctx σ c ch₀ = .ok (c', σ', ch₀', tr) →
    ch₀' = (Choices.consumeAt site b ch₀).2 ∧ ∀ ch : Choices,
      (Choices.consumeAt site b ch).1 = (Choices.consumeAt site b ch₀).1 →
      stepFn ctx σ c ch = .ok (c', σ', (Choices.consumeAt site b ch).2, tr) :=
  @GoLean.GoCore.Machine.stepFn_consumption_some

-- 63. `Prefix.lean:398` — every loop error, located on the fixed tape's prefix
example : ∀ {ctx : ProgramCtx} {fuel : Nat} {s : Store} {c : Config} {ch : Choices} {e : Stop},
    execStmtLoop ctx fuel s c ch = .error e →
    ∃ n ls sf cf chf, GoLean.GoCore.ExecutionStatement.Prefix ctx n s c ch ls sf cf chf ∧ n ≤ fuel ∧
      ((GoLean.GoCore.ExecutionStatement.Blocked cf ∧ e = .terminal .deadlock) ∨
       (n = fuel ∧ ¬ GoLean.GoCore.ExecutionStatement.ZeroCost cf ∧ e = .fuelOut) ∨
       (n + 1 ≤ fuel ∧ ¬ GoLean.GoCore.ExecutionStatement.ZeroCost cf ∧
          stepFn ctx sf cf chf = .error e)) :=
  @GoLean.GoCore.ExecutionStatement.execStmtLoop_error

-- 64. `Prefix.lean:578` — the domain premise's one-step preservation
example : ∀ {ctx : ProgramCtx} {s s' : Store} {c c' : Config} {ch₀ ch₀' : Choices} {l : StepLabel},
    GoLean.GoCore.ExecutionStatement.NoRefusal ctx s c → stepFn ctx s c ch₀ = .ok (c', s', ch₀', l) →
      GoLean.GoCore.ExecutionStatement.NoRefusal ctx s' c' :=
  @GoLean.GoCore.ExecutionStatement.noRefusal_step

-- 65. `Machine.lean` — the frame a CALL position pushes names the resolved callee (RE-PIN 3;
-- [USER] 2026-09-28 «Agree on (1)», relayed)
example : ∀ {plans : List (TargetShape × List Expr)} {env : LocalEnv} {k : Cont}
    {func : Func} {frameEnv : LocalEnv} {resultLocs : List Loc},
    Entry.callConfig plans env k (.run func frameEnv resultLocs)
      = .exec func.body frameEnv (.frame plans env resultLocs [] k func.id) :=
  @GoLean.GoCore.Machine.Entry.callConfig_run

-- 66. `Machine.lean` — a frame exit reads «`fid` returned `vs`» (RE-PIN 3)
example : ∀ {ctx : ProgramCtx} {sh : TargetShape} {e : Expr} {ops : List Expr}
    {rest : List (TargetShape × List Expr)} {tenv : LocalEnv} {results : List Loc} {k : Cont}
    {fid : FuncId} {s : Store} {vs : List GoValue} {tr : AccessTrace},
    loadResults ctx s results = .ok (vs, tr) →
    Step ctx (.next (.frame ((sh, e :: ops) :: rest) tenv results [] k fid)) s
        (.evalE e tenv (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k)) s ⟨tr, [], []⟩
      ∧ Step ctx (.signal .ret (.frame ((sh, e :: ops) :: rest) tenv results [] k fid)) s
        (.evalE e tenv (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k)) s ⟨tr, [], []⟩ :=
  @GoLean.GoCore.Machine.frame_exit_returns

-- 67. `Machine.lean` — the direct path is the function-call rule (RE-PIN 3; design §3
-- `enterFrame_declared`, charter row 3: the logic team's `MaybeUpdate` pilot uses ordinary call rules)
example : ∀ {ctx : ProgramCtx} {s : Store} {fid : FuncId} {argVals : List GoValue} {func : Func},
    findFunctionIn? ctx.functions fid = some func →
    (∀ m, methodInfoByFuncId? ctx func.id = some m → methodRecvInterfaceName? m = none) →
    func.args.size = argVals.length →
    enterFrame ctx s fid argVals = (do
      let (argsEnv, s₁) ← bindParams ctx [] s func.args.toList argVals
      let (frameEnv, s₂) ← allocDecls ctx argsEnv s₁ func.results.toList
      let resultLocs ← pinResultLocs frameEnv func.results.toList
      return (.run func frameEnv resultLocs, s₂, [])) :=
  @GoLean.GoCore.Machine.enterFrame_declared

-- 68. `Syntax.lean` — narrowing `findFunctionIn?`'s domain leaves a found function unchanged
-- (RE-PIN 4; the logic team's request 5, 2026-09-28, relayed: the bridge from the pin's table —
-- declared functions + synthesized wrappers — to the post-P table, declared functions only)
example : ∀ {funcs : Array Func} {id : FuncId} {f : Func} {p : Func → Bool},
    findFunctionIn? funcs id = some f → p f = true →
    findFunctionIn? (funcs.filter p) id = some f :=
  @GoLean.GoCore.findFunctionIn?_filter

-- 69. `Syntax.lean` — the `none` direction (RE-PIN 4)
example : ∀ {funcs : Array Func} {id : FuncId} {p : Func → Bool},
    findFunctionIn? funcs id = none → findFunctionIn? (funcs.filter p) id = none :=
  @GoLean.GoCore.findFunctionIn?_filter_none

-- 70. `Ops.lean` — a declaration lookup answers a declared method of exactly the dynamic type
-- (RE-PIN 4; design §3 `methodDecl?`)
example : ∀ {ctx : ProgramCtx} {dynTy : Ty} {member : Declaration.MemberId} {info : MethodInfo},
    methodDecl? ctx dynTy member = some info →
    (info.id == member) = true ∧ (methodRecvDynamicTy? info == some dynTy) = true ∧
      info ∈ ctx.methods :=
  @GoLean.GoCore.methodDecl?_some

-- 71. `Ops.lean` — a record lookup answers the carrier's own record (RE-PIN 4; design §3 `promotion?`)
example : ∀ {ctx : ProgramCtx} {carrier : TypeId} {member : Declaration.MemberId} {p : Promotion},
    promotion? ctx carrier member = some p →
    p.type = carrier ∧ (p.member == member) = true ∧ p ∈ ctx.promotions :=
  @GoLean.GoCore.promotion?_some

-- 72. `Ops.lean` — a declared method resolves directly: empty path, `asIs`, its own target
-- (RE-PIN 4; design §3 `resolveMethod?_declared`)
example : ∀ {ctx : ProgramCtx} {dynTy : Ty} {member : Declaration.MemberId} {info : MethodInfo},
    methodDecl? ctx dynTy member = some info →
    resolveMethod? ctx dynTy member =
      some { path := #[], adjust := .asIs, target := .method info.funcId } :=
  @GoLean.GoCore.resolveMethod?_declared

-- 73. `Ops.lean` — the `*T ⊇ T` arm: empty path, `deref` (RE-PIN 4; design §3 `resolveMethod?_ptrDeclared`)
example : ∀ {ctx : ProgramCtx} {elem : Ty} {member : Declaration.MemberId} {info : MethodInfo},
    methodDecl? ctx (.pointer elem) member = none →
    (∀ t, elem ≠ .pointer t) → (∀ i, elem ≠ .interface i) →
    methodDecl? ctx elem member = some info →
    resolveMethod? ctx (.pointer elem) member =
      some { path := #[], adjust := .deref, target := .method info.funcId } :=
  @GoLean.GoCore.resolveMethod?_ptrDeclared

-- 74. `Ops.lean` — a promoted entry resolves to its record, value box (RE-PIN 4; design §3
-- `resolveMethod?_promoted`)
example : ∀ {ctx : ProgramCtx} {idx : TypeIdx} {member : Declaration.MemberId} {carrier : TypeId}
    {p : Promotion},
    methodDecl? ctx (.defined idx) member = none →
    ctx.types.nameOf? idx = some carrier →
    promotion? ctx carrier member = some p →
    p.inPtrSetOnly = false →
    resolveMethod? ctx (.defined idx) member = some (.ofPromotion p) :=
  @GoLean.GoCore.resolveMethod?_promoted

-- 75. `Ops.lean` — a promoted entry resolves to its record, pointer box (RE-PIN 4)
example : ∀ {ctx : ProgramCtx} {idx : TypeIdx} {member : Declaration.MemberId} {carrier : TypeId}
    {p : Promotion},
    methodDecl? ctx (.pointer (.defined idx)) member = none →
    methodDecl? ctx (.defined idx) member = none →
    ctx.types.nameOf? idx = some carrier →
    promotion? ctx carrier member = some p →
    resolveMethod? ctx (.pointer (.defined idx)) member = some (.ofPromotion p) :=
  @GoLean.GoCore.resolveMethod?_promotedPtr

-- 76. `Ops.lean` — the direct path is the identity (RE-PIN 4; design §3 `receiverAt_nil_path`)
example : ∀ {ctx : ProgramCtx} (state : Store) (root : GoValue),
    receiverAt ctx state root #[] .asIs = .ok (root, []) :=
  @GoLean.GoCore.receiverAt_nil_path

-- 77. `Ops.lean` — the direct path is the single deref: the `*T ⊇ T` arm's one read (RE-PIN 4)
example : ∀ {ctx : ProgramCtx} (state : Store) (l : Loc),
    receiverAt ctx state (.addr l) #[] .deref = Mem.load ctx state l :=
  @GoLean.GoCore.receiverAt_nil_path_deref

-- 78. `Ops.lean` — the `*T ⊇ T` arm on a nil box: the nil-dereference panic (RE-PIN 4; BUG-087 member 0)
example : ∀ {ctx : ProgramCtx} (state : Store),
    receiverAt ctx state .nil #[] .deref = .error (.panic nilDerefPanicText) :=
  @GoLean.GoCore.receiverAt_nil_path_deref_nil

-- 79. `Ops.lean` — projection through nil panics (RE-PIN 4; design §3 `receiverAt_nil_panic`, S4)
example : ∀ {ctx : ProgramCtx} (state : Store) {path : Array PromotionHop} {h : PromotionHop}
    {hs : List PromotionHop},
    path.toList = h :: hs → ∀ (adjust : PromotionAdjust),
    receiverAt ctx state .nil path adjust = .error (.panic nilDerefPanicText) :=
  @GoLean.GoCore.receiverAt_nil_panic

-- 80. `Ops.lean` — one hop through a value field: the receiver read out of the field's cell
-- (RE-PIN 4; design §3 `receiverAt_field`, S8)
example : ∀ {ctx : ProgramCtx} (state : Store) {l : Loc} {h : PromotionHop},
    h.ptr = false →
    receiverAt ctx state (.addr l) #[h] .asIs = Mem.load ctx state (Loc.field l h.owner h.field) :=
  @GoLean.GoCore.receiverAt_field

-- 81. `Ops.lean` — one hop from a struct value in hand: a projection, no read (RE-PIN 4)
example : ∀ {ctx : ProgramCtx} (state : Store) {tid : TypeId} {fields : Array (String × GoValue)}
    {h : PromotionHop} {v : GoValue},
    structFieldValue ctx (.struct tid fields) h.owner h.field = .ok v →
    receiverAt ctx state (.struct tid fields) #[h] .asIs = .ok (v, []) :=
  @GoLean.GoCore.receiverAt_field_proj

-- 82. `Ops.lean` — one value hop to a pointer receiver: the field's address, no read (RE-PIN 4)
example : ∀ {ctx : ProgramCtx} (state : Store) {l : Loc} {h : PromotionHop},
    h.ptr = false →
    receiverAt ctx state (.addr l) #[h] .addr = .ok (.addr (Loc.field l h.owner h.field), []) :=
  @GoLean.GoCore.receiverAt_field_addr

-- 83. `Ops.lean` — one hop through an embedded pointer: the pointer field read (RE-PIN 4; design §3
-- `receiverAt_ptr`, S8)
example : ∀ {ctx : ProgramCtx} (state : Store) {l : Loc} {h : PromotionHop},
    h.ptr = true → ∀ {pv : GoValue} {tr : AccessTrace},
    Mem.load ctx state (Loc.field l h.owner h.field) = .ok (pv, tr) →
    receiverAt ctx state (.addr l) #[h] .asIs = .ok (pv, tr) :=
  @GoLean.GoCore.receiverAt_ptr

-- 84. `Ops.lean` — an embedded-pointer hop to a value receiver: the pointer field, then the pointee
-- (RE-PIN 4; decision 6 — THE documented access-trace change)
example : ∀ {ctx : ProgramCtx} (state : Store) {l l' : Loc} {h : PromotionHop},
    h.ptr = true → ∀ {tr : AccessTrace},
    Mem.load ctx state (Loc.field l h.owner h.field) = .ok (.addr l', tr) →
    ∀ {v : GoValue} {tr' : AccessTrace}, Mem.load ctx state l' = .ok (v, tr') →
    receiverAt ctx state (.addr l) #[h] .deref = .ok (v, tr ++ tr') :=
  @GoLean.GoCore.receiverAt_ptr_deref

-- 85. `Ops.lean` — a final pointer receiver through a nil embedded `*E` receives nil (RE-PIN 4; S4)
example : ∀ {ctx : ProgramCtx} (state : Store) {l : Loc} {h : PromotionHop},
    h.ptr = true → ∀ {tr : AccessTrace},
    Mem.load ctx state (Loc.field l h.owner h.field) = .ok (.nil, tr) →
    receiverAt ctx state (.addr l) #[h] .asIs = .ok (.nil, tr) :=
  @GoLean.GoCore.receiverAt_ptr_nil

-- 86. `Ops.lean` — a value receiver copied out of a nil embedded `*E` panics (RE-PIN 4; S4)
example : ∀ {ctx : ProgramCtx} (state : Store) {l : Loc} {h : PromotionHop},
    h.ptr = true → ∀ {tr : AccessTrace},
    Mem.load ctx state (Loc.field l h.owner h.field) = .ok (.nil, tr) →
    receiverAt ctx state (.addr l) #[h] .deref = .error (.panic nilDerefPanicText) :=
  @GoLean.GoCore.receiverAt_ptr_nil_deref

-- 87. `Machine.lean` — the recover rule: the deferred frame directly on the marker (RE-PIN 4;
-- design §3 `recoverResult_eq`, decision 7)
example : ∀ {t : List (TargetShape × List Expr)} {te : LocalEnv} {r : List Loc}
    {ds : List (GoValue × List GoValue)} {chain : List PanicEntry} {k : Cont} {f : FuncId},
    recoverResult (.frame t te r ds (.panicResumeK chain k) f) =
      match markNewestRecovered chain with
      | some (v, chain') => (v, .frame t te r ds (.panicResumeK chain' k) f)
      | none => (.nil, .frame t te r ds (.panicResumeK chain k) f) :=
  @GoLean.GoCore.Machine.recoverResult_eq

-- 88. `Machine.lean` — `recover` at a call frame: `recoverAtDeferred` on its tail decides (RE-PIN 4)
example : ∀ {t : List (TargetShape × List Expr)} {te : LocalEnv} {r : List Loc}
    {ds : List (GoValue × List GoValue)} {k' : Cont} {f : FuncId},
    recoverResult (.frame t te r ds k' f) =
      match recoverAtDeferred k' with
      | some (v, k'') => (v, .frame t te r ds k'' f)
      | none => (.nil, .frame t te r ds k' f) :=
  @GoLean.GoCore.Machine.recoverResult_frame

-- 89. `Machine.lean` — `recover` through glue: the tail's answer under the rebuilt glue (RE-PIN 4)
example : ∀ {k k' : Cont}, k.isGlue = true → k.tail = some k' →
    recoverResult k = ((recoverResult k').1, k.withTail (recoverResult k').2) :=
  @GoLean.GoCore.Machine.recoverResult_glue

-- 90. `Machine.lean` — the continuation IS a list of frames (RE-PIN 5; G-C3 decision 1: this and
-- nothing more — no `Config` reshape, no context-fill law)
example : Cont = List Frame := rfl

-- 91. `Machine.lean` — the one walk at a frame: descend (the tail's answer, the frame consed back)
-- or act (RE-PIN 5; D6)
example : ∀ {β : Type} {descend : Cont → Bool} {act : Cont → Option (β × Cont)} (f : Frame) (k : Cont),
    Cont.rebuild descend act (f :: k) =
      if descend (f :: k) = true then
        (Cont.rebuild descend act k).map fun (b, k'') => (b, f :: k'')
      else act (f :: k) :=
  @GoLean.GoCore.Machine.Cont.rebuild_cons

-- 92. `Machine.lean` — the one walk at the empty continuation acts (RE-PIN 5)
example : ∀ {β : Type} {descend : Cont → Bool} {act : Cont → Option (β × Cont)},
    Cont.rebuild descend act [] = act [] :=
  @GoLean.GoCore.Machine.Cont.rebuild_nil

-- 93. `Machine.lean` — `pushDefer` maps at the first call frame under a statement-glue prefix
-- (RE-PIN 5; D6 `pushDefer_eq`)
example : ∀ (d : GoValue × List GoValue) (pre : List Frame) (t : List (TargetShape × List Expr))
    (te : LocalEnv) (r : List Loc) (ds : List (GoValue × List GoValue)) (f : FuncId) (k : Cont),
    (∀ g ∈ pre, g.class = .stmtGlue) →
    pushDefer d (pre ++ Frame.frame t te r ds f :: k) = some (pre ++ Frame.frame t te r (d :: ds) f :: k) :=
  @GoLean.GoCore.Machine.pushDefer_eq

-- 94. `Machine.lean` — every successful `pushDefer` has that shape (RE-PIN 5)
example : ∀ {d : GoValue × List GoValue} {k k' : Cont}, pushDefer d k = some k' →
    ∃ pre t te r ds f rest, (∀ g ∈ pre, g.class = .stmtGlue)
      ∧ k = pre ++ Frame.frame t te r ds f :: rest
      ∧ k' = pre ++ Frame.frame t te r (d :: ds) f :: rest :=
  @GoLean.GoCore.Machine.pushDefer_some

-- 95. `Machine.lean` — `pushDefer` at a call frame (RE-PIN 5)
example : ∀ (d : GoValue × List GoValue) (t : List (TargetShape × List Expr)) (te : LocalEnv)
    (r : List Loc) (ds : List (GoValue × List GoValue)) (f : FuncId) (k : Cont),
    pushDefer d (Frame.frame t te r ds f :: k) = some (Frame.frame t te r (d :: ds) f :: k) :=
  @GoLean.GoCore.Machine.pushDefer_frame

-- 96. `Machine.lean` — `pushDefer` through statement glue (RE-PIN 5)
example : ∀ (d : GoValue × List GoValue) {g : Frame} (k : Cont), g.class = .stmtGlue →
    pushDefer d (g :: k) = (pushDefer d k).map (g :: ·) :=
  @GoLean.GoCore.Machine.pushDefer_glue

-- 97. `Machine.lean` — `pushDefer` at any other head fails closed (RE-PIN 5)
example : ∀ (d : GoValue × List GoValue) {g : Frame} (k : Cont), g.class ≠ .stmtGlue →
    g.class ≠ .callFrame → pushDefer d (g :: k) = none :=
  @GoLean.GoCore.Machine.pushDefer_other

-- 98. `Machine.lean` — `seqCont` splices into a same-environment sequence (RE-PIN 5; D6)
example : ∀ (ss rest : List Stmt) (env : LocalEnv) (k : Cont),
    seqCont ss env (Frame.seq rest env :: k) = Frame.seq (ss ++ rest) env :: k :=
  @GoLean.GoCore.Machine.seqCont_seq

-- 99. `Machine.lean` — `seqCont` over a foreign-environment sequence (RE-PIN 5)
example : ∀ (ss rest : List Stmt) {env env' : LocalEnv} (k : Cont), env' ≠ env →
    seqCont ss env (Frame.seq rest env' :: k) = Frame.seq ss env :: Frame.seq rest env' :: k :=
  @GoLean.GoCore.Machine.seqCont_seq_ne

-- 100. `Machine.lean` — `seqCont` at any other head (RE-PIN 5; D6 `seqCont_eq`)
example : ∀ (ss : List Stmt) (env : LocalEnv) (k : Cont),
    (∀ rest env' k', k ≠ Frame.seq rest env' :: k') → seqCont ss env k = Frame.seq ss env :: k :=
  @GoLean.GoCore.Machine.seqCont_eq

-- 101. `Machine.lean` — one unwinding step strips a glue head, of either kind (RE-PIN 5; D6
-- `panicPassthrough_eq`)
example : ∀ (g : Frame) (k : Cont),
    panicPassthrough (g :: k) = if g.class = .stmtGlue ∨ g.class = .exprGlue then some k else none :=
  @GoLean.GoCore.Machine.panicPassthrough_eq

-- 102. `Machine.lean` — no unwinding step at the empty continuation (RE-PIN 5)
example : panicPassthrough [] = none := @GoLean.GoCore.Machine.panicPassthrough_nil

-- 103. `Machine.lean` — `recover` through a glue head, as a list law (RE-PIN 5)
example : ∀ {g : Frame} (k : Cont), g.class = .stmtGlue ∨ g.class = .exprGlue →
    recoverResult (g :: k) = ((recoverResult k).1, g :: (recoverResult k).2) :=
  @GoLean.GoCore.Machine.recoverResult_cons_glue

-- 104. `Machine.lean` — `recover` at the empty continuation is the no-op `.nil` (RE-PIN 5)
example : recoverResult [] = (.nil, []) := @GoLean.GoCore.Machine.recoverResult_nil

-- 105. `StepFn.lean` — a body that falls off its end at a call frame takes frame exit over the
-- list's rest (RE-PIN 5; D6 frame exit)
example : ∀ {ctx : ProgramCtx} (s : Store) (targets : List (TargetShape × List Expr)) (tenv : LocalEnv)
    (results : List Loc) (ds : List (GoValue × List GoValue)) (fr : FuncId) (k' : Cont) (choices : Choices),
    stepFn ctx s (.next (Frame.frame targets tenv results ds fr :: k')) choices
      = stepFrameExit ctx s targets tenv results ds k' fr choices :=
  @GoLean.GoCore.Machine.stepFn_next_frame

-- 106. `StepFn.lean` — an empty frame (no targets, results or defers) pops itself (RE-PIN 5)
example : ∀ {ctx : ProgramCtx} (s : Store) (tenv : LocalEnv) (k' : Cont) (fr : FuncId) (choices : Choices),
    stepFrameExit ctx s [] tenv [] [] k' fr choices = .ok (.next k', s, choices, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Machine.stepFrameExit_nil

-- 107. `StateWf.lean` — the sup of a frame stack: the head's own payload joined with the tail's
-- (RE-PIN 5)
example : ∀ (f : Frame) (k : Cont), Cont.locSup (f :: k) = max (Cont.locSup [f]) (Cont.locSup k) :=
  @GoLean.GoCore.Machine.Cont.locSup_cons

-- ---- RE-PIN 6 (B6, numeric locals, 2026-09-30) ----

-- 108. `Syntax.lean` — a local's identity is a NUMBER: an index into its function's name table
example : VarId = Nat := rfl

-- 109. `Syntax.lean` — the binder positions are numeric: a parameter/result/declaration
example : ∀ (p : Param), p.id = p.id ∧ (Param.id : Param → VarId) = Param.id := fun _ => ⟨rfl, rfl⟩

-- 110. `Syntax.lean` — a variable read, its address, and an assignment target name a `VarId`
example : (Expr.var : VarId → Expr) = Expr.var ∧ (Expr.ref : VarId → Expr) = Expr.ref
    ∧ (Assignee.var : VarId → Assignee) = Assignee.var := ⟨rfl, rfl, rfl⟩

-- 111. `State.lean` — a scope binds ids to locations; the env is a stack of scopes (unchanged shape)
example : Scope = List (VarId × Loc) ∧ LocalEnv = List Scope := ⟨rfl, rfl⟩

-- 112. `Syntax.lean` — the name-table entry: Go's identifier, the kind, the declaring position, the
-- lowering's spelling where it differs
example : ∀ (e : LocalName), e = { name := e.name, kind := e.kind, pos := e.pos, wire := e.wire } :=
  fun _ => rfl

-- 113. `Syntax.lean` — the six kinds
example : ∀ (k : LocalKind), k = .recv ∨ k = .param ∨ k = .result ∨ k = .capture ∨ k = .local ∨ k = .temp := by
  intro k; cases k <;> simp

-- 114. `Syntax.lean` — a function carries its table; the lookup is the table's index
example : ∀ (f : Func) (id : VarId), f.localName? id = f.locals[id]? := fun _ _ => rfl

-- 115. `Locals.lean` — every id a function names: its signature's, its declarations', its mentions'
example : ∀ (f : Func), f.ids = (f.args ++ f.results).toList.map (·.id) ++ f.body.declIds ++ f.body.names :=
  fun _ => rfl

-- 116. `Locals.lean` — the decoder's final check (c5), in BOTH directions since the fix round
-- (2026-09-30, the audit's F1): tree ⊆ table, table ⊆ tree, the signature's ids pairwise distinct,
-- the kinds where the ids occur (RE-PIN 6 fix round: was the first and third conjunct only)
example : ∀ (f : Func), f.localsOk = (f.tableCovers && f.tableNamed && f.sigDistinct && f.argKinds
    && f.resultKinds && f.recvFirst && f.bodyKinds) := fun _ => rfl
example : ∀ (f : Func), f.tableCovers = f.ids.all (· < f.locals.size) := fun _ => rfl
example : ∀ (f : Func), f.tableNamed = (List.range f.locals.size).all (f.ids.contains ·) := fun _ => rfl
example : ∀ (f : Func), f.sigDistinct = namesDistinct ((f.args ++ f.results).toList.map (·.id)) := fun _ => rfl

-- 117. `Locals.lean` — «source spellings are retained»: under `localsOk`, every id the function
-- names has a table entry
example : ∀ {f : Func}, f.localsOk = true → ∀ {id : VarId}, id ∈ f.ids → (f.localName? id).isSome = true :=
  @GoLean.GoCore.Func.localsOk_covers

-- 118. `Locals.lean` — under `localsOk`, the signature's ids are pairwise distinct (the slot lemmas' premise)
example : ∀ {f : Func}, f.localsOk = true → namesDistinct ((f.args ++ f.results).toList.map (·.id)) = true :=
  @GoLean.GoCore.Func.localsOk_sigDistinct

-- 119. `State.lean` — `declare` then `lookup` of the same id: the new cell
example : ∀ (env : LocalEnv) (id : VarId) (loc : Loc), LocalEnv.lookup (env.declare id loc) id = some loc :=
  GoLean.GoCore.LocalEnv.lookup_declare_self

-- 120. `State.lean` — `declare` leaves every other id's binding alone
example : ∀ (env : LocalEnv) {id id' : VarId}, id' ≠ id → ∀ (loc : Loc),
    LocalEnv.lookup (env.declare id loc) id' = LocalEnv.lookup env id' :=
  @GoLean.GoCore.LocalEnv.lookup_declare_ne

-- 121. `State.lean` — a fresh scope changes no binding
example : ∀ (env : LocalEnv) (id : VarId), LocalEnv.lookup env.pushScope id = LocalEnv.lookup env id :=
  GoLean.GoCore.LocalEnv.lookup_pushScope

-- 122. `Machine.lean` — arguments bind in order: parameter `i` at the `i`-th cell allocated from `s`
example : ∀ (ctx : ProgramCtx) (env : LocalEnv) (s : Store) (ps : List Param) (vs : List GoValue)
    {env' : LocalEnv} {s' : Store}, bindParams ctx env s ps vs = .ok (env', s') →
    namesDistinct (ps.map (·.id)) = true →
    ∀ (i : Nat) (hi : i < ps.length), LocalEnv.lookup env' ps[i].id = some (.base ⟨s.heap.size + i⟩) :=
  @GoLean.GoCore.Machine.bindParams_lookup

-- 123. `Machine.lean` — declared locals allocate in order: declaration `j` at the `j`-th cell
example : ∀ (ctx : ProgramCtx) (env : LocalEnv) (s : Store) (ps : List Param)
    {env' : LocalEnv} {s' : Store}, allocDecls ctx env s ps = .ok (env', s') →
    namesDistinct (ps.map (·.id)) = true →
    ∀ (j : Nat) (hj : j < ps.length), LocalEnv.lookup env' ps[j].id = some (.base ⟨s.heap.size + j⟩) :=
  @GoLean.GoCore.Machine.allocDecls_lookup

-- 124. `Machine.lean` — «table lookup agrees with the activation's runtime slot», arguments: a declared
-- non-anchor function entered with `argVals` binds parameter `i` to `.base ⟨s.heap.size + i⟩`
example : ∀ {ctx : ProgramCtx} {s : Store} {fid : FuncId} {argVals : List GoValue} {func : Func},
    findFunctionIn? ctx.functions fid = some func →
    (∀ m, methodInfoByFuncId? ctx func.id = some m → methodRecvInterfaceName? m = none) →
    func.args.size = argVals.length →
    namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true →
    ∀ {frameEnv : LocalEnv} {resultLocs : List Loc} {s' : Store} {tr : AccessTrace},
    enterFrame ctx s fid argVals = .ok (.run func frameEnv resultLocs, s', tr) →
    ∀ (i : Nat) (hi : i < func.args.size),
      LocalEnv.lookup frameEnv func.args[i].id = some (.base ⟨s.heap.size + i⟩) :=
  @GoLean.GoCore.Machine.enterFrame_lookup_arg

-- 125. `Machine.lean` — the same, results: result `j` at the cell after all the parameters
example : ∀ {ctx : ProgramCtx} {s : Store} {fid : FuncId} {argVals : List GoValue} {func : Func},
    findFunctionIn? ctx.functions fid = some func →
    (∀ m, methodInfoByFuncId? ctx func.id = some m → methodRecvInterfaceName? m = none) →
    func.args.size = argVals.length →
    namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true →
    ∀ {frameEnv : LocalEnv} {resultLocs : List Loc} {s' : Store} {tr : AccessTrace},
    enterFrame ctx s fid argVals = .ok (.run func frameEnv resultLocs, s', tr) →
    ∀ (j : Nat) (hj : j < func.results.size),
      LocalEnv.lookup frameEnv func.results[j].id = some (.base ⟨s.heap.size + func.args.size + j⟩) :=
  @GoLean.GoCore.Machine.enterFrame_lookup_result

-- ---- RE-PIN 6, the fix round (B6 audit F1, 2026-09-30) ----

-- 126. `Locals.lean` — table ⊆ tree: under `localsOk`, every table entry is named by the function
example : ∀ {f : Func}, f.localsOk = true → ∀ {i : Nat}, i < f.locals.size → i ∈ f.ids :=
  @GoLean.GoCore.Func.localsOk_named

-- 127. `Locals.lean` — the kind the table records for an id
example : ∀ (f : Func) (id : VarId), f.kindOf? id = (f.locals[id]?).map (·.kind) := fun _ _ => rfl

-- 128. `Locals.lean` — a parameter's kind is receiver, parameter, capture or temporary
example : ∀ {f : Func}, f.localsOk = true → ∀ {p : Param}, p ∈ f.args.toList →
    f.kindOf? p.id = some .recv ∨ f.kindOf? p.id = some .param
      ∨ f.kindOf? p.id = some .capture ∨ f.kindOf? p.id = some .temp :=
  @GoLean.GoCore.Func.localsOk_argKind

-- 129. `Locals.lean` — a result's kind is result or temporary
example : ∀ {f : Func}, f.localsOk = true → ∀ {p : Param}, p ∈ f.results.toList →
    f.kindOf? p.id = some .result ∨ f.kindOf? p.id = some .temp :=
  @GoLean.GoCore.Func.localsOk_resultKind

-- 130. `Locals.lean` — only the first parameter may be the receiver
example : ∀ {f : Func}, f.localsOk = true → ∀ {p : Param}, p ∈ f.args.toList.drop 1 →
    f.kindOf? p.id ≠ some .recv :=
  @GoLean.GoCore.Func.localsOk_recvFirst

-- 131. `Locals.lean` — a body-declared local's kind is local or temporary (it cannot claim recv/param/
-- capture/result)
example : ∀ {f : Func}, f.localsOk = true → ∀ {id : VarId}, id ∈ f.body.declIds →
    f.kindOf? id = some .local ∨ f.kindOf? id = some .temp :=
  @GoLean.GoCore.Func.localsOk_bodyKind

-- 132. `Machine.lean` — the sweep's id-level entry check (fix round F3): the `unseqEnter` rule's
-- second premise — every binder fresh in the enclosing environment, every mentioned slot a cell
-- or a bound local. RE-PINNED at RE-PIN 8 (C4 D3 (b), 2026-10-01): the cells are allocated in a
-- sweep-PRIVATE scope (`env.pushScope`) and the continuation keeps the source environment
-- (`.seq rest env k`, was `.seq rest env' k`)
example : ∀ {ctx : ProgramCtx} {g : UnseqGraph} {thenB : Stmt} {rest : List Stmt} {env env' : LocalEnv}
    {k : Cont} {s s' : Store},
    g.wellFormed? = none → unseqEntryCheck? g env = none →
    allocDecls ctx env.pushScope s g.cells = .ok (env', s') →
    Step ctx (.exec (.unseq g thenB) env (.seq rest env k)) s
      (.next (.unseqK g thenB g.initStatus [] env' .pick (.seq rest env k))) s' ⟨[], [], []⟩ :=
  @GoLean.GoCore.Machine.Step.unseqEnter

-- ---- RE-PIN 7 (window unit 5b, the `intn` pick site, 2026-09-30) ----

-- 133. `MachineSound.lean` — the `[0, n)` draw's apply EQUATION: at the `randIntn` apply with an address
-- target and bound `n ≥ 1`, the apply stores the tape's `intn` pick at bound `n` (an `int`) and returns the
-- popped tape beside exactly the record `PickRecord.ofPick .intn n.toNat pick` (`[]` at `n = 1`, the no-pop
-- instance; the one labelled pick otherwise)
example : ∀ {ctx : ProgramCtx} {σ : Store} {tv : GoValue} {tloc : Loc} {n : Int} {ch : Choices},
    valueAsLoc tv = .ok tloc → 1 ≤ n →
    applyStmtOp ctx σ ch .randIntn 1 [tv, .int n .int]
      = (Mem.store ctx σ tloc (.int (Choices.consumeAt .intn n.toNat ch).1 .int)).map
          fun p => (p.1, (Choices.consumeAt .intn n.toNat ch).2,
            PickRecord.ofPick .intn n.toNat (Choices.consumeAt .intn n.toNat ch).1, p.2) :=
  @GoLean.GoCore.Machine.applyStmtOp_randIntn_eq

-- 134. `MachineSound.lean` — the draw's STEP RULE, derived from `stmtOpApply` (the logic team's «one step
-- rule»): for every `i < n` the singleton tape `[i]` takes the step storing `i` into the target, with the
-- label `⟨tr, PickRecord.ofPick .intn n.toNat i, []⟩` — the relation admits every member of `[0, n)`
example : ∀ {ctx : ProgramCtx} {σ : Store} {tv : GoValue} {tloc : Loc} {n : Int} {env : LocalEnv} {k : Cont},
    valueAsLoc tv = .ok tloc → 1 ≤ n → ∀ {i : Nat}, i < n.toNat →
    ∀ {σ' : Store} {tr : AccessTrace}, Mem.store ctx σ tloc (.int i .int) = .ok (σ', tr) →
    Step ctx (.retV (.int n .int) (.stmtOpK .randIntn 1 [tv] [] env k)) σ (.next k) σ'
      ⟨tr, PickRecord.ofPick .intn n.toNat i, []⟩ :=
  @GoLean.GoCore.Machine.Step_randIntn_draw

-- 135. `MachineSound.lean` — the pick-lifted plan at a POPPING bound (`intnBound? = some w`): the validate
-- phase is a function of the `intn` pick alone beside the site's pop and its record, and never panics
example : ∀ {ctx : ProgramCtx} {σ : Store} {nt : Nat} {vs : List GoValue} {w : Nat},
    intnBound? vs = some w →
    ∃ g : Nat → Except Stop (Commit (Store × AccessTrace)),
      (∀ ch : Choices,
        applyStmtOp.plan ctx σ ch .randIntn nt vs
          = (g (Choices.consumeAt .intn w ch).1).map
              (Commit.withStream (Choices.consumeAt .intn w ch).2
                [⟨.intn, w, (Choices.consumeAt .intn w ch).1⟩]))
      ∧ (∀ pick, NoPanic (g pick)) :=
  @GoLean.GoCore.Machine.applyStmtOp_plan_randIntn_draw

-- ---- RE-PIN 8 (window row 6, C4 block-entry allocation, 2026-10-01) ----

-- 136. `Machine.lean` — THE LAYOUT FUNCTION (D8, request 4): the `i`-th cell an entry allocates from
-- store `s` — frame entry's `args[i]` / `results[args.size + j]`, block entry's `decls[i]`
example : ∀ (s : Store) (i : Nat), entrySlot s i = .base ⟨s.heap.size + i⟩ :=
  GoLean.GoCore.Machine.entrySlot_def

-- 137. `Machine.lean` — two slots of one entry are distinct iff their indices are
example : ∀ (s : Store) {i j : Nat}, entrySlot s i = entrySlot s j ↔ i = j :=
  @GoLean.GoCore.Machine.entrySlot_inj

-- 138. `Machine.lean` — the block-entry RULE (every declaration of a decoded program since C4 is some
-- block's; `Stmt.initialization` is gone): the block's declarations allocate under a fresh scope
example : ∀ {ctx : ProgramCtx} {decls : Array Param} {ss : Array Stmt} {env env' : LocalEnv} {k : Cont}
    {s s' : Store},
    allocDecls ctx env.pushScope s decls.toList = .ok (env', s') →
    Step ctx (.exec (.block decls ss) env k) s (.next (.seq ss.toList env' k)) s' ⟨[], [], []⟩ :=
  @GoLean.GoCore.Machine.Step.block

-- 139. `Machine.lean` — block entry SHIFTS the heap by the declaration count
example : ∀ {ctx : ProgramCtx} {env env' : LocalEnv} {s s' : Store} {decls : Array Param},
    allocDecls ctx env.pushScope s decls.toList = .ok (env', s') →
    s'.heap.size = s.heap.size + decls.size :=
  @GoLean.GoCore.Machine.blockEntry_shift

-- 140. `Machine.lean` — block entry binds declaration `i` to `entrySlot s i` (premise: the block's ids
-- pairwise distinct — the decoder's per-block dedupe, D5)
example : ∀ {ctx : ProgramCtx} {env env' : LocalEnv} {s s' : Store} {decls : Array Param},
    allocDecls ctx env.pushScope s decls.toList = .ok (env', s') →
    namesDistinct (decls.toList.map (·.id)) = true →
    ∀ (i : Nat) (hi : i < decls.size), LocalEnv.lookup env' decls[i].id = some (entrySlot s i) :=
  @GoLean.GoCore.Machine.blockEntry_lookup

-- 141. `Machine.lean` — an id the block does not declare resolves as in the enclosing environment
-- (shadowing by scope)
example : ∀ {ctx : ProgramCtx} {env env' : LocalEnv} {s s' : Store} {decls : Array Param},
    allocDecls ctx env.pushScope s decls.toList = .ok (env', s') →
    ∀ {id : VarId}, id ∉ decls.toList.map (·.id) → LocalEnv.lookup env' id = LocalEnv.lookup env id :=
  @GoLean.GoCore.Machine.blockEntry_lookup_outer

-- 142. `Machine.lean` — FRESHNESS, the heap half: an entry slot is no cell of the entry store
example : ∀ (s : Store) (i : Nat), Heap.lookup s.heap (entrySlot s i) = none :=
  GoLean.GoCore.Machine.entrySlot_not_allocated

-- 143. `StateWf.lean` — FRESHNESS, the environment half: no binding of a loc-bounded environment names
-- an entry slot (with `ConfigWf`: no existing value, environment or label names the new cell)
example : ∀ {env : LocalEnv} {s : Store}, LocalEnv.locSup env ≤ s.nextAddr →
    ∀ (id : VarId) (i : Nat), LocalEnv.lookup env id ≠ some (entrySlot s i) :=
  @GoLean.GoCore.Machine.blockEntry_fresh

-- 144. `Machine.lean` — ZERO VALUE AT ENTRY: declaration `i`'s cell holds `defaultValue` normalized at
-- the declared type (`Store.alloc` normalizes at birth — the C1 D3 premise), at that type
example : ∀ {ctx : ProgramCtx} {env env' : LocalEnv} {s s' : Store} {decls : Array Param},
    allocDecls ctx env.pushScope s decls.toList = .ok (env', s') →
    ∀ (i : Nat) (hi : i < decls.size),
      ∃ v₀ v, defaultValue ctx decls[i].typ = .ok v₀
        ∧ normalizeValueForTy ctx decls[i].typ v₀ = .ok v
        ∧ Heap.lookup s'.heap (entrySlot s i) = some (.value decls[i].typ v) :=
  @GoLean.GoCore.Machine.blockEntry_zero

-- 145. `Machine.lean` — BLOCK EXIT, the rule: the `.seq []` pop is store-neutral
example : ∀ {ctx : ProgramCtx} {env : LocalEnv} {k : Cont} {s : Store},
    Step ctx (.next (.seq [] env k)) s (.next k) s ⟨[], [], []⟩ :=
  @GoLean.GoCore.Machine.Step.seqDone

-- 146. `StepFn.lean` — BLOCK EXIT, the executable: the pop returns the same store (an escaped /
-- captured cell survives its block's lexical exit)
example : ∀ {ctx : ProgramCtx} (s : Store) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.next (.seq [] env k)) ch = .ok (.next k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Machine.blockExit_store_eq

-- 147. `StateWf.lean` — the heap never shrinks along a step (the lifetime half of `frameEntry_fresh`;
-- the `σ.nextAddr ≤ σ'.nextAddr` conjunct of `step_preserves_wf_loc`, named)
example : ∀ {ctx : ProgramCtx} {c : Config} {σ : Store} {c' : Config} {σ' : Store} {l : StepLabel},
    Step ctx c σ c' σ' l → StateWf ctx σ → ConfigWf σ.nextAddr c → σ.heap.size ≤ σ'.heap.size :=
  @GoLean.GoCore.Machine.heap_size_mono

-- 148. `Machine.lean` — frame entry SHIFTS the heap by the activation's slot count
example : ∀ {ctx : ProgramCtx} {s : Store} {fid : FuncId} {argVals : List GoValue} {func : Func},
    findFunctionIn? ctx.functions fid = some func →
    (∀ m, methodInfoByFuncId? ctx func.id = some m → methodRecvInterfaceName? m = none) →
    func.args.size = argVals.length →
    ∀ {frameEnv : LocalEnv} {resultLocs : List Loc} {s' : Store} {tr : AccessTrace},
    enterFrame ctx s fid argVals = .ok (.run func frameEnv resultLocs, s', tr) →
    s'.heap.size = s.heap.size + func.args.size + func.results.size :=
  @GoLean.GoCore.Machine.enterFrame_shift

-- 149. `Machine.lean` — frame entry through the layout function, arguments (row 124 restated)
example : ∀ {ctx : ProgramCtx} {s : Store} {fid : FuncId} {argVals : List GoValue} {func : Func},
    findFunctionIn? ctx.functions fid = some func →
    (∀ m, methodInfoByFuncId? ctx func.id = some m → methodRecvInterfaceName? m = none) →
    func.args.size = argVals.length →
    namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true →
    ∀ {frameEnv : LocalEnv} {resultLocs : List Loc} {s' : Store} {tr : AccessTrace},
    enterFrame ctx s fid argVals = .ok (.run func frameEnv resultLocs, s', tr) →
    ∀ (i : Nat) (hi : i < func.args.size),
      LocalEnv.lookup frameEnv func.args[i].id = some (entrySlot s i) :=
  @GoLean.GoCore.Machine.frameEntry_lookup_arg

-- 150. `Machine.lean` — frame entry through the layout function, results (row 125 restated)
example : ∀ {ctx : ProgramCtx} {s : Store} {fid : FuncId} {argVals : List GoValue} {func : Func},
    findFunctionIn? ctx.functions fid = some func →
    (∀ m, methodInfoByFuncId? ctx func.id = some m → methodRecvInterfaceName? m = none) →
    func.args.size = argVals.length →
    namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true →
    ∀ {frameEnv : LocalEnv} {resultLocs : List Loc} {s' : Store} {tr : AccessTrace},
    enterFrame ctx s fid argVals = .ok (.run func frameEnv resultLocs, s', tr) →
    ∀ (j : Nat) (hj : j < func.results.size),
      LocalEnv.lookup frameEnv func.results[j].id = some (entrySlot s (func.args.size + j)) :=
  @GoLean.GoCore.Machine.frameEntry_lookup_result

-- 151. `Machine.lean` — two activations never share a slot (layout arithmetic; the lifetime premise
-- is row 147 composed along the run)
example : ∀ {s₁ s₂ : Store} {n : Nat}, s₁.heap.size + n ≤ s₂.heap.size →
    ∀ {i : Nat}, i < n → ∀ (j : Nat), entrySlot s₁ i ≠ entrySlot s₂ j :=
  @GoLean.GoCore.Machine.frameEntry_fresh

-- 152. `Machine.lean` — D7, a deferred call saves argument VALUES (no store involved)
example : ∀ (f : GoValue) (vs : List GoValue) (t : List (TargetShape × List Expr)) (te : LocalEnv)
    (r : List Loc) (ds : List (GoValue × List GoValue)) (fr : FuncId) (k : Cont),
    pushDefer (f, vs) (Frame.frame t te r ds fr :: k) = some (Frame.frame t te r ((f, vs) :: ds) fr :: k) :=
  GoLean.GoCore.Machine.pushDefer_saves_values

-- 153. `Machine.lean` — D7, a closure value packs its capture operands' VALUES, store untouched …
example : ∀ {ctx : ProgramCtx} (s : Store) (leafOf : Loc → Loc) (fid : FuncId) (vs : List GoValue),
    applyStrictOp ctx s leafOf (.funcValOf fid) vs = .ok (.funcVal fid vs, s, []) :=
  @GoLean.GoCore.Machine.funcVal_captures_locs

-- 154. `Machine.lean` — … and a capture operand `.ref x` evaluates to the local's cell ADDRESS
example : ∀ {ctx : ProgramCtx} {id : VarId} {loc : Loc} {env : LocalEnv} {k : Cont} {s : Store},
    LocalEnv.lookup env id = some loc →
    Step ctx (.evalE (.ref id) env k) s (.retV (.addr loc) k) s ⟨[], [], []⟩ :=
  @GoLean.GoCore.Machine.Step.evalRef

-- RE-PIN 9 (unit 6b, the preprint phase) — rows 155–173.
-- 155. `Machine.lean` — the abort IS a settled unrecovered chain at `.stop` (row 19's equation)
example : ∀ {c : Config} {first : PanicEntry} {rest : List PanicEntry},
    c.abort? = some (first, rest) ↔
      c = .panicking (first :: rest) .stop ∧ splitNewestPending? (first :: rest) = none :=
  @GoLean.GoCore.Machine.Config.abort?_some_iff

-- 156. `Machine.lean` — the phase's cursor splits the chain
example : ∀ {chain older : List PanicEntry} {entry : PanicEntry} {newer : List PanicEntry},
    splitNewestPending? chain = some (older, entry, newer) → chain = older ++ entry :: newer :=
  @GoLean.GoCore.Machine.splitNewestPending?_eq

-- 157. `Machine.lean` — … at an entry whose rewrite is owed
example : ∀ {chain older : List PanicEntry} {entry : PanicEntry} {newer : List PanicEntry},
    splitNewestPending? chain = some (older, entry, newer) → entry.isPending = true :=
  @GoLean.GoCore.Machine.splitNewestPending?_pending

-- 158. `StringPanic.lean` — the renderer on a REWRITTEN payload is the string member function
example : ∀ {ctx : ProgramCtx} (first : PanicEntry) (rest : List PanicEntry) (text : GoString) (pick : Nat),
    rewritableBox first.value → first.rewrite = .done text →
    renderPanicHead ctx first rest pick =
      stringPanicHead text first.recovered (collapseBit first rest pick) :=
  @GoLean.GoCore.Machine.renderPanicHead_text

-- 159. `StringPanic.lean` — the abort message on a rewritten payload
example : ∀ {ctx : ProgramCtx} (first : PanicEntry) (rest : List PanicEntry) (text : GoString) (pick : Nat)
    (msg : String), rewritableBox first.value → first.rewrite = .done text →
    stringPanicHead text first.recovered (collapseBit first rest pick) = some msg →
    abortMsg ctx first rest pick = .ok msg :=
  @GoLean.GoCore.Machine.abortMsg_text

-- 160. `StringPanic.lean` — … and its refusal, by name
example : ∀ {ctx : ProgramCtx} (first : PanicEntry) (rest : List PanicEntry) (text : GoString) (pick : Nat),
    rewritableBox first.value → first.rewrite = .done text →
    stringPanicHead text first.recovered (collapseBit first rest pick) = none →
    abortMsg ctx first rest pick = .error (.unsupported (abortRefusal ctx first)) :=
  @GoLean.GoCore.Machine.abortMsg_text_refused

-- 161. `StringPanic.lean` — the sequential abort step on a rewritten payload
example : ∀ {ctx : ProgramCtx} (s : Store) (c : Config) (choices : Choices) (first : PanicEntry)
    (rest : List PanicEntry) (text : GoString) (msg : String),
    c.abort? = some (first, rest) → rewritableBox first.value → first.rewrite = .done text →
    stringPanicHead text first.recovered
      (collapseBit first rest (abortConsult first rest choices).1) = some msg →
    stepFn ctx s c choices = .error (.panic msg) :=
  @GoLean.GoCore.Machine.stepFn_text_abort

-- 162. `StringPanic.lean` — the bounded run's abort on a rewritten payload
example : ∀ {ctx : ProgramCtx} (fuel : Nat) (s : Store) (c : Config) (choices : Choices)
    (first : PanicEntry) (rest : List PanicEntry) (text : GoString) (msg : String),
    c.abort? = some (first, rest) → rewritableBox first.value → first.rewrite = .done text →
    stringPanicHead text first.recovered
      (collapseBit first rest (abortConsult first rest choices).1) = some msg →
    runConfig ctx (fuel + 1) s c choices = .error (.panic msg) :=
  @GoLean.GoCore.Machine.runConfig_text_abort

-- 163. `Machine.lean` — the phase's collapse (slot 0 at a collision)
example : ∀ {ctx : ProgramCtx} {chain older : List PanicEntry} {entry : PanicEntry}
    {newer : List PanicEntry} {s : Store},
    splitNewestPending? chain = some (older, entry, newer) → preprintCollide older entry = true →
    Step ctx (.panicking chain .stop) s (.panicking (preprintDrop older newer) .stop) s
      ⟨[], [⟨.repanicCollapse, 2, 0⟩], []⟩ :=
  @GoLean.GoCore.Machine.Step.preprintCollapse

-- 164. `Machine.lean` — the phase's selection at a collision (slot 1)
example : ∀ {ctx : ProgramCtx} {chain older : List PanicEntry} {entry : PanicEntry}
    {newer : List PanicEntry} {s : Store},
    splitNewestPending? chain = some (older, entry, newer) → preprintCollide older entry = true →
    Step ctx (.panicking chain .stop) s (.next (.preprintK older entry newer .stop)) s
      ⟨[], [⟨.repanicCollapse, 2, 1⟩], []⟩ :=
  @GoLean.GoCore.Machine.Step.preprintDistinct

-- 165. `Machine.lean` — the phase's selection with no collision (no draw)
example : ∀ {ctx : ProgramCtx} {chain older : List PanicEntry} {entry : PanicEntry}
    {newer : List PanicEntry} {s : Store},
    splitNewestPending? chain = some (older, entry, newer) → preprintCollide older entry = false →
    Step ctx (.panicking chain .stop) s (.next (.preprintK older entry newer .stop)) s ⟨[], [], []⟩ :=
  @GoLean.GoCore.Machine.Step.preprintSelect

-- 166. `Machine.lean` — the call's resolution at the preprint frame, re-queued as a value call
example : ∀ {ctx : ProgramCtx} {older : List PanicEntry} {entry : PanicEntry} {newer : List PanicEntry}
    {k : Cont} {s : Store} {r : Result (FuncId × GoValue × AccessTrace)} {c' : Config} {s' : Store}
    {l : StepLabel},
    toResult (preprintDispatch ctx s entry) = .ok r →
    deliver s (.preprintK older entry newer k)
      (fun (fid, recv, tr) =>
        (.retV (.funcVal fid [recv]) (.callValCalleeK [] [] [] (.preprintK older entry newer k)),
          s, ⟨tr, [], []⟩)) r = (c', s', l) →
    Step ctx (.next (.preprintK older entry newer k)) s c' s' l :=
  @GoLean.GoCore.Machine.Step.preprintResolve

-- 167. `Machine.lean` — the method's frame exit delivers its one result to the frame (`return`)
example : ∀ {ctx : ProgramCtx} {tenv : LocalEnv} {rl : Loc} {older : List PanicEntry} {entry : PanicEntry}
    {newer : List PanicEntry} {k : Cont} {fr : FuncId} {s : Store} {v : GoValue} {tr : AccessTrace},
    Mem.loadBinding ctx s rl = .ok (v, tr) →
    Step ctx (.signal .ret (.frame [] tenv [rl] [] (.preprintK older entry newer k) fr)) s
      (.retV v (.preprintK older entry newer k)) s ⟨tr, [], []⟩ :=
  @GoLean.GoCore.Machine.Step.preprintReturn

-- 168. `Machine.lean` — … and on the fall-through entry
example : ∀ {ctx : ProgramCtx} {tenv : LocalEnv} {rl : Loc} {older : List PanicEntry} {entry : PanicEntry}
    {newer : List PanicEntry} {k : Cont} {fr : FuncId} {s : Store} {v : GoValue} {tr : AccessTrace},
    Mem.loadBinding ctx s rl = .ok (v, tr) →
    Step ctx (.next (.frame [] tenv [rl] [] (.preprintK older entry newer k) fr)) s
      (.retV v (.preprintK older entry newer k)) s ⟨tr, [], []⟩ :=
  @GoLean.GoCore.Machine.Step.preprintFall

-- 169. `Machine.lean` — the returned string is stored beside the payload; the chain resumes
example : ∀ {ctx : ProgramCtx} {older : List PanicEntry} {entry : PanicEntry} {newer : List PanicEntry}
    {k : Cont} {s : Store} {text : GoString},
    Step ctx (.retV (.string text) (.preprintK older entry newer k)) s
      (.panicking (older ++ { entry with rewrite := .done text } :: newer) k) s ⟨[], [], []⟩ :=
  @GoLean.GoCore.Machine.Step.preprintStore

-- 170. `MachineSound.lean` — no rule steps a SETTLED chain at `.stop` (the abort is terminal)
example : ∀ {ctx : ProgramCtx} {chain : List PanicEntry} {σ : Store} {c' : Config} {σ' : Store}
    {tr : StepLabel}, splitNewestPending? chain = none →
    ¬ Step ctx (.panicking chain .stop) σ c' σ' tr :=
  @GoLean.GoCore.Machine.step_abort_elim

-- 171. `MachineSound.lean` — a chain that steps at `.stop` is unsettled
example : ∀ {ctx : ProgramCtx} {chain : List PanicEntry} {σ : Store} {c' : Config} {σ' : Store}
    {tr : StepLabel}, Step ctx (.panicking chain .stop) σ c' σ' tr →
    ∃ older entry newer, splitNewestPending? chain = some (older, entry, newer) :=
  @GoLean.GoCore.Machine.step_stop_unsettled

-- 172. `Machine.lean` — the entry's rewrite mark at the raise (the shape, row 19's companion)
example : GoValue → PanicEntry := fun v => @GoLean.GoCore.Machine.panicEntryOf (ProgramCtx.ofTables (types := TypeEnv.reserved)) v

-- 173. `Machine.lean` — the fatal of a panic inside the payload method, as a `Stop`
example : ProgramCtx → List PanicEntry → Stop := @GoLean.GoCore.Machine.preprintFatalStop


-- ---- RE-PIN 10 (window packet D: the equations, rows 174–402; the pool projections, rows 403–436) ----

-- 174. `Equations.lean` — `storeTarget_inv_panic`
example : ∀ {ctx : ProgramCtx} {s : Store} {r : TargetRef} {v : GoValue} {msg : String}
    (_h : storeTarget ctx s r v = .error (.panic msg)),
    storeTarget.plan ctx s r v = .error (.panic msg) :=
  @GoLean.GoCore.Equations.storeTarget_inv_panic

-- 175. `Equations.lean` — `applyStmtOp_inv_panic`
example : ∀ {ctx : ProgramCtx} {s : Store} {ch : Choices} {op : StmtOp} {nt : Nat} {vs : List GoValue}
    {msg : String} (_h : applyStmtOp ctx s ch op nt vs = .error (.panic msg)),
    applyStmtOp.plan ctx s ch op nt vs = .error (.panic msg) :=
  @GoLean.GoCore.Equations.applyStmtOp_inv_panic

-- 176. `Equations.lean` — `toResult_of_error`
example : ∀ {α : Type} {x : Except Stop α} {e : Stop} (_h : x = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    toResult x = .error e :=
  @GoLean.GoCore.Equations.toResult_of_error

-- 177. `Equations.lean` — `valueAsBool_bool`
example : ∀ (b : Bool),
    valueAsBool (.bool b) = .ok b :=
  @GoLean.GoCore.Equations.valueAsBool_bool

-- 178. `Equations.lean` — `valueAsLoc_addr`
example : ∀ (loc : Loc),
    valueAsLoc (.addr loc) = .ok loc :=
  @GoLean.GoCore.Equations.valueAsLoc_addr

-- 179. `Equations.lean` — `valueAsLoc_nil`
example :
    valueAsLoc .nil = .error (.panic nilDerefPanicText) :=
  @GoLean.GoCore.Equations.valueAsLoc_nil

-- 180. `Equations.lean` — `targetPlan_var`
example : ∀ (id : VarId),
    targetPlan (.var id) = some (.chain [], [.ref id]) :=
  @GoLean.GoCore.Equations.targetPlan_var

-- 181. `Equations.lean` — `completeTargetRef_var`
example : ∀ (a : GoValue),
    completeTargetRef (.chain []) [a] = some (.chain a [] []) :=
  @GoLean.GoCore.Equations.completeTargetRef_var

-- 182. `Equations.lean` — `resolveChain_nil`
example : ∀ {ctx : ProgramCtx} (s : Store) (a : GoValue),
    resolveChain ctx s a [] [] = .ok a :=
  @GoLean.GoCore.Equations.resolveChain_nil

-- 183. `Equations.lean` — `applyRhsOp_vals`
example : ∀ {ctx : ProgramCtx} (s : Store) (vs : List GoValue),
    applyRhsOp ctx s .vals vs = .ok (vs, []) :=
  @GoLean.GoCore.Equations.applyRhsOp_vals

-- 184. `Equations.lean` — `loadRoot_base`
example : ∀ {ctx : ProgramCtx} {s : Store} {a : Addr} {ty : Ty} {v : GoValue}
    (_hl : Heap.lookup s.heap (.base a) = some (.value ty v)),
    loadRoot ctx s (.base a) = .ok v :=
  @GoLean.GoCore.Equations.loadRoot_base

-- 185. `Equations.lean` — `storeLoc_root`
example : ∀ {ctx : ProgramCtx} {s : Store} {a : Addr} {ty : Ty} {old v v' : GoValue}
    (hl : Heap.lookup s.heap (.base a) = some (.value ty old)) (_hn : normalizeValueForTy ctx ty v = .ok v'),
    storeLoc ctx s (.base a) v = .ok { heap := s.heap.set a.id (.value ty v') (Heap.lookup_lt hl) } :=
  @GoLean.GoCore.Equations.storeLoc_root

-- 186. `Equations.lean` — `Heap.lookup_set_self`
example : ∀ {h : Heap} {i : Nat} {c : HeapCell} {hi : i < h.size},
    Heap.lookup (h.set i c hi) (.base ⟨i⟩) = some c :=
  @GoLean.GoCore.Equations.Heap.lookup_set_self

-- 187. `Equations.lean` — `Heap.lookup_push_self`
example : ∀ {h : Heap} {c : HeapCell},
    Heap.lookup (h.push c) (.base ⟨h.size⟩) = some c :=
  @GoLean.GoCore.Equations.Heap.lookup_push_self

-- 188. `Equations.lean` — `exec_seqn`
example : ∀ {ctx : ProgramCtx} (s : Store) (ss : Array Stmt) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.seqn ss) env k) ch = .ok (.next (seqCont ss.toList env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_seqn

-- 189. `Equations.lean` — `exec_ifThenElse`
example : ∀ {ctx : ProgramCtx} (s : Store) (c : Expr) (t e : Stmt) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.ifThenElse c t e) env k) ch = .ok (.evalE c env (.ifK t e env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_ifThenElse

-- 190. `Equations.lean` — `exec_while`
example : ∀ {ctx : ProgramCtx} (s : Store) (c : Expr) (b : Stmt) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.while c b) env k) ch = .ok (.evalE c env (.whileK c b env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_while

-- 191. `Equations.lean` — `exec_returnStmt`
example : ∀ {ctx : ProgramCtx} (s : Store) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec .returnStmt env k) ch = .ok (.signal .ret k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_returnStmt

-- 192. `Equations.lean` — `exec_breakStmt`
example : ∀ {ctx : ProgramCtx} (s : Store) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec .breakStmt env k) ch = .ok (.signal .brk k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_breakStmt

-- 193. `Equations.lean` — `exec_continueStmt`
example : ∀ {ctx : ProgramCtx} (s : Store) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec .continueStmt env k) ch = .ok (.signal .cont k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_continueStmt

-- 194. `Equations.lean` — `exec_inertLabel`
example : ∀ {ctx : ProgramCtx} (s : Store) (name : String) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.inertLabel name) env k) ch = .ok (.next k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_inertLabel

-- 195. `Equations.lean` — `exec_labeled`
example : ∀ {ctx : ProgramCtx} (s : Store) (name : String) (b : Stmt) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.labeled name b) env k) ch = .ok (.exec b env (.labelK name k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_labeled

-- 196. `Equations.lean` — `exec_breakTo`
example : ∀ {ctx : ProgramCtx} (s : Store) (name : String) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.breakTo name) env k) ch = .ok (.signal (.brkTo name) k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_breakTo

-- 197. `Equations.lean` — `exec_continueTo`
example : ∀ {ctx : ProgramCtx} (s : Store) (name : String) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.continueTo name) env k) ch = .ok (.signal (.contTo name) k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_continueTo

-- 198. `Equations.lean` — `exec_breakable`
example : ∀ {ctx : ProgramCtx} (s : Store) (b : Stmt) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.breakable b) env k) ch = .ok (.exec b env (.breakableK k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_breakable

-- 199. `Equations.lean` — `exec_unsupported`
example : ∀ {ctx : ProgramCtx} (s : Store) (feature : String) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.unsupported feature) env k) ch = .error (.unsupported feature) :=
  @GoLean.GoCore.Equations.exec_unsupported

-- 200. `Equations.lean` — `exec_call_args`
example : ∀ {ctx : ProgramCtx} {s : Store} {targets : Array Assignee} {fid : FuncId} {args : Array Expr}
    {plans : List (TargetShape × List Expr)} {a : Expr} {rest : List Expr} (env : LocalEnv) (k : Cont)
    (ch : Choices) (_hp : targetsPlan targets.toList = some plans) (_hargs : args.toList = a :: rest),
    stepFn ctx s (.exec (.call targets fid args) env k) ch
      = .ok (.evalE a env (.callArgsK fid plans [] rest env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_call_args

-- 201. `Equations.lean` — `exec_call_nullary`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {targets : Array Assignee} {fid : FuncId} {args : Array Expr}
    {plans : List (TargetShape × List Expr)} {e : Entry} {tr : AccessTrace} (env : LocalEnv) (k : Cont)
    (ch : Choices) (_hp : targetsPlan targets.toList = some plans) (_hargs : args.toList = [])
    (_he : enterFrame ctx s fid [] = .ok (e, s', tr)),
    stepFn ctx s (.exec (.call targets fid args) env k) ch = .ok (e.callConfig plans env k, s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.exec_call_nullary

-- 202. `Equations.lean` — `exec_call_nullary_panic`
example : ∀ {ctx : ProgramCtx} {s : Store} {targets : Array Assignee} {fid : FuncId} {args : Array Expr}
    {plans : List (TargetShape × List Expr)} {msg : String} (env : LocalEnv) (k : Cont) (ch : Choices)
    (_hp : targetsPlan targets.toList = some plans) (_hargs : args.toList = [])
    (_he : enterFrame ctx s fid [] = .error (.panic msg)),
    stepFn ctx s (.exec (.call targets fid args) env k) ch
      = .ok (.panicking [panicEntry (entryPanicText ctx fid [] msg
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid []) ch).1)] k, s,
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid []) ch).2,
            ⟨[], PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid [])
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid []) ch).1, []⟩) :=
  @GoLean.GoCore.Equations.exec_call_nullary_panic

-- 203. `Equations.lean` — `exec_call_unsupported`
example : ∀ {ctx : ProgramCtx} {s : Store} {targets : Array Assignee} {fid : FuncId} {args : Array Expr}
    (env : LocalEnv) (k : Cont) (ch : Choices) (_hp : targetsPlan targets.toList = none),
    stepFn ctx s (.exec (.call targets fid args) env k) ch = .error (.unsupported "unsupported call target assignee") :=
  @GoLean.GoCore.Equations.exec_call_unsupported

-- 204. `Equations.lean` — `exec_callValue`
example : ∀ {ctx : ProgramCtx} {s : Store} {targets : Array Assignee} {callee : Expr} {args : Array Expr}
    {plans : List (TargetShape × List Expr)} (env : LocalEnv) (k : Cont) (ch : Choices)
    (_hp : targetsPlan targets.toList = some plans),
    stepFn ctx s (.exec (.callValue targets callee args) env k) ch
      = .ok (.evalE callee env (.callValCalleeK plans args.toList env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_callValue

-- 205. `Equations.lean` — `exec_callValue_unsupported`
example : ∀ {ctx : ProgramCtx} {s : Store} {targets : Array Assignee} {callee : Expr} {args : Array Expr}
    (env : LocalEnv) (k : Cont) (ch : Choices) (_hp : targetsPlan targets.toList = none),
    stepFn ctx s (.exec (.callValue targets callee args) env k) ch
      = .error (.unsupported "unsupported value-call target assignee") :=
  @GoLean.GoCore.Equations.exec_callValue_unsupported

-- 206. `Equations.lean` — `retV_callArgsK_more`
example : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (fid : FuncId) (plans : List (TargetShape × List Expr))
    (vals : List GoValue) (a : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.callArgsK fid plans vals (a :: rest) env k')) ch
      = .ok (.evalE a env (.callArgsK fid plans (vals ++ [v]) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_callArgsK_more

-- 207. `Equations.lean` — `retV_callArgsK_enter`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {v : GoValue} {fid : FuncId}
    {plans : List (TargetShape × List Expr)} {vals : List GoValue} {e : Entry} {tr : AccessTrace}
    (env : LocalEnv) (k' : Cont) (ch : Choices) (_he : enterFrame ctx s fid (vals ++ [v]) = .ok (e, s', tr)),
    stepFn ctx s (.retV v (.callArgsK fid plans vals [] env k')) ch
      = .ok (e.callConfig plans env k', s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.retV_callArgsK_enter

-- 208. `Equations.lean` — `retV_callArgsK_enter_panic`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {fid : FuncId} {plans : List (TargetShape × List Expr)}
    {vals : List GoValue} {msg : String} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_he : enterFrame ctx s fid (vals ++ [v]) = .error (.panic msg)),
    stepFn ctx s (.retV v (.callArgsK fid plans vals [] env k')) ch
      = .ok (.panicking [panicEntry (entryPanicText ctx fid (vals ++ [v]) msg
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (vals ++ [v])) ch).1)] k', s,
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (vals ++ [v])) ch).2,
            ⟨[], PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid (vals ++ [v]))
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (vals ++ [v])) ch).1, []⟩) :=
  @GoLean.GoCore.Equations.retV_callArgsK_enter_panic

-- 209. `Equations.lean` — `retV_callValCalleeK_enter`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {fid : FuncId} {captured : List GoValue}
    {plans : List (TargetShape × List Expr)} {e : Entry} {tr : AccessTrace} (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_he : enterFrame ctx s fid captured = .ok (e, s', tr)),
    stepFn ctx s (.retV (.funcVal fid captured) (.callValCalleeK plans [] env k')) ch
      = .ok (e.callConfig plans env k', s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.retV_callValCalleeK_enter

-- 210. `Equations.lean` — `retV_callValCalleeK_enter_panic`
example : ∀ {ctx : ProgramCtx} {s : Store} {fid : FuncId} {captured : List GoValue}
    {plans : List (TargetShape × List Expr)} {msg : String} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_he : enterFrame ctx s fid captured = .error (.panic msg)),
    stepFn ctx s (.retV (.funcVal fid captured) (.callValCalleeK plans [] env k')) ch
      = .ok (.panicking [panicEntry (entryPanicText ctx fid captured msg
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid captured) ch).1)] k', s,
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid captured) ch).2,
            ⟨[], PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid captured)
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid captured) ch).1, []⟩) :=
  @GoLean.GoCore.Equations.retV_callValCalleeK_enter_panic

-- 211. `Equations.lean` — `retV_callValCalleeK_nil`
example : ∀ {ctx : ProgramCtx} (s : Store) (plans : List (TargetShape × List Expr)) (env : LocalEnv) (k' : Cont)
    (ch : Choices),
    stepFn ctx s (.retV .nil (.callValCalleeK plans [] env k')) ch
      = .ok (.panicking [panicEntry nilDerefPanicText] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_callValCalleeK_nil

-- 212. `Equations.lean` — `retV_callValCalleeK_args`
example : ∀ {ctx : ProgramCtx} {s : Store} {cv : GoValue} (plans : List (TargetShape × List Expr)) (a : Expr)
    (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices) (_hd : deferrableCallee cv = true),
    stepFn ctx s (.retV cv (.callValCalleeK plans (a :: rest) env k')) ch
      = .ok (.evalE a env (.callValArgsK cv plans [] rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_callValCalleeK_args

-- 213. `Equations.lean` — `retV_callValArgsK_more`
example : ∀ {ctx : ProgramCtx} (s : Store) (v cv : GoValue) (plans : List (TargetShape × List Expr))
    (vals : List GoValue) (a : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.callValArgsK cv plans vals (a :: rest) env k')) ch
      = .ok (.evalE a env (.callValArgsK cv plans (vals ++ [v]) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_callValArgsK_more

-- 214. `Equations.lean` — `retV_callValArgsK_enter`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {v : GoValue} {fid : FuncId} {captured vals : List GoValue}
    {plans : List (TargetShape × List Expr)} {e : Entry} {tr : AccessTrace} (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_he : enterFrame ctx s fid (captured ++ vals ++ [v]) = .ok (e, s', tr)),
    stepFn ctx s (.retV v (.callValArgsK (.funcVal fid captured) plans vals [] env k')) ch
      = .ok (e.callConfig plans env k', s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.retV_callValArgsK_enter

-- 215. `Equations.lean` — `retV_callValArgsK_enter_panic`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {fid : FuncId} {captured vals : List GoValue}
    {plans : List (TargetShape × List Expr)} {msg : String} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_he : enterFrame ctx s fid (captured ++ vals ++ [v]) = .error (.panic msg)),
    stepFn ctx s (.retV v (.callValArgsK (.funcVal fid captured) plans vals [] env k')) ch
      = .ok (.panicking [panicEntry (entryPanicText ctx fid (captured ++ vals ++ [v]) msg
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ vals ++ [v])) ch).1)] k', s,
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ vals ++ [v])) ch).2,
            ⟨[], PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ vals ++ [v]))
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ vals ++ [v])) ch).1, []⟩) :=
  @GoLean.GoCore.Equations.retV_callValArgsK_enter_panic

-- 216. `Equations.lean` — `retV_callValArgsK_nil`
example : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (plans : List (TargetShape × List Expr))
    (vals : List GoValue) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.callValArgsK .nil plans vals [] env k')) ch
      = .ok (.panicking [panicEntry nilDerefPanicText] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_callValArgsK_nil

-- 217. `Equations.lean` — `exec_deferCall`
example : ∀ {ctx : ProgramCtx} (s : Store) (callee : Expr) (args : Array Expr) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.exec (.deferCall callee args) env k) ch
      = .ok (.evalE callee env (.deferCalleeK args.toList env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_deferCall

-- 218. `Equations.lean` — `retV_deferCalleeK_args`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (a : Expr) (rest : List Expr) (env : LocalEnv)
    (k' : Cont) (ch : Choices) (_hd : deferrableCallee v = true),
    stepFn ctx s (.retV v (.deferCalleeK (a :: rest) env k')) ch
      = .ok (.evalE a env (.deferArgsK v [] rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_deferCalleeK_args

-- 219. `Equations.lean` — `retV_deferCalleeK_push`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {k' k'' : Cont} (env : LocalEnv) (ch : Choices)
    (_hd : deferrableCallee v = true) (_hp : pushDefer (v, []) k' = some k''),
    stepFn ctx s (.retV v (.deferCalleeK [] env k')) ch = .ok (.next k'', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_deferCalleeK_push

-- 220. `Equations.lean` — `retV_deferCalleeK_push_frame`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (env : LocalEnv) (ch : Choices)
    (t : List (TargetShape × List Expr)) (te : LocalEnv) (r : List Loc) (ds : List (GoValue × List GoValue))
    (k'' : Cont) (fr : FuncId) (_hd : deferrableCallee v = true),
    stepFn ctx s (.retV v (.deferCalleeK [] env (.frame t te r ds k'' fr))) ch
      = .ok (.next (.frame t te r ((v, []) :: ds) k'' fr), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_deferCalleeK_push_frame

-- 221. `Equations.lean` — `retV_deferCalleeK_outside`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {k' : Cont} (env : LocalEnv) (ch : Choices)
    (_hd : deferrableCallee v = true) (_hp : pushDefer (v, []) k' = none),
    stepFn ctx s (.retV v (.deferCalleeK [] env k')) ch = .error (.stuck "defer outside a call frame") :=
  @GoLean.GoCore.Equations.retV_deferCalleeK_outside

-- 222. `Equations.lean` — `retV_deferArgsK_more`
example : ∀ {ctx : ProgramCtx} (s : Store) (v cv : GoValue) (vals : List GoValue) (a : Expr) (rest : List Expr)
    (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.deferArgsK cv vals (a :: rest) env k')) ch
      = .ok (.evalE a env (.deferArgsK cv (vals ++ [v]) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_deferArgsK_more

-- 223. `Equations.lean` — `retV_deferArgsK_push`
example : ∀ {ctx : ProgramCtx} {s : Store} {v cv : GoValue} {vals : List GoValue} {k' k'' : Cont}
    (env : LocalEnv) (ch : Choices) (_hp : pushDefer (cv, vals ++ [v]) k' = some k''),
    stepFn ctx s (.retV v (.deferArgsK cv vals [] env k')) ch = .ok (.next k'', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_deferArgsK_push

-- 224. `Equations.lean` — `retV_deferArgsK_push_frame`
example : ∀ {ctx : ProgramCtx} (s : Store) (v cv : GoValue) (vals : List GoValue) (env : LocalEnv)
    (ch : Choices) (t : List (TargetShape × List Expr)) (te : LocalEnv) (r : List Loc)
    (ds : List (GoValue × List GoValue)) (k'' : Cont) (fr : FuncId),
    stepFn ctx s (.retV v (.deferArgsK cv vals [] env (.frame t te r ds k'' fr))) ch
      = .ok (.next (.frame t te r ((cv, vals ++ [v]) :: ds) k'' fr), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_deferArgsK_push_frame

-- 225. `Equations.lean` — `retV_deferArgsK_outside`
example : ∀ {ctx : ProgramCtx} {s : Store} {v cv : GoValue} {vals : List GoValue} {k' : Cont} (env : LocalEnv)
    (ch : Choices) (_hp : pushDefer (cv, vals ++ [v]) k' = none),
    stepFn ctx s (.retV v (.deferArgsK cv vals [] env k')) ch = .error (.stuck "defer outside a call frame") :=
  @GoLean.GoCore.Equations.retV_deferArgsK_outside

-- 226. `Equations.lean` — `exec_panicStmt`
example : ∀ {ctx : ProgramCtx} (s : Store) (e : Expr) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.panicStmt e) env k) ch = .ok (.evalE e env (.panicArgK k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_panicStmt

-- 227. `Equations.lean` — `retV_panicArgK`
example : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.panicArgK k')) ch
      = .ok (.panicking [panicEntryOf ctx (panicPayload v)] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_panicArgK

-- 228. `Equations.lean` — `evalE_recoverCall`
example : ∀ {ctx : ProgramCtx} (s : Store) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.evalE .recoverCall env k) ch
      = .ok (.retV (recoverResult k).1 (recoverResult k).2, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_recoverCall

-- 229. `Equations.lean` — `panicking_frame_empty`
example : ∀ {ctx : ProgramCtx} (s : Store) (chain : List PanicEntry) (t : List (TargetShape × List Expr))
    (te : LocalEnv) (r : List Loc) (k' : Cont) (fr : FuncId) (ch : Choices),
    stepFn ctx s (.panicking chain (.frame t te r [] k' fr)) ch = .ok (.panicking chain k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_frame_empty

-- 230. `Equations.lean` — `panicking_frame_defer`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {chain : List PanicEntry} {fid : FuncId}
    {captured args : List GoValue} {e : Entry} {tr : AccessTrace} (t : List (TargetShape × List Expr))
    (te : LocalEnv) (r : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (_he : enterFrame ctx s fid (captured ++ args) = .ok (e, s', tr)),
    stepFn ctx s (.panicking chain (.frame t te r ((.funcVal fid captured, args) :: ds) k' fr)) ch
      = .ok (e.drainConfig (.panicResumeK chain (.frame t te r ds k' fr))
              (fun cv => .panicking chain (.frame t te r ((cv, []) :: ds) k' fr)), s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_frame_defer

-- 231. `Equations.lean` — `panicking_frame_defer_run`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {chain : List PanicEntry} {fid : FuncId}
    {captured args : List GoValue} {func : Func} {fenv : LocalEnv} {rl : List Loc} {tr : AccessTrace}
    (t : List (TargetShape × List Expr)) (te : LocalEnv) (r : List Loc) (ds : List (GoValue × List GoValue))
    (k' : Cont) (fr : FuncId) (ch : Choices)
    (_he : enterFrame ctx s fid (captured ++ args) = .ok (.run func fenv rl, s', tr)),
    stepFn ctx s (.panicking chain (.frame t te r ((.funcVal fid captured, args) :: ds) k' fr)) ch
      = .ok (.exec func.body fenv (.frame [] [] [] [] (.panicResumeK chain (.frame t te r ds k' fr)) func.id),
            s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_frame_defer_run

-- 232. `Equations.lean` — `panicking_frame_defer_panic`
example : ∀ {ctx : ProgramCtx} {s : Store} {chain : List PanicEntry} {fid : FuncId}
    {captured args : List GoValue} {msg : String} (t : List (TargetShape × List Expr)) (te : LocalEnv)
    (r : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (_he : enterFrame ctx s fid (captured ++ args) = .error (.panic msg)),
    stepFn ctx s (.panicking chain (.frame t te r ((.funcVal fid captured, args) :: ds) k' fr)) ch
      = .ok (.panicking (chain ++ [panicEntry (entryPanicText ctx fid (captured ++ args) msg
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args)) ch).1)])
              (.frame t te r ds k' fr), s,
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args)) ch).2,
            ⟨[], PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args))
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args)) ch).1, []⟩) :=
  @GoLean.GoCore.Equations.panicking_frame_defer_panic

-- 233. `Equations.lean` — `panicking_frame_defer_nil`
example : ∀ {ctx : ProgramCtx} (s : Store) (chain : List PanicEntry) (args : List GoValue)
    (t : List (TargetShape × List Expr)) (te : LocalEnv) (r : List Loc) (ds : List (GoValue × List GoValue))
    (k' : Cont) (fr : FuncId) (ch : Choices),
    stepFn ctx s (.panicking chain (.frame t te r ((.nil, args) :: ds) k' fr)) ch
      = .ok (.panicking (chain ++ [panicEntry nilDerefPanicText]) (.frame t te r ds k' fr), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_frame_defer_nil

-- 234. `Equations.lean` — `panicking_panicResumeK`
example : ∀ {ctx : ProgramCtx} (s : Store) (chain suspended : List PanicEntry) (k' : Cont) (ch : Choices),
    stepFn ctx s (.panicking chain (.panicResumeK suspended k')) ch
      = .ok (.panicking (suspended ++ chain) k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_panicResumeK

-- 235. `Equations.lean` — `next_panicResumeK_unrecovered`
example : ∀ {ctx : ProgramCtx} {s : Store} {chain : List PanicEntry} (k' : Cont) (ch : Choices)
    (_h : chainNewestRecovered chain = false),
    stepFn ctx s (.next (.panicResumeK chain k')) ch = .ok (.panicking chain k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_panicResumeK_unrecovered

-- 236. `Equations.lean` — `next_panicResumeK_recovered`
example : ∀ {ctx : ProgramCtx} {s : Store} {chain : List PanicEntry} (k' : Cont) (ch : Choices)
    (_h : chainNewestRecovered chain = true),
    stepFn ctx s (.next (.panicResumeK chain k')) ch = .ok (.next k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_panicResumeK_recovered

-- 237. `Equations.lean` — `panicking_glue`
example : ∀ {ctx : ProgramCtx} {s : Store} {chain : List PanicEntry} {g : Frame} (k : Cont) (ch : Choices)
    (_hg : g.class = .stmtGlue ∨ g.class = .exprGlue),
    stepFn ctx s (.panicking chain (g :: k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_glue

-- 238. `Equations.lean` — `panicking_seq`
example : ∀ {ctx : ProgramCtx} (s : Store) (chain : List PanicEntry) (rest : List Stmt) (env : LocalEnv)
    (k : Cont) (ch : Choices),
    stepFn ctx s (.panicking chain (.seq rest env k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_seq

-- 239. `Equations.lean` — `panicking_loop`
example : ∀ {ctx : ProgramCtx} (s : Store) (chain : List PanicEntry) (c : Expr) (b : Stmt) (env : LocalEnv)
    (k : Cont) (ch : Choices),
    stepFn ctx s (.panicking chain (.loop c b env k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_loop

-- 240. `Equations.lean` — `panicking_breakableK`
example : ∀ {ctx : ProgramCtx} (s : Store) (chain : List PanicEntry) (k : Cont) (ch : Choices),
    stepFn ctx s (.panicking chain (.breakableK k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_breakableK

-- 241. `Equations.lean` — `panicking_labelK`
example : ∀ {ctx : ProgramCtx} (s : Store) (chain : List PanicEntry) (name : String) (k : Cont) (ch : Choices),
    stepFn ctx s (.panicking chain (.labelK name k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_labelK

-- 242. `Equations.lean` — `panicking_strictK`
example : ∀ {ctx : ProgramCtx} (s : Store) (chain : List PanicEntry) (op : StrictOp) (done : List GoValue)
    (pending : List Expr) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.panicking chain (.strictK op done pending env k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_strictK

-- 243. `Equations.lean` — `panicking_storeK`
example : ∀ {ctx : ProgramCtx} (s : Store) (chain : List PanicEntry) (refs : List TargetRef)
    (vals : List GoValue) (body : Stmt) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.panicking chain (.storeK refs vals body env k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_storeK

-- 244. `Equations.lean` — `panicking_probeK`
example : ∀ {ctx : ProgramCtx} (s : Store) (chain : List PanicEntry) (k' : Cont) (ch : Choices),
    stepFn ctx s (.panicking chain (.probeK k')) ch
      = .ok (if (Choices.consumeAtE .unseqPanic 2 ch).1 = 0 then .next k' else .panicking chain k', s,
            (Choices.consumeAtE .unseqPanic 2 ch).2.1, ⟨[], (Choices.consumeAtE .unseqPanic 2 ch).2.2, []⟩) :=
  @GoLean.GoCore.Equations.panicking_probeK

-- 245. `Equations.lean` — `panicking_stop_settled`
example : ∀ {ctx : ProgramCtx} {s : Store} {first : PanicEntry} {rest : List PanicEntry} (ch : Choices)
    (_hs : splitNewestPending? (first :: rest) = none),
    stepFn ctx s (.panicking (first :: rest) .stop) ch
      = (do let msg ← abortMsg ctx first rest (abortConsult first rest ch).1; throw (.panic msg)) :=
  @GoLean.GoCore.Equations.panicking_stop_settled

-- 246. `Equations.lean` — `panicking_stop_pending`
example : ∀ {ctx : ProgramCtx} {s : Store} {first : PanicEntry} {rest older : List PanicEntry}
    {entry : PanicEntry} {newer : List PanicEntry} (ch : Choices)
    (_hs : splitNewestPending? (first :: rest) = some (older, entry, newer)),
    stepFn ctx s (.panicking (first :: rest) .stop) ch
      = .ok (if preprintCollide older entry && (Choices.consumeAtE .repanicCollapse (preprintWidth older entry) ch).1 = 0
              then .panicking (preprintDrop older newer) .stop
              else .next (.preprintK older entry newer .stop), s,
            (Choices.consumeAtE .repanicCollapse (preprintWidth older entry) ch).2.1,
            ⟨[], (Choices.consumeAtE .repanicCollapse (preprintWidth older entry) ch).2.2, []⟩) :=
  @GoLean.GoCore.Equations.panicking_stop_pending

-- 247. `Equations.lean` — `panicking_nil_stop`
example : ∀ {ctx : ProgramCtx} (s : Store) (ch : Choices),
    stepFn ctx s (.panicking [] .stop) ch = .error (.internal "empty panic chain at stop") :=
  @GoLean.GoCore.Equations.panicking_nil_stop

-- 248. `Equations.lean` — `next_preprintK`
example : ∀ {ctx : ProgramCtx} {s : Store} {older : List PanicEntry} {entry : PanicEntry}
    {newer : List PanicEntry} {fid : FuncId} {recv : GoValue} {tr : AccessTrace} (k' : Cont) (ch : Choices)
    (_h : preprintDispatch ctx s entry = .ok (fid, recv, tr)),
    stepFn ctx s (.next (.preprintK older entry newer k')) ch
      = .ok (.retV (.funcVal fid [recv]) (.callValCalleeK [] [] [] (.preprintK older entry newer k')), s, ch,
            ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.next_preprintK

-- 249. `Equations.lean` — `next_preprintK_panic`
example : ∀ {ctx : ProgramCtx} {s : Store} {older : List PanicEntry} {entry : PanicEntry}
    {newer : List PanicEntry} {msg : String} (k' : Cont) (ch : Choices)
    (_h : preprintDispatch ctx s entry = .error (.panic msg)),
    stepFn ctx s (.next (.preprintK older entry newer k')) ch
      = .ok (.panicking [panicEntry msg] (.preprintK older entry newer k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_preprintK_panic

-- 250. `Equations.lean` — `retV_preprintK_string`
example : ∀ {ctx : ProgramCtx} (s : Store) (text : GoString) (older : List PanicEntry) (entry : PanicEntry)
    (newer : List PanicEntry) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV (.string text) (.preprintK older entry newer k')) ch
      = .ok (.panicking (older ++ { entry with rewrite := .done text } :: newer) k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_preprintK_string

-- 251. `Equations.lean` — `panicking_preprintK`
example : ∀ {ctx : ProgramCtx} (s : Store) (chain older : List PanicEntry) (entry : PanicEntry)
    (newer : List PanicEntry) (k' : Cont) (ch : Choices),
    stepFn ctx s (.panicking chain (.preprintK older entry newer k')) ch = .error (preprintFatalStop ctx chain) :=
  @GoLean.GoCore.Equations.panicking_preprintK

-- 252. `Equations.lean` — `next_frame`
example : ∀ {ctx : ProgramCtx} (s : Store) (targets : List (TargetShape × List Expr)) (tenv : LocalEnv)
    (results : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices),
    stepFn ctx s (.next (.frame targets tenv results ds k' fr)) ch
      = stepFrameExit ctx s targets tenv results ds k' fr ch :=
  @GoLean.GoCore.Equations.next_frame

-- 253. `Equations.lean` — `signal_ret_frame`
example : ∀ {ctx : ProgramCtx} (s : Store) (targets : List (TargetShape × List Expr)) (tenv : LocalEnv)
    (results : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices),
    stepFn ctx s (.signal .ret (.frame targets tenv results ds k' fr)) ch
      = stepFrameExit ctx s targets tenv results ds k' fr ch :=
  @GoLean.GoCore.Equations.signal_ret_frame

-- 254. `Equations.lean` — `frameExit_nil`
example : ∀ {ctx : ProgramCtx} (s : Store) (tenv : LocalEnv) (k' : Cont) (fr : FuncId) (ch : Choices),
    stepFrameExit ctx s [] tenv [] [] k' fr ch = .ok (.next k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.frameExit_nil

-- 255. `Equations.lean` — `frameExit_targets`
example : ∀ {ctx : ProgramCtx} {s : Store} {results : List Loc} {vs : List GoValue} {tr : AccessTrace}
    (sh : TargetShape) (e : Expr) (ops : List Expr) (rest : List (TargetShape × List Expr)) (tenv : LocalEnv)
    (k' : Cont) (fr : FuncId) (ch : Choices) (_hl : loadResults ctx s results = .ok (vs, tr)),
    stepFrameExit ctx s ((sh, e :: ops) :: rest) tenv results [] k' fr ch
      = .ok (.evalE e tenv (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k'), s, ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.frameExit_targets

-- 256. `Equations.lean` — `frameExit_defer`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {fid : FuncId} {captured args : List GoValue} {e : Entry}
    {tr : AccessTrace} (targets : List (TargetShape × List Expr)) (tenv : LocalEnv) (results : List Loc)
    (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (_he : enterFrame ctx s fid (captured ++ args) = .ok (e, s', tr)),
    stepFrameExit ctx s targets tenv results ((.funcVal fid captured, args) :: ds) k' fr ch
      = .ok (e.drainConfig (.frame targets tenv results ds k' fr)
              (fun cv => .next (.frame targets tenv results ((cv, []) :: ds) k' fr)), s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.frameExit_defer

-- 257. `Equations.lean` — `frameExit_defer_run`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {fid : FuncId} {captured args : List GoValue} {func : Func}
    {fenv : LocalEnv} {rl : List Loc} {tr : AccessTrace} (targets : List (TargetShape × List Expr))
    (tenv : LocalEnv) (results : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId)
    (ch : Choices) (_he : enterFrame ctx s fid (captured ++ args) = .ok (.run func fenv rl, s', tr)),
    stepFrameExit ctx s targets tenv results ((.funcVal fid captured, args) :: ds) k' fr ch
      = .ok (.exec func.body fenv (.frame [] [] [] [] (.frame targets tenv results ds k' fr) func.id), s', ch,
            ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.frameExit_defer_run

-- 258. `Equations.lean` — `frameExit_defer_panic`
example : ∀ {ctx : ProgramCtx} {s : Store} {fid : FuncId} {captured args : List GoValue} {msg : String}
    (targets : List (TargetShape × List Expr)) (tenv : LocalEnv) (results : List Loc)
    (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (_he : enterFrame ctx s fid (captured ++ args) = .error (.panic msg)),
    stepFrameExit ctx s targets tenv results ((.funcVal fid captured, args) :: ds) k' fr ch
      = .ok (.panicking [panicEntry (entryPanicText ctx fid (captured ++ args) msg
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args)) ch).1)]
              (.frame targets tenv results ds k' fr), s,
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args)) ch).2,
            ⟨[], PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args))
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args)) ch).1, []⟩) :=
  @GoLean.GoCore.Equations.frameExit_defer_panic

-- 259. `Equations.lean` — `frameExit_defer_nil`
example : ∀ {ctx : ProgramCtx} (s : Store) (args : List GoValue) (targets : List (TargetShape × List Expr))
    (tenv : LocalEnv) (results : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId)
    (ch : Choices),
    stepFrameExit ctx s targets tenv results ((.nil, args) :: ds) k' fr ch
      = .ok (.panicking [panicEntry nilDerefPanicText] (.frame targets tenv results ds k' fr), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.frameExit_defer_nil

-- 260. `Equations.lean` — `frameExit_preprint`
example : ∀ {ctx : ProgramCtx} {s : Store} {rl : Loc} {v : GoValue} (tenv : LocalEnv) (older : List PanicEntry)
    (entry : PanicEntry) (newer : List PanicEntry) (k'' : Cont) (fr : FuncId) (ch : Choices)
    (_hl : loadRoot ctx s rl = .ok v),
    stepFrameExit ctx s [] tenv [rl] [] (.preprintK older entry newer k'') fr ch
      = .ok (.retV v (.preprintK older entry newer k''), s, ch, ⟨[.access .read (.data rl.canon)], [], []⟩) :=
  @GoLean.GoCore.Equations.frameExit_preprint

-- 261. `Equations.lean` — `frameExit_extra_results`
example : ∀ {ctx : ProgramCtx} {s : Store} {rl : Loc} {rls : List Loc} {vs : List GoValue} {tr : AccessTrace}
    (tenv : LocalEnv) (k' : Cont) (fr : FuncId) (ch : Choices)
    (_hl : loadResults ctx s (rl :: rls) = .ok (vs, tr))
    (_hk : ∀ older entry newer k'', k' = .preprintK older entry newer k'' → rls ≠ []),
    stepFrameExit ctx s [] tenv (rl :: rls) [] k' fr ch = .error (.stuck "extra GoCore assignment value") :=
  @GoLean.GoCore.Equations.frameExit_extra_results

-- 262. `Equations.lean` — `frameExit_malformed`
example : ∀ {ctx : ProgramCtx} (s : Store) (sh : TargetShape) (rest : List (TargetShape × List Expr))
    (tenv : LocalEnv) (results : List Loc) (k' : Cont) (fr : FuncId) (ch : Choices),
    stepFrameExit ctx s ((sh, []) :: rest) tenv results [] k' fr ch = .error (.internal "malformed call target plan") :=
  @GoLean.GoCore.Equations.frameExit_malformed

-- 263. `Equations.lean` — `loadResults_nil`
example : ∀ {ctx : ProgramCtx} (s : Store),
    loadResults ctx s [] = .ok ([], []) :=
  @GoLean.GoCore.Equations.loadResults_nil

-- 264. `Equations.lean` — `loadResults_cons`
example : ∀ {ctx : ProgramCtx} {s : Store} {l : Loc} {ls : List Loc} {v : GoValue} {vs : List GoValue}
    {tr : AccessTrace} (_hl : loadRoot ctx s l = .ok v) (_hs : loadResults ctx s ls = .ok (vs, tr)),
    loadResults ctx s (l :: ls) = .ok (v :: vs, [.access .read (.data l.canon)] ++ tr) :=
  @GoLean.GoCore.Equations.loadResults_cons

-- 265. `Equations.lean` — `signal_table`
example : ∀ {ctx : ProgramCtx} {s : Store} {sg : Signal} {k : Cont} {c' : Config} (ch : Choices)
    (_h : signalStep sg k = some c'),
    stepFn ctx s (.signal sg k) ch = .ok (c', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.signal_table

-- 266. `Equations.lean` — `signal_stop`
example : ∀ {ctx : ProgramCtx} (s : Store) (sg : Signal) (ch : Choices),
    stepFn ctx s (.signal sg .stop) ch = .error (signalRefusal sg .stop) :=
  @GoLean.GoCore.Equations.signal_stop

-- 267. `Equations.lean` — `signal_frame_escape`
example : ∀ {ctx : ProgramCtx} {s : Store} {sg : Signal} (targets : List (TargetShape × List Expr))
    (tenv : LocalEnv) (results : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId)
    (ch : Choices) (_hsg : sg ≠ .ret),
    stepFn ctx s (.signal sg (.frame targets tenv results ds k' fr)) ch
      = .error (signalRefusal sg (.frame targets tenv results ds k' fr)) :=
  @GoLean.GoCore.Equations.signal_frame_escape

-- 268. `Equations.lean` — `signalStep_seq`
example : ∀ (sg : Signal) (rest : List Stmt) (env : LocalEnv) (k' : Cont),
    signalStep sg (.seq rest env k') = some (.signal sg k') :=
  @GoLean.GoCore.Equations.signalStep_seq

-- 269. `Equations.lean` — `signalStep_breakableK_brk`
example : ∀ (k' : Cont),
    signalStep .brk (.breakableK k') = some (.next k') :=
  @GoLean.GoCore.Equations.signalStep_breakableK_brk

-- 270. `Equations.lean` — `signalStep_breakableK_ret`
example : ∀ (k' : Cont),
    signalStep .ret (.breakableK k') = some (.signal .ret k') :=
  @GoLean.GoCore.Equations.signalStep_breakableK_ret

-- 271. `Equations.lean` — `signalStep_breakableK_cont`
example : ∀ (k' : Cont),
    signalStep .cont (.breakableK k') = some (.signal .cont k') :=
  @GoLean.GoCore.Equations.signalStep_breakableK_cont

-- 272. `Equations.lean` — `signalStep_loop_brk`
example : ∀ (c : Expr) (b : Stmt) (env : LocalEnv) (k' : Cont),
    signalStep .brk (.loop c b env k') = some (.next k') :=
  @GoLean.GoCore.Equations.signalStep_loop_brk

-- 273. `Equations.lean` — `signalStep_loop_cont`
example : ∀ (c : Expr) (b : Stmt) (env : LocalEnv) (k' : Cont),
    signalStep .cont (.loop c b env k') = some (.exec (.while c b) env k') :=
  @GoLean.GoCore.Equations.signalStep_loop_cont

-- 274. `Equations.lean` — `signalStep_loop_ret`
example : ∀ (c : Expr) (b : Stmt) (env : LocalEnv) (k' : Cont),
    signalStep .ret (.loop c b env k') = some (.signal .ret k') :=
  @GoLean.GoCore.Equations.signalStep_loop_ret

-- 275. `Equations.lean` — `signalStep_labelK_ret`
example : ∀ (name : String) (k' : Cont),
    signalStep .ret (.labelK name k') = some (.signal .ret k') :=
  @GoLean.GoCore.Equations.signalStep_labelK_ret

-- 276. `Equations.lean` — `signalStep_labelK_brkTo_self`
example : ∀ (name : String) (k' : Cont),
    signalStep (.brkTo name) (.labelK name k') = some (.next k') :=
  @GoLean.GoCore.Equations.signalStep_labelK_brkTo_self

-- 277. `Equations.lean` — `next_stop`
example : ∀ {ctx : ProgramCtx} (s : Store) (ch : Choices),
    stepFn ctx s (.next .stop) ch = .error (.internal "step on terminal configuration") :=
  @GoLean.GoCore.Equations.next_stop

-- 278. `Equations.lean` — `next_seq_cons`
example : ∀ {ctx : ProgramCtx} (s : Store) (t : Stmt) (rest : List Stmt) (env : LocalEnv) (k' : Cont)
    (ch : Choices),
    stepFn ctx s (.next (.seq (t :: rest) env k')) ch = .ok (.exec t env (.seq rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_seq_cons

-- 279. `Equations.lean` — `next_seq_nil`
example : ∀ {ctx : ProgramCtx} (s : Store) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.seq [] env k')) ch = .ok (.next k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_seq_nil

-- 280. `Equations.lean` — `next_loop`
example : ∀ {ctx : ProgramCtx} (s : Store) (c : Expr) (b : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.loop c b env k')) ch = .ok (.exec (.while c b) env k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_loop

-- 281. `Equations.lean` — `next_breakableK`
example : ∀ {ctx : ProgramCtx} (s : Store) (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.breakableK k')) ch = .ok (.next k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_breakableK

-- 282. `Equations.lean` — `next_labelK`
example : ∀ {ctx : ProgramCtx} (s : Store) (name : String) (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.labelK name k')) ch = .ok (.next k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_labelK

-- 283. `Equations.lean` — `next_strictK`
example : ∀ {ctx : ProgramCtx} (s : Store) (op : StrictOp) (done : List GoValue) (pending : List Expr)
    (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.strictK op done pending env k')) ch
      = .error (.internal "completion delivered to expression continuation") :=
  @GoLean.GoCore.Equations.next_strictK

-- 284. `Equations.lean` — `next_ifK`
example : ∀ {ctx : ProgramCtx} (s : Store) (t e : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.ifK t e env k')) ch = .error (.internal "completion delivered to expression continuation") :=
  @GoLean.GoCore.Equations.next_ifK

-- 285. `Equations.lean` — `next_callArgsK`
example : ∀ {ctx : ProgramCtx} (s : Store) (fid : FuncId) (plans : List (TargetShape × List Expr))
    (vals : List GoValue) (pending : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.callArgsK fid plans vals pending env k')) ch
      = .error (.internal "completion delivered to expression continuation") :=
  @GoLean.GoCore.Equations.next_callArgsK

-- 286. `Equations.lean` — `retV_seq`
example : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (rest : List Stmt) (env : LocalEnv) (k' : Cont)
    (ch : Choices),
    stepFn ctx s (.retV v (.seq rest env k')) ch = .error (.internal "value delivered to statement continuation") :=
  @GoLean.GoCore.Equations.retV_seq

-- 287. `Equations.lean` — `retV_frame`
example : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (targets : List (TargetShape × List Expr))
    (tenv : LocalEnv) (results : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId)
    (ch : Choices),
    stepFn ctx s (.retV v (.frame targets tenv results ds k' fr)) ch
      = .error (.internal "value delivered to statement continuation") :=
  @GoLean.GoCore.Equations.retV_frame

-- 288. `Equations.lean` — `retV_storeK`
example : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (refs : List TargetRef) (vals : List GoValue)
    (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.storeK refs vals body env k')) ch
      = .error (.internal "value delivered to statement continuation") :=
  @GoLean.GoCore.Equations.retV_storeK

-- 289. `Equations.lean` — `retV_stop`
example : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (ch : Choices),
    stepFn ctx s (.retV v .stop) ch = .error (.internal "value delivered to empty continuation") :=
  @GoLean.GoCore.Equations.retV_stop

-- 290. `Equations.lean` — `evalE_var`
example : ∀ {ctx : ProgramCtx} {s : Store} {id : VarId} {loc : Loc} {v : GoValue} (env : LocalEnv) (k : Cont)
    (ch : Choices) (_hl : LocalEnv.lookup env id = some loc) (_hv : loadRoot ctx s loc = .ok v),
    stepFn ctx s (.evalE (.var id) env k) ch
      = .ok (.retV v k, s, ch, ⟨[.access .read (.data (projChainTarget ctx s k loc).canon)], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_var

-- 291. `Equations.lean` — `evalE_var_unbound`
example : ∀ {ctx : ProgramCtx} {s : Store} {id : VarId} (env : LocalEnv) (k : Cont) (ch : Choices)
    (_hl : LocalEnv.lookup env id = none),
    stepFn ctx s (.evalE (.var id) env k) ch = .error (.stuck s!"unbound GoCore variable address: {id}") :=
  @GoLean.GoCore.Equations.evalE_var_unbound

-- 292. `Equations.lean` — `evalE_ref`
example : ∀ {ctx : ProgramCtx} {s : Store} {id : VarId} {loc : Loc} (env : LocalEnv) (k : Cont) (ch : Choices)
    (_hl : LocalEnv.lookup env id = some loc),
    stepFn ctx s (.evalE (.ref id) env k) ch = .ok (.retV (.addr loc) k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_ref

-- 293. `Equations.lean` — `evalE_ref_unbound`
example : ∀ {ctx : ProgramCtx} {s : Store} {id : VarId} (env : LocalEnv) (k : Cont) (ch : Choices)
    (_hl : LocalEnv.lookup env id = none),
    stepFn ctx s (.evalE (.ref id) env k) ch = .error (.stuck s!"unbound GoCore variable address: {id}") :=
  @GoLean.GoCore.Equations.evalE_ref_unbound

-- 294. `Equations.lean` — `evalE_global`
example : ∀ {ctx : ProgramCtx} {s : Store} {gid : Nat} (env : LocalEnv) (k : Cont) (ch : Choices)
    (_h : gid < s.heap.size),
    stepFn ctx s (.evalE (.global gid) env k) ch = .ok (.retV (.addr (.base ⟨gid⟩)) k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_global

-- 295. `Equations.lean` — `evalE_global_oob`
example : ∀ {ctx : ProgramCtx} {s : Store} {gid : Nat} (env : LocalEnv) (k : Cont) (ch : Choices)
    (_h : ¬ gid < s.heap.size),
    stepFn ctx s (.evalE (.global gid) env k) ch
      = .error (.stuck s!"global {gid} out of range: the heap has {s.heap.size} cell(s)") :=
  @GoLean.GoCore.Equations.evalE_global_oob

-- 296. `Equations.lean` — `exec_assign`
example : ∀ {ctx : ProgramCtx} {s : Store} {lhs : Assignee} {sh : TargetShape} {e : Expr} {ops : List Expr}
    (rhs : Expr) (env : LocalEnv) (k : Cont) (ch : Choices) (_h : targetPlan lhs = some (sh, e :: ops)),
    stepFn ctx s (.exec (.assign lhs rhs) env k) ch
      = .ok (.evalE e env (.tgtOpK sh [] ops [] [] .vals [rhs] [] (.seqn #[]) env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_assign

-- 297. `Equations.lean` — `exec_assign_var`
example : ∀ {ctx : ProgramCtx} (s : Store) (id : VarId) (rhs : Expr) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.assign (.var id) rhs) env k) ch
      = .ok (.evalE (.ref id) env (.tgtOpK (.chain []) [] [] [] [] .vals [rhs] [] (.seqn #[]) env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_assign_var

-- 298. `Equations.lean` — `exec_assign_unsupported`
example : ∀ {ctx : ProgramCtx} (s : Store) (feature : String) (rhs : Expr) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.exec (.assign (.unsupported feature) rhs) env k) ch = .error (.unsupported feature) :=
  @GoLean.GoCore.Equations.exec_assign_unsupported

-- 299. `Equations.lean` — `retV_tgtOpK_more`
example : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (sh : TargetShape) (ops : List GoValue) (e : Expr)
    (rest : List Expr) (refs : List TargetRef) (targets : List (TargetShape × List Expr)) (rop : RhsOp)
    (rhs : List Expr) (vals : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.tgtOpK sh ops (e :: rest) refs targets rop rhs vals body env k')) ch
      = .ok (.evalE e env (.tgtOpK sh (v :: ops) rest refs targets rop rhs vals body env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_tgtOpK_more

-- 300. `Equations.lean` — `retV_tgtOpK_next_target`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {sh : TargetShape} {ops : List GoValue} {r : TargetRef}
    (refs : List TargetRef) (sh' : TargetShape) (e : Expr) (ops' : List Expr)
    (rest : List (TargetShape × List Expr)) (rop : RhsOp) (rhs : List Expr) (vals : List GoValue) (body : Stmt)
    (env : LocalEnv) (k' : Cont) (ch : Choices) (_hc : completeTargetRef sh (v :: ops).reverse = some r),
    stepFn ctx s (.retV v (.tgtOpK sh ops [] refs ((sh', e :: ops') :: rest) rop rhs vals body env k')) ch
      = .ok (.evalE e env (.tgtOpK sh' [] ops' (refs ++ [r]) rest rop rhs vals body env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_tgtOpK_next_target

-- 301. `Equations.lean` — `retV_tgtOpK_rhs`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {sh : TargetShape} {ops : List GoValue} {r : TargetRef}
    (refs : List TargetRef) (rop : RhsOp) (e : Expr) (rest : List Expr) (vals : List GoValue) (body : Stmt)
    (env : LocalEnv) (k' : Cont) (ch : Choices) (_hc : completeTargetRef sh (v :: ops).reverse = some r),
    stepFn ctx s (.retV v (.tgtOpK sh ops [] refs [] rop (e :: rest) vals body env k')) ch
      = .ok (.evalE e env (.rhsK rop (refs ++ [r]) [] rest body env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_tgtOpK_rhs

-- 302. `Equations.lean` — `retV_tgtOpK_store`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {sh : TargetShape} {ops : List GoValue} {r : TargetRef}
    (refs : List TargetRef) (rop : RhsOp) (vals : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_hc : completeTargetRef sh (v :: ops).reverse = some r),
    stepFn ctx s (.retV v (.tgtOpK sh ops [] refs [] rop [] vals body env k')) ch
      = .ok (.next (.storeK (refs ++ [r]) vals body env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_tgtOpK_store

-- 303. `Equations.lean` — `retV_tgtOpK_malformed`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {sh : TargetShape} {ops : List GoValue}
    (refs : List TargetRef) (targets : List (TargetShape × List Expr)) (rop : RhsOp) (rhs : List Expr)
    (vals : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_hc : completeTargetRef sh (v :: ops).reverse = none),
    stepFn ctx s (.retV v (.tgtOpK sh ops [] refs targets rop rhs vals body env k')) ch
      = .error (.internal "malformed receive target operands") :=
  @GoLean.GoCore.Equations.retV_tgtOpK_malformed

-- 304. `Equations.lean` — `retV_rhsK_more`
example : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (rop : RhsOp) (refs : List TargetRef)
    (done : List GoValue) (e : Expr) (rest : List Expr) (body : Stmt) (env : LocalEnv) (k' : Cont)
    (ch : Choices),
    stepFn ctx s (.retV v (.rhsK rop refs done (e :: rest) body env k')) ch
      = .ok (.evalE e env (.rhsK rop refs (v :: done) rest body env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_rhsK_more

-- 305. `Equations.lean` — `retV_rhsK_apply`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {rop : RhsOp} {done vals : List GoValue}
    {tr : AccessTrace} (refs : List TargetRef) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyRhsOp ctx s rop (v :: done).reverse = .ok (vals, tr)),
    stepFn ctx s (.retV v (.rhsK rop refs done [] body env k')) ch
      = .ok (.next (.storeK refs vals body env k'), s, ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.retV_rhsK_apply

-- 306. `Equations.lean` — `retV_rhsK_apply_panic`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {rop : RhsOp} {done : List GoValue} {msg : String}
    (refs : List TargetRef) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyRhsOp ctx s rop (v :: done).reverse = .error (.panic msg)),
    stepFn ctx s (.retV v (.rhsK rop refs done [] body env k')) ch
      = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_rhsK_apply_panic

-- 307. `Equations.lean` — `next_storeK_store`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {ref : TargetRef} {val : GoValue} {tr : AccessTrace}
    (rs : List TargetRef) (vrest : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : storeTarget ctx s ref val = .ok (s', tr)),
    stepFn ctx s (.next (.storeK (ref :: rs) (val :: vrest) body env k')) ch
      = .ok (.next (.storeK rs vrest body env k'), s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.next_storeK_store

-- 308. `Equations.lean` — `next_storeK_chain`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {anchor : GoValue} {idxs : List GoValue} {steps : List TargetStep}
    {val av : GoValue} {loc : Loc} (rs : List TargetRef) (vrest : List GoValue) (body : Stmt) (env : LocalEnv)
    (k' : Cont) (ch : Choices) (_hres : resolveChain ctx s anchor steps idxs = .ok av)
    (_hloc : valueAsLoc av = .ok loc) (_hst : storeLoc ctx s loc val = .ok s'),
    stepFn ctx s (.next (.storeK (.chain anchor idxs steps :: rs) (val :: vrest) body env k')) ch
      = .ok (.next (.storeK rs vrest body env k'), s', ch, ⟨[.access .write (.data loc.canon)], [], []⟩) :=
  @GoLean.GoCore.Equations.next_storeK_chain

-- 309. `Equations.lean` — `next_storeK_var`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {loc : Loc} {val : GoValue} (rs : List TargetRef)
    (vrest : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_hst : storeLoc ctx s loc val = .ok s'),
    stepFn ctx s (.next (.storeK (.chain (.addr loc) [] [] :: rs) (val :: vrest) body env k')) ch
      = .ok (.next (.storeK rs vrest body env k'), s', ch, ⟨[.access .write (.data loc.canon)], [], []⟩) :=
  @GoLean.GoCore.Equations.next_storeK_var

-- 310. `Equations.lean` — `next_storeK_panic`
example : ∀ {ctx : ProgramCtx} {s : Store} {ref : TargetRef} {val : GoValue} {msg : String}
    (rs : List TargetRef) (vrest : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : storeTarget ctx s ref val = .error (.panic msg)),
    stepFn ctx s (.next (.storeK (ref :: rs) (val :: vrest) body env k')) ch
      = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_storeK_panic

-- 311. `Equations.lean` — `next_storeK_done`
example : ∀ {ctx : ProgramCtx} (s : Store) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.storeK [] [] body env k')) ch = .ok (.exec body env k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_storeK_done

-- 312. `Equations.lean` — `exec_block`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {decls : Array Param} {env env' : LocalEnv} (ss : Array Stmt)
    (k : Cont) (ch : Choices) (_h : allocDecls ctx env.pushScope s decls.toList = .ok (env', s')),
    stepFn ctx s (.exec (.block decls ss) env k) ch = .ok (.next (.seq ss.toList env' k), s', ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_block

-- 313. `Equations.lean` — `allocDecls_nil`
example : ∀ {ctx : ProgramCtx} (env : LocalEnv) (s : Store),
    allocDecls ctx env s [] = .ok (env, s) :=
  @GoLean.GoCore.Equations.allocDecls_nil

-- 314. `Equations.lean` — `allocDecls_cons`
example : ∀ {ctx : ProgramCtx} {env : LocalEnv} {s s₁ : Store} {p : Param} {v : GoValue} {loc : Loc}
    (rest : List Param) (_hd : defaultValue ctx p.typ = .ok v) (_ha : Store.alloc ctx s v p.typ = .ok (loc, s₁)),
    allocDecls ctx env s (p :: rest) = allocDecls ctx (env.declare p.id loc) s₁ rest :=
  @GoLean.GoCore.Equations.allocDecls_cons

-- 315. `Equations.lean` — `bindParams_nil`
example : ∀ {ctx : ProgramCtx} (env : LocalEnv) (s : Store),
    bindParams ctx env s [] [] = .ok (env, s) :=
  @GoLean.GoCore.Equations.bindParams_nil

-- 316. `Equations.lean` — `bindParams_cons`
example : ∀ {ctx : ProgramCtx} {env : LocalEnv} {s s₁ : Store} {p : Param} {v v' : GoValue} {loc : Loc}
    (ps : List Param) (vs : List GoValue) (_hn : normalizeValueForTy ctx p.typ v = .ok v')
    (_ha : Store.alloc ctx s v' p.typ = .ok (loc, s₁)),
    bindParams ctx env s (p :: ps) (v :: vs) = bindParams ctx (env.declare p.id loc) s₁ ps vs :=
  @GoLean.GoCore.Equations.bindParams_cons

-- 317. `Equations.lean` — `retV_ifK_true`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (t e : Stmt) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_hv : valueAsBool v = .ok true),
    stepFn ctx s (.retV v (.ifK t e env k')) ch = .ok (.exec t env k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_ifK_true

-- 318. `Equations.lean` — `retV_ifK_false`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (t e : Stmt) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_hv : valueAsBool v = .ok false),
    stepFn ctx s (.retV v (.ifK t e env k')) ch = .ok (.exec e env k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_ifK_false

-- 319. `Equations.lean` — `retV_whileK_true`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (c : Expr) (b : Stmt) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_hv : valueAsBool v = .ok true),
    stepFn ctx s (.retV v (.whileK c b env k')) ch = .ok (.exec b env (.loop c b env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_whileK_true

-- 320. `Equations.lean` — `retV_whileK_false`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (c : Expr) (b : Stmt) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_hv : valueAsBool v = .ok false),
    stepFn ctx s (.retV v (.whileK c b env k')) ch = .ok (.next k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_whileK_false

-- 321. `Equations.lean` — `evalE_and`
example : ∀ {ctx : ProgramCtx} (s : Store) (l r : Expr) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.evalE (.and l r) env k) ch = .ok (.evalE l env (.andK r env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_and

-- 322. `Equations.lean` — `evalE_or`
example : ∀ {ctx : ProgramCtx} (s : Store) (l r : Expr) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.evalE (.or l r) env k) ch = .ok (.evalE l env (.orK r env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_or

-- 323. `Equations.lean` — `retV_andK_true`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (r : Expr) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_hv : valueAsBool v = .ok true),
    stepFn ctx s (.retV v (.andK r env k')) ch = .ok (.evalE r env (.boolK k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_andK_true

-- 324. `Equations.lean` — `retV_andK_false`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (r : Expr) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_hv : valueAsBool v = .ok false),
    stepFn ctx s (.retV v (.andK r env k')) ch = .ok (.retV (.bool false) k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_andK_false

-- 325. `Equations.lean` — `retV_orK_true`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (r : Expr) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_hv : valueAsBool v = .ok true),
    stepFn ctx s (.retV v (.orK r env k')) ch = .ok (.retV (.bool true) k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_orK_true

-- 326. `Equations.lean` — `retV_orK_false`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (r : Expr) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_hv : valueAsBool v = .ok false),
    stepFn ctx s (.retV v (.orK r env k')) ch = .ok (.evalE r env (.boolK k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_orK_false

-- 327. `Equations.lean` — `retV_boolK`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {b : Bool} (k' : Cont) (ch : Choices)
    (_hv : valueAsBool v = .ok b),
    stepFn ctx s (.retV v (.boolK k')) ch = .ok (.retV (.bool b) k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_boolK

-- 328. `Equations.lean` — `evalE_intLit`
example : ∀ {ctx : ProgramCtx} (s : Store) (value : Int) (kind : IntKind) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.evalE (.intLit value kind) env k) ch = .ok (.retV (.int (kind.normalize value) kind) k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_intLit

-- 329. `Equations.lean` — `evalE_boolLit`
example : ∀ {ctx : ProgramCtx} (s : Store) (value : Bool) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.evalE (.boolLit value) env k) ch = .ok (.retV (.bool value) k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_boolLit

-- 330. `Equations.lean` — `evalE_stringLit`
example : ∀ {ctx : ProgramCtx} (s : Store) (value : GoString) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.evalE (.stringLit value) env k) ch = .ok (.retV (.string value) k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_stringLit

-- 331. `Equations.lean` — `evalE_unsupported`
example : ∀ {ctx : ProgramCtx} (s : Store) (feature : String) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.evalE (.unsupported feature) env k) ch = .error (.unsupported feature) :=
  @GoLean.GoCore.Equations.evalE_unsupported

-- 332. `Equations.lean` — `evalE_strict_more`
example : ∀ {ctx : ProgramCtx} {s : Store} {e e₁ : Expr} {op : StrictOp} {rest : List Expr} (env : LocalEnv)
    (k : Cont) (ch : Choices) (_h : strictPlan e = some (op, e₁ :: rest)),
    stepFn ctx s (.evalE e env k) ch = .ok (.evalE e₁ env (.strictK op [] rest env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_strict_more

-- 333. `Equations.lean` — `evalE_strict_nullary`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {e : Expr} {op : StrictOp} {v : GoValue} {tr : AccessTrace}
    (env : LocalEnv) (k : Cont) (ch : Choices) (_h : strictPlan e = some (op, []))
    (_ha : applyStrictOp ctx s (projChainTarget ctx s k) op [] = .ok (v, s', tr)),
    stepFn ctx s (.evalE e env k) ch = .ok (.retV v k, s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_strict_nullary

-- 334. `Equations.lean` — `retV_strictK_more`
example : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (op : StrictOp) (done : List GoValue) (e : Expr)
    (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.strictK op done (e :: rest) env k')) ch
      = .ok (.evalE e env (.strictK op (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_strictK_more

-- 335. `Equations.lean` — `retV_strictK_apply`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {v out : GoValue} {op : StrictOp} {done : List GoValue}
    {tr : AccessTrace} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_ha : applyStrictOp ctx s (projChainTarget ctx s k') op (v :: done).reverse = .ok (out, s', tr)),
    stepFn ctx s (.retV v (.strictK op done [] env k')) ch = .ok (.retV out k', s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.retV_strictK_apply

-- 336. `Equations.lean` — `retV_strictK_apply_panic`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : StrictOp} {done : List GoValue} {msg : String}
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_ha : applyStrictOp ctx s (projChainTarget ctx s k') op (v :: done).reverse = .error (.panic msg)),
    stepFn ctx s (.retV v (.strictK op done [] env k')) ch = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_strictK_apply_panic

-- 337. `Equations.lean` — `retV_strictK_apply_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : StrictOp} {done : List GoValue} {e : Stop}
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_ha : applyStrictOp ctx s (projChainTarget ctx s k') op (v :: done).reverse = .error e)
    (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV v (.strictK op done [] env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_strictK_apply_error

-- 338. `Equations.lean` — `exec_wide`
example : ∀ {ctx : ProgramCtx} {s : Store} {stmt : Stmt} {op : StmtOp} {nt : Nat} {e : Expr} {rest : List Expr}
    (env : LocalEnv) (k : Cont) (ch : Choices) (_h : stmtPlan stmt = some (op, nt, e :: rest)),
    stepFn ctx s (.exec stmt env k) ch = .ok (.evalE e env (.stmtOpK op nt [] rest env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_wide

-- 339. `Equations.lean` — `exec_allocNew`
example : ∀ {ctx : ProgramCtx} {s : Store} {target : Assignee} {te : Expr} (value : Expr) (typ : Ty)
    (env : LocalEnv) (k : Cont) (ch : Choices) (_ht : assigneeExpr target = some te),
    stepFn ctx s (.exec (.allocNew target value typ) env k) ch
      = .ok (.evalE te env (.stmtOpK (.allocNew typ) 1 [] [value] env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_allocNew

-- 340. `Equations.lean` — `exec_mapAssign`
example : ∀ {ctx : ProgramCtx} (s : Store) (base index value : Expr) (keyTy valueTy : Ty) (env : LocalEnv)
    (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.mapAssign base index value keyTy valueTy) env k) ch
      = .ok (.evalE base env (.stmtOpK (.mapAssign keyTy valueTy) 0 [] [index, value] env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_mapAssign

-- 341. `Equations.lean` — `exec_appendSlice`
example : ∀ {ctx : ProgramCtx} {s : Store} {target : Assignee} {te : Expr} (elem : Ty) (slice elems : Expr)
    (env : LocalEnv) (k : Cont) (ch : Choices) (_ht : assigneeExpr target = some te),
    stepFn ctx s (.exec (.appendSlice target elem slice elems) env k) ch
      = .ok (.evalE te env (.stmtOpK (.appendSlice elem) 1 [] [slice, elems] env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_appendSlice

-- 342. `Equations.lean` — `exec_print`
example : ∀ {ctx : ProgramCtx} {s : Store} {args : Array Expr} {e : Expr} {rest : List Expr} (newline : Bool)
    (env : LocalEnv) (k : Cont) (ch : Choices) (_hargs : args.toList = e :: rest),
    stepFn ctx s (.exec (.print newline args) env k) ch
      = .ok (.evalE e env (.stmtOpK (.print newline) 0 [] rest env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_print

-- 343. `Equations.lean` — `retV_stmtOpK_more_target`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {loc : Loc} {nt : Nat} {done : List GoValue}
    (op : StmtOp) (e : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_hlt : done.length < nt) (_hloc : valueAsLoc v = .ok loc),
    stepFn ctx s (.retV v (.stmtOpK op nt done (e :: rest) env k')) ch
      = .ok (.evalE e env (.stmtOpK op nt (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_stmtOpK_more_target

-- 344. `Equations.lean` — `retV_stmtOpK_more_target_nil`
example : ∀ {ctx : ProgramCtx} {s : Store} {nt : Nat} {done : List GoValue} (op : StmtOp) (e : Expr)
    (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices) (_hlt : done.length < nt),
    stepFn ctx s (.retV .nil (.stmtOpK op nt done (e :: rest) env k')) ch
      = .ok (.panicking [panicEntry nilDerefPanicText] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_stmtOpK_more_target_nil

-- 345. `Equations.lean` — `retV_stmtOpK_more_operand`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {nt : Nat} {done : List GoValue} (op : StmtOp)
    (e : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices) (_hge : ¬ done.length < nt),
    stepFn ctx s (.retV v (.stmtOpK op nt done (e :: rest) env k')) ch
      = .ok (.evalE e env (.stmtOpK op nt (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_stmtOpK_more_operand

-- 346. `Equations.lean` — `retV_stmtOpK_apply`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {v : GoValue} {op : StmtOp} {nt : Nat} {done : List GoValue}
    {ch' : Choices} {ps : List PickRecord} {tr : AccessTrace} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyStmtOp ctx s ch op nt (v :: done).reverse = .ok (s', ch', ps, tr)),
    stepFn ctx s (.retV v (.stmtOpK op nt done [] env k')) ch
      = .ok (.next k', s', ch', ⟨tr, ps, stmtOpOut op (v :: done).reverse⟩) :=
  @GoLean.GoCore.Equations.retV_stmtOpK_apply

-- 347. `Equations.lean` — `retV_stmtOpK_apply_panic`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : StmtOp} {nt : Nat} {done : List GoValue}
    {msg : String} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyStmtOp ctx s ch op nt (v :: done).reverse = .error (.panic msg)),
    stepFn ctx s (.retV v (.stmtOpK op nt done [] env k')) ch = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_stmtOpK_apply_panic

-- 348. `Equations.lean` — `exec_mapRange`
example : ∀ {ctx : ProgramCtx} (s : Store) (keyVar valVar : Option VarId) (mapExpr : Expr) (keyTy valTy : Ty)
    (body : Stmt) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.mapRange keyVar valVar mapExpr keyTy valTy body) env k) ch
      = .ok (.evalE mapExpr env (.mapRangeK keyVar valVar keyTy valTy body env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_mapRange

-- 349. `Equations.lean` — `retV_mapRangeK`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {base : Option Loc} {start : Array Nat}
    {tr : AccessTrace} (keyVar valVar : Option VarId) (keyTy valTy : Ty) (body : Stmt) (env : LocalEnv)
    (k' : Cont) (ch : Choices) (_h : mapRangeStartSets s v = .ok (base, start, tr)),
    stepFn ctx s (.retV v (.mapRangeK keyVar valVar keyTy valTy body env k')) ch
      = .ok (.next (.mapIterK keyVar valVar keyTy valTy body base #[] start env k'), s, ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.retV_mapRangeK

-- 350. `Equations.lean` — `next_mapIterK_done`
example : ∀ {ctx : ProgramCtx} {s : Store} {keyTy valTy : Ty} {base : Option Loc} {produced : Array Nat}
    {tr : AccessTrace} (keyVar valVar : Option VarId) (body : Stmt) (start : Array Nat) (env : LocalEnv)
    (k' : Cont) (ch : Choices) (_h : mapIterCandidates ctx s keyTy valTy base produced = .ok (#[], tr)),
    stepFn ctx s (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k')) ch
      = .ok (.next k', s, ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.next_mapIterK_done

-- 351. `Equations.lean` — `next_mapIterK_pick`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {keyTy valTy : Ty} {base : Option Loc}
    {produced start : Array Nat} {cands : Array (Nat × GoValue × GoValue)} {tr : AccessTrace} {width idx : Nat}
    {ch' : Choices} {ps : List PickRecord} {id : Nat} {key value : GoValue} {env env' : LocalEnv}
    (keyVar valVar : Option VarId) (body : Stmt) (k' : Cont) (ch : Choices)
    (_h : mapIterCandidates ctx s keyTy valTy base produced = .ok (cands, tr)) (_hne : cands.isEmpty = false)
    (_hw : width = cands.size + (if mapIterMandatoryRemains cands start then 0 else 1))
    (_hc : Choices.consumeAtE .mapIter width ch = (idx, ch', ps)) (_hget : cands[idx]? = some (id, key, value))
    (_hb : bindIterVars ctx env.pushScope s keyVar valVar keyTy valTy key value = .ok (env', s')),
    stepFn ctx s (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k')) ch
      = .ok (.exec body env' (.mapIterK keyVar valVar keyTy valTy body base (produced.push id) start env k'), s', ch',
            ⟨tr, ps, []⟩) :=
  @GoLean.GoCore.Equations.next_mapIterK_pick

-- 352. `Equations.lean` — `next_mapIterK_stop`
example : ∀ {ctx : ProgramCtx} {s : Store} {keyTy valTy : Ty} {base : Option Loc} {produced start : Array Nat}
    {cands : Array (Nat × GoValue × GoValue)} {tr : AccessTrace} {width idx : Nat} {ch' : Choices}
    {ps : List PickRecord} (keyVar valVar : Option VarId) (body : Stmt) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_h : mapIterCandidates ctx s keyTy valTy base produced = .ok (cands, tr))
    (_hne : cands.isEmpty = false)
    (_hw : width = cands.size + (if mapIterMandatoryRemains cands start then 0 else 1))
    (_hc : Choices.consumeAtE .mapIter width ch = (idx, ch', ps)) (_hget : cands[idx]? = none),
    stepFn ctx s (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k')) ch
      = .ok (.next k', s, ch', ⟨tr, ps, []⟩) :=
  @GoLean.GoCore.Equations.next_mapIterK_stop

-- 353. `Equations.lean` — `exec_mapLookup`
example : ∀ {ctx : ProgramCtx} {s : Store} {t okT : Assignee} {sh : TargetShape} {e : Expr} {ops : List Expr}
    {rest : List (TargetShape × List Expr)} (base index : Expr) (keyTy valueTy : Ty) (env : LocalEnv) (k : Cont)
    (ch : Choices) (_h : targetsPlan [t, okT] = some ((sh, e :: ops) :: rest)),
    stepFn ctx s (.exec (.mapLookup t okT base index keyTy valueTy) env k) ch
      = .ok (.evalE e env (.tgtOpK sh [] ops [] rest (.mapLookup keyTy valueTy) [base, index] [] (.seqn #[]) env k), s, ch,
            ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_mapLookup

-- 354. `Equations.lean` — `exec_typeAssert`
example : ∀ {ctx : ProgramCtx} {s : Store} {t okT : Assignee} {sh : TargetShape} {e : Expr} {ops : List Expr}
    {rest : List (TargetShape × List Expr)} (expr : Expr) (targetTy : Ty) (env : LocalEnv) (k : Cont)
    (ch : Choices) (_h : targetsPlan [t, okT] = some ((sh, e :: ops) :: rest)),
    stepFn ctx s (.exec (.typeAssert t okT expr targetTy) env k) ch
      = .ok (.evalE e env (.tgtOpK sh [] ops [] rest (.typeAssert targetTy) [expr] [] (.seqn #[]) env k), s, ch,
            ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_typeAssert

-- 355. `Equations.lean` — `exec_assignMany`
example : ∀ {ctx : ProgramCtx} {s : Store} {left : Array Assignee} {right : Array Expr} {sh : TargetShape}
    {e : Expr} {ops : List Expr} {rest : List (TargetShape × List Expr)} (env : LocalEnv) (k : Cont)
    (ch : Choices) (_hsz : left.size = right.size)
    (_h : targetsPlan left.toList = some ((sh, e :: ops) :: rest)),
    stepFn ctx s (.exec (.assignMany left right) env k) ch
      = .ok (.evalE e env (.tgtOpK sh [] ops [] rest .vals right.toList [] (.seqn #[]) env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_assignMany

-- 356. `Equations.lean` — `exec_assignMany_arity`
example : ∀ {ctx : ProgramCtx} {s : Store} {left : Array Assignee} {right : Array Expr} (env : LocalEnv)
    (k : Cont) (ch : Choices) (_hsz : left.size ≠ right.size),
    stepFn ctx s (.exec (.assignMany left right) env k) ch
      = .error (.stuck s!"multi-assignment expected {left.size} value(s), got {right.size}") :=
  @GoLean.GoCore.Equations.exec_assignMany_arity

-- 357. `Equations.lean` — `exec_chanSend`
example : ∀ {ctx : ProgramCtx} (s : Store) (chE value : Expr) (elem : Ty) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.exec (.chanSend chE value elem) env k) ch
      = .ok (.evalE chE env (.chanStK (.send elem) [] [value] env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_chanSend

-- 358. `Equations.lean` — `exec_closeChan`
example : ∀ {ctx : ProgramCtx} (s : Store) (chE : Expr) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.closeChan chE) env k) ch = .ok (.evalE chE env (.chanStK .close [] [] env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_closeChan

-- 359. `Equations.lean` — `exec_chanRecv`
example : ∀ {ctx : ProgramCtx} {s : Store} {targets : Array Assignee} {plans : List (TargetShape × List Expr)}
    (chE : Expr) (elem : Ty) (env : LocalEnv) (k : Cont) (ch : Choices) (_hsz : ¬ targets.size > 2)
    (_hp : targetsPlan targets.toList = some plans),
    stepFn ctx s (.exec (.chanRecv targets chE elem) env k) ch
      = .ok (.evalE chE env (.chanStK (.recv targets.toList elem) [] [] env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_chanRecv

-- 360. `Equations.lean` — `retV_chanStK_more`
example : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (op : ChanStOp) (done : List GoValue) (e : Expr)
    (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.chanStK op done (e :: rest) env k')) ch
      = .ok (.evalE e env (.chanStK op (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_chanStK_more

-- 361. `Equations.lean` — `retV_chanStK_apply`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {v : GoValue} {op : ChanStOp} {done : List GoValue} {c' : Config}
    {tr : AccessTrace} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyChanOp ctx s op (v :: done).reverse env k' = .ok (c', s', tr)),
    stepFn ctx s (.retV v (.chanStK op done [] env k')) ch = .ok (c', s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.retV_chanStK_apply

-- 362. `Equations.lean` — `retV_chanStK_apply_panic`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : ChanStOp} {done : List GoValue} {msg : String}
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyChanOp ctx s op (v :: done).reverse env k' = .error (.panic msg)),
    stepFn ctx s (.retV v (.chanStK op done [] env k')) ch = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_chanStK_apply_panic

-- 363. `Equations.lean` — `exec_selectStmt`
example : ∀ {ctx : ProgramCtx} {s : Store} {clauses : Array (SelectClauseHead × Stmt)} {e : Expr}
    {rest : List Expr} (default? : Option Stmt) (env : LocalEnv) (k : Cont) (ch : Choices)
    (_h : selectOperands clauses.toList = e :: rest),
    stepFn ctx s (.exec (.selectStmt clauses default?) env k) ch
      = .ok (.evalE e env (.selectOpsK clauses.toList default? [] rest env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_selectStmt

-- 364. `Equations.lean` — `exec_selectStmt_default`
example : ∀ {ctx : ProgramCtx} {s : Store} {clauses : Array (SelectClauseHead × Stmt)} (d : Stmt)
    (env : LocalEnv) (k : Cont) (ch : Choices) (_h : selectOperands clauses.toList = []),
    stepFn ctx s (.exec (.selectStmt clauses (some d)) env k) ch = .ok (.exec d env k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_selectStmt_default

-- 365. `Equations.lean` — `exec_selectStmt_block`
example : ∀ {ctx : ProgramCtx} {s : Store} {clauses : Array (SelectClauseHead × Stmt)} (env : LocalEnv)
    (k : Cont) (ch : Choices) (_h : selectOperands clauses.toList = []),
    stepFn ctx s (.exec (.selectStmt clauses none) env k) ch = .ok (.blockedSelect [] env k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_selectStmt_block

-- 366. `Equations.lean` — `retV_selectOpsK_more`
example : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (clauses : List (SelectClauseHead × Stmt))
    (default? : Option Stmt) (done : List GoValue) (e : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont)
    (ch : Choices),
    stepFn ctx s (.retV v (.selectOpsK clauses default? done (e :: rest) env k')) ch
      = .ok (.evalE e env (.selectOpsK clauses default? (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_selectOpsK_more

-- 367. `Equations.lean` — `retV_selectOpsK_apply`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {v : GoValue} {clauses : List (SelectClauseHead × Stmt)}
    {default? : Option Stmt} {done : List GoValue} {c' : Config} {ch' : Choices} {ps : List PickRecord}
    {cl? : Option EvClause} {tr : AccessTrace} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applySelect ctx s clauses default? (v :: done).reverse env k' ch = .ok (c', s', ch', ps, cl?, tr)),
    stepFn ctx s (.retV v (.selectOpsK clauses default? done [] env k')) ch = .ok (c', s', ch', ⟨tr, ps, []⟩) :=
  @GoLean.GoCore.Equations.retV_selectOpsK_apply

-- 368. `Equations.lean` — `exec_goStmt`
example : ∀ {ctx : ProgramCtx} (s : Store) (callee : Expr) (args : Array Expr) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.exec (.goStmt callee args) env k) ch
      = .ok (.evalE callee env (.goCalleeK args.toList env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_goStmt

-- 369. `Equations.lean` — `retV_goCalleeK_args`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (a : Expr) (rest : List Expr) (env : LocalEnv)
    (k' : Cont) (ch : Choices) (_hd : deferrableCallee v = true),
    stepFn ctx s (.retV v (.goCalleeK (a :: rest) env k')) ch
      = .ok (.evalE a env (.goArgsK v [] rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_goCalleeK_args

-- 370. `Equations.lean` — `retV_goCalleeK_spawn`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_hd : deferrableCallee v = true),
    stepFn ctx s (.retV v (.goCalleeK [] env k')) ch
      = .error (.unsupported
          "go spawn outside the thread pool (goroutine spawn is a pool step; go during package init is refused this slice)") :=
  @GoLean.GoCore.Equations.retV_goCalleeK_spawn

-- 371. `Equations.lean` — `retV_goArgsK_more`
example : ∀ {ctx : ProgramCtx} (s : Store) (v cv : GoValue) (vals : List GoValue) (a : Expr) (rest : List Expr)
    (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.goArgsK cv vals (a :: rest) env k')) ch
      = .ok (.evalE a env (.goArgsK cv (vals ++ [v]) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_goArgsK_more

-- 372. `Equations.lean` — `retV_goArgsK_spawn`
example : ∀ {ctx : ProgramCtx} (s : Store) (v cv : GoValue) (vals : List GoValue) (env : LocalEnv) (k' : Cont)
    (ch : Choices),
    stepFn ctx s (.retV v (.goArgsK cv vals [] env k')) ch
      = .error (.unsupported
          "go spawn outside the thread pool (goroutine spawn is a pool step; go during package init is refused this slice)") :=
  @GoLean.GoCore.Equations.retV_goArgsK_spawn

-- 373. `Equations.lean` — `exec_syncStmt`
example : ∀ {ctx : ProgramCtx} {s : Store} {op : SyncStmtOp} {args : Array Expr} {targets : Array Assignee}
    {sop : SyncOp} {e : Expr} {rest : List Expr} (env : LocalEnv) (k : Cont) (ch : Choices)
    (_h : syncPlan (.syncStmt op args targets) = some (sop, e :: rest)),
    stepFn ctx s (.exec (.syncStmt op args targets) env k) ch
      = .ok (.evalE e env (.syncStK sop [] rest env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_syncStmt

-- 374. `Equations.lean` — `exec_atomicStmt`
example : ∀ {ctx : ProgramCtx} {s : Store} {op : AtomicStmtOp} {kind : IntKind} {args : Array Expr}
    {targets : Array Assignee} {aop : AtomicOp} {e : Expr} {rest : List Expr} (env : LocalEnv) (k : Cont)
    (ch : Choices) (_h : atomicPlan (.atomicStmt op kind args targets) = some (aop, e :: rest)),
    stepFn ctx s (.exec (.atomicStmt op kind args targets) env k) ch
      = .ok (.evalE e env (.atomicStK aop [] rest env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_atomicStmt

-- 375. `Equations.lean` — `retV_syncStK_more`
example : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (op : SyncOp) (done : List GoValue) (e : Expr)
    (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.syncStK op done (e :: rest) env k')) ch
      = .ok (.evalE e env (.syncStK op (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_syncStK_more

-- 376. `Equations.lean` — `retV_syncStK_apply`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {v : GoValue} {op : SyncOp} {done : List GoValue} {c' : Config}
    {ch' : Choices} {ps : List PickRecord} {tr : AccessTrace} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applySyncOp ctx s ch op (v :: done).reverse env k' = .ok (c', s', ch', ps, tr)),
    stepFn ctx s (.retV v (.syncStK op done [] env k')) ch = .ok (c', s', ch', ⟨tr, ps, []⟩) :=
  @GoLean.GoCore.Equations.retV_syncStK_apply

-- 377. `Equations.lean` — `retV_syncStK_apply_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : SyncOp} {done : List GoValue} {e : Stop}
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applySyncOp ctx s ch op (v :: done).reverse env k' = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV v (.syncStK op done [] env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_syncStK_apply_error

-- 378. `Equations.lean` — `retV_atomicStK_more`
example : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (op : AtomicOp) (done : List GoValue) (e : Expr)
    (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.atomicStK op done (e :: rest) env k')) ch
      = .ok (.evalE e env (.atomicStK op (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_atomicStK_more

-- 379. `Equations.lean` — `retV_atomicStK_apply`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {v : GoValue} {op : AtomicOp} {done : List GoValue} {c' : Config}
    {tr : AccessTrace} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyAtomicOp ctx s op (v :: done).reverse env k' = .ok (c', s', tr)),
    stepFn ctx s (.retV v (.atomicStK op done [] env k')) ch = .ok (c', s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.retV_atomicStK_apply

-- 380. `Equations.lean` — `retV_atomicStK_apply_panic`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : AtomicOp} {done : List GoValue} {msg : String}
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyAtomicOp ctx s op (v :: done).reverse env k' = .error (.panic msg)),
    stepFn ctx s (.retV v (.atomicStK op done [] env k')) ch = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_atomicStK_apply_panic

-- 381. `Equations.lean` — `blockedSend`
example : ∀ {ctx : ProgramCtx} (s : Store) (chl : Option Loc) (v : GoValue) (k : Cont) (ch : Choices),
    stepFn ctx s (.blockedSend chl v k) ch = .error .deadlock :=
  @GoLean.GoCore.Equations.blockedSend

-- 382. `Equations.lean` — `blockedRecv`
example : ∀ {ctx : ProgramCtx} (s : Store) (chl : Option Loc) (targets : List Assignee) (elem : Ty)
    (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.blockedRecv chl targets elem env k) ch = .error .deadlock :=
  @GoLean.GoCore.Equations.blockedRecv

-- 383. `Equations.lean` — `blockedSelect`
example : ∀ {ctx : ProgramCtx} (s : Store) (clauses : List EvClause) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.blockedSelect clauses env k) ch = .error .deadlock :=
  @GoLean.GoCore.Equations.blockedSelect

-- 384. `Equations.lean` — `blockedSync`
example : ∀ {ctx : ProgramCtx} (s : Store) (op : SyncOp) (loc : Loc) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.blockedSync op loc env k) ch = .error .deadlock :=
  @GoLean.GoCore.Equations.blockedSync

-- 385. `Equations.lean` — `exec_unseqProbe`
example : ∀ {ctx : ProgramCtx} (s : Store) (e : Expr) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.unseqProbe e) env k) ch = .ok (.evalE e env (.probeK k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_unseqProbe

-- 386. `Equations.lean` — `retV_probeK`
example : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.probeK k')) ch = .ok (.next k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_probeK

-- 387. `Equations.lean` — `exec_unseq`
example : ∀ {ctx : ProgramCtx} (s : Store) (g : UnseqGraph) (thenB : Stmt) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.exec (.unseq g thenB) env k) ch = stepUnseqEnter ctx s g thenB env k ch :=
  @GoLean.GoCore.Equations.exec_unseq

-- 388. `Equations.lean` — `next_unseqK`
example : ∀ {ctx : ProgramCtx} (s : Store) (g : UnseqGraph) (thenB : Stmt) (st : List UnseqStatus)
    (tg : List (VarId × TargetRef)) (env : LocalEnv) (ph : UnseqPhase) (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.unseqK g thenB st tg env ph k')) ch = stepUnseqNext ctx s g thenB st tg env ph k' ch :=
  @GoLean.GoCore.Equations.next_unseqK

-- 389. `Equations.lean` — `retV_unseqK`
example : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (g : UnseqGraph) (thenB : Stmt) (st : List UnseqStatus)
    (tg : List (VarId × TargetRef)) (env : LocalEnv) (ph : UnseqPhase) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.unseqK g thenB st tg env ph k')) ch = stepUnseqValue ctx s v g thenB st tg env ph k' ch :=
  @GoLean.GoCore.Equations.retV_unseqK

-- 390. `Equations.lean` — `unseqEnter`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {g : UnseqGraph} {env env' : LocalEnv} (thenB : Stmt)
    (rest : List Stmt) (k' : Cont) (ch : Choices) (_hwf : g.wellFormed? = none)
    (_hen : unseqEntryCheck? g env = none) (_ha : allocDecls ctx env.pushScope s g.cells = .ok (env', s')),
    stepFn ctx s (.exec (.unseq g thenB) env (.seq rest env k')) ch
      = .ok (.next (.unseqK g thenB g.initStatus [] env' .pick (.seq rest env k')), s', ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.unseqEnter

-- 391. `Equations.lean` — `unseqValue`
example : ∀ {ctx : ProgramCtx} {s s' : Store} {v : GoValue} {g : UnseqGraph} {i : Nat} {o : UnseqOcc}
    {bind : VarId} {head : Expr} {loc : Loc} (thenB : Stmt) (st : List UnseqStatus)
    (tg : List (VarId × TargetRef)) (env : LocalEnv) (k' : Cont) (ch : Choices) (_hget : g.occs[i]? = some o)
    (_hbody : o.body = .eval bind head) (_hloc : unseqCellLoc env bind = .ok loc)
    (_hst : storeLoc ctx s loc v = .ok s'),
    stepFn ctx s (.retV v (.unseqK g thenB st tg env (.wait i) k')) ch
      = .ok (.next (.unseqK g thenB (st.set i .done) tg env .pick k'), s', ch, ⟨[.access .write (.data loc.canon)], [], []⟩) :=
  @GoLean.GoCore.Equations.unseqValue

-- 392. `Equations.lean` — `unseqRun_eval`
example : ∀ {ctx : ProgramCtx} {s : Store} {g : UnseqGraph} {i : Nat} {o : UnseqOcc} {bind : VarId}
    {head : Expr} (thenB : Stmt) (st : List UnseqStatus) (tg : List (VarId × TargetRef)) (env : LocalEnv)
    (k' : Cont) (ch : Choices) (_hget : g.occs[i]? = some o) (_hbody : o.body = .eval bind head),
    stepFn ctx s (.next (.unseqK g thenB st tg env (.run i) k')) ch
      = .ok (.evalE head env (.unseqK g thenB st tg env (.wait i) k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.unseqRun_eval

-- 393. `Equations.lean` — `unseqWait_invoke`
example : ∀ {ctx : ProgramCtx} {s : Store} {g : UnseqGraph} {i : Nat} {o : UnseqOcc} {binds : List VarId}
    {callee : Expr} {args : List Expr} (thenB : Stmt) (st : List UnseqStatus) (tg : List (VarId × TargetRef))
    (env : LocalEnv) (k' : Cont) (ch : Choices) (_hget : g.occs[i]? = some o)
    (_hbody : o.body = .invoke binds callee args),
    stepFn ctx s (.next (.unseqK g thenB st tg env (.wait i) k')) ch
      = .ok (.next (.unseqK g thenB (st.set i .done) tg env .pick k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.unseqWait_invoke

-- 394. `Equations.lean` — `stateWf_empty`
example : ∀ {ctx : ProgramCtx},
    StateWf ctx ({} : Store) :=
  @GoLean.GoCore.Equations.stateWf_empty

-- 395. `Equations.lean` — `seedGlobals_nil`
example : ∀ {ctx : ProgramCtx},
    seedGlobals ctx ({} : Store) #[] = .ok {} :=
  @GoLean.GoCore.Equations.seedGlobals_nil

-- 396. `Equations.lean` — `runPkgInitM_none`
example : ∀ {ctx : ProgramCtx} {fuel : Nat} {s : Store} {ch : Choices}
    (_h : findFunctionIn? ctx.functions pkgInitFuncId = none),
    runPkgInitM ctx fuel s ch = .ok (s, ch) :=
  @GoLean.GoCore.Equations.runPkgInitM_none

-- 397. `Equations.lean` — `runProgramSetup_noInit`
example : ∀ {fuel : Nat} {program : Program} {name : String} {args : Array GoValue} {choices : Choices}
    {func : Func} {env frameEnv : LocalEnv} {s₂ s₃ : Store} {resultLocs : List Loc}
    (_hf : findFunctionIn? program.funcs ⟨name⟩ = some func) (_harity : func.args.size = args.size)
    (_hres : program.typeDefs.hasReservedPrefix = true) (_hglob : program.globals = #[])
    (_hinit : findFunctionIn? program.funcs pkgInitFuncId = none)
    (_hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (_ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃))
    (_hp : pinResultLocs frameEnv func.results.toList = .ok resultLocs),
    runProgramSetupM fuel program name args choices
      = .ok (⟨program⟩, .exec func.body frameEnv (.frame [] [] [] [] .stop func.id), s₃, resultLocs, choices) :=
  @GoLean.GoCore.Equations.runProgramSetup_noInit

-- 398. `Equations.lean` — `pinResultLocs_eq_of_lookup`
example :
    ∀ (env : LocalEnv) (ps : List Param) (f : Nat → Loc),
      (∀ (j : Nat) (hj : j < ps.length), LocalEnv.lookup env ps[j].id = some (f j)) →
      pinResultLocs env ps = .ok ((List.range ps.length).map f) :=
  @GoLean.GoCore.Equations.pinResultLocs_eq_of_lookup

-- 399. `Equations.lean` — `setup_lookup_arg`
example : ∀ {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv} {s₂ s₃ : Store}
    (_hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (_ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃))
    (_hdistinct : namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true) (i : Nat)
    (_hi : i < func.args.size),
    LocalEnv.lookup frameEnv func.args[i].id = some (.base ⟨i⟩) :=
  @GoLean.GoCore.Equations.setup_lookup_arg

-- 400. `Equations.lean` — `setup_lookup_result`
example : ∀ {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv} {s₂ s₃ : Store}
    (_hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (_ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃))
    (_hdistinct : namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true) (j : Nat)
    (_hj : j < func.results.size),
    LocalEnv.lookup frameEnv func.results[j].id = some (.base ⟨func.args.size + j⟩) :=
  @GoLean.GoCore.Equations.setup_lookup_result

-- 401. `Equations.lean` — `setup_resultLocs`
example : ∀ {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv} {s₂ s₃ : Store}
    {resultLocs : List Loc} (_hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (_ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃))
    (_hdistinct : namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true)
    (_hp : pinResultLocs frameEnv func.results.toList = .ok resultLocs),
    resultLocs = (List.range func.results.size).map (fun j => Loc.base ⟨func.args.size + j⟩) :=
  @GoLean.GoCore.Equations.setup_resultLocs

-- 402. `Equations.lean` — `setup_heap_size`
example : ∀ {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv} {s₂ s₃ : Store}
    (_hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (_ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃)),
    s₃.heap.size = func.args.size + func.results.size :=
  @GoLean.GoCore.Equations.setup_heap_size

-- 403. `PoolProjection.lean` — `transferable_wide`
example : ∀ {r : Except Stop (Store × Choices)} (_h : transferable r),
    transferableWide r :=
  @GoLean.GoCore.Machine.transferable_wide

-- 404. `PoolProjection.lean` — `transferableWide_ok`
example : ∀ (x : Store × Choices),
    transferableWide (.ok x) :=
  @GoLean.GoCore.Machine.transferableWide_ok

-- 405. `PoolProjection.lean` — `transferableWide_fuelOut`
example :
    transferableWide (.error .fuelOut) :=
  @GoLean.GoCore.Machine.transferableWide_fuelOut

-- 406. `PoolProjection.lean` — `transferableWide_terminal`
example : ∀ {t : Terminal} (_ht : t ≠ .deadlock),
    transferableWide (.error (.terminal t)) :=
  @GoLean.GoCore.Machine.transferableWide_terminal

-- 407. `PoolProjection.lean` — `not_transferableWide_deadlock`
example :
    ¬ transferableWide (.error (.terminal .deadlock)) :=
  @GoLean.GoCore.Machine.not_transferableWide_deadlock

-- 408. `PoolProjection.lean` — `not_transferableWide_refusal`
example : ∀ (r : Refusal),
    ¬ transferableWide (.error (.refusal r)) :=
  @GoLean.GoCore.Machine.not_transferableWide_refusal

-- 409. `PoolProjection.lean` — `seqOut_zero`
example : ∀ {ctx : ProgramCtx} (σ : Store) (c : Config) (ch : Choices) (acc : GoString),
    seqOut ctx 0 σ c ch acc = acc :=
  @GoLean.GoCore.Machine.seqOut_zero

-- 410. `PoolProjection.lean` — `seqOut_succ`
example : ∀ {ctx : ProgramCtx} (fuel : Nat) (σ : Store) (c : Config) (ch : Choices) (acc : GoString),
    seqOut ctx (fuel + 1) σ c ch acc
      = (if c.isTerminal || isBlockedConfig c then acc
         else match stepFn ctx σ c ch with
           | .error _ => acc
           | .ok (c', σ', ch', l) => seqOut ctx fuel σ' c' ch' (l.out.foldl GoString.append acc)) :=
  @GoLean.GoCore.Machine.seqOut_succ

-- 411. `PoolProjection.lean` — `outFold_nil`
example : ∀ (acc : GoString),
    outFold [] acc = acc :=
  @GoLean.GoCore.Machine.outFold_nil

-- 412. `PoolProjection.lean` — `outFold_cons`
example : ∀ (l : StepLabel) (ls : List StepLabel) (acc : GoString),
    outFold (l :: ls) acc = outFold ls (l.out.foldl GoString.append acc) :=
  @GoLean.GoCore.Machine.outFold_cons

-- 413. `PoolProjection.lean` — `outFold_eq_fold`
example :
    ∀ (ls : List StepLabel) (acc : GoString),
       outFold ls acc = (StepLabel.fold ls).out.foldl GoString.append acc :=
  @GoLean.GoCore.Machine.outFold_eq_fold

-- 414. `PoolProjection.lean` — `runnableIdxs_singleton_none`
example : ∀ {ctx : ProgramCtx} {σ : Store} {t : Thread} (_h : threadRunnable ctx σ t = false),
    runnableIdxs ctx σ #[t] = [] :=
  @GoLean.GoCore.Machine.runnableIdxs_singleton_none

-- 415. `PoolProjection.lean` — `mainOutcome?_single_none`
example : ∀ {σ : Store} {c : Config} (_hd : c.isTerminal = false),
    MultiConfig.mainOutcome? ⟨#[.running c none], σ, 0⟩ = none :=
  @GoLean.GoCore.Machine.mainOutcome?_single_none

-- 416. `PoolProjection.lean` — `front_single_step`
example : ∀ {ctx : ProgramCtx} {σ : Store} {c : Config} {ch : Choices} (_hd : c.isTerminal = false)
    (_hb : isBlockedConfig c = false),
    front ctx ⟨#[.running c none], σ, 0⟩ ch = .ok (.inr ch) :=
  @GoLean.GoCore.Machine.front_single_step

-- 417. `PoolProjection.lean` — `front_single_flagged`
example : ∀ {ctx : ProgramCtx} {σ : Store} {c : Config} {site : ChoiceSite} {ch : Choices},
    front ctx ⟨#[.running c (some site)], σ, 0⟩ ch = .ok (.inr ch) :=
  @GoLean.GoCore.Machine.front_single_flagged

-- 418. `PoolProjection.lean` — `front_terminal`
example : ∀ {ctx : ProgramCtx} {σ : Store} {ch : Choices},
    front ctx ⟨#[.running (.next .stop) none], σ, 0⟩ ch = .ok (.inl (σ, ch)) :=
  @GoLean.GoCore.Machine.front_terminal

-- 419. `PoolProjection.lean` — `front_aborted`
example : ∀ {ctx : ProgramCtx} {σ : Store} {msg : String} {ch : Choices},
    front ctx ⟨#[.aborted msg], σ, 0⟩ ch = .error (.panic msg) :=
  @GoLean.GoCore.Machine.front_aborted

-- 420. `PoolProjection.lean` — `stepThread_single_out`
example : ∀ {ctx : ProgramCtx} {σ : Store} {c : Config} {ch : Choices} (_hbl : isBlockedConfig c = false)
    (_hsp : spawnPlan c = none) (_hab : c.abort? = none) {c' : Config} {σ' : Store} {ch' : Choices}
    {l : StepLabel} (_hstep : stepFn ctx σ c ch = .ok (c', σ', ch', l)),
    ∃ ev, stepThread ctx σ #[.running c none] 0 ch = .ok (#[Thread.afterStep σ c c'], σ', ch', ev)
      ∧ ev.out = l.out :=
  @GoLean.GoCore.Machine.stepThread_single_out

-- 421. `PoolProjection.lean` — `stepMulti_single_out`
example : ∀ {ctx : ProgramCtx} {σ : Store} {c : Config} {ch : Choices} (_hbl : isBlockedConfig c = false)
    (_hsp : spawnPlan c = none) (_hab : c.abort? = none) (_hdone : c.isTerminal = false) {c' : Config}
    {σ' : Store} {ch' : Choices} {l : StepLabel} (_hstep : stepFn ctx σ c ch = .ok (c', σ', ch', l)),
    ∃ ev, stepMulti ctx ⟨#[.running c none], σ, 0⟩ ch = .ok (⟨#[Thread.afterStep σ c c'], σ', 0⟩, ch', ev)
      ∧ ev.out = l.out :=
  @GoLean.GoCore.Machine.stepMulti_single_out

-- 422. `PoolProjection.lean` — `execProgLoopOut_single_wide`
example : ∀ {ctx : ProgramCtx},
    ∀ {fuel : Nat} {σ : Store} {c : Config} {ch : Choices} {rs : RaceState} {acc : GoString}
      {r : Except Stop (Store × Choices)},
      execStmtLoop ctx fuel σ c ch = r → transferableWide r →
      execProgLoopOut ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch acc
        = (seqOut ctx fuel σ c ch acc, r) :=
  @GoLean.GoCore.Machine.execProgLoopOut_single_wide

-- 423. `PoolProjection.lean` — `execProgLoopOut_single`
example : ∀ {ctx : ProgramCtx} {fuel : Nat} {σ : Store} {c : Config} {ch : Choices} {rs : RaceState}
    {acc : GoString} {r : Except Stop (Store × Choices)} (_hr : execStmtLoop ctx fuel σ c ch = r)
    (_htr : transferable r),
    execProgLoopOut ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch acc
      = (seqOut ctx fuel σ c ch acc, r) :=
  @GoLean.GoCore.Machine.execProgLoopOut_single

-- 424. `PoolProjection.lean` — `execProgLoop_single_wide`
example : ∀ {ctx : ProgramCtx} {fuel : Nat} {σ : Store} {c : Config} {ch : Choices} {rs : RaceState}
    {r : Except Stop (Store × Choices)} (_hr : execStmtLoop ctx fuel σ c ch = r) (_htr : transferableWide r),
    execProgLoop ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch = r :=
  @GoLean.GoCore.Machine.execProgLoop_single_wide

-- 425. `PoolProjection.lean` — `execProgLoop_single_terminal`
example : ∀ {ctx : ProgramCtx} {fuel : Nat} {σ : Store} {c : Config} {ch : Choices} {rs : RaceState}
    {t : Terminal} (_hr : execStmtLoop ctx fuel σ c ch = .error (.terminal t)) (_ht : t ≠ .deadlock),
    execProgLoop ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch = .error (.terminal t) :=
  @GoLean.GoCore.Machine.execProgLoop_single_terminal

-- 426. `PoolProjection.lean` — `execProgLoopOut_single_terminal`
example : ∀ {ctx : ProgramCtx} {fuel : Nat} {σ : Store} {c : Config} {ch : Choices} {rs : RaceState}
    {acc : GoString} {t : Terminal} (_hr : execStmtLoop ctx fuel σ c ch = .error (.terminal t))
    (_ht : t ≠ .deadlock),
    execProgLoopOut ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch acc
      = (seqOut ctx fuel σ c ch acc, .error (.terminal t)) :=
  @GoLean.GoCore.Machine.execProgLoopOut_single_terminal

-- 427. `PoolProjection.lean` — `isTerminal_false_of_stepFn_ok`
example : ∀ {ctx : ProgramCtx} {σ : Store} {c : Config} {ch : Choices} {c' : Config} {σ' : Store}
    {ch' : Choices} {l : StepLabel} (_h : stepFn ctx σ c ch = .ok (c', σ', ch', l)),
    c.isTerminal = false :=
  @GoLean.GoCore.Machine.isTerminal_false_of_stepFn_ok

-- 428. `PoolProjection.lean` — `isBlockedConfig_false_of_stepFn_ok`
example : ∀ {ctx : ProgramCtx} {σ : Store} {c : Config} {ch : Choices} {c' : Config} {σ' : Store}
    {ch' : Choices} {l : StepLabel} (_h : stepFn ctx σ c ch = .ok (c', σ', ch', l)),
    isBlockedConfig c = false :=
  @GoLean.GoCore.Machine.isBlockedConfig_false_of_stepFn_ok

-- 429. `PoolProjection.lean` — `zeroCost_stops`
example : ∀ {c : Config} (_hz : ZeroCost c),
    (c.isTerminal || isBlockedConfig c) = true :=
  @GoLean.GoCore.Machine.zeroCost_stops

-- 430. `PoolProjection.lean` — `seqOut_stop`
example : ∀ {ctx : ProgramCtx} {fuel : Nat} {σ : Store} {c : Config} {ch : Choices} {acc : GoString}
    (_h : ZeroCost c ∨ ∃ e, stepFn ctx σ c ch = .error e),
    seqOut ctx fuel σ c ch acc = acc :=
  @GoLean.GoCore.Machine.seqOut_stop

-- 431. `PoolProjection.lean` — `seqOut_of_prefix`
example : ∀ {ctx : ProgramCtx},
    ∀ {n : Nat} {σ sf : Store} {c cf : Config} {ch chf : Choices} {ls : List StepLabel},
      Prefix ctx n σ c ch ls sf cf chf → ∀ {fuel : Nat} {acc : GoString}, n ≤ fuel →
      (n = fuel ∨ ZeroCost cf ∨ ∃ e, stepFn ctx sf cf chf = .error e) →
      seqOut ctx fuel σ c ch acc = outFold ls acc :=
  @GoLean.GoCore.Machine.seqOut_of_prefix

-- 432. `PoolProjection.lean` — `execProgLoopOut_single_prefix`
example : ∀ {ctx : ProgramCtx} {fuel n : Nat} {σ sf : Store} {c cf : Config} {ch chf : Choices}
    {ls : List StepLabel} {rs : RaceState} {acc : GoString} {r : Except Stop (Store × Choices)}
    (_hr : execStmtLoop ctx fuel σ c ch = r) (_htr : transferable r) (_hp : Prefix ctx n σ c ch ls sf cf chf)
    (_hn : n ≤ fuel) (_hstop : n = fuel ∨ ZeroCost cf ∨ ∃ e, stepFn ctx sf cf chf = .error e),
    execProgLoopOut ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch acc
      = (outFold ls acc, r) :=
  @GoLean.GoCore.Machine.execProgLoopOut_single_prefix

-- 433. `PoolProjection.lean` — `pool_run_single_prefix`
example : ∀ {ctx : ProgramCtx} {fuel n : Nat} {σ sf : Store} {c cf : Config} {ch chf : Choices}
    {ls : List StepLabel} {rs : RaceState} {acc : GoString} {r : Except Stop (Store × Choices)}
    (_hr : execStmtLoop ctx fuel σ c ch = r) (_htr : transferable r) (_hp : Prefix ctx n σ c ch ls sf cf chf)
    (_hn : n ≤ fuel) (_hstop : n = fuel ∨ ZeroCost cf ∨ ∃ e, stepFn ctx sf cf chf = .error e),
    Run ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch acc (outFold ls acc, r) :=
  @GoLean.GoCore.Machine.pool_run_single_prefix

-- 434. `PoolProjection.lean` — `afterStepFlag_none_of_noRegistry`
example : ∀ {σ : Store} {c c' : Config} (_hsp : spawnPlan c = none) (_hreg : c.registryCommits σ = false),
    c.afterStepFlag σ c' = none :=
  @GoLean.GoCore.Machine.afterStepFlag_none_of_noRegistry

-- 435. `PoolProjection.lean` — `seqOpCount_eq_zero`
example : ∀ {ctx : ProgramCtx},
    ∀ {fuel : Nat} {σ : Store} {c : Config} {ch : Choices},
      (∀ n σ' c' ch' ls, Prefix ctx n σ c ch ls σ' c' ch' → n < fuel →
        ∀ c'' σ'' ch'' l, stepFn ctx σ' c' ch' = .ok (c'', σ'', ch'', l) → c'.afterStepFlag σ' c'' = none) →
      seqOpCount ctx fuel σ c ch = 0 :=
  @GoLean.GoCore.Machine.seqOpCount_eq_zero

-- 436. `PoolProjection.lean` — `execProgLoop_single_noBoundary`
example : ∀ {ctx : ProgramCtx} {fuel : Nat} {σ : Store} {c : Config} {ch : Choices} {rs : RaceState}
    {r : Except Stop (Store × Choices)} (_hr : execStmtLoop ctx fuel σ c ch = r) (_htr : transferable r)
    (_hnb : ∀ n σ' c' ch' ls, Prefix ctx n σ c ch ls σ' c' ch' → n < fuel → ∀ c'' σ'' ch'' l, stepFn ctx σ' c' ch' = .ok (c'', σ'', ch'', l) → c'.afterStepFlag σ' c'' = none),
    execProgLoop ctx fuel ⟨#[.running c none], σ, 0⟩ rs ch = r :=
  @GoLean.GoCore.Machine.execProgLoop_single_noBoundary

-- ---- RE-PIN 10, the pre-landing round (packet D audit F3/F4): rows 437–499 (`Equations.lean`, appended), rows 500–501 (`PoolProjection.lean`, appended) ----

-- 437. `Equations.lean` — `bind_eq_error`
example : ∀ {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {e : ε} (_h : x >>= f = .error e),
    x = .error e ∨ ∃ a, x = .ok a ∧ f a = .error e :=
  @GoLean.GoCore.Equations.bind_eq_error

-- 438. `Equations.lean` — `runCommit_error`
example : ∀ {α : Type} {c : Commit α} {s : Store} {e : Stop} (_hcs : c s = .error e)
    (_hne : ∀ msg, e ≠ .panic msg),
    runCommit c s = .error e :=
  @GoLean.GoCore.Equations.runCommit_error

-- 439. `Equations.lean` — `enterFramePickV_of_plan_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {fid : FuncId} {args : List GoValue} {e : Stop} (ch : Choices)
    (_h : enterFrame.plan ctx s fid args = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    enterFramePickV ctx s fid args ch = .error e :=
  @GoLean.GoCore.Equations.enterFramePickV_of_plan_error

-- 440. `Equations.lean` — `enterFrame_inv_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {fid : FuncId} {args : List GoValue} {e : Stop}
    (_h : enterFrame ctx s fid args = .error e),
    enterFrame.plan ctx s fid args = .error e ∨ ∃ c, enterFrame.plan ctx s fid args = .ok c ∧ c s = .error e :=
  @GoLean.GoCore.Equations.enterFrame_inv_error

-- 441. `Equations.lean` — `retV_syncStK_apply_panic`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : SyncOp} {done : List GoValue} {msg : String}
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applySyncOp ctx s ch op (v :: done).reverse env k' = .error (.panic msg)),
    stepFn ctx s (.retV v (.syncStK op done [] env k')) ch = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_syncStK_apply_panic

-- 442. `Equations.lean` — `evalE_strict_nullary_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {e : Expr} {op : StrictOp} {st : Stop} (env : LocalEnv) (k : Cont)
    (ch : Choices) (_h : strictPlan e = some (op, []))
    (_ha : applyStrictOp ctx s (projChainTarget ctx s k) op [] = .error st) (_hne : ∀ msg, st ≠ .panic msg),
    stepFn ctx s (.evalE e env k) ch = .error st :=
  @GoLean.GoCore.Equations.evalE_strict_nullary_error

-- 443. `Equations.lean` — `retV_chanStK_apply_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : ChanStOp} {done : List GoValue} {e : Stop}
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyChanOp ctx s op (v :: done).reverse env k' = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV v (.chanStK op done [] env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_chanStK_apply_error

-- 444. `Equations.lean` — `retV_selectOpsK_apply_panic`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {clauses : List (SelectClauseHead × Stmt)}
    {default? : Option Stmt} {done : List GoValue} {msg : String} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applySelect ctx s clauses default? (v :: done).reverse env k' ch = .error (.panic msg)),
    stepFn ctx s (.retV v (.selectOpsK clauses default? done [] env k')) ch
      = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_selectOpsK_apply_panic

-- 445. `Equations.lean` — `retV_selectOpsK_apply_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {clauses : List (SelectClauseHead × Stmt)}
    {default? : Option Stmt} {done : List GoValue} {e : Stop} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applySelect ctx s clauses default? (v :: done).reverse env k' ch = .error e)
    (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV v (.selectOpsK clauses default? done [] env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_selectOpsK_apply_error

-- 446. `Equations.lean` — `retV_rhsK_apply_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {rop : RhsOp} {done : List GoValue} {e : Stop}
    (refs : List TargetRef) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyRhsOp ctx s rop (v :: done).reverse = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV v (.rhsK rop refs done [] body env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_rhsK_apply_error

-- 447. `Equations.lean` — `retV_atomicStK_apply_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : AtomicOp} {done : List GoValue} {e : Stop}
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyAtomicOp ctx s op (v :: done).reverse env k' = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV v (.atomicStK op done [] env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_atomicStK_apply_error

-- 448. `Equations.lean` — `next_preprintK_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {older : List PanicEntry} {entry : PanicEntry}
    {newer : List PanicEntry} {e : Stop} (k' : Cont) (ch : Choices)
    (_h : preprintDispatch ctx s entry = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.next (.preprintK older entry newer k')) ch = .error e :=
  @GoLean.GoCore.Equations.next_preprintK_error

-- 449. `Equations.lean` — `retV_stmtOpK_apply_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : StmtOp} {nt : Nat} {done : List GoValue}
    {e : Stop} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyStmtOp ctx s ch op nt (v :: done).reverse = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV v (.stmtOpK op nt done [] env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_stmtOpK_apply_error

-- 450. `Equations.lean` — `next_storeK_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {ref : TargetRef} {val : GoValue} {e : Stop} (rs : List TargetRef)
    (vrest : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : storeTarget ctx s ref val = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.next (.storeK (ref :: rs) (val :: vrest) body env k')) ch = .error e :=
  @GoLean.GoCore.Equations.next_storeK_error

-- 451. `Equations.lean` — `exec_call_nullary_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {targets : Array Assignee} {fid : FuncId} {args : Array Expr}
    {plans : List (TargetShape × List Expr)} {e : Stop} (env : LocalEnv) (k : Cont) (ch : Choices)
    (_hp : targetsPlan targets.toList = some plans) (_hargs : args.toList = [])
    (_he : enterFrame ctx s fid [] = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.exec (.call targets fid args) env k) ch = .error e :=
  @GoLean.GoCore.Equations.exec_call_nullary_error

-- 452. `Equations.lean` — `retV_callArgsK_enter_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {fid : FuncId} {plans : List (TargetShape × List Expr)}
    {vals : List GoValue} {e : Stop} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_he : enterFrame ctx s fid (vals ++ [v]) = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV v (.callArgsK fid plans vals [] env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_callArgsK_enter_error

-- 453. `Equations.lean` — `retV_callValCalleeK_enter_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {fid : FuncId} {captured : List GoValue}
    {plans : List (TargetShape × List Expr)} {e : Stop} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_he : enterFrame ctx s fid captured = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV (.funcVal fid captured) (.callValCalleeK plans [] env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_callValCalleeK_enter_error

-- 454. `Equations.lean` — `retV_callValArgsK_enter_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {fid : FuncId} {captured vals : List GoValue}
    {plans : List (TargetShape × List Expr)} {e : Stop} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_he : enterFrame ctx s fid (captured ++ vals ++ [v]) = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV v (.callValArgsK (.funcVal fid captured) plans vals [] env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_callValArgsK_enter_error

-- 455. `Equations.lean` — `panicking_frame_defer_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {chain : List PanicEntry} {fid : FuncId}
    {captured args : List GoValue} {e : Stop} (t : List (TargetShape × List Expr)) (te : LocalEnv)
    (r : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (_he : enterFrame ctx s fid (captured ++ args) = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.panicking chain (.frame t te r ((.funcVal fid captured, args) :: ds) k' fr)) ch = .error e :=
  @GoLean.GoCore.Equations.panicking_frame_defer_error

-- 456. `Equations.lean` — `frameExit_defer_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {fid : FuncId} {captured args : List GoValue} {e : Stop}
    (targets : List (TargetShape × List Expr)) (tenv : LocalEnv) (results : List Loc)
    (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (_he : enterFrame ctx s fid (captured ++ args) = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFrameExit ctx s targets tenv results ((.funcVal fid captured, args) :: ds) k' fr ch = .error e :=
  @GoLean.GoCore.Equations.frameExit_defer_error

-- 457. `Equations.lean` — `exec_block_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {decls : Array Param} {env : LocalEnv} {e : Stop} (ss : Array Stmt)
    (k : Cont) (ch : Choices) (_h : allocDecls ctx env.pushScope s decls.toList = .error e),
    stepFn ctx s (.exec (.block decls ss) env k) ch = .error e :=
  @GoLean.GoCore.Equations.exec_block_error

-- 458. `Equations.lean` — `evalE_var_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {id : VarId} {loc : Loc} {e : Stop} (env : LocalEnv) (k : Cont)
    (ch : Choices) (_hl : LocalEnv.lookup env id = some loc) (_hv : loadRoot ctx s loc = .error e),
    stepFn ctx s (.evalE (.var id) env k) ch = .error e :=
  @GoLean.GoCore.Equations.evalE_var_error

-- 459. `Equations.lean` — `retV_mapRangeK_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {e : Stop} (keyVar valVar : Option VarId)
    (keyTy valTy : Ty) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : mapRangeStartSets s v = .error e),
    stepFn ctx s (.retV v (.mapRangeK keyVar valVar keyTy valTy body env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_mapRangeK_error

-- 460. `Equations.lean` — `next_mapIterK_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {keyTy valTy : Ty} {base : Option Loc} {produced : Array Nat}
    {e : Stop} (keyVar valVar : Option VarId) (body : Stmt) (start : Array Nat) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_h : mapIterCandidates ctx s keyTy valTy base produced = .error e),
    stepFn ctx s (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k')) ch = .error e :=
  @GoLean.GoCore.Equations.next_mapIterK_error

-- 461. `Equations.lean` — `frameExit_targets_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {results : List Loc} {e : Stop} (sh : TargetShape) (ex : Expr)
    (ops : List Expr) (rest : List (TargetShape × List Expr)) (tenv : LocalEnv) (k' : Cont) (fr : FuncId)
    (ch : Choices) (_hl : loadResults ctx s results = .error e),
    stepFrameExit ctx s ((sh, ex :: ops) :: rest) tenv results [] k' fr ch = .error e :=
  @GoLean.GoCore.Equations.frameExit_targets_error

-- 462. `Equations.lean` — `frameExit_preprint_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {rl : Loc} {e : Stop} (tenv : LocalEnv) (older : List PanicEntry)
    (entry : PanicEntry) (newer : List PanicEntry) (k'' : Cont) (fr : FuncId) (ch : Choices)
    (_hl : loadRoot ctx s rl = .error e),
    stepFrameExit ctx s [] tenv [rl] [] (.preprintK older entry newer k'') fr ch = .error e :=
  @GoLean.GoCore.Equations.frameExit_preprint_error

-- 463. `Equations.lean` — `unseqEnter_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {g : UnseqGraph} {env : LocalEnv} {e : Stop} (thenB : Stmt)
    (rest : List Stmt) (k' : Cont) (ch : Choices) (_hwf : g.wellFormed? = none)
    (_hen : unseqEntryCheck? g env = none) (_ha : allocDecls ctx env.pushScope s g.cells = .error e),
    stepFn ctx s (.exec (.unseq g thenB) env (.seq rest env k')) ch = .error e :=
  @GoLean.GoCore.Equations.unseqEnter_error

-- 464. `Equations.lean` — `unseqValue_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {g : UnseqGraph} {i : Nat} {o : UnseqOcc}
    {bind : VarId} {head : Expr} {loc : Loc} {e : Stop} (thenB : Stmt) (st : List UnseqStatus)
    (tg : List (VarId × TargetRef)) (env : LocalEnv) (k' : Cont) (ch : Choices) (_hget : g.occs[i]? = some o)
    (_hbody : o.body = .eval bind head) (_hloc : unseqCellLoc env bind = .ok loc)
    (_hst : storeLoc ctx s loc v = .error e),
    stepFn ctx s (.retV v (.unseqK g thenB st tg env (.wait i) k')) ch = .error e :=
  @GoLean.GoCore.Equations.unseqValue_error

-- 465. `Equations.lean` — `retV_ifK_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {e : Stop} (t el : Stmt) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_hv : valueAsBool v = .error e),
    stepFn ctx s (.retV v (.ifK t el env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_ifK_error

-- 466. `Equations.lean` — `retV_whileK_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {e : Stop} (c : Expr) (b : Stmt) (env : LocalEnv)
    (k' : Cont) (ch : Choices) (_hv : valueAsBool v = .error e),
    stepFn ctx s (.retV v (.whileK c b env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_whileK_error

-- 467. `Equations.lean` — `retV_andK_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {e : Stop} (r : Expr) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_hv : valueAsBool v = .error e),
    stepFn ctx s (.retV v (.andK r env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_andK_error

-- 468. `Equations.lean` — `retV_orK_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {e : Stop} (r : Expr) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_hv : valueAsBool v = .error e),
    stepFn ctx s (.retV v (.orK r env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_orK_error

-- 469. `Equations.lean` — `retV_boolK_error`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {e : Stop} (k' : Cont) (ch : Choices)
    (_hv : valueAsBool v = .error e),
    stepFn ctx s (.retV v (.boolK k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_boolK_error

-- 470. `Equations.lean` — `valueAsBool_nonbool`
example : ∀ {v : GoValue} (_h : ∀ b, v ≠ .bool b),
    valueAsBool v = .error (.stuck s!"expected bool value, got {repr v}") :=
  @GoLean.GoCore.Equations.valueAsBool_nonbool

-- 471. `Equations.lean` — `retV_callValCalleeK_args_notfunc`
example : ∀ {ctx : ProgramCtx} {s : Store} {cv : GoValue} (plans : List (TargetShape × List Expr)) (a : Expr)
    (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices) (_hd : deferrableCallee cv = false),
    stepFn ctx s (.retV cv (.callValCalleeK plans (a :: rest) env k')) ch
      = .error (.stuck s!"expected function value, got {repr cv}") :=
  @GoLean.GoCore.Equations.retV_callValCalleeK_args_notfunc

-- 472. `Equations.lean` — `retV_deferCalleeK_notfunc`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (args : List Expr) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_hd : deferrableCallee v = false),
    stepFn ctx s (.retV v (.deferCalleeK args env k')) ch = .error (.stuck s!"expected function value in defer, got {repr v}") :=
  @GoLean.GoCore.Equations.retV_deferCalleeK_notfunc

-- 473. `Equations.lean` — `retV_goCalleeK_notfunc`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (args : List Expr) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_hd : deferrableCallee v = false),
    stepFn ctx s (.retV v (.goCalleeK args env k')) ch = .error (.stuck s!"expected function value in go statement, got {repr v}") :=
  @GoLean.GoCore.Equations.retV_goCalleeK_notfunc

-- 474. `Equations.lean` — `deferrableCallee_false`
example : ∀ {cv : GoValue} (_hf : ∀ fid c, cv ≠ .funcVal fid c) (_hn : cv ≠ .nil),
    deferrableCallee cv = false :=
  @GoLean.GoCore.Equations.deferrableCallee_false

-- 475. `Equations.lean` — `panicking_frame_defer_notfunc`
example : ∀ {ctx : ProgramCtx} {s : Store} {chain : List PanicEntry} {cv : GoValue} (args : List GoValue)
    (t : List (TargetShape × List Expr)) (te : LocalEnv) (r : List Loc) (ds : List (GoValue × List GoValue))
    (k' : Cont) (fr : FuncId) (ch : Choices) (_hf : ∀ fid c, cv ≠ .funcVal fid c) (_hn : cv ≠ .nil),
    stepFn ctx s (.panicking chain (.frame t te r ((cv, args) :: ds) k' fr)) ch
      = .error (.stuck s!"deferred callee is not a function value: {repr cv}") :=
  @GoLean.GoCore.Equations.panicking_frame_defer_notfunc

-- 476. `Equations.lean` — `frameExit_defer_notfunc`
example : ∀ {ctx : ProgramCtx} {s : Store} {cv : GoValue} (args : List GoValue)
    (targets : List (TargetShape × List Expr)) (tenv : LocalEnv) (results : List Loc)
    (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (_hf : ∀ fid c, cv ≠ .funcVal fid c) (_hn : cv ≠ .nil),
    stepFrameExit ctx s targets tenv results ((cv, args) :: ds) k' fr ch
      = .error (.stuck s!"deferred callee is not a function value: {repr cv}") :=
  @GoLean.GoCore.Equations.frameExit_defer_notfunc

-- 477. `Equations.lean` — `retV_preprintK_nonstring`
example : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (older : List PanicEntry) (entry : PanicEntry)
    (newer : List PanicEntry) (k' : Cont) (ch : Choices) (_hs : ∀ t, v ≠ .string t),
    stepFn ctx s (.retV v (.preprintK older entry newer k')) ch
      = .error (.stuck s!"preprint: the payload method returned a non-string result {repr v}") :=
  @GoLean.GoCore.Equations.retV_preprintK_nonstring

-- 478. `Equations.lean` — `next_storeK_arity_refs`
example : ∀ {ctx : ProgramCtx} (s : Store) (r : TargetRef) (rs : List TargetRef) (body : Stmt) (env : LocalEnv)
    (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.storeK (r :: rs) [] body env k')) ch
      = .error (.internal "storeK value/target arity mismatch (the shared phase-2 spine: receive delivery, assignment, comma-ok, call write-back)") :=
  @GoLean.GoCore.Equations.next_storeK_arity_refs

-- 479. `Equations.lean` — `next_storeK_arity_vals`
example : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (vs : List GoValue) (body : Stmt) (env : LocalEnv)
    (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.storeK [] (v :: vs) body env k')) ch
      = .error (.internal "storeK value/target arity mismatch (the shared phase-2 spine: receive delivery, assignment, comma-ok, call write-back)") :=
  @GoLean.GoCore.Equations.next_storeK_arity_vals

-- 480. `Equations.lean` — `contHeadLabel_labelK`
example : ∀ (name : String) (k : Cont),
    contHeadLabel (.labelK name k) = some name :=
  @GoLean.GoCore.Equations.contHeadLabel_labelK

-- 481. `Equations.lean` — `contHeadLabel_stop`
example :
    contHeadLabel .stop = none :=
  @GoLean.GoCore.Equations.contHeadLabel_stop

-- 482. `Equations.lean` — `contHeadLabel_frame`
example : ∀ (t : List (TargetShape × List Expr)) (te : LocalEnv) (r : List Loc)
    (ds : List (GoValue × List GoValue)) (k : Cont) (fr : FuncId),
    contHeadLabel (.frame t te r ds k fr) = none :=
  @GoLean.GoCore.Equations.contHeadLabel_frame

-- 483. `Equations.lean` — `signalStep_breakableK_brkTo`
example : ∀ (L : String) (k' : Cont),
    signalStep (.brkTo L) (.breakableK k') = some (.signal (.brkTo L) k') :=
  @GoLean.GoCore.Equations.signalStep_breakableK_brkTo

-- 484. `Equations.lean` — `signalStep_breakableK_contTo`
example : ∀ (L : String) (k' : Cont),
    signalStep (.contTo L) (.breakableK k') = some (.signal (.contTo L) k') :=
  @GoLean.GoCore.Equations.signalStep_breakableK_contTo

-- 485. `Equations.lean` — `signalStep_labelK_brk`
example : ∀ (name : String) (k' : Cont),
    signalStep .brk (.labelK name k') = some (.signal .brk k') :=
  @GoLean.GoCore.Equations.signalStep_labelK_brk

-- 486. `Equations.lean` — `signalStep_labelK_cont`
example : ∀ (name : String) (k' : Cont),
    signalStep .cont (.labelK name k') = some (.signal .cont k') :=
  @GoLean.GoCore.Equations.signalStep_labelK_cont

-- 487. `Equations.lean` — `signalStep_labelK_brkTo_ne`
example : ∀ {name L : String} (k' : Cont) (_h : name ≠ L),
    signalStep (.brkTo L) (.labelK name k') = some (.signal (.brkTo L) k') :=
  @GoLean.GoCore.Equations.signalStep_labelK_brkTo_ne

-- 488. `Equations.lean` — `signalStep_labelK_contTo_self`
example : ∀ (name : String) (k' : Cont),
    signalStep (.contTo name) (.labelK name k') = none :=
  @GoLean.GoCore.Equations.signalStep_labelK_contTo_self

-- 489. `Equations.lean` — `signalStep_labelK_contTo_ne`
example : ∀ {name L : String} (k' : Cont) (_h : name ≠ L),
    signalStep (.contTo L) (.labelK name k') = some (.signal (.contTo L) k') :=
  @GoLean.GoCore.Equations.signalStep_labelK_contTo_ne

-- 490. `Equations.lean` — `signalStep_loop_brkTo`
example : ∀ (L : String) (c : Expr) (b : Stmt) (env : LocalEnv) (k' : Cont),
    signalStep (.brkTo L) (.loop c b env k') = some (.signal (.brkTo L) k') :=
  @GoLean.GoCore.Equations.signalStep_loop_brkTo

-- 491. `Equations.lean` — `signalStep_loop_contTo_self`
example : ∀ {L : String} (c : Expr) (b : Stmt) (env : LocalEnv) {k' : Cont} (_h : contHeadLabel k' = some L),
    signalStep (.contTo L) (.loop c b env k') = some (.exec (.while c b) env k') :=
  @GoLean.GoCore.Equations.signalStep_loop_contTo_self

-- 492. `Equations.lean` — `signalStep_loop_contTo_ne`
example : ∀ {L : String} (c : Expr) (b : Stmt) (env : LocalEnv) {k' : Cont} (_h : contHeadLabel k' ≠ some L),
    signalStep (.contTo L) (.loop c b env k') = some (.signal (.contTo L) k') :=
  @GoLean.GoCore.Equations.signalStep_loop_contTo_ne

-- 493. `Equations.lean` — `signalStep_mapIterK_brk`
example : ∀ (keyVar valVar : Option VarId) (keyTy valTy : Ty) (body : Stmt) (base : Option Loc)
    (produced start : Array Nat) (env : LocalEnv) (k' : Cont),
    signalStep .brk (.mapIterK keyVar valVar keyTy valTy body base produced start env k') = some (.next k') :=
  @GoLean.GoCore.Equations.signalStep_mapIterK_brk

-- 494. `Equations.lean` — `signalStep_mapIterK_cont`
example : ∀ (keyVar valVar : Option VarId) (keyTy valTy : Ty) (body : Stmt) (base : Option Loc)
    (produced start : Array Nat) (env : LocalEnv) (k' : Cont),
    signalStep .cont (.mapIterK keyVar valVar keyTy valTy body base produced start env k')
      = some (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k')) :=
  @GoLean.GoCore.Equations.signalStep_mapIterK_cont

-- 495. `Equations.lean` — `signalStep_mapIterK_ret`
example : ∀ (keyVar valVar : Option VarId) (keyTy valTy : Ty) (body : Stmt) (base : Option Loc)
    (produced start : Array Nat) (env : LocalEnv) (k' : Cont),
    signalStep .ret (.mapIterK keyVar valVar keyTy valTy body base produced start env k') = some (.signal .ret k') :=
  @GoLean.GoCore.Equations.signalStep_mapIterK_ret

-- 496. `Equations.lean` — `signalStep_mapIterK_brkTo`
example : ∀ (L : String) (keyVar valVar : Option VarId) (keyTy valTy : Ty) (body : Stmt) (base : Option Loc)
    (produced start : Array Nat) (env : LocalEnv) (k' : Cont),
    signalStep (.brkTo L) (.mapIterK keyVar valVar keyTy valTy body base produced start env k') = some (.signal (.brkTo L) k') :=
  @GoLean.GoCore.Equations.signalStep_mapIterK_brkTo

-- 497. `Equations.lean` — `signalStep_mapIterK_contTo_self`
example : ∀ {L : String} (keyVar valVar : Option VarId) (keyTy valTy : Ty) (body : Stmt) (base : Option Loc)
    (produced start : Array Nat) (env : LocalEnv) {k' : Cont} (_h : contHeadLabel k' = some L),
    signalStep (.contTo L) (.mapIterK keyVar valVar keyTy valTy body base produced start env k')
      = some (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k')) :=
  @GoLean.GoCore.Equations.signalStep_mapIterK_contTo_self

-- 498. `Equations.lean` — `signalStep_mapIterK_contTo_ne`
example : ∀ {L : String} (keyVar valVar : Option VarId) (keyTy valTy : Ty) (body : Stmt) (base : Option Loc)
    (produced start : Array Nat) (env : LocalEnv) {k' : Cont} (_h : contHeadLabel k' ≠ some L),
    signalStep (.contTo L) (.mapIterK keyVar valVar keyTy valTy body base produced start env k') = some (.signal (.contTo L) k') :=
  @GoLean.GoCore.Equations.signalStep_mapIterK_contTo_ne

-- 499. `Equations.lean` — `signal_labelK_contTo_self`
example : ∀ {ctx : ProgramCtx} (s : Store) (name : String) (k' : Cont) (ch : Choices),
    stepFn ctx s (.signal (.contTo name) (.labelK name k')) ch = .error (.stuck s!"continue to non-loop label {name}") :=
  @GoLean.GoCore.Equations.signal_labelK_contTo_self

-- 500. `PoolProjection.lean` — `execProgLoop_single_noBoundary_wide`
example : ∀ {ctx : ProgramCtx} {fuel : Nat} {σ : Store} {c : Config} {ch : Choices} {rs : RaceState}
    {r : Except Stop (Store × Choices)} (_hr : execStmtLoop ctx fuel σ c ch = r) (_htr : transferableWide r)
    (_hnb : ∀ n σ' c' ch' ls, Prefix ctx n σ c ch ls σ' c' ch' → n < fuel → ∀ c'' σ'' ch'' l, stepFn ctx σ' c' ch' = .ok (c'', σ'', ch'', l) → c'.afterStepFlag σ' c'' = none),
    execProgLoop ctx fuel ⟨#[.running c none], σ, 0⟩ rs ch = r :=
  @GoLean.GoCore.Machine.execProgLoop_single_noBoundary_wide

-- 501. `PoolProjection.lean` — `execProgLoopOut_single_noBoundary_wide`
example : ∀ {ctx : ProgramCtx} {fuel : Nat} {σ : Store} {c : Config} {ch : Choices} {rs : RaceState}
    {acc : GoString} {r : Except Stop (Store × Choices)} (_hr : execStmtLoop ctx fuel σ c ch = r)
    (_htr : transferableWide r)
    (_hnb : ∀ n σ' c' ch' ls, Prefix ctx n σ c ch ls σ' c' ch' → n < fuel → ∀ c'' σ'' ch'' l, stepFn ctx σ' c' ch' = .ok (c'', σ'', ch'', l) → c'.afterStepFlag σ' c'' = none),
    execProgLoopOut ctx fuel ⟨#[.running c none], σ, 0⟩ rs ch acc = (seqOut ctx fuel σ c ch acc, r) :=
  @GoLean.GoCore.Machine.execProgLoopOut_single_noBoundary_wide

-- ---- RE-PIN 10, the window-review round (window review F1): row 502 (`Equations.lean`, the helper laws) ----

-- 502. `Equations.lean` — `applyStrictOp_toInterface_string` (window review F1: the boxing law FACT 3's
-- callee payload bottoms out in)
example : ∀ {ctx : ProgramCtx} (s : Store) (tgt : Loc → Loc) (ty : Ty) (v : GoValue),
    applyStrictOp ctx s tgt (.toInterface ty .string) [v] = .ok (.interface .string v, s, []) :=
  @GoLean.GoCore.Equations.applyStrictOp_toInterface_string

-- Pool grind M1, 2026-10-05: [AGENT Codex, pool grind]. Additions to rows 1–502.

-- 503. `PoolSound.lean` — `raceUpdate_error`
example :
  ∀ (ev : StepEvent) (m' : MultiConfig) (r : RaceState) (e : Stop),
    raceUpdate ev m' r = .error e → e = .raceDetected :=
  @GoLean.GoCore.PoolSound.raceUpdate_error

-- 504. `PoolSound.lean` — `stepMulti_error_cases`
example :
  ∀ (ctx : ProgramCtx) (m : MultiConfig) (ch : Choices) (e : Stop),
    stepMulti ctx m ch = .error e →
      (∃ r : Refusal, e = .refusal r) ∨ (∃ msg : String, e = .fatal msg) ∨ e = .deadlock :=
  @GoLean.GoCore.PoolSound.stepMulti_error_cases

-- 505. `PoolSound.lean` — `schedSlot_iff`
example :
  ∀ (ctx : ProgramCtx) (m : MultiConfig) (i : Nat),
    schedPick ctx m i ↔ ∃ slot : Nat, SchedSlot ctx m i slot :=
  @GoLean.GoCore.PoolSound.schedSlot_iff

-- 506. `PoolSound.lean` — `stepML_erase`
example :
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ev : StepEvent),
    StepML ctx m m' ev → StepM ctx m m' ev.trace :=
  @GoLean.GoCore.PoolSound.stepML_erase

-- 507. `PoolSound.lean` — `stepML_sound`
example :
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ch ch' : Choices) (ev : StepEvent),
    stepMulti ctx m ch = .ok (m', ch', ev) → StepML ctx m m' ev :=
  @GoLean.GoCore.PoolSound.stepML_sound

-- 508. `PoolSound.lean` — `stepML_complete`
example :
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ev : StepEvent),
    StepML ctx m m' ev → ∃ ch ch' : Choices, stepMulti ctx m ch = .ok (m', ch', ev) :=
  @GoLean.GoCore.PoolSound.stepML_complete

-- 509. `PoolSound.lean` — `stepM_lift`
example :
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (tr : AccessTrace),
    StepM ctx m m' tr → ∃ ev : StepEvent, StepML ctx m m' ev ∧ ev.trace = tr :=
  @GoLean.GoCore.PoolSound.stepM_lift

-- 510. `PoolSound.lean` — `stepsML_erase`
example :
  ∀ (ctx : ProgramCtx) (m mf : MultiConfig) (evs : List StepEvent),
    StepsML ctx m mf evs → PoolSteps ctx m mf :=
  @GoLean.GoCore.PoolSound.stepsML_erase

-- 511. `PoolSound.lean` — `stepMulti_replay`
example :
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ch ch' : Choices) (ev : StepEvent),
    stepMulti ctx m ch = .ok (m', ch', ev) →
    ∀ ch₂ ch₂' : Choices, replays ev.picks ch₂ ch₂' → stepMulti ctx m ch₂ = .ok (m', ch₂', ev) :=
  @GoLean.GoCore.PoolSound.stepMulti_replay

-- ---- RE-PIN 12 (the setup equations G-R1–G-R3, 2026-10-05): rows 512–520 (`SetupSound.lean`; the
-- `_stmt`s in `SetupStatement.lean`, each written out). Additions to rows 1–511. ----

-- 512. `SetupSound.lean` — `seedGlobals_cells_stmt`, written out (G-R2: the seeding equation — the
-- seeded heap IS the zero cells of the globals, in order, as one `Except` equation)
example :
  ∀ (ctx : ProgramCtx) (globals : Array GlobalDef),
    seedGlobals ctx {} globals
      = (fun cells => ({ heap := cells.toArray } : Store))
          <$> globals.toList.mapM (SetupStatement.zeroCell ctx) :=
  @GoLean.GoCore.SetupSound.seedGlobals_cells

-- 513. `SetupSound.lean` — `seedGlobals_cell_stmt`, written out (G-R2: global `i` at `.base ⟨i⟩`,
-- holding its zero value at its type)
example :
  ∀ {ctx : ProgramCtx} {globals : Array GlobalDef} {s₀ : Store},
    seedGlobals ctx {} globals = .ok s₀ →
    ∀ (i : Nat) (hi : i < globals.size), ∃ z : GoValue,
      defaultValue ctx globals[i].typ = .ok z
        ∧ Heap.lookup s₀.heap (.base ⟨i⟩) = some (.value globals[i].typ z) :=
  @GoLean.GoCore.SetupSound.seedGlobals_cell

-- 514. `SetupSound.lean` — `seedGlobals_heap_size_stmt`, written out (G-R2: one cell per global)
example :
  ∀ {ctx : ProgramCtx} {globals : Array GlobalDef} {s₀ : Store},
    seedGlobals ctx {} globals = .ok s₀ → s₀.heap.size = globals.size :=
  @GoLean.GoCore.SetupSound.seedGlobals_heap_size

-- 515. `SetupSound.lean` — `seedGlobals_wf_stmt`, written out (G-R2: a seeded store is well-formed,
-- unconditionally — so the setup seam's `StateWf` check never fires)
example :
  ∀ {ctx : ProgramCtx} {globals : Array GlobalDef} {s₀ : Store},
    seedGlobals ctx {} globals = .ok s₀ → StateWf ctx s₀ :=
  @GoLean.GoCore.SetupSound.seedGlobals_wf

-- 516. `SetupSound.lean` — `runProgramSetup_init_stmt`, written out (G-R1: the general setup
-- equation — seeding, package initialization and the entry bind as one rewrite; row 397
-- `runProgramSetup_noInit` is this at `globals = #[]`, no `$pkginit`)
example :
  ∀ {fuel : Nat} {program : Program} {name : String} {args : Array GoValue} {choices : Choices}
    {func : Func} {s₀ s₁ : Store} {choices₁ : Choices} {env frameEnv : LocalEnv} {s₂ s₃ : Store}
    {resultLocs : List Loc},
    findFunctionIn? program.funcs ⟨name⟩ = some func → func.args.size = args.size →
    program.typeDefs.hasReservedPrefix = true →
    seedGlobals ⟨program⟩ {} program.globals = .ok s₀ →
    runPkgInitM ⟨program⟩ fuel s₀ choices = .ok (s₁, choices₁) →
    bindParams ⟨program⟩ [] s₁ func.args.toList args.toList = .ok (env, s₂) →
    allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃) →
    pinResultLocs frameEnv func.results.toList = .ok resultLocs →
    runProgramSetupM fuel program name args choices
      = .ok (⟨program⟩, .exec func.body frameEnv (.frame [] [] [] [] .stop func.id), s₃, resultLocs,
          choices₁) :=
  @GoLean.GoCore.SetupSound.runProgramSetup_init

-- 517. `SetupSound.lean` — `setup_lookup_arg_from_stmt`, written out (G-R3: row 399 over an arbitrary
-- pre-bind store — parameter `i` at `entrySlot s₁ i`)
example :
  ∀ {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv}
    {s₁ s₂ s₃ : Store},
    bindParams ⟨program⟩ [] s₁ func.args.toList args.toList = .ok (env, s₂) →
    allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃) →
    namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true →
    ∀ (i : Nat) (hi : i < func.args.size),
      LocalEnv.lookup frameEnv func.args[i].id = some (entrySlot s₁ i) :=
  @GoLean.GoCore.SetupSound.setup_lookup_arg_from

-- 518. `SetupSound.lean` — `setup_lookup_result_from_stmt`, written out (G-R3: row 400 over an
-- arbitrary pre-bind store — result `j` at `entrySlot s₁ (func.args.size + j)`)
example :
  ∀ {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv}
    {s₁ s₂ s₃ : Store},
    bindParams ⟨program⟩ [] s₁ func.args.toList args.toList = .ok (env, s₂) →
    allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃) →
    namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true →
    ∀ (j : Nat) (hj : j < func.results.size),
      LocalEnv.lookup frameEnv func.results[j].id = some (entrySlot s₁ (func.args.size + j)) :=
  @GoLean.GoCore.SetupSound.setup_lookup_result_from

-- 519. `SetupSound.lean` — `setup_resultLocs_from_stmt`, written out (G-R3: row 401 over an arbitrary
-- pre-bind store)
example :
  ∀ {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv}
    {s₁ s₂ s₃ : Store} {resultLocs : List Loc},
    bindParams ⟨program⟩ [] s₁ func.args.toList args.toList = .ok (env, s₂) →
    allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃) →
    namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true →
    pinResultLocs frameEnv func.results.toList = .ok resultLocs →
    resultLocs = (List.range func.results.size).map (fun j => entrySlot s₁ (func.args.size + j)) :=
  @GoLean.GoCore.SetupSound.setup_resultLocs_from

-- 520. `SetupSound.lean` — `setup_heap_size_from_stmt`, written out (G-R3: row 402 over an arbitrary
-- pre-bind store)
example :
  ∀ {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv}
    {s₁ s₂ s₃ : Store},
    bindParams ⟨program⟩ [] s₁ func.args.toList args.toList = .ok (env, s₂) →
    allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃) →
    s₃.heap.size = s₁.heap.size + func.args.size + func.results.size :=
  @GoLean.GoCore.SetupSound.setup_heap_size_from

-- ---- RE-PIN 13 (G-R4 approved and proved, with the logic team's answers (a)–(d), 2026-10-05): rows
-- 521–527 (`SetupSound.lean`; the `_stmt`s in `SetupStatement.lean`, each written out). Additions to rows
-- 1–520. ----

-- 521. `SetupSound.lean` — `runInitConfig_eq_execStmtLoop_stmt`, written out (G-R4: the init loop IS the
-- entry loop when no print position is reached within the fuel; no blocked premise — answer (a))
example :
  ∀ {ctx : ProgramCtx} {fuel : Nat} {σ : Store} {c : Config} {ch : Choices},
    (∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n σ c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) →
    runInitConfig ctx fuel σ c ch = execStmtLoop ctx fuel σ c ch :=
  @GoLean.GoCore.SetupSound.runInitConfig_eq_execStmtLoop

-- 522. `SetupSound.lean` — `runInitConfig_ok_iff_stmt`, written out (answer (c); row 44 for the init loop)
example :
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s sf : Store) (c : Config) (ch chf : Choices),
    (∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) →
    (runInitConfig ctx fuel s c ch = .ok (sf, chf) ↔
      ∃ n, n ≤ fuel ∧ ∃ ls, Prefix ctx n s c ch ls sf (.next .stop) chf) :=
  @GoLean.GoCore.SetupSound.runInitConfig_ok_iff

-- 523. `SetupSound.lean` — `runInitConfig_panic_iff_stmt`, written out (answer (c); row 45 for the init loop)
example :
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices) (t : String),
    (∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) →
    (runInitConfig ctx fuel s c ch = .error (.terminal (.panic t)) ↔
      ∃ (n : Nat) (ls : List StepLabel) (sf : Store) (cf : Config) (chf ch'' : Choices)
        (rec : List PickRecord),
        n + 1 ≤ fuel ∧ Prefix ctx n s c ch ls sf cf chf ∧
          Finish ctx sf cf chf rec (.aborted t sf ch'') 1) :=
  @GoLean.GoCore.SetupSound.runInitConfig_panic_iff

-- 524. `SetupSound.lean` — `runInitConfig_deadlock_iff_stmt`, written out (answer (c); row 46 for the init
-- loop)
example :
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices),
    (∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) →
    (runInitConfig ctx fuel s c ch = .error (.terminal .deadlock) ↔
      ∃ n, n ≤ fuel ∧ ∃ (ls : List StepLabel) (sf : Store) (cf : Config) (chf : Choices),
        Prefix ctx n s c ch ls sf cf chf ∧ Finish ctx sf cf chf [] (.deadlock sf chf) 0) :=
  @GoLean.GoCore.SetupSound.runInitConfig_deadlock_iff

-- 525. `SetupSound.lean` — `runInitConfig_fuelOut_iff_stmt`, written out (answer (c); row 47 for the init
-- loop)
example :
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices),
    (∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) →
    (runInitConfig ctx fuel s c ch = .error .fuelOut ↔
      ∃ (ls : List StepLabel) (sf : Store) (cf : Config) (chf : Choices),
        Prefix ctx fuel s c ch ls sf cf chf ∧ ¬ ZeroCost cf) :=
  @GoLean.GoCore.SetupSound.runInitConfig_fuelOut_iff

-- 526. `SetupSound.lean` — `runPkgInitM_some_stmt`, written out (answer (d): `runPkgInitM` with `$pkginit`
-- present IS `runInitConfig` on the init configuration under `Except.mapError markInitPhase`; the twin of
-- row 396 `runPkgInitM_none`)
example :
  ∀ {ctx : ProgramCtx} {fuel : Nat} {s : Store} {ch : Choices} {initF : Func},
    findFunctionIn? ctx.functions pkgInitFuncId = some initF →
    initF.args.size = 0 → initF.results.size = 0 →
    runPkgInitM ctx fuel s ch
      = (runInitConfig ctx fuel s (.exec initF.body [] (.frame [] [] [] [] .stop initF.id)) ch).mapError
          markInitPhase :=
  @GoLean.GoCore.SetupSound.runPkgInitM_some

-- 527. `SetupSound.lean` — `runPkgInitM_ok_iff_stmt`, written out (answer (d): the success link G-R1's
-- `runPkgInitM` premise composes with)
example :
  ∀ {ctx : ProgramCtx} {fuel : Nat} {s s₁ : Store} {ch ch₁ : Choices} {initF : Func},
    findFunctionIn? ctx.functions pkgInitFuncId = some initF →
    initF.args.size = 0 → initF.results.size = 0 →
    (runPkgInitM ctx fuel s ch = .ok (s₁, ch₁) ↔
      runInitConfig ctx fuel s (.exec initF.body [] (.frame [] [] [] [] .stop initF.id)) ch
        = .ok (s₁, ch₁)) :=
  @GoLean.GoCore.SetupSound.runPkgInitM_ok_iff

-- Pool grind M2, 2026-10-05: [AGENT Codex, pool grind]. Rows 1–527 unchanged.

-- 528. `PoolSound.lean` — `stepML_who_runnable`
example :
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ev : StepEvent),
    StepML ctx m m' ev → ev.who ∈ runnableIdxs ctx m.shared m.threads :=
  @GoLean.GoCore.PoolSound.stepML_who_runnable

-- 529. `PoolSound.lean` — `stepML_sched`
example :
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ev : StepEvent),
    StepML ctx m m' ev → schedPick ctx m ev.who ∧ m'.cur = ev.who :=
  @GoLean.GoCore.PoolSound.stepML_sched

-- 530. `PoolSound.lean` — `stepML_switch_boundary`
example :
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ev : StepEvent),
    StepML ctx m m' ev → ev.who ≠ m.cur →
      ∃ t : Thread, m.threads[m.cur]? = some t ∧ t.atBoundary = true :=
  @GoLean.GoCore.PoolSound.stepML_switch_boundary

-- 531. `PoolSound.lean` — `stepML_sched_record`
example :
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ev : StepEvent) (site : ChoiceSite) (menu : List Nat),
    StepML ctx m m' ev → m.schedMenu? ctx = some (site, menu) → 1 < menu.length →
      ∃ slot : Nat, menu[slot]? = some ev.who ∧ ev.picks.head? = some ⟨site, menu.length, slot⟩ :=
  @GoLean.GoCore.PoolSound.stepML_sched_record

-- 532. `PoolSound.lean` — `stepML_frame`
example :
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ev : StepEvent),
    StepML ctx m m' ev →
      m.threads.size ≤ m'.threads.size ∧
      ∀ j : Nat, j < m.threads.size → j ≠ ev.who →
        m'.threads[j]? = m.threads[j]? ∨ ev.action = .paired j :=
  @GoLean.GoCore.PoolSound.stepML_frame

-- 533. `PoolSound.lean` — `stepML_paired_trace`
example :
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ev : StepEvent) (j : Nat),
    StepML ctx m m' ev → ev.action = .paired j →
      (∃ e : MemEvent, MemEvent.attributed j e ∈ ev.trace) ∨ MemEvent.hb (.rendezvous j) ∈ ev.trace :=
  @GoLean.GoCore.PoolSound.stepML_paired_trace

-- 534. `PoolSound.lean` — `stepML_spawn`
example :
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ev : StepEvent),
    StepML ctx m m' ev →
      ((∀ n : Nat, ev.action ≠ .spawned n) → m'.threads.size = m.threads.size) ∧
      (∀ n : Nat, ev.action = .spawned n →
        n = m.threads.size ∧ m'.threads.size = m.threads.size + 1 ∧
          MemEvent.hb (.spawn n) ∈ ev.trace) :=
  @GoLean.GoCore.PoolSound.stepML_spawn

-- 535. `PoolSound.lean` — `asleep_silent`
example :
  ∀ (ctx : ProgramCtx) (m : MultiConfig),
    runnableIdxs ctx m.shared m.threads = [] → ∀ (m' : MultiConfig) (ev : StepEvent), ¬ StepML ctx m m' ev :=
  @GoLean.GoCore.PoolSound.asleep_silent

-- 536. `PoolSound.lean` — `singleton_deadlock`
example :
  ∀ (ctx : ProgramCtx) (σ : Store) (c : Config),
    Blocked c → (PoolDeadlock ctx ⟨#[.running c none], σ, 0⟩ ↔ wakeReady ctx σ c = false) :=
  @GoLean.GoCore.PoolSound.singleton_deadlock

-- 537. `PoolSound.lean` — `mainOutcome_not_deadlock`
example :
  ∀ (ctx : ProgramCtx) (m : MultiConfig) (σ : Store),
    m.mainOutcome? = some σ → ¬ PoolDeadlock ctx m :=
  @GoLean.GoCore.PoolSound.mainOutcome_not_deadlock

-- 538. `PoolSound.lean` — `stepMulti_deadlock_elim`
example :
  ∀ (ctx : ProgramCtx) (m : MultiConfig) (ch ch₁ : Choices) (rec : List PickRecord),
    Continue ctx m ch ch₁ rec → stepMulti ctx m ch₁ ≠ .error .deadlock :=
  @GoLean.GoCore.PoolSound.stepMulti_deadlock_elim

-- Pool grind M3, 2026-10-05: [AGENT Codex, pool grind].

-- 539. `PoolSound.lean` — `front_continue`
example :
  ∀ (ctx : ProgramCtx) (m : MultiConfig) (ch ch₁ : Choices),
    front ctx m ch = .ok (.inr ch₁) ↔ ∃ rec : List PickRecord, Continue ctx m ch ch₁ rec :=
  @GoLean.GoCore.PoolSound.front_continue

-- 540. `PoolSound.lean` — `front_finish`
example :
  ∀ (ctx : ProgramCtx) (m : MultiConfig) (r : RaceState) (ch : Choices),
    (∀ (σ : Store) (ch' : Choices),
      front ctx m ch = .ok (.inl (σ, ch')) ↔ ∃ rec, PoolFinish ctx m r ch rec (.normal σ ch') 0) ∧
    (∀ msg : String,
      front ctx m ch = .error (.panic msg) ↔ PoolFinish ctx m r ch [] (.aborted msg ch) 0) ∧
    (front ctx m ch = .error .deadlock ↔ PoolFinish ctx m r ch [] (.deadlock ch) 0) :=
  @GoLean.GoCore.PoolSound.front_finish

-- 541. `PoolSound.lean` — `front_refusal`
example :
  ∀ (ctx : ProgramCtx) (m : MultiConfig) (ch : Choices) (rr : Refusal),
    front ctx m ch = .error (.refusal rr) ↔
      m.threads.isEmpty = true ∧ rr = .internal "thread pool without a main goroutine" :=
  @GoLean.GoCore.PoolSound.front_refusal

-- 542. `PoolSound.lean` — `poolFinish_functional`
example :
  ∀ (ctx : ProgramCtx) (m : MultiConfig) (r : RaceState) (ch : Choices)
    (rec rec' : List PickRecord) (o o' : PoolOutcome) (cost cost' : Nat),
    PoolFinish ctx m r ch rec o cost → PoolFinish ctx m r ch rec' o' cost' →
      rec = rec' ∧ o = o' ∧ cost = cost' :=
  @GoLean.GoCore.PoolSound.poolFinish_functional

-- 543. `PoolSound.lean` — `poolFinish_zero_not_continue`
example :
  ∀ (ctx : ProgramCtx) (m : MultiConfig) (r : RaceState) (ch ch₁ : Choices)
    (rec rec' : List PickRecord) (o : PoolOutcome),
    PoolFinish ctx m r ch rec o 0 → ¬ Continue ctx m ch ch₁ rec' :=
  @GoLean.GoCore.PoolSound.poolFinish_zero_not_continue

-- Pool grind M4, 2026-10-05: [AGENT Codex, pool grind].

open GoLean.GoCore.PoolStatement

-- 544. `PoolSound.lean` — `poolPrefix_comp`
example :
  ∀ (ctx : ProgramCtx) (n k : Nat) (m m₁ mf : MultiConfig) (r r₁ rf : RaceState)
    (ch ch₁ chf : Choices) (des des' : List DriverEvent),
    PoolPrefix ctx n m r ch des m₁ r₁ ch₁ → PoolPrefix ctx k m₁ r₁ ch₁ des' mf rf chf →
    PoolPrefix ctx (n + k) m r ch (des ++ des') mf rf chf :=
  @GoLean.GoCore.PoolSound.poolPrefix_comp

-- 545. `PoolSound.lean` — `poolPrefix_split`
example :
  ∀ (ctx : ProgramCtx) (n k : Nat) (m mf : MultiConfig) (r rf : RaceState) (ch chf : Choices)
    (des : List DriverEvent),
    PoolPrefix ctx (n + k) m r ch des mf rf chf →
    ∃ (des₁ des₂ : List DriverEvent) (m₁ : MultiConfig) (r₁ : RaceState) (ch₁ : Choices),
      des = des₁ ++ des₂ ∧ PoolPrefix ctx n m r ch des₁ m₁ r₁ ch₁ ∧
        PoolPrefix ctx k m₁ r₁ ch₁ des₂ mf rf chf :=
  @GoLean.GoCore.PoolSound.poolPrefix_split

-- 546. `PoolSound.lean` — `poolPrefix_labelled`
example :
  ∀ (ctx : ProgramCtx) (n : Nat) (m mf : MultiConfig) (r rf : RaceState) (ch chf : Choices)
    (des : List DriverEvent),
    PoolPrefix ctx n m r ch des mf rf chf → StepsML ctx m mf (DriverEvent.events des) :=
  @GoLean.GoCore.PoolSound.poolPrefix_labelled

-- 547. `PoolSound.lean` — `poolPrefix_erase`
example :
  ∀ (ctx : ProgramCtx) (n : Nat) (m mf : MultiConfig) (r rf : RaceState) (ch chf : Choices)
    (des : List DriverEvent),
    PoolPrefix ctx n m r ch des mf rf chf → PoolSteps ctx m mf :=
  @GoLean.GoCore.PoolSound.poolPrefix_erase

-- 548. `PoolSound.lean` — `poolPrefix_run`
example :
  ∀ (ctx : ProgramCtx) (n k : Nat) (m mf : MultiConfig) (r rf : RaceState) (ch chf : Choices)
    (des : List DriverEvent) (acc : GoString),
    PoolPrefix ctx n m r ch des mf rf chf →
    execProgLoopOut ctx (n + k) m r ch acc = execProgLoopOut ctx k mf rf chf (poolOut des acc) :=
  @GoLean.GoCore.PoolSound.poolPrefix_run

-- 549. `PoolSound.lean` — `pool_run_ok_iff`
example :
  ∀ (ctx : ProgramCtx) (fuel : Nat) (m : MultiConfig) (r : RaceState) (ch : Choices)
    (acc out : GoString) (σ : Store) (chf : Choices),
    execProgLoopOut ctx fuel m r ch acc = (out, .ok (σ, chf)) ↔
      ∃ (n : Nat) (des : List DriverEvent) (mf : MultiConfig) (rf : RaceState) (chf₀ : Choices)
        (rec : List PickRecord),
        n ≤ fuel ∧ PoolPrefix ctx n m r ch des mf rf chf₀ ∧
          PoolFinish ctx mf rf chf₀ rec (.normal σ chf) 0 ∧ out = poolOut des acc :=
  @GoLean.GoCore.PoolSound.pool_run_ok_iff

-- 550. `PoolSound.lean` — `pool_run_terminal_iff`
example :
  ∀ (ctx : ProgramCtx) (fuel : Nat) (m : MultiConfig) (r : RaceState) (ch : Choices)
    (acc out : GoString) (t : Terminal),
    execProgLoopOut ctx fuel m r ch acc = (out, .error (.terminal t)) ↔
      ∃ (n : Nat) (des : List DriverEvent) (mf : MultiConfig) (rf : RaceState) (chf : Choices)
        (rec : List PickRecord) (o : PoolOutcome) (cost : Nat),
        n + cost ≤ fuel ∧ PoolPrefix ctx n m r ch des mf rf chf ∧
          PoolFinish ctx mf rf chf rec o cost ∧ o.terminal? = some t ∧ out = poolOut des acc :=
  @GoLean.GoCore.PoolSound.pool_run_terminal_iff

-- 551. `PoolSound.lean` — `pool_run_fuelOut_iff`
example :
  ∀ (ctx : ProgramCtx) (fuel : Nat) (m : MultiConfig) (r : RaceState) (ch : Choices)
    (acc out : GoString),
    execProgLoopOut ctx fuel m r ch acc = (out, .error .fuelOut) ↔
      ∃ (des : List DriverEvent) (mf : MultiConfig) (rf : RaceState) (chf ch₁ : Choices)
        (rec : List PickRecord),
        PoolPrefix ctx fuel m r ch des mf rf chf ∧ Continue ctx mf chf ch₁ rec ∧
          out = poolOut des acc :=
  @GoLean.GoCore.PoolSound.pool_run_fuelOut_iff

-- 552. `PoolSound.lean` — `pool_run_refusal_iff`
example :
  ∀ (ctx : ProgramCtx) (fuel : Nat) (m : MultiConfig) (r : RaceState) (ch : Choices)
    (acc out : GoString) (rr : Refusal),
    execProgLoopOut ctx fuel m r ch acc = (out, .error (.refusal rr)) ↔
      ∃ (n : Nat) (des : List DriverEvent) (mf : MultiConfig) (rf : RaceState) (chf : Choices),
        PoolPrefix ctx n m r ch des mf rf chf ∧ out = poolOut des acc ∧
          ((n ≤ fuel ∧ front ctx mf chf = .error (.refusal rr)) ∨
           (n + 1 ≤ fuel ∧ ∃ (ch₁ : Choices) (rec : List PickRecord),
              Continue ctx mf chf ch₁ rec ∧ stepMulti ctx mf ch₁ = .error (.refusal rr))) :=
  @GoLean.GoCore.PoolSound.pool_run_refusal_iff

-- 553. `PoolSound.lean` — `pool_classification`
example :
  ∀ (ctx : ProgramCtx) (fuel : Nat) (m : MultiConfig) (r : RaceState) (ch : Choices)
    (acc : GoString),
    PoolClassOk ctx fuel m r ch acc ∨ PoolClassTerminal ctx fuel m r ch acc ∨
      PoolClassFuelOut ctx fuel m r ch acc ∨ PoolClassRefusal ctx fuel m r ch acc :=
  @GoLean.GoCore.PoolSound.pool_classification

-- 554. `PoolSound.lean` — `run_ok_prefix`
example :
  ∀ (ctx : ProgramCtx) (fuel : Nat) (m : MultiConfig) (r : RaceState) (ch : Choices)
    (acc out : GoString) (σ : Store) (chf : Choices),
    Run ctx fuel m r ch acc (out, .ok (σ, chf)) ↔
      ∃ (n : Nat) (des : List DriverEvent) (mf : MultiConfig) (rf : RaceState) (chf₀ : Choices)
        (rec : List PickRecord),
        n ≤ fuel ∧ PoolPrefix ctx n m r ch des mf rf chf₀ ∧
          PoolFinish ctx mf rf chf₀ rec (.normal σ chf) 0 ∧ out = poolOut des acc :=
  @GoLean.GoCore.PoolSound.run_ok_prefix

-- 555. `PoolSound.lean` — `program_prefix`
example :
  ∀ (fuel : Nat) (p : Program) (name : String) (args : Array GoValue) (ch : Choices)
    (pctx : ProgramCtx) (c₀ : Config) (s₀ : Store) (locs : List Loc) (ch₁ : Choices)
    (ro : Readout),
    runProgramSetupM fuel p name args ch = .ok (pctx, c₀, s₀, locs, ch₁) →
    runProgramPoolOutM fuel p name args ch = .ok ro →
    ∃ (n : Nat) (des : List DriverEvent) (mf : MultiConfig) (rf : RaceState) (chf₀ chf : Choices)
      (rec : List PickRecord) (sf : Store),
      n ≤ fuel ∧ PoolPrefix pctx n ⟨#[Thread.running c₀ none], s₀, 0⟩ {} ch₁ des mf rf chf₀ ∧
        PoolFinish pctx mf rf chf₀ rec (.normal sf chf) 0 ∧
        ro.output = poolOut des GoString.empty ∧ loadMany pctx sf locs = .ok ro.values.toList :=
  @GoLean.GoCore.PoolSound.program_prefix

-- 556. `PoolSound.lean` — `continue_replay`
example :
  ∀ (ctx : ProgramCtx) (m : MultiConfig) (ch ch₁ : Choices) (rec : List PickRecord),
    Continue ctx m ch ch₁ rec → ∀ ch₂ ch₂' : Choices, replays rec ch₂ ch₂' → Continue ctx m ch₂ ch₂' rec :=
  @GoLean.GoCore.PoolSound.continue_replay

-- 557. `PoolSound.lean` — `poolPrefix_replay`
example :
  ∀ (ctx : ProgramCtx) (n : Nat) (m mf : MultiConfig) (r rf : RaceState) (ch chf : Choices)
    (des : List DriverEvent),
    PoolPrefix ctx n m r ch des mf rf chf →
    ∀ ch₂ ch₂' : Choices, replays (des.flatMap fun d => d.window ++ d.event.picks) ch₂ ch₂' →
      PoolPrefix ctx n m r ch₂ des mf rf ch₂' :=
  @GoLean.GoCore.PoolSound.poolPrefix_replay

-- Pool grind M5, 2026-10-06: [AGENT Codex, pool grind].

-- 558. `PoolSound.lean` — `stepML_single_sound`
example :
  ∀ (ctx : ProgramCtx) (σ : Store) (c : Config) (m' : MultiConfig) (ev : StepEvent),
    isBlockedConfig c = false → spawnPlan c = none → c.abort? = none →
    StepML ctx ⟨#[.running c none], σ, 0⟩ m' ev →
      ∃ (c' : Config) (σ' : Store) (l : StepLabel),
        Step ctx c σ c' σ' l ∧ m' = ⟨#[Thread.afterStep σ c c'], σ', 0⟩ ∧
          ev.who = 0 ∧ ev.label = l :=
  @GoLean.GoCore.PoolSound.stepML_single_sound

-- 559. `PoolSound.lean` — `stepML_single_complete`
example :
  ∀ (ctx : ProgramCtx) (σ σ' : Store) (c c' : Config) (l : StepLabel),
    Step ctx c σ c' σ' l →
      ∃ ev : StepEvent,
        StepML ctx ⟨#[.running c none], σ, 0⟩ ⟨#[Thread.afterStep σ c c'], σ', 0⟩ ev ∧
          ev.who = 0 ∧ ev.label = l :=
  @GoLean.GoCore.PoolSound.stepML_single_complete

-- 560. `PoolSound.lean` — `singleton_finish_normal`
example :
  ∀ (ctx : ProgramCtx) (sf : Store) (chf : Choices) (rs : RaceState),
    PoolFinish ctx ⟨#[.running (.next .stop) none], sf, 0⟩ rs chf [] (.normal sf chf) 0 :=
  @GoLean.GoCore.PoolSound.singleton_finish_normal

-- 561. `PoolSound.lean` — `singleton_finish_aborted`
example :
  ∀ (ctx : ProgramCtx) (sf : Store) (cf : Config) (chf ch'' : Choices) (rec : List PickRecord)
    (t : String) (rs : RaceState),
    Finish ctx sf cf chf rec (.aborted t sf ch'') 1 →
      stepMulti ctx ⟨#[.running cf none], sf, 0⟩ chf
          = .ok (⟨#[.aborted t], sf, 0⟩, ch'', ⟨0, .aborted, ⟨[], rec, []⟩⟩) ∧
        PoolFinish ctx ⟨#[.aborted t], sf, 0⟩ rs ch'' [] (.aborted t ch'') 0 :=
  @GoLean.GoCore.PoolSound.singleton_finish_aborted

-- 562. `PoolSound.lean` — `singleton_finish_refused`
example :
  ∀ (ctx : ProgramCtx) (sf : Store) (cf : Config) (chf ch'' : Choices) (rec : List PickRecord)
    (rr : Refusal),
    Finish ctx sf cf chf rec (.refused rr sf ch'') 1 →
      stepMulti ctx ⟨#[.running cf none], sf, 0⟩ chf = .error (.refusal rr) :=
  @GoLean.GoCore.PoolSound.singleton_finish_refused

-- 563. `PoolSound.lean` — `singleton_finish_fatal`
example :
  ∀ (ctx : ProgramCtx) (sf : Store) (cf : Config) (chf : Choices) (msg : String) (rs : RaceState),
    Finish ctx sf cf chf [] (.fatal msg sf chf) 1 →
      PoolFinish ctx ⟨#[.running cf none], sf, 0⟩ rs chf [] (.fatal msg chf) 1 :=
  @GoLean.GoCore.PoolSound.singleton_finish_fatal

-- 564. `PoolSound.lean` — `singleton_finish_deadlock`
example :
  ∀ (ctx : ProgramCtx) (sf : Store) (cf : Config) (chf : Choices) (rs : RaceState),
    Finish ctx sf cf chf [] (.deadlock sf chf) 0 → wakeReady ctx sf cf = false →
      PoolFinish ctx ⟨#[.running cf none], sf, 0⟩ rs chf [] (.deadlock chf) 0 :=
  @GoLean.GoCore.PoolSound.singleton_finish_deadlock

-- 565. `PoolSound.lean` — `singleton_prefix_embedding`
example :
  ∀ (ctx : ProgramCtx) (n : Nat) (σ sf : Store) (c cf : Config) (ch chf : Choices)
    (ls : List StepLabel) (rs : RaceState),
    Prefix ctx n σ c ch ls sf cf chf →
      ∃ des : List DriverEvent,
        PoolPrefix ctx (n + seqOpCount ctx n σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch des
          ⟨#[.running cf none], sf, 0⟩ rs chf ∧
        (∀ d ∈ des, d.window = [] ∧ d.event.who = 0) ∧
        StepLabel.fold ((DriverEvent.events des).map StepEvent.label) = StepLabel.fold ls :=
  @GoLean.GoCore.PoolSound.singleton_prefix_embedding

-- 566. `PoolSound.lean` — `singleton_run`
example :
  ∀ (ctx : ProgramCtx) (fuel : Nat) (σ : Store) (c : Config) (ch : Choices) (rs : RaceState)
    (acc : GoString) (r : Except Stop (Store × Choices)),
    execStmtLoop ctx fuel σ c ch = r → transferableWide r →
    Run ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch acc
      (seqOut ctx fuel σ c ch acc, r) :=
  @GoLean.GoCore.PoolSound.singleton_run

-- ---- RE-PIN 15 (exported struct field offsets, gc-verified request (a1), 2026-10-07): rows 567–572
-- (`Ops.lean`). Additions to rows 1–566. ----

-- 567. `Ops.lean` — `structLayoutWith_sizeAlign`
example :
  ∀ (fieldSize : Ty → Except Stop (Nat × Nat)) (fields : List FieldDef)
    (offset maxAlign lastOffset lastSize : Nat),
    (fun r => (r.2.1, r.2.2)) <$> structLayoutWith fieldSize fields offset maxAlign lastOffset lastSize
      = structSizeAlignWith fieldSize fields offset maxAlign lastOffset lastSize :=
  @GoLean.GoCore.structLayoutWith_sizeAlign

-- 568. `Ops.lean` — `structLayoutWith_fields`
example :
  ∀ {fieldSize : Ty → Except Stop (Nat × Nat)} {fields : List FieldDef}
    {offset maxAlign lastOffset lastSize : Nat} {offsets : List Nat} {size align : Nat},
    offset ≤ lastOffset + lastSize →
    structLayoutWith fieldSize fields offset maxAlign lastOffset lastSize
      = .ok (offsets, size, align) →
    offset ≤ size ∧ offsets.length = fields.length ∧
    ∀ (k : Nat) (fd : FieldDef), fields[k]? = some fd →
      ∃ off sz al, offsets[k]? = some off ∧ fieldSize fd.typ = .ok (sz, al) ∧
        (al ≠ 0 → al ∣ off) ∧ offset ≤ off ∧ off + sz ≤ size :=
  @GoLean.GoCore.structLayoutWith_fields

-- 569. `Ops.lean` — `structLayoutWith_disjoint`
example :
  ∀ {fieldSize : Ty → Except Stop (Nat × Nat)} {fields : List FieldDef}
    {offset maxAlign lastOffset lastSize : Nat} {offsets : List Nat} {size align : Nat},
    structLayoutWith fieldSize fields offset maxAlign lastOffset lastSize
      = .ok (offsets, size, align) →
    ∀ (j k : Nat) (fd : FieldDef) (off off' sz al : Nat), j < k →
      fields[j]? = some fd → fieldSize fd.typ = .ok (sz, al) →
      offsets[j]? = some off → offsets[k]? = some off' → off + sz ≤ off' :=
  @GoLean.GoCore.structLayoutWith_disjoint

-- 570. `Ops.lean` — `tyStructLayoutAt_sizeAlign`
example :
  ∀ (p : Platform) (types : TypeEnv) (bound : Nat) (i : TypeIdx) (fields : Array FieldDef)
    {id : TypeId}, types[i]? = some (id, .struct fields) →
    (fun r => (r.2.1, r.2.2)) <$> tyStructLayoutAt p types (bound + 1) i
      = tySizeAlignAt p types (bound + 1) i :=
  @GoLean.GoCore.tyStructLayoutAt_sizeAlign

-- 571. `Ops.lean` — `tyStructLayout_ok_sizeAlign`
example :
  ∀ {p : Platform} {types : TypeEnv} {ty : Ty} {offsets : List Nat} {size align : Nat},
    tyStructLayout p types ty = .ok (offsets, size, align) →
    tySizeAlign p types ty = .ok (size, align) :=
  @GoLean.GoCore.tyStructLayout_ok_sizeAlign

-- 572. `Ops.lean` — `tyStructLayout_fields`
example :
  ∀ {p : Platform} {types : TypeEnv} {i : TypeIdx} {id : TypeId} {fields : Array FieldDef}
    {offsets : List Nat} {size align : Nat},
    types[i]? = some (id, .struct fields) →
    tyStructLayout p types (.defined i) = .ok (offsets, size, align) →
    offsets.length = fields.size ∧
    ∀ (k : Nat) (fd : FieldDef), fields[k]? = some fd →
      ∃ off sz al, offsets[k]? = some off ∧ tySizeAlign p types fd.typ = .ok (sz, al) ∧
        (al ≠ 0 → al ∣ off) ∧ off + sz ≤ size :=
  @GoLean.GoCore.tyStructLayout_fields

-- ---- RE-PIN 16 (layout follow-ups (f1)/(f2) of the r72 audit, 2026-10-07): rows 573–579
-- (`Ops.lean`). Additions to rows 1–572. ----

-- 573. `Ops.lean` — `tyStructLayout_disjoint`
example :
  ∀ {p : Platform} {types : TypeEnv} {i : TypeIdx} {id : TypeId} {fields : Array FieldDef}
    {offsets : List Nat} {size align : Nat},
    types[i]? = some (id, .struct fields) →
    tyStructLayout p types (.defined i) = .ok (offsets, size, align) →
    ∀ (j k : Nat) (fd : FieldDef) (off off' sz al : Nat), j < k →
      fields[j]? = some fd → tySizeAlign p types fd.typ = .ok (sz, al) →
      offsets[j]? = some off → offsets[k]? = some off' → off + sz ≤ off' :=
  @GoLean.GoCore.tyStructLayout_disjoint

-- 574. `Ops.lean` — `structLayoutWith_align_ge`
example :
  ∀ {fieldSize : Ty → Except Stop (Nat × Nat)} {fields : List FieldDef}
    {offset maxAlign lastOffset lastSize : Nat} {offsets : List Nat} {size align : Nat},
    structLayoutWith fieldSize fields offset maxAlign lastOffset lastSize
      = .ok (offsets, size, align) →
    maxAlign ≤ align ∧
    ∀ fd ∈ fields, ∃ sz al, fieldSize fd.typ = .ok (sz, al) ∧ al ≤ align :=
  @GoLean.GoCore.structLayoutWith_align_ge

-- 575. `Ops.lean` — `structLayoutWith_align_dvd`
example :
  ∀ {fieldSize : Ty → Except Stop (Nat × Nat)},
    (∀ t sz al, fieldSize t = .ok (sz, al) → al.isPowerOfTwo) →
    ∀ {fields : List FieldDef} {offset maxAlign lastOffset lastSize : Nat}
      {offsets : List Nat} {size align : Nat},
      maxAlign.isPowerOfTwo →
      structLayoutWith fieldSize fields offset maxAlign lastOffset lastSize
        = .ok (offsets, size, align) →
      ∀ {fd : FieldDef} {sz al : Nat}, fd ∈ fields → fieldSize fd.typ = .ok (sz, al) →
        al ∣ align :=
  @GoLean.GoCore.structLayoutWith_align_dvd

-- 576. `Ops.lean` — `structLayoutWith_size_dvd`
example :
  ∀ {fieldSize : Ty → Except Stop (Nat × Nat)} {fields : List FieldDef}
    {offset maxAlign lastOffset lastSize : Nat} {offsets : List Nat} {size align : Nat},
    0 < maxAlign →
    structLayoutWith fieldSize fields offset maxAlign lastOffset lastSize
      = .ok (offsets, size, align) →
    0 < align ∧ align ∣ size :=
  @GoLean.GoCore.structLayoutWith_size_dvd

-- 577. `Ops.lean` — `tyStructLayout_size_dvd`
example :
  ∀ {p : Platform} {types : TypeEnv} {ty : Ty} {offsets : List Nat} {size align : Nat},
    tyStructLayout p types ty = .ok (offsets, size, align) →
    0 < align ∧ align ∣ size :=
  @GoLean.GoCore.tyStructLayout_size_dvd

-- 578. `Ops.lean` — `tyStructLayout_align_dvd`
example :
  ∀ {p : Platform}, p.PowTwoAligns →
    ∀ {types : TypeEnv} {i : TypeIdx} {id : TypeId} {fields : Array FieldDef}
      {offsets : List Nat} {size align : Nat},
      types[i]? = some (id, .struct fields) →
      tyStructLayout p types (.defined i) = .ok (offsets, size, align) →
      ∀ {fd : FieldDef} {sz al : Nat}, fd ∈ fields →
        tySizeAlign p types fd.typ = .ok (sz, al) → al ∣ align :=
  @GoLean.GoCore.tyStructLayout_align_dvd

-- 579. `Ops.lean` — `gcAmd64_powTwoAligns`
example : gcAmd64.PowTwoAligns := GoLean.GoCore.gcAmd64_powTwoAligns

end GoLean.GoCore.BridgeSet
