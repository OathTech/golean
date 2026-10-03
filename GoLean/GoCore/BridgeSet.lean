import GoLean.GoCore.Trace
import GoLean.GoCore.ProgramTrace
import GoLean.GoCore.MultiSound
import GoLean.GoCore.Prefix
import GoLean.GoCore.Locals
import GoLean.GoCore.StringPanic

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

-- 62. `PrefixFacts.lean` — the consumption theorem's `some` half WITHOUT `appendTargetLocal`
example : ∀ {ctx : ProgramCtx} {σ : Store} {c : Config} {ch₀ : Choices} {c' : Config} {σ' : Store}
    {ch₀' : Choices} {site : ChoiceSite} {b : Nat} {tr : StepLabel},
    seqConsumption ctx σ c = some (site, b) →
    stepFn ctx σ c ch₀ = .ok (c', σ', ch₀', tr) →
    ch₀' = (Choices.consumeAt site b ch₀).2 ∧ ∀ ch : Choices,
      (Choices.consumeAt site b ch).1 = (Choices.consumeAt site b ch₀).1 →
      stepFn ctx σ c ch = .ok (c', σ', (Choices.consumeAt site b ch).2, tr) :=
  @GoLean.GoCore.Machine.stepFn_consumption_some'

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

end GoLean.GoCore.BridgeSet
