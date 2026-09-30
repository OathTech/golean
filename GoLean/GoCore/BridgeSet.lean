import GoLean.GoCore.Trace
import GoLean.GoCore.ProgramTrace
import GoLean.GoCore.MultiSound
import GoLean.GoCore.Prefix
import GoLean.GoCore.Locals

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
-- or a bound local
example : ∀ {ctx : ProgramCtx} {g : UnseqGraph} {thenB : Stmt} {rest : List Stmt} {env env' : LocalEnv}
    {k : Cont} {s s' : Store},
    g.wellFormed? = none → unseqEntryCheck? g env = none →
    allocDecls ctx env s g.cells = .ok (env', s') →
    Step ctx (.exec (.unseq g thenB) env (.seq rest env k)) s
      (.next (.unseqK g thenB g.initStatus [] env' .pick (.seq rest env' k))) s' ⟨[], [], []⟩ :=
  @GoLean.GoCore.Machine.Step.unseqEnter

end GoLean.GoCore.BridgeSet
