import GoLean.GoCore.Trace
import GoLean.GoCore.ProgramTrace
import GoLean.GoCore.MultiSound
import GoLean.GoCore.Prefix

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

The set is RE-PINNED per window row; every change to this file is a changelog line
(`docs/changelog/61958f2e-WINDOW.md`), so the file's diff between two pins IS the
interface diff.

THE DEVICE'S LIMIT: definitional equality ignores binder annotations, so a drift between
an implicit `{x}` and an explicit `(x)` binder is NOT caught; nor is a changed definition
with an unchanged type (that is the semantic-equation file's job, charter row 7).

`Trace.lean` is imported explicitly: neither `ProgramTrace` nor `MultiSound` reaches it.
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

end GoLean.GoCore.BridgeSet
