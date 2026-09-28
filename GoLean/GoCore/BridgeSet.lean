import GoLean.GoCore.Trace
import GoLean.GoCore.ProgramTrace
import GoLean.GoCore.MultiSound

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

-- 11. `Machine.lean:824`
example : ProgramCtx → Store → FuncId → List GoValue →
    Except Stop (Func × LocalEnv × List Loc × Store × AccessTrace) :=
  @GoLean.GoCore.Machine.enterFrame

-- 12. `Machine.lean:3700`
example : List Stmt → LocalEnv → Cont → Cont :=
  @GoLean.GoCore.Machine.seqCont

-- 13. `StepFn.lean:156`
example : ProgramCtx → Store → List (TargetShape × List Expr) → LocalEnv → List Loc →
    List (GoValue × List GoValue) → Cont → Bool → Choices →
    Except Stop (Config × Store × Choices × StepLabel) :=
  @GoLean.GoCore.Machine.stepFrameExit

-- 14. `Machine.lean:3781`
example : Cont → GoValue × Cont :=
  @GoLean.GoCore.Machine.recoverResult

-- 15. `Machine.lean:901`
example : ProgramCtx → Store → FuncId → List GoValue → Choices →
    Except Stop (Result (Func × LocalEnv × List Loc × Store × AccessTrace) × Choices ×
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

-- 34. `MultiSound.lean:1707` — the pool projection: a goroutine step's event label IS
-- `stepFn`'s (trace and output verbatim; the pool's arrival picks, then the step's)
example : ∀ {ctx : ProgramCtx} {s : Store} {threads : Array Thread} {i : Nat} {ch : Choices}
    {ts' : Array Thread} {s' : Store} {ch' : Choices} {ev : StepEvent},
    stepThread ctx s threads i ch = .ok (ts', s', ch', ev) → ev.action = .privateStep →
      ev.who = i ∧ ∃ c ch₁ ps₁ c' l, threads[i]? = some (.running c none) ∧
        stepFn ctx s c ch₁ = .ok (c', s', ch', l) ∧
        ev.label = ⟨l.trace, ps₁ ++ l.picks, l.out⟩ :=
  @GoLean.GoCore.Machine.stepThread_privateStep_label

end GoLean.GoCore.BridgeSet
