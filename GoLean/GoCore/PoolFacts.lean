import GoLean.GoCore.Multi
import GoLean.GoCore.StepFnFacts

/-!
# The relation-free pool facts (re-homed 2026-10-21, lane `core/retire-relation-1020`, fix round F1)

When the relational layer was retired from the build (the [USER] ruling of 2026-10-20; tag
`relational/last-main-2026-10-20`, `docs/ARCHIVE.md`), the module boundary was used as the proxy
for «relational», and that cut wider than the relation: the single-goroutine pool bridge and the
driver/observation vocabulary — stated and proved over the EXECUTABLE pool driver only — went
with their modules. The adversarial review of that branch walked every declaration's type and
proof body in the pre-retirement environment and found their closures reach no relational
constant (`Step`, `Steps`, `StepE`, `StepM`, `schedPick`, `StepML`, `stepFn_sound`,
`step_complete`, `step_preserves_wf*`); the raft-proofs design against the tag relies on exactly
this bridge (`execProgLoop_single`, the projections) to connect its sequential theorems to the
pool driver the CLI runs. This module re-homes them VERBATIM — statements, proofs, names,
binder shapes (the `variable` toggles of the origins are kept) — in the origins' order:

* from `MultiSound.lean` (namespace `GoLean.GoCore.Machine`): the blocked/terminal shape facts,
  the arrival-plan singleton facts, the boundary-site shapes, the single-goroutine driver lemmas
  (`stepThread_single`, `stepMulti_single`, `stepFn_abort`, `execProgLoop_aborted`,
  `execProgLoop_single`, `execProg_single_eq_execStmt`, …), `transferable`, `seqOpCount`,
  the singleton scheduler/runnable facts, `raceUpdate_single`, `singleton_pool_facts`, the
  spawn-shape facts — with `mapM_ok_length` from `MachineSound.lean`, the one lemma of that
  module they use which `StepFnFacts.lean` does not carry;
* from `PoolTrace.lean` (namespace `GoLean.Semantics.Pool`): `Result`, `front`, `unfold_driver`,
  `Run`, `run_iff`, `exists_run_iff` — the trace of the output-preserving pool driver;
* from `ProgramTrace.lean` (the same namespace): `ProgramRun`, `program_run_iff`,
  `exists_program_run_iff`, the observation vocabulary `Observation`/`observationOf`,
  `fuel_is_not_observation`, `refusal_is_not_observation`, `observation_iff`.

NOT re-homed, because their closures reach the relation: `stepMulti_sound`, `stepM_complete`,
`stepThreadInto_sound`, `stepMulti_of_inner`, `schedPick_cur`, `schedPick_of_boundary`,
`step_spawnPos_elim`, `abort?_none_of_stepE` (MultiSound); `PoolSteps`, `Run.success_reaches`
(PoolTrace). The relation-free kept set was computed, not chosen: every candidate whose closure
(types and proof bodies, generated auxiliaries judged by their parent) left the tip's
environment plus the candidates themselves was dropped, to a fixpoint. The sequential-to-pool
PROJECTIONS of `PoolProjection.lean`, relation-free in full, are restored under their own name
(they import `Prefix.lean`, which this module sits below).
-/

set_option maxRecDepth 8192
-- The unused-simp-arg linter misfires on the shared multi-branch simp
-- sets (an argument unused in one branch is load-bearing in another) —
-- the MachineSound sweeps' standing rationale, file-wide here.
set_option linter.unusedSimpArgs false

namespace GoLean.GoCore.Machine

-- B7 (2026-09-17): the program context is the first explicit parameter of
-- every definition below that reads it; theorems take it implicitly
-- (`variable {ctx}` toggles).
variable (ctx : ProgramCtx)

open GoLean

variable {ctx}

/-! `mapM_ok_length` came with the kept facts from `MachineSound.lean` (the only MachineSound lemma they use
that `StepFnFacts.lean` does not carry); unchanged. -/
/-- `mapM` over `Except` preserves length on success. -/
theorem mapM_ok_length {α β : Type} {f : α → Except Stop β}
    {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil =>
      simp only [List.mapM_nil, pure_eq_ok, Except.ok.injEq] at h
      subst h
      rfl
  | cons x xs ih =>
      rw [List.mapM_cons] at h
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨y, hy, ys', hys', rfl⟩ := h
      simp [ih hys']
/-! ## Small computation lemmas -/

@[simp] theorem isBlockedConfig_next {k : Cont} : isBlockedConfig (.next k) = false := rfl
@[simp] theorem isBlockedConfig_panicking {chain : List PanicEntry} {k : Cont} :
    isBlockedConfig (.panicking chain k) = false := rfl

theorem recvSideWaiters_singleton {t : Thread} {loc : Loc} :
    recvSideWaiters #[t] 0 loc = [] := rfl

theorem sendSideWaiters_singleton {t : Thread} {loc : Loc} :
    sendSideWaiters #[t] 0 loc = [] := rfl

/-- With no OTHER goroutines there is never a parked partner: the
arrival plan is a pure no-op — its waiter scans short-circuit before
any fallible helper runs. The conservation theorem's hinge. -/
theorem chanArrivalPlan_singleton {s : Store} {t : Thread}
    {op : ChanStOp} {vs : List GoValue} {env : LocalEnv} {k : Cont} :
    chanArrivalPlan ctx s #[t] 0 op vs env k = .ok none := by
  unfold chanArrivalPlan
  match op, vs with
  | .send elem, [] => rfl
  | .send elem, [x] => rfl
  | .send elem, [chv, vv] =>
      cases hcl : chanValueLoc chv with
      | none => simp [hcl]
      | some loc => simp [hcl, recvSideWaiters_singleton]
  | .send elem, x :: y :: z :: rest => rfl
  | .recv targets elem, [] => rfl
  | .recv targets elem, [chv] =>
      cases hcl : chanValueLoc chv with
      | none => simp [hcl]
      | some loc => simp [hcl, sendSideWaiters_singleton]
  | .recv targets elem, x :: y :: rest => rfl
  | .close, _ => rfl

@[inherit_doc chanArrivalPlan_singleton]
theorem selectArrivalCases_singleton {s : Store} {t : Thread}
    {clauses : List (SelectClauseHead × Stmt)} {vs : List GoValue}
    {env : LocalEnv} {k : Cont} :
    selectArrivalCases s #[t] 0 clauses vs env k = .ok .cellPath := by
  have hsw : ∀ sides : List (Option (Bool × Loc)),
      sidesHaveWaiters #[t] 0 sides = false := by
    intro sides
    induction sides with
    | nil => rfl
    | cons sd rest ih =>
        match sd with
        | none => simpa [sidesHaveWaiters] using ih
        | some (isSend, loc) =>
            cases isSend <;>
              simp [sidesHaveWaiters, recvSideWaiters_singleton,
                sendSideWaiters_singleton, ih]
  unfold selectArrivalCases
  cases hsc : selectClauseChans clauses vs with
  | none => rfl
  | some sides =>
      dsimp only
      simp only [hsw, Bool.not_false, reduceIte]
      rfl

@[inherit_doc chanArrivalPlan_singleton]
theorem arrivalCases_singleton {s : Store} {t : Thread} {c' : Config} :
    arrivalCases ctx s #[t] 0 c' = .ok .cellPath := by
  unfold arrivalCases
  split
  · rw [show chanArrivalPlan ctx s #[t] 0 _ _ _ _ = .ok none
      from chanArrivalPlan_singleton]
    rfl
  · exact selectArrivalCases_singleton
  · rfl

@[inherit_doc chanArrivalPlan_singleton]
theorem arrivalPlan_singleton {s : Store} {t : Thread} {c' : Config} {ch : Choices} :
    arrivalPlan ctx s #[t] 0 c' ch = .ok (none, ch, []) := by
  unfold arrivalPlan
  rw [show arrivalCases ctx s #[t] 0 c' = .ok .cellPath from arrivalCases_singleton]
  rfl

/-- Wrapper computations of `arrivalPlan` from a pure analysis (the
proofs' bridge between `arrivalCases` — the relation's carrier — and
the consuming wrapper the executable calls). -/
theorem arrivalPlan_of_cellPath {s : Store} {threads : Array Thread}
    {i : Nat} {c : Config} {ch : Choices}
    (h : arrivalCases ctx s threads i c = .ok .cellPath) :
    arrivalPlan ctx s threads i c ch = .ok (none, ch, []) := by
  unfold arrivalPlan
  rw [h]
  rfl

@[inherit_doc arrivalPlan_of_cellPath]
theorem arrivalPlan_of_single {s : Store} {threads : Array Thread}
    {i : Nat} {c bc : Config} {cs : List (Nat × PairTarget)} {ch : Choices}
    (h : arrivalCases ctx s threads i c = .ok (.single bc cs)) :
    arrivalPlan ctx s threads i c ch = .ok (some (.pair bc cs), ch, []) := by
  unfold arrivalPlan
  rw [h]
  rfl

@[inherit_doc arrivalPlan_of_cellPath]
theorem arrivalPlan_of_error {s : Store} {threads : Array Thread}
    {i : Nat} {c : Config} {e : Stop} {ch : Choices}
    (h : arrivalCases ctx s threads i c = .error e) :
    arrivalPlan ctx s threads i c ch = .error e := by
  unfold arrivalPlan
  rw [h]
  rfl

/-- No configuration SHAPE consults the `postOp` site: a completed op's
site is the goroutine's flag (C5). -/
theorem Config.boundarySite_ne_postOp (c : Config) : c.boundarySite ≠ .postOp := by
  unfold Config.boundarySite
  split <;> simp

/-- A postOp boundary site is exactly an open `postOp` flag. -/
theorem Thread.boundarySite_postOp_shape {t : Thread}
    (h : t.boundarySite = .postOp) :
    ∃ c, t = .running c (some .postOp) := by
  cases t with
  | aborted msg => simp [Thread.boundarySite] at h
  | running c b =>
    cases b with
    | some site =>
      simp only [Thread.boundarySite] at h
      subst h
      exact ⟨c, rfl⟩
    | none => exact absurd h (Config.boundarySite_ne_postOp c)

/-- A backEdge boundary site's goroutine is RUNNABLE (stage D: the loop
re-entry shapes are neither done nor blocked — what puts the current
goroutine at slot 0 of its own menu; a flagged goroutine is runnable
outright). -/
theorem Thread.boundarySite_backEdge_runnable {s : Store} {t : Thread}
    (h : t.boundarySite = .backEdge) :
    threadRunnable ctx s t = true := by
  cases t with
  | aborted msg => simp [Thread.boundarySite] at h
  | running c b =>
    cases b with
    | some site => rfl
    | none =>
      simp only [Thread.boundarySite] at h
      simp only [threadRunnable]
      unfold Config.boundarySite at h
      -- Order matters: `cases h` on the MATCHING arms' `refl` proof
      -- succeeds vacuously and leaves the goal, so the computation goes
      -- first.
      split at h <;>
        first
        | (simp [Config.isTerminal, isBlockedConfig]; done)
        | cases h

/-- A `selectApplyPlan` extraction pins the configuration's shape (the
`spawnedCont_shape` mold). -/
theorem selectApplyPlan_shape {c : Config} {v : GoValue}
    {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt}
    {done : List GoValue} {env : LocalEnv} {k' : Cont}
    (h : selectApplyPlan c = some (v, clauses, default?, done, env, k')) :
    c = .retV v (.selectOpsK clauses default? done [] env k') := by
  match c, h with
  | .retV v' (.selectOpsK cl' d' dn' [] env' k''), h =>
      simp only [selectApplyPlan, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      rfl

/-- `stepFn`'s select-apply arm, inverted: a successful sequential
step at the apply position is `applySelect`'s success (with SOME
emitted commit identity, which the arm projects away) or its
defensive panic wrapping. The bridge the conservation and
completeness proofs cross at the pool's select interception. -/
theorem stepFn_selectApply_inv {σ : Store} {v : GoValue}
    {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt}
    {done : List GoValue} {env : LocalEnv} {k' : Cont}
    {ch : Choices} {c' : Config} {σ' : Store} {ch' : Choices} {tr : StepLabel}
    (h : stepFn ctx σ (.retV v (.selectOpsK clauses default? done [] env k')) ch
      = .ok (c', σ', ch', tr)) :
    (∃ cl?, applySelect ctx σ clauses default? ((v :: done).reverse) env k' ch
        = .ok (c', σ', ch', tr.picks, cl?, tr.trace) ∧ tr.out = [])
      ∨ (∃ msg, applySelect ctx σ clauses default? ((v :: done).reverse) env k' ch
          = .error (.panic msg)
          ∧ c' = .panicking [panicEntry msg] k'
          ∧ σ' = σ ∧ ch' = ch ∧ tr = ⟨[], [], []⟩) := by
  unfold stepFn at h
  dsimp only at h
  cases happ : applySelect ctx σ clauses default? ((v :: done).reverse) env k' ch with
  | ok r =>
      obtain ⟨c₂, s₂, ch₂, ps₂, cl₂, tr₂⟩ := r
      rw [happ] at h
      simp only [toResult_ok, Bind.bind, Except.bind, pure_eq_ok, deliverS_ok,
        Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact .inl ⟨cl₂, rfl, rfl⟩
  | error e =>
      rw [happ] at h
      cases_stop e <;>
        simp only [toResult_panic, toResult_refusal, toResult_fatal, toResult_deadlock,
          toResult_raceDetected, toResult_fuelOut, Bind.bind, Except.bind, pure_eq_ok,
          deliverS_panic, List.nil_append, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
      case panic msg =>
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact .inr ⟨msg, rfl, rfl, rfl, rfl, rfl⟩

/-- The one-thread `stepThread` is `stepFn`, results re-wrapped with a
step event attached and the successor flagged by the post-op boundary
rule (the arrival plan is a pure no-op with no other goroutines —
`arrivalPlan_singleton`; the select interception path lands on
`stepFn`'s own result — one consuming definition, `applySelect`, whose
commit identity the sequential arm projects away). Stated away from the
shapes the pool handles ITSELF (a park, a spawn position, the abort). -/
theorem stepThread_single {σ : Store} {c : Config} {ch : Choices}
    (hbl : isBlockedConfig c = false)
    (hsp : spawnPlan c = none)
    (hab : c.abort? = none) :
    ∃ ev, stepThread ctx σ #[.running c none] 0 ch
      = (stepFn ctx σ c ch).map (fun r => (#[Thread.afterStep σ c r.1], r.2.1, r.2.2.1, ev)) := by
  unfold stepThread
  have h0 : (#[Thread.running c none] : Array Thread)[0]? = some (.running c none) := rfl
  rw [h0]
  simp only [hbl, Bool.false_eq_true, reduceIte, hab, hsp]
  rw [show arrivalPlan ctx σ #[Thread.running c none] 0 c ch = .ok (none, ch, [])
    from arrivalPlan_singleton]
  simp only [Bind.bind, Except.bind]
  cases hselp : selectApplyPlan c with
  | none =>
      -- The event's trace is the step's (S2a): choose it after the step.
      cases hstep : stepFn ctx σ c ch with
      | error e => exact ⟨⟨0, .privateStep, ⟨[], [], []⟩⟩, rfl⟩
      | ok r =>
          obtain ⟨c', s', ch₁, l⟩ := r
          exact ⟨⟨0, .privateStep, { l with picks := [] ++ l.picks }⟩, by simp [Functor.map, Except.map]⟩
  | some p =>
      obtain ⟨v, clauses, default?, done, env, k'⟩ := p
      obtain rfl := selectApplyPlan_shape hselp
      dsimp only
      cases happly : applySelect ctx σ clauses default?
          ((v :: done).reverse) env k' ch with
      | ok r =>
          obtain ⟨c', s', ch₂, ps, cl?, tr⟩ := r
          have hfn : stepFn ctx σ
              (.retV v (.selectOpsK clauses default? done [] env k')) ch
              = .ok (c', s', ch₂, ⟨tr, ps, []⟩) := by
            unfold stepFn
            dsimp only
            rw [happly]
            rfl
          refine ⟨⟨0, match cl? with
            | some cl => .selectCommit cl
            | none => .selectPass, ⟨tr, [] ++ ps, []⟩⟩, ?_⟩
          rw [hfn]
          simp only [Functor.map, Except.map]
          cases cl? <;> rfl
      | error e =>
          have hfn : stepFn ctx σ
              (.retV v (.selectOpsK clauses default? done [] env k')) ch
              = (match e with
                 | .panic msg =>
                     .ok (.panicking [panicEntry msg] k', σ, ch, ⟨[], [], []⟩)
                 | e => .error e) := by
            unfold stepFn
            dsimp only
            simp only [happly]
            cases_stop e <;> rfl
          refine ⟨⟨0, .selectPass, ⟨[], [], []⟩⟩, ?_⟩
          rw [hfn]
          cases_stop e <;> first | rfl | simp [Functor.map, Except.map]

theorem runnableIdxs_singleton {σ : Store} {t : Thread}
    (h : threadRunnable ctx σ t = true) :
    runnableIdxs ctx σ #[t] = [0] := by
  simp [runnableIdxs, h]

/-- A singleton pool's slot menu is `[0]` at EVERY site (postOp's
issuer-first reordering is invisible with one goroutine). -/
theorem schedSlots_singleton {σ : Store} {t : Thread}
    {site : ChoiceSite} (h : threadRunnable ctx σ t = true) :
    schedSlots ctx σ #[t] 0 site = [0] := by
  unfold schedSlots
  cases site <;>
    simp [runnableIdxs_singleton h]

/-- **The one-thread pool step is the sequential step** (the D2a
consumption rule at work: a single runnable goroutine never consumes a
scheduler choice — at the L1 site AND at stage C's postOp site, both by
the uniform bound-≤-1 rule of `Choices.consumeAt` — and with no partner
the intercept never fires); the successor carries the boundary the step
opened (`Thread.afterStep`, C5). -/
theorem stepMulti_single {σ : Store} {c : Config} {ch : Choices}
    (hbl : isBlockedConfig c = false)
    (hsp : spawnPlan c = none)
    (hab : c.abort? = none)
    (hdone : c.isTerminal = false) :
    ∃ ev, stepMulti ctx ⟨#[.running c none], σ, 0⟩ ch
      = (stepFn ctx σ c ch).map (fun r => (⟨#[Thread.afterStep σ c r.1], r.2.1, 0⟩, r.2.2.1, ev)) := by
  have hrun : threadRunnable ctx σ (.running c none) = true := by
    simp [threadRunnable, hdone, hbl]
  obtain ⟨ev, hst⟩ := stepThread_single (σ := σ) (ch := ch) hbl hsp hab
  refine ⟨ev, ?_⟩
  have hinto : stepThreadInto ctx ⟨#[.running c none], σ, 0⟩ 0 ch
      = (stepFn ctx σ c ch).map (fun r => (⟨#[Thread.afterStep σ c r.1], r.2.1, 0⟩, r.2.2.1, ev)) := by
    unfold stepThreadInto
    show (stepThread ctx σ #[.running c none] 0 ch).bind _ = _
    rw [hst]
    cases stepFn ctx σ c ch <;>
      simp [Bind.bind, Except.bind, Functor.map, Except.map]
  unfold stepMulti
  have h0 : (#[Thread.running c none] : Array Thread)[0]? = some (.running c none) := rfl
  simp only [h0]
  by_cases hb : Thread.atBoundary (.running c none) = true
  · simp only [hb, reduceIte]
    rw [show schedSlots ctx σ #[Thread.running c none] 0 (Thread.boundarySite (.running c none)) = [0]
      from schedSlots_singleton hrun]
    dsimp only
    rw [show Choices.consumeAtE (Thread.boundarySite (.running c none)) [0].length ch = (0, ch, [])
      from Choices.consumeAtE_le_one (by simp)]
    simp only [List.getElem?_cons_zero]
    simp only [Bind.bind, Except.bind]
    rw [hinto]
    cases hstep : stepFn ctx σ c ch with
    | error e => simp [Except.map]
    | ok r =>
        obtain ⟨c', s', ch₂, tr⟩ := r
        simp [Except.map]
  · simp only [Bool.not_eq_true] at hb
    simp only [hb, Bool.false_eq_true, reduceIte]
    exact hinto

/-- **The one-thread pool's boundary CLEAR** (C5): a flagged singleton
goroutine's pool step clears its flag and nothing else — no scheduler
consumption (the menu is `[0]`), no state change, the `.opDoneStrip`
event. The step the sequential driver does not take. -/
theorem stepMulti_flagged_single {σ : Store} {c : Config} {ch : Choices}
    {site : ChoiceSite} :
    stepMulti ctx ⟨#[.running c (some site)], σ, 0⟩ ch
      = .ok (⟨#[.running c none], σ, 0⟩, ch, ⟨0, .opDoneStrip, [], [], []⟩) := by
  have hrun : threadRunnable ctx σ (.running c (some site)) = true := rfl
  unfold stepMulti
  have h0 : (#[Thread.running c (some site)] : Array Thread)[0]?
      = some (.running c (some site)) := rfl
  simp only [h0]
  simp only [Thread.atBoundary, reduceIte]
  rw [show schedSlots ctx σ #[Thread.running c (some site)] 0
      (Thread.boundarySite (.running c (some site))) = [0]
    from schedSlots_singleton hrun]
  dsimp only
  rw [show Choices.consumeAtE (Thread.boundarySite (.running c (some site))) [0].length ch
      = (0, ch, [])
    from Choices.consumeAtE_le_one (by simp)]
  rfl

/-- The sequential machine's ABORT (B4): at an unrecovered chain at
`.stop`, `stepFn` raises the rendered `panic` terminal (or `abortMsg`'s
refusal) under the stream's `repanicCollapse` pick (`abortConsult`,
landing chunk L3 — the forced 0 at every abort outside the
recovered-equal shape). -/
theorem stepFn_abort {σ : Store} {c : Config} {ch : Choices}
    {first : PanicEntry} {rest : List PanicEntry}
    (hab : c.abort? = some (first, rest)) :
    stepFn ctx σ c ch = (do let msg ← abortMsg ctx first rest (abortConsult first rest ch).1
                            throw (.panic msg)) := by
  -- Unit 6b: the abort is a SETTLED chain at `.stop` (`Config.abort?_some_iff`);
  -- the `.stop` arm's helper takes its abort branch there.
  obtain ⟨rfl, hs⟩ := Config.abort?_some_iff.mp hab
  simp only [stepFn, stepPanicStop, hs]

/-- An abort configuration is not parked. -/
theorem isBlockedConfig_of_abort {c : Config} {first : PanicEntry}
    {rest : List PanicEntry} (hab : c.abort? = some (first, rest)) :
    isBlockedConfig c = false := by
  match c, hab with
  | .panicking (f :: r) .stop, _ => rfl

/-- An abort configuration is not a terminal. -/
theorem isTerminal_of_abort {c : Config} {first : PanicEntry}
    {rest : List PanicEntry} (hab : c.abort? = some (first, rest)) :
    c.isTerminal = false := by
  match c, hab with
  | .panicking (f :: r) .stop, _ => rfl

/-- An abort configuration is not at a boundary shape. -/
theorem atBoundary_of_abort {c : Config} {first : PanicEntry}
    {rest : List PanicEntry} (hab : c.abort? = some (first, rest)) :
    c.atBoundary = false := by
  match c, hab with
  | .panicking (f :: r) .stop, _ => rfl

/-- **The one-thread pool's ABORT** (B4): the singleton goroutine at an
unrecovered chain at `.stop` renders into its tombstone in one pool step
(or the render's refusal propagates) — the step the sequential machine
takes as its `panic` terminal (`stepFn_abort`) — under the same
`repanicCollapse` pick, the popped stream returned and the pick recorded
in the event (`consumeAtE`; `[]` at bound 1). -/
theorem stepMulti_abort_single {σ : Store} {c : Config} {ch : Choices}
    {first : PanicEntry} {rest : List PanicEntry}
    (hab : c.abort? = some (first, rest)) :
    stepMulti ctx ⟨#[.running c none], σ, 0⟩ ch
      = (abortMsg ctx first rest
            (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1).map
          (fun msg => (⟨#[.aborted msg], σ, 0⟩,
            (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).2.1,
            ⟨0, .aborted,
              ⟨[], (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).2.2, []⟩⟩)) := by
  unfold stepMulti
  have h0 : (#[Thread.running c none] : Array Thread)[0]? = some (.running c none) := rfl
  simp only [h0]
  simp only [Thread.atBoundary, atBoundary_of_abort hab, Bool.false_eq_true, reduceIte]
  unfold stepThreadInto stepThread
  rw [h0]
  simp only [isBlockedConfig_of_abort hab, Bool.false_eq_true, reduceIte, hab]
  cases abortMsg ctx first rest
      (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1 <;>
    simp [Bind.bind, Except.bind, Except.map]

/-! ## The signal at `.stop` (B4; audit fix R4, 2026-09-05)

Since B4 a signal that reaches the empty continuation is a REFUSAL, not
a `returned/broke/continued` completion: `transferable` moved from the
deleted `ExecOutcome` to `Store × Choices`, so
`execProg_single_eq_execStmt` is silent on runs that used to end there.
Unreachable from every Program driver (each seeds its subject under a
barrier `.frame`), so nothing observable changed — and the two drivers
agree on the shape anyway: both raise `signalRefusal sg .stop`, the
sequential machine at its step, the one-goroutine pool at its
`stepFn` call (no boundary, no park, no abort, no spawn, no arrival
on a `.signal` configuration). -/

theorem stepFn_signal_stop {σ : Store} {sg : Signal} {ch : Choices} :
    stepFn ctx σ (.signal sg .stop) ch = .error (signalRefusal sg .stop) := by
  cases sg <;> rfl

theorem stepMulti_signal_stop_single {σ : Store} {sg : Signal} {ch : Choices} :
    stepMulti ctx ⟨#[.running (.signal sg .stop) none], σ, 0⟩ ch
      = .error (signalRefusal sg .stop) := by
  cases sg <;> rfl

/-! ## stepFn ctx shape inversions (the spawn/terminal refusals) -/

/-- A completed spawn position never steps sequentially — `stepFn`
fails closed there with an `.unsupported`/`.stuck` refusal (exactly
the result classes the conservation transfer does NOT claim). -/
theorem spawnPlan_stepFn_refuses {c : Config} {σ : Store}
    {ch : Choices} {p : GoValue × List GoValue × Cont}
    (h : spawnPlan c = some p) :
    match stepFn ctx σ c ch with
    | .error (.unsupported _) => True
    | .error (.stuck _) => True
    | _ => False := by
  match c, h with
  | .retV cv (.goCalleeK [] env k), h =>
      by_cases hd : deferrableCallee cv = true <;>
        simp [stepFn, hd, throw, throwThe, MonadExceptOf.throw]
  | .retV v (.goArgsK cv vals [] env k), h =>
      simp [stepFn, throw, throwThe, MonadExceptOf.throw]

variable (ctx)
/-! ## Sequential conservation: the loop-level transfer (D9(a)) -/

/-- The result classes the conservation transfer claims: completions,
fuel exhaustion, and panic aborts — everything a designated sequential
statement's meaning consumes. The two excluded classes are exactly
where the pool may legitimately differ from the sequential machine's
refusals: `.deadlock` and the fail-closed
`.unsupported`/`.stuck`/`.internal` diagnostics (a spawn position is
refused sequentially and forked by the pool).

Which theorem needs which exclusion (S2 audit response — the original
note blurred them): the `.deadlock` exclusion is needed by the LOOP
lemma `execProgLoop_single`, which quantifies ARBITRARY configurations
— an artificial wake-ready blocked seed would resume in the pool where
the sequential driver classifies immediately. The headline
`execProg_single_eq_execStmt` seeds `.exec prog env .stop` (never a
blocked config), so for it the exclusion is a currently-unclaimed
strengthening opportunity (it would need a per-step
blocked-not-wake-ready invariant carried through the induction);
deadlock preservation under the driver swap is validated by the
corpus's 12 pinned deadlock cases instead. -/
def transferable : Except Stop (Store × Choices) → Prop
  | .ok _ => True
  | .error .fuelOut => True
  | .error (.panic _) => True
  | _ => False

variable {ctx}
/-- The race detector is DEFINITIONALLY inert on one-goroutine pools
(`raceUpdate`'s first branch): a single goroutine cannot race with
itself. The conservation proof's detector hinge — sequential runs
thread the `RaceState` through untouched. -/
theorem raceUpdate_single {t : Thread}
    {σ' : Store} {i : Nat} {ev : StepEvent} {rs : RaceState} :
    raceUpdate ev ⟨#[t], σ', i⟩ rs = .ok rs := by
  simp [raceUpdate]

/-- The singleton-pool projections of a mid-run (non-terminal,
non-blocked) configuration. -/
theorem singleton_pool_facts {σ : Store} {c : Config}
    (h1 : c ≠ .next .stop)
    (h6 : ∀ a b k, c ≠ .blockedSend a b k)
    (h7 : ∀ a b e env k, c ≠ .blockedRecv a b e env k)
    (h8 : ∀ cl env k, c ≠ .blockedSelect cl env k)
    (h9 : ∀ op loc env k, c ≠ .blockedSync op loc env k) :
    MultiConfig.panicMsg? ⟨#[.running c none], σ, 0⟩ = none
      ∧ MultiConfig.mainOutcome? ⟨#[.running c none], σ, 0⟩ = none
      ∧ c.isTerminal = false ∧ isBlockedConfig c = false := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · unfold MultiConfig.mainOutcome?
    have h0 : ((⟨#[.running c none], σ, 0⟩ : MultiConfig).threads[0]? : Option Thread)
        = some (.running c none) := rfl
    rw [h0]
    split <;> simp_all
  · unfold Config.isTerminal
    split <;> simp_all
  · unfold isBlockedConfig
    split <;> try simp_all
    · exact (h7 _ _ _ _ _ rfl rfl rfl rfl rfl)
    · exact (h9 _ _ _ _ rfl rfl rfl rfl)

variable (ctx)
/-- **The op count** (C5): the number of registry-op completions along a
sequential run of at most `fuel` steps from `c` — each one a boundary
CLEAR the one-goroutine pool takes and the sequential machine does not
(`Config.afterStepFlag`). Zero at a terminal, a park, or a refusing /
aborting step (no boundary opened). -/
def seqOpCount : Nat → Store → Config → Choices → Nat
  | 0, _, _, _ => 0
  | fuel + 1, σ, c, ch =>
      if c.isTerminal || isBlockedConfig c then 0
      else
        match stepFn ctx σ c ch with
        | .error _ => 0
        | .ok (c', σ', ch', _) =>
            (if (c.afterStepFlag σ c').isSome then 1 else 0) + seqOpCount fuel σ' c' ch'

variable {ctx}
/-- A tombstoned singleton pool is the panic terminal at every fuel. -/
theorem execProgLoop_aborted {fuel : Nat} {σ : Store} {msg : String}
    {rs : RaceState} {ch : Choices} :
    execProgLoop ctx fuel ⟨#[.aborted msg], σ, 0⟩ rs ch = .error (.panic msg) := by
  unfold execProgLoop
  rfl

/-- **The conservation transfer, loop level** (restated at G-C5 with the
op count): every sequential result in the `transferable` classes is the
singleton pool's result verbatim — same outcome, same final state, same
leftover stream — at the pool's fuel `fuel + seqOpCount fuel σ c ch`:
the pool spends exactly one extra step per completed registry op (the
boundary clear, `stepMulti_flagged_single`) and matches the sequential
machine step for step otherwise (`stepMulti_single`,
`stepMulti_abort_single`). -/
theorem execProgLoop_single :
    ∀ {fuel : Nat} {σ : Store} {c : Config} {ch : Choices}
      {rs : RaceState}
      {r : Except Stop (Store × Choices)},
      execStmtLoop ctx fuel σ c ch = r → transferable r →
      execProgLoop ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch = r := by
  intro fuel
  induction fuel with
  | zero =>
    intro σ c ch rs r hr htr
    unfold execStmtLoop at hr
    split at hr
    · subst hr; rfl
    · subst hr; simp [transferable, throw, throwThe, MonadExceptOf.throw] at htr
    · subst hr; simp [transferable, throw, throwThe, MonadExceptOf.throw] at htr
    · subst hr; simp [transferable, throw, throwThe, MonadExceptOf.throw] at htr
    · subst hr; simp [transferable, throw, throwThe, MonadExceptOf.throw] at htr
    · rename_i harm1 harm6 harm7 harm8 harm9
      subst hr
      obtain ⟨hp, hm, hd, hb⟩ := singleton_pool_facts
        (σ := σ) harm1 harm6 harm7 harm8 harm9
      have hrun : threadRunnable ctx σ (.running c none) = true := by
        simp [threadRunnable, hd, hb]
      simp only [seqOpCount, Nat.add_zero]
      unfold execProgLoop
      simp [hp, hm, runnableIdxs_singleton hrun]
  | succ n ih =>
    intro σ c ch rs r hr htr
    unfold execStmtLoop at hr
    split at hr
    · subst hr
      simp only [seqOpCount, Config.isTerminal, Bool.true_or, ↓reduceIte, Nat.add_zero]
      rfl
    · subst hr; simp [transferable, throw, throwThe, MonadExceptOf.throw] at htr
    · subst hr; simp [transferable, throw, throwThe, MonadExceptOf.throw] at htr
    · subst hr; simp [transferable, throw, throwThe, MonadExceptOf.throw] at htr
    · subst hr; simp [transferable, throw, throwThe, MonadExceptOf.throw] at htr
    · rename_i harm1 harm6 harm7 harm8 harm9
      obtain ⟨hp, hm, hd, hb⟩ := singleton_pool_facts
        (σ := σ) harm1 harm6 harm7 harm8 harm9
      have hrun : threadRunnable ctx σ (.running c none) = true := by
        simp [threadRunnable, hd, hb]
      simp only [Bind.bind, Except.bind] at hr
      have hcnt : seqOpCount ctx (n + 1) σ c ch
          = (match stepFn ctx σ c ch with
             | .error _ => 0
             | .ok (c', σ', ch', _) =>
                 (if (c.afterStepFlag σ c').isSome then 1 else 0) + seqOpCount ctx n σ' c' ch') := by
        simp only [seqOpCount, hd, hb, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
      cases hsp : spawnPlan c with
      | some p =>
          -- A spawn position refuses sequentially: not transferable.
          have hcls := spawnPlan_stepFn_refuses (ctx := ctx) (σ := σ) (ch := ch) hsp
          cases hstep : stepFn ctx σ c ch with
          | ok r₂ => rw [hstep] at hcls; simp at hcls
          | error e =>
              rw [hstep] at hr
              rw [hstep] at hcls
              subst hr
              cases_stop e <;> simp_all [transferable]
      | none =>
      cases hab : c.abort? with
      | some p =>
          -- THE ABORT: the sequential machine raises the panic terminal;
          -- the pool tombstones the goroutine and classifies it at the
          -- next loop head — one step on both sides.
          obtain ⟨first, rest⟩ := p
          rw [stepFn_abort hab] at hr
          have hmulti := stepMulti_abort_single (ctx := ctx) (σ := σ) (ch := ch) hab
          -- Both drivers draw the same `repanicCollapse` pick (the pool's
          -- record-emitting consult projects onto the sequential one).
          have hpick : (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1
              = (abortConsult first rest ch).1 := by
            unfold abortConsult
            rw [← Choices.consumeAtE_fst_snd]
          rw [hpick] at hmulti
          rw [hcnt, stepFn_abort hab]
          cases hmsg : abortMsg ctx first rest (abortConsult first rest ch).1 with
          | error e =>
              rw [hmsg] at hr hmulti
              simp only [Bind.bind, Except.bind] at hr
              subst hr
              simp only [Bind.bind, Except.bind, Nat.add_zero]
              unfold execProgLoop
              simp [hp, hm, runnableIdxs_singleton hrun, hmulti, Bind.bind, Except.bind,
                Except.map]
          | ok msg =>
              rw [hmsg] at hr hmulti
              simp only [Bind.bind, Except.bind] at hr
              subst hr
              simp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
                Nat.add_zero]
              unfold execProgLoop
              simp [hp, hm, runnableIdxs_singleton hrun, hmulti, Bind.bind, Except.bind,
                Except.map, raceUpdate_single, execProgLoop_aborted]
      | none =>
          obtain ⟨ev, hmulti⟩ :=
            stepMulti_single (σ := σ) (ch := ch) hb hsp hab hd
          rw [hcnt]
          cases hstep : stepFn ctx σ c ch with
          | error e =>
              rw [hstep] at hr
              subst hr
              rw [hstep] at hmulti
              simp only [Except.map] at hmulti
              simp only [Nat.add_zero]
              unfold execProgLoop
              simp [hp, hm, runnableIdxs_singleton hrun, hmulti,
                Bind.bind, Except.bind]
          | ok r₂ =>
              obtain ⟨c₂, σ₂, ch₂, tr₂⟩ := r₂
              rw [hstep] at hr
              rw [hstep] at hmulti
              simp only [Except.map] at hmulti
              have hrec := ih (rs := rs) hr htr
              simp only
              cases hflag : c.afterStepFlag σ c₂ with
              | none =>
                  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
                  rw [show n + 1 + seqOpCount ctx n σ₂ c₂ ch₂ = (n + seqOpCount ctx n σ₂ c₂ ch₂) + 1
                    from by omega]
                  unfold execProgLoop
                  simp only [Thread.afterStep, hflag] at hmulti
                  simp [hp, hm, runnableIdxs_singleton hrun, hmulti,
                    Bind.bind, Except.bind, raceUpdate_single, hrec]
              | some site =>
                  simp only [Option.isSome_some, ↓reduceIte]
                  rw [show n + 1 + (1 + seqOpCount ctx n σ₂ c₂ ch₂)
                      = ((n + seqOpCount ctx n σ₂ c₂ ch₂) + 1) + 1 from by omega]
                  unfold execProgLoop
                  simp only [Thread.afterStep, hflag] at hmulti
                  simp only [hp, hm, runnableIdxs_singleton hrun, hmulti,
                    Bind.bind, Except.bind, raceUpdate_single]
                  -- the boundary CLEAR: one more pool step, no consumption
                  have hrun₂ : threadRunnable ctx σ₂ (.running c₂ (some site)) = true := rfl
                  unfold execProgLoop
                  simp [runnableIdxs_singleton hrun₂, stepMulti_flagged_single,
                    Bind.bind, Except.bind, raceUpdate_single, hrec,
                    MultiConfig.mainOutcome?, MultiConfig.panicMsg?]

/-- **`execProg_single_eq_execStmt` — THE sequential-conservation
theorem** (machine-shape note §7; D9(a); restated at G-C5 with the op
count): for every program, every fuel, every stream, a sequential
`execStmt` result in the transferable classes (completion at the
terminal, fuel exhaustion, panic abort) IS the pool driver's `execProg`
result, verbatim — same outcome, same final state, same leftover stream —
at the pool's fuel `fuel + seqOpCount …`: the one-goroutine pool spends
one boundary-clear step per completed registry op (C5: the strip is a
POOL step; the sequential machine has no flag), and matches the
sequential machine step for step otherwise. This is the transfer lemma
that keeps every designated sequential statement valid unrestated on
the pool carrier (D9(a)): a sequential `GoSpec`'s runs and the
concurrent carrier's runs coincide on single-goroutine programs. The
differential's pool driver (`runProgramPoolIntsM`) runs at the same
fuel as before C5 — the op count is a fuel shift IN THIS THEOREM, not in
any baseline. -/
theorem execProg_single_eq_execStmt {fuel : Nat} {env : LocalEnv}
    {σ : Store} {ch : Choices} {prog : Stmt}
    {r : Except Stop (Store × Choices)}
    (hr : execStmt ctx fuel env σ ch prog = r) (htr : transferable r) :
    execProg ctx (fuel + seqOpCount ctx fuel σ (.exec prog env .stop) ch) env σ ch prog = r :=
  execProgLoop_single hr htr

/-! ## Correspondence: `stepMulti` instantiates `StepM` -/

/-- A successful spawn's PARENT successor is `.next k` (BUG-040: the
fork's completion is a registry op; the pool flags it `l1Sched` —
`Thread.afterStep` — preserving the spawn boundary's shipped default;
the flag clears at the next step). -/
theorem spawnStep_shape {s : Store} {cv : GoValue} {args : List GoValue}
    {k : Cont} {ch : Choices} {p c : Config} {s' : Store} {ch' : Choices}
    {ps : List PickRecord} {tr : AccessTrace}
    (h : spawnStep ctx s cv args k ch = .ok (p, c, s', ch', ps, tr)) :
    p = .next k := by
  -- C1 S3: the V entry funnel, then the commit (or the child's panic); every
  -- `.ok` leaf carries `.next k` as the parent's successor.
  unfold spawnStep at h
  cases cv with
  | funcVal fid captured =>
    simp only [Bind.bind, Except.bind] at h
    repeat' split at h
    all_goals (cases h <;> rfl)
  | nil => simp [throw, throwThe, MonadExceptOf.throw] at h
  | _ => simp [throw, throwThe, MonadExceptOf.throw] at h

/-- Runnable-list membership from an indexed runnable goroutine. -/
theorem mem_runnableIdxs_of {s : Store} {ts : Array Thread} {j : Nat}
    {t : Thread} (hj : ts[j]? = some t) (hr : threadRunnable ctx s t = true) :
    j ∈ runnableIdxs ctx s ts := by
  obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hj
  unfold runnableIdxs
  refine List.mem_filter.mpr ⟨List.mem_range.mpr hlt, ?_⟩
  simp only [hj, hr]

/-- The slot menu's SET is contained in the runnable set — the slot
reordering at postOp adds no member (`schedPick`'s membership
formulation is therefore unchanged by the widening). -/
theorem schedSlots_mem {s : Store} {ts : Array Thread} {cur i : Nat}
    {t : Thread} (hcur : ts[cur]? = some t)
    (hmem : i ∈ schedSlots ctx s ts cur t.boundarySite) :
    i ∈ runnableIdxs ctx s ts := by
  by_cases hpost : t.boundarySite = .postOp
  · rw [hpost] at hmem
    unfold schedSlots at hmem
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · obtain ⟨c, rfl⟩ := Thread.boundarySite_postOp_shape hpost
      exact mem_runnableIdxs_of hcur rfl
    · exact (List.mem_filter.mp hmem').1
  · by_cases hback : t.boundarySite = .backEdge
    · rw [hback] at hmem
      unfold schedSlots at hmem
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact mem_runnableIdxs_of hcur
          (Thread.boundarySite_backEdge_runnable hback)
      · exact (List.mem_filter.mp hmem').1
    · have heq : schedSlots ctx s ts cur t.boundarySite = runnableIdxs ctx s ts := by
        unfold schedSlots
        cases hbs : t.boundarySite <;>
          first | (exact absurd hbs hpost) | (exact absurd hbs hback) | rfl
      rw [heq] at hmem
      exact hmem

/-- Every runnable goroutine appears in the slot menu at every site
(completeness direction: the menu never LOSES a member either). -/
theorem mem_schedSlots_of_runnable {s : Store} {ts : Array Thread}
    {cur i : Nat} {site : ChoiceSite}
    (hmem : i ∈ runnableIdxs ctx s ts) :
    i ∈ schedSlots ctx s ts cur site := by
  unfold schedSlots
  cases site <;> try exact hmem
  -- postOp/backEdge: current-first is a reordering-plus-cons, never a
  -- loss
  all_goals
    by_cases hi : i = cur
    · subst hi
      exact List.mem_cons_self ..
    · exact List.mem_cons.mpr (Or.inr (List.mem_filter.mpr
        ⟨hmem, by simpa using hi⟩))

/-- A completed spawn position's arrival analysis is the cell path
(a spawn is no channel/select apply). -/
theorem arrivalCases_of_spawnPlan {s : Store} {ts : Array Thread} {i : Nat}
    {c : Config} {p : GoValue × List GoValue × Cont}
    (hsp : spawnPlan c = some p) :
    arrivalCases ctx s ts i c = .ok .cellPath := by
  match c, hsp with
  | .retV cv (.goCalleeK [] env k), _ => rfl
  | .retV v (.goArgsK cv vals [] env k), _ => rfl

/-- The children of a spawn, as fresh (unflagged) goroutines. -/
theorem push_eq_append_running {ts : Array Thread} {child : Config} :
    ts.push (.running child none)
      = ts ++ (([child] : List Config).map (Thread.running · none)).toArray := by
  rw [Array.push_eq_append]
  rfl

/-! ### The pool event's label projections (step-label reshape, 2026-09-28)

The pool event carries the SAME `StepLabel` as the sequential step (design note
`docs/2026-09-28_step-label.md`). At a goroutine step the event's label is `stepFn`'s:
trace and output verbatim, picks = the pool's own arrival-plan picks followed by the
step's — taken FROM the label (no double accounting). The abort's terminal event is
`stepMulti_abort_single` (its label: no trace, the `repanicCollapse` record, no output);
the spawn's attribution is `StepE.spawn`'s label. -/

/-- **A goroutine step's event label IS the sequential step's label** (the pool's
arrival-plan picks prepended). Strengthened by packet B ([AGENT packet B worker] 2026-09-28,
label-reshape audit F1, [AGENT] coordinator disposition): the prepended picks `ps₁` ARE the
pool's own arrival-plan picks, the step's tape `ch₁` IS the arrival plan's residual of `ch`,
and no select interception applies — so no pick is counted twice. -/
theorem stepThread_privateStep_label {s : Store} {threads : Array Thread} {i : Nat}
    {ch : Choices} {ts' : Array Thread} {s' : Store} {ch' : Choices} {ev : StepEvent}
    (h : stepThread ctx s threads i ch = .ok (ts', s', ch', ev))
    (ha : ev.action = .privateStep) :
    ev.who = i ∧ ∃ c ch₁ ps₁ c' l, threads[i]? = some (.running c none) ∧
      arrivalPlan ctx s threads i c ch = .ok (none, ch₁, ps₁) ∧ selectApplyPlan c = none ∧
      stepFn ctx s c ch₁ = .ok (c', s', ch', l) ∧
      ev.label = ⟨l.trace, ps₁ ++ l.picks, l.out⟩ := by
  unfold stepThread at h
  repeat' (first
    | (cases h; done)
    | (simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨ha1, ha2, ha3, rfl⟩ := h
       first | (cases ha; done) | skip)
    | (rw [bind_eq_ok] at h; obtain ⟨_, _, h⟩ := h)
    | split at h
    | (dsimp only at h))
  -- The select interception's two actions are not `privateStep`.
  all_goals first
    | (simp only at ha; split at ha <;> cases ha; done)
    | skip
  -- The one remaining leaf: the goroutine's own `stepFn` step.
  rename_i _ c hthr _ _ _ _ _ _ ch₁ ps₁ harr _ hsel w hstep
  obtain ⟨c', s₁, ch₂, l⟩ := w
  simp only at ha2 ha3
  subst ha2; subst ha3
  exact ⟨rfl, c, ch₁, ps₁, c', l, hthr, harr, hsel, hstep, rfl⟩

end GoLean.GoCore.Machine

namespace GoLean.Semantics.Pool

-- B7 (2026-09-17): the program context is the first explicit parameter of
-- every definition below that reads it; theorems take it implicitly
-- (`variable {ctx}` toggles).
variable (ctx : ProgramCtx)
open GoCore GoCore.Machine

/-! A proof-only trace for the actual output-preserving pool driver.
It retains detector state, the main-exit choice, and the output prefix.
`front` names the driver's pre-fuel classification; `unfold_driver` checks
that factoring against the existing driver. Nothing here replaces it.
-/

abbrev Result := GoString × Except Stop (Store × Choices)

/-- Left = completed; right = the stream at the upcoming pool step.
The main-exit window can consume a choice even at zero fuel. -/
def front (m : MultiConfig) (ch : Choices) :
    Except Stop ((Store × Choices) ⊕ Choices) :=
  if m.threads.isEmpty then .error (.internal "thread pool without a main goroutine")
  else match m.panicMsg? with
  | some msg => .error (.panic msg)
  | none => match m.mainOutcome? with
    | some s => match runnableIdxs ctx m.shared m.threads with
      | [] => .ok (.inl (s, ch))
      | _ :: _ =>
        let (pick, ch') := Choices.consumeAt .l5ExitWindow 2 ch
        if pick == 0 then .ok (.inl (s, ch')) else .ok (.inr ch')
    | none => if (runnableIdxs ctx m.shared m.threads).isEmpty
      then .error .deadlock else .ok (.inr ch)

variable {ctx}
theorem unfold_driver (fuel : Nat) (m : MultiConfig) (r : RaceState)
    (ch : Choices) (acc : GoString) :
    execProgLoopOut ctx fuel m r ch acc =
      match front ctx m ch with
      | .error e => (acc, .error e)
      | .ok (.inl res) => (acc, .ok res)
      | .ok (.inr next) => match fuel with
        | 0 => (acc, .error .fuelOut)
        | n + 1 => match stepMulti ctx m next with
          | .error e => (acc, .error e)
          | .ok (m', ch', ev) => match raceUpdate ev m' r with
            | .error e => (acc, .error e)
            | .ok r' => execProgLoopOut ctx n m' r' ch' (ev.out.foldl GoString.append acc) := by
  rw [execProgLoopOut.eq_def]
  unfold front
  dsimp only
  split
  · rfl
  · split
    · simp_all [throw, throwThe, MonadExceptOf.throw]
    · split
      · split
        · simp_all
        · split <;> simp_all [throw, throwThe, MonadExceptOf.throw] <;> cases fuel <;> rfl
      · split <;> simp_all [throw, throwThe, MonadExceptOf.throw] <;> cases fuel <;> rfl

variable (ctx)
/-- Fuel is a bound, not a Go event. Failure constructors preserve the
existing driver's pre-step output policy, including detector rejection. -/
inductive Run : Nat → MultiConfig → RaceState → Choices → GoString → Result → Prop where
  | stop : front ctx m ch = .error e → Run fuel m r ch acc (acc, .error e)
  | done : front ctx m ch = .ok (.inl res) → Run fuel m r ch acc (acc, .ok res)
  | exhausted : front ctx m ch = .ok (.inr next) → Run 0 m r ch acc (acc, .error .fuelOut)
  | stepError : front ctx m ch = .ok (.inr next) → stepMulti ctx m next = .error e →
      Run (n + 1) m r ch acc (acc, .error e)
  | raceError : front ctx m ch = .ok (.inr next) → stepMulti ctx m next = .ok (m', ch', ev) →
      raceUpdate ev m' r = .error e →
      Run (n + 1) m r ch acc (acc, .error e)
  | step : front ctx m ch = .ok (.inr next) → stepMulti ctx m next = .ok (m', ch', ev) →
      raceUpdate ev m' r = .ok r' →
      Run n m' r' ch' (ev.out.foldl GoString.append acc) result →
      Run (n + 1) m r ch acc result

variable {ctx}
theorem run_iff {fuel m r ch acc result} :
    execProgLoopOut ctx fuel m r ch acc = result ↔ Run ctx fuel m r ch acc result := by
  constructor
  · intro h
    induction fuel generalizing m r ch acc with
    | zero =>
      rw [unfold_driver] at h
      cases hf : front ctx m ch with
      | error e => simp only [hf] at h; subst result; exact .stop hf
      | ok v => cases v with
        | inl res => simp only [hf] at h; subst result; exact .done hf
        | inr next => simp only [hf] at h; subst result; exact .exhausted hf
    | succ n ih =>
      rw [unfold_driver] at h
      cases hf : front ctx m ch with
      | error e => simp only [hf] at h; subst result; exact .stop hf
      | ok v => cases v with
        | inl res => simp only [hf] at h; subst result; exact .done hf
        | inr next =>
          simp only [hf] at h
          cases hs : stepMulti ctx m next with
          | error e => simp only [hs] at h; subst result; exact .stepError hf hs
          | ok v =>
            obtain ⟨m', ch', ev⟩ := v
            simp only [hs] at h
            cases hr : raceUpdate ev m' r with
            | error e => simp only [hr] at h; subst result; exact .raceError hf hs hr
            | ok r' =>
              simp only [hr] at h
              exact .step hf hs hr (ih h)
  · intro h
    induction h with
    | stop hf => rw [unfold_driver, hf]
    | done hf => rw [unfold_driver, hf]
    | exhausted hf => rw [unfold_driver, hf]
    | stepError hf hs => rw [unfold_driver, hf]; simp only [hs]
    | raceError hf hs hr => rw [unfold_driver, hf]; simp only [hs, hr]
    | step hf hs hr _ ih => rw [unfold_driver, hf]; simpa only [hs, hr] using ih

/-- Correct existential-stream observation contract, over this finite,
detector-checked, output-bearing trace rather than bare `StepsM`. -/
theorem exists_run_iff {m r acc result} :
    (∃ fuel ch, execProgLoopOut ctx fuel m r ch acc = result) ↔
    ∃ fuel ch, Run ctx fuel m r ch acc result := by
  simp only [run_iff]

end GoLean.Semantics.Pool

namespace GoLean.Semantics.Pool

-- B7 (2026-09-17): `ProgramRun` is PROGRAM-level — the run's context is the
-- one `runProgramSetupM` builds and returns (`pctx` below, bound by the
-- setup premise), so nothing here takes a context parameter.
open GoCore GoCore.Machine

/-- Complete entry/readout contract for the shipped program driver.
Setup is still an executable premise, not a claimed typed-admission proof.
It uses the SAME fuel parameter as the subject loop, just as the driver does.
-/
inductive ProgramRun (fuel : Nat) (p : Program) (name : String)
    (args : Array GoValue) (ch : Choices) : RunResult → Prop where
  | setupError : runProgramSetupM fuel p name args ch = .error e →
      ProgramRun fuel p name args ch (.error (e, GoString.empty))
  | runError : runProgramSetupM fuel p name args ch = .ok (pctx, c, s, locs, ch₁) →
      Run pctx fuel ⟨#[Thread.running c none], s, 0⟩ {} ch₁ GoString.empty (out, .error e) →
      ProgramRun fuel p name args ch (.error (e, out))
  | readError : runProgramSetupM fuel p name args ch = .ok (pctx, c, s, locs, ch₁) →
      Run pctx fuel ⟨#[Thread.running c none], s, 0⟩ {} ch₁ GoString.empty (out, .ok (sf, chf)) →
      loadMany pctx sf locs = .error e →
      ProgramRun fuel p name args ch (.error (e, out))
  | done : runProgramSetupM fuel p name args ch = .ok (pctx, c, s, locs, ch₁) →
      Run pctx fuel ⟨#[Thread.running c none], s, 0⟩ {} ch₁ GoString.empty (out, .ok (sf, chf)) →
      loadMany pctx sf locs = .ok vs →
      ProgramRun fuel p name args ch (.ok { values := vs.toArray, output := out })

theorem program_run_iff {fuel p name args ch result} :
    runProgramPoolOutM fuel p name args ch = result ↔ ProgramRun fuel p name args ch result := by
  constructor
  · intro h
    unfold runProgramPoolOutM at h
    cases hs : runProgramSetupM fuel p name args ch with
    | error e => simp only [hs] at h; subst result; exact .setupError hs
    | ok v =>
      obtain ⟨pctx, c, s, locs, ch₁⟩ := v
      simp only [hs] at h
      cases hr : execProgLoopOut pctx fuel ⟨#[Thread.running c none], s, 0⟩ {} ch₁ GoString.empty with
      | mk out r => cases r with
        | error e => simp only [hr] at h; subst result; exact .runError hs (run_iff.mp hr)
        | ok v =>
          obtain ⟨sf, chf⟩ := v
          simp only [hr] at h
          cases hl : loadMany pctx sf locs with
          | error e => simp only [hl] at h; subst result; exact .readError hs (run_iff.mp hr) hl
          | ok vs => simp only [hl] at h; subst result; exact .done hs (run_iff.mp hr) hl
  · intro h
    cases h with
    | setupError hs => simp only [runProgramPoolOutM, hs]
    | runError hs hr => simp only [runProgramPoolOutM, hs, run_iff.mpr hr]
    | readError hs hr hl => simp only [runProgramPoolOutM, hs, run_iff.mpr hr, hl]
    | done hs hr hl => simp only [runProgramPoolOutM, hs, run_iff.mpr hr, hl]

/-- Existential choices belong on BOTH sides of an observation-set bridge. -/
theorem exists_program_run_iff {p name args result} :
    (∃ fuel ch, runProgramPoolOutM fuel p name args ch = result) ↔
    ∃ fuel ch, ProgramRun fuel p name args ch result := by simp only [program_run_iff]

/-- Experimental observation vocabulary: keep the actual readout and the
terminal's byte prefix. No claim about equivalence to every Go observer. -/
inductive Observation where
  | normal (readout : Readout)
  | terminal (reason : Terminal) (output : GoString)

def observationOf : RunResult → Option Observation
  | .ok r => some (.normal r)
  | .error (.terminal t, out) => some (.terminal t out)
  | .error (.refusal _, _) | .error (.fuelOut, _) => none

theorem fuel_is_not_observation (out : GoString) :
    observationOf (.error (.fuelOut, out)) = none := rfl
theorem refusal_is_not_observation (r : Refusal) (out : GoString) :
    observationOf (.error (.refusal r, out)) = none := rfl

/-- The corrected whole-program finite observation-set bridge. This is
partial correctness/may-observation infrastructure, not termination. -/
theorem observation_iff {p name args obs} :
    (∃ fuel ch, observationOf (runProgramPoolOutM fuel p name args ch) = some obs) ↔
      ∃ fuel ch result, ProgramRun fuel p name args ch result ∧ observationOf result = some obs := by
  constructor
  · rintro ⟨fuel, ch, h⟩
    exact ⟨fuel, ch, _, program_run_iff.mp rfl, h⟩
  · rintro ⟨fuel, ch, result, hrun, hobs⟩
    exact ⟨fuel, ch, (program_run_iff.mpr hrun) ▸ hobs⟩

end GoLean.Semantics.Pool

/-! ## The output-folding driver's accumulator law (backlog row 47, raft-proofs G9)

[AGENT lane core/g11-init-driver-1021] 2026-10-21. The CLI (`golean native-json-run`) runs the
pool through `execProgLoopOut` (`Multi.lean`), `execProgLoop` with the pool's `StepEvent.out`
events folded in step order onto an accumulator. THE BRIDGE the customer consumes is
`execProgLoopOut_snd` (`Multi.lean`, since 2026-09-04): the OUTCOME component IS `execProgLoop`;
the output content on one goroutine is the sequential labels' fold (`execProgLoopOut_single`,
`execProgLoopOut_single_prefix`, `seqOut_of_prefix`; `PoolProjection.lean`). Beside them, an
ACCUMULATOR LAW (review F1: a law about the driver, not the bridge — every CLI call site passes
`GoString.empty`): `execProgLoopOut_acc` says the output component is the accumulator followed by
the run's own fold from the empty string (the fold only appends), and
`execProgLoopOut_eq_execProgLoop` is that and `execProgLoopOut_snd` as one equation on the pair. -/

namespace GoLean.GoString

theorem append_assoc (a b c : GoString) : (a.append b).append c = a.append (b.append c) := by
  simp [append, Array.append_assoc]

theorem empty_append (a : GoString) : empty.append a = a := by
  cases a
  simp [append, empty]

theorem append_empty (a : GoString) : a.append empty = a := by
  cases a
  simp [append, empty]

/-- A fold of outputs onto an accumulator is the accumulator followed by the fold onto the empty
string. -/
theorem foldl_append_acc : ∀ (l : List GoString) (acc : GoString),
    l.foldl append acc = acc.append (l.foldl append empty)
  | [], acc => (append_empty acc).symm
  | o :: l, acc => by
    simp only [List.foldl_cons]
    rw [foldl_append_acc l (acc.append o), foldl_append_acc l (empty.append o), empty_append,
      append_assoc]

end GoLean.GoString

namespace GoLean.GoCore.Machine

variable {ctx : ProgramCtx}
open GoLean.Semantics.Pool (unfold_driver front)

/-- **The accumulator law of the output-folding driver**: the output component is the accumulator
followed by the run's own output (its fold from the empty string) — the fold only APPENDS to `acc`,
on every path (a Go terminal, a refusal, the fuel, a detector rejection, a normal completion). -/
theorem execProgLoopOut_acc (fuel : Nat) (m : MultiConfig) (r : RaceState) (ch : Choices)
    (acc : GoString) :
    (execProgLoopOut ctx fuel m r ch acc).1
      = acc.append (execProgLoopOut ctx fuel m r ch GoString.empty).1 := by
  induction fuel generalizing m r ch acc with
  | zero =>
    rw [unfold_driver, unfold_driver]
    cases hf : front ctx m ch with
    | error e => simp [GoString.append_empty]
    | ok v =>
      cases v with
      | inl res => simp [GoString.append_empty]
      | inr next => simp [GoString.append_empty]
  | succ n ih =>
    rw [unfold_driver, unfold_driver]
    cases hf : front ctx m ch with
    | error e => simp [GoString.append_empty]
    | ok v =>
      cases v with
      | inl res => simp [GoString.append_empty]
      | inr next =>
        simp only
        cases hs : stepMulti ctx m next with
        | error e => simp [GoString.append_empty]
        | ok v =>
          obtain ⟨m', ch', ev⟩ := v
          simp only
          cases hr : raceUpdate ev m' r with
          | error e => simp [GoString.append_empty]
          | ok r' =>
            simp only
            rw [ih m' r' ch' (ev.out.foldl GoString.append acc),
              ih m' r' ch' (ev.out.foldl GoString.append GoString.empty),
              GoString.foldl_append_acc ev.out acc, GoString.append_assoc]

/-- **The pair form of the accumulator law**: `execProgLoopOut` is `execProgLoop` paired with the
output — the accumulator followed by the run's own fold from the empty string. The outcome half is
`execProgLoopOut_snd` (the bridge), the output half `execProgLoopOut_acc`. -/
theorem execProgLoopOut_eq_execProgLoop (fuel : Nat) (m : MultiConfig) (r : RaceState)
    (ch : Choices) (acc : GoString) :
    execProgLoopOut ctx fuel m r ch acc
      = (acc.append (execProgLoopOut ctx fuel m r ch GoString.empty).1,
         execProgLoop ctx fuel m r ch) := by
  rw [← execProgLoopOut_acc, ← execProgLoopOut_snd fuel m r ch acc]

end GoLean.GoCore.Machine
