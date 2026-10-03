import GoLean.GoCore.Prefix

/-!
# The sequential-to-pool PROJECTIONS (window packet D, 2026-10-03)

[AGENT packet D worker]. Packet B's audit F5 (2026-09-28) listed two projections as OWED before the
re-pin offer, and `CLAUDE.md` names them in its «still OWED» list: the single-goroutine OUTPUT
AGREEMENT and the SEQUENTIAL-TO-POOL TERMINAL PROJECTION. Both are proved here over the
single-goroutine pool, extending `execProgLoop_single` (`MultiSound.lean`) from the outcome to
the output-folding driver and from the three `transferable` classes to every Go terminal but the
sequential deadlock (the fatal included — the preprint phase's «panic while printing panic value»
and the sync misuses).

* **Output agreement** (`execProgLoopOut_single`, `execProgLoopOut_single_prefix`): the pool's
  output fold — `execProgLoopOut`'s concatenation of the pool events' `out` in step order — equals
  the sequential labels' output fold: for a run `execStmtLoop ctx fuel σ c ch = r` in a
  transferable class, the one-goroutine pool at fuel `fuel + seqOpCount …` returns `(seqOut …, r)`,
  and `seqOut` IS the fold of the `Prefix` labels of the run (`seqOut_of_prefix`), i.e. the `out`
  channel of `StepLabel.fold` (`outFold_eq_fold`). The hinge is `stepThread_single_out`: a
  singleton goroutine step's event carries exactly the sequential step's `out` — on the private
  path (`stepThread_privateStep_label`'s shape) and on the select-interception path, whose events
  print nothing, as the select apply's label does.
* **Terminal projection** (`execProgLoop_single_wide`, `execProgLoop_single_terminal`,
  `execProgLoopOut_single_terminal`): every sequential result but the deadlock and the fail-closed
  refusals transfers verbatim — `transferableWide` widens `transferable` by the `fatal` and
  `raceDetected` terminals; a sequential Go terminal `t ≠ .deadlock` is the pool's `.error
  (.terminal t)` with the printed prefix. The deadlock stays excluded for the reason
  `MultiSound.lean` states (an artificial wake-ready blocked seed resumes in the pool).
* **The embedding without the `seqOpCount = 0` premise** (the logic team's request 9, relayed):
  `seqOpCount_eq_zero` — a run along which no reachable step opens a registry boundary
  (`Config.afterStepFlag … = none`, stated over `Prefix`-reachable steps as `NoRefusal` is) has op
  count zero, so `execProgLoop_single_noBoundary` embeds it at EQUAL fuel;
  `afterStepFlag_none_of_noRegistry` discharges the flag for a non-spawn, non-committing step.

Statements are additions only; `execProgLoop_single` and `transferable` are untouched (BridgeSet
rows 23/50 pin them). Proof-only module: no runtime definition changes; `seqOut`, `outFold` and
`transferableWide` are proof-layer definitions beside `seqOpCount`.
-/

namespace GoLean.GoCore.Machine

open GoLean GoLean.Semantics.Pool
open GoLean.GoCore.ExecutionStatement (Prefix ZeroCost Blocked)

variable (ctx : ProgramCtx)

/-- The result classes the WIDE conservation transfer claims: everything but the sequential
deadlock (the pool may resume a wake-ready blocked seed) and the fail-closed refusals (a spawn
position is refused sequentially and forked by the pool). `transferable` ⊆ this. -/
def transferableWide : Except Stop (Store × Choices) → Prop
  | .ok _ => True
  | .error .fuelOut => True
  | .error (.terminal .deadlock) => False
  | .error (.terminal _) => True
  | .error (.refusal _) => False

/-- **The sequential OUTPUT fold** along the executable run: each step's `out` appended in step
order, stopping where the driver stops (a terminal, a park, a refusing or aborting step, the fuel).
The twin of `seqOpCount`; `seqOut_of_prefix` identifies it with the `Prefix` labels' fold. -/
def seqOut : Nat → Store → Config → Choices → GoString → GoString
  | 0, _, _, _, acc => acc
  | fuel + 1, σ, c, ch, acc =>
      if c.isTerminal || isBlockedConfig c then acc
      else
        match stepFn ctx σ c ch with
        | .error _ => acc
        | .ok (c', σ', ch', l) => seqOut fuel σ' c' ch' (l.out.foldl GoString.append acc)

/-- The `out` fold of a label list onto an accumulator (the pool's fold shape). -/
def outFold (ls : List StepLabel) (acc : GoString) : GoString :=
  ls.foldl (fun a l => l.out.foldl GoString.append a) acc

variable {ctx}

theorem transferable_wide {r : Except Stop (Store × Choices)} (h : transferable r) : transferableWide r := by
  cases r with
  | ok _ => trivial
  | error e => cases_stop e <;> simp_all [transferable, transferableWide]

/-- `transferableWide`'s classes, as facts: every success, fuel-out and non-deadlock terminal is in;
the deadlock and every refusal are out. -/
theorem transferableWide_ok (x : Store × Choices) : transferableWide (.ok x) := trivial
theorem transferableWide_fuelOut : transferableWide (.error .fuelOut) := trivial
theorem transferableWide_terminal {t : Terminal} (ht : t ≠ .deadlock) : transferableWide (.error (.terminal t)) := by
  cases t <;> simp_all [transferableWide]
theorem not_transferableWide_deadlock : ¬ transferableWide (.error (.terminal .deadlock)) := fun h => h
theorem not_transferableWide_refusal (r : Refusal) : ¬ transferableWide (.error (.refusal r)) := fun h => h

/-- `seqOut`'s defining equations. -/
theorem seqOut_zero (σ : Store) (c : Config) (ch : Choices) (acc : GoString) : seqOut ctx 0 σ c ch acc = acc := rfl
theorem seqOut_succ (fuel : Nat) (σ : Store) (c : Config) (ch : Choices) (acc : GoString) :
    seqOut ctx (fuel + 1) σ c ch acc
      = (if c.isTerminal || isBlockedConfig c then acc
         else match stepFn ctx σ c ch with
           | .error _ => acc
           | .ok (c', σ', ch', l) => seqOut ctx fuel σ' c' ch' (l.out.foldl GoString.append acc)) := rfl

theorem outFold_nil (acc : GoString) : outFold [] acc = acc := rfl
theorem outFold_cons (l : StepLabel) (ls : List StepLabel) (acc : GoString) :
    outFold (l :: ls) acc = outFold ls (l.out.foldl GoString.append acc) := rfl

/-- The fold is the `out` channel of the per-field fold `StepLabel.fold`. -/
theorem outFold_eq_fold : ∀ (ls : List StepLabel) (acc : GoString),
    outFold ls acc = (StepLabel.fold ls).out.foldl GoString.append acc
  | [], acc => rfl
  | l :: ls, acc => by
      rw [outFold_cons, outFold_eq_fold ls]
      simp [StepLabel.fold, List.foldl_append]

/-! ## The singleton pool's `front` (PoolTrace's pre-step classification) -/

theorem runnableIdxs_singleton_none {σ : Store} {t : Thread} (h : threadRunnable ctx σ t = false) :
    runnableIdxs ctx σ #[t] = [] := by
  simp [runnableIdxs, h]

theorem mainOutcome?_single_none {σ : Store} {c : Config} (hd : c.isTerminal = false) :
    MultiConfig.mainOutcome? ⟨#[.running c none], σ, 0⟩ = none := by
  unfold MultiConfig.mainOutcome?
  have h0 : ((⟨#[.running c none], σ, 0⟩ : MultiConfig).threads[0]? : Option Thread) = some (.running c none) := rfl
  rw [h0]
  split <;> simp_all [Config.isTerminal]

/-- A live, unparked, unflagged singleton goroutine: the driver steps. -/
theorem front_single_step {σ : Store} {c : Config} {ch : Choices} (hd : c.isTerminal = false)
    (hb : isBlockedConfig c = false) :
    front ctx ⟨#[.running c none], σ, 0⟩ ch = .ok (.inr ch) := by
  have hrun : threadRunnable ctx σ (.running c none) = true := by simp [threadRunnable, hd, hb]
  simp [front, MultiConfig.panicMsg?, mainOutcome?_single_none hd, runnableIdxs_singleton hrun]

/-- A flagged singleton goroutine (its boundary clear pending): the driver steps. -/
theorem front_single_flagged {σ : Store} {c : Config} {site : ChoiceSite} {ch : Choices} :
    front ctx ⟨#[.running c (some site)], σ, 0⟩ ch = .ok (.inr ch) := by
  have hrun : threadRunnable ctx σ (.running c (some site)) = true := rfl
  simp [front, MultiConfig.panicMsg?, MultiConfig.mainOutcome?, runnableIdxs_singleton hrun]

/-- Main at its terminal, alone: the run completes with the shared store and the tape. -/
theorem front_terminal {σ : Store} {ch : Choices} :
    front ctx ⟨#[.running (.next .stop) none], σ, 0⟩ ch = .ok (.inl (σ, ch)) := by
  have hrun : threadRunnable ctx σ (.running (.next .stop) none) = false := by
    simp [threadRunnable, Config.isTerminal]
  simp [front, MultiConfig.panicMsg?, MultiConfig.mainOutcome?, runnableIdxs_singleton_none hrun]

/-- The abort tombstone: the `panic` terminal. -/
theorem front_aborted {σ : Store} {msg : String} {ch : Choices} :
    front ctx ⟨#[.aborted msg], σ, 0⟩ ch = .error (.panic msg) := by
  simp [front, MultiConfig.panicMsg?]

/-! ## The singleton step's EVENT carries the sequential label's output -/

/-- The one-thread `stepThread` on a successful `stepFn` step: the successor flagged by the boundary
rule, and an event whose `out` IS the step's `out` — on the private path the event's label is the
step's (`stepThread_privateStep_label`); on the select-interception path both print nothing. -/
theorem stepThread_single_out {σ : Store} {c : Config} {ch : Choices}
    (hbl : isBlockedConfig c = false) (hsp : spawnPlan c = none) (hab : c.abort? = none)
    {c' : Config} {σ' : Store} {ch' : Choices} {l : StepLabel}
    (hstep : stepFn ctx σ c ch = .ok (c', σ', ch', l)) :
    ∃ ev, stepThread ctx σ #[.running c none] 0 ch = .ok (#[Thread.afterStep σ c c'], σ', ch', ev)
      ∧ ev.out = l.out := by
  unfold stepThread
  have h0 : (#[Thread.running c none] : Array Thread)[0]? = some (.running c none) := rfl
  rw [h0]
  simp only [hbl, Bool.false_eq_true, reduceIte, hab, hsp]
  rw [show arrivalPlan ctx σ #[Thread.running c none] 0 c ch = .ok (none, ch, [])
    from arrivalPlan_singleton]
  simp only [Bind.bind, Except.bind]
  cases hselp : selectApplyPlan c with
  | none =>
      rw [hstep]
      exact ⟨⟨0, .privateStep, { l with picks := [] ++ l.picks }⟩, rfl, rfl⟩
  | some p =>
      obtain ⟨v, clauses, default?, done, env, k'⟩ := p
      obtain rfl := selectApplyPlan_shape hselp
      dsimp only
      cases happly : applySelect ctx σ clauses default? ((v :: done).reverse) env k' ch with
      | ok r =>
          obtain ⟨c₂, s₂, ch₂, ps, cl?, tr⟩ := r
          have hfn : stepFn ctx σ (.retV v (.selectOpsK clauses default? done [] env k')) ch
              = .ok (c₂, s₂, ch₂, ⟨tr, ps, []⟩) := by
            unfold stepFn
            dsimp only
            rw [happly]
            rfl
          rw [hfn] at hstep
          simp only [Except.ok.injEq, Prod.mk.injEq] at hstep
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hstep
          refine ⟨⟨0, match cl? with
            | some cl => .selectCommit cl
            | none => .selectPass, ⟨tr, [] ++ ps, []⟩⟩, ?_, rfl⟩
          cases cl? <;> rfl
      | error e =>
          have hfn : stepFn ctx σ (.retV v (.selectOpsK clauses default? done [] env k')) ch
              = (match e with
                 | .panic msg => .ok (.panicking [panicEntry msg] k', σ, ch, ⟨[], [], []⟩)
                 | e => .error e) := by
            unfold stepFn
            dsimp only
            simp only [happly]
            cases_stop e <;> rfl
          rw [hfn] at hstep
          cases_stop e <;> simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at hstep
          case panic msg =>
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hstep
            exact ⟨⟨0, .selectPass, ⟨[], [], []⟩⟩, rfl, rfl⟩

/-- `stepMulti_single` with the event's output named: the one-thread pool step on a successful
sequential step is that step, its event printing what the step printed. -/
theorem stepMulti_single_out {σ : Store} {c : Config} {ch : Choices}
    (hbl : isBlockedConfig c = false) (hsp : spawnPlan c = none) (hab : c.abort? = none)
    (hdone : c.isTerminal = false)
    {c' : Config} {σ' : Store} {ch' : Choices} {l : StepLabel}
    (hstep : stepFn ctx σ c ch = .ok (c', σ', ch', l)) :
    ∃ ev, stepMulti ctx ⟨#[.running c none], σ, 0⟩ ch = .ok (⟨#[Thread.afterStep σ c c'], σ', 0⟩, ch', ev)
      ∧ ev.out = l.out := by
  have hrun : threadRunnable ctx σ (.running c none) = true := by
    simp [threadRunnable, hdone, hbl]
  obtain ⟨ev, hst, hev⟩ := stepThread_single_out hbl hsp hab hstep
  have hinto : stepThreadInto ctx ⟨#[.running c none], σ, 0⟩ 0 ch
      = .ok (⟨#[Thread.afterStep σ c c'], σ', 0⟩, ch', ev) := by
    unfold stepThreadInto
    show (stepThread ctx σ #[.running c none] 0 ch).bind _ = _
    rw [hst]
    rfl
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
    exact ⟨_, rfl, hev⟩
  · simp only [Bool.not_eq_true] at hb
    simp only [hb, Bool.false_eq_true, reduceIte]
    exact ⟨ev, hinto, hev⟩

/-! ## The output agreement: the one-goroutine pool's fold is the sequential fold -/

/-- **The conservation transfer with OUTPUT, wide**: every sequential result but the deadlock and
the refusals is the one-goroutine output-folding pool's result verbatim at the pool's fuel
`fuel + seqOpCount …` — the SAME outcome and the sequential output fold `seqOut`. The induction is
`execProgLoop_single`'s, over `execProgLoopOut` (`PoolTrace.unfold_driver`): a boundary clear and
the abort's tombstone step print nothing (`stepMulti_flagged_single`, `stepMulti_abort_single`);
a goroutine step prints its label's `out` (`stepMulti_single_out`). -/
theorem execProgLoopOut_single_wide :
    ∀ {fuel : Nat} {σ : Store} {c : Config} {ch : Choices} {rs : RaceState} {acc : GoString}
      {r : Except Stop (Store × Choices)},
      execStmtLoop ctx fuel σ c ch = r → transferableWide r →
      execProgLoopOut ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch acc
        = (seqOut ctx fuel σ c ch acc, r) := by
  intro fuel
  induction fuel with
  | zero =>
    intro σ c ch rs acc r hr htr
    unfold execStmtLoop at hr
    split at hr
    · subst hr
      simp only [seqOpCount, Nat.add_zero]
      rw [unfold_driver, front_terminal]
      rfl
    · subst hr; simp [transferableWide, throw, throwThe, MonadExceptOf.throw] at htr
    · subst hr; simp [transferableWide, throw, throwThe, MonadExceptOf.throw] at htr
    · subst hr; simp [transferableWide, throw, throwThe, MonadExceptOf.throw] at htr
    · subst hr; simp [transferableWide, throw, throwThe, MonadExceptOf.throw] at htr
    · rename_i harm1 harm6 harm7 harm8 harm9
      subst hr
      obtain ⟨-, -, hd, hb⟩ := singleton_pool_facts (σ := σ) harm1 harm6 harm7 harm8 harm9
      simp only [seqOpCount, Nat.add_zero]
      rw [unfold_driver, front_single_step hd hb]
      rfl
  | succ n ih =>
    intro σ c ch rs acc r hr htr
    unfold execStmtLoop at hr
    split at hr
    · subst hr
      simp only [seqOpCount, Config.isTerminal, Bool.true_or, ↓reduceIte, Nat.add_zero]
      rw [unfold_driver, front_terminal]
      simp [seqOut, Config.isTerminal]
    · subst hr; simp [transferableWide, throw, throwThe, MonadExceptOf.throw] at htr
    · subst hr; simp [transferableWide, throw, throwThe, MonadExceptOf.throw] at htr
    · subst hr; simp [transferableWide, throw, throwThe, MonadExceptOf.throw] at htr
    · subst hr; simp [transferableWide, throw, throwThe, MonadExceptOf.throw] at htr
    · rename_i harm1 harm6 harm7 harm8 harm9
      obtain ⟨-, -, hd, hb⟩ := singleton_pool_facts (σ := σ) harm1 harm6 harm7 harm8 harm9
      simp only [Bind.bind, Except.bind] at hr
      have hcnt : seqOpCount ctx (n + 1) σ c ch
          = (match stepFn ctx σ c ch with
             | .error _ => 0
             | .ok (c', σ', ch', _) =>
                 (if (c.afterStepFlag σ c').isSome then 1 else 0) + seqOpCount ctx n σ' c' ch') := by
        simp only [seqOpCount, hd, hb, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
        rcases stepFn ctx σ c ch with _ | ⟨c', σ', ch', l⟩ <;> rfl
      have hout : seqOut ctx (n + 1) σ c ch acc
          = (match stepFn ctx σ c ch with
             | .error _ => acc
             | .ok (c', σ', ch', l) => seqOut ctx n σ' c' ch' (l.out.foldl GoString.append acc)) := by
        simp only [seqOut, hd, hb, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
      rw [hcnt, hout]
      cases hsp : spawnPlan c with
      | some p =>
          have hcls := spawnPlan_stepFn_refuses (ctx := ctx) (σ := σ) (ch := ch) hsp
          cases hstep : stepFn ctx σ c ch with
          | ok r₂ => rw [hstep] at hcls; simp at hcls
          | error e =>
              rw [hstep] at hr hcls
              subst hr
              cases_stop e <;> simp_all [transferableWide]
      | none =>
      cases hab : c.abort? with
      | some p =>
          obtain ⟨first, rest⟩ := p
          rw [stepFn_abort hab] at hr ⊢
          have hmulti := stepMulti_abort_single (ctx := ctx) (σ := σ) (ch := ch) hab
          have hpick : (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1
              = (abortConsult first rest ch).1 := by
            unfold abortConsult
            rw [← Choices.consumeAtE_fst_snd]
          rw [hpick] at hmulti
          cases hmsg : abortMsg ctx first rest (abortConsult first rest ch).1 with
          | error e =>
              rw [hmsg] at hr hmulti
              simp only [Bind.bind, Except.bind] at hr
              subst hr
              simp only [Bind.bind, Except.bind, Nat.add_zero]
              rw [unfold_driver, front_single_step hd hb]
              simp [hmulti, Except.map]
          | ok msg =>
              rw [hmsg] at hr hmulti
              simp only [Bind.bind, Except.bind] at hr
              subst hr
              simp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Nat.add_zero]
              rw [unfold_driver, front_single_step hd hb]
              simp only [hmulti, Except.map, raceUpdate_single]
              rw [unfold_driver, front_aborted]
              rfl
      | none =>
          cases hstep : stepFn ctx σ c ch with
          | error e =>
              rw [hstep] at hr
              subst hr
              obtain ⟨ev, hmulti⟩ := stepMulti_single (σ := σ) (ch := ch) hb hsp hab hd
              rw [hstep] at hmulti
              simp only [Except.map] at hmulti
              simp only [Nat.add_zero]
              rw [unfold_driver, front_single_step hd hb]
              simp [hmulti]
          | ok r₂ =>
              obtain ⟨c₂, σ₂, ch₂, l⟩ := r₂
              rw [hstep] at hr
              obtain ⟨ev, hmulti, hev⟩ := stepMulti_single_out hb hsp hab hd hstep
              have hrec := ih (rs := rs) (acc := l.out.foldl GoString.append acc) hr htr
              simp only
              cases hflag : c.afterStepFlag σ c₂ with
              | none =>
                  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
                  rw [show n + 1 + seqOpCount ctx n σ₂ c₂ ch₂ = (n + seqOpCount ctx n σ₂ c₂ ch₂) + 1
                    from by omega]
                  rw [unfold_driver, front_single_step hd hb]
                  simp only [Thread.afterStep, hflag] at hmulti
                  simp only [hmulti, raceUpdate_single, StepEvent.out] at hev ⊢
                  rw [hev]
                  exact hrec
              | some site =>
                  simp only [Option.isSome_some, ↓reduceIte]
                  rw [show n + 1 + (1 + seqOpCount ctx n σ₂ c₂ ch₂)
                      = ((n + seqOpCount ctx n σ₂ c₂ ch₂) + 1) + 1 from by omega]
                  rw [unfold_driver, front_single_step hd hb]
                  simp only [Thread.afterStep, hflag] at hmulti
                  simp only [hmulti, raceUpdate_single, StepEvent.out] at hev ⊢
                  rw [hev]
                  rw [unfold_driver, front_single_flagged]
                  simp only [stepMulti_flagged_single, raceUpdate_single]
                  exact hrec

/-- The output agreement in packet A's `transferable` classes. -/
theorem execProgLoopOut_single {fuel : Nat} {σ : Store} {c : Config} {ch : Choices} {rs : RaceState}
    {acc : GoString} {r : Except Stop (Store × Choices)}
    (hr : execStmtLoop ctx fuel σ c ch = r) (htr : transferable r) :
    execProgLoopOut ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch acc
      = (seqOut ctx fuel σ c ch acc, r) :=
  execProgLoopOut_single_wide hr (transferable_wide htr)

/-- **The conservation transfer, wide** (`execProgLoop_single` extended to the fatal and
race terminals): the outcome component of the output agreement. -/
theorem execProgLoop_single_wide {fuel : Nat} {σ : Store} {c : Config} {ch : Choices} {rs : RaceState}
    {r : Except Stop (Store × Choices)}
    (hr : execStmtLoop ctx fuel σ c ch = r) (htr : transferableWide r) :
    execProgLoop ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch = r := by
  have h := execProgLoopOut_single_wide (rs := rs) (acc := GoString.empty) hr htr
  rw [← execProgLoopOut_snd, h]

/-- **The sequential-to-pool TERMINAL projection**: a sequential Go terminal other than the deadlock
— the `panic` abort, the unrecoverable `fatal` (the preprint phase's «panic while printing panic
value», the sync misuses), a detected race — is the one-goroutine pool's terminal. -/
theorem execProgLoop_single_terminal {fuel : Nat} {σ : Store} {c : Config} {ch : Choices} {rs : RaceState}
    {t : Terminal} (hr : execStmtLoop ctx fuel σ c ch = .error (.terminal t)) (ht : t ≠ .deadlock) :
    execProgLoop ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch = .error (.terminal t) :=
  execProgLoop_single_wide hr (by cases t <;> simp_all [transferableWide])

/-- The terminal projection WITH the printed prefix: the pool reports the terminal together with the
output folded before it, which is the sequential fold. -/
theorem execProgLoopOut_single_terminal {fuel : Nat} {σ : Store} {c : Config} {ch : Choices} {rs : RaceState}
    {acc : GoString} {t : Terminal} (hr : execStmtLoop ctx fuel σ c ch = .error (.terminal t)) (ht : t ≠ .deadlock) :
    execProgLoopOut ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch acc
      = (seqOut ctx fuel σ c ch acc, .error (.terminal t)) :=
  execProgLoopOut_single_wide hr (by cases t <;> simp_all [transferableWide])

/-! ## `seqOut` is the `Prefix` labels' fold -/

theorem isTerminal_false_of_stepFn_ok {σ : Store} {c : Config} {ch : Choices} {c' : Config} {σ' : Store}
    {ch' : Choices} {l : StepLabel} (h : stepFn ctx σ c ch = .ok (c', σ', ch', l)) : c.isTerminal = false := by
  cases hc : c.isTerminal
  · rfl
  · exfalso
    have hz : ZeroCost c := by
      unfold Config.isTerminal at hc
      split at hc
      · exact .inl rfl
      · cases hc
    exact ExecutionStatement.stepFn_zeroCost_not_ok h hz

theorem isBlockedConfig_false_of_stepFn_ok {σ : Store} {c : Config} {ch : Choices} {c' : Config} {σ' : Store}
    {ch' : Choices} {l : StepLabel} (h : stepFn ctx σ c ch = .ok (c', σ', ch', l)) : isBlockedConfig c = false := by
  cases hc : isBlockedConfig c
  · rfl
  · exfalso
    have hz : ZeroCost c := by
      unfold isBlockedConfig at hc
      split at hc
      · exact .inr (.inl ⟨_, _, _, rfl⟩)
      · exact .inr (.inr (.inl ⟨_, _, _, _, _, rfl⟩))
      · exact .inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
      · exact .inr (.inr (.inr (.inr ⟨_, _, _, _, rfl⟩)))
      · cases hc
    exact ExecutionStatement.stepFn_zeroCost_not_ok h hz

theorem zeroCost_stops {c : Config} (hz : ZeroCost c) : (c.isTerminal || isBlockedConfig c) = true := by
  rcases hz with rfl | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> rfl

/-- `seqOut` at a zero-cost endpoint or a stopping step is the accumulator. -/
theorem seqOut_stop {fuel : Nat} {σ : Store} {c : Config} {ch : Choices} {acc : GoString}
    (h : ZeroCost c ∨ ∃ e, stepFn ctx σ c ch = .error e) : seqOut ctx fuel σ c ch acc = acc := by
  cases fuel with
  | zero => rfl
  | succ n =>
    rcases h with hz | ⟨e, he⟩
    · simp [seqOut, zeroCost_stops hz]
    · unfold seqOut
      split
      · rfl
      · simp [he]

/-- **`seqOut` IS the labels' fold**: along a `Prefix` of the run that reaches where the driver
stops (the fuel, a zero-cost endpoint, or a refusing/aborting step), the sequential output fold is
the fold of the prefix's labels. -/
theorem seqOut_of_prefix :
    ∀ {n : Nat} {σ sf : Store} {c cf : Config} {ch chf : Choices} {ls : List StepLabel},
      Prefix ctx n σ c ch ls sf cf chf → ∀ {fuel : Nat} {acc : GoString}, n ≤ fuel →
      (n = fuel ∨ ZeroCost cf ∨ ∃ e, stepFn ctx sf cf chf = .error e) →
      seqOut ctx fuel σ c ch acc = outFold ls acc := by
  intro n σ sf c cf ch chf ls hp
  induction hp with
  | done =>
    intro fuel acc _ hstop
    rcases hstop with rfl | hstop
    · rfl
    · exact seqOut_stop hstop
  | step hstep _ ih =>
    intro fuel acc hn hstop
    cases fuel with
    | zero => omega
    | succ m =>
      rw [outFold_cons]
      unfold seqOut
      rw [if_neg (by simp [isTerminal_false_of_stepFn_ok hstep, isBlockedConfig_false_of_stepFn_ok hstep]), hstep]
      rcases hstop with h | h
      · exact ih (by omega) (.inl (by omega))
      · exact ih (by omega) (.inr h)

/-- **The output agreement over `Prefix`**: the one-goroutine pool's output on a transferable run is
the fold of the run's labels. -/
theorem execProgLoopOut_single_prefix {fuel n : Nat} {σ sf : Store} {c cf : Config} {ch chf : Choices}
    {ls : List StepLabel} {rs : RaceState} {acc : GoString} {r : Except Stop (Store × Choices)}
    (hr : execStmtLoop ctx fuel σ c ch = r) (htr : transferable r)
    (hp : Prefix ctx n σ c ch ls sf cf chf) (hn : n ≤ fuel)
    (hstop : n = fuel ∨ ZeroCost cf ∨ ∃ e, stepFn ctx sf cf chf = .error e) :
    execProgLoopOut ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch acc
      = (outFold ls acc, r) := by
  rw [execProgLoopOut_single hr htr, seqOut_of_prefix hp hn hstop]

/-- The same, as the pool's `Run` relation (`PoolTrace`). -/
theorem pool_run_single_prefix {fuel n : Nat} {σ sf : Store} {c cf : Config} {ch chf : Choices}
    {ls : List StepLabel} {rs : RaceState} {acc : GoString} {r : Except Stop (Store × Choices)}
    (hr : execStmtLoop ctx fuel σ c ch = r) (htr : transferable r)
    (hp : Prefix ctx n σ c ch ls sf cf chf) (hn : n ≤ fuel)
    (hstop : n = fuel ∨ ZeroCost cf ∨ ∃ e, stepFn ctx sf cf chf = .error e) :
    Run ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch acc (outFold ls acc, r) :=
  run_iff.mp (execProgLoopOut_single_prefix hr htr hp hn hstop)

/-! ## The embedding WITHOUT the `seqOpCount = 0` premise (request 9) -/

/-- A step that is no spawn and commits no registry op opens no boundary. -/
theorem afterStepFlag_none_of_noRegistry {σ : Store} {c c' : Config} (hsp : spawnPlan c = none)
    (hreg : c.registryCommits σ = false) : c.afterStepFlag σ c' = none := by
  rw [Config.afterStepFlag_eq_ite]
  simp [hsp, hreg]

/-- **No reachable boundary, no op count**: if no `Prefix`-reachable step within the fuel opens a
registry boundary, the sequential op count is zero. -/
theorem seqOpCount_eq_zero :
    ∀ {fuel : Nat} {σ : Store} {c : Config} {ch : Choices},
      (∀ n σ' c' ch' ls, Prefix ctx n σ c ch ls σ' c' ch' → n < fuel →
        ∀ c'' σ'' ch'' l, stepFn ctx σ' c' ch' = .ok (c'', σ'', ch'', l) → c'.afterStepFlag σ' c'' = none) →
      seqOpCount ctx fuel σ c ch = 0 := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ n ih =>
    intro σ c ch hnb
    unfold seqOpCount
    split
    · rfl
    · cases hstep : stepFn ctx σ c ch with
      | error e => rfl
      | ok r =>
        obtain ⟨c', σ', ch', l⟩ := r
        have hflag := hnb 0 σ c ch [] .done (by omega) c' σ' ch' l hstep
        simp only [hflag, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        exact ih fun m σ₂ c₂ ch₂ ls hp hm => hnb (m + 1) σ₂ c₂ ch₂ (l :: ls) (.step hstep hp) (by omega)

/-- **The single-goroutine embedding at EQUAL fuel**: a transferable run along which no reachable
step opens a registry boundary IS the one-goroutine pool run at the same fuel. -/
theorem execProgLoop_single_noBoundary {fuel : Nat} {σ : Store} {c : Config} {ch : Choices} {rs : RaceState}
    {r : Except Stop (Store × Choices)}
    (hr : execStmtLoop ctx fuel σ c ch = r) (htr : transferable r)
    (hnb : ∀ n σ' c' ch' ls, Prefix ctx n σ c ch ls σ' c' ch' → n < fuel →
      ∀ c'' σ'' ch'' l, stepFn ctx σ' c' ch' = .ok (c'', σ'', ch'', l) → c'.afterStepFlag σ' c'' = none) :
    execProgLoop ctx fuel ⟨#[.running c none], σ, 0⟩ rs ch = r := by
  have h := execProgLoop_single (rs := rs) hr htr
  rwa [seqOpCount_eq_zero hnb, Nat.add_zero] at h

end GoLean.GoCore.Machine
