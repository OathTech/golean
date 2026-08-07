import GoLean.GoCore.Multi
import GoLean.GoCore.MachineSound

/-!
# ThreadPool correspondence and sequential conservation (slice 2)

The pool's proof kit, mirroring the sequential one:

* **Sequential conservation** — `stepMulti_single` (the one-thread pool
  step IS `stepFn`, an `Except.map` away) lifted to
  `execProg_single_eq_execStmt`: a sequential run's `.ok`, `.fuelOut`
  and `.panic` results transfer verbatim to the pool driver. This is
  the transfer lemma that keeps every designated sequential statement
  valid unrestated (D9(a)) — and the reason the full corpus is
  bit-identical under the pool driver.

* **Correspondence** — `stepMulti_sound` (every executable pool step is
  a `StepM` step) and `stepM_complete` (every `StepM` step is realized
  by `stepMulti` under some choice stream).
-/

set_option maxRecDepth 8192
-- The unused-simp-arg linter misfires on the shared multi-branch simp
-- sets (an argument unused in one branch is load-bearing in another) —
-- the MachineSound sweeps' standing rationale, file-wide here.
set_option linter.unusedSimpArgs false

namespace GoLean.GoCore.Machine

open GoLean

/-! ## Small computation lemmas -/

@[simp] theorem isBlockedConfig_next {k : Cont} : isBlockedConfig (.next k) = false := rfl
@[simp] theorem isBlockedConfig_panicking {chain : List PanicEntry} {k : Cont} :
    isBlockedConfig (.panicking chain k) = false := rfl

theorem recvSideWaiters_singleton {c : Config} {loc : Loc} :
    recvSideWaiters #[c] 0 loc = [] := rfl

theorem sendSideWaiters_singleton {c : Config} {loc : Loc} :
    sendSideWaiters #[c] 0 loc = [] := rfl

/-- With no OTHER goroutines there is never a parked partner: the
arrival plan is a pure no-op — its waiter scans short-circuit before
any fallible helper runs. The conservation theorem's hinge. -/
theorem chanArrivalPlan_singleton {s : ExecState} {c : Config}
    {op : ChanStOp} {vs : List GoValue} {env : LocalEnv} {k : Cont} :
    chanArrivalPlan s #[c] 0 op vs env k = .ok none := by
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
theorem selectArrivalPlan_singleton {s : ExecState} {c : Config}
    {clauses : List (SelectClauseHead × Stmt)} {vs : List GoValue}
    {env : LocalEnv} {k : Cont} :
    selectArrivalPlan s #[c] 0 clauses vs env k = .ok none := by
  have hsw : ∀ sides : List (Option (Bool × Loc)),
      sidesHaveWaiters #[c] 0 sides = false := by
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
  unfold selectArrivalPlan
  cases hsc : selectClauseChans clauses vs with
  | none => rfl
  | some sides =>
      dsimp only
      simp only [hsw, Bool.not_false, reduceIte]
      rfl

@[inherit_doc chanArrivalPlan_singleton]
theorem arrivalPlan_singleton {s : ExecState} {c c' : Config} :
    arrivalPlan s #[c] 0 c' = .ok none := by
  unfold arrivalPlan arrivalPlanAux
  split
  · exact chanArrivalPlan_singleton
  · exact selectArrivalPlan_singleton
  · rfl

/-- The post-spawn marker never steps sequentially — `stepFn` fails
closed there (`.internal`; the marker is pool-only, BUG-040). -/
theorem spawnedCont_stepFn_internal {c : Config} {σ : ExecState}
    {ch : Choices} {k : Cont} (h : spawnedCont c = some k) :
    stepFn σ c ch
      = .error (.internal "post-spawn marker outside the thread pool") := by
  match c, h with
  | .spawned k', _ => rfl

/-- The one-thread `stepThread` is `stepFn`, results re-wrapped (the
arrival plan is a pure no-op with no other goroutines —
`arrivalPlan_singleton`; the post-spawn marker is excluded — its pool
strip has no sequential counterpart). -/
theorem stepThread_single {σ : ExecState} {c : Config} {ch : Choices}
    (hbl : isBlockedConfig c = false) (hsc : spawnedCont c = none)
    (hsp : spawnPlan c = none) :
    stepThread σ #[c] 0 ch
      = (stepFn σ c ch).map (fun r => (#[r.1], r.2.1, r.2.2)) := by
  unfold stepThread
  have h0 : (#[c] : Array Config)[0]? = some c := rfl
  rw [h0]
  simp only [hbl, Bool.false_eq_true, reduceIte, hsc, hsp]
  rw [show arrivalPlan σ #[c] 0 c = .ok none from arrivalPlan_singleton]
  simp only [Bind.bind, Except.bind]
  cases hstep : stepFn σ c ch with
  | error e => rfl
  | ok r =>
      obtain ⟨c', s', ch₁⟩ := r
      simp [Functor.map, Except.map]

theorem runnableIdxs_singleton {σ : ExecState} {c : Config}
    (h : threadRunnable σ c = true) :
    runnableIdxs σ #[c] = [0] := by
  simp [runnableIdxs, h]

/-- **The one-thread pool step is the sequential step** (the D2a
consumption rule at work: a single runnable goroutine never consumes a
scheduler choice, and with no partner the intercept never fires). -/
theorem stepMulti_single {σ : ExecState} {c : Config} {ch : Choices}
    (hbl : isBlockedConfig c = false) (hsc : spawnedCont c = none)
    (hsp : spawnPlan c = none)
    (hdone : threadDone c = false) :
    stepMulti ⟨#[c], σ, 0⟩ ch
      = (stepFn σ c ch).map (fun r => (⟨#[r.1], r.2.1, 0⟩, r.2.2)) := by
  have hrun : threadRunnable σ c = true := by
    simp [threadRunnable, hdone, hbl]
  have hinto : stepThreadInto ⟨#[c], σ, 0⟩ 0 ch
      = (stepFn σ c ch).map (fun r => (⟨#[r.1], r.2.1, 0⟩, r.2.2)) := by
    unfold stepThreadInto
    show (stepThread σ #[c] 0 ch).bind _ = _
    rw [stepThread_single hbl hsc hsp]
    cases stepFn σ c ch <;>
      simp [Bind.bind, Except.bind, Functor.map, Except.map]
  unfold stepMulti
  have h0 : (#[c] : Array Config)[0]? = some c := rfl
  simp only [h0]
  by_cases hb : Config.atBoundary c = true
  · simp only [hb, reduceIte]
    rw [show runnableIdxs σ #[c] = [0] from runnableIdxs_singleton hrun]
    exact hinto
  · simp only [Bool.not_eq_true] at hb
    simp only [hb, Bool.false_eq_true, reduceIte]
    exact hinto

/-! ## stepFn shape inversions (the spawn/terminal refusals) -/

/-- A completed spawn position never steps sequentially — `stepFn`
fails closed there with an `.unsupported`/`.stuck` refusal (exactly
the result classes the conservation transfer does NOT claim). -/
theorem spawnPlan_stepFn_refuses {c : Config} {σ : ExecState}
    {ch : Choices} {p : GoValue × List GoValue × Cont}
    (h : spawnPlan c = some p) :
    match stepFn σ c ch with
    | .error (.unsupported _) => True
    | .error (.stuck _) => True
    | _ => False := by
  match c, h with
  | .retV cv (.goCalleeK [] env k), h =>
      by_cases hd : deferrableCallee cv = true <;>
        simp [stepFn, hd, throw, throwThe, MonadExceptOf.throw]
  | .retV v (.goArgsK cv vals [] env k), h =>
      simp [stepFn, throw, throwThe, MonadExceptOf.throw]

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
def transferable : Except GoError (ExecOutcome × Choices) → Prop
  | .ok _ => True
  | .error .fuelOut => True
  | .error (.panic _) => True
  | _ => False

/-- The race detector is DEFINITIONALLY inert on one-goroutine pools
(`raceUpdate`'s first branch): a single goroutine cannot race with
itself. The conservation proof's detector hinge — sequential runs
thread the `RaceState` through untouched. -/
theorem raceUpdate_single {σ : ExecState} {ts : Array Config} {c : Config}
    {σ' : ExecState} {i : Nat} {rs : RaceState} :
    raceUpdate σ ts ⟨#[c], σ', i⟩ rs = .ok rs := by
  simp [raceUpdate]

/-- The singleton-pool projections of a mid-run (non-terminal,
non-blocked) configuration. -/
theorem singleton_pool_facts {σ : ExecState} {c : Config}
    (h1 : c ≠ .next .stop) (h2 : c ≠ .returning .stop)
    (h3 : c ≠ .breaking .stop) (h4 : c ≠ .continuing .stop)
    (h5 : ∀ msg, c ≠ .panicked msg)
    (h6 : ∀ a b k, c ≠ .blockedSend a b k)
    (h7 : ∀ a b e env k, c ≠ .blockedRecv a b e env k)
    (h8 : ∀ cl env k, c ≠ .blockedSelect cl env k) :
    MultiConfig.panicMsg? ⟨#[c], σ, 0⟩ = none
      ∧ MultiConfig.mainOutcome? ⟨#[c], σ, 0⟩ = none
      ∧ threadDone c = false ∧ isBlockedConfig c = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold MultiConfig.panicMsg?
    have ht : (⟨#[c], σ, 0⟩ : MultiConfig).threads.toList = [c] := rfl
    rw [ht]
    unfold List.findSome?
    split
    · rename_i b heq
      split at heq <;> simp_all
    · rfl
  · unfold MultiConfig.mainOutcome?
    have h0 : ((⟨#[c], σ, 0⟩ : MultiConfig).threads[0]? : Option Config) = some c := rfl
    rw [h0]
    split <;> simp_all
  · unfold threadDone
    split <;> simp_all
  · unfold isBlockedConfig
    split <;> try simp_all
    exact (h7 _ _ _ _ _ rfl rfl rfl rfl rfl)

/-- **The conservation transfer, loop level**: every sequential result
in the `transferable` classes is the singleton pool's result verbatim
— same outcome, same final state, same leftover stream, same fuel
accounting. -/
theorem execProgLoop_single :
    ∀ {fuel : Nat} {σ : ExecState} {c : Config} {ch : Choices}
      {rs : RaceState}
      {r : Except GoError (ExecOutcome × Choices)},
      execStmtLoop fuel σ c ch = r → transferable r →
      execProgLoop fuel ⟨#[c], σ, 0⟩ rs ch = r := by
  intro fuel
  induction fuel with
  | zero =>
    intro σ c ch rs r hr htr
    unfold execStmtLoop at hr
    split at hr
    · subst hr; rfl
    · subst hr; rfl
    · subst hr; rfl
    · subst hr; rfl
    · subst hr; rfl
    · subst hr; simp [transferable, throw, throwThe, MonadExceptOf.throw] at htr
    · subst hr; simp [transferable, throw, throwThe, MonadExceptOf.throw] at htr
    · subst hr; simp [transferable, throw, throwThe, MonadExceptOf.throw] at htr
    · rename_i harm1 harm2 harm3 harm4 harm5 harm6 harm7 harm8
      subst hr
      obtain ⟨hp, hm, hd, hb⟩ := singleton_pool_facts
        (σ := σ) harm1 harm2 harm3 harm4 harm5 harm6 harm7 harm8
      have hrun : threadRunnable σ c = true := by
        simp [threadRunnable, hd, hb]
      unfold execProgLoop
      simp [hp, hm, runnableIdxs_singleton hrun]
  | succ n ih =>
    intro σ c ch rs r hr htr
    unfold execStmtLoop at hr
    split at hr
    · subst hr; rfl
    · subst hr; rfl
    · subst hr; rfl
    · subst hr; rfl
    · subst hr; rfl
    · subst hr; simp [transferable, throw, throwThe, MonadExceptOf.throw] at htr
    · subst hr; simp [transferable, throw, throwThe, MonadExceptOf.throw] at htr
    · subst hr; simp [transferable, throw, throwThe, MonadExceptOf.throw] at htr
    · rename_i harm1 harm2 harm3 harm4 harm5 harm6 harm7 harm8
      obtain ⟨hp, hm, hd, hb⟩ := singleton_pool_facts
        (σ := σ) harm1 harm2 harm3 harm4 harm5 harm6 harm7 harm8
      have hrun : threadRunnable σ c = true := by
        simp [threadRunnable, hd, hb]
      unfold execProgLoop
      simp only [Bind.bind, Except.bind] at hr
      cases hsc : spawnedCont c with
      | some kk =>
          -- The post-spawn marker refuses sequentially (`.internal`) —
          -- outside the transferable classes.
          rw [spawnedCont_stepFn_internal (σ := σ) (ch := ch) hsc] at hr
          subst hr
          simp [transferable] at htr
      | none =>
      cases hsp : spawnPlan c with
      | some p =>
          have hcls := spawnPlan_stepFn_refuses (σ := σ) (ch := ch) hsp
          cases hstep : stepFn σ c ch with
          | ok r₂ => rw [hstep] at hcls; simp at hcls
          | error e =>
              rw [hstep] at hr
              rw [hstep] at hcls
              subst hr
              cases e <;> simp_all [transferable]
      | none =>
          have hmulti := stepMulti_single (σ := σ) (ch := ch) hb hsc hsp hd
          cases hstep : stepFn σ c ch with
          | error e =>
              rw [hstep] at hr
              subst hr
              rw [hstep] at hmulti
              simp only [Except.map] at hmulti
              simp [hp, hm, runnableIdxs_singleton hrun, hmulti,
                Bind.bind, Except.bind]
          | ok r₂ =>
              obtain ⟨c₂, σ₂, ch₂⟩ := r₂
              rw [hstep] at hr
              rw [hstep] at hmulti
              simp only [Except.map] at hmulti
              have hrec := ih (rs := rs) hr htr
              simp [hp, hm, runnableIdxs_singleton hrun, hmulti,
                Bind.bind, Except.bind, raceUpdate_single, hrec]

/-- **`execProg_single_eq_execStmt` — THE sequential-conservation
theorem** (machine-shape note §7; D9(a)): for every program, every
fuel, every stream, a sequential `execStmt` result in the transferable
classes (completion at any terminal, fuel exhaustion, panic abort) IS
the pool driver's `execProg` result, verbatim — same outcome, same
final state, same leftover stream, same fuel accounting. This is the
transfer lemma that keeps every designated sequential statement valid
unrestated on the pool carrier (D9(a)): a sequential `GoSpec`'s runs
and the concurrent carrier's runs coincide on single-goroutine
programs. -/
theorem execProg_single_eq_execStmt {fuel : Nat} {env : LocalEnv}
    {σ : ExecState} {ch : Choices} {prog : Stmt}
    {r : Except GoError (ExecOutcome × Choices)}
    (hr : execStmt fuel env σ ch prog = r) (htr : transferable r) :
    execProg fuel env σ ch prog = r :=
  execProgLoop_single hr htr

/-! ## Correspondence: `stepMulti` instantiates `StepM` -/

/-- A successful spawn's PARENT successor is always the post-spawn
marker `.spawned k` (BUG-040: the fork's completion is a registry op;
the marker strips to `.next k` at the next pool step). -/
theorem spawnStep_shape {s : ExecState} {cv : GoValue} {args : List GoValue}
    {k : Cont} {p c : Config} {s' : ExecState}
    (h : spawnStep s cv args k = .ok (p, c, s')) : p = .spawned k := by
  unfold spawnStep at h
  cases cv <;>
    simp_all [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  rename_i fid captured
  split at h <;> simp_all

theorem schedPick_of_boundary {m : MultiConfig} {c : Config} {i : Nat}
    (hcur : m.threads[m.cur]? = some c) (hb : c.atBoundary = true)
    (hmem : i ∈ runnableIdxs m.shared m.threads) : schedPick m i := by
  unfold schedPick
  rw [hcur]
  simp [hb, hmem]

theorem schedPick_cur {m : MultiConfig} {c : Config}
    (hcur : m.threads[m.cur]? = some c) (hb : c.atBoundary = false) :
    schedPick m m.cur := by
  unfold schedPick
  rw [hcur]
  simp [hb]

/-- One goroutine-step of the executable pool is a `StepM` step (given a
legal scheduler pick). Case-for-case with `stepThread`'s arms: wake,
spawn, arrival pairing, partnerless step. -/
theorem stepThreadInto_sound {m : MultiConfig} {i : Nat} {ch ch' : Choices}
    {m' : MultiConfig} (hsched : schedPick m i)
    (h : stepThreadInto m i ch = .ok (m', ch')) : StepM m m' := by
  unfold stepThreadInto at h
  simp only [Bind.bind, Except.bind] at h
  cases hst : stepThread m.shared m.threads i ch with
  | error e => rw [hst] at h; cases h
  | ok r =>
    obtain ⟨ts, s', chX⟩ := r
    rw [hst] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    unfold stepThread at hst
    cases hti : m.threads[i]? with
    | none => rw [hti] at hst; cases hst
    | some c =>
      rw [hti] at hst
      by_cases hbl : isBlockedConfig c = true
      · -- WAKE
        simp only [hbl, reduceIte, Bind.bind, Except.bind] at hst
        cases hres : resumeThread m.shared c with
        | error e => rw [hres] at hst; cases hst
        | ok r₂ =>
          obtain ⟨c', s₂⟩ := r₂
          rw [hres] at hst
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
          obtain ⟨rfl, rfl, rfl⟩ := hst
          exact StepM.wake hsched hti hbl hres
      · simp only [Bool.not_eq_true] at hbl
        simp only [hbl, Bool.false_eq_true, reduceIte] at hst
        cases hsc : spawnedCont c with
        | some kk =>
          -- The post-spawn marker STRIP (BUG-040).
          rw [hsc] at hst
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
          obtain ⟨rfl, rfl, rfl⟩ := hst
          have hcfg : c = .spawned kk := by
            cases c <;> simp_all [spawnedCont]
          subst hcfg
          exact StepM.spawned hsched hti
        | none =>
        rw [hsc] at hst
        cases hsp : spawnPlan c with
        | some p =>
          obtain ⟨cv, args, k⟩ := p
          rw [hsp] at hst
          simp only [Bind.bind, Except.bind] at hst
          cases hspawn : spawnStep m.shared cv args k with
          | error e => rw [hspawn] at hst; cases hst
          | ok r₂ =>
            obtain ⟨parent', child, s₂⟩ := r₂
            rw [hspawn] at hst
            simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
            obtain ⟨rfl, rfl, rfl⟩ := hst
            have hplanNone : arrivalPlan m.shared m.threads i c = .ok none := by
              match c, hsp with
              | .retV cv' (.goCalleeK [] env k'), _ => rfl
              | .retV v' (.goArgsK cv' vals [] env k'), _ => rfl
            have hts : (m.threads.setIfInBounds i parent').push child
                = (m.threads.setIfInBounds i parent') ++ ([child] : List Config).toArray := by
              rw [Array.push_eq_append]
            rw [hts]
            exact StepM.thread hsched hti hbl hplanNone (StepE.spawn hsp hspawn)
        | none =>
          rw [hsp] at hst
          simp only [Bind.bind, Except.bind] at hst
          cases hplan : arrivalPlan m.shared m.threads i c with
          | error e => rw [hplan] at hst; cases hst
          | ok plan =>
            rw [hplan] at hst
            cases plan with
            | some p =>
              obtain ⟨bc, cs⟩ := p
              cases cs with
              | nil => cases hst
              | cons cand rest =>
                cases rest with
                | nil =>
                  simp only [Bind.bind, Except.bind] at hst
                  cases hap : applyPairing m.shared m.threads i bc cand with
                  | error e => rw [hap] at hst; cases hst
                  | ok r₃ =>
                    obtain ⟨ts', s₃⟩ := r₃
                    rw [hap] at hst
                    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
                    obtain ⟨rfl, rfl, rfl⟩ := hst
                    exact StepM.pair hsched hti hbl hsp hplan
                      (idx := 0) (by simp) hap
                | cons b rest' =>
                  simp only [Bind.bind, Except.bind] at hst
                  rcases hcons : ch.consume (cand :: b :: rest').length with ⟨idx, ch₃⟩
                  rw [hcons] at hst
                  cases hget : (cand :: b :: rest')[idx]? with
                  | none => rw [hget] at hst; cases hst
                  | some cand' =>
                    rw [hget] at hst
                    simp only [Bind.bind, Except.bind] at hst
                    cases hap : applyPairing m.shared m.threads i bc cand' with
                    | error e => rw [hap] at hst; cases hst
                    | ok r₃ =>
                      obtain ⟨ts', s₃⟩ := r₃
                      rw [hap] at hst
                      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
                      obtain ⟨rfl, rfl, rfl⟩ := hst
                      obtain ⟨hlt, hidxeq⟩ := List.getElem?_eq_some_iff.mp hget
                      exact StepM.pair hsched hti hbl hsp hplan
                        (idx := idx) hlt (by rw [hidxeq]; exact hap)
            | none =>
              simp only [Bind.bind, Except.bind] at hst
              cases hstep : stepFn m.shared c ch with
              | error e => rw [hstep] at hst; cases hst
              | ok r₂ =>
                obtain ⟨c', s₂, ch₂⟩ := r₂
                rw [hstep] at hst
                simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
                obtain ⟨rfl, rfl, rfl⟩ := hst
                have hts : m.threads.setIfInBounds i c'
                    = (m.threads.setIfInBounds i c') ++ ([] : List Config).toArray := by
                  simp
                rw [hts]
                exact StepM.thread hsched hti hbl hplan
                  (StepE.lift (stepFn_sound hstep))

/-- **Soundness of the pool step**: every `.ok` step of `stepMulti` is a
step of the pool relation `StepM`. -/
theorem stepMulti_sound {m : MultiConfig} {ch ch' : Choices}
    {m' : MultiConfig} (h : stepMulti m ch = .ok (m', ch')) : StepM m m' := by
  unfold stepMulti at h
  cases hcur : m.threads[m.cur]? with
  | none => rw [hcur] at h; cases h
  | some c =>
    rw [hcur] at h
    by_cases hb : c.atBoundary = true
    · simp only [hb, reduceIte] at h
      cases hrs : runnableIdxs m.shared m.threads with
      | nil => rw [hrs] at h; cases h
      | cons r0 rest =>
        rw [hrs] at h
        cases rest with
        | nil =>
          have hmem : r0 ∈ runnableIdxs m.shared m.threads := by
            rw [hrs]; exact List.mem_singleton.mpr rfl
          exact stepThreadInto_sound (schedPick_of_boundary hcur hb hmem) h
        | cons r1 rest' =>
          dsimp only at h
          rcases hcons : ch.consume (r0 :: r1 :: rest').length with ⟨pick, ch₁⟩
          rw [hcons] at h
          cases hget : (r0 :: r1 :: rest')[pick]? with
          | none => rw [hget] at h; cases h
          | some i =>
            rw [hget] at h
            have hmem : i ∈ runnableIdxs m.shared m.threads := by
              rw [hrs]
              exact List.mem_of_getElem? hget
            exact stepThreadInto_sound (schedPick_of_boundary hcur hb hmem) h
    · simp only [Bool.not_eq_true] at hb
      simp only [hb, Bool.false_eq_true, reduceIte] at h
      exact stepThreadInto_sound (schedPick_cur hcur hb) h

/-! ## Completeness: every `StepM` step is realized by `stepMulti` -/

/-- The per-goroutine relation is silent at spawn positions (the spawn
is `StepE`'s rule, not `Step`'s). -/
theorem step_spawnPos_elim {c : Config} {σ : ExecState} {c' : Config}
    {σ' : ExecState} {p : GoValue × List GoValue × Cont}
    (hsp : spawnPlan c = some p) : ¬ Step c σ c' σ' := by
  intro h
  match c, hsp with
  | .retV cv (.goCalleeK [] env k), _ => cases h
  | .retV v (.goArgsK cv vals [] env k), _ => cases h

/-- The per-goroutine relation is silent at the post-spawn marker (the
strip is `StepM.spawned`'s rule — pool-only, BUG-040). -/
theorem step_spawnedMarker_elim {c : Config} {σ : ExecState} {c' : Config}
    {σ' : ExecState} {k : Cont}
    (hsc : spawnedCont c = some k) : ¬ Step c σ c' σ' := by
  intro h
  match c, hsc with
  | .spawned _, _ => cases h

/-- A completed spawn position is not the marker (plan disjointness for
the `stepThread` dispatch proofs). -/
theorem spawnedCont_of_spawnPlan {c : Config}
    {p : GoValue × List GoValue × Cont}
    (h : spawnPlan c = some p) : spawnedCont c = none := by
  match c, h with
  | .retV cv (.goCalleeK [] env k), _ => rfl
  | .retV v (.goArgsK cv vals [] env k), _ => rfl

/-- A blocked configuration is not the marker. -/
theorem spawnedCont_of_blocked {c : Config}
    (h : isBlockedConfig c = true) : spawnedCont c = none := by
  match c, h with
  | .blockedSend _ _ _, _ => rfl
  | .blockedRecv _ _ _ _ _, _ => rfl
  | .blockedSelect _ _ _, _ => rfl

/-- Compose a scheduling prefix in front of an inner `stepThread`
realization: a legal pick is realized by the scheduler site (consumed
only at `|runnable| > 1`, the pick index prepended to the stream). -/
theorem stepMulti_of_inner {m : MultiConfig} {i : Nat} {chI chI' : Choices}
    {ts : Array Config} {s' : ExecState}
    (hsched : schedPick m i)
    (hinner : stepThread m.shared m.threads i chI = .ok (ts, s', chI')) :
    ∃ ch ch', stepMulti m ch = .ok (⟨ts, s', i⟩, ch') := by
  unfold schedPick at hsched
  cases hcur : m.threads[m.cur]? with
  | none => rw [hcur] at hsched; exact absurd hsched (by simp)
  | some c₀ =>
    rw [hcur] at hsched
    dsimp only at hsched
    by_cases hbnd : c₀.atBoundary = true
    · rw [if_pos hbnd] at hsched
      cases hrs : runnableIdxs m.shared m.threads with
      | nil =>
        rw [hrs] at hsched
        exact absurd hsched (by simp)
      | cons r0 rest =>
        cases rest with
        | nil =>
          have hi : i = r0 := by
            rw [hrs] at hsched
            simpa using hsched
          subst hi
          refine ⟨chI, chI', ?_⟩
          unfold stepMulti
          rw [hcur]
          simp only [hbnd, reduceIte]
          rw [hrs]
          dsimp only
          unfold stepThreadInto
          rw [hinner]
          rfl
        | cons r1 rest' =>
          rw [hrs] at hsched
          obtain ⟨p, hp⟩ := List.getElem?_of_mem hsched
          have hplen : p < (r0 :: r1 :: rest').length :=
            (List.getElem?_eq_some_iff.mp hp).1
          refine ⟨p :: chI, chI', ?_⟩
          unfold stepMulti
          rw [hcur]
          simp only [hbnd, reduceIte]
          rw [hrs]
          dsimp only
          have hcons : Choices.consume (p :: chI) (r0 :: r1 :: rest').length
              = (p, chI) := by
            simp only [Choices.consume]
            congr 1
            have : max 1 (r0 :: r1 :: rest').length
                = (r0 :: r1 :: rest').length := by
              simp only [List.length_cons]
              omega
            rw [this]
            exact Nat.mod_eq_of_lt hplen
          rw [hcons, hp]
          dsimp only
          unfold stepThreadInto
          rw [hinner]
          rfl
    · simp only [Bool.not_eq_true] at hbnd
      rw [if_neg (by simp [hbnd])] at hsched
      subst hsched
      refine ⟨chI, chI', ?_⟩
      unfold stepMulti
      rw [hcur]
      simp only [hbnd, Bool.false_eq_true, reduceIte]
      unfold stepThreadInto
      rw [hinner]
      rfl

/-- **Completeness of the pool step**: every `StepM` step is realized
by `stepMulti` under some choice stream (scheduler pick and L4 waiter
pick encoded in the stream; the goroutine's own step realized through
the sequential kit's `step_complete`; the pairing path never touches
`stepFn`, so its stream is exactly the waiter pick). -/
theorem stepM_complete {m m' : MultiConfig} (h : StepM m m') :
    ∃ ch ch', stepMulti m ch = .ok (m', ch') := by
  cases h with
  | thread hsched hti hblc hplan hstepE =>
    rename_i i c c' σ' efs
    cases hstepE with
    | lift hstep =>
      obtain ⟨ch₀, ch₀', hfn⟩ := step_complete hstep
      have hsp : spawnPlan c = none := by
        cases hspq : spawnPlan c with
        | none => rfl
        | some p => exact absurd hstep (step_spawnPos_elim hspq)
      have hsc : spawnedCont c = none := by
        cases hscq : spawnedCont c with
        | none => rfl
        | some kk => exact absurd hstep (step_spawnedMarker_elim hscq)
      have hinner : stepThread m.shared m.threads i ch₀
          = .ok (m.threads.setIfInBounds i c', σ', ch₀') := by
        unfold stepThread
        rw [hti]
        simp only [hblc, Bool.false_eq_true, reduceIte, hsc, hsp]
        rw [hplan]
        simp only [Bind.bind, Except.bind]
        rw [hfn]
        rfl
      have heq : (m.threads.setIfInBounds i c') ++ ([] : List Config).toArray
          = m.threads.setIfInBounds i c' := by
        rw [show (([] : List Config)).toArray = #[] from rfl, Array.append_empty]
      rw [heq]
      exact stepMulti_of_inner hsched hinner
    | spawn hplan' hspawn =>
      rename_i cv args k child
      have hinner : stepThread m.shared m.threads i []
          = .ok ((m.threads.setIfInBounds i c').push child, σ', []) := by
        unfold stepThread
        rw [hti]
        simp only [hblc, Bool.false_eq_true, reduceIte,
          spawnedCont_of_spawnPlan hplan', hplan', Bind.bind,
          Except.bind]
        rw [hspawn]
        rfl
      have heq : (m.threads.setIfInBounds i c') ++ ([child] : List Config).toArray
          = (m.threads.setIfInBounds i c').push child := by
        rw [Array.push_eq_append]
      rw [heq]
      exact stepMulti_of_inner hsched hinner
  | pair hsched hti hblc hsp hplan hidx hap =>
    rename_i i c bc σ'' cs idx ts'
    have hsc : spawnedCont c = none := by
      cases hscq : spawnedCont c with
      | none => rfl
      | some kk =>
          have hcfg : c = .spawned kk := by
            cases c <;> simp_all [spawnedCont]
          subst hcfg
          rw [show arrivalPlan m.shared m.threads i (.spawned kk) = .ok none
            from rfl] at hplan
          cases hplan
    cases cs with
    | nil => exact absurd hidx (by simp)
    | cons cand rest =>
      cases rest with
      | nil =>
        have hap' : applyPairing m.shared m.threads i bc cand = .ok (ts', σ'') := by
          have h0 : idx = 0 := by
            simp at hidx
            omega
          subst h0
          exact hap
        have hinner : stepThread m.shared m.threads i []
            = .ok (ts', σ'', []) := by
          unfold stepThread
          rw [hti]
          simp only [hblc, Bool.false_eq_true, reduceIte, hsc, hsp, Bind.bind,
            Except.bind]
          rw [hplan]
          dsimp only
          rw [hap']
          rfl
        exact stepMulti_of_inner hsched hinner
      | cons b rest' =>
        have hinner : stepThread m.shared m.threads i [idx]
            = .ok (ts', σ'', []) := by
          unfold stepThread
          rw [hti]
          simp only [hblc, Bool.false_eq_true, reduceIte, hsc, hsp, Bind.bind,
            Except.bind]
          rw [hplan]
          dsimp only
          have hcons : Choices.consume [idx] (cand :: b :: rest').length
              = (idx, []) := by
            simp only [Choices.consume]
            congr 1
            have hmax : max 1 (cand :: b :: rest').length
                = (cand :: b :: rest').length := by
              simp only [List.length_cons]
              omega
            rw [hmax]
            exact Nat.mod_eq_of_lt hidx
          rw [hcons]
          dsimp only
          rw [List.getElem?_eq_getElem hidx]
          dsimp only
          rw [hap]
          rfl
        exact stepMulti_of_inner hsched hinner
  | wake hsched hti hblc hres =>
    rename_i i c c' σ'
    have hinner : stepThread m.shared m.threads i []
        = .ok (m.threads.setIfInBounds i c', σ', []) := by
      unfold stepThread
      rw [hti]
      simp only [hblc, reduceIte, Bind.bind, Except.bind]
      rw [hres]
      rfl
    exact stepMulti_of_inner hsched hinner
  | spawned hsched hti =>
    rename_i i k
    have hinner : stepThread m.shared m.threads i []
        = .ok (m.threads.setIfInBounds i (.next k), m.shared, []) := by
      unfold stepThread
      rw [hti]
      rfl
    exact stepMulti_of_inner hsched hinner

end GoLean.GoCore.Machine
