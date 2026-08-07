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

/-- With no OTHER goroutines there is never a pairing candidate. -/
theorem pairCandidates_singleton {s : ExecState} {c bc : Config} :
    pairCandidates s #[c] 0 bc = .ok [] := by
  cases bc
  case blockedSend ch v k =>
      cases ch with
      | none => rfl
      | some loc => simp [pairCandidates, recvSideWaiters_singleton]
  case blockedRecv ch targets elem env k =>
      cases ch with
      | none => rfl
      | some loc => simp [pairCandidates, sendSideWaiters_singleton]
  case blockedSelect evs env k =>
      have hone : ∀ ci : Nat, selectClauseWaiters s #[c] 0 evs ci
          = .ok (ci, ([] : List (Nat × PairTarget))) := by
        intro ci
        unfold selectClauseWaiters
        match ha : evs[ci]? with
        | none => simp [ha]
        | some (.recvEv chv tgts e b) =>
            cases hcl : chanValueLoc chv <;>
              simp [hcl, sendSideWaiters_singleton]
        | some (.sendEv chv vv e b) =>
            cases hcl : chanValueLoc chv <;>
              simp [hcl, recvSideWaiters_singleton]
      have hmap : ∀ l : List Nat,
          l.mapM (selectClauseWaiters s #[c] 0 evs)
            = .ok (l.map (fun ci => (ci, ([] : List (Nat × PairTarget))))) := by
        intro l
        induction l with
        | nil => rfl
        | cons a rest ih =>
            simp [List.mapM_cons, hone, ih, Bind.bind, Except.bind, pure, Except.pure]
      have hfil : ∀ l : List Nat,
          (l.map (fun ci => (ci, ([] : List (Nat × PairTarget))))).filter
            (fun p => !p.2.isEmpty) = [] := by
        intro l
        induction l with
        | nil => rfl
        | cons a rest ih =>
            simp only [List.map_cons, List.filter_cons, List.isEmpty_nil,
              Bool.not_true, Bool.false_eq_true, if_false, ih]
      show (do
        let perClause : List (Nat × List (Nat × PairTarget)) ←
          (List.range evs.length).mapM (selectClauseWaiters s #[c] 0 evs)
        match perClause.filter (fun p => !p.2.isEmpty) with
        | [] => pure []
        | [(ci, ws)] =>
            if ws.any (fun w => w.2.isSelect) then
              throw (GoError.unsupported
                "select-with-select rendezvous (unmodeled this slice)")
            else
              pure (ws.map fun w => (ci, w.2))
        | _ => throw (GoError.unsupported
            "select with waiter-pairable cases on multiple clauses (the L2 multi-ready envelope is slice 4)")
        : Except GoError (List (Nat × PairTarget))) = .ok []
      rw [show ((List.range evs.length).mapM (selectClauseWaiters s #[c] 0 evs))
          = .ok ((List.range evs.length).map
              (fun ci => (ci, ([] : List (Nat × PairTarget)))))
        from hmap _]
      show (match ((List.range evs.length).map
          (fun ci => (ci, ([] : List (Nat × PairTarget))))).filter
            (fun p => !p.2.isEmpty) with
        | [] => pure []
        | [(ci, ws)] =>
            if ws.any (fun w => w.2.isSelect) then
              throw (GoError.unsupported
                "select-with-select rendezvous (unmodeled this slice)")
            else
              pure (ws.map fun w => (ci, w.2))
        | _ => throw (GoError.unsupported
            "select with waiter-pairable cases on multiple clauses (the L2 multi-ready envelope is slice 4)")
        : Except GoError (List (Nat × PairTarget))) = .ok []
      rw [hfil]
      rfl
  all_goals rfl

/-- The one-thread `stepThread` is `stepFn`, results re-wrapped. -/
theorem stepThread_single {σ : ExecState} {c : Config} {ch : Choices}
    (hbl : isBlockedConfig c = false) (hsp : spawnPlan c = none) :
    stepThread σ #[c] 0 ch
      = (stepFn σ c ch).map (fun r => (#[r.1], r.2.1, r.2.2)) := by
  unfold stepThread
  have h0 : (#[c] : Array Config)[0]? = some c := rfl
  rw [h0]
  simp only [hbl, Bool.false_eq_true, reduceIte, hsp]
  cases hstep : stepFn σ c ch with
  | error e => rfl
  | ok r =>
      obtain ⟨c', s', ch₁⟩ := r
      by_cases hbc : isBlockedConfig c' = true
      · simp [hstep, hbc, pairCandidates_singleton, Bind.bind, Except.bind,
          Functor.map, Except.map]
      · simp only [Bool.not_eq_true] at hbc
        simp [hstep, hbc, Bind.bind, Except.bind, Functor.map, Except.map]

theorem runnableIdxs_singleton {σ : ExecState} {c : Config}
    (h : threadRunnable σ c = true) :
    runnableIdxs σ #[c] = [0] := by
  simp [runnableIdxs, h]

/-- **The one-thread pool step is the sequential step** (the D2a
consumption rule at work: a single runnable goroutine never consumes a
scheduler choice, and with no partner the intercept never fires). -/
theorem stepMulti_single {σ : ExecState} {c : Config} {ch : Choices}
    (hbl : isBlockedConfig c = false) (hsp : spawnPlan c = none)
    (hdone : threadDone c = false) :
    stepMulti ⟨#[c], σ, 0⟩ ch
      = (stepFn σ c ch).map (fun r => (⟨#[r.1], r.2.1, 0⟩, r.2.2)) := by
  have hrun : threadRunnable σ c = true := by
    simp [threadRunnable, hdone, hbl]
  have hinto : stepThreadInto ⟨#[c], σ, 0⟩ 0 ch
      = (stepFn σ c ch).map (fun r => (⟨#[r.1], r.2.1, 0⟩, r.2.2)) := by
    unfold stepThreadInto
    show (stepThread σ #[c] 0 ch).bind _ = _
    rw [stepThread_single hbl hsp]
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
refusals: `.deadlock` (an ARTIFICIAL wake-ready blocked seed would
resume in the pool where the sequential driver classifies immediately —
sequential runs never produce such configurations, but the theorem
quantifies arbitrary seeds) and the fail-closed
`.unsupported`/`.stuck`/`.internal` diagnostics (a spawn position is
refused sequentially and forked by the pool). -/
def transferable : Except GoError (ExecOutcome × Choices) → Prop
  | .ok _ => True
  | .error .fuelOut => True
  | .error (.panic _) => True
  | _ => False

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
      {r : Except GoError (ExecOutcome × Choices)},
      execStmtLoop fuel σ c ch = r → transferable r →
      execProgLoop fuel ⟨#[c], σ, 0⟩ ch = r := by
  intro fuel
  induction fuel with
  | zero =>
    intro σ c ch r hr htr
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
    intro σ c ch r hr htr
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
          have hmulti := stepMulti_single (σ := σ) (ch := ch) hb hsp hd
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
              have hrec := ih hr htr
              simp [hp, hm, runnableIdxs_singleton hrun, hmulti,
                Bind.bind, Except.bind, hrec]

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

/-- A successful spawn's PARENT successor is always `.next k` (the
statement completes; the fork is the child). -/
theorem spawnStep_shape {s : ExecState} {cv : GoValue} {args : List GoValue}
    {k : Cont} {p c : Config} {s' : ExecState}
    (h : spawnStep s cv args k = .ok (p, c, s')) : p = .next k := by
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
spawn, ordinary step, park, pairing. -/
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
            have hts : (m.threads.setIfInBounds i parent').push child
                = (m.threads.setIfInBounds i parent') ++ ([child] : List Config).toArray := by
              rw [Array.push_eq_append]
            rw [hts]
            refine StepM.thread hsched hti hbl (StepE.spawn hsp hspawn) ?_
            rw [spawnStep_shape hspawn]
            rfl
        | none =>
          rw [hsp] at hst
          simp only [Bind.bind, Except.bind] at hst
          cases hstep : stepFn m.shared c ch with
          | error e => rw [hstep] at hst; cases hst
          | ok r₂ =>
            obtain ⟨c', s₂, ch₂⟩ := r₂
            rw [hstep] at hst
            by_cases hbc : isBlockedConfig c' = true
            · -- blocked outcome: park or pair
              simp only [hbc, reduceIte, Bind.bind, Except.bind] at hst
              cases hcs : pairCandidates s₂ m.threads i c' with
              | error e => rw [hcs] at hst; cases hst
              | ok cs =>
                rw [hcs] at hst
                cases cs with
                | nil =>
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
                  obtain ⟨rfl, rfl, rfl⟩ := hst
                  exact StepM.park hsched hti hbl
                    (StepE.lift (stepFn_sound hstep)) hbc hcs
                | cons cand rest =>
                  cases rest with
                  | nil =>
                    simp only [Bind.bind, Except.bind] at hst
                    cases hap : applyPairing s₂ m.threads i c' cand with
                    | error e => rw [hap] at hst; cases hst
                    | ok r₃ =>
                      obtain ⟨ts', s₃⟩ := r₃
                      rw [hap] at hst
                      simp only [pure_eq_ok, Except.ok.injEq,
                        Prod.mk.injEq] at hst
                      obtain ⟨rfl, rfl, rfl⟩ := hst
                      exact StepM.pair hsched hti hbl
                        (StepE.lift (stepFn_sound hstep)) hbc hcs
                        (idx := 0) (by simp) hap
                  | cons b rest' =>
                    simp only [Bind.bind, Except.bind] at hst
                    rcases hcons : ch₂.consume (cand :: b :: rest').length with ⟨idx, ch₃⟩
                    rw [hcons] at hst
                    cases hget : (cand :: b :: rest')[idx]? with
                    | none => rw [hget] at hst; cases hst
                    | some cand' =>
                      rw [hget] at hst
                      simp only [Bind.bind, Except.bind] at hst
                      cases hap : applyPairing s₂ m.threads i c' cand' with
                      | error e => rw [hap] at hst; cases hst
                      | ok r₃ =>
                        obtain ⟨ts', s₃⟩ := r₃
                        rw [hap] at hst
                        simp only [pure, Except.pure, Except.ok.injEq,
                          Prod.mk.injEq] at hst
                        obtain ⟨rfl, rfl, rfl⟩ := hst
                        obtain ⟨hlt, hidxeq⟩ := List.getElem?_eq_some_iff.mp hget
                        exact StepM.pair hsched hti hbl
                          (StepE.lift (stepFn_sound hstep)) hbc hcs
                          (idx := idx) hlt (by rw [hidxeq]; exact hap)
            · simp only [Bool.not_eq_true] at hbc
              simp only [hbc, Bool.false_eq_true, reduceIte] at hst
              simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
              obtain ⟨rfl, rfl, rfl⟩ := hst
              have hts : m.threads.setIfInBounds i c'
                  = (m.threads.setIfInBounds i c') ++ ([] : List Config).toArray := by
                simp
              rw [hts]
              exact StepM.thread hsched hti hbl
                (StepE.lift (stepFn_sound hstep)) (by simp [hbc])

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

end GoLean.GoCore.Machine
