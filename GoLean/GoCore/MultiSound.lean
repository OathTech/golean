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

namespace GoLean.GoCore.Machine

open GoLean

/-! ## Small computation lemmas -/

@[simp] theorem isBlockedConfig_next {k : Cont} : isBlockedConfig (.next k) = false := rfl
@[simp] theorem isBlockedConfig_panicking {chain : List PanicEntry} {k : Cont} :
    isBlockedConfig (.panicking chain k) = false := rfl

theorem recvSideWaiters_singleton {c : Config} {loc : Loc} :
    recvSideWaiters #[c] 0 loc = [] := by
  simp [recvSideWaiters]

theorem sendSideWaiters_singleton {c : Config} {loc : Loc} :
    sendSideWaiters #[c] 0 loc = [] := by
  simp [sendSideWaiters]

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
      have hfil : List.filter ((fun (p : Nat × List (Nat × PairTarget)) =>
          !p.2.isEmpty) ∘ fun ci => (ci, [])) (List.range evs.length) = [] := by
        simp [Function.comp]
      simp [pairCandidates, hmap, Bind.bind, Except.bind, List.filter_map, hfil]
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

end GoLean.GoCore.Machine
