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
theorem selectArrivalCases_singleton {s : ExecState} {c : Config}
    {clauses : List (SelectClauseHead × Stmt)} {vs : List GoValue}
    {env : LocalEnv} {k : Cont} :
    selectArrivalCases s #[c] 0 clauses vs env k = .ok .cellPath := by
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
  unfold selectArrivalCases
  cases hsc : selectClauseChans clauses vs with
  | none => rfl
  | some sides =>
      dsimp only
      simp only [hsw, Bool.not_false, reduceIte]
      rfl

@[inherit_doc chanArrivalPlan_singleton]
theorem arrivalCases_singleton {s : ExecState} {c c' : Config} :
    arrivalCases s #[c] 0 c' = .ok .cellPath := by
  unfold arrivalCases
  split
  · rw [show chanArrivalPlan s #[c] 0 _ _ _ _ = .ok none
      from chanArrivalPlan_singleton]
    rfl
  · exact selectArrivalCases_singleton
  · rfl

@[inherit_doc chanArrivalPlan_singleton]
theorem arrivalPlan_singleton {s : ExecState} {c c' : Config} {ch : Choices} :
    arrivalPlan s #[c] 0 c' ch = .ok (none, ch, []) := by
  unfold arrivalPlan
  rw [show arrivalCases s #[c] 0 c' = .ok .cellPath from arrivalCases_singleton]
  rfl

/-- Wrapper computations of `arrivalPlan` from a pure analysis (the
proofs' bridge between `arrivalCases` — the relation's carrier — and
the consuming wrapper the executable calls). -/
theorem arrivalPlan_of_cellPath {s : ExecState} {threads : Array Config}
    {i : Nat} {c : Config} {ch : Choices}
    (h : arrivalCases s threads i c = .ok .cellPath) :
    arrivalPlan s threads i c ch = .ok (none, ch, []) := by
  unfold arrivalPlan
  rw [h]
  rfl

@[inherit_doc arrivalPlan_of_cellPath]
theorem arrivalPlan_of_single {s : ExecState} {threads : Array Config}
    {i : Nat} {c bc : Config} {cs : List (Nat × PairTarget)} {ch : Choices}
    (h : arrivalCases s threads i c = .ok (.single bc cs)) :
    arrivalPlan s threads i c ch = .ok (some (.pair bc cs), ch, []) := by
  unfold arrivalPlan
  rw [h]
  rfl

@[inherit_doc arrivalPlan_of_cellPath]
theorem arrivalPlan_of_error {s : ExecState} {threads : Array Config}
    {i : Nat} {c : Config} {e : Stop} {ch : Choices}
    (h : arrivalCases s threads i c = .error e) :
    arrivalPlan s threads i c ch = .error e := by
  unfold arrivalPlan
  rw [h]
  rfl

@[inherit_doc arrivalPlan_of_cellPath]
theorem arrivalPlan_of_multi {s : ExecState} {threads : Array Config}
    {i : Nat} {c : Config} {os : List ArrivalOutcome} {sel : Nat}
    {ch ch₁ : Choices}
    (h : arrivalCases s threads i c = .ok (.multi os))
    (hcons : Choices.consume ch os.length = (sel, ch₁)) :
    arrivalPlan s threads i c ch
      = (match os[sel]? with
        | some o => .ok (some o, ch₁, [⟨.l2Arrival, os.length, sel⟩])
        | none => .error (.internal "select L2 ready pick out of range")) := by
  unfold arrivalPlan
  rw [h]
  show (do
    let (idx, ch', ps) := Choices.consumeAtE .l2Arrival os.length ch
    match os[idx]? with
    | some o => pure ((some o : Option ArrivalOutcome), ch', ps)
    | none => throw (.internal "select L2 ready pick out of range")
    : Except Stop (Option ArrivalOutcome × Choices × List PickRecord)) = _
  rw [Choices.consumeAtE_pop rfl, hcons]
  dsimp only
  cases os[sel]? <;> rfl

/-- An `opDoneInner` extraction pins the marker's shape (the
`spawnPlan` extraction mold). -/
theorem opDoneInner_shape {c inner : Config}
    (h : opDoneInner c = some inner) : ∃ sc, c = .opDone sc inner := by
  match c, h with
  | .opDone sc i', h =>
      simp only [opDoneInner, Option.some.injEq] at h
      exact ⟨sc, by rw [h]⟩

/-- The completion marker STRIPS sequentially too (stage C, B1 —
`stepFn`'s `.opDone` arm; the old `.spawned` marker failed closed
here, which is what made the strip pool-only pre-widening). -/
theorem opDoneInner_stepFn_strip {c inner : Config} {σ : ExecState}
    {ch : Choices} (h : opDoneInner c = some inner) :
    stepFn σ c ch = .ok (inner, σ, ch) := by
  obtain ⟨sc, rfl⟩ := opDoneInner_shape h
  rfl

/-- The sequential relation's marker rule, inverted: the strip is the
ONLY step from a marker. -/
theorem step_opDone_inv {sc : ChoiceSite} {c c' : Config}
    {σ σ' : ExecState} (h : Step (.opDone sc c) σ c' σ') :
    c' = c ∧ σ' = σ := by
  cases h
  exact ⟨rfl, rfl⟩

/-- The clamped boundary site never pops at bound 1 — for ARBITRARY
configurations (the clamp in `Config.boundarySite` is what makes this
unconditional; the sequential-conservation lemmas quantify over any
config). -/
theorem Config.boundarySite_consumeAtOne (c : Config) :
    (Config.boundarySite c).policy.consumeAtOne = false := by
  unfold Config.boundarySite
  split <;> rfl

/-- A postOp boundary site is exactly a postOp-tagged marker. -/
theorem Config.boundarySite_postOp_shape {c : Config}
    (h : Config.boundarySite c = .postOp) :
    ∃ inner, c = .opDone .postOp inner := by
  unfold Config.boundarySite at h
  split at h
  · rename_i inner; exact ⟨inner, rfl⟩
  all_goals cases h

/-- A backEdge boundary site's configuration is RUNNABLE (stage D: the
loop re-entry shapes are neither done nor blocked — what puts the
current goroutine at slot 0 of its own menu). -/
theorem Config.boundarySite_backEdge_runnable {s : ExecState} {c : Config}
    (h : Config.boundarySite c = .backEdge) :
    threadRunnable s c = true := by
  unfold Config.boundarySite at h
  -- Order matters: `cases h` on the MATCHING arms' `refl` proof
  -- succeeds vacuously and leaves the goal, so the computation goes
  -- first.
  split at h <;>
    first
    | (simp [threadRunnable, threadDone, isBlockedConfig]; done)
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
theorem stepFn_selectApply_inv {σ : ExecState} {v : GoValue}
    {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt}
    {done : List GoValue} {env : LocalEnv} {k' : Cont}
    {ch : Choices} {c' : Config} {σ' : ExecState} {ch' : Choices}
    (h : stepFn σ (.retV v (.selectOpsK clauses default? done [] env k')) ch
      = .ok (c', σ', ch')) :
    (∃ cl?, applySelect σ clauses default? ((v :: done).reverse) env k' ch
        = .ok (c', σ', ch', cl?))
      ∨ (∃ msg, applySelect σ clauses default? ((v :: done).reverse) env k' ch
          = .error (.panic msg)
          ∧ c' = .panicking [panicEntry msg] k'
          ∧ σ' = σ ∧ ch' = ch) := by
  unfold stepFn at h
  dsimp only at h
  cases happ : applySelect σ clauses default? ((v :: done).reverse) env k' ch with
  | ok r =>
      obtain ⟨c₂, s₂, ch₂, cl₂⟩ := r
      rw [happ] at h
      simp only [toResult_ok, Bind.bind, Except.bind, pure_eq_ok, deliverS_ok,
        Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .inl ⟨cl₂, rfl⟩
  | error e =>
      rw [happ] at h
      cases_stop e <;>
        simp only [toResult_panic, toResult_refusal, toResult_fatal, toResult_deadlock,
          toResult_raceDetected, toResult_fuelOut, Bind.bind, Except.bind, pure_eq_ok,
          deliverS_panic, List.nil_append, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
      case panic msg =>
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .inr ⟨msg, rfl, rfl, rfl, rfl⟩

/-- The one-thread `stepThread` is `stepFn`, results re-wrapped with a
step event attached (the arrival plan is a pure no-op with no other
goroutines — `arrivalPlan_singleton`; the completion marker's pool
strip matches `stepFn`'s own `.opDone` arm exactly — stage C's
both-drivers strip; the select interception path lands on `stepFn`'s
own result — one consuming definition, `applySelect`, whose commit
identity the sequential arm projects away). -/
theorem stepThread_single {σ : ExecState} {c : Config} {ch : Choices}
    (hbl : isBlockedConfig c = false)
    (hsp : spawnPlan c = none) :
    ∃ ev, stepThread σ #[c] 0 ch
      = (stepFn σ c ch).map (fun r => (#[r.1], r.2.1, r.2.2, ev)) := by
  cases hsc : opDoneInner c with
  | some inner =>
      -- The marker strip: the pool arm and `stepFn`'s arm coincide.
      refine ⟨⟨0, .opDoneStrip, []⟩, ?_⟩
      obtain ⟨sc, rfl⟩ := opDoneInner_shape hsc
      rfl
  | none =>
  unfold stepThread
  have h0 : (#[c] : Array Config)[0]? = some c := rfl
  rw [h0]
  simp only [hbl, Bool.false_eq_true, reduceIte, hsc, hsp]
  rw [show arrivalPlan σ #[c] 0 c ch = .ok (none, ch, [])
    from arrivalPlan_singleton]
  simp only [Bind.bind, Except.bind]
  cases hselp : selectApplyPlan c with
  | none =>
      refine ⟨⟨0, .privateStep, []⟩, ?_⟩
      cases hstep : stepFn σ c ch with
      | error e => rfl
      | ok r =>
          obtain ⟨c', s', ch₁⟩ := r
          simp [Functor.map, Except.map]
  | some p =>
      obtain ⟨v, clauses, default?, done, env, k'⟩ := p
      obtain rfl := selectApplyPlan_shape hselp
      dsimp only
      cases happly : applySelect σ clauses default?
          ((v :: done).reverse) env k' ch with
      | ok r =>
          obtain ⟨c', s', ch₂, cl?⟩ := r
          have hfn : stepFn σ
              (.retV v (.selectOpsK clauses default? done [] env k')) ch
              = .ok (c', s', ch₂) := by
            unfold stepFn
            dsimp only
            rw [happly]
            rfl
          refine ⟨⟨0, match cl? with
            | some cl => .selectCommit cl
            | none => .selectPass, []⟩, ?_⟩
          rw [hfn]
          simp only [Functor.map, Except.map]
          cases cl? <;> rfl
      | error e =>
          have hfn : stepFn σ
              (.retV v (.selectOpsK clauses default? done [] env k')) ch
              = (match e with
                 | .panic msg =>
                     .ok (.panicking [panicEntry msg] k', σ, ch)
                 | e => .error e) := by
            unfold stepFn
            dsimp only
            simp only [happly]
            cases_stop e <;> rfl
          refine ⟨⟨0, .selectPass, []⟩, ?_⟩
          rw [hfn]
          cases_stop e <;> first | rfl | simp [Functor.map, Except.map]

theorem runnableIdxs_singleton {σ : ExecState} {c : Config}
    (h : threadRunnable σ c = true) :
    runnableIdxs σ #[c] = [0] := by
  simp [runnableIdxs, h]

/-- A singleton pool's slot menu is `[0]` at EVERY site (postOp's
issuer-first reordering is invisible with one goroutine). -/
theorem schedSlots_singleton {σ : ExecState} {c : Config}
    {site : ChoiceSite} (h : threadRunnable σ c = true) :
    schedSlots σ #[c] 0 site = [0] := by
  unfold schedSlots
  cases site <;>
    simp [runnableIdxs_singleton h]

/-- **The one-thread pool step is the sequential step** (the D2a
consumption rule at work: a single runnable goroutine never consumes a
scheduler choice — at the L1 site AND at stage C's postOp site, both
by the declared `consumeAtOne := false` policy via the clamped
`Config.boundarySite` — and with no partner the intercept never
fires). -/
theorem stepMulti_single {σ : ExecState} {c : Config} {ch : Choices}
    (hbl : isBlockedConfig c = false)
    (hsp : spawnPlan c = none)
    (hdone : threadDone c = false) :
    ∃ ev, stepMulti ⟨#[c], σ, 0⟩ ch
      = (stepFn σ c ch).map (fun r => (⟨#[r.1], r.2.1, 0⟩, r.2.2, ev)) := by
  have hrun : threadRunnable σ c = true := by
    simp [threadRunnable, hdone, hbl]
  obtain ⟨ev, hst⟩ := stepThread_single (σ := σ) (ch := ch) hbl hsp
  refine ⟨ev, ?_⟩
  have hinto : stepThreadInto ⟨#[c], σ, 0⟩ 0 ch
      = (stepFn σ c ch).map (fun r => (⟨#[r.1], r.2.1, 0⟩, r.2.2, ev)) := by
    unfold stepThreadInto
    show (stepThread σ #[c] 0 ch).bind _ = _
    rw [hst]
    cases stepFn σ c ch <;>
      simp [Bind.bind, Except.bind, Functor.map, Except.map]
  unfold stepMulti
  have h0 : (#[c] : Array Config)[0]? = some c := rfl
  simp only [h0]
  by_cases hb : Config.atBoundary c = true
  · simp only [hb, reduceIte]
    rw [show schedSlots σ #[c] 0 c.boundarySite = [0]
      from schedSlots_singleton hrun]
    dsimp only
    rw [show Choices.consumeAtE c.boundarySite [0].length ch = (0, ch, [])
      from Choices.consumeAtE_le_one (by simp)
        (Config.boundarySite_consumeAtOne c)]
    simp only [List.getElem?_cons_zero]
    simp only [Bind.bind, Except.bind]
    rw [hinto]
    cases hstep : stepFn σ c ch with
    | error e => simp [Except.map]
    | ok r =>
        obtain ⟨c', s', ch₂⟩ := r
        simp [Except.map]
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
def transferable : Except Stop (ExecOutcome × Choices) → Prop
  | .ok _ => True
  | .error .fuelOut => True
  | .error (.panic _) => True
  | _ => False

/-- The race detector is DEFINITIONALLY inert on one-goroutine pools
(`raceUpdate`'s first branch): a single goroutine cannot race with
itself. The conservation proof's detector hinge — sequential runs
thread the `RaceState` through untouched. -/
theorem raceUpdate_single {σ : ExecState} {ts : Array Config} {c : Config}
    {σ' : ExecState} {i : Nat} {ev : StepEvent} {rs : RaceState} :
    raceUpdate σ ts ev ⟨#[c], σ', i⟩ rs = .ok rs := by
  simp [raceUpdate]

/-- The singleton-pool projections of a mid-run (non-terminal,
non-blocked) configuration. -/
theorem singleton_pool_facts {σ : ExecState} {c : Config}
    (h1 : c ≠ .next .stop) (h2 : c ≠ .returning .stop)
    (h3 : c ≠ .breaking .stop) (h4 : c ≠ .continuing .stop)
    (h5 : ∀ msg, c ≠ .panicked msg)
    (h6 : ∀ a b k, c ≠ .blockedSend a b k)
    (h7 : ∀ a b e env k, c ≠ .blockedRecv a b e env k)
    (h8 : ∀ cl env k, c ≠ .blockedSelect cl env k)
    (h9 : ∀ op loc env k, c ≠ .blockedSync op loc env k) :
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
    · exact (h7 _ _ _ _ _ rfl rfl rfl rfl rfl)
    · exact (h9 _ _ _ _ rfl rfl rfl rfl)

/-- **The conservation transfer, loop level**: every sequential result
in the `transferable` classes is the singleton pool's result verbatim
— same outcome, same final state, same leftover stream, same fuel
accounting. -/
theorem execProgLoop_single :
    ∀ {fuel : Nat} {σ : ExecState} {c : Config} {ch : Choices}
      {rs : RaceState}
      {r : Except Stop (ExecOutcome × Choices)},
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
    · subst hr; simp [transferable, throw, throwThe, MonadExceptOf.throw] at htr
    · rename_i harm1 harm2 harm3 harm4 harm5 harm6 harm7 harm8 harm9
      subst hr
      obtain ⟨hp, hm, hd, hb⟩ := singleton_pool_facts
        (σ := σ) harm1 harm2 harm3 harm4 harm5 harm6 harm7 harm8 harm9
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
    · subst hr; simp [transferable, throw, throwThe, MonadExceptOf.throw] at htr
    · rename_i harm1 harm2 harm3 harm4 harm5 harm6 harm7 harm8 harm9
      obtain ⟨hp, hm, hd, hb⟩ := singleton_pool_facts
        (σ := σ) harm1 harm2 harm3 harm4 harm5 harm6 harm7 harm8 harm9
      have hrun : threadRunnable σ c = true := by
        simp [threadRunnable, hd, hb]
      unfold execProgLoop
      simp only [Bind.bind, Except.bind] at hr
      -- Stage C: the completion marker is NOT a special case any
      -- more — `stepFn` strips it on the sequential driver and
      -- `stepThread`'s marker arm does the identical strip on the
      -- pool, so `stepMulti_single` covers it like any private step.
      cases hsp : spawnPlan c with
      | some p =>
          have hcls := spawnPlan_stepFn_refuses (σ := σ) (ch := ch) hsp
          cases hstep : stepFn σ c ch with
          | ok r₂ => rw [hstep] at hcls; simp at hcls
          | error e =>
              rw [hstep] at hr
              rw [hstep] at hcls
              subst hr
              cases_stop e <;> simp_all [transferable]
      | none =>
          obtain ⟨ev, hmulti⟩ :=
            stepMulti_single (σ := σ) (ch := ch) hb hsp hd
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
    {r : Except Stop (ExecOutcome × Choices)}
    (hr : execStmt fuel env σ ch prog = r) (htr : transferable r) :
    execProg fuel env σ ch prog = r :=
  execProgLoop_single hr htr

/-! ## Correspondence: `stepMulti` instantiates `StepM` -/

/-- A successful spawn's PARENT successor is always the completion
marker `.opDone .l1Sched (.next k)` (BUG-040: the fork's completion is
a registry op; stage C: the `l1Sched` tag preserves the spawn
boundary's shipped default; the marker strips at the next step). -/
theorem spawnStep_shape {s : ExecState} {cv : GoValue} {args : List GoValue}
    {k : Cont} {ch : Choices} {p c : Config} {s' : ExecState} {ch' : Choices}
    (h : spawnStep s cv args k ch = .ok (p, c, s', ch')) :
    p = .opDone .l1Sched (.next k) := by
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

/-- Runnable-list membership from an indexed runnable configuration. -/
theorem mem_runnableIdxs_of {s : ExecState} {ts : Array Config} {j : Nat}
    {c : Config} (hj : ts[j]? = some c) (hr : threadRunnable s c = true) :
    j ∈ runnableIdxs s ts := by
  obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hj
  unfold runnableIdxs
  refine List.mem_filter.mpr ⟨List.mem_range.mpr hlt, ?_⟩
  simp only [hj, hr]

/-- The slot menu's SET is contained in the runnable set — the slot
reordering at postOp adds no member (`schedPick`'s membership
formulation is therefore unchanged by the widening). -/
theorem schedSlots_mem {s : ExecState} {ts : Array Config} {cur i : Nat}
    {c : Config} (hcur : ts[cur]? = some c)
    (hmem : i ∈ schedSlots s ts cur c.boundarySite) :
    i ∈ runnableIdxs s ts := by
  by_cases hpost : c.boundarySite = .postOp
  · rw [hpost] at hmem
    unfold schedSlots at hmem
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · obtain ⟨inner, rfl⟩ := Config.boundarySite_postOp_shape hpost
      exact mem_runnableIdxs_of hcur rfl
    · exact (List.mem_filter.mp hmem').1
  · by_cases hback : c.boundarySite = .backEdge
    · rw [hback] at hmem
      unfold schedSlots at hmem
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact mem_runnableIdxs_of hcur
          (Config.boundarySite_backEdge_runnable hback)
      · exact (List.mem_filter.mp hmem').1
    · have heq : schedSlots s ts cur c.boundarySite = runnableIdxs s ts := by
        unfold schedSlots
        cases hbs : c.boundarySite <;>
          first | (exact absurd hbs hpost) | (exact absurd hbs hback) | rfl
      rw [heq] at hmem
      exact hmem

/-- Every runnable goroutine appears in the slot menu at every site
(completeness direction: the menu never LOSES a member either). -/
theorem mem_schedSlots_of_runnable {s : ExecState} {ts : Array Config}
    {cur i : Nat} {site : ChoiceSite}
    (hmem : i ∈ runnableIdxs s ts) :
    i ∈ schedSlots s ts cur site := by
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
    {m' : MultiConfig} {ev : StepEvent} (hsched : schedPick m i)
    (h : stepThreadInto m i ch = .ok (m', ch', ev)) : StepM m m' := by
  unfold stepThreadInto at h
  simp only [Bind.bind, Except.bind] at h
  cases hst : stepThread m.shared m.threads i ch with
  | error e => rw [hst] at h; cases h
  | ok r =>
    obtain ⟨ts, s', chX, evX⟩ := r
    rw [hst] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
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
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
          exact StepM.wake hsched hti hbl hres
      · simp only [Bool.not_eq_true] at hbl
        simp only [hbl, Bool.false_eq_true, reduceIte] at hst
        cases hsc : opDoneInner c with
        | some inner =>
          -- The completion-marker STRIP (stage C): an ordinary
          -- `.thread` step now — `Step.opDoneStrip` lifted.
          rw [hsc] at hst
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
          obtain ⟨sc, hcfg⟩ := opDoneInner_shape hsc
          subst hcfg
          have hts : m.threads.setIfInBounds i inner
              = (m.threads.setIfInBounds i inner) ++ ([] : List Config).toArray := by
            simp
          rw [hts]
          exact StepM.thread hsched hti hbl rfl (StepE.lift Step.opDoneStrip)
        | none =>
        rw [hsc] at hst
        cases hsp : spawnPlan c with
        | some p =>
          obtain ⟨cv, args, k⟩ := p
          rw [hsp] at hst
          simp only [Bind.bind, Except.bind] at hst
          cases hspawn : spawnStep m.shared cv args k ch with
          | error e => rw [hspawn] at hst; cases hst
          | ok r₂ =>
            obtain ⟨parent', child, s₂, ch₂⟩ := r₂
            rw [hspawn] at hst
            simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
            have hplanNone : arrivalCases m.shared m.threads i c
                = .ok .cellPath := by
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
          -- Dispatch on the PURE analysis; each analysis value fixes the
          -- wrapper's result (`arrivalPlan_of_*`), which rewrites `hst`.
          cases hac : arrivalCases m.shared m.threads i c with
          | error e => rw [arrivalPlan_of_error hac] at hst; cases hst
          | ok analysis =>
            cases analysis with
            | cellPath =>
              rw [arrivalPlan_of_cellPath hac] at hst
              simp only [Bind.bind, Except.bind] at hst
              cases hselp : selectApplyPlan c with
              | none =>
                rw [hselp] at hst
                dsimp only at hst
                cases hstep : stepFn m.shared c ch with
                | error e => rw [hstep] at hst; cases hst
                | ok r₂ =>
                  obtain ⟨c', s₂, ch₂⟩ := r₂
                  rw [hstep] at hst
                  dsimp only at hst
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
                  have hts : m.threads.setIfInBounds i c'
                      = (m.threads.setIfInBounds i c') ++ ([] : List Config).toArray := by
                    simp
                  rw [hts]
                  exact StepM.thread hsched hti hbl hac (StepE.lift (stepFn_sound hstep))
              | some p =>
                -- THE SELECT INTERCEPTION (Q2): the pool ran
                -- `applySelect` itself; the relation's own select rules
                -- absorb both outcomes.
                obtain ⟨v, clauses, default?, done, env, k'⟩ := p
                obtain rfl := selectApplyPlan_shape hselp
                rw [hselp] at hst
                dsimp only at hst
                cases happly : applySelect m.shared clauses default?
                    ((v :: done).reverse) env k' ch with
                | ok r₂ =>
                  obtain ⟨c', s₂, ch₂, cl?⟩ := r₂
                  rw [happly] at hst
                  simp only [toResult_ok, Bind.bind, Except.bind, pure_eq_ok,
                    Except.ok.injEq, Prod.mk.injEq] at hst
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
                  have hts : m.threads.setIfInBounds i c'
                      = (m.threads.setIfInBounds i c') ++ ([] : List Config).toArray := by
                    simp
                  rw [hts]
                  exact StepM.thread hsched hti hbl hac
                    (StepE.lift (Step.selectApply (toResult_eq_ok_ok.mpr happly) rfl))
                | error e =>
                  rw [happly] at hst
                  cases_stop e <;>
                    simp only [toResult_panic, toResult_refusal, toResult_fatal, toResult_deadlock,
                      toResult_raceDetected, toResult_fuelOut, Bind.bind, Except.bind, pure_eq_ok,
                      deliver_panic, List.nil_append, Except.ok.injEq, Prod.mk.injEq,
                      reduceCtorEq] at hst
                  case panic msg =>
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
                  have hts : m.threads.setIfInBounds i (.panicking [panicEntry msg] k')
                      = (m.threads.setIfInBounds i (.panicking [panicEntry msg] k'))
                        ++ ([] : List Config).toArray := by
                    simp
                  rw [hts]
                  exact StepM.thread hsched hti hbl hac
                    (StepE.lift (Step.selectApply (toResult_eq_ok_panic.mpr happly) rfl))
            | single bc cs =>
              rw [arrivalPlan_of_single hac] at hst
              simp only [Bind.bind, Except.bind] at hst
              cases cs with
              | nil => cases hst
              | cons cand rest =>
                  -- The L4 site (`consumeAtE .l4Waiter`): one arm covers
                  -- singleton and multi-candidate plans — the singleton
                  -- non-consumption is the site's policy now.
                  simp only [Bind.bind, Except.bind] at hst
                  rcases hcons : Choices.consumeAtE .l4Waiter
                      (cand :: rest).length ch with ⟨idx, ch₃, ps₃⟩
                  rw [hcons] at hst
                  cases hget : (cand :: rest)[idx]? with
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
                      obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
                      obtain ⟨hlt, hidxeq⟩ := List.getElem?_eq_some_iff.mp hget
                      exact StepM.pair hsched hti hbl hsp hac
                        (idx := idx) hlt (by rw [hidxeq]; exact hap)
            | multi os =>
              rcases hcons : ch.consume os.length with ⟨sel, chL⟩
              rw [arrivalPlan_of_multi hac hcons] at hst
              cases hget : os[sel]? with
              | none => rw [hget] at hst; cases hst
              | some o =>
                rw [hget] at hst
                cases o with
                | pair bc cs =>
                  simp only [Bind.bind, Except.bind] at hst
                  cases cs with
                  | nil => cases hst
                  | cons cand rest =>
                      simp only [Bind.bind, Except.bind] at hst
                      rcases hconsL : Choices.consumeAtE .l4Waiter
                          (cand :: rest).length chL with ⟨idx, ch₃, ps₃⟩
                      rw [hconsL] at hst
                      cases hgetL : (cand :: rest)[idx]? with
                      | none => rw [hgetL] at hst; cases hst
                      | some cand' =>
                        rw [hgetL] at hst
                        simp only [Bind.bind, Except.bind] at hst
                        cases hap : applyPairing m.shared m.threads i bc cand' with
                        | error e => rw [hap] at hst; cases hst
                        | ok r₃ =>
                          obtain ⟨ts', s₃⟩ := r₃
                          rw [hap] at hst
                          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
                          obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
                          obtain ⟨hlt, hidxeq⟩ := List.getElem?_eq_some_iff.mp hgetL
                          exact StepM.pickPair hsched hti hbl hsp hac hget
                            (idx := idx) hlt (by rw [hidxeq]; exact hap)
                | commit cl envc kc =>
                  simp only [Bind.bind, Except.bind] at hst
                  cases hcom : commitClause m.shared envc kc cl with
                  | error e => rw [hcom] at hst; cases hst
                  | ok r₃ =>
                    obtain ⟨c₃, s₃⟩ := r₃
                    rw [hcom] at hst
                    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
                    obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
                    exact StepM.pickCommit hsched hti hbl hsp hac hget hcom

/-- **Soundness of the pool step**: every `.ok` step of `stepMulti` is a
step of the pool relation `StepM`. -/
theorem stepMulti_sound {m : MultiConfig} {ch ch' : Choices}
    {m' : MultiConfig} {ev : StepEvent}
    (h : stepMulti m ch = .ok (m', ch', ev)) : StepM m m' := by
  unfold stepMulti at h
  cases hcur : m.threads[m.cur]? with
  | none => rw [hcur] at h; cases h
  | some c =>
    rw [hcur] at h
    by_cases hb : c.atBoundary = true
    · simp only [hb, reduceIte] at h
      cases hrs : schedSlots m.shared m.threads m.cur c.boundarySite with
      | nil => rw [hrs] at h; cases h
      | cons r0 rest =>
        rw [hrs] at h
        -- The boundary site (`consumeAtE c.boundarySite` — l1Sched or
        -- stage C's postOp): one arm covers the sole slot (policy: no
        -- pop at bound 1, `boundarySite_consumeAtOne`) and the
        -- consuming pick.
        dsimp only at h
        rcases hcons : Choices.consumeAtE c.boundarySite
            (r0 :: rest).length ch
          with ⟨pick, ch₁, ps⟩
        rw [hcons] at h
        cases hget : (r0 :: rest)[pick]? with
        | none => rw [hget] at h; cases h
        | some i =>
          rw [hget] at h
          simp only [Bind.bind, Except.bind] at h
          cases hinto : stepThreadInto m i ch₁ with
          | error e => rw [hinto] at h; cases h
          | ok r =>
            obtain ⟨m₂, ch₂, evI⟩ := r
            rw [hinto] at h
            simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            have hmem : i ∈ runnableIdxs m.shared m.threads := by
              refine schedSlots_mem hcur ?_
              rw [hrs]
              exact List.mem_of_getElem? hget
            exact stepThreadInto_sound (schedPick_of_boundary hcur hb hmem) hinto
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

-- `step_spawnedMarker_elim` DELETED (stage C): the marker now HAS a
-- sequential rule (`Step.opDoneStrip`) — the strip is an ordinary
-- lifted step, no longer relation-silent.

/-- A completed spawn position is not the marker (plan disjointness for
the `stepThread` dispatch proofs). -/
theorem opDoneInner_of_spawnPlan {c : Config}
    {p : GoValue × List GoValue × Cont}
    (h : spawnPlan c = some p) : opDoneInner c = none := by
  match c, h with
  | .retV cv (.goCalleeK [] env k), _ => rfl
  | .retV v (.goArgsK cv vals [] env k), _ => rfl

/-- A blocked configuration is not the marker. -/
theorem opDoneInner_of_blocked {c : Config}
    (h : isBlockedConfig c = true) : opDoneInner c = none := by
  match c, h with
  | .blockedSend _ _ _, _ => rfl
  | .blockedRecv _ _ _ _ _, _ => rfl
  | .blockedSelect _ _ _, _ => rfl
  | .blockedSync _ _ _ _, _ => rfl

/-- Compose a scheduling prefix in front of an inner `stepThread`
realization: a legal pick is realized by the scheduler site (consumed
only at `|runnable| > 1`, the pick index prepended to the stream). -/
theorem stepMulti_of_inner {m : MultiConfig} {i : Nat} {chI chI' : Choices}
    {ts : Array Config} {s' : ExecState} {evI : StepEvent}
    (hsched : schedPick m i)
    (hinner : stepThread m.shared m.threads i chI = .ok (ts, s', chI', evI)) :
    ∃ ch ch' ev, stepMulti m ch = .ok (⟨ts, s', i⟩, ch', ev) := by
  unfold schedPick at hsched
  cases hcur : m.threads[m.cur]? with
  | none => rw [hcur] at hsched; exact absurd hsched (by simp)
  | some c₀ =>
    rw [hcur] at hsched
    dsimp only at hsched
    by_cases hbnd : c₀.atBoundary = true
    · rw [if_pos hbnd] at hsched
      -- Realize the pick through the boundary's own slot menu
      -- (`schedSlots`/`boundarySite` — stage C): every runnable
      -- goroutine is IN the menu (`mem_schedSlots_of_runnable`), and
      -- the site never pops at a singleton menu
      -- (`boundarySite_consumeAtOne`).
      have hmenu : i ∈ schedSlots m.shared m.threads m.cur c₀.boundarySite :=
        mem_schedSlots_of_runnable hsched
      cases hrs : schedSlots m.shared m.threads m.cur c₀.boundarySite with
      | nil =>
        rw [hrs] at hmenu
        exact absurd hmenu (by simp)
      | cons r0 rest =>
        rw [hrs] at hmenu
        cases rest with
        | nil =>
          have hi : i = r0 := by
            simpa using hmenu
          subst hi
          exact ⟨chI, chI', _, by
            unfold stepMulti
            rw [hcur]
            simp only [hbnd, reduceIte]
            rw [hrs]
            dsimp only
            -- sole slot: the site's policy consumes nothing
            rw [show Choices.consumeAtE c₀.boundarySite [i].length chI
                = (0, chI, [])
              from Choices.consumeAtE_le_one (by simp)
                (Config.boundarySite_consumeAtOne c₀)]
            simp only [List.getElem?_cons_zero]
            simp only [Bind.bind, Except.bind]
            unfold stepThreadInto
            rw [hinner]
            rfl⟩
        | cons r1 rest' =>
          obtain ⟨p, hp⟩ := List.getElem?_of_mem hmenu
          have hplen : p < (r0 :: r1 :: rest').length :=
            (List.getElem?_eq_some_iff.mp hp).1
          have hcons : Choices.consumeAtE c₀.boundarySite
              (r0 :: r1 :: rest').length (p :: chI)
              = (p, chI, [⟨c₀.boundarySite, (r0 :: r1 :: rest').length, p⟩]) := by
            rw [Choices.consumeAtE_of_lt (by simp only [List.length_cons]; omega)]
            have hcc : Choices.consume (p :: chI) (r0 :: r1 :: rest').length
                = (p, chI) := by
              simp only [Choices.consume]
              congr 1
              have : max 1 (r0 :: r1 :: rest').length
                  = (r0 :: r1 :: rest').length := by
                simp only [List.length_cons]
                omega
              rw [this]
              exact Nat.mod_eq_of_lt hplen
            rw [hcc]
          exact ⟨p :: chI, chI', _, by
            unfold stepMulti
            rw [hcur]
            simp only [hbnd, reduceIte]
            rw [hrs]
            dsimp only
            rw [hcons, hp]
            dsimp only
            simp only [Bind.bind, Except.bind]
            unfold stepThreadInto
            rw [hinner]
            rfl⟩
    · simp only [Bool.not_eq_true] at hbnd
      rw [if_neg (by simp [hbnd])] at hsched
      subst hsched
      refine ⟨chI, chI', evI, ?_⟩
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
    ∃ ch ch' ev, stepMulti m ch = .ok (m', ch', ev) := by
  cases h with
  | thread hsched hti hblc hplan hstepE =>
    rename_i i c c' σ' efs
    cases hstepE with
    | lift hstep =>
      have hsp : spawnPlan c = none := by
        cases hspq : spawnPlan c with
        | none => rfl
        | some p => exact absurd hstep (step_spawnPos_elim hspq)
      have heq : (m.threads.setIfInBounds i c') ++ ([] : List Config).toArray
          = m.threads.setIfInBounds i c' := by
        rw [show (([] : List Config)).toArray = #[] from rfl, Array.append_empty]
      rw [heq]
      cases hsc : opDoneInner c with
      | some inner =>
          -- The marker strip (stage C): `Step.opDoneStrip` is the only
          -- rule from a marker; the pool's marker arm realizes it on
          -- the empty stream.
          obtain ⟨sc, hcfg⟩ := opDoneInner_shape hsc
          subst hcfg
          obtain ⟨hc', rfl⟩ := step_opDone_inv hstep
          rw [hc']
          have hinner : ∃ evI, stepThread m.shared m.threads i []
              = .ok (m.threads.setIfInBounds i inner, m.shared, [], evI) :=
            ⟨_, by
              unfold stepThread
              rw [hti]
              rfl⟩
          obtain ⟨evI, hinner⟩ := hinner
          exact stepMulti_of_inner hsched hinner
      | none =>
      obtain ⟨ch₀, ch₀', hfn⟩ := step_complete hstep
      cases hselp : selectApplyPlan c with
      | none =>
        have hinner : ∃ evI, stepThread m.shared m.threads i ch₀
            = .ok (m.threads.setIfInBounds i c', σ', ch₀', evI) :=
          ⟨_, by
            unfold stepThread
            rw [hti]
            simp only [hblc, Bool.false_eq_true, reduceIte, hsc, hsp]
            rw [show arrivalPlan m.shared m.threads i c ch₀ = .ok (none, ch₀, [])
              from arrivalPlan_of_cellPath hplan]
            simp only [Bind.bind, Except.bind]
            rw [hselp]
            dsimp only
            rw [hfn]
            rfl⟩
        obtain ⟨evI, hinner⟩ := hinner
        exact stepMulti_of_inner hsched hinner
      | some p =>
        -- THE SELECT INTERCEPTION (Q2): realize through the pool's own
        -- `applySelect` path, inverting `stepFn`'s arm.
        obtain ⟨v, clauses, default?, done, env, k'⟩ := p
        have hshape := selectApplyPlan_shape hselp
        subst hshape
        rcases stepFn_selectApply_inv hfn with ⟨cl?, happly⟩
          | ⟨msg, happly, rfl, rfl, -⟩
        · have hinner : ∃ evI, stepThread m.shared m.threads i ch₀
              = .ok (m.threads.setIfInBounds i c', σ', ch₀', evI) :=
            ⟨_, by
              unfold stepThread
              rw [hti]
              simp only [hblc, Bool.false_eq_true, reduceIte, hsc, hsp]
              rw [show arrivalPlan m.shared m.threads i
                    (.retV v (.selectOpsK clauses default? done [] env k')) ch₀
                  = .ok (none, ch₀, []) from arrivalPlan_of_cellPath hplan]
              simp only [Bind.bind, Except.bind]
              rw [hselp]
              dsimp only
              rw [happly]
              rfl⟩
          obtain ⟨evI, hinner⟩ := hinner
          exact stepMulti_of_inner hsched hinner
        · have hinner : ∃ evI, stepThread m.shared m.threads i ch₀
              = .ok (m.threads.setIfInBounds i
                    (.panicking [panicEntry msg] k'),
                  m.shared, ch₀, evI) :=
            ⟨_, by
              unfold stepThread
              rw [hti]
              simp only [hblc, Bool.false_eq_true, reduceIte, hsc, hsp]
              rw [show arrivalPlan m.shared m.threads i
                    (.retV v (.selectOpsK clauses default? done [] env k')) ch₀
                  = .ok (none, ch₀, []) from arrivalPlan_of_cellPath hplan]
              simp only [Bind.bind, Except.bind]
              rw [hselp]
              dsimp only
              rw [happly]
              rfl⟩
          obtain ⟨evI, hinner⟩ := hinner
          exact stepMulti_of_inner hsched hinner
    | spawn hplan' hspawn =>
      -- The relation's own stream is the witness (BUG-087 audit fix F1:
      -- the spawn's entry panic draws the nilValueMethodText pick).
      rename_i cv args k child chs chs'
      have hinner : ∃ evI, stepThread m.shared m.threads i chs
          = .ok ((m.threads.setIfInBounds i c').push child, σ', chs', evI) :=
        ⟨_, by
          unfold stepThread
          rw [hti]
          simp only [hblc, Bool.false_eq_true, reduceIte,
            opDoneInner_of_spawnPlan hplan', hplan', Bind.bind,
            Except.bind]
          rw [hspawn]
          rfl⟩
      obtain ⟨evI, hinner⟩ := hinner
      have heq : (m.threads.setIfInBounds i c') ++ ([child] : List Config).toArray
          = (m.threads.setIfInBounds i c').push child := by
        rw [Array.push_eq_append]
      rw [heq]
      exact stepMulti_of_inner hsched hinner
  | pair hsched hti hblc hsp hplan hidx hap =>
    rename_i i c bc σ'' cs idx ts'
    have hsc : opDoneInner c = none := by
      cases hscq : opDoneInner c with
      | none => rfl
      | some kk =>
          obtain ⟨sc, hcfg⟩ := opDoneInner_shape hscq
          subst hcfg
          rw [show arrivalCases m.shared m.threads i (.opDone sc kk)
            = .ok .cellPath from rfl] at hplan
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
        have hinner : ∃ evI, stepThread m.shared m.threads i []
            = .ok (ts', σ'', [], evI) :=
          ⟨_, by
            unfold stepThread
            rw [hti]
            simp only [hblc, Bool.false_eq_true, reduceIte, hsc, hsp, Bind.bind,
              Except.bind]
            rw [arrivalPlan_of_single hplan]
            dsimp only
            -- singleton candidate: the L4 site's policy consumes nothing
            rw [show Choices.consumeAtE .l4Waiter [cand].length ([] : Choices)
              = (0, [], []) from Choices.consumeAtE_le_one (by simp) rfl]
            simp only [List.getElem?_cons_zero]
            rw [hap']
            rfl⟩
        obtain ⟨evI, hinner⟩ := hinner
        exact stepMulti_of_inner hsched hinner
      | cons b rest' =>
        have hconsL : Choices.consumeAtE .l4Waiter (cand :: b :: rest').length
            [idx] = (idx, [],
              [⟨.l4Waiter, (cand :: b :: rest').length, idx⟩]) := by
          rw [Choices.consumeAtE_of_lt (by simp only [List.length_cons]; omega)]
          have hcc : Choices.consume [idx] (cand :: b :: rest').length
              = (idx, []) := by
            simp only [Choices.consume]
            congr 1
            have hmax : max 1 (cand :: b :: rest').length
                = (cand :: b :: rest').length := by
              simp only [List.length_cons]
              omega
            rw [hmax]
            exact Nat.mod_eq_of_lt hidx
          rw [hcc]
        have hinner : ∃ evI, stepThread m.shared m.threads i [idx]
            = .ok (ts', σ'', [], evI) :=
          ⟨_, by
            unfold stepThread
            rw [hti]
            simp only [hblc, Bool.false_eq_true, reduceIte, hsc, hsp, Bind.bind,
              Except.bind]
            rw [arrivalPlan_of_single hplan]
            dsimp only
            rw [hconsL]
            dsimp only
            rw [List.getElem?_eq_getElem hidx]
            dsimp only
            rw [hap]
            rfl⟩
        obtain ⟨evI, hinner⟩ := hinner
        exact stepMulti_of_inner hsched hinner
  | pickPair hsched hti hblc hsp hplan hget hidx hap =>
    rename_i i c bc σ'' os sel cs idx ts'
    have hsc : opDoneInner c = none := by
      cases hscq : opDoneInner c with
      | none => rfl
      | some kk =>
          obtain ⟨sc, hcfg⟩ := opDoneInner_shape hscq
          subst hcfg
          rw [show arrivalCases m.shared m.threads i (.opDone sc kk)
            = .ok .cellPath from rfl] at hplan
          cases hplan
    have hsel : sel < os.length := (List.getElem?_eq_some_iff.mp hget).1
    have hconsS : Choices.consume [sel] os.length = (sel, []) := by
      simp only [Choices.consume]
      congr 1
      have hmax : max 1 os.length = os.length := by omega
      rw [hmax]
      exact Nat.mod_eq_of_lt hsel
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
        have hinner : ∃ evI, stepThread m.shared m.threads i [sel]
            = .ok (ts', σ'', [], evI) :=
          ⟨_, by
            unfold stepThread
            rw [hti]
            simp only [hblc, Bool.false_eq_true, reduceIte, hsc, hsp, Bind.bind,
              Except.bind]
            rw [arrivalPlan_of_multi hplan hconsS, hget]
            dsimp only
            rw [show Choices.consumeAtE .l4Waiter [cand].length ([] : Choices)
              = (0, [], []) from Choices.consumeAtE_le_one (by simp) rfl]
            simp only [List.getElem?_cons_zero]
            rw [hap']
            rfl⟩
        obtain ⟨evI, hinner⟩ := hinner
        exact stepMulti_of_inner hsched hinner
      | cons b rest' =>
        have hconsS2 : Choices.consume (sel :: [idx]) os.length = (sel, [idx]) := by
          simp only [Choices.consume]
          congr 1
          have hmax : max 1 os.length = os.length := by omega
          rw [hmax]
          exact Nat.mod_eq_of_lt hsel
        have hconsL : Choices.consumeAtE .l4Waiter (cand :: b :: rest').length
            [idx] = (idx, [],
              [⟨.l4Waiter, (cand :: b :: rest').length, idx⟩]) := by
          rw [Choices.consumeAtE_of_lt (by simp only [List.length_cons]; omega)]
          have hcc : Choices.consume [idx] (cand :: b :: rest').length
              = (idx, []) := by
            simp only [Choices.consume]
            congr 1
            have hmax : max 1 (cand :: b :: rest').length
                = (cand :: b :: rest').length := by
              simp only [List.length_cons]
              omega
            rw [hmax]
            exact Nat.mod_eq_of_lt hidx
          rw [hcc]
        have hinner : ∃ evI, stepThread m.shared m.threads i (sel :: [idx])
            = .ok (ts', σ'', [], evI) :=
          ⟨_, by
            unfold stepThread
            rw [hti]
            simp only [hblc, Bool.false_eq_true, reduceIte, hsc, hsp, Bind.bind,
              Except.bind]
            rw [arrivalPlan_of_multi hplan hconsS2, hget]
            dsimp only
            rw [hconsL]
            dsimp only
            rw [List.getElem?_eq_getElem hidx]
            dsimp only
            rw [hap]
            rfl⟩
        obtain ⟨evI, hinner⟩ := hinner
        exact stepMulti_of_inner hsched hinner
  | pickCommit hsched hti hblc hsp hplan hget hcom =>
    rename_i i c cl envc kc os sel c' σ'
    have hsc : opDoneInner c = none := by
      cases hscq : opDoneInner c with
      | none => rfl
      | some kk =>
          obtain ⟨sc, hcfg⟩ := opDoneInner_shape hscq
          subst hcfg
          rw [show arrivalCases m.shared m.threads i (.opDone sc kk)
            = .ok .cellPath from rfl] at hplan
          cases hplan
    have hsel : sel < os.length := (List.getElem?_eq_some_iff.mp hget).1
    have hconsS : Choices.consume [sel] os.length = (sel, []) := by
      simp only [Choices.consume]
      congr 1
      have hmax : max 1 os.length = os.length := by omega
      rw [hmax]
      exact Nat.mod_eq_of_lt hsel
    have hinner : ∃ evI, stepThread m.shared m.threads i [sel]
        = .ok (m.threads.setIfInBounds i c', σ', [], evI) :=
      ⟨_, by
        unfold stepThread
        rw [hti]
        simp only [hblc, Bool.false_eq_true, reduceIte, hsc, hsp, Bind.bind,
          Except.bind]
        rw [arrivalPlan_of_multi hplan hconsS, hget]
        dsimp only
        rw [hcom]
        rfl⟩
    obtain ⟨evI, hinner⟩ := hinner
    exact stepMulti_of_inner hsched hinner
  | wake hsched hti hblc hres =>
    rename_i i c c' σ'
    have hinner : ∃ evI, stepThread m.shared m.threads i []
        = .ok (m.threads.setIfInBounds i c', σ', [], evI) :=
      ⟨_, by
        unfold stepThread
        rw [hti]
        simp only [hblc, reduceIte, Bind.bind, Except.bind]
        rw [hres]
        rfl⟩
    obtain ⟨evI, hinner⟩ := hinner
    exact stepMulti_of_inner hsched hinner

end GoLean.GoCore.Machine
