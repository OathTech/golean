import GoLean.GoCore.PoolFacts
import GoLean.GoCore.Consumes

/-! Stream facts supporting dedup certificate coverage, restored from the executable
parts of MachineSound and MultiStreams at relational/last-main-2026-10-20. -/

namespace GoLean.GoCore.Machine

variable {ctx : ProgramCtx}

/-- A `consumesUnseqNext` configuration IS a sweep frame at its pick position. -/
theorem consumesUnseqNext_shape {c : Config} (h : consumesUnseqNext c = true) :
    ∃ g thenB st tg env k, c = .next (.unseqK g thenB st tg env .pick k) := by
  unfold consumesUnseqNext at h
  split at h
  · exact ⟨_, _, _, _, _, _, rfl⟩
  · cases h

/-- A `consumesUnseqPanic` configuration IS a panic that reached a probe frame. -/
theorem consumesUnseqPanic_shape {c : Config} (h : consumesUnseqPanic c = true) :
    ∃ chain k, c = .panicking chain (.probeK k) := by
  unfold consumesUnseqPanic at h
  split at h
  · exact ⟨_, _, rfl⟩
  · cases h

@[simp] theorem unseqNextBound_pick {g : UnseqGraph} {thenB : Stmt} {st : List UnseqStatus}
    {tg : List (VarId × TargetRef)} {env : LocalEnv} {k : Cont} :
    unseqNextBound (.next (.unseqK g thenB st tg env .pick k)) = (g.ready st).length := rfl

/-- The accountant at a pick position reports the `unseqNext` site at EXACTLY
`unseqNextBound` when that is ≥ 2, and nothing otherwise (G-U) — the same
number the checker enumerates, read off the same frame, for every store. -/
theorem seqConsumption_unseqNext {σ : Store} {g : UnseqGraph} {thenB : Stmt}
    {st : List UnseqStatus} {tg : List (VarId × TargetRef)} {env : LocalEnv} {k : Cont} :
    seqConsumption ctx σ (.next (.unseqK g thenB st tg env .pick k))
      = if 2 ≤ (g.ready st).length then some (.unseqNext, (g.ready st).length) else none := by
  simp only [seqConsumption]

/-- The accountant at a probe-frame panic reports `unseqPanic` at bound 2, for every store. -/
theorem seqConsumption_unseqPanic {σ : Store} {chain : List PanicEntry} {k : Cont} :
    seqConsumption ctx σ (.panicking chain (.probeK k)) = some (.unseqPanic, 2) := by
  simp only [seqConsumption]

theorem consumesConvCap_strictK {v : GoValue} {op : StrictOp} {done : List GoValue}
    {env : LocalEnv} {k : Cont}
    (h : consumesConvCap (.retV v (.strictK op done [] env k)) = false) :
    op.convKind? = none := by
  simpa [consumesConvCap, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] using h

/-- The apply-position accessor's inversions (A7): a `some` names the frame. -/
theorem applyPos_stmt {c : Config} {op : StmtOp} {nt : Nat} {vs : List GoValue}
    {env : LocalEnv} {k : Cont} (h : c.applyPos = some (.stmt op nt, vs, env, k)) :
    ∃ v done, c = .retV v (.stmtOpK op nt done [] env k) ∧ vs = (v :: done).reverse := by
  unfold Config.applyPos at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, ApplyHead.stmt.injEq,
    reduceCtorEq, false_and] at h
  obtain ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
  exact ⟨_, _, rfl, rfl⟩

theorem applyPos_select {c : Config} {clauses : List (SelectClauseHead × Stmt)}
    {default? : Option Stmt} {vs : List GoValue} {env : LocalEnv} {k : Cont}
    (h : c.applyPos = some (.select clauses default?, vs, env, k)) :
    ∃ v done, c = .retV v (.selectOpsK clauses default? done [] env k) := by
  unfold Config.applyPos at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, ApplyHead.select.injEq,
    reduceCtorEq, false_and] at h
  obtain ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
  exact ⟨_, _, rfl⟩

theorem applyPos_sync {c : Config} {op : SyncOp} {vs : List GoValue}
    {env : LocalEnv} {k : Cont} (h : c.applyPos = some (.sync op, vs, env, k)) :
    ∃ v done, c = .retV v (.syncStK op done [] env k) := by
  unfold Config.applyPos at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, ApplyHead.sync.injEq,
    reduceCtorEq, false_and] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  exact ⟨_, _, rfl⟩

theorem applyPos_strict {c : Config} {op : StrictOp} {vs : List GoValue}
    {env : LocalEnv} {k : Cont} (h : c.applyPos = some (.strict op, vs, env, k)) :
    ∃ v done, c = .retV v (.strictK op done [] env k) ∧ vs = (v :: done).reverse := by
  unfold Config.applyPos at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, ApplyHead.strict.injEq,
    reduceCtorEq, false_and] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  exact ⟨_, _, rfl, rfl⟩

/-- Excluding the consuming configuration shapes makes the machine's
consumption projection `none`. The flags are the checker's conservative
shape tests; the conclusion uses the current `seqConsumption` definition. -/
theorem seqConsumption_none_of_flags {σ : Store} {c : Config}
    (hmi : ∀ (kv vv : Option VarId) (kt vt : Ty) (body : Stmt)
      (base : Option Loc) (produced start : Array Nat)
      (env : LocalEnv) (k : Cont),
      c ≠ .next (.mapIterK kv vv kt vt body base produced start env k))
    (hnc : consumesAppendSlice c = false)
    (hni : consumesRandIntn c = false)
    (hnk : consumesConvCap c = false)
    (hns : consumesSelect c = false)
    (hnv : consumesNilValueMethod ctx c = false)
    (hnt : consumesTryLock c = false)
    (hnu : consumesUnseqPanic c = false)
    (hnn : consumesUnseqNext c = false)
    (hnr : consumesRepanicCollapse c = false) :
    seqConsumption ctx σ c = none := by
  revert hmi hnc hni hnk hns hnv hnt hnu hnn hnr
  unfold seqConsumption
  split <;> intro hmi hnc hni hnk hns hnv hnt hnu hnn hnr
  · exact absurd rfl (hmi _ _ _ _ _ _ _ _ _ _)
  · simp [consumesUnseqPanic] at hnu
  · simp [consumesUnseqNext] at hnn
  · -- Unit 6b: the phase's collision draw and the abort's draw share the flag.
    simp only [consumesRepanicCollapse] at hnr
    split at hnr <;> simp [*]
  · split
    all_goals first
      | rfl
      | (rename_i heq
         obtain ⟨v, done, rfl, rfl⟩ := applyPos_stmt heq
         cases ‹StmtOp› <;> simp_all [stmtConsult?, consumesAppendSlice, consumesRandIntn])
      | (rename_i heq
         obtain ⟨v, done, rfl, rfl⟩ := applyPos_strict heq
         simp [strictConsult?, consumesConvCap_strictK hnk])
      | (rename_i heq
         obtain ⟨v, done, rfl⟩ := applyPos_select heq
         simp [consumesSelect] at hns)
      | (rename_i heq
         obtain ⟨v, done, rfl⟩ := applyPos_sync heq
         simp only [consumesTryLock, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hnt
         simp [syncConsult?, tryLockConsult?, hnt])
      | (split
         · rename_i fid args heq
           unfold consumesNilValueMethod at hnv
           rw [heq] at hnv
           (try dsimp only at hnv)
           unfold entryConsult?
           rw [ite_eq_left (by unfold nilValueMethodWidth; simp [hnv])]
         · rfl)

/-- The conservative shape flags imply stream obliviousness, by the current
consumption theorem. A successful step returns the stream untouched and
has the same successor, store and label under every stream. -/
theorem stepFn_oblivious {σ : Store} {c : Config} {ch₀ : Choices}
    {c' : Config} {σ' : Store} {ch₀' : Choices} {tr : StepLabel}
    (hmi : ∀ (kv vv : Option VarId) (kt vt : Ty) (body : Stmt)
      (base : Option Loc) (produced start : Array Nat)
      (env : LocalEnv) (k : Cont),
      c ≠ .next (.mapIterK kv vv kt vt body base produced start env k))
    (hnc : consumesAppendSlice c = false)
    (hni : consumesRandIntn c = false)
    (hnk : consumesConvCap c = false)
    (hns : consumesSelect c = false)
    (hnv : consumesNilValueMethod ctx c = false)
    (hnt : consumesTryLock c = false)
    (hnu : consumesUnseqPanic c = false)
    (hnn : consumesUnseqNext c = false)
    (hnr : consumesRepanicCollapse c = false)
    (h : stepFn ctx σ c ch₀ = .ok (c', σ', ch₀', tr)) :
    ch₀' = ch₀ ∧ ∀ ch : Choices, stepFn ctx σ c ch = .ok (c', σ', ch, tr) :=
  stepFn_consumption_none (seqConsumption_none_of_flags hmi hnc hni hnk hns hnv hnt hnu hnn hnr) h

/-- The `mapIterK` exclusion in the shape `stepFn_oblivious` consumes. -/
theorem isMapIterNext_false_elim {c : Config} (h : isMapIterNext c = false) :
    ∀ (kv vv : Option VarId) (kt vt : Ty) (body : Stmt)
      (base : Option Loc) (produced start : Array Nat)
      (env : LocalEnv) (k : Cont),
      c ≠ .next (.mapIterK kv vv kt vt body base produced start env k) := by
  intro kv vv kt vt body base produced start env k heq
  subst heq
  simp [isMapIterNext] at h

/-- A `consumesSelect` configuration is exactly the select-apply
shape. -/
theorem consumesSelect_shape {c : Config} (h : consumesSelect c = true) :
    ∃ v clauses default? done env k,
      c = .retV v (.selectOpsK clauses default? done [] env k) := by
  match c, h with
  | .retV v (.selectOpsK clauses default? done [] env k), _ =>
    exact ⟨v, clauses, default?, done, env, k, rfl⟩

/-- A non-select shape extracts no select-apply plan (the interception
dispatch's negative side, from the certified flag). -/
theorem selectApplyPlan_none_of_consumesSelect {c : Config}
    (h : consumesSelect c = false) : selectApplyPlan c = none := by
  cases hsp : selectApplyPlan c with
  | none => rfl
  | some p =>
      obtain ⟨v, clauses, d, dn, env, k⟩ := p
      obtain rfl := selectApplyPlan_shape hsp
      simp [consumesSelect] at h

/-- A non-consuming apply returns the stream untouched, whatever the
stream — with its emitted commit identity (Q2's 4th component). -/
theorem applySelect_of_done {s : Store}
    {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt}
    {vs : List GoValue} {env : LocalEnv} {k : Cont}
    {c' : Config} {s' : Store} {cl? : Option EvClause} {tr : AccessTrace}
    (h : applySelectCore ctx s clauses default? vs env k = .ok (.done c' s' cl? tr)) :
    ∀ ch : Choices,
      applySelect ctx s clauses default? vs env k ch = .ok (c', s', ch, [], cl?, tr) := by
  intro ch
  unfold applySelect
  simp only [h, Bind.bind, Except.bind]
  rfl

/-- **The `stepFn` path of the goroutine-step, as an equation** (route α,
Stage D): at a live goroutine that is not blocked, not aborting, not
spawning, whose arrival analysis is partnerless (`.cellPath`) and whose
configuration is not a select apply, `stepThread` IS `stepFn`'s step
wrapped in the pool's bookkeeping (the post-op boundary flag, the
`privateStep` event carrying the step's own label). Both the
oblivious (`stepThread_oblivious`) and the one-pick (`stepThread_pick_run`)
determinizations of `stepFn`-path shapes read the pool step off this
equation. -/
theorem stepThread_stepFn_path {s : Store} {ts : Array Thread} {i : Nat} {c : Config}
    (hti : ts[i]? = some (.running c none))
    (hblc : isBlockedConfig c = false)
    (hab : c.abort? = none)
    (hsp : spawnPlan c = none)
    (harr : arrivalCases ctx s ts i c = .ok .cellPath)
    (hselp : selectApplyPlan c = none)
    (ch : Choices) :
    stepThread ctx s ts i ch =
      (stepFn ctx s c ch >>= fun (c', s', ch₂, l) =>
        pure (ts.setIfInBounds i (Thread.afterStepWith (c.boundaryFacts s) c'), s', ch₂,
          ⟨i, .privateStep, ⟨l.trace, [] ++ l.picks, l.out⟩⟩)) := by
  unfold stepThread
  rw [hti]
  simp only [hblc, Bool.false_eq_true, reduceIte, hab, hsp, Bind.bind, Except.bind,
    arrivalPlan_of_cellPath (ch := ch) harr]
  rw [hselp]

/-- **Stream obliviousness of the certified goroutine-step shapes**:
under the `poolThreadOblivious` flags, a `stepThread` that succeeds
under one stream succeeds under EVERY stream, with the same successor,
the stream returned untouched, and the SAME step event (stage B: the
detector folds events, so obliviousness of the verdict rides on
obliviousness of the event — which holds by construction on certified
shapes, whose picks lists are empty and whose actions are computed
stream-freely). -/
theorem stepThread_oblivious {s : Store} {ts : Array Thread} {i : Nat}
    {ch₀ : Choices} {ts' : Array Thread} {s' : Store} {ch₀' : Choices}
    {ev : StepEvent}
    (hobl : poolThreadOblivious ctx s ts i = true)
    (h : stepThread ctx s ts i ch₀ = .ok (ts', s', ch₀', ev)) :
    ch₀' = ch₀
      ∧ ∀ ch : Choices, stepThread ctx s ts i ch = .ok (ts', s', ch, ev) := by
  have h₀ := h
  unfold poolThreadOblivious at hobl
  unfold stepThread at h
  cases hti : ts[i]? with
  | none => rw [hti] at hobl; cases hobl
  | some t =>
    rw [hti] at hobl h
    rcases t with ⟨c, b⟩ | msg
    case aborted => simp [throw, throwThe, MonadExceptOf.throw] at h
    cases b with
    | some site =>
      -- the boundary CLEAR (C5): stream-free
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      unfold stepThread
      rw [hti]
      rfl
    | none =>
    by_cases hblc : isBlockedConfig c = true
    · simp only [hblc, reduceIte, bind_eq_ok] at h
      obtain ⟨⟨c₂, s₂⟩, hres, h⟩ := h
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      unfold stepThread
      rw [hti]
      simp only [hblc, reduceIte, hres, Bind.bind, Except.bind]
      rfl
    · simp only [Bool.not_eq_true] at hblc
      simp only [hblc, Bool.false_eq_true, reduceIte] at h hobl
      cases hab : c.abort? with
      | some p =>
        -- THE ABORT (B4): outside the `repanicCollapse` shape (`hobl`) the
        -- consult is at bound 1 — no pop, no record — so the render reads
        -- no stream (landing chunk L3).
        obtain ⟨first, rest⟩ := p
        rw [hab] at h hobl
        simp only [Option.isSome_some, reduceIte, Bool.not_eq_true'] at hobl
        have hw : repanicCollapseWidth first rest ≤ 1 := by
          -- Unit 6b: the flag is read off the chain's shape at `.stop`; the
          -- abort is the SETTLED chain (`Config.abort?_some_iff`).
          obtain ⟨hc, hs⟩ := Config.abort?_some_iff.mp hab
          subst hc
          simp only [consumesRepanicCollapse, hs] at hobl
          simp [repanicCollapseWidth, hobl]
        simp only [Choices.consumeAtE_le_one hw, bind_eq_ok] at h
        obtain ⟨msg, hmsg, h⟩ := h
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        refine ⟨rfl, fun ch => ?_⟩
        unfold stepThread
        rw [hti]
        simp only [hblc, Bool.false_eq_true, reduceIte, hab, Choices.consumeAtE_le_one hw, hmsg,
          Bind.bind, Except.bind]
        rfl
      | none =>
        rw [hab] at h hobl
        simp only [Option.isSome_none, Bool.false_eq_true, reduceIte] at hobl
        -- Unit 6b: the preprint phase's collision draw is refused by the
        -- checker (fail closed); every shape below has the flag false.
        cases hnrc : consumesRepanicCollapse c with
        | true => rw [hnrc] at hobl; simp at hobl
        | false =>
        rw [hnrc] at hobl
        simp only [Bool.false_eq_true, reduceIte] at hobl
        cases hsp : spawnPlan c with
        | some p =>
          obtain ⟨cv, args, k⟩ := p
          rw [hsp] at h hobl
          simp only [Option.isSome_some, reduceIte, Bool.not_eq_true'] at hobl
          -- BUG-087 audit fix F1: a spawn is oblivious only outside the
          -- wrapper family (`hobl` now says so); the pick is inert there.
          have hn : ∀ fid captured, cv = .funcVal fid captured →
              nilValueMethodText? ctx fid (captured ++ args) = none := by
            intro fid captured hcv
            have hsite := entryCallSite?_of_spawnPlan hsp hcv
            cases hx : nilValueMethodText? ctx fid (captured ++ args) with
            | none => rfl
            | some alt =>
              simp [consumesNilValueMethod, hsite, hx] at hobl
          simp only [bind_eq_ok] at h
          obtain ⟨⟨parent', child, s₂, ch₂, tr₂⟩, hspawn, h⟩ := h
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          obtain ⟨rfl, hall⟩ := spawnStep_oblivious hn hspawn
          refine ⟨rfl, fun ch => ?_⟩
          unfold stepThread
          rw [hti]
          simp only [hblc, Bool.false_eq_true, reduceIte, hab, hsp, hall ch,
            Bind.bind, Except.bind]
          rfl
        | none =>
          rw [hsp] at h hobl
          simp only [Option.isSome_none, Bool.false_eq_true, reduceIte] at hobl
          -- the fail-closed stream flags
          cases hnsel : consumesSelect c with
          | true =>
            -- the slice-4 refinement: a select apply certified as
            -- partnerless AND non-consuming (`.done`) is oblivious —
            -- stage B: through the pool's select interception, whose
            -- event carries the stream-freely computed commit identity.
            rw [hnsel] at hobl
            simp only [reduceIte] at hobl
            obtain ⟨v, clauses, default?, dn, envS, kS, rfl⟩ :=
              consumesSelect_shape hnsel
            cases harr : arrivalCases ctx s ts i
                (.retV v (.selectOpsK clauses default? dn [] envS kS)) with
            | error e => rw [harr] at hobl; cases hobl
            | ok a =>
              cases a with
              | single bc cands => rw [harr] at hobl; cases hobl
              | multi os => rw [harr] at hobl; cases hobl
              | cellPath =>
                rw [harr] at hobl
                dsimp only at hobl
                simp only [selectApplyDone] at hobl
                cases happly : applySelectCore ctx s clauses default?
                    ((v :: dn).reverse) envS kS with
                | error e => rw [happly] at hobl; cases hobl
                | ok o =>
                  cases o with
                  | picks poll commits => rw [happly] at hobl; cases hobl
                  | done c₂ s₂ cl? tr₂ =>
                    simp only [bind_eq_ok] at h
                    obtain ⟨⟨plan, ch₁, ps₁⟩, hplan, h⟩ := h
                    rw [arrivalPlan_of_cellPath (ch := ch₀) harr] at hplan
                    simp only [Except.ok.injEq, Prod.mk.injEq] at hplan
                    obtain ⟨hp1, hp2, hp3⟩ := hplan
                    subst hp1
                    subst hp2
                    subst hp3
                    simp only [selectApplyPlan] at h
                    rw [applySelect_of_done happly ch₀] at h
                    simp only [pure_eq_ok] at h
                    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                    refine ⟨rfl, fun ch => ?_⟩
                    unfold stepThread
                    rw [hti]
                    simp only [hblc, Bool.false_eq_true, reduceIte, hab,
                      hsp, Bind.bind, Except.bind,
                      arrivalPlan_of_cellPath (ch := ch) harr]
                    simp only [selectApplyPlan]
                    rw [applySelect_of_done happly ch]
                    rfl
          | false =>
          rw [hnsel] at hobl
          simp only [Bool.false_eq_true, reduceIte] at hobl
          have hselp := selectApplyPlan_none_of_consumesSelect hnsel
          cases hnapp : consumesAppendSlice c with
          | true => rw [hnapp] at hobl; simp at hobl
          | false =>
          rw [hnapp] at hobl
          simp only [Bool.false_eq_true, reduceIte] at hobl
          -- unit 5b: the `randIntn` apply is refused (`false`)
          cases hnri : consumesRandIntn c with
          | true => rw [hnri] at hobl; simp at hobl
          | false =>
          rw [hnri] at hobl
          simp only [Bool.false_eq_true, reduceIte] at hobl
          -- R3 / b6: the conversion apply is refused (`false`)
          cases hnk : consumesConvCap c with
          | true => rw [hnk] at hobl; simp at hobl
          | false =>
          rw [hnk] at hobl
          simp only [Bool.false_eq_true, reduceIte] at hobl
          cases hntl : consumesTryLock c with
          | true => rw [hntl] at hobl; simp at hobl
          | false =>
          rw [hntl] at hobl
          simp only [Bool.false_eq_true, reduceIte] at hobl
          cases hnmi : isMapIterNext c with
          | true => rw [hnmi] at hobl; simp at hobl
          | false =>
          rw [hnmi] at hobl
          simp only [Bool.false_eq_true, reduceIte] at hobl
          cases hnnv : consumesNilValueMethod ctx c with
          | true => rw [hnnv] at hobl; simp at hobl
          | false =>
          rw [hnnv] at hobl
          simp only [Bool.false_eq_true, reduceIte] at hobl
          cases hnup : consumesUnseqPanic c with
          | true => rw [hnup] at hobl; simp at hobl
          | false =>
          rw [hnup] at hobl
          simp only [Bool.false_eq_true, reduceIte] at hobl
          cases hnn : consumesUnseqNext c with
          | true =>
            -- Route α (Stage D): a pick position whose ready set has ≤ 1
            -- member — the consult pops nothing (G-U), the projection is
            -- `none`, and `stepFn` is stream-oblivious there
            -- (`stepFn_consumption_none`); the pool step is its wrapper.
            rw [hnn] at hobl
            simp only [reduceIte, decide_eq_true_eq] at hobl
            obtain ⟨g, thenB, st, tg, env, k, rfl⟩ := consumesUnseqNext_shape hnn
            simp only [unseqNextBound_pick] at hobl
            have hsc : seqConsumption ctx s (.next (.unseqK g thenB st tg env .pick k)) = none := by
              rw [seqConsumption_unseqNext, ite_eq_right (by omega)]
            have hpath := stepThread_stepFn_path (ctx := ctx) (s := s) hti hblc hab hsp rfl rfl
            rw [hpath] at h₀
            simp only [bind_eq_ok] at h₀
            obtain ⟨⟨c₂, s₂, ch₂, tr₂⟩, hstep, h₀⟩ := h₀
            simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h₀
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h₀
            obtain ⟨rfl, hall⟩ := stepFn_consumption_none hsc hstep
            refine ⟨rfl, fun ch => ?_⟩
            rw [hpath ch, hall ch]
            rfl
          | false =>
          rw [hnn] at hobl
          simp only [Bool.false_eq_true, reduceIte] at hobl
          simp only [bind_eq_ok] at h
          obtain ⟨⟨plan, ch₁, ps₁⟩, hplan, h⟩ := h
          cases harr : arrivalCases ctx s ts i c with
          | error e =>
            rw [harr] at hobl
            cases hobl
          | ok r =>
            cases r with
            | cellPath =>
              rw [arrivalPlan_of_cellPath (ch := ch₀) harr] at hplan
              simp only [Except.ok.injEq, Prod.mk.injEq] at hplan
              obtain ⟨hp1, hp2, hp3⟩ := hplan
              subst hp1
              subst hp2
              subst hp3
              rw [hselp] at h
              dsimp only at h
              simp only [bind_eq_ok] at h
              obtain ⟨⟨c₂, s₂, ch₂, tr₂⟩, hstep, h⟩ := h
              simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              obtain ⟨rfl, hall⟩ := stepFn_oblivious
                (isMapIterNext_false_elim hnmi) hnapp hnri hnk hnsel hnnv hntl hnup hnn
                hnrc hstep
              refine ⟨rfl, fun ch => ?_⟩
              unfold stepThread
              rw [hti]
              simp only [hblc, Bool.false_eq_true, reduceIte, hab, hsp,
                Bind.bind, Except.bind, arrivalPlan_of_cellPath (ch := ch) harr]
              rw [hselp]
              dsimp only
              rw [hall ch]
              rfl
            | single bc cands =>
              rw [harr] at hobl
              rw [arrivalPlan_of_single (ch := ch₀) harr] at hplan
              simp only [Except.ok.injEq, Prod.mk.injEq] at hplan
              obtain ⟨hp1, hp2, hp3⟩ := hplan
              subst hp1
              subst hp2
              subst hp3
              cases cands with
              | nil => simp at hobl
              | cons cand rest =>
                cases rest with
                | nil =>
                  dsimp only at h
                  -- singleton candidate: the L4 site consumes nothing
                  rw [show Choices.consumeAtE .l4Waiter [cand].length ch₀
                    = (0, ch₀, []) from Choices.consumeAtE_le_one (by simp)] at h
                  simp only [List.getElem?_cons_zero] at h
                  simp only [bind_eq_ok] at h
                  obtain ⟨⟨ts₂, s₂⟩, hpair, h⟩ := h
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                  refine ⟨rfl, fun ch => ?_⟩
                  unfold stepThread
                  rw [hti]
                  simp only [hblc, Bool.false_eq_true, reduceIte, hab, hsp,
                    Bind.bind, Except.bind,
                    arrivalPlan_of_single (ch := ch) harr]
                  rw [show Choices.consumeAtE .l4Waiter [cand].length ch
                    = (0, ch, []) from Choices.consumeAtE_le_one (by simp)]
                  simp only [List.getElem?_cons_zero]
                  rw [hpair]
                  rfl
                | cons cand2 rest2 => simp at hobl
            | multi os =>
              rw [harr] at hobl
              cases hobl

/-- **`stepFn`-path pick determinization** (route α, Stage D — the `stepFn`
analogue of the L4 lemma `stepThread_l4_run`, vec→run direction): at a
`stepFn`-path shape (`stepThread_stepFn_path`'s hypotheses) whose
consumption projection is a bound-`b` pick with `2 ≤ b`, a SUCCESSFUL
explicit-pick goroutine-step `[p]` determines the step under every stream
whose raw pop at `b` reduces to `p` — same successor pool, same store, same
event, the stream's tail returned. The dedup checker instantiates it at the
two configuration-determined sites: `unseqPanic` (b = 2) and `unseqNext`
(b = `unseqNextBound c`). Nothing about the rest of the pool is assumed:
the pick's bound and effect are the stepping thread's own. -/
theorem stepThread_pick_run {s : Store} {ts : Array Thread} {i : Nat} {c : Config}
    (hti : ts[i]? = some (.running c none))
    (hblc : isBlockedConfig c = false)
    (hab : c.abort? = none)
    (hsp : spawnPlan c = none)
    (harr : arrivalCases ctx s ts i c = .ok .cellPath)
    (hselp : selectApplyPlan c = none)
    (_hloc : c.appendTargetLocal)
    {site : ChoiceSite} {b : Nat}
    (hsc : seqConsumption ctx s c = some (site, b))
    (hb : 2 ≤ b)
    {p : Nat} (hplt : p < b)
    {ts' : Array Thread} {s' : Store} {ev : StepEvent}
    (hvec : stepThread ctx s ts i [p] = .ok (ts', s', [], ev)) :
    ∀ {ch rest : Choices}, Choices.consume ch b = (p, rest) →
      stepThread ctx s ts i ch = .ok (ts', s', rest, ev) := by
  intro ch rest hcons
  have hnb : ¬ b ≤ 1 := by omega
  have hcP : Choices.consume [p] b = (p, []) := by
    simp only [Choices.consume]
    have hmax : max 1 b = b := by omega
    rw [hmax, Nat.mod_eq_of_lt hplt]
  rw [stepThread_stepFn_path hti hblc hab hsp harr hselp] at hvec
  simp only [bind_eq_ok] at hvec
  obtain ⟨⟨c₂, s₂, ch₂, tr₂⟩, hstep, hvec⟩ := hvec
  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hvec
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hvec
  obtain ⟨-, hall⟩ := stepFn_consumption_some hsc hstep
  have hpk : (Choices.consumeAt site b ch).1 = (Choices.consumeAt site b [p]).1 := by
    simp only [Choices.consumeAt, hnb, reduceIte, hcons, hcP]
  have hrest : (Choices.consumeAt site b ch).2 = rest := by
    simp only [Choices.consumeAt, hnb, reduceIte, hcons]
  rw [stepThread_stepFn_path hti hblc hab hsp harr hselp ch, hall ch hpk, hrest]
  rfl

/-- The one-layer unfolding of `execProgLoop`, as an equation
(incl. the BUG-044 main-exit window at `mainOutcome?`-some). -/
theorem execProgLoop_unfold (fuel : Nat) (m : MultiConfig) (r : RaceState)
    (ch : Choices) :
    execProgLoop ctx fuel m r ch
      = (if m.threads.isEmpty then
          throw (.internal "thread pool without a main goroutine")
        else
          match m.panicMsg? with
          | some msg => throw (.panic msg)
          | none =>
            match m.mainOutcome? with
            | some out =>
              (match runnableIdxs ctx m.shared m.threads with
              | [] => return (out, ch)
              | _ :: _ =>
                  let (pick, ch₁) := ch.consume 2
                  if pick == 0 then return (out, ch₁)
                  else
                    match fuel with
                    | 0 => throw .fuelOut
                    | fuel + 1 => do
                        let (m', choices', ev) ← stepMulti ctx m ch₁
                        let r' ← raceUpdate ev m' r
                        execProgLoop ctx fuel m' r' choices')
            | none =>
              if (runnableIdxs ctx m.shared m.threads).isEmpty then
                deadlockOrRefusal ctx m.shared m.threads
              else
                match fuel with
                | 0 => throw .fuelOut
                | fuel + 1 => do
                    let (m', choices', ev) ← stepMulti ctx m ch
                    let r' ← raceUpdate ev m' r
                    execProgLoop ctx fuel m' r' choices') := by
  rw [execProgLoop.eq_def]
  rfl


end GoLean.GoCore.Machine
