import GoLean.GoCore.MultiSound

/-!
# MultiWf preservation (channels arc slice 5)

The slice-2 scaffold's owed preservation theorem, by the slice-3 build
log's recorded route: the sequential `*_wf` conclusions carry the
step-level `nextAddr` monotonicity conjunct, and the pool assembly here
frames the foreign threads through it.
-/

namespace GoLean.GoCore.Machine

-- The unused-simp-arg linter misfires on the shared multi-branch simp
-- sets (an argument unused in one branch is load-bearing in another) —
-- the `MultiSound.lean`/`MachineSound.lean` precedent.
set_option linter.unusedSimpArgs false

/-! ## MultiWf preservation — the slice-2 scaffold DISCHARGED (slice 5)

The slice-3 build log's recorded route, executed: the sequential `*_wf`
family's conclusions were extended with the step-level
`σ.nextAddr ≤ σ'.nextAddr` conjunct (`applyChanOp_wf`,
`applySelect_wf`, `step_preserves_wf_loc` — `commitClause_wf`,
`enterRecvTargets_wf` and the `StmtOpPres` family already exposed it),
and the pool assembly below frames the FOREIGN threads through it: an
untouched goroutine's `ConfigWf` transports along allocator
monotonicity, and its iteration-typing component along the step's
types-invariance. `stepMulti_wf` is the preservation theorem the
slice-2 scaffold owed. -/

/-- `spawnedCont` inversion. -/
theorem spawnedCont_shape {c : Config} {k : Cont}
    (h : spawnedCont c = some k) : c = .spawned k := by
  match c, h with
  | .spawned _, h => cases h; rfl

/-- The spawn position's components are bounded by the configuration. -/
theorem spawnPlan_locSup {c : Config} {cv : GoValue} {args : List GoValue}
    {k : Cont} (h : spawnPlan c = some (cv, args, k)) :
    GoValue.locSup cv ≤ Config.locSup c
      ∧ goValueListSup args ≤ Config.locSup c
      ∧ Cont.locSup k ≤ Config.locSup c := by
  match c, h with
  | .retV cv' (.goCalleeK [] env k'), h =>
      simp only [spawnPlan, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Config.locSup, Cont.locSup, goValueListSup, exprListSup,
        Nat.max_le]
      omega
  | .retV v (.goArgsK cv' vals [] env k'), h =>
      simp only [spawnPlan, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [goValueListSup_append]
      simp only [Config.locSup, Cont.locSup, goValueListSup, exprListSup,
        Nat.max_le]
      omega

/-- The spawn position's continuation is iteration-typed by the
configuration's own check. -/
theorem spawnPlan_iters {types : TypeEnv} {c : Config} {cv : GoValue}
    {args : List GoValue} {k : Cont}
    (h : spawnPlan c = some (cv, args, k))
    (hi : Config.itersNormalized types c = true) :
    Cont.itersNormalized types k = true := by
  match c, h with
  | .retV cv' (.goCalleeK [] env k'), h =>
      simp only [spawnPlan, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simpa [Config.itersNormalized, Cont.itersNormalized] using hi
  | .retV v (.goArgsK cv' vals [] env k'), h =>
      simp only [spawnPlan, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simpa [Config.itersNormalized, Cont.itersNormalized] using hi

/-- `spawnStep` preservation: wf state out, both successor
configurations bounded and iteration-typed, types unchanged, allocator
monotone. -/
theorem spawnStep_wf {s : ExecState} {cv : GoValue} {args : List GoValue}
    {k : Cont} {p child : Config} {s' : ExecState} {types : TypeEnv}
    (hw : StateWf s) (hcv : GoValue.locSup cv ≤ s.nextAddr)
    (hargs : goValueListSup args ≤ s.nextAddr)
    (hk : Cont.locSup k ≤ s.nextAddr)
    (hik : Cont.itersNormalized types k = true)
    (h : spawnStep s cv args k = .ok (p, child, s')) :
    StateWf s' ∧ Config.locSup p ≤ s'.nextAddr
      ∧ Config.locSup child ≤ s'.nextAddr
      ∧ s'.types = s.types ∧ s.nextAddr ≤ s'.nextAddr
      ∧ Config.itersNormalized types p = true
      ∧ Config.itersNormalized types child = true := by
  unfold spawnStep at h
  split at h
  · rename_i fid captured
    split at h
    · rename_i func frameEnv resultLocs s₂ henter
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hcap : goValueListSup captured ≤ s.nextAddr := by
        simpa [GoValue.locSup] using hcv
      obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := enterFrame_wf hw
        (by rw [goValueListSup_append]; omega) henter
      refine ⟨w1, ?_, ?_, w3, w2, ?_, ?_⟩
      · simpa [Config.locSup] using Nat.le_trans hk w2
      · simp only [Config.locSup, Cont.locSup, locListSup, deferListSup,
          Nat.max_le]
        omega
      · simpa [Config.itersNormalized, Cont.itersNormalized] using hik
      · simp [Config.itersNormalized, Cont.itersNormalized]
    · rename_i msg henter
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨hw, ?_, ?_, rfl, Nat.le_refl _, ?_, ?_⟩
      · simpa [Config.locSup] using hk
      · simp [Config.locSup, panicChainSup, runtimeErrorValue_locSup,
          Cont.locSup]
      · simpa [Config.itersNormalized, Cont.itersNormalized] using hik
      · simp [Config.itersNormalized, Cont.itersNormalized]
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

/-- `resumeRecvDelivery` preservation (bounds + iteration typing). -/
theorem resumeRecvDelivery_wf {s : ExecState} {v : GoValue} {ok : Bool}
    {targets : List Assignee} {env : LocalEnv} {k : Cont}
    {c' : Config} {s' : ExecState} {types : TypeEnv}
    (hw : StateWf s) (hv : GoValue.locSup v ≤ s.nextAddr)
    (ht : assigneeListSup targets ≤ s.nextAddr)
    (henv : LocalEnv.locSup env ≤ s.nextAddr)
    (hk : Cont.locSup k ≤ s.nextAddr)
    (hik : Cont.itersNormalized types k = true)
    (h : resumeRecvDelivery s v ok targets env k = .ok (c', s')) :
    StateWf s' ∧ Config.locSup c' ≤ s'.nextAddr ∧ s'.types = s.types
      ∧ s.nextAddr ≤ s'.nextAddr
      ∧ Config.itersNormalized types c' = true := by
  unfold resumeRecvDelivery at h
  split at h
  · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hw, by simpa [Config.locSup] using hk, rfl, Nat.le_refl _,
      by simpa [Config.itersNormalized] using hik⟩
  · rename_i t ts
    obtain ⟨q1, q2, q3, q4⟩ := enterRecvTargets_wf hw ht
      (Nat.le_trans (recvStores_locSup ((t :: ts).length)) hv)
      (by simp [Stmt.locSup, stmtListSup]) henv hk h
    exact ⟨q1, q2, q3, q4, enterRecvTargets_itersNormalized h hik⟩

/-- `selectRecvDelivery` preservation (bounds + iteration typing). -/
theorem selectRecvDelivery_wf {s : ExecState} {v : GoValue} {ok : Bool}
    {targets : List Assignee} {body : Stmt} {env : LocalEnv} {k : Cont}
    {c' : Config} {s' : ExecState} {types : TypeEnv}
    (hw : StateWf s) (hv : GoValue.locSup v ≤ s.nextAddr)
    (ht : assigneeListSup targets ≤ s.nextAddr)
    (hb : Stmt.locSup body ≤ s.nextAddr)
    (henv : LocalEnv.locSup env ≤ s.nextAddr)
    (hk : Cont.locSup k ≤ s.nextAddr)
    (hik : Cont.itersNormalized types k = true)
    (h : selectRecvDelivery s v ok targets body env k = .ok (c', s')) :
    StateWf s' ∧ Config.locSup c' ≤ s'.nextAddr ∧ s'.types = s.types
      ∧ s.nextAddr ≤ s'.nextAddr
      ∧ Config.itersNormalized types c' = true := by
  unfold selectRecvDelivery at h
  split at h
  · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨hw, ?_, rfl, Nat.le_refl _, ?_⟩
    · simp only [Config.locSup, Nat.max_le]
      omega
    · simpa [Config.itersNormalized] using hik
  · rename_i t ts
    obtain ⟨q1, q2, q3, q4⟩ := enterRecvTargets_wf hw ht
      (Nat.le_trans (recvStores_locSup ((t :: ts).length)) hv) hb henv hk h
    exact ⟨q1, q2, q3, q4, enterRecvTargets_itersNormalized h hik⟩

/-- `resumeThread` preservation: the wake of a parked goroutine keeps
the state wf (allocator monotone, types unchanged) and produces a
bounded, iteration-typed configuration. -/
theorem resumeThread_wf {s : ExecState} {c c' : Config} {s' : ExecState}
    (hw : StateWf s) (hc : ConfigWf s.nextAddr c)
    (hi : Config.itersNormalized s.types c = true)
    (h : resumeThread s c = .ok (c', s')) :
    StateWf s' ∧ Config.locSup c' ≤ s'.nextAddr ∧ s'.types = s.types
      ∧ s.nextAddr ≤ s'.nextAddr
      ∧ Config.itersNormalized s.types c' = true := by
  have hheap := hw.heap_le
  unfold resumeThread at h
  split at h
  · -- blockedSend
    rename_i loc v k
    have hb : Loc.locSup loc ≤ s.nextAddr ∧ GoValue.locSup v ≤ s.nextAddr
        ∧ Cont.locSup k ≤ s.nextAddr := by
      simp only [ConfigWf, Config.locSup, optLocSup, Nat.max_le] at hc
      omega
    have hik : Cont.itersNormalized s.types k = true := by
      simpa [Config.itersNormalized] using hi
    simp only [bind_eq_ok] at h
    obtain ⟨⟨buf, capacity, closed⟩, hcell, h⟩ := h
    have hbufb := chanCell_locSup hcell
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨hw, ?_, rfl, Nat.le_refl _, ?_⟩
      · simp only [Config.locSup, panicChainSup, runtimeErrorValue_locSup,
          Nat.max_le]
        omega
      · simpa [Config.itersNormalized] using hik
    · split at h
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨s₂, hst, rfl, rfl⟩ := h
        obtain ⟨w1, w2, w3, w4, w5⟩ := storeLoc_pres hw hb.1
          (by rw [show GoValue.locSup (.chanData (buf.push v) capacity closed)
                = goValueListSup (buf.push v).toList from rfl,
              goValueListSup_push]
              omega) hst
        refine ⟨w1, ?_, w4, w2, ?_⟩
        · simp only [Config.locSup]
          omega
        · simpa [Config.itersNormalized] using hik
      · simp [throw, throwThe, MonadExceptOf.throw] at h
  · -- blockedRecv
    rename_i loc targets elem env k
    have hb : Loc.locSup loc ≤ s.nextAddr ∧ assigneeListSup targets ≤ s.nextAddr
        ∧ LocalEnv.locSup env ≤ s.nextAddr ∧ Cont.locSup k ≤ s.nextAddr := by
      simp only [ConfigWf, Config.locSup, optLocSup, Nat.max_le] at hc
      omega
    have hik : Cont.itersNormalized s.types k = true := by
      simpa [Config.itersNormalized] using hi
    simp only [bind_eq_ok] at h
    obtain ⟨⟨buf, capacity, closed⟩, hcell, h⟩ := h
    have hbufb := chanCell_locSup hcell
    split at h
    · -- dequeue
      rename_i v hv
      have hvb : GoValue.locSup v ≤ s.nextAddr := by
        have := goValueListSup_mem (l := buf.toList) (v := v)
          (List.mem_of_getElem? (by simpa using hv))
        omega
      simp only [bind_eq_ok] at h
      obtain ⟨s₁, hst, h⟩ := h
      obtain ⟨w1, w2, w3, w4, w5⟩ := storeLoc_pres hw hb.1
        (by rw [show GoValue.locSup (.chanData (buf.eraseIdx! 0) capacity closed)
              = goValueListSup (buf.eraseIdx! 0).toList from rfl]
            exact Nat.le_trans goValueListSup_eraseIdx! (by omega)) hst
      obtain ⟨q1, q2, q3, q4, q5⟩ := resumeRecvDelivery_wf w1 (by omega)
        (by omega) (by omega) (by omega) hik h
      exact ⟨q1, q2, q3.trans w4, Nat.le_trans w2 q4, q5⟩
    · split at h
      · -- closed: zero value
        simp only [bind_eq_ok] at h
        obtain ⟨z, hz, h⟩ := h
        have hzb : GoValue.locSup z ≤ s.nextAddr := by
          rw [defaultValue_locSup hz]; omega
        obtain ⟨q1, q2, q3, q4, q5⟩ := resumeRecvDelivery_wf hw hzb hb.2.1
          hb.2.2.1 hb.2.2.2 hik h
        exact ⟨q1, q2, q3, q4, q5⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at h
  · -- blockedSelect
    rename_i evs env k
    have hb : evClausesSup evs ≤ s.nextAddr ∧ LocalEnv.locSup env ≤ s.nextAddr
        ∧ Cont.locSup k ≤ s.nextAddr := by
      simp only [ConfigWf, Config.locSup, Nat.max_le] at hc
      omega
    have hik : Cont.itersNormalized s.types k = true := by
      simpa [Config.itersNormalized] using hi
    simp only [bind_eq_ok] at h
    obtain ⟨rc, hrc, h⟩ := h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · rename_i cl rest
      have hclb : evClauseSup cl ≤ s.nextAddr := by
        have hmem : cl ∈ evs := readyClauses_subset hrc cl (List.mem_cons_self ..)
        exact Nat.le_trans (evClausesSup_mem hmem) hb.1
      obtain ⟨w1, w2, w3, w4⟩ := commitClause_wf hw hclb hb.2.1 hb.2.2 h
      exact ⟨w1, w2, w3, w4, commitClause_itersNormalized h hik⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h


/-- Indexed lookup of the pool hypothesis. -/
theorem pool_get_wf {threads : Array Config} {j : Nat} {c : Config}
    {na : Nat} {types : TypeEnv}
    (hts : ∀ t (ht : t < threads.size), ConfigWf na threads[t]
      ∧ Config.itersNormalized types threads[t] = true)
    (hj : threads[j]? = some c) :
    ConfigWf na c ∧ Config.itersNormalized types c = true := by
  obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hj
  exact heq ▸ hts j hlt

/-- Frame lemma for the two-index pool update every pairing performs:
the two touched slots carry the new bounds; every other goroutine's
`ConfigWf` transports along allocator monotonicity and its typing
component is untouched. -/
theorem pool_set2_wf {threads : Array Config} {i j : Nat} {a b : Config}
    {na na' : Nat} {types : TypeEnv}
    (hmono : na ≤ na')
    (hts : ∀ t (ht : t < threads.size), ConfigWf na threads[t]
      ∧ Config.itersNormalized types threads[t] = true)
    (ha : Config.locSup a ≤ na') (hia : Config.itersNormalized types a = true)
    (hb : Config.locSup b ≤ na') (hib : Config.itersNormalized types b = true) :
    ∀ t (ht : t < ((threads.setIfInBounds i a).setIfInBounds j b).size),
      ConfigWf na' ((threads.setIfInBounds i a).setIfInBounds j b)[t]
        ∧ Config.itersNormalized types
            ((threads.setIfInBounds i a).setIfInBounds j b)[t] = true := by
  intro t ht
  have ht' : t < threads.size := by simpa using ht
  simp only [Array.getElem_setIfInBounds, Array.size_setIfInBounds, ht']
  split
  · exact ⟨hb, hib⟩
  · split
    · exact ⟨ha, hia⟩
    · exact ⟨Nat.le_trans (hts t ht').1 hmono, (hts t ht').2⟩

/-- The channel loc behind a chan value is bounded by the value. -/
theorem chanValueLoc_locSup {v : GoValue} {loc : Loc}
    (h : chanValueLoc v = some loc) : Loc.locSup loc ≤ GoValue.locSup v := by
  match v, h with
  | .chan cv, h =>
      simp only [chanValueLoc] at h
      simp [GoValue.locSup, h, optLocSup]

/-- The would-block shape a CHAN-OP arrival pairing carries is bounded
and iteration-typed by the arriving operands. -/
theorem chanArrivalPlan_wf {s : ExecState} {threads : Array Config} {i : Nat}
    {op : ChanStOp} {vs : List GoValue} {env : LocalEnv} {k : Cont}
    {bc : Config} {cands : List (Nat × PairTarget)} {types : TypeEnv}
    (_hw : StateWf s) (hvs : goValueListSup vs ≤ s.nextAddr)
    (hop : chanStOpSup op ≤ s.nextAddr)
    (henv : LocalEnv.locSup env ≤ s.nextAddr)
    (hk : Cont.locSup k ≤ s.nextAddr)
    (hik : Cont.itersNormalized types k = true)
    (h : chanArrivalPlan s threads i op vs env k = .ok (some (bc, cands))) :
    Config.locSup bc ≤ s.nextAddr
      ∧ Config.itersNormalized types bc = true := by
  unfold chanArrivalPlan at h
  split at h
  · -- send
    rename_i elem chv vv
    simp only [goValueListSup, Nat.max_le] at hvs
    split at h
    · simp at h
    · rename_i loc hloc
      have hlocb := chanValueLoc_locSup hloc
      by_cases hws : (recvSideWaiters threads i loc).isEmpty = true
      · simp [hws] at h
      · simp only [Bool.not_eq_true] at hws
        simp only [hws, Bool.false_eq_true, reduceIte, bind_eq_ok] at h
        obtain ⟨⟨buf, cap, closed⟩, hcell, h⟩ := h
        split at h
        · simp at h
        · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq,
            Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨v', hv', hbc, hcands⟩ := h
          subst hbc
          have hv'b := normalizeValueForTy_locSup hv'
          refine ⟨?_, by simpa [Config.itersNormalized] using hik⟩
          simp only [Config.locSup, optLocSup, Nat.max_le]
          omega
  · -- recv
    rename_i targets elem chv
    simp only [goValueListSup, Nat.max_le] at hvs
    simp only [chanStOpSup] at hop
    split at h
    · simp at h
    · rename_i loc hloc
      have hlocb := chanValueLoc_locSup hloc
      by_cases hws : (sendSideWaiters threads i loc).isEmpty = true
      · simp [hws] at h
      · simp only [Bool.not_eq_true] at hws
        simp only [hws, Bool.false_eq_true, reduceIte, bind_eq_ok] at h
        obtain ⟨⟨buf, cap, closed⟩, hcell, h⟩ := h
        split at h
        · simp at h
        · simp only [pure_eq_ok, Except.ok.injEq, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨hbc, hcands⟩ := h
          subst hbc
          refine ⟨?_, by simpa [Config.itersNormalized] using hik⟩
          simp only [Config.locSup, optLocSup, Nat.max_le]
          omega
  · simp at h

/-- The `.single` analysis' would-block shape is bounded and typed by
the arriving configuration. -/
theorem arrivalCases_single_wf {s : ExecState} {threads : Array Config}
    {i : Nat} {c bc : Config} {cs : List (Nat × PairTarget)}
    (hw : StateWf s) (hc : ConfigWf s.nextAddr c)
    (hi : Config.itersNormalized s.types c = true)
    (h : arrivalCases s threads i c = .ok (.single bc cs)) :
    Config.locSup bc ≤ s.nextAddr
      ∧ Config.itersNormalized s.types bc = true := by
  unfold arrivalCases at h
  split at h
  · -- chan-op apply position
    rename_i v op done env k
    simp only [bind_eq_ok] at h
    obtain ⟨plan, hplan, h⟩ := h
    match plan, h with
    | none, h => simp at h
    | some (bc', cs'), h =>
      simp only [pure_eq_ok, Except.ok.injEq, ArrivalAnalysis.single.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hb : GoValue.locSup v ≤ s.nextAddr
          ∧ chanStOpSup op ≤ s.nextAddr
          ∧ goValueListSup done ≤ s.nextAddr
          ∧ LocalEnv.locSup env ≤ s.nextAddr
          ∧ Cont.locSup k ≤ s.nextAddr := by
        simp only [ConfigWf, Config.locSup, Cont.locSup, exprListSup,
          Nat.max_le] at hc
        omega
      have hvsb : goValueListSup ((v :: done).reverse) ≤ s.nextAddr := by
        rw [goValueListSup_reverse]
        simp only [goValueListSup, Nat.max_le]
        omega
      exact chanArrivalPlan_wf hw hvsb hb.2.1 hb.2.2.2.1 hb.2.2.2.2
        (by simpa [Config.itersNormalized, Cont.itersNormalized] using hi) hplan
  · -- select apply position
    rename_i v clauses default? done env k
    have hb : GoValue.locSup v ≤ s.nextAddr
        ∧ selectClausesSup clauses ≤ s.nextAddr
        ∧ goValueListSup done ≤ s.nextAddr
        ∧ LocalEnv.locSup env ≤ s.nextAddr
        ∧ Cont.locSup k ≤ s.nextAddr := by
      simp only [ConfigWf, Config.locSup, Cont.locSup, exprListSup,
        optStmtSup, Nat.max_le] at hc
      omega
    have hvsb : goValueListSup ((v :: done).reverse) ≤ s.nextAddr := by
      rw [goValueListSup_reverse]
      simp only [goValueListSup, Nat.max_le]
      omega
    have hik : Cont.itersNormalized s.types k = true := by
      simpa [Config.itersNormalized, Cont.itersNormalized] using hi
    -- walk the select analysis to its `.single` exits: the shape is
    -- always `.blockedSelect evs env k` with `evs` the evaluated
    -- clauses.
    unfold selectArrivalCases at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [bind_eq_ok] at h
        obtain ⟨evs, hevs, h⟩ := h
        have hevsb : evClausesSup evs ≤ s.nextAddr := by
          have := evalClauses_sup hevs
          omega
        obtain ⟨readiness, hread, h⟩ := h
        split at h
        · simp at h
        · rename_i ci cell ws
          split at h
          · simp at h
          · split at h
            · simp [throw, throwThe, MonadExceptOf.throw] at h
            · simp only [pure_eq_ok, Except.ok.injEq,
                ArrivalAnalysis.single.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨?_, by simpa [Config.itersNormalized] using hik⟩
              simp only [Config.locSup, Nat.max_le]
              omega
        · rename_i ready
          split at h
          · simp at h
          · simp only [bind_eq_ok] at h
            obtain ⟨os, hos, h⟩ := h
            simp only [pure_eq_ok, Except.ok.injEq] at h
            cases h
  · simp only [pure_eq_ok, Except.ok.injEq] at h
    cases h

/-- The `.multi` analysis' SELECTED outcome is bounded and typed by the
arriving configuration: a `.pair`'s would-block shape like the single
case, a `.commit`'s clause a member of the evaluated clause list. -/
theorem arrivalCases_multi_wf {s : ExecState} {threads : Array Config}
    {i : Nat} {c : Config} {os : List ArrivalOutcome} {sel : Nat}
    {o : ArrivalOutcome}
    (_hw : StateWf s) (hc : ConfigWf s.nextAddr c)
    (hi : Config.itersNormalized s.types c = true)
    (h : arrivalCases s threads i c = .ok (.multi os))
    (hget : os[sel]? = some o) :
    (∀ {bc cs}, o = ArrivalOutcome.pair bc cs →
      Config.locSup bc ≤ s.nextAddr
        ∧ Config.itersNormalized s.types bc = true)
    ∧ (∀ {cl env k}, o = ArrivalOutcome.commit cl env k →
        evClauseSup cl ≤ s.nextAddr ∧ LocalEnv.locSup env ≤ s.nextAddr
          ∧ Cont.locSup k ≤ s.nextAddr
          ∧ Cont.itersNormalized s.types k = true) := by
  unfold arrivalCases at h
  split at h
  · -- chan-op apply: never `.multi`
    rename_i v op done env k
    simp only [bind_eq_ok] at h
    obtain ⟨plan, hplan, h⟩ := h
    match plan, h with
    | none, h => simp at h
    | some (bc', cs'), h => simp at h
  · -- select apply
    rename_i v clauses default? done env k
    have hb : GoValue.locSup v ≤ s.nextAddr
        ∧ selectClausesSup clauses ≤ s.nextAddr
        ∧ goValueListSup done ≤ s.nextAddr
        ∧ LocalEnv.locSup env ≤ s.nextAddr
        ∧ Cont.locSup k ≤ s.nextAddr := by
      simp only [ConfigWf, Config.locSup, Cont.locSup, exprListSup,
        optStmtSup, Nat.max_le] at hc
      omega
    have hvsb : goValueListSup ((v :: done).reverse) ≤ s.nextAddr := by
      rw [goValueListSup_reverse]
      simp only [goValueListSup, Nat.max_le]
      omega
    have hik : Cont.itersNormalized s.types k = true := by
      simpa [Config.itersNormalized, Cont.itersNormalized] using hi
    unfold selectArrivalCases at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [bind_eq_ok] at h
        obtain ⟨evs, hevs, h⟩ := h
        have hevsb : evClausesSup evs ≤ s.nextAddr := by
          have := evalClauses_sup hevs
          omega
        obtain ⟨readiness, hread, h⟩ := h
        split at h
        · simp at h
        · rename_i ci cell ws
          split at h
          · simp at h
          · split at h
            · simp [throw, throwThe, MonadExceptOf.throw] at h
            · simp only [pure_eq_ok, Except.ok.injEq] at h
              cases h
        · rename_i ready
          split at h
          · simp at h
          · simp only [bind_eq_ok] at h
            obtain ⟨os₂, hos, h⟩ := h
            simp only [pure_eq_ok, Except.ok.injEq,
              ArrivalAnalysis.multi.injEq] at h
            subst h
            obtain ⟨⟨ci, cell, ws⟩, hmem, hmk⟩ := mapM_getElem?_mem hos hget
            -- invert `mkOutcome` on the selected element
            simp only at hmk
            split at hmk
            · -- ws empty: a commit of evs[ci]
              split at hmk
              · rename_i cl hcl
                simp only [pure_eq_ok, Except.ok.injEq] at hmk
                subst hmk
                refine ⟨?_, ?_⟩
                · intro bc cs heq
                  cases heq
                · intro cl' env' k' heq
                  cases heq
                  have hclb : evClauseSup cl ≤ s.nextAddr := by
                    have hmem' : cl ∈ evs :=
                      List.mem_of_getElem? hcl
                    exact Nat.le_trans (evClausesSup_mem hmem') hevsb
                  exact ⟨hclb, hb.2.2.2.1, hb.2.2.2.2, hik⟩
              · simp [throw, throwThe, MonadExceptOf.throw] at hmk
            · split at hmk
              · simp [throw, throwThe, MonadExceptOf.throw] at hmk
              · simp only [pure_eq_ok, Except.ok.injEq] at hmk
                subst hmk
                refine ⟨?_, ?_⟩
                · intro bc cs heq
                  cases heq
                  refine ⟨?_, by simpa [Config.itersNormalized] using hik⟩
                  simp only [Config.locSup, Nat.max_le]
                  omega
                · intro cl' env' k' heq
                  cases heq
  · simp only [pure_eq_ok, Except.ok.injEq] at h
    cases h




set_option maxHeartbeats 1600000 in
/-- `applyPairing` preservation: the arrival pairing keeps the shared
state wf (allocator monotone, types unchanged), preserves the pool
size, and leaves EVERY slot bounded and iteration-typed — the two
touched slots by the pairing outcome's own bounds, the foreign threads
by the monotonicity frame. -/
theorem applyPairing_wf {s : ExecState} {threads : Array Config} {i : Nat}
    {bc : Config} {cand : Nat × PairTarget} {ts' : Array Config}
    {s' : ExecState}
    (hw : StateWf s)
    (hts : ∀ t (ht : t < threads.size), ConfigWf s.nextAddr threads[t]
      ∧ Config.itersNormalized s.types threads[t] = true)
    (hbc : ConfigWf s.nextAddr bc)
    (hibc : Config.itersNormalized s.types bc = true)
    (h : applyPairing s threads i bc cand = .ok (ts', s')) :
    StateWf s' ∧ s'.types = s.types ∧ s.nextAddr ≤ s'.nextAddr
      ∧ ts'.size = threads.size
      ∧ ∀ t (ht : t < ts'.size), ConfigWf s'.nextAddr ts'[t]
          ∧ Config.itersNormalized s.types ts'[t] = true := by
  have hheap := hw.heap_le
  obtain ⟨cn, ct⟩ := cand
  cases bc
  case blockedSend ch v k =>
    have hb : optLocSup ch ≤ s.nextAddr ∧ GoValue.locSup v ≤ s.nextAddr
        ∧ Cont.locSup k ≤ s.nextAddr := by
      simp only [ConfigWf, Config.locSup, Nat.max_le] at hbc
      omega
    have hik : Cont.itersNormalized s.types k = true := by
      simpa [Config.itersNormalized] using hibc
    cases ct
    case opWaiter j =>
      cases ch
      case none => simp [applyPairing, throw, throwThe, MonadExceptOf.throw] at h
      case some loc =>
        simp only [applyPairing] at h
        cases hj : threads[j]? with
        | none => simp [hj, throw, throwThe, MonadExceptOf.throw] at h
        | some pc =>
          simp only [hj] at h
          cases pc <;>
            try (simp [throw, throwThe, MonadExceptOf.throw] at h)
          case blockedRecv ch2 targets elem2 envr kr =>
            obtain ⟨hpc, hpi⟩ := pool_get_wf hts hj
            have hpb : assigneeListSup targets ≤ s.nextAddr
                ∧ LocalEnv.locSup envr ≤ s.nextAddr
                ∧ Cont.locSup kr ≤ s.nextAddr := by
              simp only [ConfigWf, Config.locSup, Nat.max_le] at hpc
              omega
            have hpk : Cont.itersNormalized s.types kr = true := by
              simpa [Config.itersNormalized] using hpi
            simp only [bind_eq_ok] at h
            obtain ⟨⟨buf, cap, closed⟩, hcell, h⟩ := h
            split at h
            · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq,
                Prod.mk.injEq] at h
              obtain ⟨⟨cr, s₂⟩, hdel, hts', hs'⟩ := h
              subst hts' hs'
              obtain ⟨q1, q2, q3, q4, q5⟩ := resumeRecvDelivery_wf hw hb.2.1
                hpb.1 hpb.2.1 hpb.2.2 hpk hdel
              refine ⟨q1, q3, q4, by simp, ?_⟩
              exact pool_set2_wf q4 hts
                (by simpa [Config.locSup] using Nat.le_trans hb.2.2 q4)
                (by simpa [Config.itersNormalized] using hik) q2 q5
            · simp [throw, throwThe, MonadExceptOf.throw] at h
    case selectWaiter j ci =>
      cases ch
      case none => simp [applyPairing, throw, throwThe, MonadExceptOf.throw] at h
      case some loc =>
        simp only [applyPairing] at h
        cases hj : threads[j]? with
        | none => simp [hj, throw, throwThe, MonadExceptOf.throw] at h
        | some pc =>
          simp only [hj] at h
          cases pc <;>
            try (simp [throw, throwThe, MonadExceptOf.throw] at h)
          case blockedSelect evs envs ks =>
            obtain ⟨hpc, hpi⟩ := pool_get_wf hts hj
            have hpb : evClausesSup evs ≤ s.nextAddr
                ∧ LocalEnv.locSup envs ≤ s.nextAddr
                ∧ Cont.locSup ks ≤ s.nextAddr := by
              simp only [ConfigWf, Config.locSup, Nat.max_le] at hpc
              omega
            have hpk : Cont.itersNormalized s.types ks = true := by
              simpa [Config.itersNormalized] using hpi
            cases hcl : evs[ci]? with
            | none => simp [hcl, throw, throwThe, MonadExceptOf.throw] at h
            | some cl =>
              simp only [hcl] at h
              cases cl with
              | sendEv chv2 vv2 selem2 body2 =>
                  simp [throw, throwThe, MonadExceptOf.throw] at h
              | recvEv chv2 targets2 elem2 body2 =>
                have hclb : evClauseSup (.recvEv chv2 targets2 elem2 body2)
                    ≤ s.nextAddr := by
                  have hmem : (EvClause.recvEv chv2 targets2 elem2 body2) ∈ evs :=
                    List.mem_of_getElem? hcl
                  exact Nat.le_trans (evClausesSup_mem hmem) hpb.1
                simp only [evClauseSup, Nat.max_le] at hclb
                simp only [bind_eq_ok] at h
                obtain ⟨⟨buf, cap, closed⟩, hcell, h⟩ := h
                split at h
                · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq,
                    Prod.mk.injEq] at h
                  obtain ⟨⟨cs', s₂⟩, hdel, hts', hs'⟩ := h
                  subst hts' hs'
                  obtain ⟨q1, q2, q3, q4, q5⟩ := selectRecvDelivery_wf hw hb.2.1
                    (by omega) (by omega) hpb.2.1 hpb.2.2 hpk hdel
                  refine ⟨q1, q3, q4, by simp, ?_⟩
                  exact pool_set2_wf q4 hts
                    (by simpa [Config.locSup] using Nat.le_trans hb.2.2 q4)
                    (by simpa [Config.itersNormalized] using hik) q2 q5
                · simp [throw, throwThe, MonadExceptOf.throw] at h
  case blockedRecv ch targets elem env k =>
    have hb : optLocSup ch ≤ s.nextAddr ∧ assigneeListSup targets ≤ s.nextAddr
        ∧ LocalEnv.locSup env ≤ s.nextAddr ∧ Cont.locSup k ≤ s.nextAddr := by
      simp only [ConfigWf, Config.locSup, Nat.max_le] at hbc
      omega
    have hik : Cont.itersNormalized s.types k = true := by
      simpa [Config.itersNormalized] using hibc
    cases ct
    case opWaiter j =>
      cases ch
      case none => simp [applyPairing, throw, throwThe, MonadExceptOf.throw] at h
      case some loc =>
        have hlocb : Loc.locSup loc ≤ s.nextAddr := by
          simpa [optLocSup] using hb.1
        simp only [applyPairing] at h
        cases hj : threads[j]? with
        | none => simp [hj, throw, throwThe, MonadExceptOf.throw] at h
        | some pc =>
          simp only [hj] at h
          cases pc <;>
            try (simp [throw, throwThe, MonadExceptOf.throw] at h)
          case blockedSend ch2 vs ks =>
            obtain ⟨hpc, hpi⟩ := pool_get_wf hts hj
            have hpb : GoValue.locSup vs ≤ s.nextAddr
                ∧ Cont.locSup ks ≤ s.nextAddr := by
              simp only [ConfigWf, Config.locSup, Nat.max_le] at hpc
              omega
            have hpk : Cont.itersNormalized s.types ks = true := by
              simpa [Config.itersNormalized] using hpi
            simp only [bind_eq_ok] at h
            obtain ⟨⟨buf, cap, closed⟩, hcell, h⟩ := h
            have hbufb := chanCell_locSup hcell
            cases hhd : buf[0]? with
            | none =>
              simp only [hhd, bind_eq_ok, pure_eq_ok, Except.ok.injEq,
                Prod.mk.injEq] at h
              obtain ⟨⟨cr, s₂⟩, hdel, hts', hs'⟩ := h
              subst hts' hs'
              obtain ⟨q1, q2, q3, q4, q5⟩ := resumeRecvDelivery_wf hw hpb.1
                hb.2.1 hb.2.2.1 hb.2.2.2 hik hdel
              refine ⟨q1, q3, q4, by simp, ?_⟩
              exact pool_set2_wf q4 hts q2 q5
                (by simpa [Config.locSup] using Nat.le_trans hpb.2 q4)
                (by simpa [Config.itersNormalized] using hpk)
            | some hd =>
              have hhdb : GoValue.locSup hd ≤ s.nextAddr := by
                have := goValueListSup_mem (l := buf.toList) (v := hd)
                  (List.mem_of_getElem? (by simpa using hhd))
                omega
              simp only [hhd, bind_eq_ok] at h
              obtain ⟨s₁, hst, h⟩ := h
              obtain ⟨w1, w2, w3, w4, w5⟩ := storeLoc_pres hw hlocb
                (by rw [show GoValue.locSup
                      (.chanData ((buf.eraseIdx! 0).push vs) cap closed)
                      = goValueListSup ((buf.eraseIdx! 0).push vs).toList from rfl,
                    goValueListSup_push]
                    refine Nat.max_le.mpr ⟨Nat.le_trans goValueListSup_eraseIdx!
                      (by omega), hpb.1⟩) hst
              simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq,
                Prod.mk.injEq] at h
              obtain ⟨⟨cr, s₂⟩, hdel, hts', hs'⟩ := h
              subst hts' hs'
              obtain ⟨q1, q2, q3, q4, q5⟩ := resumeRecvDelivery_wf w1 (by omega)
                (by omega) (by omega) (by omega) hik hdel
              have hmono : s.nextAddr ≤ s₂.nextAddr := Nat.le_trans w2 q4
              refine ⟨q1, q3.trans w4, hmono, by simp, ?_⟩
              exact pool_set2_wf hmono hts q2 q5
                (by simpa [Config.locSup] using Nat.le_trans hpb.2 hmono)
                (by simpa [Config.itersNormalized] using hpk)
    case selectWaiter j ci =>
      cases ch
      case none => simp [applyPairing, throw, throwThe, MonadExceptOf.throw] at h
      case some loc =>
        have hlocb : Loc.locSup loc ≤ s.nextAddr := by
          simpa [optLocSup] using hb.1
        simp only [applyPairing] at h
        cases hj : threads[j]? with
        | none => simp [hj, throw, throwThe, MonadExceptOf.throw] at h
        | some pc =>
          simp only [hj] at h
          cases pc <;>
            try (simp [throw, throwThe, MonadExceptOf.throw] at h)
          case blockedSelect evs envs ks =>
            obtain ⟨hpc, hpi⟩ := pool_get_wf hts hj
            have hpb : evClausesSup evs ≤ s.nextAddr
                ∧ LocalEnv.locSup envs ≤ s.nextAddr
                ∧ Cont.locSup ks ≤ s.nextAddr := by
              simp only [ConfigWf, Config.locSup, Nat.max_le] at hpc
              omega
            have hpk : Cont.itersNormalized s.types ks = true := by
              simpa [Config.itersNormalized] using hpi
            cases hcl : evs[ci]? with
            | none => simp [hcl, throw, throwThe, MonadExceptOf.throw] at h
            | some cl =>
              simp only [hcl] at h
              cases cl with
              | recvEv chv2 targets2 elem2 body2 =>
                  simp [throw, throwThe, MonadExceptOf.throw] at h
              | sendEv chv2 vv2 selem2 body2 =>
                have hclb : evClauseSup (.sendEv chv2 vv2 selem2 body2)
                    ≤ s.nextAddr := by
                  have hmem : (EvClause.sendEv chv2 vv2 selem2 body2) ∈ evs :=
                    List.mem_of_getElem? hcl
                  exact Nat.le_trans (evClausesSup_mem hmem) hpb.1
                simp only [evClauseSup, Nat.max_le] at hclb
                simp only [bind_eq_ok] at h
                obtain ⟨v', hv', h⟩ := h
                have hv'b : GoValue.locSup v' ≤ s.nextAddr := by
                  have := normalizeValueForTy_locSup hv'
                  omega
                obtain ⟨⟨buf, cap, closed⟩, hcell, h⟩ := h
                have hbufb := chanCell_locSup hcell
                cases hhd : buf[0]? with
                | none =>
                  simp only [hhd, bind_eq_ok, pure_eq_ok, Except.ok.injEq,
                    Prod.mk.injEq] at h
                  obtain ⟨⟨cr, s₂⟩, hdel, hts', hs'⟩ := h
                  subst hts' hs'
                  obtain ⟨q1, q2, q3, q4, q5⟩ := resumeRecvDelivery_wf hw hv'b
                    hb.2.1 hb.2.2.1 hb.2.2.2 hik hdel
                  refine ⟨q1, q3, q4, by simp, ?_⟩
                  refine pool_set2_wf q4 hts q2 q5 ?_ ?_
                  · simp only [Config.locSup, Nat.max_le]
                    omega
                  · simpa [Config.itersNormalized] using hpk
                | some hd =>
                  have hhdb : GoValue.locSup hd ≤ s.nextAddr := by
                    have := goValueListSup_mem (l := buf.toList) (v := hd)
                      (List.mem_of_getElem? (by simpa using hhd))
                    omega
                  simp only [hhd, bind_eq_ok] at h
                  obtain ⟨s₁, hst, h⟩ := h
                  obtain ⟨w1, w2, w3, w4, w5⟩ := storeLoc_pres hw hlocb
                    (by rw [show GoValue.locSup
                          (.chanData ((buf.eraseIdx! 0).push v') cap closed)
                          = goValueListSup
                              ((buf.eraseIdx! 0).push v').toList from rfl,
                        goValueListSup_push]
                        refine Nat.max_le.mpr
                          ⟨Nat.le_trans goValueListSup_eraseIdx! (by omega),
                            hv'b⟩) hst
                  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq,
                    Prod.mk.injEq] at h
                  obtain ⟨⟨cr, s₂⟩, hdel, hts', hs'⟩ := h
                  subst hts' hs'
                  obtain ⟨q1, q2, q3, q4, q5⟩ := resumeRecvDelivery_wf w1
                    (by omega) (by omega) (by omega) (by omega) hik hdel
                  have hmono : s.nextAddr ≤ s₂.nextAddr := Nat.le_trans w2 q4
                  refine ⟨q1, q3.trans w4, hmono, by simp, ?_⟩
                  refine pool_set2_wf hmono hts q2 q5 ?_ ?_
                  · simp only [Config.locSup, Nat.max_le]
                    omega
                  · simpa [Config.itersNormalized] using hpk
  case blockedSelect evs env k =>
    have hb : evClausesSup evs ≤ s.nextAddr ∧ LocalEnv.locSup env ≤ s.nextAddr
        ∧ Cont.locSup k ≤ s.nextAddr := by
      simp only [ConfigWf, Config.locSup, Nat.max_le] at hbc
      omega
    have hik : Cont.itersNormalized s.types k = true := by
      simpa [Config.itersNormalized] using hibc
    simp only [applyPairing] at h
    cases hcl : evs[cn]? with
    | none => simp [hcl, throw, throwThe, MonadExceptOf.throw] at h
    | some cl =>
      simp only [hcl] at h
      cases cl with
      | recvEv chv targetsc elemc body =>
        have hclb : evClauseSup (.recvEv chv targetsc elemc body)
            ≤ s.nextAddr := by
          have hmem : (EvClause.recvEv chv targetsc elemc body) ∈ evs :=
            List.mem_of_getElem? hcl
          exact Nat.le_trans (evClausesSup_mem hmem) hb.1
        simp only [evClauseSup, Nat.max_le] at hclb
        cases ct
        case selectWaiter j2 ci2 =>
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case opWaiter j =>
          cases hj : threads[j]? with
          | none => simp [hj, throw, throwThe, MonadExceptOf.throw] at h
          | some pc =>
            simp only [hj] at h
            cases pc <;>
              try (simp [throw, throwThe, MonadExceptOf.throw] at h)
            case blockedSend ch2 vs ks =>
              obtain ⟨hpc, hpi⟩ := pool_get_wf hts hj
              have hpb : GoValue.locSup vs ≤ s.nextAddr
                  ∧ Cont.locSup ks ≤ s.nextAddr := by
                simp only [ConfigWf, Config.locSup, Nat.max_le] at hpc
                omega
              have hpk : Cont.itersNormalized s.types ks = true := by
                simpa [Config.itersNormalized] using hpi
              cases hloc : chanValueLoc chv with
              | none => simp [hloc, throw, throwThe, MonadExceptOf.throw] at h
              | some loc =>
                have hlocb : Loc.locSup loc ≤ s.nextAddr :=
                  Nat.le_trans (chanValueLoc_locSup hloc) (by omega)
                simp only [hloc, bind_eq_ok] at h
                obtain ⟨⟨buf, cap, closed⟩, hcell, h⟩ := h
                have hbufb := chanCell_locSup hcell
                cases hhd : buf[0]? with
                | none =>
                  simp only [hhd, bind_eq_ok, pure_eq_ok, Except.ok.injEq,
                    Prod.mk.injEq] at h
                  obtain ⟨⟨ci', s₂⟩, hdel, hts', hs'⟩ := h
                  subst hts' hs'
                  obtain ⟨q1, q2, q3, q4, q5⟩ := selectRecvDelivery_wf hw hpb.1
                    (by omega) (by omega) hb.2.1 hb.2.2 hik hdel
                  refine ⟨q1, q3, q4, by simp, ?_⟩
                  exact pool_set2_wf q4 hts q2 q5
                    (by simpa [Config.locSup] using Nat.le_trans hpb.2 q4)
                    (by simpa [Config.itersNormalized] using hpk)
                | some hd =>
                  have hhdb : GoValue.locSup hd ≤ s.nextAddr := by
                    have := goValueListSup_mem (l := buf.toList) (v := hd)
                      (List.mem_of_getElem? (by simpa using hhd))
                    omega
                  simp only [hhd, bind_eq_ok] at h
                  obtain ⟨s₁, hst, h⟩ := h
                  obtain ⟨w1, w2, w3, w4, w5⟩ := storeLoc_pres hw hlocb
                    (by rw [show GoValue.locSup
                          (.chanData ((buf.eraseIdx! 0).push vs) cap closed)
                          = goValueListSup
                              ((buf.eraseIdx! 0).push vs).toList from rfl,
                        goValueListSup_push]
                        refine Nat.max_le.mpr
                          ⟨Nat.le_trans goValueListSup_eraseIdx! (by omega),
                            hpb.1⟩) hst
                  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq,
                    Prod.mk.injEq] at h
                  obtain ⟨⟨ci', s₂⟩, hdel, hts', hs'⟩ := h
                  subst hts' hs'
                  obtain ⟨q1, q2, q3, q4, q5⟩ := selectRecvDelivery_wf w1
                    (by omega) (by omega) (by omega) (by omega) (by omega) hik
                    hdel
                  have hmono : s.nextAddr ≤ s₂.nextAddr := Nat.le_trans w2 q4
                  refine ⟨q1, q3.trans w4, hmono, by simp, ?_⟩
                  exact pool_set2_wf hmono hts q2 q5
                    (by simpa [Config.locSup] using Nat.le_trans hpb.2 hmono)
                    (by simpa [Config.itersNormalized] using hpk)
      | sendEv chv vv selem body =>
        have hclb : evClauseSup (.sendEv chv vv selem body) ≤ s.nextAddr := by
          have hmem : (EvClause.sendEv chv vv selem body) ∈ evs :=
            List.mem_of_getElem? hcl
          exact Nat.le_trans (evClausesSup_mem hmem) hb.1
        simp only [evClauseSup, Nat.max_le] at hclb
        cases ct
        case selectWaiter j2 ci2 =>
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case opWaiter j =>
          cases hj : threads[j]? with
          | none => simp [hj, throw, throwThe, MonadExceptOf.throw] at h
          | some pc =>
            simp only [hj] at h
            cases pc <;>
              try (simp [throw, throwThe, MonadExceptOf.throw] at h)
            case blockedRecv ch2 targetsr elemr envr kr =>
              obtain ⟨hpc, hpi⟩ := pool_get_wf hts hj
              have hpb : assigneeListSup targetsr ≤ s.nextAddr
                  ∧ LocalEnv.locSup envr ≤ s.nextAddr
                  ∧ Cont.locSup kr ≤ s.nextAddr := by
                simp only [ConfigWf, Config.locSup, Nat.max_le] at hpc
                omega
              have hpk : Cont.itersNormalized s.types kr = true := by
                simpa [Config.itersNormalized] using hpi
              cases hloc : chanValueLoc chv with
              | none => simp [hloc, throw, throwThe, MonadExceptOf.throw] at h
              | some loc =>
                simp only [hloc, bind_eq_ok] at h
                obtain ⟨⟨buf, cap, closed⟩, hcell, h⟩ := h
                split at h
                · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq,
                    Prod.mk.injEq] at h
                  obtain ⟨v', hv', ⟨cr, s₂⟩, hdel, hts', hs'⟩ := h
                  subst hts' hs'
                  have hv'b : GoValue.locSup v' ≤ s.nextAddr := by
                    have := normalizeValueForTy_locSup hv'
                    omega
                  obtain ⟨q1, q2, q3, q4, q5⟩ := resumeRecvDelivery_wf hw hv'b
                    hpb.1 hpb.2.1 hpb.2.2 hpk hdel
                  refine ⟨q1, q3, q4, by simp, ?_⟩
                  refine pool_set2_wf q4 hts ?_ ?_ q2 q5
                  · simp only [Config.locSup, Nat.max_le]
                    omega
                  · simpa [Config.itersNormalized] using hik
                · simp [throw, throwThe, MonadExceptOf.throw] at h
  all_goals simp [applyPairing, throw, throwThe, MonadExceptOf.throw] at h


/-- Frame lemma for a single-slot pool update. -/
theorem pool_set1_wf {threads : Array Config} {i : Nat} {a : Config}
    {na na' : Nat} {types : TypeEnv}
    (hmono : na ≤ na')
    (hts : ∀ t (ht : t < threads.size), ConfigWf na threads[t]
      ∧ Config.itersNormalized types threads[t] = true)
    (ha : Config.locSup a ≤ na') (hia : Config.itersNormalized types a = true) :
    ∀ t (ht : t < (threads.setIfInBounds i a).size),
      ConfigWf na' (threads.setIfInBounds i a)[t]
        ∧ Config.itersNormalized types (threads.setIfInBounds i a)[t] = true := by
  intro t ht
  have ht' : t < threads.size := by simpa using ht
  simp only [Array.getElem_setIfInBounds, Array.size_setIfInBounds, ht']
  split
  · exact ⟨ha, hia⟩
  · exact ⟨Nat.le_trans (hts t ht').1 hmono, (hts t ht').2⟩

/-- Frame lemma for the spawn's pool update: one slot replaced, one
child appended. -/
theorem pool_set_push_wf {threads : Array Config} {i : Nat} {a b : Config}
    {na na' : Nat} {types : TypeEnv}
    (hmono : na ≤ na')
    (hts : ∀ t (ht : t < threads.size), ConfigWf na threads[t]
      ∧ Config.itersNormalized types threads[t] = true)
    (ha : Config.locSup a ≤ na') (hia : Config.itersNormalized types a = true)
    (hb : Config.locSup b ≤ na') (hib : Config.itersNormalized types b = true) :
    ∀ t (ht : t < ((threads.setIfInBounds i a).push b).size),
      ConfigWf na' ((threads.setIfInBounds i a).push b)[t]
        ∧ Config.itersNormalized types
            ((threads.setIfInBounds i a).push b)[t] = true := by
  intro t ht
  have hsz : t < (threads.setIfInBounds i a).size + 1 := by simpa using ht
  rw [Array.getElem_push]
  split
  · rename_i hlt
    exact pool_set1_wf hmono hts ha hia t hlt
  · exact ⟨hb, hib⟩

/-- Membership in the runnable list bounds the index. -/
theorem runnableIdxs_lt {s : ExecState} {ts : Array Config} {i : Nat}
    (h : i ∈ runnableIdxs s ts) : i < ts.size := by
  unfold runnableIdxs at h
  exact List.mem_range.mp (List.mem_filter.mp h).1

set_option maxHeartbeats 1600000 in
/-- `stepThread` preservation: one goroutine-step of the pool keeps the
shared state wf (allocator monotone, types unchanged), never shrinks
the pool, and leaves every slot bounded and iteration-typed. -/
theorem stepThread_wf {s : ExecState} {threads : Array Config} {i : Nat}
    {ch ch' : Choices} {ts' : Array Config} {s' : ExecState}
    (hw : StateWf s)
    (hts : ∀ t (ht : t < threads.size), ConfigWf s.nextAddr threads[t]
      ∧ Config.itersNormalized s.types threads[t] = true)
    (h : stepThread s threads i ch = .ok (ts', s', ch')) :
    StateWf s' ∧ s'.types = s.types ∧ s.nextAddr ≤ s'.nextAddr
      ∧ threads.size ≤ ts'.size
      ∧ ∀ t (ht : t < ts'.size), ConfigWf s'.nextAddr ts'[t]
          ∧ Config.itersNormalized s.types ts'[t] = true := by
  unfold stepThread at h
  cases hti : threads[i]? with
  | none => rw [hti] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some c =>
    rw [hti] at h
    obtain ⟨hc, hic⟩ := pool_get_wf hts hti
    by_cases hblc : isBlockedConfig c = true
    · simp only [hblc, reduceIte, bind_eq_ok] at h
      obtain ⟨⟨c₂, s₂⟩, hres, h⟩ := h
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨q1, q2, q3, q4, q5⟩ := resumeThread_wf hw hc hic hres
      exact ⟨q1, q3, q4, by simp, pool_set1_wf q4 hts q2 q5⟩
    · simp only [Bool.not_eq_true] at hblc
      simp only [hblc, Bool.false_eq_true, reduceIte] at h
      cases hsc : spawnedCont c with
      | some k =>
        rw [hsc] at h
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain rfl := spawnedCont_shape hsc
        refine ⟨hw, rfl, Nat.le_refl _, by simp, ?_⟩
        refine pool_set1_wf (Nat.le_refl _) hts ?_ ?_
        · simpa [ConfigWf, Config.locSup] using hc
        · simpa [Config.itersNormalized] using hic
      | none =>
        rw [hsc] at h
        cases hsp : spawnPlan c with
        | some p =>
          obtain ⟨cv, args, k⟩ := p
          rw [hsp] at h
          simp only [bind_eq_ok] at h
          obtain ⟨⟨parent', child, s₂⟩, hspawn, h⟩ := h
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨hcvb, hargsb, hkb⟩ := spawnPlan_locSup hsp
          obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := spawnStep_wf hw
            (Nat.le_trans hcvb hc) (Nat.le_trans hargsb hc)
            (Nat.le_trans hkb hc) (spawnPlan_iters hsp hic) hspawn
          refine ⟨q1, q4, q5, by simp, ?_⟩
          exact pool_set_push_wf q5 hts q2 q6 q3 q7
        | none =>
          rw [hsp] at h
          simp only [bind_eq_ok] at h
          obtain ⟨⟨plan, ch₁⟩, hplan, h⟩ := h
          cases harr : arrivalCases s threads i c with
          | error e =>
            rw [arrivalPlan_of_error (ch := ch) harr] at hplan
            cases hplan
          | ok r =>
            cases r with
            | cellPath =>
              rw [arrivalPlan_of_cellPath (ch := ch) harr] at hplan
              simp only [Except.ok.injEq, Prod.mk.injEq] at hplan
              obtain ⟨hp1, hp2⟩ := hplan
              subst hp1
              subst hp2
              dsimp only at h
              simp only [bind_eq_ok] at h
              obtain ⟨⟨c₂, s₂, ch₂⟩, hstep, h⟩ := h
              simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              have hstepr := stepFn_sound hstep
              obtain ⟨q1, q2, q3, q4⟩ := step_preserves_wf_loc hstepr hw hc
              have q5 := step_preserves_iters hstepr hic
              exact ⟨q1, q3, q4, by simp, pool_set1_wf q4 hts q2 q5⟩
            | single bc cands =>
              rw [arrivalPlan_of_single (ch := ch) harr] at hplan
              simp only [Except.ok.injEq, Prod.mk.injEq] at hplan
              obtain ⟨hp1, hp2⟩ := hplan
              subst hp1
              subst hp2
              obtain ⟨hbcb, hbci⟩ := arrivalCases_single_wf hw hc hic harr
              cases cands with
              | nil => simp [throw, throwThe, MonadExceptOf.throw] at h
              | cons cand rest =>
                cases rest with
                | nil =>
                  dsimp only at h
                  simp only [bind_eq_ok] at h
                  obtain ⟨⟨ts₂, s₂⟩, hpair, h⟩ := h
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  obtain ⟨q1, q2, q3, q4, q5⟩ := applyPairing_wf hw hts hbcb
                    hbci hpair
                  exact ⟨q1, q2, q3, by omega, q5⟩
                | cons cand2 rest2 =>
                  dsimp only at h
                  rcases hcons : Choices.consume ch
                      (cand :: cand2 :: rest2).length with ⟨idx, ch₂⟩
                  rw [hcons] at h
                  dsimp only at h
                  cases hget : (cand :: cand2 :: rest2)[idx]? with
                  | none =>
                    rw [hget] at h
                    simp [throw, throwThe, MonadExceptOf.throw] at h
                  | some cand3 =>
                    rw [hget] at h
                    simp only [bind_eq_ok] at h
                    obtain ⟨⟨ts₂, s₂⟩, hpair, h⟩ := h
                    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    obtain ⟨q1, q2, q3, q4, q5⟩ := applyPairing_wf hw hts hbcb
                      hbci hpair
                    exact ⟨q1, q2, q3, by omega, q5⟩
            | multi os =>
              rcases hcons : Choices.consume ch os.length with ⟨sel, chs⟩
              rw [arrivalPlan_of_multi (ch := ch) harr hcons] at hplan
              cases hget : os[sel]? with
              | none =>
                rw [hget] at hplan
                cases hplan
              | some o =>
                rw [hget] at hplan
                simp only [Except.ok.injEq, Prod.mk.injEq] at hplan
                obtain ⟨hp1, hp2⟩ := hplan
                subst hp1
                subst hp2
                obtain ⟨hpairb, hcommitb⟩ := arrivalCases_multi_wf hw hc hic
                  harr hget
                cases o with
                | pair bc cands =>
                  obtain ⟨hbcb, hbci⟩ := hpairb rfl
                  cases cands with
                  | nil => simp [throw, throwThe, MonadExceptOf.throw] at h
                  | cons cand rest =>
                    cases rest with
                    | nil =>
                      dsimp only at h
                      simp only [bind_eq_ok] at h
                      obtain ⟨⟨ts₂, s₂⟩, hpair, h⟩ := h
                      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl, rfl⟩ := h
                      obtain ⟨q1, q2, q3, q4, q5⟩ := applyPairing_wf hw hts
                        hbcb hbci hpair
                      exact ⟨q1, q2, q3, by omega, q5⟩
                    | cons cand2 rest2 =>
                      dsimp only at h
                      rcases hcons2 : Choices.consume chs
                          (cand :: cand2 :: rest2).length with ⟨idx, ch₂⟩
                      rw [hcons2] at h
                      dsimp only at h
                      cases hget2 : (cand :: cand2 :: rest2)[idx]? with
                      | none =>
                        rw [hget2] at h
                        simp [throw, throwThe, MonadExceptOf.throw] at h
                      | some cand3 =>
                        rw [hget2] at h
                        simp only [bind_eq_ok] at h
                        obtain ⟨⟨ts₂, s₂⟩, hpair, h⟩ := h
                        simp only [pure_eq_ok, Except.ok.injEq,
                          Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl, rfl⟩ := h
                        obtain ⟨q1, q2, q3, q4, q5⟩ := applyPairing_wf hw hts
                          hbcb hbci hpair
                        exact ⟨q1, q2, q3, by omega, q5⟩
                | commit cl env k =>
                  obtain ⟨hclb, henvb, hkb, hki⟩ := hcommitb rfl
                  dsimp only at h
                  simp only [bind_eq_ok] at h
                  obtain ⟨⟨c₂, s₂⟩, hcom, h⟩ := h
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  obtain ⟨q1, q2, q3, q4⟩ := commitClause_wf hw hclb henvb
                    hkb hcom
                  have q5 := commitClause_itersNormalized hcom hki
                  exact ⟨q1, q3, q4, by simp, pool_set1_wf q4 hts q2 q5⟩

/-- **`MultiWf` preservation** — the executable pool step keeps the
thread-indexed invariant. This is the slice-2 scaffold's owed theorem
(`Multi.lean`, `MultiWf`'s docstring): the invariant carrier is now a
PRESERVED invariant, not a definition awaiting one. -/
theorem stepMulti_wf {m m' : MultiConfig} {ch ch' : Choices}
    (hwf : MultiWf m) (h : stepMulti m ch = .ok (m', ch')) : MultiWf m' := by
  obtain ⟨hs, hcur, hth⟩ := hwf
  have hstep : ∀ i, i < m.threads.size →
      ∀ {ch₀ : Choices}, stepThreadInto m i ch₀ = .ok (m', ch') → MultiWf m' := by
    intro i hi ch₀ hinto
    unfold stepThreadInto at hinto
    simp only [bind_eq_ok] at hinto
    obtain ⟨⟨ts, s₂, ch₂⟩, hst, hinto⟩ := hinto
    simp only [pure_eq_ok, Except.ok.injEq] at hinto
    obtain ⟨rfl, rfl⟩ := hinto
    obtain ⟨q1, q2, q3, q4, q5⟩ := stepThread_wf hs hth hst
    refine ⟨q1, Nat.lt_of_lt_of_le hi q4, ?_⟩
    intro t ht
    refine ⟨(q5 t ht).1, ?_⟩
    rw [q2]
    exact (q5 t ht).2
  unfold stepMulti at h
  cases hti : m.threads[m.cur]? with
  | none => rw [hti] at h; cases h
  | some c =>
    rw [hti] at h
    by_cases hb : c.atBoundary = true
    · simp only [hb, reduceIte] at h
      cases hrs : runnableIdxs m.shared m.threads with
      | nil => rw [hrs] at h; cases h
      | cons r0 rest =>
        rw [hrs] at h
        cases rest with
        | nil =>
          refine hstep r0 (runnableIdxs_lt (s := m.shared) (ts := m.threads) ?_) h
          rw [hrs]
          exact List.mem_singleton.mpr rfl
        | cons r1 rest' =>
          dsimp only at h
          rcases hcons : ch.consume (r0 :: r1 :: rest').length with ⟨pick, ch₁⟩
          rw [hcons] at h
          cases hget : (r0 :: r1 :: rest')[pick]? with
          | none => rw [hget] at h; cases h
          | some i =>
            rw [hget] at h
            refine hstep i
              (runnableIdxs_lt (s := m.shared) (ts := m.threads) ?_) h
            rw [hrs]
            exact List.mem_of_getElem? hget
    · simp only [Bool.not_eq_true] at hb
      simp only [hb, Bool.false_eq_true, reduceIte] at h
      exact hstep m.cur hcur h

end GoLean.GoCore.Machine
