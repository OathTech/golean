import GoLean.GoCore.MultiSound

/-!
# MultiWf preservation (channels arc slice 5)

The slice-2 scaffold's owed preservation theorem, by the slice-3 build
log's recorded route: the sequential `*_wf` conclusions carry the
step-level `nextAddr` monotonicity conjunct, and the pool assembly here
frames the foreign threads through it.
-/

namespace GoLean.GoCore.Machine

-- B7 (2026-09-17): the program context is an IMPLICIT parameter of every
-- theorem here (lemma applications stay as they were).
variable {ctx : ProgramCtx}

-- The unused-simp-arg linter misfires on the shared multi-branch simp
-- sets (an argument unused in one branch is load-bearing in another) —
-- the `MultiSound.lean`/`MachineSound.lean` precedent.
set_option linter.unusedSimpArgs false

/-! ## MultiWf ctx preservation — the slice-2 scaffold DISCHARGED (slice 5)

The slice-3 build log's recorded route, executed: the sequential `*_wf`
family's conclusions were extended with the step-level
`σ.nextAddr ≤ σ'.nextAddr` conjunct (`applyChanOp_wf`,
`applySelect_wf`, `step_preserves_wf_loc` — `commitClause_wf`,
`enterRecvTargets_wf` and the `StmtOpPres` family already exposed it),
and the pool assembly below frames the FOREIGN threads through it: an
untouched goroutine's `ConfigWf` transports along allocator
monotonicity. `stepMulti_wf` is the preservation theorem the slice-2
scaffold owed. B7 fix round (2026-09-17, [USER] «We should delete the
vacuous conjunct right? that's just a strict improvement», relayed):
`ThreadWf`/`MultiWf` lost their constantly-true `itersNormalized`
conjunct (B7 had made `MultiWf m` context-free) and every `*_wf` lemma below
lost its `Config.itersNormalized … = true` hypotheses/conjuncts
(restatements, none weakened; `spawnPlan_iters` retired as inert). C1 S1
(2026-09-18) made `MultiWf ctx m` read the context AGAIN: `StateWf ctx
m.shared` now carries the `HeapNormal ctx` conjunct, which the type table
decides (a restatement, flagged in the C1 handoff §5; nothing weakened;
the stale «context-free» wording corrected at the C1 audit fix round, F6). -/

-- `spawnedCont_shape` retired with the marker unification (stage C);
-- `opDoneInner_shape` retired with the marker itself (C5).

/-! ## `ThreadWf` (C5: the per-goroutine invariant over `Thread`) -/

theorem ThreadWf.running {na : Nat} {c : Config} {b : Option ChoiceSite}
    (hc : Config.locSup c ≤ na) : ThreadWf na (.running c b) :=
  hc

theorem ThreadWf.aborted {na : Nat} {msg : String} :
    ThreadWf na (.aborted msg) := trivial

theorem ThreadWf.mono {na na' : Nat} {t : Thread}
    (hmono : na ≤ na') (h : ThreadWf na t) : ThreadWf na' t := by
  cases t with
  | aborted msg => trivial
  | running c b => exact Nat.le_trans h hmono

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

/-- `spawnStep` preservation: wf state out, both successor
configurations bounded, allocator monotone. -/
theorem spawnStep_wf {s : Store} {cv : GoValue} {args : List GoValue}
    {k : Cont} {ch : Choices} {p child : Config} {s' : Store} {ch' : Choices}
    {ps : List PickRecord} {tr : AccessTrace}
    (hw : StateWf ctx s) (hcv : GoValue.locSup cv ≤ s.nextAddr)
    (hargs : goValueListSup args ≤ s.nextAddr)
    (hk : Cont.locSup k ≤ s.nextAddr)
    (h : spawnStep ctx s cv args k ch = .ok (p, child, s', ch', ps, tr)) :
    StateWf ctx s' ∧ Config.locSup p ≤ s'.nextAddr
      ∧ Config.locSup child ≤ s'.nextAddr ∧ s.nextAddr ≤ s'.nextAddr := by
  unfold spawnStep at h
  split at h
  · rename_i fid captured
    -- B2 + C1 S3: the V entry funnel classifies; the commit runs on the owned
    -- store (`runCommit`), the composed entry is what `enterFrame_wf` reads.
    simp only [bind_eq_ok] at h
    obtain ⟨⟨r, ch₁, ps₁⟩, hpick, h⟩ := h
    have hcap : goValueListSup captured ≤ s.nextAddr := by
      simpa [GoValue.locSup] using hcv
    rcases enterFramePickV_cases hpick with ⟨c, rfl, hplan, rfl, rfl⟩ | ⟨msg, rfl, hplan, rfl, rfl⟩
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨w, hrun, h⟩ := h
      obtain ⟨func, frameEnv, resultLocs, s₂, tr₂⟩ := w
      try dsimp only at h
      try simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      have henter : enterFrame ctx s fid (captured ++ args)
          = .ok (func, frameEnv, resultLocs, s₂, tr₂) := by
        simp [enterFrame, hplan, Bind.bind, Except.bind, runCommit_eq_ok.mp hrun]
      obtain ⟨w1, w2, w6, w7, w8⟩ := enterFrame_wf hw
        (by rw [goValueListSup_append]; omega) henter
      refine ⟨w1, ?_, ?_, w2⟩
      · simpa [Config.locSup] using Nat.le_trans hk w2
      · simp only [Config.locSup, Cont.locSup, locListSup, deferListSup,
          targetPlansSup, LocalEnv.locSup, Nat.max_le]
        omega
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      refine ⟨hw, ?_, ?_, Nat.le_refl _⟩
      · simpa [Config.locSup] using hk
      · simp [Config.locSup, panicChainSup, panicEntry_locSup, Cont.locSup]
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

/-- `resumeRecvDelivery` preservation (bounds). -/
theorem resumeRecvDelivery_wf {s : Store} {v : GoValue} {ok : Bool}
    {targets : List Assignee} {env : LocalEnv} {k : Cont}
    {c' : Config} {s' : Store}
    (hw : StateWf ctx s) (hv : GoValue.locSup v ≤ s.nextAddr)
    (ht : assigneeListSup targets ≤ s.nextAddr)
    (henv : LocalEnv.locSup env ≤ s.nextAddr)
    (hk : Cont.locSup k ≤ s.nextAddr)
    (h : resumeRecvDelivery s v ok targets env k = .ok (c', s')) :
    StateWf ctx s' ∧ Config.locSup c' ≤ s'.nextAddr
      ∧ s.nextAddr ≤ s'.nextAddr := by
  unfold resumeRecvDelivery at h
  split at h
  · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hw, by simpa [Config.locSup] using hk, Nat.le_refl _⟩
  · rename_i t ts
    exact enterRecvTargets_wf hw ht
      (Nat.le_trans (recvStores_locSup ((t :: ts).length)) hv)
      (by simp [Stmt.locSup, stmtListSup]) henv hk h

/-- `selectRecvDelivery` preservation (bounds). -/
theorem selectRecvDelivery_wf {s : Store} {v : GoValue} {ok : Bool}
    {targets : List Assignee} {body : Stmt} {env : LocalEnv} {k : Cont}
    {c' : Config} {s' : Store}
    (hw : StateWf ctx s) (hv : GoValue.locSup v ≤ s.nextAddr)
    (ht : assigneeListSup targets ≤ s.nextAddr)
    (hb : Stmt.locSup body ≤ s.nextAddr)
    (henv : LocalEnv.locSup env ≤ s.nextAddr)
    (hk : Cont.locSup k ≤ s.nextAddr)
    (h : selectRecvDelivery s v ok targets body env k = .ok (c', s')) :
    StateWf ctx s' ∧ Config.locSup c' ≤ s'.nextAddr
      ∧ s.nextAddr ≤ s'.nextAddr := by
  unfold selectRecvDelivery at h
  split at h
  · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨hw, ?_, Nat.le_refl _⟩
    simp only [Config.locSup, Nat.max_le]
    omega
  · rename_i t ts
    exact enterRecvTargets_wf hw ht
      (Nat.le_trans (recvStores_locSup ((t :: ts).length)) hv) hb henv hk h

/-- `resumeThread` preservation: the wake of a parked goroutine keeps
the state wf (allocator monotone) and produces a bounded
configuration. -/
theorem resumeThread_wf {s : Store} {c c' : Config} {s' : Store} {tr : AccessTrace}
    (hw : StateWf ctx s) (hc : ConfigWf s.nextAddr c)
    (h : resumeThread ctx s c = .ok (c', s', tr)) :
    StateWf ctx s' ∧ Config.locSup c' ≤ s'.nextAddr
      ∧ s.nextAddr ≤ s'.nextAddr := by
  have hheap := hw.heap_le
  unfold resumeThread at h
  split at h
  · -- blockedSend
    rename_i loc v k
    have hb : Loc.locSup loc ≤ s.nextAddr ∧ GoValue.locSup v ≤ s.nextAddr
        ∧ Cont.locSup k ≤ s.nextAddr := by
      simp only [ConfigWf, Config.locSup, optLocSup, Nat.max_le] at hc
      omega
    simp only [bind_eq_ok] at h
    obtain ⟨⟨buf, capacity, closed⟩, hcell, h⟩ := h
    have hbufb := chanCell_locSup hcell
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨hw, ?_, Nat.le_refl _⟩
      simp only [Config.locSup, panicChainSup, runtimeErrorValue_locSup, panicEntry_locSup,
        Nat.max_le]
      omega
    · split at h
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨s₂, hst, rfl, rfl, rfl⟩ := h
        obtain ⟨w1, w2⟩ := storeChanPayload_pres hw hb.1
          (by rw [goValueListSup_push]
              omega) hst
        refine ⟨w1, ?_, w2⟩
        simp only [Config.locSup]
        omega
      · simp [throw, throwThe, MonadExceptOf.throw] at h
  · -- blockedRecv
    rename_i loc targets elem env k
    have hb : Loc.locSup loc ≤ s.nextAddr ∧ assigneeListSup targets ≤ s.nextAddr
        ∧ LocalEnv.locSup env ≤ s.nextAddr ∧ Cont.locSup k ≤ s.nextAddr := by
      simp only [ConfigWf, Config.locSup, optLocSup, Nat.max_le] at hc
      omega
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
      obtain ⟨w1, w2⟩ := storeChanPayload_pres hw hb.1
        (by
            exact Nat.le_trans goValueListSup_eraseIdx! (by omega)) hst
      obtain ⟨⟨c₀, σ₀⟩, hent, h⟩ := h
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨q1, q2, q4⟩ := resumeRecvDelivery_wf w1 (by omega)
        (by omega) (by omega) (by omega) hent
      exact ⟨q1, by simpa using q2, Nat.le_trans w2 q4⟩
    · split at h
      · -- closed: zero value
        simp only [bind_eq_ok] at h
        obtain ⟨z, hz, h⟩ := h
        have hzb : GoValue.locSup z ≤ s.nextAddr := by
          rw [defaultValue_locSup hz]; omega
        obtain ⟨⟨c₀, σ₀⟩, hent, h⟩ := h
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨q1, q2, q4⟩ := resumeRecvDelivery_wf hw hzb hb.2.1
          hb.2.2.1 hb.2.2.2 hent
        exact ⟨q1, by simpa using q2, q4⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at h
  · -- blockedSelect
    rename_i evs env k
    have hb : evClausesSup evs ≤ s.nextAddr ∧ LocalEnv.locSup env ≤ s.nextAddr
        ∧ Cont.locSup k ≤ s.nextAddr := by
      simp only [ConfigWf, Config.locSup, Nat.max_le] at hc
      omega
    simp only [bind_eq_ok] at h
    obtain ⟨rc, hrc, h⟩ := h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · rename_i cl rest
      have hclb : evClauseSup cl ≤ s.nextAddr := by
        have hmem : cl ∈ evs := readyClauses_subset hrc cl (List.mem_cons_self ..)
        exact Nat.le_trans (evClausesSup_mem hmem) hb.1
      exact commitClause_wf hw hclb hb.2.1 hb.2.2 h
  · -- blockedSync (spec-parity slice 2): every resume is a loc-free
    -- store then `.next k`, or the onceBegin delivery entry.
    rename_i op loc env k
    have hb : syncOpSup op ≤ s.nextAddr ∧ Loc.locSup loc ≤ s.nextAddr
        ∧ LocalEnv.locSup env ≤ s.nextAddr ∧ Cont.locSup k ≤ s.nextAddr := by
      simp only [ConfigWf, Config.locSup, Nat.max_le] at hc
      omega
    simp only [bind_eq_ok] at h
    obtain ⟨p, hcell, h⟩ := h
    split at h
    all_goals try (simp [stuck, throw, throwThe, MonadExceptOf.throw] at h; done)
    all_goals split at h
    all_goals try (simp [throw, throwThe, MonadExceptOf.throw] at h; done)
    all_goals
      first
      | (simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
         obtain ⟨s₂, hst, rfl, rfl, rfl⟩ := h
         obtain ⟨w1, w2⟩ := storeLoc_pres hw hb.2.1
           (by simp [syncData_locSup]) hst
         refine ⟨w1, ?_, w2⟩
         simp only [Config.locSup]
         omega)
      | (simp only [bind_eq_ok] at h
         obtain ⟨⟨c₀, σ₀⟩, hent, h⟩ := h
         simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl, rfl⟩ := h
         obtain ⟨q1, q2, q4⟩ := enterRecvTargets_wf hw
           (by simpa [syncOpSup] using hb.1)
           (by simp [goValueListSup, GoValue.locSup])
           (by simp [Stmt.locSup, stmtListSup]) hb.2.2.1 hb.2.2.2 hent
         exact ⟨q1, by simpa using q2, q4⟩)
  · simp [throw, throwThe, MonadExceptOf.throw] at h


/-- Indexed lookup of the pool hypothesis. -/
theorem pool_get_wf {threads : Array Thread} {j : Nat} {c : Config}
    {b : Option ChoiceSite} {na : Nat}
    (hts : ∀ t (ht : t < threads.size), ThreadWf na threads[t])
    (hj : threads[j]? = some (.running c b)) :
    ConfigWf na c := by
  obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hj
  have := hts j hlt
  rw [heq] at this
  exact this

/-- Frame lemma for the two-index pool update every pairing performs:
the two touched slots carry the new bounds; every other goroutine's
`ConfigWf` transports along allocator monotonicity. -/
theorem pool_set2_wf {threads : Array Thread} {i j : Nat} {a b : Config}
    {fa fb : Option ChoiceSite} {na na' : Nat}
    (hmono : na ≤ na')
    (hts : ∀ t (ht : t < threads.size), ThreadWf na threads[t])
    (ha : Config.locSup a ≤ na') (hb : Config.locSup b ≤ na') :
    ∀ t (ht : t < ((threads.setIfInBounds i (.running a fa)).setIfInBounds j (.running b fb)).size),
      ThreadWf na' ((threads.setIfInBounds i (.running a fa)).setIfInBounds j (.running b fb))[t] := by
  intro t ht
  have ht' : t < threads.size := by simpa using ht
  simp only [Array.getElem_setIfInBounds, Array.size_setIfInBounds, ht']
  split
  · exact ThreadWf.running hb
  · split
    · exact ThreadWf.running ha
    · exact ThreadWf.mono hmono (hts t ht')

/-- The channel loc behind a chan value is bounded by the value. -/
theorem chanValueLoc_locSup {v : GoValue} {loc : Loc}
    (h : chanValueLoc v = some loc) : Loc.locSup loc ≤ GoValue.locSup v := by
  match v, h with
  | .chan cv, h =>
      simp only [chanValueLoc] at h
      simp [GoValue.locSup, h, optLocSup]

/-- The would-block shape a CHAN-OP arrival pairing carries is bounded
by the arriving operands. -/
theorem chanArrivalPlan_wf {s : Store} {threads : Array Thread} {i : Nat}
    {op : ChanStOp} {vs : List GoValue} {env : LocalEnv} {k : Cont}
    {bc : Config} {cands : List (Nat × PairTarget)}
    (_hw : StateWf ctx s) (hvs : goValueListSup vs ≤ s.nextAddr)
    (hop : chanStOpSup op ≤ s.nextAddr)
    (henv : LocalEnv.locSup env ≤ s.nextAddr)
    (hk : Cont.locSup k ≤ s.nextAddr)
    (h : chanArrivalPlan ctx s threads i op vs env k = .ok (some (bc, cands))) :
    Config.locSup bc ≤ s.nextAddr := by
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
          simp only [Config.locSup, optLocSup, Nat.max_le]
          omega
  · simp at h

/-- The `.single` analysis' would-block shape is bounded by the arriving
configuration. -/
theorem arrivalCases_single_wf {s : Store} {threads : Array Thread}
    {i : Nat} {c bc : Config} {cs : List (Nat × PairTarget)}
    (hw : StateWf ctx s) (hc : ConfigWf s.nextAddr c)
    (h : arrivalCases ctx s threads i c = .ok (.single bc cs)) :
    Config.locSup bc ≤ s.nextAddr := by
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
      exact chanArrivalPlan_wf hw hvsb hb.2.1 hb.2.2.2.1 hb.2.2.2.2 hplan
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

/-- The `.multi` analysis' SELECTED outcome is bounded by the arriving
configuration: a `.pair`'s would-block shape like the single case, a
`.commit`'s clause a member of the evaluated clause list. -/
theorem arrivalCases_multi_wf {s : Store} {threads : Array Thread}
    {i : Nat} {c : Config} {os : List ArrivalOutcome} {sel : Nat}
    {o : ArrivalOutcome}
    (_hw : StateWf ctx s) (hc : ConfigWf s.nextAddr c)
    (h : arrivalCases ctx s threads i c = .ok (.multi os))
    (hget : os[sel]? = some o) :
    (∀ {bc cs}, o = ArrivalOutcome.pair bc cs →
      Config.locSup bc ≤ s.nextAddr)
    ∧ (∀ {evs cl env k}, o = ArrivalOutcome.commit evs cl env k →
        evClauseSup cl ≤ s.nextAddr ∧ LocalEnv.locSup env ≤ s.nextAddr
          ∧ Cont.locSup k ≤ s.nextAddr) := by
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
                · intro evs' cl' env' k' heq
                  cases heq
                  have hclb : evClauseSup cl ≤ s.nextAddr := by
                    have hmem' : cl ∈ evs :=
                      List.mem_of_getElem? hcl
                    exact Nat.le_trans (evClausesSup_mem hmem') hevsb
                  exact ⟨hclb, hb.2.2.2.1, hb.2.2.2.2⟩
              · simp [throw, throwThe, MonadExceptOf.throw] at hmk
            · split at hmk
              · simp [throw, throwThe, MonadExceptOf.throw] at hmk
              · simp only [pure_eq_ok, Except.ok.injEq] at hmk
                subst hmk
                refine ⟨?_, ?_⟩
                · intro bc cs heq
                  cases heq
                  simp only [Config.locSup, Nat.max_le]
                  omega
                · intro evs' cl' env' k' heq
                  cases heq
  · simp only [pure_eq_ok, Except.ok.injEq] at h
    cases h




set_option maxHeartbeats 1600000 in
/-- `applyPairing` preservation: the arrival pairing keeps the shared
state wf (allocator monotone), preserves the pool size, and leaves
EVERY slot bounded — the two touched slots by the pairing outcome's own
bounds, the foreign threads by the monotonicity frame. -/
theorem applyPairing_wf {s : Store} {threads : Array Thread} {i : Nat}
    {bc : Config} {cand : Nat × PairTarget} {ts' : Array Thread}
    {s' : Store} {tr : AccessTrace}
    (hw : StateWf ctx s)
    (hts : ∀ t (ht : t < threads.size), ThreadWf s.nextAddr threads[t])
    (hbc : ConfigWf s.nextAddr bc)
    (h : applyPairing ctx s threads i bc cand = .ok (ts', s', tr)) :
    StateWf ctx s' ∧ s.nextAddr ≤ s'.nextAddr
      ∧ ts'.size = threads.size
      ∧ ∀ t (ht : t < ts'.size), ThreadWf s'.nextAddr ts'[t] := by
  have hheap := hw.heap_le
  obtain ⟨cn, ct⟩ := cand
  cases bc
  case blockedSend ch v k =>
    have hb : optLocSup ch ≤ s.nextAddr ∧ GoValue.locSup v ≤ s.nextAddr
        ∧ Cont.locSup k ≤ s.nextAddr := by
      simp only [ConfigWf, Config.locSup, Nat.max_le] at hbc
      omega
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
          rcases pc with ⟨pc, bp⟩ | msg
          case aborted => simp [throw, throwThe, MonadExceptOf.throw] at h
          cases pc <;>
            try (simp [throw, throwThe, MonadExceptOf.throw] at h)
          case blockedRecv ch2 targets elem2 envr kr =>
            have hpc := pool_get_wf hts hj
            have hpb : assigneeListSup targets ≤ s.nextAddr
                ∧ LocalEnv.locSup envr ≤ s.nextAddr
                ∧ Cont.locSup kr ≤ s.nextAddr := by
              simp only [ConfigWf, Config.locSup, Nat.max_le] at hpc
              omega
            simp only [bind_eq_ok] at h
            obtain ⟨⟨buf, cap, closed⟩, hcell, h⟩ := h
            split at h
            · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq,
                Prod.mk.injEq] at h
              obtain ⟨⟨cr, s₂⟩, hdel, hts', hs', -⟩ := h
              subst hts' hs'
              obtain ⟨q1, q2, q4⟩ := resumeRecvDelivery_wf hw hb.2.1
                hpb.1 hpb.2.1 hpb.2.2 hdel
              refine ⟨q1, q4, by simp, ?_⟩
              exact pool_set2_wf q4 hts
                (by simpa [Config.locSup] using Nat.le_trans hb.2.2 q4) q2
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
          rcases pc with ⟨pc, bp⟩ | msg
          case aborted => simp [throw, throwThe, MonadExceptOf.throw] at h
          cases pc <;>
            try (simp [throw, throwThe, MonadExceptOf.throw] at h)
          case blockedSelect evs envs ks =>
            have hpc := pool_get_wf hts hj
            have hpb : evClausesSup evs ≤ s.nextAddr
                ∧ LocalEnv.locSup envs ≤ s.nextAddr
                ∧ Cont.locSup ks ≤ s.nextAddr := by
              simp only [ConfigWf, Config.locSup, Nat.max_le] at hpc
              omega
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
                  obtain ⟨⟨cs', s₂⟩, hdel, hts', hs', -⟩ := h
                  subst hts' hs'
                  obtain ⟨q1, q2, q4⟩ := selectRecvDelivery_wf hw hb.2.1
                    (by omega) (by omega) hpb.2.1 hpb.2.2 hdel
                  refine ⟨q1, q4, by simp, ?_⟩
                  exact pool_set2_wf q4 hts
                    (by simpa [Config.locSup] using Nat.le_trans hb.2.2 q4) q2
                · simp [throw, throwThe, MonadExceptOf.throw] at h
  case blockedRecv ch targets elem env k =>
    have hb : optLocSup ch ≤ s.nextAddr ∧ assigneeListSup targets ≤ s.nextAddr
        ∧ LocalEnv.locSup env ≤ s.nextAddr ∧ Cont.locSup k ≤ s.nextAddr := by
      simp only [ConfigWf, Config.locSup, Nat.max_le] at hbc
      omega
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
          rcases pc with ⟨pc, bp⟩ | msg
          case aborted => simp [throw, throwThe, MonadExceptOf.throw] at h
          cases pc <;>
            try (simp [throw, throwThe, MonadExceptOf.throw] at h)
          case blockedSend ch2 vs ks =>
            have hpc := pool_get_wf hts hj
            have hpb : GoValue.locSup vs ≤ s.nextAddr
                ∧ Cont.locSup ks ≤ s.nextAddr := by
              simp only [ConfigWf, Config.locSup, Nat.max_le] at hpc
              omega
            simp only [bind_eq_ok] at h
            obtain ⟨⟨buf, cap, closed⟩, hcell, h⟩ := h
            have hbufb := chanCell_locSup hcell
            cases hhd : buf[0]? with
            | none =>
              simp only [hhd, bind_eq_ok, pure_eq_ok, Except.ok.injEq,
                Prod.mk.injEq] at h
              obtain ⟨⟨cr, s₂⟩, hdel, hts', hs', -⟩ := h
              subst hts' hs'
              obtain ⟨q1, q2, q4⟩ := resumeRecvDelivery_wf hw hpb.1
                hb.2.1 hb.2.2.1 hb.2.2.2 hdel
              refine ⟨q1, q4, by simp, ?_⟩
              exact pool_set2_wf q4 hts q2
                (by simpa [Config.locSup] using Nat.le_trans hpb.2 q4)
            | some hd =>
              have hhdb : GoValue.locSup hd ≤ s.nextAddr := by
                have := goValueListSup_mem (l := buf.toList) (v := hd)
                  (List.mem_of_getElem? (by simpa using hhd))
                omega
              simp only [hhd, bind_eq_ok] at h
              obtain ⟨s₁, hst, h⟩ := h
              obtain ⟨w1, w2⟩ := storeChanPayload_pres hw hlocb
                (by rw [goValueListSup_push]
                    refine Nat.max_le.mpr ⟨Nat.le_trans goValueListSup_eraseIdx!
                      (by omega), hpb.1⟩) hst
              simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq,
                Prod.mk.injEq] at h
              obtain ⟨⟨cr, s₂⟩, hdel, hts', hs', -⟩ := h
              subst hts' hs'
              obtain ⟨q1, q2, q4⟩ := resumeRecvDelivery_wf w1 (by omega)
                (by omega) (by omega) (by omega) hdel
              have hmono : s.nextAddr ≤ s₂.nextAddr := Nat.le_trans w2 q4
              refine ⟨q1, hmono, by simp, ?_⟩
              exact pool_set2_wf hmono hts q2
                (by simpa [Config.locSup] using Nat.le_trans hpb.2 hmono)
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
          rcases pc with ⟨pc, bp⟩ | msg
          case aborted => simp [throw, throwThe, MonadExceptOf.throw] at h
          cases pc <;>
            try (simp [throw, throwThe, MonadExceptOf.throw] at h)
          case blockedSelect evs envs ks =>
            have hpc := pool_get_wf hts hj
            have hpb : evClausesSup evs ≤ s.nextAddr
                ∧ LocalEnv.locSup envs ≤ s.nextAddr
                ∧ Cont.locSup ks ≤ s.nextAddr := by
              simp only [ConfigWf, Config.locSup, Nat.max_le] at hpc
              omega
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
                  obtain ⟨⟨cr, s₂⟩, hdel, hts', hs', -⟩ := h
                  subst hts' hs'
                  obtain ⟨q1, q2, q4⟩ := resumeRecvDelivery_wf hw hv'b
                    hb.2.1 hb.2.2.1 hb.2.2.2 hdel
                  refine ⟨q1, q4, by simp, ?_⟩
                  refine pool_set2_wf q4 hts q2 ?_
                  simp only [Config.locSup, Nat.max_le]
                  omega
                | some hd =>
                  have hhdb : GoValue.locSup hd ≤ s.nextAddr := by
                    have := goValueListSup_mem (l := buf.toList) (v := hd)
                      (List.mem_of_getElem? (by simpa using hhd))
                    omega
                  simp only [hhd, bind_eq_ok] at h
                  obtain ⟨s₁, hst, h⟩ := h
                  obtain ⟨w1, w2⟩ := storeChanPayload_pres hw hlocb
                    (by rw [goValueListSup_push]
                        refine Nat.max_le.mpr
                          ⟨Nat.le_trans goValueListSup_eraseIdx! (by omega),
                            hv'b⟩) hst
                  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq,
                    Prod.mk.injEq] at h
                  obtain ⟨⟨cr, s₂⟩, hdel, hts', hs', -⟩ := h
                  subst hts' hs'
                  obtain ⟨q1, q2, q4⟩ := resumeRecvDelivery_wf w1
                    (by omega) (by omega) (by omega) (by omega) hdel
                  have hmono : s.nextAddr ≤ s₂.nextAddr := Nat.le_trans w2 q4
                  refine ⟨q1, hmono, by simp, ?_⟩
                  refine pool_set2_wf hmono hts q2 ?_
                  simp only [Config.locSup, Nat.max_le]
                  omega
  case blockedSelect evs env k =>
    have hb : evClausesSup evs ≤ s.nextAddr ∧ LocalEnv.locSup env ≤ s.nextAddr
        ∧ Cont.locSup k ≤ s.nextAddr := by
      simp only [ConfigWf, Config.locSup, Nat.max_le] at hbc
      omega
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
            rcases pc with ⟨pc, bp⟩ | msg
            case aborted => simp [throw, throwThe, MonadExceptOf.throw] at h
            cases pc <;>
              try (simp [throw, throwThe, MonadExceptOf.throw] at h)
            case blockedSend ch2 vs ks =>
              have hpc := pool_get_wf hts hj
              have hpb : GoValue.locSup vs ≤ s.nextAddr
                  ∧ Cont.locSup ks ≤ s.nextAddr := by
                simp only [ConfigWf, Config.locSup, Nat.max_le] at hpc
                omega
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
                  obtain ⟨⟨ci', s₂⟩, hdel, hts', hs', -⟩ := h
                  subst hts' hs'
                  obtain ⟨q1, q2, q4⟩ := selectRecvDelivery_wf hw hpb.1
                    (by omega) (by omega) hb.2.1 hb.2.2 hdel
                  refine ⟨q1, q4, by simp, ?_⟩
                  exact pool_set2_wf q4 hts q2
                    (by simpa [Config.locSup] using Nat.le_trans hpb.2 q4)
                | some hd =>
                  have hhdb : GoValue.locSup hd ≤ s.nextAddr := by
                    have := goValueListSup_mem (l := buf.toList) (v := hd)
                      (List.mem_of_getElem? (by simpa using hhd))
                    omega
                  simp only [hhd, bind_eq_ok] at h
                  obtain ⟨s₁, hst, h⟩ := h
                  obtain ⟨w1, w2⟩ := storeChanPayload_pres hw hlocb
                    (by rw [goValueListSup_push]
                        refine Nat.max_le.mpr
                          ⟨Nat.le_trans goValueListSup_eraseIdx! (by omega),
                            hpb.1⟩) hst
                  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq,
                    Prod.mk.injEq] at h
                  obtain ⟨⟨ci', s₂⟩, hdel, hts', hs', -⟩ := h
                  subst hts' hs'
                  obtain ⟨q1, q2, q4⟩ := selectRecvDelivery_wf w1
                    (by omega) (by omega) (by omega) (by omega) (by omega)
                    hdel
                  have hmono : s.nextAddr ≤ s₂.nextAddr := Nat.le_trans w2 q4
                  refine ⟨q1, hmono, by simp, ?_⟩
                  exact pool_set2_wf hmono hts q2
                    (by simpa [Config.locSup] using Nat.le_trans hpb.2 hmono)
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
            rcases pc with ⟨pc, bp⟩ | msg
            case aborted => simp [throw, throwThe, MonadExceptOf.throw] at h
            cases pc <;>
              try (simp [throw, throwThe, MonadExceptOf.throw] at h)
            case blockedRecv ch2 targetsr elemr envr kr =>
              have hpc := pool_get_wf hts hj
              have hpb : assigneeListSup targetsr ≤ s.nextAddr
                  ∧ LocalEnv.locSup envr ≤ s.nextAddr
                  ∧ Cont.locSup kr ≤ s.nextAddr := by
                simp only [ConfigWf, Config.locSup, Nat.max_le] at hpc
                omega
              cases hloc : chanValueLoc chv with
              | none => simp [hloc, throw, throwThe, MonadExceptOf.throw] at h
              | some loc =>
                simp only [hloc, bind_eq_ok] at h
                obtain ⟨⟨buf, cap, closed⟩, hcell, h⟩ := h
                split at h
                · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq,
                    Prod.mk.injEq] at h
                  obtain ⟨v', hv', ⟨cr, s₂⟩, hdel, hts', hs', -⟩ := h
                  subst hts' hs'
                  have hv'b : GoValue.locSup v' ≤ s.nextAddr := by
                    have := normalizeValueForTy_locSup hv'
                    omega
                  obtain ⟨q1, q2, q4⟩ := resumeRecvDelivery_wf hw hv'b
                    hpb.1 hpb.2.1 hpb.2.2 hdel
                  refine ⟨q1, q4, by simp, ?_⟩
                  refine pool_set2_wf q4 hts ?_ q2
                  simp only [Config.locSup, Nat.max_le]
                  omega
                · simp [throw, throwThe, MonadExceptOf.throw] at h
  all_goals simp [applyPairing, throw, throwThe, MonadExceptOf.throw] at h


/-- Frame lemma for a single-slot pool update. -/
theorem pool_set1_wf {threads : Array Thread} {i : Nat} {a : Config}
    {fa : Option ChoiceSite} {na na' : Nat}
    (hmono : na ≤ na')
    (hts : ∀ t (ht : t < threads.size), ThreadWf na threads[t])
    (ha : Config.locSup a ≤ na') :
    ∀ t (ht : t < (threads.setIfInBounds i (.running a fa)).size),
      ThreadWf na' (threads.setIfInBounds i (.running a fa))[t] := by
  intro t ht
  have ht' : t < threads.size := by simpa using ht
  simp only [Array.getElem_setIfInBounds, Array.size_setIfInBounds, ht']
  split
  · exact ThreadWf.running ha
  · exact ThreadWf.mono hmono (hts t ht')

/-- Frame lemma for the abort's pool update: one slot tombstoned (B4). -/
theorem pool_set1_aborted_wf {threads : Array Thread} {i : Nat} {msg : String}
    {na : Nat}
    (hts : ∀ t (ht : t < threads.size), ThreadWf na threads[t]) :
    ∀ t (ht : t < (threads.setIfInBounds i (.aborted msg)).size),
      ThreadWf na (threads.setIfInBounds i (.aborted msg))[t] := by
  intro t ht
  have ht' : t < threads.size := by simpa using ht
  simp only [Array.getElem_setIfInBounds, Array.size_setIfInBounds, ht']
  split
  · exact ThreadWf.aborted
  · exact hts t ht'

/-- Frame lemma for the spawn's pool update: one slot replaced, one
child appended. -/
theorem pool_set_push_wf {threads : Array Thread} {i : Nat} {a b : Config}
    {fa fb : Option ChoiceSite} {na na' : Nat}
    (hmono : na ≤ na')
    (hts : ∀ t (ht : t < threads.size), ThreadWf na threads[t])
    (ha : Config.locSup a ≤ na') (hb : Config.locSup b ≤ na') :
    ∀ t (ht : t < ((threads.setIfInBounds i (.running a fa)).push (.running b fb)).size),
      ThreadWf na' ((threads.setIfInBounds i (.running a fa)).push (.running b fb))[t] := by
  intro t ht
  have hsz : t < (threads.setIfInBounds i (.running a fa)).size + 1 := by simpa using ht
  rw [Array.getElem_push]
  split
  · rename_i hlt
    exact pool_set1_wf hmono hts ha t hlt
  · exact ThreadWf.running hb

/-- Membership in the runnable list bounds the index. -/
theorem runnableIdxs_lt {s : Store} {ts : Array Thread} {i : Nat}
    (h : i ∈ runnableIdxs ctx s ts) : i < ts.size := by
  unfold runnableIdxs at h
  exact List.mem_range.mp (List.mem_filter.mp h).1

/-- `stepThread` preservation: one goroutine-step of the pool keeps the
shared state wf (allocator monotone), never shrinks the pool, and
leaves every slot bounded. -/
theorem stepThread_wf {s : Store} {threads : Array Thread} {i : Nat}
    {ch ch' : Choices} {ts' : Array Thread} {s' : Store} {ev : StepEvent}
    (hw : StateWf ctx s)
    (hts : ∀ t (ht : t < threads.size), ThreadWf s.nextAddr threads[t])
    (h : stepThread ctx s threads i ch = .ok (ts', s', ch', ev)) :
    StateWf ctx s' ∧ s.nextAddr ≤ s'.nextAddr
      ∧ threads.size ≤ ts'.size
      ∧ ∀ t (ht : t < ts'.size), ThreadWf s'.nextAddr ts'[t] := by
  unfold stepThread at h
  cases hti : threads[i]? with
  | none => rw [hti] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some t =>
    rw [hti] at h
    rcases t with ⟨c, b⟩ | msg
    case aborted => simp [throw, throwThe, MonadExceptOf.throw] at h
    have hc := pool_get_wf hts hti
    cases b with
    | some site =>
      -- the boundary CLEAR (C5): state and configuration untouched
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨hw, Nat.le_refl _, by simp, pool_set1_wf (Nat.le_refl _) hts hc⟩
    | none =>
    by_cases hblc : isBlockedConfig c = true
    · simp only [hblc, reduceIte, bind_eq_ok] at h
      obtain ⟨⟨c₂, s₂, tr₂⟩, hres, h⟩ := h
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      obtain ⟨q1, q2, q4⟩ := resumeThread_wf hw hc hres
      exact ⟨q1, q4, by simp, pool_set1_wf q4 hts q2⟩
    · simp only [Bool.not_eq_true] at hblc
      simp only [hblc, Bool.false_eq_true, reduceIte] at h
      cases hab : c.abort? with
      | some p =>
        -- THE ABORT (B4): the tombstone carries no location
        obtain ⟨first, rest⟩ := p
        rw [hab] at h
        simp only [bind_eq_ok] at h
        obtain ⟨msg, -, h⟩ := h
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨hw, Nat.le_refl _, by simp, pool_set1_aborted_wf hts⟩
      | none =>
        rw [hab] at h
        cases hsp : spawnPlan c with
        | some p =>
          obtain ⟨cv, args, k⟩ := p
          rw [hsp] at h
          simp only [bind_eq_ok] at h
          obtain ⟨⟨parent', child, s₂, ch₂, tr₂⟩, hspawn, h⟩ := h
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          obtain ⟨hcvb, hargsb, hkb⟩ := spawnPlan_locSup hsp
          obtain ⟨q1, q2, q3, q5⟩ := spawnStep_wf hw
            (Nat.le_trans hcvb hc) (Nat.le_trans hargsb hc)
            (Nat.le_trans hkb hc) hspawn
          refine ⟨q1, q5, by simp, ?_⟩
          exact pool_set_push_wf q5 hts q2 q3
        | none =>
          rw [hsp] at h
          simp only [bind_eq_ok] at h
          obtain ⟨⟨plan, ch₁, ps₁⟩, hplan, h⟩ := h
          cases harr : arrivalCases ctx s threads i c with
          | error e =>
            rw [arrivalPlan_of_error (ch := ch) harr] at hplan
            cases hplan
          | ok r =>
            cases r with
            | cellPath =>
              rw [arrivalPlan_of_cellPath (ch := ch) harr] at hplan
              simp only [Except.ok.injEq, Prod.mk.injEq] at hplan
              obtain ⟨hp1, hp2, hp3⟩ := hplan
              subst hp1
              subst hp2
              subst hp3
              dsimp only at h
              cases hselp : selectApplyPlan c with
              | none =>
                rw [hselp] at h
                dsimp only at h
                simp only [bind_eq_ok] at h
                obtain ⟨⟨c₂, s₂, ch₂, tr₂⟩, hstep, h⟩ := h
                simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                have hstepr := stepFn_sound hstep
                obtain ⟨q1, q2, q4⟩ := step_preserves_wf_loc hstepr hw hc
                exact ⟨q1, q4, by simp, pool_set1_wf q4 hts q2⟩
              | some p =>
                obtain ⟨v, clauses, default?, done, env, k'⟩ := p
                obtain rfl := selectApplyPlan_shape hselp
                rw [hselp] at h
                dsimp only at h
                have hcomp : selectClausesSup clauses ≤ s.nextAddr
                    ∧ optStmtSup default? ≤ s.nextAddr
                    ∧ goValueListSup ((v :: done).reverse) ≤ s.nextAddr
                    ∧ LocalEnv.locSup env ≤ s.nextAddr
                    ∧ Cont.locSup k' ≤ s.nextAddr := by
                  rw [goValueListSup_reverse]
                  simp only [ConfigWf, Config.locSup, Cont.locSup,
                    goValueListSup, exprListSup, Nat.max_le] at hc
                  simp only [goValueListSup]
                  omega
                obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hcomp
                cases happly : applySelect ctx s clauses default?
                    ((v :: done).reverse) env k' ch with
                | ok r₂ =>
                  obtain ⟨c₂, s₂, ch₂, cl?⟩ := r₂
                  rw [happly] at h
                  simp only [toResult_ok, Bind.bind, Except.bind, pure_eq_ok,
                    Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                  obtain ⟨q1, q2, q4⟩ :=
                    applySelect_wf hw hb1 hb2 hb3 hb4 hb5 happly
                  exact ⟨q1, q4, by simp, pool_set1_wf q4 hts q2⟩
                | error e =>
                  rw [happly] at h
                  cases_stop e <;>
                    simp only [toResult_panic, toResult_refusal, toResult_fatal, toResult_deadlock,
                      toResult_raceDetected, toResult_fuelOut, Bind.bind, Except.bind, pure_eq_ok,
                      deliver_panic, List.nil_append, Except.ok.injEq, Prod.mk.injEq,
                      reduceCtorEq] at h
                  case panic msg =>
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                  refine ⟨hw, Nat.le_refl _, by simp, ?_⟩
                  refine pool_set1_wf (Nat.le_refl _) hts ?_
                  simp only [ConfigWf, Config.locSup, Cont.locSup,
                    goValueListSup, exprListSup, Nat.max_le] at hc ⊢
                  simp only [panicChainSup, panicEntry_locSup]
                  omega
            | single bc cands =>
              rw [arrivalPlan_of_single (ch := ch) harr] at hplan
              simp only [Except.ok.injEq, Prod.mk.injEq] at hplan
              obtain ⟨hp1, hp2, hp3⟩ := hplan
              subst hp1
              subst hp2
              subst hp3
              have hbcb := arrivalCases_single_wf hw hc harr
              cases cands with
              | nil => simp [throw, throwThe, MonadExceptOf.throw] at h
              | cons cand rest =>
                  dsimp only at h
                  rcases hcons : Choices.consumeAtE .l4Waiter
                      (cand :: rest).length ch with ⟨idx, ch₂, ps₂⟩
                  rw [hcons] at h
                  dsimp only at h
                  cases hget : (cand :: rest)[idx]? with
                  | none =>
                    rw [hget] at h
                    simp [throw, throwThe, MonadExceptOf.throw] at h
                  | some cand3 =>
                    rw [hget] at h
                    simp only [bind_eq_ok] at h
                    obtain ⟨⟨ts₂, s₂, tr₂⟩, hpair, h⟩ := h
                    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                    obtain ⟨q1, q3, q4, q5⟩ := applyPairing_wf hw hts hbcb
                      hpair
                    exact ⟨q1, q3, by omega, q5⟩
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
                obtain ⟨hp1, hp2, hp3⟩ := hplan
                subst hp1
                subst hp2
                subst hp3
                obtain ⟨hpairb, hcommitb⟩ := arrivalCases_multi_wf hw hc
                  harr hget
                cases o with
                | pair bc cands =>
                  have hbcb := hpairb rfl
                  cases cands with
                  | nil => simp [throw, throwThe, MonadExceptOf.throw] at h
                  | cons cand rest =>
                      dsimp only at h
                      rcases hcons2 : Choices.consumeAtE .l4Waiter
                          (cand :: rest).length chs with ⟨idx, ch₂, ps₂⟩
                      rw [hcons2] at h
                      dsimp only at h
                      cases hget2 : (cand :: rest)[idx]? with
                      | none =>
                        rw [hget2] at h
                        simp [throw, throwThe, MonadExceptOf.throw] at h
                      | some cand3 =>
                        rw [hget2] at h
                        simp only [bind_eq_ok] at h
                        obtain ⟨⟨ts₂, s₂, tr₂⟩, hpair, h⟩ := h
                        simp only [pure_eq_ok, Except.ok.injEq,
                          Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                        obtain ⟨q1, q3, q4, q5⟩ := applyPairing_wf hw hts
                          hbcb hpair
                        exact ⟨q1, q3, by omega, q5⟩
                | commit evs cl env k =>
                  obtain ⟨hclb, henvb, hkb⟩ := hcommitb rfl
                  dsimp only at h
                  simp only [bind_eq_ok] at h
                  obtain ⟨⟨c₂, s₂, tr₂⟩, hcom, h⟩ := h
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                  obtain ⟨q1, q2, q4⟩ := commitClause_wf hw hclb henvb
                    hkb hcom
                  exact ⟨q1, q4, by simp, pool_set1_wf q4 hts q2⟩

/-- **`MultiWf` preservation** — the executable pool step keeps the
thread-indexed invariant. This is the slice-2 scaffold's owed theorem
(`Multi.lean`, `MultiWf`'s docstring): the invariant carrier is now a
PRESERVED invariant, not a definition awaiting one. -/
theorem stepMulti_wf {m m' : MultiConfig} {ch ch' : Choices} {ev : StepEvent}
    (hwf : MultiWf ctx m) (h : stepMulti ctx m ch = .ok (m', ch', ev)) : MultiWf ctx m' := by
  obtain ⟨hs, hcur, hth⟩ := hwf
  have hstep : ∀ i, i < m.threads.size →
      ∀ {ch₀ : Choices} {ev₀ : StepEvent},
        stepThreadInto ctx m i ch₀ = .ok (m', ch', ev₀) → MultiWf ctx m' := by
    intro i hi ch₀ ev₀ hinto
    unfold stepThreadInto at hinto
    simp only [bind_eq_ok] at hinto
    obtain ⟨⟨ts, s₂, ch₂, ev₂⟩, hst, hinto⟩ := hinto
    simp only [pure_eq_ok, Except.ok.injEq] at hinto
    obtain ⟨rfl, rfl, rfl⟩ := hinto
    obtain ⟨q1, q3, q4, q5⟩ := stepThread_wf hs hth hst
    refine ⟨q1, Nat.lt_of_lt_of_le hi q4, ?_⟩
    intro t ht
    exact q5 t ht
  unfold stepMulti at h
  cases hti : m.threads[m.cur]? with
  | none => rw [hti] at h; cases h
  | some t =>
    rw [hti] at h
    by_cases hb : t.atBoundary = true
    · simp only [hb, reduceIte] at h
      cases hrs : schedSlots ctx m.shared m.threads m.cur t.boundarySite with
      | nil => rw [hrs] at h; cases h
      | cons r0 rest =>
        rw [hrs] at h
        dsimp only at h
        rcases hcons : Choices.consumeAtE t.boundarySite
            (r0 :: rest).length ch
          with ⟨pick, ch₁, ps⟩
        rw [hcons] at h
        cases hget : (r0 :: rest)[pick]? with
        | none => rw [hget] at h; cases h
        | some i =>
          rw [hget] at h
          simp only [bind_eq_ok] at h
          obtain ⟨⟨m₂, ch₂, ev₂⟩, hinto, h⟩ := h
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine hstep i
            (runnableIdxs_lt (ctx := ctx) (s := m.shared) (ts := m.threads) ?_) hinto
          refine schedSlots_mem hti ?_
          rw [hrs]
          exact List.mem_of_getElem? hget
    · simp only [Bool.not_eq_true] at hb
      simp only [hb, Bool.false_eq_true, reduceIte] at h
      exact hstep m.cur hcur h

end GoLean.GoCore.Machine
