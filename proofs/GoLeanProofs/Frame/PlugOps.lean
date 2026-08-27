import GoLeanProofs.Frame.Plug

/-!
# The plug rule, part 2: helper commutations (design note §7)

Per-helper commutation of `plugK` with every continuation-inspecting
helper the step function calls: head shape preservation, `seqCont`,
`contHeadLabel`, `pushDefer`, `panicPassthrough`, the recover pair
(`recoverThroughWrappers`/`recoverResult` — where the §7 premise
`recoverThroughWrappers k' = none` enters), and the delete-prune
walks (`pruneIterFramesKey`/`All`, `contAfterStmtOp` — where
`mapIterFree k'` enters). The proofs mirror the rename walk's helper
layer (`Frame/ContOps.lean`, `Frame/Plans.lean`) with the barrier
invariant threaded.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

variable {env' : LocalEnv} {k' : Cont}

/-! ## Reduction equations for the overlapping `frame` arms -/

/-- `plugK` at the barrier (the first arm), as an equation. -/
theorem plugK_barrier (te : LocalEnv) (r : List Loc)
    (ds : List (GoValue × List GoValue)) :
    plugK env' k' (.frame [] te r ds .stop false)
      = .frame [] env' r ds k' false := rfl

/-- `plugK` on every NON-barrier frame maps over the tail. -/
theorem plugK_frame_of_ne {t : List (TargetShape × List Expr)}
    {te : LocalEnv} {r : List Loc} {ds : List (GoValue × List GoValue)}
    {k₂ : Cont} {w : Bool}
    (h : ¬ (t = [] ∧ k₂ = .stop ∧ w = false)) :
    plugK env' k' (.frame t te r ds k₂ w)
      = .frame t te r ds (plugK env' k' k₂) w := by
  cases t <;> cases w <;> cases k₂ <;> first
    | rfl
    | exact absurd ⟨rfl, rfl, rfl⟩ h

/-- `plugK` of a frame is a frame (head preservation at the one
constructor where the barrier substitution fires). -/
theorem plugK_frame_shape (t : List (TargetShape × List Expr))
    (te : LocalEnv) (r : List Loc) (ds : List (GoValue × List GoValue))
    (k₂ : Cont) (w : Bool) :
    ∃ t₂ te₂ r₂ ds₂ k₃ w₂,
      plugK env' k' (.frame t te r ds k₂ w) = .frame t₂ te₂ r₂ ds₂ k₃ w₂ := by
  cases t <;> cases w <;> cases k₂ <;> exact ⟨_, _, _, _, _, _, rfl⟩

/-- `hasBarrierK` at the barrier. -/
theorem hasBarrierK_barrier (te : LocalEnv) (r : List Loc)
    (ds : List (GoValue × List GoValue)) :
    hasBarrierK (.frame [] te r ds .stop false) = true := rfl

/-- `hasBarrierK` on every non-barrier frame recurses on the tail. -/
theorem hasBarrierK_frame_of_ne {t : List (TargetShape × List Expr)}
    {te : LocalEnv} {r : List Loc} {ds : List (GoValue × List GoValue)}
    {k₂ : Cont} {w : Bool}
    (h : ¬ (t = [] ∧ k₂ = .stop ∧ w = false)) :
    hasBarrierK (.frame t te r ds k₂ w) = hasBarrierK k₂ := by
  cases t <;> cases w <;> cases k₂ <;> first
    | rfl
    | exact absurd ⟨rfl, rfl, rfl⟩ h

/-- A barrier-carrying continuation is never bare `.stop`. -/
theorem ne_stop_of_hasBarrier {k : Cont} (hb : hasBarrierK k = true) :
    k ≠ .stop := by
  intro h; subst h; simp [hasBarrierK] at hb

/-- Wrapper frames are never the barrier: `plugK` maps over them. -/
theorem plugK_frame_wrapper (t : List (TargetShape × List Expr))
    (te : LocalEnv) (r : List Loc) (ds : List (GoValue × List GoValue))
    (k₂ : Cont) :
    plugK env' k' (.frame t te r ds k₂ true)
      = .frame t te r ds (plugK env' k' k₂) true := by
  cases t <;> cases k₂ <;> rfl

/-- A frame whose TAIL carries the barrier: `plugK` maps over it (the
tail cannot be `.stop`). -/
theorem plugK_frame_of_bar {t : List (TargetShape × List Expr)}
    {te : LocalEnv} {r : List Loc} {ds : List (GoValue × List GoValue)}
    {k₂ : Cont} {w : Bool} (hb₂ : hasBarrierK k₂ = true) :
    plugK env' k' (.frame t te r ds k₂ w)
      = .frame t te r ds (plugK env' k' k₂) w :=
  plugK_frame_of_ne (fun h => ne_stop_of_hasBarrier hb₂ h.2.1)

/-- A frame over a barrier-carrying tail carries the barrier. -/
theorem hasBarrierK_frame_of_tail {t : List (TargetShape × List Expr)}
    {te : LocalEnv} {r : List Loc} {ds : List (GoValue × List GoValue)}
    {k₂ : Cont} {w : Bool} (hb₂ : hasBarrierK k₂ = true) :
    hasBarrierK (.frame t te r ds k₂ w) = true := by
  rw [hasBarrierK_frame_of_ne (fun h => ne_stop_of_hasBarrier hb₂ h.2.1)]
  exact hb₂

/-- The recover walk's `some` result is never bare `.stop` (every
resolving arm rebuilds a constructor around the marked marker). -/
theorem rtw_some_ne_stop :
    ∀ {k : Cont} {v : GoValue} {k₃ : Cont},
      recoverThroughWrappers k = some (v, k₃) → k₃ ≠ .stop := by
  intro k
  induction k <;> intro v k₃ hpr
  case stop => exact absurd hpr (by simp [recoverThroughWrappers])
  case panicResumeK chain k₂ _ =>
      simp only [recoverThroughWrappers] at hpr
      cases hm : markNewestRecovered chain <;> rw [hm] at hpr
      · exact absurd hpr (by simp)
      · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpr
        rw [← hpr.2]
        intro hcon; exact Cont.noConfusion hcon
  case frame t te r ds k₂ w ih =>
      cases w with
      | false => exact absurd hpr (by simp [recoverThroughWrappers])
      | true =>
          simp only [recoverThroughWrappers] at hpr
          cases hm : recoverThroughWrappers k₂ <;> rw [hm] at hpr
          · exact absurd hpr (by simp)
          · rename_i p; obtain ⟨v₂, k₄⟩ := p
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpr
            rw [← hpr.2]
            intro hcon; exact Cont.noConfusion hcon
  all_goals
    rename_i k₂ _
    simp only [recoverThroughWrappers] at hpr
    cases hm : recoverThroughWrappers k₂ <;> rw [hm] at hpr
    · exact absurd hpr (by simp)
    · rename_i p; obtain ⟨v₂, k₄⟩ := p
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpr
      rw [← hpr.2]
      intro hcon; exact Cont.noConfusion hcon

/-! ## seqCont / contHeadLabel -/

theorem seqCont_plug {k : Cont} (hb : hasBarrierK k = true)
    (ss : List Stmt) (env : LocalEnv) :
    seqCont ss env (plugK env' k' k) = plugK env' k' (seqCont ss env k) := by
  cases k
  case stop => simp [hasBarrierK] at hb
  case seq rest env₂ k₂ =>
      by_cases henv : env₂ = env <;>
        simp [plugK, seqCont, henv]
  case frame t te r ds k₂ w =>
      obtain ⟨t₂, te₂, r₂, ds₂, k₃, w₂, hsh⟩ :=
        plugK_frame_shape (env' := env') (k' := k') t te r ds k₂ w
      rw [hsh]
      show Cont.seq ss env _ = plugK env' k' (.seq ss env (.frame t te r ds k₂ w))
      rw [show plugK env' k' (.seq ss env (.frame t te r ds k₂ w))
            = .seq ss env (plugK env' k' (.frame t te r ds k₂ w)) from rfl, hsh]
  all_goals rfl

theorem contHeadLabel_plug {k : Cont} (hb : hasBarrierK k = true) :
    contHeadLabel (plugK env' k' k) = contHeadLabel k := by
  cases k
  case stop => simp [hasBarrierK] at hb
  case frame t te r ds k₂ w =>
      obtain ⟨_, _, _, _, _, _, hsh⟩ :=
        plugK_frame_shape (env' := env') (k' := k') t te r ds k₂ w
      rw [hsh]; rfl
  all_goals rfl

/-! ## pushDefer -/

theorem pushDefer_plug {k : Cont} (hb : hasBarrierK k = true)
    (d : GoValue × List GoValue) :
    pushDefer d (plugK env' k' k) = (pushDefer d k).map (plugK env' k') := by
  induction k
  case stop => simp [hasBarrierK] at hb
  case frame t te r ds k₂ w _ =>
      cases t <;> cases w <;> cases k₂ <;> rfl
  case seq rest env₂ k₂ ih =>
      simp only [hasBarrierK] at hb
      simp only [plugK, pushDefer, ih hb]
      cases pushDefer d k₂ <;> rfl
  case loop c b env₂ k₂ ih =>
      simp only [hasBarrierK] at hb
      simp only [plugK, pushDefer, ih hb]
      cases pushDefer d k₂ <;> rfl
  case breakableK k₂ ih =>
      simp only [hasBarrierK] at hb
      simp only [plugK, pushDefer, ih hb]
      cases pushDefer d k₂ <;> rfl
  case labelK name k₂ ih =>
      simp only [hasBarrierK] at hb
      simp only [plugK, pushDefer, ih hb]
      cases pushDefer d k₂ <;> rfl
  case mapIterK kv vv kt vt b base prod st env₂ k₂ ih =>
      simp only [hasBarrierK] at hb
      simp only [plugK, pushDefer, ih hb]
      cases pushDefer d k₂ <;> rfl
  all_goals rfl

/-! ## panicPassthrough -/

theorem panicPassthrough_plug {k : Cont} (hb : hasBarrierK k = true) :
    panicPassthrough (plugK env' k' k)
      = (panicPassthrough k).map (plugK env' k') := by
  cases k
  case stop => simp [hasBarrierK] at hb
  case frame t te r ds k₂ w =>
      obtain ⟨_, _, _, _, _, _, hsh⟩ :=
        plugK_frame_shape (env' := env') (k' := k') t te r ds k₂ w
      rw [hsh]; rfl
  all_goals rfl

/-! ## The recover pair (the §7 premise `hrc` enters here) -/

theorem recoverThroughWrappers_plug {k : Cont}
    (hb : hasBarrierK k = true)
    (hrc : recoverThroughWrappers k' = none) :
    recoverThroughWrappers (plugK env' k' k)
      = (recoverThroughWrappers k).map
          (fun p => (p.1, plugK env' k' p.2)) := by
  induction k
  case stop => simp [hasBarrierK] at hb
  case frame t te r ds k₂ w ih =>
      cases w with
      | false =>
          -- non-wrapper frame: refutes on BOTH sides without looking
          -- below — barrier or not.
          by_cases hbar : t = [] ∧ k₂ = .stop
          · obtain ⟨ht, hk⟩ := hbar; subst ht; subst hk
            rfl
          · rw [plugK_frame_of_ne (fun h => hbar ⟨h.1, h.2.1⟩)]; rfl
      | true =>
          -- wrapper frame: the walk crosses. Under the invariant the
          -- tail still carries the barrier (a wrapper over .stop is
          -- not a well-shaped barrier).
          have hb₂ : hasBarrierK k₂ = true := by
            rwa [hasBarrierK_frame_of_ne (by simp)] at hb
          rw [plugK_frame_wrapper]
          simp only [recoverThroughWrappers, ih hb₂]
          cases recoverThroughWrappers k₂ with
          | none => rfl
          | some p =>
              obtain ⟨v, k₃⟩ := p
              simp [plugK_frame_wrapper]
  case panicResumeK chain k₂ _ =>
      simp only [plugK, recoverThroughWrappers]
      cases markNewestRecovered chain with
      | none => rfl
      | some p => obtain ⟨v, c⟩ := p; rfl
  all_goals
    rename_i k₂ ih
    simp only [hasBarrierK] at hb
    simp only [plugK, recoverThroughWrappers, ih hb]
    cases recoverThroughWrappers k₂ with
    | none => rfl
    | some p => obtain ⟨v, k₃⟩ := p; rfl

theorem recoverResult_plug {k : Cont}
    (hb : hasBarrierK k = true)
    (hrc : recoverThroughWrappers k' = none) :
    recoverResult (plugK env' k' k)
      = ((recoverResult k).1, plugK env' k' (recoverResult k).2) := by
  induction k
  case stop => simp [hasBarrierK] at hb
  case panicResumeK chain k₂ _ => rfl
  case frame t te r ds k₂ w ih =>
      cases w with
      | false =>
          by_cases hbar : t = [] ∧ k₂ = .stop
          · -- THE BARRIER: canonical looks below at `.stop` (none);
            -- plugged looks below at k' — the premise closes it.
            obtain ⟨ht, hk⟩ := hbar; subst ht; subst hk
            show recoverResult (.frame [] env' r ds k' false) = _
            simp only [recoverResult, hrc]
            rfl
          · have hne : ¬ (t = [] ∧ k₂ = .stop ∧ (false : Bool) = false) :=
              fun h => hbar ⟨h.1, h.2.1⟩
            have hb₂ : hasBarrierK k₂ = true := by
              rwa [hasBarrierK_frame_of_ne hne] at hb
            rw [plugK_frame_of_ne hne]
            cases hm : recoverThroughWrappers k₂ with
            | none =>
                simp only [recoverResult,
                  recoverThroughWrappers_plug hb₂ hrc, hm,
                  Option.map_none]
                rw [plugK_frame_of_ne hne]
            | some p =>
                obtain ⟨v, k₃⟩ := p
                simp only [recoverResult,
                  recoverThroughWrappers_plug hb₂ hrc, hm,
                  Option.map_some]
                rw [plugK_frame_of_ne (fun h => rtw_some_ne_stop hm h.2.1)]
      | true =>
          have hb₂ : hasBarrierK k₂ = true := by
            rwa [hasBarrierK_frame_of_ne (by simp)] at hb
          rw [plugK_frame_wrapper]
          cases hrk : recoverResult k₂
          simp only [recoverResult, ih hb₂, hrk]
          rw [plugK_frame_wrapper]
  all_goals
    rename_i k₂ ih
    simp only [hasBarrierK] at hb
    cases hrk : recoverResult k₂
    simp only [plugK, recoverResult, ih hb, hrk]

/-! ## The delete-prune walks (the §7 premise `hmf` enters here) -/

/-- On a `mapIterK`-free spine the keyed prune is the identity. -/
theorem pruneKey_id_of_mapIterFree {k : Cont}
    (hmf : mapIterFree k = true) (s : ExecState) (l : Loc) (key : GoValue) :
    pruneIterFramesKey s l key k = .ok k := by
  induction k <;>
    first
    | rfl
    | (simp [mapIterFree] at hmf; done)
    | (rename_i ih
       simp only [mapIterFree] at hmf
       simp [pruneIterFramesKey, ih hmf, bind, Except.bind, pure,
         Except.pure])

/-- On a `mapIterK`-free spine the clear-prune is the identity. -/
theorem pruneAll_id_of_mapIterFree {k : Cont}
    (hmf : mapIterFree k = true) (l : Loc) :
    pruneIterFramesAll l k = k := by
  induction k <;>
    first
    | rfl
    | (simp [mapIterFree] at hmf; done)
    | (rename_i ih
       simp only [mapIterFree] at hmf
       simp [pruneIterFramesAll, ih hmf])

/-- The clear-prune never produces bare `.stop` from a non-`.stop`
spine (single-level: every arm rebuilds its own constructor). -/
theorem pruneAll_ne_stop {l : Loc} :
    ∀ {k : Cont}, k ≠ .stop → pruneIterFramesAll l k ≠ .stop := by
  intro k hne
  cases k
  case stop => exact absurd rfl hne
  case mapIterK kv vv kt vt b base prod st env₂ k₂ =>
      by_cases hbase : base == some l <;>
        simp [pruneIterFramesAll, hbase]
  all_goals simp [pruneIterFramesAll]

/-- The keyed prune never produces bare `.stop` from a non-`.stop`
spine. -/
theorem pruneKey_ne_stop {s : ExecState} {l : Loc} {key : GoValue} :
    ∀ {k k₃ : Cont}, k ≠ .stop →
      pruneIterFramesKey s l key k = .ok k₃ → k₃ ≠ .stop := by
  intro k k₃ hne hpr
  cases k
  case stop => exact absurd rfl hne
  case mapIterK kv vv kt vt b base prod st env₂ k₂ =>
      simp only [pruneIterFramesKey, bind, Except.bind] at hpr
      cases hp2 : pruneIterFramesKey s l key k₂ <;> rw [hp2] at hpr
      · exact absurd hpr (by simp)
      · by_cases hbase : base == some l
        · simp only [hbase, if_pos] at hpr
          cases h1 : removeKeyList s kt key prod.toList <;> rw [h1] at hpr
          · exact absurd hpr (by simp [bind, Except.bind])
          · cases h2 : removeKeyList s kt key st.toList <;> rw [h2] at hpr
            · exact absurd hpr (by simp [bind, Except.bind])
            · simp only [bind, Except.bind, pure, Except.pure,
                Except.ok.injEq] at hpr
              rw [← hpr]; intro hcon; exact Cont.noConfusion hcon
        · simp only [hbase, if_neg, Bool.false_eq_true,
            not_false_eq_true, pure, Except.pure, Except.ok.injEq] at hpr
          rw [← hpr]; intro hcon; exact Cont.noConfusion hcon
  case frame t te r ds k₂ w =>
      simp only [pruneIterFramesKey, bind, Except.bind] at hpr
      cases hp2 : pruneIterFramesKey s l key k₂ <;> rw [hp2] at hpr
      · exact absurd hpr (by simp)
      · simp only [pure, Except.pure, Except.ok.injEq] at hpr
        rw [← hpr]; intro hcon; exact Cont.noConfusion hcon
  all_goals
    rename_i k₂
    simp only [pruneIterFramesKey, bind, Except.bind] at hpr
    cases hp2 : pruneIterFramesKey s l key k₂ <;> rw [hp2] at hpr
    · exact absurd hpr (by simp)
    · simp only [pure, Except.pure, Except.ok.injEq] at hpr
      rw [← hpr]; intro hcon; exact Cont.noConfusion hcon

theorem pruneKey_plug {k : Cont} (hb : hasBarrierK k = true)
    (hmf : mapIterFree k' = true)
    (s : ExecState) (l : Loc) (key : GoValue) :
    pruneIterFramesKey s l key (plugK env' k' k)
      = (pruneIterFramesKey s l key k).map (plugK env' k') := by
  induction k
  case stop => simp [hasBarrierK] at hb
  case frame t te r ds k₂ w ih =>
      by_cases hbar : t = [] ∧ k₂ = .stop ∧ w = false
      · obtain ⟨ht, hk, hw⟩ := hbar; subst ht; subst hk; subst hw
        show pruneIterFramesKey s l key (.frame [] env' r ds k' false) = _
        simp only [pruneIterFramesKey,
          pruneKey_id_of_mapIterFree hmf s l key]
        rfl
      · have hb₂ : hasBarrierK k₂ = true := by
          rwa [hasBarrierK_frame_of_ne hbar] at hb
        rw [plugK_frame_of_ne hbar]
        simp only [pruneIterFramesKey, ih hb₂]
        cases hp2 : pruneIterFramesKey s l key k₂ with
        | error e => rfl
        | ok k₃ =>
            simp only [Except.map, bind, Except.bind, pure, Except.pure]
            rw [plugK_frame_of_ne
              (fun h => pruneKey_ne_stop (ne_stop_of_hasBarrier hb₂) hp2 h.2.1)]
  case mapIterK kv vv kt vt b base prod st env₂ k₂ ih =>
      simp only [hasBarrierK] at hb
      simp only [plugK, pruneIterFramesKey, ih hb]
      cases hpr : pruneIterFramesKey s l key k₂ with
      | error e => rfl
      | ok k₃ =>
          by_cases hbase : base == some l
          · simp only [hbase, if_pos]
            cases removeKeyList s kt key prod.toList <;>
              cases removeKeyList s kt key st.toList <;>
              simp [Except.map, pure, Except.pure, bind, Except.bind, plugK]
          · simp [hbase, Except.map, pure, Except.pure, bind, Except.bind,
              plugK]
  all_goals
    rename_i k₂ ih
    simp only [hasBarrierK] at hb
    simp only [plugK, pruneIterFramesKey, ih hb]
    cases pruneIterFramesKey s l key k₂ <;>
      simp [Except.map, pure, Except.pure, bind, Except.bind, plugK]

theorem pruneAll_plug {k : Cont} (hb : hasBarrierK k = true)
    (hmf : mapIterFree k' = true) (l : Loc) :
    pruneIterFramesAll l (plugK env' k' k)
      = plugK env' k' (pruneIterFramesAll l k) := by
  induction k
  case stop => simp [hasBarrierK] at hb
  case frame t te r ds k₂ w ih =>
      by_cases hbar : t = [] ∧ k₂ = .stop ∧ w = false
      · obtain ⟨ht, hk, hw⟩ := hbar; subst ht; subst hk; subst hw
        show pruneIterFramesAll l (.frame [] env' r ds k' false) = _
        simp only [pruneIterFramesAll, pruneAll_id_of_mapIterFree hmf l]
        rfl
      · have hb₂ : hasBarrierK k₂ = true := by
          rwa [hasBarrierK_frame_of_ne hbar] at hb
        rw [plugK_frame_of_ne hbar]
        simp only [pruneIterFramesAll, ih hb₂]
        rw [plugK_frame_of_ne
          (fun h => pruneAll_ne_stop (ne_stop_of_hasBarrier hb₂) h.2.1)]
  case mapIterK kv vv kt vt b base prod st env₂ k₂ ih =>
      simp only [hasBarrierK] at hb
      by_cases hbase : base == some l <;>
        simp [plugK, pruneIterFramesAll, ih hb, hbase]
  all_goals
    rename_i k₂ ih
    simp only [hasBarrierK] at hb
    simp only [plugK, pruneIterFramesAll, ih hb]

theorem contAfterStmtOp_plug {k : Cont} (hb : hasBarrierK k = true)
    (hmf : mapIterFree k' = true)
    (s : ExecState) (op : StmtOp) (vs : List GoValue) :
    contAfterStmtOp s op vs (plugK env' k' k)
      = (contAfterStmtOp s op vs k).map (plugK env' k') := by
  unfold contAfterStmtOp
  cases op
  case mapDelete keyTy =>
      match vs with
      | [baseV, keyV] =>
          cases hvm : valueAsMap baseV with
          | error e => simp [hvm, Except.map, bind, Except.bind]
          | ok m =>
              cases hmb : m.base with
              | none => simp [hvm, hmb, Except.map, bind, Except.bind,
                  pure, Except.pure]
              | some l =>
                  simp only [hvm, hmb, bind, Except.bind, pure, Except.pure]
                  cases hn : normalizeValueForTy s keyTy keyV with
                  | error e => simp [Except.map]
                  | ok keyN =>
                      simp only [pruneKey_plug hb hmf s l keyN]
                      all_goals cases pruneIterFramesKey s l keyN k <;> rfl
      | [] => rfl
      | [_] => rfl
      | _ :: _ :: _ :: _ => rfl
  case clearMap =>
      match vs with
      | [baseV] =>
          cases hvm : valueAsMap baseV with
          | error e => simp [hvm, Except.map, bind, Except.bind]
          | ok m =>
              cases hmb : m.base with
              | none => simp [hvm, hmb, Except.map, bind, Except.bind,
                  pure, Except.pure]
              | some l =>
                  simp [hvm, hmb, bind, Except.bind, pure, Except.pure,
                    pruneAll_plug hb hmf l, Except.map]
      | [] => rfl
      | _ :: _ :: _ => rfl
  all_goals rfl


/-! ## Barrier preservation through the prunes (consumed by the walk's
classification conclusion) -/

/-- The keyed prune result of `.stop` is `.stop`. -/
theorem pruneKey_stop {s : ExecState} {l : Loc} {key : GoValue} {k₃ : Cont}
    (h : pruneIterFramesKey s l key .stop = .ok k₃) : k₃ = .stop := by
  simp only [pruneIterFramesKey, pure, Except.pure, Except.ok.injEq] at h
  exact h.symm

theorem pruneKey_bar {s : ExecState} {l : Loc} {key : GoValue} :
    ∀ {k k₃ : Cont}, pruneIterFramesKey s l key k = .ok k₃ →
      hasBarrierK k₃ = hasBarrierK k := by
  intro k
  induction k <;> intro k₃ hpr
  case stop => rw [pruneKey_stop hpr]
  case frame t te r ds k₂ w ih =>
      simp only [pruneIterFramesKey, bind, Except.bind] at hpr
      cases hp2 : pruneIterFramesKey s l key k₂ <;> rw [hp2] at hpr
      · exact absurd hpr (by simp)
      · rename_i k₄
        simp only [pure, Except.pure, Except.ok.injEq] at hpr
        subst hpr
        by_cases hb2 : t = [] ∧ k₂ = .stop ∧ w = false
        · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
          rw [pruneKey_stop hp2]
        · have h4 : ¬ (t = [] ∧ k₄ = .stop ∧ w = false) := by
            intro hh
            by_cases hk2 : k₂ = .stop
            · exact hb2 ⟨hh.1, hk2, hh.2.2⟩
            · exact pruneKey_ne_stop hk2 hp2 hh.2.1
          rw [hasBarrierK_frame_of_ne h4, hasBarrierK_frame_of_ne hb2,
            ih hp2]
  case mapIterK kv vv kt vt b base prod st env₂ k₂ ih =>
      simp only [pruneIterFramesKey, bind, Except.bind] at hpr
      cases hp2 : pruneIterFramesKey s l key k₂ <;> rw [hp2] at hpr
      · exact absurd hpr (by simp)
      · rename_i k₄
        by_cases hbase : base == some l
        · simp only [hbase, if_pos] at hpr
          cases h1 : removeKeyList s kt key prod.toList <;> rw [h1] at hpr
          · exact absurd hpr (by simp [bind, Except.bind])
          · cases h2 : removeKeyList s kt key st.toList <;> rw [h2] at hpr
            · exact absurd hpr (by simp [bind, Except.bind])
            · simp only [bind, Except.bind, pure, Except.pure,
                Except.ok.injEq] at hpr
              subst hpr
              simp only [hasBarrierK]
              exact ih hp2
        · simp only [hbase, Bool.false_eq_true, if_false, pure, Except.pure,
            Except.ok.injEq] at hpr
          subst hpr
          simp only [hasBarrierK]
          exact ih hp2
  all_goals
    rename_i k₂ ih
    simp only [pruneIterFramesKey, bind, Except.bind] at hpr
    cases hp2 : pruneIterFramesKey s l key k₂ <;> rw [hp2] at hpr
    · exact absurd hpr (by simp)
    · simp only [pure, Except.pure, Except.ok.injEq] at hpr
      subst hpr
      simp only [hasBarrierK]
      exact ih hp2

theorem pruneAll_bar {l : Loc} :
    ∀ {k : Cont}, hasBarrierK (pruneIterFramesAll l k) = hasBarrierK k := by
  intro k
  induction k
  case stop => rfl
  case frame t te r ds k₂ w ih =>
      by_cases hb2 : t = [] ∧ k₂ = .stop ∧ w = false
      · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
        rfl
      · have hne2 : ¬ (t = [] ∧ pruneIterFramesAll l k₂ = .stop ∧ w = false) := by
          intro h
          by_cases hk2 : k₂ = .stop
          · exact hb2 ⟨h.1, hk2, h.2.2⟩
          · exact pruneAll_ne_stop hk2 h.2.1
        show hasBarrierK (.frame t te r ds (pruneIterFramesAll l k₂) w) = _
        rw [hasBarrierK_frame_of_ne hne2, hasBarrierK_frame_of_ne hb2, ih]
  case mapIterK kv vv kt vt b base prod st env₂ k₂ ih =>
      by_cases hbase : base == some l <;>
        simp [pruneIterFramesAll, hasBarrierK, hbase, ih]
  all_goals
    rename_i k₂ ih
    simp only [pruneIterFramesAll, hasBarrierK]
    exact ih

theorem contAfterStmtOp_bar {s : ExecState} {op : StmtOp} {vs : List GoValue}
    {k k₃ : Cont} (h : contAfterStmtOp s op vs k = .ok k₃) :
    hasBarrierK k₃ = hasBarrierK k := by
  unfold contAfterStmtOp at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (injection h with h; rw [← h]; done)
    | (injection h with h; rw [← h]; exact pruneAll_bar)
    | (exact pruneKey_bar h)
    | (exact absurd h (by simp))
    | (cases h; rfl)

end GoLean.Frame
