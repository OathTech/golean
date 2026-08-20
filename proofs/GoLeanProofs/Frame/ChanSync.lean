import GoLeanProofs.Frame.MachineRel

/-!
# The executable frame theorem, module 6: channel/sync/select operation
simulation

The concurrency-facing machine operations, commuted across `FrameSim`:
the channel apply (`applyChanOp`), the sync apply (`applySyncOp`), the
select readiness pipeline (`clauseReady`/`readyClauses`), the clause
commit (`commitClause`), and the select apply itself
(`applySelectCore`/`applySelect`), plus the shared receive-target entry
(`enterRecvTargets`).

Panic messages in this cluster are all FIXED strings ("send on closed
channel", "sync: negative WaitGroup counter", …), so panics transfer
verbatim; the mutex/RWMutex misuse `.fatal`s are NON-panic errors and
transfer vacuously (`ExSim.skip`). The multi-ready select's
pre-committed pick list is related pointwise (`SelectOutSim`), and
`applySelect` draws the SAME pick index on both runs because the ready
lists have equal length (`ListSim.length_eq`) and the choice stream is
shared.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

set_option linter.unusedSimpArgs false

section
variable {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σ σF : ExecState}

/-! ## Local rename bridges -/

private theorem renamedArray_push (buf : Array GoValue) (v : GoValue) :
    ((renameValueList ρ buf.toList).toArray).push (renameValue ρ v)
      = (renameValueList ρ (buf.push v).toList).toArray := by
  rw [← Array.toList_inj]
  simp [renameValueList_eq_map]

private theorem renamedArray_eraseIdx!_zero {buf : Array GoValue}
    (h : 0 < buf.size) :
    ((renameValueList ρ buf.toList).toArray).eraseIdx! 0
      = (renameValueList ρ (buf.eraseIdx! 0).toList).toArray := by
  have hF : 0 < ((renameValueList ρ buf.toList).toArray).size := by
    rw [renamedArray_size]; exact h
  unfold Array.eraseIdx!
  rw [dif_pos hF, dif_pos h, ← Array.toList_inj]
  simp [renameValueList_eq_map, List.eraseIdx_zero]

private theorem renameAssigneeList_length (l : List Assignee) :
    (renameAssigneeList ρ l).length = l.length := by
  simp [renameAssigneeList]

private theorem renameStmt_seqn_empty :
    renameStmt ρ (.seqn #[]) = .seqn #[] := by
  simp [renameStmt, renameStmtList]

private theorem renameConfig_panicking_rt (msg : String) (k : Cont) :
    renameConfig ρ (.panicking [⟨runtimeErrorValue msg, false⟩] k)
      = .panicking [⟨runtimeErrorValue msg, false⟩] (renameCont ρ k) := by
  simp [renameConfig, renameChain, renameEntry, runtimeErrorValue_ren]

private theorem renameConfig_panicking_str (msg : String) (k : Cont) :
    renameConfig ρ (.panicking [⟨stringPanicValue msg, false⟩] k)
      = .panicking [⟨stringPanicValue msg, false⟩] (renameCont ρ k) := by
  simp [renameConfig, renameChain, renameEntry, stringPanicValue_ren]

private theorem valueAsInt_sim (v : GoValue) :
    ExSim Eq (valueAsInt v) (valueAsInt (renameValue ρ v)) := by
  cases v with
  | int n k => exact ExSim.ok rfl
  | _ => exact ExSim.stuck'

/-! ## Generic list transfer -/

private theorem listSim_imp {α β : Type} {R S : α → β → Prop}
    (h : ∀ a b, R a b → S a b) :
    ∀ {l : List α} {l' : List β}, ListSim R l l' → ListSim S l l' := by
  intro l l' hl
  induction hl with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (h _ _ hab) ih

/-- Two `mapM`s over pointwise-related index lists (the framed one the
`t`-image of the canonical one) with `ExSim`-related element
computations transfer to `ListSim`-related result lists. -/
private theorem mapM_sim {α β γ δ : Type} {t : α → β} {R : γ → δ → Prop}
    {f : α → Except GoError γ} {g : β → Except GoError δ}
    (hfg : ∀ a, ExSim R (f a) (g (t a))) :
    ∀ l : List α, ExSim (ListSim R) (l.mapM f) ((l.map t).mapM g) := by
  intro l
  induction l with
  | nil => exact ExSim.ok .nil
  | cons a as ih =>
      simp only [List.map_cons, List.mapM_cons]
      refine ExSim.bind (hfg a) ?_
      intro b bF hb
      refine ExSim.bind ih ?_
      intro bs bsF hbs
      exact ExSim.ok (.cons hb hbs)

/-! ## The channel value coercion -/

theorem valueAsChan_sim (v : GoValue) :
    ExSim (fun c cF => cF = { base := c.base.map (renameLoc ρ) })
      (valueAsChan v) (valueAsChan (renameValue ρ v)) := by
  cases v with
  | chan c => exact ExSim.ok rfl
  | _ => exact ExSim.stuck'

/-! ## Receive-target entry -/

theorem enterRecvTargets_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (targets : List Assignee) (vals : List GoValue) (body : Stmt)
    (env : LocalEnv) (k : Cont) :
    ExSim (CfgSim ρ na₀ na fr)
      (enterRecvTargets σ targets vals body env k)
      (enterRecvTargets σF (renameAssigneeList ρ targets)
        (renameValueList ρ vals) (renameStmt ρ body)
        (renameEnv ρ env) (renameCont ρ k)) := by
  simp only [enterRecvTargets, targetsPlan_ren]
  cases targetsPlan targets with
  | none => exact ExSim.stuck'
  | some plans =>
      cases plans with
      | nil => exact ExSim.stuck'
      | cons p rest =>
          obtain ⟨sh, ops⟩ := p
          cases ops with
          | nil => exact ExSim.stuck'
          | cons e ops' => exact ExSim.ok ⟨rfl, hS⟩

/-- `enterRecvTargets_sim` with the framed value list and body given by
EQUATIONS instead of syntactic `rename*` applications — the shape the
call sites (`recvStores` deliveries, the `.seqn #[]` continuation body)
actually wear. -/
private theorem enterRecvTargets_sim' (hS : FrameSim ρ na₀ na fr σ σF)
    {valsF : List GoValue} {bodyF : Stmt}
    (targets : List Assignee) (vals : List GoValue) (body : Stmt)
    (env : LocalEnv) (k : Cont)
    (hvals : valsF = renameValueList ρ vals)
    (hbody : bodyF = renameStmt ρ body) :
    ExSim (CfgSim ρ na₀ na fr)
      (enterRecvTargets σ targets vals body env k)
      (enterRecvTargets σF (renameAssigneeList ρ targets) valsF bodyF
        (renameEnv ρ env) (renameCont ρ k)) := by
  subst hvals hbody
  exact enterRecvTargets_sim hS targets vals body env k

/-! ## The channel apply -/

theorem applyChanOp_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (op : ChanStOp) (vs : List GoValue) (env : LocalEnv) (k : Cont) :
    ExSim (CfgSim ρ na₀ na fr)
      (applyChanOp σ op vs env k)
      (applyChanOp σF (renameChanOp ρ op) (renameValueList ρ vs)
        (renameEnv ρ env) (renameCont ρ k)) := by
  cases op with
  | send elem =>
      cases vs with
      | nil => exact ExSim.stuck'
      | cons chv t =>
          cases t with
          | nil => exact ExSim.stuck'
          | cons vv t2 =>
              cases t2 with
              | cons _ _ => exact ExSim.stuck'
              | nil =>
                  simp only [applyChanOp, renameChanOp, renameValueList]
                  refine ExSim.bind (valueAsChan_sim chv) ?_
                  intro ch chF hch
                  obtain ⟨chb⟩ := ch
                  subst hch
                  refine ExSim.bind (normalizeValueForTy_sim hS.types_eq elem vv) ?_
                  intro v' vF' hv'
                  subst hv'
                  dsimp only
                  cases chb with
                  | none => exact ExSim.ok ⟨rfl, hS⟩
                  | some loc =>
                      refine ExSim.bind (chanCell_sim hS loc) ?_
                      intro c cF hc
                      obtain ⟨buf, capacity, closed⟩ := c
                      subst hc
                      dsimp only
                      by_cases hcl : closed = true
                      · simp only [if_pos hcl]
                        exact ExSim.ok ⟨(renameConfig_panicking_rt _ _).symm, hS⟩
                      · simp only [if_neg hcl]
                        rw [renamedArray_size]
                        by_cases hsz : buf.size < capacity
                        · simp only [if_pos hsz]
                          rw [renamedArray_push]
                          refine ExSim.bind (storeLoc_sim hS loc _) ?_
                          intro σ' σF' hS'
                          exact ExSim.ok ⟨rfl, hS'⟩
                        · simp only [if_neg hsz]
                          exact ExSim.ok ⟨rfl, hS⟩
  | recv targets elem =>
      cases vs with
      | nil => exact ExSim.stuck'
      | cons chv t =>
          cases t with
          | cons _ _ => exact ExSim.stuck'
          | nil =>
              simp only [applyChanOp, renameChanOp, renameValueList]
              refine ExSim.bind (valueAsChan_sim chv) ?_
              intro ch chF hch
              obtain ⟨chb⟩ := ch
              subst hch
              dsimp only
              cases chb with
              | none => exact ExSim.ok ⟨rfl, hS⟩
              | some loc =>
                  refine ExSim.bind (chanCell_sim hS loc) ?_
                  intro c cF hc
                  obtain ⟨buf, capacity, closed⟩ := c
                  subst hc
                  dsimp only
                  rw [renamedArray_getElem?]
                  cases hv0 : buf[0]? with
                  | some v =>
                      simp only [Option.map_some]
                      obtain ⟨hpos, -⟩ := Array.getElem?_eq_some_iff.mp hv0
                      rw [renamedArray_eraseIdx!_zero hpos]
                      refine ExSim.bind (storeLoc_sim hS loc _) ?_
                      intro σ₁ σF₁ hS₁
                      cases targets with
                      | nil => exact ExSim.ok ⟨rfl, hS₁⟩
                      | cons a ts =>
                          exact enterRecvTargets_sim' hS₁ (a :: ts)
                            (recvStores v true (a :: ts).length) (.seqn #[])
                            env k
                            (by rw [recvStores_ren, renameAssigneeList_length])
                            renameStmt_seqn_empty.symm
                  | none =>
                      simp only [Option.map_none]
                      by_cases hcl : closed = true
                      · simp only [if_pos hcl]
                        refine ExSim.bind (defaultValue_sim (ρ := ρ)
                          hS.types_eq elem) ?_
                        intro z zF hz
                        subst hz
                        cases targets with
                        | nil => exact ExSim.ok ⟨rfl, hS⟩
                        | cons a ts =>
                            exact enterRecvTargets_sim' hS (a :: ts)
                              (recvStores z false (a :: ts).length) (.seqn #[])
                              env k
                              (by rw [recvStores_ren, renameAssigneeList_length])
                              renameStmt_seqn_empty.symm
                      · simp only [if_neg hcl]
                        exact ExSim.ok ⟨rfl, hS⟩
  | close =>
      cases vs with
      | nil => exact ExSim.stuck'
      | cons chv t =>
          cases t with
          | cons _ _ => exact ExSim.stuck'
          | nil =>
              simp only [applyChanOp, renameChanOp, renameValueList]
              refine ExSim.bind (valueAsChan_sim chv) ?_
              intro ch chF hch
              obtain ⟨chb⟩ := ch
              subst hch
              dsimp only
              cases chb with
              | none => exact ExSim.ok ⟨(renameConfig_panicking_rt _ _).symm, hS⟩
              | some loc =>
                  refine ExSim.bind (chanCell_sim hS loc) ?_
                  intro c cF hc
                  obtain ⟨buf, capacity, closed⟩ := c
                  subst hc
                  dsimp only
                  by_cases hcl : closed = true
                  · simp only [if_pos hcl]
                    exact ExSim.ok ⟨(renameConfig_panicking_rt _ _).symm, hS⟩
                  · simp only [if_neg hcl]
                    refine ExSim.bind (storeLoc_sim hS loc _) ?_
                    intro σ' σF' hS'
                    exact ExSim.ok ⟨rfl, hS'⟩

/-! ## The sync apply -/

theorem applySyncOp_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (op : SyncOp) (vs : List GoValue) (env : LocalEnv) (k : Cont) :
    ExSim (CfgSim ρ na₀ na fr)
      (applySyncOp σ op vs env k)
      (applySyncOp σF (renameSyncOp ρ op) (renameValueList ρ vs)
        (renameEnv ρ env) (renameCont ρ k)) := by
  cases op with
  | lock =>
      cases vs with
      | nil => exact ExSim.stuck'
      | cons av t =>
          cases t with
          | cons _ _ => exact ExSim.stuck'
          | nil =>
              simp only [applySyncOp, renameSyncOp, renameValueList]
              refine ExSim.bind (valueAsLoc_sim ρ av) ?_
              intro loc locF hloc
              subst hloc
              refine ExSim.bind (syncCell_sim hS loc) ?_
              intro p pF hp
              subst hp
              cases p with
              | mutex locked =>
                  by_cases hl : locked = true
                  · simp only [if_pos hl]
                    exact ExSim.ok ⟨rfl, hS⟩
                  · simp only [if_neg hl]
                    refine ExSim.bind (storeLoc_sim hS loc _) ?_
                    intro σ' σF' hS'
                    exact ExSim.ok ⟨rfl, hS'⟩
              | _ => exact ExSim.stuck'
  | unlock =>
      cases vs with
      | nil => exact ExSim.stuck'
      | cons av t =>
          cases t with
          | cons _ _ => exact ExSim.stuck'
          | nil =>
              simp only [applySyncOp, renameSyncOp, renameValueList]
              refine ExSim.bind (valueAsLoc_sim ρ av) ?_
              intro loc locF hloc
              subst hloc
              refine ExSim.bind (syncCell_sim hS loc) ?_
              intro p pF hp
              subst hp
              cases p with
              | mutex locked =>
                  by_cases hl : locked = true
                  · simp only [if_pos hl]
                    refine ExSim.bind (storeLoc_sim hS loc _) ?_
                    intro σ' σF' hS'
                    exact ExSim.ok ⟨rfl, hS'⟩
                  · simp only [if_neg hl]
                    exact ExSim.skip fun _ h => GoError.noConfusion h
              | _ => exact ExSim.stuck'
  | rlock =>
      cases vs with
      | nil => exact ExSim.stuck'
      | cons av t =>
          cases t with
          | cons _ _ => exact ExSim.stuck'
          | nil =>
              simp only [applySyncOp, renameSyncOp, renameValueList]
              refine ExSim.bind (valueAsLoc_sim ρ av) ?_
              intro loc locF hloc
              subst hloc
              refine ExSim.bind (syncCell_sim hS loc) ?_
              intro p pF hp
              subst hp
              cases p with
              | rwmutex writer readers pendingW =>
                  by_cases hc : (writer || pendingW > 0) = true
                  · simp only [if_pos hc]
                    exact ExSim.ok ⟨rfl, hS⟩
                  · simp only [if_neg hc]
                    refine ExSim.bind (storeLoc_sim hS loc _) ?_
                    intro σ' σF' hS'
                    exact ExSim.ok ⟨rfl, hS'⟩
              | _ => exact ExSim.stuck'
  | runlock =>
      cases vs with
      | nil => exact ExSim.stuck'
      | cons av t =>
          cases t with
          | cons _ _ => exact ExSim.stuck'
          | nil =>
              simp only [applySyncOp, renameSyncOp, renameValueList]
              refine ExSim.bind (valueAsLoc_sim ρ av) ?_
              intro loc locF hloc
              subst hloc
              refine ExSim.bind (syncCell_sim hS loc) ?_
              intro p pF hp
              subst hp
              cases p with
              | rwmutex writer readers pendingW =>
                  cases readers with
                  | zero => exact ExSim.skip fun _ h => GoError.noConfusion h
                  | succ r =>
                      refine ExSim.bind (storeLoc_sim hS loc _) ?_
                      intro σ' σF' hS'
                      exact ExSim.ok ⟨rfl, hS'⟩
              | _ => exact ExSim.stuck'
  | wlock =>
      cases vs with
      | nil => exact ExSim.stuck'
      | cons av t =>
          cases t with
          | cons _ _ => exact ExSim.stuck'
          | nil =>
              simp only [applySyncOp, renameSyncOp, renameValueList]
              refine ExSim.bind (valueAsLoc_sim ρ av) ?_
              intro loc locF hloc
              subst hloc
              refine ExSim.bind (syncCell_sim hS loc) ?_
              intro p pF hp
              subst hp
              cases p with
              | rwmutex writer readers pendingW =>
                  by_cases hc : (!writer && readers == 0) = true
                  · simp only [if_pos hc]
                    refine ExSim.bind (storeLoc_sim hS loc _) ?_
                    intro σ' σF' hS'
                    exact ExSim.ok ⟨rfl, hS'⟩
                  · simp only [if_neg hc]
                    refine ExSim.bind (storeLoc_sim hS loc _) ?_
                    intro σ' σF' hS'
                    exact ExSim.ok ⟨rfl, hS'⟩
              | _ => exact ExSim.stuck'
  | wunlock =>
      cases vs with
      | nil => exact ExSim.stuck'
      | cons av t =>
          cases t with
          | cons _ _ => exact ExSim.stuck'
          | nil =>
              simp only [applySyncOp, renameSyncOp, renameValueList]
              refine ExSim.bind (valueAsLoc_sim ρ av) ?_
              intro loc locF hloc
              subst hloc
              refine ExSim.bind (syncCell_sim hS loc) ?_
              intro p pF hp
              subst hp
              cases p with
              | rwmutex writer readers pendingW =>
                  by_cases hw : writer = true
                  · simp only [if_pos hw]
                    refine ExSim.bind (storeLoc_sim hS loc _) ?_
                    intro σ' σF' hS'
                    exact ExSim.ok ⟨rfl, hS'⟩
                  · simp only [if_neg hw]
                    exact ExSim.skip fun _ h => GoError.noConfusion h
              | _ => exact ExSim.stuck'
  | wgAdd =>
      cases vs with
      | nil => exact ExSim.stuck'
      | cons av t =>
          cases t with
          | nil => exact ExSim.stuck'
          | cons dv t2 =>
              cases t2 with
              | cons _ _ => exact ExSim.stuck'
              | nil =>
                  simp only [applySyncOp, renameSyncOp, renameValueList]
                  refine ExSim.bind (valueAsLoc_sim ρ av) ?_
                  intro loc locF hloc
                  subst hloc
                  refine ExSim.bind (valueAsInt_sim dv) ?_
                  intro d dF hd
                  subst hd
                  refine ExSim.bind (syncCell_sim hS loc) ?_
                  intro p pF hp
                  subst hp
                  cases p with
                  | waitGroup counter waiters =>
                      refine ExSim.bind (storeLoc_sim hS loc _) ?_
                      intro σ' σF' hS'
                      by_cases hneg :
                        (counter + d + 2147483648).emod 4294967296 - 2147483648 < 0
                      · simp only [if_pos hneg]
                        exact ExSim.ok ⟨(renameConfig_panicking_str _ _).symm, hS'⟩
                      · simp only [if_neg hneg]
                        exact ExSim.ok ⟨rfl, hS'⟩
                  | _ => exact ExSim.stuck'
  | wgWait =>
      cases vs with
      | nil => exact ExSim.stuck'
      | cons av t =>
          cases t with
          | cons _ _ => exact ExSim.stuck'
          | nil =>
              simp only [applySyncOp, renameSyncOp, renameValueList]
              refine ExSim.bind (valueAsLoc_sim ρ av) ?_
              intro loc locF hloc
              subst hloc
              refine ExSim.bind (syncCell_sim hS loc) ?_
              intro p pF hp
              subst hp
              cases p with
              | waitGroup counter waiters =>
                  by_cases hz : (counter == 0) = true
                  · simp only [if_pos hz]
                    exact ExSim.ok ⟨rfl, hS⟩
                  · simp only [if_neg hz]
                    refine ExSim.bind (storeLoc_sim hS loc _) ?_
                    intro σ' σF' hS'
                    exact ExSim.ok ⟨rfl, hS'⟩
              | _ => exact ExSim.stuck'
  | onceBegin targets =>
      cases vs with
      | nil => exact ExSim.stuck'
      | cons av t =>
          cases t with
          | cons _ _ => exact ExSim.stuck'
          | nil =>
              simp only [applySyncOp, renameSyncOp, renameValueList]
              refine ExSim.bind (valueAsLoc_sim ρ av) ?_
              intro loc locF hloc
              subst hloc
              refine ExSim.bind (syncCell_sim hS loc) ?_
              intro p pF hp
              subst hp
              cases p with
              | once started dn =>
                  by_cases hst : (!started) = true
                  · simp only [if_pos hst]
                    refine ExSim.bind (storeLoc_sim hS loc _) ?_
                    intro σ' σF' hS'
                    exact enterRecvTargets_sim' hS' targets [.bool true]
                      (.seqn #[]) env k (by simp [renameValueList, renameValue])
                      renameStmt_seqn_empty.symm
                  · simp only [if_neg hst]
                    by_cases hdn : dn = true
                    · simp only [if_pos hdn]
                      exact enterRecvTargets_sim' hS targets [.bool false]
                        (.seqn #[]) env k (by simp [renameValueList, renameValue])
                        renameStmt_seqn_empty.symm
                    · simp only [if_neg hdn]
                      exact ExSim.ok ⟨rfl, hS⟩
              | _ => exact ExSim.stuck'
  | onceComplete =>
      cases vs with
      | nil => exact ExSim.stuck'
      | cons av t =>
          cases t with
          | cons _ _ => exact ExSim.stuck'
          | nil =>
              simp only [applySyncOp, renameSyncOp, renameValueList]
              refine ExSim.bind (valueAsLoc_sim ρ av) ?_
              intro loc locF hloc
              subst hloc
              refine ExSim.bind (syncCell_sim hS loc) ?_
              intro p pF hp
              subst hp
              cases p with
              | once started dn =>
                  by_cases hst : started = true
                  · simp only [if_pos hst]
                    refine ExSim.bind (storeLoc_sim hS loc _) ?_
                    intro σ' σF' hS'
                    exact ExSim.ok ⟨rfl, hS'⟩
                  · simp only [if_neg hst]
                    exact ExSim.internal'
              | _ => exact ExSim.stuck'

/-! ## Select readiness -/

theorem clauseReady_sim (hS : FrameSim ρ na₀ na fr σ σF) (c : EvClause) :
    ExSim Eq (clauseReady σ c) (clauseReady σF (renameEvClause ρ c)) := by
  cases c with
  | sendEv chv v elem body =>
      simp only [clauseReady, renameEvClause]
      refine ExSim.bind (valueAsChan_sim chv) ?_
      intro ch chF hch
      obtain ⟨chb⟩ := ch
      subst hch
      dsimp only
      cases chb with
      | none => exact ExSim.ok rfl
      | some loc =>
          refine ExSim.bind (chanCell_sim hS loc) ?_
          intro cc ccF hcc
          obtain ⟨buf, capacity, closed⟩ := cc
          subst hcc
          dsimp only
          rw [renamedArray_size]
          exact ExSim.ok rfl
  | recvEv chv targets elem body =>
      simp only [clauseReady, renameEvClause]
      refine ExSim.bind (valueAsChan_sim chv) ?_
      intro ch chF hch
      obtain ⟨chb⟩ := ch
      subst hch
      dsimp only
      cases chb with
      | none => exact ExSim.ok rfl
      | some loc =>
          refine ExSim.bind (chanCell_sim hS loc) ?_
          intro cc ccF hcc
          obtain ⟨buf, capacity, closed⟩ := cc
          subst hcc
          dsimp only
          rw [renamedArray_size]
          exact ExSim.ok rfl

theorem readyClauses_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (cs : List EvClause) :
    ExSim (fun l lF => lF = l.map (renameEvClause ρ))
      (readyClauses σ cs) (readyClauses σF (cs.map (renameEvClause ρ))) := by
  induction cs with
  | nil => exact ExSim.ok rfl
  | cons c rest ih =>
      simp only [List.map_cons, readyClauses]
      refine ExSim.bind ih ?_
      intro tail tailF htail
      subst htail
      refine ExSim.bind (clauseReady_sim hS c) ?_
      intro b bF hb
      subst hb
      by_cases hbt : b = true
      · simp only [if_pos hbt]
        exact ExSim.ok rfl
      · simp only [if_neg hbt]
        exact ExSim.ok rfl

/-! ## The clause commit -/

theorem commitClause_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (env : LocalEnv) (k : Cont) (c : EvClause) :
    ExSim (CfgSim ρ na₀ na fr)
      (commitClause σ env k c)
      (commitClause σF (renameEnv ρ env) (renameCont ρ k)
        (renameEvClause ρ c)) := by
  cases c with
  | sendEv chv vv elem body =>
      simp only [commitClause, renameEvClause]
      refine ExSim.bind (valueAsChan_sim chv) ?_
      intro ch chF hch
      obtain ⟨chb⟩ := ch
      subst hch
      dsimp only
      cases chb with
      | none => exact ExSim.stuck'
      | some loc =>
          refine ExSim.bind (chanCell_sim hS loc) ?_
          intro cc ccF hcc
          obtain ⟨buf, capacity, closed⟩ := cc
          subst hcc
          dsimp only
          by_cases hcl : closed = true
          · simp only [if_pos hcl]
            exact ExSim.ok ⟨(renameConfig_panicking_rt _ _).symm, hS⟩
          · simp only [if_neg hcl]
            rw [renamedArray_size]
            by_cases hsz : buf.size < capacity
            · simp only [if_pos hsz]
              refine ExSim.bind (normalizeValueForTy_sim hS.types_eq elem vv) ?_
              intro v' vF' hv'
              subst hv'
              rw [renamedArray_push]
              refine ExSim.bind (storeLoc_sim hS loc _) ?_
              intro σ' σF' hS'
              exact ExSim.ok ⟨rfl, hS'⟩
            · simp only [if_neg hsz]
              exact ExSim.stuck'
  | recvEv chv targets elem body =>
      simp only [commitClause, renameEvClause]
      refine ExSim.bind (valueAsChan_sim chv) ?_
      intro ch chF hch
      obtain ⟨chb⟩ := ch
      subst hch
      dsimp only
      cases chb with
      | none => exact ExSim.stuck'
      | some loc =>
          refine ExSim.bind (chanCell_sim hS loc) ?_
          intro cc ccF hcc
          obtain ⟨buf, capacity, closed⟩ := cc
          subst hcc
          dsimp only
          rw [renamedArray_getElem?]
          cases hv0 : buf[0]? with
          | some v =>
              simp only [Option.map_some]
              obtain ⟨hpos, -⟩ := Array.getElem?_eq_some_iff.mp hv0
              rw [renamedArray_eraseIdx!_zero hpos]
              refine ExSim.bind (storeLoc_sim hS loc _) ?_
              intro σ₁ σF₁ hS₁
              simp only [pure_bind]
              cases targets with
              | nil => exact ExSim.ok ⟨rfl, hS₁⟩
              | cons a ts =>
                  exact enterRecvTargets_sim' hS₁ (a :: ts)
                    (recvStores v true (a :: ts).length) body env k
                    (by rw [recvStores_ren, renameAssigneeList_length]) rfl
          | none =>
              simp only [Option.map_none]
              by_cases hcl : closed = true
              · simp only [if_pos hcl]
                refine ExSim.bind (defaultValue_sim (ρ := ρ)
                  hS.types_eq elem) ?_
                intro z zF hz
                subst hz
                simp only [pure_bind]
                cases targets with
                | nil => exact ExSim.ok ⟨rfl, hS⟩
                | cons a ts =>
                    exact enterRecvTargets_sim' hS (a :: ts)
                      (recvStores z false (a :: ts).length) body env k
                      (by rw [recvStores_ren, renameAssigneeList_length]) rfl
              · simp only [if_neg hcl]
                exact ExSim.stuck'

/-! ## The select apply -/

-- The SelectOutcome relation: done-config renamed + FrameSim, or the
-- pre-committed pick lists pointwise related (inl: CfgSim; inr: same
-- panic message).
def SelectOutSim (ρ : Nat → Nat) (na₀ na : Nat) (fr : Heap) :
    SelectOutcome → SelectOutcome → Prop
  | .done c s, .done cF sF => cF = renameConfig ρ c ∧ FrameSim ρ na₀ na fr s sF
  | .picks l, .picks lF =>
      ListSim (fun x xF =>
        match x, xF with
        | .inl r, .inl rF => CfgSim ρ na₀ na fr r rF
        | .inr m, .inr mF => mF = m
        | _, _ => False) l lF
  | _, _ => False

/-- The pointwise relation of `SelectOutSim`'s `.picks` arm, named so
the `mapM` induction and the `applySelect` pick-transfer can traverse
it without restating the match. -/
private def PickRel (ρ : Nat → Nat) (na₀ na : Nat) (fr : Heap) :
    Sum (Config × ExecState) String → Sum (Config × ExecState) String → Prop
  | .inl r, .inl rF => CfgSim ρ na₀ na fr r rF
  | .inr m, .inr mF => mF = m
  | _, _ => False

private theorem selectOutSim_of_picks
    {l lF : List (Sum (Config × ExecState) String)}
    (h : ListSim (PickRel ρ na₀ na fr) l lF) :
    SelectOutSim ρ na₀ na fr (.picks l) (.picks lF) :=
  listSim_imp (fun a b hab => by cases a <;> cases b <;> exact hab) h

private theorem selectOutSim_picks
    {l lF : List (Sum (Config × ExecState) String)}
    (h : SelectOutSim ρ na₀ na fr (.picks l) (.picks lF)) :
    ListSim (PickRel ρ na₀ na fr) l lF :=
  listSim_imp (fun a b hab => by cases a <;> cases b <;> exact hab) h

/-- `evalClauses` never panics: its failures are `stuck` (operand-arity
drift) and `unsupported` (receive-target assignees), both vacuous under
`ExSim`. -/
private theorem evalClauses_noPanic :
    ∀ (cs : List (SelectClauseHead × Stmt)) (vs : List GoValue),
      NoPanic (evalClauses cs vs) := by
  intro cs
  induction cs with
  | nil =>
      intro vs
      cases vs with
      | nil => exact NoPanic.pure'
      | cons v vs' => exact NoPanic.stuck'
  | cons c rest ih =>
      obtain ⟨hd, body⟩ := c
      intro vs
      cases hd with
      | send ch v elem =>
          cases vs with
          | nil => exact NoPanic.stuck'
          | cons chv vs' =>
              cases vs' with
              | nil => exact NoPanic.stuck'
              | cons vv vs'' =>
                  simp only [evalClauses]
                  exact NoPanic.bind (ih vs'') fun _ => NoPanic.pure'
      | recv targets ch elem =>
          cases vs with
          | nil => exact NoPanic.stuck'
          | cons chv vs' =>
              simp only [evalClauses]
              cases targetsPlan targets.toList with
              | some tp => exact NoPanic.bind (ih vs') fun _ => NoPanic.pure'
              | none => exact NoPanic.unsupported'

theorem applySelectCore_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (clauses : List (SelectClauseHead × Stmt)) (default? : Option Stmt)
    (vs : List GoValue) (env : LocalEnv) (k : Cont) :
    ExSim (SelectOutSim ρ na₀ na fr)
      (applySelectCore σ clauses default? vs env k)
      (applySelectCore σF (renameSelectClauses ρ clauses)
        (renameOptStmt ρ default?) (renameValueList ρ vs)
        (renameEnv ρ env) (renameCont ρ k)) := by
  simp only [applySelectCore]
  refine ExSim.bind (exSim_of_ren (evalClauses_noPanic clauses vs)
    (fun evs h => evalClauses_ren ρ h)) ?_
  intro evs evsF hevs
  subst hevs
  refine ExSim.bind (readyClauses_sim hS evs) ?_
  intro r rF hr
  subst hr
  cases r with
  | nil =>
      cases default? with
      | some d => exact ExSim.ok ⟨rfl, hS⟩
      | none => exact ExSim.ok ⟨rfl, hS⟩
  | cons c₁ rest =>
      cases rest with
      | nil =>
          refine ExSim.bind (commitClause_sim hS env k c₁) ?_
          intro p pF hp
          have hp' : pF.1 = renameConfig ρ p.1
              ∧ FrameSim ρ na₀ na fr p.2 pF.2 := hp
          obtain ⟨c', s'⟩ := p
          obtain ⟨cF', sF'⟩ := pF
          exact ExSim.ok ⟨hp'.1, hp'.2⟩
      | cons c₂ rest₂ =>
          refine ExSim.bind
            (mapM_sim (t := renameEvClause ρ) (R := PickRel ρ na₀ na fr)
              ?_ (c₁ :: c₂ :: rest₂)) ?_
          · intro cl
            have hcc := commitClause_sim hS env k cl
            cases hc : commitClause σ env k cl with
            | ok r =>
                obtain ⟨rr, hrF, hrel⟩ := hcc.ok_inv hc
                rw [hrF]
                exact ExSim.ok hrel
            | error e =>
                cases e with
                | panic msg =>
                    rw [hcc.panic_inv hc]
                    exact ExSim.ok rfl
                | _ => exact ExSim.skip fun _ h => GoError.noConfusion h
          · intro l lF hl
            exact ExSim.ok (selectOutSim_of_picks hl)

theorem applySelect_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (clauses : List (SelectClauseHead × Stmt)) (default? : Option Stmt)
    (vs : List GoValue) (env : LocalEnv) (k : Cont) (ch : Choices) :
    ExSim (fun (r rF : Config × ExecState × Choices) =>
        rF.1 = renameConfig ρ r.1 ∧ FrameSim ρ na₀ na fr r.2.1 rF.2.1
          ∧ rF.2.2 = r.2.2)
      (applySelect σ clauses default? vs env k ch)
      (applySelect σF (renameSelectClauses ρ clauses)
        (renameOptStmt ρ default?) (renameValueList ρ vs)
        (renameEnv ρ env) (renameCont ρ k) ch) := by
  simp only [applySelect]
  refine ExSim.bind (applySelectCore_sim hS clauses default? vs env k) ?_
  intro o oF ho
  cases o with
  | done c' s' =>
      cases oF with
      | done cF' sF' =>
          have hd : cF' = renameConfig ρ c'
              ∧ FrameSim ρ na₀ na fr s' sF' := ho
          exact ExSim.ok ⟨hd.1, hd.2, rfl⟩
      | picks _ => exact False.elim ho
  | picks commits =>
      cases oF with
      | done _ _ => exact False.elim ho
      | picks commitsF =>
          have hls := selectOutSim_picks ho
          have hlen : commits.length = commitsF.length := hls.length_eq
          dsimp only
          simp only [Choices.consumeAt_l2Entry]
          rw [← hlen]
          rcases hls.getElem? (ch.consume commits.length).fst with
            ⟨h1, h2⟩ | ⟨a, b, ha, hb, hab⟩
          · rw [h1, h2]
            exact ExSim.internal'
          · rw [ha, hb]
            cases a with
            | inl r =>
                cases b with
                | inl rF =>
                    have hr : rF.1 = renameConfig ρ r.1
                        ∧ FrameSim ρ na₀ na fr r.2 rF.2 := hab
                    obtain ⟨c', s'⟩ := r
                    obtain ⟨cF', sF'⟩ := rF
                    exact ExSim.ok ⟨hr.1, hr.2, rfl⟩
                | inr m => exact False.elim hab
            | inr m =>
                cases b with
                | inl rF => exact False.elim hab
                | inr mF =>
                    have hm : mF = m := hab
                    subst hm
                    exact ExSim.ok
                      ⟨(renameConfig_panicking_rt _ _).symm, hS, rfl⟩

end

end GoLean.Frame
