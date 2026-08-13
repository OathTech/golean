import GoLeanProofs.Frame.Sim

/-!
# The executable frame theorem, module 4: plan-classifier commutation

Every static classifier the machine consults (`assigneeExpr`,
`strictPlan`, `stmtPlan`, `targetSpine`/`targetPlan`/`targetsPlan`,
`chanPlan`, `syncPlan`, `selectOperands`, `evalClauses`,
`completeTargetRef`, `recvStores`, `seqCont`, `contHeadLabel`) commutes
with the address renaming: classifying the renamed syntax yields the
renamed plan, with the SAME shape/op/guard outcome. These are the
per-arm alignment facts for the `stepFn` commutation induction — each
one matches a `match`/guard in the interpreter across the two runs.

Only `seqCont_ren` needs injectivity (its env-splice `if env' = env`
test must transfer in BOTH directions); everything else is plain
structural commutation.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

variable (ρ : Nat → Nat)

/-! ## Local list bridge (the `Rename.lean` `_eq_map` pattern, for the
one carrier it does not cover) -/

private theorem renameKeyedExprList_eq_map (l : List (Int × Expr)) :
    renameKeyedExprList ρ l = l.map (fun p => (p.1, renameExpr ρ p.2)) := by
  induction l with
  | nil => rfl
  | cons p es ih =>
      obtain ⟨k, e⟩ := p
      simp [renameKeyedExprList, ih]

/-! ## Assignment-target classifiers -/

theorem assigneeExpr_ren (a : Assignee) :
    assigneeExpr (renameAssignee ρ a) = (assigneeExpr a).map (renameExpr ρ) := by
  cases a <;> simp [renameAssignee, assigneeExpr, renameExpr]

theorem targetSpine_ren (e : Expr) :
    targetSpine (renameExpr ρ e)
      = ((targetSpine e).1, renameExprList ρ (targetSpine e).2) := by
  fun_induction targetSpine e with
  | case1 b i st ops heq ih =>
      rw [heq] at ih
      simp only [renameExpr, targetSpine]
      simp [ih, renameExprList_append, renameExprList]
  | case2 b tid f st ops heq ih =>
      rw [heq] at ih
      simp only [renameExpr, targetSpine]
      simp [ih]
  | case3 e h1 h2 =>
      cases e <;>
        first
        | exact absurd rfl (h1 _ _)
        | exact absurd rfl (h2 _ _ _)
        | simp [renameExpr, targetSpine, renameExprList]

theorem targetPlan_ren (a : Assignee) :
    targetPlan (renameAssignee ρ a)
      = (targetPlan a).map (fun p => (p.1, renameExprList ρ p.2)) := by
  cases a with
  | var id => simp [renameAssignee, targetPlan, renameExprList, renameExpr]
  | addr e =>
      have hr := targetSpine_ren ρ e
      rcases hsp : targetSpine e with ⟨st, ops⟩
      rw [hsp] at hr
      simp [renameAssignee, targetPlan, hr, hsp]
  | mapElem b k kt vt => simp [renameAssignee, targetPlan, renameExprList]
  | unsupported f => simp [renameAssignee, targetPlan]

/-- `targetsPlan_ren` in the `.map` normal form the statement-side
occurrences actually wear (`renameAssigneeList` unfolds to `List.map`;
`renameStmt`'s array arms produce the map directly). -/
theorem targetsPlan_map_ren (ts : List Assignee) :
    targetsPlan (ts.map (renameAssignee ρ))
      = (targetsPlan ts).map (renamePlans ρ) := by
  induction ts with
  | nil => simp [targetsPlan, renamePlans]
  | cons a rest ih =>
      simp only [targetsPlan, List.map_cons, List.mapM_cons] at ih ⊢
      rw [targetPlan_ren]
      cases targetPlan a with
      | none => rfl
      | some p =>
          rw [ih]
          cases hrest : List.mapM targetPlan rest with
          | none => rfl
          | some tail => simp [renamePlans]

theorem targetsPlan_ren (ts : List Assignee) :
    targetsPlan (renameAssigneeList ρ ts)
      = (targetsPlan ts).map (renamePlans ρ) := by
  simpa [renameAssigneeList] using targetsPlan_map_ren ρ ts

/-! ## Expression and wide-statement classifiers -/

theorem strictPlan_ren (e : Expr) :
    strictPlan (renameExpr ρ e)
      = (strictPlan e).map (fun p => (p.1, renameExprList ρ p.2)) := by
  cases e <;>
    first
    | (simp [strictPlan, renameExpr, renameExprList_eq_map]
       done)
    | skip
  case arrayLit n elem args =>
    simp [strictPlan, renameExpr, renameKeyedExprList_eq_map,
      renameExprList_eq_map, List.map_map, Function.comp_def]
  case slice b lo hi m =>
    cases m <;>
      simp [strictPlan, renameExpr, renameOptExpr, renameExprList]

theorem stmtPlan_ren (s : Stmt) :
    stmtPlan (renameStmt ρ s)
      = (stmtPlan s).map (fun p => (p.1, p.2.1, renameExprList ρ p.2.2)) := by
  cases s <;>
    first
    | (simp [stmtPlan, renameStmt, renameExprList]
       done)
    | skip
  case newValue t v ty =>
    cases t <;>
      simp [stmtPlan, renameStmt, renameAssignee, assigneeExpr,
        renameExprList, renameExpr]
  case makeSlice t elem len cap =>
    cases t <;> cases cap <;>
      simp [stmtPlan, renameStmt, renameAssignee, assigneeExpr,
        renameExprList, renameExpr, renameOptExpr]
  case makeMap t kt vt space =>
    cases t <;> cases space <;>
      simp [stmtPlan, renameStmt, renameAssignee, assigneeExpr,
        renameExprList, renameExpr, renameOptExpr]
  case makeChan t elem cap =>
    cases t <;> cases cap <;>
      simp [stmtPlan, renameStmt, renameAssignee, assigneeExpr,
        renameExprList, renameExpr, renameOptExpr]
  case appendSlice t elem sl els =>
    cases t <;>
      simp [stmtPlan, renameStmt, renameAssignee, assigneeExpr,
        renameExprList, renameExpr]
  case copySlice t dst src =>
    cases t <;>
      simp [stmtPlan, renameStmt, renameAssignee, assigneeExpr,
        renameExprList, renameExpr]

/-! ## Channel and sync classifiers -/

theorem chanPlan_ren (s : Stmt) :
    chanPlan (renameStmt ρ s)
      = (chanPlan s).map (fun p => (renameChanOp ρ p.1, renameExprList ρ p.2)) := by
  cases s <;>
    first
    | (simp [chanPlan, renameStmt, renameChanOp, renameExprList]
       done)
    | skip
  case chanRecv targets ch elem =>
    simp only [renameStmt, chanPlan, List.size_toArray, List.length_map,
      Array.length_toList]
    split
    · rfl
    · rw [targetsPlan_map_ren]
      cases targetsPlan targets.toList <;>
        simp [renameChanOp, renameAssigneeList, renameExprList]

theorem syncPlan_ren (s : Stmt) :
    syncPlan (renameStmt ρ s)
      = (syncPlan s).map (fun p => (renameSyncOp ρ p.1, renameExprList ρ p.2)) := by
  cases s <;>
    first
    | (simp [syncPlan, renameStmt]
       done)
    | skip
  case syncStmt op args targets =>
    cases op <;>
      first
      | (simp only [renameStmt, syncPlan, Array.isEmpty, List.size_toArray,
           List.length_map, Array.length_toList, renameExprList_length]
         split <;> simp [renameSyncOp]
         done)
      | skip
    case onceBegin =>
      simp only [renameStmt, syncPlan, List.size_toArray, List.length_map,
        Array.length_toList, renameExprList_length]
      split
      · rw [targetsPlan_map_ren]
        cases targetsPlan targets.toList <;>
          simp [renameSyncOp, renameAssigneeList]
      · rfl

/-! ## Select classifiers -/

theorem selectOperands_ren (cs : List (SelectClauseHead × Stmt)) :
    selectOperands (renameSelectClauses ρ cs)
      = renameExprList ρ (selectOperands cs) := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
      obtain ⟨h, b⟩ := c
      cases h <;>
        simp [renameSelectClauses, renameSelectHead, selectOperands,
          renameExprList, ih]

/-! ## Store-side classifiers -/

theorem completeTargetRef_ren (sh : TargetShape) (ops : List GoValue) :
    completeTargetRef sh (renameValueList ρ ops)
      = (completeTargetRef sh ops).map (renameTargetRef ρ) := by
  cases sh with
  | chain steps =>
      cases ops with
      | nil => simp [renameValueList, completeTargetRef]
      | cons anchor idxs =>
          simp only [renameValueList, completeTargetRef, renameValueList_length]
          split <;> simp [renameTargetRef]
  | mapElem kt vt =>
      cases ops with
      | nil => simp [renameValueList, completeTargetRef]
      | cons b t =>
          cases t with
          | nil => simp [renameValueList, completeTargetRef]
          | cons k t2 =>
              cases t2 with
              | nil => simp [renameValueList, completeTargetRef, renameTargetRef]
              | cons x t3 => simp [renameValueList, completeTargetRef]

theorem recvStores_ren (v : GoValue) (ok : Bool) (n : Nat) :
    recvStores (renameValue ρ v) ok n = renameValueList ρ (recvStores v ok n) := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

theorem evalClauses_ren {cs : List (SelectClauseHead × Stmt)}
    {vs : List GoValue} {evs : List EvClause}
    (h : evalClauses cs vs = .ok evs) :
    evalClauses (renameSelectClauses ρ cs) (renameValueList ρ vs)
      = .ok (evs.map (renameEvClause ρ)) := by
  induction cs generalizing vs evs with
  | nil =>
      cases vs with
      | nil =>
          simp only [evalClauses, pure_eq_ok, Except.ok.injEq] at h
          subst h
          rfl
      | cons v vs' =>
          simp [evalClauses, stuck, throw, throwThe, MonadExceptOf.throw] at h
  | cons c rest ih =>
      obtain ⟨hd, body⟩ := c
      cases hd with
      | send ch v elem =>
          cases vs with
          | nil =>
              simp [evalClauses, stuck, throw, throwThe, MonadExceptOf.throw] at h
          | cons chv vs' =>
              cases vs' with
              | nil =>
                  simp [evalClauses, stuck, throw, throwThe,
                    MonadExceptOf.throw] at h
              | cons vv vs'' =>
                  simp only [evalClauses, bind_eq_ok, pure_eq_ok,
                    Except.ok.injEq] at h
                  obtain ⟨tail, htail, rfl⟩ := h
                  simp only [renameSelectClauses, renameSelectHead,
                    renameValueList, evalClauses]
                  rw [ih htail]
                  simp [Bind.bind, Except.bind, renameEvClause]
      | recv targets ch elem =>
          cases vs with
          | nil =>
              simp [evalClauses, stuck, throw, throwThe, MonadExceptOf.throw] at h
          | cons chv vs' =>
              simp only [evalClauses] at h
              cases htp : targetsPlan targets.toList with
              | none =>
                  rw [htp] at h
                  simp [throw, throwThe, MonadExceptOf.throw] at h
              | some tps =>
                  rw [htp] at h
                  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
                  obtain ⟨tail, htail, rfl⟩ := h
                  simp only [renameSelectClauses, renameSelectHead,
                    renameValueList, evalClauses, renameAssigneeList,
                    targetsPlan_map_ren, htp, Option.map_some]
                  rw [ih htail]
                  simp [Bind.bind, Except.bind, renameEvClause,
                    renameAssigneeList]

/-! ## Continuation-level classifiers -/

theorem contHeadLabel_ren (k : Cont) :
    contHeadLabel (renameCont ρ k) = contHeadLabel k := by
  cases k <;> rfl

/-- The one lemma needing injectivity: `seqCont`'s env-splice test
(`if env' = env`) must decide the SAME way on renamed environments,
which needs `renameEnv` injective (the too-coarse direction — a
renaming that merged two environments would splice where the canonical
run nests). -/
theorem seqCont_ren {ρ : Nat → Nat}
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (ss : List Stmt) (env : LocalEnv) (k : Cont) :
    seqCont (renameStmtList ρ ss) (renameEnv ρ env) (renameCont ρ k)
      = renameCont ρ (seqCont ss env k) := by
  cases k <;>
    first
    | (simp only [renameCont, seqCont]; done)
    | skip
  case seq rest env' k' =>
    simp only [renameCont, seqCont]
    by_cases h : env' = env
    · subst h
      simp [renameCont, renameStmtList_eq_map]
    · have h' : renameEnv ρ env' ≠ renameEnv ρ env :=
        fun hc => h (renameEnv_inj hinj hc)
      simp [renameCont, h, h']

end GoLean.Frame
