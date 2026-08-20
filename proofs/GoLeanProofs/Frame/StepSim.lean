import GoLeanProofs.Frame.PanicFrame
import GoLeanProofs.Frame.ChanSync
import GoLeanProofs.Frame.StmtOps
import GoLeanProofs.Frame.Ops2

/-!
# The executable frame theorem: the per-step simulation (in progress)
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

theorem valueAsBool_sim (ρ : Nat → Nat) (v : GoValue) :
    ExSim Eq (valueAsBool v) (valueAsBool (renameValue ρ v)) := by
  cases v
  case bool b => exact ExSim.ok rfl
  all_goals exact ExSim.stuck'

private theorem renameStmt_seqn_empty (ρ : Nat → Nat) :
    renameStmt ρ (.seqn #[]) = .seqn #[] := by
  simp [renameStmt, renameStmtList]

private theorem renameEnv_nil (ρ : Nat → Nat) : renameEnv ρ ([] : LocalEnv) = [] := rfl
private theorem renameChain_nil (ρ : Nat → Nat) : renameChain ρ [] = [] := rfl
private theorem renameChain_cons (ρ : Nat → Nat) (e : PanicEntry)
    (es : List PanicEntry) :
    renameChain ρ (e :: es) = renameEntry ρ e :: renameChain ρ es := rfl
private theorem renameDefers_nil (ρ : Nat → Nat) : renameDefers ρ [] = [] := rfl
private theorem renameDefers_cons (ρ : Nat → Nat) (d : GoValue × List GoValue)
    (ds : List (GoValue × List GoValue)) :
    renameDefers ρ (d :: ds) = renameDefer ρ d :: renameDefers ρ ds := rfl
private theorem renamePlans_nil (ρ : Nat → Nat) : renamePlans ρ [] = [] := rfl
private theorem renamePlans_cons (ρ : Nat → Nat) (p : TargetShape × List Expr)
    (ps : List (TargetShape × List Expr)) :
    renamePlans ρ (p :: ps) = (p.1, renameExprList ρ p.2) :: renamePlans ρ ps := rfl
private theorem renameAssigneeList_nil (ρ : Nat → Nat) :
    renameAssigneeList ρ [] = [] := rfl
private theorem renameAssigneeList_cons (ρ : Nat → Nat) (a : Assignee)
    (as' : List Assignee) :
    renameAssigneeList ρ (a :: as') = renameAssignee ρ a :: renameAssigneeList ρ as' := rfl

private theorem list_eraseIdx_map {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : Nat), (l.map f).eraseIdx i = (l.eraseIdx i).map f := by
  intro l
  induction l with
  | nil => intro i; simp
  | cons a as ih =>
      intro i
      cases i with
      | zero => simp
      | succ j => simp [List.eraseIdx_cons_succ, ih]

private theorem renameValueList_snoc (ρ : Nat → Nat) (l : List GoValue)
    (v : GoValue) :
    renameValueList ρ (l ++ [v]) = renameValueList ρ l ++ [renameValue ρ v] := by
  simp [renameValueList_eq_map]

private theorem renEntriesArr_size (ρ : Nat → Nat)
    (es : Array (GoValue × GoValue)) :
    ((renameValueEntries ρ es.toList).toArray).size = es.size := by
  simp [renameValueEntries_eq_map]

private theorem renEntriesArr_isEmpty (ρ : Nat → Nat)
    (es : Array (GoValue × GoValue)) :
    ((renameValueEntries ρ es.toList).toArray).isEmpty = es.isEmpty := by
  unfold Array.isEmpty
  rw [renEntriesArr_size]

private theorem renEntriesArr_getElem? (ρ : Nat → Nat)
    (es : Array (GoValue × GoValue)) (i : Nat) :
    ((renameValueEntries ρ es.toList).toArray)[i]?
      = (es[i]?).map (fun p => (renameValue ρ p.1, renameValue ρ p.2)) := by
  simp [renameValueEntries_eq_map, ← Array.getElem?_toList,
    List.getElem?_map]

private theorem targetsPlan_pair_ren {ρ : Nat → Nat} (a b : Assignee) :
    targetsPlan [renameAssignee ρ a, renameAssignee ρ b]
      = (targetsPlan [a, b]).map (renamePlans ρ) := by
  have := targetsPlan_ren ρ [a, b]
  simpa [renameAssigneeList] using this

/-! ### Entry-arm reduction lemmas (the catch-all scrutinee arms)

The wide-statement / strict-expression entry arms of `stepFn` sit under
a CATCH-ALL match scrutinee, so the framed run's `stepFn` cannot reduce
while the renamed statement/expression is abstract. Each lemma below
pays the per-constructor case bash ONCE, outside the induction, keyed
on the plan fact — the induction then rewrites with the renamed plan
(`stmtPlan_ren`/`strictPlan_ren`/`chanPlan_ren`/`syncPlan_ren`) and
never re-cases the syntax. -/

/-- The wide-statement entry result, keyed on the plan components (a
plain function of the plan, so the lemma below is a non-dependent
rewrite). -/
private def wideEntry (σ₀ : ExecState) (op : StmtOp) (nt : Nat)
    (es : List Expr) (env : LocalEnv) (k : Cont) (ch : Choices) :
    Except GoError (Config × ExecState × Choices) :=
  match es with
  | e :: rest => pure (.evalE e env (.stmtOpK op nt [] rest env k), σ₀, ch)
  | [] => do
      let (s', choices') ← applyStmtOp σ₀ ch op nt []
      pure (.next k, s', choices')

private theorem stepFn_exec_wide {σ₀ : ExecState} {s : Stmt} {env : LocalEnv}
    {k : Cont} {ch : Choices} {op : StmtOp} {nt : Nat} {es : List Expr}
    (hplan : stmtPlan s = some (op, nt, es)) :
    stepFn σ₀ (.exec s env k) ch = wideEntry σ₀ op nt es env k ch := by
  cases s <;>
    first
      | (simp [stmtPlan] at hplan; done)
      | (simp only [stepFn.eq_def]
         rw [hplan]
         cases es <;> rfl)

/-- The strict-expression entry result (same shape). -/
private def strictEntry (σ₀ : ExecState) (op : StrictOp) (es : List Expr)
    (env : LocalEnv) (k : Cont) (ch : Choices) :
    Except GoError (Config × ExecState × Choices) :=
  match es with
  | e₁ :: rest => pure (.evalE e₁ env (.strictK op [] rest env k), σ₀, ch)
  | [] =>
      match applyStrictOp σ₀ op [] with
      | .ok (v, s') => pure (.retV v k, s', ch)
      | .error (.panic msg) =>
          pure (.panicking [⟨runtimeErrorValue msg, false⟩] k, σ₀, ch)
      | .error err => throw err

private theorem stepFn_evalE_strict {σ₀ : ExecState} {e : Expr}
    {env : LocalEnv} {k : Cont} {ch : Choices} {op : StrictOp}
    {es : List Expr}
    (hplan : strictPlan e = some (op, es)) :
    stepFn σ₀ (.evalE e env k) ch = strictEntry σ₀ op es env k ch := by
  cases e <;>
    first
      | (simp [strictPlan] at hplan; done)
      | (simp only [stepFn.eq_def]
         rw [hplan]
         cases es <;> rfl)

private theorem stepFn_exec_chanRecv {σ₀ : ExecState}
    {targets : Array Assignee} {chE : Expr} {elem : Ty} {env : LocalEnv}
    {k : Cont} {ch : Choices} {op : ChanStOp} {e : Expr} {rest : List Expr}
    (hplan : chanPlan (.chanRecv targets chE elem) = some (op, e :: rest)) :
    stepFn σ₀ (.exec (.chanRecv targets chE elem) env k) ch
      = pure (.evalE e env (.chanStK op [] rest env k), σ₀, ch) := by
  simp only [stepFn.eq_def]
  split
  · rename_i op' e' rest' heq
    rw [hplan] at heq
    simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at heq
    obtain ⟨hop, he, hrest⟩ := heq
    subst hop; subst he; subst hrest
    rfl
  · rename_i heq
    rw [hplan] at heq
    simp at heq
  · rename_i heq
    rw [hplan] at heq
    simp at heq

private theorem stepFn_exec_sync {σ₀ : ExecState} {sop : SyncStmtOp}
    {args : Array Expr} {targets : Array Assignee} {env : LocalEnv}
    {k : Cont} {ch : Choices} {op : SyncOp} {e : Expr} {rest : List Expr}
    (hplan : syncPlan (.syncStmt sop args targets) = some (op, e :: rest)) :
    stepFn σ₀ (.exec (.syncStmt sop args targets) env k) ch
      = pure (.evalE e env (.syncStK op [] rest env k), σ₀, ch) := by
  simp only [stepFn.eq_def]
  split
  · rename_i op' e' rest' heq
    rw [hplan] at heq
    simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at heq
    obtain ⟨hop, he, hrest⟩ := heq
    subst hop; subst he; subst hrest
    rfl
  · rename_i heq
    rw [hplan] at heq
    simp at heq
  · rename_i heq
    rw [hplan] at heq
    simp at heq

private theorem stepFn_exec_assignMany {σ₀ : ExecState}
    {left : Array Assignee} {right : Array Expr} {env : LocalEnv} {k : Cont}
    {ch : Choices} {sh : TargetShape} {e : Expr} {ops : List Expr}
    {rest : List (TargetShape × List Expr)}
    (hsz : left.size = right.size)
    (hplan : targetsPlan left.toList = some ((sh, e :: ops) :: rest)) :
    stepFn σ₀ (.exec (.assignMany left right) env k) ch
      = pure (.evalE e env
          (.tgtOpK sh [] ops [] rest .vals right.toList [] (.seqn #[]) env k),
          σ₀, ch) := by
  simp only [stepFn.eq_def]
  rw [if_pos hsz, hplan]

/-- Fold the renamed spelling of a reversed operand accumulator back
through `completeTargetRef_ren` (the chan-apply fold trick, store side). -/
private theorem completeTargetRef_ren_cons (ρ : Nat → Nat) (sh : TargetShape)
    (v : GoValue) (ops : List GoValue) :
    completeTargetRef sh ((renameValue ρ v :: renameValueList ρ ops).reverse)
      = (completeTargetRef sh ((v :: ops).reverse)).map (renameTargetRef ρ) := by
  rw [show renameValue ρ v :: renameValueList ρ ops
      = renameValueList ρ (v :: ops) from rfl,
    ← renameValueList_reverse, completeTargetRef_ren]

/-- The rename-normalization simp set for the arm induction. -/
macro "ren_simp_only" hinj:term : tactic =>
  `(tactic| simp only [stepFn, renameConfig, renameCont, renameStmt,
      renameExpr, renameValue, renameEntry,
      renameValueList, renameExprList, renameStmtList,
      renameDefer, renameOptExpr, renameOptStmt,
      renameTargetRef, renameEvClause, renameLoc,
      renameStmt_seqn_empty, targetsPlan_map_ren,
      renameEnv_nil, renameChain_nil, renameChain_cons, renameDefers_nil,
      renameDefers_cons, renamePlans_nil, renamePlans_cons,
      renameAssigneeList_nil, renameAssigneeList_cons,
      pure_eq_ok, TripSim,
      seqCont_ren $hinj, contHeadLabel_ren, pushDefer_ren,
      panicPassthrough_ren, recoverResult_ren, markNewestRecovered_ren,
      chainNewestRecovered_ren, panicPayload_ren, runtimeErrorValue_ren,
      stringPanicValue_ren, localEnv_lookup_ren, localEnv_declare_ren,
      localEnv_pushScope_ren, deferrableCallee_ren, recvStores_ren,
      strictPlan_ren, stmtPlan_ren, chanPlan_ren, syncPlan_ren,
      targetPlan_ren, targetsPlan_ren, selectOperands_ren,
      completeTargetRef_ren, assigneeExpr_ren, renameChain_append,
      renameValueList_append, renameValueList_reverse, renameExprList_append,
      Option.map_some, Option.map_none, List.map_append, List.map_cons,
      List.map_nil, List.toList_toArray, List.append_nil, List.nil_append,
      List.size_toArray, List.length_map, Array.length_toList,
      targetsPlan_pair_ren])

macro "ren_simp_all" hinj:term : tactic =>
  `(tactic| simp_all only [stepFn, renameConfig, renameCont, renameStmt,
      renameExpr, renameValue, renameEntry,
      renameValueList, renameExprList, renameStmtList,
      renameDefer, renameOptExpr, renameOptStmt,
      renameTargetRef, renameEvClause, renameLoc,
      renameStmt_seqn_empty, targetsPlan_map_ren,
      renameEnv_nil, renameChain_nil, renameChain_cons, renameDefers_nil,
      renameDefers_cons, renamePlans_nil, renamePlans_cons,
      renameAssigneeList_nil, renameAssigneeList_cons,
      pure_eq_ok, TripSim,
      seqCont_ren $hinj, contHeadLabel_ren, pushDefer_ren,
      panicPassthrough_ren, recoverResult_ren, markNewestRecovered_ren,
      chainNewestRecovered_ren, panicPayload_ren, runtimeErrorValue_ren,
      stringPanicValue_ren, localEnv_lookup_ren, localEnv_declare_ren,
      localEnv_pushScope_ren, deferrableCallee_ren, recvStores_ren,
      strictPlan_ren, stmtPlan_ren, chanPlan_ren, syncPlan_ren,
      targetPlan_ren, targetsPlan_ren, selectOperands_ren,
      completeTargetRef_ren, assigneeExpr_ren, renameChain_append,
      renameValueList_append, renameValueList_reverse, renameExprList_append,
      Option.map_some, Option.map_none, List.map_append, List.map_cons,
      List.map_nil, List.toList_toArray, List.append_nil, List.nil_append,
      List.size_toArray, List.length_map, Array.length_toList,
      targetsPlan_pair_ren])

theorem stepFn_sim {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState}
    (hS : FrameSim ρ na₀ na fr σ σF) (c : Config) (ch : Choices) :
    ExSim (TripSim ρ na₀ na fr)
      (stepFn σ c ch) (stepFn σF (renameConfig ρ c) ch) := by
  have hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y := hS.spec.inj
  fun_cases stepFn σ c ch
  all_goals first
    | exact ExSim.stuck'
    | exact ExSim.unsupported'
    | exact ExSim.internal'
    | exact ExSim.skip fun m h => GoError.noConfusion h
    | (ren_simp_only hinj
       exact ExSim.ok ⟨rfl, hS, rfl⟩)
    | (ren_simp_all hinj
       exact ExSim.ok ⟨rfl, hS, rfl⟩)
    | (ren_simp_only hinj
       refine ExSim.bind (valueAsBool_sim ρ _) ?_
       intro b bF hbF
       subst hbF
       cases b <;> exact ExSim.ok ⟨rfl, hS, rfl⟩)
    | (refine ExSim.ok ⟨?_, hS, rfl⟩
       ren_simp_only hinj
       done)
    | (refine ExSim.ok ⟨?_, hS, rfl⟩
       ren_simp_all hinj
       done)
    | (rename_i hne
       exact ExSim.skip hne)
    | (rename_i hne heq
       exact ExSim.skip hne)
    | skip
  -- panic-path defer with nil callee
  case case4 =>
    ren_simp_all hinj
    refine ExSim.ok ⟨?_, hS, rfl⟩
    ren_simp_only hinj
  -- the terminal abort render
  case case7 =>
    rename_i first rest msg hrend
    have hren := renderPanicHead_ren (ρ := ρ) hS hinj first rest
    rw [hrend] at hren
    simp only [renameEntry] at hren
    ren_simp_only hinj
    rw [hren]
    exact ExSim.ok ⟨rfl, hS, rfl⟩
  -- generic panic passthrough
  case case10 =>
    rename_i chain k h4 h3 h2 h1 k' hpass
    cases k
    case stop => exact absurd rfl h1
    case panicResumeK a b => exact absurd rfl (h2 _ _)
    case frame t te r ds k2 w =>
        cases ds with
        | nil => exact absurd rfl (h4 _ _ _ _ _)
        | cons d ds2 =>
            obtain ⟨cv, av⟩ := d
            exact absurd rfl (h3 _ _ _ _ _ _ _ _)
    all_goals
      simp only [panicPassthrough, Option.some.injEq] at hpass
      subst hpass
      ren_simp_only hinj
      exact ExSim.ok ⟨rfl, hS, rfl⟩
  -- block entry (allocDecls)
  case case13 =>
    ren_simp_only hinj
    rw [← localEnv_pushScope_ren]
    refine ExSim.bind (allocDecls_sim _ _ hS) ?_
    intro r rF hr
    obtain ⟨env1, σ1⟩ := r
    obtain ⟨env1F, σ1F⟩ := rF
    obtain ⟨henv1, hS1⟩ := hr
    dsimp only at henv1 hS1 ⊢
    subst henv1
    exact ExSim.ok ⟨rfl, hS1, rfl⟩
  -- initialization in own-scope sequence
  case case14 =>
    ren_simp_all hinj
    refine ExSim.bind (defaultValue_sim (ρ := ρ) hS.types_eq _) ?_
    intro d dF hdF
    subst hdF
    refine ExSim.ok ⟨?_, hS.alloc_snd d _, rfl⟩
    rw [hS.alloc_fst d _]
    rw [← localEnv_declare_ren]
    ren_simp_only hinj
  -- call entry, nullary: frame entry
  case case36 =>
    ren_simp_all hinj
    refine enterFrameStep_sim hS _ _ _ _ _ _ ?_
    intro f e ls hbody
    ren_simp_only hinj
    rw [hbody]
  -- evalVar (env lookup + load)
  case case66 =>
    rename_i hlook
    ren_simp_only hinj
    rw [hlook]
    refine ExSim.bind (loadLoc_sim hS _) ?_
    intro v vF hvF
    subst hvF
    exact ExSim.ok ⟨rfl, hS, rfl⟩
  -- panic-path defer drain (frame entry on the panic path)
  case case3 =>
    ren_simp_all hinj
    rw [← renameValueList_append]
    refine enterFrameDeferPanicking_sim hS _ _ _ _ _ _ _ ?_
    intro f e hbody
    ren_simp_only hinj
    rw [hbody]
  -- callArgsK done: frame entry
  case case93 =>
    ren_simp_all hinj
    rw [← renameValueList_snoc]
    refine enterFrameStep_sim hS _ _ _ _ _ _ ?_
    intro f e ls hbody
    ren_simp_only hinj
    rw [hbody]
  -- callValCalleeK: no-arg closure entry
  case case101 =>
    ren_simp_all hinj
    refine enterFrameStep_sim hS _ _ _ _ _ _ ?_
    intro f e ls hbody
    ren_simp_only hinj
    rw [hbody]
  -- callValArgsK done: closure entry
  case case107 =>
    ren_simp_all hinj
    rw [← renameValueList_append, ← renameValueList_snoc]
    refine enterFrameStep_sim hS _ _ _ _ _ _ ?_
    intro f e ls hbody
    ren_simp_only hinj
    rw [hbody]
  -- normal-path defer drains
  case case156 =>
    ren_simp_all hinj
    rw [← renameValueList_append]
    refine enterFrameStep_sim hS _ _ _ _ _ _ ?_
    intro f e ls hbody
    ren_simp_only hinj
    rw [hbody]
  case case195 =>
    ren_simp_all hinj
    rw [← renameValueList_append]
    refine enterFrameStep_sim hS _ _ _ _ _ _ ?_
    intro f e ls hbody
    ren_simp_only hinj
    rw [hbody]
  -- deferCalleeK: zero-arg registration
  case case111 =>
    rename_i v env ktail hdefok k2 hpush
    ren_simp_only hinj
    rw [if_pos hdefok]
    rw [show (((renameValue ρ v, ([] : List GoValue)))
          : GoValue × List GoValue)
        = renameDefer ρ (v, []) from rfl]
    rw [pushDefer_ren, hpush]
    exact ExSim.ok ⟨rfl, hS, rfl⟩
  -- deferArgsK done: registration
  case case115 =>
    rename_i v cv vals env ktail k2 hpush
    ren_simp_only hinj
    rw [← renameValueList_snoc]
    rw [show (((renameValue ρ cv, renameValueList ρ (vals ++ [v])))
          : GoValue × List GoValue)
        = renameDefer ρ (cv, vals ++ [v]) from rfl]
    rw [pushDefer_ren, hpush]
    exact ExSim.ok ⟨rfl, hS, rfl⟩
  -- mapRange start (BUG-005 (L): base + start keys)
  case case117 =>
    ren_simp_only hinj
    refine ExSim.bind (mapRangeStartSets_sim hS _) ?_
    intro bs bsF h
    obtain ⟨b1, s1⟩ := bs
    obtain ⟨b1F, s1F⟩ := bsF
    obtain ⟨h1, h2⟩ := h
    dsimp only at h1 h2
    subst h1
    subst h2
    refine ExSim.ok ⟨?_, hS, rfl⟩
    ren_simp_only hinj
  -- chan apply: ok / panic
  case case120 =>
    rename_i v op done env k' c' s' happ
    have hsim := applyChanOp_sim (ρ := ρ) hS op ((v :: done).reverse) env k'
    simp only [renameValueList_reverse, renameValueList] at hsim
    obtain ⟨rF, hF, hrel⟩ := hsim.ok_inv happ
    obtain ⟨cF, sF2⟩ := rF
    obtain ⟨hc, hst⟩ := hrel
    subst hc
    ren_simp_only hinj
    rw [hF]
    exact ExSim.ok ⟨rfl, hst, rfl⟩
  case case121 =>
    rename_i v op done env k' msg happ
    have hsim := applyChanOp_sim (ρ := ρ) hS op ((v :: done).reverse) env k'
    simp only [renameValueList_reverse, renameValueList] at hsim
    have hF := hsim.panic_inv happ
    ren_simp_only hinj
    rw [hF]
    exact ExSim.ok ⟨by ren_simp_only hinj, hS, rfl⟩
  -- select apply: ok / panic
  case case124 =>
    rename_i v clauses default? done env k' c' s' choices' cl? happ
    have hsim := applySelect_sim (ρ := ρ) hS clauses default?
      ((v :: done).reverse) env k' ch
    simp only [renameValueList_reverse, renameValueList] at hsim
    obtain ⟨rF, hF, hrel⟩ := hsim.ok_inv happ
    obtain ⟨cF, sF2, chF2, clF2⟩ := rF
    obtain ⟨hc, hst, hch, hcl⟩ := hrel
    ren_simp_only hinj
    rw [hF]
    exact ExSim.ok ⟨hc, hst, hch⟩
  case case125 =>
    rename_i v clauses default? done env k' msg happ
    have hsim := applySelect_sim (ρ := ρ) hS clauses default?
      ((v :: done).reverse) env k' ch
    simp only [renameValueList_reverse, renameValueList] at hsim
    have hF := hsim.panic_inv happ
    ren_simp_only hinj
    rw [hF]
    exact ExSim.ok ⟨by ren_simp_only hinj, hS, rfl⟩
  -- sync apply: ok / panic
  case case143 =>
    rename_i v op done env k' c' s' happ
    have hsim := applySyncOp_sim (ρ := ρ) hS op ((v :: done).reverse) env k'
    simp only [renameValueList_reverse, renameValueList] at hsim
    obtain ⟨rF, hF, hrel⟩ := hsim.ok_inv happ
    obtain ⟨cF, sF2⟩ := rF
    obtain ⟨hc, hst⟩ := hrel
    subst hc
    ren_simp_only hinj
    rw [hF]
    exact ExSim.ok ⟨rfl, hst, rfl⟩
  case case144 =>
    rename_i v op done env k' msg happ
    have hsim := applySyncOp_sim (ρ := ρ) hS op ((v :: done).reverse) env k'
    simp only [renameValueList_reverse, renameValueList] at hsim
    have hF := hsim.panic_inv happ
    ren_simp_only hinj
    rw [hF]
    exact ExSim.ok ⟨by ren_simp_only hinj, hS, rfl⟩
  -- loadMany plumbing
  case case153 =>
    ren_simp_only hinj
    refine ExSim.bind (loadMany_sim hS _) ?_
    intro vs vsF h
    exact ExSim.stuck'
  case case192 =>
    ren_simp_only hinj
    refine ExSim.bind (loadMany_sim hS _) ?_
    intro vs vsF h
    exact ExSim.stuck'
  case case154 =>
    ren_simp_only hinj
    refine ExSim.bind (loadMany_sim hS _) ?_
    intro vs vsF h
    subst h
    refine ExSim.ok ⟨?_, hS, rfl⟩
    ren_simp_only hinj
  case case193 =>
    ren_simp_only hinj
    refine ExSim.bind (loadMany_sim hS _) ?_
    intro vs vsF h
    subst h
    refine ExSim.ok ⟨?_, hS, rfl⟩
    ren_simp_only hinj
  -- map iteration (BUG-005 (L)): the unified live pick arm — the
  -- candidates load precedes every split, so done / stop / pick are
  -- separated manually here.
  case case163 =>
    rename_i keyVar valVar keyTy valTy body base produced start env k'
    ren_simp_only hinj
    refine ExSim.bind (mapIterCandidates_sim hinj hS keyTy valTy base produced) ?_
    intro cands candsF hcandsF
    subst hcandsF
    rw [renEntriesArr_isEmpty]
    by_cases hemp : cands.isEmpty
    · rw [if_pos hemp, if_pos hemp]
      exact ExSim.ok ⟨rfl, hS, rfl⟩
    · rw [if_neg hemp, if_neg hemp]
      refine ExSim.bind
        (mapIterMandatoryRemains_sim hinj hS.types_eq keyTy cands start) ?_
      intro mand mandF hmand
      subst hmand
      rw [renEntriesArr_size]
      simp only [Choices.consumeAt_mapIter]
      rcases hcons : ch.consume (cands.size + (if mand = true then 0 else 1))
        with ⟨idx, tail⟩
      dsimp only
      rw [renEntriesArr_getElem?]
      cases hidx : cands[idx]? with
      | none =>
          simp only [Option.map_none]
          exact ExSim.ok ⟨rfl, hS, rfl⟩
      | some kv =>
          obtain ⟨key, value⟩ := kv
          simp only [Option.map_some]
          rw [← localEnv_pushScope_ren]
          refine ExSim.bind (bindIterVars_sim hS _ _ _ _ _ _ _) ?_
          intro r rF hr
          obtain ⟨env1, σ1⟩ := r
          obtain ⟨env1F, σ1F⟩ := rF
          obtain ⟨henv1, hS1⟩ := hr
          dsimp only at henv1 hS1 ⊢
          subst henv1
          refine ExSim.ok ⟨?_, hS1, rfl⟩
          ren_simp_only hinj
          congr 2
          apply Array.toList_inj.mp
          simp [renameValueList_eq_map, List.toList_toArray,
            Array.toList_push]
  -- chanRecv entry (named scrutinee)
  case case41 =>
    rename_i env k targets chE elem op e rest hplan
    have hplanF := chanPlan_ren (ρ := ρ) (.chanRecv targets chE elem)
    rw [hplan] at hplanF
    simp only [Option.map_some, renameExprList] at hplanF
    simp only [renameConfig, renameStmt] at hplanF ⊢
    rw [stepFn_exec_chanRecv hplanF]
    exact ExSim.ok ⟨rfl, hS, rfl⟩
  -- syncStmt entry (named scrutinee)
  case case60 =>
    rename_i env k sop args targets op e rest hplan
    have hplanF := syncPlan_ren (ρ := ρ) (.syncStmt sop args targets)
    rw [hplan] at hplanF
    simp only [Option.map_some, renameExprList] at hplanF
    simp only [renameConfig, renameStmt] at hplanF ⊢
    rw [stepFn_exec_sync hplanF]
    exact ExSim.ok ⟨rfl, hS, rfl⟩
  -- assignMany entry
  case case56 =>
    rename_i env k left right hsz sh e ops rest hplan
    have hplanF := targetsPlan_map_ren (ρ := ρ) left.toList
    rw [hplan] at hplanF
    simp only [Option.map_some, renamePlans, List.map_cons, renameExprList]
      at hplanF
    have hszF : ((left.toList.map (renameAssignee ρ)).toArray).size
        = ((renameExprList ρ right.toList).toArray).size := by
      simpa [renameExprList_eq_map] using hsz
    simp only [renameConfig, renameStmt]
    rw [stepFn_exec_assignMany hszF (by
      rw [List.toList_toArray]; exact hplanF)]
    refine ExSim.ok ⟨?_, hS, rfl⟩
    ren_simp_only hinj
    simp only [renamePlans]
  -- wide-statement entry (catch-all scrutinee)
  case case63 =>
    rename_i op nt e rest hplan
    have hplanF := stmtPlan_ren (ρ := ρ) ‹Stmt›
    rw [hplan] at hplanF
    simp only [Option.map_some, renameExprList] at hplanF
    simp only [renameConfig]
    rw [stepFn_exec_wide hplanF]
    simp only [wideEntry]
    exact ExSim.ok ⟨rfl, hS, rfl⟩
  -- wide-statement nullary apply
  case case64 =>
    rename_i op nt hplan
    have hplanF := stmtPlan_ren (ρ := ρ) ‹Stmt›
    rw [hplan] at hplanF
    simp only [Option.map_some, renameExprList] at hplanF
    simp only [renameConfig]
    rw [stepFn_exec_wide hplanF]
    simp only [wideEntry]
    refine ExSim.bind (applyStmtOp_sim hS hinj ch op nt []) ?_
    intro r rF hrel
    obtain ⟨s1, c1⟩ := r
    obtain ⟨s2, c2⟩ := rF
    obtain ⟨hst, hc⟩ := hrel
    dsimp only at hst hc
    subst hc
    exact ExSim.ok ⟨rfl, hst, rfl⟩
  -- strict-expression entry (catch-all scrutinee)
  case case78 =>
    rename_i e _ _ _ _ _ _ _ _ _ _ op e₁ rest hplan
    have hplanF := strictPlan_ren (ρ := ρ) e
    rw [hplan] at hplanF
    simp only [Option.map_some, renameExprList] at hplanF
    simp only [renameConfig]
    rw [stepFn_evalE_strict hplanF]
    simp only [strictEntry]
    exact ExSim.ok ⟨rfl, hS, rfl⟩
  -- strict nullary apply: ok / panic
  case case79 =>
    rename_i e _ _ _ _ _ _ _ _ _ _ op hplan v s' happ
    have hplanF := strictPlan_ren (ρ := ρ) e
    rw [hplan] at hplanF
    simp only [Option.map_some, renameExprList] at hplanF
    simp only [renameConfig]
    rw [stepFn_evalE_strict hplanF]
    simp only [strictEntry]
    have hsim := applyStrictOp_sim (ρ := ρ) hS hinj op []
    simp only [renameValueList] at hsim
    obtain ⟨rF, hF, hrel⟩ := hsim.ok_inv happ
    obtain ⟨vF, sF2⟩ := rF
    obtain ⟨hv, hst⟩ := hrel
    dsimp only at hv hst
    subst hv
    rw [hF]
    exact ExSim.ok ⟨rfl, hst, rfl⟩
  case case80 =>
    rename_i e _ _ _ _ _ _ _ _ _ _ op hplan msg happ
    have hplanF := strictPlan_ren (ρ := ρ) e
    rw [hplan] at hplanF
    simp only [Option.map_some, renameExprList] at hplanF
    simp only [renameConfig]
    rw [stepFn_evalE_strict hplanF]
    simp only [strictEntry]
    have hsim := applyStrictOp_sim (ρ := ρ) hS hinj op []
    simp only [renameValueList] at hsim
    rw [hsim.panic_inv happ]
    exact ExSim.ok ⟨by ren_simp_only hinj, hS, rfl⟩
  -- strictK apply: ok / panic
  case case84 =>
    rename_i v op done env k' out s' happ
    have hsim := applyStrictOp_sim (ρ := ρ) hS hinj op ((v :: done).reverse)
    simp only [renameValueList_reverse, renameValueList] at hsim
    obtain ⟨rF, hF, hrel⟩ := hsim.ok_inv happ
    obtain ⟨vF, sF2⟩ := rF
    obtain ⟨hv, hst⟩ := hrel
    dsimp only at hv hst
    subst hv
    ren_simp_only hinj
    rw [hF]
    exact ExSim.ok ⟨rfl, hst, rfl⟩
  case case85 =>
    rename_i v op done env k' msg happ
    have hsim := applyStrictOp_sim (ρ := ρ) hS hinj op ((v :: done).reverse)
    simp only [renameValueList_reverse, renameValueList] at hsim
    have hF := hsim.panic_inv happ
    ren_simp_only hinj
    rw [hF]
    exact ExSim.ok ⟨by ren_simp_only hinj, hS, rfl⟩
  -- stmtOpK target check / shift: panic / ok / value position
  case case94 =>
    rename_i v op nt done env k' a rest hlt msg hloc
    ren_simp_only hinj
    simp only [renameValueList_length]
    rw [if_pos hlt, valueAsLoc_panic_ren (ρ := ρ) hloc]
    exact ExSim.ok ⟨by ren_simp_only hinj, hS, rfl⟩
  case case96 =>
    rename_i v op nt done env k' a rest hlt l hloc
    ren_simp_only hinj
    simp only [renameValueList_length]
    rw [if_pos hlt, valueAsLoc_ren (ρ := ρ) hloc]
    exact ExSim.ok ⟨rfl, hS, rfl⟩
  case case97 =>
    rename_i v op nt done env k' a rest hge
    ren_simp_only hinj
    simp only [renameValueList_length]
    rw [if_neg hge]
    exact ExSim.ok ⟨rfl, hS, rfl⟩
  -- stmtOpK apply: ok / panic
  case case98 =>
    rename_i v op nt done env k' s' choices' happ
    have hsim := applyStmtOp_sim (ρ := ρ) hS hinj ch op nt ((v :: done).reverse)
    simp only [renameValueList_reverse, renameValueList] at hsim
    obtain ⟨rF, hF, hrel⟩ := hsim.ok_inv happ
    obtain ⟨sF2, chF2⟩ := rF
    obtain ⟨hst, hch⟩ := hrel
    dsimp only at hst hch
    subst hch
    ren_simp_only hinj
    rw [hF]
    -- BUG-005 (L): the contAfterStmtOp bind rides between the apply
    -- and the return on both sides.
    have hcsim := contAfterStmtOp_sim hinj hst op ((v :: done).reverse) k'
    simp only [renameValueList_reverse, renameValueList] at hcsim
    refine ExSim.bind hcsim ?_
    intro k1 k1F hk1
    subst hk1
    exact ExSim.ok ⟨rfl, hst, rfl⟩
  case case99 =>
    rename_i v op nt done env k' msg happ
    have hsim := applyStmtOp_sim (ρ := ρ) hS hinj ch op nt ((v :: done).reverse)
    simp only [renameValueList_reverse, renameValueList] at hsim
    have hF := hsim.panic_inv happ
    ren_simp_only hinj
    rw [hF]
    exact ExSim.ok ⟨by ren_simp_only hinj, hS, rfl⟩
  -- tgtOpK completion: next target / rhs entry / storeK entry
  case case129 =>
    rename_i v sh ops refs rop rhs vals body env k' r hcomp sh' e ops' rest
    ren_simp_only hinj
    rw [completeTargetRef_ren_cons, hcomp]
    refine ExSim.ok ⟨?_, hS, rfl⟩
    ren_simp_only hinj
  case case131 =>
    rename_i v sh ops refs rop vals body env k' r hcomp a rest
    ren_simp_only hinj
    rw [completeTargetRef_ren_cons, hcomp]
    refine ExSim.ok ⟨?_, hS, rfl⟩
    ren_simp_only hinj
  case case132 =>
    rename_i v sh ops refs rop vals body env k' r hcomp
    ren_simp_only hinj
    rw [completeTargetRef_ren_cons, hcomp]
    refine ExSim.ok ⟨?_, hS, rfl⟩
    ren_simp_only hinj
  -- rhsK apply: ok / panic
  case case134 =>
    rename_i v rop refs done body env k' vals happ
    have hsim := applyRhsOp_sim (ρ := ρ) hS hinj rop ((v :: done).reverse)
    simp only [renameValueList_reverse, renameValueList] at hsim
    obtain ⟨valsF, hF, hrel⟩ := hsim.ok_inv happ
    subst hrel
    ren_simp_only hinj
    rw [hF]
    exact ExSim.ok ⟨rfl, hS, rfl⟩
  case case135 =>
    rename_i v rop refs done body env k' msg happ
    have hsim := applyRhsOp_sim (ρ := ρ) hS hinj rop ((v :: done).reverse)
    simp only [renameValueList_reverse, renameValueList] at hsim
    have hF := hsim.panic_inv happ
    ren_simp_only hinj
    rw [hF]
    exact ExSim.ok ⟨by ren_simp_only hinj, hS, rfl⟩
  -- storeK stores: ok / panic
  case case164 =>
    rename_i body env k' r rs val vrest s' hstore
    have hsim := storeTarget_sim (ρ := ρ) hS hinj r val
    obtain ⟨sF2, hF, hrel⟩ := hsim.ok_inv hstore
    simp only [renameTargetRef] at hF
    ren_simp_only hinj
    rw [hF]
    exact ExSim.ok ⟨rfl, hrel, rfl⟩
  case case165 =>
    rename_i body env k' r rs val vrest msg hstore
    have hsim := storeTarget_sim (ρ := ρ) hS hinj r val
    have hF := hsim.panic_inv hstore
    simp only [renameTargetRef] at hF
    ren_simp_only hinj
    rw [hF]
    exact ExSim.ok ⟨by ren_simp_only hinj, hS, rfl⟩

end GoLean.Frame
