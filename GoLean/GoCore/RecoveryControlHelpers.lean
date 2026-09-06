import GoLean.GoCore.RecoveryExpressionProgress

namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

theorem ParamsValues.append {world ps qs vs ws} (h : ParamsValues world ps vs)
    (h' : ParamsValues world qs ws) : ParamsValues world (ps ++ qs) (vs ++ ws) := by
  induction h with
  | nil => exact h'
  | cons hv _ ih => exact .cons hv ih

theorem arguments_split {Γ es rest ps} (h : Arguments Γ (es ++ rest) ps) :
    ∃ before after, ps = before ++ after ∧ Arguments Γ es before ∧ Arguments Γ rest after := by
  induction es generalizing ps with
  | nil => exact ⟨[], ps, rfl, .nil, h⟩
  | cons e es ih =>
    cases h with
    | @cons _ _ p ps he hs =>
      obtain ⟨before, after, rfl, hb, ha⟩ := ih hs
      exact ⟨p :: before, after, rfl, .cons he hb, ha⟩

theorem expression_root_spine {Γ e} (h : ExprTyped Γ e .root) :
    targetSpine e = ([], [e]) := by cases h <;> rfl

theorem target_plan_typed {Γ target ty} (h : TargetAt Γ target ty) :
    ∃ plan, targetPlan target = some plan ∧ PlanTyped Γ plan ty := by
  cases h with
  | typed ht ha =>
    cases ha with
    | var hn => exact ⟨_, rfl, .root ht (.addressRef hn)⟩
    | addr he => exact ⟨_, by simp [targetPlan, expression_root_spine he],
        .root ht (.addressExpr he)⟩

theorem targets_plan_typed {Γ targets ps} (h : Targets Γ targets ps) :
    ∃ plans, targetsPlan targets = some plans ∧ PlansTyped Γ plans ps := by
  induction h with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons ht _ ih =>
    obtain ⟨plan, run, hp⟩ := target_plan_typed ht
    obtain ⟨plans, runs, hs⟩ := ih
    exact ⟨plan :: plans, by simp [targetsPlan, List.mapM_cons, run,
      show List.mapM targetPlan _ = some plans from runs], .cons hp hs⟩

theorem assignment_typed {Γ target expr} (h : Assignment Γ target expr) :
    ∃ ty, TargetAt Γ target ty ∧ ExprAt Γ expr ty := by
  cases h with
  | typed ht he =>
    cases ht with
    | var hn =>
      obtain ⟨ty, hn, hty⟩ := hn
      exact ⟨ty, .typed hty (.var ⟨ty, hn, hty⟩), .typed hty he⟩
    | addr hr => exact ⟨.bool, .typed .boolean (.addr hr), .typed .boolean he⟩

theorem Expression.weaken {Γ Δ e kind} (h : Expression Γ e kind) (inc : Included Γ Δ) :
    Expression Δ e kind := by
  cases h with
  | value h => exact .value (expr_weaken h inc)
  | typed h => exact .typed (exprAt_weaken h inc)
  | addressRef h => exact .addressRef (inc _ _ h)
  | addressExpr h => exact .addressExpr (expr_weaken h inc)
  | boxed h => exact .boxed (panicArgument_weaken h inc)
  | closure h => exact .closure (arguments_weaken h inc)

theorem ControlStmt.neutral_false {fs Γ stmt} (h : ControlStmt fs true Γ stmt)
    (hn : declarationCount stmt = 0) : ControlStmt fs false Γ stmt := by
  cases h <;> try constructor <;> assumption
  case initialization => simp [declarationCount] at hn

theorem ReturnCont.seqCont_neutral {world fs Γ ss env k}
    (he : EnvTyped world Γ env) (hs : ControlStmts fs Γ ss)
    (hn : declarationCounts ss = 0) (hk : ReturnCont world fs k) :
    ReturnCont world fs (seqCont ss env k) := by
  cases hk with
  | frame he' hp hr hd hx wb => exact .seq he hs (.frame he' hp hr hd hx wb)
  | @seq Δ env' rest k he' hs' hk =>
    by_cases henv : env' = env
    · subst env'
      rw [seqCont, if_pos rfl]
      have hi := he.included_append_right he'
      apply ReturnCont.seq (he.append he')
      · apply ControlStmts.append (hs.weaken (Γ ++ Δ) (Included.append_left Γ Δ))
        rw [afterStmts_neutral _ _ hn]
        exact hs'.weaken _ hi
      · exact hk
    · simpa [seqCont, henv] using ReturnCont.seq he hs (.seq he' hs' hk)

theorem RefTyped.store {world s ref ty value} (heap : HeapTyped world s)
    (hr : RefTyped world ref ty) (hv : ValueAt world ty value) :
    ∃ t, storeTarget s ref value = .ok t ∧ StoreExtension world world s t := by
  cases hr with
  | root ha =>
    obtain ⟨sort, ht, ha⟩ := ha
    obtain ⟨t, run, heap', ctx, _⟩ := heap.store ha (hv.sorted ht)
    exact ⟨t, by simpa [storeTarget, resolveChain, valueAsLoc,
      Bind.bind, Except.bind, Pure.pure, Except.pure] using run,
      ⟨.refl world, heap', ctx⟩⟩

theorem store_advances {world fs s env ps refs vs k} (heap : HeapTyped world s)
    (he : BindingsTyped world env) (hr : RefsTyped world ps refs)
    (hv : ParamsValues world ps vs) (hk : ReturnCont world fs k) :
    Advances world fs s (.next (.storeK refs vs (.seqn #[]) env k)) := by
  cases hr with
  | nil =>
    cases hv
    exact advances_same heap (.execNeutral (Γ := []) ⟨he, by simp [RecoveryTyping.lookup]⟩
      (.seqn .nil) rfl hk) (fun _ => rfl)
  | cons href hrs =>
    cases hv with
    | cons hv hvs =>
      obtain ⟨t, run, ext⟩ := href.store heap hv
      exact fun ch => ⟨world, _, t, by simp [stepFn, run, toResult]; rfl, ext,
        .store he hrs hvs hk⟩

end GoLean.GoCore.RecoveryRuntime
