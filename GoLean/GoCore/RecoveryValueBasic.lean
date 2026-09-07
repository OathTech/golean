import GoLean.GoCore.RecoveryCallControl

namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

theorem strict_advances {world fs s Γ env op doneKinds kind pendingKinds out done pending k v}
    (heap : HeapTyped world s) (he : EnvTyped world Γ env)
    (ho : Operator op (doneKinds ++ kind :: pendingKinds) out)
    (hd : DeliveryList world doneKinds done.reverse)
    (hp : Expressions Γ pending pendingKinds) (hk : ValueCont world fs out k)
    (hv : Delivered world kind v) :
    Advances world fs s (.retV v (.strictK op done pending env k)) := by
  cases hp with
  | nil =>
    have hargs : DeliveryList world (doneKinds ++ [kind]) (v :: done).reverse := by
      simpa using hd.append (.cons hv .nil)
    obtain ⟨outV, run, ht⟩ := ho.apply heap hargs
    exact advances_same heap (.ret ht hk)
      (fun _ => by simp only [stepFn, run, toResult]; rfl)
  | @cons _ _ kind' kinds' hp hps =>
    have hdone : DeliveryList world (doneKinds ++ [kind]) (v :: done).reverse := by
      simpa using hd.append (.cons hv .nil)
    have hop : Operator op ((doneKinds ++ [kind]) ++ kind' :: kinds') out := by
      simpa only [List.append_assoc, List.singleton_append] using ho
    exact advances_same heap (.eval he hp (.strict he hop hdone hps hk)) (fun _ => rfl)

theorem and_advances {world fs s Γ env e k v} (heap : HeapTyped world s)
    (he : EnvTyped world Γ env) (ht : ExprTyped Γ e .boolean)
    (hk : ValueCont world fs (.value .boolean) k)
    (hv : Delivered world (.value .boolean) v) :
    Advances world fs s (.retV v (.andK e env k)) := by
  cases hv with
  | value hv => cases hv with
    | boolean b =>
      cases b with
      | false => exact advances_same heap (.ret (.value (.boolean false)) hk) (fun _ => rfl)
      | true => exact advances_same heap (.eval he (.value ht) (.bool hk)) (fun _ => rfl)

theorem or_advances {world fs s Γ env e k v} (heap : HeapTyped world s)
    (he : EnvTyped world Γ env) (ht : ExprTyped Γ e .boolean)
    (hk : ValueCont world fs (.value .boolean) k)
    (hv : Delivered world (.value .boolean) v) :
    Advances world fs s (.retV v (.orK e env k)) := by
  cases hv with
  | value hv => cases hv with
    | boolean b =>
      cases b with
      | false => exact advances_same heap (.eval he (.value ht) (.bool hk)) (fun _ => rfl)
      | true => exact advances_same heap (.ret (.value (.boolean true)) hk) (fun _ => rfl)

theorem bool_advances {world fs s k v} (heap : HeapTyped world s)
    (hk : ValueCont world fs (.value .boolean) k)
    (hv : Delivered world (.value .boolean) v) :
    Advances world fs s (.retV v (.boolK k)) := by
  cases hv with
  | value hv => cases hv with
    | boolean b => exact advances_same heap (.ret (.value (.boolean b)) hk) (fun _ => rfl)

theorem branch_advances {world fs s Γ env t f k v} (heap : HeapTyped world s)
    (he : EnvTyped world Γ env) (ht : ControlStmt fs false Γ t)
    (hf : ControlStmt fs false Γ f) (nt : declarationCount t = 0)
    (nf : declarationCount f = 0) (hk : ReturnCont world fs k)
    (hv : Delivered world (.value .boolean) v) :
    Advances world fs s (.retV v (.ifK t f env k)) := by
  cases hv with
  | value hv => cases hv with
    | boolean b =>
      cases b with
      | false => exact advances_same heap (.execNeutral he hf nf hk) (fun _ => rfl)
      | true => exact advances_same heap (.execNeutral he ht nt hk) (fun _ => rfl)

theorem rhs_advances {world fs s Γ env p before after refs done pending k v}
    (heap : HeapTyped world s) (he : EnvTyped world Γ env)
    (hr : RefsTyped world (before ++ p :: after) refs)
    (hd : ParamsValues world before done.reverse) (hp : Arguments Γ pending after)
    (hk : ReturnCont world fs k) (hv : Delivered world (.typed p.typ) v) :
    Advances world fs s (.retV v (.rhsK .vals refs done pending (.seqn #[]) env k)) := by
  cases hv with
  | typed hv =>
    have hdone : ParamsValues world (before ++ [p]) (v :: done).reverse := by
      simpa using hd.append (.cons hv .nil)
    cases hp with
    | nil =>
      exact advances_same heap (.store he.bindings hr hdone hk)
        (fun _ => by simp [stepFn, applyRhsOp, toResult]; rfl)
    | @cons _ _ p' ps' hp hps =>
      have hr' : RefsTyped world ((before ++ [p]) ++ p' :: ps') refs := by
        simpa only [List.append_assoc, List.singleton_append] using hr
      exact advances_same heap (.eval he (.typed hp) (.rhs he hr' hdone hps hk)) (fun _ => rfl)

theorem target_advances {world fs s Γ env p sort before after refs plans rhs vals k v}
    (heap : HeapTyped world s) (he : EnvTyped world Γ env)
    (ht : TypeClass p.typ sort) (hr : RefsTyped world before refs)
    (hp : PlansTyped Γ plans after)
    (source : AssignmentSource world Γ (before ++ p :: after) rhs vals)
    (hk : ReturnCont world fs k) (hv : Delivered world (.address sort) v) :
    Advances world fs s (.retV v
      (.tgtOpK (.chain []) [] [] refs plans .vals rhs vals (.seqn #[]) env k)) := by
  cases hv with
  | @address _ loc ha =>
    have hcurrent : RefTyped world (.chain (.addr loc) [] []) p.typ := .root ⟨sort, ht, ha⟩
    have hdone := hr.append (.cons hcurrent .nil)
    cases hp with
    | nil =>
      cases source with
      | values hs =>
        exact advances_same heap (.store he.bindings hdone hs hk)
          (fun _ => by simp [stepFn, completeTargetRef, indexStepCount])
      | expressions hs =>
        generalize hps : before ++ [p] = ps at hs hdone
        cases hs with
        | nil => have := congrArg List.length hps; simp at this
        | cons hx hxs =>
          exact advances_same heap (.eval he (.typed hx)
            (.rhs (before := []) (done := []) he hdone .nil hxs hk))
            (fun _ => by simp [stepFn, completeTargetRef, indexStepCount])
    | @cons _ _ p' ps' hp hps =>
      cases hp with
      | root hty hx =>
        have source' : AssignmentSource world Γ ((before ++ [p]) ++ p' :: ps') rhs vals := by
          simpa only [List.append_assoc, List.singleton_append] using source
        exact advances_same heap (.eval he hx (.target he hty hdone hps source' hk))
          (fun _ => by simp [stepFn, completeTargetRef, indexStepCount])

theorem panic_advances {world fs s k v} (heap : HeapTyped world s)
    (hk : ReturnCont world fs k) (hv : Delivered world .boxed v) :
    Advances world fs s (.retV v (.panicArgK k)) := by
  cases hv with
  | boxed bytes =>
    exact advances_same heap
      (.panicking (ChainTyped.single bytes false) (.exit (.stmt hk))) (fun _ => rfl)

end GoLean.GoCore.RecoveryRuntime
