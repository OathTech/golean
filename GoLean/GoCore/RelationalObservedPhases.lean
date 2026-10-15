import GoLean.GoCore.RelationalObservedPath

/-!
# Source assignment and call phases

Uniform store-preserving preparation ends at one write or activation. Assignment
cleanup is valid for every post-store; it never reuses a pre-write read fact.
Existential controls keep target plans and call frames inside these proofs.
-/
namespace GoLean.GoCore.Relational.Observed
open Machine

/-- Empty sequence cleanup with intermediate source admission, for every tail. -/
theorem empty_sequence_path (ctx : ProgramCtx) (env : LocalEnv) (k : Continuation) :
    StorePath ctx (fun _ => True) (.exec (.seqn #[]) env k.toMachine) (.next k.toMachine) := by
  have shape : seqCont [] env k.toMachine = k.toMachine ∨
      seqCont [] env k.toMachine = .seq [] env k.toMachine := by
    unfold seqCont
    split
    · split <;> simp_all
    · exact .inr rfl
  rcases shape with splice | wrap
  · apply StorePath.pure _ ⟨(by intro h; cases h), rfl⟩ (by intros; rfl)
    intro s
    exact ⟨by simpa [Transition, splice] using
      (Step.seqn (ctx := ctx) (ss := #[]) (env := env) (k := k.toMachine) (s := s)), rfl⟩
  · apply (StorePath.pure (c := .exec (.seqn #[]) env k.toMachine)
      (d := .next (.seq [] env k.toMachine)) _ ⟨(by intro h; cases h), rfl⟩ (by intros; rfl)).trans
    · exact StorePath.pure (fun s => sequence_done ctx env k s) ⟨(by intro h; cases h), rfl⟩ (by intros; rfl)
    · intro s
      exact ⟨by simpa [Transition, wrap] using
        (Step.seqn (ctx := ctx) (ss := #[]) (env := env) (k := k.toMachine) (s := s)), rfl⟩

private def writeBefore (env : LocalEnv) (k : Continuation) (target : Loc) (v : GoValue) : Config :=
  .next (.storeK [.chain (.addr target) [] []] [v] (.seqn #[]) env k.toMachine)

private def writeAfter (env : LocalEnv) (k : Continuation) : Config :=
  .next (.storeK [] [] (.seqn #[]) env k.toMachine)

private theorem write_effect (ctx : ProgramCtx) (env : LocalEnv) (k : Continuation)
    (target : Loc) (v : GoValue) :
    StoreEffect ctx (fun s t => storeLoc ctx s target v = .ok t)
      (writeBefore env k target v) (writeAfter env k) := by
  refine ⟨⟨⟨(by intro h; cases h), rfl⟩, ?_⟩, by intros; rfl⟩
  intro s t hw
  have store : storeTarget ctx s (.chain (.addr target) [] []) v =
      .ok (t, [.access .write (.data target.canon)]) := by
    simp [storeTarget, storeTarget.plan, resolveChain, valueAsLoc, Mem.store,
      hw, Bind.bind, Except.bind, pure, Except.pure]
  exact ⟨_, Step.storeStep (r := .ok (t, [.access .write (.data target.canon)]))
    (by rw [store]; rfl) rfl, rfl⟩

private theorem write_suffix (ctx : ProgramCtx) (env : LocalEnv) (k : Continuation) :
    StorePath ctx (fun _ => True) (writeAfter env k) (.next k.toMachine) :=
  (StorePath.pure (fun _ => ⟨Step.storeDone, rfl⟩)
    ⟨(by intro h; cases h), rfl⟩ (by intros; rfl)).trans (empty_sequence_path ctx env k)

private theorem assignment_phases (ctx : ProgramCtx) (env : LocalEnv) (k : Continuation)
    (lhs : Assignee) (pointer rhs : Expr) (target : Loc) (value : GoValue) (fact : Store → Prop)
    (plan : targetPlan lhs = some (.chain [], [pointer]))
    (hp : ReadOnlyExpr ctx fact env pointer (.addr target))
    (hv : ReadOnlyExpr ctx fact env rhs value) :
    ∃ before after,
      StorePath ctx fact (.exec (.assign lhs rhs) env k.toMachine) before ∧
      StoreEffect ctx (fun s t => storeLoc ctx s target value = .ok t) before after ∧
      StorePath ctx (fun _ => True) after (.next k.toMachine) := by
  let pk : Continuation := ⟨.tgtOpK (.chain []) [] [] [] [] .vals [rhs] [] (.seqn #[]) env k.toMachine⟩
  let vk : Continuation := ⟨.rhsK .vals [.chain (.addr target) [] []] [] [] (.seqn #[]) env k.toMachine⟩
  refine ⟨writeBefore env k target value, writeAfter env k, ?_,
    write_effect ctx env k target value, write_suffix ctx env k⟩
  apply (StorePath.pure (d := .evalE pointer env pk.toMachine)
    (fun _ => ⟨Step.assignFirst plan, rfl⟩) ⟨(by intro h; cases h), rfl⟩ (by intros; rfl)).trans
  apply (hp pk).trans
  apply (StorePath.pure (c := .retV (.addr target) pk.toMachine) (d := .evalE rhs env vk.toMachine)
    (fun _ => ⟨Step.tgtOpRhs rfl, rfl⟩) ⟨(by intro h; cases h), rfl⟩ (by intros; rfl)).trans
  exact (hv vk).trans (StorePath.pure (fun _ => ⟨Step.rhsStores rfl rfl, rfl⟩)
    ⟨(by intro h; cases h), rfl⟩ (by intros; rfl))

/-- Compose `*p = rhs` from a successful pointer-binding read and a read-only
RHS. The pointee may be interior or aliased; reads are not assumed after writing.
Address-former chains on the assignment's left side are outside this law. -/
theorem pointer_rhs_phases (ctx : ProgramCtx) (env : LocalEnv) (k : Continuation)
    (id : VarId) (slot target : Loc) (rhs : Expr) (value : GoValue) (fact : Store → Prop)
    (bound : LocalEnv.lookup env id = some slot)
    (read : ∀ s, fact s → loadRoot ctx s slot = .ok (.addr target))
    (hv : ReadOnlyExpr ctx fact env rhs value) :
    ∃ before after,
      StorePath ctx fact (.exec (.assign (.addr (.var id)) rhs) env k.toMachine) before ∧
      StoreEffect ctx (fun s t => storeLoc ctx s target value = .ok t) before after ∧
      StorePath ctx (fun _ => True) after (.next k.toMachine) :=
  assignment_phases ctx env k (.addr (.var id)) (.var id) rhs target value fact rfl
    ((ReadOnlyExpr.variable ctx env id slot (.addr target) bound).weaken read) hv

/-- Assign a read-only RHS to a bound variable, without exposing target frames. -/
theorem variable_expression_phases (ctx : ProgramCtx) (env : LocalEnv) (k : Continuation)
    (dst : VarId) (target : Loc) (rhs : Expr) (value : GoValue) (fact : Store → Prop)
    (bound : LocalEnv.lookup env dst = some target)
    (hv : ReadOnlyExpr ctx fact env rhs value) :
    ∃ before after,
      StorePath ctx fact (.exec (.assign (.var dst) rhs) env k.toMachine) before ∧
      StoreEffect ctx (fun s t => storeLoc ctx s target value = .ok t) before after ∧
      StorePath ctx (fun _ => True) after (.next k.toMachine) :=
  assignment_phases ctx env k (.var dst) (.ref dst) rhs target value fact rfl
    ((ReadOnlyExpr.reference ctx env dst target bound).weaken (fun _ _ => trivial)) hv

/-- Split `*p = v` at its write. Both reads precede it; the target may be
interior and may alias either operand binding. No final-tail admission is imposed. -/
theorem pointer_assignment_phases (ctx : ProgramCtx) (env : LocalEnv) (k : Continuation)
    (pId vId : VarId) (pSlot vSlot target : Loc) (value : GoValue)
    (hp : LocalEnv.lookup env pId = some pSlot)
    (hv : LocalEnv.lookup env vId = some vSlot) :
    ∃ before after,
      StorePath ctx (fun s => loadRoot ctx s pSlot = .ok (.addr target) ∧
        loadRoot ctx s vSlot = .ok value)
        (.exec (.assign (.addr (.var pId)) (.var vId)) env k.toMachine) before ∧
      StoreEffect ctx (fun s t => storeLoc ctx s target value = .ok t) before after ∧
      StorePath ctx (fun _ => True) after (.next k.toMachine) := by
  exact pointer_rhs_phases ctx env k pId pSlot target (.var vId) value _ hp (fun _ h => h.1)
    ((ReadOnlyExpr.variable ctx env vId vSlot value hv).weaken (fun _ h => h.2))

/-- Split source-variable assignment at its write, including self-assignment
and interior aliases. The post-write suffix needs no successful-read premise. -/
theorem variable_assignment_phases (ctx : ProgramCtx) (env : LocalEnv) (k : Continuation)
    (dst src : VarId) (target source : Loc) (value : GoValue)
    (hd : LocalEnv.lookup env dst = some target)
    (hs : LocalEnv.lookup env src = some source) :
    ∃ before after,
      StorePath ctx (fun s => loadRoot ctx s source = .ok value)
        (.exec (.assign (.var dst) (.var src)) env k.toMachine) before ∧
      StoreEffect ctx (fun s t => storeLoc ctx s target value = .ok t) before after ∧
      StorePath ctx (fun _ => True) after (.next k.toMachine) := by
  exact variable_expression_phases ctx env k dst target (.var src) value _ hd
    (ReadOnlyExpr.variable ctx env src source value hs)

private def plans (ids : List VarId) : List (TargetShape × List Expr) :=
  ids.map fun id => (.chain [], [.ref id])

private theorem plans_ok (ids : List VarId) :
    targetsPlan (ids.map Assignee.var) = some (plans ids) := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
    simp [targetsPlan, plans, List.mapM_cons, targetPlan] at ih ⊢
    rw [ih]
    rfl

private theorem arguments_path {ctx : ProgramCtx} {fact : Store → Prop} {env : LocalEnv}
    {es : List Expr} {vs : List GoValue} (h : OperandPaths ctx fact env es vs)
    (e : Expr) (v : GoValue)
    (hv : ∀ k : Continuation, StorePath ctx fact (.evalE e env k.toMachine) (.retV v k.toMachine))
    (done : List GoValue) (fid : FuncId) (ps : List (TargetShape × List Expr)) (k : Continuation) :
    ∃ before,
      StorePath ctx fact (.evalE e env (.callArgsK fid ps done es env k.toMachine)) before ∧
      StepAdmission before ∧
      ∀ (s : Store) (f : Func) (a : Activation),
        enterFrame ctx s fid (done ++ v :: vs) = .ok (.run f a.locals a.results, a.store, []) →
        ∃ l, Enters ctx ⟨before, s⟩
          (statement f.body a.locals ⟨.frame ps env a.results [] k.toMachine f.id⟩ a.store) l
          ⟨f.id, done ++ v :: vs, s⟩ ∧ l.picks = [] := by
  induction h generalizing e v done with
  | nil =>
    refine ⟨.retV v (.callArgsK fid ps done [] env k.toMachine), hv _,
      ⟨(by intro h; cases h), rfl⟩, ?_⟩
    intro s f a entry
    refine ⟨⟨[], [], []⟩, ?_, rfl⟩
    exact ⟨fid, _, f, a.locals, a.results, [], .arguments, entry, rfl, rfl, rfl, rfl⟩
  | @cons e' v' es vs he ht ih =>
    obtain ⟨before, path, admitted, activate⟩ := ih e' v' he (done ++ [v])
    refine ⟨before, (hv _).trans (?_ : StorePath ctx fact _ before), admitted, ?_⟩
    · exact (StorePath.pure (fun _ => ⟨Step.callArgNext, rfl⟩)
        ⟨(by intro h; cases h), rfl⟩ (by intros; rfl)).trans path
    · intro s f a entry
      simpa [List.append_assoc] using activate s f a (by simpa [List.append_assoc] using entry)

/-- Source-call preparation followed by one activation transition. Dispatch,
arity and activation premises belong only to the effect, not operand traversal.
The returned control is uniform over stores, functions and activations. -/
theorem SavedCaller.entry_phases (caller : SavedCaller) (ctx : ProgramCtx) (fid : FuncId)
    (es : List Expr) (vs : List GoValue) (fact : Store → Prop)
    (operands : OperandPaths ctx fact caller.locals es vs) :
    ∃ before,
      StorePath ctx fact (caller.call fid es ⟨#[]⟩).control before ∧
      StepAdmission before ∧
      ∀ (s : Store) (f : Func) (a : Activation),
        findFunctionIn? ctx.functions fid = some f →
        methodInfoByFuncId? ctx f.id = none → f.args.size = vs.length →
        LocalEntry ctx f vs s (.ok a) →
        ∃ l, Enters ctx ⟨before, s⟩ ((caller.boundary f a).body f a) l ⟨f.id, vs, s⟩ ∧ l.picks = [] := by
  cases operands with
  | nil =>
    refine ⟨_, .refl, ⟨(by intro h; cases h), rfl⟩, ?_⟩
    intro s f a found method arity activation
    have entry := activation.declared found (by simp [method]) arity
    refine ⟨⟨[], [], []⟩, ?_, rfl⟩
    exact ⟨fid, _, f, a.locals, a.results, [], .direct
      (by simpa [plans, SavedCaller.boundary] using plans_ok caller.destinations)
      rfl, entry, rfl, rfl, rfl, rfl⟩
  | @cons e v es vs he ht =>
    obtain ⟨before, path, admitted, activate⟩ := arguments_path ht e v he [] fid
      (plans caller.destinations) caller.tail
    refine ⟨before, ?_, admitted, ?_⟩
    · exact (StorePath.pure
        (fun _ => ⟨Step.callStart (by simpa using plans_ok caller.destinations) (by simp), rfl⟩)
        ⟨(by intro h; cases h), rfl⟩ (by
          intros
          simp [Boundary.events, Boundary.entry?, Boundary.invocation?, Boundary.return?])).trans path
    · intro s f a found method arity activation
      exact activate s f a (activation.declared found (by simp [method]) arity)

end GoLean.GoCore.Relational.Observed
