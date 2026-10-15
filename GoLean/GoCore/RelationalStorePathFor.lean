import GoLean.GoCore.RelationalExpression

namespace GoLean.GoCore.Relational
open Machine

/-- A store-uniform path with an explicit predicate at each traversed source.
The predicate can be a client's observation admission condition. Endpoints
and arbitrary following continuations need not satisfy it. -/
inductive StorePathFor (ctx : ProgramCtx) (fact : Store → Prop) (policy : Config → Prop) :
    Config → Config → Prop where
  | refl {c} : StorePathFor ctx fact policy c c
  | step {c d e} :
      (∀ s, fact s → ∃ l, Transition ctx ⟨c,s⟩ l ⟨d,s⟩ ∧ l.picks = []) →
      StepAdmission c → policy c → StorePathFor ctx fact policy d e →
      StorePathFor ctx fact policy c e

theorem StorePathFor.forget {ctx fact policy c d} (h : StorePathFor ctx fact policy c d) :
    StorePath ctx fact c d := by
  induction h with
  | refl => exact .refl
  | step ht ha _ _ ih => exact .step ht ha ih

theorem StorePath.withTrue {ctx fact c d} (h : StorePath ctx fact c d) :
    StorePathFor ctx fact (fun _ => True) c d := by
  induction h with
  | refl => exact .refl
  | step ht ha _ ih => exact .step ht ha trivial ih

theorem StorePathFor.trans {ctx fact policy c d e}
    (h : StorePathFor ctx fact policy c d) (g : StorePathFor ctx fact policy d e) :
    StorePathFor ctx fact policy c e := by
  induction h with
  | refl => exact g
  | step ht ha hp _ ih => exact .step ht ha hp (ih g)

theorem StorePathFor.weaken {ctx fact policy stronger c d}
    (h : StorePathFor ctx fact policy c d) (imp : ∀ s, stronger s → fact s) :
    StorePathFor ctx stronger policy c d := by
  induction h with
  | refl => exact .refl
  | step ht ha hp _ ih => exact .step (fun s hs => ht s (imp s hs)) ha hp ih

def ReadOnlyExprFor (ctx : ProgramCtx) (fact : Store → Prop) (policy : Config → Prop)
    (env : LocalEnv) (e : Expr) (v : GoValue) : Prop :=
  ∀ k : Continuation, StorePathFor ctx fact policy (.evalE e env k.toMachine) (.retV v k.toMachine)

theorem ReadOnlyExprFor.forget {ctx fact policy env e v}
    (h : ReadOnlyExprFor ctx fact policy env e v) : ReadOnlyExpr ctx fact env e v :=
  fun k => (h k).forget

theorem ReadOnlyExpr.withTrue {ctx fact env e v} (h : ReadOnlyExpr ctx fact env e v) :
    ReadOnlyExprFor ctx fact (fun _ => True) env e v := fun k => (h k).withTrue

theorem ReadOnlyExprFor.weaken {ctx fact policy env e v stronger}
    (h : ReadOnlyExprFor ctx fact policy env e v) (imp : ∀ s, stronger s → fact s) :
    ReadOnlyExprFor ctx stronger policy env e v := fun k => (h k).weaken imp

theorem ReadOnlyExprFor.variable (ctx : ProgramCtx) (env : LocalEnv)
    (id : VarId) (loc : Loc) (v : GoValue) (bound : env.lookup id = some loc)
    (policy : Config → Prop) (allowed : ∀ k, policy (.evalE (.var id) env k)) :
    ReadOnlyExprFor ctx (fun s => loadRoot ctx s loc = .ok v) policy env (.var id) v := by
  intro k
  refine .step ?_ ⟨(by intro h; cases h), rfl⟩ (allowed _) .refl
  intro s hs
  obtain ⟨tr, ht⟩ := read_variable ctx s env k id loc v bound hs
  exact ⟨_, ht, rfl⟩

theorem ReadOnlyExprFor.add_int {ctx fact policy env left right a b} (kind : IntKind)
    (hl : ReadOnlyExprFor ctx fact policy env left (.int a kind))
    (hr : ReadOnlyExprFor ctx fact policy env right (.int b kind))
    (enter : ∀ k, policy (.evalE (.add left right) env k))
    (shift : ∀ k, policy (.retV (.int a kind) (.strictK .add [] [right] env k)))
    (finish : ∀ k, policy (.retV (.int b kind) (.strictK .add [.int a kind] [] env k))) :
    ReadOnlyExprFor ctx fact policy env (.add left right) (.int (kind.normalize (a+b)) kind) := by
  intro k
  apply (StorePathFor.step (d := .evalE left env (.strictK .add [] [right] env k.toMachine))
    (fun _ _ => ⟨_, Step.evalStrict rfl, rfl⟩) ⟨(by intro h; cases h), rfl⟩ (enter _) .refl).trans
  apply (hl _).trans
  apply (StorePathFor.step (d := .evalE right env (.strictK .add [.int a kind] [] env k.toMachine))
    (fun _ _ => ⟨_, Step.strictShift, rfl⟩) ⟨(by intro h; cases h), rfl⟩ (shift _) .refl).trans
  apply (hr _).trans
  refine .step ?_ ⟨(by intro h; cases h), rfl⟩ (finish _) .refl
  intro s _
  have compatible : IntKind.compatibleResult kind kind = some kind := by
    have self : (kind == kind) = true := by
      cases kind <;> try rfl
      rename_i name
      change (name == name) = true
      simp
    simp [IntKind.compatibleResult, self]
  have applyOp : applyStrictOp ctx s (projChainTarget ctx s k.toMachine) .add
      [.int a kind, .int b kind] = .ok (.int (kind.normalize (a+b)) kind, s, []) := by
    simp [applyStrictOp, intBinaryResult, valueAsIntValue, compatible,
      Bind.bind, Except.bind, pure, Except.pure]
  exact ⟨_, Step.strictApply (ch := [])
    (by dsimp only; simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
        rw [applyStrictOpPick_ok_of_none rfl applyOp]; rfl) rfl, rfl⟩

end GoLean.GoCore.Relational
