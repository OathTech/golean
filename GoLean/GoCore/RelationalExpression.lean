import GoLean.GoCore.RelationalStorePath

/-! Compositional read-only expression evaluation. Every saved continuation is
supported; actual access labels and source admission are retained by StorePath.
Successful read premises concern the pre-store, not any later write. -/
namespace GoLean.GoCore.Relational
open Machine

/-- Store-uniform expression evaluation at every continuation. This includes
intermediate preservation and admission, rather than just equal endpoints. -/
def ReadOnlyExpr (ctx : ProgramCtx) (fact : Store → Prop) (env : LocalEnv)
    (e : Expr) (v : GoValue) : Prop :=
  ∀ k : Continuation, StorePath ctx fact (.evalE e env k.toMachine) (.retV v k.toMachine)

theorem ReadOnlyExpr.weaken {ctx fact env e v} (h : ReadOnlyExpr ctx fact env e v)
    {stronger : Store → Prop} (implies : ∀ s, stronger s → fact s) :
    ReadOnlyExpr ctx stronger env e v := fun k => (h k).weaken implies

theorem ReadOnlyExpr.variable (ctx : ProgramCtx) (env : LocalEnv)
    (id : VarId) (loc : Loc) (v : GoValue) (bound : LocalEnv.lookup env id = some loc) :
    ReadOnlyExpr ctx (fun s => loadRoot ctx s loc = .ok v) env (.var id) v := by
  intro k
  refine .step ?_ ⟨(by intro h; cases h), rfl⟩ .refl
  intro s hs
  obtain ⟨tr, ht⟩ := read_variable ctx s env k id loc v bound hs
  exact ⟨_, ht, rfl⟩

theorem ReadOnlyExpr.reference (ctx : ProgramCtx) (env : LocalEnv)
    (id : VarId) (loc : Loc) (bound : LocalEnv.lookup env id = some loc) :
    ReadOnlyExpr ctx (fun _ => True) env (.ref id) (.addr loc) :=
  fun k => .pure (fun s => Relational.reference ctx s env k id loc bound)
    ⟨(by intro h; cases h), rfl⟩

theorem ReadOnlyExpr.int_literal (ctx : ProgramCtx) (env : LocalEnv) (v : Int) (kind : IntKind) :
    ReadOnlyExpr ctx (fun _ => True) env (.intLit v kind) (.int (kind.normalize v) kind) :=
  fun k => .pure (fun s => Relational.int_literal ctx v kind env k s)
    ⟨(by intro h; cases h), rfl⟩

/-- Dereference a read-only pointer expression, including an interior pointee.
The annotation is carried by the source; successful loadLoc supplies the value. -/
theorem ReadOnlyExpr.deref {ctx : ProgramCtx} {fact : Store → Prop} {env : LocalEnv}
    {e : Expr} {target : Loc} {v : GoValue} (ty : Ty)
    (pointer : ReadOnlyExpr ctx fact env e (.addr target))
    (read : ∀ s, fact s → loadLoc ctx s target = .ok v) :
    ReadOnlyExpr ctx fact env (.deref e ty) v := by
  intro k
  apply (StorePath.pure (d := .evalE e env (.strictK (.deref ty) [] [] env k.toMachine))
    (fun _ => ⟨Step.evalStrict rfl, rfl⟩) ⟨(by intro h; cases h), rfl⟩).trans
  apply (pointer _).trans
  refine .step ?_ ⟨(by intro h; cases h), rfl⟩ .refl
  intro s hs
  have applyOp : applyStrictOp ctx s (projChainTarget ctx s k.toMachine) (.deref ty) [.addr target] =
      .ok (v, s, [.access .read (.data (projChainTarget ctx s k.toMachine target).canon)]) := by
    simp [applyStrictOp, valueAsLoc, Mem.loadFor, read s hs, Bind.bind, Except.bind, pure, Except.pure]
  exact ⟨_, Step.strictApply (ch := [])
    (by dsimp only; simp only [List.reverse_cons, List.reverse_nil, List.nil_append]; rw [applyStrictOpPick_ok_of_none rfl applyOp]; rfl) rfl, rfl⟩

/-- Integer addition composes two read-only operands of the same kind.
Normalization is the semantic kind's modular/signed result, not host arithmetic. -/
theorem ReadOnlyExpr.add_int {ctx : ProgramCtx} {fact : Store → Prop} {env : LocalEnv}
    {left right : Expr} {a b : Int} (kind : IntKind)
    (hl : ReadOnlyExpr ctx fact env left (.int a kind))
    (hr : ReadOnlyExpr ctx fact env right (.int b kind)) :
    ReadOnlyExpr ctx fact env (.add left right) (.int (kind.normalize (a + b)) kind) := by
  intro k
  apply (StorePath.pure (d := .evalE left env (.strictK .add [] [right] env k.toMachine))
    (fun _ => ⟨Step.evalStrict rfl, rfl⟩) ⟨(by intro h; cases h), rfl⟩).trans
  apply (hl _).trans
  apply (StorePath.pure (d := .evalE right env (.strictK .add [.int a kind] [] env k.toMachine))
    (fun _ => ⟨Step.strictShift, rfl⟩) ⟨(by intro h; cases h), rfl⟩).trans
  apply (hr _).trans
  refine .step ?_ ⟨(by intro h; cases h), rfl⟩ .refl
  intro s _
  have compatible : IntKind.compatibleResult kind kind = some kind := by
    have self : (kind == kind) = true := by
      cases kind <;> try rfl
      rename_i name
      change (name == name) = true
      simp
    simp [IntKind.compatibleResult, self]
  have applyOp : applyStrictOp ctx s (projChainTarget ctx s k.toMachine) .add
      [.int a kind, .int b kind] = .ok (.int (kind.normalize (a + b)) kind, s, []) := by
    simp [applyStrictOp, intBinaryResult, valueAsIntValue, compatible,
      Bind.bind, Except.bind, pure, Except.pure]
  exact ⟨_, Step.strictApply (ch := [])
    (by dsimp only; simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; rw [applyStrictOpPick_ok_of_none rfl applyOp]; rfl) rfl, rfl⟩

/-- Less-than composes read-only integer operands. It compares the supplied
values directly, without normalization or a representability premise. -/
theorem ReadOnlyExpr.less_int {ctx : ProgramCtx} {fact : Store → Prop} {env : LocalEnv}
    {left right : Expr} {a b : Int} (kind : IntKind)
    (hl : ReadOnlyExpr ctx fact env left (.int a kind))
    (hr : ReadOnlyExpr ctx fact env right (.int b kind)) :
    ReadOnlyExpr ctx fact env (.lessCmp left right) (.bool (decide (a < b))) := by
  intro k
  apply (StorePath.pure (d := .evalE left env (.strictK .lessCmp [] [right] env k.toMachine))
    (fun _ => ⟨Step.evalStrict rfl, rfl⟩) ⟨(by intro h; cases h), rfl⟩).trans
  apply (hl _).trans
  apply (StorePath.pure (d := .evalE right env (.strictK .lessCmp [.int a kind] [] env k.toMachine))
    (fun _ => ⟨Step.strictShift, rfl⟩) ⟨(by intro h; cases h), rfl⟩).trans
  apply (hr _).trans
  refine .step ?_ ⟨(by intro h; cases h), rfl⟩ .refl
  intro s _
  have applyOp : applyStrictOp ctx s (projChainTarget ctx s k.toMachine) .lessCmp
      [.int a kind, .int b kind] = .ok (.bool (decide (a < b)), s, []) := by
    simp [applyStrictOp, valueLess, Bind.bind, Except.bind, pure, Except.pure]
  exact ⟨_, Step.strictApply (ch := [])
    (by dsimp only; simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; rw [applyStrictOpPick_ok_of_none rfl applyOp]; rfl) rfl, rfl⟩

end GoLean.GoCore.Relational
