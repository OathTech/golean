import GoLean.GoCore.RelationalStorePathFor
import GoLean.GoCore.RelationalEventSound

/-! Source policies supplement actual operation effects. Silence is required
only where the read fact or write relation holds, never at a path endpoint. -/
namespace GoLean.GoCore.Relational
open Machine

structure StoreEffectFor (ctx : ProgramCtx) (operation : Store → Store → Prop)
    (policy : State → Prop) (c d : Config) : Prop where
  effect : StoreEffect ctx operation c d
  source_policy : ∀ s t, operation s t → policy ⟨c, s⟩

theorem StoreEffectFor.forget {ctx op policy c d}
    (h : StoreEffectFor ctx op policy c d) : StoreEffect ctx op c d := h.effect

inductive OrderedWritesFor (ctx : ProgramCtx) (policy : State → Prop) :
    List Loc → List GoValue → Config → Config → Prop where
  | nil {c d} : StorePathFor ctx (fun _ => True) (fun c => ∀ s, True → policy ⟨c,s⟩) c d →
      OrderedWritesFor ctx policy [] [] c d
  | cons {l ls v vs c a b d} :
      StorePathFor ctx (fun _ => True) (fun c => ∀ s, True → policy ⟨c,s⟩) c a →
      StoreEffectFor ctx (fun s t => storeLoc ctx s l v = .ok t) policy a b →
      OrderedWritesFor ctx policy ls vs b d → OrderedWritesFor ctx policy (l::ls) (v::vs) c d

theorem OrderedWritesFor.forget {ctx policy ls vs c d}
    (h : OrderedWritesFor ctx policy ls vs c d) : OrderedWrites ctx ls vs c d := by
  induction h with
  | nil p => exact .nil p.forget
  | cons p e _ ih => exact .cons p.forget e.forget ih

inductive OperandPathsFor (ctx : ProgramCtx) (fact : Store → Prop)
    (policy : Config → Prop) (env : LocalEnv) : List Expr → List GoValue → Prop where
  | nil : OperandPathsFor ctx fact policy env [] []
  | cons {e v es vs} : ReadOnlyExprFor ctx fact policy env e v →
      OperandPathsFor ctx fact policy env es vs → OperandPathsFor ctx fact policy env (e::es) (v::vs)

theorem OperandPathsFor.forget {ctx fact policy env es vs}
    (h : OperandPathsFor ctx fact policy env es vs) : OperandPaths ctx fact env es vs := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h.forget ih

namespace Observed
abbrev StorePath (ctx : ProgramCtx) (fact : Store → Prop) :=
  StorePathFor ctx fact (fun c => ∀ s, fact s → Boundary.events ctx ⟨c,s⟩ = [])
abbrev StoreEffect (ctx : ProgramCtx) (operation : Store → Store → Prop) :=
  StoreEffectFor ctx operation (fun a => Boundary.events ctx a = [])
abbrev OrderedWrites (ctx : ProgramCtx) :=
  OrderedWritesFor ctx (fun a => Boundary.events ctx a = [])

theorem StorePath.pure {ctx fact c d}
    (step : ∀ s, Pure ctx ⟨c,s⟩ ⟨d,s⟩) (admitted : StepAdmission c)
    (quiet : ∀ s, fact s → Boundary.events ctx ⟨c,s⟩ = []) : StorePath ctx fact c d :=
  .step (fun s _ => ⟨_, (step s).1, rfl⟩) admitted quiet .refl

theorem StorePath.weaken {ctx fact stronger c d} (h : StorePath ctx fact c d)
    (imp : ∀ s, stronger s → fact s) : StorePath ctx stronger c d := by
  induction h with
  | refl => exact .refl
  | step ht ha hq _ ih =>
    exact .step (fun s hs => ht s (imp s hs)) ha (fun s hs => hq s (imp s hs)) ih

abbrev ReadOnlyExpr (ctx : ProgramCtx) (fact : Store → Prop) (env : LocalEnv)
    (e : Expr) (v : GoValue) :=
  ReadOnlyExprFor ctx fact (fun c => ∀ s, fact s → Boundary.events ctx ⟨c,s⟩ = []) env e v
abbrev OperandPaths (ctx : ProgramCtx) (fact : Store → Prop) (env : LocalEnv) :=
  OperandPathsFor ctx fact (fun c => ∀ s, fact s → Boundary.events ctx ⟨c,s⟩ = []) env

theorem ReadOnlyExpr.weaken {ctx fact stronger env e v}
    (h : ReadOnlyExpr ctx fact env e v) (imp : ∀ s, stronger s → fact s) :
    ReadOnlyExpr ctx stronger env e v := fun k => StorePath.weaken (h k) imp

theorem ReadOnlyExpr.variable (ctx : ProgramCtx) (env : LocalEnv) (id : VarId)
    (loc : Loc) (v : GoValue) (bound : env.lookup id = some loc) :
    ReadOnlyExpr ctx (fun s => loadRoot ctx s loc = .ok v) env (.var id) v :=
  ReadOnlyExprFor.variable ctx env id loc v bound _ (by intros; rfl)

theorem ReadOnlyExpr.reference (ctx : ProgramCtx) (env : LocalEnv) (id : VarId)
    (loc : Loc) (bound : env.lookup id = some loc) :
    ReadOnlyExpr ctx (fun _ => True) env (.ref id) (.addr loc) :=
  fun k => StorePath.pure (fun s => Relational.reference ctx s env k id loc bound)
    ⟨(by intro h; cases h), rfl⟩ (by intros; rfl)

theorem ReadOnlyExpr.add_int {ctx fact env left right a b} (kind : IntKind)
    (hl : ReadOnlyExpr ctx fact env left (.int a kind))
    (hr : ReadOnlyExpr ctx fact env right (.int b kind)) :
    ReadOnlyExpr ctx fact env (.add left right) (.int (kind.normalize (a+b)) kind) :=
  ReadOnlyExprFor.add_int kind hl hr (by intros; rfl) (by intros; rfl) (by intros; rfl)

end Observed
end GoLean.GoCore.Relational
