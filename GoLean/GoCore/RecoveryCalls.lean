import GoLean.GoCore.RecoveryExpressions

namespace GoLean.GoCore.RecoveryTyping

inductive Arguments (Γ : Context) : List Expr → List Param → Prop
  | nil : Arguments Γ [] []
  | cons {e es p ps} : ExprAt Γ e p.typ → Arguments Γ es ps →
      Arguments Γ (e :: es) (p :: ps)

def checkArguments (Γ : Context) : List Expr → List Param → Bool
  | [], [] => true
  | e :: es, p :: ps => checkExprAt Γ e p.typ && checkArguments Γ es ps
  | _, _ => false

theorem checkArguments_iff (Γ : Context) (es : List Expr) (ps : List Param) :
    checkArguments Γ es ps = true ↔ Arguments Γ es ps := by
  constructor
  · induction es generalizing ps with
    | nil =>
        cases ps with
        | nil => exact fun _ => .nil
        | cons => simp [checkArguments]
    | cons e es ih =>
        cases ps with
        | nil => simp [checkArguments]
        | cons p ps =>
            simp only [checkArguments, Bool.and_eq_true]
            exact fun h => .cons ((checkExprAt_iff _ _ _).mp h.1) (ih _ h.2)
  · intro h; induction h <;> simp_all [checkArguments, checkExprAt_iff]

instance (Γ : Context) (es : List Expr) (ps : List Param) : Decidable (Arguments Γ es ps) :=
  decidable_of_iff (checkArguments Γ es ps = true) (checkArguments_iff Γ es ps)

theorem Arguments.length {Γ es ps} (h : Arguments Γ es ps) : es.length = ps.length := by
  induction h <;> simp_all

inductive Targets (Γ : Context) : List Assignee → List Param → Prop
  | nil : Targets Γ [] []
  | cons {a as p ps} : TargetAt Γ a p.typ → Targets Γ as ps →
      Targets Γ (a :: as) (p :: ps)

def checkTargets (Γ : Context) : List Assignee → List Param → Bool
  | [], [] => true
  | a :: as, p :: ps => checkTargetAt Γ a p.typ && checkTargets Γ as ps
  | _, _ => false

theorem checkTargets_iff (Γ : Context) (as : List Assignee) (ps : List Param) :
    checkTargets Γ as ps = true ↔ Targets Γ as ps := by
  constructor
  · induction as generalizing ps with
    | nil =>
        cases ps with
        | nil => exact fun _ => .nil
        | cons => simp [checkTargets]
    | cons a as ih =>
        cases ps with
        | nil => simp [checkTargets]
        | cons p ps =>
            simp only [checkTargets, Bool.and_eq_true]
            exact fun h => .cons ((checkTargetAt_iff _ _ _).mp h.1) (ih _ h.2)
  · intro h; induction h <;> simp_all [checkTargets, checkTargetAt_iff]

instance (Γ : Context) (as : List Assignee) (ps : List Param) : Decidable (Targets Γ as ps) :=
  decidable_of_iff (checkTargets Γ as ps = true) (checkTargets_iff Γ as ps)

theorem Targets.length {Γ as ps} (h : Targets Γ as ps) : as.length = ps.length := by
  induction h <;> simp_all

inductive Captures (Γ : Context) : List Expr → Prop
  | nil : Captures Γ []
  | cons {e es} : ExprTyped Γ e .root → Captures Γ es → Captures Γ (e :: es)

def checkCaptures (Γ : Context) : List Expr → Bool
  | [] => true
  | e :: es => checkExpr Γ e .root && checkCaptures Γ es

theorem checkCaptures_iff (Γ : Context) (es : List Expr) :
    checkCaptures Γ es = true ↔ Captures Γ es := by
  constructor
  · induction es with
    | nil => exact fun _ => .nil
    | cons e es ih =>
        simp only [checkCaptures, Bool.and_eq_true]
        exact fun h => .cons ((checkExpr_iff _ _ _).mp h.1) (ih h.2)
  · intro h; induction h <;> simp_all [checkCaptures, checkExpr_iff]

instance (Γ : Context) (es : List Expr) : Decidable (Captures Γ es) :=
  decidable_of_iff (checkCaptures Γ es = true) (checkCaptures_iff Γ es)

/-- Lookup and complete arity/type vectors for an ordinary direct call. -/
def DirectCall (fs : Array Func) (Γ : Context) (targets : Array Assignee)
    (fid : FuncId) (args : Array Expr) : Prop :=
  ∃ f, findFunctionIn? fs fid = some f ∧
    Arguments Γ args.toList f.args.toList ∧ Targets Γ targets.toList f.results.toList

def checkDirectCall (fs : Array Func) (Γ : Context) (targets : Array Assignee)
    (fid : FuncId) (args : Array Expr) : Bool :=
  match findFunctionIn? fs fid with
  | none => false
  | some f => checkArguments Γ args.toList f.args.toList &&
      checkTargets Γ targets.toList f.results.toList

theorem checkDirectCall_iff (fs : Array Func) (Γ : Context) (targets : Array Assignee)
    (fid : FuncId) (args : Array Expr) :
    checkDirectCall fs Γ targets fid args = true ↔ DirectCall fs Γ targets fid args := by
  unfold checkDirectCall DirectCall
  cases h : findFunctionIn? fs fid <;>
    simp [checkArguments_iff, checkTargets_iff]

/-- Captures are typed root expressions, occupy the actual parameter prefix,
and are prepended to explicit arguments exactly as frame entry does. -/
inductive ClosureCall (fs : Array Func) (Γ : Context) (targets : Array Assignee)
    (args : Array Expr) : Expr → Prop
  | known {fid caps f} : findFunctionIn? fs fid = some f → Captures Γ caps.toList →
      Arguments Γ (caps.toList ++ args.toList) f.args.toList →
      Targets Γ targets.toList f.results.toList →
      ClosureCall fs Γ targets args (.funcVal fid caps)

def checkClosureCall (fs : Array Func) (Γ : Context) (targets : Array Assignee)
    (args : Array Expr) : Expr → Bool
  | .funcVal fid caps =>
      match findFunctionIn? fs fid with
      | none => false
      | some f => checkCaptures Γ caps.toList &&
          checkArguments Γ (caps.toList ++ args.toList) f.args.toList &&
          checkTargets Γ targets.toList f.results.toList
  | _ => false

theorem checkClosureCall_iff (fs : Array Func) (Γ : Context) (targets : Array Assignee)
    (args : Array Expr) (callee : Expr) :
    checkClosureCall fs Γ targets args callee = true ↔ ClosureCall fs Γ targets args callee := by
  constructor
  · intro h
    cases callee <;> try (simp only [checkClosureCall, Bool.false_eq_true] at h)
    case funcVal fid caps =>
      split at h
      · contradiction
      · rename_i f hf
        simp only [Bool.and_eq_true] at h
        exact .known hf ((checkCaptures_iff _ _).mp h.1.1)
          ((checkArguments_iff _ _ _).mp h.1.2) ((checkTargets_iff _ _ _).mp h.2)
  · intro h
    cases h with
    | known hf hc ha ht =>
        simp [checkClosureCall, hf, checkCaptures_iff, checkArguments_iff, checkTargets_iff,
          hc, ha, ht]

/-- Deferred invocation checks the same complete input vector, but has no
ordinary result-target constraint: Go deliberately discards deferred results. -/
inductive DeferredCall (fs : Array Func) (Γ : Context) (args : Array Expr) : Expr → Prop
  | known {fid caps f} : findFunctionIn? fs fid = some f → Captures Γ caps.toList →
      Arguments Γ (caps.toList ++ args.toList) f.args.toList →
      DeferredCall fs Γ args (.funcVal fid caps)

def checkDeferredCall (fs : Array Func) (Γ : Context) (args : Array Expr) : Expr → Bool
  | .funcVal fid caps =>
      match findFunctionIn? fs fid with
      | none => false
      | some f => checkCaptures Γ caps.toList &&
          checkArguments Γ (caps.toList ++ args.toList) f.args.toList
  | _ => false

theorem checkDeferredCall_iff (fs : Array Func) (Γ : Context) (args : Array Expr)
    (callee : Expr) :
    checkDeferredCall fs Γ args callee = true ↔ DeferredCall fs Γ args callee := by
  constructor
  · intro h
    cases callee <;> try (simp only [checkDeferredCall, Bool.false_eq_true] at h)
    case funcVal fid caps =>
      split at h
      · contradiction
      · rename_i f hf
        simp only [Bool.and_eq_true] at h
        exact .known hf ((checkCaptures_iff _ _).mp h.1) ((checkArguments_iff _ _ _).mp h.2)
  · intro h
    cases h with
    | known hf hc ha =>
        simp [checkDeferredCall, hf, checkCaptures_iff, checkArguments_iff, hc, ha]

end GoLean.GoCore.RecoveryTyping
