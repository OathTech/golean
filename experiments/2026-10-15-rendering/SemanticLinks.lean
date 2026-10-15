import GoLean.GoCore.StepFn

/-! Representative diagnostic sites use the total public rendering definitions.
All binders are unrestricted; no state validity or successful execution is assumed. -/
open GoLean GoLean.GoCore GoLean.GoCore.Machine
namespace GoLean.RendererLinks

theorem dynamic_type_refusal (ty : Ty) (h : ty.mentionsUnsupported = true) :
    checkedDynamicTy ty = .error (.refusal (.unsupported
      s!"interface conversion for dynamic type {Ty.render ty 0}")) := by
  simp only [checkedDynamicTy, h, ↓reduceIte]
  rfl

theorem valueEq_bool_unit (ctx : ProgramCtx) (r : GoValue) :
    valueEq ctx .bool .unit r = .error (.refusal (.stuck
      s!"bool equality expected bool operands, got {GoValue.render .unit 0} and {GoValue.render r 0}")) := by
  simp only [valueEq, TypeEnv.resolve, pure, Except.pure]
  rfl

theorem preprint_unboxed (ctx : ProgramCtx) (s : Store) (v : GoValue)
    (m : Declaration.MemberId) (recovered repanicked : Bool)
    (h : match v with | .interface _ _ => False | _ => True) :
    preprintDispatch ctx s ⟨v, recovered, .pending m, repanicked⟩ =
      .error (.refusal (.internal
        s!"preprint: a pending rewrite on an unboxed payload {GoValue.render v 0}")) := by
  cases v <;> first | contradiction | rfl

theorem unseq_nonatom (ctx : ProgramCtx) (env : LocalEnv) (s : Store) (e : Expr)
    (h : match e with
      | .var _ | .ref _ | .intLit _ _ | .boolLit _ | .stringLit _ => False
      | _ => True) :
    unseqAtom ctx env s e = .error (.refusal (.stuck
      s!"unseq: target operand is not an atom (a slot, an admitted local, the address of a local, or an int/bool/string constant): {Expr.render e 0}")) := by
  cases e <;> first | contradiction | rfl

end GoLean.RendererLinks
