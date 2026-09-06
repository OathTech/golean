import GoLean.GoCore.RecoveryEnvironment
import GoLean.GoCore.RecoveryExpressions

namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

inductive ValuesTyped (world : World) : List ValueSort → List GoValue → Prop
  | nil : ValuesTyped world [] []
  | cons {sort sorts v vs} : ValueTyped world sort v → ValuesTyped world sorts vs →
      ValuesTyped world (sort :: sorts) (v :: vs)

theorem ValuesTyped.mono {world next sorts vs} (h : ValuesTyped world sorts vs)
    (ext : Extends world next) : ValuesTyped next sorts vs := by
  induction h with
  | nil => exact .nil
  | cons hv _ ih => exact .cons (hv.mono ext) ih

theorem ValuesTyped.length {world sorts vs} (h : ValuesTyped world sorts vs) :
    sorts.length = vs.length := by induction h <;> simp_all

inductive StrictTyped : StrictOp → List ValueSort → ValueSort → Prop
  | not : StrictTyped .not [.boolean] .boolean
  | eqBoolean : StrictTyped (.eqCmp .bool) [.boolean, .boolean] .boolean
  | neqBoolean : StrictTyped (.neqCmp .bool) [.boolean, .boolean] .boolean
  | eqPayload {ty} : TypeClass ty .payload →
      StrictTyped (.eqCmp ty) [.payload, .payload] .boolean
  | neqPayload {ty} : TypeClass ty .payload →
      StrictTyped (.neqCmp ty) [.payload, .payload] .boolean
  | deref : StrictTyped (.deref .bool) [.root] .boolean
  | box {ty} : TypeClass ty .payload →
      StrictTyped (.toInterface ty .string) [.string] .payload
  | nil {ty} : NilType ty → StrictTyped (.nilLit ty) [] .payload

theorem eq_boolean (s : ExecState) (l r : Bool) :
    valueEq s .bool (.bool l) (.bool r) = .ok (l == r) := by
  unfold valueEq
  simp [TypeEnv.resolve, pure, Except.pure]

/-- The storage invariant allows only nil or a boxed string. Both dynamic
cases are comparable; admission separately restricts source comparison to nil. -/
theorem eq_payload {world ty l r} (s : ExecState) (ht : TypeClass ty .payload)
    (hl : ValueTyped world .payload l) (hr : ValueTyped world .payload r) :
    ∃ b, valueEq s ty l r = .ok b := by
  cases ht with
  | payload hi =>
    cases hl <;> cases hr
    · exact ⟨true, by unfold valueEq; simp [TypeEnv.resolve]; rfl⟩
    · exact ⟨false, by unfold valueEq; simp [TypeEnv.resolve]; rfl⟩
    · exact ⟨false, by unfold valueEq; simp [TypeEnv.resolve]; rfl⟩
    · rename_i left right
      refine ⟨left == right, ?_⟩
      have hd : (Ty.string != Ty.string) = false := rfl
      simp [valueEq, TypeEnv.resolve, tyUncomparable, tyUncomparableTy, pure, Except.pure, hd]

theorem apply_nil {ty} (ht : NilType ty) (s : ExecState) :
    applyStrictOp s (.nilLit ty) [] = .ok (.nil, s) := by
  cases ht with
  | untyped => rfl
  | typed hp => cases hp; rfl

/-- Actual strict-operator application for the whole runtime type surface.
It neither writes the state nor consults a choice stream. -/
theorem StrictTyped.apply {op sorts sort world s vs} (ht : StrictTyped op sorts sort)
    (heap : HeapTyped world s) (hv : ValuesTyped world sorts vs) :
    ∃ v, applyStrictOp s op vs = .ok (v, s) ∧ ValueTyped world sort v := by
  cases ht with
  | not =>
    cases hv with
    | cons h rest =>
      cases rest
      cases h with
      | boolean b => exact ⟨.bool (!b), rfl, .boolean (!b)⟩
  | eqBoolean =>
    cases hv with
    | cons h rest =>
      cases rest with
      | cons h' rest =>
        cases rest
        cases h with
        | boolean l =>
          cases h' with
          | boolean r => exact ⟨.bool (l == r), by simp [applyStrictOp, eq_boolean]; rfl,
              .boolean (l == r)⟩
  | neqBoolean =>
    cases hv with
    | cons h rest =>
      cases rest with
      | cons h' rest =>
        cases rest
        cases h with
        | boolean l =>
          cases h' with
          | boolean r => exact ⟨.bool (!(l == r)), by simp [applyStrictOp, eq_boolean]; rfl,
              .boolean (!(l == r))⟩
  | eqPayload ht =>
    cases hv with
    | cons h rest =>
      cases rest with
      | cons h' rest =>
        cases rest
        obtain ⟨b, hb⟩ := eq_payload s ht h h'
        exact ⟨.bool b, by simp [applyStrictOp, hb]; rfl, .boolean b⟩
  | neqPayload ht =>
    cases hv with
    | cons h rest =>
      cases rest with
      | cons h' rest =>
        cases rest
        obtain ⟨b, hb⟩ := eq_payload s ht h h'
        exact ⟨.bool (!b), by simp [applyStrictOp, hb]; rfl, .boolean (!b)⟩
  | deref =>
    cases hv with
    | cons h rest =>
      cases rest
      cases h with
      | @root a ha =>
        obtain ⟨v, hl, hv⟩ := heap.load ⟨a, rfl, ha⟩
        exact ⟨v, by simp [applyStrictOp, valueAsLoc, hl]; rfl, hv⟩
  | box ht =>
    cases hv with
    | cons h rest =>
      cases rest
      cases h with
      | string bytes => exact ⟨.interface .string (.string bytes), rfl, .boxed bytes⟩
  | nil ht =>
    cases hv
    exact ⟨.nil, apply_nil ht s, .nil⟩

end GoLean.GoCore.RecoveryRuntime
