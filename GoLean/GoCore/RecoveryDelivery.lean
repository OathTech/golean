import GoLean.GoCore.RecoveryAllocation
import GoLean.GoCore.RecoveryOperators

/-! Intermediate result classes for the actual machine
continuations. They are structural value predicates, not execution claims. -/
namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

inductive ValueKind where
  | value (sort : ValueSort)
  | typed (ty : Ty)
  | address (sort : ValueSort)
  | boxed
  | closure (fid : FuncId) (captures : List Param)

inductive Delivered (world : World) : ValueKind → GoValue → Prop
  | value {sort v} : ValueTyped world sort v → Delivered world (.value sort) v
  | typed {ty v} : ValueAt world ty v → Delivered world (.typed ty) v
  | address {sort loc} : AddressTyped world sort loc →
      Delivered world (.address sort) (.addr loc)
  | boxed (bytes : GoString) : Delivered world .boxed (.interface .string (.string bytes))
  | closure {fid ps vs} : ParamsValues world ps vs →
      Delivered world (.closure fid ps) (.funcVal fid vs)

theorem Delivered.mono {world next kind v} (h : Delivered world kind v)
    (ext : Extends world next) : Delivered next kind v := by
  cases h with
  | value h => exact .value (h.mono ext)
  | typed h => exact .typed (h.mono ext)
  | address h => exact .address (h.mono ext)
  | boxed bytes => exact .boxed bytes
  | closure h => exact .closure (h.mono ext)

inductive KindLe : ValueKind → ValueKind → Prop
  | refl (kind : ValueKind) : KindLe kind kind
  | toAt {sort ty} : TypeClass ty sort → KindLe (.value sort) (.typed ty)
  | fromAt {sort ty} : TypeClass ty sort → KindLe (.typed ty) (.value sort)
  | rootAddress : KindLe (.value .root) (.address .boolean)
  | boxPayload : KindLe .boxed (.value .payload)

theorem Delivered.coerce {world left right v} (h : Delivered world left v)
    (inc : KindLe left right) : Delivered world right v := by
  cases inc with
  | refl => exact h
  | toAt ht => cases h with | value hv => exact .typed ⟨_, ht, hv⟩
  | fromAt ht => cases h with | typed hv => exact .value (hv.sorted ht)
  | rootAddress =>
    cases h with
    | value hv => cases hv with | root ha => exact .address ⟨_, rfl, ha⟩
  | boxPayload => cases h with | boxed bytes => exact .value (.boxed bytes)

inductive DeliveryList (world : World) : List ValueKind → List GoValue → Prop
  | nil : DeliveryList world [] []
  | cons {kind kinds v vs} : Delivered world kind v → DeliveryList world kinds vs →
      DeliveryList world (kind :: kinds) (v :: vs)

theorem DeliveryList.mono {world next kinds vs} (h : DeliveryList world kinds vs)
    (ext : Extends world next) : DeliveryList next kinds vs := by
  induction h with
  | nil => exact .nil
  | cons hv _ ih => exact .cons (hv.mono ext) ih

theorem DeliveryList.length {world kinds vs} (h : DeliveryList world kinds vs) :
    kinds.length = vs.length := by induction h <;> simp_all

theorem DeliveryList.append {world kinds kinds' vs vs'}
    (h : DeliveryList world kinds vs) (h' : DeliveryList world kinds' vs') :
    DeliveryList world (kinds ++ kinds') (vs ++ vs') := by
  induction h with
  | nil => exact h'
  | cons hv _ ih => exact .cons hv ih

theorem DeliveryList.reverse {world kinds vs} (h : DeliveryList world kinds vs) :
    DeliveryList world kinds.reverse vs.reverse := by
  induction h with
  | nil => exact .nil
  | cons hv _ ih => simpa using ih.append (.cons hv .nil)

theorem DeliveryList.values {world sorts vs}
    (h : DeliveryList world (sorts.map ValueKind.value) vs) : ValuesTyped world sorts vs := by
  induction sorts generalizing vs with
  | nil => cases h; exact .nil
  | cons sort sorts ih =>
    cases h with
    | cons hv rest => cases hv with | value hv => exact .cons hv (ih rest)

theorem DeliveryList.params {world ps vs}
    (h : DeliveryList world (ps.map (fun p => ValueKind.typed p.typ)) vs) :
    ParamsValues world ps vs := by
  induction ps generalizing vs with
  | nil => cases h; exact .nil
  | cons p ps ih =>
    cases h with
    | cons hv rest => cases hv with | typed hv => exact .cons hv (ih rest)

inductive Operator : StrictOp → List ValueKind → ValueKind → Prop
  | plain {op sorts sort} : StrictTyped op sorts sort →
      Operator op (sorts.map ValueKind.value) (.value sort)
  | boxed {target} : TypeClass target .payload →
      Operator (.toInterface target .string) [.value .string] .boxed
  | closure (fid : FuncId) (ps : List Param) :
      Operator (.funcValOf fid) (ps.map (fun p => .typed p.typ)) (.closure fid ps)

theorem Operator.apply {world s op kinds kind vs} (h : Operator op kinds kind)
    (heap : HeapTyped world s) (hv : DeliveryList world kinds vs) :
    ∃ v, applyStrictOp s op vs = .ok (v, s) ∧ Delivered world kind v := by
  cases h with
  | plain h =>
    obtain ⟨v, run, hv⟩ := h.apply heap hv.values
    exact ⟨v, run, .value hv⟩
  | boxed ht =>
    cases hv with
    | cons hv rest =>
      cases rest
      cases hv with
      | value hv =>
        cases hv with
        | string bytes => exact ⟨.interface .string (.string bytes), rfl, .boxed bytes⟩
  | closure fid ps => exact ⟨.funcVal fid vs, rfl, .closure hv.params⟩

end GoLean.GoCore.RecoveryRuntime
