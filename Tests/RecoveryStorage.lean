import GoLean.GoCore.RecoveryControlTyping
import GoLean.GoCore.RecoveryAllocation
import GoLean.GoCore.RecoveryOperators

namespace GoLean.GoCore.RecoveryRuntime.Tests
open RecoveryTyping Machine

def payloadTy : Ty := .interface ⟨"any"⟩

/-- A pointer slot at a valid address cannot justify a dangling pointee. -/
theorem dangling_pointer_rejected :
    ¬ ValueTyped #[.boolean, .root] .root (.addr (.base ⟨7⟩)) := by
  intro h
  cases h with
  | root h => simp at h

/-- Being in bounds is insufficient: the pointee must be Boolean. -/
theorem wrong_pointee_rejected :
    ¬ ValueTyped #[.payload, .root] .root (.addr (.base ⟨0⟩)) := by
  intro h
  cases h with
  | root h => cases h

theorem nil_is_not_a_live_root (world : World) : ¬ ValueTyped world .root .nil := by
  intro h
  cases h

/-- Lookup of the visible binding succeeds, but a hidden dangling binding
still violates the environment's independent structural requirement. -/
theorem hidden_dangling_binding_rejected :
    ¬ EnvTyped #[.boolean] [[("x", .bool)]]
      [[("x", .base ⟨0⟩)], [("x", .base ⟨7⟩)]] := by
  intro h
  obtain ⟨sort, a, he, ha⟩ := h.bindings [("x", .base ⟨7⟩)] (by simp)
    ("x", .base ⟨7⟩) (by simp)
  cases he
  simp at ha

theorem mixed_shadow_uses_inner_lookup :
    Has [[("x", payloadTy)], [("x", .bool)]] "x" .payload := by
  exact ⟨payloadTy, rfl, .payload rfl⟩

theorem mixed_shadow_cannot_use_hidden_boolean :
    ¬ Has [[("x", payloadTy)], [("x", .bool)]] "x" .boolean := by
  rintro ⟨ty, hl, ht⟩
  have he : ty = payloadTy := Option.some.inj hl.symm
  subst ty
  cases ht

/-- A same-name declaration changes the sort. The old heterogeneous tail
cannot be carried through it by a Boolean-style name-inclusion argument. -/
theorem declaration_does_not_preserve_old_sort :
    ¬ Included [[("x", payloadTy)]]
      (RecoveryTyping.declare [[("x", payloadTy)]] ⟨"x", .bool⟩) := by
  intro h
  obtain ⟨ty, hl, ht⟩ := h "x" .payload ⟨payloadTy, rfl, .payload rfl⟩
  have he : ty = .bool := Option.some.inj hl.symm
  subst ty
  cases ht

/-- A root pointer remains live after any type-correct store, including a
write through another captured alias of the same Boolean cell. -/
theorem aliases_remain_live_after_write {world s loc v pointer sort}
    (heap : HeapTyped world s) (address : AddressTyped world sort loc)
    (value : ValueTyped world sort v) (captured : ValueTyped world .root pointer) :
    ∃ s' target, storeLoc s loc v = .ok s' ∧ pointer = .addr target ∧
      BooleanRuntime.BoolRoot s' target := by
  obtain ⟨s', run, heap', _, _⟩ := heap.store address value
  obtain ⟨target, hp, live⟩ := heap'.live_reference captured
  exact ⟨s', target, run, hp, live⟩

def aliasState (b : Bool) : ExecState := { heap := #[
  .value .bool (.bool b),
  .value (.pointer .bool) (.addr (.base ⟨0⟩)),
  .value (.pointer .bool) (.addr (.base ⟨0⟩))] }

/-- Both stored captures keep the original shared target while its value
changes; the machine does not copy the pointee at capture or at store. -/
theorem write_keeps_both_actual_aliases (before after : Bool) :
    storeLoc (aliasState before) (.base ⟨0⟩) (.bool after) = .ok (aliasState after) ∧
    loadMany (aliasState after) [.base ⟨1⟩, .base ⟨2⟩] =
      .ok [.addr (.base ⟨0⟩), .addr (.base ⟨0⟩)] ∧
    loadLoc (aliasState after) (.base ⟨0⟩) = .ok (.bool after) := by
  constructor
  · with_unfolding_all rfl
  constructor <;> with_unfolding_all rfl

theorem arbitrary_payload_bytes_comparable (s : ExecState) (world : World)
    (left right : GoString) :
    ∃ b, valueEq s payloadTy (.interface .string (.string left))
      (.interface .string (.string right)) = .ok b :=
  eq_payload (world := world) s (.payload rfl) (.boxed left) (.boxed right)

theorem zero_interface_is_nil (world : World) (s : ExecState) :
    ∃ sort v, defaultValue s payloadTy = .ok v ∧ TypeClass payloadTy sort ∧
      ValueTyped world sort v :=
  default_storage (.inr (.payload rfl)) world s

theorem pointer_local_cannot_gain_liveness_by_default : ¬ StorageType (.pointer .bool) := by
  rintro (h | h) <;> cases h

end GoLean.GoCore.RecoveryRuntime.Tests
