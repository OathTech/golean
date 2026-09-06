import ReviewedStorage
import Lean

namespace RecoveryStorageIndependent
open GoLean.GoCore GoLean.GoCore.Machine
open GoLean.GoCore.RecoveryTyping GoLean.GoCore.RecoveryRuntime

theorem no_world_without_heap : ¬ HeapTyped #[.boolean] ({} : ExecState) := by
  intro h
  have hh := h.size
  contradiction

theorem boolean_schema_cannot_hide_nil :
    ¬ HeapTyped #[.boolean] ({ heap := #[.value .bool .nil] } : ExecState) := by
  intro h
  obtain ⟨ty, v, he, _, hv⟩ := h.cells 0 .boolean rfl
  have hh : HeapCell.value .bool .nil = .value ty v := Option.some.inj he
  cases hh
  cases hv

theorem extension_cannot_remap : ¬ Extends #[.boolean] #[.payload] := by
  intro h
  have hh := h 0 .boolean rfl
  cases hh

theorem extension_cannot_drop_root : ¬ Extends #[.boolean, .root] #[.boolean] := by
  intro h
  have hh := h 1 .root rfl
  cases hh

theorem normalization_does_not_type (s : ExecState) :
    normalizeValueForTy s .bool .nil = .ok .nil ∧ ¬ ValueTyped #[] .boolean .nil := by
  exact ⟨normalize_typed (.boolean) s .nil, fun h => by cases h⟩

theorem shared_lookup_cannot_justify_incompatible_union {world env} :
    ¬ (EnvTyped world [[("x", .bool)]] env ∧
       EnvTyped world [[("x", .interface ⟨"any"⟩)]] env) := by
  rintro ⟨hb, hp⟩
  have he := hb.compatible hp
    (show Has [[("x", .bool)]] "x" .boolean from ⟨.bool, rfl, .boolean⟩)
    (show Has [[("x", .interface ⟨"any"⟩)]] "x" .payload from
      ⟨.interface ⟨"any"⟩, rfl, .payload rfl⟩)
  cases he

theorem erasure_keeps_placement :
    ¬ ControlStmt #[] false [] (.initialization ⟨"x", .bool⟩) := by
  intro h
  cases h

theorem erasure_is_not_static_admission :
    ControlStmt #[] true [[("x", .bool)]] (.initialization ⟨"x", .bool⟩) ∧
    ¬ Statement #[] true [[("x", .bool)]] (.initialization ⟨"x", .bool⟩) := by
  refine ⟨.initialization (.inl .boolean), ?_⟩
  intro h
  cases h with
  | initialization _ fresh => cases fresh

theorem captured_pointer_gets_slot_not_copied_pointee (b : Bool) :
    bindParams [] { heap := #[.value .bool (.bool b)] }
      [⟨"capture", .pointer .bool⟩] [.addr (.base ⟨0⟩)] =
    .ok ([[ ("capture", .base ⟨1⟩) ]],
      { heap := #[.value .bool (.bool b),
        .value (.pointer .bool) (.addr (.base ⟨0⟩))] }) := by
  with_unfolding_all rfl

theorem strict_box_preserves_arbitrary_bytes (s : ExecState) (bytes : GoLean.GoString) :
    applyStrictOp s (.toInterface (.interface ⟨"any"⟩) .string) [.string bytes] =
      .ok (.interface .string (.string bytes), s) := by
  rfl

theorem alias_dereference_reads_current_cell (b : Bool) :
    applyStrictOp { heap := #[.value .bool (.bool b)] }
      (.deref .bool) [.addr (.base ⟨0⟩)] =
      .ok (.bool b, { heap := #[.value .bool (.bool b)] }) := by
  with_unfolding_all rfl

end RecoveryStorageIndependent

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (name, _) in env.constants.toList do
    let relevant := match env.getModuleIdxFor? name with
      | none => true
      | some idx =>
        let origin := env.header.moduleNames[idx.toNat]!
        origin == `ReviewedStorage || origin.toString.startsWith "GoLean." ||
          origin.toString.startsWith "Tests."
    unless relevant do continue
    for ax in (← collectAxioms name) do
      unless allowed.contains ax do throwError "Independent storage review: {name} uses {ax}"
    count := count + 1
  logInfo s!"Independent recovery storage review: {count} local/imported declarations checked; classical trio only"
