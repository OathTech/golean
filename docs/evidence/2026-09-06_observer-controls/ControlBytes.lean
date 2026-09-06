import GoLean.Interface

open GoLean GoLean.GoCore GoLean.GoCore.Machine

-- The model already preserves the bytes which the old Bash observer lost.
-- These are kernel controls, not a generic UTF-8 correctness theorem.
theorem observer_nul_soh_model : renderPanicHead {types := TypeEnv.reserved}
    ⟨.interface .string (.string ⟨#[97, 0, 98, 1, 99]⟩), false⟩ [] =
    some (String.ofList ['a', Char.ofNat 0, 'b', Char.ofNat 1, 'c']) := by
  decide +kernel

theorem observer_controls_first_line : renderPanicHead {types := TypeEnv.reserved}
    ⟨.interface .string (.string ⟨#[97, 0, 1, 9, 13, 10, 98]⟩), false⟩ [] =
    some (String.ofList ['a', Char.ofNat 0, Char.ofNat 1, '\t', '\r']) := by
  decide +kernel

#print axioms observer_nul_soh_model
#print axioms observer_controls_first_line
