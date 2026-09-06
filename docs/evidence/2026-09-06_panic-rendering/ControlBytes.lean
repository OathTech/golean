import GoLean.Interface
open GoLean GoLean.GoCore GoLean.GoCore.Machine

example : renderPanicHead {types := TypeEnv.reserved}
    ⟨.interface .string (.string ⟨#[97, 0, 98, 1, 99]⟩), false⟩ [] =
      some (String.ofList ['a', Char.ofNat 0, 'b', Char.ofNat 1, 'c']) := by
  decide +kernel
