import GoLean.GoCore.ExecutionStatement
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.ExecutionStatement

-- The packet A audit's F1 witness, verbatim (docs/evidence/2026-09-27_packet-a-audit/StrayPanic.lean @ e750e13c).
def ctx0 : ProgramCtx := ProgramCtx.ofTables #[] #[]
def s0 : Store := { heap := #[.value (.array 0 .int) (.array #[])] }
def env0 : LocalEnv := [[("x", .index (.base ⟨0⟩) 5)]]
def c0 : Config := .evalE (.var "x") env0 .stop

#eval c0.abort?.isSome
#eval match stepFn ctx0 s0 c0 ([] : Choices) with
  | .ok _ => "ok" | .error e => s!"{repr e}"
#eval match execStmtLoop ctx0 1 s0 c0 ([] : Choices) with
  | .ok _ => "ok" | .error e => s!"{repr e}"
#eval match execStmtLoop ctx0 0 s0 c0 ([] : Choices) with
  | .ok _ => "ok" | .error e => s!"{repr e}"

-- After #eval: the witness is classified as a REFUSAL (ClassRefusal), at fuel 1, for every tape.
theorem f1_witness_refusal (ch : Choices) : ClassRefusal ctx0 1 s0 c0 ch :=
  ⟨_, rfl, 0, [], s0, c0, ch, Nat.le_refl 1, .done, Or.inl rfl⟩

/-- And NOT a terminal: execStmtLoop at the witness is not `.error (.terminal _)`. -/
theorem f1_witness_not_terminal (ch : Choices) : ¬ ClassTerminal ctx0 1 s0 c0 ch := by
  rintro ⟨t, h, _⟩
  obtain ⟨r, hr, _⟩ := f1_witness_refusal ch
  rw [hr] at h; cases h

#print axioms f1_witness_refusal
#print axioms f1_witness_not_terminal
