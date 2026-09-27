import GoLean.GoCore.ExecutionStatement
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.ExecutionStatement

/-! Stray-panic refusal audit (2026-09-27, [AGENT] auditor): the packet A audit's F1
witness (docs/evidence/2026-09-27_packet-a-audit/StrayPanic.lean @ e750e13c), re-run
over the candidate's core (tree 36d8571b = candidate 05d0dbd4 + packet A's two statement
files; GoLean/GoCore otherwise identical). -/

def ctx0 : ProgramCtx := ProgramCtx.ofTables #[] #[]
def s0 : Store := { heap := #[.value (.array 0 .int) (.array #[])] }
def env0 : LocalEnv := [[("x", .index (.base ⟨0⟩) 5)]]
def c0 : Config := .evalE (.var "x") env0 .stop

#eval c0.abort?.isSome
#eval match stepFn ctx0 s0 c0 ([] : Choices) with
  | .ok _ => "ok" | .error e => s!"{repr e}"
#eval match execStmtLoop ctx0 1 s0 c0 ([] : Choices) with
  | .ok _ => "ok" | .error e => s!"{repr e}"
#eval decide (MachineWf ctx0 s0 c0)
#eval decide (StateWf ctx0 s0)

/-- The audit's `step0` now: the named `.internal` refusal, for every tape. -/
theorem step0' (ch : Choices) : ∃ m, stepFn ctx0 s0 c0 ch = .error (.refusal (.internal m)) :=
  ⟨_, rfl⟩
theorem loop1' (ch : Choices) : ∃ m, execStmtLoop ctx0 1 s0 c0 ch = .error (.refusal (.internal m)) :=
  ⟨_, rfl⟩

/-- Classified: case 4 (`ClassRefusal`), every tape. -/
theorem witness_classRefusal (ch : Choices) : ClassRefusal ctx0 1 s0 c0 ch :=
  ⟨_, rfl, 0, [], s0, c0, ch, Nat.le_refl 1, .done, Or.inl rfl⟩

/-- And EXCLUDED by the corollary's domain premise: `NoRefusal` is false at the witness
(so `classification_wf_stmt` is no longer refuted by it). -/
theorem witness_not_noRefusal : ¬ NoRefusal ctx0 s0 c0 := by
  intro h
  have hz : ¬ ZeroCost c0 := by
    rintro (h | ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩) <;> cases h
  obtain ⟨m, hm⟩ := step0' []
  exact (h 0 [] [] s0 c0 [] .done).1 hz (.internal m) hm

/-- The ← direction of `finish_abort_step_stmt` at the witness is now vacuous: stepFn
is not a panic terminal there. -/
theorem witness_not_panic (ch : Choices) (t : String) :
    stepFn ctx0 s0 c0 ch ≠ .error (.terminal (.panic t)) := by
  obtain ⟨m, hm⟩ := step0' ch; rw [hm]; intro h; cases h

#print axioms witness_classRefusal
#print axioms witness_not_noRefusal
#print axioms witness_not_panic

/-! S5 positive control (absent from the lane's `strayPanicRefusalFacts`): a ROOT unseq
guard test binder is read unchanged — value, label, and the activate/skip decision. -/
def s1 : Store := { heap := #[.value .bool (.bool true)] }
#eval match unseqGuard ctx0 s1 default [[("b", .base ⟨0⟩)]] [.active] 0 "b" true "o" with
  | .ok (st, s', tr) => s!"ok st={repr st} sameStore={s' == s1} tr={repr tr}"
  | .error e => s!"{repr e}"
theorem s5_positive :
    unseqGuard ctx0 s1 default [[("b", .base ⟨0⟩)]] [.active] 0 "b" true "o"
      = .ok ([.done], s1, [.access .read (.data (.base ⟨0⟩))]) := by rfl

