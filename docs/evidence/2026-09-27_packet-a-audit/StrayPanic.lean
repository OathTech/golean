import GoLean.GoCore.ExecutionStatement
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.ExecutionStatement

def ctx0 : ProgramCtx := ProgramCtx.ofTables #[] #[]
-- one cell: a zero-length int array; `x` is bound to its element 5.
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

def msg0 : String := "runtime error: index out of range [5] with length 0"

theorem step0 (ch : Choices) : stepFn ctx0 s0 c0 ch = .error (.terminal (.panic msg0)) := rfl
theorem loop1 (ch : Choices) : execStmtLoop ctx0 1 s0 c0 ch = .error (.terminal (.panic msg0)) := rfl
theorem abort0 : c0.abort? = none := rfl

/-- The only Prefix from the witness is the empty one. -/
theorem prefix0 {n ch ls sf cf chf} (h : Prefix ctx0 n s0 c0 ch ls sf cf chf) :
    n = 0 ∧ sf = s0 ∧ cf = c0 ∧ chf = ch := by
  cases h with
  | done => exact ⟨rfl, rfl, rfl, rfl⟩
  | step hs _ => rw [step0] at hs; cases hs

theorem not_finish_abort_step : ¬ finish_abort_step_stmt := by
  intro h
  obtain ⟨rec, ch'', hf⟩ := (h ctx0 s0 c0 [] msg0).2 (step0 [])
  cases hf with
  | aborted ha _ _ => rw [abort0] at ha; cases ha

theorem not_run_panic_iff : ¬ run_panic_iff_stmt := by
  intro h
  obtain ⟨n, ls, sf, cf, chf, ch'', rec, _, hp, hf⟩ := (h ctx0 1 s0 c0 [] msg0).1 (loop1 [])
  obtain ⟨rfl, rfl, rfl, rfl⟩ := prefix0 hp
  cases hf with
  | aborted ha _ _ => rw [abort0] at ha; cases ha

theorem not_classTerminal : ¬ ClassTerminal ctx0 1 s0 c0 [] := by
  rintro ⟨t, ht, n, ls, sf, cf, chf, rec, o, cost, hle, hp, hf, hto⟩
  rw [loop1] at ht; cases ht
  obtain ⟨rfl, rfl, rfl, rfl⟩ := prefix0 hp
  cases hf with
  | blocked _ => cases hto
  | aborted ha _ _ => rw [abort0] at ha; cases ha
  | abortRefused _ _ _ => cases hto
  | fatal hs => rw [step0] at hs; cases hs

theorem not_classification : ¬ classification_stmt := by
  intro h
  rcases h ctx0 1 s0 c0 [] with ⟨sf, chf, hok, _⟩ | hT | ⟨hfo, _⟩ | ⟨r, hr, _⟩
  · rw [loop1] at hok; cases hok
  · exact not_classTerminal hT
  · rw [loop1] at hfo; cases hfo
  · rw [loop1] at hr; cases hr

theorem noRefusal0 : NoRefusal ctx0 s0 c0 := by
  intro n ch ls sf cf chf hp
  obtain ⟨rfl, rfl, rfl, rfl⟩ := prefix0 hp
  refine ⟨fun r hr => ?_, fun first rest ha => ?_⟩
  · rw [step0] at hr; cases hr
  · rw [abort0] at ha; cases ha

theorem not_classification_wf : ¬ classification_wf_stmt := by
  intro h
  have hwf : StateWf ctx0 s0 := by decide
  rcases h ctx0 1 s0 c0 [] hwf noRefusal0 with ⟨sf, chf, hok, _⟩ | hT | ⟨hfo, _⟩
  · rw [loop1] at hok; cases hok
  · exact not_classTerminal hT
  · rw [loop1] at hfo; cases hfo

#print axioms not_classification_wf
#print axioms not_run_panic_iff
#print axioms not_finish_abort_step
