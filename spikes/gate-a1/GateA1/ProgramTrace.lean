import GateA1.PoolTrace

namespace GoLean.GateA1.Pool
open GoCore GoCore.Machine

/-- Complete entry/readout contract for the shipped program driver.
Setup is still an executable premise, not a claimed typed-admission proof.
It uses the SAME fuel parameter as the subject loop, just as the driver does.
-/
inductive ProgramRun (fuel : Nat) (p : Program) (name : String)
    (args : Array GoValue) (ch : Choices) : RunResult → Prop where
  | setupError : runProgramSetupM fuel p name args ch = .error e →
      ProgramRun fuel p name args ch (.error (e, GoString.empty))
  | runError : runProgramSetupM fuel p name args ch = .ok (c, s, locs, ch₁) →
      Run fuel ⟨#[Thread.running c none], s, 0⟩ {} ch₁ GoString.empty (out, .error e) →
      ProgramRun fuel p name args ch (.error (e, out))
  | readError : runProgramSetupM fuel p name args ch = .ok (c, s, locs, ch₁) →
      Run fuel ⟨#[Thread.running c none], s, 0⟩ {} ch₁ GoString.empty (out, .ok (sf, chf)) →
      loadMany sf locs = .error e →
      ProgramRun fuel p name args ch (.error (e, out))
  | done : runProgramSetupM fuel p name args ch = .ok (c, s, locs, ch₁) →
      Run fuel ⟨#[Thread.running c none], s, 0⟩ {} ch₁ GoString.empty (out, .ok (sf, chf)) →
      loadMany sf locs = .ok vs →
      ProgramRun fuel p name args ch (.ok { values := vs.toArray, output := out })

theorem program_run_iff {fuel p name args ch result} :
    runProgramPoolOutM fuel p name args ch = result ↔ ProgramRun fuel p name args ch result := by
  constructor
  · intro h
    unfold runProgramPoolOutM at h
    cases hs : runProgramSetupM fuel p name args ch with
    | error e => simp only [hs] at h; subst result; exact .setupError hs
    | ok v =>
      obtain ⟨c, s, locs, ch₁⟩ := v
      simp only [hs] at h
      cases hr : execProgLoopOut fuel ⟨#[Thread.running c none], s, 0⟩ {} ch₁ GoString.empty with
      | mk out r => cases r with
        | error e => simp only [hr] at h; subst result; exact .runError hs (run_iff.mp hr)
        | ok v =>
          obtain ⟨sf, chf⟩ := v
          simp only [hr] at h
          cases hl : loadMany sf locs with
          | error e => simp only [hl] at h; subst result; exact .readError hs (run_iff.mp hr) hl
          | ok vs => simp only [hl] at h; subst result; exact .done hs (run_iff.mp hr) hl
  · intro h
    cases h with
    | setupError hs => simp only [runProgramPoolOutM, hs]
    | runError hs hr => simp only [runProgramPoolOutM, hs, run_iff.mpr hr]
    | readError hs hr hl => simp only [runProgramPoolOutM, hs, run_iff.mpr hr, hl]
    | done hs hr hl => simp only [runProgramPoolOutM, hs, run_iff.mpr hr, hl]

/-- Existential choices belong on BOTH sides of an observation-set bridge. -/
theorem exists_program_run_iff {p name args result} :
    (∃ fuel ch, runProgramPoolOutM fuel p name args ch = result) ↔
    ∃ fuel ch, ProgramRun fuel p name args ch result := by simp only [program_run_iff]

/-- Proposed A1 observation vocabulary: keep the actual readout and the
terminal's byte prefix. No claim about equivalence to every Go observer. -/
inductive Observation where
  | normal (readout : Readout)
  | terminal (reason : Terminal) (output : GoString)

def observationOf : RunResult → Option Observation
  | .ok r => some (.normal r)
  | .error (.terminal t, out) => some (.terminal t out)
  | .error (.refusal _, _) | .error (.fuelOut, _) => none

theorem fuel_is_not_observation (out : GoString) :
    observationOf (.error (.fuelOut, out)) = none := rfl
theorem refusal_is_not_observation (r : Refusal) (out : GoString) :
    observationOf (.error (.refusal r, out)) = none := rfl

/-- The corrected whole-program finite observation-set bridge. This is
partial correctness/may-observation infrastructure, not termination. -/
theorem observation_iff {p name args obs} :
    (∃ fuel ch, observationOf (runProgramPoolOutM fuel p name args ch) = some obs) ↔
      ∃ fuel ch result, ProgramRun fuel p name args ch result ∧ observationOf result = some obs := by
  constructor
  · rintro ⟨fuel, ch, h⟩
    exact ⟨fuel, ch, _, program_run_iff.mp rfl, h⟩
  · rintro ⟨fuel, ch, result, hrun, hobs⟩
    exact ⟨fuel, ch, (program_run_iff.mpr hrun) ▸ hobs⟩

end GoLean.GateA1.Pool
