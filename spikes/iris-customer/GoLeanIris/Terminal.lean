import GoLeanIris.SharedDriver
import GoLean.Interface

/-! Both live customers consume terminal and metadata contracts through the
experimental facade (landing chunk L3, `docs/2026-09-07_land-panic-text-tape.md`;
the sprint's `Terminal` of `7bd32ad6`, RESTATED over the `repanicCollapse`
tape and the D5 refusal). Functional results still come from their Iris
proofs. The sprint's `*_no_refusal` consequences are not restated: the
generic contract now says the ONLY refusal is the named invalid-first-line
abort (`runProgramPool_refusal_named`); these fixtures' literals are ASCII,
and their fixed-fuel successful runs (`*_all_choices`) are trivially not
refusals — stated as such, at their fuel. -/
namespace GoLean.IrisCustomer
open GoCore GoCore.Machine GoCore.RecoveryTyping

theorem observed_normal_of_program {p : Program} {name : String}
    {args : Array GoValue} {fuel ch result}
    (admitted : RecoveryAdmission p name args)
    (run : runProgramPoolOutM fuel p name args ch = .ok result) :
    RecoveryRuntime.runProgramPoolWithAbort fuel p name args ch = (.ok result, none) := by
  obtain ⟨_, _, outcome⟩ := RecoveryRuntime.runProgramPoolWithAbort_typed admitted fuel ch
  have erase := RecoveryRuntime.runProgramPoolWithAbort_erasure fuel p name args ch
  rw [run] at erase
  rcases outcome with ⟨_, _, _, _, observed⟩ | ⟨_, _, _, _, _, _, observed⟩
    | ⟨_, _, _, _, _, observed⟩ | observed
  · rw [observed] at erase
    have result_eq := Except.ok.inj erase
    simpa only [result_eq] using observed
  · rw [observed] at erase; contradiction
  · rw [observed] at erase; contradiction
  · rw [observed] at erase; contradiction

theorem recovered_observed_all_choices (ch : Choices) :
    RecoveryRuntime.runProgramPoolWithAbort 60 recoveryProgram "Recovered" #[] ch =
      (.ok {values := #[.bool true], output := GoString.empty}, none) :=
  observed_normal_of_program recovery_admitted (recovered_program_all_choices ch)

theorem normal_observed_all_choices (ch : Choices) :
    RecoveryRuntime.runProgramPoolWithAbort 60 recoveryProgram "Normal" #[] ch =
      (.ok {values := #[.bool true], output := GoString.empty}, none) :=
  observed_normal_of_program normal_admitted (normal_program_all_choices ch)

theorem shared_observed_all_choices (b : Bool) (ch : Choices) :
    RecoveryRuntime.runProgramPoolWithAbort 200 sharedProgram "Shared" #[.bool b] ch =
      (.ok {values := #[.bool (!b)], output := GoString.empty}, none) :=
  observed_normal_of_program (shared_admitted b) (shared_program_all_choices b ch)

/-- The existing uncaught semantic control obtains computed metadata from
the generic admitted-program theorem: the record's head renders
`customer panic` at the collapse bit the (empty) stream selects on the
record's own chain (an unrecovered head — `collapseBit` is false there).
No Iris NotStuck claim is made. (Restated at the L3 audit fix round
2026-09-07, R7: the bit is no longer existential.) -/
theorem uncaught_has_actual_record :
    ∃ record, RecoveryRuntime.runProgramPoolWithAbort 60 recoveryProgram "Uncaught" #[] [] =
      (.error (.panic "customer panic", GoString.empty), some record) ∧
      ∃ (first : PanicEntry) (rest : List PanicEntry), first :: rest = record.chain ∧
        stringPanicHead record.bytes record.recovered
          (collapseBit first rest (abortConsult first rest []).1) = some "customer panic" :=
  (RecoveryRuntime.runProgramPoolWithAbort_panic_iff uncaught_admitted 60 [] "customer panic").mp
    uncaught_program

/-- The only refusal any of the A2 entries could reach is the named
invalid-first-line abort refusal (D5) — for every fuel and stream. -/
theorem a2_entries_refusal_named (fuel : Nat) (ch : Choices) (reason : Refusal) (out : GoString)
    (name : String) (hname : name = "Recovered" ∨ name = "Normal" ∨ name = "Uncaught")
    (run : runProgramPoolOutM fuel recoveryProgram name #[] ch = .error (.refusal reason, out)) :
    ∃ (t : ExecState) (first : PanicEntry) (bytes : GoString),
      first.value = .interface .string (.string bytes) ∧
      stringFirstLine? bytes.bytes = none ∧
      reason = .unsupported (abortRefusal t first) ∧ out = GoString.empty := by
  rcases hname with rfl | rfl | rfl
  · exact RecoveryRuntime.runProgramPool_refusal_named recovery_admitted fuel ch reason out run
  · exact RecoveryRuntime.runProgramPool_refusal_named normal_admitted fuel ch reason out run
  · exact RecoveryRuntime.runProgramPool_refusal_named uncaught_admitted fuel ch reason out run

theorem shared_refusal_named (b : Bool) (fuel : Nat) (ch : Choices)
    (reason : Refusal) (out : GoString)
    (run : runProgramPoolOutM fuel sharedProgram "Shared" #[.bool b] ch = .error (.refusal reason, out)) :
    ∃ (t : ExecState) (first : PanicEntry) (bytes : GoString),
      first.value = .interface .string (.string bytes) ∧
      stringFirstLine? bytes.bytes = none ∧
      reason = .unsupported (abortRefusal t first) ∧ out = GoString.empty :=
  RecoveryRuntime.runProgramPool_refusal_named (shared_admitted b) fuel ch reason out run

/-- At their fixed fuels the successful fixtures are not refusals, on every
stream — a consequence of `*_all_choices`, stated at that fuel and no other. -/
theorem fixtures_not_refused_at_fuel (b : Bool) (ch : Choices) (reason : Refusal) (out : GoString) :
    runProgramPoolOutM 60 recoveryProgram "Recovered" #[] ch ≠ .error (.refusal reason, out) ∧
    runProgramPoolOutM 60 recoveryProgram "Normal" #[] ch ≠ .error (.refusal reason, out) ∧
    runProgramPoolOutM 200 sharedProgram "Shared" #[.bool b] ch ≠ .error (.refusal reason, out) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [recovered_program_all_choices ch]; simp
  · rw [normal_program_all_choices ch]; simp
  · rw [shared_program_all_choices b ch]; simp

end GoLean.IrisCustomer
