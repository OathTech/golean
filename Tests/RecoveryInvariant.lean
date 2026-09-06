import GoLean.GoCore.RecoverySuccessfulRuns
import Tests.RecoveryTypingFixture
import Tests.RecoveryA2Artifact

namespace GoLean.GoCore.RecoveryRuntime.ControlTests
open RecoveryTyping Machine

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

theorem writeback_to_stop_rejected {world fs plan plans env roots ds} :
    ¬ ReturnCont world fs (.frame (plan :: plans) env roots ds .stop false) := by
  intro h
  cases h with
  | frame _ _ _ _ _ wb => exact (wb (by simp)).not_stop

theorem writeback_to_resume_rejected {world fs plan plans env roots ds chain k} :
    ¬ ReturnCont world fs
      (.frame (plan :: plans) env roots ds (.panicResumeK chain k) false) := by
  intro h
  cases h with
  | frame _ _ _ _ _ wb => cases wb (by simp)

theorem root_return_rejected {world fs} : ¬ Control world fs (.signal .ret .stop) :=
  Control.not_return_stop

theorem empty_panic_chain_rejected {world fs k} : ¬ Control world fs (.panicking [] k) := by
  intro h
  cases h with
  | panicking hc _ => exact hc.1 rfl

theorem foreign_initialization_environment_rejected {world fs q env saved rest k}
    (hne : env ≠ saved) :
    ¬ Control world fs (.exec (.initialization q) env (.seq rest saved k)) :=
  fun h => hne h.initialization_environment

/-- Different physical addresses may not silently satisfy the same root kind. -/
theorem dangling_target_address_rejected :
    ¬ Delivered #[.boolean] (.address .boolean) (.addr (.base ⟨4⟩)) := by
  intro h
  cases h with
  | address h => obtain ⟨a, ha, ht⟩ := h; cases ha; simp at ht

theorem boxed_panic_excludes_nil (world : World) : ¬ Delivered world .boxed .nil := by
  intro h
  cases h

/-- Registration prepends each fully evaluated call; it does not run or
copy its captured pointees. This equation holds for arbitrary closures. -/
theorem registration_is_lifo (first second : GoValue × List GoValue)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv) (roots : List Loc)
    (ds : List (GoValue × List GoValue)) (k : Cont) :
    pushDefer first (.frame plans env roots ds k false) =
      some (.frame plans env roots (first :: ds) k false) ∧
    pushDefer second (.frame plans env roots (first :: ds) k false) =
      some (.frame plans env roots (second :: first :: ds) k false) := by
  constructor <;> unfold pushDefer <;> rw [Cont.rebuild_act (by rfl)] <;> rfl

def barrier : Cont := .frame [] [] [] [] .stop false
def active (bytes : GoString) : List PanicEntry :=
  [⟨.interface .string (.string bytes), false⟩]

theorem direct_recovery_marks_newest (bytes : GoString) :
    recoverResult (.frame [] [] [] [] (.panicResumeK (active bytes) barrier) false) =
      (.interface .string (.string bytes),
        .frame [] [] [] []
          (.panicResumeK [⟨.interface .string (.string bytes), true⟩] barrier) false) :=
  recover_direct (chain := active bytes) rfl [] [] [] [] barrier

/-- An ordinary function called by a deferred handler is one real frame
too deep. Its recover is nil and cannot mark the suspended panic. -/
theorem indirect_recovery_is_nil (bytes : GoString) :
    recoverResult (.frame [] [] [] []
      (.frame [] [] [] [] (.panicResumeK (active bytes) barrier) false) false) =
      (.nil, .frame [] [] [] []
        (.frame [] [] [] [] (.panicResumeK (active bytes) barrier) false) false) := by
  apply recover_indirect (world := #[]) (fs := #[])
  exact .frame (EnvTyped.empty #[]) .nil .nil (by simp [DefersTyped])
    (.resume (ChainTyped.single bytes false)
      (.frame (EnvTyped.empty #[]) .nil .nil (by simp [DefersTyped]) .stop (by simp))) (by simp)

/-- Equal re-panic payloads are distinct chain entries. Recovery marks the
newest entry while retaining the older recovered history, for any bytes. -/
theorem equal_repanic_keeps_history (bytes : GoString) :
    markNewestRecovered [⟨.interface .string (.string bytes), true⟩,
      ⟨.interface .string (.string bytes), false⟩] =
      some (.interface .string (.string bytes),
        [⟨.interface .string (.string bytes), true⟩,
          ⟨.interface .string (.string bytes), true⟩]) := rfl

theorem invalid_utf8_chain_remains_typed :
    ChainTyped [⟨.interface .string (.string ⟨#[255, 0, 10, 9]⟩), false⟩] :=
  ChainTyped.single _ false

def scopedFunction : Func := {
  id := ⟨"scoped"⟩, args := #[⟨"x", .bool⟩], results := #[⟨"result", .bool⟩]
  body := .block #[⟨"zero", .bool⟩] #[
    .block #[⟨"x", .interface ⟨"any"⟩⟩] #[
      .assign (.var "x") (.toInterface (.interface ⟨"any"⟩) .string
        (.stringLit (.fromLeanString "shadow")))],
    .seqn #[.initialization ⟨"payload", .interface ⟨"any"⟩⟩],
    .assign (.var "payload") (.nil none),
    .assign (.var "result") (.and (.var "x") (.not (.var "zero"))), .returnStmt]
}
def scopedProgram : Program := { typeDefs := TypeEnv.reserved, funcs := #[scopedFunction] }

theorem scoped_admitted (b : Bool) : checkRecovery scopedProgram "scoped" #[.bool b] = .ok () := by
  cases b <;> with_unfolding_all rfl

/-- The actual interpreter restores the Boolean outer x after a payload
shadow, sees the same-scope sequence declaration, and zero-initializes zero. -/
theorem scope_and_zero_execution (b : Bool) :
    runProgramM 60 scopedProgram "scoped" #[.bool b] [] = .ok { values := #[.bool b] } := by
  cases b <;> with_unfolding_all rfl

private theorem admitted_control {p name args} (h : RecoveryAdmission p name args)
    (fuel : Nat) (ch : Choices) :
    ∃ (f : Func) (c : Config) (s : ExecState) (pins : List Loc), runProgramSetupM fuel p name args ch = .ok (c, s, pins, ch) ∧
      Inv p f.results.toList pins s c := by
  obtain ⟨f, zeros, _, _, run, inv⟩ := setup_inv h fuel ch
  exact ⟨f, _, _, _, run, inv⟩

theorem whole_native_shared_invariant (b : Bool) (fuel : Nat) (ch : Choices) :
    ∃ (f : Func) (c : Config) (s : ExecState) (pins : List Loc), runProgramSetupM fuel Tests.nativeRecovery "Shared" #[.bool b] ch =
      .ok (c, s, pins, ch) ∧ Inv Tests.nativeRecovery f.results.toList pins s c :=
  admitted_control (checkRecovery_sound (Tests.shared_admitted b)) fuel ch

theorem whole_a2_recovered_invariant (fuel : Nat) (ch : Choices) :
    ∃ (f : Func) (c : Config) (s : ExecState) (pins : List Loc), runProgramSetupM fuel Tests.a2Program "Recovered" #[] ch =
      .ok (c, s, pins, ch) ∧ Inv Tests.a2Program f.results.toList pins s c :=
  admitted_control (checkRecovery_sound Tests.a2_recovered) fuel ch

theorem whole_a2_uncaught_invariant (fuel : Nat) (ch : Choices) :
    ∃ (f : Func) (c : Config) (s : ExecState) (pins : List Loc), runProgramSetupM fuel Tests.a2Program "Uncaught" #[] ch =
      .ok (c, s, pins, ch) ∧ Inv Tests.a2Program f.results.toList pins s c :=
  admitted_control (checkRecovery_sound Tests.a2_uncaught) fuel ch

theorem whole_a2_normal_invariant (fuel : Nat) (ch : Choices) :
    ∃ (f : Func) (c : Config) (s : ExecState) (pins : List Loc), runProgramSetupM fuel Tests.a2Program "Normal" #[] ch =
      .ok (c, s, pins, ch) ∧ Inv Tests.a2Program f.results.toList pins s c :=
  admitted_control (checkRecovery_sound Tests.a2_normal) fuel ch

end GoLean.GoCore.RecoveryRuntime.ControlTests
