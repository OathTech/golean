import GoLean.GoCore.RecoveryCallEntry
import Tests.RecoveryTypingFixture
import Tests.RecoveryA2Artifact

namespace GoLean.GoCore.RecoveryRuntime.SetupTests
open RecoveryTyping Machine

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

def mixed : Func := {
  id := ⟨"mixed"⟩
  args := #[⟨"x", .bool⟩, ⟨"y", .bool⟩]
  results := #[⟨"result", .bool⟩, ⟨"payload", .interface ⟨"any"⟩⟩]
  body := .block #[] #[
    .assign (.var "result") (.and (.var "x") (.not (.var "y"))), .returnStmt]
}

def mixedProgram : Program := { typeDefs := TypeEnv.reserved, funcs := #[mixed] }

theorem mixed_admitted (x y : Bool) :
    checkRecovery mixedProgram "mixed" #[.bool x, .bool y] = .ok () := by
  cases x <;> cases y <;> with_unfolding_all rfl

theorem mixed_actual_setup (x y : Bool) (fuel : Nat) (ch : Choices) :
    runProgramSetupM fuel mixedProgram "mixed" #[.bool x, .bool y] ch =
      .ok (.exec mixed.body (BooleanRuntime.initialEnv mixed) (.frame [] [] [] [] .stop),
        initialState mixedProgram mixed [.bool x, .bool y] [.bool false, .nil],
        [.base ⟨2⟩, .base ⟨3⟩], ch) := by
  obtain ⟨f, zeros, world, hf, _, hz, hs, _⟩ :=
    setup_typed_wf (checkRecovery_sound (mixed_admitted x y)) fuel ch
  have hfound : findFunctionIn? mixedProgram.funcs ⟨"mixed"⟩ = some mixed := by rfl
  have he : f = mixed := Option.some.inj (hf.symm.trans hfound)
  subst f
  have hzero : zeros = [.bool false, .nil] :=
    hz.unique (.boolean rfl (.payload (.payload rfl) .nil))
  subst zeros
  exact hs

theorem mixed_input_readout (x y : Bool) :
    loadLoc (initialState mixedProgram mixed [.bool x, .bool y] [.bool false, .nil])
      (.base ⟨0⟩) = .ok (.bool x) ∧
    loadLoc (initialState mixedProgram mixed [.bool x, .bool y] [.bool false, .nil])
      (.base ⟨1⟩) = .ok (.bool y) := by
  exact ⟨initialState_argument _ _ _ _ rfl 0 (by simp),
    initialState_argument _ _ _ _ rfl 1 (by simp)⟩

theorem mixed_results_start_false_and_nil (x y : Bool) :
    loadMany (initialState mixedProgram mixed [.bool x, .bool y] [.bool false, .nil])
      (BooleanRuntime.initialResults mixed) = .ok [.bool false, .nil] :=
  initialState_readout _ _ _ _ rfl rfl

/-- Externally supplied pointers cannot impersonate entry Boolean arguments. -/
theorem pointer_entry_rejected :
    checkRecovery mixedProgram "mixed" #[.addr (.base ⟨0⟩), .bool true] ≠ .ok () := by
  intro h
  with_unfolding_all cases h

/-- Result keys may not overwrite a parameter during frame initialization. -/
theorem colliding_signature_rejected :
    checkRecovery { mixedProgram with funcs := #[{ mixed with
      results := #[⟨"x", .bool⟩] }] } "mixed" #[.bool false, .bool true] ≠ .ok () := by
  intro h
  with_unfolding_all cases h

private theorem setup_witness {p name args} (h : RecoveryAdmission p name args)
    (fuel : Nat) (ch : Choices) :
    ∃ c s pins, runProgramSetupM fuel p name args ch = .ok (c, s, pins, ch) ∧
      MachineWf s c ∧ ∃ world, HeapTyped world s := by
  obtain ⟨f, zeros, world, _, _, _, hs, hw, hh, _⟩ := setup_typed_wf h fuel ch
  exact ⟨_, _, _, hs, hw, world, hh⟩

/-- The complete second native artifact uses the same generic setup for both inputs. -/
theorem native_shared_setup (b : Bool) (fuel : Nat) (ch : Choices) :
    ∃ c s pins, runProgramSetupM fuel Tests.nativeRecovery "Shared" #[.bool b] ch =
        .ok (c, s, pins, ch) ∧ MachineWf s c ∧ ∃ world, HeapTyped world s :=
  setup_witness (checkRecovery_sound (Tests.shared_admitted b)) fuel ch

theorem a2_recovered_setup (fuel : Nat) (ch : Choices) :
    ∃ c s pins, runProgramSetupM fuel Tests.a2Program "Recovered" #[] ch =
        .ok (c, s, pins, ch) ∧ MachineWf s c ∧ ∃ world, HeapTyped world s :=
  setup_witness (checkRecovery_sound Tests.a2_recovered) fuel ch

theorem a2_uncaught_setup (fuel : Nat) (ch : Choices) :
    ∃ c s pins, runProgramSetupM fuel Tests.a2Program "Uncaught" #[] ch =
        .ok (c, s, pins, ch) ∧ MachineWf s c ∧ ∃ world, HeapTyped world s :=
  setup_witness (checkRecovery_sound Tests.a2_uncaught) fuel ch

theorem a2_normal_setup (fuel : Nat) (ch : Choices) :
    ∃ c s pins, runProgramSetupM fuel Tests.a2Program "Normal" #[] ch =
        .ok (c, s, pins, ch) ∧ MachineWf s c ∧ ∃ world, HeapTyped world s :=
  setup_witness (checkRecovery_sound Tests.a2_normal) fuel ch

def emptyFunction : Func := { id := ⟨"empty"⟩, args := #[], results := #[], body := .seqn #[] }
def emptyProgram : Program := { typeDefs := TypeEnv.reserved, funcs := #[emptyFunction] }

theorem empty_setup (ch : Choices) :
    ∃ c s pins, runProgramSetupM 0 emptyProgram "empty" #[] ch = .ok (c, s, pins, ch) ∧
      MachineWf s c ∧ ∃ world, HeapTyped world s :=
  setup_witness (checkRecovery_sound (by with_unfolding_all rfl)) 0 ch

def capturedFunction : Func := {
  id := ⟨"captured"⟩
  args := #[⟨"root", .pointer .bool⟩]
  results := #[⟨"result", .bool⟩]
  body := .block #[] #[
    .assign (.var "result") (.deref (.var "root") .bool), .returnStmt]
}

def capturedProgram : Program := {
  typeDefs := TypeEnv.reserved, funcs := #[emptyFunction, capturedFunction]
}

def capturedState (b : Bool) : ExecState := {
  BooleanRuntime.programState capturedProgram with heap := #[.value .bool (.bool b)]
}

theorem captured_call_typed (b : Bool) (ch : Choices) :
    ∃ next env locs s',
      enterFramePick (capturedState b) ⟨"captured"⟩ [.addr (.base ⟨0⟩)] ch =
        .ok (.ok (capturedFunction, env, locs, s'), ch) ∧
      Extends #[.boolean] next ∧ HeapTyped next s' ∧
      ResultRoots next capturedFunction.results.toList locs := by
  have hp : RecoveryAdmission capturedProgram "empty" #[] :=
    checkRecovery_sound (by with_unfolding_all rfl)
  have hh : HeapTyped #[.boolean] (capturedState b) := by
    simpa [capturedState, BooleanRuntime.programState, ExecState.alloc, ExecState.allocCell]
      using (HeapTyped.empty (s := BooleanRuntime.programState capturedProgram) rfl).alloc
        (.boolean) (.boolean b)
  obtain ⟨next, env, locs, s', hs, ext, heap, _, roots, _⟩ :=
    enterFramePick_typed hp.2.2 (show BooleanRuntime.SameContext
      (BooleanRuntime.programState capturedProgram) (capturedState b) from rfl)
      hh (show findFunctionIn? capturedProgram.funcs ⟨"captured"⟩ =
        some capturedFunction from by rfl)
      (show ParamsValues #[.boolean] capturedFunction.args.toList [.addr (.base ⟨0⟩)] from
        .cons ⟨.root, .root, .root rfl⟩ .nil) ch
  exact ⟨next, env, locs, s', hs, ext, heap, roots⟩

theorem captured_call_storage (b : Bool) :
    enterFrame (capturedState b) ⟨"captured"⟩ [.addr (.base ⟨0⟩)] =
      .ok (capturedFunction, [[("result", .base ⟨2⟩), ("root", .base ⟨1⟩)]],
        [.base ⟨2⟩], { BooleanRuntime.programState capturedProgram with heap := #[
          .value .bool (.bool b), .value (.pointer .bool) (.addr (.base ⟨0⟩)),
          .value .bool (.bool false)] }) := by
  with_unfolding_all rfl

theorem actual_block_shadow (b : Bool) :
    ∃ next env s',
      allocDecls [[], [("x", .base ⟨0⟩)]] { heap := #[.value .bool (.bool b)] }
        [⟨"x", .interface ⟨"any"⟩⟩] = .ok (env, s') ∧
      EnvTyped next [[("x", .interface ⟨"any"⟩)], [("x", .bool)]] env ∧
      HeapTyped next s' := by
  have heap : HeapTyped #[.boolean] ({ heap := #[.value .bool (.bool b)] } : ExecState) :=
    (HeapTyped.empty (s := {}) rfl).alloc .boolean (.boolean b)
  have henv : EnvTyped #[.boolean] [[("x", .bool)]] [[("x", .base ⟨0⟩)]] :=
    (EnvTyped.empty #[.boolean]).declare ⟨"x", .bool⟩
      ⟨.boolean, .boolean, 0, rfl, rfl⟩
  obtain ⟨next, env, s', run, _, hheap, henv, _⟩ :=
    allocDecls_typed [⟨"x", .interface ⟨"any"⟩⟩] heap henv.push (by
      intro p hp
      rcases List.mem_singleton.mp hp with rfl
      exact .inr (.payload rfl))
  exact ⟨next, env, s', run, henv.pushedDecls (by simp), hheap⟩

end GoLean.GoCore.RecoveryRuntime.SetupTests
