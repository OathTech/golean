import Tests.RecoverySetup

namespace GoLean.GoCore.RecoveryRuntime.EntryReview
open RecoveryTyping Machine

set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def aliasFunction : Func := {
  id := ⟨"alias"⟩
  args := #[⟨"left", .pointer .bool⟩, ⟨"right", .pointer .bool⟩]
  results := #[⟨"result", .bool⟩]
  body := .returnStmt }

def aliasProgram : Program := {
  typeDefs := TypeEnv.reserved, funcs := #[SetupTests.emptyFunction, aliasFunction] }

def aliasState (b : Bool) : ExecState := {
  BooleanRuntime.programState aliasProgram with heap := #[.value .bool (.bool b)] }

theorem aliases_preserved (b : Bool) (ch : Choices) :
    ∃ next env locs s',
      enterFramePick (aliasState b) ⟨"alias"⟩ [.addr (.base ⟨0⟩), .addr (.base ⟨0⟩)] ch =
        .ok (.ok (aliasFunction, env, locs, s'), ch) ∧
      Extends #[.boolean] next ∧ HeapTyped next s' ∧
      EnvTyped next (initialContext aliasFunction) env ∧
      ResultRoots next aliasFunction.results.toList locs := by
  have hp : RecoveryAdmission aliasProgram "empty" #[] :=
    checkRecovery_sound (by with_unfolding_all rfl)
  have hh : HeapTyped #[.boolean] (aliasState b) := by
    simpa [aliasState, BooleanRuntime.programState, ExecState.alloc, ExecState.allocCell]
      using (HeapTyped.empty (s := BooleanRuntime.programState aliasProgram) rfl).alloc
        .boolean (.boolean b)
  obtain ⟨next, env, locs, s', he, ex, heap, henv, roots, _⟩ :=
    enterFramePick_typed hp.2.2 (show BooleanRuntime.SameContext
      (BooleanRuntime.programState aliasProgram) (aliasState b) from rfl) hh
      (show findFunctionIn? aliasProgram.funcs ⟨"alias"⟩ = some aliasFunction from by rfl)
      (show ParamsValues #[.boolean] aliasFunction.args.toList
        [.addr (.base ⟨0⟩), .addr (.base ⟨0⟩)] from
        .cons ⟨.root, .root, .root rfl⟩ (.cons ⟨.root, .root, .root rfl⟩ .nil)) ch
  exact ⟨next, env, locs, s', he, ex, heap, henv, roots⟩

theorem alias_slots_are_distinct (b : Bool) :
    enterFrame (aliasState b) ⟨"alias"⟩ [.addr (.base ⟨0⟩), .addr (.base ⟨0⟩)] =
      .ok (aliasFunction,
        [[("result", .base ⟨3⟩), ("right", .base ⟨2⟩), ("left", .base ⟨1⟩)]],
        [.base ⟨3⟩], { BooleanRuntime.programState aliasProgram with heap := #[
          .value .bool (.bool b),
          .value (.pointer .bool) (.addr (.base ⟨0⟩)),
          .value (.pointer .bool) (.addr (.base ⟨0⟩)),
          .value .bool (.bool false)] }) := by
  with_unfolding_all rfl

theorem root_nil_rejected :
    ¬ ParamsValues #[.boolean] [⟨"p", .pointer .bool⟩] [.nil] := by
  intro h
  cases h with
  | cons hv _ =>
      obtain ⟨sort, ht, hv⟩ := hv
      cases ht
      cases hv

theorem dangling_capture_rejected :
    ¬ ParamsValues #[.boolean] [⟨"p", .pointer .bool⟩] [.addr (.base ⟨1⟩)] := by
  intro h
  cases h with
  | cons hv _ =>
      obtain ⟨sort, ht, hv⟩ := hv
      cases ht
      cases hv with
      | root h => simp at h

theorem incomplete_vector_rejected :
    ¬ ParamsValues #[.boolean] aliasFunction.args.toList [.addr (.base ⟨0⟩)] := by
  intro h
  have hl := h.length
  simp [aliasFunction] at hl

theorem pointer_zero_rejected : ¬ ZeroValues [⟨"p", .pointer .bool⟩] [.nil] := by
  intro h
  cases h with
  | payload ht _ => cases ht

theorem hidden_dangling_binding_rejected :
    ¬ EnvTyped #[.boolean] [[("x", .bool)]]
      [[("x", .base ⟨0⟩)], [("hidden", .base ⟨9⟩)]] := by
  intro h
  obtain ⟨sort, a, ha, hb⟩ := h.bindings [("hidden", .base ⟨9⟩)] (by simp)
    ("hidden", .base ⟨9⟩) (by simp)
  have he : a = 9 := by simpa using ha.symm
  subst a
  simp at hb

theorem initial_readout_is_not_true :
    loadMany (initialState SetupTests.mixedProgram SetupTests.mixed
      [.bool true, .bool false] [.bool false, .nil])
      (BooleanRuntime.initialResults SetupTests.mixed) ≠ .ok [.bool true, .nil] := by
  rw [initialState_readout _ _ _ _ rfl rfl]
  intro h
  cases h

#print axioms aliases_preserved
#print axioms alias_slots_are_distinct
#print axioms root_nil_rejected
#print axioms dangling_capture_rejected
#print axioms incomplete_vector_rejected
#print axioms pointer_zero_rejected
#print axioms hidden_dangling_binding_rejected
#print axioms initial_readout_is_not_true

end GoLean.GoCore.RecoveryRuntime.EntryReview
