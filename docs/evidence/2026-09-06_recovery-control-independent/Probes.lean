import Tests.RecoveryControlAudit

namespace RecoveryControlIndependent
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.GoCore.RecoveryTyping GoLean.GoCore.RecoveryRuntime

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

theorem absent_deferred_target (world : World) (callee : GoValue) (args : List GoValue) :
    ¬ PendingCall world #[] callee args := by
  rintro ⟨fid, caps, f, _, hf, _⟩
  simp [findFunctionIn?] at hf

theorem closure_identity_cannot_change (world : World) (caps : List Param)
    (values : List GoValue) (left right : FuncId) (hne : left ≠ right) :
    ¬ Delivered world (.closure left caps) (.funcVal right values) := by
  intro h
  cases h
  exact hne rfl

theorem nil_is_not_a_live_capture (world : World) :
    ¬ ParamsValues world [⟨"capture", .pointer .bool⟩] [.nil] := by
  intro h
  cases h with
  | cons hv _ => cases hv.sorted TypeClass.root

theorem string_is_not_boolean_delivery (world : World) (bytes : GoString) :
    ¬ Delivered world (.value .boolean) (.string bytes) := by
  intro h
  cases h with
  | value h => cases h

theorem missing_call_argument_rejected (world : World) :
    ¬ ParamsValues world [⟨"a", .bool⟩, ⟨"b", .bool⟩] [.bool true] := by
  intro h
  have hl := h.length
  simp at hl

theorem result_roots_may_alias :
    ResultRoots #[.boolean] [⟨"a", .bool⟩, ⟨"b", .bool⟩]
      [.base ⟨0⟩, .base ⟨0⟩] :=
  .cons ⟨.boolean, .boolean, 0, rfl, rfl⟩
    (.cons ⟨.boolean, .boolean, 0, rfl, rfl⟩ .nil)

theorem duplicate_writeback_refs_may_alias :
    RefsTyped #[.boolean] [⟨"a", .bool⟩, ⟨"b", .bool⟩]
      [.chain (.addr (.base ⟨0⟩)) [] [], .chain (.addr (.base ⟨0⟩)) [] []] :=
  .cons (.root ⟨.boolean, .boolean, 0, rfl, rfl⟩)
    (.cons (.root ⟨.boolean, .boolean, 0, rfl, rfl⟩) .nil)

theorem recovered_history_keeps_arbitrary_bytes (bytes : GoString) :
    ChainTyped [⟨.interface .string (.string bytes), true⟩,
      ⟨.interface .string (.string bytes), false⟩] :=
  (ChainTyped.single bytes true).append (ChainTyped.single bytes false)

theorem no_runtime_integer_in_typed_chain (n : Int) (kind : IntKind) (rest : List PanicEntry) :
    ¬ ChainTyped (⟨.interface (.int kind) (.int n kind), false⟩ :: rest) := by
  intro h
  obtain ⟨bytes, impossible⟩ := h.2
    ⟨.interface (.int kind) (.int n kind), false⟩ (by simp)
  cases impossible

/-- This is an actual machine equation: suspended history precedes the new
panic, and arbitrary choices are returned unchanged. -/
theorem unwind_appends_in_order (state : ExecState) (older newer : List PanicEntry)
    (k : Cont) (choices : Choices) :
    stepFn state (.panicking newer (.panicResumeK older k)) choices =
      .ok (.panicking (older ++ newer) k, state, choices) := rfl

theorem second_direct_recover_is_nil (bytes : GoString) (k : Cont) :
    recoverResult (.frame [] [] [] []
      (.panicResumeK [⟨.interface .string (.string bytes), true⟩] k) false) =
      (.nil, .frame [] [] [] []
        (.panicResumeK [⟨.interface .string (.string bytes), true⟩] k) false) := by
  unfold recoverResult
  rw [Cont.rebuild_act (by rfl)]
  dsimp only
  unfold recoverThroughWrappers
  rw [Cont.rebuild_act (by rfl)]
  simp [markNewestRecovered]

/-- Terminal payload kind follows from the actual typed control and abort
query; it is not guessed from renderer output. -/
theorem abort_query_preserves_string_kind {world fs c first rest}
    (hc : Control world fs c) (ha : c.abort? = some (first, rest)) :
    ∃ bytes, first.value = .interface .string (.string bytes) := by
  cases hc <;> try contradiction
  case panicking chain k hchain hk =>
    cases k <;> try simp [Config.abort?] at ha
    cases chain with
    | nil => exact False.elim (hchain.1 rfl)
    | cons entry tail =>
      simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      exact hchain.2 _ (by simp)

def pair : Func := {
  id := ⟨"pair"⟩, args := #[], results := #[⟨"a", .bool⟩, ⟨"b", .bool⟩]
  body := .seqn #[.assign (.var "a") (.boolLit true),
    .assign (.var "b") (.boolLit false), .returnStmt]
}
def caller : Func := {
  id := ⟨"caller"⟩, args := #[], results := #[⟨"r", .bool⟩]
  body := .seqn #[.call #[.var "r", .var "r"] ⟨"pair"⟩ #[], .returnStmt]
}
def aliasProgram : Program := { typeDefs := TypeEnv.reserved, funcs := #[caller, pair] }

theorem aliased_call_targets_admitted : checkRecovery aliasProgram "caller" #[] = .ok () := by
  with_unfolding_all rfl

/-- Two call-result targets can denote one cell. Actual ordered writeback
retains the last value, independently of the generic type/readout theorem. -/
theorem actual_aliased_writeback :
    runProgramM 80 aliasProgram "caller" #[] [] = .ok { values := #[.bool false] } := by
  with_unfolding_all rfl

end RecoveryControlIndependent

#eval RecoveryControlAudit.run

open Lean in
def auditIndependentControl : CoreM Unit := do
  let env ← getEnv
  let mut count := 0
  for (name, _) in env.constants.toList do
    let selected := match env.getModuleIdxFor? name with
      | some i => env.header.moduleNames[i.toNat]!.getRoot == `GoLean ||
          env.header.moduleNames[i.toNat]!.getRoot == `Tests
      | none => true
    unless selected do continue
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Independent control review: {name} depends on forbidden axiom {ax}"
    count := count + 1
  logInfo s!"Independent control review: {count} complete imported/local declarations checked"

#eval auditIndependentControl
