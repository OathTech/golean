import GoLean.GoCore.StepFn

/-! Small counterexamples to tempting contract shortcuts. These are review
evidence over the kickoff machine, not the new typed contract's tests. -/
namespace GoLean.TypedContractDesignReview
open GoCore GoCore.Machine

theorem sequence_splices (ss rest : List Stmt) (env : LocalEnv) (k : Cont) :
    seqCont ss env (.seq rest env k) = .seq (ss ++ rest) env k := by
  simp [seqCont]

/-- Successful normalization alone does not establish Boolean typing. -/
theorem normalization_accepts_integer_at_bool (s : ExecState) :
    normalizeValueForTy s .bool (.int 7) = .ok (.int 7) := rfl

def nonAsciiPayload : GoValue :=
  .interface .string (.string { bytes := #[195, 169] })

def newlinePayload : GoValue :=
  .interface .string (.string { bytes := #[97, 10, 98] })

def samePayload : GoValue :=
  .interface .string (.string { bytes := #[115, 97, 109, 101] })

def invalidUtf8Payload : GoValue :=
  .interface .string (.string { bytes := #[255] })

theorem nonAscii_unrenderable (s : ExecState) :
    renderPanicPayload s nonAsciiPayload = none := by
  simp only [renderPanicPayload, nonAsciiPayload]
  decide +kernel

theorem newline_unrenderable (s : ExecState) :
    renderPanicPayload s newlinePayload = none := by
  simp only [renderPanicPayload, newlinePayload]
  decide +kernel

theorem invalidUtf8_unrenderable (s : ExecState) :
    renderPanicPayload s invalidUtf8Payload = none := by
  simp only [renderPanicPayload, invalidUtf8Payload]
  decide +kernel

theorem equal_repanic_unrenderable (s : ExecState) :
    renderPanicHead s ⟨samePayload, true⟩ [⟨samePayload, false⟩] = none := by
  with_unfolding_all rfl

/-- The abort-shape classifier can succeed although readout cannot. -/
theorem unrenderable_has_abort_shape :
    Config.abort? (.panicking [⟨nonAsciiPayload, false⟩] .stop) =
      some (⟨nonAsciiPayload, false⟩, []) := rfl

theorem nonAscii_abort_has_no_message (s : ExecState) :
    ¬ ∃ msg, abortMsg s ⟨nonAsciiPayload, false⟩ [] = .ok msg := by
  simp [abortMsg, renderPanicHead, nonAscii_unrenderable]

theorem empty_chain_is_not_abort :
    Config.abort? (.panicking [] .stop) = none := rfl

def shadowEnv : LocalEnv := [[("x", .base ⟨0⟩)], [("x", .base ⟨999⟩)]]
def shadowState : ExecState := { heap := #[.value .bool (.bool false)] }

/-- Lookup coverage cannot see a hidden outer binding. -/
theorem hidden_binding_has_visible_root :
    ∀ name loc, shadowEnv.lookup name = some loc →
      ∃ a : Nat, ∃ b : Bool, loc = .base ⟨a⟩ ∧
        shadowState.heap[a]? = some (.value .bool (.bool b)) := by
  intro name loc h
  by_cases hx : "x" = name
  · simp [shadowEnv, LocalEnv.lookup, Scope.lookup, hx] at h
    cases h
    exact ⟨0, false, rfl, rfl⟩
  · simp [shadowEnv, LocalEnv.lookup, Scope.lookup, hx] at h

theorem hidden_binding_violates_bound :
    ¬ LocalEnv.locSup shadowEnv ≤ shadowState.nextAddr := by
  decide +kernel

#print axioms sequence_splices
#print axioms normalization_accepts_integer_at_bool
#print axioms nonAscii_unrenderable
#print axioms newline_unrenderable
#print axioms invalidUtf8_unrenderable
#print axioms equal_repanic_unrenderable
#print axioms unrenderable_has_abort_shape
#print axioms nonAscii_abort_has_no_message
#print axioms empty_chain_is_not_abort
#print axioms hidden_binding_has_visible_root
#print axioms hidden_binding_violates_bound

end GoLean.TypedContractDesignReview
