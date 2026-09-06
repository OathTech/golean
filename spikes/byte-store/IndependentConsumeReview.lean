import ByteStoreConsume
import Lean

open GoLean GoLean.GoCore GoLean.GoCore.ByteStorePrototype

namespace IndependentConsumeReview

-- Certificate reuse must preserve the complete sequential result, including
-- a refusal from either store, with arbitrary indices and incoming values.
theorem composed {a : Addr} {n : Nat}
    (state : { s : ExecState // NormalBackingAt s a n })
    (i j : Int) (v w : GoValue) :
    (do
      let next ← consumeCertifiedByteElement state i v
      consumeCertifiedByteElement next j w).map Subtype.val = (do
      let next ← storeLoc state.val (.index (.base a) i) v
      storeLoc next (.index (.base a) j) w) := by
  rw [← consumeCertifiedByteElement_eq_storeLoc state i v]
  cases h : consumeCertifiedByteElement state i v with
  | error e => simp [Except.map, Bind.bind, Except.bind]
  | ok next =>
    simpa only [h, Except.map, Bind.bind, Except.bind] using
      consumeCertifiedByteElement_eq_storeLoc next j w

theorem negative_bounds_precede_bad_value :
    consumeByteElement Challenges.rawState ⟨0⟩ (-1) (.bool true) =
      .error (.panic "runtime error: index out of range [-1]") := by rfl

theorem alias_wrapping_readout :
    (do
      let next ← consumeCertifiedByteElement
        ⟨Challenges.rawState, Challenges.rawState_normal⟩ 0 (.int (-1) .int64)
      consumeCertifiedByteElement next 0 (.int 258 .uint16)).map
        (fun (next : { s : ExecState // NormalBackingAt s ⟨0⟩ 2 }) =>
          loadLoc next.val (.index (.base ⟨0⟩) 0)) =
      .ok (.ok (.int 2 .uint8)) := by rfl

-- A consuming update still needs normality: retaining an untouched 256
-- is observably different from the real root normalizer turning it into 0.
theorem no_unrestricted_refinement :
    consumeByteElement Challenges.nonNormalState ⟨0⟩ 1 (.int 1 .uint8) ≠
      storeLoc Challenges.nonNormalState (.index (.base ⟨0⟩) 1) (.int 1 .uint8) := by
  rw [consumeByteElement_eq _ _ _ _ (by rfl)]
  exact Challenges.no_unrestricted_refinement

end IndependentConsumeReview

open Lean in
run_cmd do
  let env ← getEnv
  let mut checked := 0
  for (n, _) in env.constants.toList do
    let selected := match env.getModuleIdxFor? n with
      | none => true
      | some i =>
          let m := env.header.moduleNames[i.toNat]!
          m == `ByteStore || m == `ByteStoreConsume || m.getRoot == `GoLean
    unless selected do continue
    for ax in (← collectAxioms n) do
      unless [``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "Independent consuming-store forbidden axiom: {n}: {ax}"
    checked := checked + 1
  logInfo s!"PASS independent consuming-store: four challenges; {checked} declarations audited"
