import ByteStore
import Lean

open GoLean GoLean.GoCore GoLean.GoCore.ByteStorePrototype

namespace IndependentByteStore

-- Reusing the erased certificate for two stores must agree with sequential
-- ordinary execution, including an error from either operation. No success
-- premise or incoming-value restriction is added for composition.
theorem two_stores {a : Addr} {n : Nat}
    (state : { s : ExecState // NormalBackingAt s a n })
    (i j : Int) (v w : GoValue) :
    (do
      let next ← storeCertifiedByteElement state i v
      storeCertifiedByteElement next j w).map Subtype.val = (do
      let next ← storeLoc state.val (.index (.base a) i) v
      storeLoc next (.index (.base a) j) w) := by
  rw [← storeCertifiedByteElement_eq_storeLoc state i v]
  cases h : storeCertifiedByteElement state i v with
  | error e => simp [Except.map, Bind.bind, Except.bind]
  | ok next =>
    simpa only [h, Except.map, Bind.bind, Except.bind] using
      storeCertifiedByteElement_eq_storeLoc next j w

-- The first operation may canonicalize a mismatched incoming integer tag;
-- aliasing the same cell in the second operation retains the exact result.
theorem aliased_wrapping_readout :
    (do
      let next ← storeCertifiedByteElement
        ⟨Challenges.rawState, Challenges.rawState_normal⟩ 0 (.int (-1) .int64)
      storeCertifiedByteElement next 0 (.int 258 .uint16)).map
        (fun (next : { s : ExecState // NormalBackingAt s ⟨0⟩ 2 }) =>
          loadLoc next.val (.index (.base ⟨0⟩) 0)) =
      .ok (.ok (.int 2 .uint8)) := by rfl

end IndependentByteStore

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := [``propext, ``Quot.sound, ``Classical.choice]
  let mut checked := 0
  for (n, _) in env.constants.toList do
    let selected := match env.getModuleIdxFor? n with
      | some i =>
          let m := env.header.moduleNames[i.toNat]!
          m == `ByteStore || m.getRoot == `GoLean
      | none => true
    unless selected do continue
    for ax in (← collectAxioms n) do
      unless allowed.contains ax do
        throwError "Independent byte-store forbidden axiom: {n}: {ax}"
    checked := checked + 1
  logInfo s!"Independent byte-store: two composition challenges and {checked} declarations checked"
