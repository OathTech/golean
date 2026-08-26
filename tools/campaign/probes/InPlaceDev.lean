import GoLeanProofs.Sym.SpillTransport

/-! Scratch: develop `applyStmtOp_append1_inplace_at` (the in-place
one-element append apply — the machine's other appendSlice branch). -/

namespace GoLean.Sym

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface

theorem applyStmtOp_append1_inplace_at {σ σ₁ σ₂ : ExecState} {elem : Ty}
    {nt : Nat} {tloc : Loc} {b : Loc} {off len cap : Nat}
    {eb : Loc} {eoff elen ecap : Nat} {w : GoValue}
    {ch : Choices}
    (hfits : len + 1 ≤ cap) (hec : elen ≤ ecap)
    (hvisE : sliceVisibleValues σ ⟨some eb, eoff, elen, ecap⟩ = .ok #[w])
    (hst1 : storeLoc σ (.index b (Int.ofNat (off + len))) w = .ok σ₁)
    (hst2 : storeLoc σ₁ tloc (.slice ⟨some b, off, len + 1, cap⟩) = .ok σ₂) :
    applyStmtOp σ ch (.appendSlice elem) nt
      [.addr tloc, .slice ⟨some b, off, len, cap⟩,
       .slice ⟨some eb, eoff, elen, ecap⟩]
      = .ok (σ₂, ch) := by
  simp only [applyStmtOp, valueAsSlice, valueAsLoc, Bind.bind,
    Except.bind, pure, Except.pure,
    validateSlice_some_ok (Nat.le_of_succ_le hfits),
    validateSlice_some_ok hec, hvisE]
  rw [if_pos (by simpa using hfits)]
  rw [← Array.forIn_toList,
    show (#[w] : Array GoValue).toList = [w] from rfl,
    List.forIn_cons]
  simp only [Nat.add_zero, hst1, Bind.bind, Except.bind, pure, Except.pure,
    List.forIn_nil]
  rw [show (#[w] : Array GoValue).size = 1 from rfl, hst2]

theorem stepFn_appendInPlace_transport (ρ : Valuation) (σ σ₁ : ExecState)
    {S S₂ : SymState} {elem : Ty} {nt : Nat}
    {tloc : Loc} {oldv : GoLean.Sym.Value symDom} {b : Loc}
    {off len cap : Nat}
    {eb : Loc} {eoff elen ecap : Nat} {w : GoValue}
    {env : LocalEnv} {k : GoLean.Sym.Cont symDom} {ch : Choices}
    (hold : concV (symInterp ρ) oldv
      = .slice ⟨some b, off, len, cap⟩)
    (hfits : len + 1 ≤ cap) (hec : elen ≤ ecap)
    (hvisE : sliceVisibleValues (γS ρ σ S) ⟨some eb, eoff, elen, ecap⟩
      = .ok #[w])
    (hst1 : storeLoc (γS ρ σ S) (.index b (Int.ofNat (off + len))) w
      = .ok σ₁)
    (hst2 : storeLoc σ₁ tloc (.slice ⟨some b, off, len + 1, cap⟩)
      = .ok (γS ρ σ S₂)) :
    stepFn (γS ρ σ S)
      (γC ρ (.retV (.slice ⟨some eb, eoff, elen, ecap⟩)
        (.stmtOpK (.appendSlice elem) nt [oldv, .addr tloc] [] env k))) ch
      = .ok (γC ρ (.next k), γS ρ σ S₂, ch) := by
  have happ := applyStmtOp_append1_inplace_at (σ := γS ρ σ S)
    (elem := elem) (nt := nt) (ch := ch) hfits hec hvisE hst1 hst2
  simp only [γC, concC, concK, concV, List.map_cons, List.map_nil]
  rw [hold]
  simp only [stepFn]
  rw [show ((GoValue.slice ⟨some eb, eoff, elen, ecap⟩) ::
        [GoValue.slice ⟨some b, off, len, cap⟩, GoValue.addr tloc]).reverse
      = [.addr tloc, .slice ⟨some b, off, len, cap⟩,
         .slice ⟨some eb, eoff, elen, ecap⟩] from rfl, happ]
  rfl

/-! ## Witness -/

private def ipWitS : SymState :=
  { heap := [
      (.base ⟨0⟩, .mk (some (.slice (.int .uint64)))
        (.slice ⟨some (.base ⟨1⟩), 0, 1, 2⟩)),
      (.base ⟨1⟩, .mk (some (.array 2 (.int .uint64)))
        (.array #[.int (.lit 7) .uint64, .int (.lit 0) .uint64])),
      (.base ⟨2⟩, .mk (some (.array 1 (.int .uint64)))
        (.array #[.int (.lit 9) .uint64]))],
    nextAddr := 3 }

private def ipWitSmid : SymState :=
  { heap := [
      (.base ⟨0⟩, .mk (some (.slice (.int .uint64)))
        (.slice ⟨some (.base ⟨1⟩), 0, 1, 2⟩)),
      (.base ⟨1⟩, .mk (some (.array 2 (.int .uint64)))
        (.array #[.int (.lit 7) .uint64, .int (.lit 9) .uint64])),
      (.base ⟨2⟩, .mk (some (.array 1 (.int .uint64)))
        (.array #[.int (.lit 9) .uint64]))],
    nextAddr := 3 }

private def ipWitS₂ : SymState :=
  { heap := [
      (.base ⟨0⟩, .mk (some (.slice (.int .uint64)))
        (.slice ⟨some (.base ⟨1⟩), 0, 2, 2⟩)),
      (.base ⟨1⟩, .mk (some (.array 2 (.int .uint64)))
        (.array #[.int (.lit 7) .uint64, .int (.lit 9) .uint64])),
      (.base ⟨2⟩, .mk (some (.array 1 (.int .uint64)))
        (.array #[.int (.lit 9) .uint64]))],
    nextAddr := 3 }

theorem stepFn_appendInPlace_transport_witness (ρ : Valuation)
    (σ : ExecState) (ch : Choices) :
    stepFn (γS ρ σ ipWitS)
      (γC ρ (.retV (.slice ⟨some (.base ⟨2⟩), 0, 1, 1⟩)
        (.stmtOpK (.appendSlice (.int .uint64)) 1
          [.slice ⟨some (.base ⟨1⟩), 0, 1, 2⟩, .addr (.base ⟨0⟩)] [] [] .stop)))
      ch
      = .ok (γC ρ (.next .stop), γS ρ σ ipWitS₂, ch) := by
  refine stepFn_appendInPlace_transport ρ σ (γS ρ σ ipWitSmid)
    (by with_unfolding_all rfl)
    (by decide) (by decide)
    (by with_unfolding_all rfl)
    (by with_unfolding_all rfl)
    (by with_unfolding_all rfl)

end GoLean.Sym
