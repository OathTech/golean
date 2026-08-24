import GoLeanProofs.Sym.PickTransport
import GoLeanProofs.SliceMem

/-!
# The append-spill transport (A4-U10 deliverable 1)

**LINEAGE: symbolic-execution path-condition splitting at a
nondeterministic-choice site — the same classic as
`stepFn_pick_transport` (choice-point transport in the
symbolic-execution-by-conservative-extension frame, design
`2026-08-22_campaign-arc4-sym-extension-design.md` §4(ii)) — realized
over the SliceMem Group-4 spill machinery
(`applyStmtOp_append1_spill`'s walk, WP arc s2 item 3) instead of the
map-pick step.**

The appendSlice SPILL is the machine's second choice-consumption site
(`ChoiceSite.appendSpill`): a reallocating one-element append consumes
one capacity choice of width `appendSpillWidth` and allocates a fresh
backing cell whose declared type `.array newCap elem` carries the
REALIZED capacity. The mirror quits `.q3Choice` at exactly the apply
configuration (`applyStmtOp'`, Mirror.lean), so a window ends AT the
spill and this transport crosses it in one machine step, exactly as
`stepFn_pick_transport` crosses a map pick.

The §4(ii) collapse at this site: the realized capacity
`appendRealizedCap cap (len+1) extra` depends on the consumed choice,
so the choice-dependent artifacts (the backing CELL — value AND
declared type — and the slice handle written to the target) enter the
post fixture as VALUATION atoms (`Valuation.cells` — whose docstring
names the append-backing declared type as the design case — and
`Valuation.vals`), and ONE post-window literal serves every consumed
choice; the handler's prefix-derived valuation absorbs the spill.

Shapes covered: ONE appended element (`#[w]` visible in the elems
operand), any old-slice handle (nil base included — `r.msgs` at init
is the nil slice; the SliceMem lemma pins a `some` base). All three
motivating sites (handleHeartbeat + handleAppendEntries `r.msgs`
appends, becomeLeader's appendEntry path) are one-element appends; a
multi-element variant is future work on its first consumer.
-/

namespace GoLean.Sym

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem (appendRealizedCap appendRealizedCap_lower
  appendRealizedCap_upper)

/-- `validateSlice` succeeds at a `some`-base handle with `len ≤ cap`
(the SliceMem fact is `private`; re-proved here for the Option-base
walk). -/
theorem validateSlice_some_ok {b : Loc} {off len cap : Nat}
    (hcap : len ≤ cap) :
    validateSlice ⟨some b, off, len, cap⟩ = .ok () := by
  simp [validateSlice, Nat.not_lt.mpr hcap]

/-- **The spill apply at the SINGLE realized capacity** (the SliceMem
Group-4 walk, generalized to an Option-base old handle — the nil
outbox — and conditioned at exactly the realized capacity rather than
capacity-generically; `nt` is ignored by the appendSlice arm and stays
free). -/
theorem applyStmtOp_append1_spill_at {σ σ₂ : ExecState} {elem : Ty}
    {nt : Nat} {tloc : Loc} {sb : Option Loc} {off len cap : Nat}
    {eb : Loc} {eoff elen ecap : Nat} {w : GoValue}
    {old : Array GoValue} {bk : GoValue}
    {ch ch' : Choices} {extra : Nat}
    (hfull : cap < len + 1) (hec : elen ≤ ecap)
    (hvalidO : validateSlice ⟨sb, off, len, cap⟩ = .ok ())
    (hvisE : sliceVisibleValues σ ⟨some eb, eoff, elen, ecap⟩ = .ok #[w])
    (hvisO : sliceVisibleValues σ ⟨sb, off, len, cap⟩ = .ok old)
    (hcons : ch.consume (appendSpillWidth cap (len + 1)) = (extra, ch'))
    (hbuild : buildAppendBackingValue σ elem old #[w]
        (appendRealizedCap cap (len + 1) extra) = .ok bk)
    (htgt : storeLoc { σ with
          heap := GoCore.Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
            ⟨some (.array (appendRealizedCap cap (len + 1) extra) elem), bk⟩,
          nextAddr := σ.nextAddr + 1 } tloc
        (.slice ⟨some (.base ⟨σ.nextAddr⟩), 0, len + 1,
          appendRealizedCap cap (len + 1) extra⟩)
      = .ok σ₂) :
    applyStmtOp σ ch (.appendSlice elem) nt
      [.addr tloc, .slice ⟨sb, off, len, cap⟩,
       .slice ⟨some eb, eoff, elen, ecap⟩]
      = .ok (σ₂, ch') := by
  simp only [applyStmtOp, valueAsSlice, valueAsLoc, Bind.bind,
    Except.bind, pure, Except.pure, hvalidO, validateSlice_some_ok hec,
    hvisE]
  rw [if_neg (by simp; omega)]
  simp only [hvisO, Bind.bind, Except.bind, pure, Except.pure]
  simp only [Choices.consumeAt_appendSpill,
    show (#[w] : Array GoValue).size = 1 from rfl, hcons]
  rw [show len + 1 + ((appendGrowthCap cap (len + 1) - (len + 1)
        + extra) % appendSpillWidth cap (len + 1))
      = appendRealizedCap cap (len + 1) extra from rfl]
  rw [hbuild]
  simp only [ExecState.alloc, ExecState.freshLoc, Bind.bind,
    Except.bind, pure, Except.pure]
  rw [htgt]

/-- **THE APPEND-SPILL TRANSPORT**: the spill apply step at a γ-image
— mirror-side configuration, machine-level conclusion, post state
reaching a given mirror image (`S₂` carries the choice-dependent
backing cell/handle as valuation atoms; the `htgt` premise is where a
handler discharges the target write-back, e.g. through the Lens store
laws or closed evaluation at its fixture). One appended element; the
old handle may be nil-based. -/
theorem stepFn_appendSpill_transport (ρ : Valuation) (σ : ExecState)
    {S S₂ : SymState} {elem : Ty} {nt : Nat}
    {tloc : Loc} {sb : Option Loc} {off len cap : Nat}
    {eb : Loc} {eoff elen ecap : Nat} {w : GoValue}
    {old : Array GoValue} {bk : GoValue}
    {env : LocalEnv} {k : GoLean.Sym.Cont symDom}
    {ch ch' : Choices} {extra : Nat}
    (hfull : cap < len + 1) (hec : elen ≤ ecap)
    (hvalidO : validateSlice ⟨sb, off, len, cap⟩ = .ok ())
    (hvisE : sliceVisibleValues (γS ρ σ S) ⟨some eb, eoff, elen, ecap⟩
      = .ok #[w])
    (hvisO : sliceVisibleValues (γS ρ σ S) ⟨sb, off, len, cap⟩ = .ok old)
    (hcons : ch.consume (appendSpillWidth cap (len + 1)) = (extra, ch'))
    (hbuild : buildAppendBackingValue (γS ρ σ S) elem old #[w]
        (appendRealizedCap cap (len + 1) extra) = .ok bk)
    (htgt : storeLoc { γS ρ σ S with
          heap := GoCore.Heap.set (γS ρ σ S).heap (.base ⟨(γS ρ σ S).nextAddr⟩)
            ⟨some (.array (appendRealizedCap cap (len + 1) extra) elem), bk⟩,
          nextAddr := (γS ρ σ S).nextAddr + 1 } tloc
        (.slice ⟨some (.base ⟨(γS ρ σ S).nextAddr⟩), 0, len + 1,
          appendRealizedCap cap (len + 1) extra⟩)
      = .ok (γS ρ σ S₂)) :
    stepFn (γS ρ σ S)
      (γC ρ (.retV (.slice ⟨some eb, eoff, elen, ecap⟩)
        (.stmtOpK (.appendSlice elem) nt
          [.slice ⟨sb, off, len, cap⟩, .addr tloc] [] env k))) ch
      = .ok (γC ρ (.next k), γS ρ σ S₂, ch') := by
  have happ := applyStmtOp_append1_spill_at (σ := γS ρ σ S) (nt := nt)
    hfull hec hvalidO hvisE hvisO hcons hbuild htgt
  simp only [γC, concC, concK, concV, List.map_cons, List.map_nil]
  simp only [stepFn]
  rw [show ((GoValue.slice ⟨some eb, eoff, elen, ecap⟩) ::
        [GoValue.slice ⟨sb, off, len, cap⟩, GoValue.addr tloc]).reverse
      = [.addr tloc, .slice ⟨sb, off, len, cap⟩,
         .slice ⟨some eb, eoff, elen, ecap⟩] from rfl, happ]
  rfl

/-! ## §3.3 discharge witness — the transport instantiated on a
concrete two-cell state (a nil `[]uint64` grown by one element), every
premise discharged; #eval-checked in `artifacts/probe/HhU10Probe3.lean`
before these `rfl`s were asked of the kernel. -/

private def spillWitS : SymState :=
  { heap := [
      (.base ⟨0⟩, .mk (some (.slice (.int .uint64)))
        (.slice ⟨none, 0, 0, 0⟩)),
      (.base ⟨1⟩, .mk (some (.array 1 (.int .uint64)))
        (.array #[.int (.lit 7) .uint64]))],
    nextAddr := 2 }

private def spillWitS₂ : SymState :=
  { heap := [
      (.base ⟨0⟩, .mk (some (.slice (.int .uint64)))
        (.slice ⟨some (.base ⟨2⟩), 0, 1, 4⟩)),
      (.base ⟨1⟩, .mk (some (.array 1 (.int .uint64)))
        (.array #[.int (.lit 7) .uint64])),
      (.base ⟨2⟩, .mk (some (.array 4 (.int .uint64)))
        (.array #[.int (.lit 7) .uint64, .int (.lit 0) .uint64,
                  .int (.lit 0) .uint64, .int (.lit 0) .uint64]))],
    nextAddr := 3 }

/-- The witness: at the empty-stream head choice (extra 0, the
growth-formula capacity 4), the spill step crosses and lands at the
constructed mirror image. -/
theorem stepFn_appendSpill_transport_witness (ρ : Valuation)
    (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ spillWitS)
      (γC ρ (.retV (.slice ⟨some (.base ⟨1⟩), 0, 1, 1⟩)
        (.stmtOpK (.appendSlice (.int .uint64)) 1
          [.slice ⟨none, 0, 0, 0⟩, .addr (.base ⟨0⟩)] [] [] .stop)))
      (0 :: rest)
      = .ok (γC ρ (.next .stop), γS ρ σ spillWitS₂, rest) := by
  refine stepFn_appendSpill_transport ρ σ (extra := 0)
    (by decide) (by decide) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl)

end GoLean.Sym
