import Iris.ProofMode
import Iris.BI.Lib.GenHeap
import GoLeanProofs.Ghost

/-!
# U0 reuse adoptions — the boundary pin's new instances, witnessed on OUR tier

The U0 reuse table's ADOPT-at-bump rows U1/U3
(`docs/2026-08-28_u0-refresh-log.md` §3), each pinned by a discharge
witness on GoCore's own ghost state so the adoption is a checked fact,
not a claim. These witnesses are deliberately tiny: they certify the
upstream instances RESOLVE AND FIRE for our `IProp GF`/points-to tier —
the consumer-side rewiring they enable is owned elsewhere, named below.

- **U1 (WP modality instances — `addModalFupdWp`, the `InOut`-restated
  `ElimModal`s, the WP `ElimAcc`s; upstream `WeakestPre.lean:687/641/695`
  at pin `e7a0a438`):** PRESENT at the pin (verified by read), and a
  MEASURED FINDING for G-AUTO stands recorded: from outside the iris
  package, `imod H`/`icases H with >H` on a context `|={E}=>` against a
  WP goal is refused by the proof-mode front-end ("is not a modality")
  at this rev even though the `ElimModal` instances exist — so the
  modality-dance retirement (the 4-step `go_walk_dance` body, its two
  `idance` macros, 393 `fupd_intro` sites) is NOT a free rename; it is
  G-AUTO's measured work, with this datum as its baseline. No witness
  here rather than a fake one — the honest state is "instances landed,
  tactic exploitation owed". The `ElimAcc` pair's consumer is
  invariant/atomic access at G-INV/G-CONC, exercised when the first
  invariant opens at our tier.
- **U3 (`frame_pointsto` + points-to `CombineSepGives`; upstream
  `GenHeap.lean:214/161`):** fractional points-to recombination by
  `iframe` alone, and two-observer agreement as a pure fact — the
  per-field split/combine ergonomics G-REPR's representation
  predicates sit on. CONSUMER: G-REPR (C-08 `protoclone`'s
  sibling-frame write test is its gate).
-/

open Iris Iris.ProgramLogic Iris.Std
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open Iris.ProgramLogic.Language.Notation Iris.BI

namespace GoLean.Iris

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **U3 witness (recombination)** — `frame_pointsto`
(`instFramePointsTo` + `FrameFractionalQp`): two fractional views of a
cell recombine to the sum by `iframe` alone — the split/combine move
every per-field representation predicate makes. -/
example {a : Nat} {c : HeapCell} {q₁ q₂ : Qp} :
    iprop(a ↦{.own q₁} c ∗ a ↦{.own q₂} c)
      ⊢@{IProp GF} a ↦{.own (q₁ + q₂)} c := by
  iintro ⟨H1, H2⟩
  iframe

/-- **U3 witness (agreement)** — the points-to `CombineSepGives`
instance: two observers of one cell agree, as a pure fact, with the
validity side-condition carried by the instance. -/
example {a : Nat} {c₁ c₂ : HeapCell} {q₁ q₂ : Qp} :
    iprop(a ↦{.own q₁} c₁ ∗ a ↦{.own q₂} c₂)
      ⊢@{IProp GF} ⌜c₁ = c₂⌝ := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %hv
  ipureintro
  exact hv.2

end

end GoLean.Iris
