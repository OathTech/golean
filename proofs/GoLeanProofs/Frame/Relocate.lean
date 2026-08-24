import GoLeanProofs.Frame.Sim

/-!
# The relocation seed: `FrameSim` at the rename-image (A4-U6 promotion lift)

**LINEAGE (clever-tricks doctrine): the separation-logic renaming
lemma — heap satisfaction is invariant under injective location
renaming (O'Hearn–Reynolds–Yang locality; the "renaming lemma" of
Yang–O'Hearn's semantic frame property) — instantiated as a
CONSTRUCTOR for the executable frame theorem's simulation relation.**

Promotion-ledger row taken from A4-U5 (two named consumers recorded
there): given any conforming shift `ρ` and body-invariance, the
rename-image of a state is `FrameSim`-related to it at the EMPTY
frame — a one-shot relocation seed. The existing seeds are the
zero-shift `frameSim_seed` and the incremental `rebaseSimT` chains;
this is the missing direct constructor for genuinely relocated
placements (non-identity witnesses; instantiating fixture-proven
equations at a run's real layout).

Additive-only: no existing Frame declaration is touched.

NAME DISAMBIGUATION (Iris reuse survey 2026-08-24, shortlist item 1):
the `GoLean.Frame` namespace is the MACHINE-LEVEL executable frame
theorem (state simulation over `ExecState`); it is unrelated to
iris-lean's `Iris.ProofMode` `Frame` typeclass (the BI-level framing
class over `PROP`, `ProofMode/Classes.lean:189`) and to the kit's
`wp_frame_*` lemmas (Go CALL-frame entry/exit laws). Three different
things sharing one word; cite accordingly.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-- Rename every key and every cell of a heap. -/
def renameHeap (ρ : Nat → Nat) (h : Heap) : Heap :=
  h.map (fun p => (renameLoc ρ p.1, renameCell ρ p.2))

/-- The rename-image of a state: heap keys+cells renamed, allocator
tracked through `ρ`, static tables untouched (programs contain no
renamable identity — `FrameSim.bodies_inv` is the side condition). -/
def renameState (ρ : Nat → Nat) (σ : ExecState) : ExecState :=
  { σ with heap := renameHeap ρ σ.heap, nextAddr := ρ σ.nextAddr }

/-- Lookup in a renamed heap: the renamed key finds exactly the
renamed cell (injectivity makes the key comparison transport). -/
theorem renameHeap_lookup {ρ : Nat → Nat}
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y) (h : Heap) (l : Loc) :
    Heap.lookup (renameHeap ρ h) (renameLoc ρ l)
      = (Heap.lookup h l).map (renameCell ρ) := by
  induction h with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨l', c'⟩ := p
      simp only [renameHeap, List.map_cons, Heap.lookup]
      rw [renameLoc_beq hinj l' l]
      cases hb : (l' == l) with
      | true => rfl
      | false => exact ih

/-- **The relocation seed**: any state whose allocator sits at the
shift threshold relocates to its rename-image under any conforming
shift — `FrameSim` at the empty frame. The two side conditions are
the standing ones: the allocator position and body invariance (a
program whose bodies mention a `locLit` pins that address — renaming
must fix it, which is exactly what `hbodies` checks). -/
theorem frameSim_relocate {ρ : Nat → Nat} {na₀ na : Nat}
    (hs : ShiftSpec ρ na₀ na) {σ : ExecState}
    (halloc : na₀ ≤ σ.nextAddr)
    (hbodies : ∀ f ∈ σ.functions.toList, renameStmt ρ f.body = f.body) :
    FrameSim ρ na₀ na [] σ (renameState ρ σ) := by
  refine ⟨hs, rfl, rfl, rfl, rfl, rfl, halloc, ?_, ?_, fun _ => rfl, hbodies⟩
  · intro l
    show Heap.lookup (renameHeap ρ σ.heap) (renameLoc ρ l) = _
    rw [renameHeap_lookup hs.inj]
    cases Heap.lookup σ.heap l <;> rfl
  · intro l c hl
    cases hl

end GoLean.Frame
