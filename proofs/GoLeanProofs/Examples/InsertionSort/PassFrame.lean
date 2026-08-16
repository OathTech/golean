import GoLeanProofs.Examples.InsertionSortProgram
import GoLeanProofs.Frame.Threshold
import GoLeanProofs.SliceMem
import GoLeanProofs.Frame.Rename
import GoLeanProofs.Frame.Sim
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Examples.InsertionSort.Canon

/-!
# InsertionSort — PassFrame

Per-phase shard of `GoLeanProofs.Examples.InsertionSort` (examples
phase-2 slice 0, lever 2, 2026-08-14). Every statement and proof here
is BYTE-IDENTICAL to the pre-split module; only file placement changed,
so Lake's module-level caching can see the phases separately. The
user-facing headline theorems live in the thin root module
`GoLeanProofs.Examples.InsertionSort`, whose docstring records the
example's design and the shard map.
-/

namespace GoLean.Examples.InsertionSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-! ## The per-pass frame layer

The machine re-allocates `j`/`$forFirst` on EVERY outer pass (fresh
addresses; the dead pair stays in the heap). The outer induction
therefore relates the true run to the tight canonical states through
the executable frame theorem: `ρsh d` fixes the four active cells and
shifts the pass-local region by the accumulated garbage `d = 2m`;
after each pass `rebaseSim` retires the pass's two cells INTO the
frame. -/

open GoLean.Frame

/-- The per-pass shift: identity on the active cells `0..3`, shift by
`d` on the pass-local region. -/
def ρsh (d : Nat) : Nat → Nat := ρT 4 d
-- (WP arc s1 lift 4: the kit's `ρT` at threshold 4 — the whole
-- shift/rebase layer now lives in `Frame/Threshold.lean`; this
-- wrapper keeps every downstream statement unchanged.)

theorem renCell_arr (ρ : Nat → Nat) (n : Nat) (l : List Int) :
    renameCell ρ (arrCell n l) = arrCell n l := by
  simp [renameCell, renameValue_locFree _ _ (locSup_mapU l)]

private theorem renCell_handle (d n : Nat) :
    renameCell (ρsh d) (handleCell n) = handleCell n := by
  simp [renameCell, renameValue, renameLoc, ρsh, ρT]

theorem base_ne {x y : Nat} (h : x ≠ y) :
    (Loc.base ⟨x⟩ : Loc) ≠ .base ⟨y⟩ := base_ne_of_ne h

/-- Lookup distributes over heap append (delegation to the kit form,
`Surface.lookup_append` — WP arc s1 lift 4). -/
theorem lookup_append (h1 h2 : Heap) (l : Loc) :
    Heap.lookup (h1 ++ h2) l
      = match Heap.lookup h1 l with
        | some c => some c
        | none => Heap.lookup h2 l :=
  GoLean.Surface.lookup_append h1 h2 l

private theorem lookup_σOut_ge {n : Nat} {l : List Int} {iv : Int}
    {ffv : Bool} {a : Nat} (ha : 4 ≤ a) :
    Heap.lookup (σOut n l iv ffv).heap (.base ⟨a⟩) = none := by
  simp [σOut, σOutT, Heap.lookup,
    beq_false_of_ne (base_ne (show (0 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (1 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (2 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (3 : Nat) ≠ a by omega))]

private theorem lookup_σIn_ge {n : Nat} {l : List Int} {iv jv : Int}
    {ffIv : Bool} {a : Nat} (ha : 6 ≤ a) :
    Heap.lookup (σIn n l iv jv ffIv).heap (.base ⟨a⟩) = none := by
  simp [σIn, σOutT, Heap.lookup,
    beq_false_of_ne (base_ne (show (0 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (1 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (2 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (3 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (4 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (5 : Nat) ≠ a by omega))]

private theorem lookup_σOut_field (n : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) (b : Loc) (tid : TypeId) (f : String) :
    Heap.lookup (σOut n l iv ffv).heap (.field b tid f) = none := rfl

private theorem lookup_σOut_index (n : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) (b : Loc) (i : Int) :
    Heap.lookup (σOut n l iv ffv).heap (.index b i) = none := rfl

private theorem lookup_σIn_field (n : Nat) (l : List Int) (iv jv : Int)
    (ffIv : Bool) (b : Loc) (tid : TypeId) (f : String) :
    Heap.lookup (σIn n l iv jv ffIv).heap (.field b tid f) = none := rfl

private theorem lookup_σIn_index (n : Nat) (l : List Int) (iv jv : Int)
    (ffIv : Bool) (b : Loc) (i : Int) :
    Heap.lookup (σIn n l iv jv ffIv).heap (.index b i) = none := rfl

/-- The function table carries no address literals (`by decide` over
the pinned lowering), so every `ρ` fixes the bodies. -/
theorem bodies_ρsh (ρ : Nat → Nat) :
    ∀ f ∈ (σOutT 0 [] 0 false [] 0).functions.toList,
      renameStmt ρ f.body = f.body :=
  renameBodies_id (n := 0) (fun x hx => absurd hx (Nat.not_lt_zero x))
    (by decide : funcListSup isortLowered.funcs.toList ≤ 0)

/-- The trivial-frame simulation at the loop entry (`m = 0`: the true
state IS the tight state; kit `frameSim_seed`). -/
theorem frameSim_zero (n : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) :
    FrameSim (ρsh 0) 4 4 [] (σOut n l iv ffv) (σOut n l iv ffv) :=
  frameSim_seed rfl (bodies_ρsh (ρT 4 0))

/-- **The frame REBASE** (the outer induction's between-passes step):
the pass's retired `j`/`$forFirst` cells (canonical 4/5) move INTO the
frame at their true addresses, the shift widens by 2, the canonical
state drops back to the tight 4-cell shape (kit `rebaseSimT` + this
example's fixed-cell enumeration — WP arc s1 lift 4). -/
theorem rebaseSim {d : Nat} {fr : Heap} {n : Nat} {l : List Int}
    {iv jv : Int} {σA : ExecState}
    (h : FrameSim (ρsh d) 4 (4 + d) fr (σIn n l iv jv false) σA) :
    FrameSim (ρsh (d + 2)) 4 (4 + (d + 2))
      (fr ++ retiredFrame (4 + d) [intcell jv, bcell false])
      (σOut n l iv false) σA := by
  refine rebaseSimT (retired := [intcell jv, bcell false]) h
    rfl rfl rfl rfl rfl rfl ?_ ?_
    (fun a ha => lookup_σIn_ge (by simpa using ha))
    (fun a ha => lookup_σOut_ge ha)
    ⟨fun b tid f => lookup_σIn_field n l iv jv false b tid f,
     fun b i => lookup_σIn_index n l iv jv false b i⟩
    ⟨fun b tid f => lookup_σOut_field n l iv false b tid f,
     fun b i => lookup_σOut_index n l iv false b i⟩
    (bodies_ρsh _)
  · intro a ha
    rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3)
      with rfl | rfl | rfl | rfl
    · exact ⟨rfl, fun c hc => by
        cases hc; exact fun d' => renCell_arr _ n l⟩
    · exact ⟨rfl, fun c hc => by
        cases hc; exact fun d' => renCell_handle d' n⟩
    · exact ⟨rfl, fun c hc => by cases hc; exact fun d' => rfl⟩
    · exact ⟨rfl, fun c hc => by cases hc; exact fun d' => rfl⟩
  · intro j hj
    match j, hj with
    | 0, _ => exact ⟨rfl, fun d' => rfl⟩
    | 1, _ => exact ⟨rfl, fun d' => rfl⟩

/-! ## Transfer plumbing: the shift fixes every anchor configuration
(all mentioned addresses are the active cells 0–3) -/

theorem renCfg_cmp (d : Nat) (b : Bool) :
    renameConfig (ρsh d) (.retV (.bool b) outerCmpCont)
      = .retV (.bool b) outerCmpCont := by
  with_unfolding_all rfl

theorem renCfg_stop (d : Nat) :
    renameConfig (ρsh d) (.next .stop) = .next .stop := rfl

/-- A canonical segment between shift-fixed configurations transfers to
the true placement: same fuel, same stream, related terminal states. -/
theorem transfer_seg {d : Nat} {fr : Heap} {σC σC' σA : ExecState}
    {c c' : Config} {k : Nat} {ch : Choices}
    (hFS : FrameSim (ρsh d) 4 (4 + d) fr σC σA)
    (hrun : stepFnIter k σC c ch = .ok (c', σC', ch))
    (hc : renameConfig (ρsh d) c = c) (hc' : renameConfig (ρsh d) c' = c') :
    ∃ σA', stepFnIter k σA c ch = .ok (c', σA', ch)
      ∧ FrameSim (ρsh d) 4 (4 + d) fr σC' σA' :=
  transfer_segT hFS hrun hc hc'


end GoLean.Examples.InsertionSort
