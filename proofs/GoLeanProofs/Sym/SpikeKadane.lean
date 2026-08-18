import GoLeanProofs.Sym.Refine
import GoLeanProofs.Examples.Kadane

/-!
# The Kadane non-vacuity WITNESS (WP arc slice 4; ruled OQ4)

`kd_su_A0_via_sym`: the shipped window `kd_su_A0_raw`'s statement,
BYTE-IDENTICAL (`Examples/Kadane.lean:1258`), discharged through the
general pipeline — one `rfl` evaluator run + ONE application of
**`symEvalWindow_refines`** (the refinement theorem) + the γ-image
conversions. Its hand twin stays in-tree as the direct diff
(design §6.3). The window exercises every v1 mechanism: symbolic scalar
heap reads, a comparison constructor, a store through the normalize
catch-all, opaque-atom ride-through, and a Q1 quit at the boundary.

HISTORY (phase 2, log unit S4.8): phase 1 proved this same statement
through a BESPOKE fragment-restricted route (`spikeFrag`/
`spikeStep_sound`/`spikeWindow`/`spikeWindow_sound`) as the mandatory
kernel-cost spike (gate PASS, numbers in `docs/wp-arc-log/s4.md`
§S4.3). That apparatus is RETIRED in this commit: the master walk
(`Sym/Walk.lean`) build-gates every arm the 16-shape spike guard
gated and more, and the refinement theorem's driver induction
(`Sym/Refine.lean`) is `spikeWindow_sound` generalized — keeping the
guarded driver would be dead scaffolding beside its own theorem. The
spike's measured numbers remain valid history (the transported route's
cost profile is unchanged: the same evaluator `rfl`, one lemma
application, the same γ-simp). The quit DIAGNOSTIC stays available as
`symEvalQuit` (Mirror).

This file is Kadane-specific ON PURPOSE (a witness instantiation, not
kit surface).
-/

namespace GoLean.Sym.Spike

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym
open GoLean.Examples.Kadane

/-! ## The Kadane A0 window fixtures (design §5.2's instantiation,
hand-written reflect-free so the kernel reduces them; validated by
`#guard` BEFORE any rfl — the #eval-before-decide rule) -/

/-- A symbolic-int64 cell at symbol `i`. -/
def suCell (i : Nat) : HeapCell symDom :=
  .mk (some (.int .int64)) (.int (.var i) .int64)

/-- The setup-loop heap front (`kHeapSu nv sv n l iv flag`'s symbolic
form): vars 0/1/2 = nv/sv/iv; CELL atoms 0/1/2 = the symbolic-length
handle/backing/handle cells 4–6 (JC-6). -/
def suHeap (flag : SymBool) : SymHeap :=
  [(.base ⟨0⟩, suCell 0), (.base ⟨1⟩, suCell 1),
   (.base ⟨2⟩, .mk (some (.array 8 (.int .int64)))
      (.array ⟨List.replicate 8 (.int (.lit 0) .int64)⟩)),
   (.base ⟨3⟩, .mk (some (.int .int64)) (.int (.lit 0) .int64)),
   (.base ⟨4⟩, .atom 0), (.base ⟨5⟩, .atom 1), (.base ⟨6⟩, .atom 2),
   (.base ⟨7⟩, suCell 2),
   (.base ⟨8⟩, .mk (some .bool) (.bool flag))]

def suS0 : SymState := { heap := suHeap (.lit true), nextAddr := 9 }
def suS25 : SymState := { heap := suHeap (.lit false), nextAddr := 9 }
def suFrameStop : SymCont := .frame [] [] [] [] .stop false
def suTailAfterSetup : SymCont :=
  .seq [kdS4, kdS5, kdS6, kdS7] [kSScope, kBaseScope] suFrameStop
def suHeadTail : SymCont :=
  .seq [] kSuEnv
    (.seq [] [[("i", .base ⟨7⟩)], kSScope, kBaseScope] suTailAfterSetup)
def suC0 : SymConfig :=
  .exec (.while (.boolLit true) kdSuWhileBody) kSuEnv suHeadTail
def suLoopK : SymCont := .loop (.boolLit true) kdSuWhileBody kSuEnv suHeadTail
def suCmpK : SymCont :=
  .ifK (.seqn #[]) .breakStmt kSuEnv1 (.seq [kdSuStoreBlock] kSuEnv1 suLoopK)
def suC25 : SymConfig := .retV (.bool (.ltI (.var 2) (.var 0))) suCmpK

/-- The §5.2 valuation: the hand lemma's binders as the symbols'
values. -/
def kdρ (nv sv iv : Int) (n : Nat) (l : List Int) : Valuation where
  ints := fun i => if i = 0 then nv else if i = 1 then sv else iv
  bools := fun _ => false
  vals := fun _ => .nil
  cells := fun i =>
    if i = 0 then kHandle n else if i = 1 then kBack n l else kHandle n

-- Compiled-evaluation guard BEFORE the kernel rfl (the
-- #eval-before-decide rule): the UNGUARDED driver completes the same
-- 25 steps the phase-1 guarded driver completed.
#guard (symEvalWindow 25 suS0 suC0).1 == 25

/-! ## γ-image conversions (the transported statement lands on the hand
lemma's exact spellings) -/

theorem γ_suS (σ : ExecState) (nv sv iv : Int) (n : Nat) (l : List Int)
    (b : Bool) :
    γS (kdρ nv sv iv n l) σ { heap := suHeap (.lit b), nextAddr := 9 }
      = kSt σ (kHeapSu nv sv n l iv b) 9 := by
  simp [γS, concS, concHeap, suHeap, suCell, concCell, kdρ, symInterp,
    γB, γI, kHeapSu, kHeap0, ki64, kbool, kHandle, kBack, kArr8,
    kZeros8, List.replicate]

theorem γ_suC0 (nv sv iv : Int) (n : Nat) (l : List Int) :
    γC (kdρ nv sv iv n l) suC0 = kdSuHeadCfg := by
  simp [γC, concC, concK, suC0, suHeadTail, suTailAfterSetup,
    suFrameStop, kdSuHeadCfg, kdSuHeadTail, kdTailAfterSetup,
    kdFrameStop]

theorem γ_suC25 (nv sv iv : Int) (n : Nat) (l : List Int) :
    γC (kdρ nv sv iv n l) suC25
      = .retV (.bool (decide (iv < nv))) kdSuCmpK := by
  simp [γC, concC, concK, suC25, suCmpK, suLoopK, suHeadTail,
    suTailAfterSetup, suFrameStop, kdSuCmpK, kdSuLoopK, kdSuHeadTail,
    kdTailAfterSetup, kdFrameStop, symInterp, γB, γI, kdρ]

/-! ## THE WITNESS -/

/-- `kd_su_A0_raw`'s statement, BYTE-IDENTICAL
(`Examples/Kadane.lean:1258`), discharged through THE REFINEMENT
THEOREM: one `rfl` evaluator run + `symEvalWindow_refines` + the
γ conversions. The hand twin stays in-tree as the direct diff. -/
theorem kd_su_A0_via_sym (σ : ExecState) (nv sv : Int) (n : Nat)
    (l : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 25 (kSt σ (kHeapSu nv sv n l iv true) 9) kdSuHeadCfg ch
      = .ok (.retV (.bool (decide (iv < nv))) kdSuCmpK,
          kSt σ (kHeapSu nv sv n l iv false) 9, ch) := by
  have hrun : symEvalWindow 25 suS0 suC0 = (25, suS25, suC25) := by rfl
  have ht := symEvalWindow_refines hrun (kdρ nv sv iv n l) σ ch
  simp only [show suS0 = { heap := suHeap (.lit true), nextAddr := 9 } from rfl,
    show suS25 = { heap := suHeap (.lit false), nextAddr := 9 } from rfl] at ht
  rw [γ_suC0, γ_suC25, γ_suS (b := true), γ_suS (b := false)] at ht
  exact ht

end GoLean.Sym.Spike
