import GoLeanProofs.SurfaceExit
import GoLeanProofs.Specs.GoldenSliceWP

/-!
# The golden surface discharge (arc `spec-surface` stages 5–6)

The three step-0 targets from `GoLeanProofs/Surface.lean`, proven:

- `goldenTriple` — `{r ↦ 0} r = incViaCall() {r ↦ 2}` over the frontend's
  actual lowering, via the generic exit theorem. Per the anti-hack
  invariant, the per-program work here is EXACTLY: two fragment shape
  checks and the WP proof — which is `wp_incViaCallLowered_ret2`, reused
  as-is from the golden walk.
- `goldenReturnsTwo` — the system-register (Verdi-register) corollary: the
  designated output cell, BY ADDRESS, holds 2 in every terminating run.
  This is the pinned-observable form entitled to the name **lowering
  target** (`docs/2026-07-21_native-spec-surface.md` D8) — no `∃` over
  addresses anywhere.
- `goldenNotThree` — the negative twin, now the promised two-line
  corollary.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Rel GoLean.GoCore.Correspondence
open GoLean.Surface GoLean.Iris GoLean.Iris.GoldenSlice

namespace GoLean.Surface

/-- **Step-0 target A′, proven: the full golden spec** — the FRAME-CLOSED
triple (`{r ↦ 0} r = incViaCall() {r ↦ 2}` in any heap where the output
cell is allocated, frame untouched) plus progress (safe, non-panicking
execution), discharged through the once-proven exit pipe. The WP
obligation is `wp_incViaCallLowered_ret2` reused unchanged — the frame
never appears in the per-program proof. -/
theorem goldenSpec : goldenSpec_statement := by
  unfold goldenSpec_statement
  refine goSpec_of_wp ?_ ?_ ?_
  · -- shape check: the driver is a fragment statement
    exact .call
      (by intro a ha; simp at ha; subst ha; exact .var _)
      (by intro e he; simp at he)
  · -- shape check: the golden functions are fragment functions
    exact σg_inv.funcs
  · -- the WP proof: the golden walk, reused as-is
    intro _inst hprog
    simp only [outCell0, outCell2, embed]
    iintro H0
    iapply (wp_incViaCallLowered_ret2 (ta := ⟨0⟩) (ty := .int .int)
      (hmain := by rw [hprog]; rfl)
      (hinc := by rw [hprog]; rfl)
      (htgt := by simp [LocalEnv.lookup, Scope.lookup]))
    isplitl [H0]
    · iexact H0
    iintro H2
    iapply (wp_value' (v := ()))
    iexact H2

/-- **Step-0 target A″, proven: the golden function spec** — the
engineer-readable form: `incViaCall()` needs no heap and returns 2, into
any caller cell, over any prior value, beside any frame. The WP obligation
is `wp_incViaCallLowered_ret2` reused unchanged — the FOURTH reuse of the
same walk across four different statement shapes. -/
theorem goldenFuncSpec : goldenFuncSpec_statement := by
  unfold goldenFuncSpec_statement GoFuncSpec
  intro ra w
  refine goSpec_of_wp ?_ ?_ ?_
  · exact .call
      (by intro a ha; simp at ha; subst ha; exact .var _)
      (by intro e he; simp at he)
  · exact σg_inv.funcs
  · intro _inst hprog
    simp only [embed]
    iintro ⟨H0, -⟩
    iapply (wp_incViaCallLowered_ret2 (ta := ⟨ra⟩) (ty := .int .int)
      (w := w)
      (hmain := by rw [hprog]; rfl)
      (hinc := by rw [hprog]; rfl)
      (htgt := by simp [LocalEnv.lookup, Scope.lookup]))
    isplitl [H0]
    · iexact H0
    iintro H2
    iapply (wp_value' (v := ()))
    iexists (2 : Int)
    isplitl [H2]
    · iexact H2
    · ipureintro; rfl

/-- **Step-0 target A, proven: the golden triple** (the triple half of
`goldenSpec`). -/
theorem goldenTriple : goldenTriple_statement := by
  unfold goldenTriple_statement
  have h := goldenSpec
  unfold goldenSpec_statement GoSpec at h
  exact h.1

/-- **Step-0 target B, proven — THE LOWERING TARGET.** Every terminating
interpreter run of the seeded driver over the frontend's actual lowering
leaves `int 2` in the designated output cell at base address 0. Plain
first-order statement over the interpreter; the address is pinned by the
driver convention, not existential. -/
theorem goldenReturnsTwo : goldenReturnsTwo_statement := by
  unfold goldenReturnsTwo_statement
  intro fuel ch σf ch' hrun
  have htriple := goldenTriple
  unfold goldenTriple_statement at htriple
  have hres := htriple goldenOut.heap 1 (heapletOf goldenOut.heap)
    (∅ : Heaplet)
    { bounded := by
        intro n hn
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rfl
      frag := by
        intro loc cell h
        simp only [goldenOut, Heap.lookup] at h
        split at h
        · injection h with h'
          subst h'
          exact ⟨.int 0 .int, fun t ht => by
            injection ht with ht'; subst ht'; exact .int .int⟩
        · exact absurd h (by simp)
      disj := fun k => .inr (by
        rw [heaplet_get?_eq]
        exact LawfulPartialMap.get?_empty (M := GoHeapF) (k := k))
      cover := fun k c => by
        constructor
        · exact fun h => .inl h
        · rintro (h | h)
          · exact h
          · rw [heaplet_get?_eq,
              LawfulPartialMap.get?_empty (M := GoHeapF) (k := k)] at h
            cases h
      sat_pre := by rfl }
    fuel ch σf ch' hrun
  obtain ⟨h, _hd, hsub, _hF, hsat⟩ := hres
  rw [show h = (∅ : Heaplet).insert 0 ⟨some (.int .int), .int 2 .int⟩
    from hsat] at hsub
  have hget := hsub 0 ⟨some (.int .int), .int 2 .int⟩ (by
    rw [heaplet_get?_eq, heaplet_insert_eq]
    exact LawfulPartialMap.get?_insert_eq rfl)
  rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hget
  exact loadLoc_base_of_lookup hget

/-- **Step-0 negative twin, proven** — and, as the design note promised,
it is now a two-line corollary of the pinned positive rather than a design
problem: the output cell holds 2, so it does not hold 3. -/
theorem goldenNotThree : goldenNotThree_statement := by
  unfold goldenNotThree_statement
  intro fuel ch σf ch' hrun h3
  have h2 := goldenReturnsTwo fuel ch σf ch' hrun
  have := h2.symm.trans h3
  injection this with hval
  injection hval with hn _
  exact absurd hn (by decide)

end GoLean.Surface
