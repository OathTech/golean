import GoLeanProofs.SurfaceExit
import GoLeanProofs.Specs.GoldenSliceWP

/-!
# The golden surface discharge (R3 restoration)

The step-0 targets from `GoLeanProofs/Surface.lean`, re-proven over the
fine-grained machine. The statements are the Surface module's, unchanged
in content (modulo the two recorded reshape deltas: env as a wrapper
argument, the retired fragment side-condition — both STRENGTHENINGS);
the discharges are strictly simpler than before the reshape: the
fragment shape checks are gone, and each WP obligation is the golden
walk applied once.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface GoLean.Iris GoLean.Iris.GoldenSlice

namespace GoLean.Surface

/-- **The full golden spec, proven** — the frame-closed triple
(`{r ↦ 0} r = incViaCall() {r ↦ 2}` in any heap where the output cell is
allocated, frame untouched) plus progress, through the exit pipe. The
per-program work is exactly the WP proof: `wp_goldenDriver`. -/
theorem goldenSpec : goldenSpec_statement := by
  unfold goldenSpec_statement
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths _htypes
  exact wp_goldenDriver hprog hmeths

/-- **The golden function spec, proven** — "`incViaCall()` needs no heap
and returns 2", into any caller cell, over any prior value, beside any
frame; the generic walk `wp_goldenCall` applied at the quantified target. -/
theorem goldenFuncSpec : goldenFuncSpec_statement := by
  unfold goldenFuncSpec_statement GoFuncSpec
  intro ra w
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths _htypes
  simp only [embed]
  iintro ⟨H0, -⟩
  iapply (wp_goldenCall (w := w) (x := "$callres") rfl hprog hmeths)
  isplitl [H0]
  · iexact H0
  iintro H2
  iapply (wp_value' (v := ()))
  iexists (2 : Int)
  isplitl [H2]
  · iexact H2
  · ipureintro
    rfl

/-- **The golden register invariant, proven**: at EVERY relation-reachable
configuration of the seeded driver, the output cell holds `int 0` or
`int 2` — through the invariance exit pipe, with the WP obligation the
invariant-form walk (`wp_goldenCall_inv`: the single register write opens
and re-closes the invariant at 2). -/
theorem goldenInvariant : goldenInvariant_statement := by
  unfold goldenInvariant_statement
  refine goInvariant_mono_pre ?_ (goInvariant_of_wp (P' := .emp) ?_)
  · intro hp hsat
    have hdisj : ∀ k, hp.get? k = (none : Option HeapCell)
        ∨ (∅ : Heaplet).get? k = none := fun k =>
      Or.inr (by
        rw [heaplet_get?_eq]
        exact LawfulPartialMap.get?_empty (M := GoHeapF) (k := k))
    have hcover : ∀ k (c : HeapCell), hp.get? k = some c
        ↔ (hp.get? k = some c ∨ (∅ : Heaplet).get? k = some c) := fun k c =>
      ⟨Or.inl, fun h => h.elim id (fun h0 => by
        rw [heaplet_get?_eq,
          LawfulPartialMap.get?_empty (M := GoHeapF) (k := k)] at h0
        cases h0)⟩
    exact ⟨hp, ∅, ⟨0, hp, ∅, hsat, ⟨Or.inl rfl, rfl⟩, hdisj, hcover⟩,
      rfl, hdisj, hcover⟩
  · intro _inst hprog hmeths _htypes N
    iintro ⟨HinvT, -⟩
    iapply (wp_goldenCall_inv (x := "r") (ta := ⟨0⟩)
      (S := fun cell => ∃ n : Int,
        (n = 0 ∨ n = 2) ∧ cell = ⟨some (.int .int), .int n .int⟩)
      (Icnt := embed (GF := GoCoreS) (.ex fun (n : Int) =>
        .sep (.pointsTo 0 ⟨some (.int .int), .int n .int⟩)
          (.pure (n = 0 ∨ n = 2))))
      rfl hprog hmeths (fun _ _ => CoPset.mem_full)
      (hint := fun cell hS => by
        obtain ⟨n, _, rfl⟩ := hS
        exact ⟨.int n .int, rfl⟩)
      (hopen := by
        simp only [embed]
        iintro ⟨%n, Hpt, %hn⟩
        iexists (⟨some (.int .int), .int n .int⟩ : HeapCell)
        isplitl []
        · ipureintro
          exact ⟨n, hn, rfl⟩
        · iexact Hpt)
      (hclose := by
        rw [show IntKind.normalize .int 2 = 2 from by decide]
        simp only [embed]
        iintro Hpt
        iexists (2 : Int)
        isplitl [Hpt]
        · iexact Hpt
        · ipureintro
          exact Or.inr rfl))
    isplitl [HinvT]
    · iexact HinvT
    iapply (wp_value' (v := ()))
    itrivial

/-- **The golden triple, proven** (the triple half of `goldenSpec`). -/
theorem goldenTriple : goldenTriple_statement := by
  unfold goldenTriple_statement
  have h := goldenSpec
  unfold goldenSpec_statement GoSpec at h
  exact h.1

/-- **THE LOWERING TARGET, restored**: every terminating `execStmt` run
of the seeded driver leaves `int 2` in the designated output cell at base
address 0. Plain first-order statement over the wrapper; address pinned,
no `∃`. -/
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
      sat_pre := by rfl
      wf := by decide }
    fuel ch σf ch' hrun
  obtain ⟨h, _hd, hsub, _hF, hsat⟩ := hres
  rw [show h = (∅ : Heaplet).insert 0 ⟨some (.int .int), .int 2 .int⟩
    from hsat] at hsub
  have hget := hsub 0 ⟨some (.int .int), .int 2 .int⟩ (by
    rw [heaplet_get?_eq, heaplet_insert_eq]
    exact LawfulPartialMap.get?_insert_eq rfl)
  rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hget
  exact loadLoc_base_of_lookup hget

/-- **The negative twin, proven** — still the two-line corollary. -/
theorem goldenNotThree : goldenNotThree_statement := by
  unfold goldenNotThree_statement
  intro fuel ch σf ch' hrun h3
  have h2 := goldenReturnsTwo fuel ch σf ch' hrun
  have := h2.symm.trans h3
  injection this with hval
  injection hval with hn _
  exact absurd hn (by decide)

end GoLean.Surface
