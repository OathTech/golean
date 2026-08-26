import GoLeanProofs.Frame.SpanIso

/-! # Phase-1 fixpoint adequacy (CE1 iff support, part 1)

The bridge between the canonicalizer's phase-1 collection fixpoint
(`collectFix`) and the RELATIONAL span (`RVal`/`DirectRef`/
`ViewedAt`/`MaxView` from `SpanIso.lean`): at a CLEAN stable state,

- **soundness**: every computed view/direct entry is justified by a
  reachable handle (`viewOf a` is itself a reachable window);
- **completeness**: every reachable handle's imprint is present
  (`viewOf a` dominates every reachable window; every whole-
  reference is marked).

Together: the computed `viewOf` IS the relational `MaxView` sup and
the computed `direct` IS `DirectRef` — the checker computes the
relational specification. (This is the theorem the pre-fix
`collectFix` length-only stability test FALSIFIED — the landing
audit's F2a fail-open; the `ViewFixWitness` pair is its regression
witness, and this module is the general form.)

Proof skeleton (recorded in `docs/campaign-ce-log.md` §architecture):
every phase-1 op is id-or-strict-measure-increase (under
flag-freedom), so measure-stability forces the stable pass to be the
LITERAL identity; at a literally-stable state the pass walks
everything at FINAL bounds, so local imprints extract per value
(`ValOk`) and reachability chains close through the visited set. -/

namespace GoLean.Frame.ChoiceErase

open GoLean GoLean.GoCore

/-! ## The semantic order on phase-1 states -/

/-- Phase-1 state order: views widen pointwise, direct marks and
flags persist. Every phase-1 op is `Le`-monotone. -/
structure VSt.Le (s t : VSt) : Prop where
  view : ∀ a, s.viewOf a ≤ t.viewOf a
  direct : ∀ a, a ∈ s.direct → a ∈ t.direct
  flags : ∀ f, f ∈ s.flags → f ∈ t.flags

theorem VSt.Le.rfl (s : VSt) : s.Le s :=
  ⟨fun _ => Nat.le_refl _, fun _ h => h, fun _ h => h⟩

theorem VSt.Le.trans {s t u : VSt} (h₁ : s.Le t) (h₂ : t.Le u) : s.Le u :=
  ⟨fun a => Nat.le_trans (h₁.view a) (h₂.view a),
   fun a h => h₂.direct a (h₁.direct a h),
   fun f h => h₂.flags f (h₁.flags f h)⟩

/-- Structural well-formedness of a phase-1 state: no duplicate view
keys, positive view widths, no duplicate direct marks. Holds of the
empty start state and is preserved by every op — it is what makes
the measure a faithful size. -/
structure VSt.Wf (s : VSt) : Prop where
  nodup : s.views.Pairwise (fun p q => p.1 ≠ q.1)
  pos : ∀ p, p ∈ s.views → 1 ≤ p.2
  dnodup : s.direct.Nodup

theorem VSt.Wf.empty : VSt.Wf { views := [], direct := [], flags := [] } :=
  ⟨List.Pairwise.nil, fun _ h => absurd h (List.not_mem_nil), List.nodup_nil⟩

/-! ## Op-level lemmas -/

theorem viewOf_eq_lookup (s : VSt) (a : Nat) :
    s.viewOf a = (s.views.lookup a).getD 0 := by
  unfold VSt.viewOf
  cases s.views.lookup a <;> rfl

private theorem lookup_filter_ne (l : List (Nat × Nat)) (a b : Nat) (hne : b ≠ a) :
    (l.filter (fun p => p.1 ≠ a)).lookup b = l.lookup b := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
      by_cases hpa : p.1 = a
      · have h1 : (decide (p.1 ≠ a)) = false := by simp [hpa]
        have h2 : (b == p.1) = false := by
          have : b ≠ p.1 := by omega
          simp [this]
        simp only [List.filter_cons, h1, Bool.false_eq_true, if_false, ih,
          List.lookup, h2]
      · have hd : (decide (p.1 ≠ a)) = true := by simp [hpa]
        simp only [List.filter_cons, hd, if_true, List.lookup]
        by_cases hbp : b = p.1
        · have : (b == p.1) = true := by simp [hbp]
          simp [this]
        · have hbeq : (b == p.1) = false := by simp [hbp]
          rw [hbeq]
          exact ih

/-- The pointwise effect of `bumpView`. -/
theorem viewOf_bumpView (s : VSt) (a v b : Nat) :
    (s.bumpView a v).viewOf b =
      if b = a then max (s.viewOf a) v else s.viewOf b := by
  unfold VSt.bumpView
  by_cases hle : v ≤ s.viewOf a
  · simp only [hle, if_pos]
    by_cases hba : b = a
    · subst hba; simp [Nat.max_eq_left hle]
    · simp [hba]
  · simp only [hle, if_neg, if_false]
    by_cases hba : b = a
    · subst hba
      simp only [if_pos rfl]
      rw [viewOf_eq_lookup]
      simp only [List.lookup]
      have : (b == b) = true := by simp
      simp [this]
      omega
    · simp only [if_neg hba]
      have hba' : (b == a) = false := by simp [hba]
      rw [viewOf_eq_lookup, viewOf_eq_lookup]
      simp only [List.lookup, hba']
      rw [lookup_filter_ne _ _ _ hba]

theorem bumpView_direct (s : VSt) (a v : Nat) :
    (s.bumpView a v).direct = s.direct := by
  unfold VSt.bumpView; split <;> rfl

theorem bumpView_flags (s : VSt) (a v : Nat) :
    (s.bumpView a v).flags = s.flags := by
  unfold VSt.bumpView; split <;> rfl

theorem markDirect_views (s : VSt) (a : Nat) :
    (s.markDirect a).views = s.views := by
  unfold VSt.markDirect; split <;> rfl

theorem markDirect_flags (s : VSt) (a : Nat) :
    (s.markDirect a).flags = s.flags := by
  unfold VSt.markDirect; split <;> rfl

theorem mem_markDirect (s : VSt) (a b : Nat) :
    b ∈ (s.markDirect a).direct ↔ (b = a ∨ b ∈ s.direct) := by
  unfold VSt.markDirect
  by_cases h : s.direct.contains a
  · simp only [h, if_pos]
    constructor
    · exact Or.inr
    · rintro (rfl | hb)
      · exact List.contains_iff_mem.mp h
      · exact hb
  · simp only [h, if_neg, if_false]
    simp [List.mem_cons]

theorem flag_views (s : VSt) (f : String) :
    (s.flag f).views = s.views := by
  unfold VSt.flag; split <;> rfl

theorem flag_direct (s : VSt) (f : String) :
    (s.flag f).direct = s.direct := by
  unfold VSt.flag; split <;> rfl

theorem mem_flag (s : VSt) (f g : String) :
    g ∈ (s.flag f).flags ↔ (g = f ∨ g ∈ s.flags) := by
  unfold VSt.flag
  by_cases h : s.flags.contains f
  · simp only [h, if_pos]
    constructor
    · exact Or.inr
    · rintro (rfl | hg)
      · exact List.contains_iff_mem.mp h
      · exact hg
  · simp only [h, if_neg, if_false]
    simp [List.mem_cons]

theorem viewOf_flag (s : VSt) (f : String) (a : Nat) :
    (s.flag f).viewOf a = s.viewOf a := by
  rw [viewOf_eq_lookup, viewOf_eq_lookup, flag_views]

theorem viewOf_markDirect (s : VSt) (a b : Nat) :
    (s.markDirect a).viewOf b = s.viewOf b := by
  rw [viewOf_eq_lookup, viewOf_eq_lookup, markDirect_views]

/-- `bumpView` is monotone. -/
theorem bumpView_le (s : VSt) (a v : Nat) : s.Le (s.bumpView a v) := by
  refine ⟨fun b => ?_, fun b h => ?_, fun f h => ?_⟩
  · rw [viewOf_bumpView]
    split
    · next hba => subst hba; exact Nat.le_max_left _ _
    · exact Nat.le_refl _
  · rw [bumpView_direct]; exact h
  · rw [bumpView_flags]; exact h

theorem markDirect_le (s : VSt) (a : Nat) : s.Le (s.markDirect a) := by
  refine ⟨fun b => ?_, fun b h => ?_, fun f h => ?_⟩
  · rw [viewOf_markDirect]; exact Nat.le_refl _
  · exact (mem_markDirect s a b).mpr (Or.inr h)
  · rw [markDirect_flags]; exact h

theorem flag_le (s : VSt) (f : String) : s.Le (s.flag f) := by
  refine ⟨fun b => ?_, fun b h => ?_, fun g h => ?_⟩
  · rw [viewOf_flag]; exact Nat.le_refl _
  · rw [flag_direct]; exact h
  · exact (mem_flag s f g).mpr (Or.inr h)

/-- A flag op that leaves the flag set empty was a no-op with the
flag already... impossible — empty output means the op never fired
AND the input was empty; on an empty input the op always fires. So:
an empty flag set after `flag f` is absurd. -/
theorem flag_ne_empty (s : VSt) (f : String) : (s.flag f).flags ≠ [] := by
  intro h
  have : f ∈ (s.flag f).flags := (mem_flag s f f).mpr (Or.inl rfl)
  rw [h] at this
  exact absurd this (List.not_mem_nil)

/-! ## The measure: op-level strictness

`VSt.measure` = #view-keys + Σ view-widths + #direct-marks. Under
`Wf`, every op either leaves the state LITERALLY unchanged or
strictly increases the measure (flag ops touch neither but cannot
fire under final flag-freedom) — the rigidity that turns
measure-stability into literal stability. -/

private theorem foldl_add_shift (l : List (Nat × Nat)) (n : Nat) :
    l.foldl (fun s p => s + p.2) n = n + l.foldl (fun s p => s + p.2) 0 := by
  induction l generalizing n with
  | nil => simp
  | cons p rest ih => simp only [List.foldl]; rw [ih, ih (0 + p.2)]; omega

/-- Width sum of a view list. -/
private def vsum (l : List (Nat × Nat)) : Nat := l.foldl (fun s p => s + p.2) 0

private theorem vsum_cons (p : Nat × Nat) (l : List (Nat × Nat)) :
    vsum (p :: l) = p.2 + vsum l := by
  unfold vsum
  simp only [List.foldl]
  rw [foldl_add_shift]
  omega

theorem measure_eq (s : VSt) :
    s.measure = s.views.length + vsum s.views + s.direct.length := rfl

/-- A `none` lookup means the key is absent. -/
private theorem lookup_none_keys (l : List (Nat × Nat)) (a : Nat)
    (h : l.lookup a = none) : ∀ q ∈ l, q.1 ≠ a := by
  induction l with
  | nil => intro q hq; exact absurd hq (List.not_mem_nil)
  | cons p rest ih =>
      intro q hq
      by_cases hpa : a = p.1
      · have hbeq : (a == p.1) = true := by simp [hpa]
        simp [List.lookup, hbeq] at h
      · have hbeq : (a == p.1) = false := by simp [hpa]
        simp only [List.lookup, hbeq] at h
        rcases List.mem_cons.mp hq with rfl | hq
        · omega
        · exact ih h q hq

/-- On a nodup-keyed list containing key `a` with width `w`, the
`≠ a` filter removes exactly that entry. -/
private theorem filter_ne_of_lookup (l : List (Nat × Nat)) (a w : Nat)
    (hnd : l.Pairwise (fun p q => p.1 ≠ q.1))
    (hl : l.lookup a = some w) :
    (l.filter (fun p => p.1 ≠ a)).length + 1 = l.length ∧
    vsum (l.filter (fun p => p.1 ≠ a)) + w = vsum l := by
  induction l with
  | nil => simp [List.lookup] at hl
  | cons p rest ih =>
      rcases List.pairwise_cons.mp hnd with ⟨hp, hrest⟩
      by_cases hpa : p.1 = a
      · have hbeq : (a == p.1) = true := by simp [hpa]
        simp only [List.lookup, hbeq] at hl
        have hw : p.2 = w := by cases hl; rfl
        have hfilter : rest.filter (fun p => p.1 ≠ a) = rest := by
          apply List.filter_eq_self.mpr
          intro q hq
          have hne := hp q hq
          simp
          omega
        have h1 : (decide (p.1 ≠ a)) = false := by simp [hpa]
        rw [List.filter_cons, h1]
        simp only [Bool.false_eq_true, if_false, hfilter, vsum_cons]
        exact ⟨by simp, by omega⟩
      · have hbeq : (a == p.1) = false := by
          simp
          omega
        simp only [List.lookup, hbeq] at hl
        have hd : (decide (p.1 ≠ a)) = true := by simp [hpa]
        obtain ⟨ih1, ih2⟩ := ih hrest hl
        rw [List.filter_cons, hd]
        simp only [if_true, List.length_cons, vsum_cons]
        omega

/-- `bumpView` under `Wf`: literal identity or strict measure
increase with `Wf` preserved. -/
theorem bumpView_rigid (s : VSt) (a v : Nat) (hwf : s.Wf) :
    (s.bumpView a v = s) ∨
      (VSt.Wf (s.bumpView a v) ∧ s.measure < (s.bumpView a v).measure) := by
  by_cases hle : v ≤ s.viewOf a
  · left
    unfold VSt.bumpView
    rw [if_pos hle]
  · right
    have hfired : s.bumpView a v
        = { s with views := (a, v) :: s.views.filter (fun p => p.1 ≠ a) } := by
      unfold VSt.bumpView
      rw [if_neg hle]
    have hv1 : 1 ≤ v := by omega
    have hfilterwf : (s.views.filter (fun p => p.1 ≠ a)).Pairwise
        (fun p q => p.1 ≠ q.1) := List.Pairwise.filter _ hwf.nodup
    rw [hfired]
    constructor
    · refine ⟨?_, ?_, hwf.dnodup⟩
      · refine List.pairwise_cons.mpr ⟨?_, hfilterwf⟩
        intro q hq
        have hqp := (List.mem_filter.mp hq).2
        simp at hqp
        simp
        omega
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hv1
        · exact hwf.pos p (List.mem_filter.mp hp).1
    · rw [measure_eq, measure_eq]
      simp only [List.length_cons, vsum_cons]
      rw [viewOf_eq_lookup] at hle
      cases hlk : s.views.lookup a with
      | none =>
          have hself : s.views.filter (fun p => p.1 ≠ a) = s.views := by
            apply List.filter_eq_self.mpr
            intro q hq
            have := lookup_none_keys s.views a hlk q hq
            simp
            omega
          rw [hself]
          rw [hlk] at hle
          simp at hle
          omega
      | some w =>
          obtain ⟨h1, h2⟩ := filter_ne_of_lookup s.views a w hwf.nodup hlk
          rw [hlk] at hle
          simp at hle
          omega

/-- `markDirect` under `Wf`: literal identity or strict increase. -/
theorem markDirect_rigid (s : VSt) (a : Nat) (hwf : s.Wf) :
    (s.markDirect a = s) ∨
      (VSt.Wf (s.markDirect a) ∧ s.measure < (s.markDirect a).measure) := by
  by_cases hc : s.direct.contains a
  · left
    unfold VSt.markDirect
    rw [if_pos hc]
  · right
    have hfired : s.markDirect a = { s with direct := a :: s.direct } := by
      unfold VSt.markDirect
      rw [if_neg hc]
    rw [hfired]
    refine ⟨⟨hwf.nodup, hwf.pos, ?_⟩, ?_⟩
    · exact List.nodup_cons.mpr
        ⟨fun h => hc (List.contains_iff_mem.mpr h), hwf.dnodup⟩
    · rw [measure_eq, measure_eq]
      simp only [List.length_cons]
      omega

/-- `flag` never changes the measure, and cannot fire under final
flag-freedom (`flag_ne_empty`); it preserves `Wf`. -/
theorem flag_rigid (s : VSt) (f : String) (hwf : s.Wf) :
    VSt.Wf (s.flag f) ∧ s.measure = (s.flag f).measure := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [flag_views]; exact hwf.nodup
  · rw [flag_views]; exact hwf.pos
  · rw [flag_direct]; exact hwf.dnodup
  · rw [measure_eq, measure_eq, flag_views, flag_direct]

/-! ## The composite step relation

Everything the mono/rigidity induction needs, packaged so it
composes transitively through folds: state order + visited growth +
(under `Wf`) `Wf` preservation, measure monotonicity, and RIGIDITY —
flag-free measure-stationary steps are literal identities on the
`VSt` component. -/

def PhaseStep (s t : VSt × List Nat) : Prop :=
  s.1.Le t.1 ∧ (∀ x, x ∈ s.2 → x ∈ t.2) ∧
  (VSt.Wf s.1 → VSt.Wf t.1 ∧ s.1.measure ≤ t.1.measure ∧
    (t.1.flags = [] → s.1.measure = t.1.measure → t.1 = s.1))

theorem PhaseStep.refl (s : VSt × List Nat) : PhaseStep s s :=
  ⟨VSt.Le.rfl _, fun _ h => h, fun hwf => ⟨hwf, Nat.le_refl _, fun _ _ => rfl⟩⟩

theorem PhaseStep.trans {s t u : VSt × List Nat}
    (h₁ : PhaseStep s t) (h₂ : PhaseStep t u) : PhaseStep s u := by
  obtain ⟨le₁, vis₁, w₁⟩ := h₁
  obtain ⟨le₂, vis₂, w₂⟩ := h₂
  refine ⟨le₁.trans le₂, fun x hx => vis₂ x (vis₁ x hx), fun hwf => ?_⟩
  obtain ⟨hwt, hm₁, hr₁⟩ := w₁ hwf
  obtain ⟨hwu, hm₂, hr₂⟩ := w₂ hwt
  refine ⟨hwu, Nat.le_trans hm₁ hm₂, fun hfl hms => ?_⟩
  have hmt : s.1.measure = t.1.measure := by omega
  have htfl : t.1.flags = [] := by
    rcases ht : t.1.flags with _ | ⟨f, rest⟩
    · rfl
    · have : f ∈ u.1.flags := le₂.flags f (by rw [ht]; exact List.mem_cons_self)
      rw [hfl] at this
      exact absurd this (List.not_mem_nil)
  have h1 := hr₁ htfl hmt
  have h2 := hr₂ hfl (by omega)
  rw [h2, h1]

/-- Lift a `VSt`-only op into a `PhaseStep` (visited unchanged). -/
theorem PhaseStep.ofOp {st st' : VSt} {vis : List Nat}
    (hle : st.Le st')
    (hrigid : st.Wf → (st' = st) ∨ (st'.Wf ∧ st.measure < st'.measure)) :
    PhaseStep (st, vis) (st', vis) := by
  refine ⟨hle, fun x hx => hx, fun hwf => ?_⟩
  rcases hrigid hwf with rfl | ⟨hw, hm⟩
  · exact ⟨hwf, Nat.le_refl _, fun _ _ => rfl⟩
  · refine ⟨hw, Nat.le_of_lt hm, fun _ hms => ?_⟩
    exfalso
    have hms' : st.measure = st'.measure := hms
    omega

theorem PhaseStep.bumpView (st : VSt) (vis : List Nat) (a v : Nat) :
    PhaseStep (st, vis) (st.bumpView a v, vis) :=
  .ofOp (bumpView_le st a v) (bumpView_rigid st a v)

theorem PhaseStep.markDirect (st : VSt) (vis : List Nat) (a : Nat) :
    PhaseStep (st, vis) (st.markDirect a, vis) :=
  .ofOp (markDirect_le st a) (markDirect_rigid st a)

theorem PhaseStep.flag (st : VSt) (vis : List Nat) (f : String) :
    PhaseStep (st, vis) (st.flag f, vis) := by
  refine ⟨flag_le st f, fun x hx => hx, fun hwf => ?_⟩
  obtain ⟨hw, hm⟩ := flag_rigid st f hwf
  refine ⟨hw, Nat.le_of_eq hm, fun hfl _ => ?_⟩
  exact absurd hfl (flag_ne_empty st f)

theorem PhaseStep.visit (st : VSt) (vis : List Nat) (a : Nat) :
    PhaseStep (st, vis) (st, a :: vis) :=
  ⟨VSt.Le.rfl _, fun x hx => List.mem_cons_of_mem a hx,
   fun hwf => ⟨hwf, Nat.le_refl _, fun _ _ => rfl⟩⟩

/-- Generic fold composition. -/
theorem PhaseStep.foldl {γ} (g : (VSt × List Nat) → γ → (VSt × List Nat))
    (hg : ∀ acc x, PhaseStep acc (g acc x)) :
    ∀ (l : List γ) acc, PhaseStep acc (l.foldl g acc) := by
  intro l
  induction l with
  | nil => intro acc; exact PhaseStep.refl acc
  | cons x rest ih =>
      intro acc
      exact (hg acc x).trans (ih (g acc x))

theorem PhaseStep.foldlArray {γ} (g : (VSt × List Nat) → γ → (VSt × List Nat))
    (hg : ∀ acc x, PhaseStep acc (g acc x)) :
    ∀ (l : Array γ) acc, PhaseStep acc (l.foldl g acc) := by
  intro l acc
  rw [← Array.foldl_toList]
  exact PhaseStep.foldl g hg l.toList acc

/-! ## The traversal is a `PhaseStep` (mono + rigidity, phase 1) -/

mutual

theorem collectV_step (h : Heap) (m : Mask) :
    ∀ (fuel : Nat) (acc : VSt × List Nat) (v : GoValue),
      PhaseStep acc (collectV h m fuel acc v)
  | 0, acc, v => by
      simp only [collectV]
      exact PhaseStep.flag acc.1 acc.2 "FUEL"
  | fuel + 1, acc, .unit => by
      simp only [collectV]; exact PhaseStep.refl acc
  | fuel + 1, acc, .bool _ => by
      simp only [collectV]; exact PhaseStep.refl acc
  | fuel + 1, acc, .int _ _ => by
      simp only [collectV]; exact PhaseStep.refl acc
  | fuel + 1, acc, .float _ _ => by
      simp only [collectV]; exact PhaseStep.refl acc
  | fuel + 1, acc, .string _ => by
      simp only [collectV]; exact PhaseStep.refl acc
  | fuel + 1, acc, .nil => by
      simp only [collectV]; exact PhaseStep.refl acc
  | fuel + 1, acc, .syncData _ => by
      simp only [collectV]; exact PhaseStep.refl acc
  | fuel + 1, acc, .addr l => by
      simp only [collectV]
      cases hb : baseAddr l with
      | some a =>
          exact (PhaseStep.markDirect acc.1 acc.2 a).trans
            (collectCell_step h m fuel _ a)
      | none => exact PhaseStep.flag acc.1 acc.2 "NONBASE-LOC"
  | fuel + 1, acc, .slice sv => by
      simp only [collectV]
      split
      · split
        · exact (PhaseStep.bumpView acc.1 acc.2 _ _).trans
            (collectCell_step h m fuel _ _)
        · exact PhaseStep.flag acc.1 acc.2 "NONBASE-LOC"
      · exact PhaseStep.refl acc
  | fuel + 1, acc, .map mv => by
      simp only [collectV]
      split
      · split
        · exact (PhaseStep.markDirect acc.1 acc.2 _).trans
            (collectCell_step h m fuel _ _)
        · exact PhaseStep.flag acc.1 acc.2 "NONBASE-LOC"
      · exact PhaseStep.refl acc
  | fuel + 1, acc, .chan cv => by
      simp only [collectV]
      split
      · split
        · exact (PhaseStep.markDirect acc.1 acc.2 _).trans
            (collectCell_step h m fuel _ _)
        · exact PhaseStep.flag acc.1 acc.2 "NONBASE-LOC"
      · exact PhaseStep.refl acc
  | fuel + 1, acc, .interface _ x => by
      simp only [collectV]
      exact collectV_step h m fuel acc x
  | fuel + 1, acc, .struct tid fs => by
      simp only [collectV]
      exact PhaseStep.foldlArray _
        (fun acc p => by
          by_cases hm : m.hits tid p.1
          · simp only [hm, if_pos]
            exact PhaseStep.refl acc
          · simp only [hm, Bool.false_eq_true, if_false]
            exact collectV_step h m fuel acc p.2) fs acc
  | fuel + 1, acc, .array vs => by
      simp only [collectV]
      exact PhaseStep.foldlArray _
        (fun acc x => collectV_step h m fuel acc x) vs acc
  | fuel + 1, acc, .funcVal _ cap => by
      simp only [collectV]
      exact PhaseStep.foldl _
        (fun acc x => collectV_step h m fuel acc x) cap acc
  | fuel + 1, acc, .mapData es => by
      simp only [collectV]
      exact PhaseStep.foldlArray _
        (fun acc p => (collectV_step h m fuel acc p.1).trans
          (collectV_step h m fuel _ p.2)) es acc
  | fuel + 1, acc, .chanData buf _ _ => by
      simp only [collectV]
      exact PhaseStep.foldlArray _
        (fun acc x => collectV_step h m fuel acc x) buf acc

theorem collectCell_step (h : Heap) (m : Mask) :
    ∀ (fuel : Nat) (acc : VSt × List Nat) (a : Nat),
      PhaseStep acc (collectCell h m fuel acc a)
  | 0, acc, a => by
      simp only [collectCell]
      exact PhaseStep.flag acc.1 acc.2 "FUEL"
  | fuel + 1, acc, a => by
      simp only [collectCell]
      by_cases hc : acc.2.contains a
      · rw [if_pos hc]
        exact PhaseStep.refl acc
      · rw [if_neg hc]
        refine (PhaseStep.visit acc.1 acc.2 a).trans ?_
        split
        · exact PhaseStep.refl _
        · split
          · exact PhaseStep.foldl _
              (fun acc x => collectV_step h m fuel acc x) _ _
          · exact collectV_step h m fuel _ _

end

/-- One collection pass is a `PhaseStep` on the `VSt`. -/
theorem collectPass_step (h : Heap) (m : Mask) (fuel : Nat) (st : VSt)
    (roots : List GoValue) :
    PhaseStep (st, ([] : List Nat))
      (roots.foldl (fun acc v => collectV h m fuel acc v)
        ((st, []) : VSt × List Nat)) :=
  PhaseStep.foldl _ (fun acc v => collectV_step h m fuel acc v) roots (st, [])
