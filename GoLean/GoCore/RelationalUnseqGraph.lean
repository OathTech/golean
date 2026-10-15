import GoLean.GoCore.Unseq
import Init.Data.List.Nat.Count

/-! A topological order is an explicit progress premise, separate from the
machine's name/sort checks. Graphs may have arbitrary sharing and dependencies;
guards/skipping are outside this first domain. No schedules are enumerated. -/
namespace GoLean.GoCore.Relational.Unseq

structure Ranked (g : UnseqGraph) : Prop where
  regions : ∀ o ∈ g.occs, o.region = none
  dependencies : ∀ i o, g.occs[i]? = some o → ∀ d ∈ g.deps o,
    ∃ p, g.producer? d = some p ∧ p < i
  orders : ∀ i o, g.occs[i]? = some o → ∀ name ∈ o.after,
    ∃ p, g.index? name = some p ∧ p < i
  consumers : ∀ d ∈ g.cellNames, ∃ p, g.producer? d = some p ∧ p < g.occs.length

def Binary (g : UnseqGraph) (st : List UnseqStatus) : Prop :=
  st.length = g.occs.length ∧
    ∀ i, i < g.occs.length → st[i]? = some .active ∨ st[i]? = some .done

theorem binary_initial (g : UnseqGraph) : Binary g g.initStatus := by
  refine ⟨by simp [UnseqGraph.initStatus], ?_⟩
  intro i hi
  left
  simp [UnseqGraph.initStatus, hi]

theorem Binary.set_done {g : UnseqGraph} {st : List UnseqStatus}
    (h : Binary g st) (i : Nat) : Binary g (st.set i .done) := by
  refine ⟨by simp [h.1], ?_⟩
  intro j hj
  by_cases e : i = j
  · subst i; right; exact List.getElem?_set_self (by rw [h.1]; exact hj)
  · simpa [List.getElem?_set_ne e] using h.2 j hj

theorem Binary.not_skipped {g : UnseqGraph} {st : List UnseqStatus}
    (h : Binary g st) (i : Nat) : st[i]? ≠ some .skipped := by
  by_cases hi : i < g.occs.length
  · rcases h.2 i hi with ha | hd
    · simp [ha]
    · simp [hd]
  · rw [List.getElem?_eq_none (by rw [h.1]; omega)]; simp

theorem Binary.no_skipped_dependencies {g : UnseqGraph} {st : List UnseqStatus}
    (h : Binary g st) : g.skippedDep? st = none := by
  unfold UnseqGraph.skippedDep?
  apply List.findSome?_eq_none_iff.mpr
  intro i _
  split
  · split
    · apply List.findSome?_eq_none_iff.mpr
      intro d _
      split
      · rename_i p hp
        simp [h.not_skipped p]
      · rfl
    · rfl
  · rfl

theorem Binary.settled_done {g : UnseqGraph} {st : List UnseqStatus}
    (h : Binary g st) (settled : g.allSettled st = true)
    (i : Nat) (hi : i < g.occs.length) : st[i]? = some .done := by
  rcases h.2 i hi with ha | hd
  · have bad := List.all_eq_true.mp settled i (List.mem_range.mpr hi)
    simp [ha] at bad
  · exact hd

theorem Ranked.ready_of_earlier_done {g : UnseqGraph} (gok : Ranked g)
    {st : List UnseqStatus} {i : Nat} (hi : i < g.occs.length)
    (active : st[i]? = some .active)
    (earlier : ∀ p, p < i → st[p]? = some .done) : i ∈ g.ready st := by
  have get : g.occs[i]? = some g.occs[i] := List.getElem?_eq_getElem hi
  simp only [UnseqGraph.ready, List.mem_filter, List.mem_range]
  refine ⟨hi, ?_⟩
  simp only [UnseqGraph.readyAt, get, active, beq_self_eq_true, Bool.true_and,
    UnseqGraph.regionOk, gok.regions _ (List.getElem_mem hi), Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · apply List.all_eq_true.mpr
    intro name hn
    obtain ⟨p, hp, lt⟩ := gok.orders i _ get name hn
    simp [UnseqGraph.discharged, UnseqGraph.statusOf, hp, earlier p lt]
  · apply List.all_eq_true.mpr
    intro d hd
    obtain ⟨p, hp, lt⟩ := gok.dependencies i _ get d hd
    simp [UnseqGraph.produced, hp, earlier p lt]

/-- The least active occurrence is ready. This is the realizable canonical
choice and proves progress for every binary status, not a table of schedules. -/
theorem Ranked.progress {g : UnseqGraph} (gok : Ranked g)
    {st : List UnseqStatus} (binary : Binary g st)
    (pending : g.allSettled st = false) :
    ∃ i, i ∈ g.ready st ∧ ∀ p, p < i → st[p]? = some .done := by
  classical
  have active : ∃ i, i < g.occs.length ∧ st[i]? = some .active := by
    apply Classical.byContradiction
    intro no
    have all : g.allSettled st = true := by
      apply List.all_eq_true.mpr
      intro i hi
      have ne : st[i]? ≠ some .active := fun ha => no ⟨i, List.mem_range.mp hi, ha⟩
      simpa using ne
    simp [pending] at all
  obtain ⟨n, hn⟩ := active
  have least : ∃ i, (i < g.occs.length ∧ st[i]? = some .active) ∧
      ∀ p, p < i → st[p]? ≠ some .active := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases lower : ∃ p, p < n ∧ st[p]? = some .active
      · obtain ⟨p, hp, ha⟩ := lower
        exact ih p hp ⟨by omega, ha⟩
      · exact ⟨n, hn, fun p hp ha => lower ⟨p, hp, ha⟩⟩
  obtain ⟨i, hi, minimal⟩ := least
  have earlier : ∀ p, p < i → st[p]? = some .done := by
    intro p hp
    rcases binary.2 p (by omega) with ha | hd
    · exact False.elim (minimal p hp ha)
    · exact hd
  exact ⟨i, gok.ready_of_earlier_done hi.1 hi.2 earlier, earlier⟩

theorem Ranked.completion_produced {g : UnseqGraph} (gok : Ranked g)
    {st : List UnseqStatus} (binary : Binary g st)
    (settled : g.allSettled st = true) (empty : g.stores = []) (body : Stmt) :
    g.unproducedConsumer? st body = none := by
  have produced : ∀ d, g.isCell d = true → g.produced st d = true := by
    intro d hd
    obtain ⟨p, hp, hi⟩ := gok.consumers d (by simpa [UnseqGraph.isCell] using hd)
    simp [UnseqGraph.produced, hp, binary.settled_done settled p hi]
  simp only [UnseqGraph.unproducedConsumer?, empty, List.findSome?_nil]
  apply List.findSome?_eq_none_iff.mpr
  intro d hd
  simp [produced d (List.mem_filter.mp hd).2]

theorem active_count_decreases {st : List UnseqStatus} {i : Nat}
    (active : st[i]? = some .active) :
    (st.set i .done).count .active < st.count .active := by
  obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp active
  have positive : 0 < st.count .active := List.count_pos_iff.mpr (List.mem_of_getElem? active)
  rw [List.count_set hi]
  simp only [hv]
  simp
  omega

theorem ready_produced {g : UnseqGraph} {st : List UnseqStatus} {i : Nat} {o : UnseqOcc}
    (get : g.occs[i]? = some o) (ready : i ∈ g.ready st) {d : VarId}
    (dependency : d ∈ g.deps o) : g.produced st d = true := by
  have hr := (List.mem_filter.mp ready).2
  simp only [UnseqGraph.readyAt, get, Bool.and_eq_true] at hr
  exact List.all_eq_true.mp hr.2 d dependency

end GoLean.GoCore.Relational.Unseq
