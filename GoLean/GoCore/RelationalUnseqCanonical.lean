import GoLean.GoCore.RelationalUnseq

namespace GoLean.GoCore.Relational.Unseq
open Machine

theorem Domain.occurrence_run {ctx g env} (d : Domain ctx g env)
    {st : List UnseqStatus} (binary : Binary g st) {i : Nat} (ready : i ∈ g.ready st)
    {s : Store} (hs : d.heap.At st s) (body : Stmt) (tail : Continuation) :
    ∃ t, d.heap.At (st.set i .done) t ∧ PickFreeRun ctx
      ⟨.next (.unseqK g body st [] env (.run i) tail.toMachine), s⟩
      (atPick g body (st.set i .done) env tail t) := by
  have hi : i < g.occs.length := (List.mem_filter.mp ready).1 |> List.mem_range.mp
  have hc : i < d.heap.cells.length := by rw [d.count]; exact hi
  have get : g.occs[i]? = some g.occs[i] := List.getElem?_eq_getElem hi
  obtain ⟨t, hw, ht⟩ := hs.write (by rw [binary.1, d.count]) i hc (d.normal i hc)
  have cell : unseqCellLoc env d.heap.cells[i].id = .ok (.base ⟨d.heap.base + i⟩) := by
    simp [unseqCellLoc, d.bindings i hc, pure, Except.pure]
  have write : Mem.store ctx s (.base ⟨d.heap.base + i⟩) (d.heap.value i) =
      .ok (t, [.access .write (.data (.base ⟨d.heap.base + i⟩))]) := by
    simp [Mem.store, hw, Loc.canon, Bind.bind, Except.bind, pure, Except.pure]
  refine ⟨t, ht, ?_⟩
  have start : Transition ctx
      ⟨.next (.unseqK g body st [] env (.run i) tail.toMachine), s⟩ ⟨[], [], []⟩
      ⟨.evalE (d.head i) env (.unseqK g body st [] env (.wait i) tail.toMachine), s⟩ :=
    Step.unseqRunEval get (d.bodies i hi)
  have finish : Transition ctx
      ⟨.retV (d.heap.value i) (.unseqK g body st [] env (.wait i) tail.toMachine), s⟩
      ⟨[.access .write (.data (.base ⟨d.heap.base + i⟩))], [], []⟩
      (atPick g body (st.set i .done) env tail t) :=
    Step.unseqValue get (d.bodies i hi) cell write
  exact (PickFreeRun.single start rfl).trans
    (((d.evaluates st binary i ready _).run s hs).trans (PickFreeRun.single finish rfl))

/-- A canonical occurrence order, together with the real ordered labels.
The occurrence component is an actual pick-free run, never an atomic action.
The least-active criterion respects every graph dependency/order edge. -/
inductive CanonicalExecution {ctx g env} (d : Domain ctx g env) (body : Stmt) (tail : Continuation) :
    List UnseqStatus → Store → List Nat → List StepLabel → State → Prop where
  | done {st s} : Binary g st → d.heap.At st s → g.allSettled st = true →
      CanonicalExecution d body tail st s [] [⟨[], [], []⟩, ⟨[], [], []⟩]
        ⟨.exec body env tail.toMachine, s⟩
  | step {st s i j t order labels rest final} :
      Binary g st → (g.ready st)[j]? = some i →
      (∀ p, p < i → st[p]? = some .done) →
      Run ctx ⟨.next (.unseqK g body st [] env (.run i) tail.toMachine), s⟩ labels
        (atPick g body (st.set i .done) env tail t) →
      (∀ l ∈ labels, l.picks = []) →
      CanonicalExecution d body tail (st.set i .done) t order rest final →
      CanonicalExecution d body tail st s (i :: order)
        (⟨[], PickRecord.ofPick .unseqNext (g.ready st).length j, []⟩ :: labels ++ rest) final

theorem CanonicalExecution.run {ctx g env} {d : Domain ctx g env} {body tail st s order labels final}
    (h : CanonicalExecution d body tail st s order labels final) :
    Run ctx (atPick g body st env tail s) labels final := by
  induction h with
  | @done st s binary _ settled =>
    exact .cons (b := ⟨.next (.storeK [] [] body env tail.toMachine), s⟩)
      (Step.unseqComplete binary.no_skipped_dependencies settled
      (d.ranked.completion_produced binary settled d.stores body)
      (by simp [d.stores, unseqStorePlan, pure, Except.pure]))
      (.cons (b := ⟨.exec body env tail.toMachine, s⟩) Step.storeDone .refl)
  | @step st s i j t order labels rest final binary pick _ occurrence _ _ ih =>
    exact .cons (b := ⟨.next (.unseqK g body st [] env (.run i) tail.toMachine), s⟩)
      (Step.unseqPick binary.no_skipped_dependencies pick) (occurrence.append ih)

theorem CanonicalExecution.completed {ctx g env} {d : Domain ctx g env}
    {body tail st s order labels final}
    (h : CanonicalExecution d body tail st s order labels final) : Completed d body tail final := by
  induction h with
  | done binary heap settled => exact ⟨rfl, _, binary, settled, heap⟩
  | step _ _ _ _ _ _ ih => exact ih

theorem Domain.canonical {ctx g env} (d : Domain ctx g env)
    (body : Stmt) (tail : Continuation) (st : List UnseqStatus)
    (binary : Binary g st) (s : Store) (hs : d.heap.At st s) :
    ∃ order labels final, CanonicalExecution d body tail st s order labels final := by
  generalize measure : st.count .active = n
  induction n using Nat.strongRecOn generalizing st s with
  | ind n ih =>
    cases settled : g.allSettled st with
    | true => exact ⟨[], _, _, .done binary hs settled⟩
    | false =>
      obtain ⟨i, ready, earlier⟩ := d.ranked.progress binary settled
      obtain ⟨j, pick⟩ := List.mem_iff_getElem?.mp ready
      obtain ⟨t, ht, labels, run, picks⟩ := d.occurrence_run binary ready hs body tail
      obtain ⟨order, rest, final, execution⟩ := ih _
        (by rw [← measure]; exact active_count_decreases (UnseqGraph.ready_active pick).2)
        _ (binary.set_done _) t ht rfl
      exact ⟨i :: order, _, final, .step binary pick earlier run picks execution⟩

/-- Canonical realization plus facts at every admitted intermediate prefix.
Completion equality is only one conjunct; progress excludes every failing
tape before the boundary. Ordered labels/accesses are not quotiented away. -/
theorem Domain.sequentialization {ctx g env} (d : Domain ctx g env)
    (body : Stmt) (tail : Continuation) (st : List UnseqStatus)
    (binary : Binary g st) (s : Store) (hs : d.heap.At st s) :
    ∃ order labels final, CanonicalExecution d body tail st s order labels final ∧
      ∀ prefixLabels a,
        SegmentPrefix ctx (Completed d body tail) (atPick g body st env tail s) prefixLabels a →
        d.MemInvariant a ∧
        (Completed d body tail a → a = final) ∧
        (¬ Completed d body tail a → StepAdmission a.control ∧ TotalStep ctx a) := by
  obtain ⟨order, labels, final, canonical⟩ := d.canonical body tail st binary s hs
  refine ⟨order, labels, final, canonical, ?_⟩
  intro prefixLabels a pre
  exact ⟨d.prefix_memory binary hs pre,
    fun done => d.completed_unique done canonical.completed,
    d.prefix_progress binary hs pre⟩

end GoLean.GoCore.Relational.Unseq
