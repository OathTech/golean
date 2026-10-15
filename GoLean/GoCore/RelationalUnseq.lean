import GoLean.GoCore.RelationalSegment
import GoLean.GoCore.RelationalExpression
import GoLean.GoCore.RelationalUnseqHeap
import GoLean.GoCore.RelationalUnseqTraversal

namespace GoLean.GoCore.Relational.Unseq
open Machine

/-- Operational expression contracts over every relevant intermediate heap.
These are local source evaluation laws, not assumed diamonds or WP judgments.
The source instances below discharge them using reads and arithmetic. -/
structure Domain (ctx : ProgramCtx) (g : UnseqGraph) (env : LocalEnv) where
  heap : HeapDomain
  cells : heap.cells = g.cells
  count : heap.cells.length = g.occs.length
  ranked : Ranked g
  stores : g.stores = []
  head : Nat → Expr
  bodies : ∀ i (hi : i < g.occs.length),
    g.occs[i].body = .eval heap.cells[i].id (head i)
  bindings : ∀ i (hi : i < heap.cells.length),
    env.lookup heap.cells[i].id = some (.base ⟨heap.base + i⟩)
  normal : ∀ i (hi : i < heap.cells.length),
    normalizeValueForTy ctx heap.cells[i].typ (heap.value i) = .ok (heap.value i)
  evaluates : ∀ st, Binary g st → ∀ i, i ∈ g.ready st →
    ReadOnlyExpr ctx (heap.At st) env (head i) (heap.value i)

def atPick (g : UnseqGraph) (body : Stmt) (st : List UnseqStatus)
    (env : LocalEnv) (tail : Continuation) (s : Store) : State :=
  ⟨.next (.unseqK g body st [] env .pick tail.toMachine), s⟩

def Domain.MemInvariant {ctx g env} (d : Domain ctx g env) (a : State) : Prop :=
  ∃ st, Binary g st ∧ d.heap.At st a.store

def Domain.FrameStep {ctx g env} (d : Domain ctx g env)
    (a : State) (_ : StepLabel) (b : State) : Prop :=
  d.MemInvariant a ∧ d.MemInvariant b

def Completed {ctx g env} (d : Domain ctx g env) (body : Stmt) (tail : Continuation)
    (a : State) : Prop :=
  a.control = .exec body env tail.toMachine ∧ ∃ st, Binary g st ∧
    g.allSettled st = true ∧ d.heap.At st a.store

theorem scheduler_total {ctx g st env body tail s}
    (binary : Binary g st) (pending : g.allSettled st = false)
    (ready : g.ready st ≠ []) : TotalStep ctx (atPick g body st env tail s) := by
  intro ch
  have bound : 0 < (g.ready st).length := List.length_pos_iff.mpr ready
  let j := (Choices.consumeAt .unseqNext (g.ready st).length ch).1
  have hj : j < (g.ready st).length := Choices.consumeAt_fst_lt bound
  refine ⟨⟨.next (.unseqK g body st [] env (.run (g.ready st)[j]) tail.toMachine), s⟩,
    (Choices.consumeAt .unseqNext (g.ready st).length ch).2,
    ⟨[], PickRecord.ofPick .unseqNext (g.ready st).length j, []⟩, ?_⟩
  change stepUnseqNext ctx s g body st [] env .pick tail.toMachine ch = _
  simp [stepUnseqNext, binary.no_skipped_dependencies, pending,
    Choices.consumeAtE_eq, List.getElem?_eq_getElem hj, j]

/-- A selected occurrence is a real dispatch, a finite expression path and
the actual checked binder write. Every step remains visible to guarded clients. -/
theorem Domain.occurrence {ctx g env} (d : Domain ctx g env)
    {st : List UnseqStatus} (binary : Binary g st) {i : Nat} (ready : i ∈ g.ready st)
    (path : ReadOnlyExpr ctx (d.heap.At st) env (d.head i) (d.heap.value i))
    {s : Store} (hs : d.heap.At st s) (body : Stmt) (tail : Continuation)
    {post : State → Prop}
    (next : ∀ t, d.heap.At (st.set i .done) t →
      SafeUntil ctx d.FrameStep post (atPick g body (st.set i .done) env tail t)) :
    SafeUntil ctx d.FrameStep post
      ⟨.next (.unseqK g body st [] env (.run i) tail.toMachine), s⟩ := by
  have hi : i < g.occs.length := (List.mem_filter.mp ready).1 |> List.mem_range.mp
  have hc : i < d.heap.cells.length := by rw [d.count]; exact hi
  have get : g.occs[i]? = some g.occs[i] := List.getElem?_eq_getElem hi
  obtain ⟨t, hw, ht⟩ := hs.write (by rw [binary.1, d.count]) i hc (d.normal i hc)
  have cell : unseqCellLoc env d.heap.cells[i].id = .ok (.base ⟨d.heap.base + i⟩) := by
    simp [unseqCellLoc, d.bindings i hc, pure, Except.pure]
  have write : Mem.store ctx s (.base ⟨d.heap.base + i⟩) (d.heap.value i) =
      .ok (t, [.access .write (.data (.base ⟨d.heap.base + i⟩))]) := by
    simp [Mem.store, hw, Loc.canon, Bind.bind, Except.bind, pure, Except.pure]
  refine SafeUntil.deterministic_step
    (l := ⟨[], [], []⟩)
    (b := ⟨.evalE (d.head i) env (.unseqK g body st [] env (.wait i) tail.toMachine), s⟩)
    ⟨(by intro h; cases h), rfl⟩ ?_ rfl ⟨⟨st, binary, hs⟩, ⟨st, binary, hs⟩⟩ ?_
  · exact Step.unseqRunEval get (d.bodies i hi)
  apply (path ⟨.unseqK g body st [] env (.wait i) tail.toMachine⟩).safeUntil_with s hs
    (fun _ _ _ _ => ⟨⟨st, binary, hs⟩, ⟨st, binary, hs⟩⟩)
  exact SafeUntil.deterministic_step (b := atPick g body (st.set i .done) env tail t)
    ⟨(by intro h; cases h), rfl⟩
    (Step.unseqValue get (d.bodies i hi) cell write) rfl
    ⟨⟨st, binary, hs⟩, ⟨st.set i .done, binary.set_done i, ht⟩⟩ (next t ht)

theorem Domain.complete {ctx g env} (d : Domain ctx g env)
    {st : List UnseqStatus} (binary : Binary g st) (settled : g.allSettled st = true)
    {s : Store} (hs : d.heap.At st s) (body : Stmt) (tail : Continuation) :
    SafeUntil ctx d.FrameStep (Completed d body tail) (atPick g body st env tail s) := by
  refine SafeUntil.deterministic_step (l := ⟨[], [], []⟩)
    (b := ⟨.next (.storeK [] [] body env tail.toMachine), s⟩)
    ⟨(by intro h; cases h), rfl⟩ ?_ rfl ⟨⟨st, binary, hs⟩, ⟨st, binary, hs⟩⟩ ?_
  · exact Step.unseqComplete binary.no_skipped_dependencies settled
      (d.ranked.completion_produced binary settled d.stores body)
      (by simp [d.stores, unseqStorePlan, pure, Except.pure])
  refine SafeUntil.deterministic_step (b := ⟨.exec body env tail.toMachine, s⟩)
    ⟨(by intro h; cases h), rfl⟩ Step.storeDone rfl ⟨⟨st, binary, hs⟩, ⟨st, binary, hs⟩⟩ ?_
  exact .done ⟨rfl, st, binary, settled, hs⟩

/-- General all-schedule progress/safety to the completion boundary. The
well-founded measure counts active occurrences, not an enumeration of schedules. -/
theorem Domain.all_schedules {ctx g env} (d : Domain ctx g env)
    (body : Stmt) (tail : Continuation) (st : List UnseqStatus)
    (binary : Binary g st) (s : Store) (hs : d.heap.At st s) :
    SafeUntil ctx d.FrameStep (Completed d body tail) (atPick g body st env tail s) := by
  have traversal := d.ranked.traversal
    (fun st binary i ready => (d.evaluates st binary i ready).withTrue) st binary
  induction traversal generalizing s with
  | done binary settled => exact d.complete binary settled hs body tail
  | next binary settled nonempty paths _ ih =>
    refine .step ⟨(by intro h; cases h), rfl⟩ (scheduler_total binary settled nonempty) ?_ ?_
    · intro l b ht
      rcases b with ⟨c,t⟩
      cases ht <;> exact ⟨⟨_, binary, hs⟩, ⟨_, binary, hs⟩⟩
    intro l b step
    rcases b with ⟨c,t⟩
    cases step with
    | unseqComplete _ done _ _ => simp [settled] at done
    | unseqPick _ pick =>
      have ready := List.mem_of_getElem? pick
      apply d.occurrence binary ready (paths _ ready).forget hs body tail
      intro t ht
      exact ih _ ready (binary.set_done _) t ht

theorem Domain.completed_unique {ctx g env} (d : Domain ctx g env)
    {body tail a b} (ha : Completed d body tail a) (hb : Completed d body tail b) : a = b := by
  obtain ⟨ca, sa, ba, da, ha⟩ := ha
  obtain ⟨cb, sb, bb, db, hb⟩ := hb
  have stores := ha.unique_done hb
    (fun i hi => ba.settled_done da i (by rw [← d.count]; exact hi))
    (fun i hi => bb.settled_done db i (by rw [← d.count]; exact hi))
  cases a; cases b
  simp_all

/-- A client can stop at any real intermediate step and recover the heap
invariant; progress continues on every tape unless the completion was reached. -/
theorem Domain.prefix_memory {ctx g env} (d : Domain ctx g env)
    {body tail st s a ls} (binary : Binary g st) (hs : d.heap.At st s)
    (pre : SegmentPrefix ctx (Completed d body tail) (atPick g body st env tail s) ls a) :
    d.MemInvariant a :=
  (d.all_schedules body tail st binary s hs).prefix_fact ⟨st, binary, hs⟩
    (fun _ _ _ label => label.2) pre

theorem Domain.prefix_progress {ctx g env} (d : Domain ctx g env)
    {body tail st s a ls} (binary : Binary g st) (hs : d.heap.At st s)
    (pre : SegmentPrefix ctx (Completed d body tail) (atPick g body st env tail s) ls a)
    (notDone : ¬ Completed d body tail a) :
    StepAdmission a.control ∧ TotalStep ctx a := by
  have h := ((d.all_schedules body tail st binary s hs).after_prefix pre).progress notDone
  exact ⟨h.1, h.2.1⟩

end GoLean.GoCore.Relational.Unseq
