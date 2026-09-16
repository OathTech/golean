import GoLean.GoCore.MachineSound

/-!
# The `unseq` construct's mechanism theorem — statements and Stage B's proofs

Design `docs/2026-09-16_evaluation-order-model-v2.md` §7 (the WIRE SCHEDULER
THEOREM, as tightened by the second review §4), lane
`core/unseq-scheduler-b-0916`, 2026-09-16. Stage B states the theorem over the
executed occurrence TRACE and proves its STEP-LEVEL interfaces — the facts the
multi-step composition rests on:

* T1 `unseq_pick_ready` — the scheduler runs only READY occurrences (every edge
  respected at the pick: value dependencies produced, order prerequisites
  discharged, region enabled — `UnseqGraph.ready`).
* T2 `unseq_pick_active` — a picked occurrence is ACTIVE: no double execution
  (a completed occurrence is DONE or SKIPPED, and only ACTIVE ones are ready).
* T3 `unseq_panic_drops_frame` — an escaping panic is a legal PREFIX ending at
  that failure: the sweep frame, its binders and its pending work are dropped
  over the UNCHANGED state (no later effect of this sweep), the effect prefix
  so far stands, defers and `recover` are the callee frames' business.
* T4 `unseq_complete_settled` — a successful trace COMPLETES the active graph:
  the completion step fires only with every occurrence settled, with every
  binder its stores and its completion statement consume PRODUCED
  (`UnseqGraph.unproducedConsumer?`; audit F1, 2026-09-16 — a skipped
  producer's cell is never consumed as a value), and hands exactly the
  graph's stores to the phase-2 spine.
* T5 `unseq_record_stable` — the frame's static record (graph, completion
  statement, scope, tail) is invariant along the scheduler's own steps
  (freshness: cells are allocated once, at ENTER).
* T6 `unseq_done_permanent` — DONE is permanent along the scheduler's own
  steps (status monotonicity; with T2, an occurrence runs at most once).
* Completeness at the step level is `step_complete`/`step_complete_any_wf`
  (MachineSound): every rule — the pick for EVERY ready occurrence included
  — is some tape's `stepFn` step, at every stream.

OWED (not proved in Stage B; recorded in the lane handoff): the MULTI-STEP
composition — every `Steps` execution from ENTER to completion projects to a
legal run of the graph (the occurrence bodies' internal steps, which pass
through non-sweep configurations, preserve the frame's record and return to
the pick position), and every legal finite run — including the occurrences'
own choice consumption — is realized by the concatenation of the per-step
tapes (a stream-composition lemma over `Steps` that MachineSound does not yet
state). The source-to-wire translation certificate is a separate owed
obligation (design §7(a)).
-/

namespace GoLean.GoCore.Machine

open GoLean

theorem unseq_pick_ready {g : UnseqGraph} {thenB : Stmt} {st : List UnseqStatus}
    {tg : List (String × TargetRef)} {env : LocalEnv} {k : Cont} {s : ExecState} {i : Nat}
    (h : Step (.next (.unseqK g thenB st tg env .pick k)) s
      (.next (.unseqK g thenB st tg env (.run i) k)) s) :
    i ∈ g.ready st := by
  cases h with
  | unseqPick hdep hj => exact List.mem_of_getElem? hj

theorem unseq_pick_active {g : UnseqGraph} {thenB : Stmt} {st : List UnseqStatus}
    {tg : List (String × TargetRef)} {env : LocalEnv} {k : Cont} {s : ExecState} {i : Nat}
    (h : Step (.next (.unseqK g thenB st tg env .pick k)) s
      (.next (.unseqK g thenB st tg env (.run i) k)) s) :
    i < g.occs.length ∧ st[i]? = some .active := by
  cases h with
  | unseqPick hdep hj => exact UnseqGraph.ready_active hj

theorem unseq_panic_drops_frame {chain : List PanicEntry} {g : UnseqGraph} {thenB : Stmt}
    {st : List UnseqStatus} {tg : List (String × TargetRef)} {env : LocalEnv} {ph : UnseqPhase}
    {k : Cont} {s : ExecState} {c' : Config} {s' : ExecState}
    (h : Step (.panicking chain (.unseqK g thenB st tg env ph k)) s c' s') :
    c' = .panicking chain k ∧ s' = s := by
  cases h with
  | panicUnwind hpass =>
      simp [panicPassthrough, Cont.isGlue, Cont.class, Cont.tail] at hpass
      subst hpass
      exact ⟨rfl, rfl⟩

theorem unseq_complete_settled {g : UnseqGraph} {thenB : Stmt} {st : List UnseqStatus}
    {tg : List (String × TargetRef)} {env : LocalEnv} {k : Cont} {s : ExecState}
    {refs : List TargetRef} {vals : List GoValue} {thenB' : Stmt} {env' : LocalEnv} {k' : Cont}
    {s' : ExecState}
    (h : Step (.next (.unseqK g thenB st tg env .pick k)) s
      (.next (.storeK refs vals thenB' env' k')) s') :
    g.allSettled st = true ∧ g.unproducedConsumer? st thenB = none
      ∧ unseqStorePlan s env tg g.stores = .ok (refs, vals)
      ∧ thenB' = thenB ∧ env' = env ∧ k' = k ∧ s' = s := by
  cases h with
  | unseqComplete hdep hall hprod hplan => exact ⟨hall, hprod, hplan, rfl, rfl, rfl, rfl⟩

theorem unseq_record_stable {g g' : UnseqGraph} {thenB thenB' : Stmt} {st st' : List UnseqStatus}
    {tg tg' : List (String × TargetRef)} {env env' : LocalEnv} {ph ph' : UnseqPhase} {k k' : Cont}
    {s s' : ExecState}
    (h : Step (.next (.unseqK g thenB st tg env ph k)) s
      (.next (.unseqK g' thenB' st' tg' env' ph' k')) s') :
    g' = g ∧ thenB' = thenB ∧ env' = env ∧ k' = k := by
  cases h with
  | unseqPick hdep hj => exact ⟨rfl, rfl, rfl, rfl⟩
  | unseqRunTarget hget hbody hplan => exact ⟨rfl, rfl, rfl, rfl⟩
  | unseqRunGuard hget hbody hg => exact ⟨rfl, rfl, rfl, rfl⟩
  | unseqStmtDone hget hbody => exact ⟨rfl, rfl, rfl, rfl⟩
  | unseqRunLoad hget hbody hres hdel =>
      rcases toResult_cases hres with ⟨s₂, rfl, hX⟩ | ⟨msg, rfl, hX⟩
      · simp only [deliver_ok, Prod.mk.injEq] at hdel
        obtain ⟨heq, -⟩ := hdel
        cases heq
        exact ⟨rfl, rfl, rfl, rfl⟩
      · obtain ⟨heq, -⟩ := deliver_panic_eq hdel
        cases heq

/-- Skipping never reactivates or un-does an occurrence: `skipOnce` moves
only ACTIVE members of a skipped region. -/
theorem UnseqGraph.skipOnce_done {g : UnseqGraph} {st : List UnseqStatus} {i : Nat}
    (hlen : st.length = g.occs.length) (hi : st[i]? = some .done) :
    (g.skipOnce st)[i]? = some .done := by
  have hlt : i < g.occs.length := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
  unfold UnseqGraph.skipOnce
  rw [List.getElem?_map, List.getElem?_range hlt]
  simp only [Option.map_some, hi]
  split <;> simp_all

theorem UnseqGraph.skipOnce_length {g : UnseqGraph} {st : List UnseqStatus} :
    (g.skipOnce st).length = g.occs.length := by
  simp [UnseqGraph.skipOnce]

theorem UnseqGraph.skipRegion_done {g : UnseqGraph} {st : List UnseqStatus} {gi i : Nat}
    (hlen : st.length = g.occs.length) (hne : i ≠ gi) (hi : st[i]? = some .done) :
    (g.skipRegion st gi)[i]? = some .done := by
  unfold UnseqGraph.skipRegion
  have hseed : (st.set gi .skipped)[i]? = some .done := by
    rw [List.getElem?_set_ne hne.symm]; exact hi
  have hseedlen : (st.set gi .skipped).length = g.occs.length := by simp [hlen]
  generalize st.set gi UnseqStatus.skipped = seeded at hseed hseedlen
  induction (List.range g.occs.length) generalizing seeded with
  | nil => simpa using hseed
  | cons _ rest ih =>
      simp only [List.foldl_cons]
      exact ih (g.skipOnce seeded) (UnseqGraph.skipOnce_done hseedlen hseed)
        UnseqGraph.skipOnce_length

theorem UnseqGraph.skipRegion_length {g : UnseqGraph} {st : List UnseqStatus} {gi : Nat}
    (hlen : st.length = g.occs.length) : (g.skipRegion st gi).length = g.occs.length := by
  unfold UnseqGraph.skipRegion
  have hseedlen : (st.set gi .skipped).length = g.occs.length := by simp [hlen]
  generalize st.set gi UnseqStatus.skipped = seeded at hseedlen
  induction (List.range g.occs.length) generalizing seeded with
  | nil => simpa using hseedlen
  | cons _ rest ih =>
      simp only [List.foldl_cons]
      exact ih _ UnseqGraph.skipOnce_length

theorem unseq_done_permanent {g : UnseqGraph} {thenB : Stmt} {st st' : List UnseqStatus}
    {tg tg' : List (String × TargetRef)} {env : LocalEnv} {ph ph' : UnseqPhase} {k : Cont}
    {s s' : ExecState} {i : Nat}
    (hlen : st.length = g.occs.length)
    (h : Step (.next (.unseqK g thenB st tg env ph k)) s
      (.next (.unseqK g thenB st' tg' env ph' k)) s')
    (hi : st[i]? = some .done) : st'[i]? = some .done := by
  have hlt : i < st.length := (List.getElem?_eq_some_iff.mp hi).1
  cases h with
  | unseqPick hdep hj => exact hi
  | unseqRunTarget hget hbody hplan =>
      rename_i j
      by_cases hij : j = i
      · subst hij; rw [List.getElem?_set_self hlt]
      · rw [List.getElem?_set_ne hij]; exact hi
  | unseqStmtDone hget hbody =>
      rename_i j
      by_cases hij : j = i
      · subst hij; rw [List.getElem?_set_self hlt]
      · rw [List.getElem?_set_ne hij]; exact hi
  | unseqRunLoad hget hbody hres hdel =>
      rename_i j
      rcases toResult_cases hres with ⟨s₂, rfl, hX⟩ | ⟨msg, rfl, hX⟩
      · simp only [deliver_ok, Prod.mk.injEq] at hdel
        obtain ⟨heq, -⟩ := hdel
        cases heq
        by_cases hij : j = i
        · subst hij; rw [List.getElem?_set_self hlt]
        · rw [List.getElem?_set_ne hij]; exact hi
      · obtain ⟨heq, -⟩ := deliver_panic_eq hdel
        cases heq
  | unseqRunGuard hget hbody hg =>
      rename_i j
      simp only [unseqGuard, bind_eq_ok] at hg
      obtain ⟨tl, -, tv, -, b, -, hg⟩ := hg
      split at hg
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hg
        obtain ⟨rfl, -⟩ := hg
        by_cases hij : j = i
        · subst hij; rw [List.getElem?_set_self hlt]
        · rw [List.getElem?_set_ne hij]; exact hi
      · simp only [bind_eq_ok] at hg
        obtain ⟨ol, -, s₂, -, hg⟩ := hg
        split at hg
        · rename_i ci hci
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hg
          obtain ⟨rfl, -⟩ := hg
          have hlenSR : (g.skipRegion st j).length = st.length := by
            rw [UnseqGraph.skipRegion_length hlen, hlen]
          by_cases hij : j = i
          · subst hij
            rw [List.getElem?_set_self (by rw [List.length_set, hlenSR]; exact hlt)]
          · rw [List.getElem?_set_ne hij]
            by_cases hic : ci = i
            · subst hic
              rw [List.getElem?_set_self (by rw [hlenSR]; exact hlt)]
            · rw [List.getElem?_set_ne hic]
              exact UnseqGraph.skipRegion_done hlen (Ne.symm hij) hi
        · simp [stuck, throw, throwThe, MonadExceptOf.throw] at hg

end GoLean.GoCore.Machine
