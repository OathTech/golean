import Concurrency.Constraints
import GoLean.GoCore.PoolSound

namespace Concurrency
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.Relational

theorem effect_reuse : EffectReuse := by
  intro ctx op c d m t i slot effect ordinary operation
  obtain ⟨l, step, picks⟩ := effect.transition m.shared t operation
  exact ⟨l, picks, .thread ordinary.schedule ordinary.thread ordinary.unblocked
    ordinary.noSpawn ordinary.arrival ordinary.noSelect step⟩

/-- Consume the public variable StorePath at its first step. Its endpoint and
label are pinned by the existing read law and pick determinism. Every saved
continuation, value, pool and scheduling slot remains symbolic. -/
theorem variable_phase_pool (ctx : ProgramCtx) (m : MultiConfig) (env : LocalEnv)
    (k : Continuation) (id : VarId) (loc : Loc) (v : GoValue) (i slot : Nat)
    (bound : LocalEnv.lookup env id = some loc)
    (read : loadRoot ctx m.shared loc = .ok v)
    (ordinary : Ordinary ctx m i slot (.evalE (.var id) env k.toMachine)) :
    ∃ tr, StepML ctx m
      ⟨m.threads.setIfInBounds i
        (Thread.afterStep m.shared (.evalE (.var id) env k.toMachine)
          (.retV v k.toMachine)), m.shared, i⟩
      ⟨i, .privateStep, ⟨tr, schedRecord ctx m slot, []⟩⟩ := by
  have path := ReadOnlyExpr.variable ctx env id loc v bound k
  cases path with
  | step transition _ _ =>
    obtain ⟨l, step, picks⟩ := transition m.shared read
    obtain ⟨tr, expected⟩ := read_variable ctx m.shared env k id loc v bound read
    obtain ⟨endpoint, label⟩ := step.deterministic_by_picks expected picks
    cases endpoint
    cases label
    exact ⟨tr, by simpa using (StepML.thread ordinary.schedule ordinary.thread
      ordinary.unblocked ordinary.noSpawn ordinary.arrival ordinary.noSelect step)⟩

/-- Re-establish a root read after an actual successful write to a different
root. This is heap locality, independent of the pool's thread-frame law. -/
theorem read_after_disjoint_write {ctx : ProgramCtx} {s t : Store}
    {a : Addr} {ty : Ty} {v w : GoValue} {target : Loc}
    (cell : Heap.lookup s.heap (.base a) = some (.value ty v))
    (different : a.id ≠ (Loc.rootPath target).1.id)
    (write : storeLoc ctx s target w = .ok t) :
    loadRoot ctx t (.base a) = .ok v := by
  apply read_root (ty := ty)
  have keep := (write_support write).2 a.id (Heap.lookup_lt cell) different
  exact keep.trans cell

/-- The variable-read source itself is not a scheduling boundary, regardless
of its continuation. A pending flag would be a distinct pool step. -/
theorem variable_no_switch (ctx : ProgramCtx) (m m' : MultiConfig)
    (env : LocalEnv) (k : Cont) (id : VarId) (ev : StepEvent)
    (current : m.threads[m.cur]? = some (.running (.evalE (.var id) env k) none))
    (step : StepML ctx m m' ev) : ev.who = m.cur := by
  apply Classical.byContradiction
  intro h
  obtain ⟨t, ht, boundary⟩ := PoolSound.stepML_switch_boundary ctx m m' ev step h
  rw [current] at ht
  cases ht
  contradiction

end Concurrency
