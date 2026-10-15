import GoLean.Relational
import GoLean.GoCore.PoolStep

/-! Exact obligations, compiled before their implementations. These are
propositions, never assumed axioms. The pool and driver carriers are upstream's. -/
namespace Concurrency
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.Relational

structure Ordinary (ctx : ProgramCtx) (m : MultiConfig) (i slot : Nat)
    (c : Config) : Prop where
  schedule : SchedSlot ctx m i slot
  thread : m.threads[i]? = some (.running c none)
  unblocked : isBlockedConfig c = false
  noSpawn : spawnPlan c = none
  arrival : arrivalCases ctx m.shared m.threads i c = .ok .cellPath
  noSelect : selectApplyPlan c = none

def EffectReuse : Prop :=
  ∀ (ctx : ProgramCtx) (op : Store → Store → Prop) (c d : Config)
    (m : MultiConfig) (t : Store) (i slot : Nat),
    StoreEffect ctx op c d → Ordinary ctx m i slot c → op m.shared t →
    ∃ l : StepLabel, l.picks = [] ∧ StepML ctx m
      ⟨m.threads.setIfInBounds i (Thread.afterStep m.shared c d), t, i⟩
      ⟨i, .privateStep, ⟨l.trace, schedRecord ctx m slot ++ l.picks, l.out⟩⟩

/-- The concrete experiment must instantiate the pool, events, detector, tape
and exact step count. No detector success is a premise of this obligation. -/
def CheckedPrefix (ctx : ProgramCtx) (n : Nat) (start finish : MultiConfig)
    (tape tail : Choices) (events : List DriverEvent) (detector : RaceState) : Prop :=
  PoolPrefix ctx n start {} tape events finish detector tail

/-- A future general synchronization contract: the actual paired step and
detector update must be supplied, followed by a clock order for the old epoch.
This is deliberately parameterized; a concrete use site is required. -/
def TransferBoundary (ctx : ProgramCtx) (m m' : MultiConfig) (r r' : RaceState)
    (ev : StepEvent) (sender receiver : Nat) : Prop :=
  StepML ctx m m' ev ∧ raceUpdate ev m' r = .ok r' ∧
    ∀ t, (r.vcOf sender).get t ≤ (r'.vcOf receiver).get t

end Concurrency
