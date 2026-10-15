import Concurrency.Reuse
import Concurrency.Fixture
import Concurrency.Certificate

set_option cbv.warning false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Concurrency
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.Relational

def at8 := sample% certify ctx 8 initial {} tape
def at9 := sample% certify ctx 9 initial {} tape
def at14 := sample% certify ctx 14 initial {} tape
def at15 := sample% certify ctx 15 initial {} tape
def at19 := sample% certify ctx 19 initial {} tape
def at22 := sample% certify ctx 22 initial {} tape
def finalStore : Store := ⟨#[.value .bool (.bool false), .value .bool (.bool true)]⟩
def finalPool : MultiConfig :=
  ⟨#[.running (.next .stop) none, .running (.next .stop) none], finalStore, 0⟩
def printK (rest : List Stmt) : Continuation :=
  ⟨.stmtOpK (.print false) 0 [] [] env (.seq rest env .stop)⟩
def afterRead : MultiConfig :=
  ⟨#[.running (.retV (.bool false) (printK []).toMachine) none,
     .running (.next .stop) none], finalStore, 0⟩
def afterPrint : MultiConfig :=
  ⟨#[.running (.next (.seq [] env .stop)) none, .running (.next .stop) none], finalStore, 0⟩
def readEvent : StepEvent := ⟨0, .privateStep, ⟨[.access .read (.data x)], [], []⟩⟩
def printEvent : StepEvent := ⟨0, .privateStep,
  ⟨[], [], [GoString.fromLeanString "false"]⟩⟩
def doneEvent : StepEvent := ⟨0, .privateStep, ⟨[], [], []⟩⟩

/-- Actual detector acceptance, with the D1 total comparator. -/
theorem detector_accepts : ∃ r, raceUpdate readEvent afterRead at22.2.2.1 = .ok r := by
  let r := at22.2.2.1
  let cell := ((r.shadow.find? (·.1 == .data x)).map (·.2)).getD {}
  refine ⟨{ r with shadow := (shadowSet r.shadow (.data x)
    (cell.record .read 0 ((r.vcOf 0).get 0))) }, ?_⟩
  dsimp only [cell, r]
  cbv

noncomputable def readRace : RaceState := Classical.choose detector_accepts
noncomputable def at25 : Certificate :=
  (at22.1 ++ [⟨[], readEvent⟩, ⟨[], printEvent⟩, ⟨[], doneEvent⟩], finalPool, readRace, [])

theorem prefix22 : PoolPrefix ctx 22 initial {} tape at22.1 at22.2.1 at22.2.2.1 [] := by
  exact certify_sound (by cbv)

theorem suffix3 : PoolPrefix ctx 3 at22.2.1 at22.2.2.1 []
    [⟨[], readEvent⟩, ⟨[], printEvent⟩, ⟨[], doneEvent⟩] finalPool readRace [] := by
  apply PoolPrefix.step (m' := afterRead) (ev := readEvent)
    (live_continue (by decide) []) (by rfl) (Classical.choose_spec detector_accepts)
  apply PoolPrefix.step (m' := afterPrint) (ev := printEvent)
    (live_continue (by decide) []) (by rfl) (by rfl)
  exact PoolPrefix.step (live_continue (by decide) []) (by rfl) (by rfl) .done


theorem accepted : CheckedPrefix ctx 25 initial at25.2.1 tape at25.2.2.2
    at25.1 at25.2.2.1 := by
  exact PoolSound.poolPrefix_comp ctx 22 3 _ _ _ _ _ _ _ _ _ _ _ prefix22 suffix3

theorem labelled : StepsML ctx initial at25.2.1
    (PoolStatement.DriverEvent.events at25.1) :=
  PoolSound.poolPrefix_labelled ctx 25 initial at25.2.1 {} at25.2.2.1 tape
    at25.2.2.2 at25.1 accepted

theorem first_read : ∃ tr, StepML ctx at8.2.1
    ⟨at8.2.1.threads.setIfInBounds 0
      (Thread.afterStep at8.2.1.shared (.evalE (.var 0) env
        (printK [.print false #[.var 0]]).toMachine)
        (.retV (.bool false) (printK [.print false #[.var 0]]).toMachine)),
      at8.2.1.shared, 0⟩
    ⟨0, .privateStep, ⟨tr, schedRecord ctx at8.2.1 0, []⟩⟩ := by
  apply variable_phase_pool ctx at8.2.1 env (printK [.print false #[.var 0]]) 0 x
    (.bool false) 0 0 rfl
  · exact read_root (ty := .bool) rfl
  · exact ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

theorem child_write : storeLoc ctx at14.2.1.shared y (.bool true) =
    .ok at15.2.1.shared := by
  exact write_root (ty := .bool) (old := .bool false) rfl rfl

theorem preserved_read : loadRoot ctx at15.2.1.shared x = .ok (.bool false) :=
  read_after_disjoint_write (ty := .bool) rfl (by decide) child_write

theorem second_read : ∃ tr, StepML ctx at22.2.1
    ⟨at22.2.1.threads.setIfInBounds 0
      (Thread.afterStep at22.2.1.shared (.evalE (.var 0) env (printK []).toMachine)
        (.retV (.bool false) (printK []).toMachine)), at22.2.1.shared, 0⟩
    ⟨0, .privateStep, ⟨tr, schedRecord ctx at22.2.1 0, []⟩⟩ := by
  apply variable_phase_pool ctx at22.2.1 env (printK []) 0 x (.bool false) 0 0 rfl
  · exact preserved_read
  · exact ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

/-- The disjoint write really happened between the two reads, while the
parent was paused at print apply, not inside either read phase. -/
theorem boundary_and_change :
    at9.2.1.threads[0]? = some (.running
      (.retV (.bool false) (printK [.print false #[.var 0]]).toMachine) none) ∧
    at9.2.1.schedMenu? ctx = some (.l1Sched, [0, 1]) ∧
    at15.2.1.shared.heap[1]? = some (.value .bool (.bool true)) ∧
    at9.2.1.shared.heap[1]? = some (.value .bool (.bool false)) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem exact_events :
    (at25.1.map (·.event.who)) = List.replicate 9 0 ++ List.replicate 10 1 ++ List.replicate 6 0 ∧
    (at25.1.flatMap (·.event.label.picks)) =
      [⟨.l1Sched, 2, 0⟩, ⟨.l1Sched, 2, 1⟩] ∧
    (at25.1.flatMap (fun d => d.event.trace.map (fun e => (d.event.who, e)))) =
      [(0, .hb (.spawn 1)), (0, .access .read (.data x)),
       (1, .access .write (.data y)), (0, .access .read (.data x))] := by
  exact ⟨rfl, rfl, rfl⟩

theorem finished : PoolFinish ctx at25.2.1 at25.2.2.1 at25.2.2.2 []
    (.normal at25.2.1.shared []) 0 := .normal rfl rfl rfl

/-- Exactly 25 iterations, including the spawn flag's boundary-clear step.
The cost-zero final classification is checked even with no residual fuel. -/
theorem actual_driver : execProgLoopOut ctx 25 initial {} tape GoString.empty =
    (GoString.fromLeanString "falsefalse", .ok (at25.2.1.shared, [])) := by
  rw [PoolSound.poolPrefix_run ctx 25 0 initial at25.2.1 {} at25.2.2.1 tape
    at25.2.2.2 at25.1 GoString.empty accepted]
  rfl

theorem entry_driver : execProg ctx 25 env initialStore tape program =
    .ok (at25.2.1.shared, []) := by
  change execProgLoop ctx 25 initial {} tape = _
  rw [← execProgLoopOut_snd (ctx := ctx) 25 initial {} tape GoString.empty]
  exact congrArg Prod.snd actual_driver

theorem one_less_fuel : execProgLoopOut ctx 24 initial {} tape GoString.empty =
    (GoString.fromLeanString "falsefalse", .error .fuelOut) := by
  rw [PoolSound.poolPrefix_run ctx 22 2 initial at22.2.1 {} at22.2.2.1 tape
    [] at22.1 GoString.empty prefix22]
  rw [GoLean.Semantics.Pool.unfold_driver]
  change (match raceUpdate readEvent afterRead at22.2.2.1 with
    | .error e => (GoString.fromLeanString "false", (Except.error e : Except Stop (Store × Choices)))
    | .ok r => execProgLoopOut ctx 1 afterRead r [] (GoString.fromLeanString "false")) = _
  rw [Classical.choose_spec detector_accepts]
  rfl

end Concurrency
