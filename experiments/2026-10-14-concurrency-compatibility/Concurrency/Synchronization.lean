import Concurrency.Example

set_option cbv.warning false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Concurrency.Sync
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.Relational

def worker : Func :=
  { id := ⟨"worker"⟩, args := #[], results := #[], body := .seqn #[
    .assign (.addr (.global 0)) (.boolLit true),
    .chanSend (.deref (.global 2) (.chan .both .bool)) (.boolLit true) .bool] }
def ctx : ProgramCtx := .ofTables (functions := #[worker])
def program : Stmt := .seqn #[
  .goStmt (.funcVal ⟨"worker"⟩ #[]) #[],
  .chanRecv #[] (.deref (.global 2) (.chan .both .bool)) .bool,
  .print false #[.var 0]]
def store : Store := ⟨#[.value .bool (.bool false), .value .bool (.bool false),
  .value (.chan .both .bool) (.chan ⟨some (.base ⟨3⟩)⟩), .chanPayload #[] 0 false]⟩
def initial : MultiConfig := ⟨#[.running (.exec program env .stop) none], store, 0⟩
def tape : Choices := [1]

/-- Expected detector data only; each use below proves the actual fold equals it. -/
def recorded (r : RaceState) (who : Nat) (kind : AccessKind) (key : ShadowKey) : RaceState :=
  let cell := ((r.shadow.find? (·.1 == key)).map (·.2)).getD {}
  { r with shadow := shadowSet r.shadow key (cell.record kind who ((r.vcOf who).get who)) }

def at13 := sample% certify ctx 13 initial {} tape
def at27 := sample% certify ctx 27 initial {} tape
def step27 := sample% stepMulti ctx at27.2.1 at27.2.2.2
def r28 := recorded at27.2.2.1 0 .read (.data (.base ⟨2⟩))

theorem detector28 : raceUpdate step27.2.2 step27.1 at27.2.2.1 = .ok r28 := by
  cbv

def park := sample% certify ctx 1 step27.1 r28 step27.2.1
def pairStep := sample% stepMulti ctx park.2.1 park.2.2.2
def paired : StepEvent := ⟨1, .paired 0,
  ⟨[.access .read (.chanObj (.base ⟨3⟩)), .hb (.rendezvous 0)], [], []⟩⟩
def r30 := (recorded park.2.2.1 1 .read (.chanObj (.base ⟨3⟩))).rendezvous 1 0

theorem actual_pair : stepMulti ctx park.2.1 park.2.2.2 =
    .ok (pairStep.1, pairStep.2.1, paired) := rfl

theorem detector_pair : raceUpdate paired pairStep.1 park.2.2.1 = .ok r30 := by
  cbv

def resume := sample% certify ctx 5 pairStep.1 r30 pairStep.2.1
def step35 := sample% stepMulti ctx resume.2.1 resume.2.2.2
def r36 := recorded resume.2.2.1 0 .read (.data x)

theorem detector36 : raceUpdate step35.2.2 step35.1 resume.2.2.1 = .ok r36 := by
  cbv

def finish := sample% certify ctx 2 step35.1 r36 step35.2.1

def events : List DriverEvent := at27.1 ++ [⟨[], step27.2.2⟩] ++ park.1 ++
  [⟨[], paired⟩] ++ resume.1 ++ [⟨[], step35.2.2⟩] ++ finish.1

theorem prefix27 : PoolPrefix ctx 27 initial {} tape at27.1 at27.2.1 at27.2.2.1 [] :=
  certify_sound (by cbv)

theorem accepted : CheckedPrefix ctx 38 initial finish.2.1 tape finish.2.2.2
    events finish.2.2.1 := by
  have tail : PoolPrefix ctx 3 resume.2.1 resume.2.2.1 []
      (⟨[], step35.2.2⟩ :: finish.1) finish.2.1 finish.2.2.1 [] :=
    .step (live_continue (by decide) []) (by rfl) detector36 (certify_sound (by cbv))
  have resumed := PoolSound.poolPrefix_comp ctx 5 3 _ _ _ _ _ _ _ _ _ _ _
    (certify_sound (show certify ctx 5 pairStep.1 r30 [] = .ok resume from by cbv)) tail
  have pair : PoolPrefix ctx 9 park.2.1 park.2.2.1 []
      (⟨[], paired⟩ :: (resume.1 ++ ⟨[], step35.2.2⟩ :: finish.1))
      finish.2.1 finish.2.2.1 [] :=
    .step (live_continue (by decide) []) actual_pair detector_pair resumed
  have parked := PoolSound.poolPrefix_comp ctx 1 9 _ _ _ _ _ _ _ _ _ _ _
    (certify_sound (show certify ctx 1 step27.1 r28 [] = .ok park from by cbv)) pair
  have read : PoolPrefix ctx 11 at27.2.1 at27.2.2.1 []
      (⟨[], step27.2.2⟩ :: (park.1 ++ ⟨[], paired⟩ ::
        (resume.1 ++ ⟨[], step35.2.2⟩ :: finish.1))) finish.2.1 finish.2.2.1 [] :=
    .step (live_continue (by decide) []) (by rfl) detector28 parked
  have tailEmpty : finish.2.2.2 = [] := by rfl
  simpa [CheckedPrefix, events, List.append_assoc, tailEmpty] using
    (PoolSound.poolPrefix_comp ctx 27 11 _ _ _ _ _ _ _ _ _ _ _ prefix27 read)

/-- Concrete sender-to-receiver rendezvous ordering at a detector state reached from
the actual spawn. The detector's actual shadow state is retained. -/
theorem transfer_boundary : TransferBoundary ctx park.2.1 pairStep.1
    park.2.2.1 r30 paired 1 0 := by
  refine ⟨PoolSound.stepML_sound ctx _ _ _ _ _ actual_pair, detector_pair, ?_⟩
  intro t
  have hb : park.2.2.1.vcOf 1 = #[1, 1] := by cbv
  have ha : r30.vcOf 0 = #[3, 1] := by cbv
  rw [hb, ha]
  cases t with
  | zero => decide
  | succ t => cases t with
    | zero => decide
    | succ t => simp [VClock.get]

theorem paired_flags :
    (pairStep.1.threads[1]?).bind (fun t => match t with
      | .running _ flag => flag | .aborted _ => none) = some .postOp ∧
    (pairStep.1.threads[0]?).bind (fun t => match t with
      | .running _ flag => flag | .aborted _ => none) = none ∧
    pairStep.1.threads[0]? ≠ park.2.1.threads[0]? := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  cases h

/-- Counterfactual detector probe immediately after the child's write, before
its channel-handle read. This is not an invented schedulable pool step. -/
theorem read_before_handoff_rejected :
    at13.2.2.1.events 0 [.access .read (.data x)] = .error .raceDetected := rfl

/-- Negative detector control immediately before the reachable rendezvous. -/
def PrePairRejection : Prop :=
  park.2.2.1.events 0 [.access .read (.data x)] = .error .raceDetected

/-- The real intervening 16 driver steps, including unrelated channel-handle
accesses and receiver parking. This starts at the reached post-write state. -/
def gap := sample% certify ctx 16 at13.2.1 at13.2.2.1 at13.2.2.2

theorem gap_ends : gap.2.1 = park.2.1 ∧ gap.2.2.1 = park.2.2.1 := by cbv

theorem gap_checked : PoolPrefix ctx 16 at13.2.1 at13.2.2.1 at13.2.2.2
    gap.1 gap.2.1 gap.2.2.1 gap.2.2.2 := certify_sound (by cbv)

theorem pre_pair_ordered : ShadowOrdered park.2.2.1.shadow := by
  rw [← gap_ends.2]
  exact gap_checked.shadow_ordered
    ((certify_sound (show certify ctx 13 initial {} tape = .ok at13 from by cbv)).shadow_ordered_empty)

/-- General prefix history preservation, instantiated without a final-state
map invariant assumption. The accesses in the gap use different exact keys. -/
theorem pre_pair_history : shadowLookup park.2.2.1.shadow (.data x) =
    shadowLookup at13.2.2.1.shadow (.data x) := by
  rw [← gap_ends.2]
  apply gap_checked.preserves_lookup
  simp [gap, StepEvent.trace, MemEvent.AvoidsKey, x]

/-- Unconditional negative control. The old write's history survives by the
general law, and that retained access conflicts with the receiver's clock. -/
theorem pre_pair_rejection : PrePairRejection := by
  let cell := ({} : ShadowCell).record .write 1 1
  have found : shadowLookup park.2.2.1.shadow (.data x) = some cell := by
    rw [pre_pair_history]
    rfl
  have rejected := RaceState.accessKey_reject_of_mem
    (t := 0) (kind := AccessKind.read) (key := ShadowKey.data x)
    (shadowLookup_mem found) (by decide) (by decide)
  unfold PrePairRejection
  simp [RaceState.events, RaceState.event, rejected, Bind.bind, Except.bind]

/-- D1 refutes the old conditional countermodel's premise. -/
theorem comparison_not_equal :
    instOrdLoc.ord (.base ⟨2⟩) (.base ⟨0⟩) ≠ .eq := by decide

/-- Historical conditional statement retained, now with an impossible premise.
It no longer describes an open ordering obligation. -/
theorem equal_comparison_loses_rejection
    (equal : instOrdLoc.ord (.base ⟨2⟩) (.base ⟨0⟩) = .eq) :
    ¬ PrePairRejection := by
  exact False.elim (comparison_not_equal equal)

theorem post_handoff_read : ∃ tr, StepML ctx resume.2.1
    ⟨resume.2.1.threads.setIfInBounds 0
      (Thread.afterStep resume.2.1.shared (.evalE (.var 0) env (printK []).toMachine)
        (.retV (.bool true) (printK []).toMachine)), resume.2.1.shared, 0⟩
    ⟨0, .privateStep, ⟨tr, schedRecord ctx resume.2.1 0, []⟩⟩ := by
  apply variable_phase_pool ctx resume.2.1 env (printK []) 0 x (.bool true) 0 0 rfl
  · exact read_root (ty := .bool) rfl
  · exact ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

theorem actual_driver : execProgLoopOut ctx 38 initial {} tape GoString.empty =
    (GoString.fromLeanString "true", .ok (finish.2.1.shared, [])) := by
  rw [PoolSound.poolPrefix_run ctx 38 0 initial finish.2.1 {} finish.2.2.1 tape
    finish.2.2.2 events GoString.empty accepted]
  rfl

theorem exact_choices : events.flatMap (·.event.label.picks) =
    [⟨.l1Sched, 2, 1⟩, ⟨.l1Sched, 2, 0⟩, ⟨.l1Sched, 2, 0⟩, ⟨.postOp, 2, 0⟩] := rfl

theorem entry_driver : execProg ctx 38 env store tape program =
    .ok (finish.2.1.shared, []) := by
  change execProgLoop ctx 38 initial {} tape = _
  rw [← execProgLoopOut_snd (ctx := ctx) 38 initial {} tape GoString.empty]
  exact congrArg Prod.snd actual_driver

end Concurrency.Sync
