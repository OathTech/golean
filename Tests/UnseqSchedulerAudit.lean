import Tests.UnseqScheduler
import GoLean.GoCore.UnseqSound
import Lean

/-! The post-import audit of the `unseq` construct's coherence and mechanism
theorems (Stage B): every required theorem exists, and every declaration of
every local module in the import closure depends on the classical trio only —
no `sorry`, no axiom, no native decision. -/

open Lean

namespace Tests.UnseqSchedulerAudit

def exports : List Name := [
    ``GoLean.GoCore.Machine.stepUnseqEnter_sound,
    ``GoLean.GoCore.Machine.stepUnseqValue_sound,
    ``GoLean.GoCore.Machine.stepUnseqNext_sound,
    ``GoLean.GoCore.Machine.stepUnseqEnter_stream,
    ``GoLean.GoCore.Machine.stepUnseqValue_stream,
    ``GoLean.GoCore.Machine.stepUnseqNext_consumption_none,
    ``GoLean.GoCore.Machine.stepUnseqNext_consumption_some,
    ``GoLean.GoCore.Machine.stepFn_sound,
    ``GoLean.GoCore.Machine.step_complete,
    ``GoLean.GoCore.Machine.step_complete_any_wf,
    ``GoLean.GoCore.Machine.step_preserves_wf,
    ``GoLean.GoCore.Machine.stepFn_consumption_none,
    ``GoLean.GoCore.Machine.stepFn_consumption_some,
    ``GoLean.GoCore.Machine.seqConsumption_none_of_flags,
    ``GoLean.GoCore.Machine.stepFn_oblivious,
    ``GoLean.GoCore.UnseqGraph.ready_active,
    ``GoLean.GoCore.UnseqGraph.allSettled_false,
    ``GoLean.GoCore.UnseqGraph.ready_nil_of_allSettled,
    ``GoLean.GoCore.Machine.unseq_pick_ready,
    ``GoLean.GoCore.Machine.unseq_pick_active,
    ``GoLean.GoCore.Machine.unseq_panic_drops_frame,
    ``GoLean.GoCore.Machine.unseq_complete_settled,
    ``GoLean.GoCore.Machine.unseq_record_stable,
    ``GoLean.GoCore.Machine.unseq_done_permanent]

def run : CoreM Unit := do
  let env ← getEnv
  for m in [`GoLean.GoCore.Unseq, `GoLean.GoCore.UnseqSound, `GoLean.GoCore.MachineSound,
      `Tests.UnseqScheduler, `Tests.UnseqSchedulerAudit] do
    unless env.header.moduleNames.contains m do
      throwError "Unseq scheduler audit: missing module {m}"
  for n in exports do
    let some (.thmInfo _) := env.find? n
      | throwError "Unseq scheduler audit: missing theorem {n}"
  let ours := env.header.moduleNames.map fun n =>
    n.toString.startsWith "GoLean." || n.toString.startsWith "Tests."
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for (n, _) in env.constants.toList do
    let localModule := match env.getModuleIdxFor? n with
      | some i => ours[i.toNat]!
      | none => true
    unless localModule do continue
    for ax in (← collectAxioms n) do
      unless allowed.contains ax do
        throwError "Unseq scheduler audit: {n} depends on forbidden axiom {ax}"
    checked := checked + 1
  logInfo s!"Unseq scheduler audit: {exports.length} required theorems; {checked} declarations across all imported local origins; classical trio only"

end Tests.UnseqSchedulerAudit
