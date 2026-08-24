import GoLeanProofs.FastEval.Transfer
import GoLeanProofs.Examples.GcdProgram

/-!
# FastEval — the transfer theorem's non-vacuity witness (unit P2R)

`fastRun_transfer_eqb` instantiated end-to-end on the pinned gcd
lowering: every premise discharged by kernel computation (`#eval`-first
per the repo rule: anchor eqb evaluates `true`, exact completion count
150 steps measured before asking the kernel). No literal transcription:
the setup components are named PROJECTIONS of the setup call, so the
premise equations are kernel `rfl` facts about the same computation —
zero drift by construction. UNTRUSTED METHOD — never in any statement
closure; the conclusion reads over `runProgramM` alone.
-/

namespace GoLean.FastEval.Witness

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.FastEval
open GoLean.Examples.Gcd

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def wArgs : Array GoValue := #[.int 21 .uint64, .int 14 .uint64]

/-- The witness setup call (fuel 400 covers the 150-step body). -/
def wSetup := runProgramSetupM 400 gcdLowered "gcd" wArgs []

def wC0 : Config := match wSetup with | .ok (c, _, _, _) => c | _ => .next .stop
def wS3 : ExecState := match wSetup with | .ok (_, s, _, _) => s | _ => {}
def wLocs : List Loc := match wSetup with | .ok (_, _, l, _) => l | _ => []
def wCh1 : Choices := match wSetup with | .ok (_, _, _, ch) => ch | _ => []

/-- The witness fast run (exactly 150 steps to `.next .stop`). -/
def wRun := iterF stepFast 150 (absState wS3) wC0 wCh1

def wSF' : ExecStateF := match wRun with | .ok (_, σF, _) => σF | _ => {}
def wCh' : Choices := match wRun with | .ok (_, _, ch) => ch | _ => []

set_option smartUnfolding false in
private theorem wSetup_eq : wSetup = .ok (wC0, wS3, wLocs, wCh1) := by
  with_unfolding_all rfl

set_option smartUnfolding false in
private theorem wAnchor : ExecState.eqb (γF (absState wS3)) wS3 = true := by
  with_unfolding_all rfl

set_option smartUnfolding false in
private theorem wRun_eq : wRun = .ok (.next .stop, wSF', wCh') := by
  with_unfolding_all rfl

set_option smartUnfolding false in
private theorem wLoad : loadManyF wSF' wLocs = .ok [.int 7 .uint64] := by
  with_unfolding_all rfl

/-- **The witness** (non-vacuity gate): the transfer theorem's premises
are jointly satisfiable on a real lowered program, and the conclusion
is the interpreter's own verdict — `gcd(21, 14) = 7`. -/
theorem fastRun_transfer_witness :
    runProgramM 400 gcdLowered "gcd" wArgs []
      = .ok { values := #[.int 7 .uint64] } :=
  fastRun_transfer_eqb (n := 150) wSetup_eq wAnchor (by omega) wRun_eq wLoad

end GoLean.FastEval.Witness
