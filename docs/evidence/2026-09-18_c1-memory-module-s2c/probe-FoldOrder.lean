import GoLean.ChoiceTrace
/-! C1 S2c-i positive control (2026-09-18): the label's ORDER is load-bearing and the
tracer's fold-equality audit DETECTS a difference. Two labels that differ only in
the order of `Mutex.Unlock`'s state Add (`.access .atomicWrite @state`) and its
release action fold to DIFFERENT detector states (the access is recorded at the
pre-release epoch in one, at the bumped epoch in the other), and `Acc.auditFold`
reports it. A two-goroutine pool (the fold is inert at ≤ 1). -/
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.ChoiceTrace

def loc0 : Loc := .base ⟨0⟩
def key0 : ShadowKey := syncWord loc0 .mutex .state
def tailFirst : AccessTrace := [.access .atomicWrite key0, .hb (.syncRelease loc0 false)]
def releaseFirst : AccessTrace := [.hb (.syncRelease loc0 false), .access .atomicWrite key0]
def pool2 : MultiConfig :=
  { threads := #[.running (.next .stop) none, .running (.next .stop) none], shared := {}, cur := 0 }
def ev (tr : AccessTrace) : StepEvent := { who := 0, action := .privateStep, picks := [], out := [], trace := tr }

#eval (raceFold (ev tailFirst) pool2 {} |>.toOption |>.map (·.clocks))
#eval (raceFold (ev releaseFirst) pool2 {} |>.toOption |>.map (·.clocks))
#eval (raceFold (ev tailFirst) pool2 {} |>.toOption |>.map (fun r => r.shadow.map (·.2.writes)))
#eval (raceFold (ev releaseFirst) pool2 {} |>.toOption |>.map (fun r => r.shadow.map (·.2.writes)))
-- the audit instrument on the two folds: a finding
#eval ((({ stream := [] } : Acc).auditFold (ev tailFirst) (raceFold (ev tailFirst) pool2 {}) (raceFold (ev releaseFirst) pool2 {})).mismatches)
-- and on equal folds: none
#eval ((({ stream := [] } : Acc).auditFold (ev tailFirst) (raceFold (ev tailFirst) pool2 {}) (raceFold (ev tailFirst) pool2 {})).mismatches)
-- inert at one goroutine: both labels fold to the empty state
#eval (raceFold (ev tailFirst) { pool2 with threads := #[.running (.next .stop) none] } {} |>.toOption |>.map (·.clocks))
