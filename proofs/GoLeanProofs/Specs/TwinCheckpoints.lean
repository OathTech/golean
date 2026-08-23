import GoLeanProofs.Specs.StateWire

/-!
# Mid-run checkpoints of the pinned twin (campaign Arc 2, U2 — the
go/no-go measurement's subject; route memo §5 charter items 1–2)

Each checkpoint is the `(heap, nextAddr, config, choices)` literal
reached after the named number of SUBJECT-phase steps
(post-`runProgramSetupM` prelude), reflected at elaboration by
`twinCheckpoint%` (`StateWire.lean` — the fail-loud reflector; a
drifted literal fails the downstream segment `rfl`, never lies).
Checkpoint states are spelled program-generically:
`{ twinBase with heap := …, nextAddr := … }` — the tables appear once,
in `twinBase`.

Chosen index: 350,000 — mid-run, heap 19,093 cells (probe C,
`docs/campaign-arc2-probes/records/probeC-heapgrowth.out`), the
representative point the route memo's projections need.
-/

namespace GoLean.Examples.RaftTwin

open GoLean.GoCore GoLean.GoCore.Machine GoLean.StateWire

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 0 in
/-- The 350,000-subject-step checkpoint, reflected. -/
def ckpt350k : Heap × Nat × Config × Choices := twinCheckpoint% 350000

/-- The checkpoint's machine state, program-generic spelling. -/
def ckpt350kState : ExecState :=
  { twinBase with heap := ckpt350k.1, nextAddr := ckpt350k.2.1 }

/-- The checkpoint's configuration. -/
def ckpt350kCfg : Config := ckpt350k.2.2.1

/-- The checkpoint's remaining choice stream. -/
def ckpt350kCh : Choices := ckpt350k.2.2.2

end GoLean.Examples.RaftTwin
