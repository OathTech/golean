import GoLeanProofs.Specs.StateWire
import GoLeanProofs.FastEval.Ops

/-!
# Trie-form checkpoints of the pinned twin (campaign Arc 2, U4 —
route (d)'s mid-build gate subject and assembly seed)

`twinCheckpointF%` reflections (`StateWire.lean`): the post-prelude
seed (n = 0) and the mid-run gate point (n = 350,000; heap 19,093
cells, probe C). The literals are scaffolding-emitted and
kernel-guarded downstream: the segment sims and the assembly's
`γF ckptF0State = s₃` equality are checked over exactly these terms —
a drifted literal fails a proof, never lies. UNTRUSTED METHOD — never
in any statement closure.
-/

namespace GoLean.Examples.RaftTwin

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.StateWire
open GoLean.FastEval

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 0 in
/-- The post-prelude seed, trie form (subject step 0). -/
def ckptF0 : HeapT × Nat × Config × Choices := twinCheckpointF% 0

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 0 in
/-- The 350,000-subject-step checkpoint, trie form (the U4 mid-build
gate's segment start). -/
def ckptF350k : HeapT × Nat × Config × Choices := twinCheckpointF% 350000

/-- The seed fast state (program-generic: tables once, from the pinned
lowering). -/
def twinBaseF : ExecStateF :=
  { types := twinLowered.typeDefs.toList
    functions := twinLowered.funcs
    methods := twinLowered.methods
    methodSets := twinLowered.methodSets
    heapT := ckptF0.1
    nextAddr := ckptF0.2.1 }

/-- The gate checkpoint's fast state. -/
def ckptF350kState : ExecStateF :=
  { twinBaseF with heapT := ckptF350k.1, nextAddr := ckptF350k.2.1 }

end GoLean.Examples.RaftTwin
