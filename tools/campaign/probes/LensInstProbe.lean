import GoLeanProofs
open GoLean GoLean.GoCore GoLean.RaftSeam
def σW : ExecState :=
  { wBase with heap := [(.base ⟨0⟩, ⟨some tyRaft, wRaftVal⟩),
                        (.base ⟨1⟩, ⟨some tyRaftLog, wLogVal⟩)],
               nextAddr := 2 }
#eval match storeLoc σW (.field (.base ⟨0⟩) ⟨"raft.raft"⟩ "Term") (.int 5 .uint64) with
  | .ok σ' => "OK; Term after = " ++ toString (repr (GoLean.Lens.fieldRead σ' ⟨0⟩ ⟨"raft.raft"⟩ "Term")) ++ "; Vote after = " ++ toString (repr (GoLean.Lens.fieldReadU64 σ' ⟨0⟩ ⟨"raft.raft"⟩ "Vote")) ++ "; Vote before = " ++ toString (repr (GoLean.Lens.fieldReadU64 σW ⟨0⟩ ⟨"raft.raft"⟩ "Vote"))
  | .error e => "ERROR: " ++ toString (repr e)
-- fieldTy? spot checks
#eval toString (repr (GoLean.Lens.structFieldTy wBase.types ⟨"raft.raft"⟩ "state"))
#eval toString (repr (GoLean.Lens.structFieldTy wBase.types ⟨"raft.raft"⟩ "Term"))
#eval toString (repr (TypeEnv.lookup wBase.types ⟨"raft.StateType"⟩))
#eval toString (repr (GoLean.Lens.fieldRead σW ⟨0⟩ ⟨"raft.raft"⟩ "state"))
