import GoLeanProofs.Specs.Raft.AbsStateV2
open GoLean GoLean.GoCore GoLean.RaftSeam
#eval toString (repr (absRaftLog (uσ 7 2 1 5) ⟨1⟩))
#eval toString (repr ((absRaftLog (uσ 7 2 1 5) ⟨1⟩).map AbsLog.lastIndex))
#eval toString (repr ((absRaftLog (uσ 7 2 1 5) ⟨1⟩).map AbsLog.view))
#eval toString (repr (absOutbox (uσ 7 2 1 5) ⟨0⟩ "msgs"))
#eval toString (repr (absOutbox (uσ 7 2 1 5) ⟨0⟩ "msgsAfterAppend"))
-- a hand message state: default Message value in a cell + one Term ptr
def tyMsg : Ty := .defined ⟨"raftpb.Message"⟩
def msgVal : GoValue := (defaultValue wBase tyMsg).toOption.getD .nil
def σM : ExecState :=
  { wBase with heap := [(.base ⟨0⟩, ⟨some tyMsg, msgVal⟩),
                        (.base ⟨1⟩, ⟨some (.int .uint64), .int 9 .uint64⟩)],
               nextAddr := 2 }
#eval toString (repr (absMessage σM (.addr (.base ⟨0⟩))))
-- with a populated Term field
def msgVal2 : GoValue :=
  match msgVal with
  | .struct tid fs => match StructFields.set fs "Term" (.addr (.base ⟨1⟩)) with
    | .ok fs2 => .struct tid fs2
    | .error _ => .nil
  | _ => .nil
def σM2 : ExecState :=
  { wBase with heap := [(.base ⟨0⟩, ⟨some tyMsg, msgVal2⟩),
                        (.base ⟨1⟩, ⟨some (.int .uint64), .int 9 .uint64⟩)],
               nextAddr := 2 }
#eval toString (repr (absMessage σM2 (.addr (.base ⟨0⟩))))
