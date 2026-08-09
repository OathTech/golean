/-!
# verdi-raft's per-node state record

1:1 port of `deps/verdi-raft/theories/Raft/RaftState.v:15-38` (the record;
their lines 41-128 are python2-generated setter boilerplate + update
notations, all subsumed by Lean's native `{ s with f := v }`).

`electoralVictories` is a GHOST field: it is baked into the real state
record but written only by `handleRequestVoteReply` on victory and read
by no handler. Kept for 1:1 fidelity; dropping it is a recorded option in
the design note.
-/

namespace VerdiCompat

/-- `RaftState.v:15-38` -/
structure RaftData (term name entry logIndex serverType stateMachineData clientId output : Type) where
  -- persistent
  currentTerm : term
  votedFor : Option name
  leaderId : Option name
  log : List entry
  -- volatile
  commitIndex : logIndex
  lastApplied : logIndex
  stateMachine : stateMachineData
  -- leader state
  nextIndex : List (name × logIndex)
  matchIndex : List (name × logIndex)
  shouldSend : Bool
  -- candidate state
  votesReceived : List name
  -- whoami
  type : serverType
  -- client request state
  clientCache : List (clientId × (Nat × output))
  -- ghost variables
  electoralVictories : List (term × List name × List entry)

end VerdiCompat
