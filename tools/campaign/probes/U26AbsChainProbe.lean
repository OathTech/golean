import GoLeanProofs.Specs.Raft.NativeEtcdDischarge
import GoLeanProofs.Specs.Raft.SeedPin

/-! A4-U26: #eval-first checks for the abstract EStep witness chain
(seedN₀ → campaign(1) → recvVote(2 grants 1) → selfResp → winning
resp), before any `decide`/`rfl` is asked of the kernel. -/

open GoLean.RaftSeam GoLean.RaftSeam.NativeSpec

def voters3 : List Nat := [1, 2, 3]

def absN0 : SNet := seedN₀
def absN1 : SNet :=
  updNode absN0 1 (specBecomeCandidate (absN0.node 1) 1)
    (pushVote absN0.ghost 1 ((absN0.node 1).term + 1) 1)

-- the recvVote spec computation at node 2
#eval specRecvVote (absN1.node 2) 1 1 1 1
-- expected: ({state 0, term 1, vote 1, lead 0, log [(1,1)], committed 1, votesRec []}, true)

def r2' : ENode :=
  { state := 0, term := 1, vote := 1, lead := 0, log := [(1, 1)],
    committed := 1, votesRec := [] }
#eval (specRecvVote (absN1.node 2) 1 1 1 1 == (r2', true))

def absN2 : SNet := updNode absN1 2 r2' (pushVote absN1.ghost 2 1 1)

-- self-resp at node 1
#eval specRecvVoteResp (absN2.node 1) 1 voters3 1 false
def r3' : ENode :=
  { state := 1, term := 1, vote := 1, lead := 0, log := [(1, 1)],
    committed := 1, votesRec := [(1, true)] }
#eval (specRecvVoteResp (absN2.node 1) 1 voters3 1 false == (r3', false))

def absN3 : SNet := updNode absN2 1 r3' absN2.ghost

-- the winning resp at node 1
#eval specRecvVoteResp (absN3.node 1) 1 voters3 2 false
def r4' : ENode :=
  { state := 2, term := 1, vote := 1, lead := 1, log := [(2, 1), (1, 1)],
    committed := 1, votesRec := [] }
#eval (specRecvVoteResp (absN3.node 1) 1 voters3 2 false == (r4', true))

-- ghost membership facts (the hgen/faithful premises)
#eval decide (((absN2.node 1).term, 1) ∈ absN2.ghost.votes 1)
#eval decide (((absN3.node 1).term, 1) ∈ absN3.ghost.votes 2)
#eval absN3.ghost.votes 1
#eval absN3.ghost.votes 2
#eval (grantedOf (recordVote (absN3.node 1).votesRec 2 true))
-- TallyOK components
#eval decide ((((absN2.node 1).votesRec).map Prod.fst).Nodup)
#eval decide ((((absN3.node 1).votesRec).map Prod.fst).Nodup)
-- the leader non-vacuity at the end
def absN4 : SNet :=
  updNode absN3 1 r4'
    (pushVictory absN3.ghost (absN3.node 1).term 1
      (grantedOf (recordVote (absN3.node 1).votesRec 2 true)))
#eval (absN4.node 1).state
#eval absN4.ghost.victories
