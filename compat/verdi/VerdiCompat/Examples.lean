import VerdiCompat.Raft

/-!
# Non-vacuity witness: the spec instantiates and runs

Mirrors the repo's witness doctrine: a spec port is a scaffold until a
concrete instantiation exercises it. Instantiates the Raft spec with a
trivial replicated counter (verdi-raft's own example is the VarD
key-value store, `theories/Systems/VarDRaft.v:8-19` — same shape, more
fields) at N = 3 and checks handler executions by `rfl` (kernel
reduction; no `native_decide`, per repo doctrine).
-/

namespace VerdiCompat.Examples

open VerdiCompat.Raft

/-- A counter state machine: input = increment amount, output = new total. -/
@[reducible] def counterBase : BaseParams where
  data := Nat
  input := Nat
  output := Nat

instance : OneNodeParams counterBase where
  init := show Nat from 0
  handler := fun (i d : Nat) => (d + i, d + i)

instance : RaftParams counterBase where
  N := 3
  input_eq_dec := show DecidableEq Nat from inferInstance
  output_eq_dec := show DecidableEq Nat from inferInstance
  clientId := Nat
  clientId_eq_dec := inferInstance

abbrev node0 : name (P := counterBase) := ⟨0, by decide⟩

/-- A fresh node that times out becomes a candidate in term 1... -/
example :
    ((RaftInputHandler node0 .Timeout (init_handlers node0)).2.1).currentTerm = 1 ∧
    ((RaftInputHandler node0 .Timeout (init_handlers node0)).2.1).type = .Candidate := by
  exact ⟨rfl, rfl⟩

/-- ...and solicits votes from exactly the two other nodes. -/
example :
    ((RaftInputHandler node0 .Timeout (init_handlers node0)).2.2).map Prod.fst
      = [⟨1, by decide⟩, ⟨2, by decide⟩] := rfl

/-- A follower grants a first-contact RequestVote and records the vote. -/
example :
    (handleRequestVote node0 (init_handlers node0) 1 ⟨1, by decide⟩ 0 0).1.votedFor
      = some ⟨1, by decide⟩ := rfl

/-- Elections need a strict majority: 2 of 3 wins, 1 of 3 does not. -/
example : wonElection (P := counterBase) [⟨0, by decide⟩, ⟨1, by decide⟩] = true := rfl
example : wonElection (P := counterBase) [⟨0, by decide⟩] = false := rfl

end VerdiCompat.Examples
