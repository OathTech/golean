import VerdiCompat.Raft
import VerdiCompat.RaftLinearizable

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

/-!
## Linearizability-vocabulary witnesses (P1)

A tiny concrete network trace — client 7 submits request id 1 with input
5 and the response 5 surfaces — exercised through every component of the
headline statement (`RaftLinearizableStatement`). SCOPE, honestly: these
witness that each definition COMPUTES and that the statement's
conclusion is constructible for a trace of the right shape; they do NOT
derive the trace from a `step_failure_star` run (that takes an
election + replication + commit schedule — the differential harness's
territory computationally, and the transfer proof's territory formally).
-/

/-- One request, one response, keyed `(7, 1)`. (Literals are ascribed
`: Nat` because typeclass-projected types like
`RaftParams.clientId counterBase` don't reduce during `OfNat` instance
search, though they are defeq to `Nat`.) -/
def linTrace : List (RaftTraceElt (P := counterBase)) :=
  [(node0, .inl (.ClientRequest (7 : Nat) 1 (5 : Nat))),
   (node0, .inr [.ClientResponse (7 : Nat) 1 (5 : Nat)])]

/-- `importTrace` projects it onto the operation alphabet. -/
example : importTrace linTrace = [.I ((7 : Nat), 1), .O ((7 : Nat), 1)] := rfl

/-- The environments read back the request's input and output. -/
example : get_input linTrace ((7 : Nat), 1) = some (5 : Nat) := rfl
example : get_output linTrace ((7 : Nat), 1) = some (5 : Nat) := rfl

/-- `log_to_IR` on a one-entry log with the response surfaced. -/
example :
    log_to_IR (get_output linTrace) [⟨node0, (7 : Nat), 1, 1, 1, (5 : Nat)⟩]
      = [.IRI ((7 : Nat), 1), .IRO ((7 : Nat), 1)] := rfl

/-- The trace satisfies the headline theorem's side condition. -/
example : input_correct linTrace := by
  intro client id i i' h h' hin hin'
  simp only [linTrace, List.mem_cons, List.not_mem_nil, or_false] at hin hin'
  rcases hin with h1 | h1 <;> rcases hin' with h2 | h2 <;>
    simp_all

/-- The conclusion of `RaftLinearizableStatement`, inhabited at
`linTrace`: linearization `[IRI, IRO]`, exported sequential trace
`[(5, 5)]`, final machine state `5`. -/
theorem raft_linearizable_conclusion_witness :
    ∃ ir tr1 st,
      equivalent (importTrace linTrace) ir ∧
      exported (get_input linTrace) (get_output linTrace) ir tr1 ∧
      step_1_star counterBase inferInstance (0 : Nat) st tr1 := by
  refine ⟨[.IRI ((7 : Nat), 1), .IRO ((7 : Nat), 1)], [((5 : Nat), (5 : Nat))], (5 : Nat),
    -- equivalent: good_trace ∧ an acknowledgment reaching the IR list
    ⟨⟨rfl, trivial⟩,
     [.IRI ((7 : Nat), 1), .IRO ((7 : Nat), 1)],
     .AAO_IO _ _ _ (List.Mem.head _) (.AAO_O _ _ _ .AAO_nil),
     IR_equivalent_refl _⟩,
    -- exported: the IO pair reads its input/output from the trace
    ?_,
    -- step_1_star: one deliver step of the counter machine, 0 --5/5--> 5
    ?_⟩
  · refine .exported_IO _ _ _ _ _ ?_ ?_ .exported_nil <;> rfl
  · refine .RT1nTStep (0 : Nat) (5 : Nat) (5 : Nat)
      [((5 : Nat), (5 : Nat))] [] ?_ (.RT1nTBase (5 : Nat))
    refine .S1T_deliver _ _ _ _ ?_
    rfl

end VerdiCompat.Examples
