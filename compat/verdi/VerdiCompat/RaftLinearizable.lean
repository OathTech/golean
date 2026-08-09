import VerdiCompat.Raft
import VerdiCompat.CommonDefinitions
import VerdiCompat.Linearizability

/-!
# verdi-raft's linearizability glue + the headline transfer target

1:1 port of the raft-side statement vocabulary of the end-to-end
linearizability theorem: `deps/verdi-raft/theories/Raft/`
`RaftLinearizableProofs.v:26-95` (`import`/`exported`/`get_input`/
`get_output`), `:261-270` (`log_to_IR`, the linearization witness the
proof exhibits), `:994-998` (`input_correct`), and the theorem statement
itself (`RaftProofs/EndToEndLinearizability.v:471-478`, =
`raft_linearizable'` at `RaftLinearizableProofs.v:1056-1064`) as the
named transfer target `RaftLinearizableStatement`.

Per design-note §4d this client-observable statement is the intended
DURABLE top-level theorem shape: its text mentions traces and the
replicated machine only, so it survives every extension ring including
snapshots.

Trace elements are `name × (raft_input ⊕ List raft_output)` — exactly
`NetTrace raft_base_params raft_multi_params`, the external-I/O-only
observation type of the ported `step_failure`.
-/

namespace VerdiCompat
namespace Raft

section RaftLinearizable
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

/-- The raft network-trace element type (spelled out; defeq to
`NetTrace (raft_base_params (P := P)) raft_multi_params`). -/
abbrev RaftTraceElt :=
  name (P := P) × (raft_input (P := P) ⊕ List (raft_output (P := P)))

/-- `RaftLinearizableProofs.v:26-41`, Coq `import` — project a network
trace onto client-visible operations: each first request occurrence
keyed `(client, id)` becomes `I`, each first response occurrence `O`;
later duplicates are removed (Coq `List.remove`/StructTact `remove_all`
= `removeAll`/`removeList`). RENAMED: `import` is a Lean 4 keyword
(lane-log delta 1). -/
def importTrace : List (RaftTraceElt (P := P)) → List (op (key (P := P)))
  | [] => []
  | (_, .inl (.ClientRequest c id _)) :: xs =>
    .I (c, id) :: removeAll (.I (c, id)) (importTrace xs)
  | (_, .inr l) :: xs =>
    let os := dedup (filterMap (fun x =>
      match x with
      | .ClientResponse c id _ => some (op.O (c, id))
      | _ => none) l)
    os ++ removeList os (importTrace xs)
  | _ :: xs => importTrace xs

/-- `RaftLinearizableProofs.v:44-56`. NOTE the `IU` case binds an output
`o` that is never constrained — verbatim from the source, not cleaned up
(lane-log delta 5): an unacknowledged request pairs with an arbitrary
output in the exported sequential trace. -/
inductive exported (env_i : key (P := P) → Option P.input)
    (env_o : key (P := P) → Option P.output) :
    List (IR (key (P := P))) → List (P.input × P.output) → Prop where
  | exported_nil : exported env_i env_o [] []
  | exported_IO : ∀ k i o l tr,
      env_i k = some i →
      env_o k = some o →
      exported env_i env_o l tr →
      exported env_i env_o (.IRI k :: .IRO k :: l) ((i, o) :: tr)
  | exported_IU : ∀ k i o l tr,
      env_i k = some i →
      exported env_i env_o l tr →
      exported env_i env_o (.IRI k :: .IRU k :: l) ((i, o) :: tr)

/-- `RaftLinearizableProofs.v:59-71` (`sumbool_and` → decidable `∧`,
lane-log delta 3). -/
def get_input : List (RaftTraceElt (P := P)) → key (P := P) → Option P.input
  | [], _ => none
  | (_, .inl (.ClientRequest c id cmd)) :: xs, k =>
    if c = k.1 ∧ id = k.2 then some cmd else get_input xs k
  | _ :: xs, k => get_input xs k

/-- `RaftLinearizableProofs.v:73-84` -/
def get_output' : List (raft_output (P := P)) → key (P := P) → Option P.output
  | [], _ => none
  | .ClientResponse c id o :: xs, k =>
    if c = k.1 ∧ id = k.2 then some o else get_output' xs k
  | _ :: xs, k => get_output' xs k

/-- `RaftLinearizableProofs.v:86-95` -/
def get_output : List (RaftTraceElt (P := P)) → key (P := P) → Option P.output
  | [], _ => none
  | (_, .inr os) :: xs, k =>
    (match get_output' os k with
     | some o => some o
     | none => get_output xs k)
  | _ :: xs, k => get_output xs k

/-- `RaftLinearizableProofs.v:261-270` — the linearization the proof
exhibits: read IR pairs off a (deduplicated) log, `IRO` when a response
for the key surfaced, `IRU` otherwise. -/
def log_to_IR (env_o : key (P := P) → Option P.output) :
    List (entry (P := P)) → List (IR (key (P := P)))
  | [] => []
  | ⟨_, client, id, _, _, _⟩ :: log' =>
    (match env_o (client, id) with
     | none => [.IRI (client, id), .IRU (client, id)]
     | some _ => [.IRI (client, id), .IRO (client, id)]) ++
    log_to_IR env_o log'

/-- `RaftLinearizableProofs.v:994-998` — the side condition of the
headline theorem: a `(client, id)` key is never reused for two different
commands anywhere in the trace. -/
def input_correct (tr : List (RaftTraceElt (P := P))) : Prop :=
  ∀ client id i i' h h',
    (h, .inl (.ClientRequest client id i)) ∈ tr →
    (h', .inl (.ClientRequest client id i')) ∈ tr →
    i = i'

end RaftLinearizable

/-- The headline transfer target, `EndToEndLinearizability.v:471-478`
(statement identical to `raft_linearizable'`,
`RaftLinearizableProofs.v:1056-1064`, whose interface hypotheses the
end-to-end proof discharges): every `step_failure` trace of the Raft
network with well-formed client keys is, after acknowledgment, equivalent
to an exported run of the SEQUENTIAL replicated machine (`step_1_star`).
What Verdi PROVED (≈37k lines we do not port); re-establishing it in
Lean — by P2 certificate transfer or native re-proof — is the compat
layer's client-observable endgame (design note §4d/§4e). -/
def RaftLinearizableStatement (P : BaseParams) [O : OneNodeParams P]
    [R : RaftParams P] : Prop :=
  ∀ failed net tr,
    input_correct tr →
    step_failure_star (raft_base_params (P := P)) raft_multi_params
      raft_failure_params (step_failure_init _ _) (failed, net) tr →
    ∃ ir tr1 st,
      equivalent (importTrace tr) ir ∧
      exported (get_input tr) (get_output tr) ir tr1 ∧
      step_1_star P O O.init st tr1

end Raft
end VerdiCompat
