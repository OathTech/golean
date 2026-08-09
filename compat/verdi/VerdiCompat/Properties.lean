import VerdiCompat.CommonDefinitions

/-!
# The consensus property statements, in Lean

1:1 ports of verdi-raft's ghost-free headline property STATEMENTS — the
formal answer to "is the statement of the consensus property over Raft the
same as ours": these are now Lean `Prop`s over the ported spec, inspectable
side-by-side with anything golean states. All three are invariants of
`raft_intermediate_reachable` in Verdi (proved there over ~37k lines of
Rocq we do not port); here they are stated as named transfer targets, house
style (`def … : Prop` before machinery).

Sources: `OneLeaderPerTermInterface.v`, `LogMatchingInterface.v`,
`StateMachineSafetyInterface.v`. Leader completeness is NOT here — its
statement needs the ghost/refinement layer (recorded gap).
-/

namespace VerdiCompat
namespace Raft

section Properties
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

/-- Election safety, `OneLeaderPerTermInterface.v:8-13`: at most one leader
per term. -/
def one_leader_per_term (net : Network (raft_base_params (P := P)) raft_multi_params) : Prop :=
  ∀ h h' : name (P := P),
    (net.nwState h).currentTerm = (net.nwState h').currentTerm →
    (net.nwState h).type = .Leader →
    (net.nwState h').type = .Leader →
    h = h'

/-- `LogMatchingInterface.v:9-18` -/
def log_matching_hosts (net : Network (raft_base_params (P := P)) raft_multi_params) : Prop :=
  (∀ h h' : name (P := P),
    entries_match (net.nwState h).log (net.nwState h').log) ∧
  (∀ (h : name (P := P)) i,
    1 ≤ i ∧ i ≤ maxIndex (net.nwState h).log →
    ∃ e, entry.eIndex e = i ∧ e ∈ (net.nwState h).log) ∧
  (∀ (h : name (P := P)) e,
    e ∈ (net.nwState h).log → entry.eIndex e > 0)

/-- `LogMatchingInterface.v:20-62` — the in-flight `AppendEntries` half of
log matching. -/
def log_matching_nw (net : Network (raft_base_params (P := P)) raft_multi_params) : Prop :=
  ∀ p t leaderId prevLogIndex prevLogTerm entries leaderCommit,
    p ∈ net.nwPackets →
    p.pBody = .AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit →
    (∀ (h : name (P := P)) e1 e2,
      e1 ∈ entries →
      e2 ∈ (net.nwState h).log →
      entry.eIndex e1 = entry.eIndex e2 →
      entry.eTerm e1 = entry.eTerm e2 →
      (∀ e3, entry.eIndex e3 ≤ entry.eIndex e1 → e3 ∈ entries →
        e3 ∈ (net.nwState h).log) ∧
      (prevLogIndex ≠ 0 →
        ∃ e4, entry.eIndex e4 = prevLogIndex ∧ entry.eTerm e4 = prevLogTerm ∧
          e4 ∈ (net.nwState h).log)) ∧
    (∀ i, prevLogIndex < i ∧ i ≤ maxIndex entries →
      ∃ e, entry.eIndex e = i ∧ e ∈ entries) ∧
    (∀ e, e ∈ entries → prevLogIndex < entry.eIndex e) ∧
    (∀ p' t' leaderId' prevLogIndex' prevLogTerm' entries' leaderCommit',
      p' ∈ net.nwPackets →
      p'.pBody = .AppendEntries t' leaderId' prevLogIndex' prevLogTerm' entries' leaderCommit' →
      (∀ e1 e2,
        e1 ∈ entries →
        e2 ∈ entries' →
        entry.eIndex e1 = entry.eIndex e2 →
        entry.eTerm e1 = entry.eTerm e2 →
        (∀ e3, prevLogIndex' < entry.eIndex e3 ∧ entry.eIndex e3 ≤ entry.eIndex e1 →
          e3 ∈ entries → e3 ∈ entries') ∧
        (∀ e3, e3 ∈ entries → entry.eIndex e3 = prevLogIndex' →
          entry.eTerm e3 = prevLogTerm') ∧
        (prevLogIndex ≠ 0 → prevLogIndex = prevLogIndex' → prevLogTerm = prevLogTerm')))

/-- `LogMatchingInterface.v:64-65` -/
def log_matching (net : Network (raft_base_params (P := P)) raft_multi_params) : Prop :=
  log_matching_hosts net ∧ log_matching_nw net

/-- State machine safety (host half), `StateMachineSafetyInterface.v:8-13`:
committed entries agree — THE consensus property. -/
def state_machine_safety_host
    (net : Network (raft_base_params (P := P)) raft_multi_params) : Prop :=
  ∀ (h h' : name (P := P)) e e',
    commit_recorded net h e →
    commit_recorded net h' e' →
    entry.eIndex e = entry.eIndex e' →
    e = e'

/-- `StateMachineSafetyInterface.v:15-25` -/
def state_machine_safety_nw
    (net : Network (raft_base_params (P := P)) raft_multi_params) : Prop :=
  ∀ (h : name (P := P)) p t leaderId prevLogIndex prevLogTerm entries leaderCommit e,
    p ∈ net.nwPackets →
    p.pBody = .AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit →
    t ≥ (net.nwState h).currentTerm →
    commit_recorded net h e →
    (prevLogIndex > entry.eIndex e ∨
     (prevLogIndex = entry.eIndex e ∧ prevLogTerm = entry.eTerm e) ∨
     entry.eIndex e > maxIndex entries ∨
     e ∈ entries)

/-- `StateMachineSafetyInterface.v:27-28` -/
def state_machine_safety
    (net : Network (raft_base_params (P := P)) raft_multi_params) : Prop :=
  state_machine_safety_host net ∧ state_machine_safety_nw net

/-- The transfer target (`StateMachineSafetyInterface.v:30-36`, class form
flattened): what Verdi PROVED, stated over the ported spec. Re-establishing
this in Lean — by transport (P2 certificate) or native re-proof over the
extended model — is the compat layer's endgame. -/
def StateMachineSafetyStatement (P : BaseParams) [OneNodeParams P] [RaftParams P] : Prop :=
  ∀ net, raft_intermediate_reachable (P := P) net → state_machine_safety net

/-- Ditto for election safety (`OneLeaderPerTermInterface.v:15-20`). -/
def OneLeaderPerTermStatement (P : BaseParams) [OneNodeParams P] [RaftParams P] : Prop :=
  ∀ net, raft_intermediate_reachable (P := P) net → one_leader_per_term net

/-- Ditto for log matching (`LogMatchingInterface.v:67-73`). -/
def LogMatchingStatement (P : BaseParams) [OneNodeParams P] [RaftParams P] : Prop :=
  ∀ net, raft_intermediate_reachable (P := P) net → log_matching net

end Properties

end Raft
end VerdiCompat
