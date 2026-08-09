import VerdiCompat.Raft

/-!
# verdi-raft's common statement vocabulary (slice)

1:1 port of the slice of `deps/verdi-raft/theories/Raft/CommonDefinitions.v`
needed to STATE the headline safety properties (`commit_recorded` and the
predicates the log-matching statement uses). The linearizability vocabulary
(`execute_log`, `deduplicate_log`, `applied_entries`, …) is a recorded P1
follow-up, not yet ported.
-/

namespace VerdiCompat
namespace Raft

section CommonDefs
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

/-- `CommonDefinitions.v:8-15` -/
def entries_match (entries entries' : List (entry (P := P))) : Prop :=
  ∀ e e' e'',
    e.eIndex = e'.eIndex →
    e.eTerm = e'.eTerm →
    e ∈ entries →
    e' ∈ entries' →
    e''.eIndex ≤ e.eIndex →
    (e'' ∈ entries ↔ e'' ∈ entries')

/-- `CommonDefinitions.v:17-25` (the newest-first log invariant shape) -/
def sorted : List (entry (P := P)) → Prop
  | [] => True
  | e :: es =>
    (∀ e', e' ∈ es → e.eIndex > e'.eIndex ∧ e.eTerm ≥ e'.eTerm) ∧ sorted es

/-- `CommonDefinitions.v:58-59` -/
def uniqueIndices (xs : List (entry (P := P))) : Prop :=
  (xs.map entry.eIndex).Nodup

/-- `CommonDefinitions.v:102-105` — "node `h` has committed entry `e`":
it is in `h`'s log at or below `h`'s applied/commit watermark. -/
def commit_recorded (net : Network (raft_base_params (P := P)) raft_multi_params)
    (h : name (P := P)) (e : entry (P := P)) : Prop :=
  e ∈ (net.nwState h).log ∧
  (e.eIndex ≤ (net.nwState h).lastApplied ∨
   e.eIndex ≤ (net.nwState h).commitIndex)

/-- `CommonDefinitions.v:124-127` -/
def terms_and_indices_from_one (l : List (entry (P := P))) : Prop :=
  ∀ e, e ∈ l → e.eTerm ≥ 1 ∧ e.eIndex ≥ 1

end CommonDefs

end Raft
end VerdiCompat
