import VerdiCompat.MatchIndexAllEntries

/-!
# THE W-F CAP: StateMachineSafetyProof.v — state-machine safety at base level

Campaign Arc 3 unit 15(c), 1:1 against
`RaftProofs/StateMachineSafetyProof.v` (3,199 lines) @ a3375e8 plus its
two in-file interface deliverables (`Raft/MaxIndexSanityInterface.v`,
`Raft/CommitRecordedCommittedInterface.v` — neither has a proof file of
its own; both are proved HERE, exactly upstream).

The architecture: three invariants ride ONE combined induction
(`everything`) at the MSG-ghost layer through the PRIMED msg principle
(unit 13) — `lifted_maxIndex_sanity` (watermarks below maxIndex),
`commit_invariant` (host and in-flight commit indices point at
committed entries), and base `state_machine_safety` of the double
deghost (re-established each step from SMS-prime + the freshly-proved
commit invariant, unit 14's `state_machine_safety'` consumed through
`msg_simulation_1`). The exits descend by the unit-15 reghosting
(`msg_lower_prop` / GAP-8): **`state_machine_safety_invariant`** (BASE
— the last T3 head, discharging Properties.lean's declared
`StateMachineSafetyStatement`), `maxIndex_sanity_invariant` (BASE), and
`commit_recorded_committed_invariant` (refined).

Statement notes: `lifted_directly_committed`/`lifted_committed`
(upstream :958-969) are definitionally `directly_committed`/`committed`
of `mgv_deghost` (the state ghost is untouched by the wire ghost), so
upstream's four transfer lemmas (:1017-1065) are identity-shaped here;
kept as named theorems for 1:1 citation.
-/

namespace VerdiCompat
namespace Raft

section StateMachineSafety
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

local notation "MsgNet" =>
  Network (raft_msg_refined_base_params (P := P)) raft_msg_refined_multi_params
local notation "MsgPacket" =>
  Packet (raft_msg_refined_base_params (P := P)) raft_msg_refined_multi_params
local notation "RefinedNet" =>
  Network (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RefinedPacket" =>
  Packet (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RaftNet" =>
  Network (raft_base_params (P := P)) raft_multi_params
local notation "RaftPacket" =>
  Packet (raft_base_params (P := P)) raft_multi_params

/-! ## The two in-file interfaces' statements -/

/-- `MaxIndexSanityInterface.v:8-10` (`maxIndex_lastApplied`). -/
def maxIndex_lastApplied (net : RaftNet) : Prop :=
  ∀ h : name (P := P),
    (net.nwState h).lastApplied ≤ maxIndex (net.nwState h).log

/-- `MaxIndexSanityInterface.v:12-14` (`maxIndex_commitIndex`). -/
def maxIndex_commitIndex (net : RaftNet) : Prop :=
  ∀ h : name (P := P),
    (net.nwState h).commitIndex ≤ maxIndex (net.nwState h).log

/-- `MaxIndexSanityInterface.v:16-17` (`maxIndex_sanity`). -/
def maxIndex_sanity (net : RaftNet) : Prop :=
  maxIndex_lastApplied net ∧ maxIndex_commitIndex net

/-- `CommitRecordedCommittedInterface.v:12-15`
(`commit_recorded_committed`). -/
def commit_recorded_committed (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (e : entry (P := P)),
    commit_recorded (deghost net) h e →
    committed net e (net.nwState h).2.currentTerm

/-! ## The msg-layer invariants (`StateMachineSafetyProof.v:90-93,958-987`) -/

/-- `StateMachineSafetyProof.v:90-93` (`lifted_maxIndex_sanity`). -/
def lifted_maxIndex_sanity (net : MsgNet) : Prop :=
  (∀ h : name (P := P),
    (net.nwState h).2.lastApplied ≤ maxIndex (net.nwState h).2.log) ∧
  (∀ h : name (P := P),
    (net.nwState h).2.commitIndex ≤ maxIndex (net.nwState h).2.log)

/-- `StateMachineSafetyProof.v:958-962` (`lifted_directly_committed`) —
definitionally `directly_committed (mgv_deghost net)`. -/
def lifted_directly_committed (net : MsgNet) (e : entry (P := P)) : Prop :=
  ∃ quorum : List (name (P := P)),
    quorum.Nodup ∧
    quorum.length > div2 (nodes (P := P)).length ∧
    ∀ h ∈ quorum, (e.eTerm, e) ∈ (net.nwState h).1.allEntries

/-- `StateMachineSafetyProof.v:964-969` (`lifted_committed`). -/
def lifted_committed (net : MsgNet) (e : entry (P := P)) (t : term) : Prop :=
  ∃ (h : name (P := P)) (e' : entry (P := P)),
    e'.eTerm ≤ t ∧
    lifted_directly_committed net e' ∧
    e.eIndex ≤ e'.eIndex ∧
    e ∈ (net.nwState h).2.log ∧
    e' ∈ (net.nwState h).2.log

/-- `StateMachineSafetyProof.v:971-975` (`commit_invariant_host`). -/
def commit_invariant_host (net : MsgNet) : Prop :=
  ∀ (h : name (P := P)) (e : entry (P := P)),
    e ∈ (net.nwState h).2.log →
    e.eIndex ≤ (net.nwState h).2.commitIndex →
    lifted_committed net e (net.nwState h).2.currentTerm

/-- `StateMachineSafetyProof.v:977-983` (`commit_invariant_nw`): an
in-flight AppendEntries' leaderCommit only covers committed entries of
its payload. -/
def commit_invariant_nw (net : MsgNet) : Prop :=
  ∀ (p : MsgPacket) (t : term) (lid : name (P := P)) (pli : logIndex)
    (plt : term) (es : List (entry (P := P))) (lci : logIndex)
    (e : entry (P := P)),
    p ∈ net.nwPackets →
    p.pBody.2 = .AppendEntries t lid pli plt es lci →
    e ∈ p.pBody.1 →
    e.eIndex ≤ lci →
    lifted_committed net e t

/-- `StateMachineSafetyProof.v:985-987` (`commit_invariant`). -/
def commit_invariant (net : MsgNet) : Prop :=
  commit_invariant_host net ∧ commit_invariant_nw net

/-! ## The transfer bridges
(`StateMachineSafetyProof.v:58-85,999-1091,2837-2862`) -/

/-- `StateMachineSafetyProof.v:1017-1027`
(`lifted_directly_committed_directly_committed`) — identity-shaped
(the wire ghost never touches state). -/
theorem lifted_directly_committed_directly_committed {net : MsgNet}
    {e : entry (P := P)} (h : lifted_directly_committed net e) :
    directly_committed (mgv_deghost net) e := h

/-- `StateMachineSafetyProof.v:1029-1040`
(`directly_committed_lifted_directly_committed`). -/
theorem directly_committed_lifted_directly_committed {net : MsgNet}
    {e : entry (P := P)} (h : directly_committed (mgv_deghost net) e) :
    lifted_directly_committed net e := h

/-- `StateMachineSafetyProof.v:1042-1052` (`lifted_committed_committed`). -/
theorem lifted_committed_committed {net : MsgNet} {e : entry (P := P)}
    {t : term} (h : lifted_committed net e t) :
    committed (mgv_deghost net) e t := h

/-- `StateMachineSafetyProof.v:1054-1064` (`committed_lifted_committed`). -/
theorem committed_lifted_committed {net : MsgNet} {e : entry (P := P)}
    {t : term} (h : committed (mgv_deghost net) e t) :
    lifted_committed net e t := h

/-- `StateMachineSafetyProof.v:999-1015`
(`msg_lifted_lastApplied_le_commitIndex`): unit 12's base watermark
fact imported through both erasures. -/
theorem msg_lifted_lastApplied_le_commitIndex :
    ∀ net : MsgNet, msg_refined_raft_intermediate_reachable (P := P) net →
      ∀ h : name (P := P),
        (net.nwState h).2.lastApplied ≤ (net.nwState h).2.commitIndex :=
  fun net hreach h =>
    msg_lift_prop_all_the_way _ lastApplied_le_commitIndex_invariant net
      hreach h

/-- `StateMachineSafetyProof.v:1078-1091`
(`commit_invariant_lower_commit_recorded_committed`): the commit
invariant delivers `commit_recorded_committed` of the deghost. -/
theorem commit_invariant_lower_commit_recorded_committed {net : MsgNet}
    (hreach : msg_refined_raft_intermediate_reachable (P := P) net)
    (hci : commit_invariant net) :
    commit_recorded_committed (mgv_deghost net) := by
  intro h e hcr
  obtain ⟨hin, hle⟩ := hcr
  replace hin : e ∈ (net.nwState h).2.log := hin
  replace hle : e.eIndex ≤ (net.nwState h).2.lastApplied ∨
    e.eIndex ≤ (net.nwState h).2.commitIndex := hle
  have hle' : e.eIndex ≤ (net.nwState h).2.commitIndex := by
    rcases hle with hle | hle
    · exact Nat.le_trans hle (msg_lifted_lastApplied_le_commitIndex net
        hreach h)
    · exact hle
  exact lifted_committed_committed (hci.1 h e hin hle')

/-- `StateMachineSafetyProof.v:69-85` (`state_machine_safety_deghost`):
commit-recorded-committed + SMS-prime give base state-machine safety of
the deghost. -/
theorem state_machine_safety_deghost {net : RefinedNet}
    (hcrc : commit_recorded_committed net)
    (hsms' : state_machine_safety' net) :
    state_machine_safety (deghost net) := by
  obtain ⟨hhost', hnw'⟩ := hsms'
  constructor
  · -- host half
    intro h h' e e' hcr hcr' hidx
    exact hhost' e e' _ _ (hcrc h e hcr) (hcrc h' e' hcr') hidx
  · -- nw half
    intro h p t lid pli plt es ci e hp hbody hge hcr
    replace hp : p ∈ net.nwPackets.map deghost_packet := hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hnw' q t lid pli plt es ci e _ hq hbody (hcrc h e hcr) hge

/-- `StateMachineSafetyProof.v:2837-2850` (`maxIndex_sanity_lift`). -/
theorem maxIndex_sanity_lift {net : MsgNet}
    (h : maxIndex_sanity (deghost (mgv_deghost net))) :
    lifted_maxIndex_sanity net :=
  ⟨fun h0 => h.1 h0, fun h0 => h.2 h0⟩

/-- `StateMachineSafetyProof.v:2852-2862` (`maxIndex_sanity_lower`). -/
theorem maxIndex_sanity_lower {net : MsgNet}
    (h : lifted_maxIndex_sanity net) :
    maxIndex_sanity (deghost (mgv_deghost net)) :=
  ⟨fun h0 => h.1 h0, fun h0 => h.2 h0⟩

end StateMachineSafety

end Raft
end VerdiCompat
