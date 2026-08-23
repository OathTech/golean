import VerdiCompat.LeaderCompleteness

/-!
# GAP-2 — the msg-ghost layer (`RaftMsgRefinementInterface.v`)

Campaign Arc 3 unit 11 (closure + scope in the arc log's unit-11
opening entry), 1:1 against the sources @ a3375e8:

- the per-PACKET ghost vocabulary (`ghost_log`, `write_ghost_log`,
  `add_ghost_msg`) — Verdi's generic `MsgGhostMultiParams`/`mgv_*`
  construction (`GhostSimulations.v:298-377`) inlined at its raft
  `ghost_log` instance, the same D1 design call as the state-ghost
  layer (`RefinedProofStructure.lean`);
- the msg-refined parameter triple and
  `msg_refined_raft_intermediate_reachable`
  (`RaftMsgRefinementInterface.v:19-79`);
- the ELEVEN obligation shapes (`:83-195`), the dispatchers, and THE
  principle `msg_refined_raft_net_invariant`
  (`RaftProofs/RaftMsgRefinementProof.v:12-275`);
- the erasure half of the transfer: `mgv_deghost`,
  `mgv_ghost_simulation_1`, `msg_simulation_1` (`Proof.v:566-645`),
  `msg_lift_prop` (`:646-654`), `msg_deghost_spec` (`:908-917`);
- the §3.3 discharge witness `ghost_entries_gt_0`.

DEFERRED (unit-11 scope call, logged with the consumer census): the
PRIMED obligation set + `msg_refined_raft_net_invariant'`
(`Interface :197-439`, `Proof :276-565`) and the reghosting direction
(`simulation_2`/`msg_lower_prop`/`_all_the_way`, `Proof :655-940`) —
first needed at the W-F cap.

The KEY semantic point of this layer (why SMS needs it): every message
carries as ghost the SENDER's log at send time, giving in-flight
AppendEntries a full-log context that the entries alone lack.
-/

namespace VerdiCompat
namespace Raft

section MsgRefinement
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

/-- `RaftMsgRefinementInterface.v:9` (`ghost_log`): the per-packet
ghost — a full log. -/
abbrev ghost_log := List (entry (P := P))

/-- `RaftMsgRefinementInterface.v:17` (`write_ghost_log`): the ghost
written on every send is the sender's (post-step) log. -/
def write_ghost_log (_h : name (P := P))
    (st : electionsData (P := P) × raft_data (P := P)) :
    ghost_log (P := P) :=
  st.2.log

/-- `GhostSimulations.v:314-316` (`add_ghost_msg`) at the raft
instance. -/
def add_ghost_msg (me : name (P := P))
    (st : electionsData (P := P) × raft_data (P := P))
    (ps : List (name (P := P) × msg (P := P))) :
    List (name (P := P) × (ghost_log (P := P) × msg (P := P))) :=
  ps.map fun m => (m.1, (write_ghost_log me st, m.2))

/-- `add_ghost_msg` distributes over append. -/
theorem add_ghost_msg_app (me : name (P := P))
    (st : electionsData (P := P) × raft_data (P := P))
    (l₁ l₂ : List (name (P := P) × msg (P := P))) :
    add_ghost_msg me st (l₁ ++ l₂)
      = add_ghost_msg me st l₁ ++ add_ghost_msg me st l₂ :=
  List.map_append ..

/-- The ghost value depends only on the state's log: states with equal
logs attach equal ghosts (the reconciliation fact behind the principle's
staged decomposition — `doLeader`/`doGenericServer` never move the log,
so the per-stage ghosts coincide with the handler's single final
write). -/
theorem add_ghost_msg_log_eq {me : name (P := P)}
    {st st' : electionsData (P := P) × raft_data (P := P)}
    (h : st.2.log = st'.2.log)
    (ps : List (name (P := P) × msg (P := P))) :
    add_ghost_msg me st ps = add_ghost_msg me st' ps := by
  unfold add_ghost_msg write_ghost_log
  rw [h]

/-- `GhostSimulations.v:333-338` + `RaftMsgRefinementInterface.v:26`
(`raft_msg_refined_base_params` = `mgv_refined_base_params`): the state
is the refined state unchanged; only the wire type changes. -/
@[reducible] def raft_msg_refined_base_params : BaseParams where
  data := electionsData (P := P) × raft_data (P := P)
  input := raft_input (P := P)
  output := raft_output (P := P)

/-- `GhostSimulations.v:318-320` (`mgv_refined_net_handlers`) at the
instance: run the refined handler on the underlying message, then
attach the post-state ghost to every send. -/
def mgv_refined_net_handlers (me src : name (P := P))
    (m : ghost_log (P := P) × msg (P := P))
    (st : electionsData (P := P) × raft_data (P := P)) :
    List (raft_output (P := P)) ×
      (electionsData (P := P) × raft_data (P := P)) ×
      List (name (P := P) × (ghost_log (P := P) × msg (P := P))) :=
  let (out, st', ps) := refined_net_handlers me src m.2 st
  (out, st', add_ghost_msg me st' ps)

/-- `GhostSimulations.v:322-324` (`mgv_refined_input_handlers`). -/
def mgv_refined_input_handlers (me : name (P := P))
    (inp : raft_input (P := P))
    (st : electionsData (P := P) × raft_data (P := P)) :
    List (raft_output (P := P)) ×
      (electionsData (P := P) × raft_data (P := P)) ×
      List (name (P := P) × (ghost_log (P := P) × msg (P := P))) :=
  let (out, st', ps) := refined_input_handlers me inp st
  (out, st', add_ghost_msg me st' ps)

/-- `GhostSimulations.v:340-352` + `RaftMsgRefinementInterface.v:27`
(`raft_msg_refined_multi_params`). -/
@[reducible] def raft_msg_refined_multi_params :
    MultiParams (raft_msg_refined_base_params (P := P)) where
  name := name (P := P)
  msg := ghost_log (P := P) × msg (P := P)
  msg_eq_dec := inferInstance
  name_eq_dec := inferInstance
  nodes := nodes
  all_names_nodes := fun n => allFin_all n
  no_dup_nodes := allFin_NoDup _
  init_handlers := fun h => (elections_ghost_init, init_handlers h)
  net_handlers := mgv_refined_net_handlers
  input_handlers := mgv_refined_input_handlers

/-- `GhostSimulations.v:354-357` + `RaftMsgRefinementInterface.v:28`
(`raft_msg_refined_failure_params`): reboot as at the refined layer —
the (state) ghost survives; the per-packet ghosts live on the wire and
are untouched. -/
@[reducible] def raft_msg_refined_failure_params :
    FailureParams (raft_msg_refined_multi_params (P := P)) where
  reboot := fun st => (st.1, reboot st.2)

local notation "MsgNet" =>
  Network (raft_msg_refined_base_params (P := P)) raft_msg_refined_multi_params
local notation "MsgPacket" =>
  Packet (raft_msg_refined_base_params (P := P)) raft_msg_refined_multi_params
local notation "RefinedNet" =>
  Network (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RefinedPacket" =>
  Packet (raft_refined_base_params (P := P)) raft_refined_multi_params

/-- `RaftMsgRefinementInterface.v:34-79`
(`msg_refined_raft_intermediate_reachable`) — the msg-ghost twin of the
sibling `refined_raft_intermediate_reachable`, in its premise style
(ghost-update terms inlined; the per-packet ghost attached by
`add_ghost_msg` at each sending stage with that stage's state). -/
inductive msg_refined_raft_intermediate_reachable : MsgNet → Prop
  | MRRIR_init :
      msg_refined_raft_intermediate_reachable (step_async_init _ _)
  | MRRIR_step_failure :
      ∀ failed (net : MsgNet) failed' net' out,
        msg_refined_raft_intermediate_reachable net →
        step_failure _ _ raft_msg_refined_failure_params (failed, net)
          (failed', net') out →
        msg_refined_raft_intermediate_reachable net'
  | MRRIR_handleInput :
      ∀ (net : MsgNet) (h : name (P := P)) inp out d l ps' st',
        msg_refined_raft_intermediate_reachable net →
        handleInput h inp (net.nwState h).2 = (out, d, l) →
        (∀ h', st' h' = update net.nwState h
          (update_elections_data_input h inp (net.nwState h), d) h') →
        (∀ p', p' ∈ ps' → p' ∈ net.nwPackets ∨
          p' ∈ send_packets h (add_ghost_msg h
            (update_elections_data_input h inp (net.nwState h), d) l)) →
        msg_refined_raft_intermediate_reachable ⟨ps', st'⟩
  | MRRIR_handleMessage :
      ∀ (p : MsgPacket) (net : MsgNet) xs ys st' ps' d l,
        msg_refined_raft_intermediate_reachable net →
        handleMessage p.pSrc p.pDst p.pBody.2 (net.nwState p.pDst).2
          = (d, l) →
        net.nwPackets = xs ++ p :: ys →
        (∀ h, st' h = update net.nwState p.pDst
          (update_elections_data_net p.pDst p.pSrc p.pBody.2
            (net.nwState p.pDst), d) h) →
        (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys) ∨
          p' ∈ send_packets p.pDst (add_ghost_msg p.pDst
            (update_elections_data_net p.pDst p.pSrc p.pBody.2
              (net.nwState p.pDst), d) l)) →
        msg_refined_raft_intermediate_reachable ⟨ps', st'⟩
  | MRRIR_doLeader :
      ∀ (net : MsgNet) st' ps' (h : name (P := P)) os d' ms,
        msg_refined_raft_intermediate_reachable net →
        doLeader (net.nwState h).2 h = (os, d', ms) →
        (∀ h', st' h' = update net.nwState h ((net.nwState h).1, d') h') →
        (∀ q, q ∈ ps' → q ∈ net.nwPackets ∨
          q ∈ send_packets h (add_ghost_msg h ((net.nwState h).1, d') ms)) →
        msg_refined_raft_intermediate_reachable ⟨ps', st'⟩
  | MRRIR_doGenericServer :
      ∀ (net : MsgNet) st' ps' (h : name (P := P)) os d' ms,
        msg_refined_raft_intermediate_reachable net →
        doGenericServer h (net.nwState h).2 = (os, d', ms) →
        (∀ h', st' h' = update net.nwState h ((net.nwState h).1, d') h') →
        (∀ q, q ∈ ps' → q ∈ net.nwPackets ∨
          q ∈ send_packets h (add_ghost_msg h ((net.nwState h).1, d') ms)) →
        msg_refined_raft_intermediate_reachable ⟨ps', st'⟩

end MsgRefinement
end Raft
end VerdiCompat
