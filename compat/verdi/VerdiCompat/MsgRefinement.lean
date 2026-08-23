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
      ∀ (net : MsgNet) st' ps' gd d (h : name (P := P)) os d' ms,
        msg_refined_raft_intermediate_reachable net →
        doLeader d h = (os, d', ms) →
        net.nwState h = (gd, d) →
        (∀ h', st' h' = update net.nwState h (gd, d') h') →
        (∀ q, q ∈ ps' → q ∈ net.nwPackets ∨
          q ∈ send_packets h (add_ghost_msg h (gd, d') ms)) →
        msg_refined_raft_intermediate_reachable ⟨ps', st'⟩
  | MRRIR_doGenericServer :
      ∀ (net : MsgNet) st' ps' gd d (h : name (P := P)) os d' ms,
        msg_refined_raft_intermediate_reachable net →
        doGenericServer h d = (os, d', ms) →
        net.nwState h = (gd, d) →
        (∀ h', st' h' = update net.nwState h (gd, d') h') →
        (∀ q, q ∈ ps' → q ∈ net.nwPackets ∨
          q ∈ send_packets h (add_ghost_msg h (gd, d') ms)) →
        msg_refined_raft_intermediate_reachable ⟨ps', st'⟩

/-! ## The eleven obligation shapes (`RaftMsgRefinementInterface.v:83-195`)

Premise shapes 1:1 (explicit `gd` with its defining equation, the
sibling layer's D2 discipline); sends carry `add_ghost_msg`, and the
single-reply handlers (AppendEntries, RequestVote) name the reply
packet with its written ghost. -/

/-- `RaftMsgRefinementInterface.v:83-92` -/
def msg_refined_raft_net_invariant_client_request (Pr : MsgNet → Prop) : Prop :=
  ∀ (h : name (P := P)) (net : MsgNet) st' ps' gd out d l client id c,
    handleClientRequest h (net.nwState h).2 client id c = (out, d, l) →
    gd = update_elections_data_client_request h (net.nwState h) client id c →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    (∀ h', st' h' = update net.nwState h (gd, d) h') →
    (∀ p', p' ∈ ps' → p' ∈ net.nwPackets ∨
      p' ∈ send_packets h (add_ghost_msg h (gd, d) l)) →
    Pr ⟨ps', st'⟩

/-- `RaftMsgRefinementInterface.v:94-103` -/
def msg_refined_raft_net_invariant_timeout (Pr : MsgNet → Prop) : Prop :=
  ∀ (net : MsgNet) (h : name (P := P)) st' ps' gd out d l,
    handleTimeout h (net.nwState h).2 = (out, d, l) →
    gd = update_elections_data_timeout h (net.nwState h) →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    (∀ h', st' h' = update net.nwState h (gd, d) h') →
    (∀ p', p' ∈ ps' → p' ∈ net.nwPackets ∨
      p' ∈ send_packets h (add_ghost_msg h (gd, d) l)) →
    Pr ⟨ps', st'⟩

/-- `RaftMsgRefinementInterface.v:105-116` -/
def msg_refined_raft_net_invariant_append_entries (Pr : MsgNet → Prop) : Prop :=
  ∀ xs (p : MsgPacket) ys (net : MsgNet) st' ps' gd d m t n pli plt es ci,
    handleAppendEntries p.pDst (net.nwState p.pDst).2 t n pli plt es ci
      = (d, m) →
    gd = update_elections_data_appendEntries p.pDst (net.nwState p.pDst)
      t n pli plt es ci →
    p.pBody.2 = .AppendEntries t n pli plt es ci →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    net.nwPackets = xs ++ p :: ys →
    (∀ h, st' h = update net.nwState p.pDst (gd, d) h) →
    (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys) ∨
      p' = (⟨p.pDst, p.pSrc, (write_ghost_log p.pDst (gd, d), m)⟩ :
        MsgPacket)) →
    Pr ⟨ps', st'⟩

/-- `RaftMsgRefinementInterface.v:118-129` -/
def msg_refined_raft_net_invariant_append_entries_reply
    (Pr : MsgNet → Prop) : Prop :=
  ∀ xs (p : MsgPacket) ys (net : MsgNet) st' ps' gd d m t es res,
    handleAppendEntriesReply p.pDst (net.nwState p.pDst).2 p.pSrc t es res
      = (d, m) →
    gd = (net.nwState p.pDst).1 →
    p.pBody.2 = .AppendEntriesReply t es res →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    net.nwPackets = xs ++ p :: ys →
    (∀ h, st' h = update net.nwState p.pDst (gd, d) h) →
    (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys) ∨
      p' ∈ send_packets p.pDst (add_ghost_msg p.pDst (gd, d) m)) →
    Pr ⟨ps', st'⟩

/-- `RaftMsgRefinementInterface.v:127-139` -/
def msg_refined_raft_net_invariant_request_vote (Pr : MsgNet → Prop) : Prop :=
  ∀ xs (p : MsgPacket) ys (net : MsgNet) st' ps' gd d m t cid lli llt,
    handleRequestVote p.pDst (net.nwState p.pDst).2 t p.pSrc lli llt
      = (d, m) →
    gd = update_elections_data_requestVote p.pDst p.pSrc t p.pSrc lli llt
      (net.nwState p.pDst) →
    p.pBody.2 = .RequestVote t cid lli llt →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    net.nwPackets = xs ++ p :: ys →
    (∀ h, st' h = update net.nwState p.pDst (gd, d) h) →
    (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys) ∨
      p' = (⟨p.pDst, p.pSrc, (write_ghost_log p.pDst (gd, d), m)⟩ :
        MsgPacket)) →
    Pr ⟨ps', st'⟩

/-- `RaftMsgRefinementInterface.v:140-151` -/
def msg_refined_raft_net_invariant_request_vote_reply
    (Pr : MsgNet → Prop) : Prop :=
  ∀ xs (p : MsgPacket) ys (net : MsgNet) st' ps' gd d t v,
    handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc t v = d →
    gd = update_elections_data_requestVoteReply p.pDst p.pSrc t v
      (net.nwState p.pDst) →
    p.pBody.2 = .RequestVoteReply t v →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    net.nwPackets = xs ++ p :: ys →
    (∀ h, st' h = update net.nwState p.pDst (gd, d) h) →
    (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys)) →
    Pr ⟨ps', st'⟩

/-- `RaftMsgRefinementInterface.v:153-163` -/
def msg_refined_raft_net_invariant_do_leader (Pr : MsgNet → Prop) : Prop :=
  ∀ (net : MsgNet) st' ps' gd d (h : name (P := P)) os d' ms,
    doLeader d h = (os, d', ms) →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    net.nwState h = (gd, d) →
    (∀ h', st' h' = update net.nwState h (gd, d') h') →
    (∀ q, q ∈ ps' → q ∈ net.nwPackets ∨
      q ∈ send_packets h (add_ghost_msg h (gd, d') ms)) →
    Pr ⟨ps', st'⟩

/-- `RaftMsgRefinementInterface.v:165-175` -/
def msg_refined_raft_net_invariant_do_generic_server
    (Pr : MsgNet → Prop) : Prop :=
  ∀ (net : MsgNet) st' ps' gd d os d' ms (h : name (P := P)),
    doGenericServer h d = (os, d', ms) →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    net.nwState h = (gd, d) →
    (∀ h', st' h' = update net.nwState h (gd, d') h') →
    (∀ q, q ∈ ps' → q ∈ net.nwPackets ∨
      q ∈ send_packets h (add_ghost_msg h (gd, d') ms)) →
    Pr ⟨ps', st'⟩

/-- `RaftMsgRefinementInterface.v:177-183` -/
def msg_refined_raft_net_invariant_state_same_packet_subset
    (Pr : MsgNet → Prop) : Prop :=
  ∀ net net' : MsgNet,
    (∀ h, net.nwState h = net'.nwState h) →
    (∀ q, q ∈ net'.nwPackets → q ∈ net.nwPackets) →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    Pr net'

/-- `RaftMsgRefinementInterface.v:185-193` -/
def msg_refined_raft_net_invariant_reboot (Pr : MsgNet → Prop) : Prop :=
  ∀ (net net' : MsgNet) gd d (h : name (P := P)) d',
    reboot d = d' →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    net.nwState h = (gd, d) →
    (∀ h', net'.nwState h' = update net.nwState h (gd, d') h') →
    net.nwPackets = net'.nwPackets →
    Pr net'

/-- `RaftMsgRefinementInterface.v:194-195` -/
def msg_refined_raft_net_invariant_init (Pr : MsgNet → Prop) : Prop :=
  Pr (step_async_init _ _)

/-! ## The dispatchers and THE principle
(`RaftProofs/RaftMsgRefinementProof.v:12-275`) -/

/-- `RaftMsgRefinementProof.v:12-36` — dispatch a `handleMessage` step
(on the pair's underlying message) to the per-message obligations. -/
theorem msg_refined_raft_invariant_handle_message {Pr : MsgNet → Prop}
    (hae : msg_refined_raft_net_invariant_append_entries Pr)
    (haer : msg_refined_raft_net_invariant_append_entries_reply Pr)
    (hrv : msg_refined_raft_net_invariant_request_vote Pr)
    (hrvr : msg_refined_raft_net_invariant_request_vote_reply Pr) :
    ∀ xs (p : MsgPacket) ys (net : MsgNet) st' ps' d l,
      handleMessage p.pSrc p.pDst p.pBody.2 (net.nwState p.pDst).2 = (d, l) →
      Pr net →
      msg_refined_raft_intermediate_reachable net →
      net.nwPackets = xs ++ p :: ys →
      (∀ h, st' h = update net.nwState p.pDst
        (update_elections_data_net p.pDst p.pSrc p.pBody.2
          (net.nwState p.pDst), d) h) →
      (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys) ∨
        p' ∈ send_packets p.pDst (add_ghost_msg p.pDst
          (update_elections_data_net p.pDst p.pSrc p.pBody.2
            (net.nwState p.pDst), d) l)) →
      Pr ⟨ps', st'⟩ := by
  intro xs p ys net st' ps' d l hm hP hreach hpkts hst hps
  unfold handleMessage at hm
  cases hbody : p.pBody.2 with
  | AppendEntries t lid pli plt es ci =>
    rw [hbody] at hm
    simp only [] at hm
    rcases hh : handleAppendEntries p.pDst (net.nwState p.pDst).2 t lid
      pli plt es ci with ⟨d0, r0⟩
    rw [hh] at hm
    simp only [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact hae xs p ys net st' ps'
      (update_elections_data_net p.pDst p.pSrc p.pBody.2 (net.nwState p.pDst))
      d0 r0 t lid pli plt es ci hh (by rw [hbody]; rfl) hbody hP hreach
      hpkts hst
      (fun p' hp' => by
        rcases hps p' hp' with h | h
        · exact Or.inl h
        · right
          have h' : p' ∈ [(⟨p.pDst, p.pSrc,
              (write_ghost_log p.pDst
                (update_elections_data_net p.pDst p.pSrc p.pBody.2
                  (net.nwState p.pDst), d0), r0)⟩ : MsgPacket)] := h
          simpa using h')
  | AppendEntriesReply t es res =>
    rw [hbody] at hm
    simp only [] at hm
    exact haer xs p ys net st' ps'
      (update_elections_data_net p.pDst p.pSrc p.pBody.2 (net.nwState p.pDst))
      d l t es res hm (by rw [hbody]; rfl) hbody hP hreach hpkts hst hps
  | RequestVote t cid lli llt =>
    rw [hbody] at hm
    simp only [] at hm
    rcases hh : handleRequestVote p.pDst (net.nwState p.pDst).2 t p.pSrc
      lli llt with ⟨d0, r0⟩
    rw [hh] at hm
    simp only [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact hrv xs p ys net st' ps'
      (update_elections_data_net p.pDst p.pSrc p.pBody.2 (net.nwState p.pDst))
      d0 r0 t cid lli llt hh (by rw [hbody]; rfl) hbody hP hreach hpkts hst
      (fun p' hp' => by
        rcases hps p' hp' with h | h
        · exact Or.inl h
        · right
          have h' : p' ∈ [(⟨p.pDst, p.pSrc,
              (write_ghost_log p.pDst
                (update_elections_data_net p.pDst p.pSrc p.pBody.2
                  (net.nwState p.pDst), d0), r0)⟩ : MsgPacket)] := h
          simpa using h')
  | RequestVoteReply t v =>
    rw [hbody] at hm
    simp only [] at hm
    simp only [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact hrvr xs p ys net st' ps'
      (update_elections_data_net p.pDst p.pSrc p.pBody.2 (net.nwState p.pDst))
      _ t v rfl (by rw [hbody]; rfl) hbody hP hreach hpkts hst
      (fun p' hp' => by
        rcases hps p' hp' with h | h
        · exact h
        · simp [send_packets, add_ghost_msg] at h)

/-- `RaftMsgRefinementProof.v:38-57` — dispatch a `handleInput` step. -/
theorem msg_refined_raft_invariant_handle_input {Pr : MsgNet → Prop}
    (hto : msg_refined_raft_net_invariant_timeout Pr)
    (hcr : msg_refined_raft_net_invariant_client_request Pr) :
    ∀ (h : name (P := P)) inp (net : MsgNet) st' ps' out d l,
      handleInput h inp (net.nwState h).2 = (out, d, l) →
      Pr net →
      msg_refined_raft_intermediate_reachable net →
      (∀ h', st' h' = update net.nwState h
        (update_elections_data_input h inp (net.nwState h), d) h') →
      (∀ p', p' ∈ ps' → p' ∈ net.nwPackets ∨
        p' ∈ send_packets h (add_ghost_msg h
          (update_elections_data_input h inp (net.nwState h), d) l)) →
      Pr ⟨ps', st'⟩ := by
  intro h inp net st' ps' out d l hi hP hreach hst hps
  unfold handleInput at hi
  cases inp with
  | Timeout => exact hto net h st' ps' _ out d l hi rfl hP hreach hst hps
  | ClientRequest client id c =>
    exact hcr h net st' ps' _ out d l client id c hi rfl hP hreach hst hps

/-- `RaftMsgRefinementProof.v:58-275` — THE msg-ghost induction
principle. Re-proved from scratch in the sibling layer's style; the one
genuinely new step is the GHOST RECONCILIATION: the real handler
attaches the FINAL state's log to all sends, the staged constructors
attach each stage's — equal because `doLeader`/`doGenericServer` never
move the log (`add_ghost_msg_log_eq`). -/
theorem msg_refined_raft_net_invariant {Pr : MsgNet → Prop}
    (hinit : msg_refined_raft_net_invariant_init Pr)
    (hcr : msg_refined_raft_net_invariant_client_request Pr)
    (hto : msg_refined_raft_net_invariant_timeout Pr)
    (hae : msg_refined_raft_net_invariant_append_entries Pr)
    (haer : msg_refined_raft_net_invariant_append_entries_reply Pr)
    (hrv : msg_refined_raft_net_invariant_request_vote Pr)
    (hrvr : msg_refined_raft_net_invariant_request_vote_reply Pr)
    (hdl : msg_refined_raft_net_invariant_do_leader Pr)
    (hgs : msg_refined_raft_net_invariant_do_generic_server Pr)
    (hsub : msg_refined_raft_net_invariant_state_same_packet_subset Pr)
    (hreb : msg_refined_raft_net_invariant_reboot Pr) :
    ∀ net, msg_refined_raft_intermediate_reachable (P := P) net → Pr net := by
  intro net hreach
  induction hreach with
  | MRRIR_init => exact hinit
  | MRRIR_handleInput net h inp out d l ps' st' hreach hi hst hps ih =>
    exact msg_refined_raft_invariant_handle_input hto hcr h inp net st' ps'
      out d l hi ih hreach hst hps
  | MRRIR_handleMessage p net xs ys st' ps' d l hreach hm hpkts hst hps ih =>
    exact msg_refined_raft_invariant_handle_message hae haer hrv hrvr xs p
      ys net st' ps' d l hm ih hreach hpkts hst hps
  | MRRIR_doLeader net st' ps' gd d h os d' ms hreach hdo hstate hst hps ih =>
    exact hdl net st' ps' gd d h os d' ms hdo ih hreach hstate hst hps
  | MRRIR_doGenericServer net st' ps' gd d h os d' ms hreach hdo hstate hst hps ih =>
    exact hgs net st' ps' gd d os d' ms h hdo ih hreach hstate hst hps
  | MRRIR_step_failure failed net failed' net' out hreach hstep ih =>
    cases hstep with
    | StepFailure_deliver net _ failed p xs ys out' dfull l hpkts hlive hnh hnet' =>
      rcases hm : handleMessage p.pSrc p.pDst p.pBody.2 (net.nwState p.pDst).2
        with ⟨d0, l0⟩
      rcases hl : doLeader d0 p.pDst with ⟨o1, d1, l1⟩
      rcases hg : doGenericServer p.pDst d1 with ⟨o2, d2, l2⟩
      have hnh' : (o1 ++ o2,
          ((update_elections_data_net p.pDst p.pSrc p.pBody.2
              (net.nwState p.pDst), d2) :
            electionsData (P := P) × raft_data (P := P)),
          add_ghost_msg p.pDst
            (update_elections_data_net p.pDst p.pSrc p.pBody.2
              (net.nwState p.pDst), d2) (l0 ++ l1 ++ l2)) = (out', dfull, l) := by
        have hnh : mgv_refined_net_handlers p.pDst p.pSrc p.pBody
            (net.nwState p.pDst) = (out', dfull, l) := hnh
        unfold mgv_refined_net_handlers refined_net_handlers RaftNetHandler
          at hnh
        rw [hm] at hnh
        simp only [] at hnh
        rw [hl] at hnh
        simp only [] at hnh
        rw [hg] at hnh
        simpa using hnh
      simp only [Prod.mk.injEq] at hnh'
      obtain ⟨-, rfl, rfl⟩ := hnh'
      subst hnet'
      obtain ⟨-, -, -, -, hl_log, -⟩ := doLeader_spec d0 p.pDst hl
      obtain ⟨hg_log, -, -, -, -, -⟩ := doGenericServer_spec p.pDst d1 hg
      have h20 : d2.log = d0.log := hg_log.trans hl_log
      have h21 : d2.log = d1.log := hg_log
      -- staged intermediate nets, each with its stage's ghost
      have hnet1 : msg_refined_raft_intermediate_reachable (P := P)
          ⟨(xs ++ ys) ++ send_packets p.pDst
              (add_ghost_msg p.pDst
                (update_elections_data_net p.pDst p.pSrc p.pBody.2
                  (net.nwState p.pDst), d0) l0),
           update net.nwState p.pDst
             (update_elections_data_net p.pDst p.pSrc p.pBody.2
               (net.nwState p.pDst), d0)⟩ :=
        .MRRIR_handleMessage p net xs ys _ _ d0 l0 hreach hm hpkts
          (fun _ => rfl)
          (fun p' hp' => by simpa using (List.mem_append.mp hp'))
      have hstate1 : (update net.nwState p.pDst
          (update_elections_data_net p.pDst p.pSrc p.pBody.2
            (net.nwState p.pDst), d0)) p.pDst
          = (update_elections_data_net p.pDst p.pSrc p.pBody.2
              (net.nwState p.pDst), d0) :=
        update_same ..
      have hnet2 : msg_refined_raft_intermediate_reachable (P := P)
          ⟨((xs ++ ys) ++ send_packets p.pDst
              (add_ghost_msg p.pDst
                (update_elections_data_net p.pDst p.pSrc p.pBody.2
                  (net.nwState p.pDst), d0) l0)) ++ send_packets p.pDst
              (add_ghost_msg p.pDst
                (update_elections_data_net p.pDst p.pSrc p.pBody.2
                  (net.nwState p.pDst), d1) l1),
           update (update net.nwState p.pDst
               (update_elections_data_net p.pDst p.pSrc p.pBody.2
                 (net.nwState p.pDst), d0)) p.pDst
             (update_elections_data_net p.pDst p.pSrc p.pBody.2
               (net.nwState p.pDst), d1)⟩ :=
        .MRRIR_doLeader ⟨(xs ++ ys) ++ send_packets p.pDst
              (add_ghost_msg p.pDst
                (update_elections_data_net p.pDst p.pSrc p.pBody.2
                  (net.nwState p.pDst), d0) l0),
            update net.nwState p.pDst
              (update_elections_data_net p.pDst p.pSrc p.pBody.2
                (net.nwState p.pDst), d0)⟩
          _ _ _ d0 p.pDst o1 d1 l1 hnet1 hl hstate1
          (fun h' => by simp only [update_same])
          (fun q hq => by simpa using (List.mem_append.mp hq))
      have hP1 : Pr ⟨(xs ++ ys) ++ send_packets p.pDst
          (add_ghost_msg p.pDst
            (update_elections_data_net p.pDst p.pSrc p.pBody.2
              (net.nwState p.pDst), d0) l0),
          update net.nwState p.pDst
            (update_elections_data_net p.pDst p.pSrc p.pBody.2
              (net.nwState p.pDst), d0)⟩ :=
        msg_refined_raft_invariant_handle_message hae haer hrv hrvr xs p ys
          net _ _ d0 l0 hm ih hreach hpkts (fun _ => rfl)
          (fun p' hp' => List.mem_append.mp hp')
      have hP2 : Pr ⟨((xs ++ ys) ++ send_packets p.pDst
          (add_ghost_msg p.pDst
            (update_elections_data_net p.pDst p.pSrc p.pBody.2
              (net.nwState p.pDst), d0) l0)) ++ send_packets p.pDst
          (add_ghost_msg p.pDst
            (update_elections_data_net p.pDst p.pSrc p.pBody.2
              (net.nwState p.pDst), d1) l1),
          update (update net.nwState p.pDst
              (update_elections_data_net p.pDst p.pSrc p.pBody.2
                (net.nwState p.pDst), d0)) p.pDst
            (update_elections_data_net p.pDst p.pSrc p.pBody.2
              (net.nwState p.pDst), d1)⟩ :=
        hdl ⟨(xs ++ ys) ++ send_packets p.pDst
            (add_ghost_msg p.pDst
              (update_elections_data_net p.pDst p.pSrc p.pBody.2
                (net.nwState p.pDst), d0) l0),
            update net.nwState p.pDst
              (update_elections_data_net p.pDst p.pSrc p.pBody.2
                (net.nwState p.pDst), d0)⟩
          _ _ _ d0 p.pDst o1 d1 l1 hl hP1 hnet1 hstate1
          (fun h' => by rw [update_update_same])
          (fun q hq => List.mem_append.mp hq)
      refine hgs ⟨((xs ++ ys) ++ send_packets p.pDst
          (add_ghost_msg p.pDst
            (update_elections_data_net p.pDst p.pSrc p.pBody.2
              (net.nwState p.pDst), d0) l0)) ++ send_packets p.pDst
          (add_ghost_msg p.pDst
            (update_elections_data_net p.pDst p.pSrc p.pBody.2
              (net.nwState p.pDst), d1) l1),
          update (update net.nwState p.pDst
              (update_elections_data_net p.pDst p.pSrc p.pBody.2
                (net.nwState p.pDst), d0)) p.pDst
            (update_elections_data_net p.pDst p.pSrc p.pBody.2
              (net.nwState p.pDst), d1)⟩
        _ _ (update_elections_data_net p.pDst p.pSrc p.pBody.2
          (net.nwState p.pDst)) d1 o2 d2 l2 p.pDst hg hP2 hnet2 (by simp)
        ?_ ?_
      · intro h'
        simp only [update_update_same]
      · intro q hq
        -- the real successor's sends carry the FINAL ghost; reconcile
        -- the stage pieces via add_ghost_msg_log_eq
        rw [add_ghost_msg_app, add_ghost_msg_app] at hq
        rw [send_packets_app, send_packets_app] at hq
        rw [add_ghost_msg_log_eq (st' := (update_elections_data_net p.pDst
              p.pSrc p.pBody.2 (net.nwState p.pDst), d0)) h20 l0,
            add_ghost_msg_log_eq (st' := (update_elections_data_net p.pDst
              p.pSrc p.pBody.2 (net.nwState p.pDst), d1)) h21 l1] at hq
        simp only [update_update_same, update_same, List.mem_append] at hq ⊢
        -- hq : (((l0 ∨ l1) ∨ l2) ∨ xs) ∨ ys ; ⊢ (((xs ∨ ys) ∨ l0) ∨ l1) ∨ l2
        rcases hq with (((h | h) | h) | h) | h
        · exact Or.inl (Or.inl (Or.inr h))
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
        · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
        · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    | StepFailure_input h net _ failed out' inp dfull l hlive hih hnet' =>
      rcases hi : handleInput h inp (net.nwState h).2 with ⟨o0, d0, l0⟩
      rcases hl : doLeader d0 h with ⟨o1, d1, l1⟩
      rcases hg : doGenericServer h d1 with ⟨o2, d2, l2⟩
      have hih' : (o0 ++ o1 ++ o2,
          ((update_elections_data_input h inp (net.nwState h), d2) :
            electionsData (P := P) × raft_data (P := P)),
          add_ghost_msg h (update_elections_data_input h inp (net.nwState h),
            d2) (l0 ++ l1 ++ l2)) = (out', dfull, l) := by
        have hih : mgv_refined_input_handlers h inp (net.nwState h)
            = (out', dfull, l) := hih
        unfold mgv_refined_input_handlers refined_input_handlers
          RaftInputHandler at hih
        rw [hi] at hih
        simp only [] at hih
        rw [hl] at hih
        simp only [] at hih
        rw [hg] at hih
        simpa using hih
      simp only [Prod.mk.injEq] at hih'
      obtain ⟨-, rfl, rfl⟩ := hih'
      subst hnet'
      obtain ⟨-, -, -, -, hl_log, -⟩ := doLeader_spec d0 h hl
      obtain ⟨hg_log, -, -, -, -, -⟩ := doGenericServer_spec h d1 hg
      have h20 : d2.log = d0.log := hg_log.trans hl_log
      have h21 : d2.log = d1.log := hg_log
      have hnet1 : msg_refined_raft_intermediate_reachable (P := P)
          ⟨net.nwPackets ++ send_packets h
              (add_ghost_msg h
                (update_elections_data_input h inp (net.nwState h), d0) l0),
           update net.nwState h
             (update_elections_data_input h inp (net.nwState h), d0)⟩ :=
        .MRRIR_handleInput net h inp o0 d0 l0 _ _ hreach hi (fun _ => rfl)
          (fun p' hp' => List.mem_append.mp hp')
      have hstate1 : (update net.nwState h
            (update_elections_data_input h inp (net.nwState h), d0)) h
          = (update_elections_data_input h inp (net.nwState h), d0) :=
        update_same ..
      have hnet2 : msg_refined_raft_intermediate_reachable (P := P)
          ⟨(net.nwPackets ++ send_packets h
              (add_ghost_msg h
                (update_elections_data_input h inp (net.nwState h), d0) l0))
              ++ send_packets h
              (add_ghost_msg h
                (update_elections_data_input h inp (net.nwState h), d1) l1),
           update (update net.nwState h
               (update_elections_data_input h inp (net.nwState h), d0)) h
             (update_elections_data_input h inp (net.nwState h), d1)⟩ :=
        .MRRIR_doLeader ⟨net.nwPackets ++ send_packets h
              (add_ghost_msg h
                (update_elections_data_input h inp (net.nwState h), d0) l0),
            update net.nwState h
              (update_elections_data_input h inp (net.nwState h), d0)⟩
          _ _ _ d0 h o1 d1 l1 hnet1 hl hstate1
          (fun h' => by simp only [update_same])
          (fun q hq => by simpa using (List.mem_append.mp hq))
      have hP1 : Pr ⟨net.nwPackets ++ send_packets h
          (add_ghost_msg h
            (update_elections_data_input h inp (net.nwState h), d0) l0),
          update net.nwState h
            (update_elections_data_input h inp (net.nwState h), d0)⟩ :=
        msg_refined_raft_invariant_handle_input hto hcr h inp net _ _ o0 d0
          l0 hi ih hreach (fun _ => rfl) (fun p' hp' => List.mem_append.mp hp')
      have hP2 : Pr ⟨(net.nwPackets ++ send_packets h
          (add_ghost_msg h
            (update_elections_data_input h inp (net.nwState h), d0) l0))
          ++ send_packets h
          (add_ghost_msg h
            (update_elections_data_input h inp (net.nwState h), d1) l1),
          update (update net.nwState h
              (update_elections_data_input h inp (net.nwState h), d0)) h
            (update_elections_data_input h inp (net.nwState h), d1)⟩ :=
        hdl ⟨net.nwPackets ++ send_packets h
            (add_ghost_msg h
              (update_elections_data_input h inp (net.nwState h), d0) l0),
            update net.nwState h
              (update_elections_data_input h inp (net.nwState h), d0)⟩
          _ _ _ d0 h o1 d1 l1 hl hP1 hnet1 hstate1
          (fun h' => by rw [update_update_same])
          (fun q hq => List.mem_append.mp hq)
      refine hgs ⟨(net.nwPackets ++ send_packets h
          (add_ghost_msg h
            (update_elections_data_input h inp (net.nwState h), d0) l0))
          ++ send_packets h
          (add_ghost_msg h
            (update_elections_data_input h inp (net.nwState h), d1) l1),
          update (update net.nwState h
              (update_elections_data_input h inp (net.nwState h), d0)) h
            (update_elections_data_input h inp (net.nwState h), d1)⟩
        _ _ (update_elections_data_input h inp (net.nwState h)) d1
        o2 d2 l2 h hg hP2 hnet2 (by simp) ?_ ?_
      · intro h'
        simp only [update_update_same]
      · intro q hq
        rw [add_ghost_msg_app, add_ghost_msg_app] at hq
        rw [send_packets_app, send_packets_app] at hq
        rw [add_ghost_msg_log_eq (st' := (update_elections_data_input h inp
              (net.nwState h), d0)) h20 l0,
            add_ghost_msg_log_eq (st' := (update_elections_data_input h inp
              (net.nwState h), d1)) h21 l1] at hq
        simp only [update_update_same, update_same, List.mem_append] at hq ⊢
        -- hq : ((l0 ∨ l1) ∨ l2) ∨ pk ; ⊢ ((pk ∨ l0) ∨ l1) ∨ l2
        rcases hq with ((h' | h') | h') | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
        · exact Or.inl (Or.inl (Or.inl h'))
    | StepFailure_drop net _ failed p xs ys hpkts hnet' =>
      subst hnet'
      refine hsub net _ (fun _ => rfl) (fun q hq => ?_) ih hreach
      rw [hpkts]
      simp only [List.mem_append, List.mem_cons] at hq ⊢
      rcases hq with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    | StepFailure_dup net _ failed p xs ys hpkts hnet' =>
      subst hnet'
      refine hsub net _ (fun _ => rfl) (fun q hq => ?_) ih hreach
      rw [hpkts]
      simp only [List.mem_append, List.mem_cons] at hq ⊢
      rcases hq with (h | h) | (h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    | StepFailure_fail h net failed => exact ih
    | StepFailure_reboot h net _ failed failed' hmem hfailed' hnet' =>
      subst hnet'
      exact hreb net _ (net.nwState h).1 (net.nwState h).2 h _ rfl ih hreach
        rfl (fun _ => rfl) rfl

/-! ## The PRIMED obligation set and principle
(`RaftMsgRefinementInterface.v:195-406`,
`RaftProofs/RaftMsgRefinementProof.v:276-565`) — GAP-1's msg-side
instance, ported on FIRST GENUINE NEED (unit 13:
`log_properties_hold_on_ghost_logs` quantifies over all
reachability-closed log properties, and a fresh packet's ghost is the
POST-state's log — no pre-state route exists; decision logged in the
arc log's unit-13 opening).

Each primed obligation = its unprimed twin + the SUCCESSOR net's
reachability premise (upstream :195-315; `state_same_packet_subset'`
is upstream-identical to the unprimed shape and kept as its own def
for 1:1 citation). The principle `msg_refined_raft_net_invariant'` is
upstream's :276-565 statement; its proof here is a logged §9
re-derivation — instead of re-running the 290-line staged induction
with reachability asserts, it instantiates the ported UNPRIMED
principle at `Q net := msg_refined_raft_intermediate_reachable net →
Pr net`: every unprimed obligation carries the pre-state reachability
premise, so each Q-obligation discharges by pure logic from the
corresponding primed obligation, and the two reachability applications
collapse at the end. Of the ten `_weak` bridges (:317-406) the three
the first consumer uses are ported; the rest are one-line drops,
port-on-need. -/

/-- `RaftMsgRefinementInterface.v:195-205` -/
def msg_refined_raft_net_invariant_client_request' (Pr : MsgNet → Prop) : Prop :=
  ∀ (h : name (P := P)) (net : MsgNet) st' ps' gd out d l client id c,
    handleClientRequest h (net.nwState h).2 client id c = (out, d, l) →
    gd = update_elections_data_client_request h (net.nwState h) client id c →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    msg_refined_raft_intermediate_reachable ⟨ps', st'⟩ →
    (∀ h', st' h' = update net.nwState h (gd, d) h') →
    (∀ p', p' ∈ ps' → p' ∈ net.nwPackets ∨
      p' ∈ send_packets h (add_ghost_msg h (gd, d) l)) →
    Pr ⟨ps', st'⟩

/-- `RaftMsgRefinementInterface.v:207-217` -/
def msg_refined_raft_net_invariant_timeout' (Pr : MsgNet → Prop) : Prop :=
  ∀ (net : MsgNet) (h : name (P := P)) st' ps' gd out d l,
    handleTimeout h (net.nwState h).2 = (out, d, l) →
    gd = update_elections_data_timeout h (net.nwState h) →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    msg_refined_raft_intermediate_reachable ⟨ps', st'⟩ →
    (∀ h', st' h' = update net.nwState h (gd, d) h') →
    (∀ p', p' ∈ ps' → p' ∈ net.nwPackets ∨
      p' ∈ send_packets h (add_ghost_msg h (gd, d) l)) →
    Pr ⟨ps', st'⟩

/-- `RaftMsgRefinementInterface.v:219-232` -/
def msg_refined_raft_net_invariant_append_entries' (Pr : MsgNet → Prop) : Prop :=
  ∀ xs (p : MsgPacket) ys (net : MsgNet) st' ps' gd d m t n pli plt es ci,
    handleAppendEntries p.pDst (net.nwState p.pDst).2 t n pli plt es ci
      = (d, m) →
    gd = update_elections_data_appendEntries p.pDst (net.nwState p.pDst)
      t n pli plt es ci →
    p.pBody.2 = .AppendEntries t n pli plt es ci →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    msg_refined_raft_intermediate_reachable ⟨ps', st'⟩ →
    net.nwPackets = xs ++ p :: ys →
    (∀ h, st' h = update net.nwState p.pDst (gd, d) h) →
    (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys) ∨
      p' = (⟨p.pDst, p.pSrc, (write_ghost_log p.pDst (gd, d), m)⟩ :
        MsgPacket)) →
    Pr ⟨ps', st'⟩

/-- `RaftMsgRefinementInterface.v:233-246` -/
def msg_refined_raft_net_invariant_append_entries_reply'
    (Pr : MsgNet → Prop) : Prop :=
  ∀ xs (p : MsgPacket) ys (net : MsgNet) st' ps' gd d m t es res,
    handleAppendEntriesReply p.pDst (net.nwState p.pDst).2 p.pSrc t es res
      = (d, m) →
    gd = (net.nwState p.pDst).1 →
    p.pBody.2 = .AppendEntriesReply t es res →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    msg_refined_raft_intermediate_reachable ⟨ps', st'⟩ →
    net.nwPackets = xs ++ p :: ys →
    (∀ h, st' h = update net.nwState p.pDst (gd, d) h) →
    (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys) ∨
      p' ∈ send_packets p.pDst (add_ghost_msg p.pDst (gd, d) m)) →
    Pr ⟨ps', st'⟩

/-- `RaftMsgRefinementInterface.v:247-260` -/
def msg_refined_raft_net_invariant_request_vote' (Pr : MsgNet → Prop) : Prop :=
  ∀ xs (p : MsgPacket) ys (net : MsgNet) st' ps' gd d m t cid lli llt,
    handleRequestVote p.pDst (net.nwState p.pDst).2 t p.pSrc lli llt
      = (d, m) →
    gd = update_elections_data_requestVote p.pDst p.pSrc t p.pSrc lli llt
      (net.nwState p.pDst) →
    p.pBody.2 = .RequestVote t cid lli llt →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    msg_refined_raft_intermediate_reachable ⟨ps', st'⟩ →
    net.nwPackets = xs ++ p :: ys →
    (∀ h, st' h = update net.nwState p.pDst (gd, d) h) →
    (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys) ∨
      p' = (⟨p.pDst, p.pSrc, (write_ghost_log p.pDst (gd, d), m)⟩ :
        MsgPacket)) →
    Pr ⟨ps', st'⟩

/-- `RaftMsgRefinementInterface.v:261-273` -/
def msg_refined_raft_net_invariant_request_vote_reply'
    (Pr : MsgNet → Prop) : Prop :=
  ∀ xs (p : MsgPacket) ys (net : MsgNet) st' ps' gd d t v,
    handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc t v = d →
    gd = update_elections_data_requestVoteReply p.pDst p.pSrc t v
      (net.nwState p.pDst) →
    p.pBody.2 = .RequestVoteReply t v →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    msg_refined_raft_intermediate_reachable ⟨ps', st'⟩ →
    net.nwPackets = xs ++ p :: ys →
    (∀ h, st' h = update net.nwState p.pDst (gd, d) h) →
    (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys)) →
    Pr ⟨ps', st'⟩

/-- `RaftMsgRefinementInterface.v:274-285` -/
def msg_refined_raft_net_invariant_do_leader' (Pr : MsgNet → Prop) : Prop :=
  ∀ (net : MsgNet) st' ps' gd d (h : name (P := P)) os d' ms,
    doLeader d h = (os, d', ms) →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    msg_refined_raft_intermediate_reachable ⟨ps', st'⟩ →
    net.nwState h = (gd, d) →
    (∀ h', st' h' = update net.nwState h (gd, d') h') →
    (∀ q, q ∈ ps' → q ∈ net.nwPackets ∨
      q ∈ send_packets h (add_ghost_msg h (gd, d') ms)) →
    Pr ⟨ps', st'⟩

/-- `RaftMsgRefinementInterface.v:286-297` -/
def msg_refined_raft_net_invariant_do_generic_server'
    (Pr : MsgNet → Prop) : Prop :=
  ∀ (net : MsgNet) st' ps' gd d os d' ms (h : name (P := P)),
    doGenericServer h d = (os, d', ms) →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    msg_refined_raft_intermediate_reachable ⟨ps', st'⟩ →
    net.nwState h = (gd, d) →
    (∀ h', st' h' = update net.nwState h (gd, d') h') →
    (∀ q, q ∈ ps' → q ∈ net.nwPackets ∨
      q ∈ send_packets h (add_ghost_msg h (gd, d') ms)) →
    Pr ⟨ps', st'⟩

/-- `RaftMsgRefinementInterface.v:298-304` — upstream-identical to the
unprimed shape (no successor-reachability premise); kept as its own
def so chain files cite it 1:1. -/
def msg_refined_raft_net_invariant_state_same_packet_subset'
    (Pr : MsgNet → Prop) : Prop :=
  ∀ net net' : MsgNet,
    (∀ h, net.nwState h = net'.nwState h) →
    (∀ q, q ∈ net'.nwPackets → q ∈ net.nwPackets) →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    Pr net'

/-- `RaftMsgRefinementInterface.v:306-315` -/
def msg_refined_raft_net_invariant_reboot' (Pr : MsgNet → Prop) : Prop :=
  ∀ (net net' : MsgNet) gd d (h : name (P := P)) d',
    reboot d = d' →
    Pr net →
    msg_refined_raft_intermediate_reachable net →
    msg_refined_raft_intermediate_reachable net' →
    net.nwState h = (gd, d) →
    (∀ h', net'.nwState h' = update net.nwState h (gd, d') h') →
    net.nwPackets = net'.nwPackets →
    Pr net'

/-- `RaftMsgRefinementInterface.v:362-370`
(`msg_refined_raft_net_invariant_request_vote_reply'_weak`). -/
theorem msg_refined_raft_net_invariant_request_vote_reply'_weak
    {Pr : MsgNet → Prop}
    (h : msg_refined_raft_net_invariant_request_vote_reply Pr) :
    msg_refined_raft_net_invariant_request_vote_reply' Pr := by
  intro xs p ys net st' ps' gd d t v hrvr hgd hbody hP hreach _hreach'
    hpkts hst hps
  exact h xs p ys net st' ps' gd d t v hrvr hgd hbody hP hreach hpkts hst
    hps

/-- `RaftMsgRefinementInterface.v:398-406`
(`msg_refined_raft_net_invariant_subset'_weak`) — the two shapes
coincide upstream, so this is the identity. -/
theorem msg_refined_raft_net_invariant_subset'_weak {Pr : MsgNet → Prop}
    (h : msg_refined_raft_net_invariant_state_same_packet_subset Pr) :
    msg_refined_raft_net_invariant_state_same_packet_subset' Pr := h

/-- `RaftMsgRefinementInterface.v:389-397`
(`msg_refined_raft_net_invariant_reboot'_weak`). -/
theorem msg_refined_raft_net_invariant_reboot'_weak {Pr : MsgNet → Prop}
    (h : msg_refined_raft_net_invariant_reboot Pr) :
    msg_refined_raft_net_invariant_reboot' Pr := by
  intro net net' gd d h0 d' hrb hP hreach _hreach' hstate hst hpkts
  exact h net net' gd d h0 d' hrb hP hreach hstate hst hpkts

/-- `RaftMsgRefinementInterface.v:317-325`
(`msg_refined_raft_net_invariant_client_request'_weak`). -/
theorem msg_refined_raft_net_invariant_client_request'_weak
    {Pr : MsgNet → Prop}
    (h : msg_refined_raft_net_invariant_client_request Pr) :
    msg_refined_raft_net_invariant_client_request' Pr := by
  intro h0 net st' ps' gd out d l client id c hcr hgd hP hreach _hreach'
    hst hps
  exact h h0 net st' ps' gd out d l client id c hcr hgd hP hreach hst hps

/-- `RaftMsgRefinementInterface.v:326-334`
(`msg_refined_raft_net_invariant_timeout'_weak`). -/
theorem msg_refined_raft_net_invariant_timeout'_weak {Pr : MsgNet → Prop}
    (h : msg_refined_raft_net_invariant_timeout Pr) :
    msg_refined_raft_net_invariant_timeout' Pr := by
  intro net h0 st' ps' gd out d l hto hgd hP hreach _hreach' hst hps
  exact h net h0 st' ps' gd out d l hto hgd hP hreach hst hps

/-- `RaftMsgRefinementInterface.v:344-352`
(`msg_refined_raft_net_invariant_append_entries_reply'_weak`). -/
theorem msg_refined_raft_net_invariant_append_entries_reply'_weak
    {Pr : MsgNet → Prop}
    (h : msg_refined_raft_net_invariant_append_entries_reply Pr) :
    msg_refined_raft_net_invariant_append_entries_reply' Pr := by
  intro xs p ys net st' ps' gd d m t es res haer hgd hbody hP hreach
    _hreach' hpkts hst hps
  exact h xs p ys net st' ps' gd d m t es res haer hgd hbody hP hreach
    hpkts hst hps

/-- `RaftMsgRefinementInterface.v:371-379`
(`msg_refined_raft_net_invariant_do_leader'_weak`). -/
theorem msg_refined_raft_net_invariant_do_leader'_weak {Pr : MsgNet → Prop}
    (h : msg_refined_raft_net_invariant_do_leader Pr) :
    msg_refined_raft_net_invariant_do_leader' Pr := by
  intro net st' ps' gd d h0 os d' ms hdl hP hreach _hreach' hstate hst hps
  exact h net st' ps' gd d h0 os d' ms hdl hP hreach hstate hst hps

/-- `RaftMsgRefinementInterface.v:380-388`
(`msg_refined_raft_net_invariant_do_generic_server'_weak`). -/
theorem msg_refined_raft_net_invariant_do_generic_server'_weak
    {Pr : MsgNet → Prop}
    (h : msg_refined_raft_net_invariant_do_generic_server Pr) :
    msg_refined_raft_net_invariant_do_generic_server' Pr := by
  intro net st' ps' gd d os d' ms h0 hgs hP hreach _hreach' hstate hst hps
  exact h net st' ps' gd d os d' ms h0 hgs hP hreach hstate hst hps

/-- `RaftProofs/RaftMsgRefinementProof.v:276-565`
(`msg_refined_raft_net_invariant'`) — THE primed principle: the
obligations additionally receive the SUCCESSOR net's reachability.
Proof by the logged Q-route (see the section header): instantiate the
unprimed principle at `Q net := reachable net → Pr net`. -/
theorem msg_refined_raft_net_invariant' {Pr : MsgNet → Prop}
    (hinit : msg_refined_raft_net_invariant_init Pr)
    (hcr : msg_refined_raft_net_invariant_client_request' Pr)
    (hto : msg_refined_raft_net_invariant_timeout' Pr)
    (hae : msg_refined_raft_net_invariant_append_entries' Pr)
    (haer : msg_refined_raft_net_invariant_append_entries_reply' Pr)
    (hrv : msg_refined_raft_net_invariant_request_vote' Pr)
    (hrvr : msg_refined_raft_net_invariant_request_vote_reply' Pr)
    (hdl : msg_refined_raft_net_invariant_do_leader' Pr)
    (hgs : msg_refined_raft_net_invariant_do_generic_server' Pr)
    (hsub : msg_refined_raft_net_invariant_state_same_packet_subset' Pr)
    (hreb : msg_refined_raft_net_invariant_reboot' Pr) :
    ∀ net, msg_refined_raft_intermediate_reachable (P := P) net → Pr net := by
  refine fun net hreach => msg_refined_raft_net_invariant
    (Pr := fun n => msg_refined_raft_intermediate_reachable (P := P) n → Pr n)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ net hreach hreach
  · -- init
    exact fun _ => hinit
  · -- client_request
    intro h net0 st' ps' gd out d l client id c hcr0 hgd hQ hreach0 hst hps
      hreach'
    exact hcr h net0 st' ps' gd out d l client id c hcr0 hgd (hQ hreach0)
      hreach0 hreach' hst hps
  · -- timeout
    intro net0 h st' ps' gd out d l hto0 hgd hQ hreach0 hst hps hreach'
    exact hto net0 h st' ps' gd out d l hto0 hgd (hQ hreach0) hreach0
      hreach' hst hps
  · -- append_entries
    intro xs p ys net0 st' ps' gd d m t n pli plt es ci hae0 hgd hbody hQ
      hreach0 hpkts hst hps hreach'
    exact hae xs p ys net0 st' ps' gd d m t n pli plt es ci hae0 hgd hbody
      (hQ hreach0) hreach0 hreach' hpkts hst hps
  · -- append_entries_reply
    intro xs p ys net0 st' ps' gd d m t es res haer0 hgd hbody hQ hreach0
      hpkts hst hps hreach'
    exact haer xs p ys net0 st' ps' gd d m t es res haer0 hgd hbody
      (hQ hreach0) hreach0 hreach' hpkts hst hps
  · -- request_vote
    intro xs p ys net0 st' ps' gd d m t cid lli llt hrv0 hgd hbody hQ
      hreach0 hpkts hst hps hreach'
    exact hrv xs p ys net0 st' ps' gd d m t cid lli llt hrv0 hgd hbody
      (hQ hreach0) hreach0 hreach' hpkts hst hps
  · -- request_vote_reply
    intro xs p ys net0 st' ps' gd d t v hrvr0 hgd hbody hQ hreach0 hpkts
      hst hps hreach'
    exact hrvr xs p ys net0 st' ps' gd d t v hrvr0 hgd hbody (hQ hreach0)
      hreach0 hreach' hpkts hst hps
  · -- do_leader
    intro net0 st' ps' gd d h os d' ms hdl0 hQ hreach0 hstate hst hps
      hreach'
    exact hdl net0 st' ps' gd d h os d' ms hdl0 (hQ hreach0) hreach0
      hreach' hstate hst hps
  · -- do_generic_server
    intro net0 st' ps' gd d os d' ms h hgs0 hQ hreach0 hstate hst hps
      hreach'
    exact hgs net0 st' ps' gd d os d' ms h hgs0 (hQ hreach0) hreach0
      hreach' hstate hst hps
  · -- state_same_packet_subset
    intro net0 net1 hstates hsubp hQ hreach0 _hreach'
    exact hsub net0 net1 hstates hsubp (hQ hreach0) hreach0
  · -- reboot
    intro net0 net1 gd d h d' hrb hQ hreach0 hstate hst hpkts hreach'
    exact hreb net0 net1 gd d h d' hrb (hQ hreach0) hreach0 hreach' hstate
      hst hpkts

/-! ## Erasure: `mgv_deghost` and the msg→refined simulation
(`GhostSimulations.v:359-377`, `RaftProofs/RaftMsgRefinementProof.v:566-654,908-917`) -/

/-- `GhostSimulations.v:359-363` (`mgv_deghost_packet`): strip the
per-packet ghost. -/
def mgv_deghost_packet (q : MsgPacket) : RefinedPacket :=
  ⟨q.pSrc, q.pDst, q.pBody.2⟩

/-- `GhostSimulations.v:365-375` (`mgv_deghost`): the state is
untouched — only the wire loses its ghost. -/
def mgv_deghost (net : MsgNet) : RefinedNet :=
  ⟨net.nwPackets.map mgv_deghost_packet, net.nwState⟩

/-- `RaftMsgRefinementProof.v:908-917` (`msg_deghost_spec`). -/
theorem msg_deghost_spec (net : MsgNet) (h : name (P := P)) :
    (mgv_deghost net).nwState h = net.nwState h := rfl

/-- Deghosting ghost-attached sends yields plain refined sends. -/
theorem mgv_deghost_send_packets (src : name (P := P))
    (st : electionsData (P := P) × raft_data (P := P))
    (l : List (name (P := P) × msg (P := P))) :
    (send_packets (P := raft_msg_refined_base_params (P := P))
        (M := raft_msg_refined_multi_params) src
        (add_ghost_msg src st l)).map mgv_deghost_packet
      = send_packets (P := raft_refined_base_params (P := P))
          (M := raft_refined_multi_params) src l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [send_packets, add_ghost_msg, List.map_cons] at ih ⊢
    exact congrArg (List.cons _) ih

/-- `GhostSimulations.v` (`mgv_ghost_simulation_1`) at the raft
instance: every msg-ghost `step_failure` projects to a refined
`step_failure` between the deghosts (the state components are literally
shared, so only the packet lists move). -/
theorem mgv_ghost_simulation_1 {failed failed' : List (name (P := P))}
    {net net' : MsgNet} {out}
    (h : step_failure _ _ raft_msg_refined_failure_params (failed, net)
      (failed', net') out) :
    step_failure _ _ raft_refined_failure_params (failed, mgv_deghost net)
      (failed', mgv_deghost net') out := by
  cases h with
  | StepFailure_deliver net _ failed p xs ys out0 dfull l hpkts hlive hnh hnet' =>
    subst hnet'
    rcases hr : refined_net_handlers p.pDst p.pSrc p.pBody.2 (net.nwState p.pDst)
      with ⟨o, st2, ps⟩
    have hnh' : mgv_refined_net_handlers p.pDst p.pSrc p.pBody
        (net.nwState p.pDst) = (out0, dfull, l) := hnh
    unfold mgv_refined_net_handlers at hnh'
    rw [hr] at hnh'
    simp only [Prod.mk.injEq] at hnh'
    obtain ⟨rfl, rfl, rfl⟩ := hnh'
    refine .StepFailure_deliver (mgv_deghost net) _ failed
      (mgv_deghost_packet p) (xs.map mgv_deghost_packet)
      (ys.map mgv_deghost_packet) o st2 ps ?_ hlive hr ?_
    · show net.nwPackets.map mgv_deghost_packet = _
      rw [hpkts]
      simp
    · refine network_eq_mk ?_ (fun h' => rfl)
      show (send_packets p.pDst (add_ghost_msg p.pDst st2 ps) ++ xs ++ ys).map
        mgv_deghost_packet = _
      simp only [List.map_append, mgv_deghost_send_packets]
      rfl
  | StepFailure_input h net _ failed out0 inp dfull l hlive hih hnet' =>
    subst hnet'
    rcases hr : refined_input_handlers h inp (net.nwState h) with ⟨o, st2, ps⟩
    have hih' : mgv_refined_input_handlers h inp (net.nwState h)
        = (out0, dfull, l) := hih
    unfold mgv_refined_input_handlers at hih'
    rw [hr] at hih'
    simp only [Prod.mk.injEq] at hih'
    obtain ⟨rfl, rfl, rfl⟩ := hih'
    refine .StepFailure_input (M := raft_refined_multi_params (P := P)) h
      (mgv_deghost net) _ failed o inp st2 ps hlive hr ?_
    refine network_eq_mk ?_ (fun h' => rfl)
    show (send_packets h (add_ghost_msg h st2 ps) ++ net.nwPackets).map
      mgv_deghost_packet = _
    simp only [List.map_append, mgv_deghost_send_packets]
    rfl
  | StepFailure_drop net _ failed p xs ys hpkts hnet' =>
    subst hnet'
    refine .StepFailure_drop (mgv_deghost net) _ failed (mgv_deghost_packet p)
      (xs.map mgv_deghost_packet) (ys.map mgv_deghost_packet) ?_ ?_
    · show net.nwPackets.map mgv_deghost_packet = _
      rw [hpkts]
      simp
    · refine network_eq_mk ?_ (fun _ => rfl)
      show (xs ++ ys).map mgv_deghost_packet = _
      simp
  | StepFailure_dup net _ failed p xs ys hpkts hnet' =>
    subst hnet'
    refine .StepFailure_dup (mgv_deghost net) _ failed (mgv_deghost_packet p)
      (xs.map mgv_deghost_packet) (ys.map mgv_deghost_packet) ?_ ?_
    · show net.nwPackets.map mgv_deghost_packet = _
      rw [hpkts]
      simp
    · refine network_eq_mk ?_ (fun _ => rfl)
      show (p :: (xs ++ p :: ys)).map mgv_deghost_packet = _
      simp
  | StepFailure_fail h net failed =>
    exact .StepFailure_fail (M := raft_refined_multi_params (P := P)) h
      (mgv_deghost net) failed
  | StepFailure_reboot h net _ failed failed' hmem hfailed' hnet' =>
    subst hnet'
    exact .StepFailure_reboot (M := raft_refined_multi_params (P := P)) h
      (mgv_deghost net) _ failed failed' hmem hfailed'
      (network_eq_mk rfl (fun h' => rfl))

/-- `RaftMsgRefinementProof.v:566-645` (`simulation_1` /
`msg_simulation_1`): every msg-ghost reachable network deghosts to a
refined-reachable network. -/
theorem msg_simulation_1 :
    ∀ net : MsgNet, msg_refined_raft_intermediate_reachable (P := P) net →
      refined_raft_intermediate_reachable (mgv_deghost net) := by
  intro net hreach
  induction hreach with
  | MRRIR_init => exact .RRIR_init
  | MRRIR_step_failure failed net failed' net' out hreach hstep ih =>
    exact .RRIR_step_failure failed (mgv_deghost net) failed'
      (mgv_deghost net') _ ih (mgv_ghost_simulation_1 hstep)
  | MRRIR_handleInput net h inp out d l ps' st' hreach hi hst hps ih =>
    show refined_raft_intermediate_reachable
      ⟨ps'.map mgv_deghost_packet, st'⟩
    refine .RRIR_handleInput (mgv_deghost net) h inp out d l _ _ ih hi
      (fun h' => hst h') ?_
    intro p' hp'
    rcases List.mem_map.mp hp' with ⟨q, hq, rfl⟩
    rcases hps q hq with h1 | h1
    · exact Or.inl (List.mem_map_of_mem h1)
    · right
      rw [← mgv_deghost_send_packets h
        (update_elections_data_input h inp (net.nwState h), d) l]
      exact List.mem_map_of_mem h1
  | MRRIR_handleMessage p net xs ys st' ps' d l hreach hm hpkts hst hps ih =>
    show refined_raft_intermediate_reachable
      ⟨ps'.map mgv_deghost_packet, st'⟩
    refine .RRIR_handleMessage (mgv_deghost_packet p) (mgv_deghost net)
      (xs.map mgv_deghost_packet) (ys.map mgv_deghost_packet) _ _ d l ih
      hm ?_ (fun h' => hst h') ?_
    · show net.nwPackets.map mgv_deghost_packet = _
      rw [hpkts]
      simp
    · intro p' hp'
      rcases List.mem_map.mp hp' with ⟨q, hq, rfl⟩
      rcases hps q hq with h1 | h1
      · left
        rw [← List.map_append]
        exact List.mem_map_of_mem h1
      · right
        show mgv_deghost_packet q ∈ send_packets
          (P := raft_refined_base_params (P := P))
          (M := raft_refined_multi_params) p.pDst l
        rw [← mgv_deghost_send_packets p.pDst
          (update_elections_data_net p.pDst p.pSrc p.pBody.2
            (net.nwState p.pDst), d) l]
        exact List.mem_map_of_mem h1
  | MRRIR_doLeader net st' ps' gd d h os d' ms hreach hdo hstate hst hps ih =>
    show refined_raft_intermediate_reachable
      ⟨ps'.map mgv_deghost_packet, st'⟩
    refine .RRIR_doLeader (mgv_deghost net) _ _ h os d' ms ih ?_ ?_ ?_
    · show doLeader ((mgv_deghost net).nwState h).2 h = (os, d', ms)
      rw [msg_deghost_spec, hstate]
      exact hdo
    · intro h'
      rw [hst h']
      show update net.nwState h (gd, d') h'
        = update net.nwState h ((net.nwState h).1, d') h'
      rw [hstate]
    · intro q hq
      rcases List.mem_map.mp hq with ⟨q0, hq0, rfl⟩
      rcases hps q0 hq0 with h1 | h1
      · exact Or.inl (List.mem_map_of_mem h1)
      · right
        rw [← mgv_deghost_send_packets h (gd, d') ms]
        exact List.mem_map_of_mem h1
  | MRRIR_doGenericServer net st' ps' gd d h os d' ms hreach hdo hstate hst hps ih =>
    show refined_raft_intermediate_reachable
      ⟨ps'.map mgv_deghost_packet, st'⟩
    refine .RRIR_doGenericServer (mgv_deghost net) _ _ h os d' ms ih ?_ ?_ ?_
    · show doGenericServer h ((mgv_deghost net).nwState h).2 = (os, d', ms)
      rw [msg_deghost_spec, hstate]
      exact hdo
    · intro h'
      rw [hst h']
      show update net.nwState h (gd, d') h'
        = update net.nwState h ((net.nwState h).1, d') h'
      rw [hstate]
    · intro q hq
      rcases List.mem_map.mp hq with ⟨q0, hq0, rfl⟩
      rcases hps q0 hq0 with h1 | h1
      · exact Or.inl (List.mem_map_of_mem h1)
      · right
        rw [← mgv_deghost_send_packets h (gd, d') ms]
        exact List.mem_map_of_mem h1

/-- `RaftMsgRefinementProof.v:646-654` (`msg_lift_prop`): refined-layer
invariants import into msg-ghost proofs through the deghost. -/
theorem msg_lift_prop (Pr : RefinedNet → Prop)
    (href : ∀ net, refined_raft_intermediate_reachable (P := P) net → Pr net) :
    ∀ net, msg_refined_raft_intermediate_reachable (P := P) net →
      Pr (mgv_deghost net) :=
  fun net h => href _ (msg_simulation_1 net h)

/-- `RaftMsgRefinementInterface.v` (`msg_lift_prop_all_the_way`): base
invariants import through both erasures. -/
theorem msg_lift_prop_all_the_way (Pr : _ → Prop)
    (hbase : ∀ net, raft_intermediate_reachable (P := P) net → Pr net) :
    ∀ net, msg_refined_raft_intermediate_reachable (P := P) net →
      Pr (deghost (mgv_deghost net)) :=
  fun net h => lift_prop Pr hbase _ (msg_simulation_1 net h)

/-! ## The §3.3 discharge witness

A real (if small) ghost invariant instantiating THE principle with all
eleven obligations discharged: every entry of every in-flight ghost log
has a positive index. Deliberately NOT one of the GhostLog* chain's
named statements (unit 1's `VotesShape` discipline — no pre-emption);
it exercises every obligation's packet clause, every handler's log
shape, and the `msg_simulation_1`/`msg_lift_prop` import path. -/

/-- Every in-flight ghost log's entries have positive indices. -/
def ghost_entries_gt_0 (net : MsgNet) : Prop :=
  ∀ p ∈ net.nwPackets, ∀ e ∈ (p.pBody :
    ghost_log (P := P) × msg (P := P)).1, e.eIndex > 0

/-- The ghost of a freshly sent packet is the writing state's log. -/
theorem ghost_of_send {src : name (P := P)}
    {st : electionsData (P := P) × raft_data (P := P)}
    {l : List (name (P := P) × msg (P := P))} {p : MsgPacket}
    (hp : p ∈ send_packets src (add_ghost_msg src st l)) :
    (p.pBody : ghost_log (P := P) × msg (P := P)).1 = st.2.log := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  obtain ⟨m1, hm1, rfl⟩ := List.mem_map.mp hq
  rfl

/-- Host logs of a msg-reachable net have positive indices — the
refined `entries_gt_0` imported through `msg_lift_prop`
(the transfer's first consumer). -/
theorem ghost_entries_host_gt_0 {net : MsgNet}
    (hreach : msg_refined_raft_intermediate_reachable (P := P) net)
    (h : name (P := P)) :
    ∀ e ∈ (net.nwState h).2.log, e.eIndex > 0 := by
  intro e he
  exact entries_gt_0_invariant (mgv_deghost net)
    (msg_simulation_1 net hreach) h e he

theorem ghost_entries_gt_0_invariant :
    ∀ net, msg_refined_raft_intermediate_reachable (P := P) net →
      ghost_entries_gt_0 net := by
  refine msg_refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init: no packets
    intro p hp
    exact nomatch hp
  · -- client_request: the fresh ghost is the appended log
    intro h net st' ps' gd out d l client id c hcr hgd hP hreach hst hps
    intro p hp e he
    replace hp : p ∈ ps' := hp
    rcases hps p hp with hold | hnew
    · exact hP p hold e he
    · rw [ghost_of_send hnew] at he
      replace he : e ∈ d.log := he
      rcases handleClientRequest_log_full h (net.nwState h).2 client id c
          hcr with ⟨-, hlog⟩ | ⟨-, hdeq⟩
      · rw [hlog] at he
        rcases List.mem_cons.mp he with rfl | he
        · exact Nat.succ_pos _
        · exact ghost_entries_host_gt_0 hreach h e he
      · rw [hdeq] at he
        exact ghost_entries_host_gt_0 hreach h e he
  · -- timeout: log unchanged
    intro net h st' ps' gd out d l hto hgd hP hreach hst hps
    intro p hp e he
    replace hp : p ∈ ps' := hp
    rcases hps p hp with hold | hnew
    · exact hP p hold e he
    · rw [ghost_of_send hnew] at he
      replace he : e ∈ d.log := he
      obtain ⟨hlog, -, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
      rw [hlog] at he
      exact ghost_entries_host_gt_0 hreach h e he
  · -- append_entries: the reply ghost is the (possibly spliced) log
    intro xs p ys net st' ps' gd d m t n pli plt es ci hae hgd hbody hP
      hreach hpkts hst hps
    intro p0 hp0 e he
    replace hp0 : p0 ∈ ps' := hp0
    have hes_pos : ∀ e0 ∈ es, e0.eIndex > 0 := by
      intro e0 he0
      refine entries_gt_0_nw_invariant (mgv_deghost net)
        (msg_simulation_1 net hreach) (mgv_deghost_packet p) t n pli plt
        es ci e0 ?_ hbody he0
      show mgv_deghost_packet p ∈ net.nwPackets.map mgv_deghost_packet
      refine List.mem_map_of_mem ?_
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    rcases hps p0 hp0 with hold | rfl
    · exact hP p0 (by rw [hpkts]; exact mem_of_mem_remove_middle hold) e he
    · replace he : e ∈ d.log := he
      rcases handleAppendEntries_log_cases p.pDst (net.nwState p.pDst).2
          t n pli plt es ci hae with hd | ⟨-, hd⟩ |
        ⟨e2, -, -, -, hd⟩
      · rw [hd] at he
        exact ghost_entries_host_gt_0 hreach p.pDst e he
      · rw [hd] at he
        exact hes_pos e he
      · rw [hd] at he
        rcases List.mem_append.mp he with he | he
        · exact hes_pos e he
        · exact ghost_entries_host_gt_0 hreach p.pDst e
            (removeAfterIndex_in he)
  · -- append_entries_reply: log unchanged
    intro xs p ys net st' ps' gd d m t es res haer hgd hbody hP hreach
      hpkts hst hps
    intro p0 hp0 e he
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · exact hP p0 (by rw [hpkts]; exact mem_of_mem_remove_middle hold) e he
    · rw [ghost_of_send hnew] at he
      replace he : e ∈ d.log := he
      rw [handleAppendEntriesReply_log p.pDst (net.nwState p.pDst).2
        p.pSrc t es res haer] at he
      exact ghost_entries_host_gt_0 hreach p.pDst e he
  · -- request_vote: log unchanged
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd hbody hP
      hreach hpkts hst hps
    intro p0 hp0 e he
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | rfl
    · exact hP p0 (by rw [hpkts]; exact mem_of_mem_remove_middle hold) e he
    · replace he : e ∈ d.log := he
      rw [handleRequestVote_log p.pDst (net.nwState p.pDst).2 t p.pSrc
        lli llt hrv] at he
      exact ghost_entries_host_gt_0 hreach p.pDst e he
  · -- request_vote_reply: no sends
    intro xs p ys net st' ps' gd d t v hrvr hgd hbody hP hreach hpkts
      hst hps
    intro p0 hp0 e he
    replace hp0 : p0 ∈ ps' := hp0
    exact hP p0 (by rw [hpkts]; exact mem_of_mem_remove_middle (hps p0 hp0))
      e he
  · -- do_leader: log unchanged
    intro net st' ps' gd d h os d' ms hdl hP hreach hstate hst hps
    intro p hp e he
    replace hp : p ∈ ps' := hp
    rcases hps p hp with hold | hnew
    · exact hP p hold e he
    · rw [ghost_of_send hnew] at he
      replace he : e ∈ d'.log := he
      obtain ⟨-, -, -, -, hlog, -⟩ := doLeader_spec d h hdl
      rw [hlog] at he
      have hd2 : d = (net.nwState h).2 := by rw [hstate]
      rw [hd2] at he
      exact ghost_entries_host_gt_0 hreach h e he
  · -- do_generic_server: log unchanged
    intro net st' ps' gd d os d' ms h hdgs hP hreach hstate hst hps
    intro p hp e he
    replace hp : p ∈ ps' := hp
    rcases hps p hp with hold | hnew
    · exact hP p hold e he
    · rw [ghost_of_send hnew] at he
      replace he : e ∈ d'.log := he
      obtain ⟨hlog, -, -, -, -, -⟩ := doGenericServer_spec h d hdgs
      rw [hlog] at he
      have hd2 : d = (net.nwState h).2 := by rw [hstate]
      rw [hd2] at he
      exact ghost_entries_host_gt_0 hreach h e he
  · -- state_same_packet_subset
    intro net net' hstate hpk hP hreach
    intro p hp e he
    exact hP p (hpk p hp) e he
  · -- reboot: packets unchanged
    intro net net' gd d h d' hrb hP hreach hstate hst hpkts
    intro p hp e he
    rw [← hpkts] at hp
    exact hP p hp e he

end MsgRefinement
end Raft
end VerdiCompat
