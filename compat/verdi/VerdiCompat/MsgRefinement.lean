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

end MsgRefinement
end Raft
end VerdiCompat
