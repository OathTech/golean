import VerdiCompat.Raft

/-!
# verdi-raft's proof scaffold, re-proved in Lean

1:1 port of `deps/verdi-raft/theories/Raft/Raft.v:556-848`: the
`raft_net_invariant_*` per-handler obligation shapes, the two dispatcher
lemmas, THE induction principle `raft_net_invariant`, and the
`step_failure_star → raft_intermediate_reachable` bridge.

This is the load-bearing feasibility demonstration for "import the Verdi
proof structure": verdi-raft proves its invariants by instantiating
handler-indexed induction principles of exactly this shape — ~17 of the
90 RaftProofs files instantiate `raft_net_invariant` directly, and the
rest instantiate its same-shaped ghost-layer twin
`refined_raft_net_invariant` (`RaftRefinementProof.v`, not yet ported —
a known-shape repeat of this file). With the principle proved in Lean,
extending the model (new messages, new handlers) means extending the
obligation list — the proof architecture transfers even where individual
proofs must be redone.

Naming: Coq's invariant variable `P` is `Pr` here (`P` is our `BaseParams`
section variable). Proofs are re-proved from scratch (Ltac does not port);
the STATEMENTS are 1:1.
-/

namespace VerdiCompat
namespace Raft

section ProofStructure
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

local notation "RaftNet" => Network (raft_base_params (P := P)) raft_multi_params
local notation "RaftPacket" => Packet (raft_base_params (P := P)) raft_multi_params

/-- `Raft.v:594-602` -/
def raft_net_invariant_client_request (Pr : RaftNet → Prop) : Prop :=
  ∀ (h : name (P := P)) (net : RaftNet) st' ps' out d l client id c,
    handleClientRequest h (net.nwState h) client id c = (out, d, l) →
    Pr net →
    raft_intermediate_reachable net →
    (∀ h', st' h' = update net.nwState h d h') →
    (∀ p', p' ∈ ps' → p' ∈ net.nwPackets ∨ p' ∈ send_packets h l) →
    Pr ⟨ps', st'⟩

/-- `Raft.v:604-612` -/
def raft_net_invariant_timeout (Pr : RaftNet → Prop) : Prop :=
  ∀ (net : RaftNet) (h : name (P := P)) st' ps' out d l,
    handleTimeout h (net.nwState h) = (out, d, l) →
    Pr net →
    raft_intermediate_reachable net →
    (∀ h', st' h' = update net.nwState h d h') →
    (∀ p', p' ∈ ps' → p' ∈ net.nwPackets ∨ p' ∈ send_packets h l) →
    Pr ⟨ps', st'⟩

/-- `Raft.v:614-624` -/
def raft_net_invariant_append_entries (Pr : RaftNet → Prop) : Prop :=
  ∀ xs (p : RaftPacket) ys (net : RaftNet) st' ps' d m t n pli plt es ci,
    handleAppendEntries p.pDst (net.nwState p.pDst) t n pli plt es ci = (d, m) →
    p.pBody = .AppendEntries t n pli plt es ci →
    Pr net →
    raft_intermediate_reachable net →
    net.nwPackets = xs ++ p :: ys →
    (∀ h, st' h = update net.nwState p.pDst d h) →
    (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys) ∨ p' = (⟨p.pDst, p.pSrc, m⟩ : RaftPacket)) →
    Pr ⟨ps', st'⟩

/-- `Raft.v:626-636` -/
def raft_net_invariant_append_entries_reply (Pr : RaftNet → Prop) : Prop :=
  ∀ xs (p : RaftPacket) ys (net : RaftNet) st' ps' d m t es res,
    handleAppendEntriesReply p.pDst (net.nwState p.pDst) p.pSrc t es res = (d, m) →
    p.pBody = .AppendEntriesReply t es res →
    Pr net →
    raft_intermediate_reachable net →
    net.nwPackets = xs ++ p :: ys →
    (∀ h, st' h = update net.nwState p.pDst d h) →
    (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys) ∨ p' ∈ send_packets p.pDst m) →
    Pr ⟨ps', st'⟩

/-- `Raft.v:638-648` -/
def raft_net_invariant_request_vote (Pr : RaftNet → Prop) : Prop :=
  ∀ xs (p : RaftPacket) ys (net : RaftNet) st' ps' d m t cid lli llt,
    handleRequestVote p.pDst (net.nwState p.pDst) t p.pSrc lli llt = (d, m) →
    p.pBody = .RequestVote t cid lli llt →
    Pr net →
    raft_intermediate_reachable net →
    net.nwPackets = xs ++ p :: ys →
    (∀ h, st' h = update net.nwState p.pDst d h) →
    (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys) ∨ p' = (⟨p.pDst, p.pSrc, m⟩ : RaftPacket)) →
    Pr ⟨ps', st'⟩

/-- `Raft.v:650-659` -/
def raft_net_invariant_request_vote_reply (Pr : RaftNet → Prop) : Prop :=
  ∀ xs (p : RaftPacket) ys (net : RaftNet) st' ps' d t v,
    handleRequestVoteReply p.pDst (net.nwState p.pDst) p.pSrc t v = d →
    p.pBody = .RequestVoteReply t v →
    Pr net →
    raft_intermediate_reachable net →
    net.nwPackets = xs ++ p :: ys →
    (∀ h, st' h = update net.nwState p.pDst d h) →
    (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys)) →
    Pr ⟨ps', st'⟩

/-- `Raft.v:661-670` -/
def raft_net_invariant_do_leader (Pr : RaftNet → Prop) : Prop :=
  ∀ (net : RaftNet) st' ps' d (h : name (P := P)) os d' ms,
    doLeader d h = (os, d', ms) →
    Pr net →
    raft_intermediate_reachable net →
    net.nwState h = d →
    (∀ h', st' h' = update net.nwState h d' h') →
    (∀ p, p ∈ ps' → p ∈ net.nwPackets ∨ p ∈ send_packets h ms) →
    Pr ⟨ps', st'⟩

/-- `Raft.v:672-681` -/
def raft_net_invariant_do_generic_server (Pr : RaftNet → Prop) : Prop :=
  ∀ (net : RaftNet) st' ps' d os d' ms (h : name (P := P)),
    doGenericServer h d = (os, d', ms) →
    Pr net →
    raft_intermediate_reachable net →
    net.nwState h = d →
    (∀ h', st' h' = update net.nwState h d' h') →
    (∀ p, p ∈ ps' → p ∈ net.nwPackets ∨ p ∈ send_packets h ms) →
    Pr ⟨ps', st'⟩

/-- `Raft.v:728-734` -/
def raft_net_invariant_state_same_packet_subset (Pr : RaftNet → Prop) : Prop :=
  ∀ net net' : RaftNet,
    (∀ h, net.nwState h = net'.nwState h) →
    (∀ p, p ∈ net'.nwPackets → p ∈ net.nwPackets) →
    Pr net →
    raft_intermediate_reachable net →
    Pr net'

/-- `Raft.v:736-744` -/
def raft_net_invariant_reboot (Pr : RaftNet → Prop) : Prop :=
  ∀ (net net' : RaftNet) d (h : name (P := P)) d',
    reboot d = d' →
    Pr net →
    raft_intermediate_reachable net →
    net.nwState h = d →
    (∀ h', net'.nwState h' = update net.nwState h d' h') →
    net.nwPackets = net'.nwPackets →
    Pr net'

/-- `Raft.v:746-747` -/
def raft_net_invariant_init (Pr : RaftNet → Prop) : Prop :=
  Pr (step_async_init _ _)

/-- `Raft.v:683-706` — dispatch a `handleMessage` step to the per-message
obligations. -/
theorem raft_invariant_handle_message {Pr : RaftNet → Prop}
    (hae : raft_net_invariant_append_entries Pr)
    (haer : raft_net_invariant_append_entries_reply Pr)
    (hrv : raft_net_invariant_request_vote Pr)
    (hrvr : raft_net_invariant_request_vote_reply Pr) :
    ∀ xs (p : RaftPacket) ys (net : RaftNet) st' ps' d l,
      handleMessage p.pSrc p.pDst p.pBody (net.nwState p.pDst) = (d, l) →
      Pr net →
      raft_intermediate_reachable net →
      net.nwPackets = xs ++ p :: ys →
      (∀ h, st' h = update net.nwState p.pDst d h) →
      (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys) ∨ p' ∈ send_packets p.pDst l) →
      Pr ⟨ps', st'⟩ := by
  intro xs p ys net st' ps' d l hm hP hreach hpkts hst hps
  unfold handleMessage at hm
  cases hbody : p.pBody with
  | AppendEntries t lid pli plt es ci =>
    rw [hbody] at hm
    simp only [] at hm
    rcases hh : handleAppendEntries p.pDst (net.nwState p.pDst) t lid pli plt es ci
      with ⟨d0, r0⟩
    rw [hh] at hm
    simp only [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact hae xs p ys net st' ps' d0 r0 t lid pli plt es ci hh hbody hP hreach hpkts hst
      (fun p' hp' => by
        rcases hps p' hp' with h | h
        · exact Or.inl h
        · right
          have h' : p' ∈ [(⟨p.pDst, p.pSrc, r0⟩ : RaftPacket)] := h
          simpa using h')
  | AppendEntriesReply t es res =>
    rw [hbody] at hm
    simp only [] at hm
    exact haer xs p ys net st' ps' d l t es res hm hbody hP hreach hpkts hst hps
  | RequestVote t cid lli llt =>
    rw [hbody] at hm
    simp only [] at hm
    rcases hh : handleRequestVote p.pDst (net.nwState p.pDst) t p.pSrc lli llt
      with ⟨d0, r0⟩
    rw [hh] at hm
    simp only [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact hrv xs p ys net st' ps' d0 r0 t cid lli llt hh hbody hP hreach hpkts hst
      (fun p' hp' => by
        rcases hps p' hp' with h | h
        · exact Or.inl h
        · right
          have h' : p' ∈ [(⟨p.pDst, p.pSrc, r0⟩ : RaftPacket)] := h
          simpa using h')
  | RequestVoteReply t v =>
    rw [hbody] at hm
    simp only [] at hm
    simp only [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact hrvr xs p ys net st' ps' _ t v rfl hbody hP hreach hpkts hst
      (fun p' hp' => by
        rcases hps p' hp' with h | h
        · exact h
        · simp [send_packets] at h)

/-- `Raft.v:708-726` — dispatch a `handleInput` step. -/
theorem raft_invariant_handle_input {Pr : RaftNet → Prop}
    (hto : raft_net_invariant_timeout Pr)
    (hcr : raft_net_invariant_client_request Pr) :
    ∀ (h : name (P := P)) inp (net : RaftNet) st' ps' out d l,
      handleInput h inp (net.nwState h) = (out, d, l) →
      Pr net →
      raft_intermediate_reachable net →
      (∀ h', st' h' = update net.nwState h d h') →
      (∀ p', p' ∈ ps' → p' ∈ net.nwPackets ∨ p' ∈ send_packets h l) →
      Pr ⟨ps', st'⟩ := by
  intro h inp net st' ps' out d l hi hP hreach hst hps
  unfold handleInput at hi
  cases inp with
  | Timeout => exact hto net h st' ps' out d l hi hP hreach hst hps
  | ClientRequest client id c =>
    exact hcr h net st' ps' out d l client id c hi hP hreach hst hps

/-- `Raft.v:749-848` — THE induction principle: an invariant holds of every
`raft_intermediate_reachable` network iff it is preserved by each handler
step (plus init, packet-subset, and reboot obligations). Verdi proves all
~90 of its invariants by instantiating exactly this. Re-proved here from
scratch (the Coq proof is 100 lines of Ltac). -/
theorem raft_net_invariant {Pr : RaftNet → Prop}
    (hinit : raft_net_invariant_init Pr)
    (hcr : raft_net_invariant_client_request Pr)
    (hto : raft_net_invariant_timeout Pr)
    (hae : raft_net_invariant_append_entries Pr)
    (haer : raft_net_invariant_append_entries_reply Pr)
    (hrv : raft_net_invariant_request_vote Pr)
    (hrvr : raft_net_invariant_request_vote_reply Pr)
    (hdl : raft_net_invariant_do_leader Pr)
    (hgs : raft_net_invariant_do_generic_server Pr)
    (hsub : raft_net_invariant_state_same_packet_subset Pr)
    (hreb : raft_net_invariant_reboot Pr) :
    ∀ net, raft_intermediate_reachable (P := P) net → Pr net := by
  intro net hreach
  induction hreach with
  | RIR_init => exact hinit
  | RIR_handleInput net h inp out d l ps' st' hreach hi hst hps ih =>
    exact raft_invariant_handle_input hto hcr h inp net st' ps' out d l hi ih hreach hst hps
  | RIR_handleMessage p net xs ys st' ps' d l hreach hm hpkts hst hps ih =>
    exact raft_invariant_handle_message hae haer hrv hrvr xs p ys net st' ps' d l
      hm ih hreach hpkts hst hps
  | RIR_doLeader net st' ps' h os d' ms hreach hdo hst hps ih =>
    exact hdl net st' ps' _ h os d' ms hdo ih hreach rfl hst hps
  | RIR_doGenericServer net st' ps' os d' ms h hreach hdo hst hps ih =>
    exact hgs net st' ps' _ os d' ms h hdo ih hreach rfl hst hps
  | RIR_step_failure failed net failed' net' out hreach hstep ih =>
    cases hstep with
    | StepFailure_deliver net _ failed p xs ys out' d l hpkts hlive hnh hnet' =>
      -- decompose RaftNetHandler = handleMessage ; doLeader ; doGenericServer
      rcases hm : handleMessage p.pSrc p.pDst p.pBody (net.nwState p.pDst) with ⟨d0, l0⟩
      rcases hl : doLeader d0 p.pDst with ⟨o1, d1, l1⟩
      rcases hg : doGenericServer p.pDst d1 with ⟨o2, d2, l2⟩
      have hnh' : (o1 ++ o2, d2, l0 ++ l1 ++ l2) = (out', d, l) := by
        have hnh : RaftNetHandler p.pDst p.pSrc p.pBody (net.nwState p.pDst)
            = (out', d, l) := hnh
        unfold RaftNetHandler at hnh
        rw [hm] at hnh
        simp only [] at hnh
        rw [hl] at hnh
        simp only [] at hnh
        rw [hg] at hnh
        simpa using hnh
      simp only [Prod.mk.injEq] at hnh'
      obtain ⟨-, rfl, rfl⟩ := hnh'
      subst hnet'
      -- intermediate reachable states, mirroring the Coq assert chain
      have hnet1 : raft_intermediate_reachable (P := P)
          ⟨(xs ++ ys) ++ send_packets p.pDst l0,
           update net.nwState p.pDst d0⟩ :=
        .RIR_handleMessage p net xs ys _ _ d0 l0 hreach hm hpkts (fun _ => rfl)
          (fun p' hp' => by simpa using (List.mem_append.mp hp'))
      have hstate1 : (update net.nwState p.pDst d0) p.pDst = d0 := update_same ..
      have hnet2 : raft_intermediate_reachable (P := P)
          ⟨((xs ++ ys) ++ send_packets p.pDst l0) ++ send_packets p.pDst l1,
           update (update net.nwState p.pDst d0) p.pDst d1⟩ :=
        .RIR_doLeader ⟨(xs ++ ys) ++ send_packets p.pDst l0,
            update net.nwState p.pDst d0⟩ _ _ p.pDst o1 d1 l1 hnet1
          (by show doLeader (update net.nwState p.pDst d0 p.pDst) p.pDst = (o1, d1, l1)
              rw [hstate1]; exact hl)
          (fun _ => rfl)
          (fun q hq => by simpa using (List.mem_append.mp hq))
      -- P net1 via the message dispatcher
      have hP1 : Pr ⟨(xs ++ ys) ++ send_packets p.pDst l0,
          update net.nwState p.pDst d0⟩ :=
        raft_invariant_handle_message hae haer hrv hrvr xs p ys net _ _ d0 l0 hm ih
          hreach hpkts (fun _ => rfl)
          (fun p' hp' => List.mem_append.mp hp')
      -- P net2 via the do_leader obligation
      have hP2 : Pr ⟨((xs ++ ys) ++ send_packets p.pDst l0) ++ send_packets p.pDst l1,
          update (update net.nwState p.pDst d0) p.pDst d1⟩ :=
        hdl ⟨(xs ++ ys) ++ send_packets p.pDst l0, update net.nwState p.pDst d0⟩
          _ _ d0 p.pDst o1 d1 l1 hl hP1 hnet1 hstate1
          (fun h' => by rw [update_update_same])
          (fun q hq => List.mem_append.mp hq)
      -- conclude via the do_generic_server obligation on net2
      refine hgs ⟨((xs ++ ys) ++ send_packets p.pDst l0) ++ send_packets p.pDst l1,
          update (update net.nwState p.pDst d0) p.pDst d1⟩
        _ _ d1 o2 d2 l2 p.pDst hg hP2 hnet2 (by simp) ?_ ?_
      · intro h'
        simp only [update_update_same]
      · intro q hq
        rw [send_packets_app, send_packets_app] at hq
        simp only [List.mem_append] at hq ⊢
        -- hq : (((l0 ∨ l1) ∨ l2) ∨ xs) ∨ ys ; ⊢ (((xs ∨ ys) ∨ l0) ∨ l1) ∨ l2
        rcases hq with (((h | h) | h) | h) | h
        · exact Or.inl (Or.inl (Or.inr h))
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
        · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
        · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    | StepFailure_input h net _ failed out' inp d l hlive hih hnet' =>
      rcases hi : handleInput h inp (net.nwState h) with ⟨o0, d0, l0⟩
      rcases hl : doLeader d0 h with ⟨o1, d1, l1⟩
      rcases hg : doGenericServer h d1 with ⟨o2, d2, l2⟩
      have hih' : (o0 ++ o1 ++ o2, d2, l0 ++ l1 ++ l2) = (out', d, l) := by
        have hih : RaftInputHandler h inp (net.nwState h) = (out', d, l) := hih
        unfold RaftInputHandler at hih
        rw [hi] at hih
        simp only [] at hih
        rw [hl] at hih
        simp only [] at hih
        rw [hg] at hih
        simpa using hih
      simp only [Prod.mk.injEq] at hih'
      obtain ⟨-, rfl, rfl⟩ := hih'
      subst hnet'
      have hnet1 : raft_intermediate_reachable (P := P)
          ⟨net.nwPackets ++ send_packets h l0, update net.nwState h d0⟩ :=
        .RIR_handleInput net h inp o0 d0 l0 _ _ hreach hi (fun _ => rfl)
          (fun p' hp' => List.mem_append.mp hp')
      have hstate1 : (update net.nwState h d0) h = d0 := update_same ..
      have hnet2 : raft_intermediate_reachable (P := P)
          ⟨(net.nwPackets ++ send_packets h l0) ++ send_packets h l1,
           update (update net.nwState h d0) h d1⟩ :=
        .RIR_doLeader ⟨net.nwPackets ++ send_packets h l0, update net.nwState h d0⟩
          _ _ h o1 d1 l1 hnet1
          (by show doLeader (update net.nwState h d0 h) h = (o1, d1, l1)
              rw [hstate1]; exact hl)
          (fun _ => rfl)
          (fun q hq => List.mem_append.mp hq)
      have hP1 : Pr ⟨net.nwPackets ++ send_packets h l0, update net.nwState h d0⟩ :=
        raft_invariant_handle_input hto hcr h inp net _ _ o0 d0 l0 hi ih hreach
          (fun _ => rfl) (fun p' hp' => List.mem_append.mp hp')
      have hP2 : Pr ⟨(net.nwPackets ++ send_packets h l0) ++ send_packets h l1,
          update (update net.nwState h d0) h d1⟩ :=
        hdl ⟨net.nwPackets ++ send_packets h l0, update net.nwState h d0⟩
          _ _ d0 h o1 d1 l1 hl hP1 hnet1 hstate1
          (fun h' => by rw [update_update_same])
          (fun q hq => List.mem_append.mp hq)
      refine hgs ⟨(net.nwPackets ++ send_packets h l0) ++ send_packets h l1,
          update (update net.nwState h d0) h d1⟩
        _ _ d1 o2 d2 l2 h hg hP2 hnet2 (by simp) ?_ ?_
      · intro h'
        simp only [update_update_same]
      · intro q hq
        rw [send_packets_app, send_packets_app] at hq
        simp only [List.mem_append] at hq ⊢
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
      -- hq : (q = p ∨ q ∈ xs) ∨ (q = p ∨ q ∈ ys) ; ⊢ q ∈ xs ∨ q = p ∨ q ∈ ys
      rcases hq with (h | h) | (h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    | StepFailure_fail h net failed => exact ih
    | StepFailure_reboot h net _ failed failed' hmem hfailed' hnet' =>
      subst hnet'
      exact hreb net _ (net.nwState h) h _ rfl ih hreach rfl (fun _ => rfl) rfl

/-- `Raft.v:579-592` — reachability extends along `step_failure` chains. -/
theorem step_failure_star_raft_intermediate_reachable_extend :
    ∀ (x x' : List (name (P := P)) × Network (raft_base_params (P := P)) raft_multi_params) tr,
      refl_trans_1n_trace (step_failure _ _ raft_failure_params) x x' tr →
      raft_intermediate_reachable x.2 →
      raft_intermediate_reachable x'.2 := by
  intro x x' tr h
  induction h with
  | RT1nTBase _ => exact id
  | RT1nTStep a b c cs cs' hstep _ ih =>
    intro ha
    exact ih (.RIR_step_failure a.1 a.2 b.1 b.2 cs ha hstep)

/-- `Raft.v:569-577` — every network reachable in the full fault model
(from the initial state) is `raft_intermediate_reachable`; composing with
`raft_net_invariant` turns any handler-wise invariant into a property of
all `step_failure` traces. -/
theorem step_failure_star_raft_intermediate_reachable
    {failed : List (name (P := P))} {net tr}
    (h : step_failure_star _ _ raft_failure_params (step_failure_init _ _)
          (failed, net) tr) :
    raft_intermediate_reachable net :=
  step_failure_star_raft_intermediate_reachable_extend _ _ _ h .RIR_init

end ProofStructure

end Raft
end VerdiCompat
