import VerdiCompat.SafetyPrime

/-!
# W-E: MatchIndexAllEntries — the last pre-cap file

Campaign Arc 3 unit 15 (closure in the arc log's unit-15 opening
entry), 1:1 against `Raft/MatchIndexAllEntriesInterface.v` /
`RaftProofs/MatchIndexAllEntriesProof.v` (1,134 lines) @ a3375e8:
every entry at or below a leader's matchIndex estimate for a follower
`h`, in the leader's own log at the leader's current term, is recorded
in `h`'s `allEntries` — the bridge from replication bookkeeping to the
ghost record that `StateMachineSafetyProof.v`'s commit argument reads.

THE FIRST CONSUMER OF THE STATE-SIDE PRIMED PRINCIPLE
(`refined_raft_net_invariant'`, GAP-1's first genuine trigger — the
per-site decision is logged in the unit-15 opening entry): upstream's
assembly (:1101-1127) takes the append_entries obligation PRIMED and
every other handler through a `_'_weak` bridge. The AE case's
fresh-reply half certifies the reply's entries against the RECEIVER's
post-splice log and allEntries via `entries_match_invariant` and
`log_all_entries_invariant` AT THE SUCCESSOR NET — exactly what the
successor-reachability premise licenses.

Route notes (§9 guided re-proof; statements 1:1, routes re-derived
where the lane already holds the fact at invariant level):

- upstream's `appendEntries_sublog` (:472-498) IS the lane's
  `append_entries_leader_invariant` (unit 7) — not re-proved;
- upstream's `handleAppendEntries_success_allEntries` (:365-432, the
  entries_match-premise analysis) dissolves into
  `handleAppendEntries_true_reply_log` +
  `appendEntries_haveNewEntries_false` (unit 8), which already package
  the accept/no-new-entries dichotomy at the invariant level;
- upstream's `handleAppendEntries_post_leader_nop`/`_leader_was_leader`
  + `lifted_no_AE_to_leader` detour (:279-338) dissolves into unit 9's
  `update_elections_data_appendEntries_log_allEntries_leader` (an AE
  that leaves you Leader was a rejection — state AND ghost unmoved),
  so the still-leader receiver case needs no `no_AE_to_leader` at all.
-/

namespace VerdiCompat
namespace Raft

section MatchIndexAllEntries
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

local notation "RefinedNet" =>
  Network (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RefinedPacket" =>
  Packet (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RaftNet" =>
  Network (raft_base_params (P := P)) raft_multi_params
local notation "RaftPacket" =>
  Packet (raft_base_params (P := P)) raft_multi_params

/-- `MatchIndexAllEntriesInterface.v:8-16` (`match_index_all_entries`). -/
def match_index_all_entries (net : RefinedNet) : Prop :=
  ∀ (e : entry (P := P)) (leader h : name (P := P)),
    (net.nwState leader).2.type = .Leader →
    e.eIndex ≤ assoc_default (net.nwState leader).2.matchIndex h 0 →
    e ∈ (net.nwState leader).2.log →
    e.eTerm = (net.nwState leader).2.currentTerm →
    (e.eTerm, e) ∈ (net.nwState h).1.allEntries

/-- `MatchIndexAllEntriesProof.v:46-55` (`match_index_all_entries_nw`):
the in-flight companion — a true AppendEntriesReply at the leader's
term certifies its entries into the SENDER's allEntries. -/
def match_index_all_entries_nw (net : RefinedNet) : Prop :=
  ∀ (p : RefinedPacket) (t : term) (es : List (entry (P := P)))
    (e : entry (P := P)),
    p ∈ net.nwPackets →
    p.pBody = .AppendEntriesReply t es true →
    (net.nwState p.pDst).2.currentTerm = t →
    e ∈ (net.nwState p.pDst).2.log →
    e.eTerm = t →
    e.eIndex ≤ maxIndex es →
    (net.nwState p.pDst).2.type = .Leader →
    (t, e) ∈ (net.nwState p.pSrc).1.allEntries

/-- `MatchIndexAllEntriesProof.v:57-58` (`match_index_all_entries_inv`). -/
def match_index_all_entries_inv (net : RefinedNet) : Prop :=
  match_index_all_entries net ∧ match_index_all_entries_nw net

/-! ## Lifted base facts (`MatchIndexAllEntriesProof.v:91-131`) -/

/-- `MatchIndexAllEntriesProof.v:91-101` (`lifted_match_index_leader`). -/
theorem lifted_match_index_leader {net : RefinedNet}
    (hreach : refined_raft_intermediate_reachable (P := P) net)
    (leader : name (P := P))
    (hty : (net.nwState leader).2.type = .Leader) :
    assoc_default (net.nwState leader).2.matchIndex leader 0 =
      maxIndex (net.nwState leader).2.log :=
  lift_prop _ match_index_leader_invariant net hreach leader hty

/-- `MatchIndexAllEntriesProof.v:103-113` (`lifted_match_index_sanity`). -/
theorem lifted_match_index_sanity {net : RefinedNet}
    (hreach : refined_raft_intermediate_reachable (P := P) net)
    (leader h : name (P := P))
    (hty : (net.nwState leader).2.type = .Leader) :
    assoc_default (net.nwState leader).2.matchIndex h 0 ≤
      maxIndex (net.nwState leader).2.log :=
  lift_prop _ match_index_sanity_invariant net hreach leader h hty

/-- `MatchIndexAllEntriesProof.v:115-131`
(`lifted_append_entries_reply_sublog`). -/
theorem lifted_append_entries_reply_sublog {net : RefinedNet}
    (hreach : refined_raft_intermediate_reachable (P := P) net)
    {p : RefinedPacket} {t : term} {es : List (entry (P := P))}
    {h : name (P := P)} {e : entry (P := P)}
    (hp : p ∈ net.nwPackets)
    (hbody : p.pBody = .AppendEntriesReply t es true)
    (hct : (net.nwState h).2.currentTerm = t)
    (hty : (net.nwState h).2.type = .Leader)
    (he : e ∈ es) :
    e ∈ (net.nwState h).2.log :=
  lift_prop _ append_entries_reply_sublog_invariant net hreach
    (deghost_packet p) t es h e (List.mem_map_of_mem hp) hbody hct hty he

/-! ## Small support facts -/

omit O in
/-- `Nat.max_le`'s Coq elimination direction: below a max means below
one of the arms. -/
theorem le_max_elim {n a b : Nat} (h : n ≤ max a b) : n ≤ a ∨ n ≤ b := by
  rcases Nat.le_total a b with hab | hba
  · exact Or.inr (by rw [Nat.max_eq_right hab] at h; exact h)
  · exact Or.inl (by rw [Nat.max_eq_left hba] at h; exact h)

/-- allEntries transport into an updated network: the untouched hosts
keep their records, the updated host's ghost only grows. -/
theorem mia_allEntries_grow {net : RefinedNet}
    {st' : name (P := P) → electionsData (P := P) × raft_data (P := P)}
    {u : name (P := P)} {gd : electionsData (P := P)}
    {d : raft_data (P := P)}
    (hst : ∀ h', st' h' = update net.nwState u (gd, d) h')
    (hgrow : ∀ (t : term) (e : entry (P := P)),
      (t, e) ∈ (net.nwState u).1.allEntries → (t, e) ∈ gd.allEntries)
    {h0 : name (P := P)} {t : term} {e : entry (P := P)}
    (hin : (t, e) ∈ (net.nwState h0).1.allEntries) :
    (t, e) ∈ (st' h0).1.allEntries := by
  rw [hst h0]
  by_cases heq : h0 = u
  · subst heq
    rw [update_same]
    exact hgrow t e hin
  · rw [update_neq _ _ heq]
    exact hin

omit O in
/-- The client-request ghost update in the leader-append case records
exactly the fresh log head at the handler's term (the correlated form
of `update_elections_data_client_request_allEntries_cases`; local to
this file, single consumer). -/
theorem update_elections_data_client_request_allEntries_append
    (me : name (P := P)) (st : electionsData (P := P) × raft_data (P := P))
    (client : R.clientId) (id : Nat) (c : P.input) {out d l}
    {e' : entry (P := P)}
    (hcr : handleClientRequest me st.2 client id c = (out, d, l))
    (hlog : d.log = e' :: st.2.log) :
    (update_elections_data_client_request me st client id c).allEntries
      = (d.currentTerm, e') :: st.1.allEntries := by
  unfold update_elections_data_client_request
  rw [hcr]
  simp only []
  rw [hlog, if_pos (by
    simp only [Nat.blt_eq, List.length_cons]
    exact Nat.lt_succ_self _)]

/-! ## The eleven obligations -/

/-- `MatchIndexAllEntriesProof.v:60-69` (`match_index_all_entries_init`). -/
private theorem mia_init :
    refined_raft_net_invariant_init (P := P) match_index_all_entries_inv := by
  refine ⟨?_, ?_⟩
  · intro e leader h hty _ hin _
    exact nomatch hin
  · intro p t es e hp _ _ _ _ _ _
    exact nomatch hp

/-- `MatchIndexAllEntriesProof.v:249-277` (`match_index_all_entries_timeout`). -/
private theorem mia_timeout :
    refined_raft_net_invariant_timeout (P := P) match_index_all_entries_inv := by
  intro net h st' ps' gd out d l hto hgd hP _hreach hst hps
  obtain ⟨hP1, hP2⟩ := hP
  obtain ⟨hlog, hcases, hmsgs⟩ := handleTimeout_spec h (net.nwState h).2 hto
  have hmi := handleTimeout_matchIndex h (net.nwState h).2 hto
  have hgrow : ∀ (t0 : term) (e0 : entry (P := P)),
      (t0, e0) ∈ (net.nwState h).1.allEntries → (t0, e0) ∈ gd.allEntries := by
    intro t0 e0 hin
    rw [hgd, (update_elections_data_timeout_ghost h (net.nwState h)).2]
    exact hin
  constructor
  · -- host half
    intro e leader h0 hty hle hin hterm
    replace hty : (st' leader).2.type = .Leader := hty
    replace hle : e.eIndex ≤ assoc_default (st' leader).2.matchIndex h0 0 := hle
    replace hin : e ∈ (st' leader).2.log := hin
    replace hterm : e.eTerm = (st' leader).2.currentTerm := hterm
    rw [hst leader] at hty hle hin hterm
    show (e.eTerm, e) ∈ (st' h0).1.allEntries
    refine mia_allEntries_grow hst hgrow ?_
    by_cases heq : leader = h
    · rw [heq, update_same] at hty hle hin hterm
      replace hty : d.type = .Leader := hty
      replace hle : e.eIndex ≤ assoc_default d.matchIndex h0 0 := hle
      replace hin : e ∈ d.log := hin
      replace hterm : e.eTerm = d.currentTerm := hterm
      rcases hcases with ⟨hcteq, htyeq, -, -⟩ | ⟨-, htyc, -, -, -⟩
      · rw [hmi] at hle
        rw [hlog] at hin
        rw [hcteq] at hterm
        rw [htyeq] at hty
        exact hP1 e h h0 hty hle hin hterm
      · rw [htyc] at hty
        exact nomatch hty
    · rw [update_neq _ _ heq] at hty hle hin hterm
      exact hP1 e leader h0 hty hle hin hterm
  · -- nw half
    intro p0 t es e hp0 hbody hct hin hterm hle hty
    replace hp0 : p0 ∈ ps' := hp0
    replace hct : (st' p0.pDst).2.currentTerm = t := hct
    replace hin : e ∈ (st' p0.pDst).2.log := hin
    replace hty : (st' p0.pDst).2.type = .Leader := hty
    rw [hst p0.pDst] at hct hin hty
    show (t, e) ∈ (st' p0.pSrc).1.allEntries
    rcases hps p0 hp0 with hold | hnew
    · refine mia_allEntries_grow hst hgrow ?_
      by_cases heq : p0.pDst = h
      · rw [heq, update_same] at hct hin hty
        replace hct : d.currentTerm = t := hct
        replace hin : e ∈ d.log := hin
        replace hty : d.type = .Leader := hty
        rcases hcases with ⟨hcteq, htyeq, -, -⟩ | ⟨-, htyc, -, -, -⟩
        · have hct' : (net.nwState p0.pDst).2.currentTerm = t := by
            rw [heq, ← hcteq]; exact hct
          have hin' : e ∈ (net.nwState p0.pDst).2.log := by
            rw [heq, ← hlog]; exact hin
          have hty' : (net.nwState p0.pDst).2.type = .Leader := by
            rw [heq, ← htyeq]; exact hty
          exact hP2 p0 t es e hold hbody hct' hin' hterm hle hty'
        · rw [htyc] at hty
          exact nomatch hty
      · rw [update_neq _ _ heq] at hct hin hty
        exact hP2 p0 t es e hold hbody hct hin hterm hle hty
    · exfalso
      obtain ⟨m1, hm1, rfl⟩ := List.mem_map.mp hnew
      obtain ⟨t', cid, lli, llt, hq⟩ := hmsgs m1 hm1
      replace hbody : m1.2 = msg.AppendEntriesReply t es true := hbody
      rw [hq] at hbody
      exact nomatch hbody

/-- `MatchIndexAllEntriesProof.v:711-788`
(`match_index_all_entries_request_vote`). -/
private theorem mia_request_vote :
    refined_raft_net_invariant_request_vote (P := P)
      match_index_all_entries_inv := by
  intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP _hreach
    hpkts hst hps
  obtain ⟨hP1, hP2⟩ := hP
  obtain ⟨-, -, htycases, -⟩ := handleRequestVote_spec p.pDst
    (net.nwState p.pDst).2 t p.pSrc lli llt hrv
  have hlog := handleRequestVote_log p.pDst (net.nwState p.pDst).2 t p.pSrc
    lli llt hrv
  have hmi := handleRequestVote_matchIndex p.pDst (net.nwState p.pDst).2 t
    p.pSrc lli llt hrv
  have hgrow : ∀ (t0 : term) (e0 : entry (P := P)),
      (t0, e0) ∈ (net.nwState p.pDst).1.allEntries →
      (t0, e0) ∈ gd.allEntries := by
    intro t0 e0 hin
    rw [hgd, (update_elections_data_requestVote_cronies p.pDst p.pSrc t
      p.pSrc lli llt (net.nwState p.pDst)).2.2]
    exact hin
  constructor
  · -- host half
    intro e leader h0 hty hle hin hterm
    replace hty : (st' leader).2.type = .Leader := hty
    replace hle : e.eIndex ≤ assoc_default (st' leader).2.matchIndex h0 0 := hle
    replace hin : e ∈ (st' leader).2.log := hin
    replace hterm : e.eTerm = (st' leader).2.currentTerm := hterm
    rw [hst leader] at hty hle hin hterm
    show (e.eTerm, e) ∈ (st' h0).1.allEntries
    refine mia_allEntries_grow hst hgrow ?_
    by_cases heq : leader = p.pDst
    · rw [heq, update_same] at hty hle hin hterm
      replace hty : d.type = .Leader := hty
      replace hle : e.eIndex ≤ assoc_default d.matchIndex h0 0 := hle
      replace hin : e ∈ d.log := hin
      replace hterm : e.eTerm = d.currentTerm := hterm
      rcases htycases with ⟨hcteq, htyeq⟩ | htyf
      · rw [hmi] at hle
        rw [hlog] at hin
        rw [hcteq] at hterm
        rw [htyeq] at hty
        exact hP1 e p.pDst h0 hty hle hin hterm
      · rw [htyf] at hty
        exact nomatch hty
    · rw [update_neq _ _ heq] at hty hle hin hterm
      exact hP1 e leader h0 hty hle hin hterm
  · -- nw half
    intro p0 t0 es e hp0 hbody hct hin hterm hle hty
    replace hp0 : p0 ∈ ps' := hp0
    replace hct : (st' p0.pDst).2.currentTerm = t0 := hct
    replace hin : e ∈ (st' p0.pDst).2.log := hin
    replace hty : (st' p0.pDst).2.type = .Leader := hty
    rw [hst p0.pDst] at hct hin hty
    show (t0, e) ∈ (st' p0.pSrc).1.allEntries
    rcases hps p0 hp0 with hold | hnew
    · have hold2 : p0 ∈ net.nwPackets := by
        rw [hpkts]
        exact mem_of_mem_remove_middle hold
      refine mia_allEntries_grow hst hgrow ?_
      by_cases heq : p0.pDst = p.pDst
      · rw [heq, update_same] at hct hin hty
        replace hct : d.currentTerm = t0 := hct
        replace hin : e ∈ d.log := hin
        replace hty : d.type = .Leader := hty
        rcases htycases with ⟨hcteq, htyeq⟩ | htyf
        · have hct' : (net.nwState p0.pDst).2.currentTerm = t0 := by
            rw [heq, ← hcteq]; exact hct
          have hin' : e ∈ (net.nwState p0.pDst).2.log := by
            rw [heq, ← hlog]; exact hin
          have hty' : (net.nwState p0.pDst).2.type = .Leader := by
            rw [heq, ← htyeq]; exact hty
          exact hP2 p0 t0 es e hold2 hbody hct' hin' hterm hle hty'
        · rw [htyf] at hty
          exact nomatch hty
      · rw [update_neq _ _ heq] at hct hin hty
        exact hP2 p0 t0 es e hold2 hbody hct hin hterm hle hty
    · exfalso
      obtain ⟨t', v, hm⟩ := handleRequestVote_reply_shape p.pDst
        (net.nwState p.pDst).2 t p.pSrc lli llt hrv
      rw [hnew] at hbody
      replace hbody : m = msg.AppendEntriesReply t0 es true := hbody
      rw [hm] at hbody
      exact nomatch hbody

/-- `MatchIndexAllEntriesProof.v:930-988`
(`match_index_all_entries_do_leader`). -/
private theorem mia_do_leader :
    refined_raft_net_invariant_do_leader (P := P)
      match_index_all_entries_inv := by
  intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst hps
  obtain ⟨hP1, hP2⟩ := hP
  obtain ⟨hcteq, -, htyeq, -, hlogeq, hmsgs⟩ := doLeader_spec d h hdl
  have hmi := doLeader_matchIndex d h hdl
  have hd2 : (net.nwState h).2 = d := by rw [hstate]
  have hgrow : ∀ (t0 : term) (e0 : entry (P := P)),
      (t0, e0) ∈ (net.nwState h).1.allEntries → (t0, e0) ∈ gd.allEntries := by
    intro t0 e0 hin
    rw [hstate] at hin
    exact hin
  constructor
  · -- host half
    intro e leader h0 hty hle hin hterm
    replace hty : (st' leader).2.type = .Leader := hty
    replace hle : e.eIndex ≤ assoc_default (st' leader).2.matchIndex h0 0 := hle
    replace hin : e ∈ (st' leader).2.log := hin
    replace hterm : e.eTerm = (st' leader).2.currentTerm := hterm
    rw [hst leader] at hty hle hin hterm
    show (e.eTerm, e) ∈ (st' h0).1.allEntries
    refine mia_allEntries_grow hst hgrow ?_
    by_cases heq : leader = h
    · rw [heq, update_same] at hty hle hin hterm
      replace hty : d'.type = .Leader := hty
      replace hle : e.eIndex ≤ assoc_default d'.matchIndex h0 0 := hle
      replace hin : e ∈ d'.log := hin
      replace hterm : e.eTerm = d'.currentTerm := hterm
      rw [hmi, ← hd2] at hle
      rw [hlogeq, ← hd2] at hin
      rw [hcteq, ← hd2] at hterm
      rw [htyeq, ← hd2] at hty
      exact hP1 e h h0 hty hle hin hterm
    · rw [update_neq _ _ heq] at hty hle hin hterm
      exact hP1 e leader h0 hty hle hin hterm
  · -- nw half
    intro p0 t0 es e hp0 hbody hct hin hterm hle hty
    replace hp0 : p0 ∈ ps' := hp0
    replace hct : (st' p0.pDst).2.currentTerm = t0 := hct
    replace hin : e ∈ (st' p0.pDst).2.log := hin
    replace hty : (st' p0.pDst).2.type = .Leader := hty
    rw [hst p0.pDst] at hct hin hty
    show (t0, e) ∈ (st' p0.pSrc).1.allEntries
    rcases hps p0 hp0 with hold | hnew
    · refine mia_allEntries_grow hst hgrow ?_
      by_cases heq : p0.pDst = h
      · rw [heq, update_same] at hct hin hty
        replace hct : d'.currentTerm = t0 := hct
        replace hin : e ∈ d'.log := hin
        replace hty : d'.type = .Leader := hty
        have hct' : (net.nwState p0.pDst).2.currentTerm = t0 := by
          rw [heq, hd2, ← hcteq]; exact hct
        have hin' : e ∈ (net.nwState p0.pDst).2.log := by
          rw [heq, hd2, ← hlogeq]; exact hin
        have hty' : (net.nwState p0.pDst).2.type = .Leader := by
          rw [heq, hd2, ← htyeq]; exact hty
        exact hP2 p0 t0 es e hold hbody hct' hin' hterm hle hty'
      · rw [update_neq _ _ heq] at hct hin hty
        exact hP2 p0 t0 es e hold hbody hct hin hterm hle hty
    · exfalso
      obtain ⟨m1, hm1, rfl⟩ := List.mem_map.mp hnew
      obtain ⟨t', lid, pli, plt, es', ci, hq⟩ := hmsgs m1 hm1
      replace hbody : m1.2 = msg.AppendEntriesReply t0 es true := hbody
      rw [hq] at hbody
      exact nomatch hbody

/-- `MatchIndexAllEntriesProof.v:990-1047`
(`match_index_all_entries_do_generic_server`). -/
private theorem mia_do_generic_server :
    refined_raft_net_invariant_do_generic_server (P := P)
      match_index_all_entries_inv := by
  intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps
  obtain ⟨hP1, hP2⟩ := hP
  obtain ⟨hlogeq, htyeq, hcteq, -, -, hms⟩ := doGenericServer_spec h d hgs
  have hmi := doGenericServer_matchIndex h d hgs
  have hd2 : (net.nwState h).2 = d := by rw [hstate]
  have hgrow : ∀ (t0 : term) (e0 : entry (P := P)),
      (t0, e0) ∈ (net.nwState h).1.allEntries → (t0, e0) ∈ gd.allEntries := by
    intro t0 e0 hin
    rw [hstate] at hin
    exact hin
  constructor
  · intro e leader h0 hty hle hin hterm
    replace hty : (st' leader).2.type = .Leader := hty
    replace hle : e.eIndex ≤ assoc_default (st' leader).2.matchIndex h0 0 := hle
    replace hin : e ∈ (st' leader).2.log := hin
    replace hterm : e.eTerm = (st' leader).2.currentTerm := hterm
    rw [hst leader] at hty hle hin hterm
    show (e.eTerm, e) ∈ (st' h0).1.allEntries
    refine mia_allEntries_grow hst hgrow ?_
    by_cases heq : leader = h
    · rw [heq, update_same] at hty hle hin hterm
      replace hty : d'.type = .Leader := hty
      replace hle : e.eIndex ≤ assoc_default d'.matchIndex h0 0 := hle
      replace hin : e ∈ d'.log := hin
      replace hterm : e.eTerm = d'.currentTerm := hterm
      rw [hmi, ← hd2] at hle
      rw [hlogeq, ← hd2] at hin
      rw [hcteq, ← hd2] at hterm
      rw [htyeq, ← hd2] at hty
      exact hP1 e h h0 hty hle hin hterm
    · rw [update_neq _ _ heq] at hty hle hin hterm
      exact hP1 e leader h0 hty hle hin hterm
  · intro p0 t0 es e hp0 hbody hct hin hterm hle hty
    replace hp0 : p0 ∈ ps' := hp0
    replace hct : (st' p0.pDst).2.currentTerm = t0 := hct
    replace hin : e ∈ (st' p0.pDst).2.log := hin
    replace hty : (st' p0.pDst).2.type = .Leader := hty
    rw [hst p0.pDst] at hct hin hty
    show (t0, e) ∈ (st' p0.pSrc).1.allEntries
    rcases hps p0 hp0 with hold | hnew
    · refine mia_allEntries_grow hst hgrow ?_
      by_cases heq : p0.pDst = h
      · rw [heq, update_same] at hct hin hty
        replace hct : d'.currentTerm = t0 := hct
        replace hin : e ∈ d'.log := hin
        replace hty : d'.type = .Leader := hty
        have hct' : (net.nwState p0.pDst).2.currentTerm = t0 := by
          rw [heq, hd2, ← hcteq]; exact hct
        have hin' : e ∈ (net.nwState p0.pDst).2.log := by
          rw [heq, hd2, ← hlogeq]; exact hin
        have hty' : (net.nwState p0.pDst).2.type = .Leader := by
          rw [heq, hd2, ← htyeq]; exact hty
        exact hP2 p0 t0 es e hold hbody hct' hin' hterm hle hty'
      · rw [update_neq _ _ heq] at hct hin hty
        exact hP2 p0 t0 es e hold hbody hct hin hterm hle hty
    · exfalso
      rw [hms] at hnew
      simp [send_packets] at hnew

/-- `MatchIndexAllEntriesProof.v:1049-1064`
(`match_index_all_entries_state_same_packet_subset`). -/
private theorem mia_state_same :
    refined_raft_net_invariant_state_same_packet_subset (P := P)
      match_index_all_entries_inv := by
  intro net net' hstates hsubp hP _hreach
  obtain ⟨hP1, hP2⟩ := hP
  constructor
  · intro e leader h hty hle hin hterm
    rw [← hstates leader] at hty hle hin hterm
    rw [← hstates h]
    exact hP1 e leader h hty hle hin hterm
  · intro p t es e hp hbody hct hin hterm hle hty
    rw [← hstates p.pDst] at hct hin hty
    rw [← hstates p.pSrc]
    exact hP2 p t es e (hsubp p hp) hbody hct hin hterm hle hty

/-- `MatchIndexAllEntriesProof.v:1066-1097`
(`match_index_all_entries_reboot`). -/
private theorem mia_reboot :
    refined_raft_net_invariant_reboot (P := P)
      match_index_all_entries_inv := by
  intro net net' gd d h d' hrb hP _hreach hstate hst hpkts
  obtain ⟨hP1, hP2⟩ := hP
  have hgrow : ∀ (t0 : term) (e0 : entry (P := P)),
      (t0, e0) ∈ (net.nwState h).1.allEntries → (t0, e0) ∈ gd.allEntries := by
    intro t0 e0 hin
    rw [hstate] at hin
    exact hin
  have htransport : ∀ (h0 : name (P := P)) (t0 : term) (e0 : entry (P := P)),
      (t0, e0) ∈ (net.nwState h0).1.allEntries →
      (t0, e0) ∈ (net'.nwState h0).1.allEntries := by
    intro h0 t0 e0 hin
    rw [hst h0]
    by_cases heq : h0 = h
    · subst heq
      rw [update_same]
      exact hgrow t0 e0 hin
    · rw [update_neq _ _ heq]
      exact hin
  constructor
  · intro e leader h0 hty hle hin hterm
    rw [hst leader] at hty hle hin hterm
    by_cases heq : leader = h
    · exfalso
      rw [heq, update_same] at hty
      replace hty : d'.type = .Leader := hty
      rw [← hrb] at hty
      exact nomatch hty
    · rw [update_neq _ _ heq] at hty hle hin hterm
      exact htransport h0 e.eTerm e (hP1 e leader h0 hty hle hin hterm)
  · intro p t es e hp hbody hct hin hterm hle hty
    rw [hst p.pDst] at hct hin hty
    rw [← hpkts] at hp
    by_cases heq : p.pDst = h
    · exfalso
      rw [heq, update_same] at hty
      replace hty : d'.type = .Leader := hty
      rw [← hrb] at hty
      exact nomatch hty
    · rw [update_neq _ _ heq] at hct hin hty
      exact htransport p.pSrc t e (hP2 p t es e hp hbody hct hin hterm hle hty)

/-- `MatchIndexAllEntriesProof.v:133-210`
(`match_index_all_entries_client_request`). -/
private theorem mia_client_request :
    refined_raft_net_invariant_client_request (P := P)
      match_index_all_entries_inv := by
  intro h net st' ps' gd out d l client id c hcr hgd hP hreach hst hps
  obtain ⟨hP1, hP2⟩ := hP
  obtain ⟨htyeq, hcteq, -, -, hl⟩ :=
    handleClientRequest_spec h (net.nwState h).2 client id c hcr
  have hmi := handleClientRequest_matchIndex h (net.nwState h).2 client id
    c hcr
  have hlogf := handleClientRequest_log_full h (net.nwState h).2 client id
    c hcr
  have hgrow : ∀ (t0 : term) (e0 : entry (P := P)),
      (t0, e0) ∈ (net.nwState h).1.allEntries → (t0, e0) ∈ gd.allEntries := by
    intro t0 e0 hin
    rw [hgd]
    rcases update_elections_data_client_request_allEntries_cases h
      (net.nwState h) client id c with hsame | ⟨t1, e1, hcons, -⟩
    · rw [hsame]
      exact hin
    · rw [hcons]
      exact List.mem_cons_of_mem _ hin
  constructor
  · -- host half
    intro e leader h0 hty hle hin hterm
    replace hty : (st' leader).2.type = .Leader := hty
    replace hle : e.eIndex ≤ assoc_default (st' leader).2.matchIndex h0 0 := hle
    replace hin : e ∈ (st' leader).2.log := hin
    replace hterm : e.eTerm = (st' leader).2.currentTerm := hterm
    rw [hst leader] at hty hle hin hterm
    show (e.eTerm, e) ∈ (st' h0).1.allEntries
    by_cases heq : leader = h
    · rw [heq, update_same] at hty hle hin hterm
      replace hty : d.type = .Leader := hty
      replace hle : e.eIndex ≤ assoc_default d.matchIndex h0 0 := hle
      replace hin : e ∈ d.log := hin
      replace hterm : e.eTerm = d.currentTerm := hterm
      rcases hlogf with ⟨htyL, hlog⟩ | ⟨htyN, -⟩
      · -- the leader appends its fresh entry
        rcases hmi with ⟨hmax, -⟩ | ⟨hmiset, -⟩
        · -- maxIndex-unchanged arm is impossible beside the append
          exfalso
          rw [hlog] at hmax
          replace hmax : maxIndex (net.nwState h).2.log + 1
              = maxIndex (net.nwState h).2.log := hmax
          exact Nat.succ_ne_self _ hmax
        · rw [hmiset] at hle
          rw [hlog] at hin
          by_cases hh0 : h0 = h
          · rw [hh0, assoc_set_same_default] at hle
            rcases List.mem_cons.mp hin with heqe | hin0
            · -- the fresh entry's own record
              rw [hst h0, hh0, update_same]
              show (e.eTerm, e) ∈ gd.allEntries
              rw [hgd, update_elections_data_client_request_allEntries_append
                h (net.nwState h) client id c hcr hlog]
              rw [hterm, heqe]
              exact List.mem_cons_self ..
            · -- an old entry below the leader's own maxIndex slot
              refine mia_allEntries_grow hst hgrow ?_
              have hsorted := entries_sorted_invariant net hreach h
              have hle0 : e.eIndex ≤
                  assoc_default (net.nwState h).2.matchIndex h 0 := by
                rw [lifted_match_index_leader hreach h htyL]
                exact maxIndex_is_max hsorted hin0
              rw [hh0]
              exact hP1 e h h htyL hle0 hin0 (hcteq ▸ hterm)
          · rw [assoc_set_diff_default _ _ _ _ _ hh0] at hle
            rcases List.mem_cons.mp hin with rfl | hin0
            · -- the fresh entry sits above every other slot's estimate
              exfalso
              have hsan := lifted_match_index_sanity hreach h h0 htyL
              replace hle : maxIndex (net.nwState h).2.log + 1 ≤
                  assoc_default (net.nwState h).2.matchIndex h0 0 := hle
              exact Nat.not_succ_le_self _ (Nat.le_trans hle hsan)
            · refine mia_allEntries_grow hst hgrow ?_
              exact hP1 e h h0 htyL hle hin0 (hcteq ▸ hterm)
      · -- not a leader: no append, but then the post-type is not Leader
        exfalso
        rw [htyeq] at hty
        exact htyN hty
    · rw [update_neq _ _ heq] at hty hle hin hterm
      exact mia_allEntries_grow hst hgrow (hP1 e leader h0 hty hle hin hterm)
  · -- nw half: no packets are sent
    intro p0 t0 es e hp0 hbody hct hin hterm hle hty
    replace hp0 : p0 ∈ ps' := hp0
    replace hct : (st' p0.pDst).2.currentTerm = t0 := hct
    replace hin : e ∈ (st' p0.pDst).2.log := hin
    replace hty : (st' p0.pDst).2.type = .Leader := hty
    rw [hst p0.pDst] at hct hin hty
    show (t0, e) ∈ (st' p0.pSrc).1.allEntries
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · exact h1
      · exfalso
        rw [hl] at h1
        simp [send_packets] at h1
    refine mia_allEntries_grow hst hgrow ?_
    by_cases heq : p0.pDst = h
    · rw [heq, update_same] at hct hin hty
      replace hct : d.currentTerm = t0 := hct
      replace hin : e ∈ d.log := hin
      replace hty : d.type = .Leader := hty
      have hct' : (net.nwState p0.pDst).2.currentTerm = t0 := by
        rw [heq, ← hcteq]; exact hct
      have hty' : (net.nwState p0.pDst).2.type = .Leader := by
        rw [heq, ← htyeq]; exact hty
      rcases hlogf with ⟨htyL, hlog⟩ | ⟨-, hds⟩
      · rw [hlog] at hin
        rcases List.mem_cons.mp hin with rfl | hin0
        · -- the fresh head cannot sit below an in-flight true reply's max
          exfalso
          have hesne : es ≠ [] := by
            intro hnil
            rw [hnil] at hle
            replace hle : maxIndex (net.nwState h).2.log + 1 ≤ 0 := hle
            exact Nat.not_succ_le_zero _ hle
          obtain ⟨x, hx, hxi, -⟩ := maxIndex_non_empty hesne
          have hxlog : x ∈ (net.nwState h).2.log := by
            have := lifted_append_entries_reply_sublog hreach hold hbody
              hct' hty' hx
            rw [heq] at this
            exact this
          have hxle : x.eIndex ≤ maxIndex (net.nwState h).2.log :=
            maxIndex_is_max (entries_sorted_invariant net hreach h) hxlog
          rw [hxi] at hxle
          replace hle : maxIndex (net.nwState h).2.log + 1 ≤ maxIndex es := hle
          exact Nat.not_succ_le_self _ (Nat.le_trans hle hxle)
        · have hin' : e ∈ (net.nwState p0.pDst).2.log := by
            rw [heq]; exact hin0
          exact hP2 p0 t0 es e hold hbody hct' hin' hterm hle hty'
      · rw [hds] at hin
        have hin' : e ∈ (net.nwState p0.pDst).2.log := by
          rw [heq]; exact hin
        exact hP2 p0 t0 es e hold hbody hct' hin' hterm hle hty'
    · rw [update_neq _ _ heq] at hct hin hty
      exact hP2 p0 t0 es e hold hbody hct hin hterm hle hty

/-- `MatchIndexAllEntriesProof.v:640-699`
(`match_index_all_entries_append_entries_reply`). -/
private theorem mia_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply (P := P)
      match_index_all_entries_inv := by
  intro xs p ys net st' ps' gd d m t es res haer hgd hbody hP hreach
    hpkts hst hps
  obtain ⟨hP1, hP2⟩ := hP
  obtain ⟨-, harms, hl⟩ := handleAppendEntriesReply_spec p.pDst
    (net.nwState p.pDst).2 p.pSrc t es res haer
  have hlogeq := handleAppendEntriesReply_log p.pDst
    (net.nwState p.pDst).2 p.pSrc t es res haer
  have hp_in : p ∈ net.nwPackets := by
    rw [hpkts]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hgrow : ∀ (t0 : term) (e0 : entry (P := P)),
      (t0, e0) ∈ (net.nwState p.pDst).1.allEntries →
      (t0, e0) ∈ gd.allEntries := by
    intro t0 e0 hin
    rw [hgd]
    exact hin
  constructor
  · -- host half
    intro e leader h0 hty hle hin hterm
    replace hty : (st' leader).2.type = .Leader := hty
    replace hle : e.eIndex ≤ assoc_default (st' leader).2.matchIndex h0 0 := hle
    replace hin : e ∈ (st' leader).2.log := hin
    replace hterm : e.eTerm = (st' leader).2.currentTerm := hterm
    rw [hst leader] at hty hle hin hterm
    show (e.eTerm, e) ∈ (st' h0).1.allEntries
    refine mia_allEntries_grow hst hgrow ?_
    by_cases heq : leader = p.pDst
    · rw [heq, update_same] at hty hle hin hterm
      replace hty : d.type = .Leader := hty
      replace hle : e.eIndex ≤ assoc_default d.matchIndex h0 0 := hle
      replace hin : e ∈ d.log := hin
      replace hterm : e.eTerm = d.currentTerm := hterm
      rcases harms with ⟨hcteq, -, htyeq⟩ | ⟨-, -, htyf⟩
      · obtain ⟨htyeq', -, hmi⟩ := handleAppendEntriesReply_matchIndex
          p.pDst (net.nwState p.pDst).2 p.pSrc t es res haer hty
        have htyL : (net.nwState p.pDst).2.type = .Leader := by
          rw [htyeq']; exact hty
        rw [hlogeq] at hin
        rw [hcteq] at hterm
        rcases hmi with hmieq | ⟨hres, hctt, hmiset⟩
        · rw [hmieq] at hle
          exact hP1 e p.pDst h0 htyL hle hin hterm
        · rw [hmiset] at hle
          by_cases hh0 : h0 = p.pSrc
          · rw [hh0, assoc_set_same_default] at hle
            rcases le_max_elim hle with hle1 | hle2
            · rw [hh0]
              exact hP1 e p.pDst p.pSrc htyL hle1 hin hterm
            · -- the bumped slot: the consumed true reply certifies e
              subst hres
              have hres' := hP2 p t es e hp_in hbody hctt hin
                (by rw [hterm]; exact hctt) hle2 htyL
              rw [hh0, hterm, hctt]
              exact hres'
          · rw [assoc_set_diff_default _ _ _ _ _ hh0] at hle
            exact hP1 e p.pDst h0 htyL hle hin hterm
      · rw [htyf] at hty
        exact nomatch hty
    · rw [update_neq _ _ heq] at hty hle hin hterm
      exact hP1 e leader h0 hty hle hin hterm
  · -- nw half: no sends
    intro p0 t0 es0 e hp0 hbody0 hct hin hterm hle hty
    replace hp0 : p0 ∈ ps' := hp0
    replace hct : (st' p0.pDst).2.currentTerm = t0 := hct
    replace hin : e ∈ (st' p0.pDst).2.log := hin
    replace hty : (st' p0.pDst).2.type = .Leader := hty
    rw [hst p0.pDst] at hct hin hty
    show (t0, e) ∈ (st' p0.pSrc).1.allEntries
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · rw [hpkts]
        exact mem_of_mem_remove_middle h1
      · exfalso
        rw [hl] at h1
        simp [send_packets] at h1
    refine mia_allEntries_grow hst hgrow ?_
    by_cases heq : p0.pDst = p.pDst
    · rw [heq, update_same] at hct hin hty
      replace hct : d.currentTerm = t0 := hct
      replace hin : e ∈ d.log := hin
      replace hty : d.type = .Leader := hty
      rcases harms with ⟨hcteq, -, htyeq⟩ | ⟨-, -, htyf⟩
      · have hct' : (net.nwState p0.pDst).2.currentTerm = t0 := by
          rw [heq, ← hcteq]; exact hct
        have hin' : e ∈ (net.nwState p0.pDst).2.log := by
          rw [heq, ← hlogeq]; exact hin
        have hty' : (net.nwState p0.pDst).2.type = .Leader := by
          rw [heq, ← htyeq]; exact hty
        exact hP2 p0 t0 es0 e hold hbody0 hct' hin' hterm hle hty'
      · rw [htyf] at hty
        exact nomatch hty
    · rw [update_neq _ _ heq] at hct hin hty
      exact hP2 p0 t0 es0 e hold hbody0 hct hin hterm hle hty

/-- `MatchIndexAllEntriesProof.v:823-913`
(`match_index_all_entries_request_vote_reply`). -/
private theorem mia_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply (P := P)
      match_index_all_entries_inv := by
  intro xs p ys net st' ps' gd d t v hrvr hgd hbody hP hreach hpkts hst hps
  obtain ⟨hP1, hP2⟩ := hP
  obtain ⟨-, -, -, hleader⟩ := handleRequestVoteReply_spec p.pDst
    (net.nwState p.pDst).2 p.pSrc t v hrvr
  have hlogeq : d.log = (net.nwState p.pDst).2.log := by
    rw [← hrvr]
    exact handleRequestVoteReply_log p.pDst (net.nwState p.pDst).2 p.pSrc t v
  have hp_in : p ∈ net.nwPackets := by
    rw [hpkts]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hgrow : ∀ (t0 : term) (e0 : entry (P := P)),
      (t0, e0) ∈ (net.nwState p.pDst).1.allEntries →
      (t0, e0) ∈ gd.allEntries := by
    intro t0 e0 hin
    rw [hgd, (update_elections_data_requestVoteReply_votes p.pDst p.pSrc t
      v (net.nwState p.pDst)).2.2]
    exact hin
  constructor
  · -- host half
    intro e leader h0 hty hle hin hterm
    replace hty : (st' leader).2.type = .Leader := hty
    replace hle : e.eIndex ≤ assoc_default (st' leader).2.matchIndex h0 0 := hle
    replace hin : e ∈ (st' leader).2.log := hin
    replace hterm : e.eTerm = (st' leader).2.currentTerm := hterm
    rw [hst leader] at hty hle hin hterm
    show (e.eTerm, e) ∈ (st' h0).1.allEntries
    by_cases heq : leader = p.pDst
    · rw [heq, update_same] at hty hle hin hterm
      replace hty : d.type = .Leader := hty
      replace hle : e.eIndex ≤ assoc_default d.matchIndex h0 0 := hle
      replace hin : e ∈ d.log := hin
      replace hterm : e.eTerm = d.currentTerm := hterm
      rcases hleader hty with hds | ⟨htyC, -, hcteq⟩
      · rw [hds] at hty hle hin hterm
        exact mia_allEntries_grow hst hgrow
          (hP1 e p.pDst h0 hty hle hin hterm)
      · -- fresh win: matchIndex reset to the leader's own maxIndex slot
        rcases handleRequestVoteReply_matchIndex p.pDst
            (net.nwState p.pDst).2 p.pSrc t v hrvr hty with ⟨htyL, -⟩ | hmiset
        · rw [htyL] at htyC
          exact nomatch htyC
        · rw [hmiset] at hle
          rw [hlogeq] at hin
          rw [hcteq] at hterm
          by_cases hh0 : h0 = p.pDst
          · -- the leader's own slot: log_all_entries at the pre-state
            refine mia_allEntries_grow hst hgrow ?_
            rw [hh0]
            exact log_all_entries_invariant net hreach p.pDst e hin hterm
          · -- any other slot's estimate is the empty map's default 0
            exfalso
            rw [assoc_set_diff_default _ _ _ _ _ hh0] at hle
            replace hle : e.eIndex ≤ 0 := hle
            have hgt := entries_gt_0_invariant net hreach p.pDst e hin
            exact Nat.not_succ_le_zero _ (Nat.le_trans hgt hle)
    · rw [update_neq _ _ heq] at hty hle hin hterm
      exact mia_allEntries_grow hst hgrow (hP1 e leader h0 hty hle hin hterm)
  · -- nw half: no sends
    intro p0 t0 es0 e hp0 hbody0 hct hin hterm hle hty
    replace hp0 : p0 ∈ ps' := hp0
    replace hct : (st' p0.pDst).2.currentTerm = t0 := hct
    replace hin : e ∈ (st' p0.pDst).2.log := hin
    replace hty : (st' p0.pDst).2.type = .Leader := hty
    rw [hst p0.pDst] at hct hin hty
    show (t0, e) ∈ (st' p0.pSrc).1.allEntries
    have hold : p0 ∈ net.nwPackets := by
      rw [hpkts]
      exact mem_of_mem_remove_middle (hps p0 hp0)
    refine mia_allEntries_grow hst hgrow ?_
    by_cases heq : p0.pDst = p.pDst
    · rw [heq, update_same] at hct hin hty
      replace hct : d.currentTerm = t0 := hct
      replace hin : e ∈ d.log := hin
      replace hty : d.type = .Leader := hty
      rcases hleader hty with hds | ⟨htyC, -, hcteq⟩
      · rw [hds] at hct hin hty
        have hct' : (net.nwState p0.pDst).2.currentTerm = t0 := by
          rw [heq]; exact hct
        have hin' : e ∈ (net.nwState p0.pDst).2.log := by
          rw [heq]; exact hin
        have hty' : (net.nwState p0.pDst).2.type = .Leader := by
          rw [heq]; exact hty
        exact hP2 p0 t0 es0 e hold hbody0 hct' hin' hterm hle hty'
      · -- a candidate winning the election with a same-term true
        -- AppendEntriesReply in flight against its own log is refuted by
        -- the candidate-entries lattice (upstream :880-897)
        exfalso
        obtain ⟨-, hv, hteq, -, hvr, -, hwon⟩ :=
          handleRequestVoteReply_leader_transition p.pDst
            (net.nwState p.pDst).2 p.pSrc t v hrvr
            (by rw [htyC]; intro hc; exact nomatch hc) hty
        rw [hlogeq] at hin
        have hce : candidateEntries e net.nwState :=
          (candidate_entries_invariant net hreach).1 p.pDst e hin
        have hterm_ct : (net.nwState p.pDst).2.currentTerm = e.eTerm := by
          rw [hterm, ← hct, hcteq]
        refine wonElection_candidateEntries_rvr
          (votes_correct_invariant net hreach)
          (cronies_correct_invariant net hreach) hce hp_in ?_ hterm_ct ?_
          htyC
        · rw [hbody, hv]
          show msg.RequestVoteReply t true = _
          rw [← hteq, hterm_ct]
        · exact hwon
    · rw [update_neq _ _ heq] at hct hin hty
      exact hP2 p0 t0 es0 e hold hbody0 hct hin hterm hle hty

/-- `MatchIndexAllEntriesProof.v:499-608`
(`match_index_all_entries_append_entries`) — THE PRIMED OBLIGATION,
the whole port's reason to trigger GAP-1: the fresh true reply's
entries are certified against the RECEIVER's post-splice log and
allEntries by `entries_match_invariant` and `log_all_entries_invariant`
applied AT THE SUCCESSOR NET (`hreach'`). The still-leader receiver
branches ride unit 9's leaves-leader nop instead of upstream's
`no_AE_to_leader` detour (route note in the file header). -/
private theorem mia_append_entries :
    refined_raft_net_invariant_append_entries' (P := P)
      match_index_all_entries_inv := by
  intro xs p ys net st' ps' gd d m t n pli plt es ci hae hgd hbody hP hreach
    hreach' hpkts hst hps
  obtain ⟨hP1, hP2⟩ := hP
  obtain ⟨t'', r'', rfl⟩ := handleAppendEntries_reply_entries p.pDst
    (net.nwState p.pDst).2 t n pli plt es ci hae
  have hp_in : p ∈ net.nwPackets := by
    rw [hpkts]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hgrow : ∀ (t0 : term) (e0 : entry (P := P)),
      (t0, e0) ∈ (net.nwState p.pDst).1.allEntries →
      (t0, e0) ∈ gd.allEntries := by
    intro t0 e0 hin
    rw [hgd]
    rcases update_elections_data_appendEntries_allEntries_cases p.pDst
      (net.nwState p.pDst) t n pli plt es ci with hsame | ⟨t1, happ⟩
    · rw [hsame]
      exact hin
    · rw [happ]
      exact List.mem_append.mpr (Or.inr hin)
  constructor
  · -- host half: a post-state leader was untouched (leaves-leader nop)
    intro e leader h0 hty hle hin hterm
    replace hty : (st' leader).2.type = .Leader := hty
    replace hle : e.eIndex ≤ assoc_default (st' leader).2.matchIndex h0 0 := hle
    replace hin : e ∈ (st' leader).2.log := hin
    replace hterm : e.eTerm = (st' leader).2.currentTerm := hterm
    rw [hst leader] at hty hle hin hterm
    show (e.eTerm, e) ∈ (st' h0).1.allEntries
    refine mia_allEntries_grow hst hgrow ?_
    by_cases heq : leader = p.pDst
    · rw [heq, update_same] at hty hle hin hterm
      replace hty : d.type = .Leader := hty
      replace hle : e.eIndex ≤ assoc_default d.matchIndex h0 0 := hle
      replace hin : e ∈ d.log := hin
      replace hterm : e.eTerm = d.currentTerm := hterm
      obtain ⟨hds, -⟩ := update_elections_data_appendEntries_log_allEntries_leader
        p.pDst (net.nwState p.pDst) t n pli plt es ci hae hty
      rw [hds] at hty hle hin hterm
      exact hP1 e p.pDst h0 hty hle hin hterm
    · rw [update_neq _ _ heq] at hty hle hin hterm
      exact hP1 e leader h0 hty hle hin hterm
  · -- nw half
    intro p0 t0 es0 e hp0 hbody0 hct hin hterm hle hty
    replace hp0 : p0 ∈ ps' := hp0
    replace hct : (st' p0.pDst).2.currentTerm = t0 := hct
    replace hin : e ∈ (st' p0.pDst).2.log := hin
    replace hty : (st' p0.pDst).2.type = .Leader := hty
    show (t0, e) ∈ (st' p0.pSrc).1.allEntries
    rcases hps p0 hp0 with hold | hnew
    · -- an old reply: leaves-leader nop at the receiver, transport
      have hold2 : p0 ∈ net.nwPackets := by
        rw [hpkts]
        exact mem_of_mem_remove_middle hold
      rw [hst p0.pDst] at hct hin hty
      refine mia_allEntries_grow hst hgrow ?_
      by_cases heq : p0.pDst = p.pDst
      · rw [heq, update_same] at hct hin hty
        replace hct : d.currentTerm = t0 := hct
        replace hin : e ∈ d.log := hin
        replace hty : d.type = .Leader := hty
        obtain ⟨hds, -⟩ :=
          update_elections_data_appendEntries_log_allEntries_leader
            p.pDst (net.nwState p.pDst) t n pli plt es ci hae hty
        rw [hds] at hct hin hty
        have hct' : (net.nwState p0.pDst).2.currentTerm = t0 := by
          rw [heq]; exact hct
        have hin' : e ∈ (net.nwState p0.pDst).2.log := by
          rw [heq]; exact hin
        have hty' : (net.nwState p0.pDst).2.type = .Leader := by
          rw [heq]; exact hty
        exact hP2 p0 t0 es0 e hold2 hbody0 hct' hin' hterm hle hty'
      · rw [update_neq _ _ heq] at hct hin hty
        exact hP2 p0 t0 es0 e hold2 hbody0 hct hin hterm hle hty
    · -- THE fresh true reply — the primed premise's payoff
      rw [hnew] at hct hin hty hbody0 ⊢
      replace hbody0 : msg.AppendEntriesReply (P := P) t'' es r''
          = .AppendEntriesReply t0 es0 true := hbody0
      injection hbody0 with h1 h2 h3
      subst h1
      subst h2
      subst h3
      replace hct : (st' p.pSrc).2.currentTerm = t'' := hct
      replace hin : e ∈ (st' p.pSrc).2.log := hin
      replace hty : (st' p.pSrc).2.type = .Leader := hty
      show (t'', e) ∈ (st' p.pDst).1.allEntries
      by_cases hsrc : p.pSrc = p.pDst
      · -- an AppendEntries to self is impossible
        exact absurd hsrc.symm
          (fun hc => no_append_entries_to_self_refined net hreach p t n pli
            plt es ci hp_in hbody hc)
      · -- the leader is untouched; certify through the successor net
        rw [hst p.pSrc, update_neq _ _ hsrc] at hct hin hty
        obtain ⟨hteq, -⟩ := handleAppendEntries_reply_true p.pDst
          (net.nwState p.pDst).2 t n pli plt es ci hae
        have hctd : d.currentTerm = t := handleAppendEntries_true_reply_currentTerm
          p.pDst (net.nwState p.pDst).2 t n pli plt es ci hae
        -- the leader's term IS the request's term
        have hctL : (net.nwState p.pSrc).2.currentTerm = t := by
          rw [← hteq]; exact hct
        -- es is non-empty: e sits at a positive index at or below its max
        have hgt := entries_gt_0_invariant net hreach p.pSrc e hin
        have hesne : es ≠ [] := by
          intro hnil
          rw [hnil] at hle
          replace hle : e.eIndex ≤ 0 := hle
          exact Nat.not_succ_le_zero _ (Nat.le_trans hgt hle)
        obtain ⟨x, hx, hxi, -⟩ := maxIndex_non_empty hesne
        -- the max entry of es is in the receiver's NEW log
        have hxd : x ∈ d.log := by
          rcases handleAppendEntries_true_reply_log p.pDst
              (net.nwState p.pDst).2 t n pli plt es ci hae with hall | ⟨hfalse, hdlog⟩
          · exact hall x hx
          · rw [hdlog]
            exact appendEntries_haveNewEntries_false net hreach p t n pli
              plt es ci p.pDst x hp_in hbody hfalse hx
        -- ... and in the leader's log (the in-flight request's entries)
        have hxL : x ∈ (net.nwState p.pSrc).2.log :=
          append_entries_leader_invariant net hreach p t n pli plt es ci
            p.pSrc x hp_in hbody hx hctL hty
        -- entries_match at the SUCCESSOR net glues e across
        have hmatch := entries_match_invariant ⟨ps', st'⟩ hreach' p.pDst p.pSrc
        replace hmatch : entries_match (st' p.pDst).2.log
            (st' p.pSrc).2.log := hmatch
        rw [hst p.pDst, update_same, hst p.pSrc, update_neq _ _ hsrc]
          at hmatch
        replace hmatch : entries_match d.log (net.nwState p.pSrc).2.log :=
          hmatch
        have hle' : e.eIndex ≤ x.eIndex := by
          rw [hxi]
          exact hle
        have he_d : e ∈ d.log :=
          (hmatch x x e rfl rfl hxd hxL hle').mpr hin
        -- log_all_entries at the SUCCESSOR net reads off the record
        have hlae := log_all_entries_invariant ⟨ps', st'⟩ hreach' p.pDst e
          (by show e ∈ (st' p.pDst).2.log
              rw [hst p.pDst, update_same]
              exact he_d)
          (by show e.eTerm = (st' p.pDst).2.currentTerm
              rw [hst p.pDst, update_same]
              show e.eTerm = d.currentTerm
              rw [hctd, ← hteq]
              exact hterm)
        replace hlae : (e.eTerm, e) ∈ (st' p.pDst).1.allEntries := hlae
        rw [hterm] at hlae
        exact hlae

/-- `MatchIndexAllEntriesProof.v:1101-1127`
(`match_index_all_entries_invariant`'s inductive form) — assembled
through THE PRIMED PRINCIPLE `refined_raft_net_invariant'`, exactly
upstream: the append_entries obligation primed, every other handler
through its `_'_weak` bridge. This is the state-side primed set's
discharge witness (constitution §3.3): all eleven obligations
instantiated on a real invariant, the successor-reachability premise
consumed in the AE case. -/
theorem match_index_all_entries_inv_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      match_index_all_entries_inv net :=
  refined_raft_net_invariant' mia_init
    (refined_raft_net_invariant_client_request'_weak mia_client_request)
    (refined_raft_net_invariant_timeout'_weak mia_timeout)
    mia_append_entries
    (refined_raft_net_invariant_append_entries_reply'_weak
      mia_append_entries_reply)
    (refined_raft_net_invariant_request_vote'_weak mia_request_vote)
    (refined_raft_net_invariant_request_vote_reply'_weak
      mia_request_vote_reply)
    (refined_raft_net_invariant_do_leader'_weak mia_do_leader)
    (refined_raft_net_invariant_do_generic_server'_weak
      mia_do_generic_server)
    mia_state_same
    (refined_raft_net_invariant_reboot'_weak mia_reboot)

/-- `MatchIndexAllEntriesInterface.v:17-22`
(`match_index_all_entries_invariant`, the interface field). -/
theorem match_index_all_entries_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      match_index_all_entries net :=
  fun net hreach => (match_index_all_entries_inv_invariant net hreach).1

end MatchIndexAllEntries

end Raft
end VerdiCompat
