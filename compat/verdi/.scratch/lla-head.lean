import VerdiCompat.AppendEntriesChain

/-!
# The GAP-7 assembly — the logs ↔ leaderLogs invariant chain

Campaign Arc 3 unit 8 (the fresh closure derivation is in the arc log's
unit-8 opening entry: exactly six upstream proof files, 3,519 lines, no
msg-ghost), 1:1 against the sources @ a3375e8 —

- `Prefix` (StructTact's `Prefix` fixpoint, `StructTact/ListUtil.v`) and
  `Prefix_sane` / `append_entries_leaderLogs`
  (`Raft/AppendEntriesRequestLeaderLogsInterface.v:9-22`): every
  in-flight AppendEntries' entry list splits as own-term entries atop a
  prefix of a recorded leaderLog snapshot at the packet's term
  (`RaftProofs/AppendEntriesRequestLeaderLogsProof.v`, 621 lines);
- `logs_leaderLogs` / `logs_leaderLogs_nw`
  (`Raft/LogsLeaderLogsInterface.v:9-30`): every host log entry (and
  every in-flight entry) sits atop a leaderLog snapshot at its own term
  (`RaftProofs/LogsLeaderLogsProof.v`, 848 lines);
- **`leaderLogs_preserved`** (`Raft/LeaderLogsPreservedInterface.v:9-15`,
  GAP-7b) via `RaftProofs/LeaderLogsPreservedProof.v` (263 lines);
- `allEntries_leaderLogs_term`
  (`Raft/AllEntriesLeaderLogsTermInterface.v:9-15`) via
  `RaftProofs/AllEntriesLeaderLogsTermProof.v` (342 lines);
- `allEntries_log` (`Raft/AllEntriesLogInterface.v:10-19`) via
  `RaftProofs/AllEntriesLogProof.v` (1,089 lines);
- **`allEntries_votesWithLog`**
  (`Raft/AllEntriesVotesWithLogInterface.v:10-19`, GAP-7a) via
  `RaftProofs/AllEntriesVotesWithLogProof.v` (356 lines).

Statements 1:1 with the Interface files; proofs re-derived through the
ported principles.
-/

namespace VerdiCompat
namespace Raft

section LeaderLogsAssembly
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

local notation "RefinedNet" =>
  Network (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RefinedPacket" =>
  Packet (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RaftNet" => Network (raft_base_params (P := P)) raft_multi_params

/-! ## Prefix (StructTact) and the interface statement -/

/-- StructTact `ListUtil.v` (`Prefix`), the fixpoint form 1:1. -/
def Prefix {α : Type _} : List α → List α → Prop
  | [], _ => True
  | _ :: _, [] => False
  | a :: l1, b :: l2 => a = b ∧ Prefix l1 l2

omit O R in
theorem Prefix_refl {α : Type _} (l : List α) : Prefix l l := by
  induction l with
  | nil => trivial
  | cons a l ih => exact ⟨rfl, ih⟩

omit O R in
theorem Prefix_nil {α : Type _} (l : List α) : Prefix ([] : List α) l :=
  trivial

omit O R in
/-- A prefix's members are members (`StructTact` `Prefix_In`). -/
theorem Prefix_In {α : Type _} {l l' : List α} (hp : Prefix l l') :
    ∀ x ∈ l, x ∈ l' := by
  induction l generalizing l' with
  | nil => exact fun x hx => nomatch hx
  | cons a l ih =>
    cases l' with
    | nil => exact absurd hp not_false
    | cons b l'' =>
      obtain ⟨rfl, hp'⟩ := hp
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hp' x hx)

/-- `AppendEntriesRequestLeaderLogsInterface.v:9-10` (`Prefix_sane`). -/
def Prefix_sane (l l' : List (entry (P := P))) (i : logIndex) : Prop :=
  l ≠ [] ∨ i = maxIndex l'

/-- `AppendEntriesRequestLeaderLogsInterface.v:12-22`
(`append_entries_leaderLogs`): every in-flight AppendEntries carries
`es' ++ ll'` where `es'` is all at the packet's term and `ll'` prefixes
a recorded leaderLog snapshot at that term, with the prevLog position
either past the snapshot, inside it, or at the origin. -/
def append_entries_leaderLogs (net : RefinedNet) : Prop :=
  ∀ (p : RefinedPacket) (t : term) (n : name (P := P)) (pli : logIndex)
    (plt : term) (es : List (entry (P := P))) (ci : logIndex),
    p ∈ net.nwPackets → p.pBody = .AppendEntries t n pli plt es ci →
    ∃ (h : name (P := P)) (ll es' ll' : List (entry (P := P))),
      es = es' ++ ll' ∧
      (∀ e ∈ es', e.eTerm = t) ∧
      (t, ll) ∈ (net.nwState h).1.leaderLogs ∧
      Prefix ll' ll ∧
      ((plt = t ∧ pli > maxIndex ll) ∨
       (∃ e, e ∈ ll ∧ e.eIndex = pli ∧ e.eTerm = plt ∧
         Prefix_sane ll' ll pli) ∨
       (plt = 0 ∧ pli = 0 ∧ ll' = ll))

/-- Witness transport: the packet-side witness structure mentions the
network only through the leaderLog membership, and leaderLogs only grow
at the updated node. -/
theorem aell_transport {net net' : RefinedNet} {u : name (P := P)}
    {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hgrow : ∀ (t : term) (ll : List (entry (P := P))),
      (t, ll) ∈ (net.nwState u).1.leaderLogs → (t, ll) ∈ gd.leaderLogs)
    {t : term} {pli : logIndex} {plt : term} {es : List (entry (P := P))}
    (hw : ∃ (h : name (P := P)) (ll es' ll' : List (entry (P := P))),
      es = es' ++ ll' ∧ (∀ e ∈ es', e.eTerm = t) ∧
      (t, ll) ∈ (net.nwState h).1.leaderLogs ∧ Prefix ll' ll ∧
      ((plt = t ∧ pli > maxIndex ll) ∨
       (∃ e, e ∈ ll ∧ e.eIndex = pli ∧ e.eTerm = plt ∧
         Prefix_sane ll' ll pli) ∨
       (plt = 0 ∧ pli = 0 ∧ ll' = ll))) :
    ∃ (h : name (P := P)) (ll es' ll' : List (entry (P := P))),
      es = es' ++ ll' ∧ (∀ e ∈ es', e.eTerm = t) ∧
      (t, ll) ∈ (net'.nwState h).1.leaderLogs ∧ Prefix ll' ll ∧
      ((plt = t ∧ pli > maxIndex ll) ∨
       (∃ e, e ∈ ll ∧ e.eIndex = pli ∧ e.eTerm = plt ∧
         Prefix_sane ll' ll pli) ∨
       (plt = 0 ∧ pli = 0 ∧ ll' = ll)) := by
  obtain ⟨h, ll, es', ll', h1, h2, h3, h4, h5⟩ := hw
  refine ⟨h, ll, es', ll', h1, h2, ?_, h4, h5⟩
  rw [hst h]
  by_cases heq : h = u
  · subst heq
    rw [update_same]
    exact hgrow t ll h3
  · rw [update_neq _ _ heq]
    exact h3

/-! ## findGtIndex-over-append machinery
(`AppendEntriesRequestLeaderLogsProof.v:374-478`) -/

omit O in
/-- `AppendEntriesRequestLeaderLogsProof.v:374-384`
(`sorted_findGtIndex_0`). -/
theorem sorted_findGtIndex_0 {l : List (entry (P := P))}
    (hpos : ∀ e ∈ l, e.eIndex > 0) (_hs : sorted l) :
    findGtIndex l 0 = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    unfold findGtIndex
    split
    · rename_i hgt
      rw [ih (fun e he => hpos e (List.mem_cons_of_mem _ he)) _hs.2]
    · rename_i hgt
      exfalso
      apply hgt
      simpa [Nat.blt_eq] using hpos a (List.mem_cons_self ..)

omit O in
/-- `AppendEntriesRequestLeaderLogsProof.v:440-446`
(`findGtIndex_Prefix`). -/
theorem findGtIndex_Prefix (l : List (entry (P := P))) (i : logIndex) :
    Prefix (findGtIndex l i) l := by
  induction l with
  | nil => trivial
  | cons a as ih =>
    unfold findGtIndex
    split
    · exact ⟨rfl, ih⟩
    · trivial

omit O in
/-- `AppendEntriesRequestLeaderLogsProof.v:409-426`
(`findGtIndex_app_in_1`): cutting a sorted `l1 ++ l2` above a member of
`l1` stays inside `l1`. -/
theorem findGtIndex_app_in_1 {l1 l2 : List (entry (P := P))}
    {e : entry (P := P)} (hs : sorted (l1 ++ l2)) (he : e ∈ l1) :
    ∃ l', findGtIndex (l1 ++ l2) e.eIndex = l' ∧ ∀ x ∈ l', x ∈ l1 := by
  induction l1 with
  | nil => exact nomatch he
  | cons a l1 ih =>
    rcases List.mem_cons.mp he with rfl | he'
    · refine ⟨[], ?_, fun x hx => nomatch hx⟩
      show findGtIndex (e :: (l1 ++ l2)) e.eIndex = []
      unfold findGtIndex
      split
      · rename_i hgt
        simp only [Nat.blt_eq] at hgt
        exact absurd hgt (Nat.lt_irrefl _)
      · rfl
    · have hgt : a.eIndex > e.eIndex :=
        (hs.1 e (List.mem_append.mpr (Or.inl he'))).1
      obtain ⟨l', hfg, hsub⟩ := ih hs.2 he'
      refine ⟨a :: l', ?_, ?_⟩
      · show findGtIndex (a :: (l1 ++ l2)) e.eIndex = a :: l'
        unfold findGtIndex
        split
        · rw [hfg]
        · rename_i hng
          exact absurd (by simpa [Nat.blt_eq] using hgt) hng
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hsub x hx)

omit O in
/-- `AppendEntriesRequestLeaderLogsProof.v:428-438` (`sorted_app_in_1`):
a positive-index member of the front block of a sorted append lies
strictly above everything behind it. -/
theorem sorted_app_in_1 {l1 l2 : List (entry (P := P))}
    {e : entry (P := P)} (hs : sorted (l1 ++ l2)) (hpos : e.eIndex > 0)
    (he : e ∈ l1) : e.eIndex > maxIndex l2 := by
  induction l1 with
  | nil => exact nomatch he
  | cons a l1 ih =>
    rcases List.mem_cons.mp he with rfl | he'
    · cases l2 with
      | nil => exact hpos
      | cons b l2' =>
        exact (hs.1 b (List.mem_append.mpr (Or.inr (List.mem_cons_self ..)))).1
    · exact ih hs.2 he'

omit O in
/-- `AppendEntriesRequestLeaderLogsProof.v:448-463`
(`findGtIndex_app_in_2`): cutting a sorted `l1 ++ l2` above a member of
`l2` keeps all of `l1` plus a prefix of `l2`. -/
theorem findGtIndex_app_in_2 {l1 l2 : List (entry (P := P))}
    {e : entry (P := P)} (hs : sorted (l1 ++ l2)) (he : e ∈ l2) :
    ∃ l', findGtIndex (l1 ++ l2) e.eIndex = l1 ++ l' ∧ Prefix l' l2 := by
  induction l1 with
  | nil => exact ⟨findGtIndex l2 e.eIndex, rfl, findGtIndex_Prefix l2 e.eIndex⟩
  | cons a l1 ih =>
    have hgt : a.eIndex > e.eIndex :=
      (hs.1 e (List.mem_append.mpr (Or.inr he))).1
    obtain ⟨l', hfg, hpref⟩ := ih hs.2
    refine ⟨l', ?_, hpref⟩
    show findGtIndex (a :: (l1 ++ l2)) e.eIndex = (a :: l1) ++ l'
    unfold findGtIndex
    split
    · rw [hfg]
      rfl
    · rename_i hng
      exact absurd (by simpa [Nat.blt_eq] using hgt) hng

omit O in
/-- `AppendEntriesRequestLeaderLogsProof.v:465-478`
(`findGtIndex_app_eq`): if the cut above a member of `l2` returns
exactly `l1`, that member closes `l2` (it is `l2`'s max index). -/
theorem findGtIndex_app_eq {l1 l2 : List (entry (P := P))}
    {e : entry (P := P)} (hs : sorted (l1 ++ l2)) (he : e ∈ l2)
    (hfg : findGtIndex (l1 ++ l2) e.eIndex = l1) :
    e.eIndex = maxIndex l2 := by
  induction l1 with
  | nil =>
    cases l2 with
    | nil => exact nomatch he
    | cons b l2' =>
      replace hfg : findGtIndex (b :: l2') e.eIndex = [] := hfg
      unfold findGtIndex at hfg
      split at hfg
      · exact nomatch hfg
      · rename_i hng
        simp only [Nat.blt_eq, Nat.not_lt] at hng
        rcases List.mem_cons.mp he with rfl | he'
        · rfl
        · exact absurd (hs.1 e he').1 (Nat.not_lt.mpr hng)
  | cons a l1 ih =>
    replace hfg : findGtIndex (a :: (l1 ++ l2)) e.eIndex = a :: l1 := hfg
    unfold findGtIndex at hfg
    split at hfg
    · exact ih hs.2 (List.tail_eq_of_cons_eq hfg)
    · exact nomatch hfg

/-! ## doLeader's replica-message shape, nextIndex-aware
(`AppendEntriesRequestLeaderLogsProof.v:304-335`, `doLeader_spec`) -/

omit O in
/-- `AppendEntriesRequestLeaderLogsProof.v:304-335` (`doLeader_spec`),
in the exact-shape style of `doLeader_messages_full` but RETAINING that
the prevLog index is `pred (getNextIndex st host)` for some host — the
piece `nextIndex_sanity` needs to rule the unresolvable case out. -/
theorem doLeader_messages_nextIndex (st : raft_data (P := P))
    (me : name (P := P)) {os st' ms}
    (h : doLeader st me = (os, st', ms)) :
    ∀ q ∈ ms, ∃ host,
      q.2 = msg.AppendEntries (P := P) st.currentTerm me
        (Nat.pred (getNextIndex st host))
        (match findAtIndex st.log (Nat.pred (getNextIndex st host)) with
         | some e => e.eTerm
         | none => 0)
        (findGtIndex st.log (Nat.pred (getNextIndex st host)))
        (advanceCommitIndex st me).commitIndex := by
  unfold doLeader at h
  simp only [] at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨-, -, rfl⟩ := h
  all_goals intro q hq
  · simp only [List.mem_map] at hq
    obtain ⟨node, -, rfl⟩ := hq
    exact ⟨node, rfl⟩
  · exact nomatch hq
  · exact nomatch hq

/-- `AppendEntriesRequestLeaderLogsProof.v:346-372` (`nextIndex_sanity`):
a leader's nonzero prevLog position always resolves in its own log —
lifted `nextIndex_safety` bounds it by `maxIndex`, lifted contiguity
produces the entry, and sortedness makes `findAtIndex` find it. -/
theorem nextIndex_sanity :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      ∀ (h h' : name (P := P)),
        (net.nwState h).2.type = .Leader →
        Nat.pred (getNextIndex (net.nwState h).2 h') ≠ 0 →
        ∃ e, findAtIndex (net.nwState h).2.log
          (Nat.pred (getNextIndex (net.nwState h).2 h')) = some e := by
  intro net hreach h h' hty hne
  have hnis := lift_prop _ nextIndex_safety_invariant net hreach h h'
  have hle := hnis hty
  have hpos : 0 < Nat.pred (getNextIndex (net.nwState h).2 h') :=
    Nat.pos_of_ne_zero hne
  obtain ⟨e, hei, hemem⟩ := (logs_contiguous net hreach h).1
    (Nat.pred (getNextIndex (net.nwState h).2 h')) ⟨hpos, hle⟩
  exact ⟨e, findAtIndex_intro (sorted_host_lifted net hreach h) hemem hei
    (sorted_uniqueIndices (sorted_host_lifted net hreach h))⟩

/-- `AppendEntriesRequestLeaderLogsProof.v:597-615`
(`append_entries_leaderLogs_invariant`): the ten transport cases ride
`aell_transport` (leaderLogs only grow; fresh non-AE sends are ruled
out by the handler message shapes); the CREATION case is `doLeader`,
where `leaders_have_leaderLogs_strong` splits the sender's log as
`es0 ++ ll` over its own snapshot and the findGtIndex-over-append
machinery classifies the cut (`:480-566`). -/
theorem append_entries_leaderLogs_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      append_entries_leaderLogs net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init: no packets
    intro p0 t0 n1 pli2 plt2 es2 ci2 hp0 _
    exact nomatch hp0
  · -- client_request: no packets sent; leaderLogs unchanged
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst hps
    obtain ⟨-, -, -, -, hl⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    intro p0 t0 n1 pli2 plt2 es2 ci2 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · exact h1
      · rw [hl] at h1
        simp [send_packets] at h1
    refine aell_transport hst ?_
      (hP p0 t0 n1 pli2 plt2 es2 ci2 hold hbody0)
    intro t2 ll hll
    subst hgd
    rw [(update_elections_data_client_request_ghost h (net.nwState h)
      client id c).2.2.2]
    exact hll
  · -- timeout: only RequestVotes; leaderLogs unchanged
    intro net h st' ps' gd out d l hto hgd hP _hreach hst hps
    obtain ⟨-, -, hmsgs⟩ := handleTimeout_spec h (net.nwState h).2 hto
    intro p0 t0 n1 pli2 plt2 es2 ci2 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp h1
        obtain ⟨t3, c3, l3, l4, hq2⟩ := hmsgs m0 hm0
        replace hbody0 : m0.2 = msg.AppendEntries t0 n1 pli2 plt2 es2 ci2 :=
          hbody0
        rw [hq2] at hbody0
        exact nomatch hbody0
    refine aell_transport hst ?_
      (hP p0 t0 n1 pli2 plt2 es2 ci2 hold hbody0)
    intro t2 ll hll
    subst hgd
    rw [(update_elections_data_timeout_ghost h (net.nwState h)).1]
    exact hll
  · -- append_entries: the reply is an AppendEntriesReply; ghost keeps
    -- leaderLogs
    intro xs p ys net st' ps' gd d m t n0 pli plt es ci hae hgd _hbody hP
      _hreach hpkts hst hps
    obtain ⟨-, -, -, t', es', r', hmshape⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst).2 t n0 pli plt
        es ci hae
    intro p0 t0 n1 pli2 plt2 es2 ci2 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · rw [hpkts]
        exact mem_of_mem_remove_middle h1
      · exfalso
        rw [h1] at hbody0
        replace hbody0 : m = msg.AppendEntries t0 n1 pli2 plt2 es2 ci2 :=
          hbody0
        rw [hmshape] at hbody0
        exact nomatch hbody0
    refine aell_transport hst ?_
      (hP p0 t0 n1 pli2 plt2 es2 ci2 hold hbody0)
    intro t2 ll hll
    subst hgd
    rw [(update_elections_data_appendEntries_ghost p.pDst
      (net.nwState p.pDst) t n0 pli plt es ci).2.2.2]
    exact hll
  · -- append_entries_reply: no messages; ghost untouched
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP _hreach
      hpkts hst hps
    obtain ⟨-, -, hl⟩ := handleAppendEntriesReply_spec p.pDst
      (net.nwState p.pDst).2 p.pSrc t es res haer
    intro p0 t0 n1 pli2 plt2 es2 ci2 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · rw [hpkts]
        exact mem_of_mem_remove_middle h1
      · rw [hl] at h1
        simp [send_packets] at h1
    refine aell_transport hst ?_
      (hP p0 t0 n1 pli2 plt2 es2 ci2 hold hbody0)
    intro t2 ll hll
    rw [hgd]
    exact hll
  · -- request_vote: the reply is a RequestVoteReply; leaderLogs
    -- unchanged
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP
      _hreach hpkts hst hps
    obtain ⟨t'', v'', hmshape⟩ := handleRequestVote_reply_shape p.pDst
      (net.nwState p.pDst).2 t p.pSrc lli llt hrv
    intro p0 t0 n1 pli2 plt2 es2 ci2 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · rw [hpkts]
        exact mem_of_mem_remove_middle h1
      · exfalso
        rw [h1] at hbody0
        replace hbody0 : m = msg.AppendEntries t0 n1 pli2 plt2 es2 ci2 :=
          hbody0
        rw [hmshape] at hbody0
        exact nomatch hbody0
    refine aell_transport hst ?_
      (hP p0 t0 n1 pli2 plt2 es2 ci2 hold hbody0)
    intro t2 ll hll
    subst hgd
    rw [(update_elections_data_requestVote_cronies p.pDst p.pSrc t p.pSrc
      lli llt (net.nwState p.pDst)).2.1]
    exact hll
  · -- request_vote_reply: no sends; old snapshots survive the cons
    intro xs p ys net st' ps' gd d t v hrvr hgd _hbody hP _hreach hpkts
      hst hps
    intro p0 t0 n1 pli2 plt2 es2 ci2 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rw [hpkts]
      exact mem_of_mem_remove_middle (hps p0 hp0)
    refine aell_transport hst ?_
      (hP p0 t0 n1 pli2 plt2 es2 ci2 hold hbody0)
    intro t2 ll hll
    subst hgd
    exact update_elections_data_requestVoteReply_leaderLogs_old p.pDst
      p.pSrc t v (net.nwState p.pDst) hll
  · -- do_leader: THE CREATION CASE
    intro net st' ps' gd d h os d' ms hdl hP hreach hstate hst hps
    intro p0 t0 n1 pli2 plt2 es2 ci2 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · refine aell_transport hst ?_
        (hP p0 t0 n1 pli2 plt2 es2 ci2 hold hbody0)
      intro t2 ll hll
      rw [hstate] at hll
      exact hll
    · obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hnew
      have htype : d.type = .Leader := doLeader_messages_leader d h hdl hm0
      obtain ⟨host, hq2⟩ := doLeader_messages_nextIndex d h hdl m0 hm0
      replace hbody0 : m0.2 = msg.AppendEntries t0 n1 pli2 plt2 es2 ci2 :=
        hbody0
      rw [hq2] at hbody0
      injection hbody0 with f1 f2 f3 f4 f5 f6
      subst f1 f3 f5
      have hty_net : (net.nwState h).2.type = .Leader := by
        rw [hstate]
        exact htype
      obtain ⟨ll, es0, hllmem, hsplit, hterm⟩ :=
        leaders_have_leaderLogs_strong_invariant net hreach h hty_net
      rw [hstate] at hllmem hsplit hterm
      replace hllmem : (d.currentTerm, ll) ∈ gd.leaderLogs := hllmem
      replace hsplit : d.log = es0 ++ ll := hsplit
      replace hterm : ∀ e ∈ es0, e.eTerm = d.currentTerm := hterm
      have hsorted : sorted d.log := by
        have hsl := sorted_host_lifted net hreach h
        rw [hstate] at hsl
        exact hsl
      have hgt0 : ∀ e ∈ d.log, e.eIndex > 0 := by
        intro e he
        refine entries_gt_0_invariant net hreach h e ?_
        rw [hstate]
        exact he
      have hsorted' : sorted (es0 ++ ll) := hsplit ▸ hsorted
      have hmem' : (d.currentTerm, ll) ∈ (st' h).1.leaderLogs := by
        rw [hst h, update_same]
        exact hllmem
      rcases hfaeq : findAtIndex d.log (Nat.pred (getNextIndex d host))
        with _ | e0
      · -- prevLog unresolved: either the origin, or impossible
        rw [hfaeq] at f4
        simp only [] at f4
        by_cases hz : Nat.pred (getNextIndex d host) = 0
        · have hlogeq : findGtIndex d.log 0 = d.log :=
            sorted_findGtIndex_0 hgt0 hsorted
          refine ⟨h, ll, es0, ll, ?_, hterm, hmem', Prefix_refl ll, ?_⟩
          · rw [hz, hlogeq, hsplit]
          · exact Or.inr (Or.inr ⟨f4.symm, hz, rfl⟩)
        · exfalso
          obtain ⟨e, hfae⟩ := nextIndex_sanity net hreach h host hty_net
            (by rw [hstate]; exact hz)
          rw [hstate] at hfae
          replace hfae :
              findAtIndex d.log (Nat.pred (getNextIndex d host)) = some e :=
            hfae
          rw [hfaeq] at hfae
          exact nomatch hfae
      · -- prevLog resolves at e0 ∈ d.log = es0 ++ ll
        rw [hfaeq] at f4
        simp only [] at f4
        obtain ⟨he0mem, he0idx⟩ := findAtIndex_elim hfaeq
        have he0split : e0 ∈ es0 ++ ll := hsplit ▸ he0mem
        rcases List.mem_append.mp he0split with he0es | he0ll
        · -- e0 in the own-term top: everything cut is own-term (disj 1)
          obtain ⟨l', hfg, hsub⟩ := findGtIndex_app_in_1 hsorted' he0es
          refine ⟨h, ll, l', [], ?_, ?_, hmem', Prefix_nil ll, ?_⟩
          · rw [List.append_nil, ← hfg, he0idx, hsplit]
          · intro x hx
            exact hterm x (hsub x hx)
          · refine Or.inl ⟨f4 ▸ hterm e0 he0es, ?_⟩
            rw [← he0idx]
            exact sorted_app_in_1 hsorted' (hgt0 e0 he0mem) he0es
        · -- e0 in the snapshot: the cut is es0 ++ (prefix of ll) (disj 2)
          obtain ⟨l', hfg, hpref⟩ := findGtIndex_app_in_2 hsorted' he0ll
          refine ⟨h, ll, es0, l', ?_, hterm, hmem', hpref, ?_⟩
          · rw [← hfg, he0idx, hsplit]
          · refine Or.inr (Or.inl ⟨e0, he0ll, he0idx, f4, ?_⟩)
            cases l' with
            | nil =>
              refine Or.inr ?_
              rw [← he0idx]
              refine findGtIndex_app_eq hsorted' he0ll ?_
              rw [hfg, List.append_nil]
            | cons a l'' =>
              exact Or.inl (List.cons_ne_nil a l'')
  · -- do_generic_server: no messages; ghost untouched
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps
    obtain ⟨-, -, -, -, -, hms⟩ := doGenericServer_spec h d hgs
    intro p0 t0 n1 pli2 plt2 es2 ci2 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · exact h1
      · rw [hms] at h1
        simp [send_packets] at h1
    refine aell_transport hst ?_
      (hP p0 t0 n1 pli2 plt2 es2 ci2 hold hbody0)
    intro t2 ll hll
    rw [hstate] at hll
    exact hll
  · -- state_same_packet_subset
    intro net net' hstates hsub hP _hreach p0 t0 n1 pli2 plt2 es2 ci2 hp0
      hbody0
    obtain ⟨x, ll, es', ll', h1, h2, h3, h4, h5⟩ :=
      hP p0 t0 n1 pli2 plt2 es2 ci2 (hsub p0 hp0) hbody0
    rw [hstates x] at h3
    exact ⟨x, ll, es', ll', h1, h2, h3, h4, h5⟩
  · -- reboot: ghost and packets survive
    intro net net' gd d h d' _hrb hP _hreach hstate hst hpkts
    intro p0 t0 n1 pli2 plt2 es2 ci2 hp0 hbody0
    rw [← hpkts] at hp0
    refine aell_transport hst ?_
      (hP p0 t0 n1 pli2 plt2 es2 ci2 hp0 hbody0)
    intro t2 ll hll
    rw [hstate] at hll
    exact hll

end LeaderLogsAssembly
end Raft
end VerdiCompat
