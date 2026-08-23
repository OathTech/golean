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

/-! ## The logs_leaderLogs support layer (`CommonTheorems.v` slices,
constructive per GAP-4; `removeAfterIndex_same_sufficient` re-routed
through a direct `sorted_mem_eq` induction in place of upstream's
`sorted_Permutation_eq`/`NoDup_Permutation` chain). The four cons-step
lemmas make every guard rewrite explicit (the `unfold`-both-sides trap
recorded in the arc log). -/

omit O in
theorem findGtIndex_cons_pos {a : entry (P := P)}
    {as : List (entry (P := P))} {i : logIndex}
    (h : (a.eIndex >? i) = true) :
    findGtIndex (a :: as) i = a :: findGtIndex as i := by
  show (if (a.eIndex >? i) = true then a :: findGtIndex as i else []) = _
  rw [if_pos h]

omit O in
theorem findGtIndex_cons_neg {a : entry (P := P)}
    {as : List (entry (P := P))} {i : logIndex}
    (h : ¬ (a.eIndex >? i) = true) :
    findGtIndex (a :: as) i = [] := by
  unfold findGtIndex
  rw [if_neg h]

omit O in
theorem removeAfterIndex_cons_pos {a : entry (P := P)}
    {as : List (entry (P := P))} {i : logIndex}
    (h : (a.eIndex <=? i) = true) :
    removeAfterIndex (a :: as) i = a :: as := by
  unfold removeAfterIndex
  rw [if_pos h]

omit O in
theorem removeAfterIndex_cons_neg {a : entry (P := P)}
    {as : List (entry (P := P))} {i : logIndex}
    (h : ¬ (a.eIndex <=? i) = true) :
    removeAfterIndex (a :: as) i = removeAfterIndex as i := by
  show (if (a.eIndex <=? i) = true then a :: as else removeAfterIndex as i)
    = _
  rw [if_neg h]

omit O in
/-- `CommonTheorems.v:1922-1932` (`removeAfterIndex_eq`). -/
theorem removeAfterIndex_eq {l : List (entry (P := P))} {i : logIndex}
    (h : ∀ e ∈ l, e.eIndex ≤ i) : removeAfterIndex l i = l := by
  cases l with
  | nil => rfl
  | cons a as =>
    exact removeAfterIndex_cons_pos
      (by simpa [Nat.ble_eq] using h a (List.mem_cons_self ..))

omit O in
/-- `CommonTheorems.v` (`contiguous_index_singleton`). -/
theorem contiguous_index_singleton {x : entry (P := P)} {i : logIndex}
    (hc : contiguous_range_exact_lo [x] i) : x.eIndex = i + 1 := by
  obtain ⟨h1, h2⟩ := hc
  have hgt : i < x.eIndex := h2 x (List.mem_cons_self ..)
  rcases Nat.lt_or_ge (i + 1) x.eIndex with hlt | hge
  · obtain ⟨e, hei, hemem⟩ := h1 (i + 1)
      ⟨Nat.lt_succ_self i, Nat.le_of_lt hlt⟩
    rcases List.mem_cons.mp hemem with rfl | h
    · exact absurd (hei ▸ hlt) (Nat.lt_irrefl _)
    · exact nomatch h
  · exact Nat.le_antisymm hge (Nat.succ_le_of_lt hgt)

omit O in
/-- `CommonTheorems.v` (`cons_contiguous_sorted`). -/
theorem cons_contiguous_sorted {a : entry (P := P)}
    {l : List (entry (P := P))} {i : logIndex} (hs : sorted (a :: l))
    (hc : contiguous_range_exact_lo (a :: l) i) :
    contiguous_range_exact_lo l i := by
  obtain ⟨h1, h2⟩ := hc
  refine ⟨?_, fun e he => h2 e (List.mem_cons_of_mem _ he)⟩
  intro j hj
  obtain ⟨hj1, hj2⟩ := hj
  cases l with
  | nil =>
    exfalso
    replace hj2 : j ≤ 0 := hj2
    exact absurd (Nat.lt_of_lt_of_le hj1 hj2) (Nat.not_lt.mpr (Nat.zero_le i))
  | cons b l' =>
    have hmaxlt : maxIndex (b :: l') < a.eIndex := by
      show b.eIndex < a.eIndex
      exact (hs.1 b (List.mem_cons_self ..)).1
    obtain ⟨e, hei, hemem⟩ := h1 j
      ⟨hj1, Nat.le_of_lt (Nat.lt_of_le_of_lt hj2 hmaxlt)⟩
    rcases List.mem_cons.mp hemem with rfl | he
    · exact absurd (Nat.lt_of_le_of_lt hj2 hmaxlt)
        (hei ▸ Nat.lt_irrefl _)
    · exact ⟨e, hei, he⟩

omit O in
/-- `CommonTheorems.v:1525-1536` (`contiguous_app`). -/
theorem contiguous_app {l1 l2 : List (entry (P := P))} {i : logIndex}
    (hs : sorted (l1 ++ l2)) (hc : contiguous_range_exact_lo (l1 ++ l2) i) :
    contiguous_range_exact_lo l2 i := by
  induction l1 with
  | nil => exact hc
  | cons a l1 ih => exact ih hs.2 (cons_contiguous_sorted hs hc)

omit O in
/-- `CommonTheorems.v:1576-1587` (`removeAfterIndex_contiguous`). -/
theorem removeAfterIndex_contiguous {l : List (entry (P := P))}
    {i i' : logIndex} (hs : sorted l)
    (hc : contiguous_range_exact_lo l i) :
    contiguous_range_exact_lo (removeAfterIndex l i') i := by
  induction l with
  | nil => exact hc
  | cons a as ih =>
    by_cases hle : (a.eIndex <=? i') = true
    · rw [removeAfterIndex_cons_pos hle]
      exact hc
    · rw [removeAfterIndex_cons_neg hle]
      exact ih hs.2 (cons_contiguous_sorted hs hc)

omit O in
/-- Sorted logs with the same members coincide — the constructive spine
under `removeAfterIndex_same_sufficient` (upstream routes it through
`sorted_Permutation_eq` + `NoDup_Permutation`). -/
theorem sorted_mem_eq {l l' : List (entry (P := P))} (hs : sorted l)
    (hs' : sorted l') (hmem : ∀ e, e ∈ l ↔ e ∈ l') : l = l' := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => rfl
    | cons b l₁ =>
      exact absurd ((hmem b).mpr (List.mem_cons_self ..)) (fun h => nomatch h)
  | cons a l₀ ih =>
    cases l' with
    | nil =>
      exact absurd ((hmem a).mp (List.mem_cons_self ..)) (fun h => nomatch h)
    | cons b l₁ =>
      have hab : a = b := by
        rcases List.mem_cons.mp ((hmem a).mp (List.mem_cons_self ..)) with
          h | ha1
        · exact h
        · rcases List.mem_cons.mp ((hmem b).mpr (List.mem_cons_self ..)) with
            h | hb0
          · exact h.symm
          · exact absurd (hs.1 b hb0).1
              (Nat.not_lt.mpr (Nat.le_of_lt (hs'.1 a ha1).1))
      subst hab
      have htails : ∀ e, e ∈ l₀ ↔ e ∈ l₁ := by
        intro e
        constructor
        · intro he
          rcases List.mem_cons.mp ((hmem e).mp (List.mem_cons_of_mem _ he))
            with rfl | h
          · exact absurd (hs.1 e he).1 (Nat.lt_irrefl _)
          · exact h
        · intro he
          rcases List.mem_cons.mp ((hmem e).mpr (List.mem_cons_of_mem _ he))
            with rfl | h
          · exact absurd (hs'.1 e he).1 (Nat.lt_irrefl _)
          · exact h
      rw [ih hs.2 hs'.2 htails]

omit O in
/-- `CommonTheorems.v:1624-1642` (`removeAfterIndex_same_sufficient`). -/
theorem removeAfterIndex_same_sufficient {x : logIndex}
    {l l' : List (entry (P := P))} (hs : sorted l) (hs' : sorted l')
    (h1 : ∀ e, e.eIndex ≤ x → e ∈ l → e ∈ l')
    (h2 : ∀ e, e.eIndex ≤ x → e ∈ l' → e ∈ l) :
    removeAfterIndex l' x = removeAfterIndex l x := by
  refine sorted_mem_eq (removeAfterIndex_sorted hs')
    (removeAfterIndex_sorted hs) ?_
  intro e
  constructor
  · intro he
    exact removeAfterIndex_le_In (removeAfterIndex_In_le hs' he)
      (h2 e (removeAfterIndex_In_le hs' he) (removeAfterIndex_in he))
  · intro he
    exact removeAfterIndex_le_In (removeAfterIndex_In_le hs he)
      (h1 e (removeAfterIndex_In_le hs he) (removeAfterIndex_in he))

omit O in
/-- `CommonTheorems.v:1538-1552` (`prefix_sorted`). -/
theorem prefix_sorted {l l' : List (entry (P := P))} (hs : sorted l)
    (hp : Prefix l' l) : sorted l' := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => trivial
    | cons b l₁ => exact absurd hp not_false
  | cons a l₀ ih =>
    cases l' with
    | nil => trivial
    | cons b l₁ =>
      obtain ⟨rfl, hp'⟩ := hp
      exact ⟨fun e' he' => hs.1 e' (Prefix_In hp' e' he'), ih hs.2 hp'⟩

omit O in
/-- `CommonTheorems.v:1663-1735` (`thing2`): a nonempty prefix of a
sorted, 0-contiguous log, itself contiguous down to `i`, splits the log
exactly at `i`. -/
theorem thing2 {l l' : List (entry (P := P))} {i : logIndex}
    (hne : l ≠ []) (hp : Prefix l l') (hs' : sorted l')
    (hc : contiguous_range_exact_lo l i)
    (hc' : contiguous_range_exact_lo l' 0) :
    l ++ removeAfterIndex l' i = l' := by
  induction l generalizing l' with
  | nil => exact absurd rfl hne
  | cons a l₀ ih =>
    cases l' with
    | nil => exact absurd hp not_false
    | cons b l₁ =>
      obtain ⟨rfl, hp'⟩ := hp
      show a :: (l₀ ++ removeAfterIndex (a :: l₁) i) = a :: l₁
      have hagt : i < a.eIndex := hc.2 a (List.mem_cons_self ..)
      rw [removeAfterIndex_cons_neg
        (fun hle => absurd hagt
          (Nat.not_lt.mpr (by simpa [Nat.ble_eq] using hle)))]
      cases l₀ with
      | nil =>
        -- singleton prefix: a's index is exactly i+1, so everything
        -- below survives removeAfterIndex untouched
        have hai : a.eIndex = i + 1 := contiguous_index_singleton hc
        have hall : ∀ e ∈ l₁, e.eIndex ≤ i := by
          intro e he
          have hlt : e.eIndex < a.eIndex := (hs'.1 e he).1
          rw [hai] at hlt
          exact Nat.le_of_lt_succ hlt
        rw [removeAfterIndex_eq hall]
        rfl
      | cons c l₂ =>
        have hcl : c :: l₂ ≠ [] := List.cons_ne_nil c l₂
        have hcc : contiguous_range_exact_lo (c :: l₂) i :=
          cons_contiguous_sorted (prefix_sorted hs' ⟨rfl, hp'⟩) hc
        have hc1' : contiguous_range_exact_lo l₁ 0 :=
          cons_contiguous_sorted hs' hc'
        rw [ih hcl hp' hs'.2 hcc hc1']

omit O in
/-- `CommonTheorems.v:1737-1757` (`thing`): a nonempty prefix of a
leader snapshot, contiguous down to a pivot shared (by index and term)
between a log and the snapshot, extends the log's cut to exactly the
snapshot. -/
theorem thing {es l l' : List (entry (P := P))} {e e' : entry (P := P)}
    (hs : sorted l) (hs' : sorted l')
    (hc' : contiguous_range_exact_lo l' 0) (hm : entries_match l l')
    (hne : es ≠ []) (hp : Prefix es l')
    (hces : contiguous_range_exact_lo es e.eIndex) (hel : e ∈ l)
    (hel' : e' ∈ l') (hidx : e.eIndex = e'.eIndex)
    (hterm : e.eTerm = e'.eTerm) :
    es ++ removeAfterIndex l e.eIndex = l' := by
  have hsame : removeAfterIndex l e.eIndex
      = removeAfterIndex l' e.eIndex := by
    refine (removeAfterIndex_same_sufficient hs hs' ?_ ?_).symm
    · intro e'' hle he''
      exact (hm e e' e'' hidx hterm hel hel' hle).mp he''
    · intro e'' hle he''
      exact (hm e e' e'' hidx hterm hel hel' hle).mpr he''
  rw [hsame]
  exact thing2 hne hp hs' hces hc'

omit O in
/-- `CommonTheorems.v:1880-1894` (`thing3`): a member of a sorted
append with positive indices that is bounded by the back block's max
lives in the back block. -/
theorem thing3 {l l' : List (entry (P := P))} {e : entry (P := P)}
    (hs : sorted (l ++ l'))
    (hpos : ∀ e' ∈ l ++ l', e'.eIndex > 0)
    (he : e ∈ l ++ l') (hle : e.eIndex ≤ maxIndex l') : e ∈ l' := by
  induction l with
  | nil => exact he
  | cons a l₀ ih =>
    rcases List.mem_cons.mp he with rfl | he'
    · exfalso
      cases l' with
      | nil =>
        replace hle : e.eIndex ≤ 0 := hle
        exact absurd (hpos e (List.mem_cons_self ..))
          (Nat.not_lt.mpr hle)
      | cons b l₁ =>
        have hgt : e.eIndex > b.eIndex :=
          (hs.1 b (List.mem_append.mpr (Or.inr (List.mem_cons_self ..)))).1
        replace hle : e.eIndex ≤ b.eIndex := hle
        exact absurd hgt (Nat.not_lt.mpr hle)
    · exact ih hs.2 (fun e' he'' => hpos e' (List.mem_cons_of_mem _ he'')) he'

omit O in
/-- `findGtIndex_nil` (helper for the commute lemma). -/
theorem findGtIndex_nil {l : List (entry (P := P))} {i : logIndex}
    (h : ∀ e ∈ l, ¬ e.eIndex > i) : findGtIndex l i = [] := by
  cases l with
  | nil => rfl
  | cons a as =>
    exact findGtIndex_cons_neg
      (fun hgt => h a (List.mem_cons_self ..)
        (by simpa [Nat.blt_eq] using hgt))

omit O in
/-- `CommonTheorems.v:1837-1850` (`findGtIndex_removeAfterIndex_commute`). -/
theorem findGtIndex_removeAfterIndex_commute {l : List (entry (P := P))}
    {i i' : logIndex} (hs : sorted l) :
    removeAfterIndex (findGtIndex l i) i' =
      findGtIndex (removeAfterIndex l i') i := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    by_cases hgt : (a.eIndex >? i) = true
    · rw [findGtIndex_cons_pos hgt]
      by_cases hle : (a.eIndex <=? i') = true
      · rw [removeAfterIndex_cons_pos hle, removeAfterIndex_cons_pos hle,
          findGtIndex_cons_pos hgt]
      · rw [removeAfterIndex_cons_neg hle, removeAfterIndex_cons_neg hle,
          ih hs.2]
    · rw [findGtIndex_cons_neg hgt]
      have hai : a.eIndex ≤ i :=
        Nat.not_lt.mp (fun hlt => hgt (by simpa [Nat.blt_eq] using hlt))
      by_cases hle : (a.eIndex <=? i') = true
      · rw [removeAfterIndex_cons_pos hle, findGtIndex_cons_neg hgt]
        rfl
      · rw [removeAfterIndex_cons_neg hle]
        show ([] : List (entry (P := P)))
          = findGtIndex (removeAfterIndex as i') i
        refine (findGtIndex_nil ?_).symm
        intro e he hgt'
        have hin : e ∈ as := removeAfterIndex_in he
        have h1 : e.eIndex < a.eIndex := (hs.1 e hin).1
        exact absurd (Nat.lt_trans hgt' h1) (Nat.not_lt.mpr hai)

omit O in
/-- `CommonTheorems.v:1852-1862` (`findGtIndex_app_1`). -/
theorem findGtIndex_app_1 {l l' : List (entry (P := P))} {i : logIndex}
    (h : maxIndex l' ≤ i) : findGtIndex (l ++ l') i = findGtIndex l i := by
  induction l with
  | nil =>
    show findGtIndex l' i = []
    cases l' with
    | nil => rfl
    | cons b l₁ =>
      replace h : b.eIndex ≤ i := h
      exact findGtIndex_cons_neg
        (fun hgt => absurd (by simpa [Nat.blt_eq] using hgt)
          (Nat.not_lt.mpr h))
  | cons a l₀ ih =>
    show findGtIndex (a :: (l₀ ++ l')) i = findGtIndex (a :: l₀) i
    by_cases hgt : (a.eIndex >? i) = true
    · rw [findGtIndex_cons_pos hgt, findGtIndex_cons_pos hgt, ih]
    · rw [findGtIndex_cons_neg hgt, findGtIndex_cons_neg hgt]

omit O in
/-- `CommonTheorems.v:1864-1878` (`findGtIndex_app_2`). -/
theorem findGtIndex_app_2 {l l' : List (entry (P := P))} {i : logIndex}
    (hs : sorted (l ++ l')) (hlt : i < maxIndex l') :
    findGtIndex (l ++ l') i = l ++ findGtIndex l' i := by
  induction l with
  | nil => rfl
  | cons a l₀ ih =>
    show findGtIndex (a :: (l₀ ++ l')) i = a :: (l₀ ++ findGtIndex l' i)
    have hgt : (a.eIndex >? i) = true := by
      cases hl' : l' with
      | nil =>
        rw [hl'] at hlt
        exact absurd hlt (Nat.not_lt.mpr (Nat.zero_le i))
      | cons b l₁ =>
        have hab : b.eIndex < a.eIndex := (hs.1 b (by
          rw [hl']
          exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..)))).1
        rw [hl'] at hlt
        replace hlt : i < b.eIndex := hlt
        simp only [Nat.blt_eq]
        exact Nat.lt_trans hlt hab
    rw [findGtIndex_cons_pos hgt, ih hs.2]

omit O in
/-- `CommonTheorems.v:1896-1904` (`findGtIndex_non_empty`). -/
theorem findGtIndex_non_empty {l : List (entry (P := P))} {i : logIndex}
    (h : i < maxIndex l) : findGtIndex l i ≠ [] := by
  cases l with
  | nil => exact absurd h (Nat.not_lt.mpr (Nat.zero_le i))
  | cons a as =>
    replace h : i < a.eIndex := h
    rw [findGtIndex_cons_pos (by simpa [Nat.blt_eq] using h)]
    exact List.cons_ne_nil _ _

omit O in
/-- `CommonTheorems.v:1934-1943` (`removeAfterIndex_in_app`). -/
theorem removeAfterIndex_in_app {l l' : List (entry (P := P))}
    {e : entry (P := P)} (he : e ∈ l) :
    removeAfterIndex (l ++ l') e.eIndex =
      removeAfterIndex l e.eIndex ++ l' := by
  induction l with
  | nil => exact nomatch he
  | cons a l₀ ih =>
    show removeAfterIndex (a :: (l₀ ++ l')) e.eIndex
      = removeAfterIndex (a :: l₀) e.eIndex ++ l'
    by_cases hle : (a.eIndex <=? e.eIndex) = true
    · rw [removeAfterIndex_cons_pos hle, removeAfterIndex_cons_pos hle]
      rfl
    · rcases List.mem_cons.mp he with rfl | he'
      · exact absurd (by simp [Nat.ble_eq]) hle
      · rw [removeAfterIndex_cons_neg hle, removeAfterIndex_cons_neg hle,
          ih he']

omit O in
/-- `CommonTheorems.v:1945-1955` (`removeAfterIndex_in_app_l'`). -/
theorem removeAfterIndex_in_app_l' {l l' : List (entry (P := P))}
    {e : entry (P := P)} (h : ∀ e' ∈ l, e'.eIndex > e.eIndex)
    (_he : e ∈ l') :
    removeAfterIndex (l ++ l') e.eIndex = removeAfterIndex l' e.eIndex := by
  induction l with
  | nil => rfl
  | cons a l₀ ih =>
    show removeAfterIndex (a :: (l₀ ++ l')) e.eIndex
      = removeAfterIndex l' e.eIndex
    by_cases hle : (a.eIndex <=? e.eIndex) = true
    · exact absurd (h a (List.mem_cons_self ..))
        (Nat.not_lt.mpr (by simpa [Nat.ble_eq] using hle))
    · rw [removeAfterIndex_cons_neg hle]
      exact ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))

omit O in
/-- `CommonTheorems.v:1957-1964` (`removeAfterIndex_maxIndex_sorted`). -/
theorem removeAfterIndex_maxIndex_sorted {l : List (entry (P := P))}
    (_hs : sorted l) : l = removeAfterIndex l (maxIndex l) := by
  cases l with
  | nil => rfl
  | cons a as =>
    exact (removeAfterIndex_cons_pos (by simp [maxIndex, Nat.ble_eq])).symm

omit O in
/-- `CommonTheorems.v:220-231` (`removeAfterIndex_le`). -/
theorem removeAfterIndex_le {l : List (entry (P := P))} {i j : logIndex}
    (h : i ≤ j) :
    removeAfterIndex l i = removeAfterIndex (removeAfterIndex l j) i := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    by_cases hlej : (a.eIndex <=? j) = true
    · rw [removeAfterIndex_cons_pos hlej]
    · have hlei : ¬ (a.eIndex <=? i) = true := fun hi =>
        hlej (by
          simp only [Nat.ble_eq] at hi ⊢
          exact Nat.le_trans hi h)
      rw [removeAfterIndex_cons_neg hlej, removeAfterIndex_cons_neg hlei,
        ih]

/-! ## logs_leaderLogs (`LogsLeaderLogsInterface.v:9-30`) -/

/-- `LogsLeaderLogsInterface.v:9-16` (`logs_leaderLogs`): every host log
entry sits atop a leaderLog snapshot at its own term. -/
def logs_leaderLogs (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (e : entry (P := P)),
    e ∈ (net.nwState h).2.log →
    ∃ (leader : name (P := P)) (ll es : List (entry (P := P))),
      (e.eTerm, ll) ∈ (net.nwState leader).1.leaderLogs ∧
      removeAfterIndex (net.nwState h).2.log e.eIndex = es ++ ll ∧
      (∀ e' ∈ es, e'.eTerm = e.eTerm)

/-- `LogsLeaderLogsInterface.v:18-30` (`logs_leaderLogs_nw`): the
in-flight strengthening the induction carries. -/
def logs_leaderLogs_nw (net : RefinedNet) : Prop :=
  ∀ (p : RefinedPacket) (t : term) (n : name (P := P)) (pli : logIndex)
    (plt : term) (es : List (entry (P := P))) (ci : logIndex)
    (e : entry (P := P)),
    p ∈ net.nwPackets → p.pBody = .AppendEntries t n pli plt es ci →
    e ∈ es →
    ∃ (leader : name (P := P)) (ll es' ll' : List (entry (P := P))),
      (e.eTerm, ll) ∈ (net.nwState leader).1.leaderLogs ∧
      Prefix ll' ll ∧
      removeAfterIndex es e.eIndex = es' ++ ll' ∧
      (∀ e' ∈ es', e'.eTerm = e.eTerm) ∧
      ((plt = e.eTerm ∧ pli > maxIndex ll) ∨
       (∃ e2, e2 ∈ ll ∧ e2.eIndex = pli ∧ e2.eTerm = plt ∧
         (ll' ≠ [] ∨ pli = maxIndex ll)) ∨
       (plt = 0 ∧ pli = 0 ∧ ll' = ll))

/-- `LogsLeaderLogsProof.v:59-61` (`logs_leaderLogs_inductive`). -/
def logs_leaderLogs_inductive (net : RefinedNet) : Prop :=
  logs_leaderLogs net ∧ logs_leaderLogs_nw net

/-- Host-side transport: leaderLogs grow at the updated node and its
log is unchanged. -/
theorem logs_leaderLogs_of_update {net net' : RefinedNet}
    {u : name (P := P)} {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hP : logs_leaderLogs net)
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hgrow : ∀ (t : term) (ll : List (entry (P := P))),
      (t, ll) ∈ (net.nwState u).1.leaderLogs → (t, ll) ∈ gd.leaderLogs)
    (hlog : d.log = (net.nwState u).2.log) :
    logs_leaderLogs net' := by
  intro h e he
  have hlog' : (net'.nwState h).2.log = (net.nwState h).2.log := by
    rw [hst h]
    by_cases heq : h = u
    · subst heq
      rw [update_same]
      exact hlog
    · rw [update_neq _ _ heq]
  rw [hlog'] at he ⊢
  obtain ⟨leader, ll, es, hmem, heq2, hterm⟩ := hP h e he
  refine ⟨leader, ll, es, ?_, heq2, hterm⟩
  rw [hst leader]
  by_cases heql : leader = u
  · subst heql
    rw [update_same]
    exact hgrow _ _ hmem
  · rw [update_neq _ _ heql]
    exact hmem

/-- nw-side witness transport (the witness mentions the network only
through the leaderLog membership). -/
theorem lll_nw_transport {net net' : RefinedNet} {u : name (P := P)}
    {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hgrow : ∀ (t : term) (ll : List (entry (P := P))),
      (t, ll) ∈ (net.nwState u).1.leaderLogs → (t, ll) ∈ gd.leaderLogs)
    {pli : logIndex} {plt : term} {es : List (entry (P := P))}
    {e : entry (P := P)}
    (hw : ∃ (leader : name (P := P)) (ll es' ll' : List (entry (P := P))),
      (e.eTerm, ll) ∈ (net.nwState leader).1.leaderLogs ∧
      Prefix ll' ll ∧
      removeAfterIndex es e.eIndex = es' ++ ll' ∧
      (∀ e' ∈ es', e'.eTerm = e.eTerm) ∧
      ((plt = e.eTerm ∧ pli > maxIndex ll) ∨
       (∃ e2, e2 ∈ ll ∧ e2.eIndex = pli ∧ e2.eTerm = plt ∧
         (ll' ≠ [] ∨ pli = maxIndex ll)) ∨
       (plt = 0 ∧ pli = 0 ∧ ll' = ll))) :
    ∃ (leader : name (P := P)) (ll es' ll' : List (entry (P := P))),
      (e.eTerm, ll) ∈ (net'.nwState leader).1.leaderLogs ∧
      Prefix ll' ll ∧
      removeAfterIndex es e.eIndex = es' ++ ll' ∧
      (∀ e' ∈ es', e'.eTerm = e.eTerm) ∧
      ((plt = e.eTerm ∧ pli > maxIndex ll) ∨
       (∃ e2, e2 ∈ ll ∧ e2.eIndex = pli ∧ e2.eTerm = plt ∧
         (ll' ≠ [] ∨ pli = maxIndex ll)) ∨
       (plt = 0 ∧ pli = 0 ∧ ll' = ll)) := by
  obtain ⟨leader, ll, es', ll', h1, h2, h3, h4, h5⟩ := hw
  refine ⟨leader, ll, es', ll', ?_, h2, h3, h4, h5⟩
  rw [hst leader]
  by_cases heq : leader = u
  · subst heq
    rw [update_same]
    exact hgrow _ _ h1
  · rw [update_neq _ _ heq]
    exact h1

/-- `LogsLeaderLogsProof.v:479-520`
(`logs_leaderLogs_inductive_clientRequest`): a leader's fresh entry
stacks on the split `leaders_have_leaderLogs_strong` provides; old
entries sit below the fresh maxIndex+1 head. -/
theorem logs_leaderLogs_inductive_clientRequest :
    refined_raft_net_invariant_client_request (P := P)
      logs_leaderLogs_inductive := by
  intro h net st' ps' gd out d l client id c hcr hgd hP hreach hst hps
  obtain ⟨hPh, hPn⟩ := hP
  obtain ⟨-, -, -, -, hl⟩ := handleClientRequest_spec h (net.nwState h).2
    client id c hcr
  have hgrow : ∀ (t2 : term) (ll : List (entry (P := P))),
      (t2, ll) ∈ (net.nwState h).1.leaderLogs → (t2, ll) ∈ gd.leaderLogs := by
    intro t2 ll hin
    subst hgd
    rw [(update_elections_data_client_request_ghost h (net.nwState h)
      client id c).2.2.2]
    exact hin
  have hreloc : ∀ (t2 : term) (ll : List (entry (P := P)))
      (leader : name (P := P)),
      (t2, ll) ∈ (net.nwState leader).1.leaderLogs →
      (t2, ll) ∈ (st' leader).1.leaderLogs := by
    intro t2 ll leader hin
    rw [hst leader]
    by_cases heq : leader = h
    · subst heq
      rw [update_same]
      exact hgrow _ _ hin
    · rw [update_neq _ _ heq]
      exact hin
  constructor
  · -- HOST
    rcases handleClientRequest_log_full h (net.nwState h).2 client id c hcr
      with ⟨hty, hlogd⟩ | ⟨-, heqd⟩
    · -- leader: log = enew :: L
      intro h0 e he
      replace he : e ∈ (st' h0).2.log := he
      by_cases heq0 : h0 = h
      case neg =>
        have hlog0 : (st' h0).2.log = (net.nwState h0).2.log := by
          rw [hst h0, update_neq _ _ heq0]
        rw [hlog0] at he
        obtain ⟨leader, ll, es2, hmem, hrm, hterm⟩ := hPh h0 e he
        refine ⟨leader, ll, es2, hreloc _ _ _ hmem, ?_, hterm⟩
        show removeAfterIndex (st' h0).2.log e.eIndex = es2 ++ ll
        rw [hlog0]
        exact hrm
      case pos =>
        subst heq0
        have hdst : (st' h0).2 = d := by
          rw [hst h0, update_same]
        rw [hdst] at he
        show ∃ (leader : name (P := P)) (ll es2 : List (entry (P := P))),
          (e.eTerm, ll) ∈ (st' leader).1.leaderLogs ∧
          removeAfterIndex (st' h0).2.log e.eIndex = es2 ++ ll ∧
          (∀ e' ∈ es2, e'.eTerm = e.eTerm)
        rw [hdst, hlogd]
        rw [hlogd] at he
        generalize henew : (⟨h0, client, id,
          maxIndex (net.nwState h0).2.log + 1,
          (net.nwState h0).2.currentTerm, c⟩ : entry (P := P)) = enew
        rw [henew] at he
        have hterm_enew : enew.eTerm = (net.nwState h0).2.currentTerm := by
          rw [← henew]
        have hidx_enew :
            enew.eIndex = maxIndex (net.nwState h0).2.log + 1 := by
          rw [← henew]
        have hsortL : sorted (net.nwState h0).2.log :=
          sorted_host_lifted net hreach h0
        rcases List.mem_cons.mp he with rfl | heL
        · -- the fresh entry rides the strong leader split
          obtain ⟨ll, es0, hmem, hsplit, hterm0⟩ :=
            leaders_have_leaderLogs_strong_invariant net hreach h0 hty
          refine ⟨h0, ll, e :: es0, ?_, ?_, ?_⟩
          · rw [hterm_enew]
            exact hreloc _ _ _ hmem
          · rw [removeAfterIndex_cons_pos (by simp [Nat.ble_eq]), hsplit]
            rfl
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx0
            · rfl
            · rw [hterm_enew]
              exact hterm0 x hx0
        · -- an old entry: the fresh head sits above its index
          obtain ⟨leader, ll, es2, hmem, hrm, hterm⟩ := hPh h0 e heL
          refine ⟨leader, ll, es2, hreloc _ _ _ hmem, ?_, hterm⟩
          have hne : ¬ ((enew.eIndex <=? e.eIndex) = true) := by
            intro hle
            simp only [Nat.ble_eq] at hle
            rw [hidx_enew] at hle
            exact absurd (maxIndex_is_max hsortL heL)
              (Nat.not_le.mpr (Nat.lt_of_succ_le hle))
          rw [removeAfterIndex_cons_neg hne]
          exact hrm
    · -- not leader: state unchanged
      refine logs_leaderLogs_of_update hPh hst hgrow ?_
      rw [heqd]
  · -- NW: no packets sent
    intro p0 t0 n1 pli2 plt2 es2 ci2 e0 hp0 hbody0 he0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · exact h1
      · rw [hl] at h1
        simp [send_packets] at h1
    exact lll_nw_transport hst hgrow
      (hPn p0 t0 n1 pli2 plt2 es2 ci2 e0 hold hbody0 he0)

/-- `LogsLeaderLogsProof.v:204-406`
(`logs_leaderLogs_inductive_appendEntries`) — the splice case: a new
entry's witness comes from the nw invariant, glued to the host witness
at the pivot via `thing`/`removeAfterIndex_same_sufficient`; an old
entry's witness survives below the prevLog cut. The upstream
`weak_sanity`/`logs_leaderLogs_nw_weaken` detour is not needed: with
the strong nw disjunction, `pli = 0` forces its third disjunct
outright (disjunct 1 dies on `0 > maxIndex`, disjunct 2 on
`leaderLogs_contiguous`). -/
theorem logs_leaderLogs_inductive_appendEntries :
    refined_raft_net_invariant_append_entries (P := P)
      logs_leaderLogs_inductive := by
  intro xs p ys net st' ps' gd d m t n0 pli plt es ci hae hgd hbody hP
    hreach hpkts hst hps
  obtain ⟨hPh, hPn⟩ := hP
  have hpin : p ∈ net.nwPackets := by
    rw [hpkts]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hgrow : ∀ (t2 : term) (ll : List (entry (P := P))),
      (t2, ll) ∈ (net.nwState p.pDst).1.leaderLogs →
      (t2, ll) ∈ gd.leaderLogs := by
    intro t2 ll hin
    subst hgd
    rw [(update_elections_data_appendEntries_ghost p.pDst
      (net.nwState p.pDst) t n0 pli plt es ci).2.2.2]
    exact hin
  have hreloc : ∀ (t2 : term) (ll : List (entry (P := P)))
      (leader : name (P := P)),
      (t2, ll) ∈ (net.nwState leader).1.leaderLogs →
      (t2, ll) ∈ (st' leader).1.leaderLogs := by
    intro t2 ll leader hin
    rw [hst leader]
    by_cases heq : leader = p.pDst
    · subst heq
      rw [update_same]
      exact hgrow _ _ hin
    · rw [update_neq _ _ heq]
      exact hin
  have hsortL : sorted (net.nwState p.pDst).2.log :=
    sorted_host_lifted net hreach p.pDst
  have hsortes : sorted es :=
    entries_sorted_nw_invariant net hreach p t n0 pli plt es ci hpin hbody
  have hcontig_es : contiguous_range_exact_lo es pli :=
    entries_contiguous_nw_invariant net hreach p t n0 pli plt es ci hpin
      hbody
  constructor
  · -- HOST
    intro h0 e he
    replace he : e ∈ (st' h0).2.log := he
    by_cases heq0 : h0 = p.pDst
    case neg =>
      have hlog0 : (st' h0).2.log = (net.nwState h0).2.log := by
        rw [hst h0, update_neq _ _ heq0]
      rw [hlog0] at he
      obtain ⟨leader, ll, es2, hmem, hrm, hterm⟩ := hPh h0 e he
      refine ⟨leader, ll, es2, hreloc _ _ _ hmem, ?_, hterm⟩
      show removeAfterIndex (st' h0).2.log e.eIndex = es2 ++ ll
      rw [hlog0]
      exact hrm
    case pos =>
      subst heq0
      have hdst : (st' p.pDst).2 = d := by
        rw [hst p.pDst, update_same]
      rw [hdst] at he
      show ∃ (leader : name (P := P)) (ll es2 : List (entry (P := P))),
        (e.eTerm, ll) ∈ (st' leader).1.leaderLogs ∧
        removeAfterIndex (st' p.pDst).2.log e.eIndex = es2 ++ ll ∧
        (∀ e' ∈ es2, e'.eTerm = e.eTerm)
      rw [hdst]
      rcases handleAppendEntries_log_cases p.pDst (net.nwState p.pDst).2 t n0
        pli plt es ci hae with hsame | ⟨hpli0, hlog⟩ |
        ⟨e0, he0L, he0idx, he0term, hlog⟩
      · -- log unchanged
        rw [hsame] at he ⊢
        obtain ⟨leader, ll, es2, hmem, hrm, hterm⟩ := hPh p.pDst e he
        exact ⟨leader, ll, es2, hreloc _ _ _ hmem, hrm, hterm⟩
      · -- wholesale (pli = 0): the nw disjunction collapses to ll' = ll
        rw [hlog] at he ⊢
        obtain ⟨leader, ll, es', ll', hmem, hpref, hrm, hterm, hdisj⟩ :=
          hPn p t n0 pli plt es ci e hpin hbody he
        rcases hdisj with ⟨-, hgt⟩ | ⟨e2, he2ll, he2idx, -, -⟩ | ⟨-, -, hll⟩
        · rw [hpli0] at hgt
          exact absurd hgt (Nat.not_lt.mpr (Nat.zero_le _))
        · exfalso
          have hpos := (leaderLogs_contiguous_invariant net hreach leader
            e.eTerm ll hmem).2 e2 he2ll
          rw [he2idx, hpli0] at hpos
          exact Nat.lt_irrefl 0 hpos
        · rw [hll] at hrm
          exact ⟨leader, ll, es', hreloc _ _ _ hmem, hrm, hterm⟩
      · -- splice at the pivot e0
        rw [hlog] at he ⊢
        rcases List.mem_append.mp he with hees | heold
        · -- NEW entry
          obtain ⟨leader, ll, es', ll', hmem, hpref, hrm, hterm, hdisj⟩ :=
            hPn p t n0 pli plt es ci e hpin hbody hees
          have hsortrm : sorted (removeAfterIndex es e.eIndex) :=
            removeAfterIndex_sorted hsortes
          have hcontigrm : contiguous_range_exact_lo
              (removeAfterIndex es e.eIndex) pli :=
            removeAfterIndex_contiguous hsortes hcontig_es
          have hsortll : sorted ll :=
            leaderLogs_sorted_invariant net hreach leader e.eTerm ll hmem
          have hcontig_ll' : contiguous_range_exact_lo ll' pli := by
            rw [hrm] at hsortrm hcontigrm
            exact contiguous_app hsortrm hcontigrm
          rcases hdisj with ⟨hplt, hpligt⟩ |
            ⟨e2, he2ll, he2idx, he2term, hsane⟩ | ⟨-, hpli0, -⟩
          · -- prevLog past the snapshot: cut is all fresh; glue to the
            -- pivot's host witness
            have hll'nil : ll' = [] := by
              cases hll' : ll' with
              | nil => rfl
              | cons x xs =>
                exfalso
                have hx : x ∈ ll' := by
                  rw [hll']
                  exact List.mem_cons_self ..
                have h1 : pli < x.eIndex := hcontig_ll'.2 x hx
                have h2 : x.eIndex ≤ maxIndex ll :=
                  maxIndex_is_max hsortll (Prefix_In hpref x hx)
                exact absurd (Nat.lt_of_lt_of_le h1
                  (Nat.le_trans h2 (Nat.le_of_lt hpligt)))
                  (Nat.lt_irrefl pli)
            rw [hll'nil, List.append_nil] at hrm
            obtain ⟨leader2, ll2, es2, hmem2, hrm2, hterm2⟩ :=
              hPh p.pDst e0 he0L
            have hterm_eq : e0.eTerm = e.eTerm := by
              rw [he0term, hplt]
            rw [hterm_eq] at hmem2
            refine ⟨leader2, ll2, removeAfterIndex es e.eIndex ++ es2,
              hreloc _ _ _ hmem2, ?_, ?_⟩
            · rw [removeAfterIndex_in_app hees, ← he0idx, hrm2]
              exact (List.append_assoc _ _ _).symm
            · intro x hx
              rcases List.mem_append.mp hx with hx1 | hx2
              · exact hterm x (hrm ▸ hx1)
              · rw [hterm2 x hx2]
                exact hterm_eq
          · -- prevLog inside the snapshot
            have hmatch : entries_match (net.nwState p.pDst).2.log ll :=
              leaderLogs_entries_match_invariant net hreach p.pDst leader
                e.eTerm ll hmem
            have hcontigll : contiguous_range_exact_lo ll 0 :=
              leaderLogs_contiguous_invariant net hreach leader e.eTerm ll
                hmem
            have hidx02 : e0.eIndex = e2.eIndex := by
              rw [he0idx, he2idx]
            have hterm02 : e0.eTerm = e2.eTerm := by
              rw [he0term, he2term]
            rcases hsane with hll'ne | hplimax
            · -- shared entry: `thing` extends the cut to the snapshot
              have hthing : ll' ++ removeAfterIndex (net.nwState p.pDst).2.log
                  e0.eIndex = ll := by
                refine thing hsortL hsortll hcontigll hmatch hll'ne hpref
                  ?_ he0L he2ll hidx02 hterm02
                rw [he0idx]
                exact hcontig_ll'
              refine ⟨leader, ll, es', hreloc _ _ _ hmem, ?_, hterm⟩
              rw [removeAfterIndex_in_app hees, hrm, List.append_assoc,
                ← he0idx, hthing]
            · -- prevLog at the snapshot's max: the cut below the pivot
              -- IS the snapshot
              have hll'nil : ll' = [] := by
                cases hll' : ll' with
                | nil => rfl
                | cons x xs =>
                  exfalso
                  have hx : x ∈ ll' := by
                    rw [hll']
                    exact List.mem_cons_self ..
                  have h1 : pli < x.eIndex := hcontig_ll'.2 x hx
                  have h2 : x.eIndex ≤ maxIndex ll :=
                    maxIndex_is_max hsortll (Prefix_In hpref x hx)
                  rw [hplimax] at h1
                  exact absurd h1 (Nat.not_lt.mpr h2)
              rw [hll'nil, List.append_nil] at hrm
              have hRll : removeAfterIndex (net.nwState p.pDst).2.log pli
                  = ll := by
                have h1 : removeAfterIndex ll pli
                    = removeAfterIndex (net.nwState p.pDst).2.log pli := by
                  refine removeAfterIndex_same_sufficient hsortL hsortll
                    ?_ ?_
                  · intro x hle hx
                    exact (hmatch e0 e2 x hidx02 hterm02 he0L he2ll
                      (by rw [he0idx]; exact hle)).mp hx
                  · intro x hle hx
                    exact (hmatch e0 e2 x hidx02 hterm02 he0L he2ll
                      (by rw [he0idx]; exact hle)).mpr hx
                rw [← h1, hplimax,
                  ← removeAfterIndex_maxIndex_sorted hsortll]
              refine ⟨leader, ll, es', hreloc _ _ _ hmem, ?_, hterm⟩
              rw [removeAfterIndex_in_app hees, hrm, hRll]
          · -- pli = 0 with a real pivot in the log: impossible
            exfalso
            have hpos := entries_gt_0_invariant net hreach p.pDst e0 he0L
            rw [he0idx, hpli0] at hpos
            exact Nat.lt_irrefl 0 hpos
        · -- OLD entry: it survives below the cut
          have heL : e ∈ (net.nwState p.pDst).2.log := removeAfterIndex_in heold
          have hele : e.eIndex ≤ pli := removeAfterIndex_In_le hsortL heold
          obtain ⟨leader, ll, es2, hmem, hrm2, hterm2⟩ := hPh p.pDst e heL
          refine ⟨leader, ll, es2, hreloc _ _ _ hmem, ?_, hterm2⟩
          have hgtes : ∀ e' ∈ es, e'.eIndex > e.eIndex := fun e' he' =>
            Nat.lt_of_le_of_lt hele (hcontig_es.2 e' he')
          rw [removeAfterIndex_in_app_l' hgtes heold,
            ← removeAfterIndex_le hele]
          exact hrm2
  · -- NW
    intro p0 t0 n1 pli2 plt2 es2 ci2 e0 hp0 hbody0 he0
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with h1 | h1
    · have hold : p0 ∈ net.nwPackets := by
        rw [hpkts]
        exact mem_of_mem_remove_middle h1
      exact lll_nw_transport hst hgrow
        (hPn p0 t0 n1 pli2 plt2 es2 ci2 e0 hold hbody0 he0)
    · exfalso
      obtain ⟨-, -, -, t', es', r', hmshape⟩ :=
        handleAppendEntries_spec p.pDst (net.nwState p.pDst).2 t n0 pli plt
          es ci hae
      rw [h1] at hbody0
      replace hbody0 : m = msg.AppendEntries t0 n1 pli2 plt2 es2 ci2 :=
        hbody0
      rw [hmshape] at hbody0
      exact nomatch hbody0

/-- `LogsLeaderLogsProof.v:607-756`
(`logs_leaderLogs_inductive_doLeader`) — the packet-creation case:
a replica message's entries are `findGtIndex log pli`, classified by
the trichotomy of `pli` against the witness snapshot's max. -/
theorem logs_leaderLogs_inductive_doLeader :
    refined_raft_net_invariant_do_leader (P := P)
      logs_leaderLogs_inductive := by
  intro net st' ps' gd d h os d' ms hdl hP hreach hstate hst hps
  obtain ⟨hPh, hPn⟩ := hP
  obtain ⟨-, -, -, -, hdlog, -⟩ := doLeader_spec d h hdl
  have hgrow : ∀ (t2 : term) (ll : List (entry (P := P))),
      (t2, ll) ∈ (net.nwState h).1.leaderLogs → (t2, ll) ∈ gd.leaderLogs := by
    intro t2 ll hin
    rw [hstate] at hin
    exact hin
  have hreloc : ∀ (t2 : term) (ll : List (entry (P := P)))
      (leader : name (P := P)),
      (t2, ll) ∈ (net.nwState leader).1.leaderLogs →
      (t2, ll) ∈ (st' leader).1.leaderLogs := by
    intro t2 ll leader hin
    rw [hst leader]
    by_cases heq : leader = h
    · subst heq
      rw [update_same]
      exact hgrow _ _ hin
    · rw [update_neq _ _ heq]
      exact hin
  constructor
  · refine logs_leaderLogs_of_update hPh hst hgrow ?_
    rw [hdlog, hstate]
  · intro p0 t0 n1 pli2 plt2 es2 ci2 e0 hp0 hbody0 he0
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · exact lll_nw_transport hst hgrow
        (hPn p0 t0 n1 pli2 plt2 es2 ci2 e0 hold hbody0 he0)
    · obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hnew
      have htype : d.type = .Leader := doLeader_messages_leader d h hdl hm0
      obtain ⟨host, hq2⟩ := doLeader_messages_nextIndex d h hdl m0 hm0
      replace hbody0 : m0.2 = msg.AppendEntries t0 n1 pli2 plt2 es2 ci2 :=
        hbody0
      rw [hq2] at hbody0
      injection hbody0 with f1 f2 f3 f4 f5 f6
      subst f1 f2 f3 f5 f6
      obtain ⟨he0d, he0gt⟩ := findGtIndex_necessary he0
      have hsortd : sorted d.log := by
        have hsl := sorted_host_lifted net hreach h
        rw [hstate] at hsl
        exact hsl
      have hgt0 : ∀ x ∈ d.log, x.eIndex > 0 := by
        intro x hx
        refine entries_gt_0_invariant net hreach h x ?_
        rw [hstate]
        exact hx
      have hPh' : ∀ x, x ∈ d.log →
          ∃ (leader : name (P := P)) (ll es3 : List (entry (P := P))),
            (x.eTerm, ll) ∈ (net.nwState leader).1.leaderLogs ∧
            removeAfterIndex d.log x.eIndex = es3 ++ ll ∧
            (∀ e' ∈ es3, e'.eTerm = x.eTerm) := by
        intro x hx
        have hx' : x ∈ (net.nwState h).2.log := by
          rw [hstate]
          exact hx
        obtain ⟨leader, ll, es3, hmem, hrm, hterm⟩ := hPh h x hx'
        rw [hstate] at hrm
        exact ⟨leader, ll, es3, hmem, hrm, hterm⟩
      rcases hfaeq : findAtIndex d.log (Nat.pred (getNextIndex d host))
        with _ | e1
      · rw [hfaeq] at f4
        simp only [] at f4
        by_cases hz : Nat.pred (getNextIndex d host) = 0
        · -- origin packet: the whole log rides the host witness
          obtain ⟨leader, ll, es3, hmem, hrm, hterm⟩ := hPh' e0 he0d
          refine ⟨leader, ll, es3, ll, hreloc _ _ _ hmem, Prefix_refl ll,
            ?_, hterm, Or.inr (Or.inr ⟨f4.symm, hz, rfl⟩)⟩
          rw [hz, sorted_findGtIndex_0 hgt0 hsortd]
          exact hrm
        · exfalso
          have hty_net : (net.nwState h).2.type = .Leader := by
            rw [hstate]
            exact htype
          obtain ⟨e, hfae⟩ := nextIndex_sanity net hreach h host hty_net
            (by rw [hstate]; exact hz)
          rw [hstate] at hfae
          replace hfae :
              findAtIndex d.log (Nat.pred (getNextIndex d host)) = some e :=
            hfae
          rw [hfaeq] at hfae
          exact nomatch hfae
      · rw [hfaeq] at f4
        simp only [] at f4
        obtain ⟨he1d, he1idx⟩ := findAtIndex_elim hfaeq
        obtain ⟨leader, ll, es3, hmem, hrm, hterm⟩ := hPh' e0 he0d
        have hsortll : sorted ll :=
          leaderLogs_sorted_invariant net hreach leader e0.eTerm ll hmem
        have hsortrm : sorted (es3 ++ ll) := by
          rw [← hrm]
          exact removeAfterIndex_sorted hsortd
        have hposrm : ∀ x ∈ es3 ++ ll, x.eIndex > 0 := by
          intro x hx
          rw [← hrm] at hx
          exact hgt0 x (removeAfterIndex_in hx)
        have he1cut : e1 ∈ es3 ++ ll := by
          rw [← hrm]
          exact removeAfterIndex_le_In
            (by rw [he1idx]; exact Nat.le_of_lt he0gt) he1d
        rcases Nat.lt_trichotomy (maxIndex ll)
          (Nat.pred (getNextIndex d host)) with hlt | heqm | hgtm
        · -- snapshot entirely below prevLog: the cut stays in es3
          refine ⟨leader, ll,
            findGtIndex es3 (Nat.pred (getNextIndex d host)), [],
            hreloc _ _ _ hmem, Prefix_nil ll, ?_, ?_, ?_⟩
          · rw [List.append_nil,
              findGtIndex_removeAfterIndex_commute hsortd, hrm,
              findGtIndex_app_1 (Nat.le_of_lt hlt)]
          · intro x hx
            exact hterm x (findGtIndex_in hx)
          · refine Or.inl ⟨?_, hlt⟩
            rw [← f4]
            rcases List.mem_append.mp he1cut with h1 | h1
            · exact hterm e1 h1
            · exfalso
              have hle := maxIndex_is_max hsortll h1
              rw [he1idx] at hle
              exact absurd hlt (Nat.not_lt.mpr hle)
        · -- prevLog exactly at the snapshot's max
          refine ⟨leader, ll,
            findGtIndex es3 (Nat.pred (getNextIndex d host)), [],
            hreloc _ _ _ hmem, Prefix_nil ll, ?_, ?_, ?_⟩
          · rw [List.append_nil,
              findGtIndex_removeAfterIndex_commute hsortd, hrm,
              findGtIndex_app_1 (Nat.le_of_eq heqm)]
          · intro x hx
            exact hterm x (findGtIndex_in hx)
          · refine Or.inr (Or.inl ⟨e1, ?_, he1idx, f4, Or.inr heqm.symm⟩)
            refine thing3 hsortrm hposrm he1cut ?_
            rw [he1idx]
            exact Nat.le_of_eq heqm.symm
        · -- prevLog inside the snapshot
          refine ⟨leader, ll, es3,
            findGtIndex ll (Nat.pred (getNextIndex d host)),
            hreloc _ _ _ hmem, findGtIndex_Prefix ll _, ?_, hterm, ?_⟩
          · rw [findGtIndex_removeAfterIndex_commute hsortd, hrm,
              findGtIndex_app_2 hsortrm hgtm]
          · refine Or.inr (Or.inl ⟨e1, ?_, he1idx, f4,
              Or.inl (findGtIndex_non_empty hgtm)⟩)
            refine thing3 hsortrm hposrm he1cut ?_
            rw [he1idx]
            exact Nat.le_of_lt hgtm

/-- `LogsLeaderLogsProof.v:807-825`
(`logs_leaderLogs_inductive_invariant`). -/
theorem logs_leaderLogs_inductive_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      logs_leaderLogs_inductive net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    constructor
    · intro h e he
      exact nomatch he
    · intro p0 t0 n1 pli2 plt2 es2 ci2 e0 hp0 _ _
      exact nomatch hp0
  · exact logs_leaderLogs_inductive_clientRequest
  · -- timeout
    intro net h st' ps' gd out d l hto hgd hP _hreach hst hps
    obtain ⟨hPh, hPn⟩ := hP
    obtain ⟨hlog, -, hmsgs⟩ := handleTimeout_spec h (net.nwState h).2 hto
    have hgrow : ∀ (t2 : term) (ll : List (entry (P := P))),
        (t2, ll) ∈ (net.nwState h).1.leaderLogs →
        (t2, ll) ∈ gd.leaderLogs := by
      intro t2 ll hin
      subst hgd
      rw [(update_elections_data_timeout_ghost h (net.nwState h)).1]
      exact hin
    constructor
    · exact logs_leaderLogs_of_update hPh hst hgrow hlog
    · intro p0 t0 n1 pli2 plt2 es2 ci2 e0 hp0 hbody0 he0
      replace hp0 : p0 ∈ ps' := hp0
      have hold : p0 ∈ net.nwPackets := by
        rcases hps p0 hp0 with h1 | h1
        · exact h1
        · exfalso
          obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp h1
          obtain ⟨t3, c3, l3, l4, hq2⟩ := hmsgs m0 hm0
          replace hbody0 :
              m0.2 = msg.AppendEntries t0 n1 pli2 plt2 es2 ci2 := hbody0
          rw [hq2] at hbody0
          exact nomatch hbody0
      exact lll_nw_transport hst hgrow
        (hPn p0 t0 n1 pli2 plt2 es2 ci2 e0 hold hbody0 he0)
  · exact logs_leaderLogs_inductive_appendEntries
  · -- append_entries_reply
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP _hreach
      hpkts hst hps
    obtain ⟨hPh, hPn⟩ := hP
    obtain ⟨-, -, hl⟩ := handleAppendEntriesReply_spec p.pDst
      (net.nwState p.pDst).2 p.pSrc t es res haer
    have hgrow : ∀ (t2 : term) (ll : List (entry (P := P))),
        (t2, ll) ∈ (net.nwState p.pDst).1.leaderLogs →
        (t2, ll) ∈ gd.leaderLogs := by
      intro t2 ll hin
      rw [hgd]
      exact hin
    constructor
    · refine logs_leaderLogs_of_update hPh hst hgrow ?_
      exact handleAppendEntriesReply_log p.pDst (net.nwState p.pDst).2
        p.pSrc t es res haer
    · intro p0 t0 n1 pli2 plt2 es2 ci2 e0 hp0 hbody0 he0
      replace hp0 : p0 ∈ ps' := hp0
      have hold : p0 ∈ net.nwPackets := by
        rcases hps p0 hp0 with h1 | h1
        · rw [hpkts]
          exact mem_of_mem_remove_middle h1
        · rw [hl] at h1
          simp [send_packets] at h1
      exact lll_nw_transport hst hgrow
        (hPn p0 t0 n1 pli2 plt2 es2 ci2 e0 hold hbody0 he0)
  · -- request_vote
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP
      _hreach hpkts hst hps
    obtain ⟨hPh, hPn⟩ := hP
    obtain ⟨t'', v'', hmshape⟩ := handleRequestVote_reply_shape p.pDst
      (net.nwState p.pDst).2 t p.pSrc lli llt hrv
    have hgrow : ∀ (t2 : term) (ll : List (entry (P := P))),
        (t2, ll) ∈ (net.nwState p.pDst).1.leaderLogs →
        (t2, ll) ∈ gd.leaderLogs := by
      intro t2 ll hin
      subst hgd
      rw [(update_elections_data_requestVote_cronies p.pDst p.pSrc t
        p.pSrc lli llt (net.nwState p.pDst)).2.1]
      exact hin
    constructor
    · refine logs_leaderLogs_of_update hPh hst hgrow ?_
      exact handleRequestVote_log p.pDst (net.nwState p.pDst).2 t p.pSrc
        lli llt hrv
    · intro p0 t0 n1 pli2 plt2 es2 ci2 e0 hp0 hbody0 he0
      replace hp0 : p0 ∈ ps' := hp0
      rcases hps p0 hp0 with h1 | h1
      · have hold : p0 ∈ net.nwPackets := by
          rw [hpkts]
          exact mem_of_mem_remove_middle h1
        exact lll_nw_transport hst hgrow
          (hPn p0 t0 n1 pli2 plt2 es2 ci2 e0 hold hbody0 he0)
      · exfalso
        rw [h1] at hbody0
        replace hbody0 : m = msg.AppendEntries t0 n1 pli2 plt2 es2 ci2 :=
          hbody0
        rw [hmshape] at hbody0
        exact nomatch hbody0
  · -- request_vote_reply
    intro xs p ys net st' ps' gd d t v hrvr hgd _hbody hP _hreach hpkts
      hst hps
    obtain ⟨hPh, hPn⟩ := hP
    have hgrow : ∀ (t2 : term) (ll : List (entry (P := P))),
        (t2, ll) ∈ (net.nwState p.pDst).1.leaderLogs →
        (t2, ll) ∈ gd.leaderLogs := by
      intro t2 ll hin
      subst hgd
      exact update_elections_data_requestVoteReply_leaderLogs_old p.pDst
        p.pSrc t v (net.nwState p.pDst) hin
    constructor
    · refine logs_leaderLogs_of_update hPh hst hgrow ?_
      rw [← hrvr]
      exact handleRequestVoteReply_log p.pDst (net.nwState p.pDst).2
        p.pSrc t v
    · intro p0 t0 n1 pli2 plt2 es2 ci2 e0 hp0 hbody0 he0
      replace hp0 : p0 ∈ ps' := hp0
      have hold : p0 ∈ net.nwPackets := by
        rw [hpkts]
        exact mem_of_mem_remove_middle (hps p0 hp0)
      exact lll_nw_transport hst hgrow
        (hPn p0 t0 n1 pli2 plt2 es2 ci2 e0 hold hbody0 he0)
  · exact logs_leaderLogs_inductive_doLeader
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps
    obtain ⟨hPh, hPn⟩ := hP
    obtain ⟨hlog, -, -, -, -, hms⟩ := doGenericServer_spec h d hgs
    have hgrow : ∀ (t2 : term) (ll : List (entry (P := P))),
        (t2, ll) ∈ (net.nwState h).1.leaderLogs →
        (t2, ll) ∈ gd.leaderLogs := by
      intro t2 ll hin
      rw [hstate] at hin
      exact hin
    constructor
    · refine logs_leaderLogs_of_update hPh hst hgrow ?_
      rw [hlog, hstate]
    · intro p0 t0 n1 pli2 plt2 es2 ci2 e0 hp0 hbody0 he0
      replace hp0 : p0 ∈ ps' := hp0
      have hold : p0 ∈ net.nwPackets := by
        rcases hps p0 hp0 with h1 | h1
        · exact h1
        · rw [hms] at h1
          simp [send_packets] at h1
      exact lll_nw_transport hst hgrow
        (hPn p0 t0 n1 pli2 plt2 es2 ci2 e0 hold hbody0 he0)
  · -- state_same_packet_subset
    intro net net' hstates hsub hP _hreach
    obtain ⟨hPh, hPn⟩ := hP
    constructor
    · intro h e he
      replace he : e ∈ (net'.nwState h).2.log := he
      rw [← hstates h] at he
      obtain ⟨leader, ll, es2, hmem, hrm, hterm⟩ := hPh h e he
      rw [hstates leader] at hmem
      refine ⟨leader, ll, es2, hmem, ?_, hterm⟩
      show removeAfterIndex (net'.nwState h).2.log e.eIndex = es2 ++ ll
      rw [← hstates h]
      exact hrm
    · intro p0 t0 n1 pli2 plt2 es2 ci2 e0 hp0 hbody0 he0
      obtain ⟨leader, ll, es', ll', h1, h2, h3, h4, h5⟩ :=
        hPn p0 t0 n1 pli2 plt2 es2 ci2 e0 (hsub p0 hp0) hbody0 he0
      rw [hstates leader] at h1
      exact ⟨leader, ll, es', ll', h1, h2, h3, h4, h5⟩
  · -- reboot
    intro net net' gd d h d' hrb hP _hreach hstate hst hpkts
    obtain ⟨hPh, hPn⟩ := hP
    have hgrow : ∀ (t2 : term) (ll : List (entry (P := P))),
        (t2, ll) ∈ (net.nwState h).1.leaderLogs →
        (t2, ll) ∈ gd.leaderLogs := by
      intro t2 ll hin
      rw [hstate] at hin
      exact hin
    constructor
    · refine logs_leaderLogs_of_update hPh hst hgrow ?_
      rw [← hrb, hstate]
      rfl
    · intro p0 t0 n1 pli2 plt2 es2 ci2 e0 hp0 hbody0 he0
      rw [← hpkts] at hp0
      exact lll_nw_transport hst hgrow
        (hPn p0 t0 n1 pli2 plt2 es2 ci2 e0 hp0 hbody0 he0)

/-- `LogsLeaderLogsProof.v:827-833` (`logs_leaderLogs_invariant`). -/
theorem logs_leaderLogs_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      logs_leaderLogs net :=
  fun net hreach => (logs_leaderLogs_inductive_invariant net hreach).1

/-- `LogsLeaderLogsProof.v:835-841` (`logs_leaderLogs_nw_invariant`). -/
theorem logs_leaderLogs_nw_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      logs_leaderLogs_nw net :=
  fun net hreach => (logs_leaderLogs_inductive_invariant net hreach).2

/-! ## leaderLogs_preserved (GAP-7b) -/

/-- `LeaderLogsPreservedInterface.v:9-15` (`leaderLogs_preserved`):
snapshots only ever extend — an entry of a later snapshot that shares a
snapshot with an entry `e` pulls every co-member of `e`'s snapshot in
with it. -/
def leaderLogs_preserved (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (ll : List (entry (P := P))) (t' : term)
    (h' : name (P := P)) (ll' : List (entry (P := P)))
    (e e' : entry (P := P)),
    (e.eTerm, ll) ∈ (net.nwState h).1.leaderLogs →
    (t', ll') ∈ (net.nwState h').1.leaderLogs →
    e ∈ ll' → e' ∈ ll → e' ∈ ll'

/-- Ghost-unchanged transport for `leaderLogs_preserved`. -/
theorem leaderLogs_preserved_of_update {net net' : RefinedNet}
    {u : name (P := P)} {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hP : leaderLogs_preserved net)
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hgd : gd.leaderLogs = (net.nwState u).1.leaderLogs) :
    leaderLogs_preserved net' := by
  intro h ll t' h' ll' e e' h1 h2 he he'
  have hred : ∀ (hh : name (P := P)) (tt : term)
      (lll : List (entry (P := P))),
      (tt, lll) ∈ (net'.nwState hh).1.leaderLogs →
      (tt, lll) ∈ (net.nwState hh).1.leaderLogs := by
    intro hh tt lll hin
    rw [hst hh] at hin
    by_cases heq : hh = u
    · subst heq
      rw [update_same] at hin
      replace hin : (tt, lll) ∈ gd.leaderLogs := hin
      rw [hgd] at hin
      exact hin
    · rw [update_neq _ _ heq] at hin
      exact hin
  exact hP h ll t' h' ll' e e' (hred h _ _ h1) (hred h' _ _ h2) he he'

/-- `LeaderLogsPreservedProof.v:98-257` (`leaderLogs_preserved_invariant`,
GAP-7b). Ten cases are pure ghost transport; the RVR case's fresh
snapshot resolves through `logs_leaderLogs` + `one_leaderLog_per_term`
(fresh on the `ll'` side) or dies on
`wonElection_candidateEntries_rvr` (fresh on the `ll` side — upstream's
same-host term-sanity bullet is subsumed by the candidate-entries
contradiction, which needs no host split; docstring-noted
simplification). -/
theorem leaderLogs_preserved_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      leaderLogs_preserved net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro h ll t' h' ll' e e' h1 _ _ _
    exact nomatch h1
  · -- client_request
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst hps
    refine leaderLogs_preserved_of_update hP hst ?_
    subst hgd
    exact (update_elections_data_client_request_ghost h (net.nwState h)
      client id c).2.2.2
  · -- timeout
    intro net h st' ps' gd out d l hto hgd hP _hreach hst hps
    refine leaderLogs_preserved_of_update hP hst ?_
    subst hgd
    exact (update_elections_data_timeout_ghost h (net.nwState h)).1
  · -- append_entries
    intro xs p ys net st' ps' gd d m t n0 pli plt es ci hae hgd _hbody hP
      _hreach hpkts hst hps
    refine leaderLogs_preserved_of_update hP hst ?_
    subst hgd
    exact (update_elections_data_appendEntries_ghost p.pDst
      (net.nwState p.pDst) t n0 pli plt es ci).2.2.2
  · -- append_entries_reply
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP _hreach
      hpkts hst hps
    refine leaderLogs_preserved_of_update hP hst ?_
    rw [hgd]
  · -- request_vote
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP
      _hreach hpkts hst hps
    refine leaderLogs_preserved_of_update hP hst ?_
    subst hgd
    exact (update_elections_data_requestVote_cronies p.pDst p.pSrc t
      p.pSrc lli llt (net.nwState p.pDst)).2.1
  · -- request_vote_reply: THE case
    intro xs p ys net st' ps' gd d t v hrvr hgd hbody hP hreach hpkts hst
      hps
    intro h ll t' h' ll' e e' h1 h2 he he'
    replace h1 : (e.eTerm, ll) ∈ (st' h).1.leaderLogs := h1
    replace h2 : (t', ll') ∈ (st' h').1.leaderLogs := h2
    have helim : ∀ (hh : name (P := P)) (tt : term)
        (lll : List (entry (P := P))),
        (tt, lll) ∈ (st' hh).1.leaderLogs →
        (tt, lll) ∈ (net.nwState hh).1.leaderLogs ∨
        (hh = p.pDst ∧
         (handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc t
           v).type = .Leader ∧
         (net.nwState p.pDst).2.type = .Candidate ∧
         tt = (handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc
           t v).currentTerm ∧
         lll = (handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc
           t v).log) := by
      intro hh tt lll hin
      rw [hst hh] at hin
      by_cases heq : hh = p.pDst
      · subst heq
        rw [update_same] at hin
        replace hin : (tt, lll) ∈ gd.leaderLogs := hin
        subst hgd
        rcases leaderLogs_update_elections_data_RVR hin with hold | hnew
        · exact Or.inl hold
        · exact Or.inr ⟨rfl, hnew⟩
      · rw [update_neq _ _ heq] at hin
        exact Or.inl hin
    have hq : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    rcases helim h _ _ h1 with h1old | ⟨heqh, hty1, hcand1, hterm1, hll1⟩
    · rcases helim h' _ _ h2 with h2old | ⟨heqh', hty2, hcand2, hterm2, hll2⟩
      · -- both old
        exact hP h ll t' h' ll' e e' h1old h2old he he'
      · -- ll' is the fresh snapshot: resolve e through logs_leaderLogs
        -- and identify ll with e's snapshot there via one_leaderLog
        subst heqh'
        have hnl : (net.nwState p.pDst).2.type ≠ .Leader := by
          rw [hcand2]
          exact fun hc => nomatch hc
        obtain ⟨-, -, -, -, -, hlogEq, -⟩ :=
          handleRequestVoteReply_leader_transition p.pDst
            (net.nwState p.pDst).2 p.pSrc t v rfl hnl hty2
        rw [hll2, hlogEq] at he ⊢
        obtain ⟨leader, llx, esx, hmemx, hrmx, -⟩ :=
          logs_leaderLogs_invariant net hreach p.pDst e he
        have hllx : ll = llx :=
          one_leaderLog_per_term_log_invariant net hreach h leader e.eTerm
            ll llx h1old hmemx
        rw [hllx] at he'
        have hin2 : e' ∈ esx ++ llx := List.mem_append.mpr (Or.inr he')
        rw [← hrmx] at hin2
        exact removeAfterIndex_in hin2
    · -- ll is the fresh snapshot
      subst heqh
      rcases helim h' _ _ h2 with h2old | ⟨-, -, -, -, hll2⟩
      · -- e bears the winner's current term inside an OLD snapshot —
        -- the candidate-entries contradiction
        exfalso
        have hnl : (net.nwState p.pDst).2.type ≠ .Leader := by
          rw [hcand1]
          exact fun hc => nomatch hc
        obtain ⟨-, hv, hctt, hctEq, -, -, hwon⟩ :=
          handleRequestVoteReply_leader_transition p.pDst
            (net.nwState p.pDst).2 p.pSrc t v rfl hnl hty1
        have hteq : e.eTerm = t := by
          rw [hterm1, hctEq, hctt]
        have hce : candidateEntries e net.nwState :=
          leaderLogs_candidateEntries_invariant net hreach h' e t' ll'
            h2old he
        have hbody' : p.pBody = .RequestVoteReply e.eTerm true := by
          rw [hbody, hteq, hv]
        have hct : (net.nwState p.pDst).2.currentTerm = e.eTerm := by
          rw [hteq]
          exact hctt
        exact wonElection_candidateEntries_rvr
          (votes_correct_invariant net hreach)
          (cronies_correct_invariant net hreach) hce hq hbody' hct hwon
          hcand1
      · -- both fresh: the two snapshots are the same log
        rw [hll2, ← hll1]
        exact he'
  · -- do_leader: ghost untouched
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst hps
    refine leaderLogs_preserved_of_update hP hst ?_
    rw [hstate]
  · -- do_generic_server: ghost untouched
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps
    refine leaderLogs_preserved_of_update hP hst ?_
    rw [hstate]
  · -- state_same_packet_subset
    intro net net' hstates hsub hP _hreach h ll t' h' ll' e e' h1 h2 he he'
    replace h1 : (e.eTerm, ll) ∈ (net'.nwState h).1.leaderLogs := h1
    replace h2 : (t', ll') ∈ (net'.nwState h').1.leaderLogs := h2
    rw [← hstates h] at h1
    rw [← hstates h'] at h2
    exact hP h ll t' h' ll' e e' h1 h2 he he'
  · -- reboot: ghost preserved
    intro net net' gd d h d' _hrb hP _hreach hstate hst hpkts
    refine leaderLogs_preserved_of_update hP hst ?_
    rw [hstate]

/-! ## allEntries_leaderLogs_term
(`AllEntriesLeaderLogsTermInterface.v:9-15`) -/

/-- `AllEntriesLeaderLogsTermInterface.v:9-15`
(`allEntries_leaderLogs_term`): every recorded (term, entry) pair is at
the entry's own term, or the entry sits in a leaderLog snapshot at the
recorded term. -/
def allEntries_leaderLogs_term (net : RefinedNet) : Prop :=
  ∀ (t : term) (e : entry (P := P)) (h : name (P := P)),
    (t, e) ∈ (net.nwState h).1.allEntries →
    t = e.eTerm ∨
    ∃ (ll : List (entry (P := P))) (leader : name (P := P)),
      (t, ll) ∈ (net.nwState leader).1.leaderLogs ∧ e ∈ ll

omit O in
/-- The client-request ghost record's pair carries the leader's current
term, which is also the fresh entry's term (sharpens the lane's
`update_elections_data_client_request_allEntries_term_cases` by the
head's term, read off `handleClientRequest_log_full`). -/
theorem update_elections_data_client_request_allEntries_head_term
    (me : name (P := P)) (st : electionsData (P := P) × raft_data (P := P))
    (client : R.clientId) (id : Nat) (c : P.input) {out d l}
    (hcr : handleClientRequest me st.2 client id c = (out, d, l)) :
    (update_elections_data_client_request me st client id c).allEntries
      = st.1.allEntries ∨
    ∃ e : entry (P := P), e.eTerm = d.currentTerm ∧
      (update_elections_data_client_request me st client id c).allEntries
        = (d.currentTerm, e) :: st.1.allEntries := by
  unfold update_elections_data_client_request
  rw [hcr]
  simp only []
  rcases handleClientRequest_log_full me st.2 client id c hcr with
    ⟨-, hlog⟩ | ⟨-, heq⟩
  · rw [hlog, if_pos (by
      simp only [Nat.blt_eq, List.length_cons]
      exact Nat.lt_succ_self _)]
    exact Or.inr ⟨_,
      ((handleClientRequest_spec me st.2 client id c hcr).2.1).symm, rfl⟩
  · rw [heq, if_neg (by
      simp only [Nat.blt_eq]
      exact Nat.lt_irrefl _)]
    exact Or.inl rfl

/-- Transport for `allEntries_leaderLogs_term` across steps that keep
`allEntries` at the updated node and only grow its leaderLogs. -/
theorem allEntries_leaderLogs_term_of_update {net net' : RefinedNet}
    {u : name (P := P)} {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hP : allEntries_leaderLogs_term net)
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hgrow : ∀ (t : term) (ll : List (entry (P := P))),
      (t, ll) ∈ (net.nwState u).1.leaderLogs → (t, ll) ∈ gd.leaderLogs)
    (hae : gd.allEntries = (net.nwState u).1.allEntries) :
    allEntries_leaderLogs_term net' := by
  intro t e h hin
  replace hin : (t, e) ∈ (net'.nwState h).1.allEntries := hin
  have hin' : (t, e) ∈ (net.nwState h).1.allEntries := by
    rw [hst h] at hin
    by_cases heq : h = u
    · subst heq
      rw [update_same] at hin
      replace hin : (t, e) ∈ gd.allEntries := hin
      rw [hae] at hin
      exact hin
    · rw [update_neq _ _ heq] at hin
      exact hin
  rcases hP t e h hin' with h1 | ⟨ll, leader, hmem, hell⟩
  · exact Or.inl h1
  · refine Or.inr ⟨ll, leader, ?_, hell⟩
    rw [hst leader]
    by_cases heql : leader = u
    · subst heql
      rw [update_same]
      exact hgrow _ _ hmem
    · rw [update_neq _ _ heql]
      exact hmem

/-- `AllEntriesLeaderLogsTermProof.v:322-340`
(`allEntries_leaderLogs_term_invariant`): the append-entries case is
`append_entries_leaderLogs`' payoff — a freshly recorded entry either
came in the request's own-term block or inside the prefix of a
leaderLog snapshot at the request's term; a leader's fresh record is at
its own term. -/
theorem allEntries_leaderLogs_term_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      allEntries_leaderLogs_term net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro t e h hin
    exact nomatch hin
  · -- client_request
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst hps
    have hgrow : ∀ (t2 : term) (ll : List (entry (P := P))),
        (t2, ll) ∈ (net.nwState h).1.leaderLogs →
        (t2, ll) ∈ gd.leaderLogs := by
      intro t2 ll hin
      subst hgd
      rw [(update_elections_data_client_request_ghost h (net.nwState h)
        client id c).2.2.2]
      exact hin
    rcases update_elections_data_client_request_allEntries_head_term h
      (net.nwState h) client id c hcr with hsame | ⟨enew, hterm, hcons⟩
    · exact allEntries_leaderLogs_term_of_update hP hst hgrow
        (hgd ▸ hsame)
    · intro t e h0 hin
      replace hin : (t, e) ∈ (st' h0).1.allEntries := hin
      have hred : (t, e) ∈ (net.nwState h0).1.allEntries ∨
          (t = d.currentTerm ∧ e = enew) := by
        rw [hst h0] at hin
        by_cases heq : h0 = h
        · subst heq
          rw [update_same] at hin
          replace hin : (t, e) ∈ gd.allEntries := hin
          rw [hgd, hcons] at hin
          rcases List.mem_cons.mp hin with heq2 | hin
          · injection heq2 with h1 h2
            exact Or.inr ⟨h1, h2⟩
          · exact Or.inl hin
        · rw [update_neq _ _ heq] at hin
          exact Or.inl hin
      rcases hred with hin' | ⟨rfl, rfl⟩
      · rcases hP t e h0 hin' with h1 | ⟨ll, leader, hmem, hell⟩
        · exact Or.inl h1
        · refine Or.inr ⟨ll, leader, ?_, hell⟩
          show (t, ll) ∈ (st' leader).1.leaderLogs
          rw [hst leader]
          by_cases heql : leader = h
          · subst heql
            rw [update_same]
            exact hgrow _ _ hmem
          · rw [update_neq _ _ heql]
            exact hmem
      · exact Or.inl hterm.symm
  · -- timeout
    intro net h st' ps' gd out d l hto hgd hP _hreach hst hps
    refine allEntries_leaderLogs_term_of_update hP hst ?_ ?_
    · intro t2 ll hin
      subst hgd
      rw [(update_elections_data_timeout_ghost h (net.nwState h)).1]
      exact hin
    · subst hgd
      exact (update_elections_data_timeout_ghost h (net.nwState h)).2
  · -- append_entries: append_entries_leaderLogs pays off
    intro xs p ys net st' ps' gd d m t n0 pli plt es ci hae hgd hbody hP
      hreach hpkts hst hps
    have hpin : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    have hgrow : ∀ (t2 : term) (ll : List (entry (P := P))),
        (t2, ll) ∈ (net.nwState p.pDst).1.leaderLogs →
        (t2, ll) ∈ gd.leaderLogs := by
      intro t2 ll hin
      subst hgd
      rw [(update_elections_data_appendEntries_ghost p.pDst
        (net.nwState p.pDst) t n0 pli plt es ci).2.2.2]
      exact hin
    have hreloc : ∀ (t2 : term) (ll : List (entry (P := P)))
        (leader : name (P := P)),
        (t2, ll) ∈ (net.nwState leader).1.leaderLogs →
        (t2, ll) ∈ (st' leader).1.leaderLogs := by
      intro t2 ll leader hin
      rw [hst leader]
      by_cases heq : leader = p.pDst
      · subst heq
        rw [update_same]
        exact hgrow _ _ hin
      · rw [update_neq _ _ heq]
        exact hin
    rcases update_elections_data_appendEntries_allEntries_term_cases
      p.pDst (net.nwState p.pDst) t n0 pli plt es ci hae with hsame |
      ⟨t', hm, hcons⟩
    · exact allEntries_leaderLogs_term_of_update hP hst hgrow
        (hgd ▸ hsame)
    · have ht' : t' = t :=
        (handleAppendEntries_reply_true p.pDst (net.nwState p.pDst).2 t n0
          pli plt es ci (hm ▸ hae)).1
      intro t0 e h0 hin
      replace hin : (t0, e) ∈ (st' h0).1.allEntries := hin
      have hred : (t0, e) ∈ (net.nwState h0).1.allEntries ∨
          (t0 = t' ∧ e ∈ es) := by
        rw [hst h0] at hin
        by_cases heq : h0 = p.pDst
        · subst heq
          rw [update_same] at hin
          replace hin : (t0, e) ∈ gd.allEntries := hin
          rw [hgd, hcons] at hin
          rcases List.mem_append.mp hin with hmap | hold
          · obtain ⟨e2, he2, heq2⟩ := List.mem_map.mp hmap
            injection heq2 with h1 h2
            exact Or.inr ⟨h1.symm, h2 ▸ he2⟩
          · exact Or.inl hold
        · rw [update_neq _ _ heq] at hin
          exact Or.inl hin
      rcases hred with hin' | ⟨rfl, hees⟩
      · rcases hP t0 e h0 hin' with h1 | ⟨ll, leader, hmem, hell⟩
        · exact Or.inl h1
        · exact Or.inr ⟨ll, leader, hreloc _ _ _ hmem, hell⟩
      · -- the fresh record: classify e inside the request via the
        -- packet invariant
        obtain ⟨h1, ll, es', ll', hsplit, hterm, hmem, hpref, -⟩ :=
          append_entries_leaderLogs_invariant net hreach p t n0 pli plt es
            ci hpin hbody
        rw [hsplit] at hees
        rcases List.mem_append.mp hees with hes' | hll'
        · exact Or.inl (ht'.trans (hterm e hes').symm)
        · refine Or.inr ⟨ll, h1, ?_, Prefix_In hpref e hll'⟩
          rw [ht']
          exact hreloc _ _ _ hmem
  · -- append_entries_reply: ghost untouched
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP _hreach
      hpkts hst hps
    refine allEntries_leaderLogs_term_of_update hP hst ?_ ?_
    · intro t2 ll hin
      rw [hgd]
      exact hin
    · rw [hgd]
  · -- request_vote
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP
      _hreach hpkts hst hps
    refine allEntries_leaderLogs_term_of_update hP hst ?_ ?_
    · intro t2 ll hin
      subst hgd
      rw [(update_elections_data_requestVote_cronies p.pDst p.pSrc t
        p.pSrc lli llt (net.nwState p.pDst)).2.1]
      exact hin
    · subst hgd
      exact (update_elections_data_requestVote_cronies p.pDst p.pSrc t
        p.pSrc lli llt (net.nwState p.pDst)).2.2
  · -- request_vote_reply: leaderLogs grow, allEntries untouched
    intro xs p ys net st' ps' gd d t v hrvr hgd _hbody hP _hreach hpkts
      hst hps
    refine allEntries_leaderLogs_term_of_update hP hst ?_ ?_
    · intro t2 ll hin
      subst hgd
      exact update_elections_data_requestVoteReply_leaderLogs_old p.pDst
        p.pSrc t v (net.nwState p.pDst) hin
    · subst hgd
      exact (update_elections_data_requestVoteReply_votes p.pDst p.pSrc t
        v (net.nwState p.pDst)).2.2
  · -- do_leader
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst hps
    refine allEntries_leaderLogs_term_of_update hP hst ?_ ?_
    · intro t2 ll hin
      rw [hstate] at hin
      exact hin
    · rw [hstate]
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps
    refine allEntries_leaderLogs_term_of_update hP hst ?_ ?_
    · intro t2 ll hin
      rw [hstate] at hin
      exact hin
    · rw [hstate]
  · -- state_same_packet_subset
    intro net net' hstates hsub hP _hreach t e h hin
    replace hin : (t, e) ∈ (net'.nwState h).1.allEntries := hin
    rw [← hstates h] at hin
    rcases hP t e h hin with h1 | ⟨ll, leader, hmem, hell⟩
    · exact Or.inl h1
    · rw [hstates leader] at hmem
      exact Or.inr ⟨ll, leader, hmem, hell⟩
  · -- reboot
    intro net net' gd d h d' _hrb hP _hreach hstate hst hpkts
    refine allEntries_leaderLogs_term_of_update hP hst ?_ ?_
    · intro t2 ll hin
      rw [hstate] at hin
      exact hin
    · rw [hstate]

end LeaderLogsAssembly
end Raft
end VerdiCompat
