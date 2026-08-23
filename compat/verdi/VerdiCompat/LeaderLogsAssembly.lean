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
        = (d.currentTerm, e) :: st.1.allEntries ∧
      st.2.type = .Leader ∧ e ∈ d.log ∧
      e.eIndex = maxIndex st.2.log + 1 := by
  unfold update_elections_data_client_request
  rw [hcr]
  simp only []
  rcases handleClientRequest_log_full me st.2 client id c hcr with
    ⟨hty, hlog⟩ | ⟨-, heq⟩
  · rw [hlog, if_pos (by
      simp only [Nat.blt_eq, List.length_cons]
      exact Nat.lt_succ_self _)]
    exact Or.inr ⟨_,
      ((handleClientRequest_spec me st.2 client id c hcr).2.1).symm, rfl,
      hty, List.mem_cons_self .., rfl⟩
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
      (net.nwState h) client id c hcr with hsame | ⟨enew, hterm, hcons, -, -, -⟩
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

/-! ## AllEntriesLog support layer (`AllEntriesLogProof.v:36-265`,
`SpecLemmas.v` handler details) -/

omit O in
/-- A nonempty sorted-shape list realizes its `maxIndex`/`maxTerm` at
its head (`CommonTheorems.v` `maxIndex_non_empty`). -/
theorem maxIndex_non_empty {l : List (entry (P := P))} (h : l ≠ []) :
    ∃ e ∈ l, e.eIndex = maxIndex l ∧ e.eTerm = maxTerm l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a as => exact ⟨a, List.mem_cons_self .., rfl, rfl⟩

omit O in
/-- `AllEntriesLogProof.v:130-144` (`maxIndex_le'`). -/
theorem maxIndex_le' {l1 l2 : List (entry (P := P))} {i : logIndex}
    (hs1 : sorted l1) (hc1 : contiguous_range_exact_lo l1 0)
    (hne : l2 ≠ []) (hc2 : contiguous_range_exact_lo l2 i)
    (hf : findAtIndex l1 (maxIndex l2) = none) :
    maxIndex l1 ≤ maxIndex l2 := by
  rcases Nat.lt_or_ge (maxIndex l2) (maxIndex l1) with hlt | hge
  · exfalso
    have hpos : 0 < maxIndex l2 := by
      obtain ⟨e2, he2, hidx2, -⟩ := maxIndex_non_empty hne
      rw [← hidx2]
      exact Nat.lt_of_le_of_lt (Nat.zero_le i) (hc2.2 e2 he2)
    obtain ⟨e1, hidx1, he1⟩ := hc1.1 (maxIndex l2) ⟨hpos, Nat.le_of_lt hlt⟩
    exact findAtIndex_None hs1 hf he1 hidx1
  · exact hge

omit O in
/-- `AllEntriesLogProof.v:242-251` (`Prefix_maxIndex_eq`). -/
theorem Prefix_maxIndex_eq {l l' : List (entry (P := P))}
    (hp : Prefix l l') (hne : l ≠ []) : maxIndex l = maxIndex l' := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a l0 =>
    cases l' with
    | nil => exact absurd hp not_false
    | cons b l1 =>
      obtain ⟨rfl, -⟩ := hp
      rfl

omit O in
/-- `CommonTheorems.v:1554-1573` (`prefix_contiguous`): a member of the
whole list above the cut lands in any nonempty contiguous prefix. -/
theorem prefix_contiguous {l l' : List (entry (P := P))}
    {e : entry (P := P)} {i : logIndex} (hne : l' ≠ [])
    (hp : Prefix l' l) (hs : sorted l) (he : e ∈ l)
    (hgt : e.eIndex > i) (hc : contiguous_range_exact_lo l' i) :
    e ∈ l' := by
  induction l generalizing l' with
  | nil => exact nomatch he
  | cons a l0 ih =>
    cases l' with
    | nil => exact absurd rfl hne
    | cons b l1 =>
      obtain ⟨rfl, hp'⟩ := hp
      rcases List.mem_cons.mp he with rfl | he'
      · exact List.mem_cons_self ..
      · cases hl1 : l1 with
        | nil =>
          -- singleton prefix: its head index is i+1; anything above i
          -- in the tail of l contradicts sortedness
          exfalso
          subst hl1
          have hbi : b.eIndex = i + 1 := contiguous_index_singleton hc
          have hlt : e.eIndex < b.eIndex := (hs.1 e he').1
          rw [hbi] at hlt
          exact absurd hgt (Nat.not_lt.mpr (Nat.le_of_lt_succ hlt))
        | cons c l2 =>
          subst hl1
          refine List.mem_cons_of_mem _ (ih ?_ hp' hs.2 he' ?_)
          · exact List.cons_ne_nil c l2
          · exact cons_contiguous_sorted
              (prefix_sorted hs ⟨rfl, hp'⟩) hc

omit O in
/-- `haveNewEntries` elimination (`SpecLemmas.v` `haveNewEntries_true`). -/
theorem haveNewEntries_true {st : raft_data (P := P)}
    {es : List (entry (P := P))} (h : haveNewEntries st es = true) :
    es ≠ [] ∧
    (findAtIndex st.log (maxIndex es) = none ∨
     ∃ em, findAtIndex st.log (maxIndex es) = some em ∧
       em.eTerm ≠ maxTerm es) := by
  unfold haveNewEntries at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro heq
    subst heq
    exact nomatch h1
  · rcases hf : findAtIndex st.log (maxIndex es) with _ | em
    · exact Or.inl rfl
    · rw [hf] at h2
      refine Or.inr ⟨em, rfl, ?_⟩
      intro heq
      rw [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne] at h2
      exact h2 heq.symm

/-- `AllEntriesLogProof.v:79-102` (`appendEntries_haveNewEntries_false`):
if a packet's entries are not news to a host, they are all in its log
(via the shared max entry and log matching). -/
theorem appendEntries_haveNewEntries_false :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      ∀ (p : RefinedPacket) (t : term) (n : name (P := P))
        (pli : logIndex) (plt : term) (es : List (entry (P := P)))
        (ci : logIndex) (h : name (P := P)) (e : entry (P := P)),
        p ∈ net.nwPackets → p.pBody = .AppendEntries t n pli plt es ci →
        haveNewEntries (net.nwState h).2 es = false →
        e ∈ es → e ∈ (net.nwState h).2.log := by
  intro net hreach p t n pli plt es ci h e hp hbody hfalse he
  cases es with
  | nil => exact nomatch he
  | cons e1 es1 =>
    unfold haveNewEntries not_empty at hfalse
    simp only [Bool.true_and] at hfalse
    rcases hf : findAtIndex (net.nwState h).2.log (maxIndex (e1 :: es1))
      with _ | em
    · rw [hf] at hfalse
      exact nomatch hfalse
    · rw [hf] at hfalse
      simp only [] at hfalse
      have hbeq : maxTerm (e1 :: es1) = em.eTerm := by
        rcases hb : (maxTerm (e1 :: es1) == em.eTerm) with _ | _
        · rw [hb] at hfalse
          exact nomatch hfalse
        · exact beq_iff_eq.mp hb
      obtain ⟨hemL, hemidx⟩ := findAtIndex_elim hf
      have hsortes : sorted (e1 :: es1) :=
        entries_sorted_nw_invariant net hreach p t n pli plt (e1 :: es1)
          ci hp hbody
      refine entries_match_nw_host_invariant net hreach p t n pli plt
        (e1 :: es1) ci h e1 em e hp hbody (List.mem_cons_self ..) hemL
        hemidx.symm hbeq he ?_
      exact maxIndex_is_max hsortes he

omit O in
/-- `SpecLemmas.v:236-280` (`handleAppendEntries_log_detailed`), in the
shape the AllEntriesLog induction consumes: unchanged log, or an ACCEPT
with the leaderId set, the current term at the request's, the entries
genuinely new, and the log wholesale or spliced at a real pivot. -/
theorem handleAppendEntries_accept_detail (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (lid : name (P := P))
    (pli : logIndex) (plt : term) (es : List (entry (P := P)))
    (ci : logIndex) {st' m}
    (h : handleAppendEntries me st t lid pli plt es ci = (st', m)) :
    st'.log = st.log ∨
    (st'.leaderId ≠ none ∧ st'.currentTerm = t ∧
     haveNewEntries st es = true ∧
     ((pli = 0 ∧ st'.log = es) ∨
      (∃ e0, e0 ∈ st.log ∧ e0.eIndex = pli ∧ e0.eTerm = plt ∧
        st'.log = es ++ removeAfterIndex st.log pli))) := by
  have hadv := advanceCurrentTerm_spec st t
  unfold handleAppendEntries at h
  split at h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  · rename_i hng
    have hle : st.currentTerm ≤ t :=
      Nat.not_lt.mp (fun hlt => hng (by simpa [Nat.blt_eq] using hlt))
    split at h
    · rename_i hpli0
      simp only [beq_iff_eq] at hpli0
      split at h
      · rename_i hnew
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        refine Or.inr ⟨?_, ?_, ?_, Or.inl ⟨hpli0, ?_⟩⟩
        · exact fun hc => nomatch hc
        · exact advanceCurrentTerm_le_eq hle
        · exact hnew
        · rfl
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact Or.inl hadv.2.1
    · split at h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact Or.inl rfl
      · rename_i e0 hfind
        split at h
        · simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact Or.inl rfl
        · rename_i hterm0
          have hplt : plt = e0.eTerm := by
            rcases hb : (plt == e0.eTerm) with _ | _
            · rw [hb] at hterm0
              exact absurd rfl hterm0
            · exact beq_iff_eq.mp hb
          obtain ⟨he0L, he0idx⟩ := findAtIndex_elim hfind
          split at h
          · rename_i hnew
            simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            refine Or.inr ⟨?_, ?_, ?_, Or.inr ⟨e0, he0L, he0idx, hplt.symm, ?_⟩⟩
            · exact fun hc => nomatch hc
            · exact advanceCurrentTerm_le_eq hle
            · exact hnew
            · rfl
          · simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            exact Or.inl hadv.2.1

omit O in
/-- `advanceCurrentTerm` on term/leaderId (`SpecLemmas.v:335-344`). -/
theorem advanceCurrentTerm_currentTerm_leaderId (st : raft_data (P := P))
    (t : term) :
    st.currentTerm < (advanceCurrentTerm st t).currentTerm ∨
    ((advanceCurrentTerm st t).currentTerm = st.currentTerm ∧
     (advanceCurrentTerm st t).leaderId = st.leaderId) := by
  unfold advanceCurrentTerm
  split
  · rename_i hgt
    exact Or.inl (by simpa [Nat.blt_eq] using hgt)
  · exact Or.inr ⟨rfl, rfl⟩

omit O in
/-- `AllEntriesLogProof.v:822-830`
(`handleAppendEntriesReply_currentTerm_leaderId`). -/
theorem handleAppendEntriesReply_currentTerm_leaderId
    (me : name (P := P)) (st : raft_data (P := P)) (src : name (P := P))
    (t : term) (es : List (entry (P := P))) (r : Bool) {st' l}
    (h : handleAppendEntriesReply me st src t es r = (st', l)) :
    st.currentTerm < st'.currentTerm ∨
    (st'.currentTerm = st.currentTerm ∧ st'.leaderId = st.leaderId) := by
  have hadv := advanceCurrentTerm_currentTerm_leaderId st t
  unfold handleAppendEntriesReply at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, -⟩ := h
  all_goals first
    | exact Or.inr ⟨rfl, rfl⟩
    | exact hadv

omit O in
/-- `SpecLemmas.v` (`handleRequestVote_currentTerm_leaderId`). -/
theorem handleRequestVote_currentTerm_leaderId (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (cand : name (P := P))
    (lli : logIndex) (llt : term) {st' m}
    (h : handleRequestVote me st t cand lli llt = (st', m)) :
    st.currentTerm < st'.currentTerm ∨
    (st'.currentTerm = st.currentTerm ∧ st'.leaderId = st.leaderId) := by
  have hadv := advanceCurrentTerm_currentTerm_leaderId st t
  unfold handleRequestVote at h
  simp only [] at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, -⟩ := h
  all_goals first
    | exact Or.inr ⟨rfl, rfl⟩
    | exact hadv
    | (rcases hadv with hlt | ⟨heq, hlid⟩
       · exact Or.inl hlt
       · exact Or.inr ⟨heq, hlid⟩)

omit O in
/-- (`handleRequestVoteReply_currentTerm_leaderId`). -/
theorem handleRequestVoteReply_currentTerm_leaderId (me : name (P := P))
    (st : raft_data (P := P)) (src : name (P := P)) (t : term) (v : Bool) :
    st.currentTerm <
      (handleRequestVoteReply me st src t v).currentTerm ∨
    ((handleRequestVoteReply me st src t v).currentTerm = st.currentTerm ∧
     (handleRequestVoteReply me st src t v).leaderId = st.leaderId) := by
  have hadv := advanceCurrentTerm_currentTerm_leaderId st t
  unfold handleRequestVoteReply
  simp only []
  repeat' split
  all_goals first
    | exact Or.inr ⟨rfl, rfl⟩
    | exact hadv

omit O in
/-- (`handleClientRequest_currentTerm_leaderId`). -/
theorem handleClientRequest_currentTerm_leaderId (me : name (P := P))
    (st : raft_data (P := P)) (client : R.clientId) (id : Nat)
    (c : P.input) {out st' l}
    (h : handleClientRequest me st client id c = (out, st', l)) :
    st'.currentTerm = st.currentTerm ∧ st'.leaderId = st.leaderId := by
  unfold handleClientRequest at h
  split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨-, rfl, -⟩ := h
  all_goals exact ⟨rfl, rfl⟩

omit O in
/-- (`handleTimeout_currentTerm_leaderId`). -/
theorem handleTimeout_currentTerm_leaderId (me : name (P := P))
    (st : raft_data (P := P)) {out st' l}
    (h : handleTimeout me st = (out, st', l)) :
    st.currentTerm < st'.currentTerm ∨
    (st'.currentTerm = st.currentTerm ∧ st'.leaderId = st.leaderId) := by
  unfold handleTimeout tryToBecomeLeader at h
  split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨-, rfl, -⟩ := h
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl (Nat.lt_succ_self _)

omit O in
/-- (`doLeader_currentTerm_leaderId`). -/
theorem doLeader_currentTerm_leaderId (st : raft_data (P := P))
    (me : name (P := P)) {os st' ms} (h : doLeader st me = (os, st', ms)) :
    st'.currentTerm = st.currentTerm ∧ st'.leaderId = st.leaderId := by
  unfold doLeader advanceCommitIndex at h
  simp only [] at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨-, rfl, -⟩ := h
  all_goals exact ⟨rfl, rfl⟩

/-- `cacheApplyEntry` never touches `leaderId`. -/
theorem cacheApplyEntry_leaderId (st : raft_data (P := P))
    (e : entry (P := P)) {o st'} (h : cacheApplyEntry st e = (o, st')) :
    st'.leaderId = st.leaderId := by
  unfold cacheApplyEntry applyEntry at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨-, rfl⟩ := h
  all_goals rfl

/-- `applyEntries` never touches `leaderId`. -/
theorem applyEntries_leaderId (me : name (P := P)) :
    ∀ (es : List (entry (P := P))) (st : raft_data (P := P)) {o st'},
    applyEntries me st es = (o, st') → st'.leaderId = st.leaderId := by
  intro es
  induction es with
  | nil =>
    intro st o st' h
    unfold applyEntries at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  | cons e es ih =>
    intro st o st' h
    unfold applyEntries at h
    rcases hc : cacheApplyEntry st e with ⟨o1, st1⟩
    rw [hc] at h
    simp only [] at h
    rcases ha : applyEntries me st1 es with ⟨o2, st2⟩
    rw [ha] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rw [ih st1 ha, cacheApplyEntry_leaderId st e hc]

/-- (`doGenericServer_currentTerm_leaderId`). -/
theorem doGenericServer_currentTerm_leaderId (me : name (P := P))
    (st : raft_data (P := P)) {os st' ms}
    (h : doGenericServer me st = (os, st', ms)) :
    st'.currentTerm = st.currentTerm ∧ st'.leaderId = st.leaderId := by
  unfold doGenericServer at h
  rcases hae : applyEntries me st
      ((findGtIndex st.log st.lastApplied).filter
        (fun x => (st.lastApplied <? x.eIndex) &&
          (x.eIndex <=? st.commitIndex))).reverse
    with ⟨o1, st1⟩
  rw [hae] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨-, rfl, -⟩ := h
  obtain ⟨-, -, hct, -, -, -, -⟩ := applyEntries_spec me _ st hae
  have hlid : st1.leaderId = st.leaderId :=
    applyEntries_leaderId me _ st hae
  exact ⟨hct, hlid⟩

/-! ## allEntries_log (`AllEntriesLogInterface.v:10-19`) -/

/-- `AllEntriesLogInterface.v:10-19` (`allEntries_log`): every recorded
entry is in its recorder's log, or was overwritten by a later leader
whose election snapshot excludes it (with the recorder's term/leaderId
fine print). -/
def allEntries_log (net : RefinedNet) : Prop :=
  ∀ (t : term) (e : entry (P := P)) (h : name (P := P)),
    (t, e) ∈ (net.nwState h).1.allEntries →
    e ∈ (net.nwState h).2.log ∨
    ∃ (t' : term) (leader : name (P := P)) (ll : List (entry (P := P))),
      (t', ll) ∈ (net.nwState leader).1.leaderLogs ∧
      t < t' ∧ t' ≤ (net.nwState h).2.currentTerm ∧
      e ∉ ll ∧
      ((net.nwState h).2.leaderId ≠ none ∨
       t' < (net.nwState h).2.currentTerm)

/-- Transport for `allEntries_log` across steps that keep allEntries and
log at the updated node, grow leaderLogs, and move currentTerm/leaderId
per the standard handler shape. -/
theorem allEntries_log_of_update {net net' : RefinedNet}
    {u : name (P := P)} {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hP : allEntries_log net)
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hgrow : ∀ (t : term) (ll : List (entry (P := P))),
      (t, ll) ∈ (net.nwState u).1.leaderLogs → (t, ll) ∈ gd.leaderLogs)
    (hae : gd.allEntries = (net.nwState u).1.allEntries)
    (hlog : d.log = (net.nwState u).2.log)
    (hctlid : (net.nwState u).2.currentTerm < d.currentTerm ∨
      (d.currentTerm = (net.nwState u).2.currentTerm ∧
       d.leaderId = (net.nwState u).2.leaderId)) :
    allEntries_log net' := by
  intro t e h hin
  replace hin : (t, e) ∈ (net'.nwState h).1.allEntries := hin
  by_cases heq : h = u
  · subst heq
    have hst2 : net'.nwState h = (gd, d) := by
      rw [hst h, update_same]
    rw [hst2] at hin
    replace hin : (t, e) ∈ gd.allEntries := hin
    rw [hae] at hin
    rcases hP t e h hin with hL |
      ⟨t', leader, ll, hmem, hlt, hle, hnin, hlast⟩
    · left
      rw [hst2]
      show e ∈ d.log
      rw [hlog]
      exact hL
    · right
      refine ⟨t', leader, ll, ?_, hlt, ?_, hnin, ?_⟩
      · rw [hst leader]
        by_cases heql : leader = h
        · subst heql
          rw [update_same]
          exact hgrow _ _ hmem
        · rw [update_neq _ _ heql]
          exact hmem
      · rw [hst2]
        show t' ≤ d.currentTerm
        rcases hctlid with hlt2 | ⟨hct2, -⟩
        · exact Nat.le_of_lt (Nat.lt_of_le_of_lt hle hlt2)
        · rw [hct2]
          exact hle
      · rw [hst2]
        show d.leaderId ≠ none ∨ t' < d.currentTerm
        rcases hctlid with hlt2 | ⟨hct2, hlid2⟩
        · exact Or.inr (Nat.lt_of_le_of_lt hle hlt2)
        · rcases hlast with h1 | h1
          · left
            rw [hlid2]
            exact h1
          · right
            rw [hct2]
            exact h1
  · have hst2 : net'.nwState h = net.nwState h := by
      rw [hst h, update_neq _ _ heq]
    rw [hst2] at hin
    rcases hP t e h hin with hL |
      ⟨t', leader, ll, hmem, hlt, hle, hnin, hlast⟩
    · left
      rw [hst2]
      exact hL
    · right
      refine ⟨t', leader, ll, ?_, hlt, ?_, hnin, ?_⟩
      · rw [hst leader]
        by_cases heql : leader = u
        · subst heql
          rw [update_same]
          exact hgrow _ _ hmem
        · rw [update_neq _ _ heql]
          exact hmem
      · rw [hst2]
        exact hle
      · rw [hst2]
        exact hlast

omit O in
/-- `AllEntriesLogProof.v:905-917`
(`update_elections_data_client_request_allEntries'`). -/
theorem update_elections_data_client_request_allEntries_mem
    (me : name (P := P)) (st : electionsData (P := P) × raft_data (P := P))
    (client : R.clientId) (id : Nat) (c : P.input) {out d l}
    (hcr : handleClientRequest me st.2 client id c = (out, d, l))
    {t : term} {e : entry (P := P)}
    (hin : (t, e) ∈
      (update_elections_data_client_request me st client id c).allEntries) :
    (t, e) ∈ st.1.allEntries ∨ e ∈ d.log := by
  unfold update_elections_data_client_request at hin
  rw [hcr] at hin
  simp only [] at hin
  split at hin
  · rename_i hlen
    rcases hdl : d.log with _ | ⟨e1, rest⟩
    · rw [hdl] at hin
      exact Or.inl hin
    · rw [hdl] at hin
      replace hin : (t, e) ∈ (d.currentTerm, e1) :: st.1.allEntries := hin
      rcases List.mem_cons.mp hin with heq | hin
      · injection heq with h1 h2
        right
        rw [h2]
        exact List.mem_cons_self ..
      · exact Or.inl hin
  · exact Or.inl hin

omit O in
/-- `SpecLemmas.v:346-355` (`handleAppendEntries_currentTerm_leaderId`),
in the transport-ready shape. -/
theorem handleAppendEntries_currentTerm_leaderId (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (lid : name (P := P))
    (pli : logIndex) (plt : term) (es : List (entry (P := P)))
    (ci : logIndex) {st' m}
    (h : handleAppendEntries me st t lid pli plt es ci = (st', m)) :
    st.currentTerm ≤ st'.currentTerm ∧
    (st.currentTerm < st'.currentTerm ∨ st'.leaderId = st.leaderId ∨
     st'.leaderId ≠ none) := by
  have hadv := advanceCurrentTerm_currentTerm_leaderId st t
  have hle_adv : st.currentTerm ≤ (advanceCurrentTerm st t).currentTerm := by
    rcases hadv with hlt | ⟨heq2, -⟩
    · exact Nat.le_of_lt hlt
    · exact Nat.le_of_eq heq2.symm
  unfold handleAppendEntries at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, -⟩ := h
  all_goals first
    | exact ⟨Nat.le_refl _, Or.inr (Or.inl rfl)⟩
    | exact ⟨hle_adv, Or.inr (Or.inr (fun hc => nomatch hc))⟩

omit O in
/-- A TRUE AppendEntries reply certifies its entries are all in the new
log, or nothing was new and the log is untouched. -/
theorem handleAppendEntries_true_reply_log (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (lid : name (P := P))
    (pli : logIndex) (plt : term) (es : List (entry (P := P)))
    (ci : logIndex) {d : raft_data (P := P)} {t' : term}
    {es' : List (entry (P := P))}
    (h : handleAppendEntries me st t lid pli plt es ci
      = (d, .AppendEntriesReply t' es' true)) :
    (∀ x ∈ es, x ∈ d.log) ∨
    (haveNewEntries st es = false ∧ d.log = st.log) := by
  have hadv := advanceCurrentTerm_spec st t
  unfold handleAppendEntries at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, hm⟩ := h
  · exact absurd hm (by intro hc; injection hc with f1 f2 f3; exact nomatch f3)
  · exact Or.inl (fun x hx => hx)
  · rename_i hcond
    refine Or.inr ⟨?_, hadv.2.1⟩
    rcases hb : haveNewEntries st es with _ | _
    · rfl
    · exact absurd hb hcond
  · exact absurd hm (by intro hc; injection hc with f1 f2 f3; exact nomatch f3)
  · exact absurd hm (by intro hc; injection hc with f1 f2 f3; exact nomatch f3)
  · exact Or.inl (fun x hx => List.mem_append.mpr (Or.inl hx))
  · rename_i hcond
    refine Or.inr ⟨?_, hadv.2.1⟩
    rcases hb : haveNewEntries st es with _ | _
    · rfl
    · exact absurd hb hcond

omit O in
/-- The membership form of the append-entries ghost update
(`RefinementSpecLemmas.v`
`update_elections_data_appendEntries_allEntries_detailed`). -/
theorem update_elections_data_appendEntries_allEntries_mem
    (me : name (P := P)) (st : electionsData (P := P) × raft_data (P := P))
    (t : term) (lid : name (P := P)) (pli : logIndex) (plt : term)
    (es : List (entry (P := P))) (ci : logIndex) {d m}
    (hae : handleAppendEntries me st.2 t lid pli plt es ci = (d, m))
    {te : term} {e : entry (P := P)}
    (hin : (te, e) ∈ (update_elections_data_appendEntries me st t lid pli
      plt es ci).allEntries) :
    (te, e) ∈ st.1.allEntries ∨ e ∈ d.log ∨
    (e ∈ es ∧ haveNewEntries st.2 es = false ∧ d.log = st.2.log) := by
  obtain ⟨t'', r'', rfl⟩ :=
    handleAppendEntries_reply_entries me st.2 t lid pli plt es ci hae
  unfold update_elections_data_appendEntries at hin
  rw [hae] at hin
  cases r''
  · exact Or.inl hin
  · simp only [] at hin
    replace hin : (te, e) ∈ (es.map fun e => (t'', e)) ++ st.1.allEntries :=
      hin
    rcases List.mem_append.mp hin with hmap | hold
    · obtain ⟨e2, he2, heq2⟩ := List.mem_map.mp hmap
      injection heq2 with h1 h2
      have hees : e ∈ es := h2 ▸ he2
      rcases handleAppendEntries_true_reply_log me st.2 t lid pli plt es
        ci hae with hall | ⟨hnf, hlog⟩
      · exact Or.inr (Or.inl (hall e hees))
      · exact Or.inr (Or.inr ⟨hees, hnf, hlog⟩)
    · exact Or.inl hold

/-- Snapshot containment: under an ACCEPT, a host-log member of the
packet's term-`t` snapshot is in the new log. (One of the two
containment lemmas replacing upstream's per-case exfalso battles —
`AllEntriesLogProof.v:267-820`; same invariant lattice, re-derived
route, logged in the arc log.) -/
theorem ae_snapshot_in_newlog {net : RefinedNet}
    (hreach : refined_raft_intermediate_reachable (P := P) net)
    {p : RefinedPacket} {t : term} {n0 : name (P := P)} {pli : logIndex}
    {plt : term} {es : List (entry (P := P))} {ci : logIndex}
    (hpin : p ∈ net.nwPackets)
    (hbody : p.pBody = .AppendEntries t n0 pli plt es ci)
    {w : name (P := P)} {d : raft_data (P := P)}
    (hshape : (pli = 0 ∧ d.log = es) ∨
      (∃ e0, e0 ∈ (net.nwState w).2.log ∧ e0.eIndex = pli ∧
        e0.eTerm = plt ∧
        d.log = es ++ removeAfterIndex (net.nwState w).2.log pli))
    {h1 : name (P := P)} {ll es' ll' : List (entry (P := P))}
    (hsplit : es = es' ++ ll')
    (hmem : (t, ll) ∈ (net.nwState h1).1.leaderLogs)
    (hpref : Prefix ll' ll)
    (hdisj : (plt = t ∧ pli > maxIndex ll) ∨
      (∃ e2, e2 ∈ ll ∧ e2.eIndex = pli ∧ e2.eTerm = plt ∧
        Prefix_sane ll' ll pli) ∨
      (plt = 0 ∧ pli = 0 ∧ ll' = ll))
    {e : entry (P := P)} (hell : e ∈ ll)
    (heL : e ∈ (net.nwState w).2.log) :
    e ∈ d.log := by
  have hsortll : sorted ll :=
    leaderLogs_sorted_invariant net hreach h1 t ll hmem
  have hsortes : sorted es :=
    entries_sorted_nw_invariant net hreach p t n0 pli plt es ci hpin hbody
  have hcontig_es : contiguous_range_exact_lo es pli :=
    entries_contiguous_nw_invariant net hreach p t n0 pli plt es ci hpin
      hbody
  rcases hshape with ⟨hpli0, hlog⟩ | ⟨e0, he0L, he0idx, he0term, hlog⟩
  · -- wholesale
    rcases hdisj with ⟨-, hgt⟩ | ⟨e2, he2ll, he2idx, -, -⟩ | ⟨-, -, hll⟩
    · rw [hpli0] at hgt
      exact absurd hgt (Nat.not_lt.mpr (Nat.zero_le _))
    · exfalso
      have hpos := (leaderLogs_contiguous_invariant net hreach h1 t ll
        hmem).2 e2 he2ll
      rw [he2idx, hpli0] at hpos
      exact Nat.lt_irrefl 0 hpos
    · rw [hlog, hsplit]
      exact List.mem_append.mpr (Or.inr (hll.symm ▸ hell))
  · -- splice
    rcases hdisj with ⟨-, hgt⟩ | ⟨e2, he2ll, he2idx, -, hsane⟩ |
      ⟨-, hpli0, -⟩
    · have hle : e.eIndex ≤ pli :=
        Nat.le_of_lt (Nat.lt_of_le_of_lt (maxIndex_is_max hsortll hell)
          hgt)
      rw [hlog]
      exact List.mem_append.mpr (Or.inr (removeAfterIndex_le_In hle heL))
    · rcases hsane with hll'ne | hplimax
      · by_cases hle : e.eIndex ≤ pli
        · rw [hlog]
          exact List.mem_append.mpr
            (Or.inr (removeAfterIndex_le_In hle heL))
        · have hcontig_ll' : contiguous_range_exact_lo ll' pli := by
            rw [hsplit] at hsortes hcontig_es
            exact contiguous_app hsortes hcontig_es
          have hll' := prefix_contiguous hll'ne hpref hsortll hell
            (Nat.not_le.mp hle) hcontig_ll'
          rw [hlog, hsplit]
          exact List.mem_append.mpr
            (Or.inl (List.mem_append.mpr (Or.inr hll')))
      · have hle : e.eIndex ≤ pli := by
          rw [hplimax]
          exact maxIndex_is_max hsortll hell
        rw [hlog]
        exact List.mem_append.mpr (Or.inr (removeAfterIndex_le_In hle heL))
    · exfalso
      have hpos := entries_gt_0_invariant net hreach w e0 he0L
      rw [he0idx, hpli0] at hpos
      exact Nat.lt_irrefl 0 hpos

/-- Own-term containment: under an ACCEPT with genuinely new entries, a
host-log entry AT the request's term survives into the new log (the
second containment lemma — the entry reappears inside `es` via the
haveNewEntries bound and log matching). -/
theorem ae_own_term_in_newlog {net : RefinedNet}
    (hreach : refined_raft_intermediate_reachable (P := P) net)
    {p : RefinedPacket} {t : term} {n0 : name (P := P)} {pli : logIndex}
    {plt : term} {es : List (entry (P := P))} {ci : logIndex}
    (hpin : p ∈ net.nwPackets)
    (hbody : p.pBody = .AppendEntries t n0 pli plt es ci)
    {w : name (P := P)} {d : raft_data (P := P)}
    (hnewE : haveNewEntries (net.nwState w).2 es = true)
    (hshape : (pli = 0 ∧ d.log = es) ∨
      (∃ e0, e0 ∈ (net.nwState w).2.log ∧ e0.eIndex = pli ∧
        e0.eTerm = plt ∧
        d.log = es ++ removeAfterIndex (net.nwState w).2.log pli))
    {h1 : name (P := P)} {ll es' ll' : List (entry (P := P))}
    (hsplit : es = es' ++ ll')
    (hterm' : ∀ x ∈ es', x.eTerm = t)
    (hmem : (t, ll) ∈ (net.nwState h1).1.leaderLogs)
    (hpref : Prefix ll' ll)
    (hdisj : (plt = t ∧ pli > maxIndex ll) ∨
      (∃ e2, e2 ∈ ll ∧ e2.eIndex = pli ∧ e2.eTerm = plt ∧
        Prefix_sane ll' ll pli) ∨
      (plt = 0 ∧ pli = 0 ∧ ll' = ll))
    {e : entry (P := P)} (heL : e ∈ (net.nwState w).2.log)
    (heterm : e.eTerm = t) :
    e ∈ d.log := by
  obtain ⟨lx, llx, esx, hmemx, hrmx, htermx⟩ :=
    logs_leaderLogs_invariant net hreach w e heL
  rw [heterm] at hmemx
  have hid : llx = ll :=
    one_leaderLog_per_term_log_invariant net hreach lx h1 t llx ll hmemx
      hmem
  rw [hid] at hrmx
  have hsortL : sorted (net.nwState w).2.log :=
    sorted_host_lifted net hreach w
  have hein : e ∈ esx ++ ll := by
    rw [← hrmx]
    exact removeAfterIndex_le_In (Nat.le_refl _) heL
  rcases List.mem_append.mp hein with hesx | hell
  case inr =>
    exact ae_snapshot_in_newlog hreach hpin hbody hshape hsplit hmem
      hpref hdisj hell heL
  case inl =>
    have hsortrm : sorted (esx ++ ll) := by
      rw [← hrmx]
      exact removeAfterIndex_sorted hsortL
    have hposrm : ∀ x ∈ esx ++ ll, x.eIndex > 0 := by
      intro x hx
      rw [← hrmx] at hx
      exact entries_gt_0_invariant net hreach w x (removeAfterIndex_in hx)
    have hgtll : maxIndex ll < e.eIndex :=
      sorted_app_in_1 hsortrm (hposrm e hein) hesx
    have hsortes : sorted es :=
      entries_sorted_nw_invariant net hreach p t n0 pli plt es ci hpin
        hbody
    have hcontig_es : contiguous_range_exact_lo es pli :=
      entries_contiguous_nw_invariant net hreach p t n0 pli plt es ci
        hpin hbody
    have hsortll : sorted ll :=
      leaderLogs_sorted_invariant net hreach h1 t ll hmem
    have hclose : ∀ x, x ∈ es → x ∈ d.log := by
      intro x hx
      rcases hshape with ⟨-, hlog⟩ | ⟨-, -, -, -, hlog⟩
      · rw [hlog]
        exact hx
      · rw [hlog]
        exact List.mem_append.mpr (Or.inl hx)
    have hpli_lt_or : pli < e.eIndex ∨ e ∈ d.log := by
      rcases hshape with ⟨hpli0, -⟩ | ⟨e0, he0L, he0idx, he0term, hlog⟩
      · left
        rw [hpli0]
        exact hposrm e hein
      · by_cases hle : e.eIndex ≤ pli
        · right
          rw [hlog]
          exact List.mem_append.mpr
            (Or.inr (removeAfterIndex_le_In hle heL))
        · left
          exact Nat.not_le.mp hle
    rcases hpli_lt_or with hpli_lt | hdone
    case inr => exact hdone
    obtain ⟨hesne, hfacases⟩ := haveNewEntries_true hnewE
    have hcontigL : contiguous_range_exact_lo (net.nwState w).2.log 0 :=
      logs_contiguous net hreach w
    have heIle : e.eIndex ≤ maxIndex es := by
      rcases hfacases with hnone | ⟨em, hfem, hemne⟩
      · exact Nat.le_trans (maxIndex_is_max hsortL heL)
          (maxIndex_le' hsortL hcontigL hesne hcontig_es hnone)
      · by_cases hle2 : e.eIndex ≤ maxIndex es
        · exact hle2
        · exfalso
          obtain ⟨hemL, hemidx⟩ := findAtIndex_elim hfem
          have hemin : em ∈ esx ++ ll := by
            rw [← hrmx]
            refine removeAfterIndex_le_In ?_ hemL
            rw [hemidx]
            exact Nat.le_of_lt (Nat.not_le.mp hle2)
          obtain ⟨er, herin, heridx, herterm⟩ := maxIndex_non_empty hesne
          rcases List.mem_append.mp hemin with hem_esx | hem_ll
          · have hemgt : maxIndex ll < em.eIndex :=
              sorted_app_in_1 hsortrm (hposrm em hemin) hem_esx
            rw [hsplit] at herin
            rcases List.mem_append.mp herin with her_es' | her_ll'
            · have h1t : er.eTerm = t := hterm' er her_es'
              have hemt : em.eTerm = t := by
                rw [htermx em hem_esx, heterm]
              exact hemne (by rw [hemt, ← herterm, h1t])
            · have hler : er.eIndex ≤ maxIndex ll :=
                maxIndex_is_max hsortll (Prefix_In hpref er her_ll')
              rw [heridx] at hler
              have hcap : em.eIndex ≤ maxIndex ll := by
                rw [hemidx]
                exact hler
              exact absurd hemgt (Nat.not_lt.mpr hcap)
          · have hemle : em.eIndex ≤ maxIndex ll :=
              maxIndex_is_max hsortll hem_ll
            rw [hemidx] at hemle
            have hergt : pli < er.eIndex := hcontig_es.2 er herin
            rw [heridx] at hergt
            rcases hdisj with ⟨-, hgt⟩ |
              ⟨e2, he2ll, he2idx, -, hsane⟩ | ⟨-, -, hll'll⟩
            · exact Nat.lt_irrefl pli
                (Nat.lt_trans (Nat.lt_of_lt_of_le hergt hemle) hgt)
            · rcases hsane with hll'ne | hplimax
              · have hmeq : maxIndex ll' = maxIndex ll :=
                  Prefix_maxIndex_eq hpref hll'ne
                obtain ⟨hd', hhd'in, hhd'idx, -⟩ :=
                  maxIndex_non_empty hll'ne
                have hhd'es : hd' ∈ es := by
                  rw [hsplit]
                  exact List.mem_append.mpr (Or.inr hhd'in)
                have hhd'le : hd'.eIndex ≤ maxIndex es :=
                  maxIndex_is_max hsortes hhd'es
                rw [hhd'idx, hmeq] at hhd'le
                have hmeq2 : maxIndex es = maxIndex ll :=
                  Nat.le_antisymm hemle hhd'le
                have hhd'll : hd' ∈ ll := Prefix_In hpref hd' hhd'in
                have hemeq : em = hd' := by
                  refine uniqueIndices_elim_eq
                    (sorted_uniqueIndices hsortll) hem_ll hhd'll ?_
                  rw [hemidx, hmeq2, hhd'idx, hmeq]
                have hemes : em ∈ es := hemeq.symm ▸ hhd'es
                have hereq : er = em := by
                  refine uniqueIndices_elim_eq
                    (sorted_uniqueIndices hsortes) herin hemes ?_
                  rw [heridx, hemidx]
                exact hemne (by rw [← hereq, herterm])
              · rw [hplimax] at hergt
                exact absurd hergt (Nat.not_lt.mpr hemle)
            · have hemes : em ∈ es := by
                rw [hsplit]
                exact List.mem_append.mpr (Or.inr (hll'll.symm ▸ hem_ll))
              have hereq : er = em := by
                refine uniqueIndices_elim_eq
                  (sorted_uniqueIndices hsortes) herin hemes ?_
                rw [heridx, hemidx]
              exact hemne (by rw [← hereq, herterm])
    obtain ⟨e', he'idx, he'es⟩ := hcontig_es.1 e.eIndex ⟨hpli_lt, heIle⟩
    have he'term : e'.eTerm = e.eTerm := by
      rw [hsplit] at he'es
      rcases List.mem_append.mp he'es with h' | h'
      · rw [hterm' e' h', heterm]
      · exfalso
        have hcap := maxIndex_is_max hsortll (Prefix_In hpref e' h')
        rw [he'idx] at hcap
        exact absurd hgtll (Nat.not_lt.mpr hcap)
    have he'es2 : e' ∈ es := by
      rw [hsplit] at he'es ⊢
      exact he'es
    have he'L : e' ∈ (net.nwState w).2.log :=
      entries_match_nw_host_invariant net hreach p t n0 pli plt es ci w
        e' e e' hpin hbody he'es2 heL he'idx he'term he'es2
        (Nat.le_refl _)
    have hfin : e' = e :=
      uniqueIndices_elim_eq (sorted_uniqueIndices hsortL) he'L heL he'idx
    exact hfin ▸ hclose e' he'es2

/-- `AllEntriesLogProof.v:267-820` (`allEntries_log_append_entries`):
an old record's log-witness may be destroyed by the splice — the
replacement witness is the packet's own `append_entries_leaderLogs`
snapshot at term `t` (with `t0 < t` by term sanity, or the containment
lemmas forcing the entry back into the new log when `t0 = t`); old
snapshot-witnesses transport along the ct/leaderId movement; new
records are in the new log or nothing was new. -/
theorem allEntries_log_appendEntries :
    refined_raft_net_invariant_append_entries (P := P) allEntries_log := by
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
  intro t0 e h0 hin
  replace hin : (t0, e) ∈ (st' h0).1.allEntries := hin
  show e ∈ (st' h0).2.log ∨
    ∃ (t' : term) (leader : name (P := P)) (ll : List (entry (P := P))),
      (t', ll) ∈ (st' leader).1.leaderLogs ∧ t0 < t' ∧
      t' ≤ (st' h0).2.currentTerm ∧ e ∉ ll ∧
      ((st' h0).2.leaderId ≠ none ∨ t' < (st' h0).2.currentTerm)
  by_cases heq0 : h0 = p.pDst
  case neg =>
    have hst2 : st' h0 = net.nwState h0 := by
      rw [hst h0, update_neq _ _ heq0]
    rw [hst2] at hin ⊢
    rcases hP t0 e h0 hin with hL |
      ⟨t', leader, ll, hmem, hlt, hle, hnin, hlast⟩
    · exact Or.inl hL
    · exact Or.inr ⟨t', leader, ll, hreloc _ _ _ hmem, hlt, hle, hnin,
        hlast⟩
  case pos =>
    subst heq0
    have hst2 : st' p.pDst = (gd, d) := by
      rw [hst p.pDst, update_same]
    rw [hst2] at hin ⊢
    replace hin : (t0, e) ∈ gd.allEntries := hin
    subst hgd
    obtain ⟨hctle, hlidmove⟩ := handleAppendEntries_currentTerm_leaderId
      p.pDst (net.nwState p.pDst).2 t n0 pli plt es ci hae
    rcases update_elections_data_appendEntries_allEntries_mem p.pDst
      (net.nwState p.pDst) t n0 pli plt es ci hae hin with hold | hnewlog |
      ⟨hees, hnf, hlogsame⟩
    · -- OLD record
      rcases hP t0 e p.pDst hold with hL |
        ⟨t', leader, ll0, hmem0, hlt0, hle0, hnin0, hlast0⟩
      · -- its log-witness: survives, or the packet snapshot replaces it
        by_cases hind : e ∈ d.log
        · exact Or.inl hind
        · right
          rcases handleAppendEntries_accept_detail p.pDst (net.nwState p.pDst).2
            t n0 pli plt es ci hae with hsame |
            ⟨hlid, hctd, hnewE, hshape⟩
          · exact absurd (hsame.symm ▸ hL) hind
          · obtain ⟨h1, ll, es', ll', hsplit, hterm', hmem, hpref,
              hdisj⟩ := append_entries_leaderLogs_invariant net hreach p
              t n0 pli plt es ci hpin hbody
            have hts : t0 ≤ (net.nwState p.pDst).2.currentTerm :=
              allEntries_term_sanity_invariant net hreach t0 e p.pDst hold
            rcases Nat.lt_trichotomy t0 t with hlt | heqt | hgt
            · refine ⟨t, h1, ll, hreloc _ _ _ hmem, hlt,
                Nat.le_of_eq hctd.symm, ?_, Or.inl hlid⟩
              intro hell
              exact hind (ae_snapshot_in_newlog hreach hpin hbody hshape
                hsplit hmem hpref hdisj hell hL)
            · exfalso
              rcases allEntries_leaderLogs_term_invariant net hreach t0
                e p.pDst hold with heterm | ⟨ll0', leader0, hmem0', hell0⟩
              · exact hind (ae_own_term_in_newlog hreach hpin hbody
                  hnewE hshape hsplit hterm' hmem hpref hdisj hL
                  (by rw [← heterm, heqt]))
              · have hid0 : ll0' = ll := by
                  refine one_leaderLog_per_term_log_invariant net hreach
                    leader0 h1 t ll0' ll ?_ hmem
                  rw [← heqt]
                  exact hmem0'
                rw [hid0] at hell0
                exact hind (ae_snapshot_in_newlog hreach hpin hbody
                  hshape hsplit hmem hpref hdisj hell0 hL)
            · exact absurd (Nat.le_trans hts (hctd ▸ hctle))
                (Nat.not_le.mpr hgt)
      · -- old snapshot-witness: transport
        right
        refine ⟨t', leader, ll0, hreloc _ _ _ hmem0, hlt0,
          Nat.le_trans hle0 hctle, hnin0, ?_⟩
        rcases hlidmove with hltct | hsameid | hnn
        · exact Or.inr (Nat.lt_of_le_of_lt hle0 hltct)
        · rcases hlast0 with hx | hx
          · left
            rw [hsameid]
            exact hx
          · exact Or.inr (Nat.lt_of_lt_of_le hx hctle)
        · exact Or.inl hnn
    · exact Or.inl hnewlog
    · left
      have hL := appendEntries_haveNewEntries_false net hreach p t n0
        pli plt es ci p.pDst e hpin hbody hnf hees
      show e ∈ d.log
      rw [hlogsame]
      exact hL

/-- `AllEntriesLogProof.v:1067-1084` (`allEntries_log_invariant`). -/
theorem allEntries_log_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      allEntries_log net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro t e h hin
    exact nomatch hin
  · -- client_request: the fresh record is the fresh log head; old
    -- records ride the grown log
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst hps
    obtain ⟨hcteq, hlideq⟩ := handleClientRequest_currentTerm_leaderId h
      (net.nwState h).2 client id c hcr
    have hgrow : ∀ (t2 : term) (ll : List (entry (P := P))),
        (t2, ll) ∈ (net.nwState h).1.leaderLogs →
        (t2, ll) ∈ gd.leaderLogs := by
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
    have hsub : ∀ x, x ∈ (net.nwState h).2.log → x ∈ d.log := by
      intro x hx
      rcases handleClientRequest_log_full h (net.nwState h).2 client id c
        hcr with ⟨-, hlogd⟩ | ⟨-, heqd⟩
      · rw [hlogd]
        exact List.mem_cons_of_mem _ hx
      · rw [heqd]
        exact hx
    intro t0 e h0 hin
    replace hin : (t0, e) ∈ (st' h0).1.allEntries := hin
    show e ∈ (st' h0).2.log ∨
      ∃ (t' : term) (leader : name (P := P)) (ll : List (entry (P := P))),
        (t', ll) ∈ (st' leader).1.leaderLogs ∧ t0 < t' ∧
        t' ≤ (st' h0).2.currentTerm ∧ e ∉ ll ∧
        ((st' h0).2.leaderId ≠ none ∨ t' < (st' h0).2.currentTerm)
    by_cases heq0 : h0 = h
    case neg =>
      have hst2 : st' h0 = net.nwState h0 := by
        rw [hst h0, update_neq _ _ heq0]
      rw [hst2] at hin ⊢
      rcases hP t0 e h0 hin with hL |
        ⟨t', leader, ll, hmem, hlt, hle, hnin, hlast⟩
      · exact Or.inl hL
      · exact Or.inr ⟨t', leader, ll, hreloc _ _ _ hmem, hlt, hle, hnin,
          hlast⟩
    case pos =>
      subst heq0
      have hst2 : st' h0 = (gd, d) := by
        rw [hst h0, update_same]
      rw [hst2] at hin ⊢
      replace hin : (t0, e) ∈ gd.allEntries := hin
      subst hgd
      rcases update_elections_data_client_request_allEntries_mem h0
        (net.nwState h0) client id c hcr hin with hold | hnew
      · rcases hP t0 e h0 hold with hL |
          ⟨t', leader, ll, hmem, hlt, hle, hnin, hlast⟩
        · exact Or.inl (hsub e hL)
        · right
          refine ⟨t', leader, ll, hreloc _ _ _ hmem, hlt, ?_, hnin, ?_⟩
          · show t' ≤ d.currentTerm
            rw [hcteq]
            exact hle
          · show d.leaderId ≠ none ∨ t' < d.currentTerm
            rw [hcteq, hlideq]
            exact hlast
      · exact Or.inl hnew
  · -- timeout
    intro net h st' ps' gd out d l hto hgd hP _hreach hst hps
    obtain ⟨hlog, -, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
    refine allEntries_log_of_update hP hst ?_ ?_ hlog ?_
    · intro t2 ll hin
      subst hgd
      rw [(update_elections_data_timeout_ghost h (net.nwState h)).1]
      exact hin
    · subst hgd
      exact (update_elections_data_timeout_ghost h (net.nwState h)).2
    · exact handleTimeout_currentTerm_leaderId h (net.nwState h).2 hto
  · exact allEntries_log_appendEntries
  · -- append_entries_reply
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP _hreach
      hpkts hst hps
    refine allEntries_log_of_update hP hst ?_ ?_ ?_ ?_
    · intro t2 ll hin
      rw [hgd]
      exact hin
    · rw [hgd]
    · exact handleAppendEntriesReply_log p.pDst (net.nwState p.pDst).2
        p.pSrc t es res haer
    · exact handleAppendEntriesReply_currentTerm_leaderId p.pDst
        (net.nwState p.pDst).2 p.pSrc t es res haer
  · -- request_vote
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP
      _hreach hpkts hst hps
    refine allEntries_log_of_update hP hst ?_ ?_ ?_ ?_
    · intro t2 ll hin
      subst hgd
      rw [(update_elections_data_requestVote_cronies p.pDst p.pSrc t
        p.pSrc lli llt (net.nwState p.pDst)).2.1]
      exact hin
    · subst hgd
      exact (update_elections_data_requestVote_cronies p.pDst p.pSrc t
        p.pSrc lli llt (net.nwState p.pDst)).2.2
    · exact handleRequestVote_log p.pDst (net.nwState p.pDst).2 t p.pSrc
        lli llt hrv
    · exact handleRequestVote_currentTerm_leaderId p.pDst
        (net.nwState p.pDst).2 t p.pSrc lli llt hrv
  · -- request_vote_reply
    intro xs p ys net st' ps' gd d t v hrvr hgd _hbody hP _hreach hpkts
      hst hps
    refine allEntries_log_of_update hP hst ?_ ?_ ?_ ?_
    · intro t2 ll hin
      subst hgd
      exact update_elections_data_requestVoteReply_leaderLogs_old p.pDst
        p.pSrc t v (net.nwState p.pDst) hin
    · subst hgd
      exact (update_elections_data_requestVoteReply_votes p.pDst p.pSrc
        t v (net.nwState p.pDst)).2.2
    · rw [← hrvr]
      exact handleRequestVoteReply_log p.pDst (net.nwState p.pDst).2
        p.pSrc t v
    · rw [← hrvr]
      exact handleRequestVoteReply_currentTerm_leaderId p.pDst
        (net.nwState p.pDst).2 p.pSrc t v
  · -- do_leader
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst hps
    obtain ⟨hcteq, hlideq⟩ := doLeader_currentTerm_leaderId d h hdl
    obtain ⟨-, -, -, -, hdlog, -⟩ := doLeader_spec d h hdl
    refine allEntries_log_of_update hP hst ?_ ?_ ?_ ?_
    · intro t2 ll hin
      rw [hstate] at hin
      exact hin
    · rw [hstate]
    · rw [hdlog, hstate]
    · right
      rw [hstate]
      exact ⟨hcteq, hlideq⟩
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps
    obtain ⟨hcteq, hlideq⟩ := doGenericServer_currentTerm_leaderId h d hgs
    obtain ⟨hlog, -, -, -, -, -⟩ := doGenericServer_spec h d hgs
    refine allEntries_log_of_update hP hst ?_ ?_ ?_ ?_
    · intro t2 ll hin
      rw [hstate] at hin
      exact hin
    · rw [hstate]
    · rw [hlog, hstate]
    · right
      rw [hstate]
      exact ⟨hcteq, hlideq⟩
  · -- state_same_packet_subset
    intro net net' hstates hsub hP _hreach t e h hin
    replace hin : (t, e) ∈ (net'.nwState h).1.allEntries := hin
    rw [← hstates h] at hin
    show e ∈ (net'.nwState h).2.log ∨
      ∃ (t' : term) (leader : name (P := P)) (ll : List (entry (P := P))),
        (t', ll) ∈ (net'.nwState leader).1.leaderLogs ∧ t < t' ∧
        t' ≤ (net'.nwState h).2.currentTerm ∧ e ∉ ll ∧
        ((net'.nwState h).2.leaderId ≠ none ∨
         t' < (net'.nwState h).2.currentTerm)
    rw [← hstates h]
    rcases hP t e h hin with hL |
      ⟨t', leader, ll, hmem, hlt, hle, hnin, hlast⟩
    · exact Or.inl hL
    · rw [hstates leader] at hmem
      exact Or.inr ⟨t', leader, ll, hmem, hlt, hle, hnin, hlast⟩
  · -- reboot
    intro net net' gd d h d' hrb hP _hreach hstate hst hpkts
    refine allEntries_log_of_update hP hst ?_ ?_ ?_ ?_
    · intro t2 ll hin
      rw [hstate] at hin
      exact hin
    · rw [hstate]
    · rw [← hrb, hstate]
      rfl
    · right
      rw [← hrb, hstate]
      exact ⟨rfl, rfl⟩

/-! ## allEntries_votesWithLog (GAP-7a,
`AllEntriesVotesWithLogInterface.v:10-19`) -/

/-- `AllEntriesVotesWithLogInterface.v:10-19`
(`allEntries_votesWithLog`): a recorded entry from before a recorded
vote is in the vote's log, or some intermediate election's snapshot
excludes it. -/
def allEntries_votesWithLog (net : RefinedNet) : Prop :=
  ∀ (t : term) (e : entry (P := P)) (t' : term) (leader : name (P := P))
    (h : name (P := P)) (llog : List (entry (P := P))),
    (t, e) ∈ (net.nwState h).1.allEntries →
    (t', leader, llog) ∈ (net.nwState h).1.votesWithLog →
    t < t' →
    e ∈ llog ∨
    ∃ (t'' : term) (leader' : name (P := P))
      (log' : List (entry (P := P))),
      (t'', log') ∈ (net.nwState leader').1.leaderLogs ∧
      t < t'' ∧ t'' < t' ∧ e ∉ log'

/-- Transport for `allEntries_votesWithLog` across ghost-preserving
steps. -/
theorem allEntries_votesWithLog_of_update {net net' : RefinedNet}
    {u : name (P := P)} {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hP : allEntries_votesWithLog net)
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hgrow : ∀ (t : term) (ll : List (entry (P := P))),
      (t, ll) ∈ (net.nwState u).1.leaderLogs → (t, ll) ∈ gd.leaderLogs)
    (hae : gd.allEntries = (net.nwState u).1.allEntries)
    (hvwl : gd.votesWithLog = (net.nwState u).1.votesWithLog) :
    allEntries_votesWithLog net' := by
  intro t e t' leader h llog hin hvin hlt
  replace hin : (t, e) ∈ (net'.nwState h).1.allEntries := hin
  replace hvin : (t', leader, llog) ∈ (net'.nwState h).1.votesWithLog :=
    hvin
  have hred : (t, e) ∈ (net.nwState h).1.allEntries ∧
      (t', leader, llog) ∈ (net.nwState h).1.votesWithLog := by
    rw [hst h] at hin hvin
    by_cases heq : h = u
    · subst heq
      rw [update_same] at hin hvin
      replace hin : (t, e) ∈ gd.allEntries := hin
      replace hvin : (t', leader, llog) ∈ gd.votesWithLog := hvin
      rw [hae] at hin
      rw [hvwl] at hvin
      exact ⟨hin, hvin⟩
    · rw [update_neq _ _ heq] at hin hvin
      exact ⟨hin, hvin⟩
  rcases hP t e t' leader h llog hred.1 hred.2 hlt with hL |
    ⟨t'', leader', log', hmem, h1, h2, h3⟩
  · exact Or.inl hL
  · refine Or.inr ⟨t'', leader', log', ?_, h1, h2, h3⟩
    rw [hst leader']
    by_cases heql : leader' = u
    · subst heql
      rw [update_same]
      exact hgrow _ _ hmem
    · rw [update_neq _ _ heql]
      exact hmem

omit O in
/-- A TRUE AppendEntries reply's term dominates the old current term. -/
theorem handleAppendEntries_true_reply_ge (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (lid : name (P := P))
    (pli : logIndex) (plt : term) (es : List (entry (P := P)))
    (ci : logIndex) {d : raft_data (P := P)} {t' : term}
    {es' : List (entry (P := P))}
    (h : handleAppendEntries me st t lid pli plt es ci
      = (d, .AppendEntriesReply t' es' true)) :
    st.currentTerm ≤ t' := by
  unfold handleAppendEntries at h
  split at h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨-, hm⟩ := h
    injection hm with f1 f2 f3
    exact nomatch f3
  · rename_i hng
    have hle : st.currentTerm ≤ t :=
      Nat.not_lt.mp (fun hlt => hng (by simpa [Nat.blt_eq] using hlt))
    repeat' split at h
    all_goals simp only [Prod.mk.injEq] at h
    all_goals obtain ⟨-, hm⟩ := h
    all_goals injection hm with f1 f2 f3
    all_goals first
      | (rw [← f1]
         exact hle)
      | exact nomatch f3

omit O in
/-- `AllEntriesVotesWithLogProof.v:22-33`
(`update_elections_data_appendEntries_allEntries'`). -/
theorem update_elections_data_appendEntries_allEntries_ge
    (me : name (P := P)) (st : electionsData (P := P) × raft_data (P := P))
    (t : term) (lid : name (P := P)) (pli : logIndex) (plt : term)
    (es : List (entry (P := P))) (ci : logIndex) {d m}
    (hae : handleAppendEntries me st.2 t lid pli plt es ci = (d, m))
    {te : term} {e : entry (P := P)}
    (hin : (te, e) ∈ (update_elections_data_appendEntries me st t lid
      pli plt es ci).allEntries) :
    (te, e) ∈ st.1.allEntries ∨ st.2.currentTerm ≤ te := by
  obtain ⟨t'', r'', rfl⟩ :=
    handleAppendEntries_reply_entries me st.2 t lid pli plt es ci hae
  unfold update_elections_data_appendEntries at hin
  rw [hae] at hin
  cases r''
  · exact Or.inl hin
  · simp only [] at hin
    replace hin : (te, e) ∈ (es.map fun e => (t'', e)) ++ st.1.allEntries :=
      hin
    rcases List.mem_append.mp hin with hmap | hold
    · obtain ⟨e2, he2, heq2⟩ := List.mem_map.mp hmap
      injection heq2 with h1 h2
      right
      rw [← h1]
      exact handleAppendEntries_true_reply_ge me st.2 t lid pli plt es
        ci hae
    · exact Or.inl hold

omit O in
/-- A RequestVote that changes the (term, votedFor) pair either advanced
the term or had no known leader (the guard behind the fresh vote
record's fine print — upstream `handleRequestVote_currentTerm_leaderId'`,
`AllEntriesVotesWithLogProof.v:84-94`). -/
theorem handleRequestVote_vote_change (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (cand : name (P := P))
    (lli : logIndex) (llt : term) {st' m}
    (h : handleRequestVote me st t cand lli llt = (st', m))
    (hchange : ¬ (st'.currentTerm = st.currentTerm ∧
      st'.votedFor = st.votedFor)) :
    st.currentTerm < st'.currentTerm ∨ st.leaderId = none := by
  have hadv := advanceCurrentTerm_currentTerm_leaderId st t
  have hspec := advanceCurrentTerm_spec st t
  unfold handleRequestVote at h
  simp only [] at h
  split at h
  · -- reject: state unchanged
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact absurd ⟨rfl, rfl⟩ hchange
  · split at h
    · rename_i hguard
      rw [Bool.and_eq_true] at hguard
      obtain ⟨hiso, -⟩ := hguard
      rw [Option.isNone_iff_eq_none] at hiso
      split at h
      · -- fresh grant: no known leader post-advance
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rcases hadv with hlt | ⟨-, hlid2⟩
        · exact Or.inl hlt
        · right
          rw [← hlid2]
          exact hiso
      · -- standing vote: state is the advanced state
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rcases hspec.2.2 with ⟨hct, hvf, -⟩ | ⟨hlt, -, -⟩
        · exact absurd ⟨hct, hvf⟩ hchange
        · exact Or.inl hlt
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rcases hspec.2.2 with ⟨hct, hvf, -⟩ | ⟨hlt, -, -⟩
      · exact absurd ⟨hct, hvf⟩ hchange
      · exact Or.inl hlt

omit O in
/-- The RV `votesWithLog` elimination WITH the fresh record's fine
print (`AllEntriesVotesWithLogProof.v:106-128`,
`votesWithLog_update_elections_data_request_vote`). -/
theorem update_elections_data_requestVote_votesWithLog_elim_fine
    {me src : name (P := P)} {t : term} {cand : name (P := P)}
    {lli : logIndex} {llt : term}
    {st : electionsData (P := P) × raft_data (P := P)} {st' m}
    (h : handleRequestVote me st.2 t cand lli llt = (st', m))
    {t' : term} {h' : name (P := P)} {vl : List (entry (P := P))}
    (hin : (t', h', vl) ∈ (update_elections_data_requestVote me src t
      cand lli llt st).votesWithLog) :
    (t', h', vl) ∈ st.1.votesWithLog ∨
    (t' = st'.currentTerm ∧ vl = st'.log ∧
     (st.2.currentTerm < st'.currentTerm ∨ st.2.leaderId = none)) := by
  unfold update_elections_data_requestVote at hin
  rw [h] at hin
  simp only [] at hin
  split at hin
  · -- none → some: votedFor changed
    rename_i hvfold hvfnew
    rcases List.mem_cons.mp hin with heq | hin
    · injection heq with h1 h2
      injection h2 with h2 h3
      refine Or.inr ⟨h1, h3, ?_⟩
      refine handleRequestVote_vote_change me st.2 t cand lli llt h ?_
      intro hc
      rw [hc.2, hvfold] at hvfnew
      exact nomatch hvfnew
    · exact Or.inl hin
  · -- some → some
    rename_i cid cid' hvfold hvfnew
    split at hin
    · exact Or.inl hin
    · rename_i hguard
      rcases List.mem_cons.mp hin with heq | hin
      · injection heq with h1 h2
        injection h2 with h2 h3
        refine Or.inr ⟨h1, h3, ?_⟩
        refine handleRequestVote_vote_change me st.2 t cand lli llt h ?_
        intro hc
        apply hguard
        rw [Bool.and_eq_true]
        constructor
        · exact beq_iff_eq.mpr hc.1.symm
        · rw [hc.2, hvfold] at hvfnew
          injection hvfnew with hcid
          exact decide_eq_true hcid
      · exact Or.inl hin
  · -- votedFor cleared: no record added
    exact Or.inl hin

/-- `AllEntriesVotesWithLogProof.v:333-351`
(`allEntries_votesWithLog_invariant`, GAP-7a): the fresh-vote cases are
`allEntries_log`'s payoff — the vote snapshots the voter's own log, so
a recorded entry is in it or an intermediate leaderLog excludes it,
with the vote's term above that snapshot's by the grant fine print. -/
theorem allEntries_votesWithLog_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      allEntries_votesWithLog net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro t e t' leader h llog hin _ _
    exact nomatch hin
  · -- client_request: a fresh record is at the recorder's own current
    -- term, above every recorded vote — vacuous by term sanity
    intro h net st' ps' gd out d l client id c hcr hgd hP hreach hst hps
    obtain ⟨hcteq, -⟩ := handleClientRequest_currentTerm_leaderId h
      (net.nwState h).2 client id c hcr
    have hgrow : ∀ (t2 : term) (ll : List (entry (P := P))),
        (t2, ll) ∈ (net.nwState h).1.leaderLogs →
        (t2, ll) ∈ gd.leaderLogs := by
      intro t2 ll hin
      subst hgd
      rw [(update_elections_data_client_request_ghost h (net.nwState h)
        client id c).2.2.2]
      exact hin
    intro t0 e t' leader h0 llog hin hvin hlt
    replace hin : (t0, e) ∈ (st' h0).1.allEntries := hin
    replace hvin : (t', leader, llog) ∈ (st' h0).1.votesWithLog := hvin
    have hreloc : ∀ (t2 : term) (ll : List (entry (P := P)))
        (x : name (P := P)),
        (t2, ll) ∈ (net.nwState x).1.leaderLogs →
        (t2, ll) ∈ (st' x).1.leaderLogs := by
      intro t2 ll x hin2
      rw [hst x]
      by_cases heq : x = h
      · subst heq
        rw [update_same]
        exact hgrow _ _ hin2
      · rw [update_neq _ _ heq]
        exact hin2
    by_cases heq0 : h0 = h
    case neg =>
      have hst2 : st' h0 = net.nwState h0 := by
        rw [hst h0, update_neq _ _ heq0]
      rw [hst2] at hin hvin
      rcases hP t0 e t' leader h0 llog hin hvin hlt with hL |
        ⟨t'', leader', log', hmem, h1, h2, h3⟩
      · exact Or.inl hL
      · exact Or.inr ⟨t'', leader', log', hreloc _ _ _ hmem, h1, h2, h3⟩
    case pos =>
      subst heq0
      have hst2 : st' h0 = (gd, d) := by
        rw [hst h0, update_same]
      rw [hst2] at hin hvin
      replace hin : (t0, e) ∈ gd.allEntries := hin
      replace hvin : (t', leader, llog) ∈ gd.votesWithLog := hvin
      subst hgd
      rw [(update_elections_data_client_request_ghost h0 (net.nwState h0)
        client id c).2.1] at hvin
      rcases update_elections_data_client_request_allEntries_head_term
        h0 (net.nwState h0) client id c hcr with hsame | ⟨enew, -, hcons, -, -, -⟩
      · rw [hsame] at hin
        rcases hP t0 e t' leader h0 llog hin hvin hlt with hL |
          ⟨t'', leader', log', hmem, h1, h2, h3⟩
        · exact Or.inl hL
        · exact Or.inr ⟨t'', leader', log', hreloc _ _ _ hmem, h1, h2,
            h3⟩
      · rw [hcons] at hin
        rcases List.mem_cons.mp hin with heqp | hin
        · -- fresh record at the recorder's current term: no recorded
          -- vote can be above it
          exfalso
          injection heqp with h1 h2
          have hts := votesWithLog_term_sanity_invariant net hreach t'
            leader llog h0 hvin
          rw [h1, hcteq] at hlt
          exact absurd hts (Nat.not_le.mpr hlt)
        · rcases hP t0 e t' leader h0 llog hin hvin hlt with hL |
            ⟨t'', leader', log', hmem, h1, h2, h3⟩
          · exact Or.inl hL
          · exact Or.inr ⟨t'', leader', log', hreloc _ _ _ hmem, h1, h2,
              h3⟩
  · -- timeout: allEntries_log's payoff at the candidacy's self-record
    intro net h st' ps' gd out d l hto hgd hP hreach hst hps
    obtain ⟨hlog, -, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
    have hgrow : ∀ (t2 : term) (ll : List (entry (P := P))),
        (t2, ll) ∈ (net.nwState h).1.leaderLogs →
        (t2, ll) ∈ gd.leaderLogs := by
      intro t2 ll hin
      subst hgd
      rw [(update_elections_data_timeout_ghost h (net.nwState h)).1]
      exact hin
    intro t0 e t' leader h0 llog hin hvin hlt
    replace hin : (t0, e) ∈ (st' h0).1.allEntries := hin
    replace hvin : (t', leader, llog) ∈ (st' h0).1.votesWithLog := hvin
    have hreloc : ∀ (t2 : term) (ll : List (entry (P := P)))
        (x : name (P := P)),
        (t2, ll) ∈ (net.nwState x).1.leaderLogs →
        (t2, ll) ∈ (st' x).1.leaderLogs := by
      intro t2 ll x hin2
      rw [hst x]
      by_cases heq : x = h
      · subst heq
        rw [update_same]
        exact hgrow _ _ hin2
      · rw [update_neq _ _ heq]
        exact hin2
    by_cases heq0 : h0 = h
    case neg =>
      have hst2 : st' h0 = net.nwState h0 := by
        rw [hst h0, update_neq _ _ heq0]
      rw [hst2] at hin hvin
      rcases hP t0 e t' leader h0 llog hin hvin hlt with hL |
        ⟨t'', leader', log', hmem, h1, h2, h3⟩
      · exact Or.inl hL
      · exact Or.inr ⟨t'', leader', log', hreloc _ _ _ hmem, h1, h2, h3⟩
    case pos =>
      subst heq0
      have hst2 : st' h0 = (gd, d) := by
        rw [hst h0, update_same]
      rw [hst2] at hin hvin
      replace hin : (t0, e) ∈ gd.allEntries := hin
      replace hvin : (t', leader, llog) ∈ gd.votesWithLog := hvin
      subst hgd
      rw [(update_elections_data_timeout_ghost h0 (net.nwState h0)).2]
        at hin
      rcases update_elections_data_timeout_votesWithLog_votesReceived
        hto with ⟨-, hvwl, -⟩ | ⟨-, hvwl, hctgrow⟩
      · rw [hvwl] at hvin
        rcases hP t0 e t' leader h0 llog hin hvin hlt with hL |
          ⟨t'', leader', log', hmem, h1, h2, h3⟩
        · exact Or.inl hL
        · exact Or.inr ⟨t'', leader', log', hreloc _ _ _ hmem, h1, h2,
            h3⟩
      · rw [hvwl] at hvin
        rcases List.mem_cons.mp hvin with heqv | hvin
        · -- the candidacy's self-record snapshots the (unchanged) log
          injection heqv with h1 h2
          injection h2 with h2 h3
          rcases allEntries_log_invariant net hreach t0 e h0 hin with
            hL | ⟨t'', leader', ll, hmem, hlt2, hle2, hnin, -⟩
          · left
            rw [h3, hlog]
            exact hL
          · refine Or.inr ⟨t'', leader', ll, hreloc _ _ _ hmem, hlt2,
              ?_, hnin⟩
            rw [h1, hctgrow]
            exact Nat.lt_succ_of_le hle2
        · rcases hP t0 e t' leader h0 llog hin hvin hlt with hL |
            ⟨t'', leader', log', hmem, h1, h2, h3⟩
          · exact Or.inl hL
          · exact Or.inr ⟨t'', leader', log', hreloc _ _ _ hmem, h1, h2,
              h3⟩
  · -- append_entries: fresh records are at/above the old current term,
    -- above every recorded vote
    intro xs p ys net st' ps' gd d m t n0 pli plt es ci hae hgd hbody hP
      hreach hpkts hst hps
    have hgrow : ∀ (t2 : term) (ll : List (entry (P := P))),
        (t2, ll) ∈ (net.nwState p.pDst).1.leaderLogs →
        (t2, ll) ∈ gd.leaderLogs := by
      intro t2 ll hin
      subst hgd
      rw [(update_elections_data_appendEntries_ghost p.pDst
        (net.nwState p.pDst) t n0 pli plt es ci).2.2.2]
      exact hin
    intro t0 e t' leader h0 llog hin hvin hlt
    replace hin : (t0, e) ∈ (st' h0).1.allEntries := hin
    replace hvin : (t', leader, llog) ∈ (st' h0).1.votesWithLog := hvin
    have hreloc : ∀ (t2 : term) (ll : List (entry (P := P)))
        (x : name (P := P)),
        (t2, ll) ∈ (net.nwState x).1.leaderLogs →
        (t2, ll) ∈ (st' x).1.leaderLogs := by
      intro t2 ll x hin2
      rw [hst x]
      by_cases heq : x = p.pDst
      · subst heq
        rw [update_same]
        exact hgrow _ _ hin2
      · rw [update_neq _ _ heq]
        exact hin2
    by_cases heq0 : h0 = p.pDst
    case neg =>
      have hst2 : st' h0 = net.nwState h0 := by
        rw [hst h0, update_neq _ _ heq0]
      rw [hst2] at hin hvin
      rcases hP t0 e t' leader h0 llog hin hvin hlt with hL |
        ⟨t'', leader', log', hmem, h1, h2, h3⟩
      · exact Or.inl hL
      · exact Or.inr ⟨t'', leader', log', hreloc _ _ _ hmem, h1, h2, h3⟩
    case pos =>
      subst heq0
      have hst2 : st' p.pDst = (gd, d) := by
        rw [hst p.pDst, update_same]
      rw [hst2] at hin hvin
      replace hin : (t0, e) ∈ gd.allEntries := hin
      replace hvin : (t', leader, llog) ∈ gd.votesWithLog := hvin
      subst hgd
      rw [(update_elections_data_appendEntries_ghost p.pDst
        (net.nwState p.pDst) t n0 pli plt es ci).2.1] at hvin
      rcases update_elections_data_appendEntries_allEntries_ge p.pDst
        (net.nwState p.pDst) t n0 pli plt es ci hae hin with hold | hge
      · rcases hP t0 e t' leader p.pDst llog hold hvin hlt with hL |
          ⟨t'', leader', log', hmem, h1, h2, h3⟩
        · exact Or.inl hL
        · exact Or.inr ⟨t'', leader', log', hreloc _ _ _ hmem, h1, h2,
            h3⟩
      · exfalso
        have hts := votesWithLog_term_sanity_invariant net hreach t'
          leader llog p.pDst hvin
        exact Nat.lt_irrefl t0
          (Nat.lt_of_lt_of_le hlt (Nat.le_trans hts hge))
  · -- append_entries_reply: ghost untouched
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP _hreach
      hpkts hst hps
    refine allEntries_votesWithLog_of_update hP hst ?_ ?_ ?_
    · intro t2 ll hin
      rw [hgd]
      exact hin
    · rw [hgd]
    · rw [hgd]
  · -- request_vote: allEntries_log's payoff at the fresh grant
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP
      hreach hpkts hst hps
    have hgrow : ∀ (t2 : term) (ll : List (entry (P := P))),
        (t2, ll) ∈ (net.nwState p.pDst).1.leaderLogs →
        (t2, ll) ∈ gd.leaderLogs := by
      intro t2 ll hin
      subst hgd
      rw [(update_elections_data_requestVote_cronies p.pDst p.pSrc t
        p.pSrc lli llt (net.nwState p.pDst)).2.1]
      exact hin
    intro t0 e t' leader h0 llog hin hvin hlt
    replace hin : (t0, e) ∈ (st' h0).1.allEntries := hin
    replace hvin : (t', leader, llog) ∈ (st' h0).1.votesWithLog := hvin
    have hreloc : ∀ (t2 : term) (ll : List (entry (P := P)))
        (x : name (P := P)),
        (t2, ll) ∈ (net.nwState x).1.leaderLogs →
        (t2, ll) ∈ (st' x).1.leaderLogs := by
      intro t2 ll x hin2
      rw [hst x]
      by_cases heq : x = p.pDst
      · subst heq
        rw [update_same]
        exact hgrow _ _ hin2
      · rw [update_neq _ _ heq]
        exact hin2
    by_cases heq0 : h0 = p.pDst
    case neg =>
      have hst2 : st' h0 = net.nwState h0 := by
        rw [hst h0, update_neq _ _ heq0]
      rw [hst2] at hin hvin
      rcases hP t0 e t' leader h0 llog hin hvin hlt with hL |
        ⟨t'', leader', log', hmem, h1, h2, h3⟩
      · exact Or.inl hL
      · exact Or.inr ⟨t'', leader', log', hreloc _ _ _ hmem, h1, h2, h3⟩
    case pos =>
      subst heq0
      have hst2 : st' p.pDst = (gd, d) := by
        rw [hst p.pDst, update_same]
      rw [hst2] at hin hvin
      replace hin : (t0, e) ∈ gd.allEntries := hin
      replace hvin : (t', leader, llog) ∈ gd.votesWithLog := hvin
      subst hgd
      rw [(update_elections_data_requestVote_cronies p.pDst p.pSrc t
        p.pSrc lli llt (net.nwState p.pDst)).2.2] at hin
      rcases update_elections_data_requestVote_votesWithLog_elim_fine
        hrv hvin with hold | ⟨ht', hvl, hfine⟩
      · rcases hP t0 e t' leader p.pDst llog hin hold hlt with hL |
          ⟨t'', leader', log', hmem, h1, h2, h3⟩
        · exact Or.inl hL
        · exact Or.inr ⟨t'', leader', log', hreloc _ _ _ hmem, h1, h2,
            h3⟩
      · -- the fresh grant snapshots the voter's (unchanged) log
        have hloge : d.log = (net.nwState p.pDst).2.log :=
          handleRequestVote_log p.pDst (net.nwState p.pDst).2 t p.pSrc lli llt
            hrv
        have hctmono : (net.nwState p.pDst).2.currentTerm ≤ d.currentTerm := by
          rcases handleRequestVote_currentTerm_leaderId p.pDst
            (net.nwState p.pDst).2 t p.pSrc lli llt hrv with hlt2 |
            ⟨heq2, -⟩
          · exact Nat.le_of_lt hlt2
          · exact Nat.le_of_eq heq2.symm
        rcases allEntries_log_invariant net hreach t0 e p.pDst hin with hL |
          ⟨t'', leader', ll, hmem, hlt2, hle2, hnin, hlast⟩
        · left
          rw [hvl, hloge]
          exact hL
        · refine Or.inr ⟨t'', leader', ll, hreloc _ _ _ hmem, hlt2, ?_,
            hnin⟩
          rw [ht']
          rcases hfine with hgrew | hnolead
          · exact Nat.lt_of_le_of_lt hle2 hgrew
          · rcases hlast with hnn | hlt3
            · exact absurd hnolead hnn
            · exact Nat.lt_of_lt_of_le hlt3 hctmono
  · -- request_vote_reply: ghost votes/votesWithLog/allEntries
    -- untouched; leaderLogs grow
    intro xs p ys net st' ps' gd d t v hrvr hgd _hbody hP _hreach hpkts
      hst hps
    refine allEntries_votesWithLog_of_update hP hst ?_ ?_ ?_
    · intro t2 ll hin
      subst hgd
      exact update_elections_data_requestVoteReply_leaderLogs_old p.pDst
        p.pSrc t v (net.nwState p.pDst) hin
    · subst hgd
      exact (update_elections_data_requestVoteReply_votes p.pDst p.pSrc
        t v (net.nwState p.pDst)).2.2
    · subst hgd
      exact (update_elections_data_requestVoteReply_votes p.pDst p.pSrc
        t v (net.nwState p.pDst)).2.1
  · -- do_leader
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst hps
    refine allEntries_votesWithLog_of_update hP hst ?_ ?_ ?_
    · intro t2 ll hin
      rw [hstate] at hin
      exact hin
    · rw [hstate]
    · rw [hstate]
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps
    refine allEntries_votesWithLog_of_update hP hst ?_ ?_ ?_
    · intro t2 ll hin
      rw [hstate] at hin
      exact hin
    · rw [hstate]
    · rw [hstate]
  · -- state_same_packet_subset
    intro net net' hstates hsub hP _hreach t e t' leader h llog hin hvin
      hlt
    replace hin : (t, e) ∈ (net'.nwState h).1.allEntries := hin
    replace hvin : (t', leader, llog) ∈ (net'.nwState h).1.votesWithLog :=
      hvin
    rw [← hstates h] at hin hvin
    rcases hP t e t' leader h llog hin hvin hlt with hL |
      ⟨t'', leader', log', hmem, h1, h2, h3⟩
    · exact Or.inl hL
    · rw [hstates leader'] at hmem
      exact Or.inr ⟨t'', leader', log', hmem, h1, h2, h3⟩
  · -- reboot
    intro net net' gd d h d' _hrb hP _hreach hstate hst hpkts
    refine allEntries_votesWithLog_of_update hP hst ?_ ?_ ?_
    · intro t2 ll hin
      rw [hstate] at hin
      exact hin
    · rw [hstate]
    · rw [hstate]

end LeaderLogsAssembly
end Raft
end VerdiCompat
