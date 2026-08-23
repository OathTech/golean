import Lean
import VerdiCompat

/-!
# In-build axiom gate for the Verdi compat port — ENFORCING

Upgraded from advisory `#print axioms` lines at the 2026-08-10 merge
window (lane log, queue item 1: the advisory form printed axiom drift
into the build log but the build stayed green — a human-read check).
Both mainline mechanisms from `proofs/Audit.lean` now apply:

- **Curated pins**: `#guard_msgs in #print axioms` per named theorem —
  an acquired axiom (a `sorryAx`, `ofReduceBool`, or a hand-rolled
  `axiom`) changes the message and FAILS the build. To re-baseline
  after an intended change, update the docstring in the same commit
  with the reason.
- **Exhaustive sweep**: every constant declared in a `VerdiCompat.*`
  module (by module of origin, so a new file or an odd namespace is
  still swept) has its transitive axioms collected; anything outside
  the lane's recorded set `{propext, Quot.sound}` FAILS the build via
  `throwError`. Note this is stricter than mainline's classical trio —
  the lane's doctrine is propext/Quot.sound only (lane log, S2-S6);
  widening it is a deliberate, recorded decision, not an edit here.
-/

open VerdiCompat VerdiCompat.Raft

/-- info: 'VerdiCompat.allFin_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms allFin_all
/-- info: 'VerdiCompat.allFin_NoDup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms allFin_NoDup
/-- info: 'VerdiCompat.Raft.reboot_idem' does not depend on any axioms -/
#guard_msgs in #print axioms reboot_idem
/-- info: 'VerdiCompat.Raft.reboot_init_handlers' does not depend on any axioms -/
#guard_msgs in #print axioms reboot_init_handlers
/-- info: 'VerdiCompat.Raft.handleRequestVote_grant_votedFor' depends on axioms: [propext] -/
#guard_msgs in #print axioms handleRequestVote_grant_votedFor
/-- info: 'VerdiCompat.Raft.raft_net_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms raft_net_invariant
/-- info: 'VerdiCompat.Raft.step_failure_star_raft_intermediate_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_failure_star_raft_intermediate_reachable
/-- info: 'VerdiCompat.acknowledge_all_ops_func_correct' depends on axioms: [propext] -/
#guard_msgs in #print axioms VerdiCompat.acknowledge_all_ops_func_correct
/-- info: 'VerdiCompat.IR_equivalent_refl' does not depend on any axioms -/
#guard_msgs in #print axioms VerdiCompat.IR_equivalent_refl
/-- info: 'VerdiCompat.Examples.raft_linearizable_conclusion_witness' depends on axioms: [propext] -/
#guard_msgs in #print axioms VerdiCompat.Examples.raft_linearizable_conclusion_witness

-- Ghost-layer port (campaign Arc 3, RefinedProofStructure.lean): the
-- refined induction principle, the two simulations, the two transfer
-- directions, and the principle's discharge witness.
/-- info: 'VerdiCompat.Raft.refined_raft_net_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.refined_raft_net_invariant
/-- info: 'VerdiCompat.Raft.simulation_1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.simulation_1
/-- info: 'VerdiCompat.Raft.simulation_2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.simulation_2
/-- info: 'VerdiCompat.Raft.lift_prop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.lift_prop
/-- info: 'VerdiCompat.Raft.lower_prop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.lower_prop
/-- info: 'VerdiCompat.Raft.refined_votes_shape_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.refined_votes_shape_witness

-- Election-safety chain (campaign Arc 3 unit 2, ElectionSafety.lean):
-- the five chain invariants and the discharged P1 transfer target.
/-- info: 'VerdiCompat.Raft.votes_le_currentTerm_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.votes_le_currentTerm_invariant
/-- info: 'VerdiCompat.Raft.votes_correct_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.votes_correct_invariant
/-- info: 'VerdiCompat.Raft.candidates_vote_for_selves_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.candidates_vote_for_selves_invariant
/-- info: 'VerdiCompat.Raft.cronies_correct_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.cronies_correct_invariant
/-- info: 'VerdiCompat.Raft.one_leader_per_term_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.one_leader_per_term_invariant
/-- info: 'VerdiCompat.Raft.oneLeaderPerTermStatement_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.oneLeaderPerTermStatement_holds

-- The candidate_entries ring (campaign Arc 3 unit 3, CandidateEntries.lean).
/-- info: 'VerdiCompat.Raft.cronies_term_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.cronies_term_invariant
/-- info: 'VerdiCompat.Raft.no_entries_past_current_term_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.no_entries_past_current_term_invariant
/-- info: 'VerdiCompat.Raft.candidate_entries_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.candidate_entries_invariant

-- The leaderLogs ring (campaign Arc 3 unit 4, LeaderLogs.lean).
/-- info: 'VerdiCompat.Raft.candidate_term_gt_log_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.candidate_term_gt_log_invariant
/-- info: 'VerdiCompat.Raft.leaderLogs_term_sanity_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.leaderLogs_term_sanity_invariant
/-- info: 'VerdiCompat.Raft.leaders_have_leaderLogs_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.leaders_have_leaderLogs_invariant
/-- info: 'VerdiCompat.Raft.votedFor_moreUpToDate_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.votedFor_moreUpToDate_invariant
/-- info: 'VerdiCompat.Raft.leaderLogs_votesWithLog_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.leaderLogs_votesWithLog_invariant
/-- info: 'VerdiCompat.Raft.one_leaderLog_per_term_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.one_leaderLog_per_term_invariant

-- The creation ring (campaign Arc 3 unit 5, CreationRing.lean).
/-- info: 'VerdiCompat.Raft.every_entry_was_created_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.every_entry_was_created_invariant
/-- info: 'VerdiCompat.Raft.logs_sorted_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.logs_sorted_invariant
/-- info: 'VerdiCompat.Raft.votesWithLog_sorted_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.votesWithLog_sorted_invariant
/-- info: 'VerdiCompat.Raft.terms_and_indices_from_one_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.terms_and_indices_from_one_invariant
/-- info: 'VerdiCompat.Raft.leaderLogs_candidateEntries_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.leaderLogs_candidateEntries_invariant

-- The log-matching core (campaign Arc 3 unit 6, LogMatching.lean).
/-- info: 'VerdiCompat.Raft.leaderLogs_sorted_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.leaderLogs_sorted_invariant
/-- info: 'VerdiCompat.Raft.UniqueIndices_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.UniqueIndices_invariant
/-- info: 'VerdiCompat.Raft.leader_sublog_invariant_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.leader_sublog_invariant_invariant
/-- info: 'VerdiCompat.Raft.log_matching_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.log_matching_invariant
/-- info: 'VerdiCompat.Raft.logMatchingStatement_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.logMatchingStatement_holds
/-- info: 'VerdiCompat.Raft.leaderLogs_contiguous_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.leaderLogs_contiguous_invariant
/-- info: 'VerdiCompat.Raft.allEntries_indices_gt_0_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.allEntries_indices_gt_0_invariant
/-- info: 'VerdiCompat.Raft.entries_match_nw_host_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.entries_match_nw_host_invariant

-- The AppendEntries feeder chain (campaign Arc 3 unit 7, AppendEntriesChain.lean).
/-- info: 'VerdiCompat.Raft.allEntries_term_sanity_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.allEntries_term_sanity_invariant
/-- info: 'VerdiCompat.Raft.log_properties_hold_on_leader_logs_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.log_properties_hold_on_leader_logs_invariant
/-- info: 'VerdiCompat.Raft.leaders_have_leaderLogs_strong_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.leaders_have_leaderLogs_strong_invariant
/-- info: 'VerdiCompat.Raft.append_entries_request_reply_correspondence_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.append_entries_request_reply_correspondence_invariant
/-- info: 'VerdiCompat.Raft.append_entries_came_from_leaders_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.append_entries_came_from_leaders_invariant
/-- info: 'VerdiCompat.Raft.leaderLogs_sublog_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.leaderLogs_sublog_invariant
/-- info: 'VerdiCompat.Raft.append_entries_leader_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.append_entries_leader_invariant
/-- info: 'VerdiCompat.Raft.append_entries_reply_sublog_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.append_entries_reply_sublog_invariant
/-- info: 'VerdiCompat.Raft.nextIndex_safety_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.nextIndex_safety_invariant
/-- info: 'VerdiCompat.Raft.leaderLogs_entries_match_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.leaderLogs_entries_match_invariant
/-- info: 'VerdiCompat.Raft.append_entries_leaderLogs_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.append_entries_leaderLogs_invariant
/-- info: 'VerdiCompat.Raft.logs_leaderLogs_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.logs_leaderLogs_invariant
/-- info: 'VerdiCompat.Raft.logs_leaderLogs_nw_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.logs_leaderLogs_nw_invariant
/-- info: 'VerdiCompat.Raft.leaderLogs_preserved_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.leaderLogs_preserved_invariant
/-- info: 'VerdiCompat.Raft.allEntries_leaderLogs_term_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.allEntries_leaderLogs_term_invariant
/-- info: 'VerdiCompat.Raft.allEntries_log_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.allEntries_log_invariant
/-- info: 'VerdiCompat.Raft.allEntries_votesWithLog_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.allEntries_votesWithLog_invariant
/-- info: 'VerdiCompat.Raft.append_entries_request_term_sanity_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.append_entries_request_term_sanity_invariant
/-- info: 'VerdiCompat.Raft.allEntries_candidateEntries_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.allEntries_candidateEntries_invariant
/-- info: 'VerdiCompat.Raft.allEntries_leader_sublog_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.allEntries_leader_sublog_invariant
/-- info: 'VerdiCompat.Raft.allEntries_log_matching_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.allEntries_log_matching_invariant
/-- info: 'VerdiCompat.Raft.log_log_prefix_within_term_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.log_log_prefix_within_term_invariant
/-- info: 'VerdiCompat.Raft.append_entries_append_entries_prefix_within_term_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.append_entries_append_entries_prefix_within_term_invariant
/-- info: 'VerdiCompat.Raft.prefix_within_term_inductive_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.prefix_within_term_inductive_invariant
/-- info: 'VerdiCompat.Raft.allEntries_leaderLogs_prefix_within_term_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.allEntries_leaderLogs_prefix_within_term_invariant
/-- info: 'VerdiCompat.Raft.leader_completeness_directly_committed_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.leader_completeness_directly_committed_invariant
/-- info: 'VerdiCompat.Raft.leader_completeness_committed_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.leader_completeness_committed_invariant
/-- info: 'VerdiCompat.Raft.leader_completeness_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.leader_completeness_invariant
/-- info: 'VerdiCompat.Raft.msg_refined_raft_net_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.msg_refined_raft_net_invariant
/-- info: 'VerdiCompat.Raft.msg_simulation_1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.msg_simulation_1
/-- info: 'VerdiCompat.Raft.msg_lift_prop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.msg_lift_prop
/-- info: 'VerdiCompat.Raft.ghost_entries_gt_0_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.ghost_entries_gt_0_invariant
/-- info: 'VerdiCompat.Raft.transitive_commit_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.transitive_commit_invariant
/-- info: 'VerdiCompat.Raft.all_entries_leader_logs_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.all_entries_leader_logs_invariant
/-- info: 'VerdiCompat.Raft.in_log_in_all_entries_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.in_log_in_all_entries_invariant
/-- info: 'VerdiCompat.Raft.log_all_entries_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.log_all_entries_invariant
/-- info: 'VerdiCompat.Raft.lastApplied_le_commitIndex_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.lastApplied_le_commitIndex_invariant
/-- info: 'VerdiCompat.Raft.no_append_entries_to_self_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.no_append_entries_to_self_invariant

/-! Unit-13 headliners: the W-B remainder (match_index_sanity,
prevLog_candidateEntriesTerm), the primed msg principle (GAP-1
msg-side), and the W-C ghost chain (GhostLogCorrect +
GhostLogsLogProperties — the latter is the primed principle's
discharge witness). -/
/-- info: 'VerdiCompat.Raft.match_index_sanity_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.match_index_sanity_invariant
/-- info: 'VerdiCompat.Raft.prevLog_candidateEntriesTerm_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.prevLog_candidateEntriesTerm_invariant
/-- info: 'VerdiCompat.Raft.msg_refined_raft_net_invariant'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.msg_refined_raft_net_invariant'
/-- info: 'VerdiCompat.Raft.ghost_log_correct_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.ghost_log_correct_invariant
/-- info: 'VerdiCompat.Raft.log_properties_hold_on_ghost_logs_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms VerdiCompat.Raft.log_properties_hold_on_ghost_logs_invariant

/-! ## Exhaustive sweep (fails the build on any disallowed axiom) -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Quot.sound]
  let mods := env.header.moduleNames
  let isOurs : Array Bool := mods.map fun m =>
    m.getRoot.toString.startsWith "VerdiCompat"
  let names : Array Name := env.constants.fold (fun acc n _ => acc.push n) #[]
  let mut bad : Array (Name × Name) := #[]
  let mut audited := 0
  for n in names do
    let ours := match env.getModuleIdxFor? n with
      | some idx => isOurs[idx.toNat]!
      | none => true  -- declared in this file: swept too
    unless ours do continue
    let axs ← collectAxioms n
    audited := audited + 1
    for ax in axs do
      unless allowed.contains ax do
        bad := bad.push (n, ax)
  if bad.isEmpty then
    IO.println s!"AxCheck sweep: {audited} declarations across VerdiCompat modules, axiom set within [propext, Quot.sound]"
  else
    throwError "AxCheck sweep FAILED — declarations with disallowed axioms \
      (sorryAx = a sorry; ofReduceBool = native_decide): \
      {bad.toList.map fun (n, ax) => s!"{n} ← {ax}"}"
