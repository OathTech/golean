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
