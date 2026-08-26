import GoLeanProofs.Specs.Raft.RoundInduction
import GoLeanProofs.Specs.Raft.RoundMaLemma
import GoLeanProofs.Specs.Raft.RoundVoteLemma
import GoLeanProofs.Specs.Raft.RoundMarLemma
import GoLeanProofs.Specs.Raft.RoundVrLemma
import GoLeanProofs.Specs.Raft.NativeEtcdDischarge

/-! # A4-U26 (slice 2, witness-in-same-slice): THE ROUND INDUCTION'S
WITNESSES over the four proved round kinds

## What this module discharges (stated precisely, so nothing
overclaims)

1. **The shared loop-head configuration, kernel-pinned** (`c0_*_shared`):
   the four proved round kinds' `C0`s are LITERALLY one configuration —
   the driver's `round < 400` loop head recurs identically across
   kinds (the U18 census claim, now a kernel fact). This is what makes
   cross-kind literal chaining config-compatible.
2. **The abstract witness chain** (`absN0 … absN4`): a GENUINE
   `EStep`-trace of the etcd election dialect from the discharged seed
   `seedN₀` — campaign(1), node 2's grant, the self-vote poll, and the
   winning MsgVoteResp (leader born, victory ghost pushed). Every spec
   computation was `#eval`-checked before `decide`
   (`artifacts/probe/U26AbsChainProbe.lean`).
3. **The induction witnesses**: `round_induction` discharged at the
   identity placement on
   - the Vr link (the election-completion round paired with its
     GENUINE abstract step — the round where the S1 leadership claim
     is born);
   - the Vote link (paired with node 2's genuine grant step);
   - a 2-link chain (trivial ++ Ma) exercising the CHAINING mechanics
     end to end;
   - the Mar 1-link (abstractly SILENT in the election fragment —
     `ReachRel.refl`; see the honesty note below).
4. **The seeded witness**: `seeded_round_induction` discharged at the
   trivial chain from `seedσ` — every premise concretely satisfied
   (non-vacuity of the seeded statement). The REAL seeded chain awaits
   the campaign-span round lemma (seedσ → first loop head), a named
   open obligation of the T1 assembly.
5. **Safety, non-vacuously**: `oneLeaderPerTerm absN4` via the
   obligation discharge + `seed_N₀` + the witness trace's `ReachRel`,
   at a net that REALLY HAS a leader (`absN4_leader`).

## Honesty notes

- The concrete↔abstract PAIRING in each link is witness DATA (the
  induction transports it; it does not assert `absRead σ = N`). The
  Vr/Vote links' pairings are faithful to the rounds' kernel-pinned
  readouts (state/term/vote/lead deltas match `roundVr_*`/`roundVote_*`
  readout theorems); the Ma/Mar links are paired REFL in the election
  fragment — their concrete commit/append movement has NO constructor
  in `EStep` (election fragment by design), which is a named T1
  obligation: the full-dialect step relation (commit/append members)
  is the assembly's seam, not this module's claim.
- The four kinds do NOT chain concretely (probe
  `artifacts/probe/U26CanonProbe.lean`: no cross-kind literal or ~ₘ
  adjacency exists among the DOCTORED fixtures — expected, they were
  doctored to exercise kinds). Multi-link chains over REAL successive
  rounds are the T1 replay's per-round emitter products (A5).

This module is LIVE (default target) since the arc-4 landing fix
round — the witness-return correction (witnesses of live laws ship in
the gated build; see GoLeanProofs.lean's witness-return block). -/

namespace GoLean.RaftSeam.RoundInd

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Frame GoLean.Surface
open GoLean.RaftSeam GoLean.RaftSeam.NativeSpec

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

/-! ## 1. The shared loop-head configuration (kernel pins) -/

theorem c0_vote_shared : RoundVote.roundVoteC0 = RoundMa.roundC0 := by
  kernel_rfl

theorem c0_mar_shared : RoundMar.roundMarC0 = RoundMa.roundC0 := by
  kernel_rfl

theorem c0_vr_shared : RoundVr.roundVrC0 = RoundMa.roundC0 := by
  kernel_rfl

/-! ## 2. The abstract witness chain (the etcd dialect, from the seed) -/

def voters3 : List Nat := [1, 2, 3]

def absN0 : SNet := seedN₀

/-- Node 1 campaigns: candidate at term 1, self-vote ghost-pushed. -/
def absN1 : SNet :=
  updNode absN0 1 (NativeSpec.specBecomeCandidate (absN0.node 1) 1)
    (pushVote absN0.ghost 1 ((absN0.node 1).term + 1) 1)

theorem abs_step01 : EStep voters3 absN0 absN1 :=
  EStep.campaign absN0 1 (by decide)

/-- Node 2's post-grant state (#eval-pinned in the probe). -/
def r2' : ENode :=
  { state := 0, term := 1, vote := 1, lead := 0, log := [(1, 1)],
    committed := 1, votesRec := [] }

/-- Node 2 receives MsgVote{term 1, last (1,1)} and grants. -/
def absN2 : SNet := updNode absN1 2 r2' (pushVote absN1.ghost 2 1 1)

theorem abs_step12 : EStep voters3 absN1 absN2 :=
  EStep.recvVote absN1 2 1 1 1 1 r2' true (by decide) (by decide)

/-- Node 1 after polling its own MsgVoteResp (tally [(1, true)]). -/
def r3' : ENode :=
  { state := 1, term := 1, vote := 1, lead := 0, log := [(1, 1)],
    committed := 1, votesRec := [(1, true)] }

def absN3 : SNet := updNode absN2 1 r3' absN2.ghost

theorem abs_step23 : EStep voters3 absN2 absN3 :=
  EStep.recvVoteResp absN2 1 1 false r3' false (by decide)
    ⟨by decide, by decide, by decide⟩ (fun _ => by decide) (by decide)

/-- Node 1 wins on node 2's grant: leader at term 1, noop appended,
tally cleared (`becomeLeader`), victory `(1, 1, [2,1])` ghost-pushed. -/
def r4' : ENode :=
  { state := 2, term := 1, vote := 1, lead := 1, log := [(2, 1), (1, 1)],
    committed := 1, votesRec := [] }

def absN4 : SNet :=
  updNode absN3 1 r4'
    (pushVictory absN3.ghost (absN3.node 1).term 1
      (grantedOf (recordVote (absN3.node 1).votesRec 2 true)))

theorem abs_step34 : EStep voters3 absN3 absN4 :=
  EStep.recvVoteResp absN3 1 2 false r4' true (by decide)
    ⟨by decide, by decide, by decide⟩ (fun _ => by decide) (by decide)

/-- The witness chain's reachability record: `absN4` is `EStep`-
reachable from the DISCHARGED seed. -/
theorem abs_reach04 : ReachRel (EStep voters3) absN0 absN4 :=
  .tail (.tail (.tail (.tail (.refl _) abs_step01) abs_step12)
    abs_step23) abs_step34

/-- **Safety at the witness end net, non-vacuously**: election safety
holds at `absN4` — via the etcd obligation discharge, `seed_N₀`, and
the chain — and `absN4` REALLY HAS a leader. -/
theorem abs_safety : oneLeaderPerTerm absN4 :=
  native_one_leader_per_term (etcd_discharges voters3) seed_N₀ abs_reach04

theorem absN4_leader : (absN4.node 1).state = 2 := by decide

/-! ## 3. The links -/

/-- The election-completion round paired with its GENUINE abstract
step (the tally-complete candidate wins on the delivered grant). -/
def vrLink : RoundLink :=
  ⟨RoundVr.canonVr, RoundVr.canonVr', 33274, RoundVr.πVr, absN3, absN4⟩

/-- The vote round paired with node 2's genuine grant step. -/
def voteLink : RoundLink :=
  ⟨RoundVote.canonVote, RoundVote.canonVote', 19291, RoundVote.πVote,
   absN1, absN2⟩

/-- The append round — abstractly SILENT in the election fragment
(refl pairing; the commit/append dialect members are the T1 seam). -/
def maLink : RoundLink :=
  ⟨RoundMa.canonMa, RoundMa.canonMa', 23488, RoundMa.πMa, absN4, absN4⟩

/-- The commit round — abstractly silent in the election fragment. -/
def marLink : RoundLink :=
  ⟨RoundMar.canonMar, RoundMar.canonMar', 26224, RoundMar.πMar,
   absN4, absN4⟩

/-- The identity placement of a state (the `RoundFam.self`
construction, exposed as a `FrameSim`). -/
def idPlace (σ : ExecState) :
    FrameSim (ρT σ.nextAddr 0) σ.nextAddr σ.nextAddr [] σ σ :=
  frameSim_seed rfl (fun f _ => renameStmt_ρT_zero σ.nextAddr f.body)

/-! ## 4. The induction witnesses -/

/-- The Vr 1-link witness: the induction discharged end to end at the
identity placement, with the genuine abstract step riding along. -/
theorem vr_chain_witness :
    ∃ σE NE, FamTrace (EStep voters3) (ρT RoundVr.canonVr.nextAddr 0)
      RoundVr.canonVr.nextAddr
      (renameConfig (ρT RoundVr.canonVr.nextAddr 0) RoundVr.roundVrC0)
      RoundVr.canonVr absN3 [vrLink] (chainπ [vrLink] ++ []) σE NE [] :=
  round_induction [vrLink] ⟨rfl, rfl, trivial⟩
    (by intro l hl; rw [List.mem_singleton] at hl; subst hl
        exact RoundVr.roundVr_lemma)
    (by intro l hl; rw [List.mem_singleton] at hl; subst hl
        exact .tail (.refl _) abs_step34)
    (idPlace RoundVr.canonVr) []

/-- The Vote 1-link witness (genuine grant step). -/
theorem vote_chain_witness :
    ∃ σE NE, FamTrace (EStep voters3) (ρT RoundVote.canonVote.nextAddr 0)
      RoundVote.canonVote.nextAddr
      (renameConfig (ρT RoundVote.canonVote.nextAddr 0)
        RoundVote.roundVoteC0)
      RoundVote.canonVote absN1 [voteLink] (chainπ [voteLink] ++ [])
      σE NE [] :=
  round_induction [voteLink] ⟨rfl, rfl, trivial⟩
    (by intro l hl; rw [List.mem_singleton] at hl; subst hl
        exact RoundVote.roundVote_lemma)
    (by intro l hl; rw [List.mem_singleton] at hl; subst hl
        exact .tail (.refl _) abs_step12)
    (idPlace RoundVote.canonVote) []

/-- The Mar 1-link witness (election-fragment-silent pairing). -/
theorem mar_chain_witness :
    ∃ σE NE, FamTrace (EStep voters3) (ρT RoundMar.canonMar.nextAddr 0)
      RoundMar.canonMar.nextAddr
      (renameConfig (ρT RoundMar.canonMar.nextAddr 0) RoundMar.roundMarC0)
      RoundMar.canonMar absN4 [marLink] (chainπ [marLink] ++ []) σE NE [] :=
  round_induction [marLink] ⟨rfl, rfl, trivial⟩
    (by intro l hl; rw [List.mem_singleton] at hl; subst hl
        exact RoundMar.roundMar_lemma)
    (by intro l hl; rw [List.mem_singleton] at hl; subst hl
        exact .refl _)
    (idPlace RoundMar.canonMar) []

/-- The trivial pad link at the Ma canon (the chaining-mechanics
witness's first link). -/
def ma0Link : RoundLink := RoundLink.trivial RoundMa.canonMa absN4

/-- **The 2-link chaining witness**: trivial ++ Ma — `ChainedFrom`,
the per-link lemmas (`RoundLemmaShape.refl` + `roundMa_lemma`), and
the trace's `cons`/`cons`/`nil` mechanics all exercised concretely. -/
theorem ma_chain2_witness :
    ∃ σE NE, FamTrace (EStep voters3) (ρT RoundMa.canonMa.nextAddr 0)
      RoundMa.canonMa.nextAddr
      (renameConfig (ρT RoundMa.canonMa.nextAddr 0) RoundMa.roundC0)
      RoundMa.canonMa absN4 [ma0Link, maLink]
      (chainπ [ma0Link, maLink] ++ []) σE NE [] :=
  round_induction [ma0Link, maLink] ⟨rfl, rfl, rfl, rfl, trivial⟩
    (by intro l hl
        rcases List.mem_cons.mp hl with h | hl
        · subst h; exact RoundLemmaShape.refl RoundMa.canonMa RoundMa.roundC0
        · rw [List.mem_singleton] at hl; subst hl
          exact RoundMa.roundMa_lemma)
    (by intro l hl
        rcases List.mem_cons.mp hl with h | hl
        · subst h; exact .refl _
        · rw [List.mem_singleton] at hl; subst hl; exact .refl _)
    (idPlace RoundMa.canonMa) []

/-! ## 5. The seeded witness (non-vacuity of the seeded statement) -/

/-- `seeded_round_induction`'s premises are concretely satisfiable:
the trivial chain from `(seedσ, seedN₀)` at the identity placement.
The REAL seeded chain (campaign span → round ladder) is the T1
assembly's named open obligation — this witness claims only that the
seeded statement is non-vacuous and its `Seed` discharge fires. -/
theorem seeded_witness :
    ∃ σE NE, FamTrace (EStep voters3) (ρT seedσ.nextAddr 0) seedσ.nextAddr
        (renameConfig (ρT seedσ.nextAddr 0) RoundMa.roundC0) seedσ seedN₀
        [RoundLink.trivial seedσ seedN₀]
        (chainπ [RoundLink.trivial seedσ seedN₀] ++ []) σE NE []
      ∧ (∀ {voters : List Nat}, ElectObligations voters (EStep voters3) →
          oneLeaderPerTerm NE) := by
  obtain ⟨σE, NE, htr, hsafe⟩ :=
    seeded_round_induction (step := EStep voters3) (C0 := RoundMa.roundC0)
      [RoundLink.trivial seedσ seedN₀] ⟨rfl, rfl, trivial⟩
      (by intro l hl; rw [List.mem_singleton] at hl; subst hl
          exact RoundLemmaShape.refl seedσ RoundMa.roundC0)
      (by intro l hl; rw [List.mem_singleton] at hl; subst hl
          exact .refl _)
      (idPlace seedσ) []
  exact ⟨σE, NE, htr, hsafe⟩

end GoLean.RaftSeam.RoundInd
