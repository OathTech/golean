import GoLeanProofs.Specs.Raft.NativeEtcdDischarge

/-! # C3 — the S1 checker-implication leaf (I4-scoped)
(scoping lane `campaign-arc4b`, unit C3, 2026-08-27; design of
record: the campaign worktree's
`docs/2026-08-26_campaign-flexibility-redesign.md` §3 I4 — the
abstract checker interface, scoped EXACTLY to the S1 check per §7's
middle-path calibration: no general checker theory.)

## What this module is

Charter part 4: **signature invariants ⇒ the S1 check's
false-delta**, through the abstract checker interface. The
checker-computes-P side is stated as the INTERFACE PREMISE
(`S1CheckerInterface` below) — its interpreter-side proof (that the
twin checker's actual span instantiates it through `absTwinRead`) is
the arc-4 lane's I2 work, NOT this lane's; this leaf CONSUMES the
interface.

## The checker's S1, read at source (twin-lib.go, `harvest`)

The claim source is a Ready carrying `SoftState.RaftState ==
StateLeader`: the harvest records `(nd.term, nd.id)` into
`leaderOf : term ↦ node` and fires
`"S1 election safety: term .. claimed by both .."` exactly when a
DIFFERENT node claims an already-claimed term. Two facts shape the
interface:

- claims accumulate ACROSS harvests — the check is CROSS-TIME, so
  the spec-side fact it needs is
  `native_one_leader_per_term_cross_time`, not the per-net
  statement (the victory ghost carries the earlier observation
  forward; no extra signature member was needed — see the chain
  module);
- the claims of one run are totally ordered along ONE trace — the
  interface premise (`ClaimTrace`) carries exactly that linearity
  and nothing else about the checker's mechanics.

LINEAGE: property transfer through a refinement/abstraction mapping
(the observation trace is the abstraction of the harvest loop);
standard assume-guarantee interface decomposition for the
checker-computes-P premise. -/

namespace GoLean.RaftSeam.NativeSpec

/-- The S1 observation trace: the claims list, in harvest order,
each claim observed on a net reachable from the previous
observation point — the abstraction of "one run's harvests, in
order". (`done` permits truncation anywhere: the interface never
demands the run complete.) -/
inductive ClaimTrace (step : SNet → SNet → Prop) :
    SNet → List (Nat × Nat) → Prop where
  | done (N : SNet) : ClaimTrace step N []
  | obs {N N' : SNet} {t l : Nat} {cls : List (Nat × Nat)} :
      ReachRel step N N' →
      (N'.node l).state = 2 → (N'.node l).term = t →
      ClaimTrace step N' cls →
      ClaimTrace step N ((t, l) :: cls)

/-- The S1 delta over a claims list: one term claimed by two
distinct nodes (the exact condition of the checker's `leaderOf`
branch — `prev != nd.id` at a recorded term, order-abstracted). -/
def S1Delta (claims : List (Nat × Nat)) : Prop :=
  ∃ t l l', (t, l) ∈ claims ∧ (t, l') ∈ claims ∧ l ≠ l'

/-- **The I4 interface premise, S1-scoped** (the checker-computes-P
side, stated — its proof against the checker's actual code through
`absTwinRead` is I2 work on the arc-4 lane): the checker's claims
are harvest observations along the run's trace, and its S1
violation branch fires only on a delta of those claims. -/
structure S1CheckerInterface (step : SNet → SNet → Prop) (N₁ : SNet)
    (claims : List (Nat × Nat)) (violation : Prop) : Prop where
  claimsFromTrace : ClaimTrace step N₁ claims
  violationImpliesDelta : violation → S1Delta claims

/-! ## The leaf's spine -/

/-- Every claim's observation net is reachable from the trace's
start (the trace's `ReachRel` segments composed). -/
theorem claim_reachable {step : SNet → SNet → Prop} {N : SNet}
    {cls : List (Nat × Nat)} (htr : ClaimTrace step N cls)
    {t l : Nat} (h : (t, l) ∈ cls) :
    ∃ N', ReachRel step N N' ∧
      (N'.node l).state = 2 ∧ (N'.node l).term = t := by
  induction htr with
  | done N => cases h
  | obs hr hst htm _ ih =>
    rcases List.mem_cons.mp h with heq | hmem
    · have ht : t = _ := congrArg Prod.fst heq
      have hl : l = _ := congrArg Prod.snd heq
      subst ht; subst hl
      exact ⟨_, hr, hst, htm⟩
    · obtain ⟨N'', hr'', hst'', htm''⟩ := ih hmem
      exact ⟨N'', hr.trans hr'', hst'', htm''⟩

/-- Any two same-term claims of one trace agree — the pairwise core:
head-vs-head is reflexivity, head-vs-tail is the cross-time theorem
(the head's observation net reaches the tail claim's), tail-vs-tail
is the induction hypothesis with the base advanced. -/
theorem claimTrace_agree {voters : List Nat}
    {step : SNet → SNet → Prop} (ob : ElectObligations voters step)
    {N₀ : SNet} (hseed : Seed N₀) :
    ∀ {N₁ : SNet} {cls : List (Nat × Nat)}, ClaimTrace step N₁ cls →
    ReachRel step N₀ N₁ →
    ∀ t l l', (t, l) ∈ cls → (t, l') ∈ cls → l = l' := by
  intro N₁ cls htr
  induction htr with
  | done N => intro _ t l l' hl _; cases hl
  | obs hr hst htm htail ih =>
    intro h01 t l l' hl hl'
    rcases List.mem_cons.mp hl with heq | hmem
    · rcases List.mem_cons.mp hl' with heq' | hmem'
      · -- both are the head claim
        have h1 : l = _ := congrArg Prod.snd heq
        have h2 : l' = _ := congrArg Prod.snd heq'
        rw [h1, h2]
      · -- head vs a later claim: cross-time, head's net first
        have hteq : t = _ := congrArg Prod.fst heq
        have hleq : l = _ := congrArg Prod.snd heq
        obtain ⟨N'', hr'', hst'', htm''⟩ := claim_reachable htail hmem'
        subst hleq
        exact native_one_leader_per_term_cross_time ob hseed
          (h01.trans hr) hr'' hst (hteq ▸ htm) hst'' htm''
    · rcases List.mem_cons.mp hl' with heq' | hmem'
      · -- a later claim vs the head: symmetric
        have hteq : t = _ := congrArg Prod.fst heq'
        have hleq : l' = _ := congrArg Prod.snd heq'
        obtain ⟨N'', hr'', hst'', htm''⟩ := claim_reachable htail hmem
        subst hleq
        exact (native_one_leader_per_term_cross_time ob hseed
          (h01.trans hr) hr'' hst (hteq ▸ htm) hst'' htm'').symm
      · exact ih (h01.trans hr) t l l' hmem hmem'

/-- **THE S1 LEAF** — signature invariants ⇒ the S1 check's
false-delta: for ANY dialect discharging the obligation signature,
from any seeded start, the claims of any observation trace carry no
S1 delta — so, through the interface premise, the checker's S1
violation branch never fires. -/
theorem s1_leaf {voters : List Nat} {step : SNet → SNet → Prop}
    (ob : ElectObligations voters step) {N₀ N₁ : SNet}
    (hseed : Seed N₀) (h01 : ReachRel step N₀ N₁)
    {claims : List (Nat × Nat)} {violation : Prop}
    (hIface : S1CheckerInterface step N₁ claims violation) :
    ¬ violation := by
  intro hviol
  obtain ⟨t, l, l', hl, hl', hne⟩ := hIface.violationImpliesDelta hviol
  exact hne (claimTrace_agree ob hseed hIface.claimsFromTrace h01
    t l l' hl hl')

/-- The etcd-dialect corollary (the discharge layer plugged in): the
S1 check is silent on every etcd-election-fragment run from an
empty-ghost, no-leader start. -/
theorem etcd_s1_leaf (voters : List Nat) {N₀ N₁ : SNet}
    (hv : ∀ v t c, (t, c) ∉ N₀.ghost.votes v)
    (hnl : ∀ i, (N₀.node i).state ≠ 2)
    (h01 : ReachRel (EStep voters) N₀ N₁)
    {claims : List (Nat × Nat)} {violation : Prop}
    (hIface : S1CheckerInterface (EStep voters) N₁ claims violation) :
    ¬ violation :=
  s1_leaf (etcd_discharges voters) ⟨hv, hnl⟩ h01 hIface

end GoLean.RaftSeam.NativeSpec
