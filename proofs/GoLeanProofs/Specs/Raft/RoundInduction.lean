import GoLeanProofs.Specs.Raft.RoundStatement
import GoLeanProofs.Specs.Raft.NativeS1Chain
import GoLeanProofs.Specs.Raft.SeedPin

/-! # A4-U26 (slice 2): THE ROUND INDUCTION — the simulation induction
over round sequences, composed at absState level

## What this module is

The C-ladder's induction skeleton made a THEOREM: given a CHAIN of
round links — each carrying a proved `RoundLemmaShape` instance (the
R-form: A4-U22/U23/U24/U25 delivered four kinds) and an abstract
`ReachRel`-segment of a dialect step relation — the whole trace runs
from ANY `FrameSim` placement of the first canon, returns to the
shared loop-head configuration at every boundary, re-establishes
family membership at every boundary (trace-long Fam membership: the
`FamTrace` constructors CARRY the per-boundary `FrameSim` facts), and
the abstract boundary nets form a `ReachRel` trace of the dialect
(the absState trace IS a specRound trace). With the arc4c seed pin
(`seedσ`/`seedN₀`/`seed_N₀`, landed this unit) the seeded corollary
discharges `Seed` and hands every obligation-discharging dialect
`oneLeaderPerTerm` at the trace's end net — the layer-C design §3
carry (`R σ N := σ ∈ Fam ∧ absRead σ = N`, stepped by round lemmas),
mechanized at the granularity the R-form actually provides.

## The chaining decision (the successor-canon design verdict, A4-U26
slice 1 — probe `artifacts/probe/U26CanonProbe.lean`, recorded in
`docs/campaign-arc4-log.md` U26)

The canon step between consecutive links is LITERAL EQUALITY
(`l.canon' = next.canon`, folded into `ChainedFrom`), NOT the ~ₘ
(masked latitude-equivalence) form the successor-canon design
proposed. Three probe findings force this, each recorded in the log:
(1) the four proved kinds share ONE loop-head configuration literally
(kernel-pinned in `RoundInductionWitness`), so literal chaining is
config-compatible; (2) the landed doctored+pruned fixtures RESIST
canonicalization (`canonStateM` fails closed with MISSING flags —
pruning drops twin-reachable cells, so the fixtures are open terms
with dangling references; only FULL states like `seedσ` canonicalize
cleanly); (3) `CEquivM` cannot transport `RoundFam` membership —
capacity slack, dropped garbage, and the mask are outside `FrameSim`'s
vocabulary, and the bridge (canonicalizer congruence under placement +
per-class preservation) is exactly the machinery the standing [USER]
decision schedules with the symbolic semantics (post-T1). Literal
chaining is also what the T1 round-replay actually needs: the pinned
run's successive loop-head states ARE successive literals (A5,
certificate replay at round granularity).

`ReachRel`-valued abstract segments (not single steps) let one
concrete round carry zero (`refl` — abstractly silent rounds, e.g.
append/commit rounds in the ELECTION fragment) or several abstract
steps; the dialect and the concrete↔abstract pairing stay parameters —
the pairing (absRead σᵢ = readout of Nᵢ) is the T1 assembly's seam,
deliberately NOT asserted here (statement honesty: this module never
claims the projection, it TRANSPORTS whatever pairing the instance
supplies).

LINEAGE: simulation induction / refinement mapping over an inductive
invariant (Abadi–Lamport — the layer-C design §3/§7 pin); the
abstract side is the standard RT-closure invariance rule
(`NativeS1Chain.invariance`). No new mechanism class. -/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Frame GoLean.Surface
open GoLean.RaftSeam.NativeSpec

/-! ## 1. Round links and chains -/

/-- One link of a round chain: the R-form data (canonical loop-head
state, successor state, span, censused prefix) paired with the
abstract boundary nets. The concrete↔abstract PAIRING is data — the
induction transports it; asserting its faithfulness (absRead) is the
assembly's obligation, not this structure's. -/
structure RoundLink where
  canon : ExecState
  canon' : ExecState
  Δ : Nat
  π : Choices
  N : SNet
  N' : SNet

/-- The trivial (zero-step) link: pads chains, witnesses chaining
mechanics. Its R-form instance is `RoundLemmaShape.refl` below. -/
def RoundLink.trivial (σ : ExecState) (N : SNet) : RoundLink :=
  ⟨σ, σ, 0, [], N, N⟩

/-- Chain-from: the first link starts at `(c, n)`, consecutive links
meet LITERALLY (concrete canon and abstract net both) — the
successor-canon verdict above. -/
def ChainedFrom (c : ExecState) (n : SNet) : List RoundLink → Prop
  | [] => True
  | l :: rest => l.canon = c ∧ l.N = n ∧ ChainedFrom l.canon' l.N' rest

/-- The chain's concatenated censused choice prefix. -/
def chainπ : List RoundLink → Choices
  | [] => []
  | l :: rest => l.π ++ chainπ rest

/-- The chain's total span. -/
def chainΔ : List RoundLink → Nat
  | [] => 0
  | l :: rest => l.Δ + chainΔ rest

/-- The zero-step R-form instance (every placement, trivially):
`stepFnIter 0` returns immediately and membership is the premise. -/
theorem RoundLemmaShape.refl (canon : ExecState) (C0 : Config) :
    RoundLemmaShape canon canon C0 0 [] := by
  intro r na₀ na fr σF hF ch
  exact ⟨σF, by simp [stepFnIter], na, fr, hF⟩

/-! ## 2. The trace-long conclusion (`FamTrace`)

Each `cons` CARRIES the boundary facts: the round's run equation (the
loop-head config `Cr` recurs), the re-established family membership
(`FrameSim` at the SAME placement `r, na₀` — the R-form's conclusion
shape is what makes literal chaining compose without a `FrameSim`
transitivity lemma), and the abstract segment. Consumers read
per-boundary facts by destructuring — the tail of a `FamTrace` is a
`FamTrace`. -/
inductive FamTrace (step : SNet → SNet → Prop) (r : Nat → Nat) (na₀ : Nat)
    (Cr : Config) :
    ExecState → SNet → List RoundLink → Choices → ExecState → SNet →
    Choices → Prop where
  | nil (σ : ExecState) (N : SNet) (ch : Choices) :
      FamTrace step r na₀ Cr σ N [] ch σ N ch
  | cons {l : RoundLink} {rest : List RoundLink} {σF σF' σE : ExecState}
      {NE : SNet} {ch chE : Choices}
      (hrun : stepFnIter l.Δ σF Cr (l.π ++ ch) = .ok (Cr, σF', ch))
      (hfam : ∃ na' fr', FrameSim r na₀ na' fr' l.canon' σF')
      (habs : ReachRel step l.N l.N')
      (tail : FamTrace step r na₀ Cr σF' l.N' rest ch σE NE chE) :
      FamTrace step r na₀ Cr σF l.N (l :: rest) (l.π ++ ch) σE NE chE

/-! ## 3. THE ROUND INDUCTION -/

/-- **THE ROUND INDUCTION.** From any `FrameSim` placement of the
chain's first canon, with each link's R-form lemma and abstract
segment in hand, the whole chain runs: the trace exists with
family membership re-established at every boundary and the abstract
nets stepping by the dialect. The placement `r, na₀` is FIXED along
the whole trace (the R-form conclusion preserves it), which is
exactly why literal canon chaining needs no `FrameSim` composition. -/
theorem round_induction {step : SNet → SNet → Prop} {C0 : Config} :
    ∀ (links : List RoundLink) {c₀ : ExecState} {N₀ : SNet},
      ChainedFrom c₀ N₀ links →
      (∀ l ∈ links, RoundLemmaShape l.canon l.canon' C0 l.Δ l.π) →
      (∀ l ∈ links, ReachRel step l.N l.N') →
      ∀ {r : Nat → Nat} {na₀ na : Nat} {fr : GoCore.Heap} {σF : ExecState},
      FrameSim r na₀ na fr c₀ σF → ∀ ch : Choices,
      ∃ σE NE, FamTrace step r na₀ (renameConfig r C0) σF N₀ links
        (chainπ links ++ ch) σE NE ch := by
  intro links
  induction links with
  | nil =>
      intro c₀ N₀ _ _ _ r na₀ na fr σF _ ch
      exact ⟨σF, N₀, FamTrace.nil σF N₀ ch⟩
  | cons l rest ih =>
      intro c₀ N₀ hch hlem habs r na₀ na fr σF hF ch
      obtain ⟨hc, hN, hch'⟩ := hch
      subst hc; subst hN
      obtain ⟨σF', hrun, na', fr', hfs'⟩ :=
        hlem l (List.mem_cons_self ..) r na₀ na fr σF hF (chainπ rest ++ ch)
      obtain ⟨σE, NE, htail⟩ :=
        ih hch' (fun l' hl' => hlem l' (List.mem_cons_of_mem _ hl'))
          (fun l' hl' => habs l' (List.mem_cons_of_mem _ hl')) hfs' ch
      refine ⟨σE, NE, ?_⟩
      have hstream : chainπ (l :: rest) ++ ch = l.π ++ (chainπ rest ++ ch) := by
        simp [chainπ]
      rw [hstream]
      exact FamTrace.cons hrun ⟨na', fr', hfs'⟩
        (habs l (List.mem_cons_self ..)) htail

/-! ## 4. Trace corollaries (what the trace yields) -/

/-- The abstract boundary nets form a `ReachRel` trace end to end. -/
theorem FamTrace.reach {step : SNet → SNet → Prop} {r na₀ Cr}
    {σ : ExecState} {N : SNet} {links : List RoundLink} {st : Choices}
    {σE : ExecState} {NE : SNet} {chE : Choices}
    (h : FamTrace step r na₀ Cr σ N links st σE NE chE) :
    ReachRel step N NE := by
  induction h with
  | nil => exact .refl _
  | cons _ _ habs _ ih => exact habs.trans ih

/-- The flat composed run: the whole chain is ONE `stepFnIter`
equation at the summed span (certificate-replay shape; the per-round
equations compose by `stepFnIter_chain`). -/
theorem FamTrace.flat {step : SNet → SNet → Prop} {r na₀ Cr}
    {σ : ExecState} {N : SNet} {links : List RoundLink} {st : Choices}
    {σE : ExecState} {NE : SNet} {chE : Choices}
    (h : FamTrace step r na₀ Cr σ N links st σE NE chE) :
    stepFnIter (chainΔ links) σ Cr st = .ok (Cr, σE, chE) := by
  induction h with
  | nil => simp [chainΔ, stepFnIter]
  | cons hrun _ _ _ ih =>
      exact GoLean.Surface.stepFnIter_chain hrun ih

/-- Safety at the trace's end: every obligation-discharging dialect
carries `one_leader_per_term` to the end net of any trace from a
seeded start (the native chain consumed wholesale). -/
theorem FamTrace.safety {voters : List Nat} {step : SNet → SNet → Prop}
    {r na₀ Cr} {σ : ExecState} {N : SNet} {links : List RoundLink}
    {st : Choices} {σE : ExecState} {NE : SNet} {chE : Choices}
    (ob : ElectObligations voters step) (hseed : Seed N)
    (h : FamTrace step r na₀ Cr σ N links st σE NE chE) :
    oneLeaderPerTerm NE :=
  native_one_leader_per_term ob hseed h.reach

/-- The full invariant bundle at the trace's end (same shape; the
bundle at INTERIOR boundaries follows by destructuring the trace —
each tail is a `FamTrace` from a net `ReachRel`-below the end). -/
theorem FamTrace.fullInv {voters : List Nat} {step : SNet → SNet → Prop}
    {r na₀ Cr} {σ : ExecState} {N : SNet} {links : List RoundLink}
    {st : Choices} {σE : ExecState} {NE : SNet} {chE : Choices}
    (ob : ElectObligations voters step) (hseed : Seed N)
    (h : FamTrace step r na₀ Cr σ N links st σE NE chE) :
    FullInv voters NE :=
  fullInv_reachable ob hseed h.reach

/-! ## 5. The seeded base (the arc4c landing consumed)

`seedσ`/`seedN₀` are the C-ladder's base case (SP1): `SeedFam` is
`RoundFam seedσ` and `seed_N₀ : Seed seedN₀` is the discharged
hypothesis. A chain from the seed starts at ANY `SeedFam` member —
the placement is the member's own. -/

/-- **THE SEEDED ROUND INDUCTION**: a chain from `(seedσ, seedN₀)`
runs from any `SeedFam` member at its placement, and every
obligation-discharging dialect carries `one_leader_per_term` to the
end net — `Seed` discharged by `seed_N₀`, nothing left premised on
the abstract side but the dialect's own obligation discharge. -/
theorem seeded_round_induction {step : SNet → SNet → Prop} {C0 : Config}
    (links : List RoundLink)
    (hch : ChainedFrom seedσ seedN₀ links)
    (hlem : ∀ l ∈ links, RoundLemmaShape l.canon l.canon' C0 l.Δ l.π)
    (habs : ∀ l ∈ links, ReachRel step l.N l.N')
    {r : Nat → Nat} {na₀ na : Nat} {fr : GoCore.Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr seedσ σF) (ch : Choices) :
    ∃ σE NE, FamTrace step r na₀ (renameConfig r C0) σF seedN₀ links
        (chainπ links ++ ch) σE NE ch
      ∧ (∀ {voters : List Nat}, ElectObligations voters step →
          oneLeaderPerTerm NE) := by
  obtain ⟨σE, NE, htr⟩ := round_induction links hch hlem habs hF ch
  exact ⟨σE, NE, htr, fun ob => htr.safety ob seed_N₀⟩

end GoLean.RaftSeam
