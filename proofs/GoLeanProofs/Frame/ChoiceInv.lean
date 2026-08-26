import GoLeanProofs.Frame.ChoiceCanon

/-! # Anchored runs and the CHOICE-INVARIANCE statement layer
(campaign lane arc4c, unit SP1)

**What this module is.** The general machinery for stating that a
SPAN of execution is latitude-invariant: an executable ANCHORED RUN
(walk until a configuration predicate fires, fuel-bounded,
fail-closed) and the CHOICE-INVARIANCE Prop former — "from this
start, EVERY choice stream reaches the anchor at the same
configuration with `~`-equivalent states". The seed pin
(`Specs/Raft/SeedPin.lean`) instantiates it at the twin's init span;
future spans (round ladders, harvest rings) can instantiate the same
former at their own anchors.

**THE LEMMA'S STANDING (stated bluntly, so nothing overclaims).**
The choice-invariance LEMMA for a span is the ∀-stream discharge of
`ChoiceInvariantTo`. This unit ships:
- the STATEMENT layer (this module),
- the `~` carrier (`ChoiceCanon`) with reader-invariance by
  construction,
- the measured operation-class census of the init span (probe record
  in `docs/campaign-arc4c-log.md`: every init draw is one of
  `mapIter`/`appendSpill`, both classes' single-position deviations
  landing `~`-equal by computation), and
- KERNEL-CHECKED instances (`SeedWitness`): non-canonical streams
  landing `CEquiv`-equal to the canonical representative — the
  occupation proof that the equivalence is real, including a
  different-capacities instance.
The GENERAL ∀-stream discharge is bisimulation-up-to-`~` over the
span's operation classes — per the standing [USER] design decisions
(campaign log 2026-08-27) that bisimulation IS the future symbolic
semantics' correspondence ("the choice-invariance lemma is its
erased half"), scheduled post-T1. Until it lands, a consumer of the
∀-form consumes `ChoiceInvariantTo` as a named premise, never a
silently assumed fact.

LINEAGE: data independence / bisimulation up-to (the statement
shape); the anchored runner is the U18 `isAnchor` loop-head pattern
made total and predicate-parametric. -/

namespace GoLean.ChoiceErase

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-- One fueled step of the anchored walk: run until `anchor` fires
(checked BEFORE stepping, so the anchor configuration itself is not
executed), returning the step count, state, anchor configuration and
remaining stream. Fail-closed: fuel exhaustion, machine errors, and
termination without anchor all return `none`. -/
def anchorRun (anchor : Config → Bool) :
    Nat → Nat → ExecState → Config → Choices →
    Option (Nat × ExecState × Config × Choices)
  | 0, _, _, _, _ => none
  | fuel + 1, n, σ, c, ch =>
      if anchor c then some (n, σ, c, ch)
      else
        match stepFn σ c ch with
        | .ok (c', σ', ch') => anchorRun anchor fuel (n + 1) σ' c' ch'
        | .error _ => none

/-- The anchored run from a program setup (the closed form a kernel
link can evaluate: setup + walk are one computation over the pinned
program). -/
def anchorRunProg (fuel : Nat) (program : GoCore.Program)
    (entry : String) (anchor : Config → Bool) (ch : Choices) :
    Option (Nat × ExecState × Config × Choices) :=
  match runProgramSetupM 20000 program entry #[] ch with
  | .error _ => none
  | .ok (c₀, s₃, _, ch₁) => anchorRun anchor fuel 0 s₃ c₀ ch₁

/-- **THE CHOICE-INVARIANCE STATEMENT FORMER.** A span (from `σ₀`,
`C₀`, up to the first `anchor` configuration) is choice-invariant to
the representative `(σR, CR)` at root builder `roots` when EVERY
stream's anchored run lands at the SAME configuration with a
`~`-equivalent state. `roots` is a function of the landed state so
instantiations can name state-dependent root sets (in practice the
root set is a fixed shape — statics + the subject cell).

The conjuncts: the run EXISTS (fail-closed runner succeeded), the
anchor configuration is the representative's, and the state is
latitude-equivalent to the representative. -/
def ChoiceInvariantToM (m : Mask) (fuel : Nat) (σ₀ : ExecState)
    (C₀ : Config) (anchor : Config → Bool)
    (roots : ExecState → List GoValue) (σR : ExecState) (CR : Config) :
    Prop :=
  ∀ ch : Choices, ∃ n σ chR,
    anchorRun anchor fuel 0 σ₀ C₀ ch = some (n, σ, CR, chR) ∧
    CEquivM m σ (roots σ) σR (roots σR)

/-- The strict (empty-mask) form. -/
def ChoiceInvariantTo (fuel : Nat) (σ₀ : ExecState) (C₀ : Config)
    (anchor : Config → Bool) (roots : ExecState → List GoValue)
    (σR : ExecState) (CR : Config) : Prop :=
  ChoiceInvariantToM [] fuel σ₀ C₀ anchor roots σR CR

/-- A single stream's instance of the former — the shape witnesses
discharge (kernel-evaluable when everything is a literal). -/
def ChoiceInstanceAtM (m : Mask) (fuel : Nat) (σ₀ : ExecState)
    (C₀ : Config) (anchor : Config → Bool)
    (roots : ExecState → List GoValue) (σR : ExecState) (CR : Config)
    (ch : Choices) : Prop :=
  ∃ n σ chR,
    anchorRun anchor fuel 0 σ₀ C₀ ch = some (n, σ, CR, chR) ∧
    CEquivM m σ (roots σ) σR (roots σR)

theorem choiceInvariant_instance {m fuel σ₀ C₀ anchor roots σR CR}
    (h : ChoiceInvariantToM m fuel σ₀ C₀ anchor roots σR CR)
    (ch : Choices) :
    ChoiceInstanceAtM m fuel σ₀ C₀ anchor roots σR CR ch := h ch

/-- Any `CForm`-reader agrees across the whole invariant family with
its value at the representative (the consumer-facing corollary:
`absRead`-class facts proved once at the representative transfer to
EVERY stream's landed state). -/
theorem choiceInvariant_read {α : Type} {m : Mask} (read : CForm → α)
    {fuel σ₀ C₀ anchor roots σR CR}
    (h : ChoiceInvariantToM m fuel σ₀ C₀ anchor roots σR CR)
    (ch : Choices) :
    ∃ n σ chR,
      anchorRun anchor fuel 0 σ₀ C₀ ch = some (n, σ, CR, chR) ∧
      read (canonStateM m σ (roots σ))
        = read (canonStateM m σR (roots σR)) := by
  obtain ⟨n, σ, chR, hrun, hequiv⟩ := h ch
  exact ⟨n, σ, chR, hrun, readM_invariant m read hequiv⟩

end GoLean.ChoiceErase
