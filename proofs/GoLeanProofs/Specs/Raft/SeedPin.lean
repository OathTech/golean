import GoLeanProofs.Specs.Raft.SeedLit
import GoLeanProofs.Specs.Raft.SeedCFormLit
import GoLeanProofs.Specs.Raft.BecomeFollowerWitness
import GoLeanProofs.Specs.Raft.RoundStatement
import GoLeanProofs.Specs.Raft.NativeS1Chain
import GoLeanProofs.Frame.ChoiceInv
import GoLeanProofs.Sym.KernelRfl

/-! # THE SEED PIN (SP1, campaign lane arc4c) — the representative
post-init state, its abstract readout `N₀`, and the init span's
choice-invariance statement

## What this module pins

The C-ladder's BASE CASE: the pinned twin's state at the POST-INIT
PRE-CAMPAIGN anchor — the first `main.twin.step` call configuration
(twin-chdriver.go: `newTwin(3,2)` → say → `t.step(op{opCampaign,1})`),
reached from the seeded start in **81,261 steps consuming 171
choices** (canonical all-zero stream; U18's init census, replicated
independently by this unit's probe to the step). The representative
literal is `seedσ` (`SeedLit.lean`, generator
`artifacts/probe/SeedLitGen.lean`); the abstract side is `seedN₀ :
SNet` — three followers at term 0, no votes, empty ghost — which
DISCHARGES the native chain's `Seed` hypothesis (`seed_N₀` below),
the hypothesis `native_one_leader_per_term` consumes.

## The trust story — what IS and IS NOT kernel-checked (bluntly)

Kernel-checked in this module, on every build:
- `seed_setup_link` — the CLOSED setup computation (`runProgramSetupM`
  on the pinned `twinLowered`: seeding + the full 1,382-step
  `$pkginit`) equals the setup literal EXACTLY (the StaticCells
  closed-link idiom; measured ≈ 120 s kernel);
- `seed_front_link` — the init span's first 300 steps from the setup
  literal land on the front-boundary literal (`stepFnIter`, empty
  stream = the canonical member by the exhaustion rule);
- the ENDPOINT READOUTS — `absTwinRead`/`absTwinNodeRaft`/lens reads
  over `seedσ`: checker counters 0, three follower shells
  (state 0, term 0), empty net, per-node raft `Term`/`Vote`/`lead`/
  `state` all 0 — the exact content `seedN₀` abstracts;
- `seed_inFam` — family membership at the identity placement
  (`RoundFam.self`); `SeedFam` is defined as `RoundFam seedσ`, the
  R-form family anchored at the representative;
- `seed_clean` — the masked canonical form of `seedσ` is CLEAN
  (no fail-closed flags) with its measured shape (207 live cells out
  of 4,965 — init garbage is quotiented away by `~`).
GENERATOR-VERIFIED ONLY (compiled `stepFn` walk, probe-replicated
4× against U18/Arc-2 numbers, NOT kernel-replayed): the init span's
steps 300–81,261. The kernel-completion route of record: mirror
window chains (the C-wave's instrument, ≈35–45 min kernel at
measured ring rates) or FastEval reflection at the arc-2 merge
(Arc 2 unit 4's anchor equation is exactly this instrument);
recorded, not owed by this unit's charter.

## The mask (`twinLatMask`) and its justification obligations

The init probe (log, slice 1) REFUTED the strict
relocation×capacity-slack `~` at exactly 3 of 171 init draws: the
per-node `resetRandomizedElectionTimeout` picks, whose drawn value
persists as `raft.raft.randomizedElectionTimeout`. The pin therefore
uses the MASKED equivalence at the ONE-FIELD mask
`twinLatMask = [(raft.raft, randomizedElectionTimeout)]`. The mask's
justification, each part on the record:
1. the field's ONLY subject reader is `pastElectionTimeout`
   (deps/raft/raft.go:2050), consumed exclusively on tick paths;
2. the driver NEVER ticks (twin-chdriver.go's stated design; U18's
   structural reachability refutation — no `Tick` calls, so no
   election-timeout reads on ANY stream);
3. the landed equation layer already classifies exactly this field
   as a latitude-bearing spot no abstract reader consumes
   (BfEquation.lean:22 — the pick-quantified becomeFollower span).
Masking is VISIBLE (`CVal.masked` in the form) — the masked
equivalence is a different Prop from the strict one by construction.

## The choice-invariance statement (`seedLift`)

`SeedChoiceInvariance` states the init span's ∀-stream lift: EVERY
choice stream's anchored run lands at THE SAME configuration `seedC`
with a state `~ₘ`-equivalent to `seedσ`. Its standing (stated so the
docstring never overclaims): the probe measured all 171
single-position deviations (both site classes, both value sweeps)
plus multi-class combined streams landing `~ₘ`-equal, and
`SeedWitness.lean` KERNEL-checks a combined non-canonical instance
(different capacities included); the GENERAL ∀ discharge is
bisimulation-up-to-`~` — the future symbolic semantics' erased half
per the standing [USER] design decisions (campaign log 2026-08-27),
scheduled post-T1. Consumers take `SeedChoiceInvariance` as a NAMED
premise (`seed_absRead_invariant` shows the consumption shape);
nothing in this module asserts it proved.

LINEAGE: refinement-mapping seed + closed-computation link pin
(StaticCells idiom); bisimulation up-to / data independence for the
lift statement; CompCert-block-naming for the `~` carrier. -/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.ChoiceErase
open GoLean.RaftSeam.NativeSpec

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## 1. The representative and its anchor -/

/-- The post-setup state: the twin's tables + the post-`$pkginit`
heap literal. `seed_setup_link` proves this IS `runProgramSetupM`'s
output on the pinned program — nothing about it is trusted from the
generator. -/
def seedSetupσ : ExecState :=
  { wBase with heap := seedSetupHeap, nextAddr := seedSetupNa }

def seedResultLocs : List Loc :=
  [.base ⟨98⟩, .base ⟨99⟩, .base ⟨100⟩, .base ⟨101⟩, .base ⟨102⟩]

/-- The post-init anchor predicate: about to CALL `main.twin.step`
(the campaign event — everything before it is init). -/
def seedAnchor : Config → Bool
  | .exec (.call _ fid _) _ _ => fid.key == "main.twin.step"
  | _ => false

/-- **The representative post-init state** (the seed literal). -/
def seedσ : ExecState := { wBase with heap := seedHeap, nextAddr := seedNa }

/-- The front-sliver boundary state (step 300 of the init span). -/
def seedFrontσ : ExecState :=
  { wBase with heap := seedFrontHeap, nextAddr := seedFrontNa }

/-- The twin struct's address in the seeded run (probe-located by
shape; every readout below re-verifies its consequences). -/
def seedTwinLoc : Loc := .base ⟨121⟩

/-- The seed root set: the statics region (every cell a `locLit` in
the pinned program text can reach, [0, setup na)) plus the twin
cell. -/
def seedRoots : List GoValue :=
  ((List.range seedSetupNa).map (fun a => GoValue.addr (.base ⟨a⟩))) ++
  [GoValue.addr seedTwinLoc]

/-- **The declared latitude mask** — exactly one field; justification
obligations in the module docstring (reader census + no-tick
reachability + the BfEquation precedent). -/
def twinLatMask : Mask := [(⟨"raft.raft"⟩, "randomizedElectionTimeout")]

/-! ## 2. The kernel links (the U12 closed-computation idiom) -/

/-- **THE SETUP LINK**: seeding + the full `$pkginit` run on the
pinned program, kernel-recomputed against the literal on every build
(the empty stream is the canonical member — exhaustion draws slot 0).
≈120 s kernel, measured. -/
theorem seed_setup_link :
    runProgramSetupM 20000 GoLean.Examples.RaftTwin.twinLowered
      "twinChoiceVerdict" #[] []
      = .ok (seedSetupC, seedSetupσ, seedResultLocs, []) := by kernel_rfl

/-- **THE FRONT SLIVER**: the init span's first 300 steps from the
setup literal (zero draws in [0,300) — the first init draw sits at
step 495), kernel-replayed. -/
theorem seed_front_link :
    stepFnIter seedFrontN seedSetupσ seedSetupC []
      = .ok (seedFrontC, seedFrontσ, []) := by kernel_rfl

/-! ## 3. The endpoint readouts (kernel-evaluated over `seedσ`) -/

/-- PRE-CAMPAIGN abstract readout: checker counters ZERO, three
follower shells (state 0, term 0, commit 0, applied 0 at the harness
shells), and an EMPTY net — the abstract content `seedN₀` carries. -/
theorem seed_absRead :
    absTwinRead seedσ seedTwinLoc
      = some { violations := 0, claims := 0, committed := 0,
               nodes := [(0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)],
               net := [] } := by kernel_rfl

/-- The three per-node deep raft reads: `Term`/`Vote`/`lead`/`state`
all 0 at every node — no leader, no vote, term 0 (the `Seed`
conditions at the concrete state). -/
theorem seed_nodes_zero :
    (List.range 3).map (fun i =>
      (absTwinNodeRaft seedσ seedTwinLoc i).map (fun a =>
        (GoLean.Lens.fieldReadU64 seedσ a ⟨"raft.raft"⟩ "Term",
         GoLean.Lens.fieldReadU64 seedσ a ⟨"raft.raft"⟩ "Vote",
         GoLean.Lens.fieldReadU64 seedσ a ⟨"raft.raft"⟩ "lead",
         GoLean.Lens.fieldReadU64 seedσ a ⟨"raft.raft"⟩ "state")))
    = [some (some 0, some 0, some 0, some 0),
       some (some 0, some 0, some 0, some 0),
       some (some 0, some 0, some 0, some 0)] := by kernel_rfl

/-! ## 4. Family membership (the R-form base) -/

/-- **The seed family**: the R-form family anchored at the
representative (`RoundFam` = FrameSim placement — the arm equations'
placement premise, one ring up; RoundStatement.lean §1). -/
def SeedFam (σF : ExecState) : Prop := RoundFam seedσ σF

/-- The representative is a member at the identity placement. -/
theorem seed_inFam : SeedFam seedσ := RoundFam.self seedσ

/-! ## 5. The canonical form (the `~ₘ` side) -/

/-- **THE CANONICAL-FORM PIN**: the representative's masked canonical
form kernel-recomputed against the pinned literal (`SeedCFormLit`) on
every build. Comparisons against the form route THROUGH this pin
(never head-on between two computed forms — the U21
representation-asymmetry lesson applied at the `~` layer: the
witness's equivalence is two pins sharing one literal). -/
theorem seed_cform_pin :
    canonStateM twinLatMask seedσ seedRoots = seedCForm := by kernel_rfl

/-- The masked canonical form of the representative is CLEAN — no
fail-closed refusals (no fuel exhaustion, no unsortable map keys, no
non-zero-like trimmed tails, no mixed references, view fixpoint
stable). -/
theorem seed_clean :
    (canonStateM twinLatMask seedσ seedRoots).flags = [] := by
  rw [seed_cform_pin]; rfl

/-- The live-state shape: 207 canonical cells out of the 4,965-cell
post-init heap — the `~` quotient drops init's allocation garbage. -/
theorem seed_cform_cells :
    (canonStateM twinLatMask seedσ seedRoots).cells.length = 207 := by
  rw [seed_cform_pin]; rfl

/-! ## 6. The abstract seed `N₀` and the `Seed` discharge -/

/-- The boot ENode: follower (state 0), term 0, no vote, no lead, the
snapshot-boot log [(1,1)] with committed 1 (the twin boots from a
snapshot at index 1 term 1 — U21's boot-log decode), empty tally. -/
def seedBootNode : ENode :=
  { state := 0, term := 0, vote := 0, lead := 0,
    log := [(1, 1)], committed := 1, votesRec := [] }

/-- **`N₀`** — the abstract seed net: every node at the boot state,
empty ghost. The concrete correspondence: `seed_absRead` (three
follower shells, counters zero, empty net) + `seed_nodes_zero`
(per-node Term/Vote/lead/state all 0). -/
def seedN₀ : SNet :=
  { node := fun _ => seedBootNode,
    ghost := { votes := fun _ => [], victories := [] } }

/-- **THE `Seed` DISCHARGE** — the native chain's hypothesis
(`NativeS1Chain.Seed`), consumed by `native_one_leader_per_term` and
every `GoodReach` skeleton: no ghost votes (empty ghost by
construction), no leaders (state 0 ≠ 2 everywhere). -/
theorem seed_N₀ : Seed seedN₀ := by
  constructor
  · intro v t c h
    simp [seedN₀] at h
  · intro i
    simp [seedN₀, seedBootNode]

/-! ## 7. The init span's choice-invariance statement (the lift) -/

/-- The init-span walk fuel (the span is 81,261 steps; 200,000 gives
slack without changing which runs land — `anchorRun` stops at the
FIRST anchor hit). -/
def seedFuel : Nat := 200000

/-- **THE CHOICE-INVARIANCE STATEMENT for the init span** (the
lift): every stream's anchored run from the (kernel-linked) setup
state lands at `seedC` with a `~ₘ`-equivalent state. STANDING: probe-
measured at all 171 single-position deviations + combined streams;
kernel-witnessed at a combined non-canonical stream
(`SeedWitness.lean`); general discharge = the symbolic semantics'
bisimulation (post-T1). Consumers name this Prop as a premise. -/
def SeedChoiceInvariance : Prop :=
  ChoiceInvariantToM twinLatMask seedFuel seedSetupσ seedSetupC
    seedAnchor (fun _ => seedRoots) seedσ seedC

/-- The consumption shape: under the lift, EVERY stream's post-init
state answers any canonical-form reader exactly as the representative
does (readers are `~ₘ`-invariant by construction — the
representation-engineering form). -/
theorem seed_absRead_invariant {α : Type} (read : CForm → α)
    (h : SeedChoiceInvariance) (ch : Choices) :
    ∃ n σ chR,
      anchorRun seedAnchor seedFuel 0 seedSetupσ seedSetupC ch
        = some (n, σ, seedC, chR) ∧
      read (canonStateM twinLatMask σ seedRoots)
        = read (canonStateM twinLatMask seedσ seedRoots) :=
  choiceInvariant_read read h ch

end GoLean.RaftSeam
