import GoLeanProofs.Specs.ChanRendezvous

/-!
# PERMANENT WARNING FIXTURE: a frame-quantified triple for a program
# that always deadlocks (channel-logic S1 audit, 2026-08-11)

**Negative knowledge — keep forever.** This module proves, through the
SHIPPED channel laws and the shipped exit, a full frame-quantified
`GoTripleC` for a program the interpreter classifies `.deadlock` on
every schedule (`deadlockRecvDeadlocks` below is the boring executable
fact). Nothing here is a bug: `GoTripleC` is RUN-CONDITIONED partial
correctness (`Surface.lean` — every premise chain starts from
`execProg … = .ok (.normal σf, _)`), so a program with no completing
runs satisfies ANY triple vacuously, by design. What this module
demonstrates, permanently:

- **A channel triple ALONE certifies nothing about communication,
  liveness, or deadlock.** The S1 design note's original §3 claimed
  the nil-park/vacuous-triple route was "closed off" by the pipe —
  FALSE (the S1 audit's major): `StepDC.pairRelease` ∃-quantifies the
  entire imagined pool, `applyPairing`'s PARTNER patterns match the
  partner's channel with a wildcard, and `isBlockedConfig` does not
  inspect the channel — so nil parks and never-matched parks are both
  spinnable and releasable, and the WP walk goes through
  (`nilParkSpins`/`nilParkReleases`/`crossChannelSendRelease` below
  pin the three envelope members the corrected note §1a/§3 cites).
- **The protection is the BORING EXECUTABLE ANCHOR** (user doctrine
  2026-08-11, the TCB-grounding principle): every soundness-carrying
  channel-triple bundle must ship its ∃-completion member
  (`TerminatesNormallyC`-class — a semantically trivial property of
  the interpreter, discharged by kernel evaluation), and the Iris /
  Löb / simulation machinery is untrusted METHOD only. The
  completion-pin gate in `Audit.lean` enforces the pairing
  structurally; THIS module is its negative-test fixture — it
  declares a `GoTripleC` with (necessarily) no completion pin, and
  the gate's negative test asserts the checker flags exactly it.

Provenance: the S1 audit verifier's reproductions (probes B/C and
V1a/V1b, rebuilt independently of the reviewer's files); committed as
tracked fixtures at the operator's direction.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface

namespace GoLean.Iris

/-- Receive on a rendezvous channel NOBODY sends on: deadlocks on
every schedule. -/
abbrev deadlockRecvProg : Stmt := .seqn #[.chanRecv #[] (.var "chv") .int]
abbrev deadlockRecvEnv : LocalEnv := [[("chv", .base ⟨1⟩)]]
abbrev deadlockRecvPre : HProp :=
  .sep (.pointsTo 1 rdvHandleCell) (.pointsTo 2 rdvChanCell)
abbrev deadlockRecvPost : HProp := .pointsTo 1 rdvHandleCell

def deadlockRecvSeed : ExecState :=
  { types := [], functions := #[], methods := #[],
    heap := [(.base ⟨1⟩, rdvHandleCell), (.base ⟨2⟩, rdvChanCell)],
    nextAddr := 3 }

/-- **THE BORING FACT** (the trusted half of this fixture, interpreter
vocabulary only, kernel-evaluated): the program deadlocks — under the
canonical stream, and `.deadlock` is stream-independent here (one
goroutine, no choice site ever consumed). This is what the triple
below is compatible with. -/
theorem deadlockRecvDeadlocks :
    (match execProg 200 deadlockRecvEnv deadlockRecvSeed {} deadlockRecvProg
      with
      | .error .deadlock => true
      | _ => false) = true := by
  decide +kernel

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

set_option maxHeartbeats 1600000 in
/-- The walk: exactly the shipped laws — the receive parks, the parked
law's (necessarily phantom — no other thread exists) release branch
delivers `.next k`, main "completes". Every step is honest about the
D-Language's wider envelope; the falsehood would be CLAIMING the
triple certifies the run. -/
theorem wpD_deadlockRecv_witness :
    embed (GF := GF) deadlockRecvPre
      ⊢ WP (PoolCfgD.mk (.exec deadlockRecvProg deadlockRecvEnv .stop))
        {{ _v, embed (GF := GF) deadlockRecvPost }} := by
  iintro HP
  simp only [deadlockRecvPre, deadlockRecvPost, embed]
  icases HP with ⟨H1, H2⟩
  iapply fupd_wp
  imod inv_alloc rdvN ⊤ (iprop((2 : Nat) ↦ rdvChanCell)) $$ [H2] with Hinv
  · inext
    iexact H2
  icases Hinv with #Hinv
  imodintro
  iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.seqn)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all [stmtPlan, chanPlan, syncPlan]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred1
  simp only [seqCont]
  iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.seqNext)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred2
  iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.chanStFirst rfl)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;>
        simp_all [stmtPlan, chanPlan, syncPlan, targetsPlan, targetPlan]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred3
  iapply (wpD_eval_var (a := ⟨1⟩) (cell := rdvHandleCell) (hres := rfl))
  isplitl [H1]
  · iexact H1
  iintro H1
  iapply (wpD_recv_nil_rendezvous_inv (a := ⟨2⟩) (cell := rdvChanCell)
    (hN := CoPset.subseteq_top) (hcv := rfl))
  isplitl []
  · iexact Hinv
  iintro %c₂ %hc₂
  rcases hc₂ with rfl | rfl
  · iapply (wpD_blocked_recv_nil_rendezvous_inv (a := ⟨2⟩)
      (cell := rdvChanCell) (hN := CoPset.subseteq_top) (hcv := rfl))
    isplitl []
    · iexact Hinv
    iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.seqDone)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred4
    iapply (wp_value' (v := ()))
    iexact H1
  · iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.seqDone)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred5
    iapply (wp_value' (v := ()))
    iexact H1

end

/-- **THE VACUOUS TRIPLE** — true, axiom-identical to the real
exemplars, and compatible with a program that never completes
(`deadlockRecvDeadlocks`). The reason exported channel triples ship
ONLY inside a bundle with their completion pin (the Audit gate). -/
theorem deadlockRecvTripleC :
    GoTripleC [] #[] #[] deadlockRecvEnv deadlockRecvPre deadlockRecvProg
      deadlockRecvPost :=
  goTripleC_of_wpD (fun _hprog _hmeths _htypes => wpD_deadlockRecv_witness)

/-! ## The envelope members the corrected note cites (S1 audit
verifier probes V1a/V1b/B, tracked) -/

/-- A NIL-channel park is REDUCIBLE (spins) whenever the state holds
any empty-buffer channel cell — `isBlockedConfig` does not inspect the
channel, so the shipped `stepDC_parked_spin` applies verbatim.
(Refutes the original note's "a nil-parked thread is IRREDUCIBLE".) -/
theorem nilParkSpins {σ : ExecState} {loc : Loc} {cap : Nat}
    {closed : Bool} {targets : List Assignee} {elem : Ty} {env : LocalEnv}
    {k : Cont}
    (hload : loadLoc σ loc = .ok (.chanData #[] cap closed)) :
    StepDC (.blockedRecv none targets elem env k) σ
      (.blockedRecv none targets elem env k) σ [] :=
  stepDC_parked_spin (by simp [isBlockedConfig]) hload

/-- A NIL-channel zero-target park is moreover RELEASABLE to `.next k`:
`applyPairing`'s partner patterns wildcard the partner's channel, so
the ∃-pool can seat the nil park at the partner index of a
real-channel handoff. (Refutes "no `applyPairing` arm matches a
`none` loc" as a premise about the PARTNER side — it is true of the
ARRIVING side only.) -/
theorem nilParkReleases {σ : ExecState} {loc : Loc} {cap : Nat}
    {closed : Bool} {elem : Ty} {env : LocalEnv} {k : Cont}
    (hload : loadLoc σ loc = .ok (.chanData #[] cap closed)) :
    StepDC (.blockedRecv none [] elem env k) σ (.next k) σ [] := by
  have hcell : chanCell σ loc = .ok (#[], cap, closed) := by
    unfold chanCell
    rw [hload]
    rfl
  refine StepDC.pairRelease (by simp [isBlockedConfig])
    ⟨σ, #[.blockedSend (some loc) (.bool false) .stop,
          .blockedRecv none [] elem env k],
      0, 1, .blockedSend (some loc) (.bool false) .stop,
      [(0, .opWaiter 1)], 0,
      ((#[.blockedSend (some loc) (.bool false) .stop,
          .blockedRecv none [] elem env k] : Array Config).setIfInBounds
            0 (.next .stop)).setIfInBounds 1 (.next k),
      (by decide), rfl, (by omega), ?_, ?_⟩
  · show applyPairing σ _ 0 (.blockedSend (some loc) (.bool false) .stop)
      (0, .opWaiter 1) = _
    simp only [applyPairing]
    rw [show (#[Config.blockedSend (some loc) (.bool false) .stop,
        Config.blockedRecv none [] elem env k] : Array Config)[1]?
      = some (.blockedRecv none [] elem env k) from rfl]
    rw [hcell]
    simp [Bind.bind, Except.bind, resumeRecvDelivery, Array.isEmpty]
  · rfl

/-- A parked SENDER releases to `.next k` off a pairing on a DIFFERENT
channel: the release can be wholly PHANTOM — no partner, no handoff,
no delivery, no cell write (the sender's own channel `locB` is never
read; only the imagined arriving receiver's `locA` is). The reason a
release to `.next k` carries NO delivery information — the corrected
parked-law docstrings and P-CL1-1/P-CL1-3 rest on this. -/
theorem crossChannelSendRelease {σ : ExecState} {locA locB : Loc}
    {cap : Nat} {closed : Bool} {v : GoValue} {k : Cont}
    (hload : loadLoc σ locA = .ok (.chanData #[] cap closed)) :
    StepDC (.blockedSend (some locB) v k) σ (.next k) σ [] := by
  have hcell : chanCell σ locA = .ok (#[], cap, closed) := by
    unfold chanCell
    rw [hload]
    rfl
  refine StepDC.pairRelease rfl
    ⟨σ, #[.blockedRecv (some locA) [] (.bool) [] .stop,
          .blockedSend (some locB) v k],
      0, 1, .blockedRecv (some locA) [] (.bool) [] .stop,
      [(0, .opWaiter 1)], 0,
      ((#[.blockedRecv (some locA) [] (.bool) [] .stop,
          .blockedSend (some locB) v k] : Array Config).setIfInBounds
            0 (.next .stop)).setIfInBounds 1 (.next k),
      (by decide), rfl, (by omega), ?_, ?_⟩
  · show applyPairing σ _ 0 (.blockedRecv (some locA) [] (.bool) [] .stop)
      (0, .opWaiter 1) = _
    simp only [applyPairing]
    rw [show (#[Config.blockedRecv (some locA) [] (.bool) [] .stop,
        Config.blockedSend (some locB) v k] : Array Config)[1]?
      = some (.blockedSend (some locB) v k) from rfl]
    rw [hcell]
    simp [Bind.bind, Except.bind, resumeRecvDelivery, Array.isEmpty]
  · rfl

end GoLean.Iris
