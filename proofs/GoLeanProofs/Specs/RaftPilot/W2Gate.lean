import GoLeanProofs.Specs.RaftPilot.CBecomeFollowerSpec
import GoLeanProofs.Frame.PlugRule
import GoLeanProofs.Frame.Threshold
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Specs.Raft.RenCongr
import GoLeanProofs.StepKit

/-!
# THE W2 GATE: `becomeFollower`'s CallSpec consumed at a REAL caller
site with STATE FRAMING — Leg B as intended (clean-proof plan §W1's
pilot leg, completed by W2's plug rule + compliant fixture)

The composition the W3 handler-into-driver assembly rests on,
end-to-end and measured:

* the CALLEE fact is the compliant-layout `cBecomeFollower_callSpec`
  (∀-state over the footprint carrier, ∀ env k, ∀ ch, ∃n) —
  instantiated at ONE concrete footprint member and at the CANONICAL
  anchor `([], .stop)`;
* the STATE half (the frame): `FrameSim (ρT 52 4)` carries the
  canonical member to a framed state `σFG` whose gap `[52,56)` holds
  the CALLER's locals — the receiver pointer `r` (pointing INTO the
  footprint), the two evaluated arguments `$c1567`/`$c1568`, and the
  unread `m` — the cells no admissible ρ could cover (W1 finding 1);
* the CONTROL half (the plug): `callSpan_plug` installs the real
  caller context `(envG, kG)` at the transported anchor span;
* the CALL SITE is REAL: the statement is `raft.stepCandidate`'s
  lowered MsgApp-case call VERBATIM from the pinned wire
  (`.call #[] ⟨raft.raft.becomeFollower⟩ #[.var "r", .var "$c1567",
  .var "$c1568"]`), `kG` carries the real next statement (the
  `handleAppendEntries` call) over the caller's frame;
* the readout is the READER-VOCABULARY postcondition at the framed
  terminal state via `absRaftNode_frameSim`.

Honest scope: the gate instance's σFG is a CONSTRUCTED framed state
(a Spec-precondition instance/∃-discharge, the unit-4 charter's
deliverable class), not a state reached by running the driver — the
init-spec/W3 chain supplies reachable states. The statics beyond the
one the span reads (`globalRand ⟨18⟩`) are absent from the instance's
heap; W3's production states carry them via the init spec.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.Frame

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000

/-! ## The instance: canonical member, frame cells, framed state -/

/-- The concrete footprint valuation (the `cBfPre_inhabited` member:
vote 7, lead 2, state 1, ldT 5, leadArg 4). -/
def gρ : Sym.Valuation :=
  { ints := fun i => [0, 7, 2, 1, 5, 0, 0, 0, 0, 4].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

/-- The canonical footprint member. -/
def σcG : ExecState := Sym.γS gρ wBase cS0

/-- The gate's placement: identity below the fixture top (52), shift
by the frame width (4) above. -/
def ρG : Nat → Nat := ρT 52 4

/-- The caller's locals — the frame heap in the gap `[52,56)`. -/
def frG : Heap :=
  [(.base ⟨52⟩, ⟨some (.pointer (.defined ⟨"raft.raft"⟩)),
      .addr (.base ⟨31⟩)⟩),
   (.base ⟨53⟩, ⟨some (.int .uint64), .int 0 .uint64⟩),
   (.base ⟨54⟩, ⟨some (.int .uint64), .int 4 .uint64⟩),
   (.base ⟨55⟩, ⟨some (.pointer (.defined ⟨"raftpb.Message"⟩)), .nil⟩)]

/-- The framed caller state: the ρG-image of the canonical member
plus the caller's locals. -/
def σFG : ExecState :=
  { σcG with
      heap := σcG.heap.map (fun p => (renameLoc ρG p.1, renameCell ρG p.2))
        ++ frG
      nextAddr := 56 }

/-! ## The REAL call site (verbatim from the pinned wire:
`raft.stepCandidate`, the MsgApp case) -/

def realCall : Stmt :=
  .call #[] ⟨"raft.raft.becomeFollower"⟩
    #[.var "r", .var "$c1567", .var "$c1568"]

/-- The caller environment at the site: the case-block temps over the
function's argument scope, bound into the frame gap. -/
def envG : LocalEnv :=
  [[("$c1567", .base ⟨53⟩), ("$c1568", .base ⟨54⟩)],
   [("r", .base ⟨52⟩), ("m", .base ⟨55⟩)]]

/-- The real continuation: the site's NEXT statement (the
`handleAppendEntries` call, verbatim) over the caller's own frame. -/
def kG : Cont :=
  .seq [.call #[] ⟨"raft.raft.handleAppendEntries"⟩
      #[.var "r", .var "m"]] envG
    (.frame [] [] [] [] .stop false)

/-! ## The FrameSim instance -/

private theorem hinjG : ∀ {x y : Nat}, ρG x = ρG y → x = y :=
  (shiftSpec_ρT 52 4).inj

/-- Renamed-heap lookup, generically: looking up a renamed key in a
key-and-cell-renamed heap finds the renamed cell. -/
private theorem lookup_map_rename {ρ : Nat → Nat}
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y) (h : Heap) (l : Loc) :
    Heap.lookup (h.map (fun p => (renameLoc ρ p.1, renameCell ρ p.2)))
        (renameLoc ρ l)
      = (Heap.lookup h l).map (renameCell ρ) := by
  induction h with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨l₁, c₁⟩ := p
      simp only [List.map_cons, Heap.lookup]
      by_cases he : l₁ = l
      · subst he
        simp
      · have h2 : renameLoc ρ l₁ ≠ renameLoc ρ l :=
          fun hc => he (renameLoc_inj hinj hc)
        simp only [beq_eq_false_iff_ne.mpr he, beq_eq_false_iff_ne.mpr h2,
          Bool.false_eq_true, if_false]
        exact ih

/-- The canonical heap's keys sit below 52 (kernel facts at the four
frame keys). -/
private theorem mapped_none_52 :
    Heap.lookup (σcG.heap.map
      (fun p => (renameLoc ρG p.1, renameCell ρG p.2))) (.base ⟨52⟩)
      = none := by kernel_rfl
private theorem mapped_none_53 :
    Heap.lookup (σcG.heap.map
      (fun p => (renameLoc ρG p.1, renameCell ρG p.2))) (.base ⟨53⟩)
      = none := by kernel_rfl
private theorem mapped_none_54 :
    Heap.lookup (σcG.heap.map
      (fun p => (renameLoc ρG p.1, renameCell ρG p.2))) (.base ⟨54⟩)
      = none := by kernel_rfl
private theorem mapped_none_55 :
    Heap.lookup (σcG.heap.map
      (fun p => (renameLoc ρG p.1, renameCell ρG p.2))) (.base ⟨55⟩)
      = none := by kernel_rfl

private theorem hsupG :
    GoCore.Machine.funcListSup σcG.functions.toList ≤ 52 := by
  have h31 : GoCore.Machine.funcListSup σcG.functions.toList = 31 := by
    kernel_rfl
  omega

/-- **The gate's frame instance**: the canonical member simulates the
framed caller state with the caller's locals as the frame. -/
theorem frameSimG : FrameSim ρG 52 56 frG σcG σFG := by
  refine ⟨shiftSpec_ρT 52 4, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- next_eq: 56 = ρG (σcG.nextAddr) = ρG 52
    show σFG.nextAddr = ρG σcG.nextAddr
    rw [show σcG.nextAddr = 52 from rfl]
    rfl
  · -- alloc_reg
    show 52 ≤ σcG.nextAddr
    rw [show σcG.nextAddr = 52 from rfl]
    exact Nat.le_refl 52
  · -- lookup_img
    intro l
    show Heap.lookup σFG.heap (renameLoc ρG l) = _
    have hmap := lookup_map_rename hinjG σcG.heap l
    cases hl : Heap.lookup σcG.heap l with
    | some c =>
        rw [hl] at hmap
        exact lookup_append_left hmap
    | none =>
        rw [hl] at hmap
        exact lookup_append_right hmap
  · -- frame_pres
    intro l c hl
    have hnone : Heap.lookup (σcG.heap.map
        (fun p => (renameLoc ρG p.1, renameCell ρG p.2))) l = none := by
      by_cases h52 : l = .base ⟨52⟩
      · subst h52; exact mapped_none_52
      · by_cases h53 : l = .base ⟨53⟩
        · subst h53; exact mapped_none_53
        · by_cases h54 : l = .base ⟨54⟩
          · subst h54; exact mapped_none_54
          · by_cases h55 : l = .base ⟨55⟩
            · subst h55; exact mapped_none_55
            · exfalso
              simp only [frG] at hl
              rw [lookup_cons_ne (beq_false_of_ne (fun h => h52 h.symm)),
                lookup_cons_ne (beq_false_of_ne (fun h => h53 h.symm)),
                lookup_cons_ne (beq_false_of_ne (fun h => h54 h.symm)),
                lookup_cons_ne (beq_false_of_ne (fun h => h55 h.symm))]
                at hl
              cases hl
    show Heap.lookup (σcG.heap.map
      (fun p => (renameLoc ρG p.1, renameCell ρG p.2)) ++ frG) l = some c
    rw [lookup_append_right hnone]
    exact hl
  · -- fr_avoid
    intro a
    by_cases ha : a < 52
    · rw [show ρG a = a from ρT_lt ha]
      show Heap.lookup frG (.base ⟨a⟩) = none
      simp only [frG]
      rw [lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega))]
      rfl
    · rw [show ρG a = a + 4 from ρT_ge (by omega)]
      show Heap.lookup frG (.base ⟨a + 4⟩) = none
      simp only [frG]
      rw [lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega))]
      rfl
  · -- bodies_inv
    exact renameBodies_id (fun x hx => ρT_lt hx) hsupG

/-! ## The gate assembly -/

/-- The canonical anchor configuration (the c-spec's span start at
`([], .stop)`). -/
def anchorG : Config :=
  .retV (.int 4 .uint64)
    (.callArgsK ⟨"raft.raft.becomeFollower"⟩ []
      [.addr (.base ⟨31⟩), .int 0 .uint64] [] [] .stop)

private theorem renameConfig_anchor : renameConfig ρG anchorG = anchorG := by
  kernel_rfl

/-- The non-wrapper witness at the framed entry. -/
private def wrapOfG : Bool :=
  match enterFrame σFG ⟨"raft.raft.becomeFollower"⟩
      [.addr (.base ⟨31⟩), .int 0 .uint64, .int 4 .uint64] with
  | .ok (f, _, _, _) => f.wrapper
  | .error _ => false

private theorem wrapOfG_false : wrapOfG = false := by kernel_rfl

private theorem hnwG : ∀ (func : Func) (fenv : LocalEnv) (rls : List Loc)
    (σe : ExecState),
    enterFrame σFG ⟨"raft.raft.becomeFollower"⟩
      ([.addr (.base ⟨31⟩), .int 0 .uint64] ++ [.int 4 .uint64])
      = .ok (func, fenv, rls, σe) →
    func.wrapper = false := by
  intro func fenv rls σe h
  rw [show (([.addr (.base ⟨31⟩), .int 0 .uint64] ++ [.int 4 .uint64] :
      List GoValue))
      = [.addr (.base ⟨31⟩), .int 0 .uint64, .int 4 .uint64] from rfl] at h
  have hw := wrapOfG_false
  unfold wrapOfG at hw
  rw [h] at hw
  exact hw

/-- The REAL site's argument-evaluation segment: six machine steps
from the verbatim call statement to the drained configuration —
reading the caller's locals out of the FRAME cells. -/
private theorem hargsG (ch : Choices) :
    stepFnIter 6 σFG (.exec realCall envG kG) ch
      = .ok (.retV (.int 4 .uint64)
          (.callArgsK ⟨"raft.raft.becomeFollower"⟩ []
            [.addr (.base ⟨31⟩), .int 0 .uint64] [] envG kG),
          σFG, ch) := by
  kernel_rfl

set_option maxHeartbeats 256000000 in
/-- **THE W2 GATE — Leg B as intended.** The verbatim
`raft.stepCandidate` MsgApp-case call statement, at the framed caller
state (the callee's footprint at the compliant placement + the
caller's locals in the frame gap), over the REAL continuation (the
`handleAppendEntries` call over the caller's frame), at EVERY choice
stream: the span completes to `.next kG` and the framed terminal
state reads back exactly the spec handler's result. Composed from
`cBecomeFollower_callSpec` (the callee fact) + `frameSimG`/
`stepFnIter_sim` (the state half) + `callSpan_plug` (the control
half) + `absRaftNode_frameSim` (the reader transport). -/
theorem w2_gate (ch : Choices) :
    ∃ (n : Nat) (σ' : ExecState) (ch' : Choices),
      stepFnIter n σFG (.exec realCall envG kG) ch
        = .ok (.next kG, σ', ch')
      ∧ ch' <:+ ch
      ∧ absRaftNode σ' ⟨31⟩
          = some (specBecomeFollower ⟨0, 7, 2, 1, 1, 1⟩ 0 4) := by
  -- the canonical span at the anchor
  have hP : CBfPre 7 2 1 5 4 σcG :=
    ⟨gρ, wBase, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨n, σc', chc', hrun, hpost, hsuf⟩ :=
    cBecomeFollower_callSpec 7 2 1 5 4 (by decide) (by decide)
      σcG hP [] .stop ch
  -- transport the anchor span to the framed state
  have htr := stepFnIter_sim (ρ := ρG) (na₀ := 52) (na := 56) (fr := frG)
    n frameSimG anchorG ch
  have hrun' : stepFnIter n σcG anchorG ch
      = .ok (.next .stop, σc', chc') := hrun
  obtain ⟨bF, hbF, htrip⟩ := ExSim.ok_inv htr hrun'
  obtain ⟨cF', σF₁, chF'⟩ := bF
  obtain ⟨hc1, hsim1, hc3⟩ := htrip
  dsimp only at hc1 hsim1 hc3
  rw [renameConfig_anchor] at hbF
  rw [show renameConfig ρG (.next .stop) = .next .stop from rfl] at hc1
  rw [hc1, hc3] at hbF
  -- plug the real caller context into the framed anchor span
  have hplugged := callSpan_plug (env' := envG) (k' := kG)
    (by rfl) (by rfl) hnwG hbF
  -- chain the real site's argument segment
  refine ⟨6 + n, σF₁, chc', ?_, hsuf, ?_⟩
  · exact stepFnIter_chain (hargsG ch) hplugged
  · have := absRaftNode_frameSim hsim1 31 hpost
    rwa [show ρG 31 = 31 from rfl] at this

end GoLean.RaftSeam
