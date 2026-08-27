import GoLeanProofs.Specs.RaftPilot.BfSortStep
import GoLeanProofs.SpecJudgment
import GoLeanProofs.Sym.ReflectConc
import GoLeanProofs.Specs.Raft.AbsState

/-!
# W1 pilot LEG A: becomeFollower's function Spec, end-to-end through
the judgment + rules

The pilot gate's first leg (clean-proof plan §W1): `becomeFollower`'s
`CallSpec` — precondition and postcondition in READER vocabulary
(`absRaftNode` + the footprint carrier), proved end-to-end via the
judgment and the driver pattern (open-tail windows + choice-crossing
transports + the reflection retraction).

**The exported statements are count-free** (∃n in the judgment; no
measured span length, no fixture identity beyond the canonical
footprint the precondition itself denotes). The count-bearing
composition (`bf_full_span`, the window links) is PRIVATE proof-body
scaffolding inside the Pilot modules, labeled at birth, consumed
only here — the plan's "the arc4d span walks become the specs' proof
bodies under the driver", with the W1 open-tail transformation
supplying the judgment's ∀ env k and the `headD`/`tail` stream forms
supplying the judgment's ∀ ch (short streams included — exhaustion
draws 0 without popping).

**Scope, honest**: the footprint is the CANONICAL placement (the
fixture's addresses; the raft cell at `⟨0⟩`) — the placement/frame
transport to arbitrary layouts is the recorded W3 obligation (design
note §3 findings 1 and 3). The term-change branch (`term ≠ 0`) is
the recorded arc4d residual, unchanged. Non-vacuity: `BfPre`'s
inhabitant (`bfPre_inhabited`) is the ∃-discharge; the judgment's
instance is THIS spec.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-- Iterated `uint64` normalize — the shape store-time
re-normalization leaves on the raft cell's symbolic scalars (every
whole-struct write re-wraps them). -/
def unrm : Nat → Int → Int
  | 0, v => v
  | n + 1, v => IntKind.normalize .uint64 (unrm n v)

theorem unrm_id {v : Int} (h : IntKind.normalize .uint64 v = v) :
    ∀ n, unrm n v = v
  | 0 => rfl
  | n + 1 => by rw [unrm, unrm_id h n, h]

/-- The composed becomeFollower span (PRIVATE scaffolding: the
count-bearing whole-handler walk — 7 open-tail windows chained
through the 6 stream-total crossings; never exported, consumed only
by the count-free `CallSpec` below). -/
private theorem bf_full_span (tenv : LocalEnv) (k : SymCont)
    (ρ : Valuation) (σ : ExecState) (hag : bfTB.Agrees σ)
    (ch : Choices) :
    stepFnIter 3234
      (γS (uρ' ρ (ch.headD 0) (ch.tail.headD 0) (ch.tail.tail.headD 0))
        σ uS0)
      (γC (uρ' ρ (ch.headD 0) (ch.tail.headD 0) (ch.tail.tail.headD 0))
        (uC0 tenv k)) ch
      = .ok (.next (γK (uρ' ρ (ch.headD 0) (ch.tail.headD 0)
              (ch.tail.tail.headD 0)) k),
          γS (uρ' ρ (ch.headD 0) (ch.tail.headD 0) (ch.tail.tail.headD 0))
            σ uS13,
          ch.tail.tail.tail.tail) := by
  have w1 := fun chx => uWin1 tenv k (uρ' ρ (ch.headD 0) (ch.tail.headD 0) (ch.tail.tail.headD 0)) σ chx hag
  have w2 := fun chx => uWin2 tenv k (uρ' ρ (ch.headD 0) (ch.tail.headD 0) (ch.tail.tail.headD 0)) σ chx hag
  have w3 := fun chx => uWin3 tenv k (uρ' ρ (ch.headD 0) (ch.tail.headD 0) (ch.tail.tail.headD 0)) σ chx hag
  have w4 := fun chx => uWin4 tenv k (uρ' ρ (ch.headD 0) (ch.tail.headD 0) (ch.tail.tail.headD 0)) σ chx hag
  have w5 := fun chx => uWin5 tenv k (uρ' ρ (ch.headD 0) (ch.tail.headD 0) (ch.tail.tail.headD 0)) σ chx hag
  have w6 := fun chx => uWin6 tenv k (uρ' ρ (ch.headD 0) (ch.tail.headD 0) (ch.tail.tail.headD 0)) σ chx hag
  have w7 := fun chx => uWin7 tenv k (uρ' ρ (ch.headD 0) (ch.tail.headD 0) (ch.tail.tail.headD 0)) σ chx hag
  have p1 := uPick1_step tenv k ρ σ hag (uKey1 (ch.tail.headD 0)) (uKey2 (ch.tail.headD 0) (ch.tail.tail.headD 0))
    (uKey3 (ch.tail.headD 0) (ch.tail.tail.headD 0)) ch
  have p2 := uPick2_step tenv k ρ σ ((ch.headD 0 % 10 : Nat) : Int)
    (uKey2 (ch.tail.headD 0) (ch.tail.tail.headD 0))
    (uKey3 (ch.tail.headD 0) (ch.tail.tail.headD 0)) ch.tail
  have p3 := uPick3_step tenv k ρ σ ((ch.headD 0 % 10 : Nat) : Int)
    (uKey3 (ch.tail.headD 0) (ch.tail.tail.headD 0)) (ch.tail.headD 0)
    ch.tail.tail
  have p4 := uPick4_step tenv k ρ σ ((ch.headD 0 % 10 : Nat) : Int)
    (ch.tail.headD 0) (ch.tail.tail.headD 0) ch.tail.tail.tail
  have pstop := uStop_step tenv k ρ σ ((ch.headD 0 % 10 : Nat) : Int)
    (ch.tail.headD 0) (ch.tail.tail.headD 0) ch.tail.tail.tail.tail
  have psort := uSort_step tenv k ρ σ ((ch.headD 0 % 10 : Nat) : Int)
    (ch.tail.headD 0) (ch.tail.tail.headD 0) ch.tail.tail.tail.tail
  have h := GoLean.Surface.stepFnIter_chain
    (GoLean.Surface.stepFnIter_chain
      (GoLean.Surface.stepFnIter_chain
        (GoLean.Surface.stepFnIter_chain
          (GoLean.Surface.stepFnIter_chain
            (GoLean.Surface.stepFnIter_chain
              (GoLean.Surface.stepFnIter_chain
                (GoLean.Surface.stepFnIter_chain
                  (GoLean.Surface.stepFnIter_chain
                    (GoLean.Surface.stepFnIter_chain
                      (GoLean.Surface.stepFnIter_chain
                        (GoLean.Surface.stepFnIter_chain
                          (w1 ch)
                          (GoLean.Surface.stepFnIter_one p1))
                        (w2 ch.tail))
                      (GoLean.Surface.stepFnIter_one p2))
                    (w3 ch.tail.tail))
                  (GoLean.Surface.stepFnIter_one p3))
                (w4 ch.tail.tail.tail))
              (GoLean.Surface.stepFnIter_one p4))
            (w5 ch.tail.tail.tail.tail))
          (GoLean.Surface.stepFnIter_one pstop))
        (w6 ch.tail.tail.tail.tail))
      (GoLean.Surface.stepFnIter_one psort))
    (w7 ch.tail.tail.tail.tail)
  have hstop : γC (uρ' ρ (ch.headD 0) (ch.tail.headD 0) (ch.tail.tail.headD 0)) (uC13 tenv k)
      = .next (γK (uρ' ρ (ch.headD 0) (ch.tail.headD 0) (ch.tail.tail.headD 0)) k) := rfl
  rw [← hstop]
  exact h

/-- **THE FOOTPRINT CARRIER** (Leg A's precondition): the state is a
γ-image of the canonical becomeFollower footprint — the fixture
family at SOME valuation whose reader-visible scalar slots carry
`(vote, lead, state, ldT)` and whose pending-argument slot carries
`leadArg` — over any table-carrier agreeing with the twin's pinned
tables. The disjointness/aliasing content of the footprint enters
ONCE through the γ-image (ρ-injectivity is trivial here: the
canonical placement), never as pairwise enumerations. -/
def BfPre (vote lead state ldT leadArg : Int) (σm : ExecState) : Prop :=
  ∃ (ρ : Valuation) (σt : ExecState),
    bfTB.Agrees σt
    ∧ σm = γS ρ σt uS0
    ∧ ρ.ints 1 = vote ∧ ρ.ints 2 = lead ∧ ρ.ints 3 = state
    ∧ ρ.ints 4 = ldT ∧ ρ.ints 9 = leadArg

/-- The footprint carrier DETERMINES the reader (the "precondition in
reader vocabulary" direction): a `BfPre` state projects to exactly
the named abstract raft state. -/
theorem bfPre_reader {vote lead state ldT leadArg : Int}
    {σm : ExecState} (h : BfPre vote lead state ldT leadArg σm) :
    absRaftNode σm ⟨0⟩ = some ⟨0, vote, lead, state, 1, 1⟩ := by
  obtain ⟨ρ, σt, hag, rfl, h1, h2, h3, h4, h9⟩ := h
  have hproj : absRaftNode (γS ρ σt uS0) ⟨0⟩
      = some ⟨0, ρ.ints 1, ρ.ints 2, ρ.ints 3, 1, 1⟩ := by
    kernel_rfl
  rw [hproj, h1, h2, h3]

/-- **LEG A — the pilot's handler spec** (the judgment's honest
`CallSpec` instance, stated as such): `becomeFollower(0, leadArg)` at
any footprint-carrying state whose reader shows
`(vote, lead, state, ldT)` reaches the post-store configuration with
the reader showing exactly the SPEC HANDLER's result
(`specBecomeFollower` — term overwritten, vote preserved on the
term-equal branch, follower of `leadArg`). ∀-state over the
precondition, ∀ env k (continuation-parametric — the open-tail
route), ∀ ch (demonic, short streams included), ∃ n. The two
normalize premises are the genuinely-external side conditions
(uint64-normalized inputs). -/
theorem becomeFollower_callSpec (vote lead state ldT leadArg : Int)
    (hvote : IntKind.normalize .uint64 vote = vote)
    (hlead : IntKind.normalize .uint64 leadArg = leadArg) :
    Spec.CallSpec (BfPre vote lead state ldT leadArg)
      ⟨"raft.raft.becomeFollower"⟩
      [.addr (.base ⟨0⟩), .int 0 .uint64]
      (.int leadArg .uint64)
      (fun σ' => absRaftNode σ' ⟨0⟩
        = some (specBecomeFollower ⟨0, vote, lead, state, 1, 1⟩ 0
            leadArg)) := by
  intro σm hP env km ch
  obtain ⟨ρ, σt, hag, hσ, h1, h2, h3, h4, h9⟩ := hP
  -- the prefix-derived valuation leaves the fixture's γ-image and the
  -- projection slots unchanged (slots 5–8 are absent from uS0 and
  -- from slots 1–4/9)
  have hs0 : γS ρ σt uS0
      = γS (uρ' ρ (ch.headD 0) (ch.tail.headD 0) (ch.tail.tail.headD 0))
          σt uS0 := by
    kernel_rfl
  have hints9 :
      (uρ' ρ (ch.headD 0) (ch.tail.headD 0)
        (ch.tail.tail.headD 0)).ints 9 = leadArg := by
    simp [uρ', uρ, h9]
  -- the call configuration is the γ-image of the open-tail fixture
  -- config at (env, reflect km)
  have hkm : γK (uρ' ρ (ch.headD 0) (ch.tail.headD 0)
        (ch.tail.tail.headD 0)) (reflectK symDom km) = km :=
    reflectK_conc (D := symDom)
      (symInterp_sound (uρ' ρ (ch.headD 0) (ch.tail.headD 0)
        (ch.tail.tail.headD 0))) km
  have hcfg : γC (uρ' ρ (ch.headD 0) (ch.tail.headD 0)
        (ch.tail.tail.headD 0)) (uC0 env (reflectK symDom km))
      = Machine.Config.retV
          (.int ((uρ' ρ (ch.headD 0) (ch.tail.headD 0)
            (ch.tail.tail.headD 0)).ints 9) .uint64)
          (.callArgsK ⟨"raft.raft.becomeFollower"⟩ []
            [.addr (.base ⟨0⟩), .int 0 .uint64] [] env
            (γK (uρ' ρ (ch.headD 0) (ch.tail.headD 0)
              (ch.tail.tail.headD 0)) (reflectK symDom km))) := by
    kernel_rfl
  -- the span
  have hspan := bf_full_span env (reflectK symDom km) ρ σt hag ch
  refine ⟨3234,
    γS (uρ' ρ (ch.headD 0) (ch.tail.headD 0) (ch.tail.tail.headD 0))
      σt uS13,
    ch.tail.tail.tail.tail, ?_, ?_, ?_⟩
  · rw [hσ, hs0, show (Machine.Config.retV (.int leadArg .uint64)
        (.callArgsK ⟨"raft.raft.becomeFollower"⟩ []
          [.addr (.base ⟨0⟩), .int 0 .uint64] [] env km))
      = γC (uρ' ρ (ch.headD 0) (ch.tail.headD 0) (ch.tail.tail.headD 0))
          (uC0 env (reflectK symDom km))
      from by rw [hcfg, hints9, hkm], hspan, hkm]
  · -- the reader postcondition, through the store-normalize wrappers
    dsimp only
    have hproj : absRaftNode
        (γS (uρ' ρ (ch.headD 0) (ch.tail.headD 0)
          (ch.tail.tail.headD 0)) σt uS13) ⟨0⟩
        = some ⟨0, unrm 13 (ρ.ints 1), unrm 3 (ρ.ints 9), 0, 1, 1⟩ := by
      kernel_rfl
    rw [hproj, h9, h1, unrm_id hlead 3, unrm_id hvote 13]
    with_unfolding_all rfl
  · exact ((((List.tail_suffix _).trans (List.tail_suffix _)).trans
      (List.tail_suffix _)).trans (List.tail_suffix _))

/-- Non-vacuity of the footprint carrier (the ∃-discharge, stated as
such): a concrete inhabitant over the pinned tables at live scalar
values. -/
theorem bfPre_inhabited :
    BfPre 7 2 1 5 4
      (γS { ints := fun i => [0, 7, 2, 1, 5, 0, 0, 0, 0, 4].getD i 0
            bools := fun _ => false
            vals := fun _ => .nil
            cells := fun _ => ⟨none, .nil⟩ } wBase uS0) :=
  ⟨_, wBase, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-! ## The open-tail reduction finding, tracked (design note §3
finding 2 / log probe record): kernel reduction of the window
evaluator never inspects below the barrier on a successful span, so
window facts close by `rfl` with the below-barrier tail and the
frame's caller-env OPEN — the wp_bind lift by reflection. These are
the probe's three examples, kept in-build so the finding is
re-checked every build. -/

example : ∀ (k : SymCont),
    symEvalWindow 2 { heap := [], nextAddr := 0 }
      (.exec .returnStmt [] (.frame [] [] [] [] k false))
      = (2, { heap := [], nextAddr := 0 }, .next k) := fun _ => rfl

example : ∀ (k : SymCont) (env : LocalEnv),
    symEvalWindow 2 { heap := [], nextAddr := 0 }
      (.exec .returnStmt [] (.frame [] env [] [] k false))
      = (2, { heap := [], nextAddr := 0 }, .next k) := fun _ _ => rfl

example : ∀ (k : SymCont) (env : LocalEnv),
    symEvalWindow 5 { heap := [], nextAddr := 0 }
      (.exec (.seqn #[.returnStmt]) []
        (.seq [] [] (.frame [] env [] [] k false)))
      = (5, { heap := [], nextAddr := 0 }, .next k) := fun _ _ => rfl

end GoLean.RaftSeam
