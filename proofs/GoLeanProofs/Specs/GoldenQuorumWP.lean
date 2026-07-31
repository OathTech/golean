import GoLeanProofs.SurfaceExit
import GoLeanProofs.Laws.QuorumOps
import GoLeanProofs.Specs.QuorumRefSpec

/-!
# The quorum walk — TARGETS and the math link (quorum pilot phase 4, 2026-07-31)

Honest status, stated once and repeated in every docstring below: the
`CommittedIndex` machine walk is **NOT discharged**. What this file holds
is (a) the target STATEMENTS, `def … : Prop`, in the phase-0 idiom
(`Specs/QuorumTargets.lean`) so the obligation is pinned and cannot drift,
and (b) the parts of the tier-1 claim that ARE proven — the pure-math
half, which now needs only the machine half to close.

Why the walk is not here (recorded, not glossed): phase 4's law batch
landed the per-construct laws and, this slice, the `σ.types` ghost pin and
the dynamic-dispatch frame-entry law with its witness on the REAL
`AckedIndexer.AckedIndex` anchor. The remaining walk is
`committedOneKnown → run → CommittedIndex`, which needs, beyond what
exists: an ALLOCATING wide-op apply core (`makeMap` allocates inside
`applyStmtOp`), array-to-slice (`stk[:n]`) and `makeSlice` laws, a
two-result frame-exit law, and the composition of ~200 steps. Each is
tracked in the arc doc's build log with its owner.

The claim shape, for the record: the machine result `12` equals
`GoLean.Quorum.committedIndexRef [1] (fun v => if v = 1 then some 12
else none)` (proven by `rfl` below), and `committedIndexRef_meets_spec`
(PROVEN, `Specs/QuorumRefSpec.lean`) upgrades that to
`IsCommittedIndex` — so the ONLY missing link between the pinned real
etcd-io/raft lowering and the declarative quorum spec is the machine
walk. That is the point of stating the targets here rather than in chat.
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Iris GoLean.Iris.GoldenQuorum

namespace GoLean.Quorum

/-! ## The math half — PROVEN

These are theorems, not targets. They pin the value the machine walk must
land on and immediately upgrade it to the declarative spec. -/

/-- The one-voter instance's acked data: voter `1` reported index `12`
(the `committedOneKnown` driver's map literal). -/
def ackedOneKnown : Nat → Option Nat := fun v => if v = 1 then some 12 else none

/-- **The value the machine must produce**, from the reference — `rfl`,
so it is a computation, not a claim. -/
theorem committedIndexRef_oneKnown :
    committedIndexRef [1] ackedOneKnown = 12 := rfl

/-- **The declarative spec holds at 12** for this instance: committedness
and maximality, via the proven general agreement theorem. Together with a
machine walk landing on `12`, this is the tier-1 statement on a one-voter
config. -/
theorem isCommittedIndex_oneKnown : IsCommittedIndex [1] ackedOneKnown 12 :=
  committedIndexRef_oneKnown ▸ committedIndexRef_meets_spec [1] ackedOneKnown
    (by decide)

/-- Negative twin: `11` is NOT the committed index of this instance
(maximality fails at 12) — the guard against a spec that accepts anything
below the true value. -/
theorem not_isCommittedIndex_oneKnown_11 :
    ¬ IsCommittedIndex [1] ackedOneKnown 11 := by
  rintro (⟨h, -⟩ | ⟨-, -, hmax⟩)
  · simp at h
  · exact absurd (hmax 12 (by omega)) (by decide)

end GoLean.Quorum

namespace GoLean.Surface

open GoLean.GoCore GoLean.Quorum

/-- **TARGET (phase 4, item 3 — NOT PROVEN).** The `GoFuncSpec` form over
the PINNED ACTUAL LOWERING of the real etcd-io/raft quorum source:
"`committedOneKnown()` takes no arguments, needs no heap, and returns
12" — ∀-quantified over the caller's target cell, its prior value, and
the frame, exactly as `recoverFuncSpec_statement`/
`goldenFuncSpec_statement`. The driver builds `MajorityConfig{1:{}}` and
`mapAckIndexer{1:12}` and calls `run → CommittedIndex`, so discharging
this walks the real interface dispatch, the real map range, the real sort
extern and the real defined-type conversions.

`12` is `committedIndexRef [1] ackedOneKnown` (`committedIndexRef_oneKnown`,
`rfl`), so discharging this target plus `committedIndexRef_meets_spec`
(PROVEN) yields `IsCommittedIndex` on this instance — the tier-1 claim.
No theorem names this def yet and no docstring may claim it is
dischargeable today. -/
def quorumOneKnownFuncSpec_statement : Prop :=
  GoFuncSpec quorumLowered.typeDefs.toList quorumLowered.funcs
    ⟨"committedOneKnown"⟩ .uint64 #[] .emp (fun n => .pure (n = 12))

/-- **TARGET — the negative twin.** The same spec must FAIL at 11; once
the positive target is proven this is the usual two-line corollary
(`.pure` injectivity), and stating it now is what stops a trivialized
postcondition from passing for the real one. -/
def quorumOneKnownNotEleven_statement : Prop :=
  ¬ GoFuncSpec quorumLowered.typeDefs.toList quorumLowered.funcs
      ⟨"committedOneKnown"⟩ .uint64 #[] .emp (fun n => .pure (n = 11))

/-- **TARGET — the truncated scope the fallback names.** The
implementation method `main.mapAckIndexer.AckedIndex` at `GoFuncSpec2`
strength (its `(Index, bool)` result pair is the arity widening the pilot
forces). Strictly smaller than the full walk and the natural next slice:
frame entry through the anchor is already proven
(`wp_call_dynamic_enter_ackedIndex`), and the body's one wide statement
is already proven (`wp_map_lookup_ackedIndex`); what is missing is the
two-result frame EXIT law and the block/scope plumbing between them. -/
def quorumAckedIndexFuncSpec2_statement : Prop :=
  GoFuncSpec2 quorumLowered.typeDefs.toList quorumLowered.funcs
    ⟨"main.mapAckIndexer.AckedIndex"⟩ .uint64 #[] .emp
    (fun n b => .pure (b = true → n = 12))

end GoLean.Surface
