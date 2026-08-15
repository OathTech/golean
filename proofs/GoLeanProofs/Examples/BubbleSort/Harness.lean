import GoLeanProofs.Examples.BubbleSort.Machine
import GoLeanProofs.Examples.BubbleSort.Pure

/-!
# BubbleSort — Harness (entry, setup, first copy loop)

The harness phases BEFORE the subject call: entry through `make`, the
LCG setup loop (`x = x*A + B; s[i] = x`), and the `pre` copy loop, up
to the delivered `bubbleSort(s)` argument. All raw segments are
`with_unfolding_all rfl` at symbolic values; the conditioned steps are
the makeSlice apply, the per-iteration slice/array element stores, and
the element reads — exactly the heap-consulting ops.

Per-segment step counts (probe-measured with `.tmp/Probe.lean` at
`(n, seed) = (2, 3)` and `(2, 7)`, re-checked by `rfl` here):

| phase | steps |
|---|---|
| entry → makeSlice apply | 10 |
| makeSlice apply → setup head | 1 + 55 |
| setup dispatch (first / later) | 25 / 29 |
| one setup iteration | 68 |
| setup exit → copy head | 39 |
| copy dispatch (first / later) | 25 / 29 |
| one copy iteration | 53 |
| copy exit → call argument delivered | 9 |
-/

namespace GoLean.Examples.BubbleSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## The wrap-arithmetic normal forms -/

/-- A `Nat`-cast value normalizes to its wrap (the general form of
`unorm_add_nat`'s conclusion).
-- KIT-GAP WITNESS (see .tmp/kitgaps-bubble.md): SliceMem has
`unorm_add_nat` but no bare-cast or multiplicative form; both sorts
need them for the LCG setup. -/
theorem unorm_nat (Y : Nat) :
    IntKind.normalize .uint64 ((Y : Nat) : Int)
      = ((Y % 2 ^ 64 : Nat) : Int) := by
  simp [IntKind.normalize, IntKind.bits?, IntKind.signed]

/-- The machine's three-normalize spelling of one LCG step collapses
to the `Nat` wrap `(X*A + B) % 2^64`.
-- KIT-GAP WITNESS (see .tmp/kitgaps-bubble.md). -/
theorem bubX_step_norm (X : Nat) :
    IntKind.normalize .uint64 (IntKind.normalize .uint64
        (IntKind.normalize .uint64 ((X : Int) * 2862933555777941757)
          + 3037000493))
      = (((X * 2862933555777941757 + 3037000493) % 2 ^ 64 : Nat)
          : Int) := by
  rw [show ((X : Int) * 2862933555777941757)
        = ((X * 2862933555777941757 : Nat) : Int) from by
      rw [Int.natCast_mul]; rfl,
    unorm_nat,
    show (3037000493 : Int) = ((3037000493 : Nat) : Int) from rfl,
    unorm_add_nat, unorm_nat]
  have h : (X * 2862933555777941757 % 2 ^ 64 + 3037000493) % 2 ^ 64 % 2 ^ 64
      = (X * 2862933555777941757 + 3037000493) % 2 ^ 64 := by omega
  rw [h]

/-- One `lcgStep` unfolding, in the shape `bubX_step_norm` lands on. -/
theorem bubX_succ (i seed : Nat) :
    (((SortShared.lcgStep bubA bubB i seed * 2862933555777941757
        + 3037000493) % 2 ^ 64 : Nat) : Int)
      = bubX (i + 1) seed := by
  rw [bubX, SortShared.lcgStep]

/-! ## Raw run segments — entry -/

/-- Entry A: body start → the `$c4` makeSlice apply point. 10 steps. -/
theorem b_E1_raw (nv sv : Int) (ch : Choices) :
    stepFnIter 10 (σB (bHeap0 nv sv) 4) (bHC0) ch
      = .ok (.retV (.int nv .uint64)
          (.stmtOpK (.makeSlice tU64 false) 1
            [.addr (.base ⟨4⟩)] [] envC4B
            (.seq [bS2, bS3, bS4, bS5, bS6, bS7, bS8, bS9, bS10] envC4B
              (.frame [] [] [] [] .stop))),
        σB (bHeapC4 nv sv) 5, ch) := by
  with_unfolding_all rfl

/-- **`make([]uint64, n)` at SYMBOLIC `n`** (conditioned: the one
stmt-op that allocates). -/
theorem b_make_apply (nv sv : Int) (n : Nat) (ch : Choices) :
    applyStmtOp (σB (bHeapC4 nv sv) 5) ch (.makeSlice tU64 false) 1
      [.addr (.base ⟨4⟩), .int (n : Nat) .uint64]
      = .ok (σB (bHeapMake nv sv n) 6, ch) := by
  have hnn1 := natFromNonneg_cast
    "runtime error: makeslice: len out of range" n
  have hnn2 := natFromNonneg_cast
    "runtime error: makeslice: cap out of range" n
  have hb := GoLean.Iris.buildDefaultArrayValue_int
    (σB (bHeapC4 nv sv) 5) .uint64 n
  have harr : (List.replicate n (GoValue.int 0 .uint64)).toArray
      = (⟨(List.replicate n (0 : Int)).map
          (fun v => GoValue.int v .uint64)⟩ : Array GoValue) := by
    simp [List.map_replicate]
  rw [harr] at hb
  simp only [applyStmtOp, applyStmtOpCore, valueAsInt, valueAsLoc,
    hnn1, hnn2, hb, Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (Nat.lt_irrefl n)]
  with_unfolding_all rfl

/-- Entry B: `s := $c4`, `x := seed`, the setup counter and flag → the
setup loop head. 55 steps. -/
theorem b_E2_raw (nv sv : Int) (n : Nat) (ch : Choices) :
    stepFnIter 55 (σB (bHeapMake nv sv n) 6)
      (.next (.seq [bS2, bS3, bS4, bS5, bS6, bS7, bS8, bS9, bS10] envC4B
        (.frame [] [] [] [] .stop))) ch
      = .ok (suHeadCfgB,
          σB (bHeapSu nv sv n (List.replicate n 0)
            (IntKind.normalize .uint64 sv) 0 true) 10, ch) := by
  with_unfolding_all rfl

end GoLean.Examples.BubbleSort
