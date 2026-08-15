import GoLeanProofs.Examples.BubbleSort.Harness

/-!
# BubbleSort — the LCG setup loop

Split from `BubbleSort.Harness` (proof-cost shard split, second cut).
Content and statements unchanged.
-/

namespace GoLean.Examples.BubbleSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## Raw run segments — the setup loop -/

theorem su_A0_rawB (nv sv : Int) (n : Nat) (l : List Int) (xv iv : Int)
    (ch : Choices) :
    stepFnIter 25 (σB (bHeapSu nv sv n l xv iv true) 10) suHeadCfgB ch
      = .ok (.retV (.bool (decide (iv < nv))) suCmpKB,
          σB (bHeapSu nv sv n l xv iv false) 10, ch) := by
  with_unfolding_all rfl

theorem su_A1_rawB (nv sv : Int) (n : Nat) (l : List Int) (xv iv : Int)
    (ch : Choices) :
    stepFnIter 29 (σB (bHeapSu nv sv n l xv iv false) 10) suHeadCfgB ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < nv))) suCmpKB,
          σB (bHeapSu nv sv n l xv
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false) 10, ch) := by
  with_unfolding_all rfl

/-- Setup fill: test true → `x = x*A + B` (raw: cell 7's store
normalizes but consults no symbolic branch) → the `s[i]` element-store
point. 33 steps. -/
theorem su_B1_rawB (nv sv : Int) (n : Nat) (l : List Int) (xv iv : Int)
    (ch : Choices) :
    stepFnIter 33 (σB (bHeapSu nv sv n l xv iv false) 10)
      (.retV (.bool true) suCmpKB) ch
      = .ok (.next (.storeK [suRefB n iv]
            [.int (IntKind.normalize .uint64 (IntKind.normalize .uint64
              (IntKind.normalize .uint64 (xv * 2862933555777941757)
                + 3037000493))) .uint64]
            (.seqn #[]) suEnvB2 suStTailB),
          σB (bHeapSu nv sv n l
            (IntKind.normalize .uint64 (IntKind.normalize .uint64
              (IntKind.normalize .uint64 (xv * 2862933555777941757)
                + 3037000493))) iv false) 10, ch) := by
  with_unfolding_all rfl

theorem su_D_rawB (nv sv : Int) (n : Nat) (l : List Int) (xv iv : Int)
    (ch : Choices) :
    stepFnIter 5 (σB (bHeapSu nv sv n l xv iv false) 10)
      (.next (.storeK [] [] (.seqn #[]) suEnvB2 suStTailB)) ch
      = .ok (suHeadCfgB, σB (bHeapSu nv sv n l xv iv false) 10, ch) := by
  with_unfolding_all rfl

/-- Setup exit: test false → `var pre` declared and the copy loop
head. 39 steps. -/
theorem su_X_rawB (nv sv : Int) (n : Nat) (l : List Int) (xv iv : Int)
    (ch : Choices) :
    stepFnIter 39 (σB (bHeapSu nv sv n l xv iv false) 10)
      (.retV (.bool false) suCmpKB) ch
      = .ok (cpHeadCfgB,
          σB (bHeapCp nv sv n l zeros8 xv iv 0 true) 13, ch) := by
  with_unfolding_all rfl

end GoLean.Examples.BubbleSort
