import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Examples.InsertionSort.Canon
import GoLeanProofs.Examples.InsertionSort.Family
import GoLeanProofs.Examples.InsertionSort.Scan
import GoLeanProofs.Examples.InsertionSort.Setup

/-!
# InsertionSort — Rebuild

Per-phase shard of `GoLeanProofs.Examples.InsertionSort` (examples
phase-2 slice 0, lever 2, 2026-08-14). Every statement and proof here
is BYTE-IDENTICAL to the pre-split module; only file placement changed,
so Lake's module-level caching can see the phases separately. The
user-facing headline theorems live in the thin root module
`GoLeanProofs.Examples.InsertionSort`, whose docstring records the
example's design and the shard map.
-/

namespace GoLean.Examples.InsertionSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-! ## The test phase, part 2: the rebuild (`t := make; t[i] = seed*(i+1)`
— the setup machinery re-instantiated at the `t` placement, cells
14–18, backing at 15) -/

private def c5Scope : Scope :=
  [("$c5", .base ⟨14⟩), ("ok", .base ⟨11⟩), ("s", .base ⟨5⟩),
   ("$c4", .base ⟨3⟩)]
private def envC5 : LocalEnv := [c5Scope, hIScope0]
private def hIAfterMs2K : Cont := .seq (hIBodyList.drop 7) envC5 hIFrame0
private def hIMs2K : Cont :=
  .stmtOpK (.makeSlice (.int .uint64) false) 1 [.addr (.base ⟨14⟩)] []
    envC5 hIAfterMs2K

/-- The `t` handle over the backing array at its fixed address 15. -/
abbrev hTHandleCell (n : Nat) : HeapCell :=
  ⟨some (.slice (.int .uint64)), .slice ⟨some (.base ⟨15⟩), 0, n, n⟩⟩
abbrev hTSliceH (n : Nat) : GoValue :=
  .slice ⟨some (.base ⟨15⟩), 0, n, n⟩

/-- Pre-makeSlice: `$c5` declared (default slice) at 14. -/
def σSCc5 (n seed : Nat) (ivF : Int) (l : List Int) (sciv : Int) :
    ExecState :=
  σHOutT n seed l ivF false
    [(.base ⟨11⟩, ucell 1), (.base ⟨12⟩, ucell sciv), (.base ⟨13⟩, bcell false),
     (.base ⟨14⟩, ⟨some (.slice (.int .uint64)), .slice ⟨none, 0, 0, 0⟩⟩)]
    15

/-- Post-makeSlice: the `t` backing (zeroed) at 15, the handle in 14. -/
def σMs2 (n seed : Nat) (ivF : Int) (l : List Int) (sciv : Int) :
    ExecState :=
  σHOutT n seed l ivF false
    [(.base ⟨11⟩, ucell 1), (.base ⟨12⟩, ucell sciv), (.base ⟨13⟩, bcell false),
     (.base ⟨14⟩, hTHandleCell n),
     (.base ⟨15⟩, arrCell n (List.replicate n 0))]
    16

/-- Scan exit: test false → break unwinding → `$c5` declared → the
second makeSlice's length delivered. 15 steps (trace 973→988). -/
theorem hsc_X_raw (n seed : Nat) (ivF : Int) (l : List Int)
    (sciv : Int) (ch : Choices) :
    stepFnIter 15 (σSC n seed ivF l sciv false)
      (.retV (.bool false) scCmpK) ch
      = .ok (.retV (.int ((n : Nat) : Int) .uint64) hIMs2K,
          σSCc5 n seed ivF l sciv, ch) := by
  with_unfolding_all rfl

/-- **The second makeSlice apply at symbolic length** (the `t`
backing). -/
theorem hstep_Ims2 (n seed : Nat) (ivF : Int) (l : List Int)
    (sciv : Int) (ch : Choices) :
    stepFn (σSCc5 n seed ivF l sciv)
      (.retV (.int ((n : Nat) : Int) .uint64) hIMs2K) ch
      = .ok (.next hIAfterMs2K, σMs2 n seed ivF l sciv, ch) := by
  have hb := GoLean.Iris.buildDefaultArrayValue_int (σSCc5 n seed ivF l sciv)
    .uint64 n
  have harr : (List.replicate n (GoValue.int 0 .uint64)).toArray
      = (⟨(List.replicate n (0 : Int)).map
          (fun v => GoValue.int v .uint64)⟩ : Array GoValue) := by
    simp [List.map_replicate]
  rw [harr] at hb
  have hnn1 := natFromNonneg_cast
    "runtime error: makeslice: len out of range" n
  have hnn2 := natFromNonneg_cast
    "runtime error: makeslice: cap out of range" n
  have happly : applyStmtOp (σSCc5 n seed ivF l sciv) ch
      (.makeSlice (.int .uint64) false) 1
      [.addr (.base ⟨14⟩), .int ((n : Nat) : Int) .uint64]
      = .ok (σMs2 n seed ivF l sciv, ch) := by
    simp only [applyStmtOp, applyStmtOpCore, valueAsInt, valueAsLoc,
      hnn1, hnn2, hb, Bind.bind, Except.bind, pure, Except.pure]
    rw [if_neg (Nat.lt_irrefl n)]
    with_unfolding_all rfl
  exact stepFn_stmtOp_apply
    (done := [.addr (.base ⟨14⟩)]) (v := .int ((n : Nat) : Int) .uint64)
    happly

def tScope : Scope :=
  [("t", .base ⟨16⟩), ("$c5", .base ⟨14⟩), ("ok", .base ⟨11⟩),
   ("s", .base ⟨5⟩), ("$c4", .base ⟨3⟩)]
def envT : LocalEnv := [tScope, hIScope0]
def envRB : LocalEnv :=
  [[("$forFirst", .base ⟨18⟩)], [("i", .base ⟨17⟩)], tScope, hIScope0]

/-- The rebuild loop's desugared body (the multiplicative store to `t`). -/
private abbrev isortRebuildBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i")
          (.add (.var "i") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n"))
        (.seqn #[])
        .breakStmt,
      .block #[]
        #[.seqn
            #[.assign
                (.addr (.indexAddr (.var "t") (.var "i")))
                (.mul (.var "seed")
                  (.add (.var "i") (.intLit 1 .uint64)))]]]

private def rbTail : Cont :=
  .seq [] envRB
    (.seq [] [[("i", .base ⟨17⟩)], tScope, hIScope0]
      (.seq (hIBodyList.drop 9) envT hIFrame0))
private def rbHeadCfg : Config :=
  .exec (.while (.boolLit true) isortRebuildBody) envRB rbTail
private def rbLoopK : Cont :=
  .loop (.boolLit true) isortRebuildBody envRB rbTail
private def rbStoreBlk : Stmt :=
  .block #[]
    #[.seqn
        #[.assign
            (.addr (.indexAddr (.var "t") (.var "i")))
            (.mul (.var "seed")
              (.add (.var "i") (.intLit 1 .uint64)))]]
def rbCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envRB)
    (.seq [rbStoreBlk] ([] :: envRB) rbLoopK)
private def rbStoreTail : Cont :=
  .seq [] ([] :: [] :: envRB) (.seq [] ([] :: envRB) rbLoopK)

/-- The rebuild-loop state family (fixed cells 0–18). -/
def σRB (n seed : Nat) (ivF sciv : Int) (l tl : List Int) (iv : Int)
    (ffv : Bool) : ExecState :=
  σHOutT n seed l ivF false
    [(.base ⟨11⟩, ucell 1), (.base ⟨12⟩, ucell sciv), (.base ⟨13⟩, bcell false),
     (.base ⟨14⟩, hTHandleCell n), (.base ⟨15⟩, arrCell n tl),
     (.base ⟨16⟩, hTHandleCell n), (.base ⟨17⟩, ucell iv),
     (.base ⟨18⟩, bcell ffv)]
    19

/-- makeSlice done → `t := $c5`, `i := 0`, the flag block → the rebuild
loop head. 42 steps (trace 989→1031). -/
theorem hR2_raw (n seed : Nat) (ivF : Int) (l : List Int)
    (sciv : Int) (ch : Choices) :
    stepFnIter 42 (σMs2 n seed ivF l sciv) (.next hIAfterMs2K) ch
      = .ok (rbHeadCfg,
          σRB n seed ivF sciv l (List.replicate n 0) 0 true, ch) := by
  with_unfolding_all rfl

/-- Rebuild first-pass dispatch. -/
theorem hrb_d0_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 25 (σRB n seed ivF sciv l tl iv true) rbHeadCfg ch
      = .ok (.retV (.bool (decide (iv < ((n : Nat) : Int)))) rbCmpK,
          σRB n seed ivF sciv l tl iv false, ch) := by
  with_unfolding_all rfl

/-- Rebuild body: test true → the store point of `t[i] = seed*(i+1)`. -/
private theorem hrb_body_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 22 (σRB n seed ivF sciv l tl iv false)
      (.retV (.bool true) rbCmpK) ch
      = .ok (.next (.storeK
            [.chain (hTSliceH n) [.int iv .uint64] [.index]]
            [.int (IntKind.normalize .uint64
                (((seed : Nat) : Int) * IntKind.normalize .uint64 (iv + 1)))
              .uint64]
            (.seqn #[]) ([] :: [] :: envRB) rbStoreTail),
          σRB n seed ivF sciv l tl iv false, ch) := by
  with_unfolding_all rfl

/-- The rebuild element store, cleaned. -/
private theorem hstep_rbstore (n seed : Nat) (ivF sciv : Int)
    (l tl : List Int) (i : Nat) (w : Int) (hi : i < n) (hlen : tl.length = n)
    (hl : ∀ v ∈ tl, 0 ≤ v ∧ v < 2 ^ 64) (hw : 0 ≤ w ∧ w < 2 ^ 64)
    (iv : Int) (ch : Choices) :
    stepFnIter 1 (σRB n seed ivF sciv l tl iv false)
      (.next (.storeK [.chain (hTSliceH n) [.int ((i : Nat) : Int) .uint64]
          [.index]]
        [.int w .uint64] (.seqn #[]) ([] :: [] :: envRB) rbStoreTail))
      ch
      = .ok (.next (.storeK [] [] (.seqn #[]) ([] :: [] :: envRB)
            rbStoreTail),
          σRB n seed ivF sciv l (tl.set i w) iv false, ch) := by
  have hstore := storeTarget_slice_u64 (σ := σRB n seed ivF sciv l tl iv false)
    (a := ⟨15⟩) (off := 0) (len := n) (cap := n) (i := i) (n := n)
    (ik := .uint64) (l := tl) (w := w) rfl (Nat.le_refl n) hi
    (by omega) hlen hl hw
  rw [Nat.zero_add] at hstore
  exact stepFnIter_one (stepFn_store_step hstore)

/-- Rebuild dispatch (later passes): store done → head → `i := i + 1`
→ the exit test delivery. -/
private theorem hrb_d1_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 34 (σRB n seed ivF sciv l tl iv false)
      (.next (.storeK [] [] (.seqn #[]) ([] :: [] :: envRB)
        rbStoreTail)) ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < ((n : Nat) : Int)))) rbCmpK,
          σRB n seed ivF sciv l tl
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false, ch) := by
  with_unfolding_all rfl

/-- One rebuild iteration from the exit-test's true delivery at `i`
(body → element store → head → `i++` → the next test). 57 steps. -/
private theorem hrb_iter (n seed : Nat) (ivF sciv : Int) (l : List Int)
    (i : Nat) (hn : n < 2 ^ 63) (hi : i < n) (ch : Choices) :
    stepFnIter 57
      (σRB n seed ivF sciv l (isFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false)
      (.retV (.bool true) rbCmpK) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) rbCmpK,
          σRB n seed ivF sciv l
            (isFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
            ((i + 1 : Nat) : Int) false, ch) := by
  have h1 := hrb_body_raw n seed ivF sciv l
    (isFamily i seed ++ List.replicate (n - i) 0) ((i : Nat) : Int) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    unorm_of_range (by omega)
      (by omega : ((i + 1 : Nat) : Int) < 2 ^ 64),
    show ((seed : Nat) : Int) * ((i + 1 : Nat) : Int)
      = ((seed * (i + 1) : Nat) : Int) from
      (Int.natCast_mul seed (i + 1)).symm,
    unorm_nat (seed * (i + 1))] at h1
  have h2 := hstep_rbstore n seed ivF sciv l
    (isFamily i seed ++ List.replicate (n - i) 0) i
    (((seed * (i + 1)) % 2 ^ 64 : Nat) : Int) hi
    (by rw [List.length_append, isFamily_length, List.length_replicate]
        omega)
    (isFamilyZ_range (by omega))
    ⟨by omega, by
      have := Nat.mod_lt (seed * (i + 1)) (y := 2 ^ 64) (by omega)
      omega⟩
    ((i : Nat) : Int) ch
  rw [isFamily_set hi] at h2
  have h3 := hrb_d1_raw n seed ivF sciv l
    (isFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
    ((i : Nat) : Int) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    unorm_of_range (by omega)
      (by omega : ((i + 1 : Nat) : Int) < 2 ^ 64),
    unorm_of_range (by omega)
      (by omega : ((i + 1 : Nat) : Int) < 2 ^ 64)] at h3
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- **The rebuild loop**: exactly `57·(n-i)` steps re-materialize the
wrapped multiplicative family at the `t` placement — the P5 iteration
schema (`stepFnIter_iterate`) at the composite above; the second isort
instance of the deleted `strongRecOn` boilerplate (G0 item 3a P6
rollback). Statement unchanged. -/
theorem hrebuild_loop (n seed : Nat) (hn : n < 2 ^ 63)
    (ivF sciv : Int) (l : List Int) :
    ∀ μ i, μ = n - i → i ≤ n → ∀ ch : Choices,
    stepFnIter (57 * (n - i))
      (σRB n seed ivF sciv l (isFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false)
      (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
        rbCmpK) ch
      = .ok (.retV (.bool (decide (((n : Nat) : Int) < ((n : Nat) : Int))))
            rbCmpK,
          σRB n seed ivF sciv l (isFamily n seed) ((n : Nat) : Int) false,
          ch) := by
  intro _ i _ hin ch
  have hgen := stepFnIter_iterate (c := 57) (n := n)
    (T := fun j => σRB n seed ivF sciv l
      (isFamily j seed ++ List.replicate (n - j) 0) ((j : Nat) : Int) false)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int)
      < ((n : Nat) : Int)))) rbCmpK)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact hrb_iter n seed ivF sciv l j hn hj ch')
    i hin ch
  simpa using hgen


end GoLean.Examples.InsertionSort
