import GoLeanProofs.Examples.WordCountProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Examples.WordCount.CanonRange

/-!
# WordCount — Return

Per-phase shard of `GoLeanProofs.Examples.WordCount` (examples phase-2
slice 0, lever 2, 2026-08-14). Every statement and proof here is
BYTE-IDENTICAL to the pre-split module; only file placement changed, so
Lake's module-level caching can see the phases separately. The
user-facing headline theorems live in the thin root module
`GoLeanProofs.Examples.WordCount`; the module docstring there records
the example's design.
-/

namespace GoLean.Examples.WordCount

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## The return path (range exit → the driver terminal) -/

/-- The exit-phase front: result cells written (`$callres` at 0, `$res0`
at 3), counters at their final values. -/
def frontX (L : Nat) (ws : List Int) (kvs : List (Int × Nat))
    (r0 r3 : Int) : Heap :=
  [(.base ⟨0⟩, u64cell r0), (.base ⟨1⟩, arrCell L ws),
   (.base ⟨2⟩, handleCell L), (.base ⟨3⟩, u64cell r3),
   (.base ⟨4⟩, mhCell), (.base ⟨5⟩, mdCell kvs),
   (.base ⟨6⟩, mhCell), (.base ⟨7⟩, intcell (L : Int)),
   (.base ⟨8⟩, bcell false)]

def σX (L : Nat) (ws : List Int) (kvs : List (Int × Nat))
    (r0 r3 : Int) (tail : Heap) (na : Nat) : ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := frontX L ws kvs r0 r3 ++ tail, nextAddr := na }

theorem lookup_frontX_none (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (r0 r3 : Int) {x : Nat} (hx : 9 ≤ x) :
    Heap.lookup (frontX L ws kvs r0 r3) (.base ⟨x⟩) = none := by
  simp only [frontX, Heap.lookup,
    base_beq_false (by omega : (0 : Nat) ≠ x),
    base_beq_false (by omega : (1 : Nat) ≠ x),
    base_beq_false (by omega : (2 : Nat) ≠ x),
    base_beq_false (by omega : (3 : Nat) ≠ x),
    base_beq_false (by omega : (4 : Nat) ≠ x),
    base_beq_false (by omega : (5 : Nat) ≠ x),
    base_beq_false (by omega : (6 : Nat) ≠ x),
    base_beq_false (by omega : (7 : Nat) ≠ x),
    base_beq_false (by omega : (8 : Nat) ≠ x),
    Bool.false_eq_true, if_false]

/-- X1: loop exit → the `best` read of `$res0 := best`. 6 steps (one
`.seqn` splice glued). -/
theorem wc_segX1_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (r0 r3 : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 6 (σX L ws kvs r0 r3 tail na) (.next (kR B)) ch
      = .ok (.evalE (.var "best") (envRB B)
            (.rhsK .vals [.chain (.addr (.base ⟨3⟩)) [] []] [] []
              (.seqn #[]) (envRB B)
              (.seq [.returnStmt] (envRB B) frameK)),
          σX L ws kvs r0 r3 tail na, ch) := by
  have h1 : stepFnIter 1 (σX L ws kvs r0 r3 tail na) (.next (kR B)) ch
      = .ok (.exec retSeqn (envRB B) (.seq [] (envRB B) frameK),
          σX L ws kvs r0 r3 tail na, ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σX L ws kvs r0 r3 tail na)
    (ss := #[.assign (.var "$res0") (.var "best"), .returnStmt])
    (env := envRB B) (rest := []) (k := frameK) (ch := ch))
  have h3 : stepFnIter 4 (σX L ws kvs r0 r3 tail na)
      (.next (.seq
        ((#[.assign (.var "$res0") (.var "best"),
          .returnStmt] : Array Stmt).toList ++ [])
        (envRB B) frameK)) ch
      = .ok (.evalE (.var "best") (envRB B)
            (.rhsK .vals [.chain (.addr (.base ⟨3⟩)) [] []] [] []
              (.seqn #[]) (envRB B)
              (.seq [.returnStmt] (envRB B) frameK)),
          σX L ws kvs r0 r3 tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- X2a: the `best` value delivered → stored into `$res0` (concrete
cell 3; the wrap rides). 2 steps. -/
theorem wc_segX2a_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (r0 r3 bvv : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 2 (σX L ws kvs r0 r3 tail na)
      (.retV (.int bvv .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨3⟩)) [] []] [] [] (.seqn #[])
          (envRB B) (.seq [.returnStmt] (envRB B) frameK))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envRB B)
            (.seq [.returnStmt] (envRB B) frameK)),
          σX L ws kvs r0 (IntKind.normalize .uint64 bvv) tail na, ch) := by
  with_unfolding_all rfl

/-- X2b + the splice: → the `returnStmt` dispatch point. 2 steps. -/
theorem wc_segX2b_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (r0 r3 : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 2 (σX L ws kvs r0 r3 tail na)
      (.next (.storeK [] [] (.seqn #[]) (envRB B)
        (.seq [.returnStmt] (envRB B) frameK))) ch
      = .ok (.next (.seq
            (((#[] : Array Stmt).toList) ++ [.returnStmt]) (envRB B) frameK),
          σX L ws kvs r0 r3 tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σX L ws kvs r0 r3 tail na) (body := .seqn #[]) (env := envRB B)
    (k := .seq [.returnStmt] (envRB B) frameK) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σX L ws kvs r0 r3 tail na) (ss := #[]) (env := envRB B)
    (rest := [.returnStmt]) (k := frameK) (ch := ch))
  exact stepFnIter_chain h1 h2

/-- X2c: `return`, the frame exit's result read, the `$callres`
write-back, the driver terminal. 10 steps. -/
theorem wc_segX2c_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (r0 r3 : Int) (tail : Heap) (na : Nat)
    (B : Nat) (ch : Choices) :
    stepFnIter 10 (σX L ws kvs r0 r3 tail na)
      (.next (.seq (((#[] : Array Stmt).toList) ++ [.returnStmt])
        (envRB B) frameK)) ch
      = .ok (.next .stop,
          σX L ws kvs (IntKind.normalize .uint64 r3) r3 tail na, ch) := by
  with_unfolding_all rfl


end GoLean.Examples.WordCount
