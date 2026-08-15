import GoLeanProofs.Examples.WordCountProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Examples.WordCount.CountGeneric

/-!
# WordCount — CanonCount

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
open GoLean.MapMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false


/-! ## Entry and dispatch segments (`with_unfolding_all rfl` where every
step is address-concrete; conditioned glue at the data-dependent
points) -/

def callK : Cont :=
  .callArgsK ⟨"maxCount"⟩ [(.chain [], [.ref "$callres"])] [] [] wcEnv .stop

/-- Entry A: driver start → the slice-expression apply point. 7 steps. -/
theorem wc_entryA_raw (ws : List Int) (ch : Choices) :
    stepFnIter 7 (wcSeed ws 1 [] 2) (.exec (wcCall ws 1) wcEnv .stop) ch
      = .ok (.retV (.int (IntKind.normalize .int (ws.length : Int)) .int)
            (.strictK (.sliceExpr false) [.int 0 .int, .addr (.base ⟨1⟩)] []
              wcEnv callK),
          wcSeed ws 1 [] 2, ch) := by
  with_unfolding_all rfl

/-- Entry B: frame entry, `$c0`/`makeMap`/`counts`/`i`/`$forFirst`
setup → the counting-loop head at `nextAddr = 9`. 52 steps. -/
theorem wc_entryB_raw (ws : List Int) (ch : Choices) :
    stepFnIter 52 (wcSeed ws 1 [] 2) (.retV (sliceH ws.length) callK) ch
      = .ok (headC, σC ws.length ws [] 0 true [] 9, ch) := by
  with_unfolding_all rfl

/-- First-pass dispatch: head with the flag up → the `len(words)` apply
point (the flag comes down; counters untouched). 25 steps. -/
theorem wc_segA0_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 25 (σC L ws kvs iv true dead na) headC ch
      = .ok (.retV (sliceH L) (lenK iv), σC L ws kvs iv false dead na, ch) := by
  with_unfolding_all rfl

/-- Later-pass dispatch: head with the flag down → `i++`, then the
`len(words)` apply point. 29 steps. -/
private theorem wc_segA1_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 29 (σC L ws kvs iv false dead na) headC ch
      = .ok (.retV (sliceH L)
            (lenK (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
          σC L ws kvs
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            false dead na, ch) := by
  with_unfolding_all rfl

/-- The `<` apply after the length delivery: one step, the comparison
riding symbolically. -/
theorem wc_cmp_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv jv : Int) (dead : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 1 (σC L ws kvs iv false dead na)
      (.retV (.int (L : Int) .int)
        (.strictK .lessCmp [.int jv .int] [] env2 cmpContC)) ch
      = .ok (.retV (.bool (decide (jv < (L : Int)))) cmpContC,
          σC L ws kvs iv false dead na, ch) := by
  with_unfolding_all rfl

/-! ## The counting-iteration segments (§10c glue: the per-iteration
`$c1`/`$c2` cells live at the SYMBOLIC addresses `na`, `na + 1`) -/

theorem lookup_frontC_none (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (ff : Bool) {x : Nat} (hx : 9 ≤ x) :
    Heap.lookup (frontC L ws kvs iv ff) (.base ⟨x⟩) = none := by
  simp only [frontC, Heap.lookup,
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

def stK0 (na : Nat) : Cont :=
  .stmtOpK (.mapAssign tU64 tU64) 0 []
    [.var "$c2",
     .add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64) (.intLit 1 .uint64)]
    (uEnv na) (.seq [] (uEnv na) postBodyK)
def stK2 (na : Nat) (w : Int) : Cont :=
  .stmtOpK (.mapAssign tU64 tU64) 0
    [.int w .uint64, .map ⟨some (.base ⟨5⟩)⟩] []
    (uEnv na) (.seq [] (uEnv na) postBodyK)
def addK (na : Nat) (w : Int) : Cont :=
  .strictK .add [] [.intLit 1 .uint64] (uEnv na) (stK2 na w)
def mapGetK (na : Nat) (w : Int) : Cont :=
  .strictK (.mapGet tU64 tU64) [.map ⟨some (.base ⟨5⟩)⟩] [] (uEnv na)
    (addK na w)

/-- C1: exit test true → the `$c1` initialization. 7 steps. -/
private theorem wc_segC1_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 7 (σC L ws kvs iv false tail na) (.retV (.bool true) cmpContC)
      ch
      = .ok (.exec (.initialization { id := "$c1", typ := tMap }) env3
            (.seq [asgnC1, seqnC2, mapAsgnStmt] env3 postBodyK),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C2: `$c1` declared → its store point (`$c1 := counts` delivered). 6
steps. -/
private theorem wc_segC2_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 6 (σC L ws kvs iv false tail na)
      (.next (.seq [asgnC1, seqnC2, mapAsgnStmt] (u1Env na₀) postBodyK)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀⟩)) [] []]
            [.map ⟨some (.base ⟨5⟩)⟩] (.seqn #[]) (u1Env na₀)
            (.seq [seqnC2, mapAsgnStmt] (u1Env na₀) postBodyK)),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C3 (composed from glue: two `.seqn` splices under the symbolic env):
`$c1` stored → the `$c2` initialization. 5 steps. -/
private theorem wc_segC3_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 5 (σC L ws kvs iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (u1Env na₀)
        (.seq [seqnC2, mapAsgnStmt] (u1Env na₀) postBodyK))) ch
      = .ok (.exec (.initialization { id := "$c2", typ := tU64 }) (u1Env na₀)
            (.seq [.assign (.var "$c2")
                (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
              (u1Env na₀) postBodyK),
          σC L ws kvs iv false tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σC L ws kvs iv false tail na) (body := .seqn #[])
    (env := u1Env na₀)
    (k := .seq [seqnC2, mapAsgnStmt] (u1Env na₀) postBodyK) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σC L ws kvs iv false tail na) (ss := #[]) (env := u1Env na₀)
    (rest := [seqnC2, mapAsgnStmt]) (k := postBodyK) (ch := ch))
  have h3 := stepFnIter_one (stepFn_seq_pop
    (σ := σC L ws kvs iv false tail na) (t := seqnC2)
    (rest := [mapAsgnStmt]) (env := u1Env na₀) (k := postBodyK) (ch := ch))
  have h4 := stepFnIter_one (stepFn_seqn_splice
    (σ := σC L ws kvs iv false tail na)
    (ss := #[.initialization { id := "$c2", typ := tU64 },
      .assign (.var "$c2") (.indexGet (.var "words") (.var "i"))])
    (env := u1Env na₀) (rest := [mapAsgnStmt]) (k := postBodyK) (ch := ch))
  have h5 := stepFnIter_one (stepFn_seq_pop
    (σ := σC L ws kvs iv false tail na)
    (t := .initialization { id := "$c2", typ := tU64 })
    (rest := [.assign (.var "$c2")
      (.indexGet (.var "words") (.var "i")), mapAsgnStmt])
    (env := u1Env na₀) (k := postBodyK) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h1 h2) h3) h4) h5

/-- C4: `$c2` declared → the `words[i]` read point. 8 steps. -/
private theorem wc_segC4_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 8 (σC L ws kvs iv false tail na)
      (.next (.seq [.assign (.var "$c2")
          (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
        (uEnv na₀) postBodyK)) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [sliceH L] [] (uEnv na₀)
              (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
                (.seqn #[]) (uEnv na₀)
                (.seq [mapAsgnStmt] (uEnv na₀) postBodyK))),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C5: element delivered → its store point. 1 step. -/
private theorem wc_segC5_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (w : GoValue) (ch : Choices) :
    stepFnIter 1 (σC L ws kvs iv false tail na)
      (.retV w
        (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
          (.seqn #[]) (uEnv na₀) (.seq [mapAsgnStmt] (uEnv na₀) postBodyK)))
      ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [w]
            (.seqn #[]) (uEnv na₀)
            (.seq [mapAsgnStmt] (uEnv na₀) postBodyK)),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C6 (composed): `$c2` stored → the `mapAssign` operand walk's first
`$c1` read. 4 steps. -/
private theorem wc_segC6_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 4 (σC L ws kvs iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (uEnv na₀)
        (.seq [mapAsgnStmt] (uEnv na₀) postBodyK))) ch
      = .ok (.evalE (.var "$c1") (uEnv na₀) (stK0 na₀),
          σC L ws kvs iv false tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σC L ws kvs iv false tail na) (body := .seqn #[])
    (env := uEnv na₀) (k := .seq [mapAsgnStmt] (uEnv na₀) postBodyK)
    (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σC L ws kvs iv false tail na) (ss := #[]) (env := uEnv na₀)
    (rest := [mapAsgnStmt]) (k := postBodyK) (ch := ch))
  have h3 : stepFnIter 2 (σC L ws kvs iv false tail na)
      (.next (.seq ((#[] : Array Stmt).toList ++ [mapAsgnStmt]) (uEnv na₀)
        postBodyK)) ch
      = .ok (.evalE (.var "$c1") (uEnv na₀) (stK0 na₀),
          σC L ws kvs iv false tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- C7: map handle delivered → the `$c2` operand read. 1 step. -/
private theorem wc_segC7_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 1 (σC L ws kvs iv false tail na)
      (.retV (.map ⟨some (.base ⟨5⟩)⟩) (stK0 na₀)) ch
      = .ok (.evalE (.var "$c2") (uEnv na₀)
            (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨5⟩)⟩]
              [.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
                (.intLit 1 .uint64)]
              (uEnv na₀) (.seq [] (uEnv na₀) postBodyK)),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C8: key delivered → the `mapGet`'s `$c1` read. 3 steps. -/
private theorem wc_segC8_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (w : Int) (ch : Choices) :
    stepFnIter 3 (σC L ws kvs iv false tail na)
      (.retV (.int w .uint64)
        (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨5⟩)⟩]
          [.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
            (.intLit 1 .uint64)]
          (uEnv na₀) (.seq [] (uEnv na₀) postBodyK))) ch
      = .ok (.evalE (.var "$c1") (uEnv na₀)
            (.strictK (.mapGet tU64 tU64) [] [.var "$c2"] (uEnv na₀)
              (addK na₀ w)),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C9: `mapGet`'s handle delivered → its `$c2` read. 1 step. -/
private theorem wc_segC9_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (w : Int) (ch : Choices) :
    stepFnIter 1 (σC L ws kvs iv false tail na)
      (.retV (.map ⟨some (.base ⟨5⟩)⟩)
        (.strictK (.mapGet tU64 tU64) [] [.var "$c2"] (uEnv na₀)
          (addK na₀ w))) ch
      = .ok (.evalE (.var "$c2") (uEnv na₀) (mapGetK na₀ w),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C10: the count delivered → the `+ 1` runs → the `mapAssign` apply
point. 3 steps. -/
private theorem wc_segC10_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (w cv : Int) (ch : Choices) :
    stepFnIter 3 (σC L ws kvs iv false tail na)
      (.retV (.int cv .uint64) (addK na₀ w)) ch
      = .ok (.retV (.int (IntKind.normalize .uint64 (cv + 1)) .uint64)
            (stK2 na₀ w),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C11: `mapAssign` applied → back to the loop head. 3 steps. -/
private theorem wc_segC11_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 3 (σC L ws kvs iv false tail na)
      (.next (.seq [] (uEnv na₀) postBodyK)) ch
      = .ok (headC, σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-! ## The composed counting iteration -/

-- (`take_succ_getD` and `cnt_take_le` are the kit's, via
-- `open GoLean.MapMem` — the local copies were deleted in the GAP-P1
-- closure.)

/-! ## The canonical placement's discharge lemmas (the generic layer's
hypotheses at `S := σC ws.length ws`; every statement pins the full
transition — the E-form made structural) -/

private theorem wcC_init1 (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
      (ch : Choices), 9 ≤ na → DeadFrom dead na →
    stepFn (σC ws.length ws kvs iv false dead na)
        (.exec (.initialization { id := "$c1", typ := tMap }) env3
          (.seq [asgnC1, seqnC2, mapAsgnStmt] env3 postBodyK)) ch
      = .ok (.next (.seq [asgnC1, seqnC2, mapAsgnStmt] (u1Env na) postBodyK),
          σC ws.length ws kvs iv false (dead ++ [(.base ⟨na⟩, nilMapCell)])
            (na + 1), ch) := by
  intro kvs iv dead na ch hna hdead
  have hmiss : Heap.lookup
      (frontC ws.length ws kvs iv false ++ dead) (.base ⟨na⟩) = none := by
    rw [lookup_append_right (lookup_frontC_none ws.length ws kvs iv false
      hna)]
    exact hdead na (Nat.le_refl na)
  have h := stepFn_init_seq (σ := σC ws.length ws kvs iv false dead na)
    (p := { id := "$c1", typ := tMap })
    (rest := [asgnC1, seqnC2, mapAsgnStmt]) (env := env3) (k := postBodyK)
    (ch := ch) (v := .map ⟨none⟩)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show (σC ws.length ws kvs iv false dead na).nextAddr = na from rfl,
    show (σC ws.length ws kvs iv false dead na).heap
      = frontC ws.length ws kvs iv false ++ dead from rfl,
    set_fresh hmiss, List.append_assoc] at h
  exact h

private theorem wcC_st1 (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ na : Nat)
      (ch : Choices), 9 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, nilMapCell)]) na)
        (.next (.storeK [.chain (.addr (.base ⟨na₀⟩)) [] []]
          [.map ⟨some (.base ⟨5⟩)⟩] (.seqn #[]) (u1Env na₀)
          (.seq [seqnC2, mapAsgnStmt] (u1Env na₀) postBodyK))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (u1Env na₀)
            (.seq [seqnC2, mapAsgnStmt] (u1Env na₀) postBodyK)),
          σC ws.length ws kvs iv false (dead ++ [(.base ⟨na₀⟩, mhCell)]) na,
          ch) := by
  intro kvs iv dead na₀ na ch hna hdead
  have hlook : Heap.lookup
      (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, nilMapCell)]) na).heap
      (.base ⟨na₀⟩) = some ⟨some tMap, .map ⟨none⟩⟩ := by
    show Heap.lookup
      (frontC ws.length ws kvs iv false
        ++ (dead ++ [(.base ⟨na₀⟩, nilMapCell)]))
      (.base ⟨na₀⟩) = some ⟨some tMap, .map ⟨none⟩⟩
    rw [lookup_append_right (lookup_frontC_none ws.length ws kvs iv false
        hna),
      lookup_append_right (hdead na₀ (Nat.le_refl na₀))]
    exact lookup_singleton_self
  have h := storeTarget_addr (v := .map ⟨some (.base ⟨5⟩)⟩)
    (v' := .map ⟨some (.base ⟨5⟩)⟩) hlook
    (by simp [normalizeValueForTy, normalizeValueForTyFuel,
      typeResolutionFuel])
  rw [show (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, nilMapCell)]) na).heap
      = frontC ws.length ws kvs iv false
        ++ (dead ++ [(.base ⟨na₀⟩, nilMapCell)]) from rfl,
    set_append_right (lookup_frontC_none ws.length ws kvs iv false hna),
    set_append_right (hdead na₀ (Nat.le_refl na₀)),
    set_singleton_self] at h
  exact stepFn_store_step h

private theorem wcC_init2 (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ : Nat)
      (ch : Choices), 9 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 5)]) (na₀ + 1))
        (.exec (.initialization { id := "$c2", typ := tU64 }) (u1Env na₀)
          (.seq [.assign (.var "$c2")
              (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
            (u1Env na₀) postBodyK)) ch
      = .ok (.next (.seq [.assign (.var "$c2")
            (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
            (uEnv na₀) postBodyK),
          σC ws.length ws kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell 0)])
            (na₀ + 2), ch) := by
  intro kvs iv dead na₀ ch hna hdead
  have hmiss : Heap.lookup
      (frontC ws.length ws kvs iv false ++ (dead ++ [(.base ⟨na₀⟩, mhG 5)]))
      (.base ⟨na₀ + 1⟩) = none := by
    rw [lookup_append_right
        (lookup_frontC_none ws.length ws kvs iv false (by omega)),
      lookup_append_right (hdead (na₀ + 1) (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
    rfl
  have h := stepFn_init_seq
    (σ := σC ws.length ws kvs iv false (dead ++ [(.base ⟨na₀⟩, mhG 5)])
      (na₀ + 1))
    (p := { id := "$c2", typ := tU64 })
    (rest := [.assign (.var "$c2")
      (.indexGet (.var "words") (.var "i")), mapAsgnStmt])
    (env := u1Env na₀) (k := postBodyK) (ch := ch)
    (v := .int 0 .uint64)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show (σC ws.length ws kvs iv false (dead ++ [(.base ⟨na₀⟩, mhG 5)])
        (na₀ + 1)).nextAddr = na₀ + 1 from rfl,
    show (σC ws.length ws kvs iv false (dead ++ [(.base ⟨na₀⟩, mhG 5)])
        (na₀ + 1)).heap
      = frontC ws.length ws kvs iv false ++ (dead ++ [(.base ⟨na₀⟩, mhG 5)])
      from rfl,
    set_fresh hmiss, List.append_assoc, List.append_assoc] at h
  exact h

private theorem wcC_st2 (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ na : Nat)
      (w : Int) (ch : Choices), 0 ≤ w → w < 2 ^ 64 →
      9 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell 0)]) na)
        (.next (.storeK [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []]
          [.int w .uint64] (.seqn #[]) (uEnv na₀)
          (.seq [mapAsgnStmt] (uEnv na₀) postBodyK))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (uEnv na₀)
            (.seq [mapAsgnStmt] (uEnv na₀) postBodyK)),
          σC ws.length ws kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell w)])
            na, ch) := by
  intro kvs iv dead na₀ na w ch hw0 hw64 hna hdead
  have hwnorm : IntKind.normalize .uint64 w = w := unorm_of_range hw0 hw64
  have hlook : Heap.lookup
      (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell 0)])
        na).heap
      (.base ⟨na₀ + 1⟩) = some ⟨some tU64, .int 0 .uint64⟩ := by
    show Heap.lookup
      (frontC ws.length ws kvs iv false
        ++ (dead ++ ([(.base ⟨na₀⟩, mhG 5)]
          ++ [(.base ⟨na₀ + 1⟩, u64cell 0)])))
      (.base ⟨na₀ + 1⟩) = some ⟨some tU64, .int 0 .uint64⟩
    rw [lookup_append_right
        (lookup_frontC_none ws.length ws kvs iv false (by omega)),
      lookup_append_right (hdead (na₀ + 1) (by omega)),
      lookup_append_right (show Heap.lookup [(.base ⟨na₀⟩, mhG 5)]
          (.base ⟨na₀ + 1⟩) = none from by
        rw [lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
        rfl)]
    exact lookup_singleton_self
  have h := storeTarget_addr (v := .int w .uint64) (v' := .int w .uint64)
    hlook
    (by
      simp only [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel]
      rw [hwnorm]
      rfl)
  rw [show (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell 0)])
        na).heap
      = frontC ws.length ws kvs iv false
        ++ (dead ++ ([(.base ⟨na₀⟩, mhG 5)]
          ++ [(.base ⟨na₀ + 1⟩, u64cell 0)])) from rfl,
    set_append_right (lookup_frontC_none ws.length ws kvs iv false
      (by omega)),
    set_append_right (hdead (na₀ + 1) (by omega)),
    set_append_right (show Heap.lookup [(.base ⟨na₀⟩, mhG 5)]
        (.base ⟨na₀ + 1⟩) = none from by
      rw [lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
      rfl),
    set_singleton_self] at h
  exact stepFn_store_step h

private theorem wcC_lk1 (ws : List Int) (kvs : List (Int × Nat)) (iv w : Int)
    (dead : Heap) (na₀ na : Nat) (hna : 9 ≤ na₀) (hdead : DeadFrom dead na₀) :
    Heap.lookup (σC ws.length ws kvs iv false
      (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell w)]) na).heap
      (.base ⟨na₀⟩) = some mhCell := by
  show Heap.lookup
    (frontC ws.length ws kvs iv false
      ++ (dead ++ ([(.base ⟨na₀⟩, mhCell)]
        ++ [(.base ⟨na₀ + 1⟩, u64cell w)])))
    (.base ⟨na₀⟩) = some mhCell
  rw [lookup_append_right (lookup_frontC_none ws.length ws kvs iv false hna),
    lookup_append_right (hdead na₀ (Nat.le_refl na₀))]
  exact lookup_append_left lookup_singleton_self

private theorem wcC_lk2 (ws : List Int) (kvs : List (Int × Nat)) (iv w : Int)
    (dead : Heap) (na₀ na : Nat) (hna : 9 ≤ na₀) (hdead : DeadFrom dead na₀) :
    Heap.lookup (σC ws.length ws kvs iv false
      (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell w)]) na).heap
      (.base ⟨na₀ + 1⟩) = some (u64cell w) := by
  show Heap.lookup
    (frontC ws.length ws kvs iv false
      ++ (dead ++ ([(.base ⟨na₀⟩, mhCell)]
        ++ [(.base ⟨na₀ + 1⟩, u64cell w)])))
    (.base ⟨na₀ + 1⟩) = some (u64cell w)
  rw [lookup_append_right
      (lookup_frontC_none ws.length ws kvs iv false (by omega)),
    lookup_append_right (hdead (na₀ + 1) (by omega)),
    lookup_append_right (show Heap.lookup [(.base ⟨na₀⟩, mhCell)]
        (.base ⟨na₀ + 1⟩) = none from by
      rw [lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
      rfl)]
  exact lookup_singleton_self

private theorem wcC_var1 (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv w : Int) (dead : Heap) (na₀ na : Nat)
      (k : Cont) (ch : Choices), 9 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell w)]) na)
        (.evalE (.var "$c1") (uEnv na₀) k) ch
      = .ok (.retV (.map ⟨some (.base ⟨5⟩)⟩) k,
          σC ws.length ws kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell w)])
            na, ch) := by
  intro kvs iv w dead na₀ na k ch hna hdead
  exact stepFn_var rfl (wcC_lk1 ws kvs iv w dead na₀ na hna hdead)

private theorem wcC_var2 (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv w : Int) (dead : Heap) (na₀ na : Nat)
      (k : Cont) (ch : Choices), 9 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell w)]) na)
        (.evalE (.var "$c2") (uEnv na₀) k) ch
      = .ok (.retV (.int w .uint64) k,
          σC ws.length ws kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell w)])
            na, ch) := by
  intro kvs iv w dead na₀ na k ch hna hdead
  exact stepFn_var rfl (wcC_lk2 ws kvs iv w dead na₀ na hna hdead)

private theorem wcC_read (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (i : Nat) (dead : Heap) (na : Nat),
      i < ws.length →
    applyStrictOp (σC ws.length ws kvs ((i : Nat) : Int) false dead na)
        .indexGet [wsHG 1 ws.length, .int ((i : Nat) : Int) .int]
      = .ok (.int (ws.getD i 0) .uint64,
          σC ws.length ws kvs ((i : Nat) : Int) false dead na) := by
  intro kvs i dead na hi
  have hget : (⟨ws.map (fun v => .int v .uint64)⟩ : Array GoValue)[0 + i]?
      = some (.int (ws.getD i 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU ws i hi]
  exact applyStrictOp_indexGet_slice (dty := some (.array ws.length tU64))
    (off := 0) (len := ws.length) (cap := ws.length) (ik := .int) rfl
    (Nat.le_refl ws.length) hi hget

private theorem wcC_mapGet (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
      (w : Int), 0 ≤ w → w < 2 ^ 64 →
    applyStrictOp (σC ws.length ws kvs iv false dead na) (.mapGet tU64 tU64)
        [.map ⟨some (.base ⟨5⟩)⟩, .int w .uint64]
      = .ok (.int (cnt kvs w : Int) .uint64,
          σC ws.length ws kvs iv false dead na) := by
  intro kvs iv dead na w hw0 hw64
  exact applyStrictOp_mapGet (a := ⟨5⟩) (dty := none) rfl
    (unorm_of_range hw0 hw64)

private theorem wcC_mapAsgn (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ na : Nat)
      (w : Int) (v : Nat) (ch : Choices), 0 ≤ w → w < 2 ^ 64 → v < 2 ^ 64 →
    stepFn (σC ws.length ws kvs iv false dead na)
        (.retV (.int ((v : Nat) : Int) .uint64)
          (.stmtOpK (.mapAssign tU64 tU64) 0
            [.int w .uint64, .map ⟨some (.base ⟨5⟩)⟩] []
            (uEnv na₀) (.seq [] (uEnv na₀) postBodyK))) ch
      = .ok (.next (.seq [] (uEnv na₀) postBodyK),
          σC ws.length ws (setk kvs w v) iv false dead na, ch) := by
  intro kvs iv dead na₀ na w v ch hw0 hw64 hv
  have hMA := mapAssignValue_toEntries (a := ⟨5⟩)
    (σ := σC ws.length ws kvs iv false dead na)
    (v := v) rfl (unorm_of_range hw0 hw64)
    (unorm_of_range (by omega) (by exact_mod_cast hv))
  rw [show Heap.set (σC ws.length ws kvs iv false dead na).heap (.base ⟨5⟩)
      ⟨none, .mapData (toEntries (setk kvs w v))⟩
      = frontC ws.length ws (setk kvs w v) iv false ++ dead from rfl] at hMA
  exact stepFn_mapAssign_apply hMA

/-- **One counting iteration** (exit test true at word `i`): the map
data cell advances from the counts of `ws.take i` to those of
`ws.take (i+1)`; two fresh dead cells land at `na`, `na + 1`. 53
steps — INSTANTIATED from the placement-generic `wcIter_generic`
(consolidation slice 2026-08-13). -/
private theorem wc_count_iter (ws : List Int) (i : Nat) (dead : Heap)
    (na : Nat) (ch : Choices)
    (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64) (hlen : ws.length < 2 ^ 63)
    (hi : i < ws.length) (hna : 9 ≤ na)
    (hdead : ∀ x : Nat, na ≤ x → Heap.lookup dead (.base ⟨x⟩) = none) :
    stepFnIter 53
      (σC ws.length ws (countsFold (ws.take i)) (i : Int) false dead na)
      (.retV (.bool true) cmpContC) ch
      = .ok (headC,
          σC ws.length ws (countsFold (ws.take (i + 1))) (i : Int) false
            (dead ++ [(.base ⟨na⟩, mhCell),
              (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2), ch) := by
  have hw := hws (ws.getD i 0) (getD_mem hi)
  have hcnt : cnt (countsFold (ws.take i)) (ws.getD i 0) + 1 < 2 ^ 64 := by
    have := cnt_take_le (ws := ws) (i := i) (ws.getD i 0)
    omega
  have h := wcIter_generic (σC ws.length ws) ws 1 5 9 headC cmpContC
    postBodyK env3 u1Env uEnv
    (fun kvs iv dead na ch => wc_segC1_raw ws.length ws kvs iv dead na ch)
    (wcC_init1 ws)
    (fun kvs iv dead na₀ na ch =>
      wc_segC2_raw ws.length ws kvs iv dead na₀ na ch)
    (wcC_st1 ws)
    (fun kvs iv dead na₀ na ch =>
      wc_segC3_raw ws.length ws kvs iv dead na₀ na ch)
    (wcC_init2 ws)
    (fun kvs iv dead na₀ na ch =>
      wc_segC4_raw ws.length ws kvs iv dead na₀ na ch)
    (wcC_read ws)
    (fun kvs iv dead na₀ na w ch =>
      wc_segC5_raw ws.length ws kvs iv dead na₀ na w ch)
    (wcC_st2 ws)
    (fun kvs iv dead na₀ na ch =>
      wc_segC6_raw ws.length ws kvs iv dead na₀ na ch)
    (wcC_var1 ws)
    (wcC_var2 ws)
    (fun kvs iv dead na₀ na ch =>
      wc_segC7_raw ws.length ws kvs iv dead na₀ na ch)
    (fun kvs iv dead na₀ na w ch =>
      wc_segC8_raw ws.length ws kvs iv dead na₀ na w ch)
    (fun kvs iv dead na₀ na w ch =>
      wc_segC9_raw ws.length ws kvs iv dead na₀ na w ch)
    (wcC_mapGet ws)
    (fun kvs iv dead na₀ na w cv ch =>
      wc_segC10_raw ws.length ws kvs iv dead na₀ na w cv ch)
    (wcC_mapAsgn ws)
    (fun kvs iv dead na₀ na ch =>
      wc_segC11_raw ws.length ws kvs iv dead na₀ na ch)
    (countsFold (ws.take i)) i dead na ch hi hw.1 hw.2 hcnt hna hdead
  rw [show setk (countsFold (ws.take i)) (ws.getD i 0)
      (cnt (countsFold (ws.take i)) (ws.getD i 0) + 1)
      = countsFold (ws.take (i + 1)) from by
    rw [setk_cnt_succ, ← countsFold_append, ← take_succ_getD hi]] at h
  exact h

/-! ## Exit of the counting loop → the range head -/

def envRB (B : Nat) : LocalEnv := (("best", .base ⟨B⟩) :: sc1) :: [sc0]
def kR (B : Nat) : Cont := .seq [retSeqn] (envRB B) frameK
/-- The range-loop head: the `mapIterK` pick point at snapshot `rem`. -/
def rangeHead (B : Nat) (rem : List (Int × Nat)) : Config :=
  .next (.mapIterK none (some "c") tU64 tU64 wcRangeBody (toEntries rem)
    (envRB B) (kR B))

/-- X0: exit test false → break unwinding → the `best` initialization.
9 steps. -/
private theorem wc_segX0_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 9 (σC L ws kvs iv false tail na)
      (.retV (.bool false) cmpContC) ch
      = .ok (.exec (.initialization { id := "best", typ := tU64 }) envR0
            (.seq [.assign (.var "best") (.intLit 0 .uint64),
              wcMapRangeStmt, retSeqn] envR0 frameK),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- X0b: `best` declared → its zeroing store point. 6 steps. -/
private theorem wc_segX0b_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 6 (σC L ws kvs iv false tail na)
      (.next (.seq [.assign (.var "best") (.intLit 0 .uint64),
        wcMapRangeStmt, retSeqn] (envRB B) frameK)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
            [.int 0 .uint64] (.seqn #[]) (envRB B)
            (.seq [wcMapRangeStmt, retSeqn] (envRB B) frameK)),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- X0c: `best` stored → the ranged map handle delivered at the
snapshot point. 5 steps (one `.seqn` splice glued). -/
private theorem wc_segX0c_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 5 (σC L ws kvs iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (envRB B)
        (.seq [wcMapRangeStmt, retSeqn] (envRB B) frameK))) ch
      = .ok (.retV (.map ⟨some (.base ⟨5⟩)⟩)
            (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRB B)
              (kR B)),
          σC L ws kvs iv false tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σC L ws kvs iv false tail na) (body := .seqn #[])
    (env := envRB B) (k := .seq [wcMapRangeStmt, retSeqn] (envRB B) frameK)
    (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σC L ws kvs iv false tail na) (ss := #[]) (env := envRB B)
    (rest := [wcMapRangeStmt, retSeqn]) (k := frameK) (ch := ch))
  have h3 : stepFnIter 3 (σC L ws kvs iv false tail na)
      (.next (.seq ((#[] : Array Stmt).toList ++ [wcMapRangeStmt, retSeqn])
        (envRB B) frameK)) ch
      = .ok (.retV (.map ⟨some (.base ⟨5⟩)⟩)
            (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRB B)
              (kR B)),
          σC L ws kvs iv false tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- The counts-list range facts (keys are words; values are counts). -/
theorem countsFold_norm (ws : List Int)
    (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64) (hlen : ws.length < 2 ^ 63) :
    ∀ p ∈ countsFold ws, IntKind.normalize .uint64 p.1 = p.1
      ∧ IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int) := by
  intro p hp
  have hkey : p.1 ∈ ws := by
    exact countsFold_key_mem hp
  have hkr := hws p.1 hkey
  have hvle : p.2 ≤ ws.length := countsFold_val_le ws hp
  refine ⟨unorm_of_range hkr.1 hkr.2, unorm_of_range (by omega) ?_⟩
  have : p.2 < 2 ^ 64 := by omega
  exact_mod_cast this

private theorem wcC_initBest (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
      (ch : Choices), 9 ≤ na → DeadFrom dead na →
    stepFn (σC ws.length ws kvs iv false dead na)
        (.exec (.initialization { id := "best", typ := tU64 }) envR0
          (.seq [.assign (.var "best") (.intLit 0 .uint64),
            wcMapRangeStmt, retSeqn] envR0 frameK)) ch
      = .ok (.next (.seq [.assign (.var "best") (.intLit 0 .uint64),
            wcMapRangeStmt, retSeqn] (envRB na) frameK),
          σC ws.length ws kvs iv false (dead ++ [(.base ⟨na⟩, u64cell 0)])
            (na + 1), ch) := by
  intro kvs iv dead na ch hna hdead
  have hmiss : Heap.lookup
      (frontC ws.length ws kvs iv false ++ dead) (.base ⟨na⟩) = none := by
    rw [lookup_append_right (lookup_frontC_none ws.length ws kvs iv false
      hna)]
    exact hdead na (Nat.le_refl na)
  have h := stepFn_init_seq (σ := σC ws.length ws kvs iv false dead na)
    (p := { id := "best", typ := tU64 })
    (rest := [.assign (.var "best") (.intLit 0 .uint64),
      wcMapRangeStmt, retSeqn])
    (env := envR0) (k := frameK) (ch := ch) (v := .int 0 .uint64)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show (σC ws.length ws kvs iv false dead na).nextAddr = na from rfl,
    show (σC ws.length ws kvs iv false dead na).heap
      = frontC ws.length ws kvs iv false ++ dead from rfl,
    set_fresh hmiss, List.append_assoc] at h
  exact h

private theorem wcC_stBest (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (B na : Nat)
      (ch : Choices), 9 ≤ B → DeadFrom dead B →
    stepFn (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨B⟩, u64cell 0)]) na)
        (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
          [.int 0 .uint64] (.seqn #[]) (envRB B)
          (.seq [wcMapRangeStmt, retSeqn] (envRB B) frameK))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envRB B)
            (.seq [wcMapRangeStmt, retSeqn] (envRB B) frameK)),
          σC ws.length ws kvs iv false (dead ++ [(.base ⟨B⟩, u64cell 0)]) na,
          ch) := by
  intro kvs iv dead B na ch hB hdead
  have hlook : Heap.lookup
      (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨B⟩, u64cell 0)]) na).heap
      (.base ⟨B⟩) = some ⟨some tU64, .int 0 .uint64⟩ := by
    show Heap.lookup
      (frontC ws.length ws kvs iv false ++ (dead ++ [(.base ⟨B⟩, u64cell 0)]))
      (.base ⟨B⟩) = some ⟨some tU64, .int 0 .uint64⟩
    rw [lookup_append_right (lookup_frontC_none ws.length ws kvs iv false hB),
      lookup_append_right (hdead B (Nat.le_refl B))]
    exact lookup_singleton_self
  have h := storeTarget_addr (v := .int 0 .uint64) (v' := .int 0 .uint64)
    hlook
    (by simp [normalizeValueForTy, normalizeValueForTyFuel,
      typeResolutionFuel, IntKind.normalize, IntKind.bits?, IntKind.signed])
  rw [show (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨B⟩, u64cell 0)]) na).heap
      = frontC ws.length ws kvs iv false ++ (dead ++ [(.base ⟨B⟩, u64cell 0)])
      from rfl,
    set_append_right (lookup_frontC_none ws.length ws kvs iv false hB),
    set_append_right (hdead B (Nat.le_refl B)),
    set_singleton_self] at h
  exact stepFn_store_step h

private theorem wcC_snap (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (B na : Nat)
      (ch : Choices),
      (∀ p ∈ kvs, IntKind.normalize .uint64 p.1 = p.1
        ∧ IntKind.normalize .uint64 ((p.2 : Nat) : Int)
            = ((p.2 : Nat) : Int)) →
    stepFn (σC ws.length ws kvs iv false dead na)
        (.retV (.map ⟨some (.base ⟨5⟩)⟩)
          (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRB B)
            (kR B))) ch
      = .ok (.next (.mapIterK none (some "c") tU64 tU64 wcRangeBody
            (toEntries kvs) (envRB B) (kR B)),
          σC ws.length ws kvs iv false dead na, ch) := by
  intro kvs iv dead B na ch hkv
  exact stepFn_snapshot (snapshot_toEntries (a := ⟨5⟩) (dty := none) rfl hkv)

/-- **The counting loop**, by strong induction on the remaining word
count: from the exit-test delivery at word `i`, the run reaches the
RANGE HEAD over the snapshot of the full counts, with `best` zeroed at
address `na + 2·(L - i)`, within `84·(L-i) + 23` steps — INSTANTIATED
from the placement-generic `wcLoop_generic` (consolidation slice
2026-08-13). -/
theorem wc_count_loop (ws : List Int)
    (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64) (hlen : ws.length < 2 ^ 63) :
    ∀ (n i : Nat), n = ws.length - i → i ≤ ws.length →
    ∀ (dead : Heap) (na : Nat), 9 ≤ na →
    (∀ x : Nat, na ≤ x → Heap.lookup dead (.base ⟨x⟩) = none) →
    ∀ ch : Choices,
    ∃ (k : Nat) (tail : Heap),
      k ≤ 84 * n + 23
      ∧ (∀ x : Nat, na + 2 * n + 1 ≤ x →
          Heap.lookup tail (.base ⟨x⟩) = none)
      ∧ Heap.lookup tail (.base ⟨na + 2 * n⟩) = some (u64cell 0)
      ∧ stepFnIter k
          (σC ws.length ws (countsFold (ws.take i)) (i : Int) false dead na)
          (.retV (.bool (decide ((i : Int) < (ws.length : Int)))) cmpContC)
          ch
        = .ok (rangeHead (na + 2 * n) (countsFold ws),
            σC ws.length ws (countsFold ws) (ws.length : Int) false tail
              (na + 2 * n + 1), ch) := by
  intro n i hn hi dead na hna hdead ch
  obtain ⟨k, tail, hk, htail, hbest, hrun⟩ :=
    wcLoop_generic (σC ws.length ws) ws 1 5 9 headC cmpContC frameK
      env2 envR0 envRB kR hlen
      (fun i dead na ch hi hna hdead =>
        wc_count_iter ws i dead na ch hws hlen hi hna hdead)
      (fun kvs iv dead na ch =>
        wc_segA1_raw ws.length ws kvs iv dead na ch)
      (fun kvs iv dead na ch =>
        wc_segX0_raw ws.length ws kvs iv dead na ch)
      (wcC_initBest ws)
      (fun kvs iv dead B na ch =>
        wc_segX0b_raw ws.length ws kvs iv dead B na ch)
      (wcC_stBest ws)
      (fun kvs iv dead B na ch =>
        wc_segX0c_raw ws.length ws kvs iv dead B na ch)
      (wcC_snap ws)
      (countsFold_norm ws hws hlen)
      n i hn hi dead na hna hdead ch
  exact ⟨k, tail, hk, htail, hbest, hrun⟩


end GoLean.Examples.WordCount
