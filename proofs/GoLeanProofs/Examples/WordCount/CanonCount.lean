import GoLeanProofs.MapMem
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.MapLoops
import GoLeanProofs.Examples.WordCount.Machine
import GoLeanProofs.Examples.WordCount.Pure

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
open GoLean.MapLoops

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false


/-! ## Entry and dispatch segments (`with_unfolding_all rfl` where every
step is address-concrete; conditioned glue at the data-dependent
points) -/

private def callK : Cont :=
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

private def stK0 (na : Nat) : Cont :=
  .stmtOpK (.mapAssign tU64 tU64) 0 []
    [.var "$c2",
     .add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64) (.intLit 1 .uint64)]
    (uEnv na) (.seq [] (uEnv na) postBodyK)
private def stK2 (na : Nat) (w : Int) : Cont :=
  .stmtOpK (.mapAssign tU64 tU64) 0
    [.int w .uint64, .map ⟨some (.base ⟨5⟩)⟩] []
    (uEnv na) (.seq [] (uEnv na) postBodyK)
private def addK (na : Nat) (w : Int) : Cont :=
  .strictK .add [] [.intLit 1 .uint64] (uEnv na) (stK2 na w)
private def mapGetK (na : Nat) (w : Int) : Cont :=
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

/-! ## The canonical placement, via the kit's bundled iteration

GAP-C1 CLOSED (kit-gap closure, 2026-08-15): the conditioned
discharges this shard carried (`wcC_init1`/`wcC_st1`/`wcC_init2`/
`wcC_st2`/`wcC_lk1`/`wcC_lk2`/`wcC_var1`/`wcC_var2`/`wcC_read`/
`wcC_mapGet`/`wcC_mapAsgn`, ~270 lines) are DELETED — the kit's
`MapLoops.mapCountIter_at` constructs them from nine placement facts,
every one of which is a `rfl` here except the front-freshness lemma
(`lookup_frontC_none`, kept above). -/

/-- **One counting iteration** (exit test true at word `i`): the map
data cell advances from the counts of `ws.take i` to those of
`ws.take (i+1)`; two fresh dead cells land at `na`, `na + 1`. 53
steps — via the kit's bundled `MapLoops.mapCountIter_at` (GAP-C1
closure, 2026-08-15). -/
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
  have h := mapCountIter_at "words" "counts" "$c1" "$c2" "i" (σC ws.length ws) (wcSeed ws 1 [] 2)
    (fun kvs iv => frontC ws.length ws kvs iv false) ws 1 5 9
    headC cmpContC postBodyK env3 u1Env uEnv
    (fun _ _ _ _ => rfl)
    (fun kvs iv x hx => lookup_frontC_none ws.length ws kvs iv false hx)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun kvs iv dead na ch => wc_segC1_raw ws.length ws kvs iv dead na ch)
    (fun kvs iv dead na₀ na ch =>
      wc_segC2_raw ws.length ws kvs iv dead na₀ na ch)
    (fun kvs iv dead na₀ na ch =>
      wc_segC3_raw ws.length ws kvs iv dead na₀ na ch)
    (fun kvs iv dead na₀ na ch =>
      wc_segC4_raw ws.length ws kvs iv dead na₀ na ch)
    (fun kvs iv dead na₀ na w ch =>
      wc_segC5_raw ws.length ws kvs iv dead na₀ na w ch)
    (fun kvs iv dead na₀ na ch =>
      wc_segC6_raw ws.length ws kvs iv dead na₀ na ch)
    (fun kvs iv dead na₀ na ch =>
      wc_segC7_raw ws.length ws kvs iv dead na₀ na ch)
    (fun kvs iv dead na₀ na w ch =>
      wc_segC8_raw ws.length ws kvs iv dead na₀ na w ch)
    (fun kvs iv dead na₀ na w ch =>
      wc_segC9_raw ws.length ws kvs iv dead na₀ na w ch)
    (fun kvs iv dead na₀ na w cv ch =>
      wc_segC10_raw ws.length ws kvs iv dead na₀ na w cv ch)
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
/-- The range-loop head: the live `mapIterK` pick point (BUG-005 (L)):
map cell at base 5, start keys `st`, produced set `pr`. -/
def rangeHead (B : Nat) (st pr : Array GoValue) : Config :=
  .next (.mapIterK none (some "c") tU64 tU64 wcRangeBody
    (some (.base ⟨5⟩)) pr st (envRB B) (kR B))

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

private theorem wcC_rangeStart (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (B na : Nat)
      (ch : Choices),
    stepFn (σC ws.length ws kvs iv false dead na)
        (.retV (.map ⟨some (.base ⟨5⟩)⟩)
          (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRB B)
            (kR B))) ch
      = .ok (.next (.mapIterK none (some "c") tU64 tU64 wcRangeBody
            (some (.base ⟨5⟩)) #[] (toKeys (kvs.map (·.1)))
            (envRB B) (kR B)),
          σC ws.length ws kvs iv false dead na, ch) := by
  intro kvs iv dead B na ch
  exact stepFn_mapRangeStart
    (rangeStart_toEntries (a := ⟨5⟩) (dty := none) rfl)

/-- **The counting loop**, by strong induction on the remaining word
count: from the exit-test delivery at word `i`, the run reaches the
RANGE HEAD over the snapshot of the full counts, with `best` zeroed at
address `na + 2·(L - i)`, within `84·(L-i) + 23` steps — the kit's
`MapLoops.mapCountLoop_generic` (exactly `84·(L−i)` to the false test)
plus this placement's own 23-step exit tower (GAP-C1 closure,
2026-08-15: the exit is deliberately example-side — histogram's exit
differs). -/
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
        = .ok (rangeHead (na + 2 * n)
              (toKeys ((countsFold ws).map (·.1))) #[],
            σC ws.length ws (countsFold ws) (ws.length : Int) false tail
              (na + 2 * n + 1), ch) := by
  intro n i hn hi dead na hna hdead ch
  obtain ⟨tail₀, htail₀, hrun₀⟩ :=
    mapCountLoop_generic (σC ws.length ws) ws 1 5 9 headC cmpContC env2 hlen
      (fun i dead na ch hi hna hdead =>
        wc_count_iter ws i dead na ch hws hlen hi hna hdead)
      (fun kvs iv dead na ch =>
        wc_segA1_raw ws.length ws kvs iv dead na ch)
      n i hn hi dead na hna hdead ch
  -- the exit tower: 23 steps, `best` allocated at `na + 2·n`
  have hX := wc_segX0_raw ws.length ws (countsFold ws)
    ((ws.length : Nat) : Int) tail₀ (na + 2 * n) ch
  have hIB := wcC_initBest ws (countsFold ws) ((ws.length : Nat) : Int)
    tail₀ (na + 2 * n) ch (by omega) htail₀
  have h1 := stepFnIter_chain hX (stepFnIter_one hIB)
  have hXb := wc_segX0b_raw ws.length ws (countsFold ws)
    ((ws.length : Nat) : Int) (tail₀ ++ [(.base ⟨na + 2 * n⟩, u64cell 0)])
    (na + 2 * n) (na + 2 * n + 1) ch
  have h2 := stepFnIter_chain h1 hXb
  have hSB := wcC_stBest ws (countsFold ws) ((ws.length : Nat) : Int)
    tail₀ (na + 2 * n) (na + 2 * n + 1) ch (by omega) htail₀
  have h3 := stepFnIter_chain h2 (stepFnIter_one hSB)
  have hXc := wc_segX0c_raw ws.length ws (countsFold ws)
    ((ws.length : Nat) : Int) (tail₀ ++ [(.base ⟨na + 2 * n⟩, u64cell 0)])
    (na + 2 * n) (na + 2 * n + 1) ch
  have h4 := stepFnIter_chain h3 hXc
  have hSn := wcC_rangeStart ws (countsFold ws) ((ws.length : Nat) : Int)
    (tail₀ ++ [(.base ⟨na + 2 * n⟩, u64cell 0)]) (na + 2 * n)
    (na + 2 * n + 1) ch
  have h5 := stepFnIter_chain h4 (stepFnIter_one hSn)
  refine ⟨84 * n + 23, tail₀ ++ [(.base ⟨na + 2 * n⟩, u64cell 0)],
    Nat.le_refl _, ?_, ?_, ?_⟩
  · intro x hx
    exact DeadFrom.push (c := u64cell 0) htail₀ x (by omega)
  · rw [lookup_append_right (htail₀ (na + 2 * n) (Nat.le_refl _))]
    exact lookup_singleton_self
  · exact stepFnIter_chain hrun₀ h5


end GoLean.Examples.WordCount
