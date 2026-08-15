import GoLeanProofs.Examples.WordCountProgram
import GoLeanProofs.MapMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Examples.WordCount.HarnessSetup

/-!
# WordCount — HarnessSubject

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
open GoLean.MapMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ### The subject phase at the harness placement (front cells 0–15,
symbolic region from 16) — the phase-C tower re-instantiated: same
statements, same step counts, new concrete addresses, and the subject
frame sitting on the harness's after-call continuation instead of the
driver's `frameK` -/

def envWCall : LocalEnv :=
  [[("$c10", .base ⟨8⟩), ("w", .base ⟨5⟩), ("$c9", .base ⟨3⟩)], hWScope0]
def afterCallKW : Cont := .seq (hWBodyList.drop 4) envWCall hWFrame0
def callKW : Cont :=
  .callArgsK ⟨"maxCount"⟩ [(.chain [], [.ref "$c10"])] [] [] envWCall
    afterCallKW
/-- The subject's call frame: result loc 10, write-back target `$c10`,
returning into the harness's tail — the abstract-outer-continuation
point of the re-instantiation. -/
def frameKH : Cont :=
  .frame [(.chain [], [.ref "$c10"])] envWCall [.base ⟨10⟩] [] afterCallKW

def sc0H : Scope := [("$res0", .base ⟨10⟩), ("words", .base ⟨9⟩)]
def sc1H : Scope := [("counts", .base ⟨13⟩), ("$c0", .base ⟨11⟩)]
def envR0H : LocalEnv := [sc1H, sc0H]
def envBH : LocalEnv :=
  [[("$forFirst", .base ⟨15⟩)], [("i", .base ⟨14⟩)], sc1H, sc0H]
def envB1H : LocalEnv := [[("i", .base ⟨14⟩)], sc1H, sc0H]
def env2H : LocalEnv := [] :: envBH
def env3H : LocalEnv := [] :: env2H
def u1EnvH (na : Nat) : LocalEnv := [("$c1", .base ⟨na⟩)] :: env2H
def uEnvH (na : Nat) : LocalEnv :=
  [("$c2", .base ⟨na + 1⟩), ("$c1", .base ⟨na⟩)] :: env2H

def tailBH : Cont :=
  .seq [] envBH (.seq [] envB1H
    (.seq [bestSeqn, wcMapRangeStmt, retSeqn] envR0H frameKH))
/-- The counting-loop head configuration (harness placement). -/
def headCH : Config :=
  .exec (.while (.boolLit true) wcWhileBody) envBH tailBH
def loopKCH : Cont := .loop (.boolLit true) wcWhileBody envBH tailBH
def bodyTailH : Cont := .seq [wcCountBody] env2H loopKCH
def cmpContCH : Cont := .ifK (.seqn #[]) .breakStmt env2H bodyTailH
def lenKH (iv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice tU64))) [] [] env2H
    (.strictK .lessCmp [.int iv .int] [] env2H cmpContCH)
def postBodyKH : Cont := .seq [] env2H loopKCH

abbrev mhCellW : HeapCell := ⟨some tMap, .map ⟨some (.base ⟨12⟩)⟩⟩

/-- The sixteen concrete front cells during the harness counting loop
(`sv` = the parked `seed` cell, `siv` = the parked setup counter). -/
def frontH (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (ff : Bool) : Heap :=
  [(.base ⟨0⟩, u64cell (L : Int)), (.base ⟨1⟩, u64cell sv),
   (.base ⟨2⟩, u64cell 0), (.base ⟨3⟩, wHandleCell L),
   (.base ⟨4⟩, arrCell L ws), (.base ⟨5⟩, wHandleCell L),
   (.base ⟨6⟩, u64cell siv), (.base ⟨7⟩, bcell false),
   (.base ⟨8⟩, u64cell 0), (.base ⟨9⟩, wHandleCell L),
   (.base ⟨10⟩, u64cell 0), (.base ⟨11⟩, mhCellW),
   (.base ⟨12⟩, mdCell kvs), (.base ⟨13⟩, mhCellW),
   (.base ⟨14⟩, intcell iv), (.base ⟨15⟩, bcell ff)]

/-- The harness phase-C state: concrete front + the symbolic dead-cell
tail. -/
def σH (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (ff : Bool) (dead : Heap)
    (na : Nat) : ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := frontH L sv siv ws kvs iv ff ++ dead, nextAddr := na }

theorem lookup_frontH_none (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (ff : Bool) {x : Nat}
    (hx : 16 ≤ x) :
    Heap.lookup (frontH L sv siv ws kvs iv ff) (.base ⟨x⟩) = none := by
  simp only [frontH, Heap.lookup,
    base_beq_false (by omega : (0 : Nat) ≠ x),
    base_beq_false (by omega : (1 : Nat) ≠ x),
    base_beq_false (by omega : (2 : Nat) ≠ x),
    base_beq_false (by omega : (3 : Nat) ≠ x),
    base_beq_false (by omega : (4 : Nat) ≠ x),
    base_beq_false (by omega : (5 : Nat) ≠ x),
    base_beq_false (by omega : (6 : Nat) ≠ x),
    base_beq_false (by omega : (7 : Nat) ≠ x),
    base_beq_false (by omega : (8 : Nat) ≠ x),
    base_beq_false (by omega : (9 : Nat) ≠ x),
    base_beq_false (by omega : (10 : Nat) ≠ x),
    base_beq_false (by omega : (11 : Nat) ≠ x),
    base_beq_false (by omega : (12 : Nat) ≠ x),
    base_beq_false (by omega : (13 : Nat) ≠ x),
    base_beq_false (by omega : (14 : Nat) ≠ x),
    base_beq_false (by omega : (15 : Nat) ≠ x),
    Bool.false_eq_true, if_false]

/-- `$c10` declared: the setup-exit state at the call's argument
delivery (cells 0–8, allocator at 9). -/
def σWCallg (n : Nat) (sv : Int) (l : List Int) (iv : Int) :
    ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := [(.base ⟨0⟩, u64cell (n : Int)), (.base ⟨1⟩, u64cell sv),
             (.base ⟨2⟩, u64cell 0), (.base ⟨3⟩, wHandleCell n),
             (.base ⟨4⟩, arrCell n l), (.base ⟨5⟩, wHandleCell n),
             (.base ⟨6⟩, u64cell iv), (.base ⟨7⟩, bcell false),
             (.base ⟨8⟩, u64cell 0)],
    nextAddr := 9 }

/-- Setup exit: test false → break unwinding → `$c10` declared → the
call's `w` argument delivered at the frame-entry point. 13 steps. -/
theorem wcH_X_raw (n : Nat) (sv iv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 13 (sWSU n sv l iv false) (.retV (.bool false) suWCmpK) ch
      = .ok (.retV (wSliceH n) callKW, σWCallg n sv l iv, ch) := by
  with_unfolding_all rfl

/-- Subject entry: frame entered (`words` at 9, `$res0` at 10), the
subject prologue (`$c0`/makeMap/`counts`/`i`/`$forFirst`) → the
counting-loop head at `nextAddr = 16`. 52 steps — the harness twin of
the canonical `wc_entryB_raw`. -/
theorem wcH_entryS_raw (n : Nat) (sv iv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 52 (σWCallg n sv l iv) (.retV (wSliceH n) callKW) ch
      = .ok (headCH, σH n sv iv l [] 0 true [] 16, ch) := by
  with_unfolding_all rfl

/-! ### The counting-loop segments at the harness placement (step
counts identical to the canonical tower — the statements are the same;
only addresses and the outer continuation differ) -/

/-- First-pass dispatch: head with the flag up → the `len(words)`
apply point. 25 steps. -/
theorem wcH_segA0_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 25 (σH L sv siv ws kvs iv true dead na) headCH ch
      = .ok (.retV (wSliceH L) (lenKH iv),
          σH L sv siv ws kvs iv false dead na, ch) := by
  with_unfolding_all rfl

/-- Later-pass dispatch: head with the flag down → `i++`, then the
`len(words)` apply point. 29 steps. -/
theorem wcH_segA1_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 29 (σH L sv siv ws kvs iv false dead na) headCH ch
      = .ok (.retV (wSliceH L)
            (lenKH (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
          σH L sv siv ws kvs
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            false dead na, ch) := by
  with_unfolding_all rfl

/-- The `<` apply after the length delivery: one step. -/
theorem wcH_cmp_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv jv : Int) (dead : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 1 (σH L sv siv ws kvs iv false dead na)
      (.retV (.int (L : Int) .int)
        (.strictK .lessCmp [.int jv .int] [] env2H cmpContCH)) ch
      = .ok (.retV (.bool (decide (jv < (L : Int)))) cmpContCH,
          σH L sv siv ws kvs iv false dead na, ch) := by
  with_unfolding_all rfl

def stK0H (na : Nat) : Cont :=
  .stmtOpK (.mapAssign tU64 tU64) 0 []
    [.var "$c2",
     .add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64) (.intLit 1 .uint64)]
    (uEnvH na) (.seq [] (uEnvH na) postBodyKH)
def stK2H (na : Nat) (w : Int) : Cont :=
  .stmtOpK (.mapAssign tU64 tU64) 0
    [.int w .uint64, .map ⟨some (.base ⟨12⟩)⟩] []
    (uEnvH na) (.seq [] (uEnvH na) postBodyKH)
def addKH (na : Nat) (w : Int) : Cont :=
  .strictK .add [] [.intLit 1 .uint64] (uEnvH na) (stK2H na w)
def mapGetKH (na : Nat) (w : Int) : Cont :=
  .strictK (.mapGet tU64 tU64) [.map ⟨some (.base ⟨12⟩)⟩] [] (uEnvH na)
    (addKH na w)

/-- C1: exit test true → the `$c1` initialization. 7 steps. -/
theorem wcH_segC1_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 7 (σH L sv siv ws kvs iv false tail na)
      (.retV (.bool true) cmpContCH) ch
      = .ok (.exec (.initialization { id := "$c1", typ := tMap }) env3H
            (.seq [asgnC1, seqnC2, mapAsgnStmt] env3H postBodyKH),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C2: `$c1` declared → its store point. 6 steps. -/
theorem wcH_segC2_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 6 (σH L sv siv ws kvs iv false tail na)
      (.next (.seq [asgnC1, seqnC2, mapAsgnStmt] (u1EnvH na₀) postBodyKH)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀⟩)) [] []]
            [.map ⟨some (.base ⟨12⟩)⟩] (.seqn #[]) (u1EnvH na₀)
            (.seq [seqnC2, mapAsgnStmt] (u1EnvH na₀) postBodyKH)),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C3 (composed from the generic glue): `$c1` stored → the `$c2`
initialization. 5 steps. -/
theorem wcH_segC3_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 5 (σH L sv siv ws kvs iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (u1EnvH na₀)
        (.seq [seqnC2, mapAsgnStmt] (u1EnvH na₀) postBodyKH))) ch
      = .ok (.exec (.initialization { id := "$c2", typ := tU64 }) (u1EnvH na₀)
            (.seq [.assign (.var "$c2")
                (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
              (u1EnvH na₀) postBodyKH),
          σH L sv siv ws kvs iv false tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σH L sv siv ws kvs iv false tail na) (body := .seqn #[])
    (env := u1EnvH na₀)
    (k := .seq [seqnC2, mapAsgnStmt] (u1EnvH na₀) postBodyKH) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σH L sv siv ws kvs iv false tail na) (ss := #[]) (env := u1EnvH na₀)
    (rest := [seqnC2, mapAsgnStmt]) (k := postBodyKH) (ch := ch))
  have h3 := stepFnIter_one (stepFn_seq_pop
    (σ := σH L sv siv ws kvs iv false tail na) (t := seqnC2)
    (rest := [mapAsgnStmt]) (env := u1EnvH na₀) (k := postBodyKH) (ch := ch))
  have h4 := stepFnIter_one (stepFn_seqn_splice
    (σ := σH L sv siv ws kvs iv false tail na)
    (ss := #[.initialization { id := "$c2", typ := tU64 },
      .assign (.var "$c2") (.indexGet (.var "words") (.var "i"))])
    (env := u1EnvH na₀) (rest := [mapAsgnStmt]) (k := postBodyKH) (ch := ch))
  have h5 := stepFnIter_one (stepFn_seq_pop
    (σ := σH L sv siv ws kvs iv false tail na)
    (t := .initialization { id := "$c2", typ := tU64 })
    (rest := [.assign (.var "$c2")
      (.indexGet (.var "words") (.var "i")), mapAsgnStmt])
    (env := u1EnvH na₀) (k := postBodyKH) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h1 h2) h3) h4) h5

/-- C4: `$c2` declared → the `words[i]` read point. 8 steps. -/
theorem wcH_segC4_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 8 (σH L sv siv ws kvs iv false tail na)
      (.next (.seq [.assign (.var "$c2")
          (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
        (uEnvH na₀) postBodyKH)) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [wSliceH L] [] (uEnvH na₀)
              (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
                (.seqn #[]) (uEnvH na₀)
                (.seq [mapAsgnStmt] (uEnvH na₀) postBodyKH))),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C5: element delivered → its store point. 1 step. -/
theorem wcH_segC5_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (w : GoValue) (ch : Choices) :
    stepFnIter 1 (σH L sv siv ws kvs iv false tail na)
      (.retV w
        (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
          (.seqn #[]) (uEnvH na₀) (.seq [mapAsgnStmt] (uEnvH na₀) postBodyKH)))
      ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [w]
            (.seqn #[]) (uEnvH na₀)
            (.seq [mapAsgnStmt] (uEnvH na₀) postBodyKH)),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C6 (composed): `$c2` stored → the `mapAssign` operand walk's first
`$c1` read. 4 steps. -/
theorem wcH_segC6_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 4 (σH L sv siv ws kvs iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (uEnvH na₀)
        (.seq [mapAsgnStmt] (uEnvH na₀) postBodyKH))) ch
      = .ok (.evalE (.var "$c1") (uEnvH na₀) (stK0H na₀),
          σH L sv siv ws kvs iv false tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σH L sv siv ws kvs iv false tail na) (body := .seqn #[])
    (env := uEnvH na₀) (k := .seq [mapAsgnStmt] (uEnvH na₀) postBodyKH)
    (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σH L sv siv ws kvs iv false tail na) (ss := #[]) (env := uEnvH na₀)
    (rest := [mapAsgnStmt]) (k := postBodyKH) (ch := ch))
  have h3 : stepFnIter 2 (σH L sv siv ws kvs iv false tail na)
      (.next (.seq ((#[] : Array Stmt).toList ++ [mapAsgnStmt]) (uEnvH na₀)
        postBodyKH)) ch
      = .ok (.evalE (.var "$c1") (uEnvH na₀) (stK0H na₀),
          σH L sv siv ws kvs iv false tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- C7: map handle delivered → the `$c2` operand read. 1 step. -/
theorem wcH_segC7_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 1 (σH L sv siv ws kvs iv false tail na)
      (.retV (.map ⟨some (.base ⟨12⟩)⟩) (stK0H na₀)) ch
      = .ok (.evalE (.var "$c2") (uEnvH na₀)
            (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨12⟩)⟩]
              [.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
                (.intLit 1 .uint64)]
              (uEnvH na₀) (.seq [] (uEnvH na₀) postBodyKH)),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C8: key delivered → the `mapGet`'s `$c1` read. 3 steps. -/
theorem wcH_segC8_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (w : Int) (ch : Choices) :
    stepFnIter 3 (σH L sv siv ws kvs iv false tail na)
      (.retV (.int w .uint64)
        (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨12⟩)⟩]
          [.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
            (.intLit 1 .uint64)]
          (uEnvH na₀) (.seq [] (uEnvH na₀) postBodyKH))) ch
      = .ok (.evalE (.var "$c1") (uEnvH na₀)
            (.strictK (.mapGet tU64 tU64) [] [.var "$c2"] (uEnvH na₀)
              (addKH na₀ w)),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C9: `mapGet`'s handle delivered → its `$c2` read. 1 step. -/
theorem wcH_segC9_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (w : Int) (ch : Choices) :
    stepFnIter 1 (σH L sv siv ws kvs iv false tail na)
      (.retV (.map ⟨some (.base ⟨12⟩)⟩)
        (.strictK (.mapGet tU64 tU64) [] [.var "$c2"] (uEnvH na₀)
          (addKH na₀ w))) ch
      = .ok (.evalE (.var "$c2") (uEnvH na₀) (mapGetKH na₀ w),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C10: the count delivered → the `+ 1` runs → the `mapAssign` apply
point. 3 steps. -/
theorem wcH_segC10_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (w cv : Int) (ch : Choices) :
    stepFnIter 3 (σH L sv siv ws kvs iv false tail na)
      (.retV (.int cv .uint64) (addKH na₀ w)) ch
      = .ok (.retV (.int (IntKind.normalize .uint64 (cv + 1)) .uint64)
            (stK2H na₀ w),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C11: `mapAssign` applied → back to the loop head. 3 steps. -/
theorem wcH_segC11_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 3 (σH L sv siv ws kvs iv false tail na)
      (.next (.seq [] (uEnvH na₀) postBodyKH)) ch
      = .ok (headCH, σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl


/-! ### Counting-loop exit → the range head (harness placement) -/

def envRBH (B : Nat) : LocalEnv :=
  (("best", .base ⟨B⟩) :: sc1H) :: [sc0H]
def kRH (B : Nat) : Cont := .seq [retSeqn] (envRBH B) frameKH
/-- The range-loop head: the `mapIterK` pick point at snapshot `rem`. -/
def rangeHeadH (B : Nat) (rem : List (Int × Nat)) : Config :=
  .next (.mapIterK none (some "c") tU64 tU64 wcRangeBody (toEntries rem)
    (envRBH B) (kRH B))

/-- X0: exit test false → break unwinding → the `best` initialization.
9 steps. -/
theorem wcH_segX0_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 9 (σH L sv siv ws kvs iv false tail na)
      (.retV (.bool false) cmpContCH) ch
      = .ok (.exec (.initialization { id := "best", typ := tU64 }) envR0H
            (.seq [.assign (.var "best") (.intLit 0 .uint64),
              wcMapRangeStmt, retSeqn] envR0H frameKH),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- X0b: `best` declared → its zeroing store point. 6 steps. -/
theorem wcH_segX0b_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 6 (σH L sv siv ws kvs iv false tail na)
      (.next (.seq [.assign (.var "best") (.intLit 0 .uint64),
        wcMapRangeStmt, retSeqn] (envRBH B) frameKH)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
            [.int 0 .uint64] (.seqn #[]) (envRBH B)
            (.seq [wcMapRangeStmt, retSeqn] (envRBH B) frameKH)),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- X0c: `best` stored → the ranged map handle delivered at the
snapshot point. 5 steps (one `.seqn` splice glued). -/
theorem wcH_segX0c_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 5 (σH L sv siv ws kvs iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (envRBH B)
        (.seq [wcMapRangeStmt, retSeqn] (envRBH B) frameKH))) ch
      = .ok (.retV (.map ⟨some (.base ⟨12⟩)⟩)
            (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRBH B)
              (kRH B)),
          σH L sv siv ws kvs iv false tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σH L sv siv ws kvs iv false tail na) (body := .seqn #[])
    (env := envRBH B) (k := .seq [wcMapRangeStmt, retSeqn] (envRBH B) frameKH)
    (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σH L sv siv ws kvs iv false tail na) (ss := #[]) (env := envRBH B)
    (rest := [wcMapRangeStmt, retSeqn]) (k := frameKH) (ch := ch))
  have h3 : stepFnIter 3 (σH L sv siv ws kvs iv false tail na)
      (.next (.seq ((#[] : Array Stmt).toList ++ [wcMapRangeStmt, retSeqn])
        (envRBH B) frameKH)) ch
      = .ok (.retV (.map ⟨some (.base ⟨12⟩)⟩)
            (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRBH B)
              (kRH B)),
          σH L sv siv ws kvs iv false tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3



end GoLean.Examples.WordCount
