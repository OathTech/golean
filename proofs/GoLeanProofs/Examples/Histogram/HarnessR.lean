import GoLeanProofs.Examples.Histogram.CountLoop

/-!
# Histogram — the harness run (entry, setup, copy, query, range, exit)

The `histogram_harness_r` run, PROGRAM-generic throughout: every raw
segment is proven over an abstract `σ` (only `heap`/`nextAddr` pinned),
and the one step that consults the program — the `histogram(v, q)`
frame entry — is conditioned through `StepKit.stepFn_call_enter`. The
pinned program is unfolded exactly twice in this example: the lowering
pins (`Histogram.Machine`) and that one `enterFrame` discharge.

The counting loop lives in `Histogram.CountLoop` (imported here);
everything else, and the end-to-end run, is here.

## Kit gaps witnessed here (campaign log `g1.md`)

* **GAP-P2** — `histPre` re-derives wordcount's `wcPre` (the copy
  loop's zero-padded prefix invariant), which re-derives minmax's. It
  is the `SliceMem.familyMod` companion: shape wanted is
  `SliceMem.prefixPad (fam : Nat → Nat → List Int) (cap m seed : Nat)`
  with `zero`/`length`/`range`/`set`/`full` proven once. Three landed
  consumers (minmax, wordcount, histogram).
* **GAP-R1 — CLOSED** (kit-gap closure, 2026-08-15): the §10b
  choice-pick induction now lives in the kit as
  `MapLoops.mapPickLoop_generic`, over an abstract state descriptor
  with the whole per-iteration effect as ONE hypothesis — no body, no
  binder shape. `hg_range_loop` below instantiates it with the
  conservation invariant "`distinct` + remaining entries = constant";
  `hg_range_iter` supplies the 16-step iteration, given the pick.
-/

namespace GoLean.Examples.Histogram

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem
open GoLean.MapMem
open GoLean.MapLoops

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## The copy loop's array invariant

GAP-P2 CLOSED (kit-gap closure, 2026-08-15): `histPre` is the kit's
`prefixPad` at cap 8; the facts are one-line delegations. -/

/-- The `vals` array after `m` copy steps: the family prefix, the rest
still the array's zero default. -/
def histPre (m seed : Nat) : List Int :=
  prefixPad (GoLean.SliceMem.familyMod 3) 8 m seed

theorem histPre_zero (seed : Nat) : histPre 0 seed = List.replicate 8 0 :=
  prefixPad_zero rfl

theorem histPre_length {m seed : Nat} (h : m ≤ 8) :
    (histPre m seed).length = 8 :=
  prefixPad_length (familyMod_length 3 m seed) h

theorem histPre_range {m seed : Nat} :
    ∀ v ∈ histPre m seed, 0 ≤ v ∧ v < 2 ^ 64 :=
  prefixPad_range (familyMod_range 3 m seed)

theorem histPre_set {seed m : Nat} (hm : m < 8) :
    (histPre m seed).set m (((seed + m % 3) % 2 ^ 64 : Nat) : Int)
      = histPre (m + 1) seed :=
  prefixPad_familyMod_set hm

/-- The copy loop's terminal list IS `histArr8`'s content at the
family. -/
theorem histPre_full {n seed : Nat} :
    histPre n seed
      = histFamily n seed
          ++ List.replicate (8 - (histFamily n seed).length) 0 :=
  prefixPad_full (familyMod_length 3 n seed)

/-! ## Heap-lookup facts -/

theorem lookup_suH (σ : ExecState) (nv sv qv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ff : Bool) (na : Nat) :
    Heap.lookup (hSt σ (hHeapSu nv sv qv n l iv ff) na).heap (.base ⟨7⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [hHeapSu, hHeap0, Heap.lookup]

theorem lookup_cpV_H (σ : ExecState) (nv sv qv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ff : Bool) (na : Nat) :
    Heap.lookup (hSt σ (hHeapCp nv sv qv n l lp siv civ ff) na).heap
        (.base ⟨7⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [hHeapCp, hHeapSu, hHeap0, Heap.lookup]

theorem lookup_cpVals_H (σ : ExecState) (nv sv qv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ff : Bool) (na : Nat) :
    Heap.lookup (hSt σ (hHeapCp nv sv qv n l lp siv civ ff) na).heap
        (.base ⟨11⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨lp.map (fun v => .int v .uint64)⟩⟩ := by
  simp [hHeapCp, hHeapSu, hHeap0, Heap.lookup]

/-! ## Raw run segments — PROGRAM-generic throughout -/

/-- Entry A: body start → the `$c12` makeSlice apply point. 10 steps. -/
theorem h_E1_raw (σ : ExecState) (nv sv qv : Int) (ch : Choices) :
    stepFnIter 10 (hSt σ (hHeap0 nv sv qv) 6) hHC0 ch
      = .ok (.retV (.int nv .uint64)
          (.stmtOpK (.makeSlice tU64 false) 1
            [.addr (.base ⟨6⟩)] [] envC12H
            (.seq [hS2, hS3, hS4, hS5, hS6, hS7] envC12H
              (.frame [] [] [] [] .stop))),
        hSt σ (hHeapC12 nv sv qv) 7, ch) := by
  with_unfolding_all rfl

/-- **`make([]uint64, n)` at SYMBOLIC `n`.** -/
theorem h_make_apply (σ : ExecState) (nv sv qv : Int) (n : Nat)
    (ch : Choices) :
    applyStmtOp (hSt σ (hHeapC12 nv sv qv) 7) ch (.makeSlice tU64 false) 1
      [.addr (.base ⟨6⟩), .int (n : Nat) .uint64]
      = .ok (hSt σ (hHeapMake nv sv qv n) 8, ch) := by
  have hnn1 := natFromNonneg_cast
    "runtime error: makeslice: len out of range" n
  have hnn2 := natFromNonneg_cast
    "runtime error: makeslice: cap out of range" n
  have hb := GoLean.Iris.buildDefaultArrayValue_int
    (hSt σ (hHeapC12 nv sv qv) 7) .uint64 n
  have harr : (List.replicate n (GoValue.int 0 .uint64)).toArray
      = (⟨(List.replicate n (0 : Int)).map
          (fun v => GoValue.int v .uint64)⟩ : Array GoValue) := by
    simp [List.map_replicate]
  rw [harr] at hb
  simp only [applyStmtOp, applyStmtOpCore, valueAsInt, valueAsLoc,
    hnn1, hnn2, hb, Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (Nat.lt_irrefl n)]
  with_unfolding_all rfl

/-- Entry B: `v := $c12`, the setup counter and flag → the setup loop
head. 42 steps. -/
theorem h_E2_raw (σ : ExecState) (nv sv qv : Int) (n : Nat) (ch : Choices) :
    stepFnIter 42 (hSt σ (hHeapMake nv sv qv n) 8)
      (.next (.seq [hS2, hS3, hS4, hS5, hS6, hS7] envC12H
        (.frame [] [] [] [] .stop))) ch
      = .ok (suHeadCfgH,
          hSt σ (hHeapSu nv sv qv n (List.replicate n 0) 0 true) 11, ch) := by
  with_unfolding_all rfl

/-! ### The setup loop -/

theorem su_A0_rawH (σ : ExecState) (nv sv qv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 25 (hSt σ (hHeapSu nv sv qv n l iv true) 11) suHeadCfgH ch
      = .ok (.retV (.bool (decide (iv < nv))) suCmpKH,
          hSt σ (hHeapSu nv sv qv n l iv false) 11, ch) := by
  with_unfolding_all rfl

theorem su_A1_rawH (σ : ExecState) (nv sv qv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 29 (hSt σ (hHeapSu nv sv qv n l iv false) 11) suHeadCfgH ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < nv))) suCmpKH,
          hSt σ (hHeapSu nv sv qv n l
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false) 11, ch) := by
  with_unfolding_all rfl

/-- Setup fill phase A: test true → the `%` apply point. 19 steps. -/
theorem su_B1a_rawH (σ : ExecState) (nv sv qv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 19 (hSt σ (hHeapSu nv sv qv n l iv false) 11)
      (.retV (.bool true) suCmpKH) ch
      = .ok (.retV (.int 3 .uint64) (suModKH n sv iv),
          hSt σ (hHeapSu nv sv qv n l iv false) 11, ch) := by
  with_unfolding_all rfl

/-- Setup fill phase B: the `%` result → the add → the element-store
point. 2 steps. -/
theorem su_B1b_rawH (σ : ExecState) (nv sv qv : Int) (n : Nat) (l : List Int)
    (iv rv : Int) (ch : Choices) :
    stepFnIter 2 (hSt σ (hHeapSu nv sv qv n l iv false) 11)
      (.retV (.int rv .uint64) (suAddKH n sv iv)) ch
      = .ok (.next (.storeK [suRefH n iv]
            [.int (IntKind.normalize .uint64 (sv + rv)) .uint64]
            (.seqn #[]) suEnvH2 suStTailH),
          hSt σ (hHeapSu nv sv qv n l iv false) 11, ch) := by
  with_unfolding_all rfl

theorem su_D_rawH (σ : ExecState) (nv sv qv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 5 (hSt σ (hHeapSu nv sv qv n l iv false) 11)
      (.next (.storeK [] [] (.seqn #[]) suEnvH2 suStTailH)) ch
      = .ok (suHeadCfgH, hSt σ (hHeapSu nv sv qv n l iv false) 11, ch) := by
  with_unfolding_all rfl

/-- Setup exit: test false → `var vals` declared (an `.initialization`,
NOT a `makeSlice`) and the copy loop head. 39 steps. -/
theorem su_X_rawH (σ : ExecState) (nv sv qv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 39 (hSt σ (hHeapSu nv sv qv n l iv false) 11)
      (.retV (.bool false) suCmpKH) ch
      = .ok (cpHeadCfgH,
          hSt σ (hHeapCp nv sv qv n l zeros8 iv 0 true) 14, ch) := by
  with_unfolding_all rfl

/-! ### The copy loop -/

theorem cp_A0_rawH (σ : ExecState) (nv sv qv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 25 (hSt σ (hHeapCp nv sv qv n l lp siv civ true) 14)
      cpHeadCfgH ch
      = .ok (.retV (.bool (decide (civ < nv))) cpCmpKH,
          hSt σ (hHeapCp nv sv qv n l lp siv civ false) 14, ch) := by
  with_unfolding_all rfl

theorem cp_A1_rawH (σ : ExecState) (nv sv qv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 29 (hSt σ (hHeapCp nv sv qv n l lp siv civ false) 14)
      cpHeadCfgH ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1))
              < nv))) cpCmpKH,
          hSt σ (hHeapCp nv sv qv n l lp siv
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1)))
            false) 14, ch) := by
  with_unfolding_all rfl

/-- Copy phase 1: test true → the `vals[i]` target banked, the `v[i]`
read at its apply point. 16 steps. -/
theorem cp_B1_rawH (σ : ExecState) (nv sv qv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 16 (hSt σ (hHeapCp nv sv qv n l lp siv civ false) 14)
      (.retV (.bool true) cpCmpKH) ch
      = .ok (.retV (.int civ .uint64)
            (.strictK .indexGet [hSliceV n] [] cpEnvH2 (cpRhsKH civ)),
          hSt σ (hHeapCp nv sv qv n l lp siv civ false) 14, ch) := by
  with_unfolding_all rfl

theorem cp_B2_rawH (σ : ExecState) (nv sv qv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1 (hSt σ (hHeapCp nv sv qv n l lp siv civ false) 14)
      (.retV w (cpRhsKH civ)) ch
      = .ok (.next (.storeK [cpRefH civ] [w] (.seqn #[]) cpEnvH2 cpStTailH),
          hSt σ (hHeapCp nv sv qv n l lp siv civ false) 14, ch) := by
  with_unfolding_all rfl

theorem cp_D_rawH (σ : ExecState) (nv sv qv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 5 (hSt σ (hHeapCp nv sv qv n l lp siv civ false) 14)
      (.next (.storeK [] [] (.seqn #[]) cpEnvH2 cpStTailH)) ch
      = .ok (cpHeadCfgH, hSt σ (hHeapCp nv sv qv n l lp siv civ false) 14,
          ch) := by
  with_unfolding_all rfl

/-- Copy exit: test false → `hits`/`distinct` declared and BOTH
`histogram(v, q)` arguments delivered at the drained `callArgsK`. 17
steps (wordcount's 13 plus the four the second argument costs). -/
theorem cp_X_rawH (σ : ExecState) (nv sv qv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 17 (hSt σ (hHeapCp nv sv qv n l lp siv civ false) 14)
      (.retV (.bool false) cpCmpKH) ch
      = .ok (.retV (.int qv .uint64) (hCallArgsK2 n),
          hSt σ (hHeapCall nv sv qv n l lp siv civ) 16, ch) := by
  with_unfolding_all rfl

/-- The `histogram` prologue: `$c0`/makeMap/`counts`/`i`/`$forFirst` →
the counting-loop head at `nextAddr = 25`. 51 steps, program-free given
the frame entry. -/
theorem h_prologue_rawH (σ : ExecState) (sv qv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 51
      (hSt σ (hHeapHFrame ((n : Nat) : Int) sv qv n l lp siv civ) 20)
      (.exec histogramFunc.body hFrameEnv frameKH) ch
      = .ok (headCH, σH σ n sv qv siv civ l lp [] 0 true [] 25, ch) := by
  with_unfolding_all rfl

/-! ### The counting loop's entry test (its body is `Histogram.CountLoop`) -/

theorem hg_segA0_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (na : Nat) (ch : Choices) :
    stepFnIter 25 (σH σ L sv qv siv civ ws lp kvs iv true dead na) headCH ch
      = .ok (.retV (hSliceV L) (lenKH iv),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  with_unfolding_all rfl

theorem hg_cmp_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv jv : Int) (dead : Heap)
    (na : Nat) (ch : Choices) :
    stepFnIter 1 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.retV (.int (L : Int) .int)
        (.strictK .lessCmp [.int jv .int] [] env2H cmpContCH)) ch
      = .ok (.retV (.bool (decide (jv < (L : Int)))) cmpContCH,
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  with_unfolding_all rfl

/-! ## The query phase: `hits := counts[q]` -/

/-- The `hits` declaration allocates the cell at the loop's `nextAddr`
(`B`). -/
theorem hg_initHits (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
      (ch : Choices), 25 ≤ na → DeadFrom dead na →
    stepFn (σH σ L sv qv siv civ ws lp kvs iv false dead na)
        (.exec (.initialization { id := "hits", typ := tU64 }) envR0H
          (.seq [.assign (.var "hits")
              (.mapGet (.var "counts") (.var "q") tU64 tU64),
            distinctSeqn, hMapRangeStmt, hRetSeqn] envR0H frameKH)) ch
      = .ok (.next (.seq [.assign (.var "hits")
              (.mapGet (.var "counts") (.var "q") tU64 tU64),
            distinctSeqn, hMapRangeStmt, hRetSeqn] (envRBH na) frameKH),
          σH σ L sv qv siv civ ws lp kvs iv false
            (dead ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1), ch) := by
  intro kvs iv dead na ch hna hdead
  have hmiss : Heap.lookup
      (frontH L sv qv siv civ ws lp kvs iv false ++ dead) (.base ⟨na⟩)
      = none := by
    rw [lookup_append_right
      (lookup_frontH_none L sv qv siv civ ws lp kvs iv false hna)]
    exact hdead na (Nat.le_refl na)
  have h := stepFn_init_seq
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead na)
    (p := { id := "hits", typ := tU64 }) (env := envR0H)
    (rest := [.assign (.var "hits")
        (.mapGet (.var "counts") (.var "q") tU64 tU64),
      distinctSeqn, hMapRangeStmt, hRetSeqn]) (k := frameKH)
    (ch := ch) (v := .int 0 .uint64)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show (σH σ L sv qv siv civ ws lp kvs iv false dead na).nextAddr = na
      from rfl,
    show (σH σ L sv qv siv civ ws lp kvs iv false dead na).heap
      = frontH L sv qv siv civ ws lp kvs iv false ++ dead from rfl,
    set_fresh hmiss, List.append_assoc] at h
  exact h

/-- Query A: the declaration's tail → the `counts[q]` apply point. 8
steps. -/
theorem hg_qA_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (B na : Nat) (ch : Choices) :
    stepFnIter 8 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.next (.seq [.assign (.var "hits")
          (.mapGet (.var "counts") (.var "q") tU64 tU64),
        distinctSeqn, hMapRangeStmt, hRetSeqn] (envRBH B) frameKH)) ch
      = .ok (.retV (.int qv .uint64)
            (.strictK (.mapGet tU64 tU64) [.map ⟨some (.base ⟨21⟩)⟩] []
              (envRBH B)
              (.rhsK .vals [.chain (.addr (.base ⟨B⟩)) [] []] [] []
                (.seqn #[]) (envRBH B)
                (.seq [distinctSeqn, hMapRangeStmt, hRetSeqn] (envRBH B)
                  frameKH))),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  with_unfolding_all rfl

/-- **The map READ**: `counts[q]` answers `cnt kvs q`, and an ABSENT
key answers Go's zero value — which is `occurrences q ws = 0` on the
spec side. -/
theorem hg_queryGet (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (B na : Nat)
      (ch : Choices), IntKind.normalize .uint64 qv = qv →
    stepFn (σH σ L sv qv siv civ ws lp kvs iv false dead na)
        (.retV (.int qv .uint64)
          (.strictK (.mapGet tU64 tU64) [.map ⟨some (.base ⟨21⟩)⟩] []
            (envRBH B)
            (.rhsK .vals [.chain (.addr (.base ⟨B⟩)) [] []] [] []
              (.seqn #[]) (envRBH B)
              (.seq [distinctSeqn, hMapRangeStmt, hRetSeqn] (envRBH B)
                frameKH)))) ch
      = .ok (.retV (.int (cnt kvs qv : Int) .uint64)
            (.rhsK .vals [.chain (.addr (.base ⟨B⟩)) [] []] [] []
              (.seqn #[]) (envRBH B)
              (.seq [distinctSeqn, hMapRangeStmt, hRetSeqn] (envRBH B)
                frameKH)),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  intro kvs iv dead B na ch hq
  exact stepFn_strict_apply
    (applyStrictOp_mapGet (a := ⟨21⟩) (dty := none) rfl hq)

/-- Query B: the read result → the `hits` store point. 1 step. -/
theorem hg_qB_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (B na : Nat) (hv : Int) (ch : Choices) :
    stepFnIter 1 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.retV (.int hv .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨B⟩)) [] []] [] [] (.seqn #[])
          (envRBH B)
          (.seq [distinctSeqn, hMapRangeStmt, hRetSeqn] (envRBH B)
            frameKH))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
            [.int hv .uint64] (.seqn #[])
            (envRBH B)
            (.seq [distinctSeqn, hMapRangeStmt, hRetSeqn] (envRBH B)
              frameKH)),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  with_unfolding_all rfl

/-- The `hits` store, at the symbolic cell `B` in the dead tail. -/
theorem hg_stHits (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (B na : Nat)
      (bv hv : Int) (ch : Choices), 25 ≤ B →
      Heap.lookup dead (.base ⟨B⟩) = some (u64cell bv) →
      IntKind.normalize .uint64 hv = hv →
    stepFn (σH σ L sv qv siv civ ws lp kvs iv false dead na)
        (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
          [.int hv .uint64] (.seqn #[]) (envRBH B)
          (.seq [distinctSeqn, hMapRangeStmt, hRetSeqn] (envRBH B)
            frameKH))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envRBH B)
            (.seq [distinctSeqn, hMapRangeStmt, hRetSeqn] (envRBH B)
              frameKH)),
          σH σ L sv qv siv civ ws lp kvs iv false
            (Heap.set dead (.base ⟨B⟩) ⟨some tU64, .int hv .uint64⟩) na,
          ch) := by
  intro kvs iv dead B na bv hv ch hB hlk hn
  have hlook : Heap.lookup
      (σH σ L sv qv siv civ ws lp kvs iv false dead na).heap (.base ⟨B⟩)
      = some ⟨some tU64, .int bv .uint64⟩ := by
    show Heap.lookup (frontH L sv qv siv civ ws lp kvs iv false ++ dead)
      (.base ⟨B⟩) = some ⟨some tU64, .int bv .uint64⟩
    rw [lookup_append_right
      (lookup_frontH_none L sv qv siv civ ws lp kvs iv false hB)]
    exact hlk
  have h := storeTarget_addr (v := .int hv .uint64) (v' := .int hv .uint64)
    hlook
    (by
      simp only [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel]
      rw [hn]
      rfl)
  rw [show (σH σ L sv qv siv civ ws lp kvs iv false dead na).heap
      = frontH L sv qv siv civ ws lp kvs iv false ++ dead from rfl,
    set_append_right
      (lookup_frontH_none L sv qv siv civ ws lp kvs iv false hB)] at h
  exact stepFn_store_step h

/-- Query C: the store drains → the `distinct` declaration. 5 steps. -/
theorem hg_qC_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (B na : Nat) (ch : Choices) :
    stepFnIter 5 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.next (.storeK [] [] (.seqn #[]) (envRBH B)
        (.seq [distinctSeqn, hMapRangeStmt, hRetSeqn] (envRBH B) frameKH)))
      ch
      = .ok (.exec (.initialization { id := "distinct", typ := tU64 })
            (envRBH B)
            (.seq [.assign (.var "distinct") (.intLit 0 .uint64),
              hMapRangeStmt, hRetSeqn] (envRBH B) frameKH),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead na)
    (body := .seqn #[]) (env := envRBH B)
    (k := .seq [distinctSeqn, hMapRangeStmt, hRetSeqn] (envRBH B) frameKH)
    (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead na) (ss := #[])
    (env := envRBH B) (rest := [distinctSeqn, hMapRangeStmt, hRetSeqn])
    (k := frameKH) (ch := ch))
  have h3 := stepFnIter_one (stepFn_seq_pop
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead na)
    (t := distinctSeqn) (rest := [hMapRangeStmt, hRetSeqn])
    (env := envRBH B) (k := frameKH) (ch := ch))
  have h4 := stepFnIter_one (stepFn_seqn_splice
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead na)
    (ss := #[.initialization { id := "distinct", typ := tU64 },
      .assign (.var "distinct") (.intLit 0 .uint64)])
    (env := envRBH B) (rest := [hMapRangeStmt, hRetSeqn])
    (k := frameKH) (ch := ch))
  have h5 := stepFnIter_one (stepFn_seq_pop
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead na)
    (t := .initialization { id := "distinct", typ := tU64 })
    (rest := [.assign (.var "distinct") (.intLit 0 .uint64),
      hMapRangeStmt, hRetSeqn])
    (env := envRBH B) (k := frameKH) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h1 h2) h3) h4) h5

/-! ## `distinct := 0` and the range head -/

theorem hg_initDistinct (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (B na : Nat)
      (ch : Choices), 25 ≤ na → DeadFrom dead na → B + 1 = na →
    stepFn (σH σ L sv qv siv civ ws lp kvs iv false dead na)
        (.exec (.initialization { id := "distinct", typ := tU64 })
          (envRBH B)
          (.seq [.assign (.var "distinct") (.intLit 0 .uint64),
            hMapRangeStmt, hRetSeqn] (envRBH B) frameKH)) ch
      = .ok (.next (.seq [.assign (.var "distinct") (.intLit 0 .uint64),
            hMapRangeStmt, hRetSeqn] (envRBDH B) frameKH),
          σH σ L sv qv siv civ ws lp kvs iv false
            (dead ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1), ch) := by
  intro kvs iv dead B na ch hna hdead hBna
  have hmiss : Heap.lookup
      (frontH L sv qv siv civ ws lp kvs iv false ++ dead) (.base ⟨na⟩)
      = none := by
    rw [lookup_append_right
      (lookup_frontH_none L sv qv siv civ ws lp kvs iv false hna)]
    exact hdead na (Nat.le_refl na)
  subst hBna
  have h := stepFn_init_seq
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead (B + 1))
    (p := { id := "distinct", typ := tU64 }) (env := envRBH B)
    (rest := [.assign (.var "distinct") (.intLit 0 .uint64),
      hMapRangeStmt, hRetSeqn]) (k := frameKH)
    (ch := ch) (v := .int 0 .uint64)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show (σH σ L sv qv siv civ ws lp kvs iv false dead (B + 1)).nextAddr
      = B + 1 from rfl,
    show (σH σ L sv qv siv civ ws lp kvs iv false dead (B + 1)).heap
      = frontH L sv qv siv civ ws lp kvs iv false ++ dead from rfl,
    set_fresh hmiss, List.append_assoc] at h
  exact h

/-- Range head A: `distinct = 0` up to its store point. 6 steps. -/
theorem hg_rA_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (B na : Nat) (ch : Choices) :
    stepFnIter 6 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.next (.seq [.assign (.var "distinct") (.intLit 0 .uint64),
        hMapRangeStmt, hRetSeqn] (envRBDH B) frameKH)) ch
      = .ok (.next (.storeK [rngRef B] [.int 0 .uint64] (.seqn #[])
            (envRBDH B)
            (.seq [hMapRangeStmt, hRetSeqn] (envRBDH B) frameKH)),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  with_unfolding_all rfl

/-- The `distinct` store, at the symbolic cell `B + 1`. -/
theorem hg_stDistinct (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (B na : Nat)
      (bv dv : Int) (k : Cont) (ch : Choices), 25 ≤ B + 1 →
      Heap.lookup dead (.base ⟨B + 1⟩) = some (u64cell bv) →
      IntKind.normalize .uint64 dv = dv →
    ∀ (rs : List TargetRef) (vs : List GoValue) (body : Stmt)
      (env : LocalEnv),
    stepFn (σH σ L sv qv siv civ ws lp kvs iv false dead na)
        (.next (.storeK (rngRef B :: rs) (.int dv .uint64 :: vs) body env k))
        ch
      = .ok (.next (.storeK rs vs body env k),
          σH σ L sv qv siv civ ws lp kvs iv false
            (Heap.set dead (.base ⟨B + 1⟩) ⟨some tU64, .int dv .uint64⟩) na,
          ch) := by
  intro kvs iv dead B na bv dv k ch hB hlk hn rs vs body env
  have hlook : Heap.lookup
      (σH σ L sv qv siv civ ws lp kvs iv false dead na).heap (.base ⟨B + 1⟩)
      = some ⟨some tU64, .int bv .uint64⟩ := by
    show Heap.lookup (frontH L sv qv siv civ ws lp kvs iv false ++ dead)
      (.base ⟨B + 1⟩) = some ⟨some tU64, .int bv .uint64⟩
    rw [lookup_append_right
      (lookup_frontH_none L sv qv siv civ ws lp kvs iv false hB)]
    exact hlk
  have h := storeTarget_addr (v := .int dv .uint64) (v' := .int dv .uint64)
    hlook
    (by
      simp only [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel]
      rw [hn]
      rfl)
  rw [show (σH σ L sv qv siv civ ws lp kvs iv false dead na).heap
      = frontH L sv qv siv civ ws lp kvs iv false ++ dead from rfl,
    set_append_right
      (lookup_frontH_none L sv qv siv civ ws lp kvs iv false hB)] at h
  exact stepFn_store_step h

/-- Range head B: the store drains → the `counts` handle delivered at
the `mapRangeK` snapshot point. 5 steps. -/
theorem hg_rB_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (B na : Nat) (ch : Choices) :
    stepFnIter 5 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.next (.storeK [] [] (.seqn #[]) (envRBDH B)
        (.seq [hMapRangeStmt, hRetSeqn] (envRBDH B) frameKH))) ch
      = .ok (.retV (.map ⟨some (.base ⟨21⟩)⟩)
            (.mapRangeK none none tU64 tU64 hRangeBody (envRBDH B) (kRH B)),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead na)
    (body := .seqn #[]) (env := envRBDH B)
    (k := .seq [hMapRangeStmt, hRetSeqn] (envRBDH B) frameKH) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead na) (ss := #[])
    (env := envRBDH B) (rest := [hMapRangeStmt, hRetSeqn]) (k := frameKH)
    (ch := ch))
  have h3 : stepFnIter 3 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.next (.seq ((#[] : Array Stmt).toList ++ [hMapRangeStmt, hRetSeqn])
        (envRBDH B) frameKH)) ch
      = .ok (.retV (.map ⟨some (.base ⟨21⟩)⟩)
            (.mapRangeK none none tU64 tU64 hRangeBody (envRBDH B) (kRH B)),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- The range START (BUG-005 (L)): the map data cell read once for the
base loc and the start-key set; the produced set begins empty. -/
theorem hg_rangeStart (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (B na : Nat)
      (ch : Choices),
    stepFn (σH σ L sv qv siv civ ws lp kvs iv false dead na)
        (.retV (.map ⟨some (.base ⟨21⟩)⟩)
          (.mapRangeK none none tU64 tU64 hRangeBody (envRBDH B) (kRH B))) ch
      = .ok (.next (iterKH B (toKeys (kvs.map (·.1))) #[]),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  intro kvs iv dead B na ch
  exact stepFn_mapRangeStart (rangeStart_toEntries (a := ⟨21⟩) (dty := none) rfl)

/-! ## The range loop (GAP-R1)

The whole per-iteration content is: consume one choice, erase the
picked entry, add one to `distinct`. Nothing else moves — no cell is
allocated (the binders are absent), the map is untouched, and the body
has no branch. So the number of iterations is `rem.length` at EVERY
choice stream, which is exactly why `distinctCount` is provable here
and "the first key visited" would not be. -/

/-- Range R1: after the pick, up to the `distinct` read. 6 steps. -/
theorem hg_R1_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (st pr : Array GoValue)
    (iv : Int) (dead : Heap)
    (B na : Nat) (ch : Choices) :
    stepFnIter 6 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.exec hRangeBody (envIt1 B) (iterKH B st pr)) ch
      = .ok (.evalE (.var "distinct") (envIt2 B) (rngAddK B st pr),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  with_unfolding_all rfl

/-- The `distinct` read at the symbolic cell `B + 1`. -/
theorem hg_varDistinct (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (B na : Nat)
      (dv : Int) (env : LocalEnv) (k : Cont) (ch : Choices),
      LocalEnv.lookup env "distinct" = some (.base ⟨B + 1⟩) → 25 ≤ B + 1 →
      Heap.lookup dead (.base ⟨B + 1⟩) = some (u64cell dv) →
    stepFn (σH σ L sv qv siv civ ws lp kvs iv false dead na)
        (.evalE (.var "distinct") env k) ch
      = .ok (.retV (.int dv .uint64) k,
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  intro kvs iv dead B na dv env k ch henv hB hlk
  refine stepFn_var (c := u64cell dv) henv ?_
  show Heap.lookup (frontH L sv qv siv civ ws lp kvs iv false ++ dead)
    (.base ⟨B + 1⟩) = some (u64cell dv)
  rw [lookup_append_right
    (lookup_frontH_none L sv qv siv civ ws lp kvs iv false hB)]
  exact hlk

/-- Range R2: the read value → the `distinct` store point. 4 steps. -/
theorem hg_R2_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (st pr : Array GoValue)
    (iv : Int) (dead : Heap)
    (B na : Nat) (dv : Int) (ch : Choices) :
    stepFnIter 4 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.retV (.int dv .uint64) (rngAddK B st pr)) ch
      = .ok (.next (.storeK [rngRef B]
            [.int (IntKind.normalize .uint64 (dv + 1)) .uint64] (.seqn #[])
            (envIt2 B) (rngStoreK B st pr)),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  with_unfolding_all rfl

/-- Range R3: the store drains → the next `mapIterK`. 3 steps. -/
theorem hg_R3_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (st pr : Array GoValue)
    (iv : Int) (dead : Heap)
    (B na : Nat) (ch : Choices) :
    stepFnIter 3 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.next (.storeK [] [] (.seqn #[]) (envIt2 B) (rngStoreK B st pr))) ch
      = .ok (.next (iterKH B st pr),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead na)
    (body := .seqn #[]) (env := envIt2 B) (k := .seq [] (envIt2 B)
      (iterKH B st pr)) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead na) (ss := #[])
    (env := envIt2 B) (rest := []) (k := iterKH B st pr) (ch := ch))
  have h3 : stepFnIter 1 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.next (.seq ((#[] : Array Stmt).toList ++ []) (envIt2 B)
        (iterKH B st pr))) ch
      = .ok (.next (iterKH B st pr),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-! ## The setup loop's induction (the P5 schema) -/

/-- One setup iteration from the exit test's true delivery at `i`. 57
steps. -/
theorem su_iterH (σ : ExecState) (n seed q i : Nat) (hn : n < 2 ^ 63)
    (hi : i < n) (ch : Choices) :
    stepFnIter 57
      (hSt σ (hHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) ((q : Nat) : Int)
        n (histFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false) 11)
      (.retV (.bool true) suCmpKH) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) suCmpKH,
          hSt σ (hHeapSu ((n : Nat) : Int) ((seed : Nat) : Int)
            ((q : Nat) : Int) n
            (histFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
            ((i + 1 : Nat) : Int) false) 11, ch) := by
  have hB1a := su_B1a_rawH σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((q : Nat) : Int) n (histFamily i seed ++ List.replicate (n - i) 0)
    ((i : Nat) : Int) ch
  have hmod := stepFnIter_one (stepFn_strict_apply
    (done := [.int ((i : Nat) : Int) .uint64]) (env := suEnvH2)
    (k := suAddKH n ((seed : Nat) : Int) ((i : Nat) : Int)) (ch := ch)
    (applyStrictOp_mod_u64
      (σ := hSt σ (hHeapSu ((n : Nat) : Int) ((seed : Nat) : Int)
        ((q : Nat) : Int) n
        (histFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false) 11)
      (a := i) (b := 3) (by omega) (by omega)))
  have h1 := stepFnIter_chain hB1a hmod
  have hB1b := su_B1b_rawH σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((q : Nat) : Int) n (histFamily i seed ++ List.replicate (n - i) 0)
    ((i : Nat) : Int) ((i % 3 : Nat) : Int) ch
  rw [unorm_add_nat seed (i % 3)] at hB1b
  have h2 := stepFnIter_chain h1 hB1b
  have hw : (0 : Int) ≤ (((seed + i % 3) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + i % 3) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + i % 3) (y := 2 ^ 64) (by omega)
    omega
  have hst := storeTarget_slice_u64
    (σ := hSt σ (hHeapSu ((n : Nat) : Int) ((seed : Nat) : Int)
      ((q : Nat) : Int) n (histFamily i seed ++ List.replicate (n - i) 0)
      ((i : Nat) : Int) false) 11)
    (a := ⟨7⟩) (off := 0) (len := n) (cap := n) (i := i) (n := n)
    (ik := .uint64) (l := histFamily i seed ++ List.replicate (n - i) 0)
    (w := (((seed + i % 3) % 2 ^ 64 : Nat) : Int))
    (lookup_suH σ ((n : Nat) : Int) ((seed : Nat) : Int) ((q : Nat) : Int) n
      (histFamily i seed ++ List.replicate (n - i) 0) ((i : Nat) : Int)
      false 11)
    (Nat.le_refl n) hi
    (by rw [List.length_append, histFamily_length, List.length_replicate]
        omega)
    (by rw [List.length_append, histFamily_length, List.length_replicate]
        omega)
    histFamilyZ_range hw
  rw [Nat.zero_add, histFamily_set hi] at hst
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hst))
  have hD := su_D_rawH σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((q : Nat) : Int) n
    (histFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
    ((i : Nat) : Int) ch
  have h4 := stepFnIter_chain h3 hD
  have hA1 := su_A1_rawH σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((q : Nat) : Int) n
    (histFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
    ((i : Nat) : Int) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  exact stepFnIter_chain h4 hA1

/-- **The setup loop**, by the P5 iteration schema: exactly `57·(n−i)`
steps materialize the wrapped `seed + i%3` family. -/
theorem su_loopH (σ : ExecState) (n seed q : Nat) (hn : n < 2 ^ 63) :
    ∀ μ i, μ = n - i → i ≤ n → ∀ ch : Choices,
    stepFnIter (57 * (n - i))
      (hSt σ (hHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) ((q : Nat) : Int)
        n (histFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false) 11)
      (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
        suCmpKH) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) suCmpKH,
          hSt σ (hHeapSu ((n : Nat) : Int) ((seed : Nat) : Int)
            ((q : Nat) : Int) n (histFamily n seed) ((n : Nat) : Int)
            false) 11, ch) := by
  intro _ i _ hin ch
  have hgen := stepFnIter_iterate (c := 57) (n := n)
    (T := fun j => hSt σ (hHeapSu ((n : Nat) : Int) ((seed : Nat) : Int)
      ((q : Nat) : Int) n
      (histFamily j seed ++ List.replicate (n - j) 0)
      ((j : Nat) : Int) false) 11)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int)
      < ((n : Nat) : Int)))) suCmpKH)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact su_iterH σ n seed q j hn hj ch')
    i hin ch
  simpa using hgen

/-! ## The copy loop's induction, then the call -/

theorem cp_iterH (σ : ExecState) (n seed q : Nat) (siv : Int) (m : Nat)
    (hn : n < 2 ^ 63) (hcap : n ≤ 8) (hm : m < n) (ch : Choices) :
    stepFnIter 53
      (hSt σ (hHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) ((q : Nat) : Int)
        n (histFamily n seed) (histPre m seed) siv ((m : Nat) : Int) false) 14)
      (.retV (.bool true) cpCmpKH) ch
      = .ok (.retV (.bool (decide
            (((m + 1 : Nat) : Int) < ((n : Nat) : Int)))) cpCmpKH,
          hSt σ (hHeapCp ((n : Nat) : Int) ((seed : Nat) : Int)
            ((q : Nat) : Int) n (histFamily n seed) (histPre (m + 1) seed) siv
            ((m + 1 : Nat) : Int) false) 14, ch) := by
  have hlenF : (histFamily n seed).length = n := histFamily_length n seed
  have hB1 := cp_B1_rawH σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((q : Nat) : Int) n (histFamily n seed) (histPre m seed) siv
    ((m : Nat) : Int) ch
  have hget : (⟨(histFamily n seed).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + m]?
      = some (.int (((seed + m % 3) % 2 ^ 64 : Nat) : Int) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega), histFamily_getD hm]
  have hread := stepFn_strict_apply (done := [hSliceV n]) (env := cpEnvH2)
    (k := cpRhsKH ((m : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .uint64)
      (lookup_cpV_H σ ((n : Nat) : Int) ((seed : Nat) : Int) ((q : Nat) : Int)
        n (histFamily n seed) (histPre m seed) siv ((m : Nat) : Int) false 14)
      (Nat.le_refl n) hm hget)
  have hB2 := cp_B2_rawH σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((q : Nat) : Int) n (histFamily n seed) (histPre m seed) siv
    ((m : Nat) : Int)
    (.int (((seed + m % 3) % 2 ^ 64 : Nat) : Int) .uint64) ch
  have hw : (0 : Int) ≤ (((seed + m % 3) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + m % 3) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + m % 3) (y := 2 ^ 64) (by omega)
    omega
  have hst := storeTarget_arrayLocal_u64 (a := ⟨11⟩) (N := 8) (i := m)
    (ik := .uint64) (l := histPre m seed)
    (w := (((seed + m % 3) % 2 ^ 64 : Nat) : Int))
    (lookup_cpVals_H σ ((n : Nat) : Int) ((seed : Nat) : Int)
      ((q : Nat) : Int) n (histFamily n seed) (histPre m seed) siv
      ((m : Nat) : Int) false 14)
    (by rw [histPre_length (by omega)]; omega)
    (histPre_length (by omega)) histPre_range hw
  rw [histPre_set (by omega : m < 8)] at hst
  have hstore : storeTarget
      (hSt σ (hHeapCp ((n : Nat) : Int) ((seed : Nat) : Int)
        ((q : Nat) : Int) n (histFamily n seed) (histPre m seed) siv
        ((m : Nat) : Int) false) 14)
      (cpRefH ((m : Nat) : Int))
      (.int (((seed + m % 3) % 2 ^ 64 : Nat) : Int) .uint64)
      = .ok (hSt σ (hHeapCp ((n : Nat) : Int) ((seed : Nat) : Int)
          ((q : Nat) : Int) n (histFamily n seed) (histPre (m + 1) seed) siv
          ((m : Nat) : Int) false) 14) := hst
  have hD := cp_D_rawH σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((q : Nat) : Int) n (histFamily n seed) (histPre (m + 1) seed) siv
    ((m : Nat) : Int) ch
  have hA1 := cp_A1_rawH σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((q : Nat) : Int) n (histFamily n seed) (histPre (m + 1) seed) siv
    ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  have h1 := stepFnIter_chain hB1 (stepFnIter_one hread)
  have h2 := stepFnIter_chain h1 hB2
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hstore))
  exact stepFnIter_chain (stepFnIter_chain h3 hD) hA1

/-- **The copy loop + the call**: from the exit-test delivery at `m`,
the run reaches the subject's counting-loop head within `53·μ + 69`
steps — the copy exit (17), the ONE program-consulting `enterFrame`
step, and `histogram`'s prologue (51). -/
theorem cp_loopH (σ : ExecState) (n seed q : Nat) (hn : n < 2 ^ 63)
    (hcap : n ≤ 8)
    (henter : ∀ (l lp : List Int) (siv civ : Int),
      enterFrame (hSt σ (hHeapCall ((n : Nat) : Int) ((seed : Nat) : Int)
          ((q : Nat) : Int) n l lp siv civ) 16) ⟨"histogram"⟩
          [hSliceV n, .int ((q : Nat) : Int) .uint64]
        = .ok (histogramFunc, hFrameEnv, [.base ⟨18⟩, .base ⟨19⟩],
            hSt σ (hHeapHFrame ((n : Nat) : Int) ((seed : Nat) : Int)
              ((q : Nat) : Int) n l lp siv civ) 20)) :
    ∀ μ m : Nat, m + μ = n → ∀ ch : Choices,
    ∃ k : Nat, k ≤ 53 * μ + 69 ∧
      stepFnIter k
        (hSt σ (hHeapCp ((n : Nat) : Int) ((seed : Nat) : Int)
          ((q : Nat) : Int) n (histFamily n seed) (histPre m seed)
          ((n : Nat) : Int) ((m : Nat) : Int) false) 14)
        (.retV (.bool (decide (((m : Nat) : Int) < ((n : Nat) : Int))))
          cpCmpKH) ch
        = .ok (headCH,
            σH σ n ((seed : Nat) : Int) ((q : Nat) : Int) ((n : Nat) : Int)
              ((n : Nat) : Int) (histFamily n seed) (histPre n seed) [] 0 true
              [] 25, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hm ch
    rcases Nat.lt_or_ge m n with hlt | hge
    · rw [show (decide (((m : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      obtain ⟨k, hk, hrun⟩ := ih (μ - 1) (by omega) (m + 1) (by omega) ch
      exact ⟨53 + k, by omega,
        stepFnIter_chain
          (cp_iterH σ n seed q ((n : Nat) : Int) m hn hcap hlt ch) hrun⟩
    · have hmn : m = n := by omega
      subst hmn
      rw [show (decide (((m : Nat) : Int) < ((m : Nat) : Int))) = false from
        decide_eq_false (by omega)]
      have hX := cp_X_rawH σ ((m : Nat) : Int) ((seed : Nat) : Int)
        ((q : Nat) : Int) m (histFamily m seed) (histPre m seed)
        ((m : Nat) : Int) ((m : Nat) : Int) ch
      have hent := stepFnIter_one (ch := ch)
        (stepFn_call_enter (plans := hCallPlans)
          (env := callEnvH) (k := hAfterCall) (vals := [hSliceV m])
          (v := .int ((q : Nat) : Int) .uint64)
          (henter (histFamily m seed) (histPre m seed) ((m : Nat) : Int)
            ((m : Nat) : Int)))
      have hpro := h_prologue_rawH σ ((seed : Nat) : Int) ((q : Nat) : Int) m
        (histFamily m seed) (histPre m seed) ((m : Nat) : Int)
        ((m : Nat) : Int) ch
      exact ⟨17 + 1 + 51, by omega,
        stepFnIter_chain (stepFnIter_chain hX hent) hpro⟩

/-! ## The range loop (GAP-R1) -/

-- (`lookup_set_self`, formerly a private copy here, is StepKit's
-- since WP arc s2 item 1.)

/-- The pick-coherence relation of this placement's walk (BUG-005
(L)): the produced set is the wrapped `done` keys, the remaining
candidates are the cell's entries minus them. -/
def hgPC (kvs : List (Int × Nat)) (pr : Array GoValue)
    (rem : List (Int × Nat)) : Prop :=
  ∃ done : List Int, pr = toKeys done
    ∧ rem = kvs.filter (fun p => !done.contains p.1)

/-- The choice-pick at this placement: one choice consumed, the picked
key joins the produced set, NO cell allocated. The candidates and the
mandatory bit are computed against the map cell at base 21 (the lookup
is definitional in `σH`), given the entries' normalization and the
coherence relation. -/
theorem hg_pick (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs rem : List (Int × Nat)) (pr : Array GoValue) (idx : Nat)
      (ch ch₂ : Choices)
      (iv : Int) (dead : Heap) (B na : Nat)
      (_hkv : ∀ p ∈ kvs, IntKind.normalize .uint64 p.1 = p.1
        ∧ IntKind.normalize .uint64 ((p.2 : Nat) : Int)
            = ((p.2 : Nat) : Int))
      (_hPC : hgPC kvs pr rem)
      (_hcons : Choices.consume ch rem.length = (idx, ch₂))
      (hidx : idx < rem.length),
    stepFn (σH σ L sv qv siv civ ws lp kvs iv false dead na)
        (.next (iterKH B (toKeys (kvs.map (·.1))) pr)) ch
      = .ok (.exec hRangeBody (envIt1 B)
            (iterKH B (toKeys (kvs.map (·.1)))
              (pr.push (.int (rem[idx]'hidx).1 .uint64))),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch₂) := by
  intro kvs rem pr idx ch ch₂ iv dead B na hkv hPC hcons hidx
  obtain ⟨done, rfl, hrem⟩ := hPC
  have hcands : mapIterCandidates
      (σH σ L sv qv siv civ ws lp kvs iv false dead na) tU64 tU64
      (some (.base ⟨21⟩)) (toKeys done) = .ok (toEntries rem) := by
    rw [hrem]
    exact candidates_toEntries (a := ⟨21⟩) (dty := none) rfl hkv
  have hrem_sub : ∀ p ∈ rem, (kvs.map (·.1)).contains p.1 := by
    intro p hp
    rw [hrem] at hp
    have := (List.mem_filter.mp hp).1
    exact List.contains_iff_exists_mem_beq.mpr
      ⟨p.1, List.mem_map.mpr ⟨p, this, rfl⟩, by simp⟩
  have hne : rem ≠ [] := by
    intro hc
    rw [hc] at hidx
    exact absurd hidx (by simp)
  have hmand : mapIterMandatoryRemains
      (σH σ L sv qv siv civ ws lp kvs iv false dead na) tU64
      (toEntries rem) (toKeys (kvs.map (·.1))) = .ok true :=
    mandatory_true_of_all _ hne hrem_sub
  have hcons' : Choices.consume ch
      (rem.length + (if true then 0 else 1)) = (idx, ch₂) := by
    simpa using hcons
  exact stepFn_pick_novars (body := hRangeBody) (env := envRBDH B)
    (k := kRH B) hcands hmand hcons' hidx

/-- **One range iteration, GIVEN the pick**: 16 steps, one entry gone,
`distinct` up by one — and the state is otherwise IDENTICAL (GAP-R1
closure, 2026-08-15: the pick destructuring and the induction moved to
the kit's `mapPickLoop_generic`; this placement supplies only the
iteration). -/
theorem hg_range_iter (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs rem : List (Int × Nat)) (pr : Array GoValue) (idx : Nat)
      (ch ch₂ : Choices)
      (iv : Int) (dead : Heap) (B na : Nat) (dv : Nat)
      (_hkv : ∀ p ∈ kvs, IntKind.normalize .uint64 p.1 = p.1
        ∧ IntKind.normalize .uint64 ((p.2 : Nat) : Int)
            = ((p.2 : Nat) : Int))
      (_hPC : hgPC kvs pr rem)
      (_hcons : Choices.consume ch rem.length = (idx, ch₂))
      (hidx : idx < rem.length)
      (_hB : 25 ≤ B + 1) (_hdv : dv + 1 < 2 ^ 64)
      (_hlk : Heap.lookup dead (.base ⟨B + 1⟩)
        = some (u64cell ((dv : Nat) : Int))),
      stepFnIter 16 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
          (.next (iterKH B (toKeys (kvs.map (·.1))) pr)) ch
        = .ok (.next (iterKH B (toKeys (kvs.map (·.1)))
              (pr.push (.int (rem[idx]'hidx).1 .uint64))),
            σH σ L sv qv siv civ ws lp kvs iv false
              (Heap.set dead (.base ⟨B + 1⟩)
                (u64cell ((dv + 1 : Nat) : Int))) na, ch₂) := by
  intro kvs rem pr idx ch ch₂ iv dead B na dv hkv hPC hcons hidx hB hdv hlk
  have hp := stepFnIter_one
    (hg_pick σ L sv qv siv civ ws lp kvs rem pr idx ch ch₂ iv dead B na
      hkv hPC hcons hidx)
  have hR1 := hg_R1_raw σ L sv qv siv civ ws lp kvs
    (toKeys (kvs.map (·.1))) (pr.push (.int (rem[idx]'hidx).1 .uint64)) iv
    dead B na ch₂
  have hvar := stepFnIter_one
    (hg_varDistinct σ L sv qv siv civ ws lp kvs iv dead B na
      ((dv : Nat) : Int) (envIt2 B)
      (rngAddK B (toKeys (kvs.map (·.1)))
        (pr.push (.int (rem[idx]'hidx).1 .uint64))) ch₂
      rfl hB hlk)
  have hR2 := hg_R2_raw σ L sv qv siv civ ws lp kvs
    (toKeys (kvs.map (·.1))) (pr.push (.int (rem[idx]'hidx).1 .uint64)) iv
    dead B na ((dv : Nat) : Int) ch₂
  rw [show ((dv : Nat) : Int) + 1 = ((dv + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((dv + 1 : Nat) : Int)) (by omega)
      (by omega)] at hR2
  have hst := stepFnIter_one
    (hg_stDistinct σ L sv qv siv civ ws lp kvs iv dead B na
      ((dv : Nat) : Int) ((dv + 1 : Nat) : Int)
      (rngStoreK B (toKeys (kvs.map (·.1)))
        (pr.push (.int (rem[idx]'hidx).1 .uint64))) ch₂ hB hlk
      (unorm_of_range (v := ((dv + 1 : Nat) : Int)) (by omega) (by omega))
      [] [] (.seqn #[]) (envIt2 B))
  have hR3 := hg_R3_raw σ L sv qv siv civ ws lp kvs
    (toKeys (kvs.map (·.1))) (pr.push (.int (rem[idx]'hidx).1 .uint64)) iv
    (Heap.set dead (.base ⟨B + 1⟩) (u64cell ((dv + 1 : Nat) : Int))) B na ch₂
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain hp hR1) hvar) hR2) hst) hR3

/-- **The range loop, at EVERY choice stream**: within `16·m + 1`
steps `distinct` ends at `dv + m`, where `m` is the number of map
entries — the pick never enters the answer. The kit's
`mapPickLoop_generic` at this placement's iteration, with the
conservation invariant "`distinct` + remaining entries = `dv + m`"
(GAP-R1 closure, 2026-08-15; the step count became the schema's
`∃ k ≤ 16·m + 1` — the run assembly's fuel arithmetic carries the
bound). -/
theorem hg_range_loop (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int)
    (hkv : ∀ p ∈ kvs, IntKind.normalize .uint64 p.1 = p.1
      ∧ IntKind.normalize .uint64 ((p.2 : Nat) : Int)
          = ((p.2 : Nat) : Int))
    (hnodup : (kvs.map (·.1)).Nodup) :
    ∀ (m : Nat) (rem : List (Int × Nat)), rem.length = m →
    ∀ (pr : Array GoValue) (dv : Nat) (dead : Heap) (B na : Nat)
      (ch : Choices),
      hgPC kvs pr rem →
      25 ≤ B + 1 → B + 1 < na → dv + m < 2 ^ 64 →
      Heap.lookup dead (.base ⟨B + 1⟩) = some (u64cell ((dv : Nat) : Int)) →
      DeadFrom dead na →
    ∃ (k : Nat) (ch' : Choices) (tail : Heap),
      k ≤ 16 * m + 1
      ∧ Heap.lookup tail (.base ⟨B + 1⟩)
          = some (u64cell ((dv + m : Nat) : Int))
      ∧ Heap.lookup tail (.base ⟨B⟩) = Heap.lookup dead (.base ⟨B⟩)
      ∧ DeadFrom tail na
      ∧ stepFnIter k
          (σH σ L sv qv siv civ ws lp kvs iv false dead na)
          (.next (iterKH B (toKeys (kvs.map (·.1))) pr))
          ch
        = .ok (.next (kRH B),
            σH σ L sv qv siv civ ws lp kvs iv false tail na, ch') := by
  intro m rem hm pr dv dead B na ch hPC hB hBna hdv hlk hdead
  subst hm
  obtain ⟨k, d', ch', hk, hP, hrun⟩ :=
    mapPickLoop_generic
      (T := fun d : Heap × Array GoValue =>
        σH σ L sv qv siv civ ws lp kvs iv false d.1 na)
      (cfg := fun d _ => .next (iterKH B (toKeys (kvs.map (·.1))) d.2))
      (exitCfg := .next (kRH B))
      (P := fun d r =>
        r.length ≤ rem.length
        ∧ hgPC kvs d.2 r
        ∧ Heap.lookup d.1 (.base ⟨B + 1⟩)
            = some (u64cell ((dv + (rem.length - r.length) : Nat) : Int))
        ∧ Heap.lookup d.1 (.base ⟨B⟩) = Heap.lookup dead (.base ⟨B⟩)
        ∧ DeadFrom d.1 na)
      (c := 16) (e := 1)
      (fun d r idx p ch₀ ch₂ hcons hidx hp hP => by
        obtain ⟨hlen, hPCd, hlk', hlkB, hdead'⟩ := hP
        have hlpos : 0 < r.length := by omega
        have hiter := hg_range_iter σ L sv qv siv civ ws lp kvs r d.2 idx
          ch₀ ch₂ iv d.1 B na (dv + (rem.length - r.length)) hkv hPCd
          hcons hidx hB (by omega) hlk'
        have hne : ∀ x : Nat, x ≠ B + 1 →
            Heap.lookup (Heap.set d.1 (.base ⟨B + 1⟩)
                (u64cell ((dv + (rem.length - r.length) + 1 : Nat) : Int)))
              (.base ⟨x⟩)
              = Heap.lookup d.1 (.base ⟨x⟩) := by
          intro x hx
          refine Machine.Heap.lookup_set_ne ?_
          intro hc
          exact hx (by
            have h := congrArg Loc.rootBase hc
            simp only [Loc.rootBase] at h
            omega)
        have hkey : (r[idx]'hidx) = p := by
          have hg := List.getElem?_eq_getElem hidx
          rw [hp] at hg
          exact (Option.some.inj hg).symm
        rw [hkey] at hiter
        have hPC' : hgPC kvs (d.2.push (.int p.1 .uint64))
            (r.eraseIdx idx) := by
          obtain ⟨done, hdone, hrem'⟩ := hPCd
          refine ⟨done ++ [p.1], ?_, ?_⟩
          · rw [hdone]
            simp [toKeys, List.map_append]
          · rw [hrem']
            refine (filter_push_key hnodup ?_).symm
            rw [← hrem']
            exact hp
        refine ⟨16, (Heap.set d.1 (.base ⟨B + 1⟩)
            (u64cell ((dv + (rem.length - r.length) + 1 : Nat) : Int)),
            d.2.push (.int p.1 .uint64)),
          Nat.le_refl _,
          ⟨by rw [eraseIdx_length_of_lt hidx]; omega, hPC', ?_, ?_, ?_⟩,
          hiter⟩
        · rw [lookup_set_self]
          congr 3
          rw [eraseIdx_length_of_lt hidx]
          omega
        · rw [hne B (by omega)]
          exact hlkB
        · intro x hx
          rw [hne x (by omega)]
          exact hdead' x hx)
      (fun d ch₀ hP => by
        obtain ⟨-, hPCd, -, -, -⟩ := hP
        obtain ⟨done, hdone, hnilf⟩ := hPCd
        have hcands : mapIterCandidates
            (σH σ L sv qv siv civ ws lp kvs iv false d.1 na) tU64 tU64
            (some (.base ⟨21⟩)) d.2 = .ok #[] := by
          rw [hdone]
          have := candidates_toEntries (σ :=
              σH σ L sv qv siv civ ws lp kvs iv false d.1 na)
            (a := ⟨21⟩) (dty := none) (kvs := kvs) (ks := done) rfl hkv
          rw [← hnilf] at this
          simpa [toEntries] using this
        exact stepFnIter_one (stepFn_iter_done hcands))
      rem.length rem rfl (dead, pr) ch
      ⟨Nat.le_refl _, hPC, by simpa using hlk, rfl, hdead⟩
  obtain ⟨-, -, hlk', hlkB, hdead'⟩ := hP
  refine ⟨k, ch', d'.1, hk, ?_, hlkB, hdead', hrun⟩
  simpa using hlk'

/-! ## Normalization of the map's entries (the snapshot's side
condition) -/

theorem countsFold_norm (ws : List Int) (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64)
    (hlen : ws.length < 2 ^ 64) :
    ∀ p ∈ countsFold ws, IntKind.normalize .uint64 p.1 = p.1
      ∧ IntKind.normalize .uint64 ((p.2 : Nat) : Int)
          = ((p.2 : Nat) : Int) := by
  intro p hp
  refine ⟨?_, ?_⟩
  · have h := countsFold_key_mem hp
    exact unorm_of_range (hws p.1 h).1 (hws p.1 h).2
  · have := countsFold_val_le ws hp
    exact unorm_nat_of_lt (by omega)

/-! ## The exit phase -/

def hEpiTail : Cont :=
  .seq [.assign (.var "$res1") (.var "hits"),
        .assign (.var "$res2") (.var "distinct"), .returnStmt] callEnvH
    (.frame [] [] [] [] .stop)
def hRes0Ref : TargetRef := .chain (.addr (.base ⟨3⟩)) [] []

/-- X1: range-loop exit → the `hits` read of the subject's
`$res0 := hits`. 6 steps. -/
theorem hg_X1_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp r3 : List Int) (kvs : List (Int × Nat))
    (r4 r5 r14 r15 r18 r19 : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 6
      (σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na)
      (.next (kRH B)) ch
      = .ok (.evalE (.var "hits") (envRBDH B)
            (.rhsK .vals [.chain (.addr (.base ⟨18⟩)) [] []] [] []
              (.seqn #[]) (envRBDH B)
              (.seq [.assign (.var "$res1") (.var "distinct"), .returnStmt]
                (envRBDH B) frameKH)),
          σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na,
          ch) := by
  have h1 := stepFnIter_one (stepFn_seq_pop
    (σ := σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na)
    (t := hRetSeqn) (rest := []) (env := envRBDH B) (k := frameKH) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na)
    (ss := #[.assign (.var "$res0") (.var "hits"),
      .assign (.var "$res1") (.var "distinct"), .returnStmt])
    (env := envRBDH B) (rest := []) (k := frameKH) (ch := ch))
  have h3 : stepFnIter 4
      (σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na)
      (.next (.seq ((#[.assign (.var "$res0") (.var "hits"),
        .assign (.var "$res1") (.var "distinct"),
        .returnStmt] : Array Stmt).toList ++ []) (envRBDH B) frameKH)) ch
      = .ok (.evalE (.var "hits") (envRBDH B)
            (.rhsK .vals [.chain (.addr (.base ⟨18⟩)) [] []] [] []
              (.seqn #[]) (envRBDH B)
              (.seq [.assign (.var "$res1") (.var "distinct"), .returnStmt]
                (envRBDH B) frameKH)),
          σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na,
          ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- The `hits` read at the symbolic cell `B` in the tail. -/
theorem hg_varHits (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp r3 : List Int) (kvs : List (Int × Nat))
    (r4 r5 r14 r15 r18 r19 : Int) (tail : Heap) (B na : Nat) (hv : Int)
    (env : LocalEnv) (k : Cont) (ch : Choices)
    (henv : LocalEnv.lookup env "hits" = some (.base ⟨B⟩)) (hB : 25 ≤ B)
    (hlk : Heap.lookup tail (.base ⟨B⟩) = some (u64cell hv)) :
    stepFn
      (σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na)
      (.evalE (.var "hits") env k) ch
      = .ok (.retV (.int hv .uint64) k,
          σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na,
          ch) := by
  refine stepFn_var (c := u64cell hv) henv ?_
  show Heap.lookup
    (frontXH L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 ++ tail)
    (.base ⟨B⟩) = some (u64cell hv)
  rw [lookup_append_right
    (lookup_frontXH_none L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19
      hB)]
  exact hlk

/-- The `distinct` read at the symbolic cell `B + 1` in the tail. -/
theorem hg_varDistinctX (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp r3 : List Int) (kvs : List (Int × Nat))
    (r4 r5 r14 r15 r18 r19 : Int) (tail : Heap) (B na : Nat) (dv : Int)
    (env : LocalEnv) (k : Cont) (ch : Choices)
    (henv : LocalEnv.lookup env "distinct" = some (.base ⟨B + 1⟩))
    (hB : 25 ≤ B + 1)
    (hlk : Heap.lookup tail (.base ⟨B + 1⟩) = some (u64cell dv)) :
    stepFn
      (σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na)
      (.evalE (.var "distinct") env k) ch
      = .ok (.retV (.int dv .uint64) k,
          σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na,
          ch) := by
  refine stepFn_var (c := u64cell dv) henv ?_
  show Heap.lookup
    (frontXH L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 ++ tail)
    (.base ⟨B + 1⟩) = some (u64cell dv)
  rw [lookup_append_right
    (lookup_frontXH_none L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19
      hB)]
  exact hlk

/-- X2a: the `hits` value stored into the subject's `$res0` (cell 18).
2 steps. -/
theorem hg_X2a_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp r3 : List Int) (kvs : List (Int × Nat))
    (r4 r5 r14 r15 r18 r19 hv : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 2
      (σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na)
      (.retV (.int hv .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨18⟩)) [] []] [] [] (.seqn #[])
          (envRBDH B)
          (.seq [.assign (.var "$res1") (.var "distinct"), .returnStmt]
            (envRBDH B) frameKH))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envRBDH B)
            (.seq [.assign (.var "$res1") (.var "distinct"), .returnStmt]
              (envRBDH B) frameKH)),
          σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15
            (IntKind.normalize .uint64 hv) r19 tail na, ch) := by
  with_unfolding_all rfl

/-- X2b: the store drains → the `distinct` read of
`$res1 := distinct`. 6 steps. -/
theorem hg_X2b_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp r3 : List Int) (kvs : List (Int × Nat))
    (r4 r5 r14 r15 r18 r19 : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 6
      (σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na)
      (.next (.storeK [] [] (.seqn #[]) (envRBDH B)
        (.seq [.assign (.var "$res1") (.var "distinct"), .returnStmt]
          (envRBDH B) frameKH))) ch
      = .ok (.evalE (.var "distinct") (envRBDH B)
            (.rhsK .vals [.chain (.addr (.base ⟨19⟩)) [] []] [] []
              (.seqn #[]) (envRBDH B)
              (.seq [.returnStmt] (envRBDH B) frameKH)),
          σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na,
          ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na)
    (body := .seqn #[]) (env := envRBDH B)
    (k := .seq [.assign (.var "$res1") (.var "distinct"), .returnStmt]
      (envRBDH B) frameKH) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na)
    (ss := #[]) (env := envRBDH B)
    (rest := [.assign (.var "$res1") (.var "distinct"), .returnStmt])
    (k := frameKH) (ch := ch))
  have h3 : stepFnIter 4
      (σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na)
      (.next (.seq ((#[] : Array Stmt).toList
        ++ [.assign (.var "$res1") (.var "distinct"), .returnStmt])
        (envRBDH B) frameKH)) ch
      = .ok (.evalE (.var "distinct") (envRBDH B)
            (.rhsK .vals [.chain (.addr (.base ⟨19⟩)) [] []] [] []
              (.seqn #[]) (envRBDH B)
              (.seq [.returnStmt] (envRBDH B) frameKH)),
          σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na,
          ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- X3: the `distinct` value stored into the subject's `$res1`, the
subject returns, both results write back to the harness's
`hits`/`distinct`, and the harness epilogue reaches the
`$res0 = vals` ARRAY store POINT. 24 steps; the store itself cannot
reduce definitionally (the array's contents are symbolic), which is
why it is split out. -/
theorem hg_X3a_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp r3 : List Int) (kvs : List (Int × Nat))
    (r4 r5 r14 r15 r18 r19 dv : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 2
      (σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na)
      (.retV (.int dv .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨19⟩)) [] []] [] [] (.seqn #[])
          (envRBDH B) (.seq [.returnStmt] (envRBDH B) frameKH))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envRBDH B)
            (.seq [.returnStmt] (envRBDH B) frameKH)),
          σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18
            (IntKind.normalize .uint64 dv) tail na, ch) := by
  with_unfolding_all rfl

theorem hg_X3b_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp r3 : List Int) (kvs : List (Int × Nat))
    (r4 r5 r14 r15 r18 r19 : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 22
      (σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na)
      (.next (.storeK [] [] (.seqn #[]) (envRBDH B)
        (.seq [.returnStmt] (envRBDH B) frameKH))) ch
      = .ok (.next (.storeK [hRes0Ref]
            [.array ⟨lp.map (fun v => .int v .uint64)⟩] (.seqn #[])
            callEnvH hEpiTail),
          σXH σ L sv qv siv civ ws lp r3 kvs r4 r5
            (IntKind.normalize .uint64 r18) (IntKind.normalize .uint64 r19)
            r18 r19 tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na)
    (body := .seqn #[]) (env := envRBDH B)
    (k := .seq [.returnStmt] (envRBDH B) frameKH) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na)
    (ss := #[]) (env := envRBDH B) (rest := [.returnStmt]) (k := frameKH)
    (ch := ch))
  have h3 : stepFnIter 20
      (σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na)
      (.next (.seq ((#[] : Array Stmt).toList ++ [.returnStmt])
        (envRBDH B) frameKH)) ch
      = .ok (.next (.storeK [hRes0Ref]
            [.array ⟨lp.map (fun v => .int v .uint64)⟩] (.seqn #[])
            callEnvH hEpiTail),
          σXH σ L sv qv siv civ ws lp r3 kvs r4 r5
            (IntKind.normalize .uint64 r18) (IntKind.normalize .uint64 r19)
            r18 r19 tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- X4: the harness's `$res1`/`$res2` stores, the return, the harness
frame exit — the driver terminal. 24 steps. -/
theorem hg_X4_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp r3 : List Int) (kvs : List (Int × Nat))
    (r4 r5 r14 r15 r18 r19 : Int) (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 24
      (σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na)
      (.next (.storeK [] [] (.seqn #[]) callEnvH hEpiTail)) ch
      = .ok (.next .stop,
          σXH σ L sv qv siv civ ws lp r3 kvs
            (IntKind.normalize .uint64 r14) (IntKind.normalize .uint64 r15)
            r14 r15 r18 r19 tail na, ch) := by
  with_unfolding_all rfl

theorem lookup_res0_XH (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp r3 : List Int) (kvs : List (Int × Nat))
    (r4 r5 r14 r15 r18 r19 : Int) (tail : Heap) (na : Nat) :
    Heap.lookup
        (σXH σ L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 tail na).heap
        (.base ⟨3⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨r3.map (fun v => .int v .uint64)⟩⟩ := by
  simp [σXH, hSt, frontXH, Heap.lookup]

/-! ## The run, end to end -/

/-- The `enterFrame` discharge at the pinned program: the second and
last unfolding of `histogramLowered` in this example. -/
theorem h_enterFrame_fact (n seed q : Nat)
    (hq : IntKind.normalize .uint64 ((q : Nat) : Int) = ((q : Nat) : Int))
    (l lp : List Int) (siv civ : Int) :
    enterFrame (hSt hProg (hHeapCall ((n : Nat) : Int) ((seed : Nat) : Int)
        ((q : Nat) : Int) n l lp siv civ) 16) ⟨"histogram"⟩
        [hSliceV n, .int ((q : Nat) : Int) .uint64]
      = .ok (histogramFunc, hFrameEnv, [.base ⟨18⟩, .base ⟨19⟩],
          hSt hProg (hHeapHFrame ((n : Nat) : Int) ((seed : Nat) : Int)
            ((q : Nat) : Int) n l lp siv civ) 20) := by
  have e : enterFrame (hSt hProg (hHeapCall ((n : Nat) : Int)
        ((seed : Nat) : Int) ((q : Nat) : Int) n l lp siv civ) 16)
        ⟨"histogram"⟩ [hSliceV n, .int ((q : Nat) : Int) .uint64]
      = .ok (histogramFunc, hFrameEnv, [.base ⟨18⟩, .base ⟨19⟩],
          hSt hProg (hHeapCall ((n : Nat) : Int) ((seed : Nat) : Int)
            ((q : Nat) : Int) n l lp siv civ ++
            [(.base ⟨16⟩, hHandleV n),
             (.base ⟨17⟩,
               u64cell (IntKind.normalize .uint64 ((q : Nat) : Int))),
             (.base ⟨18⟩, u64cell 0), (.base ⟨19⟩, u64cell 0)]) 20) := by
    with_unfolding_all rfl
  rw [hq] at e
  exact e

/-- **The harness run, PROGRAM-generic**: within `210·n + 344` steps the
harness reaches the driver terminal with the counted values in `$res0`,
the queried key's number of occurrences in `$res1`, and the number of
distinct values in `$res2`. -/
theorem hg_runs_generic (σ : ExecState) (n seed q : Nat) (hcap : n ≤ 8)
    (hq : q < 2 ^ 64)
    (henter : ∀ (l lp : List Int) (siv civ : Int),
      enterFrame (hSt σ (hHeapCall ((n : Nat) : Int) ((seed : Nat) : Int)
          ((q : Nat) : Int) n l lp siv civ) 16) ⟨"histogram"⟩
          [hSliceV n, .int ((q : Nat) : Int) .uint64]
        = .ok (histogramFunc, hFrameEnv, [.base ⟨18⟩, .base ⟨19⟩],
            hSt σ (hHeapHFrame ((n : Nat) : Int) ((seed : Nat) : Int)
              ((q : Nat) : Int) n l lp siv civ) 20))
    (ch : Choices) :
    ∃ (k : Nat) (ch' : Choices) (tail : Heap) (na : Nat),
      k ≤ 210 * n + 344 ∧
      stepFnIter k
          (hSt σ (hHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)
            ((q : Nat) : Int)) 6) hHC0 ch
        = .ok (.next .stop,
            σXH σ n ((seed : Nat) : Int) ((q : Nat) : Int) ((n : Nat) : Int)
              ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
              (histPre n seed) (countsFold (histFamily n seed))
              ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
              ((distinctCount (histFamily n seed) : Nat) : Int)
              ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
              ((distinctCount (histFamily n seed) : Nat) : Int)
              ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
              ((distinctCount (histFamily n seed) : Nat) : Int)
              tail na, ch') := by
  have hn : n < 2 ^ 63 := by omega
  have hws := histFamily_range n seed
  have hLen : (histFamily n seed).length = n := histFamily_length n seed
  have hlen : (histFamily n seed).length < 2 ^ 63 := by omega
  have hqn : IntKind.normalize .uint64 ((q : Nat) : Int)
      = ((q : Nat) : Int) := unorm_nat_of_lt hq
  -- the two answers, and their uint64-domain facts
  have hOcc : occurrences ((q : Nat) : Int) (histFamily n seed) ≤ n := by
    simp only [occurrences]
    have h1 := List.length_filter_le (· = ((q : Nat) : Int))
      (histFamily n seed)
    omega
  have hDist : distinctCount (histFamily n seed) ≤ n := by
    have := distinctCount_le (histFamily n seed)
    omega
  have hcntq : cnt (countsFold (histFamily n seed)) ((q : Nat) : Int)
      = occurrences ((q : Nat) : Int) (histFamily n seed) :=
    cnt_countsList' (histFamily n seed) ((q : Nat) : Int)
  have hdlen : (countsFold (histFamily n seed)).length
      = distinctCount (histFamily n seed) :=
    countsList_length (histFamily n seed)
  have hHn : IntKind.normalize .uint64
      ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
      = ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int) :=
    unorm_nat_of_lt (by omega)
  have hDn : IntKind.normalize .uint64
      ((distinctCount (histFamily n seed) : Nat) : Int)
      = ((distinctCount (histFamily n seed) : Nat) : Int) :=
    unorm_nat_of_lt (by omega)
  -- ENTRY
  have hE1 := h_E1_raw σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((q : Nat) : Int) ch
  have hmk := stepFnIter_one
    (stepFn_makeSlice_u64_step (env := envC12H)
      (k := .seq [hS2, hS3, hS4, hS5, hS6, hS7] envC12H
        (.frame [] [] [] [] .stop))
      (h_make_apply σ ((n : Nat) : Int) ((seed : Nat) : Int)
        ((q : Nat) : Int) n ch))
  have hE2 := h_E2_raw σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((q : Nat) : Int) n ch
  have hA0 := su_A0_rawH σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((q : Nat) : Int) n (List.replicate n 0) 0 ch
  have hSU := su_loopH σ n seed q hn (n - 0) 0 rfl (by omega) ch
  have hS1 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hE1 hmk) hE2) hA0) hSU
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hS1
  have hX := su_X_rawH σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((q : Nat) : Int) n (histFamily n seed) ((n : Nat) : Int) ch
  have hS2' := stepFnIter_chain hS1 hX
  -- the copy loop and the call
  have hcA0 := cp_A0_rawH σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((q : Nat) : Int) n (histFamily n seed) zeros8 ((n : Nat) : Int) 0 ch
  obtain ⟨k₂, hk₂, hcp⟩ := cp_loopH σ n seed q hn hcap henter n 0 (by omega) ch
  rw [show histPre 0 seed = zeros8 from histPre_zero seed,
    show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hcp
  have hS3 := stepFnIter_chain (stepFnIter_chain hS2' hcA0) hcp
  -- the counting loop's entry test
  have hcnt0 := hg_segA0_raw σ n ((seed : Nat) : Int) ((q : Nat) : Int)
    ((n : Nat) : Int) ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
    [] 0 [] 25 ch
  have hlenap := stepFnIter_one
    (stepFn_strict_apply (done := []) (env := env2H)
      (k := .strictK .lessCmp [.int (0 : Int) .int] [] env2H cmpContCH)
      (ch := ch)
      (applyStrictOp_len_slice
        (σ := σH σ n ((seed : Nat) : Int) ((q : Nat) : Int) ((n : Nat) : Int)
          ((n : Nat) : Int) (histFamily n seed) (histPre n seed) [] 0 false []
          25)
        (b := .base ⟨7⟩) (off := 0) (len := n) (cap := n) (elem := tU64)
        (Nat.le_refl n)))
  have hCmp := hg_cmp_raw σ n ((seed : Nat) : Int) ((q : Nat) : Int)
    ((n : Nat) : Int) ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
    [] 0 0 [] 25 ch
  have hS4 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hS3 hcnt0)
    hlenap) hCmp
  -- THE COUNTING LOOP
  obtain ⟨k₃, tail₁, hk₃, htail₁, hrun₁⟩ :=
    hg_count_loop σ ((seed : Nat) : Int) ((q : Nat) : Int) ((n : Nat) : Int)
      ((n : Nat) : Int) (histFamily n seed) (histPre n seed) hws hlen
      ((histFamily n seed).length - 0) 0 rfl (by omega) [] 25 (by omega)
      (fun _ _ => rfl) ch
  rw [hLen] at hrun₁ htail₁ hk₃
  have hS5 := stepFnIter_chain hS4 hrun₁
  -- the query phase
  have hB25 : 25 ≤ 25 + 2 * n := by omega
  have hlkB : Heap.lookup (tail₁ ++ [(.base ⟨25 + 2 * n⟩, u64cell 0)])
      (.base ⟨25 + 2 * n⟩) = some (u64cell 0) := by
    rw [lookup_append_right (htail₁ (25 + 2 * n) (Nat.le_refl _))]
    exact lookup_singleton_self
  have hIH := stepFnIter_one
    (hg_initHits σ n ((seed : Nat) : Int) ((q : Nat) : Int) ((n : Nat) : Int)
      ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
      (countsFold (histFamily n seed)) ((n : Nat) : Int) tail₁ (25 + 2 * n) ch
      hB25 htail₁)
  have hS6 := stepFnIter_chain hS5 hIH
  have hqA := hg_qA_raw σ n ((seed : Nat) : Int) ((q : Nat) : Int)
    ((n : Nat) : Int) ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
    (countsFold (histFamily n seed)) ((n : Nat) : Int)
    (tail₁ ++ [(.base ⟨25 + 2 * n⟩, u64cell 0)]) (25 + 2 * n)
    (25 + 2 * n + 1) ch
  have hS7 := stepFnIter_chain hS6 hqA
  have hget := stepFnIter_one
    (hg_queryGet σ n ((seed : Nat) : Int) ((q : Nat) : Int) ((n : Nat) : Int)
      ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
      (countsFold (histFamily n seed)) ((n : Nat) : Int)
      (tail₁ ++ [(.base ⟨25 + 2 * n⟩, u64cell 0)]) (25 + 2 * n)
      (25 + 2 * n + 1) ch hqn)
  rw [hcntq] at hget
  have hS8 := stepFnIter_chain hS7 hget
  have hqB := hg_qB_raw σ n ((seed : Nat) : Int) ((q : Nat) : Int)
    ((n : Nat) : Int) ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
    (countsFold (histFamily n seed)) ((n : Nat) : Int)
    (tail₁ ++ [(.base ⟨25 + 2 * n⟩, u64cell 0)]) (25 + 2 * n)
    (25 + 2 * n + 1)
    ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int) ch
  have hS9 := stepFnIter_chain hS8 hqB
  have hstH := stepFnIter_one
    (hg_stHits σ n ((seed : Nat) : Int) ((q : Nat) : Int) ((n : Nat) : Int)
      ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
      (countsFold (histFamily n seed)) ((n : Nat) : Int)
      (tail₁ ++ [(.base ⟨25 + 2 * n⟩, u64cell 0)]) (25 + 2 * n)
      (25 + 2 * n + 1) 0
      ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int) ch
      hB25 hlkB hHn)
  rw [set_append_right (htail₁ (25 + 2 * n) (Nat.le_refl _)),
    set_singleton_self] at hstH
  have hS10 := stepFnIter_chain hS9 hstH
  have hqC := hg_qC_raw σ n ((seed : Nat) : Int) ((q : Nat) : Int)
    ((n : Nat) : Int) ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
    (countsFold (histFamily n seed)) ((n : Nat) : Int)
    (tail₁ ++ [(.base ⟨25 + 2 * n⟩,
      ⟨some tU64,
        .int ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
          .uint64⟩)]) (25 + 2 * n) (25 + 2 * n + 1) ch
  have hS11 := stepFnIter_chain hS10 hqC
  -- `distinct := 0` and the range head
  have hdead2 : DeadFrom (tail₁ ++ [(.base ⟨25 + 2 * n⟩,
      ⟨some tU64,
        .int ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
          .uint64⟩)]) (25 + 2 * n + 1) := htail₁.push
  have hID := stepFnIter_one
    (hg_initDistinct σ n ((seed : Nat) : Int) ((q : Nat) : Int)
      ((n : Nat) : Int) ((n : Nat) : Int) (histFamily n seed)
      (histPre n seed) (countsFold (histFamily n seed)) ((n : Nat) : Int)
      (tail₁ ++ [(.base ⟨25 + 2 * n⟩,
        ⟨some tU64,
          .int ((occurrences ((q : Nat) : Int)
            (histFamily n seed) : Nat) : Int) .uint64⟩)])
      (25 + 2 * n) (25 + 2 * n + 1) ch (by omega) hdead2 rfl)
  have hS12 := stepFnIter_chain hS11 hID
  have hrA := hg_rA_raw σ n ((seed : Nat) : Int) ((q : Nat) : Int)
    ((n : Nat) : Int) ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
    (countsFold (histFamily n seed)) ((n : Nat) : Int)
    (tail₁ ++ [(.base ⟨25 + 2 * n⟩,
      ⟨some tU64,
        .int ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
          .uint64⟩)] ++ [(.base ⟨25 + 2 * n + 1⟩, u64cell 0)])
    (25 + 2 * n) (25 + 2 * n + 2) ch
  have hS13 := stepFnIter_chain hS12 hrA
  have hlkD : Heap.lookup (tail₁ ++ [(.base ⟨25 + 2 * n⟩,
      ⟨some tU64,
        .int ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
          .uint64⟩)] ++ [(.base ⟨25 + 2 * n + 1⟩, u64cell 0)])
      (.base ⟨25 + 2 * n + 1⟩) = some (u64cell 0) := by
    rw [lookup_append_right (hdead2 (25 + 2 * n + 1) (Nat.le_refl _))]
    exact lookup_singleton_self
  have hstD := stepFnIter_one
    (hg_stDistinct σ n ((seed : Nat) : Int) ((q : Nat) : Int)
      ((n : Nat) : Int) ((n : Nat) : Int) (histFamily n seed)
      (histPre n seed) (countsFold (histFamily n seed)) ((n : Nat) : Int)
      (tail₁ ++ [(.base ⟨25 + 2 * n⟩,
        ⟨some tU64,
          .int ((occurrences ((q : Nat) : Int)
            (histFamily n seed) : Nat) : Int) .uint64⟩)]
        ++ [(.base ⟨25 + 2 * n + 1⟩, u64cell 0)])
      (25 + 2 * n) (25 + 2 * n + 2) 0 0
      (.seq [hMapRangeStmt, hRetSeqn] (envRBDH (25 + 2 * n)) frameKH) ch
      (by omega) hlkD (by rfl) [] [] (.seqn #[]) (envRBDH (25 + 2 * n)))
  rw [set_append_right (hdead2 (25 + 2 * n + 1) (Nat.le_refl _)),
    set_singleton_self] at hstD
  have hS14 := stepFnIter_chain hS13 hstD
  -- the range head
  have hrB := hg_rB_raw σ n ((seed : Nat) : Int) ((q : Nat) : Int)
    ((n : Nat) : Int) ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
    (countsFold (histFamily n seed)) ((n : Nat) : Int)
    (tail₁ ++ [(.base ⟨25 + 2 * n⟩,
      ⟨some tU64,
        .int ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
          .uint64⟩)] ++ [(.base ⟨25 + 2 * n + 1⟩, u64cell 0)])
    (25 + 2 * n) (25 + 2 * n + 2) ch
  have hS15 := stepFnIter_chain hS14 hrB
  have hsnap := stepFnIter_one
    (hg_rangeStart σ n ((seed : Nat) : Int) ((q : Nat) : Int) ((n : Nat) : Int)
      ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
      (countsFold (histFamily n seed)) ((n : Nat) : Int)
      (tail₁ ++ [(.base ⟨25 + 2 * n⟩,
        ⟨some tU64,
          .int ((occurrences ((q : Nat) : Int)
            (histFamily n seed) : Nat) : Int) .uint64⟩)]
        ++ [(.base ⟨25 + 2 * n + 1⟩, u64cell 0)])
      (25 + 2 * n) (25 + 2 * n + 2) ch)
  have hS16 := stepFnIter_chain hS15 hsnap
  -- THE RANGE LOOP, at every choice stream
  have hlkH3 : Heap.lookup (tail₁ ++ [(.base ⟨25 + 2 * n⟩,
      ⟨some tU64,
        .int ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
          .uint64⟩)] ++ [(.base ⟨25 + 2 * n + 1⟩, u64cell 0)])
      (.base ⟨25 + 2 * n⟩)
      = some (u64cell
          ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)) :=
    lookup_append_left
      (by
        rw [lookup_append_right (htail₁ (25 + 2 * n) (Nat.le_refl _))]
        exact lookup_singleton_self)
  have hmle : (countsFold (histFamily n seed)).length ≤ n := by
    have := countsList_length_le (histFamily n seed)
    omega
  obtain ⟨k₅, ch₅, tail₂, hk₅, hd1, hd2, hd3, hrun₂⟩ :=
    hg_range_loop σ n ((seed : Nat) : Int) ((q : Nat) : Int) ((n : Nat) : Int)
      ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
      (countsFold (histFamily n seed)) ((n : Nat) : Int)
      (countsFold_norm (histFamily n seed) hws (by omega))
      (countsFold_nodup_keys (histFamily n seed))
      (countsFold (histFamily n seed)).length (countsFold (histFamily n seed))
      rfl #[] 0
      (tail₁ ++ [(.base ⟨25 + 2 * n⟩,
        ⟨some tU64,
          .int ((occurrences ((q : Nat) : Int)
            (histFamily n seed) : Nat) : Int) .uint64⟩)]
        ++ [(.base ⟨25 + 2 * n + 1⟩, u64cell 0)])
      (25 + 2 * n) (25 + 2 * n + 2) ch
      ⟨[], by simp [toKeys], by
        symm
        apply List.filter_eq_self.mpr
        intro q _
        simp⟩
      (by omega) (by omega) (by omega) hlkD
      hdead2.push
  rw [hlkH3] at hd2
  rw [Nat.zero_add, hdlen] at hd1
  have hS17 := stepFnIter_chain hS16 hrun₂
  -- THE EXIT PHASE (the state family shifts to `σXH`; the fronts agree)
  have hbridge : σH σ n ((seed : Nat) : Int) ((q : Nat) : Int)
      ((n : Nat) : Int) ((n : Nat) : Int) (histFamily n seed)
      (histPre n seed) (countsFold (histFamily n seed)) ((n : Nat) : Int)
      false tail₂ (25 + 2 * n + 2)
      = σXH σ n ((seed : Nat) : Int) ((q : Nat) : Int) ((n : Nat) : Int)
        ((n : Nat) : Int) (histFamily n seed) (histPre n seed) zeros8
        (countsFold (histFamily n seed)) 0 0 0 0 0 0 tail₂
        (25 + 2 * n + 2) := rfl
  rw [hbridge] at hS17
  have hX1 := hg_X1_raw σ n ((seed : Nat) : Int) ((q : Nat) : Int)
    ((n : Nat) : Int) ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
    zeros8 (countsFold (histFamily n seed)) 0 0 0 0 0 0 tail₂ (25 + 2 * n)
    (25 + 2 * n + 2) ch₅
  have hS18 := stepFnIter_chain hS17 hX1
  have hvH := stepFnIter_one
    (hg_varHits σ n ((seed : Nat) : Int) ((q : Nat) : Int) ((n : Nat) : Int)
      ((n : Nat) : Int) (histFamily n seed) (histPre n seed) zeros8
      (countsFold (histFamily n seed)) 0 0 0 0 0 0 tail₂ (25 + 2 * n)
      (25 + 2 * n + 2)
      ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
      (envRBDH (25 + 2 * n))
      (.rhsK .vals [.chain (.addr (.base ⟨18⟩)) [] []] [] [] (.seqn #[])
        (envRBDH (25 + 2 * n))
        (.seq [.assign (.var "$res1") (.var "distinct"), .returnStmt]
          (envRBDH (25 + 2 * n)) frameKH))
      ch₅ rfl (by omega) hd2)
  have hS19 := stepFnIter_chain hS18 hvH
  have hX2a := hg_X2a_raw σ n ((seed : Nat) : Int) ((q : Nat) : Int)
    ((n : Nat) : Int) ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
    zeros8 (countsFold (histFamily n seed)) 0 0 0 0 0 0
    ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int) tail₂
    (25 + 2 * n) (25 + 2 * n + 2) ch₅
  rw [hHn] at hX2a
  have hS20 := stepFnIter_chain hS19 hX2a
  have hX2b := hg_X2b_raw σ n ((seed : Nat) : Int) ((q : Nat) : Int)
    ((n : Nat) : Int) ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
    zeros8 (countsFold (histFamily n seed)) 0 0 0 0
    ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int) 0 tail₂
    (25 + 2 * n) (25 + 2 * n + 2) ch₅
  have hS21 := stepFnIter_chain hS20 hX2b
  have hvD := stepFnIter_one
    (hg_varDistinctX σ n ((seed : Nat) : Int) ((q : Nat) : Int)
      ((n : Nat) : Int) ((n : Nat) : Int) (histFamily n seed)
      (histPre n seed) zeros8 (countsFold (histFamily n seed)) 0 0 0 0
      ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int) 0
      tail₂ (25 + 2 * n) (25 + 2 * n + 2)
      ((distinctCount (histFamily n seed) : Nat) : Int)
      (envRBDH (25 + 2 * n))
      (.rhsK .vals [.chain (.addr (.base ⟨19⟩)) [] []] [] [] (.seqn #[])
        (envRBDH (25 + 2 * n))
        (.seq [.returnStmt] (envRBDH (25 + 2 * n)) frameKH))
      ch₅ rfl (by omega) hd1)
  have hS22 := stepFnIter_chain hS21 hvD
  have hX3a := hg_X3a_raw σ n ((seed : Nat) : Int) ((q : Nat) : Int)
    ((n : Nat) : Int) ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
    zeros8 (countsFold (histFamily n seed)) 0 0 0 0
    ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int) 0
    ((distinctCount (histFamily n seed) : Nat) : Int) tail₂ (25 + 2 * n)
    (25 + 2 * n + 2) ch₅
  rw [hDn] at hX3a
  have hS23 := stepFnIter_chain hS22 hX3a
  have hX3b := hg_X3b_raw σ n ((seed : Nat) : Int) ((q : Nat) : Int)
    ((n : Nat) : Int) ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
    zeros8 (countsFold (histFamily n seed)) 0 0 0 0
    ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
    ((distinctCount (histFamily n seed) : Nat) : Int) tail₂ (25 + 2 * n)
    (25 + 2 * n + 2) ch₅
  rw [hHn, hDn] at hX3b
  have hS24 := stepFnIter_chain hS23 hX3b
  -- the ARRAY store `$res0 = vals` (the one conditioned epilogue step)
  have hstore : storeTarget
      (σXH σ n ((seed : Nat) : Int) ((q : Nat) : Int) ((n : Nat) : Int)
        ((n : Nat) : Int) (histFamily n seed) (histPre n seed) zeros8
        (countsFold (histFamily n seed)) 0 0
        ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
        ((distinctCount (histFamily n seed) : Nat) : Int)
        ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
        ((distinctCount (histFamily n seed) : Nat) : Int) tail₂
        (25 + 2 * n + 2))
      hRes0Ref (.array ⟨(histPre n seed).map (fun v => .int v .uint64)⟩)
      = .ok (σXH σ n ((seed : Nat) : Int) ((q : Nat) : Int) ((n : Nat) : Int)
          ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
          (histPre n seed) (countsFold (histFamily n seed)) 0 0
          ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
          ((distinctCount (histFamily n seed) : Nat) : Int)
          ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
          ((distinctCount (histFamily n seed) : Nat) : Int) tail₂
          (25 + 2 * n + 2)) :=
    storeTarget_addr
      (lookup_res0_XH σ n ((seed : Nat) : Int) ((q : Nat) : Int)
        ((n : Nat) : Int) ((n : Nat) : Int) (histFamily n seed)
        (histPre n seed) zeros8 (countsFold (histFamily n seed)) 0 0
        ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
        ((distinctCount (histFamily n seed) : Nat) : Int)
        ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
        ((distinctCount (histFamily n seed) : Nat) : Int) tail₂
        (25 + 2 * n + 2))
      (normalizeValueForTy_arr_u64 (histPre_length hcap) histPre_range)
  have hS25 := stepFnIter_chain hS24 (stepFnIter_one
    (stepFn_store_step hstore))
  have hX4 := hg_X4_raw σ n ((seed : Nat) : Int) ((q : Nat) : Int)
    ((n : Nat) : Int) ((n : Nat) : Int) (histFamily n seed) (histPre n seed)
    (histPre n seed) (countsFold (histFamily n seed)) 0 0
    ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
    ((distinctCount (histFamily n seed) : Nat) : Int)
    ((occurrences ((q : Nat) : Int) (histFamily n seed) : Nat) : Int)
    ((distinctCount (histFamily n seed) : Nat) : Int) tail₂
    (25 + 2 * n + 2) ch₅
  rw [hHn, hDn] at hX4
  have hS26 := stepFnIter_chain hS25 hX4
  exact ⟨_, ch₅, tail₂, 25 + 2 * n + 2, by omega, hS26⟩


end GoLean.Examples.Histogram
