import GoLeanProofs.Examples.Histogram.Machine

/-!
# Histogram — CountLoop

The COUNTING-LOOP half of the `histogram` run proof: from the exit-test
delivery at value `i` (`.retV (.bool (decide (i < len vals)))
cmpContCH`), the run folds every value into the counts map and exits
into the `hits := counts[q]` head, in at most `84·m + 9` steps
(`m = len vals − i`), allocating exactly the two per-iteration scratch
cells (`$c1` at `na`, `$c2` at `na + 1`).

## Kit gap witnessed here (campaign log `g1.md`)

**GAP-C1 the counting-loop generic layer is wordcount-specific.**
`Examples/WordCount/CountGeneric.lean` proves exactly this iteration
(`wcIter_generic`, 53 steps) and loop induction (`wcLoop_generic`)
placement-generically — but both are STATED over the concrete statement
constants `asgnC1`/`seqnC2`/`mapAsgnStmt`, which mention the Go
variable name `"words"`. Histogram's counting body mentions `"vals"`
(`asgnC1H`/`seqnC2H`/`mapAsgnStmtH`), so neither theorem applies and
this module re-derives the whole tower at histogram's (single)
placement. Shape wanted: the generic layer parameterized over the
body's three statement constants (equivalently, over the slice/counter
variable names they embed) the same way it is already parameterized
over the state family, placement environments and continuations — then
an example discharges the same per-segment facts and instantiates
instead of re-deriving. Because histogram has ONE placement (wordcount
had three), this module takes the direct route (concrete placement,
raw segments + conditioned discharges + one composed iteration + the
loop induction) rather than re-deriving a histogram-local generic pair;
the storm-avoidance discipline is unchanged — every statement is over
the abstract state family `σH σ L sv qv siv civ ws lp kvs iv ff dead
na`, and no concrete 25-cell front ever reaches the unifier inside a
composition step.

Two smaller re-derivations, same family as Pure's GAP-P1 (the
`bump`/`countsList` fold layer): `take_succ_getD` and `cnt_take_le`
below are verbatim `Examples/WordCount/CanonCount.lean` lemmas
(wordcount-local, so not importable without pulling in wordcount's
program). They belong with the `MapMem`-lifted fold vocabulary.
-/

namespace GoLean.Examples.Histogram

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem
open GoLean.MapMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- The nil-map cell — `$c1`'s default value before the `counts`
handle is copied over it (the wordcount `nilMapCell`, re-derived:
GAP-C1's cell vocabulary). -/
abbrev nilMapCellH : HeapCell := ⟨some tMap, .map ⟨none⟩⟩

/-! ## The GAP-P1-family list lemmas (re-derived from
`Examples/WordCount/CanonCount.lean`) -/

private theorem take_succ_getD {ws : List Int} {i : Nat}
    (hi : i < ws.length) :
    ws.take (i + 1) = ws.take i ++ [ws.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

private theorem cnt_take_le {ws : List Int} {i : Nat} (w : Int) :
    cnt (countsList (ws.take i)) w ≤ i := by
  rw [cnt_countsList']
  simp only [occurrences]
  have h1 : ((ws.take i).filter (· = w)).length ≤ (ws.take i).length :=
    List.length_filter_le _ _
  have h2 : (ws.take i).length ≤ i := by
    rw [List.length_take]
    exact Nat.min_le_left _ _
  omega

/-! ## The counting-loop raw segments (step counts identical to the
wordcount tower — same statements up to the `"vals"` rename, new
addresses) -/

/-- Head at `$forFirst = false`: the `i++` else branch, the store back
to `i`, the next `len(vals)` read at its apply point. 29 steps. -/
theorem hg_segA1_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (na : Nat) (ch : Choices) :
    stepFnIter 29 (σH σ L sv qv siv civ ws lp kvs iv false dead na) headCH ch
      = .ok (.retV (hSliceV L)
            (lenKH (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
          σH σ L sv qv siv civ ws lp kvs
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            false dead na, ch) := by
  with_unfolding_all rfl

/-- Exit test true → the `$c1` initialization under the counting
body's spliced sequence. 7 steps. -/
theorem hg_segC1_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (na : Nat) (ch : Choices) :
    stepFnIter 7 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.retV (.bool true) cmpContCH) ch
      = .ok (.exec (.initialization { id := "$c1", typ := tMap }) env3H
            (.seq [asgnC1H, seqnC2H, mapAsgnStmtH] env3H postBodyKH),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  with_unfolding_all rfl

/-- `$c1 = counts`: the handle read banked at the drained store. 6
steps. -/
theorem hg_segC2_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (na₀ na : Nat) (ch : Choices) :
    stepFnIter 6 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.next (.seq [asgnC1H, seqnC2H, mapAsgnStmtH] (u1EnvH na₀) postBodyKH))
      ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀⟩)) [] []]
            [.map ⟨some (.base ⟨21⟩)⟩] (.seqn #[]) (u1EnvH na₀)
            (.seq [seqnC2H, mapAsgnStmtH] (u1EnvH na₀) postBodyKH)),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  with_unfolding_all rfl

/-- Drained store → the `$c2` initialization (kit steps: the `seqCont`
env check blocks `rfl` once the env carries the symbolic `na₀`). 5
steps. -/
theorem hg_segC3_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (na₀ na : Nat) (ch : Choices) :
    stepFnIter 5 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.next (.storeK [] [] (.seqn #[]) (u1EnvH na₀)
        (.seq [seqnC2H, mapAsgnStmtH] (u1EnvH na₀) postBodyKH))) ch
      = .ok (.exec (.initialization { id := "$c2", typ := tU64 }) (u1EnvH na₀)
            (.seq [.assign (.var "$c2")
                (.indexGet (.var "vals") (.var "i")), mapAsgnStmtH]
              (u1EnvH na₀) postBodyKH),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead na) (body := .seqn #[])
    (env := u1EnvH na₀)
    (k := .seq [seqnC2H, mapAsgnStmtH] (u1EnvH na₀) postBodyKH) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead na) (ss := #[])
    (env := u1EnvH na₀) (rest := [seqnC2H, mapAsgnStmtH]) (k := postBodyKH)
    (ch := ch))
  have h3 := stepFnIter_one (stepFn_seq_pop
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead na) (t := seqnC2H)
    (rest := [mapAsgnStmtH]) (env := u1EnvH na₀) (k := postBodyKH) (ch := ch))
  have h4 := stepFnIter_one (stepFn_seqn_splice
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead na)
    (ss := #[.initialization { id := "$c2", typ := tU64 },
      .assign (.var "$c2") (.indexGet (.var "vals") (.var "i"))])
    (env := u1EnvH na₀) (rest := [mapAsgnStmtH]) (k := postBodyKH) (ch := ch))
  have h5 := stepFnIter_one (stepFn_seq_pop
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead na)
    (t := .initialization { id := "$c2", typ := tU64 })
    (rest := [.assign (.var "$c2")
      (.indexGet (.var "vals") (.var "i")), mapAsgnStmtH])
    (env := u1EnvH na₀) (k := postBodyKH) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h1 h2) h3) h4) h5

/-- `$c2 = vals[i]`: the `vals` handle and the `i` read delivered at
the `indexGet` apply point. 8 steps. -/
theorem hg_segC4_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (na₀ na : Nat) (ch : Choices) :
    stepFnIter 8 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.next (.seq [.assign (.var "$c2")
          (.indexGet (.var "vals") (.var "i")), mapAsgnStmtH]
        (uEnvH na₀) postBodyKH)) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [hSliceV L] [] (uEnvH na₀)
              (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
                (.seqn #[]) (uEnvH na₀)
                (.seq [mapAsgnStmtH] (uEnvH na₀) postBodyKH))),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  with_unfolding_all rfl

theorem hg_segC5_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (na₀ na : Nat) (w : GoValue) (ch : Choices) :
    stepFnIter 1 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.retV w
        (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
          (.seqn #[]) (uEnvH na₀)
          (.seq [mapAsgnStmtH] (uEnvH na₀) postBodyKH))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [w]
            (.seqn #[]) (uEnvH na₀)
            (.seq [mapAsgnStmtH] (uEnvH na₀) postBodyKH)),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  with_unfolding_all rfl

/-- Drained store → the `mapAssign` spine's first operand read. 4
steps (kit + a 2-step tail, as in the wordcount original). -/
theorem hg_segC6_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (na₀ na : Nat) (ch : Choices) :
    stepFnIter 4 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.next (.storeK [] [] (.seqn #[]) (uEnvH na₀)
        (.seq [mapAsgnStmtH] (uEnvH na₀) postBodyKH))) ch
      = .ok (.evalE (.var "$c1") (uEnvH na₀) (stK0H na₀),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead na) (body := .seqn #[])
    (env := uEnvH na₀) (k := .seq [mapAsgnStmtH] (uEnvH na₀) postBodyKH)
    (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead na) (ss := #[])
    (env := uEnvH na₀) (rest := [mapAsgnStmtH]) (k := postBodyKH) (ch := ch))
  have h3 : stepFnIter 2 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.next (.seq ((#[] : Array Stmt).toList ++ [mapAsgnStmtH]) (uEnvH na₀)
        postBodyKH)) ch
      = .ok (.evalE (.var "$c1") (uEnvH na₀) (stK0H na₀),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

theorem hg_segC7_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (na₀ na : Nat) (ch : Choices) :
    stepFnIter 1 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.retV (.map ⟨some (.base ⟨21⟩)⟩) (stK0H na₀)) ch
      = .ok (.evalE (.var "$c2") (uEnvH na₀)
            (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨21⟩)⟩]
              [.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
                (.intLit 1 .uint64)]
              (uEnvH na₀) (.seq [] (uEnvH na₀) postBodyKH)),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  with_unfolding_all rfl

theorem hg_segC8_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (na₀ na : Nat) (w : Int) (ch : Choices) :
    stepFnIter 3 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.retV (.int w .uint64)
        (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨21⟩)⟩]
          [.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
            (.intLit 1 .uint64)]
          (uEnvH na₀) (.seq [] (uEnvH na₀) postBodyKH))) ch
      = .ok (.evalE (.var "$c1") (uEnvH na₀)
            (.strictK (.mapGet tU64 tU64) [] [.var "$c2"] (uEnvH na₀)
              (addKH na₀ w)),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  with_unfolding_all rfl

theorem hg_segC9_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (na₀ na : Nat) (w : Int) (ch : Choices) :
    stepFnIter 1 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.retV (.map ⟨some (.base ⟨21⟩)⟩)
        (.strictK (.mapGet tU64 tU64) [] [.var "$c2"] (uEnvH na₀)
          (addKH na₀ w))) ch
      = .ok (.evalE (.var "$c2") (uEnvH na₀) (mapGetKH na₀ w),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  with_unfolding_all rfl

theorem hg_segC10_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (na₀ na : Nat) (w cv : Int) (ch : Choices) :
    stepFnIter 3 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.retV (.int cv .uint64) (addKH na₀ w)) ch
      = .ok (.retV (.int (IntKind.normalize .uint64 (cv + 1)) .uint64)
            (stK2H na₀ w),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  with_unfolding_all rfl

theorem hg_segC11_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (na₀ na : Nat) (ch : Choices) :
    stepFnIter 3 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.next (.seq [] (uEnvH na₀) postBodyKH)) ch
      = .ok (headCH, σH σ L sv qv siv civ ws lp kvs iv false dead na,
          ch) := by
  with_unfolding_all rfl

/-- Counting-loop exit: test false → break unwinds to the function
tail, whose first statement (`hitsSeqn`) splices down to the `hits`
initialization. 9 steps — and, unlike wordcount's 23-step exit, no
allocation: the `hits` cell itself is the OTHER shard's first step. -/
theorem hg_segX0_raw (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (na : Nat) (ch : Choices) :
    stepFnIter 9 (σH σ L sv qv siv civ ws lp kvs iv false dead na)
      (.retV (.bool false) cmpContCH) ch
      = .ok (.exec (.initialization { id := "hits", typ := tU64 }) envR0H
            (.seq [.assign (.var "hits")
                (.mapGet (.var "counts") (.var "q") tU64 tU64),
              distinctSeqn, hMapRangeStmt, hRetSeqn] envR0H frameKH),
          σH σ L sv qv siv civ ws lp kvs iv false dead na, ch) := by
  with_unfolding_all rfl

/-! ## The conditioned discharges (heap-touching steps; `base0 = 25`) -/

theorem hg_init1 (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
      (ch : Choices), 25 ≤ na → DeadFrom dead na →
    stepFn (σH σ L sv qv siv civ ws lp kvs iv false dead na)
        (.exec (.initialization { id := "$c1", typ := tMap }) env3H
          (.seq [asgnC1H, seqnC2H, mapAsgnStmtH] env3H postBodyKH)) ch
      = .ok (.next (.seq [asgnC1H, seqnC2H, mapAsgnStmtH] (u1EnvH na)
            postBodyKH),
          σH σ L sv qv siv civ ws lp kvs iv false
            (dead ++ [(.base ⟨na⟩, nilMapCellH)]) (na + 1), ch) := by
  intro kvs iv dead na ch hna hdead
  have hmiss : Heap.lookup
      (frontH L sv qv siv civ ws lp kvs iv false ++ dead) (.base ⟨na⟩)
      = none := by
    rw [lookup_append_right
      (lookup_frontH_none L sv qv siv civ ws lp kvs iv false hna)]
    exact hdead na (Nat.le_refl na)
  have h := stepFn_init_seq
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead na)
    (p := { id := "$c1", typ := tMap })
    (rest := [asgnC1H, seqnC2H, mapAsgnStmtH]) (env := env3H)
    (k := postBodyKH) (ch := ch) (v := .map ⟨none⟩)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show (σH σ L sv qv siv civ ws lp kvs iv false dead na).nextAddr = na
      from rfl,
    show (σH σ L sv qv siv civ ws lp kvs iv false dead na).heap
      = frontH L sv qv siv civ ws lp kvs iv false ++ dead from rfl,
    set_fresh hmiss, List.append_assoc] at h
  exact h

theorem hg_st1 (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ na : Nat)
      (ch : Choices), 25 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σH σ L sv qv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, nilMapCellH)]) na)
        (.next (.storeK [.chain (.addr (.base ⟨na₀⟩)) [] []]
          [.map ⟨some (.base ⟨21⟩)⟩] (.seqn #[]) (u1EnvH na₀)
          (.seq [seqnC2H, mapAsgnStmtH] (u1EnvH na₀) postBodyKH))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (u1EnvH na₀)
            (.seq [seqnC2H, mapAsgnStmtH] (u1EnvH na₀) postBodyKH)),
          σH σ L sv qv siv civ ws lp kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhCellH)]) na, ch) := by
  intro kvs iv dead na₀ na ch hna hdead
  have hlook : Heap.lookup
      (σH σ L sv qv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, nilMapCellH)]) na).heap
      (.base ⟨na₀⟩) = some ⟨some tMap, .map ⟨none⟩⟩ := by
    show Heap.lookup
      (frontH L sv qv siv civ ws lp kvs iv false
        ++ (dead ++ [(.base ⟨na₀⟩, nilMapCellH)]))
      (.base ⟨na₀⟩) = some ⟨some tMap, .map ⟨none⟩⟩
    rw [lookup_append_right
        (lookup_frontH_none L sv qv siv civ ws lp kvs iv false hna),
      lookup_append_right (hdead na₀ (Nat.le_refl na₀))]
    exact lookup_singleton_self
  have h := storeTarget_addr (v := .map ⟨some (.base ⟨21⟩)⟩)
    (v' := .map ⟨some (.base ⟨21⟩)⟩) hlook
    (by simp [normalizeValueForTy, normalizeValueForTyFuel,
      typeResolutionFuel])
  rw [show (σH σ L sv qv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, nilMapCellH)]) na).heap
      = frontH L sv qv siv civ ws lp kvs iv false
        ++ (dead ++ [(.base ⟨na₀⟩, nilMapCellH)]) from rfl,
    set_append_right
      (lookup_frontH_none L sv qv siv civ ws lp kvs iv false hna),
    set_append_right (hdead na₀ (Nat.le_refl na₀)),
    set_singleton_self] at h
  exact stepFn_store_step h

theorem hg_init2 (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ : Nat)
      (ch : Choices), 25 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σH σ L sv qv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhCellH)]) (na₀ + 1))
        (.exec (.initialization { id := "$c2", typ := tU64 }) (u1EnvH na₀)
          (.seq [.assign (.var "$c2")
              (.indexGet (.var "vals") (.var "i")), mapAsgnStmtH]
            (u1EnvH na₀) postBodyKH)) ch
      = .ok (.next (.seq [.assign (.var "$c2")
            (.indexGet (.var "vals") (.var "i")), mapAsgnStmtH]
            (uEnvH na₀) postBodyKH),
          σH σ L sv qv siv civ ws lp kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhCellH), (.base ⟨na₀ + 1⟩, u64cell 0)])
            (na₀ + 2), ch) := by
  intro kvs iv dead na₀ ch hna hdead
  have hmiss : Heap.lookup
      (frontH L sv qv siv civ ws lp kvs iv false
        ++ (dead ++ [(.base ⟨na₀⟩, mhCellH)]))
      (.base ⟨na₀ + 1⟩) = none := by
    rw [lookup_append_right
        (lookup_frontH_none L sv qv siv civ ws lp kvs iv false (by omega)),
      lookup_append_right (hdead (na₀ + 1) (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
    rfl
  have h := stepFn_init_seq
    (σ := σH σ L sv qv siv civ ws lp kvs iv false
      (dead ++ [(.base ⟨na₀⟩, mhCellH)]) (na₀ + 1))
    (p := { id := "$c2", typ := tU64 })
    (rest := [.assign (.var "$c2")
      (.indexGet (.var "vals") (.var "i")), mapAsgnStmtH])
    (env := u1EnvH na₀) (k := postBodyKH) (ch := ch) (v := .int 0 .uint64)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show (σH σ L sv qv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhCellH)]) (na₀ + 1)).nextAddr = na₀ + 1
      from rfl,
    show (σH σ L sv qv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhCellH)]) (na₀ + 1)).heap
      = frontH L sv qv siv civ ws lp kvs iv false
        ++ (dead ++ [(.base ⟨na₀⟩, mhCellH)]) from rfl,
    set_fresh hmiss, List.append_assoc, List.append_assoc] at h
  exact h

theorem hg_st2 (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ na : Nat)
      (w : Int) (ch : Choices), 0 ≤ w → w < 2 ^ 64 →
      25 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σH σ L sv qv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhCellH), (.base ⟨na₀ + 1⟩, u64cell 0)]) na)
        (.next (.storeK [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []]
          [.int w .uint64] (.seqn #[]) (uEnvH na₀)
          (.seq [mapAsgnStmtH] (uEnvH na₀) postBodyKH))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (uEnvH na₀)
            (.seq [mapAsgnStmtH] (uEnvH na₀) postBodyKH)),
          σH σ L sv qv siv civ ws lp kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhCellH), (.base ⟨na₀ + 1⟩, u64cell w)])
            na, ch) := by
  intro kvs iv dead na₀ na w ch hw0 hw64 hna hdead
  have hwnorm : IntKind.normalize .uint64 w = w := unorm_of_range hw0 hw64
  have hlook : Heap.lookup
      (σH σ L sv qv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhCellH), (.base ⟨na₀ + 1⟩, u64cell 0)])
        na).heap
      (.base ⟨na₀ + 1⟩) = some ⟨some tU64, .int 0 .uint64⟩ := by
    show Heap.lookup
      (frontH L sv qv siv civ ws lp kvs iv false
        ++ (dead ++ ([(.base ⟨na₀⟩, mhCellH)]
          ++ [(.base ⟨na₀ + 1⟩, u64cell 0)])))
      (.base ⟨na₀ + 1⟩) = some ⟨some tU64, .int 0 .uint64⟩
    rw [lookup_append_right
        (lookup_frontH_none L sv qv siv civ ws lp kvs iv false (by omega)),
      lookup_append_right (hdead (na₀ + 1) (by omega)),
      lookup_append_right (show Heap.lookup [(.base ⟨na₀⟩, mhCellH)]
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
  rw [show (σH σ L sv qv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhCellH), (.base ⟨na₀ + 1⟩, u64cell 0)])
        na).heap
      = frontH L sv qv siv civ ws lp kvs iv false
        ++ (dead ++ ([(.base ⟨na₀⟩, mhCellH)]
          ++ [(.base ⟨na₀ + 1⟩, u64cell 0)])) from rfl,
    set_append_right
      (lookup_frontH_none L sv qv siv civ ws lp kvs iv false (by omega)),
    set_append_right (hdead (na₀ + 1) (by omega)),
    set_append_right (show Heap.lookup [(.base ⟨na₀⟩, mhCellH)]
        (.base ⟨na₀ + 1⟩) = none from by
      rw [lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
      rfl),
    set_singleton_self] at h
  exact stepFn_store_step h

theorem hg_lk1 (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv w : Int)
    (dead : Heap) (na₀ na : Nat) (hna : 25 ≤ na₀)
    (hdead : DeadFrom dead na₀) :
    Heap.lookup (σH σ L sv qv siv civ ws lp kvs iv false
      (dead ++ [(.base ⟨na₀⟩, mhCellH), (.base ⟨na₀ + 1⟩, u64cell w)])
      na).heap
      (.base ⟨na₀⟩) = some mhCellH := by
  show Heap.lookup
    (frontH L sv qv siv civ ws lp kvs iv false
      ++ (dead ++ ([(.base ⟨na₀⟩, mhCellH)]
        ++ [(.base ⟨na₀ + 1⟩, u64cell w)])))
    (.base ⟨na₀⟩) = some mhCellH
  rw [lookup_append_right
      (lookup_frontH_none L sv qv siv civ ws lp kvs iv false hna),
    lookup_append_right (hdead na₀ (Nat.le_refl na₀))]
  exact lookup_append_left lookup_singleton_self

theorem hg_lk2 (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv w : Int)
    (dead : Heap) (na₀ na : Nat) (hna : 25 ≤ na₀)
    (hdead : DeadFrom dead na₀) :
    Heap.lookup (σH σ L sv qv siv civ ws lp kvs iv false
      (dead ++ [(.base ⟨na₀⟩, mhCellH), (.base ⟨na₀ + 1⟩, u64cell w)])
      na).heap
      (.base ⟨na₀ + 1⟩) = some (u64cell w) := by
  show Heap.lookup
    (frontH L sv qv siv civ ws lp kvs iv false
      ++ (dead ++ ([(.base ⟨na₀⟩, mhCellH)]
        ++ [(.base ⟨na₀ + 1⟩, u64cell w)])))
    (.base ⟨na₀ + 1⟩) = some (u64cell w)
  rw [lookup_append_right
      (lookup_frontH_none L sv qv siv civ ws lp kvs iv false (by omega)),
    lookup_append_right (hdead (na₀ + 1) (by omega)),
    lookup_append_right (show Heap.lookup [(.base ⟨na₀⟩, mhCellH)]
        (.base ⟨na₀ + 1⟩) = none from by
      rw [lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
      rfl)]
  exact lookup_singleton_self

theorem hg_var1 (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv w : Int) (dead : Heap) (na₀ na : Nat)
      (k : Cont) (ch : Choices), 25 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σH σ L sv qv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhCellH), (.base ⟨na₀ + 1⟩, u64cell w)]) na)
        (.evalE (.var "$c1") (uEnvH na₀) k) ch
      = .ok (.retV (.map ⟨some (.base ⟨21⟩)⟩) k,
          σH σ L sv qv siv civ ws lp kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhCellH), (.base ⟨na₀ + 1⟩, u64cell w)])
            na, ch) := by
  intro kvs iv w dead na₀ na k ch hna hdead
  exact stepFn_var rfl (hg_lk1 σ L sv qv siv civ ws lp kvs iv w dead na₀ na
    hna hdead)

theorem hg_var2 (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv w : Int) (dead : Heap) (na₀ na : Nat)
      (k : Cont) (ch : Choices), 25 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σH σ L sv qv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhCellH), (.base ⟨na₀ + 1⟩, u64cell w)]) na)
        (.evalE (.var "$c2") (uEnvH na₀) k) ch
      = .ok (.retV (.int w .uint64) k,
          σH σ L sv qv siv civ ws lp kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhCellH), (.base ⟨na₀ + 1⟩, u64cell w)])
            na, ch) := by
  intro kvs iv w dead na₀ na k ch hna hdead
  exact stepFn_var rfl (hg_lk2 σ L sv qv siv civ ws lp kvs iv w dead na₀ na
    hna hdead)

theorem hg_read (σ : ExecState) (sv qv siv civ : Int) (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (i : Nat) (dead : Heap) (na : Nat),
      i < ws.length →
    applyStrictOp (σH σ ws.length sv qv siv civ ws lp kvs ((i : Nat) : Int)
        false dead na) .indexGet
        [hSliceV ws.length, .int ((i : Nat) : Int) .int]
      = .ok (.int (ws.getD i 0) .uint64,
          σH σ ws.length sv qv siv civ ws lp kvs ((i : Nat) : Int) false dead
            na) := by
  intro kvs i dead na hi
  have hget : (⟨ws.map (fun v => .int v .uint64)⟩ : Array GoValue)[0 + i]?
      = some (.int (ws.getD i 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU ws i hi]
  exact applyStrictOp_indexGet_slice (dty := some (.array ws.length tU64))
    (off := 0) (len := ws.length) (cap := ws.length) (ik := .int) rfl
    (Nat.le_refl ws.length) hi hget

theorem hg_mapGet (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
      (w : Int), 0 ≤ w → w < 2 ^ 64 →
    applyStrictOp (σH σ L sv qv siv civ ws lp kvs iv false dead na)
        (.mapGet tU64 tU64) [.map ⟨some (.base ⟨21⟩)⟩, .int w .uint64]
      = .ok (.int (cnt kvs w : Int) .uint64,
          σH σ L sv qv siv civ ws lp kvs iv false dead na) := by
  intro kvs iv dead na w hw0 hw64
  exact applyStrictOp_mapGet (a := ⟨21⟩) (dty := none) rfl
    (unorm_of_range hw0 hw64)

theorem hg_mapAsgn (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ na : Nat)
      (w : Int) (v : Nat) (ch : Choices), 0 ≤ w → w < 2 ^ 64 → v < 2 ^ 64 →
    stepFn (σH σ L sv qv siv civ ws lp kvs iv false dead na)
        (.retV (.int ((v : Nat) : Int) .uint64) (stK2H na₀ w)) ch
      = .ok (.next (.seq [] (uEnvH na₀) postBodyKH),
          σH σ L sv qv siv civ ws lp (setk kvs w v) iv false dead na,
          ch) := by
  intro kvs iv dead na₀ na w v ch hw0 hw64 hv
  have hMA := mapAssignValue_toEntries (a := ⟨21⟩)
    (σ := σH σ L sv qv siv civ ws lp kvs iv false dead na)
    (v := v) rfl (unorm_of_range hw0 hw64)
    (unorm_of_range (by omega) (by exact_mod_cast hv))
  rw [show Heap.set (σH σ L sv qv siv civ ws lp kvs iv false dead na).heap
      (.base ⟨21⟩) ⟨none, .mapData (toEntries (setk kvs w v))⟩
      = frontH L sv qv siv civ ws lp (setk kvs w v) iv false ++ dead
      from rfl] at hMA
  exact stepFn_mapAssign_apply hMA

/-! ## One counting iteration, composed -/

/-- **One counting iteration** from the exit test's true delivery at
value `i`: `counts[vals[i]]++` in 53 steps, `$c1`/`$c2` materialized at
`na`/`na + 1`, the counts fold advanced one value (the chain is the
GAP-C1 re-derivation of `wcIter_generic`'s body at this placement). -/
theorem hg_count_iter (σ : ExecState) (sv qv siv civ : Int)
    (ws lp : List Int) (i : Nat) (dead : Heap) (na : Nat) (ch : Choices)
    (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64) (hlen : ws.length < 2 ^ 63)
    (hi : i < ws.length) (hna : 25 ≤ na) (hdead : DeadFrom dead na) :
    stepFnIter 53
      (σH σ ws.length sv qv siv civ ws lp (countsList (ws.take i)) (i : Int)
        false dead na)
      (.retV (.bool true) cmpContCH) ch
      = .ok (headCH,
          σH σ ws.length sv qv siv civ ws lp (countsList (ws.take (i + 1)))
            (i : Int) false
            (dead ++ [(.base ⟨na⟩, mhCellH),
              (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2), ch) := by
  have hw := hws (ws.getD i 0) (getD_mem hi)
  have hcnt : cnt (countsList (ws.take i)) (ws.getD i 0) + 1 < 2 ^ 64 := by
    have := cnt_take_le (ws := ws) (i := i) (ws.getD i 0)
    omega
  have h1 := stepFnIter_chain
    (hg_segC1_raw σ ws.length sv qv siv civ ws lp (countsList (ws.take i))
      ((i : Nat) : Int) dead na ch)
    (stepFnIter_one (hg_init1 σ ws.length sv qv siv civ ws lp
      (countsList (ws.take i)) ((i : Nat) : Int) dead na ch hna hdead))
  have h2 := stepFnIter_chain h1
    (hg_segC2_raw σ ws.length sv qv siv civ ws lp (countsList (ws.take i))
      ((i : Nat) : Int) (dead ++ [(.base ⟨na⟩, nilMapCellH)]) na (na + 1) ch)
  have h3 := stepFnIter_chain h2
    (stepFnIter_one (hg_st1 σ ws.length sv qv siv civ ws lp
      (countsList (ws.take i)) ((i : Nat) : Int) dead na (na + 1) ch hna
      hdead))
  have h4 := stepFnIter_chain h3
    (hg_segC3_raw σ ws.length sv qv siv civ ws lp (countsList (ws.take i))
      ((i : Nat) : Int) (dead ++ [(.base ⟨na⟩, mhCellH)]) na (na + 1) ch)
  have h5 := stepFnIter_chain h4
    (stepFnIter_one (hg_init2 σ ws.length sv qv siv civ ws lp
      (countsList (ws.take i)) ((i : Nat) : Int) dead na ch hna hdead))
  have h6 := stepFnIter_chain h5
    (hg_segC4_raw σ ws.length sv qv siv civ ws lp (countsList (ws.take i))
      ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhCellH), (.base ⟨na + 1⟩, u64cell 0)]) na
      (na + 2) ch)
  have h7 := stepFnIter_chain h6
    (stepFnIter_one (stepFn_strict_apply (done := [hSliceV ws.length])
      (hg_read σ sv qv siv civ ws lp (countsList (ws.take i)) i
        (dead ++ [(.base ⟨na⟩, mhCellH), (.base ⟨na + 1⟩, u64cell 0)])
        (na + 2) hi)))
  have h8 := stepFnIter_chain h7
    (hg_segC5_raw σ ws.length sv qv siv civ ws lp (countsList (ws.take i))
      ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhCellH), (.base ⟨na + 1⟩, u64cell 0)]) na
      (na + 2) (.int (ws.getD i 0) .uint64) ch)
  have h9 := stepFnIter_chain h8
    (stepFnIter_one (hg_st2 σ ws.length sv qv siv civ ws lp
      (countsList (ws.take i)) ((i : Nat) : Int) dead na (na + 2)
      (ws.getD i 0) ch hw.1 hw.2 hna hdead))
  have h10 := stepFnIter_chain h9
    (hg_segC6_raw σ ws.length sv qv siv civ ws lp (countsList (ws.take i))
      ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhCellH),
        (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) na (na + 2) ch)
  have h11 := stepFnIter_chain h10
    (stepFnIter_one (hg_var1 σ ws.length sv qv siv civ ws lp
      (countsList (ws.take i)) ((i : Nat) : Int) (ws.getD i 0) dead na
      (na + 2) _ ch hna hdead))
  have h12 := stepFnIter_chain h11
    (hg_segC7_raw σ ws.length sv qv siv civ ws lp (countsList (ws.take i))
      ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhCellH),
        (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) na (na + 2) ch)
  have h13 := stepFnIter_chain h12
    (stepFnIter_one (hg_var2 σ ws.length sv qv siv civ ws lp
      (countsList (ws.take i)) ((i : Nat) : Int) (ws.getD i 0) dead na
      (na + 2) _ ch hna hdead))
  have h14 := stepFnIter_chain h13
    (hg_segC8_raw σ ws.length sv qv siv civ ws lp (countsList (ws.take i))
      ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhCellH),
        (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) na (na + 2)
      (ws.getD i 0) ch)
  have h15 := stepFnIter_chain h14
    (stepFnIter_one (hg_var1 σ ws.length sv qv siv civ ws lp
      (countsList (ws.take i)) ((i : Nat) : Int) (ws.getD i 0) dead na
      (na + 2) _ ch hna hdead))
  have h16 := stepFnIter_chain h15
    (hg_segC9_raw σ ws.length sv qv siv civ ws lp (countsList (ws.take i))
      ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhCellH),
        (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) na (na + 2)
      (ws.getD i 0) ch)
  have h17 := stepFnIter_chain h16
    (stepFnIter_one (hg_var2 σ ws.length sv qv siv civ ws lp
      (countsList (ws.take i)) ((i : Nat) : Int) (ws.getD i 0) dead na
      (na + 2) _ ch hna hdead))
  have h18 := stepFnIter_chain h17
    (stepFnIter_one (stepFn_strict_apply
      (done := [.map ⟨some (.base ⟨21⟩)⟩])
      (hg_mapGet σ ws.length sv qv siv civ ws lp (countsList (ws.take i))
        ((i : Nat) : Int)
        (dead ++ [(.base ⟨na⟩, mhCellH),
          (.base ⟨na + 1⟩, u64cell (ws.getD i 0))])
        (na + 2) (ws.getD i 0) hw.1 hw.2)))
  have h19 := stepFnIter_chain h18
    (hg_segC10_raw σ ws.length sv qv siv civ ws lp (countsList (ws.take i))
      ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhCellH),
        (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) na (na + 2)
      (ws.getD i 0)
      ((cnt (countsList (ws.take i)) (ws.getD i 0) : Nat) : Int) ch)
  have hcast : ((cnt (countsList (ws.take i)) (ws.getD i 0) : Nat) : Int) + 1
      = ((cnt (countsList (ws.take i)) (ws.getD i 0) + 1 : Nat) : Int) := by
    omega
  have hnorm1 : IntKind.normalize .uint64
      ((cnt (countsList (ws.take i)) (ws.getD i 0) + 1 : Nat) : Int)
      = ((cnt (countsList (ws.take i)) (ws.getD i 0) + 1 : Nat) : Int) := by
    refine GoLean.SliceMem.unorm_of_range (by omega) ?_
    exact_mod_cast hcnt
  rw [hcast, hnorm1] at h19
  have h20 := stepFnIter_chain h19
    (stepFnIter_one (hg_mapAsgn σ ws.length sv qv siv civ ws lp
      (countsList (ws.take i)) ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhCellH),
        (.base ⟨na + 1⟩, u64cell (ws.getD i 0))])
      na (na + 2) (ws.getD i 0)
      (cnt (countsList (ws.take i)) (ws.getD i 0) + 1) ch hw.1 hw.2 hcnt))
  have h21 := stepFnIter_chain h20
    (hg_segC11_raw σ ws.length sv qv siv civ ws lp
      (setk (countsList (ws.take i)) (ws.getD i 0)
        (cnt (countsList (ws.take i)) (ws.getD i 0) + 1))
      ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhCellH),
        (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) na (na + 2) ch)
  rw [show setk (countsList (ws.take i)) (ws.getD i 0)
      (cnt (countsList (ws.take i)) (ws.getD i 0) + 1)
      = countsList (ws.take (i + 1)) from by
    rw [setk_cnt_succ, ← countsList_append_value,
      ← take_succ_getD hi]] at h21
  exact h21

/-! ## The counting loop + exit -/

/-- **The counting loop and its exit** (strong induction on the
remaining value count `m = len vals − i`): from the exit-test delivery
at value `i`, the run folds the remaining values and lands on the
`hits := counts[q]` head within `84·m + 9` steps, with exactly the
`2·m` per-iteration scratch cells appended (the exit itself allocates
nothing — the `hits` cell is the next shard's first step). -/
theorem hg_count_loop (σ : ExecState) (sv qv siv civ : Int)
    (ws lp : List Int)
    (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64) (hlen : ws.length < 2 ^ 63) :
    ∀ (m i : Nat), m = ws.length - i → i ≤ ws.length →
    ∀ (dead : Heap) (na : Nat), 25 ≤ na → DeadFrom dead na →
    ∀ ch : Choices,
    ∃ (k : Nat) (tail : Heap),
      k ≤ 84 * m + 9
      ∧ DeadFrom tail (na + 2 * m)
      ∧ stepFnIter k
          (σH σ ws.length sv qv siv civ ws lp (countsList (ws.take i))
            (i : Int) false dead na)
          (.retV (.bool (decide ((i : Int) < (ws.length : Int)))) cmpContCH)
          ch
        = .ok (.exec (.initialization { id := "hits", typ := tU64 }) envR0H
              (.seq [.assign (.var "hits")
                  (.mapGet (.var "counts") (.var "q") tU64 tU64),
                distinctSeqn, hMapRangeStmt, hRetSeqn] envR0H frameKH),
            σH σ ws.length sv qv siv civ ws lp (countsList ws)
              ((ws.length : Nat) : Int) false tail (na + 2 * m), ch) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro i hm hi dead na hna hdead ch
    rcases Nat.lt_or_ge i ws.length with hlt | hge
    · -- iterate
      rw [show (decide (((i : Nat) : Int) < (ws.length : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      have hIt := hg_count_iter σ sv qv siv civ ws lp i dead na ch hws hlen
        hlt hna hdead
      have hdead₂ : DeadFrom (dead ++ [(.base ⟨na⟩, mhCellH),
          (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2) :=
        DeadFrom.push2 hdead
      have hA1' := hg_segA1_raw σ ws.length sv qv siv civ ws lp
        (countsList (ws.take (i + 1))) ((i : Nat) : Int)
        (dead ++ [(.base ⟨na⟩, mhCellH),
          (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2) ch
      rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
        GoLean.SliceMem.inorm_nat_of_lt (by omega : i + 1 < 2 ^ 63),
        GoLean.SliceMem.inorm_nat_of_lt (by omega : i + 1 < 2 ^ 63)] at hA1'
      have hLen := stepFnIter_one
        (stepFn_strict_apply (done := []) (env := env2H)
          (k := .strictK .lessCmp [.int ((i + 1 : Nat) : Int) .int] [] env2H
            cmpContCH)
          (ch := ch)
          (GoLean.SliceMem.applyStrictOp_len_slice
            (σ := σH σ ws.length sv qv siv civ ws lp
              (countsList (ws.take (i + 1))) ((i + 1 : Nat) : Int) false
              (dead ++ [(.base ⟨na⟩, mhCellH),
                (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2))
            (b := .base ⟨7⟩) (off := 0) (len := ws.length)
            (cap := ws.length) (elem := tU64) (Nat.le_refl _)))
      have hCmp := stepFnIter_one
        (stepFn_strict_apply
          (done := [.int ((i + 1 : Nat) : Int) .int]) (env := env2H)
          (k := cmpContCH) (ch := ch)
          (GoLean.SliceMem.applyStrictOp_lessCmp_int
            (σ := σH σ ws.length sv qv siv civ ws lp
              (countsList (ws.take (i + 1))) ((i + 1 : Nat) : Int) false
              (dead ++ [(.base ⟨na⟩, mhCellH),
                (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2))
            (a := ((i + 1 : Nat) : Int)) (b := ((ws.length : Nat) : Int))
            (k := .int) (k' := .int)))
      obtain ⟨k, tail, hk, htail, hrun⟩ := ih (m - 1) (by omega)
        (i + 1) (by omega) (by omega)
        (dead ++ [(.base ⟨na⟩, mhCellH),
          (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2)
        (by omega) hdead₂ ch
      refine ⟨53 + 29 + 1 + 1 + k, tail, by omega, ?_, ?_⟩
      · rw [show na + 2 * m = na + 2 + 2 * (m - 1) from by omega]
        exact htail
      · rw [show na + 2 * m = na + 2 + 2 * (m - 1) from by omega]
        exact stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hIt hA1')
            hLen) hCmp) hrun
    · -- exit: i = ws.length, m = 0
      have hiL : i = ws.length := by omega
      subst hiL
      have hm0 : m = 0 := by omega
      subst hm0
      rw [show (decide (((ws.length : Nat) : Int) < ((ws.length : Nat) : Int)))
          = false from decide_eq_false (by omega)]
      have hX := hg_segX0_raw σ ws.length sv qv siv civ ws lp
        (countsList (ws.take ws.length)) ((ws.length : Nat) : Int) dead na ch
      refine ⟨9, dead, by omega, ?_, ?_⟩
      · intro x hx
        exact hdead x (by omega)
      · simpa using hX

end GoLean.Examples.Histogram
