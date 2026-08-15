import GoLeanProofs.MapLoops
import GoLeanProofs.Examples.Histogram.Machine

/-!
# Histogram — CountLoop

The COUNTING-LOOP half of the `histogram` run proof: from the exit-test
delivery at value `i` (`.retV (.bool (decide (i < len vals)))
cmpContCH`), the run folds every value into the counts map and exits
into the `hits := counts[q]` head, in at most `84·m + 9` steps
(`m = len vals − i`), allocating exactly the two per-iteration scratch
cells (`$c1` at `na`, `$c2` at `na + 1`).

## Kit gaps closed here (campaign log `g1.md`)

**GAP-C1 CLOSED** (kit-gap closure, 2026-08-15): the whole re-derived
tower this module carried — the conditioned discharges, the composed
53-step iteration and the loop induction — is DELETED. What remains
per this placement is exactly what cannot be generic: the raw `rfl`
segments (this program's own step transcriptions), the nine placement
facts (all `rfl` but the front-freshness lemma), the
`mapCountIter_at`/`mapCountLoop_generic` instantiations, and the
9-step exit (histogram's exit allocates nothing, unlike wordcount's —
which is why the kit loop deliberately ends at the exit test's `false`
delivery). The storm-avoidance discipline is unchanged — every
statement is over the abstract state family `σH σ L sv qv siv civ ws
lp kvs iv ff dead na`, and no concrete 25-cell front ever reaches the
unifier inside a composition step.

(GAP-P1 CLOSED, kit-gap closure 2026-08-15: the `take_succ_getD` /
`cnt_take_le` / `nilMapCell` re-derivations this module carried are
deleted — the kit forms live in `GoLeanProofs/MapMem.lean`.)
-/

namespace GoLean.Examples.Histogram

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem
open GoLean.MapMem
open GoLean.MapLoops

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

-- (`nilMapCell`, `take_succ_getD`, `cnt_take_le` are the kit's, via
-- `open GoLean.MapMem` — the local copies were deleted in the GAP-P1
-- closure.)

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

/-! ## The placement facts

GAP-C1 CLOSED (kit-gap closure, 2026-08-15): the conditioned
discharges this module re-derived (`hg_init1`/`hg_st1`/`hg_init2`/
`hg_st2`/`hg_lk1`/`hg_lk2`/`hg_var1`/`hg_var2`/`hg_read`/`hg_mapGet`/
`hg_mapAsgn`, ~270 lines) are DELETED — the kit's
`MapLoops.mapCountIter_at` constructs them from nine placement facts,
every one a `rfl` here except the front-freshness lemma
(`lookup_frontH_none`, in `Histogram.Machine`). -/

/-! ## One counting iteration, composed -/

/-- **One counting iteration** from the exit test's true delivery at
value `i`: `counts[vals[i]]++` in 53 steps, `$c1`/`$c2` materialized at
`na`/`na + 1`, the counts fold advanced one value — via the kit's
bundled `MapLoops.mapCountIter_at` (GAP-C1 closure, 2026-08-15). -/
theorem hg_count_iter (σ : ExecState) (sv qv siv civ : Int)
    (ws lp : List Int) (i : Nat) (dead : Heap) (na : Nat) (ch : Choices)
    (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64) (hlen : ws.length < 2 ^ 63)
    (hi : i < ws.length) (hna : 25 ≤ na) (hdead : DeadFrom dead na) :
    stepFnIter 53
      (σH σ ws.length sv qv siv civ ws lp (countsFold (ws.take i)) (i : Int)
        false dead na)
      (.retV (.bool true) cmpContCH) ch
      = .ok (headCH,
          σH σ ws.length sv qv siv civ ws lp (countsFold (ws.take (i + 1)))
            (i : Int) false
            (dead ++ [(.base ⟨na⟩, mhCellH),
              (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2), ch) := by
  have hw := hws (ws.getD i 0) (getD_mem hi)
  have hcnt : cnt (countsFold (ws.take i)) (ws.getD i 0) + 1 < 2 ^ 64 := by
    have := cnt_take_le (ws := ws) (i := i) (ws.getD i 0)
    omega
  have h := mapCountIter_at "vals" (σH σ ws.length sv qv siv civ ws lp) σ
    (fun kvs iv => frontH ws.length sv qv siv civ ws lp kvs iv false)
    ws 7 21 25 headCH cmpContCH postBodyKH env3H u1EnvH uEnvH
    (fun _ _ _ _ => rfl)
    (fun kvs iv x hx =>
      lookup_frontH_none ws.length sv qv siv civ ws lp kvs iv false hx)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun kvs iv dead na ch =>
      hg_segC1_raw σ ws.length sv qv siv civ ws lp kvs iv dead na ch)
    (fun kvs iv dead na₀ na ch =>
      hg_segC2_raw σ ws.length sv qv siv civ ws lp kvs iv dead na₀ na ch)
    (fun kvs iv dead na₀ na ch =>
      hg_segC3_raw σ ws.length sv qv siv civ ws lp kvs iv dead na₀ na ch)
    (fun kvs iv dead na₀ na ch =>
      hg_segC4_raw σ ws.length sv qv siv civ ws lp kvs iv dead na₀ na ch)
    (fun kvs iv dead na₀ na w ch =>
      hg_segC5_raw σ ws.length sv qv siv civ ws lp kvs iv dead na₀ na w ch)
    (fun kvs iv dead na₀ na ch =>
      hg_segC6_raw σ ws.length sv qv siv civ ws lp kvs iv dead na₀ na ch)
    (fun kvs iv dead na₀ na ch =>
      hg_segC7_raw σ ws.length sv qv siv civ ws lp kvs iv dead na₀ na ch)
    (fun kvs iv dead na₀ na w ch =>
      hg_segC8_raw σ ws.length sv qv siv civ ws lp kvs iv dead na₀ na w ch)
    (fun kvs iv dead na₀ na w ch =>
      hg_segC9_raw σ ws.length sv qv siv civ ws lp kvs iv dead na₀ na w ch)
    (fun kvs iv dead na₀ na w cv ch =>
      hg_segC10_raw σ ws.length sv qv siv civ ws lp kvs iv dead na₀ na w cv
        ch)
    (fun kvs iv dead na₀ na ch =>
      hg_segC11_raw σ ws.length sv qv siv civ ws lp kvs iv dead na₀ na ch)
    (countsFold (ws.take i)) i dead na ch hi hw.1 hw.2 hcnt hna hdead
  rw [show setk (countsFold (ws.take i)) (ws.getD i 0)
      (cnt (countsFold (ws.take i)) (ws.getD i 0) + 1)
      = countsFold (ws.take (i + 1)) from by
    rw [setk_cnt_succ, ← countsFold_append,
      ← take_succ_getD hi]] at h
  exact h

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
          (σH σ ws.length sv qv siv civ ws lp (countsFold (ws.take i))
            (i : Int) false dead na)
          (.retV (.bool (decide ((i : Int) < (ws.length : Int)))) cmpContCH)
          ch
        = .ok (.exec (.initialization { id := "hits", typ := tU64 }) envR0H
              (.seq [.assign (.var "hits")
                  (.mapGet (.var "counts") (.var "q") tU64 tU64),
                distinctSeqn, hMapRangeStmt, hRetSeqn] envR0H frameKH),
            σH σ ws.length sv qv siv civ ws lp (countsFold ws)
              ((ws.length : Nat) : Int) false tail (na + 2 * m), ch) := by
  intro m i hm hi dead na hna hdead ch
  obtain ⟨tail, htail, hrun⟩ :=
    mapCountLoop_generic (σH σ ws.length sv qv siv civ ws lp) ws 7 21 25
      headCH cmpContCH env2H hlen
      (fun i dead na ch hi hna hdead =>
        hg_count_iter σ sv qv siv civ ws lp i dead na ch hws hlen hi hna
          hdead)
      (fun kvs iv dead na ch =>
        hg_segA1_raw σ ws.length sv qv siv civ ws lp kvs iv dead na ch)
      m i hm hi dead na hna hdead ch
  have hX := hg_segX0_raw σ ws.length sv qv siv civ ws lp (countsFold ws)
    ((ws.length : Nat) : Int) tail (na + 2 * m) ch
  exact ⟨84 * m + 9, tail, Nat.le_refl _, htail, stepFnIter_chain hrun hX⟩

end GoLean.Examples.Histogram
