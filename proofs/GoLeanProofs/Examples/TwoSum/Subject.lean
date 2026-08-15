import GoLeanProofs.Examples.TwoSum.HarnessR

/-!
# TwoSum — the subject phase (the nested loop) and the end-to-end run

The `twoSum` double loop, from the outer loop head to the DRIVER
TERMINAL. The shape that makes this example's proof different from its
siblings:

* **The inner loop's cells live at SYMBOLIC addresses.** Each outer
  iteration allocates a fresh inner `j` and loop flag, so the heap
  grows by two dead cells per outer round. Every subject-phase segment
  is parameterized by the abstract dead region `D` (with
  `StepKit.DeadFrom` freshness) and the live-pair base address `ja`;
  raw `rfl` segments carry both opaquely (everything they RESOLVE is
  in the concrete front), and the per-iteration accesses to `j` and
  `$forFirst` go through conditioned kit steps.
* **The subject has an EARLY RETURN out of the INNER loop** — so, as
  in the array-palindrome exemplar, the inner analysis runs all the
  way to the driver terminal on the hit path, and the outer induction
  existentially forgets everything the return does not determine (the
  dead region, the final `nextAddr`, the outer counter's last value).
* **TWO inductions.** The inner loop's uniform miss iterations go
  through the P5 schema (`stepFnIter_iterate`, shifted to the row's
  start); the outer loop is a plain strong induction
  (`Nat.strongRecOn`), with the answer function `tsAnsF` carrying
  "first pair from row `t` on" through the recursion so no invariant
  needs threading.

Per-segment step counts (probe-measured, re-checked by `rfl`):

| phase | steps |
|---|---|
| outer dispatch (first pass) | 25 |
| outer body → `j` alloc + store | 9 + 1 + 10 + 1 |
| flag alloc + store → inner head | 5 + 1 + 6 + 1 + 3 |
| inner dispatch (first pass) | 25 |
| one inner miss iteration | 57 |
| inner hit: test → `retV true` at the found `if` | 23 |
| the found tail (return → terminal) | 78 |
| inner exit → next outer exit-test delivery | 38 |
| outer exit → the pending `$res0 = vals` store | 46 |
| the store + the epilogue tail | 1 + 24 |
-/

namespace GoLean.Examples.TwoSum

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## Pure glue -/

/-- Wrapped uint64 addition of two in-range values, in the spec's
`Int.emod` spelling. -/
theorem unorm_add_range {a b : Int} (ha : 0 ≤ a ∧ a < 2 ^ 64)
    (hb : 0 ≤ b ∧ b < 2 ^ 64) :
    IntKind.normalize .uint64 (a + b) = (a + b) % 2 ^ 64 := by
  rw [show a + b = ((a.toNat : Nat) : Int) + ((b.toNat : Nat) : Int) from
    by omega, unorm_add_nat]
  omega

/-- The answer from row `t` on: the machine induction's carried
value. -/
def tsAnsF (l : List Int) (tgt : Int) (t : Nat) : Nat × Nat :=
  match findPair l tgt t with
  | some p => p
  | none => (l.length, l.length)

theorem tsAnsF_exit {l : List Int} {tgt : Int} {t : Nat}
    (h : l.length ≤ t) : tsAnsF l tgt t = (l.length, l.length) := by
  rw [tsAnsF, findPair_end h]

theorem tsAnsF_hit {l : List Int} {tgt : Int} {t u : Nat}
    (ht : t < l.length) (h : findFrom l tgt t (t + 1) = some u) :
    tsAnsF l tgt t = (t, u) := by
  rw [tsAnsF, findPair_hit ht h]

theorem tsAnsF_miss {l : List Int} {tgt : Int} {t : Nat}
    (ht : t < l.length) (h : findFrom l tgt t (t + 1) = none) :
    tsAnsF l tgt t = tsAnsF l tgt (t + 1) := by
  rw [tsAnsF, findPair_step ht h, tsAnsF]

/-- `twoSumSpec` is `tsAnsF` at row 0, cast. -/
theorem twoSumSpec_eq_ansF (xs : List Int) (tgt : Int) :
    twoSumSpec xs tgt
      = (((tsAnsF xs tgt 0).1 : Int), ((tsAnsF xs tgt 0).2 : Int)) := by
  rw [twoSumSpec, tsAnsF]
  cases findPair xs tgt 0 with
  | none => rfl
  | some p => rfl

/-! ## Env-lookup facts at the symbolic live addresses -/

theorem env_inC_ff (ja : Nat) :
    LocalEnv.lookup (inEnvCT ja) "$forFirst" = some (.base ⟨ja + 1⟩) := rfl
theorem env_inC_j (ja : Nat) :
    LocalEnv.lookup (inEnvCT ja) "j" = some (.base ⟨ja⟩) := rfl
theorem env_inB2_j (ja : Nat) :
    LocalEnv.lookup (inEnvB2T ja) "j" = some (.base ⟨ja⟩) := rfl

/-- The found-block env (one more scope over the body pair). -/
def fEnvT (ja : Nat) : LocalEnv := [] :: inEnvB2T ja
/-- The found block's continuation (the inner `if`'s own). -/
def tFoundK (ja : Nat) : Cont :=
  .seq [] (inEnvB2T ja) (.seq [] (inEnvCT ja) (tInLoopK ja))

theorem env_f_j (ja : Nat) :
    LocalEnv.lookup (fEnvT ja) "j" = some (.base ⟨ja⟩) := rfl

/-! ## Freshness / live-cell plumbing over the abstract dead region -/

/-- The outer front plus the dead region misses the fresh address. -/
theorem lookup_outD_none (nv sv tv : Int) (n : Nat) (l lp : List Int)
    (siv civ tvp mv iv : Int) (ffv : Bool) {D : Heap} {x : Nat}
    (hx : 23 ≤ x) (hD : Heap.lookup D (.base ⟨x⟩) = none) :
    Heap.lookup (tsHeapOut nv sv tv n l lp siv civ tvp mv iv ffv ++ D)
      (.base ⟨x⟩) = none := by
  rw [lookup_append_right (lookup_out_none nv sv tv n l lp siv civ tvp mv
    iv ffv hx), hD]

/-- Reading the solo `j` cell (the window between the two allocs). -/
theorem lookup_soloJ (nv sv tv : Int) (n : Nat) (l lp : List Int)
    (siv civ tvp mv iv : Int) (D : Heap) (ja : Nat) (jv : Int)
    (hja : 23 ≤ ja) (hD : DeadFrom D ja) :
    Heap.lookup (tsHeapOut nv sv tv n l lp siv civ tvp mv iv false
        ++ (D ++ [(.base ⟨ja⟩, tsu64 jv)])) (.base ⟨ja⟩)
      = some (tsu64 jv) := by
  rw [lookup_append_right (lookup_out_none nv sv tv n l lp siv civ tvp mv
    iv false hja), lookup_append_right (hD ja (Nat.le_refl _))]
  exact lookup_singleton_self

/-- Writing the solo `j` cell. -/
theorem set_soloJ (nv sv tv : Int) (n : Nat) (l lp : List Int)
    (siv civ tvp mv iv : Int) (D : Heap) (ja : Nat) (jv jv' : Int)
    (hja : 23 ≤ ja) (hD : DeadFrom D ja) :
    Heap.set (tsHeapOut nv sv tv n l lp siv civ tvp mv iv false
        ++ (D ++ [(.base ⟨ja⟩, tsu64 jv)])) (.base ⟨ja⟩) (tsu64 jv')
      = tsHeapOut nv sv tv n l lp siv civ tvp mv iv false
          ++ (D ++ [(.base ⟨ja⟩, tsu64 jv')]) := by
  rw [set_append_right (lookup_out_none nv sv tv n l lp siv civ tvp mv
    iv false hja), set_append_right (hD ja (Nat.le_refl _)),
    set_singleton_self]

/-- The front of the post-return state misses any address ≥ 23. -/
theorem lookup_ret_none (nv sv tv : Int) (n : Nat) (l lp : List Int)
    (siv civ tvp mv iv riv rjv : Int) {x : Nat} (hx : 23 ≤ x) :
    Heap.lookup (tsHeapRet nv sv tv n l lp siv civ tvp mv iv riv rjv)
      (.base ⟨x⟩) = none := by
  simp only [tsHeapRet, tsHeapCall, tsHeapCp, tsHeapSu,
    tsHeap0, List.append_assoc, List.cons_append, List.nil_append]
  rw [lookup_cons_ne (base_beq_false (show 0 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 1 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 2 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 3 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 4 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 5 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 6 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 7 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 8 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 9 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 10 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 11 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 12 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 13 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 14 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 15 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 16 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 17 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 18 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 19 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 20 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 21 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 22 ≠ x by omega))]
  rfl

/-- Reading the live `j` through the dead region, post-return front. -/
theorem lookup_retD_j (nv sv tv : Int) (n : Nat) (l lp : List Int)
    (siv civ tvp mv iv riv rjv : Int) (D : Heap) (ja : Nat) (jv : Int)
    (ffv : Bool) (hja : 23 ≤ ja) (hD : DeadFrom D ja) :
    Heap.lookup (tsHeapRet nv sv tv n l lp siv civ tvp mv iv riv rjv
        ++ (D ++ tsLive ja jv ffv)) (.base ⟨ja⟩)
      = some (tsu64 jv) := by
  rw [lookup_append_right (lookup_ret_none nv sv tv n l lp siv civ tvp mv
    iv riv rjv hja), lookup_append_right (hD ja (Nat.le_refl _))]
  simp [tsLive, Heap.lookup]

/-! ## Raw run segments — subject phase -/

/-- Outer dispatch, first pass: head → the exit-test delivery.
25 steps. -/
theorem t_oDisp_raw (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv : Int) (D : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 25
      (tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp mv iv true ++ D) na)
      tOutHeadCfg ch
      = .ok (.retV (.bool (decide (iv < mv))) tOutCmpK,
          tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp mv iv false ++ D)
            na, ch) := by
  with_unfolding_all rfl

/-- Outer body start → the inner `j` initialization. 9 steps,
control-only (fully abstract state). -/
theorem t_oB1_raw (σ : ExecState) (ch : Choices) :
    stepFnIter 9 σ (.retV (.bool true) tOutCmpK) ch
      = .ok (.exec (.initialization { id := "j", typ := tU64 }) bodyEnvT
          (.seq [tJAssign, tInnerLoopBlock] bodyEnvT tJSeqTail), σ, ch) := by
  with_unfolding_all rfl

/-- `j := i + 1` up to the store point. 10 steps; reads the outer
counter from the concrete front. -/
theorem t_jAssign_raw (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv : Int) (Dj : Heap) (ja : Nat)
    (na : Nat) (ch : Choices) :
    stepFnIter 10
      (tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp mv iv false ++ Dj) na)
      (.next (.seq [tJAssign, tInnerLoopBlock] (jEnvT ja) tJSeqTail)) ch
      = .ok (.next (.storeK [tJRef ja]
            [.int (IntKind.normalize .uint64 (iv + 1)) .uint64]
            (.seqn #[]) (jEnvT ja)
            (.seq [tInnerLoopBlock] (jEnvT ja) tJSeqTail)),
          tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp mv iv false ++ Dj)
            na, ch) := by
  with_unfolding_all rfl

/-- The inner block descent after the `j` store: drained store → the
flag initialization. Control-only single step for the block. -/
theorem t_blockIn_raw (σ : ExecState) (ja : Nat) (ch : Choices) :
    stepFn σ (.exec tInnerLoopBlock (jEnvT ja)
        (.seq [] (jEnvT ja) tJSeqTail)) ch
      = .ok (.next (.seq [.initialization { id := "$forFirst", typ := .bool },
            .assign (.var "$forFirst") (.boolLit true),
            .while (.boolLit true) twoSumFunc.innerBody]
          ([] :: jEnvT ja) (.seq [] (jEnvT ja) tJSeqTail)), σ, ch) := by
  with_unfolding_all rfl

/-- `$forFirst := true` up to the store point. 6 steps, control-only. -/
theorem t_ffAssign_raw (σ : ExecState) (ja : Nat) (ch : Choices) :
    stepFnIter 6 σ
      (.next (.seq [.assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) twoSumFunc.innerBody]
        (inEnvT ja) (.seq [] (jEnvT ja) tJSeqTail))) ch
      = .ok (.next (.storeK [tFFRef ja] [.bool true] (.seqn #[])
            (inEnvT ja)
            (.seq [.while (.boolLit true) twoSumFunc.innerBody]
              (inEnvT ja) (.seq [] (jEnvT ja) tJSeqTail))), σ, ch) := by
  with_unfolding_all rfl

/-- Inner head → the flag read. 6 steps, control-only. -/
theorem t_iH_raw (σ : ExecState) (ja : Nat) (ch : Choices) :
    stepFnIter 6 σ (tInHeadCfg ja) ch
      = .ok (.evalE (.var "$forFirst") (inEnvCT ja) (tFFIfK ja),
          σ, ch) := by
  with_unfolding_all rfl

/-- First pass: flag true → the `$forFirst := false` store point.
6 steps, control-only. -/
theorem t_iFFT_raw (σ : ExecState) (ja : Nat) (ch : Choices) :
    stepFnIter 6 σ (.retV (.bool true) (tFFIfK ja)) ch
      = .ok (.next (.storeK [tFFRef ja] [.bool false] (.seqn #[])
            (inEnvCT ja) (tInBodyTail ja)), σ, ch) := by
  with_unfolding_all rfl

/-- Later pass: flag false → the `j++` read. 5 steps, control-only. -/
theorem t_iFFF_raw (σ : ExecState) (ja : Nat) (ch : Choices) :
    stepFnIter 5 σ (.retV (.bool false) (tFFIfK ja)) ch
      = .ok (.evalE (.var "j") (inEnvCT ja) (tJIncrK ja), σ, ch) := by
  with_unfolding_all rfl

/-- The `j + 1` computation after the read. 4 steps, control-only. -/
theorem t_iIncr_raw (σ : ExecState) (ja : Nat) (jv : Int)
    (ch : Choices) :
    stepFnIter 4 σ (.retV (.int jv .uint64) (tJIncrK ja)) ch
      = .ok (.next (.storeK [tJRef ja]
            [.int (IntKind.normalize .uint64 (jv + 1)) .uint64]
            (.seqn #[]) (inEnvCT ja) (tInBodyTail ja)), σ, ch) := by
  with_unfolding_all rfl

/-- The exit test's `if` + `<` push (after the two body splices).
2 steps, control-only. -/
theorem t_iIfPush_raw (σ : ExecState) (ja : Nat) (ch : Choices) :
    stepFnIter 2 σ
      (.exec tIfJN (inEnvCT ja)
        (.seq [twoSumFunc.matchBlock] (inEnvCT ja) (tInLoopK ja))) ch
      = .ok (.evalE (.var "j") (inEnvCT ja) (tJTestK ja), σ, ch) := by
  with_unfolding_all rfl

/-- The exit test's completion: `j` delivered → `n` read (concrete
front) → the comparison verdict. 3 steps. -/
theorem t_iTest_raw (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv : Int) (D : Heap) (ja : Nat)
    (jv jv' : Int) (ffv : Bool) (na : Nat) (ch : Choices) :
    stepFnIter 3
      (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv' ffv) na)
      (.retV (.int jv .uint64) (tJTestK ja)) ch
      = .ok (.retV (.bool (decide (jv < mv))) (tInCmpK ja),
          tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv' ffv)
            na, ch) := by
  with_unfolding_all rfl

/-- Body: the inner `if` at the pair test → the `s[i]` apply point.
7 steps; reads `s` and `i` from the concrete front. -/
theorem t_bodyB_raw (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv : Int) (D : Heap) (ja : Nat)
    (jv : Int) (na : Nat) (ch : Choices) :
    stepFnIter 7
      (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv false) na)
      (.exec (.ifThenElse
          (.eqCmp tU64
            (.add (.indexGet (.var "s") (.var "i"))
                  (.indexGet (.var "s") (.var "j")))
            (.var "target"))
          twoSumFunc.foundBlock (.seqn #[])) (inEnvB2T ja)
        (tFoundK ja)) ch
      = .ok (.retV (.int iv .uint64) (tIdx1K n ja),
          tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv false)
            na, ch) := by
  with_unfolding_all rfl

/-- Body: `s[i]` banked → the second index's `j` read. 4 steps. -/
theorem t_bodyC_raw (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv : Int) (D : Heap) (ja : Nat)
    (jv a : Int) (na : Nat) (ch : Choices) :
    stepFnIter 4
      (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv false) na)
      (.retV (.int a .uint64)
        (.strictK .add [] [.indexGet (.var "s") (.var "j")] (inEnvB2T ja)
          (.strictK (.eqCmp tU64) [] [.var "target"] (inEnvB2T ja)
            (tInIfK ja)))) ch
      = .ok (.evalE (.var "j") (inEnvB2T ja) (tIdx2K n ja a),
          tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv false)
            na, ch) := by
  with_unfolding_all rfl

/-- Body: both elements banked → the wrapped sum against `target`.
4 steps; reads `target` from the concrete front (cell 17 = `tvp`). -/
theorem t_bodyD_raw (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv : Int) (D : Heap) (ja : Nat)
    (jv a b : Int) (na : Nat) (ch : Choices) :
    stepFnIter 4
      (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv false) na)
      (.retV (.int b .uint64)
        (.strictK .add [.int a .uint64] [] (inEnvB2T ja)
          (.strictK (.eqCmp tU64) [] [.var "target"] (inEnvB2T ja)
            (tInIfK ja)))) ch
      = .ok (.retV (.bool ((IntKind.normalize .uint64 (a + b)) == tvp))
            (tInIfK ja),
          tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv false)
            na, ch) := by
  with_unfolding_all rfl

/-- Miss: the pair test false → back at the inner loop head (after the
one splice). 3 steps, control-only. -/
theorem t_missTail_raw (σ : ExecState) (ja : Nat) (ch : Choices) :
    stepFnIter 3 σ
      (.next (.seq [] (inEnvB2T ja)
        (.seq [] (inEnvCT ja) (tInLoopK ja)))) ch
      = .ok (tInHeadCfg ja, σ, ch) := by
  with_unfolding_all rfl

/-- Inner exit: test false → break out, the outer `i++` dispatch, the
next outer exit-test delivery. 38 steps; every access is in the
concrete front. -/
theorem t_oX_raw (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv : Int) (D2 : Heap) (ja : Nat)
    (na : Nat) (ch : Choices) :
    stepFnIter 38
      (tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp mv iv false ++ D2) na)
      (.retV (.bool false) (tInCmpK ja)) ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < mv))) tOutCmpK,
          tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp mv
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false ++ D2) na, ch) := by
  with_unfolding_all rfl

/-! ### The found tail (the early return) -/

/-- Found: test true → the found block's statement list. 3 steps,
control-only. -/
theorem t_fA_raw (σ : ExecState) (ja : Nat) (ch : Choices) :
    stepFnIter 3 σ (.retV (.bool true) (tInIfK ja)) ch
      = .ok (.exec (.seqn #[.assign (.var "$res0") (.var "i"),
            .assign (.var "$res1") (.var "j"), .returnStmt])
          (fEnvT ja) (.seq [] (fEnvT ja) (tFoundK ja)), σ, ch) := by
  with_unfolding_all rfl

/-- Found: `$res0 := i` (front store into cell 18). 8 steps. -/
theorem t_fB_raw (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv : Int) (Din : Heap) (ja : Nat)
    (na : Nat) (ch : Choices) :
    stepFnIter 8
      (tSt σ (tsHeapRet nv sv tv n l lp siv civ tvp mv iv 0 0 ++ Din) na)
      (.next (.seq [.assign (.var "$res0") (.var "i"),
          .assign (.var "$res1") (.var "j"), .returnStmt]
        (fEnvT ja) (tFoundK ja))) ch
      = .ok (.exec (.seqn #[]) (fEnvT ja)
            (.seq [.assign (.var "$res1") (.var "j"), .returnStmt]
              (fEnvT ja) (tFoundK ja)),
          tSt σ (tsHeapRet nv sv tv n l lp siv civ tvp mv iv
            (IntKind.normalize .uint64 iv) 0 ++ Din) na, ch) := by
  with_unfolding_all rfl

/-- Found: pop to the `$res1 := j` read. 4 steps, control-only. -/
theorem t_fC_raw (σ : ExecState) (ja : Nat) (ch : Choices) :
    stepFnIter 4 σ
      (.next (.seq [.assign (.var "$res1") (.var "j"), .returnStmt]
        (fEnvT ja) (tFoundK ja))) ch
      = .ok (.evalE (.var "j") (fEnvT ja)
          (.rhsK .vals [.chain (.addr (.base ⟨19⟩)) [] []] [] []
            (.seqn #[]) (fEnvT ja)
            (.seq [.returnStmt] (fEnvT ja) (tFoundK ja))), σ, ch) := by
  with_unfolding_all rfl

/-- Found: `$res1 := j` store (front cell 19) + drain. 3 steps. -/
theorem t_fD1_raw (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv riv : Int) (Din : Heap)
    (ja : Nat) (jv : Int) (na : Nat) (ch : Choices) :
    stepFnIter 3
      (tSt σ (tsHeapRet nv sv tv n l lp siv civ tvp mv iv riv 0 ++ Din) na)
      (.retV (.int jv .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨19⟩)) [] []] [] []
          (.seqn #[]) (fEnvT ja)
          (.seq [.returnStmt] (fEnvT ja) (tFoundK ja)))) ch
      = .ok (.exec (.seqn #[]) (fEnvT ja)
            (.seq [.returnStmt] (fEnvT ja) (tFoundK ja)),
          tSt σ (tsHeapRet nv sv tv n l lp siv civ tvp mv iv riv
            (IntKind.normalize .uint64 jv) ++ Din) na, ch) := by
  with_unfolding_all rfl

/-- Found: the return through BOTH loop continuations and the frame
exit — the receiver refs evaluated, the result cells read (front).
19 steps. -/
theorem t_fE_raw (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv riv rjv : Int) (Din : Heap)
    (ja : Nat) (na : Nat) (ch : Choices) :
    stepFnIter 19
      (tSt σ (tsHeapRet nv sv tv n l lp siv civ tvp mv iv riv rjv ++ Din)
        na)
      (.next (.seq [.returnStmt] (fEnvT ja) (tFoundK ja))) ch
      = .ok (.next (.storeK
            [.chain (.addr (.base ⟨14⟩)) [] [],
             .chain (.addr (.base ⟨15⟩)) [] []]
            [.int riv .uint64, .int rjv .uint64]
            (.seqn #[]) callEnvT tAfterCall),
          tSt σ (tsHeapRet nv sv tv n l lp siv civ tvp mv iv riv rjv
            ++ Din) na, ch) := by
  with_unfolding_all rfl

/-- The receiver stores (front cells 14/15) and the walk to the
pending `$res0 = vals` array store. 12 steps. -/
theorem t_fF_raw (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv riv rjv : Int) (Din : Heap)
    (na : Nat) (ch : Choices) :
    stepFnIter 12
      (tSt σ (tsHeapRet nv sv tv n l lp siv civ tvp mv iv riv rjv ++ Din)
        na)
      (.next (.storeK
        [.chain (.addr (.base ⟨14⟩)) [] [],
         .chain (.addr (.base ⟨15⟩)) [] []]
        [.int riv .uint64, .int rjv .uint64]
        (.seqn #[]) callEnvT tAfterCall)) ch
      = .ok (.next (.storeK [tRes0Ref]
            [.array ⟨lp.map (fun v => .int v .uint64)⟩] (.seqn #[])
            callEnvT tEpiTail),
          tSt σ (tsHeapEpi nv sv tv n l lp siv civ tvp mv iv riv rjv
            (IntKind.normalize .uint64 riv)
            (IntKind.normalize .uint64 rjv) ++ Din) na, ch) := by
  with_unfolding_all rfl

/-! ### The sentinel tail (no pair) -/

/-- Outer exit: test false → break, `$res0/$res1 := n`, the frame
exit, the receiver stores, the walk to the pending array store.
46 steps; every access is in the concrete front. -/
theorem t_mX1_raw (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv : Int) (D2 : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 46
      (tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp mv iv false ++ D2) na)
      (.retV (.bool false) tOutCmpK) ch
      = .ok (.next (.storeK [tRes0Ref]
            [.array ⟨lp.map (fun v => .int v .uint64)⟩] (.seqn #[])
            callEnvT tEpiTail),
          tSt σ (tsHeapEpi nv sv tv n l lp siv civ tvp mv iv
            (IntKind.normalize .uint64 mv)
            (IntKind.normalize .uint64 mv)
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 mv))
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 mv))
            ++ D2) na, ch) := by
  with_unfolding_all rfl

/-! ### The shared epilogue -/

/-- The `$res0 = vals` store's discharge: the pending array store on
the epilogue front. -/
theorem t_epiStore (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv riv rjv hiv hjv : Int)
    (Drest : Heap) (na : Nat) (hlp : lp.length = 8)
    (hlpr : ∀ v ∈ lp, 0 ≤ v ∧ v < 2 ^ 64) :
    storeTarget
        (tSt σ (tsHeapEpi nv sv tv n l lp siv civ tvp mv iv riv rjv hiv
          hjv ++ Drest) na)
        tRes0Ref (.array ⟨lp.map (fun v => .int v .uint64)⟩)
      = .ok (tSt σ (tsHeapEnd nv sv tv n l lp siv civ tvp mv iv riv rjv
          hiv hjv 0 0 ++ Drest) na) := by
  have hfront : Heap.lookup
      (tsHeapEpi nv sv tv n l lp siv civ tvp mv iv riv rjv hiv hjv)
      (.base ⟨3⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun v => .int v .uint64)⟩⟩ := by
    simp [tsHeapEpi, tsHeapCp, tsHeapSu, tsHeap0, Heap.lookup]
  have hlook : Heap.lookup
      (tSt σ (tsHeapEpi nv sv tv n l lp siv civ tvp mv iv riv rjv hiv hjv
        ++ Drest) na).heap (.base ⟨3⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun v => .int v .uint64)⟩⟩ :=
    lookup_append_left hfront
  have hst := storeTarget_addr hlook
    (GoLean.SliceMem.normalizeValueForTy_arr_u64 (N := 8) hlp hlpr)
  simp only [tRes0Ref]
  rw [hst]
  have hset : Heap.set
      (tsHeapEpi nv sv tv n l lp siv civ tvp mv iv riv rjv hiv hjv
        ++ Drest) (.base ⟨3⟩)
      ⟨some (.array 8 tU64), .array ⟨lp.map (fun v => .int v .uint64)⟩⟩
      = tsHeapEnd nv sv tv n l lp siv civ tvp mv iv riv rjv hiv hjv 0 0
          ++ Drest := by
    rw [set_append_left hfront]
    with_unfolding_all rfl
  rw [hset]

/-- The epilogue tail: `$res1 := i`, `$res2 := j`, return, barrier
exit — the driver terminal. 24 steps. -/
theorem t_epi_raw (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv riv rjv hiv hjv : Int)
    (Drest : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 24
      (tSt σ (tsHeapEnd nv sv tv n l lp siv civ tvp mv iv riv rjv hiv hjv
        0 0 ++ Drest) na)
      (.next (.storeK [] [] (.seqn #[]) callEnvT tEpiTail)) ch
      = .ok (.next .stop,
          tSt σ (tsHeapEnd nv sv tv n l lp siv civ tvp mv iv riv rjv hiv
            hjv (IntKind.normalize .uint64 hiv)
            (IntKind.normalize .uint64 hjv) ++ Drest) na, ch) := by
  with_unfolding_all rfl

/-! ### Micro-steps (single conditioned/control steps the composites
chain between the raw spans) -/

theorem def_u64 (σ : ExecState) :
    defaultValue σ tU64 = .ok (.int 0 .uint64) := by with_unfolding_all rfl
theorem def_bool (σ : ExecState) :
    defaultValue σ .bool = .ok (.bool false) := by with_unfolding_all rfl
theorem norm_u64_scalar (σ : ExecState) (v : Int) :
    normalizeValueForTy σ tU64 (.int v .uint64)
      = .ok (.int (IntKind.normalize .uint64 v) .uint64) := by
  with_unfolding_all rfl
theorem norm_bool_val (σ : ExecState) (b : Bool) :
    normalizeValueForTy σ .bool (.bool b) = .ok (.bool b) := by
  with_unfolding_all rfl

/-- Store into the live `j` cell, at the state level (norms collapsed). -/
theorem storeJ_liveT (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv : Int) (D : Heap) (ja : Nat)
    (jv w : Int) (ffv : Bool) (na' : Nat) (hw1 : 0 ≤ w) (hw2 : w < 2 ^ 64)
    (hja : 23 ≤ ja) (hD : DeadFrom D ja) :
    storeTarget
        (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv ffv)
          na') (tJRef ja) (.int w .uint64)
      = .ok (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja w ffv)
          na') := by
  have hn := norm_u64_scalar
    (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv ffv) na') w
  rw [unorm_of_range hw1 hw2] at hn
  rw [show tJRef ja = .chain (.addr (.base ⟨ja⟩)) [] [] from rfl,
    storeTarget_addr
      (show Heap.lookup (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv
          D ja jv ffv) na').heap (.base ⟨ja⟩)
          = some ⟨some tU64, .int jv .uint64⟩ from
        lookup_liveJ nv sv tv n l lp siv civ tvp mv iv D ja jv ffv hja hD)
      hn,
    show (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv ffv)
      na').heap = tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv ffv
      from rfl,
    set_liveJ nv sv tv n l lp siv civ tvp mv iv D ja jv w ffv hja hD]

/-- Store into the live flag cell, at the state level. -/
theorem storeFF_liveT (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv : Int) (D : Heap) (ja : Nat)
    (jv : Int) (ffv ffv' : Bool) (na' : Nat)
    (hja : 23 ≤ ja) (hD : DeadFrom D ja) :
    storeTarget
        (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv ffv)
          na') (tFFRef ja) (.bool ffv')
      = .ok (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv
          ffv') na') := by
  rw [show tFFRef ja = .chain (.addr (.base ⟨ja + 1⟩)) [] [] from rfl,
    storeTarget_addr
      (show Heap.lookup (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv
          D ja jv ffv) na').heap (.base ⟨ja + 1⟩)
          = some ⟨some .bool, .bool ffv⟩ from
        lookup_liveFF nv sv tv n l lp siv civ tvp mv iv D ja jv ffv hja hD)
      (norm_bool_val _ ffv'),
    show (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv ffv)
      na').heap = tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv ffv
      from rfl,
    set_liveFF nv sv tv n l lp siv civ tvp mv iv D ja jv ffv ffv' hja hD]

/-- Store into the solo `j` cell (the window before the flag exists). -/
theorem storeJ_soloT (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv : Int) (D : Heap) (ja : Nat)
    (jv w : Int) (na' : Nat) (hw1 : 0 ≤ w) (hw2 : w < 2 ^ 64)
    (hja : 23 ≤ ja) (hD : DeadFrom D ja) :
    storeTarget
        (tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp mv iv false
          ++ (D ++ [(.base ⟨ja⟩, tsu64 jv)])) na') (tJRef ja)
        (.int w .uint64)
      = .ok (tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp mv iv false
          ++ (D ++ [(.base ⟨ja⟩, tsu64 w)])) na') := by
  have hn := norm_u64_scalar
    (tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp mv iv false
      ++ (D ++ [(.base ⟨ja⟩, tsu64 jv)])) na') w
  rw [unorm_of_range hw1 hw2] at hn
  rw [show tJRef ja = .chain (.addr (.base ⟨ja⟩)) [] [] from rfl,
    storeTarget_addr
      (show Heap.lookup (tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp mv
          iv false ++ (D ++ [(.base ⟨ja⟩, tsu64 jv)])) na').heap
          (.base ⟨ja⟩) = some ⟨some tU64, .int jv .uint64⟩ from
        lookup_soloJ nv sv tv n l lp siv civ tvp mv iv D ja jv hja hD)
      hn,
    show (tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp mv iv false
      ++ (D ++ [(.base ⟨ja⟩, tsu64 jv)])) na').heap
      = tsHeapOut nv sv tv n l lp siv civ tvp mv iv false
        ++ (D ++ [(.base ⟨ja⟩, tsu64 jv)]) from rfl,
    set_soloJ nv sv tv n l lp siv civ tvp mv iv D ja jv w hja hD]

/-- The pair test's TRUE arm entry (the `ifK` dispatch). 1 step. -/
theorem t_inTrue_raw (σ : ExecState) (ja : Nat) (ch : Choices) :
    stepFn σ (.retV (.bool true) (tInCmpK ja)) ch
      = .ok (.exec (.seqn #[]) (inEnvCT ja)
          (.seq [twoSumFunc.matchBlock] (inEnvCT ja) (tInLoopK ja)),
        σ, ch) := by
  with_unfolding_all rfl

/-- The match block's scope push. 1 step. -/
theorem t_matchBlock_raw (σ : ExecState) (ja : Nat) (ch : Choices) :
    stepFn σ (.exec twoSumFunc.matchBlock (inEnvCT ja)
        (.seq [] (inEnvCT ja) (tInLoopK ja))) ch
      = .ok (.next (.seq [.ifThenElse
            (.eqCmp tU64
              (.add (.indexGet (.var "s") (.var "i"))
                    (.indexGet (.var "s") (.var "j")))
              (.var "target"))
            twoSumFunc.foundBlock (.seqn #[])]
          (inEnvB2T ja) (.seq [] (inEnvCT ja) (tInLoopK ja))), σ, ch) := by
  with_unfolding_all rfl

/-- The pair test's FALSE arm entry. 1 step. -/
theorem t_inMissIf_raw (σ : ExecState) (ja : Nat) (ch : Choices) :
    stepFn σ (.retV (.bool false) (tInIfK ja)) ch
      = .ok (.exec (.seqn #[]) (inEnvB2T ja) (tFoundK ja), σ, ch) := by
  with_unfolding_all rfl

/-! ## The composed pieces of one outer iteration -/

/-- **The inner `j`/flag allocation** (the nested loop's signature
cost): from the outer test's TRUE delivery at `i = t`, allocate the
fresh live pair at `⟨na, na+1⟩`, store `j := t + 1`, flag `true`, and
reach the inner loop head. `21 + 16 = 37` steps. -/
theorem ts_alloc (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp : Int) (t : Nat) (D : Heap) (na : Nat)
    (hna : 23 ≤ na) (hD : DeadFrom D na) (ht : t + 1 < 2 ^ 64)
    (ch : Choices) :
    stepFnIter 37
      (tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp ((n : Nat) : Int)
        ((t : Nat) : Int) false ++ D) na)
      (.retV (.bool true) tOutCmpK) ch
      = .ok (tInHeadCfg na,
          tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp ((n : Nat) : Int)
            ((t : Nat) : Int) D na ((t + 1 : Nat) : Int) true) (na + 2),
          ch) := by
  -- outer body → the `j` initialization
  have h1 := t_oB1_raw (tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) false ++ D) na) ch
  -- the `j` allocation at `na`
  have hmiss : Heap.lookup (tsHeapOut nv sv tv n l lp siv civ tvp
      ((n : Nat) : Int) ((t : Nat) : Int) false ++ D) (.base ⟨na⟩)
      = none :=
    lookup_outD_none nv sv tv n l lp siv civ tvp _ _ false hna
      (hD na (Nat.le_refl _))
  have h2 : stepFnIter 1 (tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) false ++ D) na)
      (.exec (.initialization { id := "j", typ := tU64 }) bodyEnvT
        (.seq [tJAssign, tInnerLoopBlock] bodyEnvT tJSeqTail)) ch
      = .ok (.next (.seq [tJAssign, tInnerLoopBlock] (jEnvT na) tJSeqTail),
          tSt σ (Heap.set (tsHeapOut nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) false ++ D) (.base ⟨na⟩) (tsu64 0)) (na + 1),
          ch) :=
    stepFnIter_one (stepFn_init_seq (def_u64 _))
  rw [set_fresh hmiss, List.append_assoc] at h2
  -- `j := t + 1`
  have h3 := t_jAssign_raw σ nv sv tv n l lp siv civ tvp
    ((n : Nat) : Int) ((t : Nat) : Int)
    (D ++ [(.base ⟨na⟩, tsu64 0)]) na (na + 1) ch
  rw [show ((t : Nat) : Int) + 1 = ((t + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((t + 1 : Nat) : Int)) (by omega)
      (by exact_mod_cast ht)] at h3
  have hstJ := storeJ_soloT σ nv sv tv n l lp siv civ tvp
    ((n : Nat) : Int) ((t : Nat) : Int) D na 0 ((t + 1 : Nat) : Int)
    (na + 1) (by omega) (by exact_mod_cast ht) hna hD
  have h4 := stepFnIter_one (stepFn_store_step (ch := ch) (rs := [])
    (vs := []) (body := .seqn #[]) (env := jEnvT na)
    (k := .seq [tInnerLoopBlock] (jEnvT na) tJSeqTail) hstJ)
  -- storeK drain → the flag initialization
  have h5 : stepFnIter 5
      (tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) false ++ (D ++ [(.base ⟨na⟩, tsu64 ((t + 1 : Nat) : Int))]))
        (na + 1))
      (.next (.storeK [] [] (.seqn #[]) (jEnvT na)
        (.seq [tInnerLoopBlock] (jEnvT na) tJSeqTail))) ch
      = .ok (.exec (.initialization { id := "$forFirst", typ := .bool })
            ([] :: jEnvT na)
            (.seq [.assign (.var "$forFirst") (.boolLit true),
                   .while (.boolLit true) twoSumFunc.innerBody]
              ([] :: jEnvT na) (.seq [] (jEnvT na) tJSeqTail)),
          tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) false ++ (D ++ [(.base ⟨na⟩, tsu64 ((t + 1 : Nat) : Int))]))
            (na + 1), ch) := by
    have s1 := stepFnIter_one (σ := tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) false ++ (D ++ [(.base ⟨na⟩,
        tsu64 ((t + 1 : Nat) : Int))])) (na + 1)) (ch := ch)
      (stepFn_storeK_nil (body := .seqn #[]) (env := jEnvT na)
        (k := .seq [tInnerLoopBlock] (jEnvT na) tJSeqTail))
    have s2 := stepFnIter_one (σ := tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) false ++ (D ++ [(.base ⟨na⟩,
        tsu64 ((t + 1 : Nat) : Int))])) (na + 1)) (ch := ch)
      (stepFn_seqn_splice (ss := #[]) (env := jEnvT na)
        (rest := [tInnerLoopBlock]) (k := tJSeqTail))
    have s3 := stepFnIter_one (σ := tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) false ++ (D ++ [(.base ⟨na⟩,
        tsu64 ((t + 1 : Nat) : Int))])) (na + 1)) (ch := ch)
      (stepFn_seq_pop (t := tInnerLoopBlock) (rest := [])
        (env := jEnvT na) (k := tJSeqTail))
    have s4 := stepFnIter_one
      (t_blockIn_raw (tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) false ++ (D ++ [(.base ⟨na⟩,
        tsu64 ((t + 1 : Nat) : Int))])) (na + 1)) na ch)
    have s5 := stepFnIter_one (σ := tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) false ++ (D ++ [(.base ⟨na⟩,
        tsu64 ((t + 1 : Nat) : Int))])) (na + 1)) (ch := ch)
      (stepFn_seq_pop
        (t := .initialization { id := "$forFirst", typ := .bool })
        (rest := [.assign (.var "$forFirst") (.boolLit true),
                  .while (.boolLit true) twoSumFunc.innerBody])
        (env := [] :: jEnvT na) (k := .seq [] (jEnvT na) tJSeqTail))
    exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain s1 s2) s3) s4) s5
  -- the flag allocation at `na + 1`
  have hmissF : Heap.lookup
      (tsHeapOut nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) false ++ (D ++ [(.base ⟨na⟩, tsu64 ((t + 1 : Nat) : Int))]))
      (.base ⟨na + 1⟩) = none := by
    rw [lookup_append_right (lookup_out_none nv sv tv n l lp siv civ tvp
        _ _ false (by omega)),
      lookup_append_right (hD (na + 1) (by omega)),
      lookup_cons_ne (base_beq_false (show na ≠ na + 1 by omega))]
    rfl
  have h6 : stepFnIter 1
      (tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) false ++ (D ++ [(.base ⟨na⟩, tsu64 ((t + 1 : Nat) : Int))]))
        (na + 1))
      (.exec (.initialization { id := "$forFirst", typ := .bool })
        ([] :: jEnvT na)
        (.seq [.assign (.var "$forFirst") (.boolLit true),
               .while (.boolLit true) twoSumFunc.innerBody]
          ([] :: jEnvT na) (.seq [] (jEnvT na) tJSeqTail))) ch
      = .ok (.next (.seq [.assign (.var "$forFirst") (.boolLit true),
              .while (.boolLit true) twoSumFunc.innerBody]
            (inEnvT na) (.seq [] (jEnvT na) tJSeqTail)),
          tSt σ (Heap.set
            (tsHeapOut nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) false ++ (D ++ [(.base ⟨na⟩, tsu64 ((t + 1 : Nat) : Int))]))
            (.base ⟨na + 1⟩) (tsbool false)) (na + 2), ch) :=
    stepFnIter_one (stepFn_init_seq (def_bool _))
  rw [set_fresh hmissF, List.append_assoc, List.append_assoc] at h6
  -- `$forFirst := true`
  have h7 := t_ffAssign_raw
    (tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) false ++ (D ++ ([(.base ⟨na⟩, tsu64 ((t + 1 : Nat) : Int))] ++ [(.base ⟨na + 1⟩, tsbool false)]))) (na + 2)) na ch
  have hstF : storeTarget
      (tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) false ++ (D ++ ([(.base ⟨na⟩, tsu64 ((t + 1 : Nat) : Int))]
        ++ [(.base ⟨na + 1⟩, tsbool false)]))) (na + 2))
      (tFFRef na) (.bool true)
      = .ok (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp
          ((n : Nat) : Int) ((t : Nat) : Int) D na
          ((t + 1 : Nat) : Int) true) (na + 2)) :=
    storeFF_liveT σ nv sv tv n l lp siv civ tvp ((n : Nat) : Int)
      ((t : Nat) : Int) D na ((t + 1 : Nat) : Int) false true (na + 2)
      hna hD
  have h8 := stepFnIter_one (stepFn_store_step (ch := ch) (rs := [])
    (vs := []) (body := .seqn #[]) (env := inEnvT na)
    (k := .seq [.while (.boolLit true) twoSumFunc.innerBody]
      (inEnvT na) (.seq [] (jEnvT na) tJSeqTail)) hstF)
  -- drain → the inner loop head
  have h9 : stepFnIter 3
      (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp ((n : Nat) : Int)
        ((t : Nat) : Int) D na ((t + 1 : Nat) : Int) true) (na + 2))
      (.next (.storeK [] [] (.seqn #[]) (inEnvT na)
        (.seq [.while (.boolLit true) twoSumFunc.innerBody]
          (inEnvT na) (.seq [] (jEnvT na) tJSeqTail)))) ch
      = .ok (tInHeadCfg na,
          tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp ((n : Nat) : Int)
            ((t : Nat) : Int) D na ((t + 1 : Nat) : Int) true) (na + 2),
          ch) := by
    have s1 := stepFnIter_one (σ := tSt σ (tsHeapIn nv sv tv n l lp siv
        civ tvp ((n : Nat) : Int) ((t : Nat) : Int) D na
        ((t + 1 : Nat) : Int) true) (na + 2)) (ch := ch)
      (stepFn_storeK_nil (body := .seqn #[]) (env := inEnvT na)
        (k := .seq [.while (.boolLit true) twoSumFunc.innerBody]
          (inEnvT na) (.seq [] (jEnvT na) tJSeqTail)))
    have s2 := stepFnIter_one (σ := tSt σ (tsHeapIn nv sv tv n l lp siv
        civ tvp ((n : Nat) : Int) ((t : Nat) : Int) D na
        ((t + 1 : Nat) : Int) true) (na + 2)) (ch := ch)
      (stepFn_seqn_splice (ss := #[]) (env := inEnvT na)
        (rest := [.while (.boolLit true) twoSumFunc.innerBody])
        (k := .seq [] (jEnvT na) tJSeqTail))
    have s3 := stepFnIter_one (σ := tSt σ (tsHeapIn nv sv tv n l lp siv
        civ tvp ((n : Nat) : Int) ((t : Nat) : Int) D na
        ((t + 1 : Nat) : Int) true) (na + 2)) (ch := ch)
      (stepFn_seq_pop
        (t := .while (.boolLit true) twoSumFunc.innerBody) (rest := [])
        (env := inEnvT na) (k := .seq [] (jEnvT na) tJSeqTail))
    exact stepFnIter_chain (stepFnIter_chain s1 s2) s3
  -- assemble: 9 + 1 + 10 + 1 + 5 + 1 + 6 + 1 + 3 = 37
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4) h5) h6) h7) h8) h9

/-- **The `storeK`-to-exit-test walk** shared by both dispatch passes:
drained flag/`j` store → the exit test's `j` read. 7 steps. -/
theorem ts_toTest (σ : ExecState) (ja : Nat) (ch : Choices) :
    stepFnIter 7 σ
      (.next (.storeK [] [] (.seqn #[]) (inEnvCT ja) (tInBodyTail ja))) ch
      = .ok (.evalE (.var "j") (inEnvCT ja) (tJTestK ja), σ, ch) := by
  have s1 := stepFnIter_one (σ := σ) (ch := ch)
    (stepFn_storeK_nil (body := .seqn #[]) (env := inEnvCT ja)
      (k := tInBodyTail ja))
  have s2 := stepFnIter_one (σ := σ) (ch := ch)
    (stepFn_seqn_splice (ss := #[]) (env := inEnvCT ja)
      (rest := [.seqn #[], tIfJN, twoSumFunc.matchBlock])
      (k := tInLoopK ja))
  have s3 := stepFnIter_one (σ := σ) (ch := ch)
    (stepFn_seq_pop (t := .seqn #[])
      (rest := [tIfJN, twoSumFunc.matchBlock])
      (env := inEnvCT ja) (k := tInLoopK ja))
  have s4 := stepFnIter_one (σ := σ) (ch := ch)
    (stepFn_seqn_splice (ss := #[]) (env := inEnvCT ja)
      (rest := [tIfJN, twoSumFunc.matchBlock]) (k := tInLoopK ja))
  have s5 := stepFnIter_one (σ := σ) (ch := ch)
    (stepFn_seq_pop (t := tIfJN) (rest := [twoSumFunc.matchBlock])
      (env := inEnvCT ja) (k := tInLoopK ja))
  have s6 := t_iIfPush_raw σ ja ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain s1 s2) s3) s4) s5) s6

/-- **The inner first-pass dispatch**: head (flag `true`) → the
exit-test delivery at `j = jv`. 25 steps. -/
theorem ts_inDispatch (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv : Int) (D : Heap) (ja : Nat)
    (jv : Int) (na : Nat) (hja : 23 ≤ ja) (hD : DeadFrom D ja)
    (ch : Choices) :
    stepFnIter 25
      (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv true) na)
      (tInHeadCfg ja) ch
      = .ok (.retV (.bool (decide (jv < mv))) (tInCmpK ja),
          tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv false)
            na, ch) := by
  have h1 := t_iH_raw
    (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv true) na)
    ja ch
  have h2 := stepFnIter_one (ch := ch)
    (stepFn_var (σ := tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv
        D ja jv true) na) (env_inC_ff ja)
      (show Heap.lookup (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv
          D ja jv true) na).heap (.base ⟨ja + 1⟩) = some (tsbool true) from
        lookup_liveFF nv sv tv n l lp siv civ tvp mv iv D ja jv true hja hD)
      (k := tFFIfK ja))
  have h3 := t_iFFT_raw
    (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv true) na)
    ja ch
  have hstF := storeFF_liveT σ nv sv tv n l lp siv civ tvp mv iv D ja jv
    true false na hja hD
  have h4 := stepFnIter_one (stepFn_store_step (ch := ch) (rs := [])
    (vs := []) (body := .seqn #[]) (env := inEnvCT ja)
    (k := tInBodyTail ja) hstF)
  have h5 := ts_toTest
    (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv false) na)
    ja ch
  have h6 := stepFnIter_one (ch := ch)
    (stepFn_var (σ := tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv
        D ja jv false) na) (env_inC_j ja)
      (show Heap.lookup (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv
          D ja jv false) na).heap (.base ⟨ja⟩) = some (tsu64 jv) from
        lookup_liveJ nv sv tv n l lp siv civ tvp mv iv D ja jv false hja hD)
      (k := tJTestK ja))
  have h7 := t_iTest_raw σ nv sv tv n l lp siv civ tvp mv iv D ja jv jv
    false na ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4)
      h5) h6) h7

/-- **The inner later-pass dispatch**: head (flag `false`, `j = u`) →
the exit-test delivery at `j = u + 1`. 29 steps. -/
theorem ts_inLater (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv : Int) (D : Heap) (ja : Nat)
    (u : Nat) (na : Nat) (hja : 23 ≤ ja) (hD : DeadFrom D ja)
    (hu : u + 1 < 2 ^ 64) (ch : Choices) :
    stepFnIter 29
      (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja
        ((u : Nat) : Int) false) na)
      (tInHeadCfg ja) ch
      = .ok (.retV (.bool (decide (((u + 1 : Nat) : Int) < mv)))
            (tInCmpK ja),
          tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja
            ((u + 1 : Nat) : Int) false) na, ch) := by
  have h1 := t_iH_raw
    (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja
      ((u : Nat) : Int) false) na) ja ch
  have h2 := stepFnIter_one (ch := ch)
    (stepFn_var (σ := tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv
        D ja ((u : Nat) : Int) false) na) (env_inC_ff ja)
      (show Heap.lookup (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv
          D ja ((u : Nat) : Int) false) na).heap (.base ⟨ja + 1⟩)
          = some (tsbool false) from
        lookup_liveFF nv sv tv n l lp siv civ tvp mv iv D ja
          ((u : Nat) : Int) false hja hD)
      (k := tFFIfK ja))
  have h3 := t_iFFF_raw
    (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja
      ((u : Nat) : Int) false) na) ja ch
  have h4 := stepFnIter_one (ch := ch)
    (stepFn_var (σ := tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv
        D ja ((u : Nat) : Int) false) na) (env_inC_j ja)
      (show Heap.lookup (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv
          D ja ((u : Nat) : Int) false) na).heap (.base ⟨ja⟩)
          = some (tsu64 ((u : Nat) : Int)) from
        lookup_liveJ nv sv tv n l lp siv civ tvp mv iv D ja
          ((u : Nat) : Int) false hja hD)
      (k := tJIncrK ja))
  have h5 := t_iIncr_raw
    (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja
      ((u : Nat) : Int) false) na) ja ((u : Nat) : Int) ch
  rw [show ((u : Nat) : Int) + 1 = ((u + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((u + 1 : Nat) : Int)) (by omega)
      (by exact_mod_cast hu)] at h5
  have hstJ := storeJ_liveT σ nv sv tv n l lp siv civ tvp mv iv D ja
    ((u : Nat) : Int) ((u + 1 : Nat) : Int) false na (by omega)
    (by exact_mod_cast hu) hja hD
  have h6 := stepFnIter_one (stepFn_store_step (ch := ch) (rs := [])
    (vs := []) (body := .seqn #[]) (env := inEnvCT ja)
    (k := tInBodyTail ja) hstJ)
  have h7 := ts_toTest
    (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja
      ((u + 1 : Nat) : Int) false) na) ja ch
  have h8 := stepFnIter_one (ch := ch)
    (stepFn_var (σ := tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv
        D ja ((u + 1 : Nat) : Int) false) na) (env_inC_j ja)
      (show Heap.lookup (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv
          D ja ((u + 1 : Nat) : Int) false) na).heap (.base ⟨ja⟩)
          = some (tsu64 ((u + 1 : Nat) : Int)) from
        lookup_liveJ nv sv tv n l lp siv civ tvp mv iv D ja
          ((u + 1 : Nat) : Int) false hja hD)
      (k := tJTestK ja))
  have h9 := t_iTest_raw σ nv sv tv n l lp siv civ tvp mv iv D ja
    ((u + 1 : Nat) : Int) ((u + 1 : Nat) : Int) false na ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4) h5) h6) h7) h8) h9

/-- **The pair test** (both branches share it): the exit test's TRUE
delivery at `(i, j) = (t, u)` → the wrapped-sum verdict at the found
`if`. 23 steps. -/
theorem ts_inBody (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp : Int) (t u : Nat) (D : Heap)
    (ja : Nat) (na : Nat) (hja : 23 ≤ ja) (hD : DeadFrom D ja)
    (hlen : l.length = n) (hrange : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64)
    (ht : t < n) (hu : u < n) (ch : Choices) :
    stepFnIter 23
      (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp ((n : Nat) : Int)
        ((t : Nat) : Int) D ja ((u : Nat) : Int) false) na)
      (.retV (.bool true) (tInCmpK ja)) ch
      = .ok (.retV (.bool
            ((l.getD t 0 + l.getD u 0) % 2 ^ 64 == tvp)) (tInIfK ja),
          tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp ((n : Nat) : Int)
            ((t : Nat) : Int) D ja ((u : Nat) : Int) false) na, ch) := by
  have h1 := stepFnIter_one (t_inTrue_raw (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) D ja ((u : Nat) : Int) false) na) ja ch)
  have h2 := stepFnIter_one (σ := (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) D ja ((u : Nat) : Int) false) na)) (ch := ch)
    (stepFn_seqn_splice (ss := #[]) (env := inEnvCT ja)
      (rest := [twoSumFunc.matchBlock]) (k := tInLoopK ja))
  have h3 := stepFnIter_one (σ := (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) D ja ((u : Nat) : Int) false) na)) (ch := ch)
    (stepFn_seq_pop (t := twoSumFunc.matchBlock) (rest := [])
      (env := inEnvCT ja) (k := tInLoopK ja))
  have h4 := stepFnIter_one (t_matchBlock_raw (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) D ja ((u : Nat) : Int) false) na) ja ch)
  have h5 := stepFnIter_one (σ := (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) D ja ((u : Nat) : Int) false) na)) (ch := ch)
    (stepFn_seq_pop
      (t := .ifThenElse
        (.eqCmp tU64
          (.add (.indexGet (.var "s") (.var "i"))
                (.indexGet (.var "s") (.var "j")))
          (.var "target"))
        twoSumFunc.foundBlock (.seqn #[])) (rest := [])
      (env := inEnvB2T ja) (k := .seq [] (inEnvCT ja) (tInLoopK ja)))
  have h6 := t_bodyB_raw σ nv sv tv n l lp siv civ tvp ((n : Nat) : Int)
    ((t : Nat) : Int) D ja ((u : Nat) : Int) na ch
  have hgetT : (⟨l.map (fun v => .int v .uint64)⟩ : Array GoValue)[0 + t]?
      = some (.int (l.getD t 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega)]
  have hgetU : (⟨l.map (fun v => .int v .uint64)⟩ : Array GoValue)[0 + u]?
      = some (.int (l.getD u 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega)]
  have h7 := stepFnIter_one (ch := ch)
    (stepFn_strict_apply (done := [tsSliceS n]) (env := inEnvB2T ja)
      (k := .strictK .add [] [.indexGet (.var "s") (.var "j")]
        (inEnvB2T ja)
        (.strictK (.eqCmp tU64) [] [.var "target"] (inEnvB2T ja)
          (tInIfK ja)))
      (applyStrictOp_indexGet_slice (ik := .uint64) (i := t)
        (lookup_inS_T σ nv sv tv n l lp siv civ tvp ((n : Nat) : Int)
          ((t : Nat) : Int) D ja ((u : Nat) : Int) false na)
        (Nat.le_refl n) ht hgetT))
  have h8 := t_bodyC_raw σ nv sv tv n l lp siv civ tvp ((n : Nat) : Int)
    ((t : Nat) : Int) D ja ((u : Nat) : Int) (l.getD t 0) na ch
  have h9 := stepFnIter_one (ch := ch)
    (stepFn_var (σ := tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp
        ((n : Nat) : Int) ((t : Nat) : Int) D ja ((u : Nat) : Int) false)
        na) (env_inB2_j ja)
      (show Heap.lookup (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp
          ((n : Nat) : Int) ((t : Nat) : Int) D ja ((u : Nat) : Int)
          false) na).heap (.base ⟨ja⟩)
          = some (tsu64 ((u : Nat) : Int)) from
        lookup_liveJ nv sv tv n l lp siv civ tvp ((n : Nat) : Int)
          ((t : Nat) : Int) D ja ((u : Nat) : Int) false hja hD)
      (k := tIdx2K n ja (l.getD t 0)))
  have h10 := stepFnIter_one (ch := ch)
    (stepFn_strict_apply (done := [tsSliceS n]) (env := inEnvB2T ja)
      (k := .strictK .add [.int (l.getD t 0) .uint64] [] (inEnvB2T ja)
        (.strictK (.eqCmp tU64) [] [.var "target"] (inEnvB2T ja)
          (tInIfK ja)))
      (applyStrictOp_indexGet_slice (ik := .uint64) (i := u)
        (lookup_inS_T σ nv sv tv n l lp siv civ tvp ((n : Nat) : Int)
          ((t : Nat) : Int) D ja ((u : Nat) : Int) false na)
        (Nat.le_refl n) hu hgetU))
  have h11 := t_bodyD_raw σ nv sv tv n l lp siv civ tvp ((n : Nat) : Int)
    ((t : Nat) : Int) D ja ((u : Nat) : Int) (l.getD t 0) (l.getD u 0)
    na ch
  rw [unorm_add_range (hrange _ (getD_mem (by omega)))
    (hrange _ (getD_mem (by omega)))] at h11
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain h1 h2) h3) h4) h5) h6) h7) h8) h9) h10) h11

/-- **One inner MISS iteration**: exit-test TRUE delivery at `u`, the
pair does not hit, back to the exit-test delivery at `u + 1`.
57 steps exactly (the P5 schema's `hstep`). -/
theorem ts_inIter (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp : Int) (t u : Nat) (D : Heap)
    (ja : Nat) (na : Nat) (hja : 23 ≤ ja) (hD : DeadFrom D ja)
    (hlen : l.length = n) (hrange : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64)
    (hn : n < 2 ^ 63) (ht : t < n) (hu : u < n)
    (hne : ¬ (l.getD t 0 + l.getD u 0) % 2 ^ 64 = tvp) (ch : Choices) :
    stepFnIter 57
      (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp ((n : Nat) : Int)
        ((t : Nat) : Int) D ja ((u : Nat) : Int) false) na)
      (.retV (.bool true) (tInCmpK ja)) ch
      = .ok (.retV (.bool (decide
            (((u + 1 : Nat) : Int) < ((n : Nat) : Int)))) (tInCmpK ja),
          tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp ((n : Nat) : Int)
            ((t : Nat) : Int) D ja ((u + 1 : Nat) : Int) false) na,
          ch) := by
  have h1 := ts_inBody σ nv sv tv n l lp siv civ tvp t u D ja na hja hD
    hlen hrange ht hu ch
  rw [show ((l.getD t 0 + l.getD u 0) % 2 ^ 64 == tvp) = false from
    beq_eq_false_iff_ne.mpr hne] at h1
  have h2 := stepFnIter_one (t_inMissIf_raw (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) D ja ((u : Nat) : Int) false) na) ja ch)
  have h3 := stepFnIter_one (σ := (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) D ja ((u : Nat) : Int) false) na)) (ch := ch)
    (stepFn_seqn_splice (ss := #[]) (env := inEnvB2T ja) (rest := [])
      (k := .seq [] (inEnvCT ja) (tInLoopK ja)))
  have h4 := t_missTail_raw (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp ((n : Nat) : Int) ((t : Nat) : Int) D ja ((u : Nat) : Int) false) na) ja ch
  have h5 := ts_inLater σ nv sv tv n l lp siv civ tvp ((n : Nat) : Int)
    ((t : Nat) : Int) D ja u na hja hD (by omega) ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h1 h2) h3) h4) h5

end GoLean.Examples.TwoSum
