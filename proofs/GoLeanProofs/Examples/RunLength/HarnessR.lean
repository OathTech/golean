import GoLeanProofs.Examples.RunLength.Machine

/-!
# RunLength — the harness run (entry, setup, copy, subject, exit)

The `rle_harness_r` run, PROGRAM-generic throughout: every raw segment
is proven over an abstract `σ` (only `heap`/`nextAddr` pinned), and
the ONE step that consults the program — the `rle(s)` frame entry — is
conditioned through `StepKit.stepFn_call_enter`.

## Scope: the SINGLE-RUN regime (`n ≤ 3`), and why

The harness's own cap is `n ≤ 8`. This module proves the run for
`n ≤ 3` — the regime where the family `seed + i/3` is constant, so the
subject performs exactly ONE new-run event (two `append`s, both from
cap 0, both SPILLS with choice-dependent capacities `capV, capC ∈
[1, 32]`, carried symbolically) and extends thereafter.

**The `n ∈ [4, 8]` regime is a RECORDED HONEST GAP**, not a
todo-comment: at the second new-run event (`i = 3`) the appends run at
`len 1, cap capV` where `capV` came from the FIRST spill's choice —
so whether the second append spills (allocates) or extends in place is
CHOICE-DEPENDENT, and every heap address allocated after it shifts by
the number of spills so far. Raw `with_unfolding_all rfl` segments
need literal addresses, so each spill history needs its own segment
set (3 layouts at the second event, 5 at the third, multiplied across
both output slices), OR kit machinery that does not exist yet — an
address-shift frame lemma, or a conditioned micro-step library that
can walk allocation at a symbolic `nextAddr`. Both are recorded as kit
gaps in the campaign log (`.tmp/kitgaps-rle.md`, lane B). Nothing here
weakens fail-closed behavior: the theorem simply does not claim
`n > 3`.

## Kit gaps witnessed in this module

* `applyStrictOp_div_u64` — the kit has the `%` executable fact only;
  `/` is re-derived locally below (KIT-GAP WITNESS).
* `applyStmtOp` has NO appendSlice vocabulary — the spill-step
  executable fact (`append_spill1` below, with its `buildAppendBackingValue`
  closed form) is this example's main kit-gap witness.
-/

namespace GoLean.Examples.RunLength

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## The `/` executable fact

-- KIT-GAP WITNESS (see .tmp/kitgaps-rle.md): mirror of
-- `SliceMem.applyStrictOp_mod_u64`, which the kit has; `/` it does
-- not. -/

theorem applyStrictOp_div_u64 {σ : ExecState} {a b : Nat}
    (ha : a < 2 ^ 64) (hb : 0 < b) (hb64 : b < 2 ^ 64) :
    applyStrictOp σ .div [.int (a : Int) .uint64, .int (b : Int) .uint64]
      = .ok (.int ((a / b : Nat) : Int) .uint64, σ) := by
  have hbne : (((b : Nat) : Int) == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, Int.natCast_eq_zero]
    omega
  have htdiv : Int.tdiv (a : Int) (b : Int) = ((a / b : Nat) : Int) := rfl
  have hnorm : IntKind.normalize .uint64 ((a / b : Nat) : Int)
      = ((a / b : Nat) : Int) :=
    unorm_nat_of_lt (by
      have := Nat.div_le_self a b
      omega)
  simp only [applyStrictOp, valueAsInt, hbne, intBinaryResult,
    valueAsIntValue, htdiv, IntKind.compatibleResult,
    Bool.false_eq_true, if_false, Bind.bind, Except.bind, pure, Except.pure]
  simp only [show (IntKind.uint64 == IntKind.uint64) = true from rfl,
    if_true, hnorm]

/-! ## Raw run segments — the harness front, PROGRAM-generic -/

/-- Entry A: body start → the `$c10` makeSlice apply point. 10 steps. -/
theorem q_E1_raw (σ : ExecState) (nv sv : Int) (ch : Choices) :
    stepFnIter 10 (qSt σ (qHeap0 nv sv) 6) qHC0 ch
      = .ok (.retV (.int nv .uint64)
          (.stmtOpK (.makeSlice tU64 false) 1
            [.addr (.base ⟨6⟩)] [] envC10Q
            (.seq [qS2, qS3, qS4, qS5, qS6, qS7, qS8, qS9, qS10] envC10Q
              (.frame [] [] [] [] .stop))),
        qSt σ (qHeapC8 nv sv) 7, ch) := by
  with_unfolding_all rfl

/-- **`make([]uint64, n)` at SYMBOLIC `n`.** -/
theorem q_make_apply (σ : ExecState) (nv sv : Int) (n : Nat)
    (ch : Choices) :
    applyStmtOp (qSt σ (qHeapC8 nv sv) 7) ch (.makeSlice tU64 false) 1
      [.addr (.base ⟨6⟩), .int (n : Nat) .uint64]
      = .ok (qSt σ (qHeapMake nv sv n) 8, ch) := by
  have hnn1 := natFromNonneg_cast
    "runtime error: makeslice: len out of range" n
  have hnn2 := natFromNonneg_cast
    "runtime error: makeslice: cap out of range" n
  have hb := GoLean.Iris.buildDefaultArrayValue_int
    (qSt σ (qHeapC8 nv sv) 7) .uint64 n
  have harr : (List.replicate n (GoValue.int 0 .uint64)).toArray
      = (⟨(List.replicate n (0 : Int)).map
          (fun v => GoValue.int v .uint64)⟩ : Array GoValue) := by
    simp [List.map_replicate]
  rw [harr] at hb
  simp only [applyStmtOp, applyStmtOpCore, valueAsInt, valueAsLoc,
    hnn1, hnn2, hb, Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (Nat.lt_irrefl n)]
  with_unfolding_all rfl

/-- Entry B: `s := $c10`, the setup counter and flag → the setup loop
head. 42 steps. -/
theorem q_E2_raw (σ : ExecState) (nv sv : Int) (n : Nat) (ch : Choices) :
    stepFnIter 42 (qSt σ (qHeapMake nv sv n) 8)
      (.next (.seq [qS2, qS3, qS4, qS5, qS6, qS7, qS8, qS9, qS10] envC10Q
        (.frame [] [] [] [] .stop))) ch
      = .ok (suHeadCfgQ,
          qSt σ (qHeapSu nv sv n (List.replicate n 0) 0 true) 11, ch) := by
  with_unfolding_all rfl

/-! ### The setup loop -/

theorem su_A0_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 25 (qSt σ (qHeapSu nv sv n l iv true) 11) suHeadCfgQ ch
      = .ok (.retV (.bool (decide (iv < nv))) suCmpKQ,
          qSt σ (qHeapSu nv sv n l iv false) 11, ch) := by
  with_unfolding_all rfl

theorem su_A1_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 29 (qSt σ (qHeapSu nv sv n l iv false) 11) suHeadCfgQ ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < nv))) suCmpKQ,
          qSt σ (qHeapSu nv sv n l
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false) 11, ch) := by
  with_unfolding_all rfl

/-- Setup fill phase A: test true → the `/` apply point. 19 steps. -/
theorem su_B1a_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 19 (qSt σ (qHeapSu nv sv n l iv false) 11)
      (.retV (.bool true) suCmpKQ) ch
      = .ok (.retV (.int 3 .uint64) (suDivKQ n sv iv),
          qSt σ (qHeapSu nv sv n l iv false) 11, ch) := by
  with_unfolding_all rfl

/-- Setup fill phase B: the `/` result → the add → the element-store
point. 2 steps. -/
theorem su_B1b_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv rv : Int) (ch : Choices) :
    stepFnIter 2 (qSt σ (qHeapSu nv sv n l iv false) 11)
      (.retV (.int rv .uint64) (suAddKQ n sv iv)) ch
      = .ok (.next (.storeK [suRefQ n iv]
            [.int (IntKind.normalize .uint64 (sv + rv)) .uint64]
            (.seqn #[]) suEnvQ2 suStTailQ),
          qSt σ (qHeapSu nv sv n l iv false) 11, ch) := by
  with_unfolding_all rfl

theorem su_D_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 5 (qSt σ (qHeapSu nv sv n l iv false) 11)
      (.next (.storeK [] [] (.seqn #[]) suEnvQ2 suStTailQ)) ch
      = .ok (suHeadCfgQ, qSt σ (qHeapSu nv sv n l iv false) 11, ch) := by
  with_unfolding_all rfl

/-- Setup exit: test false → `var pre` declared and the copy loop head.
39 steps. -/
theorem su_X_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 39 (qSt σ (qHeapSu nv sv n l iv false) 11)
      (.retV (.bool false) suCmpKQ) ch
      = .ok (cpHeadCfgQ,
          qSt σ (qHeapCp nv sv n l zeros8 iv 0 true) 14, ch) := by
  with_unfolding_all rfl

/-! ### The copy loop -/

theorem cp_A0_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 25 (qSt σ (qHeapCp nv sv n l lp siv civ true) 14) cpHeadCfgQ ch
      = .ok (.retV (.bool (decide (civ < nv))) cpCmpKQ,
          qSt σ (qHeapCp nv sv n l lp siv civ false) 14, ch) := by
  with_unfolding_all rfl

theorem cp_A1_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 29 (qSt σ (qHeapCp nv sv n l lp siv civ false) 14) cpHeadCfgQ
      ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1))
              < nv))) cpCmpKQ,
          qSt σ (qHeapCp nv sv n l lp siv
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1)))
            false) 14, ch) := by
  with_unfolding_all rfl

/-- Copy phase 1: test true → the `pre[i]` target banked, the `s[i]`
read at its apply point. 16 steps. -/
theorem cp_B1_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 16 (qSt σ (qHeapCp nv sv n l lp siv civ false) 14)
      (.retV (.bool true) cpCmpKQ) ch
      = .ok (.retV (.int civ .uint64)
            (.strictK .indexGet [qSliceS n] [] cpEnvQ2 (cpRhsKQ civ)),
          qSt σ (qHeapCp nv sv n l lp siv civ false) 14, ch) := by
  with_unfolding_all rfl

theorem cp_B2_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1 (qSt σ (qHeapCp nv sv n l lp siv civ false) 14)
      (.retV w (cpRhsKQ civ)) ch
      = .ok (.next (.storeK [cpRefQ civ] [w] (.seqn #[]) cpEnvQ2 cpStTailQ),
          qSt σ (qHeapCp nv sv n l lp siv civ false) 14, ch) := by
  with_unfolding_all rfl

theorem cp_D_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 5 (qSt σ (qHeapCp nv sv n l lp siv civ false) 14)
      (.next (.storeK [] [] (.seqn #[]) cpEnvQ2 cpStTailQ)) ch
      = .ok (cpHeadCfgQ, qSt σ (qHeapCp nv sv n l lp siv civ false) 14,
          ch) := by
  with_unfolding_all rfl

/-- Copy exit: test false → `vals`/`counts` declared and the `rle(s)`
argument delivered at the drained `callArgsK`. 15 steps. -/
theorem cp_X_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 15 (qSt σ (qHeapCp nv sv n l lp siv civ false) 14)
      (.retV (.bool false) cpCmpKQ) ch
      = .ok (.retV (qSliceS n) qCallArgsK,
          qSt σ (qHeapCall nv sv n l lp siv civ) 16, ch) := by
  with_unfolding_all rfl

/-! ## The setup loop, cleaned + its induction (the P5 schema) -/

/-- One setup iteration from the exit test's true delivery at `i`.
57 steps. -/
theorem su_iterQ (σ : ExecState) (n seed i : Nat) (hn : n < 2 ^ 63)
    (hi : i < n) (ch : Choices) :
    stepFnIter 57
      (qSt σ (qHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
        (rleFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false) 11)
      (.retV (.bool true) suCmpKQ) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) suCmpKQ,
          qSt σ (qHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
            (rleFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
            ((i + 1 : Nat) : Int) false) 11, ch) := by
  have hB1a := su_B1a_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily i seed ++ List.replicate (n - i) 0) ((i : Nat) : Int) ch
  have hdiv := stepFnIter_one (stepFn_strict_apply
    (done := [.int ((i : Nat) : Int) .uint64]) (env := suEnvQ2)
    (k := suAddKQ n ((seed : Nat) : Int) ((i : Nat) : Int)) (ch := ch)
    (applyStrictOp_div_u64
      (σ := qSt σ (qHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
        (rleFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false) 11)
      (a := i) (b := 3) (by omega) (by omega) (by omega)))
  have h1 := stepFnIter_chain hB1a hdiv
  have hB1b := su_B1b_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily i seed ++ List.replicate (n - i) 0)
    ((i : Nat) : Int) ((i / 3 : Nat) : Int) ch
  rw [unorm_add_nat seed (i / 3)] at hB1b
  have h2 := stepFnIter_chain h1 hB1b
  have hw : (0 : Int) ≤ (((seed + i / 3) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + i / 3) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + i / 3) (y := 2 ^ 64) (by omega)
    omega
  have hst := storeTarget_slice_u64
    (σ := qSt σ (qHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
      (rleFamily i seed ++ List.replicate (n - i) 0)
      ((i : Nat) : Int) false) 11)
    (a := ⟨7⟩) (off := 0) (len := n) (cap := n) (i := i) (n := n)
    (ik := .uint64) (l := rleFamily i seed ++ List.replicate (n - i) 0)
    (w := (((seed + i / 3) % 2 ^ 64 : Nat) : Int))
    (lookup_suQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
      (rleFamily i seed ++ List.replicate (n - i) 0) ((i : Nat) : Int)
      false 11)
    (Nat.le_refl n) hi
    (by rw [List.length_append, rleFamily_length, List.length_replicate]
        omega)
    (by rw [List.length_append, rleFamily_length, List.length_replicate]
        omega)
    rleFamilyZ_range hw
  rw [Nat.zero_add, rleFamily_set hi] at hst
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hst))
  have hD := su_D_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
    ((i : Nat) : Int) ch
  have h4 := stepFnIter_chain h3 hD
  have hA1 := su_A1_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
    ((i : Nat) : Int) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  exact stepFnIter_chain h4 hA1

/-- **The setup loop**, by the P5 iteration schema: `57·(n−i)` steps
materialize the wrapped `seed + i/3` family. -/
theorem su_loopQ (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 63) :
    ∀ i, i ≤ n → ∀ ch : Choices,
    stepFnIter (57 * (n - i))
      (qSt σ (qHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
        (rleFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false) 11)
      (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
        suCmpKQ) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) suCmpKQ,
          qSt σ (qHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
            (rleFamily n seed) ((n : Nat) : Int) false) 11, ch) := by
  intro i hin ch
  have hgen := stepFnIter_iterate (c := 57) (n := n)
    (T := fun j => qSt σ (qHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
      (rleFamily j seed ++ List.replicate (n - j) 0)
      ((j : Nat) : Int) false) 11)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int)
      < ((n : Nat) : Int)))) suCmpKQ)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact su_iterQ σ n seed j hn hj ch')
    i hin ch
  simpa using hgen

/-! ## The copy loop, cleaned + its induction -/

theorem cp_iterQ (σ : ExecState) (n seed : Nat) (siv : Int) (m : Nat)
    (hn : n < 2 ^ 63) (hcap : n ≤ 8) (hm : m < n) (ch : Choices) :
    stepFnIter 53
      (qSt σ (qHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
        (rleFamily n seed) (rlePre m seed) siv ((m : Nat) : Int) false) 14)
      (.retV (.bool true) cpCmpKQ) ch
      = .ok (.retV (.bool (decide
            (((m + 1 : Nat) : Int) < ((n : Nat) : Int)))) cpCmpKQ,
          qSt σ (qHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
            (rleFamily n seed) (rlePre (m + 1) seed) siv
            ((m + 1 : Nat) : Int) false) 14, ch) := by
  have hB1 := cp_B1_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre m seed) siv ((m : Nat) : Int) ch
  have hget : (⟨(rleFamily n seed).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + m]?
      = some (.int (((seed + m / 3) % 2 ^ 64 : Nat) : Int) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by rw [rleFamily_length]; omega),
      rleFamily_getD hm]
  have hread := stepFn_strict_apply (done := [qSliceS n]) (env := cpEnvQ2)
    (k := cpRhsKQ ((m : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .uint64)
      (lookup_cpS_Q σ ((n : Nat) : Int) ((seed : Nat) : Int) n
        (rleFamily n seed) (rlePre m seed) siv ((m : Nat) : Int) false 14)
      (Nat.le_refl n) hm hget)
  have hB2 := cp_B2_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre m seed) siv ((m : Nat) : Int)
    (.int (((seed + m / 3) % 2 ^ 64 : Nat) : Int) .uint64) ch
  have hw : (0 : Int) ≤ (((seed + m / 3) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + m / 3) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + m / 3) (y := 2 ^ 64) (by omega)
    omega
  have hst := storeTarget_arrayLocal_u64 (a := ⟨11⟩) (N := 8) (i := m)
    (ik := .uint64) (l := rlePre m seed)
    (w := (((seed + m / 3) % 2 ^ 64 : Nat) : Int))
    (lookup_cpPre_Q σ ((n : Nat) : Int) ((seed : Nat) : Int) n
      (rleFamily n seed) (rlePre m seed) siv ((m : Nat) : Int) false 14)
    (by rw [rlePre_length (by omega)]; omega)
    (rlePre_length (by omega)) rlePre_range hw
  rw [rlePre_set (by omega : m < 8)] at hst
  have hstore : storeTarget
      (qSt σ (qHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
        (rleFamily n seed) (rlePre m seed) siv ((m : Nat) : Int) false) 14)
      (cpRefQ ((m : Nat) : Int))
      (.int (((seed + m / 3) % 2 ^ 64 : Nat) : Int) .uint64)
      = .ok (qSt σ (qHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
          (rleFamily n seed) (rlePre (m + 1) seed) siv
          ((m : Nat) : Int) false) 14) := hst
  have hD := cp_D_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre (m + 1) seed) siv ((m : Nat) : Int) ch
  have hA1 := cp_A1_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre (m + 1) seed) siv ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  have h1 := stepFnIter_chain hB1 (stepFnIter_one hread)
  have h2 := stepFnIter_chain h1 hB2
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hstore))
  exact stepFnIter_chain (stepFnIter_chain h3 hD) hA1

/-- **The copy loop**: `53·(n−m)` steps materialize the zero-padded
prefix. -/
theorem cp_loopQ (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 63)
    (hcap : n ≤ 8) :
    ∀ m, m ≤ n → ∀ ch : Choices,
    stepFnIter (53 * (n - m))
      (qSt σ (qHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
        (rleFamily n seed) (rlePre m seed) ((n : Nat) : Int)
        ((m : Nat) : Int) false) 14)
      (.retV (.bool (decide (((m : Nat) : Int) < ((n : Nat) : Int))))
        cpCmpKQ) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) cpCmpKQ,
          qSt σ (qHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
            (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
            ((n : Nat) : Int) false) 14, ch) := by
  intro m hmn ch
  have hgen := stepFnIter_iterate (c := 53) (n := n)
    (T := fun j => qSt σ (qHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
      (rleFamily n seed) (rlePre j seed) ((n : Nat) : Int)
      ((j : Nat) : Int) false) 14)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int)
      < ((n : Nat) : Int)))) cpCmpKQ)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact cp_iterQ σ n seed ((n : Nat) : Int) j hn hcap hj ch')
    m hmn ch
  simpa using hgen

/-! ## The `rle` frame entry and its prologue -/

/-- The `enterFrame` discharge at the pinned program: the second and
last unfolding of `rleLowered` in this example. -/
theorem q_enterFrame_fact (n seed : Nat) (l lp : List Int) (siv civ : Int) :
    enterFrame
        (qSt qProg (qHeapCall ((n : Nat) : Int) ((seed : Nat) : Int) n l lp
          siv civ) 16) ⟨"rle"⟩ [qSliceS n]
      = .ok (rleFunc, rFrameEnv, [.base ⟨17⟩, .base ⟨18⟩],
          qSt qProg (qHeapFrame ((n : Nat) : Int) ((seed : Nat) : Int) n l lp
            siv civ) 19) := by
  with_unfolding_all rfl

/-- The `rle` prologue, first half: `$c0`/`runVals`, `$c1` declared →
the `$c1` makeSlice apply point. 37 steps, all raw (every operand is
literal). -/
theorem r_R1a_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 37 (qSt σ (qHeapFrame nv sv n l lp siv civ) 19)
      (.exec rleFunc.body rFrameEnv rFrameK) ch
      = .ok (.retV (.int 0 .int)
          (.stmtOpK (.makeSlice tU64 true) 1
            [.int 0 .int, .addr (.base ⟨22⟩)] [] rMidEnv
            (.seq [rS4, rS5, rTailSeqn] rMidEnv rFrameK)),
        qSt σ (qHeapR1Mid nv sv n l lp siv civ) 23, ch) := by
  with_unfolding_all rfl

/-- The `rle` prologue, second half: the `$c1` make applied,
`runCounts`, the subject counter and flag → the subject loop head.
43 steps. -/
theorem r_R1b_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 43 (qSt σ (qHeapR1Mid nv sv n l lp siv civ) 23)
      (.retV (.int 0 .int)
        (.stmtOpK (.makeSlice tU64 true) 1
          [.int 0 .int, .addr (.base ⟨22⟩)] [] rMidEnv
          (.seq [rS4, rS5, rTailSeqn] rMidEnv rFrameK))) ch
      = .ok (rHeadCfgQ,
          qSt σ (qHeapRle0 nv sv n l lp siv civ 0 true) 27, ch) := by
  with_unfolding_all rfl

/-! ## The appendSlice SPILL step

-- KIT-GAP WITNESS (see .tmp/kitgaps-rle.md): `SliceMem` has no
-- append/slice-growth vocabulary at all. The two lemmas below are the
-- executable facts this example needs: the backing-builder closed form
-- at one appended element, and the spill arm of `applyStmtOp` with its
-- capacity CHOICE surfaced as an existential envelope `[1, 32]`. -/

/-- `buildAppendBackingValue` at no old values and ONE appended
element: the element, then the capacity pad of zeros. -/
theorem buildAppendBackingValue_one (σ : ExecState) {v : Int}
    (hv : 0 ≤ v ∧ v < 2 ^ 64) {c : Nat} (hc : 1 ≤ c) :
    buildAppendBackingValue σ tU64 #[] #[.int v .uint64] c
      = .ok (.array ⟨(qPadL c v).map (fun x => .int x .uint64)⟩) := by
  have hnorm : normalizeValueForTy σ tU64 (.int v .uint64)
      = .ok (.int v .uint64) := by
    simp only [normalizeValueForTy]
    rw [show typeResolutionFuel = 1023 + 1 from rfl]
    simp only [normalizeValueForTyFuel, unorm_of_range hv.1 hv.2]
    rfl
  simp only [buildAppendBackingValue, Std.Legacy.Range.forIn_eq_forIn_range',
    Bind.bind, Except.bind, pure, Except.pure]
  simp only [show ((#[] : Array GoValue) ++ #[GoValue.int v .uint64])
      = #[GoValue.int v .uint64] from rfl]
  simp only [← Array.forIn_toList, List.toList_toArray, List.forIn_cons,
    List.forIn_nil, hnorm, Bind.bind, Except.bind, pure, Except.pure]
  simp only [show ((#[] : Array GoValue).push (GoValue.int v .uint64))
      = #[GoValue.int v .uint64] from rfl,
    show ((#[GoValue.int v .uint64] : Array GoValue).size) = 1 from rfl]
  rw [if_neg (by omega : ¬ (1 > c))]
  rw [show ([:c - 1] : Std.Legacy.Range).size = c - 1 from by
    simp [Std.Legacy.Range.size]]
  rw [GoLean.Iris.forIn_range'_inv (N := c - 1) (n := c - 1) (j := 0)
    (b := #[GoValue.int v .uint64])
    (Q := fun i acc => acc
      = #[GoValue.int v .uint64] ++ (List.replicate i (GoValue.int 0 .uint64)).toArray)
    (out := fun _ acc => acc.push (.int 0 .uint64))
    (res := #[GoValue.int v .uint64]
      ++ (List.replicate (c - 1) (GoValue.int 0 .uint64)).toArray)
    ?hfill (by omega) (by simp) (by intro b' h; rw [h, Nat.zero_add])]
  · congr 1
    simp [qPadL, List.map_replicate]
  · case hfill =>
      intro i acc hi hacc
      refine ⟨by simp [defaultValue, defaultValueFuel, typeResolutionFuel], ?_⟩
      rw [hacc, List.replicate_succ']
      simp [← List.toArray_replicate]

/-- Setting one key leaves every OTHER key's lookup unchanged (local
plumbing for the spill lemma; the kit's set/lookup laws are all
append-shaped). -/
theorem lookup_set_ne_local {h : Heap} {l l' : Loc} {c : HeapCell}
    (hne : (l' == l) = false) :
    Heap.lookup (Heap.set h l' c) l = Heap.lookup h l := by
  induction h with
  | nil => simp [Heap.set, Heap.lookup, hne]
  | cons p rest ih =>
    obtain ⟨loc, old⟩ := p
    by_cases hb : loc = l'
    · subst hb
      simp [Heap.set, Heap.lookup, hne]
    · simp only [Heap.set, show (loc == l') = false from by simpa using hb,
        Bool.false_eq_true, if_false]
      simp only [Heap.lookup, ih]

/-- **The append-spill executable fact** at this example's shape:
appending a one-element slice onto an EMPTY (cap 0) slice. The spill
allocates a fresh backing at `nextAddr` whose capacity is drawn from
the choice stream — the envelope `[newLen, appendSpillUpper] = [1, 32]`
— and stores the new handle into the target cell. The capacity and the
consumed stream are EXISTENTIAL: nothing downstream may depend on
them beyond the bounds. -/
theorem applyStmtOp_append_spill1 {σ : ExecState} {ta sb eb : Addr}
    {v : Int} {oldv : GoValue}
    (hlookT : Heap.lookup σ.heap (.base ta)
      = some ⟨some (.slice tU64), oldv⟩)
    (hlookE : Heap.lookup σ.heap (.base eb)
      = some ⟨some (.array 1 tU64),
              .array ⟨[v].map (fun x => .int x .uint64)⟩⟩)
    (hv : 0 ≤ v ∧ v < 2 ^ 64)
    (hta : ((Loc.base ⟨σ.nextAddr⟩) == (.base ta)) = false) (ch : Choices) :
    ∃ (cap : Nat) (ch' : Choices), 1 ≤ cap ∧ cap ≤ 32 ∧
      applyStmtOp σ ch (.appendSlice tU64) 1
        [.addr (.base ta), .slice ⟨some (.base sb), 0, 0, 0⟩,
         .slice ⟨some (.base eb), 0, 1, 1⟩]
        = .ok ({ σ with
            heap := Heap.set
              (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
                ⟨some (.array cap tU64),
                 .array ⟨(qPadL cap v).map (fun x => .int x .uint64)⟩⟩)
              (.base ta)
              ⟨some (.slice tU64),
               .slice ⟨some (.base ⟨σ.nextAddr⟩), 0, 1, cap⟩⟩,
            nextAddr := σ.nextAddr + 1 }, ch') := by
  -- the elems slice's visible values: the one element at `eb[0]`
  have hload : loadLoc σ (Loc.index (.base eb) (Int.ofNat (0 + 0)))
      = .ok (.int v .uint64) := by
    simp only [loadLoc, hlookE]
    rfl
  have hvis : sliceVisibleValues σ ⟨some (.base eb), 0, 1, 1⟩
      = .ok #[.int v .uint64] := by
    simp only [sliceVisibleValues, validateSlice,
      Std.Legacy.Range.forIn_eq_forIn_range', Bind.bind, Except.bind,
      pure, Except.pure]
    rw [show ([:(1 : Nat)] : Std.Legacy.Range).size = 1 from by
      simp [Std.Legacy.Range.size]]
    simp only [List.range'_one, List.forIn'_cons, List.forIn'_nil,
      Bind.bind, Except.bind, pure, Except.pure]
    simp [sliceIndexLoc, validateSlice, Bind.bind, Except.bind, pure,
      Except.pure, loadLoc, hlookE, arrayGet, arrayIndexNat]
  have hvis0 : sliceVisibleValues σ ⟨some (.base sb), 0, 0, 0⟩
      = .ok #[] := by
    simp only [sliceVisibleValues, validateSlice,
      Std.Legacy.Range.forIn_eq_forIn_range', Bind.bind, Except.bind,
      pure, Except.pure]
    rw [show ([:(0 : Nat)] : Std.Legacy.Range).size = 0 from by
      simp [Std.Legacy.Range.size]]
    simp [forIn, List.forIn', List.forIn'.loop]
  have hmain : ∀ (extra : Nat) (rest' : Choices),
      Choices.consume ch 32 = (extra, rest') → extra < 32 →
      applyStmtOp σ ch (.appendSlice tU64) 1
        [.addr (.base ta), .slice ⟨some (.base sb), 0, 0, 0⟩,
         .slice ⟨some (.base eb), 0, 1, 1⟩]
        = .ok ({ σ with
            heap := Heap.set
              (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
                ⟨some (.array (1 + ((3 + extra) % 32)) tU64),
                 .array ⟨(qPadL (1 + ((3 + extra) % 32)) v).map
                   (fun x => .int x .uint64)⟩⟩)
              (.base ta)
              ⟨some (.slice tU64),
               .slice ⟨some (.base ⟨σ.nextAddr⟩), 0, 1,
                 1 + ((3 + extra) % 32)⟩⟩,
            nextAddr := σ.nextAddr + 1 }, rest') := by
    intro extra rest' hcons hlt
    have hbuild := buildAppendBackingValue_one σ hv
      (c := 1 + ((3 + extra) % 32)) (by omega)
    have hval0 : validateSlice ⟨some (.base sb), 0, 0, 0⟩ = .ok () := rfl
    have hval1 : validateSlice ⟨some (.base eb), 0, 1, 1⟩ = .ok () := rfl
    have hnorms : ∀ (σ' : ExecState) (sv : SliceValue),
        normalizeValueForTy σ' (.slice tU64) (.slice sv)
          = .ok (.slice sv) := by
      intro σ' sv
      simp only [normalizeValueForTy]
      rw [show typeResolutionFuel = 1023 + 1 from rfl]
      rfl
    simp only [applyStmtOp, valueAsSlice, hval0, hval1, valueAsLoc,
      hvis, hvis0, Bind.bind, Except.bind, pure, Except.pure]
    simp only [List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add]
    rw [if_neg (by omega : ¬ (0 + 1 ≤ 0))]
    simp only [show appendSpillWidth 0 (0 + 1) = 32 from rfl,
      show appendGrowthCap 0 (0 + 1) = 4 from rfl, hcons]
    rw [show 0 + 1 + (4 - (0 + 1) + extra) % 32 = 1 + ((3 + extra) % 32)
      from by omega]
    rw [hbuild]
    simp only [ExecState.alloc, ExecState.freshLoc, storeLoc,
      lookup_set_ne_local hta, hlookT, hnorms, Bind.bind, Except.bind,
      pure, Except.pure]
  rcases ch with _ | ⟨c, rest⟩
  · exact ⟨1 + ((3 + 0) % 32), [], by omega, by omega,
      hmain 0 [] rfl (by omega)⟩
  · exact ⟨1 + ((3 + c % 32) % 32), rest, by omega,
      by have := Nat.mod_lt (3 + c % 32) (y := 32) (by omega); omega,
      hmain (c % 32) rest rfl (Nat.mod_lt _ (by omega))⟩

end GoLean.Examples.RunLength
