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
gaps in the campaign log (`docs/gallery-campaign-log/g1.md § KIT-GAP LIST (rle)`, lane B). Nothing here
weakens fail-closed behavior: the theorem simply does not claim
`n > 3`.

## Kit gaps witnessed in this module

* `applyStrictOp_div_u64` — the kit has the `%` executable fact only;
  `/` is re-derived locally below (GAP-WITNESS).
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

/-! ## The `/` executable fact — LIFTED (WP arc s1 lift 1): the proof
moved to `SliceMem.applyStrictOp_div_u64`; this name survives as a
zero-proof-line delegation under its original signature (the audit
shard's roll-call names it; the kit form drops the unused `b < 2^64`
hypothesis, absorbed here). -/

theorem applyStrictOp_div_u64 {σ : ExecState} {a b : Nat}
    (ha : a < 2 ^ 64) (hb : 0 < b) (hb64 : b < 2 ^ 64) :
    applyStrictOp σ .div [.int (a : Int) .uint64, .int (b : Int) .uint64]
      = .ok (.int ((a / b : Nat) : Int) .uint64, σ) :=
  SliceMem.applyStrictOp_div_u64 hb ha

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

-- GAP-WITNESS (see docs/gallery-campaign-log/g1.md § KIT-GAP LIST (rle)): `SliceMem` has no
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
  -- WP arc s2 item 3: the forIn fight replaced by the kit's generic
  -- builder closed form.
  have hnorm : ∀ x ∈ ([] : List GoValue) ++ [GoValue.int v .uint64],
      normalizeValueForTy σ tU64 x = .ok x := by
    intro x hx
    simp only [List.nil_append, List.mem_singleton] at hx
    subst hx
    simp only [normalizeValueForTy]
    rw [show typeResolutionFuel = 1023 + 1 from rfl]
    simp only [normalizeValueForTyFuel, unorm_of_range hv.1 hv.2]
    rfl
  have h := SliceMem.buildAppendBackingValue_of_norm (σ := σ)
    (l₁ := []) (l₂ := [.int v .uint64]) (newCap := c)
    (d := .int 0 .uint64) hnorm
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
    (by simpa using hc)
  rw [h]
  congr 2
  simp [qPadL, List.map_replicate]

/-- Setting one key leaves every OTHER key's lookup unchanged (the
beq-hypothesis view of the core's `Heap.lookup_set_ne`; a zero-proof
delegation since WP arc s2 item 1). -/
theorem lookup_set_ne_local {h : Heap} {l l' : Loc} {c : HeapCell}
    (hne : (l' == l) = false) :
    Heap.lookup (Heap.set h l' c) l = Heap.lookup h l :=
  Machine.Heap.lookup_set_ne (fun heq => by subst heq; simp at hne)

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
  -- WP arc s2 item 3: the applyStmtOp unfolding and the choice-stream
  -- case split replaced by the kit's envelope existential
  -- `SliceMem.applyStmtOp_append1_spill_ex`; the per-type facts
  -- (visible values, the builder, the handle store) discharge its
  -- hypotheses.
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
  have hnorms : ∀ (σ' : ExecState) (sv : SliceValue),
      normalizeValueForTy σ' (.slice tU64) (.slice sv)
        = .ok (.slice sv) := by
    intro σ' sv
    simp only [normalizeValueForTy]
    rw [show typeResolutionFuel = 1023 + 1 from rfl]
    rfl
  obtain ⟨newCap, ch', h1, h2, happly⟩ :=
    SliceMem.applyStmtOp_append1_spill_ex (σ := σ) (elem := tU64)
      (tloc := .base ta) (bb := .base sb) (off := 0) (len := 0)
      (cap := 0) (eb := .base eb) (eoff := 0) (elen := 1) (ecap := 1)
      (w := .int v .uint64) (old := #[])
      (bk := fun nc => .array ⟨(qPadL nc v).map (fun x => .int x .uint64)⟩)
      (σT := fun nc => { σ with
          heap := Heap.set
            (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
              ⟨some (.array nc tU64),
               .array ⟨(qPadL nc v).map (fun x => .int x .uint64)⟩⟩)
            (.base ta)
            ⟨some (.slice tU64),
             .slice ⟨some (.base ⟨σ.nextAddr⟩), 0, 1, nc⟩⟩,
          nextAddr := σ.nextAddr + 1 })
      (ch := ch)
      (by omega) (by omega) (by omega) hvis hvis0
      (fun nc hnc => buildAppendBackingValue_one σ hv hnc)
      (fun nc hnc => by
        simp only [storeLoc, lookup_set_ne_local hta, hlookT, hnorms,
          Bind.bind, Except.bind, pure, Except.pure])
  refine ⟨newCap, ch', by omega, ?_, happly⟩
  have hup : appendSpillUpper 0 (0 + 1) = 32 := rfl
  omega

/-! ## The subject loop — raw segments

Iteration `i = 0` is THE NEW-RUN EVENT (both `append`s spill —
`runVals`/`runCounts` have cap 0); iterations `i = 1, 2` extend. The
`k`/`extended` cells are allocated afresh EVERY iteration, so extend
segments are stated at their literal addresses. -/

/-- Subject head, first dispatch: flag → `i` read → the `len(s)` apply
point. 25 steps. -/
theorem r_A0_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 25 (qSt σ (qHeapRle0 nv sv n l lp siv civ 0 true) 27)
      rHeadCfgQ ch
      = .ok (.retV (qSliceS n) (rLenSK 0),
          qSt σ (qHeapRle0 nv sv n l lp siv civ 0 false) 27, ch) := by
  with_unfolding_all rfl

/-- Test true at `i = 0` → the `k := len(runVals)` apply point
(`k`'s cell allocated). 14 steps. -/
theorem r_i0_a_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 14 (qSt σ (qHeapRle0 nv sv n l lp siv civ 0 false) 27)
      (.retV (.bool true) rCmpKQ) ch
      = .ok (.retV (qESliceV 20) (rKLenK 27),
          qSt σ (qHeapRle0 nv sv n l lp siv civ 0 false
            ++ [(.base ⟨27⟩, qint 0)]) 28, ch) := by
  with_unfolding_all rfl

/-- `k = 0` delivered → through `extended := false`, the `k > 0` guard
(false), `!extended` (true), the `$c2` make and its store target → the
`s[i]` read point. 55 steps. -/
theorem r_i0_b_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 55 (qSt σ (qHeapRle0 nv sv n l lp siv civ 0 false
        ++ [(.base ⟨27⟩, qint 0)]) 28)
      (.retV (.int 0 .int)
        (.rhsK .vals [.chain (.addr (.base ⟨27⟩)) [] []] [] [] (.seqn #[])
          (rKEnv 27) (rKTailK 27))) ch
      = .ok (.retV (.int 0 .int)
          (.strictK .indexGet [qSliceS n] [] rNREnv1
            (.rhsK .vals [rC2Ref] [] [] (.seqn #[]) rNREnv1 rNRTail1)),
        qSt σ (qHeapRle0 nv sv n l lp siv civ 0 false
          ++ [(.base ⟨27⟩, qint 0), (.base ⟨28⟩, qbool false),
              (.base ⟨29⟩, qC1Slice 30), (.base ⟨30⟩, qBack1 0)]) 31,
        ch) := by
  with_unfolding_all rfl

/-- `s[0]` delivered → the pending `$c2[0]` store. 1 step. -/
theorem r_i0_c_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1 (qSt σ (qHeapRle0 nv sv n l lp siv civ 0 false
        ++ [(.base ⟨27⟩, qint 0), (.base ⟨28⟩, qbool false),
            (.base ⟨29⟩, qC1Slice 30), (.base ⟨30⟩, qBack1 0)]) 31)
      (.retV w (.rhsK .vals [rC2Ref] [] [] (.seqn #[]) rNREnv1 rNRTail1))
      ch
      = .ok (.next (.storeK [rC2Ref] [w] (.seqn #[]) rNREnv1 rNRTail1),
          qSt σ (qHeapRle0 nv sv n l lp siv civ 0 false
            ++ [(.base ⟨27⟩, qint 0), (.base ⟨28⟩, qbool false),
                (.base ⟨29⟩, qC1Slice 30), (.base ⟨30⟩, qBack1 0)]) 31,
          ch) := by
  with_unfolding_all rfl

/-- The `$c2[0]` store done → `$c3` declared → the FIRST `appendSlice`
apply point. 13 steps. -/
theorem r_i0_d_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (v : Int) (ch : Choices) :
    stepFnIter 13 (qSt σ (qHeapRle0 nv sv n l lp siv civ 0 false
        ++ [(.base ⟨27⟩, qint 0), (.base ⟨28⟩, qbool false),
            (.base ⟨29⟩, qC1Slice 30), (.base ⟨30⟩, qBack1 v)]) 31)
      (.next (.storeK [] [] (.seqn #[]) rNREnv1 rNRTail1)) ch
      = .ok (.retV (qC1SliceV 30)
          (.stmtOpK (.appendSlice tU64) 1
            [qESliceV 20, .addr (.base ⟨31⟩)] [] rNREnv2 rNRTail2),
        qSt σ (qHeapRle0 nv sv n l lp siv civ 0 false
          ++ [(.base ⟨27⟩, qint 0), (.base ⟨28⟩, qbool false),
              (.base ⟨29⟩, qC1Slice 30), (.base ⟨30⟩, qBack1 v),
              (.base ⟨31⟩, qNilSlice)]) 32, ch) := by
  with_unfolding_all rfl

/-- After the first append: `runVals := $c3`, the `$c4` make and its
literal store, `$c5` declared → the SECOND `appendSlice` apply point.
45 steps. -/
theorem r_i0_e_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (v : Int) (capV : Nat) (ch : Choices) :
    stepFnIter 45 (qSt σ (qHeapRle0 nv sv n l lp siv civ 0 false
        ++ [(.base ⟨27⟩, qint 0), (.base ⟨28⟩, qbool false),
            (.base ⟨29⟩, qC1Slice 30), (.base ⟨30⟩, qBack1 v),
            (.base ⟨31⟩, qRunSlice 32 capV), (.base ⟨32⟩, qBackPad capV v)])
        33)
      (.next rNRTail2) ch
      = .ok (.retV (qC1SliceV 34)
          (.stmtOpK (.appendSlice tU64) 1
            [qESliceV 23, .addr (.base ⟨35⟩)] [] rNREnv4 rNRTail4),
        qSt σ (qHeapRle0' nv sv n l lp siv civ capV
          ++ [(.base ⟨27⟩, qint 0), (.base ⟨28⟩, qbool false),
              (.base ⟨29⟩, qC1Slice 30), (.base ⟨30⟩, qBack1 v),
              (.base ⟨31⟩, qRunSlice 32 capV), (.base ⟨32⟩, qBackPad capV v),
              (.base ⟨33⟩, qC1Slice 34), (.base ⟨34⟩, qBack1 1),
              (.base ⟨35⟩, qNilSlice)]) 36, ch) := by
  with_unfolding_all rfl

/-- After the second append: `runCounts := $c5`, pops → the loop head.
15 steps. -/
theorem r_i0_f_rawQ (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (v : Int) (capV capC : Nat) (ch : Choices) :
    stepFnIter 15 (qSt σ (qHeapRle0' nv sv n l lp siv civ capV
        ++ [(.base ⟨27⟩, qint 0), (.base ⟨28⟩, qbool false),
            (.base ⟨29⟩, qC1Slice 30), (.base ⟨30⟩, qBack1 v),
            (.base ⟨31⟩, qRunSlice 32 capV), (.base ⟨32⟩, qBackPad capV v),
            (.base ⟨33⟩, qC1Slice 34), (.base ⟨34⟩, qBack1 1),
            (.base ⟨35⟩, qRunSlice 36 capC), (.base ⟨36⟩, qBackPad capC 1)])
        37)
      (.next rNRTail4) ch
      = .ok (rHeadCfgQ,
          qSt σ (qHeapRun nv sv n l lp siv civ capV capC v 1 0 false []) 37,
          ch) := by
  with_unfolding_all rfl

/-! ## The extend iterations — raw segments

Two literal instances (`k` at 37 for `i = 1`, at 39 for `i = 2`): raw
segments need literal addresses, and each iteration allocates its own
`k`/`extended` pair. -/

/-- The integer `==` apply step, PROGRAM- and STATE-generic (the
result is the symbolic `Bool` the machine computes; the composition
rewrites it). -/
theorem r_eq_apply (σ : ExecState) (a b : Int) (env : LocalEnv) (k : Cont)
    (ch : Choices) :
    stepFnIter 1 σ
      (.retV (.int b .uint64)
        (.strictK (.eqCmp tU64) [.int a .uint64] [] env k)) ch
      = .ok (.retV (.bool (a == b)) k, σ, ch) := by
  with_unfolding_all rfl

/-- Later-dispatch at the subject head (`$forFirst` false): `i++` →
the `len(s)` apply point. 29 steps. Instance: after iteration 0. -/
theorem r_A1_raw37 (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (capV capC : Nat) (v cnt iv : Int) (ch : Choices) :
    stepFnIter 29
      (qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false []) 37)
      rHeadCfgQ ch
      = .ok (.retV (qSliceS n)
          (rLenSK (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
        qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt
          (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
          false []) 37, ch) := by
  with_unfolding_all rfl

/-- Same, after iteration 1 (`ke1` garbage, `nextAddr` 39). -/
theorem r_A1_raw39 (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (capV capC : Nat) (v cnt iv : Int) (ch : Choices) :
    stepFnIter 29
      (qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false ke1) 39)
      rHeadCfgQ ch
      = .ok (.retV (qSliceS n)
          (rLenSK (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
        qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt
          (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
          false ke1) 39, ch) := by
  with_unfolding_all rfl

/-- Same, after iteration 2 (`ke2`, `nextAddr` 41 — the `n = 3` exit
dispatch). -/
theorem r_A1_raw41 (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (capV capC : Nat) (v cnt iv : Int) (ch : Choices) :
    stepFnIter 29
      (qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false ke2) 41)
      rHeadCfgQ ch
      = .ok (.retV (qSliceS n)
          (rLenSK (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
        qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt
          (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
          false ke2) 41, ch) := by
  with_unfolding_all rfl

/-- Extend, phase a: test true → the `k := len(runVals)` apply point.
14 steps. -/
theorem r_ext_a37 (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (capV capC : Nat) (v cnt iv : Int) (ch : Choices) :
    stepFnIter 14
      (qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false []) 37)
      (.retV (.bool true) rCmpKQ) ch
      = .ok (.retV (qRunSliceV 32 capV) (rKLenK 37),
        qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
          [(.base ⟨37⟩, qint 0)]) 38, ch) := by
  with_unfolding_all rfl

theorem r_ext_a39 (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (capV capC : Nat) (v cnt iv : Int) (ch : Choices) :
    stepFnIter 14
      (qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false ke1) 39)
      (.retV (.bool true) rCmpKQ) ch
      = .ok (.retV (qRunSliceV 32 capV) (rKLenK 39),
        qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
          (ke1 ++ [(.base ⟨39⟩, qint 0)])) 40, ch) := by
  with_unfolding_all rfl

/-- Extend, phase b: `k = 1` delivered → `extended := false`, the
`k > 0` guard (true) → the `runVals[k-1]` read point. 37 steps. -/
theorem r_ext_b37 (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (capV capC : Nat) (v cnt iv : Int) (ch : Choices) :
    stepFnIter 37
      (qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
        [(.base ⟨37⟩, qint 0)]) 38)
      (.retV (.int 1 .int)
        (.rhsK .vals [.chain (.addr (.base ⟨37⟩)) [] []] [] [] (.seqn #[])
          (rKEnv 37) (rKTailK 37))) ch
      = .ok (.retV (.int 0 .int) (rExtEqK 37 capV),
        qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
          [(.base ⟨37⟩, qint 1), (.base ⟨38⟩, qbool false)]) 39, ch) := by
  with_unfolding_all rfl

theorem r_ext_b39 (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (capV capC : Nat) (v cnt iv : Int) (ch : Choices) :
    stepFnIter 37
      (qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
        (ke1 ++ [(.base ⟨39⟩, qint 0)])) 40)
      (.retV (.int 1 .int)
        (.rhsK .vals [.chain (.addr (.base ⟨39⟩)) [] []] [] [] (.seqn #[])
          (rKEnv 39) (rKTailK 39))) ch
      = .ok (.retV (.int 0 .int) (rExtEqK 39 capV),
        qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
          (ke1 ++ [(.base ⟨39⟩, qint 1), (.base ⟨40⟩, qbool false)])) 41,
        ch) := by
  with_unfolding_all rfl

/-- Extend, phase c: `runVals[0]` banked → the `s[i]` read point.
5 steps. -/
theorem r_ext_c37 (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (capV capC : Nat) (v cnt iv a : Int) (ch : Choices) :
    stepFnIter 5
      (qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
        [(.base ⟨37⟩, qint 1), (.base ⟨38⟩, qbool false)]) 39)
      (.retV (.int a .uint64)
        (.strictK (.eqCmp tU64) [] [.indexGet (.var "s") (.var "i")]
          (rExtGuardEnv 37) (rExtIfK 37))) ch
      = .ok (.retV (.int iv .int) (rExtEq2K n 37 a),
        qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
          [(.base ⟨37⟩, qint 1), (.base ⟨38⟩, qbool false)]) 39, ch) := by
  with_unfolding_all rfl

theorem r_ext_c39 (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (capV capC : Nat) (v cnt iv a : Int) (ch : Choices) :
    stepFnIter 5
      (qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
        (ke1 ++ [(.base ⟨39⟩, qint 1), (.base ⟨40⟩, qbool false)])) 41)
      (.retV (.int a .uint64)
        (.strictK (.eqCmp tU64) [] [.indexGet (.var "s") (.var "i")]
          (rExtGuardEnv 39) (rExtIfK 39))) ch
      = .ok (.retV (.int iv .int) (rExtEq2K n 39 a),
        qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
          (ke1 ++ [(.base ⟨39⟩, qint 1), (.base ⟨40⟩, qbool false)])) 41,
        ch) := by
  with_unfolding_all rfl

/-- Extend, phase d: the pair matched → into the extend arm, to the
`runCounts[k-1]` read point. 21 steps. -/
theorem r_ext_d37 (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (capV capC : Nat) (v cnt iv : Int) (ch : Choices) :
    stepFnIter 21
      (qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
        [(.base ⟨37⟩, qint 1), (.base ⟨38⟩, qbool false)]) 39)
      (.retV (.bool true) (rExtIfK 37)) ch
      = .ok (.retV (.int 0 .int) (rExtCntReadK 37 capC),
        qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
          [(.base ⟨37⟩, qint 1), (.base ⟨38⟩, qbool false)]) 39, ch) := by
  with_unfolding_all rfl

theorem r_ext_d39 (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (capV capC : Nat) (v cnt iv : Int) (ch : Choices) :
    stepFnIter 21
      (qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
        (ke1 ++ [(.base ⟨39⟩, qint 1), (.base ⟨40⟩, qbool false)])) 41)
      (.retV (.bool true) (rExtIfK 39)) ch
      = .ok (.retV (.int 0 .int) (rExtCntReadK 39 capC),
        qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
          (ke1 ++ [(.base ⟨39⟩, qint 1), (.base ⟨40⟩, qbool false)])) 41,
        ch) := by
  with_unfolding_all rfl

/-- Extend, phase e: `runCounts[0]` banked → `+ 1` → the pending
element store. 4 steps. -/
theorem r_ext_e37 (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (capV capC : Nat) (v cnt iv cv : Int) (ch : Choices) :
    stepFnIter 4
      (qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
        [(.base ⟨37⟩, qint 1), (.base ⟨38⟩, qbool false)]) 39)
      (.retV (.int cv .uint64)
        (.strictK .add [] [.intLit 1 .uint64] (rExtBEnv 37)
          (rExtRhsK 37 capC))) ch
      = .ok (.next (.storeK [rCntRef capC]
            [.int (IntKind.normalize .uint64 (cv + 1)) .uint64]
            (.seqn #[]) (rExtBEnv 37) (rExtStTail 37)),
        qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
          [(.base ⟨37⟩, qint 1), (.base ⟨38⟩, qbool false)]) 39, ch) := by
  with_unfolding_all rfl

theorem r_ext_e39 (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (capV capC : Nat) (v cnt iv cv : Int) (ch : Choices) :
    stepFnIter 4
      (qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
        (ke1 ++ [(.base ⟨39⟩, qint 1), (.base ⟨40⟩, qbool false)])) 41)
      (.retV (.int cv .uint64)
        (.strictK .add [] [.intLit 1 .uint64] (rExtBEnv 39)
          (rExtRhsK 39 capC))) ch
      = .ok (.next (.storeK [rCntRef capC]
            [.int (IntKind.normalize .uint64 (cv + 1)) .uint64]
            (.seqn #[]) (rExtBEnv 39) (rExtStTail 39)),
        qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
          (ke1 ++ [(.base ⟨39⟩, qint 1), (.base ⟨40⟩, qbool false)])) 41,
        ch) := by
  with_unfolding_all rfl

/-- Extend, phase f: the store done → `extended := true`, `!extended`
skips the new-run arm, pops → the loop head. 25 steps. -/
theorem r_ext_f37 (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (capV capC : Nat) (v cnt iv : Int) (ch : Choices) :
    stepFnIter 25
      (qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
        [(.base ⟨37⟩, qint 1), (.base ⟨38⟩, qbool false)]) 39)
      (.next (.storeK [] [] (.seqn #[]) (rExtBEnv 37) (rExtStTail 37))) ch
      = .ok (rHeadCfgQ,
        qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
          ke1) 39, ch) := by
  with_unfolding_all rfl

theorem r_ext_f39 (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (capV capC : Nat) (v cnt iv : Int) (ch : Choices) :
    stepFnIter 25
      (qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
        (ke1 ++ [(.base ⟨39⟩, qint 1), (.base ⟨40⟩, qbool false)])) 41)
      (.next (.storeK [] [] (.seqn #[]) (rExtBEnv 39) (rExtStTail 39))) ch
      = .ok (rHeadCfgQ,
        qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false
          ke2) 41, ch) := by
  with_unfolding_all rfl

/-! ## The subject exit, the final copy loop and the epilogue

Per-`n` literal instances: the four post-return cells live at
`A = 37/39/41` for `n = 1/2/3` (and 27 for `n = 0`), because each
extend iteration left two garbage cells behind. -/

/-- Subject exit (`n = 3` layout): test false → break → the subject's
epilogue (`$res0/$res1 :=` the run slices) → the frame return delivers
them into `vals`/`counts` → `runVals`/`runCounts` arrays and the final
copy counter/flag declared → the final-copy head. 75 steps. -/
theorem r_exit_raw41 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (ch : Choices) :
    stepFnIter 75
      (qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false ke2) 41)
      (.retV (.bool false) rCmpKQ) ch
      = .ok (fcHeadCfg 41,
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke2
          zeros8 zeros8 0 true 41) 45, ch) := by
  with_unfolding_all rfl

/-- Final-copy head, first dispatch → the `len(vals)` apply point.
25 steps. -/
theorem fc_A0_raw41 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (ch : Choices) :
    stepFnIter 25
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke2
        rv rc 0 true 41) 45) (fcHeadCfg 41) ch
      = .ok (.retV (qRunSliceV 32 capV) (fcLenSK 41 0),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke2
          rv rc 0 false 41) 45, ch) := by
  with_unfolding_all rfl

/-- Final-copy head, later dispatch (`i++`) → the `len(vals)` apply
point. 29 steps. -/
theorem fc_A1_raw41 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 29
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke2
        rv rc fiv false 41) 45) (fcHeadCfg 41) ch
      = .ok (.retV (qRunSliceV 32 capV)
          (fcLenSK 41
            (IntKind.normalize .int (IntKind.normalize .int (fiv + 1)))),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke2
          rv rc (IntKind.normalize .int (IntKind.normalize .int (fiv + 1)))
          false 41) 45, ch) := by
  with_unfolding_all rfl

/-- Final-copy body: test true → the `vals[i]` read point. 16 steps. -/
theorem fc_b_raw41 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 16
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke2
        rv rc fiv false 41) 45)
      (.retV (.bool true) (fcCmpK 41)) ch
      = .ok (.retV (.int fiv .int) (fcVReadK 41 capV fiv),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke2
          rv rc fiv false 41) 45, ch) := by
  with_unfolding_all rfl

/-- `vals[i]` delivered → the pending `runVals[i]` store. 1 step. -/
theorem fc_c_raw41 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke2
        rv rc fiv false 41) 45)
      (.retV w (fcVRhsK 41 fiv)) ch
      = .ok (.next (.storeK [fcVRef 41 fiv] [w] (.seqn #[]) (fcEnvB2 41)
            (fcStTail1 41)),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke2
          rv rc fiv false 41) 45, ch) := by
  with_unfolding_all rfl

/-- The first store done → the `counts[i]` read point. 14 steps. -/
theorem fc_d_raw41 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 14
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke2
        rv rc fiv false 41) 45)
      (.next (.storeK [] [] (.seqn #[]) (fcEnvB2 41) (fcStTail1 41))) ch
      = .ok (.retV (.int fiv .int) (fcCReadK 41 capC fiv),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke2
          rv rc fiv false 41) 45, ch) := by
  with_unfolding_all rfl

/-- `counts[i]` delivered → the pending `runCounts[i]` store. 1 step. -/
theorem fc_e_raw41 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke2
        rv rc fiv false 41) 45)
      (.retV w (fcCRhsK 41 fiv)) ch
      = .ok (.next (.storeK [fcCRef 41 fiv] [w] (.seqn #[]) (fcEnvB2 41)
            (fcStTail2 41)),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke2
          rv rc fiv false 41) 45, ch) := by
  with_unfolding_all rfl

/-- The second store done → the loop head. 5 steps. -/
theorem fc_f_raw41 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 5
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke2
        rv rc fiv false 41) 45)
      (.next (.storeK [] [] (.seqn #[]) (fcEnvB2 41) (fcStTail2 41))) ch
      = .ok (fcHeadCfg 41,
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke2
          rv rc fiv false 41) 45, ch) := by
  with_unfolding_all rfl

/-- Final-copy exit: test false → break → the harness epilogue up to
the pending `$res0 = pre` store. 14 steps. -/
theorem ep_a_raw41 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 14
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke2
        rv rc fiv false 41) 45)
      (.retV (.bool false) (fcCmpK 41)) ch
      = .ok (.next (.storeK [qRes0Ref]
            [.array ⟨lp.map (fun x => .int x .uint64)⟩] (.seqn #[])
            (fcTopEnv 41) (epK 41 [epA1, epA2, epA3, .returnStmt])),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke2
          rv rc fiv false 41) 45, ch) := by
  with_unfolding_all rfl

/-- `$res0` stored → the pending `$res1 = runVals` store. 8 steps. -/
theorem ep_b_raw41 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 8
      (qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ke2
        rv rc fiv 41 lp zeros8 zeros8) 45)
      (.next (.storeK [] [] (.seqn #[]) (fcTopEnv 41)
        (epK 41 [epA1, epA2, epA3, .returnStmt]))) ch
      = .ok (.next (.storeK [qRes1Ref]
            [.array ⟨rv.map (fun x => .int x .uint64)⟩] (.seqn #[])
            (fcTopEnv 41) (epK 41 [epA2, epA3, .returnStmt])),
        qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ke2
          rv rc fiv 41 lp zeros8 zeros8) 45, ch) := by
  with_unfolding_all rfl

/-- `$res1` stored → the pending `$res2 = runCounts` store. 8 steps. -/
theorem ep_c_raw41 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 8
      (qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ke2
        rv rc fiv 41 lp rv zeros8) 45)
      (.next (.storeK [] [] (.seqn #[]) (fcTopEnv 41)
        (epK 41 [epA2, epA3, .returnStmt]))) ch
      = .ok (.next (.storeK [qRes2Ref]
            [.array ⟨rc.map (fun x => .int x .uint64)⟩] (.seqn #[])
            (fcTopEnv 41) (epK 41 [epA3, .returnStmt])),
        qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ke2
          rv rc fiv 41 lp rv zeros8) 45, ch) := by
  with_unfolding_all rfl

/-- `$res2` stored → the `len(vals)` apply point inside
`$res3 = uint64(len(vals))`. 9 steps. -/
theorem ep_d_raw41 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 9
      (qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ke2
        rv rc fiv 41 lp rv rc) 45)
      (.next (.storeK [] [] (.seqn #[]) (fcTopEnv 41)
        (epK 41 [epA3, .returnStmt]))) ch
      = .ok (.retV (qRunSliceV 32 capV)
          (.strictK (.lengthOf (some (.slice tU64))) [] [] (fcTopEnv 41)
            (.strictK (.convert tU64) [] [] (fcTopEnv 41)
              (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
                (.seqn #[]) (fcTopEnv 41) (epK 41 [.returnStmt])))),
        qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ke2
          rv rc fiv 41 lp rv rc) 45, ch) := by
  with_unfolding_all rfl

/-- The length delivered → convert, the `$res3` store (a concrete
scalar — raw), return, the frame pops → the DRIVER TERMINAL. 9 steps. -/
theorem ep_e_raw41 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 9
      (qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ke2
        rv rc fiv 41 lp rv rc) 45)
      (.retV (.int 1 .int)
        (.strictK (.convert tU64) [] [] (fcTopEnv 41)
          (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
            (.seqn #[]) (fcTopEnv 41) (epK 41 [.returnStmt])))) ch
      = .ok (.next .stop,
        qSt σ (qHeapEnd1 nv sv n l lp siv civ capV capC v cnt 1 iv ke2
          rv rc fiv 41) 45, ch) := by
  with_unfolding_all rfl

/-- Subject exit (layout for A = 39): test false → break → the subject's
epilogue (`$res0/$res1 :=` the run slices) → the frame return delivers
them into `vals`/`counts` → `runVals`/`runCounts` arrays and the final
copy counter/flag declared → the final-copy head. 75 steps. -/
theorem r_exit_raw39 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (ch : Choices) :
    stepFnIter 75
      (qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false ke1) 39)
      (.retV (.bool false) rCmpKQ) ch
      = .ok (fcHeadCfg 39,
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke1
          zeros8 zeros8 0 true 39) 43, ch) := by
  with_unfolding_all rfl

/-- Final-copy head, first dispatch → the `len(vals)` apply point.
25 steps. -/
theorem fc_A0_raw39 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (ch : Choices) :
    stepFnIter 25
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke1
        rv rc 0 true 39) 43) (fcHeadCfg 39) ch
      = .ok (.retV (qRunSliceV 32 capV) (fcLenSK 39 0),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke1
          rv rc 0 false 39) 43, ch) := by
  with_unfolding_all rfl

/-- Final-copy head, later dispatch (`i++`) → the `len(vals)` apply
point. 29 steps. -/
theorem fc_A1_raw39 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 29
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke1
        rv rc fiv false 39) 43) (fcHeadCfg 39) ch
      = .ok (.retV (qRunSliceV 32 capV)
          (fcLenSK 39
            (IntKind.normalize .int (IntKind.normalize .int (fiv + 1)))),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke1
          rv rc (IntKind.normalize .int (IntKind.normalize .int (fiv + 1)))
          false 39) 43, ch) := by
  with_unfolding_all rfl

/-- Final-copy body: test true → the `vals[i]` read point. 16 steps. -/
theorem fc_b_raw39 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 16
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke1
        rv rc fiv false 39) 43)
      (.retV (.bool true) (fcCmpK 39)) ch
      = .ok (.retV (.int fiv .int) (fcVReadK 39 capV fiv),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke1
          rv rc fiv false 39) 43, ch) := by
  with_unfolding_all rfl

/-- `vals[i]` delivered → the pending `runVals[i]` store. 1 step. -/
theorem fc_c_raw39 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke1
        rv rc fiv false 39) 43)
      (.retV w (fcVRhsK 39 fiv)) ch
      = .ok (.next (.storeK [fcVRef 39 fiv] [w] (.seqn #[]) (fcEnvB2 39)
            (fcStTail1 39)),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke1
          rv rc fiv false 39) 43, ch) := by
  with_unfolding_all rfl

/-- The first store done → the `counts[i]` read point. 14 steps. -/
theorem fc_d_raw39 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 14
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke1
        rv rc fiv false 39) 43)
      (.next (.storeK [] [] (.seqn #[]) (fcEnvB2 39) (fcStTail1 39))) ch
      = .ok (.retV (.int fiv .int) (fcCReadK 39 capC fiv),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke1
          rv rc fiv false 39) 43, ch) := by
  with_unfolding_all rfl

/-- `counts[i]` delivered → the pending `runCounts[i]` store. 1 step. -/
theorem fc_e_raw39 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke1
        rv rc fiv false 39) 43)
      (.retV w (fcCRhsK 39 fiv)) ch
      = .ok (.next (.storeK [fcCRef 39 fiv] [w] (.seqn #[]) (fcEnvB2 39)
            (fcStTail2 39)),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke1
          rv rc fiv false 39) 43, ch) := by
  with_unfolding_all rfl

/-- The second store done → the loop head. 5 steps. -/
theorem fc_f_raw39 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 5
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke1
        rv rc fiv false 39) 43)
      (.next (.storeK [] [] (.seqn #[]) (fcEnvB2 39) (fcStTail2 39))) ch
      = .ok (fcHeadCfg 39,
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke1
          rv rc fiv false 39) 43, ch) := by
  with_unfolding_all rfl

/-- Final-copy exit: test false → break → the harness epilogue up to
the pending `$res0 = pre` store. 14 steps. -/
theorem ep_a_raw39 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 14
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke1
        rv rc fiv false 39) 43)
      (.retV (.bool false) (fcCmpK 39)) ch
      = .ok (.next (.storeK [qRes0Ref]
            [.array ⟨lp.map (fun x => .int x .uint64)⟩] (.seqn #[])
            (fcTopEnv 39) (epK 39 [epA1, epA2, epA3, .returnStmt])),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ke1
          rv rc fiv false 39) 43, ch) := by
  with_unfolding_all rfl

/-- `$res0` stored → the pending `$res1 = runVals` store. 8 steps. -/
theorem ep_b_raw39 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 8
      (qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ke1
        rv rc fiv 39 lp zeros8 zeros8) 43)
      (.next (.storeK [] [] (.seqn #[]) (fcTopEnv 39)
        (epK 39 [epA1, epA2, epA3, .returnStmt]))) ch
      = .ok (.next (.storeK [qRes1Ref]
            [.array ⟨rv.map (fun x => .int x .uint64)⟩] (.seqn #[])
            (fcTopEnv 39) (epK 39 [epA2, epA3, .returnStmt])),
        qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ke1
          rv rc fiv 39 lp zeros8 zeros8) 43, ch) := by
  with_unfolding_all rfl

/-- `$res1` stored → the pending `$res2 = runCounts` store. 8 steps. -/
theorem ep_c_raw39 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 8
      (qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ke1
        rv rc fiv 39 lp rv zeros8) 43)
      (.next (.storeK [] [] (.seqn #[]) (fcTopEnv 39)
        (epK 39 [epA2, epA3, .returnStmt]))) ch
      = .ok (.next (.storeK [qRes2Ref]
            [.array ⟨rc.map (fun x => .int x .uint64)⟩] (.seqn #[])
            (fcTopEnv 39) (epK 39 [epA3, .returnStmt])),
        qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ke1
          rv rc fiv 39 lp rv zeros8) 43, ch) := by
  with_unfolding_all rfl

/-- `$res2` stored → the `len(vals)` apply point inside
`$res3 = uint64(len(vals))`. 9 steps. -/
theorem ep_d_raw39 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 9
      (qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ke1
        rv rc fiv 39 lp rv rc) 43)
      (.next (.storeK [] [] (.seqn #[]) (fcTopEnv 39)
        (epK 39 [epA3, .returnStmt]))) ch
      = .ok (.retV (qRunSliceV 32 capV)
          (.strictK (.lengthOf (some (.slice tU64))) [] [] (fcTopEnv 39)
            (.strictK (.convert tU64) [] [] (fcTopEnv 39)
              (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
                (.seqn #[]) (fcTopEnv 39) (epK 39 [.returnStmt])))),
        qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ke1
          rv rc fiv 39 lp rv rc) 43, ch) := by
  with_unfolding_all rfl

/-- The length delivered → convert, the `$res3` store (a concrete
scalar — raw), return, the frame pops → the DRIVER TERMINAL. 9 steps. -/
theorem ep_e_raw39 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 9
      (qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ke1
        rv rc fiv 39 lp rv rc) 43)
      (.retV (.int 1 .int)
        (.strictK (.convert tU64) [] [] (fcTopEnv 39)
          (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
            (.seqn #[]) (fcTopEnv 39) (epK 39 [.returnStmt])))) ch
      = .ok (.next .stop,
        qSt σ (qHeapEnd1 nv sv n l lp siv civ capV capC v cnt 1 iv ke1
          rv rc fiv 39) 43, ch) := by
  with_unfolding_all rfl

/-- Subject exit (layout for A = 37): test false → break → the subject's
epilogue (`$res0/$res1 :=` the run slices) → the frame return delivers
them into `vals`/`counts` → `runVals`/`runCounts` arrays and the final
copy counter/flag declared → the final-copy head. 75 steps. -/
theorem r_exit_raw37 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (ch : Choices) :
    stepFnIter 75
      (qSt σ (qHeapRun nv sv n l lp siv civ capV capC v cnt iv false ([] : Heap)) 37)
      (.retV (.bool false) rCmpKQ) ch
      = .ok (fcHeadCfg 37,
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ([] : Heap)
          zeros8 zeros8 0 true 37) 41, ch) := by
  with_unfolding_all rfl

/-- Final-copy head, first dispatch → the `len(vals)` apply point.
25 steps. -/
theorem fc_A0_raw37 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (ch : Choices) :
    stepFnIter 25
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ([] : Heap)
        rv rc 0 true 37) 41) (fcHeadCfg 37) ch
      = .ok (.retV (qRunSliceV 32 capV) (fcLenSK 37 0),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ([] : Heap)
          rv rc 0 false 37) 41, ch) := by
  with_unfolding_all rfl

/-- Final-copy head, later dispatch (`i++`) → the `len(vals)` apply
point. 29 steps. -/
theorem fc_A1_raw37 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 29
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ([] : Heap)
        rv rc fiv false 37) 41) (fcHeadCfg 37) ch
      = .ok (.retV (qRunSliceV 32 capV)
          (fcLenSK 37
            (IntKind.normalize .int (IntKind.normalize .int (fiv + 1)))),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ([] : Heap)
          rv rc (IntKind.normalize .int (IntKind.normalize .int (fiv + 1)))
          false 37) 41, ch) := by
  with_unfolding_all rfl

/-- Final-copy body: test true → the `vals[i]` read point. 16 steps. -/
theorem fc_b_raw37 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 16
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ([] : Heap)
        rv rc fiv false 37) 41)
      (.retV (.bool true) (fcCmpK 37)) ch
      = .ok (.retV (.int fiv .int) (fcVReadK 37 capV fiv),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ([] : Heap)
          rv rc fiv false 37) 41, ch) := by
  with_unfolding_all rfl

/-- `vals[i]` delivered → the pending `runVals[i]` store. 1 step. -/
theorem fc_c_raw37 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ([] : Heap)
        rv rc fiv false 37) 41)
      (.retV w (fcVRhsK 37 fiv)) ch
      = .ok (.next (.storeK [fcVRef 37 fiv] [w] (.seqn #[]) (fcEnvB2 37)
            (fcStTail1 37)),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ([] : Heap)
          rv rc fiv false 37) 41, ch) := by
  with_unfolding_all rfl

/-- The first store done → the `counts[i]` read point. 14 steps. -/
theorem fc_d_raw37 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 14
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ([] : Heap)
        rv rc fiv false 37) 41)
      (.next (.storeK [] [] (.seqn #[]) (fcEnvB2 37) (fcStTail1 37))) ch
      = .ok (.retV (.int fiv .int) (fcCReadK 37 capC fiv),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ([] : Heap)
          rv rc fiv false 37) 41, ch) := by
  with_unfolding_all rfl

/-- `counts[i]` delivered → the pending `runCounts[i]` store. 1 step. -/
theorem fc_e_raw37 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ([] : Heap)
        rv rc fiv false 37) 41)
      (.retV w (fcCRhsK 37 fiv)) ch
      = .ok (.next (.storeK [fcCRef 37 fiv] [w] (.seqn #[]) (fcEnvB2 37)
            (fcStTail2 37)),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ([] : Heap)
          rv rc fiv false 37) 41, ch) := by
  with_unfolding_all rfl

/-- The second store done → the loop head. 5 steps. -/
theorem fc_f_raw37 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 5
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ([] : Heap)
        rv rc fiv false 37) 41)
      (.next (.storeK [] [] (.seqn #[]) (fcEnvB2 37) (fcStTail2 37))) ch
      = .ok (fcHeadCfg 37,
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ([] : Heap)
          rv rc fiv false 37) 41, ch) := by
  with_unfolding_all rfl

/-- Final-copy exit: test false → break → the harness epilogue up to
the pending `$res0 = pre` store. 14 steps. -/
theorem ep_a_raw37 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 14
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ([] : Heap)
        rv rc fiv false 37) 41)
      (.retV (.bool false) (fcCmpK 37)) ch
      = .ok (.next (.storeK [qRes0Ref]
            [.array ⟨lp.map (fun x => .int x .uint64)⟩] (.seqn #[])
            (fcTopEnv 37) (epK 37 [epA1, epA2, epA3, .returnStmt])),
        qSt σ (qHeapFC nv sv n l lp siv civ capV capC v cnt iv ([] : Heap)
          rv rc fiv false 37) 41, ch) := by
  with_unfolding_all rfl

/-- `$res0` stored → the pending `$res1 = runVals` store. 8 steps. -/
theorem ep_b_raw37 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 8
      (qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ([] : Heap)
        rv rc fiv 37 lp zeros8 zeros8) 41)
      (.next (.storeK [] [] (.seqn #[]) (fcTopEnv 37)
        (epK 37 [epA1, epA2, epA3, .returnStmt]))) ch
      = .ok (.next (.storeK [qRes1Ref]
            [.array ⟨rv.map (fun x => .int x .uint64)⟩] (.seqn #[])
            (fcTopEnv 37) (epK 37 [epA2, epA3, .returnStmt])),
        qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ([] : Heap)
          rv rc fiv 37 lp zeros8 zeros8) 41, ch) := by
  with_unfolding_all rfl

/-- `$res1` stored → the pending `$res2 = runCounts` store. 8 steps. -/
theorem ep_c_raw37 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 8
      (qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ([] : Heap)
        rv rc fiv 37 lp rv zeros8) 41)
      (.next (.storeK [] [] (.seqn #[]) (fcTopEnv 37)
        (epK 37 [epA2, epA3, .returnStmt]))) ch
      = .ok (.next (.storeK [qRes2Ref]
            [.array ⟨rc.map (fun x => .int x .uint64)⟩] (.seqn #[])
            (fcTopEnv 37) (epK 37 [epA3, .returnStmt])),
        qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ([] : Heap)
          rv rc fiv 37 lp rv zeros8) 41, ch) := by
  with_unfolding_all rfl

/-- `$res2` stored → the `len(vals)` apply point inside
`$res3 = uint64(len(vals))`. 9 steps. -/
theorem ep_d_raw37 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 9
      (qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ([] : Heap)
        rv rc fiv 37 lp rv rc) 41)
      (.next (.storeK [] [] (.seqn #[]) (fcTopEnv 37)
        (epK 37 [epA3, .returnStmt]))) ch
      = .ok (.retV (qRunSliceV 32 capV)
          (.strictK (.lengthOf (some (.slice tU64))) [] [] (fcTopEnv 37)
            (.strictK (.convert tU64) [] [] (fcTopEnv 37)
              (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
                (.seqn #[]) (fcTopEnv 37) (epK 37 [.returnStmt])))),
        qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ([] : Heap)
          rv rc fiv 37 lp rv rc) 41, ch) := by
  with_unfolding_all rfl

/-- The length delivered → convert, the `$res3` store (a concrete
scalar — raw), return, the frame pops → the DRIVER TERMINAL. 9 steps. -/
theorem ep_e_raw37 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (capV capC : Nat) (v cnt iv : Int)
    (rv rc : List Int) (fiv : Int) (ch : Choices) :
    stepFnIter 9
      (qSt σ (qHeapEp nv sv n l lp siv civ capV capC v cnt 0 iv ([] : Heap)
        rv rc fiv 37 lp rv rc) 41)
      (.retV (.int 1 .int)
        (.strictK (.convert tU64) [] [] (fcTopEnv 37)
          (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
            (.seqn #[]) (fcTopEnv 37) (epK 37 [.returnStmt])))) ch
      = .ok (.next .stop,
        qSt σ (qHeapEnd1 nv sv n l lp siv civ capV capC v cnt 1 iv ([] : Heap)
          rv rc fiv 37) 41, ch) := by
  with_unfolding_all rfl

/-! ## The `n = 0` path: no run event ever fires -/

/-- `n = 0` subject exit: test false at the FIRST dispatch → the
subject epilogue delivers the two EMPTY slices → the final-copy head.
75 steps. -/
theorem r_exit_raw0 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 75 (qSt σ (qHeapRle0 nv sv n l lp siv civ 0 false) 27)
      (.retV (.bool false) rCmpKQ) ch
      = .ok (fcHeadCfg 27,
        qSt σ (qHeapPost0 nv sv n l lp siv civ 0 true) 31, ch) := by
  with_unfolding_all rfl

/-- `n = 0` final-copy head: first dispatch, `len(vals) = 0` (a
CONCRETE empty slice — the length reduces definitionally), test false.
27 steps. -/
theorem fc_A0_raw0 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 27 (qSt σ (qHeapPost0 nv sv n l lp siv civ 0 true) 31)
      (fcHeadCfg 27) ch
      = .ok (.retV (.bool false) (fcCmpK 27),
        qSt σ (qHeapPost0 nv sv n l lp siv civ 0 false) 31, ch) := by
  with_unfolding_all rfl

/-- `n = 0` final-copy exit → the pending `$res0 = pre` store.
14 steps. -/
theorem ep_a_raw0 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 14 (qSt σ (qHeapPost0 nv sv n l lp siv civ 0 false) 31)
      (.retV (.bool false) (fcCmpK 27)) ch
      = .ok (.next (.storeK [qRes0Ref]
            [.array ⟨lp.map (fun x => .int x .uint64)⟩] (.seqn #[])
            (fcTopEnv 27) (epK 27 [epA1, epA2, epA3, .returnStmt])),
        qSt σ (qHeapPost0 nv sv n l lp siv civ 0 false) 31, ch) := by
  with_unfolding_all rfl

/-- `n = 0` epilogue tail: `$res1`/`$res2` (both the CONCRETE zero
array), `$res3 = 0`, return → the DRIVER TERMINAL. 37 steps. -/
theorem ep_z_raw0 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 37
      (qSt σ (qHeapEnd0 nv sv n l lp siv civ 0) 31)
      (.next (.storeK [] [] (.seqn #[]) (fcTopEnv 27)
        (epK 27 [epA1, epA2, epA3, .returnStmt]))) ch
      = .ok (.next .stop,
        qSt σ (qHeapEnd0 nv sv n l lp siv civ 0) 31, ch) := by
  with_unfolding_all rfl

/-! ## The composed iterations -/

/-- The wrapped seed — the single run's VALUE (`s[i] = seed + i/3` is
constant on `i < 3`). -/
def wSeed (seed : Nat) : Int := ((seed % 2 ^ 64 : Nat) : Int)

theorem wSeed_range (seed : Nat) : 0 ≤ wSeed seed ∧ wSeed seed < 2 ^ 64 := by
  have := Nat.mod_lt seed (y := 2 ^ 64) (by omega)
  unfold wSeed
  omega

/-- The family's element at any `m < n ≤ 3` IS the wrapped seed. -/
theorem rleFamily_getD_const {n seed m : Nat} (hm : m < n) (hn : n ≤ 3) :
    (rleFamily n seed).getD m 0 = wSeed seed := by
  rw [rleFamily_getD hm, wSeed]
  congr 1
  have : m / 3 = 0 := Nat.div_eq_of_lt (by omega)
  rw [this, Nat.add_zero]

/-- **Iteration `i = 0`, composed — THE NEW-RUN EVENT.** From the
test-true delivery, through both SPILLING `append`s, back to the loop
head: the output slices now hold the one-run state `([w], [1])` over
fresh backings with CHOICE-DEPENDENT capacities in `[1, 32]`, and the
stream has advanced past the two consumed choices. 148 steps. -/
theorem r_iter0C (σ : ExecState) (n seed : Nat) (hn1 : 1 ≤ n)
    (hn : n ≤ 3) (ch : Choices) :
    ∃ (capV capC : Nat) (ch' : Choices),
      1 ≤ capV ∧ capV ≤ 32 ∧ 1 ≤ capC ∧ capC ≤ 32 ∧
      stepFnIter 148
        (qSt σ (qHeapRle0 ((n : Nat) : Int) ((seed : Nat) : Int) n
          (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
          ((n : Nat) : Int) 0 false) 27)
        (.retV (.bool true) rCmpKQ) ch
        = .ok (rHeadCfgQ,
            qSt σ (qHeapRun ((n : Nat) : Int) ((seed : Nat) : Int) n
              (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
              ((n : Nat) : Int) capV capC (wSeed seed) 1 0 false []) 37,
            ch') := by
  have hwr := wSeed_range seed
  have ha := r_i0_a_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) ch
  -- the k length (runVals is the empty slice)
  have hlen := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := []) (env := rKEnv 27)
    (k := .rhsK .vals [.chain (.addr (.base ⟨27⟩)) [] []] [] [] (.seqn #[])
      (rKEnv 27) (rKTailK 27))
    (applyStrictOp_len_slice (σ := qSt σ (qHeapRle0 ((n : Nat) : Int)
        ((seed : Nat) : Int) n (rleFamily n seed) (rlePre n seed)
        ((n : Nat) : Int) ((n : Nat) : Int) 0 false
        ++ [(.base ⟨27⟩, qint 0)]) 28)
      (b := .base ⟨20⟩) (off := 0) (len := 0) (cap := 0) (elem := tU64)
      (Nat.le_refl 0)))
  have h1 := stepFnIter_chain ha hlen
  have hb := r_i0_b_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) ch
  have h2 := stepFnIter_chain h1 hb
  -- the s[0] read: the family's head is the wrapped seed
  have hgetS : (⟨(rleFamily n seed).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + 0]? = some (.int (wSeed seed) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by rw [rleFamily_length]; omega),
      rleFamily_getD_const (by omega) hn]
  have hlookS : Heap.lookup (qSt σ (qHeapRle0 ((n : Nat) : Int)
      ((seed : Nat) : Int) n (rleFamily n seed) (rlePre n seed)
      ((n : Nat) : Int) ((n : Nat) : Int) 0 false
      ++ [(.base ⟨27⟩, qint 0), (.base ⟨28⟩, qbool false),
          (.base ⟨29⟩, qC1Slice 30), (.base ⟨30⟩, qBack1 0)]) 31).heap
      (.base ⟨7⟩)
      = some ⟨some (.array n tU64),
          .array ⟨(rleFamily n seed).map (fun v => .int v .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hreadS := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [qSliceS n]) (env := rNREnv1)
    (k := .rhsK .vals [rC2Ref] [] [] (.seqn #[]) rNREnv1 rNRTail1)
    (applyStrictOp_indexGet_slice (ik := .int) (i := 0) hlookS
      (Nat.le_refl n) (by omega) hgetS))
  have h3 := stepFnIter_chain h2 hreadS
  have hc := r_i0_c_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) (.int (wSeed seed) .uint64) ch
  have h4 := stepFnIter_chain h3 hc
  -- the $c2[0] store
  have hlookC2 : Heap.lookup (qSt σ (qHeapRle0 ((n : Nat) : Int)
      ((seed : Nat) : Int) n (rleFamily n seed) (rlePre n seed)
      ((n : Nat) : Int) ((n : Nat) : Int) 0 false
      ++ [(.base ⟨27⟩, qint 0), (.base ⟨28⟩, qbool false),
          (.base ⟨29⟩, qC1Slice 30), (.base ⟨30⟩, qBack1 0)]) 31).heap
      (.base ⟨30⟩)
      = some ⟨some (.array 1 tU64),
          .array ⟨([0] : List Int).map (fun v => .int v .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hstC2 := storeTarget_slice_u64
    (σ := qSt σ (qHeapRle0 ((n : Nat) : Int) ((seed : Nat) : Int) n
      (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
      ((n : Nat) : Int) 0 false
      ++ [(.base ⟨27⟩, qint 0), (.base ⟨28⟩, qbool false),
          (.base ⟨29⟩, qC1Slice 30), (.base ⟨30⟩, qBack1 0)]) 31)
    (a := ⟨30⟩) (off := 0) (len := 1) (cap := 1) (i := 0) (n := 1)
    (ik := .int) (l := [0]) (w := wSeed seed)
    hlookC2 (Nat.le_refl 1) (by omega) (by simp) (by simp)
    (by intro x hx; simp at hx; omega) hwr
  have h5 := stepFnIter_chain h4
    (stepFnIter_one (stepFn_store_step hstC2))
  have hd := r_i0_d_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) (wSeed seed) ch
  have h6 := stepFnIter_chain h5 hd
  -- the FIRST append: runVals spills
  obtain ⟨capV, ch1, hcV1, hcV2, happ1⟩ :=
    applyStmtOp_append_spill1
      (σ := qSt σ (qHeapRle0 ((n : Nat) : Int) ((seed : Nat) : Int) n
        (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
        ((n : Nat) : Int) 0 false
        ++ [(.base ⟨27⟩, qint 0), (.base ⟨28⟩, qbool false),
            (.base ⟨29⟩, qC1Slice 30), (.base ⟨30⟩, qBack1 (wSeed seed)),
            (.base ⟨31⟩, qNilSlice)]) 32)
      (ta := ⟨31⟩) (sb := ⟨20⟩) (eb := ⟨30⟩) (v := wSeed seed)
      (oldv := .slice ⟨none, 0, 0, 0⟩)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) hwr
      (by with_unfolding_all rfl) ch
  have h7 := stepFnIter_chain h6
    (stepFnIter_one (stepFn_stmtOp_apply happ1))
  have he := r_i0_e_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) (wSeed seed) capV ch1
  have h8 := stepFnIter_chain h7 he
  -- the SECOND append: runCounts spills
  obtain ⟨capC, ch2, hcC1, hcC2, happ2⟩ :=
    applyStmtOp_append_spill1
      (σ := qSt σ (qHeapRle0' ((n : Nat) : Int) ((seed : Nat) : Int) n
        (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
        ((n : Nat) : Int) capV
        ++ [(.base ⟨27⟩, qint 0), (.base ⟨28⟩, qbool false),
            (.base ⟨29⟩, qC1Slice 30), (.base ⟨30⟩, qBack1 (wSeed seed)),
            (.base ⟨31⟩, qRunSlice 32 capV),
            (.base ⟨32⟩, qBackPad capV (wSeed seed)),
            (.base ⟨33⟩, qC1Slice 34), (.base ⟨34⟩, qBack1 1),
            (.base ⟨35⟩, qNilSlice)]) 36)
      (ta := ⟨35⟩) (sb := ⟨23⟩) (eb := ⟨34⟩) (v := 1)
      (oldv := .slice ⟨none, 0, 0, 0⟩)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl)
      (by omega) (by with_unfolding_all rfl) ch1
  have h9 := stepFnIter_chain h8
    (stepFnIter_one (stepFn_stmtOp_apply happ2))
  have hf := r_i0_f_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) (wSeed seed) capV capC ch2
  have h10 := stepFnIter_chain h9 hf
  exact ⟨capV, capC, ch2, hcV1, hcV2, hcC1, hcC2, h10⟩

/-- **Extend iteration `i = 1`, composed** (from the loop head through
the dispatch, the extend test — the pair matches, the family is
constant — and `runCounts[0]++`, back to the head). 143 steps; the
choice stream is untouched (no allocation spills). -/
theorem r_extC37 (σ : ExecState) (n seed : Nat) (capV capC : Nat)
    (hcV : 1 ≤ capV) (hcC : 1 ≤ capC) (h1n : 1 < n) (hn : n ≤ 3)
    (ch : Choices) :
    stepFnIter 143
      (qSt σ (qHeapRun ((n : Nat) : Int) ((seed : Nat) : Int) n
        (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
        ((n : Nat) : Int) capV capC (wSeed seed) 1 0 false []) 37)
      rHeadCfgQ ch
      = .ok (rHeadCfgQ,
          qSt σ (qHeapRun ((n : Nat) : Int) ((seed : Nat) : Int) n
            (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
            ((n : Nat) : Int) capV capC (wSeed seed) 2 1 false ke1) 39,
          ch) := by
  have hwr := wSeed_range seed
  have hA1 := r_A1_raw37 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) capV capC (wSeed seed) 1 0 ch
  rw [show IntKind.normalize .int (IntKind.normalize .int ((0 : Int) + 1))
      = (1 : Int) from rfl] at hA1
  -- len(s), then the exit test (true: 1 < n)
  have hlenS := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := []) (env := rBodyEnv)
    (k := .strictK .lessCmp [.int 1 .int] [] rBodyEnv rCmpKQ)
    (applyStrictOp_len_slice (σ := qSt σ (qHeapRun ((n : Nat) : Int)
        ((seed : Nat) : Int) n (rleFamily n seed) (rlePre n seed)
        ((n : Nat) : Int) ((n : Nat) : Int) capV capC (wSeed seed) 1 1
        false []) 37)
      (b := .base ⟨7⟩) (off := 0) (len := n) (cap := n) (elem := tU64)
      (Nat.le_refl n)))
  have hlt := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [.int 1 .int]) (env := rBodyEnv) (k := rCmpKQ)
    (applyStrictOp_lessCmp_int (σ := qSt σ (qHeapRun ((n : Nat) : Int)
        ((seed : Nat) : Int) n (rleFamily n seed) (rlePre n seed)
        ((n : Nat) : Int) ((n : Nat) : Int) capV capC (wSeed seed) 1 1
        false []) 37)
      (a := 1) (b := ((n : Nat) : Int)) (k := .int) (k' := .int)))
  rw [show decide ((1 : Int) < ((n : Nat) : Int)) = true from
    decide_eq_true (by exact_mod_cast h1n)] at hlt
  have h1 := stepFnIter_chain (stepFnIter_chain hA1 hlenS) hlt
  have ha := r_ext_a37 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) capV capC (wSeed seed) 1 1 ch
  have h2 := stepFnIter_chain h1 ha
  -- k := len(runVals) = 1
  have hlenV := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := []) (env := rKEnv 37)
    (k := .rhsK .vals [.chain (.addr (.base ⟨37⟩)) [] []] [] [] (.seqn #[])
      (rKEnv 37) (rKTailK 37))
    (applyStrictOp_len_slice (σ := qSt σ (qHeapRun ((n : Nat) : Int)
        ((seed : Nat) : Int) n (rleFamily n seed) (rlePre n seed)
        ((n : Nat) : Int) ((n : Nat) : Int) capV capC (wSeed seed) 1 1
        false [(.base ⟨37⟩, qint 0)]) 38)
      (b := .base ⟨32⟩) (off := 0) (len := 1) (cap := capV) (elem := tU64)
      hcV))
  have h3 := stepFnIter_chain h2 hlenV
  have hb := r_ext_b37 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) capV capC (wSeed seed) 1 1 ch
  have h4 := stepFnIter_chain h3 hb
  -- runVals[0] (the banked run value)
  have hlookV : Heap.lookup (qSt σ (qHeapRun ((n : Nat) : Int)
      ((seed : Nat) : Int) n (rleFamily n seed) (rlePre n seed)
      ((n : Nat) : Int) ((n : Nat) : Int) capV capC (wSeed seed) 1 1 false
      [(.base ⟨37⟩, qint 1), (.base ⟨38⟩, qbool false)]) 39).heap
      (.base ⟨32⟩)
      = some ⟨some (.array capV tU64),
          .array ⟨(qPadL capV (wSeed seed)).map
            (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hreadV := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [qRunSliceV 32 capV]) (env := rExtGuardEnv 37)
    (k := .strictK (.eqCmp tU64) [] [.indexGet (.var "s") (.var "i")]
      (rExtGuardEnv 37) (rExtIfK 37))
    (applyStrictOp_indexGet_slice (ik := .int) (i := 0) hlookV hcV
      (by omega) (by rfl)))
  have h5 := stepFnIter_chain h4 hreadV
  have hc := r_ext_c37 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) capV capC (wSeed seed) 1 1 (wSeed seed) ch
  have h6 := stepFnIter_chain h5 hc
  -- s[1] (the family is constant, so it MATCHES)
  have hgetS : (⟨(rleFamily n seed).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + 1]? = some (.int (wSeed seed) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by rw [rleFamily_length]; omega),
      rleFamily_getD_const (by omega) hn]
  have hlookS : Heap.lookup (qSt σ (qHeapRun ((n : Nat) : Int)
      ((seed : Nat) : Int) n (rleFamily n seed) (rlePre n seed)
      ((n : Nat) : Int) ((n : Nat) : Int) capV capC (wSeed seed) 1 1 false
      [(.base ⟨37⟩, qint 1), (.base ⟨38⟩, qbool false)]) 39).heap
      (.base ⟨7⟩)
      = some ⟨some (.array n tU64),
          .array ⟨(rleFamily n seed).map (fun v => .int v .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hreadS := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [qSliceS n]) (env := rExtGuardEnv 37)
    (k := .strictK (.eqCmp tU64) [.int (wSeed seed) .uint64] []
      (rExtGuardEnv 37) (rExtIfK 37))
    (applyStrictOp_indexGet_slice (ik := .int) (i := 1) hlookS
      (Nat.le_refl n) (by omega) hgetS))
  have h7 := stepFnIter_chain h6 hreadS
  have heq := r_eq_apply (qSt σ (qHeapRun ((n : Nat) : Int)
      ((seed : Nat) : Int) n (rleFamily n seed) (rlePre n seed)
      ((n : Nat) : Int) ((n : Nat) : Int) capV capC (wSeed seed) 1 1 false
      [(.base ⟨37⟩, qint 1), (.base ⟨38⟩, qbool false)]) 39)
    (wSeed seed) (wSeed seed) (rExtGuardEnv 37) (rExtIfK 37) ch
  rw [show ((wSeed seed) == (wSeed seed)) = true from beq_self_eq_true _]
    at heq
  have h8 := stepFnIter_chain h7 heq
  have hd := r_ext_d37 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) capV capC (wSeed seed) 1 1 ch
  have h9 := stepFnIter_chain h8 hd
  -- runCounts[0] = 1
  have hlookC : Heap.lookup (qSt σ (qHeapRun ((n : Nat) : Int)
      ((seed : Nat) : Int) n (rleFamily n seed) (rlePre n seed)
      ((n : Nat) : Int) ((n : Nat) : Int) capV capC (wSeed seed) 1 1 false
      [(.base ⟨37⟩, qint 1), (.base ⟨38⟩, qbool false)]) 39).heap
      (.base ⟨36⟩)
      = some ⟨some (.array capC tU64),
          .array ⟨(qPadL capC 1).map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hreadC := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [qRunSliceV 36 capC]) (env := rExtBEnv 37)
    (k := .strictK .add [] [.intLit 1 .uint64] (rExtBEnv 37)
      (rExtRhsK 37 capC))
    (applyStrictOp_indexGet_slice (ik := .int) (i := 0) hlookC hcC
      (by omega) (by rfl)))
  have h10 := stepFnIter_chain h9 hreadC
  have he := r_ext_e37 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) capV capC (wSeed seed) 1 1 1 ch
  rw [show IntKind.normalize .uint64 ((1 : Int) + 1) = (2 : Int) from rfl]
    at he
  have h11 := stepFnIter_chain h10 he
  -- the runCounts[0] := 2 store
  have hstC := storeTarget_slice_u64
    (σ := qSt σ (qHeapRun ((n : Nat) : Int) ((seed : Nat) : Int) n
      (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
      ((n : Nat) : Int) capV capC (wSeed seed) 1 1 false
      [(.base ⟨37⟩, qint 1), (.base ⟨38⟩, qbool false)]) 39)
    (a := ⟨36⟩) (off := 0) (len := 1) (cap := capC) (i := 0) (n := capC)
    (ik := .int) (l := qPadL capC 1) (w := 2)
    hlookC hcC (by omega)
    (by simp only [qPadL, List.length_cons, List.length_replicate]; omega)
    (by simp only [qPadL, List.length_cons, List.length_replicate]; omega)
    (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · rcases List.mem_replicate.mp hx with ⟨-, rfl⟩; omega)
    (by omega)
  have h12 := stepFnIter_chain h11
    (stepFnIter_one (stepFn_store_step hstC))
  have hf := r_ext_f37 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) capV capC (wSeed seed) 2 1 ch
  exact stepFnIter_chain h12 hf

/-- **Extend iteration `i = 2`, composed** (from the loop head through
the dispatch, the extend test — the pair matches, the family is
constant — and `runCounts[0]++`, back to the head). 143 steps; the
choice stream is untouched (no allocation spills). -/
theorem r_extC39 (σ : ExecState) (n seed : Nat) (capV capC : Nat)
    (hcV : 1 ≤ capV) (hcC : 1 ≤ capC) (h1n : 2 < n) (hn : n ≤ 3)
    (ch : Choices) :
    stepFnIter 143
      (qSt σ (qHeapRun ((n : Nat) : Int) ((seed : Nat) : Int) n
        (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
        ((n : Nat) : Int) capV capC (wSeed seed) 2 1 false ke1) 39)
      rHeadCfgQ ch
      = .ok (rHeadCfgQ,
          qSt σ (qHeapRun ((n : Nat) : Int) ((seed : Nat) : Int) n
            (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
            ((n : Nat) : Int) capV capC (wSeed seed) 3 2 false ke2) 41,
          ch) := by
  have hwr := wSeed_range seed
  have hA1 := r_A1_raw39 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) capV capC (wSeed seed) 2 1 ch
  rw [show IntKind.normalize .int (IntKind.normalize .int ((1 : Int) + 1))
      = (2 : Int) from rfl] at hA1
  -- len(s), then the exit test (true: 1 < n)
  have hlenS := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := []) (env := rBodyEnv)
    (k := .strictK .lessCmp [.int 2 .int] [] rBodyEnv rCmpKQ)
    (applyStrictOp_len_slice (σ := qSt σ (qHeapRun ((n : Nat) : Int)
        ((seed : Nat) : Int) n (rleFamily n seed) (rlePre n seed)
        ((n : Nat) : Int) ((n : Nat) : Int) capV capC (wSeed seed) 2 2
        false ke1) 39)
      (b := .base ⟨7⟩) (off := 0) (len := n) (cap := n) (elem := tU64)
      (Nat.le_refl n)))
  have hlt := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [.int 2 .int]) (env := rBodyEnv) (k := rCmpKQ)
    (applyStrictOp_lessCmp_int (σ := qSt σ (qHeapRun ((n : Nat) : Int)
        ((seed : Nat) : Int) n (rleFamily n seed) (rlePre n seed)
        ((n : Nat) : Int) ((n : Nat) : Int) capV capC (wSeed seed) 2 2
        false ke1) 39)
      (a := 2) (b := ((n : Nat) : Int)) (k := .int) (k' := .int)))
  rw [show decide ((2 : Int) < ((n : Nat) : Int)) = true from
    decide_eq_true (by exact_mod_cast h1n)] at hlt
  have h1 := stepFnIter_chain (stepFnIter_chain hA1 hlenS) hlt
  have ha := r_ext_a39 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) capV capC (wSeed seed) 2 2 ch
  have h2 := stepFnIter_chain h1 ha
  -- k := len(runVals) = 1
  have hlenV := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := []) (env := rKEnv 39)
    (k := .rhsK .vals [.chain (.addr (.base ⟨39⟩)) [] []] [] [] (.seqn #[])
      (rKEnv 39) (rKTailK 39))
    (applyStrictOp_len_slice (σ := qSt σ (qHeapRun ((n : Nat) : Int)
        ((seed : Nat) : Int) n (rleFamily n seed) (rlePre n seed)
        ((n : Nat) : Int) ((n : Nat) : Int) capV capC (wSeed seed) 2 2
        false (ke1 ++ [(.base ⟨39⟩, qint 0)])) 40)
      (b := .base ⟨32⟩) (off := 0) (len := 1) (cap := capV) (elem := tU64)
      hcV))
  have h3 := stepFnIter_chain h2 hlenV
  have hb := r_ext_b39 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) capV capC (wSeed seed) 2 2 ch
  have h4 := stepFnIter_chain h3 hb
  -- runVals[0] (the banked run value)
  have hlookV : Heap.lookup (qSt σ (qHeapRun ((n : Nat) : Int)
      ((seed : Nat) : Int) n (rleFamily n seed) (rlePre n seed)
      ((n : Nat) : Int) ((n : Nat) : Int) capV capC (wSeed seed) 2 2 false
      (ke1 ++ [(.base ⟨39⟩, qint 1), (.base ⟨40⟩, qbool false)])) 41).heap
      (.base ⟨32⟩)
      = some ⟨some (.array capV tU64),
          .array ⟨(qPadL capV (wSeed seed)).map
            (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hreadV := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [qRunSliceV 32 capV]) (env := rExtGuardEnv 39)
    (k := .strictK (.eqCmp tU64) [] [.indexGet (.var "s") (.var "i")]
      (rExtGuardEnv 39) (rExtIfK 39))
    (applyStrictOp_indexGet_slice (ik := .int) (i := 0) hlookV hcV
      (by omega) (by rfl)))
  have h5 := stepFnIter_chain h4 hreadV
  have hc := r_ext_c39 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) capV capC (wSeed seed) 2 2 (wSeed seed) ch
  have h6 := stepFnIter_chain h5 hc
  -- s[1] (the family is constant, so it MATCHES)
  have hgetS : (⟨(rleFamily n seed).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + 2]? = some (.int (wSeed seed) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by rw [rleFamily_length]; omega),
      rleFamily_getD_const (by omega) hn]
  have hlookS : Heap.lookup (qSt σ (qHeapRun ((n : Nat) : Int)
      ((seed : Nat) : Int) n (rleFamily n seed) (rlePre n seed)
      ((n : Nat) : Int) ((n : Nat) : Int) capV capC (wSeed seed) 2 2 false
      (ke1 ++ [(.base ⟨39⟩, qint 1), (.base ⟨40⟩, qbool false)])) 41).heap
      (.base ⟨7⟩)
      = some ⟨some (.array n tU64),
          .array ⟨(rleFamily n seed).map (fun v => .int v .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hreadS := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [qSliceS n]) (env := rExtGuardEnv 39)
    (k := .strictK (.eqCmp tU64) [.int (wSeed seed) .uint64] []
      (rExtGuardEnv 39) (rExtIfK 39))
    (applyStrictOp_indexGet_slice (ik := .int) (i := 2) hlookS
      (Nat.le_refl n) (by omega) hgetS))
  have h7 := stepFnIter_chain h6 hreadS
  have heq := r_eq_apply (qSt σ (qHeapRun ((n : Nat) : Int)
      ((seed : Nat) : Int) n (rleFamily n seed) (rlePre n seed)
      ((n : Nat) : Int) ((n : Nat) : Int) capV capC (wSeed seed) 2 2 false
      (ke1 ++ [(.base ⟨39⟩, qint 1), (.base ⟨40⟩, qbool false)])) 41)
    (wSeed seed) (wSeed seed) (rExtGuardEnv 39) (rExtIfK 39) ch
  rw [show ((wSeed seed) == (wSeed seed)) = true from beq_self_eq_true _]
    at heq
  have h8 := stepFnIter_chain h7 heq
  have hd := r_ext_d39 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) capV capC (wSeed seed) 2 2 ch
  have h9 := stepFnIter_chain h8 hd
  -- runCounts[0] = 1
  have hlookC : Heap.lookup (qSt σ (qHeapRun ((n : Nat) : Int)
      ((seed : Nat) : Int) n (rleFamily n seed) (rlePre n seed)
      ((n : Nat) : Int) ((n : Nat) : Int) capV capC (wSeed seed) 2 2 false
      (ke1 ++ [(.base ⟨39⟩, qint 1), (.base ⟨40⟩, qbool false)])) 41).heap
      (.base ⟨36⟩)
      = some ⟨some (.array capC tU64),
          .array ⟨(qPadL capC 2).map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hreadC := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [qRunSliceV 36 capC]) (env := rExtBEnv 39)
    (k := .strictK .add [] [.intLit 1 .uint64] (rExtBEnv 39)
      (rExtRhsK 39 capC))
    (applyStrictOp_indexGet_slice (ik := .int) (i := 0) hlookC hcC
      (by omega) (by rfl)))
  have h10 := stepFnIter_chain h9 hreadC
  have he := r_ext_e39 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) capV capC (wSeed seed) 2 2 2 ch
  rw [show IntKind.normalize .uint64 ((2 : Int) + 1) = (3 : Int) from rfl]
    at he
  have h11 := stepFnIter_chain h10 he
  -- the runCounts[0] := 2 store
  have hstC := storeTarget_slice_u64
    (σ := qSt σ (qHeapRun ((n : Nat) : Int) ((seed : Nat) : Int) n
      (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
      ((n : Nat) : Int) capV capC (wSeed seed) 2 2 false
      (ke1 ++ [(.base ⟨39⟩, qint 1), (.base ⟨40⟩, qbool false)])) 41)
    (a := ⟨36⟩) (off := 0) (len := 1) (cap := capC) (i := 0) (n := capC)
    (ik := .int) (l := qPadL capC 2) (w := 3)
    hlookC hcC (by omega)
    (by simp only [qPadL, List.length_cons, List.length_replicate]; omega)
    (by simp only [qPadL, List.length_cons, List.length_replicate]; omega)
    (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · rcases List.mem_replicate.mp hx with ⟨-, rfl⟩; omega)
    (by omega)
  have h12 := stepFnIter_chain h11
    (stepFnIter_one (stepFn_store_step hstC))
  have hf := r_ext_f39 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) capV capC (wSeed seed) 3 2 ch
  exact stepFnIter_chain h12 hf

/-! ## The composed final copy + epilogue (one instance per exit
layout) -/

/-- The `[8]uint64` array holding one live element. -/
def qPad8 (x : Int) : List Int := x :: List.replicate 7 0

theorem qPad8_length (x : Int) : (qPad8 x).length = 8 := by
  simp [qPad8]

theorem qPad8_range {x : Int} (hx : 0 ≤ x ∧ x < 2 ^ 64) :
    ∀ v ∈ qPad8 x, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hx
  · rcases List.mem_replicate.mp hv with ⟨-, rfl⟩; omega

/-- **The final copy loop + the epilogue, composed** (`A = 41`
layout): one iteration lifts `(w, cnt)` into the arrays, the loop
exits at `i = 1 = len(vals)`, and the four results are delivered.
151 steps. -/
theorem fcC41 (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (capV capC : Nat) (w cnt : Int)
    (hcV : 1 ≤ capV) (hcC : 1 ≤ capC)
    (hw : 0 ≤ w ∧ w < 2 ^ 64) (hcnt : 0 ≤ cnt ∧ cnt < 2 ^ 64)
    (hlp : lp.length = 8) (hlpr : ∀ v ∈ lp, 0 ≤ v ∧ v < 2 ^ 64)
    (iv : Int) (ch : Choices) :
    stepFnIter 151
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC w cnt iv ke2
        zeros8 zeros8 0 true 41) 45) (fcHeadCfg 41) ch
      = .ok (.next .stop,
          qSt σ (qHeapEnd1 nv sv n l lp siv civ capV capC w cnt 1 iv ke2
            (qPad8 w) (qPad8 cnt) 1 41) 45, ch) := by
  have hA0 := fc_A0_raw41 σ nv sv n l lp siv civ capV capC w cnt iv
    zeros8 zeros8 ch
  -- len(vals) = 1, then 0 < 1
  have hlen1 := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := []) (env := fcEnvB 41)
    (k := .strictK .lessCmp [.int 0 .int] [] (fcEnvB 41) (fcCmpK 41))
    (applyStrictOp_len_slice (σ := qSt σ (qHeapFC nv sv n l lp siv civ
        capV capC w cnt iv ke2 zeros8 zeros8 0 false 41) 45)
      (b := .base ⟨32⟩) (off := 0) (len := 1) (cap := capV)
      (elem := tU64) hcV))
  have hlt1 := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [.int 0 .int]) (env := fcEnvB 41) (k := fcCmpK 41)
    (applyStrictOp_lessCmp_int (σ := qSt σ (qHeapFC nv sv n l lp siv civ
        capV capC w cnt iv ke2 zeros8 zeros8 0 false 41) 45)
      (a := 0) (b := ((1 : Nat) : Int)) (k := .int) (k' := .int)))
  rw [show decide ((0 : Int) < ((1 : Nat) : Int)) = true from
    decide_eq_true (by omega)] at hlt1
  have h1 := stepFnIter_chain (stepFnIter_chain hA0 hlen1) hlt1
  have hb := fc_b_raw41 σ nv sv n l lp siv civ capV capC w cnt iv
    zeros8 zeros8 0 ch
  have h2 := stepFnIter_chain h1 hb
  -- vals[0] = w
  have hlookV : Heap.lookup (qSt σ (qHeapFC nv sv n l lp siv civ
      capV capC w cnt iv ke2 zeros8 zeros8 0 false 41) 45).heap
      (.base ⟨32⟩)
      = some ⟨some (.array capV tU64),
          .array ⟨(qPadL capV w).map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hreadV := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [qRunSliceV 32 capV]) (env := fcEnvB2 41)
    (k := fcVRhsK 41 0)
    (applyStrictOp_indexGet_slice (ik := .int) (i := 0) hlookV hcV
      (by omega) (by rfl)))
  have h3 := stepFnIter_chain h2 hreadV
  have hc := fc_c_raw41 σ nv sv n l lp siv civ capV capC w cnt iv
    zeros8 zeros8 0 (.int w .uint64) ch
  have h4 := stepFnIter_chain h3 hc
  -- runVals[0] := w
  have hlookA : Heap.lookup (qSt σ (qHeapFC nv sv n l lp siv civ
      capV capC w cnt iv ke2 zeros8 zeros8 0 false 41) 45).heap
      (.base ⟨41⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hstV := storeTarget_arrayLocal_u64 (a := ⟨41⟩) (N := 8) (i := 0)
    (ik := .int) (l := zeros8) (w := w) hlookA
    (by simp [zeros8]) (by simp [zeros8])
    (by intro x hx; rcases List.mem_replicate.mp hx with ⟨-, rfl⟩; omega)
    hw
  have h5 := stepFnIter_chain h4
    (stepFnIter_one (stepFn_store_step hstV))
  have hd := fc_d_raw41 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) zeros8 0 ch
  have h6 := stepFnIter_chain h5 hd
  -- counts[0] = cnt
  have hlookC : Heap.lookup (qSt σ (qHeapFC nv sv n l lp siv civ
      capV capC w cnt iv ke2 (qPad8 w) zeros8 0 false 41) 45).heap
      (.base ⟨36⟩)
      = some ⟨some (.array capC tU64),
          .array ⟨(qPadL capC cnt).map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hreadC := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [qRunSliceV 36 capC]) (env := fcEnvB2 41)
    (k := fcCRhsK 41 0)
    (applyStrictOp_indexGet_slice (ik := .int) (i := 0) hlookC hcC
      (by omega) (by rfl)))
  have h7 := stepFnIter_chain h6 hreadC
  have he := fc_e_raw41 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) zeros8 0 (.int cnt .uint64) ch
  have h8 := stepFnIter_chain h7 he
  -- runCounts[0] := cnt
  have hlookB : Heap.lookup (qSt σ (qHeapFC nv sv n l lp siv civ
      capV capC w cnt iv ke2 (qPad8 w) zeros8 0 false 41) 45).heap
      (.base ⟨42⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hstC := storeTarget_arrayLocal_u64 (a := ⟨42⟩) (N := 8) (i := 0)
    (ik := .int) (l := zeros8) (w := cnt) hlookB
    (by simp [zeros8]) (by simp [zeros8])
    (by intro x hx; rcases List.mem_replicate.mp hx with ⟨-, rfl⟩; omega)
    hcnt
  have h9 := stepFnIter_chain h8
    (stepFnIter_one (stepFn_store_step hstC))
  have hf := fc_f_raw41 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 0 ch
  have h10 := stepFnIter_chain h9 hf
  -- the second dispatch: i = 1, the test fails
  have hA1 := fc_A1_raw41 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 0 ch
  rw [show IntKind.normalize .int (IntKind.normalize .int ((0 : Int) + 1))
      = (1 : Int) from rfl] at hA1
  have hlen2 := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := []) (env := fcEnvB 41)
    (k := .strictK .lessCmp [.int 1 .int] [] (fcEnvB 41) (fcCmpK 41))
    (applyStrictOp_len_slice (σ := qSt σ (qHeapFC nv sv n l lp siv civ
        capV capC w cnt iv ke2 (qPad8 w) (qPad8 cnt) 1 false 41) 45)
      (b := .base ⟨32⟩) (off := 0) (len := 1) (cap := capV)
      (elem := tU64) hcV))
  have hlt2 := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [.int 1 .int]) (env := fcEnvB 41) (k := fcCmpK 41)
    (applyStrictOp_lessCmp_int (σ := qSt σ (qHeapFC nv sv n l lp siv civ
        capV capC w cnt iv ke2 (qPad8 w) (qPad8 cnt) 1 false 41) 45)
      (a := 1) (b := ((1 : Nat) : Int)) (k := .int) (k' := .int)))
  rw [show decide ((1 : Int) < ((1 : Nat) : Int)) = false from
    decide_eq_false (by omega)] at hlt2
  have h11 := stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h10 hA1) hlen2) hlt2
  have hepa := ep_a_raw41 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 1 ch
  have h12 := stepFnIter_chain h11 hepa
  -- $res0 := pre
  have hlook2 : Heap.lookup (qSt σ (qHeapFC nv sv n l lp siv civ
      capV capC w cnt iv ke2 (qPad8 w) (qPad8 cnt) 1 false 41) 45).heap
      (.base ⟨2⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hst0 := storeTarget_addr (ty := .array 8 tU64) hlook2
    (normalizeValueForTy_arr_u64 hlp hlpr)
  have h13 := stepFnIter_chain h12
    (stepFnIter_one (stepFn_store_step hst0))
  have hepb := ep_b_raw41 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 1 ch
  have h14 := stepFnIter_chain h13 hepb
  -- $res1 := runVals
  have hlook3 : Heap.lookup (qSt σ (qHeapEp nv sv n l lp siv civ
      capV capC w cnt 0 iv ke2 (qPad8 w) (qPad8 cnt) 1 41
      lp zeros8 zeros8) 45).heap (.base ⟨3⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hst1 := storeTarget_addr (ty := .array 8 tU64) hlook3
    (normalizeValueForTy_arr_u64 (qPad8_length w) (qPad8_range hw))
  have h15 := stepFnIter_chain h14
    (stepFnIter_one (stepFn_store_step hst1))
  have hepc := ep_c_raw41 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 1 ch
  have h16 := stepFnIter_chain h15 hepc
  -- $res2 := runCounts
  have hlook4 : Heap.lookup (qSt σ (qHeapEp nv sv n l lp siv civ
      capV capC w cnt 0 iv ke2 (qPad8 w) (qPad8 cnt) 1 41
      lp (qPad8 w) zeros8) 45).heap (.base ⟨4⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hst2 := storeTarget_addr (ty := .array 8 tU64) hlook4
    (normalizeValueForTy_arr_u64 (qPad8_length cnt) (qPad8_range hcnt))
  have h17 := stepFnIter_chain h16
    (stepFnIter_one (stepFn_store_step hst2))
  have hepd := ep_d_raw41 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 1 ch
  have h18 := stepFnIter_chain h17 hepd
  -- len(vals) once more, then convert + the $res3 store + return
  have hlen3 := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := []) (env := fcTopEnv 41)
    (k := .strictK (.convert tU64) [] [] (fcTopEnv 41)
      (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
        (.seqn #[]) (fcTopEnv 41) (epK 41 [.returnStmt])))
    (applyStrictOp_len_slice (σ := qSt σ (qHeapEp nv sv n l lp siv civ
        capV capC w cnt 0 iv ke2 (qPad8 w) (qPad8 cnt) 1 41
        lp (qPad8 w) (qPad8 cnt)) 45)
      (b := .base ⟨32⟩) (off := 0) (len := 1) (cap := capV)
      (elem := tU64) hcV))
  have h19 := stepFnIter_chain h18 hlen3
  have hepe := ep_e_raw41 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 1 ch
  exact stepFnIter_chain h19 hepe

/-- **The final copy loop + the epilogue, composed** (`A = 39`
layout): one iteration lifts `(w, cnt)` into the arrays, the loop
exits at `i = 1 = len(vals)`, and the four results are delivered.
151 steps. -/
theorem fcC39 (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (capV capC : Nat) (w cnt : Int)
    (hcV : 1 ≤ capV) (hcC : 1 ≤ capC)
    (hw : 0 ≤ w ∧ w < 2 ^ 64) (hcnt : 0 ≤ cnt ∧ cnt < 2 ^ 64)
    (hlp : lp.length = 8) (hlpr : ∀ v ∈ lp, 0 ≤ v ∧ v < 2 ^ 64)
    (iv : Int) (ch : Choices) :
    stepFnIter 151
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC w cnt iv ke1
        zeros8 zeros8 0 true 39) 43) (fcHeadCfg 39) ch
      = .ok (.next .stop,
          qSt σ (qHeapEnd1 nv sv n l lp siv civ capV capC w cnt 1 iv ke1
            (qPad8 w) (qPad8 cnt) 1 39) 43, ch) := by
  have hA0 := fc_A0_raw39 σ nv sv n l lp siv civ capV capC w cnt iv
    zeros8 zeros8 ch
  -- len(vals) = 1, then 0 < 1
  have hlen1 := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := []) (env := fcEnvB 39)
    (k := .strictK .lessCmp [.int 0 .int] [] (fcEnvB 39) (fcCmpK 39))
    (applyStrictOp_len_slice (σ := qSt σ (qHeapFC nv sv n l lp siv civ
        capV capC w cnt iv ke1 zeros8 zeros8 0 false 39) 43)
      (b := .base ⟨32⟩) (off := 0) (len := 1) (cap := capV)
      (elem := tU64) hcV))
  have hlt1 := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [.int 0 .int]) (env := fcEnvB 39) (k := fcCmpK 39)
    (applyStrictOp_lessCmp_int (σ := qSt σ (qHeapFC nv sv n l lp siv civ
        capV capC w cnt iv ke1 zeros8 zeros8 0 false 39) 43)
      (a := 0) (b := ((1 : Nat) : Int)) (k := .int) (k' := .int)))
  rw [show decide ((0 : Int) < ((1 : Nat) : Int)) = true from
    decide_eq_true (by omega)] at hlt1
  have h1 := stepFnIter_chain (stepFnIter_chain hA0 hlen1) hlt1
  have hb := fc_b_raw39 σ nv sv n l lp siv civ capV capC w cnt iv
    zeros8 zeros8 0 ch
  have h2 := stepFnIter_chain h1 hb
  -- vals[0] = w
  have hlookV : Heap.lookup (qSt σ (qHeapFC nv sv n l lp siv civ
      capV capC w cnt iv ke1 zeros8 zeros8 0 false 39) 43).heap
      (.base ⟨32⟩)
      = some ⟨some (.array capV tU64),
          .array ⟨(qPadL capV w).map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hreadV := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [qRunSliceV 32 capV]) (env := fcEnvB2 39)
    (k := fcVRhsK 39 0)
    (applyStrictOp_indexGet_slice (ik := .int) (i := 0) hlookV hcV
      (by omega) (by rfl)))
  have h3 := stepFnIter_chain h2 hreadV
  have hc := fc_c_raw39 σ nv sv n l lp siv civ capV capC w cnt iv
    zeros8 zeros8 0 (.int w .uint64) ch
  have h4 := stepFnIter_chain h3 hc
  -- runVals[0] := w
  have hlookA : Heap.lookup (qSt σ (qHeapFC nv sv n l lp siv civ
      capV capC w cnt iv ke1 zeros8 zeros8 0 false 39) 43).heap
      (.base ⟨39⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hstV := storeTarget_arrayLocal_u64 (a := ⟨39⟩) (N := 8) (i := 0)
    (ik := .int) (l := zeros8) (w := w) hlookA
    (by simp [zeros8]) (by simp [zeros8])
    (by intro x hx; rcases List.mem_replicate.mp hx with ⟨-, rfl⟩; omega)
    hw
  have h5 := stepFnIter_chain h4
    (stepFnIter_one (stepFn_store_step hstV))
  have hd := fc_d_raw39 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) zeros8 0 ch
  have h6 := stepFnIter_chain h5 hd
  -- counts[0] = cnt
  have hlookC : Heap.lookup (qSt σ (qHeapFC nv sv n l lp siv civ
      capV capC w cnt iv ke1 (qPad8 w) zeros8 0 false 39) 43).heap
      (.base ⟨36⟩)
      = some ⟨some (.array capC tU64),
          .array ⟨(qPadL capC cnt).map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hreadC := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [qRunSliceV 36 capC]) (env := fcEnvB2 39)
    (k := fcCRhsK 39 0)
    (applyStrictOp_indexGet_slice (ik := .int) (i := 0) hlookC hcC
      (by omega) (by rfl)))
  have h7 := stepFnIter_chain h6 hreadC
  have he := fc_e_raw39 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) zeros8 0 (.int cnt .uint64) ch
  have h8 := stepFnIter_chain h7 he
  -- runCounts[0] := cnt
  have hlookB : Heap.lookup (qSt σ (qHeapFC nv sv n l lp siv civ
      capV capC w cnt iv ke1 (qPad8 w) zeros8 0 false 39) 43).heap
      (.base ⟨40⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hstC := storeTarget_arrayLocal_u64 (a := ⟨40⟩) (N := 8) (i := 0)
    (ik := .int) (l := zeros8) (w := cnt) hlookB
    (by simp [zeros8]) (by simp [zeros8])
    (by intro x hx; rcases List.mem_replicate.mp hx with ⟨-, rfl⟩; omega)
    hcnt
  have h9 := stepFnIter_chain h8
    (stepFnIter_one (stepFn_store_step hstC))
  have hf := fc_f_raw39 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 0 ch
  have h10 := stepFnIter_chain h9 hf
  -- the second dispatch: i = 1, the test fails
  have hA1 := fc_A1_raw39 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 0 ch
  rw [show IntKind.normalize .int (IntKind.normalize .int ((0 : Int) + 1))
      = (1 : Int) from rfl] at hA1
  have hlen2 := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := []) (env := fcEnvB 39)
    (k := .strictK .lessCmp [.int 1 .int] [] (fcEnvB 39) (fcCmpK 39))
    (applyStrictOp_len_slice (σ := qSt σ (qHeapFC nv sv n l lp siv civ
        capV capC w cnt iv ke1 (qPad8 w) (qPad8 cnt) 1 false 39) 43)
      (b := .base ⟨32⟩) (off := 0) (len := 1) (cap := capV)
      (elem := tU64) hcV))
  have hlt2 := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [.int 1 .int]) (env := fcEnvB 39) (k := fcCmpK 39)
    (applyStrictOp_lessCmp_int (σ := qSt σ (qHeapFC nv sv n l lp siv civ
        capV capC w cnt iv ke1 (qPad8 w) (qPad8 cnt) 1 false 39) 43)
      (a := 1) (b := ((1 : Nat) : Int)) (k := .int) (k' := .int)))
  rw [show decide ((1 : Int) < ((1 : Nat) : Int)) = false from
    decide_eq_false (by omega)] at hlt2
  have h11 := stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h10 hA1) hlen2) hlt2
  have hepa := ep_a_raw39 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 1 ch
  have h12 := stepFnIter_chain h11 hepa
  -- $res0 := pre
  have hlook2 : Heap.lookup (qSt σ (qHeapFC nv sv n l lp siv civ
      capV capC w cnt iv ke1 (qPad8 w) (qPad8 cnt) 1 false 39) 43).heap
      (.base ⟨2⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hst0 := storeTarget_addr (ty := .array 8 tU64) hlook2
    (normalizeValueForTy_arr_u64 hlp hlpr)
  have h13 := stepFnIter_chain h12
    (stepFnIter_one (stepFn_store_step hst0))
  have hepb := ep_b_raw39 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 1 ch
  have h14 := stepFnIter_chain h13 hepb
  -- $res1 := runVals
  have hlook3 : Heap.lookup (qSt σ (qHeapEp nv sv n l lp siv civ
      capV capC w cnt 0 iv ke1 (qPad8 w) (qPad8 cnt) 1 39
      lp zeros8 zeros8) 43).heap (.base ⟨3⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hst1 := storeTarget_addr (ty := .array 8 tU64) hlook3
    (normalizeValueForTy_arr_u64 (qPad8_length w) (qPad8_range hw))
  have h15 := stepFnIter_chain h14
    (stepFnIter_one (stepFn_store_step hst1))
  have hepc := ep_c_raw39 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 1 ch
  have h16 := stepFnIter_chain h15 hepc
  -- $res2 := runCounts
  have hlook4 : Heap.lookup (qSt σ (qHeapEp nv sv n l lp siv civ
      capV capC w cnt 0 iv ke1 (qPad8 w) (qPad8 cnt) 1 39
      lp (qPad8 w) zeros8) 43).heap (.base ⟨4⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hst2 := storeTarget_addr (ty := .array 8 tU64) hlook4
    (normalizeValueForTy_arr_u64 (qPad8_length cnt) (qPad8_range hcnt))
  have h17 := stepFnIter_chain h16
    (stepFnIter_one (stepFn_store_step hst2))
  have hepd := ep_d_raw39 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 1 ch
  have h18 := stepFnIter_chain h17 hepd
  -- len(vals) once more, then convert + the $res3 store + return
  have hlen3 := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := []) (env := fcTopEnv 39)
    (k := .strictK (.convert tU64) [] [] (fcTopEnv 39)
      (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
        (.seqn #[]) (fcTopEnv 39) (epK 39 [.returnStmt])))
    (applyStrictOp_len_slice (σ := qSt σ (qHeapEp nv sv n l lp siv civ
        capV capC w cnt 0 iv ke1 (qPad8 w) (qPad8 cnt) 1 39
        lp (qPad8 w) (qPad8 cnt)) 43)
      (b := .base ⟨32⟩) (off := 0) (len := 1) (cap := capV)
      (elem := tU64) hcV))
  have h19 := stepFnIter_chain h18 hlen3
  have hepe := ep_e_raw39 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 1 ch
  exact stepFnIter_chain h19 hepe

/-- **The final copy loop + the epilogue, composed** (`A = 37`
layout): one iteration lifts `(w, cnt)` into the arrays, the loop
exits at `i = 1 = len(vals)`, and the four results are delivered.
151 steps. -/
theorem fcC37 (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (capV capC : Nat) (w cnt : Int)
    (hcV : 1 ≤ capV) (hcC : 1 ≤ capC)
    (hw : 0 ≤ w ∧ w < 2 ^ 64) (hcnt : 0 ≤ cnt ∧ cnt < 2 ^ 64)
    (hlp : lp.length = 8) (hlpr : ∀ v ∈ lp, 0 ≤ v ∧ v < 2 ^ 64)
    (iv : Int) (ch : Choices) :
    stepFnIter 151
      (qSt σ (qHeapFC nv sv n l lp siv civ capV capC w cnt iv ([] : Heap)
        zeros8 zeros8 0 true 37) 41) (fcHeadCfg 37) ch
      = .ok (.next .stop,
          qSt σ (qHeapEnd1 nv sv n l lp siv civ capV capC w cnt 1 iv ([] : Heap)
            (qPad8 w) (qPad8 cnt) 1 37) 41, ch) := by
  have hA0 := fc_A0_raw37 σ nv sv n l lp siv civ capV capC w cnt iv
    zeros8 zeros8 ch
  -- len(vals) = 1, then 0 < 1
  have hlen1 := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := []) (env := fcEnvB 37)
    (k := .strictK .lessCmp [.int 0 .int] [] (fcEnvB 37) (fcCmpK 37))
    (applyStrictOp_len_slice (σ := qSt σ (qHeapFC nv sv n l lp siv civ
        capV capC w cnt iv ([] : Heap) zeros8 zeros8 0 false 37) 41)
      (b := .base ⟨32⟩) (off := 0) (len := 1) (cap := capV)
      (elem := tU64) hcV))
  have hlt1 := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [.int 0 .int]) (env := fcEnvB 37) (k := fcCmpK 37)
    (applyStrictOp_lessCmp_int (σ := qSt σ (qHeapFC nv sv n l lp siv civ
        capV capC w cnt iv ([] : Heap) zeros8 zeros8 0 false 37) 41)
      (a := 0) (b := ((1 : Nat) : Int)) (k := .int) (k' := .int)))
  rw [show decide ((0 : Int) < ((1 : Nat) : Int)) = true from
    decide_eq_true (by omega)] at hlt1
  have h1 := stepFnIter_chain (stepFnIter_chain hA0 hlen1) hlt1
  have hb := fc_b_raw37 σ nv sv n l lp siv civ capV capC w cnt iv
    zeros8 zeros8 0 ch
  have h2 := stepFnIter_chain h1 hb
  -- vals[0] = w
  have hlookV : Heap.lookup (qSt σ (qHeapFC nv sv n l lp siv civ
      capV capC w cnt iv ([] : Heap) zeros8 zeros8 0 false 37) 41).heap
      (.base ⟨32⟩)
      = some ⟨some (.array capV tU64),
          .array ⟨(qPadL capV w).map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hreadV := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [qRunSliceV 32 capV]) (env := fcEnvB2 37)
    (k := fcVRhsK 37 0)
    (applyStrictOp_indexGet_slice (ik := .int) (i := 0) hlookV hcV
      (by omega) (by rfl)))
  have h3 := stepFnIter_chain h2 hreadV
  have hc := fc_c_raw37 σ nv sv n l lp siv civ capV capC w cnt iv
    zeros8 zeros8 0 (.int w .uint64) ch
  have h4 := stepFnIter_chain h3 hc
  -- runVals[0] := w
  have hlookA : Heap.lookup (qSt σ (qHeapFC nv sv n l lp siv civ
      capV capC w cnt iv ([] : Heap) zeros8 zeros8 0 false 37) 41).heap
      (.base ⟨37⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hstV := storeTarget_arrayLocal_u64 (a := ⟨37⟩) (N := 8) (i := 0)
    (ik := .int) (l := zeros8) (w := w) hlookA
    (by simp [zeros8]) (by simp [zeros8])
    (by intro x hx; rcases List.mem_replicate.mp hx with ⟨-, rfl⟩; omega)
    hw
  have h5 := stepFnIter_chain h4
    (stepFnIter_one (stepFn_store_step hstV))
  have hd := fc_d_raw37 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) zeros8 0 ch
  have h6 := stepFnIter_chain h5 hd
  -- counts[0] = cnt
  have hlookC : Heap.lookup (qSt σ (qHeapFC nv sv n l lp siv civ
      capV capC w cnt iv ([] : Heap) (qPad8 w) zeros8 0 false 37) 41).heap
      (.base ⟨36⟩)
      = some ⟨some (.array capC tU64),
          .array ⟨(qPadL capC cnt).map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hreadC := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [qRunSliceV 36 capC]) (env := fcEnvB2 37)
    (k := fcCRhsK 37 0)
    (applyStrictOp_indexGet_slice (ik := .int) (i := 0) hlookC hcC
      (by omega) (by rfl)))
  have h7 := stepFnIter_chain h6 hreadC
  have he := fc_e_raw37 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) zeros8 0 (.int cnt .uint64) ch
  have h8 := stepFnIter_chain h7 he
  -- runCounts[0] := cnt
  have hlookB : Heap.lookup (qSt σ (qHeapFC nv sv n l lp siv civ
      capV capC w cnt iv ([] : Heap) (qPad8 w) zeros8 0 false 37) 41).heap
      (.base ⟨38⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hstC := storeTarget_arrayLocal_u64 (a := ⟨38⟩) (N := 8) (i := 0)
    (ik := .int) (l := zeros8) (w := cnt) hlookB
    (by simp [zeros8]) (by simp [zeros8])
    (by intro x hx; rcases List.mem_replicate.mp hx with ⟨-, rfl⟩; omega)
    hcnt
  have h9 := stepFnIter_chain h8
    (stepFnIter_one (stepFn_store_step hstC))
  have hf := fc_f_raw37 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 0 ch
  have h10 := stepFnIter_chain h9 hf
  -- the second dispatch: i = 1, the test fails
  have hA1 := fc_A1_raw37 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 0 ch
  rw [show IntKind.normalize .int (IntKind.normalize .int ((0 : Int) + 1))
      = (1 : Int) from rfl] at hA1
  have hlen2 := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := []) (env := fcEnvB 37)
    (k := .strictK .lessCmp [.int 1 .int] [] (fcEnvB 37) (fcCmpK 37))
    (applyStrictOp_len_slice (σ := qSt σ (qHeapFC nv sv n l lp siv civ
        capV capC w cnt iv ([] : Heap) (qPad8 w) (qPad8 cnt) 1 false 37) 41)
      (b := .base ⟨32⟩) (off := 0) (len := 1) (cap := capV)
      (elem := tU64) hcV))
  have hlt2 := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [.int 1 .int]) (env := fcEnvB 37) (k := fcCmpK 37)
    (applyStrictOp_lessCmp_int (σ := qSt σ (qHeapFC nv sv n l lp siv civ
        capV capC w cnt iv ([] : Heap) (qPad8 w) (qPad8 cnt) 1 false 37) 41)
      (a := 1) (b := ((1 : Nat) : Int)) (k := .int) (k' := .int)))
  rw [show decide ((1 : Int) < ((1 : Nat) : Int)) = false from
    decide_eq_false (by omega)] at hlt2
  have h11 := stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h10 hA1) hlen2) hlt2
  have hepa := ep_a_raw37 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 1 ch
  have h12 := stepFnIter_chain h11 hepa
  -- $res0 := pre
  have hlook2 : Heap.lookup (qSt σ (qHeapFC nv sv n l lp siv civ
      capV capC w cnt iv ([] : Heap) (qPad8 w) (qPad8 cnt) 1 false 37) 41).heap
      (.base ⟨2⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hst0 := storeTarget_addr (ty := .array 8 tU64) hlook2
    (normalizeValueForTy_arr_u64 hlp hlpr)
  have h13 := stepFnIter_chain h12
    (stepFnIter_one (stepFn_store_step hst0))
  have hepb := ep_b_raw37 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 1 ch
  have h14 := stepFnIter_chain h13 hepb
  -- $res1 := runVals
  have hlook3 : Heap.lookup (qSt σ (qHeapEp nv sv n l lp siv civ
      capV capC w cnt 0 iv ([] : Heap) (qPad8 w) (qPad8 cnt) 1 37
      lp zeros8 zeros8) 41).heap (.base ⟨3⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hst1 := storeTarget_addr (ty := .array 8 tU64) hlook3
    (normalizeValueForTy_arr_u64 (qPad8_length w) (qPad8_range hw))
  have h15 := stepFnIter_chain h14
    (stepFnIter_one (stepFn_store_step hst1))
  have hepc := ep_c_raw37 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 1 ch
  have h16 := stepFnIter_chain h15 hepc
  -- $res2 := runCounts
  have hlook4 : Heap.lookup (qSt σ (qHeapEp nv sv n l lp siv civ
      capV capC w cnt 0 iv ([] : Heap) (qPad8 w) (qPad8 cnt) 1 37
      lp (qPad8 w) zeros8) 41).heap (.base ⟨4⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hst2 := storeTarget_addr (ty := .array 8 tU64) hlook4
    (normalizeValueForTy_arr_u64 (qPad8_length cnt) (qPad8_range hcnt))
  have h17 := stepFnIter_chain h16
    (stepFnIter_one (stepFn_store_step hst2))
  have hepd := ep_d_raw37 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 1 ch
  have h18 := stepFnIter_chain h17 hepd
  -- len(vals) once more, then convert + the $res3 store + return
  have hlen3 := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := []) (env := fcTopEnv 37)
    (k := .strictK (.convert tU64) [] [] (fcTopEnv 37)
      (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
        (.seqn #[]) (fcTopEnv 37) (epK 37 [.returnStmt])))
    (applyStrictOp_len_slice (σ := qSt σ (qHeapEp nv sv n l lp siv civ
        capV capC w cnt 0 iv ([] : Heap) (qPad8 w) (qPad8 cnt) 1 37
        lp (qPad8 w) (qPad8 cnt)) 41)
      (b := .base ⟨32⟩) (off := 0) (len := 1) (cap := capV)
      (elem := tU64) hcV))
  have h19 := stepFnIter_chain h18 hlen3
  have hepe := ep_e_raw37 σ nv sv n l lp siv civ capV capC w cnt iv
    (qPad8 w) (qPad8 cnt) 1 ch
  exact stepFnIter_chain h19 hepe

/-! ## The run, end to end -/

/-- The harness FRONT, composed: entry, the setup loop (the family
`seed + i/3`), the `pre` copy loop, the call, the `rle` prologue — to
the subject loop head. `238 + 110·n` steps. -/
theorem q_frontC (σ : ExecState) (n seed : Nat) (hn : n ≤ 3)
    (henter : ∀ (l lp : List Int) (siv civ : Int),
      enterFrame (qSt σ (qHeapCall ((n : Nat) : Int) ((seed : Nat) : Int)
          n l lp siv civ) 16) ⟨"rle"⟩ [qSliceS n]
        = .ok (rleFunc, rFrameEnv, [.base ⟨17⟩, .base ⟨18⟩],
            qSt σ (qHeapFrame ((n : Nat) : Int) ((seed : Nat) : Int)
              n l lp siv civ) 19))
    (ch : Choices) :
    stepFnIter (238 + 110 * n)
      (qSt σ (qHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)) 6) qHC0 ch
      = .ok (rHeadCfgQ,
          qSt σ (qHeapRle0 ((n : Nat) : Int) ((seed : Nat) : Int) n
            (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
            ((n : Nat) : Int) 0 true) 27, ch) := by
  have hnn : n < 2 ^ 63 := by omega
  have hE1 := q_E1_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) ch
  have hmk := stepFnIter_one
    (stepFn_makeSlice_u64_step (env := envC10Q)
      (k := .seq [qS2, qS3, qS4, qS5, qS6, qS7, qS8, qS9, qS10] envC10Q
        (.frame [] [] [] [] .stop))
      (q_make_apply σ ((n : Nat) : Int) ((seed : Nat) : Int) n ch))
  have hE2 := q_E2_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n ch
  have hA0 := su_A0_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (List.replicate n 0) 0 ch
  have hsu := su_loopQ σ n seed hnn 0 (by omega) ch
  rw [show rleFamily 0 seed ++ List.replicate (n - 0) 0
      = List.replicate n 0 from by simp [rleFamily],
    show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hsu
  have hentry := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hE1 hmk) hE2) hA0) hsu
  have hX := su_X_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) ((n : Nat) : Int) ch
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hentry
  have hthru := stepFnIter_chain hentry hX
  have hcA0 := cp_A0_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) zeros8 ((n : Nat) : Int) 0 ch
  have hcp := cp_loopQ σ n seed hnn (by omega) 0 (by omega) ch
  rw [show rlePre 0 seed = zeros8 from rlePre_zero seed,
    show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hcp
  have hthru2 := stepFnIter_chain (stepFnIter_chain hthru hcA0) hcp
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hthru2
  have hcX := cp_X_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) ch
  have hthru3 := stepFnIter_chain hthru2 hcX
  have hent := stepFnIter_one (ch := ch)
    (stepFn_call_enter (plans := qShapes) (env := callEnvQ)
      (k := qAfterCall) (vals := []) (v := qSliceS n)
      (henter (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
        ((n : Nat) : Int)))
  have hthru4 := stepFnIter_chain hthru3 hent
  have hR1a := r_R1a_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) ch
  have hR1b := r_R1b_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) ch
  have hall := stepFnIter_chain (stepFnIter_chain hthru4 hR1a) hR1b
  have harith : 10 + 1 + 42 + 25 + 57 * (n - 0) + 39 +
      (25 + 53 * (n - 0)) + 15 + 1 + 37 + 43 = 238 + 110 * n := by omega
  rw [show 10 + 1 = 11 from rfl] at hall
  -- normalize the accumulated step count
  have : stepFnIter (238 + 110 * n)
      (qSt σ (qHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)) 6) qHC0 ch
      = stepFnIter (11 + 42 + 25 + 57 * (n - 0) + 39 + 25 + 53 * (n - 0)
          + 15 + 1 + 37 + 43)
        (qSt σ (qHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)) 6) qHC0
        ch := by
    congr 1
    omega
  rw [this]
  exact hall

/-- The subject head's dispatch + exit test, composed (first
dispatch). -/
theorem r_headTest (σ : ExecState) (n seed : Nat) (ch : Choices) :
    stepFnIter 27
      (qSt σ (qHeapRle0 ((n : Nat) : Int) ((seed : Nat) : Int) n
        (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
        ((n : Nat) : Int) 0 true) 27) rHeadCfgQ ch
      = .ok (.retV (.bool (decide ((0 : Int) < ((n : Nat) : Int))))
            rCmpKQ,
          qSt σ (qHeapRle0 ((n : Nat) : Int) ((seed : Nat) : Int) n
            (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
            ((n : Nat) : Int) 0 false) 27, ch) := by
  have hA0 := r_A0_rawQ σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (rleFamily n seed) (rlePre n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) ch
  have hlen := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := []) (env := rBodyEnv)
    (k := .strictK .lessCmp [.int 0 .int] [] rBodyEnv rCmpKQ)
    (applyStrictOp_len_slice (σ := qSt σ (qHeapRle0 ((n : Nat) : Int)
        ((seed : Nat) : Int) n (rleFamily n seed) (rlePre n seed)
        ((n : Nat) : Int) ((n : Nat) : Int) 0 false) 27)
      (b := .base ⟨7⟩) (off := 0) (len := n) (cap := n) (elem := tU64)
      (Nat.le_refl n)))
  have hlt := stepFnIter_one (ch := ch) (stepFn_strict_apply
    (done := [.int 0 .int]) (env := rBodyEnv) (k := rCmpKQ)
    (applyStrictOp_lessCmp_int (σ := qSt σ (qHeapRle0 ((n : Nat) : Int)
        ((seed : Nat) : Int) n (rleFamily n seed) (rlePre n seed)
        ((n : Nat) : Int) ((n : Nat) : Int) 0 false) 27)
      (a := 0) (b := ((n : Nat) : Int)) (k := .int) (k' := .int)))
  exact stepFnIter_chain (stepFnIter_chain hA0 hlen) hlt

/-- **The `n = 3` run, end to end**: `1286` steps to the driver
terminal, with the spilled capacities existential. -/
theorem q_runs3 (σ : ExecState) (seed : Nat)
    (henter : ∀ (l lp : List Int) (siv civ : Int),
      enterFrame (qSt σ (qHeapCall ((3 : Nat) : Int) ((seed : Nat) : Int)
          3 l lp siv civ) 16) ⟨"rle"⟩ [qSliceS 3]
        = .ok (rleFunc, rFrameEnv, [.base ⟨17⟩, .base ⟨18⟩],
            qSt σ (qHeapFrame ((3 : Nat) : Int) ((seed : Nat) : Int)
              3 l lp siv civ) 19))
    (ch : Choices) :
    ∃ (k capV capC : Nat) (ch' : Choices), k ≤ 1286 ∧
      stepFnIter k
        (qSt σ (qHeap0 ((3 : Nat) : Int) ((seed : Nat) : Int)) 6) qHC0 ch
        = .ok (.next .stop,
            qSt σ (qHeapEnd1 ((3 : Nat) : Int) ((seed : Nat) : Int) 3
              (rleFamily 3 seed) (rlePre 3 seed) ((3 : Nat) : Int)
              ((3 : Nat) : Int) capV capC (wSeed seed) 3 1 3 ke2
              (qPad8 (wSeed seed)) (qPad8 3) 1 41) 45, ch') := by
  have hfront := q_frontC σ 3 seed (by omega) henter ch
  have hht := r_headTest σ 3 seed ch
  rw [show decide ((0 : Int) < ((3 : Nat) : Int)) = true from
    decide_eq_true (by exact_mod_cast Nat.zero_lt_succ 2)] at hht
  have h1 := stepFnIter_chain hfront hht
  obtain ⟨capV, capC, ch1, hcV1, hcV2, hcC1, hcC2, hiter0⟩ :=
    r_iter0C σ 3 seed (by omega) (by omega) ch
  have h2 := stepFnIter_chain h1 hiter0
  have hext1 := r_extC37 σ 3 seed capV capC hcV1 hcC1 (by omega)
    (by omega) ch1
  have h3 := stepFnIter_chain h2 hext1
  have hext2 := r_extC39 σ 3 seed capV capC hcV1 hcC1 (by omega)
    (by omega) ch1
  have h4 := stepFnIter_chain h3 hext2
  -- the exit dispatch: i → 3, the test fails
  have hA1 := r_A1_raw41 σ ((3 : Nat) : Int) ((seed : Nat) : Int) 3
    (rleFamily 3 seed) (rlePre 3 seed) ((3 : Nat) : Int)
    ((3 : Nat) : Int) capV capC (wSeed seed) 3 2 ch1
  rw [show IntKind.normalize .int (IntKind.normalize .int ((2 : Int) + 1))
      = (3 : Int) from rfl] at hA1
  have hlen := stepFnIter_one (ch := ch1) (stepFn_strict_apply
    (done := []) (env := rBodyEnv)
    (k := .strictK .lessCmp [.int 3 .int] [] rBodyEnv rCmpKQ)
    (applyStrictOp_len_slice (σ := qSt σ (qHeapRun ((3 : Nat) : Int)
        ((seed : Nat) : Int) 3 (rleFamily 3 seed) (rlePre 3 seed)
        ((3 : Nat) : Int) ((3 : Nat) : Int) capV capC (wSeed seed) 3 3
        false ke2) 41)
      (b := .base ⟨7⟩) (off := 0) (len := 3) (cap := 3) (elem := tU64)
      (by omega)))
  have hlt := stepFnIter_one (ch := ch1) (stepFn_strict_apply
    (done := [.int 3 .int]) (env := rBodyEnv) (k := rCmpKQ)
    (applyStrictOp_lessCmp_int (σ := qSt σ (qHeapRun ((3 : Nat) : Int)
        ((seed : Nat) : Int) 3 (rleFamily 3 seed) (rlePre 3 seed)
        ((3 : Nat) : Int) ((3 : Nat) : Int) capV capC (wSeed seed) 3 3
        false ke2) 41)
      (a := 3) (b := ((3 : Nat) : Int)) (k := .int) (k' := .int)))
  rw [show decide ((3 : Int) < ((3 : Nat) : Int)) = false from
    decide_eq_false (by exact_mod_cast Nat.lt_irrefl 3)] at hlt
  have h5 := stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h4 hA1) hlen) hlt
  have hexit := r_exit_raw41 σ ((3 : Nat) : Int) ((seed : Nat) : Int) 3
    (rleFamily 3 seed) (rlePre 3 seed) ((3 : Nat) : Int)
    ((3 : Nat) : Int) capV capC (wSeed seed) 3 3 ch1
  have h6 := stepFnIter_chain h5 hexit
  have hfc := fcC41 σ ((3 : Nat) : Int) ((seed : Nat) : Int) 3
    (rleFamily 3 seed) (rlePre 3 seed) ((3 : Nat) : Int)
    ((3 : Nat) : Int) capV capC (wSeed seed) 3 hcV1 hcC1
    (wSeed_range seed) (by omega) (rlePre_length (by omega))
    rlePre_range 3 ch1
  have h7 := stepFnIter_chain h6 hfc
  exact ⟨_, capV, capC, ch1, by omega, h7⟩

/-- **The `n = 2` run, end to end**: `1033` steps to the driver
terminal, with the spilled capacities existential. -/
theorem q_runs2 (σ : ExecState) (seed : Nat)
    (henter : ∀ (l lp : List Int) (siv civ : Int),
      enterFrame (qSt σ (qHeapCall ((2 : Nat) : Int) ((seed : Nat) : Int)
          2 l lp siv civ) 16) ⟨"rle"⟩ [qSliceS 2]
        = .ok (rleFunc, rFrameEnv, [.base ⟨17⟩, .base ⟨18⟩],
            qSt σ (qHeapFrame ((2 : Nat) : Int) ((seed : Nat) : Int)
              2 l lp siv civ) 19))
    (ch : Choices) :
    ∃ (k capV capC : Nat) (ch' : Choices), k ≤ 1033 ∧
      stepFnIter k
        (qSt σ (qHeap0 ((2 : Nat) : Int) ((seed : Nat) : Int)) 6) qHC0 ch
        = .ok (.next .stop,
            qSt σ (qHeapEnd1 ((2 : Nat) : Int) ((seed : Nat) : Int) 2
              (rleFamily 2 seed) (rlePre 2 seed) ((2 : Nat) : Int)
              ((2 : Nat) : Int) capV capC (wSeed seed) 2 1 2 ke1
              (qPad8 (wSeed seed)) (qPad8 2) 1 39) 43, ch') := by
  have hfront := q_frontC σ 2 seed (by omega) henter ch
  have hht := r_headTest σ 2 seed ch
  rw [show decide ((0 : Int) < ((2 : Nat) : Int)) = true from
    decide_eq_true (by exact_mod_cast Nat.zero_lt_succ 1)] at hht
  have h1 := stepFnIter_chain hfront hht
  obtain ⟨capV, capC, ch1, hcV1, hcV2, hcC1, hcC2, hiter0⟩ :=
    r_iter0C σ 2 seed (by omega) (by omega) ch
  have h2 := stepFnIter_chain h1 hiter0
  have hext1 := r_extC37 σ 2 seed capV capC hcV1 hcC1 (by omega)
    (by omega) ch1
  have h3 := stepFnIter_chain h2 hext1
  -- the exit dispatch: i → 2, the test fails
  have hA1 := r_A1_raw39 σ ((2 : Nat) : Int) ((seed : Nat) : Int) 2
    (rleFamily 2 seed) (rlePre 2 seed) ((2 : Nat) : Int)
    ((2 : Nat) : Int) capV capC (wSeed seed) 2 1 ch1
  rw [show IntKind.normalize .int (IntKind.normalize .int ((1 : Int) + 1))
      = (2 : Int) from rfl] at hA1
  have hlen := stepFnIter_one (ch := ch1) (stepFn_strict_apply
    (done := []) (env := rBodyEnv)
    (k := .strictK .lessCmp [.int 2 .int] [] rBodyEnv rCmpKQ)
    (applyStrictOp_len_slice (σ := qSt σ (qHeapRun ((2 : Nat) : Int)
        ((seed : Nat) : Int) 2 (rleFamily 2 seed) (rlePre 2 seed)
        ((2 : Nat) : Int) ((2 : Nat) : Int) capV capC (wSeed seed) 2 2
        false ke1) 39)
      (b := .base ⟨7⟩) (off := 0) (len := 2) (cap := 2) (elem := tU64)
      (by omega)))
  have hlt := stepFnIter_one (ch := ch1) (stepFn_strict_apply
    (done := [.int 2 .int]) (env := rBodyEnv) (k := rCmpKQ)
    (applyStrictOp_lessCmp_int (σ := qSt σ (qHeapRun ((2 : Nat) : Int)
        ((seed : Nat) : Int) 2 (rleFamily 2 seed) (rlePre 2 seed)
        ((2 : Nat) : Int) ((2 : Nat) : Int) capV capC (wSeed seed) 2 2
        false ke1) 39)
      (a := 2) (b := ((2 : Nat) : Int)) (k := .int) (k' := .int)))
  rw [show decide ((2 : Int) < ((2 : Nat) : Int)) = false from
    decide_eq_false (by exact_mod_cast Nat.lt_irrefl 2)] at hlt
  have h5 := stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h3 hA1) hlen) hlt
  have hexit := r_exit_raw39 σ ((2 : Nat) : Int) ((seed : Nat) : Int) 2
    (rleFamily 2 seed) (rlePre 2 seed) ((2 : Nat) : Int)
    ((2 : Nat) : Int) capV capC (wSeed seed) 2 2 ch1
  have h6 := stepFnIter_chain h5 hexit
  have hfc := fcC39 σ ((2 : Nat) : Int) ((seed : Nat) : Int) 2
    (rleFamily 2 seed) (rlePre 2 seed) ((2 : Nat) : Int)
    ((2 : Nat) : Int) capV capC (wSeed seed) 2 hcV1 hcC1
    (wSeed_range seed) (by omega) (rlePre_length (by omega))
    rlePre_range 2 ch1
  have h7 := stepFnIter_chain h6 hfc
  exact ⟨_, capV, capC, ch1, by omega, h7⟩

/-- **The `n = 1` run, end to end**: `780` steps to the driver
terminal, with the spilled capacities existential. -/
theorem q_runs1 (σ : ExecState) (seed : Nat)
    (henter : ∀ (l lp : List Int) (siv civ : Int),
      enterFrame (qSt σ (qHeapCall ((1 : Nat) : Int) ((seed : Nat) : Int)
          1 l lp siv civ) 16) ⟨"rle"⟩ [qSliceS 1]
        = .ok (rleFunc, rFrameEnv, [.base ⟨17⟩, .base ⟨18⟩],
            qSt σ (qHeapFrame ((1 : Nat) : Int) ((seed : Nat) : Int)
              1 l lp siv civ) 19))
    (ch : Choices) :
    ∃ (k capV capC : Nat) (ch' : Choices), k ≤ 780 ∧
      stepFnIter k
        (qSt σ (qHeap0 ((1 : Nat) : Int) ((seed : Nat) : Int)) 6) qHC0 ch
        = .ok (.next .stop,
            qSt σ (qHeapEnd1 ((1 : Nat) : Int) ((seed : Nat) : Int) 1
              (rleFamily 1 seed) (rlePre 1 seed) ((1 : Nat) : Int)
              ((1 : Nat) : Int) capV capC (wSeed seed) 1 1 1 ([] : Heap)
              (qPad8 (wSeed seed)) (qPad8 1) 1 37) 41, ch') := by
  have hfront := q_frontC σ 1 seed (by omega) henter ch
  have hht := r_headTest σ 1 seed ch
  rw [show decide ((0 : Int) < ((1 : Nat) : Int)) = true from
    decide_eq_true (by exact_mod_cast Nat.zero_lt_succ 0)] at hht
  have h1 := stepFnIter_chain hfront hht
  obtain ⟨capV, capC, ch1, hcV1, hcV2, hcC1, hcC2, hiter0⟩ :=
    r_iter0C σ 1 seed (by omega) (by omega) ch
  have h2 := stepFnIter_chain h1 hiter0
  -- the exit dispatch: i → 1, the test fails
  have hA1 := r_A1_raw37 σ ((1 : Nat) : Int) ((seed : Nat) : Int) 1
    (rleFamily 1 seed) (rlePre 1 seed) ((1 : Nat) : Int)
    ((1 : Nat) : Int) capV capC (wSeed seed) 1 0 ch1
  rw [show IntKind.normalize .int (IntKind.normalize .int ((0 : Int) + 1))
      = (1 : Int) from rfl] at hA1
  have hlen := stepFnIter_one (ch := ch1) (stepFn_strict_apply
    (done := []) (env := rBodyEnv)
    (k := .strictK .lessCmp [.int 1 .int] [] rBodyEnv rCmpKQ)
    (applyStrictOp_len_slice (σ := qSt σ (qHeapRun ((1 : Nat) : Int)
        ((seed : Nat) : Int) 1 (rleFamily 1 seed) (rlePre 1 seed)
        ((1 : Nat) : Int) ((1 : Nat) : Int) capV capC (wSeed seed) 1 1
        false ([] : Heap)) 37)
      (b := .base ⟨7⟩) (off := 0) (len := 1) (cap := 1) (elem := tU64)
      (by omega)))
  have hlt := stepFnIter_one (ch := ch1) (stepFn_strict_apply
    (done := [.int 1 .int]) (env := rBodyEnv) (k := rCmpKQ)
    (applyStrictOp_lessCmp_int (σ := qSt σ (qHeapRun ((1 : Nat) : Int)
        ((seed : Nat) : Int) 1 (rleFamily 1 seed) (rlePre 1 seed)
        ((1 : Nat) : Int) ((1 : Nat) : Int) capV capC (wSeed seed) 1 1
        false ([] : Heap)) 37)
      (a := 1) (b := ((1 : Nat) : Int)) (k := .int) (k' := .int)))
  rw [show decide ((1 : Int) < ((1 : Nat) : Int)) = false from
    decide_eq_false (by exact_mod_cast Nat.lt_irrefl 1)] at hlt
  have h5 := stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h2 hA1) hlen) hlt
  have hexit := r_exit_raw37 σ ((1 : Nat) : Int) ((seed : Nat) : Int) 1
    (rleFamily 1 seed) (rlePre 1 seed) ((1 : Nat) : Int)
    ((1 : Nat) : Int) capV capC (wSeed seed) 1 1 ch1
  have h6 := stepFnIter_chain h5 hexit
  have hfc := fcC37 σ ((1 : Nat) : Int) ((seed : Nat) : Int) 1
    (rleFamily 1 seed) (rlePre 1 seed) ((1 : Nat) : Int)
    ((1 : Nat) : Int) capV capC (wSeed seed) 1 hcV1 hcC1
    (wSeed_range seed) (by omega) (rlePre_length (by omega))
    rlePre_range 1 ch1
  have h7 := stepFnIter_chain h6 hfc
  exact ⟨_, capV, capC, ch1, by omega, h7⟩

/-- **The `n = 0` run, end to end**: `419` steps; no run event ever
fires and no choice is consumed. -/
theorem q_runs0 (σ : ExecState) (seed : Nat)
    (henter : ∀ (l lp : List Int) (siv civ : Int),
      enterFrame (qSt σ (qHeapCall ((0 : Nat) : Int) ((seed : Nat) : Int)
          0 l lp siv civ) 16) ⟨"rle"⟩ [qSliceS 0]
        = .ok (rleFunc, rFrameEnv, [.base ⟨17⟩, .base ⟨18⟩],
            qSt σ (qHeapFrame ((0 : Nat) : Int) ((seed : Nat) : Int)
              0 l lp siv civ) 19))
    (ch : Choices) :
    ∃ (k : Nat) (ch' : Choices), k ≤ 527 ∧
      stepFnIter k
        (qSt σ (qHeap0 ((0 : Nat) : Int) ((seed : Nat) : Int)) 6) qHC0 ch
        = .ok (.next .stop,
            qSt σ (qHeapEnd0 ((0 : Nat) : Int) ((seed : Nat) : Int) 0
              (rleFamily 0 seed) (rlePre 0 seed) ((0 : Nat) : Int)
              ((0 : Nat) : Int) 0) 31, ch') := by
  have hfront := q_frontC σ 0 seed (by omega) henter ch
  have hht := r_headTest σ 0 seed ch
  rw [show decide ((0 : Int) < ((0 : Nat) : Int)) = false from
    decide_eq_false (by exact_mod_cast Nat.lt_irrefl 0)] at hht
  have h1 := stepFnIter_chain hfront hht
  have hexit := r_exit_raw0 σ ((0 : Nat) : Int) ((seed : Nat) : Int) 0
    (rleFamily 0 seed) (rlePre 0 seed) ((0 : Nat) : Int)
    ((0 : Nat) : Int) ch
  have h2 := stepFnIter_chain h1 hexit
  have hfcA0 := fc_A0_raw0 σ ((0 : Nat) : Int) ((seed : Nat) : Int) 0
    (rleFamily 0 seed) (rlePre 0 seed) ((0 : Nat) : Int)
    ((0 : Nat) : Int) ch
  have h3 := stepFnIter_chain h2 hfcA0
  have hepa := ep_a_raw0 σ ((0 : Nat) : Int) ((seed : Nat) : Int) 0
    (rleFamily 0 seed) (rlePre 0 seed) ((0 : Nat) : Int)
    ((0 : Nat) : Int) ch
  have h4 := stepFnIter_chain h3 hepa
  -- $res0 := pre
  have hlook2 : Heap.lookup (qSt σ (qHeapPost0 ((0 : Nat) : Int)
      ((seed : Nat) : Int) 0 (rleFamily 0 seed) (rlePre 0 seed)
      ((0 : Nat) : Int) ((0 : Nat) : Int) 0 false) 31).heap (.base ⟨2⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun x => .int x .uint64)⟩⟩ := by
    with_unfolding_all rfl
  have hst0 := storeTarget_addr (ty := .array 8 tU64) hlook2
    (normalizeValueForTy_arr_u64 (rlePre_length (by omega))
      (rlePre_range (m := 0) (seed := seed)))
  have h5 := stepFnIter_chain h4
    (stepFnIter_one (stepFn_store_step hst0))
  have hz := ep_z_raw0 σ ((0 : Nat) : Int) ((seed : Nat) : Int) 0
    (rleFamily 0 seed) (rlePre 0 seed) ((0 : Nat) : Int)
    ((0 : Nat) : Int) ch
  have h6 := stepFnIter_chain h5 hz
  exact ⟨_, ch, by omega, h6⟩

end GoLean.Examples.RunLength

