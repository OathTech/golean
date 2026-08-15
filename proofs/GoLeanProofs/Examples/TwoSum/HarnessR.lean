import GoLeanProofs.Examples.TwoSum.Machine

/-!
# TwoSum — the harness half of the run (entry, setup, copy, prologue)

Raw segments and loop inductions from the harness entry to the SUBJECT
OUTER LOOP HEAD: entry and `make([]uint64, n)`, the setup loop
(`s[i] = seed + i`, 53 steps per iteration, the P5 schema), the copy
loop (`vals[i] = s[i]`, 53 steps), the two-argument `twoSum(s, target)`
call boundary, and the subject's prologue (`n := uint64(len(s))`,
split at the `len` apply — the one heap-consulting op in it).

Everything is PROGRAM-generic (`tSt σ H na` — abstract `σ`, only
heap/nextAddr pinned); the ONE step that consults the program (the
`twoSum` frame entry) enters as the `henter` hypothesis, discharged at
the pinned program in `Subject.lean`.

Per-segment step counts (probe-measured with the lane's generic tracer
`.tmp/Probe.lean`, then re-checked by `rfl` here):

| phase | steps |
|---|---|
| entry → makeSlice apply | 10 |
| makeSlice apply → setup head | 42 |
| setup dispatch (first / later) | 25 / 29 |
| one setup iteration | 53 |
| setup exit → copy head | 39 |
| copy dispatch (first / later) | 25 / 29 |
| one copy iteration | 53 |
| copy exit → both call args delivered | 17 |
| `enterFrame` (the one program step) | 1 |
| subject prologue (split at `len(s)`) | 12 + 1 + 34 |
-/

namespace GoLean.Examples.TwoSum

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## Raw run segments — PROGRAM-generic throughout -/

/-- Entry A: body start → the `$c9` makeSlice apply point. 10 steps. -/
theorem t_E1_raw (σ : ExecState) (nv sv tv : Int) (ch : Choices) :
    stepFnIter 10 (tSt σ (tsHeap0 nv sv tv) 6) tHC0 ch
      = .ok (.retV (.int nv .uint64)
          (.stmtOpK (.makeSlice tU64 false) 1
            [.addr (.base ⟨6⟩)] [] envC9T
            (.seq [tS2, tS3, tS4, tS5, tS6, tS7] envC9T
              (.frame [] [] [] [] .stop))),
        tSt σ (tsHeapC9 nv sv tv) 7, ch) := by
  with_unfolding_all rfl

/-- **`make([]uint64, n)` at SYMBOLIC `n`.** -/
theorem t_make_apply (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (ch : Choices) :
    applyStmtOp (tSt σ (tsHeapC9 nv sv tv) 7) ch (.makeSlice tU64 false) 1
      [.addr (.base ⟨6⟩), .int (n : Nat) .uint64]
      = .ok (tSt σ (tsHeapMake nv sv tv n) 8, ch) := by
  have hnn1 := natFromNonneg_cast
    "runtime error: makeslice: len out of range" n
  have hnn2 := natFromNonneg_cast
    "runtime error: makeslice: cap out of range" n
  have hb := GoLean.Iris.buildDefaultArrayValue_int
    (tSt σ (tsHeapC9 nv sv tv) 7) .uint64 n
  have harr : (List.replicate n (GoValue.int 0 .uint64)).toArray
      = (⟨(List.replicate n (0 : Int)).map
          (fun v => GoValue.int v .uint64)⟩ : Array GoValue) := by
    simp [List.map_replicate]
  rw [harr] at hb
  simp only [applyStmtOp, applyStmtOpCore, valueAsInt, valueAsLoc,
    hnn1, hnn2, hb, Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (Nat.lt_irrefl n)]
  with_unfolding_all rfl

/-- Entry B: `s := $c9`, the setup counter and flag → the setup loop
head. 42 steps. -/
theorem t_E2_raw (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (ch : Choices) :
    stepFnIter 42 (tSt σ (tsHeapMake nv sv tv n) 8)
      (.next (.seq [tS2, tS3, tS4, tS5, tS6, tS7] envC9T
        (.frame [] [] [] [] .stop))) ch
      = .ok (suHeadCfgT,
          tSt σ (tsHeapSu nv sv tv n (List.replicate n 0) 0 true) 11,
          ch) := by
  with_unfolding_all rfl

/-! ### The setup loop -/

theorem su_A0_rawT (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 25 (tSt σ (tsHeapSu nv sv tv n l iv true) 11) suHeadCfgT ch
      = .ok (.retV (.bool (decide (iv < nv))) suCmpKT,
          tSt σ (tsHeapSu nv sv tv n l iv false) 11, ch) := by
  with_unfolding_all rfl

theorem su_A1_rawT (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 29 (tSt σ (tsHeapSu nv sv tv n l iv false) 11) suHeadCfgT ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < nv))) suCmpKT,
          tSt σ (tsHeapSu nv sv tv n l
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false) 11, ch) := by
  with_unfolding_all rfl

/-- Setup fill: test true → the element-store point. 18 steps. -/
theorem su_B1_rawT (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 18 (tSt σ (tsHeapSu nv sv tv n l iv false) 11)
      (.retV (.bool true) suCmpKT) ch
      = .ok (.next (.storeK [suRefT n iv]
            [.int (IntKind.normalize .uint64 (sv + iv)) .uint64]
            (.seqn #[]) suEnvT2 suStTailT),
          tSt σ (tsHeapSu nv sv tv n l iv false) 11, ch) := by
  with_unfolding_all rfl

theorem su_D_rawT (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 5 (tSt σ (tsHeapSu nv sv tv n l iv false) 11)
      (.next (.storeK [] [] (.seqn #[]) suEnvT2 suStTailT)) ch
      = .ok (suHeadCfgT, tSt σ (tsHeapSu nv sv tv n l iv false) 11,
          ch) := by
  with_unfolding_all rfl

/-- Setup exit: test false → `var vals` declared and the copy loop
head. 39 steps. -/
theorem su_X_rawT (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 39 (tSt σ (tsHeapSu nv sv tv n l iv false) 11)
      (.retV (.bool false) suCmpKT) ch
      = .ok (cpHeadCfgT,
          tSt σ (tsHeapCp nv sv tv n l zeros8 iv 0 true) 14, ch) := by
  with_unfolding_all rfl

/-! ### The copy loop -/

theorem cp_A0_rawT (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 25 (tSt σ (tsHeapCp nv sv tv n l lp siv civ true) 14)
      cpHeadCfgT ch
      = .ok (.retV (.bool (decide (civ < nv))) cpCmpKT,
          tSt σ (tsHeapCp nv sv tv n l lp siv civ false) 14, ch) := by
  with_unfolding_all rfl

theorem cp_A1_rawT (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 29 (tSt σ (tsHeapCp nv sv tv n l lp siv civ false) 14)
      cpHeadCfgT ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1))
              < nv))) cpCmpKT,
          tSt σ (tsHeapCp nv sv tv n l lp siv
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1)))
            false) 14, ch) := by
  with_unfolding_all rfl

/-- Copy phase 1: test true → the `vals[i]` target banked, the `s[i]`
read at its apply point. 16 steps. -/
theorem cp_B1_rawT (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 16 (tSt σ (tsHeapCp nv sv tv n l lp siv civ false) 14)
      (.retV (.bool true) cpCmpKT) ch
      = .ok (.retV (.int civ .uint64)
            (.strictK .indexGet [tsSliceS n] [] cpEnvT2 (cpRhsKT civ)),
          tSt σ (tsHeapCp nv sv tv n l lp siv civ false) 14, ch) := by
  with_unfolding_all rfl

theorem cp_B2_rawT (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1 (tSt σ (tsHeapCp nv sv tv n l lp siv civ false) 14)
      (.retV w (cpRhsKT civ)) ch
      = .ok (.next (.storeK [cpRefT civ] [w] (.seqn #[]) cpEnvT2 cpStTailT),
          tSt σ (tsHeapCp nv sv tv n l lp siv civ false) 14, ch) := by
  with_unfolding_all rfl

theorem cp_D_rawT (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 5 (tSt σ (tsHeapCp nv sv tv n l lp siv civ false) 14)
      (.next (.storeK [] [] (.seqn #[]) cpEnvT2 cpStTailT)) ch
      = .ok (cpHeadCfgT, tSt σ (tsHeapCp nv sv tv n l lp siv civ false) 14,
          ch) := by
  with_unfolding_all rfl

/-- Copy exit: test false → the harness's receivers `i`/`j` declared
and BOTH `twoSum(s, target)` arguments delivered at the drained
`callArgsK`. 17 steps. -/
theorem cp_X_rawT (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 17 (tSt σ (tsHeapCp nv sv tv n l lp siv civ false) 14)
      (.retV (.bool false) cpCmpKT) ch
      = .ok (.retV (.int tv .uint64) (tCallArgsK n),
          tSt σ (tsHeapCall nv sv tv n l lp siv civ) 16, ch) := by
  with_unfolding_all rfl

/-! ### The `twoSum` prologue

Split at `len(s)`: the length op reads the slice against the heap, so
it is a conditioned step, not a definitional one. -/

/-- Prologue A: `n` declared → the `len(s)` apply point. 12 steps. -/
theorem t_preA_rawT (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp : Int) (ch : Choices) :
    stepFnIter 12 (tSt σ (tsHeapFrame nv sv tv n l lp siv civ tvp) 20)
      (.exec twoSumFunc.body tFrameEnv tFrameK) ch
      = .ok (.retV (tsSliceS n) tLenKP,
          tSt σ (tsHeapPro nv sv tv n l lp siv civ tvp) 21, ch) := by
  with_unfolding_all rfl

/-- Prologue B: the length delivered at the conversion → `n` stored,
the outer counter and flag, the outer loop head. 34 steps. -/
theorem t_preB_rawT (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp : Int) (w : Int) (ch : Choices) :
    stepFnIter 34 (tSt σ (tsHeapPro nv sv tv n l lp siv civ tvp) 21)
      (.retV (.int w .int) tConvK) ch
      = .ok (tOutHeadCfg,
          tSt σ (tsHeapOut nv sv tv n l lp siv civ tvp
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 w))
            0 true) 23, ch) := by
  with_unfolding_all rfl

/-! ## The setup loop, cleaned + its induction (the P5 schema) -/

/-- One setup iteration from the exit test's true delivery at `i`.
53 steps materialize one wrapped `seed + i` element. -/
theorem su_iterT (σ : ExecState) (n seed target : Nat) (i : Nat)
    (hn : n < 2 ^ 63) (hi : i < n) (ch : Choices) :
    stepFnIter 53
      (tSt σ (tsHeapSu ((n : Nat) : Int) ((seed : Nat) : Int)
        ((target : Nat) : Int) n
        (tsFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false) 11)
      (.retV (.bool true) suCmpKT) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) suCmpKT,
          tSt σ (tsHeapSu ((n : Nat) : Int) ((seed : Nat) : Int)
            ((target : Nat) : Int) n
            (tsFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
            ((i + 1 : Nat) : Int) false) 11, ch) := by
  have hB := su_B1_rawT σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((target : Nat) : Int) n (tsFamily i seed ++ List.replicate (n - i) 0)
    ((i : Nat) : Int) ch
  rw [unorm_add_nat seed i] at hB
  have hw : (0 : Int) ≤ (((seed + i) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + i) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + i) (y := 2 ^ 64) (by omega)
    omega
  have hst := storeTarget_slice_u64
    (σ := tSt σ (tsHeapSu ((n : Nat) : Int) ((seed : Nat) : Int)
      ((target : Nat) : Int) n
      (tsFamily i seed ++ List.replicate (n - i) 0)
      ((i : Nat) : Int) false) 11)
    (a := ⟨7⟩) (off := 0) (len := n) (cap := n) (i := i) (n := n)
    (ik := .uint64) (l := tsFamily i seed ++ List.replicate (n - i) 0)
    (w := (((seed + i) % 2 ^ 64 : Nat) : Int))
    (lookup_suT σ ((n : Nat) : Int) ((seed : Nat) : Int)
      ((target : Nat) : Int) n
      (tsFamily i seed ++ List.replicate (n - i) 0) ((i : Nat) : Int)
      false 11)
    (Nat.le_refl n) hi
    (by rw [List.length_append, tsFamily_length, List.length_replicate]
        omega)
    (by rw [List.length_append, tsFamily_length, List.length_replicate]
        omega)
    tsFamilyZ_range hw
  rw [Nat.zero_add, tsFamily_set hi] at hst
  have h1 := stepFnIter_chain hB (stepFnIter_one (stepFn_store_step hst))
  have hD := su_D_rawT σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((target : Nat) : Int) n
    (tsFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
    ((i : Nat) : Int) ch
  have h2 := stepFnIter_chain h1 hD
  have hA1 := su_A1_rawT σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((target : Nat) : Int) n
    (tsFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
    ((i : Nat) : Int) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  exact stepFnIter_chain h2 hA1

/-- **The setup loop**, by the P5 iteration schema: `53·(n−i)` steps
materialize the wrapped `seed + i` family. -/
theorem su_loopT (σ : ExecState) (n seed target : Nat) (hn : n < 2 ^ 63) :
    ∀ i, i ≤ n → ∀ ch : Choices,
    stepFnIter (53 * (n - i))
      (tSt σ (tsHeapSu ((n : Nat) : Int) ((seed : Nat) : Int)
        ((target : Nat) : Int) n
        (tsFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false) 11)
      (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
        suCmpKT) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) suCmpKT,
          tSt σ (tsHeapSu ((n : Nat) : Int) ((seed : Nat) : Int)
            ((target : Nat) : Int) n (tsFamily n seed)
            ((n : Nat) : Int) false) 11, ch) := by
  intro i hin ch
  have hgen := stepFnIter_iterate (c := 53) (n := n)
    (T := fun j => tSt σ (tsHeapSu ((n : Nat) : Int) ((seed : Nat) : Int)
      ((target : Nat) : Int) n
      (tsFamily j seed ++ List.replicate (n - j) 0)
      ((j : Nat) : Int) false) 11)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int)
      < ((n : Nat) : Int)))) suCmpKT)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact su_iterT σ n seed target j hn hj ch')
    i hin ch
  simpa using hgen

/-! ## The copy loop, cleaned + its induction -/

theorem cp_iterT (σ : ExecState) (n seed target : Nat) (siv : Int)
    (m : Nat) (hn : n < 2 ^ 63) (hcap : n ≤ 8) (hm : m < n)
    (ch : Choices) :
    stepFnIter 53
      (tSt σ (tsHeapCp ((n : Nat) : Int) ((seed : Nat) : Int)
        ((target : Nat) : Int) n (tsFamily n seed) (tsPre m seed) siv
        ((m : Nat) : Int) false) 14)
      (.retV (.bool true) cpCmpKT) ch
      = .ok (.retV (.bool (decide
            (((m + 1 : Nat) : Int) < ((n : Nat) : Int)))) cpCmpKT,
          tSt σ (tsHeapCp ((n : Nat) : Int) ((seed : Nat) : Int)
            ((target : Nat) : Int) n (tsFamily n seed)
            (tsPre (m + 1) seed) siv ((m + 1 : Nat) : Int) false) 14,
          ch) := by
  have hB1 := cp_B1_rawT σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((target : Nat) : Int) n (tsFamily n seed) (tsPre m seed) siv
    ((m : Nat) : Int) ch
  have hget : (⟨(tsFamily n seed).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + m]?
      = some (.int (((seed + m) % 2 ^ 64 : Nat) : Int) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by rw [tsFamily_length]; omega),
      tsFamily_getD hm]
  have hread := stepFn_strict_apply (done := [tsSliceS n]) (env := cpEnvT2)
    (k := cpRhsKT ((m : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .uint64)
      (lookup_cpS_T σ ((n : Nat) : Int) ((seed : Nat) : Int)
        ((target : Nat) : Int) n (tsFamily n seed) (tsPre m seed) siv
        ((m : Nat) : Int) false 14)
      (Nat.le_refl n) hm hget)
  have hB2 := cp_B2_rawT σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((target : Nat) : Int) n (tsFamily n seed) (tsPre m seed) siv
    ((m : Nat) : Int)
    (.int (((seed + m) % 2 ^ 64 : Nat) : Int) .uint64) ch
  have hw : (0 : Int) ≤ (((seed + m) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + m) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + m) (y := 2 ^ 64) (by omega)
    omega
  have hst := storeTarget_arrayLocal_u64 (a := ⟨11⟩) (N := 8) (i := m)
    (ik := .uint64) (l := tsPre m seed)
    (w := (((seed + m) % 2 ^ 64 : Nat) : Int))
    (lookup_cpVals_T σ ((n : Nat) : Int) ((seed : Nat) : Int)
      ((target : Nat) : Int) n (tsFamily n seed) (tsPre m seed) siv
      ((m : Nat) : Int) false 14)
    (by rw [tsPre_length (by omega)]; omega)
    (tsPre_length (by omega)) tsPre_range hw
  rw [tsPre_set (by omega : m < 8)] at hst
  have hD := cp_D_rawT σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((target : Nat) : Int) n (tsFamily n seed) (tsPre (m + 1) seed) siv
    ((m : Nat) : Int) ch
  have hA1 := cp_A1_rawT σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((target : Nat) : Int) n (tsFamily n seed) (tsPre (m + 1) seed) siv
    ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  have h1 := stepFnIter_chain hB1 (stepFnIter_one hread)
  have h2 := stepFnIter_chain h1 hB2
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hst))
  exact stepFnIter_chain (stepFnIter_chain h3 hD) hA1

/-- **The copy loop + the call + the prologue**: from the exit-test
delivery at `m`, the run reaches the subject's OUTER LOOP HEAD within
`53·μ + 65` steps — the copy exit (17), the ONE program-consulting
`enterFrame` step, and the `twoSum` prologue (12 + 1 + 34). -/
theorem cp_loopT (σ : ExecState) (n seed target : Nat) (hn : n < 2 ^ 63)
    (hcap : n ≤ 8) (htgt : target < 2 ^ 64)
    (henter : ∀ (l lp : List Int) (siv civ : Int),
      enterFrame (tSt σ (tsHeapCall ((n : Nat) : Int) ((seed : Nat) : Int)
          ((target : Nat) : Int) n l lp siv civ) 16) ⟨"twoSum"⟩
          [tsSliceS n, .int ((target : Nat) : Int) .uint64]
        = .ok (twoSumFunc, tFrameEnv, [.base ⟨18⟩, .base ⟨19⟩],
            tSt σ (tsHeapFrame ((n : Nat) : Int) ((seed : Nat) : Int)
              ((target : Nat) : Int) n l lp siv civ
              (IntKind.normalize .uint64 ((target : Nat) : Int))) 20)) :
    ∀ μ m : Nat, m + μ = n → ∀ ch : Choices,
    ∃ k : Nat, k ≤ 53 * μ + 65 ∧
      stepFnIter k
        (tSt σ (tsHeapCp ((n : Nat) : Int) ((seed : Nat) : Int)
          ((target : Nat) : Int) n (tsFamily n seed) (tsPre m seed)
          ((n : Nat) : Int) ((m : Nat) : Int) false) 14)
        (.retV (.bool (decide (((m : Nat) : Int) < ((n : Nat) : Int))))
          cpCmpKT) ch
        = .ok (tOutHeadCfg,
            tSt σ (tsHeapOut ((n : Nat) : Int) ((seed : Nat) : Int)
              ((target : Nat) : Int) n (tsFamily n seed) (tsPre n seed)
              ((n : Nat) : Int) ((n : Nat) : Int) ((target : Nat) : Int)
              ((n : Nat) : Int) 0 true) 23, ch) := by
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
          (cp_iterT σ n seed target ((n : Nat) : Int) m hn hcap hlt ch)
          hrun⟩
    · have hmn : m = n := by omega
      subst hmn
      rw [show (decide (((m : Nat) : Int) < ((m : Nat) : Int))) = false from
        decide_eq_false (by omega)]
      have hX := cp_X_rawT σ ((m : Nat) : Int) ((seed : Nat) : Int)
        ((target : Nat) : Int) m (tsFamily m seed) (tsPre m seed)
        ((m : Nat) : Int) ((m : Nat) : Int) ch
      have hent := stepFnIter_one (ch := ch)
        (stepFn_call_enter (plans := tShapes) (env := callEnvT)
          (k := tAfterCall) (vals := [tsSliceS m])
          (v := .int ((target : Nat) : Int) .uint64)
          (henter (tsFamily m seed) (tsPre m seed) ((m : Nat) : Int)
            ((m : Nat) : Int)))
      rw [unorm_of_range (v := ((target : Nat) : Int)) (by omega)
        (by exact_mod_cast htgt)] at hent
      have hA := t_preA_rawT σ ((m : Nat) : Int) ((seed : Nat) : Int)
        ((target : Nat) : Int) m (tsFamily m seed) (tsPre m seed)
        ((m : Nat) : Int) ((m : Nat) : Int) ((target : Nat) : Int) ch
      have hlenap : applyStrictOp
          (tSt σ (tsHeapPro ((m : Nat) : Int) ((seed : Nat) : Int)
            ((target : Nat) : Int) m (tsFamily m seed) (tsPre m seed)
            ((m : Nat) : Int) ((m : Nat) : Int) ((target : Nat) : Int)) 21)
          (.lengthOf (some (.slice tU64))) [tsSliceS m]
          = .ok (.int ((m : Nat) : Int) .int,
              tSt σ (tsHeapPro ((m : Nat) : Int) ((seed : Nat) : Int)
                ((target : Nat) : Int) m (tsFamily m seed) (tsPre m seed)
                ((m : Nat) : Int) ((m : Nat) : Int)
                ((target : Nat) : Int)) 21) :=
        applyStrictOp_len_slice (Nat.le_refl _)
      have hlen := stepFnIter_one (ch := ch)
        (stepFn_strict_apply (done := []) (env := envNT) (k := tConvK)
          hlenap)
      have hB := t_preB_rawT σ ((m : Nat) : Int) ((seed : Nat) : Int)
        ((target : Nat) : Int) m (tsFamily m seed) (tsPre m seed)
        ((m : Nat) : Int) ((m : Nat) : Int) ((target : Nat) : Int)
        ((m : Nat) : Int) ch
      rw [unorm_of_range (v := ((m : Nat) : Int)) (by omega) (by omega),
        unorm_of_range (v := ((m : Nat) : Int)) (by omega) (by omega)] at hB
      exact ⟨17 + 1 + 12 + 1 + 34, by omega,
        stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain hX hent) hA) hlen) hB⟩

end GoLean.Examples.TwoSum
