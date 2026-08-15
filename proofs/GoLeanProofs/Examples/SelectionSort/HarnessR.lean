import GoLeanProofs.Examples.SelectionSort.Machine

/-!
# SelectionSort — HarnessR (phase A: entry, setup, copy, the call)

The harness run up to the SUBJECT's outer loop head: entry and
makeSlice, the LCG setup loop (`x = x*A + B; s[i] = x`), the first
copy loop (`pre[i] = s[i]`), the call boundary (the one
program-consulting `enterFrame` step) and the subject prologue.

Per-segment step counts (probe-measured with `.tmp/Probe.lean` at
`(n, seed) = (3, 7)`, re-checked by `rfl` here):

| phase | steps |
|---|---|
| entry → makeSlice apply | 10 |
| makeSlice apply → setup head | 1 + 55 |
| setup dispatch (first / later) | 25 / 29 |
| one setup iteration | 68 |
| setup exit → copy head | 39 |
| copy dispatch (first / later) | 25 / 29 |
| one copy iteration | 53 |
| copy exit → call args delivered | 9 |
| `enterFrame` (the one program step) | 1 |
| subject prologue → the outer head | 30 |

Phase A is branch-free, so `sA_runs` is EXACT: `121·n + 195` steps.
-/

namespace GoLean.Examples.SelectionSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem
open GoLean.Examples.SortShared

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## The setup family's copy-prefix -/

/-- The `pre` array after `m` copy steps: the family prefix, zero tail
(the fixed-cap `[8]uint64`). -/
def selPre (m seed : Nat) : List Int :=
  lcgFamily lcgA lcgB m seed ++ List.replicate (8 - m) 0

theorem selPre_zero (seed : Nat) : selPre 0 seed = zeros8 := rfl

theorem selPre_length {m seed : Nat} (h : m ≤ 8) :
    (selPre m seed).length = 8 := by
  rw [selPre, List.length_append, lcgFamily_length, List.length_replicate]
  omega

theorem selPre_range {m seed : Nat} :
    ∀ v ∈ selPre m seed, 0 ≤ v ∧ v < 2 ^ 64 :=
  lcgFamilyZ_range

theorem selPre_full {n seed : Nat} :
    selPre n seed = selPad8 (selFam n seed) := by
  rw [selPre, selPad8, lcgFamily_length]

/-! ## Entry -/

/-- Entry A: body start → the `$c4` makeSlice length delivery.
10 steps. -/
theorem sE1_raw (nv sv : Int) (ch : Choices) :
    stepFnIter 10 (σS (hp0 nv sv) 4) sHC₀ ch
      = .ok (.retV (.int nv .uint64)
          (.stmtOpK (.makeSlice tU64 false) 1 [.addr (.base ⟨4⟩)] [] envC4
            (.seq [sS2, sS3, sS4, sS5, sS6, sS7, sS8, sS9, sS10] envC4
              sFrame0)),
        σS (hpC4 nv sv) 5, ch) := by
  with_unfolding_all rfl

/-- `make([]uint64, n)` at SYMBOLIC `n`. -/
theorem s_make_apply (nv sv : Int) (n : Nat) (ch : Choices) :
    applyStmtOp (σS (hpC4 nv sv) 5) ch (.makeSlice tU64 false) 1
      [.addr (.base ⟨4⟩), .int (n : Nat) .uint64]
      = .ok (σS (hpMk nv sv n) 6, ch) := by
  have hnn1 := natFromNonneg_cast
    "runtime error: makeslice: len out of range" n
  have hnn2 := natFromNonneg_cast
    "runtime error: makeslice: cap out of range" n
  have hb := GoLean.Iris.buildDefaultArrayValue_int
    (σS (hpC4 nv sv) 5) .uint64 n
  have harr : (List.replicate n (GoValue.int 0 .uint64)).toArray
      = (⟨(List.replicate n (0 : Int)).map
          (fun v => GoValue.int v .uint64)⟩ : Array GoValue) := by
    simp [List.map_replicate]
  rw [harr] at hb
  simp only [applyStmtOp, applyStmtOpCore, valueAsInt, valueAsLoc,
    hnn1, hnn2, hb, Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (Nat.lt_irrefl n)]
  with_unfolding_all rfl

/-- Entry B: `s := $c4`, `x := seed`, the setup counter and flag →
the setup loop head. 55 steps. The `x` cell lands NORMALIZED (the
scalar-store normal form); the caller rewrites it away at in-range
`seed`. -/
theorem sE2_raw (nv sv : Int) (n : Nat) (ch : Choices) :
    stepFnIter 55 (σS (hpMk nv sv n) 6)
      (.next (.seq [sS2, sS3, sS4, sS5, sS6, sS7, sS8, sS9, sS10] envC4
        sFrame0)) ch
      = .ok (suHeadCfg,
          σS (hpSu nv sv n (List.replicate n 0)
            (IntKind.normalize .uint64 sv) 0 true) 10, ch) := by
  with_unfolding_all rfl

/-! ## The setup loop -/

theorem su_A0_raw (nv sv : Int) (n : Nat) (l : List Int) (xv iv : Int)
    (ch : Choices) :
    stepFnIter 25 (σS (hpSu nv sv n l xv iv true) 10) suHeadCfg ch
      = .ok (.retV (.bool (decide (iv < nv))) suCmpK,
          σS (hpSu nv sv n l xv iv false) 10, ch) := by
  with_unfolding_all rfl

theorem su_A1_raw (nv sv : Int) (n : Nat) (l : List Int) (xv iv : Int)
    (ch : Choices) :
    stepFnIter 29 (σS (hpSu nv sv n l xv iv false) 10) suHeadCfg ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < nv))) suCmpK,
          σS (hpSu nv sv n l xv
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false) 10, ch) := by
  with_unfolding_all rfl

/-- Setup body: test true → `x = x*A + B` (definitional arithmetic,
the register store) → the `s[i] = x` element-store point. 33 steps. -/
theorem su_B1_raw (nv sv : Int) (n : Nat) (l : List Int) (xv iv : Int)
    (ch : Choices) :
    stepFnIter 33 (σS (hpSu nv sv n l xv iv false) 10)
      (.retV (.bool true) suCmpK) ch
      = .ok (.next (.storeK [suRef n iv]
            [.int (IntKind.normalize .uint64
              (IntKind.normalize .uint64
                (IntKind.normalize .uint64 (xv * 6364136223846793005)
                  + 1442695040888963407))) .uint64]
            (.seqn #[]) suEnv2 suStTail),
          σS (hpSu nv sv n l
            (IntKind.normalize .uint64
              (IntKind.normalize .uint64
                (IntKind.normalize .uint64 (xv * 6364136223846793005)
                  + 1442695040888963407))) iv false) 10, ch) := by
  with_unfolding_all rfl

theorem su_D_raw (nv sv : Int) (n : Nat) (l : List Int) (xv iv : Int)
    (ch : Choices) :
    stepFnIter 5 (σS (hpSu nv sv n l xv iv false) 10)
      (.next (.storeK [] [] (.seqn #[]) suEnv2 suStTail)) ch
      = .ok (suHeadCfg, σS (hpSu nv sv n l xv iv false) 10, ch) := by
  with_unfolding_all rfl

/-- Setup exit: test false → `var pre` declared and the copy loop
head. 39 steps. -/
theorem su_X_raw (nv sv : Int) (n : Nat) (l : List Int) (xv iv : Int)
    (ch : Choices) :
    stepFnIter 39 (σS (hpSu nv sv n l xv iv false) 10)
      (.retV (.bool false) suCmpK) ch
      = .ok (cpHeadCfg,
          σS (hpCp nv sv n l xv iv zeros8 0 true) 13, ch) := by
  with_unfolding_all rfl

/-- The wrapped-LCG value chain: the machine's triple-normalized store
value IS the next `lcgStep` iterate. -/
theorem lcg_norm_chain (j seed : Nat) :
    IntKind.normalize .uint64
      (IntKind.normalize .uint64
        (IntKind.normalize .uint64
          (((lcgStep lcgA lcgB j seed : Nat) : Int) * 6364136223846793005)
            + 1442695040888963407))
      = ((lcgStep lcgA lcgB (j + 1) seed : Nat) : Int) := by
  have hc : ((lcgStep lcgA lcgB j seed : Nat) : Int) * 6364136223846793005
      = ((lcgStep lcgA lcgB j seed * lcgA : Nat) : Int) := by
    rw [Int.natCast_mul]
    rfl
  rw [hc, unorm_nat_mod,
    show (1442695040888963407 : Int) = ((lcgB : Nat) : Int) from rfl,
    unorm_add_nat, unorm_nat_mod]
  have hnat : ((lcgStep lcgA lcgB j seed * lcgA % 2 ^ 64 + lcgB) % 2 ^ 64)
      % 2 ^ 64 = lcgStep lcgA lcgB (j + 1) seed := by
    show _ = (lcgStep lcgA lcgB j seed * lcgA + lcgB) % 2 ^ 64
    omega
  rw [hnat]

/-- One setup iteration from the exit test's true delivery at `i`:
68 steps materialize the next LCG iterate into `x` and `s[i]`. -/
theorem su_iter (n seed i : Nat) (hn : n < 2 ^ 63) (hi : i < n)
    (ch : Choices) :
    stepFnIter 68
      (σS (hpSu ((n : Nat) : Int) ((seed : Nat) : Int) n
        (selFam i seed ++ List.replicate (n - i) 0)
        ((lcgStep lcgA lcgB i seed : Nat) : Int)
        ((i : Nat) : Int) false) 10)
      (.retV (.bool true) suCmpK) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) suCmpK,
          σS (hpSu ((n : Nat) : Int) ((seed : Nat) : Int) n
            (selFam (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
            ((lcgStep lcgA lcgB (i + 1) seed : Nat) : Int)
            ((i + 1 : Nat) : Int) false) 10, ch) := by
  have hB1 := su_B1_raw ((n : Nat) : Int) ((seed : Nat) : Int) n
    (selFam i seed ++ List.replicate (n - i) 0)
    ((lcgStep lcgA lcgB i seed : Nat) : Int) ((i : Nat) : Int) ch
  rw [lcg_norm_chain i seed] at hB1
  have hw : (0 : Int) ≤ ((lcgStep lcgA lcgB (i + 1) seed : Nat) : Int)
      ∧ ((lcgStep lcgA lcgB (i + 1) seed : Nat) : Int) < 2 ^ 64 := by
    constructor
    · omega
    · exact_mod_cast lcgStep_lt (by omega)
  have hst := storeTarget_slice_u64
    (σ := σS (hpSu ((n : Nat) : Int) ((seed : Nat) : Int) n
      (selFam i seed ++ List.replicate (n - i) 0)
      ((lcgStep lcgA lcgB (i + 1) seed : Nat) : Int)
      ((i : Nat) : Int) false) 10)
    (a := ⟨5⟩) (off := 0) (len := n) (cap := n) (i := i) (n := n)
    (ik := .uint64) (l := selFam i seed ++ List.replicate (n - i) 0)
    (w := ((lcgStep lcgA lcgB (i + 1) seed : Nat) : Int))
    (lookup_su5 ((n : Nat) : Int) ((seed : Nat) : Int) n
      (selFam i seed ++ List.replicate (n - i) 0)
      ((lcgStep lcgA lcgB (i + 1) seed : Nat) : Int) ((i : Nat) : Int)
      false 10)
    (Nat.le_refl n) hi
    (by rw [List.length_append, lcgFamily_length, List.length_replicate]
        omega)
    (by rw [List.length_append, lcgFamily_length, List.length_replicate]
        omega)
    lcgFamilyZ_range hw
  rw [Nat.zero_add, lcgFamily_set hi] at hst
  have h2 := stepFnIter_chain hB1
    (stepFnIter_one (stepFn_store_step hst))
  have hD := su_D_raw ((n : Nat) : Int) ((seed : Nat) : Int) n
    (selFam (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
    ((lcgStep lcgA lcgB (i + 1) seed : Nat) : Int) ((i : Nat) : Int) ch
  have h3 := stepFnIter_chain h2 hD
  have hA1 := su_A1_raw ((n : Nat) : Int) ((seed : Nat) : Int) n
    (selFam (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
    ((lcgStep lcgA lcgB (i + 1) seed : Nat) : Int) ((i : Nat) : Int) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega)]
    at hA1
  exact stepFnIter_chain h3 hA1

/-- **The setup loop** (the P5 iteration schema): `68·(n−i)` steps
materialize the wrapped LCG family. -/
theorem su_loop (n seed : Nat) (hn : n < 2 ^ 63) :
    ∀ i, i ≤ n → ∀ ch : Choices,
    stepFnIter (68 * (n - i))
      (σS (hpSu ((n : Nat) : Int) ((seed : Nat) : Int) n
        (selFam i seed ++ List.replicate (n - i) 0)
        ((lcgStep lcgA lcgB i seed : Nat) : Int)
        ((i : Nat) : Int) false) 10)
      (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
        suCmpK) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) suCmpK,
          σS (hpSu ((n : Nat) : Int) ((seed : Nat) : Int) n
            (selFam n seed)
            ((lcgStep lcgA lcgB n seed : Nat) : Int)
            ((n : Nat) : Int) false) 10, ch) := by
  intro i hin ch
  have hgen := stepFnIter_iterate (c := 68) (n := n)
    (T := fun j => σS (hpSu ((n : Nat) : Int) ((seed : Nat) : Int) n
      (selFam j seed ++ List.replicate (n - j) 0)
      ((lcgStep lcgA lcgB j seed : Nat) : Int)
      ((j : Nat) : Int) false) 10)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int)
      < ((n : Nat) : Int)))) suCmpK)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact su_iter n seed j hn hj ch')
    i hin ch
  have hfam : selFam n seed ++ List.replicate (n - n) 0 = selFam n seed := by
    simp
  rw [hfam] at hgen
  exact hgen

/-! ## The copy loop -/

theorem cp_A0_raw (nv sv : Int) (n : Nat) (l : List Int) (xv siv : Int)
    (lp : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 25 (σS (hpCp nv sv n l xv siv lp civ true) 13) cpHeadCfg ch
      = .ok (.retV (.bool (decide (civ < nv))) cpCmpK,
          σS (hpCp nv sv n l xv siv lp civ false) 13, ch) := by
  with_unfolding_all rfl

theorem cp_A1_raw (nv sv : Int) (n : Nat) (l : List Int) (xv siv : Int)
    (lp : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 29 (σS (hpCp nv sv n l xv siv lp civ false) 13) cpHeadCfg
      ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1))
              < nv))) cpCmpK,
          σS (hpCp nv sv n l xv siv lp
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1)))
            false) 13, ch) := by
  with_unfolding_all rfl

/-- Copy phase 1: test true → the `pre[i]` target banked, the `s[i]`
read at its apply point. 16 steps. -/
theorem cp_B1_raw (nv sv : Int) (n : Nat) (l : List Int) (xv siv : Int)
    (lp : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 16 (σS (hpCp nv sv n l xv siv lp civ false) 13)
      (.retV (.bool true) cpCmpK) ch
      = .ok (.retV (.int civ .uint64)
            (.strictK .indexGet [sHandle n] [] cpEnv2 (cpRhsK civ)),
          σS (hpCp nv sv n l xv siv lp civ false) 13, ch) := by
  with_unfolding_all rfl

theorem cp_B2_raw (nv sv : Int) (n : Nat) (l : List Int) (xv siv : Int)
    (lp : List Int) (civ : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1 (σS (hpCp nv sv n l xv siv lp civ false) 13)
      (.retV w (cpRhsK civ)) ch
      = .ok (.next (.storeK [cpRef civ] [w] (.seqn #[]) cpEnv2 cpStTail),
          σS (hpCp nv sv n l xv siv lp civ false) 13, ch) := by
  with_unfolding_all rfl

theorem cp_D_raw (nv sv : Int) (n : Nat) (l : List Int) (xv siv : Int)
    (lp : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 5 (σS (hpCp nv sv n l xv siv lp civ false) 13)
      (.next (.storeK [] [] (.seqn #[]) cpEnv2 cpStTail)) ch
      = .ok (cpHeadCfg, σS (hpCp nv sv n l xv siv lp civ false) 13,
          ch) := by
  with_unfolding_all rfl

/-- Copy exit: test false → the `selectionSort(s)` argument delivered
at the drained `callArgsK`. 9 steps. -/
theorem cp_X_raw (nv sv : Int) (n : Nat) (l : List Int) (xv siv : Int)
    (lp : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 9 (σS (hpCp nv sv n l xv siv lp civ false) 13)
      (.retV (.bool false) cpCmpK) ch
      = .ok (.retV (sHandle n) sCallArgsK,
          σS (hpCp nv sv n l xv siv lp civ false) 13, ch) := by
  with_unfolding_all rfl

/-- One copy iteration: 53 steps from the exit test's true delivery at
`m`. -/
theorem cp_iter (n seed : Nat) (m : Nat)
    (hn : n < 2 ^ 63) (hcap : n ≤ 8) (hm : m < n) (ch : Choices) :
    stepFnIter 53
      (σS (hpCp ((n : Nat) : Int) ((seed : Nat) : Int) n
        (selFam n seed) ((lcgStep lcgA lcgB n seed : Nat) : Int)
        ((n : Nat) : Int) (selPre m seed) ((m : Nat) : Int) false) 13)
      (.retV (.bool true) cpCmpK) ch
      = .ok (.retV (.bool (decide
            (((m + 1 : Nat) : Int) < ((n : Nat) : Int)))) cpCmpK,
          σS (hpCp ((n : Nat) : Int) ((seed : Nat) : Int) n
            (selFam n seed) ((lcgStep lcgA lcgB n seed : Nat) : Int)
            ((n : Nat) : Int) (selPre (m + 1) seed)
            ((m + 1 : Nat) : Int) false) 13, ch) := by
  have hB1 := cp_B1_raw ((n : Nat) : Int) ((seed : Nat) : Int) n
    (selFam n seed) ((lcgStep lcgA lcgB n seed : Nat) : Int)
    ((n : Nat) : Int) (selPre m seed) ((m : Nat) : Int) ch
  have hget : (⟨(selFam n seed).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + m]?
      = some (.int ((lcgStep lcgA lcgB (m + 1) seed : Nat) : Int)
          .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by rw [lcgFamily_length]; omega),
      lcgFamily_getD hm]
  have hread := stepFn_strict_apply (done := [sHandle n]) (env := cpEnv2)
    (k := cpRhsK ((m : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .uint64)
      (lookup_cp5 ((n : Nat) : Int) ((seed : Nat) : Int) n
        (selFam n seed) ((lcgStep lcgA lcgB n seed : Nat) : Int)
        ((n : Nat) : Int) (selPre m seed) ((m : Nat) : Int) false 13)
      (Nat.le_refl n) hm hget)
  have hB2 := cp_B2_raw ((n : Nat) : Int) ((seed : Nat) : Int) n
    (selFam n seed) ((lcgStep lcgA lcgB n seed : Nat) : Int)
    ((n : Nat) : Int) (selPre m seed) ((m : Nat) : Int)
    (.int ((lcgStep lcgA lcgB (m + 1) seed : Nat) : Int) .uint64) ch
  have hw : (0 : Int) ≤ ((lcgStep lcgA lcgB (m + 1) seed : Nat) : Int)
      ∧ ((lcgStep lcgA lcgB (m + 1) seed : Nat) : Int) < 2 ^ 64 := by
    constructor
    · omega
    · exact_mod_cast lcgStep_lt (by omega)
  have hst := storeTarget_arrayLocal_u64 (a := ⟨10⟩) (N := 8) (i := m)
    (ik := .uint64) (l := selPre m seed)
    (w := ((lcgStep lcgA lcgB (m + 1) seed : Nat) : Int))
    (lookup_cp10 ((n : Nat) : Int) ((seed : Nat) : Int) n
      (selFam n seed) ((lcgStep lcgA lcgB n seed : Nat) : Int)
      ((n : Nat) : Int) (selPre m seed) ((m : Nat) : Int) false 13)
    (by rw [selPre_length (by omega)]; omega)
    (selPre_length (by omega)) selPre_range hw
  rw [show (selPre m seed).set m
        ((lcgStep lcgA lcgB (m + 1) seed : Nat) : Int)
      = selPre (m + 1) seed from lcgFamily_set (by omega)] at hst
  have hD := cp_D_raw ((n : Nat) : Int) ((seed : Nat) : Int) n
    (selFam n seed) ((lcgStep lcgA lcgB n seed : Nat) : Int)
    ((n : Nat) : Int) (selPre (m + 1) seed) ((m : Nat) : Int) ch
  have hA1 := cp_A1_raw ((n : Nat) : Int) ((seed : Nat) : Int) n
    (selFam n seed) ((lcgStep lcgA lcgB n seed : Nat) : Int)
    ((n : Nat) : Int) (selPre (m + 1) seed) ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)]
    at hA1
  have h1 := stepFnIter_chain hB1 (stepFnIter_one hread)
  have h2 := stepFnIter_chain h1 hB2
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hst))
  exact stepFnIter_chain (stepFnIter_chain h3 hD) hA1

/-- **The copy loop** (P5 schema): `53·(n−m)` steps copy the family
into `pre`. -/
theorem cp_loop (n seed : Nat) (hn : n < 2 ^ 63) (hcap : n ≤ 8) :
    ∀ m, m ≤ n → ∀ ch : Choices,
    stepFnIter (53 * (n - m))
      (σS (hpCp ((n : Nat) : Int) ((seed : Nat) : Int) n
        (selFam n seed) ((lcgStep lcgA lcgB n seed : Nat) : Int)
        ((n : Nat) : Int) (selPre m seed) ((m : Nat) : Int) false) 13)
      (.retV (.bool (decide (((m : Nat) : Int) < ((n : Nat) : Int))))
        cpCmpK) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) cpCmpK,
          σS (hpCp ((n : Nat) : Int) ((seed : Nat) : Int) n
            (selFam n seed) ((lcgStep lcgA lcgB n seed : Nat) : Int)
            ((n : Nat) : Int) (selPre n seed) ((n : Nat) : Int) false)
            13, ch) := by
  intro m hmn ch
  have hgen := stepFnIter_iterate (c := 53) (n := n)
    (T := fun j => σS (hpCp ((n : Nat) : Int) ((seed : Nat) : Int) n
      (selFam n seed) ((lcgStep lcgA lcgB n seed : Nat) : Int)
      ((n : Nat) : Int) (selPre j seed) ((j : Nat) : Int) false) 13)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int)
      < ((n : Nat) : Int)))) cpCmpK)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact cp_iter n seed j hn hcap hj ch')
    m hmn ch
  exact hgen

/-! ## The call boundary and the subject prologue -/

/-- The `enterFrame` discharge at the pinned program — the one
program-consulting step of the whole run. -/
theorem s_enterFrame_fact (nv sv : Int) (n : Nat) (l : List Int)
    (xv siv : Int) (lp : List Int) (civ : Int) :
    enterFrame (σS (hpCp nv sv n l xv siv lp civ false) 13)
        ⟨"selectionSort"⟩ [sHandle n]
      = .ok (selectionSortFunc, sFrameEnv, [],
          σS (hpCp nv sv n l xv siv lp civ false
            ++ [(.base ⟨13⟩, sHandleCell n)]) 14) := by
  with_unfolding_all rfl

/-- The subject prologue: frame entry → `i := 0` (cell 14), the outer
`$forFirst` (cell 15) → the outer loop head. 30 steps. -/
theorem s_prologue_raw (nv sv : Int) (n : Nat) (l : List Int)
    (xv siv : Int) (lp : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 30
      (σS (hpCp nv sv n l xv siv lp civ false
        ++ [(.base ⟨13⟩, sHandleCell n)]) 14)
      (.exec selectionSortFunc.body sFrameEnv sSubjFrameK) ch
      = .ok (outerHeadCfg,
          σS (hpCp nv sv n l xv siv lp civ false
            ++ [(.base ⟨13⟩, sHandleCell n), (.base ⟨14⟩, sint 0),
                (.base ⟨15⟩, sbool true)]) 16, ch) := by
  with_unfolding_all rfl

/-- The phase-A/phase-B state bridge: the accumulated phase-A front at
the parked values IS the subject phase's 16-cell front. -/
theorem hpBridge (n seed : Nat) :
    σS (hpCp ((n : Nat) : Int) ((seed : Nat) : Int) n (selFam n seed)
        ((lcgStep lcgA lcgB n seed : Nat) : Int) ((n : Nat) : Int)
        (selPre n seed) ((n : Nat) : Int) false
      ++ [(.base ⟨13⟩, sHandleCell n), (.base ⟨14⟩, sint 0),
          (.base ⟨15⟩, sbool true)]) 16
      = σOut n seed (selFam n seed) 0 true := by
  rw [σOut, σOutT, hpSubj, hpCp, hpSu, hp0, selPre_full]
  rfl

/-- **Phase A, end to end** (EXACT, branch-free): `121·n + 195` steps
from the entry to the subject's outer loop head, with the family in
the backing, its padded copy in `pre`, and the subject's `i` at 0. -/
theorem sA_runs (n seed : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64)
    (ch : Choices) :
    stepFnIter (121 * n + 195)
      (σS (hp0 ((n : Nat) : Int) ((seed : Nat) : Int)) 4) sHC₀ ch
      = .ok (outerHeadCfg, σOut n seed (selFam n seed) 0 true, ch) := by
  have hn : n < 2 ^ 63 := by omega
  have hE1 := sE1_raw ((n : Nat) : Int) ((seed : Nat) : Int) ch
  have hmk := stepFnIter_one
    (stepFn_makeSlice_u64_step (env := envC4)
      (k := .seq [sS2, sS3, sS4, sS5, sS6, sS7, sS8, sS9, sS10] envC4
        sFrame0)
      (s_make_apply ((n : Nat) : Int) ((seed : Nat) : Int) n ch))
  have hE2 := sE2_raw ((n : Nat) : Int) ((seed : Nat) : Int) n ch
  rw [unorm_of_range (v := ((seed : Nat) : Int)) (by omega)
    (by exact_mod_cast hseed)] at hE2
  have hA0 := su_A0_raw ((n : Nat) : Int) ((seed : Nat) : Int) n
    (List.replicate n 0) ((seed : Nat) : Int) 0 ch
  have hsu := su_loop n seed hn 0 (by omega) ch
  rw [show selFam 0 seed ++ List.replicate (n - 0) 0
      = List.replicate n 0 from by simp [selFam, lcgFamily],
    show ((lcgStep lcgA lcgB 0 seed : Nat) : Int) = ((seed : Nat) : Int)
      from rfl,
    show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hsu
  have h1 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hE1 hmk) hE2) hA0) hsu
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at h1
  have hX := su_X_raw ((n : Nat) : Int) ((seed : Nat) : Int) n
    (selFam n seed) ((lcgStep lcgA lcgB n seed : Nat) : Int)
    ((n : Nat) : Int) ch
  have h2 := stepFnIter_chain h1 hX
  have hcA0 := cp_A0_raw ((n : Nat) : Int) ((seed : Nat) : Int) n
    (selFam n seed) ((lcgStep lcgA lcgB n seed : Nat) : Int)
    ((n : Nat) : Int) zeros8 0 ch
  have hcp := cp_loop n seed hn hcap 0 (by omega) ch
  rw [show selPre 0 seed = zeros8 from rfl,
    show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hcp
  have h3 := stepFnIter_chain (stepFnIter_chain h2 hcA0) hcp
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at h3
  have hcX := cp_X_raw ((n : Nat) : Int) ((seed : Nat) : Int) n
    (selFam n seed) ((lcgStep lcgA lcgB n seed : Nat) : Int)
    ((n : Nat) : Int) (selPre n seed) ((n : Nat) : Int) ch
  have h4 := stepFnIter_chain h3 hcX
  have hent := stepFnIter_one (ch := ch)
    (stepFn_call_enter (plans := []) (env := callEnv)
      (k := sAfterCallK) (vals := []) (v := sHandle n)
      (s_enterFrame_fact ((n : Nat) : Int) ((seed : Nat) : Int) n
        (selFam n seed) ((lcgStep lcgA lcgB n seed : Nat) : Int)
        ((n : Nat) : Int) (selPre n seed) ((n : Nat) : Int)))
  have h5 := stepFnIter_chain h4 hent
  have hpro := s_prologue_raw ((n : Nat) : Int) ((seed : Nat) : Int) n
    (selFam n seed) ((lcgStep lcgA lcgB n seed : Nat) : Int)
    ((n : Nat) : Int) (selPre n seed) ((n : Nat) : Int) ch
  rw [hpBridge n seed] at hpro
  have h6 := stepFnIter_chain h5 hpro
  have harith : 10 + 1 + 55 + 25 + 68 * (n - 0) + 39 + 25
      + 53 * (n - 0) + 9 + 1 + 30 = 121 * n + 195 := by omega
  rw [harith] at h6
  exact h6

end GoLean.Examples.SelectionSort
