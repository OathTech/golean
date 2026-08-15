import GoLeanProofs.Examples.ArrayPalindrome.Machine

/-!
# ArrayPalindrome — the harness run (entry, setup, copy, subject, exit)

The `palin_harness_r` run, PROGRAM-generic throughout: every raw
segment is proven over an abstract `σ` (only `heap`/`nextAddr` pinned),
and the ONE step that consults the program — the `isPalindrome(s)`
frame entry — is conditioned through `StepKit.stepFn_call_enter`.

## The shape of the subject loop, and why it needs one theorem not two

`isPalindrome` has an EARLY RETURN: the first mismatched pair leaves
the function immediately with verdict `0`. So the loop induction below
does not stop at "the loop head after `μ` iterations" — it runs all the
way to the DRIVER TERMINAL, and both ways out (the middle is reached,
or a pair mismatches) land on the same `.next .stop` with the verdict
`palinSpec l` in `$res1`. The final `i`/`j` cells differ between the
two exits, so they are existentially quantified: the harness returns
`$res0`/`$res1` and nothing reads them.

Per-segment step counts (probe-measured with the lane's generic tracer
`.tmp/Probe.lean`, then re-checked by `rfl` here):

| phase | steps |
|---|---|
| entry → makeSlice apply | 10 |
| makeSlice apply → setup head | 42 |
| setup dispatch (first / later) | 25 / 29 |
| one setup iteration | 57 |
| setup exit → copy head | 39 |
| copy dispatch (first / later) | 25 / 29 |
| one copy iteration | 53 |
| copy exit → call args delivered | 13 |
| `enterFrame` (the one program step) | 1 |
| subject prologue (split by `len(s)`) | 25 + 1 + 21 |
| subject dispatch (first / later) | 25 / 18 |
| one full subject iteration | 68 |
| subject exit → the `$res0` store | 33 |
| subject mismatch → the `$res0` store | 35 |
| the `$res0 = pre` store + tail | 1 + 15 |
-/

namespace GoLean.Examples.ArrayPalindrome

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## The setup family and the copy loop's array invariant

Both are the kit's, at modulus 2 — the `familyMod`/`prefixPad` lift
(GAP-P2) covers this example with no re-derivation at all. -/

/-- The alternating setup family `s[i] = seed + i%2`, wrapped. -/
abbrev palFamily (n seed : Nat) : List Int := familyMod 2 n seed

/-- The `pre` array after `m` copy steps. -/
abbrev palPre (m seed : Nat) : List Int := prefixPad (familyMod 2) 8 m seed

theorem palPre_zero (seed : Nat) : palPre 0 seed = zeros8 :=
  prefixPad_zero rfl

theorem palPre_length {m seed : Nat} (h : m ≤ 8) :
    (palPre m seed).length = 8 :=
  prefixPad_length (familyMod_length 2 m seed) h

theorem palPre_range {m seed : Nat} :
    ∀ v ∈ palPre m seed, 0 ≤ v ∧ v < 2 ^ 64 :=
  prefixPad_range (familyMod_range 2 m seed)

theorem palPre_full {n seed : Nat} :
    palPre n seed
      = palFamily n seed
          ++ List.replicate (8 - (palFamily n seed).length) 0 :=
  prefixPad_full (familyMod_length 2 n seed)

/-! ## Raw run segments — PROGRAM-generic throughout -/

/-- Entry A: body start → the `$c8` makeSlice apply point. 10 steps. -/
theorem p_E1_raw (σ : ExecState) (nv sv : Int) (ch : Choices) :
    stepFnIter 10 (pSt σ (pHeap0 nv sv) 4) pHC0 ch
      = .ok (.retV (.int nv .uint64)
          (.stmtOpK (.makeSlice tU64 false) 1
            [.addr (.base ⟨4⟩)] [] envC8P
            (.seq [pS2, pS3, pS4, pS5, pS6, pS7] envC8P
              (.frame [] [] [] [] .stop))),
        pSt σ (pHeapC8 nv sv) 5, ch) := by
  with_unfolding_all rfl

/-- **`make([]uint64, n)` at SYMBOLIC `n`.** -/
theorem p_make_apply (σ : ExecState) (nv sv : Int) (n : Nat)
    (ch : Choices) :
    applyStmtOp (pSt σ (pHeapC8 nv sv) 5) ch (.makeSlice tU64 false) 1
      [.addr (.base ⟨4⟩), .int (n : Nat) .uint64]
      = .ok (pSt σ (pHeapMake nv sv n) 6, ch) := by
  have hnn1 := natFromNonneg_cast
    "runtime error: makeslice: len out of range" n
  have hnn2 := natFromNonneg_cast
    "runtime error: makeslice: cap out of range" n
  have hb := GoLean.Iris.buildDefaultArrayValue_int
    (pSt σ (pHeapC8 nv sv) 5) .uint64 n
  have harr : (List.replicate n (GoValue.int 0 .uint64)).toArray
      = (⟨(List.replicate n (0 : Int)).map
          (fun v => GoValue.int v .uint64)⟩ : Array GoValue) := by
    simp [List.map_replicate]
  rw [harr] at hb
  simp only [applyStmtOp, applyStmtOpCore, valueAsInt, valueAsLoc,
    hnn1, hnn2, hb, Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (Nat.lt_irrefl n)]
  with_unfolding_all rfl

/-- Entry B: `s := $c8`, the setup counter and flag → the setup loop
head. 42 steps. -/
theorem p_E2_raw (σ : ExecState) (nv sv : Int) (n : Nat) (ch : Choices) :
    stepFnIter 42 (pSt σ (pHeapMake nv sv n) 6)
      (.next (.seq [pS2, pS3, pS4, pS5, pS6, pS7] envC8P
        (.frame [] [] [] [] .stop))) ch
      = .ok (suHeadCfgP,
          pSt σ (pHeapSu nv sv n (List.replicate n 0) 0 true) 9, ch) := by
  with_unfolding_all rfl

/-! ### The setup loop -/

theorem su_A0_rawP (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 25 (pSt σ (pHeapSu nv sv n l iv true) 9) suHeadCfgP ch
      = .ok (.retV (.bool (decide (iv < nv))) suCmpKP,
          pSt σ (pHeapSu nv sv n l iv false) 9, ch) := by
  with_unfolding_all rfl

theorem su_A1_rawP (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 29 (pSt σ (pHeapSu nv sv n l iv false) 9) suHeadCfgP ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < nv))) suCmpKP,
          pSt σ (pHeapSu nv sv n l
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false) 9, ch) := by
  with_unfolding_all rfl

/-- Setup fill phase A: test true → the `%` apply point. 19 steps. -/
theorem su_B1a_rawP (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 19 (pSt σ (pHeapSu nv sv n l iv false) 9)
      (.retV (.bool true) suCmpKP) ch
      = .ok (.retV (.int 2 .uint64) (suModKP n sv iv),
          pSt σ (pHeapSu nv sv n l iv false) 9, ch) := by
  with_unfolding_all rfl

/-- Setup fill phase B: the `%` result → the add → the element-store
point. 2 steps. -/
theorem su_B1b_rawP (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv rv : Int) (ch : Choices) :
    stepFnIter 2 (pSt σ (pHeapSu nv sv n l iv false) 9)
      (.retV (.int rv .uint64) (suAddKP n sv iv)) ch
      = .ok (.next (.storeK [suRefP n iv]
            [.int (IntKind.normalize .uint64 (sv + rv)) .uint64]
            (.seqn #[]) suEnvP2 suStTailP),
          pSt σ (pHeapSu nv sv n l iv false) 9, ch) := by
  with_unfolding_all rfl

theorem su_D_rawP (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 5 (pSt σ (pHeapSu nv sv n l iv false) 9)
      (.next (.storeK [] [] (.seqn #[]) suEnvP2 suStTailP)) ch
      = .ok (suHeadCfgP, pSt σ (pHeapSu nv sv n l iv false) 9, ch) := by
  with_unfolding_all rfl

/-- Setup exit: test false → `var pre` declared and the copy loop head.
39 steps. -/
theorem su_X_rawP (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 39 (pSt σ (pHeapSu nv sv n l iv false) 9)
      (.retV (.bool false) suCmpKP) ch
      = .ok (cpHeadCfgP,
          pSt σ (pHeapCp nv sv n l zeros8 iv 0 true) 12, ch) := by
  with_unfolding_all rfl

/-! ### The copy loop -/

theorem cp_A0_rawP (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 25 (pSt σ (pHeapCp nv sv n l lp siv civ true) 12) cpHeadCfgP ch
      = .ok (.retV (.bool (decide (civ < nv))) cpCmpKP,
          pSt σ (pHeapCp nv sv n l lp siv civ false) 12, ch) := by
  with_unfolding_all rfl

theorem cp_A1_rawP (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 29 (pSt σ (pHeapCp nv sv n l lp siv civ false) 12) cpHeadCfgP
      ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1))
              < nv))) cpCmpKP,
          pSt σ (pHeapCp nv sv n l lp siv
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1)))
            false) 12, ch) := by
  with_unfolding_all rfl

/-- Copy phase 1: test true → the `pre[i]` target banked, the `s[i]`
read at its apply point. 16 steps. -/
theorem cp_B1_rawP (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 16 (pSt σ (pHeapCp nv sv n l lp siv civ false) 12)
      (.retV (.bool true) cpCmpKP) ch
      = .ok (.retV (.int civ .uint64)
            (.strictK .indexGet [pSliceS n] [] cpEnvP2 (cpRhsKP civ)),
          pSt σ (pHeapCp nv sv n l lp siv civ false) 12, ch) := by
  with_unfolding_all rfl

theorem cp_B2_rawP (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1 (pSt σ (pHeapCp nv sv n l lp siv civ false) 12)
      (.retV w (cpRhsKP civ)) ch
      = .ok (.next (.storeK [cpRefP civ] [w] (.seqn #[]) cpEnvP2 cpStTailP),
          pSt σ (pHeapCp nv sv n l lp siv civ false) 12, ch) := by
  with_unfolding_all rfl

theorem cp_D_rawP (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 5 (pSt σ (pHeapCp nv sv n l lp siv civ false) 12)
      (.next (.storeK [] [] (.seqn #[]) cpEnvP2 cpStTailP)) ch
      = .ok (cpHeadCfgP, pSt σ (pHeapCp nv sv n l lp siv civ false) 12,
          ch) := by
  with_unfolding_all rfl

/-- Copy exit: test false → `v` declared and the `isPalindrome(s)`
argument delivered at the drained `callArgsK`. 13 steps. -/
theorem cp_X_rawP (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 13 (pSt σ (pHeapCp nv sv n l lp siv civ false) 12)
      (.retV (.bool false) cpCmpKP) ch
      = .ok (.retV (pSliceS n) pCallArgsK,
          pSt σ (pHeapCall nv sv n l lp siv civ) 13, ch) := by
  with_unfolding_all rfl

/-! ### The `isPalindrome` prologue

Split at `len(s)`: the length op reads the slice against the heap, so
it is a conditioned step, not a definitional one. -/

/-- Prologue A: `i := 0`, `j` declared → the `len(s)` apply point.
25 steps. -/
theorem p_preA_rawP (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 25 (pSt σ (pHeapPFrame nv sv n l lp siv civ) 15)
      (.exec isPalindromeFunc.body pFrameEnv pFrameK) ch
      = .ok (.retV (pSliceS n) pJLenKP,
          pSt σ (pHeapP1 nv sv n l lp siv civ) 17, ch) := by
  with_unfolding_all rfl

/-- Prologue B: the length delivered → `j := len-1`, the first-pass
flag, the loop head. 21 steps. -/
theorem p_preB_rawP (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 21 (pSt σ (pHeapP1 nv sv n l lp siv civ) 17)
      (.retV (.int ((n : Nat) : Int) .int) pJSubKP) ch
      = .ok (pHeadCfgP,
          pSt σ (pHeapP nv sv n l lp siv civ 0
            (IntKind.normalize .int
              (IntKind.normalize .int (((n : Nat) : Int) - 1))) true) 18,
          ch) := by
  with_unfolding_all rfl

/-! ### The subject loop -/

theorem ph_A0_rawP (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ iv jv : Int) (ch : Choices) :
    stepFnIter 25 (pSt σ (pHeapP nv sv n l lp siv civ iv jv true) 18)
      pHeadCfgP ch
      = .ok (.retV (.bool (decide (iv < jv))) pCmpIfKP,
          pSt σ (pHeapP nv sv n l lp siv civ iv jv false) 18, ch) := by
  with_unfolding_all rfl

theorem ph_A1_rawP (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ iv jv : Int) (ch : Choices) :
    stepFnIter 18 (pSt σ (pHeapP nv sv n l lp siv civ iv jv false) 18)
      pHeadCfgP ch
      = .ok (.retV (.bool (decide (iv < jv))) pCmpIfKP,
          pSt σ (pHeapP nv sv n l lp siv civ iv jv false) 18, ch) := by
  with_unfolding_all rfl

/-- Body A: test true → the `s[i]` read at its apply point. 11 steps. -/
theorem ph_B1_rawP (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ iv jv : Int) (ch : Choices) :
    stepFnIter 11 (pSt σ (pHeapP nv sv n l lp siv civ iv jv false) 18)
      (.retV (.bool true) pCmpIfKP) ch
      = .ok (.retV (.int iv .int) (pIdx1KP n),
          pSt σ (pHeapP nv sv n l lp siv civ iv jv false) 18, ch) := by
  with_unfolding_all rfl

/-- Body B: `s[i]` banked → the `s[j]` read at its apply point.
5 steps. -/
theorem ph_B2_rawP (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ iv jv a : Int) (ch : Choices) :
    stepFnIter 5 (pSt σ (pHeapP nv sv n l lp siv civ iv jv false) 18)
      (.retV (.int a .uint64)
        (.strictK (.neqCmp tU64) [] [.indexGet (.var "s") (.var "j")] pEnvB2
          pNeIfKP)) ch
      = .ok (.retV (.int jv .int) (pIdx2KP n a),
          pSt σ (pHeapP nv sv n l lp siv civ iv jv false) 18, ch) := by
  with_unfolding_all rfl

/-- Body C: both elements banked → the `!=` verdict. 1 step. -/
theorem ph_B3_rawP (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ iv jv a b : Int) (ch : Choices) :
    stepFnIter 1 (pSt σ (pHeapP nv sv n l lp siv civ iv jv false) 18)
      (.retV (.int b .uint64)
        (.strictK (.neqCmp tU64) [.int a .uint64] [] pEnvB2 pNeIfKP)) ch
      = .ok (.retV (.bool (!(a == b))) pNeIfKP,
          pSt σ (pHeapP nv sv n l lp siv civ iv jv false) 18, ch) := by
  with_unfolding_all rfl

/-- The MATCH branch: the pair agreed → `i++`, `j--`, the loop head.
31 steps. -/
theorem ph_match_rawP (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ iv jv : Int) (ch : Choices) :
    stepFnIter 31 (pSt σ (pHeapP nv sv n l lp siv civ iv jv false) 18)
      (.retV (.bool false) pNeIfKP) ch
      = .ok (pHeadCfgP,
          pSt σ (pHeapP nv sv n l lp siv civ
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            (IntKind.normalize .int (IntKind.normalize .int (jv - 1)))
            false) 18, ch) := by
  with_unfolding_all rfl

/-- The MISMATCH branch: `return 0`, the frame exit into `v`, and the
`$res0 = pre` store PENDING. 35 steps; the store itself cannot reduce
definitionally (the array's contents are symbolic), which is exactly
why it is split out. -/
theorem ph_mismatch_rawP (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ iv jv : Int) (ch : Choices) :
    stepFnIter 35 (pSt σ (pHeapP nv sv n l lp siv civ iv jv false) 18)
      (.retV (.bool true) pNeIfKP) ch
      = .ok (.next (.storeK [pRes0Ref]
            [.array ⟨lp.map (fun v => .int v .uint64)⟩] (.seqn #[])
            callEnvP pEpiTail),
          pSt σ (pHeapPreStore nv sv n l lp siv civ iv jv 0) 18, ch) := by
  with_unfolding_all rfl

/-- The LOOP EXIT: `i ≥ j`, the walk met in the middle → `return 1`,
the frame exit, and the same pending `$res0` store. 33 steps. -/
theorem ph_exit_rawP (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ iv jv : Int) (ch : Choices) :
    stepFnIter 33 (pSt σ (pHeapP nv sv n l lp siv civ iv jv false) 18)
      (.retV (.bool false) pCmpIfKP) ch
      = .ok (.next (.storeK [pRes0Ref]
            [.array ⟨lp.map (fun v => .int v .uint64)⟩] (.seqn #[])
            callEnvP pEpiTail),
          pSt σ (pHeapPreStore nv sv n l lp siv civ iv jv 1) 18, ch) := by
  with_unfolding_all rfl

/-- The tail: `$res1 := v`, return, barrier exit — the driver terminal.
15 steps. -/
theorem ph_fin_rawP (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ iv jv vv : Int) (ch : Choices) :
    stepFnIter 15 (pSt σ (pHeapStored nv sv n l lp siv civ iv jv vv) 18)
      (.next (.storeK [] [] (.seqn #[]) callEnvP pEpiTail)) ch
      = .ok (.next .stop,
          pSt σ (pHeapEnd nv sv n l lp siv civ iv jv vv) 18, ch) := by
  with_unfolding_all rfl

/-! ## The `$res0 = pre` store's side condition -/

/-- Normalizing an in-range uint64 list at an array type is the
identity. -/
theorem normalizeValueForTy_arr8_u64P {σ : ExecState} {lp : List Int}
    (hlen : lp.length = 8) (hl : ∀ v ∈ lp, 0 ≤ v ∧ v < 2 ^ 64) :
    normalizeValueForTy σ (.array 8 tU64)
        (.array ⟨lp.map (fun v => .int v .uint64)⟩)
      = .ok (.array ⟨lp.map (fun v => .int v .uint64)⟩) :=
  GoLean.SliceMem.normalizeValueForTy_arr_u64 hlen hl

/-! ## The setup loop, cleaned + its induction (the P5 schema) -/

/-- One setup iteration from the exit test's true delivery at `i`.
57 steps. -/
theorem su_iterP (σ : ExecState) (n seed i : Nat) (hn : n < 2 ^ 63)
    (hi : i < n) (ch : Choices) :
    stepFnIter 57
      (pSt σ (pHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
        (palFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false) 9)
      (.retV (.bool true) suCmpKP) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) suCmpKP,
          pSt σ (pHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
            (palFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
            ((i + 1 : Nat) : Int) false) 9, ch) := by
  have hB1a := su_B1a_rawP σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (palFamily i seed ++ List.replicate (n - i) 0) ((i : Nat) : Int) ch
  have hmod := stepFnIter_one (stepFn_strict_apply
    (done := [.int ((i : Nat) : Int) .uint64]) (env := suEnvP2)
    (k := suAddKP n ((seed : Nat) : Int) ((i : Nat) : Int)) (ch := ch)
    (applyStrictOp_mod_u64
      (σ := pSt σ (pHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
        (palFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false) 9)
      (a := i) (b := 2) (by omega) (by omega)))
  have h1 := stepFnIter_chain hB1a hmod
  have hB1b := su_B1b_rawP σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (palFamily i seed ++ List.replicate (n - i) 0)
    ((i : Nat) : Int) ((i % 2 : Nat) : Int) ch
  rw [unorm_add_nat seed (i % 2)] at hB1b
  have h2 := stepFnIter_chain h1 hB1b
  have hw : (0 : Int) ≤ (((seed + i % 2) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + i % 2) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + i % 2) (y := 2 ^ 64) (by omega)
    omega
  have hst := storeTarget_slice_u64
    (σ := pSt σ (pHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
      (palFamily i seed ++ List.replicate (n - i) 0)
      ((i : Nat) : Int) false) 9)
    (a := ⟨5⟩) (off := 0) (len := n) (cap := n) (i := i) (n := n)
    (ik := .uint64) (l := palFamily i seed ++ List.replicate (n - i) 0)
    (w := (((seed + i % 2) % 2 ^ 64 : Nat) : Int))
    (lookup_suP σ ((n : Nat) : Int) ((seed : Nat) : Int) n
      (palFamily i seed ++ List.replicate (n - i) 0) ((i : Nat) : Int)
      false 9)
    (Nat.le_refl n) hi
    (by rw [List.length_append, familyMod_length, List.length_replicate]
        omega)
    (by rw [List.length_append, familyMod_length, List.length_replicate]
        omega)
    familyModZ_range hw
  rw [Nat.zero_add, familyMod_set hi] at hst
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hst))
  have hD := su_D_rawP σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (palFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
    ((i : Nat) : Int) ch
  have h4 := stepFnIter_chain h3 hD
  have hA1 := su_A1_rawP σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (palFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
    ((i : Nat) : Int) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  exact stepFnIter_chain h4 hA1

/-- **The setup loop**, by the P5 iteration schema: `57·(n−i)` steps
materialize the wrapped `seed + i%2` family. -/
theorem su_loopP (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 63) :
    ∀ i, i ≤ n → ∀ ch : Choices,
    stepFnIter (57 * (n - i))
      (pSt σ (pHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
        (palFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false) 9)
      (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
        suCmpKP) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) suCmpKP,
          pSt σ (pHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
            (palFamily n seed) ((n : Nat) : Int) false) 9, ch) := by
  intro i hin ch
  have hgen := stepFnIter_iterate (c := 57) (n := n)
    (T := fun j => pSt σ (pHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
      (palFamily j seed ++ List.replicate (n - j) 0)
      ((j : Nat) : Int) false) 9)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int)
      < ((n : Nat) : Int)))) suCmpKP)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact su_iterP σ n seed j hn hj ch')
    i hin ch
  simpa using hgen

/-! ## The copy loop, cleaned + its induction -/

theorem cp_iterP (σ : ExecState) (n seed : Nat) (siv : Int) (m : Nat)
    (hn : n < 2 ^ 63) (hcap : n ≤ 8) (hm : m < n) (ch : Choices) :
    stepFnIter 53
      (pSt σ (pHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
        (palFamily n seed) (palPre m seed) siv ((m : Nat) : Int) false) 12)
      (.retV (.bool true) cpCmpKP) ch
      = .ok (.retV (.bool (decide
            (((m + 1 : Nat) : Int) < ((n : Nat) : Int)))) cpCmpKP,
          pSt σ (pHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
            (palFamily n seed) (palPre (m + 1) seed) siv
            ((m + 1 : Nat) : Int) false) 12, ch) := by
  have hB1 := cp_B1_rawP σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (palFamily n seed) (palPre m seed) siv ((m : Nat) : Int) ch
  have hget : (⟨(palFamily n seed).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + m]?
      = some (.int (((seed + m % 2) % 2 ^ 64 : Nat) : Int) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by rw [familyMod_length]; omega),
      familyMod_getD hm]
  have hread := stepFn_strict_apply (done := [pSliceS n]) (env := cpEnvP2)
    (k := cpRhsKP ((m : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .uint64)
      (lookup_cpS_P σ ((n : Nat) : Int) ((seed : Nat) : Int) n
        (palFamily n seed) (palPre m seed) siv ((m : Nat) : Int) false 12)
      (Nat.le_refl n) hm hget)
  have hB2 := cp_B2_rawP σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (palFamily n seed) (palPre m seed) siv ((m : Nat) : Int)
    (.int (((seed + m % 2) % 2 ^ 64 : Nat) : Int) .uint64) ch
  have hw : (0 : Int) ≤ (((seed + m % 2) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + m % 2) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + m % 2) (y := 2 ^ 64) (by omega)
    omega
  have hst := storeTarget_arrayLocal_u64 (a := ⟨9⟩) (N := 8) (i := m)
    (ik := .uint64) (l := palPre m seed)
    (w := (((seed + m % 2) % 2 ^ 64 : Nat) : Int))
    (lookup_cpPre_P σ ((n : Nat) : Int) ((seed : Nat) : Int) n
      (palFamily n seed) (palPre m seed) siv ((m : Nat) : Int) false 12)
    (by rw [palPre_length (by omega)]; omega)
    (palPre_length (by omega)) palPre_range hw
  rw [prefixPad_familyMod_set (by omega : m < 8)] at hst
  have hstore : storeTarget
      (pSt σ (pHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
        (palFamily n seed) (palPre m seed) siv ((m : Nat) : Int) false) 12)
      (cpRefP ((m : Nat) : Int))
      (.int (((seed + m % 2) % 2 ^ 64 : Nat) : Int) .uint64)
      = .ok (pSt σ (pHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
          (palFamily n seed) (palPre (m + 1) seed) siv
          ((m : Nat) : Int) false) 12) := hst
  have hD := cp_D_rawP σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (palFamily n seed) (palPre (m + 1) seed) siv ((m : Nat) : Int) ch
  have hA1 := cp_A1_rawP σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (palFamily n seed) (palPre (m + 1) seed) siv ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  have h1 := stepFnIter_chain hB1 (stepFnIter_one hread)
  have h2 := stepFnIter_chain h1 hB2
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hstore))
  exact stepFnIter_chain (stepFnIter_chain h3 hD) hA1

/-- **The copy loop + the call**: from the exit-test delivery at `m`,
the run reaches the subject's loop head within `53·μ + 61` steps — the
copy exit (13), the ONE program-consulting `enterFrame` step, and
`isPalindrome`'s prologue (25 + 1 + 21). -/
theorem cp_loopP (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 63)
    (hcap : n ≤ 8)
    (henter : ∀ (l lp : List Int) (siv civ : Int),
      enterFrame (pSt σ (pHeapCall ((n : Nat) : Int) ((seed : Nat) : Int)
          n l lp siv civ) 13) ⟨"isPalindrome"⟩ [pSliceS n]
        = .ok (isPalindromeFunc, pFrameEnv, [.base ⟨14⟩],
            pSt σ (pHeapPFrame ((n : Nat) : Int) ((seed : Nat) : Int)
              n l lp siv civ) 15)) :
    ∀ μ m : Nat, m + μ = n → ∀ ch : Choices,
    ∃ k : Nat, k ≤ 53 * μ + 61 ∧
      stepFnIter k
        (pSt σ (pHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
          (palFamily n seed) (palPre m seed) ((n : Nat) : Int)
          ((m : Nat) : Int) false) 12)
        (.retV (.bool (decide (((m : Nat) : Int) < ((n : Nat) : Int))))
          cpCmpKP) ch
        = .ok (pHeadCfgP,
            pSt σ (pHeapP ((n : Nat) : Int) ((seed : Nat) : Int) n
              (palFamily n seed) (palPre n seed) ((n : Nat) : Int)
              ((n : Nat) : Int) ((0 : Nat) : Int)
              (((n : Nat) : Int) - 1 - ((0 : Nat) : Int)) true) 18,
            ch) := by
  have hjfix : IntKind.normalize .int
      (IntKind.normalize .int (((n : Nat) : Int) - 1))
      = ((n : Nat) : Int) - 1 - ((0 : Nat) : Int) := by
    rw [inorm_of_range (v := ((n : Nat) : Int) - 1) (by omega) (by omega),
      inorm_of_range (v := ((n : Nat) : Int) - 1) (by omega) (by omega)]
    omega
  have hifix : (0 : Int) = ((0 : Nat) : Int) := rfl
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
          (cp_iterP σ n seed ((n : Nat) : Int) m hn hcap hlt ch) hrun⟩
    · have hmn : m = n := by omega
      subst hmn
      rw [show (decide (((m : Nat) : Int) < ((m : Nat) : Int))) = false from
        decide_eq_false (by omega)]
      have hX := cp_X_rawP σ ((m : Nat) : Int) ((seed : Nat) : Int) m
        (palFamily m seed) (palPre m seed) ((m : Nat) : Int)
        ((m : Nat) : Int) ch
      have hent := stepFnIter_one (ch := ch)
        (stepFn_call_enter (plans := pShapes) (env := callEnvP)
          (k := pAfterCall) (vals := []) (v := pSliceS m)
          (henter (palFamily m seed) (palPre m seed) ((m : Nat) : Int)
            ((m : Nat) : Int)))
      have hA := p_preA_rawP σ ((m : Nat) : Int) ((seed : Nat) : Int) m
        (palFamily m seed) (palPre m seed) ((m : Nat) : Int)
        ((m : Nat) : Int) ch
      have hlenap : applyStrictOp
          (pSt σ (pHeapP1 ((m : Nat) : Int) ((seed : Nat) : Int) m
            (palFamily m seed) (palPre m seed) ((m : Nat) : Int)
            ((m : Nat) : Int)) 17)
          (.lengthOf (some (.slice tU64))) [pSliceS m]
          = .ok (.int ((m : Nat) : Int) .int,
              pSt σ (pHeapP1 ((m : Nat) : Int) ((seed : Nat) : Int) m
                (palFamily m seed) (palPre m seed) ((m : Nat) : Int)
                ((m : Nat) : Int)) 17) :=
        applyStrictOp_len_slice (Nat.le_refl _)
      have hlen := stepFnIter_one (ch := ch)
        (stepFn_strict_apply (done := []) (env := pEnvIJ) (k := pJSubKP)
          hlenap)
      have hB := p_preB_rawP σ ((m : Nat) : Int) ((seed : Nat) : Int) m
        (palFamily m seed) (palPre m seed) ((m : Nat) : Int)
        ((m : Nat) : Int) ch
      rw [hjfix, hifix] at hB
      exact ⟨13 + 1 + 25 + 1 + 21, by omega,
        stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain hX hent) hA) hlen) hB⟩

/-! ## The subject loop, cleaned + its induction

The loop runs to the DRIVER TERMINAL: both exits (the middle reached,
or a mismatched pair) land on `.next .stop` with `palinSpec l` in
`$res1`. `i`/`j` differ between them and are existentially quantified —
nothing downstream reads those cells. -/

/-- One full subject iteration (the pair matched): 68 steps from the
exit test's true delivery at `m` to the next exit test's delivery at
`m+1`. -/
theorem ph_iterP (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (m : Nat) (hln : l.length = n) (hn : n ≤ 8)
    (hm : m < n / 2)
    (heq : l.getD m 0 = l.getD (n - 1 - m) 0) (ch : Choices) :
    stepFnIter 68
      (pSt σ (pHeapP nv sv n l lp siv civ ((m : Nat) : Int)
        (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) false) 18)
      (.retV (.bool true) pCmpIfKP) ch
      = .ok (.retV (.bool (decide (((m + 1 : Nat) : Int)
            < ((n : Nat) : Int) - 1 - ((m + 1 : Nat) : Int)))) pCmpIfKP,
          pSt σ (pHeapP nv sv n l lp siv civ ((m + 1 : Nat) : Int)
            (((n : Nat) : Int) - 1 - ((m + 1 : Nat) : Int)) false) 18,
          ch) := by
  have hmn : m < n := by omega
  have hjn : n - 1 - m < n := by omega
  have hgeti : (⟨l.map (fun v => .int v .uint64)⟩ : Array GoValue)[0 + m]?
      = some (.int (l.getD m 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega)]
  have hgetj : (⟨l.map (fun v => .int v .uint64)⟩ : Array GoValue)[0 + (n - 1 - m)]?
      = some (.int (l.getD (n - 1 - m) 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega)]
  have hB1 := ph_B1_rawP σ nv sv n l lp siv civ ((m : Nat) : Int)
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) ch
  have hread1 := stepFn_strict_apply (done := [pSliceS n]) (env := pEnvB2)
    (k := .strictK (.neqCmp tU64) [] [.indexGet (.var "s") (.var "j")]
      pEnvB2 pNeIfKP) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .int) (i := m)
      (lookup_pP σ nv sv n l lp siv civ ((m : Nat) : Int)
        (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) false 18)
      (Nat.le_refl n) hmn hgeti)
  have hB2 := ph_B2_rawP σ nv sv n l lp siv civ ((m : Nat) : Int)
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) (l.getD m 0) ch
  have hjcast : (((n : Nat) : Int) - 1 - ((m : Nat) : Int))
      = (((n - 1 - m : Nat) : Int)) := by omega
  have hread2 := stepFn_strict_apply (done := [pSliceS n]) (env := pEnvB2)
    (k := .strictK (.neqCmp tU64) [.int (l.getD m 0) .uint64] [] pEnvB2
      pNeIfKP) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .int) (i := n - 1 - m)
      (lookup_pP σ nv sv n l lp siv civ ((m : Nat) : Int)
        (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) false 18)
      (Nat.le_refl n) hjn hgetj)
  rw [← hjcast] at hread2
  have hB3 := ph_B3_rawP σ nv sv n l lp siv civ ((m : Nat) : Int)
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) (l.getD m 0)
    (l.getD (n - 1 - m) 0) ch
  rw [show (!((l.getD m 0) == (l.getD (n - 1 - m) 0))) = false from by
    rw [heq]; simp] at hB3
  have hM := ph_match_rawP σ nv sv n l lp siv civ ((m : Nat) : Int)
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) ch
  rw [show IntKind.normalize .int (IntKind.normalize .int
        (((m : Nat) : Int) + 1)) = ((m + 1 : Nat) : Int) from by
      rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
        inorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
        inorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)],
    show IntKind.normalize .int (IntKind.normalize .int
        ((((n : Nat) : Int) - 1 - ((m : Nat) : Int)) - 1))
        = ((n : Nat) : Int) - 1 - ((m + 1 : Nat) : Int) from by
      rw [inorm_of_range (v := (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) - 1)
          (by omega) (by omega),
        inorm_of_range (v := (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) - 1)
          (by omega) (by omega)]
      omega] at hM
  have hA1 := ph_A1_rawP σ nv sv n l lp siv civ ((m + 1 : Nat) : Int)
    (((n : Nat) : Int) - 1 - ((m + 1 : Nat) : Int)) ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain hB1 (stepFnIter_one hread1)) hB2)
        (stepFnIter_one hread2)) hB3) hM) hA1


/-! ### The two ways out of the subject loop

Both land on the SAME driver terminal; they differ only in the verdict
and in where `i`/`j` stopped. -/

/-- **The mismatch exit**: a pair disagrees at `m`, so `isPalindrome`
returns `0` immediately. 70 steps from the exit test's true delivery
(19 to the `!=` verdict, 35 to the pending `$res0` store, the store,
15 to the terminal). -/
theorem ph_bailP (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (m : Nat) (hln : l.length = n)
    (hlp : lp.length = 8) (hlpr : ∀ v ∈ lp, 0 ≤ v ∧ v < 2 ^ 64)
    (hm : m < n / 2)
    (hne : ¬ (l.getD m 0 = l.getD (n - 1 - m) 0)) (ch : Choices) :
    stepFnIter 70
      (pSt σ (pHeapP nv sv n l lp siv civ ((m : Nat) : Int)
        (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) false) 18)
      (.retV (.bool true) pCmpIfKP) ch
      = .ok (.next .stop,
          pSt σ (pHeapEnd nv sv n l lp siv civ ((m : Nat) : Int)
            (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) 0) 18, ch) := by
  have hmn : m < n := by omega
  have hjn : n - 1 - m < n := by omega
  have hgeti : (⟨l.map (fun v => .int v .uint64)⟩ : Array GoValue)[0 + m]?
      = some (.int (l.getD m 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega)]
  have hgetj : (⟨l.map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + (n - 1 - m)]?
      = some (.int (l.getD (n - 1 - m) 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega)]
  have hjcast : (((n : Nat) : Int) - 1 - ((m : Nat) : Int))
      = (((n - 1 - m : Nat) : Int)) := by omega
  have hB1 := ph_B1_rawP σ nv sv n l lp siv civ ((m : Nat) : Int)
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) ch
  have hread1 := stepFn_strict_apply (done := [pSliceS n]) (env := pEnvB2)
    (k := .strictK (.neqCmp tU64) [] [.indexGet (.var "s") (.var "j")]
      pEnvB2 pNeIfKP) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .int) (i := m)
      (lookup_pP σ nv sv n l lp siv civ ((m : Nat) : Int)
        (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) false 18)
      (Nat.le_refl n) hmn hgeti)
  have hB2 := ph_B2_rawP σ nv sv n l lp siv civ ((m : Nat) : Int)
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) (l.getD m 0) ch
  have hread2 := stepFn_strict_apply (done := [pSliceS n]) (env := pEnvB2)
    (k := .strictK (.neqCmp tU64) [.int (l.getD m 0) .uint64] [] pEnvB2
      pNeIfKP) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .int) (i := n - 1 - m)
      (lookup_pP σ nv sv n l lp siv civ ((m : Nat) : Int)
        (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) false 18)
      (Nat.le_refl n) hjn hgetj)
  rw [← hjcast] at hread2
  have hB3 := ph_B3_rawP σ nv sv n l lp siv civ ((m : Nat) : Int)
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) (l.getD m 0)
    (l.getD (n - 1 - m) 0) ch
  rw [show (!((l.getD m 0) == (l.getD (n - 1 - m) 0))) = true from by
    simp only [beq_eq_false_iff_ne, ne_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not]
    exact hne] at hB3
  have hX := ph_mismatch_rawP σ nv sv n l lp siv civ ((m : Nat) : Int)
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) ch
  have hstore : storeTarget
      (pSt σ (pHeapPreStore nv sv n l lp siv civ ((m : Nat) : Int)
        (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) 0) 18)
      pRes0Ref (.array ⟨lp.map (fun v => .int v .uint64)⟩)
      = .ok (pSt σ (pHeapStored nv sv n l lp siv civ ((m : Nat) : Int)
          (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) 0) 18) :=
    storeTarget_addr
      (lookup_preStoreP σ nv sv n l lp siv civ ((m : Nat) : Int)
        (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) 0 18)
      (normalizeValueForTy_arr8_u64P hlp hlpr)
  have hF := ph_fin_rawP σ nv sv n l lp siv civ ((m : Nat) : Int)
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) 0 ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain hB1 (stepFnIter_one hread1)) hB2)
        (stepFnIter_one hread2)) hB3) hX)
          (stepFnIter_one (stepFn_store_step hstore))) hF

/-- **The middle exit**: `i ≥ j`, so `isPalindrome` returns `1`.
49 steps from the exit test's false delivery. -/
theorem ph_outP (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ iv jv : Int) (hlp : lp.length = 8)
    (hlpr : ∀ v ∈ lp, 0 ≤ v ∧ v < 2 ^ 64) (ch : Choices) :
    stepFnIter 49 (pSt σ (pHeapP nv sv n l lp siv civ iv jv false) 18)
      (.retV (.bool false) pCmpIfKP) ch
      = .ok (.next .stop,
          pSt σ (pHeapEnd nv sv n l lp siv civ iv jv 1) 18, ch) := by
  have hX := ph_exit_rawP σ nv sv n l lp siv civ iv jv ch
  have hstore : storeTarget
      (pSt σ (pHeapPreStore nv sv n l lp siv civ iv jv 1) 18)
      pRes0Ref (.array ⟨lp.map (fun v => .int v .uint64)⟩)
      = .ok (pSt σ (pHeapStored nv sv n l lp siv civ iv jv 1) 18) :=
    storeTarget_addr
      (lookup_preStoreP σ nv sv n l lp siv civ iv jv 1 18)
      (normalizeValueForTy_arr8_u64P hlp hlpr)
  have hF := ph_fin_rawP σ nv sv n l lp siv civ iv jv 1 ch
  exact stepFnIter_chain (stepFnIter_chain hX
    (stepFnIter_one (stepFn_store_step hstore))) hF

/-- **The subject loop**: from the exit-test delivery at `m` — with
every earlier pair known to match — the run reaches the DRIVER TERMINAL
within `68·μ + 70` steps, with `palinSpec l` as the verdict. The final
`i`/`j` are existentially quantified: the two exits stop at different
places and nothing downstream reads those cells. -/
theorem ph_loopP (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (hln : l.length = n) (hn : n ≤ 8) (hlp : lp.length = 8)
    (hlpr : ∀ v ∈ lp, 0 ≤ v ∧ v < 2 ^ 64) :
    ∀ μ m : Nat, m ≤ n / 2 → μ = n / 2 - m → PalinUpTo l m → ∀ ch : Choices,
    ∃ (k : Nat) (iv jv : Int), k ≤ 68 * μ + 70 ∧
      stepFnIter k
        (pSt σ (pHeapP nv sv n l lp siv civ ((m : Nat) : Int)
          (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) false) 18)
        (.retV (.bool (decide (((m : Nat) : Int)
          < ((n : Nat) : Int) - 1 - ((m : Nat) : Int)))) pCmpIfKP) ch
        = .ok (.next .stop,
            pSt σ (pHeapEnd nv sv n l lp siv civ iv jv (palinSpec l)) 18,
            ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hmc hμ hup ch
    rcases Nat.lt_or_ge m (n / 2) with hlt | hge
    · rw [show (decide (((m : Nat) : Int)
          < ((n : Nat) : Int) - 1 - ((m : Nat) : Int))) = true from
        decide_eq_true (by omega)]
      by_cases heq : l.getD m 0 = l.getD (n - 1 - m) 0
      · -- the pair matches: one full iteration, then recurse
        obtain ⟨k, iv, jv, hk, hrun⟩ := ih (μ - 1) (by omega) (m + 1)
          (by omega) (by omega) (palinUpTo_succ hup (by rw [hln]; exact heq)) ch
        refine ⟨68 + k, iv, jv, by omega, ?_⟩
        exact stepFnIter_chain
          (ph_iterP σ nv sv n l lp siv civ m hln hn hlt heq ch) hrun
      · -- the pair disagrees: the early return, verdict 0
        refine ⟨70, ((m : Nat) : Int),
          (((n : Nat) : Int) - 1 - ((m : Nat) : Int)), by omega, ?_⟩
        rw [show palinSpec l = 0 from
          palinSpec_of_mismatch (by omega : m < l.length)
            (by rw [hln]; exact heq)]
        exact ph_bailP σ nv sv n l lp siv civ m hln hlp hlpr hlt heq ch
    · -- the walk met in the middle: verdict 1
      have hmn : m = n / 2 := by omega
      subst hmn
      rw [show (decide (((n / 2 : Nat) : Int)
          < ((n : Nat) : Int) - 1 - ((n / 2 : Nat) : Int))) = false from
        decide_eq_false (by omega)]
      refine ⟨49, ((n / 2 : Nat) : Int),
        (((n : Nat) : Int) - 1 - ((n / 2 : Nat) : Int)), by omega, ?_⟩
      rw [show palinSpec l = 1 from
        palinSpec_of_full (by rw [hln]; exact hup)]
      exact ph_outP σ nv sv n l lp siv civ _ _ hlp hlpr ch

/-! ## The run, end to end -/

/-- The `enterFrame` discharge at the pinned program: the second and
last unfolding of `palinLowered` in this example. -/
theorem p_enterFrame_fact (n seed : Nat) (l lp : List Int) (siv civ : Int) :
    enterFrame
        (pSt pProg (pHeapCall ((n : Nat) : Int) ((seed : Nat) : Int) n l lp
          siv civ) 13) ⟨"isPalindrome"⟩ [pSliceS n]
      = .ok (isPalindromeFunc, pFrameEnv, [.base ⟨14⟩],
          pSt pProg (pHeapPFrame ((n : Nat) : Int) ((seed : Nat) : Int) n l lp
            siv civ) 15) := by
  with_unfolding_all rfl

/-- **The harness run, PROGRAM-generic**: within `144·n + 298` steps the
harness reaches the driver terminal with the pre-copy in `$res0` and
`palinSpec` of the family in `$res1`. -/
theorem p_runs_generic (σ : ExecState) (n seed : Nat) (hcap : n ≤ 8)
    (henter : ∀ (l lp : List Int) (siv civ : Int),
      enterFrame (pSt σ (pHeapCall ((n : Nat) : Int) ((seed : Nat) : Int)
          n l lp siv civ) 13) ⟨"isPalindrome"⟩ [pSliceS n]
        = .ok (isPalindromeFunc, pFrameEnv, [.base ⟨14⟩],
            pSt σ (pHeapPFrame ((n : Nat) : Int) ((seed : Nat) : Int)
              n l lp siv civ) 15))
    (ch : Choices) :
    ∃ (k : Nat) (iv jv : Int), k ≤ 144 * n + 298 ∧
      stepFnIter k (pSt σ (pHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)) 4)
        pHC0 ch
        = .ok (.next .stop,
            pSt σ (pHeapEnd ((n : Nat) : Int) ((seed : Nat) : Int) n
              (palFamily n seed) (palPre n seed) ((n : Nat) : Int)
              ((n : Nat) : Int) iv jv (palinSpec (palFamily n seed))) 18,
            ch) := by
  have hn : n < 2 ^ 63 := by omega
  have hlen : (palFamily n seed).length = n := familyMod_length 2 n seed
  -- entry
  have hE1 := p_E1_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) ch
  have hmk := stepFnIter_one
    (stepFn_makeSlice_u64_step (env := envC8P)
      (k := .seq [pS2, pS3, pS4, pS5, pS6, pS7] envC8P
        (.frame [] [] [] [] .stop))
      (p_make_apply σ ((n : Nat) : Int) ((seed : Nat) : Int) n ch))
  have hE2 := p_E2_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n ch
  have hA0 := su_A0_rawP σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (List.replicate n 0) 0 ch
  have hsu := su_loopP σ n seed hn 0 (by omega) ch
  rw [show palFamily 0 seed ++ List.replicate (n - 0) 0
      = List.replicate n 0 from by simp [familyMod],
    show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hsu
  have hentry := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hE1 hmk) hE2) hA0) hsu
  -- the setup exit
  have hX := su_X_rawP σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (palFamily n seed) ((n : Nat) : Int) ch
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hentry
  have hthru := stepFnIter_chain hentry hX
  -- the copy loop and the call
  have hcA0 := cp_A0_rawP σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (palFamily n seed) zeros8 ((n : Nat) : Int) 0 ch
  obtain ⟨k2, hk2, hcp⟩ := cp_loopP σ n seed hn hcap henter n 0 (by omega) ch
  rw [show palPre 0 seed = zeros8 from palPre_zero seed,
    show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hcp
  have hthru2 := stepFnIter_chain (stepFnIter_chain hthru hcA0) hcp
  -- the subject loop
  have hpA0 := ph_A0_rawP σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (palFamily n seed) (palPre n seed) ((n : Nat) : Int) ((n : Nat) : Int)
    ((0 : Nat) : Int) (((n : Nat) : Int) - 1 - ((0 : Nat) : Int)) ch
  obtain ⟨k3, iv, jv, hk3, hph⟩ := ph_loopP σ ((n : Nat) : Int)
    ((seed : Nat) : Int) n (palFamily n seed) (palPre n seed)
    ((n : Nat) : Int) ((n : Nat) : Int) hlen hcap
    (palPre_length hcap) palPre_range (n / 2) 0 (by omega) (by omega)
    (palinUpTo_zero _) ch
  refine ⟨10 + 1 + 42 + 25 + 57 * (n - 0) + 39 + 25 + k2 + (25 + k3),
    iv, jv, by omega, ?_⟩
  exact stepFnIter_chain hthru2 (stepFnIter_chain hpA0 hph)

end GoLean.Examples.ArrayPalindrome
