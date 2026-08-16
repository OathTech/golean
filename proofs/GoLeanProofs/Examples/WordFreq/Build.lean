import GoLeanProofs.Examples.WordFreq.Machine

/-!
# WordFreq — the `buildText` phase

Entry (the harness prologue and the `buildText(n, seed)` call), the
build loop — `out += string(rune(97 + (seed+i)%3))` plus the `i % 3`
separator append (one space / two spaces / a tab) — and the exit
through the `q` computation into the `wordFreq(pre, q)` call's frame
entry point.

Per-segment step counts (probe-measured, tracer
`.tmp/e5-drafts/trace-3-4-1.txt`, re-checked by `rfl` here): entry →
args delivered 10; frame prologue 43; dispatch first/later 25/29; one
iteration 63 (separator `" "`) / 74 (`"  "`, `"\t"`) to the loop head,
so 92/103 delivery-to-delivery; exit → the `wordFreq` call's second
argument delivered 43 + 1 + 2 + 1 + 15 (two conditioned points: the
`qsel % 3` mod and the ASCII `string(rune(·))`).

The loop's per-iteration conditioned steps are PURE facts — the two
`%`s (kit) and the ASCII `string(rune(·))` (Machine) — because a Go
string is a value; everything else is `with_unfolding_all rfl`. The
iteration count varies by separator arm, so the loop lemma carries
`∃ k ≤ 103·(n−i)` accounting rather than a uniform product.
-/

namespace GoLean.Examples.WordFreq

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## Environments and continuations — the `buildText` frame -/

def btFScope : Scope :=
  [("$res0", .base ⟨10⟩), ("seed", .base ⟨9⟩), ("n", .base ⟨8⟩)]
def btEnv : LocalEnv :=
  [[("$forFirst", .base ⟨13⟩)], [("i", .base ⟨12⟩)],
   [("out", .base ⟨11⟩)], btFScope]
/-- The while-body block's scope. -/
def btEnvC : LocalEnv := [] :: btEnv
/-- The store block's scope. -/
def btEnv2 : LocalEnv := [] :: btEnvC
/-- A separator arm block's scope. -/
def btEnv3 : LocalEnv := [] :: btEnv2

def btTailSeqn : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "out"), .returnStmt]
def btHeadTail : Cont :=
  .seq [] btEnv
    (.seq [] [[("i", .base ⟨12⟩)], [("out", .base ⟨11⟩)], btFScope]
      (.seq [btTailSeqn] [[("out", .base ⟨11⟩)], btFScope] btFrameK))
def btHeadCfg : Config :=
  .exec (.while (.boolLit true) buildTextFunc.btWhileBody) btEnv btHeadTail
def btLoopK : Cont :=
  .loop (.boolLit true) buildTextFunc.btWhileBody btEnv btHeadTail
def btCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt btEnvC
    (.seq [buildTextFunc.btStoreBlock] btEnvC btLoopK)

/-- After the letter store: the separator `if` is next. -/
def btStTail1 : Cont :=
  .seq [buildTextFunc.btSepIf] btEnv2 (.seq [] btEnvC btLoopK)
def btOutRef : TargetRef := .chain (.addr (.base ⟨11⟩)) [] []
def btRhsK1 : Cont := .rhsK .vals [btOutRef] [] [] (.seqn #[]) btEnv2 btStTail1
def btAppK (ov : GoString) : Cont := .strictK .add [.string ov] [] btEnv2 btRhsK1
def btRuneK (ov : GoString) : Cont :=
  .strictK .stringFromRune [] [] btEnv2 (btAppK ov)
def btConvK (ov : GoString) : Cont :=
  .strictK (.convert (.int .int32)) [] [] btEnv2 (btRuneK ov)
def btA97K (ov : GoString) : Cont :=
  .strictK .add [.int 97 .uint64] [] btEnv2 (btConvK ov)
/-- The letter `%` apply point: divisor delivered, the wrapped
`seed+i` sum banked. -/
def btModK (ov : GoString) (x : Int) : Cont :=
  .strictK .mod [.int x .uint64] [] btEnv2 (btA97K ov)

/-- The separator arm statements (named for the `ifK`s). -/
def btArm0 : Stmt :=
  .block #[]
    #[.assign (.var "out")
        (.add (.var "out") (.stringLit { bytes := #[32] }))]
def btArm1 : Stmt :=
  .block #[]
    #[.assign (.var "out")
        (.add (.var "out") (.stringLit { bytes := #[32, 32] }))]
def btArm2 : Stmt :=
  .block #[]
    #[.assign (.var "out")
        (.add (.var "out") (.stringLit { bytes := #[9] }))]
def btSepIf1 : Stmt :=
  .ifThenElse
    (.eqCmp tU64 (.mod (.var "i") (.intLit 3 .uint64))
      (.intLit 1 .uint64))
    btArm1 btArm2

/-- The separator-if tail (shared by both `ifK`s). -/
def btSepTail : Cont := .seq [] btEnv2 (.seq [] btEnvC btLoopK)
def btSepIf0K : Cont := .ifK btArm0 btSepIf1 btEnv2 btSepTail
def btSepEq0K : Cont :=
  .strictK (.eqCmp tU64) [] [.intLit 0 .uint64] btEnv2 btSepIf0K
/-- The separator `%` apply point (first test), `i` banked. -/
def btSepModK (x : Int) : Cont := .strictK .mod [.int x .uint64] [] btEnv2 btSepEq0K
def btSepIf1K : Cont := .ifK btArm1 btArm2 btEnv2 btSepTail
def btSepEq1K : Cont :=
  .strictK (.eqCmp tU64) [] [.intLit 1 .uint64] btEnv2 btSepIf1K
/-- The separator `%` apply point (second test), `i` banked. -/
def btSepMod1K (x : Int) : Cont :=
  .strictK .mod [.int x .uint64] [] btEnv2 btSepEq1K

/-! ## Continuations — the `q` computation and the `wordFreq` call -/

def qStTail : Cont :=
  .seq [wordfreqHarnessRFunc.hS3, wordfreqHarnessRFunc.hS4] hEnv2 frameStop
def qRhsK : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨14⟩)) [] []] [] [] (.seqn #[]) hEnv2
    qStTail
def qRuneK : Cont := .strictK .stringFromRune [] [] hEnv2 qRhsK
def qConvK : Cont := .strictK (.convert (.int .int32)) [] [] hEnv2 qRuneK
def qA97K : Cont := .strictK .add [.int 97 .uint64] [] hEnv2 qConvK
/-- The `qsel % 3` apply point. -/
def qModK (x : Int) : Cont := .strictK .mod [.int x .uint64] [] hEnv2 qA97K

/-- The shim call's argument point inside `wordFreq`. -/
def shimCallK0 : Cont :=
  .callArgsK ⟨"goleanShimStringsFields"⟩ shimShapes [] [] wfEnvW wfAfterShim

/-! ## Raw segments — PROGRAM-generic throughout -/

/-- Entry: body start → the `buildText` call's second argument
delivered. 10 steps. -/
theorem s_E1_raw (σ : ExecState) (nv sv qv : Int) (ch : Choices) :
    stepFnIter 10 (wSt σ (wHeap0 nv sv qv) 7) sHC0 ch
      = .ok (.retV (.int sv .uint64) (btCallK1 nv),
          wSt σ (wHeapPre nv sv qv) 8, ch) := by
  with_unfolding_all rfl

/-- The `buildText` frame prologue: `out := " "`, `i := 0`, the
first-pass flag → the loop head. 43 steps. -/
theorem bt_pro_raw (σ : ExecState) (nv sv qv bnv bsv : Int) (ch : Choices) :
    stepFnIter 43 (wSt σ (wHeapBF nv sv qv bnv bsv) 11)
      (.exec buildTextFunc.body btFrameEnv btFrameK) ch
      = .ok (btHeadCfg,
          wSt σ (wHeapBt nv sv qv bnv bsv (gs [32]) 0 true) 14, ch) := by
  with_unfolding_all rfl

/-- Build dispatch, first pass: flag true → the exit test delivered.
25 steps. -/
theorem bt_A0_raw (σ : ExecState) (nv sv qv bnv bsv : Int) (ov : GoString)
    (iv : Int) (ch : Choices) :
    stepFnIter 25 (wSt σ (wHeapBt nv sv qv bnv bsv ov iv true) 14)
      btHeadCfg ch
      = .ok (.retV (.bool (decide (iv < bnv))) btCmpK,
          wSt σ (wHeapBt nv sv qv bnv bsv ov iv false) 14, ch) := by
  with_unfolding_all rfl

/-- Build dispatch, later passes: `i++`, exit test delivered. 29
steps. -/
theorem bt_A1_raw (σ : ExecState) (nv sv qv bnv bsv : Int) (ov : GoString)
    (iv : Int) (ch : Choices) :
    stepFnIter 29 (wSt σ (wHeapBt nv sv qv bnv bsv ov iv false) 14)
      btHeadCfg ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < bnv))) btCmpK,
          wSt σ (wHeapBt nv sv qv bnv bsv ov
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false) 14, ch) := by
  with_unfolding_all rfl

/-- Build body A: test true → the letter `%` apply point (the wrapped
`seed+i` sum banked, the divisor delivered). 24 steps. -/
theorem bt_B1_raw (σ : ExecState) (nv sv qv bnv bsv : Int) (ov : GoString)
    (iv : Int) (ch : Choices) :
    stepFnIter 24 (wSt σ (wHeapBt nv sv qv bnv bsv ov iv false) 14)
      (.retV (.bool true) btCmpK) ch
      = .ok (.retV (.int 3 .uint64)
            (btModK ov (IntKind.normalize .uint64 (bsv + iv))),
          wSt σ (wHeapBt nv sv qv bnv bsv ov iv false) 14, ch) := by
  with_unfolding_all rfl

/-- Build body B: the `%` result delivered → `97 + r`, the `rune`
conversion → the `string(rune(·))` apply point. 2 steps. -/
theorem bt_B2_raw (σ : ExecState) (nv sv qv bnv bsv : Int) (ov : GoString)
    (iv rv : Int) (ch : Choices) :
    stepFnIter 2 (wSt σ (wHeapBt nv sv qv bnv bsv ov iv false) 14)
      (.retV (.int rv .uint64) (btA97K ov)) ch
      = .ok (.retV (.int (IntKind.normalize .int32
              (IntKind.normalize .uint64 (97 + rv))) .int32) (btRuneK ov),
          wSt σ (wHeapBt nv sv qv bnv bsv ov iv false) 14, ch) := by
  with_unfolding_all rfl

/-- Build body C: the one-byte string delivered → the append, the
store, and the separator `if`'s first `%` apply point. 12 steps. -/
theorem bt_B3_raw (σ : ExecState) (nv sv qv bnv bsv : Int) (ov w : GoString)
    (iv : Int) (ch : Choices) :
    stepFnIter 12 (wSt σ (wHeapBt nv sv qv bnv bsv ov iv false) 14)
      (.retV (.string w) (btAppK ov)) ch
      = .ok (.retV (.int 3 .uint64) (btSepModK iv),
          wSt σ (wHeapBt nv sv qv bnv bsv (GoString.append ov w) iv false)
            14, ch) := by
  with_unfolding_all rfl

/-- Separator test 1: the `i % 3` result delivered → the `== 0`
verdict. 3 steps. -/
theorem bt_S1_raw (σ : ExecState) (nv sv qv bnv bsv : Int) (ov : GoString)
    (iv rv : Int) (ch : Choices) :
    stepFnIter 3 (wSt σ (wHeapBt nv sv qv bnv bsv ov iv false) 14)
      (.retV (.int rv .uint64) btSepEq0K) ch
      = .ok (.retV (.bool (rv == 0)) btSepIf0K,
          wSt σ (wHeapBt nv sv qv bnv bsv ov iv false) 14, ch) := by
  with_unfolding_all rfl

/-- Separator arm `" "`: verdict true → append, store, loop head. 19
steps. -/
theorem bt_arm0_raw (σ : ExecState) (nv sv qv bnv bsv : Int) (ov : GoString)
    (iv : Int) (ch : Choices) :
    stepFnIter 19 (wSt σ (wHeapBt nv sv qv bnv bsv ov iv false) 14)
      (.retV (.bool true) btSepIf0K) ch
      = .ok (btHeadCfg,
          wSt σ (wHeapBt nv sv qv bnv bsv
            (GoString.append ov (gs [32])) iv false) 14, ch) := by
  with_unfolding_all rfl

/-- Separator test 2: verdict-1 false → the second `%` apply point.
7 steps. -/
theorem bt_S2_raw (σ : ExecState) (nv sv qv bnv bsv : Int) (ov : GoString)
    (iv : Int) (ch : Choices) :
    stepFnIter 7 (wSt σ (wHeapBt nv sv qv bnv bsv ov iv false) 14)
      (.retV (.bool false) btSepIf0K) ch
      = .ok (.retV (.int 3 .uint64) (btSepMod1K iv),
          wSt σ (wHeapBt nv sv qv bnv bsv ov iv false) 14, ch) := by
  with_unfolding_all rfl

/-- Separator test 2, verdict: the `i % 3` result delivered → the
`== 1` verdict. 3 steps. -/
theorem bt_S3_raw (σ : ExecState) (nv sv qv bnv bsv : Int) (ov : GoString)
    (iv rv : Int) (ch : Choices) :
    stepFnIter 3 (wSt σ (wHeapBt nv sv qv bnv bsv ov iv false) 14)
      (.retV (.int rv .uint64) btSepEq1K) ch
      = .ok (.retV (.bool (rv == 1)) btSepIf1K,
          wSt σ (wHeapBt nv sv qv bnv bsv ov iv false) 14, ch) := by
  with_unfolding_all rfl

/-- Separator arm `"  "`: verdict true → append, store, loop head. 19
steps. -/
theorem bt_arm1_raw (σ : ExecState) (nv sv qv bnv bsv : Int) (ov : GoString)
    (iv : Int) (ch : Choices) :
    stepFnIter 19 (wSt σ (wHeapBt nv sv qv bnv bsv ov iv false) 14)
      (.retV (.bool true) btSepIf1K) ch
      = .ok (btHeadCfg,
          wSt σ (wHeapBt nv sv qv bnv bsv
            (GoString.append ov (gs [32, 32])) iv false) 14, ch) := by
  with_unfolding_all rfl

/-- Separator arm `"\t"`: verdict-2 false → append, store, loop head.
19 steps. -/
theorem bt_arm2_raw (σ : ExecState) (nv sv qv bnv bsv : Int) (ov : GoString)
    (iv : Int) (ch : Choices) :
    stepFnIter 19 (wSt σ (wHeapBt nv sv qv bnv bsv ov iv false) 14)
      (.retV (.bool false) btSepIf1K) ch
      = .ok (btHeadCfg,
          wSt σ (wHeapBt nv sv qv bnv bsv
            (GoString.append ov (gs [9])) iv false) 14, ch) := by
  with_unfolding_all rfl

/-- Build exit A: test false → break, `$res0 := out`, the frame pop
into `pre`, `var q`, and the `qsel % 3` apply point. 43 steps. -/
theorem bt_X1_raw (σ : ExecState) (nv sv qv bnv bsv : Int) (l : List UInt8)
    (iv : Int) (ch : Choices) :
    stepFnIter 43 (wSt σ (wHeapBt nv sv qv bnv bsv (gs l) iv false) 14)
      (.retV (.bool false) btCmpK) ch
      = .ok (.retV (.int 3 .uint64) (qModK qv),
          wSt σ (wHeapBX nv sv qv bnv bsv l iv) 15, ch) := by
  with_unfolding_all rfl

/-- Build exit B: the `qsel % 3` result delivered → `97 + r`, the
`rune` conversion → the `string(rune(·))` apply point. 2 steps. -/
theorem bt_X2_raw (σ : ExecState) (nv sv qv bnv bsv : Int) (l : List UInt8)
    (iv rv : Int) (ch : Choices) :
    stepFnIter 2 (wSt σ (wHeapBX nv sv qv bnv bsv l iv) 15)
      (.retV (.int rv .uint64) qA97K) ch
      = .ok (.retV (.int (IntKind.normalize .int32
              (IntKind.normalize .uint64 (97 + rv))) .int32) qRuneK,
          wSt σ (wHeapBX nv sv qv bnv bsv l iv) 15, ch) := by
  with_unfolding_all rfl

/-- Build exit C: the query string delivered → the `q` store,
`var hits`, `var best`, and the `wordFreq(pre, q)` second argument
delivered. 15 steps. -/
theorem bt_X3_raw (σ : ExecState) (nv sv qv bnv bsv : Int)
    (l q : List UInt8) (iv : Int) (ch : Choices) :
    stepFnIter 15 (wSt σ (wHeapBX nv sv qv bnv bsv l iv) 15)
      (.retV (.string (gs q)) qRhsK) ch
      = .ok (.retV (.string (gs q)) (wfCallK1 l),
          wSt σ (wHeapCall nv sv qv bnv bsv l q iv) 17, ch) := by
  with_unfolding_all rfl

/-! ## One iteration, cleaned (three separator arms) -/

/-- One build iteration from the exit test's true delivery at `i`:
within 103 steps the next family block (letter + separator)
materializes. -/
theorem bt_iter (σ : ExecState) (qv : Int) (n seed : Nat)
    (hn : n < 2 ^ 61) (hseed : seed < 2 ^ 64) (i : Nat) (hi : i < n)
    (ch : Choices) :
    ∃ k : Nat, k ≤ 103 ∧
    stepFnIter k
      (wSt σ (wHeapBt ((n : Nat) : Int) ((seed : Nat) : Int) qv
        ((n : Nat) : Int) ((seed : Nat) : Int)
        (gs (textFamily i seed)) ((i : Nat) : Int) false) 14)
      (.retV (.bool true) btCmpK) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) btCmpK,
          wSt σ (wHeapBt ((n : Nat) : Int) ((seed : Nat) : Int) qv
            ((n : Nat) : Int) ((seed : Nat) : Int)
            (gs (textFamily (i + 1) seed)) ((i + 1 : Nat) : Int) false) 14,
          ch) := by
  -- the letter store
  have hB1 := bt_B1_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) qv
    ((n : Nat) : Int) ((seed : Nat) : Int) (gs (textFamily i seed))
    ((i : Nat) : Int) ch
  rw [unorm_add_nat seed i] at hB1
  have hmod := stepFnIter_one (stepFn_strict_apply
    (done := [.int (((seed + i) % 2 ^ 64 : Nat) : Int) .uint64])
    (env := btEnv2) (k := btA97K (gs (textFamily i seed))) (ch := ch)
    (applyStrictOp_mod_u64
      (σ := wSt σ (wHeapBt ((n : Nat) : Int) ((seed : Nat) : Int) qv
        ((n : Nat) : Int) ((seed : Nat) : Int) (gs (textFamily i seed))
        ((i : Nat) : Int) false) 14)
      (a := (seed + i) % 2 ^ 64) (b := 3) (by omega) (by omega)))
  have hB2 := bt_B2_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) qv
    ((n : Nat) : Int) ((seed : Nat) : Int) (gs (textFamily i seed))
    ((i : Nat) : Int) ((((seed + i) % 2 ^ 64) % 3 : Nat) : Int) ch
  have hbyte : 97 + ((seed + i) % 2 ^ 64) % 3 < 128 := by
    have := Nat.mod_lt ((seed + i) % 2 ^ 64) (show 0 < 3 by omega)
    omega
  rw [show (97 : Int) + ((((seed + i) % 2 ^ 64) % 3 : Nat) : Int)
        = ((97 + ((seed + i) % 2 ^ 64) % 3 : Nat) : Int) from by omega,
    unorm_nat_of_lt (by omega : 97 + ((seed + i) % 2 ^ 64) % 3 < 2 ^ 64),
    i32norm_nat_of_lt (by omega : 97 + ((seed + i) % 2 ^ 64) % 3 < 2 ^ 31)]
    at hB2
  have hrune := stepFnIter_one (stepFn_strict_apply
    (done := []) (env := btEnv2)
    (k := btAppK (gs (textFamily i seed))) (ch := ch)
    (applyStrictOp_stringFromRune_ascii
      (σ := wSt σ (wHeapBt ((n : Nat) : Int) ((seed : Nat) : Int) qv
        ((n : Nat) : Int) ((seed : Nat) : Int) (gs (textFamily i seed))
        ((i : Nat) : Int) false) 14)
      (c := 97 + ((seed + i) % 2 ^ 64) % 3) (ik := .int32) hbyte))
  have hB3 := bt_B3_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) qv
    ((n : Nat) : Int) ((seed : Nat) : Int) (gs (textFamily i seed))
    (gs [UInt8.ofNat (97 + ((seed + i) % 2 ^ 64) % 3)])
    ((i : Nat) : Int) ch
  rw [gs_append,
    show textFamily i seed ++ [UInt8.ofNat (97 + ((seed + i) % 2 ^ 64) % 3)]
        = textFamily i seed ++ [letterByte seed i] from by
      simp [letterByte]] at hB3
  -- the separator % (i % 3, no wrap: i < 2^61)
  have hsmod := stepFnIter_one (stepFn_strict_apply
    (done := [.int ((i : Nat) : Int) .uint64])
    (env := btEnv2) (k := btSepEq0K) (ch := ch)
    (applyStrictOp_mod_u64
      (σ := wSt σ (wHeapBt ((n : Nat) : Int) ((seed : Nat) : Int) qv
        ((n : Nat) : Int) ((seed : Nat) : Int)
        (gs (textFamily i seed ++ [letterByte seed i]))
        ((i : Nat) : Int) false) 14)
      (a := i) (b := 3) (by omega) (by omega)))
  have hS1 := bt_S1_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) qv
    ((n : Nat) : Int) ((seed : Nat) : Int)
    (gs (textFamily i seed ++ [letterByte seed i]))
    ((i : Nat) : Int) (((i % 3 : Nat) : Int)) ch
  have hpre := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hB1 hmod) hB2)
      hrune) hB3) hsmod) hS1
  -- the separator arm, by `i % 3`
  have harm : ∃ karm : Nat, karm ≤ 30 ∧
      stepFnIter karm
        (wSt σ (wHeapBt ((n : Nat) : Int) ((seed : Nat) : Int) qv
          ((n : Nat) : Int) ((seed : Nat) : Int)
          (gs (textFamily i seed ++ [letterByte seed i]))
          ((i : Nat) : Int) false) 14)
        (.retV (.bool (((i % 3 : Nat) : Int) == 0)) btSepIf0K) ch
        = .ok (btHeadCfg,
            wSt σ (wHeapBt ((n : Nat) : Int) ((seed : Nat) : Int) qv
              ((n : Nat) : Int) ((seed : Nat) : Int)
              (gs (textFamily (i + 1) seed)) ((i : Nat) : Int) false) 14,
            ch) := by
    have hstep := textFamily_succ i seed
    have h3cases : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases h3cases with h3 | h3 | h3
    · -- " "
      refine ⟨19, by omega, ?_⟩
      rw [show ((((i % 3 : Nat) : Int)) == 0) = true from by
        rw [h3]; rfl]
      have h := bt_arm0_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) qv
        ((n : Nat) : Int) ((seed : Nat) : Int)
        (gs (textFamily i seed ++ [letterByte seed i]))
        ((i : Nat) : Int) ch
      rw [gs_append, List.append_assoc,
        show [letterByte seed i] ++ [32] = letterByte seed i :: sepBytes i
          from by simp [sepBytes, h3], ← hstep] at h
      exact h
    · -- "  "
      rw [show ((((i % 3 : Nat) : Int)) == 0) = false from by
        rw [h3]; rfl]
      have hS2 := bt_S2_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) qv
        ((n : Nat) : Int) ((seed : Nat) : Int)
        (gs (textFamily i seed ++ [letterByte seed i]))
        ((i : Nat) : Int) ch
      have hmod2 := stepFnIter_one (stepFn_strict_apply
        (done := [.int ((i : Nat) : Int) .uint64])
        (env := btEnv2) (k := btSepEq1K) (ch := ch)
        (applyStrictOp_mod_u64
          (σ := wSt σ (wHeapBt ((n : Nat) : Int) ((seed : Nat) : Int) qv
            ((n : Nat) : Int) ((seed : Nat) : Int)
            (gs (textFamily i seed ++ [letterByte seed i]))
            ((i : Nat) : Int) false) 14)
          (a := i) (b := 3) (by omega) (by omega)))
      have hS3 := bt_S3_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) qv
        ((n : Nat) : Int) ((seed : Nat) : Int)
        (gs (textFamily i seed ++ [letterByte seed i]))
        ((i : Nat) : Int) (((i % 3 : Nat) : Int)) ch
      rw [show ((((i % 3 : Nat) : Int)) == 1) = true from by
        rw [h3]; rfl] at hS3
      have h := bt_arm1_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) qv
        ((n : Nat) : Int) ((seed : Nat) : Int)
        (gs (textFamily i seed ++ [letterByte seed i]))
        ((i : Nat) : Int) ch
      rw [gs_append, List.append_assoc,
        show [letterByte seed i] ++ [32, 32]
            = letterByte seed i :: sepBytes i from by
          simp [sepBytes, h3], ← hstep] at h
      exact ⟨7 + 1 + 3 + 19, by omega,
        stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hS2 hmod2)
          hS3) h⟩
    · -- "\t"
      rw [show ((((i % 3 : Nat) : Int)) == 0) = false from by
        rw [h3]; rfl]
      have hS2 := bt_S2_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) qv
        ((n : Nat) : Int) ((seed : Nat) : Int)
        (gs (textFamily i seed ++ [letterByte seed i]))
        ((i : Nat) : Int) ch
      have hmod2 := stepFnIter_one (stepFn_strict_apply
        (done := [.int ((i : Nat) : Int) .uint64])
        (env := btEnv2) (k := btSepEq1K) (ch := ch)
        (applyStrictOp_mod_u64
          (σ := wSt σ (wHeapBt ((n : Nat) : Int) ((seed : Nat) : Int) qv
            ((n : Nat) : Int) ((seed : Nat) : Int)
            (gs (textFamily i seed ++ [letterByte seed i]))
            ((i : Nat) : Int) false) 14)
          (a := i) (b := 3) (by omega) (by omega)))
      have hS3 := bt_S3_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) qv
        ((n : Nat) : Int) ((seed : Nat) : Int)
        (gs (textFamily i seed ++ [letterByte seed i]))
        ((i : Nat) : Int) (((i % 3 : Nat) : Int)) ch
      rw [show ((((i % 3 : Nat) : Int)) == 1) = false from by
        rw [h3]; rfl] at hS3
      have h := bt_arm2_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) qv
        ((n : Nat) : Int) ((seed : Nat) : Int)
        (gs (textFamily i seed ++ [letterByte seed i]))
        ((i : Nat) : Int) ch
      rw [gs_append, List.append_assoc,
        show [letterByte seed i] ++ [9]
            = letterByte seed i :: sepBytes i from by
          simp [sepBytes, h3], ← hstep] at h
      exact ⟨7 + 1 + 3 + 19, by omega,
        stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hS2 hmod2)
          hS3) h⟩
  obtain ⟨karm, hkarm, harm⟩ := harm
  -- the next dispatch
  have hA1 := bt_A1_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) qv
    ((n : Nat) : Int) ((seed : Nat) : Int) (gs (textFamily (i + 1) seed))
    ((i : Nat) : Int) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    unorm_nat_of_lt (by omega : i + 1 < 2 ^ 64),
    unorm_nat_of_lt (by omega : i + 1 < 2 ^ 64)] at hA1
  exact ⟨24 + 1 + 2 + 1 + 12 + 1 + 3 + karm + 29, by omega,
    stepFnIter_chain (stepFnIter_chain hpre harm) hA1⟩

/-! ## The loop (`∃ k` accounting: the arm shapes differ) -/

/-- **The build loop**: within `103·(n−i)` steps the family
materializes. -/
theorem bt_loop (σ : ExecState) (qv : Int) (n seed : Nat)
    (hn : n < 2 ^ 61) (hseed : seed < 2 ^ 64) :
    ∀ m i : Nat, m = n - i → i ≤ n → ∀ ch : Choices,
    ∃ k : Nat, k ≤ 103 * m ∧
    stepFnIter k
      (wSt σ (wHeapBt ((n : Nat) : Int) ((seed : Nat) : Int) qv
        ((n : Nat) : Int) ((seed : Nat) : Int)
        (gs (textFamily i seed)) ((i : Nat) : Int) false) 14)
      (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
        btCmpK) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) btCmpK,
          wSt σ (wHeapBt ((n : Nat) : Int) ((seed : Nat) : Int) qv
            ((n : Nat) : Int) ((seed : Nat) : Int)
            (gs (textFamily n seed)) ((n : Nat) : Int) false) 14, ch) := by
  intro m
  induction m with
  | zero =>
      intro i hm hi ch
      have : i = n := by omega
      subst this
      exact ⟨0, by omega, rfl⟩
  | succ m ih =>
      intro i hm hi ch
      have hilt : i < n := by omega
      rw [show (decide (((i : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hilt)]
      obtain ⟨k₁, hk₁, h₁⟩ := bt_iter σ qv n seed hn hseed i hilt ch
      obtain ⟨k₂, hk₂, h₂⟩ := ih (i + 1) (by omega) (by omega) ch
      exact ⟨k₁ + k₂, by omega, stepFnIter_chain h₁ h₂⟩

/-! ## The phase, assembled: entry → the `wordFreq` frame entry point -/

/-- **The build phase**: within `103·n + 141` steps from the
post-prelude seed, the run delivers the `wordFreq(pre, q)` call's
second argument with `pre = textFamily n seed` and `q = qWord qsel`
materialized. -/
theorem build_phase (n seed qsel : Nat)
    (hn : n < 2 ^ 61) (hseed : seed < 2 ^ 64) (hqsel : qsel < 2 ^ 64)
    (ch : Choices) :
    ∃ k : Nat, k ≤ 103 * n + 141 ∧
    stepFnIter k
      (wSt sProg (wHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)
        ((qsel : Nat) : Int)) 7) sHC0 ch
      = .ok (.retV (.string (gs (qWord qsel)))
            (wfCallK1 (textFamily n seed)),
          wSt sProg (wHeapCall ((n : Nat) : Int) ((seed : Nat) : Int)
            ((qsel : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int)
            (textFamily n seed) (qWord qsel) ((n : Nat) : Int)) 17,
          ch) := by
  have hE1 := s_E1_raw sProg ((n : Nat) : Int) ((seed : Nat) : Int)
    ((qsel : Nat) : Int) ch
  have hent := stepFnIter_one (ch := ch)
    (stepFn_call_enter (plans := btShapes) (env := hEnv1) (k := hAfterBt)
      (vals := [.int ((n : Nat) : Int) .uint64])
      (v := .int ((seed : Nat) : Int) .uint64)
      (bt_enterFrame_fact ((n : Nat) : Int) ((seed : Nat) : Int)
        ((qsel : Nat) : Int) (unorm_nat_of_lt (by omega))
        (unorm_nat_of_lt hseed)))
  have hpro := bt_pro_raw sProg ((n : Nat) : Int) ((seed : Nat) : Int)
    ((qsel : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int) ch
  have hA0 := bt_A0_raw sProg ((n : Nat) : Int) ((seed : Nat) : Int)
    ((qsel : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int)
    (gs [32]) 0 ch
  obtain ⟨kL, hkL, hLoop⟩ := bt_loop sProg ((qsel : Nat) : Int) n seed hn
    hseed n 0 (by omega) (by omega) ch
  rw [show gs (textFamily 0 seed) = gs [32] from by rw [textFamily_zero],
    show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hLoop
  have h1 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hE1 hent) hpro) hA0) hLoop
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at h1
  -- the exit through q
  have hX1 := bt_X1_raw sProg ((n : Nat) : Int) ((seed : Nat) : Int)
    ((qsel : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int)
    (textFamily n seed) ((n : Nat) : Int) ch
  have hqmod := stepFnIter_one (stepFn_strict_apply
    (done := [.int ((qsel : Nat) : Int) .uint64])
    (env := hEnv2) (k := qA97K) (ch := ch)
    (applyStrictOp_mod_u64
      (σ := wSt sProg (wHeapBX ((n : Nat) : Int) ((seed : Nat) : Int)
        ((qsel : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int)
        (textFamily n seed) ((n : Nat) : Int)) 15)
      (a := qsel) (b := 3) (by omega) (by omega)))
  have hX2 := bt_X2_raw sProg ((n : Nat) : Int) ((seed : Nat) : Int)
    ((qsel : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int)
    (textFamily n seed) ((n : Nat) : Int) (((qsel % 3 : Nat) : Int)) ch
  have hq128 : 97 + qsel % 3 < 128 := by
    have := Nat.mod_lt qsel (show 0 < 3 by omega)
    omega
  rw [show (97 : Int) + (((qsel % 3 : Nat) : Int))
        = ((97 + qsel % 3 : Nat) : Int) from by omega,
    unorm_nat_of_lt (by omega : 97 + qsel % 3 < 2 ^ 64),
    i32norm_nat_of_lt (by omega : 97 + qsel % 3 < 2 ^ 31)] at hX2
  have hsfr := stepFnIter_one (stepFn_strict_apply
    (done := []) (env := hEnv2) (k := qRhsK) (ch := ch)
    (applyStrictOp_stringFromRune_ascii
      (σ := wSt sProg (wHeapBX ((n : Nat) : Int) ((seed : Nat) : Int)
        ((qsel : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int)
        (textFamily n seed) ((n : Nat) : Int)) 15)
      (c := 97 + qsel % 3) (ik := .int32) hq128))
  have hX3 := bt_X3_raw sProg ((n : Nat) : Int) ((seed : Nat) : Int)
    ((qsel : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int)
    (textFamily n seed) [UInt8.ofNat (97 + qsel % 3)]
    ((n : Nat) : Int) ch
  have h2 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain h1 hX1) hqmod) hX2) hsfr) hX3
  rw [show [UInt8.ofNat (97 + qsel % 3)] = qWord qsel from by
    simp [qWord]] at h2
  exact ⟨10 + 1 + 43 + 25 + kL + 43 + 1 + 2 + 1 + 15, by omega, h2⟩

end GoLean.Examples.WordFreq
