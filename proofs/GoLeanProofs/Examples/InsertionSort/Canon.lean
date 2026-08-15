import GoLeanProofs.Examples.InsertionSortProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Examples.InsertionSort.Pure

/-!
# InsertionSort — Canon

Per-phase shard of `GoLeanProofs.Examples.InsertionSort` (examples
phase-2 slice 0, lever 2, 2026-08-14). Every statement and proof here
is BYTE-IDENTICAL to the pre-split module; only file placement changed,
so Lake's module-level caching can see the phases separately. The
user-facing headline theorems live in the thin root module
`GoLeanProofs.Examples.InsertionSort`, whose docstring records the
example's design and the shard map.
-/

namespace GoLean.Examples.InsertionSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-! ## The machine layer: canonical-placement configurations

Transcribed from the machine (probe-verified against concrete runs;
every raw segment below re-checks the transcription by `rfl`).
Canonical address layout: 0 = the backing array, 1 = the parameter `s`
(the handle), 2 = `i`, 3 = the OUTER `$forFirst`; the pass-local cells
4 = `j`, 5 = the INNER `$forFirst` exist only inside a pass at the
tight placement (the true run re-allocates them per pass at moving
addresses — the frame-rebase layer below carries that). -/

abbrev intcell (v : Int) : HeapCell := ⟨some (.int .int), .int v .int⟩
abbrev bcell (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
abbrev arrCell (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n (.int .uint64)), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev handleCell (n : Nat) : HeapCell :=
  ⟨some (.slice (.int .uint64)), .slice ⟨some (.base ⟨0⟩), 0, n, n⟩⟩
abbrev sliceH (n : Nat) : GoValue :=
  .slice ⟨some (.base ⟨0⟩), 0, n, n⟩

def envO : LocalEnv :=
  [[("$forFirst", .base ⟨3⟩)], [("i", .base ⟨2⟩)], [], [("s", .base ⟨1⟩)]]
private def envOMid : LocalEnv := [[("i", .base ⟨2⟩)], [], [("s", .base ⟨1⟩)]]
private def envOOut : LocalEnv := [[], [("s", .base ⟨1⟩)]]

private def headTailO : Cont :=
  .seq [] envO (.seq [] envOMid (.seq [] envOOut
    (.frame [] [] [] [] .stop false)))
/-- The OUTER loop-head configuration. -/
private def outerHeadCfg : Config :=
  .exec (.while (.boolLit true) outerWhileBody) envO headTailO
private def loopKO : Cont := .loop (.boolLit true) outerWhileBody envO headTailO
/-- The outer exit test's delivery continuation. -/
def outerCmpCont : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envO)
    (.seq [innerForBlock] ([] :: envO) loopKO)
/-- The `len(s)` apply point inside the outer test, carrying the
already-evaluated `i` operand. -/
def lenTestK (iv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice (.int .uint64)))) [] [] ([] :: envO)
    (.strictK .lessCmp [.int iv .int] [] ([] :: envO) outerCmpCont)

def envI : LocalEnv :=
  [("$forFirst", .base ⟨5⟩)] :: [("j", .base ⟨4⟩)] :: [] :: [] :: envO
private def innerTail : Cont :=
  .seq [] envI
    (.seq [] ([("j", .base ⟨4⟩)] :: [] :: [] :: envO)
      (.seq [] ([] :: [] :: envO)
        (.seq [] ([] :: envO) loopKO)))
/-- The INNER loop-head configuration (tight placement). -/
private def innerHeadCfg : Config :=
  .exec (.while (.boolLit true) innerWhileBody) envI innerTail
private def loopKI : Cont := .loop (.boolLit true) innerWhileBody envI innerTail
/-- The inner test's `if` delivery continuation. -/
def innerIfK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envI)
    (.seq [isortSwapBlock] ([] :: envI) loopKI)
/-- The short-circuit `&&` continuation: first conjunct delivers HERE;
`false` skips the index reads entirely (Go's laziness — load-bearing at
`j = 0`). -/
private def andKCont : Cont :=
  .andK (.greaterCmp
      (.indexGet (.var "s") (.sub (.var "j") (.intLit 1 .int)))
      (.indexGet (.var "s") (.var "j")))
    ([] :: envI) innerIfK
/-- The second conjunct's spine: first index read pending the second. -/
private def gcK1 : Cont :=
  .strictK .greaterCmp [] [.indexGet (.var "s") (.var "j")] ([] :: envI)
    (.boolK innerIfK)
private def gcK2 (w1 : GoValue) : Cont :=
  .strictK .greaterCmp [w1] [] ([] :: envI) (.boolK innerIfK)

private def envSw : LocalEnv := [] :: [] :: envI
def swTail : Cont :=
  .seq [] envSw (.seq [] ([] :: envI) loopKI)
private def refj (n : Nat) (idx : Int) : TargetRef :=
  .chain (sliceH n) [.int idx .int] [.index]
def rhsK1 (n : Nat) (idx1 jv : Int) : Cont :=
  .rhsK .vals [refj n idx1, refj n jv] []
    [.indexGet (.var "s") (.sub (.var "j") (.intLit 1 .int))]
    (.seqn #[]) envSw swTail
def rhsK2 (n : Nat) (idx1 jv : Int) (wj : GoValue) : Cont :=
  .rhsK .vals [refj n idx1, refj n jv] [wj] [] (.seqn #[]) envSw swTail

/-- The outer-head state family, TAIL-PARAMETRIC: the four active cells
in front, an arbitrary inert tail behind (the raw dispatch/exit
segments never touch past cell 3, so one segment statement serves both
the tight 4-cell state and the post-pass 6-cell state). -/
def σOutT (n : Nat) (l : List Int) (iv : Int) (ffv : Bool)
    (tail : Heap) (na : Nat) : ExecState :=
  { types := isortLowered.typeDefs.toList,
    functions := isortLowered.funcs,
    methods := isortLowered.methods,
    heap := (.base ⟨0⟩, arrCell n l) :: (.base ⟨1⟩, handleCell n)
      :: (.base ⟨2⟩, intcell iv) :: (.base ⟨3⟩, bcell ffv) :: tail,
    nextAddr := na }

/-- The tight 4-cell outer state (canonical pass placement). -/
def σOut (n : Nat) (l : List Int) (iv : Int) (ffv : Bool) :
    ExecState :=
  σOutT n l iv ffv [] 4

/-- The tight 6-cell in-pass state: `j` at 4, inner `$forFirst` at 5.
The outer `$forFirst` is `false` throughout a pass. -/
def σIn (n : Nat) (l : List Int) (iv jv : Int) (ffIv : Bool) :
    ExecState :=
  σOutT n l iv false [(.base ⟨4⟩, intcell jv), (.base ⟨5⟩, bcell ffIv)] 6

/-! ## Raw run segments (`with_unfolding_all rfl`) -/

def entryK : Cont := .callArgsK ⟨"insertionSort"⟩ [] [] [] [] .stop

/-- Entry A: driver start → the slice-expression apply point. -/
theorem isort_entryA_raw (xs : List Int) (ch : Choices) :
    stepFnIter 7 (isortSeed xs 0 [] 1) (.exec (isortCall xs 0) [] .stop) ch
      = .ok (.retV (.int (IntKind.normalize .int (xs.length : Int)) .int)
            (.strictK (.sliceExpr false) [.int 0 .int, .addr (.base ⟨0⟩)]
              [] [] entryK),
          isortSeed xs 0 [] 1, ch) := by
  with_unfolding_all rfl

/-- Entry B: frame entry, `i := 1`, the `$forFirst` block → the outer
loop head at the tight 4-cell state. -/
theorem isort_entryB_raw (xs : List Int) (ch : Choices) :
    stepFnIter 31 (isortSeed xs 0 [] 1) (.retV (sliceH xs.length) entryK) ch
      = .ok (outerHeadCfg, σOut xs.length xs 1 true, ch) := by
  with_unfolding_all rfl

/-- First-pass outer dispatch: head with the flag up → the `len(s)`
apply point of the exit test (`i` unchanged, flag lowered). TAIL-
PARAMETRIC: touches only cells 0–3. -/
theorem isort_segO0_raw (n : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 25 (σOutT n l iv true tail na) outerHeadCfg ch
      = .ok (.retV (sliceH n) (lenTestK iv),
          σOutT n l iv false tail na, ch) := by
  with_unfolding_all rfl

/-- Later-pass outer dispatch: head with the flag down → `i := i + 1`,
then the `len(s)` apply point. -/
private theorem isort_segO1_raw (n : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 29 (σOutT n l iv false tail na) outerHeadCfg ch
      = .ok (.retV (sliceH n)
            (lenTestK (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
          σOutT n l (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            false tail na, ch) := by
  with_unfolding_all rfl

/-- The outer comparison delivered: `len` value in → the test bool at
the `if` continuation. -/
theorem isort_segOB_raw (n : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 1 (σOutT n l iv false tail na)
      (.retV (.int ((n : Nat) : Int) .int)
        (.strictK .lessCmp [.int iv .int] [] ([] :: envO) outerCmpCont)) ch
      = .ok (.retV (.bool (decide (iv < ((n : Nat) : Int)))) outerCmpCont,
          σOutT n l iv false tail na, ch) := by
  with_unfolding_all rfl

/-- Outer exit: test false → break unwinding, frame exit, the driver
terminal. The state is untouched. -/
theorem isort_exitO_raw (n : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 8 (σOutT n l iv false tail na)
      (.retV (.bool false) outerCmpCont) ch
      = .ok (.next .stop, σOutT n l iv false tail na, ch) := by
  with_unfolding_all rfl

/-- Pass entry: outer test true → the inner `for`'s declarations
(`j := i` at 4, inner `$forFirst` at 5 — allocation, so TIGHT placement
only) → the inner loop head. -/
private theorem isort_segPA_raw (n : Nat) (l : List Int) (iv : Int)
    (ch : Choices) :
    stepFnIter 33 (σOut n l iv false) (.retV (.bool true) outerCmpCont) ch
      = .ok (innerHeadCfg, σIn n l iv (IntKind.normalize .int iv) true, ch) := by
  with_unfolding_all rfl

/-- First-pass inner dispatch: inner head with the flag up → the FIRST
conjunct (`j > 0`) delivered at the short-circuit `&&` continuation
(the second conjunct's reads have NOT run). -/
private theorem isort_segI0_raw (n : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 26 (σIn n l iv jv true) innerHeadCfg ch
      = .ok (.retV (.bool (decide (0 < jv))) andKCont,
          σIn n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Later-pass inner dispatch: `j := j - 1`, then the first conjunct at
the `&&` continuation. -/
private theorem isort_segI1_raw (n : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 30 (σIn n l iv jv false) innerHeadCfg ch
      = .ok (.retV (.bool (decide
              (0 < IntKind.normalize .int (IntKind.normalize .int (jv - 1)))))
            andKCont,
          σIn n l iv
            (IntKind.normalize .int (IntKind.normalize .int (jv - 1)))
            false, ch) := by
  with_unfolding_all rfl

/-- The `&&` SHORT-CIRCUIT arm: first conjunct false → `false` delivered
straight to the inner `if` — no index read happens (`j = 0` never
evaluates `s[j-1]`). -/
private theorem isort_andFalse_raw (n : Nat) (l : List Int) (iv jv : Int)
    (ffIv : Bool) (ch : Choices) :
    stepFnIter 1 (σIn n l iv jv ffIv) (.retV (.bool false) andKCont) ch
      = .ok (.retV (.bool false) innerIfK, σIn n l iv jv ffIv, ch) := by
  with_unfolding_all rfl

/-- Inner exit: the inner `if` sees false → break unwinds the INNER
loop only, popping back to the OUTER loop head. State untouched. -/
private theorem isort_exitI_raw (n : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 9 (σIn n l iv jv false) (.retV (.bool false) innerIfK) ch
      = .ok (outerHeadCfg, σIn n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Second conjunct, phase A: `&&` sees true → the `s[j-1]` read's
apply point (handle fetched, `j - 1` computed). -/
private theorem isort_segCA_raw (n : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 10 (σIn n l iv jv false) (.retV (.bool true) andKCont) ch
      = .ok (.retV (.int (IntKind.normalize .int (jv - 1)) .int)
            (.strictK .indexGet [sliceH n] [] ([] :: envI) gcK1),
          σIn n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Second conjunct, phase B: first element in → the `s[j]` read's
apply point. -/
private theorem isort_segCB_raw (n : Nat) (l : List Int) (iv jv : Int)
    (w1 : GoValue) (ch : Choices) :
    stepFnIter 5 (σIn n l iv jv false) (.retV w1 gcK1) ch
      = .ok (.retV (.int jv .int)
            (.strictK .indexGet [sliceH n] [] ([] :: envI) (gcK2 w1)),
          σIn n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Second conjunct, phase C: both elements in → the comparison bool
through `boolK` to the inner `if`. -/
private theorem isort_segCC_raw (n : Nat) (l : List Int) (iv jv a b : Int)
    (ch : Choices) :
    stepFnIter 2 (σIn n l iv jv false)
      (.retV (.int b .uint64) (gcK2 (.int a .uint64))) ch
      = .ok (.retV (.bool (decide (b < a))) innerIfK,
          σIn n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase A: inner `if` true → both target refs resolved → the
first rhs read's (`s[j]`) apply point. -/
private theorem isort_segSA_raw (n : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 24 (σIn n l iv jv false) (.retV (.bool true) innerIfK) ch
      = .ok (.retV (.int jv .int)
            (.strictK .indexGet [sliceH n] [] envSw
              (rhsK1 n (IntKind.normalize .int (jv - 1)) jv)),
          σIn n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase B: first rhs value in → the second rhs read's
(`s[j-1]`) apply point. -/
private theorem isort_segSB_raw (n : Nat) (l : List Int) (iv jv idx1 : Int)
    (wj : GoValue) (ch : Choices) :
    stepFnIter 9 (σIn n l iv jv false) (.retV wj (rhsK1 n idx1 jv)) ch
      = .ok (.retV (.int (IntKind.normalize .int (jv - 1)) .int)
            (.strictK .indexGet [sliceH n] [] envSw (rhsK2 n idx1 jv wj)),
          σIn n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase B → stores: both rhs values in → phase 2 begins. -/
private theorem isort_segSC_raw (n : Nat) (l : List Int) (iv jv idx1 : Int)
    (wj wi : GoValue) (ch : Choices) :
    stepFnIter 1 (σIn n l iv jv false) (.retV wi (rhsK2 n idx1 jv wj)) ch
      = .ok (.next (.storeK [refj n idx1, refj n jv] [wj, wi] (.seqn #[])
            envSw swTail),
          σIn n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap tail: stores done → back to the inner loop head. -/
private theorem isort_segSD_raw (n : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 5 (σIn n l iv jv false)
      (.next (.storeK [] [] (.seqn #[]) envSw swTail)) ch
      = .ok (innerHeadCfg, σIn n l iv jv false, ch) := by
  with_unfolding_all rfl

/-! ## Cleaned discharge facts -/

theorem getD_append_left {l1 l2 : List Int} {k : Nat}
    (h : k < l1.length) : (l1 ++ l2).getD k 0 = l1.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h]

private theorem lookup_σIn0 (n : Nat) (l : List Int) (iv jv : Int)
    (ffIv : Bool) :
    Heap.lookup (σIn n l iv jv ffIv).heap (.base ⟨0⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := rfl

/-- One element read at the tight in-pass state (both `s[j-1]` and
`s[j]` go through this). -/
private theorem stepFn_read_σIn {n : Nat} {l : List Int} {iv jv : Int}
    {ffIv : Bool} {k : Nat} {env : LocalEnv} {K : Cont} {ch : Choices}
    (hk : k < n) (hlen : l.length = n) :
    stepFn (σIn n l iv jv ffIv)
      (.retV (.int ((k : Nat) : Int) .int)
        (.strictK .indexGet [sliceH n] [] env K)) ch
      = .ok (.retV (.int (l.getD k 0) .uint64) K, σIn n l iv jv ffIv, ch) :=
  stepFn_strict_apply
    (applyStrictOp_indexGet_slice (lookup_σIn0 n l iv jv ffIv)
      (Nat.le_refl n) hk
      (by rw [Nat.zero_add]; exact getElem?_mapU l k (by omega)))

/-- One element store at the tight in-pass state. -/
private theorem store_σIn {n : Nat} {l : List Int} {iv jv : Int}
    {ffIv : Bool} {k : Nat} {w : Int}
    (hk : k < n) (hlen : l.length = n)
    (hl : ∀ x ∈ l, 0 ≤ x ∧ x < 2 ^ 64) (hw : 0 ≤ w ∧ w < 2 ^ 64) :
    storeTarget (σIn n l iv jv ffIv) (refj n ((k : Nat) : Int))
      (.int w .uint64)
      = .ok (σIn n (l.set k w) iv jv ffIv) := by
  have h := storeTarget_slice_u64 (a := ⟨0⟩) (off := 0) (len := n) (cap := n)
    (i := k) (n := n) (ik := .int) (l := l) (w := w)
    (lookup_σIn0 n l iv jv ffIv) (Nat.le_refl n) hk (by omega) hlen hl hw
  rw [Nat.zero_add] at h
  exact h

/-! ## The INNER induction (arc design: plain strong induction on the
descending counter `j`; invariant `bubbleState`; anchored at the
first-conjunct delivery point of the short-circuit `&&`) -/

/-- **The inner loop**: from the first-conjunct delivery at counter
`jv` — backing list `bubbleState p v jv ++ suffix`, `v` bubbling down
the sorted prefix `p` — the run returns to the OUTER loop head with the
insertion complete, within `92·jv + 10` steps. `jex` is the final
(retired) counter value. -/
private theorem inner_loop (n : Nat) (ivv : Int) (p suffix : List Int)
    (v : Int) (hn : n < 2 ^ 63)
    (hlen : p.length + 1 + suffix.length = n)
    (hsort : Sorted p)
    (hrp : ∀ x ∈ p, 0 ≤ x ∧ x < 2 ^ 64)
    (hrv : 0 ≤ v ∧ v < 2 ^ 64)
    (hrs : ∀ x ∈ suffix, 0 ≤ x ∧ x < 2 ^ 64) :
    ∀ μ jv, μ = jv → jv ≤ p.length →
    (∀ k, jv ≤ k → k < p.length → v < p.getD k 0) →
    ∀ ch : Choices, ∃ (k jex : Nat),
      k ≤ 92 * jv + 10 ∧ jex ≤ p.length ∧
      stepFnIter k
        (σIn n (bubbleState p v jv ++ suffix) ivv ((jv : Nat) : Int) false)
        (.retV (.bool (decide (0 < ((jv : Nat) : Int)))) andKCont) ch
        = .ok (outerHeadCfg,
            σIn n (insertSpec v p ++ suffix) ivv ((jex : Nat) : Int) false,
            ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro jv hμ hjp hinv ch
    have hbl : (bubbleState p v jv ++ suffix).length = n := by
      rw [List.length_append, bubbleState_length hjp]; omega
    cases jv with
    | zero =>
        -- the SHORT-CIRCUIT exit: j = 0, the index reads never run
        rw [show (decide (0 < ((0 : Nat) : Int))) = false from
          decide_eq_false (by omega)]
        rw [← bubbleState_exit hsort (by omega) (.inl rfl)
          (fun k _ hk => hinv k (by omega) hk)]
        have hX0 := isort_andFalse_raw n (bubbleState p v 0 ++ suffix) ivv
          ((0 : Nat) : Int) false ch
        have hX1 := isort_exitI_raw n (bubbleState p v 0 ++ suffix) ivv
          ((0 : Nat) : Int) ch
        exact ⟨10, 0, by omega, by omega, stepFnIter_chain hX0 hX1⟩
    | succ jj =>
        have hjj : jj < p.length := by omega
        have hjj63 : jj < 2 ^ 63 := by omega
        have hrL : ∀ x ∈ bubbleState p v (jj + 1) ++ suffix,
            0 ≤ x ∧ x < 2 ^ 64 := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · rcases mem_bubbleState hx with rfl | hx
            · exact hrv
            · exact hrp x hx
          · exact hrs x hx
        rw [show (decide (0 < ((jj + 1 : Nat) : Int))) = true from
          decide_eq_true (by omega)]
        -- condition reads: s[j-1] then s[j]
        have hCA := isort_segCA_raw n (bubbleState p v (jj + 1) ++ suffix)
          ivv ((jj + 1 : Nat) : Int) ch
        rw [show (((jj + 1 : Nat) : Int) - 1) = ((jj : Nat) : Int) from by
            omega,
          inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega)]
          at hCA
        have hgd1 : (bubbleState p v (jj + 1) ++ suffix).getD jj 0
            = p.getD jj 0 := by
          rw [getD_append_left (by rw [bubbleState_length hjp]; omega),
            bubbleState_getD_lt (by omega) hjp]
        have hread1 := stepFn_read_σIn (n := n)
          (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
          (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj)
          (env := [] :: envI) (K := gcK1) (ch := ch) (by omega) hbl
        rw [hgd1] at hread1
        have hCB := isort_segCB_raw n (bubbleState p v (jj + 1) ++ suffix)
          ivv ((jj + 1 : Nat) : Int) (.int (p.getD jj 0) .uint64) ch
        have hgd2 : (bubbleState p v (jj + 1) ++ suffix).getD (jj + 1) 0
            = v := by
          rw [getD_append_left (by rw [bubbleState_length hjp]; omega),
            bubbleState_getD_eq hjp]
        have hread2 := stepFn_read_σIn (n := n)
          (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
          (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj + 1)
          (env := [] :: envI) (K := gcK2 (.int (p.getD jj 0) .uint64))
          (ch := ch) (by omega) hbl
        rw [hgd2] at hread2
        have hCC := isort_segCC_raw n (bubbleState p v (jj + 1) ++ suffix)
          ivv ((jj + 1 : Nat) : Int) (p.getD jj 0) v ch
        have h19 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain hCA (stepFnIter_one hread1)) hCB)
          (stepFnIter_one hread2)) hCC
        by_cases hcmp : v < p.getD jj 0
        · -- the element test fires: SWAP, then recurse at jj
          rw [decide_eq_true hcmp] at h19
          have hSA := isort_segSA_raw n (bubbleState p v (jj + 1) ++ suffix)
            ivv ((jj + 1 : Nat) : Int) ch
          rw [show (((jj + 1 : Nat) : Int) - 1) = ((jj : Nat) : Int) from by
              omega,
            inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega)]
            at hSA
          -- rhs read 1: s[j] (the bubbled v)
          have hgetj := stepFn_read_σIn (n := n)
            (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
            (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj + 1)
            (env := envSw)
            (K := rhsK1 n ((jj : Nat) : Int) ((jj + 1 : Nat) : Int))
            (ch := ch) (by omega) hbl
          rw [hgd2] at hgetj
          have hSB := isort_segSB_raw n (bubbleState p v (jj + 1) ++ suffix)
            ivv ((jj + 1 : Nat) : Int) ((jj : Nat) : Int)
            (.int v .uint64) ch
          rw [show (((jj + 1 : Nat) : Int) - 1) = ((jj : Nat) : Int) from by
              omega,
            inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega)]
            at hSB
          -- rhs read 2: s[j-1] (the displaced prefix element)
          have hgetj1 := stepFn_read_σIn (n := n)
            (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
            (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj)
            (env := envSw)
            (K := rhsK2 n ((jj : Nat) : Int) ((jj + 1 : Nat) : Int)
              (.int v .uint64))
            (ch := ch) (by omega) hbl
          rw [hgd1] at hgetj1
          have hSC := isort_segSC_raw n (bubbleState p v (jj + 1) ++ suffix)
            ivv ((jj + 1 : Nat) : Int) ((jj : Nat) : Int)
            (.int v .uint64) (.int (p.getD jj 0) .uint64) ch
          -- store 1: s[j-1] := v
          have hst1 := store_σIn (n := n)
            (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
            (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj)
            (w := v) (by omega) hbl hrL hrv
          have hstep1 := stepFn_store_step
            (rs := [refj n ((jj + 1 : Nat) : Int)])
            (vs := [.int (p.getD jj 0) .uint64]) (body := .seqn #[])
            (env := envSw) (k := swTail) (ch := ch) hst1
          -- store 2: s[j] := old s[j-1]
          have hrL1 : ∀ x ∈ (bubbleState p v (jj + 1) ++ suffix).set jj v,
              0 ≤ x ∧ x < 2 ^ 64 := by
            intro x hx
            rcases mem_set_of_mem hx with rfl | hx
            · exact hrv
            · exact hrL x hx
          have hst2 := store_σIn (n := n)
            (l := (bubbleState p v (jj + 1) ++ suffix).set jj v) (iv := ivv)
            (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj + 1)
            (w := p.getD jj 0) (by omega)
            (by rw [List.length_set]; exact hbl) hrL1
            (hrp _ (getD_mem hjj))
          have hstep2 := stepFn_store_step (rs := []) (vs := [])
            (body := .seqn #[]) (env := envSw) (k := swTail) (ch := ch)
            hst2
          -- the list surgery: two sets = the bubble advanced
          have hsurg : ((bubbleState p v (jj + 1) ++ suffix).set jj v).set
              (jj + 1) (p.getD jj 0)
              = bubbleState p v jj ++ suffix := by
            rw [set_append_left (by rw [bubbleState_length hjp]; omega),
              set_append_left (by
                rw [List.length_set, bubbleState_length hjp]; omega)]
            exact congrArg (· ++ suffix)
              (bubbleState_swap (by omega) hjp)
          rw [hsurg] at hstep2
          have hSD := isort_segSD_raw n (bubbleState p v jj ++ suffix) ivv
            ((jj + 1 : Nat) : Int) ch
          -- the next dispatch: j := j - 1, first conjunct delivered
          have hI1 := isort_segI1_raw n (bubbleState p v jj ++ suffix) ivv
            ((jj + 1 : Nat) : Int) ch
          rw [show (((jj + 1 : Nat) : Int) - 1) = ((jj : Nat) : Int) from by
              omega,
            inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega),
            inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega)]
            at hI1
          -- recurse
          obtain ⟨k, jex, hk, hjex, hrec⟩ := ih jj (by omega) jj rfl
            (by omega)
            (fun k hk hk' => by
              rcases Nat.eq_or_lt_of_le hk with rfl | hlt
              · exact hcmp
              · exact hinv k (by omega) hk') ch
          refine ⟨92 + k, jex, by omega, hjex, ?_⟩
          have h62 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
            (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
              (stepFnIter_chain (stepFnIter_chain h19 hSA)
                (stepFnIter_one hgetj)) hSB) (stepFnIter_one hgetj1))
              hSC) (stepFnIter_one hstep1)) (stepFnIter_one hstep2)) hSD
          exact stepFnIter_chain (stepFnIter_chain h62 hI1) hrec
        · -- the element test fails: exit with the insertion complete
          rw [decide_eq_false hcmp] at h19
          rw [← bubbleState_exit hsort (by omega)
            (.inr (Int.not_lt.mp hcmp)) hinv]
          have hX1 := isort_exitI_raw n (bubbleState p v (jj + 1) ++ suffix)
            ivv ((jj + 1 : Nat) : Int) ch
          exact ⟨28, jj + 1, by omega, by omega, stepFnIter_chain h19 hX1⟩

/-! ## One canonical pass, composed -/

/-- **One outer pass at the tight placement** (outer test true at the
4-cell state → the NEXT outer test delivery at the 6-cell state): the
pass allocates `j`/`$forFirst` at 4/5, bubbles `v` into the sorted
prefix `p` (the inner induction), and the following outer dispatch
advances `i`. `jex` is the retired inner counter's final value. -/
theorem pass_seg (n : Nat) (p suffix : List Int) (v : Int) (m : Nat)
    (hn : n < 2 ^ 63)
    (hplen : p.length = m + 1)
    (hlen : p.length + 1 + suffix.length = n)
    (hsort : Sorted p)
    (hrp : ∀ x ∈ p, 0 ≤ x ∧ x < 2 ^ 64)
    (hrv : 0 ≤ v ∧ v < 2 ^ 64)
    (hrs : ∀ x ∈ suffix, 0 ≤ x ∧ x < 2 ^ 64)
    (ch : Choices) :
    ∃ (k jex : Nat), k ≤ 92 * n + 118 ∧ jex ≤ m + 1 ∧
      stepFnIter k (σOut n (p ++ v :: suffix) ((m + 1 : Nat) : Int) false)
        (.retV (.bool true) outerCmpCont) ch
        = .ok (.retV (.bool (decide
              (((m + 2 : Nat) : Int) < ((n : Nat) : Int)))) outerCmpCont,
            σIn n (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
              ((jex : Nat) : Int) false, ch) := by
  have hm1n : m + 2 ≤ n := by omega
  -- pass entry: allocate j := i and the inner $forFirst
  have hPA := isort_segPA_raw n (p ++ v :: suffix) ((m + 1 : Nat) : Int) ch
  rw [inorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)]
    at hPA
  -- first inner dispatch
  have hI0 := isort_segI0_raw n (p ++ v :: suffix) ((m + 1 : Nat) : Int)
    ((m + 1 : Nat) : Int) ch
  -- the inner loop, from j = i = p.length
  have hbub : bubbleState p v (m + 1) ++ suffix = p ++ v :: suffix := by
    rw [← hplen, bubbleState_full, List.append_assoc]
    rfl
  obtain ⟨kin, jex, hkin, hjex, hrun⟩ := inner_loop n ((m + 1 : Nat) : Int)
    p suffix v hn hlen hsort hrp hrv hrs (m + 1) (m + 1) rfl (by omega)
    (fun k hk hk' => by omega) ch
  rw [hbub] at hrun
  -- next outer dispatch (6-cell state; tail-parametric raw segment)
  have hO1 : stepFnIter 29
      (σIn n (insertSpec v p ++ suffix) ((m + 1 : Nat) : Int)
        ((jex : Nat) : Int) false) outerHeadCfg ch
      = .ok (.retV (sliceH n)
            (lenTestK (IntKind.normalize .int (IntKind.normalize .int
              (((m + 1 : Nat) : Int) + 1)))),
          σIn n (insertSpec v p ++ suffix)
            (IntKind.normalize .int (IntKind.normalize .int
              (((m + 1 : Nat) : Int) + 1)))
            ((jex : Nat) : Int) false, ch) :=
    isort_segO1_raw n (insertSpec v p ++ suffix) ((m + 1 : Nat) : Int)
      [(.base ⟨4⟩, intcell ((jex : Nat) : Int)), (.base ⟨5⟩, bcell false)]
      6 ch
  rw [show (((m + 1 : Nat) : Int) + 1) = ((m + 2 : Nat) : Int) from by omega,
    inorm_of_range (v := ((m + 2 : Nat) : Int)) (by omega) (by omega),
    inorm_of_range (v := ((m + 2 : Nat) : Int)) (by omega) (by omega)]
    at hO1
  -- the len(s) apply
  have hlenapp : stepFn
      (σIn n (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
        ((jex : Nat) : Int) false)
      (.retV (sliceH n) (lenTestK ((m + 2 : Nat) : Int))) ch
      = .ok (.retV (.int ((n : Nat) : Int) .int)
          (.strictK .lessCmp [.int ((m + 2 : Nat) : Int) .int] []
            ([] :: envO) outerCmpCont),
        σIn n (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
          ((jex : Nat) : Int) false, ch) :=
    stepFn_strict_apply (done := [])
      (applyStrictOp_len_slice (Nat.le_refl n))
  -- the comparison delivery
  have hOB : stepFnIter 1
      (σIn n (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
        ((jex : Nat) : Int) false)
      (.retV (.int ((n : Nat) : Int) .int)
        (.strictK .lessCmp [.int ((m + 2 : Nat) : Int) .int] []
          ([] :: envO) outerCmpCont)) ch
      = .ok (.retV (.bool (decide
            (((m + 2 : Nat) : Int) < ((n : Nat) : Int)))) outerCmpCont,
          σIn n (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
            ((jex : Nat) : Int) false, ch) :=
    isort_segOB_raw n (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
      [(.base ⟨4⟩, intcell ((jex : Nat) : Int)), (.base ⟨5⟩, bcell false)]
      6 ch
  refine ⟨33 + 26 + kin + 29 + 1 + 1, jex, by omega, by omega, ?_⟩
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain hPA hI0) hrun) hO1)
    (stepFnIter_one hlenapp)) hOB


end GoLean.Examples.InsertionSort
