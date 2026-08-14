import GoLeanProofs.Examples.InsertionSortProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Examples.InsertionSort.Setup

/-!
# InsertionSort — Subject

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
open GoLean.Frame

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-! ## The subject phase at the harness placement

The committed pass/frame-rebase machinery re-derived under the harness
continuation (Reverse's route (b): concrete re-derivation — the frame
theorem maps ADDRESSES, not continuations, so the canonical subject
run cannot be transferred here). Harness subject cells: 8 = the `s`
parameter, 9 = the subject `i`, 10 = the outer `$forFirst`; the
per-pass `j`/`$forFirst` pair sits TIGHT at 11/12 and is rebased into
the frame between passes (`rebaseSim11`, threshold 11 — the port of
`rebaseSim`). All step counts carry over from the canonical segments
verbatim (same statements, same machine paths — only addresses and the
tail continuation differ); each is re-checked by `rfl` here. -/

/-- The harness continuation after the subject call (`ok := 1` on). -/
def hAfterCallK : Cont := .seq (hIBodyList.drop 4) envIH2 hIFrame0

/-- The subject call's frame continuation (caller env saved). -/
def hSubjFrameK : Cont := .frame [] envIH2 [] [] hAfterCallK false

def envHO : LocalEnv :=
  [[("$forFirst", .base ⟨10⟩)], [("i", .base ⟨9⟩)], [], [("s", .base ⟨8⟩)]]
def envHOMid : LocalEnv :=
  [[("i", .base ⟨9⟩)], [], [("s", .base ⟨8⟩)]]
def envHOOut : LocalEnv := [[], [("s", .base ⟨8⟩)]]

def hHeadTailO : Cont :=
  .seq [] envHO (.seq [] envHOMid (.seq [] envHOOut hSubjFrameK))
/-- The subject OUTER loop-head configuration (harness placement). -/
def hOuterHeadCfg : Config :=
  .exec (.while (.boolLit true) outerWhileBody) envHO hHeadTailO
def hLoopKO : Cont :=
  .loop (.boolLit true) outerWhileBody envHO hHeadTailO
def hOuterCmpCont : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envHO)
    (.seq [innerForBlock] ([] :: envHO) hLoopKO)
def hLenTestK (iv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice (.int .uint64)))) [] [] ([] :: envHO)
    (.strictK .lessCmp [.int iv .int] [] ([] :: envHO) hOuterCmpCont)

def envHI : LocalEnv :=
  [("$forFirst", .base ⟨12⟩)] :: [("j", .base ⟨11⟩)] :: [] :: [] :: envHO
def hInnerTail : Cont :=
  .seq [] envHI
    (.seq [] ([("j", .base ⟨11⟩)] :: [] :: [] :: envHO)
      (.seq [] ([] :: [] :: envHO)
        (.seq [] ([] :: envHO) hLoopKO)))
/-- The subject INNER loop-head configuration (tight placement). -/
def hInnerHeadCfg : Config :=
  .exec (.while (.boolLit true) innerWhileBody) envHI hInnerTail
def hLoopKI : Cont :=
  .loop (.boolLit true) innerWhileBody envHI hInnerTail
def hInnerIfK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envHI)
    (.seq [isortSwapBlock] ([] :: envHI) hLoopKI)
def hAndKCont : Cont :=
  .andK (.greaterCmp
      (.indexGet (.var "s") (.sub (.var "j") (.intLit 1 .int)))
      (.indexGet (.var "s") (.var "j")))
    ([] :: envHI) hInnerIfK
def hGcK1 : Cont :=
  .strictK .greaterCmp [] [.indexGet (.var "s") (.var "j")] ([] :: envHI)
    (.boolK hInnerIfK)
def hGcK2 (w1 : GoValue) : Cont :=
  .strictK .greaterCmp [w1] [] ([] :: envHI) (.boolK hInnerIfK)

def envHSw : LocalEnv := [] :: [] :: envHI
def hSwTail : Cont :=
  .seq [] envHSw (.seq [] ([] :: envHI) hLoopKI)
def hrefj (n : Nat) (idx : Int) : TargetRef :=
  .chain (hISliceH n) [.int idx .int] [.index]
def hRhsK1 (n : Nat) (idx1 jv : Int) : Cont :=
  .rhsK .vals [hrefj n idx1, hrefj n jv] []
    [.indexGet (.var "s") (.sub (.var "j") (.intLit 1 .int))]
    (.seqn #[]) envHSw hSwTail
def hRhsK2 (n : Nat) (idx1 jv : Int) (wj : GoValue) : Cont :=
  .rhsK .vals [hrefj n idx1, hrefj n jv] [wj] [] (.seqn #[]) envHSw hSwTail

/-- The harness-subject state family, TAIL-PARAMETRIC: the eleven
fixed harness cells in front (setup counter parked at `n`, verdict
still 0), an arbitrary inert tail behind. -/
def σHOutT (n seed : Nat) (l : List Int) (iv : Int) (ffv : Bool)
    (tail : Heap) (na : Nat) : ExecState :=
  { types := isortLowered.typeDefs.toList,
    functions := isortLowered.funcs,
    methods := isortLowered.methods,
    heap := (.base ⟨0⟩, ucell (n : Int)) :: (.base ⟨1⟩, ucell (seed : Int))
      :: (.base ⟨2⟩, ucell 0) :: (.base ⟨3⟩, hIHandleCell n)
      :: (.base ⟨4⟩, arrCell n l) :: (.base ⟨5⟩, hIHandleCell n)
      :: (.base ⟨6⟩, ucell ((n : Nat) : Int)) :: (.base ⟨7⟩, bcell false)
      :: (.base ⟨8⟩, hIHandleCell n) :: (.base ⟨9⟩, intcell iv)
      :: (.base ⟨10⟩, bcell ffv) :: tail,
    nextAddr := na }

/-- The tight 11-cell outer state (canonical pass placement). -/
def σHOut (n seed : Nat) (l : List Int) (iv : Int) (ffv : Bool) :
    ExecState :=
  σHOutT n seed l iv ffv [] 11

/-- The tight 13-cell in-pass state: `j` at 11, inner `$forFirst` at 12. -/
def σHIn (n seed : Nat) (l : List Int) (iv jv : Int) (ffIv : Bool) :
    ExecState :=
  σHOutT n seed l iv false
    [(.base ⟨11⟩, intcell jv), (.base ⟨12⟩, bcell ffIv)] 13

/-- **The bridge**: setup exit (test false) → break unwinding → the
subject call — argument read, frame entry (`s` param at 8), `i := 1`
(at 9), the `$forFirst` block (at 10) — → the subject outer loop head.
40 steps (trace 306→346). -/
theorem hbridge_raw (n seed : Nat) (l : List Int) (ch : Choices) :
    stepFnIter 40 (sISU n (seed : Int) l ((n : Nat) : Int) false)
      (.retV (.bool false) suICmpK) ch
      = .ok (hOuterHeadCfg, σHOut n seed l 1 true, ch) := by
  with_unfolding_all rfl

/-- First-pass outer dispatch (tail-parametric; touches only 0–10). -/
theorem hseg_O0_raw (n seed : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 25 (σHOutT n seed l iv true tail na) hOuterHeadCfg ch
      = .ok (.retV (hISliceH n) (hLenTestK iv),
          σHOutT n seed l iv false tail na, ch) := by
  with_unfolding_all rfl

/-- Later-pass outer dispatch: `i := i + 1`, then the `len(s)` apply. -/
private theorem hseg_O1_raw (n seed : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 29 (σHOutT n seed l iv false tail na) hOuterHeadCfg ch
      = .ok (.retV (hISliceH n)
            (hLenTestK (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
          σHOutT n seed l (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            false tail na, ch) := by
  with_unfolding_all rfl

/-- The outer comparison delivered. -/
theorem hseg_OB_raw (n seed : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 1 (σHOutT n seed l iv false tail na)
      (.retV (.int ((n : Nat) : Int) .int)
        (.strictK .lessCmp [.int iv .int] [] ([] :: envHO) hOuterCmpCont)) ch
      = .ok (.retV (.bool (decide (iv < ((n : Nat) : Int)))) hOuterCmpCont,
          σHOutT n seed l iv false tail na, ch) := by
  with_unfolding_all rfl

/-- Outer exit: test false → break unwinding, subject frame exit → the
harness continuation (`.next hAfterCallK`). State untouched. -/
private theorem hseg_exitO_raw (n seed : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 8 (σHOutT n seed l iv false tail na)
      (.retV (.bool false) hOuterCmpCont) ch
      = .ok (.next hAfterCallK, σHOutT n seed l iv false tail na, ch) := by
  with_unfolding_all rfl

/-- Pass entry: outer test true → `j := i` at 11, inner `$forFirst` at
12 (allocation — TIGHT placement only) → the inner loop head. -/
private theorem hseg_PA_raw (n seed : Nat) (l : List Int) (iv : Int)
    (ch : Choices) :
    stepFnIter 33 (σHOut n seed l iv false) (.retV (.bool true) hOuterCmpCont) ch
      = .ok (hInnerHeadCfg, σHIn n seed l iv (IntKind.normalize .int iv) true, ch) := by
  with_unfolding_all rfl

/-- First-pass inner dispatch → the first conjunct at the `&&`. -/
private theorem hseg_I0_raw (n seed : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 26 (σHIn n seed l iv jv true) hInnerHeadCfg ch
      = .ok (.retV (.bool (decide (0 < jv))) hAndKCont,
          σHIn n seed l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Later-pass inner dispatch: `j := j - 1`, then the first conjunct. -/
private theorem hseg_I1_raw (n seed : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 30 (σHIn n seed l iv jv false) hInnerHeadCfg ch
      = .ok (.retV (.bool (decide
              (0 < IntKind.normalize .int (IntKind.normalize .int (jv - 1)))))
            hAndKCont,
          σHIn n seed l iv
            (IntKind.normalize .int (IntKind.normalize .int (jv - 1)))
            false, ch) := by
  with_unfolding_all rfl

/-- The `&&` short-circuit arm (`j = 0` never reads `s[j-1]`). -/
private theorem hseg_andFalse_raw (n seed : Nat) (l : List Int) (iv jv : Int)
    (ffIv : Bool) (ch : Choices) :
    stepFnIter 1 (σHIn n seed l iv jv ffIv) (.retV (.bool false) hAndKCont) ch
      = .ok (.retV (.bool false) hInnerIfK, σHIn n seed l iv jv ffIv, ch) := by
  with_unfolding_all rfl

/-- Inner exit: break unwinds the inner loop only → the outer head. -/
private theorem hseg_exitI_raw (n seed : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 9 (σHIn n seed l iv jv false) (.retV (.bool false) hInnerIfK) ch
      = .ok (hOuterHeadCfg, σHIn n seed l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Second conjunct, phase A: `&&` true → the `s[j-1]` read's apply. -/
private theorem hseg_CA_raw (n seed : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 10 (σHIn n seed l iv jv false) (.retV (.bool true) hAndKCont) ch
      = .ok (.retV (.int (IntKind.normalize .int (jv - 1)) .int)
            (.strictK .indexGet [hISliceH n] [] ([] :: envHI) hGcK1),
          σHIn n seed l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Second conjunct, phase B: first element in → the `s[j]` apply. -/
private theorem hseg_CB_raw (n seed : Nat) (l : List Int) (iv jv : Int)
    (w1 : GoValue) (ch : Choices) :
    stepFnIter 5 (σHIn n seed l iv jv false) (.retV w1 hGcK1) ch
      = .ok (.retV (.int jv .int)
            (.strictK .indexGet [hISliceH n] [] ([] :: envHI) (hGcK2 w1)),
          σHIn n seed l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Second conjunct, phase C: comparison bool through `boolK`. -/
private theorem hseg_CC_raw (n seed : Nat) (l : List Int) (iv jv a b : Int)
    (ch : Choices) :
    stepFnIter 2 (σHIn n seed l iv jv false)
      (.retV (.int b .uint64) (hGcK2 (.int a .uint64))) ch
      = .ok (.retV (.bool (decide (b < a))) hInnerIfK,
          σHIn n seed l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase A: inner `if` true → targets resolved → `s[j]` apply. -/
private theorem hseg_SA_raw (n seed : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 24 (σHIn n seed l iv jv false) (.retV (.bool true) hInnerIfK) ch
      = .ok (.retV (.int jv .int)
            (.strictK .indexGet [hISliceH n] [] envHSw
              (hRhsK1 n (IntKind.normalize .int (jv - 1)) jv)),
          σHIn n seed l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase B: first rhs value in → the `s[j-1]` apply. -/
private theorem hseg_SB_raw (n seed : Nat) (l : List Int) (iv jv idx1 : Int)
    (wj : GoValue) (ch : Choices) :
    stepFnIter 9 (σHIn n seed l iv jv false) (.retV wj (hRhsK1 n idx1 jv)) ch
      = .ok (.retV (.int (IntKind.normalize .int (jv - 1)) .int)
            (.strictK .indexGet [hISliceH n] [] envHSw (hRhsK2 n idx1 jv wj)),
          σHIn n seed l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase B → stores: both rhs values in → phase 2 begins. -/
private theorem hseg_SC_raw (n seed : Nat) (l : List Int) (iv jv idx1 : Int)
    (wj wi : GoValue) (ch : Choices) :
    stepFnIter 1 (σHIn n seed l iv jv false) (.retV wi (hRhsK2 n idx1 jv wj)) ch
      = .ok (.next (.storeK [hrefj n idx1, hrefj n jv] [wj, wi] (.seqn #[])
            envHSw hSwTail),
          σHIn n seed l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap tail: stores done → back to the inner loop head. -/
private theorem hseg_SD_raw (n seed : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 5 (σHIn n seed l iv jv false)
      (.next (.storeK [] [] (.seqn #[]) envHSw hSwTail)) ch
      = .ok (hInnerHeadCfg, σHIn n seed l iv jv false, ch) := by
  with_unfolding_all rfl

/-- The backing-cell lookup at the tight in-pass state. -/
private theorem lookup_σHIn4 (n seed : Nat) (l : List Int) (iv jv : Int)
    (ffIv : Bool) :
    Heap.lookup (σHIn n seed l iv jv ffIv).heap (.base ⟨4⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := rfl

/-- One element read at the tight in-pass state. -/
private theorem stepFn_read_σHIn {n seed : Nat} {l : List Int} {iv jv : Int}
    {ffIv : Bool} {k : Nat} {env : LocalEnv} {K : Cont} {ch : Choices}
    (hk : k < n) (hlen : l.length = n) :
    stepFn (σHIn n seed l iv jv ffIv)
      (.retV (.int ((k : Nat) : Int) .int)
        (.strictK .indexGet [hISliceH n] [] env K)) ch
      = .ok (.retV (.int (l.getD k 0) .uint64) K, σHIn n seed l iv jv ffIv, ch) :=
  stepFn_strict_apply
    (applyStrictOp_indexGet_slice (lookup_σHIn4 n seed l iv jv ffIv)
      (Nat.le_refl n) hk
      (by rw [Nat.zero_add]; exact getElem?_mapU l k (by omega)))

/-- One element store at the tight in-pass state. -/
private theorem store_σHIn {n seed : Nat} {l : List Int} {iv jv : Int}
    {ffIv : Bool} {k : Nat} {w : Int}
    (hk : k < n) (hlen : l.length = n)
    (hl : ∀ x ∈ l, 0 ≤ x ∧ x < 2 ^ 64) (hw : 0 ≤ w ∧ w < 2 ^ 64) :
    storeTarget (σHIn n seed l iv jv ffIv) (hrefj n ((k : Nat) : Int))
      (.int w .uint64)
      = .ok (σHIn n seed (l.set k w) iv jv ffIv) := by
  have h := storeTarget_slice_u64 (a := ⟨4⟩) (off := 0) (len := n) (cap := n)
    (i := k) (n := n) (ik := .int) (l := l) (w := w)
    (lookup_σHIn4 n seed l iv jv ffIv) (Nat.le_refl n) hk (by omega) hlen hl hw
  rw [Nat.zero_add] at h
  exact h

/-! ### The inner induction at the harness placement (the canonical
`inner_loop`, re-derived — same measure, same invariant, same counts) -/

/-- **The inner loop (harness placement)**: from the first-conjunct
delivery at counter `jv` the run returns to the OUTER loop head with
the insertion complete, within `92·jv + 10` steps. -/
private theorem hs_inner_loop (n seed : Nat) (ivv : Int) (p suffix : List Int)
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
        (σHIn n seed (bubbleState p v jv ++ suffix) ivv ((jv : Nat) : Int) false)
        (.retV (.bool (decide (0 < ((jv : Nat) : Int)))) hAndKCont) ch
        = .ok (hOuterHeadCfg,
            σHIn n seed (insertSpec v p ++ suffix) ivv ((jex : Nat) : Int) false,
            ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro jv hμ hjp hinv ch
    have hbl : (bubbleState p v jv ++ suffix).length = n := by
      rw [List.length_append, bubbleState_length hjp]; omega
    cases jv with
    | zero =>
        rw [show (decide (0 < ((0 : Nat) : Int))) = false from
          decide_eq_false (by omega)]
        rw [← bubbleState_exit hsort (by omega) (.inl rfl)
          (fun k _ hk => hinv k (by omega) hk)]
        have hX0 := hseg_andFalse_raw n seed (bubbleState p v 0 ++ suffix) ivv
          ((0 : Nat) : Int) false ch
        have hX1 := hseg_exitI_raw n seed (bubbleState p v 0 ++ suffix) ivv
          ((0 : Nat) : Int) ch
        exact ⟨10, 0, by omega, by omega, stepFnIter_chain hX0 hX1⟩
    | succ jj =>
        have hjj : jj < p.length := by omega
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
        have hCA := hseg_CA_raw n seed (bubbleState p v (jj + 1) ++ suffix)
          ivv ((jj + 1 : Nat) : Int) ch
        rw [show (((jj + 1 : Nat) : Int) - 1) = ((jj : Nat) : Int) from by
            omega,
          inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega)]
          at hCA
        have hgd1 : (bubbleState p v (jj + 1) ++ suffix).getD jj 0
            = p.getD jj 0 := by
          rw [getD_append_left (by rw [bubbleState_length hjp]; omega),
            bubbleState_getD_lt (by omega) hjp]
        have hread1 := stepFn_read_σHIn (n := n) (seed := seed)
          (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
          (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj)
          (env := [] :: envHI) (K := hGcK1) (ch := ch) (by omega) hbl
        rw [hgd1] at hread1
        have hCB := hseg_CB_raw n seed (bubbleState p v (jj + 1) ++ suffix)
          ivv ((jj + 1 : Nat) : Int) (.int (p.getD jj 0) .uint64) ch
        have hgd2 : (bubbleState p v (jj + 1) ++ suffix).getD (jj + 1) 0
            = v := by
          rw [getD_append_left (by rw [bubbleState_length hjp]; omega),
            bubbleState_getD_eq hjp]
        have hread2 := stepFn_read_σHIn (n := n) (seed := seed)
          (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
          (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj + 1)
          (env := [] :: envHI) (K := hGcK2 (.int (p.getD jj 0) .uint64))
          (ch := ch) (by omega) hbl
        rw [hgd2] at hread2
        have hCC := hseg_CC_raw n seed (bubbleState p v (jj + 1) ++ suffix)
          ivv ((jj + 1 : Nat) : Int) (p.getD jj 0) v ch
        have h19 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain hCA (stepFnIter_one hread1)) hCB)
          (stepFnIter_one hread2)) hCC
        by_cases hcmp : v < p.getD jj 0
        · rw [decide_eq_true hcmp] at h19
          have hSA := hseg_SA_raw n seed (bubbleState p v (jj + 1) ++ suffix)
            ivv ((jj + 1 : Nat) : Int) ch
          rw [show (((jj + 1 : Nat) : Int) - 1) = ((jj : Nat) : Int) from by
              omega,
            inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega)]
            at hSA
          have hgetj := stepFn_read_σHIn (n := n) (seed := seed)
            (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
            (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj + 1)
            (env := envHSw)
            (K := hRhsK1 n ((jj : Nat) : Int) ((jj + 1 : Nat) : Int))
            (ch := ch) (by omega) hbl
          rw [hgd2] at hgetj
          have hSB := hseg_SB_raw n seed (bubbleState p v (jj + 1) ++ suffix)
            ivv ((jj + 1 : Nat) : Int) ((jj : Nat) : Int)
            (.int v .uint64) ch
          rw [show (((jj + 1 : Nat) : Int) - 1) = ((jj : Nat) : Int) from by
              omega,
            inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega)]
            at hSB
          have hgetj1 := stepFn_read_σHIn (n := n) (seed := seed)
            (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
            (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj)
            (env := envHSw)
            (K := hRhsK2 n ((jj : Nat) : Int) ((jj + 1 : Nat) : Int)
              (.int v .uint64))
            (ch := ch) (by omega) hbl
          rw [hgd1] at hgetj1
          have hSC := hseg_SC_raw n seed (bubbleState p v (jj + 1) ++ suffix)
            ivv ((jj + 1 : Nat) : Int) ((jj : Nat) : Int)
            (.int v .uint64) (.int (p.getD jj 0) .uint64) ch
          have hst1 := store_σHIn (n := n) (seed := seed)
            (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
            (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj)
            (w := v) (by omega) hbl hrL hrv
          have hstep1 := stepFn_store_step
            (rs := [hrefj n ((jj + 1 : Nat) : Int)])
            (vs := [.int (p.getD jj 0) .uint64]) (body := .seqn #[])
            (env := envHSw) (k := hSwTail) (ch := ch) hst1
          have hrL1 : ∀ x ∈ (bubbleState p v (jj + 1) ++ suffix).set jj v,
              0 ≤ x ∧ x < 2 ^ 64 := by
            intro x hx
            rcases mem_set_of_mem hx with rfl | hx
            · exact hrv
            · exact hrL x hx
          have hst2 := store_σHIn (n := n) (seed := seed)
            (l := (bubbleState p v (jj + 1) ++ suffix).set jj v) (iv := ivv)
            (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj + 1)
            (w := p.getD jj 0) (by omega)
            (by rw [List.length_set]; exact hbl) hrL1
            (hrp _ (getD_mem hjj))
          have hstep2 := stepFn_store_step (rs := []) (vs := [])
            (body := .seqn #[]) (env := envHSw) (k := hSwTail) (ch := ch)
            hst2
          have hsurg : ((bubbleState p v (jj + 1) ++ suffix).set jj v).set
              (jj + 1) (p.getD jj 0)
              = bubbleState p v jj ++ suffix := by
            rw [set_append_left (by rw [bubbleState_length hjp]; omega),
              set_append_left (by
                rw [List.length_set, bubbleState_length hjp]; omega)]
            exact congrArg (· ++ suffix)
              (bubbleState_swap (by omega) hjp)
          rw [hsurg] at hstep2
          have hSD := hseg_SD_raw n seed (bubbleState p v jj ++ suffix) ivv
            ((jj + 1 : Nat) : Int) ch
          have hI1 := hseg_I1_raw n seed (bubbleState p v jj ++ suffix) ivv
            ((jj + 1 : Nat) : Int) ch
          rw [show (((jj + 1 : Nat) : Int) - 1) = ((jj : Nat) : Int) from by
              omega,
            inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega),
            inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega)]
            at hI1
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
        · rw [decide_eq_false hcmp] at h19
          rw [← bubbleState_exit hsort (by omega)
            (.inr (Int.not_lt.mp hcmp)) hinv]
          have hX1 := hseg_exitI_raw n seed (bubbleState p v (jj + 1) ++ suffix)
            ivv ((jj + 1 : Nat) : Int) ch
          exact ⟨28, jj + 1, by omega, by omega, stepFnIter_chain h19 hX1⟩

/-- **One outer pass at the tight harness placement** (outer test true
at the 11-cell state → the NEXT outer test delivery at the 13-cell
state). -/
private theorem hs_pass_seg (n seed : Nat) (p suffix : List Int) (v : Int)
    (m : Nat) (hn : n < 2 ^ 63)
    (hplen : p.length = m + 1)
    (hlen : p.length + 1 + suffix.length = n)
    (hsort : Sorted p)
    (hrp : ∀ x ∈ p, 0 ≤ x ∧ x < 2 ^ 64)
    (hrv : 0 ≤ v ∧ v < 2 ^ 64)
    (hrs : ∀ x ∈ suffix, 0 ≤ x ∧ x < 2 ^ 64)
    (ch : Choices) :
    ∃ (k jex : Nat), k ≤ 92 * n + 118 ∧ jex ≤ m + 1 ∧
      stepFnIter k (σHOut n seed (p ++ v :: suffix) ((m + 1 : Nat) : Int) false)
        (.retV (.bool true) hOuterCmpCont) ch
        = .ok (.retV (.bool (decide
              (((m + 2 : Nat) : Int) < ((n : Nat) : Int)))) hOuterCmpCont,
            σHIn n seed (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
              ((jex : Nat) : Int) false, ch) := by
  have hm1n : m + 2 ≤ n := by omega
  have hPA := hseg_PA_raw n seed (p ++ v :: suffix) ((m + 1 : Nat) : Int) ch
  rw [inorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)]
    at hPA
  have hI0 := hseg_I0_raw n seed (p ++ v :: suffix) ((m + 1 : Nat) : Int)
    ((m + 1 : Nat) : Int) ch
  have hbub : bubbleState p v (m + 1) ++ suffix = p ++ v :: suffix := by
    rw [← hplen, bubbleState_full, List.append_assoc]
    rfl
  obtain ⟨kin, jex, hkin, hjex, hrun⟩ := hs_inner_loop n seed
    ((m + 1 : Nat) : Int) p suffix v hn hlen hsort hrp hrv hrs (m + 1)
    (m + 1) rfl (by omega) (fun k hk hk' => by omega) ch
  rw [hbub] at hrun
  have hO1 : stepFnIter 29
      (σHIn n seed (insertSpec v p ++ suffix) ((m + 1 : Nat) : Int)
        ((jex : Nat) : Int) false) hOuterHeadCfg ch
      = .ok (.retV (hISliceH n)
            (hLenTestK (IntKind.normalize .int (IntKind.normalize .int
              (((m + 1 : Nat) : Int) + 1)))),
          σHIn n seed (insertSpec v p ++ suffix)
            (IntKind.normalize .int (IntKind.normalize .int
              (((m + 1 : Nat) : Int) + 1)))
            ((jex : Nat) : Int) false, ch) :=
    hseg_O1_raw n seed (insertSpec v p ++ suffix) ((m + 1 : Nat) : Int)
      [(.base ⟨11⟩, intcell ((jex : Nat) : Int)), (.base ⟨12⟩, bcell false)]
      13 ch
  rw [show (((m + 1 : Nat) : Int) + 1) = ((m + 2 : Nat) : Int) from by omega,
    inorm_of_range (v := ((m + 2 : Nat) : Int)) (by omega) (by omega),
    inorm_of_range (v := ((m + 2 : Nat) : Int)) (by omega) (by omega)]
    at hO1
  have hlenapp : stepFn
      (σHIn n seed (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
        ((jex : Nat) : Int) false)
      (.retV (hISliceH n) (hLenTestK ((m + 2 : Nat) : Int))) ch
      = .ok (.retV (.int ((n : Nat) : Int) .int)
          (.strictK .lessCmp [.int ((m + 2 : Nat) : Int) .int] []
            ([] :: envHO) hOuterCmpCont),
        σHIn n seed (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
          ((jex : Nat) : Int) false, ch) :=
    stepFn_strict_apply (done := [])
      (applyStrictOp_len_slice (Nat.le_refl n))
  have hOB : stepFnIter 1
      (σHIn n seed (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
        ((jex : Nat) : Int) false)
      (.retV (.int ((n : Nat) : Int) .int)
        (.strictK .lessCmp [.int ((m + 2 : Nat) : Int) .int] []
          ([] :: envHO) hOuterCmpCont)) ch
      = .ok (.retV (.bool (decide
            (((m + 2 : Nat) : Int) < ((n : Nat) : Int)))) hOuterCmpCont,
          σHIn n seed (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
            ((jex : Nat) : Int) false, ch) :=
    hseg_OB_raw n seed (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
      [(.base ⟨11⟩, intcell ((jex : Nat) : Int)), (.base ⟨12⟩, bcell false)]
      13 ch
  refine ⟨33 + 26 + kin + 29 + 1 + 1, jex, by omega, by omega, ?_⟩
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain hPA hI0) hrun) hO1)
    (stepFnIter_one hlenapp)) hOB

/-! ### The per-pass frame layer at threshold 11 (the canonical
`ρsh`/`rebaseSim` layer, re-derived at the harness prefix: the eleven
fixed cells 0–10, the pass-local region from 11) -/

/-- The per-pass shift: identity on the fixed cells `0..10`, shift by
`d` on the pass-local region. -/
def ρ11 (d : Nat) : Nat → Nat := fun x => if x < 11 then x else x + d

private theorem ρ11_lt {d a : Nat} (h : a < 11) : ρ11 d a = a := if_pos h
private theorem ρ11_ge {d a : Nat} (h : 11 ≤ a) : ρ11 d a = a + d :=
  if_neg (by omega)

private theorem shiftSpec_ρ11 (d : Nat) : ShiftSpec (ρ11 d) 11 (11 + d) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    simp only [ρ11] at hxy
    split at hxy <;> split at hxy <;> omega
  · intro k
    simp only [ρ11]
    rw [if_neg (by omega)]
    omega

private theorem renCell_handleH (d n : Nat) :
    renameCell (ρ11 d) (hIHandleCell n) = hIHandleCell n := by
  simp [renameCell, renameValue, renameLoc, ρ11]

private theorem lookup_σHOut_ge {n seed : Nat} {l : List Int} {iv : Int}
    {ffv : Bool} {a : Nat} (ha : 11 ≤ a) :
    Heap.lookup (σHOut n seed l iv ffv).heap (.base ⟨a⟩) = none := by
  simp [σHOut, σHOutT, Heap.lookup,
    beq_false_of_ne (base_ne (show (0 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (1 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (2 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (3 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (4 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (5 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (6 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (7 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (8 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (9 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (10 : Nat) ≠ a by omega))]

private theorem lookup_σHIn_ge {n seed : Nat} {l : List Int} {iv jv : Int}
    {ffIv : Bool} {a : Nat} (ha : 13 ≤ a) :
    Heap.lookup (σHIn n seed l iv jv ffIv).heap (.base ⟨a⟩) = none := by
  simp [σHIn, σHOutT, Heap.lookup,
    beq_false_of_ne (base_ne (show (0 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (1 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (2 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (3 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (4 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (5 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (6 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (7 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (8 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (9 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (10 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (11 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (12 : Nat) ≠ a by omega))]

private theorem lookup_σHOut_field (n seed : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) (b : Loc) (tid : TypeId) (f : String) :
    Heap.lookup (σHOut n seed l iv ffv).heap (.field b tid f) = none := rfl

private theorem lookup_σHOut_index (n seed : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) (b : Loc) (i : Int) :
    Heap.lookup (σHOut n seed l iv ffv).heap (.index b i) = none := rfl

private theorem lookup_σHIn_field (n seed : Nat) (l : List Int) (iv jv : Int)
    (ffIv : Bool) (b : Loc) (tid : TypeId) (f : String) :
    Heap.lookup (σHIn n seed l iv jv ffIv).heap (.field b tid f) = none := rfl

private theorem lookup_σHIn_index (n seed : Nat) (l : List Int) (iv jv : Int)
    (ffIv : Bool) (b : Loc) (i : Int) :
    Heap.lookup (σHIn n seed l iv jv ffIv).heap (.index b i) = none := rfl

/-- Root bump by 2 above the fixed cells (threshold 11). -/
def bump2H : Loc → Loc
  | .base a => .base ⟨if a.id < 11 then a.id else a.id + 2⟩
  | .field b tid f => .field (bump2H b) tid f
  | .index b i => .index (bump2H b) i

private theorem renameLoc_bump2H (d : Nat) (l : Loc) :
    renameLoc (ρ11 (d + 2)) l = renameLoc (ρ11 d) (bump2H l) := by
  induction l with
  | base a =>
      have h : ρ11 (d + 2) a.id
          = ρ11 d (if a.id < 11 then a.id else a.id + 2) := by
        by_cases ha : a.id < 11
        · rw [if_pos ha, ρ11_lt ha, ρ11_lt ha]
        · rw [if_neg ha, ρ11_ge (d := d + 2) (a := a.id) (by omega),
            ρ11_ge (d := d) (a := a.id + 2) (by omega)]
          omega
      simp only [renameLoc, bump2H, h]
  | field b tid f ih => simp only [renameLoc, bump2H, ih]
  | index b i ih => simp only [renameLoc, bump2H, ih]

/-- The trivial-frame simulation at the subject-loop entry. -/
theorem frameSim_zero11 (n seed : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) :
    FrameSim (ρ11 0) 11 11 [] (σHOut n seed l iv ffv)
      (σHOut n seed l iv ffv) := by
  refine ⟨shiftSpec_ρ11 0, rfl, rfl, rfl, rfl, rfl, Nat.le_refl 11,
    ?_, ?_, fun a => rfl, bodies_ρsh (ρ11 0)⟩
  · intro loc
    match loc with
    | .base ⟨a⟩ =>
        match a with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
        | 3 =>
            show Heap.lookup (σHOut n seed l iv ffv).heap (.base ⟨ρ11 0 3⟩)
              = some (renameCell (ρ11 0) (hIHandleCell n))
            rw [renCell_handleH 0 n]
            rfl
        | 4 =>
            show Heap.lookup (σHOut n seed l iv ffv).heap (.base ⟨ρ11 0 4⟩)
              = some (renameCell (ρ11 0) (arrCell n l))
            rw [renCell_arr]
            rfl
        | 5 =>
            show Heap.lookup (σHOut n seed l iv ffv).heap (.base ⟨ρ11 0 5⟩)
              = some (renameCell (ρ11 0) (hIHandleCell n))
            rw [renCell_handleH 0 n]
            rfl
        | 6 => rfl
        | 7 => rfl
        | 8 =>
            show Heap.lookup (σHOut n seed l iv ffv).heap (.base ⟨ρ11 0 8⟩)
              = some (renameCell (ρ11 0) (hIHandleCell n))
            rw [renCell_handleH 0 n]
            rfl
        | 9 => rfl
        | 10 => rfl
        | (a + 11) =>
            show Heap.lookup (σHOut n seed l iv ffv).heap
              (.base ⟨ρ11 0 (a + 11)⟩) = _
            rw [ρ11_ge (d := 0) (a := a + 11) (by omega)]
            rw [lookup_σHOut_ge (a := a + 11 + 0) (by omega)]
            rfl
    | .field b tid f => rfl
    | .index b i => rfl
  · intro loc c hc
    simp [Heap.lookup] at hc

theorem fs_lookup_none11 {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (h : FrameSim ρ na₀ na fr σ σF) {l : Loc}
    (hl : Heap.lookup σ.heap l = none) :
    Heap.lookup σF.heap (renameLoc ρ l) = Heap.lookup fr (renameLoc ρ l) := by
  have h2 := h.lookup_img l
  rw [hl] at h2
  exact h2

/-- **The frame rebase at threshold 11**: the pass's retired
`j`/`$forFirst` cells (canonical 11/12) move INTO the frame at their
true addresses `11+d`/`12+d`. -/
private theorem rebaseSim11 {d : Nat} {fr : Heap} {n seed : Nat}
    {l : List Int} {iv jv : Int} {σA : ExecState}
    (h : FrameSim (ρ11 d) 11 (11 + d) fr (σHIn n seed l iv jv false) σA) :
    FrameSim (ρ11 (d + 2)) 11 (11 + (d + 2))
      (fr ++ [(.base ⟨11 + d⟩, intcell jv), (.base ⟨12 + d⟩, bcell false)])
      (σHOut n seed l iv false) σA := by
  refine ⟨shiftSpec_ρ11 (d + 2), h.types_eq, h.funcs_eq, h.methods_eq,
    h.methodSets_eq, ?_, Nat.le_refl 11, ?_, ?_, ?_, bodies_ρsh _⟩
  · have hne := h.next_eq
    rw [show (σHIn n seed l iv jv false).nextAddr = 13 from rfl,
      ρ11_ge (d := d) (a := 13) (by omega)] at hne
    show σA.nextAddr = ρ11 (d + 2) 11
    rw [ρ11_ge (d := d + 2) (a := 11) (by omega)]
    omega
  · intro loc
    match loc with
    | .base ⟨a⟩ =>
        by_cases ha : a < 11
        · rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5
              ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10)
            with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact h.lookup_some (l := .base ⟨0⟩) (c := ucell (n : Int)) rfl
          · exact h.lookup_some (l := .base ⟨1⟩) (c := ucell (seed : Int)) rfl
          · exact h.lookup_some (l := .base ⟨2⟩) (c := ucell 0) rfl
          · exact h.lookup_some (l := .base ⟨3⟩) (c := hIHandleCell n) rfl
          · have himg := h.lookup_some (l := .base ⟨4⟩) (c := arrCell n l) rfl
            rw [renCell_arr] at himg
            show Heap.lookup σA.heap (.base ⟨ρ11 (d + 2) 4⟩)
              = some (renameCell (ρ11 (d + 2)) (arrCell n l))
            rw [renCell_arr]
            exact himg
          · exact h.lookup_some (l := .base ⟨5⟩) (c := hIHandleCell n) rfl
          · exact h.lookup_some (l := .base ⟨6⟩)
              (c := ucell ((n : Nat) : Int)) rfl
          · exact h.lookup_some (l := .base ⟨7⟩) (c := bcell false) rfl
          · exact h.lookup_some (l := .base ⟨8⟩) (c := hIHandleCell n) rfl
          · exact h.lookup_some (l := .base ⟨9⟩) (c := intcell iv) rfl
          · exact h.lookup_some (l := .base ⟨10⟩) (c := bcell false) rfl
        · have himg := fs_lookup_none11 h (l := .base ⟨a + 2⟩)
            (lookup_σHIn_ge (by omega))
          have hren1 : renameLoc (ρ11 d) (.base ⟨a + 2⟩)
              = .base ⟨a + 2 + d⟩ := by
            simp [renameLoc, ρ11_ge (d := d) (a := a + 2) (by omega)]
          rw [hren1] at himg
          have hren2 : renameLoc (ρ11 (d + 2)) (.base ⟨a⟩)
              = .base ⟨a + (d + 2)⟩ := by
            simp [renameLoc, ρ11_ge (d := d + 2) (a := a) (by omega)]
          rw [hren2, lookup_σHOut_ge (by omega)]
          show Heap.lookup σA.heap (.base ⟨a + (d + 2)⟩)
            = Heap.lookup (fr ++ [(.base ⟨11 + d⟩, intcell jv),
                (.base ⟨12 + d⟩, bcell false)]) (.base ⟨a + (d + 2)⟩)
          rw [show a + (d + 2) = a + 2 + d from by omega, himg,
            lookup_append]
          cases hfr : Heap.lookup fr (.base ⟨a + 2 + d⟩) with
          | some c => rfl
          | none =>
              show (none : Option HeapCell)
                = Heap.lookup [(.base ⟨11 + d⟩, intcell jv),
                    (.base ⟨12 + d⟩, bcell false)] (.base ⟨a + 2 + d⟩)
              simp [Heap.lookup,
                beq_false_of_ne (base_ne (show 11 + d ≠ a + 2 + d by omega)),
                beq_false_of_ne (base_ne (show 12 + d ≠ a + 2 + d by omega))]
    | .field b tid f =>
        have himg := fs_lookup_none11 h (l := bump2H (.field b tid f))
          (lookup_σHIn_field n seed l iv jv false (bump2H b) tid f)
        rw [← renameLoc_bump2H] at himg
        show Heap.lookup σA.heap (renameLoc (ρ11 (d + 2)) (.field b tid f))
          = Heap.lookup (fr ++ [(.base ⟨11 + d⟩, intcell jv),
              (.base ⟨12 + d⟩, bcell false)])
            (renameLoc (ρ11 (d + 2)) (.field b tid f))
        rw [himg, lookup_append]
        cases hfr : Heap.lookup fr
            (renameLoc (ρ11 (d + 2)) (.field b tid f)) with
        | some c => rfl
        | none => rfl
    | .index b i =>
        have himg := fs_lookup_none11 h (l := bump2H (.index b i))
          (lookup_σHIn_index n seed l iv jv false (bump2H b) i)
        rw [← renameLoc_bump2H] at himg
        show Heap.lookup σA.heap (renameLoc (ρ11 (d + 2)) (.index b i))
          = Heap.lookup (fr ++ [(.base ⟨11 + d⟩, intcell jv),
              (.base ⟨12 + d⟩, bcell false)])
            (renameLoc (ρ11 (d + 2)) (.index b i))
        rw [himg, lookup_append]
        cases hfr : Heap.lookup fr
            (renameLoc (ρ11 (d + 2)) (.index b i)) with
        | some c => rfl
        | none => rfl
  · intro loc c hc
    rw [lookup_append] at hc
    cases hfr : Heap.lookup fr loc with
    | some c0 =>
        rw [hfr] at hc
        have hc' : some c0 = some c := hc
        injection hc' with hcc
        exact hcc ▸ h.frame_pres loc c0 hfr
    | none =>
        rw [hfr] at hc
        have hc' : Heap.lookup [(.base ⟨11 + d⟩, intcell jv),
            (.base ⟨12 + d⟩, bcell false)] loc = some c := hc
        by_cases h4 : (.base ⟨11 + d⟩ : Loc) = loc
        · subst h4
          have hcell : c = intcell jv := by
            simp [Heap.lookup] at hc'
            exact hc'.symm
          subst hcell
          exact h.lookup_some (l := .base ⟨11⟩) (c := intcell jv) rfl
        · by_cases h5 : (.base ⟨12 + d⟩ : Loc) = loc
          · subst h5
            have hcell : c = bcell false := by
              simp [Heap.lookup, beq_false_of_ne h4] at hc'
              exact hc'.symm
            subst hcell
            exact h.lookup_some (l := .base ⟨12⟩) (c := bcell false) rfl
          · exfalso
            simp [Heap.lookup, beq_false_of_ne h4, beq_false_of_ne h5] at hc'
  · intro a
    rw [lookup_append]
    by_cases ha : a < 11
    · rw [ρ11_lt ha]
      have h2 := h.fr_avoid a
      rw [ρ11_lt ha] at h2
      rw [h2]
      show Heap.lookup [(.base ⟨11 + d⟩, intcell jv),
          (.base ⟨12 + d⟩, bcell false)] (.base ⟨a⟩) = none
      simp [Heap.lookup,
        beq_false_of_ne (base_ne (show 11 + d ≠ a by omega)),
        beq_false_of_ne (base_ne (show 12 + d ≠ a by omega))]
    · rw [ρ11_ge (d := d + 2) (a := a) (by omega)]
      have h2 := h.fr_avoid (a + 2)
      rw [ρ11_ge (d := d) (a := a + 2) (by omega)] at h2
      rw [show a + (d + 2) = a + 2 + d from by omega, h2]
      show Heap.lookup [(.base ⟨11 + d⟩, intcell jv),
          (.base ⟨12 + d⟩, bcell false)] (.base ⟨a + 2 + d⟩) = none
      simp [Heap.lookup,
        beq_false_of_ne (base_ne (show 11 + d ≠ a + 2 + d by omega)),
        beq_false_of_ne (base_ne (show 12 + d ≠ a + 2 + d by omega))]

private theorem renCfg_hcmp (d : Nat) (b : Bool) :
    renameConfig (ρ11 d) (.retV (.bool b) hOuterCmpCont)
      = .retV (.bool b) hOuterCmpCont := by
  with_unfolding_all rfl

theorem renCfg_hanchor (d : Nat) :
    renameConfig (ρ11 d) (.next hAfterCallK) = .next hAfterCallK := by
  with_unfolding_all rfl

/-- A canonical segment between shift-fixed configurations transfers
to the true placement (threshold-11 instance). -/
theorem transfer_seg11 {d : Nat} {fr : Heap} {σC σC' σA : ExecState}
    {c c' : Config} {k : Nat} {ch : Choices}
    (hFS : FrameSim (ρ11 d) 11 (11 + d) fr σC σA)
    (hrun : stepFnIter k σC c ch = .ok (c', σC', ch))
    (hc : renameConfig (ρ11 d) c = c) (hc' : renameConfig (ρ11 d) c' = c') :
    ∃ σA', stepFnIter k σA c ch = .ok (c', σA', ch)
      ∧ FrameSim (ρ11 d) 11 (11 + d) fr σC' σA' := by
  have hsim := stepFnIter_sim k hFS c ch
  rw [hc] at hsim
  obtain ⟨rF, hrunF, htrip⟩ := hsim.ok_inv hrun
  obtain ⟨cF, σF, chF⟩ := rF
  obtain ⟨h1, h2, h3⟩ := htrip
  dsimp only at h1 h2 h3
  rw [h1, hc'] at hrunF
  rw [h3] at hrunF
  exact ⟨σF, hrunF, h2⟩

/-! ### The subject outer induction (harness placement): each pass
transferred from the tight placement, rebased, ending at the harness
anchor `.next hAfterCallK` with the surviving frame simulation -/

/-- **The subject outer loop over the true (garbage-laden) harness
run**: from the outer test delivery after `m` passes, the run reaches
the post-subject anchor with the backing fully sorted, delivering the
final frame simulation (existential shift `d`, frame `fr'`, parked
subject counter `ivF`). -/
theorem hs_outer_loop (xs : List Int) (n seed : Nat)
    (hn : n = xs.length)
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (h63 : n < 2 ^ 63) :
    ∀ μ m (σA : ExecState) (fr : Heap), μ = n - (m + 1) →
    FrameSim (ρ11 (2 * m)) 11 (11 + 2 * m) fr
      (σHOut n seed (sortPrefix xs (m + 1)) ((m + 1 : Nat) : Int) false) σA →
    ∀ ch : Choices, ∃ (k : Nat) (σA' : ExecState) (d : Nat) (fr' : Heap)
      (ivF : Int),
      k ≤ (92 * n + 160) * μ + 10 ∧
      stepFnIter k σA
        (.retV (.bool (decide (((m + 1 : Nat) : Int) < ((n : Nat) : Int))))
          hOuterCmpCont) ch
        = .ok (.next hAfterCallK, σA', ch)
      ∧ FrameSim (ρ11 d) 11 (11 + d) fr'
          (σHOut n seed (sortSpec xs) ivF false) σA' := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m σA fr hμ hFS ch
    subst hμ
    rcases Nat.lt_or_ge (m + 1) n with hlt | hge
    · rw [show (decide (((m + 1 : Nat) : Int) < ((n : Nat) : Int))) = true
        from decide_eq_true (by exact_mod_cast (by omega : m + 1 < n))]
      have hplen : (sortSpec (xs.take (m + 1))).length = m + 1 := by
        rw [sortSpec_length, List.length_take]
        omega
      obtain ⟨K, jex, hK, hjex, hpass⟩ := hs_pass_seg n seed
        (sortSpec (xs.take (m + 1))) (xs.drop (m + 2)) (xs.getD (m + 1) 0)
        m h63 hplen (by rw [hplen, List.length_drop]; omega)
        (sortSpec_sorted _)
        (fun x hx => hxs x (List.mem_of_mem_take (mem_sortSpec hx)))
        (hxs _ (getD_mem (by omega)))
        (fun x hx => hxs x (List.mem_of_mem_drop hx)) ch
      rw [← sortPrefix_decomp (by omega)] at hpass
      have hnext : sortPrefix xs (m + 2)
          = insertSpec (xs.getD (m + 1) 0) (sortSpec (xs.take (m + 1)))
            ++ xs.drop (m + 2) := by
        rw [sortPrefix]
        congr 1
        exact sortSpec_take_succ (k := m + 1) (by omega)
      rw [← hnext] at hpass
      obtain ⟨σA', hrunA, hFS'⟩ := transfer_seg11 hFS hpass
        (renCfg_hcmp (2 * m) true) (renCfg_hcmp (2 * m) _)
      have hFS2 := rebaseSim11 hFS'
      obtain ⟨k, σA'', d, fr', ivF, hk, hrun, hFSf⟩ := ih (n - (m + 2))
        (by omega) (m + 1) σA'
        (fr ++ [(.base ⟨11 + 2 * m⟩, intcell ((jex : Nat) : Int)),
          (.base ⟨12 + 2 * m⟩, bcell false)]) rfl
        (by
          have : 2 * m + 2 = 2 * (m + 1) := by omega
          rw [← this]
          exact hFS2) ch
      refine ⟨K + k, σA'', d, fr', ivF, ?_,
        stepFnIter_chain hrunA hrun, hFSf⟩
      have hmul : (92 * n + 160) * (n - (m + 2)) + (92 * n + 160)
          = (92 * n + 160) * (n - (m + 1)) := by
        rw [← Nat.mul_succ]
        congr 1
        omega
      omega
    · rw [show (decide (((m + 1 : Nat) : Int) < ((n : Nat) : Int))) = false
        from decide_eq_false (by exact_mod_cast (by omega : ¬ (m + 1 < n)))]
      have hX := hseg_exitO_raw n seed (sortPrefix xs (m + 1))
        ((m + 1 : Nat) : Int) [] 11 ch
      obtain ⟨σA', hrunA, hFS'⟩ := transfer_seg11 hFS hX
        (renCfg_hcmp (2 * m) false) (renCfg_hanchor (2 * m))
      rw [sortPrefix_full (by omega)] at hFS'
      exact ⟨8, σA', 2 * m, fr, ((m + 1 : Nat) : Int), by omega, hrunA, hFS'⟩


end GoLean.Examples.InsertionSort
