import GoLeanProofs.Sym.UtoaForKit
import GoLeanProofs.Sym.KernelRfl
import GoLeanProofs.StringMem
import GoLeanProofs.Specs.TwinProgram
import GoLeanProofs.Specs.Raft.HandlerEqSym

/-!
# The `utoa` weak span (A4d-SM1 item 2 — the checker spans' cost
driver, in the banked WEAK FORM)

`utoa` (twin-lib.go:74-84) renders a uint64 in decimal; the checker's
violation branches call it (3×) to build the violation string. The
U24 banked weak-form design: the span lemmas need only ∃-STRING
conclusions — bounded completion + frame respect; NO decimal
correctness — because the checker's counters never depend on the
message text. That halves the obligations: the digit loop's invariant
carries "the accumulator holds SOME string", never its bytes.

Layers:
1. **The verbatim body pin** (`utoa_pinned`): the spelled statement
   `utoaBody` — with its digit loop in the `CondFor` schema
   vocabulary — IS the pinned lowering's `utoa` body,
   `findFunctionIn?`-equal by kernel reflexivity. A frontend
   re-lowering that reshapes `utoa` turns the pin red.
2. **The frame entry** (`utoa_enterFrame`): `enterFrame` at the
   twin's tables, symbolic heap/frontier — the two frame cells.
3. **The digit-loop instance** of `CondFor.condFor_loop`
   (`utoa_loop_span`): invariant = flag schedule + `v/10^i` in the
   `v` cell + ∃-string in `s`; `n = dig10 v` iterations.
4. **The body span** (`utoa_body_span`): `.exec utoaBody … .frame` →
   `.returning .frame`, result cell = SOME string, frame respect
   (only `v`/`s`/`$forFirst`/`$res0` cells move; `s`/`$forFirst` are
   fresh), bound `utoaBodyBound v`.
5. **The call span** (`utoa_call_span`): the P-H call combinator
   closed at `utoa` — from the delivered argument value to the
   caller's resumption with the target cell holding SOME string.

The state carrier is `twinSt h na` (the twin's four tables + symbolic
heap/frontier — the round modules' `bfTB` carrier); `twinSt_of_agrees`
transports any `bfTB.Agrees` state into it.

LINEAGE: the loop instance is a Floyd/Hoare invariant through the
`CondFor` schema; the call layer is the P-H call-span combinator
(`stepFnIter_call_span`); the ∃-string weakening is standard
auxiliary-variable abstraction (drop the ghost you do not consume).
-/

namespace GoLean.RaftSeam.UtoaSpan

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceWalk (envB flagCell flagSet stepFn_ref normalize_bool
  lookup_pushScope)
open GoLean.CondFor
open GoLean.Examples.RaftTwin (twinLowered)
open GoLean.StringMem (gs)

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

/-! ## 1. The spelled body (the `CondFor` vocabulary at the digit
loop) and the verbatim pin -/

abbrev tU : Ty := .int .uint64

/-- The digit loop's condition: `v > 0`. -/
def utoaCond : Expr := .greaterCmp (.var "v") (.intLit 0 .uint64)

/-- `s = string(rune('0'+int(v%10))) + s` (twin-lib.go:80), lowered. -/
def sAssign : Stmt :=
  .assign (.var "s")
    (.add
      (.stringFromRune
        (.convert (.int .int32)
          (.add (.intLit 48 .int)
            (.convert (.int .int)
              (.mod (.var "v") (.intLit 10 .uint64))))))
      (.var "s"))

/-- `v /= 10` (twin-lib.go:81), lowered. -/
def vAssign : Stmt :=
  .assign (.var "v") (.div (.var "v") (.intLit 10 .uint64))

/-- The digit-loop body block. -/
def digitBody : Stmt := .block #[] #[.seqn #[sAssign], vAssign]

/-- The `v == 0` early-return branch. -/
def zeroIf : Stmt :=
  .ifThenElse (.eqCmp tU (.var "v") (.intLit 0 .uint64))
    (.block #[] #[.seqn
      #[.assign (.var "$res0") (.stringLit (gs [48])), .returnStmt]])
    (.seqn #[])

/-- `s := ""` (declaration + assignment). -/
def sInit : Stmt :=
  .seqn #[.initialization { id := "s", typ := .string },
    .assign (.var "s") (.stringLit (gs []))]

/-- The `for` block: latch declaration + the `CondFor` while. -/
def forBlock : Stmt :=
  .block #[] #[.initialization { id := "$forFirst", typ := .bool },
    .assign (.var "$forFirst") (.boolLit true),
    cwhile "$forFirst" utoaCond digitBody]

/-- `return s`. -/
def retSeqn : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "s"), .returnStmt]

/-- The whole `utoa` body, spelled. -/
def utoaBody : Stmt := .block #[] #[zeroIf, sInit, forBlock, retSeqn]

/-- The whole `utoa` `Func`, spelled. -/
def utoaFunc : Func :=
  { id := ⟨"utoa"⟩,
    args := #[{ id := "v", typ := tU }],
    results := #[{ id := "$res0", typ := .string }],
    body := utoaBody }

/-- **THE VERBATIM PIN**: the pinned lowering's `utoa` IS the spelled
function — body, signature, flags (`artifacts/probe/utoadump.out`;
kernel-checked equality on the whole `Func`). -/
theorem utoa_pinned :
    findFunctionIn? twinLowered.funcs ⟨"utoa"⟩ = some utoaFunc := by
  kernel_rfl

/-! ## 2. The state carrier and the frame entry -/

/-- The twin-table state at a symbolic heap and frontier (the round
modules' `bfTB` carrier, record form). -/
def twinSt (h : Heap) (na : Nat) : ExecState :=
  { types := twinTypes,
    functions := twinLowered.funcs,
    methods := twinLowered.methods,
    methodSets := twinLowered.methodSets,
    heap := h, nextAddr := na }

/-- Any `bfTB`-agreeing state IS a `twinSt` (the transport from the
window modules' `Agrees` premise). -/
theorem twinSt_of_agrees {σ : ExecState} (hag : bfTB.Agrees σ) :
    σ = twinSt σ.heap σ.nextAddr := by
  obtain ⟨h1, h2, h3, h4⟩ := hag
  cases σ
  simp only [twinSt, bfTB] at *
  subst h1 h2 h3 h4
  rfl

/-- The `utoa` frame environment: results then parameters, one scope
(the trace-verified shape). -/
def utoaEnv (na : Nat) : LocalEnv :=
  [[("$res0", .base ⟨na + 1⟩), ("v", .base ⟨na⟩)]]

/-- The v-cell payload. -/
abbrev uCell (w : Int) : HeapCell := ⟨some tU, .int w .uint64⟩
/-- A string cell payload. -/
abbrev sCell (str : GoString) : HeapCell := ⟨some .string, .string str⟩

/-- Raw `enterFrame` reduct at the twin tables, symbolic heap,
frontier, and argument (normalization left symbolic). -/
private theorem utoa_enterFrame_raw (h : Heap) (na : Nat) (v : Int) :
    enterFrame (twinSt h na) ⟨"utoa"⟩ [.int v .uint64]
      = .ok (utoaFunc, utoaEnv na, [.base ⟨na + 1⟩],
          twinSt
            (Heap.set (Heap.set h (.base ⟨na⟩)
                (uCell (IntKind.normalize .uint64 v)))
              (.base ⟨na + 1⟩) (sCell (gs [])))
            (na + 2)) := by
  kernel_rfl

/-- **The `utoa` frame entry** (in-range argument): the two frame
cells appended at the frontier. -/
theorem utoa_enterFrame (h : Heap) (na : Nat) (v : Nat)
    (hv : v < 2 ^ 64) :
    enterFrame (twinSt h na) ⟨"utoa"⟩ [.int (v : Int) .uint64]
      = .ok (utoaFunc, utoaEnv na, [.base ⟨na + 1⟩],
          twinSt
            (Heap.set (Heap.set h (.base ⟨na⟩) (uCell (v : Int)))
              (.base ⟨na + 1⟩) (sCell (gs [])))
            (na + 2)) := by
  have hraw := utoa_enterFrame_raw h na (v : Int)
  rw [GoLean.SliceMem.unorm_nat_of_lt hv] at hraw
  exact hraw

/-! ## 3. The decimal-length measure and its characterization -/

/-- The digit loop's iteration count: the decimal length of `v`
(0 for 0 — the zero branch returns before the loop). -/
def dig10 (v : Nat) : Nat :=
  if v = 0 then 0 else dig10 (v / 10) + 1
  decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero (by assumption)) (by omega)

theorem dig10_eq (v : Nat) :
    dig10 v = if v = 0 then 0 else dig10 (v / 10) + 1 := by
  rw [dig10]

theorem dig10_zero : dig10 0 = 0 := by
  rw [dig10_eq]
  rfl

theorem dig10_pos {v : Nat} (h : v ≠ 0) :
    dig10 v = dig10 (v / 10) + 1 := by
  rw [dig10_eq v, if_neg h]

/-- Division-tower step: `v / 10^(i+1) = (v / 10^i) / 10` — stated in
the update direction the body fact rewrites with. -/
theorem div_pow_succ (v i : Nat) : v / 10 ^ i / 10 = v / 10 ^ (i + 1) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

/-- **The measure characterization**: the loop condition holds at
iteration `i` exactly below the decimal length. -/
theorem dig10_iff : ∀ v i : Nat, i < dig10 v ↔ 0 < v / 10 ^ i := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro i
    by_cases hv : v = 0
    · subst hv
      rw [dig10_zero, Nat.zero_div]
      omega
    · rw [dig10_pos hv]
      cases i with
      | zero =>
        rw [Nat.pow_zero, Nat.div_one]
        have := Nat.pos_of_ne_zero hv
        omega
      | succ j =>
        have hlt : v / 10 < v :=
          Nat.div_lt_self (Nat.pos_of_ne_zero hv) (by omega)
        have hIH := ih (v / 10) hlt j
        rw [show v / 10 ^ (j + 1) = v / 10 / 10 ^ j from by
          rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 10 (10 ^ j)]]
        omega

/-! ## 4. The conditioned singles the digit body consumes -/

/-- `>` on ints at any kinds (the `applyStrictOp_atLeast_int`
sibling at the general-kind shape). -/
theorem applyStrictOp_greater {σ : ExecState} {a b : Int}
    {k1 k2 : IntKind} :
    applyStrictOp σ .greaterCmp [.int a k1, .int b k2]
      = .ok (.bool (decide (b < a)), σ) := by
  simp only [applyStrictOp, valueGreater, Bind.bind, Except.bind, pure,
    Except.pure, gt_iff_lt]

/-- `+` on two string values is `GoString.append`, state-free. -/
theorem applyStrictOp_add_string {σ : ExecState} {a b : GoString} :
    applyStrictOp σ .add [.string a, .string b]
      = .ok (.string (GoString.append a b), σ) := rfl

/-- `int(x)` conversion of an in-range uint64-kind value: identity on
the payload, kind change only. -/
theorem applyStrictOp_convert_int {σ : ExecState} {a : Nat} {k : IntKind}
    (ha : a < 2 ^ 63) :
    applyStrictOp σ (.convert (.int .int)) [.int (a : Int) k]
      = .ok (.int ((a : Nat) : Int) .int, σ) := by
  have hraw : applyStrictOp σ (.convert (.int .int)) [.int (a : Int) k]
      = .ok (.int (IntKind.normalize .int (a : Int)) .int, σ) := rfl
  rw [hraw, GoLean.SliceMem.inorm_nat_of_lt ha]

/-- A signed-`int32` value in Go range is its own normal form. -/
theorem i32norm_nat_of_lt {x : Nat} (h : x < 2 ^ 31) :
    IntKind.normalize .int32 (x : Int) = (x : Int) := by
  simp only [IntKind.normalize, IntKind.bits?, IntKind.signed, if_true]
  split <;> omega

/-- `int32(x)` conversion of an in-range value. -/
theorem applyStrictOp_convert_i32 {σ : ExecState} {a : Nat} {k : IntKind}
    (ha : a < 2 ^ 31) :
    applyStrictOp σ (.convert (.int .int32)) [.int (a : Int) k]
      = .ok (.int ((a : Nat) : Int) .int32, σ) := by
  have hraw : applyStrictOp σ (.convert (.int .int32)) [.int (a : Int) k]
      = .ok (.int (IntKind.normalize .int32 (a : Int)) .int32, σ) := rfl
  rw [hraw, i32norm_nat_of_lt ha]

/-- String normalization is the identity (any state). -/
theorem normalize_string {σ : ExecState} {s : GoString} :
    normalizeValueForTy σ .string (.string s) = .ok (.string s) := by
  simp only [normalizeValueForTy, normalizeValueForTyFuel,
    typeResolutionFuel, pure, Except.pure]

/-- uint64 normalization of an in-range `Nat`-cast payload is the
identity (any state). -/
theorem normalize_int_u64 {σ : ExecState} {x : Nat} (h : x < 2 ^ 64) :
    normalizeValueForTy σ tU (.int (x : Int) .uint64)
      = .ok (.int (x : Int) .uint64) := by
  simp only [normalizeValueForTy, normalizeValueForTyFuel,
    typeResolutionFuel, GoLean.SliceMem.unorm_nat_of_lt h, pure,
    Except.pure]

/-! ## 5. The digit-loop instance -/

section Loop

variable {envW : LocalEnv} {k : Cont} {lf lv ls : Nat}

/-- The digit-loop invariant (the WEAK FORM: the accumulator holds
SOME string — no decimal modeling). -/
def UtoaInv (lf lv ls v : Nat) (i : Nat) (σ : ExecState) : Prop :=
  Heap.lookup σ.heap (.base ⟨lf⟩) = some (flagCell (i == 0))
    ∧ Heap.lookup σ.heap (.base ⟨lv⟩)
        = some (uCell ((v / 10 ^ i : Nat) : Int))
    ∧ ∃ str, Heap.lookup σ.heap (.base ⟨ls⟩) = some (sCell str)

/-- Cell reads through the glue write (the latch is disjoint from the
`v`/`s` cells). -/
private theorem glue_lookup_ne {i x : Nat} {σ : ExecState}
    (hne : lf ≠ x) {c : HeapCell}
    (h : Heap.lookup σ.heap (.base ⟨x⟩) = some c) :
    Heap.lookup (glueW lf i σ).heap (.base ⟨x⟩) = some c := by
  unfold glueW
  split
  · show Heap.lookup (Heap.set σ.heap (.base ⟨lf⟩) (flagCell false))
      (.base ⟨x⟩) = some c
    rw [lookup_set_other hne]
    exact h
  · exact h

/-- The glued latch reads `false` (written at `i = 0`, carried by the
invariant after). -/
private theorem glue_flag_false {i : Nat} {σ : ExecState}
    (hflag : Heap.lookup σ.heap (.base ⟨lf⟩) = some (flagCell (i == 0))) :
    Heap.lookup (glueW lf i σ).heap (.base ⟨lf⟩)
      = some (flagCell false) := by
  unfold glueW
  split
  · exact lookup_set_self
  · rename_i hi
    have : (i == 0) = false := by simp [hi]
    rw [this] at hflag
    exact hflag

/-- The `utoa` cond fact: 5 steps, state untouched, `v > 0` decided
by the measure characterization. -/
theorem utoa_cond_fact
    (hFV : lf ≠ lv)
    (henvV : LocalEnv.lookup envW "v" = some (.base ⟨lv⟩))
    {v : Nat} (_hv : v < 2 ^ 64) :
    ∀ i σ ch, i ≤ dig10 v → UtoaInv lf lv ls v i σ →
      ∃ m ≤ 5, stepFnIter m (glueW lf i σ)
          (.evalE utoaCond (envB envW)
            (condK "$forFirst" utoaCond digitBody envW k)) ch
        = .ok (.retV (.bool (decide (i < dig10 v)))
            (condK "$forFirst" utoaCond digitBody envW k),
          glueW lf i σ, ch) := by
  intro i σ ch _hin hI
  obtain ⟨hflag, hvc, _⟩ := hI
  have hvg := glue_lookup_ne (i := i) (σ := σ) hFV hvc
  refine ⟨5, Nat.le_refl 5, ?_⟩
  have h1 : stepFnIter 1 (glueW lf i σ) (.evalE utoaCond (envB envW)
      (condK "$forFirst" utoaCond digitBody envW k)) ch
      = .ok (.evalE (.var "v") (envB envW)
          (.strictK .greaterCmp [] [.intLit 0 .uint64] (envB envW)
            (condK "$forFirst" utoaCond digitBody envW k)),
        glueW lf i σ, ch) := by
    with_unfolding_all rfl
  have h2 : stepFnIter 1 (glueW lf i σ) (.evalE (.var "v") (envB envW)
      (.strictK .greaterCmp [] [.intLit 0 .uint64] (envB envW)
        (condK "$forFirst" utoaCond digitBody envW k))) ch
      = .ok (.retV (.int ((v / 10 ^ i : Nat) : Int) .uint64)
          (.strictK .greaterCmp [] [.intLit 0 .uint64] (envB envW)
            (condK "$forFirst" utoaCond digitBody envW k)),
        glueW lf i σ, ch) :=
    stepFnIter_one (stepFn_var
      (henv := (lookup_pushScope envW "v").trans henvV) (hlook := hvg))
  have h3 : stepFnIter 2 (glueW lf i σ)
      (.retV (.int ((v / 10 ^ i : Nat) : Int) .uint64)
        (.strictK .greaterCmp [] [.intLit 0 .uint64] (envB envW)
          (condK "$forFirst" utoaCond digitBody envW k))) ch
      = .ok (.retV (.int 0 .uint64)
          (.strictK .greaterCmp [.int ((v / 10 ^ i : Nat) : Int) .uint64]
            [] (envB envW)
            (condK "$forFirst" utoaCond digitBody envW k)),
        glueW lf i σ, ch) := by
    with_unfolding_all rfl
  have h4 : stepFnIter 1 (glueW lf i σ) (.retV (.int 0 .uint64)
      (.strictK .greaterCmp [.int ((v / 10 ^ i : Nat) : Int) .uint64]
        [] (envB envW)
        (condK "$forFirst" utoaCond digitBody envW k))) ch
      = .ok (.retV (.bool (decide (i < dig10 v)))
          (condK "$forFirst" utoaCond digitBody envW k),
        glueW lf i σ, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.int 0 .uint64,
        GoValue.int ((v / 10 ^ i : Nat) : Int) .uint64])
      = [GoValue.int ((v / 10 ^ i : Nat) : Int) .uint64,
         GoValue.int 0 .uint64] from rfl,
      applyStrictOp_greater]
    have hd : decide ((0 : Int) < ((v / 10 ^ i : Nat) : Int))
        = decide (i < dig10 v) := by
      have hiff := dig10_iff v i
      rcases Nat.lt_or_ge i (dig10 v) with h | h
      · rw [decide_eq_true (show (0 : Int) < ((v / 10 ^ i : Nat) : Int)
            by have := hiff.mp h; omega),
          decide_eq_true h]
      · rw [decide_eq_false (show ¬((0 : Int) < ((v / 10 ^ i : Nat) : Int))
            by intro hc
               have : 0 < v / 10 ^ i := by omega
               have := hiff.mpr this
               omega),
          decide_eq_false (by omega)]
    rw [hd]
  exact stepFnIter_chain h1 (stepFnIter_chain h2
    (stepFnIter_chain h3 h4))

/-- The digit-body post-state: `s`-cell appended, `v`-cell divided. -/
def digitPost (lv ls : Nat) (w : Nat) (cat : GoString)
    (σg : ExecState) : ExecState :=
  { σg with heap := Heap.set (Heap.set σg.heap (.base ⟨ls⟩) (sCell cat)) (.base ⟨lv⟩) (uCell ((w / 10 : Nat) : Int)) }

/-- The `utoa` digit-body fact: 44 steps (trace-verified), the digit
prepended to the accumulator (∃-string), `v` divided by 10. -/
theorem utoa_body_fact
    (hFV : lf ≠ lv) (hFS : lf ≠ ls) (hVS : lv ≠ ls)
    (henvV : LocalEnv.lookup envW "v" = some (.base ⟨lv⟩))
    (henvS : LocalEnv.lookup envW "s" = some (.base ⟨ls⟩))
    {v : Nat} (hv : v < 2 ^ 64) :
    ∀ i σ ch, i < dig10 v → UtoaInv lf lv ls v i σ →
      ∃ m ≤ 44, ∃ cat,
        stepFnIter m (glueW lf i σ)
            (bodyCfg "$forFirst" utoaCond digitBody envW k) ch
          = .ok (bodyDoneCfg "$forFirst" utoaCond digitBody envW k,
              digitPost lv ls (v / 10 ^ i) cat (glueW lf i σ), ch)
        ∧ UtoaInv lf lv ls v (i + 1)
            (digitPost lv ls (v / 10 ^ i) cat (glueW lf i σ)) := by
  intro i σ ch hlt hI
  obtain ⟨hflag, hvc, str, hsc⟩ := hI
  -- the current value and its ranges
  obtain ⟨w, hw⟩ : ∃ w, v / 10 ^ i = w := ⟨_, rfl⟩
  rw [hw] at hvc
  rw [hw]
  have hw64 : w < 2 ^ 64 := by
    have := Nat.div_le_self v (10 ^ i)
    omega
  have hd10 : w % 10 < 10 := Nat.mod_lt _ (by omega)
  -- cell reads at the glued state
  have hvg := glue_lookup_ne (i := i) (σ := σ) hFV hvc
  have hsg := glue_lookup_ne (i := i) (σ := σ) hFS hsc
  have hfg := glue_flag_false (i := i) (σ := σ) hflag
  -- the two environment paths (through the block scope + body scope)
  have henvV2 : LocalEnv.lookup ([] :: envB envW) "v"
      = some (.base ⟨lv⟩) :=
    (lookup_pushScope (envB envW) "v").trans
      ((lookup_pushScope envW "v").trans henvV)
  have henvS2 : LocalEnv.lookup ([] :: envB envW) "s"
      = some (.base ⟨ls⟩) :=
    (lookup_pushScope (envB envW) "s").trans
      ((lookup_pushScope envW "s").trans henvS)
  -- continuation abbreviations
  let envBB : LocalEnv := [] :: envB envW
  let KL : Cont := loopK "$forFirst" utoaCond digitBody envW k
  let Kout : Cont := .seq [] (envB envW) KL
  let Kblk : Cont := .seq [vAssign] envBB Kout
  let K3 : Cont := .seq [] envBB Kout
  -- the rune expression (the s-assign's RHS spine)
  let runeE : Expr := .stringFromRune (.convert (.int .int32)
    (.add (.intLit 48 .int)
      (.convert (.int .int) (.mod (.var "v") (.intLit 10 .uint64)))))
  -- C1: body entry → the s-ref (5 steps: block, pop, splice, pop,
  -- assign entry — splice/pop via the kit singles, whose env-equality
  -- checks do not reduce at a symbolic env)
  have hC1 : stepFnIter 5 (glueW lf i σ)
      (bodyCfg "$forFirst" utoaCond digitBody envW k) ch
      = .ok (.evalE (.ref "s") envBB
          (.tgtOpK (.chain []) [] [] [] [] .vals
            [.add runeE (.var "s")] [] (.seqn #[]) envBB Kblk),
        glueW lf i σ, ch) := by
    have s1 : stepFnIter 1 (glueW lf i σ)
        (bodyCfg "$forFirst" utoaCond digitBody envW k) ch
        = .ok (.next (.seq [.seqn #[sAssign], vAssign] envBB Kout),
          glueW lf i σ, ch) := by
      with_unfolding_all rfl
    have s2 : stepFnIter 3 (glueW lf i σ)
        (.next (.seq [.seqn #[sAssign], vAssign] envBB Kout)) ch
        = .ok (.exec sAssign envBB Kblk, glueW lf i σ, ch) :=
      stepFnIter_chain (stepFnIter_one stepFn_seq_pop)
        (stepFnIter_splice_pop (ss := #[sAssign]) rfl)
    have s3 : stepFnIter 1 (glueW lf i σ) (.exec sAssign envBB Kblk) ch
        = .ok (.evalE (.ref "s") envBB
            (.tgtOpK (.chain []) [] [] [] [] .vals
              [.add runeE (.var "s")] [] (.seqn #[]) envBB Kblk),
          glueW lf i σ, ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain s1 (stepFnIter_chain s2 s3)
  -- the s-ref (conditioned)
  have hC2 : stepFnIter 1 (glueW lf i σ) (.evalE (.ref "s") envBB
      (.tgtOpK (.chain []) [] [] [] [] .vals
        [.add runeE (.var "s")] [] (.seqn #[]) envBB Kblk)) ch
      = .ok (.retV (.addr (.base ⟨ls⟩))
          (.tgtOpK (.chain []) [] [] [] [] .vals
            [.add runeE (.var "s")] [] (.seqn #[]) envBB Kblk),
        glueW lf i σ, ch) :=
    stepFnIter_one (stepFn_ref henvS2)
  -- C3: dispatch down to the v-read (9 pure steps)
  have hC3 : stepFnIter 9 (glueW lf i σ) (.retV (.addr (.base ⟨ls⟩))
      (.tgtOpK (.chain []) [] [] [] [] .vals
        [.add runeE (.var "s")] [] (.seqn #[]) envBB Kblk)) ch
      = .ok (.evalE (.var "v") envBB
          (.strictK .mod [] [.intLit 10 .uint64] envBB
            (.strictK (.convert (.int .int)) [] [] envBB
              (.strictK .add [.int 48 .int] [] envBB
                (.strictK (.convert (.int .int32)) [] [] envBB
                  (.strictK .stringFromRune [] [] envBB
                    (.strictK .add [] [.var "s"] envBB
                      (.rhsK .vals
                        [.chain (.addr (.base ⟨ls⟩)) [] []] [] []
                        (.seqn #[]) envBB Kblk))))))),
        glueW lf i σ, ch) := by
    with_unfolding_all rfl
  -- the v-read (conditioned)
  have hC4 : stepFnIter 1 (glueW lf i σ) (.evalE (.var "v") envBB
      (.strictK .mod [] [.intLit 10 .uint64] envBB
        (.strictK (.convert (.int .int)) [] [] envBB
          (.strictK .add [.int 48 .int] [] envBB
            (.strictK (.convert (.int .int32)) [] [] envBB
              (.strictK .stringFromRune [] [] envBB
                (.strictK .add [] [.var "s"] envBB
                  (.rhsK .vals [.chain (.addr (.base ⟨ls⟩)) [] []] [] []
                    (.seqn #[]) envBB Kblk)))))))) ch
      = .ok (.retV (.int ((w : Nat) : Int) .uint64)
          (.strictK .mod [] [.intLit 10 .uint64] envBB
            (.strictK (.convert (.int .int)) [] [] envBB
              (.strictK .add [.int 48 .int] [] envBB
                (.strictK (.convert (.int .int32)) [] [] envBB
                  (.strictK .stringFromRune [] [] envBB
                    (.strictK .add [] [.var "s"] envBB
                      (.rhsK .vals
                        [.chain (.addr (.base ⟨ls⟩)) [] []] [] []
                        (.seqn #[]) envBB Kblk))))))),
        glueW lf i σ, ch) :=
    stepFnIter_one (stepFn_var (henv := henvV2) (hlook := hvg))
  -- C5: the 10-literal (2 pure steps)
  have hC5 : stepFnIter 2 (glueW lf i σ)
      (.retV (.int ((w : Nat) : Int) .uint64)
        (.strictK .mod [] [.intLit 10 .uint64] envBB
          (.strictK (.convert (.int .int)) [] [] envBB
            (.strictK .add [.int 48 .int] [] envBB
              (.strictK (.convert (.int .int32)) [] [] envBB
                (.strictK .stringFromRune [] [] envBB
                  (.strictK .add [] [.var "s"] envBB
                    (.rhsK .vals [.chain (.addr (.base ⟨ls⟩)) [] []]
                      [] [] (.seqn #[]) envBB Kblk)))))))) ch
      = .ok (.retV (.int 10 .uint64)
          (.strictK .mod [.int ((w : Nat) : Int) .uint64] [] envBB
            (.strictK (.convert (.int .int)) [] [] envBB
              (.strictK .add [.int 48 .int] [] envBB
                (.strictK (.convert (.int .int32)) [] [] envBB
                  (.strictK .stringFromRune [] [] envBB
                    (.strictK .add [] [.var "s"] envBB
                      (.rhsK .vals
                        [.chain (.addr (.base ⟨ls⟩)) [] []] [] []
                        (.seqn #[]) envBB Kblk))))))),
        glueW lf i σ, ch) := by
    with_unfolding_all rfl
  -- C6: the four strict applications (mod, int-convert, add,
  -- int32-convert) + the rune encoding (5 conditioned steps)
  let T1 : Cont := .rhsK .vals [.chain (.addr (.base ⟨ls⟩)) [] []] [] []
    (.seqn #[]) envBB Kblk
  let T2 : Cont := .strictK .add [] [.var "s"] envBB T1
  let T3 : Cont := .strictK .stringFromRune [] [] envBB T2
  let T4 : Cont := .strictK (.convert (.int .int32)) [] [] envBB T3
  let T5 : Cont := .strictK .add [.int 48 .int] [] envBB T4
  let T6 : Cont := .strictK (.convert (.int .int)) [] [] envBB T5
  have hC6 : stepFnIter 5 (glueW lf i σ) (.retV (.int 10 .uint64)
      (.strictK .mod [.int ((w : Nat) : Int) .uint64] [] envBB T6)) ch
      = .ok (.retV (.string (gs [UInt8.ofNat (48 + w % 10)])) T2,
        glueW lf i σ, ch) := by
    have s1 : stepFnIter 1 (glueW lf i σ) (.retV (.int 10 .uint64)
        (.strictK .mod [.int ((w : Nat) : Int) .uint64] [] envBB T6)) ch
        = .ok (.retV (.int ((w % 10 : Nat) : Int) .uint64) T6,
          glueW lf i σ, ch) := by
      refine stepFnIter_one (stepFn_strict_apply (h := ?_))
      rw [show (List.reverse [GoValue.int 10 .uint64,
          GoValue.int ((w : Nat) : Int) .uint64])
        = [GoValue.int ((w : Nat) : Int) .uint64,
           GoValue.int 10 .uint64] from rfl]
      exact GoLean.SliceMem.applyStrictOp_mod_u64 (a := w) (b := 10)
        (by omega) (by omega)
    have s2 : stepFnIter 1 (glueW lf i σ)
        (.retV (.int ((w % 10 : Nat) : Int) .uint64) T6) ch
        = .ok (.retV (.int ((w % 10 : Nat) : Int) .int) T5,
          glueW lf i σ, ch) := by
      refine stepFnIter_one (stepFn_strict_apply (h := ?_))
      rw [show (List.reverse [GoValue.int ((w % 10 : Nat) : Int)
          .uint64]) = [GoValue.int ((w % 10 : Nat) : Int) .uint64]
        from rfl]
      exact applyStrictOp_convert_int (a := w % 10) (by omega)
    have s3 : stepFnIter 1 (glueW lf i σ)
        (.retV (.int ((w % 10 : Nat) : Int) .int) T5) ch
        = .ok (.retV (.int (((48 + w % 10 : Nat)) : Int) .int) T4,
          glueW lf i σ, ch) := by
      refine stepFnIter_one (stepFn_strict_apply (h := ?_))
      rw [show (List.reverse [GoValue.int ((w % 10 : Nat) : Int) .int,
          GoValue.int 48 .int])
        = [GoValue.int 48 .int,
           GoValue.int ((w % 10 : Nat) : Int) .int] from rfl]
      rw [GoLean.SliceWalk.applyStrictOp_add_int (a := 48)
        (b := ((w % 10 : Nat) : Int)) (by omega) (by omega)]
      rw [show (48 : Int) + ((w % 10 : Nat) : Int)
        = (((48 + w % 10 : Nat)) : Int) from by omega]
    have s4 : stepFnIter 1 (glueW lf i σ)
        (.retV (.int (((48 + w % 10 : Nat)) : Int) .int) T4) ch
        = .ok (.retV (.int (((48 + w % 10 : Nat)) : Int) .int32) T3,
          glueW lf i σ, ch) := by
      refine stepFnIter_one (stepFn_strict_apply (h := ?_))
      rw [show (List.reverse [GoValue.int (((48 + w % 10 : Nat)) : Int)
          .int]) = [GoValue.int (((48 + w % 10 : Nat)) : Int) .int]
        from rfl]
      exact applyStrictOp_convert_i32 (a := 48 + w % 10) (by omega)
    have s5 : stepFnIter 1 (glueW lf i σ)
        (.retV (.int (((48 + w % 10 : Nat)) : Int) .int32) T3) ch
        = .ok (.retV (.string (gs [UInt8.ofNat (48 + w % 10)])) T2,
          glueW lf i σ, ch) := by
      refine stepFnIter_one (stepFn_strict_apply (h := ?_))
      rw [show (List.reverse [GoValue.int (((48 + w % 10 : Nat)) : Int)
          .int32]) = [GoValue.int (((48 + w % 10 : Nat)) : Int) .int32]
        from rfl]
      exact GoLean.StringMem.applyStrictOp_stringFromRune_ascii
        (c := 48 + w % 10) (ik := .int32) (by omega)
    exact stepFnIter_chain s1 (stepFnIter_chain s2 (stepFnIter_chain s3
      (stepFnIter_chain s4 s5)))
  -- C7: the s-read dispatch + read (1 pure + 1 conditioned)
  have hC7 : stepFnIter 1 (glueW lf i σ)
      (.retV (.string (gs [UInt8.ofNat (48 + w % 10)]))
        (.strictK .add [] [.var "s"] envBB
          (.rhsK .vals [.chain (.addr (.base ⟨ls⟩)) [] []] [] []
            (.seqn #[]) envBB Kblk))) ch
      = .ok (.evalE (.var "s") envBB
          (.strictK .add [.string (gs [UInt8.ofNat (48 + w % 10)])] []
            envBB (.rhsK .vals [.chain (.addr (.base ⟨ls⟩)) [] []] [] []
              (.seqn #[]) envBB Kblk)),
        glueW lf i σ, ch) := by
    with_unfolding_all rfl
  have hC8 : stepFnIter 1 (glueW lf i σ) (.evalE (.var "s") envBB
      (.strictK .add [.string (gs [UInt8.ofNat (48 + w % 10)])] []
        envBB (.rhsK .vals [.chain (.addr (.base ⟨ls⟩)) [] []] [] []
          (.seqn #[]) envBB Kblk))) ch
      = .ok (.retV (.string str)
          (.strictK .add [.string (gs [UInt8.ofNat (48 + w % 10)])] []
            envBB (.rhsK .vals [.chain (.addr (.base ⟨ls⟩)) [] []] [] []
              (.seqn #[]) envBB Kblk)),
        glueW lf i σ, ch) :=
    stepFnIter_one (stepFn_var (henv := henvS2) (hlook := hsg))
  -- C9: the concat + rhs drain (1 conditioned + 1 pure)
  let cat : GoString :=
    GoString.append (gs [UInt8.ofNat (48 + w % 10)]) str
  have hC9 : stepFnIter 1 (glueW lf i σ) (.retV (.string str)
      (.strictK .add [.string (gs [UInt8.ofNat (48 + w % 10)])] []
        envBB (.rhsK .vals [.chain (.addr (.base ⟨ls⟩)) [] []] [] []
          (.seqn #[]) envBB Kblk))) ch
      = .ok (.retV (.string cat)
          (.rhsK .vals [.chain (.addr (.base ⟨ls⟩)) [] []] [] []
            (.seqn #[]) envBB Kblk),
        glueW lf i σ, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.string str,
        GoValue.string (gs [UInt8.ofNat (48 + w % 10)])])
      = [GoValue.string (gs [UInt8.ofNat (48 + w % 10)]),
         GoValue.string str] from rfl]
    exact applyStrictOp_add_string
  have hC10 : stepFnIter 1 (glueW lf i σ) (.retV (.string cat)
      (.rhsK .vals [.chain (.addr (.base ⟨ls⟩)) [] []] [] []
        (.seqn #[]) envBB Kblk)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨ls⟩)) [] []]
          [.string cat] (.seqn #[]) envBB Kblk),
        glueW lf i σ, ch) := by
    with_unfolding_all rfl
  -- C11: the s-store (conditioned)
  let σ1 : ExecState := { (glueW lf i σ) with
    heap := Heap.set (glueW lf i σ).heap (.base ⟨ls⟩) (sCell cat) }
  have hC11 : stepFnIter 1 (glueW lf i σ) (.next (.storeK
      [.chain (.addr (.base ⟨ls⟩)) [] []] [.string cat] (.seqn #[])
      envBB Kblk)) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) envBB Kblk), σ1, ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_addr (ty := .string) (old := .string str)
        (hlook := hsg) (hnorm := normalize_string)))
  -- C12: drain + pop to the v-assign, then to the v-ref (4 steps:
  -- storeK nil, splice, pop, assign entry)
  have hC12 : stepFnIter 4 σ1
      (.next (.storeK [] [] (.seqn #[]) envBB Kblk)) ch
      = .ok (.evalE (.ref "v") envBB
          (.tgtOpK (.chain []) [] [] [] [] .vals
            [.div (.var "v") (.intLit 10 .uint64)] [] (.seqn #[])
            envBB K3), σ1, ch) := by
    have s1 : stepFnIter 3 σ1
        (.next (.storeK [] [] (.seqn #[]) envBB Kblk)) ch
        = .ok (.exec vAssign envBB K3, σ1, ch) :=
      stepFnIter_chain (stepFnIter_one stepFn_storeK_nil)
        (stepFnIter_splice_pop (ss := #[]) rfl)
    have s2 : stepFnIter 1 σ1 (.exec vAssign envBB K3) ch
        = .ok (.evalE (.ref "v") envBB
            (.tgtOpK (.chain []) [] [] [] [] .vals
              [.div (.var "v") (.intLit 10 .uint64)] [] (.seqn #[])
              envBB K3), σ1, ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain s1 s2
  -- the v-ref + dispatch + v-read (post-s-store)
  have hvc1 : Heap.lookup σ1.heap (.base ⟨lv⟩)
      = some (uCell ((w : Nat) : Int)) := by
    show Heap.lookup (Heap.set (glueW lf i σ).heap (.base ⟨ls⟩)
      (sCell cat)) (.base ⟨lv⟩) = _
    rw [lookup_set_other (Ne.symm hVS)]
    exact hvg
  have hC13 : stepFnIter 1 σ1 (.evalE (.ref "v") envBB
      (.tgtOpK (.chain []) [] [] [] [] .vals
        [.div (.var "v") (.intLit 10 .uint64)] [] (.seqn #[])
        envBB K3)) ch
      = .ok (.retV (.addr (.base ⟨lv⟩))
          (.tgtOpK (.chain []) [] [] [] [] .vals
            [.div (.var "v") (.intLit 10 .uint64)] [] (.seqn #[])
            envBB K3), σ1, ch) :=
    stepFnIter_one (stepFn_ref henvV2)
  have hC14 : stepFnIter 2 σ1 (.retV (.addr (.base ⟨lv⟩))
      (.tgtOpK (.chain []) [] [] [] [] .vals
        [.div (.var "v") (.intLit 10 .uint64)] [] (.seqn #[])
        envBB K3)) ch
      = .ok (.evalE (.var "v") envBB
          (.strictK .div [] [.intLit 10 .uint64] envBB
            (.rhsK .vals [.chain (.addr (.base ⟨lv⟩)) [] []] [] []
              (.seqn #[]) envBB K3)), σ1, ch) := by
    with_unfolding_all rfl
  have hC15 : stepFnIter 1 σ1 (.evalE (.var "v") envBB
      (.strictK .div [] [.intLit 10 .uint64] envBB
        (.rhsK .vals [.chain (.addr (.base ⟨lv⟩)) [] []] [] []
          (.seqn #[]) envBB K3))) ch
      = .ok (.retV (.int ((w : Nat) : Int) .uint64)
          (.strictK .div [] [.intLit 10 .uint64] envBB
            (.rhsK .vals [.chain (.addr (.base ⟨lv⟩)) [] []] [] []
              (.seqn #[]) envBB K3)), σ1, ch) :=
    stepFnIter_one (stepFn_var (henv := henvV2) (hlook := hvc1))
  have hC16 : stepFnIter 2 σ1 (.retV (.int ((w : Nat) : Int) .uint64)
      (.strictK .div [] [.intLit 10 .uint64] envBB
        (.rhsK .vals [.chain (.addr (.base ⟨lv⟩)) [] []] [] []
          (.seqn #[]) envBB K3))) ch
      = .ok (.retV (.int 10 .uint64)
          (.strictK .div [.int ((w : Nat) : Int) .uint64] [] envBB
            (.rhsK .vals [.chain (.addr (.base ⟨lv⟩)) [] []] [] []
              (.seqn #[]) envBB K3)), σ1, ch) := by
    with_unfolding_all rfl
  have hC17 : stepFnIter 1 σ1 (.retV (.int 10 .uint64)
      (.strictK .div [.int ((w : Nat) : Int) .uint64] [] envBB
        (.rhsK .vals [.chain (.addr (.base ⟨lv⟩)) [] []] [] []
          (.seqn #[]) envBB K3))) ch
      = .ok (.retV (.int ((w / 10 : Nat) : Int) .uint64)
          (.rhsK .vals [.chain (.addr (.base ⟨lv⟩)) [] []] [] []
            (.seqn #[]) envBB K3), σ1, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.int 10 .uint64,
        GoValue.int ((w : Nat) : Int) .uint64])
      = [GoValue.int ((w : Nat) : Int) .uint64,
         GoValue.int 10 .uint64] from rfl]
    exact GoLean.SliceMem.applyStrictOp_div_u64 (a := w) (b := 10) (by omega) hw64
  have hC18 : stepFnIter 1 σ1
      (.retV (.int ((w / 10 : Nat) : Int) .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨lv⟩)) [] []] [] []
          (.seqn #[]) envBB K3)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨lv⟩)) [] []]
          [.int ((w / 10 : Nat) : Int) .uint64] (.seqn #[]) envBB K3),
        σ1, ch) := by
    with_unfolding_all rfl
  -- C19: the v-store (conditioned)
  have hC19 : stepFnIter 1 σ1 (.next (.storeK
      [.chain (.addr (.base ⟨lv⟩)) [] []]
      [.int ((w / 10 : Nat) : Int) .uint64] (.seqn #[]) envBB K3)) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) envBB K3),
        digitPost lv ls w cat (glueW lf i σ), ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_addr (ty := tU) (old := .int ((w : Nat) : Int) .uint64)
        (hlook := hvc1)
        (hnorm := normalize_int_u64 (by
          have := Nat.div_le_self w 10
          omega))))
  -- C20: drain to the body-done configuration (3 steps: storeK nil,
  -- splice, empty-seq pop)
  have hC20 : stepFnIter 3 (digitPost lv ls w cat (glueW lf i σ))
      (.next (.storeK [] [] (.seqn #[]) envBB K3)) ch
      = .ok (bodyDoneCfg "$forFirst" utoaCond digitBody envW k,
        digitPost lv ls w cat (glueW lf i σ), ch) := by
    have s1 : stepFnIter 2 (digitPost lv ls w cat (glueW lf i σ))
        (.next (.storeK [] [] (.seqn #[]) envBB K3)) ch
        = .ok (.next (.seq [] envBB Kout),
          digitPost lv ls w cat (glueW lf i σ), ch) :=
      stepFnIter_chain (stepFnIter_one stepFn_storeK_nil)
        (stepFnIter_one stepFn_seqn_splice)
    have s2 : stepFnIter 1 (digitPost lv ls w cat (glueW lf i σ))
        (.next (.seq [] envBB Kout)) ch
        = .ok (bodyDoneCfg "$forFirst" utoaCond digitBody envW k,
          digitPost lv ls w cat (glueW lf i σ), ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain s1 s2
  -- compose
  have hall := stepFnIter_chain hC1 (stepFnIter_chain hC2
    (stepFnIter_chain hC3 (stepFnIter_chain hC4 (stepFnIter_chain hC5
      (stepFnIter_chain hC6 (stepFnIter_chain hC7 (stepFnIter_chain hC8
        (stepFnIter_chain hC9 (stepFnIter_chain hC10
          (stepFnIter_chain hC11 (stepFnIter_chain hC12
            (stepFnIter_chain hC13 (stepFnIter_chain hC14
              (stepFnIter_chain hC15 (stepFnIter_chain hC16
                (stepFnIter_chain hC17 (stepFnIter_chain hC18
                  (stepFnIter_chain hC19 hC20))))))))))))))))))
  refine ⟨_, by omega, cat, hall, ?_, ?_, cat, ?_⟩
  · -- the latch at i + 1
    show Heap.lookup (digitPost lv ls w cat (glueW lf i σ)).heap
      (.base ⟨lf⟩) = some (flagCell ((i + 1) == 0))
    unfold digitPost
    show Heap.lookup (Heap.set (Heap.set (glueW lf i σ).heap
      (.base ⟨ls⟩) (sCell cat)) (.base ⟨lv⟩)
      (uCell ((w / 10 : Nat) : Int))) (.base ⟨lf⟩) = _
    rw [lookup_set_other (Ne.symm hFV), lookup_set_other (Ne.symm hFS)]
    have : ((i + 1) == 0) = false := by simp
    rw [this]
    exact hfg
  · -- the v-cell at i + 1
    show Heap.lookup (digitPost lv ls w cat (glueW lf i σ)).heap
      (.base ⟨lv⟩) = some (uCell ((v / 10 ^ (i + 1) : Nat) : Int))
    unfold digitPost
    show Heap.lookup (Heap.set (Heap.set (glueW lf i σ).heap
      (.base ⟨ls⟩) (sCell cat)) (.base ⟨lv⟩)
      (uCell ((w / 10 : Nat) : Int))) (.base ⟨lv⟩) = _
    rw [lookup_set_self, ← hw, div_pow_succ]
  · -- the accumulator holds a string
    show Heap.lookup (digitPost lv ls w cat (glueW lf i σ)).heap
      (.base ⟨ls⟩) = some (sCell cat)
    unfold digitPost
    show Heap.lookup (Heap.set (Heap.set (glueW lf i σ).heap
      (.base ⟨ls⟩) (sCell cat)) (.base ⟨lv⟩)
      (uCell ((w / 10 : Nat) : Int))) (.base ⟨ls⟩) = _
    rw [lookup_set_other hVS, lookup_set_self]

/-! ### The frame-carrying invariant and the composed loop span -/

/-- The frame clause the whole-body span threads through the loop:
every cell OUTSIDE the loop's three working cells matches the
reference heap, the frontier is parked, and the table components
agree with the twin pack (heap-only steps preserve all three). -/
def UtoaFrame (lf lv ls : Nat) (href : Heap) (naR : Nat)
    (σ : ExecState) : Prop :=
  (∀ x : Nat, x ≠ lf → x ≠ lv → x ≠ ls →
    Heap.lookup σ.heap (.base ⟨x⟩) = Heap.lookup href (.base ⟨x⟩))
    ∧ σ.nextAddr = naR ∧ bfTB.Agrees σ

theorem agrees_set_heap {σ : ExecState} {h : Heap}
    (hag : bfTB.Agrees σ) : bfTB.Agrees { σ with heap := h } := hag

/-- `glueW` preserves the frame clause (it writes only the latch). -/
theorem utoaFrame_glueW {lf lv ls : Nat} {href : Heap} {naR i : Nat}
    {σ : ExecState} (hF : UtoaFrame lf lv ls href naR σ) :
    UtoaFrame lf lv ls href naR (glueW lf i σ) := by
  obtain ⟨hfr, hna, hag⟩ := hF
  unfold glueW
  split
  · refine ⟨?_, hna, agrees_set_heap hag⟩
    intro x hxf hxv hxs
    show Heap.lookup (Heap.set σ.heap (.base ⟨lf⟩) (flagCell false))
      (.base ⟨x⟩) = _
    rw [lookup_set_other (fun he => hxf he.symm)]
    exact hfr x hxf hxv hxs
  · exact ⟨hfr, hna, hag⟩

/-- `digitPost` preserves the frame clause (it writes only the `s`
and `v` cells). -/
theorem utoaFrame_digitPost {lf lv ls : Nat} {href : Heap}
    {naR w : Nat} {cat : GoString} {σ : ExecState}
    (hF : UtoaFrame lf lv ls href naR σ) :
    UtoaFrame lf lv ls href naR (digitPost lv ls w cat σ) := by
  obtain ⟨hfr, hna, hag⟩ := hF
  refine ⟨?_, hna, agrees_set_heap hag⟩
  intro x hxf hxv hxs
  show Heap.lookup (Heap.set (Heap.set σ.heap (.base ⟨ls⟩) (sCell cat))
    (.base ⟨lv⟩) (uCell ((w / 10 : Nat) : Int))) (.base ⟨x⟩) = _
  rw [lookup_set_other (fun he => hxv he.symm),
    lookup_set_other (fun he => hxs he.symm)]
  exact hfr x hxf hxv hxs

/-- **THE `utoa` DIGIT-LOOP SPAN** (the `CondFor` schema instance):
from the loop head at the initial invariant, the whole loop completes
within `74 · dig10 v + 29` steps, delivering `.next k` with the
invariant and frame clause at `dig10 v`. -/
theorem utoa_loop_span
    (hFV : lf ≠ lv) (hFS : lf ≠ ls) (hVS : lv ≠ ls)
    (henvF : LocalEnv.lookup envW "$forFirst" = some (.base ⟨lf⟩))
    (henvV : LocalEnv.lookup envW "v" = some (.base ⟨lv⟩))
    (henvS : LocalEnv.lookup envW "s" = some (.base ⟨ls⟩))
    {v : Nat} (hv : v < 2 ^ 64) {href : Heap} {naR : Nat} :
    ∀ σ ch, UtoaInv lf lv ls v 0 σ →
      UtoaFrame lf lv ls href naR σ →
      ∃ m ≤ 74 * dig10 v + 29, ∃ σf,
        UtoaInv lf lv ls v (dig10 v) σf
        ∧ UtoaFrame lf lv ls href naR σf
        ∧ stepFnIter m σ
            (headCfg "$forFirst" utoaCond digitBody envW k) ch
          = .ok (.next k, glueW lf (dig10 v) σf, ch) := by
  intro σ ch hI hF
  have h := condFor_loop (cond := utoaCond) (body := digitBody)
    (k := k) henvF (n := dig10 v) (bC := 5) (bB := 44)
    (fun i σ' => UtoaInv lf lv ls v i σ'
      ∧ UtoaFrame lf lv ls href naR σ')
    (fun i σ' _ hI' => hI'.1.1)
    (fun i σ' ch' hin hI' =>
      utoa_cond_fact hFV henvV hv i σ' ch' hin hI'.1)
    (fun i σ' ch' hilt hI' => by
      obtain ⟨m, hm, cat, hrun, hinv'⟩ :=
        utoa_body_fact hFV hFS hVS henvV henvS hv i σ' ch' hilt hI'.1
      exact ⟨m, hm, digitPost lv ls (v / 10 ^ i) cat (glueW lf i σ'),
        hrun, hinv', utoaFrame_digitPost (utoaFrame_glueW hI'.2)⟩)
    0 σ ch (Nat.zero_le _) ⟨hI, hF⟩
  obtain ⟨m, hm, σf, ⟨hIf, hFf⟩, hrun⟩ := h
  exact ⟨m, by simpa using hm, σf, hIf, hFf, hrun⟩

end Loop

/-! ## 6. The whole-body span (entry / zero path / exit tail /
assembly) -/

/-- The string default (any state). -/
theorem defaultValue_string {σ : ExecState} :
    defaultValue σ .string = .ok (.string (gs [])) := by
  with_unfolding_all rfl

/-- The bool default (any state). -/
theorem defaultValue_bool {σ : ExecState} :
    defaultValue σ .bool = .ok (.bool false) := by
  with_unfolding_all rfl

section Body

variable {env : LocalEnv} {lv lr : Nat}

/-- The scope stack after the `s` declaration. -/
def env1' (env : LocalEnv) (na : Nat) : LocalEnv :=
  [("s", .base ⟨na⟩)] :: env

/-- The scope stack inside the `for` block. -/
def env2' (env : LocalEnv) (na : Nat) : LocalEnv :=
  [("$forFirst", .base ⟨na + 1⟩)] :: env1' env na

/-- The while continuation inside the body. -/
def kW (env : LocalEnv) (na : Nat) (KF : Cont) : Cont :=
  .seq [] (env2' env na) (.seq [retSeqn] (env1' env na) KF)

/-- The state at the loop head: the two loop cells allocated, the
frontier advanced by 2. -/
def entrySt (na : Nat) (σ : ExecState) : ExecState :=
  { σ with
      heap := Heap.set (Heap.set σ.heap (.base ⟨na⟩) (sCell (gs [])))
        (.base ⟨na + 1⟩) (flagCell true),
      nextAddr := na + 2 }

/-- **The entry segment** (37 steps, `v ≠ 0`): from the body's
execution to the digit loop's head, the two loop cells allocated. -/
theorem utoa_entry
    (henvV : LocalEnv.lookup env "v" = some (.base ⟨lv⟩))
    {v : Nat} (hvne : v ≠ 0)
    (σ : ExecState) (ch : Choices) (KF : Cont)
    (hvc : Heap.lookup σ.heap (.base ⟨lv⟩) = some (uCell (v : Int)))
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none) :
    stepFnIter 37 σ (.exec utoaBody env KF) ch
      = .ok (headCfg "$forFirst" utoaCond digitBody
          (env2' env σ.nextAddr) (kW env σ.nextAddr KF),
        entrySt σ.nextAddr σ, ch) := by
  have hlvna : lv ≠ σ.nextAddr := by
    intro he
    rw [he, hfr _ (Nat.le_refl _)] at hvc
    cases hvc
  -- E1: block + pop (2 steps)
  have hE1 : stepFnIter 2 σ (.exec utoaBody env KF) ch
      = .ok (.exec zeroIf ([] :: env)
          (.seq [sInit, forBlock, retSeqn] ([] :: env) KF), σ, ch) :=
    stepFnIter_chain (stepFnIter_one stepFn_block)
      (stepFnIter_one stepFn_seq_pop)
  -- E2: if entry + eqCmp dispatch (2 pure)
  have hE2 : stepFnIter 2 σ (.exec zeroIf ([] :: env)
      (.seq [sInit, forBlock, retSeqn] ([] :: env) KF)) ch
      = .ok (.evalE (.var "v") ([] :: env)
          (.strictK (.eqCmp tU) [] [.intLit 0 .uint64] ([] :: env)
            (.ifK (.block #[] #[.seqn
                #[.assign (.var "$res0") (.stringLit (gs [48])),
                  .returnStmt]])
              (.seqn #[]) ([] :: env)
              (.seq [sInit, forBlock, retSeqn] ([] :: env) KF))),
        σ, ch) := by
    with_unfolding_all rfl
  -- E3: the v read
  have hE3 : stepFnIter 1 σ (.evalE (.var "v") ([] :: env)
      (.strictK (.eqCmp tU) [] [.intLit 0 .uint64] ([] :: env)
        (.ifK (.block #[] #[.seqn
            #[.assign (.var "$res0") (.stringLit (gs [48])),
              .returnStmt]])
          (.seqn #[]) ([] :: env)
          (.seq [sInit, forBlock, retSeqn] ([] :: env) KF)))) ch
      = .ok (.retV (.int (v : Int) .uint64)
          (.strictK (.eqCmp tU) [] [.intLit 0 .uint64] ([] :: env)
            (.ifK (.block #[] #[.seqn
                #[.assign (.var "$res0") (.stringLit (gs [48])),
                  .returnStmt]])
              (.seqn #[]) ([] :: env)
              (.seq [sInit, forBlock, retSeqn] ([] :: env) KF))),
        σ, ch) :=
    stepFnIter_one (stepFn_var
      (henv := (lookup_pushScope env "v").trans henvV) (hlook := hvc))
  -- E4: intLit (2 pure)
  have hE4 : stepFnIter 2 σ (.retV (.int (v : Int) .uint64)
      (.strictK (.eqCmp tU) [] [.intLit 0 .uint64] ([] :: env)
        (.ifK (.block #[] #[.seqn
            #[.assign (.var "$res0") (.stringLit (gs [48])),
              .returnStmt]])
          (.seqn #[]) ([] :: env)
          (.seq [sInit, forBlock, retSeqn] ([] :: env) KF)))) ch
      = .ok (.retV (.int 0 .uint64)
          (.strictK (.eqCmp tU) [.int (v : Int) .uint64] [] ([] :: env)
            (.ifK (.block #[] #[.seqn
                #[.assign (.var "$res0") (.stringLit (gs [48])),
                  .returnStmt]])
              (.seqn #[]) ([] :: env)
              (.seq [sInit, forBlock, retSeqn] ([] :: env) KF))),
        σ, ch) := by
    with_unfolding_all rfl
  -- E5: the comparison (false branch value)
  have hE5 : stepFnIter 1 σ (.retV (.int 0 .uint64)
      (.strictK (.eqCmp tU) [.int (v : Int) .uint64] [] ([] :: env)
        (.ifK (.block #[] #[.seqn
            #[.assign (.var "$res0") (.stringLit (gs [48])),
              .returnStmt]])
          (.seqn #[]) ([] :: env)
          (.seq [sInit, forBlock, retSeqn] ([] :: env) KF)))) ch
      = .ok (.retV (.bool false)
          (.ifK (.block #[] #[.seqn
              #[.assign (.var "$res0") (.stringLit (gs [48])),
                .returnStmt]])
            (.seqn #[]) ([] :: env)
            (.seq [sInit, forBlock, retSeqn] ([] :: env) KF)),
        σ, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.int 0 .uint64,
        GoValue.int (v : Int) .uint64])
      = [GoValue.int (v : Int) .uint64, GoValue.int 0 .uint64]
      from rfl,
      GoLean.SliceMem.applyStrictOp_eqCmp_int]
    rw [show (((v : Nat) : Int) == 0) = false from by
      simp only [beq_eq_false_iff_ne, ne_eq, Int.natCast_eq_zero]
      exact hvne]
  -- E6+E7: else branch + splice/pop to sInit (3 steps)
  have hE6 : stepFnIter 3 σ (.retV (.bool false)
      (.ifK (.block #[] #[.seqn
          #[.assign (.var "$res0") (.stringLit (gs [48])),
            .returnStmt]])
        (.seqn #[]) ([] :: env)
        (.seq [sInit, forBlock, retSeqn] ([] :: env) KF))) ch
      = .ok (.exec sInit ([] :: env)
          (.seq [forBlock, retSeqn] ([] :: env) KF), σ, ch) := by
    have hif : stepFnIter 1 σ (.retV (.bool false)
        (.ifK (.block #[] #[.seqn
            #[.assign (.var "$res0") (.stringLit (gs [48])),
              .returnStmt]])
          (.seqn #[]) ([] :: env)
          (.seq [sInit, forBlock, retSeqn] ([] :: env) KF))) ch
        = .ok (.exec (.seqn #[]) ([] :: env)
            (.seq [sInit, forBlock, retSeqn] ([] :: env) KF), σ, ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain hif (stepFnIter_splice_pop (ss := #[]) rfl)
  -- E8: sInit splice/pop (2 steps)
  have hE8 : stepFnIter 2 σ (.exec sInit ([] :: env)
      (.seq [forBlock, retSeqn] ([] :: env) KF)) ch
      = .ok (.exec (.initialization { id := "s", typ := .string })
          ([] :: env)
          (.seq [.assign (.var "s") (.stringLit (gs [])), forBlock,
            retSeqn] ([] :: env) KF), σ, ch) :=
    stepFnIter_splice_pop
      (ss := #[.initialization { id := "s", typ := .string },
        .assign (.var "s") (.stringLit (gs []))]) rfl
  -- E9: the s allocation
  have hE9 : stepFnIter 1 σ
      (.exec (.initialization { id := "s", typ := .string }) ([] :: env)
        (.seq [.assign (.var "s") (.stringLit (gs [])), forBlock,
          retSeqn] ([] :: env) KF)) ch
      = .ok (.next (.seq [.assign (.var "s") (.stringLit (gs [])),
            forBlock, retSeqn] (env1' env σ.nextAddr) KF),
        { σ with
            heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
              (sCell (gs [])),
            nextAddr := σ.nextAddr + 1 }, ch) :=
    stepFnIter_one (stepFn_init_seq (hdef := defaultValue_string))
  -- the working states
  let σa : ExecState := { σ with
    heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩) (sCell (gs [])),
    nextAddr := σ.nextAddr + 1 }
  -- E10+E11: pop + the s-assign (7 steps)
  have hsa : Heap.lookup σa.heap (.base ⟨σ.nextAddr⟩)
      = some (sCell (gs [])) := lookup_set_self
  have hE10 : stepFnIter 2 σa (.next (.seq
      [.assign (.var "s") (.stringLit (gs [])), forBlock, retSeqn]
      (env1' env σ.nextAddr) KF)) ch
      = .ok (.evalE (.ref "s") (env1' env σ.nextAddr)
          (.tgtOpK (.chain []) [] [] [] [] .vals [.stringLit (gs [])]
            [] (.seqn #[]) (env1' env σ.nextAddr)
            (.seq [forBlock, retSeqn] (env1' env σ.nextAddr) KF)),
        σa, ch) := by
    with_unfolding_all rfl
  have hE11 : stepFnIter 1 σa (.evalE (.ref "s") (env1' env σ.nextAddr)
      (.tgtOpK (.chain []) [] [] [] [] .vals [.stringLit (gs [])]
        [] (.seqn #[]) (env1' env σ.nextAddr)
        (.seq [forBlock, retSeqn] (env1' env σ.nextAddr) KF))) ch
      = .ok (.retV (.addr (.base ⟨σ.nextAddr⟩))
          (.tgtOpK (.chain []) [] [] [] [] .vals [.stringLit (gs [])]
            [] (.seqn #[]) (env1' env σ.nextAddr)
            (.seq [forBlock, retSeqn] (env1' env σ.nextAddr) KF)),
        σa, ch) :=
    stepFnIter_one (stepFn_ref rfl)
  have hE12 : stepFnIter 3 σa (.retV (.addr (.base ⟨σ.nextAddr⟩))
      (.tgtOpK (.chain []) [] [] [] [] .vals [.stringLit (gs [])]
        [] (.seqn #[]) (env1' env σ.nextAddr)
        (.seq [forBlock, retSeqn] (env1' env σ.nextAddr) KF))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨σ.nextAddr⟩)) [] []]
          [.string (gs [])] (.seqn #[]) (env1' env σ.nextAddr)
          (.seq [forBlock, retSeqn] (env1' env σ.nextAddr) KF)),
        σa, ch) := by
    with_unfolding_all rfl
  have hE13 : stepFnIter 1 σa (.next (.storeK
      [.chain (.addr (.base ⟨σ.nextAddr⟩)) [] []] [.string (gs [])]
      (.seqn #[]) (env1' env σ.nextAddr)
      (.seq [forBlock, retSeqn] (env1' env σ.nextAddr) KF))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (env1' env σ.nextAddr)
          (.seq [forBlock, retSeqn] (env1' env σ.nextAddr) KF)),
        { σa with heap := Heap.set σa.heap (.base ⟨σ.nextAddr⟩) (sCell (gs [])) }, ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_addr (ty := .string) (old := .string (gs []))
        (hlook := hsa) (hnorm := normalize_string)))
  -- E14: drain to forBlock (3 steps)
  have hE14 : stepFnIter 3
      { σa with heap := Heap.set σa.heap (.base ⟨σ.nextAddr⟩) (sCell (gs [])) }
      (.next (.storeK [] [] (.seqn #[]) (env1' env σ.nextAddr)
        (.seq [forBlock, retSeqn] (env1' env σ.nextAddr) KF))) ch
      = .ok (.exec forBlock (env1' env σ.nextAddr)
          (.seq [retSeqn] (env1' env σ.nextAddr) KF),
        { σa with heap := Heap.set σa.heap (.base ⟨σ.nextAddr⟩) (sCell (gs [])) }, ch) :=
    stepFnIter_chain (stepFnIter_one stepFn_storeK_nil)
      (stepFnIter_splice_pop (ss := #[]) rfl)
  -- collapse the double set
  have hcollapse : ({ σa with heap := Heap.set σa.heap (.base ⟨σ.nextAddr⟩) (sCell (gs [])) } : ExecState)
      = { σ with
          heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩) (sCell (gs [])),
          nextAddr := σ.nextAddr + 1 } := by
    show ({ σa with heap := Heap.set σa.heap (.base ⟨σ.nextAddr⟩) (sCell (gs [])) } : ExecState) = σa
    have : Heap.set σa.heap (.base ⟨σ.nextAddr⟩) (sCell (gs []))
        = σa.heap := by
      show Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
        (sCell (gs []))) (.base ⟨σ.nextAddr⟩) (sCell (gs []))
        = Heap.set σ.heap (.base ⟨σ.nextAddr⟩) (sCell (gs []))
      exact set_set
    rw [this]
  rw [hcollapse] at hE13 hE14
  -- E15: forBlock block + pop (2 steps)
  have hE15 : stepFnIter 2 σa (.exec forBlock (env1' env σ.nextAddr)
      (.seq [retSeqn] (env1' env σ.nextAddr) KF)) ch
      = .ok (.exec (.initialization { id := "$forFirst", typ := .bool })
          ([] :: env1' env σ.nextAddr)
          (.seq [.assign (.var "$forFirst") (.boolLit true),
            cwhile "$forFirst" utoaCond digitBody]
            ([] :: env1' env σ.nextAddr)
            (.seq [retSeqn] (env1' env σ.nextAddr) KF)), σa, ch) :=
    stepFnIter_chain (stepFnIter_one stepFn_block)
      (stepFnIter_one stepFn_seq_pop)
  -- E16: the latch allocation (at σa.nextAddr = na + 1)
  have hE16 : stepFnIter 1 σa
      (.exec (.initialization { id := "$forFirst", typ := .bool })
        ([] :: env1' env σ.nextAddr)
        (.seq [.assign (.var "$forFirst") (.boolLit true),
          cwhile "$forFirst" utoaCond digitBody]
          ([] :: env1' env σ.nextAddr)
          (.seq [retSeqn] (env1' env σ.nextAddr) KF))) ch
      = .ok (.next (.seq [.assign (.var "$forFirst") (.boolLit true),
            cwhile "$forFirst" utoaCond digitBody]
          (env2' env σ.nextAddr)
          (.seq [retSeqn] (env1' env σ.nextAddr) KF)),
        { σa with
            heap := Heap.set σa.heap (.base ⟨σ.nextAddr + 1⟩)
              ⟨some .bool, .bool false⟩,
            nextAddr := σ.nextAddr + 2 }, ch) :=
    stepFnIter_one (stepFn_init_seq (hdef := defaultValue_bool))
  let σb : ExecState := { σa with
    heap := Heap.set σa.heap (.base ⟨σ.nextAddr + 1⟩)
      ⟨some .bool, .bool false⟩,
    nextAddr := σ.nextAddr + 2 }
  have hfb : Heap.lookup σb.heap (.base ⟨σ.nextAddr + 1⟩)
      = some ⟨some .bool, .bool false⟩ := lookup_set_self
  -- E17: pop + the latch assign (7 steps)
  have hE17 : stepFnIter 2 σb (.next (.seq
      [.assign (.var "$forFirst") (.boolLit true),
        cwhile "$forFirst" utoaCond digitBody]
      (env2' env σ.nextAddr)
      (.seq [retSeqn] (env1' env σ.nextAddr) KF))) ch
      = .ok (.evalE (.ref "$forFirst") (env2' env σ.nextAddr)
          (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit true] []
            (.seqn #[]) (env2' env σ.nextAddr)
            (.seq [cwhile "$forFirst" utoaCond digitBody]
              (env2' env σ.nextAddr)
              (.seq [retSeqn] (env1' env σ.nextAddr) KF))), σb, ch) := by
    with_unfolding_all rfl
  have hE18 : stepFnIter 1 σb
      (.evalE (.ref "$forFirst") (env2' env σ.nextAddr)
        (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit true] []
          (.seqn #[]) (env2' env σ.nextAddr)
          (.seq [cwhile "$forFirst" utoaCond digitBody]
            (env2' env σ.nextAddr)
            (.seq [retSeqn] (env1' env σ.nextAddr) KF)))) ch
      = .ok (.retV (.addr (.base ⟨σ.nextAddr + 1⟩))
          (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit true] []
            (.seqn #[]) (env2' env σ.nextAddr)
            (.seq [cwhile "$forFirst" utoaCond digitBody]
              (env2' env σ.nextAddr)
              (.seq [retSeqn] (env1' env σ.nextAddr) KF))), σb, ch) :=
    stepFnIter_one (stepFn_ref rfl)
  have hE19 : stepFnIter 3 σb
      (.retV (.addr (.base ⟨σ.nextAddr + 1⟩))
        (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit true] []
          (.seqn #[]) (env2' env σ.nextAddr)
          (.seq [cwhile "$forFirst" utoaCond digitBody]
            (env2' env σ.nextAddr)
            (.seq [retSeqn] (env1' env σ.nextAddr) KF)))) ch
      = .ok (.next (.storeK
          [.chain (.addr (.base ⟨σ.nextAddr + 1⟩)) [] []] [.bool true]
          (.seqn #[]) (env2' env σ.nextAddr)
          (.seq [cwhile "$forFirst" utoaCond digitBody]
            (env2' env σ.nextAddr)
            (.seq [retSeqn] (env1' env σ.nextAddr) KF))), σb, ch) := by
    with_unfolding_all rfl
  have hE20 : stepFnIter 1 σb (.next (.storeK
      [.chain (.addr (.base ⟨σ.nextAddr + 1⟩)) [] []] [.bool true]
      (.seqn #[]) (env2' env σ.nextAddr)
      (.seq [cwhile "$forFirst" utoaCond digitBody]
        (env2' env σ.nextAddr)
        (.seq [retSeqn] (env1' env σ.nextAddr) KF)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (env2' env σ.nextAddr)
          (.seq [cwhile "$forFirst" utoaCond digitBody]
            (env2' env σ.nextAddr)
            (.seq [retSeqn] (env1' env σ.nextAddr) KF))),
        { σb with heap := Heap.set σb.heap (.base ⟨σ.nextAddr + 1⟩) (flagCell true) }, ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_addr (ty := .bool) (old := .bool false)
        (hlook := hfb) (hnorm := normalize_bool)))
  have hE21 : stepFnIter 3
      { σb with heap := Heap.set σb.heap (.base ⟨σ.nextAddr + 1⟩) (flagCell true) }
      (.next (.storeK [] [] (.seqn #[]) (env2' env σ.nextAddr)
        (.seq [cwhile "$forFirst" utoaCond digitBody]
          (env2' env σ.nextAddr)
          (.seq [retSeqn] (env1' env σ.nextAddr) KF)))) ch
      = .ok (headCfg "$forFirst" utoaCond digitBody
          (env2' env σ.nextAddr) (kW env σ.nextAddr KF),
        { σb with heap := Heap.set σb.heap (.base ⟨σ.nextAddr + 1⟩) (flagCell true) }, ch) :=
    stepFnIter_chain (stepFnIter_one stepFn_storeK_nil)
      (stepFnIter_splice_pop (ss := #[]) rfl)
  -- the final-state collapse
  have hfin : ({ σb with heap := Heap.set σb.heap (.base ⟨σ.nextAddr + 1⟩) (flagCell true) } : ExecState)
      = entrySt σ.nextAddr σ := by
    show ({ σb with heap := Heap.set σb.heap (.base ⟨σ.nextAddr + 1⟩) (flagCell true) } : ExecState) = _
    unfold entrySt
    have : Heap.set σb.heap (.base ⟨σ.nextAddr + 1⟩) (flagCell true)
        = Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
            (sCell (gs []))) (.base ⟨σ.nextAddr + 1⟩) (flagCell true) := by
      show Heap.set (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
        (sCell (gs []))) (.base ⟨σ.nextAddr + 1⟩)
        ⟨some .bool, .bool false⟩) (.base ⟨σ.nextAddr + 1⟩)
        (flagCell true) = _
      exact set_set
    rw [this]
  rw [hfin] at hE20 hE21
  exact stepFnIter_chain hE1 (stepFnIter_chain hE2 (stepFnIter_chain hE3
    (stepFnIter_chain hE4 (stepFnIter_chain hE5 (stepFnIter_chain hE6
      (stepFnIter_chain hE8 (stepFnIter_chain hE9 (stepFnIter_chain hE10
        (stepFnIter_chain hE11 (stepFnIter_chain hE12
          (stepFnIter_chain hE13 (stepFnIter_chain hE14
            (stepFnIter_chain hE15 (stepFnIter_chain hE16
              (stepFnIter_chain hE17 (stepFnIter_chain hE18
                (stepFnIter_chain hE19 (stepFnIter_chain hE20
                  hE21))))))))))))))))))

/-- **The zero path** (25 steps): `v = 0` returns `"0"` directly —
only the result cell moves. -/
theorem utoa_zero_path
    (henvV : LocalEnv.lookup env "v" = some (.base ⟨lv⟩))
    (henvR : LocalEnv.lookup env "$res0" = some (.base ⟨lr⟩))
    (σ : ExecState) (ch : Choices) (KF : Cont) (r0 : GoString)
    (hvc : Heap.lookup σ.heap (.base ⟨lv⟩) = some (uCell 0))
    (hrc : Heap.lookup σ.heap (.base ⟨lr⟩) = some (sCell r0)) :
    stepFnIter 25 σ (.exec utoaBody env KF) ch
      = .ok (.returning KF,
        { σ with heap := Heap.set σ.heap (.base ⟨lr⟩) (sCell (gs [48])) }, ch) := by
  -- the then-branch continuation
  let K1 : Cont := .seq [sInit, forBlock, retSeqn] ([] :: env) KF
  let thn : Stmt := .block #[] #[.seqn
    #[.assign (.var "$res0") (.stringLit (gs [48])), .returnStmt]]
  -- Z1: block + pop (2 steps)
  have hZ1 : stepFnIter 2 σ (.exec utoaBody env KF) ch
      = .ok (.exec zeroIf ([] :: env) K1, σ, ch) :=
    stepFnIter_chain (stepFnIter_one stepFn_block)
      (stepFnIter_one stepFn_seq_pop)
  -- Z2: if entry + dispatch (2 pure)
  have hZ2 : stepFnIter 2 σ (.exec zeroIf ([] :: env) K1) ch
      = .ok (.evalE (.var "v") ([] :: env)
          (.strictK (.eqCmp tU) [] [.intLit 0 .uint64] ([] :: env)
            (.ifK thn (.seqn #[]) ([] :: env) K1)), σ, ch) := by
    with_unfolding_all rfl
  -- Z3: the v read (v = 0)
  have hZ3 : stepFnIter 1 σ (.evalE (.var "v") ([] :: env)
      (.strictK (.eqCmp tU) [] [.intLit 0 .uint64] ([] :: env)
        (.ifK thn (.seqn #[]) ([] :: env) K1))) ch
      = .ok (.retV (.int 0 .uint64)
          (.strictK (.eqCmp tU) [] [.intLit 0 .uint64] ([] :: env)
            (.ifK thn (.seqn #[]) ([] :: env) K1)), σ, ch) :=
    stepFnIter_one (stepFn_var
      (henv := (lookup_pushScope env "v").trans henvV) (hlook := hvc))
  -- Z4: intLit + the comparison (3 steps: 2 pure + 1 apply, true)
  have hZ4 : stepFnIter 3 σ (.retV (.int 0 .uint64)
      (.strictK (.eqCmp tU) [] [.intLit 0 .uint64] ([] :: env)
        (.ifK thn (.seqn #[]) ([] :: env) K1))) ch
      = .ok (.retV (.bool true)
          (.ifK thn (.seqn #[]) ([] :: env) K1), σ, ch) := by
    with_unfolding_all rfl
  -- Z5: then branch + block + pop (3 steps)
  have hZ5 : stepFnIter 3 σ (.retV (.bool true)
      (.ifK thn (.seqn #[]) ([] :: env) K1)) ch
      = .ok (.exec (.seqn
            #[.assign (.var "$res0") (.stringLit (gs [48])),
              .returnStmt])
          ([] :: [] :: env) (.seq [] ([] :: [] :: env) K1), σ, ch) := by
    have hif : stepFnIter 1 σ (.retV (.bool true)
        (.ifK thn (.seqn #[]) ([] :: env) K1)) ch
        = .ok (.exec thn ([] :: env) K1, σ, ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain hif
      (stepFnIter_chain (stepFnIter_one stepFn_block)
        (stepFnIter_one stepFn_seq_pop))
  -- Z6: splice/pop to the assign (2 steps)
  have hZ6 : stepFnIter 2 σ (.exec (.seqn
      #[.assign (.var "$res0") (.stringLit (gs [48])), .returnStmt])
      ([] :: [] :: env) (.seq [] ([] :: [] :: env) K1)) ch
      = .ok (.exec (.assign (.var "$res0") (.stringLit (gs [48])))
          ([] :: [] :: env)
          (.seq [.returnStmt] ([] :: [] :: env) K1), σ, ch) :=
    stepFnIter_splice_pop
      (ss := #[.assign (.var "$res0") (.stringLit (gs [48])),
        .returnStmt]) rfl
  -- Z7: the assign (6 steps: entry, ref, lit walk, store)
  have hZ7 : stepFnIter 1 σ
      (.exec (.assign (.var "$res0") (.stringLit (gs [48])))
        ([] :: [] :: env) (.seq [.returnStmt] ([] :: [] :: env) K1)) ch
      = .ok (.evalE (.ref "$res0") ([] :: [] :: env)
          (.tgtOpK (.chain []) [] [] [] [] .vals
            [.stringLit (gs [48])] [] (.seqn #[]) ([] :: [] :: env)
            (.seq [.returnStmt] ([] :: [] :: env) K1)), σ, ch) := by
    with_unfolding_all rfl
  have hZ8 : stepFnIter 1 σ (.evalE (.ref "$res0") ([] :: [] :: env)
      (.tgtOpK (.chain []) [] [] [] [] .vals [.stringLit (gs [48])]
        [] (.seqn #[]) ([] :: [] :: env)
        (.seq [.returnStmt] ([] :: [] :: env) K1))) ch
      = .ok (.retV (.addr (.base ⟨lr⟩))
          (.tgtOpK (.chain []) [] [] [] [] .vals
            [.stringLit (gs [48])] [] (.seqn #[]) ([] :: [] :: env)
            (.seq [.returnStmt] ([] :: [] :: env) K1)), σ, ch) :=
    stepFnIter_one (stepFn_ref
      ((lookup_pushScope ([] :: env) "$res0").trans
        ((lookup_pushScope env "$res0").trans henvR)))
  have hZ9 : stepFnIter 3 σ (.retV (.addr (.base ⟨lr⟩))
      (.tgtOpK (.chain []) [] [] [] [] .vals [.stringLit (gs [48])]
        [] (.seqn #[]) ([] :: [] :: env)
        (.seq [.returnStmt] ([] :: [] :: env) K1))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨lr⟩)) [] []]
          [.string (gs [48])] (.seqn #[]) ([] :: [] :: env)
          (.seq [.returnStmt] ([] :: [] :: env) K1)), σ, ch) := by
    with_unfolding_all rfl
  have hZ10 : stepFnIter 1 σ (.next (.storeK
      [.chain (.addr (.base ⟨lr⟩)) [] []] [.string (gs [48])]
      (.seqn #[]) ([] :: [] :: env)
      (.seq [.returnStmt] ([] :: [] :: env) K1))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) ([] :: [] :: env)
          (.seq [.returnStmt] ([] :: [] :: env) K1)),
        { σ with heap := Heap.set σ.heap (.base ⟨lr⟩) (sCell (gs [48])) }, ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_addr (ty := .string) (old := .string r0)
        (hlook := hrc) (hnorm := normalize_string)))
  -- Z11: drain + return unwind (6 steps)
  have hZ11 : stepFnIter 6
      { σ with heap := Heap.set σ.heap (.base ⟨lr⟩) (sCell (gs [48])) }
      (.next (.storeK [] [] (.seqn #[]) ([] :: [] :: env)
        (.seq [.returnStmt] ([] :: [] :: env) K1))) ch
      = .ok (.returning KF,
        { σ with heap := Heap.set σ.heap (.base ⟨lr⟩) (sCell (gs [48])) }, ch) := by
    have s1 : stepFnIter 3
        { σ with heap := Heap.set σ.heap (.base ⟨lr⟩) (sCell (gs [48])) }
        (.next (.storeK [] [] (.seqn #[]) ([] :: [] :: env)
          (.seq [.returnStmt] ([] :: [] :: env) K1))) ch
        = .ok (.exec .returnStmt ([] :: [] :: env)
            (.seq [] ([] :: [] :: env) K1),
          { σ with heap := Heap.set σ.heap (.base ⟨lr⟩) (sCell (gs [48])) }, ch) :=
      stepFnIter_chain (stepFnIter_one stepFn_storeK_nil)
        (stepFnIter_splice_pop (ss := #[]) rfl)
    have s2 : stepFnIter 3
        { σ with heap := Heap.set σ.heap (.base ⟨lr⟩) (sCell (gs [48])) }
        (.exec .returnStmt ([] :: [] :: env)
          (.seq [] ([] :: [] :: env) K1)) ch
        = .ok (.returning KF,
          { σ with heap := Heap.set σ.heap (.base ⟨lr⟩) (sCell (gs [48])) }, ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain s1 s2
  exact stepFnIter_chain hZ1 (stepFnIter_chain hZ2 (stepFnIter_chain hZ3
    (stepFnIter_chain hZ4 (stepFnIter_chain hZ5 (stepFnIter_chain hZ6
      (stepFnIter_chain hZ7 (stepFnIter_chain hZ8 (stepFnIter_chain hZ9
        (stepFnIter_chain hZ10 hZ11)))))))))

/-- **The exit tail** (15 steps): from the loop's delivered
continuation to the frame return — `$res0 := s`, then the unwind. -/
theorem utoa_tail
    (henvR : LocalEnv.lookup env "$res0" = some (.base ⟨lr⟩))
    {na : Nat} (_hRS : lr ≠ na)
    (σ : ExecState) (ch : Choices) (KF : Cont)
    (str r1 : GoString)
    (hsc : Heap.lookup σ.heap (.base ⟨na⟩) = some (sCell str))
    (hrc : Heap.lookup σ.heap (.base ⟨lr⟩) = some (sCell r1)) :
    stepFnIter 15 σ (.next (kW env na KF)) ch
      = .ok (.returning KF,
        { σ with heap := Heap.set σ.heap (.base ⟨lr⟩) (sCell str) }, ch) := by
  -- T1: pop-empty + pop (2 steps)
  have hT1 : stepFnIter 2 σ (.next (kW env na KF)) ch
      = .ok (.exec retSeqn (env1' env na)
          (.seq [] (env1' env na) KF), σ, ch) := by
    with_unfolding_all rfl
  -- T2: splice/pop (2 steps)
  have hT2 : stepFnIter 2 σ (.exec retSeqn (env1' env na)
      (.seq [] (env1' env na) KF)) ch
      = .ok (.exec (.assign (.var "$res0") (.var "s")) (env1' env na)
          (.seq [.returnStmt] (env1' env na) KF), σ, ch) :=
    stepFnIter_splice_pop
      (ss := #[.assign (.var "$res0") (.var "s"), .returnStmt]) rfl
  -- T3: the assign (6 steps)
  have hT3 : stepFnIter 1 σ
      (.exec (.assign (.var "$res0") (.var "s")) (env1' env na)
        (.seq [.returnStmt] (env1' env na) KF)) ch
      = .ok (.evalE (.ref "$res0") (env1' env na)
          (.tgtOpK (.chain []) [] [] [] [] .vals [.var "s"] []
            (.seqn #[]) (env1' env na)
            (.seq [.returnStmt] (env1' env na) KF)), σ, ch) := by
    with_unfolding_all rfl
  have hT4 : stepFnIter 1 σ (.evalE (.ref "$res0") (env1' env na)
      (.tgtOpK (.chain []) [] [] [] [] .vals [.var "s"] []
        (.seqn #[]) (env1' env na)
        (.seq [.returnStmt] (env1' env na) KF))) ch
      = .ok (.retV (.addr (.base ⟨lr⟩))
          (.tgtOpK (.chain []) [] [] [] [] .vals [.var "s"] []
            (.seqn #[]) (env1' env na)
            (.seq [.returnStmt] (env1' env na) KF)), σ, ch) :=
    stepFnIter_one (stepFn_ref
      ((lookup_pushScope env "$res0").trans henvR))
  have hT5 : stepFnIter 1 σ (.retV (.addr (.base ⟨lr⟩))
      (.tgtOpK (.chain []) [] [] [] [] .vals [.var "s"] []
        (.seqn #[]) (env1' env na)
        (.seq [.returnStmt] (env1' env na) KF))) ch
      = .ok (.evalE (.var "s") (env1' env na)
          (.rhsK .vals [.chain (.addr (.base ⟨lr⟩)) [] []] [] []
            (.seqn #[]) (env1' env na)
            (.seq [.returnStmt] (env1' env na) KF)), σ, ch) := by
    with_unfolding_all rfl
  have hT6 : stepFnIter 1 σ (.evalE (.var "s") (env1' env na)
      (.rhsK .vals [.chain (.addr (.base ⟨lr⟩)) [] []] [] []
        (.seqn #[]) (env1' env na)
        (.seq [.returnStmt] (env1' env na) KF))) ch
      = .ok (.retV (.string str)
          (.rhsK .vals [.chain (.addr (.base ⟨lr⟩)) [] []] [] []
            (.seqn #[]) (env1' env na)
            (.seq [.returnStmt] (env1' env na) KF)), σ, ch) :=
    stepFnIter_one (stepFn_var (henv := rfl) (hlook := hsc))
  have hT7 : stepFnIter 1 σ (.retV (.string str)
      (.rhsK .vals [.chain (.addr (.base ⟨lr⟩)) [] []] [] []
        (.seqn #[]) (env1' env na)
        (.seq [.returnStmt] (env1' env na) KF))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨lr⟩)) [] []]
          [.string str] (.seqn #[]) (env1' env na)
          (.seq [.returnStmt] (env1' env na) KF)), σ, ch) := by
    with_unfolding_all rfl
  have hT8 : stepFnIter 1 σ (.next (.storeK
      [.chain (.addr (.base ⟨lr⟩)) [] []] [.string str] (.seqn #[])
      (env1' env na) (.seq [.returnStmt] (env1' env na) KF))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (env1' env na)
          (.seq [.returnStmt] (env1' env na) KF)),
        { σ with heap := Heap.set σ.heap (.base ⟨lr⟩) (sCell str) }, ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_addr (ty := .string) (old := .string r1)
        (hlook := hrc) (hnorm := normalize_string)))
  -- T4: drain + return unwind (5 steps)
  have hT9 : stepFnIter 5
      { σ with heap := Heap.set σ.heap (.base ⟨lr⟩) (sCell str) }
      (.next (.storeK [] [] (.seqn #[]) (env1' env na)
        (.seq [.returnStmt] (env1' env na) KF))) ch
      = .ok (.returning KF,
        { σ with heap := Heap.set σ.heap (.base ⟨lr⟩) (sCell str) }, ch) := by
    have s1 : stepFnIter 3
        { σ with heap := Heap.set σ.heap (.base ⟨lr⟩) (sCell str) }
        (.next (.storeK [] [] (.seqn #[]) (env1' env na)
          (.seq [.returnStmt] (env1' env na) KF))) ch
        = .ok (.exec .returnStmt (env1' env na)
            (.seq [] (env1' env na) KF),
          { σ with heap := Heap.set σ.heap (.base ⟨lr⟩) (sCell str) }, ch) :=
      stepFnIter_chain (stepFnIter_one stepFn_storeK_nil)
        (stepFnIter_splice_pop (ss := #[]) rfl)
    have s2 : stepFnIter 2
        { σ with heap := Heap.set σ.heap (.base ⟨lr⟩) (sCell str) }
        (.exec .returnStmt (env1' env na)
          (.seq [] (env1' env na) KF)) ch
        = .ok (.returning KF,
          { σ with heap := Heap.set σ.heap (.base ⟨lr⟩) (sCell str) }, ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain s1 s2
  exact stepFnIter_chain hT1 (stepFnIter_chain hT2 (stepFnIter_chain hT3
    (stepFnIter_chain hT4 (stepFnIter_chain hT5 (stepFnIter_chain hT6
      (stepFnIter_chain hT7 (stepFnIter_chain hT8 hT9)))))))

/-- **THE `utoa` WHOLE-BODY WEAK SPAN** (the banked ∃-string form):
from the body's execution under any frame continuation, the function
returns within `74·dig10 v + 81` steps with SOME string in the
result cell; only the `v`/result cells and cells at/above the entry
frontier move; the frontier advances by exactly the loop's two cells;
freshness and the table pack are preserved. -/
theorem utoa_body_span
    (henvV : LocalEnv.lookup env "v" = some (.base ⟨lv⟩))
    (henvR : LocalEnv.lookup env "$res0" = some (.base ⟨lr⟩))
    (hVR : lv ≠ lr)
    {v : Nat} (hv : v < 2 ^ 64) :
    ∀ σ ch (KF : Cont) (r0 : GoString),
      Heap.lookup σ.heap (.base ⟨lv⟩) = some (uCell (v : Int)) →
      Heap.lookup σ.heap (.base ⟨lr⟩) = some (sCell r0) →
      (∀ x, σ.nextAddr ≤ x → Heap.lookup σ.heap (.base ⟨x⟩) = none) →
      bfTB.Agrees σ →
      ∃ m ≤ 74 * dig10 v + 81, ∃ str : GoString, ∃ σ' : ExecState,
        stepFnIter m σ (.exec utoaBody env KF) ch
          = .ok (.returning KF, σ', ch)
        ∧ Heap.lookup σ'.heap (.base ⟨lr⟩) = some (sCell str)
        ∧ σ'.nextAddr = σ.nextAddr + (if v = 0 then 0 else 2)
        ∧ (∀ x, x < σ.nextAddr → x ≠ lv → x ≠ lr →
            Heap.lookup σ'.heap (.base ⟨x⟩)
              = Heap.lookup σ.heap (.base ⟨x⟩))
        ∧ (∀ x, σ'.nextAddr ≤ x →
            Heap.lookup σ'.heap (.base ⟨x⟩) = none)
        ∧ bfTB.Agrees σ' := by
  intro σ ch KF r0 hvc hrc hfr hag
  have hlvna : lv < σ.nextAddr := by
    rcases Nat.lt_or_ge lv σ.nextAddr with h | h
    · exact h
    · rw [hfr lv h] at hvc
      cases hvc
  have hlrna : lr < σ.nextAddr := by
    rcases Nat.lt_or_ge lr σ.nextAddr with h | h
    · exact h
    · rw [hfr lr h] at hrc
      cases hrc
  by_cases hz : v = 0
  · -- the zero path
    subst hz
    have hrun := utoa_zero_path henvV henvR σ ch KF r0 hvc hrc
    refine ⟨25, by omega, gs [48],
      { σ with heap := Heap.set σ.heap (.base ⟨lr⟩) (sCell (gs [48])) },
      hrun, lookup_set_self, by simp, ?_, ?_, agrees_set_heap hag⟩
    · intro x _ _ hxr
      show Heap.lookup (Heap.set σ.heap (.base ⟨lr⟩) (sCell (gs [48])))
        (.base ⟨x⟩) = _
      rw [lookup_set_other (fun he => hxr he.symm)]
    · intro x hx
      have hx' : σ.nextAddr ≤ x := hx
      show Heap.lookup (Heap.set σ.heap (.base ⟨lr⟩) (sCell (gs [48])))
        (.base ⟨x⟩) = none
      rw [lookup_set_other (by omega : lr ≠ x)]
      exact hfr x hx'
  · -- the loop path
    have hentry := utoa_entry henvV hz σ ch KF hvc hfr
    -- the loop working cells
    have hn1 : 1 ≤ dig10 v := by
      rw [dig10_pos hz]
      omega
    -- invariant at the loop head
    have hI0 : UtoaInv (σ.nextAddr + 1) lv σ.nextAddr v 0
        (entrySt σ.nextAddr σ) := by
      refine ⟨lookup_set_self, ?_, gs [], ?_⟩
      · show Heap.lookup (Heap.set (Heap.set σ.heap
          (.base ⟨σ.nextAddr⟩) (sCell (gs [])))
          (.base ⟨σ.nextAddr + 1⟩) (flagCell true)) (.base ⟨lv⟩) = _
        rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ lv),
          lookup_set_other (by omega : σ.nextAddr ≠ lv),
          show v / 10 ^ 0 = v from by
            rw [Nat.pow_zero, Nat.div_one]]
        exact hvc
      · show Heap.lookup (Heap.set (Heap.set σ.heap
          (.base ⟨σ.nextAddr⟩) (sCell (gs [])))
          (.base ⟨σ.nextAddr + 1⟩) (flagCell true))
          (.base ⟨σ.nextAddr⟩) = _
        rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ σ.nextAddr)]
        exact lookup_set_self
    have hF0 : UtoaFrame (σ.nextAddr + 1) lv σ.nextAddr σ.heap
        (σ.nextAddr + 2) (entrySt σ.nextAddr σ) := by
      refine ⟨?_, rfl, hag⟩
      intro x hxf _ hxs
      show Heap.lookup (Heap.set (Heap.set σ.heap
        (.base ⟨σ.nextAddr⟩) (sCell (gs [])))
        (.base ⟨σ.nextAddr + 1⟩) (flagCell true)) (.base ⟨x⟩) = _
      rw [lookup_set_other (fun he => hxf he.symm),
        lookup_set_other (fun he => hxs he.symm)]
    obtain ⟨mL, hmL, σf, hIf, hFf, hloop⟩ :=
      utoa_loop_span (envW := env2' env σ.nextAddr)
        (k := kW env σ.nextAddr KF)
        (by omega) (by omega) (by omega)
        rfl
        ((show LocalEnv.lookup (env2' env σ.nextAddr) "v"
            = LocalEnv.lookup env "v" from rfl).trans henvV)
        rfl
        hv (entrySt σ.nextAddr σ) ch hI0 hF0
    -- glueW at a positive count is the identity
    have hglue : glueW (σ.nextAddr + 1) (dig10 v) σf = σf := by
      unfold glueW
      rw [if_neg (by omega)]
    rw [hglue] at hloop
    -- the tail
    obtain ⟨hflagf, hvf, strf, hsf⟩ := hIf
    obtain ⟨hframe, hnaf, hagf⟩ := hFf
    have hrcf : Heap.lookup σf.heap (.base ⟨lr⟩) = some (sCell r0) := by
      rw [hframe lr (by omega) (by omega) (by omega)]
      exact hrc
    have htail := utoa_tail (env := env) (na := σ.nextAddr)
      henvR (by omega) σf ch KF strf r0 hsf hrcf
    -- assemble
    have hall := stepFnIter_chain hentry
      (stepFnIter_chain hloop htail)
    refine ⟨37 + (mL + 15), by omega, strf,
      { σf with heap := Heap.set σf.heap (.base ⟨lr⟩) (sCell strf) },
      hall, lookup_set_self, ?_, ?_, ?_, agrees_set_heap hagf⟩
    · show σf.nextAddr = σ.nextAddr + (if v = 0 then 0 else 2)
      rw [if_neg hz]
      exact hnaf
    · intro x hxlt hxv hxr
      show Heap.lookup (Heap.set σf.heap (.base ⟨lr⟩) (sCell strf))
        (.base ⟨x⟩) = _
      rw [lookup_set_other (fun he => hxr he.symm)]
      exact hframe x (by omega) hxv (by omega)
    · intro x hx
      show Heap.lookup (Heap.set σf.heap (.base ⟨lr⟩) (sCell strf))
        (.base ⟨x⟩) = none
      have hx' : σ.nextAddr + 2 ≤ x := by
        rw [hnaf] at hx
        omega
      rw [lookup_set_other (by omega : lr ≠ x),
        hframe x (by omega) (by omega) (by omega)]
      exact hfr x (by omega)

end Body

/-! ## 7. The call span (the P-H combinator closed at `utoa`) -/

section Call

variable {envC : LocalEnv} {tgt : String} {ltc : Nat} {Kc : Cont}

/-- **THE `utoa` CALL SPAN**: from the delivered argument value under
the call continuation (single `.var` target), through frame entry,
the whole body, and the frame exit, to the caller's resumption — the
target cell holds SOME string; the four dead frame/loop cells sit
between the old and new frontier. -/
theorem utoa_call_span
    (henvT : LocalEnv.lookup envC tgt = some (.base ⟨ltc⟩))
    {v : Nat} (hv : v < 2 ^ 64) :
    ∀ σ ch (t0 : GoString),
      bfTB.Agrees σ →
      Heap.lookup σ.heap (.base ⟨ltc⟩) = some (sCell t0) →
      (∀ x, σ.nextAddr ≤ x → Heap.lookup σ.heap (.base ⟨x⟩) = none) →
      ∃ m ≤ 74 * dig10 v + 87, ∃ str : GoString, ∃ σ' : ExecState,
        stepFnIter m σ (.retV (.int (v : Int) .uint64)
            (.callArgsK ⟨"utoa"⟩ [(.chain [], [.ref tgt])] [] []
              envC Kc)) ch
          = .ok (.exec (.seqn #[]) envC Kc, σ', ch)
        ∧ Heap.lookup σ'.heap (.base ⟨ltc⟩) = some (sCell str)
        ∧ σ'.nextAddr = σ.nextAddr + 2 + (if v = 0 then 0 else 2)
        ∧ (∀ x, x < σ.nextAddr → x ≠ ltc →
            Heap.lookup σ'.heap (.base ⟨x⟩)
              = Heap.lookup σ.heap (.base ⟨x⟩))
        ∧ (∀ x, σ'.nextAddr ≤ x →
            Heap.lookup σ'.heap (.base ⟨x⟩) = none)
        ∧ bfTB.Agrees σ' := by
  intro σ ch t0 hag htc hfr
  have hltna : ltc < σ.nextAddr := by
    rcases Nat.lt_or_ge ltc σ.nextAddr with h | h
    · exact h
    · rw [hfr ltc h] at htc
      cases htc
  -- pin the carrier
  have hσ := twinSt_of_agrees hag
  -- frame entry
  have henter : enterFrame σ ⟨"utoa"⟩ [.int (v : Int) .uint64]
      = .ok (utoaFunc, utoaEnv σ.nextAddr, [.base ⟨σ.nextAddr + 1⟩],
        twinSt (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
            (uCell (v : Int))) (.base ⟨σ.nextAddr + 1⟩) (sCell (gs [])))
          (σ.nextAddr + 2)) := by
    have h0 := utoa_enterFrame σ.heap σ.nextAddr v hv
    rw [← hσ] at h0
    exact h0
  -- the entered state
  let σ₁ : ExecState := twinSt (Heap.set (Heap.set σ.heap
    (.base ⟨σ.nextAddr⟩) (uCell (v : Int))) (.base ⟨σ.nextAddr + 1⟩)
    (sCell (gs []))) (σ.nextAddr + 2)
  -- the body span at the entered state
  have hbody := utoa_body_span (env := utoaEnv σ.nextAddr)
    (lv := σ.nextAddr) (lr := σ.nextAddr + 1)
    rfl rfl (by omega) hv σ₁ ch
    (.frame [(.chain [], [.ref tgt])] envC [.base ⟨σ.nextAddr + 1⟩]
      [] Kc utoaFunc.wrapper)
    (gs [])
    (by
      show Heap.lookup (Heap.set (Heap.set σ.heap
        (.base ⟨σ.nextAddr⟩) (uCell (v : Int)))
        (.base ⟨σ.nextAddr + 1⟩) (sCell (gs [])))
        (.base ⟨σ.nextAddr⟩) = _
      rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ σ.nextAddr)]
      exact lookup_set_self)
    lookup_set_self
    (by
      intro x hx
      show Heap.lookup (Heap.set (Heap.set σ.heap
        (.base ⟨σ.nextAddr⟩) (uCell (v : Int)))
        (.base ⟨σ.nextAddr + 1⟩) (sCell (gs [])))
        (.base ⟨x⟩) = none
      have hx2 : σ.nextAddr + 2 ≤ x := hx
      rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ x),
        lookup_set_other (by omega : σ.nextAddr ≠ x)]
      exact hfr x (by omega))
    ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨mB, hmB, str, σ₂, hrun, hres, hna2, hframe2, hfr2, hag2⟩ :=
    hbody
  have hσ₁na : σ₁.nextAddr = σ.nextAddr + 2 := rfl
  -- the frame exit (5 steps)
  have hload : loadMany σ₂ [.base ⟨σ.nextAddr + 1⟩]
      = .ok [.string str] := by
    have := loadMany_one (σ := σ₂) (a := ⟨σ.nextAddr + 1⟩)
      (c := sCell str) hres
    exact this
  have htc2 : Heap.lookup σ₂.heap (.base ⟨ltc⟩) = some (sCell t0) := by
    rw [hframe2 ltc (by rw [hσ₁na]; omega) (by omega) (by omega)]
    show Heap.lookup (Heap.set (Heap.set σ.heap
      (.base ⟨σ.nextAddr⟩) (uCell (v : Int)))
      (.base ⟨σ.nextAddr + 1⟩) (sCell (gs []))) (.base ⟨ltc⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ ltc),
      lookup_set_other (by omega : σ.nextAddr ≠ ltc)]
    exact htc
  have hX1 : stepFnIter 1 σ₂ (.returning
      (.frame [(.chain [], [.ref tgt])] envC [.base ⟨σ.nextAddr + 1⟩]
        [] Kc utoaFunc.wrapper)) ch
      = .ok (.evalE (.ref tgt) envC
          (.tgtOpK (.chain []) [] [] [] [] .vals [] [.string str]
            (.seqn #[]) envC Kc), σ₂, ch) :=
    stepFnIter_one (stepFn_return_frame (h := hload))
  have hX2 : stepFnIter 1 σ₂ (.evalE (.ref tgt) envC
      (.tgtOpK (.chain []) [] [] [] [] .vals [] [.string str]
        (.seqn #[]) envC Kc)) ch
      = .ok (.retV (.addr (.base ⟨ltc⟩))
          (.tgtOpK (.chain []) [] [] [] [] .vals [] [.string str]
            (.seqn #[]) envC Kc), σ₂, ch) :=
    stepFnIter_one (stepFn_ref henvT)
  have hX3 : stepFnIter 1 σ₂ (.retV (.addr (.base ⟨ltc⟩))
      (.tgtOpK (.chain []) [] [] [] [] .vals [] [.string str]
        (.seqn #[]) envC Kc)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨ltc⟩)) [] []]
          [.string str] (.seqn #[]) envC Kc), σ₂, ch) := by
    with_unfolding_all rfl
  have hX4 : stepFnIter 1 σ₂ (.next (.storeK
      [.chain (.addr (.base ⟨ltc⟩)) [] []] [.string str] (.seqn #[])
      envC Kc)) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) envC Kc),
        { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) (sCell str) },
        ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_addr (ty := .string) (old := .string t0)
        (hlook := htc2) (hnorm := normalize_string)))
  have hX5 : stepFnIter 1
      { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) (sCell str) }
      (.next (.storeK [] [] (.seqn #[]) envC Kc)) ch
      = .ok (.exec (.seqn #[]) envC Kc,
        { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) (sCell str) },
        ch) :=
    stepFnIter_one stepFn_storeK_nil
  -- assemble via the P-H combinator
  have hcall := stepFnIter_call_span (vals := [])
    (v := .int (v : Int) .uint64) (henter := henter) (hbody := hrun)
    (hexit := stepFnIter_chain hX1 (stepFnIter_chain hX2
      (stepFnIter_chain hX3 (stepFnIter_chain hX4 hX5))))
  refine ⟨1 + mB + 5, by omega, str,
    { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) (sCell str) },
    hcall, lookup_set_self, ?_, ?_, ?_, agrees_set_heap hag2⟩
  · show σ₂.nextAddr = σ.nextAddr + 2 + (if v = 0 then 0 else 2)
    rw [hna2, hσ₁na]
  · intro x hxlt hxt
    show Heap.lookup (Heap.set σ₂.heap (.base ⟨ltc⟩) (sCell str))
      (.base ⟨x⟩) = _
    rw [lookup_set_other (fun he => hxt he.symm),
      hframe2 x (by rw [hσ₁na]; omega) (by omega) (by omega)]
    show Heap.lookup (Heap.set (Heap.set σ.heap
      (.base ⟨σ.nextAddr⟩) (uCell (v : Int)))
      (.base ⟨σ.nextAddr + 1⟩) (sCell (gs []))) (.base ⟨x⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ x),
      lookup_set_other (by omega : σ.nextAddr ≠ x)]
  · intro x hx
    show Heap.lookup (Heap.set σ₂.heap (.base ⟨ltc⟩) (sCell str))
      (.base ⟨x⟩) = none
    have hxb : σ₂.nextAddr ≤ x := hx
    rw [lookup_set_other (by omega : ltc ≠ x)]
    exact hfr2 x hxb

end Call

end GoLean.RaftSeam.UtoaSpan
