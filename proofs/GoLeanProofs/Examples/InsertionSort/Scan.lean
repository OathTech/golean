import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Examples.InsertionSort.Subject

/-!
# InsertionSort — Scan

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

/-! ## The test phase, part 1: the sortedness scan (canonical remainder
placement — `ok` at 11, scan counter at 12, flag at 13; the scan never
allocates per iteration, so its segments are address-concrete; the
whole remainder run is transferred to the true placement in ONE
`transfer_seg11` application at the end) -/

def okScopeI : Scope :=
  [("ok", .base ⟨11⟩), ("s", .base ⟨5⟩), ("$c4", .base ⟨3⟩)]
def envIH2ok : LocalEnv := [okScopeI, hIScope0]
def envSC : LocalEnv :=
  [[("$forFirst", .base ⟨13⟩)], [("i", .base ⟨12⟩)], okScopeI, hIScope0]

/-- The scan loop's desugared while body (from the pinned record). -/
abbrev isortScanBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i")
          (.add (.var "i") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n"))
        (.seqn #[])
        .breakStmt,
      .block #[]
        #[.ifThenElse
            (.greaterCmp
              (.indexGet (.var "s")
                (.sub (.var "i") (.intLit 1 .uint64)))
              (.indexGet (.var "s") (.var "i")))
            (.block #[]
              #[.seqn #[.assign (.var "ok") (.intLit 0 .uint64)]])
            (.seqn #[])]]

def scTail : Cont :=
  .seq [] envSC
    (.seq [] [[("i", .base ⟨12⟩)], okScopeI, hIScope0]
      (.seq (hIBodyList.drop 6) envIH2ok hIFrame0))
def scHeadCfg : Config :=
  .exec (.while (.boolLit true) isortScanBody) envSC scTail
def scLoopK : Cont :=
  .loop (.boolLit true) isortScanBody envSC scTail
def scChkBlk : Stmt :=
  .block #[]
    #[.ifThenElse
        (.greaterCmp
          (.indexGet (.var "s") (.sub (.var "i") (.intLit 1 .uint64)))
          (.indexGet (.var "s") (.var "i")))
        (.block #[] #[.seqn #[.assign (.var "ok") (.intLit 0 .uint64)]])
        (.seqn #[])]
def scCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envSC)
    (.seq [scChkBlk] ([] :: envSC) scLoopK)
def scEnv2 : LocalEnv := [] :: [] :: envSC
def scIfK : Cont :=
  .ifK (.block #[] #[.seqn #[.assign (.var "ok") (.intLit 0 .uint64)]])
    (.seqn #[]) scEnv2 (.seq [] scEnv2 (.seq [] ([] :: envSC) scLoopK))
def scGcK1 : Cont :=
  .strictK .greaterCmp [] [.indexGet (.var "s") (.var "i")] scEnv2 scIfK
def scGcK2 (w1 : GoValue) : Cont :=
  .strictK .greaterCmp [w1] [] scEnv2 scIfK

/-- The scan-phase state: `ok` pinned 1, scan counter `iv`, flag. -/
def σSC (n seed : Nat) (ivF : Int) (l : List Int) (iv : Int)
    (ffv : Bool) : ExecState :=
  σHOutT n seed l ivF false
    [(.base ⟨11⟩, ucell 1), (.base ⟨12⟩, ucell iv), (.base ⟨13⟩, bcell ffv)]
    14

/-- Post-subject → the scan head: `ok := 1` at 11, `i := 1` at 12,
the flag at 13. 42 steps (trace 735→777). -/
theorem hR1_raw (n seed : Nat) (ivF : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 42 (σHOut n seed l ivF false) (.next hAfterCallK) ch
      = .ok (scHeadCfg, σSC n seed ivF l 1 true, ch) := by
  with_unfolding_all rfl

/-- Scan first-pass dispatch. -/
theorem hsc_d0_raw (n seed : Nat) (ivF : Int) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 25 (σSC n seed ivF l iv true) scHeadCfg ch
      = .ok (.retV (.bool (decide (iv < ((n : Nat) : Int)))) scCmpK,
          σSC n seed ivF l iv false, ch) := by
  with_unfolding_all rfl

/-- Scan later-pass dispatch: `i++`, then the exit test. -/
private theorem hsc_d1_raw (n seed : Nat) (ivF : Int) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 29 (σSC n seed ivF l iv false) scHeadCfg ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < ((n : Nat) : Int)))) scCmpK,
          σSC n seed ivF l
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false, ch) := by
  with_unfolding_all rfl

/-- Scan check phase 1: test true → the `s[i-1]` read's apply point. -/
private theorem hsc_B1_raw (n seed : Nat) (ivF : Int) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 15 (σSC n seed ivF l iv false) (.retV (.bool true) scCmpK) ch
      = .ok (.retV (.int (IntKind.normalize .uint64 (iv - 1)) .uint64)
            (.strictK .indexGet [hISliceH n] [] scEnv2 scGcK1),
          σSC n seed ivF l iv false, ch) := by
  with_unfolding_all rfl

/-- Scan check phase 2: first element in → the `s[i]` apply. -/
private theorem hsc_B2_raw (n seed : Nat) (ivF : Int) (l : List Int)
    (iv : Int) (w1 : GoValue) (ch : Choices) :
    stepFnIter 5 (σSC n seed ivF l iv false) (.retV w1 scGcK1) ch
      = .ok (.retV (.int iv .uint64)
            (.strictK .indexGet [hISliceH n] [] scEnv2 (scGcK2 w1)),
          σSC n seed ivF l iv false, ch) := by
  with_unfolding_all rfl

/-- Scan check phase 3: comparison delivered at the `if`. -/
private theorem hsc_B3_raw (n seed : Nat) (ivF : Int) (l : List Int)
    (iv a b : Int) (ch : Choices) :
    stepFnIter 1 (σSC n seed ivF l iv false)
      (.retV (.int b .uint64) (scGcK2 (.int a .uint64))) ch
      = .ok (.retV (.bool (decide (b < a))) scIfK,
          σSC n seed ivF l iv false, ch) := by
  with_unfolding_all rfl

/-- Scan check phase 4 (the sorted case): else branch drains to the
loop head. -/
private theorem hsc_B4_raw (n seed : Nat) (ivF : Int) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 5 (σSC n seed ivF l iv false) (.retV (.bool false) scIfK) ch
      = .ok (scHeadCfg, σSC n seed ivF l iv false, ch) := by
  with_unfolding_all rfl

/-- One scan element read (`ik = .uint64` indices). -/
private theorem stepFn_read_σSC {n seed : Nat} {ivF : Int} {l : List Int}
    {iv : Int} {k : Nat} {K : Cont} {ch : Choices}
    (hk : k < n) (hlen : l.length = n) :
    stepFn (σSC n seed ivF l iv false)
      (.retV (.int ((k : Nat) : Int) .uint64)
        (.strictK .indexGet [hISliceH n] [] scEnv2 K)) ch
      = .ok (.retV (.int (l.getD k 0) .uint64) K,
          σSC n seed ivF l iv false, ch) :=
  stepFn_strict_apply
    (applyStrictOp_indexGet_slice (ik := .uint64) rfl
      (Nat.le_refl n) hk
      (by rw [Nat.zero_add]; exact getElem?_mapU l k (by omega)))

/-- One scan iteration from the exit-test's true delivery at `m ≥ 1`:
read `s[m-1]` and `s[m]` (sorted, so the check does NOT fire), return
to the head, dispatch, deliver the next test. 57 steps. -/
private theorem hsc_iter (n seed : Nat) (hn : n < 2 ^ 63) (ivF : Int)
    (l : List Int) (m : Nat) (h1 : 1 ≤ m) (hm : m < n)
    (hlen : l.length = n) (hsort : Sorted l)
    (ch : Choices) :
    stepFnIter 57 (σSC n seed ivF l ((m : Nat) : Int) false)
      (.retV (.bool true) scCmpK) ch
      = .ok (.retV (.bool (decide (((m + 1 : Nat) : Int) < ((n : Nat) : Int))))
            scCmpK,
          σSC n seed ivF l ((m + 1 : Nat) : Int) false, ch) := by
  have hB1 := hsc_B1_raw n seed ivF l ((m : Nat) : Int) ch
  rw [show (((m : Nat) : Int) - 1) = ((m - 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m - 1 : Nat) : Int)) (by omega) (by omega)] at hB1
  have hread1 := stepFn_read_σSC (n := n) (seed := seed) (ivF := ivF)
    (l := l) (iv := ((m : Nat) : Int)) (k := m - 1) (K := scGcK1)
    (ch := ch) (by omega) hlen
  have hB2 := hsc_B2_raw n seed ivF l ((m : Nat) : Int)
    (.int (l.getD (m - 1) 0) .uint64) ch
  have hread2 := stepFn_read_σSC (n := n) (seed := seed) (ivF := ivF)
    (l := l) (iv := ((m : Nat) : Int)) (k := m)
    (K := scGcK2 (.int (l.getD (m - 1) 0) .uint64)) (ch := ch) (by omega) hlen
  have hB3 := hsc_B3_raw n seed ivF l ((m : Nat) : Int)
    (l.getD (m - 1) 0) (l.getD m 0) ch
  rw [show (decide (l.getD m 0 < l.getD (m - 1) 0)) = false from
    decide_eq_false (by
      have := hsort (m - 1) m (by omega) (by omega)
      omega)] at hB3
  have hB4 := hsc_B4_raw n seed ivF l ((m : Nat) : Int) ch
  have hd1 := hsc_d1_raw n seed ivF l ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)] at hd1
  have h1' := stepFnIter_chain hB1 (stepFnIter_one hread1)
  have h2 := stepFnIter_chain h1' hB2
  have h3 := stepFnIter_chain h2 (stepFnIter_one hread2)
  have h4 := stepFnIter_chain h3 hB3
  have h5 := stepFnIter_chain h4 hB4
  exact stepFnIter_chain h5 hd1

/-- **The scan loop**: from the exit-test delivery at `m ≥ 1` the run
reaches the exit-test's FALSE delivery at some final counter `mf`,
within `57·μ` steps (uniform in `n = 0` — the first test already
fails there). -/
theorem hscan_loop (n seed : Nat) (hn : n < 2 ^ 63) (ivF : Int)
    (l : List Int) (hlen : l.length = n) (hsort : Sorted l) :
    ∀ μ m, μ = n - m → 1 ≤ m → ∀ ch : Choices,
    ∃ (k mf : Nat), k ≤ 57 * μ ∧ 1 ≤ mf ∧
      stepFnIter k (σSC n seed ivF l ((m : Nat) : Int) false)
        (.retV (.bool (decide (((m : Nat) : Int) < ((n : Nat) : Int))))
          scCmpK) ch
        = .ok (.retV (.bool false) scCmpK,
            σSC n seed ivF l ((mf : Nat) : Int) false, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hμ h1 ch
    rcases Nat.lt_or_ge m n with hlt | hge
    · rw [show (decide (((m : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      obtain ⟨k, mf, hk, hmf, hrun⟩ := ih (n - (m + 1)) (by omega) (m + 1)
        rfl (by omega) ch
      exact ⟨57 + k, mf, by omega, hmf,
        stepFnIter_chain (hsc_iter n seed hn ivF l m h1 hlt hlen hsort ch)
          hrun⟩
    · rw [show (decide (((m : Nat) : Int) < ((n : Nat) : Int))) = false from
        decide_eq_false (by exact_mod_cast (by omega : ¬ (m < n)))]
      exact ⟨0, m, by omega, h1, rfl⟩


end GoLean.Examples.InsertionSort
