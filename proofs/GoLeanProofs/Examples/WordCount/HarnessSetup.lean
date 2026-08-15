import GoLeanProofs.Examples.WordCountProgram
import GoLeanProofs.EntryEq
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Examples.WordCount.Family
import GoLeanProofs.Examples.WordCount.Machine
import GoLeanProofs.Examples.Targets

/-!
# WordCount — HarnessSetup

Per-phase shard of `GoLeanProofs.Examples.WordCount` (examples phase-2
slice 0, lever 2, 2026-08-14). Every statement and proof here is
BYTE-IDENTICAL to the pre-split module; only file placement changed, so
Lake's module-level caching can see the phases separately. The
user-facing headline theorems live in the thin root module
`GoLeanProofs.Examples.WordCount`; the module docstring there records
the example's design.
-/

namespace GoLean.Examples.WordCount

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ### The harness `Func`, pinned -/

-- HOISTED to `GoLeanProofs/Examples/Targets.lean` (designation, 2026-08-14):
-- `wordcountHarnessFunc` is statement vocabulary of a DESIGNATED gallery headline, so it must
-- live in a def-only module inside the Comparator Challenge's trusted import
-- closure. The definition is unchanged and still visible here via the import.

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem wordcountHarness_pin :
    findFunctionIn? wordCountLowered.funcs ⟨"wordcount_harness"⟩
    = some wordcountHarnessFunc := rfl

/-! ### The entry equation and the setup phase (harness addresses
0–8; every segment `with_unfolding_all rfl` except the conditioned
makeSlice / `%` / element-store steps) -/

def hWScope0 : Scope :=
  [("$res0", .base ⟨2⟩), ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]

def hWFrame0 : Cont := .frame [] [] [] [] .stop

/- The post-prelude state (`σWH0`), the start configuration (`wcHC₀`),
and the entry equation (`wcH_entry_eq`) are DERIVED — the P4
entry-equation macro (G0 item 3c retrofit). Same conventions as the
old hand-written forms (already-normalized state arguments, normalize
at the equation's argument positions); the one spelling change is the
named start config `wcHC₀` replacing the inline
`.exec … [hWScope0] hWFrame0` (definitionally equal — the headline
carries the one-line show-bridge). -/
derive_entry_eq wcH_entry_eq wordCountLowered wordcountHarnessFunc σWH0 wcHC₀

/-- The harness slice handle: backing at its fixed address 4. -/
abbrev wHandleCell (n : Nat) : HeapCell :=
  ⟨some (.slice tU64), .slice ⟨some (.base ⟨4⟩), 0, n, n⟩⟩
abbrev wSliceH (n : Nat) : GoValue :=
  .slice ⟨some (.base ⟨4⟩), 0, n, n⟩

/-- The harness body's top statement list (projection of the pinned
record — reducible data, so the `rfl` segments see through it). -/
def hWBodyList : List Stmt :=
  match wordcountHarnessFunc.body with
  | .block _ ss => ss.toList
  | _ => []

private def envWC9 : LocalEnv := [[("$c9", .base ⟨3⟩)], hWScope0]
private def hWAfterMsK : Cont := .seq (hWBodyList.drop 1) envWC9 hWFrame0
private def hWMsK : Cont :=
  .stmtOpK (.makeSlice tU64 false) 1 [.addr (.base ⟨3⟩)] [] envWC9
    hWAfterMsK

/-- `$c9` declared (default slice), the makeSlice length delivered. -/
def σWStartC9 (nv sv : Int) : ExecState :=
  { σWH0 nv sv with
    heap := (σWH0 nv sv).heap
      ++ [(.base ⟨3⟩, ⟨some (.slice tU64), .slice ⟨none, 0, 0, 0⟩⟩)],
    nextAddr := 4 }

/-- Entry A: harness body start → the makeSlice length delivery.
10 steps. -/
theorem wcH_E1_raw (n seed : Nat) (ch : Choices) :
    stepFnIter 10 (σWH0 ((n : Nat) : Int) ((seed : Nat) : Int))
      (.exec wordcountHarnessFunc.body [hWScope0] hWFrame0) ch
      = .ok (.retV (.int ((n : Nat) : Int) .uint64) hWMsK,
          σWStartC9 ((n : Nat) : Int) ((seed : Nat) : Int), ch) := by
  with_unfolding_all rfl

/-- Post-makeSlice: the handle in `$c9`, the zeroed backing at 4. -/
def σWMkS (n seed : Nat) : ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := [(.base ⟨0⟩, u64cell (n : Int)), (.base ⟨1⟩, u64cell (seed : Int)),
             (.base ⟨2⟩, u64cell 0),
             (.base ⟨3⟩, wHandleCell n),
             (.base ⟨4⟩, arrCell n (List.replicate n 0))],
    nextAddr := 5 }

/-- **The makeSlice apply at a SYMBOLIC length**: allocates the zeroed
backing at 4 and stores the handle in `$c9`
(`GoLean.Iris.buildDefaultArrayValue_int`, proof-side import). -/
theorem wcH_makeSlice (n seed : Nat) (ch : Choices) :
    stepFn (σWStartC9 ((n : Nat) : Int) ((seed : Nat) : Int))
      (.retV (.int ((n : Nat) : Int) .uint64) hWMsK) ch
      = .ok (.next hWAfterMsK, σWMkS n seed, ch) := by
  have hb := GoLean.Iris.buildDefaultArrayValue_int
    (σWStartC9 ((n : Nat) : Int) ((seed : Nat) : Int)) .uint64 n
  have harr : (List.replicate n (GoValue.int 0 .uint64)).toArray
      = (⟨(List.replicate n (0 : Int)).map
          (fun v => GoValue.int v .uint64)⟩ : Array GoValue) := by
    simp [List.map_replicate]
  rw [harr] at hb
  have hnn1 := natFromNonneg_cast
    "runtime error: makeslice: len out of range" n
  have hnn2 := natFromNonneg_cast
    "runtime error: makeslice: cap out of range" n
  have happly : applyStmtOp (σWStartC9 ((n : Nat) : Int) ((seed : Nat) : Int))
      ch (.makeSlice tU64 false) 1
      [.addr (.base ⟨3⟩), .int ((n : Nat) : Int) .uint64]
      = .ok (σWMkS n seed, ch) := by
    simp only [applyStmtOp, applyStmtOpCore, valueAsInt, valueAsLoc,
      hnn1, hnn2, hb, Bind.bind, Except.bind, pure, Except.pure]
    rw [if_neg (Nat.lt_irrefl n)]
    with_unfolding_all rfl
  exact stepFn_stmtOp_apply
    (done := [.addr (.base ⟨3⟩)]) (v := .int ((n : Nat) : Int) .uint64)
    happly

/-! ### The setup loop (fixed cells 0–7; the loop never allocates) -/

private def wScopeH : Scope := [("w", .base ⟨5⟩), ("$c9", .base ⟨3⟩)]
private def suWEnv : LocalEnv :=
  [[("$forFirst", .base ⟨7⟩)], [("i", .base ⟨6⟩)], wScopeH, hWScope0]

/-- The setup-loop state family: backing list `l`, counter `iv`,
flag. -/
def sWSU (n : Nat) (sv : Int) (l : List Int) (iv : Int)
    (ff : Bool) : ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := [(.base ⟨0⟩, u64cell (n : Int)), (.base ⟨1⟩, u64cell sv),
             (.base ⟨2⟩, u64cell 0), (.base ⟨3⟩, wHandleCell n),
             (.base ⟨4⟩, arrCell n l), (.base ⟨5⟩, wHandleCell n),
             (.base ⟨6⟩, u64cell iv), (.base ⟨7⟩, bcell ff)],
    nextAddr := 8 }

private def suWTail : Cont :=
  .seq [] suWEnv
    (.seq [] [[("i", .base ⟨6⟩)], wScopeH, hWScope0]
      (.seq (hWBodyList.drop 3) [wScopeH, hWScope0] hWFrame0))
private def suWHeadCfg : Config :=
  .exec (.while (.boolLit true) wordcountHarnessFunc.suBody) suWEnv suWTail
private def suWLoopK : Cont :=
  .loop (.boolLit true) wordcountHarnessFunc.suBody suWEnv suWTail
private def suWStoreBlk : Stmt :=
  .block #[]
    #[.seqn
        #[.assign (.addr (.indexAddr (.var "w") (.var "i")))
            (.add (.var "seed") (.mod (.var "i") (.intLit 3 .uint64)))]]
def suWCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: suWEnv)
    (.seq [suWStoreBlk] ([] :: suWEnv) suWLoopK)
private def envW6 : LocalEnv := [] :: [] :: suWEnv
private def suWRef (n : Nat) (iv : Int) : TargetRef :=
  .chain (wSliceH n) [.int iv .uint64] [.index]
private def suWStoreTail : Cont :=
  .seq [] envW6 (.seq [] ([] :: suWEnv) suWLoopK)
private def suWRhsK (n : Nat) (iv : Int) : Cont :=
  .rhsK .vals [suWRef n iv] [] [] (.seqn #[]) envW6 suWStoreTail
private def suWAddK (n : Nat) (sv iv : Int) : Cont :=
  .strictK .add [.int sv .uint64] [] envW6 (suWRhsK n iv)
private def suWModK (n : Nat) (sv iv : Int) : Cont :=
  .strictK .mod [.int iv .uint64] [] envW6 (suWAddK n sv iv)

/-- Entry B: makeSlice done → `w := $c9`, `i := 0`, the flag block →
the setup loop head. 42 steps. -/
theorem wcH_E2_raw (n seed : Nat) (ch : Choices) :
    stepFnIter 42 (σWMkS n seed) (.next hWAfterMsK) ch
      = .ok (suWHeadCfg,
          sWSU n (seed : Int) (List.replicate n 0) 0 true, ch) := by
  with_unfolding_all rfl

/-- Setup first-pass dispatch: the flag drops, the exit test `i < n`
delivers. 25 steps. -/
theorem wcH_suA0_raw (n : Nat) (sv iv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 25 (sWSU n sv l iv true) suWHeadCfg ch
      = .ok (.retV (.bool (decide (iv < ((n : Nat) : Int)))) suWCmpK,
          sWSU n sv l iv false, ch) := by
  with_unfolding_all rfl

/-- Setup fill phase A: test true → the `%` apply point (the divisor
literal delivered; the one data-dependent arithmetic branch is the
divide-by-zero check, discharged by the conditioned step below).
19 steps. -/
private theorem wcH_suB1a_raw (n : Nat) (sv iv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 19 (sWSU n sv l iv false) (.retV (.bool true) suWCmpK) ch
      = .ok (.retV (.int 3 .uint64) (suWModK n sv iv),
          sWSU n sv l iv false, ch) := by
  with_unfolding_all rfl

/-- Setup fill phase B: the `%` result delivered → the add runs → the
element-store point (the wrapped `seed + i%3` riding). 2 steps. -/
private theorem wcH_suB1b_raw (n : Nat) (sv iv rv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 2 (sWSU n sv l iv false)
      (.retV (.int rv .uint64) (suWAddK n sv iv)) ch
      = .ok (.next (.storeK [suWRef n iv]
            [.int (IntKind.normalize .uint64 (sv + rv)) .uint64]
            (.seqn #[]) envW6 suWStoreTail),
          sWSU n sv l iv false, ch) := by
  with_unfolding_all rfl

/-- Setup fill tail: store done → back to the loop head. 5 steps. -/
private theorem wcH_suD_raw (n : Nat) (sv iv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 5 (sWSU n sv l iv false)
      (.next (.storeK [] [] (.seqn #[]) envW6 suWStoreTail)) ch
      = .ok (suWHeadCfg, sWSU n sv l iv false, ch) := by
  with_unfolding_all rfl

/-- Setup later-pass dispatch: `i++`, then the exit test. 29 steps. -/
private theorem wcH_suA1_raw (n : Nat) (sv iv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 29 (sWSU n sv l iv false) suWHeadCfg ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < ((n : Nat) : Int)))) suWCmpK,
          sWSU n sv l
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false, ch) := by
  with_unfolding_all rfl

/-- One setup iteration from the exit-test's true delivery at `i`:
`i % 3` (conditioned), the wrapped add, the element store, back to the
head, `i++`, the next test — the family prefix advanced. 57 steps. -/
private theorem wcH_su_iter (n seed i : Nat) (hn : n < 2 ^ 63)
    (hi : i < n) (ch : Choices) :
    stepFnIter 57
      (sWSU n (seed : Int) (wcFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false)
      (.retV (.bool true) suWCmpK) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) suWCmpK,
          sWSU n (seed : Int)
            (wcFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
            ((i + 1 : Nat) : Int) false, ch) := by
  have hB1a := wcH_suB1a_raw n (seed : Int) ((i : Nat) : Int)
    (wcFamily i seed ++ List.replicate (n - i) 0) ch
  -- the % apply, conditioned
  have hmod := stepFnIter_one (stepFn_strict_apply
    (done := [.int ((i : Nat) : Int) .uint64])
    (env := envW6) (k := suWAddK n (seed : Int) ((i : Nat) : Int))
    (ch := ch)
    (applyStrictOp_mod_u64
      (σ := sWSU n (seed : Int) (wcFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false)
      (a := i) (b := 3) (by omega) (by omega)))
  have h1 := stepFnIter_chain hB1a hmod
  -- the add + rhs collect
  have hB1b := wcH_suB1b_raw n (seed : Int) ((i : Nat) : Int)
    ((i % 3 : Nat) : Int) (wcFamily i seed ++ List.replicate (n - i) 0) ch
  rw [unorm_add_nat seed (i % 3)] at hB1b
  have h2 := stepFnIter_chain h1 hB1b
  -- the element store
  have hw : (0 : Int) ≤ (((seed + i % 3) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + i % 3) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + i % 3) (y := 2 ^ 64) (by omega)
    omega
  have hst := storeTarget_slice_u64
    (σ := sWSU n (seed : Int) (wcFamily i seed ++ List.replicate (n - i) 0)
      ((i : Nat) : Int) false)
    (a := ⟨4⟩) (off := 0) (len := n) (cap := n) (i := i) (n := n)
    (ik := .uint64) (l := wcFamily i seed ++ List.replicate (n - i) 0)
    (w := (((seed + i % 3) % 2 ^ 64 : Nat) : Int))
    rfl (Nat.le_refl n) hi
    (by rw [List.length_append, wcFamily_length, List.length_replicate]
        omega)
    (by rw [List.length_append, wcFamily_length, List.length_replicate]
        omega)
    wcFamilyZ_range hw
  rw [Nat.zero_add, wcFamily_set hi] at hst
  have h3 := stepFnIter_chain h2
    (stepFnIter_one (stepFn_store_step hst))
  -- store drain → head → i++ → the next test
  have hD := wcH_suD_raw n (seed : Int) ((i : Nat) : Int)
    (wcFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0) ch
  have h4 := stepFnIter_chain h3 hD
  have hA1 := wcH_suA1_raw n (seed : Int) ((i : Nat) : Int)
    (wcFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  exact stepFnIter_chain h4 hA1

/-- **The setup loop**, by strong induction on `n - i`: exactly
`57·(n-i)` steps materialize the wrapped `seed + i%3` family. No
seed hypothesis — the wrap is the family's own definition; only the
length domain `n < 2^63` is consumed, for the counter arithmetic. -/
theorem wcH_setup_loop (n seed : Nat) (hn : n < 2 ^ 63) :
    ∀ μ i, μ = n - i → i ≤ n → ∀ ch : Choices,
    stepFnIter (57 * (n - i))
      (sWSU n (seed : Int) (wcFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false)
      (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
        suWCmpK) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) suWCmpK,
          sWSU n (seed : Int) (wcFamily n seed) ((n : Nat) : Int) false,
          ch) := by
  -- The P5 iteration schema (`stepFnIter_iterate`) at the existing
  -- per-iteration composite `wcH_su_iter`; the `strongRecOn`
  -- boilerplate deleted (Gallery Campaign G0 item 3a retrofit).
  -- Statement unchanged (vestigial `μ` binder kept for consumers).
  intro _ i _ hin ch
  have hgen := stepFnIter_iterate (c := 57) (n := n)
    (T := fun j => sWSU n (seed : Int)
      (wcFamily j seed ++ List.replicate (n - j) 0) ((j : Nat) : Int) false)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int)
      < ((n : Nat) : Int)))) suWCmpK)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact wcH_su_iter n seed j hn hj ch')
    i hin ch
  simpa using hgen


end GoLean.Examples.WordCount
