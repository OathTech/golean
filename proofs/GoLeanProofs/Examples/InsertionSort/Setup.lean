import GoLeanProofs.Examples.InsertionSortProgram
import GoLeanProofs.EntryEq
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Examples.InsertionSort.Canon
import GoLeanProofs.Examples.InsertionSort.Family
import GoLeanProofs.Examples.Targets

/-!
# InsertionSort — Setup

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

/-! ## The entry equation (§11 glue) -/

/-- The entry frame environment (probe-pinned). -/
def hIEnv0 : LocalEnv :=
  [[("$res0", .base ⟨2⟩), ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]]

abbrev ucell (v : Int) : HeapCell :=
  ⟨some (.int .uint64), .int v .uint64⟩
abbrev ucellU (v : Int) : HeapCell :=
  ⟨some (.int .uint64), .int (IntKind.normalize .uint64 v) .uint64⟩

/- The post-prelude state (`σIH0`), the start configuration (`iHC₀`),
and the entry equation (`iharness_entry_eq`) are DERIVED — the P4
entry-equation macro (G0 item 3c retrofit). CONVENTION CHANGE,
absorbed by the headline's existing unorm rewrites: the emitted
`σIH0` receives ALREADY-normalized parameter values (the macro's
convention), where the old hand-written def normalized internally
(`ucellU`); the entry equation applies it at
`IntKind.normalize .uint64 _` argument positions. -/
derive_entry_eq iharness_entry_eq isortLowered isortHarnessFunc σIH0 iHC₀

/-! ## The setup phase (the family materialized — the first third of
the harness run; segment counts probe-pinned, re-checked by `rfl`) -/

/-- The `s` handle over the backing array at its fixed address 4. -/
abbrev hIHandleCell (n : Nat) : HeapCell :=
  ⟨some (.slice (.int .uint64)), .slice ⟨some (.base ⟨4⟩), 0, n, n⟩⟩
abbrev hISliceH (n : Nat) : GoValue :=
  .slice ⟨some (.base ⟨4⟩), 0, n, n⟩

def hIScope0 : List (String × Loc) :=
  [("$res0", .base ⟨2⟩), ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]

/-- The cleaned start state. -/
def σIStart (n seed : Nat) : ExecState :=
  { types := isortLowered.typeDefs.toList,
    functions := isortLowered.funcs,
    methods := isortLowered.methods,
    heap := [(.base ⟨0⟩, ucell (n : Int)), (.base ⟨1⟩, ucell (seed : Int)),
             (.base ⟨2⟩, ucell 0)],
    nextAddr := 3 }

/-- `$c4` declared (default slice), the makeSlice length delivered. -/
def σIStartC4 (n seed : Nat) : ExecState :=
  { σIStart n seed with
    heap := (σIStart n seed).heap
      ++ [(.base ⟨3⟩, ⟨some (.slice (.int .uint64)),
            .slice ⟨none, 0, 0, 0⟩⟩)],
    nextAddr := 4 }

/-- Post-makeSlice: the handle in `$c4`, the zeroed backing at 4. -/
def σIMkS (n seed : Nat) : ExecState :=
  { types := isortLowered.typeDefs.toList,
    functions := isortLowered.funcs,
    methods := isortLowered.methods,
    heap := [(.base ⟨0⟩, ucell (n : Int)), (.base ⟨1⟩, ucell (seed : Int)),
             (.base ⟨2⟩, ucell 0),
             (.base ⟨3⟩, hIHandleCell n),
             (.base ⟨4⟩, arrCell n (List.replicate n 0))],
    nextAddr := 5 }

def envC4 : LocalEnv := [[("$c4", .base ⟨3⟩)], hIScope0]

/-- The harness body's top statement list (projection of the pinned
record — reducible data, so the `rfl` segments see through it). -/
def hIBodyList : List Stmt :=
  match isortHarnessFunc.body with
  | .block _ ss => ss.toList
  | _ => []

def hIFrame0 : Cont := .frame [] [] [] [] .stop false

/-- The continuation below the makeSlice apply. -/
def hIAfterMsK : Cont :=
  .seq (hIBodyList.drop 1) envC4 hIFrame0

def hIMsK : Cont :=
  .stmtOpK (.makeSlice (.int .uint64) false) 1 [.addr (.base ⟨3⟩)] []
    envC4 hIAfterMsK

/-- Entry A: harness body start → the makeSlice length delivery. -/
theorem hseg_IA1_raw (n seed : Nat) (ch : Choices) :
    stepFnIter 10 (σIStart n seed)
      (.exec isortHarnessFunc.body hIEnv0 hIFrame0) ch
      = .ok (.retV (.int ((n : Nat) : Int) .uint64) hIMsK,
          σIStartC4 n seed, ch) := by
  with_unfolding_all rfl

/-- **The makeSlice apply at a SYMBOLIC length**: allocates the zeroed
backing at 4 and stores the handle in `$c4`. -/
theorem hstep_ImakeSlice (n seed : Nat) (ch : Choices) :
    stepFn (σIStartC4 n seed)
      (.retV (.int ((n : Nat) : Int) .uint64) hIMsK) ch
      = .ok (.next hIAfterMsK, σIMkS n seed, ch) := by
  have hb := GoLean.Iris.buildDefaultArrayValue_int (σIStartC4 n seed)
    .uint64 n
  have harr : (List.replicate n (GoValue.int 0 .uint64)).toArray
      = (⟨(List.replicate n (0 : Int)).map
          (fun v => GoValue.int v .uint64)⟩ : Array GoValue) := by
    simp [List.map_replicate]
  rw [harr] at hb
  have hnn1 := natFromNonneg_cast
    "runtime error: makeslice: len out of range" n
  have hnn2 := natFromNonneg_cast
    "runtime error: makeslice: cap out of range" n
  have happly : applyStmtOp (σIStartC4 n seed) ch
      (.makeSlice (.int .uint64) false) 1
      [.addr (.base ⟨3⟩), .int ((n : Nat) : Int) .uint64]
      = .ok (σIMkS n seed, ch) := by
    simp only [applyStmtOp, applyStmtOpCore, valueAsInt, valueAsLoc,
      hnn1, hnn2, hb, Bind.bind, Except.bind, pure, Except.pure]
    rw [if_neg (Nat.lt_irrefl n)]
    with_unfolding_all rfl
  exact stepFn_stmtOp_apply
    (done := [.addr (.base ⟨3⟩)]) (v := .int ((n : Nat) : Int) .uint64)
    happly

/-- The setup-loop state family (fixed cells 0–7; the setup loop never
allocates). -/
def sISU (n : Nat) (sv : Int) (l : List Int) (iv : Int)
    (ff : Bool) : ExecState :=
  { types := isortLowered.typeDefs.toList,
    functions := isortLowered.funcs,
    methods := isortLowered.methods,
    heap := [(.base ⟨0⟩, ucell (n : Int)), (.base ⟨1⟩, ucell sv),
             (.base ⟨2⟩, ucell 0), (.base ⟨3⟩, hIHandleCell n),
             (.base ⟨4⟩, arrCell n l), (.base ⟨5⟩, hIHandleCell n),
             (.base ⟨6⟩, ucell iv), (.base ⟨7⟩, bcell ff)],
    nextAddr := 8 }

/-- The setup loop's `for`-desugar body (the multiplicative store). -/
abbrev isortSetupBody : Stmt :=
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
        #[.seqn
            #[.assign
                (.addr (.indexAddr (.var "s") (.var "i")))
                (.mul (.var "seed")
                  (.add (.var "i") (.intLit 1 .uint64)))]]]

def envISU : LocalEnv :=
  [[("$forFirst", .base ⟨7⟩)], [("i", .base ⟨6⟩)],
   [("s", .base ⟨5⟩), ("$c4", .base ⟨3⟩)], hIScope0]
def envISU2 : LocalEnv :=
  [[("i", .base ⟨6⟩)], [("s", .base ⟨5⟩), ("$c4", .base ⟨3⟩)], hIScope0]
def envIH2 : LocalEnv :=
  [[("s", .base ⟨5⟩), ("$c4", .base ⟨3⟩)], hIScope0]

def suITail : Cont :=
  .seq [] envISU (.seq [] envISU2
    (.seq (hIBodyList.drop 3) envIH2 hIFrame0))
/-- The setup loop-head configuration. -/
def suIHeadCfg : Config :=
  .exec (.while (.boolLit true) isortSetupBody) envISU suITail
def suILoopK : Cont :=
  .loop (.boolLit true) isortSetupBody envISU suITail

def suIStoreBlk : Stmt :=
  .block #[]
    #[.seqn
        #[.assign
            (.addr (.indexAddr (.var "s") (.var "i")))
            (.mul (.var "seed")
              (.add (.var "i") (.intLit 1 .uint64)))]]

/-- The setup exit test's delivery continuation. -/
def suICmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envISU)
    (.seq [suIStoreBlk] ([] :: envISU) suILoopK)

def suIStoreTail : Cont :=
  .seq [] ([] :: [] :: envISU) (.seq [] ([] :: envISU) suILoopK)

/-- Entry A2: makeSlice done → `s := $c4`, `i := 0`, the `$forFirst`
block → the setup loop head. -/
theorem hseg_IA2_raw (n seed : Nat) (ch : Choices) :
    stepFnIter 42 (σIMkS n seed) (.next hIAfterMsK) ch
      = .ok (suIHeadCfg,
          sISU n (seed : Int) (List.replicate n 0) 0 true, ch) := by
  with_unfolding_all rfl

/-- Setup first-pass dispatch: flag drops, the exit test `i < n`. -/
theorem hsegISU_d0_raw (n : Nat) (sv iv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 25 (sISU n sv l iv true) suIHeadCfg ch
      = .ok (.retV (.bool (decide (iv < ((n : Nat) : Int)))) suICmpK,
          sISU n sv l iv false, ch) := by
  with_unfolding_all rfl

/-- Setup body: test true → the store point of `s[i] = seed*(i+1)`. -/
private theorem hsegISU_body_raw (n : Nat) (sv iv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 22 (sISU n sv l iv false) (.retV (.bool true) suICmpK) ch
      = .ok (.next (.storeK
            [.chain (hISliceH n) [.int iv .uint64] [.index]]
            [.int (IntKind.normalize .uint64
                (sv * IntKind.normalize .uint64 (iv + 1))) .uint64]
            (.seqn #[]) ([] :: [] :: envISU) suIStoreTail),
          sISU n sv l iv false, ch) := by
  with_unfolding_all rfl

/-- The setup element store, cleaned. -/
private theorem hstep_Istore_setup (n : Nat) (sv : Int) (l : List Int)
    (i : Nat) (w : Int) (hi : i < n) (hlen : l.length = n)
    (hl : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64) (hw : 0 ≤ w ∧ w < 2 ^ 64)
    (iv : Int) (ch : Choices) :
    stepFnIter 1 (sISU n sv l iv false)
      (.next (.storeK [.chain (hISliceH n) [.int ((i : Nat) : Int) .uint64]
          [.index]]
        [.int w .uint64] (.seqn #[]) ([] :: [] :: envISU) suIStoreTail))
      ch
      = .ok (.next (.storeK [] [] (.seqn #[]) ([] :: [] :: envISU)
            suIStoreTail),
          sISU n sv (l.set i w) iv false, ch) := by
  have hstore := storeTarget_slice_u64 (σ := sISU n sv l iv false)
    (a := ⟨4⟩) (off := 0) (len := n) (cap := n) (i := i) (n := n)
    (ik := .uint64) (l := l) (w := w) rfl (Nat.le_refl n) hi
    (by omega) hlen hl hw
  rw [Nat.zero_add] at hstore
  exact stepFnIter_one (stepFn_store_step hstore)

/-- Setup dispatch (later passes): store done → the loop head →
`i := i + 1` → the exit test delivery. -/
private theorem hsegISU_d1_raw (n : Nat) (sv iv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 34 (sISU n sv l iv false)
      (.next (.storeK [] [] (.seqn #[]) ([] :: [] :: envISU)
        suIStoreTail)) ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < ((n : Nat) : Int)))) suICmpK,
          sISU n sv l
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false, ch) := by
  with_unfolding_all rfl

/-- One setup iteration from the exit-test's true delivery at `i`:
body → the element store (the wrapped multiplicative family value) →
head → `i++` → the next test delivery. 57 steps. The per-iteration
composite the P5 iteration schema consumes. -/
private theorem hIsu_iter (n seed i : Nat) (hn : n < 2 ^ 63) (hi : i < n)
    (ch : Choices) :
    stepFnIter 57
      (sISU n (seed : Int) (isFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false)
      (.retV (.bool true) suICmpK) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) suICmpK,
          sISU n (seed : Int)
            (isFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
            ((i + 1 : Nat) : Int) false, ch) := by
  have h1 := hsegISU_body_raw n (seed : Int) ((i : Nat) : Int)
    (isFamily i seed ++ List.replicate (n - i) 0) ch
  -- clean the stored value: (seed * (i+1)) mod 2^64
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    unorm_of_range (by omega)
      (by omega : ((i + 1 : Nat) : Int) < 2 ^ 64),
    show ((seed : Nat) : Int) * ((i + 1 : Nat) : Int)
      = ((seed * (i + 1) : Nat) : Int) from
      (Int.natCast_mul seed (i + 1)).symm,
    unorm_nat_mod (seed * (i + 1))] at h1
  have h2 := hstep_Istore_setup n (seed : Int)
    (isFamily i seed ++ List.replicate (n - i) 0) i
    (((seed * (i + 1)) % 2 ^ 64 : Nat) : Int) hi
    (by rw [List.length_append, isFamily_length, List.length_replicate]
        omega)
    (isFamilyZ_range (by omega))
    ⟨by omega, by
      have := Nat.mod_lt (seed * (i + 1)) (y := 2 ^ 64) (by omega)
      omega⟩
    ((i : Nat) : Int) ch
  rw [isFamily_set hi] at h2
  have h3 := hsegISU_d1_raw n (seed : Int) ((i : Nat) : Int)
    (isFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    unorm_of_range (by omega)
      (by omega : ((i + 1 : Nat) : Int) < 2 ^ 64),
    unorm_of_range (by omega)
      (by omega : ((i + 1 : Nat) : Int) < 2 ^ 64)] at h3
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- **The setup loop**: exactly `57·(n-i)` steps materialize the
wrapped multiplicative family — the P5 iteration schema
(`stepFnIter_iterate`) at the per-iteration composite above; the
per-example `strongRecOn` boilerplate this theorem used to carry is
deleted (Gallery Campaign G0 item 3a retrofit). Statement unchanged
(the vestigial `μ` binder kept for consumer compatibility). -/
theorem hIsetup_loop (n seed : Nat) (hn : n < 2 ^ 63) :
    ∀ μ i, μ = n - i → i ≤ n → ∀ ch : Choices,
    stepFnIter (57 * (n - i))
      (sISU n (seed : Int) (isFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false)
      (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
        suICmpK) ch
      = .ok (.retV (.bool (decide (((n : Nat) : Int) < ((n : Nat) : Int))))
            suICmpK,
          sISU n (seed : Int) (isFamily n seed) ((n : Nat) : Int) false,
          ch) := by
  intro _ i _ hin ch
  have hgen := stepFnIter_iterate (c := 57) (n := n)
    (T := fun j => sISU n (seed : Int)
      (isFamily j seed ++ List.replicate (n - j) 0) ((j : Nat) : Int) false)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int)
      < ((n : Nat) : Int)))) suICmpK)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by omega)]
      exact hIsu_iter n seed j hn hj ch')
    i hin ch
  simpa using hgen


end GoLean.Examples.InsertionSort
