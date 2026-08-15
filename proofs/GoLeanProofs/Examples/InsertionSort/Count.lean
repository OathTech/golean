import GoLeanProofs.Examples.InsertionSortProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Rename
import GoLeanProofs.Frame.Sim
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Examples.InsertionSort.Canon
import GoLeanProofs.Examples.InsertionSort.PassFrame
import GoLeanProofs.Examples.InsertionSort.Rebuild
import GoLeanProofs.Examples.InsertionSort.Setup
import GoLeanProofs.Examples.InsertionSort.Subject

/-!
# InsertionSort — Count

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

/-! ## The test phase, part 3: the O(n²) count loops (the permutation
check). The outer count loop re-allocates `cs`/`ct`/`j`/`$forFirst`
every pass — the SECOND frame-rebase layer (threshold 21, retire FOUR
cells per pass). Count cells: 19 = the count `i`, 20 = its flag;
tight pass placement 21 = `cs`, 22 = `ct`, 23 = `j`, 24 = its flag. -/

def envCNT : LocalEnv :=
  [[("$forFirst", .base ⟨20⟩)], [("i", .base ⟨19⟩)], tScope, hIScope0]

/-- The count inner loop's desugared body (from the pinned record). -/
abbrev isortCountInnerBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "j")
          (.add (.var "j") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "j") (.var "n"))
        (.seqn #[])
        .breakStmt,
      .block #[]
        #[.ifThenElse
            (.eqCmp (.int .uint64)
              (.indexGet (.var "s") (.var "j"))
              (.indexGet (.var "t") (.var "i")))
            (.block #[]
              #[.assign (.var "cs")
                  (.add (.var "cs") (.intLit 1 .uint64))])
            (.seqn #[]),
          .ifThenElse
            (.eqCmp (.int .uint64)
              (.indexGet (.var "t") (.var "j"))
              (.indexGet (.var "t") (.var "i")))
            (.block #[]
              #[.assign (.var "ct")
                  (.add (.var "ct") (.intLit 1 .uint64))])
            (.seqn #[])]]

/-- The count pass block (`cs`/`ct` declarations, the `j` loop, the
`cs != ct` verdict fold). -/
abbrev isortCountPassBlk : Stmt :=
  .block #[]
    #[.seqn
        #[.initialization { id := "cs", typ := .int .uint64 },
          .assign (.var "cs") (.intLit 0 .uint64)],
      .seqn
        #[.initialization { id := "ct", typ := .int .uint64 },
          .assign (.var "ct") (.intLit 0 .uint64)],
      .block #[]
        #[.seqn
            #[.initialization { id := "j", typ := .int .uint64 },
              .assign (.var "j") (.intLit 0 .uint64)],
          .block #[]
            #[.initialization { id := "$forFirst", typ := .bool },
              .assign (.var "$forFirst") (.boolLit true),
              .while (.boolLit true) isortCountInnerBody]],
      .ifThenElse
        (.neqCmp (.int .uint64) (.var "cs") (.var "ct"))
        (.block #[] #[.seqn #[.assign (.var "ok") (.intLit 0 .uint64)]])
        (.seqn #[])]

/-- The count OUTER loop's desugared body. -/
abbrev isortCountOuterBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i")
          (.add (.var "i") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n"))
        (.seqn #[])
        .breakStmt,
      isortCountPassBlk]

def cntTail : Cont :=
  .seq [] envCNT
    (.seq [] [[("i", .base ⟨19⟩)], tScope, hIScope0]
      (.seq (hIBodyList.drop 10) envT hIFrame0))
def cntHeadCfg : Config :=
  .exec (.while (.boolLit true) isortCountOuterBody) envCNT cntTail
def cntLoopK : Cont :=
  .loop (.boolLit true) isortCountOuterBody envCNT cntTail
def cntCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envCNT)
    (.seq [isortCountPassBlk] ([] :: envCNT) cntLoopK)

def envP : LocalEnv :=
  [("ct", .base ⟨22⟩), ("cs", .base ⟨21⟩)] :: [] :: envCNT
def envCJ : LocalEnv :=
  [("$forFirst", .base ⟨24⟩)] :: [("j", .base ⟨23⟩)] :: envP
def cntNeqIf : Stmt :=
  .ifThenElse (.neqCmp (.int .uint64) (.var "cs") (.var "ct"))
    (.block #[] #[.seqn #[.assign (.var "ok") (.intLit 0 .uint64)]])
    (.seqn #[])
def cntInTail : Cont :=
  .seq [] envCJ
    (.seq [] ([("j", .base ⟨23⟩)] :: envP)
      (.seq [cntNeqIf] envP (.seq [] ([] :: envCNT) cntLoopK)))
def cntInHeadCfg : Config :=
  .exec (.while (.boolLit true) isortCountInnerBody) envCJ cntInTail
def cntInLoopK : Cont :=
  .loop (.boolLit true) isortCountInnerBody envCJ cntInTail
def cntChkBlk : Stmt :=
  .block #[]
    #[.ifThenElse
        (.eqCmp (.int .uint64)
          (.indexGet (.var "s") (.var "j"))
          (.indexGet (.var "t") (.var "i")))
        (.block #[]
          #[.assign (.var "cs") (.add (.var "cs") (.intLit 1 .uint64))])
        (.seqn #[]),
      .ifThenElse
        (.eqCmp (.int .uint64)
          (.indexGet (.var "t") (.var "j"))
          (.indexGet (.var "t") (.var "i")))
        (.block #[]
          #[.assign (.var "ct") (.add (.var "ct") (.intLit 1 .uint64))])
        (.seqn #[])]
def cntInCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envCJ)
    (.seq [cntChkBlk] ([] :: envCJ) cntInLoopK)
def env2C : LocalEnv := [] :: [] :: envCJ
def cntIf2Stmt : Stmt :=
  .ifThenElse
    (.eqCmp (.int .uint64)
      (.indexGet (.var "t") (.var "j"))
      (.indexGet (.var "t") (.var "i")))
    (.block #[]
      #[.assign (.var "ct") (.add (.var "ct") (.intLit 1 .uint64))])
    (.seqn #[])
def cntIf1K : Cont :=
  .ifK (.block #[]
      #[.assign (.var "cs") (.add (.var "cs") (.intLit 1 .uint64))])
    (.seqn #[]) env2C
    (.seq [cntIf2Stmt] env2C (.seq [] ([] :: envCJ) cntInLoopK))
def cntIf2K : Cont :=
  .ifK (.block #[]
      #[.assign (.var "ct") (.add (.var "ct") (.intLit 1 .uint64))])
    (.seqn #[]) env2C
    (.seq [] env2C (.seq [] ([] :: envCJ) cntInLoopK))
def cntEq1K1 : Cont :=
  .strictK (.eqCmp (.int .uint64)) []
    [.indexGet (.var "t") (.var "i")] env2C cntIf1K
def cntEq1K2 (w : GoValue) : Cont :=
  .strictK (.eqCmp (.int .uint64)) [w] [] env2C cntIf1K
def cntEq2K1 : Cont :=
  .strictK (.eqCmp (.int .uint64)) []
    [.indexGet (.var "t") (.var "i")] env2C cntIf2K
def cntEq2K2 (w : GoValue) : Cont :=
  .strictK (.eqCmp (.int .uint64)) [w] [] env2C cntIf2K
def cntNeqIfK : Cont :=
  .ifK (.block #[] #[.seqn #[.assign (.var "ok") (.intLit 0 .uint64)]])
    (.seqn #[]) envP (.seq [] envP (.seq [] ([] :: envCNT) cntLoopK))

/-- The count-phase outer state family, TAIL-PARAMETRIC (fixed cells
0–20: the harness cells, the parked scan/rebuild counters, the count
counter at 19 and flag at 20). -/
def σCntOutT (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ : Int) (ffv : Bool) (tail : Heap) (na : Nat) : ExecState :=
  σHOutT n seed l ivF false
    ([(.base ⟨11⟩, ucell 1), (.base ⟨12⟩, ucell sciv),
      (.base ⟨13⟩, bcell false), (.base ⟨14⟩, hTHandleCell n),
      (.base ⟨15⟩, arrCell n tl), (.base ⟨16⟩, hTHandleCell n),
      (.base ⟨17⟩, ucell ((n : Nat) : Int)), (.base ⟨18⟩, bcell false),
      (.base ⟨19⟩, ucell civ), (.base ⟨20⟩, bcell ffv)] ++ tail)
    na

/-- The tight 21-cell count-outer state. -/
def σCntOut (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ : Int) (ffv : Bool) : ExecState :=
  σCntOutT n seed ivF sciv l tl civ ffv [] 21

/-- The tight 25-cell in-pass count state (`cs`/`ct`/`j`/flag at
21–24). -/
def σCntIn (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ csv ctv jv : Int) (jffv : Bool) : ExecState :=
  σCntOutT n seed ivF sciv l tl civ false
    [(.base ⟨21⟩, ucell csv), (.base ⟨22⟩, ucell ctv),
     (.base ⟨23⟩, ucell jv), (.base ⟨24⟩, bcell jffv)]
    25

/-- The terminal state: verdict 1 delivered to the result cell 2. -/
def σCntEnd (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ : Int) (tail : Heap) (na : Nat) : ExecState :=
  { types := isortLowered.typeDefs.toList,
    functions := isortLowered.funcs,
    methods := isortLowered.methods,
    heap := (.base ⟨0⟩, ucell (n : Int)) :: (.base ⟨1⟩, ucell (seed : Int))
      :: (.base ⟨2⟩, ucell 1) :: (.base ⟨3⟩, hIHandleCell n)
      :: (.base ⟨4⟩, arrCell n l) :: (.base ⟨5⟩, hIHandleCell n)
      :: (.base ⟨6⟩, ucell ((n : Nat) : Int)) :: (.base ⟨7⟩, bcell false)
      :: (.base ⟨8⟩, hIHandleCell n) :: (.base ⟨9⟩, intcell ivF)
      :: (.base ⟨10⟩, bcell false)
      :: ([(.base ⟨11⟩, ucell 1), (.base ⟨12⟩, ucell sciv),
          (.base ⟨13⟩, bcell false), (.base ⟨14⟩, hTHandleCell n),
          (.base ⟨15⟩, arrCell n tl), (.base ⟨16⟩, hTHandleCell n),
          (.base ⟨17⟩, ucell ((n : Nat) : Int)), (.base ⟨18⟩, bcell false),
          (.base ⟨19⟩, ucell civ), (.base ⟨20⟩, bcell false)] ++ tail),
    nextAddr := na }

/-- Rebuild exit → break unwinding → the count `i := 0` at 19, the
flag at 20 → the count outer head. 35 steps (trace 1284→1319). -/
theorem hcnt_entry_raw (n seed : Nat) (ivF sciv : Int)
    (l tl : List Int) (ch : Choices) :
    stepFnIter 35 (σRB n seed ivF sciv l tl ((n : Nat) : Int) false)
      (.retV (.bool false) rbCmpK) ch
      = .ok (cntHeadCfg, σCntOut n seed ivF sciv l tl 0 true, ch) := by
  with_unfolding_all rfl

/-- Count outer first-pass dispatch (tail-parametric). -/
theorem hcnt_d0_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ : Int) (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 25 (σCntOutT n seed ivF sciv l tl civ true tail na)
      cntHeadCfg ch
      = .ok (.retV (.bool (decide (civ < ((n : Nat) : Int)))) cntCmpK,
          σCntOutT n seed ivF sciv l tl civ false tail na, ch) := by
  with_unfolding_all rfl

/-- Count outer later-pass dispatch: `i := i + 1`, then the test. -/
private theorem hcnt_d1_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ : Int) (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 29 (σCntOutT n seed ivF sciv l tl civ false tail na)
      cntHeadCfg ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1))
              < ((n : Nat) : Int)))) cntCmpK,
          σCntOutT n seed ivF sciv l tl
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1)))
            false tail na, ch) := by
  with_unfolding_all rfl

/-- Count pass entry: outer test true → `cs`/`ct`/`j`/flag allocated
at 21–24 (TIGHT placement only) → the inner loop head. 59 steps
(trace 1344→1403). -/
private theorem hcnt_PA_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ : Int) (ch : Choices) :
    stepFnIter 59 (σCntOut n seed ivF sciv l tl civ false)
      (.retV (.bool true) cntCmpK) ch
      = .ok (cntInHeadCfg, σCntIn n seed ivF sciv l tl civ 0 0 0 true, ch) := by
  with_unfolding_all rfl

/-- Count inner first-pass dispatch. -/
private theorem hcnt_i0_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ csv ctv jv : Int) (ch : Choices) :
    stepFnIter 25 (σCntIn n seed ivF sciv l tl civ csv ctv jv true)
      cntInHeadCfg ch
      = .ok (.retV (.bool (decide (jv < ((n : Nat) : Int)))) cntInCmpK,
          σCntIn n seed ivF sciv l tl civ csv ctv jv false, ch) := by
  with_unfolding_all rfl

/-- Count inner later-pass dispatch: `j := j + 1`, then the test. -/
private theorem hcnt_i1_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ csv ctv jv : Int) (ch : Choices) :
    stepFnIter 29 (σCntIn n seed ivF sciv l tl civ csv ctv jv false)
      cntInHeadCfg ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (jv + 1))
              < ((n : Nat) : Int)))) cntInCmpK,
          σCntIn n seed ivF sciv l tl civ csv ctv
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (jv + 1)))
            false, ch) := by
  with_unfolding_all rfl

/-- Count check phase A: inner test true → the `s[j]` read's apply. -/
private theorem hcnt_A_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ csv ctv jv : Int) (ch : Choices) :
    stepFnIter 11 (σCntIn n seed ivF sciv l tl civ csv ctv jv false)
      (.retV (.bool true) cntInCmpK) ch
      = .ok (.retV (.int jv .uint64)
            (.strictK .indexGet [hISliceH n] [] env2C cntEq1K1),
          σCntIn n seed ivF sciv l tl civ csv ctv jv false, ch) := by
  with_unfolding_all rfl

/-- Count check phase B: `s[j]` in → the `t[i]` read's apply. -/
private theorem hcnt_B_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ csv ctv jv : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 5 (σCntIn n seed ivF sciv l tl civ csv ctv jv false)
      (.retV w cntEq1K1) ch
      = .ok (.retV (.int civ .uint64)
            (.strictK .indexGet [hTSliceH n] [] env2C (cntEq1K2 w)),
          σCntIn n seed ivF sciv l tl civ csv ctv jv false, ch) := by
  with_unfolding_all rfl

/-- Count check phase C: both in → the equality delivered at if 1. -/
private theorem hcnt_C_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ csv ctv jv a b : Int) (ch : Choices) :
    stepFnIter 1 (σCntIn n seed ivF sciv l tl civ csv ctv jv false)
      (.retV (.int b .uint64) (cntEq1K2 (.int a .uint64))) ch
      = .ok (.retV (.bool (a == b)) cntIf1K,
          σCntIn n seed ivF sciv l tl civ csv ctv jv false, ch) := by
  with_unfolding_all rfl

/-- Count check D (equal case): `cs++` → the `t[j]` read's apply of
if 2. 23 steps. -/
private theorem hcnt_D1_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ csv ctv jv : Int) (ch : Choices) :
    stepFnIter 23 (σCntIn n seed ivF sciv l tl civ csv ctv jv false)
      (.retV (.bool true) cntIf1K) ch
      = .ok (.retV (.int jv .uint64)
            (.strictK .indexGet [hTSliceH n] [] env2C cntEq2K1),
          σCntIn n seed ivF sciv l tl civ
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (csv + 1)))
            ctv jv false, ch) := by
  with_unfolding_all rfl

/-- Count check D (unequal case): `cs` untouched → the same apply
point. 9 steps. -/
private theorem hcnt_D0_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ csv ctv jv : Int) (ch : Choices) :
    stepFnIter 9 (σCntIn n seed ivF sciv l tl civ csv ctv jv false)
      (.retV (.bool false) cntIf1K) ch
      = .ok (.retV (.int jv .uint64)
            (.strictK .indexGet [hTSliceH n] [] env2C cntEq2K1),
          σCntIn n seed ivF sciv l tl civ csv ctv jv false, ch) := by
  with_unfolding_all rfl

/-- Count check phase E: `t[j]` in → the `t[i]` read's apply of if 2. -/
private theorem hcnt_E_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ csv ctv jv : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 5 (σCntIn n seed ivF sciv l tl civ csv ctv jv false)
      (.retV w cntEq2K1) ch
      = .ok (.retV (.int civ .uint64)
            (.strictK .indexGet [hTSliceH n] [] env2C (cntEq2K2 w)),
          σCntIn n seed ivF sciv l tl civ csv ctv jv false, ch) := by
  with_unfolding_all rfl

/-- Count check phase F: both in → the equality delivered at if 2. -/
private theorem hcnt_F_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ csv ctv jv a b : Int) (ch : Choices) :
    stepFnIter 1 (σCntIn n seed ivF sciv l tl civ csv ctv jv false)
      (.retV (.int b .uint64) (cntEq2K2 (.int a .uint64))) ch
      = .ok (.retV (.bool (a == b)) cntIf2K,
          σCntIn n seed ivF sciv l tl civ csv ctv jv false, ch) := by
  with_unfolding_all rfl

/-- Count check G (equal case): `ct++` → the inner loop head. -/
private theorem hcnt_G1_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ csv ctv jv : Int) (ch : Choices) :
    stepFnIter 19 (σCntIn n seed ivF sciv l tl civ csv ctv jv false)
      (.retV (.bool true) cntIf2K) ch
      = .ok (cntInHeadCfg,
          σCntIn n seed ivF sciv l tl civ csv
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (ctv + 1)))
            jv false, ch) := by
  with_unfolding_all rfl

/-- Count check G (unequal case): → the inner loop head. -/
private theorem hcnt_G0_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ csv ctv jv : Int) (ch : Choices) :
    stepFnIter 5 (σCntIn n seed ivF sciv l tl civ csv ctv jv false)
      (.retV (.bool false) cntIf2K) ch
      = .ok (cntInHeadCfg,
          σCntIn n seed ivF sciv l tl civ csv ctv jv false, ch) := by
  with_unfolding_all rfl

/-- Count pass exit: inner test false → break unwinding → the
`cs != ct` comparison delivered. 13 steps (trace 1736→1749). -/
private theorem hcnt_X1_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ csv ctv jv : Int) (ch : Choices) :
    stepFnIter 13 (σCntIn n seed ivF sciv l tl civ csv ctv jv false)
      (.retV (.bool false) cntInCmpK) ch
      = .ok (.retV (.bool (!(csv == ctv))) cntNeqIfK,
          σCntIn n seed ivF sciv l tl civ csv ctv jv false, ch) := by
  with_unfolding_all rfl

/-- Count pass exit, equal counts: the verdict untouched → the outer
loop head. 5 steps. -/
private theorem hcnt_X2_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ csv ctv jv : Int) (ch : Choices) :
    stepFnIter 5 (σCntIn n seed ivF sciv l tl civ csv ctv jv false)
      (.retV (.bool false) cntNeqIfK) ch
      = .ok (cntHeadCfg,
          σCntIn n seed ivF sciv l tl civ csv ctv jv false, ch) := by
  with_unfolding_all rfl

/-- **The harness exit**: count outer test false → break unwinding →
`$res0 := ok` (the verdict 1 into cell 2) → `return` → frame exit →
the driver terminal. 21 steps (trace 3100→3121); tail-parametric. -/
private theorem hcnt_exit_raw (n seed : Nat) (ivF sciv : Int)
    (l tl : List Int) (civ : Int) (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 21 (σCntOutT n seed ivF sciv l tl civ false tail na)
      (.retV (.bool false) cntCmpK) ch
      = .ok (.next .stop, σCntEnd n seed ivF sciv l tl civ tail na, ch) := by
  with_unfolding_all rfl

/-- One `s`-element read at the tight count state (backing 4). -/
private theorem stepFn_read_σCntIn_s {n seed : Nat} {ivF sciv : Int}
    {l tl : List Int} {civ csv ctv jv : Int} {k : Nat} {K : Cont}
    {ch : Choices} (hk : k < n) (hlen : l.length = n) :
    stepFn (σCntIn n seed ivF sciv l tl civ csv ctv jv false)
      (.retV (.int ((k : Nat) : Int) .uint64)
        (.strictK .indexGet [hISliceH n] [] env2C K)) ch
      = .ok (.retV (.int (l.getD k 0) .uint64) K,
          σCntIn n seed ivF sciv l tl civ csv ctv jv false, ch) :=
  stepFn_strict_apply
    (applyStrictOp_indexGet_slice (ik := .uint64) rfl
      (Nat.le_refl n) hk
      (by rw [Nat.zero_add]; exact getElem?_mapU l k (by omega)))

/-- One `t`-element read at the tight count state (backing 15). -/
private theorem stepFn_read_σCntIn_t {n seed : Nat} {ivF sciv : Int}
    {l tl : List Int} {civ csv ctv jv : Int} {k : Nat} {K : Cont}
    {ch : Choices} (hk : k < n) (hlen : tl.length = n) :
    stepFn (σCntIn n seed ivF sciv l tl civ csv ctv jv false)
      (.retV (.int ((k : Nat) : Int) .uint64)
        (.strictK .indexGet [hTSliceH n] [] env2C K)) ch
      = .ok (.retV (.int (tl.getD k 0) .uint64) K,
          σCntIn n seed ivF sciv l tl civ csv ctv jv false, ch) :=
  stepFn_strict_apply
    (applyStrictOp_indexGet_slice (ik := .uint64) rfl
      (Nat.le_refl n) hk
      (by rw [Nat.zero_add]; exact getElem?_mapU tl k (by omega)))

/-! ### The pure counting layer (the accumulator invariant's bridge to
`List.count`, closed by `sortSpec_count`) -/

/-- The accumulator's meaning: occurrences of `v` in a list. -/
def cntSpec (v : Int) : List Int → Nat
  | [] => 0
  | x :: rest => cntSpec v rest + (if x = v then 1 else 0)

private theorem cntSpec_append (v : Int) (a b : List Int) :
    cntSpec v (a ++ b) = cntSpec v a + cntSpec v b := by
  induction a with
  | nil => simp [cntSpec]
  | cons x rest ih =>
      simp only [List.cons_append, cntSpec, ih]
      omega

private theorem cntSpec_take_succ {l : List Int} {v : Int} {j : Nat}
    (hj : j < l.length) :
    cntSpec v (l.take (j + 1))
      = cntSpec v (l.take j) + (if l.getD j 0 = v then 1 else 0) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  show cntSpec v (l.take j ++ [l[j]]) = _
  rw [cntSpec_append]
  have hgd : l.getD j 0 = l[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  rw [hgd]
  simp [cntSpec]

private theorem cntSpec_le_length (v : Int) (l : List Int) :
    cntSpec v l ≤ l.length := by
  induction l with
  | nil => simp [cntSpec]
  | cons x rest ih =>
      simp only [cntSpec, List.length_cons]
      split <;> omega

private theorem cntSpec_take_le {l : List Int} {v : Int} (j : Nat) :
    cntSpec v (l.take j) ≤ j := by
  calc cntSpec v (l.take j) ≤ (l.take j).length := cntSpec_le_length v _
    _ ≤ j := by rw [List.length_take]; omega

theorem cntSpec_eq_count (v : Int) (l : List Int) :
    cntSpec v l = l.count v := by
  induction l with
  | nil => simp [cntSpec]
  | cons x rest ih =>
      rw [cntSpec, ih, List.count_cons]
      by_cases h : x = v
      · simp [h, beq_iff_eq]
      · simp [h, beq_iff_eq]

/-! ### One count-inner iteration, then the inner induction -/

/-- **One count-inner iteration** from the inner test's true delivery
at `j`: read `s[j]`/`t[p]`, conditionally `cs++`; read `t[j]`/`t[p]`,
conditionally `ct++`; dispatch. Both accumulators advance to the
`take (j+1)` counts. ≤ 98 steps. -/
private theorem hcnt_iter (n seed : Nat) (hn : n < 2 ^ 63) (ivF sciv : Int)
    (l tl : List Int) (hll : l.length = n) (htl : tl.length = n)
    (p : Nat) (hp : p < n) (j : Nat) (hj : j < n) (ch : Choices) :
    ∃ k : Nat, k ≤ 98 ∧
      stepFnIter k (σCntIn n seed ivF sciv l tl ((p : Nat) : Int)
          ((cntSpec (tl.getD p 0) (l.take j) : Nat) : Int)
          ((cntSpec (tl.getD p 0) (tl.take j) : Nat) : Int)
          ((j : Nat) : Int) false)
        (.retV (.bool true) cntInCmpK) ch
        = .ok (.retV (.bool (decide
              (((j + 1 : Nat) : Int) < ((n : Nat) : Int)))) cntInCmpK,
            σCntIn n seed ivF sciv l tl ((p : Nat) : Int)
              ((cntSpec (tl.getD p 0) (l.take (j + 1)) : Nat) : Int)
              ((cntSpec (tl.getD p 0) (tl.take (j + 1)) : Nat) : Int)
              ((j + 1 : Nat) : Int) false, ch) := by
  have hcsle := cntSpec_take_le (l := l) (v := tl.getD p 0) j
  have hctle := cntSpec_take_le (l := tl) (v := tl.getD p 0) j
  -- phase 1: the two reads and the first equality
  have hA := hcnt_A_raw n seed ivF sciv l tl ((p : Nat) : Int)
    ((cntSpec (tl.getD p 0) (l.take j) : Nat) : Int)
    ((cntSpec (tl.getD p 0) (tl.take j) : Nat) : Int) ((j : Nat) : Int) ch
  have hrdS := stepFn_read_σCntIn_s (n := n) (seed := seed) (ivF := ivF)
    (sciv := sciv) (l := l) (tl := tl) (civ := ((p : Nat) : Int))
    (csv := ((cntSpec (tl.getD p 0) (l.take j) : Nat) : Int))
    (ctv := ((cntSpec (tl.getD p 0) (tl.take j) : Nat) : Int))
    (jv := ((j : Nat) : Int)) (k := j) (K := cntEq1K1) (ch := ch) hj hll
  have hB := hcnt_B_raw n seed ivF sciv l tl ((p : Nat) : Int)
    ((cntSpec (tl.getD p 0) (l.take j) : Nat) : Int)
    ((cntSpec (tl.getD p 0) (tl.take j) : Nat) : Int) ((j : Nat) : Int)
    (.int (l.getD j 0) .uint64) ch
  have hrdT := stepFn_read_σCntIn_t (n := n) (seed := seed) (ivF := ivF)
    (sciv := sciv) (l := l) (tl := tl) (civ := ((p : Nat) : Int))
    (csv := ((cntSpec (tl.getD p 0) (l.take j) : Nat) : Int))
    (ctv := ((cntSpec (tl.getD p 0) (tl.take j) : Nat) : Int))
    (jv := ((j : Nat) : Int)) (k := p)
    (K := cntEq1K2 (.int (l.getD j 0) .uint64)) (ch := ch) hp htl
  have hC := hcnt_C_raw n seed ivF sciv l tl ((p : Nat) : Int)
    ((cntSpec (tl.getD p 0) (l.take j) : Nat) : Int)
    ((cntSpec (tl.getD p 0) (tl.take j) : Nat) : Int) ((j : Nat) : Int)
    (l.getD j 0) (tl.getD p 0) ch
  have h19 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hA (stepFnIter_one hrdS)) hB)
    (stepFnIter_one hrdT)) hC
  -- the cs branch, factored to a uniform endpoint
  obtain ⟨kD, hkD, hD⟩ : ∃ kD : Nat, kD ≤ 23 ∧
      stepFnIter kD (σCntIn n seed ivF sciv l tl ((p : Nat) : Int)
          ((cntSpec (tl.getD p 0) (l.take j) : Nat) : Int)
          ((cntSpec (tl.getD p 0) (tl.take j) : Nat) : Int)
          ((j : Nat) : Int) false)
        (.retV (.bool ((l.getD j 0) == (tl.getD p 0))) cntIf1K) ch
        = .ok (.retV (.int ((j : Nat) : Int) .uint64)
              (.strictK .indexGet [hTSliceH n] [] env2C cntEq2K1),
            σCntIn n seed ivF sciv l tl ((p : Nat) : Int)
              ((cntSpec (tl.getD p 0) (l.take (j + 1)) : Nat) : Int)
              ((cntSpec (tl.getD p 0) (tl.take j) : Nat) : Int)
              ((j : Nat) : Int) false, ch) := by
    by_cases heq1 : l.getD j 0 = tl.getD p 0
    · rw [heq1, beq_self_eq_true]
      have hD1 := hcnt_D1_raw n seed ivF sciv l tl ((p : Nat) : Int)
        ((cntSpec (tl.getD p 0) (l.take j) : Nat) : Int)
        ((cntSpec (tl.getD p 0) (tl.take j) : Nat) : Int)
        ((j : Nat) : Int) ch
      rw [show ((cntSpec (tl.getD p 0) (l.take j) : Nat) : Int) + 1
            = ((cntSpec (tl.getD p 0) (l.take j) + 1 : Nat) : Int) from by
          omega,
        unorm_of_range (by omega) (by omega :
          ((cntSpec (tl.getD p 0) (l.take j) + 1 : Nat) : Int) < 2 ^ 64),
        unorm_of_range (by omega) (by omega :
          ((cntSpec (tl.getD p 0) (l.take j) + 1 : Nat) : Int) < 2 ^ 64)]
        at hD1
      rw [show cntSpec (tl.getD p 0) (l.take (j + 1))
            = cntSpec (tl.getD p 0) (l.take j) + 1 from by
          rw [cntSpec_take_succ (by omega), if_pos heq1]]
      exact ⟨23, by omega, hD1⟩
    · rw [beq_eq_false_iff_ne.mpr heq1]
      rw [show cntSpec (tl.getD p 0) (l.take (j + 1))
            = cntSpec (tl.getD p 0) (l.take j) from by
          rw [cntSpec_take_succ (by omega), if_neg heq1]; omega]
      exact ⟨9, by omega, hcnt_D0_raw n seed ivF sciv l tl ((p : Nat) : Int)
        ((cntSpec (tl.getD p 0) (l.take j) : Nat) : Int)
        ((cntSpec (tl.getD p 0) (tl.take j) : Nat) : Int)
        ((j : Nat) : Int) ch⟩
  -- phase 2: the t reads and the second equality
  have hrdT2 := stepFn_read_σCntIn_t (n := n) (seed := seed) (ivF := ivF)
    (sciv := sciv) (l := l) (tl := tl) (civ := ((p : Nat) : Int))
    (csv := ((cntSpec (tl.getD p 0) (l.take (j + 1)) : Nat) : Int))
    (ctv := ((cntSpec (tl.getD p 0) (tl.take j) : Nat) : Int))
    (jv := ((j : Nat) : Int)) (k := j) (K := cntEq2K1) (ch := ch) hj htl
  have hE := hcnt_E_raw n seed ivF sciv l tl ((p : Nat) : Int)
    ((cntSpec (tl.getD p 0) (l.take (j + 1)) : Nat) : Int)
    ((cntSpec (tl.getD p 0) (tl.take j) : Nat) : Int) ((j : Nat) : Int)
    (.int (tl.getD j 0) .uint64) ch
  have hrdT3 := stepFn_read_σCntIn_t (n := n) (seed := seed) (ivF := ivF)
    (sciv := sciv) (l := l) (tl := tl) (civ := ((p : Nat) : Int))
    (csv := ((cntSpec (tl.getD p 0) (l.take (j + 1)) : Nat) : Int))
    (ctv := ((cntSpec (tl.getD p 0) (tl.take j) : Nat) : Int))
    (jv := ((j : Nat) : Int)) (k := p)
    (K := cntEq2K2 (.int (tl.getD j 0) .uint64)) (ch := ch) hp htl
  have hF := hcnt_F_raw n seed ivF sciv l tl ((p : Nat) : Int)
    ((cntSpec (tl.getD p 0) (l.take (j + 1)) : Nat) : Int)
    ((cntSpec (tl.getD p 0) (tl.take j) : Nat) : Int) ((j : Nat) : Int)
    (tl.getD j 0) (tl.getD p 0) ch
  -- the ct branch, factored
  obtain ⟨kG, hkG, hG⟩ : ∃ kG : Nat, kG ≤ 19 ∧
      stepFnIter kG (σCntIn n seed ivF sciv l tl ((p : Nat) : Int)
          ((cntSpec (tl.getD p 0) (l.take (j + 1)) : Nat) : Int)
          ((cntSpec (tl.getD p 0) (tl.take j) : Nat) : Int)
          ((j : Nat) : Int) false)
        (.retV (.bool ((tl.getD j 0) == (tl.getD p 0))) cntIf2K) ch
        = .ok (cntInHeadCfg,
            σCntIn n seed ivF sciv l tl ((p : Nat) : Int)
              ((cntSpec (tl.getD p 0) (l.take (j + 1)) : Nat) : Int)
              ((cntSpec (tl.getD p 0) (tl.take (j + 1)) : Nat) : Int)
              ((j : Nat) : Int) false, ch) := by
    by_cases heq2 : tl.getD j 0 = tl.getD p 0
    · rw [heq2, beq_self_eq_true]
      have hG1 := hcnt_G1_raw n seed ivF sciv l tl ((p : Nat) : Int)
        ((cntSpec (tl.getD p 0) (l.take (j + 1)) : Nat) : Int)
        ((cntSpec (tl.getD p 0) (tl.take j) : Nat) : Int)
        ((j : Nat) : Int) ch
      rw [show ((cntSpec (tl.getD p 0) (tl.take j) : Nat) : Int) + 1
            = ((cntSpec (tl.getD p 0) (tl.take j) + 1 : Nat) : Int) from by
          omega,
        unorm_of_range (by omega) (by omega :
          ((cntSpec (tl.getD p 0) (tl.take j) + 1 : Nat) : Int) < 2 ^ 64),
        unorm_of_range (by omega) (by omega :
          ((cntSpec (tl.getD p 0) (tl.take j) + 1 : Nat) : Int) < 2 ^ 64)]
        at hG1
      rw [show cntSpec (tl.getD p 0) (tl.take (j + 1))
            = cntSpec (tl.getD p 0) (tl.take j) + 1 from by
          rw [cntSpec_take_succ (by omega), if_pos heq2]]
      exact ⟨19, by omega, hG1⟩
    · rw [beq_eq_false_iff_ne.mpr heq2]
      rw [show cntSpec (tl.getD p 0) (tl.take (j + 1))
            = cntSpec (tl.getD p 0) (tl.take j) from by
          rw [cntSpec_take_succ (by omega), if_neg heq2]; omega]
      exact ⟨5, by omega, hcnt_G0_raw n seed ivF sciv l tl ((p : Nat) : Int)
        ((cntSpec (tl.getD p 0) (l.take (j + 1)) : Nat) : Int)
        ((cntSpec (tl.getD p 0) (tl.take j) : Nat) : Int)
        ((j : Nat) : Int) ch⟩
  -- the dispatch
  have hi1 := hcnt_i1_raw n seed ivF sciv l tl ((p : Nat) : Int)
    ((cntSpec (tl.getD p 0) (l.take (j + 1)) : Nat) : Int)
    ((cntSpec (tl.getD p 0) (tl.take (j + 1)) : Nat) : Int)
    ((j : Nat) : Int) ch
  rw [show ((j : Nat) : Int) + 1 = ((j + 1 : Nat) : Int) from by omega,
    unorm_of_range (by omega) (by omega : ((j + 1 : Nat) : Int) < 2 ^ 64),
    unorm_of_range (by omega) (by omega : ((j + 1 : Nat) : Int) < 2 ^ 64)]
    at hi1
  refine ⟨19 + kD + 1 + 5 + 1 + 1 + kG + 29, by omega, ?_⟩
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain h19 hD) (stepFnIter_one hrdT2)) hE)
      (stepFnIter_one hrdT3)) hF) hG) hi1

/-- **The count inner loop**: from the inner test delivery at `j`, the
accumulators reach the FULL counts at `j = n`, within `110·μ` steps. -/
private theorem hcnt_inner (n seed : Nat) (hn : n < 2 ^ 63) (ivF sciv : Int)
    (l tl : List Int) (hll : l.length = n) (htl : tl.length = n)
    (p : Nat) (hp : p < n) :
    ∀ μ j, μ = n - j → j ≤ n → ∀ ch : Choices,
    ∃ k : Nat, k ≤ 110 * μ ∧
      stepFnIter k (σCntIn n seed ivF sciv l tl ((p : Nat) : Int)
          ((cntSpec (tl.getD p 0) (l.take j) : Nat) : Int)
          ((cntSpec (tl.getD p 0) (tl.take j) : Nat) : Int)
          ((j : Nat) : Int) false)
        (.retV (.bool (decide (((j : Nat) : Int) < ((n : Nat) : Int))))
          cntInCmpK) ch
        = .ok (.retV (.bool false) cntInCmpK,
            σCntIn n seed ivF sciv l tl ((p : Nat) : Int)
              ((cntSpec (tl.getD p 0) l : Nat) : Int)
              ((cntSpec (tl.getD p 0) tl : Nat) : Int)
              ((n : Nat) : Int) false, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro j hμ hjn ch
    rcases Nat.lt_or_ge j n with hlt | hge
    · rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      obtain ⟨kit, hkit, hit⟩ := hcnt_iter n seed hn ivF sciv l tl hll htl
        p hp j hlt ch
      obtain ⟨k, hk, hrun⟩ := ih (n - (j + 1)) (by omega) (j + 1) rfl
        (by omega) ch
      refine ⟨kit + k, ?_, stepFnIter_chain hit hrun⟩
      have hmul : 110 * (n - (j + 1)) + 110 = 110 * (n - j) := by
        rw [← Nat.mul_succ]
        congr 1
        omega
      omega
    · have hEq : j = n := by omega
      subst hEq
      rw [show (decide (((j : Nat) : Int) < ((j : Nat) : Int))) = false from
        decide_eq_false (by omega)]
      rw [show l.take j = l from List.take_of_length_le (by omega),
        show tl.take j = tl from List.take_of_length_le (by omega)]
      exact ⟨0, by omega, rfl⟩

/-- **One count pass at the tight placement** (outer test true → the
NEXT outer test delivery at the 25-cell state): the inner loop counts
the pass's probe value in both arrays; the counts AGREE (`hcount`), so
the verdict is untouched. -/
private theorem hcnt_pass_seg (n seed : Nat) (hn : n < 2 ^ 63)
    (ivF sciv : Int) (l tl : List Int) (hll : l.length = n)
    (htl : tl.length = n)
    (hcount : ∀ v, cntSpec v l = cntSpec v tl)
    (p : Nat) (hp : p < n) (ch : Choices) :
    ∃ k : Nat, k ≤ 110 * n + 160 ∧
      stepFnIter k (σCntOut n seed ivF sciv l tl ((p : Nat) : Int) false)
        (.retV (.bool true) cntCmpK) ch
        = .ok (.retV (.bool (decide
              (((p + 1 : Nat) : Int) < ((n : Nat) : Int)))) cntCmpK,
            σCntIn n seed ivF sciv l tl ((p + 1 : Nat) : Int)
              ((cntSpec (tl.getD p 0) l : Nat) : Int)
              ((cntSpec (tl.getD p 0) tl : Nat) : Int)
              ((n : Nat) : Int) false, ch) := by
  have hPA := hcnt_PA_raw n seed ivF sciv l tl ((p : Nat) : Int) ch
  have hi0 := hcnt_i0_raw n seed ivF sciv l tl ((p : Nat) : Int) 0 0 0 ch
  obtain ⟨kin, hkin, hin⟩ := hcnt_inner n seed hn ivF sciv l tl hll htl
    p hp n 0 (by omega) (by omega) ch
  rw [show ((0 : Nat) : Int) = (0 : Int) from rfl,
    show cntSpec (tl.getD p 0) (l.take 0) = 0 from rfl,
    show cntSpec (tl.getD p 0) (tl.take 0) = 0 from rfl] at hin
  have hX1 := hcnt_X1_raw n seed ivF sciv l tl ((p : Nat) : Int)
    ((cntSpec (tl.getD p 0) l : Nat) : Int)
    ((cntSpec (tl.getD p 0) tl : Nat) : Int) ((n : Nat) : Int) ch
  have hbeq : (((cntSpec (tl.getD p 0) l : Nat) : Int)
      == ((cntSpec (tl.getD p 0) tl : Nat) : Int)) = true := by
    rw [hcount (tl.getD p 0)]
    exact beq_self_eq_true _
  rw [hbeq, Bool.not_true] at hX1
  have hX2 := hcnt_X2_raw n seed ivF sciv l tl ((p : Nat) : Int)
    ((cntSpec (tl.getD p 0) l : Nat) : Int)
    ((cntSpec (tl.getD p 0) tl : Nat) : Int) ((n : Nat) : Int) ch
  have hd1 : stepFnIter 29
      (σCntIn n seed ivF sciv l tl ((p : Nat) : Int)
        ((cntSpec (tl.getD p 0) l : Nat) : Int)
        ((cntSpec (tl.getD p 0) tl : Nat) : Int) ((n : Nat) : Int) false)
      cntHeadCfg ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64
              (((p : Nat) : Int) + 1))
              < ((n : Nat) : Int)))) cntCmpK,
          σCntIn n seed ivF sciv l tl
            (IntKind.normalize .uint64 (IntKind.normalize .uint64
              (((p : Nat) : Int) + 1)))
            ((cntSpec (tl.getD p 0) l : Nat) : Int)
            ((cntSpec (tl.getD p 0) tl : Nat) : Int) ((n : Nat) : Int)
            false, ch) :=
    hcnt_d1_raw n seed ivF sciv l tl ((p : Nat) : Int)
      [(.base ⟨21⟩, ucell ((cntSpec (tl.getD p 0) l : Nat) : Int)),
       (.base ⟨22⟩, ucell ((cntSpec (tl.getD p 0) tl : Nat) : Int)),
       (.base ⟨23⟩, ucell ((n : Nat) : Int)), (.base ⟨24⟩, bcell false)]
      25 ch
  rw [show (((p : Nat) : Int) + 1) = ((p + 1 : Nat) : Int) from by omega,
    unorm_of_range (by omega) (by omega : ((p + 1 : Nat) : Int) < 2 ^ 64),
    unorm_of_range (by omega) (by omega : ((p + 1 : Nat) : Int) < 2 ^ 64)]
    at hd1
  refine ⟨59 + 25 + kin + 13 + 5 + 29, by omega, ?_⟩
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain hPA hi0) hin) hX1) hX2) hd1

/-! ### The count frame layer at threshold 21 (retire FOUR cells) -/

def ρ21 (d : Nat) : Nat → Nat := fun x => if x < 21 then x else x + d

private theorem ρ21_lt {d a : Nat} (h : a < 21) : ρ21 d a = a := if_pos h
private theorem ρ21_ge {d a : Nat} (h : 21 ≤ a) : ρ21 d a = a + d :=
  if_neg (by omega)

private theorem shiftSpec_ρ21 (d : Nat) : ShiftSpec (ρ21 d) 21 (21 + d) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    simp only [ρ21] at hxy
    split at hxy <;> split at hxy <;> omega
  · intro k
    simp only [ρ21]
    rw [if_neg (by omega)]
    omega

private theorem renCell_handleH21 (d n : Nat) :
    renameCell (ρ21 d) (hIHandleCell n) = hIHandleCell n := by
  simp [renameCell, renameValue, renameLoc, ρ21]

private theorem renCell_handleT21 (d n : Nat) :
    renameCell (ρ21 d) (hTHandleCell n) = hTHandleCell n := by
  simp [renameCell, renameValue, renameLoc, ρ21]

private theorem lookup_σCntOut_ge {n seed : Nat} {ivF sciv : Int}
    {l tl : List Int} {civ : Int} {ffv : Bool} {a : Nat} (ha : 21 ≤ a) :
    Heap.lookup (σCntOut n seed ivF sciv l tl civ ffv).heap (.base ⟨a⟩)
      = none := by
  simp [σCntOut, σCntOutT, σHOutT, Heap.lookup, List.cons_append,
    List.nil_append, List.append_nil,
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
    beq_false_of_ne (base_ne (show (12 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (13 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (14 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (15 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (16 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (17 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (18 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (19 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (20 : Nat) ≠ a by omega))]

private theorem lookup_σCntIn_ge {n seed : Nat} {ivF sciv : Int}
    {l tl : List Int} {civ csv ctv jv : Int} {jffv : Bool} {a : Nat}
    (ha : 25 ≤ a) :
    Heap.lookup (σCntIn n seed ivF sciv l tl civ csv ctv jv jffv).heap
      (.base ⟨a⟩) = none := by
  simp [σCntIn, σCntOutT, σHOutT, Heap.lookup, List.cons_append,
    List.nil_append, List.append_nil,
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
    beq_false_of_ne (base_ne (show (12 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (13 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (14 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (15 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (16 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (17 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (18 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (19 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (20 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (21 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (22 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (23 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (24 : Nat) ≠ a by omega))]

private theorem lookup_σCntIn_field (n seed : Nat) (ivF sciv : Int)
    (l tl : List Int) (civ csv ctv jv : Int) (jffv : Bool) (b : Loc)
    (tid : TypeId) (f : String) :
    Heap.lookup (σCntIn n seed ivF sciv l tl civ csv ctv jv jffv).heap
      (.field b tid f) = none := rfl

private theorem lookup_σCntIn_index (n seed : Nat) (ivF sciv : Int)
    (l tl : List Int) (civ csv ctv jv : Int) (jffv : Bool) (b : Loc)
    (i : Int) :
    Heap.lookup (σCntIn n seed ivF sciv l tl civ csv ctv jv jffv).heap
      (.index b i) = none := rfl

/-- Root bump by 4 above the fixed count cells (threshold 21). -/
def bump4C : Loc → Loc
  | .base a => .base ⟨if a.id < 21 then a.id else a.id + 4⟩
  | .field b tid f => .field (bump4C b) tid f
  | .index b i => .index (bump4C b) i

private theorem renameLoc_bump4C (d : Nat) (l : Loc) :
    renameLoc (ρ21 (d + 4)) l = renameLoc (ρ21 d) (bump4C l) := by
  induction l with
  | base a =>
      have h : ρ21 (d + 4) a.id
          = ρ21 d (if a.id < 21 then a.id else a.id + 4) := by
        by_cases ha : a.id < 21
        · rw [if_pos ha, ρ21_lt ha, ρ21_lt ha]
        · rw [if_neg ha, ρ21_ge (d := d + 4) (a := a.id) (by omega),
            ρ21_ge (d := d) (a := a.id + 4) (by omega)]
          omega
      simp only [renameLoc, bump4C, h]
  | field b tid f ih => simp only [renameLoc, bump4C, ih]
  | index b i ih => simp only [renameLoc, bump4C, ih]

/-- The trivial-frame simulation at the count-loop entry. -/
theorem frameSim_zero21 (n seed : Nat) (ivF sciv : Int)
    (l tl : List Int) (civ : Int) (ffv : Bool) :
    FrameSim (ρ21 0) 21 21 [] (σCntOut n seed ivF sciv l tl civ ffv)
      (σCntOut n seed ivF sciv l tl civ ffv) := by
  refine ⟨shiftSpec_ρ21 0, rfl, rfl, rfl, rfl, rfl, Nat.le_refl 21,
    ?_, ?_, fun a => rfl, bodies_ρsh (ρ21 0)⟩
  · intro loc
    match loc with
    | .base ⟨a⟩ =>
        match a with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
        | 3 =>
            show Heap.lookup (σCntOut n seed ivF sciv l tl civ ffv).heap
              (.base ⟨ρ21 0 3⟩) = some (renameCell (ρ21 0) (hIHandleCell n))
            rw [renCell_handleH21 0 n]
            rfl
        | 4 =>
            show Heap.lookup (σCntOut n seed ivF sciv l tl civ ffv).heap
              (.base ⟨ρ21 0 4⟩) = some (renameCell (ρ21 0) (arrCell n l))
            rw [renCell_arr]
            rfl
        | 5 =>
            show Heap.lookup (σCntOut n seed ivF sciv l tl civ ffv).heap
              (.base ⟨ρ21 0 5⟩) = some (renameCell (ρ21 0) (hIHandleCell n))
            rw [renCell_handleH21 0 n]
            rfl
        | 6 => rfl
        | 7 => rfl
        | 8 =>
            show Heap.lookup (σCntOut n seed ivF sciv l tl civ ffv).heap
              (.base ⟨ρ21 0 8⟩) = some (renameCell (ρ21 0) (hIHandleCell n))
            rw [renCell_handleH21 0 n]
            rfl
        | 9 => rfl
        | 10 => rfl
        | 11 => rfl
        | 12 => rfl
        | 13 => rfl
        | 14 =>
            show Heap.lookup (σCntOut n seed ivF sciv l tl civ ffv).heap
              (.base ⟨ρ21 0 14⟩) = some (renameCell (ρ21 0) (hTHandleCell n))
            rw [renCell_handleT21 0 n]
            rfl
        | 15 =>
            show Heap.lookup (σCntOut n seed ivF sciv l tl civ ffv).heap
              (.base ⟨ρ21 0 15⟩) = some (renameCell (ρ21 0) (arrCell n tl))
            rw [renCell_arr]
            rfl
        | 16 =>
            show Heap.lookup (σCntOut n seed ivF sciv l tl civ ffv).heap
              (.base ⟨ρ21 0 16⟩) = some (renameCell (ρ21 0) (hTHandleCell n))
            rw [renCell_handleT21 0 n]
            rfl
        | 17 => rfl
        | 18 => rfl
        | 19 => rfl
        | 20 => rfl
        | (a + 21) =>
            show Heap.lookup (σCntOut n seed ivF sciv l tl civ ffv).heap
              (.base ⟨ρ21 0 (a + 21)⟩) = _
            rw [ρ21_ge (d := 0) (a := a + 21) (by omega)]
            rw [lookup_σCntOut_ge (a := a + 21 + 0) (by omega)]
            rfl
    | .field b tid f => rfl
    | .index b i => rfl
  · intro loc c hc
    simp [Heap.lookup] at hc

/-- **The frame rebase at threshold 21**: the pass's retired
`cs`/`ct`/`j`/flag cells (canonical 21–24) move INTO the frame at
their true addresses `21+d`–`24+d`. -/
private theorem rebaseSim21 {d : Nat} {fr : Heap} {n seed : Nat}
    {ivF sciv : Int} {l tl : List Int} {civ csv ctv jv : Int}
    {σA : ExecState}
    (h : FrameSim (ρ21 d) 21 (21 + d) fr
      (σCntIn n seed ivF sciv l tl civ csv ctv jv false) σA) :
    FrameSim (ρ21 (d + 4)) 21 (21 + (d + 4))
      (fr ++ [(.base ⟨21 + d⟩, ucell csv), (.base ⟨22 + d⟩, ucell ctv),
              (.base ⟨23 + d⟩, ucell jv), (.base ⟨24 + d⟩, bcell false)])
      (σCntOut n seed ivF sciv l tl civ false) σA := by
  refine ⟨shiftSpec_ρ21 (d + 4), h.types_eq, h.funcs_eq, h.methods_eq,
    h.methodSets_eq, ?_, Nat.le_refl 21, ?_, ?_, ?_, bodies_ρsh _⟩
  · have hne := h.next_eq
    rw [show (σCntIn n seed ivF sciv l tl civ csv ctv jv false).nextAddr = 25
        from rfl,
      ρ21_ge (d := d) (a := 25) (by omega)] at hne
    show σA.nextAddr = ρ21 (d + 4) 21
    rw [ρ21_ge (d := d + 4) (a := 21) (by omega)]
    omega
  · intro loc
    match loc with
    | .base ⟨a⟩ =>
        by_cases ha : a < 21
        · rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5
              ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨ a = 12
              ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 ∨ a = 17 ∨ a = 18
              ∨ a = 19 ∨ a = 20)
            with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
              | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
              | rfl
          · exact h.lookup_some (l := .base ⟨0⟩) (c := ucell (n : Int)) rfl
          · exact h.lookup_some (l := .base ⟨1⟩) (c := ucell (seed : Int)) rfl
          · exact h.lookup_some (l := .base ⟨2⟩) (c := ucell 0) rfl
          · exact h.lookup_some (l := .base ⟨3⟩) (c := hIHandleCell n) rfl
          · have himg := h.lookup_some (l := .base ⟨4⟩) (c := arrCell n l) rfl
            rw [renCell_arr] at himg
            show Heap.lookup σA.heap (.base ⟨ρ21 (d + 4) 4⟩)
              = some (renameCell (ρ21 (d + 4)) (arrCell n l))
            rw [renCell_arr]
            exact himg
          · exact h.lookup_some (l := .base ⟨5⟩) (c := hIHandleCell n) rfl
          · exact h.lookup_some (l := .base ⟨6⟩)
              (c := ucell ((n : Nat) : Int)) rfl
          · exact h.lookup_some (l := .base ⟨7⟩) (c := bcell false) rfl
          · exact h.lookup_some (l := .base ⟨8⟩) (c := hIHandleCell n) rfl
          · exact h.lookup_some (l := .base ⟨9⟩) (c := intcell ivF) rfl
          · exact h.lookup_some (l := .base ⟨10⟩) (c := bcell false) rfl
          · exact h.lookup_some (l := .base ⟨11⟩) (c := ucell 1) rfl
          · exact h.lookup_some (l := .base ⟨12⟩) (c := ucell sciv) rfl
          · exact h.lookup_some (l := .base ⟨13⟩) (c := bcell false) rfl
          · exact h.lookup_some (l := .base ⟨14⟩) (c := hTHandleCell n) rfl
          · have himg := h.lookup_some (l := .base ⟨15⟩)
              (c := arrCell n tl) rfl
            rw [renCell_arr] at himg
            show Heap.lookup σA.heap (.base ⟨ρ21 (d + 4) 15⟩)
              = some (renameCell (ρ21 (d + 4)) (arrCell n tl))
            rw [renCell_arr]
            exact himg
          · exact h.lookup_some (l := .base ⟨16⟩) (c := hTHandleCell n) rfl
          · exact h.lookup_some (l := .base ⟨17⟩)
              (c := ucell ((n : Nat) : Int)) rfl
          · exact h.lookup_some (l := .base ⟨18⟩) (c := bcell false) rfl
          · exact h.lookup_some (l := .base ⟨19⟩) (c := ucell civ) rfl
          · exact h.lookup_some (l := .base ⟨20⟩) (c := bcell false) rfl
        · have himg := fs_lookup_none11 h (l := .base ⟨a + 4⟩)
            (lookup_σCntIn_ge (by omega))
          have hren1 : renameLoc (ρ21 d) (.base ⟨a + 4⟩)
              = .base ⟨a + 4 + d⟩ := by
            simp [renameLoc, ρ21_ge (d := d) (a := a + 4) (by omega)]
          rw [hren1] at himg
          have hren2 : renameLoc (ρ21 (d + 4)) (.base ⟨a⟩)
              = .base ⟨a + (d + 4)⟩ := by
            simp [renameLoc, ρ21_ge (d := d + 4) (a := a) (by omega)]
          rw [hren2, lookup_σCntOut_ge (by omega)]
          show Heap.lookup σA.heap (.base ⟨a + (d + 4)⟩)
            = Heap.lookup (fr ++ [(.base ⟨21 + d⟩, ucell csv),
                (.base ⟨22 + d⟩, ucell ctv), (.base ⟨23 + d⟩, ucell jv),
                (.base ⟨24 + d⟩, bcell false)]) (.base ⟨a + (d + 4)⟩)
          rw [show a + (d + 4) = a + 4 + d from by omega, himg,
            lookup_append]
          cases hfr : Heap.lookup fr (.base ⟨a + 4 + d⟩) with
          | some c => rfl
          | none =>
              show (none : Option HeapCell)
                = Heap.lookup [(.base ⟨21 + d⟩, ucell csv),
                    (.base ⟨22 + d⟩, ucell ctv), (.base ⟨23 + d⟩, ucell jv),
                    (.base ⟨24 + d⟩, bcell false)] (.base ⟨a + 4 + d⟩)
              simp [Heap.lookup,
                beq_false_of_ne (base_ne (show 21 + d ≠ a + 4 + d by omega)),
                beq_false_of_ne (base_ne (show 22 + d ≠ a + 4 + d by omega)),
                beq_false_of_ne (base_ne (show 23 + d ≠ a + 4 + d by omega)),
                beq_false_of_ne (base_ne (show 24 + d ≠ a + 4 + d by omega))]
    | .field b tid f =>
        have himg := fs_lookup_none11 h (l := bump4C (.field b tid f))
          (lookup_σCntIn_field n seed ivF sciv l tl civ csv ctv jv false
            (bump4C b) tid f)
        rw [← renameLoc_bump4C] at himg
        show Heap.lookup σA.heap (renameLoc (ρ21 (d + 4)) (.field b tid f))
          = Heap.lookup (fr ++ [(.base ⟨21 + d⟩, ucell csv),
              (.base ⟨22 + d⟩, ucell ctv), (.base ⟨23 + d⟩, ucell jv),
              (.base ⟨24 + d⟩, bcell false)])
            (renameLoc (ρ21 (d + 4)) (.field b tid f))
        rw [himg, lookup_append]
        cases hfr : Heap.lookup fr
            (renameLoc (ρ21 (d + 4)) (.field b tid f)) with
        | some c => rfl
        | none => rfl
    | .index b i =>
        have himg := fs_lookup_none11 h (l := bump4C (.index b i))
          (lookup_σCntIn_index n seed ivF sciv l tl civ csv ctv jv false
            (bump4C b) i)
        rw [← renameLoc_bump4C] at himg
        show Heap.lookup σA.heap (renameLoc (ρ21 (d + 4)) (.index b i))
          = Heap.lookup (fr ++ [(.base ⟨21 + d⟩, ucell csv),
              (.base ⟨22 + d⟩, ucell ctv), (.base ⟨23 + d⟩, ucell jv),
              (.base ⟨24 + d⟩, bcell false)])
            (renameLoc (ρ21 (d + 4)) (.index b i))
        rw [himg, lookup_append]
        cases hfr : Heap.lookup fr
            (renameLoc (ρ21 (d + 4)) (.index b i)) with
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
        have hc' : Heap.lookup [(.base ⟨21 + d⟩, ucell csv),
            (.base ⟨22 + d⟩, ucell ctv), (.base ⟨23 + d⟩, ucell jv),
            (.base ⟨24 + d⟩, bcell false)] loc = some c := hc
        by_cases h1 : (.base ⟨21 + d⟩ : Loc) = loc
        · subst h1
          have hcell : c = ucell csv := by
            simp [Heap.lookup] at hc'
            exact hc'.symm
          subst hcell
          exact h.lookup_some (l := .base ⟨21⟩) (c := ucell csv) rfl
        · by_cases h2 : (.base ⟨22 + d⟩ : Loc) = loc
          · subst h2
            have hcell : c = ucell ctv := by
              simp [Heap.lookup, beq_false_of_ne h1] at hc'
              exact hc'.symm
            subst hcell
            exact h.lookup_some (l := .base ⟨22⟩) (c := ucell ctv) rfl
          · by_cases h3 : (.base ⟨23 + d⟩ : Loc) = loc
            · subst h3
              have hcell : c = ucell jv := by
                simp [Heap.lookup, beq_false_of_ne h1,
                  beq_false_of_ne h2] at hc'
                exact hc'.symm
              subst hcell
              exact h.lookup_some (l := .base ⟨23⟩) (c := ucell jv) rfl
            · by_cases h4 : (.base ⟨24 + d⟩ : Loc) = loc
              · subst h4
                have hcell : c = bcell false := by
                  simp [Heap.lookup, beq_false_of_ne h1, beq_false_of_ne h2,
                    beq_false_of_ne h3] at hc'
                  exact hc'.symm
                subst hcell
                exact h.lookup_some (l := .base ⟨24⟩) (c := bcell false) rfl
              · exfalso
                simp [Heap.lookup, beq_false_of_ne h1, beq_false_of_ne h2,
                  beq_false_of_ne h3, beq_false_of_ne h4] at hc'
  · intro a
    rw [lookup_append]
    by_cases ha : a < 21
    · rw [ρ21_lt ha]
      have h2 := h.fr_avoid a
      rw [ρ21_lt ha] at h2
      rw [h2]
      show Heap.lookup [(.base ⟨21 + d⟩, ucell csv),
          (.base ⟨22 + d⟩, ucell ctv), (.base ⟨23 + d⟩, ucell jv),
          (.base ⟨24 + d⟩, bcell false)] (.base ⟨a⟩) = none
      simp [Heap.lookup,
        beq_false_of_ne (base_ne (show 21 + d ≠ a by omega)),
        beq_false_of_ne (base_ne (show 22 + d ≠ a by omega)),
        beq_false_of_ne (base_ne (show 23 + d ≠ a by omega)),
        beq_false_of_ne (base_ne (show 24 + d ≠ a by omega))]
    · rw [ρ21_ge (d := d + 4) (a := a) (by omega)]
      have h2 := h.fr_avoid (a + 4)
      rw [ρ21_ge (d := d) (a := a + 4) (by omega)] at h2
      rw [show a + (d + 4) = a + 4 + d from by omega, h2]
      show Heap.lookup [(.base ⟨21 + d⟩, ucell csv),
          (.base ⟨22 + d⟩, ucell ctv), (.base ⟨23 + d⟩, ucell jv),
          (.base ⟨24 + d⟩, bcell false)] (.base ⟨a + 4 + d⟩) = none
      simp [Heap.lookup,
        beq_false_of_ne (base_ne (show 21 + d ≠ a + 4 + d by omega)),
        beq_false_of_ne (base_ne (show 22 + d ≠ a + 4 + d by omega)),
        beq_false_of_ne (base_ne (show 23 + d ≠ a + 4 + d by omega)),
        beq_false_of_ne (base_ne (show 24 + d ≠ a + 4 + d by omega))]

private theorem renCfg_cntcmp (d : Nat) (b : Bool) :
    renameConfig (ρ21 d) (.retV (.bool b) cntCmpK)
      = .retV (.bool b) cntCmpK := by
  with_unfolding_all rfl

private theorem renCfg_stop21 (d : Nat) :
    renameConfig (ρ21 d) (.next .stop) = .next .stop := rfl

private theorem transfer_seg21 {d : Nat} {fr : Heap} {σC σC' σA : ExecState}
    {c c' : Config} {k : Nat} {ch : Choices}
    (hFS : FrameSim (ρ21 d) 21 (21 + d) fr σC σA)
    (hrun : stepFnIter k σC c ch = .ok (c', σC', ch))
    (hc : renameConfig (ρ21 d) c = c) (hc' : renameConfig (ρ21 d) c' = c') :
    ∃ σA', stepFnIter k σA c ch = .ok (c', σA', ch)
      ∧ FrameSim (ρ21 d) 21 (21 + d) fr σC' σA' := by
  have hsim := stepFnIter_sim k hFS c ch
  rw [hc] at hsim
  obtain ⟨rF, hrunF, htrip⟩ := hsim.ok_inv hrun
  obtain ⟨cF, σF, chF⟩ := rF
  obtain ⟨h1, h2, h3⟩ := htrip
  dsimp only at h1 h2 h3
  rw [h1, hc'] at hrunF
  rw [h3] at hrunF
  exact ⟨σF, hrunF, h2⟩

/-- **The count outer loop over the (count-)garbage-laden run**: from
the outer test delivery after `p` passes, the run reaches the DRIVER
TERMINAL with the verdict 1 in the result cell. -/
theorem hcnt_outer_loop (n seed : Nat) (h63 : n < 2 ^ 63)
    (ivF sciv : Int) (l tl : List Int) (hll : l.length = n)
    (htl : tl.length = n)
    (hcount : ∀ v, cntSpec v l = cntSpec v tl) :
    ∀ μ p (σA : ExecState) (fr : Heap), μ = n - p → p ≤ n →
    FrameSim (ρ21 (4 * p)) 21 (21 + 4 * p) fr
      (σCntOut n seed ivF sciv l tl ((p : Nat) : Int) false) σA →
    ∀ ch : Choices, ∃ (k : Nat) (σf : ExecState),
      k ≤ (110 * n + 220) * μ + 21 ∧
      stepFnIter k σA
        (.retV (.bool (decide (((p : Nat) : Int) < ((n : Nat) : Int))))
          cntCmpK) ch
        = .ok (.next .stop, σf, ch)
      ∧ Heap.lookup σf.heap (.base ⟨2⟩) = some (ucell 1) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro p σA fr hμ hpn hFS ch
    subst hμ
    rcases Nat.lt_or_ge p n with hlt | hge
    · rw [show (decide (((p : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      obtain ⟨K, hK, hpass⟩ := hcnt_pass_seg n seed h63 ivF sciv l tl hll htl
        hcount p hlt ch
      obtain ⟨σA', hrunA, hFS'⟩ := transfer_seg21 hFS hpass
        (renCfg_cntcmp (4 * p) true) (renCfg_cntcmp (4 * p) _)
      have hFS2 := rebaseSim21 hFS'
      obtain ⟨k, σf, hk, hrun, hread⟩ := ih (n - (p + 1)) (by omega) (p + 1)
        σA'
        (fr ++ [(.base ⟨21 + 4 * p⟩,
            ucell ((cntSpec (tl.getD p 0) l : Nat) : Int)),
          (.base ⟨22 + 4 * p⟩,
            ucell ((cntSpec (tl.getD p 0) tl : Nat) : Int)),
          (.base ⟨23 + 4 * p⟩, ucell ((n : Nat) : Int)),
          (.base ⟨24 + 4 * p⟩, bcell false)]) rfl (by omega)
        (by
          have : 4 * p + 4 = 4 * (p + 1) := by omega
          rw [← this]
          exact hFS2) ch
      refine ⟨K + k, σf, ?_, stepFnIter_chain hrunA hrun, hread⟩
      have hmul : (110 * n + 220) * (n - (p + 1)) + (110 * n + 220)
          = (110 * n + 220) * (n - p) := by
        rw [← Nat.mul_succ]
        congr 1
        omega
      omega
    · have hEq : p = n := by omega
      subst hEq
      rw [show (decide (((p : Nat) : Int) < ((p : Nat) : Int))) = false from
        decide_eq_false (by omega)]
      have hX := hcnt_exit_raw p seed ivF sciv l tl ((p : Nat) : Int) [] 21 ch
      obtain ⟨σf, hrunA, hFS'⟩ := transfer_seg21 hFS hX
        (renCfg_cntcmp (4 * p) false) (renCfg_stop21 (4 * p))
      refine ⟨21, σf, by omega, hrunA, ?_⟩
      have hread := hFS'.lookup_some (l := .base ⟨2⟩) (c := ucell 1) rfl
      have hren : renameLoc (ρ21 (4 * p)) (.base ⟨2⟩) = .base ⟨2⟩ := by
        simp [renameLoc, ρ21]
      rw [hren] at hread
      exact hread


end GoLean.Examples.InsertionSort
