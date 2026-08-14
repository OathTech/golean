import GoLeanProofs.Examples.MinMax
import GoLeanProofs.Examples.Targets

/-!
# MinMax — the S3 RELATIONAL harness (`minmax_harness_r`)

Examples phase-2, slice 1 (2026-08-14; slice record
`docs/2026-08-14_phase2-slice1-spec-swaps.md`, scoping study
`docs/2026-08-14_harness-style-scoping.md` §4.4). The user-facing
headline `minmax_ok` now states the RELATIONAL harness: the Go returns
the PRE-STATE alongside the subject's `(lo, hi)`, so the Lean
postcondition relates the RETURNED DATA directly — `lo = minSpec pre`
and `hi = maxSpec pre` — with no family function re-describing the
setup inside the claim. `mmFamily` leaves the statement (it survives
only as the existential's witness, in the proof).

The previous headline over `minmax_harness` — the returned PAIR
compared against `minSpec/maxSpec (mmFamily n seed)`, i.e. with the
family IN the statement — is KEPT in `Examples/MinMax.lean` as
`minmax_ok_v1` / `minmax_readout_v1`, with its corpus rows.

## The bounded cap is the honest cost of this style

Go's pass-by-value fragment cannot return unbounded data, so the
harness returns a FIXED-CAP `[8]uint64` and the theorem carries
`hn : n ≤ 8` as a hypothesis. That is a toy bound and it is stated
plainly rather than hidden: the harness's own domain is `n ≤ 8`, the
cap is visible in the Go as `const minmaxCapN = 8`, and the copy loop
plus zero-padding exist only so the pre-state can cross the
observation boundary. `∃ pre` is also still family-DETERMINED — the
statement merely avoids saying so; the ghost rung-1 annotation that
would make it genuine ∀-data is designed, not built.

## Cost shape and genericity

Same discipline as `Examples/Reverse/HarnessV.lean`: every raw segment
is PROGRAM-generic (`rSt σ H na` — abstract `σ`, only heap/nextAddr
pinned), and the one step that consults the program (the `minMax(s)`
frame entry) is conditioned through `StepKit.stepFn_call_enter`. The
pinned program is unfolded exactly twice: the lowering pin and that one
`enterFrame` discharge. Placement (address) genericity is not taken,
for the reason recorded in the reverse module and the slice record.

Address layout (probe-measured; `nextAddr = 22`):
0 = `n`, 1 = `seed`, 2 = `$res0` (`[8]uint64`), 3 = `$res1`,
4 = `$res2`, 5 = `$c15` (handle), 6 = backing, 7 = `s`,
8 = setup `i`, 9 = setup flag, 10 = `pre`, 11 = copy `i`,
12 = copy flag, 13 = the harness's `lo`, 14 = its `hi`,
15 = minMax's `s`, 16/17 = minMax's `$res0`/`$res1`,
18/19 = minMax's `lo`/`hi`, 20 = minMax's `i`, 21 = its flag.
-/

namespace GoLean.Examples.MinMax

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-- The PROGRAM-generic state form (the reverse module's `vSt`). -/
abbrev rSt (σ : ExecState) (H : Heap) (na : Nat) : ExecState :=
  { σ with heap := H, nextAddr := na }

/-! ## The S3 statement adapter

`goArr8` is STATEMENT vocabulary: it is what "the returned
`[minmaxCapN]uint64`" means as a `GoValue`. Under the §11 closure rules
it is never a proof-kit definition — it belongs to the example. It was
introduced in this module until the 2026-08-14 designation moved it,
unchanged, to the def-only `Examples/Targets.lean`, which is what the
Comparator Challenge's trusted closure can import; the rule it obeys is
the same one, now enforced by a gate instead of by convention. -/

-- HOISTED to `GoLeanProofs/Examples/Targets.lean` (designation, 2026-08-14):
-- `goArr8` is statement vocabulary of a DESIGNATED gallery headline, so it must
-- live in a def-only module inside the Comparator Challenge's trusted import
-- closure. The definition is unchanged and still visible here via the import.

/-! ## Extra pure facts -/

/-- The family is prefix-closed: taking `m` of the length-`N` family is
the length-`m` family. -/
theorem mmFamily_take {N seed m : Nat} (h : m ≤ N) :
    (mmFamily N seed).take m = mmFamily m seed := by
  simp only [mmFamily, ← List.map_take, List.take_range,
    Nat.min_eq_left h]

/-- The pre-copy's invariant list IS the setup loop's, at cap 8. -/
theorem preList_full {n seed : Nat} (h : n ≤ 8) :
    setupList 8 seed n
      = (mmFamily n seed) ++ List.replicate (8 - (mmFamily n seed).length) 0 := by
  rw [setupList, mmFamily_take h, mmFamily_length]

/-! ## Cells and handles at the r-layout -/

abbrev ru64 (v : Int) : HeapCell := ⟨some (.int .uint64), .int v .uint64⟩
abbrev rint (v : Int) : HeapCell := ⟨some (.int .int), .int v .int⟩
abbrev rbool (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
abbrev rSliceS (n : Nat) : GoValue := .slice ⟨some (.base ⟨6⟩), 0, n, n⟩
abbrev rHandle (n : Nat) : HeapCell :=
  ⟨some (.slice (.int .uint64)), rSliceS n⟩
abbrev rBack (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n (.int .uint64)), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev rArr8 (l : List Int) : HeapCell :=
  ⟨some (.array 8 (.int .uint64)), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev rNilSlice : HeapCell :=
  ⟨some (.slice (.int .uint64)), .slice ⟨none, 0, 0, 0⟩⟩

/-! ## The harness `Func`, verbatim from the pinned lowering -/

-- HOISTED to `GoLeanProofs/Examples/Targets.lean` (designation, 2026-08-14):
-- `mmHarnessRFunc` is statement vocabulary of a DESIGNATED gallery headline, so it must
-- live in a def-only module inside the Comparator Challenge's trusted import
-- closure. The definition is unchanged and still visible here via the import.

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem minmaxHarnessR_pin :
    findFunctionIn? minMaxLowered.funcs ⟨"minmax_harness_r"⟩
    = some mmHarnessRFunc := rfl

/-! ## The array-local element store

`pre[i] = w` on an ARRAY-typed local. LIFTED to
`SliceMem.storeTarget_arrayLocal_u64` in phase-2 slice 1 (2026-08-14)
once its second consumer landed — `Examples/WordCount/HarnessR.lean`'s
`words[i] = w[i]` copy loop, whose store target is the same
ADDRESS-rooted chain. CORRECTED (audit response, 2026-08-15): the lift
did NOT generalize this lemma — it was already stated at an arbitrary
array length `N` where it stood here, and moved unchanged. The lemma
generalized by that lift is its neighbour `normalizeValueForTy_arr_u64`
(`normalizeValueForTy_arr8_u64`, cap 8 → `N`). The local name survives
as a re-export so this
module's uses are untouched; it is one of the lift's two fixture
witnesses (form note §12). -/
theorem storeTarget_arrayLocal_u64 {σ : ExecState} {a : Addr} {N i : Nat}
    {ik : IntKind} {l : List Int} {w : Int}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨some (.array N (.int .uint64)),
              .array ⟨l.map (fun v => .int v .uint64)⟩⟩)
    (hi : i < l.length) (hn : l.length = N)
    (hl : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64) (hw : 0 ≤ w ∧ w < 2 ^ 64) :
    storeTarget σ (.chain (.addr (.base a)) [.int (i : Nat) ik] [.index])
        (.int w .uint64)
      = .ok { σ with
          heap := Heap.set σ.heap (.base a)
            ⟨some (.array N (.int .uint64)),
             .array ⟨(l.set i w).map (fun v => .int v .uint64)⟩⟩ } :=
  GoLean.SliceMem.storeTarget_arrayLocal_u64 hlook hi hn hl hw

/-! ## Statement pieces, environments, continuations -/

def rS2 : Stmt :=
  .seqn #[.initialization { id := "s", typ := .slice (.int .uint64) },
          .assign (.var "s") (.var "$c15")]
def rS3 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .uint64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) mmHarnessFunc.shBody]]
def rS4 : Stmt :=
  .seqn #[.initialization { id := "pre", typ := .array 8 (.int .uint64) }]
def rS5 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .uint64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) mmHarnessRFunc.cpBody]]
def rS6 : Stmt :=
  .seqn #[.initialization { id := "lo", typ := .int .uint64 },
          .initialization { id := "hi", typ := .int .uint64 },
          .call #[.var "lo", .var "hi"] ⟨"minMax"⟩ #[.var "s"]]
def rS7 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "pre"),
          .assign (.var "$res1") (.var "lo"),
          .assign (.var "$res2") (.var "hi"),
          .returnStmt]

def baseEnvR : Scope :=
  [("$res2", .base ⟨4⟩), ("$res1", .base ⟨3⟩), ("$res0", .base ⟨2⟩),
   ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]
def envC15R : LocalEnv := [[("$c15", .base ⟨5⟩)], baseEnvR]
def sScopeR : Scope := [("s", .base ⟨7⟩), ("$c15", .base ⟨5⟩)]
def preScopeR : Scope :=
  [("pre", .base ⟨10⟩), ("s", .base ⟨7⟩), ("$c15", .base ⟨5⟩)]
def callScopeR : Scope :=
  [("hi", .base ⟨14⟩), ("lo", .base ⟨13⟩), ("pre", .base ⟨10⟩),
   ("s", .base ⟨7⟩), ("$c15", .base ⟨5⟩)]
def callEnvR : LocalEnv := [callScopeR, baseEnvR]

def suEnvR : LocalEnv :=
  [[("$forFirst", .base ⟨9⟩)], [("i", .base ⟨8⟩)], sScopeR, baseEnvR]
def suEnvR2 : LocalEnv := [] :: [] :: suEnvR
def cpEnvR : LocalEnv :=
  [[("$forFirst", .base ⟨12⟩)], [("i", .base ⟨11⟩)], preScopeR, baseEnvR]
def cpEnvR2 : LocalEnv := [] :: [] :: cpEnvR

def rTailAfterSetup : Cont :=
  .seq [rS4, rS5, rS6, rS7] [sScopeR, baseEnvR] (.frame [] [] [] [] .stop)
def suHeadTailR : Cont :=
  .seq [] suEnvR
    (.seq [] [[("i", .base ⟨8⟩)], sScopeR, baseEnvR] rTailAfterSetup)
def suHeadCfgR : Config :=
  .exec (.while (.boolLit true) mmHarnessFunc.shBody) suEnvR suHeadTailR
def suLoopKR : Cont :=
  .loop (.boolLit true) mmHarnessFunc.shBody suEnvR suHeadTailR
def suStoreBlockR : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
        (.add (.var "seed") (.var "i"))]]
def suCmpKR : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: suEnvR)
    (.seq [suStoreBlockR] ([] :: suEnvR) suLoopKR)
def suRefR (n : Nat) (iv : Int) : TargetRef :=
  .chain (rSliceS n) [.int iv .uint64] [.index]
def suStTailR : Cont :=
  .seq [] suEnvR2 (.seq [] ([] :: suEnvR) suLoopKR)

def rTailAfterCopy : Cont :=
  .seq [rS6, rS7] [preScopeR, baseEnvR] (.frame [] [] [] [] .stop)
def cpHeadTailR : Cont :=
  .seq [] cpEnvR
    (.seq [] [[("i", .base ⟨11⟩)], preScopeR, baseEnvR] rTailAfterCopy)
def cpHeadCfgR : Config :=
  .exec (.while (.boolLit true) mmHarnessRFunc.cpBody) cpEnvR cpHeadTailR
def cpLoopKR : Cont :=
  .loop (.boolLit true) mmHarnessRFunc.cpBody cpEnvR cpHeadTailR
def cpStoreBlockR : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.ref "pre") (.var "i")))
        (.indexGet (.var "s") (.var "i"))]]
def cpCmpKR : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: cpEnvR)
    (.seq [cpStoreBlockR] ([] :: cpEnvR) cpLoopKR)
def cpRefR (iv : Int) : TargetRef :=
  .chain (.addr (.base ⟨10⟩)) [.int iv .uint64] [.index]
def cpStTailR : Cont :=
  .seq [] cpEnvR2 (.seq [] ([] :: cpEnvR) cpLoopKR)
def cpRhsKR (iv : Int) : Cont :=
  .rhsK .vals [cpRefR iv] [] [] (.seqn #[]) cpEnvR2 cpStTailR

/-! ### The minMax frame at the r-layout -/

def mEnvBR : LocalEnv :=
  [[("hi", .base ⟨19⟩), ("lo", .base ⟨18⟩)],
   [("$res1", .base ⟨17⟩), ("$res0", .base ⟨16⟩), ("s", .base ⟨15⟩)]]
def mEnvIR : LocalEnv := [("i", .base ⟨20⟩)] :: mEnvBR
def mEnvInR : LocalEnv := [("$forFirst", .base ⟨21⟩)] :: mEnvIR
def mEnvCR : LocalEnv := [] :: mEnvInR
def mEnvB2R : LocalEnv := [] :: mEnvCR
def mEnvB3R : LocalEnv := [] :: mEnvB2R

def mShapesR : List (TargetShape × List Expr) :=
  [(.chain [], [.ref "lo"]), (.chain [], [.ref "hi"])]
def rAfterCall : Cont :=
  .seq [rS7] callEnvR (.frame [] [] [] [] .stop)
def mFrameKR : Cont :=
  .frame mShapesR callEnvR [.base ⟨16⟩, .base ⟨17⟩] [] rAfterCall false
def rCallArgsKR : Cont :=
  .callArgsK ⟨"minMax"⟩ mShapesR [] [] callEnvR rAfterCall
def mEntryTailR : Cont := .seq [mmIffBlock, mmTailSeqn] mEnvBR mFrameKR
def mtref18 : TargetRef := .chain (.addr (.base ⟨18⟩)) [] []
def mtref19 : TargetRef := .chain (.addr (.base ⟨19⟩)) [] []
def mRhs1KR : Cont :=
  .rhsK .vals [mtref18, mtref19] []
    [.indexGet (.var "s") (.intLit 0 .int)] (.seqn #[]) mEnvBR mEntryTailR
def mRhs2KR (w : Int) : Cont :=
  .rhsK .vals [mtref18, mtref19] [.int w .uint64] [] (.seqn #[]) mEnvBR
    mEntryTailR
def mHeadTailR : Cont :=
  .seq [] mEnvInR (.seq [] mEnvIR (.seq [mmTailSeqn] mEnvBR mFrameKR))
def mHeadCfgR : Config :=
  .exec (.while (.boolLit true) mmWhileBody) mEnvInR mHeadTailR
def mLoopKR : Cont := .loop (.boolLit true) mmWhileBody mEnvInR mHeadTailR
def mCmpIfKR : Cont :=
  .ifK (.seqn #[]) .breakStmt mEnvCR
    (.seq [.block #[] #[mmLoIf, mmHiIf]] mEnvCR mLoopKR)
def mLenApplyKR (iv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice (.int .uint64)))) [] [] mEnvCR
    (.strictK .lessCmp [.int iv .int] [] mEnvCR mCmpIfKR)
def mLoIfKR : Cont :=
  .ifK (.block #[]
      #[.seqn #[.assign (.var "lo") (.indexGet (.var "s") (.var "i"))]])
    (.seqn #[]) mEnvB2R (.seq [mmHiIf] mEnvB2R (.seq [] mEnvCR mLoopKR))
def mLoCmpKR : Cont := .strictK .lessCmp [] [.var "lo"] mEnvB2R mLoIfKR
def mLoStoreKR : Cont :=
  .rhsK .vals [mtref18] [] [] (.seqn #[]) mEnvB3R
    (.seq [] mEnvB3R (.seq [mmHiIf] mEnvB2R (.seq [] mEnvCR mLoopKR)))
def mHiIfKR : Cont :=
  .ifK (.block #[]
      #[.seqn #[.assign (.var "hi") (.indexGet (.var "s") (.var "i"))]])
    (.seqn #[]) mEnvB2R (.seq [] mEnvB2R (.seq [] mEnvCR mLoopKR))
def mHiCmpKR : Cont := .strictK .greaterCmp [] [.var "hi"] mEnvB2R mHiIfKR
def mHiStoreKR : Cont :=
  .rhsK .vals [mtref19] [] [] (.seqn #[]) mEnvB3R
    (.seq [] mEnvB3R (.seq [] mEnvB2R (.seq [] mEnvCR mLoopKR)))

/-! ## Heap fronts (program-generic) -/

def zeros8 : List Int := List.replicate 8 0

def rHeap0 (nv sv : Int) : Heap :=
  [(.base ⟨0⟩, ru64 nv), (.base ⟨1⟩, ru64 sv), (.base ⟨2⟩, rArr8 zeros8),
   (.base ⟨3⟩, ru64 0), (.base ⟨4⟩, ru64 0)]

def rHeapC15 (nv sv : Int) : Heap :=
  rHeap0 nv sv ++ [(.base ⟨5⟩, rNilSlice)]

def rHeapMake (nv sv : Int) (n : Nat) : Heap :=
  rHeap0 nv sv ++
    [(.base ⟨5⟩, rHandle n), (.base ⟨6⟩, rBack n (List.replicate n 0))]

def rHeapSu (nv sv : Int) (n : Nat) (l : List Int) (iv : Int) (ffv : Bool) :
    Heap :=
  rHeap0 nv sv ++
    [(.base ⟨5⟩, rHandle n), (.base ⟨6⟩, rBack n l), (.base ⟨7⟩, rHandle n),
     (.base ⟨8⟩, ru64 iv), (.base ⟨9⟩, rbool ffv)]

def rHeapCp (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (ffv : Bool) : Heap :=
  rHeapSu nv sv n l siv false ++
    [(.base ⟨10⟩, rArr8 lp), (.base ⟨11⟩, ru64 civ), (.base ⟨12⟩, rbool ffv)]

def rHeapCall (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int) :
    Heap :=
  rHeapCp nv sv n l lp siv civ false ++
    [(.base ⟨13⟩, ru64 0), (.base ⟨14⟩, ru64 0)]

def rHeapMFrame (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int) :
    Heap :=
  rHeapCall nv sv n l lp siv civ ++
    [(.base ⟨15⟩, rHandle n), (.base ⟨16⟩, ru64 0), (.base ⟨17⟩, ru64 0)]

def rHeapM1 (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int) :
    Heap :=
  rHeapMFrame nv sv n l lp siv civ ++
    [(.base ⟨18⟩, ru64 0), (.base ⟨19⟩, ru64 0)]

def rHeapM (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (lov hiv iv : Int) (ffv : Bool) : Heap :=
  rHeapMFrame nv sv n l lp siv civ ++
    [(.base ⟨18⟩, ru64 lov), (.base ⟨19⟩, ru64 hiv),
     (.base ⟨20⟩, rint iv), (.base ⟨21⟩, rbool ffv)]

/-- The state just before the `$res0 = pre` store (the one epilogue step
that cannot reduce definitionally at a symbolic array). -/
def rHeapPreStore (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (lov hiv iv : Int) : Heap :=
  rHeapSu nv sv n l siv false ++
    [(.base ⟨10⟩, rArr8 lp), (.base ⟨11⟩, ru64 civ), (.base ⟨12⟩, rbool false),
     (.base ⟨13⟩, ru64 (IntKind.normalize .uint64
        (IntKind.normalize .uint64 lov))),
     (.base ⟨14⟩, ru64 (IntKind.normalize .uint64
        (IntKind.normalize .uint64 hiv))),
     (.base ⟨15⟩, rHandle n),
     (.base ⟨16⟩, ru64 (IntKind.normalize .uint64 lov)),
     (.base ⟨17⟩, ru64 (IntKind.normalize .uint64 hiv)),
     (.base ⟨18⟩, ru64 lov), (.base ⟨19⟩, ru64 hiv),
     (.base ⟨20⟩, rint iv), (.base ⟨21⟩, rbool false)]

/-- Same, with `pre` delivered into `$res0`. -/
def rHeapStored (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (lov hiv iv : Int) : Heap :=
  [(.base ⟨0⟩, ru64 nv), (.base ⟨1⟩, ru64 sv), (.base ⟨2⟩, rArr8 lp),
   (.base ⟨3⟩, ru64 0), (.base ⟨4⟩, ru64 0),
   (.base ⟨5⟩, rHandle n), (.base ⟨6⟩, rBack n l), (.base ⟨7⟩, rHandle n),
   (.base ⟨8⟩, ru64 siv), (.base ⟨9⟩, rbool false),
   (.base ⟨10⟩, rArr8 lp), (.base ⟨11⟩, ru64 civ), (.base ⟨12⟩, rbool false),
   (.base ⟨13⟩, ru64 (IntKind.normalize .uint64
      (IntKind.normalize .uint64 lov))),
   (.base ⟨14⟩, ru64 (IntKind.normalize .uint64
      (IntKind.normalize .uint64 hiv))),
   (.base ⟨15⟩, rHandle n),
   (.base ⟨16⟩, ru64 (IntKind.normalize .uint64 lov)),
   (.base ⟨17⟩, ru64 (IntKind.normalize .uint64 hiv)),
   (.base ⟨18⟩, ru64 lov), (.base ⟨19⟩, ru64 hiv),
   (.base ⟨20⟩, rint iv), (.base ⟨21⟩, rbool false)]

/-- The terminal heap. -/
def rHeapEnd (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (lov hiv iv : Int) : Heap :=
  [(.base ⟨0⟩, ru64 nv), (.base ⟨1⟩, ru64 sv), (.base ⟨2⟩, rArr8 lp),
   (.base ⟨3⟩, ru64 (IntKind.normalize .uint64 (IntKind.normalize .uint64
      (IntKind.normalize .uint64 lov)))),
   (.base ⟨4⟩, ru64 (IntKind.normalize .uint64 (IntKind.normalize .uint64
      (IntKind.normalize .uint64 hiv)))),
   (.base ⟨5⟩, rHandle n), (.base ⟨6⟩, rBack n l), (.base ⟨7⟩, rHandle n),
   (.base ⟨8⟩, ru64 siv), (.base ⟨9⟩, rbool false),
   (.base ⟨10⟩, rArr8 lp), (.base ⟨11⟩, ru64 civ), (.base ⟨12⟩, rbool false),
   (.base ⟨13⟩, ru64 (IntKind.normalize .uint64
      (IntKind.normalize .uint64 lov))),
   (.base ⟨14⟩, ru64 (IntKind.normalize .uint64
      (IntKind.normalize .uint64 hiv))),
   (.base ⟨15⟩, rHandle n),
   (.base ⟨16⟩, ru64 (IntKind.normalize .uint64 lov)),
   (.base ⟨17⟩, ru64 (IntKind.normalize .uint64 hiv)),
   (.base ⟨18⟩, ru64 lov), (.base ⟨19⟩, ru64 hiv),
   (.base ⟨20⟩, rint iv), (.base ⟨21⟩, rbool false)]

/-- The pinned program as an empty-heap state — with the
`derive_entry_eq` invocation below, the one place this module carries
`minMaxLowered` (moved up from the run section for the macro's sake,
G0 item 3c). -/
def rProg : ExecState :=
  { types := minMaxLowered.typeDefs.toList,
    functions := minMaxLowered.funcs,
    methods := minMaxLowered.methods,
    heap := [], nextAddr := 0 }

/- The post-prelude state (`rHSeed`), the start configuration
(`rHC0`), and the entry equation (`rH_entry_eq`, formerly hand-written
in the run section) are DERIVED — the P4 entry-equation macro in its
PROGRAM-GENERIC form (G0 item 3c): the emitted state is the record
update `{ rProg with … }`, so the headline's show-bridge to the
compositional `rSt rProg (rHeap0 …) 5` spelling is structural. -/
derive_entry_eq rH_entry_eq minMaxLowered mmHarnessRFunc rHSeed rHC0 rProg

/-! ## Heap-lookup facts -/

theorem lookup_suR (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (rSt σ (rHeapSu nv sv n l iv ffv) na).heap (.base ⟨6⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [rHeapSu, rHeap0, Heap.lookup, rBack]

theorem lookup_cpS_R (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (rSt σ (rHeapCp nv sv n l lp siv civ ffv) na).heap
        (.base ⟨6⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [rHeapCp, rHeapSu, rHeap0, Heap.lookup, rBack]

theorem lookup_cpPre_R (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (rSt σ (rHeapCp nv sv n l lp siv civ ffv) na).heap
        (.base ⟨10⟩)
      = some ⟨some (.array 8 (.int .uint64)),
          .array ⟨lp.map (fun v => .int v .uint64)⟩⟩ := by
  simp [rHeapCp, rHeapSu, rHeap0, Heap.lookup, rArr8]

theorem lookup_m1R (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (na : Nat) :
    Heap.lookup (rSt σ (rHeapM1 nv sv n l lp siv civ) na).heap (.base ⟨6⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [rHeapM1, rHeapMFrame, rHeapCall, rHeapCp, rHeapSu, rHeap0,
    Heap.lookup, rBack]

theorem lookup_mR (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ lov hiv iv : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv ffv) na).heap
        (.base ⟨6⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [rHeapM, rHeapMFrame, rHeapCall, rHeapCp, rHeapSu, rHeap0,
    Heap.lookup, rBack]

theorem lookup_preStore (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ lov hiv iv : Int) (na : Nat) :
    Heap.lookup
        (rSt σ (rHeapPreStore nv sv n l lp siv civ lov hiv iv) na).heap
        (.base ⟨2⟩)
      = some ⟨some (.array 8 (.int .uint64)),
          .array ⟨zeros8.map (fun v => .int v .uint64)⟩⟩ := by
  simp [rHeapPreStore, rHeapSu, rHeap0, Heap.lookup, rArr8]

/-- Normalizing an in-range uint64 list at an array type is the
identity (the `$res0 = pre` store's side condition). The thin cap-8
alias of `SliceMem.normalizeValueForTy_arr_u64`, lifted with the store
lemma above in phase-2 slice 1. -/
theorem normalizeValueForTy_arr8_u64 {σ : ExecState} {lp : List Int}
    (hlen : lp.length = 8) (hl : ∀ v ∈ lp, 0 ≤ v ∧ v < 2 ^ 64) :
    normalizeValueForTy σ (.array 8 (.int .uint64))
        (.array ⟨lp.map (fun v => .int v .uint64)⟩)
      = .ok (.array ⟨lp.map (fun v => .int v .uint64)⟩) :=
  GoLean.SliceMem.normalizeValueForTy_arr_u64 hlen hl

def rEpiTail : Cont :=
  .seq [.assign (.var "$res1") (.var "lo"),
        .assign (.var "$res2") (.var "hi"), .returnStmt] callEnvR
    (.frame [] [] [] [] .stop)
def rRes0Ref : TargetRef := .chain (.addr (.base ⟨2⟩)) [] []

/-! ## Raw run segments — PROGRAM-generic throughout -/

/-- Entry A: body start → the `$c15` makeSlice apply point. 10 steps. -/
theorem r_E1_raw (σ : ExecState) (nv sv : Int) (ch : Choices) :
    stepFnIter 10 (rSt σ (rHeap0 nv sv) 5) rHC0 ch
      = .ok (.retV (.int nv .uint64)
          (.stmtOpK (.makeSlice (.int .uint64) false) 1
            [.addr (.base ⟨5⟩)] [] envC15R
            (.seq [rS2, rS3, rS4, rS5, rS6, rS7] envC15R
              (.frame [] [] [] [] .stop))),
        rSt σ (rHeapC15 nv sv) 6, ch) := by
  with_unfolding_all rfl

/-- **`make([]uint64, n)` at SYMBOLIC `n`.** -/
theorem r_make_apply (σ : ExecState) (nv sv : Int) (n : Nat) (ch : Choices) :
    applyStmtOp (rSt σ (rHeapC15 nv sv) 6) ch
      (.makeSlice (.int .uint64) false) 1
      [.addr (.base ⟨5⟩), .int (n : Nat) .uint64]
      = .ok (rSt σ (rHeapMake nv sv n) 7, ch) := by
  have hnat : ∀ t : String,
      natFromNonnegativeInt t ((n : Nat) : Int) = .ok n := by
    intro t
    simp only [natFromNonnegativeInt]
    rw [if_neg (by omega : ¬ (((n : Nat) : Int) < 0))]
    rfl
  have hback := GoLean.Iris.buildDefaultArrayValue_int
    (rSt σ (rHeapC15 nv sv) 6) .uint64 n
  simp only [applyStmtOp, applyStmtOpCore, valueAsInt, Bind.bind,
    Except.bind, pure, Except.pure, hnat, hback]
  rw [if_neg (by omega : ¬ (n < n))]
  simp only [ExecState.alloc, ExecState.freshLoc, valueAsLoc, Except.bind,
    storeLoc, Heap.lookup, normalizeValueForTy, normalizeValueForTyFuel,
    typeResolutionFuel, Heap.set, pure, Except.pure, rSt, rHeapC15,
    rHeapMake, rHeap0, rBack, rHandle, rSliceS, ru64, rArr8, rNilSlice,
    List.map_replicate]
  rfl

/-- Entry B: `s := $c15`, the setup counter and flag → the setup loop
head. 42 steps. -/
theorem r_E2_raw (σ : ExecState) (nv sv : Int) (n : Nat) (ch : Choices) :
    stepFnIter 42 (rSt σ (rHeapMake nv sv n) 7)
      (.next (.seq [rS2, rS3, rS4, rS5, rS6, rS7] envC15R
        (.frame [] [] [] [] .stop))) ch
      = .ok (suHeadCfgR,
          rSt σ (rHeapSu nv sv n (List.replicate n 0) 0 true) 10, ch) := by
  with_unfolding_all rfl

/-! ### The setup loop -/

theorem su_A0_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 25 (rSt σ (rHeapSu nv sv n l iv true) 10) suHeadCfgR ch
      = .ok (.retV (.bool (decide (iv < nv))) suCmpKR,
          rSt σ (rHeapSu nv sv n l iv false) 10, ch) := by
  with_unfolding_all rfl

theorem su_A1_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 29 (rSt σ (rHeapSu nv sv n l iv false) 10) suHeadCfgR ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < nv))) suCmpKR,
          rSt σ (rHeapSu nv sv n l
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false) 10, ch) := by
  with_unfolding_all rfl

theorem su_B1_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 18 (rSt σ (rHeapSu nv sv n l iv false) 10)
      (.retV (.bool true) suCmpKR) ch
      = .ok (.next (.storeK [suRefR n iv]
            [.int (IntKind.normalize .uint64 (sv + iv)) .uint64]
            (.seqn #[]) suEnvR2 suStTailR),
          rSt σ (rHeapSu nv sv n l iv false) 10, ch) := by
  with_unfolding_all rfl

theorem su_D_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 5 (rSt σ (rHeapSu nv sv n l iv false) 10)
      (.next (.storeK [] [] (.seqn #[]) suEnvR2 suStTailR)) ch
      = .ok (suHeadCfgR, rSt σ (rHeapSu nv sv n l iv false) 10, ch) := by
  with_unfolding_all rfl

/-- Setup exit: test false → `var pre` declared (an `.initialization`,
NOT a `makeSlice`) and the copy loop head. 39 steps. -/
theorem su_X_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 39 (rSt σ (rHeapSu nv sv n l iv false) 10)
      (.retV (.bool false) suCmpKR) ch
      = .ok (cpHeadCfgR,
          rSt σ (rHeapCp nv sv n l zeros8 iv 0 true) 13, ch) := by
  with_unfolding_all rfl

/-! ### The copy loop -/

theorem cp_A0_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 25 (rSt σ (rHeapCp nv sv n l lp siv civ true) 13) cpHeadCfgR ch
      = .ok (.retV (.bool (decide (civ < nv))) cpCmpKR,
          rSt σ (rHeapCp nv sv n l lp siv civ false) 13, ch) := by
  with_unfolding_all rfl

theorem cp_A1_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 29 (rSt σ (rHeapCp nv sv n l lp siv civ false) 13) cpHeadCfgR
      ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1))
              < nv))) cpCmpKR,
          rSt σ (rHeapCp nv sv n l lp siv
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1)))
            false) 13, ch) := by
  with_unfolding_all rfl

/-- Copy phase 1: test true → the `pre[i]` target banked, the `s[i]`
read at its apply point. 16 steps. -/
theorem cp_B1_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 16 (rSt σ (rHeapCp nv sv n l lp siv civ false) 13)
      (.retV (.bool true) cpCmpKR) ch
      = .ok (.retV (.int civ .uint64)
            (.strictK .indexGet [rSliceS n] [] cpEnvR2 (cpRhsKR civ)),
          rSt σ (rHeapCp nv sv n l lp siv civ false) 13, ch) := by
  with_unfolding_all rfl

theorem cp_B2_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1 (rSt σ (rHeapCp nv sv n l lp siv civ false) 13)
      (.retV w (cpRhsKR civ)) ch
      = .ok (.next (.storeK [cpRefR civ] [w] (.seqn #[]) cpEnvR2 cpStTailR),
          rSt σ (rHeapCp nv sv n l lp siv civ false) 13, ch) := by
  with_unfolding_all rfl

theorem cp_D_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 5 (rSt σ (rHeapCp nv sv n l lp siv civ false) 13)
      (.next (.storeK [] [] (.seqn #[]) cpEnvR2 cpStTailR)) ch
      = .ok (cpHeadCfgR, rSt σ (rHeapCp nv sv n l lp siv civ false) 13,
          ch) := by
  with_unfolding_all rfl

/-- Copy exit: test false → `lo`/`hi` declared and the `minMax(s)`
argument delivered at the drained `callArgsK`. 15 steps. -/
theorem cp_X_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 15 (rSt σ (rHeapCp nv sv n l lp siv civ false) 13)
      (.retV (.bool false) cpCmpKR) ch
      = .ok (.retV (rSliceS n) rCallArgsKR,
          rSt σ (rHeapCall nv sv n l lp siv civ) 15, ch) := by
  with_unfolding_all rfl

/-! ### The minMax phase -/

/-- minMax prologue: `lo`/`hi` declared, the first `s[0]` operand walk →
the first index-read apply point. 17 steps. -/
theorem m_pre_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 17 (rSt σ (rHeapMFrame nv sv n l lp siv civ) 18)
      (.exec minMaxFunc.body
        [[("$res1", .base ⟨17⟩), ("$res0", .base ⟨16⟩), ("s", .base ⟨15⟩)]]
        mFrameKR) ch
      = .ok (.retV (.int 0 .int)
            (.strictK .indexGet [rSliceS n] [] mEnvBR mRhs1KR),
          rSt σ (rHeapM1 nv sv n l lp siv civ) 20, ch) := by
  with_unfolding_all rfl

theorem m_entryC_rawR (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (w : Int) (ch : Choices) :
    stepFnIter 5 (rSt σ (rHeapM1 nv sv n l lp siv civ) 20)
      (.retV (.int w .uint64) mRhs1KR) ch
      = .ok (.retV (.int 0 .int)
            (.strictK .indexGet [rSliceS n] [] mEnvBR (mRhs2KR w)),
          rSt σ (rHeapM1 nv sv n l lp siv civ) 20, ch) := by
  with_unfolding_all rfl

theorem m_entryD_rawR (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (w1 w2 : Int) (ch : Choices) :
    stepFnIter 34 (rSt σ (rHeapM1 nv sv n l lp siv civ) 20)
      (.retV (.int w2 .uint64) (mRhs2KR w1)) ch
      = .ok (mHeadCfgR,
          rSt σ (rHeapM nv sv n l lp siv civ (IntKind.normalize .uint64 w1)
            (IntKind.normalize .uint64 w2) 1 true) 22, ch) := by
  with_unfolding_all rfl

theorem mh_dispA_rawR (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ lov hiv iv : Int) (ch : Choices) :
    stepFnIter 25 (rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv true) 22)
      mHeadCfgR ch
      = .ok (.retV (rSliceS n) (mLenApplyKR iv),
          rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv false) 22, ch) := by
  with_unfolding_all rfl

theorem mh_dispB_rawR (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ lov hiv iv : Int) (ch : Choices) :
    stepFnIter 29 (rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv false) 22)
      mHeadCfgR ch
      = .ok (.retV (rSliceS n)
            (mLenApplyKR
              (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
          rSt σ (rHeapM nv sv n l lp siv civ lov hiv
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            false) 22, ch) := by
  with_unfolding_all rfl

theorem mh_bodyA_rawR (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ lov hiv iv : Int) (ch : Choices) :
    stepFnIter 11 (rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv false) 22)
      (.retV (.bool true) mCmpIfKR) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [rSliceS n] [] mEnvB2R mLoCmpKR),
          rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv false) 22, ch) := by
  with_unfolding_all rfl

theorem mh_bodyB_rawR (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ lov hiv iv w : Int) (ch : Choices) :
    stepFnIter 3 (rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv false) 22)
      (.retV (.int w .uint64) mLoCmpKR) ch
      = .ok (.retV (.bool (decide (w < lov))) mLoIfKR,
          rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv false) 22, ch) := by
  with_unfolding_all rfl

theorem mh_loT_rawR (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ lov hiv iv : Int) (ch : Choices) :
    stepFnIter 12 (rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv false) 22)
      (.retV (.bool true) mLoIfKR) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [rSliceS n] [] mEnvB3R mLoStoreKR),
          rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv false) 22, ch) := by
  with_unfolding_all rfl

theorem mh_loT2_rawR (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ lov hiv iv w : Int) (ch : Choices) :
    stepFnIter 12 (rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv false) 22)
      (.retV (.int w .uint64) mLoStoreKR) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [rSliceS n] [] mEnvB2R mHiCmpKR),
          rSt σ (rHeapM nv sv n l lp siv civ (IntKind.normalize .uint64 w)
            hiv iv false) 22, ch) := by
  with_unfolding_all rfl

theorem mh_loF_rawR (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ lov hiv iv : Int) (ch : Choices) :
    stepFnIter 9 (rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv false) 22)
      (.retV (.bool false) mLoIfKR) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [rSliceS n] [] mEnvB2R mHiCmpKR),
          rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv false) 22, ch) := by
  with_unfolding_all rfl

theorem mh_hiB_rawR (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ lov hiv iv w : Int) (ch : Choices) :
    stepFnIter 3 (rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv false) 22)
      (.retV (.int w .uint64) mHiCmpKR) ch
      = .ok (.retV (.bool (decide (hiv < w))) mHiIfKR,
          rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv false) 22, ch) := by
  with_unfolding_all rfl

theorem mh_hiT_rawR (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ lov hiv iv : Int) (ch : Choices) :
    stepFnIter 12 (rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv false) 22)
      (.retV (.bool true) mHiIfKR) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [rSliceS n] [] mEnvB3R mHiStoreKR),
          rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv false) 22, ch) := by
  with_unfolding_all rfl

theorem mh_hiT2_rawR (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ lov hiv iv w : Int) (ch : Choices) :
    stepFnIter 8 (rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv false) 22)
      (.retV (.int w .uint64) mHiStoreKR) ch
      = .ok (mHeadCfgR,
          rSt σ (rHeapM nv sv n l lp siv civ lov
            (IntKind.normalize .uint64 w) iv false) 22, ch) := by
  with_unfolding_all rfl

theorem mh_hiF_rawR (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ lov hiv iv : Int) (ch : Choices) :
    stepFnIter 5 (rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv false) 22)
      (.retV (.bool false) mHiIfKR) ch
      = .ok (mHeadCfgR,
          rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv false) 22, ch) := by
  with_unfolding_all rfl

/-- minMax exit A: test false → the epilogue, the frame exit into the
harness's `lo`/`hi`, and the `$res0 = pre` store PENDING. 46 steps; the
store itself cannot reduce definitionally (the array's contents are
symbolic), which is exactly why it is split out. -/
theorem mh_exitA_rawR (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ lov hiv iv : Int) (ch : Choices) :
    stepFnIter 46 (rSt σ (rHeapM nv sv n l lp siv civ lov hiv iv false) 22)
      (.retV (.bool false) mCmpIfKR) ch
      = .ok (.next (.storeK [rRes0Ref]
            [.array ⟨lp.map (fun v => .int v .uint64)⟩] (.seqn #[])
            callEnvR rEpiTail),
          rSt σ (rHeapPreStore nv sv n l lp siv civ lov hiv iv) 22, ch) := by
  with_unfolding_all rfl

/-- minMax exit B: `$res1`/`$res2` delivered, return, barrier exit —
the driver terminal. 24 steps. -/
theorem mh_exitB_rawR (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ lov hiv iv : Int) (ch : Choices) :
    stepFnIter 24 (rSt σ (rHeapStored nv sv n l lp siv civ lov hiv iv) 22)
      (.next (.storeK [] [] (.seqn #[]) callEnvR rEpiTail)) ch
      = .ok (.next .stop,
          rSt σ (rHeapEnd nv sv n l lp siv civ lov hiv iv) 22, ch) := by
  with_unfolding_all rfl

/-! ## The setup loop, cleaned + its induction -/

theorem su_iterR (σ : ExecState) (n seed : Nat) (m : Nat) (hn : n < 2 ^ 63)
    (hm : m < n) (ch : Choices) :
    stepFnIter 53
      (rSt σ (rHeapSu (n : Int) (seed : Int) n (setupList n seed m)
        ((m : Nat) : Int) false) 10)
      (.retV (.bool true) suCmpKR) ch
      = .ok (.retV (.bool (decide (((m + 1 : Nat) : Int) < (n : Int))))
            suCmpKR,
          rSt σ (rHeapSu (n : Int) (seed : Int) n (setupList n seed (m + 1))
            ((m + 1 : Nat) : Int) false) 10, ch) := by
  have hB := su_B1_rawR σ (n : Int) (seed : Int) n (setupList n seed m)
    ((m : Nat) : Int) ch
  rw [show IntKind.normalize .uint64 ((seed : Int) + ((m : Nat) : Int))
      = (((seed + m) % 2 ^ 64 : Nat) : Int) from by
    rw [show ((seed : Int) + ((m : Nat) : Int))
        = (((seed + m : Nat)) : Int) from by omega]
    exact unorm_nat_wrap _] at hB
  have hw : (0 : Int) ≤ (((seed + m) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + m) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    constructor
    · omega
    · exact_mod_cast Nat.mod_lt _ (by omega)
  have hst := storeTarget_slice_u64 (a := ⟨6⟩) (off := 0) (len := n)
    (cap := n) (i := m) (n := n) (ik := .uint64) (l := setupList n seed m)
    (w := (((seed + m) % 2 ^ 64 : Nat) : Int))
    (lookup_suR σ (n : Int) (seed : Int) n (setupList n seed m)
      ((m : Nat) : Int) false 10)
    (Nat.le_refl _) hm (by rw [setupList_length (by omega)]; omega)
    (setupList_length (by omega)) (setupList_range n seed m) hw
  rw [Nat.zero_add, setupList_set hm] at hst
  have hstore : storeTarget
      (rSt σ (rHeapSu (n : Int) (seed : Int) n (setupList n seed m)
        ((m : Nat) : Int) false) 10)
      (suRefR n ((m : Nat) : Int))
      (.int (((seed + m) % 2 ^ 64 : Nat) : Int) .uint64)
      = .ok (rSt σ (rHeapSu (n : Int) (seed : Int) n
          (setupList n seed (m + 1)) ((m : Nat) : Int) false) 10) := hst
  have hD := su_D_rawR σ (n : Int) (seed : Int) n (setupList n seed (m + 1))
    ((m : Nat) : Int) ch
  have hA1 := su_A1_rawR σ (n : Int) (seed : Int) n (setupList n seed (m + 1))
    ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hB
    (stepFnIter_one (stepFn_store_step hstore))) hD) hA1

theorem su_loopR (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 63) :
    ∀ μ m : Nat, m + μ = n → ∀ ch : Choices,
    ∃ k : Nat, k ≤ 53 * μ + 39 ∧
      stepFnIter k
        (rSt σ (rHeapSu (n : Int) (seed : Int) n (setupList n seed m)
          ((m : Nat) : Int) false) 10)
        (.retV (.bool (decide (((m : Nat) : Int) < (n : Int)))) suCmpKR) ch
        = .ok (cpHeadCfgR,
            rSt σ (rHeapCp (n : Int) (seed : Int) n (mmFamily n seed) zeros8
              ((n : Nat) : Int) 0 true) 13, ch) := by
  -- The P5 iterate-then-exit schema (`stepFnIter_iterate_exit`) at
  -- `su_iterR` + the exit segment; the `strongRecOn` boilerplate
  -- deleted (G0 item 3a P6 rollback). Statement unchanged.
  intro μ m hm ch
  have hexit : ∀ ch' : Choices, stepFnIter 39
      (rSt σ (rHeapSu (n : Int) (seed : Int) n (setupList n seed n)
        ((n : Nat) : Int) false) 10)
      (.retV (.bool (decide (((n : Nat) : Int) < (n : Int)))) suCmpKR) ch'
      = .ok (cpHeadCfgR,
          rSt σ (rHeapCp (n : Int) (seed : Int) n (mmFamily n seed) zeros8
            ((n : Nat) : Int) 0 true) 13, ch') := by
    intro ch'
    rw [show (decide (((n : Nat) : Int) < (n : Int))) = false from
      decide_eq_false (by omega)]
    have hX := su_X_rawR σ (n : Int) (seed : Int) n (setupList n seed n)
      ((n : Nat) : Int) ch'
    rw [← setupList_full (n := n) (seed := seed)]
    exact hX
  refine ⟨53 * (n - m) + 39, by omega, ?_⟩
  exact stepFnIter_iterate_exit (c := 53) (e := 39) (n := n)
    (T := fun j => rSt σ (rHeapSu (n : Int) (seed : Int) n
      (setupList n seed j) ((j : Nat) : Int) false) 10)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int) < (n : Int))))
      suCmpKR)
    (fun j hj ch'' => by
      rw [show (decide (((j : Nat) : Int) < (n : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact su_iterR σ n seed j hn hj ch'')
    hexit m (by omega) ch

/-! ## The copy loop, cleaned + its induction

The pre-copy's invariant is the SETUP loop's at cap 8 — `pre[i] = s[i]`
copies exactly the family value the setup loop wrote, so `setupList`
and `setupList_set` serve both and no new pure layer is needed. -/

theorem cp_iterR (σ : ExecState) (n seed : Nat) (siv : Int) (m : Nat)
    (hn : n < 2 ^ 63) (hcap : n ≤ 8) (hm : m < n) (ch : Choices) :
    stepFnIter 53
      (rSt σ (rHeapCp (n : Int) (seed : Int) n (mmFamily n seed)
        (setupList 8 seed m) siv ((m : Nat) : Int) false) 13)
      (.retV (.bool true) cpCmpKR) ch
      = .ok (.retV (.bool (decide (((m + 1 : Nat) : Int) < (n : Int))))
            cpCmpKR,
          rSt σ (rHeapCp (n : Int) (seed : Int) n (mmFamily n seed)
            (setupList 8 seed (m + 1)) siv ((m + 1 : Nat) : Int) false) 13,
          ch) := by
  have hlenF : (mmFamily n seed).length = n := mmFamily_length n seed
  have hB1 := cp_B1_rawR σ (n : Int) (seed : Int) n (mmFamily n seed)
    (setupList 8 seed m) siv ((m : Nat) : Int) ch
  have hget : (⟨(mmFamily n seed).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + m]?
      = some (.int (((seed + m) % 2 ^ 64 : Nat) : Int) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega), mmFamily_getD hm]
  have hread := stepFn_strict_apply (done := [rSliceS n]) (env := cpEnvR2)
    (k := cpRhsKR ((m : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .uint64)
      (lookup_cpS_R σ (n : Int) (seed : Int) n (mmFamily n seed)
        (setupList 8 seed m) siv ((m : Nat) : Int) false 13)
      (Nat.le_refl n) hm hget)
  have hB2 := cp_B2_rawR σ (n : Int) (seed : Int) n (mmFamily n seed)
    (setupList 8 seed m) siv ((m : Nat) : Int)
    (.int (((seed + m) % 2 ^ 64 : Nat) : Int) .uint64) ch
  have hw : (0 : Int) ≤ (((seed + m) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + m) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    constructor
    · omega
    · exact_mod_cast Nat.mod_lt _ (by omega)
  have hst := storeTarget_arrayLocal_u64 (a := ⟨10⟩) (N := 8) (i := m)
    (ik := .uint64) (l := setupList 8 seed m)
    (w := (((seed + m) % 2 ^ 64 : Nat) : Int))
    (lookup_cpPre_R σ (n : Int) (seed : Int) n (mmFamily n seed)
      (setupList 8 seed m) siv ((m : Nat) : Int) false 13)
    (by rw [setupList_length (by omega)]; omega)
    (setupList_length (by omega)) (setupList_range 8 seed m) hw
  rw [setupList_set (by omega : m < 8)] at hst
  have hstore : storeTarget
      (rSt σ (rHeapCp (n : Int) (seed : Int) n (mmFamily n seed)
        (setupList 8 seed m) siv ((m : Nat) : Int) false) 13)
      (cpRefR ((m : Nat) : Int))
      (.int (((seed + m) % 2 ^ 64 : Nat) : Int) .uint64)
      = .ok (rSt σ (rHeapCp (n : Int) (seed : Int) n (mmFamily n seed)
          (setupList 8 seed (m + 1)) siv ((m : Nat) : Int) false) 13) := hst
  have hD := cp_D_rawR σ (n : Int) (seed : Int) n (mmFamily n seed)
    (setupList 8 seed (m + 1)) siv ((m : Nat) : Int) ch
  have hA1 := cp_A1_rawR σ (n : Int) (seed : Int) n (mmFamily n seed)
    (setupList 8 seed (m + 1)) siv ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  have h1 := stepFnIter_chain hB1 (stepFnIter_one hread)
  have h2 := stepFnIter_chain h1 hB2
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hstore))
  exact stepFnIter_chain (stepFnIter_chain h3 hD) hA1

theorem cp_loopR (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 63)
    (h1 : 1 ≤ n) (hcap : n ≤ 8)
    (henter : ∀ (l lp : List Int) (siv civ : Int),
      enterFrame (rSt σ (rHeapCall (n : Int) (seed : Int) n l lp siv civ) 15)
          ⟨"minMax"⟩ [rSliceS n]
        = .ok (minMaxFunc,
            [[("$res1", .base ⟨17⟩), ("$res0", .base ⟨16⟩),
              ("s", .base ⟨15⟩)]], [.base ⟨16⟩, .base ⟨17⟩],
            rSt σ (rHeapMFrame (n : Int) (seed : Int) n l lp siv civ) 18)) :
    ∀ μ m : Nat, m + μ = n → ∀ ch : Choices,
    ∃ k : Nat, k ≤ 53 * μ + 74 ∧
      stepFnIter k
        (rSt σ (rHeapCp (n : Int) (seed : Int) n (mmFamily n seed)
          (setupList 8 seed m) ((n : Nat) : Int) ((m : Nat) : Int) false) 13)
        (.retV (.bool (decide (((m : Nat) : Int) < (n : Int)))) cpCmpKR) ch
        = .ok (mHeadCfgR,
            rSt σ (rHeapM (n : Int) (seed : Int) n (mmFamily n seed)
              (setupList 8 seed n) ((n : Nat) : Int) ((n : Nat) : Int)
              (IntKind.normalize .uint64 ((mmFamily n seed).getD 0 0))
              (IntKind.normalize .uint64 ((mmFamily n seed).getD 0 0))
              1 true) 22, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hm ch
    rcases Nat.lt_or_ge m n with hlt | hge
    · rw [show (decide (((m : Nat) : Int) < (n : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      obtain ⟨k, hk, hrun⟩ := ih (μ - 1) (by omega) (m + 1) (by omega) ch
      exact ⟨53 + k, by omega,
        stepFnIter_chain
          (cp_iterR σ n seed ((n : Nat) : Int) m hn hcap hlt ch) hrun⟩
    · have hmn : m = n := by omega
      subst hmn
      rw [show (decide (((m : Nat) : Int) < (m : Int))) = false from
        decide_eq_false (by omega)]
      have hX := cp_X_rawR σ (m : Int) (seed : Int) m (mmFamily m seed)
        (setupList 8 seed m) ((m : Nat) : Int) ((m : Nat) : Int) ch
      have hent := stepFnIter_one (ch := ch)
        (stepFn_call_enter (plans := mShapesR) (env := callEnvR)
          (k := rAfterCall) (vals := []) (v := rSliceS m)
          (henter (mmFamily m seed) (setupList 8 seed m) ((m : Nat) : Int)
            ((m : Nat) : Int)))
      have hpre := m_pre_rawR σ (m : Int) (seed : Int) m (mmFamily m seed)
        (setupList 8 seed m) ((m : Nat) : Int) ((m : Nat) : Int) ch
      have hget : (⟨(mmFamily m seed).map (fun v => .int v .uint64)⟩ :
          Array GoValue)[0 + 0]?
          = some (.int ((mmFamily m seed).getD 0 0) .uint64) := by
        rw [Nat.zero_add, getElem?_mapU _ _ (by rw [mmFamily_length]; omega)]
      have hread1 := stepFn_strict_apply (done := [rSliceS m])
        (env := mEnvBR) (k := mRhs1KR) (ch := ch)
        (applyStrictOp_indexGet_slice (ik := .int) (i := 0)
          (lookup_m1R σ (m : Int) (seed : Int) m (mmFamily m seed)
            (setupList 8 seed m) ((m : Nat) : Int) ((m : Nat) : Int) 20)
          (Nat.le_refl m) (by omega) hget)
      have hC := m_entryC_rawR σ (m : Int) (seed : Int) m (mmFamily m seed)
        (setupList 8 seed m) ((m : Nat) : Int) ((m : Nat) : Int)
        ((mmFamily m seed).getD 0 0) ch
      have hread2 := stepFn_strict_apply (done := [rSliceS m])
        (env := mEnvBR) (k := mRhs2KR ((mmFamily m seed).getD 0 0)) (ch := ch)
        (applyStrictOp_indexGet_slice (ik := .int) (i := 0)
          (lookup_m1R σ (m : Int) (seed : Int) m (mmFamily m seed)
            (setupList 8 seed m) ((m : Nat) : Int) ((m : Nat) : Int) 20)
          (Nat.le_refl m) (by omega) hget)
      have hD := m_entryD_rawR σ (m : Int) (seed : Int) m (mmFamily m seed)
        (setupList 8 seed m) ((m : Nat) : Int) ((m : Nat) : Int)
        ((mmFamily m seed).getD 0 0) ((mmFamily m seed).getD 0 0) ch
      refine ⟨15 + 1 + 17 + 1 + 5 + 1 + 34, by omega, ?_⟩
      exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hX hent) hpre)
          (stepFnIter_one hread1)) hC) (stepFnIter_one hread2)) hD

/-! ## The minMax loop, cleaned + its induction (the shipped harness's
`mh_iter`/`mh_loop`, ported to the r-layout) -/

/-- The exit-test heap after the dispatch of iteration `m`. -/
abbrev rCmpHeap (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (m : Nat) : Heap :=
  rHeapM nv sv n l lp siv civ (minSpec (l.take m)) (maxSpec (l.take m))
    ((m : Nat) : Int) false

theorem mh_iterR (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (m : Nat) (hln : l.length = n) (hxs : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64)
    (hn : n < 2 ^ 63) (siv civ : Int) (hm1 : 1 ≤ m) (hm : m < n)
    (ch : Choices) :
    ∃ k : Nat, k ≤ 96 ∧
      stepFnIter k (rSt σ (rCmpHeap nv sv n l lp siv civ m) 22)
        (.retV (.bool true) mCmpIfKR) ch
        = .ok (.retV (.bool (decide
              (((m + 1 : Nat) : Int) < ((n : Nat) : Int)))) mCmpIfKR,
            rSt σ (rCmpHeap nv sv n l lp siv civ (m + 1)) 22, ch) := by
  have hm' : m < l.length := by omega
  have hw := hxs _ (getD_mem hm')
  have hget : (⟨l.map (fun v => .int v .uint64)⟩ : Array GoValue)[0 + m]?
      = some (.int (l.getD m 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ hm']
  -- Phase 1: the first conditional, `lo` advanced.
  have phase1 : ∃ k₁ : Nat, k₁ ≤ 40 ∧
      stepFnIter k₁ (rSt σ (rCmpHeap nv sv n l lp siv civ m) 22)
        (.retV (.bool true) mCmpIfKR) ch
        = .ok (.retV (.int ((m : Nat) : Int) .int)
              (.strictK .indexGet [rSliceS n] [] mEnvB2R mHiCmpKR),
            rSt σ (rHeapM nv sv n l lp siv civ (minSpec (l.take (m + 1)))
              (maxSpec (l.take m)) ((m : Nat) : Int) false) 22, ch) := by
    have hA := mh_bodyA_rawR σ nv sv n l lp siv civ (minSpec (l.take m))
      (maxSpec (l.take m)) ((m : Nat) : Int) ch
    have hidx1 := stepFn_strict_apply (done := [rSliceS n]) (env := mEnvB2R)
      (k := mLoCmpKR) (ch := ch)
      (applyStrictOp_indexGet_slice (ik := .int)
        (lookup_mR σ nv sv n l lp siv civ (minSpec (l.take m))
          (maxSpec (l.take m)) ((m : Nat) : Int) false 22)
        (Nat.le_refl _) hm hget)
    have hB := mh_bodyB_rawR σ nv sv n l lp siv civ (minSpec (l.take m))
      (maxSpec (l.take m)) ((m : Nat) : Int) (l.getD m 0) ch
    have h15 := stepFnIter_chain
      (stepFnIter_chain hA (stepFnIter_one hidx1)) hB
    by_cases hlt : l.getD m 0 < minSpec (l.take m)
    · rw [show (decide (l.getD m 0 < minSpec (l.take m))) = true from
        decide_eq_true hlt] at h15
      have hC := mh_loT_rawR σ nv sv n l lp siv civ (minSpec (l.take m))
        (maxSpec (l.take m)) ((m : Nat) : Int) ch
      have hidx2 := stepFn_strict_apply (done := [rSliceS n]) (env := mEnvB3R)
        (k := mLoStoreKR) (ch := ch)
        (applyStrictOp_indexGet_slice (ik := .int)
          (lookup_mR σ nv sv n l lp siv civ (minSpec (l.take m))
            (maxSpec (l.take m)) ((m : Nat) : Int) false 22)
          (Nat.le_refl _) hm hget)
      have hD := mh_loT2_rawR σ nv sv n l lp siv civ (minSpec (l.take m))
        (maxSpec (l.take m)) ((m : Nat) : Int) (l.getD m 0) ch
      rw [unorm_of_range hw.1 hw.2] at hD
      refine ⟨40, Nat.le_refl _, ?_⟩
      rw [show minSpec (l.take (m + 1)) = l.getD m 0 from by
        rw [minSpec_take_succ hm1 hm']; omega]
      exact stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain h15 hC) (stepFnIter_one hidx2)) hD
    · rw [show (decide (l.getD m 0 < minSpec (l.take m))) = false from
        decide_eq_false hlt] at h15
      have hC := mh_loF_rawR σ nv sv n l lp siv civ (minSpec (l.take m))
        (maxSpec (l.take m)) ((m : Nat) : Int) ch
      refine ⟨24, by omega, ?_⟩
      rw [show minSpec (l.take (m + 1)) = minSpec (l.take m) from by
        rw [minSpec_take_succ hm1 hm']; omega]
      exact stepFnIter_chain h15 hC
  obtain ⟨k₁, hk₁, h1⟩ := phase1
  -- Phase 2: the second conditional, `hi` advanced.
  have phase2 : ∃ k₂ : Nat, k₂ ≤ 25 ∧
      stepFnIter k₂
        (rSt σ (rHeapM nv sv n l lp siv civ (minSpec (l.take (m + 1)))
          (maxSpec (l.take m)) ((m : Nat) : Int) false) 22)
        (.retV (.int ((m : Nat) : Int) .int)
          (.strictK .indexGet [rSliceS n] [] mEnvB2R mHiCmpKR)) ch
        = .ok (mHeadCfgR,
            rSt σ (rHeapM nv sv n l lp siv civ (minSpec (l.take (m + 1)))
              (maxSpec (l.take (m + 1))) ((m : Nat) : Int) false) 22,
            ch) := by
    have hidx3 := stepFn_strict_apply (done := [rSliceS n]) (env := mEnvB2R)
      (k := mHiCmpKR) (ch := ch)
      (applyStrictOp_indexGet_slice (ik := .int)
        (lookup_mR σ nv sv n l lp siv civ (minSpec (l.take (m + 1)))
          (maxSpec (l.take m)) ((m : Nat) : Int) false 22)
        (Nat.le_refl _) hm hget)
    have hB := mh_hiB_rawR σ nv sv n l lp siv civ (minSpec (l.take (m + 1)))
      (maxSpec (l.take m)) ((m : Nat) : Int) (l.getD m 0) ch
    have h4 := stepFnIter_chain (stepFnIter_one hidx3) hB
    by_cases hgt : maxSpec (l.take m) < l.getD m 0
    · rw [show (decide (maxSpec (l.take m) < l.getD m 0)) = true from
        decide_eq_true hgt] at h4
      have hC := mh_hiT_rawR σ nv sv n l lp siv civ (minSpec (l.take (m + 1)))
        (maxSpec (l.take m)) ((m : Nat) : Int) ch
      have hidx4 := stepFn_strict_apply (done := [rSliceS n]) (env := mEnvB3R)
        (k := mHiStoreKR) (ch := ch)
        (applyStrictOp_indexGet_slice (ik := .int)
          (lookup_mR σ nv sv n l lp siv civ (minSpec (l.take (m + 1)))
            (maxSpec (l.take m)) ((m : Nat) : Int) false 22)
          (Nat.le_refl _) hm hget)
      have hD := mh_hiT2_rawR σ nv sv n l lp siv civ
        (minSpec (l.take (m + 1))) (maxSpec (l.take m)) ((m : Nat) : Int)
        (l.getD m 0) ch
      rw [unorm_of_range hw.1 hw.2] at hD
      refine ⟨25, Nat.le_refl _, ?_⟩
      rw [show maxSpec (l.take (m + 1)) = l.getD m 0 from by
        rw [maxSpec_take_succ hm1 hm']; omega]
      exact stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain h4 hC) (stepFnIter_one hidx4)) hD
    · rw [show (decide (maxSpec (l.take m) < l.getD m 0)) = false from
        decide_eq_false hgt] at h4
      have hC := mh_hiF_rawR σ nv sv n l lp siv civ (minSpec (l.take (m + 1)))
        (maxSpec (l.take m)) ((m : Nat) : Int) ch
      refine ⟨9, by omega, ?_⟩
      rw [show maxSpec (l.take (m + 1)) = maxSpec (l.take m) from by
        rw [maxSpec_take_succ hm1 hm']; omega]
      exact stepFnIter_chain h4 hC
  obtain ⟨k₂, hk₂, h2⟩ := phase2
  -- Phase 3: the later-pass dispatch and the next exit test.
  have hDisp := mh_dispB_rawR σ nv sv n l lp siv civ
    (minSpec (l.take (m + 1))) (maxSpec (l.take (m + 1))) ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    inorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    inorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)]
    at hDisp
  have hlenap : applyStrictOp
      (rSt σ (rHeapM nv sv n l lp siv civ (minSpec (l.take (m + 1)))
        (maxSpec (l.take (m + 1))) ((m + 1 : Nat) : Int) false) 22)
      (.lengthOf (some (.slice (.int .uint64)))) [rSliceS n]
      = .ok (.int ((n : Nat) : Int) .int,
          rSt σ (rHeapM nv sv n l lp siv civ (minSpec (l.take (m + 1)))
            (maxSpec (l.take (m + 1))) ((m + 1 : Nat) : Int) false) 22) :=
    applyStrictOp_len_slice (Nat.le_refl _)
  have h3a := stepFnIter_chain hDisp
    (stepFnIter_one (stepFn_strict_apply (done := []) hlenap))
  have h3 := stepFnIter_chain h3a
    (stepFnIter_one (stepFn_strict_apply
      (done := [.int ((m + 1 : Nat) : Int) .int]) applyStrictOp_lessCmp_int))
  exact ⟨k₁ + (k₂ + 31), by omega,
    stepFnIter_chain h1 (stepFnIter_chain h2 h3)⟩

/-- **The minMax loop**: from the exit-test delivery of iteration `m`,
the run reaches the ENTRY TERMINAL within `96·μ + 71` steps. The
epilogue's `$res0 = pre` store is the one conditioned step (its value is
a symbolic array, so it cannot reduce definitionally). -/
theorem mh_loopR (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (hln : l.length = n) (hxs : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64)
    (hlp : lp.length = 8) (hlpr : ∀ v ∈ lp, 0 ≤ v ∧ v < 2 ^ 64)
    (hn : n < 2 ^ 63) (siv civ : Int) :
    ∀ μ m : Nat, 1 ≤ m → m ≤ n → μ = n - m → ∀ ch : Choices,
      ∃ k : Nat, k ≤ 96 * μ + 71 ∧
        stepFnIter k (rSt σ (rCmpHeap nv sv n l lp siv civ m) 22)
          (.retV (.bool (decide
            (((m : Nat) : Int) < ((n : Nat) : Int)))) mCmpIfKR) ch
          = .ok (.next .stop,
              rSt σ (rHeapEnd nv sv n l lp siv civ (minSpec l) (maxSpec l)
                ((n : Nat) : Int)) 22, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hm1 hmn hμ ch
    rcases Nat.lt_or_ge m n with hlt | hge
    · rw [show (decide (((m : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      obtain ⟨k₀, hk₀, hstep⟩ :=
        mh_iterR σ nv sv n l lp m hln hxs hn siv civ hm1 hlt ch
      obtain ⟨k, hk, hrun⟩ := ih (n - (m + 1)) (by omega) (m + 1)
        (by omega) (by omega) rfl ch
      exact ⟨k₀ + k, by omega, stepFnIter_chain hstep hrun⟩
    · have hmn' : m = n := by omega
      subst hmn'
      rw [show (decide (((m : Nat) : Int) < ((m : Nat) : Int))) = false from
        decide_eq_false (by omega)]
      have htake : l.take m = l := by
        rw [List.take_of_length_le (by omega)]
      simp only [rCmpHeap, htake]
      have hA := mh_exitA_rawR σ nv sv m l lp siv civ (minSpec l) (maxSpec l)
        ((m : Nat) : Int) ch
      have hstore : storeTarget
          (rSt σ (rHeapPreStore nv sv m l lp siv civ (minSpec l) (maxSpec l)
            ((m : Nat) : Int)) 22)
          rRes0Ref (.array ⟨lp.map (fun v => .int v .uint64)⟩)
          = .ok (rSt σ (rHeapStored nv sv m l lp siv civ (minSpec l)
              (maxSpec l) ((m : Nat) : Int)) 22) :=
        storeTarget_addr
          (lookup_preStore σ nv sv m l lp siv civ (minSpec l) (maxSpec l)
            ((m : Nat) : Int) 22)
          (normalizeValueForTy_arr8_u64 hlp hlpr)
      have hB := mh_exitB_rawR σ nv sv m l lp siv civ (minSpec l) (maxSpec l)
        ((m : Nat) : Int) ch
      exact ⟨46 + 1 + 24, by omega,
        stepFnIter_chain (stepFnIter_chain hA
          (stepFnIter_one (stepFn_store_step hstore))) hB⟩

/-! ## The run, end to end -/

/-- The `enterFrame` discharge at the pinned program: the second and
last unfolding of `minMaxLowered` in this module. -/
theorem r_enterFrame_fact (n seed : Nat) (l lp : List Int) (siv civ : Int) :
    enterFrame
        (rSt rProg (rHeapCall (n : Int) (seed : Int) n l lp siv civ) 15)
        ⟨"minMax"⟩ [rSliceS n]
      = .ok (minMaxFunc,
          [[("$res1", .base ⟨17⟩), ("$res0", .base ⟨16⟩),
            ("s", .base ⟨15⟩)]], [.base ⟨16⟩, .base ⟨17⟩],
          rSt rProg (rHeapMFrame (n : Int) (seed : Int) n l lp siv civ) 18) := by
  with_unfolding_all rfl

/-- **The harness run, PROGRAM-generic**: within `202·n + 218` steps the
harness reaches the driver terminal with the pre-copy in `$res0` and
`minSpec`/`maxSpec` of the family in `$res1`/`$res2`. -/
theorem r_runs_generic (σ : ExecState) (n seed : Nat) (h1 : 1 ≤ n)
    (hcap : n ≤ 8) (_hseed : seed < 2 ^ 64)
    (henter : ∀ (l lp : List Int) (siv civ : Int),
      enterFrame (rSt σ (rHeapCall (n : Int) (seed : Int) n l lp siv civ) 15)
          ⟨"minMax"⟩ [rSliceS n]
        = .ok (minMaxFunc,
            [[("$res1", .base ⟨17⟩), ("$res0", .base ⟨16⟩),
              ("s", .base ⟨15⟩)]], [.base ⟨16⟩, .base ⟨17⟩],
            rSt σ (rHeapMFrame (n : Int) (seed : Int) n l lp siv civ) 18))
    (ch : Choices) :
    ∃ k : Nat, k ≤ 202 * n + 218 ∧
      stepFnIter k (rSt σ (rHeap0 (n : Int) (seed : Int)) 5) rHC0 ch
        = .ok (.next .stop,
            rSt σ (rHeapEnd (n : Int) (seed : Int) n (mmFamily n seed)
              (setupList 8 seed n) ((n : Nat) : Int) ((n : Nat) : Int)
              (minSpec (mmFamily n seed)) (maxSpec (mmFamily n seed))
              ((n : Nat) : Int)) 22, ch) := by
  have hn : n < 2 ^ 63 := by omega
  have hne : mmFamily n seed ≠ [] := mmFamily_ne_nil h1
  have hlen : (mmFamily n seed).length = n := mmFamily_length n seed
  have hrange := mmFamily_range n seed
  have hw0 := hrange _ (getD_mem (by omega : 0 < (mmFamily n seed).length))
  -- entry
  have hE1 := r_E1_raw σ (n : Int) (seed : Int) ch
  have hmk := stepFnIter_one
    (stepFn_makeSlice_u64_step (env := envC15R)
      (k := .seq [rS2, rS3, rS4, rS5, rS6, rS7] envC15R
        (.frame [] [] [] [] .stop))
      (r_make_apply σ (n : Int) (seed : Int) n ch))
  have hE2 := r_E2_raw σ (n : Int) (seed : Int) n ch
  have hA0 := su_A0_rawR σ (n : Int) (seed : Int) n (List.replicate n 0) 0 ch
  obtain ⟨k1, hk1, hsu⟩ := su_loopR σ n seed hn n 0 (by omega) ch
  rw [setupList_zero, show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hsu
  have hentry := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hE1 hmk) hE2) hA0) hsu
  -- the copy loop
  have hcA0 := cp_A0_rawR σ (n : Int) (seed : Int) n (mmFamily n seed) zeros8
    ((n : Nat) : Int) 0 ch
  obtain ⟨k2, hk2, hcp⟩ := cp_loopR σ n seed hn h1 hcap henter n 0
    (by omega) ch
  rw [show setupList 8 seed 0 = zeros8 from setupList_zero 8 seed,
    show (((0 : Nat) : Int)) = (0 : Int) from rfl,
    unorm_of_range hw0.1 hw0.2] at hcp
  have hthru := stepFnIter_chain (stepFnIter_chain hentry hcA0) hcp
  -- the minMax loop's first exit test
  have hdA := mh_dispA_rawR σ (n : Int) (seed : Int) n (mmFamily n seed)
    (setupList 8 seed n) ((n : Nat) : Int) ((n : Nat) : Int)
    ((mmFamily n seed).getD 0 0) ((mmFamily n seed).getD 0 0) 1 ch
  have hlenap : applyStrictOp
      (rSt σ (rHeapM (n : Int) (seed : Int) n (mmFamily n seed)
        (setupList 8 seed n) ((n : Nat) : Int) ((n : Nat) : Int)
        ((mmFamily n seed).getD 0 0) ((mmFamily n seed).getD 0 0) 1 false) 22)
      (.lengthOf (some (.slice (.int .uint64)))) [rSliceS n]
      = .ok (.int ((n : Nat) : Int) .int,
          rSt σ (rHeapM (n : Int) (seed : Int) n (mmFamily n seed)
            (setupList 8 seed n) ((n : Nat) : Int) ((n : Nat) : Int)
            ((mmFamily n seed).getD 0 0) ((mmFamily n seed).getD 0 0) 1
            false) 22) :=
    applyStrictOp_len_slice (Nat.le_refl _)
  have hlenstep := stepFnIter_one (ch := ch)
    (stepFn_strict_apply (done := []) (env := mEnvCR)
      (k := .strictK .lessCmp [.int (1 : Int) .int] [] mEnvCR mCmpIfKR)
      hlenap)
  have hcmp := stepFnIter_one (ch := ch)
    (stepFn_strict_apply (done := [.int (1 : Int) .int]) (env := mEnvCR)
      (k := mCmpIfKR) (v := .int ((n : Nat) : Int) .int)
      (applyStrictOp_lessCmp_int (σ :=
        rSt σ (rHeapM (n : Int) (seed : Int) n (mmFamily n seed)
          (setupList 8 seed n) ((n : Nat) : Int) ((n : Nat) : Int)
          ((mmFamily n seed).getD 0 0) ((mmFamily n seed).getD 0 0) 1 false)
          22)
        (a := (1 : Int)) (b := ((n : Nat) : Int))))
  obtain ⟨k3, hk3, hmm⟩ := mh_loopR σ (n : Int) (seed : Int) n
    (mmFamily n seed) (setupList 8 seed n) hlen hrange
    (setupList_length (by omega)) (setupList_range 8 seed n) hn
    ((n : Nat) : Int) ((n : Nat) : Int) (n - 1) 1 (by omega) (by omega)
    rfl ch
  simp only [rCmpHeap] at hmm
  rw [show minSpec (List.take 1 (mmFamily n seed)) = (mmFamily n seed).getD 0 0
      from by rw [minSpec_take_one hne],
    show maxSpec (List.take 1 (mmFamily n seed)) = (mmFamily n seed).getD 0 0
      from by rw [maxSpec_take_one hne],
    show (((1 : Nat) : Int)) = (1 : Int) from rfl] at hmm
  refine ⟨10 + 1 + 42 + 25 + k1 + 25 + k2 + (25 + 1 + 1 + k3), by omega, ?_⟩
  exact stepFnIter_chain hthru (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hdA hlenstep) hcmp) hmm)

/-! ## The user-facing statement -/

/-- **THE HEADLINE (§11 harness form, S3 RELATIONAL)**: for every
`1 ≤ n ≤ 8` and every `seed < 2^64`, running the Go harness
`minmax_harness_r(n, seed)` through the machine's native function entry
— empty-heap state, both arguments at the call boundary — completes
normally past one fuel bound, at every nondeterminism-choice stream, and
returns THREE values: a length-`n` list `pre` as the fixed-cap array the
Go returns, and the pair `(minSpec pre, maxSpec pre)`. The
postcondition is a relation over the RETURNED DATA — no family function
appears in it.

Honesty clauses, all recorded rather than hidden:

* **The cap `n ≤ 8` is a toy bound.** Go's pass-by-value fragment
  cannot return unbounded data, so the harness returns
  `[minmaxCapN]uint64` with `minmaxCapN = 8` (visible in the corpus Go)
  and the copy loop plus zero-padding exist ONLY so the pre-state can
  cross the observation boundary.
* **`∃ pre` is still family-determined.** The witness is
  `mmFamily n seed`; the statement merely avoids SAYING so. Making the
  input genuine ∀-data needs the ghost rung-1 annotation, which is
  designed and not built. What the S3 swap buys is that the
  POSTCONDITION no longer mentions the family — `minmax_ok_v1` states
  `minSpec (mmFamily n seed)`, this states `minSpec pre` over what the
  program returned.
* **`1 ≤ n` is Go's own boundary**, not a proof convenience: `minMax`
  of an empty slice panics at `s[0]` (corpus row
  `examples/minmax/harness-r-empty-panics` pins it against `go run`).
* **Machine idealization** as in the other entries: entry from an empty
  heap, an unbounded heap, allocation always succeeds.

Fuel bound `N = 202·n + 218` — the branch-UNIFORM worst case (either
`if` inside `minMax` may fire, at 16 steps each). The measured law at
a non-wrapping seed is `186·n + 234`; reaching it in the proof would
require carrying `minSpec ≤ maxSpec` through the loop induction to rule
out both branches firing in one iteration, which buys nothing here
because the statement is `∃N`. -/
theorem minmax_ok (n seed : Nat) (h1 : 1 ≤ n) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel minMaxLowered.typeDefs.toList
            minMaxLowered.funcs mmHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            minMaxLowered.methods ch
          = .ok { values := #[goArr8 pre,
                              .int (minSpec pre) .uint64,
                              .int (maxSpec pre) .uint64] } := by
  refine ⟨mmFamily n seed, mmFamily_length n seed, 202 * n + 218,
    fun fuel hfuel ch => ?_⟩
  have hne : mmFamily n seed ≠ [] := mmFamily_ne_nil h1
  have hrange := mmFamily_range n seed
  have hmin := hrange _ (minSpec_mem hne)
  have hmax := hrange _ (maxSpec_mem hne)
  obtain ⟨k, hk, hrun⟩ :=
    r_runs_generic rProg n seed h1 hcap hseed (r_enterFrame_fact n seed) ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  -- the recorded show-bridge (structural: record updates of rProg)
  have hst : rHSeed ((n : Nat) : Int) ((seed : Nat) : Int)
      = rSt rProg (rHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)) 5 := rfl
  rw [rH_entry_eq, unorm_of_range (v := (n : Int)) (by omega) (by omega),
    unorm_of_range (v := (seed : Int)) (by omega) (by omega),
    hst, hfold, runConfig_next_stop]
  show (Except.ok { values := #[.array _, .int _ .uint64, .int _ .uint64] } :
      Except GoError Result) = _
  rw [goArr8, preList_full hcap,
    unorm_of_range hmin.1 hmin.2, unorm_of_range hmin.1 hmin.2,
    unorm_of_range hmin.1 hmin.2, unorm_of_range hmax.1 hmax.2,
    unorm_of_range hmax.1 hmax.2, unorm_of_range hmax.1 hmax.2]

/-- **The D1 run-conditioned twin**: any successful completion of the
harness entry returns those three values. -/
theorem minmax_readout (n seed : Nat) (h1 : 1 ≤ n) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∀ (fuel : Nat) (ch : Choices) (r : Result),
        runFunctionWithContextM fuel minMaxLowered.typeDefs.toList
            minMaxLowered.funcs mmHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            minMaxLowered.methods ch
          = .ok r →
        r = { values := #[goArr8 pre,
                          .int (minSpec pre) .uint64,
                          .int (maxSpec pre) .uint64] } := by
  obtain ⟨pre, hlen, htot⟩ := minmax_ok n seed h1 hcap hseed
  exact ⟨pre, hlen, harness_readout_of_total htot⟩

end GoLean.Examples.MinMax
