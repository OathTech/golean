import GoLeanProofs.Examples.Reverse
import GoLeanProofs.Examples.Targets

/-!
# Reverse — the S1 COPY-RELATIONAL harness (`reverse_harness_v`)

Examples phase-2, slice 1 (2026-08-14; slice record
`docs/2026-08-14_phase2-slice1-spec-swaps.md`, scoping study
`docs/2026-08-14_harness-style-scoping.md` §4.3). The user-facing
headline `reverse_ok` now states the COPY-RELATIONAL harness: setup
builds the family AND saves a pre-copy `t`, and the test phase checks
`s[i] != t[n-1-i]` — the check IS the reversal relation, not the setup
algebra, so the Go reads as an ordinary unit test. The pre-copy is a
HISTORY GHOST materialized as real Go (ghost ladder rung 0 — no
annotations anywhere).

The previous verdict headline over `reverse_harness` (whose check
re-derives the setup formula `seed+(n-1-i)`) is KEPT in
`Examples/Reverse.lean` as the supporting theorem `reverse_ok_v1`
(with `reverse_readout_v1`); its corpus rows and its proof stand
unchanged.

## Cost shape: the segment layer is PROGRAM-GENERIC

Every raw segment below is stated over an ABSTRACT `σ : ExecState`
with only `heap`/`nextAddr` pinned (the `vSt` abbreviation), per
`StepKit`'s "Long CONCRETE runs: the PROGRAM-generic form" (slice
1.5). The kernel therefore never whnf's a state embedding
`reverseLowered.funcs`, and this module's cost does not grow when the
corpus program does. The ONE step that genuinely consults the program
— the `reverse(s)` frame entry — is conditioned on its `enterFrame`
fact through `StepKit.stepFn_call_enter`; this module is that lemma's
SECOND consumer, which is what promoted it out of
`Examples/WordCount/EmptyRun.lean`. The pinned program is unfolded
exactly twice in the whole module: at the lowering pin, and at that
one `enterFrame` discharge.

Placement (address) genericity was assessed and NOT taken: the four
loop phases here touch a heap cell at almost every step, so an
address-abstract statement cannot close by `with_unfolding_all rfl`
and would have to be rebuilt as ~25 conditioned one-steps per
segment. The measured lever is program-genericity; the slice record
carries the assessment.

## Reused, not rebuilt

The pure layers come from `Examples/Reverse.lean` verbatim (they were
un-`private`d for this module, not restated): the input family
`revFamily` with `suList`/`suList_set`/`suList_full`, the two-pointer
surgery `revSwap`/`revSwap_step`/`revSwap_reverse`, and
`getD_reverse_revFamily`. Genuinely new here: the COPY-loop induction
(its invariant is the same prefix shape as the setup loop's, because
`t[i] = s[i]` copies exactly the family element the setup loop wrote),
and a test loop with TWO index reads per iteration instead of one read
plus arithmetic.

Address layout (probe-measured, `n`-independent — `nextAddr = 20`):
0 = `n`, 1 = `seed`, 2 = `$res0`, 3 = `$c5` (s handle), 4 = s backing,
5 = `s`, 6 = setup `i`, 7 = setup flag, 8 = `$c6` (t handle),
9 = t backing, 10 = `t`, 11 = copy `i`, 12 = copy flag,
13 = reverse's `s`, 14/15 = reverse's `i`/`j`, 16 = reverse's flag,
17 = `ok`, 18 = test `i`, 19 = test flag.
-/

namespace GoLean.Examples.Reverse

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-- The PROGRAM-generic state form: an abstract `σ` with only the heap
front and the allocator pinned. Reducible, so `with_unfolding_all rfl`
sees straight through it. -/
abbrev vSt (σ : ExecState) (H : Heap) (na : Nat) : ExecState :=
  { σ with heap := H, nextAddr := na }

/-! ## The harness `Func`, verbatim from the pinned lowering -/

-- HOISTED to `GoLeanProofs/Examples/Targets.lean` (designation, 2026-08-14):
-- `reverseHarnessVFunc` is statement vocabulary of a DESIGNATED gallery headline, so it must
-- live in a def-only module inside the Comparator Challenge's trusted import
-- closure. The definition is unchanged and still visible here via the import.

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem reverseHarnessV_pin :
    findFunctionIn? reverseLowered.funcs ⟨"reverse_harness_v"⟩
    = some reverseHarnessVFunc := rfl

/-! ## Extra pure facts -/

/-- The family's own element at an in-range index (the copy loop reads
`s[i]`, which is exactly this). -/
theorem getD_revFamily {n seed m : Nat} (hm : m < n) :
    (revFamily n seed).getD m 0 = (((seed + m) % 2 ^ 64 : Nat) : Int) := by
  rw [List.getD]
  simp only [revFamily, List.getElem?_map, List.getElem?_range hm]
  rfl

/-! ## Cells and slice handles at the v-layout -/

abbrev vu64 (v : Int) : HeapCell := ⟨some (.int .uint64), .int v .uint64⟩
abbrev vbool (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
abbrev vint (v : Int) : HeapCell := ⟨some (.int .int), .int v .int⟩
/-- `s`'s handle: backing at 4, offset 0, len = cap = `n`. -/
abbrev vSliceS (n : Nat) : GoValue := .slice ⟨some (.base ⟨4⟩), 0, n, n⟩
/-- `t`'s handle: backing at 9. -/
abbrev vSliceT (n : Nat) : GoValue := .slice ⟨some (.base ⟨9⟩), 0, n, n⟩
abbrev vHandleS (n : Nat) : HeapCell :=
  ⟨some (.slice (.int .uint64)), vSliceS n⟩
abbrev vHandleT (n : Nat) : HeapCell :=
  ⟨some (.slice (.int .uint64)), vSliceT n⟩
abbrev vArr (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n (.int .uint64)), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev vNilSlice : HeapCell :=
  ⟨some (.slice (.int .uint64)), .slice ⟨none, 0, 0, 0⟩⟩

/-! ## Statement pieces (suffixes of the harness body) -/

def vS2 : Stmt :=
  .seqn #[.initialization { id := "s", typ := .slice (.int .uint64) },
          .assign (.var "s") (.var "$c5")]
def vS3 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .uint64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) reverseHarnessFunc.suBody]]
def vS4 : Stmt :=
  .seqn #[.initialization { id := "$c6", typ := .slice (.int .uint64) },
          .makeSlice (.var "$c6") (.int .uint64) (.var "n") none]
def vS5 : Stmt :=
  .seqn #[.initialization { id := "t", typ := .slice (.int .uint64) },
          .assign (.var "t") (.var "$c6")]
def vS6 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .uint64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) reverseHarnessVFunc.cpBody]]
def vS7 : Stmt := .call #[] ⟨"reverse"⟩ #[.var "s"]
def vS8 : Stmt :=
  .seqn #[.initialization { id := "ok", typ := .int .uint64 },
          .assign (.var "ok") (.intLit 1 .uint64)]
def vS9 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .uint64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) reverseHarnessVFunc.tvBody]]
def vS10 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "ok"), .returnStmt]

/-! ## Environments -/

def baseEnvV : Scope :=
  [("$res0", .base ⟨2⟩), ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]
def envC5V : LocalEnv := [[("$c5", .base ⟨3⟩)], baseEnvV]
def sScopeV : Scope := [("s", .base ⟨5⟩), ("$c5", .base ⟨3⟩)]
def c6ScopeV : Scope :=
  [("$c6", .base ⟨8⟩), ("s", .base ⟨5⟩), ("$c5", .base ⟨3⟩)]
def tScopeV : Scope :=
  [("t", .base ⟨10⟩), ("$c6", .base ⟨8⟩), ("s", .base ⟨5⟩),
   ("$c5", .base ⟨3⟩)]
def okScopeV : Scope :=
  [("ok", .base ⟨17⟩), ("t", .base ⟨10⟩), ("$c6", .base ⟨8⟩),
   ("s", .base ⟨5⟩), ("$c5", .base ⟨3⟩)]

def suEnvV : LocalEnv :=
  [[("$forFirst", .base ⟨7⟩)], [("i", .base ⟨6⟩)], sScopeV, baseEnvV]
def suEnvV2 : LocalEnv := [] :: [] :: suEnvV
def cpEnvV : LocalEnv :=
  [[("$forFirst", .base ⟨12⟩)], [("i", .base ⟨11⟩)], tScopeV, baseEnvV]
def cpEnvV2 : LocalEnv := [] :: [] :: cpEnvV
def tvEnvV : LocalEnv :=
  [[("$forFirst", .base ⟨19⟩)], [("i", .base ⟨18⟩)], okScopeV, baseEnvV]
def tvEnvV2 : LocalEnv := [] :: [] :: tvEnvV

/-! ## Continuations -/

def vTailAfterSetup : Cont :=
  .seq [vS4, vS5, vS6, vS7, vS8, vS9, vS10] [sScopeV, baseEnvV]
    (.frame [] [] [] [] .stop)
def suHeadTailV : Cont :=
  .seq [] suEnvV
    (.seq [] [[("i", .base ⟨6⟩)], sScopeV, baseEnvV] vTailAfterSetup)
def suHeadCfgV : Config :=
  .exec (.while (.boolLit true) reverseHarnessFunc.suBody) suEnvV suHeadTailV
def suLoopKV : Cont :=
  .loop (.boolLit true) reverseHarnessFunc.suBody suEnvV suHeadTailV
def suStoreBlockV : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
        (.add (.var "seed") (.var "i"))]]
def suCmpContV : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: suEnvV)
    (.seq [suStoreBlockV] ([] :: suEnvV) suLoopKV)
def suRefV (n : Nat) (iv : Int) : TargetRef :=
  .chain (vSliceS n) [.int iv .uint64] [.index]
def suSwTailV : Cont :=
  .seq [] suEnvV2 (.seq [] ([] :: suEnvV) suLoopKV)

def vTailAfterCopy : Cont :=
  .seq [vS7, vS8, vS9, vS10] [tScopeV, baseEnvV] (.frame [] [] [] [] .stop)
def cpHeadTailV : Cont :=
  .seq [] cpEnvV
    (.seq [] [[("i", .base ⟨11⟩)], tScopeV, baseEnvV] vTailAfterCopy)
def cpHeadCfgV : Config :=
  .exec (.while (.boolLit true) reverseHarnessVFunc.cpBody) cpEnvV cpHeadTailV
def cpLoopKV : Cont :=
  .loop (.boolLit true) reverseHarnessVFunc.cpBody cpEnvV cpHeadTailV
def cpStoreBlockV : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.var "t") (.var "i")))
        (.indexGet (.var "s") (.var "i"))]]
def cpCmpContV : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: cpEnvV)
    (.seq [cpStoreBlockV] ([] :: cpEnvV) cpLoopKV)
def cpRefV (n : Nat) (iv : Int) : TargetRef :=
  .chain (vSliceT n) [.int iv .uint64] [.index]
def cpSwTailV : Cont :=
  .seq [] cpEnvV2 (.seq [] ([] :: cpEnvV) cpLoopKV)
def cpRhsKV (n : Nat) (iv : Int) : Cont :=
  .rhsK .vals [cpRefV n iv] [] [] (.seqn #[]) cpEnvV2 cpSwTailV

/-! ### Reverse-phase continuations at the v-layout (the subject's own
tower sitting on the after-call continuation) -/

def rvEnvInV : LocalEnv :=
  [[("$forFirst", .base ⟨16⟩)], [("j", .base ⟨15⟩), ("i", .base ⟨14⟩)],
   [], [("s", .base ⟨13⟩)]]
def rvEnvMidV : LocalEnv :=
  [[("j", .base ⟨15⟩), ("i", .base ⟨14⟩)], [], [("s", .base ⟨13⟩)]]
def rvEnvOutV : LocalEnv := [[], [("s", .base ⟨13⟩)]]
def rvAfterCallV : Cont :=
  .seq [vS8, vS9, vS10] [tScopeV, baseEnvV] (.frame [] [] [] [] .stop)
def rvFrameV : Cont :=
  .frame [] [tScopeV, baseEnvV] [] [] rvAfterCallV false
def rvHeadTailV : Cont :=
  .seq [] rvEnvInV (.seq [] rvEnvMidV (.seq [] rvEnvOutV rvFrameV))
def rvHeadCfgV : Config :=
  .exec (.while (.boolLit true) revWhileBody) rvEnvInV rvHeadTailV
def rvLoopKV : Cont :=
  .loop (.boolLit true) revWhileBody rvEnvInV rvHeadTailV
def rvCmpContV : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: rvEnvInV)
    (.seq [revSwapBlock] ([] :: rvEnvInV) rvLoopKV)
def rvEnvIn2V : LocalEnv := [] :: [] :: rvEnvInV
def rvSwTailV : Cont :=
  .seq [] rvEnvIn2V (.seq [] ([] :: rvEnvInV) rvLoopKV)
def rvRefV (n : Nat) (v : Int) : TargetRef :=
  .chain (vSliceS n) [.int v .int] [.index]
def rvRhsK1V (n : Nat) (iv jv : Int) : Cont :=
  .rhsK .vals [rvRefV n iv, rvRefV n jv] [] [.indexGet (.var "s") (.var "i")]
    (.seqn #[]) rvEnvIn2V rvSwTailV
def rvRhsK2V (n : Nat) (iv jv : Int) (wj : GoValue) : Cont :=
  .rhsK .vals [rvRefV n iv, rvRefV n jv] [wj] [] (.seqn #[]) rvEnvIn2V
    rvSwTailV
def rvEntryRhsKV : Cont :=
  .rhsK .vals
    [.chain (.addr (.base ⟨14⟩)) [] [], .chain (.addr (.base ⟨15⟩)) [] []]
    [.int 0 .int] [] (.seqn #[]) rvEnvMidV
    (.seq [ffBlock] rvEnvMidV (.seq [] rvEnvOutV rvFrameV))
/-- The drained call-argument continuation at the `reverse(s)` call —
the one point the machine consults the pinned program. -/
def rvCallArgsKV : Cont :=
  .callArgsK ⟨"reverse"⟩ [] [] [] [tScopeV, baseEnvV] rvAfterCallV

/-! ### Test-phase continuations -/

def tvIdxExpr : Expr :=
  .sub (.sub (.var "n") (.intLit 1 .uint64)) (.var "i")
def tvHeadTailV : Cont :=
  .seq [] tvEnvV
    (.seq [] [[("i", .base ⟨18⟩)], okScopeV, baseEnvV]
      (.seq [vS10] [okScopeV, baseEnvV] (.frame [] [] [] [] .stop)))
def tvHeadCfgV : Config :=
  .exec (.while (.boolLit true) reverseHarnessVFunc.tvBody) tvEnvV tvHeadTailV
def tvLoopKV : Cont :=
  .loop (.boolLit true) reverseHarnessVFunc.tvBody tvEnvV tvHeadTailV
def tvCheckBlockV : Stmt :=
  .block #[]
    #[.ifThenElse
        (.neqCmp (.int .uint64) (.indexGet (.var "s") (.var "i"))
          (.indexGet (.var "t") tvIdxExpr))
        (.block #[] #[.seqn #[.assign (.var "ok") (.intLit 0 .uint64)]])
        (.seqn #[])]
def tvCmpContV : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: tvEnvV)
    (.seq [tvCheckBlockV] ([] :: tvEnvV) tvLoopKV)
def tvIfKV : Cont :=
  .ifK (.block #[] #[.seqn #[.assign (.var "ok") (.intLit 0 .uint64)]])
    (.seqn #[]) tvEnvV2 (.seq [] tvEnvV2 (.seq [] ([] :: tvEnvV) tvLoopKV))
def tvNeqK1V : Cont :=
  .strictK (.neqCmp (.int .uint64)) [] [.indexGet (.var "t") tvIdxExpr]
    tvEnvV2 tvIfKV
def tvNeqK2V (w : GoValue) : Cont :=
  .strictK (.neqCmp (.int .uint64)) [w] [] tvEnvV2 tvIfKV

/-! ## Heap fronts (program-generic: only these are ever pinned) -/

def vHeap0 (nv sv : Int) : Heap :=
  [(.base ⟨0⟩, vu64 nv), (.base ⟨1⟩, vu64 sv), (.base ⟨2⟩, vu64 0)]

def vHeapC5 (n seed : Nat) : Heap :=
  [(.base ⟨0⟩, vu64 (n : Int)), (.base ⟨1⟩, vu64 (seed : Int)),
   (.base ⟨2⟩, vu64 0), (.base ⟨3⟩, vNilSlice)]

def vHeapMakeS (n seed : Nat) : Heap :=
  [(.base ⟨0⟩, vu64 (n : Int)), (.base ⟨1⟩, vu64 (seed : Int)),
   (.base ⟨2⟩, vu64 0), (.base ⟨3⟩, vHandleS n),
   (.base ⟨4⟩, vArr n (List.replicate n 0))]

def vHeapSu (n seed : Nat) (l : List Int) (iv : Int) (ffv : Bool) : Heap :=
  [(.base ⟨0⟩, vu64 (n : Int)), (.base ⟨1⟩, vu64 (seed : Int)),
   (.base ⟨2⟩, vu64 0), (.base ⟨3⟩, vHandleS n),
   (.base ⟨4⟩, vArr n l), (.base ⟨5⟩, vHandleS n),
   (.base ⟨6⟩, vu64 iv), (.base ⟨7⟩, vbool ffv)]

def vHeapC6 (n seed : Nat) (l : List Int) (iv : Int) : Heap :=
  vHeapSu n seed l iv false ++ [(.base ⟨8⟩, vNilSlice)]

def vHeapMakeT (n seed : Nat) (l : List Int) (iv : Int) : Heap :=
  vHeapSu n seed l iv false ++
    [(.base ⟨8⟩, vHandleT n),
     (.base ⟨9⟩, vArr n (List.replicate n 0))]

def vHeapCp (n seed : Nat) (siv : Int) (ls lt : List Int) (iv : Int)
    (ffv : Bool) : Heap :=
  [(.base ⟨0⟩, vu64 (n : Int)), (.base ⟨1⟩, vu64 (seed : Int)),
   (.base ⟨2⟩, vu64 0), (.base ⟨3⟩, vHandleS n),
   (.base ⟨4⟩, vArr n ls), (.base ⟨5⟩, vHandleS n),
   (.base ⟨6⟩, vu64 siv), (.base ⟨7⟩, vbool false),
   (.base ⟨8⟩, vHandleT n), (.base ⟨9⟩, vArr n lt),
   (.base ⟨10⟩, vHandleT n), (.base ⟨11⟩, vu64 iv),
   (.base ⟨12⟩, vbool ffv)]

def vHeapRvEntry (n seed : Nat) (siv civ : Int) (ls lt : List Int) : Heap :=
  vHeapCp n seed siv ls lt civ false ++
    [(.base ⟨13⟩, vHandleS n), (.base ⟨14⟩, vint 0), (.base ⟨15⟩, vint 0)]

def vHeapRv (n seed : Nat) (siv civ : Int) (ls lt : List Int)
    (iv jv : Int) (ffv : Bool) : Heap :=
  vHeapCp n seed siv ls lt civ false ++
    [(.base ⟨13⟩, vHandleS n), (.base ⟨14⟩, vint iv),
     (.base ⟨15⟩, vint jv), (.base ⟨16⟩, vbool ffv)]

def vHeapTv (n seed : Nat) (siv civ rif rjf : Int) (ls lt : List Int)
    (iv : Int) (ffv : Bool) : Heap :=
  vHeapRv n seed siv civ ls lt rif rjf false ++
    [(.base ⟨17⟩, vu64 1), (.base ⟨18⟩, vu64 iv), (.base ⟨19⟩, vbool ffv)]

/-- The terminal heap: the verdict 1 delivered to `$res0`. -/
def vHeapEnd (n seed : Nat) (siv civ rif rjf : Int) (ls lt : List Int)
    (iv : Int) : Heap :=
  [(.base ⟨0⟩, vu64 (n : Int)), (.base ⟨1⟩, vu64 (seed : Int)),
   (.base ⟨2⟩, vu64 1), (.base ⟨3⟩, vHandleS n),
   (.base ⟨4⟩, vArr n ls), (.base ⟨5⟩, vHandleS n),
   (.base ⟨6⟩, vu64 siv), (.base ⟨7⟩, vbool false),
   (.base ⟨8⟩, vHandleT n), (.base ⟨9⟩, vArr n lt),
   (.base ⟨10⟩, vHandleT n), (.base ⟨11⟩, vu64 civ),
   (.base ⟨12⟩, vbool false), (.base ⟨13⟩, vHandleS n),
   (.base ⟨14⟩, vint rif), (.base ⟨15⟩, vint rjf),
   (.base ⟨16⟩, vbool false), (.base ⟨17⟩, vu64 1),
   (.base ⟨18⟩, vu64 iv), (.base ⟨19⟩, vbool false)]

/-- The pinned program as a state with an empty heap — with the
`derive_entry_eq` invocation below, the one place this module carries
`reverseLowered` (moved up from the run section for the macro's sake,
G0 item 3c). -/
def vProg : ExecState :=
  { types := reverseLowered.typeDefs.toList,
    functions := reverseLowered.funcs,
    methods := reverseLowered.methods,
    heap := [], nextAddr := 0 }

/- The post-prelude state (`vHSeed`), the start configuration
(`vHC₀`), and the entry equation (`revHV_entry_eq`, formerly
hand-written in the run section) are DERIVED — the P4 entry-equation
macro in its PROGRAM-GENERIC form (G0 item 3c): the emitted state is
the record update `{ vProg with … }`, so the headline's show-bridge to
the compositional `vSt vProg (vHeap0 …) 3` spelling is structural. -/
derive_entry_eq revHV_entry_eq reverseLowered reverseHarnessVFunc vHSeed vHC₀ vProg

/-! ## The backing-cell lookups (the conditioned steps' premises) -/

theorem lookup_suV (σ : ExecState) (n seed : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) (na : Nat) :
    Heap.lookup (vSt σ (vHeapSu n seed l iv ffv) na).heap (.base ⟨4⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [vHeapSu, Heap.lookup, vArr]

theorem lookup_cpS (σ : ExecState) (n seed : Nat) (siv : Int)
    (ls lt : List Int) (iv : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (vSt σ (vHeapCp n seed siv ls lt iv ffv) na).heap (.base ⟨4⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨ls.map (fun v => .int v .uint64)⟩⟩ := by
  simp [vHeapCp, Heap.lookup, vArr]

theorem lookup_cpT (σ : ExecState) (n seed : Nat) (siv : Int)
    (ls lt : List Int) (iv : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (vSt σ (vHeapCp n seed siv ls lt iv ffv) na).heap (.base ⟨9⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨lt.map (fun v => .int v .uint64)⟩⟩ := by
  simp [vHeapCp, Heap.lookup, vArr]

theorem lookup_rvS (σ : ExecState) (n seed : Nat) (siv civ : Int)
    (ls lt : List Int) (iv jv : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (vSt σ (vHeapRv n seed siv civ ls lt iv jv ffv) na).heap
        (.base ⟨4⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨ls.map (fun v => .int v .uint64)⟩⟩ := by
  simp [vHeapRv, vHeapCp, Heap.lookup, vArr]

theorem lookup_tvS (σ : ExecState) (n seed : Nat) (siv civ rif rjf : Int)
    (ls lt : List Int) (iv : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup
        (vSt σ (vHeapTv n seed siv civ rif rjf ls lt iv ffv) na).heap
        (.base ⟨4⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨ls.map (fun v => .int v .uint64)⟩⟩ := by
  simp [vHeapTv, vHeapRv, vHeapCp, Heap.lookup, vArr]

theorem lookup_tvT (σ : ExecState) (n seed : Nat) (siv civ rif rjf : Int)
    (ls lt : List Int) (iv : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup
        (vSt σ (vHeapTv n seed siv civ rif rjf ls lt iv ffv) na).heap
        (.base ⟨9⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨lt.map (fun v => .int v .uint64)⟩⟩ := by
  simp [vHeapTv, vHeapRv, vHeapCp, Heap.lookup, vArr]

/-! ## Raw run segments — every one PROGRAM-generic, split exactly at
the data-dependent points: the two `makeSlice` applies, each loop's
exit test, the setup store, the copy read and store, the two swap
reads and stores, the two test reads. -/

/-- Entry A: the post-prelude configuration → the `$c5` makeSlice
apply point. 10 steps. -/
theorem vH_E1_raw (σ : ExecState) (n seed : Nat) (ch : Choices) :
    stepFnIter 10 (vSt σ (vHeap0 (n : Int) (seed : Int)) 3) vHC₀ ch
      = .ok (.retV (.int (n : Int) .uint64)
          (.stmtOpK (.makeSlice (.int .uint64) false) 1
            [.addr (.base ⟨3⟩)] [] envC5V
            (.seq [vS2, vS3, vS4, vS5, vS6, vS7, vS8, vS9, vS10] envC5V
              (.frame [] [] [] [] .stop))),
        vSt σ (vHeapC5 n seed) 4, ch) := by
  with_unfolding_all rfl

/-- The `makeSlice` machine step, conditioned on the apply fact.
PROMOTED to `StepKit.stepFn_makeSlice_u64_step` (phase-2 slice 1, second
consumer: the minmax S3 layer); this module is one of the promotion's
two fixture witnesses. -/
theorem stepFn_makeSliceV {σ σ' : ExecState} {n : Nat}
    {tv : GoValue} {env : LocalEnv} {k : Cont} {ch : Choices}
    (happly : applyStmtOp σ ch (.makeSlice (.int .uint64) false) 1
      [tv, .int (n : Nat) .uint64] = .ok (σ', ch)) :
    stepFn σ (.retV (.int (n : Nat) .uint64)
      (.stmtOpK (.makeSlice (.int .uint64) false) 1 [tv] [] env k)) ch
      = .ok (.next k, σ', ch) :=
  stepFn_makeSlice_u64_step happly

/-- **`make([]uint64, n)` at SYMBOLIC `n`, for `s`** — the entry
phase's one branch point (the machine's non-negativity check on the
length). The backing is `n` zeros. -/
theorem vH_makeS_apply (σ : ExecState) (n seed : Nat) (ch : Choices) :
    applyStmtOp (vSt σ (vHeapC5 n seed) 4) ch
      (.makeSlice (.int .uint64) false) 1
      [.addr (.base ⟨3⟩), .int (n : Nat) .uint64]
      = .ok (vSt σ (vHeapMakeS n seed) 5, ch) := by
  have hnat : ∀ s : String,
      natFromNonnegativeInt s ((n : Nat) : Int) = .ok n := by
    intro s
    simp only [natFromNonnegativeInt]
    rw [if_neg (by omega : ¬ (((n : Nat) : Int) < 0))]
    rfl
  have hback := GoLean.Iris.buildDefaultArrayValue_int
    (vSt σ (vHeapC5 n seed) 4) .uint64 n
  simp only [applyStmtOp, applyStmtOpCore, valueAsInt, Bind.bind,
    Except.bind, pure, Except.pure, hnat, hback]
  rw [if_neg (by omega : ¬ (n < n))]
  simp only [ExecState.alloc, ExecState.freshLoc, valueAsLoc, Except.bind,
    storeLoc, Heap.lookup, normalizeValueForTy, normalizeValueForTyFuel,
    typeResolutionFuel, Heap.set, pure, Except.pure, vSt, vHeapC5,
    vHeapMakeS, vArr, vHandleS, vSliceS, vu64, vNilSlice, List.map_replicate]
  rfl

/-- Entry B: the `s := $c5` binding, the setup counter and flag → the
setup loop head. 42 steps. -/
theorem vH_E2_raw (σ : ExecState) (n seed : Nat) (ch : Choices) :
    stepFnIter 42 (vSt σ (vHeapMakeS n seed) 5)
      (.next (.seq [vS2, vS3, vS4, vS5, vS6, vS7, vS8, vS9, vS10] envC5V
        (.frame [] [] [] [] .stop))) ch
      = .ok (suHeadCfgV,
          vSt σ (vHeapSu n seed (List.replicate n 0) 0 true) 8, ch) := by
  with_unfolding_all rfl

/-! ### The setup loop -/

/-- Setup first-pass dispatch: head with the flag up → the exit test. -/
theorem su_A0_rawV (σ : ExecState) (n seed : Nat) (l : List Int) (iv : Int)
    (ch : Choices) :
    stepFnIter 25 (vSt σ (vHeapSu n seed l iv true) 8) suHeadCfgV ch
      = .ok (.retV (.bool (decide (iv < (n : Int)))) suCmpContV,
          vSt σ (vHeapSu n seed l iv false) 8, ch) := by
  with_unfolding_all rfl

/-- Setup later-pass dispatch: `i++`, then the exit test. -/
theorem su_A1_rawV (σ : ExecState) (n seed : Nat) (l : List Int) (iv : Int)
    (ch : Choices) :
    stepFnIter 29 (vSt σ (vHeapSu n seed l iv false) 8) suHeadCfgV ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < (n : Int)))) suCmpContV,
          vSt σ (vHeapSu n seed l
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false) 8, ch) := by
  with_unfolding_all rfl

/-- Setup fill phase: test true → target + RHS evaluated, the store
pending (`seed + i`, wrapped once by the add). 18 steps. -/
theorem su_B1_rawV (σ : ExecState) (n seed : Nat) (l : List Int) (iv : Int)
    (ch : Choices) :
    stepFnIter 18 (vSt σ (vHeapSu n seed l iv false) 8)
      (.retV (.bool true) suCmpContV) ch
      = .ok (.next (.storeK [suRefV n iv]
            [.int (IntKind.normalize .uint64 ((seed : Int) + iv)) .uint64]
            (.seqn #[]) suEnvV2 suSwTailV),
          vSt σ (vHeapSu n seed l iv false) 8, ch) := by
  with_unfolding_all rfl

/-- Setup fill tail: store done → back to the loop head. 5 steps. -/
theorem su_D_rawV (σ : ExecState) (n seed : Nat) (l : List Int) (iv : Int)
    (ch : Choices) :
    stepFnIter 5 (vSt σ (vHeapSu n seed l iv false) 8)
      (.next (.storeK [] [] (.seqn #[]) suEnvV2 suSwTailV)) ch
      = .ok (suHeadCfgV, vSt σ (vHeapSu n seed l iv false) 8, ch) := by
  with_unfolding_all rfl

/-- Setup exit: test false → the `$c6` makeSlice apply point. 15 steps. -/
theorem su_X_rawV (σ : ExecState) (n seed : Nat) (l : List Int) (iv : Int)
    (ch : Choices) :
    stepFnIter 15 (vSt σ (vHeapSu n seed l iv false) 8)
      (.retV (.bool false) suCmpContV) ch
      = .ok (.retV (.int (n : Int) .uint64)
          (.stmtOpK (.makeSlice (.int .uint64) false) 1
            [.addr (.base ⟨8⟩)] [] [c6ScopeV, baseEnvV]
            (.seq [vS5, vS6, vS7, vS8, vS9, vS10] [c6ScopeV, baseEnvV]
              (.frame [] [] [] [] .stop))),
        vSt σ (vHeapC6 n seed l iv) 9, ch) := by
  with_unfolding_all rfl

/-- **`make([]uint64, n)` at SYMBOLIC `n`, for `t`** — the copy
phase's allocation, at the second placement. -/
theorem vH_makeT_apply (σ : ExecState) (n seed : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    applyStmtOp (vSt σ (vHeapC6 n seed l iv) 9) ch
      (.makeSlice (.int .uint64) false) 1
      [.addr (.base ⟨8⟩), .int (n : Nat) .uint64]
      = .ok (vSt σ (vHeapMakeT n seed l iv) 10, ch) := by
  have hnat : ∀ s : String,
      natFromNonnegativeInt s ((n : Nat) : Int) = .ok n := by
    intro s
    simp only [natFromNonnegativeInt]
    rw [if_neg (by omega : ¬ (((n : Nat) : Int) < 0))]
    rfl
  have hback := GoLean.Iris.buildDefaultArrayValue_int
    (vSt σ (vHeapC6 n seed l iv) 9) .uint64 n
  simp only [applyStmtOp, applyStmtOpCore, valueAsInt, Bind.bind,
    Except.bind, pure, Except.pure, hnat, hback]
  rw [if_neg (by omega : ¬ (n < n))]
  simp only [ExecState.alloc, ExecState.freshLoc, valueAsLoc, Except.bind,
    storeLoc, Heap.lookup, normalizeValueForTy, normalizeValueForTyFuel,
    typeResolutionFuel, Heap.set, pure, Except.pure, vSt, vHeapC6,
    vHeapMakeT, vHeapSu, vArr, vHandleT, vSliceT, vHandleS, vSliceS, vu64,
    vbool, vNilSlice, List.map_replicate]
  rfl

/-- Copy entry: the `t := $c6` binding, the copy counter and flag →
the copy loop head. 42 steps. -/
theorem cp_E_rawV (σ : ExecState) (n seed : Nat) (l : List Int) (iv : Int)
    (ch : Choices) :
    stepFnIter 42 (vSt σ (vHeapMakeT n seed l iv) 10)
      (.next (.seq [vS5, vS6, vS7, vS8, vS9, vS10] [c6ScopeV, baseEnvV]
        (.frame [] [] [] [] .stop))) ch
      = .ok (cpHeadCfgV,
          vSt σ (vHeapCp n seed iv l (List.replicate n 0) 0 true) 13, ch) := by
  with_unfolding_all rfl

/-! ### The copy loop — the history ghost being materialized -/

/-- Copy first-pass dispatch: head with the flag up → the exit test. -/
theorem cp_A0_rawV (σ : ExecState) (n seed : Nat) (siv : Int)
    (ls lt : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 25 (vSt σ (vHeapCp n seed siv ls lt iv true) 13) cpHeadCfgV ch
      = .ok (.retV (.bool (decide (iv < (n : Int)))) cpCmpContV,
          vSt σ (vHeapCp n seed siv ls lt iv false) 13, ch) := by
  with_unfolding_all rfl

/-- Copy later-pass dispatch: `i++`, then the exit test. -/
theorem cp_A1_rawV (σ : ExecState) (n seed : Nat) (siv : Int)
    (ls lt : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 29 (vSt σ (vHeapCp n seed siv ls lt iv false) 13) cpHeadCfgV ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < (n : Int)))) cpCmpContV,
          vSt σ (vHeapCp n seed siv ls lt
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false) 13, ch) := by
  with_unfolding_all rfl

/-- Copy phase 1: test true → the store target banked, the `s[i]` read
at its apply point. 16 steps. -/
theorem cp_B1_rawV (σ : ExecState) (n seed : Nat) (siv : Int)
    (ls lt : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 16 (vSt σ (vHeapCp n seed siv ls lt iv false) 13)
      (.retV (.bool true) cpCmpContV) ch
      = .ok (.retV (.int iv .uint64)
            (.strictK .indexGet [vSliceS n] [] cpEnvV2 (cpRhsKV n iv)),
          vSt σ (vHeapCp n seed siv ls lt iv false) 13, ch) := by
  with_unfolding_all rfl

/-- Copy phase 2: the read value delivered → the store pending. -/
theorem cp_B2_rawV (σ : ExecState) (n seed : Nat) (siv : Int)
    (ls lt : List Int) (iv : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1 (vSt σ (vHeapCp n seed siv ls lt iv false) 13)
      (.retV w (cpRhsKV n iv)) ch
      = .ok (.next (.storeK [cpRefV n iv] [w] (.seqn #[]) cpEnvV2 cpSwTailV),
          vSt σ (vHeapCp n seed siv ls lt iv false) 13, ch) := by
  with_unfolding_all rfl

/-- Copy tail: store done → back to the loop head. 5 steps. -/
theorem cp_D_rawV (σ : ExecState) (n seed : Nat) (siv : Int)
    (ls lt : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 5 (vSt σ (vHeapCp n seed siv ls lt iv false) 13)
      (.next (.storeK [] [] (.seqn #[]) cpEnvV2 cpSwTailV)) ch
      = .ok (cpHeadCfgV, vSt σ (vHeapCp n seed siv ls lt iv false) 13,
          ch) := by
  with_unfolding_all rfl

/-- Copy exit: test false → the `reverse(s)` call's argument delivered
at the drained `callArgsK` — the machine's ONE program-consulting
point. 9 steps. -/
theorem cp_X_rawV (σ : ExecState) (n seed : Nat) (siv : Int)
    (ls lt : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 9 (vSt σ (vHeapCp n seed siv ls lt iv false) 13)
      (.retV (.bool false) cpCmpContV) ch
      = .ok (.retV (vSliceS n) rvCallArgsKV,
          vSt σ (vHeapCp n seed siv ls lt iv false) 13, ch) := by
  with_unfolding_all rfl

/-- The frame heap right after `reverse`'s entry: the parameter `s`
bound at 13. -/
def vHeapRvFrame (n seed : Nat) (siv civ : Int) (ls lt : List Int) : Heap :=
  vHeapCp n seed siv ls lt civ false ++ [(.base ⟨13⟩, vHandleS n)]

/-- Reverse prologue: `i`/`j` declared, `len(s)` walked to its apply
point. 20 steps. -/
theorem rv_pre_rawV (σ : ExecState) (n seed : Nat) (siv civ : Int)
    (ls lt : List Int) (ch : Choices) :
    stepFnIter 20 (vSt σ (vHeapRvFrame n seed siv civ ls lt) 14)
      (.exec reverseFunc.body [[("s", .base ⟨13⟩)]] rvFrameV) ch
      = .ok (.retV (vSliceS n)
            (.strictK (.lengthOf (some (.slice (.int .uint64)))) [] []
              rvEnvMidV (.strictK .sub [] [.intLit 1 .int] rvEnvMidV
                rvEntryRhsKV)),
          vSt σ (vHeapRvEntry n seed siv civ ls lt) 16, ch) := by
  with_unfolding_all rfl

/-- Reverse entry tail: `len - 1` delivered → `i, j` stored, the flag
block run, the reverse loop head. 22 steps. -/
theorem rv_entry_rawV (σ : ExecState) (n seed : Nat) (siv civ : Int)
    (ls lt : List Int) (ch : Choices) :
    stepFnIter 22 (vSt σ (vHeapRvEntry n seed siv civ ls lt) 16)
      (.retV (.int (n : Nat) .int)
        (.strictK .sub [] [.intLit 1 .int] rvEnvMidV rvEntryRhsKV)) ch
      = .ok (rvHeadCfgV,
          vSt σ (vHeapRv n seed siv civ ls lt 0
            (IntKind.normalize .int
              (IntKind.normalize .int ((n : Int) - 1))) true) 17, ch) := by
  with_unfolding_all rfl

/-! ### The reverse phase (the subject's own two-pointer loop, at the
v-layout) -/

/-- Reverse first-pass dispatch. -/
theorem rv_A0_rawV (σ : ExecState) (n seed : Nat) (siv civ : Int)
    (ls lt : List Int) (iv jv : Int) (ch : Choices) :
    stepFnIter 25 (vSt σ (vHeapRv n seed siv civ ls lt iv jv true) 17)
      rvHeadCfgV ch
      = .ok (.retV (.bool (decide (iv < jv))) rvCmpContV,
          vSt σ (vHeapRv n seed siv civ ls lt iv jv false) 17, ch) := by
  with_unfolding_all rfl

/-- Reverse later-pass dispatch: `i, j = i+1, j-1`, then the test. -/
theorem rv_A1_rawV (σ : ExecState) (n seed : Nat) (siv civ : Int)
    (ls lt : List Int) (iv jv : Int) (ch : Choices) :
    stepFnIter 40 (vSt σ (vHeapRv n seed siv civ ls lt iv jv false) 17)
      rvHeadCfgV ch
      = .ok (.retV (.bool (decide
              (IntKind.normalize .int (IntKind.normalize .int (iv + 1))
                < IntKind.normalize .int (IntKind.normalize .int (jv - 1)))))
            rvCmpContV,
          vSt σ (vHeapRv n seed siv civ ls lt
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            (IntKind.normalize .int (IntKind.normalize .int (jv - 1)))
            false) 17, ch) := by
  with_unfolding_all rfl

/-- Swap phase 1a: test true → the first index-read apply (`s[j]`). -/
theorem rv_swapA_rawV (σ : ExecState) (n seed : Nat) (siv civ : Int)
    (ls lt : List Int) (iv jv : Int) (ch : Choices) :
    stepFnIter 20 (vSt σ (vHeapRv n seed siv civ ls lt iv jv false) 17)
      (.retV (.bool true) rvCmpContV) ch
      = .ok (.retV (.int jv .int)
            (.strictK .indexGet [vSliceS n] [] rvEnvIn2V (rvRhsK1V n iv jv)),
          vSt σ (vHeapRv n seed siv civ ls lt iv jv false) 17, ch) := by
  with_unfolding_all rfl

/-- Swap phase 1b: first read delivered → the second read apply. -/
theorem rv_swapB_rawV (σ : ExecState) (n seed : Nat) (siv civ : Int)
    (ls lt : List Int) (iv jv : Int) (wj : GoValue) (ch : Choices) :
    stepFnIter 5 (vSt σ (vHeapRv n seed siv civ ls lt iv jv false) 17)
      (.retV wj (rvRhsK1V n iv jv)) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [vSliceS n] [] rvEnvIn2V
              (rvRhsK2V n iv jv wj)),
          vSt σ (vHeapRv n seed siv civ ls lt iv jv false) 17, ch) := by
  with_unfolding_all rfl

/-- Swap phase 1 → 2: both reads banked, the stores begin. -/
theorem rv_swapC_rawV (σ : ExecState) (n seed : Nat) (siv civ : Int)
    (ls lt : List Int) (iv jv : Int) (wj wi : GoValue) (ch : Choices) :
    stepFnIter 1 (vSt σ (vHeapRv n seed siv civ ls lt iv jv false) 17)
      (.retV wi (rvRhsK2V n iv jv wj)) ch
      = .ok (.next (.storeK [rvRefV n iv, rvRefV n jv] [wj, wi] (.seqn #[])
            rvEnvIn2V rvSwTailV),
          vSt σ (vHeapRv n seed siv civ ls lt iv jv false) 17, ch) := by
  with_unfolding_all rfl

/-- Swap tail: stores done → back to the loop head. -/
theorem rv_swapD_rawV (σ : ExecState) (n seed : Nat) (siv civ : Int)
    (ls lt : List Int) (iv jv : Int) (ch : Choices) :
    stepFnIter 5 (vSt σ (vHeapRv n seed siv civ ls lt iv jv false) 17)
      (.next (.storeK [] [] (.seqn #[]) rvEnvIn2V rvSwTailV)) ch
      = .ok (rvHeadCfgV, vSt σ (vHeapRv n seed siv civ ls lt iv jv false) 17,
          ch) := by
  with_unfolding_all rfl

/-- Reverse exit → frame exit, `ok := 1`, the test loop's counter and
flag declared, the test loop head. 50 steps. -/
theorem rv_X_rawV (σ : ExecState) (n seed : Nat) (siv civ : Int)
    (ls lt : List Int) (iv jv : Int) (ch : Choices) :
    stepFnIter 50 (vSt σ (vHeapRv n seed siv civ ls lt iv jv false) 17)
      (.retV (.bool false) rvCmpContV) ch
      = .ok (tvHeadCfgV,
          vSt σ (vHeapTv n seed siv civ iv jv ls lt 0 true) 20, ch) := by
  with_unfolding_all rfl

/-! ### The test loop — the RELATIONAL check, two index reads -/

/-- Test first-pass dispatch. -/
theorem tv_A0_rawV (σ : ExecState) (n seed : Nat) (siv civ rif rjf : Int)
    (ls lt : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 25 (vSt σ (vHeapTv n seed siv civ rif rjf ls lt iv true) 20)
      tvHeadCfgV ch
      = .ok (.retV (.bool (decide (iv < (n : Int)))) tvCmpContV,
          vSt σ (vHeapTv n seed siv civ rif rjf ls lt iv false) 20, ch) := by
  with_unfolding_all rfl

/-- Test later-pass dispatch: `i++`, then the exit test. -/
theorem tv_A1_rawV (σ : ExecState) (n seed : Nat) (siv civ rif rjf : Int)
    (ls lt : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 29 (vSt σ (vHeapTv n seed siv civ rif rjf ls lt iv false) 20)
      tvHeadCfgV ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < (n : Int)))) tvCmpContV,
          vSt σ (vHeapTv n seed siv civ rif rjf ls lt
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false) 20, ch) := by
  with_unfolding_all rfl

/-- Test check phase 1: test true → the `s[i]` read apply. 11 steps. -/
theorem tv_B1_rawV (σ : ExecState) (n seed : Nat) (siv civ rif rjf : Int)
    (ls lt : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 11 (vSt σ (vHeapTv n seed siv civ rif rjf ls lt iv false) 20)
      (.retV (.bool true) tvCmpContV) ch
      = .ok (.retV (.int iv .uint64)
            (.strictK .indexGet [vSliceS n] [] tvEnvV2 tvNeqK1V),
          vSt σ (vHeapTv n seed siv civ rif rjf ls lt iv false) 20, ch) := by
  with_unfolding_all rfl

/-- Test check phase 2: `s[i]` banked → the ghost index `(n-1) - i`
computed in Go's wrapping uint64 arithmetic and the `t[...]` read at
its apply point. 13 steps. -/
theorem tv_B2_rawV (σ : ExecState) (n seed : Nat) (siv civ rif rjf : Int)
    (ls lt : List Int) (iv wv : Int) (ch : Choices) :
    stepFnIter 13 (vSt σ (vHeapTv n seed siv civ rif rjf ls lt iv false) 20)
      (.retV (.int wv .uint64) tvNeqK1V) ch
      = .ok (.retV (.int (IntKind.normalize .uint64
              (IntKind.normalize .uint64 ((n : Int) - 1) - iv)) .uint64)
            (.strictK .indexGet [vSliceT n] [] tvEnvV2
              (tvNeqK2V (.int wv .uint64))),
          vSt σ (vHeapTv n seed siv civ rif rjf ls lt iv false) 20, ch) := by
  with_unfolding_all rfl

/-- Test check phase 3: both elements banked → the `!=` delivered. -/
theorem tv_B3_rawV (σ : ExecState) (n seed : Nat) (siv civ rif rjf : Int)
    (ls lt : List Int) (iv wv uv : Int) (ch : Choices) :
    stepFnIter 1 (vSt σ (vHeapTv n seed siv civ rif rjf ls lt iv false) 20)
      (.retV (.int uv .uint64) (tvNeqK2V (.int wv .uint64))) ch
      = .ok (.retV (.bool (!(wv == uv))) tvIfKV,
          vSt σ (vHeapTv n seed siv civ rif rjf ls lt iv false) 20, ch) := by
  with_unfolding_all rfl

/-- Test check phase 4 (the EQUAL case): the else branch drains back to
the loop head, the verdict untouched. 5 steps. -/
theorem tv_B4_rawV (σ : ExecState) (n seed : Nat) (siv civ rif rjf : Int)
    (ls lt : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 5 (vSt σ (vHeapTv n seed siv civ rif rjf ls lt iv false) 20)
      (.retV (.bool false) tvIfKV) ch
      = .ok (tvHeadCfgV,
          vSt σ (vHeapTv n seed siv civ rif rjf ls lt iv false) 20, ch) := by
  with_unfolding_all rfl

/-- Test exit: verdict 1 to the result cell, return, barrier exit —
the driver terminal, terminal state pinned. 21 steps. -/
theorem tv_X_rawV (σ : ExecState) (n seed : Nat) (siv civ rif rjf : Int)
    (ls lt : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 21 (vSt σ (vHeapTv n seed siv civ rif rjf ls lt iv false) 20)
      (.retV (.bool false) tvCmpContV) ch
      = .ok (.next .stop,
          vSt σ (vHeapEnd n seed siv civ rif rjf ls lt iv) 20, ch) := by
  with_unfolding_all rfl

/-! ## The setup loop, cleaned + its induction -/

/-- One setup iteration from the exit test's true delivery at `m`:
fill `s[m] = seed + m` (wrapped), return to the head, dispatch, deliver
the next test — the family prefix advanced. 53 steps. -/
theorem su_iterV (σ : ExecState) (n seed : Nat) (m : Nat) (hn64 : n < 2 ^ 64)
    (hm : m < n) (ch : Choices) :
    stepFnIter 53
      (vSt σ (vHeapSu n seed (suList n seed m) ((m : Nat) : Int) false) 8)
      (.retV (.bool true) suCmpContV) ch
      = .ok (.retV (.bool (decide (((m + 1 : Nat) : Int) < (n : Int))))
            suCmpContV,
          vSt σ (vHeapSu n seed (suList n seed (m + 1))
            ((m + 1 : Nat) : Int) false) 8, ch) := by
  have hB1 := su_B1_rawV σ n seed (suList n seed m) ((m : Nat) : Int) ch
  rw [unorm_add_nat seed m] at hB1
  have hw : (0 : Int) ≤ (((seed + m) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + m) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + m) (y := 2 ^ 64) (by omega)
    omega
  have hst := storeTarget_slice_u64 (a := ⟨4⟩) (off := 0) (len := n)
    (cap := n) (i := m) (n := n) (ik := .uint64) (l := suList n seed m)
    (w := (((seed + m) % 2 ^ 64 : Nat) : Int))
    (lookup_suV σ n seed (suList n seed m) ((m : Nat) : Int) false 8)
    (Nat.le_refl _) hm (by rw [length_suList (by omega)]; omega)
    (length_suList (by omega)) (fun v hv => mem_suList hv) hw
  rw [Nat.zero_add, suList_set hm] at hst
  have hstore : storeTarget
      (vSt σ (vHeapSu n seed (suList n seed m) ((m : Nat) : Int) false) 8)
      (suRefV n ((m : Nat) : Int))
      (.int (((seed + m) % 2 ^ 64 : Nat) : Int) .uint64)
      = .ok (vSt σ (vHeapSu n seed (suList n seed (m + 1))
          ((m : Nat) : Int) false) 8) := hst
  have hD := su_D_rawV σ n seed (suList n seed (m + 1)) ((m : Nat) : Int) ch
  have hA1 := su_A1_rawV σ n seed (suList n seed (m + 1)) ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hB1
    (stepFnIter_one (stepFn_store_step hstore))) hD) hA1

/-- **The setup loop**: from the exit-test delivery at `m` the run
reaches the COPY LOOP HEAD with the full family in `s`'s backing and a
freshly zeroed `t`, within `53·μ + 58` steps. -/
theorem su_loopV (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 63) :
    ∀ μ m : Nat, m + μ = n → ∀ ch : Choices,
    ∃ k : Nat, k ≤ 53 * μ + 58 ∧
      stepFnIter k
        (vSt σ (vHeapSu n seed (suList n seed m) ((m : Nat) : Int) false) 8)
        (.retV (.bool (decide (((m : Nat) : Int) < (n : Int)))) suCmpContV) ch
        = .ok (cpHeadCfgV,
            vSt σ (vHeapCp n seed ((n : Nat) : Int) (revFamily n seed)
              (List.replicate n 0) 0 true) 13, ch) := by
  -- The P5 iterate-then-exit schema (`stepFnIter_iterate_exit`) at
  -- `su_iterV` + the exit tower; the `strongRecOn` boilerplate deleted
  -- (G0 item 3a P6 rollback). Statement unchanged.
  intro μ m hm ch
  have hexit : ∀ ch' : Choices, stepFnIter 58
      (vSt σ (vHeapSu n seed (suList n seed n) ((n : Nat) : Int) false) 8)
      (.retV (.bool (decide (((n : Nat) : Int) < (n : Int)))) suCmpContV) ch'
      = .ok (cpHeadCfgV,
          vSt σ (vHeapCp n seed ((n : Nat) : Int) (revFamily n seed)
            (List.replicate n 0) 0 true) 13, ch') := by
    intro ch'
    rw [show (decide (((n : Nat) : Int) < (n : Int))) = false from
      decide_eq_false (by omega)]
    have hX := su_X_rawV σ n seed (suList n seed n) ((n : Nat) : Int) ch'
    rw [suList_full] at hX
    have hmk := stepFnIter_one
      (stepFn_makeSliceV (env := [c6ScopeV, baseEnvV])
        (k := .seq [vS5, vS6, vS7, vS8, vS9, vS10] [c6ScopeV, baseEnvV]
          (.frame [] [] [] [] .stop))
        (vH_makeT_apply σ n seed (revFamily n seed) ((n : Nat) : Int) ch'))
    have hE := cp_E_rawV σ n seed (revFamily n seed) ((n : Nat) : Int) ch'
    rw [suList_full]
    exact stepFnIter_chain (stepFnIter_chain hX hmk) hE
  refine ⟨53 * (n - m) + 58, by omega, ?_⟩
  exact stepFnIter_iterate_exit (c := 53) (e := 58) (n := n)
    (T := fun j => vSt σ (vHeapSu n seed (suList n seed j)
      ((j : Nat) : Int) false) 8)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int) < (n : Int))))
      suCmpContV)
    (fun j hj ch'' => by
      rw [show (decide (((j : Nat) : Int) < (n : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact su_iterV σ n seed j (by omega) hj ch'')
    hexit m (by omega) ch

/-! ## The copy loop, cleaned + its induction

`t`'s backing after `m` copies is the SAME prefix shape the setup loop
built, because `t[i] = s[i]` copies exactly the family element that
loop wrote — so `suList` serves both invariants and nothing new is
needed on the pure side. -/

/-- One copy iteration from the exit test's true delivery at `m`:
read `s[m]`, store it into `t[m]`, return to the head, dispatch,
deliver the next test. 53 steps. -/
theorem cp_iterV (σ : ExecState) (n seed : Nat) (siv : Int) (m : Nat)
    (hn : n < 2 ^ 63) (hm : m < n) (ch : Choices) :
    stepFnIter 53
      (vSt σ (vHeapCp n seed siv (revFamily n seed) (suList n seed m)
        ((m : Nat) : Int) false) 13)
      (.retV (.bool true) cpCmpContV) ch
      = .ok (.retV (.bool (decide (((m + 1 : Nat) : Int) < (n : Int))))
            cpCmpContV,
          vSt σ (vHeapCp n seed siv (revFamily n seed)
            (suList n seed (m + 1)) ((m + 1 : Nat) : Int) false) 13, ch) := by
  have hlenF : (revFamily n seed).length = n := length_revFamily n seed
  have hB1 := cp_B1_rawV σ n seed siv (revFamily n seed) (suList n seed m)
    ((m : Nat) : Int) ch
  -- the s[m] read: the family's own element
  have hget : (⟨(revFamily n seed).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + m]?
      = some (.int (((seed + m) % 2 ^ 64 : Nat) : Int) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega), getD_revFamily hm]
  have hread := stepFn_strict_apply (done := [vSliceS n]) (env := cpEnvV2)
    (k := cpRhsKV n ((m : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .uint64)
      (lookup_cpS σ n seed siv (revFamily n seed) (suList n seed m)
        ((m : Nat) : Int) false 13)
      (Nat.le_refl n) hm hget)
  have hB2 := cp_B2_rawV σ n seed siv (revFamily n seed) (suList n seed m)
    ((m : Nat) : Int)
    (.int (((seed + m) % 2 ^ 64 : Nat) : Int) .uint64) ch
  -- the t[m] store
  have hw : (0 : Int) ≤ (((seed + m) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + m) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + m) (y := 2 ^ 64) (by omega)
    omega
  have hst := storeTarget_slice_u64 (a := ⟨9⟩) (off := 0) (len := n)
    (cap := n) (i := m) (n := n) (ik := .uint64) (l := suList n seed m)
    (w := (((seed + m) % 2 ^ 64 : Nat) : Int))
    (lookup_cpT σ n seed siv (revFamily n seed) (suList n seed m)
      ((m : Nat) : Int) false 13)
    (Nat.le_refl _) hm (by rw [length_suList (by omega)]; omega)
    (length_suList (by omega)) (fun v hv => mem_suList hv) hw
  rw [Nat.zero_add, suList_set hm] at hst
  have hstore : storeTarget
      (vSt σ (vHeapCp n seed siv (revFamily n seed) (suList n seed m)
        ((m : Nat) : Int) false) 13)
      (cpRefV n ((m : Nat) : Int))
      (.int (((seed + m) % 2 ^ 64 : Nat) : Int) .uint64)
      = .ok (vSt σ (vHeapCp n seed siv (revFamily n seed)
          (suList n seed (m + 1)) ((m : Nat) : Int) false) 13) := hst
  have hD := cp_D_rawV σ n seed siv (revFamily n seed) (suList n seed (m + 1))
    ((m : Nat) : Int) ch
  have hA1 := cp_A1_rawV σ n seed siv (revFamily n seed)
    (suList n seed (m + 1)) ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  have h1 := stepFnIter_chain hB1 (stepFnIter_one hread)
  have h2 := stepFnIter_chain h1 hB2
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hstore))
  exact stepFnIter_chain (stepFnIter_chain h3 hD) hA1

/-- **The copy loop**: from the exit-test delivery at `m` the run
reaches the REVERSE LOOP HEAD with the pre-copy complete in `t`, within
`53·μ + 53` steps. The base case crosses the one program-consulting
step, so it carries the `enterFrame` fact as a hypothesis. -/
theorem cp_loopV (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 63)
    (henter : ∀ (siv civ : Int) (ls lt : List Int),
      enterFrame (vSt σ (vHeapCp n seed siv ls lt civ false) 13)
          ⟨"reverse"⟩ [vSliceS n]
        = .ok (reverseFunc, [[("s", .base ⟨13⟩)]], [],
            vSt σ (vHeapRvFrame n seed siv civ ls lt) 14)) :
    ∀ μ m : Nat, m + μ = n → ∀ ch : Choices,
    ∃ k : Nat, k ≤ 53 * μ + 53 ∧
      stepFnIter k
        (vSt σ (vHeapCp n seed ((n : Nat) : Int) (revFamily n seed)
          (suList n seed m) ((m : Nat) : Int) false) 13)
        (.retV (.bool (decide (((m : Nat) : Int) < (n : Int)))) cpCmpContV) ch
        = .ok (rvHeadCfgV,
            vSt σ (vHeapRv n seed ((n : Nat) : Int) ((n : Nat) : Int)
              (revFamily n seed) (revFamily n seed) 0 ((n : Int) - 1) true)
              17, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hm ch
    rcases Nat.lt_or_ge m n with hlt | hge
    · rw [show (decide (((m : Nat) : Int) < (n : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      obtain ⟨k, hk, hrun⟩ := ih (μ - 1) (by omega) (m + 1) (by omega) ch
      exact ⟨53 + k, by omega,
        stepFnIter_chain (cp_iterV σ n seed ((n : Nat) : Int) m hn hlt ch)
          hrun⟩
    · have hmn : m = n := by omega
      subst hmn
      rw [show (decide (((m : Nat) : Int) < (m : Int))) = false from
        decide_eq_false (by omega)]
      have hX := cp_X_rawV σ m seed ((m : Nat) : Int) (revFamily m seed)
        (suList m seed m) ((m : Nat) : Int) ch
      rw [suList_full] at hX
      have hent := stepFnIter_one (ch := ch)
        (stepFn_call_enter (plans := []) (env := [tScopeV, baseEnvV])
          (k := rvAfterCallV) (vals := []) (v := vSliceS m)
          (henter ((m : Nat) : Int) ((m : Nat) : Int) (revFamily m seed)
            (revFamily m seed)))
      have hpre := rv_pre_rawV σ m seed ((m : Nat) : Int) ((m : Nat) : Int)
        (revFamily m seed) (revFamily m seed) ch
      have happ : applyStrictOp
          (vSt σ (vHeapRvEntry m seed ((m : Nat) : Int) ((m : Nat) : Int)
            (revFamily m seed) (revFamily m seed)) 16)
          (.lengthOf (some (.slice (.int .uint64)))) [vSliceS m]
          = .ok (.int (m : Nat) .int,
              vSt σ (vHeapRvEntry m seed ((m : Nat) : Int) ((m : Nat) : Int)
                (revFamily m seed) (revFamily m seed)) 16) :=
        applyStrictOp_len_slice (Nat.le_refl m)
      have hlen := stepFnIter_one (ch := ch) (stepFn_strict_apply
        (done := []) (env := rvEnvMidV)
        (k := .strictK .sub [] [.intLit 1 .int] rvEnvMidV rvEntryRhsKV) happ)
      have hY := rv_entry_rawV σ m seed ((m : Nat) : Int) ((m : Nat) : Int)
        (revFamily m seed) (revFamily m seed) ch
      rw [inorm_of_range (v := (m : Int) - 1) (by omega) (by omega),
        inorm_of_range (v := (m : Int) - 1) (by omega) (by omega)] at hY
      refine ⟨9 + 1 + 20 + 1 + 22, by omega, ?_⟩
      rw [suList_full]
      exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain hX hent) hpre) hlen) hY

/-! ## The reverse loop, cleaned + its induction (the `revSwap`
machinery of `Examples/Reverse.lean`, re-consumed at the v-layout) -/

/-- The reverse-phase exit-test delivery heap at iteration `m`. -/
abbrev vHeapRvCmp (n seed : Nat) (siv civ : Int) (m : Nat) : Heap :=
  vHeapRv n seed siv civ (revSwap (revFamily n seed) m) (revFamily n seed)
    ((m : Nat) : Int) ((n - 1 - m : Nat) : Int) false

/-- One swap at the v-layout: 35 steps from the true test back to the
head, the partial reversal advanced. -/
theorem rv_swap_segV (σ : ExecState) (n seed : Nat) (siv civ : Int)
    (m : Nat) (hm : 2 * m + 1 < n) (ch : Choices) :
    stepFnIter 35 (vSt σ (vHeapRvCmp n seed siv civ m) 17)
      (.retV (.bool true) rvCmpContV) ch
      = .ok (rvHeadCfgV,
          vSt σ (vHeapRv n seed siv civ (revSwap (revFamily n seed) (m + 1))
            (revFamily n seed) ((m : Nat) : Int) ((n - 1 - m : Nat) : Int)
            false) 17, ch) := by
  have hxs : ∀ v ∈ revFamily n seed, 0 ≤ v ∧ v < 2 ^ 64 :=
    fun v hv => mem_revFamily hv
  have hlenxs : (revFamily n seed).length = n := length_revFamily n seed
  have hlenm : (revSwap (revFamily n seed) m).length = n := by
    rw [length_revSwap, hlenxs]
  have hrangeSwap : ∀ v ∈ revSwap (revFamily n seed) m, 0 ≤ v ∧ v < 2 ^ 64 :=
    fun v hv => hxs v (mem_revSwap hv)
  have hwj_range :
      0 ≤ (revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0
      ∧ (revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0
          < 2 ^ 64 :=
    hxs _ (getD_mem (by omega))
  have hwi_range : 0 ≤ (revFamily n seed).getD m 0
      ∧ (revFamily n seed).getD m 0 < 2 ^ 64 :=
    hxs _ (getD_mem (by omega))
  have hA := rv_swapA_rawV σ n seed siv civ (revSwap (revFamily n seed) m)
    (revFamily n seed) ((m : Nat) : Int) ((n - 1 - m : Nat) : Int) ch
  have hget_j : (⟨(revSwap (revFamily n seed) m).map
      (fun v => .int v .uint64)⟩ : Array GoValue)[0 + (n - 1 - m)]?
      = some (.int ((revFamily n seed).getD
          ((revFamily n seed).length - 1 - m) 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega),
      show n - 1 - m = (revFamily n seed).length - 1 - m from by omega,
      getD_revSwap_hi (by omega)]
  have hread_j := stepFn_strict_apply (done := [vSliceS n])
    (env := rvEnvIn2V)
    (k := rvRhsK1V n ((m : Nat) : Int) ((n - 1 - m : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .int)
      (lookup_rvS σ n seed siv civ (revSwap (revFamily n seed) m)
        (revFamily n seed) ((m : Nat) : Int) ((n - 1 - m : Nat) : Int)
        false 17)
      (Nat.le_refl n) (by omega : n - 1 - m < n) hget_j)
  have hB := rv_swapB_rawV σ n seed siv civ (revSwap (revFamily n seed) m)
    (revFamily n seed) ((m : Nat) : Int) ((n - 1 - m : Nat) : Int)
    (.int ((revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0)
      .uint64) ch
  have hget_i : (⟨(revSwap (revFamily n seed) m).map
      (fun v => .int v .uint64)⟩ : Array GoValue)[0 + m]?
      = some (.int ((revFamily n seed).getD m 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega),
      getD_revSwap_lo (by omega)]
  have hread_i := stepFn_strict_apply (done := [vSliceS n])
    (env := rvEnvIn2V)
    (k := rvRhsK2V n ((m : Nat) : Int) ((n - 1 - m : Nat) : Int)
      (.int ((revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0)
        .uint64)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .int)
      (lookup_rvS σ n seed siv civ (revSwap (revFamily n seed) m)
        (revFamily n seed) ((m : Nat) : Int) ((n - 1 - m : Nat) : Int)
        false 17)
      (Nat.le_refl n) (by omega : m < n) hget_i)
  have hC := rv_swapC_rawV σ n seed siv civ (revSwap (revFamily n seed) m)
    (revFamily n seed) ((m : Nat) : Int) ((n - 1 - m : Nat) : Int)
    (.int ((revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0)
      .uint64)
    (.int ((revFamily n seed).getD m 0) .uint64) ch
  have hst1 := storeTarget_slice_u64 (a := ⟨4⟩) (off := 0) (len := n)
    (cap := n) (i := m) (n := n) (ik := .int)
    (l := revSwap (revFamily n seed) m)
    (w := (revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0)
    (lookup_rvS σ n seed siv civ (revSwap (revFamily n seed) m)
      (revFamily n seed) ((m : Nat) : Int) ((n - 1 - m : Nat) : Int) false 17)
    (Nat.le_refl _) (by omega) (by omega) hlenm hrangeSwap hwj_range
  rw [Nat.zero_add] at hst1
  have hstore1 : storeTarget (vSt σ (vHeapRvCmp n seed siv civ m) 17)
      (rvRefV n ((m : Nat) : Int))
      (.int ((revFamily n seed).getD
        ((revFamily n seed).length - 1 - m) 0) .uint64)
      = .ok (vSt σ (vHeapRv n seed siv civ
          ((revSwap (revFamily n seed) m).set m
            ((revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0))
          (revFamily n seed) ((m : Nat) : Int) ((n - 1 - m : Nat) : Int)
          false) 17) := hst1
  have hlen1 : ((revSwap (revFamily n seed) m).set m
      ((revFamily n seed).getD
        ((revFamily n seed).length - 1 - m) 0)).length = n := by simp [hlenm]
  have hrange1 : ∀ v ∈ (revSwap (revFamily n seed) m).set m
      ((revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0),
      0 ≤ v ∧ v < 2 ^ 64 := by
    intro v hv
    rcases mem_set_of_mem hv with rfl | hv
    · exact hwj_range
    · exact hrangeSwap v hv
  have hst2 := storeTarget_slice_u64 (a := ⟨4⟩) (off := 0) (len := n)
    (cap := n) (i := n - 1 - m) (n := n) (ik := .int)
    (l := (revSwap (revFamily n seed) m).set m
      ((revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0))
    (w := (revFamily n seed).getD m 0)
    (lookup_rvS σ n seed siv civ
      ((revSwap (revFamily n seed) m).set m
        ((revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0))
      (revFamily n seed) ((m : Nat) : Int) ((n - 1 - m : Nat) : Int) false 17)
    (Nat.le_refl _) (by omega) (by omega) hlen1 hrange1 hwi_range
  rw [Nat.zero_add] at hst2
  have hstore2 : storeTarget
      (vSt σ (vHeapRv n seed siv civ
        ((revSwap (revFamily n seed) m).set m
          ((revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0))
        (revFamily n seed) ((m : Nat) : Int) ((n - 1 - m : Nat) : Int)
        false) 17)
      (rvRefV n ((n - 1 - m : Nat) : Int))
      (.int ((revFamily n seed).getD m 0) .uint64)
      = .ok (vSt σ (vHeapRv n seed siv civ
          (revSwap (revFamily n seed) (m + 1)) (revFamily n seed)
          ((m : Nat) : Int) ((n - 1 - m : Nat) : Int) false) 17) := by
    rw [show n - 1 - m = (revFamily n seed).length - 1 - m from by omega]
      at hst2 ⊢
    rw [← revSwap_step (by omega)]
    exact hst2
  have hD := rv_swapD_rawV σ n seed siv civ
    (revSwap (revFamily n seed) (m + 1)) (revFamily n seed)
    ((m : Nat) : Int) ((n - 1 - m : Nat) : Int) ch
  have h1 := stepFnIter_chain hA (stepFnIter_one hread_j)
  have h2 := stepFnIter_chain h1 hB
  have h3 := stepFnIter_chain h2 (stepFnIter_one hread_i)
  have h4 := stepFnIter_chain h3 hC
  have h5 := stepFnIter_chain h4 (stepFnIter_one (stepFn_store_step hstore1))
  have h6 := stepFnIter_chain h5 (stepFnIter_one (stepFn_store_step hstore2))
  exact stepFnIter_chain h6 hD

/-- The later-pass dispatch, cleaned: counters advance to
`(m+1, n-1-(m+1))` and the next test delivers. 40 steps. -/
theorem rv_dispatchV (σ : ExecState) (n seed : Nat) (siv civ : Int)
    (m : Nat) (hn : n < 2 ^ 63) (hm : 2 * m + 1 < n) (ch : Choices) :
    stepFnIter 40
      (vSt σ (vHeapRv n seed siv civ (revSwap (revFamily n seed) (m + 1))
        (revFamily n seed) ((m : Nat) : Int) ((n - 1 - m : Nat) : Int) false)
        17) rvHeadCfgV ch
      = .ok (.retV (.bool (decide (((m + 1 : Nat) : Int)
              < ((n - 1 - (m + 1) : Nat) : Int)))) rvCmpContV,
          vSt σ (vHeapRvCmp n seed siv civ (m + 1)) 17, ch) := by
  have hA := rv_A1_rawV σ n seed siv civ (revSwap (revFamily n seed) (m + 1))
    (revFamily n seed) ((m : Nat) : Int) ((n - 1 - m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    show ((n - 1 - m : Nat) : Int) - 1
      = ((n - 1 - (m + 1) : Nat) : Int) from by omega] at hA
  rw [inorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    inorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    inorm_of_range (v := ((n - 1 - (m + 1) : Nat) : Int))
      (by omega) (by omega),
    inorm_of_range (v := ((n - 1 - (m + 1) : Nat) : Int))
      (by omega) (by omega)] at hA
  exact hA

/-- **The reverse loop**, by strong induction on `(n-1) - 2m` (which
drops by 2 per iteration, so the bound counts SWAPS, not units of the
measure): from the exit-test delivery at `m` the run reaches the TEST
LOOP HEAD — reversal complete in `s`, pre-copy intact in `t`, verdict
cell initialized to 1 — within `75·⌊(μ+1)/2⌋ + 50` steps. -/
theorem rv_loopV (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 63)
    (siv civ : Int) :
    ∀ μ m : Nat, μ = (n - 1) - 2 * m → ∀ ch : Choices,
    ∃ (k m' : Nat), k ≤ 75 * ((μ + 1) / 2) + 50 ∧ n ≤ 2 * m' + 1 ∧
      stepFnIter k (vSt σ (vHeapRvCmp n seed siv civ m) 17)
        (.retV (.bool (decide (((m : Nat) : Int)
          < ((n - 1 - m : Nat) : Int)))) rvCmpContV) ch
        = .ok (tvHeadCfgV,
            vSt σ (vHeapTv n seed siv civ ((m' : Nat) : Int)
              ((n - 1 - m' : Nat) : Int) (revSwap (revFamily n seed) m')
              (revFamily n seed) 0 true) 20, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hμ ch
    rcases Nat.lt_or_ge (2 * m + 1) n with hlt | hge
    · rw [show (decide (((m : Nat) : Int) < ((n - 1 - m : Nat) : Int)))
          = true from decide_eq_true (by
            have : m < n - 1 - m := by omega
            exact_mod_cast this)]
      obtain ⟨k, m', hk, hm', hrun⟩ := ih ((n - 1) - 2 * (m + 1))
        (by omega) (m + 1) rfl ch
      refine ⟨35 + 40 + k, m', by omega, hm', ?_⟩
      exact stepFnIter_chain
        (stepFnIter_chain (rv_swap_segV σ n seed siv civ m hlt ch)
          (rv_dispatchV σ n seed siv civ m hn hlt ch)) hrun
    · rw [show (decide (((m : Nat) : Int) < ((n - 1 - m : Nat) : Int)))
          = false from decide_eq_false (by
            have : ¬ (m < n - 1 - m) := by omega
            exact_mod_cast this)]
      exact ⟨50, m, by omega, by omega,
        rv_X_rawV σ n seed siv civ (revSwap (revFamily n seed) m)
          (revFamily n seed) ((m : Nat) : Int) ((n - 1 - m : Nat) : Int) ch⟩

/-! ## The test loop: the RELATIONAL check, verified read against read -/

/-- One test iteration from the exit test's true delivery at `m`: read
`s[m]` (the reversed family), compute the ghost index `(n-1)-m` in Go's
wrapping uint64 arithmetic, read `t[(n-1)-m]` (the PRE-COPY), find them
EQUAL — so the verdict stays 1 — return to the head, dispatch, deliver
the next test. 61 steps. This is the whole payoff of the copy-relational
style: the machine compares two reads, and the proof's obligation is
that the reversal relation holds between them, not that the check's
arithmetic re-derives the setup formula. -/
theorem tv_iterV (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 63)
    (siv civ rif rjf : Int) (m : Nat) (hm : m < n) (ch : Choices) :
    stepFnIter 61
      (vSt σ (vHeapTv n seed siv civ rif rjf ((revFamily n seed).reverse)
        (revFamily n seed) ((m : Nat) : Int) false) 20)
      (.retV (.bool true) tvCmpContV) ch
      = .ok (.retV (.bool (decide (((m + 1 : Nat) : Int) < (n : Int))))
            tvCmpContV,
          vSt σ (vHeapTv n seed siv civ rif rjf ((revFamily n seed).reverse)
            (revFamily n seed) ((m + 1 : Nat) : Int) false) 20, ch) := by
  have hlenF : (revFamily n seed).length = n := length_revFamily n seed
  have hB1 := tv_B1_rawV σ n seed siv civ rif rjf
    ((revFamily n seed).reverse) (revFamily n seed) ((m : Nat) : Int) ch
  -- read 1: s[m], the reversed family's element
  have hget1 : (⟨((revFamily n seed).reverse).map
      (fun v => .int v .uint64)⟩ : Array GoValue)[0 + m]?
      = some (.int ((((seed + (n - 1 - m)) % 2 ^ 64 : Nat)) : Int)
          .uint64) := by
    rw [Nat.zero_add,
      getElem?_mapU _ _ (by rw [List.length_reverse, hlenF]; omega),
      getD_reverse_revFamily hm]
  have hread1 := stepFn_strict_apply (done := [vSliceS n]) (env := tvEnvV2)
    (k := tvNeqK1V) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .uint64)
      (lookup_tvS σ n seed siv civ rif rjf ((revFamily n seed).reverse)
        (revFamily n seed) ((m : Nat) : Int) false 20)
      (Nat.le_refl n) hm hget1)
  have hB2 := tv_B2_rawV σ n seed siv civ rif rjf
    ((revFamily n seed).reverse) (revFamily n seed) ((m : Nat) : Int)
    ((((seed + (n - 1 - m)) % 2 ^ 64 : Nat)) : Int) ch
  -- the ghost index reduces to the Nat cast `n - 1 - m`
  rw [show IntKind.normalize .uint64 ((n : Int) - 1)
        = ((n - 1 : Nat) : Int) from by
      rw [show (n : Int) - 1 = ((n - 1 : Nat) : Int) from by omega]
      exact unorm_of_range (by omega) (by omega),
    show IntKind.normalize .uint64 (((n - 1 : Nat) : Int) - ((m : Nat) : Int))
        = ((n - 1 - m : Nat) : Int) from by
      rw [show ((n - 1 : Nat) : Int) - ((m : Nat) : Int)
          = ((n - 1 - m : Nat) : Int) from by omega]
      exact unorm_of_range (by omega) (by omega)] at hB2
  -- read 2: t[n-1-m], the PRE-COPY's element
  have hget2 : (⟨(revFamily n seed).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + (n - 1 - m)]?
      = some (.int ((((seed + (n - 1 - m)) % 2 ^ 64 : Nat)) : Int)
          .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega),
      getD_revFamily (by omega : n - 1 - m < n)]
  have hread2 := stepFn_strict_apply (done := [vSliceT n]) (env := tvEnvV2)
    (k := tvNeqK2V
      (.int ((((seed + (n - 1 - m)) % 2 ^ 64 : Nat)) : Int) .uint64))
    (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .uint64)
      (lookup_tvT σ n seed siv civ rif rjf ((revFamily n seed).reverse)
        (revFamily n seed) ((m : Nat) : Int) false 20)
      (Nat.le_refl n) (by omega : n - 1 - m < n) hget2)
  have hB3 := tv_B3_rawV σ n seed siv civ rif rjf
    ((revFamily n seed).reverse) (revFamily n seed) ((m : Nat) : Int)
    ((((seed + (n - 1 - m)) % 2 ^ 64 : Nat)) : Int)
    ((((seed + (n - 1 - m)) % 2 ^ 64 : Nat)) : Int) ch
  rw [show ((((seed + (n - 1 - m)) % 2 ^ 64 : Nat) : Int) ==
      (((seed + (n - 1 - m)) % 2 ^ 64 : Nat) : Int)) = true from
    beq_self_eq_true _, Bool.not_true] at hB3
  have hB4 := tv_B4_rawV σ n seed siv civ rif rjf
    ((revFamily n seed).reverse) (revFamily n seed) ((m : Nat) : Int) ch
  have hA1 := tv_A1_rawV σ n seed siv civ rif rjf
    ((revFamily n seed).reverse) (revFamily n seed) ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  have h1 := stepFnIter_chain hB1 (stepFnIter_one hread1)
  have h2 := stepFnIter_chain h1 hB2
  have h3 := stepFnIter_chain h2 (stepFnIter_one hread2)
  have h4 := stepFnIter_chain h3 hB3
  have h5 := stepFnIter_chain h4 hB4
  exact stepFnIter_chain h5 hA1

/-- **The test loop**: from the exit-test delivery at `m` the run
reaches the driver terminal with the verdict 1 delivered, within
`61·μ + 21` steps. -/
theorem tv_loopV (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 63)
    (siv civ rif rjf : Int) :
    ∀ μ m : Nat, m + μ = n → ∀ ch : Choices,
    ∃ k : Nat, k ≤ 61 * μ + 21 ∧
      stepFnIter k
        (vSt σ (vHeapTv n seed siv civ rif rjf ((revFamily n seed).reverse)
          (revFamily n seed) ((m : Nat) : Int) false) 20)
        (.retV (.bool (decide (((m : Nat) : Int) < (n : Int)))) tvCmpContV) ch
        = .ok (.next .stop,
            vSt σ (vHeapEnd n seed siv civ rif rjf
              ((revFamily n seed).reverse) (revFamily n seed)
              ((n : Nat) : Int)) 20, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hm ch
    rcases Nat.lt_or_ge m n with hlt | hge
    · rw [show (decide (((m : Nat) : Int) < (n : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      obtain ⟨k, hk, hrun⟩ := ih (μ - 1) (by omega) (m + 1) (by omega) ch
      exact ⟨61 + k, by omega, stepFnIter_chain
        (tv_iterV σ n seed hn siv civ rif rjf m hlt ch) hrun⟩
    · have hmn : m = n := by omega
      subst hmn
      rw [show (decide (((m : Nat) : Int) < (m : Int))) = false from
        decide_eq_false (by omega)]
      exact ⟨21, by omega, tv_X_rawV σ m seed siv civ rif rjf
        ((revFamily m seed).reverse) (revFamily m seed)
        ((m : Nat) : Int) ch⟩

/-! ## The run, end to end -/

/-- **The harness run, PROGRAM-generic**: the only fact about the
pinned program is the `enterFrame` hypothesis. Within `205·n + 335`
steps the harness reaches the driver terminal with the verdict 1 in the
result cell (the terminal state is pinned up to `reverse`'s parked
final counters). -/
theorem vH_runs_generic (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 63)
    (henter : ∀ (siv civ : Int) (ls lt : List Int),
      enterFrame (vSt σ (vHeapCp n seed siv ls lt civ false) 13)
          ⟨"reverse"⟩ [vSliceS n]
        = .ok (reverseFunc, [[("s", .base ⟨13⟩)]], [],
            vSt σ (vHeapRvFrame n seed siv civ ls lt) 14))
    (ch : Choices) :
    ∃ (k : Nat) (rif rjf : Int), k ≤ 205 * n + 335 ∧
      stepFnIter k (vSt σ (vHeap0 (n : Int) (seed : Int)) 3) vHC₀ ch
        = .ok (.next .stop,
            vSt σ (vHeapEnd n seed ((n : Nat) : Int) ((n : Nat) : Int)
              rif rjf ((revFamily n seed).reverse) (revFamily n seed)
              ((n : Nat) : Int)) 20, ch) := by
  -- entry → the setup loop's first test
  have hE1 := vH_E1_raw σ n seed ch
  have hmk := stepFnIter_one
    (stepFn_makeSliceV (env := envC5V)
      (k := .seq [vS2, vS3, vS4, vS5, vS6, vS7, vS8, vS9, vS10] envC5V
        (.frame [] [] [] [] .stop))
      (vH_makeS_apply σ n seed ch))
  have hE2 := vH_E2_raw σ n seed ch
  have hA0 := su_A0_rawV σ n seed (List.replicate n 0) 0 ch
  obtain ⟨k1, hk1, hsu⟩ := su_loopV σ n seed hn n 0 (by omega) ch
  rw [suList_zero, show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hsu
  have hentry := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hE1 hmk) hE2) hA0) hsu
  -- the copy loop
  have hcA0 := cp_A0_rawV σ n seed ((n : Nat) : Int) (revFamily n seed)
    (List.replicate n 0) 0 ch
  obtain ⟨k2, hk2, hcp⟩ := cp_loopV σ n seed hn henter n 0 (by omega) ch
  rw [suList_zero, show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hcp
  have hthruCopy := stepFnIter_chain (stepFnIter_chain hentry hcA0) hcp
  -- the reverse phase's first test
  have hrA0 := rv_A0_rawV σ n seed ((n : Nat) : Int) ((n : Nat) : Int)
    (revFamily n seed) (revFamily n seed) 0 ((n : Int) - 1) ch
  rcases Nat.lt_or_ge n 2 with hshort | hlong
  · -- n ≤ 1: the first test fails; nothing swaps, and the family is its
    -- own reversal
    rw [show (decide ((0 : Int) < (n : Int) - 1)) = false from
      decide_eq_false (by omega)] at hrA0
    have hX := rv_X_rawV σ n seed ((n : Nat) : Int) ((n : Nat) : Int)
      (revFamily n seed) (revFamily n seed) 0 ((n : Int) - 1) ch
    have hrevshort : (revFamily n seed).reverse = revFamily n seed :=
      reverse_short (by rw [length_revFamily]; omega)
    have htA0 := tv_A0_rawV σ n seed ((n : Nat) : Int) ((n : Nat) : Int)
      0 ((n : Int) - 1) (revFamily n seed) (revFamily n seed) 0 ch
    obtain ⟨k3, hk3, htv⟩ := tv_loopV σ n seed hn ((n : Nat) : Int)
      ((n : Nat) : Int) 0 ((n : Int) - 1) n 0 (by omega) ch
    rw [hrevshort, show (((0 : Nat) : Int)) = (0 : Int) from rfl] at htv
    refine ⟨10 + 1 + 42 + 25 + k1 + 25 + k2 + (25 + 50 + 25 + k3),
      0, (n : Int) - 1, by omega, ?_⟩
    rw [hrevshort]
    exact stepFnIter_chain hthruCopy (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain hrA0 hX) htA0) htv)
  · -- n ≥ 2: enter the two-pointer loop at iteration 0
    rw [show (decide ((0 : Int) < (n : Int) - 1)) = true from
      decide_eq_true (by omega)] at hrA0
    obtain ⟨k3, m', hk3, hm', hrv⟩ := rv_loopV σ n seed hn
      ((n : Nat) : Int) ((n : Nat) : Int) ((n - 1) - 2 * 0) 0 rfl ch
    simp only [vHeapRvCmp] at hrv
    rw [show revSwap (revFamily n seed) 0 = revFamily n seed from
        revSwap_zero _,
      show (((0 : Nat) : Int)) = (0 : Int) from rfl,
      show ((n - 1 - 0 : Nat) : Int) = (n : Int) - 1 from by omega,
      show (decide ((0 : Int) < (n : Int) - 1)) = true from
        decide_eq_true (by omega)] at hrv
    have hrev := stepFnIter_chain hrA0 hrv
    rw [revSwap_reverse (by rw [length_revFamily]; omega)] at hrev
    have htA0 := tv_A0_rawV σ n seed ((n : Nat) : Int) ((n : Nat) : Int)
      ((m' : Nat) : Int) ((n - 1 - m' : Nat) : Int)
      ((revFamily n seed).reverse) (revFamily n seed) 0 ch
    obtain ⟨k4, hk4, htv⟩ := tv_loopV σ n seed hn ((n : Nat) : Int)
      ((n : Nat) : Int) ((m' : Nat) : Int) ((n - 1 - m' : Nat) : Int)
      n 0 (by omega) ch
    rw [show (((0 : Nat) : Int)) = (0 : Int) from rfl] at htv
    refine ⟨10 + 1 + 42 + 25 + k1 + 25 + k2 + (25 + k3 + 25 + k4),
      ((m' : Nat) : Int), ((n - 1 - m' : Nat) : Int), by omega, ?_⟩
    exact stepFnIter_chain hthruCopy (stepFnIter_chain (stepFnIter_chain
      hrev htA0) htv)

/-- The `enterFrame` discharge at the pinned program: the SECOND and
last unfolding of `reverseLowered` in this module (`reverse` is the
funcs array's head, so the scan stops immediately). -/
theorem vH_enterFrame_fact (n seed : Nat) (siv civ : Int)
    (ls lt : List Int) :
    enterFrame (vSt vProg (vHeapCp n seed siv ls lt civ false) 13)
        ⟨"reverse"⟩ [vSliceS n]
      = .ok (reverseFunc, [[("s", .base ⟨13⟩)]], [],
          vSt vProg (vHeapRvFrame n seed siv civ ls lt) 14) := by
  with_unfolding_all rfl

/-! ## The user-facing statement -/

/-- **THE HEADLINE (§11 harness form, S1 COPY-RELATIONAL)**: for every
`n < 2^63` (Go's `int` domain for lengths — `make([]uint64, n)` panics
past it) and every `seed < 2^64` (the full uint64 domain), running the
Go harness `reverse_harness_v(n, seed)` through the machine's native
function entry — empty-heap state, both arguments at the call
boundary — completes normally past one fuel bound, at every
nondeterminism-choice stream, and RETURNS the verdict 1: the test
phase, IN GO and inside the verified footprint, compared `s[i]` against
the SAVED PRE-COPY `t[n-1-i]` element-wise and found every pair equal,
which is the reversal relation itself.

INPUT-FAMILY HONESTY (§11, recorded): the quantification is over the
scalars `(n, seed)` — i.e. over the input family `revFamily n seed =
[seed, seed+1, …, seed+(n-1)] (mod 2^64)`, honestly WEAKER than ∀xs
over arbitrary slice contents (the choice-consuming input pick is
designed, not built). The ∀xs claim remains available proof-side as
`reverse_framed`. What the copy-relational swap buys is a different
axis: the CHECK no longer encodes the family, so this is the
annotation-ready form — at ghost rung 1, annotating the one setup
assignment makes the input ∀-data with the SAME test phase, which the
`reverse_ok_v1` harness could never do because its check re-derives
`seed+(n-1-i)`.

The wrapping family is deliberate: `seed + i` wraps at `2^64`, so the
family covers wrap boundaries — the corpus rows
(`examples/reverse/harness-v-{five,empty,wrapping}`) exercise the same
harness against `go run` at concrete arguments including a
near-`2^63` seed. -/
theorem reverse_ok (n seed : Nat) (hn : n < 2 ^ 63) (hseed : seed < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel reverseLowered.typeDefs.toList
          reverseLowered.funcs reverseHarnessVFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
          reverseLowered.methods ch
        = .ok { values := #[.int 1 .uint64] } := by
  refine ⟨205 * n + 335, fun fuel hfuel ch => ?_⟩
  obtain ⟨k, rif, rjf, hk, hrun⟩ :=
    vH_runs_generic vProg n seed hn (vH_enterFrame_fact n seed) ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  -- the recorded show-bridge (structural: record updates of vProg)
  have hst : vHSeed ((n : Nat) : Int) ((seed : Nat) : Int)
      = vSt vProg (vHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)) 3 := rfl
  rw [revHV_entry_eq, unorm_of_range (v := (n : Int)) (by omega) (by omega),
    unorm_of_range (v := (seed : Int)) (by omega) (by omega),
    hst, hfold, runConfig_next_stop]
  with_unfolding_all rfl

/-- **The D1 run-conditioned twin**: any successful completion of the
harness entry, at any fuel and any choice stream, returns the verdict
1 — derived from `reverse_ok` via `harness_readout_of_total`. -/
theorem reverse_readout (n seed : Nat) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) :
    ∀ (fuel : Nat) (ch : Choices) (r : Result),
      runFunctionWithContextM fuel reverseLowered.typeDefs.toList
          reverseLowered.funcs reverseHarnessVFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
          reverseLowered.methods ch
        = .ok r →
      r = { values := #[.int 1 .uint64] } :=
  harness_readout_of_total (reverse_ok n seed hn hseed)

end GoLean.Examples.Reverse
