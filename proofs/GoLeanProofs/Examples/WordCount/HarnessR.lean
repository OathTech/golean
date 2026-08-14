import GoLeanProofs.Examples.WordCount
import GoLeanProofs.Examples.Targets

/-!
# WordCount — the S3 RELATIONAL harness (`wordcount_harness_r`)

Examples phase-2, slice 1, swap 3 of 3 (2026-08-14; slice record
`docs/2026-08-14_phase2-slice1-spec-swaps.md`, scoping study
`docs/2026-08-14_harness-style-scoping.md` §4.7). The user-facing
headline `wordcount_ok` now states the RELATIONAL harness: the Go
returns the WORDS it counted alongside the subject's answer, so the
Lean postcondition relates the RETURNED DATA directly —
`best = maxMultiplicity words` — with no family function re-describing
the setup inside the claim. `wcFamily` leaves the statement (it
survives only as the existential's witness, in the proof), and the
closed form `wcFamily_maxMult : maxMultiplicity (wcFamily n seed)
= (n+2)/3` is deliberately NOT used: that is the whole point of the
swap.

The previous headline over `wordcount_harness` — the returned scalar
compared against the closed form `⌈n/3⌉`, i.e. with the family AND its
solved value in the statement — is KEPT in `Examples/WordCount.lean` as
`wordcount_ok_v1` / `wordcount_readout_v1`, with its corpus rows.

## What the ∀-choices quantifier means here, and why it is honest

`for _, c := range counts` consumes one `Choices` pick per iteration, so
the headline quantifies over EVERY map-iteration order. The claim holds
at all of them precisely because `maxMultiplicity` is ORDER-INVARIANT
(a max-fold over multiplicities, which do not depend on order). That is
load-bearing for reading the statement: "the returned count is the max
multiplicity of the returned words" says what a reader thinks it says
ONLY because the spec function cannot see the order the machine chose.
A spec naming "the first key with maximal count" would be unprovable
here — and that unprovability would be the envelope working.

## The bounded cap is the honest cost of this style

Go's pass-by-value fragment cannot return unbounded data, so the
harness returns a FIXED-CAP `[8]uint64` and the theorem carries
`hcap : n ≤ 8`. That is a toy bound, stated plainly rather than hidden:
the cap is visible in the corpus Go as `const wordcountCapN = 8`, and
the copy loop plus zero-padding exist only so the counted words can
cross the observation boundary. Note that unlike minmax this harness
needs NO `1 ≤ n` — `maxCount` of an empty slice returns 0 rather than
panicking (corpus row `examples/wordcount/harness-r-empty`).

## Cost shape and genericity

Same discipline as `Examples/Reverse/HarnessV.lean` and
`Examples/MinMax/HarnessR.lean`: every raw segment is PROGRAM-generic
(`wSt σ H na` — abstract `σ`, only heap/nextAddr pinned), and the one
step that consults the program (the `maxCount(w)` frame entry) is
conditioned through `StepKit.stepFn_call_enter`. The pinned program is
unfolded exactly twice: the lowering pin and that one `enterFrame`
discharge. This matters more here than anywhere else in the repo —
`EmptyRun`'s 50.8 GiB blocker (slice 1.5) was exactly the cost of NOT
doing it.

The counting and range phases are INSTANTIATIONS of the
placement-generic layers `wcIter_generic` / `wcLoop_generic`
(`CountGeneric`) and `wcRange_generic` (`RangeGeneric`) — the same
layers the canonical and `wordcount_harness` placements instantiate.
Only the addresses change.

Address layout (probe-measured; `nextAddr = 20` at the subject's
counting head, growing during the counting and range loops):
0 = `n`, 1 = `seed`, 2 = `$res0` (`[8]uint64`), 3 = `$res1`,
4 = `$c11` (handle), 5 = backing, 6 = `w`, 7 = setup `i`,
8 = setup flag, 9 = `words` (`[8]uint64`), 10 = copy `i`,
11 = copy flag, 12 = `best`, 13 = `maxCount`'s `words` param,
14 = its `$res0`, 15 = `$c0`, 16 = the map DATA cell, 17 = `counts`,
18 = the counting counter, 19 = its flag; base0 = 20.
-/

namespace GoLean.Examples.WordCount

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- The PROGRAM-generic state form (the reverse/minmax modules' `vSt`
/ `rSt`). -/
abbrev wSt (σ : ExecState) (H : Heap) (na : Nat) : ExecState :=
  { σ with heap := H, nextAddr := na }

/-! ## The S3 statement adapter

`goArr8` is STATEMENT vocabulary: it is what "the returned
`[wordcountCapN]uint64`" means as a `GoValue`. Under the §11 closure
rules it is never a proof-kit definition, and it stays deliberately NOT
shared with the identically shaped `MinMax.goArr8` — unifying them would
change what these statements say. It was introduced in this module until
the 2026-08-14 designation moved it, unchanged and still a separate def
in its own namespace, to the def-only `Examples/Targets.lean` that the
Comparator Challenge's trusted closure imports. -/

-- HOISTED to `GoLeanProofs/Examples/Targets.lean` (designation, 2026-08-14):
-- `goArr8` is statement vocabulary of a DESIGNATED gallery headline, so it must
-- live in a def-only module inside the Comparator Challenge's trusted import
-- closure. The definition is unchanged and still visible here via the import.

/-! ## Extra pure facts -/

-- (`wcFamily_take`, the prefix-closure fact, was DELETED in the
-- 2026-08-15 audit response: it had zero consumers — the copy-loop
-- induction carries `wcPre` instead — and an unused lemma in a proof
-- module is a maintenance surface, not a fact anyone reads.)

/-- The family's element at an in-range index. -/
theorem wcFamily_getD {n seed m : Nat} (hm : m < n) :
    (wcFamily n seed).getD m 0 = (((seed + m % 3) % 2 ^ 64 : Nat) : Int) := by
  rw [wcFamily, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using hm)]
  simp

/-- The `words` array after `m` copy steps: the family prefix, the rest
still the array's zero default. -/
def wcPre (m seed : Nat) : List Int :=
  wcFamily m seed ++ List.replicate (8 - m) 0

theorem wcPre_zero (seed : Nat) : wcPre 0 seed = List.replicate 8 0 := by
  simp [wcPre, wcFamily]

theorem wcPre_length {m seed : Nat} (h : m ≤ 8) :
    (wcPre m seed).length = 8 := by
  rw [wcPre, List.length_append, wcFamily_length, List.length_replicate]
  omega

theorem wcPre_range {m seed : Nat} :
    ∀ v ∈ wcPre m seed, 0 ≤ v ∧ v < 2 ^ 64 := wcFamilyZ_range

theorem wcPre_set {seed m : Nat} (hm : m < 8) :
    (wcPre m seed).set m (((seed + m % 3) % 2 ^ 64 : Nat) : Int)
      = wcPre (m + 1) seed := wcFamily_set hm

/-- The copy loop's terminal list IS `goArr8`'s content at the family:
`wcFamily_length` is what makes `8 - (wcFamily n seed).length` reduce
to `8 - n`. -/
theorem wcPre_full {n seed : Nat} :
    wcPre n seed
      = wcFamily n seed ++ List.replicate (8 - (wcFamily n seed).length) 0 := by
  rw [wcPre, wcFamily_length]

/-! ## Cells and handles at the r-layout -/

abbrev rSliceW (n : Nat) : GoValue := .slice ⟨some (.base ⟨5⟩), 0, n, n⟩
abbrev rHandleW (n : Nat) : HeapCell := ⟨some (.slice tU64), rSliceW n⟩
abbrev rNilSlice : HeapCell :=
  ⟨some (.slice tU64), .slice ⟨none, 0, 0, 0⟩⟩
abbrev mhCellR : HeapCell := ⟨some tMap, .map ⟨some (.base ⟨16⟩)⟩⟩
abbrev zeros8 : List Int := List.replicate 8 0

/-! ## The harness `Func`, verbatim from the pinned lowering -/

-- HOISTED to `GoLeanProofs/Examples/Targets.lean` (designation, 2026-08-14):
-- `wcHarnessRFunc` is statement vocabulary of a DESIGNATED gallery headline, so it must
-- live in a def-only module inside the Comparator Challenge's trusted import
-- closure. The definition is unchanged and still visible here via the import.

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem wordcountHarnessR_pin :
    findFunctionIn? wordCountLowered.funcs ⟨"wordcount_harness_r"⟩
    = some wcHarnessRFunc := rfl

/-! ## Statement pieces, environments, continuations -/

def rS2 : Stmt :=
  .seqn #[.initialization { id := "w", typ := .slice (.int .uint64) },
          .assign (.var "w") (.var "$c11")]
def rS3 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .uint64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) wordcountHarnessFunc.suBody]]
def rS4 : Stmt :=
  .seqn #[.initialization { id := "words", typ := .array 8 (.int .uint64) }]
def rS5 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .uint64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) wcHarnessRFunc.cpBody]]
def rS6 : Stmt :=
  .seqn #[.initialization { id := "best", typ := .int .uint64 },
          .call #[.var "best"] ⟨"maxCount"⟩ #[.var "w"]]
def rS7 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "words"),
          .assign (.var "$res1") (.var "best"),
          .returnStmt]

def baseEnvR : Scope :=
  [("$res1", .base ⟨3⟩), ("$res0", .base ⟨2⟩),
   ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]
def envC11R : LocalEnv := [[("$c11", .base ⟨4⟩)], baseEnvR]
def wScopeR : Scope := [("w", .base ⟨6⟩), ("$c11", .base ⟨4⟩)]
def wordsScopeR : Scope :=
  [("words", .base ⟨9⟩), ("w", .base ⟨6⟩), ("$c11", .base ⟨4⟩)]
def callScopeR : Scope :=
  [("best", .base ⟨12⟩), ("words", .base ⟨9⟩), ("w", .base ⟨6⟩),
   ("$c11", .base ⟨4⟩)]
def callEnvR : LocalEnv := [callScopeR, baseEnvR]

def suEnvR : LocalEnv :=
  [[("$forFirst", .base ⟨8⟩)], [("i", .base ⟨7⟩)], wScopeR, baseEnvR]
def suEnvR2 : LocalEnv := [] :: [] :: suEnvR
def cpEnvR : LocalEnv :=
  [[("$forFirst", .base ⟨11⟩)], [("i", .base ⟨10⟩)], wordsScopeR, baseEnvR]
def cpEnvR2 : LocalEnv := [] :: [] :: cpEnvR

def rTailAfterSetup : Cont :=
  .seq [rS4, rS5, rS6, rS7] [wScopeR, baseEnvR] (.frame [] [] [] [] .stop)
def suHeadTailR : Cont :=
  .seq [] suEnvR
    (.seq [] [[("i", .base ⟨7⟩)], wScopeR, baseEnvR] rTailAfterSetup)
def suHeadCfgR : Config :=
  .exec (.while (.boolLit true) wordcountHarnessFunc.suBody) suEnvR suHeadTailR
def suLoopKR : Cont :=
  .loop (.boolLit true) wordcountHarnessFunc.suBody suEnvR suHeadTailR
def suStoreBlockR : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.var "w") (.var "i")))
        (.add (.var "seed") (.mod (.var "i") (.intLit 3 .uint64)))]]
def suCmpKR : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: suEnvR)
    (.seq [suStoreBlockR] ([] :: suEnvR) suLoopKR)
def suRefR (n : Nat) (iv : Int) : TargetRef :=
  .chain (rSliceW n) [.int iv .uint64] [.index]
def suStTailR : Cont :=
  .seq [] suEnvR2 (.seq [] ([] :: suEnvR) suLoopKR)
def suRhsKR (n : Nat) (iv : Int) : Cont :=
  .rhsK .vals [suRefR n iv] [] [] (.seqn #[]) suEnvR2 suStTailR
def suAddKR (n : Nat) (sv iv : Int) : Cont :=
  .strictK .add [.int sv .uint64] [] suEnvR2 (suRhsKR n iv)
def suModKR (n : Nat) (sv iv : Int) : Cont :=
  .strictK .mod [.int iv .uint64] [] suEnvR2 (suAddKR n sv iv)

def rTailAfterCopy : Cont :=
  .seq [rS6, rS7] [wordsScopeR, baseEnvR] (.frame [] [] [] [] .stop)
def cpHeadTailR : Cont :=
  .seq [] cpEnvR
    (.seq [] [[("i", .base ⟨10⟩)], wordsScopeR, baseEnvR] rTailAfterCopy)
def cpHeadCfgR : Config :=
  .exec (.while (.boolLit true) wcHarnessRFunc.cpBody) cpEnvR cpHeadTailR
def cpLoopKR : Cont :=
  .loop (.boolLit true) wcHarnessRFunc.cpBody cpEnvR cpHeadTailR
def cpStoreBlockR : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.ref "words") (.var "i")))
        (.indexGet (.var "w") (.var "i"))]]
def cpCmpKR : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: cpEnvR)
    (.seq [cpStoreBlockR] ([] :: cpEnvR) cpLoopKR)
def cpRefR (iv : Int) : TargetRef :=
  .chain (.addr (.base ⟨9⟩)) [.int iv .uint64] [.index]
def cpStTailR : Cont :=
  .seq [] cpEnvR2 (.seq [] ([] :: cpEnvR) cpLoopKR)
def cpRhsKR (iv : Int) : Cont :=
  .rhsK .vals [cpRefR iv] [] [] (.seqn #[]) cpEnvR2 cpStTailR

/-! ### The `maxCount` frame at the r-layout (the subject cells shift
+4 from the `wordcount_harness` layer: 9–15 → 13–19) -/

def rAfterCall : Cont :=
  .seq [rS7] callEnvR (.frame [] [] [] [] .stop)
def rCallArgsKR : Cont :=
  .callArgsK ⟨"maxCount"⟩ [(.chain [], [.ref "best"])] [] [] callEnvR
    rAfterCall
/-- The subject's call frame: result loc 14, write-back target `best`,
returning into the harness's epilogue. -/
def frameKR : Cont :=
  .frame [(.chain [], [.ref "best"])] callEnvR [.base ⟨14⟩] [] rAfterCall
def rFrameEnv : LocalEnv :=
  [[("$res0", .base ⟨14⟩), ("words", .base ⟨13⟩)]]

def sc0R : Scope := [("$res0", .base ⟨14⟩), ("words", .base ⟨13⟩)]
def sc1R : Scope := [("counts", .base ⟨17⟩), ("$c0", .base ⟨15⟩)]
def envR0R : LocalEnv := [sc1R, sc0R]
def envBR : LocalEnv :=
  [[("$forFirst", .base ⟨19⟩)], [("i", .base ⟨18⟩)], sc1R, sc0R]
def envB1R : LocalEnv := [[("i", .base ⟨18⟩)], sc1R, sc0R]
def env2R : LocalEnv := [] :: envBR
def env3R : LocalEnv := [] :: env2R
def u1EnvR (na : Nat) : LocalEnv := [("$c1", .base ⟨na⟩)] :: env2R
def uEnvR (na : Nat) : LocalEnv :=
  [("$c2", .base ⟨na + 1⟩), ("$c1", .base ⟨na⟩)] :: env2R

def tailBR : Cont :=
  .seq [] envBR (.seq [] envB1R
    (.seq [bestSeqn, wcMapRangeStmt, retSeqn] envR0R frameKR))
/-- The counting-loop head configuration (r-harness placement). -/
def headCR : Config :=
  .exec (.while (.boolLit true) wcWhileBody) envBR tailBR
def loopKCR : Cont := .loop (.boolLit true) wcWhileBody envBR tailBR
def bodyTailR : Cont := .seq [wcCountBody] env2R loopKCR
def cmpContCR : Cont := .ifK (.seqn #[]) .breakStmt env2R bodyTailR
def lenKR (iv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice tU64))) [] [] env2R
    (.strictK .lessCmp [.int iv .int] [] env2R cmpContCR)
def postBodyKR : Cont := .seq [] env2R loopKCR

def stK0R (na : Nat) : Cont :=
  .stmtOpK (.mapAssign tU64 tU64) 0 []
    [.var "$c2",
     .add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64) (.intLit 1 .uint64)]
    (uEnvR na) (.seq [] (uEnvR na) postBodyKR)
def stK2R (na : Nat) (w : Int) : Cont :=
  .stmtOpK (.mapAssign tU64 tU64) 0
    [.int w .uint64, .map ⟨some (.base ⟨16⟩)⟩] []
    (uEnvR na) (.seq [] (uEnvR na) postBodyKR)
def addKR (na : Nat) (w : Int) : Cont :=
  .strictK .add [] [.intLit 1 .uint64] (uEnvR na) (stK2R na w)
def mapGetKR (na : Nat) (w : Int) : Cont :=
  .strictK (.mapGet tU64 tU64) [.map ⟨some (.base ⟨16⟩)⟩] [] (uEnvR na)
    (addKR na w)

def envRBR (B : Nat) : LocalEnv := (("best", .base ⟨B⟩) :: sc1R) :: [sc0R]
def kRR (B : Nat) : Cont := .seq [retSeqn] (envRBR B) frameKR

/-! ## Heap fronts (program-generic) -/

def rHeap0 (nv sv : Int) : Heap :=
  [(.base ⟨0⟩, u64cell nv), (.base ⟨1⟩, u64cell sv),
   (.base ⟨2⟩, arrCell 8 zeros8), (.base ⟨3⟩, u64cell 0)]

def rHeapC11 (nv sv : Int) : Heap :=
  rHeap0 nv sv ++ [(.base ⟨4⟩, rNilSlice)]

def rHeapMake (nv sv : Int) (n : Nat) : Heap :=
  rHeap0 nv sv ++
    [(.base ⟨4⟩, rHandleW n), (.base ⟨5⟩, arrCell n (List.replicate n 0))]

def rHeapSu (nv sv : Int) (n : Nat) (l : List Int) (iv : Int) (ff : Bool) :
    Heap :=
  rHeap0 nv sv ++
    [(.base ⟨4⟩, rHandleW n), (.base ⟨5⟩, arrCell n l),
     (.base ⟨6⟩, rHandleW n), (.base ⟨7⟩, u64cell iv), (.base ⟨8⟩, bcell ff)]

def rHeapCp (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (ff : Bool) : Heap :=
  rHeapSu nv sv n l siv false ++
    [(.base ⟨9⟩, arrCell 8 lp), (.base ⟨10⟩, u64cell civ),
     (.base ⟨11⟩, bcell ff)]

def rHeapCall (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int) :
    Heap :=
  rHeapCp nv sv n l lp siv civ false ++ [(.base ⟨12⟩, u64cell 0)]

def rHeapMFrame (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int) :
    Heap :=
  rHeapCall nv sv n l lp siv civ ++
    [(.base ⟨13⟩, rHandleW n), (.base ⟨14⟩, u64cell 0)]

/-- The twenty concrete front cells during the subject's counting and
range phases (`sv`/`siv`/`civ` = the parked seed and the two parked
loop counters). -/
def frontR (L : Nat) (sv siv civ : Int) (ws lp : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (ff : Bool) : Heap :=
  [(.base ⟨0⟩, u64cell (L : Int)), (.base ⟨1⟩, u64cell sv),
   (.base ⟨2⟩, arrCell 8 zeros8), (.base ⟨3⟩, u64cell 0),
   (.base ⟨4⟩, rHandleW L), (.base ⟨5⟩, arrCell L ws),
   (.base ⟨6⟩, rHandleW L), (.base ⟨7⟩, u64cell siv),
   (.base ⟨8⟩, bcell false), (.base ⟨9⟩, arrCell 8 lp),
   (.base ⟨10⟩, u64cell civ), (.base ⟨11⟩, bcell false),
   (.base ⟨12⟩, u64cell 0), (.base ⟨13⟩, rHandleW L),
   (.base ⟨14⟩, u64cell 0), (.base ⟨15⟩, mhCellR),
   (.base ⟨16⟩, mdCell kvs), (.base ⟨17⟩, mhCellR),
   (.base ⟨18⟩, intcell iv), (.base ⟨19⟩, bcell ff)]

/-- The subject-phase state: concrete front + the symbolic dead-cell
tail, over an ABSTRACT program context. Partially applied, this is the
state family `S` the generic counting/range layers quantify over. -/
def σR (σ : ExecState) (L : Nat) (sv siv civ : Int) (ws lp : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (ff : Bool) (dead : Heap)
    (na : Nat) : ExecState :=
  wSt σ (frontR L sv siv civ ws lp kvs iv ff ++ dead) na

theorem lookup_frontR_none (L : Nat) (sv siv civ : Int) (ws lp : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (ff : Bool) {x : Nat} (hx : 20 ≤ x) :
    Heap.lookup (frontR L sv siv civ ws lp kvs iv ff) (.base ⟨x⟩) = none := by
  simp only [frontR, Heap.lookup,
    base_beq_false (by omega : (0 : Nat) ≠ x),
    base_beq_false (by omega : (1 : Nat) ≠ x),
    base_beq_false (by omega : (2 : Nat) ≠ x),
    base_beq_false (by omega : (3 : Nat) ≠ x),
    base_beq_false (by omega : (4 : Nat) ≠ x),
    base_beq_false (by omega : (5 : Nat) ≠ x),
    base_beq_false (by omega : (6 : Nat) ≠ x),
    base_beq_false (by omega : (7 : Nat) ≠ x),
    base_beq_false (by omega : (8 : Nat) ≠ x),
    base_beq_false (by omega : (9 : Nat) ≠ x),
    base_beq_false (by omega : (10 : Nat) ≠ x),
    base_beq_false (by omega : (11 : Nat) ≠ x),
    base_beq_false (by omega : (12 : Nat) ≠ x),
    base_beq_false (by omega : (13 : Nat) ≠ x),
    base_beq_false (by omega : (14 : Nat) ≠ x),
    base_beq_false (by omega : (15 : Nat) ≠ x),
    base_beq_false (by omega : (16 : Nat) ≠ x),
    base_beq_false (by omega : (17 : Nat) ≠ x),
    base_beq_false (by omega : (18 : Nat) ≠ x),
    base_beq_false (by omega : (19 : Nat) ≠ x),
    Bool.false_eq_true, if_false]

/-- The exit-phase front: `$res0` (2), `$res1` (3), `best` (12) and the
subject's `$res0` (14) generalized; the counting counter parked at
`L`. -/
def frontXR (L : Nat) (sv siv civ : Int) (ws lp r2 : List Int)
    (kvs : List (Int × Nat)) (r3 r12 r14 : Int) : Heap :=
  [(.base ⟨0⟩, u64cell (L : Int)), (.base ⟨1⟩, u64cell sv),
   (.base ⟨2⟩, arrCell 8 r2), (.base ⟨3⟩, u64cell r3),
   (.base ⟨4⟩, rHandleW L), (.base ⟨5⟩, arrCell L ws),
   (.base ⟨6⟩, rHandleW L), (.base ⟨7⟩, u64cell siv),
   (.base ⟨8⟩, bcell false), (.base ⟨9⟩, arrCell 8 lp),
   (.base ⟨10⟩, u64cell civ), (.base ⟨11⟩, bcell false),
   (.base ⟨12⟩, u64cell r12), (.base ⟨13⟩, rHandleW L),
   (.base ⟨14⟩, u64cell r14), (.base ⟨15⟩, mhCellR),
   (.base ⟨16⟩, mdCell kvs), (.base ⟨17⟩, mhCellR),
   (.base ⟨18⟩, intcell ((L : Nat) : Int)), (.base ⟨19⟩, bcell false)]

def σXR (σ : ExecState) (L : Nat) (sv siv civ : Int) (ws lp r2 : List Int)
    (kvs : List (Int × Nat)) (r3 r12 r14 : Int) (tail : Heap) (na : Nat) :
    ExecState :=
  wSt σ (frontXR L sv siv civ ws lp r2 kvs r3 r12 r14 ++ tail) na

theorem lookup_frontXR_none (L : Nat) (sv siv civ : Int)
    (ws lp r2 : List Int) (kvs : List (Int × Nat)) (r3 r12 r14 : Int)
    {x : Nat} (hx : 20 ≤ x) :
    Heap.lookup (frontXR L sv siv civ ws lp r2 kvs r3 r12 r14) (.base ⟨x⟩)
      = none := by
  simp only [frontXR, Heap.lookup,
    base_beq_false (by omega : (0 : Nat) ≠ x),
    base_beq_false (by omega : (1 : Nat) ≠ x),
    base_beq_false (by omega : (2 : Nat) ≠ x),
    base_beq_false (by omega : (3 : Nat) ≠ x),
    base_beq_false (by omega : (4 : Nat) ≠ x),
    base_beq_false (by omega : (5 : Nat) ≠ x),
    base_beq_false (by omega : (6 : Nat) ≠ x),
    base_beq_false (by omega : (7 : Nat) ≠ x),
    base_beq_false (by omega : (8 : Nat) ≠ x),
    base_beq_false (by omega : (9 : Nat) ≠ x),
    base_beq_false (by omega : (10 : Nat) ≠ x),
    base_beq_false (by omega : (11 : Nat) ≠ x),
    base_beq_false (by omega : (12 : Nat) ≠ x),
    base_beq_false (by omega : (13 : Nat) ≠ x),
    base_beq_false (by omega : (14 : Nat) ≠ x),
    base_beq_false (by omega : (15 : Nat) ≠ x),
    base_beq_false (by omega : (16 : Nat) ≠ x),
    base_beq_false (by omega : (17 : Nat) ≠ x),
    base_beq_false (by omega : (18 : Nat) ≠ x),
    base_beq_false (by omega : (19 : Nat) ≠ x),
    Bool.false_eq_true, if_false]

/-- The post-prelude configuration. -/
def rHC0 : Config :=
  .exec wcHarnessRFunc.body [baseEnvR] (.frame [] [] [] [] .stop)

/-! ## Heap-lookup facts -/

theorem lookup_suR (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ff : Bool) (na : Nat) :
    Heap.lookup (wSt σ (rHeapSu nv sv n l iv ff) na).heap (.base ⟨5⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [rHeapSu, rHeap0, Heap.lookup]

theorem lookup_cpW_R (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ff : Bool) (na : Nat) :
    Heap.lookup (wSt σ (rHeapCp nv sv n l lp siv civ ff) na).heap (.base ⟨5⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [rHeapCp, rHeapSu, rHeap0, Heap.lookup]

theorem lookup_cpWords_R (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ff : Bool) (na : Nat) :
    Heap.lookup (wSt σ (rHeapCp nv sv n l lp siv civ ff) na).heap (.base ⟨9⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨lp.map (fun v => .int v .uint64)⟩⟩ := by
  simp [rHeapCp, rHeapSu, rHeap0, Heap.lookup]

/-! ## Raw run segments — PROGRAM-generic throughout -/

/-- Entry A: body start → the `$c11` makeSlice apply point. 10 steps. -/
theorem r_E1_raw (σ : ExecState) (nv sv : Int) (ch : Choices) :
    stepFnIter 10 (wSt σ (rHeap0 nv sv) 4) rHC0 ch
      = .ok (.retV (.int nv .uint64)
          (.stmtOpK (.makeSlice tU64 false) 1
            [.addr (.base ⟨4⟩)] [] envC11R
            (.seq [rS2, rS3, rS4, rS5, rS6, rS7] envC11R
              (.frame [] [] [] [] .stop))),
        wSt σ (rHeapC11 nv sv) 5, ch) := by
  with_unfolding_all rfl

/-- **`make([]uint64, n)` at SYMBOLIC `n`.** -/
theorem r_make_apply (σ : ExecState) (nv sv : Int) (n : Nat) (ch : Choices) :
    applyStmtOp (wSt σ (rHeapC11 nv sv) 5) ch (.makeSlice tU64 false) 1
      [.addr (.base ⟨4⟩), .int (n : Nat) .uint64]
      = .ok (wSt σ (rHeapMake nv sv n) 6, ch) := by
  have hnn1 := natFromNonneg_cast
    "runtime error: makeslice: len out of range" n
  have hnn2 := natFromNonneg_cast
    "runtime error: makeslice: cap out of range" n
  have hb := GoLean.Iris.buildDefaultArrayValue_int
    (wSt σ (rHeapC11 nv sv) 5) .uint64 n
  have harr : (List.replicate n (GoValue.int 0 .uint64)).toArray
      = (⟨(List.replicate n (0 : Int)).map
          (fun v => GoValue.int v .uint64)⟩ : Array GoValue) := by
    simp [List.map_replicate]
  rw [harr] at hb
  simp only [applyStmtOp, applyStmtOpCore, valueAsInt, valueAsLoc,
    hnn1, hnn2, hb, Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (Nat.lt_irrefl n)]
  with_unfolding_all rfl

/-- Entry B: `w := $c11`, the setup counter and flag → the setup loop
head. 42 steps. -/
theorem r_E2_raw (σ : ExecState) (nv sv : Int) (n : Nat) (ch : Choices) :
    stepFnIter 42 (wSt σ (rHeapMake nv sv n) 6)
      (.next (.seq [rS2, rS3, rS4, rS5, rS6, rS7] envC11R
        (.frame [] [] [] [] .stop))) ch
      = .ok (suHeadCfgR,
          wSt σ (rHeapSu nv sv n (List.replicate n 0) 0 true) 9, ch) := by
  with_unfolding_all rfl

/-! ### The setup loop -/

theorem su_A0_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 25 (wSt σ (rHeapSu nv sv n l iv true) 9) suHeadCfgR ch
      = .ok (.retV (.bool (decide (iv < nv))) suCmpKR,
          wSt σ (rHeapSu nv sv n l iv false) 9, ch) := by
  with_unfolding_all rfl

theorem su_A1_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 29 (wSt σ (rHeapSu nv sv n l iv false) 9) suHeadCfgR ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < nv))) suCmpKR,
          wSt σ (rHeapSu nv sv n l
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false) 9, ch) := by
  with_unfolding_all rfl

/-- Setup fill phase A: test true → the `%` apply point. 19 steps. -/
theorem su_B1a_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 19 (wSt σ (rHeapSu nv sv n l iv false) 9)
      (.retV (.bool true) suCmpKR) ch
      = .ok (.retV (.int 3 .uint64) (suModKR n sv iv),
          wSt σ (rHeapSu nv sv n l iv false) 9, ch) := by
  with_unfolding_all rfl

/-- Setup fill phase B: the `%` result → the add → the element-store
point. 2 steps. -/
theorem su_B1b_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv rv : Int) (ch : Choices) :
    stepFnIter 2 (wSt σ (rHeapSu nv sv n l iv false) 9)
      (.retV (.int rv .uint64) (suAddKR n sv iv)) ch
      = .ok (.next (.storeK [suRefR n iv]
            [.int (IntKind.normalize .uint64 (sv + rv)) .uint64]
            (.seqn #[]) suEnvR2 suStTailR),
          wSt σ (rHeapSu nv sv n l iv false) 9, ch) := by
  with_unfolding_all rfl

theorem su_D_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 5 (wSt σ (rHeapSu nv sv n l iv false) 9)
      (.next (.storeK [] [] (.seqn #[]) suEnvR2 suStTailR)) ch
      = .ok (suHeadCfgR, wSt σ (rHeapSu nv sv n l iv false) 9, ch) := by
  with_unfolding_all rfl

/-- Setup exit: test false → `var words` declared (an `.initialization`,
NOT a `makeSlice`) and the copy loop head. 39 steps. -/
theorem su_X_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 39 (wSt σ (rHeapSu nv sv n l iv false) 9)
      (.retV (.bool false) suCmpKR) ch
      = .ok (cpHeadCfgR,
          wSt σ (rHeapCp nv sv n l zeros8 iv 0 true) 12, ch) := by
  with_unfolding_all rfl

/-! ### The copy loop (byte-identical in shape to minmax's `cp_*`) -/

theorem cp_A0_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 25 (wSt σ (rHeapCp nv sv n l lp siv civ true) 12) cpHeadCfgR ch
      = .ok (.retV (.bool (decide (civ < nv))) cpCmpKR,
          wSt σ (rHeapCp nv sv n l lp siv civ false) 12, ch) := by
  with_unfolding_all rfl

theorem cp_A1_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 29 (wSt σ (rHeapCp nv sv n l lp siv civ false) 12) cpHeadCfgR
      ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1))
              < nv))) cpCmpKR,
          wSt σ (rHeapCp nv sv n l lp siv
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1)))
            false) 12, ch) := by
  with_unfolding_all rfl

/-- Copy phase 1: test true → the `words[i]` target banked, the `w[i]`
read at its apply point. 16 steps. -/
theorem cp_B1_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 16 (wSt σ (rHeapCp nv sv n l lp siv civ false) 12)
      (.retV (.bool true) cpCmpKR) ch
      = .ok (.retV (.int civ .uint64)
            (.strictK .indexGet [rSliceW n] [] cpEnvR2 (cpRhsKR civ)),
          wSt σ (rHeapCp nv sv n l lp siv civ false) 12, ch) := by
  with_unfolding_all rfl

theorem cp_B2_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1 (wSt σ (rHeapCp nv sv n l lp siv civ false) 12)
      (.retV w (cpRhsKR civ)) ch
      = .ok (.next (.storeK [cpRefR civ] [w] (.seqn #[]) cpEnvR2 cpStTailR),
          wSt σ (rHeapCp nv sv n l lp siv civ false) 12, ch) := by
  with_unfolding_all rfl

theorem cp_D_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 5 (wSt σ (rHeapCp nv sv n l lp siv civ false) 12)
      (.next (.storeK [] [] (.seqn #[]) cpEnvR2 cpStTailR)) ch
      = .ok (cpHeadCfgR, wSt σ (rHeapCp nv sv n l lp siv civ false) 12,
          ch) := by
  with_unfolding_all rfl

/-- Copy exit: test false → `best` declared and the `maxCount(w)`
argument delivered at the drained `callArgsK`. 13 steps. -/
theorem cp_X_rawR (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) (ch : Choices) :
    stepFnIter 13 (wSt σ (rHeapCp nv sv n l lp siv civ false) 12)
      (.retV (.bool false) cpCmpKR) ch
      = .ok (.retV (rSliceW n) rCallArgsKR,
          wSt σ (rHeapCall nv sv n l lp siv civ) 13, ch) := by
  with_unfolding_all rfl

/-- The `maxCount` prologue: `$c0`/makeMap/`counts`/`i`/`$forFirst` →
the counting-loop head at `nextAddr = 20`. 51 steps, program-free given
the frame entry. -/
theorem r_prologue_rawR (σ : ExecState) (sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 51 (wSt σ (rHeapMFrame ((n : Nat) : Int) sv n l lp siv civ) 15)
      (.exec maxCountFunc.body rFrameEnv frameKR) ch
      = .ok (headCR, σR σ n sv siv civ l lp [] 0 true [] 20, ch) := by
  with_unfolding_all rfl

/-! ### The counting-loop segments at the r-placement (step counts
identical to the `wordcount_harness` tower — same statements, new
addresses, and the subject frame sitting on the r-harness's epilogue) -/

theorem wcR_segA0_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (na : Nat) (ch : Choices) :
    stepFnIter 25 (σR σ L sv siv civ ws lp kvs iv true dead na) headCR ch
      = .ok (.retV (rSliceW L) (lenKR iv),
          σR σ L sv siv civ ws lp kvs iv false dead na, ch) := by
  with_unfolding_all rfl

theorem wcR_segA1_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (dead : Heap)
    (na : Nat) (ch : Choices) :
    stepFnIter 29 (σR σ L sv siv civ ws lp kvs iv false dead na) headCR ch
      = .ok (.retV (rSliceW L)
            (lenKR (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
          σR σ L sv siv civ ws lp kvs
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            false dead na, ch) := by
  with_unfolding_all rfl

theorem wcR_cmp_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv jv : Int) (dead : Heap)
    (na : Nat) (ch : Choices) :
    stepFnIter 1 (σR σ L sv siv civ ws lp kvs iv false dead na)
      (.retV (.int (L : Int) .int)
        (.strictK .lessCmp [.int jv .int] [] env2R cmpContCR)) ch
      = .ok (.retV (.bool (decide (jv < (L : Int)))) cmpContCR,
          σR σ L sv siv civ ws lp kvs iv false dead na, ch) := by
  with_unfolding_all rfl

theorem wcR_segC1_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (tail : Heap)
    (na : Nat) (ch : Choices) :
    stepFnIter 7 (σR σ L sv siv civ ws lp kvs iv false tail na)
      (.retV (.bool true) cmpContCR) ch
      = .ok (.exec (.initialization { id := "$c1", typ := tMap }) env3R
            (.seq [asgnC1, seqnC2, mapAsgnStmt] env3R postBodyKR),
          σR σ L sv siv civ ws lp kvs iv false tail na, ch) := by
  with_unfolding_all rfl

theorem wcR_segC2_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (tail : Heap)
    (na₀ na : Nat) (ch : Choices) :
    stepFnIter 6 (σR σ L sv siv civ ws lp kvs iv false tail na)
      (.next (.seq [asgnC1, seqnC2, mapAsgnStmt] (u1EnvR na₀) postBodyKR)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀⟩)) [] []]
            [.map ⟨some (.base ⟨16⟩)⟩] (.seqn #[]) (u1EnvR na₀)
            (.seq [seqnC2, mapAsgnStmt] (u1EnvR na₀) postBodyKR)),
          σR σ L sv siv civ ws lp kvs iv false tail na, ch) := by
  with_unfolding_all rfl

theorem wcR_segC3_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (tail : Heap)
    (na₀ na : Nat) (ch : Choices) :
    stepFnIter 5 (σR σ L sv siv civ ws lp kvs iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (u1EnvR na₀)
        (.seq [seqnC2, mapAsgnStmt] (u1EnvR na₀) postBodyKR))) ch
      = .ok (.exec (.initialization { id := "$c2", typ := tU64 }) (u1EnvR na₀)
            (.seq [.assign (.var "$c2")
                (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
              (u1EnvR na₀) postBodyKR),
          σR σ L sv siv civ ws lp kvs iv false tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σR σ L sv siv civ ws lp kvs iv false tail na) (body := .seqn #[])
    (env := u1EnvR na₀)
    (k := .seq [seqnC2, mapAsgnStmt] (u1EnvR na₀) postBodyKR) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σR σ L sv siv civ ws lp kvs iv false tail na) (ss := #[])
    (env := u1EnvR na₀) (rest := [seqnC2, mapAsgnStmt]) (k := postBodyKR)
    (ch := ch))
  have h3 := stepFnIter_one (stepFn_seq_pop
    (σ := σR σ L sv siv civ ws lp kvs iv false tail na) (t := seqnC2)
    (rest := [mapAsgnStmt]) (env := u1EnvR na₀) (k := postBodyKR) (ch := ch))
  have h4 := stepFnIter_one (stepFn_seqn_splice
    (σ := σR σ L sv siv civ ws lp kvs iv false tail na)
    (ss := #[.initialization { id := "$c2", typ := tU64 },
      .assign (.var "$c2") (.indexGet (.var "words") (.var "i"))])
    (env := u1EnvR na₀) (rest := [mapAsgnStmt]) (k := postBodyKR) (ch := ch))
  have h5 := stepFnIter_one (stepFn_seq_pop
    (σ := σR σ L sv siv civ ws lp kvs iv false tail na)
    (t := .initialization { id := "$c2", typ := tU64 })
    (rest := [.assign (.var "$c2")
      (.indexGet (.var "words") (.var "i")), mapAsgnStmt])
    (env := u1EnvR na₀) (k := postBodyKR) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h1 h2) h3) h4) h5

theorem wcR_segC4_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (tail : Heap)
    (na₀ na : Nat) (ch : Choices) :
    stepFnIter 8 (σR σ L sv siv civ ws lp kvs iv false tail na)
      (.next (.seq [.assign (.var "$c2")
          (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
        (uEnvR na₀) postBodyKR)) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [rSliceW L] [] (uEnvR na₀)
              (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
                (.seqn #[]) (uEnvR na₀)
                (.seq [mapAsgnStmt] (uEnvR na₀) postBodyKR))),
          σR σ L sv siv civ ws lp kvs iv false tail na, ch) := by
  with_unfolding_all rfl

theorem wcR_segC5_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (tail : Heap)
    (na₀ na : Nat) (w : GoValue) (ch : Choices) :
    stepFnIter 1 (σR σ L sv siv civ ws lp kvs iv false tail na)
      (.retV w
        (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
          (.seqn #[]) (uEnvR na₀)
          (.seq [mapAsgnStmt] (uEnvR na₀) postBodyKR))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [w]
            (.seqn #[]) (uEnvR na₀)
            (.seq [mapAsgnStmt] (uEnvR na₀) postBodyKR)),
          σR σ L sv siv civ ws lp kvs iv false tail na, ch) := by
  with_unfolding_all rfl

theorem wcR_segC6_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (tail : Heap)
    (na₀ na : Nat) (ch : Choices) :
    stepFnIter 4 (σR σ L sv siv civ ws lp kvs iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (uEnvR na₀)
        (.seq [mapAsgnStmt] (uEnvR na₀) postBodyKR))) ch
      = .ok (.evalE (.var "$c1") (uEnvR na₀) (stK0R na₀),
          σR σ L sv siv civ ws lp kvs iv false tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σR σ L sv siv civ ws lp kvs iv false tail na) (body := .seqn #[])
    (env := uEnvR na₀) (k := .seq [mapAsgnStmt] (uEnvR na₀) postBodyKR)
    (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σR σ L sv siv civ ws lp kvs iv false tail na) (ss := #[])
    (env := uEnvR na₀) (rest := [mapAsgnStmt]) (k := postBodyKR) (ch := ch))
  have h3 : stepFnIter 2 (σR σ L sv siv civ ws lp kvs iv false tail na)
      (.next (.seq ((#[] : Array Stmt).toList ++ [mapAsgnStmt]) (uEnvR na₀)
        postBodyKR)) ch
      = .ok (.evalE (.var "$c1") (uEnvR na₀) (stK0R na₀),
          σR σ L sv siv civ ws lp kvs iv false tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

theorem wcR_segC7_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (tail : Heap)
    (na₀ na : Nat) (ch : Choices) :
    stepFnIter 1 (σR σ L sv siv civ ws lp kvs iv false tail na)
      (.retV (.map ⟨some (.base ⟨16⟩)⟩) (stK0R na₀)) ch
      = .ok (.evalE (.var "$c2") (uEnvR na₀)
            (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨16⟩)⟩]
              [.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
                (.intLit 1 .uint64)]
              (uEnvR na₀) (.seq [] (uEnvR na₀) postBodyKR)),
          σR σ L sv siv civ ws lp kvs iv false tail na, ch) := by
  with_unfolding_all rfl

theorem wcR_segC8_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (tail : Heap)
    (na₀ na : Nat) (w : Int) (ch : Choices) :
    stepFnIter 3 (σR σ L sv siv civ ws lp kvs iv false tail na)
      (.retV (.int w .uint64)
        (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨16⟩)⟩]
          [.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
            (.intLit 1 .uint64)]
          (uEnvR na₀) (.seq [] (uEnvR na₀) postBodyKR))) ch
      = .ok (.evalE (.var "$c1") (uEnvR na₀)
            (.strictK (.mapGet tU64 tU64) [] [.var "$c2"] (uEnvR na₀)
              (addKR na₀ w)),
          σR σ L sv siv civ ws lp kvs iv false tail na, ch) := by
  with_unfolding_all rfl

theorem wcR_segC9_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (tail : Heap)
    (na₀ na : Nat) (w : Int) (ch : Choices) :
    stepFnIter 1 (σR σ L sv siv civ ws lp kvs iv false tail na)
      (.retV (.map ⟨some (.base ⟨16⟩)⟩)
        (.strictK (.mapGet tU64 tU64) [] [.var "$c2"] (uEnvR na₀)
          (addKR na₀ w))) ch
      = .ok (.evalE (.var "$c2") (uEnvR na₀) (mapGetKR na₀ w),
          σR σ L sv siv civ ws lp kvs iv false tail na, ch) := by
  with_unfolding_all rfl

theorem wcR_segC10_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (tail : Heap)
    (na₀ na : Nat) (w cv : Int) (ch : Choices) :
    stepFnIter 3 (σR σ L sv siv civ ws lp kvs iv false tail na)
      (.retV (.int cv .uint64) (addKR na₀ w)) ch
      = .ok (.retV (.int (IntKind.normalize .uint64 (cv + 1)) .uint64)
            (stK2R na₀ w),
          σR σ L sv siv civ ws lp kvs iv false tail na, ch) := by
  with_unfolding_all rfl

theorem wcR_segC11_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (tail : Heap)
    (na₀ na : Nat) (ch : Choices) :
    stepFnIter 3 (σR σ L sv siv civ ws lp kvs iv false tail na)
      (.next (.seq [] (uEnvR na₀) postBodyKR)) ch
      = .ok (headCR, σR σ L sv siv civ ws lp kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-! ### Counting-loop exit → the range head -/

theorem wcR_segX0_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (tail : Heap)
    (na : Nat) (ch : Choices) :
    stepFnIter 9 (σR σ L sv siv civ ws lp kvs iv false tail na)
      (.retV (.bool false) cmpContCR) ch
      = .ok (.exec (.initialization { id := "best", typ := tU64 }) envR0R
            (.seq [.assign (.var "best") (.intLit 0 .uint64),
              wcMapRangeStmt, retSeqn] envR0R frameKR),
          σR σ L sv siv civ ws lp kvs iv false tail na, ch) := by
  with_unfolding_all rfl

theorem wcR_segX0b_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (tail : Heap)
    (B na : Nat) (ch : Choices) :
    stepFnIter 6 (σR σ L sv siv civ ws lp kvs iv false tail na)
      (.next (.seq [.assign (.var "best") (.intLit 0 .uint64),
        wcMapRangeStmt, retSeqn] (envRBR B) frameKR)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
            [.int 0 .uint64] (.seqn #[]) (envRBR B)
            (.seq [wcMapRangeStmt, retSeqn] (envRBR B) frameKR)),
          σR σ L sv siv civ ws lp kvs iv false tail na, ch) := by
  with_unfolding_all rfl

theorem wcR_segX0c_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv : Int) (tail : Heap)
    (B na : Nat) (ch : Choices) :
    stepFnIter 5 (σR σ L sv siv civ ws lp kvs iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (envRBR B)
        (.seq [wcMapRangeStmt, retSeqn] (envRBR B) frameKR))) ch
      = .ok (.retV (.map ⟨some (.base ⟨16⟩)⟩)
            (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRBR B)
              (kRR B)),
          σR σ L sv siv civ ws lp kvs iv false tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σR σ L sv siv civ ws lp kvs iv false tail na) (body := .seqn #[])
    (env := envRBR B)
    (k := .seq [wcMapRangeStmt, retSeqn] (envRBR B) frameKR) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σR σ L sv siv civ ws lp kvs iv false tail na) (ss := #[])
    (env := envRBR B) (rest := [wcMapRangeStmt, retSeqn]) (k := frameKR)
    (ch := ch))
  have h3 : stepFnIter 3 (σR σ L sv siv civ ws lp kvs iv false tail na)
      (.next (.seq ((#[] : Array Stmt).toList ++ [wcMapRangeStmt, retSeqn])
        (envRBR B) frameKR)) ch
      = .ok (.retV (.map ⟨some (.base ⟨16⟩)⟩)
            (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRBR B)
              (kRR B)),
          σR σ L sv siv civ ws lp kvs iv false tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3


/-! ## The setup loop, cleaned + its induction -/

/-- One setup iteration from the exit test's true delivery at `i`:
`i % 3` (conditioned), the wrapped add, the element store, back to the
head, `i++`, the next test — the family prefix advanced. 57 steps. -/
theorem su_iterR (σ : ExecState) (n seed i : Nat) (hn : n < 2 ^ 63)
    (hi : i < n) (ch : Choices) :
    stepFnIter 57
      (wSt σ (rHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
        (wcFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false) 9)
      (.retV (.bool true) suCmpKR) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) suCmpKR,
          wSt σ (rHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
            (wcFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
            ((i + 1 : Nat) : Int) false) 9, ch) := by
  have hB1a := su_B1a_rawR σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (wcFamily i seed ++ List.replicate (n - i) 0) ((i : Nat) : Int) ch
  have hmod := stepFnIter_one (stepFn_strict_apply
    (done := [.int ((i : Nat) : Int) .uint64]) (env := suEnvR2)
    (k := suAddKR n ((seed : Nat) : Int) ((i : Nat) : Int)) (ch := ch)
    (applyStrictOp_mod_u64
      (σ := wSt σ (rHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
        (wcFamily i seed ++ List.replicate (n - i) 0) ((i : Nat) : Int) false) 9)
      (a := i) (b := 3) (by omega) (by omega)))
  have h1 := stepFnIter_chain hB1a hmod
  have hB1b := su_B1b_rawR σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (wcFamily i seed ++ List.replicate (n - i) 0) ((i : Nat) : Int)
    ((i % 3 : Nat) : Int) ch
  rw [unorm_add_nat seed (i % 3)] at hB1b
  have h2 := stepFnIter_chain h1 hB1b
  have hw : (0 : Int) ≤ (((seed + i % 3) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + i % 3) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + i % 3) (y := 2 ^ 64) (by omega)
    omega
  have hst := storeTarget_slice_u64
    (σ := wSt σ (rHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
      (wcFamily i seed ++ List.replicate (n - i) 0) ((i : Nat) : Int) false) 9)
    (a := ⟨5⟩) (off := 0) (len := n) (cap := n) (i := i) (n := n)
    (ik := .uint64) (l := wcFamily i seed ++ List.replicate (n - i) 0)
    (w := (((seed + i % 3) % 2 ^ 64 : Nat) : Int))
    (lookup_suR σ ((n : Nat) : Int) ((seed : Nat) : Int) n
      (wcFamily i seed ++ List.replicate (n - i) 0) ((i : Nat) : Int) false 9)
    (Nat.le_refl n) hi
    (by rw [List.length_append, wcFamily_length, List.length_replicate]
        omega)
    (by rw [List.length_append, wcFamily_length, List.length_replicate]
        omega)
    wcFamilyZ_range hw
  rw [Nat.zero_add, wcFamily_set hi] at hst
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hst))
  have hD := su_D_rawR σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (wcFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
    ((i : Nat) : Int) ch
  have h4 := stepFnIter_chain h3 hD
  have hA1 := su_A1_rawR σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (wcFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
    ((i : Nat) : Int) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  exact stepFnIter_chain h4 hA1

/-- **The setup loop**, by strong induction on `n - i`: exactly
`57·(n-i)` steps materialize the wrapped `seed + i%3` family. -/
theorem su_loopR (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 63) :
    ∀ μ i, μ = n - i → i ≤ n → ∀ ch : Choices,
    stepFnIter (57 * (n - i))
      (wSt σ (rHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
        (wcFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false) 9)
      (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
        suCmpKR) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) suCmpKR,
          wSt σ (rHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
            (wcFamily n seed) ((n : Nat) : Int) false) 9, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro i hμ hin ch
    rcases Nat.lt_or_ge i n with hlt | hge
    · rw [show (decide (((i : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      have hiter := su_iterR σ n seed i hn hlt ch
      have hrec := ih (n - (i + 1)) (by omega) (i + 1) rfl (by omega) ch
      have hc := stepFnIter_chain hiter hrec
      rw [show 57 + 57 * (n - (i + 1)) = 57 * (n - i) from by omega] at hc
      exact hc
    · have hEq : i = n := by omega
      subst hEq
      simp only [Nat.sub_self, Nat.mul_zero, List.replicate_zero,
        List.append_nil]
      rfl

/-! ## The copy loop, cleaned + its induction

`words[i] = w[i]` copies exactly the family element the setup loop
wrote, so `wcFamily`/`wcPre` serve both invariants and the store is the
lifted `SliceMem.storeTarget_arrayLocal_u64` at the array-typed local
`words` (address 9, cap 8). -/

theorem cp_iterR (σ : ExecState) (n seed : Nat) (siv : Int) (m : Nat)
    (hn : n < 2 ^ 63) (hcap : n ≤ 8) (hm : m < n) (ch : Choices) :
    stepFnIter 53
      (wSt σ (rHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
        (wcFamily n seed) (wcPre m seed) siv ((m : Nat) : Int) false) 12)
      (.retV (.bool true) cpCmpKR) ch
      = .ok (.retV (.bool (decide
            (((m + 1 : Nat) : Int) < ((n : Nat) : Int)))) cpCmpKR,
          wSt σ (rHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
            (wcFamily n seed) (wcPre (m + 1) seed) siv
            ((m + 1 : Nat) : Int) false) 12, ch) := by
  have hlenF : (wcFamily n seed).length = n := wcFamily_length n seed
  have hB1 := cp_B1_rawR σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (wcFamily n seed) (wcPre m seed) siv ((m : Nat) : Int) ch
  have hget : (⟨(wcFamily n seed).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + m]?
      = some (.int (((seed + m % 3) % 2 ^ 64 : Nat) : Int) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega), wcFamily_getD hm]
  have hread := stepFn_strict_apply (done := [rSliceW n]) (env := cpEnvR2)
    (k := cpRhsKR ((m : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .uint64)
      (lookup_cpW_R σ ((n : Nat) : Int) ((seed : Nat) : Int) n
        (wcFamily n seed) (wcPre m seed) siv ((m : Nat) : Int) false 12)
      (Nat.le_refl n) hm hget)
  have hB2 := cp_B2_rawR σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (wcFamily n seed) (wcPre m seed) siv ((m : Nat) : Int)
    (.int (((seed + m % 3) % 2 ^ 64 : Nat) : Int) .uint64) ch
  have hw : (0 : Int) ≤ (((seed + m % 3) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + m % 3) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + m % 3) (y := 2 ^ 64) (by omega)
    omega
  have hst := storeTarget_arrayLocal_u64 (a := ⟨9⟩) (N := 8) (i := m)
    (ik := .uint64) (l := wcPre m seed)
    (w := (((seed + m % 3) % 2 ^ 64 : Nat) : Int))
    (lookup_cpWords_R σ ((n : Nat) : Int) ((seed : Nat) : Int) n
      (wcFamily n seed) (wcPre m seed) siv ((m : Nat) : Int) false 12)
    (by rw [wcPre_length (by omega)]; omega)
    (wcPre_length (by omega)) wcPre_range hw
  rw [wcPre_set (by omega : m < 8)] at hst
  have hstore : storeTarget
      (wSt σ (rHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
        (wcFamily n seed) (wcPre m seed) siv ((m : Nat) : Int) false) 12)
      (cpRefR ((m : Nat) : Int))
      (.int (((seed + m % 3) % 2 ^ 64 : Nat) : Int) .uint64)
      = .ok (wSt σ (rHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
          (wcFamily n seed) (wcPre (m + 1) seed) siv
          ((m : Nat) : Int) false) 12) := hst
  have hD := cp_D_rawR σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (wcFamily n seed) (wcPre (m + 1) seed) siv ((m : Nat) : Int) ch
  have hA1 := cp_A1_rawR σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (wcFamily n seed) (wcPre (m + 1) seed) siv ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  have h1 := stepFnIter_chain hB1 (stepFnIter_one hread)
  have h2 := stepFnIter_chain h1 hB2
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hstore))
  exact stepFnIter_chain (stepFnIter_chain h3 hD) hA1

/-- **The copy loop + the call**: from the exit-test delivery at `m`,
the run reaches the subject's counting-loop head within `53·μ + 65`
steps — the copy exit (13), the ONE program-consulting `enterFrame`
step, and `maxCount`'s prologue (51). -/
theorem cp_loopR (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 63)
    (hcap : n ≤ 8)
    (henter : ∀ (l lp : List Int) (siv civ : Int),
      enterFrame (wSt σ (rHeapCall ((n : Nat) : Int) ((seed : Nat) : Int) n
          l lp siv civ) 13) ⟨"maxCount"⟩ [rSliceW n]
        = .ok (maxCountFunc, rFrameEnv, [.base ⟨14⟩],
            wSt σ (rHeapMFrame ((n : Nat) : Int) ((seed : Nat) : Int) n
              l lp siv civ) 15)) :
    ∀ μ m : Nat, m + μ = n → ∀ ch : Choices,
    ∃ k : Nat, k ≤ 53 * μ + 65 ∧
      stepFnIter k
        (wSt σ (rHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
          (wcFamily n seed) (wcPre m seed) ((n : Nat) : Int)
          ((m : Nat) : Int) false) 12)
        (.retV (.bool (decide (((m : Nat) : Int) < ((n : Nat) : Int))))
          cpCmpKR) ch
        = .ok (headCR,
            σR σ n ((seed : Nat) : Int) ((n : Nat) : Int) ((n : Nat) : Int)
              (wcFamily n seed) (wcPre n seed) [] 0 true [] 20, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hm ch
    rcases Nat.lt_or_ge m n with hlt | hge
    · rw [show (decide (((m : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      obtain ⟨k, hk, hrun⟩ := ih (μ - 1) (by omega) (m + 1) (by omega) ch
      exact ⟨53 + k, by omega,
        stepFnIter_chain
          (cp_iterR σ n seed ((n : Nat) : Int) m hn hcap hlt ch) hrun⟩
    · have hmn : m = n := by omega
      subst hmn
      rw [show (decide (((m : Nat) : Int) < ((m : Nat) : Int))) = false from
        decide_eq_false (by omega)]
      have hX := cp_X_rawR σ ((m : Nat) : Int) ((seed : Nat) : Int) m
        (wcFamily m seed) (wcPre m seed) ((m : Nat) : Int) ((m : Nat) : Int) ch
      have hent := stepFnIter_one (ch := ch)
        (stepFn_call_enter (plans := [(.chain [], [.ref "best"])])
          (env := callEnvR) (k := rAfterCall) (vals := []) (v := rSliceW m)
          (henter (wcFamily m seed) (wcPre m seed) ((m : Nat) : Int)
            ((m : Nat) : Int)))
      have hpro := r_prologue_rawR σ ((seed : Nat) : Int) m
        (wcFamily m seed) (wcPre m seed) ((m : Nat) : Int) ((m : Nat) : Int) ch
      exact ⟨13 + 1 + 51, by omega,
        stepFnIter_chain (stepFnIter_chain hX hent) hpro⟩

/-! ## The counting phase: the generic layer's discharges at the
r-placement (`S := σR σ L sv siv civ ws lp`, `bArr = 5`, `bMap = 16`,
`base0 = 20`) -/

theorem wcR_init1 (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
      (ch : Choices), 20 ≤ na → DeadFrom dead na →
    stepFn (σR σ L sv siv civ ws lp kvs iv false dead na)
        (.exec (.initialization { id := "$c1", typ := tMap }) env3R
          (.seq [asgnC1, seqnC2, mapAsgnStmt] env3R postBodyKR)) ch
      = .ok (.next (.seq [asgnC1, seqnC2, mapAsgnStmt] (u1EnvR na) postBodyKR),
          σR σ L sv siv civ ws lp kvs iv false
            (dead ++ [(.base ⟨na⟩, nilMapCell)]) (na + 1), ch) := by
  intro kvs iv dead na ch hna hdead
  have hmiss : Heap.lookup
      (frontR L sv siv civ ws lp kvs iv false ++ dead) (.base ⟨na⟩) = none := by
    rw [lookup_append_right
      (lookup_frontR_none L sv siv civ ws lp kvs iv false hna)]
    exact hdead na (Nat.le_refl na)
  have h := stepFn_init_seq (σ := σR σ L sv siv civ ws lp kvs iv false dead na)
    (p := { id := "$c1", typ := tMap })
    (rest := [asgnC1, seqnC2, mapAsgnStmt]) (env := env3R) (k := postBodyKR)
    (ch := ch) (v := .map ⟨none⟩)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show (σR σ L sv siv civ ws lp kvs iv false dead na).nextAddr = na from rfl,
    show (σR σ L sv siv civ ws lp kvs iv false dead na).heap
      = frontR L sv siv civ ws lp kvs iv false ++ dead from rfl,
    set_fresh hmiss, List.append_assoc] at h
  exact h

theorem wcR_st1 (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ na : Nat)
      (ch : Choices), 20 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σR σ L sv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, nilMapCell)]) na)
        (.next (.storeK [.chain (.addr (.base ⟨na₀⟩)) [] []]
          [.map ⟨some (.base ⟨16⟩)⟩] (.seqn #[]) (u1EnvR na₀)
          (.seq [seqnC2, mapAsgnStmt] (u1EnvR na₀) postBodyKR))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (u1EnvR na₀)
            (.seq [seqnC2, mapAsgnStmt] (u1EnvR na₀) postBodyKR)),
          σR σ L sv siv civ ws lp kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhCellR)]) na, ch) := by
  intro kvs iv dead na₀ na ch hna hdead
  have hlook : Heap.lookup
      (σR σ L sv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, nilMapCell)]) na).heap
      (.base ⟨na₀⟩) = some ⟨some tMap, .map ⟨none⟩⟩ := by
    show Heap.lookup
      (frontR L sv siv civ ws lp kvs iv false
        ++ (dead ++ [(.base ⟨na₀⟩, nilMapCell)]))
      (.base ⟨na₀⟩) = some ⟨some tMap, .map ⟨none⟩⟩
    rw [lookup_append_right
        (lookup_frontR_none L sv siv civ ws lp kvs iv false hna),
      lookup_append_right (hdead na₀ (Nat.le_refl na₀))]
    exact lookup_singleton_self
  have h := storeTarget_addr (v := .map ⟨some (.base ⟨16⟩)⟩)
    (v' := .map ⟨some (.base ⟨16⟩)⟩) hlook
    (by simp [normalizeValueForTy, normalizeValueForTyFuel,
      typeResolutionFuel])
  rw [show (σR σ L sv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, nilMapCell)]) na).heap
      = frontR L sv siv civ ws lp kvs iv false
        ++ (dead ++ [(.base ⟨na₀⟩, nilMapCell)]) from rfl,
    set_append_right (lookup_frontR_none L sv siv civ ws lp kvs iv false hna),
    set_append_right (hdead na₀ (Nat.le_refl na₀)),
    set_singleton_self] at h
  exact stepFn_store_step h

theorem wcR_init2 (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ : Nat)
      (ch : Choices), 20 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σR σ L sv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 16)]) (na₀ + 1))
        (.exec (.initialization { id := "$c2", typ := tU64 }) (u1EnvR na₀)
          (.seq [.assign (.var "$c2")
              (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
            (u1EnvR na₀) postBodyKR)) ch
      = .ok (.next (.seq [.assign (.var "$c2")
            (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
            (uEnvR na₀) postBodyKR),
          σR σ L sv siv civ ws lp kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG 16), (.base ⟨na₀ + 1⟩, u64cell 0)])
            (na₀ + 2), ch) := by
  intro kvs iv dead na₀ ch hna hdead
  have hmiss : Heap.lookup
      (frontR L sv siv civ ws lp kvs iv false
        ++ (dead ++ [(.base ⟨na₀⟩, mhG 16)]))
      (.base ⟨na₀ + 1⟩) = none := by
    rw [lookup_append_right
        (lookup_frontR_none L sv siv civ ws lp kvs iv false (by omega)),
      lookup_append_right (hdead (na₀ + 1) (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
    rfl
  have h := stepFn_init_seq
    (σ := σR σ L sv siv civ ws lp kvs iv false
      (dead ++ [(.base ⟨na₀⟩, mhG 16)]) (na₀ + 1))
    (p := { id := "$c2", typ := tU64 })
    (rest := [.assign (.var "$c2")
      (.indexGet (.var "words") (.var "i")), mapAsgnStmt])
    (env := u1EnvR na₀) (k := postBodyKR) (ch := ch) (v := .int 0 .uint64)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show (σR σ L sv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 16)]) (na₀ + 1)).nextAddr = na₀ + 1
      from rfl,
    show (σR σ L sv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 16)]) (na₀ + 1)).heap
      = frontR L sv siv civ ws lp kvs iv false
        ++ (dead ++ [(.base ⟨na₀⟩, mhG 16)]) from rfl,
    set_fresh hmiss, List.append_assoc, List.append_assoc] at h
  exact h

theorem wcR_st2 (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ na : Nat)
      (w : Int) (ch : Choices), 0 ≤ w → w < 2 ^ 64 →
      20 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σR σ L sv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 16), (.base ⟨na₀ + 1⟩, u64cell 0)]) na)
        (.next (.storeK [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []]
          [.int w .uint64] (.seqn #[]) (uEnvR na₀)
          (.seq [mapAsgnStmt] (uEnvR na₀) postBodyKR))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (uEnvR na₀)
            (.seq [mapAsgnStmt] (uEnvR na₀) postBodyKR)),
          σR σ L sv siv civ ws lp kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG 16), (.base ⟨na₀ + 1⟩, u64cell w)])
            na, ch) := by
  intro kvs iv dead na₀ na w ch hw0 hw64 hna hdead
  have hwnorm : IntKind.normalize .uint64 w = w := unorm_of_range hw0 hw64
  have hlook : Heap.lookup
      (σR σ L sv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 16), (.base ⟨na₀ + 1⟩, u64cell 0)])
        na).heap
      (.base ⟨na₀ + 1⟩) = some ⟨some tU64, .int 0 .uint64⟩ := by
    show Heap.lookup
      (frontR L sv siv civ ws lp kvs iv false
        ++ (dead ++ ([(.base ⟨na₀⟩, mhG 16)]
          ++ [(.base ⟨na₀ + 1⟩, u64cell 0)])))
      (.base ⟨na₀ + 1⟩) = some ⟨some tU64, .int 0 .uint64⟩
    rw [lookup_append_right
        (lookup_frontR_none L sv siv civ ws lp kvs iv false (by omega)),
      lookup_append_right (hdead (na₀ + 1) (by omega)),
      lookup_append_right (show Heap.lookup [(.base ⟨na₀⟩, mhG 16)]
          (.base ⟨na₀ + 1⟩) = none from by
        rw [lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
        rfl)]
    exact lookup_singleton_self
  have h := storeTarget_addr (v := .int w .uint64) (v' := .int w .uint64)
    hlook
    (by
      simp only [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel]
      rw [hwnorm]
      rfl)
  rw [show (σR σ L sv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 16), (.base ⟨na₀ + 1⟩, u64cell 0)])
        na).heap
      = frontR L sv siv civ ws lp kvs iv false
        ++ (dead ++ ([(.base ⟨na₀⟩, mhG 16)]
          ++ [(.base ⟨na₀ + 1⟩, u64cell 0)])) from rfl,
    set_append_right
      (lookup_frontR_none L sv siv civ ws lp kvs iv false (by omega)),
    set_append_right (hdead (na₀ + 1) (by omega)),
    set_append_right (show Heap.lookup [(.base ⟨na₀⟩, mhG 16)]
        (.base ⟨na₀ + 1⟩) = none from by
      rw [lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
      rfl),
    set_singleton_self] at h
  exact stepFn_store_step h

theorem wcR_lk1 (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv w : Int)
    (dead : Heap) (na₀ na : Nat) (hna : 20 ≤ na₀)
    (hdead : DeadFrom dead na₀) :
    Heap.lookup (σR σ L sv siv civ ws lp kvs iv false
      (dead ++ [(.base ⟨na₀⟩, mhG 16), (.base ⟨na₀ + 1⟩, u64cell w)]) na).heap
      (.base ⟨na₀⟩) = some mhCellR := by
  show Heap.lookup
    (frontR L sv siv civ ws lp kvs iv false
      ++ (dead ++ ([(.base ⟨na₀⟩, mhCellR)]
        ++ [(.base ⟨na₀ + 1⟩, u64cell w)])))
    (.base ⟨na₀⟩) = some mhCellR
  rw [lookup_append_right
      (lookup_frontR_none L sv siv civ ws lp kvs iv false hna),
    lookup_append_right (hdead na₀ (Nat.le_refl na₀))]
  exact lookup_append_left lookup_singleton_self

theorem wcR_lk2 (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) (iv w : Int)
    (dead : Heap) (na₀ na : Nat) (hna : 20 ≤ na₀)
    (hdead : DeadFrom dead na₀) :
    Heap.lookup (σR σ L sv siv civ ws lp kvs iv false
      (dead ++ [(.base ⟨na₀⟩, mhG 16), (.base ⟨na₀ + 1⟩, u64cell w)]) na).heap
      (.base ⟨na₀ + 1⟩) = some (u64cell w) := by
  show Heap.lookup
    (frontR L sv siv civ ws lp kvs iv false
      ++ (dead ++ ([(.base ⟨na₀⟩, mhCellR)]
        ++ [(.base ⟨na₀ + 1⟩, u64cell w)])))
    (.base ⟨na₀ + 1⟩) = some (u64cell w)
  rw [lookup_append_right
      (lookup_frontR_none L sv siv civ ws lp kvs iv false (by omega)),
    lookup_append_right (hdead (na₀ + 1) (by omega)),
    lookup_append_right (show Heap.lookup [(.base ⟨na₀⟩, mhCellR)]
        (.base ⟨na₀ + 1⟩) = none from by
      rw [lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
      rfl)]
  exact lookup_singleton_self

theorem wcR_var1 (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv w : Int) (dead : Heap) (na₀ na : Nat)
      (k : Cont) (ch : Choices), 20 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σR σ L sv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 16), (.base ⟨na₀ + 1⟩, u64cell w)]) na)
        (.evalE (.var "$c1") (uEnvR na₀) k) ch
      = .ok (.retV (.map ⟨some (.base ⟨16⟩)⟩) k,
          σR σ L sv siv civ ws lp kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG 16), (.base ⟨na₀ + 1⟩, u64cell w)])
            na, ch) := by
  intro kvs iv w dead na₀ na k ch hna hdead
  exact stepFn_var rfl (wcR_lk1 σ L sv siv civ ws lp kvs iv w dead na₀ na hna
    hdead)

theorem wcR_var2 (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv w : Int) (dead : Heap) (na₀ na : Nat)
      (k : Cont) (ch : Choices), 20 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σR σ L sv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 16), (.base ⟨na₀ + 1⟩, u64cell w)]) na)
        (.evalE (.var "$c2") (uEnvR na₀) k) ch
      = .ok (.retV (.int w .uint64) k,
          σR σ L sv siv civ ws lp kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG 16), (.base ⟨na₀ + 1⟩, u64cell w)])
            na, ch) := by
  intro kvs iv w dead na₀ na k ch hna hdead
  exact stepFn_var rfl (wcR_lk2 σ L sv siv civ ws lp kvs iv w dead na₀ na hna
    hdead)

theorem wcR_read (σ : ExecState) (sv siv civ : Int) (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (i : Nat) (dead : Heap) (na : Nat),
      i < ws.length →
    applyStrictOp (σR σ ws.length sv siv civ ws lp kvs ((i : Nat) : Int) false
        dead na) .indexGet
        [wsHG 5 ws.length, .int ((i : Nat) : Int) .int]
      = .ok (.int (ws.getD i 0) .uint64,
          σR σ ws.length sv siv civ ws lp kvs ((i : Nat) : Int) false dead
            na) := by
  intro kvs i dead na hi
  have hget : (⟨ws.map (fun v => .int v .uint64)⟩ : Array GoValue)[0 + i]?
      = some (.int (ws.getD i 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU ws i hi]
  exact applyStrictOp_indexGet_slice (dty := some (.array ws.length tU64))
    (off := 0) (len := ws.length) (cap := ws.length) (ik := .int) rfl
    (Nat.le_refl ws.length) hi hget

theorem wcR_mapGet (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
      (w : Int), 0 ≤ w → w < 2 ^ 64 →
    applyStrictOp (σR σ L sv siv civ ws lp kvs iv false dead na)
        (.mapGet tU64 tU64) [.map ⟨some (.base ⟨16⟩)⟩, .int w .uint64]
      = .ok (.int (cnt kvs w : Int) .uint64,
          σR σ L sv siv civ ws lp kvs iv false dead na) := by
  intro kvs iv dead na w hw0 hw64
  exact applyStrictOp_mapGet (a := ⟨16⟩) (dty := none) rfl
    (unorm_of_range hw0 hw64)

theorem wcR_mapAsgn (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ na : Nat)
      (w : Int) (v : Nat) (ch : Choices), 0 ≤ w → w < 2 ^ 64 → v < 2 ^ 64 →
    stepFn (σR σ L sv siv civ ws lp kvs iv false dead na)
        (.retV (.int ((v : Nat) : Int) .uint64)
          (.stmtOpK (.mapAssign tU64 tU64) 0
            [.int w .uint64, .map ⟨some (.base ⟨16⟩)⟩] []
            (uEnvR na₀) (.seq [] (uEnvR na₀) postBodyKR))) ch
      = .ok (.next (.seq [] (uEnvR na₀) postBodyKR),
          σR σ L sv siv civ ws lp (setk kvs w v) iv false dead na, ch) := by
  intro kvs iv dead na₀ na w v ch hw0 hw64 hv
  have hMA := mapAssignValue_toEntries (a := ⟨16⟩)
    (σ := σR σ L sv siv civ ws lp kvs iv false dead na)
    (v := v) rfl (unorm_of_range hw0 hw64)
    (unorm_of_range (by omega) (by exact_mod_cast hv))
  rw [show Heap.set (σR σ L sv siv civ ws lp kvs iv false dead na).heap
      (.base ⟨16⟩) ⟨none, .mapData (toEntries (setk kvs w v))⟩
      = frontR L sv siv civ ws lp (setk kvs w v) iv false ++ dead
      from rfl] at hMA
  exact stepFn_mapAssign_apply hMA

/-- **One counting iteration** at the r-placement — INSTANTIATED from
`wcIter_generic`. 53 steps. -/
theorem wcR_count_iter (σ : ExecState) (sv siv civ : Int)
    (ws lp : List Int) (i : Nat) (dead : Heap) (na : Nat) (ch : Choices)
    (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64) (hlen : ws.length < 2 ^ 63)
    (hi : i < ws.length) (hna : 20 ≤ na) (hdead : DeadFrom dead na) :
    stepFnIter 53
      (σR σ ws.length sv siv civ ws lp (countsList (ws.take i)) (i : Int)
        false dead na)
      (.retV (.bool true) cmpContCR) ch
      = .ok (headCR,
          σR σ ws.length sv siv civ ws lp (countsList (ws.take (i + 1)))
            (i : Int) false
            (dead ++ [(.base ⟨na⟩, mhCellR),
              (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2), ch) := by
  have hw := hws (ws.getD i 0) (getD_mem hi)
  have hcnt : cnt (countsList (ws.take i)) (ws.getD i 0) + 1 < 2 ^ 64 := by
    have := cnt_take_le (ws := ws) (i := i) (ws.getD i 0)
    omega
  have h := wcIter_generic (σR σ ws.length sv siv civ ws lp) ws 5 16 20
    headCR cmpContCR postBodyKR env3R u1EnvR uEnvR
    (fun kvs iv dead na ch =>
      wcR_segC1_raw σ ws.length sv siv civ ws lp kvs iv dead na ch)
    (wcR_init1 σ ws.length sv siv civ ws lp)
    (fun kvs iv dead na₀ na ch =>
      wcR_segC2_raw σ ws.length sv siv civ ws lp kvs iv dead na₀ na ch)
    (wcR_st1 σ ws.length sv siv civ ws lp)
    (fun kvs iv dead na₀ na ch =>
      wcR_segC3_raw σ ws.length sv siv civ ws lp kvs iv dead na₀ na ch)
    (wcR_init2 σ ws.length sv siv civ ws lp)
    (fun kvs iv dead na₀ na ch =>
      wcR_segC4_raw σ ws.length sv siv civ ws lp kvs iv dead na₀ na ch)
    (wcR_read σ sv siv civ ws lp)
    (fun kvs iv dead na₀ na w ch =>
      wcR_segC5_raw σ ws.length sv siv civ ws lp kvs iv dead na₀ na w ch)
    (wcR_st2 σ ws.length sv siv civ ws lp)
    (fun kvs iv dead na₀ na ch =>
      wcR_segC6_raw σ ws.length sv siv civ ws lp kvs iv dead na₀ na ch)
    (wcR_var1 σ ws.length sv siv civ ws lp)
    (wcR_var2 σ ws.length sv siv civ ws lp)
    (fun kvs iv dead na₀ na ch =>
      wcR_segC7_raw σ ws.length sv siv civ ws lp kvs iv dead na₀ na ch)
    (fun kvs iv dead na₀ na w ch =>
      wcR_segC8_raw σ ws.length sv siv civ ws lp kvs iv dead na₀ na w ch)
    (fun kvs iv dead na₀ na w ch =>
      wcR_segC9_raw σ ws.length sv siv civ ws lp kvs iv dead na₀ na w ch)
    (wcR_mapGet σ ws.length sv siv civ ws lp)
    (fun kvs iv dead na₀ na w cv ch =>
      wcR_segC10_raw σ ws.length sv siv civ ws lp kvs iv dead na₀ na w cv ch)
    (wcR_mapAsgn σ ws.length sv siv civ ws lp)
    (fun kvs iv dead na₀ na ch =>
      wcR_segC11_raw σ ws.length sv siv civ ws lp kvs iv dead na₀ na ch)
    (countsList (ws.take i)) i dead na ch hi hw.1 hw.2 hcnt hna hdead
  rw [show setk (countsList (ws.take i)) (ws.getD i 0)
      (cnt (countsList (ws.take i)) (ws.getD i 0) + 1)
      = countsList (ws.take (i + 1)) from by
    rw [setk_cnt_succ, ← countsList_append_word, ← take_succ_getD hi]] at h
  exact h

theorem wcR_initBest (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
      (ch : Choices), 20 ≤ na → DeadFrom dead na →
    stepFn (σR σ L sv siv civ ws lp kvs iv false dead na)
        (.exec (.initialization { id := "best", typ := tU64 }) envR0R
          (.seq [.assign (.var "best") (.intLit 0 .uint64),
            wcMapRangeStmt, retSeqn] envR0R frameKR)) ch
      = .ok (.next (.seq [.assign (.var "best") (.intLit 0 .uint64),
            wcMapRangeStmt, retSeqn] (envRBR na) frameKR),
          σR σ L sv siv civ ws lp kvs iv false
            (dead ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1), ch) := by
  intro kvs iv dead na ch hna hdead
  have hmiss : Heap.lookup
      (frontR L sv siv civ ws lp kvs iv false ++ dead) (.base ⟨na⟩) = none := by
    rw [lookup_append_right
      (lookup_frontR_none L sv siv civ ws lp kvs iv false hna)]
    exact hdead na (Nat.le_refl na)
  have h := stepFn_init_seq (σ := σR σ L sv siv civ ws lp kvs iv false dead na)
    (p := { id := "best", typ := tU64 })
    (rest := [.assign (.var "best") (.intLit 0 .uint64),
      wcMapRangeStmt, retSeqn])
    (env := envR0R) (k := frameKR) (ch := ch) (v := .int 0 .uint64)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show (σR σ L sv siv civ ws lp kvs iv false dead na).nextAddr = na
      from rfl,
    show (σR σ L sv siv civ ws lp kvs iv false dead na).heap
      = frontR L sv siv civ ws lp kvs iv false ++ dead from rfl,
    set_fresh hmiss, List.append_assoc] at h
  exact h

theorem wcR_stBest (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (B na : Nat)
      (ch : Choices), 20 ≤ B → DeadFrom dead B →
    stepFn (σR σ L sv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨B⟩, u64cell 0)]) na)
        (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
          [.int 0 .uint64] (.seqn #[]) (envRBR B)
          (.seq [wcMapRangeStmt, retSeqn] (envRBR B) frameKR))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envRBR B)
            (.seq [wcMapRangeStmt, retSeqn] (envRBR B) frameKR)),
          σR σ L sv siv civ ws lp kvs iv false
            (dead ++ [(.base ⟨B⟩, u64cell 0)]) na, ch) := by
  intro kvs iv dead B na ch hB hdead
  have hlook : Heap.lookup
      (σR σ L sv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨B⟩, u64cell 0)]) na).heap
      (.base ⟨B⟩) = some ⟨some tU64, .int 0 .uint64⟩ := by
    show Heap.lookup
      (frontR L sv siv civ ws lp kvs iv false
        ++ (dead ++ [(.base ⟨B⟩, u64cell 0)]))
      (.base ⟨B⟩) = some ⟨some tU64, .int 0 .uint64⟩
    rw [lookup_append_right
        (lookup_frontR_none L sv siv civ ws lp kvs iv false hB),
      lookup_append_right (hdead B (Nat.le_refl B))]
    exact lookup_singleton_self
  have h := storeTarget_addr (v := .int 0 .uint64) (v' := .int 0 .uint64)
    hlook
    (by simp [normalizeValueForTy, normalizeValueForTyFuel,
      typeResolutionFuel, IntKind.normalize, IntKind.bits?, IntKind.signed])
  rw [show (σR σ L sv siv civ ws lp kvs iv false
        (dead ++ [(.base ⟨B⟩, u64cell 0)]) na).heap
      = frontR L sv siv civ ws lp kvs iv false
        ++ (dead ++ [(.base ⟨B⟩, u64cell 0)]) from rfl,
    set_append_right (lookup_frontR_none L sv siv civ ws lp kvs iv false hB),
    set_append_right (hdead B (Nat.le_refl B)),
    set_singleton_self] at h
  exact stepFn_store_step h

theorem wcR_snap (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (B na : Nat)
      (ch : Choices),
      (∀ p ∈ kvs, IntKind.normalize .uint64 p.1 = p.1
        ∧ IntKind.normalize .uint64 ((p.2 : Nat) : Int)
            = ((p.2 : Nat) : Int)) →
    stepFn (σR σ L sv siv civ ws lp kvs iv false dead na)
        (.retV (.map ⟨some (.base ⟨16⟩)⟩)
          (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRBR B)
            (kRR B))) ch
      = .ok (.next (.mapIterK none (some "c") tU64 tU64 wcRangeBody
            (toEntries kvs) (envRBR B) (kRR B)),
          σR σ L sv siv civ ws lp kvs iv false dead na, ch) := by
  intro kvs iv dead B na ch hkv
  exact stepFn_snapshot (snapshot_toEntries (a := ⟨16⟩) (dty := none) rfl hkv)

/-- **The counting loop** at the r-placement — INSTANTIATED from
`wcLoop_generic`. -/
theorem wcR_count_loop (σ : ExecState) (sv siv civ : Int)
    (ws lp : List Int)
    (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64) (hlen : ws.length < 2 ^ 63) :
    ∀ (n i : Nat), n = ws.length - i → i ≤ ws.length →
    ∀ (dead : Heap) (na : Nat), 20 ≤ na → DeadFrom dead na →
    ∀ ch : Choices,
    ∃ (k : Nat) (tail : Heap),
      k ≤ 84 * n + 23
      ∧ DeadFrom tail (na + 2 * n + 1)
      ∧ Heap.lookup tail (.base ⟨na + 2 * n⟩) = some (u64cell 0)
      ∧ stepFnIter k
          (σR σ ws.length sv siv civ ws lp (countsList (ws.take i)) (i : Int)
            false dead na)
          (.retV (.bool (decide ((i : Int) < (ws.length : Int)))) cmpContCR)
          ch
        = .ok (.next (.mapIterK none (some "c") tU64 tU64 wcRangeBody
              (toEntries (countsList ws)) (envRBR (na + 2 * n))
              (kRR (na + 2 * n))),
            σR σ ws.length sv siv civ ws lp (countsList ws)
              ((ws.length : Nat) : Int) false tail (na + 2 * n + 1), ch) := by
  intro n i hn hi dead na hna hdead ch
  exact wcLoop_generic (σR σ ws.length sv siv civ ws lp) ws 5 16 20
    headCR cmpContCR frameKR env2R envR0R envRBR kRR hlen
    (fun i dead na ch hi hna hdead =>
      wcR_count_iter σ sv siv civ ws lp i dead na ch hws hlen hi hna hdead)
    (fun kvs iv dead na ch =>
      wcR_segA1_raw σ ws.length sv siv civ ws lp kvs iv dead na ch)
    (fun kvs iv dead na ch =>
      wcR_segX0_raw σ ws.length sv siv civ ws lp kvs iv dead na ch)
    (wcR_initBest σ ws.length sv siv civ ws lp)
    (fun kvs iv dead B na ch =>
      wcR_segX0b_raw σ ws.length sv siv civ ws lp kvs iv dead B na ch)
    (wcR_stBest σ ws.length sv siv civ ws lp)
    (fun kvs iv dead B na ch =>
      wcR_segX0c_raw σ ws.length sv siv civ ws lp kvs iv dead B na ch)
    (wcR_snap σ ws.length sv siv civ ws lp)
    (countsList_norm ws hws hlen)
    n i hn hi dead na hna hdead ch

/-! ## The range phase: the generic layer's discharges at the
r-placement -/

theorem wcR_pick (σ : ExecState) (sv siv civ : Int) (ws lp : List Int) :
    ∀ (kvs rem : List (Int × Nat)) (idx : Nat) (ch ch₂ : Choices)
      (p : Int × Nat) (tail : Heap) (B na : Nat),
      Choices.consume ch rem.length = (idx, ch₂) → idx < rem.length →
      rem[idx]? = some p →
      IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int) →
      20 ≤ na → DeadFrom tail na →
      stepFn (σR σ ws.length sv siv civ ws lp kvs (ws.length : Int) false
          tail na) (rangeHeadR envRBR kRR B rem) ch
        = .ok (.exec wcRangeBody (envIterR envRBR B na)
              (iterKR envRBR kRR B (rem.eraseIdx idx)),
            σR σ ws.length sv siv civ ws lp kvs (ws.length : Int) false
              (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
              (na + 1), ch₂) := by
  intro kvs rem idx ch ch₂ p tail B na hcons hidx hp hvnorm hna htail
  have hmiss : Heap.lookup
      (frontR ws.length sv siv civ ws lp kvs (ws.length : Int) false ++ tail)
      (.base ⟨na⟩) = none := by
    rw [lookup_append_right (lookup_frontR_none ws.length sv siv civ ws lp kvs
      (ws.length : Int) false hna)]
    exact htail na (Nat.le_refl na)
  have hPick := stepFn_pick
    (σ := σR σ ws.length sv siv civ ws lp kvs (ws.length : Int) false tail na)
    (body := wcRangeBody) (env := envRBR B) (k := kRR B)
    hcons hidx hp hvnorm
  rw [show (σR σ ws.length sv siv civ ws lp kvs (ws.length : Int) false tail
        na).nextAddr = na from rfl,
    show (σR σ ws.length sv siv civ ws lp kvs (ws.length : Int) false tail
        na).heap
      = frontR ws.length sv siv civ ws lp kvs (ws.length : Int) false ++ tail
      from rfl,
    set_fresh hmiss, List.append_assoc] at hPick
  exact hPick

theorem wcR_R4b (σ : ExecState) (sv siv civ : Int) (ws lp : List Int) :
    ∀ (kvs rem : List (Int × Nat)) (tail : Heap) (B na₀ na : Nat)
      (ch : Choices),
      stepFnIter 4 (σR σ ws.length sv siv civ ws lp kvs (ws.length : Int)
          false tail na)
          (.next (.seq [.assign (.var "best") (.var "c")]
            (env4R envRBR B na₀)
            (.seq [] (envIfR envRBR B na₀) (iterKR envRBR kRR B rem)))) ch
        = .ok (.evalE (.var "c") (env4R envRBR B na₀)
              (.rhsK .vals [.chain (.addr (.base ⟨B⟩)) [] []] [] []
                (.seqn #[]) (env4R envRBR B na₀)
                (storeBestKR envRBR kRR B na₀ rem)),
            σR σ ws.length sv siv civ ws lp kvs (ws.length : Int) false tail
              na, ch) := by
  intro kvs rem tail B na₀ na ch
  with_unfolding_all rfl

theorem wcR_varC (σ : ExecState) (sv siv civ : Int) (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (tail : Heap) (na₀ na : Nat)
      (v : Int) (env : LocalEnv) (k : Cont) (ch : Choices),
      LocalEnv.lookup env "c" = some (.base ⟨na₀⟩) →
      20 ≤ na₀ → DeadFrom tail na₀ →
      stepFn (σR σ ws.length sv siv civ ws lp kvs (ws.length : Int) false
          (tail ++ [(.base ⟨na₀⟩, ⟨some tU64, .int v .uint64⟩)]) na)
          (.evalE (.var "c") env k) ch
        = .ok (.retV (.int v .uint64) k,
            σR σ ws.length sv siv civ ws lp kvs (ws.length : Int) false
              (tail ++ [(.base ⟨na₀⟩, ⟨some tU64, .int v .uint64⟩)]) na,
            ch) := by
  intro kvs tail na₀ na v env k ch henv hna hdead
  refine stepFn_var (c := ⟨some tU64, .int v .uint64⟩) henv ?_
  show Heap.lookup
    (frontR ws.length sv siv civ ws lp kvs (ws.length : Int) false
      ++ (tail ++ [(.base ⟨na₀⟩, ⟨some tU64, .int v .uint64⟩)]))
    (.base ⟨na₀⟩) = some ⟨some tU64, .int v .uint64⟩
  rw [lookup_append_right (lookup_frontR_none ws.length sv siv civ ws lp kvs
      (ws.length : Int) false hna),
    lookup_append_right (hdead na₀ (Nat.le_refl na₀))]
  exact lookup_singleton_self

theorem wcR_varBest (σ : ExecState) (sv siv civ : Int) (ws lp : List Int) :
    ∀ (kvs : List (Int × Nat)) (tail : Heap) (B na : Nat)
      (bv : Int) (env : LocalEnv) (k : Cont) (ch : Choices),
      LocalEnv.lookup env "best" = some (.base ⟨B⟩) → 20 ≤ B →
      Heap.lookup tail (.base ⟨B⟩) = some (u64cell bv) →
      stepFn (σR σ ws.length sv siv civ ws lp kvs (ws.length : Int) false
          tail na) (.evalE (.var "best") env k) ch
        = .ok (.retV (.int bv .uint64) k,
            σR σ ws.length sv siv civ ws lp kvs (ws.length : Int) false tail
              na, ch) := by
  intro kvs tail B na bv env k ch henv hB hlkB
  refine stepFn_var (c := u64cell bv) henv ?_
  show Heap.lookup
    (frontR ws.length sv siv civ ws lp kvs (ws.length : Int) false ++ tail)
    (.base ⟨B⟩) = some (u64cell bv)
  rw [lookup_append_right (lookup_frontR_none ws.length sv siv civ ws lp kvs
      (ws.length : Int) false hB)]
  exact hlkB

theorem wcR_stB (σ : ExecState) (sv siv civ : Int) (ws lp : List Int) :
    ∀ (kvs rem : List (Int × Nat)) (tail : Heap) (B na₀ na : Nat)
      (bv v : Int) (ch : Choices),
      20 ≤ B → Heap.lookup tail (.base ⟨B⟩) = some (u64cell bv) →
      IntKind.normalize .uint64 v = v →
      stepFn (σR σ ws.length sv siv civ ws lp kvs (ws.length : Int) false
          tail na)
          (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
            [.int v .uint64] (.seqn #[]) (env4R envRBR B na₀)
            (storeBestKR envRBR kRR B na₀ rem))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (env4R envRBR B na₀)
              (storeBestKR envRBR kRR B na₀ rem)),
            σR σ ws.length sv siv civ ws lp kvs (ws.length : Int) false
              (Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int v .uint64⟩) na,
            ch) := by
  intro kvs rem tail B na₀ na bv v ch hB hlkB hvn
  have hlook : Heap.lookup
      (σR σ ws.length sv siv civ ws lp kvs (ws.length : Int) false tail
        na).heap (.base ⟨B⟩) = some ⟨some tU64, .int bv .uint64⟩ := by
    show Heap.lookup
      (frontR ws.length sv siv civ ws lp kvs (ws.length : Int) false ++ tail)
      (.base ⟨B⟩) = some ⟨some tU64, .int bv .uint64⟩
    rw [lookup_append_right (lookup_frontR_none ws.length sv siv civ ws lp kvs
        (ws.length : Int) false hB)]
    exact hlkB
  have h := storeTarget_addr (v := .int v .uint64) (v' := .int v .uint64)
    hlook
    (by
      simp only [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel]
      rw [hvn]
      rfl)
  rw [show (σR σ ws.length sv siv civ ws lp kvs (ws.length : Int) false tail
        na).heap
      = frontR ws.length sv siv civ ws lp kvs (ws.length : Int) false ++ tail
      from rfl,
    set_append_right (lookup_frontR_none ws.length sv siv civ ws lp kvs
      (ws.length : Int) false hB)] at h
  exact stepFn_store_step h

/-- **The range loop, at every choice stream** — INSTANTIATED from
`wcRange_generic` (§10b). -/
theorem wcR_range_loop (σ : ExecState) (sv siv civ : Int)
    (ws lp : List Int) (kvs : List (Int × Nat)) :
    ∀ (m : Nat) (rem : List (Int × Nat)), rem.length = m →
    ∀ (bv : Nat) (B na : Nat) (tail : Heap) (ch : Choices),
    (∀ p ∈ rem, p.2 ≤ ws.length) → ws.length < 2 ^ 63 → bv ≤ ws.length →
    20 ≤ B → B < na →
    Heap.lookup tail (.base ⟨B⟩) = some (u64cell (bv : Int)) →
    DeadFrom tail na →
    ∃ (k : Nat) (ch' : Choices) (tail' : Heap) (na' : Nat),
      k ≤ 24 * m + 1 ∧ na ≤ na'
      ∧ Heap.lookup tail' (.base ⟨B⟩)
          = some (u64cell ((max bv (maxOf (rem.map Prod.snd)) : Nat) : Int))
      ∧ DeadFrom tail' na'
      ∧ stepFnIter k (σR σ ws.length sv siv civ ws lp kvs (ws.length : Int)
          false tail na) (rangeHeadR envRBR kRR B rem) ch
        = .ok (.next (kRR B),
            σR σ ws.length sv siv civ ws lp kvs (ws.length : Int) false tail'
              na', ch') := by
  intro m rem hm bv B na tail ch hrem hlen hbv hB hBna hbest htail
  exact wcRange_generic envRBR kRR (σR σ ws.length sv siv civ ws lp)
    (ws.length : Int) 20 ws.length hlen
    (fun B na₀ => rfl)
    (wcR_pick σ sv siv civ ws lp) (wcR_R4b σ sv siv civ ws lp)
    (wcR_varC σ sv siv civ ws lp) (wcR_varBest σ sv siv civ ws lp)
    (wcR_stB σ sv siv civ ws lp)
    m kvs rem hm bv B na tail ch hrem hbv hB hBna hbest htail

/-! ## The exit phase

The harness epilogue is `$res0 = words; $res1 = best; return`, and the
FIRST of those cannot reduce definitionally — re-normalizing an array
whose contents are a symbolic list is stuck — so the exit splits
`17 + 1 + 15` with the array store conditioned on `storeTarget_addr`
plus `SliceMem.normalizeValueForTy_arr_u64` (the lifted fact). Any S3
harness returning an array hits the same split; minmax hit it first. -/

def rEpiTail : Cont :=
  .seq [.assign (.var "$res1") (.var "best"), .returnStmt] callEnvR
    (.frame [] [] [] [] .stop)
def rRes0Ref : TargetRef := .chain (.addr (.base ⟨2⟩)) [] []

/-- X1: range-loop exit → the `best` read of `$res0 := best`. 6 steps. -/
theorem wcR_segX1_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp r2 : List Int) (kvs : List (Int × Nat)) (r3 r12 r14 : Int)
    (tail : Heap) (B na : Nat) (ch : Choices) :
    stepFnIter 6 (σXR σ L sv siv civ ws lp r2 kvs r3 r12 r14 tail na)
      (.next (kRR B)) ch
      = .ok (.evalE (.var "best") (envRBR B)
            (.rhsK .vals [.chain (.addr (.base ⟨14⟩)) [] []] [] []
              (.seqn #[]) (envRBR B)
              (.seq [.returnStmt] (envRBR B) frameKR)),
          σXR σ L sv siv civ ws lp r2 kvs r3 r12 r14 tail na, ch) := by
  have h1 : stepFnIter 1 (σXR σ L sv siv civ ws lp r2 kvs r3 r12 r14 tail na)
      (.next (kRR B)) ch
      = .ok (.exec retSeqn (envRBR B) (.seq [] (envRBR B) frameKR),
          σXR σ L sv siv civ ws lp r2 kvs r3 r12 r14 tail na, ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σXR σ L sv siv civ ws lp r2 kvs r3 r12 r14 tail na)
    (ss := #[.assign (.var "$res0") (.var "best"), .returnStmt])
    (env := envRBR B) (rest := []) (k := frameKR) (ch := ch))
  have h3 : stepFnIter 4 (σXR σ L sv siv civ ws lp r2 kvs r3 r12 r14 tail na)
      (.next (.seq
        ((#[.assign (.var "$res0") (.var "best"),
          .returnStmt] : Array Stmt).toList ++ [])
        (envRBR B) frameKR)) ch
      = .ok (.evalE (.var "best") (envRBR B)
            (.rhsK .vals [.chain (.addr (.base ⟨14⟩)) [] []] [] []
              (.seqn #[]) (envRBR B)
              (.seq [.returnStmt] (envRBR B) frameKR)),
          σXR σ L sv siv civ ws lp r2 kvs r3 r12 r14 tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- X2a: the `best` value delivered → stored into the subject's `$res0`
(cell 14). 2 steps. -/
theorem wcR_segX2a_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp r2 : List Int) (kvs : List (Int × Nat)) (r3 r12 r14 bvv : Int)
    (tail : Heap) (B na : Nat) (ch : Choices) :
    stepFnIter 2 (σXR σ L sv siv civ ws lp r2 kvs r3 r12 r14 tail na)
      (.retV (.int bvv .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨14⟩)) [] []] [] [] (.seqn #[])
          (envRBR B) (.seq [.returnStmt] (envRBR B) frameKR))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envRBR B)
            (.seq [.returnStmt] (envRBR B) frameKR)),
          σXR σ L sv siv civ ws lp r2 kvs r3 r12
            (IntKind.normalize .uint64 bvv) tail na, ch) := by
  with_unfolding_all rfl

/-- X2b: → the `returnStmt` dispatch point. 2 steps. -/
theorem wcR_segX2b_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp r2 : List Int) (kvs : List (Int × Nat)) (r3 r12 r14 : Int)
    (tail : Heap) (B na : Nat) (ch : Choices) :
    stepFnIter 2 (σXR σ L sv siv civ ws lp r2 kvs r3 r12 r14 tail na)
      (.next (.storeK [] [] (.seqn #[]) (envRBR B)
        (.seq [.returnStmt] (envRBR B) frameKR))) ch
      = .ok (.next (.seq
            (((#[] : Array Stmt).toList) ++ [.returnStmt]) (envRBR B)
            frameKR),
          σXR σ L sv siv civ ws lp r2 kvs r3 r12 r14 tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σXR σ L sv siv civ ws lp r2 kvs r3 r12 r14 tail na)
    (body := .seqn #[]) (env := envRBR B)
    (k := .seq [.returnStmt] (envRBR B) frameKR) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σXR σ L sv siv civ ws lp r2 kvs r3 r12 r14 tail na) (ss := #[])
    (env := envRBR B) (rest := [.returnStmt]) (k := frameKR) (ch := ch))
  exact stepFnIter_chain h1 h2

/-- Exit A: `return`, the subject frame's result read + the `best`
write-back, then the harness epilogue up to the `$res0 = words` store
POINT. 17 steps; the store itself cannot reduce definitionally (the
array's contents are symbolic), which is why it is split out. -/
theorem wcR_exitA_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp r2 : List Int) (kvs : List (Int × Nat)) (r3 r12 r14 : Int)
    (tail : Heap) (B na : Nat) (ch : Choices) :
    stepFnIter 17 (σXR σ L sv siv civ ws lp r2 kvs r3 r12 r14 tail na)
      (.next (.seq (((#[] : Array Stmt).toList) ++ [.returnStmt])
        (envRBR B) frameKR)) ch
      = .ok (.next (.storeK [rRes0Ref]
            [.array ⟨lp.map (fun v => .int v .uint64)⟩] (.seqn #[])
            callEnvR rEpiTail),
          σXR σ L sv siv civ ws lp r2 kvs r3
            (IntKind.normalize .uint64 r14) r14 tail na, ch) := by
  with_unfolding_all rfl

/-- Exit B: `$res1 := best`, return, the harness frame exit — the
driver terminal. 15 steps. -/
theorem wcR_exitB_raw (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp r2 : List Int) (kvs : List (Int × Nat)) (r3 r12 r14 : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 15 (σXR σ L sv siv civ ws lp r2 kvs r3 r12 r14 tail na)
      (.next (.storeK [] [] (.seqn #[]) callEnvR rEpiTail)) ch
      = .ok (.next .stop,
          σXR σ L sv siv civ ws lp r2 kvs
            (IntKind.normalize .uint64 r12) r12 r14 tail na, ch) := by
  with_unfolding_all rfl

theorem lookup_res0_X (σ : ExecState) (L : Nat) (sv siv civ : Int)
    (ws lp r2 : List Int) (kvs : List (Int × Nat)) (r3 r12 r14 : Int)
    (tail : Heap) (na : Nat) :
    Heap.lookup (σXR σ L sv siv civ ws lp r2 kvs r3 r12 r14 tail na).heap
        (.base ⟨2⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨r2.map (fun v => .int v .uint64)⟩⟩ := by
  simp [σXR, wSt, frontXR, Heap.lookup]

/-! ## The run, end to end -/

/-- The pinned program as an empty-heap state — the ONE place this
module carries `wordCountLowered`. -/
def rProg : ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := [], nextAddr := 0 }

/-- The `enterFrame` discharge at the pinned program: the second and
last unfolding of `wordCountLowered` in this module. -/
theorem r_enterFrame_fact (n seed : Nat) (l lp : List Int) (siv civ : Int) :
    enterFrame (wSt rProg (rHeapCall ((n : Nat) : Int) ((seed : Nat) : Int)
        n l lp siv civ) 13) ⟨"maxCount"⟩ [rSliceW n]
      = .ok (maxCountFunc, rFrameEnv, [.base ⟨14⟩],
          wSt rProg (rHeapMFrame ((n : Nat) : Int) ((seed : Nat) : Int)
            n l lp siv civ) 15) := by
  with_unfolding_all rfl

/-- **The harness run, PROGRAM-generic**: within `218·n + 302` steps the
harness reaches the driver terminal with the counted words in `$res0`
and their max multiplicity in `$res1`. -/
theorem r_runs_generic (σ : ExecState) (n seed : Nat) (hcap : n ≤ 8)
    (henter : ∀ (l lp : List Int) (siv civ : Int),
      enterFrame (wSt σ (rHeapCall ((n : Nat) : Int) ((seed : Nat) : Int)
          n l lp siv civ) 13) ⟨"maxCount"⟩ [rSliceW n]
        = .ok (maxCountFunc, rFrameEnv, [.base ⟨14⟩],
            wSt σ (rHeapMFrame ((n : Nat) : Int) ((seed : Nat) : Int)
              n l lp siv civ) 15))
    (ch : Choices) :
    ∃ (k : Nat) (ch' : Choices) (tail : Heap) (na : Nat),
      k ≤ 218 * n + 302 ∧
      stepFnIter k (wSt σ (rHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)) 4)
          rHC0 ch
        = .ok (.next .stop,
            σXR σ n ((seed : Nat) : Int) ((n : Nat) : Int) ((n : Nat) : Int)
              (wcFamily n seed) (wcPre n seed) (wcPre n seed)
              (countsList (wcFamily n seed))
              ((maxMultiplicity (wcFamily n seed) : Nat) : Int)
              ((maxMultiplicity (wcFamily n seed) : Nat) : Int)
              ((maxMultiplicity (wcFamily n seed) : Nat) : Int)
              tail na, ch') := by
  have hn : n < 2 ^ 63 := by omega
  have hws := wcFamily_range n seed
  have hLen : (wcFamily n seed).length = n := wcFamily_length n seed
  have hlen : (wcFamily n seed).length < 2 ^ 63 := by omega
  have hMle : maxMultiplicity (wcFamily n seed) ≤ n := by
    refine maxMult_le (fun v _ => ?_)
    simp only [multiplicity]
    have h1 := List.length_filter_le (· = v) (wcFamily n seed)
    omega
  have hMnorm : IntKind.normalize .uint64
      ((maxMultiplicity (wcFamily n seed) : Nat) : Int)
      = ((maxMultiplicity (wcFamily n seed) : Nat) : Int) :=
    unorm_nat_of_lt (by omega)
  -- entry
  have hE1 := r_E1_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) ch
  have hmk := stepFnIter_one
    (stepFn_makeSlice_u64_step (env := envC11R)
      (k := .seq [rS2, rS3, rS4, rS5, rS6, rS7] envC11R
        (.frame [] [] [] [] .stop))
      (r_make_apply σ ((n : Nat) : Int) ((seed : Nat) : Int) n ch))
  have hE2 := r_E2_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n ch
  have hA0 := su_A0_rawR σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (List.replicate n 0) 0 ch
  have hSU := su_loopR σ n seed hn (n - 0) 0 rfl (by omega) ch
  have hS1 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hE1 hmk) hE2) hA0) hSU
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hS1
  have hX := su_X_rawR σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (wcFamily n seed) ((n : Nat) : Int) ch
  have hS2 := stepFnIter_chain hS1 hX
  -- the copy loop and the call
  have hcA0 := cp_A0_rawR σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (wcFamily n seed) zeros8 ((n : Nat) : Int) 0 ch
  obtain ⟨k₂, hk₂, hcp⟩ := cp_loopR σ n seed hn hcap henter n 0 (by omega) ch
  rw [show wcPre 0 seed = zeros8 from wcPre_zero seed,
    show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hcp
  have hS3 := stepFnIter_chain (stepFnIter_chain hS2 hcA0) hcp
  -- the subject's first exit test
  have hcnt0 := wcR_segA0_raw σ n ((seed : Nat) : Int) ((n : Nat) : Int)
    ((n : Nat) : Int) (wcFamily n seed) (wcPre n seed) [] 0 [] 20 ch
  have hlenap := stepFnIter_one
    (stepFn_strict_apply (done := []) (env := env2R)
      (k := .strictK .lessCmp [.int (0 : Int) .int] [] env2R cmpContCR)
      (ch := ch)
      (applyStrictOp_len_slice
        (σ := σR σ n ((seed : Nat) : Int) ((n : Nat) : Int) ((n : Nat) : Int)
          (wcFamily n seed) (wcPre n seed) [] 0 false [] 20)
        (b := .base ⟨5⟩) (off := 0) (len := n) (cap := n) (elem := tU64)
        (Nat.le_refl n)))
  have hCmp := wcR_cmp_raw σ n ((seed : Nat) : Int) ((n : Nat) : Int)
    ((n : Nat) : Int) (wcFamily n seed) (wcPre n seed) [] 0 0 [] 20 ch
  have hS4 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hS3 hcnt0)
    hlenap) hCmp
  -- the counting loop
  obtain ⟨k₃, tail₁, hk₃, htail₁, hbest₁, hrun₁⟩ :=
    wcR_count_loop σ ((seed : Nat) : Int) ((n : Nat) : Int) ((n : Nat) : Int)
      (wcFamily n seed) (wcPre n seed) hws hlen
      ((wcFamily n seed).length - 0) 0 rfl (by omega) [] 20 (by omega)
      (fun _ _ => rfl) ch
  rw [hLen] at hrun₁ hbest₁ htail₁ hk₃
  have hS5 := stepFnIter_chain hS4 hrun₁
  -- the range loop
  obtain ⟨k₄, ch₄, tail₂, na₂, hk₄, hna₂, hbest₂, htail₂, hrun₂⟩ :=
    wcR_range_loop σ ((seed : Nat) : Int) ((n : Nat) : Int) ((n : Nat) : Int)
      (wcFamily n seed) (wcPre n seed) (countsList (wcFamily n seed))
      (countsList (wcFamily n seed)).length (countsList (wcFamily n seed))
      rfl 0 (20 + 2 * (n - 0)) (20 + 2 * (n - 0) + 1) tail₁ ch
      (fun p hp => by
        have := countsList_val_le (wcFamily n seed) hp
        omega)
      hlen (by omega) (by omega) (by omega) hbest₁ htail₁
  rw [hLen] at hrun₂
  have hS6 := stepFnIter_chain hS5 hrun₂
  rw [show max 0 (maxOf ((countsList (wcFamily n seed)).map Prod.snd))
      = maxMultiplicity (wcFamily n seed) from by
    rw [Nat.zero_max, maxOf_countsList (wcFamily n seed)]] at hbest₂
  -- the exit phase
  have hX1 := wcR_segX1_raw σ n ((seed : Nat) : Int) ((n : Nat) : Int)
    ((n : Nat) : Int) (wcFamily n seed) (wcPre n seed) zeros8
    (countsList (wcFamily n seed)) 0 0 0 tail₂ (20 + 2 * (n - 0)) na₂ ch₄
  have hS7 := stepFnIter_chain hS6 hX1
  have hlkB : Heap.lookup
      (σXR σ n ((seed : Nat) : Int) ((n : Nat) : Int) ((n : Nat) : Int)
        (wcFamily n seed) (wcPre n seed) zeros8
        (countsList (wcFamily n seed)) 0 0 0 tail₂ na₂).heap
      (.base ⟨20 + 2 * (n - 0)⟩)
      = some (u64cell ((maxMultiplicity (wcFamily n seed) : Nat) : Int)) := by
    show Heap.lookup
      (frontXR n ((seed : Nat) : Int) ((n : Nat) : Int) ((n : Nat) : Int)
        (wcFamily n seed) (wcPre n seed) zeros8
        (countsList (wcFamily n seed)) 0 0 0 ++ tail₂)
      (.base ⟨20 + 2 * (n - 0)⟩)
      = some (u64cell ((maxMultiplicity (wcFamily n seed) : Nat) : Int))
    rw [lookup_append_right
      (lookup_frontXR_none n ((seed : Nat) : Int) ((n : Nat) : Int)
        ((n : Nat) : Int) (wcFamily n seed) (wcPre n seed) zeros8
        (countsList (wcFamily n seed)) 0 0 0 (by omega))]
    exact hbest₂
  have hS8 := stepFnIter_chain hS7 (stepFnIter_one
    (stepFn_var (x := "best") (env := envRBR (20 + 2 * (n - 0)))
      (a := ⟨20 + 2 * (n - 0)⟩) (ch := ch₄) rfl hlkB))
  have hX2a := wcR_segX2a_raw σ n ((seed : Nat) : Int) ((n : Nat) : Int)
    ((n : Nat) : Int) (wcFamily n seed) (wcPre n seed) zeros8
    (countsList (wcFamily n seed)) 0 0 0
    ((maxMultiplicity (wcFamily n seed) : Nat) : Int) tail₂
    (20 + 2 * (n - 0)) na₂ ch₄
  rw [hMnorm] at hX2a
  have hS9 := stepFnIter_chain hS8 hX2a
  have hX2b := wcR_segX2b_raw σ n ((seed : Nat) : Int) ((n : Nat) : Int)
    ((n : Nat) : Int) (wcFamily n seed) (wcPre n seed) zeros8
    (countsList (wcFamily n seed)) 0 0
    ((maxMultiplicity (wcFamily n seed) : Nat) : Int) tail₂
    (20 + 2 * (n - 0)) na₂ ch₄
  have hS10 := stepFnIter_chain hS9 hX2b
  have hXA := wcR_exitA_raw σ n ((seed : Nat) : Int) ((n : Nat) : Int)
    ((n : Nat) : Int) (wcFamily n seed) (wcPre n seed) zeros8
    (countsList (wcFamily n seed)) 0 0
    ((maxMultiplicity (wcFamily n seed) : Nat) : Int) tail₂
    (20 + 2 * (n - 0)) na₂ ch₄
  rw [hMnorm] at hXA
  have hS11 := stepFnIter_chain hS10 hXA
  -- the ARRAY store `$res0 = words` (the one conditioned epilogue step)
  have hstore : storeTarget
      (σXR σ n ((seed : Nat) : Int) ((n : Nat) : Int) ((n : Nat) : Int)
        (wcFamily n seed) (wcPre n seed) zeros8
        (countsList (wcFamily n seed)) 0
        ((maxMultiplicity (wcFamily n seed) : Nat) : Int)
        ((maxMultiplicity (wcFamily n seed) : Nat) : Int) tail₂ na₂)
      rRes0Ref (.array ⟨(wcPre n seed).map (fun v => .int v .uint64)⟩)
      = .ok (σXR σ n ((seed : Nat) : Int) ((n : Nat) : Int) ((n : Nat) : Int)
          (wcFamily n seed) (wcPre n seed) (wcPre n seed)
          (countsList (wcFamily n seed)) 0
          ((maxMultiplicity (wcFamily n seed) : Nat) : Int)
          ((maxMultiplicity (wcFamily n seed) : Nat) : Int) tail₂ na₂) :=
    storeTarget_addr
      (lookup_res0_X σ n ((seed : Nat) : Int) ((n : Nat) : Int)
        ((n : Nat) : Int) (wcFamily n seed) (wcPre n seed) zeros8
        (countsList (wcFamily n seed)) 0
        ((maxMultiplicity (wcFamily n seed) : Nat) : Int)
        ((maxMultiplicity (wcFamily n seed) : Nat) : Int) tail₂ na₂)
      (normalizeValueForTy_arr_u64 (wcPre_length hcap) wcPre_range)
  have hS12 := stepFnIter_chain hS11 (stepFnIter_one
    (stepFn_store_step hstore))
  have hXB := wcR_exitB_raw σ n ((seed : Nat) : Int) ((n : Nat) : Int)
    ((n : Nat) : Int) (wcFamily n seed) (wcPre n seed) (wcPre n seed)
    (countsList (wcFamily n seed)) 0
    ((maxMultiplicity (wcFamily n seed) : Nat) : Int)
    ((maxMultiplicity (wcFamily n seed) : Nat) : Int) tail₂ na₂ ch₄
  rw [hMnorm] at hXB
  have hS13 := stepFnIter_chain hS12 hXB
  refine ⟨_, ch₄, tail₂, na₂, ?_, hS13⟩
  have hm : (countsList (wcFamily n seed)).length ≤ n := by
    have := countsList_length_le (wcFamily n seed)
    omega
  omega

/-- **The entry equation**: the machine entry IS its post-prelude
`runConfig` form — `with_unfolding_all rfl` at symbolic `n`, `seed`,
`fuel`, `ch`. -/
theorem rH_entry_eq (n seed fuel : Nat) (ch : Choices) :
    runFunctionWithContextM fuel wordCountLowered.typeDefs.toList
        wordCountLowered.funcs wcHarnessRFunc
        #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
        wordCountLowered.methods ch
      = (do
          let (sF, _) ← runConfig fuel
            (wSt rProg (rHeap0 (IntKind.normalize .uint64 (n : Int))
              (IntKind.normalize .uint64 (seed : Int))) 4) rHC0 ch
          return { values := (← loadMany sF
            [Loc.base ⟨2⟩, Loc.base ⟨3⟩]).toArray }) := by
  with_unfolding_all rfl

/-! ## The user-facing statement -/

/-- **THE HEADLINE (§11 harness form, S3 RELATIONAL)**: for every
`n ≤ 8` and every `seed < 2^64`, running the Go harness
`wordcount_harness_r(n, seed)` through the machine's native function
entry — empty-heap state, both arguments at the call boundary —
completes normally past one fuel bound, at every nondeterminism-choice
stream, and returns TWO values: a length-`n` word list `words` as the
fixed-cap array the Go returns, and `maxMultiplicity words`. The
postcondition is a relation over the RETURNED DATA — no family function
and no closed form appears in it.

Honesty clauses, all recorded rather than hidden:

* **ORDER-INVARIANCE is what makes this claim mean what it looks like.**
  The `for _, c := range counts` loop consumes one choice per iteration,
  so `∀ ch` ranges over every map-iteration order; the equation holds at
  all of them BECAUSE `maxMultiplicity` cannot see the order. Read the
  statement with that in mind: it says "the returned count is the
  greatest multiplicity among the returned words", full stop — a
  spec that named an order-dependent witness would be unprovable here.
* **The cap `n ≤ 8` is a toy bound.** Go's pass-by-value fragment
  cannot return unbounded data, so the harness returns
  `[wordcountCapN]uint64` with `wordcountCapN = 8` (visible in the
  corpus Go) and the copy loop plus zero-padding exist ONLY so the
  counted words can cross the observation boundary.
* **`∃ words` is still family-determined.** The witness is
  `wcFamily n seed`; the statement merely avoids SAYING so. Making the
  input genuine ∀-data needs the ghost rung-1 annotation, which is
  designed and not built. What the S3 swap buys is that the
  POSTCONDITION no longer mentions the family or its solved value —
  `wordcount_ok_v1` states `⌈n/3⌉` via `wcFamily_maxMult`, this states
  `maxMultiplicity words` over what the program returned, and
  `wcFamily_maxMult` is not used at all.
* **Machine idealization** as in the other entries: entry from an empty
  heap, an unbounded heap, allocation always succeeds.

Fuel bound `N = 218·n + 302` — provable from the branch-UNIFORM loop
bounds (`wcRange_generic` charges 24 per range iteration, the cost of
the `c > best` THEN branch, though the else branch costs 12; the
snapshot is bounded by the word count rather than by the ≤3 distinct
family values). The MEASURED step counts are bounded above by
`206·n + 314`, which is tight at `n ≤ 3`; that is an affine upper bound
on the measurements, NOT a law — the true counts are not affine (first
differences 206, 206, 194, because the family `w[i] = seed + i%3` stops
adding new map entries after the third word, so later words are cheaper).
Neither number is presented as the other. -/
theorem wordcount_ok (n seed : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64) :
    ∃ words : List Int, words.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel wordCountLowered.typeDefs.toList
            wordCountLowered.funcs wcHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            wordCountLowered.methods ch
          = .ok { values := #[goArr8 words,
                              .int (maxMultiplicity words : Nat) .uint64] } := by
  refine ⟨wcFamily n seed, wcFamily_length n seed, 218 * n + 302,
    fun fuel hfuel ch => ?_⟩
  obtain ⟨k, ch', tail, na, hk, hrun⟩ :=
    r_runs_generic rProg n seed hcap (r_enterFrame_fact n seed) ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [rH_entry_eq, unorm_of_range (v := (n : Int)) (by omega) (by omega),
    unorm_of_range (v := (seed : Int)) (by omega) (by omega),
    hfold, runConfig_next_stop]
  show (Except.ok { values := #[.array _, .int _ .uint64] } :
      Except GoError Result) = _
  rw [goArr8, ← wcPre_full]

/-- **The D1 run-conditioned twin**: any successful completion of the
harness entry returns those two values. -/
theorem wordcount_readout (n seed : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) :
    ∃ words : List Int, words.length = n ∧
      ∀ (fuel : Nat) (ch : Choices) (r : Result),
        runFunctionWithContextM fuel wordCountLowered.typeDefs.toList
            wordCountLowered.funcs wcHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            wordCountLowered.methods ch
          = .ok r →
        r = { values := #[goArr8 words,
                          .int (maxMultiplicity words : Nat) .uint64] } := by
  obtain ⟨words, hlen, htot⟩ := wordcount_ok n seed hcap hseed
  exact ⟨words, hlen, harness_readout_of_total htot⟩

end GoLean.Examples.WordCount
