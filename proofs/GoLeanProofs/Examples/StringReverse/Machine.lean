import GoLeanProofs.Examples.StringReverse.Pure
import GoLeanProofs.Examples.StringReverseProgram
import GoLeanProofs.StepKit
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StringMem
import GoLeanProofs.EntryEq

/-!
# StringReverse — Machine

The machine-facing layer: the four `Func` records transcribed from the
pinned lowering (each tied to it by an `rfl` pin), the string-op
conditioned facts, the address layout, the environments and
continuations of the three call frames, the heap fronts, and the
entry equation.

**The entry equation was hand-written at landing** (a real finding,
reported to the lane): `derive_entry_eq` failed closed on this
harness — its result defaults are STRINGS, outside `quoteScalarVal`'s
fragment. CLOSED in WP arc s2 item 6: the string result-default arm
was added to the quoter and the equation below is MACRO-DERIVED (same
statement, same `with_unfolding_all rfl` closure).

**What is DIFFERENT about strings, machine-side** (probe-established,
2026-08-15, `.tmp/Probe.lean`): a Go string is a pure VALUE
(`GoValue.string`, a byte array) — there is no backing-array cell, no
handle, no allocation on `+=`. So `len(s)`, `s[i]`, string `+` and
every string store reduce definitionally inside raw segments, and the
ONLY conditioned steps in this example are the three `enterFrame`s and
the pure strict-op facts below (`stringFromRune`, string `indexGet`,
`%`). There is no `storeTarget`/`Heap.lookup` conditioning anywhere.

Address layout (probe-measured at `(n, seed) = (2, 7)`; every raw
segment downstream re-checks the transcription by `rfl`):

```
0 = n            1 = seed         2 = $res0 (string)
3 = $res1 (string)                4 = $res2 (uint64)
5 = pre
-- the buildStr frame (na 6 → 9) --
6 = n'  7 = seed'  8 = $res0'  9 = out  10 = i  11 = $forFirst
12 = post
-- the reverseString frame (na 13 → 15) --
13 = s  14 = $res0''  15 = out'  16 = i'  17 = $forFirst'
18 = isPalin
-- the isStringPalindrome frame (na 19 → 21) --
19 = s'  20 = $res0'''  21 = i''  22 = j  23 = $forFirst''   -- na 24
```
-/

namespace GoLean.Examples.StringReverse

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

abbrev tU64 : Ty := .int .uint64

/-! ## The four `Func` records, verbatim from the pinned lowering -/

/-- `buildStr`: the setup subject — `out += string(rune(97 +
(seed+i)%26))` over a counted uint64 loop. -/
def buildStrFunc : Func :=
  { id := { key := "buildStr" },
    args := #[{ id := "n", typ := tU64 }, { id := "seed", typ := tU64 }],
    results := #[{ id := "$res0", typ := .string }],
    body := .block #[]
      #[.seqn #[.initialization { id := "out", typ := .string },
                .assign (.var "out") (.stringLit { bytes := #[] })],
        .block #[]
          #[.seqn #[.initialization { id := "i", typ := tU64 },
                    .assign (.var "i") (.intLit 0 .uint64)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) buWhileBody]],
        .seqn #[.assign (.var "$res0") (.var "out"), .returnStmt]],
    variadic := false,
    wrapper := false }
  where
    /-- The byte-append store: `out += string(rune(97 + (seed+i)%26))`. -/
    buStoreBlock : Stmt :=
      .block #[]
        #[.assign (.var "out")
            (.add (.var "out")
              (.stringFromRune
                (.convert (.int .int32)
                  (.add (.intLit 97 .uint64)
                    (.mod (.add (.var "seed") (.var "i"))
                      (.intLit 26 .uint64))))))]
    /-- The desugared `for i < n`: first-pass flag, `i++` in the
    dispatch, exit test, body. -/
    buWhileBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
          .seqn #[],
          .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[]) .breakStmt,
          buStoreBlock]

/-- `reverseString`: the subject — walk the bytes from the end,
building the reversal by concatenation. -/
def reverseStringFunc : Func :=
  { id := { key := "reverseString" },
    args := #[{ id := "s", typ := .string }],
    results := #[{ id := "$res0", typ := .string }],
    body := .block #[]
      #[.seqn #[.initialization { id := "out", typ := .string },
                .assign (.var "out") (.stringLit { bytes := #[] })],
        .block #[]
          #[.seqn #[.initialization { id := "i", typ := .int .int },
                    .assign (.var "i")
                      (.sub (.length (.var "s") (some .string))
                        (.intLit 1 .int))],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) rvWhileBody]],
        .seqn #[.assign (.var "$res0") (.var "out"), .returnStmt]],
    variadic := false,
    wrapper := false }
  where
    /-- `out += string(rune(s[i]))` — the machine models the rune
    round-trip FAITHFULLY: a byte `≥ 128` would come back UTF-8
    expanded, which is why the proof carries the ASCII invariant. -/
    rvStoreBlock : Stmt :=
      .block #[]
        #[.assign (.var "out")
            (.add (.var "out")
              (.stringFromRune
                (.convert (.int .int32)
                  (.indexGet (.var "s") (.var "i")))))]
    /-- The desugared `for i ≥ 0`, `i--` in the dispatch. -/
    rvWhileBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "i") (.sub (.var "i") (.intLit 1 .int))),
          .seqn #[],
          .ifThenElse (.atLeastCmp (.var "i") (.intLit 0 .int))
            (.seqn #[]) .breakStmt,
          rvStoreBlock]

/-- `isStringPalindrome`: the companion subject — the two-index inward
byte walk with the early `return 0` on the first mismatched pair. -/
def isStringPalindromeFunc : Func :=
  { id := { key := "isStringPalindrome" },
    args := #[{ id := "s", typ := .string }],
    results := #[{ id := "$res0", typ := tU64 }],
    body := .block #[]
      #[.seqn #[.initialization { id := "i", typ := .int .int },
                .assign (.var "i") (.intLit 0 .int)],
        .seqn #[.initialization { id := "j", typ := .int .int },
                .assign (.var "j")
                  (.sub (.length (.var "s") (some .string))
                    (.intLit 1 .int))],
        .block #[]
          #[.initialization { id := "$forFirst", typ := .bool },
            .assign (.var "$forFirst") (.boolLit true),
            .while (.boolLit true) palWhileBody],
        palTailSeqn],
    variadic := false,
    wrapper := false }
  where
    /-- The `return 0` arm. -/
    palRet0Block : Stmt :=
      .block #[]
        #[.seqn #[.assign (.var "$res0") (.intLit 0 .uint64), .returnStmt]]
    /-- Compare `s[i]` with `s[j]` at `uint8`, then step both indices
    inward. -/
    palBodyBlock : Stmt :=
      .block #[]
        #[.ifThenElse
            (.neqCmp (.int .uint8)
              (.indexGet (.var "s") (.var "i"))
              (.indexGet (.var "s") (.var "j")))
            palRet0Block (.seqn #[]),
          .assign (.var "i") (.add (.var "i") (.intLit 1 .int)),
          .assign (.var "j") (.sub (.var "j") (.intLit 1 .int))]
    /-- The desugared `for i < j` (empty else-arm dispatch: both index
    steps live in the body). -/
    palWhileBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.seqn #[]),
          .seqn #[],
          .ifThenElse (.lessCmp (.var "i") (.var "j")) (.seqn #[]) .breakStmt,
          palBodyBlock]
    /-- The fall-through verdict. -/
    palTailSeqn : Stmt :=
      .seqn #[.assign (.var "$res0") (.intLit 1 .uint64), .returnStmt]

/-- The harness `Func`, restated readably from the guardrails wave's
mechanically-extracted spelling; `strrevHarnessRFunc_pin` ties it to
the lowering by `rfl` (the wave's recorded allowance). -/
def strrevHarnessRFunc : Func :=
  { id := { key := "strrev_harness_r" },
    args := #[{ id := "n", typ := tU64 }, { id := "seed", typ := tU64 }],
    results := #[{ id := "$res0", typ := .string },
                 { id := "$res1", typ := .string },
                 { id := "$res2", typ := tU64 }],
    body := .block #[] #[hS1, hS2, hS3, hS4],
    variadic := false,
    wrapper := false }
  where
    hS1 : Stmt :=
      .seqn #[.initialization { id := "pre", typ := .string },
              .call #[.var "pre"] { key := "buildStr" }
                #[.var "n", .var "seed"]]
    hS2 : Stmt :=
      .seqn #[.initialization { id := "post", typ := .string },
              .call #[.var "post"] { key := "reverseString" }
                #[.var "pre"]]
    hS3 : Stmt :=
      .seqn #[.initialization { id := "isPalin", typ := tU64 },
              .call #[.var "isPalin"] { key := "isStringPalindrome" }
                #[.var "pre"]]
    hS4 : Stmt :=
      .seqn #[.assign (.var "$res0") (.var "pre"),
              .assign (.var "$res1") (.var "post"),
              .assign (.var "$res2") (.var "isPalin"),
              .returnStmt]

/-! ## The lowering pins (the third link of the golden chain) -/

theorem buildStr_pin :
    findFunctionIn? strrevLowered.funcs ⟨"buildStr"⟩
      = some buildStrFunc := rfl

theorem reverseString_pin :
    findFunctionIn? strrevLowered.funcs ⟨"reverseString"⟩
      = some reverseStringFunc := rfl

theorem isStringPalindrome_pin :
    findFunctionIn? strrevLowered.funcs ⟨"isStringPalindrome"⟩
      = some isStringPalindromeFunc := rfl

/-- The harness lowering pin: the readable restatement IS the
frontend's lowering. -/
theorem strrevHarnessRFunc_pin :
    findFunctionIn? strrevLowered.funcs ⟨"strrev_harness_r"⟩
      = some strrevHarnessRFunc := rfl

/-! ## String values, list-side -/

/-- The `GoString` of a byte list — the bridge between the machine's
value and the pure layer's `List UInt8`. STATEMENT vocabulary: the
headline's returned strings are `.string (gs pre)` etc. -/
def gs (l : List UInt8) : GoString := ⟨⟨l⟩⟩

theorem gs_nil : gs [] = GoString.empty := rfl

/-- String `+` at the list spelling — what turns the append the
machine performs into the pure prefix invariant. (Zero-proof
delegation since WP arc s2 item 4 — `StringMem`; the local `gs` def
stays: it is headline vocabulary, and it is definitionally the
kit's.) -/
theorem gs_append (a b : List UInt8) :
    GoString.append (gs a) (gs b) = gs (a ++ b) :=
  StringMem.gs_append a b

/-! ## The string strict-op conditioned facts

-- GAP-WITNESS (see docs/gallery-campaign-log/g1.md § KIT-GAP LIST (strrev)): there is no string
-- vocabulary in `SliceMem`/`StepKit`; these four facts are what a
-- `StringMem` kit module would open with. -/

/-- `string(rune(c))` at an ASCII code point is the one-byte string.
(The general op is the full UTF-8 encoder; `c < 128` is the single-byte
arm, and it is all this example's data ever exercises.) -/
theorem applyStrictOp_stringFromRune_ascii {σ : ExecState} {c : Nat}
    {ik : IntKind} (h : c < 128) :
    applyStrictOp σ .stringFromRune [.int (c : Nat) ik]
      = .ok (.string (gs [UInt8.ofNat c]), σ) :=
  StringMem.applyStrictOp_stringFromRune_ascii h

/-- `s[i]` on a string VALUE: the in-range byte read, at the `getD`
spelling. Pure — the string is an operand, not a heap cell. -/
theorem applyStrictOp_indexGet_string {σ : ExecState} {l : List UInt8}
    {i : Nat} {ik : IntKind} (hi : i < l.length) :
    applyStrictOp σ .indexGet [.string (gs l), .int (i : Nat) ik]
      = .ok (.int ((l.getD i 0).toNat : Nat) .uint8, σ) :=
  StringMem.applyStrictOp_indexGet_string hi

/-- `int32` normalization is the identity on `0 ≤ v < 2^31` — the
`rune(...)` conversions this example performs (byte values). -/
theorem i32norm_of_range {v : Int} (h0 : 0 ≤ v) (h1 : v < 2 ^ 31) :
    IntKind.normalize .int32 v = v :=
  SliceMem.normalize_of_range_signed (bits := 31) rfl rfl (by omega) h1

/-- The `Nat`-cast corner of `i32norm_of_range`. -/
theorem i32norm_nat_of_lt {x : Nat} (h : x < 2 ^ 31) :
    IntKind.normalize .int32 (x : Int) = (x : Int) :=
  i32norm_of_range (by omega) (by exact_mod_cast h)

/-! ## Cells -/

abbrev su64 (v : Int) : HeapCell := ⟨some tU64, .int v .uint64⟩
abbrev sint (v : Int) : HeapCell := ⟨some (.int .int), .int v .int⟩
abbrev sbool (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
abbrev sstr (v : GoString) : HeapCell := ⟨some .string, .string v⟩

/-! ## The PROGRAM-generic state form -/

abbrev sSt (σ : ExecState) (H : Heap) (na : Nat) : ExecState :=
  { σ with heap := H, nextAddr := na }

/-! ## Environments -/

def baseScopeS : Scope :=
  [("$res2", .base ⟨4⟩), ("$res1", .base ⟨3⟩), ("$res0", .base ⟨2⟩),
   ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]
def hScope1 : Scope := [("pre", .base ⟨5⟩)]
def hEnv1 : LocalEnv := [hScope1, baseScopeS]
def hScope2 : Scope := [("post", .base ⟨12⟩), ("pre", .base ⟨5⟩)]
def hEnv2 : LocalEnv := [hScope2, baseScopeS]
def hScope3 : Scope :=
  [("isPalin", .base ⟨18⟩), ("post", .base ⟨12⟩), ("pre", .base ⟨5⟩)]
def hEnv3 : LocalEnv := [hScope3, baseScopeS]

def buFScope : Scope :=
  [("$res0", .base ⟨8⟩), ("seed", .base ⟨7⟩), ("n", .base ⟨6⟩)]
def buFrameEnv : LocalEnv := [buFScope]
def buEnv : LocalEnv :=
  [[("$forFirst", .base ⟨11⟩)], [("i", .base ⟨10⟩)],
   [("out", .base ⟨9⟩)], buFScope]
def buEnv2 : LocalEnv := [] :: [] :: buEnv

def revFScope : Scope := [("$res0", .base ⟨14⟩), ("s", .base ⟨13⟩)]
def revFrameEnv : LocalEnv := [revFScope]
def revEnv : LocalEnv :=
  [[("$forFirst", .base ⟨17⟩)], [("i", .base ⟨16⟩)],
   [("out", .base ⟨15⟩)], revFScope]
def revEnv2 : LocalEnv := [] :: [] :: revEnv

def pFScope : Scope := [("$res0", .base ⟨20⟩), ("s", .base ⟨19⟩)]
def pFrameEnv : LocalEnv := [pFScope]
def pEnvIJ : LocalEnv :=
  [("j", .base ⟨22⟩), ("i", .base ⟨21⟩)] :: pFrameEnv
def pEnvIn : LocalEnv := [("$forFirst", .base ⟨23⟩)] :: pEnvIJ
def pEnvC : LocalEnv := [] :: pEnvIn
def pEnvB2 : LocalEnv := [] :: pEnvC

/-! ## Continuations — the harness half -/

def frameStop : Cont := .frame [] [] [] [] .stop

def buShapes : List (TargetShape × List Expr) := [(.chain [], [.ref "pre"])]
def revShapes : List (TargetShape × List Expr) := [(.chain [], [.ref "post"])]
def palShapes : List (TargetShape × List Expr) :=
  [(.chain [], [.ref "isPalin"])]

def hAfterBu : Cont :=
  .seq [strrevHarnessRFunc.hS2, strrevHarnessRFunc.hS3,
        strrevHarnessRFunc.hS4] hEnv1 frameStop
def hAfterRev : Cont :=
  .seq [strrevHarnessRFunc.hS3, strrevHarnessRFunc.hS4] hEnv2 frameStop
def hAfterPal : Cont := .seq [strrevHarnessRFunc.hS4] hEnv3 frameStop

/-- The `buildStr` call's argument point, first argument banked. -/
def buCallK1 (nv : Int) : Cont :=
  .callArgsK ⟨"buildStr"⟩ buShapes [.int nv .uint64] [] hEnv1 hAfterBu
def revCallK0 : Cont :=
  .callArgsK ⟨"reverseString"⟩ revShapes [] [] hEnv2 hAfterRev
def palCallK0 : Cont :=
  .callArgsK ⟨"isStringPalindrome"⟩ palShapes [] [] hEnv3 hAfterPal

def buFrameK : Cont := .frame buShapes hEnv1 [.base ⟨8⟩] [] hAfterBu false
def revFrameK : Cont := .frame revShapes hEnv2 [.base ⟨14⟩] [] hAfterRev false
def palFrameK : Cont := .frame palShapes hEnv3 [.base ⟨20⟩] [] hAfterPal false

/-! ## Continuations — the `buildStr` frame -/

def buTailSeqn : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "out"), .returnStmt]
def buHeadTail : Cont :=
  .seq [] buEnv
    (.seq [] [[("i", .base ⟨10⟩)], [("out", .base ⟨9⟩)], buFScope]
      (.seq [buTailSeqn] [[("out", .base ⟨9⟩)], buFScope] buFrameK))
def buHeadCfg : Config :=
  .exec (.while (.boolLit true) buildStrFunc.buWhileBody) buEnv buHeadTail
def buLoopK : Cont :=
  .loop (.boolLit true) buildStrFunc.buWhileBody buEnv buHeadTail
def buCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: buEnv)
    (.seq [buildStrFunc.buStoreBlock] ([] :: buEnv) buLoopK)
def buStTail : Cont := .seq [] buEnv2 (.seq [] ([] :: buEnv) buLoopK)
def buOutRef : TargetRef := .chain (.addr (.base ⟨9⟩)) [] []
def buRhsK : Cont := .rhsK .vals [buOutRef] [] [] (.seqn #[]) buEnv2 buStTail
def buAppK (ov : GoString) : Cont :=
  .strictK .add [.string ov] [] buEnv2 buRhsK
def buRuneK (ov : GoString) : Cont :=
  .strictK .stringFromRune [] [] buEnv2 (buAppK ov)
def buConvK (ov : GoString) : Cont :=
  .strictK (.convert (.int .int32)) [] [] buEnv2 (buRuneK ov)
def buA97K (ov : GoString) : Cont :=
  .strictK .add [.int 97 .uint64] [] buEnv2 (buConvK ov)
/-- The `%` apply point: divisor delivered, the wrapped `seed+i` sum
banked. -/
def buModK (ov : GoString) (x : Int) : Cont :=
  .strictK .mod [.int x .uint64] [] buEnv2 (buA97K ov)

/-! ## Continuations — the `reverseString` frame -/

def revTailSeqn : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "out"), .returnStmt]
def revHeadTail : Cont :=
  .seq [] revEnv
    (.seq [] [[("i", .base ⟨16⟩)], [("out", .base ⟨15⟩)], revFScope]
      (.seq [revTailSeqn] [[("out", .base ⟨15⟩)], revFScope] revFrameK))
def revHeadCfg : Config :=
  .exec (.while (.boolLit true) reverseStringFunc.rvWhileBody) revEnv
    revHeadTail
def revLoopK : Cont :=
  .loop (.boolLit true) reverseStringFunc.rvWhileBody revEnv revHeadTail
def revCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: revEnv)
    (.seq [reverseStringFunc.rvStoreBlock] ([] :: revEnv) revLoopK)
def revStTail : Cont := .seq [] revEnv2 (.seq [] ([] :: revEnv) revLoopK)
def revOutRef : TargetRef := .chain (.addr (.base ⟨15⟩)) [] []
def revRhsK : Cont :=
  .rhsK .vals [revOutRef] [] [] (.seqn #[]) revEnv2 revStTail
def revAppK (ov : GoString) : Cont :=
  .strictK .add [.string ov] [] revEnv2 revRhsK
def revRuneK (ov : GoString) : Cont :=
  .strictK .stringFromRune [] [] revEnv2 (revAppK ov)
def revConvK (ov : GoString) : Cont :=
  .strictK (.convert (.int .int32)) [] [] revEnv2 (revRuneK ov)
/-- The `s[i]` apply point inside the reverse body, `s` banked. -/
def revIdxK (ov : GoString) (l : List UInt8) : Cont :=
  .strictK .indexGet [.string (gs l)] [] revEnv2 (revConvK ov)

/-! ## Continuations — the `isStringPalindrome` frame -/

def pHeadTail : Cont :=
  .seq [] pEnvIn (.seq [isStringPalindromeFunc.palTailSeqn] pEnvIJ palFrameK)
def pHeadCfg : Config :=
  .exec (.while (.boolLit true) isStringPalindromeFunc.palWhileBody) pEnvIn
    pHeadTail
def pLoopK : Cont :=
  .loop (.boolLit true) isStringPalindromeFunc.palWhileBody pEnvIn pHeadTail
def pCmpIfK : Cont :=
  .ifK (.seqn #[]) .breakStmt pEnvC
    (.seq [isStringPalindromeFunc.palBodyBlock] pEnvC pLoopK)
def pNeIfK : Cont :=
  .ifK isStringPalindromeFunc.palRet0Block (.seqn #[]) pEnvB2
    (.seq [.assign (.var "i") (.add (.var "i") (.intLit 1 .int)),
           .assign (.var "j") (.sub (.var "j") (.intLit 1 .int))] pEnvB2
      (.seq [] pEnvC pLoopK))
/-- The FIRST byte read's apply point (`s[i]`), the second pending. -/
def pIdx1K (l : List UInt8) : Cont :=
  .strictK .indexGet [.string (gs l)] [] pEnvB2
    (.strictK (.neqCmp (.int .uint8)) []
      [.indexGet (.var "s") (.var "j")] pEnvB2 pNeIfK)
/-- The SECOND byte read's apply point (`s[j]`), the first banked. -/
def pIdx2K (l : List UInt8) (a : Int) : Cont :=
  .strictK .indexGet [.string (gs l)] [] pEnvB2
    (.strictK (.neqCmp (.int .uint8)) [.int a .uint8] [] pEnvB2 pNeIfK)

/-! ## Heap fronts (program-generic) -/

def sHeap0 (nv sv : Int) : Heap :=
  [(.base ⟨0⟩, su64 nv), (.base ⟨1⟩, su64 sv),
   (.base ⟨2⟩, sstr GoString.empty), (.base ⟨3⟩, sstr GoString.empty),
   (.base ⟨4⟩, su64 0)]

def sHeapPre (nv sv : Int) : Heap :=
  sHeap0 nv sv ++ [(.base ⟨5⟩, sstr GoString.empty)]

/-- The `buildStr` frame's parameter/result cells (`bnv`/`bsv` are the
frame's own copies — the composition instantiates all four at the same
`↑n`/`↑seed`). -/
def sHeapBF (nv sv bnv bsv : Int) : Heap :=
  sHeapPre nv sv ++
    [(.base ⟨6⟩, su64 bnv), (.base ⟨7⟩, su64 bsv),
     (.base ⟨8⟩, sstr GoString.empty)]

/-- The build loop's state: accumulator `ov`, counter `iv`, flag. -/
def sHeapBu (nv sv bnv bsv : Int) (ov : GoString) (iv : Int) (ffv : Bool) :
    Heap :=
  sHeapBF nv sv bnv bsv ++
    [(.base ⟨9⟩, sstr ov), (.base ⟨10⟩, su64 iv), (.base ⟨11⟩, sbool ffv)]

/-- After the `buildStr` frame: the built string delivered into `pre`
(and left in the dead frame cells), `post` declared. From here on the
built bytes are a LIST `l` (the family, at the assembly). -/
def sHeapBX (nv sv bnv bsv : Int) (l : List UInt8) (biv : Int) : Heap :=
  [(.base ⟨0⟩, su64 nv), (.base ⟨1⟩, su64 sv),
   (.base ⟨2⟩, sstr GoString.empty), (.base ⟨3⟩, sstr GoString.empty),
   (.base ⟨4⟩, su64 0), (.base ⟨5⟩, sstr (gs l)),
   (.base ⟨6⟩, su64 bnv), (.base ⟨7⟩, su64 bsv), (.base ⟨8⟩, sstr (gs l)),
   (.base ⟨9⟩, sstr (gs l)), (.base ⟨10⟩, su64 biv),
   (.base ⟨11⟩, sbool false), (.base ⟨12⟩, sstr GoString.empty)]

/-- The `reverseString` frame's cells. -/
def sHeapRF (nv sv bnv bsv : Int) (l : List UInt8) (biv : Int) : Heap :=
  sHeapBX nv sv bnv bsv l biv ++
    [(.base ⟨13⟩, sstr (gs l)), (.base ⟨14⟩, sstr GoString.empty)]

/-- The reverse loop's state: accumulator `rov`, down-counter `riv`. -/
def sHeapRev (nv sv bnv bsv : Int) (l : List UInt8) (biv : Int)
    (rov : GoString) (riv : Int) (ffv : Bool) : Heap :=
  sHeapRF nv sv bnv bsv l biv ++
    [(.base ⟨15⟩, sstr rov), (.base ⟨16⟩, sint riv), (.base ⟨17⟩, sbool ffv)]

/-- After the `reverseString` frame: the reversal delivered into
`post` (and the dead frame cells), `isPalin` declared. -/
def sHeapRX (nv sv bnv bsv : Int) (l : List UInt8) (biv : Int)
    (rov : GoString) (riv : Int) : Heap :=
  [(.base ⟨0⟩, su64 nv), (.base ⟨1⟩, su64 sv),
   (.base ⟨2⟩, sstr GoString.empty), (.base ⟨3⟩, sstr GoString.empty),
   (.base ⟨4⟩, su64 0), (.base ⟨5⟩, sstr (gs l)),
   (.base ⟨6⟩, su64 bnv), (.base ⟨7⟩, su64 bsv), (.base ⟨8⟩, sstr (gs l)),
   (.base ⟨9⟩, sstr (gs l)), (.base ⟨10⟩, su64 biv),
   (.base ⟨11⟩, sbool false), (.base ⟨12⟩, sstr rov),
   (.base ⟨13⟩, sstr (gs l)), (.base ⟨14⟩, sstr rov),
   (.base ⟨15⟩, sstr rov), (.base ⟨16⟩, sint riv), (.base ⟨17⟩, sbool false),
   (.base ⟨18⟩, su64 0)]

/-- The `isStringPalindrome` frame's cells. -/
def sHeapPF (nv sv bnv bsv : Int) (l : List UInt8) (biv : Int)
    (rov : GoString) (riv : Int) : Heap :=
  sHeapRX nv sv bnv bsv l biv rov riv ++
    [(.base ⟨19⟩, sstr (gs l)), (.base ⟨20⟩, su64 0)]

/-- The palindrome loop's state. -/
def sHeapPal (nv sv bnv bsv : Int) (l : List UInt8) (biv : Int)
    (rov : GoString) (riv : Int) (piv pjv : Int) (ffv : Bool) : Heap :=
  sHeapPF nv sv bnv bsv l biv rov riv ++
    [(.base ⟨21⟩, sint piv), (.base ⟨22⟩, sint pjv),
     (.base ⟨23⟩, sbool ffv)]

/-- The terminal heap: verdict `vv` (a literal `0`/`1` at the branch
lemmas) in the subject's result cell, `isPalin`, and `$res2`; the
observed triple in cells `2`/`3`/`4`. -/
def sHeapEnd (nv sv bnv bsv : Int) (l : List UInt8) (biv : Int)
    (rov : GoString) (riv : Int) (piv pjv vv : Int) : Heap :=
  [(.base ⟨0⟩, su64 nv), (.base ⟨1⟩, su64 sv),
   (.base ⟨2⟩, sstr (gs l)), (.base ⟨3⟩, sstr rov),
   (.base ⟨4⟩, su64 vv), (.base ⟨5⟩, sstr (gs l)),
   (.base ⟨6⟩, su64 bnv), (.base ⟨7⟩, su64 bsv), (.base ⟨8⟩, sstr (gs l)),
   (.base ⟨9⟩, sstr (gs l)), (.base ⟨10⟩, su64 biv),
   (.base ⟨11⟩, sbool false), (.base ⟨12⟩, sstr rov),
   (.base ⟨13⟩, sstr (gs l)), (.base ⟨14⟩, sstr rov),
   (.base ⟨15⟩, sstr rov), (.base ⟨16⟩, sint riv), (.base ⟨17⟩, sbool false),
   (.base ⟨18⟩, su64 vv), (.base ⟨19⟩, sstr (gs l)), (.base ⟨20⟩, su64 vv),
   (.base ⟨21⟩, sint piv), (.base ⟨22⟩, sint pjv),
   (.base ⟨23⟩, sbool false)]

/-! ## The entry equation (macro-derived since WP arc s2 item 6 — the
string result-default arm closed the gap that made this module
hand-write it) -/

def sProg : ExecState :=
  { types := strrevLowered.typeDefs.toList,
    functions := strrevLowered.funcs,
    methods := strrevLowered.methods,
    heap := [], nextAddr := 0 }

derive_entry_eq sH_entry_eq strrevLowered strrevHarnessRFunc sHSeed sHC0 sProg

/-! ## The three `enterFrame` discharges (the only program-consulting
steps outside the entry) -/

/-- `buildStr(n, seed)` frame entry at the pinned program. -/
theorem bu_enterFrame_fact (nv sv : Int) (h6 : IntKind.normalize .uint64 nv = nv)
    (h7 : IntKind.normalize .uint64 sv = sv) :
    enterFrame (sSt sProg (sHeapPre nv sv) 6) ⟨"buildStr"⟩
        [.int nv .uint64, .int sv .uint64]
      = .ok (buildStrFunc, buFrameEnv, [.base ⟨8⟩],
          sSt sProg (sHeapBF nv sv nv sv) 9) := by
  have hraw : enterFrame (sSt sProg (sHeapPre nv sv) 6) ⟨"buildStr"⟩
        [.int nv .uint64, .int sv .uint64]
      = .ok (buildStrFunc, buFrameEnv, [.base ⟨8⟩],
          sSt sProg (sHeapBF nv sv (IntKind.normalize .uint64 nv)
            (IntKind.normalize .uint64 sv)) 9) := by
    with_unfolding_all rfl
  rw [hraw, h6, h7]

/-- `reverseString(pre)` frame entry at the pinned program. -/
theorem rev_enterFrame_fact (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) :
    enterFrame (sSt sProg (sHeapBX nv sv bnv bsv l biv) 13)
        ⟨"reverseString"⟩ [.string (gs l)]
      = .ok (reverseStringFunc, revFrameEnv, [.base ⟨14⟩],
          sSt sProg (sHeapRF nv sv bnv bsv l biv) 15) := by
  with_unfolding_all rfl

/-- `isStringPalindrome(pre)` frame entry at the pinned program. -/
theorem pal_enterFrame_fact (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (rov : GoString) (riv : Int) :
    enterFrame (sSt sProg (sHeapRX nv sv bnv bsv l biv rov riv) 19)
        ⟨"isStringPalindrome"⟩ [.string (gs l)]
      = .ok (isStringPalindromeFunc, pFrameEnv, [.base ⟨20⟩],
          sSt sProg (sHeapPF nv sv bnv bsv l biv rov riv) 21) := by
  with_unfolding_all rfl

end GoLean.Examples.StringReverse
