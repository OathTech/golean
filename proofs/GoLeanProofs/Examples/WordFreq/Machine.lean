import GoLeanProofs.Examples.WordFreq.Pure
import GoLeanProofs.Examples.WordFreqProgram
import GoLeanProofs.StepKit
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StringMem
import GoLeanProofs.SliceMem

/-!
# WordFreq — Machine

The machine-facing layer shared by every run shard: the four `Func`
records transcribed from the pinned lowering (each tied to it by an
`rfl` pin), the string strict-op facts, the state formers and cell
vocabulary, the whole-heap freshness predicate, the hand-written entry
equation, and the three `enterFrame` discharges.

**Why the entry equation is hand-written**: as in
`StringReverse.Machine`, `derive_entry_eq` fails closed on this harness
— two of its result defaults are STRINGS, and the macro's
`quoteScalarVal` quotes scalar/array/nil-slice/nil-map defaults only.
The theorem below is exactly the shape the macro's program-generic form
emits, transcribed by hand, and closes by the same
`with_unfolding_all rfl`.

**Address layout** (probe-measured at `(n, seed, qsel) = (2, 1, 0)`,
tracer `.tmp/e5-drafts/trace-2-1-0.txt`; every raw segment downstream
re-checks the transcription by `rfl`):

```
0 = n      1 = seed   2 = qsel
3 = $res0 (string)    4 = $res1 (string)
5 = $res2 (uint64)    6 = $res3 (uint64)
7 = pre
-- the buildText frame (na 8 → 11) --
8 = n'   9 = seed'  10 = $res0'  11 = out  12 = i  13 = $forFirst
14 = q   15 = hits  16 = best (harness)
-- the wordFreq frame (na 17 → 21) --
17 = text  18 = query  19 = $res0''  20 = $res1''  21 = words
-- the shim frame (na 22 → 24) --
22 = s   23 = $res0'''
24 = $c15 (handle)  25 = $c15 backing ([]string, len 0 cap 0)
26 = out (handle)   27 = i  28 = start  29 = inField  30 = $forFirst
-- from 31 on the scan loop allocates per iteration (w, c, and on the
-- long letter path c1, c2; per append $c16 handle + backing, $c17
-- handle, and on a SPILL a fresh out backing) — every post-30 address
-- is run- and CHOICE-dependent (append spills consume capacity
-- choices), so all post-shim placement is symbolic (footprint style).
```

The count/range phases (`Count.lean`, `Range.lean`) run at a symbolic
post-shim base: the shim's exit `nextAddr` depends on the choice
stream, so `$c0`/map-data/`counts`/`i`/`$forFirst`/`best` live at
symbolic offsets and every heap access there is a conditioned step.
-/

namespace GoLean.Examples.WordFreq

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

abbrev tU64 : Ty := .int .uint64
abbrev tInt : Ty := .int .int
abbrev tU8 : Ty := .int .uint8
abbrev tStr : Ty := .string
abbrev tSlS : Ty := .slice .string
abbrev tMapSU : Ty := .map .string tU64

/-! ## The four `Func` records, verbatim from the pinned lowering -/

/-- `buildText`: the setup subject — `out := " "`, then per `i < n` the
letter `string(rune(97 + (seed+i)%3))` and a separator chosen by
`i % 3` (one space / two spaces / a tab). -/
def buildTextFunc : Func :=
  { id := { key := "buildText" },
    args := #[{ id := "n", typ := tU64 }, { id := "seed", typ := tU64 }],
    results := #[{ id := "$res0", typ := tStr }],
    body := .block #[]
      #[.seqn #[.initialization { id := "out", typ := tStr },
                .assign (.var "out") (.stringLit { bytes := #[32] })],
        .block #[]
          #[.seqn #[.initialization { id := "i", typ := tU64 },
                    .assign (.var "i") (.intLit 0 .uint64)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) btWhileBody]],
        .seqn #[.assign (.var "$res0") (.var "out"), .returnStmt]],
    variadic := false,
    wrapper := false }
  where
    /-- `out += string(rune(97 + (seed+i)%3))`. -/
    btLetterStmt : Stmt :=
      .assign (.var "out")
        (.add (.var "out")
          (.stringFromRune
            (.convert (.int .int32)
              (.add (.intLit 97 .uint64)
                (.mod (.add (.var "seed") (.var "i"))
                  (.intLit 3 .uint64))))))
    /-- One separator arm: `out += lit`. -/
    btSepArm (bytesLit : Array UInt8) : Stmt :=
      .block #[]
        #[.assign (.var "out")
            (.add (.var "out") (.stringLit { bytes := bytesLit }))]
    /-- The `i % 3` separator selection. -/
    btSepIf : Stmt :=
      .ifThenElse
        (.eqCmp tU64
          (.mod (.var "i") (.intLit 3 .uint64))
          (.intLit 0 .uint64))
        (btSepArm #[32])
        (.ifThenElse
          (.eqCmp tU64
            (.mod (.var "i") (.intLit 3 .uint64))
            (.intLit 1 .uint64))
          (btSepArm #[32, 32])
          (btSepArm #[9]))
    /-- The loop-body store block. -/
    btStoreBlock : Stmt := .block #[] #[btLetterStmt, btSepIf]
    /-- The desugared `for i < n`: first-pass flag, `i++` in the
    dispatch, exit test, body. -/
    btWhileBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
          .seqn #[],
          .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[]) .breakStmt,
          btStoreBlock]

/-- `wordFreq`: the subject — split via the injected shim, count into a
`map[string]uint64`, read the query, max over the values by
`for _, c := range counts`. -/
def wordFreqFunc : Func :=
  { id := { key := "wordFreq" },
    args := #[{ id := "text", typ := tStr }, { id := "query", typ := tStr }],
    results := #[{ id := "$res0", typ := tU64 }, { id := "$res1", typ := tU64 }],
    body := .block #[]
      #[.seqn #[.initialization { id := "words", typ := tSlS },
                .call #[.var "words"] { key := "goleanShimStringsFields" }
                  #[.var "text"]],
        .seqn #[.initialization { id := "$c0", typ := tMapSU },
                .makeMap (.var "$c0") tStr tU64 none],
        .seqn #[.initialization { id := "counts", typ := tMapSU },
                .assign (.var "counts") (.var "$c0")],
        .block #[]
          #[.seqn #[.initialization { id := "i", typ := tInt },
                    .assign (.var "i") (.intLit 0 .int)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) wfWhileBody]],
        .seqn #[.initialization { id := "best", typ := tU64 },
                .assign (.var "best") (.intLit 0 .uint64)],
        .mapRange none (some "c") (.var "counts") tStr tU64 wfRangeBody,
        .seqn #[.assign (.var "$res0")
                  (.mapGet (.var "counts") (.var "query") tStr tU64),
                .assign (.var "$res1") (.var "best"),
                .returnStmt]],
    variadic := false,
    wrapper := false }
  where
    /-- One counting step: `counts[words[i]]++` in its desugared
    temp-and-`mapAssign` form. -/
    wfCountBody : Stmt :=
      .block #[]
        #[.seqn #[.initialization { id := "$c1", typ := tMapSU },
                  .assign (.var "$c1") (.var "counts")],
          .seqn #[.initialization { id := "$c2", typ := tStr },
                  .assign (.var "$c2")
                    (.indexGet (.var "words") (.var "i"))],
          .mapAssign (.var "$c1") (.var "$c2")
            (.add (.mapGet (.var "$c1") (.var "$c2") tStr tU64)
              (.intLit 1 .uint64))
            tStr tU64]
    /-- The counting loop's desugared body. -/
    wfWhileBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "i") (.add (.var "i") (.intLit 1 .int))),
          .seqn #[],
          .ifThenElse
            (.lessCmp (.var "i") (.length (.var "words") (some tSlS)))
            (.seqn #[]) .breakStmt,
          wfCountBody]
    /-- The range body: `if c > best { best = c }`. -/
    wfRangeBody : Stmt :=
      .block #[]
        #[.ifThenElse (.greaterCmp (.var "c") (.var "best"))
            (.block #[] #[.seqn #[.assign (.var "best") (.var "c")]])
            (.seqn #[])]

/-- The harness `Func`: `pre := buildText(n, seed)`, the query letter,
`hits, best := wordFreq(pre, q)`, all four returned as data. -/
def wordfreqHarnessRFunc : Func :=
  { id := { key := "wordfreq_harness_r" },
    args := #[{ id := "n", typ := tU64 }, { id := "seed", typ := tU64 },
              { id := "qsel", typ := tU64 }],
    results := #[{ id := "$res0", typ := tStr }, { id := "$res1", typ := tStr },
                 { id := "$res2", typ := tU64 }, { id := "$res3", typ := tU64 }],
    body := .block #[] #[hS1, hS2, hS3, hS4],
    variadic := false,
    wrapper := false }
  where
    hS1 : Stmt :=
      .seqn #[.initialization { id := "pre", typ := tStr },
              .call #[.var "pre"] { key := "buildText" }
                #[.var "n", .var "seed"]]
    hS2 : Stmt :=
      .seqn #[.initialization { id := "q", typ := tStr },
              .assign (.var "q")
                (.stringFromRune
                  (.convert (.int .int32)
                    (.add (.intLit 97 .uint64)
                      (.mod (.var "qsel") (.intLit 3 .uint64)))))]
    hS3 : Stmt :=
      .seqn #[.initialization { id := "hits", typ := tU64 },
              .initialization { id := "best", typ := tU64 },
              .call #[.var "hits", .var "best"] { key := "wordFreq" }
                #[.var "pre", .var "q"]]
    hS4 : Stmt :=
      .seqn #[.assign (.var "$res0") (.var "pre"),
              .assign (.var "$res1") (.var "q"),
              .assign (.var "$res2") (.var "hits"),
              .assign (.var "$res3") (.var "best"),
              .returnStmt]

/-- `goleanShimStringsFields`: the injected `strings.Fields` shim — the
byte scan over the full Unicode White_Space class, appending
`s[start:i]` segments to a `[]string`. -/
def goleanShimStringsFieldsFunc : Func :=
  { id := { key := "goleanShimStringsFields" },
    args := #[{ id := "s", typ := tStr }],
    results := #[{ id := "$res0", typ := tSlS }],
    body := .block #[]
      #[.seqn #[.initialization { id := "$c15", typ := tSlS },
                .makeSlice (.var "$c15") tStr (.intLit 0 .int)
                  (some (.intLit 0 .int))],
        .seqn #[.initialization { id := "out", typ := tSlS },
                .assign (.var "out") (.var "$c15")],
        .seqn #[.initialization { id := "i", typ := tInt },
                .assign (.var "i") (.intLit 0 .int)],
        .seqn #[.initialization { id := "start", typ := tInt },
                .assign (.var "start") (.intLit 0 .int)],
        .seqn #[.initialization { id := "inField", typ := .bool },
                .assign (.var "inField") (.boolLit false)],
        .block #[]
          #[.initialization { id := "$forFirst", typ := .bool },
            .assign (.var "$forFirst") (.boolLit true),
            .while (.boolLit true) scWhileBody],
        .ifThenElse (.var "inField") scTailAppend (.seqn #[]),
        .seqn #[.assign (.var "$res0") (.var "out"), .returnStmt]],
    variadic := false,
    wrapper := false }
  where
    /-- `c == lit` at uint8. -/
    scEq (e : Expr) (v : Int) : Expr :=
      .eqCmp tU8 e (.intLit v .uint8)
    /-- The 1-byte class: `c == 32 || c == 9 || … || c == 13`. -/
    scCond1 : Expr :=
      .or (.or (.or (.or (.or
        (scEq (.var "c") 32)
        (scEq (.var "c") 9))
        (scEq (.var "c") 10))
        (scEq (.var "c") 11))
        (scEq (.var "c") 12))
        (scEq (.var "c") 13)
    /-- The 2-byte class: `c == 194 && i+1 < len(s) && (s[i+1] == 133
    || s[i+1] == 160)`. -/
    scCond2 : Expr :=
      .and
        (.and (scEq (.var "c") 194)
          (.lessCmp (.add (.var "i") (.intLit 1 .int))
            (.length (.var "s") (some tStr))))
        (.or
          (scEq (.indexGet (.var "s")
            (.add (.var "i") (.intLit 1 .int))) 133)
          (scEq (.indexGet (.var "s")
            (.add (.var "i") (.intLit 1 .int))) 160))
    /-- The 3-byte class over the loaded `c1`/`c2`. -/
    scCond3 : Expr :=
      .or (.or (.or
        (.and (.and (scEq (.var "c") 225) (scEq (.var "c1") 154))
          (scEq (.var "c2") 128))
        (.and (.and (scEq (.var "c") 226) (scEq (.var "c1") 128))
          (.or (.or (.or
            (.and (.atLeastCmp (.var "c2") (.intLit 128 .uint8))
              (.atMostCmp (.var "c2") (.intLit 138 .uint8)))
            (scEq (.var "c2") 168))
            (scEq (.var "c2") 169))
            (scEq (.var "c2") 175))))
        (.and (.and (scEq (.var "c") 226) (scEq (.var "c1") 129))
          (scEq (.var "c2") 159)))
        (.and (.and (scEq (.var "c") 227) (scEq (.var "c1") 128))
          (scEq (.var "c2") 128))
    /-- The 3-byte probe block: load `c1`, `c2`, test `scCond3`. -/
    scC3Block : Stmt :=
      .block #[]
        #[.seqn #[.initialization { id := "c1", typ := tU8 },
                  .assign (.var "c1")
                    (.indexGet (.var "s")
                      (.add (.var "i") (.intLit 1 .int)))],
          .seqn #[.initialization { id := "c2", typ := tU8 },
                  .assign (.var "c2")
                    (.indexGet (.var "s")
                      (.add (.var "i") (.intLit 2 .int)))],
          .ifThenElse scCond3
            (.block #[]
              #[.seqn #[.assign (.var "w") (.intLit 3 .int)]])
            (.seqn #[])]
    /-- The width classifier: the three `if` levels writing `w`. -/
    scClassify : Stmt :=
      .ifThenElse scCond1
        (.block #[] #[.seqn #[.assign (.var "w") (.intLit 1 .int)]])
        (.ifThenElse scCond2
          (.block #[] #[.seqn #[.assign (.var "w") (.intLit 2 .int)]])
          (.ifThenElse
            (.lessCmp (.add (.var "i") (.intLit 2 .int))
              (.length (.var "s") (some tStr)))
            scC3Block
            (.seqn #[])))
    /-- The in-loop append: `$c16 := make([]string, 1, 1);
    $c16[0] = s[start:i]; $c17 := append(out, $c16...); out = $c17;
    inField = false`. -/
    scAppendBlock : Stmt :=
      .block #[]
        #[.seqn #[.initialization { id := "$c16", typ := tSlS },
                  .makeSlice (.var "$c16") tStr (.intLit 1 .int)
                    (some (.intLit 1 .int)),
                  .assign
                    (.addr (.indexAddr (.var "$c16") (.intLit 0 .int)))
                    (.slice (.var "s") (.var "start") (.var "i") none)],
          .seqn #[.initialization { id := "$c17", typ := tSlS },
                  .appendSlice (.var "$c17") tStr (.var "out")
                    (.var "$c16")],
          .seqn #[.assign (.var "out") (.var "$c17")],
          .seqn #[.assign (.var "inField") (.boolLit false)]]
    /-- The separator arm: close the open field, `i += w`. -/
    scSepArm : Stmt :=
      .block #[]
        #[.ifThenElse (.var "inField") scAppendBlock (.seqn #[]),
          .assign (.var "i") (.add (.var "i") (.var "w"))]
    /-- The field-content arm: open a field if none, `i += 1`. -/
    scLetterArm : Stmt :=
      .block #[]
        #[.ifThenElse (.not (.var "inField"))
            (.block #[]
              #[.seqn #[.assign (.var "start") (.var "i")],
                .seqn #[.assign (.var "inField") (.boolLit true)]])
            (.seqn #[]),
          .assign (.var "i") (.add (.var "i") (.intLit 1 .int))]
    /-- The per-byte body: `w := 0; c := s[i]`, classify, branch on
    `w > 0`. -/
    scByteBlock : Stmt :=
      .block #[]
        #[.seqn #[.initialization { id := "w", typ := tInt },
                  .assign (.var "w") (.intLit 0 .int)],
          .seqn #[.initialization { id := "c", typ := tU8 },
                  .assign (.var "c")
                    (.indexGet (.var "s") (.var "i"))],
          scClassify,
          .ifThenElse (.greaterCmp (.var "w") (.intLit 0 .int))
            scSepArm scLetterArm]
    /-- The desugared `for i < len(s)` (empty else-arm dispatch: the
    index steps live in the body arms). -/
    scWhileBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.seqn #[]),
          .seqn #[],
          .ifThenElse
            (.lessCmp (.var "i") (.length (.var "s") (some tStr)))
            (.seqn #[]) .breakStmt,
          scByteBlock]
    /-- The trailing `if inField` append (`s[start:len(s)]`). -/
    scTailAppend : Stmt :=
      .block #[]
        #[.seqn #[.initialization { id := "$c18", typ := tSlS },
                  .makeSlice (.var "$c18") tStr (.intLit 1 .int)
                    (some (.intLit 1 .int)),
                  .assign
                    (.addr (.indexAddr (.var "$c18") (.intLit 0 .int)))
                    (.slice (.var "s") (.var "start")
                      (.length (.var "s") (some tStr)) none)],
          .seqn #[.initialization { id := "$c19", typ := tSlS },
                  .appendSlice (.var "$c19") tStr (.var "out")
                    (.var "$c18")],
          .seqn #[.assign (.var "out") (.var "$c19")]]

/-! ## The lowering pins (the third link of the golden chain) -/

theorem buildText_pin :
    findFunctionIn? wordfreqLowered.funcs ⟨"buildText"⟩
      = some buildTextFunc := rfl

theorem wordFreq_pin :
    findFunctionIn? wordfreqLowered.funcs ⟨"wordFreq"⟩
      = some wordFreqFunc := rfl

theorem wordfreqHarnessRFunc_pin :
    findFunctionIn? wordfreqLowered.funcs ⟨"wordfreq_harness_r"⟩
      = some wordfreqHarnessRFunc := rfl

theorem goleanShimStringsFields_pin :
    findFunctionIn? wordfreqLowered.funcs ⟨"goleanShimStringsFields"⟩
      = some goleanShimStringsFieldsFunc := rfl

/-! ## String values, list-side -/

/-- The `GoString` of a byte list — the bridge between the machine's
value and the pure layer's `List UInt8` (the `StringReverse.Machine`
spelling, re-declared: statement vocabulary is deliberately not shared
across examples — the §11 closure rule). -/
def gs (l : List UInt8) : GoString := ⟨⟨l⟩⟩

theorem gs_nil : gs [] = GoString.empty := rfl

/-- String `+` at the list spelling. -/
theorem gs_append (a b : List UInt8) :
    GoString.append (gs a) (gs b) = gs (a ++ b) :=
  -- zero-proof delegation since WP arc s2 item 4 (`StringMem`); the
  -- local `gs` stays — headline vocabulary, definitionally the kit's
  StringMem.gs_append a b

/-! ## The string strict-op conditioned facts

-- GAP-WITNESS: no string vocabulary in `SliceMem`/`StepKit`; these
-- are the `StringMem` facts `StringReverse.Machine` first recorded,
-- re-derived at this example (2nd consumer — promotion candidate),
-- plus the SUBSTRING fact (`s[lo:hi]`), new here. -/

/-- `string(rune(c))` at an ASCII code point is the one-byte string. -/
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

/-- `len(s)` on a string VALUE. -/
theorem applyStrictOp_len_string {σ : ExecState} {l : List UInt8} :
    applyStrictOp σ (.lengthOf (some tStr)) [.string (gs l)]
      = .ok (.int (l.length : Nat) .int, σ) :=
  StringMem.applyStrictOp_len_string

/-- The SUBSTRING fact: `s[lo:hi]` on a string value, in bounds, is the
byte sublist `(l.drop lo).take (hi - lo)` — pure, no allocation (a Go
string slice shares no mutable state the machine models). -/
theorem applyStrictOp_slice_string {σ : ExecState} {l : List UInt8}
    {lo hi : Nat} {ik ik' : IntKind}
    (h1 : lo ≤ hi) (h2 : hi ≤ l.length) :
    applyStrictOp σ (.sliceExpr false)
      [.string (gs l), .int (lo : Nat) ik, .int (hi : Nat) ik']
      = .ok (.string (gs ((l.drop lo).take (hi - lo))), σ) :=
  StringMem.applyStrictOp_slice_string h1 h2

/-- `int32` normalization is the identity on `0 ≤ v < 2^31`. -/
theorem i32norm_of_range {v : Int} (h0 : 0 ≤ v) (h1 : v < 2 ^ 31) :
    IntKind.normalize .int32 v = v :=
  SliceMem.normalize_of_range_signed (bits := 31) rfl rfl (by omega) h1

/-- The `Nat`-cast corner of `i32norm_of_range`. -/
theorem i32norm_nat_of_lt {x : Nat} (h : x < 2 ^ 31) :
    IntKind.normalize .int32 (x : Int) = (x : Int) :=
  i32norm_of_range (by omega) (by exact_mod_cast h)

/-! ## Cells -/

abbrev su64 (v : Int) : HeapCell := ⟨some tU64, .int v .uint64⟩
abbrev sint (v : Int) : HeapCell := ⟨some tInt, .int v .int⟩
abbrev su8 (v : Int) : HeapCell := ⟨some tU8, .int v .uint8⟩
abbrev sbool (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
abbrev sstr (v : GoString) : HeapCell := ⟨some tStr, .string v⟩

/-- A `[]string` handle value. -/
abbrev slsVal (b : Nat) (off len cap : Nat) : GoValue :=
  .slice ⟨some (.base ⟨b⟩), off, len, cap⟩
/-- A `[]string` handle cell. -/
abbrev slsCell (b : Nat) (off len cap : Nat) : HeapCell :=
  ⟨some tSlS, slsVal b off len cap⟩
/-- The nil `[]string` cell (a slice variable's default). -/
abbrev slsNil : HeapCell := ⟨some tSlS, .slice ⟨none, 0, 0, 0⟩⟩

/-- The `[]string` backing-array VALUE holding the byte lists `fs`
padded with empty strings to capacity `cap`. -/
def strArr (fs : List (List UInt8)) (cap : Nat) : GoValue :=
  .array ⟨(fs.map (fun f => GoValue.string (gs f)))
    ++ List.replicate (cap - fs.length) (GoValue.string GoString.empty)⟩

/-- The `[]string` backing-array CELL at declared type `[cap]string`. -/
abbrev strArrCell (fs : List (List UInt8)) (cap : Nat) : HeapCell :=
  ⟨some (.array cap tStr), strArr fs cap⟩

/-! ## The state former (footprint style) and whole-heap freshness -/

/-- The PROGRAM-generic state form: `σ` carries the program context,
the heap and allocator are pinned. -/
abbrev wSt (σ : ExecState) (H : Heap) (na : Nat) : ExecState :=
  { σ with heap := H, nextAddr := na }

-- Whole-heap freshness is the kit's `DeadFrom` (same shape as the
-- FibMemo/Stein `FreshFrom`); `DeadFrom.push`/`push2` are the kit's.

/-! ## Heap fronts, entry through the shim prologue (concrete
addresses 0–30; every post-30 address is run/choice-dependent) -/

/-- The post-prelude front: arguments and result defaults. -/
def wHeap0 (nv sv qv : Int) : Heap :=
  [(.base ⟨0⟩, su64 nv), (.base ⟨1⟩, su64 sv), (.base ⟨2⟩, su64 qv),
   (.base ⟨3⟩, sstr GoString.empty), (.base ⟨4⟩, sstr GoString.empty),
   (.base ⟨5⟩, su64 0), (.base ⟨6⟩, su64 0)]

/-- `pre` declared. -/
def wHeapPre (nv sv qv : Int) : Heap :=
  wHeap0 nv sv qv ++ [(.base ⟨7⟩, sstr GoString.empty)]

/-- The `buildText` frame's cells. -/
def wHeapBF (nv sv qv bnv bsv : Int) : Heap :=
  wHeapPre nv sv qv ++
    [(.base ⟨8⟩, su64 bnv), (.base ⟨9⟩, su64 bsv),
     (.base ⟨10⟩, sstr GoString.empty)]

/-- The build loop's state: accumulator `ov`, counter `iv`, flag. -/
def wHeapBt (nv sv qv bnv bsv : Int) (ov : GoString) (iv : Int)
    (ffv : Bool) : Heap :=
  wHeapBF nv sv qv bnv bsv ++
    [(.base ⟨11⟩, sstr ov), (.base ⟨12⟩, su64 iv), (.base ⟨13⟩, sbool ffv)]

/-- After the `buildText` frame: the built bytes `l` delivered into
`pre` (and left in the dead frame cells), `q` declared. -/
def wHeapBX (nv sv qv bnv bsv : Int) (l : List UInt8) (biv : Int) : Heap :=
  [(.base ⟨0⟩, su64 nv), (.base ⟨1⟩, su64 sv), (.base ⟨2⟩, su64 qv),
   (.base ⟨3⟩, sstr GoString.empty), (.base ⟨4⟩, sstr GoString.empty),
   (.base ⟨5⟩, su64 0), (.base ⟨6⟩, su64 0), (.base ⟨7⟩, sstr (gs l)),
   (.base ⟨8⟩, su64 bnv), (.base ⟨9⟩, su64 bsv), (.base ⟨10⟩, sstr (gs l)),
   (.base ⟨11⟩, sstr (gs l)), (.base ⟨12⟩, su64 biv),
   (.base ⟨13⟩, sbool false), (.base ⟨14⟩, sstr GoString.empty)]

/-- `q` stored, `hits`/`best` declared (the `wordFreq` call point). -/
def wHeapCall (nv sv qv bnv bsv : Int) (l q : List UInt8) (biv : Int) :
    Heap :=
  [(.base ⟨0⟩, su64 nv), (.base ⟨1⟩, su64 sv), (.base ⟨2⟩, su64 qv),
   (.base ⟨3⟩, sstr GoString.empty), (.base ⟨4⟩, sstr GoString.empty),
   (.base ⟨5⟩, su64 0), (.base ⟨6⟩, su64 0), (.base ⟨7⟩, sstr (gs l)),
   (.base ⟨8⟩, su64 bnv), (.base ⟨9⟩, su64 bsv), (.base ⟨10⟩, sstr (gs l)),
   (.base ⟨11⟩, sstr (gs l)), (.base ⟨12⟩, su64 biv),
   (.base ⟨13⟩, sbool false), (.base ⟨14⟩, sstr (gs q)),
   (.base ⟨15⟩, su64 0), (.base ⟨16⟩, su64 0)]

/-- The `wordFreq` frame's cells. -/
def wHeapWF (nv sv qv bnv bsv : Int) (l q : List UInt8) (biv : Int) :
    Heap :=
  wHeapCall nv sv qv bnv bsv l q biv ++
    [(.base ⟨17⟩, sstr (gs l)), (.base ⟨18⟩, sstr (gs q)),
     (.base ⟨19⟩, su64 0), (.base ⟨20⟩, su64 0)]

/-- `words` declared (the shim call point). -/
def wHeapWords (nv sv qv bnv bsv : Int) (l q : List UInt8) (biv : Int) :
    Heap :=
  wHeapWF nv sv qv bnv bsv l q biv ++ [(.base ⟨21⟩, slsNil)]

/-- The shim frame's cells. -/
def wHeapShim (nv sv qv bnv bsv : Int) (l q : List UInt8) (biv : Int) :
    Heap :=
  wHeapWords nv sv qv bnv bsv l q biv ++
    [(.base ⟨22⟩, sstr (gs l)), (.base ⟨23⟩, slsNil)]

/-- The scan loop's front (post-prologue): the `out` handle at
`(b, 0, k, cap)` over a symbolic backing address, position `iv`, field
start `sv2`, the in-field flag, the first-pass flag. Cells 0–30; the
backing array and all scan debris live PAST this front. -/
def wHeapScan (nv sv qv bnv bsv : Int) (l q : List UInt8) (biv : Int)
    (b k cap : Nat) (iv sv2 : Int) (fv ffv : Bool) : Heap :=
  wHeapShim nv sv qv bnv bsv l q biv ++
    [(.base ⟨24⟩, slsCell 25 0 0 0), (.base ⟨25⟩, strArrCell [] 0),
     (.base ⟨26⟩, slsCell b 0 k cap), (.base ⟨27⟩, sint iv),
     (.base ⟨28⟩, sint sv2), (.base ⟨29⟩, sbool fv),
     (.base ⟨30⟩, sbool ffv)]

/-- No front address reaches 31 (the scan-phase freshness seed). -/
theorem lookup_wHeapScan_none (nv sv qv bnv bsv : Int)
    (l q : List UInt8) (biv : Int) (b k cap : Nat) (iv sv2 : Int)
    (fv ffv : Bool) {x : Nat} (hx : 31 ≤ x) :
    Heap.lookup
        (wHeapScan nv sv qv bnv bsv l q biv b k cap iv sv2 fv ffv)
        (.base ⟨x⟩)
      = none := by
  simp only [wHeapScan, wHeapShim, wHeapWords, wHeapWF, wHeapCall,
    List.append_assoc, List.cons_append, List.nil_append, Heap.lookup,
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
    base_beq_false (by omega : (20 : Nat) ≠ x),
    base_beq_false (by omega : (21 : Nat) ≠ x),
    base_beq_false (by omega : (22 : Nat) ≠ x),
    base_beq_false (by omega : (23 : Nat) ≠ x),
    base_beq_false (by omega : (24 : Nat) ≠ x),
    base_beq_false (by omega : (25 : Nat) ≠ x),
    base_beq_false (by omega : (26 : Nat) ≠ x),
    base_beq_false (by omega : (27 : Nat) ≠ x),
    base_beq_false (by omega : (28 : Nat) ≠ x),
    base_beq_false (by omega : (29 : Nat) ≠ x),
    base_beq_false (by omega : (30 : Nat) ≠ x),
    Bool.false_eq_true, if_false]

/-! ## Environments (harness level; frame-local envs live in the
phase shards) -/

def baseScopeW : Scope :=
  [("$res3", .base ⟨6⟩), ("$res2", .base ⟨5⟩), ("$res1", .base ⟨4⟩),
   ("$res0", .base ⟨3⟩), ("qsel", .base ⟨2⟩), ("seed", .base ⟨1⟩),
   ("n", .base ⟨0⟩)]
def hScope1 : Scope := [("pre", .base ⟨7⟩)]
def hEnv1 : LocalEnv := [hScope1, baseScopeW]
def hScope2 : Scope := [("q", .base ⟨14⟩), ("pre", .base ⟨7⟩)]
def hEnv2 : LocalEnv := [hScope2, baseScopeW]
def hScope3 : Scope :=
  [("best", .base ⟨16⟩), ("hits", .base ⟨15⟩), ("q", .base ⟨14⟩),
   ("pre", .base ⟨7⟩)]
def hEnv3 : LocalEnv := [hScope3, baseScopeW]

def frameStop : Cont := .frame [] [] [] [] .stop

def btShapes : List (TargetShape × List Expr) := [(.chain [], [.ref "pre"])]
def wfShapes : List (TargetShape × List Expr) :=
  [(.chain [], [.ref "hits"]), (.chain [], [.ref "best"])]

def hAfterBt : Cont :=
  .seq [wordfreqHarnessRFunc.hS2, wordfreqHarnessRFunc.hS3,
        wordfreqHarnessRFunc.hS4] hEnv1 frameStop
def hAfterWf : Cont := .seq [wordfreqHarnessRFunc.hS4] hEnv3 frameStop

/-- The `buildText` call's argument point, first argument banked. -/
def btCallK1 (nv : Int) : Cont :=
  .callArgsK ⟨"buildText"⟩ btShapes [.int nv .uint64] [] hEnv1 hAfterBt
/-- The `wordFreq` call's argument point, `pre` banked, `q` delivered. -/
def wfCallK1 (l : List UInt8) : Cont :=
  .callArgsK ⟨"wordFreq"⟩ wfShapes [.string (gs l)] [] hEnv3 hAfterWf

/-- The `buildText` frame continuation. -/
def btFrameK : Cont := .frame btShapes hEnv1 [.base ⟨10⟩] [] hAfterBt
/-- The `wordFreq` frame continuation. -/
def wfFrameK : Cont :=
  .frame wfShapes hEnv3 [.base ⟨19⟩, .base ⟨20⟩] [] hAfterWf

def btFrameEnv : LocalEnv :=
  [[("$res0", .base ⟨10⟩), ("seed", .base ⟨9⟩), ("n", .base ⟨8⟩)]]
def wfFrameScope : Scope :=
  [("$res1", .base ⟨20⟩), ("$res0", .base ⟨19⟩), ("query", .base ⟨18⟩),
   ("text", .base ⟨17⟩)]
def wfFrameEnv : LocalEnv := [wfFrameScope]
def shimFrameScope : Scope :=
  [("$res0", .base ⟨23⟩), ("s", .base ⟨22⟩)]
def shimFrameEnv : LocalEnv := [shimFrameScope]

/-- The shim call's argument point inside `wordFreq` (env: `words`
declared over the frame scope). -/
def wfWordsScope : Scope := [("words", .base ⟨21⟩)]
def wfEnvW : LocalEnv := [wfWordsScope, wfFrameScope]
def shimShapes : List (TargetShape × List Expr) :=
  [(.chain [], [.ref "words"])]
/-- The `wordFreq` body's statements after the shim call (the shim
frame returns into this sequence). -/
def wfAfterShim : Cont :=
  .seq [.seqn #[.initialization { id := "$c0", typ := tMapSU },
                .makeMap (.var "$c0") tStr tU64 none],
        .seqn #[.initialization { id := "counts", typ := tMapSU },
                .assign (.var "counts") (.var "$c0")],
        .block #[]
          #[.seqn #[.initialization { id := "i", typ := tInt },
                    .assign (.var "i") (.intLit 0 .int)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) wordFreqFunc.wfWhileBody]],
        .seqn #[.initialization { id := "best", typ := tU64 },
                .assign (.var "best") (.intLit 0 .uint64)],
        .mapRange none (some "c") (.var "counts") tStr tU64
          wordFreqFunc.wfRangeBody,
        .seqn #[.assign (.var "$res0")
                  (.mapGet (.var "counts") (.var "query") tStr tU64),
                .assign (.var "$res1") (.var "best"),
                .returnStmt]]
    wfEnvW wfFrameK
/-- The shim frame continuation. -/
def shimFrameK : Cont := .frame shimShapes wfEnvW [.base ⟨23⟩] [] wfAfterShim

/-! ## The entry equation (hand-written; the macro fails closed on
string result defaults, as in `StringReverse.Machine`) -/

/-- The pinned program as an empty-heap state. -/
def sProg : ExecState :=
  { types := wordfreqLowered.typeDefs.toList,
    functions := wordfreqLowered.funcs,
    methods := wordfreqLowered.methods,
    heap := [], nextAddr := 0 }

/-- The machine entry's post-prelude state (program-generic form):
argument cells at `0`–`2` — this def receives the ALREADY-normalized
parameter values — and result cells at their defaults after them. -/
def sHSeed (n seed qsel : Int) : ExecState :=
  { sProg with heap := wHeap0 n seed qsel, nextAddr := 7 }

/-- The post-prelude start configuration. -/
def sHC0 : Config :=
  .exec wordfreqHarnessRFunc.body [baseScopeW] frameStop

/-- **The entry equation** (§11 glue): the machine entry IS its
post-prelude `runConfig` form, at fully symbolic arguments, fuel and
choice stream. -/
theorem w_entry_eq (n seed qsel : Int) (fuel : Nat) (ch : Choices) :
    runFunctionWithContextM fuel wordfreqLowered.typeDefs.toList
        wordfreqLowered.funcs wordfreqHarnessRFunc
        #[.int n .uint64, .int seed .uint64, .int qsel .uint64]
        wordfreqLowered.methods ch
      = (do
          let r ← runConfig fuel
            (sHSeed (IntKind.normalize .uint64 n)
              (IntKind.normalize .uint64 seed)
              (IntKind.normalize .uint64 qsel)) sHC0 ch
          return { values :=
            (← loadMany r.1
              [.base ⟨3⟩, .base ⟨4⟩, .base ⟨5⟩, .base ⟨6⟩]).toArray }) := by
  with_unfolding_all rfl

/-! ## The three `enterFrame` discharges (the only program-consulting
steps outside the entry) -/

/-- `buildText(n, seed)` frame entry at the pinned program. -/
theorem bt_enterFrame_fact (nv sv qv : Int)
    (h8 : IntKind.normalize .uint64 nv = nv)
    (h9 : IntKind.normalize .uint64 sv = sv) :
    enterFrame (wSt sProg (wHeapPre nv sv qv) 8) ⟨"buildText"⟩
        [.int nv .uint64, .int sv .uint64]
      = .ok (buildTextFunc, btFrameEnv, [.base ⟨10⟩],
          wSt sProg (wHeapBF nv sv qv nv sv) 11) := by
  have hraw : enterFrame (wSt sProg (wHeapPre nv sv qv) 8) ⟨"buildText"⟩
        [.int nv .uint64, .int sv .uint64]
      = .ok (buildTextFunc, btFrameEnv, [.base ⟨10⟩],
          wSt sProg (wHeapBF nv sv qv (IntKind.normalize .uint64 nv)
            (IntKind.normalize .uint64 sv)) 11) := by
    with_unfolding_all rfl
  rw [hraw, h8, h9]

/-- `wordFreq(pre, q)` frame entry at the pinned program. -/
theorem wf_enterFrame_fact (nv sv qv bnv bsv : Int) (l q : List UInt8)
    (biv : Int) :
    enterFrame (wSt sProg (wHeapCall nv sv qv bnv bsv l q biv) 17)
        ⟨"wordFreq"⟩ [.string (gs l), .string (gs q)]
      = .ok (wordFreqFunc, wfFrameEnv, [.base ⟨19⟩, .base ⟨20⟩],
          wSt sProg (wHeapWF nv sv qv bnv bsv l q biv) 21) := by
  with_unfolding_all rfl

/-- `goleanShimStringsFields(text)` frame entry at the pinned program. -/
theorem shim_enterFrame_fact (nv sv qv bnv bsv : Int) (l q : List UInt8)
    (biv : Int) :
    enterFrame (wSt sProg (wHeapWords nv sv qv bnv bsv l q biv) 22)
        ⟨"goleanShimStringsFields"⟩ [.string (gs l)]
      = .ok (goleanShimStringsFieldsFunc, shimFrameEnv, [.base ⟨23⟩],
          wSt sProg (wHeapShim nv sv qv bnv bsv l q biv) 24) := by
  with_unfolding_all rfl

end GoLean.Examples.WordFreq
