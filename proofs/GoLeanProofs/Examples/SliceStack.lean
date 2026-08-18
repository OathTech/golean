import GoLeanProofs.Examples.SliceStackProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.EntryEq
import GoLeanProofs.Laws.StmtOps

/-!
# SliceStack — the `stack` example (Gallery Campaign G1, lane A2)

Go source: `Corpus/coverage/exec/examples/stack/main.go` (13 rows,
differentially green against `go run`). The lowering is pinned by
`scripts/check-golden` against `baselines/golden/stack-lowered.repr`
and carried in `GoLeanProofs.Examples.SliceStackProgram`.

The subject is a slice-backed stack: `push` is Go's `append`, `pop` is
`s[:len(s)-1]` plus the read of the last element. The harness
`stack_harness_r(n, seed, k)` is the S3 RELATIONAL shape: push
`seed + i` (wrapping) for `i < n`, recording each pushed value into a
fixed-cap `[8]uint64`; pop `min(k, n)` values, recording them in pop
order; return `(pushed, popped, size(s))` — the postcondition is a
relation over the RETURNED data (LIFO is `pushed.reverse.take k`).

**THE PROOF IS CAPACITY- AND ADDRESS-GENERIC, and has to be.** The
machine models `append`'s spill capacity as a NONDETERMINISM ENVELOPE:
a spilling `append` consumes one choice from the `ch` stream and the
realized capacity varies with it (Go's spec pins only "sufficiently
large"; gc's realized capacity comes from size-class rounding). So the
backing address, the capacity, which pushes spill, and even the NUMBER
of consumed choices are all choice-dependent — and the push loop is
proved by a genuinely parametric induction (existential backing
address/capacity + a dead-tail freshness invariant), never by
unrolling to one stream's concrete states. The STEP COUNT is
choice-invariant (probe-checked), which is what makes one fuel bound
serve every stream.

THE HEADLINE is stated HERE, in the root, so the aggregator's
`import GoLeanProofs.Examples.SliceStack` reaches it by name (the
C-H4/C-H5 shape, adopted from birth).
-/

namespace GoLean.Examples.SliceStack

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

abbrev tU64 : Ty := .int .uint64
abbrev sliceU : Ty := .slice tU64

/-! ## The statement vocabulary -/

/-- The returned fixed-cap array: the observed value list, zero-padded to
the harness's `stackCapN = 8` slots. Deliberately NOT shared with the
identically shaped arrays of other examples (the §11 closure rule). -/
def stArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map (fun v => .int v .uint64)⟩

/-! ## The `Func`s, verbatim from the pinned lowering — restated in the
readable compositional form; the pins below tie each to the lowering by
`rfl`, so the two spellings are the same term. -/

/-- One push-loop fill step `v := seed + i` (fresh `v` each iteration). -/
def stFill1 : Stmt :=
  .seqn #[.initialization { id := "v", typ := tU64 },
          .assign (.var "v") (.add (.var "seed") (.var "i"))]

/-- The push call `s = push(s, v)`. -/
def stFill2 : Stmt :=
  .seqn #[.call #[.var "s"] ⟨"push"⟩ #[.var "s", .var "v"]]

/-- The record `pushed[i] = v`. -/
def stFill3 : Stmt :=
  .seqn #[.assign (.addr (.indexAddr (.ref "pushed") (.var "i")))
    (.var "v")]

def stFillBlock : Stmt := .block #[] #[stFill1, stFill2, stFill3]

/-- The push loop's desugared body. -/
def stPushBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i")
          (.add (.var "i") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n"))
        (.seqn #[]) .breakStmt,
      stFillBlock]

/-- One pop-loop fill step: fresh `v`. -/
def stPFill1 : Stmt := .seqn #[.initialization { id := "v", typ := tU64 }]

/-- The pop call `s, v = pop(s)`. -/
def stPFill2 : Stmt :=
  .seqn #[.call #[.var "s", .var "v"] ⟨"pop"⟩ #[.var "s"]]

/-- The record `popped[j] = v`. -/
def stPFill3 : Stmt :=
  .seqn #[.assign (.addr (.indexAddr (.ref "popped") (.var "j")))
    (.var "v")]

def stPFillBlock : Stmt := .block #[] #[stPFill1, stPFill2, stPFill3]

/-- The pop loop's desugared body. -/
def stPopBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "j")
          (.add (.var "j") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "j") (.var "m"))
        (.seqn #[]) .breakStmt,
      stPFillBlock]

/-! ### The harness body's top-level statement pieces -/

def stS1 : Stmt :=
  .seqn #[.initialization { id := "$c7", typ := sliceU },
          .makeSlice (.var "$c7") tU64 (.intLit 0 .int)
            (some (.intLit 0 .int))]
def stS2 : Stmt :=
  .seqn #[.initialization { id := "s", typ := sliceU },
          .assign (.var "s") (.var "$c7")]
def stS3 : Stmt :=
  .seqn #[.initialization { id := "pushed", typ := .array 8 tU64 }]
def stS4 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := tU64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) stPushBody]]
def stS5 : Stmt :=
  .seqn #[.initialization { id := "m", typ := tU64 },
          .assign (.var "m") (.var "k")]
def stS6 : Stmt :=
  .ifThenElse (.lessCmp (.var "n") (.var "m"))
    (.block #[] #[.seqn #[.assign (.var "m") (.var "n")]])
    (.seqn #[])
def stS7 : Stmt :=
  .seqn #[.initialization { id := "popped", typ := .array 8 tU64 }]
def stS8 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "j", typ := tU64 },
              .assign (.var "j") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) stPopBody]]
def stS9 : Stmt :=
  .seqn #[.initialization { id := "$c8", typ := tU64 },
          .call #[.var "$c8"] ⟨"size"⟩ #[.var "s"]]
def stS10 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "pushed"),
          .assign (.var "$res1") (.var "popped"),
          .assign (.var "$res2") (.var "$c8"),
          .returnStmt]

/-- The harness `Func`, verbatim from the pinned lowering (the pin below
ties it by `rfl`) — restated in the readable compositional form; the
guardrails stub carried the byte-extracted monolith, and the pin holding
proves the two spellings identical. -/
def stackHarnessRFunc : Func :=
  { id := { key := "stack_harness_r" },
    args := #[{ id := "n", typ := tU64 }, { id := "seed", typ := tU64 },
              { id := "k", typ := tU64 }],
    results := #[{ id := "$res0", typ := .array 8 tU64 },
                 { id := "$res1", typ := .array 8 tU64 },
                 { id := "$res2", typ := tU64 }],
    body := .block #[]
      #[stS1, stS2, stS3, stS4, stS5, stS6, stS7, stS8, stS9, stS10],
    variadic := false,
    wrapper := false }

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem stackHarnessRFunc_pin :
    findFunctionIn? stackLowered.funcs ⟨"stack_harness_r"⟩
    = some stackHarnessRFunc := rfl

/-! ### The subject `Func`s (`push`, `pop`) and the `size` observer -/

def pushB1 : Stmt :=
  .seqn #[.initialization { id := "$c0", typ := sliceU },
          .makeSlice (.var "$c0") tU64 (.intLit 1 .int)
            (some (.intLit 1 .int)),
          .assign (.addr (.indexAddr (.var "$c0") (.intLit 0 .int)))
            (.var "v")]
def pushB2 : Stmt :=
  .seqn #[.initialization { id := "$c1", typ := sliceU },
          .appendSlice (.var "$c1") tU64 (.var "s") (.var "$c0")]
def pushB3 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "$c1"), .returnStmt]

/-- The `push` subject: Go's `append`, verbatim from the pinned
lowering. -/
def pushFunc : Func :=
  { id := { key := "push" },
    args := #[{ id := "s", typ := sliceU }, { id := "v", typ := tU64 }],
    results := #[{ id := "$res0", typ := sliceU }],
    body := .block #[] #[pushB1, pushB2, pushB3],
    variadic := false,
    wrapper := false }

/-- The `push` subject pin. -/
theorem push_pin :
    findFunctionIn? stackLowered.funcs ⟨"push"⟩ = some pushFunc := rfl

def sLenM1 : Expr :=
  .sub (.length (.var "s") (some sliceU)) (.intLit 1 .int)

def popB1 : Stmt :=
  .seqn #[.initialization { id := "v", typ := tU64 },
          .assign (.var "v") (.indexGet (.var "s") sLenM1)]
def popB2 : Stmt :=
  .seqn #[.assign (.var "$res0")
            (.slice (.var "s") (.intLit 0 .int) sLenM1 none),
          .assign (.var "$res1") (.var "v"),
          .returnStmt]

/-- The `pop` subject: read the top, reslice `s[:len(s)-1]` — same
backing array, shorter header. Verbatim from the pinned lowering. -/
def popFunc : Func :=
  { id := { key := "pop" },
    args := #[{ id := "s", typ := sliceU }],
    results := #[{ id := "$res0", typ := sliceU },
                 { id := "$res1", typ := tU64 }],
    body := .block #[] #[popB1, popB2],
    variadic := false,
    wrapper := false }

/-- The `pop` subject pin. -/
theorem pop_pin :
    findFunctionIn? stackLowered.funcs ⟨"pop"⟩ = some popFunc := rfl

/-- The `size` observer (the harness's third return rides through it). -/
def sizeFunc : Func :=
  { id := { key := "size" },
    args := #[{ id := "s", typ := sliceU }],
    results := #[{ id := "$res0", typ := tU64 }],
    body := .block #[]
      #[.seqn #[.assign (.var "$res0")
                  (.convert tU64 (.length (.var "s") (some sliceU))),
                .returnStmt]],
    variadic := false,
    wrapper := false }

/-- The `size` observer pin. -/
theorem size_pin :
    findFunctionIn? stackLowered.funcs ⟨"size"⟩ = some sizeFunc := rfl

/-! ## The pushed family and its prefixes

`stFam n seed = [seed+0, seed+1, …]` WRAPPED mod 2^64 elementwise.
Kit near-dup note (GAP-P2b, recorded — we are the 4th consumer):
`SliceMem.familyMod k` is `seed + i%k`; the affine family here is
`seed + i` (MinMax's `mmFamily` formula, designated statement
vocabulary THERE and deliberately not shared; DotProduct's `dpFamA` is
the same formula as proof vocabulary, also per-example). The
zero-padded prefix DOES reuse the kit's `prefixPad` generically. -/

def stFam (n seed : Nat) : List Int :=
  (List.range n).map (fun i => (((seed + i) % 2 ^ 64 : Nat) : Int))

theorem stFam_length (n seed : Nat) : (stFam n seed).length = n :=
  familyF_length id n seed

theorem stFam_range (n seed : Nat) :
    ∀ v ∈ stFam n seed, 0 ≤ v ∧ v < 2 ^ 64 :=
  familyF_range id n seed

theorem stFam_succ (i seed : Nat) :
    stFam (i + 1) seed
      = stFam i seed ++ [(((seed + i) % 2 ^ 64 : Nat) : Int)] :=
  familyF_succ id i seed

theorem stFam_getD {n seed m : Nat} (hm : m < n) :
    (stFam n seed).getD m 0 = (((seed + m) % 2 ^ 64 : Nat) : Int) :=
  familyF_getD (f := id) hm

/-- The family prefix with a zero tail (to an arbitrary capacity `c`)
stays in uint64 range. -/
theorem stFamZ_range {c seed i : Nat} :
    ∀ v ∈ stFam i seed ++ List.replicate (c - i) (0 : Int),
      0 ≤ v ∧ v < 2 ^ 64 :=
  familyFZ_range (f := id)

/-- One in-place append advances the family prefix inside a fixed-cap
backing: setting slot `i` of `fam i ++ zeros (c-i)` yields
`fam (i+1) ++ zeros (c-(i+1))`. -/
theorem stFam_set {c seed i : Nat} (hi : i < c) :
    (stFam i seed ++ List.replicate (c - i) 0).set i
        (((seed + i) % 2 ^ 64 : Nat) : Int)
      = stFam (i + 1) seed ++ List.replicate (c - (i + 1)) 0 :=
  familyF_set (f := id) hi

/-- The `pushed` array after `m` recorded pushes (the kit's
`prefixPad`, cap 8). -/
def stPre (m seed : Nat) : List Int := prefixPad stFam 8 m seed

theorem stPre_zero (seed : Nat) : stPre 0 seed = List.replicate 8 0 :=
  prefixPad_zero rfl

theorem stPre_length {m seed : Nat} (h : m ≤ 8) :
    (stPre m seed).length = 8 :=
  prefixPad_length (stFam_length m seed) h

theorem stPre_range {m seed : Nat} :
    ∀ v ∈ stPre m seed, 0 ≤ v ∧ v < 2 ^ 64 :=
  prefixPad_range (stFam_range m seed)

theorem stPre_set {seed m : Nat} (hm : m < 8) :
    (stPre m seed).set m (((seed + m) % 2 ^ 64 : Nat) : Int)
      = stPre (m + 1) seed := by
  have h := stFam_set (c := 8) (seed := seed) (i := m) hm
  exact h

theorem stPre_full {n seed : Nat} :
    stPre n seed
      = stFam n seed ++ List.replicate (8 - (stFam n seed).length) 0 :=
  prefixPad_full (stFam_length n seed)

/-! ## The popped list and its prefixes

`stPopL n seed j` is the list of the first `j` popped values: pop `t`
removes the top of a stack currently holding `n - t` values, so it
yields `fam[n-1-t]`. The bridge below identifies the full popped list
with the STATEMENT's `pushed.reverse.take k`. -/

def stPopL (n seed j : Nat) : List Int :=
  (List.range j).map (fun t => (stFam n seed).getD (n - 1 - t) 0)

theorem stPopL_length (n seed j : Nat) : (stPopL n seed j).length = j := by
  simp [stPopL]

theorem stPopL_range (n seed j : Nat) :
    ∀ v ∈ stPopL n seed j, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  simp only [stPopL, List.mem_map, List.mem_range] at hv
  obtain ⟨t, -, rfl⟩ := hv
  by_cases h : n - 1 - t < n
  · rw [stFam_getD h]
    have : (seed + (n - 1 - t)) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by omega)
    omega
  · rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [stFam_length]; omega)]
    simp

theorem stPopL_succ (n seed j : Nat) :
    stPopL n seed (j + 1)
      = stPopL n seed j ++ [(stFam n seed).getD (n - 1 - j) 0] := by
  simp [stPopL, List.range_succ]

/-- The `popped` array after `j` recorded pops (the `prefixPad` shape,
spelled directly — `prefixPad`'s family signature carries a seed slot
the pop list does not have). -/
def stPopPre (n seed j : Nat) : List Int :=
  stPopL n seed j ++ List.replicate (8 - j) 0

theorem stPopPre_zero (n seed : Nat) :
    stPopPre n seed 0 = List.replicate 8 0 := by
  simp [stPopPre, stPopL]

theorem stPopPre_length {n seed j : Nat} (h : j ≤ 8) :
    (stPopPre n seed j).length = 8 := by
  rw [stPopPre, List.length_append, stPopL_length, List.length_replicate]
  omega

theorem stPopPre_range {n seed j : Nat} :
    ∀ v ∈ stPopPre n seed j, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact stPopL_range n seed j v hv
  · rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
    omega

theorem stPopPre_set {n seed j : Nat} (hj : j < 8) :
    (stPopPre n seed j).set j ((stFam n seed).getD (n - 1 - j) 0)
      = stPopPre n seed (j + 1) := by
  have hlen : (stPopL n seed j).length = j := stPopL_length n seed j
  have hnm : 8 - j = (8 - (j + 1)) + 1 := by omega
  unfold stPopPre
  rw [List.set_append_right _ _ (by omega), hlen, Nat.sub_self, hnm,
    List.replicate_succ, List.set_cons_zero, stPopL_succ]
  simp

/-- **The LIFO bridge**: with `m = min k n` pops of an `n`-element
stack, the recorded pop list IS the statement's `pushed.reverse.take k`
— `List.take` truncates, so the two spellings of "everything you asked
for, at most what is there" coincide. -/
theorem stPopL_reverse_take (n seed k m : Nat) (hm : m = min k n) :
    (stFam n seed).reverse.take k = stPopL n seed m := by
  subst hm
  apply List.ext_getElem
  · simp [stPopL_length, stFam_length]
  · intro t h1 h2
    have htk : t < min k n := by
      simpa [List.length_take, List.length_reverse, stFam_length] using h1
    have htn : t < n := by omega
    rw [List.getElem_take, List.getElem_reverse]
    simp only [stPopL, List.getElem_map, List.getElem_range,
      stFam_length]
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [stFam_length]; omega)]
    simp

/-! ## Address layout

Probe-measured (`.tmp/sttags.lean`; every raw segment below re-checks
the transcription by `rfl`). The CONCRETE front (addresses 0–11) is
choice-independent:

```
0 = n     1 = seed   2 = k
3 = $res0 ([8])  4 = $res1 ([8])  5 = $res2
6 = $c7 handle   7 = its cap-0 backing
8 = s handle     9 = pushed ([8])  10 = push i   11 = push $forFirst
```

EVERYTHING PAST 11 IS CHOICE-DEPENDENT — a spilling `append` consumes a
choice and allocates one extra cell — so the push phase carries a
SYMBOLIC tail `T` (dead push-frame junk + the live backing at a
symbolic address `b` with symbolic capacity `c`), the pop phase adds
the `m`/`popped`/`j`/`$forFirst` block at a symbolic base `q`, and all
reasoning past the front is conditioned on `Heap.lookup` facts plus the
kit's `DeadFrom` freshness predicate. Per iteration the machine
allocates 7 cells (v, the callee's s/v/$res0, $c0, its backing, $c1)
plus 1 more on a spill; a pop iteration allocates 5 (v, the callee's
s/$res0/$res1, its v). -/

abbrev u64c (v : Int) : HeapCell := ⟨some tU64, .int v .uint64⟩
abbrev bcell (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
abbrev arrC (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n tU64), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev slC (v : GoValue) : HeapCell := ⟨some sliceU, v⟩
/-- The nil slice value (a fresh slice cell's default). -/
abbrev nilSl : GoValue := .slice ⟨none, 0, 0, 0⟩
abbrev zeros8 : List Int := List.replicate 8 0

/-- The `s` handle over backing address `b`, length `len`, capacity
`c`. -/
abbrev sHv (b len c : Nat) : GoValue :=
  .slice ⟨some (.base ⟨b⟩), 0, len, c⟩

/-- The live backing cell: a capacity-`c` array holding `l` (callers
pass the family prefix zero-padded to `c`). -/
abbrev backC (c : Nat) (l : List Int) : HeapCell := arrC c l

/-- The PROGRAM-generic state form. -/
abbrev stStx (σ : ExecState) (H : Heap) (na : Nat) : ExecState :=
  { σ with heap := H, nextAddr := na }

/-- The concrete 12-cell front. `sh` is the current `s` handle value,
`pl` the current `pushed` contents, `iv`/`ff` the loop counter and
flag; `r3 r4 r5` are the result cells (zeros until the epilogue). -/
def stF (nv sv kv : Int) (r3 r4 : List Int) (r5 : Int) (sh : GoValue)
    (pl : List Int) (iv : Int) (ff : Bool) : Heap :=
  [(.base ⟨0⟩, u64c nv), (.base ⟨1⟩, u64c sv), (.base ⟨2⟩, u64c kv),
   (.base ⟨3⟩, arrC 8 r3), (.base ⟨4⟩, arrC 8 r4), (.base ⟨5⟩, u64c r5),
   (.base ⟨6⟩, slC (sHv 7 0 0)), (.base ⟨7⟩, arrC 0 []),
   (.base ⟨8⟩, slC sh), (.base ⟨9⟩, arrC 8 pl),
   (.base ⟨10⟩, u64c iv), (.base ⟨11⟩, bcell ff)]

/-- The pop-phase locals block at symbolic base `q`:
`m` / `popped` / `j` / `$forFirst`. -/
def stM (q : Nat) (mv : Int) (ppl : List Int) (jv : Int) (ff : Bool) :
    Heap :=
  [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 ppl),
   (.base ⟨q + 2⟩, u64c jv), (.base ⟨q + 3⟩, bcell ff)]

/-! ### Environments -/

def stBase : Scope :=
  [("$res2", .base ⟨5⟩), ("$res1", .base ⟨4⟩), ("$res0", .base ⟨3⟩),
   ("k", .base ⟨2⟩), ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]
def stTop : Scope :=
  [("pushed", .base ⟨9⟩), ("s", .base ⟨8⟩), ("$c7", .base ⟨6⟩)]
def stPuIScope : Scope := [("i", .base ⟨10⟩)]

/-- The push loop's env at its head. -/
def stPuEnv : LocalEnv :=
  [[("$forFirst", .base ⟨11⟩)], stPuIScope, stTop, stBase]
def stPuEnv1 : LocalEnv := [] :: stPuEnv
def stPuEnv2 : LocalEnv := [] :: stPuEnv1
/-- The fill block's env once `v` (at the iteration-local address `na`)
is declared. -/
def stPuEnvV (na : Nat) : LocalEnv := [("v", .base ⟨na⟩)] :: stPuEnv1

/-- The push callee's frame env (cells `na+1 … na+3`). -/
def stPuFrEnv (na : Nat) : LocalEnv :=
  [[("$res0", .base ⟨na + 3⟩), ("v", .base ⟨na + 2⟩),
    ("s", .base ⟨na + 1⟩)]]
def stPuFrEnv2 (na : Nat) : LocalEnv := [] :: stPuFrEnv na
def stPuFrEnvC0 (na : Nat) : LocalEnv :=
  [("$c0", .base ⟨na + 4⟩)] :: stPuFrEnv na
def stPuFrEnvC1 (na : Nat) : LocalEnv :=
  [("$c1", .base ⟨na + 6⟩), ("$c0", .base ⟨na + 4⟩)] :: stPuFrEnv na

/-- The top scope after `m` and `popped` are declared (pop phase; `q`
is the pop-block base). -/
def stTopP (q : Nat) : Scope :=
  [("popped", .base ⟨q + 1⟩), ("m", .base ⟨q⟩),
   ("pushed", .base ⟨9⟩), ("s", .base ⟨8⟩), ("$c7", .base ⟨6⟩)]

/-- The pop loop's env at its head. -/
def stPoEnv (q : Nat) : LocalEnv :=
  [[("$forFirst", .base ⟨q + 3⟩)], [("j", .base ⟨q + 2⟩)], stTopP q,
   stBase]
def stPoEnv1 (q : Nat) : LocalEnv := [] :: stPoEnv q
def stPoEnv2 (q : Nat) : LocalEnv := [] :: stPoEnv1 q
def stPoEnvV (q na : Nat) : LocalEnv :=
  [("v", .base ⟨na⟩)] :: stPoEnv1 q

/-- The pop callee's frame env (cells `na+1 … na+3`). -/
def stPoFrEnv (na : Nat) : LocalEnv :=
  [[("$res1", .base ⟨na + 3⟩), ("$res0", .base ⟨na + 2⟩),
    ("s", .base ⟨na + 1⟩)]]
def stPoFrEnv2 (na : Nat) : LocalEnv := [] :: stPoFrEnv na

/-! ### Continuations -/

def stStop : Cont := .frame [] [] [] [] .stop

/-- What follows the push loop, at the harness's top level. -/
def stTailK : Cont :=
  .seq [stS5, stS6, stS7, stS8, stS9, stS10] [stTop, stBase] stStop
def stPuHeadTail : Cont :=
  .seq [] stPuEnv (.seq [] [stPuIScope, stTop, stBase] stTailK)
def stPuLoopK : Cont :=
  .loop (.boolLit true) stPushBody stPuEnv stPuHeadTail
/-- The push checkpoint continuation: the `i < n` test's `ifK`. -/
def stPuCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt stPuEnv1
    (.seq [stFillBlock] stPuEnv1 stPuLoopK)

/-- After the fill block: back to the loop. -/
def stPuK0 : Cont := .seq [] stPuEnv1 stPuLoopK
/-- The fill tail once `v` is declared at `na`. -/
def stPuKF23 (na : Nat) : Cont :=
  .seq [stFill2, stFill3] (stPuEnvV na) stPuK0
/-- After the push call returns and writes back. -/
def stPuKCall (na : Nat) : Cont := .seq [stFill3] (stPuEnvV na) stPuK0
/-- The push call's target plans (`s = push(…)`). -/
def stPuPlans : List (TargetShape × List Expr) := [(.chain [], [.ref "s"])]
/-- The push callee's frame continuation. -/
def stPuFrameK (na : Nat) : Cont :=
  .frame stPuPlans (stPuEnvV na) [.base ⟨na + 3⟩] [] (stPuKCall na) false

/-- What follows the pop loop (`q` the pop-block base). -/
def stPoTailK (q : Nat) : Cont :=
  .seq [stS9, stS10] [stTopP q, stBase] stStop
def stPoHeadTail (q : Nat) : Cont :=
  .seq [] (stPoEnv q)
    (.seq [] [[("j", .base ⟨q + 2⟩)], stTopP q, stBase] (stPoTailK q))
def stPoLoopK (q : Nat) : Cont :=
  .loop (.boolLit true) stPopBody (stPoEnv q) (stPoHeadTail q)
/-- The pop checkpoint continuation: the `j < m` test's `ifK`. -/
def stPoCmpK (q : Nat) : Cont :=
  .ifK (.seqn #[]) .breakStmt (stPoEnv1 q)
    (.seq [stPFillBlock] (stPoEnv1 q) (stPoLoopK q))

def stPoK0 (q : Nat) : Cont := .seq [] (stPoEnv1 q) (stPoLoopK q)
def stPoKCall (q na : Nat) : Cont :=
  .seq [stPFill3] (stPoEnvV q na) (stPoK0 q)
/-- The pop call's target plans (`s, v = pop(s)`). -/
def stPoPlans : List (TargetShape × List Expr) :=
  [(.chain [], [.ref "s"]), (.chain [], [.ref "v"])]

/-! ## Heap facts at the symbolic split

The front has concrete addresses, the tail is symbolic; these are the
composition lemmas every conditioned step discharges its `Heap.lookup`
/ `Heap.set` side conditions with. -/

/-- Nothing at address ≥ 12 lives in the front. -/
theorem stF_lookup_none {nv sv kv : Int} {r3 r4 : List Int} {r5 : Int}
    {sh : GoValue} {pl : List Int} {iv : Int} {ff : Bool} {x : Nat}
    (hx : 12 ≤ x) :
    Heap.lookup (stF nv sv kv r3 r4 r5 sh pl iv ff) (.base ⟨x⟩)
      = none := by
  unfold stF
  rw [lookup_cons_ne (base_beq_false (by omega)),
    lookup_cons_ne (base_beq_false (by omega)),
    lookup_cons_ne (base_beq_false (by omega)),
    lookup_cons_ne (base_beq_false (by omega)),
    lookup_cons_ne (base_beq_false (by omega)),
    lookup_cons_ne (base_beq_false (by omega)),
    lookup_cons_ne (base_beq_false (by omega)),
    lookup_cons_ne (base_beq_false (by omega)),
    lookup_cons_ne (base_beq_false (by omega)),
    lookup_cons_ne (base_beq_false (by omega)),
    lookup_cons_ne (base_beq_false (by omega)),
    lookup_cons_ne (base_beq_false (by omega))]
  rfl

/-- A tail lookup passes through the front. -/
theorem stF_lookup_tail {nv sv kv : Int} {r3 r4 : List Int} {r5 : Int}
    {sh : GoValue} {pl : List Int} {iv : Int} {ff : Bool} {T : Heap}
    {x : Nat} (hx : 12 ≤ x) :
    Heap.lookup (stF nv sv kv r3 r4 r5 sh pl iv ff ++ T) (.base ⟨x⟩)
      = Heap.lookup T (.base ⟨x⟩) :=
  lookup_append_right (stF_lookup_none hx)

/-- A tail set passes through the front. -/
theorem stF_set_tail {nv sv kv : Int} {r3 r4 : List Int} {r5 : Int}
    {sh : GoValue} {pl : List Int} {iv : Int} {ff : Bool} {T : Heap}
    {x : Nat} {c : HeapCell} (hx : 12 ≤ x) :
    Heap.set (stF nv sv kv r3 r4 r5 sh pl iv ff ++ T) (.base ⟨x⟩) c
      = stF nv sv kv r3 r4 r5 sh pl iv ff ++ Heap.set T (.base ⟨x⟩) c :=
  set_append_right (stF_lookup_none hx)

/-- Fresh allocation at `x ≥ na` on a front+tail heap appends. -/
theorem stF_set_fresh {nv sv kv : Int} {r3 r4 : List Int} {r5 : Int}
    {sh : GoValue} {pl : List Int} {iv : Int} {ff : Bool} {T : Heap}
    {na x : Nat} {c : HeapCell} (hna : 12 ≤ na)
    (hdead : DeadFrom T na) (hx : na ≤ x) :
    Heap.set (stF nv sv kv r3 r4 r5 sh pl iv ff ++ T) (.base ⟨x⟩) c
      = stF nv sv kv r3 r4 r5 sh pl iv ff ++ (T ++ [(.base ⟨x⟩, c)]) := by
  rw [stF_set_tail (by omega), set_fresh (hdead x hx)]

/-! ## Executable op facts (the conditioned-step layer)

Each fact is conditioned on exactly the `Heap.lookup` / range
hypotheses it needs and stated over an abstract `σ` (the kit's E-form
discipline). The append facts are NEW GROUND for the gallery — no
landed example has proved through a growing slice — and are reported
as kit-gap witnesses. -/

/-- Scalar uint64 store normalization (the cell's declared type
re-normalizes on store). -/
theorem st_norm_u64 (σ : ExecState) (w : Int) :
    normalizeValueForTy σ tU64 (.int w .uint64)
      = .ok (.int (IntKind.normalize .uint64 w) .uint64) := by
  rw [normalizeValueForTy, typeResolutionFuel]
  simp only [normalizeValueForTyFuel]
  rfl

/-- A slice-typed cell stores any slice handle unchanged (the
normalizer's catch-all arm). -/
theorem st_norm_sliceU (σ : ExecState) (v : GoValue) :
    normalizeValueForTy σ sliceU v = .ok v := by
  rw [normalizeValueForTy, typeResolutionFuel]
  simp only [normalizeValueForTyFuel]
  rfl

private theorem st_validateSlice {b : Loc} {off len cap : Nat}
    (h : len ≤ cap) :
    validateSlice ⟨some b, off, len, cap⟩ = .ok () := by
  simp [validateSlice, Nat.not_lt.mpr h, Bind.bind, Except.bind]

/-- The visible values of a full-prefix slice over an in-memory
`[]uint64` backing, at a SYMBOLIC length (the spill path reads the
whole old backing this way). -/
theorem st_sliceVisible {σ : ExecState} {b : Nat} {len cap : Nat}
    {l : List Int}
    (hlook : Heap.lookup σ.heap (.base ⟨b⟩) = some (arrC cap l))
    (hlen : l.length = cap) (hlc : len ≤ cap) :
    sliceVisibleValues σ ⟨some (.base ⟨b⟩), 0, len, cap⟩
      = .ok ((l.take len).map (fun v => .int v .uint64)).toArray := by
  simp only [sliceVisibleValues, st_validateSlice hlc,
    Std.Legacy.Range.forIn_eq_forIn_range', Bind.bind, Except.bind, pure,
    Except.pure]
  rw [show ([:len] : Std.Legacy.Range).size = len from by
    simp [Std.Legacy.Range.size]]
  rw [GoLean.Iris.forIn_range'_inv (N := len) (n := len) (j := 0)
    (b := (#[] : Array GoValue))
    (Q := fun i acc =>
      acc = ((l.take i).map (fun v => .int v .uint64)).toArray)
    (out := fun i acc => acc.push (.int (l.getD i 0) .uint64))
    (res := ((l.take len).map (fun v => .int v .uint64)).toArray)
    ?hstep (by omega) (by simp)
    (fun b' hq => by rw [Nat.zero_add] at hq; exact hq)]
  intro i acc hi hacc
  have hi' : i < l.length := by omega
  have hget := getElem?_mapU l i hi'
  constructor
  · rw [GoLean.Iris.sliceIndexLoc_prefix (by omega) hlc]
    simp only [loadLoc, hlook, arrayGet, arrayIndexNat, Bind.bind,
      Except.bind, pure, Except.pure, Int.ofNat_eq_natCast]
    rw [if_neg (by omega : ¬ ((i : Int) < 0)), Int.toNat_natCast,
      if_pos (by simpa using hi')]
    simp [hget]
  · rw [hacc, List.push_toArray]
    congr 1
    rw [List.take_add_one, List.getElem?_eq_getElem hi', List.map_append]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']

/-- The normalize-each walk of `buildAppendBackingValue`, over a list of
already-normal values — body-generic (the goal's compiled matcher
lambda unifies with `body`; the shape hypothesis pins what it does). -/
private theorem st_forIn_norm
    {body : GoValue → Array GoValue → Except GoError (ForInStep (Array GoValue))}
    {P : GoValue → Prop}
    (hbody : ∀ x acc, P x → body x acc = .ok (.yield (acc.push x))) :
    ∀ (xs : List GoValue) (acc : Array GoValue), (∀ x ∈ xs, P x) →
      forIn xs acc body = .ok (acc ++ xs.toArray)
  | [], acc, _ => by
      rw [List.forIn_nil]
      simp [pure, Except.pure]
  | x :: xs, acc, h => by
      rw [List.forIn_cons, hbody x acc (h x (by simp))]
      show (forIn xs (acc.push x) body : Except GoError (Array GoValue)) = _
      rw [st_forIn_norm hbody xs (acc.push x)
        (fun y hy => h y (by simp [hy]))]
      simp

/-- The spill path's fresh backing: the old values, the appended value,
then zeros out to the (choice-dependent) new capacity — at a SYMBOLIC
capacity. -/
theorem st_buildAppendBacking (σ : ExecState) (l : List Int) (w : Int)
    (c' : Nat) (hr : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64)
    (hw : 0 ≤ w ∧ w < 2 ^ 64) (hc : l.length + 1 ≤ c') :
    buildAppendBackingValue σ tU64
        (l.map (fun v => .int v .uint64)).toArray #[.int w .uint64] c'
      = .ok (.array
          ⟨((l ++ [w]) ++ List.replicate (c' - (l.length + 1)) 0).map
            (fun v => .int v .uint64)⟩) := by
  have hnormAll : ∀ x ∈ (l.map (fun v => GoValue.int v .uint64))
      ++ [GoValue.int w .uint64], normalizeValueForTy σ tU64 x = .ok x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [List.mem_map] at hx
      obtain ⟨v, hv, rfl⟩ := hx
      rw [st_norm_u64, unorm_of_range (hr v hv).1 (hr v hv).2]
    · rw [List.mem_singleton] at hx
      subst hx
      rw [st_norm_u64, unorm_of_range hw.1 hw.2]
  simp only [buildAppendBackingValue, Bind.bind, Except.bind, pure,
    Except.pure]
  rw [show (l.map (fun v => GoValue.int v .uint64)).toArray
        ++ #[GoValue.int w .uint64]
      = ((l.map (fun v => GoValue.int v .uint64))
        ++ [GoValue.int w .uint64]).toArray from by simp]
  rw [← Array.forIn_toList, List.toList_toArray,
    st_forIn_norm (P := fun x => normalizeValueForTy σ tU64 x = .ok x)
      (fun x acc hx => by rw [hx]) _ _ hnormAll]
  have hsize : (((l.map (fun v => GoValue.int v .uint64))
      ++ [GoValue.int w .uint64]).toArray).size = l.length + 1 := by simp
  simp only [Array.empty_append, hsize]
  rw [if_neg (by omega : ¬ l.length + 1 > c')]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  rw [show ([:c' - (l.length + 1)] : Std.Legacy.Range).size
      = c' - (l.length + 1) from by simp [Std.Legacy.Range.size]]
  rw [GoLean.Iris.forIn_range'_inv (N := c' - (l.length + 1))
    (n := c' - (l.length + 1)) (j := 0)
    (b := ((l.map (fun v => GoValue.int v .uint64))
      ++ [GoValue.int w .uint64]).toArray)
    (Q := fun i acc => acc
      = (((l ++ [w]) ++ List.replicate i 0).map
          (fun v => GoValue.int v .uint64)).toArray)
    (out := fun _ acc => acc.push (.int 0 .uint64))
    (res := (((l ++ [w]) ++ List.replicate (c' - (l.length + 1)) 0).map
        (fun v => GoValue.int v .uint64)).toArray)
    ?hstep (by omega) (by simp) (fun b' hq => by
      rw [Nat.zero_add] at hq; exact hq)]
  case hstep =>
    intro i acc hi hacc
    refine ⟨by simp [defaultValue, defaultValueFuel, typeResolutionFuel], ?_⟩
    rw [hacc, List.push_toArray]
    congr 1
    rw [List.replicate_succ', ← List.append_assoc, List.map_append]
    simp

/-! ## The pinned program and the entry equation -/

/-- The pinned program as an empty-heap state — with the
`derive_entry_eq` invocation below and the frame-entry facts, the only
places this module carries `stackLowered` outside the pins. -/
def stProg : ExecState :=
  { types := stackLowered.typeDefs.toList,
    functions := stackLowered.funcs,
    methods := stackLowered.methods,
    heap := [], nextAddr := 0 }

derive_entry_eq stH_entry_eq stackLowered stackHarnessRFunc stHSeed stHC0
  stProg

/-! ## Frame-entry facts (the one program-consulting step per call)

Stated at a SYMBOLIC heap and allocation front: `enterFrame` never
branches on the heap (parameter binding is `Heap.set` at fresh
addresses), so `with_unfolding_all rfl` closes them with `H`/`a` fully
symbolic — the program constant is unfolded exactly here. -/

theorem st_enter_push (H : Heap) (a : Nat) (sh : GoValue) (w : Int) :
    enterFrame (stStx stProg H a) ⟨"push"⟩ [sh, .int w .uint64]
      = .ok (pushFunc,
          [[("$res0", .base ⟨a + 2⟩), ("v", .base ⟨a + 1⟩),
            ("s", .base ⟨a⟩)]],
          [.base ⟨a + 2⟩],
          stStx stProg
            (Heap.set (Heap.set (Heap.set H (.base ⟨a⟩) (slC sh))
                (.base ⟨a + 1⟩) (u64c (IntKind.normalize .uint64 w)))
              (.base ⟨a + 2⟩) (slC nilSl))
            (a + 3)) := by
  with_unfolding_all rfl

theorem st_enter_pop (H : Heap) (a : Nat) (sh : GoValue) :
    enterFrame (stStx stProg H a) ⟨"pop"⟩ [sh]
      = .ok (popFunc,
          [[("$res1", .base ⟨a + 2⟩), ("$res0", .base ⟨a + 1⟩),
            ("s", .base ⟨a⟩)]],
          [.base ⟨a + 1⟩, .base ⟨a + 2⟩],
          stStx stProg
            (Heap.set (Heap.set (Heap.set H (.base ⟨a⟩) (slC sh))
                (.base ⟨a + 1⟩) (slC nilSl))
              (.base ⟨a + 2⟩) (u64c 0))
            (a + 3)) := by
  with_unfolding_all rfl

theorem st_enter_size (H : Heap) (a : Nat) (sh : GoValue) :
    enterFrame (stStx stProg H a) ⟨"size"⟩ [sh]
      = .ok (sizeFunc,
          [[("$res0", .base ⟨a + 1⟩), ("s", .base ⟨a⟩)]],
          [.base ⟨a + 1⟩],
          stStx stProg
            (Heap.set (Heap.set H (.base ⟨a⟩) (slC sh))
              (.base ⟨a + 1⟩) (u64c 0))
            (a + 2)) := by
  with_unfolding_all rfl

/-! ## The `push`-body op facts -/

/-- `make([]uint64, 1, 1)` at a symbolic target cell: allocate the
one-zero backing at the allocation front, store the handle. -/
theorem st_make1_apply (σ : ExecState) (tc : Nat) (v0 : GoValue)
    (ch : Choices)
    (hlook : Heap.lookup σ.heap (.base ⟨tc⟩) = some ⟨some sliceU, v0⟩)
    (htc : (Loc.base ⟨σ.nextAddr⟩ : Loc) ≠ .base ⟨tc⟩) :
    applyStmtOp σ ch (.makeSlice tU64 true) 1
      [.addr (.base ⟨tc⟩), .int 1 .int, .int 1 .int]
      = .ok ({ σ with
          heap := Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
              (arrC 1 [0]))
            (.base ⟨tc⟩) (slC (sHv σ.nextAddr 1 1)),
          nextAddr := σ.nextAddr + 1 }, ch) := by
  have hb := GoLean.Iris.buildDefaultArrayValue_int σ .uint64 1
  simp only [applyStmtOp, applyStmtOpCore, valueAsInt, valueAsLoc,
    natFromNonneg_cast, Bind.bind, Except.bind, pure, Except.pure]
  rw [show natFromNonnegativeInt
      "runtime error: makeslice: len out of range" (1 : Int) = .ok 1 from
      rfl,
    show natFromNonnegativeInt
      "runtime error: makeslice: cap out of range" (1 : Int) = .ok 1 from
      rfl]
  simp only [hb, Bind.bind, Except.bind]
  rw [if_neg (Nat.lt_irrefl 1)]
  simp only [ExecState.alloc, ExecState.freshLoc, storeLoc,
    Heap.lookup_set_ne htc, hlook, st_norm_sliceU, Bind.bind, Except.bind,
    pure, Except.pure]
  rfl

/-- The append CAPACITY REALIZATION at a spill, as a function of the
consumed choice `e`: the envelope member the machine picks. -/
def stNewCap (i e : Nat) : Nat :=
  (i + 1) + ((appendGrowthCap i (i + 1) - (i + 1) + e)
    % appendSpillWidth i (i + 1))

theorem stNewCap_ge (i e : Nat) : i + 1 ≤ stNewCap i e := by
  unfold stNewCap
  omega

/-- **`append` WITHOUT spill** (`i < c`): the element lands in place in
the backing cell, the target gets the length-extended handle, NO choice
is consumed. GAP-WITNESS (kit gap, append family): the gallery's first
proof through a growing slice. -/
theorem st_append_inplace (σ : ExecState) (b tc nb i c : Nat)
    (l : List Int) (w : Int) (v1 : GoValue) (ch : Choices)
    (hlookB : Heap.lookup σ.heap (.base ⟨b⟩) = some (backC c l))
    (hlookNb : Heap.lookup σ.heap (.base ⟨nb⟩) = some (arrC 1 [w]))
    (hlookTc : Heap.lookup σ.heap (.base ⟨tc⟩) = some ⟨some sliceU, v1⟩)
    (hbtc : (Loc.base ⟨b⟩ : Loc) ≠ .base ⟨tc⟩)
    (hfit : i < c) (hlen : l.length = c)
    (hlr : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64) (hw : 0 ≤ w ∧ w < 2 ^ 64) :
    applyStmtOp σ ch (.appendSlice tU64) 1
      [.addr (.base ⟨tc⟩), .slice ⟨some (.base ⟨b⟩), 0, i, c⟩,
       .slice ⟨some (.base ⟨nb⟩), 0, 1, 1⟩]
      = .ok ({ σ with
          heap := Heap.set (Heap.set σ.heap (.base ⟨b⟩)
                      (backC c (l.set i w))) (.base ⟨tc⟩)
                    (slC (sHv b (i + 1) c)) }, ch) := by
  have hvis := st_sliceVisible (σ := σ) (b := nb) (len := 1) (cap := 1)
    (l := [w]) hlookNb rfl (Nat.le_refl 1)
  have hset : ∀ v ∈ l.set i w, 0 ≤ v ∧ v < 2 ^ 64 := by
    intro v hv
    rcases mem_set_of_mem hv with rfl | hv
    · exact hw
    · exact hlr v hv
  have hglist : l[i]? = some (l[i]'(by omega)) :=
    List.getElem?_eq_getElem (by omega)
  have harrset : arraySet
      (⟨l.map (fun v => .int v .uint64)⟩ : Array GoValue)
      (Int.ofNat (0 + i + 0)) (.int w .uint64)
      = .ok ⟨(l.set i w).map (fun v => .int v .uint64)⟩ := by
    have hidx : ((0 + i + 0 : Nat) : Int).toNat = i := by omega
    simp only [arraySet, arrayIndexNat, Bind.bind, Except.bind,
      Int.ofNat_eq_natCast, hidx]
    rw [if_neg (by omega), if_pos (by simp; omega)]
    rw [show (0 + i + 0 : Nat) = i from by omega]
    simp [hglist, coerceStoredValue, unorm_of_range hw.1 hw.2,
      Array.set!, pure, Except.pure]
  have hnorm := normalizeValueForTy_arr_u64 (σ := σ) (N := c)
    (lp := l.set i w) (by rw [List.length_set]; exact hlen) hset
  have hstore : storeLoc σ (.index (.base ⟨b⟩) (Int.ofNat (0 + i + 0)))
      (.int w .uint64)
      = .ok { σ with
          heap := Heap.set σ.heap (.base ⟨b⟩)
                    (backC c (l.set i w)) } := by
    simp only [storeLoc, loadLoc, hlookB, harrset, Bind.bind, Except.bind,
      pure, Except.pure]
    simp only [backC, arrC] at hnorm ⊢
    rw [hnorm]
  simp only [applyStmtOp, valueAsSlice, valueAsLoc, Bind.bind,
    Except.bind, pure, Except.pure, st_validateSlice (by omega : i ≤ c),
    st_validateSlice (Nat.le_refl 1), hvis]
  rw [if_pos (by simp; omega)]
  simp only [List.take_add_one, List.take_zero, List.getElem?_cons_zero,
    Option.toList_some, List.nil_append, List.map_cons, List.map_nil]
  rw [← Array.forIn_toList]
  simp only [List.toList_toArray, List.forIn_cons, List.forIn_nil, hstore,
    Bind.bind, Except.bind, pure, Except.pure]
  simp only [storeLoc, Heap.lookup_set_ne hbtc, hlookTc, st_norm_sliceU,
    Bind.bind, Except.bind, pure, Except.pure]
  rfl

/-- **`append` WITH spill** (`c = i`, the backing full): consume ONE
choice, allocate a fresh backing at the allocation front with the
choice-dependent capacity `stNewCap i e`, copy, append, zero-pad; the
target gets a handle over the NEW backing. GAP-WITNESS (kit gap,
append family). -/
theorem st_append_spill (σ : ExecState) (b tc nb i : Nat)
    (l : List Int) (w : Int) (v1 : GoValue) (ch ch' : Choices) (e : Nat)
    (hlookB : Heap.lookup σ.heap (.base ⟨b⟩) = some (backC i l))
    (hlookNb : Heap.lookup σ.heap (.base ⟨nb⟩) = some (arrC 1 [w]))
    (hlookTc : Heap.lookup σ.heap (.base ⟨tc⟩) = some ⟨some sliceU, v1⟩)
    (htc : (Loc.base ⟨σ.nextAddr⟩ : Loc) ≠ .base ⟨tc⟩)
    (hcons : ch.consume (appendSpillWidth i (i + 1)) = (e, ch'))
    (hlen : l.length = i)
    (hlr : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64) (hw : 0 ≤ w ∧ w < 2 ^ 64) :
    applyStmtOp σ ch (.appendSlice tU64) 1
      [.addr (.base ⟨tc⟩), .slice ⟨some (.base ⟨b⟩), 0, i, i⟩,
       .slice ⟨some (.base ⟨nb⟩), 0, 1, 1⟩]
      = .ok ({ σ with
          heap := Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
              (backC (stNewCap i e)
                ((l ++ [w])
                  ++ List.replicate (stNewCap i e - (i + 1)) 0)))
            (.base ⟨tc⟩) (slC (sHv σ.nextAddr (i + 1) (stNewCap i e))),
          nextAddr := σ.nextAddr + 1 }, ch') := by
  have hvisO := st_sliceVisible (σ := σ) (b := b) (len := i) (cap := i)
    (l := l) hlookB hlen (Nat.le_refl i)
  rw [show l.take i = l from by rw [← hlen]; exact List.take_length] at hvisO
  have hvisE := st_sliceVisible (σ := σ) (b := nb) (len := 1) (cap := 1)
    (l := [w]) hlookNb rfl (Nat.le_refl 1)
  have hbuild := st_buildAppendBacking σ l w (stNewCap i e) hlr hw
    (by rw [hlen]; exact stNewCap_ge i e)
  simp only [applyStmtOp, valueAsSlice, valueAsLoc, Bind.bind,
    Except.bind, pure, Except.pure, st_validateSlice (Nat.le_refl i),
    st_validateSlice (Nat.le_refl 1), hvisO, hvisE]
  rw [if_neg (by simp)]
  simp only [List.take_add_one, List.take_zero, List.getElem?_cons_zero,
    Option.toList_some, List.nil_append, List.map_cons, List.map_nil]
  simp only [show (#[GoValue.int w IntKind.uint64] : Array GoValue).size
      = 1 from rfl, hcons]
  rw [show i + 1 + ((appendGrowthCap i (i + 1) - (i + 1) + e)
      % appendSpillWidth i (i + 1)) = stNewCap i e from rfl]
  rw [hlen] at hbuild
  rw [hbuild]
  simp only [ExecState.alloc, ExecState.freshLoc, storeLoc,
    Heap.lookup_set_ne htc, hlookTc, st_norm_sliceU, Bind.bind,
    Except.bind, pure, Except.pure]

/-! ## The `pop`-body op facts -/

-- (The private `st_checkSliceBounds` helper that sat here fed only the
-- reslice fact below and was deleted with its proof in WP arc s1
-- lift 6.)

/-- **The reslice `s[0:d]` on a SLICE base** (`pop`'s `s[:len(s)-1]`):
same backing array, same offset, length `d`, capacity KEPT.
GAP-WITNESS, closed (WP arc s1 lift 6): the `lo = 0` instance of the
kit's general `SliceMem.applyStrictOp_sliceExpr_slice`; this pinned
name survives as a zero-proof delegation. -/
theorem st_sliceExpr_slice (σ : ExecState) (bl : Loc)
    (len d c : Nat) (ik ik' : IntKind) (hd : d ≤ c) (hlen : len ≤ c) :
    applyStrictOp σ (.sliceExpr false)
      [.slice ⟨some bl, 0, len, c⟩, .int 0 ik, .int (d : Int) ik']
      = .ok (.slice ⟨some bl, 0, d, c⟩, σ) :=
  SliceMem.applyStrictOp_sliceExpr_slice (lo := 0)
    (Nat.zero_le d) hd hlen

/-- The conditioned frame-exit step (GAP-WITNESS, closed in WP arc s1
lift 6: promoted to StepKit's P1 family as
`Surface.stepFn_return_frame`; this pinned name survives as a
zero-proof delegation). `stepFn_call_enter`'s exit-side mirror. -/
theorem stepFn_return_frame {σ : ExecState} {sh : TargetShape} {e : Expr}
    {ops : List Expr} {rest : List (TargetShape × List Expr)}
    {tenv : LocalEnv} {results : List Loc} {k : Cont} {w : Bool}
    {ch : Choices} {vs : List GoValue}
    (h : loadMany σ results = .ok vs) :
    stepFn σ (.returning (.frame ((sh, e :: ops) :: rest) tenv results []
        k w)) ch
      = .ok (.evalE e tenv
          (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k),
        σ, ch) :=
  Surface.stepFn_return_frame h

/-- One-cell `loadMany` (the push/size frame exits). -/
theorem st_loadMany1 {σ : ExecState} {a : Nat} {c : HeapCell}
    (h : Heap.lookup σ.heap (.base ⟨a⟩) = some c) :
    loadMany σ [.base ⟨a⟩] = .ok [c.value] := by
  simp [loadMany, loadLoc, h, Bind.bind, Except.bind, pure, Except.pure]

/-- Two-cell `loadMany` (the pop frame exit). -/
theorem st_loadMany2 {σ : ExecState} {a b : Nat} {c d : HeapCell}
    (ha : Heap.lookup σ.heap (.base ⟨a⟩) = some c)
    (hb : Heap.lookup σ.heap (.base ⟨b⟩) = some d) :
    loadMany σ [.base ⟨a⟩, .base ⟨b⟩] = .ok [c.value, d.value] := by
  simp [loadMany, loadLoc, ha, hb, Bind.bind, Except.bind, pure,
    Except.pure]

/-! ## The push phase

The phase heap: fixed front + a symbolic tail `T` (dead push-frame
junk and, from the first push on, the live backing at a symbolic
address). Segments are raw (`with_unfolding_all rfl`) between the
symbolic-address steps; every heap access past the front is a
conditioned kit step. -/

/-- The push-phase heap (result cells still zero, flag consumed). -/
abbrev stHp (nv sv kv : Int) (sh : GoValue) (pl : List Int) (iv : Int)
    (T : Heap) : Heap :=
  stF nv sv kv zeros8 zeros8 0 sh pl iv false ++ T

def stAssignV : Stmt :=
  .assign (.var "v") (.add (.var "seed") (.var "i"))
def stAssignC00 : Stmt :=
  .assign (.addr (.indexAddr (.var "$c0") (.intLit 0 .int))) (.var "v")

/-- The makeSlice-in-push governing sequence. -/
def stPuKMS (na : Nat) : Cont :=
  .seq [stAssignC00, pushB2, pushB3] (stPuFrEnvC0 na) (stPuFrameK na)

/-- R1: checkpoint (test true) → the `v` declaration. 7 steps, heap
untouched, envs concrete — fully state-generic. -/
theorem pu_R1 (σ : ExecState) (ch : Choices) :
    stepFnIter 7 σ (.retV (.bool true) stPuCmpK) ch
      = .ok (.exec (.initialization { id := "v", typ := tU64 }) stPuEnv2
          (.seq [stAssignV, stFill2, stFill3] stPuEnv2 stPuK0), σ, ch) := by
  with_unfolding_all rfl

/-- R2: `v` declared → the `v := seed + i` store point. 10 steps (the
add rides inside; front reads only). -/
theorem pu_R2 (σ : ExecState) (nv sv kv : Int) (sh : GoValue)
    (pl : List Int) (iv : Int) (T : Heap) (na na' : Nat) (ch : Choices) :
    stepFnIter 10 (stStx σ (stHp nv sv kv sh pl iv T) na')
      (.next (.seq [stAssignV, stFill2, stFill3] (stPuEnvV na) stPuK0)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
            [.int (IntKind.normalize .uint64 (sv + iv)) .uint64]
            (.seqn #[]) (stPuEnvV na) (stPuKF23 na)),
          stStx σ (stHp nv sv kv sh pl iv T) na', ch) := by
  with_unfolding_all rfl

/-- R3: the `v` store drained → the call's `v`-argument read point.
8 steps (two splices at the `v`-bearing env ride as kit steps inside
the composite; this is the raw part before the first splice). -/
theorem pu_R3a (σ : ExecState) (na : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (stPuEnvV na) (stPuKF23 na))) ch
      = .ok (.exec (.seqn #[]) (stPuEnvV na) (stPuKF23 na), σ, ch) := by
  with_unfolding_all rfl

theorem pu_R3b (σ : ExecState) (na : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.seq [stFill2, stFill3] (stPuEnvV na) stPuK0)) ch
      = .ok (.exec stFill2 (stPuEnvV na) (stPuKCall na), σ, ch) := by
  with_unfolding_all rfl

theorem pu_R3c (σ : ExecState) (nv sv kv : Int) (sh : GoValue)
    (pl : List Int) (iv : Int) (T : Heap) (na na' : Nat) (ch : Choices) :
    stepFnIter 4 (stStx σ (stHp nv sv kv sh pl iv T) na')
      (.next (.seq [.call #[.var "s"] ⟨"push"⟩ #[.var "s", .var "v"],
        stFill3] (stPuEnvV na) stPuK0)) ch
      = .ok (.evalE (.var "v") (stPuEnvV na)
          (.callArgsK ⟨"push"⟩ stPuPlans [sh] [] (stPuEnvV na)
            (stPuKCall na)),
        stStx σ (stHp nv sv kv sh pl iv T) na', ch) := by
  with_unfolding_all rfl

/-- C1: frame entry → the `$c0` declaration. 4 steps (one splice
inside the composite; this is the two raw pieces). -/
theorem pu_C1a (σ : ExecState) (na : Nat) (ch : Choices) :
    stepFnIter 2 σ
      (.exec pushFunc.body (stPuFrEnv na) (stPuFrameK na)) ch
      = .ok (.exec pushB1 (stPuFrEnv2 na)
          (.seq [pushB2, pushB3] (stPuFrEnv2 na) (stPuFrameK na)), σ,
        ch) := by
  with_unfolding_all rfl

theorem pu_C1b (σ : ExecState) (na : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.seq [.initialization { id := "$c0", typ := sliceU },
          .makeSlice (.var "$c0") tU64 (.intLit 1 .int)
            (some (.intLit 1 .int)), stAssignC00, pushB2, pushB3]
        (stPuFrEnv2 na) (stPuFrameK na))) ch
      = .ok (.exec (.initialization { id := "$c0", typ := sliceU })
          (stPuFrEnv2 na)
          (.seq [.makeSlice (.var "$c0") tU64 (.intLit 1 .int)
              (some (.intLit 1 .int)), stAssignC00, pushB2, pushB3]
            (stPuFrEnv2 na) (stPuFrameK na)), σ, ch) := by
  with_unfolding_all rfl

/-- C3: `$c0` declared → the makeSlice apply point. 7 steps. -/
theorem pu_C3 (σ : ExecState) (na _na' : Nat) (ch : Choices) :
    stepFnIter 7 σ
      (.next (.seq [.makeSlice (.var "$c0") tU64 (.intLit 1 .int)
          (some (.intLit 1 .int)), stAssignC00, pushB2, pushB3]
        (stPuFrEnvC0 na) (stPuFrameK na))) ch
      = .ok (.retV (.int 1 .int)
          (.stmtOpK (.makeSlice tU64 true) 1
            [.int 1 .int, .addr (.base ⟨na + 4⟩)] [] (stPuFrEnvC0 na)
            (stPuKMS na)), σ, ch) := by
  with_unfolding_all rfl

/-- C4: the makeSlice drained → the `$c0` read of the `$c0[0] = v`
store target. 2 steps. -/
theorem pu_C4 (σ : ExecState) (na : Nat) (ch : Choices) :
    stepFnIter 2 σ (.next (stPuKMS na)) ch
      = .ok (.evalE (.var "$c0") (stPuFrEnvC0 na)
          (.tgtOpK (.chain [.index]) [] [.intLit 0 .int] [] [] .vals
            [.var "v"] [] (.seqn #[]) (stPuFrEnvC0 na)
            (.seq [pushB2, pushB3] (stPuFrEnvC0 na) (stPuFrameK na))),
        σ, ch) := by
  with_unfolding_all rfl

/-- C5: the `$c0` handle delivered → the `v` read of the store's RHS.
3 steps. -/
theorem pu_C5 (σ : ExecState) (na : Nat) (hv : GoValue) (ch : Choices) :
    stepFnIter 3 σ
      (.retV hv (.tgtOpK (.chain [.index]) [] [.intLit 0 .int] [] [] .vals
        [.var "v"] [] (.seqn #[]) (stPuFrEnvC0 na)
        (.seq [pushB2, pushB3] (stPuFrEnvC0 na) (stPuFrameK na)))) ch
      = .ok (.evalE (.var "v") (stPuFrEnvC0 na)
          (.rhsK .vals [.chain hv [.int 0 .int] [.index]] [] [] (.seqn #[])
            (stPuFrEnvC0 na)
            (.seq [pushB2, pushB3] (stPuFrEnvC0 na) (stPuFrameK na))),
        σ, ch) := by
  with_unfolding_all rfl

/-- C6: the RHS `v` delivered → the `$c0[0]` store point. 1 step. -/
theorem pu_C6 (σ : ExecState) (na : Nat) (hv w : GoValue) (ch : Choices) :
    stepFnIter 1 σ
      (.retV w (.rhsK .vals [.chain hv [.int 0 .int] [.index]] [] []
        (.seqn #[]) (stPuFrEnvC0 na)
        (.seq [pushB2, pushB3] (stPuFrEnvC0 na) (stPuFrameK na)))) ch
      = .ok (.next (.storeK [.chain hv [.int 0 .int] [.index]] [w]
          (.seqn #[]) (stPuFrEnvC0 na)
          (.seq [pushB2, pushB3] (stPuFrEnvC0 na) (stPuFrameK na))),
        σ, ch) := by
  with_unfolding_all rfl

/-- C7: the `$c0[0]` store drained → the `$c1` declaration. 4 steps
(two splices ride as kit steps; the raw pieces). -/
theorem pu_C7a (σ : ExecState) (na : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (stPuFrEnvC0 na)
        (.seq [pushB2, pushB3] (stPuFrEnvC0 na) (stPuFrameK na)))) ch
      = .ok (.exec (.seqn #[]) (stPuFrEnvC0 na)
          (.seq [pushB2, pushB3] (stPuFrEnvC0 na) (stPuFrameK na)), σ,
        ch) := by
  with_unfolding_all rfl

theorem pu_C7b (σ : ExecState) (na : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.seq [pushB2, pushB3] (stPuFrEnvC0 na) (stPuFrameK na))) ch
      = .ok (.exec pushB2 (stPuFrEnvC0 na)
          (.seq [pushB3] (stPuFrEnvC0 na) (stPuFrameK na)), σ, ch) := by
  with_unfolding_all rfl

theorem pu_C7c (σ : ExecState) (na : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.seq [.initialization { id := "$c1", typ := sliceU },
          .appendSlice (.var "$c1") tU64 (.var "s") (.var "$c0"),
          pushB3] (stPuFrEnvC0 na) (stPuFrameK na))) ch
      = .ok (.exec (.initialization { id := "$c1", typ := sliceU })
          (stPuFrEnvC0 na)
          (.seq [.appendSlice (.var "$c1") tU64 (.var "s") (.var "$c0"),
            pushB3] (stPuFrEnvC0 na) (stPuFrameK na)), σ, ch) := by
  with_unfolding_all rfl

/-- C8: `$c1` declared → the appendSlice's `s` read. 3 steps. -/
theorem pu_C8 (σ : ExecState) (na : Nat) (ch : Choices) :
    stepFnIter 4 σ
      (.next (.seq [.appendSlice (.var "$c1") tU64 (.var "s")
          (.var "$c0"), pushB3] (stPuFrEnvC1 na) (stPuFrameK na))) ch
      = .ok (.evalE (.var "s") (stPuFrEnvC1 na)
          (.stmtOpK (.appendSlice tU64) 1 [.addr (.base ⟨na + 6⟩)]
            [.var "$c0"] (stPuFrEnvC1 na)
            (.seq [pushB3] (stPuFrEnvC1 na) (stPuFrameK na))), σ,
        ch) := by
  with_unfolding_all rfl

/-- C9: the appendSlice `s` operand delivered → the `$c0` read. 1
step. -/
theorem pu_C9 (σ : ExecState) (na : Nat) (shv : GoValue) (ch : Choices) :
    stepFnIter 1 σ
      (.retV shv (.stmtOpK (.appendSlice tU64) 1 [.addr (.base ⟨na + 6⟩)]
        [.var "$c0"] (stPuFrEnvC1 na)
        (.seq [pushB3] (stPuFrEnvC1 na) (stPuFrameK na)))) ch
      = .ok (.evalE (.var "$c0") (stPuFrEnvC1 na)
          (.stmtOpK (.appendSlice tU64) 1 [shv, .addr (.base ⟨na + 6⟩)]
            [] (stPuFrEnvC1 na)
            (.seq [pushB3] (stPuFrEnvC1 na) (stPuFrameK na))), σ,
        ch) := by
  with_unfolding_all rfl

/-- E1: the append applied → the `$c1` read of `$res0 = $c1`. 6 steps
(one splice; the raw pieces). -/
theorem pu_E1a (σ : ExecState) (na : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.seq [pushB3] (stPuFrEnvC1 na) (stPuFrameK na))) ch
      = .ok (.exec pushB3 (stPuFrEnvC1 na)
          (.seq [] (stPuFrEnvC1 na) (stPuFrameK na)), σ, ch) := by
  with_unfolding_all rfl

theorem pu_E1b (σ : ExecState) (na : Nat) (ch : Choices) :
    stepFnIter 4 σ
      (.next (.seq [.assign (.var "$res0") (.var "$c1"), .returnStmt]
        (stPuFrEnvC1 na) (stPuFrameK na))) ch
      = .ok (.evalE (.var "$c1") (stPuFrEnvC1 na)
          (.rhsK .vals [.chain (.addr (.base ⟨na + 3⟩)) [] []] [] []
            (.seqn #[]) (stPuFrEnvC1 na)
            (.seq [.returnStmt] (stPuFrEnvC1 na) (stPuFrameK na))), σ,
        ch) := by
  with_unfolding_all rfl

/-- E2: the `$c1` value delivered → the `$res0` store point. 1 step. -/
theorem pu_E2 (σ : ExecState) (na : Nat) (w : GoValue) (ch : Choices) :
    stepFnIter 1 σ
      (.retV w (.rhsK .vals [.chain (.addr (.base ⟨na + 3⟩)) [] []] [] []
        (.seqn #[]) (stPuFrEnvC1 na)
        (.seq [.returnStmt] (stPuFrEnvC1 na) (stPuFrameK na)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na + 3⟩)) [] []] [w]
          (.seqn #[]) (stPuFrEnvC1 na)
          (.seq [.returnStmt] (stPuFrEnvC1 na) (stPuFrameK na))), σ,
        ch) := by
  with_unfolding_all rfl

/-- E3a: the `$res0` store drained → its body seqn (one raw step; the
splice follows as a kit step). -/
theorem pu_E3a (σ : ExecState) (na : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (stPuFrEnvC1 na)
        (.seq [.returnStmt] (stPuFrEnvC1 na) (stPuFrameK na)))) ch
      = .ok (.exec (.seqn #[]) (stPuFrEnvC1 na)
          (.seq [.returnStmt] (stPuFrEnvC1 na) (stPuFrameK na)), σ,
        ch) := by
  with_unfolding_all rfl

/-- E3b: the return statement unwinds to the frame. 3 steps. -/
theorem pu_E3b (σ : ExecState) (na : Nat) (ch : Choices) :
    stepFnIter 3 σ
      (.next (.seq [.returnStmt] (stPuFrEnvC1 na) (stPuFrameK na))) ch
      = .ok (.returning (stPuFrameK na), σ, ch) := by
  with_unfolding_all rfl

/-- E4: the write-back value read → the `s` store at the front, the
fill-3 head. 2 steps. -/
theorem pu_E4 (σ : ExecState) (na : Nat) (vs0 : GoValue) (ch : Choices) :
    stepFnIter 2 σ
      (.evalE (.ref "s") (stPuEnvV na)
        (.tgtOpK (.chain []) [] [] [] [] .vals [] [vs0] (.seqn #[])
          (stPuEnvV na) (stPuKCall na))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨8⟩)) [] []] [vs0]
          (.seqn #[]) (stPuEnvV na) (stPuKCall na)), σ, ch) := by
  with_unfolding_all rfl

/-- E5: the front `s` store itself + drain to the `pushed[i] = v`
read of `v`. 8 steps (the store lands raw at the concrete front; one
splice + one splice ride as kit steps; these are the raw pieces). -/
theorem pu_E5a (σ : ExecState) (nv sv kv : Int) (sh : GoValue)
    (pl : List Int) (iv : Int) (T : Heap) (na na' : Nat) (sh' : GoValue)
    (ch : Choices) :
    stepFnIter 2 (stStx σ (stHp nv sv kv sh pl iv T) na')
      (.next (.storeK [.chain (.addr (.base ⟨8⟩)) [] []] [sh']
        (.seqn #[]) (stPuEnvV na) (stPuKCall na))) ch
      = .ok (.exec (.seqn #[]) (stPuEnvV na) (stPuKCall na),
          stStx σ (stHp nv sv kv sh' pl iv T) na', ch) := by
  with_unfolding_all rfl

theorem pu_E5b (σ : ExecState) (na : Nat) (ch : Choices) :
    stepFnIter 1 σ (.next (.seq [stFill3] (stPuEnvV na) stPuK0)) ch
      = .ok (.exec stFill3 (stPuEnvV na) (.seq [] (stPuEnvV na) stPuK0),
          σ, ch) := by
  with_unfolding_all rfl

theorem pu_E5c (σ : ExecState) (nv sv kv : Int) (sh : GoValue)
    (pl : List Int) (iv : Int) (T : Heap) (na na' : Nat) (ch : Choices) :
    stepFnIter 6 (stStx σ (stHp nv sv kv sh pl iv T) na')
      (.next (.seq [.assign (.addr (.indexAddr (.ref "pushed")
          (.var "i"))) (.var "v")] (stPuEnvV na) stPuK0)) ch
      = .ok (.evalE (.var "v") (stPuEnvV na)
          (.rhsK .vals
            [.chain (.addr (.base ⟨9⟩)) [.int iv .uint64] [.index]] [] []
            (.seqn #[]) (stPuEnvV na)
            (.seq [] (stPuEnvV na) stPuK0)),
        stStx σ (stHp nv sv kv sh pl iv T) na', ch) := by
  with_unfolding_all rfl

/-- E6: the `v` value delivered → the `pushed[i]` store point. 1
step. -/
theorem pu_E6 (σ : ExecState) (na : Nat) (w : GoValue) (iv : Int)
    (ch : Choices) :
    stepFnIter 1 σ
      (.retV w (.rhsK .vals
        [.chain (.addr (.base ⟨9⟩)) [.int iv .uint64] [.index]] [] []
        (.seqn #[]) (stPuEnvV na) (.seq [] (stPuEnvV na) stPuK0))) ch
      = .ok (.next (.storeK
          [.chain (.addr (.base ⟨9⟩)) [.int iv .uint64] [.index]] [w]
          (.seqn #[]) (stPuEnvV na) (.seq [] (stPuEnvV na) stPuK0)),
        σ, ch) := by
  with_unfolding_all rfl

/-- F1: the `pushed[i]` store drained → the seqn head. 1 step. -/
theorem pu_F1 (σ : ExecState) (na : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (stPuEnvV na)
        (.seq [] (stPuEnvV na) stPuK0))) ch
      = .ok (.exec (.seqn #[]) (stPuEnvV na)
          (.seq [] (stPuEnvV na) stPuK0), σ, ch) := by
  with_unfolding_all rfl

/-- F2: scope exit, loop redispatch, `i` increment, the next test's
delivery — the whole front-only tail of an iteration. 32 steps. -/
theorem pu_F2 (σ : ExecState) (nv sv kv : Int) (sh : GoValue)
    (pl : List Int) (iv : Int) (T : Heap) (na na' : Nat) (ch : Choices) :
    stepFnIter 32 (stStx σ (stHp nv sv kv sh pl iv T) na')
      (.next (.seq [] (stPuEnvV na) stPuK0)) ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < nv))) stPuCmpK,
          stStx σ (stHp nv sv kv sh pl
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            T) na', ch) := by
  with_unfolding_all rfl

/-! ### Heap micro-helpers for the workspace region -/

-- (`lookup_cons_self`/`set_cons_self`/`set_cons_ne`, formerly here,
-- are StepKit's footprint battery since WP arc s2 item 1.)

/-- Setting the `pushed` cell (front 9) rewrites the front in place. -/
theorem stF_set9 {nv sv kv : Int} {r3 r4 : List Int} {r5 : Int}
    {sh : GoValue} {pl pl' : List Int} {iv : Int} {ff : Bool} :
    Heap.set (stF nv sv kv r3 r4 r5 sh pl iv ff) (.base ⟨9⟩)
        (arrC 8 pl')
      = stF nv sv kv r3 r4 r5 sh pl' iv ff := by
  simp [stF, Heap.set]

/-- The `stF` cell-9 lookup (the `pushed` array). -/
theorem stF_lookup9 {nv sv kv : Int} {r3 r4 : List Int} {r5 : Int}
    {sh : GoValue} {pl : List Int} {iv : Int} {ff : Bool} {T : Heap} :
    Heap.lookup (stF nv sv kv r3 r4 r5 sh pl iv ff ++ T) (.base ⟨9⟩)
      = some (arrC 8 pl) := by
  simp [stF, Heap.lookup]

/-- Fresh allocation on the phase heap: set = append, through the
front and the dead region. -/
theorem stHp_alloc {nv sv kv : Int} {sh : GoValue} {pl : List Int}
    {iv : Int} {T : Heap} {x : Nat} {cell : HeapCell} (hx : 12 ≤ x)
    (hnone : Heap.lookup T (.base ⟨x⟩) = none) :
    Heap.set (stHp nv sv kv sh pl iv T) (.base ⟨x⟩) cell
      = stHp nv sv kv sh pl iv (T ++ [(.base ⟨x⟩, cell)]) := by
  rw [stF_set_tail hx, set_fresh hnone]

/-- The front-only cell-9 lookup. -/
theorem stF_only_lookup9 {nv sv kv : Int} {r3 r4 : List Int} {r5 : Int}
    {sh : GoValue} {pl : List Int} {iv : Int} {ff : Bool} :
    Heap.lookup (stF nv sv kv r3 r4 r5 sh pl iv ff) (.base ⟨9⟩)
      = some (arrC 8 pl) := by
  simp [stF, Heap.lookup]

theorem stF_only_lookup3 {nv sv kv : Int} {r3 r4 : List Int} {r5 : Int}
    {sh : GoValue} {pl : List Int} {iv : Int} {ff : Bool} :
    Heap.lookup (stF nv sv kv r3 r4 r5 sh pl iv ff) (.base ⟨3⟩)
      = some (arrC 8 r3) := by
  simp [stF, Heap.lookup]

theorem stF_only_lookup4 {nv sv kv : Int} {r3 r4 : List Int} {r5 : Int}
    {sh : GoValue} {pl : List Int} {iv : Int} {ff : Bool} :
    Heap.lookup (stF nv sv kv r3 r4 r5 sh pl iv ff) (.base ⟨4⟩)
      = some (arrC 8 r4) := by
  simp [stF, Heap.lookup]

theorem stF_only_lookup5 {nv sv kv : Int} {r3 r4 : List Int} {r5 : Int}
    {sh : GoValue} {pl : List Int} {iv : Int} {ff : Bool} :
    Heap.lookup (stF nv sv kv r3 r4 r5 sh pl iv ff) (.base ⟨5⟩)
      = some (u64c r5) := by
  simp [stF, Heap.lookup]

/-! ### The push-iteration composite -/

/-- **The post-append phase of one push iteration** (65 steps): from
the drained append back through `$res0 = $c1`, the frame exit, the `s`
write-back, `pushed[i] = v`, the loop redispatch, the `i` increment and
the next test's delivery. Shared verbatim by the in-place and the spill
case — the tail `Tp` (with the workspace and the live backing, the
`$c1` cell already holding the NEW handle) enters as a parameter with
exactly the lookup/set facts the steps consume. -/
theorem pu_post (σ : ExecState) (n seed k i b c b' c' na na' : Nat)
    (Tp Tp' : Heap) (ch : Choices)
    (hin : i < n) (hcap : n ≤ 8) (hna12 : 12 ≤ na)
    (hfamlt : (seed + i) % 2 ^ 64 < 2 ^ 64)
    (hc1 : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int)
      (sHv b i c) (stPre i seed) (i : Int) Tp) (.base ⟨na + 6⟩)
      = some (slC (sHv b' (i + 1) c')))
    (hres0 : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int)
      (sHv b i c) (stPre i seed) (i : Int) Tp) (.base ⟨na + 3⟩)
      = some (slC nilSl))
    (hsetres : Heap.set (stHp (n : Int) (seed : Int) (k : Int)
        (sHv b i c) (stPre i seed) (i : Int) Tp) (.base ⟨na + 3⟩)
        (slC (sHv b' (i + 1) c'))
      = stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
          (stPre i seed) (i : Int) Tp')
    (hres0' : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int)
      (sHv b i c) (stPre i seed) (i : Int) Tp') (.base ⟨na + 3⟩)
      = some (slC (sHv b' (i + 1) c')))
    (hv' : Heap.lookup Tp' (.base ⟨na⟩)
      = some (u64c (((seed + i) % 2 ^ 64 : Nat) : Int))) :
    stepFnIter 65
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
        (stPre i seed) (i : Int) Tp) na')
      (.next (.seq [pushB3] (stPuFrEnvC1 na) (stPuFrameK na))) ch
      = .ok (.retV (.bool (decide (((i + 1 : Nat) : Int)
            < ((n : Nat) : Int)))) stPuCmpK,
          stStx σ (stHp (n : Int) (seed : Int) (k : Int)
            (sHv b' (i + 1) c') (stPre (i + 1) seed)
            ((i + 1 : Nat) : Int) Tp') na', ch) := by
  have hi8 : i < 8 := by omega
  -- E1: to the `$c1` read
  have g1 := pu_E1a (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
    (sHv b i c) (stPre i seed) (i : Int) Tp) na') na ch
  have g2 : stepFnIter 1
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
        (stPre i seed) (i : Int) Tp) na')
      (.exec pushB3 (stPuFrEnvC1 na)
        (.seq [] (stPuFrEnvC1 na) (stPuFrameK na))) ch
      = .ok (.next (.seq (#[Stmt.assign (.var "$res0") (.var "$c1"),
            Stmt.returnStmt].toList ++ []) (stPuFrEnvC1 na)
            (stPuFrameK na)),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
            (stPre i seed) (i : Int) Tp) na', ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have g3 := pu_E1b (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
    (sHv b i c) (stPre i seed) (i : Int) Tp) na') na ch
  have g4 : stepFnIter 1
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
        (stPre i seed) (i : Int) Tp) na')
      (.evalE (.var "$c1") (stPuFrEnvC1 na)
        (.rhsK .vals [.chain (.addr (.base ⟨na + 3⟩)) [] []] [] []
          (.seqn #[]) (stPuFrEnvC1 na)
          (.seq [.returnStmt] (stPuFrEnvC1 na) (stPuFrameK na)))) ch
      = .ok (.retV (slC (sHv b' (i + 1) c')).value
            (.rhsK .vals [.chain (.addr (.base ⟨na + 3⟩)) [] []] [] []
              (.seqn #[]) (stPuFrEnvC1 na)
              (.seq [.returnStmt] (stPuFrEnvC1 na) (stPuFrameK na))),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
            (stPre i seed) (i : Int) Tp) na', ch) :=
    stepFnIter_one (stepFn_var rfl hc1)
  have g5 := pu_E2 (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
    (sHv b i c) (stPre i seed) (i : Int) Tp) na') na
    (sHv b' (i + 1) c') ch
  have hstres : storeTarget
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
        (stPre i seed) (i : Int) Tp) na')
      (.chain (.addr (.base ⟨na + 3⟩)) [] []) (sHv b' (i + 1) c')
      = .ok (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
          (stPre i seed) (i : Int) Tp') na') := by
    have h := storeTarget_addr
      (σ := stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
        (stPre i seed) (i : Int) Tp) na')
      (a := ⟨na + 3⟩) (old := nilSl) (v := sHv b' (i + 1) c')
      hres0 (st_norm_sliceU _ _)
    rwa [hsetres] at h
  have g6 : stepFnIter 1
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
        (stPre i seed) (i : Int) Tp) na')
      (.next (.storeK [.chain (.addr (.base ⟨na + 3⟩)) [] []]
        [sHv b' (i + 1) c'] (.seqn #[]) (stPuFrEnvC1 na)
        (.seq [.returnStmt] (stPuFrEnvC1 na) (stPuFrameK na)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (stPuFrEnvC1 na)
            (.seq [.returnStmt] (stPuFrEnvC1 na) (stPuFrameK na))),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
            (stPre i seed) (i : Int) Tp') na', ch) :=
    stepFnIter_one (stepFn_store_step hstres)
  have g7 := pu_E3a (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
    (sHv b i c) (stPre i seed) (i : Int) Tp') na') na ch
  have g8 : stepFnIter 1
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
        (stPre i seed) (i : Int) Tp') na')
      (.exec (.seqn #[]) (stPuFrEnvC1 na)
        (.seq [.returnStmt] (stPuFrEnvC1 na) (stPuFrameK na))) ch
      = .ok (.next (.seq (#[].toList ++ [.returnStmt]) (stPuFrEnvC1 na)
            (stPuFrameK na)),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
            (stPre i seed) (i : Int) Tp') na', ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have g9 := pu_E3b (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
    (sHv b i c) (stPre i seed) (i : Int) Tp') na') na ch
  -- the frame exit
  have g10 : stepFnIter 1
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
        (stPre i seed) (i : Int) Tp') na')
      (.returning (stPuFrameK na)) ch
      = .ok (.evalE (.ref "s") (stPuEnvV na)
            (.tgtOpK (.chain []) [] [] [] [] .vals []
              [slC (sHv b' (i + 1) c')|>.value] (.seqn #[]) (stPuEnvV na)
              (stPuKCall na)),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
            (stPre i seed) (i : Int) Tp') na', ch) :=
    stepFnIter_one (stepFn_return_frame (st_loadMany1 hres0'))
  have g11 := pu_E4 (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
    (sHv b i c) (stPre i seed) (i : Int) Tp') na') na
    (sHv b' (i + 1) c') ch
  have g12 := pu_E5a σ (n : Int) (seed : Int) (k : Int) (sHv b i c)
    (stPre i seed) (i : Int) Tp' na na' (sHv b' (i + 1) c') ch
  have g13 : stepFnIter 1
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
        (sHv b' (i + 1) c') (stPre i seed) (i : Int) Tp') na')
      (.exec (.seqn #[]) (stPuEnvV na) (stPuKCall na)) ch
      = .ok (.next (.seq (#[].toList ++ [stFill3]) (stPuEnvV na)
            stPuK0),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int)
            (sHv b' (i + 1) c') (stPre i seed) (i : Int) Tp') na', ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have g14 := pu_E5b (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
    (sHv b' (i + 1) c') (stPre i seed) (i : Int) Tp') na') na ch
  have g15 : stepFnIter 1
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
        (sHv b' (i + 1) c') (stPre i seed) (i : Int) Tp') na')
      (.exec stFill3 (stPuEnvV na) (.seq [] (stPuEnvV na) stPuK0)) ch
      = .ok (.next (.seq (#[Stmt.assign (.addr (.indexAddr
            (.ref "pushed") (.var "i"))) (.var "v")].toList ++ [])
            (stPuEnvV na) stPuK0),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int)
            (sHv b' (i + 1) c') (stPre i seed) (i : Int) Tp') na', ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have g16 := pu_E5c σ (n : Int) (seed : Int) (k : Int)
    (sHv b' (i + 1) c') (stPre i seed) (i : Int) Tp' na na' ch
  have hv'' : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int)
      (sHv b' (i + 1) c') (stPre i seed) (i : Int) Tp') (.base ⟨na⟩)
      = some (u64c (((seed + i) % 2 ^ 64 : Nat) : Int)) := by
    rw [stF_lookup_tail hna12]
    exact hv'
  have g17 : stepFnIter 1
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
        (sHv b' (i + 1) c') (stPre i seed) (i : Int) Tp') na')
      (.evalE (.var "v") (stPuEnvV na)
        (.rhsK .vals
          [.chain (.addr (.base ⟨9⟩)) [.int (i : Int) .uint64] [.index]]
          [] [] (.seqn #[]) (stPuEnvV na)
          (.seq [] (stPuEnvV na) stPuK0))) ch
      = .ok (.retV (.int (((seed + i) % 2 ^ 64 : Nat) : Int) .uint64)
            (.rhsK .vals
              [.chain (.addr (.base ⟨9⟩)) [.int (i : Int) .uint64]
                [.index]] [] [] (.seqn #[]) (stPuEnvV na)
              (.seq [] (stPuEnvV na) stPuK0)),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int)
            (sHv b' (i + 1) c') (stPre i seed) (i : Int) Tp') na', ch) :=
    stepFnIter_one (stepFn_var
      (c := u64c (((seed + i) % 2 ^ 64 : Nat) : Int)) rfl hv'')
  have g18 := pu_E6 (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
    (sHv b' (i + 1) c') (stPre i seed) (i : Int) Tp') na') na
    (.int (((seed + i) % 2 ^ 64 : Nat) : Int) .uint64) (i : Int) ch
  -- the pushed[i] store, at the concrete front
  have hstp : storeTarget
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
        (sHv b' (i + 1) c') (stPre i seed) (i : Int) Tp') na')
      (.chain (.addr (.base ⟨9⟩)) [.int (i : Int) .uint64] [.index])
      (.int (((seed + i) % 2 ^ 64 : Nat) : Int) .uint64)
      = .ok (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
          (sHv b' (i + 1) c') (stPre (i + 1) seed) (i : Int) Tp')
          na') := by
    have h := storeTarget_arrayLocal_u64
      (σ := stStx σ (stHp (n : Int) (seed : Int) (k : Int)
        (sHv b' (i + 1) c') (stPre i seed) (i : Int) Tp') na')
      (a := ⟨9⟩) (N := 8) (i := i) (ik := .uint64) (l := stPre i seed)
      (w := (((seed + i) % 2 ^ 64 : Nat) : Int))
      (stF_lookup9)
      (by rw [stPre_length (by omega)]; omega)
      (stPre_length (by omega)) stPre_range
      ⟨Int.natCast_nonneg _, by exact_mod_cast hfamlt⟩
    rw [stPre_set hi8] at h
    have hset : Heap.set (stHp (n : Int) (seed : Int) (k : Int)
        (sHv b' (i + 1) c') (stPre i seed) (i : Int) Tp') (.base ⟨9⟩)
        (arrC 8 (stPre (i + 1) seed))
        = stHp (n : Int) (seed : Int) (k : Int) (sHv b' (i + 1) c')
            (stPre (i + 1) seed) (i : Int) Tp' := by
      rw [show (stHp (n : Int) (seed : Int) (k : Int) (sHv b' (i + 1) c')
          (stPre i seed) (i : Int) Tp' : Heap)
          = stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0
              (sHv b' (i + 1) c') (stPre i seed) (i : Int) false ++ Tp'
          from rfl,
        set_append_left stF_only_lookup9, stF_set9]
    rwa [hset] at h
  have g19 : stepFnIter 1
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
        (sHv b' (i + 1) c') (stPre i seed) (i : Int) Tp') na')
      (.next (.storeK
        [.chain (.addr (.base ⟨9⟩)) [.int (i : Int) .uint64] [.index]]
        [.int (((seed + i) % 2 ^ 64 : Nat) : Int) .uint64] (.seqn #[])
        (stPuEnvV na) (.seq [] (stPuEnvV na) stPuK0))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (stPuEnvV na)
            (.seq [] (stPuEnvV na) stPuK0)),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int)
            (sHv b' (i + 1) c') (stPre (i + 1) seed) (i : Int) Tp')
            na', ch) :=
    stepFnIter_one (stepFn_store_step hstp)
  have g20 := pu_F1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
    (sHv b' (i + 1) c') (stPre (i + 1) seed) (i : Int) Tp') na') na ch
  have g21 : stepFnIter 1
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
        (sHv b' (i + 1) c') (stPre (i + 1) seed) (i : Int) Tp') na')
      (.exec (.seqn #[]) (stPuEnvV na)
        (.seq [] (stPuEnvV na) stPuK0)) ch
      = .ok (.next (.seq (#[].toList ++ []) (stPuEnvV na) stPuK0),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int)
            (sHv b' (i + 1) c') (stPre (i + 1) seed) (i : Int) Tp')
            na', ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have g22 := pu_F2 σ (n : Int) (seed : Int) (k : Int)
    (sHv b' (i + 1) c') (stPre (i + 1) seed) (i : Int) Tp' na na' ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    unorm_nat_of_lt (by omega : i + 1 < 2 ^ 64),
    unorm_nat_of_lt (by omega : i + 1 < 2 ^ 64)] at g22
  -- assemble
  have hall := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      g1 g2) g3) g4) g5) g6) g7) g8) g9) g10) g11) g12) g13) g14) g15)
      g16) g17) g18) g19) g20) g21) g22
  rw [show (65 : Nat)
      = 1 + 1 + 4 + 1 + 1 + 1 + 1 + 1 + 3 + 1 + 2 + 2 + 1 + 1 + 1 + 6
        + 1 + 1 + 1 + 1 + 1 + 32 from rfl]
  exact hall

/-- The push-loop INVARIANT on the backing: either we are before the
first push (the front's cap-0 cell 7) or the live backing lives in the
tail at a symbolic address/capacity. -/
def PuInv (T : Heap) (b c i seed na : Nat) : Prop :=
  (b = 7 ∧ c = 0)
    ∨ (12 ≤ b ∧ b < na
        ∧ Heap.lookup T (.base ⟨b⟩)
            = some (backC c (stFam i seed ++ List.replicate (c - i) 0)))

/-- **One push iteration, capacity- and address-generic**: 130 steps
from the checkpoint at `i` to the checkpoint at `i+1`, for SOME new
backing address/capacity/allocation front/tail/choice stream — one
choice consumed exactly when the append spills (`c = i`), none when it
fits (`i < c`). -/
theorem pu_iter (σ : ExecState) (n seed k i b c na : Nat) (T : Heap)
    (ch : Choices)
    (henterP : ∀ (H : Heap) (a : Nat) (sh : GoValue) (w : Int),
      enterFrame (stStx σ H a) ⟨"push"⟩ [sh, .int w .uint64]
        = .ok (pushFunc,
            [[("$res0", .base ⟨a + 2⟩), ("v", .base ⟨a + 1⟩),
              ("s", .base ⟨a⟩)]],
            [.base ⟨a + 2⟩],
            stStx σ
              (Heap.set (Heap.set (Heap.set H (.base ⟨a⟩) (slC sh))
                  (.base ⟨a + 1⟩) (u64c (IntKind.normalize .uint64 w)))
                (.base ⟨a + 2⟩) (slC nilSl))
              (a + 3)))
    (hin : i < n) (hcap : n ≤ 8) (hic : i ≤ c)
    (hbi : PuInv T b c i seed na)
    (hna12 : 12 ≤ na) (hdead : DeadFrom T na) :
    ∃ (b' c' na' : Nat) (T' : Heap) (ch' : Choices),
      stepFnIter 130
        (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
          (stPre i seed) (i : Int) T) na)
        (.retV (.bool true) stPuCmpK) ch
      = .ok (.retV (.bool (decide (((i + 1 : Nat) : Int)
            < ((n : Nat) : Int)))) stPuCmpK,
          stStx σ (stHp (n : Int) (seed : Int) (k : Int)
            (sHv b' (i + 1) c') (stPre (i + 1) seed)
            ((i + 1 : Nat) : Int) T') na', ch')
      ∧ i + 1 ≤ c' ∧ PuInv T' b' c' (i + 1) seed na'
      ∧ na ≤ na' ∧ 12 ≤ na' ∧ DeadFrom T' na' := by
  have hfamlt : (seed + i) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by omega)
  have hfr : (0 : Int) ≤ (((seed + i) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + i) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    refine ⟨Int.natCast_nonneg _, ?_⟩
    exact_mod_cast hfamlt
  -- ## A: checkpoint → v allocated and stored (19 steps)
  have h1 := pu_R1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
    (sHv b i c) (stPre i seed) (i : Int) T) na) ch
  have h2 : stepFnIter 1
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
        (stPre i seed) (i : Int) T) na)
      (.exec (.initialization { id := "v", typ := tU64 }) stPuEnv2
        (.seq [stAssignV, stFill2, stFill3] stPuEnv2 stPuK0)) ch
      = .ok (.next (.seq [stAssignV, stFill2, stFill3] (stPuEnvV na)
            stPuK0),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
            (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c 0)]))
            (na + 1), ch) := by
    have h := stepFn_init_seq (σ := stStx σ (stHp (n : Int) (seed : Int)
      (k : Int) (sHv b i c) (stPre i seed) (i : Int) T) na)
      (p := { id := "v", typ := tU64 })
      (rest := [stAssignV, stFill2, stFill3]) (env := stPuEnv2)
      (k := stPuK0) (ch := ch) (v := .int 0 .uint64)
      (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
    dsimp only at h
    rw [stF_set_fresh hna12 hdead (Nat.le_refl na)] at h
    exact stepFnIter_one h
  have hA0 := stepFnIter_chain h1 h2
  have h3 := pu_R2 σ (n : Int) (seed : Int) (k : Int) (sHv b i c)
    (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c 0)]) na (na + 1) ch
  rw [unorm_add_nat seed i] at h3
  have hA1 := stepFnIter_chain hA0 h3
  -- the v store
  have hlookV0 : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int)
      (sHv b i c) (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c 0)])) (.base ⟨na⟩) = some (u64c 0) := by
    rw [stF_lookup_tail hna12,
      lookup_append_right (hdead na (Nat.le_refl na)),
      lookup_singleton_self]
  have hst4 : storeTarget
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
        (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c 0)])) (na + 1))
      (.chain (.addr (.base ⟨na⟩)) [] [])
      (.int (((seed + i) % 2 ^ 64 : Nat) : Int) .uint64)
      = .ok (stStx σ
          (Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
            (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c 0)]))
            (.base ⟨na⟩)
            (u64c (IntKind.normalize .uint64
              (((seed + i) % 2 ^ 64 : Nat) : Int))))
          (na + 1)) :=
    storeTarget_addr hlookV0
      (st_norm_u64 _ (((seed + i) % 2 ^ 64 : Nat) : Int))
  have hset4 : Heap.set (stHp (n : Int) (seed : Int) (k : Int)
      (sHv b i c) (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c 0)])) (.base ⟨na⟩) (u64c (((seed + i) % 2 ^ 64 : Nat) : Int))
      = stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
          (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int))]) := by
    rw [stF_set_tail hna12,
      set_append_right (hdead na (Nat.le_refl na)), set_singleton_self]
  have h4 : stepFnIter 1
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
        (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c 0)])) (na + 1))
      (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
        [.int (((seed + i) % 2 ^ 64 : Nat) : Int) .uint64]
        (.seqn #[]) (stPuEnvV na) (stPuKF23 na))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (stPuEnvV na)
            (stPuKF23 na)),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
            (stPre i seed) (i : Int)
            (T ++ [(.base ⟨na⟩,
              u64c (((seed + i) % 2 ^ 64 : Nat) : Int))])) (na + 1),
          ch) := by
    have h := stepFnIter_one (stepFn_store_step (rs := []) (vs := [])
      (body := .seqn #[]) (env := stPuEnvV na) (k := stPuKF23 na)
      (ch := ch) hst4)
    rwa [unorm_nat_of_lt hfamlt, hset4] at h
  have hA := stepFnIter_chain hA1 h4
  -- ## B: to the call's frame entry (9 steps)
  have h5 := pu_R3a (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
    (sHv b i c) (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int))]))
    (na + 1)) na ch
  have h6 := stepFnIter_one (stepFn_seqn_splice (σ := stStx σ
    (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c) (stPre i seed)
      (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int))])) (na + 1)) (ss := #[])
    (env := stPuEnvV na) (rest := [stFill2, stFill3]) (k := stPuK0)
    (ch := ch))
  have h7 := pu_R3b (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
    (sHv b i c) (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int))]))
    (na + 1)) na ch
  have h8 := stepFnIter_one (stepFn_seqn_splice (σ := stStx σ
    (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c) (stPre i seed)
      (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int))])) (na + 1))
    (ss := #[.call #[.var "s"] ⟨"push"⟩ #[.var "s", .var "v"]])
    (env := stPuEnvV na) (rest := [stFill3]) (k := stPuK0) (ch := ch))
  have h9 := pu_R3c σ (n : Int) (seed : Int) (k : Int) (sHv b i c)
    (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int))]) na (na + 1) ch
  have hlookV : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int)
      (sHv b i c) (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int))])) (.base ⟨na⟩) = some (u64c (((seed + i) % 2 ^ 64 : Nat) : Int)) := by
    rw [stF_lookup_tail hna12,
      lookup_append_right (hdead na (Nat.le_refl na)),
      lookup_singleton_self]
  have h10 : stepFnIter 1
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
        (stPre i seed) (i : Int)
        (T ++ [(.base ⟨na⟩,
          u64c (((seed + i) % 2 ^ 64 : Nat) : Int))])) (na + 1))
      (.evalE (.var "v") (stPuEnvV na)
        (.callArgsK ⟨"push"⟩ stPuPlans [sHv b i c] [] (stPuEnvV na)
          (stPuKCall na))) ch
      = .ok (.retV (.int (((seed + i) % 2 ^ 64 : Nat) : Int) .uint64)
            (.callArgsK ⟨"push"⟩ stPuPlans [sHv b i c] [] (stPuEnvV na)
              (stPuKCall na)),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
            (stPre i seed) (i : Int)
            (T ++ [(.base ⟨na⟩,
              u64c (((seed + i) % 2 ^ 64 : Nat) : Int))])) (na + 1),
          ch) :=
    stepFnIter_one (stepFn_var
      (c := u64c (((seed + i) % 2 ^ 64 : Nat) : Int)) rfl hlookV)
  have hB0 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain hA h5) h6) h7) h8) h9
  have hB1 := stepFnIter_chain hB0 h10
  -- frame entry
  have hent := henterP (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
    (stPre i seed) (i : Int)
    (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int))]))
    (na + 1) (sHv b i c) (((seed + i) % 2 ^ 64 : Nat) : Int)
  rw [unorm_nat_of_lt hfamlt,
    show na + 1 + 1 = na + 2 from rfl, show na + 1 + 2 = na + 3 from rfl,
    show na + 1 + 3 = na + 4 from rfl] at hent
  -- massage the three parameter/result allocations into tail appends
  have hlkA1 : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int)
      (sHv b i c) (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int))]))
      (.base ⟨na + 1⟩) = none := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdead (na + 1) (by omega)),
      lookup_cons_ne (base_beq_false (by omega))]
    rfl
  have hlkA2 : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int)
      (sHv b i c) (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int))]))
      (.base ⟨na + 2⟩) = none := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdead (na + 2) (by omega)),
      lookup_cons_ne (base_beq_false (by omega))]
    rfl
  have hlkA3 : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int)
      (sHv b i c) (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int))]))
      (.base ⟨na + 3⟩) = none := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdead (na + 3) (by omega)),
      lookup_cons_ne (base_beq_false (by omega))]
    rfl
  rw [set_fresh hlkA1] at hent
  rw [set_fresh (show Heap.lookup ((stHp (n : Int) (seed : Int) (k : Int)
      (sHv b i c) (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int))]))
      ++ [(.base ⟨na + 1⟩, slC (sHv b i c))]) (.base ⟨na + 2⟩) = none from by
    rw [lookup_append_right hlkA2,
      lookup_cons_ne (base_beq_false (by omega))]
    rfl)] at hent
  rw [set_fresh (show Heap.lookup (((stHp (n : Int) (seed : Int) (k : Int)
      (sHv b i c) (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int))]))
      ++ [(.base ⟨na + 1⟩, slC (sHv b i c))])
      ++ [(.base ⟨na + 2⟩,
        u64c (((seed + i) % 2 ^ 64 : Nat) : Int))]) (.base ⟨na + 3⟩)
      = none from by
    rw [lookup_append_right (show Heap.lookup ((stHp (n : Int)
        (seed : Int) (k : Int) (sHv b i c) (stPre i seed) (i : Int)
        (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int))]))
        ++ [(.base ⟨na + 1⟩, slC (sHv b i c))]) (.base ⟨na + 3⟩)
        = none from by
      rw [lookup_append_right hlkA3,
        lookup_cons_ne (base_beq_false (by omega))]
      rfl),
      lookup_cons_ne (base_beq_false (by omega))]
    rfl)] at hent
  rw [show (((stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
        (stPre i seed) (i : Int)
        (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int))]))
      ++ [(.base ⟨na + 1⟩, slC (sHv b i c))])
      ++ [(.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int))])
      ++ [(.base ⟨na + 3⟩, slC nilSl)]
      = stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
          (stPre i seed) (i : Int)
          (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 1⟩, slC (sHv b i c)),
            (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 3⟩, slC nilSl)]) from by
    simp [stHp]] at hent
  have h11 := stepFnIter_one (stepFn_call_enter (plans := stPuPlans)
    (env := stPuEnvV na) (k := stPuKCall na) (vals := [sHv b i c])
    (v := .int (((seed + i) % 2 ^ 64 : Nat) : Int) .uint64) (ch := ch) hent)
  have hB := stepFnIter_chain hB1 h11
  -- ## C: through the push frame to the append apply point
  -- W3-tail: v, s-param, v-param, $res0
  have h12 := pu_C1a (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
    (sHv b i c) (stPre i seed) (i : Int)
    (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
      (.base ⟨na + 1⟩, slC (sHv b i c)),
      (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
      (.base ⟨na + 3⟩, slC nilSl)])) (na + 4)) na ch
  have h13 : stepFnIter 1
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
        (stPre i seed) (i : Int)
        (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
          (.base ⟨na + 1⟩, slC (sHv b i c)),
          (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
          (.base ⟨na + 3⟩, slC nilSl)])) (na + 4))
      (.exec pushB1 (stPuFrEnv2 na)
        (.seq [pushB2, pushB3] (stPuFrEnv2 na) (stPuFrameK na))) ch
      = .ok (.next (.seq (#[Stmt.initialization
            { id := "$c0", typ := sliceU },
            Stmt.makeSlice (.var "$c0") tU64 (.intLit 1 .int)
              (some (.intLit 1 .int)), stAssignC00].toList
            ++ [pushB2, pushB3]) (stPuFrEnv2 na) (stPuFrameK na)),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
            (stPre i seed) (i : Int)
            (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
              (.base ⟨na + 1⟩, slC (sHv b i c)),
              (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
              (.base ⟨na + 3⟩, slC nilSl)])) (na + 4), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have h14 := pu_C1b (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
    (sHv b i c) (stPre i seed) (i : Int)
    (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
      (.base ⟨na + 1⟩, slC (sHv b i c)),
      (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
      (.base ⟨na + 3⟩, slC nilSl)])) (na + 4)) na ch
  have hlkW3 : ∀ x : Nat, na + 4 ≤ x →
      Heap.lookup (T ++ [(.base ⟨na⟩,
          u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl)]) (.base ⟨x⟩) = none := by
    intro x hx
    rw [lookup_append_right (hdead x (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega))]
    rfl
  have h15 : stepFnIter 1
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
        (stPre i seed) (i : Int)
        (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
          (.base ⟨na + 1⟩, slC (sHv b i c)),
          (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
          (.base ⟨na + 3⟩, slC nilSl)])) (na + 4))
      (.exec (.initialization { id := "$c0", typ := sliceU })
        (stPuFrEnv2 na)
        (.seq [.makeSlice (.var "$c0") tU64 (.intLit 1 .int)
            (some (.intLit 1 .int)), stAssignC00, pushB2, pushB3]
          (stPuFrEnv2 na) (stPuFrameK na))) ch
      = .ok (.next (.seq [.makeSlice (.var "$c0") tU64 (.intLit 1 .int)
            (some (.intLit 1 .int)), stAssignC00, pushB2, pushB3]
            (stPuFrEnvC0 na) (stPuFrameK na)),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
            (stPre i seed) (i : Int)
            (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
              (.base ⟨na + 1⟩, slC (sHv b i c)),
              (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
              (.base ⟨na + 3⟩, slC nilSl),
              (.base ⟨na + 4⟩, slC nilSl)])) (na + 5), ch) := by
    have h := stepFn_init_seq (σ := stStx σ (stHp (n : Int) (seed : Int)
      (k : Int) (sHv b i c) (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl)])) (na + 4))
      (p := { id := "$c0", typ := sliceU })
      (rest := [.makeSlice (.var "$c0") tU64 (.intLit 1 .int)
        (some (.intLit 1 .int)), stAssignC00, pushB2, pushB3])
      (env := stPuFrEnv2 na) (k := stPuFrameK na) (ch := ch)
      (v := nilSl)
      (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
    dsimp only at h
    rw [stHp_alloc (by omega) (hlkW3 (na + 4) (by omega)),
      show (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
          (.base ⟨na + 1⟩, slC (sHv b i c)),
          (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
          (.base ⟨na + 3⟩, slC nilSl)])
        ++ [(.base ⟨na + 4⟩, ⟨some sliceU, nilSl⟩)]
        = T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
          (.base ⟨na + 1⟩, slC (sHv b i c)),
          (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
          (.base ⟨na + 3⟩, slC nilSl),
          (.base ⟨na + 4⟩, slC nilSl)] from by simp] at h
    exact stepFnIter_one h
  have h16 := pu_C3 (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
    (sHv b i c) (stPre i seed) (i : Int)
    (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
      (.base ⟨na + 1⟩, slC (sHv b i c)),
      (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
      (.base ⟨na + 3⟩, slC nilSl),
      (.base ⟨na + 4⟩, slC nilSl)])) (na + 5)) na (na + 5) ch
  -- makeSlice apply: the one-zero backing at na+5, the handle into na+4
  have hlkW4 : ∀ x : Nat, na + 5 ≤ x →
      Heap.lookup (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC nilSl)]) (.base ⟨x⟩) = none := by
    intro x hx
    rw [lookup_append_right (hdead x (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega))]
    rfl
  have hlkC0cell : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC nilSl)])) (.base ⟨na + 4⟩)
      = some ⟨some sliceU, nilSl⟩ := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdead (na + 4) (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self]
  have h17 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC nilSl)])) (na + 5))
      (.retV (.int 1 .int)
        (.stmtOpK (.makeSlice tU64 true) 1
          [.int 1 .int, .addr (.base ⟨na + 4⟩)] [] (stPuFrEnvC0 na)
          (stPuKMS na))) ch
      = .ok (.next (stPuKMS na), (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [0])])) (na + 6)), ch) := by
    have happ := st_make1_apply (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC nilSl)])) (na + 5)) (na + 4) nilSl ch
      hlkC0cell (by intro hq; simp at hq)
    dsimp only at happ
    rw [stHp_alloc (by omega) (hlkW4 (na + 5) (by omega))] at happ
    rw [show (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC nilSl)]) ++ [(.base ⟨na + 5⟩, arrC 1 [0])]
        = T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC nilSl),
        (.base ⟨na + 5⟩, arrC 1 [0])] from by
      simp] at happ
    rw [show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC nilSl),
        (.base ⟨na + 5⟩, arrC 1 [0])]))
        (.base ⟨na + 4⟩) (slC (sHv (na + 5) 1 1))
        = (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [0])])) from by
      rw [stF_set_tail (by omega),
        set_append_right (hdead (na + 4) (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_self]] at happ
    exact stepFnIter_one (stepFn_stmtOp_apply
      (done := [.int 1 .int, .addr (.base ⟨na + 4⟩)]) (nt := 1)
      (env := stPuFrEnvC0 na) (k := stPuKMS na) happ)
  have h18 := pu_C4 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [0])])) (na + 6)) na ch
  have hlkC0h : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [0])])) (.base ⟨na + 4⟩)
      = some (slC (sHv (na + 5) 1 1)) := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdead (na + 4) (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self]
  have h19 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [0])])) (na + 6))
      (.evalE (.var "$c0") (stPuFrEnvC0 na)
        (.tgtOpK (.chain [.index]) [] [.intLit 0 .int] [] [] .vals
          [.var "v"] [] (.seqn #[]) (stPuFrEnvC0 na)
          (.seq [pushB2, pushB3] (stPuFrEnvC0 na) (stPuFrameK na)))) ch
      = .ok (.retV (sHv (na + 5) 1 1)
          (.tgtOpK (.chain [.index]) [] [.intLit 0 .int] [] [] .vals
            [.var "v"] [] (.seqn #[]) (stPuFrEnvC0 na)
            (.seq [pushB2, pushB3] (stPuFrEnvC0 na) (stPuFrameK na))),
        (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [0])])) (na + 6)), ch) :=
    stepFnIter_one (stepFn_var (c := slC (sHv (na + 5) 1 1)) rfl hlkC0h)
  have h20 := pu_C5 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [0])])) (na + 6)) na (sHv (na + 5) 1 1) ch
  have hlkVp : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [0])])) (.base ⟨na + 2⟩)
      = some (u64c (((seed + i) % 2 ^ 64 : Nat) : Int)) := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdead (na + 2) (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self]
  have h21 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [0])])) (na + 6))
      (.evalE (.var "v") (stPuFrEnvC0 na)
        (.rhsK .vals [.chain (sHv (na + 5) 1 1) [.int 0 .int] [.index]]
          [] [] (.seqn #[]) (stPuFrEnvC0 na)
          (.seq [pushB2, pushB3] (stPuFrEnvC0 na) (stPuFrameK na)))) ch
      = .ok (.retV (.int (((seed + i) % 2 ^ 64 : Nat) : Int) .uint64)
          (.rhsK .vals [.chain (sHv (na + 5) 1 1) [.int 0 .int] [.index]]
            [] [] (.seqn #[]) (stPuFrEnvC0 na)
            (.seq [pushB2, pushB3] (stPuFrEnvC0 na) (stPuFrameK na))),
        (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [0])])) (na + 6)), ch) :=
    stepFnIter_one (stepFn_var (c := u64c (((seed + i) % 2 ^ 64 : Nat) : Int)) rfl hlkVp)
  have h22 := pu_C6 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [0])])) (na + 6)) na (sHv (na + 5) 1 1)
    (.int (((seed + i) % 2 ^ 64 : Nat) : Int) .uint64) ch
  have hlkBk1 : Heap.lookup (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [0])])) (na + 6)).heap (.base ⟨na + 5⟩)
      = some ⟨some (.array 1 tU64),
          .array ⟨([0] : List Int).map (fun v => .int v .uint64)⟩⟩ := by
    show Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [0])])) (.base ⟨na + 5⟩) = _
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdead (na + 5) (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self]
  have h23 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [0])])) (na + 6))
      (.next (.storeK [.chain (sHv (na + 5) 1 1) [.int 0 .int] [.index]]
        [.int (((seed + i) % 2 ^ 64 : Nat) : Int) .uint64] (.seqn #[]) (stPuFrEnvC0 na)
        (.seq [pushB2, pushB3] (stPuFrEnvC0 na) (stPuFrameK na)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (stPuFrEnvC0 na)
            (.seq [pushB2, pushB3] (stPuFrEnvC0 na) (stPuFrameK na))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)])])) (na + 6)), ch) := by
    have hst := storeTarget_slice_u64
      (σ := (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [0])])) (na + 6))) (a := ⟨na + 5⟩) (off := 0) (len := 1)
      (cap := 1) (i := 0) (n := 1) (ik := .int) (l := [0]) (w := (((seed + i) % 2 ^ 64 : Nat) : Int))
      hlkBk1 (Nat.le_refl 1) (Nat.lt_irrefl 0 |> fun _ => Nat.zero_lt_one)
      (by simp) (by simp) (by intro v hv; simp at hv; omega) hfr
    rw [show ([0] : List Int).set (0 + 0) (((seed + i) % 2 ^ 64 : Nat) : Int) = [(((seed + i) % 2 ^ 64 : Nat) : Int)] from rfl] at hst
    rw [show Heap.set (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [0])])) (na + 6)).heap (.base ⟨na + 5⟩)
        ⟨some (.array 1 tU64),
          .array ⟨([(((seed + i) % 2 ^ 64 : Nat) : Int)] : List Int).map (fun v => .int v .uint64)⟩⟩
        = (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)])])) from by
      show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [0])])) _ _ = _
      rw [stF_set_tail (by omega),
        set_append_right (hdead (na + 5) (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_self]] at hst
    exact stepFnIter_one (stepFn_store_step hst)
  have h24 := pu_C7a (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)])])) (na + 6)) na ch
  have h25 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)])])) (na + 6))
      (.exec (.seqn #[]) (stPuFrEnvC0 na)
        (.seq [pushB2, pushB3] (stPuFrEnvC0 na) (stPuFrameK na))) ch
      = .ok (.next (.seq (#[].toList ++ [pushB2, pushB3])
            (stPuFrEnvC0 na) (stPuFrameK na)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)])])) (na + 6)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have h26 := pu_C7b (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)])])) (na + 6)) na ch
  have h27 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)])])) (na + 6))
      (.exec pushB2 (stPuFrEnvC0 na)
        (.seq [pushB3] (stPuFrEnvC0 na) (stPuFrameK na))) ch
      = .ok (.next (.seq (#[Stmt.initialization
            { id := "$c1", typ := sliceU },
            Stmt.appendSlice (.var "$c1") tU64 (.var "s")
              (.var "$c0")].toList ++ [pushB3]) (stPuFrEnvC0 na)
            (stPuFrameK na)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)])])) (na + 6)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have h28 := pu_C7c (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)])])) (na + 6)) na ch
  have hlkW6 : ∀ x : Nat, na + 6 ≤ x →
      Heap.lookup (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)])]) (.base ⟨x⟩) = none := by
    intro x hx
    rw [lookup_append_right (hdead x (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega))]
    rfl
  have h29 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)])])) (na + 6))
      (.exec (.initialization { id := "$c1", typ := sliceU })
        (stPuFrEnvC0 na)
        (.seq [.appendSlice (.var "$c1") tU64 (.var "s") (.var "$c0"),
          pushB3] (stPuFrEnvC0 na) (stPuFrameK na))) ch
      = .ok (.next (.seq [.appendSlice (.var "$c1") tU64 (.var "s")
            (.var "$c0"), pushB3] (stPuFrEnvC1 na) (stPuFrameK na)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) (na + 7)), ch) := by
    have h := stepFn_init_seq (σ := (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)])])) (na + 6)))
      (p := { id := "$c1", typ := sliceU })
      (rest := [.appendSlice (.var "$c1") tU64 (.var "s") (.var "$c0"),
        pushB3])
      (env := stPuFrEnvC0 na) (k := stPuFrameK na) (ch := ch)
      (v := nilSl)
      (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
    dsimp only at h
    rw [stHp_alloc (by omega) (hlkW6 (na + 6) (by omega)),
      show (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)])]) ++ [(.base ⟨na + 6⟩, ⟨some sliceU, nilSl⟩)]
        = T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)] from by simp] at h
    exact stepFnIter_one h
  have h30 := pu_C8 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) (na + 7)) na ch
  have hlkSp : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) (.base ⟨na + 1⟩)
      = some (slC (sHv b i c)) := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdead (na + 1) (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self]
  have h31 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) (na + 7))
      (.evalE (.var "s") (stPuFrEnvC1 na)
        (.stmtOpK (.appendSlice tU64) 1 [.addr (.base ⟨na + 6⟩)]
          [.var "$c0"] (stPuFrEnvC1 na)
          (.seq [pushB3] (stPuFrEnvC1 na) (stPuFrameK na)))) ch
      = .ok (.retV (sHv b i c)
          (.stmtOpK (.appendSlice tU64) 1 [.addr (.base ⟨na + 6⟩)]
            [.var "$c0"] (stPuFrEnvC1 na)
            (.seq [pushB3] (stPuFrEnvC1 na) (stPuFrameK na))),
        (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) (na + 7)), ch) :=
    stepFnIter_one (stepFn_var (c := slC (sHv b i c)) rfl hlkSp)
  have h32 := pu_C9 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) (na + 7)) na (sHv b i c) ch
  have hlkC0h7 : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) (.base ⟨na + 4⟩)
      = some (slC (sHv (na + 5) 1 1)) := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdead (na + 4) (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self]
  have h33 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) (na + 7))
      (.evalE (.var "$c0") (stPuFrEnvC1 na)
        (.stmtOpK (.appendSlice tU64) 1
          [sHv b i c, .addr (.base ⟨na + 6⟩)] [] (stPuFrEnvC1 na)
          (.seq [pushB3] (stPuFrEnvC1 na) (stPuFrameK na)))) ch
      = .ok (.retV (sHv (na + 5) 1 1)
          (.stmtOpK (.appendSlice tU64) 1
            [sHv b i c, .addr (.base ⟨na + 6⟩)] [] (stPuFrEnvC1 na)
            (.seq [pushB3] (stPuFrEnvC1 na) (stPuFrameK na))),
        (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) (na + 7)), ch) :=
    stepFnIter_one (stepFn_var (c := slC (sHv (na + 5) 1 1)) rfl hlkC0h7)
  have hPre := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hB h12) h13) h14) h15) h16) h17) h18) h19) h20)
    h21) h22) h23) h24) h25) h26) h27) h28) h29) h30) h31) h32) h33
  -- ## the append: in place (`i < c`) or spill (`c = i`)
  rcases Nat.eq_or_lt_of_le hic with hceq | hclt
  case inr =>
    -- IN PLACE: no choice consumed, backing updated at `b`, cap kept
    have hbi' : 12 ≤ b ∧ b < na
        ∧ Heap.lookup T (.base ⟨b⟩)
            = some (backC c (stFam i seed ++ List.replicate (c - i) 0)) := by
      rcases hbi with ⟨-, rfl⟩ | h
      · omega
      · exact h
    obtain ⟨hb12', hbna', hlkTb⟩ := hbi'
    have hbneq : ∀ x : Nat, b ≠ x → (Loc.base ⟨b⟩ : Loc) ≠ .base ⟨x⟩ := by
      intro x hx hq
      simp at hq
      omega
    have happly : applyStmtOp (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) (na + 7)) ch
        (.appendSlice tU64) 1
        [.addr (.base ⟨na + 6⟩), .slice ⟨some (.base ⟨b⟩), 0, i, c⟩,
         .slice ⟨some (.base ⟨na + 5⟩), 0, 1, 1⟩]
        = .ok ((stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int) (Heap.set T (.base ⟨b⟩) (backC c (stFam (i + 1) seed ++ List.replicate (c - (i + 1)) 0)) ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC (sHv b (i + 1) c))])) (na + 7)), ch) := by
      have h := st_append_inplace
        (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) (na + 7))
        b (na + 6) (na + 5) i c
        (stFam i seed ++ List.replicate (c - i) 0) (((seed + i) % 2 ^ 64 : Nat) : Int) nilSl ch
        (by rw [show ((stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) (na + 7))).heap
              = (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) from rfl,
            stF_lookup_tail (by omega), lookup_append_left hlkTb])
        (by show Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) _ = _
            rw [stF_lookup_tail (by omega),
              lookup_append_right (hdead (na + 5) (by omega)),
              lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
              lookup_cons_self])
        (by show Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) _ = _
            rw [stF_lookup_tail (by omega),
              lookup_append_right (hdead (na + 6) (by omega)),
              lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
              lookup_cons_self])
        (hbneq (na + 6) (by omega)) hclt
        (by rw [List.length_append, stFam_length, List.length_replicate]
            omega)
        stFamZ_range hfr
      rw [stFam_set hclt] at h
      rw [show Heap.set ((stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) (na + 7))).heap
            (.base ⟨b⟩)
            (backC c (stFam (i + 1) seed
              ++ List.replicate (c - (i + 1)) 0))
          = (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int) ((Heap.set T (.base ⟨b⟩) (backC c (stFam (i + 1) seed ++ List.replicate (c - (i + 1)) 0))) ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) from by
        show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) _ _ = _
        rw [stF_set_tail (by omega), set_append_left hlkTb]] at h
      rw [show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int) ((Heap.set T (.base ⟨b⟩) (backC c (stFam (i + 1) seed ++ List.replicate (c - (i + 1)) 0))) ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)]))
            (.base ⟨na + 6⟩) (slC (sHv b (i + 1) c))
          = (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int) ((Heap.set T (.base ⟨b⟩) (backC c (stFam (i + 1) seed ++ List.replicate (c - (i + 1)) 0))) ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC (sHv b (i + 1) c))])) from by
        rw [stF_set_tail (by omega),
          set_append_right (by
            rw [Heap.lookup_set_ne (hbneq (na + 6) (by omega))]
            exact hdead (na + 6) (by omega)),
          set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
          set_cons_self]] at h
      exact h
    have hap : stepFnIter 1
        (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) (na + 7))
        (.retV (sHv (na + 5) 1 1)
          (.stmtOpK (.appendSlice tU64) 1
            [sHv b i c, .addr (.base ⟨na + 6⟩)] [] (stPuFrEnvC1 na)
            (.seq [pushB3] (stPuFrEnvC1 na) (stPuFrameK na)))) ch
        = .ok (.next (.seq [pushB3] (stPuFrEnvC1 na) (stPuFrameK na)),
            (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
      (stPre i seed) (i : Int) ((Heap.set T (.base ⟨b⟩) (backC c (stFam (i + 1) seed ++ List.replicate (c - (i + 1)) 0))) ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC (sHv b (i + 1) c))])) (na + 7)), ch) :=
      stepFnIter_one (stepFn_stmtOp_apply
        (done := [sHv b i c, .addr (.base ⟨na + 6⟩)]) (nt := 1)
        (env := stPuFrEnvC1 na)
        (k := .seq [pushB3] (stPuFrEnvC1 na) (stPuFrameK na)) happly)
    have hlkTin : ∀ x : Nat, na ≤ x →
        Heap.lookup (Heap.set T (.base ⟨b⟩) (backC c (stFam (i + 1) seed ++ List.replicate (c - (i + 1)) 0))) (.base ⟨x⟩) = none := by
      intro x hx
      rw [Heap.lookup_set_ne (hbneq x (by omega))]
      exact hdead x hx
    have hpost := pu_post σ n seed k i b c b c na (na + 7)
      ((Heap.set T (.base ⟨b⟩) (backC c (stFam (i + 1) seed ++ List.replicate (c - (i + 1)) 0))) ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC (sHv b (i + 1) c))])
      ((Heap.set T (.base ⟨b⟩) (backC c (stFam (i + 1) seed ++ List.replicate (c - (i + 1)) 0))) ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC (sHv b (i + 1) c)),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC (sHv b (i + 1) c))])
      ch hin hcap hna12 hfamlt
      (by rw [stF_lookup_tail (by omega),
            lookup_append_right (hlkTin (na + 6) (by omega)),
            lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
            lookup_cons_self])
      (by rw [stF_lookup_tail (by omega),
            lookup_append_right (hlkTin (na + 3) (by omega)),
            lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
            lookup_cons_self])
      (by rw [stF_set_tail (by omega),
            set_append_right (hlkTin (na + 3) (by omega)),
            set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
            set_cons_self])
      (by rw [stF_lookup_tail (by omega),
            lookup_append_right (hlkTin (na + 3) (by omega)),
            lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
            lookup_cons_self])
      (by rw [lookup_append_right (hlkTin na (by omega)),
            lookup_cons_self])
    refine ⟨b, c, na + 7, (Heap.set T (.base ⟨b⟩) (backC c (stFam (i + 1) seed ++ List.replicate (c - (i + 1)) 0))) ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i c)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC (sHv b (i + 1) c)),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC (sHv b (i + 1) c))], ch, ?_, by omega, ?_, by omega, by omega, ?_⟩
    · rw [show (130 : Nat) = 7 + 1 + 10 + 1 + 1 + 1 + 1 + 1 + 4 + 1 + 1 + 2 + 1 + 1 + 1 + 7 + 1 + 2 + 1 + 3 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 4 + 1 + 1 + 1 + 1 + 65 from rfl]
      exact stepFnIter_chain (stepFnIter_chain hPre hap) hpost
    · refine Or.inr ⟨hb12', by omega, ?_⟩
      rw [lookup_append_left (GoLean.Iris.heap_lookup_set_base_self T ⟨b⟩ _)]
    · intro x hx
      rw [lookup_append_right (hlkTin x (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega))]
      rfl
  case inl =>
    -- SPILL: `c = i`, one choice consumed, fresh backing at `na + 7`
    subst hceq
    rcases hcs : Choices.consume ch (appendSpillWidth i (i + 1))
      with ⟨e, ch2⟩
    have hlkBfull : Heap.lookup
        (stHp (n : Int) (seed : Int) (k : Int) (sHv b i i)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i i)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)]))
        (.base ⟨b⟩) = some (backC i (stFam i seed)) := by
      rcases hbi with ⟨rfl, hc0⟩ | ⟨hb12', hbna', hlkTb⟩
      · rw [show (backC i (stFam i seed)) = arrC 0 [] from by
          rw [show i = 0 from by omega]
          rfl]
        rw [show i = 0 from by omega]
        simp [stHp, stF, Heap.lookup]
      · rw [stF_lookup_tail (by omega), lookup_append_left]
        rw [show stFam i seed ++ List.replicate (i - i) 0
            = stFam i seed from by simp] at hlkTb
        exact hlkTb
    have hlkW7 : ∀ x : Nat, na + 7 ≤ x →
        Heap.lookup (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i i)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)]) (.base ⟨x⟩) = none := by
      intro x hx
      rw [lookup_append_right (hdead x (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega))]
      rfl
    have happly : applyStmtOp (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i i)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i i)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) (na + 7)) ch
        (.appendSlice tU64) 1
        [.addr (.base ⟨na + 6⟩), .slice ⟨some (.base ⟨b⟩), 0, i, i⟩,
         .slice ⟨some (.base ⟨na + 5⟩), 0, 1, 1⟩]
        = .ok ((stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i i)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i i)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC (sHv (na + 7) (i + 1) (stNewCap i e))),
        (.base ⟨na + 7⟩, backC (stNewCap i e) (stFam (i + 1) seed ++ List.replicate (stNewCap i e - (i + 1)) 0))])) (na + 8)), ch2) := by
      have h : applyStmtOp (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i i)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i i)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) (na + 7)) ch
          (.appendSlice tU64) 1
          [.addr (.base ⟨na + 6⟩), .slice ⟨some (.base ⟨b⟩), 0, i, i⟩,
           .slice ⟨some (.base ⟨na + 5⟩), 0, 1, 1⟩]
          = .ok (stStx σ
              (Heap.set (Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b i i)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i i)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) (.base ⟨na + 7⟩)
                  (backC (stNewCap i e)
                    ((stFam i seed ++ [(((seed + i) % 2 ^ 64 : Nat) : Int)])
                      ++ List.replicate ((stNewCap i e) - (i + 1)) 0)))
                (.base ⟨na + 6⟩) (slC (sHv (na + 7) (i + 1) (stNewCap i e))))
              (na + 8), ch2) :=
by
        refine st_append_spill _ b (na + 6) (na + 5) i (stFam i seed) _
          nilSl ch ch2 e hlkBfull ?_ ?_ ?_ hcs (stFam_length i seed)
          (stFam_range i seed) hfr
        · show Heap.lookup (stHp (n : Int) (seed : Int) (k : Int)
            (sHv b i i) (stPre i seed) (i : Int)
            (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
              (.base ⟨na + 1⟩, slC (sHv b i i)),
              (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
              (.base ⟨na + 3⟩, slC nilSl),
              (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
              (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
              (.base ⟨na + 6⟩, slC nilSl)])) (.base ⟨na + 5⟩)
            = some (arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)])
          rw [stF_lookup_tail (by omega),
            lookup_append_right (hdead (na + 5) (by omega)),
            lookup_cons_ne (base_beq_false (by omega)),
            lookup_cons_ne (base_beq_false (by omega)),
            lookup_cons_ne (base_beq_false (by omega)),
            lookup_cons_ne (base_beq_false (by omega)),
            lookup_cons_ne (base_beq_false (by omega)),
            lookup_cons_self]
        · show Heap.lookup (stHp (n : Int) (seed : Int) (k : Int)
            (sHv b i i) (stPre i seed) (i : Int)
            (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
              (.base ⟨na + 1⟩, slC (sHv b i i)),
              (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
              (.base ⟨na + 3⟩, slC nilSl),
              (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
              (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
              (.base ⟨na + 6⟩, slC nilSl)])) (.base ⟨na + 6⟩)
            = some ⟨some sliceU, nilSl⟩
          rw [stF_lookup_tail (by omega),
            lookup_append_right (hdead (na + 6) (by omega)),
            lookup_cons_ne (base_beq_false (by omega)),
            lookup_cons_ne (base_beq_false (by omega)),
            lookup_cons_ne (base_beq_false (by omega)),
            lookup_cons_ne (base_beq_false (by omega)),
            lookup_cons_ne (base_beq_false (by omega)),
            lookup_cons_ne (base_beq_false (by omega)),
            lookup_cons_self]
        · show (Loc.base ⟨na + 7⟩ : Loc) ≠ .base ⟨na + 6⟩
          intro hq
          injection hq with h1
          injection h1 with h2
          omega
      rw [show (stFam i seed ++ [(((seed + i) % 2 ^ 64 : Nat) : Int)])
          = stFam (i + 1) seed from (stFam_succ i seed).symm] at h
      rw [show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b i i)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i i)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)]))
            (.base ⟨na + 7⟩) (backC (stNewCap i e) (stFam (i + 1) seed ++ List.replicate (stNewCap i e - (i + 1)) 0))
          = (stHp (n : Int) (seed : Int) (k : Int) (sHv b i i)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i i)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl),
        (.base ⟨na + 7⟩, backC (stNewCap i e) (stFam (i + 1) seed ++ List.replicate (stNewCap i e - (i + 1)) 0))])) from by
        show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b i i)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i i)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) _ _ = _
        rw [stHp_alloc (by omega) (hlkW7 (na + 7) (by omega)),
          show (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i i)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)]) ++ [(.base ⟨na + 7⟩, backC (stNewCap i e) (stFam (i + 1) seed ++ List.replicate (stNewCap i e - (i + 1)) 0))] = T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i i)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl),
        (.base ⟨na + 7⟩, backC (stNewCap i e) (stFam (i + 1) seed ++ List.replicate (stNewCap i e - (i + 1)) 0))] from by simp]] at h
      rw [show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b i i)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i i)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl),
        (.base ⟨na + 7⟩, backC (stNewCap i e) (stFam (i + 1) seed ++ List.replicate (stNewCap i e - (i + 1)) 0))]))
            (.base ⟨na + 6⟩) (slC (sHv (na + 7) (i + 1) (stNewCap i e)))
          = (stHp (n : Int) (seed : Int) (k : Int) (sHv b i i)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i i)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC (sHv (na + 7) (i + 1) (stNewCap i e))),
        (.base ⟨na + 7⟩, backC (stNewCap i e) (stFam (i + 1) seed ++ List.replicate (stNewCap i e - (i + 1)) 0))])) from by
        rw [stF_set_tail (by omega),
          set_append_right (hdead (na + 6) (by omega)),
          set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
          set_cons_self]] at h
      exact h
    have hap : stepFnIter 1
        (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i i)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i i)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC nilSl)])) (na + 7))
        (.retV (sHv (na + 5) 1 1)
          (.stmtOpK (.appendSlice tU64) 1
            [sHv b i i, .addr (.base ⟨na + 6⟩)] [] (stPuFrEnvC1 na)
            (.seq [pushB3] (stPuFrEnvC1 na) (stPuFrameK na)))) ch
        = .ok (.next (.seq [pushB3] (stPuFrEnvC1 na) (stPuFrameK na)),
            (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i i)
      (stPre i seed) (i : Int) (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i i)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC (sHv (na + 7) (i + 1) (stNewCap i e))),
        (.base ⟨na + 7⟩, backC (stNewCap i e) (stFam (i + 1) seed ++ List.replicate (stNewCap i e - (i + 1)) 0))])) (na + 8)), ch2) :=
      stepFnIter_one (stepFn_stmtOp_apply
        (done := [sHv b i i, .addr (.base ⟨na + 6⟩)]) (nt := 1)
        (env := stPuFrEnvC1 na)
        (k := .seq [pushB3] (stPuFrEnvC1 na) (stPuFrameK na)) happly)
    have hpost := pu_post σ n seed k i b i (na + 7) (stNewCap i e) na (na + 8)
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i i)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC nilSl),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC (sHv (na + 7) (i + 1) (stNewCap i e))),
        (.base ⟨na + 7⟩, backC (stNewCap i e) (stFam (i + 1) seed ++ List.replicate (stNewCap i e - (i + 1)) 0))])
      (T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i i)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC (sHv (na + 7) (i + 1) (stNewCap i e))),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC (sHv (na + 7) (i + 1) (stNewCap i e))),
        (.base ⟨na + 7⟩, backC (stNewCap i e) (stFam (i + 1) seed ++ List.replicate (stNewCap i e - (i + 1)) 0))])
      ch2 hin hcap hna12 hfamlt
      (by rw [stF_lookup_tail (by omega),
            lookup_append_right (hdead (na + 6) (by omega)),
            lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
            lookup_cons_self])
      (by rw [stF_lookup_tail (by omega),
            lookup_append_right (hdead (na + 3) (by omega)),
            lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
            lookup_cons_self])
      (by rw [stF_set_tail (by omega),
            set_append_right (hdead (na + 3) (by omega)),
            set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
            set_cons_self])
      (by rw [stF_lookup_tail (by omega),
            lookup_append_right (hdead (na + 3) (by omega)),
            lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
            lookup_cons_self])
      (by rw [lookup_append_right (hdead na (by omega)),
            lookup_cons_self])
    refine ⟨na + 7, stNewCap i e, na + 8, T ++ [(.base ⟨na⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slC (sHv b i i)),
        (.base ⟨na + 2⟩, u64c (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slC (sHv (na + 7) (i + 1) (stNewCap i e))),
        (.base ⟨na + 4⟩, slC (sHv (na + 5) 1 1)),
        (.base ⟨na + 5⟩, arrC 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slC (sHv (na + 7) (i + 1) (stNewCap i e))),
        (.base ⟨na + 7⟩, backC (stNewCap i e) (stFam (i + 1) seed ++ List.replicate (stNewCap i e - (i + 1)) 0))], ch2, ?_,
      stNewCap_ge i e, ?_, by omega, by omega, ?_⟩
    · rw [show (130 : Nat) = 7 + 1 + 10 + 1 + 1 + 1 + 1 + 1 + 4 + 1 + 1 + 2 + 1 + 1 + 1 + 7 + 1 + 2 + 1 + 3 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 4 + 1 + 1 + 1 + 1 + 65 from rfl]
      exact stepFnIter_chain (stepFnIter_chain hPre hap) hpost
    · refine Or.inr ⟨by omega, by omega, ?_⟩
      rw [lookup_append_right (hdead (na + 7) (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_self]
    · intro x hx
      rw [lookup_append_right (hdead x (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega))]
      rfl

/-- **The push loop**: exactly `130·(n−i)` steps from any invariant
checkpoint to the exit checkpoint, by strong induction with the
existentially packaged backing invariant (`stepFnIter_iterate` does NOT
apply — the state family is not a function of `i` alone; the backing
address, capacity, allocation front and choice stream all vary with
the consumed choices). -/
theorem pu_loop (σ : ExecState) (n seed k : Nat)
    (henterP : ∀ (H : Heap) (a : Nat) (sh : GoValue) (w : Int),
      enterFrame (stStx σ H a) ⟨"push"⟩ [sh, .int w .uint64]
        = .ok (pushFunc,
            [[("$res0", .base ⟨a + 2⟩), ("v", .base ⟨a + 1⟩),
              ("s", .base ⟨a⟩)]],
            [.base ⟨a + 2⟩],
            stStx σ
              (Heap.set (Heap.set (Heap.set H (.base ⟨a⟩) (slC sh))
                  (.base ⟨a + 1⟩) (u64c (IntKind.normalize .uint64 w)))
                (.base ⟨a + 2⟩) (slC nilSl))
              (a + 3)))
    (hcap : n ≤ 8) :
    ∀ (d i b c na : Nat) (T : Heap) (ch : Choices), d = n - i → i ≤ n →
      i ≤ c → PuInv T b c i seed na → 12 ≤ na → DeadFrom T na →
      ∃ (b' c' na' : Nat) (T' : Heap) (ch' : Choices),
        stepFnIter (130 * (n - i))
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b i c)
            (stPre i seed) (i : Int) T) na)
          (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
            stPuCmpK) ch
        = .ok (.retV (.bool (decide (((n : Nat) : Int)
              < ((n : Nat) : Int)))) stPuCmpK,
            stStx σ (stHp (n : Int) (seed : Int) (k : Int)
              (sHv b' n c') (stPre n seed) ((n : Nat) : Int) T') na',
            ch')
        ∧ n ≤ c' ∧ PuInv T' b' c' n seed na' ∧ 12 ≤ na'
        ∧ DeadFrom T' na' := by
  intro d
  induction d with
  | zero =>
      intro i b c na T ch hd hin hic hbi hna12 hdead
      have hieq : i = n := by omega
      subst hieq
      exact ⟨b, c, na, T, ch, by rw [Nat.sub_self, Nat.mul_zero]; rfl,
        hic, hbi, hna12, hdead⟩
  | succ d ih =>
      intro i b c na T ch hd hin hic hbi hna12 hdead
      have hlt : i < n := by omega
      obtain ⟨b1, c1, na1, T1, ch1, hstep, hc1, hbi1, hna1le, hna1, hdead1⟩ :=
        pu_iter σ n seed k i b c na T ch henterP hlt hcap hic hbi hna12
          hdead
      obtain ⟨b', c', na', T', ch', hrest, hc', hbi', hna', hdead'⟩ :=
        ih (i + 1) b1 c1 na1 T1 ch1 (by omega) (by omega) hc1 hbi1 hna1
          hdead1
      refine ⟨b', c', na', T', ch', ?_, hc', hbi', hna', hdead'⟩
      have hcast : (decide (((i : Nat) : Int) < ((n : Nat) : Int)))
          = true := decide_eq_true (by exact_mod_cast hlt)
      rw [hcast] at *
      have hchain := stepFnIter_chain hstep hrest
      rw [show 130 + 130 * (n - (i + 1)) = 130 * (n - i) from by
        rw [show n - i = (n - (i + 1)) + 1 from by omega, Nat.mul_succ]
        omega] at hchain
      rw [hcast]
      exact hchain

/-! ## Entry: post-prelude seed → the first push checkpoint (84 steps,
all at concrete addresses 6–11). -/

theorem st_entry (σ : ExecState) (nv sv kv : Int) (ch : Choices) :
    stepFnIter 84 (stStx σ
      [(.base ⟨0⟩, u64c nv), (.base ⟨1⟩, u64c sv), (.base ⟨2⟩, u64c kv),
       (.base ⟨3⟩, arrC 8 zeros8), (.base ⟨4⟩, arrC 8 zeros8),
       (.base ⟨5⟩, u64c 0)] 6)
      (.exec stackHarnessRFunc.body [stBase] stStop) ch
      = .ok (.retV (.bool (decide ((0 : Int) < nv))) stPuCmpK,
          stStx σ (stHp nv sv kv (sHv 7 0 0) zeros8 0 ([] : Heap)) 12,
          ch) := by
  with_unfolding_all rfl

/-! ## The min phase: push exit → the first pop checkpoint

`m := k; if n < m { m = n }` — the branch on `n < k` is taken exactly
when `k > n` (the drain-everything rows), costing 12 extra steps; then
`popped`/`j`/`$forFirst` allocate the pop block at the symbolic base
`q` (= the push phase's final allocation front). -/

/-- MnA: exit test false → the `m` declaration. 9 steps (concrete
envs). -/
theorem mn_A (σ : ExecState) (ch : Choices) :
    stepFnIter 9 σ (.retV (.bool false) stPuCmpK) ch
      = .ok (.exec (.initialization { id := "m", typ := tU64 })
          [stTop, stBase]
          (.seq [.assign (.var "m") (.var "k"), stS6, stS7, stS8, stS9,
            stS10] [stTop, stBase] stStop), σ, ch) := by
  with_unfolding_all rfl

/-- MnB: `m` declared → the `m := k` store point. 6 steps. -/
theorem mn_B (σ : ExecState) (nv sv kv : Int) (sh : GoValue)
    (pl : List Int) (iv : Int) (T : Heap) (q na' : Nat) (ch : Choices) :
    stepFnIter 6 (stStx σ (stHp nv sv kv sh pl iv T) na')
      (.next (.seq [.assign (.var "m") (.var "k"), stS6, stS7, stS8,
        stS9, stS10] [("m", .base ⟨q⟩) :: stTop, stBase] stStop)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨q⟩)) [] []]
            [.int kv .uint64] (.seqn #[])
            ([("m", .base ⟨q⟩) :: stTop, stBase])
            (.seq [stS6, stS7, stS8, stS9, stS10]
              ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)),
          stStx σ (stHp nv sv kv sh pl iv T) na', ch) := by
  with_unfolding_all rfl

/-- MnC0: the `m` store drained (1 raw step; splice follows). -/
theorem mn_C0 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) ([("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS6, stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop))) ch
      = .ok (.exec (.seqn #[]) ([("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS6, stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop), σ, ch) := by
  with_unfolding_all rfl

/-- MnC1: to the `n < m` test's `m` read. 5 steps. -/
theorem mn_C1 (σ : ExecState) (nv sv kv : Int) (sh : GoValue)
    (pl : List Int) (iv : Int) (T : Heap) (q na' : Nat) (ch : Choices) :
    stepFnIter 5 (stStx σ (stHp nv sv kv sh pl iv T) na')
      (.next (.seq [stS6, stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)) ch
      = .ok (.evalE (.var "m") ([("m", .base ⟨q⟩) :: stTop, stBase])
          (.strictK .lessCmp [.int nv .uint64] [] ([("m", .base ⟨q⟩) :: stTop, stBase]) (.ifK (.block #[] #[.seqn #[.assign (.var "m") (.var "n")]])
          (.seqn #[]) ([("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop))),
        stStx σ (stHp nv sv kv sh pl iv T) na', ch) := by
  with_unfolding_all rfl

/-- MnC2: the `m` value delivered → the branch decision. 1 step. -/
theorem mn_C2 (σ : ExecState) (nv mv : Int) (q : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.retV (.int mv .uint64)
        (.strictK .lessCmp [.int nv .uint64] [] ([("m", .base ⟨q⟩) :: stTop, stBase]) (.ifK (.block #[] #[.seqn #[.assign (.var "m") (.var "n")]])
          (.seqn #[]) ([("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)))) ch
      = .ok (.retV (.bool (decide (nv < mv))) (.ifK (.block #[] #[.seqn #[.assign (.var "m") (.var "n")]])
          (.seqn #[]) ([("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)), σ, ch) := by
  with_unfolding_all rfl

/-- MnD0 (branch taken): into the `m = n` assign's seqn. 2 steps. -/
theorem mn_D0 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 2 σ (.retV (.bool true) (.ifK (.block #[] #[.seqn #[.assign (.var "m") (.var "n")]])
          (.seqn #[]) ([("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop))) ch
      = .ok (.next (.seq [.seqn #[.assign (.var "m") (.var "n")]]
          ([] :: [("m", .base ⟨q⟩) :: stTop, stBase])
          (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)), σ, ch) := by
  with_unfolding_all rfl

theorem mn_D1 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.seq [.seqn #[.assign (.var "m") (.var "n")]]
        ([] :: [("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop))) ch
      = .ok (.exec (.seqn #[.assign (.var "m") (.var "n")])
          ([] :: [("m", .base ⟨q⟩) :: stTop, stBase])
          (.seq [] ([] :: [("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)),
        σ, ch) := by
  with_unfolding_all rfl

/-- MnD2: the `m = n` store point. 6 steps. -/
theorem mn_D2 (σ : ExecState) (nv sv kv : Int) (sh : GoValue)
    (pl : List Int) (iv : Int) (T : Heap) (q na' : Nat) (ch : Choices) :
    stepFnIter 6 (stStx σ (stHp nv sv kv sh pl iv T) na')
      (.next (.seq [.assign (.var "m") (.var "n")]
        ([] :: [("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨q⟩)) [] []]
            [.int nv .uint64] (.seqn #[])
            ([] :: [("m", .base ⟨q⟩) :: stTop, stBase])
            (.seq [] ([] :: [("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop))),
          stStx σ (stHp nv sv kv sh pl iv T) na', ch) := by
  with_unfolding_all rfl

theorem mn_D3 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[])
        ([] :: [("m", .base ⟨q⟩) :: stTop, stBase])
        (.seq [] ([] :: [("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)))) ch
      = .ok (.exec (.seqn #[])
          ([] :: [("m", .base ⟨q⟩) :: stTop, stBase])
          (.seq [] ([] :: [("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)),
        σ, ch) := by
  with_unfolding_all rfl

theorem mn_D4 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 2 σ
      (.next (.seq [] ([] :: [("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)))
      ch
      = .ok (.exec stS7 ([("m", .base ⟨q⟩) :: stTop, stBase])
          (.seq [stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop), σ, ch) := by
  with_unfolding_all rfl

/-- MnE (branch not taken): 1 raw step to the merge seqn (splice
follows). -/
theorem mn_E0 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 1 σ (.retV (.bool false) (.ifK (.block #[] #[.seqn #[.assign (.var "m") (.var "n")]])
          (.seqn #[]) ([("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop))) ch
      = .ok (.exec (.seqn #[]) ([("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop), σ, ch) := by
  with_unfolding_all rfl

theorem mn_E1 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 1 σ (.next (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)) ch
      = .ok (.exec stS7 ([("m", .base ⟨q⟩) :: stTop, stBase])
          (.seq [stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop), σ, ch) := by
  with_unfolding_all rfl

/-! ### The pop-block setup (`popped`/`j`/`$forFirst`, 55 steps from
`stS7`'s head to the first pop checkpoint) -/

/-- G0: `stS7`'s splice result → the `j` seqn. 4 steps. -/
theorem mn_G0 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 3 σ
      (.next (.seq [stS8, stS9, stS10] ([stTopP q, stBase]) stStop)) ch
      = .ok (.exec (.seqn #[.initialization { id := "j", typ := tU64 },
            .assign (.var "j") (.intLit 0 .uint64)]) ([] :: [stTopP q, stBase])
          (.seq [.block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) stPopBody]] ([] :: [stTopP q, stBase])
            (.seq [stS9, stS10] ([stTopP q, stBase]) stStop)), σ, ch) := by
  with_unfolding_all rfl

/-- G1: post-splice → the `j` declaration. 1 step. -/
theorem mn_G1 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.seq [.initialization { id := "j", typ := tU64 },
        .assign (.var "j") (.intLit 0 .uint64),
        .block #[]
          #[.initialization { id := "$forFirst", typ := .bool },
            .assign (.var "$forFirst") (.boolLit true),
            .while (.boolLit true) stPopBody]] ([] :: [stTopP q, stBase])
        (.seq [stS9, stS10] ([stTopP q, stBase]) stStop))) ch
      = .ok (.exec (.initialization { id := "j", typ := tU64 }) ([] :: [stTopP q, stBase])
          (.seq [.assign (.var "j") (.intLit 0 .uint64),
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) stPopBody]] ([] :: [stTopP q, stBase])
            (.seq [stS9, stS10] ([stTopP q, stBase]) stStop)), σ, ch) := by
  with_unfolding_all rfl

/-- G2: `j` declared → the `j := 0` store point. 6 steps. -/
theorem mn_G2 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 6 σ
      (.next (.seq [.assign (.var "j") (.intLit 0 .uint64),
        .block #[]
          #[.initialization { id := "$forFirst", typ := .bool },
            .assign (.var "$forFirst") (.boolLit true),
            .while (.boolLit true) stPopBody]] ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
        (.seq [stS9, stS10] ([stTopP q, stBase]) stStop))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨q + 2⟩)) [] []]
            [.int 0 .uint64] (.seqn #[]) ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
            (.seq [.block #[]
                #[.initialization { id := "$forFirst", typ := .bool },
                  .assign (.var "$forFirst") (.boolLit true),
                  .while (.boolLit true) stPopBody]] ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
              (.seq [stS9, stS10] ([stTopP q, stBase]) stStop))), σ, ch) := by
  with_unfolding_all rfl

/-- G3: the `j` store drained. 1 step. -/
theorem mn_G3 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
        (.seq [.block #[]
            #[.initialization { id := "$forFirst", typ := .bool },
              .assign (.var "$forFirst") (.boolLit true),
              .while (.boolLit true) stPopBody]] ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
          (.seq [stS9, stS10] ([stTopP q, stBase]) stStop)))) ch
      = .ok (.exec (.seqn #[]) ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
          (.seq [.block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) stPopBody]] ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
            (.seq [stS9, stS10] ([stTopP q, stBase]) stStop)), σ, ch) := by
  with_unfolding_all rfl

/-- G4: post-splice → the `$forFirst` declaration. 3 steps. -/
theorem mn_G4 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 3 σ
      (.next (.seq [.block #[]
          #[.initialization { id := "$forFirst", typ := .bool },
            .assign (.var "$forFirst") (.boolLit true),
            .while (.boolLit true) stPopBody]] ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
        (.seq [stS9, stS10] ([stTopP q, stBase]) stStop))) ch
      = .ok (.exec (.initialization { id := "$forFirst", typ := .bool })
          ([] :: [[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
          (.seq [.assign (.var "$forFirst") (.boolLit true),
            .while (.boolLit true) stPopBody] ([] :: [[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
            (.seq [] ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase]) (.seq [stS9, stS10] ([stTopP q, stBase]) stStop))), σ,
        ch) := by
  with_unfolding_all rfl

/-- G5: `$forFirst` declared → its `:= true` store point. 5 steps. -/
theorem mn_G5 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 6 σ
      (.next (.seq [.assign (.var "$forFirst") (.boolLit true),
        .while (.boolLit true) stPopBody] (stPoEnv q)
        (.seq [] ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase]) (.seq [stS9, stS10] ([stTopP q, stBase]) stStop)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨q + 3⟩)) [] []]
            [.bool true] (.seqn #[]) (stPoEnv q)
            (.seq [.while (.boolLit true) stPopBody] (stPoEnv q)
              (.seq [] ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase]) (.seq [stS9, stS10] ([stTopP q, stBase]) stStop)))),
          σ, ch) := by
  with_unfolding_all rfl

/-- G6: the flag store drained. 1 step. -/
theorem mn_G6 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (stPoEnv q)
        (.seq [.while (.boolLit true) stPopBody] (stPoEnv q)
          (.seq [] ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase]) (.seq [stS9, stS10] ([stTopP q, stBase]) stStop))))) ch
      = .ok (.exec (.seqn #[]) (stPoEnv q)
          (.seq [.while (.boolLit true) stPopBody] (stPoEnv q)
            (.seq [] ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase]) (.seq [stS9, stS10] ([stTopP q, stBase]) stStop))), σ,
        ch) := by
  with_unfolding_all rfl

/-- G7: pop the while, dispatch it, into the first-iteration flag
read. 7 steps. -/
theorem mn_G7 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 7 σ
      (.next (.seq [.while (.boolLit true) stPopBody] (stPoEnv q)
        (.seq [] ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase]) (.seq [stS9, stS10] ([stTopP q, stBase]) stStop)))) ch
      = .ok (.evalE (.var "$forFirst") (stPoEnv1 q)
          (.ifK (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "j")
              (.add (.var "j") (.intLit 1 .uint64)))
            (stPoEnv1 q)
            (.seq [.seqn #[], .ifThenElse
                (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
              stPFillBlock] (stPoEnv1 q) (stPoLoopK q))), σ, ch) := by
  with_unfolding_all rfl

/-- G8: flag true → its `:= false` store point. 6 steps. -/
theorem mn_G8 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 6 σ
      (.retV (.bool true)
        (.ifK (.assign (.var "$forFirst") (.boolLit false))
          (.assign (.var "j") (.add (.var "j") (.intLit 1 .uint64)))
          (stPoEnv1 q)
          (.seq [.seqn #[], .ifThenElse
              (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
            stPFillBlock] (stPoEnv1 q) (stPoLoopK q)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨q + 3⟩)) [] []]
            [.bool false] (.seqn #[]) (stPoEnv1 q)
            (.seq [.seqn #[], .ifThenElse
                (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
              stPFillBlock] (stPoEnv1 q) (stPoLoopK q))), σ, ch) := by
  with_unfolding_all rfl

/-- G9: the flag store drained. 1 step. -/
theorem mn_G9 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (stPoEnv1 q)
        (.seq [.seqn #[], .ifThenElse
            (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
          stPFillBlock] (stPoEnv1 q) (stPoLoopK q)))) ch
      = .ok (.exec (.seqn #[]) (stPoEnv1 q)
          (.seq [.seqn #[], .ifThenElse
              (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
            stPFillBlock] (stPoEnv1 q) (stPoLoopK q)), σ, ch) := by
  with_unfolding_all rfl

/-- G10: pop the body's inner empty seqn. 1 step. -/
theorem mn_G10 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.seq [.seqn #[], .ifThenElse
          (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
        stPFillBlock] (stPoEnv1 q) (stPoLoopK q))) ch
      = .ok (.exec (.seqn #[]) (stPoEnv1 q)
          (.seq [.ifThenElse (.lessCmp (.var "j") (.var "m"))
              (.seqn #[]) .breakStmt, stPFillBlock] (stPoEnv1 q)
            (stPoLoopK q)), σ, ch) := by
  with_unfolding_all rfl

/-- G11: to the test's `j` read. 3 steps. -/
theorem mn_G11 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 3 σ
      (.next (.seq [.ifThenElse (.lessCmp (.var "j") (.var "m"))
          (.seqn #[]) .breakStmt, stPFillBlock] (stPoEnv1 q)
        (stPoLoopK q))) ch
      = .ok (.evalE (.var "j") (stPoEnv1 q)
          (.strictK .lessCmp [] [.var "m"] (stPoEnv1 q)
            (stPoCmpK q)), σ, ch) := by
  with_unfolding_all rfl

/-- G12: the `j` value delivered → the `m` read. 1 step. -/
theorem mn_G12 (σ : ExecState) (q : Nat) (jv : Int) (ch : Choices) :
    stepFnIter 1 σ
      (.retV (.int jv .uint64)
        (.strictK .lessCmp [] [.var "m"] (stPoEnv1 q) (stPoCmpK q))) ch
      = .ok (.evalE (.var "m") (stPoEnv1 q)
          (.strictK .lessCmp [.int jv .uint64] [] (stPoEnv1 q)
            (stPoCmpK q)), σ, ch) := by
  with_unfolding_all rfl

/-- G13: the `m` value delivered → the checkpoint. 1 step. -/
theorem mn_G13 (σ : ExecState) (q : Nat) (jv mv : Int) (ch : Choices) :
    stepFnIter 1 σ
      (.retV (.int mv .uint64)
        (.strictK .lessCmp [.int jv .uint64] [] (stPoEnv1 q)
          (stPoCmpK q))) ch
      = .ok (.retV (.bool (decide (jv < mv))) (stPoCmpK q), σ, ch) := by
  with_unfolding_all rfl

/-- Bool cells store unchanged (normalizer catch-all). -/
theorem st_norm_bool (σ : ExecState) (v : GoValue) :
    normalizeValueForTy σ .bool v = .ok v := by
  rw [normalizeValueForTy, typeResolutionFuel]
  simp only [normalizeValueForTyFuel]
  rfl

/-- **The min-phase tail** (57 steps): from `stS7`'s head — the `m`
cell already holding its final value `mv` — through the pop block's
allocations to the first pop checkpoint. -/
theorem mn_tail (σ : ExecState) (n seed k : Nat) (b c q : Nat)
    (mv : Int) (T : Heap) (ch : Choices) (hq12 : 12 ≤ q)
    (hdead : DeadFrom T q) :
    stepFnIter 57 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv)])) (q + 1))
      (.exec stS7 ([("m", .base ⟨q⟩) :: stTop, stBase])
        (.seq [stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)) ch
      = .ok (.retV (.bool (decide ((0 : Int) < mv))) (stPoCmpK q),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ stM q mv zeros8 0 false)) (q + 4)), ch) := by
  have hlkTM : ∀ (L : Heap) (x : Nat), q ≤ x →
      Heap.lookup T (.base ⟨x⟩) = none := fun _ x hx => hdead x hx
  -- splice stS7's seqn
  have s1 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv)])) (q + 1))
      (.exec stS7 ([("m", .base ⟨q⟩) :: stTop, stBase])
        (.seq [stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)) ch
      = .ok (.next (.seq
            (#[Stmt.initialization
              { id := "popped", typ := .array 8 tU64 }].toList
              ++ [stS8, stS9, stS10])
            ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv)])) (q + 1)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have s2 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv)])) (q + 1))
      (.next (.seq [.initialization
        { id := "popped", typ := .array 8 tU64 }, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)) ch
      = .ok (.exec (.initialization
            { id := "popped", typ := .array 8 tU64 })
          ([("m", .base ⟨q⟩) :: stTop, stBase])
          (.seq [stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv)])) (q + 1)), ch) :=
    stepFnIter_one (stepFn_seq_pop)
  have s3 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv)])) (q + 1))
      (.exec (.initialization { id := "popped", typ := .array 8 tU64 })
        ([("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)) ch
      = .ok (.next (.seq [stS8, stS9, stS10] ([stTopP q, stBase])
            stStop),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8)])) (q + 2)), ch) := by
    have h := stepFn_init_seq (σ := (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv)])) (q + 1)))
      (p := { id := "popped", typ := .array 8 tU64 })
      (rest := [stS8, stS9, stS10]) (env := ([("m", .base ⟨q⟩) :: stTop, stBase])) (k := stStop)
      (ch := ch) (v := .array ⟨zeros8.map (fun v => .int v .uint64)⟩)
      (by with_unfolding_all rfl)
    dsimp only at h
    rw [show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv)])) (.base ⟨q + 1⟩)
        ⟨some (.array 8 tU64), .array ⟨zeros8.map (fun v => .int v .uint64)⟩⟩
        = (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8)])) from by
      rw [stF_set_tail (by omega),
        set_append_right (hdead (q + 1) (by omega)),
        set_cons_ne (base_beq_false (by omega))]
      rfl] at h
    exact stepFnIter_one h
  have s4 := mn_G0 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8)])) (q + 2)) q ch
  have s5 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8)])) (q + 2))
      (.exec (.seqn #[.initialization { id := "j", typ := tU64 },
        .assign (.var "j") (.intLit 0 .uint64)])
        ([] :: [stTopP q, stBase])
        (.seq [.block #[]
            #[.initialization { id := "$forFirst", typ := .bool },
              .assign (.var "$forFirst") (.boolLit true),
              .while (.boolLit true) stPopBody]]
          ([] :: [stTopP q, stBase])
          (.seq [stS9, stS10] ([stTopP q, stBase]) stStop))) ch
      = .ok (.next (.seq
            (#[Stmt.initialization { id := "j", typ := tU64 },
              Stmt.assign (.var "j") (.intLit 0 .uint64)].toList
            ++ [.block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) stPopBody]])
            ([] :: [stTopP q, stBase])
            (.seq [stS9, stS10] ([stTopP q, stBase]) stStop)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8)])) (q + 2)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have s6 := mn_G1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8)])) (q + 2)) q ch
  have s7 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8)])) (q + 2))
      (.exec (.initialization { id := "j", typ := tU64 })
        ([] :: [stTopP q, stBase])
        (.seq [.assign (.var "j") (.intLit 0 .uint64),
          .block #[]
            #[.initialization { id := "$forFirst", typ := .bool },
              .assign (.var "$forFirst") (.boolLit true),
              .while (.boolLit true) stPopBody]]
          ([] :: [stTopP q, stBase])
          (.seq [stS9, stS10] ([stTopP q, stBase]) stStop))) ch
      = .ok (.next (.seq [.assign (.var "j") (.intLit 0 .uint64),
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) stPopBody]]
            ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
            (.seq [stS9, stS10] ([stTopP q, stBase]) stStop)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0)])) (q + 3)), ch) := by
    have h := stepFn_init_seq (σ := (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8)])) (q + 2)))
      (p := { id := "j", typ := tU64 })
      (rest := [.assign (.var "j") (.intLit 0 .uint64),
        .block #[]
          #[.initialization { id := "$forFirst", typ := .bool },
            .assign (.var "$forFirst") (.boolLit true),
            .while (.boolLit true) stPopBody]])
      (env := [] :: [stTopP q, stBase])
      (k := .seq [stS9, stS10] ([stTopP q, stBase]) stStop) (ch := ch)
      (v := .int 0 .uint64)
      (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
    dsimp only at h
    rw [show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8)])) (.base ⟨q + 2⟩)
        ⟨some tU64, .int 0 .uint64⟩
        = (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0)])) from by
      rw [stF_set_tail (by omega),
        set_append_right (hdead (q + 2) (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega))]
      rfl] at h
    exact stepFnIter_one h
  have s8 := mn_G2 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0)])) (q + 3)) q ch
  have s9 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0)])) (q + 3))
      (.next (.storeK [.chain (.addr (.base ⟨q + 2⟩)) [] []]
        [.int 0 .uint64] (.seqn #[])
        ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
        (.seq [.block #[]
            #[.initialization { id := "$forFirst", typ := .bool },
              .assign (.var "$forFirst") (.boolLit true),
              .while (.boolLit true) stPopBody]]
          ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
          (.seq [stS9, stS10] ([stTopP q, stBase]) stStop)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[])
            ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
            (.seq [.block #[]
                #[.initialization { id := "$forFirst", typ := .bool },
                  .assign (.var "$forFirst") (.boolLit true),
                  .while (.boolLit true) stPopBody]]
              ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
              (.seq [stS9, stS10] ([stTopP q, stBase]) stStop))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0)])) (q + 3)), ch) := by
    have hlk : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0)])) (.base ⟨q + 2⟩)
        = some (u64c 0) := by
      rw [stF_lookup_tail (by omega),
        lookup_append_right (hdead (q + 2) (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_self]
    have hst : storeTarget (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0)])) (q + 3))
        (.chain (.addr (.base ⟨q + 2⟩)) [] []) (.int 0 .uint64)
        = .ok (stStx σ (Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0)])) (.base ⟨q + 2⟩)
            (u64c (IntKind.normalize .uint64 0))) (q + 3)) :=
      storeTarget_addr hlk (st_norm_u64 _ 0)
    rw [show IntKind.normalize .uint64 (0 : Int) = (0 : Int) from rfl]
      at hst
    have h := stepFnIter_one (stepFn_store_step (rs := []) (vs := [])
      (body := .seqn #[])
      (env := [[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
      (k := .seq [.block #[]
          #[.initialization { id := "$forFirst", typ := .bool },
            .assign (.var "$forFirst") (.boolLit true),
            .while (.boolLit true) stPopBody]]
        ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
        (.seq [stS9, stS10] ([stTopP q, stBase]) stStop)) (ch := ch)
      hst)
    rw [show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0)])) (.base ⟨q + 2⟩) (u64c 0)
        = (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0)])) from by
      rw [stF_set_tail (by omega),
        set_append_right (hdead (q + 2) (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_self]] at h
    exact h
  have s10 := mn_G3 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0)])) (q + 3)) q ch
  have s11 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0)])) (q + 3))
      (.exec (.seqn #[]) ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
        (.seq [.block #[]
            #[.initialization { id := "$forFirst", typ := .bool },
              .assign (.var "$forFirst") (.boolLit true),
              .while (.boolLit true) stPopBody]]
          ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
          (.seq [stS9, stS10] ([stTopP q, stBase]) stStop))) ch
      = .ok (.next (.seq (#[].toList ++ [.block #[]
            #[.initialization { id := "$forFirst", typ := .bool },
              .assign (.var "$forFirst") (.boolLit true),
              .while (.boolLit true) stPopBody]])
            ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
            (.seq [stS9, stS10] ([stTopP q, stBase]) stStop)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0)])) (q + 3)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have s12 := mn_G4 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0)])) (q + 3)) q ch
  have s13 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0)])) (q + 3))
      (.exec (.initialization { id := "$forFirst", typ := .bool })
        ([] :: [[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
        (.seq [.assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) stPopBody]
          ([] :: [[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
          (.seq [] ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
            (.seq [stS9, stS10] ([stTopP q, stBase]) stStop)))) ch
      = .ok (.next (.seq [.assign (.var "$forFirst") (.boolLit true),
            .while (.boolLit true) stPopBody] (stPoEnv q)
            (.seq [] ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
              (.seq [stS9, stS10] ([stTopP q, stBase]) stStop))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (q + 4)), ch) := by
    have h := stepFn_init_seq (σ := (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0)])) (q + 3)))
      (p := { id := "$forFirst", typ := .bool })
      (rest := [.assign (.var "$forFirst") (.boolLit true),
        .while (.boolLit true) stPopBody])
      (env := [] :: [[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
      (k := .seq [] ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
        (.seq [stS9, stS10] ([stTopP q, stBase]) stStop)) (ch := ch)
      (v := .bool false)
      (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
    dsimp only at h
    rw [show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0)])) (.base ⟨q + 3⟩)
        ⟨some .bool, .bool false⟩
        = (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) from by
      rw [stF_set_tail (by omega),
        set_append_right (hdead (q + 3) (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega))]
      rfl] at h
    exact stepFnIter_one h
  have s14 := mn_G5 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (q + 4)) q ch
  have s15 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (q + 4))
      (.next (.storeK [.chain (.addr (.base ⟨q + 3⟩)) [] []]
        [.bool true] (.seqn #[]) (stPoEnv q) (.seq [.while (.boolLit true) stPopBody] (stPoEnv q) (.seq [] ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase]) (.seq [stS9, stS10] ([stTopP q, stBase]) stStop))))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (stPoEnv q) (.seq [.while (.boolLit true) stPopBody] (stPoEnv q) (.seq [] ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase]) (.seq [stS9, stS10] ([stTopP q, stBase]) stStop)))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell true)])) (q + 4)), ch) := by
    have hlk : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (.base ⟨q + 3⟩)
        = some (bcell false) := by
      rw [stF_lookup_tail (by omega),
        lookup_append_right (hdead (q + 3) (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_self]
    have hst : storeTarget (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (q + 4))
        (.chain (.addr (.base ⟨q + 3⟩)) [] []) (.bool true)
        = .ok (stStx σ (Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (.base ⟨q + 3⟩)
            ⟨some .bool, .bool true⟩) (q + 4)) :=
      storeTarget_addr hlk (st_norm_bool _ _)
    have h := stepFnIter_one (stepFn_store_step (rs := []) (vs := [])
      (body := .seqn #[]) (env := stPoEnv q) (k := (.seq [.while (.boolLit true) stPopBody] (stPoEnv q) (.seq [] ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase]) (.seq [stS9, stS10] ([stTopP q, stBase]) stStop)))) (ch := ch) hst)
    rw [show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (.base ⟨q + 3⟩)
        ⟨some .bool, .bool true⟩ = (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell true)])) from by
      rw [stF_set_tail (by omega),
        set_append_right (hdead (q + 3) (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_self]] at h
    exact h
  have s16 := mn_G6 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell true)])) (q + 4)) q ch
  have s17 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell true)])) (q + 4))
      (.exec (.seqn #[]) (stPoEnv q) (.seq [.while (.boolLit true) stPopBody] (stPoEnv q) (.seq [] ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase]) (.seq [stS9, stS10] ([stTopP q, stBase]) stStop)))) ch
      = .ok (.next (.seq (#[].toList
            ++ [.while (.boolLit true) stPopBody]) (stPoEnv q)
            (.seq [] ([[("j", .base ⟨q + 2⟩)], stTopP q, stBase])
              (.seq [stS9, stS10] ([stTopP q, stBase]) stStop))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell true)])) (q + 4)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have s18 := mn_G7 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell true)])) (q + 4)) q ch
  have s19 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell true)])) (q + 4))
      (.evalE (.var "$forFirst") (stPoEnv1 q)
        (.ifK (.assign (.var "$forFirst") (.boolLit false))
          (.assign (.var "j") (.add (.var "j") (.intLit 1 .uint64)))
          (stPoEnv1 q) (.seq [.seqn #[], .ifThenElse (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt, stPFillBlock] (stPoEnv1 q) (stPoLoopK q)))) ch
      = .ok (.retV (.bool true)
            (.ifK (.assign (.var "$forFirst") (.boolLit false))
              (.assign (.var "j")
                (.add (.var "j") (.intLit 1 .uint64)))
              (stPoEnv1 q) (.seq [.seqn #[], .ifThenElse (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt, stPFillBlock] (stPoEnv1 q) (stPoLoopK q))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell true)])) (q + 4)), ch) := by
    have hlk : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell true)])) (.base ⟨q + 3⟩)
        = some (bcell true) := by
      rw [stF_lookup_tail (by omega),
        lookup_append_right (hdead (q + 3) (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_self]
    exact stepFnIter_one (stepFn_var (c := bcell true) rfl hlk)
  have s20 := mn_G8 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell true)])) (q + 4)) q ch
  have s21 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell true)])) (q + 4))
      (.next (.storeK [.chain (.addr (.base ⟨q + 3⟩)) [] []]
        [.bool false] (.seqn #[]) (stPoEnv1 q) (.seq [.seqn #[], .ifThenElse (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt, stPFillBlock] (stPoEnv1 q) (stPoLoopK q)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (stPoEnv1 q) (.seq [.seqn #[], .ifThenElse (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt, stPFillBlock] (stPoEnv1 q) (stPoLoopK q))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (q + 4)), ch) := by
    have hlk : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell true)])) (.base ⟨q + 3⟩)
        = some (bcell true) := by
      rw [stF_lookup_tail (by omega),
        lookup_append_right (hdead (q + 3) (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_self]
    have hst : storeTarget (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell true)])) (q + 4))
        (.chain (.addr (.base ⟨q + 3⟩)) [] []) (.bool false)
        = .ok (stStx σ (Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell true)])) (.base ⟨q + 3⟩)
            ⟨some .bool, .bool false⟩) (q + 4)) :=
      storeTarget_addr hlk (st_norm_bool _ _)
    have h := stepFnIter_one (stepFn_store_step (rs := []) (vs := [])
      (body := .seqn #[]) (env := stPoEnv1 q) (k := (.seq [.seqn #[], .ifThenElse (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt, stPFillBlock] (stPoEnv1 q) (stPoLoopK q))) (ch := ch)
      hst)
    rw [show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell true)])) (.base ⟨q + 3⟩)
        ⟨some .bool, .bool false⟩ = (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) from by
      rw [stF_set_tail (by omega),
        set_append_right (hdead (q + 3) (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_self]] at h
    exact h
  have s22 := mn_G9 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (q + 4)) q ch
  have s23 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (q + 4))
      (.exec (.seqn #[]) (stPoEnv1 q) (.seq [.seqn #[], .ifThenElse (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt, stPFillBlock] (stPoEnv1 q) (stPoLoopK q))) ch
      = .ok (.next (.seq (#[].toList ++ [.seqn #[], .ifThenElse
            (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
            stPFillBlock]) (stPoEnv1 q) (stPoLoopK q)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (q + 4)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have s24 := mn_G10 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (q + 4)) q ch
  have s25 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (q + 4))
      (.exec (.seqn #[]) (stPoEnv1 q)
        (.seq [.ifThenElse (.lessCmp (.var "j") (.var "m"))
            (.seqn #[]) .breakStmt, stPFillBlock] (stPoEnv1 q)
          (stPoLoopK q))) ch
      = .ok (.next (.seq (#[].toList ++ [.ifThenElse
            (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
            stPFillBlock]) (stPoEnv1 q) (stPoLoopK q)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (q + 4)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have s26 := mn_G11 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (q + 4)) q ch
  have s27 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (q + 4))
      (.evalE (.var "j") (stPoEnv1 q)
        (.strictK .lessCmp [] [.var "m"] (stPoEnv1 q) (stPoCmpK q))) ch
      = .ok (.retV (.int 0 .uint64)
            (.strictK .lessCmp [] [.var "m"] (stPoEnv1 q)
              (stPoCmpK q)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (q + 4)), ch) := by
    have hlk : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (.base ⟨q + 2⟩)
        = some (u64c 0) := by
      rw [stF_lookup_tail (by omega),
        lookup_append_right (hdead (q + 2) (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_self]
    exact stepFnIter_one (stepFn_var (c := u64c 0) rfl hlk)
  have s28 := mn_G12 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (q + 4)) q 0 ch
  have s29 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (q + 4))
      (.evalE (.var "m") (stPoEnv1 q)
        (.strictK .lessCmp [.int 0 .uint64] [] (stPoEnv1 q)
          (stPoCmpK q))) ch
      = .ok (.retV (.int mv .uint64)
            (.strictK .lessCmp [.int 0 .uint64] [] (stPoEnv1 q)
              (stPoCmpK q)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (q + 4)), ch) := by
    have hlk : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (.base ⟨q⟩)
        = some (u64c mv) := by
      rw [stF_lookup_tail (by omega),
        lookup_append_right (hdead q (by omega)),
        lookup_cons_self]
    exact stepFnIter_one (stepFn_var (c := u64c mv) rfl hlk)
  have s30 := mn_G13 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)])) (q + 4)) q 0 mv ch
  have hall := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain s1 s2) s3) s4) s5) s6) s7) s8)
    s9) s10) s11) s12) s13) s14) s15) s16) s17) s18) s19) s20) s21)
    s22) s23) s24) s25) s26) s27) s28) s29) s30
  rw [show (57 : Nat) = 1 + 1 + 1 + 3 + 1 + 1 + 1 + 6 + 1 + 1 + 1 + 3
      + 1 + 6 + 1 + 1 + 1 + 7 + 1 + 6 + 1 + 1 + 1 + 1 + 1 + 3 + 1 + 1
      + 1 + 1 from rfl]
  rw [show (T ++ stM q mv zeros8 0 false : Heap)
      = T ++ [(.base ⟨q⟩, u64c mv), (.base ⟨q + 1⟩, arrC 8 zeros8), (.base ⟨q + 2⟩, u64c 0), (.base ⟨q + 3⟩, bcell false)] from by simp [stM]]
  exact hall

/-- **The min phase**: push exit → the first pop checkpoint. `86 + 12·[n<k]`
steps; `m` lands at `min k n`; the pop block allocates at the symbolic
base `q`. -/
theorem mn_phase (σ : ExecState) (n seed k : Nat) (b c q : Nat)
    (T : Heap) (ch : Choices) (hq12 : 12 ≤ q) (hn8 : n ≤ 8)
    (hk : k < 2 ^ 64) (hdead : DeadFrom T q) :
    stepFnIter (86 + (if n < k then 12 else 0))
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
        (stPre n seed) ((n : Nat) : Int) T) q)
      (.retV (.bool false) stPuCmpK) ch
      = .ok (.retV (.bool (decide ((0 : Int)
            < ((min k n : Nat) : Int)))) (stPoCmpK q),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
            (stPre n seed) ((n : Nat) : Int)
            (T ++ stM q ((min k n : Nat) : Int) zeros8 0 false)) (q + 4),
          ch) := by
  have hA := mn_A (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
    (sHv b n c) (stPre n seed) ((n : Nat) : Int) T) q) ch
  -- m declared at q
  have h1 : stepFnIter 1
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
        (stPre n seed) ((n : Nat) : Int) T) q)
      (.exec (.initialization { id := "m", typ := tU64 })
        [stTop, stBase]
        (.seq [.assign (.var "m") (.var "k"), stS6, stS7, stS8, stS9,
          stS10] [stTop, stBase] stStop)) ch
      = .ok (.next (.seq [.assign (.var "m") (.var "k"), stS6, stS7,
            stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase])
            stStop),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
            (stPre n seed) ((n : Nat) : Int)
            (T ++ [(.base ⟨q⟩, u64c 0)])) (q + 1), ch) := by
    have h := stepFn_init_seq (σ := stStx σ (stHp (n : Int) (seed : Int)
      (k : Int) (sHv b n c) (stPre n seed) ((n : Nat) : Int) T) q)
      (p := { id := "m", typ := tU64 })
      (rest := [.assign (.var "m") (.var "k"), stS6, stS7, stS8, stS9,
        stS10])
      (env := [stTop, stBase]) (k := stStop) (ch := ch)
      (v := .int 0 .uint64)
      (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
    dsimp only at h
    rw [stF_set_fresh hq12 hdead (Nat.le_refl q)] at h
    exact stepFnIter_one h
  have hB := mn_B σ (n : Int) (seed : Int) (k : Int) (sHv b n c)
    (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c 0)]) q
    (q + 1) ch
  have hlkM0 : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int)
      (sHv b n c) (stPre n seed) ((n : Nat) : Int)
      (T ++ [(.base ⟨q⟩, u64c 0)])) (.base ⟨q⟩) = some (u64c 0) := by
    rw [stF_lookup_tail hq12,
      lookup_append_right (hdead q (Nat.le_refl q)),
      lookup_singleton_self]
  have h2 : stepFnIter 1
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
        (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c 0)]))
        (q + 1))
      (.next (.storeK [.chain (.addr (.base ⟨q⟩)) [] []]
        [.int (k : Int) .uint64] (.seqn #[])
        ([("m", .base ⟨q⟩) :: stTop, stBase])
        (.seq [stS6, stS7, stS8, stS9, stS10]
          ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop))) ch
      = .ok (.next (.storeK [] [] (.seqn #[])
            ([("m", .base ⟨q⟩) :: stTop, stBase])
            (.seq [stS6, stS7, stS8, stS9, stS10]
              ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
            (stPre n seed) ((n : Nat) : Int)
            (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (q + 1), ch) := by
    have hst : storeTarget
        (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
          (stPre n seed) ((n : Nat) : Int)
          (T ++ [(.base ⟨q⟩, u64c 0)])) (q + 1))
        (.chain (.addr (.base ⟨q⟩)) [] []) (.int (k : Int) .uint64)
        = .ok (stStx σ
            (Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
              (stPre n seed) ((n : Nat) : Int)
              (T ++ [(.base ⟨q⟩, u64c 0)])) (.base ⟨q⟩)
              (u64c (IntKind.normalize .uint64 (k : Int)))) (q + 1)) :=
      storeTarget_addr hlkM0 (st_norm_u64 _ (k : Int))
    rw [unorm_nat_of_lt hk] at hst
    have h := stepFnIter_one (stepFn_store_step (rs := []) (vs := [])
      (body := .seqn #[])
      (env := [("m", .base ⟨q⟩) :: stTop, stBase])
      (k := .seq [stS6, stS7, stS8, stS9, stS10]
        ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop) (ch := ch) hst)
    rw [show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
        (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c 0)]))
        (.base ⟨q⟩) (u64c (k : Int))
        = stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
            (stPre n seed) ((n : Nat) : Int)
            (T ++ [(.base ⟨q⟩, u64c (k : Int))]) from by
      rw [stF_set_tail hq12,
        set_append_right (hdead q (Nat.le_refl q)),
        set_singleton_self]] at h
    exact h
  have hC0 := mn_C0 (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
    (sHv b n c) (stPre n seed) ((n : Nat) : Int)
    (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (q + 1)) q ch
  have hSp1 : stepFnIter 1
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
        (stPre n seed) ((n : Nat) : Int)
        (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (q + 1))
      (.exec (.seqn #[]) ([("m", .base ⟨q⟩) :: stTop, stBase])
        (.seq [stS6, stS7, stS8, stS9, stS10]
          ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)) ch
      = .ok (.next (.seq (#[].toList ++ [stS6, stS7, stS8, stS9, stS10])
            ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
            (stPre n seed) ((n : Nat) : Int)
            (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (q + 1), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have hC1 := mn_C1 σ (n : Int) (seed : Int) (k : Int) (sHv b n c)
    (stPre n seed) ((n : Nat) : Int)
    (T ++ [(.base ⟨q⟩, u64c (k : Int))]) q (q + 1) ch
  have hlkM : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int)
      (sHv b n c) (stPre n seed) ((n : Nat) : Int)
      (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (.base ⟨q⟩)
      = some (u64c (k : Int)) := by
    rw [stF_lookup_tail hq12,
      lookup_append_right (hdead q (Nat.le_refl q)),
      lookup_singleton_self]
  have h3 : stepFnIter 1
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
        (stPre n seed) ((n : Nat) : Int)
        (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (q + 1))
      (.evalE (.var "m") ([("m", .base ⟨q⟩) :: stTop, stBase])
        (.strictK .lessCmp [.int ((n : Nat) : Int) .uint64] []
          ([("m", .base ⟨q⟩) :: stTop, stBase])
          (.ifK (.block #[] #[.seqn #[.assign (.var "m") (.var "n")]])
            (.seqn #[]) ([("m", .base ⟨q⟩) :: stTop, stBase])
            (.seq [stS7, stS8, stS9, stS10]
              ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)))) ch
      = .ok (.retV (.int (k : Int) .uint64)
            (.strictK .lessCmp [.int ((n : Nat) : Int) .uint64] []
              ([("m", .base ⟨q⟩) :: stTop, stBase])
              (.ifK (.block #[]
                  #[.seqn #[.assign (.var "m") (.var "n")]])
                (.seqn #[]) ([("m", .base ⟨q⟩) :: stTop, stBase])
                (.seq [stS7, stS8, stS9, stS10]
                  ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop))),
          stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
            (stPre n seed) ((n : Nat) : Int)
            (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (q + 1), ch) :=
    stepFnIter_one (stepFn_var (c := u64c (k : Int)) rfl hlkM)
  have hC2 := mn_C2 (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
    (sHv b n c) (stPre n seed) ((n : Nat) : Int)
    (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (q + 1))
    ((n : Nat) : Int) ((k : Nat) : Int) q ch
  have hHead := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain hA h1) hB) h2) hC0) hSp1) hC1)
    h3) hC2
  by_cases hnk : n < k
  · -- branch TAKEN: m = n
    rw [show (decide (((n : Nat) : Int) < ((k : Nat) : Int))) = true from
      decide_eq_true (by exact_mod_cast hnk)] at hHead
    have d0 := mn_D0 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (q + 1)) q ch
    have d1 := mn_D1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (q + 1)) q ch
    have d1s : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (q + 1))
        (.exec (.seqn #[.assign (.var "m") (.var "n")])
          ([] :: [("m", .base ⟨q⟩) :: stTop, stBase])
          (.seq [] ([] :: [("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)))
        ch
        = .ok (.next (.seq
              (#[Stmt.assign (.var "m") (.var "n")].toList ++ [])
              ([] :: [("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)),
            (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (q + 1)), ch) :=
      stepFnIter_one (stepFn_seqn_splice)
    have d2 := mn_D2 σ (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int)
      (T ++ [(.base ⟨q⟩, u64c (k : Int))]) q (q + 1) ch
    have hlkMq : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (.base ⟨q⟩)
        = some (u64c (k : Int)) := by
      rw [stF_lookup_tail hq12,
        lookup_append_right (hdead q (Nat.le_refl q)),
        lookup_singleton_self]
    have d3 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (q + 1))
        (.next (.storeK [.chain (.addr (.base ⟨q⟩)) [] []]
          [.int ((n : Nat) : Int) .uint64] (.seqn #[])
          ([] :: [("m", .base ⟨q⟩) :: stTop, stBase])
          (.seq [] ([] :: [("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop))))
        ch
        = .ok (.next (.storeK [] [] (.seqn #[])
              ([] :: [("m", .base ⟨q⟩) :: stTop, stBase])
              (.seq [] ([] :: [("m", .base ⟨q⟩) :: stTop, stBase])
                (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop))),
            (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c ((n : Nat) : Int))])) (q + 1)), ch) := by
      have hst : storeTarget (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (q + 1))
          (.chain (.addr (.base ⟨q⟩)) [] [])
          (.int ((n : Nat) : Int) .uint64)
          = .ok (stStx σ (Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (.base ⟨q⟩)
              (u64c (IntKind.normalize .uint64 ((n : Nat) : Int))))
              (q + 1)) :=
        storeTarget_addr hlkMq (st_norm_u64 _ ((n : Nat) : Int))
      rw [unorm_nat_of_lt (by omega : n < 2 ^ 64)] at hst
      have h := stepFnIter_one (stepFn_store_step (rs := []) (vs := [])
        (body := .seqn #[])
        (env := [] :: [("m", .base ⟨q⟩) :: stTop, stBase])
        (k := .seq [] ([] :: [("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop))
        (ch := ch) hst)
      rw [show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (.base ⟨q⟩)
          (u64c ((n : Nat) : Int)) = (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c ((n : Nat) : Int))])) from by
        rw [stF_set_tail hq12,
          set_append_right (hdead q (Nat.le_refl q)),
          set_singleton_self]] at h
      exact h
    have d4 := mn_D3 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c ((n : Nat) : Int))])) (q + 1)) q ch
    have d4s : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c ((n : Nat) : Int))])) (q + 1))
        (.exec (.seqn #[])
          ([] :: [("m", .base ⟨q⟩) :: stTop, stBase])
          (.seq [] ([] :: [("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)))
        ch
        = .ok (.next (.seq (#[].toList ++ [])
              ([] :: [("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)),
            (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c ((n : Nat) : Int))])) (q + 1)), ch) :=
      stepFnIter_one (stepFn_seqn_splice)
    have d5 := mn_D4 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c ((n : Nat) : Int))])) (q + 1)) q ch
    have htl := mn_tail σ n seed k b c q ((n : Nat) : Int) T ch hq12
      hdead
    have hfull := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain hHead d0) d1) d1s) d2) d3)
      d4) d4s) d5
    have hfull2 := stepFnIter_chain hfull htl
    rw [if_pos hnk]
    rw [show (86 + 12 : Nat)
        = 9 + 1 + 6 + 1 + 1 + 1 + 5 + 1 + 1 + 2 + 1 + 1 + 6 + 1 + 1
          + 1 + 2 + 57 from rfl]
    rw [show ((min k n : Nat) : Int) = ((n : Nat) : Int) from by
      rw [Nat.min_eq_right (Nat.le_of_lt hnk)]]
    exact hfull2
  · -- branch NOT taken: m = k
    rw [show (decide (((n : Nat) : Int) < ((k : Nat) : Int))) = false from
      decide_eq_false (by
        intro hlt
        exact hnk (by exact_mod_cast hlt))] at hHead
    have e0 := mn_E0 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (q + 1)) q ch
    have e0s : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (q + 1))
        (.exec (.seqn #[]) ([("m", .base ⟨q⟩) :: stTop, stBase]) (.seq [stS7, stS8, stS9, stS10] ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop)) ch
        = .ok (.next (.seq
              (#[].toList ++ [stS7, stS8, stS9, stS10]) ([("m", .base ⟨q⟩) :: stTop, stBase]) stStop),
            (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (q + 1)), ch) :=
      stepFnIter_one (stepFn_seqn_splice)
    have e1 := mn_E1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b n c)
      (stPre n seed) ((n : Nat) : Int) (T ++ [(.base ⟨q⟩, u64c (k : Int))])) (q + 1)) q ch
    have htl := mn_tail σ n seed k b c q ((k : Nat) : Int) T ch hq12
      hdead
    have hfull := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      hHead e0) e0s) e1
    have hfull2 := stepFnIter_chain hfull htl
    rw [if_neg hnk]
    rw [show (86 + 0 : Nat)
        = 9 + 1 + 6 + 1 + 1 + 1 + 5 + 1 + 1 + 1 + 1 + 1 + 57 from rfl]
    rw [show ((min k n : Nat) : Int) = ((k : Nat) : Int) from by
      rw [Nat.min_eq_left (by omega)]]
    exact hfull2

/-! ## The pop phase: raw segments (state-generic where no heap cell
is touched; the `s` reads at the concrete front carry the heap
shape) -/

def stPoKCall2 (q na : Nat) : Cont :=
  .seq [stPFill3] (stPoEnvV q na) (stPoK0 q)
def stPoFrameK2 (q na : Nat) : Cont :=
  .frame stPoPlans (stPoEnvV q na) [.base ⟨na + 2⟩, .base ⟨na + 3⟩] []
    (stPoKCall2 q na) false
/-- The pop callee env with its local `v` declared. -/
def stPoFrEnvV2 (na : Nat) : LocalEnv :=
  [("v", .base ⟨na + 4⟩)] :: stPoFrEnv na

theorem po_A1 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 1 σ (.retV (.bool true) (stPoCmpK q)) ch
      = .ok (.exec (.seqn #[]) (stPoEnv1 q)
          (.seq [stPFillBlock] (stPoEnv1 q) (stPoLoopK q)), σ, ch) := by
  with_unfolding_all rfl

theorem po_A2 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 3 σ
      (.next (.seq [stPFillBlock] (stPoEnv1 q) (stPoLoopK q))) ch
      = .ok (.exec stPFill1 (stPoEnv2 q)
          (.seq [stPFill2, stPFill3] (stPoEnv2 q)
            (.seq [] (stPoEnv1 q) (stPoLoopK q))), σ, ch) := by
  with_unfolding_all rfl

theorem po_A3 (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.seq [.initialization { id := "v", typ := tU64 },
        stPFill2, stPFill3] (stPoEnv2 q)
        (.seq [] (stPoEnv1 q) (stPoLoopK q)))) ch
      = .ok (.exec (.initialization { id := "v", typ := tU64 })
          (stPoEnv2 q)
          (.seq [stPFill2, stPFill3] (stPoEnv2 q)
            (.seq [] (stPoEnv1 q) (stPoLoopK q))), σ, ch) := by
  with_unfolding_all rfl

theorem po_B1 (σ : ExecState) (q na : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.seq [stPFill2, stPFill3] (stPoEnvV q na) (stPoK0 q))) ch
      = .ok (.exec stPFill2 (stPoEnvV q na) (stPoKCall2 q na), σ,
        ch) := by
  with_unfolding_all rfl

/-- B2: the pop call's `s` argument read at the concrete front. 3
steps. -/
theorem po_B2 (σ : ExecState) (nv sv kv : Int) (sh : GoValue)
    (pl : List Int) (iv : Int) (T : Heap) (q na na' : Nat)
    (ch : Choices) :
    stepFnIter 3 (stStx σ (stHp nv sv kv sh pl iv T) na')
      (.next (.seq [.call #[.var "s", .var "v"] ⟨"pop"⟩ #[.var "s"],
        stPFill3] (stPoEnvV q na) (stPoK0 q))) ch
      = .ok (.retV sh
          (.callArgsK ⟨"pop"⟩ stPoPlans [] [] (stPoEnvV q na)
            (stPoKCall2 q na)),
        stStx σ (stHp nv sv kv sh pl iv T) na', ch) := by
  with_unfolding_all rfl

theorem po_C1 (σ : ExecState) (q na : Nat) (ch : Choices) :
    stepFnIter 2 σ
      (.exec popFunc.body (stPoFrEnv na) (stPoFrameK2 q na)) ch
      = .ok (.exec popB1 (stPoFrEnv2 na)
          (.seq [popB2] (stPoFrEnv2 na) (stPoFrameK2 q na)), σ,
        ch) := by
  with_unfolding_all rfl

theorem po_C2 (σ : ExecState) (q na : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.seq [.initialization { id := "v", typ := tU64 },
        .assign (.var "v") (.indexGet (.var "s") sLenM1), popB2]
        (stPoFrEnv2 na) (stPoFrameK2 q na))) ch
      = .ok (.exec (.initialization { id := "v", typ := tU64 })
          (stPoFrEnv2 na)
          (.seq [.assign (.var "v") (.indexGet (.var "s") sLenM1),
            popB2] (stPoFrEnv2 na) (stPoFrameK2 q na)), σ, ch) := by
  with_unfolding_all rfl

theorem po_D1 (σ : ExecState) (q na : Nat) (ch : Choices) :
    stepFnIter 5 σ
      (.next (.seq [.assign (.var "v") (.indexGet (.var "s") sLenM1),
        popB2] (stPoFrEnvV2 na) (stPoFrameK2 q na))) ch
      = .ok (.evalE (.var "s") (stPoFrEnvV2 na)
          (.strictK .indexGet [] [sLenM1] (stPoFrEnvV2 na)
            (.rhsK .vals [.chain (.addr (.base ⟨na + 4⟩)) [] []] [] []
              (.seqn #[]) (stPoFrEnvV2 na)
              (.seq [popB2] (stPoFrEnvV2 na) (stPoFrameK2 q na)))),
        σ, ch) := by
  with_unfolding_all rfl

theorem po_E (σ : ExecState) (q na : Nat) (sh : GoValue)
    (ch : Choices) :
    stepFnIter 3 σ
      (.retV sh (.strictK .indexGet [] [sLenM1] (stPoFrEnvV2 na)
        (.rhsK .vals [.chain (.addr (.base ⟨na + 4⟩)) [] []] [] []
          (.seqn #[]) (stPoFrEnvV2 na)
          (.seq [popB2] (stPoFrEnvV2 na) (stPoFrameK2 q na))))) ch
      = .ok (.evalE (.var "s") (stPoFrEnvV2 na)
          (.strictK (.lengthOf (some sliceU)) [] [] (stPoFrEnvV2 na)
            (.strictK .sub [] [.intLit 1 .int] (stPoFrEnvV2 na)
              (.strictK .indexGet [sh] [] (stPoFrEnvV2 na)
                (.rhsK .vals [.chain (.addr (.base ⟨na + 4⟩)) [] []]
                  [] [] (.seqn #[]) (stPoFrEnvV2 na)
                  (.seq [popB2] (stPoFrEnvV2 na)
                    (stPoFrameK2 q na)))))),
        σ, ch) := by
  with_unfolding_all rfl

theorem po_F (σ : ExecState) (q na : Nat) (sh : GoValue) (lv : Int)
    (ch : Choices) :
    stepFnIter 3 σ
      (.retV (.int lv .int)
        (.strictK .sub [] [.intLit 1 .int] (stPoFrEnvV2 na)
          (.strictK .indexGet [sh] [] (stPoFrEnvV2 na)
            (.rhsK .vals [.chain (.addr (.base ⟨na + 4⟩)) [] []] [] []
              (.seqn #[]) (stPoFrEnvV2 na)
              (.seq [popB2] (stPoFrEnvV2 na) (stPoFrameK2 q na)))))) ch
      = .ok (.retV (.int (IntKind.normalize .int (lv - 1)) .int)
          (.strictK .indexGet [sh] [] (stPoFrEnvV2 na)
            (.rhsK .vals [.chain (.addr (.base ⟨na + 4⟩)) [] []] [] []
              (.seqn #[]) (stPoFrEnvV2 na)
              (.seq [popB2] (stPoFrEnvV2 na) (stPoFrameK2 q na)))),
        σ, ch) := by
  with_unfolding_all rfl

theorem po_G (σ : ExecState) (q na : Nat) (w : GoValue) (ch : Choices) :
    stepFnIter 1 σ
      (.retV w (.rhsK .vals [.chain (.addr (.base ⟨na + 4⟩)) [] []] [] []
        (.seqn #[]) (stPoFrEnvV2 na)
        (.seq [popB2] (stPoFrEnvV2 na) (stPoFrameK2 q na)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na + 4⟩)) [] []] [w]
          (.seqn #[]) (stPoFrEnvV2 na)
          (.seq [popB2] (stPoFrEnvV2 na) (stPoFrameK2 q na))), σ,
        ch) := by
  with_unfolding_all rfl

theorem po_H1 (σ : ExecState) (q na : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (stPoFrEnvV2 na)
        (.seq [popB2] (stPoFrEnvV2 na) (stPoFrameK2 q na)))) ch
      = .ok (.exec (.seqn #[]) (stPoFrEnvV2 na)
          (.seq [popB2] (stPoFrEnvV2 na) (stPoFrameK2 q na)), σ,
        ch) := by
  with_unfolding_all rfl

theorem po_H2 (σ : ExecState) (q na : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.seq [popB2] (stPoFrEnvV2 na) (stPoFrameK2 q na))) ch
      = .ok (.exec popB2 (stPoFrEnvV2 na)
          (.seq [] (stPoFrEnvV2 na) (stPoFrameK2 q na)), σ, ch) := by
  with_unfolding_all rfl

theorem po_H3 (σ : ExecState) (q na : Nat) (ch : Choices) :
    stepFnIter 5 σ
      (.next (.seq [.assign (.var "$res0")
          (.slice (.var "s") (.intLit 0 .int) sLenM1 none),
        .assign (.var "$res1") (.var "v"), .returnStmt]
        (stPoFrEnvV2 na) (stPoFrameK2 q na))) ch
      = .ok (.evalE (.var "s") (stPoFrEnvV2 na)
          (.strictK (.sliceExpr false) [] [.intLit 0 .int, sLenM1]
            (stPoFrEnvV2 na)
            (.rhsK .vals [.chain (.addr (.base ⟨na + 2⟩)) [] []] [] []
              (.seqn #[]) (stPoFrEnvV2 na)
              (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
                (stPoFrEnvV2 na) (stPoFrameK2 q na)))), σ, ch) := by
  with_unfolding_all rfl

theorem po_I (σ : ExecState) (q na : Nat) (sh : GoValue)
    (ch : Choices) :
    stepFnIter 5 σ
      (.retV sh (.strictK (.sliceExpr false) [] [.intLit 0 .int, sLenM1]
        (stPoFrEnvV2 na)
        (.rhsK .vals [.chain (.addr (.base ⟨na + 2⟩)) [] []] [] []
          (.seqn #[]) (stPoFrEnvV2 na)
          (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
            (stPoFrEnvV2 na) (stPoFrameK2 q na))))) ch
      = .ok (.evalE (.var "s") (stPoFrEnvV2 na)
          (.strictK (.lengthOf (some sliceU)) [] [] (stPoFrEnvV2 na)
            (.strictK .sub [] [.intLit 1 .int] (stPoFrEnvV2 na)
              (.strictK (.sliceExpr false) [.int 0 .int, sh] []
                (stPoFrEnvV2 na)
                (.rhsK .vals [.chain (.addr (.base ⟨na + 2⟩)) [] []]
                  [] [] (.seqn #[]) (stPoFrEnvV2 na)
                  (.seq [.assign (.var "$res1") (.var "v"),
                    .returnStmt] (stPoFrEnvV2 na)
                    (stPoFrameK2 q na)))))),
        σ, ch) := by
  with_unfolding_all rfl

theorem po_J (σ : ExecState) (q na : Nat) (sh : GoValue) (lv : Int)
    (ch : Choices) :
    stepFnIter 3 σ
      (.retV (.int lv .int)
        (.strictK .sub [] [.intLit 1 .int] (stPoFrEnvV2 na)
          (.strictK (.sliceExpr false) [.int 0 .int, sh] []
            (stPoFrEnvV2 na)
            (.rhsK .vals [.chain (.addr (.base ⟨na + 2⟩)) [] []] [] []
              (.seqn #[]) (stPoFrEnvV2 na)
              (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
                (stPoFrEnvV2 na) (stPoFrameK2 q na)))))) ch
      = .ok (.retV (.int (IntKind.normalize .int (lv - 1)) .int)
          (.strictK (.sliceExpr false) [.int 0 .int, sh] []
            (stPoFrEnvV2 na)
            (.rhsK .vals [.chain (.addr (.base ⟨na + 2⟩)) [] []] [] []
              (.seqn #[]) (stPoFrEnvV2 na)
              (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
                (stPoFrEnvV2 na) (stPoFrameK2 q na)))), σ, ch) := by
  with_unfolding_all rfl

theorem po_K (σ : ExecState) (q na : Nat) (w : GoValue) (ch : Choices) :
    stepFnIter 1 σ
      (.retV w (.rhsK .vals [.chain (.addr (.base ⟨na + 2⟩)) [] []] [] []
        (.seqn #[]) (stPoFrEnvV2 na)
        (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
          (stPoFrEnvV2 na) (stPoFrameK2 q na)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na + 2⟩)) [] []] [w]
          (.seqn #[]) (stPoFrEnvV2 na)
          (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
            (stPoFrEnvV2 na) (stPoFrameK2 q na))), σ, ch) := by
  with_unfolding_all rfl

theorem po_L1 (σ : ExecState) (q na : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (stPoFrEnvV2 na)
        (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
          (stPoFrEnvV2 na) (stPoFrameK2 q na)))) ch
      = .ok (.exec (.seqn #[]) (stPoFrEnvV2 na)
          (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
            (stPoFrEnvV2 na) (stPoFrameK2 q na)), σ, ch) := by
  with_unfolding_all rfl

theorem po_L2 (σ : ExecState) (q na : Nat) (ch : Choices) :
    stepFnIter 4 σ
      (.next (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
        (stPoFrEnvV2 na) (stPoFrameK2 q na))) ch
      = .ok (.evalE (.var "v") (stPoFrEnvV2 na)
          (.rhsK .vals [.chain (.addr (.base ⟨na + 3⟩)) [] []] [] []
            (.seqn #[]) (stPoFrEnvV2 na)
            (.seq [.returnStmt] (stPoFrEnvV2 na)
              (stPoFrameK2 q na))), σ, ch) := by
  with_unfolding_all rfl

theorem po_M (σ : ExecState) (q na : Nat) (w : GoValue) (ch : Choices) :
    stepFnIter 1 σ
      (.retV w (.rhsK .vals [.chain (.addr (.base ⟨na + 3⟩)) [] []] [] []
        (.seqn #[]) (stPoFrEnvV2 na)
        (.seq [.returnStmt] (stPoFrEnvV2 na) (stPoFrameK2 q na)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na + 3⟩)) [] []] [w]
          (.seqn #[]) (stPoFrEnvV2 na)
          (.seq [.returnStmt] (stPoFrEnvV2 na) (stPoFrameK2 q na))),
        σ, ch) := by
  with_unfolding_all rfl

theorem po_N1 (σ : ExecState) (q na : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (stPoFrEnvV2 na)
        (.seq [.returnStmt] (stPoFrEnvV2 na) (stPoFrameK2 q na)))) ch
      = .ok (.exec (.seqn #[]) (stPoFrEnvV2 na)
          (.seq [.returnStmt] (stPoFrEnvV2 na) (stPoFrameK2 q na)),
        σ, ch) := by
  with_unfolding_all rfl

theorem po_N2 (σ : ExecState) (q na : Nat) (ch : Choices) :
    stepFnIter 3 σ
      (.next (.seq [.returnStmt] (stPoFrEnvV2 na) (stPoFrameK2 q na)))
      ch
      = .ok (.returning (stPoFrameK2 q na), σ, ch) := by
  with_unfolding_all rfl

theorem po_O (σ : ExecState) (q na : Nat) (v1 v2 : GoValue)
    (ch : Choices) :
    stepFnIter 4 σ
      (.evalE (.ref "s") (stPoEnvV q na)
        (.tgtOpK (.chain []) [] [] []
          [(.chain [], [.ref "v"])] .vals [] [v1, v2] (.seqn #[])
          (stPoEnvV q na) (stPoKCall2 q na))) ch
      = .ok (.next (.storeK
            [.chain (.addr (.base ⟨8⟩)) [] [],
             .chain (.addr (.base ⟨na⟩)) [] []] [v1, v2] (.seqn #[])
            (stPoEnvV q na) (stPoKCall2 q na)), σ, ch) := by
  with_unfolding_all rfl

/-- O2: the front `s` write-back (the first of the two pop stores). 1
step at the concrete front. -/
theorem po_O2 (σ : ExecState) (nv sv kv : Int) (sh sh' : GoValue)
    (pl : List Int) (iv : Int) (T : Heap) (q na na' : Nat)
    (v2 : GoValue) (ch : Choices) :
    stepFnIter 1 (stStx σ (stHp nv sv kv sh pl iv T) na')
      (.next (.storeK
        [.chain (.addr (.base ⟨8⟩)) [] [],
         .chain (.addr (.base ⟨na⟩)) [] []] [sh', v2] (.seqn #[])
        (stPoEnvV q na) (stPoKCall2 q na))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []] [v2]
            (.seqn #[]) (stPoEnvV q na) (stPoKCall2 q na)),
          stStx σ (stHp nv sv kv sh' pl iv T) na', ch) := by
  with_unfolding_all rfl

theorem po_P (σ : ExecState) (q na : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (stPoEnvV q na)
        (stPoKCall2 q na))) ch
      = .ok (.exec (.seqn #[]) (stPoEnvV q na) (stPoKCall2 q na), σ,
        ch) := by
  with_unfolding_all rfl

theorem po_Q (σ : ExecState) (q na : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.seq [stPFill3] (stPoEnvV q na) (stPoK0 q))) ch
      = .ok (.exec stPFill3 (stPoEnvV q na)
          (.seq [] (stPoEnvV q na) (stPoK0 q)), σ, ch) := by
  with_unfolding_all rfl

theorem po_R (σ : ExecState) (q na : Nat) (ch : Choices) :
    stepFnIter 4 σ
      (.next (.seq [.assign (.addr (.indexAddr (.ref "popped")
          (.var "j"))) (.var "v")] (stPoEnvV q na) (stPoK0 q))) ch
      = .ok (.evalE (.var "j") (stPoEnvV q na)
          (.tgtOpK (.chain [.index]) [.addr (.base ⟨q + 1⟩)] [] [] []
            .vals [.var "v"] [] (.seqn #[]) (stPoEnvV q na)
            (.seq [] (stPoEnvV q na) (stPoK0 q))), σ, ch) := by
  with_unfolding_all rfl

theorem po_S (σ : ExecState) (q na : Nat) (jv : Int) (ch : Choices) :
    stepFnIter 1 σ
      (.retV (.int jv .uint64)
        (.tgtOpK (.chain [.index]) [.addr (.base ⟨q + 1⟩)] [] [] []
          .vals [.var "v"] [] (.seqn #[]) (stPoEnvV q na)
          (.seq [] (stPoEnvV q na) (stPoK0 q)))) ch
      = .ok (.evalE (.var "v") (stPoEnvV q na)
          (.rhsK .vals
            [.chain (.addr (.base ⟨q + 1⟩)) [.int jv .uint64] [.index]]
            [] [] (.seqn #[]) (stPoEnvV q na)
            (.seq [] (stPoEnvV q na) (stPoK0 q))), σ, ch) := by
  with_unfolding_all rfl

theorem po_T (σ : ExecState) (q na : Nat) (jv : Int) (w : GoValue)
    (ch : Choices) :
    stepFnIter 1 σ
      (.retV w (.rhsK .vals
        [.chain (.addr (.base ⟨q + 1⟩)) [.int jv .uint64] [.index]]
        [] [] (.seqn #[]) (stPoEnvV q na)
        (.seq [] (stPoEnvV q na) (stPoK0 q)))) ch
      = .ok (.next (.storeK
          [.chain (.addr (.base ⟨q + 1⟩)) [.int jv .uint64] [.index]]
          [w] (.seqn #[]) (stPoEnvV q na)
          (.seq [] (stPoEnvV q na) (stPoK0 q))), σ, ch) := by
  with_unfolding_all rfl

theorem po_U (σ : ExecState) (q na : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (stPoEnvV q na)
        (.seq [] (stPoEnvV q na) (stPoK0 q)))) ch
      = .ok (.exec (.seqn #[]) (stPoEnvV q na)
          (.seq [] (stPoEnvV q na) (stPoK0 q)), σ, ch) := by
  with_unfolding_all rfl

theorem po_V (σ : ExecState) (q na : Nat) (ch : Choices) :
    stepFnIter 2 σ
      (.next (.seq [] (stPoEnvV q na) (stPoK0 q))) ch
      = .ok (.next (stPoLoopK q), σ, ch) := by
  with_unfolding_all rfl

theorem po_W (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 7 σ (.next (stPoLoopK q)) ch
      = .ok (.evalE (.var "$forFirst") (stPoEnv1 q)
          (.ifK (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "j") (.add (.var "j") (.intLit 1 .uint64)))
            (stPoEnv1 q)
            (.seq [.seqn #[], .ifThenElse
                (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
              stPFillBlock] (stPoEnv1 q) (stPoLoopK q))), σ, ch) := by
  with_unfolding_all rfl

theorem po_X (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.retV (.bool false)
        (.ifK (.assign (.var "$forFirst") (.boolLit false))
          (.assign (.var "j") (.add (.var "j") (.intLit 1 .uint64)))
          (stPoEnv1 q)
          (.seq [.seqn #[], .ifThenElse
              (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
            stPFillBlock] (stPoEnv1 q) (stPoLoopK q)))) ch
      = .ok (.exec (.assign (.var "j")
            (.add (.var "j") (.intLit 1 .uint64))) (stPoEnv1 q)
          (.seq [.seqn #[], .ifThenElse
              (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
            stPFillBlock] (stPoEnv1 q) (stPoLoopK q)), σ, ch) := by
  with_unfolding_all rfl

theorem po_Y (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 4 σ
      (.exec (.assign (.var "j")
        (.add (.var "j") (.intLit 1 .uint64))) (stPoEnv1 q)
        (.seq [.seqn #[], .ifThenElse
            (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
          stPFillBlock] (stPoEnv1 q) (stPoLoopK q))) ch
      = .ok (.evalE (.var "j") (stPoEnv1 q)
          (.strictK .add [] [.intLit 1 .uint64] (stPoEnv1 q)
            (.rhsK .vals [.chain (.addr (.base ⟨q + 2⟩)) [] []] [] []
              (.seqn #[]) (stPoEnv1 q)
              (.seq [.seqn #[], .ifThenElse
                  (.lessCmp (.var "j") (.var "m")) (.seqn #[])
                  .breakStmt,
                stPFillBlock] (stPoEnv1 q) (stPoLoopK q)))), σ,
        ch) := by
  with_unfolding_all rfl

theorem po_Z (σ : ExecState) (q : Nat) (jv : Int) (ch : Choices) :
    stepFnIter 4 σ
      (.retV (.int jv .uint64)
        (.strictK .add [] [.intLit 1 .uint64] (stPoEnv1 q)
          (.rhsK .vals [.chain (.addr (.base ⟨q + 2⟩)) [] []] [] []
            (.seqn #[]) (stPoEnv1 q)
            (.seq [.seqn #[], .ifThenElse
                (.lessCmp (.var "j") (.var "m")) (.seqn #[])
                .breakStmt,
              stPFillBlock] (stPoEnv1 q) (stPoLoopK q))))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨q + 2⟩)) [] []]
            [.int (IntKind.normalize .uint64 (jv + 1)) .uint64]
            (.seqn #[]) (stPoEnv1 q)
            (.seq [.seqn #[], .ifThenElse
                (.lessCmp (.var "j") (.var "m")) (.seqn #[])
                .breakStmt,
              stPFillBlock] (stPoEnv1 q) (stPoLoopK q))), σ, ch) := by
  with_unfolding_all rfl

theorem po_AB (σ : ExecState) (q : Nat) (ch : Choices) :
    stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (stPoEnv1 q)
        (.seq [.seqn #[], .ifThenElse
            (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
          stPFillBlock] (stPoEnv1 q) (stPoLoopK q)))) ch
      = .ok (.exec (.seqn #[]) (stPoEnv1 q)
          (.seq [.seqn #[], .ifThenElse
              (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
            stPFillBlock] (stPoEnv1 q) (stPoLoopK q)), σ, ch) := by
  with_unfolding_all rfl

/-- The backing's total read at the top-of-stack index. -/
theorem st_back_getD {n c j seed : Nat} (hj : j < n) (_hnc : n ≤ c) :
    (stFam n seed ++ List.replicate (c - n) (0 : Int)).getD (n - j - 1) 0
      = (stFam n seed).getD (n - 1 - j) 0 := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [stFam_length]; omega),
    ← List.getD_eq_getElem?_getD, show n - j - 1 = n - 1 - j from by
      omega]

/-- **One pop iteration** (127 steps): read the top, reslice in place
(same backing, `len − 1`), record into `popped[j]`, come back to the
test — deterministic (no choice consumed), the workspace appended past
the allocation front. -/
theorem po_iter (σ : ExecState) (n seed k m j b c q na' : Nat)
    (T P : Heap) (ch : Choices)
    (henterPop : ∀ (H : Heap) (a : Nat) (sh : GoValue),
      enterFrame (stStx σ H a) ⟨"pop"⟩ [sh]
        = .ok (popFunc,
            [[("$res1", .base ⟨a + 2⟩), ("$res0", .base ⟨a + 1⟩),
              ("s", .base ⟨a⟩)]],
            [.base ⟨a + 1⟩, .base ⟨a + 2⟩],
            stStx σ
              (Heap.set (Heap.set (Heap.set H (Loc.base ⟨a⟩) (slC sh))
                  (Loc.base ⟨a + 1⟩) (slC nilSl))
                (Loc.base ⟨a + 2⟩) (u64c 0))
              (a + 3)))
    (hcap : n ≤ 8) (hjm : j < m) (hmn : m ≤ n)
    (hb12 : 12 ≤ b) (hbq : b < q) (hq12 : 12 ≤ q) (hqna : q + 4 ≤ na')
    (hnc : n ≤ c)
    (hbT : Heap.lookup T (Loc.base ⟨b⟩)
      = some (backC c (stFam n seed ++ List.replicate (c - n) 0)))
    (hdT : DeadFrom T q) (hdP : DeadFrom P na') :
    stepFnIter 127
      (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ P))) (na'))
      (.retV (.bool true) (stPoCmpK q)) ch
      = .ok (.retV (.bool (decide (((j + 1 : Nat) : Int)
            < ((m : Nat) : Int)))) (stPoCmpK q),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j + 1 : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))]))) (na' + 5)), ch) := by
  have hnj1 : 1 ≤ n - j := by omega
  have hpopr : (0 : Int) ≤ ((stFam n seed).getD (n - 1 - j) 0) ∧ ((stFam n seed).getD (n - 1 - j) 0) < 2 ^ 64 := by
    have h := stFam_getD (n := n) (seed := seed) (m := n - 1 - j)
      (by omega)
    rw [h]
    have := Nat.mod_lt (seed + (n - 1 - j)) (y := 2 ^ 64) (by omega)
    refine ⟨Int.natCast_nonneg _, ?_⟩
    exact_mod_cast this
  -- parametric helpers over the growing workspace `L` (the P-part)
  have hgrow : ∀ (L : Heap) (x : Nat),
      Heap.lookup L (Loc.base ⟨x⟩) = none → q + 4 ≤ x →
      Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
        (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ L)))
        (Loc.base ⟨x⟩) = none := by
    intro L x hLx hx
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdT x (by omega))]
    simp only [List.cons_append, List.nil_append]
    rw [lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega))]
    exact hLx
  have halloc : ∀ (L : Heap) (x : Nat) (cell : HeapCell),
      Heap.lookup L (Loc.base ⟨x⟩) = none → q + 4 ≤ x →
      Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
        (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ L)))
        (Loc.base ⟨x⟩) cell
      = stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
          (stPre n seed) ((n : Nat) : Int)
          (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (L ++ [(Loc.base ⟨x⟩, cell)]))) := by
    intro L x cell hLx hx
    rw [stF_set_tail (by omega),
      set_append_right (hdT x (by omega))]
    simp only [List.cons_append, List.nil_append]
    rw [set_cons_ne (base_beq_false (by omega)),
      set_cons_ne (base_beq_false (by omega)),
      set_cons_ne (base_beq_false (by omega)),
      set_cons_ne (base_beq_false (by omega)),
      set_fresh hLx]
  -- A: checkpoint → the v declaration (7 steps)
  have a1 := po_A1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P)))) (na')) q ch
  have a2 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P)))) (na'))
      (.exec (.seqn #[]) (stPoEnv1 q)
        (.seq [stPFillBlock] (stPoEnv1 q) (stPoLoopK q))) ch
      = .ok (.next (.seq (#[].toList ++ [stPFillBlock]) (stPoEnv1 q)
            (stPoLoopK q)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P)))) (na')), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have a3 := po_A2 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P)))) (na')) q ch
  have a4 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P)))) (na'))
      (.exec stPFill1 (stPoEnv2 q)
        (.seq [stPFill2, stPFill3] (stPoEnv2 q)
          (.seq [] (stPoEnv1 q) (stPoLoopK q)))) ch
      = .ok (.next (.seq
            (#[Stmt.initialization { id := "v", typ := tU64 }].toList
            ++ [stPFill2, stPFill3]) (stPoEnv2 q)
            (.seq [] (stPoEnv1 q) (stPoLoopK q))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P)))) (na')), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have a5 := po_A3 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P)))) (na')) q ch
  have a6 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P)))) (na'))
      (.exec (.initialization { id := "v", typ := tU64 }) (stPoEnv2 q)
        (.seq [stPFill2, stPFill3] (stPoEnv2 q)
          (.seq [] (stPoEnv1 q) (stPoLoopK q)))) ch
      = .ok (.next (.seq [stPFill2, stPFill3] (stPoEnvV q na')
            (stPoK0 q)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0)])))) (na' + 1)), ch) := by
    have h := stepFn_init_seq (σ := (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P)))) (na')))
      (p := { id := "v", typ := tU64 })
      (rest := [stPFill2, stPFill3]) (env := stPoEnv2 q)
      (k := .seq [] (stPoEnv1 q) (stPoLoopK q)) (ch := ch)
      (v := .int 0 .uint64)
      (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
    dsimp only at h
    rw [halloc P na' (u64c 0) (hdP na' (Nat.le_refl na')) (by omega)]
      at h
    exact stepFnIter_one h
  -- B: the call (5 steps + frame entry)
  have b1 := po_B1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0)])))) (na' + 1)) q na' ch
  have b2 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0)])))) (na' + 1))
      (.exec stPFill2 (stPoEnvV q na') (stPoKCall2 q na')) ch
      = .ok (.next (.seq
            (#[Stmt.call #[Assignee.var "s", Assignee.var "v"]
              ⟨"pop"⟩ #[Expr.var "s"]].toList ++ [stPFill3])
            (stPoEnvV q na') (stPoK0 q)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0)])))) (na' + 1)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have b3 := po_B2 σ (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
    (stPre n seed) ((n : Nat) : Int)
    ((T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0)])) : Heap)) q na' (na' + 1) ch
  have hdP1 : DeadFrom (P ++ [(Loc.base ⟨na'⟩, u64c 0)]) (na' + 1) := hdP.push
  have hdP2 : DeadFrom (P ++ [(Loc.base ⟨na'⟩, u64c 0),
      (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c))]) (na' + 2) :=
    hdP.push2
  have hread : ∀ (L : Heap) (x : Nat) (cl : HeapCell),
      Heap.lookup L (Loc.base ⟨x⟩) = some cl → q + 4 ≤ x →
      Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
        (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ L)))
        (Loc.base ⟨x⟩) = some cl := by
    intro L x cl hLx hx
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdT x (by omega))]
    simp only [List.cons_append, List.nil_append]
    rw [lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega))]
    exact hLx
  -- frame entry
  have hent := henterPop (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0)])))) (na' + 1) (sHv b (n - j) c)
  rw [show na' + 1 + 1 = na' + 2 from rfl,
    show na' + 1 + 2 = na' + 3 from rfl] at hent
  rw [halloc (P ++ [(Loc.base ⟨na'⟩, u64c 0)]) (na' + 1) (slC (sHv b (n - j) c))
    (by
      rw [lookup_append_right (hdP _ (by omega)),
        lookup_cons_ne (base_beq_false (by omega))]
      rfl) (by omega)] at hent
  rw [show (P ++ [(Loc.base ⟨na'⟩, u64c 0)]) ++ [(Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c))] = P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c))] from by simp] at hent
  rw [halloc (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c))]) (na' + 2) (slC nilSl)
    (by
      rw [lookup_append_right (hdP _ (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega))]
      rfl) (by omega)] at hent
  rw [show (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c))]) ++ [(Loc.base ⟨na' + 2⟩, slC nilSl)] = P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl)] from by simp] at hent
  rw [halloc (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl)]) (na' + 3) (u64c 0)
    (by
      rw [lookup_append_right (hdP _ (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega))]
      rfl) (by omega)] at hent
  rw [show (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl)]) ++ [(Loc.base ⟨na' + 3⟩, u64c 0)] = P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0)] from by simp] at hent
  have b4 := stepFnIter_one (stepFn_call_enter (plans := stPoPlans)
    (env := stPoEnvV q na') (k := stPoKCall2 q na') (vals := [])
    (v := (sHv b (n - j) c)) (ch := ch) hent)
  -- C: into the pop frame
  have c1 := po_C1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0)])))) (na' + 4)) q na' ch
  have c2 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0)])))) (na' + 4))
      (.exec popB1 (stPoFrEnv2 na')
        (.seq [popB2] (stPoFrEnv2 na') (stPoFrameK2 q na'))) ch
      = .ok (.next (.seq
            (#[Stmt.initialization { id := "v", typ := tU64 },
              Stmt.assign (.var "v")
                (.indexGet (.var "s") sLenM1)].toList ++ [popB2])
            (stPoFrEnv2 na') (stPoFrameK2 q na')),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0)])))) (na' + 4)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have c3 := po_C2 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0)])))) (na' + 4)) q na' ch
  have c4 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0)])))) (na' + 4))
      (.exec (.initialization { id := "v", typ := tU64 })
        (stPoFrEnv2 na')
        (.seq [.assign (.var "v") (.indexGet (.var "s") sLenM1), popB2]
          (stPoFrEnv2 na') (stPoFrameK2 q na'))) ch
      = .ok (.next (.seq [.assign (.var "v")
            (.indexGet (.var "s") sLenM1), popB2] (stPoFrEnvV2 na')
            (stPoFrameK2 q na')),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (na' + 5)), ch) := by
    have h := stepFn_init_seq (σ := (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0)])))) (na' + 4)))
      (p := { id := "v", typ := tU64 })
      (rest := [.assign (.var "v") (.indexGet (.var "s") sLenM1),
        popB2])
      (env := stPoFrEnv2 na') (k := stPoFrameK2 q na') (ch := ch)
      (v := .int 0 .uint64)
      (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
    dsimp only at h
    rw [halloc (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0)]) (na' + 4) (u64c 0)
      (by
      rw [lookup_append_right (hdP _ (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega))]
      rfl) (by omega)] at h
    rw [show (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0)]) ++ [(Loc.base ⟨na' + 4⟩, u64c 0)] = P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)] from by simp] at h
    exact stepFnIter_one h
  have c5 := po_D1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (na' + 5)) q na' ch
  have hlkSp : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (Loc.base ⟨na' + 1⟩)
      = some (slC (sHv b (n - j) c)) := by
    refine hread _ _ _ ?_ (by omega)
    rw [lookup_append_right (hdP _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self]
  have c6 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (na' + 5))
      (.evalE (.var "s") (stPoFrEnvV2 na')
        (.strictK .indexGet [] [sLenM1] (stPoFrEnvV2 na')
          (.rhsK .vals [.chain (.addr (Loc.base ⟨na' + 4⟩)) [] []] [] []
            (.seqn #[]) (stPoFrEnvV2 na')
            (.seq [popB2] (stPoFrEnvV2 na') (stPoFrameK2 q na'))))) ch
      = .ok (.retV (slC (sHv b (n - j) c)).value
            (.strictK .indexGet [] [sLenM1] (stPoFrEnvV2 na')
              (.rhsK .vals [.chain (.addr (Loc.base ⟨na' + 4⟩)) [] []] [] []
                (.seqn #[]) (stPoFrEnvV2 na')
                (.seq [popB2] (stPoFrEnvV2 na') (stPoFrameK2 q na')))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_var rfl hlkSp)
  have c7 := po_E (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (na' + 5)) q na' (sHv b (n - j) c) ch
  have c8 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (na' + 5))
      (.evalE (.var "s") (stPoFrEnvV2 na')
        (.strictK (.lengthOf (some sliceU)) [] [] (stPoFrEnvV2 na')
          (.strictK .sub [] [.intLit 1 .int] (stPoFrEnvV2 na')
            (.strictK .indexGet [(sHv b (n - j) c)] [] (stPoFrEnvV2 na')
              (.rhsK .vals [.chain (.addr (Loc.base ⟨na' + 4⟩)) [] []] [] []
                (.seqn #[]) (stPoFrEnvV2 na')
                (.seq [popB2] (stPoFrEnvV2 na')
                  (stPoFrameK2 q na'))))))) ch
      = .ok (.retV (slC (sHv b (n - j) c)).value
            (.strictK (.lengthOf (some sliceU)) [] [] (stPoFrEnvV2 na')
              (.strictK .sub [] [.intLit 1 .int] (stPoFrEnvV2 na')
                (.strictK .indexGet [(sHv b (n - j) c)] [] (stPoFrEnvV2 na')
                  (.rhsK .vals [.chain (.addr (Loc.base ⟨na' + 4⟩)) [] []]
                    [] [] (.seqn #[]) (stPoFrEnvV2 na')
                    (.seq [popB2] (stPoFrEnvV2 na')
                      (stPoFrameK2 q na')))))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_var rfl hlkSp)
  have c9 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (na' + 5))
      (.retV (slC (sHv b (n - j) c)).value
        (.strictK (.lengthOf (some sliceU)) [] [] (stPoFrEnvV2 na')
          (.strictK .sub [] [.intLit 1 .int] (stPoFrEnvV2 na')
            (.strictK .indexGet [(sHv b (n - j) c)] [] (stPoFrEnvV2 na')
              (.rhsK .vals [.chain (.addr (Loc.base ⟨na' + 4⟩)) [] []] [] []
                (.seqn #[]) (stPoFrEnvV2 na')
                (.seq [popB2] (stPoFrEnvV2 na')
                  (stPoFrameK2 q na'))))))) ch
      = .ok (.retV (.int ((n - j : Nat) : Int) .int)
            (.strictK .sub [] [.intLit 1 .int] (stPoFrEnvV2 na')
              (.strictK .indexGet [(sHv b (n - j) c)] [] (stPoFrEnvV2 na')
                (.rhsK .vals [.chain (.addr (Loc.base ⟨na' + 4⟩)) [] []]
                  [] [] (.seqn #[]) (stPoFrEnvV2 na')
                  (.seq [popB2] (stPoFrEnvV2 na')
                    (stPoFrameK2 q na'))))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_strict_apply (done := [])
      (applyStrictOp_len_slice (b := .base ⟨b⟩) (off := 0)
        (len := n - j) (cap := c) (elem := tU64) (by omega)))
  have c10 := po_F (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (na' + 5)) q na' (sHv b (n - j) c)
    ((n - j : Nat) : Int) ch
  rw [show ((n - j : Nat) : Int) - 1 = ((n - j - 1 : Nat) : Int) from by
      omega,
    inorm_nat_of_lt (by omega : n - j - 1 < 2 ^ 63)] at c10
  have hlkB : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (Loc.base ⟨b⟩)
      = some (backC c (stFam n seed ++ List.replicate (c - n) 0)) := by
    rw [stF_lookup_tail (by omega), lookup_append_left hbT]
  have hgetB : (⟨(stFam n seed
      ++ List.replicate (c - n) 0).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + (n - j - 1)]?
      = some (.int ((stFam n seed).getD (n - 1 - j) 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by
      rw [List.length_append, stFam_length, List.length_replicate]
      omega)]
    rw [st_back_getD (by omega) hnc]
  have c11 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (na' + 5))
      (.retV (.int ((n - j - 1 : Nat) : Int) .int)
        (.strictK .indexGet [(sHv b (n - j) c)] [] (stPoFrEnvV2 na')
          (.rhsK .vals [.chain (.addr (Loc.base ⟨na' + 4⟩)) [] []] [] []
            (.seqn #[]) (stPoFrEnvV2 na')
            (.seq [popB2] (stPoFrEnvV2 na') (stPoFrameK2 q na'))))) ch
      = .ok (.retV (.int ((stFam n seed).getD (n - 1 - j) 0) .uint64)
            (.rhsK .vals [.chain (.addr (Loc.base ⟨na' + 4⟩)) [] []] [] []
              (.seqn #[]) (stPoFrEnvV2 na')
              (.seq [popB2] (stPoFrEnvV2 na') (stPoFrameK2 q na'))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_strict_apply (done := [(sHv b (n - j) c)])
      (applyStrictOp_indexGet_slice (ik := .int) hlkB (by omega)
        (by omega) hgetB))
  have c12 := po_G (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (na' + 5)) q na'
    (.int ((stFam n seed).getD (n - 1 - j) 0) .uint64) ch
  have hlkVp5 : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (Loc.base ⟨na' + 4⟩)
      = some (u64c 0) := by
    refine hread _ _ _ ?_ (by omega)
    rw [lookup_append_right (hdP _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self]
  have c13 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (na' + 5))
      (.next (.storeK [.chain (.addr (Loc.base ⟨na' + 4⟩)) [] []]
        [.int ((stFam n seed).getD (n - 1 - j) 0) .uint64] (.seqn #[]) (stPoFrEnvV2 na')
        (.seq [popB2] (stPoFrEnvV2 na') (stPoFrameK2 q na')))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (stPoFrEnvV2 na')
            (.seq [popB2] (stPoFrEnvV2 na') (stPoFrameK2 q na'))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) := by
    have hst : storeTarget (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (na' + 5))
        (.chain (.addr (Loc.base ⟨na' + 4⟩)) [] [])
        (.int ((stFam n seed).getD (n - 1 - j) 0) .uint64)
        = .ok (stStx σ (Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (Loc.base ⟨na' + 4⟩)
            (u64c (IntKind.normalize .uint64 ((stFam n seed).getD (n - 1 - j) 0)))) (na' + 5)) :=
      storeTarget_addr hlkVp5 (st_norm_u64 _ _)
    rw [unorm_of_range hpopr.1 hpopr.2] at hst
    have h := stepFnIter_one (stepFn_store_step (rs := []) (vs := [])
      (body := .seqn #[]) (env := stPoFrEnvV2 na')
      (k := .seq [popB2] (stPoFrEnvV2 na') (stPoFrameK2 q na'))
      (ch := ch) hst)
    rw [show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c 0)])))) (Loc.base ⟨na' + 4⟩)
        (u64c ((stFam n seed).getD (n - 1 - j) 0)) = (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) from by
      rw [stF_set_tail (by omega),
        set_append_right (hdT _ (by omega))]
      simp only [List.cons_append, List.nil_append]
      rw [set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_append_right (hdP _ (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_self]] at h
    exact h
  -- H..N: through the reslice and the return
  have d1 := po_H1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q na' ch
  have d2 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.exec (.seqn #[]) (stPoFrEnvV2 na')
        (.seq [popB2] (stPoFrEnvV2 na') (stPoFrameK2 q na'))) ch
      = .ok (.next (.seq (#[].toList ++ [popB2]) (stPoFrEnvV2 na')
            (stPoFrameK2 q na')),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have d3 := po_H2 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q na' ch
  have d4 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.exec popB2 (stPoFrEnvV2 na')
        (.seq [] (stPoFrEnvV2 na') (stPoFrameK2 q na'))) ch
      = .ok (.next (.seq (#[Stmt.assign (.var "$res0")
            (.slice (.var "s") (.intLit 0 .int) sLenM1 none),
            Stmt.assign (.var "$res1") (.var "v"),
            Stmt.returnStmt].toList ++ []) (stPoFrEnvV2 na')
            (stPoFrameK2 q na')),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have d5 := po_H3 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q na' ch
  have hlkSp6 : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨na' + 1⟩)
      = some (slC (sHv b (n - j) c)) := (by
    refine hread _ _ _ ?_ (by omega)
    rw [lookup_append_right (hdP _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self])
  have d6 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.evalE (.var "s") (stPoFrEnvV2 na')
        (.strictK (.sliceExpr false) [] [.intLit 0 .int, sLenM1]
          (stPoFrEnvV2 na')
          (.rhsK .vals [.chain (.addr (.base ⟨na' + 2⟩)) [] []] [] []
            (.seqn #[]) (stPoFrEnvV2 na')
            (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
              (stPoFrEnvV2 na') (stPoFrameK2 q na'))))) ch
      = .ok (.retV (slC (sHv b (n - j) c)).value
            (.strictK (.sliceExpr false) [] [.intLit 0 .int, sLenM1]
              (stPoFrEnvV2 na')
              (.rhsK .vals [.chain (.addr (.base ⟨na' + 2⟩)) [] []] [] []
                (.seqn #[]) (stPoFrEnvV2 na')
                (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
                  (stPoFrEnvV2 na') (stPoFrameK2 q na')))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_var rfl hlkSp6)
  have d7 := po_I (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q na' (sHv b (n - j) c) ch
  have d8 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.evalE (.var "s") (stPoFrEnvV2 na')
        (.strictK (.lengthOf (some sliceU)) [] [] (stPoFrEnvV2 na')
          (.strictK .sub [] [.intLit 1 .int] (stPoFrEnvV2 na')
            (.strictK (.sliceExpr false) [.int 0 .int, (sHv b (n - j) c)] []
              (stPoFrEnvV2 na')
              (.rhsK .vals [.chain (.addr (.base ⟨na' + 2⟩)) [] []] [] []
                (.seqn #[]) (stPoFrEnvV2 na')
                (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
                  (stPoFrEnvV2 na') (stPoFrameK2 q na'))))))) ch
      = .ok (.retV (slC (sHv b (n - j) c)).value
            (.strictK (.lengthOf (some sliceU)) [] [] (stPoFrEnvV2 na')
              (.strictK .sub [] [.intLit 1 .int] (stPoFrEnvV2 na')
                (.strictK (.sliceExpr false) [.int 0 .int, (sHv b (n - j) c)] []
                  (stPoFrEnvV2 na')
                  (.rhsK .vals [.chain (.addr (.base ⟨na' + 2⟩)) [] []]
                    [] [] (.seqn #[]) (stPoFrEnvV2 na')
                    (.seq [.assign (.var "$res1") (.var "v"),
                      .returnStmt] (stPoFrEnvV2 na')
                      (stPoFrameK2 q na')))))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_var rfl hlkSp6)
  have d9 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.retV (slC (sHv b (n - j) c)).value
        (.strictK (.lengthOf (some sliceU)) [] [] (stPoFrEnvV2 na')
          (.strictK .sub [] [.intLit 1 .int] (stPoFrEnvV2 na')
            (.strictK (.sliceExpr false) [.int 0 .int, (sHv b (n - j) c)] []
              (stPoFrEnvV2 na')
              (.rhsK .vals [.chain (.addr (.base ⟨na' + 2⟩)) [] []] [] []
                (.seqn #[]) (stPoFrEnvV2 na')
                (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
                  (stPoFrEnvV2 na') (stPoFrameK2 q na'))))))) ch
      = .ok (.retV (.int ((n - j : Nat) : Int) .int)
            (.strictK .sub [] [.intLit 1 .int] (stPoFrEnvV2 na')
              (.strictK (.sliceExpr false) [.int 0 .int, (sHv b (n - j) c)] []
                (stPoFrEnvV2 na')
                (.rhsK .vals [.chain (.addr (.base ⟨na' + 2⟩)) [] []]
                  [] [] (.seqn #[]) (stPoFrEnvV2 na')
                  (.seq [.assign (.var "$res1") (.var "v"),
                    .returnStmt] (stPoFrEnvV2 na')
                    (stPoFrameK2 q na'))))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_strict_apply (done := [])
      (applyStrictOp_len_slice (b := .base ⟨b⟩) (off := 0)
        (len := n - j) (cap := c) (elem := tU64) (by omega)))
  have d10 := po_J (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q na' (sHv b (n - j) c)
    ((n - j : Nat) : Int) ch
  rw [show ((n - j : Nat) : Int) - 1 = ((n - j - 1 : Nat) : Int) from by
      omega,
    inorm_nat_of_lt (by omega : n - j - 1 < 2 ^ 63)] at d10
  have d11 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.retV (.int ((n - j - 1 : Nat) : Int) .int)
        (.strictK (.sliceExpr false) [.int 0 .int, (sHv b (n - j) c)] []
          (stPoFrEnvV2 na')
          (.rhsK .vals [.chain (.addr (.base ⟨na' + 2⟩)) [] []] [] []
            (.seqn #[]) (stPoFrEnvV2 na')
            (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
              (stPoFrEnvV2 na') (stPoFrameK2 q na'))))) ch
      = .ok (.retV (.slice ⟨some (.base ⟨b⟩), 0, n - j - 1, c⟩)
            (.rhsK .vals [.chain (.addr (.base ⟨na' + 2⟩)) [] []] [] []
              (.seqn #[]) (stPoFrEnvV2 na')
              (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
                (stPoFrEnvV2 na') (stPoFrameK2 q na'))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_strict_apply
      (done := [.int 0 .int, (sHv b (n - j) c)])
      (st_sliceExpr_slice _ (.base ⟨b⟩) (n - j) (n - j - 1) c .int .int
        (show n - j - 1 ≤ c by omega) (show n - j ≤ c by omega)))
  have d12 := po_K (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q na' (sHv b (n - j - 1) c) ch
  have hlkR0 : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨na' + 2⟩)
      = some (slC nilSl) := (by
    refine hread _ _ _ ?_ (by omega)
    rw [lookup_append_right (hdP _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self])
  have d13 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.next (.storeK [.chain (.addr (.base ⟨na' + 2⟩)) [] []]
        [(sHv b (n - j - 1) c)] (.seqn #[]) (stPoFrEnvV2 na')
        (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
          (stPoFrEnvV2 na') (stPoFrameK2 q na')))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (stPoFrEnvV2 na')
            (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
              (stPoFrEnvV2 na') (stPoFrameK2 q na'))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) := by
    have hst : storeTarget (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
        (.chain (.addr (.base ⟨na' + 2⟩)) [] []) (sHv b (n - j - 1) c)
        = .ok (stStx σ (Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨na' + 2⟩)
            (slC (sHv b (n - j - 1) c))) (na' + 5)) :=
      storeTarget_addr hlkR0 (st_norm_sliceU _ _)
    have h := stepFnIter_one (stepFn_store_step (rs := []) (vs := [])
      (body := .seqn #[]) (env := stPoFrEnvV2 na')
      (k := .seq [.assign (.var "$res1") (.var "v"), .returnStmt]
        (stPoFrEnvV2 na') (stPoFrameK2 q na')) (ch := ch) hst)
    rw [show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC nilSl), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨na' + 2⟩)
        (slC (sHv b (n - j - 1) c)) = (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) from by
      rw [stF_set_tail (by omega),
        set_append_right (hdT _ (by omega))]
      simp only [List.cons_append, List.nil_append]
      rw [set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_append_right (hdP _ (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_self]] at h
    exact h
  have d14 := po_L1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q na' ch
  have d15 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.exec (.seqn #[]) (stPoFrEnvV2 na')
        (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
          (stPoFrEnvV2 na') (stPoFrameK2 q na'))) ch
      = .ok (.next (.seq (#[].toList ++ [.assign (.var "$res1")
            (.var "v"), .returnStmt]) (stPoFrEnvV2 na')
            (stPoFrameK2 q na')),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have d16 := po_L2 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q na' ch
  have hlkVp7 : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨na' + 4⟩)
      = some (u64c ((stFam n seed).getD (n - 1 - j) 0)) := (by
    refine hread _ _ _ ?_ (by omega)
    rw [lookup_append_right (hdP _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self])
  have d17 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.evalE (.var "v") (stPoFrEnvV2 na')
        (.rhsK .vals [.chain (.addr (.base ⟨na' + 3⟩)) [] []] [] []
          (.seqn #[]) (stPoFrEnvV2 na')
          (.seq [.returnStmt] (stPoFrEnvV2 na') (stPoFrameK2 q na'))))
      ch
      = .ok (.retV (.int ((stFam n seed).getD (n - 1 - j) 0) .uint64)
            (.rhsK .vals [.chain (.addr (.base ⟨na' + 3⟩)) [] []] [] []
              (.seqn #[]) (stPoFrEnvV2 na')
              (.seq [.returnStmt] (stPoFrEnvV2 na')
                (stPoFrameK2 q na'))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_var (c := u64c ((stFam n seed).getD (n - 1 - j) 0)) rfl hlkVp7)
  have d18 := po_M (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q na'
    (.int ((stFam n seed).getD (n - 1 - j) 0) .uint64) ch
  have hlkR1 : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨na' + 3⟩)
      = some (u64c 0) := (by
    refine hread _ _ _ ?_ (by omega)
    rw [lookup_append_right (hdP _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self])
  have d19 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.next (.storeK [.chain (.addr (.base ⟨na' + 3⟩)) [] []]
        [.int ((stFam n seed).getD (n - 1 - j) 0) .uint64] (.seqn #[]) (stPoFrEnvV2 na')
        (.seq [.returnStmt] (stPoFrEnvV2 na') (stPoFrameK2 q na')))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (stPoFrEnvV2 na')
            (.seq [.returnStmt] (stPoFrEnvV2 na')
              (stPoFrameK2 q na'))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) := by
    have hst : storeTarget (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
        (.chain (.addr (.base ⟨na' + 3⟩)) [] [])
        (.int ((stFam n seed).getD (n - 1 - j) 0) .uint64)
        = .ok (stStx σ (Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨na' + 3⟩)
            (u64c (IntKind.normalize .uint64 ((stFam n seed).getD (n - 1 - j) 0)))) (na' + 5)) :=
      storeTarget_addr hlkR1 (st_norm_u64 _ _)
    rw [unorm_of_range hpopr.1 hpopr.2] at hst
    have h := stepFnIter_one (stepFn_store_step (rs := []) (vs := [])
      (body := .seqn #[]) (env := stPoFrEnvV2 na')
      (k := .seq [.returnStmt] (stPoFrEnvV2 na') (stPoFrameK2 q na'))
      (ch := ch) hst)
    rw [show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c 0), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨na' + 3⟩)
        (u64c ((stFam n seed).getD (n - 1 - j) 0)) = (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) from by
      rw [stF_set_tail (by omega),
        set_append_right (hdT _ (by omega))]
      simp only [List.cons_append, List.nil_append]
      rw [set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_append_right (hdP _ (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_self]] at h
    exact h
  have d20 := po_N1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q na' ch
  have d21 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.exec (.seqn #[]) (stPoFrEnvV2 na')
        (.seq [.returnStmt] (stPoFrEnvV2 na') (stPoFrameK2 q na'))) ch
      = .ok (.next (.seq (#[].toList ++ [.returnStmt])
            (stPoFrEnvV2 na') (stPoFrameK2 q na')),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have d22 := po_N2 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q na' ch
  have hlkR0' : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨na' + 2⟩)
      = some (slC (sHv b (n - j - 1) c)) := (by
    refine hread _ _ _ ?_ (by omega)
    rw [lookup_append_right (hdP _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self])
  have hlkR1' : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨na' + 3⟩)
      = some (u64c ((stFam n seed).getD (n - 1 - j) 0)) := (by
    refine hread _ _ _ ?_ (by omega)
    rw [lookup_append_right (hdP _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self])
  have d23 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.returning (stPoFrameK2 q na')) ch
      = .ok (.evalE (.ref "s") (stPoEnvV q na')
            (.tgtOpK (.chain []) [] [] []
              [(.chain [], [.ref "v"])] .vals []
              [(slC (sHv b (n - j - 1) c)).value, (u64c ((stFam n seed).getD (n - 1 - j) 0)).value] (.seqn #[])
              (stPoEnvV q na') (stPoKCall2 q na')),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_return_frame (st_loadMany2 hlkR0' hlkR1'))
  have d24 := po_O (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q na' (sHv b (n - j - 1) c)
    (.int ((stFam n seed).getD (n - 1 - j) 0) .uint64) ch
  have d25 := po_O2 σ (n : Int) (seed : Int) (k : Int) (sHv b (n - j) c) (sHv b (n - j - 1) c)
    (stPre n seed) ((n : Nat) : Int) ((T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])) : Heap)) q na'
    (na' + 5) (.int ((stFam n seed).getD (n - 1 - j) 0) .uint64) ch
  have hlkV8 : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨na'⟩)
      = some (u64c 0) := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdT _ (by omega))]
    simp only [List.cons_append, List.nil_append]
    rw [lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
      lookup_append_right (hdP _ (by omega)),
      lookup_cons_self]
  have d26 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.next (.storeK [.chain (.addr (.base ⟨na'⟩)) [] []]
        [.int ((stFam n seed).getD (n - 1 - j) 0) .uint64] (.seqn #[]) (stPoEnvV q na')
        (stPoKCall2 q na'))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (stPoEnvV q na')
            (stPoKCall2 q na')),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) := by
    have hst : storeTarget (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
        (.chain (.addr (.base ⟨na'⟩)) [] []) (.int ((stFam n seed).getD (n - 1 - j) 0) .uint64)
        = .ok (stStx σ (Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨na'⟩)
            (u64c (IntKind.normalize .uint64 ((stFam n seed).getD (n - 1 - j) 0)))) (na' + 5)) :=
      storeTarget_addr hlkV8 (st_norm_u64 _ _)
    rw [unorm_of_range hpopr.1 hpopr.2] at hst
    have h := stepFnIter_one (stepFn_store_step (rs := []) (vs := [])
      (body := .seqn #[]) (env := stPoEnvV q na')
      (k := stPoKCall2 q na') (ch := ch) hst)
    rw [show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c 0), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨na'⟩)
        (u64c ((stFam n seed).getD (n - 1 - j) 0)) = (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) from by
      rw [stF_set_tail (by omega),
        set_append_right (hdT _ (by omega))]
      simp only [List.cons_append, List.nil_append]
      rw [set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_append_right (hdP _ (by omega)),
        set_cons_self]] at h
    exact h
  -- fill-3: popped[j] = v, then the loop redispatch
  have e1 := po_P (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q na' ch
  have e2 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.exec (.seqn #[]) (stPoEnvV q na') (stPoKCall2 q na')) ch
      = .ok (.next (.seq (#[].toList ++ [stPFill3]) (stPoEnvV q na')
            (stPoK0 q)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have e3 := po_Q (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q na' ch
  have e4 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.exec stPFill3 (stPoEnvV q na')
        (.seq [] (stPoEnvV q na') (stPoK0 q))) ch
      = .ok (.next (.seq (#[Stmt.assign (.addr (.indexAddr
            (.ref "popped") (.var "j"))) (.var "v")].toList ++ [])
            (stPoEnvV q na') (stPoK0 q)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have e5 := po_R (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q na' ch
  have hlkJ : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨q + 2⟩)
      = some (u64c ((j : Nat) : Int)) := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdT _ (by omega))]
    simp only [List.cons_append, List.nil_append]
    rw [lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self]
  have e6 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.evalE (.var "j") (stPoEnvV q na')
        (.tgtOpK (.chain [.index]) [.addr (.base ⟨q + 1⟩)] [] [] []
          .vals [.var "v"] [] (.seqn #[]) (stPoEnvV q na')
          (.seq [] (stPoEnvV q na') (stPoK0 q)))) ch
      = .ok (.retV (.int ((j : Nat) : Int) .uint64)
            (.tgtOpK (.chain [.index]) [.addr (.base ⟨q + 1⟩)] [] [] []
              .vals [.var "v"] [] (.seqn #[]) (stPoEnvV q na')
              (.seq [] (stPoEnvV q na') (stPoK0 q))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_var (c := u64c ((j : Nat) : Int)) rfl hlkJ)
  have e7 := po_S (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q na'
    ((j : Nat) : Int) ch
  have hlkVh : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨na'⟩)
      = some (u64c ((stFam n seed).getD (n - 1 - j) 0)) := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdT _ (by omega))]
    simp only [List.cons_append, List.nil_append]
    rw [lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
      lookup_append_right (hdP _ (by omega)),
      lookup_cons_self]
  have e8 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.evalE (.var "v") (stPoEnvV q na')
        (.rhsK .vals
          [.chain (.addr (.base ⟨q + 1⟩)) [.int ((j : Nat) : Int)
            .uint64] [.index]] [] [] (.seqn #[]) (stPoEnvV q na')
          (.seq [] (stPoEnvV q na') (stPoK0 q)))) ch
      = .ok (.retV (.int ((stFam n seed).getD (n - 1 - j) 0) .uint64)
            (.rhsK .vals
              [.chain (.addr (.base ⟨q + 1⟩)) [.int ((j : Nat) : Int)
                .uint64] [.index]] [] [] (.seqn #[]) (stPoEnvV q na')
              (.seq [] (stPoEnvV q na') (stPoK0 q))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_var (c := u64c ((stFam n seed).getD (n - 1 - j) 0)) rfl hlkVh)
  have e9 := po_T (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q na'
    ((j : Nat) : Int) (.int ((stFam n seed).getD (n - 1 - j) 0) .uint64) ch
  have hlkPop : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨q + 1⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨(stPopPre n seed j).map (fun v => .int v .uint64)⟩⟩ := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdT _ (by omega))]
    simp only [List.cons_append, List.nil_append]
    rw [lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self]
  have e10 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.next (.storeK
        [.chain (.addr (.base ⟨q + 1⟩)) [.int ((j : Nat) : Int)
          .uint64] [.index]]
        [.int ((stFam n seed).getD (n - 1 - j) 0) .uint64] (.seqn #[]) (stPoEnvV q na')
        (.seq [] (stPoEnvV q na') (stPoK0 q)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (stPoEnvV q na')
            (.seq [] (stPoEnvV q na') (stPoK0 q))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) := by
    have hst := storeTarget_arrayLocal_u64
      (σ := (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))) (a := ⟨q + 1⟩) (N := 8)
      (i := j) (ik := .uint64) (l := stPopPre n seed j) (w := ((stFam n seed).getD (n - 1 - j) 0))
      hlkPop
      (by rw [stPopPre_length (by omega)]; omega)
      (stPopPre_length (by omega)) stPopPre_range hpopr
    rw [stPopPre_set (by omega : j < 8)] at hst
    have h := stepFnIter_one (stepFn_store_step (rs := []) (vs := [])
      (body := .seqn #[]) (env := stPoEnvV q na')
      (k := .seq [] (stPoEnvV q na') (stPoK0 q)) (ch := ch) hst)
    rw [show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed j)), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨q + 1⟩)
        ⟨some (.array 8 tU64),
          .array ⟨(stPopPre n seed (j + 1)).map
            (fun v => .int v .uint64)⟩⟩
        = (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) from by
      rw [stF_set_tail (by omega),
        set_append_right (hdT _ (by omega))]
      simp only [List.cons_append, List.nil_append]
      rw [set_cons_ne (base_beq_false (by omega)),
        set_cons_self]] at h
    exact h
  have e11 := po_U (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q na' ch
  have e12 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.exec (.seqn #[]) (stPoEnvV q na')
        (.seq [] (stPoEnvV q na') (stPoK0 q))) ch
      = .ok (.next (.seq (#[].toList ++ []) (stPoEnvV q na')
            (stPoK0 q)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have e13 := po_V (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q na' ch
  have e14 := po_W (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q ch
  have hlkFF : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨q + 3⟩)
      = some (bcell false) := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdT _ (by omega))]
    simp only [List.cons_append, List.nil_append]
    rw [lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self]
  have e15 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.evalE (.var "$forFirst") (stPoEnv1 q)
        (.ifK (.assign (.var "$forFirst") (.boolLit false))
          (.assign (.var "j") (.add (.var "j") (.intLit 1 .uint64)))
          (stPoEnv1 q)
          (.seq [.seqn #[], .ifThenElse
              (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
            stPFillBlock] (stPoEnv1 q) (stPoLoopK q)))) ch
      = .ok (.retV (.bool false)
            (.ifK (.assign (.var "$forFirst") (.boolLit false))
              (.assign (.var "j")
                (.add (.var "j") (.intLit 1 .uint64)))
              (stPoEnv1 q)
              (.seq [.seqn #[], .ifThenElse
                  (.lessCmp (.var "j") (.var "m")) (.seqn #[])
                  .breakStmt,
                stPFillBlock] (stPoEnv1 q) (stPoLoopK q))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_var (c := bcell false) rfl hlkFF)
  have e16 := po_X (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q ch
  have e17 := po_Y (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q ch
  have hlkJ1 : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨q + 2⟩)
      = some (u64c ((j : Nat) : Int)) := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdT _ (by omega))]
    simp only [List.cons_append, List.nil_append]
    rw [lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self]
  have e18 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.evalE (.var "j") (stPoEnv1 q)
        (.strictK .add [] [.intLit 1 .uint64] (stPoEnv1 q)
          (.rhsK .vals [.chain (.addr (.base ⟨q + 2⟩)) [] []] [] []
            (.seqn #[]) (stPoEnv1 q)
            (.seq [.seqn #[], .ifThenElse
                (.lessCmp (.var "j") (.var "m")) (.seqn #[])
                .breakStmt,
              stPFillBlock] (stPoEnv1 q) (stPoLoopK q))))) ch
      = .ok (.retV (.int ((j : Nat) : Int) .uint64)
            (.strictK .add [] [.intLit 1 .uint64] (stPoEnv1 q)
              (.rhsK .vals [.chain (.addr (.base ⟨q + 2⟩)) [] []] [] []
                (.seqn #[]) (stPoEnv1 q)
                (.seq [.seqn #[], .ifThenElse
                    (.lessCmp (.var "j") (.var "m")) (.seqn #[])
                    .breakStmt,
                  stPFillBlock] (stPoEnv1 q) (stPoLoopK q)))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_var (c := u64c ((j : Nat) : Int)) rfl hlkJ1)
  have e19 := po_Z (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q
    ((j : Nat) : Int) ch
  rw [show ((j : Nat) : Int) + 1 = ((j + 1 : Nat) : Int) from by omega,
    unorm_nat_of_lt (by omega : j + 1 < 2 ^ 64)] at e19
  have e20 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.next (.storeK [.chain (.addr (.base ⟨q + 2⟩)) [] []]
        [.int ((j + 1 : Nat) : Int) .uint64] (.seqn #[]) (stPoEnv1 q)
        (.seq [.seqn #[], .ifThenElse
            (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
          stPFillBlock] (stPoEnv1 q) (stPoLoopK q)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (stPoEnv1 q)
            (.seq [.seqn #[], .ifThenElse
                (.lessCmp (.var "j") (.var "m")) (.seqn #[])
                .breakStmt,
              stPFillBlock] (stPoEnv1 q) (stPoLoopK q))),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j + 1 : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) := by
    have hst : storeTarget (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
        (.chain (.addr (.base ⟨q + 2⟩)) [] [])
        (.int ((j + 1 : Nat) : Int) .uint64)
        = .ok (stStx σ (Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨q + 2⟩)
            (u64c (IntKind.normalize .uint64 ((j + 1 : Nat) : Int))))
            (na' + 5)) :=
      storeTarget_addr hlkJ1 (st_norm_u64 _ _)
    rw [unorm_nat_of_lt (by omega : j + 1 < 2 ^ 64)] at hst
    have h := stepFnIter_one (stepFn_store_step (rs := []) (vs := [])
      (body := .seqn #[]) (env := stPoEnv1 q)
      (k := .seq [.seqn #[], .ifThenElse
          (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
        stPFillBlock] (stPoEnv1 q) (stPoLoopK q)) (ch := ch) hst)
    rw [show Heap.set (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨q + 2⟩)
        (u64c ((j + 1 : Nat) : Int)) = (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j + 1 : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) from by
      rw [stF_set_tail (by omega),
        set_append_right (hdT _ (by omega))]
      simp only [List.cons_append, List.nil_append]
      rw [set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_self]] at h
    exact h
  have e21 := po_AB (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j + 1 : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q ch
  have e22 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j + 1 : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.exec (.seqn #[]) (stPoEnv1 q)
        (.seq [.seqn #[], .ifThenElse
            (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
          stPFillBlock] (stPoEnv1 q) (stPoLoopK q))) ch
      = .ok (.next (.seq (#[].toList ++ [.seqn #[], .ifThenElse
            (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
            stPFillBlock]) (stPoEnv1 q) (stPoLoopK q)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j + 1 : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have e23 := mn_G10 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j + 1 : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q ch
  have e24 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j + 1 : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.exec (.seqn #[]) (stPoEnv1 q)
        (.seq [.ifThenElse (.lessCmp (.var "j") (.var "m"))
            (.seqn #[]) .breakStmt, stPFillBlock] (stPoEnv1 q)
          (stPoLoopK q))) ch
      = .ok (.next (.seq (#[].toList ++ [.ifThenElse
            (.lessCmp (.var "j") (.var "m")) (.seqn #[]) .breakStmt,
            stPFillBlock]) (stPoEnv1 q) (stPoLoopK q)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j + 1 : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have e25 := mn_G11 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j + 1 : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q ch
  have hlkJ2 : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j + 1 : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨q + 2⟩)
      = some (u64c ((j + 1 : Nat) : Int)) := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdT _ (by omega))]
    simp only [List.cons_append, List.nil_append]
    rw [lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self]
  have e26 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j + 1 : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.evalE (.var "j") (stPoEnv1 q)
        (.strictK .lessCmp [] [.var "m"] (stPoEnv1 q) (stPoCmpK q))) ch
      = .ok (.retV (.int ((j + 1 : Nat) : Int) .uint64)
            (.strictK .lessCmp [] [.var "m"] (stPoEnv1 q)
              (stPoCmpK q)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j + 1 : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_var (c := u64c ((j + 1 : Nat) : Int)) rfl
      hlkJ2)
  have e27 := mn_G12 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j + 1 : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q
    ((j + 1 : Nat) : Int) ch
  have hlkM2 : Heap.lookup (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j + 1 : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (.base ⟨q⟩)
      = some (u64c ((m : Nat) : Int)) := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdT _ (by omega))]
    simp only [List.cons_append, List.nil_append]
    rw [lookup_cons_self]
  have e28 : stepFnIter 1 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j + 1 : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5))
      (.evalE (.var "m") (stPoEnv1 q)
        (.strictK .lessCmp [.int ((j + 1 : Nat) : Int) .uint64] []
          (stPoEnv1 q) (stPoCmpK q))) ch
      = .ok (.retV (.int ((m : Nat) : Int) .uint64)
            (.strictK .lessCmp [.int ((j + 1 : Nat) : Int) .uint64] []
              (stPoEnv1 q) (stPoCmpK q)),
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j + 1 : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)), ch) :=
    stepFnIter_one (stepFn_var (c := u64c ((m : Nat) : Int)) rfl hlkM2)
  have e29 := mn_G13 (stStx σ (stHp (n : Int) (seed : Int) (k : Int) (sHv b (n - j - 1) c)
      (stPre n seed) ((n : Nat) : Int) (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (j + 1))), (Loc.base ⟨q + 2⟩, u64c ((j + 1 : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na'⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 1⟩, slC (sHv b (n - j) c)), (Loc.base ⟨na' + 2⟩, slC (sHv b (n - j - 1) c)), (Loc.base ⟨na' + 3⟩, u64c ((stFam n seed).getD (n - 1 - j) 0)), (Loc.base ⟨na' + 4⟩, u64c ((stFam n seed).getD (n - 1 - j) 0))])))) (na' + 5)) q
    ((j + 1 : Nat) : Int) ((m : Nat) : Int) ch
  -- assemble the 127 steps
  have hall := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain a1 a2) a3) a4) a5) a6) b1) b2) b3) b4) c1) c2) c3) c4) c5) c6) c7) c8) c9) c10) c11) c12) c13) d1) d2) d3) d4) d5) d6) d7) d8) d9) d10) d11) d12) d13) d14) d15) d16) d17) d18) d19) d20) d21) d22) d23) d24) d25) d26) e1) e2) e3) e4) e5) e6) e7) e8) e9) e10) e11) e12) e13) e14) e15) e16) e17) e18) e19) e20) e21) e22) e23) e24) e25) e26) e27) e28) e29
  rw [show (127 : Nat)
      = 1 + 1 + 3 + 1 + 1 + 1 + 1 + 1 + 3 + 1 + 2 + 1 + 1 + 1 + 5 +
        1 + 3 + 1 + 1 + 3 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 5 + 1 + 5 +
        1 + 1 + 3 + 1 + 1 + 1 + 1 + 1 + 4 + 1 + 1 + 1 + 1 + 1 + 3 +
        1 + 4 + 1 + 1 + 1 + 1 + 1 + 1 + 4 + 1 + 1 + 1 + 1 + 1 + 1 +
        1 + 2 + 7 + 1 + 1 + 4 + 1 + 4 + 1 + 1 + 1 + 1 + 1 + 3 + 1 +
        1 + 1 + 1 from rfl]
  exact hall

/-- **The pop loop**: exactly `127·(m−j)` steps, existentially
packaging the growing dead workspace. -/
theorem po_loop (σ : ExecState) (n seed k m b c q : Nat) (T : Heap)
    (henterPop : ∀ (H : Heap) (a : Nat) (sh : GoValue),
      enterFrame (stStx σ H a) ⟨"pop"⟩ [sh]
        = .ok (popFunc,
            [[("$res1", .base ⟨a + 2⟩), ("$res0", .base ⟨a + 1⟩),
              ("s", .base ⟨a⟩)]],
            [.base ⟨a + 1⟩, .base ⟨a + 2⟩],
            stStx σ
              (Heap.set (Heap.set (Heap.set H (.base ⟨a⟩) (slC sh))
                  (.base ⟨a + 1⟩) (slC nilSl))
                (.base ⟨a + 2⟩) (u64c 0))
              (a + 3)))
    (hcap : n ≤ 8) (hmn : m ≤ n) (hb12 : 12 ≤ b) (hbq : b < q)
    (hq12 : 12 ≤ q) (hnc : n ≤ c)
    (hbT : Heap.lookup T (.base ⟨b⟩)
      = some (backC c (stFam n seed ++ List.replicate (c - n) 0)))
    (hdT : DeadFrom T q) :
    ∀ (d jj na' : Nat) (P : Heap) (ch : Choices), d = m - jj → jj ≤ m →
      q + 4 ≤ na' → DeadFrom P na' →
      ∃ (na'' : Nat) (P' : Heap),
        stepFnIter (127 * (m - jj))
          (stStx σ (stHp (n : Int) (seed : Int) (k : Int)
            (sHv b (n - jj) c) (stPre n seed) ((n : Nat) : Int)
            (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (jj))), (Loc.base ⟨q + 2⟩, u64c ((jj : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ P))) na')
          (.retV (.bool (decide (((jj : Nat) : Int)
            < ((m : Nat) : Int)))) (stPoCmpK q)) ch
        = .ok (.retV (.bool (decide (((m : Nat) : Int)
              < ((m : Nat) : Int)))) (stPoCmpK q),
            stStx σ (stHp (n : Int) (seed : Int) (k : Int)
              (sHv b (n - m) c) (stPre n seed) ((n : Nat) : Int)
              (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed (m))), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ P'))) na'', ch)
        ∧ q + 4 ≤ na'' ∧ DeadFrom P' na'' := by
  intro d
  induction d with
  | zero =>
      intro jj na' P ch hd hjm hqna hdP
      have hjeq : jj = m := by omega
      subst hjeq
      exact ⟨na', P, by rw [Nat.sub_self, Nat.mul_zero]; rfl, hqna, hdP⟩
  | succ d ih =>
      intro jj na' P ch hd hjm hqna hdP
      have hlt : jj < m := by omega
      have hstep := po_iter σ n seed k m jj b c q na' T P ch henterPop
        hcap hlt hmn hb12 hbq hq12 hqna hnc hbT hdT hdP
      rw [show n - jj - 1 = n - (jj + 1) from by omega] at hstep
      have hdP' : DeadFrom (P
          ++ [(Loc.base ⟨na'⟩,
              u64c ((stFam n seed).getD (n - 1 - jj) 0)),
            (Loc.base ⟨na' + 1⟩, slC (sHv b (n - jj) c)),
            (Loc.base ⟨na' + 2⟩, slC (sHv b (n - (jj + 1)) c)),
            (Loc.base ⟨na' + 3⟩,
              u64c ((stFam n seed).getD (n - 1 - jj) 0)),
            (Loc.base ⟨na' + 4⟩,
              u64c ((stFam n seed).getD (n - 1 - jj) 0))])
          (na' + 5) := by
        intro x hx
        rw [lookup_append_right (hdP x (by omega)),
          lookup_cons_ne (base_beq_false (by omega)),
          lookup_cons_ne (base_beq_false (by omega)),
          lookup_cons_ne (base_beq_false (by omega)),
          lookup_cons_ne (base_beq_false (by omega)),
          lookup_cons_ne (base_beq_false (by omega))]
        rfl
      obtain ⟨na'', P', hrest, hqna'', hdP''⟩ :=
        ih (jj + 1) (na' + 5) _ ch (by omega) (by omega) (by omega)
          hdP'
      refine ⟨na'', P', ?_, hqna'', hdP''⟩
      rw [show (decide (((jj : Nat) : Int) < ((m : Nat) : Int)))
          = true from decide_eq_true (by exact_mod_cast hlt)]
      have hchain := stepFnIter_chain hstep hrest
      rw [show 127 + 127 * (m - (jj + 1)) = 127 * (m - jj) from by
        rw [show m - jj = (m - (jj + 1)) + 1 from by omega,
          Nat.mul_succ]
        omega] at hchain
      exact hchain

/-- Front epilogue set helpers (cells 3/4/5, in place). -/
theorem stF_set3 {nv sv kv : Int} {r3 r3' r4 : List Int} {r5 : Int}
    {sh : GoValue} {pl : List Int} {iv : Int} {ff : Bool} :
    Heap.set (stF nv sv kv r3 r4 r5 sh pl iv ff) (.base ⟨3⟩)
        (arrC 8 r3')
      = stF nv sv kv r3' r4 r5 sh pl iv ff := by
  simp [stF, Heap.set]

theorem stF_set4 {nv sv kv : Int} {r3 r4 r4' : List Int} {r5 : Int}
    {sh : GoValue} {pl : List Int} {iv : Int} {ff : Bool} :
    Heap.set (stF nv sv kv r3 r4 r5 sh pl iv ff) (.base ⟨4⟩)
        (arrC 8 r4')
      = stF nv sv kv r3 r4' r5 sh pl iv ff := by
  simp [stF, Heap.set]

theorem stF_set5 {nv sv kv : Int} {r3 r4 : List Int} {r5 r5' : Int}
    {sh : GoValue} {pl : List Int} {iv : Int} {ff : Bool} :
    Heap.set (stF nv sv kv r3 r4 r5 sh pl iv ff) (.base ⟨5⟩)
        (u64c r5')
      = stF nv sv kv r3 r4 r5' sh pl iv ff := by
  simp [stF, Heap.set]

theorem stF_lookup3 {nv sv kv : Int} {r3 r4 : List Int} {r5 : Int}
    {sh : GoValue} {pl : List Int} {iv : Int} {ff : Bool} {T : Heap} :
    Heap.lookup (stF nv sv kv r3 r4 r5 sh pl iv ff ++ T) (.base ⟨3⟩)
      = some (arrC 8 r3) := by
  simp [stF, Heap.lookup]

theorem stF_lookup4 {nv sv kv : Int} {r3 r4 : List Int} {r5 : Int}
    {sh : GoValue} {pl : List Int} {iv : Int} {ff : Bool} {T : Heap} :
    Heap.lookup (stF nv sv kv r3 r4 r5 sh pl iv ff ++ T) (.base ⟨4⟩)
      = some (arrC 8 r4) := by
  simp [stF, Heap.lookup]

theorem stF_lookup5 {nv sv kv : Int} {r3 r4 : List Int} {r5 : Int}
    {sh : GoValue} {pl : List Int} {iv : Int} {ff : Bool} {T : Heap} :
    Heap.lookup (stF nv sv kv r3 r4 r5 sh pl iv ff ++ T) (.base ⟨5⟩)
      = some (u64c r5) := by
  simp [stF, Heap.lookup]

/-- **The exit phase** (72 steps): pop-loop exit → `$c8 := size(s)` →
the three result-cell stores → the entry frame's terminal. -/
theorem st_exit (σ : ExecState) (n seed k m b c q na'' : Nat)
    (T P : Heap) (ch : Choices)
    (henterSize : ∀ (H : Heap) (a : Nat) (sh : GoValue),
      enterFrame (stStx σ H a) ⟨"size"⟩ [sh]
        = .ok (sizeFunc,
            [[("$res0", .base ⟨a + 1⟩), ("s", .base ⟨a⟩)]],
            [.base ⟨a + 1⟩],
            stStx σ
              (Heap.set (Heap.set H (.base ⟨a⟩) (slC sh))
                (.base ⟨a + 1⟩) (u64c 0))
              (a + 2)))
    (hcap : n ≤ 8) (hmn : m ≤ n) (hnc : n ≤ c) (hq12 : 12 ≤ q)
    (hqna : q + 4 ≤ na'') (hdT : DeadFrom T q) (hdP : DeadFrom P na'') :
    stepFnIter 72
      (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P)))) (na''))
      (.retV (.bool false) (stPoCmpK q)) ch
      = .ok (.next .stop,
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) ((n - m : Nat) : Int) (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)),
          ch) := by
  have hnm64 : n - m < 2 ^ 64 := by omega
  -- x1: break-unwind to the `$c8` seqn (7 raw steps)
  have x1 : stepFnIter 7 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P)))) (na''))
      (.retV (.bool false) (stPoCmpK q)) ch
      = .ok (.exec stS9 ([stTopP q, stBase])
            (.seq [stS10] ([stTopP q, stBase]) stStop),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P)))) (na'')), ch) := by
    with_unfolding_all rfl
  have x2 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P)))) (na''))
      (.exec stS9 ([stTopP q, stBase])
        (.seq [stS10] ([stTopP q, stBase]) stStop)) ch
      = .ok (.next (.seq (#[Stmt.initialization
            { id := "$c8", typ := tU64 },
            Stmt.call #[.var "$c8"] ⟨"size"⟩ #[.var "s"]].toList
            ++ [stS10]) ([stTopP q, stBase]) stStop),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P)))) (na'')), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have x3 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P)))) (na''))
      (.next (.seq [.initialization { id := "$c8", typ := tU64 },
        .call #[.var "$c8"] ⟨"size"⟩ #[.var "s"], stS10]
        ([stTopP q, stBase]) stStop)) ch
      = .ok (.exec (.initialization { id := "$c8", typ := tU64 })
          ([stTopP q, stBase])
          (.seq [.call #[.var "$c8"] ⟨"size"⟩ #[.var "s"], stS10]
            ([stTopP q, stBase]) stStop),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P)))) (na'')), ch) :=
    stepFnIter_one (stepFn_seq_pop)
  have x4 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P)))) (na''))
      (.exec (.initialization { id := "$c8", typ := tU64 })
        ([stTopP q, stBase])
        (.seq [.call #[.var "$c8"] ⟨"size"⟩ #[.var "s"], stS10]
          ([stTopP q, stBase]) stStop)) ch
      = .ok (.next (.seq [.call #[.var "$c8"] ⟨"size"⟩ #[.var "s"],
            stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0)])))) (na'' + 1)), ch) := by
    have h := stepFn_init_seq (σ := (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P)))) (na'')))
      (p := { id := "$c8", typ := tU64 })
      (rest := [.call #[.var "$c8"] ⟨"size"⟩ #[.var "s"], stS10])
      (env := [stTopP q, stBase]) (k := stStop) (ch := ch)
      (v := .int 0 .uint64)
      (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
    dsimp only at h
    rw [show Heap.set (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P)))) (.base ⟨na''⟩)
        ⟨some tU64, .int 0 .uint64⟩ = (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0)])))) from by
      rw [stF_set_tail (by omega),
        set_append_right (hdT _ (by omega))]
      simp only [List.cons_append, List.nil_append]
      rw [set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_fresh (hdP _ (by omega))]] at h
    exact stepFnIter_one h
  have x5 : stepFnIter 3 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0)])))) (na'' + 1))
      (.next (.seq [.call #[.var "$c8"] ⟨"size"⟩ #[.var "s"], stS10]
        ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)) ch
      = .ok (.retV (sHv b (n - m) c)
            (.callArgsK ⟨"size"⟩ [(.chain [], [.ref "$c8"])] [] []
              ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0)])))) (na'' + 1)), ch) := by
    with_unfolding_all rfl
  have hent := henterSize (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0)])))) (na'' + 1) (sHv b (n - m) c)
  rw [show na'' + 1 + 1 = na'' + 2 from rfl] at hent
  rw [show Heap.set (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0)])))) (.base ⟨na'' + 1⟩)
      (slC (sHv b (n - m) c)) = (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c))])))) from by
    rw [stF_set_tail (by omega),
      set_append_right (hdT _ (by omega))]
    simp only [List.cons_append, List.nil_append]
    rw [set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
      set_append_right (hdP _ (by omega)),
      set_cons_ne (base_beq_false (by omega)),
      set_fresh (by rfl)]
    simp] at hent
  rw [show Heap.set (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c))])))) (.base ⟨na'' + 2⟩)
      (u64c 0) = (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c 0)])))) from by
    rw [stF_set_tail (by omega),
      set_append_right (hdT _ (by omega))]
    simp only [List.cons_append, List.nil_append]
    rw [set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
      set_append_right (hdP _ (by omega)),
      set_cons_ne (base_beq_false (by omega)),
      set_cons_ne (base_beq_false (by omega)),
      set_fresh (by rfl)]
    simp] at hent
  have x6 := stepFnIter_one (stepFn_call_enter
    (plans := [(.chain [], [.ref "$c8"])]) (env := ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]))
    (k := .seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) (vals := []) (v := (sHv b (n - m) c))
    (ch := ch) hent)
  have x7 : stepFnIter 2 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c 0)])))) (na'' + 3))
      (.exec sizeFunc.body ([[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]) (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false)) ch
      = .ok (.exec (.seqn #[.assign (.var "$res0") (.convert tU64 (.length (.var "s") (some sliceU))), .returnStmt]) ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
            (.seq [] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]) (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false)),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c 0)])))) (na'' + 3)), ch) := by
    with_unfolding_all rfl
  have x8 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c 0)])))) (na'' + 3))
      (.exec (.seqn #[.assign (.var "$res0") (.convert tU64 (.length (.var "s") (some sliceU))), .returnStmt]) ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
        (.seq [] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]) (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false))) ch
      = .ok (.next (.seq (#[.assign (.var "$res0") (.convert tU64 (.length (.var "s") (some sliceU))),
            Stmt.returnStmt].toList ++ []) ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]) (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false)),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c 0)])))) (na'' + 3)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have x9 : stepFnIter 6 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c 0)])))) (na'' + 3))
      (.next (.seq [.assign (.var "$res0") (.convert tU64 (.length (.var "s") (some sliceU))), .returnStmt] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]) (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false))) ch
      = .ok (.evalE (.var "s") ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
            (.strictK (.lengthOf (some sliceU)) [] [] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
              (.strictK (.convert tU64) [] [] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
                (.rhsK .vals
                  [.chain (.addr (.base ⟨na'' + 2⟩)) [] []] [] []
                  (.seqn #[]) ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
                  (.seq [.returnStmt] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]) (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false))))),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c 0)])))) (na'' + 3)), ch) := by
    with_unfolding_all rfl
  have hlkSz : Heap.lookup (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c 0)])))) (.base ⟨na'' + 1⟩)
      = some (slC (sHv b (n - m) c)) := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdT _ (by omega))]
    simp only [List.cons_append, List.nil_append]
    rw [lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
      lookup_append_right (hdP _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self]
  have x10 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c 0)])))) (na'' + 3))
      (.evalE (.var "s") ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
        (.strictK (.lengthOf (some sliceU)) [] [] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
          (.strictK (.convert tU64) [] [] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
            (.rhsK .vals [.chain (.addr (.base ⟨na'' + 2⟩)) [] []] [] []
              (.seqn #[]) ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
              (.seq [.returnStmt] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]) (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false)))))) ch
      = .ok (.retV (slC (sHv b (n - m) c)).value
            (.strictK (.lengthOf (some sliceU)) [] [] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
              (.strictK (.convert tU64) [] [] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
                (.rhsK .vals [.chain (.addr (.base ⟨na'' + 2⟩)) [] []]
                  [] [] (.seqn #[]) ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
                  (.seq [.returnStmt] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]) (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false))))),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c 0)])))) (na'' + 3)), ch) :=
    stepFnIter_one (stepFn_var rfl hlkSz)
  have x11 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c 0)])))) (na'' + 3))
      (.retV (slC (sHv b (n - m) c)).value
        (.strictK (.lengthOf (some sliceU)) [] [] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
          (.strictK (.convert tU64) [] [] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
            (.rhsK .vals [.chain (.addr (.base ⟨na'' + 2⟩)) [] []] [] []
              (.seqn #[]) ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
              (.seq [.returnStmt] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]) (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false)))))) ch
      = .ok (.retV (.int ((n - m : Nat) : Int) .int)
            (.strictK (.convert tU64) [] [] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
              (.rhsK .vals [.chain (.addr (.base ⟨na'' + 2⟩)) [] []]
                [] [] (.seqn #[]) ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
                (.seq [.returnStmt] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]) (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false)))),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c 0)])))) (na'' + 3)), ch) :=
    stepFnIter_one (stepFn_strict_apply (done := [])
      (applyStrictOp_len_slice (b := .base ⟨b⟩) (off := 0)
        (len := n - m) (cap := c) (elem := tU64) (by omega)))
  have x12 : stepFnIter 2 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c 0)])))) (na'' + 3))
      (.retV (.int ((n - m : Nat) : Int) .int)
        (.strictK (.convert tU64) [] [] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
          (.rhsK .vals [.chain (.addr (.base ⟨na'' + 2⟩)) [] []] [] []
            (.seqn #[]) ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
            (.seq [.returnStmt] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]) (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false))))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na'' + 2⟩)) [] []]
            [.int (IntKind.normalize .uint64 ((n - m : Nat) : Int))
              .uint64] (.seqn #[]) ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
            (.seq [.returnStmt] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]) (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false))),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c 0)])))) (na'' + 3)), ch) := by
    with_unfolding_all rfl
  rw [unorm_nat_of_lt hnm64] at x12
  have hlkRz : Heap.lookup (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c 0)])))) (.base ⟨na'' + 2⟩)
      = some (u64c 0) := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdT _ (by omega))]
    simp only [List.cons_append, List.nil_append]
    rw [lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
      lookup_append_right (hdP _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self]
  have x13 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c 0)])))) (na'' + 3))
      (.next (.storeK [.chain (.addr (.base ⟨na'' + 2⟩)) [] []]
        [.int ((n - m : Nat) : Int) .uint64] (.seqn #[]) ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
        (.seq [.returnStmt] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]) (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
            (.seq [.returnStmt] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]) (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false))),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
    have hst : storeTarget (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c 0)])))) (na'' + 3))
        (.chain (.addr (.base ⟨na'' + 2⟩)) [] []) (.int ((n - m : Nat) : Int) .uint64)
        = .ok (stStx σ (Heap.set (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c 0)]))))
            (.base ⟨na'' + 2⟩)
            (u64c (IntKind.normalize .uint64 ((n - m : Nat) : Int)))) (na'' + 3)) :=
      storeTarget_addr hlkRz (st_norm_u64 _ _)
    rw [unorm_nat_of_lt hnm64] at hst
    have h := stepFnIter_one (stepFn_store_step (rs := []) (vs := [])
      (body := .seqn #[]) (env := ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]))
      (k := .seq [.returnStmt] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]) (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false)) (ch := ch) hst)
    rw [show Heap.set (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c 0)])))) (.base ⟨na'' + 2⟩)
        (u64c ((n - m : Nat) : Int)) = (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) from by
      rw [stF_set_tail (by omega),
        set_append_right (hdT _ (by omega))]
      simp only [List.cons_append, List.nil_append]
      rw [set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_append_right (hdP _ (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_self]] at h
    exact h
  have x14 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.next (.storeK [] [] (.seqn #[]) ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
        (.seq [.returnStmt] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]) (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false)))) ch
      = .ok (.exec (.seqn #[]) ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
            (.seq [.returnStmt] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]) (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false)),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
    with_unfolding_all rfl
  have x15 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.exec (.seqn #[]) ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
        (.seq [.returnStmt] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]) (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false))) ch
      = .ok (.next (.seq (#[].toList ++ [.returnStmt]) ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]])
            (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false)),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have x16 : stepFnIter 3 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.next (.seq [.returnStmt] ([] :: [[("$res0", Loc.base ⟨na'' + 2⟩), ("s", Loc.base ⟨na'' + 1⟩)]]) (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false))) ch
      = .ok (.returning (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
    with_unfolding_all rfl
  have hlkRv : Heap.lookup (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (.base ⟨na'' + 2⟩)
      = some (u64c ((n - m : Nat) : Int)) := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdT _ (by omega))]
    simp only [List.cons_append, List.nil_append]
    rw [lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
      lookup_append_right (hdP _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self]
  have x17 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.returning (.frame [(.chain [], [.ref "$c8"])] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) [Loc.base ⟨na'' + 2⟩] [] (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) false)) ch
      = .ok (.evalE (.ref "$c8") ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
            (.tgtOpK (.chain []) [] [] [] [] .vals []
              [(u64c ((n - m : Nat) : Int)).value] (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
              (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) :=
    stepFnIter_one (stepFn_return_frame (st_loadMany1 hlkRv))
  have x18 : stepFnIter 2 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.evalE (.ref "$c8") ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
        (.tgtOpK (.chain []) [] [] [] [] .vals []
          [.int ((n - m : Nat) : Int) .uint64] (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
          (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na''⟩)) [] []]
            [.int ((n - m : Nat) : Int) .uint64] (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
            (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
    with_unfolding_all rfl
  have hlkC8 : Heap.lookup (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (.base ⟨na''⟩)
      = some (u64c 0) := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdT _ (by omega))]
    simp only [List.cons_append, List.nil_append]
    rw [lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
      lookup_append_right (hdP _ (by omega)),
      lookup_cons_self]
  have x19 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.next (.storeK [.chain (.addr (.base ⟨na''⟩)) [] []]
        [.int ((n - m : Nat) : Int) .uint64] (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
        (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
            (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
    have hst : storeTarget (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
        (.chain (.addr (.base ⟨na''⟩)) [] []) (.int ((n - m : Nat) : Int) .uint64)
        = .ok (stStx σ (Heap.set (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (.base ⟨na''⟩)
            (u64c (IntKind.normalize .uint64 ((n - m : Nat) : Int)))) (na'' + 3)) :=
      storeTarget_addr hlkC8 (st_norm_u64 _ _)
    rw [unorm_nat_of_lt hnm64] at hst
    have h := stepFnIter_one (stepFn_store_step (rs := []) (vs := [])
      (body := .seqn #[]) (env := ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]))
      (k := .seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) (ch := ch) hst)
    rw [show Heap.set (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c 0), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (.base ⟨na''⟩)
        (u64c ((n - m : Nat) : Int)) = (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) from by
      rw [stF_set_tail (by omega),
        set_append_right (hdT _ (by omega))]
      simp only [List.cons_append, List.nil_append]
      rw [set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_cons_ne (base_beq_false (by omega)),
        set_append_right (hdP _ (by omega)),
        set_cons_self]] at h
    exact h
  -- the epilogue: `$res0 = pushed; $res1 = popped; $res2 = $c8; return`
  have x20 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.next (.storeK [] [] (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
        (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop))) ch
      = .ok (.exec (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
            (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
    with_unfolding_all rfl
  have x21 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.exec (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)) ch
      = .ok (.next (.seq (#[].toList ++ [stS10]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have x22 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.next (.seq [stS10] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)) ch
      = .ok (.exec stS10 ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) (.seq [] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) :=
    stepFnIter_one (stepFn_seq_pop)
  have x23 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.exec stS10 ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) (.seq [] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)) ch
      = .ok (.next (.seq (#[Stmt.assign (.var "$res0") (.var "pushed"),
            Stmt.assign (.var "$res1") (.var "popped"),
            Stmt.assign (.var "$res2") (.var "$c8"),
            Stmt.returnStmt].toList ++ []) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) :=
    stepFnIter_one (stepFn_seqn_splice)
  have x24 : stepFnIter 6 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.next (.seq [.assign (.var "$res0") (.var "pushed"),
        .assign (.var "$res1") (.var "popped"),
        .assign (.var "$res2") (.var "$c8"), .returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
        stStop)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨3⟩)) [] []]
            [.array ⟨(stPre n seed).map (fun v => .int v .uint64)⟩]
            (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
            (.seq [.assign (.var "$res1") (.var "popped"),
              .assign (.var "$res2") (.var "$c8"), .returnStmt]
              ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
    with_unfolding_all rfl
  have x25 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.next (.storeK [.chain (.addr (.base ⟨3⟩)) [] []]
        [.array ⟨(stPre n seed).map (fun v => .int v .uint64)⟩]
        (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
        (.seq [.assign (.var "$res1") (.var "popped"),
          .assign (.var "$res2") (.var "$c8"), .returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
          stStop))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
            (.seq [.assign (.var "$res1") (.var "popped"),
              .assign (.var "$res2") (.var "$c8"), .returnStmt]
              ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
    have hst : storeTarget (stStx σ (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
        (.chain (.addr (.base ⟨3⟩)) [] [])
        (.array ⟨(stPre n seed).map (fun v => .int v .uint64)⟩)
        = .ok (stStx σ (Heap.set (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (.base ⟨3⟩)
            (arrC 8 (stPre n seed))) (na'' + 3)) :=
      storeTarget_addr stF_lookup3
        (normalizeValueForTy_arr_u64 (stPre_length (by omega))
          stPre_range)
    have h := stepFnIter_one (stepFn_store_step (rs := []) (vs := [])
      (body := .seqn #[]) (env := ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]))
      (k := .seq [.assign (.var "$res1") (.var "popped"),
        .assign (.var "$res2") (.var "$c8"), .returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
        stStop) (ch := ch) hst)
    rw [show Heap.set (stF (n : Int) (seed : Int) (k : Int) zeros8 zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (.base ⟨3⟩)
        (arrC 8 (stPre n seed))
        = (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) from by
      rw [set_append_left stF_only_lookup3, stF_set3]] at h
    exact h
  have x26 : stepFnIter 2 (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.next (.storeK [] [] (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) (.seq [.assign (.var "$res1") (.var "popped"), .assign (.var "$res2") (.var "$c8"), .returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop))) ch
      = .ok (.next (.seq (#[].toList
            ++ [.assign (.var "$res1") (.var "popped"),
              .assign (.var "$res2") (.var "$c8"), .returnStmt])
            ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
    have h1 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
        (.next (.storeK [] [] (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) (.seq [.assign (.var "$res1") (.var "popped"), .assign (.var "$res2") (.var "$c8"), .returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop))) ch
        = .ok (.exec (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) (.seq [.assign (.var "$res1") (.var "popped"), .assign (.var "$res2") (.var "$c8"), .returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop),
            (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain h1 (stepFnIter_one (stepFn_seqn_splice))
  have x27 : stepFnIter 4 (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.next (.seq [.assign (.var "$res1") (.var "popped"),
        .assign (.var "$res2") (.var "$c8"), .returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
        stStop)) ch
      = .ok (.evalE (.var "popped") ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
            (.rhsK .vals [.chain (.addr (.base ⟨4⟩)) [] []] [] []
              (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
    with_unfolding_all rfl
  have hlkPopA : Heap.lookup (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (.base ⟨q + 1⟩)
      = some (arrC 8 (stPopPre n seed m)) := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdT _ (by omega))]
    simp only [List.cons_append, List.nil_append]
    rw [lookup_cons_ne (base_beq_false (by omega)),
      lookup_cons_self]
  have x28 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.evalE (.var "popped") ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
        (.rhsK .vals [.chain (.addr (.base ⟨4⟩)) [] []] [] []
          (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop))) ch
      = .ok (.retV (arrC 8 (stPopPre n seed m)).value
            (.rhsK .vals [.chain (.addr (.base ⟨4⟩)) [] []] [] []
              (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) :=
    stepFnIter_one (stepFn_var rfl hlkPopA)
  have x29 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.retV (arrC 8 (stPopPre n seed m)).value
        (.rhsK .vals [.chain (.addr (.base ⟨4⟩)) [] []] [] []
          (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨4⟩)) [] []]
            [(arrC 8 (stPopPre n seed m)).value] (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
            (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
    with_unfolding_all rfl
  have x30 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.next (.storeK [.chain (.addr (.base ⟨4⟩)) [] []]
        [.array ⟨(stPopPre n seed m).map (fun v => .int v .uint64)⟩]
        (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
    have hst : storeTarget (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
        (.chain (.addr (.base ⟨4⟩)) [] [])
        (.array ⟨(stPopPre n seed m).map (fun v => .int v .uint64)⟩)
        = .ok (stStx σ (Heap.set (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (.base ⟨4⟩)
            (arrC 8 (stPopPre n seed m))) (na'' + 3)) :=
      storeTarget_addr stF_lookup4
        (normalizeValueForTy_arr_u64 (stPopPre_length (by omega))
          stPopPre_range)
    have h := stepFnIter_one (stepFn_store_step (rs := []) (vs := [])
      (body := .seqn #[]) (env := ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])) (k := (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)) (ch := ch) hst)
    rw [show Heap.set (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) zeros8 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (.base ⟨4⟩)
        (arrC 8 (stPopPre n seed m)) = (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) from by
      rw [set_append_left stF_only_lookup4, stF_set4]] at h
    exact h
  have x31 : stepFnIter 2 (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.next (.storeK [] [] (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop))) ch
      = .ok (.next (.seq (#[].toList
            ++ [.assign (.var "$res2") (.var "$c8"), .returnStmt])
            ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
    have h1 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
        (.next (.storeK [] [] (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop))) ch
        = .ok (.exec (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop),
            (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain h1 (stepFnIter_one (stepFn_seqn_splice))
  have x32 : stepFnIter 4 (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.next (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt]
        ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)) ch
      = .ok (.evalE (.var "$c8") ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
            (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
              (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
              (.seq [.returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
    with_unfolding_all rfl
  have hlkC8v : Heap.lookup (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (.base ⟨na''⟩)
      = some (u64c ((n - m : Nat) : Int)) := by
    rw [stF_lookup_tail (by omega),
      lookup_append_right (hdT _ (by omega))]
    simp only [List.cons_append, List.nil_append]
    rw [lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
        lookup_cons_ne (base_beq_false (by omega)),
      lookup_append_right (hdP _ (by omega)),
      lookup_cons_self]
  have x33 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.evalE (.var "$c8") ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
        (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
          (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
          (.seq [.returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop))) ch
      = .ok (.retV (.int ((n - m : Nat) : Int) .uint64)
            (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
              (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
              (.seq [.returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) :=
    stepFnIter_one (stepFn_var (c := u64c ((n - m : Nat) : Int)) rfl hlkC8v)
  have x34 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.retV (.int ((n - m : Nat) : Int) .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
          (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
          (.seq [.returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨5⟩)) [] []]
            [.int ((n - m : Nat) : Int) .uint64] (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
            (.seq [.returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
    with_unfolding_all rfl
  have x35 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.next (.storeK [.chain (.addr (.base ⟨5⟩)) [] []]
        [.int ((n - m : Nat) : Int) .uint64] (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
        (.seq [.returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
            (.seq [.returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)),
          (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) ((n - m : Nat) : Int) (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
    have hst : storeTarget (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
        (.chain (.addr (.base ⟨5⟩)) [] []) (.int ((n - m : Nat) : Int) .uint64)
        = .ok (stStx σ (Heap.set (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (.base ⟨5⟩)
            (u64c (IntKind.normalize .uint64 ((n - m : Nat) : Int)))) (na'' + 3)) :=
      storeTarget_addr stF_lookup5 (st_norm_u64 _ _)
    rw [unorm_nat_of_lt hnm64] at hst
    have h := stepFnIter_one (stepFn_store_step (rs := []) (vs := [])
      (body := .seqn #[]) (env := ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]))
      (k := .seq [.returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop) (ch := ch) hst)
    rw [show Heap.set (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) 0 (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (.base ⟨5⟩)
        (u64c ((n - m : Nat) : Int)) = (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) ((n - m : Nat) : Int) (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) from by
      rw [set_append_left stF_only_lookup5, stF_set5]] at h
    exact h
  have x36 : stepFnIter 6 (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) ((n - m : Nat) : Int) (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
      (.next (.storeK [] [] (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
        (.seq [.returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop))) ch
      = .ok (.next .stop, (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) ((n - m : Nat) : Int) (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
    have h1 : stepFnIter 1 (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) ((n - m : Nat) : Int) (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
        (.next (.storeK [] [] (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
          (.seq [.returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop))) ch
        = .ok (.exec (.seqn #[]) ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])
              (.seq [.returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop),
            (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) ((n - m : Nat) : Int) (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
      with_unfolding_all rfl
    have h2 := stepFnIter_one (stepFn_seqn_splice
      (σ := (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) ((n - m : Nat) : Int) (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))) (ss := #[])
      (env := ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase])) (rest := [.returnStmt]) (k := stStop) (ch := ch))
    have h3 : stepFnIter 4 (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) ((n - m : Nat) : Int) (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3))
        (.next (.seq [.returnStmt] ([("$c8", Loc.base ⟨na''⟩) :: stTopP q, stBase]) stStop)) ch
        = .ok (.next .stop, (stStx σ (stF (n : Int) (seed : Int) (k : Int) (stPre n seed) (stPopPre n seed m) ((n - m : Nat) : Int) (sHv b (n - m) c)
      (stPre n seed) ((n : Nat) : Int) false ++ (T ++ ([(Loc.base ⟨q⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 1⟩, arrC 8 (stPopPre n seed m)), (Loc.base ⟨q + 2⟩, u64c ((m : Nat) : Int)), (Loc.base ⟨q + 3⟩, bcell false)] ++ (P ++ [(Loc.base ⟨na''⟩, u64c ((n - m : Nat) : Int)), (Loc.base ⟨na'' + 1⟩, slC (sHv b (n - m) c)), (Loc.base ⟨na'' + 2⟩, u64c ((n - m : Nat) : Int))])))) (na'' + 3)), ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain (stepFnIter_chain h1 h2) h3
  have hall := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain
      x1 x2) x3) x4) x5) x6) x7) x8) x9) x10) x11) x12) x13) x14) x15)
      x16) x17) x18) x19) x20) x21) x22) x23) x24) x25) x26) x27) x28)
      x29) x30) x31) x32) x33) x34) x35) x36
  rw [show (72 : Nat)
      = 7 + 1 + 1 + 1 + 3 + 1 + 2 + 1 + 6 + 1 + 1 + 2 + 1 + 1 + 1 + 3
        + 1 + 2 + 1 + 1 + 1 + 1 + 1 + 6 + 1 + 2 + 4 + 1 + 1 + 1 + 2
        + 4 + 1 + 1 + 1 + 6 from rfl]
  exact hall

/-! ## The run, end to end -/

/-- The final-state readback: the three result cells, generic over the
tail. -/
theorem st_readback (σ : ExecState) (nv sv kv r5 : Int)
    (r3 r4 : List Int) (sh : GoValue) (pl : List Int) (iv : Int)
    (ff : Bool) (Tf : Heap) (naf : Nat) :
    loadMany (stStx σ (stF nv sv kv r3 r4 r5 sh pl iv ff ++ Tf) naf)
      [.base ⟨3⟩, .base ⟨4⟩, .base ⟨5⟩]
      = .ok [.array ⟨r3.map (fun v => .int v .uint64)⟩,
             .array ⟨r4.map (fun v => .int v .uint64)⟩,
             .int r5 .uint64] := by
  with_unfolding_all rfl

/-- **The harness run**: exactly `242 + 130·n + 127·min(k,n) + 12·[n<k]`
steps from the machine entry's post-prelude seed to the driver
terminal, at EVERY choice stream — the count is choice-invariant even
though the heap layout is not (the existential backing
address/capacity, final tail, allocation front and leftover stream
carry the choice-dependence). -/
theorem st_run (n seed k : Nat) (hcap : n ≤ 8) (_hseed : seed < 2 ^ 64)
    (hk : k < 2 ^ 64) (ch : Choices) :
    ∃ (bf cf naf : Nat) (Tf : Heap) (ch' : Choices),
      stepFnIter (242 + 130 * n + 127 * min k n
          + (if n < k then 12 else 0))
        (stStx stProg
          [(.base ⟨0⟩, u64c (n : Int)), (.base ⟨1⟩, u64c (seed : Int)),
           (.base ⟨2⟩, u64c (k : Int)), (.base ⟨3⟩, arrC 8 zeros8),
           (.base ⟨4⟩, arrC 8 zeros8), (.base ⟨5⟩, u64c 0)] 6)
        (.exec stackHarnessRFunc.body [stBase] stStop) ch
      = .ok (.next .stop,
          stStx stProg
            (stF (n : Int) (seed : Int) (k : Int) (stPre n seed)
              (stPopPre n seed (min k n)) ((n - min k n : Nat) : Int)
              (sHv bf (n - min k n) cf)
              (stPre n seed) ((n : Nat) : Int) false ++ Tf) naf,
          ch') := by
  have hE := st_entry stProg (n : Int) (seed : Int) (k : Int) ch
  rw [show ((0 : Int)) = ((0 : Nat) : Int) from rfl] at hE
  rw [show (stHp (n : Int) (seed : Int) (k : Int) (sHv 7 0 0) zeros8
      ((0 : Nat) : Int) ([] : Heap))
      = stHp (n : Int) (seed : Int) (k : Int) (sHv 7 0 0)
          (stPre 0 seed) ((0 : Nat) : Int) ([] : Heap) from by
    rw [stPre_zero]] at hE
  -- the push loop from the freshly established invariant
  obtain ⟨b', c', na', T', ch1, hPush, hnc', hbi', hna12', hdead'⟩ :=
    pu_loop stProg n seed k st_enter_push hcap n 0 7 0 12 ([] : Heap)
      ch rfl (by omega) (by omega) (Or.inl ⟨rfl, rfl⟩) (by omega)
      (fun x _ => rfl)
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hPush
  have hEP := stepFnIter_chain hE hPush
  -- the min phase
  have hMin := mn_phase stProg n seed k b' c' na' T' ch1 hna12' hcap hk
    hdead'
  have hEPM := stepFnIter_chain hEP hMin
  -- bridge the min-phase tail into the pop-loop shape
  rw [show (stM na' ((min k n : Nat) : Int) zeros8 0 false : Heap)
      = [(Loc.base ⟨na'⟩, u64c ((min k n : Nat) : Int)),
         (Loc.base ⟨na' + 1⟩, arrC 8 (stPopPre n seed 0)),
         (Loc.base ⟨na' + 2⟩, u64c ((0 : Nat) : Int)),
         (Loc.base ⟨na' + 3⟩, bcell false)]
        ++ ([] : Heap) from by
    rw [stM, stPopPre_zero]
    simp] at hEPM
  rw [show (T' ++ ([(Loc.base ⟨na'⟩, u64c ((min k n : Nat) : Int)),
        (Loc.base ⟨na' + 1⟩, arrC 8 (stPopPre n seed 0)),
        (Loc.base ⟨na' + 2⟩, u64c ((0 : Nat) : Int)),
        (Loc.base ⟨na' + 3⟩, bcell false)]
        ++ ([] : Heap)) : Heap)
      = T' ++ ([(Loc.base ⟨na'⟩, u64c ((min k n : Nat) : Int)),
        (Loc.base ⟨na' + 1⟩, arrC 8 (stPopPre n seed 0)),
        (Loc.base ⟨na' + 2⟩, u64c ((0 : Nat) : Int)),
        (Loc.base ⟨na' + 3⟩, bcell false)]
        ++ ([] : Heap)) from rfl] at hEPM
  -- the pop loop (or nothing, when the stack was never pushed)
  rcases hbi' with ⟨hb7, hc0⟩ | ⟨hb12', hbna', hbT'⟩
  · -- the backing is still the front's cap-0 cell ⇒ `n = 0`, no pops
    have hn0 : n = 0 := by omega
    have hm0 : min k n = 0 := by omega
    rw [show (decide ((0 : Int) < ((min k n : Nat) : Int))) = false from
      decide_eq_false (by rw [hm0]; omega)] at hEPM
    have hX := st_exit stProg n seed k (min k n) b' c' na' (na' + 4)
      T' ([] : Heap) ch1 st_enter_size hcap (by omega) (by omega)
      hna12' (by omega) hdead' (fun x _ => rfl)
    rw [show (stPopPre n seed (min k n)) = stPopPre n seed 0 from by
      rw [hm0]] at hX
    rw [show n - min k n = n from by omega] at hX
    rw [show ((min k n : Nat) : Int) = ((0 : Nat) : Int) from by
      rw [hm0]] at hEPM
    rw [show ((min k n : Nat) : Int) = ((0 : Nat) : Int) from by
      rw [hm0]] at hX
    have hFull := stepFnIter_chain hEPM hX
    refine ⟨b', c', na' + 4 + 3,
      T' ++ ([(Loc.base ⟨na'⟩, u64c ((0 : Nat) : Int)),
        (Loc.base ⟨na' + 1⟩, arrC 8 (stPopPre n seed 0)),
        (Loc.base ⟨na' + 2⟩, u64c ((0 : Nat) : Int)),
        (Loc.base ⟨na' + 3⟩, bcell false)]
        ++ (([] : Heap)
          ++ [(Loc.base ⟨na' + 4⟩,
              u64c ((n - min k n : Nat) : Int)),
            (Loc.base ⟨na' + 4 + 1⟩, slC (sHv b' (n - min k n) c')),
            (Loc.base ⟨na' + 4 + 2⟩,
              u64c ((n - min k n : Nat) : Int))])), ch1, ?_⟩
    rw [show 242 + 130 * n + 127 * min k n + (if n < k then 12 else 0)
        = 84 + 130 * (n - 0) + (86 + (if n < k then 12 else 0)) + 72
        from by
      by_cases hnk2 : n < k
      · simp only [if_pos hnk2]
        omega
      · simp only [if_neg hnk2]
        omega]
    rw [hm0]
    exact hFull
  · -- the general case: the backing lives in the tail
    obtain ⟨na'', P', hPop, hqna'', hdP''⟩ :=
      po_loop stProg n seed k (min k n) b' c' na' T' st_enter_pop hcap
        (by omega) hb12' hbna' hna12' hnc'
        (by
          rw [show stFam n seed ++ List.replicate (c' - n) 0
              = stFam n seed ++ List.replicate (c' - n) 0 from rfl]
          exact hbT') hdead'
        (min k n) 0 (na' + 4) ([] : Heap) ch1 rfl (by omega) (by omega)
        (fun x _ => rfl)
    rw [show n - 0 = n from by omega] at hPop
    rw [show (decide (((min k n : Nat) : Int)
        < ((min k n : Nat) : Int))) = false from
      decide_eq_false (by omega)] at hPop
    rw [show ((0 : Nat) : Int) = (0 : Int) from rfl] at hPop
    have hEPMP := stepFnIter_chain hEPM hPop
    have hX := st_exit stProg n seed k (min k n) b' c' na' na'' T' P'
      ch1 st_enter_size hcap (by omega) hnc' hna12' hqna'' hdead'
      hdP''
    have hFull := stepFnIter_chain hEPMP hX
    refine ⟨b', c', na'' + 3,
      T' ++ ([(Loc.base ⟨na'⟩, u64c ((min k n : Nat) : Int)),
        (Loc.base ⟨na' + 1⟩, arrC 8 (stPopPre n seed (min k n))),
        (Loc.base ⟨na' + 2⟩, u64c ((min k n : Nat) : Int)),
        (Loc.base ⟨na' + 3⟩, bcell false)]
        ++ (P'
          ++ [(Loc.base ⟨na''⟩, u64c ((n - min k n : Nat) : Int)),
            (Loc.base ⟨na'' + 1⟩, slC (sHv b' (n - min k n) c')),
            (Loc.base ⟨na'' + 2⟩,
              u64c ((n - min k n : Nat) : Int))])), ch1, ?_⟩
    rw [show 242 + 130 * n + 127 * min k n + (if n < k then 12 else 0)
        = 84 + 130 * (n - 0) + (86 + (if n < k then 12 else 0))
          + 127 * (min k n - 0) + 72 from by
      by_cases hnk2 : n < k
      · simp only [if_pos hnk2]
        omega
      · simp only [if_neg hnk2]
        omega]
    exact hFull

/-! ## The user-facing statements -/

/-- **THE HEADLINE (§11 harness form, S3 RELATIONAL)**: for every
`n ≤ 8`, EVERY `seed < 2^64`, and EVERY `k < 2^64`, running the Go
harness `stack_harness_r(n, seed, k)` through the machine's native
function entry completes normally past one fuel bound, AT EVERY
NONDETERMINISM-CHOICE STREAM, and returns three values: the `n` pushed
values as a fixed-cap array, `pushed.reverse.take k` — LIFO order,
truncated at what the stack holds — and the count of pops that found
the stack empty, `n − k` truncated at zero. The postcondition is a
relation over the RETURNED DATA — no family function appears in it.

Honesty clauses, recorded rather than hidden:

* **`∀ ch` DOES REAL WORK HERE.** This is the gallery's first
  non-map example (alongside `queue`) whose subject actually consumes
  nondeterminism choices: each `append` that outgrows its backing
  array draws one choice to fix the fresh capacity inside the
  machine's growth envelope (`appendSpillWidth`/`appendGrowthCap`).
  The proof is CAPACITY- AND ADDRESS-GENERIC — the push-loop invariant
  carries an existential backing address and capacity (`PuInv`) and
  never names the choice-dependent layout, so the theorem holds at
  every stream and even survives a re-envelope of the append growth
  rule that keeps the choice arity. The step COUNT is
  choice-invariant (probe-checked at three streams); the heap layout
  is not, and only the count reaches the statement.
* **`∃ pushed` is family-determined.** The witness is
  `stFam n seed = [seed, seed+1, …]` reduced mod 2^64; the statement
  merely avoids SAYING so — exactly as in `Histogram`'s and
  `DotProduct`'s headlines. Making the input genuine ∀-data needs the
  ghost rung-1 annotation, which is designed and not built.
* **The arithmetic wraps, and the claim covers the wrap region.**
  `seed + i` is uint64 and reduces mod 2^64; the theorem's domain is
  the FULL `seed < 2^64`. The corpus's differential ceiling is
  `seed = 2^63 − 1` (row `harness-maxseed`, `8,9223372036854775807,4`
  — the harness family's largest pinned seed), so the region
  `[2^63, 2^64)` is theorem-claimed but oracle-unpinned: the machine
  was probe-run there (`n = 1, 3, 8` at `seed = 2^64 − 1`,
  `n = k = 8` at `2^64 − 2`) and matches the statement, but no
  corpus row exercises it against `go run`.
* **The cap `n ≤ 8` is a toy bound** — the program's own
  `stackCapN = 8` observation arrays (Go's pass-by-value fragment
  cannot return unbounded data); `n` beyond 8 would index past the
  fixed-cap `pushed` array. `seed`/`k` range over their full uint64
  domain; their bounds are Go's, not ours.
* **The third value is the REMAINING stack size, and `n − k` is Nat
  subtraction.** The Go returns `size(s)` — `uint64(len(s))` — after
  popping `m := min(k, n)` values, so the remaining size is
  `n − min(k, n)`, which is exactly `(n - k : Nat)`: Nat subtraction
  truncates at zero, so an over-large `k` simply drains the stack
  rather than driving the count negative. No separate `max 0` is
  needed, and the Go never pops an empty stack — the loop runs `m`
  times, not `k`.
* **The fuel bound `257·n + 254` is a BOUND, not the exact count.**
  The measured count is `242 + 130·n + 127·min(k,n) + 12·[n < k]`
  (probe-confirmed at `n = 0…8` across `k` under, at, and over `n`);
  the shipped `N` equals it exactly when `k > n` (then
  `min(k,n) = n` and the branch surcharge fires) and is loose by
  `127·(n − k) + 12` steps when `k ≤ n` — see `st_run` for the exact
  formula as proved.
* **Machine idealization** as in the other entries: entry from an
  empty heap, an unbounded heap, allocation always succeeds. -/
theorem stack_ok (n seed k : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64)
    (hk : k < 2 ^ 64) :
    ∃ pushed : List Int, pushed.length = n ∧
      ∃ N : Nat, ∀ fuel ≥ N, ∀ ch : Choices,
        runFunctionWithContextM fuel stackLowered.typeDefs.toList
            stackLowered.funcs stackHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
              .int (k : Int) .uint64]
            stackLowered.methods ch
          = .ok { values := #[stArr8 pushed,
                              stArr8 (pushed.reverse.take k),
                              .int ((n - k : Nat) : Int) .uint64] } := by
  refine ⟨stFam n seed, stFam_length n seed, 257 * n + 254,
    fun fuel hfuel ch => ?_⟩
  obtain ⟨bf, cf, naf, Tf, ch', hrun⟩ := st_run n seed k hcap hseed hk ch
  have hle : 242 + 130 * n + 127 * min k n
      + (if n < k then 12 else 0) ≤ fuel := by
    by_cases hnk : n < k
    · simp only [if_pos hnk]
      omega
    · simp only [if_neg hnk]
      omega
  have hfold := runConfig_of_stepFnIter hrun
    (fuel - (242 + 130 * n + 127 * min k n + (if n < k then 12 else 0)))
  rw [Nat.add_sub_cancel' hle] at hfold
  have hst : stHSeed ((n : Nat) : Int) ((seed : Nat) : Int)
        ((k : Nat) : Int)
      = stStx stProg
          [(.base ⟨0⟩, u64c (n : Int)), (.base ⟨1⟩, u64c (seed : Int)),
           (.base ⟨2⟩, u64c (k : Int)), (.base ⟨3⟩, arrC 8 zeros8),
           (.base ⟨4⟩, arrC 8 zeros8), (.base ⟨5⟩, u64c 0)] 6 := rfl
  have hc0 : stHC0 = Config.exec stackHarnessRFunc.body [stBase] stStop :=
    rfl
  rw [stH_entry_eq (n : Int) (seed : Int) (k : Int) fuel ch,
    unorm_nat_of_lt (by omega : n < 2 ^ 64), unorm_nat_of_lt hseed,
    unorm_nat_of_lt hk, hst, hc0, hfold, runConfig_next_stop]
  simp only [bind, Except.bind, st_readback, pure, Except.pure]
  rw [show ((n - k : Nat) : Int) = ((n - min k n : Nat) : Int) from by
    congr 1
    omega]
  rw [stArr8, stArr8, ← stPre_full,
    stPopL_reverse_take n seed k (min k n) rfl, stPopL_length,
    show stPopL n seed (min k n)
        ++ List.replicate (8 - min k n) 0
      = stPopPre n seed (min k n) from rfl]

/-- **The D1 run-conditioned twin**: ANY successful completion of the
harness entry, at any fuel and any choice stream, returns exactly those
three values — derived from `stack_ok` through the shared
`harness_readout_of_total` bridge; nothing is re-proven. -/
theorem stack_readout (n seed k : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) (hk : k < 2 ^ 64) :
    ∃ pushed : List Int, pushed.length = n ∧
      ∀ (fuel : Nat) (ch : Choices) (r : Result),
        runFunctionWithContextM fuel stackLowered.typeDefs.toList
            stackLowered.funcs stackHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
              .int (k : Int) .uint64]
            stackLowered.methods ch
          = .ok r →
        r = { values := #[stArr8 pushed,
                          stArr8 (pushed.reverse.take k),
                          .int ((n - k : Nat) : Int) .uint64] } := by
  obtain ⟨pushed, hlen, N, htot⟩ := stack_ok n seed k hcap hseed hk
  exact ⟨pushed, hlen, harness_readout_of_total ⟨N, htot⟩⟩

end GoLean.Examples.SliceStack
