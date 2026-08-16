import GoLeanProofs.Examples.DotProductProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.EntryEq
import GoLeanProofs.Laws.StmtOps

/-!
# DotProduct — the `dotprod` example (Gallery Campaign G1)

Go source: `Corpus/coverage/exec/examples/dotprod/main.go` (14 rows,
differentially green against `go run`). The lowering is pinned by
`scripts/check-golden` against `baselines/golden/dotprod-lowered.repr`
and carried in `GoLeanProofs.Examples.DotProductProgram`.

The subject is the accumulate loop `acc += a[i]*b[i]` over `[]uint64`,
WRAPPING mod 2^64 — the wrap is the semantics, not an edge case (the
corpus rows `four-wrap`, `one-wrap`, `harness-r-wrap-max` and
`harness-r-wrap-62` exercise it deliberately). The harness
`dotprod_harness_r(n, seed)` is the S3 RELATIONAL shape: one setup loop
builds BOTH families `a[i] = seed + i` and `b[i] = i + 1`, two copy
loops lift them into the fixed-cap `[8]uint64` arrays `av`/`bv`
(zero-padded past `n`), then `dotProduct(a, b)` runs and the observable
is `(av, bv, dot)` — so the postcondition is a relation over the
RETURNED DATA.

THE HEADLINE is stated HERE, in the root, so the aggregator's
`import GoLeanProofs.Examples.DotProduct` reaches it by name (the
C-H4/C-H5 shape, adopted from birth).
-/

namespace GoLean.Examples.DotProduct

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

abbrev tU64 : Ty := .int .uint64
abbrev sliceU : Ty := .slice tU64

/-! ## The statement vocabulary

`dotSpec` is the whole postcondition on the third returned value: the
MATHEMATICAL integer dot product of the two returned lists, reduced
once mod 2^64. The modular reduction IS the claim (machine-integer
honesty, FD-E3): uint64 multiplication and accumulation genuinely wrap,
and the theorem says exactly what the wrapped answer is, on the FULL
seed domain — no hypothesis excludes the wrap region. -/

/-- The wrapped dot product: `(Σ aᵢ·bᵢ) mod 2^64`, one modular
reduction of the true integer sum. First-order and order-respecting;
a reader can check it against the Go loop by eye. -/
def dotSpec (a b : List Int) : Int :=
  (List.zipWith (· * ·) a b).sum % (2 ^ 64 : Int)

/-- The returned fixed-cap array: the observed value list, zero-padded
to the harness's `dotCapN = 8` slots. Deliberately NOT shared with the
identically shaped `Histogram.histArr8` etc. — unifying them would
change what these statements say (the §11 closure rule). -/
def dpArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map
    (fun v => .int v .uint64)⟩

/-! ## The two `Func`s, verbatim from the pinned lowering -/

/-- One setup store `a[i] = seed + i`. -/
def suSeqnA : Stmt :=
  .seqn #[.assign (.addr (.indexAddr (.var "a") (.var "i")))
    (.add (.var "seed") (.var "i"))]

/-- One setup store `b[i] = i + 1`. -/
def suSeqnB : Stmt :=
  .seqn #[.assign (.addr (.indexAddr (.var "b") (.var "i")))
    (.add (.var "i") (.intLit 1 .uint64))]

/-- The setup loop's fill block: BOTH stores, one iteration. -/
def suFill : Stmt := .block #[] #[suSeqnA, suSeqnB]

/-- The setup loop's desugared body. -/
def suBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i")
          (.add (.var "i") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n"))
        (.seqn #[]) .breakStmt,
      suFill]

/-- The copy-loop store `av[i] = a[i]` (ADDRESS-rooted target: `av` is
an array-typed local). -/
def cp1Store : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.ref "av") (.var "i")))
        (.indexGet (.var "a") (.var "i"))]]

def cp1Body : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i")
          (.add (.var "i") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n"))
        (.seqn #[]) .breakStmt,
      cp1Store]

/-- The copy-loop store `bv[i] = b[i]`. -/
def cp2Store : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.ref "bv") (.var "i")))
        (.indexGet (.var "b") (.var "i"))]]

def cp2Body : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i")
          (.add (.var "i") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n"))
        (.seqn #[]) .breakStmt,
      cp2Store]

/-! ### The harness body's top-level statement pieces -/

def dpS1 : Stmt :=
  .seqn #[.initialization { id := "$c12", typ := sliceU },
          .makeSlice (.var "$c12") tU64 (.var "n") none]
def dpS2 : Stmt :=
  .seqn #[.initialization { id := "a", typ := sliceU },
          .assign (.var "a") (.var "$c12")]
def dpS3 : Stmt :=
  .seqn #[.initialization { id := "$c13", typ := sliceU },
          .makeSlice (.var "$c13") tU64 (.var "n") none]
def dpS4 : Stmt :=
  .seqn #[.initialization { id := "b", typ := sliceU },
          .assign (.var "b") (.var "$c13")]
def dpS5 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := tU64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) suBody]]
def dpS6 : Stmt :=
  .seqn #[.initialization { id := "av", typ := .array 8 tU64 }]
def dpS7 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := tU64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) cp1Body]]
def dpS8 : Stmt :=
  .seqn #[.initialization { id := "bv", typ := .array 8 tU64 }]
def dpS9 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := tU64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) cp2Body]]
def dpS10 : Stmt :=
  .seqn #[.initialization { id := "dot", typ := tU64 },
          .call #[.var "dot"] ⟨"dotProduct"⟩
            #[.var "a", .var "b"]]
def dpS11 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "av"),
          .assign (.var "$res1") (.var "bv"),
          .assign (.var "$res2") (.var "dot"),
          .returnStmt]

/-- The harness `Func`, verbatim from the pinned lowering (the pin below
ties it by `rfl`) — restated in the readable compositional form; the
guardrails stub carried the byte-extracted monolith, and the pin holding
proves the two spellings identical. -/
def dotprodHarnessRFunc : Func :=
  { id := { key := "dotprod_harness_r" },
    args := #[{ id := "n", typ := tU64 }, { id := "seed", typ := tU64 }],
    results := #[{ id := "$res0", typ := .array 8 tU64 },
                 { id := "$res1", typ := .array 8 tU64 },
                 { id := "$res2", typ := tU64 }],
    body := .block #[]
      #[dpS1, dpS2, dpS3, dpS4, dpS5, dpS6, dpS7, dpS8, dpS9, dpS10, dpS11],
    variadic := false,
    wrapper := false }

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem dotprodHarnessRFunc_pin :
    findFunctionIn? dotprodLowered.funcs ⟨"dotprod_harness_r"⟩
    = some dotprodHarnessRFunc := rfl

/-! ### The subject `Func` -/

def sjT1 : Stmt :=
  .seqn #[.initialization { id := "n", typ := .int .int },
          .assign (.var "n") (.length (.var "a") (some sliceU))]
def sjGuardThen : Stmt :=
  .block #[]
    #[.seqn #[.assign (.var "n") (.length (.var "b") (some sliceU))]]
def sjT2 : Stmt :=
  .ifThenElse
    (.lessCmp (.length (.var "b") (some sliceU)) (.var "n"))
    sjGuardThen (.seqn #[])
def sjT3 : Stmt :=
  .seqn #[.initialization { id := "acc", typ := tU64 },
          .assign (.var "acc") (.intLit 0 .uint64)]
def sjAccAsgn : Stmt :=
  .assign (.var "acc")
    (.add (.var "acc")
      (.mul (.indexGet (.var "a") (.var "i"))
        (.indexGet (.var "b") (.var "i"))))
def sjAccBlock : Stmt := .block #[] #[sjAccAsgn]
def sjBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i")
          (.add (.var "i") (.intLit 1 .int))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n"))
        (.seqn #[]) .breakStmt,
      sjAccBlock]
def sjT4 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .int },
              .assign (.var "i") (.intLit 0 .int)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) sjBody]]
def sjT5 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "acc"), .returnStmt]

/-- The subject `Func`: the min-length guard and the wrapping
accumulate loop, verbatim from the pinned lowering. -/
def dotProductFunc : Func :=
  { id := { key := "dotProduct" },
    args := #[{ id := "a", typ := sliceU }, { id := "b", typ := sliceU }],
    results := #[{ id := "$res0", typ := tU64 }],
    body := .block #[] #[sjT1, sjT2, sjT3, sjT4, sjT5],
    variadic := false,
    wrapper := false }

/-- The subject pin. -/
theorem dotProduct_pin :
    findFunctionIn? dotprodLowered.funcs ⟨"dotProduct"⟩
    = some dotProductFunc := rfl

/-! ## The setup families and their prefixes

`dpFamA n seed = [seed+0, seed+1, …]` WRAPPED mod 2^64 elementwise (the
wrap is part of the family by design — the wrap-region corpus rows live
here); `dpFamB n = [1, 2, …, n]`. Near-dup note (kit): `SliceMem.familyMod k`
is `seed + i%k`; the A-family here is `seed + i` (MinMax's `mmFamily`
formula, which is designated statement vocabulary there and deliberately
not shared). The zero-padded copy prefix DOES reuse the kit's
`prefixPad` generically. -/

def dpFamA (n seed : Nat) : List Int :=
  (List.range n).map (fun i => (((seed + i) % 2 ^ 64 : Nat) : Int))

def dpFamB (n : Nat) : List Int :=
  (List.range n).map (fun i => ((i + 1 : Nat) : Int))

theorem dpFamA_length (n seed : Nat) : (dpFamA n seed).length = n :=
  familyF_length id n seed

theorem dpFamB_length (n : Nat) : (dpFamB n).length = n := by
  simp [dpFamB]

theorem dpFamA_range (n seed : Nat) :
    ∀ v ∈ dpFamA n seed, 0 ≤ v ∧ v < 2 ^ 64 :=
  familyF_range id n seed

theorem dpFamB_range {n : Nat} (hn : n < 2 ^ 64) :
    ∀ v ∈ dpFamB n, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  simp only [dpFamB, List.mem_map, List.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  omega

theorem dpFamAZ_range {n seed i : Nat} :
    ∀ v ∈ dpFamA i seed ++ List.replicate (n - i) (0 : Int),
      0 ≤ v ∧ v < 2 ^ 64 :=
  familyFZ_range (f := id)

theorem dpFamBZ_range {n i : Nat} (hi : i < 2 ^ 64) :
    ∀ v ∈ dpFamB i ++ List.replicate (n - i) (0 : Int),
      0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact dpFamB_range hi v hv
  · rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
    omega

theorem dpFamA_succ (i seed : Nat) :
    dpFamA (i + 1) seed
      = dpFamA i seed ++ [(((seed + i) % 2 ^ 64 : Nat) : Int)] :=
  familyF_succ id i seed

theorem dpFamB_succ (i : Nat) :
    dpFamB (i + 1) = dpFamB i ++ [((i + 1 : Nat) : Int)] := by
  simp [dpFamB, List.range_succ]

/-- One setup store advances the A-family prefix. -/
theorem dpFamA_set {n seed i : Nat} (hi : i < n) :
    (dpFamA i seed ++ List.replicate (n - i) 0).set i
        (((seed + i) % 2 ^ 64 : Nat) : Int)
      = dpFamA (i + 1) seed ++ List.replicate (n - (i + 1)) 0 :=
  familyF_set (f := id) hi

/-- One setup store advances the B-family prefix. -/
theorem dpFamB_set {n i : Nat} (hi : i < n) :
    (dpFamB i ++ List.replicate (n - i) 0).set i ((i + 1 : Nat) : Int)
      = dpFamB (i + 1) ++ List.replicate (n - (i + 1)) 0 := by
  have hlen : (dpFamB i).length = i := dpFamB_length i
  have hnm : n - i = (n - (i + 1)) + 1 := by omega
  rw [List.set_append_right _ _ (by omega), hlen, Nat.sub_self, hnm,
    List.replicate_succ, List.set_cons_zero, dpFamB_succ]
  simp

theorem dpFamA_getD {n seed m : Nat} (hm : m < n) :
    (dpFamA n seed).getD m 0 = (((seed + m) % 2 ^ 64 : Nat) : Int) :=
  familyF_getD (f := id) hm

theorem dpFamB_getD {n m : Nat} (hm : m < n) :
    (dpFamB n).getD m 0 = ((m + 1 : Nat) : Int) := by
  rw [dpFamB, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using hm)]
  simp

/-! ### The copy prefixes (the kit's `prefixPad`, GAP-P2 lift) -/

/-- The `av` array after `m` copy steps. -/
def dpPreA (m seed : Nat) : List Int := prefixPad dpFamA 8 m seed

/-- The `bv` array after `m` copy steps. -/
def dpPreB (m : Nat) : List Int :=
  prefixPad (fun k _ => dpFamB k) 8 m 0

theorem dpPreA_zero (seed : Nat) : dpPreA 0 seed = List.replicate 8 0 :=
  prefixPad_zero rfl

theorem dpPreB_zero : dpPreB 0 = List.replicate 8 0 :=
  prefixPad_zero rfl

theorem dpPreA_length {m seed : Nat} (h : m ≤ 8) :
    (dpPreA m seed).length = 8 :=
  prefixPad_length (dpFamA_length m seed) h

theorem dpPreB_length {m : Nat} (h : m ≤ 8) : (dpPreB m).length = 8 :=
  prefixPad_length (dpFamB_length m) h

theorem dpPreA_range {m seed : Nat} :
    ∀ v ∈ dpPreA m seed, 0 ≤ v ∧ v < 2 ^ 64 :=
  prefixPad_range (dpFamA_range m seed)

theorem dpPreB_range {m : Nat} (hm : m < 2 ^ 64) :
    ∀ v ∈ dpPreB m, 0 ≤ v ∧ v < 2 ^ 64 :=
  prefixPad_range (dpFamB_range hm)

theorem dpPreA_set {seed m : Nat} (hm : m < 8) :
    (dpPreA m seed).set m (((seed + m) % 2 ^ 64 : Nat) : Int)
      = dpPreA (m + 1) seed :=
  dpFamA_set hm

theorem dpPreB_set {m : Nat} (hm : m < 8) :
    (dpPreB m).set m ((m + 1 : Nat) : Int) = dpPreB (m + 1) :=
  dpFamB_set hm

theorem dpPreA_full {n seed : Nat} :
    dpPreA n seed
      = dpFamA n seed
          ++ List.replicate (8 - (dpFamA n seed).length) 0 :=
  prefixPad_full (dpFamA_length n seed)

theorem dpPreB_full {n : Nat} :
    dpPreB n = dpFamB n ++ List.replicate (8 - (dpFamB n).length) 0 :=
  prefixPad_full (dpFamB_length n)

/-! ## The accumulator recursion and the bridge to `dotSpec` -/

/-- The Go loop's own accumulator: after `i` iterations,
`acc = dpAcc seed i` — product wrapped first, then the sum wrapped,
exactly the machine's two uint64 normalizations per iteration. -/
def dpAcc (seed : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 =>
      (dpAcc seed i + (((seed + i) % 2 ^ 64) * (i + 1)) % 2 ^ 64) % 2 ^ 64

theorem dpAcc_lt (seed : Nat) : ∀ i, dpAcc seed i < 2 ^ 64
  | 0 => by simp [dpAcc]
  | i + 1 => by
      show (dpAcc seed i + (((seed + i) % 2 ^ 64) * (i + 1)) % 2 ^ 64)
        % 2 ^ 64 < 2 ^ 64
      exact Nat.mod_lt _ (by omega)

/-- The true (unwrapped) sum of products. -/
def dpSum (seed n : Nat) : Nat :=
  ((List.range n).map (fun i => ((seed + i) % 2 ^ 64) * (i + 1))).sum

theorem dpSum_succ (seed n : Nat) :
    dpSum seed (n + 1)
      = dpSum seed n + ((seed + n) % 2 ^ 64) * (n + 1) := by
  simp [dpSum, List.range_succ]

/-- Per-step wrapping equals one final reduction (mod distributes over
the sum). -/
theorem dpAcc_eq (seed : Nat) : ∀ n, dpAcc seed n = dpSum seed n % 2 ^ 64
  | 0 => by simp [dpAcc, dpSum]
  | n + 1 => by
      show (dpAcc seed n + (((seed + n) % 2 ^ 64) * (n + 1)) % 2 ^ 64)
          % 2 ^ 64 = _
      rw [dpAcc_eq seed n, dpSum_succ, Nat.add_mod
        (dpSum seed n) (((seed + n) % 2 ^ 64) * (n + 1))]

/-- `zipWith` over two snocs of equal-length lists. -/
private theorem zipWith_mul_snoc :
    ∀ (xs ys : List Int) (a b : Int), xs.length = ys.length →
      List.zipWith (· * ·) (xs ++ [a]) (ys ++ [b])
        = List.zipWith (· * ·) xs ys ++ [a * b]
  | [], [], a, b, _ => rfl
  | x :: xs, y :: ys, a, b, h => by
      simp only [List.cons_append, List.zipWith_cons_cons]
      rw [zipWith_mul_snoc xs ys a b (by simpa using h)]
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h

private theorem dp_zip_sum (seed : Nat) :
    ∀ n, (List.zipWith (· * ·) (dpFamA n seed) (dpFamB n)).sum
      = ((dpSum seed n : Nat) : Int)
  | 0 => by simp [dpFamA, dpFamB, dpSum]
  | n + 1 => by
      rw [dpFamA_succ, dpFamB_succ,
        zipWith_mul_snoc _ _ _ _
          (by rw [dpFamA_length, dpFamB_length]),
        List.sum_append, dp_zip_sum seed n, dpSum_succ,
        List.sum_cons, List.sum_nil, Int.add_zero, ← Int.natCast_mul,
        ← Int.natCast_add]

/-- **The bridge**: the wrapped machine accumulator IS `dotSpec` of the
two families. -/
theorem dotSpec_fam (n seed : Nat) :
    dotSpec (dpFamA n seed) (dpFamB n) = ((dpAcc seed n : Nat) : Int) := by
  rw [dotSpec, dp_zip_sum seed n, dpAcc_eq]
  omega

/-! ## Machine-integer wrap forms — LIFTED (WP arc s1 lift 1): the
local `unorm_nat` is deleted (call sites resolve to `SliceMem.unorm_nat`
through the module's `open`); the pinned `unorm_mul_nat` survives as a
delegation, zero proof lines. -/

theorem unorm_mul_nat (a b : Nat) :
    IntKind.normalize .uint64 ((a : Int) * (b : Int))
      = ((a * b % 2 ^ 64 : Nat) : Int) :=
  -- The `have _` anchors `unorm_add_nat` (the old local proof's
  -- dependency) so this PINNED name keeps its recorded axiom set
  -- `[propext, Quot.sound]` and the frozen audit shard stays
  -- byte-identical; the kit proof alone is `[propext]`. Recorded in
  -- `docs/wp-arc-log/s1.md` (lift 1 JC).
  have _ := unorm_add_nat 0 0
  SliceMem.unorm_mul_nat a b

/-! ## Address layout

Probe-measured at `(n, seed) = (3, 900001)` (`.tmp/dpprobe.lean`
traced every `nextAddr` bump; every raw segment below re-checks the
transcription by `rfl`):

```
0 = n            1 = seed
2 = $res0 ([8])  3 = $res1 ([8])   4 = $res2
5 = $c12 handle  6 = a backing     7 = a
8 = $c13 handle  9 = b backing    10 = b
11 = setup i    12 = setup flag
13 = av ([8])   14 = copy1 i      15 = copy1 flag
16 = bv ([8])   17 = copy2 i      18 = copy2 flag
19 = dot
-- the `dotProduct` frame --
20 = a param    21 = b param      22 = its $res0
23 = subject n (int)  24 = acc    25 = subject i (int)  26 = subject flag
-- nextAddr = 27; NOTHING allocates past this point --
```
-/

abbrev u64cell (v : Int) : HeapCell := ⟨some tU64, .int v .uint64⟩
abbrev icell (v : Int) : HeapCell := ⟨some (.int .int), .int v .int⟩
abbrev bcell (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
abbrev arrCell (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n tU64), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev zeros8 : List Int := List.replicate 8 0

abbrev aSliceV (n : Nat) : GoValue := .slice ⟨some (.base ⟨6⟩), 0, n, n⟩
abbrev bSliceV (n : Nat) : GoValue := .slice ⟨some (.base ⟨9⟩), 0, n, n⟩
abbrev aHcell (n : Nat) : HeapCell := ⟨some sliceU, aSliceV n⟩
abbrev bHcell (n : Nat) : HeapCell := ⟨some sliceU, bSliceV n⟩
abbrev nilSliceCell : HeapCell := ⟨some sliceU, .slice ⟨none, 0, 0, 0⟩⟩

/-- The PROGRAM-generic state form. -/
abbrev dpSt (σ : ExecState) (H : Heap) (na : Nat) : ExecState :=
  { σ with heap := H, nextAddr := na }

/-! ### Heap fronts, one per phase (append-extension until the exit) -/

def dpHeap0 (nv sv : Int) : Heap :=
  [(.base ⟨0⟩, u64cell nv), (.base ⟨1⟩, u64cell sv),
   (.base ⟨2⟩, arrCell 8 zeros8), (.base ⟨3⟩, arrCell 8 zeros8),
   (.base ⟨4⟩, u64cell 0)]

def dpHeapC12 (nv sv : Int) : Heap :=
  dpHeap0 nv sv ++ [(.base ⟨5⟩, nilSliceCell)]

def dpHeapMkA (nv sv : Int) (n : Nat) : Heap :=
  dpHeap0 nv sv
    ++ [(.base ⟨5⟩, aHcell n),
        (.base ⟨6⟩, arrCell n (List.replicate n 0))]

def dpHeapC13 (nv sv : Int) (n : Nat) : Heap :=
  dpHeapMkA nv sv n
    ++ [(.base ⟨7⟩, aHcell n), (.base ⟨8⟩, nilSliceCell)]

def dpHeapMkB (nv sv : Int) (n : Nat) : Heap :=
  dpHeapMkA nv sv n
    ++ [(.base ⟨7⟩, aHcell n), (.base ⟨8⟩, bHcell n),
        (.base ⟨9⟩, arrCell n (List.replicate n 0))]

def dpHeapSu (nv sv : Int) (n : Nat) (lA lB : List Int) (iv : Int)
    (ff : Bool) : Heap :=
  dpHeap0 nv sv
    ++ [(.base ⟨5⟩, aHcell n), (.base ⟨6⟩, arrCell n lA),
        (.base ⟨7⟩, aHcell n), (.base ⟨8⟩, bHcell n),
        (.base ⟨9⟩, arrCell n lB), (.base ⟨10⟩, bHcell n),
        (.base ⟨11⟩, u64cell iv), (.base ⟨12⟩, bcell ff)]

def dpHeapCp1 (nv sv : Int) (n : Nat) (lA lB : List Int) (siv : Int)
    (lp : List Int) (civ : Int) (ff : Bool) : Heap :=
  dpHeapSu nv sv n lA lB siv false
    ++ [(.base ⟨13⟩, arrCell 8 lp), (.base ⟨14⟩, u64cell civ),
        (.base ⟨15⟩, bcell ff)]

def dpHeapCp2 (nv sv : Int) (n : Nat) (lA lB : List Int) (siv : Int)
    (lp : List Int) (c1v : Int) (lq : List Int) (civ : Int)
    (ff : Bool) : Heap :=
  dpHeapCp1 nv sv n lA lB siv lp c1v false
    ++ [(.base ⟨16⟩, arrCell 8 lq), (.base ⟨17⟩, u64cell civ),
        (.base ⟨18⟩, bcell ff)]

def dpHeapCall (nv sv : Int) (n : Nat) (lA lB : List Int) (siv : Int)
    (lp : List Int) (c1v : Int) (lq : List Int) (c2v : Int) : Heap :=
  dpHeapCp2 nv sv n lA lB siv lp c1v lq c2v false
    ++ [(.base ⟨19⟩, u64cell 0)]

def dpHeapFrame (nv sv : Int) (n : Nat) (lA lB : List Int) (siv : Int)
    (lp : List Int) (c1v : Int) (lq : List Int) (c2v : Int) : Heap :=
  dpHeapCall nv sv n lA lB siv lp c1v lq c2v
    ++ [(.base ⟨20⟩, aHcell n), (.base ⟨21⟩, bHcell n),
        (.base ⟨22⟩, u64cell 0)]

/-- The subject-phase front (all 27 cells; the loop touches only
`acc`/`i`/`$forFirst`). -/
def dpHeapSubj (nv sv : Int) (n : Nat) (lA lB : List Int) (siv : Int)
    (lp : List Int) (c1v : Int) (lq : List Int) (c2v : Int)
    (nsv accv iv : Int) (ff : Bool) : Heap :=
  dpHeapFrame nv sv n lA lB siv lp c1v lq c2v
    ++ [(.base ⟨23⟩, icell nsv), (.base ⟨24⟩, u64cell accv),
        (.base ⟨25⟩, icell iv), (.base ⟨26⟩, bcell ff)]

/-- The exit-phase front: the epilogue writes IN PLACE (cells 22, 19,
2, 3, 4), so this family is the explicit flat literal. -/
def dpHeapX (nv sv : Int) (n : Nat) (lA lB : List Int) (siv : Int)
    (lp : List Int) (c1v : Int) (lq : List Int) (c2v : Int)
    (r2 r3 : List Int) (r4 dv r22 nsv accv iv : Int) : Heap :=
  [(.base ⟨0⟩, u64cell nv), (.base ⟨1⟩, u64cell sv),
   (.base ⟨2⟩, arrCell 8 r2), (.base ⟨3⟩, arrCell 8 r3),
   (.base ⟨4⟩, u64cell r4),
   (.base ⟨5⟩, aHcell n), (.base ⟨6⟩, arrCell n lA),
   (.base ⟨7⟩, aHcell n), (.base ⟨8⟩, bHcell n),
   (.base ⟨9⟩, arrCell n lB), (.base ⟨10⟩, bHcell n),
   (.base ⟨11⟩, u64cell siv), (.base ⟨12⟩, bcell false),
   (.base ⟨13⟩, arrCell 8 lp), (.base ⟨14⟩, u64cell c1v),
   (.base ⟨15⟩, bcell false),
   (.base ⟨16⟩, arrCell 8 lq), (.base ⟨17⟩, u64cell c2v),
   (.base ⟨18⟩, bcell false),
   (.base ⟨19⟩, u64cell dv),
   (.base ⟨20⟩, aHcell n), (.base ⟨21⟩, bHcell n),
   (.base ⟨22⟩, u64cell r22),
   (.base ⟨23⟩, icell nsv), (.base ⟨24⟩, u64cell accv),
   (.base ⟨25⟩, icell iv), (.base ⟨26⟩, bcell false)]

/-! ### Environments -/

def baseEnvD : Scope :=
  [("$res2", .base ⟨4⟩), ("$res1", .base ⟨3⟩), ("$res0", .base ⟨2⟩),
   ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]
def envC12D : LocalEnv := [[("$c12", .base ⟨5⟩)], baseEnvD]
def envC13D : LocalEnv :=
  [[("$c13", .base ⟨8⟩), ("a", .base ⟨7⟩), ("$c12", .base ⟨5⟩)], baseEnvD]
def abScope : Scope :=
  [("b", .base ⟨10⟩), ("$c13", .base ⟨8⟩), ("a", .base ⟨7⟩),
   ("$c12", .base ⟨5⟩)]
def avScope : Scope := ("av", .base ⟨13⟩) :: abScope
def bvScope : Scope := ("bv", .base ⟨16⟩) :: avScope
def dotScope : Scope := ("dot", .base ⟨19⟩) :: bvScope

def suEnv : LocalEnv :=
  [[("$forFirst", .base ⟨12⟩)], [("i", .base ⟨11⟩)], abScope, baseEnvD]
def suEnv1 : LocalEnv := [] :: suEnv
def suEnv2 : LocalEnv := [] :: suEnv1

def cp1Env : LocalEnv :=
  [[("$forFirst", .base ⟨15⟩)], [("i", .base ⟨14⟩)], avScope, baseEnvD]
def cp1Env1 : LocalEnv := [] :: cp1Env
def cp1Env2 : LocalEnv := [] :: cp1Env1

def cp2Env : LocalEnv :=
  [[("$forFirst", .base ⟨18⟩)], [("i", .base ⟨17⟩)], bvScope, baseEnvD]
def cp2Env1 : LocalEnv := [] :: cp2Env
def cp2Env2 : LocalEnv := [] :: cp2Env1

def callEnvD : LocalEnv := [dotScope, baseEnvD]
def sjScope0 : Scope :=
  [("$res0", .base ⟨22⟩), ("b", .base ⟨21⟩), ("a", .base ⟨20⟩)]
def sjFrameEnv : LocalEnv := [sjScope0]
def sjEnvN : LocalEnv := [[("n", .base ⟨23⟩)], sjScope0]
def sjAccScope : Scope := [("acc", .base ⟨24⟩), ("n", .base ⟨23⟩)]
def sjEnv : LocalEnv :=
  [[("$forFirst", .base ⟨26⟩)], [("i", .base ⟨25⟩)], sjAccScope, sjScope0]
def sjEnv1 : LocalEnv := [] :: sjEnv
def sjEnv2 : LocalEnv := [] :: sjEnv1

/-! ### Continuations -/

def dpStop : Cont := .frame [] [] [] [] .stop

def tailAfterSetup : Cont :=
  .seq [dpS6, dpS7, dpS8, dpS9, dpS10, dpS11] [abScope, baseEnvD] dpStop
def suHeadTail : Cont :=
  .seq [] suEnv
    (.seq [] [[("i", .base ⟨11⟩)], abScope, baseEnvD] tailAfterSetup)
def suHeadCfg : Config := .exec (.while (.boolLit true) suBody) suEnv suHeadTail
def suLoopK : Cont := .loop (.boolLit true) suBody suEnv suHeadTail
def suCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt suEnv1 (.seq [suFill] suEnv1 suLoopK)
def suRefA (n : Nat) (iv : Int) : TargetRef :=
  .chain (aSliceV n) [.int iv .uint64] [.index]
def suRefB (n : Nat) (iv : Int) : TargetRef :=
  .chain (bSliceV n) [.int iv .uint64] [.index]
def suTailA : Cont := .seq [suSeqnB] suEnv2 (.seq [] suEnv1 suLoopK)
def suTailB : Cont := .seq [] suEnv2 (.seq [] suEnv1 suLoopK)

def tailAfterCp1 : Cont :=
  .seq [dpS8, dpS9, dpS10, dpS11] [avScope, baseEnvD] dpStop
def cp1HeadTail : Cont :=
  .seq [] cp1Env
    (.seq [] [[("i", .base ⟨14⟩)], avScope, baseEnvD] tailAfterCp1)
def cp1HeadCfg : Config :=
  .exec (.while (.boolLit true) cp1Body) cp1Env cp1HeadTail
def cp1LoopK : Cont := .loop (.boolLit true) cp1Body cp1Env cp1HeadTail
def cp1CmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt cp1Env1 (.seq [cp1Store] cp1Env1 cp1LoopK)
def cp1Ref (iv : Int) : TargetRef :=
  .chain (.addr (.base ⟨13⟩)) [.int iv .uint64] [.index]
def cp1StTail : Cont := .seq [] cp1Env2 (.seq [] cp1Env1 cp1LoopK)
def cp1RhsK (iv : Int) : Cont :=
  .rhsK .vals [cp1Ref iv] [] [] (.seqn #[]) cp1Env2 cp1StTail

def tailAfterCp2 : Cont :=
  .seq [dpS10, dpS11] [bvScope, baseEnvD] dpStop
def cp2HeadTail : Cont :=
  .seq [] cp2Env
    (.seq [] [[("i", .base ⟨17⟩)], bvScope, baseEnvD] tailAfterCp2)
def cp2HeadCfg : Config :=
  .exec (.while (.boolLit true) cp2Body) cp2Env cp2HeadTail
def cp2LoopK : Cont := .loop (.boolLit true) cp2Body cp2Env cp2HeadTail
def cp2CmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt cp2Env1 (.seq [cp2Store] cp2Env1 cp2LoopK)
def cp2Ref (iv : Int) : TargetRef :=
  .chain (.addr (.base ⟨16⟩)) [.int iv .uint64] [.index]
def cp2StTail : Cont := .seq [] cp2Env2 (.seq [] cp2Env1 cp2LoopK)
def cp2RhsK (iv : Int) : Cont :=
  .rhsK .vals [cp2Ref iv] [] [] (.seqn #[]) cp2Env2 cp2StTail

/-! ### The call and the subject -/

def dpCallPlans : List (TargetShape × List Expr) :=
  [(.chain [], [.ref "dot"])]
def afterCallK : Cont := .seq [dpS11] callEnvD dpStop
/-- The `callArgsK` after `a` is delivered and `b` still pending. -/
def dpCallArgsK (n : Nat) : Cont :=
  .callArgsK ⟨"dotProduct"⟩ dpCallPlans [aSliceV n] [] callEnvD afterCallK
/-- The subject's call frame: result loc 22, write-back target `dot`. -/
def frameKD : Cont := .frame dpCallPlans callEnvD [.base ⟨22⟩] [] afterCallK

def sjGuardK : Cont :=
  .ifK sjGuardThen (.seqn #[]) sjEnvN
    (.seq [sjT3, sjT4, sjT5] sjEnvN frameKD)
def sjNRhsK : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨23⟩)) [] []] [] [] (.seqn #[]) sjEnvN
    (.seq [sjT2, sjT3, sjT4, sjT5] sjEnvN frameKD)
def sjLenAK : Cont := .strictK (.lengthOf (some sliceU)) [] [] sjEnvN sjNRhsK
def sjLenBK : Cont :=
  .strictK (.lengthOf (some sliceU)) [] [] sjEnvN
    (.strictK .lessCmp [] [.var "n"] sjEnvN sjGuardK)

def sjHeadTail : Cont :=
  .seq [] sjEnv
    (.seq [] [[("i", .base ⟨25⟩)], sjAccScope, sjScope0]
      (.seq [sjT5] [sjAccScope, sjScope0] frameKD))
def sjHeadCfg : Config := .exec (.while (.boolLit true) sjBody) sjEnv sjHeadTail
def sjLoopK : Cont := .loop (.boolLit true) sjBody sjEnv sjHeadTail
def sjCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt sjEnv1 (.seq [sjAccBlock] sjEnv1 sjLoopK)
def sjStTail : Cont := .seq [] sjEnv2 (.seq [] sjEnv1 sjLoopK)
def sjAccRhsK : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨24⟩)) [] []] [] [] (.seqn #[]) sjEnv2
    sjStTail
def sjAddK (accv : Int) : Cont := .strictK .add [.int accv .uint64] [] sjEnv2 sjAccRhsK
def sjMulK (accv : Int) : Cont :=
  .strictK .mul [] [.indexGet (.var "b") (.var "i")] sjEnv2 (sjAddK accv)
def sjIdxAK (n : Nat) (accv : Int) : Cont :=
  .strictK .indexGet [aSliceV n] [] sjEnv2 (sjMulK accv)
def sjMulK2 (accv av : Int) : Cont :=
  .strictK .mul [.int av .uint64] [] sjEnv2 (sjAddK accv)
def sjIdxBK (n : Nat) (accv av : Int) : Cont :=
  .strictK .indexGet [bSliceV n] [] sjEnv2 (sjMulK2 accv av)

/-! ### The exit epilogue -/

def epiTail1 : Cont :=
  .seq [.assign (.var "$res1") (.var "bv"),
        .assign (.var "$res2") (.var "dot"), .returnStmt] callEnvD dpStop
def epiTail2 : Cont :=
  .seq [.assign (.var "$res2") (.var "dot"), .returnStmt] callEnvD dpStop

/-! ## The pinned program and the entry equation -/

/-- The pinned program as an empty-heap state — with the
`derive_entry_eq` invocation below, the one place this module carries
`dotprodLowered` outside the pins. -/
def dpProg : ExecState :=
  { types := dotprodLowered.typeDefs.toList,
    functions := dotprodLowered.funcs,
    methods := dotprodLowered.methods,
    heap := [], nextAddr := 0 }

derive_entry_eq dpH_entry_eq dotprodLowered dotprodHarnessRFunc dpHSeed dpHC0
  dpProg

/-! ## Heap-lookup facts for the conditioned steps -/

theorem lookup_su6 (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (iv : Int) (ff : Bool) (na : Nat) :
    Heap.lookup (dpSt σ (dpHeapSu nv sv n lA lB iv ff) na).heap (.base ⟨6⟩)
      = some ⟨some (.array n tU64),
          .array ⟨lA.map (fun v => .int v .uint64)⟩⟩ := by
  simp [dpHeapSu, dpHeap0, Heap.lookup]

theorem lookup_su9 (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (iv : Int) (ff : Bool) (na : Nat) :
    Heap.lookup (dpSt σ (dpHeapSu nv sv n lA lB iv ff) na).heap (.base ⟨9⟩)
      = some ⟨some (.array n tU64),
          .array ⟨lB.map (fun v => .int v .uint64)⟩⟩ := by
  simp [dpHeapSu, dpHeap0, Heap.lookup]

theorem lookup_cp1_6 (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (civ : Int) (ff : Bool)
    (na : Nat) :
    Heap.lookup (dpSt σ (dpHeapCp1 nv sv n lA lB siv lp civ ff) na).heap
        (.base ⟨6⟩)
      = some ⟨some (.array n tU64),
          .array ⟨lA.map (fun v => .int v .uint64)⟩⟩ := by
  simp [dpHeapCp1, dpHeapSu, dpHeap0, Heap.lookup]

theorem lookup_cp1_13 (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (civ : Int) (ff : Bool)
    (na : Nat) :
    Heap.lookup (dpSt σ (dpHeapCp1 nv sv n lA lB siv lp civ ff) na).heap
        (.base ⟨13⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨lp.map (fun v => .int v .uint64)⟩⟩ := by
  simp [dpHeapCp1, dpHeapSu, dpHeap0, Heap.lookup]

theorem lookup_cp2_9 (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (civ : Int) (ff : Bool) (na : Nat) :
    Heap.lookup
        (dpSt σ (dpHeapCp2 nv sv n lA lB siv lp c1v lq civ ff) na).heap
        (.base ⟨9⟩)
      = some ⟨some (.array n tU64),
          .array ⟨lB.map (fun v => .int v .uint64)⟩⟩ := by
  simp [dpHeapCp2, dpHeapCp1, dpHeapSu, dpHeap0, Heap.lookup]

theorem lookup_cp2_16 (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (civ : Int) (ff : Bool) (na : Nat) :
    Heap.lookup
        (dpSt σ (dpHeapCp2 nv sv n lA lB siv lp c1v lq civ ff) na).heap
        (.base ⟨16⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨lq.map (fun v => .int v .uint64)⟩⟩ := by
  simp [dpHeapCp2, dpHeapCp1, dpHeapSu, dpHeap0, Heap.lookup]

theorem lookup_subj6 (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (c2v nsv accv iv : Int) (ff : Bool) (na : Nat) :
    Heap.lookup
        (dpSt σ
          (dpHeapSubj nv sv n lA lB siv lp c1v lq c2v nsv accv iv ff)
          na).heap (.base ⟨6⟩)
      = some ⟨some (.array n tU64),
          .array ⟨lA.map (fun v => .int v .uint64)⟩⟩ := by
  simp [dpHeapSubj, dpHeapFrame, dpHeapCall, dpHeapCp2, dpHeapCp1,
    dpHeapSu, dpHeap0, Heap.lookup]

theorem lookup_subj9 (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (c2v nsv accv iv : Int) (ff : Bool) (na : Nat) :
    Heap.lookup
        (dpSt σ
          (dpHeapSubj nv sv n lA lB siv lp c1v lq c2v nsv accv iv ff)
          na).heap (.base ⟨9⟩)
      = some ⟨some (.array n tU64),
          .array ⟨lB.map (fun v => .int v .uint64)⟩⟩ := by
  simp [dpHeapSubj, dpHeapFrame, dpHeapCall, dpHeapCp2, dpHeapCp1,
    dpHeapSu, dpHeap0, Heap.lookup]

theorem lookup_X2 (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (c2v : Int) (r2 r3 : List Int)
    (r4 dv r22 nsv accv iv : Int) (na : Nat) :
    Heap.lookup
        (dpSt σ
          (dpHeapX nv sv n lA lB siv lp c1v lq c2v r2 r3 r4 dv r22 nsv accv
            iv) na).heap (.base ⟨2⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨r2.map (fun v => .int v .uint64)⟩⟩ := by
  simp [dpHeapX, Heap.lookup]

theorem lookup_X3 (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (c2v : Int) (r2 r3 : List Int)
    (r4 dv r22 nsv accv iv : Int) (na : Nat) :
    Heap.lookup
        (dpSt σ
          (dpHeapX nv sv n lA lB siv lp c1v lq c2v r2 r3 r4 dv r22 nsv accv
            iv) na).heap (.base ⟨3⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨r3.map (fun v => .int v .uint64)⟩⟩ := by
  simp [dpHeapX, Heap.lookup]

/-! ## Raw run segments (`with_unfolding_all rfl`: pure definitional
evaluation of the interpreter at symbolic values; split exactly at the
data-dependent points — makeSlice, the element stores/reads, the one
`enterFrame`, the two `len` applies, and the two epilogue array
stores). -/

/-- Entry E1: body start → the `$c12` makeSlice apply point. 10 steps. -/
theorem dp_E1_raw (σ : ExecState) (nv sv : Int) (ch : Choices) :
    stepFnIter 10 (dpSt σ (dpHeap0 nv sv) 5) dpHC0 ch
      = .ok (.retV (.int nv .uint64)
          (.stmtOpK (.makeSlice tU64 false) 1 [.addr (.base ⟨5⟩)] [] envC12D
            (.seq [dpS2, dpS3, dpS4, dpS5, dpS6, dpS7, dpS8, dpS9, dpS10,
              dpS11] envC12D dpStop)),
        dpSt σ (dpHeapC12 nv sv) 6, ch) := by
  with_unfolding_all rfl

/-- `make([]uint64, n)` at SYMBOLIC `n` — the `a` slice (cell 5,
backing 6). -/
theorem dp_makeA_apply (σ : ExecState) (nv sv : Int) (n : Nat)
    (ch : Choices) :
    applyStmtOp (dpSt σ (dpHeapC12 nv sv) 6) ch (.makeSlice tU64 false) 1
      [.addr (.base ⟨5⟩), .int (n : Nat) .uint64]
      = .ok (dpSt σ (dpHeapMkA nv sv n) 7, ch) := by
  have hnn1 := natFromNonneg_cast
    "runtime error: makeslice: len out of range" n
  have hnn2 := natFromNonneg_cast
    "runtime error: makeslice: cap out of range" n
  have hb := GoLean.Iris.buildDefaultArrayValue_int
    (dpSt σ (dpHeapC12 nv sv) 6) .uint64 n
  have harr : (List.replicate n (GoValue.int 0 .uint64)).toArray
      = (⟨(List.replicate n (0 : Int)).map
          (fun v => GoValue.int v .uint64)⟩ : Array GoValue) := by
    simp [List.map_replicate]
  rw [harr] at hb
  simp only [applyStmtOp, applyStmtOpCore, valueAsInt, valueAsLoc,
    hnn1, hnn2, hb, Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (Nat.lt_irrefl n)]
  with_unfolding_all rfl

/-- Entry E2: `a := $c12`, `$c13` declared → the second makeSlice apply
point. 22 steps. -/
theorem dp_E2_raw (σ : ExecState) (nv sv : Int) (n : Nat) (ch : Choices) :
    stepFnIter 22 (dpSt σ (dpHeapMkA nv sv n) 7)
      (.next (.seq [dpS2, dpS3, dpS4, dpS5, dpS6, dpS7, dpS8, dpS9, dpS10,
        dpS11] envC12D dpStop)) ch
      = .ok (.retV (.int nv .uint64)
          (.stmtOpK (.makeSlice tU64 false) 1 [.addr (.base ⟨8⟩)] [] envC13D
            (.seq [dpS4, dpS5, dpS6, dpS7, dpS8, dpS9, dpS10, dpS11]
              envC13D dpStop)),
        dpSt σ (dpHeapC13 nv sv n) 9, ch) := by
  with_unfolding_all rfl

/-- `make([]uint64, n)` — the `b` slice (cell 8, backing 9). -/
theorem dp_makeB_apply (σ : ExecState) (nv sv : Int) (n : Nat)
    (ch : Choices) :
    applyStmtOp (dpSt σ (dpHeapC13 nv sv n) 9) ch (.makeSlice tU64 false) 1
      [.addr (.base ⟨8⟩), .int (n : Nat) .uint64]
      = .ok (dpSt σ (dpHeapMkB nv sv n) 10, ch) := by
  have hnn1 := natFromNonneg_cast
    "runtime error: makeslice: len out of range" n
  have hnn2 := natFromNonneg_cast
    "runtime error: makeslice: cap out of range" n
  have hb := GoLean.Iris.buildDefaultArrayValue_int
    (dpSt σ (dpHeapC13 nv sv n) 9) .uint64 n
  have harr : (List.replicate n (GoValue.int 0 .uint64)).toArray
      = (⟨(List.replicate n (0 : Int)).map
          (fun v => GoValue.int v .uint64)⟩ : Array GoValue) := by
    simp [List.map_replicate]
  rw [harr] at hb
  simp only [applyStmtOp, applyStmtOpCore, valueAsInt, valueAsLoc,
    hnn1, hnn2, hb, Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (Nat.lt_irrefl n)]
  with_unfolding_all rfl

/-- Entry E3: `b := $c13`, the setup counter and flag → the setup loop
head. 42 steps. -/
theorem dp_E3_raw (σ : ExecState) (nv sv : Int) (n : Nat) (ch : Choices) :
    stepFnIter 42 (dpSt σ (dpHeapMkB nv sv n) 10)
      (.next (.seq [dpS4, dpS5, dpS6, dpS7, dpS8, dpS9, dpS10, dpS11]
        envC13D dpStop)) ch
      = .ok (suHeadCfg,
          dpSt σ
            (dpHeapSu nv sv n (List.replicate n 0) (List.replicate n 0) 0
              true) 13, ch) := by
  with_unfolding_all rfl

/-! ### The setup loop -/

theorem su_A0_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 25 (dpSt σ (dpHeapSu nv sv n lA lB iv true) 13) suHeadCfg ch
      = .ok (.retV (.bool (decide (iv < nv))) suCmpK,
          dpSt σ (dpHeapSu nv sv n lA lB iv false) 13, ch) := by
  with_unfolding_all rfl

/-- Setup fill A: test true → the `a[i] = seed + i` store point. 18
steps (the add rides inside; the store value arrives wrapped). -/
theorem su_B1_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 18 (dpSt σ (dpHeapSu nv sv n lA lB iv false) 13)
      (.retV (.bool true) suCmpK) ch
      = .ok (.next (.storeK [suRefA n iv]
            [.int (IntKind.normalize .uint64 (sv + iv)) .uint64]
            (.seqn #[]) suEnv2 suTailA),
          dpSt σ (dpHeapSu nv sv n lA lB iv false) 13, ch) := by
  with_unfolding_all rfl

/-- Setup fill B: the `a` store drained → the `b[i] = i + 1` store
point. 16 steps. -/
theorem su_B2_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 16 (dpSt σ (dpHeapSu nv sv n lA lB iv false) 13)
      (.next (.storeK [] [] (.seqn #[]) suEnv2 suTailA)) ch
      = .ok (.next (.storeK [suRefB n iv]
            [.int (IntKind.normalize .uint64 (iv + 1)) .uint64]
            (.seqn #[]) suEnv2 suTailB),
          dpSt σ (dpHeapSu nv sv n lA lB iv false) 13, ch) := by
  with_unfolding_all rfl

/-- Setup fill C: the `b` store drained → the incremented dispatch and
the next exit test's delivery. 34 steps. -/
theorem su_C_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 34 (dpSt σ (dpHeapSu nv sv n lA lB iv false) 13)
      (.next (.storeK [] [] (.seqn #[]) suEnv2 suTailB)) ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < nv))) suCmpK,
          dpSt σ (dpHeapSu nv sv n lA lB
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false) 13, ch) := by
  with_unfolding_all rfl

/-- Setup exit: test false → `var av` declared and the first copy loop's
head. 39 steps. -/
theorem su_X_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 39 (dpSt σ (dpHeapSu nv sv n lA lB iv false) 13)
      (.retV (.bool false) suCmpK) ch
      = .ok (cp1HeadCfg,
          dpSt σ (dpHeapCp1 nv sv n lA lB iv zeros8 0 true) 16, ch) := by
  with_unfolding_all rfl

/-! ### The copy loops -/

theorem cp1_A0_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (civ : Int)
    (ch : Choices) :
    stepFnIter 25 (dpSt σ (dpHeapCp1 nv sv n lA lB siv lp civ true) 16)
      cp1HeadCfg ch
      = .ok (.retV (.bool (decide (civ < nv))) cp1CmpK,
          dpSt σ (dpHeapCp1 nv sv n lA lB siv lp civ false) 16, ch) := by
  with_unfolding_all rfl

/-- Copy-1 phase 1: test true → the `av[i]` target banked, the `a[i]`
read at its apply point. 16 steps. -/
theorem cp1_B1_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (civ : Int)
    (ch : Choices) :
    stepFnIter 16 (dpSt σ (dpHeapCp1 nv sv n lA lB siv lp civ false) 16)
      (.retV (.bool true) cp1CmpK) ch
      = .ok (.retV (.int civ .uint64)
            (.strictK .indexGet [aSliceV n] [] cp1Env2 (cp1RhsK civ)),
          dpSt σ (dpHeapCp1 nv sv n lA lB siv lp civ false) 16, ch) := by
  with_unfolding_all rfl

theorem cp1_B2_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (civ : Int)
    (w : GoValue) (ch : Choices) :
    stepFnIter 1 (dpSt σ (dpHeapCp1 nv sv n lA lB siv lp civ false) 16)
      (.retV w (cp1RhsK civ)) ch
      = .ok (.next (.storeK [cp1Ref civ] [w] (.seqn #[]) cp1Env2 cp1StTail),
          dpSt σ (dpHeapCp1 nv sv n lA lB siv lp civ false) 16, ch) := by
  with_unfolding_all rfl

/-- Copy-1 phase D: the store drained → the incremented dispatch and the
next exit test's delivery. 34 steps. -/
theorem cp1_D_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (civ : Int)
    (ch : Choices) :
    stepFnIter 34 (dpSt σ (dpHeapCp1 nv sv n lA lB siv lp civ false) 16)
      (.next (.storeK [] [] (.seqn #[]) cp1Env2 cp1StTail)) ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1))
              < nv))) cp1CmpK,
          dpSt σ (dpHeapCp1 nv sv n lA lB siv lp
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1)))
            false) 16, ch) := by
  with_unfolding_all rfl

/-- Copy-1 exit: test false → `var bv` declared and the second copy
loop's head. 39 steps. -/
theorem cp1_X_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (civ : Int)
    (ch : Choices) :
    stepFnIter 39 (dpSt σ (dpHeapCp1 nv sv n lA lB siv lp civ false) 16)
      (.retV (.bool false) cp1CmpK) ch
      = .ok (cp2HeadCfg,
          dpSt σ (dpHeapCp2 nv sv n lA lB siv lp civ zeros8 0 true) 19,
          ch) := by
  with_unfolding_all rfl

theorem cp2_A0_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 25
      (dpSt σ (dpHeapCp2 nv sv n lA lB siv lp c1v lq civ true) 19)
      cp2HeadCfg ch
      = .ok (.retV (.bool (decide (civ < nv))) cp2CmpK,
          dpSt σ (dpHeapCp2 nv sv n lA lB siv lp c1v lq civ false) 19,
          ch) := by
  with_unfolding_all rfl

theorem cp2_B1_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 16
      (dpSt σ (dpHeapCp2 nv sv n lA lB siv lp c1v lq civ false) 19)
      (.retV (.bool true) cp2CmpK) ch
      = .ok (.retV (.int civ .uint64)
            (.strictK .indexGet [bSliceV n] [] cp2Env2 (cp2RhsK civ)),
          dpSt σ (dpHeapCp2 nv sv n lA lB siv lp c1v lq civ false) 19,
          ch) := by
  with_unfolding_all rfl

theorem cp2_B2_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (civ : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1
      (dpSt σ (dpHeapCp2 nv sv n lA lB siv lp c1v lq civ false) 19)
      (.retV w (cp2RhsK civ)) ch
      = .ok (.next (.storeK [cp2Ref civ] [w] (.seqn #[]) cp2Env2 cp2StTail),
          dpSt σ (dpHeapCp2 nv sv n lA lB siv lp c1v lq civ false) 19,
          ch) := by
  with_unfolding_all rfl

theorem cp2_D_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 34
      (dpSt σ (dpHeapCp2 nv sv n lA lB siv lp c1v lq civ false) 19)
      (.next (.storeK [] [] (.seqn #[]) cp2Env2 cp2StTail)) ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1))
              < nv))) cp2CmpK,
          dpSt σ (dpHeapCp2 nv sv n lA lB siv lp c1v lq
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1)))
            false) 19, ch) := by
  with_unfolding_all rfl

/-- Copy-2 exit: test false → `var dot` declared and BOTH
`dotProduct(a, b)` arguments delivered at the drained `callArgsK`. 15
steps. -/
theorem cp2_X_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 15
      (dpSt σ (dpHeapCp2 nv sv n lA lB siv lp c1v lq civ false) 19)
      (.retV (.bool false) cp2CmpK) ch
      = .ok (.retV (bSliceV n) (dpCallArgsK n),
          dpSt σ (dpHeapCall nv sv n lA lB siv lp c1v lq civ) 20, ch) := by
  with_unfolding_all rfl

/-! ### The subject: prologue, loop, exit -/

/-- Subject P1: frame entry → `n := len(a)`'s apply point. 11 steps. -/
theorem sj_P1_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (c2v : Int) (ch : Choices) :
    stepFnIter 11
      (dpSt σ (dpHeapFrame nv sv n lA lB siv lp c1v lq c2v) 23)
      (.exec dotProductFunc.body sjFrameEnv frameKD) ch
      = .ok (.retV (aSliceV n) sjLenAK,
          dpSt σ
            (dpHeapFrame nv sv n lA lB siv lp c1v lq c2v
              ++ [(.base ⟨23⟩, icell 0)]) 24, ch) := by
  with_unfolding_all rfl

/-- Subject P2: `len(a)` delivered → the guard's `len(b)` apply point.
9 steps (the `n` store rides inside). -/
theorem sj_P2_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (c2v : Int) (w : Int) (ch : Choices) :
    stepFnIter 9
      (dpSt σ (dpHeapFrame nv sv n lA lB siv lp c1v lq c2v
        ++ [(.base ⟨23⟩, icell 0)]) 24)
      (.retV (.int w .int) sjNRhsK) ch
      = .ok (.retV (bSliceV n) sjLenBK,
          dpSt σ (dpHeapFrame nv sv n lA lB siv lp c1v lq c2v
            ++ [(.base ⟨23⟩, icell (IntKind.normalize .int w))]) 24,
          ch) := by
  with_unfolding_all rfl

/-- Subject P3: `len(b)` delivered → the guard test's delivery. 3
steps. -/
theorem sj_P3_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (c2v nsv : Int) (w : Int) (ch : Choices) :
    stepFnIter 3
      (dpSt σ (dpHeapFrame nv sv n lA lB siv lp c1v lq c2v
        ++ [(.base ⟨23⟩, icell nsv)]) 24)
      (.retV (.int w .int)
        (.strictK .lessCmp [] [.var "n"] sjEnvN sjGuardK)) ch
      = .ok (.retV (.bool (decide (w < nsv))) sjGuardK,
          dpSt σ (dpHeapFrame nv sv n lA lB siv lp c1v lq c2v
            ++ [(.base ⟨23⟩, icell nsv)]) 24, ch) := by
  with_unfolding_all rfl

/-- Subject P4: guard false → `acc`, `i`, `$forFirst` declared, first
dispatch → the exit test's delivery at `i = 0`. 69 steps. -/
theorem sj_P4_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (c2v nsv : Int) (ch : Choices) :
    stepFnIter 69
      (dpSt σ (dpHeapFrame nv sv n lA lB siv lp c1v lq c2v
        ++ [(.base ⟨23⟩, icell nsv)]) 24)
      (.retV (.bool false) sjGuardK) ch
      = .ok (.retV (.bool (decide ((0 : Int) < nsv))) sjCmpK,
          dpSt σ
            (dpHeapSubj nv sv n lA lB siv lp c1v lq c2v nsv 0 0 false) 27,
          ch) := by
  with_unfolding_all rfl

/-- Iteration I1: test true → the `a[i]` read's apply point. 16
steps. -/
theorem sj_I1_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (c2v nsv accv iv : Int) (ch : Choices) :
    stepFnIter 16
      (dpSt σ (dpHeapSubj nv sv n lA lB siv lp c1v lq c2v nsv accv iv false)
        27)
      (.retV (.bool true) sjCmpK) ch
      = .ok (.retV (.int iv .int) (sjIdxAK n accv),
          dpSt σ
            (dpHeapSubj nv sv n lA lB siv lp c1v lq c2v nsv accv iv false)
            27, ch) := by
  with_unfolding_all rfl

/-- Iteration I2: `a[i]` delivered → the `b[i]` read's apply point. 5
steps. -/
theorem sj_I2_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (c2v nsv accv iv av : Int) (ch : Choices) :
    stepFnIter 5
      (dpSt σ (dpHeapSubj nv sv n lA lB siv lp c1v lq c2v nsv accv iv false)
        27)
      (.retV (.int av .uint64) (sjMulK accv)) ch
      = .ok (.retV (.int iv .int) (sjIdxBK n accv av),
          dpSt σ
            (dpHeapSubj nv sv n lA lB siv lp c1v lq c2v nsv accv iv false)
            27, ch) := by
  with_unfolding_all rfl

/-- Iteration I3: `b[i]` delivered → the wrapped multiply, the wrapped
accumulate, the store, the incremented dispatch, the next exit test's
delivery. 38 steps, all definitional. -/
theorem sj_I3_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (c2v nsv accv iv av bv : Int) (ch : Choices) :
    stepFnIter 38
      (dpSt σ (dpHeapSubj nv sv n lA lB siv lp c1v lq c2v nsv accv iv false)
        27)
      (.retV (.int bv .uint64) (sjMulK2 accv av)) ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1))
              < nsv))) sjCmpK,
          dpSt σ
            (dpHeapSubj nv sv n lA lB siv lp c1v lq c2v nsv
              (IntKind.normalize .uint64
                (IntKind.normalize .uint64
                  (accv + IntKind.normalize .uint64 (av * bv))))
              (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
              false) 27, ch) := by
  with_unfolding_all rfl

/-- Exit X1: test false → break unwinding, the subject's
`$res0 = acc`, the return, the frame write-back into `dot`, and the
harness epilogue up to the `$res0 = av` ARRAY store point. 34 steps. -/
theorem sj_X1_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (c2v : Int) (r2 r3 : List Int)
    (r4 dv r22 nsv accv iv : Int) (ch : Choices) :
    stepFnIter 34
      (dpSt σ
        (dpHeapX nv sv n lA lB siv lp c1v lq c2v r2 r3 r4 dv r22 nsv accv
          iv) 27)
      (.retV (.bool false) sjCmpK) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨2⟩)) [] []]
            [.array ⟨lp.map (fun v => .int v .uint64)⟩] (.seqn #[])
            callEnvD epiTail1),
          dpSt σ
            (dpHeapX nv sv n lA lB siv lp c1v lq c2v r2 r3 r4
              (IntKind.normalize .uint64 (IntKind.normalize .uint64 accv))
              (IntKind.normalize .uint64 accv) nsv accv iv) 27, ch) := by
  with_unfolding_all rfl

/-- Exit X2: the `av` store drained → the `$res1 = bv` ARRAY store
point. 8 steps. -/
theorem sj_X2_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (c2v : Int) (r2 r3 : List Int)
    (r4 dv r22 nsv accv iv : Int) (ch : Choices) :
    stepFnIter 8
      (dpSt σ
        (dpHeapX nv sv n lA lB siv lp c1v lq c2v r2 r3 r4 dv r22 nsv accv
          iv) 27)
      (.next (.storeK [] [] (.seqn #[]) callEnvD epiTail1)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨3⟩)) [] []]
            [.array ⟨lq.map (fun v => .int v .uint64)⟩] (.seqn #[])
            callEnvD epiTail2),
          dpSt σ
            (dpHeapX nv sv n lA lB siv lp c1v lq c2v r2 r3 r4 dv r22 nsv
              accv iv) 27, ch) := by
  with_unfolding_all rfl

/-- Exit X3: the `bv` store drained → `$res2 = dot`, the return, the
harness frame exit, the driver terminal. 15 steps. -/
theorem sj_X3_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
    (lq : List Int) (c2v : Int) (r2 r3 : List Int)
    (r4 dv r22 nsv accv iv : Int) (ch : Choices) :
    stepFnIter 15
      (dpSt σ
        (dpHeapX nv sv n lA lB siv lp c1v lq c2v r2 r3 r4 dv r22 nsv accv
          iv) 27)
      (.next (.storeK [] [] (.seqn #[]) callEnvD epiTail2)) ch
      = .ok (.next .stop,
          dpSt σ
            (dpHeapX nv sv n lA lB siv lp c1v lq c2v r2 r3
              (IntKind.normalize .uint64 dv) dv r22 nsv accv iv) 27,
          ch) := by
  with_unfolding_all rfl

/-! ## The loop inductions (the P5 uniform-iteration schema) -/

/-- One setup iteration: `70` steps materialize `a[i] = seed + i` and
`b[i] = i + 1` (both wrapped) and return to the exit test. -/
theorem su_iter (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 63)
    (i : Nat) (hi : i < n) (ch : Choices) :
    stepFnIter 70
      (dpSt σ (dpHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
        (dpFamA i seed ++ List.replicate (n - i) 0)
        (dpFamB i ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false) 13)
      (.retV (.bool true) suCmpK) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) suCmpK,
          dpSt σ (dpHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
            (dpFamA (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
            (dpFamB (i + 1) ++ List.replicate (n - (i + 1)) 0)
            ((i + 1 : Nat) : Int) false) 13, ch) := by
  have hB1 := su_B1_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA i seed ++ List.replicate (n - i) 0)
    (dpFamB i ++ List.replicate (n - i) 0) ((i : Nat) : Int) ch
  rw [unorm_add_nat seed i] at hB1
  have hwA : (0 : Int) ≤ (((seed + i) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + i) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + i) (y := 2 ^ 64) (by omega)
    omega
  have hstA := storeTarget_slice_u64
    (σ := dpSt σ (dpHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
      (dpFamA i seed ++ List.replicate (n - i) 0)
      (dpFamB i ++ List.replicate (n - i) 0) ((i : Nat) : Int) false) 13)
    (a := ⟨6⟩) (off := 0) (len := n) (cap := n) (i := i) (n := n)
    (ik := .uint64) (l := dpFamA i seed ++ List.replicate (n - i) 0)
    (w := (((seed + i) % 2 ^ 64 : Nat) : Int))
    (lookup_su6 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
      (dpFamA i seed ++ List.replicate (n - i) 0)
      (dpFamB i ++ List.replicate (n - i) 0) ((i : Nat) : Int) false 13)
    (Nat.le_refl n) hi
    (by rw [List.length_append, dpFamA_length, List.length_replicate]; omega)
    (by rw [List.length_append, dpFamA_length, List.length_replicate]; omega)
    dpFamAZ_range hwA
  rw [Nat.zero_add, dpFamA_set hi] at hstA
  have h1 := stepFnIter_chain hB1 (stepFnIter_one (stepFn_store_step hstA))
  have hB2 := su_B2_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
    (dpFamB i ++ List.replicate (n - i) 0) ((i : Nat) : Int) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    unorm_nat_of_lt (by omega : i + 1 < 2 ^ 64)] at hB2
  have h2 := stepFnIter_chain h1 hB2
  have hwB : (0 : Int) ≤ ((i + 1 : Nat) : Int)
      ∧ ((i + 1 : Nat) : Int) < 2 ^ 64 := by omega
  have hstB := storeTarget_slice_u64
    (σ := dpSt σ (dpHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
      (dpFamA (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
      (dpFamB i ++ List.replicate (n - i) 0) ((i : Nat) : Int) false) 13)
    (a := ⟨9⟩) (off := 0) (len := n) (cap := n) (i := i) (n := n)
    (ik := .uint64) (l := dpFamB i ++ List.replicate (n - i) 0)
    (w := ((i + 1 : Nat) : Int))
    (lookup_su9 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
      (dpFamA (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
      (dpFamB i ++ List.replicate (n - i) 0) ((i : Nat) : Int) false 13)
    (Nat.le_refl n) hi
    (by rw [List.length_append, dpFamB_length, List.length_replicate]; omega)
    (by rw [List.length_append, dpFamB_length, List.length_replicate]; omega)
    (dpFamBZ_range (by omega)) hwB
  rw [Nat.zero_add, dpFamB_set hi] at hstB
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hstB))
  have hC := su_C_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
    (dpFamB (i + 1) ++ List.replicate (n - (i + 1)) 0)
    ((i : Nat) : Int) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    unorm_nat_of_lt (by omega : i + 1 < 2 ^ 64),
    unorm_nat_of_lt (by omega : i + 1 < 2 ^ 64)] at hC
  exact stepFnIter_chain h3 hC

/-- **The setup loop**: exactly `70·(n−i)` steps materialize both
families. -/
theorem su_loop (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 63) :
    ∀ i, i ≤ n → ∀ ch : Choices,
    stepFnIter (70 * (n - i))
      (dpSt σ (dpHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
        (dpFamA i seed ++ List.replicate (n - i) 0)
        (dpFamB i ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false) 13)
      (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
        suCmpK) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) suCmpK,
          dpSt σ (dpHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
            (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) false) 13, ch) := by
  intro i hin ch
  have hgen := stepFnIter_iterate (c := 70) (n := n)
    (T := fun j => dpSt σ (dpHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
      (dpFamA j seed ++ List.replicate (n - j) 0)
      (dpFamB j ++ List.replicate (n - j) 0) ((j : Nat) : Int) false) 13)
    (C := fun j => .retV (.bool (decide
      (((j : Nat) : Int) < ((n : Nat) : Int)))) suCmpK)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact su_iter σ n seed hn j hj ch')
    i hin ch
  simpa using hgen

/-- One copy-1 iteration: 53 steps copy `a[m]` into `av[m]`. -/
theorem cp1_iter (σ : ExecState) (n seed : Nat) (siv : Int) (m : Nat)
    (hn : n < 2 ^ 63) (hcap : n ≤ 8) (hm : m < n) (ch : Choices) :
    stepFnIter 53
      (dpSt σ (dpHeapCp1 ((n : Nat) : Int) ((seed : Nat) : Int) n
        (dpFamA n seed) (dpFamB n) siv (dpPreA m seed) ((m : Nat) : Int)
        false) 16)
      (.retV (.bool true) cp1CmpK) ch
      = .ok (.retV (.bool (decide
            (((m + 1 : Nat) : Int) < ((n : Nat) : Int)))) cp1CmpK,
          dpSt σ (dpHeapCp1 ((n : Nat) : Int) ((seed : Nat) : Int) n
            (dpFamA n seed) (dpFamB n) siv (dpPreA (m + 1) seed)
            ((m + 1 : Nat) : Int) false) 16, ch) := by
  have hB1 := cp1_B1_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) siv (dpPreA m seed) ((m : Nat) : Int) ch
  have hget : (⟨(dpFamA n seed).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + m]?
      = some (.int (((seed + m) % 2 ^ 64 : Nat) : Int) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by rw [dpFamA_length]; omega),
      dpFamA_getD hm]
  have hread := stepFn_strict_apply (done := [aSliceV n]) (env := cp1Env2)
    (k := cp1RhsK ((m : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .uint64)
      (lookup_cp1_6 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
        (dpFamA n seed) (dpFamB n) siv (dpPreA m seed) ((m : Nat) : Int)
        false 16)
      (Nat.le_refl n) hm hget)
  have hB2 := cp1_B2_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) siv (dpPreA m seed) ((m : Nat) : Int)
    (.int (((seed + m) % 2 ^ 64 : Nat) : Int) .uint64) ch
  have hw : (0 : Int) ≤ (((seed + m) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + m) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + m) (y := 2 ^ 64) (by omega)
    omega
  have hst := storeTarget_arrayLocal_u64 (a := ⟨13⟩) (N := 8) (i := m)
    (ik := .uint64) (l := dpPreA m seed)
    (w := (((seed + m) % 2 ^ 64 : Nat) : Int))
    (lookup_cp1_13 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
      (dpFamA n seed) (dpFamB n) siv (dpPreA m seed) ((m : Nat) : Int)
      false 16)
    (by rw [dpPreA_length (by omega)]; omega)
    (dpPreA_length (by omega)) dpPreA_range hw
  rw [dpPreA_set (by omega : m < 8)] at hst
  have hD := cp1_D_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) siv (dpPreA (m + 1) seed) ((m : Nat) : Int)
    ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_nat_of_lt (by omega : m + 1 < 2 ^ 64),
    unorm_nat_of_lt (by omega : m + 1 < 2 ^ 64)] at hD
  have h1 := stepFnIter_chain hB1 (stepFnIter_one hread)
  have h2 := stepFnIter_chain h1 hB2
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hst))
  exact stepFnIter_chain h3 hD

/-- **The first copy loop**: exactly `53·(n−m)` steps. -/
theorem cp1_loop (σ : ExecState) (n seed : Nat) (siv : Int)
    (hn : n < 2 ^ 63) (hcap : n ≤ 8) :
    ∀ m, m ≤ n → ∀ ch : Choices,
    stepFnIter (53 * (n - m))
      (dpSt σ (dpHeapCp1 ((n : Nat) : Int) ((seed : Nat) : Int) n
        (dpFamA n seed) (dpFamB n) siv (dpPreA m seed) ((m : Nat) : Int)
        false) 16)
      (.retV (.bool (decide (((m : Nat) : Int) < ((n : Nat) : Int))))
        cp1CmpK) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) cp1CmpK,
          dpSt σ (dpHeapCp1 ((n : Nat) : Int) ((seed : Nat) : Int) n
            (dpFamA n seed) (dpFamB n) siv (dpPreA n seed)
            ((n : Nat) : Int) false) 16, ch) := by
  intro m hmn ch
  have hgen := stepFnIter_iterate (c := 53) (n := n)
    (T := fun j => dpSt σ (dpHeapCp1 ((n : Nat) : Int) ((seed : Nat) : Int)
      n (dpFamA n seed) (dpFamB n) siv (dpPreA j seed) ((j : Nat) : Int)
      false) 16)
    (C := fun j => .retV (.bool (decide
      (((j : Nat) : Int) < ((n : Nat) : Int)))) cp1CmpK)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact cp1_iter σ n seed siv j hn hcap hj ch')
    m hmn ch
  simpa using hgen

/-- One copy-2 iteration: 53 steps copy `b[m]` into `bv[m]`. -/
theorem cp2_iter (σ : ExecState) (n seed : Nat) (siv c1v : Int) (m : Nat)
    (hn : n < 2 ^ 63) (hcap : n ≤ 8) (hm : m < n) (ch : Choices) :
    stepFnIter 53
      (dpSt σ (dpHeapCp2 ((n : Nat) : Int) ((seed : Nat) : Int) n
        (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v (dpPreB m)
        ((m : Nat) : Int) false) 19)
      (.retV (.bool true) cp2CmpK) ch
      = .ok (.retV (.bool (decide
            (((m + 1 : Nat) : Int) < ((n : Nat) : Int)))) cp2CmpK,
          dpSt σ (dpHeapCp2 ((n : Nat) : Int) ((seed : Nat) : Int) n
            (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v
            (dpPreB (m + 1)) ((m + 1 : Nat) : Int) false) 19, ch) := by
  have hB1 := cp2_B1_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v (dpPreB m)
    ((m : Nat) : Int) ch
  have hget : (⟨(dpFamB n).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + m]?
      = some (.int ((m + 1 : Nat) : Int) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by rw [dpFamB_length]; omega),
      dpFamB_getD hm]
  have hread := stepFn_strict_apply (done := [bSliceV n]) (env := cp2Env2)
    (k := cp2RhsK ((m : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .uint64)
      (lookup_cp2_9 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
        (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v (dpPreB m)
        ((m : Nat) : Int) false 19)
      (Nat.le_refl n) hm hget)
  have hB2 := cp2_B2_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v (dpPreB m)
    ((m : Nat) : Int) (.int ((m + 1 : Nat) : Int) .uint64) ch
  have hw : (0 : Int) ≤ ((m + 1 : Nat) : Int)
      ∧ ((m + 1 : Nat) : Int) < 2 ^ 64 := by omega
  have hst := storeTarget_arrayLocal_u64 (a := ⟨16⟩) (N := 8) (i := m)
    (ik := .uint64) (l := dpPreB m) (w := ((m + 1 : Nat) : Int))
    (lookup_cp2_16 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
      (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v (dpPreB m)
      ((m : Nat) : Int) false 19)
    (by rw [dpPreB_length (by omega)]; omega)
    (dpPreB_length (by omega)) (dpPreB_range (by omega)) hw
  rw [dpPreB_set (by omega : m < 8)] at hst
  have hD := cp2_D_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v (dpPreB (m + 1))
    ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_nat_of_lt (by omega : m + 1 < 2 ^ 64),
    unorm_nat_of_lt (by omega : m + 1 < 2 ^ 64)] at hD
  have h1 := stepFnIter_chain hB1 (stepFnIter_one hread)
  have h2 := stepFnIter_chain h1 hB2
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hst))
  exact stepFnIter_chain h3 hD

/-- **The second copy loop**: exactly `53·(n−m)` steps. -/
theorem cp2_loop (σ : ExecState) (n seed : Nat) (siv c1v : Int)
    (hn : n < 2 ^ 63) (hcap : n ≤ 8) :
    ∀ m, m ≤ n → ∀ ch : Choices,
    stepFnIter (53 * (n - m))
      (dpSt σ (dpHeapCp2 ((n : Nat) : Int) ((seed : Nat) : Int) n
        (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v (dpPreB m)
        ((m : Nat) : Int) false) 19)
      (.retV (.bool (decide (((m : Nat) : Int) < ((n : Nat) : Int))))
        cp2CmpK) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) cp2CmpK,
          dpSt σ (dpHeapCp2 ((n : Nat) : Int) ((seed : Nat) : Int) n
            (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v (dpPreB n)
            ((n : Nat) : Int) false) 19, ch) := by
  intro m hmn ch
  have hgen := stepFnIter_iterate (c := 53) (n := n)
    (T := fun j => dpSt σ (dpHeapCp2 ((n : Nat) : Int) ((seed : Nat) : Int)
      n (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v (dpPreB j)
      ((j : Nat) : Int) false) 19)
    (C := fun j => .retV (.bool (decide
      (((j : Nat) : Int) < ((n : Nat) : Int)))) cp2CmpK)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact cp2_iter σ n seed siv c1v j hn hcap hj ch')
    m hmn ch
  simpa using hgen

/-- One subject iteration: 61 steps, `acc` advances by the WRAPPED
product — `dpAcc` is exactly the machine's two normalizations. -/
theorem sj_iter (σ : ExecState) (n seed : Nat) (siv c1v c2v : Int)
    (j : Nat) (hn : n < 2 ^ 63) (hcap : n ≤ 8) (hj : j < n)
    (ch : Choices) :
    stepFnIter 61
      (dpSt σ (dpHeapSubj ((n : Nat) : Int) ((seed : Nat) : Int) n
        (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v (dpPreB n) c2v
        ((n : Nat) : Int) ((dpAcc seed j : Nat) : Int) ((j : Nat) : Int)
        false) 27)
      (.retV (.bool true) sjCmpK) ch
      = .ok (.retV (.bool (decide
            (((j + 1 : Nat) : Int) < ((n : Nat) : Int)))) sjCmpK,
          dpSt σ (dpHeapSubj ((n : Nat) : Int) ((seed : Nat) : Int) n
            (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v (dpPreB n)
            c2v ((n : Nat) : Int) ((dpAcc seed (j + 1) : Nat) : Int)
            ((j + 1 : Nat) : Int) false) 27, ch) := by
  have hI1 := sj_I1_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v (dpPreB n) c2v
    ((n : Nat) : Int) ((dpAcc seed j : Nat) : Int) ((j : Nat) : Int) ch
  have hgetA : (⟨(dpFamA n seed).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + j]?
      = some (.int (((seed + j) % 2 ^ 64 : Nat) : Int) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by rw [dpFamA_length]; omega),
      dpFamA_getD hj]
  have hreadA := stepFn_strict_apply (done := [aSliceV n]) (env := sjEnv2)
    (k := sjMulK ((dpAcc seed j : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .int)
      (lookup_subj6 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
        (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v (dpPreB n) c2v
        ((n : Nat) : Int) ((dpAcc seed j : Nat) : Int) ((j : Nat) : Int)
        false 27)
      (Nat.le_refl n) hj hgetA)
  have hI2 := sj_I2_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v (dpPreB n) c2v
    ((n : Nat) : Int) ((dpAcc seed j : Nat) : Int) ((j : Nat) : Int)
    (((seed + j) % 2 ^ 64 : Nat) : Int) ch
  have hgetB : (⟨(dpFamB n).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + j]?
      = some (.int ((j + 1 : Nat) : Int) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by rw [dpFamB_length]; omega),
      dpFamB_getD hj]
  have hreadB := stepFn_strict_apply (done := [bSliceV n]) (env := sjEnv2)
    (k := sjMulK2 ((dpAcc seed j : Nat) : Int)
      (((seed + j) % 2 ^ 64 : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .int)
      (lookup_subj9 σ ((n : Nat) : Int) ((seed : Nat) : Int) n
        (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v (dpPreB n) c2v
        ((n : Nat) : Int) ((dpAcc seed j : Nat) : Int) ((j : Nat) : Int)
        false 27)
      (Nat.le_refl n) hj hgetB)
  have hI3 := sj_I3_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v (dpPreB n) c2v
    ((n : Nat) : Int) ((dpAcc seed j : Nat) : Int) ((j : Nat) : Int)
    (((seed + j) % 2 ^ 64 : Nat) : Int) ((j + 1 : Nat) : Int) ch
  rw [unorm_mul_nat ((seed + j) % 2 ^ 64) (j + 1),
    unorm_add_nat (dpAcc seed j) (((seed + j) % 2 ^ 64) * (j + 1) % 2 ^ 64),
    show (dpAcc seed j + ((seed + j) % 2 ^ 64) * (j + 1) % 2 ^ 64) % 2 ^ 64
      = dpAcc seed (j + 1) from rfl,
    unorm_nat_of_lt (dpAcc_lt seed (j + 1)),
    show ((j : Nat) : Int) + 1 = ((j + 1 : Nat) : Int) from by omega,
    inorm_nat_of_lt (by omega : j + 1 < 2 ^ 63),
    inorm_nat_of_lt (by omega : j + 1 < 2 ^ 63)] at hI3
  have h1 := stepFnIter_chain hI1 (stepFnIter_one hreadA)
  have h2 := stepFnIter_chain h1 hI2
  have h3 := stepFnIter_chain h2 (stepFnIter_one hreadB)
  exact stepFnIter_chain h3 hI3

/-- **The accumulate loop**: exactly `61·(n−j)` steps land
`acc = dpAcc seed n`. -/
theorem sj_loop (σ : ExecState) (n seed : Nat) (siv c1v c2v : Int)
    (hn : n < 2 ^ 63) (hcap : n ≤ 8) :
    ∀ j, j ≤ n → ∀ ch : Choices,
    stepFnIter (61 * (n - j))
      (dpSt σ (dpHeapSubj ((n : Nat) : Int) ((seed : Nat) : Int) n
        (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v (dpPreB n) c2v
        ((n : Nat) : Int) ((dpAcc seed j : Nat) : Int) ((j : Nat) : Int)
        false) 27)
      (.retV (.bool (decide (((j : Nat) : Int) < ((n : Nat) : Int))))
        sjCmpK) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) sjCmpK,
          dpSt σ (dpHeapSubj ((n : Nat) : Int) ((seed : Nat) : Int) n
            (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v (dpPreB n)
            c2v ((n : Nat) : Int) ((dpAcc seed n : Nat) : Int)
            ((n : Nat) : Int) false) 27, ch) := by
  intro j hjn ch
  have hgen := stepFnIter_iterate (c := 61) (n := n)
    (T := fun j => dpSt σ (dpHeapSubj ((n : Nat) : Int) ((seed : Nat) : Int)
      n (dpFamA n seed) (dpFamB n) siv (dpPreA n seed) c1v (dpPreB n) c2v
      ((n : Nat) : Int) ((dpAcc seed j : Nat) : Int) ((j : Nat) : Int)
      false) 27)
    (C := fun j => .retV (.bool (decide
      (((j : Nat) : Int) < ((n : Nat) : Int)))) sjCmpK)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact sj_iter σ n seed siv c1v c2v j hn hcap hj ch')
    j hjn ch
  simpa using hgen

/-! ## The run, end to end -/

/-- The `enterFrame` discharge at the pinned program: the one
program-consulting step, and (with the pins) the only place
`dotprodLowered` is unfolded. -/
theorem dp_enterFrame_fact (n : Nat) (nv sv : Int) (lA lB : List Int)
    (siv : Int) (lp : List Int) (c1v : Int) (lq : List Int) (c2v : Int) :
    enterFrame
        (dpSt dpProg (dpHeapCall nv sv n lA lB siv lp c1v lq c2v) 20)
        ⟨"dotProduct"⟩ [aSliceV n, bSliceV n]
      = .ok (dotProductFunc, sjFrameEnv, [.base ⟨22⟩],
          dpSt dpProg (dpHeapFrame nv sv n lA lB siv lp c1v lq c2v) 23) := by
  with_unfolding_all rfl

/-- **The harness run, PROGRAM-generic**: exactly `237·n + 398` steps
from the machine entry's post-prelude seed to the driver terminal, with
`av = dpPreA n seed` and `bv = dpPreB n` in the result-array cells and
`dpAcc seed n` in the result-scalar cell. Deterministic throughout: the
subject consumes no nondeterminism choice, so the stream rides through
unchanged. -/
theorem dp_runs_generic (σ : ExecState) (n seed : Nat) (hcap : n ≤ 8)
    (henter : ∀ (lA lB : List Int) (siv : Int) (lp : List Int) (c1v : Int)
      (lq : List Int) (c2v : Int),
      enterFrame
          (dpSt σ (dpHeapCall ((n : Nat) : Int) ((seed : Nat) : Int) n lA lB
            siv lp c1v lq c2v) 20)
          ⟨"dotProduct"⟩ [aSliceV n, bSliceV n]
        = .ok (dotProductFunc, sjFrameEnv, [.base ⟨22⟩],
            dpSt σ (dpHeapFrame ((n : Nat) : Int) ((seed : Nat) : Int) n lA
              lB siv lp c1v lq c2v) 23))
    (ch : Choices) :
    stepFnIter (237 * n + 398)
      (dpSt σ (dpHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)) 5) dpHC0 ch
      = .ok (.next .stop,
          dpSt σ
            (dpHeapX ((n : Nat) : Int) ((seed : Nat) : Int) n
              (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
              ((n : Nat) : Int) (dpPreB n) ((n : Nat) : Int)
              (dpPreA n seed) (dpPreB n) ((dpAcc seed n : Nat) : Int)
              ((dpAcc seed n : Nat) : Int) ((dpAcc seed n : Nat) : Int)
              ((n : Nat) : Int) ((dpAcc seed n : Nat) : Int)
              ((n : Nat) : Int)) 27, ch) := by
  have hn : n < 2 ^ 63 := by omega
  have hAccLt := dpAcc_lt seed n
  -- ENTRY
  have hE1 := dp_E1_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) ch
  have hmkA := stepFnIter_one
    (stepFn_makeSlice_u64_step (env := envC12D)
      (k := .seq [dpS2, dpS3, dpS4, dpS5, dpS6, dpS7, dpS8, dpS9, dpS10,
        dpS11] envC12D dpStop)
      (dp_makeA_apply σ ((n : Nat) : Int) ((seed : Nat) : Int) n ch))
  have hE2 := dp_E2_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n ch
  have hmkB := stepFnIter_one
    (stepFn_makeSlice_u64_step (env := envC13D)
      (k := .seq [dpS4, dpS5, dpS6, dpS7, dpS8, dpS9, dpS10, dpS11]
        envC13D dpStop)
      (dp_makeB_apply σ ((n : Nat) : Int) ((seed : Nat) : Int) n ch))
  have hE3 := dp_E3_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n ch
  have hA0 := su_A0_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (List.replicate n 0) (List.replicate n 0) 0 ch
  have hSU := su_loop σ n seed hn 0 (by omega) ch
  rw [show ((0 : Nat) : Int) = (0 : Int) from rfl,
    show dpFamA 0 seed ++ List.replicate (n - 0) 0 = List.replicate n 0 from
      by simp [dpFamA],
    show dpFamB 0 ++ List.replicate (n - 0) 0 = List.replicate n 0 from
      by simp [dpFamB]] at hSU
  have hS1 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hE1 hmkA) hE2)
      hmkB) hE3) hA0) hSU
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hS1
  -- SETUP EXIT + COPY 1
  have hX := su_X_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) ch
  have hcA0 := cp1_A0_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) zeros8 0 ch
  have hCP1 := cp1_loop σ n seed ((n : Nat) : Int) hn hcap 0 (by omega) ch
  rw [show ((0 : Nat) : Int) = (0 : Int) from rfl,
    show dpPreA 0 seed = zeros8 from dpPreA_zero seed] at hCP1
  have hS2 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hS1 hX)
    hcA0) hCP1
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hS2
  -- COPY 1 EXIT + COPY 2
  have hX1 := cp1_X_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
    ((n : Nat) : Int) ch
  have hcB0 := cp2_A0_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
    ((n : Nat) : Int) zeros8 0 ch
  have hCP2 := cp2_loop σ n seed ((n : Nat) : Int) ((n : Nat) : Int) hn hcap
    0 (by omega) ch
  rw [show ((0 : Nat) : Int) = (0 : Int) from rfl,
    show dpPreB 0 = zeros8 from dpPreB_zero] at hCP2
  have hS3 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hS2 hX1)
    hcB0) hCP2
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hS3
  -- COPY 2 EXIT + THE CALL
  have hX2 := cp2_X_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
    ((n : Nat) : Int) (dpPreB n) ((n : Nat) : Int) ch
  have hent := stepFnIter_one (ch := ch)
    (stepFn_call_enter (plans := dpCallPlans) (env := callEnvD)
      (k := afterCallK) (vals := [aSliceV n]) (v := bSliceV n)
      (henter (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
        ((n : Nat) : Int) (dpPreB n) ((n : Nat) : Int)))
  have hS4 := stepFnIter_chain (stepFnIter_chain hS3 hX2) hent
  -- SUBJECT PROLOGUE
  have hP1 := sj_P1_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
    ((n : Nat) : Int) (dpPreB n) ((n : Nat) : Int) ch
  have hlenA := stepFnIter_one
    (stepFn_strict_apply (done := []) (env := sjEnvN) (k := sjNRhsK)
      (ch := ch)
      (applyStrictOp_len_slice
        (σ := dpSt σ (dpHeapFrame ((n : Nat) : Int) ((seed : Nat) : Int) n
          (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
          ((n : Nat) : Int) (dpPreB n) ((n : Nat) : Int)
          ++ [(.base ⟨23⟩, icell 0)]) 24)
        (b := .base ⟨6⟩) (off := 0) (len := n) (cap := n) (elem := tU64)
        (Nat.le_refl n)))
  have hP2 := sj_P2_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
    ((n : Nat) : Int) (dpPreB n) ((n : Nat) : Int) ((n : Nat) : Int) ch
  rw [inorm_nat_of_lt hn] at hP2
  have hlenB := stepFnIter_one
    (stepFn_strict_apply (done := []) (env := sjEnvN)
      (k := .strictK .lessCmp [] [.var "n"] sjEnvN sjGuardK) (ch := ch)
      (applyStrictOp_len_slice
        (σ := dpSt σ (dpHeapFrame ((n : Nat) : Int) ((seed : Nat) : Int) n
          (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
          ((n : Nat) : Int) (dpPreB n) ((n : Nat) : Int)
          ++ [(.base ⟨23⟩, icell ((n : Nat) : Int))]) 24)
        (b := .base ⟨9⟩) (off := 0) (len := n) (cap := n) (elem := tU64)
        (Nat.le_refl n)))
  have hP3 := sj_P3_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
    ((n : Nat) : Int) (dpPreB n) ((n : Nat) : Int) ((n : Nat) : Int)
    ((n : Nat) : Int) ch
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hP3
  have hP4 := sj_P4_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
    ((n : Nat) : Int) (dpPreB n) ((n : Nat) : Int) ((n : Nat) : Int) ch
  have hS5 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hS4 hP1) hlenA)
      hP2) hlenB) hP3) hP4
  -- THE ACCUMULATE LOOP
  have hSJ := sj_loop σ n seed ((n : Nat) : Int) ((n : Nat) : Int)
    ((n : Nat) : Int) hn hcap 0 (by omega) ch
  rw [show ((0 : Nat) : Int) = (0 : Int) from rfl,
    show ((dpAcc seed 0 : Nat) : Int) = (0 : Int) from by simp [dpAcc]]
    at hSJ
  have hS6 := stepFnIter_chain hS5 hSJ
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hS6
  -- THE EXIT (the state family shifts to `dpHeapX`; the fronts agree)
  have hbridge :
      dpSt σ (dpHeapSubj ((n : Nat) : Int) ((seed : Nat) : Int) n
        (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
        ((n : Nat) : Int) (dpPreB n) ((n : Nat) : Int) ((n : Nat) : Int)
        ((dpAcc seed n : Nat) : Int) ((n : Nat) : Int) false) 27
      = dpSt σ (dpHeapX ((n : Nat) : Int) ((seed : Nat) : Int) n
          (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
          ((n : Nat) : Int) (dpPreB n) ((n : Nat) : Int) zeros8 zeros8 0 0
          0 ((n : Nat) : Int) ((dpAcc seed n : Nat) : Int)
          ((n : Nat) : Int)) 27 := rfl
  rw [hbridge] at hS6
  have hXa := sj_X1_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
    ((n : Nat) : Int) (dpPreB n) ((n : Nat) : Int) zeros8 zeros8 0 0 0
    ((n : Nat) : Int) ((dpAcc seed n : Nat) : Int) ((n : Nat) : Int) ch
  rw [unorm_nat_of_lt hAccLt, unorm_nat_of_lt hAccLt] at hXa
  have hS7 := stepFnIter_chain hS6 hXa
  -- the `$res0 = av` array store
  have hstAv : storeTarget
      (dpSt σ (dpHeapX ((n : Nat) : Int) ((seed : Nat) : Int) n
        (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
        ((n : Nat) : Int) (dpPreB n) ((n : Nat) : Int) zeros8 zeros8 0
        ((dpAcc seed n : Nat) : Int) ((dpAcc seed n : Nat) : Int)
        ((n : Nat) : Int) ((dpAcc seed n : Nat) : Int) ((n : Nat) : Int))
        27)
      (.chain (.addr (.base ⟨2⟩)) [] [])
      (.array ⟨(dpPreA n seed).map (fun v => .int v .uint64)⟩)
      = .ok (dpSt σ (dpHeapX ((n : Nat) : Int) ((seed : Nat) : Int) n
          (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
          ((n : Nat) : Int) (dpPreB n) ((n : Nat) : Int) (dpPreA n seed)
          zeros8 0 ((dpAcc seed n : Nat) : Int)
          ((dpAcc seed n : Nat) : Int) ((n : Nat) : Int)
          ((dpAcc seed n : Nat) : Int) ((n : Nat) : Int)) 27) :=
    storeTarget_addr
      (lookup_X2 σ ((n : Nat) : Int) ((seed : Nat) : Int) n (dpFamA n seed)
        (dpFamB n) ((n : Nat) : Int) (dpPreA n seed) ((n : Nat) : Int)
        (dpPreB n) ((n : Nat) : Int) zeros8 zeros8 0
        ((dpAcc seed n : Nat) : Int) ((dpAcc seed n : Nat) : Int)
        ((n : Nat) : Int) ((dpAcc seed n : Nat) : Int) ((n : Nat) : Int)
        27)
      (normalizeValueForTy_arr_u64 (dpPreA_length hcap) dpPreA_range)
  have hS8 := stepFnIter_chain hS7
    (stepFnIter_one (stepFn_store_step hstAv))
  have hXb := sj_X2_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
    ((n : Nat) : Int) (dpPreB n) ((n : Nat) : Int) (dpPreA n seed) zeros8
    0 ((dpAcc seed n : Nat) : Int) ((dpAcc seed n : Nat) : Int)
    ((n : Nat) : Int) ((dpAcc seed n : Nat) : Int) ((n : Nat) : Int) ch
  have hS9 := stepFnIter_chain hS8 hXb
  -- the `$res1 = bv` array store
  have hstBv : storeTarget
      (dpSt σ (dpHeapX ((n : Nat) : Int) ((seed : Nat) : Int) n
        (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
        ((n : Nat) : Int) (dpPreB n) ((n : Nat) : Int) (dpPreA n seed)
        zeros8 0 ((dpAcc seed n : Nat) : Int) ((dpAcc seed n : Nat) : Int)
        ((n : Nat) : Int) ((dpAcc seed n : Nat) : Int) ((n : Nat) : Int))
        27)
      (.chain (.addr (.base ⟨3⟩)) [] [])
      (.array ⟨(dpPreB n).map (fun v => .int v .uint64)⟩)
      = .ok (dpSt σ (dpHeapX ((n : Nat) : Int) ((seed : Nat) : Int) n
          (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
          ((n : Nat) : Int) (dpPreB n) ((n : Nat) : Int) (dpPreA n seed)
          (dpPreB n) 0 ((dpAcc seed n : Nat) : Int)
          ((dpAcc seed n : Nat) : Int) ((n : Nat) : Int)
          ((dpAcc seed n : Nat) : Int) ((n : Nat) : Int)) 27) :=
    storeTarget_addr
      (lookup_X3 σ ((n : Nat) : Int) ((seed : Nat) : Int) n (dpFamA n seed)
        (dpFamB n) ((n : Nat) : Int) (dpPreA n seed) ((n : Nat) : Int)
        (dpPreB n) ((n : Nat) : Int) (dpPreA n seed) zeros8 0
        ((dpAcc seed n : Nat) : Int) ((dpAcc seed n : Nat) : Int)
        ((n : Nat) : Int) ((dpAcc seed n : Nat) : Int) ((n : Nat) : Int)
        27)
      (normalizeValueForTy_arr_u64 (dpPreB_length hcap)
        (dpPreB_range (by omega)))
  have hS10 := stepFnIter_chain hS9
    (stepFnIter_one (stepFn_store_step hstBv))
  have hXc := sj_X3_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dpFamA n seed) (dpFamB n) ((n : Nat) : Int) (dpPreA n seed)
    ((n : Nat) : Int) (dpPreB n) ((n : Nat) : Int) (dpPreA n seed)
    (dpPreB n) 0 ((dpAcc seed n : Nat) : Int) ((dpAcc seed n : Nat) : Int)
    ((n : Nat) : Int) ((dpAcc seed n : Nat) : Int) ((n : Nat) : Int) ch
  rw [unorm_nat_of_lt hAccLt] at hXc
  have hS11 := stepFnIter_chain hS10 hXc
  rw [show 237 * n + 398
      = 10 + 1 + 22 + 1 + 42 + 25 + 70 * (n - 0) + 39 + 25 + 53 * (n - 0)
        + 39 + 25 + 53 * (n - 0) + 15 + 1 + 11 + 1 + 9 + 1 + 3 + 69
        + 61 * (n - 0) + 34 + 1 + 8 + 1 + 15 from by omega]
  exact hS11

/-! ## The user-facing statements -/

/-- The final-state readback: the three result cells, in declaration
order. -/
theorem dp_readback (σ : ExecState) (n seed : Nat) :
    loadMany
      (dpSt σ
        (dpHeapX ((n : Nat) : Int) ((seed : Nat) : Int) n (dpFamA n seed)
          (dpFamB n) ((n : Nat) : Int) (dpPreA n seed) ((n : Nat) : Int)
          (dpPreB n) ((n : Nat) : Int) (dpPreA n seed) (dpPreB n)
          ((dpAcc seed n : Nat) : Int) ((dpAcc seed n : Nat) : Int)
          ((dpAcc seed n : Nat) : Int) ((n : Nat) : Int)
          ((dpAcc seed n : Nat) : Int) ((n : Nat) : Int)) 27)
      [.base ⟨2⟩, .base ⟨3⟩, .base ⟨4⟩]
      = .ok [.array ⟨(dpPreA n seed).map (fun v => .int v .uint64)⟩,
             .array ⟨(dpPreB n).map (fun v => .int v .uint64)⟩,
             .int ((dpAcc seed n : Nat) : Int) .uint64] := by
  with_unfolding_all rfl

/-- **THE HEADLINE (§11 harness form, S3 RELATIONAL)**: for every
`n ≤ 8` and EVERY `seed < 2^64` — the wrap region included — running
the Go harness `dotprod_harness_r(n, seed)` through the machine's
native function entry completes normally past one fuel bound, at every
nondeterminism-choice stream, and returns THREE values: two length-`n`
value lists `av`/`bv` as the fixed-cap arrays the Go returns, and
`dotSpec av bv` — the mathematical dot product `Σ avᵢ·bvᵢ` of the
returned lists, reduced mod 2^64. The postcondition is a relation over
the RETURNED DATA — no family function appears in it.

Honesty clauses, recorded rather than hidden:

* **THE ARITHMETIC WRAPS, AND THE CLAIM SAYS SO.** `a[i]*b[i]` and the
  accumulation are uint64 and genuinely reduce mod 2^64; `dotSpec` is
  `(Σ aᵢ·bᵢ) % 2^64` and the theorem covers the FULL `seed < 2^64`
  domain — no hypothesis excludes the wrap region (the corpus rows
  `four-wrap`, `one-wrap`, `harness-r-wrap-max`, `harness-r-wrap-62`
  pin it differentially). The single final reduction equals the
  machine's per-step wrapping because `mod` distributes over the sum
  (`dpAcc_eq`) — that equality is proved, not assumed. Machine-integer
  honesty (FD-E3); compare `Fib.lean` (same wrapped-claim shape) and
  `PowMod.lean` (the opposite choice, excluding its wrap region, with
  its own disclosure). Attribution: the program's own arithmetic.
* **`dotSpec` is mathematics, not a loop restatement**: one modular
  reduction of the true integer sum `(zipWith (·*·) av bv).sum`. The
  loop-shaped accumulator `dpAcc` (product wrapped, then sum wrapped,
  per step) is proof-side only, bridged by `dotSpec_fam`; it does not
  appear in the statement.
* **`∃ av bv` is family-determined.** The witnesses are
  `dpFamA n seed = [seed, seed+1, …]` (wrapped) and
  `dpFamB n = [1, …, n]`; the statement merely avoids SAYING so —
  exactly as in `Histogram`'s headline. Making the input genuine
  ∀-data needs the ghost rung-1 annotation, which is designed and not
  built.
* **The cap `n ≤ 8` is a toy bound.** Go's pass-by-value fragment
  cannot return unbounded data, so the harness returns `[8]uint64`
  zero-padded past `n`; the copy loops exist only so the multiplied
  values can cross the observation boundary.
* **The subject's min-length guard is NOT exercised by this harness**
  (both slices have length `n`, so `len(b) < n` is false on every run
  here); the mismatched-length corpus row `uneven` pins that branch
  differentially. The theorem claims the harness's runs, nothing more.
* **The fuel bound `237·n + 398` is EXACT for this harness** — every
  loop iteration is branch-free, so the composed step count is an
  equality, and the probe-measured counts coincide with it at
  `n = 0…8` (398, 635, …, 2294). Bound and measurement agree here;
  neither is presented as the other.
* **`∀ ch` is vacuous here and stated anyway.** The subject consumes
  no nondeterminism choice; the quantifier records that rather than
  hiding a `Choices` argument.
* **Machine idealization** as in the other entries: entry from an
  empty heap, an unbounded heap, allocation always succeeds. -/
theorem dotprod_ok (n seed : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64) :
    ∃ av bv : List Int, av.length = n ∧ bv.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel dotprodLowered.typeDefs.toList
            dotprodLowered.funcs dotprodHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            dotprodLowered.methods ch
          = .ok { values := #[dpArr8 av, dpArr8 bv,
                              .int (dotSpec av bv) .uint64] } := by
  refine ⟨dpFamA n seed, dpFamB n, dpFamA_length n seed, dpFamB_length n,
    237 * n + 398, fun fuel hfuel ch => ?_⟩
  have hrun := dp_runs_generic dpProg n seed hcap
    (fun lA lB siv lp c1v lq c2v =>
      dp_enterFrame_fact n ((n : Nat) : Int) ((seed : Nat) : Int) lA lB siv
        lp c1v lq c2v) ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - (237 * n + 398))
  rw [show 237 * n + 398 + (fuel - (237 * n + 398)) = fuel from by omega]
    at hfold
  have hst : dpHSeed ((n : Nat) : Int) ((seed : Nat) : Int)
      = dpSt dpProg (dpHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)) 5 := rfl
  rw [dpH_entry_eq (n : Int) (seed : Int) fuel ch,
    unorm_nat_of_lt (by omega : n < 2 ^ 64), unorm_nat_of_lt hseed,
    hst, hfold, runConfig_next_stop]
  simp only [bind, Except.bind, dp_readback, pure, Except.pure]
  rw [dpArr8, dpArr8, ← dpPreA_full, ← dpPreB_full, dotSpec_fam]

/-- **The D1 run-conditioned twin**: ANY successful completion of the
harness entry, at any fuel and any choice stream, returns exactly those
three values — derived from `dotprod_ok` through the shared
`harness_readout_of_total` bridge; nothing is re-proven. -/
theorem dotprod_readout (n seed : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) :
    ∃ av bv : List Int, av.length = n ∧ bv.length = n ∧
      ∀ (fuel : Nat) (ch : Choices) (r : Result),
        runFunctionWithContextM fuel dotprodLowered.typeDefs.toList
            dotprodLowered.funcs dotprodHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            dotprodLowered.methods ch
          = .ok r →
        r = { values := #[dpArr8 av, dpArr8 bv,
                          .int (dotSpec av bv) .uint64] } := by
  obtain ⟨av, bv, hla, hlb, htot⟩ := dotprod_ok n seed hcap hseed
  exact ⟨av, bv, hla, hlb, harness_readout_of_total htot⟩

end GoLean.Examples.DotProduct
