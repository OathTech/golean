import GoLeanProofs.Examples.KadaneProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.EntryEq
import GoLeanProofs.Laws.StmtOps

/-!
# Kadane — the `kadane` example (Gallery Campaign G1)

Go source: `Corpus/coverage/exec/examples/kadane/main.go` (14 rows,
differentially green against `go run`). The lowering is pinned by
`scripts/check-golden` against `baselines/golden/kadane-lowered.repr`
and carried in `GoLeanProofs.Examples.KadaneProgram`.

The subject is the running-best maximum-subarray scan (Kadane's
algorithm) over `[]int64` — the wave's only SIGNED example. The
harness is the S3 RELATIONAL shape: `kadane_harness_r(n, seed)` builds
the alternating-sign family `s[i] = seed + i`, odd indices negated,
copies it into the fixed-cap `[8]int64` pre-state array, runs
`kadane(s)`, and returns `(pre, best)` so the postcondition is a
relation over the RETURNED DATA — `best = maxSubarraySum vals` with
`vals` the length-`n` value list the returned array carries.

THE HEADLINE (`kadane_ok`) is stated HERE, in the root, so the
aggregator's `import GoLeanProofs.Examples.Kadane` reaches it by name
(the C-H4/C-H5 shape, adopted from birth).

**The spec is the mathematics, not the scan.** `maxSubarraySum` is the
maximum over ALL non-empty contiguous segments' sums (`segments` +
`List.max?`), with `0` for the empty list — the Go source's own
documented empty-slice definition. The loop-shaped scan functions
(`kadCur`/`kadBest`) are proof-side only and are bridged to the
mathematics by `kadCur_eq_maxEnd`/`kadBest_eq_maxSub`; they never
appear in the headline's statement closure.
-/

namespace GoLean.Examples.Kadane

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## The harness `Func`, verbatim from the pinned lowering, in the
readable dot-notation form (the pin below keeps holding by `rfl`). -/

/-- The setup loop's per-iteration store block: `s[i] = seed + i`, then
the odd-index negation `if i%2 == 1 { s[i] = -s[i] }`. -/
abbrev kdSuStoreBlock : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
        (.add (.var "seed") (.var "i"))],
      .ifThenElse
        (.eqCmp (.int .int64)
          (.mod (.var "i") (.intLit 2 .int64)) (.intLit 1 .int64))
        (.block #[]
          #[.seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
              (.neg (.indexGet (.var "s") (.var "i")))]])
        (.seqn #[])]

abbrev kdSuWhileBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .int64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n"))
        (.seqn #[]) .breakStmt,
      kdSuStoreBlock]

abbrev kdCpStoreBlock : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.ref "pre") (.var "i")))
        (.indexGet (.var "s") (.var "i"))]]

abbrev kdCpWhileBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .int64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n"))
        (.seqn #[]) .breakStmt,
      kdCpStoreBlock]

abbrev kdS1 : Stmt :=
  .seqn #[.initialization { id := "$c8", typ := .slice (.int .int64) },
          .makeSlice (.var "$c8") (.int .int64) (.var "n") none]
abbrev kdS2 : Stmt :=
  .seqn #[.initialization { id := "s", typ := .slice (.int .int64) },
          .assign (.var "s") (.var "$c8")]
abbrev kdS3 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .int64 },
              .assign (.var "i") (.intLit 0 .int64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) kdSuWhileBody]]
abbrev kdS4 : Stmt :=
  .seqn #[.initialization { id := "pre", typ := .array 8 (.int .int64) }]
abbrev kdS5 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .int64 },
              .assign (.var "i") (.intLit 0 .int64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) kdCpWhileBody]]
abbrev kdS6 : Stmt :=
  .seqn #[.initialization { id := "best", typ := .int .int64 },
          .call #[.var "best"] { key := "kadane" } #[.var "s"]]
abbrev kdS7 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "pre"),
          .assign (.var "$res1") (.var "best"),
          .returnStmt]

/-- The harness `Func`, verbatim from the pinned lowering (the pin below
ties it by `rfl`). -/
def kadaneHarnessRFunc : Func :=
{ id := { key := "kadane_harness_r" },
  args := #[{ id := "n", typ := .int .int64 },
            { id := "seed", typ := .int .int64 }],
  results := #[{ id := "$res0", typ := .array 8 (.int .int64) },
               { id := "$res1", typ := .int .int64 }],
  body := .block #[] #[kdS1, kdS2, kdS3, kdS4, kdS5, kdS6, kdS7],
  variadic := false,
  wrapper := false }

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem kadaneHarnessRFunc_pin :
    findFunctionIn? kadaneLowered.funcs ⟨"kadane_harness_r"⟩
    = some kadaneHarnessRFunc := rfl

/-! ## The subject `Func`, verbatim from the pinned lowering -/

abbrev kLenS : Expr := .length (.var "s") (some (.slice (.int .int64)))

abbrev kGuardThen : Stmt :=
  .block #[] #[.seqn #[.assign (.var "$res0") (.intLit 0 .int64),
                       .returnStmt]]
abbrev kGuard : Stmt :=
  .ifThenElse (.eqCmp (.int .int) kLenS (.intLit 0 .int))
    kGuardThen (.seqn #[])
abbrev kBestInit : Stmt :=
  .seqn #[.initialization { id := "best", typ := .int .int64 },
          .assign (.var "best") (.indexGet (.var "s") (.intLit 0 .int))]
abbrev kCurInit : Stmt :=
  .seqn #[.initialization { id := "cur", typ := .int .int64 },
          .assign (.var "cur") (.indexGet (.var "s") (.intLit 0 .int))]
abbrev kCurIf : Stmt :=
  .ifThenElse (.lessCmp (.var "cur") (.intLit 0 .int64))
    (.block #[] #[.seqn #[.assign (.var "cur")
        (.indexGet (.var "s") (.var "i"))]])
    (.block #[] #[.seqn #[.assign (.var "cur")
        (.add (.var "cur") (.indexGet (.var "s") (.var "i")))]])
abbrev kBestIf : Stmt :=
  .ifThenElse (.greaterCmp (.var "cur") (.var "best"))
    (.block #[] #[.seqn #[.assign (.var "best") (.var "cur")]])
    (.seqn #[])
abbrev kWhileBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .int))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") kLenS)
        (.seqn #[]) .breakStmt,
      .block #[] #[kCurIf, kBestIf]]
abbrev kLoopBlock : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .int },
              .assign (.var "i") (.intLit 1 .int)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) kWhileBody]]
abbrev kEpilogue : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "best"), .returnStmt]

/-- The subject `Func`, verbatim from the pinned lowering. -/
def kadaneFunc : Func :=
  { id := { key := "kadane" },
    args := #[{ id := "s", typ := .slice (.int .int64) }],
    results := #[{ id := "$res0", typ := .int .int64 }],
    body := .block #[] #[kGuard, kBestInit, kCurInit, kLoopBlock, kEpilogue],
    variadic := false, wrapper := false }

/-- The subject pin. -/
theorem kadane_pin :
    findFunctionIn? kadaneLowered.funcs ⟨"kadane"⟩ = some kadaneFunc := rfl

/-! ## The statement vocabulary

`maxSubarraySum` is the whole postcondition: the MATHEMATICAL maximum
over all non-empty contiguous segments' sums, with `0` for the empty
list (the Go source's own documented empty-slice definition — chosen
there so the `s[0]` read is guarded). It is defined by enumerating the
segments as data (`segments`, via `nePrefixes`) and taking
`List.max?` — not by restating the scan loop. -/

/-- All non-empty prefixes of `xs`, shortest first. -/
def nePrefixes : List Int → List (List Int)
  | [] => []
  | x :: t => [x] :: (nePrefixes t).map (x :: ·)

/-- All non-empty contiguous segments of `xs`: the non-empty prefixes
starting at position 0, then the segments of the tail. -/
def segments : List Int → List (List Int)
  | [] => []
  | x :: t => nePrefixes (x :: t) ++ segments t

/-- **The maximum subarray sum**: the greatest sum over all non-empty
contiguous segments, `0` for the empty list. -/
def maxSubarraySum (xs : List Int) : Int :=
  (((segments xs).map List.sum).max?).getD 0

/-- The returned fixed-cap array: the observed list, zero-padded to the
harness's `kadaneCapN = 8` slots, at the int64 kind. Statement
vocabulary — deliberately not shared with the uint64 `goArr8`s. -/
def kadArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map
    (fun v => .int v .int64)⟩

/-! ## The pure proof layer: `List.max?` plumbing -/

/-- `max?.getD 0`, the working spelling of the spec's maximum. -/
private def mx (l : List Int) : Int := l.max?.getD 0

private theorem foldl_max_pull (l : List Int) :
    ∀ a b : Int, l.foldl max (max a b) = max a (l.foldl max b) := by
  induction l with
  | nil => intro a b; rfl
  | cons x t ih =>
      intro a b
      show t.foldl max (max (max a b) x) = _
      rw [show max (max a b) x = max a (max b x) from by omega, ih]
      rfl

private theorem mx_append {A B : List Int} (hA : A ≠ []) (hB : B ≠ []) :
    mx (A ++ B) = max (mx A) (mx B) := by
  obtain ⟨a, A, rfl⟩ := List.exists_cons_of_ne_nil hA
  obtain ⟨b, B, rfl⟩ := List.exists_cons_of_ne_nil hB
  show (A ++ b :: B).foldl max a = _
  rw [List.foldl_append]
  show B.foldl max (max (A.foldl max a) b) = _
  rw [foldl_max_pull]
  rfl

private theorem foldl_max_map_add (y : Int) (l : List Int) :
    ∀ a : Int, (l.map (y + ·)).foldl max (y + a) = y + l.foldl max a := by
  induction l with
  | nil => intro a; rfl
  | cons x t ih =>
      intro a
      show (t.map (y + ·)).foldl max (max (y + a) (y + x)) = _
      rw [show max (y + a) (y + x) = y + max a x from by omega, ih]
      rfl

private theorem mx_map_add (y x : Int) (l : List Int) :
    mx ((x :: l).map (y + ·)) = y + mx (x :: l) := by
  show (l.map (y + ·)).foldl max (y + x) = y + l.foldl max x
  exact foldl_max_map_add y l x

private theorem mx_single (x : Int) : mx [x] = x := rfl

/-! ## Prefix and suffix sums -/

/-- The sums of the non-empty prefixes, shortest first. -/
private def prefixSums : List Int → List Int
  | [] => []
  | x :: t => x :: (prefixSums t).map (x + ·)

private theorem prefixSums_ne_nil {xs : List Int} (h : xs ≠ []) :
    prefixSums xs ≠ [] := by
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil h
  simp [prefixSums]

private theorem nePrefixes_sums (xs : List Int) :
    (nePrefixes xs).map List.sum = prefixSums xs := by
  induction xs with
  | nil => rfl
  | cons x t ih =>
      show List.sum [x] :: ((nePrefixes t).map (x :: ·)).map List.sum = _
      rw [List.map_map]
      have hc : (List.sum ∘ (x :: ·) : List Int → Int)
          = ((x + ·) ∘ List.sum) := by
        funext p; simp [List.sum_cons]
      rw [hc, ← List.map_map, ih]
      simp [prefixSums]

private theorem prefixSums_snoc (q : List Int) (y : Int) :
    prefixSums (q ++ [y]) = prefixSums q ++ [q.sum + y] := by
  induction q with
  | nil => simp [prefixSums]
  | cons x t ih =>
      show x :: (prefixSums (t ++ [y])).map (x + ·) = _
      rw [ih, List.map_append]
      simp [prefixSums, List.sum_cons, Int.add_assoc]

/-- The sums of the non-empty suffixes, longest first. -/
private def suffSums : List Int → List Int
  | [] => []
  | x :: t => (x + t.sum) :: suffSums t

private theorem suffSums_ne_nil {xs : List Int} (h : xs ≠ []) :
    suffSums xs ≠ [] := by
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil h
  simp [suffSums]

private theorem suffSums_snoc (p : List Int) (y : Int) :
    suffSums (p ++ [y]) = (suffSums p).map (· + y) ++ [y] := by
  induction p with
  | nil => simp [suffSums]
  | cons x t ih =>
      show (x + (t ++ [y]).sum) :: suffSums (t ++ [y]) = _
      rw [ih, List.sum_append]
      simp [suffSums, Int.add_assoc]

/-- The maximum non-empty-suffix sum (proof-side; junk `0` on `[]`). -/
private def maxEnd (xs : List Int) : Int := mx (suffSums xs)

private theorem maxEnd_single (x : Int) : maxEnd [x] = x := by
  simp [maxEnd, suffSums, mx]

private theorem maxEnd_cons (x : Int) (t : List Int) (ht : t ≠ []) :
    maxEnd (x :: t) = max (x + t.sum) (maxEnd t) := by
  rw [maxEnd, suffSums]
  obtain ⟨b, B, rfl⟩ := List.exists_cons_of_ne_nil ht
  rw [show ((x + (b :: B).sum) :: suffSums (b :: B))
      = [x + (b :: B).sum] ++ suffSums (b :: B) from rfl,
    mx_append (by simp) (suffSums_ne_nil (by simp)), mx_single]
  rfl

private theorem maxEnd_snoc (p : List Int) (hp : p ≠ []) (y : Int) :
    maxEnd (p ++ [y]) = max (maxEnd p + y) y := by
  rw [maxEnd, suffSums_snoc]
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hp
  rw [show suffSums (x :: t) = (x + t.sum) :: suffSums t from rfl,
    List.map_cons,
    show (((x + t.sum) + y) :: (suffSums t).map (· + y))
      = ((x + t.sum) :: suffSums t).map (· + y) from by simp,
    mx_append (by simp) (by simp),
    show ((x + t.sum) :: suffSums t).map (· + y)
      = ((x + t.sum) :: suffSums t).map ((y + ·)) from by
        simp [Int.add_comm],
    mx_map_add, mx_single]
  rw [maxEnd, show suffSums (x :: t) = (x + t.sum) :: suffSums t from rfl]
  omega

/-! ## The spec's own equations -/

private theorem segments_ne_nil {xs : List Int} (h : xs ≠ []) :
    segments xs ≠ [] := by
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil h
  simp [segments, nePrefixes]

theorem maxSub_single (x : Int) : maxSubarraySum [x] = x := by
  simp [maxSubarraySum, segments, nePrefixes, List.max?]

private theorem maxSub_cons (x : Int) (t : List Int) (ht : t ≠ []) :
    maxSubarraySum (x :: t)
      = max (mx (prefixSums (x :: t))) (maxSubarraySum t) := by
  show mx ((segments (x :: t)).map List.sum) = _
  rw [show segments (x :: t) = nePrefixes (x :: t) ++ segments t from rfl,
    List.map_append, nePrefixes_sums]
  rw [mx_append (prefixSums_ne_nil (by simp))
    (by
      obtain ⟨b, B, rfl⟩ := List.exists_cons_of_ne_nil ht
      have : segments (b :: B) ≠ [] := segments_ne_nil (by simp)
      simpa using this)]
  rfl

private theorem mxP_snoc (q : List Int) (hq : q ≠ []) (y : Int) :
    mx (prefixSums (q ++ [y])) = max (mx (prefixSums q)) (q.sum + y) := by
  rw [prefixSums_snoc, mx_append (prefixSums_ne_nil hq) (by simp), mx_single]

/-- **The spec's snoc equation**: appending one element extends the
maximum either inside the old list or as a segment ending at the new
element. -/
private theorem maxSub_snoc (p : List Int) (hp : p ≠ []) (y : Int) :
    maxSubarraySum (p ++ [y])
      = max (maxSubarraySum p) (maxEnd (p ++ [y])) := by
  induction p with
  | nil => cases hp rfl
  | cons x t ih =>
      by_cases ht : t = []
      · subst ht
        simp only [List.nil_append, List.cons_append, maxSub_single]
        simp [maxSubarraySum, segments, nePrefixes, maxEnd, suffSums, mx,
          List.max?]
      · have hty : t ++ [y] ≠ [] := by
          obtain ⟨b, B, rfl⟩ := List.exists_cons_of_ne_nil ht
          simp
        rw [show ((x :: t) ++ [y]) = x :: (t ++ [y]) from rfl,
          maxSub_cons x (t ++ [y]) hty, ih ht,
          show (x :: (t ++ [y])) = (x :: t) ++ [y] from rfl,
          mxP_snoc (x :: t) (by simp) y,
          maxSub_cons x t ht,
          maxEnd_snoc (x :: t) (by simp) y,
          maxEnd_cons x t ht,
          maxEnd_snoc t ht y,
          List.sum_cons]
        omega

/-! ## The loop-shaped scan (proof-side) and the bridge -/

/-- The scan's `cur` at loop entry `i = m` (max suffix sum of the first
`m` elements); junk `0` at `m = 0`. Proof-side only. -/
def kadCur (l : List Int) : Nat → Int
  | 0 => 0
  | 1 => l.getD 0 0
  | m + 2 =>
      if kadCur l (m + 1) < 0 then l.getD (m + 1) 0
      else kadCur l (m + 1) + l.getD (m + 1) 0

/-- The scan's `best` at loop entry `i = m`; junk `0` at `m = 0`.
Proof-side only. -/
def kadBest (l : List Int) : Nat → Int
  | 0 => 0
  | 1 => l.getD 0 0
  | m + 2 => max (kadBest l (m + 1)) (kadCur l (m + 2))

/-- The scan's step equation at `1 ≤ m`, isolated so consumers never
touch the match. -/
theorem kadCur_step (l : List Int) (m : Nat) (hm : 1 ≤ m) :
    kadCur l (m + 1)
      = (if kadCur l m < 0 then l.getD m 0
         else kadCur l m + l.getD m 0) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rfl

theorem kadBest_step (l : List Int) (m : Nat) (hm : 1 ≤ m) :
    kadBest l (m + 1) = max (kadBest l m) (kadCur l (m + 1)) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rfl

private theorem take_one_of_ne_nil {l : List Int} (h : l ≠ []) :
    l.take 1 = [l.getD 0 0] := by
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil h
  simp [List.take]

private theorem take_succ_getD {l : List Int} {m : Nat} (h : m < l.length) :
    l.take (m + 1) = l.take m ++ [l.getD m 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

private theorem take_ne_nil {l : List Int} {m : Nat} (h1 : 1 ≤ m)
    (h : m ≤ l.length) : l.take m ≠ [] := by
  have : (l.take m).length = m := by
    rw [List.length_take]; omega
  intro hc
  rw [hc] at this
  simp at this
  omega

/-- The `cur` bridge: the scan's accumulator IS the maximum non-empty
suffix sum of the processed prefix. -/
theorem kadCur_eq_maxEnd (l : List Int) :
    ∀ m : Nat, 1 ≤ m → m ≤ l.length → kadCur l m = maxEnd (l.take m) := by
  intro m
  induction m with
  | zero => omega
  | succ m ih =>
      intro _ hlen
      match m with
      | 0 =>
          rw [take_one_of_ne_nil (by intro hc; subst hc; simp at hlen),
            maxEnd_single]
          rfl
      | m + 1 =>
          have hm : m + 1 < l.length := by omega
          have hcur := ih (by omega) (by omega)
          rw [show kadCur l (m + 1 + 1)
              = (if kadCur l (m + 1) < 0 then l.getD (m + 1) 0
                 else kadCur l (m + 1) + l.getD (m + 1) 0) from rfl,
            take_succ_getD hm,
            maxEnd_snoc (l.take (m + 1)) (take_ne_nil (by omega) (by omega)) _,
            ← hcur]
          by_cases hlt : kadCur l (m + 1) < 0
          · rw [if_pos hlt]; omega
          · rw [if_neg hlt]; omega

/-- The `best` bridge: the scan's running best IS the maximum subarray
sum of the processed prefix. -/
theorem kadBest_eq_maxSub (l : List Int) :
    ∀ m : Nat, 1 ≤ m → m ≤ l.length →
      kadBest l m = maxSubarraySum (l.take m) := by
  intro m
  induction m with
  | zero => omega
  | succ m ih =>
      intro _ hlen
      match m with
      | 0 =>
          rw [take_one_of_ne_nil (by intro hc; subst hc; simp at hlen),
            maxSub_single]
          rfl
      | m + 1 =>
          have hm : m + 1 < l.length := by omega
          have hbest := ih (by omega) (by omega)
          have hcur := kadCur_eq_maxEnd l (m + 1 + 1) (by omega) (by omega)
          rw [show kadBest l (m + 1 + 1)
              = max (kadBest l (m + 1)) (kadCur l (m + 1 + 1)) from rfl,
            take_succ_getD hm,
            maxSub_snoc (l.take (m + 1))
              (take_ne_nil (by omega) (by omega)) _,
            hbest, hcur, take_succ_getD hm]

/-- The whole-list corollary the run uses. -/
theorem kadBest_spec {l : List Int} (h1 : 1 ≤ l.length) :
    kadBest l l.length = maxSubarraySum l := by
  rw [kadBest_eq_maxSub l l.length h1 (Nat.le_refl _),
    List.take_of_length_le (Nat.le_refl _)]

/-! ## Range bounds for the scan values (machine-integer honesty) -/

private theorem getD_mem_int {l : List Int} {k : Nat} (hk : k < l.length) :
    l.getD k 0 ∈ l := GoLean.SliceMem.getD_mem hk

/-- `cur` and `best` stay within `m·B` of zero when every element is
within `B` — the reason the int64 arithmetic never wraps on the
harness's domain. -/
theorem kad_bounds (l : List Int) (B : Int) (hB : 0 ≤ B)
    (hl : ∀ v ∈ l, -B ≤ v ∧ v ≤ B) :
    ∀ m : Nat, 1 ≤ m → m ≤ l.length →
      (-((m : Int) * B) ≤ kadCur l m ∧ kadCur l m ≤ (m : Int) * B) ∧
      (-((m : Int) * B) ≤ kadBest l m ∧ kadBest l m ≤ (m : Int) * B) := by
  intro m
  induction m with
  | zero => omega
  | succ m ih =>
      intro _ hlen
      match m with
      | 0 =>
          have hv := hl _ (getD_mem_int (show 0 < l.length by omega))
          constructor <;> constructor <;>
            simp only [kadCur, kadBest] <;> omega
      | m + 1 =>
          have hv := hl _ (getD_mem_int (show m + 1 < l.length by omega))
          obtain ⟨⟨hc1, hc2⟩, ⟨hb1, hb2⟩⟩ := ih (by omega) (by omega)
          have hmul : ((m + 1 + 1 : Nat) : Int) * B
              = ((m + 1 : Nat) : Int) * B + B := by
            push_cast
            rw [Int.add_mul, Int.one_mul]
          have hBmono : B ≤ ((m + 1 : Nat) : Int) * B := by
            have : (1 : Int) * B ≤ ((m + 1 : Nat) : Int) * B := by
              apply Int.mul_le_mul_of_nonneg_right _ hB
              push_cast; omega
            omega
          have hbest' : kadBest l (m + 1 + 1)
              = max (kadBest l (m + 1)) (kadCur l (m + 1 + 1)) := rfl
          have hcur' : kadCur l (m + 1 + 1)
              = (if kadCur l (m + 1) < 0 then l.getD (m + 1) 0
                 else kadCur l (m + 1) + l.getD (m + 1) 0) := rfl
          rw [hbest', hcur', hmul]
          by_cases hlt : kadCur l (m + 1) < 0
          · rw [if_pos hlt]
            omega
          · rw [if_neg hlt]
            omega

/-! ## The setup family and the padded prefixes -/

/-- One family element: `seed + i`, negated at odd `i` — exactly the
harness setup's arithmetic (no wrap on the headline's domain). -/
def kadFamVal (seed : Int) (i : Nat) : Int :=
  if i % 2 = 1 then -(seed + i) else seed + i

/-- The setup family: `s[i] = seed + i`, odd indices negated. The
existential's witness in the headline (never in its postcondition). -/
def kadFamily (n : Nat) (seed : Int) : List Int :=
  (List.range n).map (kadFamVal seed)

theorem kadFamily_length (n : Nat) (seed : Int) :
    (kadFamily n seed).length = n :=
  familyZ_length (kadFamVal seed) n

theorem kadFamily_range {n : Nat} {seed : Int} (hn : n ≤ 8)
    (hs1 : -(2 ^ 59) ≤ seed) (hs2 : seed ≤ 2 ^ 59) :
    ∀ v ∈ kadFamily n seed, -(2 ^ 59 + 8) ≤ v ∧ v ≤ 2 ^ 59 + 8 := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := familyZ_mem (g := kadFamVal seed) hv
  have : (i : Int) ≤ 8 := by omega
  rw [kadFamVal]
  split <;> omega

theorem kadFamily_getD {n m : Nat} {seed : Int} (hm : m < n) :
    (kadFamily n seed).getD m 0 = kadFamVal seed m :=
  familyZ_getD hm

theorem kadFamily_succ (m : Nat) (seed : Int) :
    kadFamily (m + 1) seed = kadFamily m seed ++ [kadFamVal seed m] :=
  familyZ_succ (kadFamVal seed) m

/-- The setup/copy invariant list: the family prefix, zero-padded to
`cap`. -/
def kadPad (cap m : Nat) (seed : Int) : List Int :=
  kadFamily m seed ++ List.replicate (cap - m) 0

theorem kadPad_zero (cap : Nat) (seed : Int) :
    kadPad cap 0 seed = List.replicate cap 0 :=
  padZ_zero (kadFamVal seed) cap

theorem kadPad_length {cap m : Nat} {seed : Int} (hm : m ≤ cap) :
    (kadPad cap m seed).length = cap :=
  padZ_length hm

theorem kadPad_range {cap m : Nat} {seed : Int} (_hm : m ≤ cap)
    (hcap : m ≤ 8) (hs1 : -(2 ^ 59) ≤ seed) (hs2 : seed ≤ 2 ^ 59) :
    ∀ v ∈ kadPad cap m seed, -(2 ^ 59 + 8) ≤ v ∧ v ≤ 2 ^ 59 + 8 :=
  padZ_range
    (fun i hi => by
      have : (i : Int) ≤ 8 := by omega
      rw [kadFamVal]
      split <;> omega)
    ⟨by omega, by omega⟩

/-- One padded-prefix store advances the prefix. -/
theorem kadPad_set {cap m : Nat} {seed : Int} (hm : m < cap) :
    (kadPad cap m seed).set m (kadFamVal seed m)
      = kadPad cap (m + 1) seed :=
  padZ_set hm

/-- The EVEN-index setup store lands the family value directly. -/
theorem kadPad_set_even {cap m : Nat} {seed : Int} (hm : m < cap)
    (hev : m % 2 = 0) :
    (kadPad cap m seed).set m (seed + m) = kadPad cap (m + 1) seed := by
  have : kadFamVal seed m = seed + m := by
    rw [kadFamVal, if_neg (by omega)]
  rw [← this]
  exact kadPad_set hm

/-- The ODD-index intermediate list (after the first store, before the
negation): the padded prefix with `seed + m` at `m`. -/
def kadMid (cap m : Nat) (seed : Int) : List Int :=
  kadFamily m seed ++ ((seed + m) :: List.replicate (cap - (m + 1)) 0)

theorem kadMid_of_set {cap m : Nat} {seed : Int} (hm : m < cap) :
    (kadPad cap m seed).set m (seed + m) = kadMid cap m seed :=
  padZ_set_any (seed + (m : Int)) hm

theorem kadMid_length {cap m : Nat} {seed : Int} (_hm : m < cap) :
    (kadMid cap m seed).length = cap := by
  rw [kadMid, List.length_append, kadFamily_length, List.length_cons,
    List.length_replicate]
  omega

theorem kadMid_getD {cap m : Nat} {seed : Int} (_hm : m < cap) :
    (kadMid cap m seed).getD m 0 = seed + m := by
  rw [kadMid, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [kadFamily_length]; exact Nat.le_refl m),
    kadFamily_length, Nat.sub_self]
  rfl

theorem kadMid_range {cap m : Nat} {seed : Int} (_hm : m < cap)
    (hcap : m ≤ 8) (hs1 : -(2 ^ 59) ≤ seed) (hs2 : seed ≤ 2 ^ 59) :
    ∀ v ∈ kadMid cap m seed, -(2 ^ 59 + 8) ≤ v ∧ v ≤ 2 ^ 59 + 8 := by
  intro v hv
  rw [kadMid] at hv
  rcases List.mem_append.mp hv with hv | hv
  · exact kadFamily_range (by omega) hs1 hs2 v hv
  · rcases List.mem_cons.mp hv with rfl | hv
    · have : (m : Int) ≤ 8 := by omega
      omega
    · rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
      omega

/-- The ODD-index second store (the negation) lands the family value. -/
theorem kadMid_set_odd {cap m : Nat} {seed : Int} (_hm : m < cap)
    (hodd : m % 2 = 1) :
    (kadMid cap m seed).set m (-(seed + m)) = kadPad cap (m + 1) seed := by
  have hlen : (kadFamily m seed).length = m := kadFamily_length m seed
  rw [kadMid, List.set_append_right _ _ (by omega), hlen, Nat.sub_self,
    List.set_cons_zero, kadPad, kadFamily_succ]
  have : kadFamVal seed m = -(seed + m) := by
    rw [kadFamVal, if_pos hodd]
  rw [this]
  simp

/-- The copy loop's terminal list at cap 8 IS the family, zero-padded —
what `kadArr8` states over the witness. -/
theorem kadPad_full {n : Nat} {seed : Int} (_h : n ≤ 8) :
    kadPad 8 n seed
      = kadFamily n seed
        ++ List.replicate (8 - (kadFamily n seed).length) 0 := by
  rw [kadPad, kadFamily_length]

/-! ## Machine-integer facts at the SIGNED int64 kind

GAP-WITNESS family (kit gap `i64-ops`): the kit's machine-integer and
store facts (`unorm_*`, `storeTarget_slice_u64`,
`storeTarget_arrayLocal_u64`, `normalizeValueForTy_arr_u64`,
`stepFn_makeSlice_u64_step`, `getElem?_mapU`) are all stated at the
uint64 kind; kadane is the wave's only SIGNED example, so their int64
mirrors live here as local copies until a second signed consumer
promotes them into `SliceMem`/`StepKit`. -/

/-- An int64 value in Go range is its own normal form. (Was
GAP-WITNESS i64-ops; WP arc s1 lift 1: the pinned name survives as a
delegation to the kind-generic `SliceMem.normalize_of_range_signed`,
zero proof lines.) -/
theorem inorm64_of_range {v : Int} (h0 : -(2 ^ 63) ≤ v) (h1 : v < 2 ^ 63) :
    IntKind.normalize .int64 v = v :=
  SliceMem.normalize_of_range_signed (bits := 63) rfl rfl h0 h1

/-- The `Nat`-cast corner (loop counters). -/
theorem inorm64_nat_of_lt {x : Nat} (h : x < 2 ^ 63) :
    IntKind.normalize .int64 (x : Int) = (x : Int) :=
  inorm64_of_range (by omega) (by exact_mod_cast h)

/-- GAP-WITNESS (kit gap i64-ops): the int64 mirror of `getElem?_mapU`. -/
private theorem getElem?_mapI (l : List Int) (k : Nat) (hk : k < l.length) :
    (⟨l.map (fun v => .int v .int64)⟩ : Array GoValue)[k]?
      = some (.int (l.getD k 0) .int64) := by
  simp [List.getElem?_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk]

private theorem validateSlice_ok' {b : Loc} {off len cap : Nat}
    (hcap : len ≤ cap) :
    validateSlice ⟨some b, off, len, cap⟩ = .ok () := by
  simp [validateSlice, Nat.not_lt.mpr hcap, Bind.bind, Except.bind]

private theorem sliceIndexLoc_ok' {b : Loc} {off len cap i : Nat}
    (hcap : len ≤ cap) (hi : i < len) :
    sliceIndexLoc ⟨some b, off, len, cap⟩ (i : Nat) =
      .ok (.index b (Int.ofNat (off + i))) := by
  simp only [sliceIndexLoc, validateSlice_ok' hcap, Bind.bind, Except.bind,
    pure, Except.pure, Int.toNat_natCast, Int.ofNat_eq_natCast]
  rw [if_neg (by omega)]
  simp [hi]

private theorem normalizeListWith_i64 {σ : ExecState} {fuel : Nat}
    (hf : 0 < fuel)
    (l : List Int) (hl : ∀ v ∈ l, -(2 ^ 63) ≤ v ∧ v < 2 ^ 63) :
    normalizeListWith (normalizeValueForTyFuel fuel σ (.int .int64))
      (l.map (fun v => .int v .int64))
      = .ok ⟨l.map (fun v => .int v .int64)⟩ := by
  match fuel, hf with
  | f + 1, _ =>
    induction l with
    | nil => simp [normalizeListWith]
    | cons v rest ih =>
        have hv := hl v (by simp)
        have hrest := ih (fun w hw => hl w (by simp [hw]))
        simp [normalizeListWith, normalizeValueForTyFuel,
          inorm64_of_range hv.1 hv.2, hrest, Bind.bind, Except.bind]

/-- GAP-WITNESS (kit gap i64-ops): the int64 mirror of
`normalizeValueForTy_arr_u64`. -/
theorem normalizeValueForTy_arr_i64 {σ : ExecState} {N : Nat} {lp : List Int}
    (hlen : lp.length = N)
    (hl : ∀ v ∈ lp, -(2 ^ 63) ≤ v ∧ v < 2 ^ 63) :
    normalizeValueForTy σ (.array N (.int .int64))
        (.array ⟨lp.map (fun v => .int v .int64)⟩)
      = .ok (.array ⟨lp.map (fun v => .int v .int64)⟩) := by
  rw [normalizeValueForTy, typeResolutionFuel]
  simp only [normalizeValueForTyFuel]
  rw [if_neg (by simp [hlen])]
  have hlist := normalizeListWith_i64 (σ := σ) (fuel := 1023) (by omega) lp hl
  simp [hlist, Bind.bind, Except.bind, Functor.map, Except.map]

/-- GAP-WITNESS (kit gap i64-ops): the int64 mirror of
`storeTarget_slice_u64` (`s[i] = w` on `[]int64`). -/
theorem storeTarget_slice_i64 {σ : ExecState} {a : Addr}
    {off len cap i n : Nat} {ik : IntKind} {l : List Int} {w : Int}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨some (.array n (.int .int64)),
              .array ⟨l.map (fun v => .int v .int64)⟩⟩)
    (hcap : len ≤ cap) (hi : i < len)
    (hsz : off + i < l.length) (hn : l.length = n)
    (hl : ∀ v ∈ l, -(2 ^ 63) ≤ v ∧ v < 2 ^ 63)
    (hw : -(2 ^ 63) ≤ w ∧ w < 2 ^ 63) :
    storeTarget σ
      (.chain (.slice ⟨some (.base a), off, len, cap⟩) [.int (i : Nat) ik]
        [.index])
      (.int w .int64)
      = .ok { σ with heap := (Heap.set σ.heap (.base a)
          ⟨some (.array n (.int .int64)),
           .array ⟨(l.set (off + i) w).map (fun v => .int v .int64)⟩⟩) } := by
  have hglist : l[off + i]? = some (l[off + i]'hsz) :=
    List.getElem?_eq_getElem hsz
  have hset : ∀ v ∈ l.set (off + i) w, -(2 ^ 63) ≤ v ∧ v < 2 ^ 63 := by
    intro v hv
    rcases GoLean.SliceMem.mem_set_of_mem hv with rfl | hv
    · exact hw
    · exact hl v hv
  have harrset : arraySet (⟨l.map (fun v => .int v .int64)⟩ : Array GoValue)
      (Int.ofNat (off + i)) (.int w .int64)
      = .ok ⟨(l.set (off + i) w).map (fun v => .int v .int64)⟩ := by
    have hidx : ((off + i : Nat) : Int).toNat = off + i := by omega
    simp only [arraySet, arrayIndexNat, Bind.bind, Except.bind,
      Int.ofNat_eq_natCast, hidx]
    rw [if_neg (by omega), if_pos (by simpa using hsz)]
    simp [hglist, coerceStoredValue, inorm64_of_range hw.1 hw.2,
      Array.set!, pure, Except.pure]
  have hnorm : normalizeValueForTy σ (.array n (.int .int64))
      (.array ⟨(l.set (off + i) w).map (fun v => .int v .int64)⟩)
      = .ok (.array ⟨(l.set (off + i) w).map (fun v => .int v .int64)⟩) :=
    normalizeValueForTy_arr_i64 (by rw [List.length_set]; exact hn) hset
  simp only [storeTarget, resolveChain, indexTargetLoc, valueAsInt,
    valueAsLoc, sliceIndexLoc_ok' hcap hi, Bind.bind, Except.bind, storeLoc,
    loadLoc, hlook, harrset, hnorm, pure, Except.pure]

/-- GAP-WITNESS (kit gap i64-ops): the int64 mirror of
`storeTarget_arrayLocal_u64` (`pre[i] = w` on `[8]int64`). -/
theorem storeTarget_arrayLocal_i64 {σ : ExecState} {a : Addr} {N i : Nat}
    {ik : IntKind} {l : List Int} {w : Int}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨some (.array N (.int .int64)),
              .array ⟨l.map (fun v => .int v .int64)⟩⟩)
    (hi : i < l.length) (hn : l.length = N)
    (hl : ∀ v ∈ l, -(2 ^ 63) ≤ v ∧ v < 2 ^ 63)
    (hw : -(2 ^ 63) ≤ w ∧ w < 2 ^ 63) :
    storeTarget σ (.chain (.addr (.base a)) [.int (i : Nat) ik] [.index])
        (.int w .int64)
      = .ok { σ with
          heap := Heap.set σ.heap (.base a)
            ⟨some (.array N (.int .int64)),
             .array ⟨(l.set i w).map (fun v => .int v .int64)⟩⟩ } := by
  have hsize : (⟨l.map (fun v => .int v .int64)⟩ : Array GoValue).size
      = l.length := by simp
  have hglist : l[i]? = some (l[i]'hi) := List.getElem?_eq_getElem hi
  have hset : ∀ v ∈ l.set i w, -(2 ^ 63) ≤ v ∧ v < 2 ^ 63 := by
    intro v hv
    rcases GoLean.SliceMem.mem_set_of_mem hv with rfl | hv
    · exact hw
    · exact hl v hv
  have hidxn : arrayIndexNat (⟨l.map (fun v => .int v .int64)⟩ : Array GoValue)
      ((i : Nat) : Int) = .ok i := by
    simp only [arrayIndexNat, Bind.bind, Except.bind]
    rw [if_neg (by omega), Int.toNat_natCast,
      if_pos (by simpa [hsize] using hi)]
    rfl
  have harrset : arraySet (⟨l.map (fun v => .int v .int64)⟩ : Array GoValue)
      ((i : Nat) : Int) (.int w .int64)
      = .ok ⟨(l.set i w).map (fun v => .int v .int64)⟩ := by
    simp only [arraySet, Bind.bind, Except.bind, hidxn]
    simp [hglist, coerceStoredValue, inorm64_of_range hw.1 hw.2,
      Array.set!, pure, Except.pure]
  have hnorm : normalizeValueForTy σ (.array N (.int .int64))
      (.array ⟨(l.set i w).map (fun v => .int v .int64)⟩)
      = .ok (.array ⟨(l.set i w).map (fun v => .int v .int64)⟩) :=
    normalizeValueForTy_arr_i64 (by rw [List.length_set]; exact hn) hset
  simp only [storeTarget, resolveChain, indexTargetLoc, valueAsInt,
    valueAsLoc, Bind.bind, Except.bind, storeLoc, loadLoc, hlook, hidxn,
    harrset, hnorm, pure, Except.pure]

/-- GAP-WITNESS (kit gap i64-ops): the int64 mirror of
`stepFn_makeSlice_u64_step`. -/
theorem stepFn_makeSlice_i64_step {σ σ' : ExecState} {n : Nat}
    {tv : GoValue} {env : LocalEnv} {k : Cont} {ch : Choices}
    (happly : applyStmtOp σ ch (.makeSlice (.int .int64) false) 1
      [tv, .int (n : Nat) .int64] = .ok (σ', ch)) :
    stepFn σ (.retV (.int (n : Nat) .int64)
      (.stmtOpK (.makeSlice (.int .int64) false) 1 [tv] [] env k)) ch
      = .ok (.next k, σ', ch) := by
  simp only [stepFn, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append]
  rw [happly]
  rfl

/-! ## Cells and handles at the run's layout

Address layout (probe-measured; terminal `nextAddr = 19`):
0 = `n`, 1 = `seed`, 2 = `$res0` (`[8]int64`), 3 = `$res1`,
4 = `$c8` (handle), 5 = backing, 6 = `s`, 7 = setup `i`,
8 = setup flag, 9 = `pre`, 10 = copy `i`, 11 = copy flag,
12 = the harness's `best`, 13 = kadane's `s`, 14 = kadane's `$res0`,
15 = kadane's `best`, 16 = `cur`, 17 = kadane's `i` (kind `int`),
18 = its flag. -/

/-- The PROGRAM-generic state form. -/
abbrev kSt (σ : ExecState) (H : Heap) (na : Nat) : ExecState :=
  { σ with heap := H, nextAddr := na }

abbrev ki64 (v : Int) : HeapCell := ⟨some (.int .int64), .int v .int64⟩
abbrev kint (v : Int) : HeapCell := ⟨some (.int .int), .int v .int⟩
abbrev kbool (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
abbrev kSliceS (n : Nat) : GoValue := .slice ⟨some (.base ⟨5⟩), 0, n, n⟩
abbrev kHandle (n : Nat) : HeapCell :=
  ⟨some (.slice (.int .int64)), kSliceS n⟩
abbrev kBack (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n (.int .int64)), .array ⟨l.map (fun v => .int v .int64)⟩⟩
abbrev kArr8 (l : List Int) : HeapCell :=
  ⟨some (.array 8 (.int .int64)), .array ⟨l.map (fun v => .int v .int64)⟩⟩
abbrev kNilSlice : HeapCell :=
  ⟨some (.slice (.int .int64)), .slice ⟨none, 0, 0, 0⟩⟩
abbrev kZeros8 : List Int := List.replicate 8 0

/-! ## Environments -/

def kBaseScope : Scope :=
  [("$res1", .base ⟨3⟩), ("$res0", .base ⟨2⟩),
   ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]
def kEnvC8 : LocalEnv := [[("$c8", .base ⟨4⟩)], kBaseScope]
def kSScope : Scope := [("s", .base ⟨6⟩), ("$c8", .base ⟨4⟩)]
def kSuEnv : LocalEnv :=
  [[("$forFirst", .base ⟨8⟩)], [("i", .base ⟨7⟩)], kSScope, kBaseScope]
def kSuEnv1 : LocalEnv := [] :: kSuEnv
def kSuEnv2 : LocalEnv := [] :: kSuEnv1
def kSuEnv3 : LocalEnv := [] :: kSuEnv2
def kPreScope : Scope :=
  [("pre", .base ⟨9⟩), ("s", .base ⟨6⟩), ("$c8", .base ⟨4⟩)]
def kCpEnv : LocalEnv :=
  [[("$forFirst", .base ⟨11⟩)], [("i", .base ⟨10⟩)], kPreScope, kBaseScope]
def kCpEnv1 : LocalEnv := [] :: kCpEnv
def kCpEnv2 : LocalEnv := [] :: kCpEnv1
def kCallScope : Scope :=
  [("best", .base ⟨12⟩), ("pre", .base ⟨9⟩), ("s", .base ⟨6⟩),
   ("$c8", .base ⟨4⟩)]
def kCallEnv : LocalEnv := [kCallScope, kBaseScope]
def kEnvB : LocalEnv := [[("$res0", .base ⟨14⟩), ("s", .base ⟨13⟩)]]
def kEnvG : LocalEnv := [] :: kEnvB
def kEnvG1 : LocalEnv := [("best", .base ⟨15⟩)] :: kEnvB
def kEnvBC : LocalEnv := [("cur", .base ⟨16⟩), ("best", .base ⟨15⟩)] :: kEnvB
def kEnvI : LocalEnv := [("i", .base ⟨17⟩)] :: kEnvBC
def kEnvIn : LocalEnv := [("$forFirst", .base ⟨18⟩)] :: kEnvI
def kEnvC : LocalEnv := [] :: kEnvIn
def kEnvD : LocalEnv := [] :: kEnvC
def kEnvE : LocalEnv := [] :: kEnvD

/-! ## Continuations -/

def kdFrameStop : Cont := .frame [] [] [] [] .stop false
def kdTail0 : Cont :=
  .seq [kdS2, kdS3, kdS4, kdS5, kdS6, kdS7] kEnvC8 kdFrameStop

abbrev kdSuNegBlock : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
        (.neg (.indexGet (.var "s") (.var "i")))]]
abbrev kdSuParityIf : Stmt :=
  .ifThenElse
    (.eqCmp (.int .int64)
      (.mod (.var "i") (.intLit 2 .int64)) (.intLit 1 .int64))
    kdSuNegBlock (.seqn #[])

def kdTailAfterSetup : Cont :=
  .seq [kdS4, kdS5, kdS6, kdS7] [kSScope, kBaseScope] kdFrameStop
def kdSuHeadTail : Cont :=
  .seq [] kSuEnv
    (.seq [] [[("i", .base ⟨7⟩)], kSScope, kBaseScope] kdTailAfterSetup)
def kdSuHeadCfg : Config :=
  .exec (.while (.boolLit true) kdSuWhileBody) kSuEnv kdSuHeadTail
def kdSuLoopK : Cont :=
  .loop (.boolLit true) kdSuWhileBody kSuEnv kdSuHeadTail
def kdSuCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt kSuEnv1 (.seq [kdSuStoreBlock] kSuEnv1 kdSuLoopK)
def kdSuRef (n : Nat) (iv : Int) : TargetRef :=
  .chain (kSliceS n) [.int iv .int64] [.index]
def kdSuIfTail : Cont := .seq [] kSuEnv2 (.seq [] kSuEnv1 kdSuLoopK)
def kdSuStTail : Cont :=
  .seq [kdSuParityIf] kSuEnv2 (.seq [] kSuEnv1 kdSuLoopK)
def kdSuParityIfK : Cont := .ifK kdSuNegBlock (.seqn #[]) kSuEnv2 kdSuIfTail
def kdSuNegStTail : Cont := .seq [] kSuEnv3 kdSuIfTail
def kdSuNegRhsK (n : Nat) (iv : Int) : Cont :=
  .rhsK .vals [kdSuRef n iv] [] [] (.seqn #[]) kSuEnv3 kdSuNegStTail

def kdTailAfterCopy : Cont :=
  .seq [kdS6, kdS7] [kPreScope, kBaseScope] kdFrameStop
def kdCpHeadTail : Cont :=
  .seq [] kCpEnv
    (.seq [] [[("i", .base ⟨10⟩)], kPreScope, kBaseScope] kdTailAfterCopy)
def kdCpHeadCfg : Config :=
  .exec (.while (.boolLit true) kdCpWhileBody) kCpEnv kdCpHeadTail
def kdCpLoopK : Cont :=
  .loop (.boolLit true) kdCpWhileBody kCpEnv kdCpHeadTail
def kdCpCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt kCpEnv1 (.seq [kdCpStoreBlock] kCpEnv1 kdCpLoopK)
def kdCpRef (iv : Int) : TargetRef :=
  .chain (.addr (.base ⟨9⟩)) [.int iv .int64] [.index]
def kdCpStTail : Cont := .seq [] kCpEnv2 (.seq [] kCpEnv1 kdCpLoopK)
def kdCpRhsK (iv : Int) : Cont :=
  .rhsK .vals [kdCpRef iv] [] [] (.seqn #[]) kCpEnv2 kdCpStTail

/-! ### The kadane frame -/

def kShapes : List (TargetShape × List Expr) := [(.chain [], [.ref "best"])]
def kdAfterCall : Cont := .seq [kdS7] kCallEnv kdFrameStop
def kFrameK : Cont := .frame kShapes kCallEnv [.base ⟨14⟩] [] kdAfterCall false
def kdCallArgsK : Cont := .callArgsK ⟨"kadane"⟩ kShapes [] [] kCallEnv kdAfterCall

def kGuardTail : Cont :=
  .seq [kBestInit, kCurInit, kLoopBlock, kEpilogue] kEnvG kFrameK
def kGuardIfK : Cont := .ifK kGuardThen (.seqn #[]) kEnvG kGuardTail
def kGEqK : Cont :=
  .strictK (.eqCmp (.int .int)) [] [.intLit 0 .int] kEnvG kGuardIfK
def kGLenK : Cont :=
  .strictK (.lengthOf (some (.slice (.int .int64)))) [] [] kEnvG kGEqK

def ktref15 : TargetRef := .chain (.addr (.base ⟨15⟩)) [] []
def ktref16 : TargetRef := .chain (.addr (.base ⟨16⟩)) [] []
def kBestRhsK : Cont :=
  .rhsK .vals [ktref15] [] [] (.seqn #[]) kEnvG1
    (.seq [kCurInit, kLoopBlock, kEpilogue] kEnvG1 kFrameK)
def kCurRhsK : Cont :=
  .rhsK .vals [ktref16] [] [] (.seqn #[]) kEnvBC
    (.seq [kLoopBlock, kEpilogue] kEnvBC kFrameK)

def kHeadTail : Cont :=
  .seq [] kEnvIn (.seq [] kEnvI (.seq [kEpilogue] kEnvBC kFrameK))
def kHeadCfg : Config :=
  .exec (.while (.boolLit true) kWhileBody) kEnvIn kHeadTail
def kLoopK : Cont := .loop (.boolLit true) kWhileBody kEnvIn kHeadTail
def kCmpIfK : Cont :=
  .ifK (.seqn #[]) .breakStmt kEnvC
    (.seq [.block #[] #[kCurIf, kBestIf]] kEnvC kLoopK)
def kLenApplyK (iv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice (.int .int64)))) [] [] kEnvC
    (.strictK .lessCmp [.int iv .int] [] kEnvC kCmpIfK)

abbrev kCurThen : Stmt :=
  .block #[] #[.seqn #[.assign (.var "cur")
    (.indexGet (.var "s") (.var "i"))]]
abbrev kCurElse : Stmt :=
  .block #[] #[.seqn #[.assign (.var "cur")
    (.add (.var "cur") (.indexGet (.var "s") (.var "i")))]]
abbrev kBestThen : Stmt :=
  .block #[] #[.seqn #[.assign (.var "best") (.var "cur")]]

def kCurIfTail : Cont := .seq [kBestIf] kEnvD (.seq [] kEnvC kLoopK)
def kCurIfK : Cont := .ifK kCurThen kCurElse kEnvD kCurIfTail
def kCurStTail : Cont := .seq [] kEnvE kCurIfTail
def kCurSetRhsK : Cont :=
  .rhsK .vals [ktref16] [] [] (.seqn #[]) kEnvE kCurStTail
def kBestIfTail : Cont := .seq [] kEnvD (.seq [] kEnvC kLoopK)
def kBestIfK : Cont := .ifK kBestThen (.seqn #[]) kEnvD kBestIfTail

def kdRes0Ref : TargetRef := .chain (.addr (.base ⟨2⟩)) [] []
def kdEpiTail : Cont :=
  .seq [.assign (.var "$res1") (.var "best"), .returnStmt] kCallEnv
    kdFrameStop

/-! ## Heap fronts (program-generic) -/

def kHeap0 (nv sv : Int) : Heap :=
  [(.base ⟨0⟩, ki64 nv), (.base ⟨1⟩, ki64 sv), (.base ⟨2⟩, kArr8 kZeros8),
   (.base ⟨3⟩, ki64 0)]
def kHeapC8 (nv sv : Int) : Heap := kHeap0 nv sv ++ [(.base ⟨4⟩, kNilSlice)]
def kHeapMake (nv sv : Int) (n : Nat) : Heap :=
  kHeap0 nv sv ++
    [(.base ⟨4⟩, kHandle n), (.base ⟨5⟩, kBack n (List.replicate n 0))]
def kHeapSu (nv sv : Int) (n : Nat) (l : List Int) (iv : Int) (ffv : Bool) :
    Heap :=
  kHeap0 nv sv ++
    [(.base ⟨4⟩, kHandle n), (.base ⟨5⟩, kBack n l), (.base ⟨6⟩, kHandle n),
     (.base ⟨7⟩, ki64 iv), (.base ⟨8⟩, kbool ffv)]
def kHeapCp (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (ffv : Bool) : Heap :=
  kHeapSu nv sv n l siv false ++
    [(.base ⟨9⟩, kArr8 lp), (.base ⟨10⟩, ki64 civ), (.base ⟨11⟩, kbool ffv)]
def kHeapCall (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int) :
    Heap :=
  kHeapCp nv sv n l lp siv civ false ++ [(.base ⟨12⟩, ki64 0)]
def kHeapKFrame (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int) :
    Heap :=
  kHeapCall nv sv n l lp siv civ ++
    [(.base ⟨13⟩, kHandle n), (.base ⟨14⟩, ki64 0)]
def kHeapP1 (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int) :
    Heap :=
  kHeapKFrame nv sv n l lp siv civ ++ [(.base ⟨15⟩, ki64 0)]
def kHeapKB (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ bv : Int) :
    Heap :=
  kHeapKFrame nv sv n l lp siv civ ++
    [(.base ⟨15⟩, ki64 bv), (.base ⟨16⟩, ki64 0)]
def kHeapM (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ bv cv iv : Int)
    (ffv : Bool) : Heap :=
  kHeapKFrame nv sv n l lp siv civ ++
    [(.base ⟨15⟩, ki64 bv), (.base ⟨16⟩, ki64 cv), (.base ⟨17⟩, kint iv),
     (.base ⟨18⟩, kbool ffv)]

/-- The state just before the `$res0 = pre` store (the one epilogue
step whose value is a symbolic array). -/
def kHeapPreStore (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ bv cv iv : Int) : Heap :=
  kHeapSu nv sv n l siv false ++
    [(.base ⟨9⟩, kArr8 lp), (.base ⟨10⟩, ki64 civ), (.base ⟨11⟩, kbool false),
     (.base ⟨12⟩, ki64 (IntKind.normalize .int64
        (IntKind.normalize .int64 bv))),
     (.base ⟨13⟩, kHandle n),
     (.base ⟨14⟩, ki64 (IntKind.normalize .int64 bv)),
     (.base ⟨15⟩, ki64 bv), (.base ⟨16⟩, ki64 cv), (.base ⟨17⟩, kint iv),
     (.base ⟨18⟩, kbool false)]

/-- Same, with `pre` delivered into `$res0`. -/
def kHeapStored (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ bv cv iv : Int) : Heap :=
  [(.base ⟨0⟩, ki64 nv), (.base ⟨1⟩, ki64 sv), (.base ⟨2⟩, kArr8 lp),
   (.base ⟨3⟩, ki64 0),
   (.base ⟨4⟩, kHandle n), (.base ⟨5⟩, kBack n l), (.base ⟨6⟩, kHandle n),
   (.base ⟨7⟩, ki64 siv), (.base ⟨8⟩, kbool false),
   (.base ⟨9⟩, kArr8 lp), (.base ⟨10⟩, ki64 civ), (.base ⟨11⟩, kbool false),
   (.base ⟨12⟩, ki64 (IntKind.normalize .int64
      (IntKind.normalize .int64 bv))),
   (.base ⟨13⟩, kHandle n),
   (.base ⟨14⟩, ki64 (IntKind.normalize .int64 bv)),
   (.base ⟨15⟩, ki64 bv), (.base ⟨16⟩, ki64 cv), (.base ⟨17⟩, kint iv),
   (.base ⟨18⟩, kbool false)]

/-- The terminal heap. -/
def kHeapEnd (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ bv cv iv : Int) : Heap :=
  [(.base ⟨0⟩, ki64 nv), (.base ⟨1⟩, ki64 sv), (.base ⟨2⟩, kArr8 lp),
   (.base ⟨3⟩, ki64 (IntKind.normalize .int64 (IntKind.normalize .int64
      (IntKind.normalize .int64 bv)))),
   (.base ⟨4⟩, kHandle n), (.base ⟨5⟩, kBack n l), (.base ⟨6⟩, kHandle n),
   (.base ⟨7⟩, ki64 siv), (.base ⟨8⟩, kbool false),
   (.base ⟨9⟩, kArr8 lp), (.base ⟨10⟩, ki64 civ), (.base ⟨11⟩, kbool false),
   (.base ⟨12⟩, ki64 (IntKind.normalize .int64
      (IntKind.normalize .int64 bv))),
   (.base ⟨13⟩, kHandle n),
   (.base ⟨14⟩, ki64 (IntKind.normalize .int64 bv)),
   (.base ⟨15⟩, ki64 bv), (.base ⟨16⟩, ki64 cv), (.base ⟨17⟩, kint iv),
   (.base ⟨18⟩, kbool false)]

/-- The guard path's terminal heap (`n = 0`): `$res0` holds the
(all-zero) pre array, `$res1` the guard's `0`. -/
def kHeapGEnd (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int) :
    Heap :=
  [(.base ⟨0⟩, ki64 nv), (.base ⟨1⟩, ki64 sv), (.base ⟨2⟩, kArr8 lp),
   (.base ⟨3⟩, ki64 0),
   (.base ⟨4⟩, kHandle n), (.base ⟨5⟩, kBack n l), (.base ⟨6⟩, kHandle n),
   (.base ⟨7⟩, ki64 siv), (.base ⟨8⟩, kbool false),
   (.base ⟨9⟩, kArr8 lp), (.base ⟨10⟩, ki64 civ), (.base ⟨11⟩, kbool false),
   (.base ⟨12⟩, ki64 0), (.base ⟨13⟩, kHandle n), (.base ⟨14⟩, ki64 0)]

/-- The pinned program as an empty-heap state. -/
def kdProg : ExecState :=
  { types := kadaneLowered.typeDefs.toList,
    functions := kadaneLowered.funcs,
    methods := kadaneLowered.methods,
    heap := [], nextAddr := 0 }

derive_entry_eq kdH_entry_eq kadaneLowered kadaneHarnessRFunc kdHSeed kdHC0 kdProg

/-! ## Heap-lookup facts -/

theorem lookup_kSu (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (kSt σ (kHeapSu nv sv n l iv ffv) na).heap (.base ⟨5⟩)
      = some ⟨some (.array n (.int .int64)),
          .array ⟨l.map (fun v => .int v .int64)⟩⟩ := by
  simp [kHeapSu, kHeap0, Heap.lookup, kBack]

theorem lookup_kCpS (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (kSt σ (kHeapCp nv sv n l lp siv civ ffv) na).heap
        (.base ⟨5⟩)
      = some ⟨some (.array n (.int .int64)),
          .array ⟨l.map (fun v => .int v .int64)⟩⟩ := by
  simp [kHeapCp, kHeapSu, kHeap0, Heap.lookup, kBack]

theorem lookup_kCpPre (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (kSt σ (kHeapCp nv sv n l lp siv civ ffv) na).heap
        (.base ⟨9⟩)
      = some ⟨some (.array 8 (.int .int64)),
          .array ⟨lp.map (fun v => .int v .int64)⟩⟩ := by
  simp [kHeapCp, kHeapSu, kHeap0, Heap.lookup, kArr8]

theorem lookup_kP1 (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (na : Nat) :
    Heap.lookup (kSt σ (kHeapP1 nv sv n l lp siv civ) na).heap (.base ⟨5⟩)
      = some ⟨some (.array n (.int .int64)),
          .array ⟨l.map (fun v => .int v .int64)⟩⟩ := by
  simp [kHeapP1, kHeapKFrame, kHeapCall, kHeapCp, kHeapSu, kHeap0,
    Heap.lookup, kBack]

theorem lookup_kKB (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ bv : Int) (na : Nat) :
    Heap.lookup (kSt σ (kHeapKB nv sv n l lp siv civ bv) na).heap
        (.base ⟨5⟩)
      = some ⟨some (.array n (.int .int64)),
          .array ⟨l.map (fun v => .int v .int64)⟩⟩ := by
  simp [kHeapKB, kHeapKFrame, kHeapCall, kHeapCp, kHeapSu, kHeap0,
    Heap.lookup, kBack]

theorem lookup_kM (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ bv cv iv : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (kSt σ (kHeapM nv sv n l lp siv civ bv cv iv ffv) na).heap
        (.base ⟨5⟩)
      = some ⟨some (.array n (.int .int64)),
          .array ⟨l.map (fun v => .int v .int64)⟩⟩ := by
  simp [kHeapM, kHeapKFrame, kHeapCall, kHeapCp, kHeapSu, kHeap0,
    Heap.lookup, kBack]

theorem lookup_kPreStore (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ bv cv iv : Int) (na : Nat) :
    Heap.lookup
        (kSt σ (kHeapPreStore nv sv n l lp siv civ bv cv iv) na).heap
        (.base ⟨2⟩)
      = some ⟨some (.array 8 (.int .int64)),
          .array ⟨kZeros8.map (fun v => .int v .int64)⟩⟩ := by
  simp [kHeapPreStore, kHeapSu, kHeap0, Heap.lookup, kArr8]

theorem lookup_kGFrame (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (na : Nat) :
    Heap.lookup (kSt σ (kHeapKFrame nv sv n l lp siv civ) na).heap
        (.base ⟨2⟩)
      = some ⟨some (.array 8 (.int .int64)),
          .array ⟨kZeros8.map (fun v => .int v .int64)⟩⟩ := by
  simp [kHeapKFrame, kHeapCall, kHeapCp, kHeapSu, kHeap0, Heap.lookup,
    kArr8]

/-! ## Raw run segments — PROGRAM-generic throughout
(`with_unfolding_all rfl`: definitional evaluation split exactly at the
data-dependent points). -/

/-- Entry A: body start → the `$c8` makeSlice apply point. 10 steps. -/
theorem kd_E1_raw (σ : ExecState) (nv sv : Int) (ch : Choices) :
    stepFnIter 10 (kSt σ (kHeap0 nv sv) 4) kdHC0 ch
      = .ok (.retV (.int nv .int64)
          (.stmtOpK (.makeSlice (.int .int64) false) 1
            [.addr (.base ⟨4⟩)] [] kEnvC8 kdTail0),
        kSt σ (kHeapC8 nv sv) 5, ch) := by
  with_unfolding_all rfl

/-- `make([]int64, n)` at SYMBOLIC `n`. -/
theorem kd_make_apply (σ : ExecState) (nv sv : Int) (n : Nat)
    (ch : Choices) :
    applyStmtOp (kSt σ (kHeapC8 nv sv) 5) ch
      (.makeSlice (.int .int64) false) 1
      [.addr (.base ⟨4⟩), .int (n : Nat) .int64]
      = .ok (kSt σ (kHeapMake nv sv n) 6, ch) := by
  have hnat : ∀ t : String,
      natFromNonnegativeInt t ((n : Nat) : Int) = .ok n := by
    intro t
    simp only [natFromNonnegativeInt]
    rw [if_neg (by omega : ¬ (((n : Nat) : Int) < 0))]
    rfl
  have hback := GoLean.Iris.buildDefaultArrayValue_int
    (kSt σ (kHeapC8 nv sv) 5) .int64 n
  simp only [applyStmtOp, applyStmtOpCore, valueAsInt, Bind.bind,
    Except.bind, pure, Except.pure, hnat, hback]
  rw [if_neg (by omega : ¬ (n < n))]
  simp only [ExecState.alloc, ExecState.freshLoc, valueAsLoc, Except.bind,
    storeLoc, Heap.lookup, normalizeValueForTy, normalizeValueForTyFuel,
    typeResolutionFuel, Heap.set, pure, Except.pure, kSt, kHeapC8,
    kHeapMake, kHeap0, kBack, kHandle, kSliceS, ki64, kArr8, kNilSlice,
    kZeros8, List.map_replicate]
  rfl

/-- Entry B: `s := $c8`, the setup counter and flag → the setup loop
head. 42 steps. -/
theorem kd_E2_raw (σ : ExecState) (nv sv : Int) (n : Nat) (ch : Choices) :
    stepFnIter 42 (kSt σ (kHeapMake nv sv n) 6) (.next kdTail0) ch
      = .ok (kdSuHeadCfg,
          kSt σ (kHeapSu nv sv n (List.replicate n 0) 0 true) 9, ch) := by
  with_unfolding_all rfl

/-! ### The setup loop -/

theorem kd_su_A0_raw (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 25 (kSt σ (kHeapSu nv sv n l iv true) 9) kdSuHeadCfg ch
      = .ok (.retV (.bool (decide (iv < nv))) kdSuCmpK,
          kSt σ (kHeapSu nv sv n l iv false) 9, ch) := by
  with_unfolding_all rfl

theorem kd_su_A1_raw (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 29 (kSt σ (kHeapSu nv sv n l iv false) 9) kdSuHeadCfg ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .int64 (IntKind.normalize .int64 (iv + 1))
              < nv))) kdSuCmpK,
          kSt σ (kHeapSu nv sv n l
            (IntKind.normalize .int64 (IntKind.normalize .int64 (iv + 1)))
            false) 9, ch) := by
  with_unfolding_all rfl

/-- Setup phase 1: test true → the `s[i] = seed + i` store pending.
18 steps. -/
theorem kd_su_B1_raw (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 18 (kSt σ (kHeapSu nv sv n l iv false) 9)
      (.retV (.bool true) kdSuCmpK) ch
      = .ok (.next (.storeK [kdSuRef n iv]
            [.int (IntKind.normalize .int64 (sv + iv)) .int64]
            (.seqn #[]) kSuEnv2 kdSuStTail),
          kSt σ (kHeapSu nv sv n l iv false) 9, ch) := by
  with_unfolding_all rfl

/-- Setup phase 2: store drained → the parity test's delivery.
13 steps. -/
theorem kd_su_C_raw (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 13 (kSt σ (kHeapSu nv sv n l iv false) 9)
      (.next (.storeK [] [] (.seqn #[]) kSuEnv2 kdSuStTail)) ch
      = .ok (.retV (.bool
            (IntKind.normalize .int64 (Int.tmod iv 2) == 1)) kdSuParityIfK,
          kSt σ (kHeapSu nv sv n l iv false) 9, ch) := by
  with_unfolding_all rfl

/-- Even join: parity false → the loop head. 5 steps. -/
theorem kd_su_E_raw (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 5 (kSt σ (kHeapSu nv sv n l iv false) 9)
      (.retV (.bool false) kdSuParityIfK) ch
      = .ok (kdSuHeadCfg, kSt σ (kHeapSu nv sv n l iv false) 9, ch) := by
  with_unfolding_all rfl

/-- Odd phase 1: parity true → the `s[i]` read at its apply point.
15 steps. -/
theorem kd_su_O1_raw (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 15 (kSt σ (kHeapSu nv sv n l iv false) 9)
      (.retV (.bool true) kdSuParityIfK) ch
      = .ok (.retV (.int iv .int64)
            (.strictK .indexGet [kSliceS n] [] kSuEnv3
              (.strictK .neg [] [] kSuEnv3 (kdSuNegRhsK n iv))),
          kSt σ (kHeapSu nv sv n l iv false) 9, ch) := by
  with_unfolding_all rfl

/-- Odd phase 2: the read value delivered → negated, the second store
pending. 2 steps. -/
theorem kd_su_O2_raw (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv w : Int) (ch : Choices) :
    stepFnIter 2 (kSt σ (kHeapSu nv sv n l iv false) 9)
      (.retV (.int w .int64) (.strictK .neg [] [] kSuEnv3
        (kdSuNegRhsK n iv))) ch
      = .ok (.next (.storeK [kdSuRef n iv]
            [.int (IntKind.normalize .int64 (0 - w)) .int64]
            (.seqn #[]) kSuEnv3 kdSuNegStTail),
          kSt σ (kHeapSu nv sv n l iv false) 9, ch) := by
  with_unfolding_all rfl

/-- Odd join: second store drained → the loop head. 6 steps. -/
theorem kd_su_O3_raw (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 6 (kSt σ (kHeapSu nv sv n l iv false) 9)
      (.next (.storeK [] [] (.seqn #[]) kSuEnv3 kdSuNegStTail)) ch
      = .ok (kdSuHeadCfg, kSt σ (kHeapSu nv sv n l iv false) 9, ch) := by
  with_unfolding_all rfl

/-- Setup exit: test false → `var pre` declared and the copy loop head.
39 steps. -/
theorem kd_su_X_raw (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 39 (kSt σ (kHeapSu nv sv n l iv false) 9)
      (.retV (.bool false) kdSuCmpK) ch
      = .ok (kdCpHeadCfg,
          kSt σ (kHeapCp nv sv n l kZeros8 iv 0 true) 12, ch) := by
  with_unfolding_all rfl

/-! ### The copy loop -/

theorem kd_cp_A0_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 25 (kSt σ (kHeapCp nv sv n l lp siv civ true) 12)
      kdCpHeadCfg ch
      = .ok (.retV (.bool (decide (civ < nv))) kdCpCmpK,
          kSt σ (kHeapCp nv sv n l lp siv civ false) 12, ch) := by
  with_unfolding_all rfl

theorem kd_cp_A1_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 29 (kSt σ (kHeapCp nv sv n l lp siv civ false) 12)
      kdCpHeadCfg ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .int64 (IntKind.normalize .int64 (civ + 1))
              < nv))) kdCpCmpK,
          kSt σ (kHeapCp nv sv n l lp siv
            (IntKind.normalize .int64 (IntKind.normalize .int64 (civ + 1)))
            false) 12, ch) := by
  with_unfolding_all rfl

/-- Copy phase 1: test true → the `pre[i]` target banked, the `s[i]`
read at its apply point. 16 steps. -/
theorem kd_cp_B1_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 16 (kSt σ (kHeapCp nv sv n l lp siv civ false) 12)
      (.retV (.bool true) kdCpCmpK) ch
      = .ok (.retV (.int civ .int64)
            (.strictK .indexGet [kSliceS n] [] kCpEnv2 (kdCpRhsK civ)),
          kSt σ (kHeapCp nv sv n l lp siv civ false) 12, ch) := by
  with_unfolding_all rfl

theorem kd_cp_B2_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1 (kSt σ (kHeapCp nv sv n l lp siv civ false) 12)
      (.retV w (kdCpRhsK civ)) ch
      = .ok (.next (.storeK [kdCpRef civ] [w] (.seqn #[]) kCpEnv2
            kdCpStTail),
          kSt σ (kHeapCp nv sv n l lp siv civ false) 12, ch) := by
  with_unfolding_all rfl

theorem kd_cp_D_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 5 (kSt σ (kHeapCp nv sv n l lp siv civ false) 12)
      (.next (.storeK [] [] (.seqn #[]) kCpEnv2 kdCpStTail)) ch
      = .ok (kdCpHeadCfg, kSt σ (kHeapCp nv sv n l lp siv civ false) 12,
          ch) := by
  with_unfolding_all rfl

/-- Copy exit: test false → `best` declared and the `kadane(s)` argument
delivered at the drained `callArgsK`. 13 steps. -/
theorem kd_cp_X_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 13 (kSt σ (kHeapCp nv sv n l lp siv civ false) 12)
      (.retV (.bool false) kdCpCmpK) ch
      = .ok (.retV (kSliceS n) kdCallArgsK,
          kSt σ (kHeapCall nv sv n l lp siv civ) 13, ch) := by
  with_unfolding_all rfl

/-! ### The kadane frame -/

/-- The `enterFrame` discharge at the pinned program. -/
theorem kd_enterFrame_fact (n : Nat) (nv sv : Int) (l lp : List Int)
    (siv civ : Int) :
    enterFrame (kSt kdProg (kHeapCall nv sv n l lp siv civ) 13)
        ⟨"kadane"⟩ [kSliceS n]
      = .ok (kadaneFunc, kEnvB, [.base ⟨14⟩],
          kSt kdProg (kHeapKFrame nv sv n l lp siv civ) 15) := by
  with_unfolding_all rfl

/-- Guard phase 1: frame body start → the `len(s)` apply point.
6 steps. -/
theorem kd_g1_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 6 (kSt σ (kHeapKFrame nv sv n l lp siv civ) 15)
      (.exec kadaneFunc.body kEnvB kFrameK) ch
      = .ok (.retV (kSliceS n) kGLenK,
          kSt σ (kHeapKFrame nv sv n l lp siv civ) 15, ch) := by
  with_unfolding_all rfl

/-- Guard phase 2: the length delivered → the `== 0` test's delivery.
3 steps. -/
theorem kd_g2_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (w : Int) (ch : Choices) :
    stepFnIter 3 (kSt σ (kHeapKFrame nv sv n l lp siv civ) 15)
      (.retV (.int w .int) kGEqK) ch
      = .ok (.retV (.bool (w == 0)) kGuardIfK,
          kSt σ (kHeapKFrame nv sv n l lp siv civ) 15, ch) := by
  with_unfolding_all rfl

/-- The guard-TRUE path (`n = 0`): `$res0 = 0`, return, frame exit into
the harness's `best`, harness epilogue up to the `$res0 = pre` store.
31 steps. -/
theorem kd_gT_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 31 (kSt σ (kHeapKFrame nv sv n l lp siv civ) 15)
      (.retV (.bool true) kGuardIfK) ch
      = .ok (.next (.storeK [kdRes0Ref]
            [.array ⟨lp.map (fun v => .int v .int64)⟩] (.seqn #[])
            kCallEnv kdEpiTail),
          kSt σ (kHeapKFrame nv sv n l lp siv civ) 15, ch) := by
  with_unfolding_all rfl

/-- The guard path's tail: `$res1 = best` (= 0), return — the driver
terminal. 15 steps. -/
theorem kd_gX_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 15 (kSt σ (kHeapGEnd nv sv n l lp siv civ) 15)
      (.next (.storeK [] [] (.seqn #[]) kCallEnv kdEpiTail)) ch
      = .ok (.next .stop, kSt σ (kHeapGEnd nv sv n l lp siv civ) 15,
          ch) := by
  with_unfolding_all rfl

/-- Prologue 1: guard false → `best` declared, the first `s[0]` read at
its apply point. 14 steps. -/
theorem kd_p1_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 14 (kSt σ (kHeapKFrame nv sv n l lp siv civ) 15)
      (.retV (.bool false) kGuardIfK) ch
      = .ok (.retV (.int 0 .int)
            (.strictK .indexGet [kSliceS n] [] kEnvG1 kBestRhsK),
          kSt σ (kHeapP1 nv sv n l lp siv civ) 16, ch) := by
  with_unfolding_all rfl

/-- Prologue 2: `best` stored, `cur` declared, the second `s[0]` read at
its apply point. 16 steps. -/
theorem kd_p2_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ w : Int) (ch : Choices) :
    stepFnIter 16 (kSt σ (kHeapP1 nv sv n l lp siv civ) 16)
      (.retV (.int w .int64) kBestRhsK) ch
      = .ok (.retV (.int 0 .int)
            (.strictK .indexGet [kSliceS n] [] kEnvBC kCurRhsK),
          kSt σ (kHeapKB nv sv n l lp siv civ
            (IntKind.normalize .int64 w)) 17, ch) := by
  with_unfolding_all rfl

/-- Prologue 3: `cur` stored, `i := 1`, the flag → the loop head.
33 steps. -/
theorem kd_p3_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ bv w : Int) (ch : Choices) :
    stepFnIter 33 (kSt σ (kHeapKB nv sv n l lp siv civ bv) 17)
      (.retV (.int w .int64) kCurRhsK) ch
      = .ok (kHeadCfg,
          kSt σ (kHeapM nv sv n l lp siv civ bv
            (IntKind.normalize .int64 w) 1 true) 19, ch) := by
  with_unfolding_all rfl

/-! ### The kadane loop -/

theorem kd_dispA_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ bv cv iv : Int) (ch : Choices) :
    stepFnIter 25 (kSt σ (kHeapM nv sv n l lp siv civ bv cv iv true) 19)
      kHeadCfg ch
      = .ok (.retV (kSliceS n) (kLenApplyK iv),
          kSt σ (kHeapM nv sv n l lp siv civ bv cv iv false) 19, ch) := by
  with_unfolding_all rfl

theorem kd_dispB_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ bv cv iv : Int) (ch : Choices) :
    stepFnIter 29 (kSt σ (kHeapM nv sv n l lp siv civ bv cv iv false) 19)
      kHeadCfg ch
      = .ok (.retV (kSliceS n)
            (kLenApplyK
              (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
          kSt σ (kHeapM nv sv n l lp siv civ bv cv
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            false) 19, ch) := by
  with_unfolding_all rfl

/-- Body phase 1: test true → the `cur < 0` test's delivery.
11 steps. -/
theorem kd_b1_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ bv cv iv : Int) (ch : Choices) :
    stepFnIter 11 (kSt σ (kHeapM nv sv n l lp siv civ bv cv iv false) 19)
      (.retV (.bool true) kCmpIfK) ch
      = .ok (.retV (.bool (decide (cv < 0))) kCurIfK,
          kSt σ (kHeapM nv sv n l lp siv civ bv cv iv false) 19, ch) := by
  with_unfolding_all rfl

/-- Restart branch (`cur < 0`): to the `s[i]` read. 12 steps. -/
theorem kd_b2T_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ bv cv iv : Int) (ch : Choices) :
    stepFnIter 12 (kSt σ (kHeapM nv sv n l lp siv civ bv cv iv false) 19)
      (.retV (.bool true) kCurIfK) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [kSliceS n] [] kEnvE kCurSetRhsK),
          kSt σ (kHeapM nv sv n l lp siv civ bv cv iv false) 19, ch) := by
  with_unfolding_all rfl

/-- Restart branch tail: the read delivered → `cur` stored, the
`cur > best` test's delivery. 12 steps. -/
theorem kd_b3T_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ bv cv iv w : Int) (ch : Choices) :
    stepFnIter 12 (kSt σ (kHeapM nv sv n l lp siv civ bv cv iv false) 19)
      (.retV (.int w .int64) kCurSetRhsK) ch
      = .ok (.retV (.bool (decide (bv < IntKind.normalize .int64 w)))
            kBestIfK,
          kSt σ (kHeapM nv sv n l lp siv civ bv
            (IntKind.normalize .int64 w) iv false) 19, ch) := by
  with_unfolding_all rfl

/-- Extend branch (`cur ≥ 0`): to the `s[i]` read under the pending
`cur + _` apply. 15 steps. -/
theorem kd_b2F_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ bv cv iv : Int) (ch : Choices) :
    stepFnIter 15 (kSt σ (kHeapM nv sv n l lp siv civ bv cv iv false) 19)
      (.retV (.bool false) kCurIfK) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [kSliceS n] [] kEnvE
              (.strictK .add [.int cv .int64] [] kEnvE kCurSetRhsK)),
          kSt σ (kHeapM nv sv n l lp siv civ bv cv iv false) 19, ch) := by
  with_unfolding_all rfl

/-- Extend branch tail: the read delivered → summed, `cur` stored, the
`cur > best` test's delivery. 13 steps. -/
theorem kd_b3F_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ bv cv iv w : Int) (ch : Choices) :
    stepFnIter 13 (kSt σ (kHeapM nv sv n l lp siv civ bv cv iv false) 19)
      (.retV (.int w .int64)
        (.strictK .add [.int cv .int64] [] kEnvE kCurSetRhsK)) ch
      = .ok (.retV (.bool (decide (bv < IntKind.normalize .int64
              (IntKind.normalize .int64 (cv + w))))) kBestIfK,
          kSt σ (kHeapM nv sv n l lp siv civ bv
            (IntKind.normalize .int64 (IntKind.normalize .int64 (cv + w)))
            iv false) 19, ch) := by
  with_unfolding_all rfl

/-- Best-update branch: `best` stored from `cur` → the loop head.
17 steps. -/
theorem kd_b4T_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ bv cv iv : Int) (ch : Choices) :
    stepFnIter 17 (kSt σ (kHeapM nv sv n l lp siv civ bv cv iv false) 19)
      (.retV (.bool true) kBestIfK) ch
      = .ok (kHeadCfg,
          kSt σ (kHeapM nv sv n l lp siv civ
            (IntKind.normalize .int64 cv) cv iv false) 19, ch) := by
  with_unfolding_all rfl

/-- Best unchanged → the loop head. 5 steps. -/
theorem kd_b4F_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ bv cv iv : Int) (ch : Choices) :
    stepFnIter 5 (kSt σ (kHeapM nv sv n l lp siv civ bv cv iv false) 19)
      (.retV (.bool false) kBestIfK) ch
      = .ok (kHeadCfg,
          kSt σ (kHeapM nv sv n l lp siv civ bv cv iv false) 19, ch) := by
  with_unfolding_all rfl

/-- Exit A: test false → break unwinding, `$res0 = best`, return, frame
exit into the harness's `best`, harness epilogue up to the `$res0 = pre`
store. 34 steps. -/
theorem kd_X1_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ bv cv iv : Int) (ch : Choices) :
    stepFnIter 34 (kSt σ (kHeapM nv sv n l lp siv civ bv cv iv false) 19)
      (.retV (.bool false) kCmpIfK) ch
      = .ok (.next (.storeK [kdRes0Ref]
            [.array ⟨lp.map (fun v => .int v .int64)⟩] (.seqn #[])
            kCallEnv kdEpiTail),
          kSt σ (kHeapPreStore nv sv n l lp siv civ bv cv iv) 19,
          ch) := by
  with_unfolding_all rfl

/-- Exit B: `$res1 = best`, return — the driver terminal. 15 steps. -/
theorem kd_X2_raw (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ bv cv iv : Int) (ch : Choices) :
    stepFnIter 15 (kSt σ (kHeapStored nv sv n l lp siv civ bv cv iv) 19)
      (.next (.storeK [] [] (.seqn #[]) kCallEnv kdEpiTail)) ch
      = .ok (.next .stop,
          kSt σ (kHeapEnd nv sv n l lp siv civ bv cv iv) 19, ch) := by
  with_unfolding_all rfl

/-! ## The setup loop, cleaned + its induction -/

/-- One setup iteration: both parities, branch-uniform bound 86 (the
odd branch's extra read/negate/store costs 20 over the even 66). -/
theorem kd_su_iter (σ : ExecState) (n : Nat) (seed : Int) (m : Nat)
    (hcap : n ≤ 8) (hs1 : -(2 ^ 59) ≤ seed) (hs2 : seed ≤ 2 ^ 59)
    (hm : m < n) (ch : Choices) :
    ∃ k : Nat, k ≤ 86 ∧
      stepFnIter k
        (kSt σ (kHeapSu ((n : Nat) : Int) seed n (kadPad n m seed)
          ((m : Nat) : Int) false) 9)
        (.retV (.bool true) kdSuCmpK) ch
        = .ok (.retV (.bool (decide
              (((m + 1 : Nat) : Int) < ((n : Nat) : Int)))) kdSuCmpK,
            kSt σ (kHeapSu ((n : Nat) : Int) seed n (kadPad n (m + 1) seed)
              ((m + 1 : Nat) : Int) false) 9, ch) := by
  have hmi : ((m : Nat) : Int) ≤ 8 := by
    have : m ≤ 8 := by omega
    exact_mod_cast this
  have hsm : -(2 ^ 63) ≤ seed + ((m : Nat) : Int)
      ∧ seed + ((m : Nat) : Int) < 2 ^ 63 := by omega
  have hpadlen : (kadPad n m seed).length = n := kadPad_length (by omega)
  have hpadr : ∀ v ∈ kadPad n m seed, -(2 ^ 63) ≤ v ∧ v < 2 ^ 63 := by
    intro v hv
    have := kadPad_range (by omega) (by omega) hs1 hs2 v hv
    omega
  -- phase 1: the `s[i] = seed + i` store
  have hB1 := kd_su_B1_raw σ ((n : Nat) : Int) seed n (kadPad n m seed)
    ((m : Nat) : Int) ch
  rw [inorm64_of_range hsm.1 hsm.2] at hB1
  have hst1 : storeTarget
      (kSt σ (kHeapSu ((n : Nat) : Int) seed n (kadPad n m seed)
        ((m : Nat) : Int) false) 9)
      (kdSuRef n ((m : Nat) : Int))
      (.int (seed + ((m : Nat) : Int)) .int64)
      = .ok (kSt σ (kHeapSu ((n : Nat) : Int) seed n
          ((kadPad n m seed).set m (seed + ((m : Nat) : Int)))
          ((m : Nat) : Int) false) 9) := by
    have h := storeTarget_slice_i64 (a := ⟨5⟩) (off := 0) (len := n)
      (cap := n) (i := m) (n := n) (ik := .int64) (l := kadPad n m seed)
      (w := seed + ((m : Nat) : Int))
      (lookup_kSu σ ((n : Nat) : Int) seed n (kadPad n m seed)
        ((m : Nat) : Int) false 9)
      (Nat.le_refl _) hm (by omega) hpadlen hpadr ⟨hsm.1, hsm.2⟩
    rw [Nat.zero_add] at h
    exact h
  -- phase 2: the parity test
  have hC := kd_su_C_raw σ ((n : Nat) : Int) seed n
    ((kadPad n m seed).set m (seed + ((m : Nat) : Int)))
    ((m : Nat) : Int) ch
  rw [show Int.tmod ((m : Nat) : Int) 2 = ((m % 2 : Nat) : Int) from rfl,
    inorm64_nat_of_lt (by omega)] at hC
  -- the A1 dispatch, increments collapsed
  have hA1 : ∀ l' : List Int,
      stepFnIter 29 (kSt σ (kHeapSu ((n : Nat) : Int) seed n l'
          ((m : Nat) : Int) false) 9) kdSuHeadCfg ch
        = .ok (.retV (.bool (decide
              (((m + 1 : Nat) : Int) < ((n : Nat) : Int)))) kdSuCmpK,
            kSt σ (kHeapSu ((n : Nat) : Int) seed n l'
              ((m + 1 : Nat) : Int) false) 9, ch) := by
    intro l'
    have h := kd_su_A1_raw σ ((n : Nat) : Int) seed n l'
      ((m : Nat) : Int) ch
    rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
      inorm64_nat_of_lt (by omega), inorm64_nat_of_lt (by omega)] at h
    exact h
  by_cases hpar : m % 2 = 1
  · -- ODD: read back, negate, store again
    rw [show ((((m % 2 : Nat)) : Int) == 1) = true from by
      rw [hpar]; decide] at hC
    rw [kadMid_of_set hm] at hst1 hC
    have hO1 := kd_su_O1_raw σ ((n : Nat) : Int) seed n (kadMid n m seed)
      ((m : Nat) : Int) ch
    have hget : (⟨(kadMid n m seed).map (fun v => .int v .int64)⟩ :
        Array GoValue)[0 + m]?
        = some (.int (seed + ((m : Nat) : Int)) .int64) := by
      rw [Nat.zero_add, getElem?_mapI _ _ (by rw [kadMid_length hm]; omega),
        kadMid_getD hm]
    have hread := stepFn_strict_apply (done := [kSliceS n]) (env := kSuEnv3)
      (k := .strictK .neg [] [] kSuEnv3 (kdSuNegRhsK n ((m : Nat) : Int)))
      (ch := ch)
      (applyStrictOp_indexGet_slice (ik := .int64)
        (lookup_kSu σ ((n : Nat) : Int) seed n (kadMid n m seed)
          ((m : Nat) : Int) false 9)
        (Nat.le_refl n) hm hget)
    have hO2 := kd_su_O2_raw σ ((n : Nat) : Int) seed n (kadMid n m seed)
      ((m : Nat) : Int) (seed + ((m : Nat) : Int)) ch
    rw [show (0 : Int) - (seed + ((m : Nat) : Int))
        = -(seed + ((m : Nat) : Int)) from by omega,
      inorm64_of_range (by omega) (by omega)] at hO2
    have hmidr : ∀ v ∈ kadMid n m seed, -(2 ^ 63) ≤ v ∧ v < 2 ^ 63 := by
      intro v hv
      have := kadMid_range hm (by omega) hs1 hs2 v hv
      omega
    have hst2 : storeTarget
        (kSt σ (kHeapSu ((n : Nat) : Int) seed n (kadMid n m seed)
          ((m : Nat) : Int) false) 9)
        (kdSuRef n ((m : Nat) : Int))
        (.int (-(seed + ((m : Nat) : Int))) .int64)
        = .ok (kSt σ (kHeapSu ((n : Nat) : Int) seed n
            (kadPad n (m + 1) seed) ((m : Nat) : Int) false) 9) := by
      have h := storeTarget_slice_i64 (a := ⟨5⟩) (off := 0) (len := n)
        (cap := n) (i := m) (n := n) (ik := .int64) (l := kadMid n m seed)
        (w := -(seed + ((m : Nat) : Int)))
        (lookup_kSu σ ((n : Nat) : Int) seed n (kadMid n m seed)
          ((m : Nat) : Int) false 9)
        (Nat.le_refl _) hm (by rw [kadMid_length hm]; omega)
        (kadMid_length hm) hmidr ⟨by omega, by omega⟩
      rw [Nat.zero_add,
        show ((kadMid n m seed).set m (-(seed + ((m : Nat) : Int))))
          = kadPad n (m + 1) seed from kadMid_set_odd hm hpar] at h
      exact h
    have hO3 := kd_su_O3_raw σ ((n : Nat) : Int) seed n
      (kadPad n (m + 1) seed) ((m : Nat) : Int) ch
    refine ⟨18 + 1 + 13 + 15 + 1 + 2 + 1 + 6 + 29, by omega, ?_⟩
    exact stepFnIter_chain
      (stepFnIter_chain
        (stepFnIter_chain
          (stepFnIter_chain
            (stepFnIter_chain
              (stepFnIter_chain
                (stepFnIter_chain
                  (stepFnIter_chain hB1
                    (stepFnIter_one (stepFn_store_step hst1)))
                  hC)
                hO1)
              (stepFnIter_one hread))
            hO2)
          (stepFnIter_one (stepFn_store_step hst2)))
        hO3)
      (hA1 _)
  · -- EVEN: the first store already landed the family value
    have hev : m % 2 = 0 := by omega
    rw [show ((((m % 2 : Nat)) : Int) == 1) = false from by
      rw [hev]; decide] at hC
    rw [show ((kadPad n m seed).set m (seed + ((m : Nat) : Int)))
        = kadPad n (m + 1) seed from kadPad_set_even hm hev] at hst1 hC
    have hE := kd_su_E_raw σ ((n : Nat) : Int) seed n
      (kadPad n (m + 1) seed) ((m : Nat) : Int) ch
    refine ⟨18 + 1 + 13 + 5 + 29, by omega, ?_⟩
    exact stepFnIter_chain
      (stepFnIter_chain
        (stepFnIter_chain
          (stepFnIter_chain hB1 (stepFnIter_one (stepFn_store_step hst1)))
          hC)
        hE)
      (hA1 _)

/-- The setup loop, iterated to its exit: reaches the copy loop head. -/
theorem kd_su_loop (σ : ExecState) (n : Nat) (seed : Int)
    (hcap : n ≤ 8) (hs1 : -(2 ^ 59) ≤ seed) (hs2 : seed ≤ 2 ^ 59) :
    ∀ μ m : Nat, m + μ = n → ∀ ch : Choices,
    ∃ k : Nat, k ≤ 86 * μ + 39 ∧
      stepFnIter k
        (kSt σ (kHeapSu ((n : Nat) : Int) seed n (kadPad n m seed)
          ((m : Nat) : Int) false) 9)
        (.retV (.bool (decide (((m : Nat) : Int) < ((n : Nat) : Int))))
          kdSuCmpK) ch
        = .ok (kdCpHeadCfg,
            kSt σ (kHeapCp ((n : Nat) : Int) seed n (kadFamily n seed)
              kZeros8 ((n : Nat) : Int) 0 true) 12, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hm ch
    rcases Nat.lt_or_ge m n with hlt | hge
    · rw [show (decide (((m : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      obtain ⟨k₀, hk₀, hstep⟩ := kd_su_iter σ n seed m hcap hs1 hs2 hlt ch
      obtain ⟨k, hk, hrun⟩ := ih (μ - 1) (by omega) (m + 1) (by omega) ch
      exact ⟨k₀ + k, by omega, stepFnIter_chain hstep hrun⟩
    · have hmn : m = n := by omega
      subst hmn
      rw [show (decide (((m : Nat) : Int) < ((m : Nat) : Int))) = false from
        decide_eq_false (by omega)]
      have hpe : kadPad m m seed = kadFamily m seed := by
        simp [kadPad, Nat.sub_self]
      refine ⟨39, by omega, ?_⟩
      rw [← hpe]
      exact kd_su_X_raw σ ((m : Nat) : Int) seed m (kadPad m m seed)
        ((m : Nat) : Int) ch

/-! ## The copy loop, cleaned + its induction -/

/-- One copy iteration: uniform 53 steps. -/
theorem kd_cp_iter (σ : ExecState) (n : Nat) (seed : Int) (m : Nat)
    (hcap : n ≤ 8) (hs1 : -(2 ^ 59) ≤ seed) (hs2 : seed ≤ 2 ^ 59)
    (hm : m < n) (ch : Choices) :
    stepFnIter 53
      (kSt σ (kHeapCp ((n : Nat) : Int) seed n (kadFamily n seed)
        (kadPad 8 m seed) ((n : Nat) : Int) ((m : Nat) : Int) false) 12)
      (.retV (.bool true) kdCpCmpK) ch
      = .ok (.retV (.bool (decide
            (((m + 1 : Nat) : Int) < ((n : Nat) : Int)))) kdCpCmpK,
          kSt σ (kHeapCp ((n : Nat) : Int) seed n (kadFamily n seed)
            (kadPad 8 (m + 1) seed) ((n : Nat) : Int) ((m + 1 : Nat) : Int)
            false) 12, ch) := by
  have hlenF : (kadFamily n seed).length = n := kadFamily_length n seed
  have hfamr : ∀ v ∈ kadFamily n seed, -(2 ^ 63) ≤ v ∧ v < 2 ^ 63 := by
    intro v hv
    have := kadFamily_range hcap hs1 hs2 v hv
    omega
  have hpadr : ∀ v ∈ kadPad 8 m seed, -(2 ^ 63) ≤ v ∧ v < 2 ^ 63 := by
    intro v hv
    have := kadPad_range (by omega) (by omega) hs1 hs2 v hv
    omega
  have hwv : -(2 ^ 59 + 8) ≤ kadFamVal seed m ∧ kadFamVal seed m ≤ 2 ^ 59 + 8 := by
    have hmi : ((m : Nat) : Int) ≤ 8 := by
      have : m ≤ 8 := by omega
      exact_mod_cast this
    rw [kadFamVal]
    split <;> omega
  have hB1 := kd_cp_B1_raw σ ((n : Nat) : Int) seed n (kadFamily n seed)
    (kadPad 8 m seed) ((n : Nat) : Int) ((m : Nat) : Int) ch
  have hget : (⟨(kadFamily n seed).map (fun v => .int v .int64)⟩ :
      Array GoValue)[0 + m]?
      = some (.int (kadFamVal seed m) .int64) := by
    rw [Nat.zero_add, getElem?_mapI _ _ (by omega), kadFamily_getD hm]
  have hread := stepFn_strict_apply (done := [kSliceS n]) (env := kCpEnv2)
    (k := kdCpRhsK ((m : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .int64)
      (lookup_kCpS σ ((n : Nat) : Int) seed n (kadFamily n seed)
        (kadPad 8 m seed) ((n : Nat) : Int) ((m : Nat) : Int) false 12)
      (Nat.le_refl n) hm hget)
  have hB2 := kd_cp_B2_raw σ ((n : Nat) : Int) seed n (kadFamily n seed)
    (kadPad 8 m seed) ((n : Nat) : Int) ((m : Nat) : Int)
    (.int (kadFamVal seed m) .int64) ch
  have hstore : storeTarget
      (kSt σ (kHeapCp ((n : Nat) : Int) seed n (kadFamily n seed)
        (kadPad 8 m seed) ((n : Nat) : Int) ((m : Nat) : Int) false) 12)
      (kdCpRef ((m : Nat) : Int)) (.int (kadFamVal seed m) .int64)
      = .ok (kSt σ (kHeapCp ((n : Nat) : Int) seed n (kadFamily n seed)
          (kadPad 8 (m + 1) seed) ((n : Nat) : Int) ((m : Nat) : Int)
          false) 12) := by
    have h := storeTarget_arrayLocal_i64 (a := ⟨9⟩) (N := 8) (i := m)
      (ik := .int64) (l := kadPad 8 m seed) (w := kadFamVal seed m)
      (lookup_kCpPre σ ((n : Nat) : Int) seed n (kadFamily n seed)
        (kadPad 8 m seed) ((n : Nat) : Int) ((m : Nat) : Int) false 12)
      (by rw [kadPad_length (by omega)]; omega)
      (kadPad_length (by omega)) hpadr ⟨by omega, by omega⟩
    rw [kadPad_set (by omega : m < 8)] at h
    exact h
  have hD := kd_cp_D_raw σ ((n : Nat) : Int) seed n (kadFamily n seed)
    (kadPad 8 (m + 1) seed) ((n : Nat) : Int) ((m : Nat) : Int) ch
  have hA1 := kd_cp_A1_raw σ ((n : Nat) : Int) seed n (kadFamily n seed)
    (kadPad 8 (m + 1) seed) ((n : Nat) : Int) ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    inorm64_nat_of_lt (by omega), inorm64_nat_of_lt (by omega)] at hA1
  show stepFnIter (16 + 1 + 1 + 1 + 5 + 29) _ _ _ = _
  exact stepFnIter_chain
    (stepFnIter_chain
      (stepFnIter_chain
        (stepFnIter_chain
          (stepFnIter_chain hB1 (stepFnIter_one hread))
          hB2)
        (stepFnIter_one (stepFn_store_step hstore)))
      hD)
    hA1

/-- The copy loop, iterated to its exit: the `kadane(s)` argument
delivered at the drained `callArgsK`. -/
theorem kd_cp_loop (σ : ExecState) (n : Nat) (seed : Int)
    (hcap : n ≤ 8) (hs1 : -(2 ^ 59) ≤ seed) (hs2 : seed ≤ 2 ^ 59) :
    ∀ μ m : Nat, m + μ = n → ∀ ch : Choices,
    ∃ k : Nat, k ≤ 53 * μ + 13 ∧
      stepFnIter k
        (kSt σ (kHeapCp ((n : Nat) : Int) seed n (kadFamily n seed)
          (kadPad 8 m seed) ((n : Nat) : Int) ((m : Nat) : Int) false) 12)
        (.retV (.bool (decide (((m : Nat) : Int) < ((n : Nat) : Int))))
          kdCpCmpK) ch
        = .ok (.retV (kSliceS n) kdCallArgsK,
            kSt σ (kHeapCall ((n : Nat) : Int) seed n (kadFamily n seed)
              (kadPad 8 n seed) ((n : Nat) : Int) ((n : Nat) : Int)) 13,
            ch) := by
  intro μ m hm ch
  have hexit : ∀ ch' : Choices, stepFnIter 13
      (kSt σ (kHeapCp ((n : Nat) : Int) seed n (kadFamily n seed)
        (kadPad 8 n seed) ((n : Nat) : Int) ((n : Nat) : Int) false) 12)
      (.retV (.bool (decide (((n : Nat) : Int) < ((n : Nat) : Int))))
        kdCpCmpK) ch'
      = .ok (.retV (kSliceS n) kdCallArgsK,
          kSt σ (kHeapCall ((n : Nat) : Int) seed n (kadFamily n seed)
            (kadPad 8 n seed) ((n : Nat) : Int) ((n : Nat) : Int)) 13,
          ch') := by
    intro ch'
    rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
      decide_eq_false (by omega)]
    exact kd_cp_X_raw σ ((n : Nat) : Int) seed n (kadFamily n seed)
      (kadPad 8 n seed) ((n : Nat) : Int) ((n : Nat) : Int) ch'
  refine ⟨53 * (n - m) + 13, by omega, ?_⟩
  exact stepFnIter_iterate_exit (c := 53) (e := 13) (n := n)
    (T := fun j => kSt σ (kHeapCp ((n : Nat) : Int) seed n
      (kadFamily n seed) (kadPad 8 j seed) ((n : Nat) : Int)
      ((j : Nat) : Int) false) 12)
    (C := fun j => .retV (.bool (decide
      (((j : Nat) : Int) < ((n : Nat) : Int)))) kdCpCmpK)
    (fun j hj ch'' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact kd_cp_iter σ n seed j hcap hs1 hs2 hj ch'')
    hexit m (by omega) ch

/-! ## The kadane loop, cleaned + its induction -/

/-- One kadane iteration at `1 ≤ m < n`: the state advances from the
scan values at `m` to the scan values at `m + 1`. Branch-uniform bound
88 (worst path: extend + best-update). -/
theorem kd_iter (σ : ExecState) (n : Nat) (sv : Int) (l lp : List Int)
    (m : Nat) (hln : l.length = n)
    (hlr : ∀ v ∈ l, -(2 ^ 59 + 8) ≤ v ∧ v ≤ 2 ^ 59 + 8)
    (hcap : n ≤ 8) (hm1 : 1 ≤ m) (hm : m < n) (ch : Choices) :
    ∃ k : Nat, k ≤ 88 ∧
      stepFnIter k
        (kSt σ (kHeapM ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
          ((n : Nat) : Int) (kadBest l m) (kadCur l m) ((m : Nat) : Int)
          false) 19)
        (.retV (.bool true) kCmpIfK) ch
        = .ok (.retV (.bool (decide
              (((m + 1 : Nat) : Int) < ((n : Nat) : Int)))) kCmpIfK,
            kSt σ (kHeapM ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
              ((n : Nat) : Int) (kadBest l (m + 1)) (kadCur l (m + 1))
              ((m + 1 : Nat) : Int) false) 19, ch) := by
  have hB : (0 : Int) ≤ 2 ^ 59 + 8 := by omega
  have hbnd_m := kad_bounds l (2 ^ 59 + 8) hB hlr m hm1 (by omega)
  have hbnd_m1 := kad_bounds l (2 ^ 59 + 8) hB hlr (m + 1) (by omega)
    (by omega)
  have hmB : ((m : Nat) : Int) * (2 ^ 59 + 8) ≤ 8 * (2 ^ 59 + 8) := by
    apply Int.mul_le_mul_of_nonneg_right _ hB
    have : m ≤ 8 := by omega
    exact_mod_cast this
  have hm1B : ((m + 1 : Nat) : Int) * (2 ^ 59 + 8) ≤ 8 * (2 ^ 59 + 8) := by
    apply Int.mul_le_mul_of_nonneg_right _ hB
    have : m + 1 ≤ 8 := by omega
    exact_mod_cast this
  have hcv1r : -(2 ^ 63) ≤ kadCur l (m + 1)
      ∧ kadCur l (m + 1) < 2 ^ 63 := by
    obtain ⟨⟨h1, h2⟩, -⟩ := hbnd_m1
    omega
  have hw := hlr _ (getD_mem_int (show m < l.length by omega))
  have hget : (⟨l.map (fun v => .int v .int64)⟩ : Array GoValue)[0 + m]?
      = some (.int (l.getD m 0) .int64) := by
    rw [Nat.zero_add, getElem?_mapI _ _ (by omega)]
  have hb1 := kd_b1_raw σ ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
    ((n : Nat) : Int) (kadBest l m) (kadCur l m) ((m : Nat) : Int) ch
  -- the shared dispatch tail from the loop head at the (m+1) values
  have htail : ∀ bv' cv' : Int,
      stepFnIter 31
        (kSt σ (kHeapM ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
          ((n : Nat) : Int) bv' cv' ((m : Nat) : Int) false) 19)
        kHeadCfg ch
        = .ok (.retV (.bool (decide
              (((m + 1 : Nat) : Int) < ((n : Nat) : Int)))) kCmpIfK,
            kSt σ (kHeapM ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
              ((n : Nat) : Int) bv' cv' ((m + 1 : Nat) : Int) false) 19,
            ch) := by
    intro bv' cv'
    have hdisp := kd_dispB_raw σ ((n : Nat) : Int) sv n l lp
      ((n : Nat) : Int) ((n : Nat) : Int) bv' cv' ((m : Nat) : Int) ch
    rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
      inorm_nat_of_lt (by omega), inorm_nat_of_lt (by omega)] at hdisp
    have hlenap : applyStrictOp
        (kSt σ (kHeapM ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
          ((n : Nat) : Int) bv' cv' ((m + 1 : Nat) : Int) false) 19)
        (.lengthOf (some (.slice (.int .int64)))) [kSliceS n]
        = .ok (.int ((n : Nat) : Int) .int,
            kSt σ (kHeapM ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
              ((n : Nat) : Int) bv' cv' ((m + 1 : Nat) : Int) false) 19) :=
      applyStrictOp_len_slice (Nat.le_refl _)
    have hlen := stepFnIter_one (ch := ch)
      (stepFn_strict_apply (done := []) (env := kEnvC)
        (k := .strictK .lessCmp [.int ((m + 1 : Nat) : Int) .int] [] kEnvC
          kCmpIfK)
        hlenap)
    have hcmp := stepFnIter_one (ch := ch)
      (stepFn_strict_apply
        (done := [.int ((m + 1 : Nat) : Int) .int]) (env := kEnvC)
        (k := kCmpIfK) (v := .int ((n : Nat) : Int) .int)
        (applyStrictOp_lessCmp_int
          (σ := kSt σ (kHeapM ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
            ((n : Nat) : Int) bv' cv' ((m + 1 : Nat) : Int) false) 19)
          (a := ((m + 1 : Nat) : Int)) (b := ((n : Nat) : Int))
          (k := .int) (k' := .int)))
    show stepFnIter (29 + 1 + 1) _ _ _ = _
    exact stepFnIter_chain (stepFnIter_chain hdisp hlen) hcmp
  -- the best-update phase, at the already-advanced cur
  have hbest : ∀ ch' : Choices, ∃ k₂ : Nat, k₂ ≤ 17 ∧
      stepFnIter k₂
        (kSt σ (kHeapM ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
          ((n : Nat) : Int) (kadBest l m) (kadCur l (m + 1))
          ((m : Nat) : Int) false) 19)
        (.retV (.bool (decide (kadBest l m < kadCur l (m + 1)))) kBestIfK)
        ch'
        = .ok (kHeadCfg,
            kSt σ (kHeapM ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
              ((n : Nat) : Int) (kadBest l (m + 1)) (kadCur l (m + 1))
              ((m : Nat) : Int) false) 19, ch') := by
    intro ch'
    by_cases hbt : kadBest l m < kadCur l (m + 1)
    · rw [show (decide (kadBest l m < kadCur l (m + 1))) = true from
        decide_eq_true hbt]
      refine ⟨17, by omega, ?_⟩
      rw [show kadBest l (m + 1) = kadCur l (m + 1) from by
        rw [kadBest_step l m hm1]; omega]
      have h := kd_b4T_raw σ ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
        ((n : Nat) : Int) (kadBest l m) (kadCur l (m + 1))
        ((m : Nat) : Int) ch'
      rw [inorm64_of_range hcv1r.1 hcv1r.2] at h
      exact h
    · rw [show (decide (kadBest l m < kadCur l (m + 1))) = false from
        decide_eq_false hbt]
      refine ⟨5, by omega, ?_⟩
      rw [show kadBest l (m + 1) = kadBest l m from by
        rw [kadBest_step l m hm1]; omega]
      exact kd_b4F_raw σ ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
        ((n : Nat) : Int) (kadBest l m) (kadCur l (m + 1))
        ((m : Nat) : Int) ch'
  by_cases hlt : kadCur l m < 0
  · -- RESTART: cur = s[i]
    rw [show (decide (kadCur l m < 0)) = true from decide_eq_true hlt] at hb1
    have hb2 := kd_b2T_raw σ ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
      ((n : Nat) : Int) (kadBest l m) (kadCur l m) ((m : Nat) : Int) ch
    have hread := stepFn_strict_apply (done := [kSliceS n]) (env := kEnvE)
      (k := kCurSetRhsK) (ch := ch)
      (applyStrictOp_indexGet_slice (ik := .int)
        (lookup_kM σ ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
          ((n : Nat) : Int) (kadBest l m) (kadCur l m) ((m : Nat) : Int)
          false 19)
        (Nat.le_refl n) hm hget)
    have hb3 := kd_b3T_raw σ ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
      ((n : Nat) : Int) (kadBest l m) (kadCur l m) ((m : Nat) : Int)
      (l.getD m 0) ch
    rw [inorm64_of_range (by omega) (by omega)] at hb3
    have hpre := stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain hb1 hb2) (stepFnIter_one hread))
      hb3
    rw [show l.getD m 0 = kadCur l (m + 1) from by
      rw [kadCur_step l m hm1, if_pos hlt]] at hpre
    obtain ⟨k₂, hk₂, hb4⟩ := hbest ch
    exact ⟨11 + 12 + 1 + 12 + (k₂ + 31), by omega,
      stepFnIter_chain hpre (stepFnIter_chain hb4 (htail _ _))⟩
  · -- EXTEND: cur = cur + s[i]
    rw [show (decide (kadCur l m < 0)) = false from decide_eq_false hlt]
      at hb1
    have hb2 := kd_b2F_raw σ ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
      ((n : Nat) : Int) (kadBest l m) (kadCur l m) ((m : Nat) : Int) ch
    have hread := stepFn_strict_apply (done := [kSliceS n]) (env := kEnvE)
      (k := .strictK .add [.int (kadCur l m) .int64] [] kEnvE kCurSetRhsK)
      (ch := ch)
      (applyStrictOp_indexGet_slice (ik := .int)
        (lookup_kM σ ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
          ((n : Nat) : Int) (kadBest l m) (kadCur l m) ((m : Nat) : Int)
          false 19)
        (Nat.le_refl n) hm hget)
    have hb3 := kd_b3F_raw σ ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
      ((n : Nat) : Int) (kadBest l m) (kadCur l m) ((m : Nat) : Int)
      (l.getD m 0) ch
    have hsum : kadCur l m + l.getD m 0 = kadCur l (m + 1) := by
      rw [kadCur_step l m hm1, if_neg hlt]
    rw [hsum, inorm64_of_range hcv1r.1 hcv1r.2,
      inorm64_of_range hcv1r.1 hcv1r.2] at hb3
    have hpre := stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain hb1 hb2) (stepFnIter_one hread))
      hb3
    obtain ⟨k₂, hk₂, hb4⟩ := hbest ch
    exact ⟨11 + 15 + 1 + 13 + (k₂ + 31), by omega,
      stepFnIter_chain hpre (stepFnIter_chain hb4 (htail _ _))⟩

/-- The kadane loop, iterated to the driver terminal. -/
theorem kd_loop (σ : ExecState) (n : Nat) (sv : Int) (l lp : List Int)
    (hln : l.length = n)
    (hlr : ∀ v ∈ l, -(2 ^ 59 + 8) ≤ v ∧ v ≤ 2 ^ 59 + 8)
    (hlp : lp.length = 8)
    (hlpr : ∀ v ∈ lp, -(2 ^ 63) ≤ v ∧ v < 2 ^ 63)
    (hcap : n ≤ 8) :
    ∀ μ m : Nat, 1 ≤ m → m ≤ n → μ = n - m → ∀ ch : Choices,
    ∃ k : Nat, k ≤ 88 * μ + 50 ∧
      stepFnIter k
        (kSt σ (kHeapM ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
          ((n : Nat) : Int) (kadBest l m) (kadCur l m) ((m : Nat) : Int)
          false) 19)
        (.retV (.bool (decide (((m : Nat) : Int) < ((n : Nat) : Int))))
          kCmpIfK) ch
        = .ok (.next .stop,
            kSt σ (kHeapEnd ((n : Nat) : Int) sv n l lp ((n : Nat) : Int)
              ((n : Nat) : Int) (kadBest l n) (kadCur l n)
              ((n : Nat) : Int)) 19, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hm1 hmn hμ ch
    rcases Nat.lt_or_ge m n with hlt | hge
    · rw [show (decide (((m : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      obtain ⟨k₀, hk₀, hstep⟩ :=
        kd_iter σ n sv l lp m hln hlr hcap hm1 hlt ch
      obtain ⟨k, hk, hrun⟩ := ih (n - (m + 1)) (by omega) (m + 1)
        (by omega) (by omega) rfl ch
      exact ⟨k₀ + k, by omega, stepFnIter_chain hstep hrun⟩
    · have hmn' : m = n := by omega
      subst hmn'
      rw [show (decide (((m : Nat) : Int) < ((m : Nat) : Int))) = false from
        decide_eq_false (by omega)]
      have hX1 := kd_X1_raw σ ((m : Nat) : Int) sv m l lp ((m : Nat) : Int)
        ((m : Nat) : Int) (kadBest l m) (kadCur l m) ((m : Nat) : Int) ch
      have hstore : storeTarget
          (kSt σ (kHeapPreStore ((m : Nat) : Int) sv m l lp
            ((m : Nat) : Int) ((m : Nat) : Int) (kadBest l m) (kadCur l m)
            ((m : Nat) : Int)) 19)
          kdRes0Ref (.array ⟨lp.map (fun v => .int v .int64)⟩)
          = .ok (kSt σ (kHeapStored ((m : Nat) : Int) sv m l lp
              ((m : Nat) : Int) ((m : Nat) : Int) (kadBest l m)
              (kadCur l m) ((m : Nat) : Int)) 19) :=
        storeTarget_addr
          (lookup_kPreStore σ ((m : Nat) : Int) sv m l lp ((m : Nat) : Int)
            ((m : Nat) : Int) (kadBest l m) (kadCur l m) ((m : Nat) : Int)
            19)
          (normalizeValueForTy_arr_i64 hlp hlpr)
      have hX2 := kd_X2_raw σ ((m : Nat) : Int) sv m l lp ((m : Nat) : Int)
        ((m : Nat) : Int) (kadBest l m) (kadCur l m) ((m : Nat) : Int) ch
      exact ⟨34 + 1 + 15, by omega,
        stepFnIter_chain (stepFnIter_chain hX1
          (stepFnIter_one (stepFn_store_step hstore))) hX2⟩

/-! ## The run, end to end -/

/-- **The harness run, PROGRAM-generic**: within `227·n + 220` steps
the harness reaches the driver terminal with the zero-padded family in
`$res0` and `maxSubarraySum` of the family in `$res1`. Both guard
branches (`n = 0` through kadane's empty-slice guard, `n ≥ 1` through
the scan loop) land in the same readout. -/
theorem kd_runs (σ : ExecState) (n : Nat) (seed : Int)
    (hcap : n ≤ 8) (hs1 : -(2 ^ 59) ≤ seed) (hs2 : seed ≤ 2 ^ 59)
    (henter : ∀ (l lp : List Int) (siv civ : Int),
      enterFrame (kSt σ (kHeapCall ((n : Nat) : Int) seed n l lp siv civ)
          13) ⟨"kadane"⟩ [kSliceS n]
        = .ok (kadaneFunc, kEnvB, [.base ⟨14⟩],
            kSt σ (kHeapKFrame ((n : Nat) : Int) seed n l lp siv civ) 15))
    (ch : Choices) :
    ∃ (k : Nat) (σf : ExecState), k ≤ 227 * n + 220 ∧
      stepFnIter k (kSt σ (kHeap0 ((n : Nat) : Int) seed) 4) kdHC0 ch
        = .ok (.next .stop, σf, ch)
      ∧ loadMany σf [.base ⟨2⟩, .base ⟨3⟩]
          = .ok [.array ⟨(kadPad 8 n seed).map (fun v => .int v .int64)⟩,
                 .int (maxSubarraySum (kadFamily n seed)) .int64] := by
  have hlpr : ∀ v ∈ kadPad 8 n seed, -(2 ^ 63) ≤ v ∧ v < 2 ^ 63 := by
    intro v hv
    have := kadPad_range (by omega) (by omega) hs1 hs2 v hv
    omega
  -- entry
  have hE1 := kd_E1_raw σ ((n : Nat) : Int) seed ch
  have hmk := stepFnIter_one (ch := ch)
    (stepFn_makeSlice_i64_step (env := kEnvC8) (k := kdTail0)
      (kd_make_apply σ ((n : Nat) : Int) seed n ch))
  have hE2 := kd_E2_raw σ ((n : Nat) : Int) seed n ch
  rw [show (List.replicate n (0 : Int)) = kadPad n 0 seed from
    (kadPad_zero n seed).symm] at hE2
  have hA0 := kd_su_A0_raw σ ((n : Nat) : Int) seed n (kadPad n 0 seed) 0 ch
  obtain ⟨k1, hk1, hsu⟩ := kd_su_loop σ n seed hcap hs1 hs2 n 0
    (by omega) ch
  rw [show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hsu
  have hentry := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hE1 hmk) hE2) hA0) hsu
  -- the copy loop
  have hcA0 := kd_cp_A0_raw σ ((n : Nat) : Int) seed n (kadFamily n seed)
    kZeros8 ((n : Nat) : Int) 0 ch
  obtain ⟨k2, hk2, hcp⟩ := kd_cp_loop σ n seed hcap hs1 hs2 n 0
    (by omega) ch
  rw [show kadPad 8 0 seed = kZeros8 from kadPad_zero 8 seed,
    show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hcp
  have hthru := stepFnIter_chain (stepFnIter_chain hentry hcA0) hcp
  -- the call and the guard
  have hent := stepFnIter_one (ch := ch)
    (stepFn_call_enter (plans := kShapes) (env := kCallEnv)
      (k := kdAfterCall) (vals := []) (v := kSliceS n)
      (henter (kadFamily n seed) (kadPad 8 n seed) ((n : Nat) : Int)
        ((n : Nat) : Int)))
  have hg1 := kd_g1_raw σ ((n : Nat) : Int) seed n (kadFamily n seed)
    (kadPad 8 n seed) ((n : Nat) : Int) ((n : Nat) : Int) ch
  have hlenap : applyStrictOp
      (kSt σ (kHeapKFrame ((n : Nat) : Int) seed n (kadFamily n seed)
        (kadPad 8 n seed) ((n : Nat) : Int) ((n : Nat) : Int)) 15)
      (.lengthOf (some (.slice (.int .int64)))) [kSliceS n]
      = .ok (.int ((n : Nat) : Int) .int,
          kSt σ (kHeapKFrame ((n : Nat) : Int) seed n (kadFamily n seed)
            (kadPad 8 n seed) ((n : Nat) : Int) ((n : Nat) : Int)) 15) :=
    applyStrictOp_len_slice (Nat.le_refl _)
  have hlen := stepFnIter_one (ch := ch)
    (stepFn_strict_apply (done := []) (env := kEnvG) (k := kGEqK) hlenap)
  have hg2 := kd_g2_raw σ ((n : Nat) : Int) seed n (kadFamily n seed)
    (kadPad 8 n seed) ((n : Nat) : Int) ((n : Nat) : Int)
    ((n : Nat) : Int) ch
  have hto_guard := stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain hthru hent) hg1) hlen) hg2
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · -- the empty-slice guard path
    subst hn0
    rw [show ((((0 : Nat) : Int)) == (0 : Int)) = true from by decide]
      at hto_guard
    have hgT := kd_gT_raw σ ((0 : Nat) : Int) seed 0 (kadFamily 0 seed)
      (kadPad 8 0 seed) ((0 : Nat) : Int) ((0 : Nat) : Int) ch
    have hstore : storeTarget
        (kSt σ (kHeapKFrame ((0 : Nat) : Int) seed 0 (kadFamily 0 seed)
          (kadPad 8 0 seed) ((0 : Nat) : Int) ((0 : Nat) : Int)) 15)
        kdRes0Ref
        (.array ⟨(kadPad 8 0 seed).map (fun v => .int v .int64)⟩)
        = .ok (kSt σ (kHeapGEnd ((0 : Nat) : Int) seed 0 (kadFamily 0 seed)
            (kadPad 8 0 seed) ((0 : Nat) : Int) ((0 : Nat) : Int)) 15) :=
      storeTarget_addr
        (lookup_kGFrame σ ((0 : Nat) : Int) seed 0 (kadFamily 0 seed)
          (kadPad 8 0 seed) ((0 : Nat) : Int) ((0 : Nat) : Int) 15)
        (normalizeValueForTy_arr_i64 (kadPad_length (by omega)) hlpr)
    have hgX := kd_gX_raw σ ((0 : Nat) : Int) seed 0 (kadFamily 0 seed)
      (kadPad 8 0 seed) ((0 : Nat) : Int) ((0 : Nat) : Int) ch
    refine ⟨10 + 1 + 42 + 25 + k1 + 25 + k2 + 1 + 6 + 1 + 3
        + (31 + 1 + 15), _, by omega,
      stepFnIter_chain hto_guard
        (stepFnIter_chain
          (stepFnIter_chain hgT (stepFnIter_one (stepFn_store_step hstore)))
          hgX), ?_⟩
    rfl
  · -- the scan path
    rw [show ((((n : Nat) : Int)) == (0 : Int)) = false from by
      simp only [beq_eq_false_iff_ne, ne_eq, Int.natCast_eq_zero]
      omega] at hto_guard
    have hlenL : (kadFamily n seed).length = n := kadFamily_length n seed
    have hlrL : ∀ v ∈ kadFamily n seed,
        -(2 ^ 59 + 8) ≤ v ∧ v ≤ 2 ^ 59 + 8 := by
      intro v hv
      have := kadFamily_range hcap hs1 hs2 v hv
      omega
    have hw0 := hlrL _ (getD_mem_int (show 0 < (kadFamily n seed).length
      by omega))
    have hget0 : (⟨(kadFamily n seed).map (fun v => .int v .int64)⟩ :
        Array GoValue)[0 + 0]?
        = some (.int ((kadFamily n seed).getD 0 0) .int64) := by
      rw [Nat.zero_add, getElem?_mapI _ _ (by omega)]
    -- the prologue
    have hp1 := kd_p1_raw σ ((n : Nat) : Int) seed n (kadFamily n seed)
      (kadPad 8 n seed) ((n : Nat) : Int) ((n : Nat) : Int) ch
    have hread1 := stepFn_strict_apply (done := [kSliceS n])
      (env := kEnvG1) (k := kBestRhsK) (ch := ch)
      (applyStrictOp_indexGet_slice (ik := .int) (i := 0)
        (lookup_kP1 σ ((n : Nat) : Int) seed n (kadFamily n seed)
          (kadPad 8 n seed) ((n : Nat) : Int) ((n : Nat) : Int) 16)
        (Nat.le_refl n) (by omega) hget0)
    have hp2 := kd_p2_raw σ ((n : Nat) : Int) seed n (kadFamily n seed)
      (kadPad 8 n seed) ((n : Nat) : Int) ((n : Nat) : Int)
      ((kadFamily n seed).getD 0 0) ch
    rw [inorm64_of_range (by omega) (by omega)] at hp2
    have hread2 := stepFn_strict_apply (done := [kSliceS n])
      (env := kEnvBC) (k := kCurRhsK) (ch := ch)
      (applyStrictOp_indexGet_slice (ik := .int) (i := 0)
        (lookup_kKB σ ((n : Nat) : Int) seed n (kadFamily n seed)
          (kadPad 8 n seed) ((n : Nat) : Int) ((n : Nat) : Int)
          ((kadFamily n seed).getD 0 0) 17)
        (Nat.le_refl n) (by omega) hget0)
    have hp3 := kd_p3_raw σ ((n : Nat) : Int) seed n (kadFamily n seed)
      (kadPad 8 n seed) ((n : Nat) : Int) ((n : Nat) : Int)
      ((kadFamily n seed).getD 0 0) ((kadFamily n seed).getD 0 0) ch
    rw [inorm64_of_range (by omega) (by omega)] at hp3
    -- the first dispatch
    have hdA := kd_dispA_raw σ ((n : Nat) : Int) seed n (kadFamily n seed)
      (kadPad 8 n seed) ((n : Nat) : Int) ((n : Nat) : Int)
      ((kadFamily n seed).getD 0 0) ((kadFamily n seed).getD 0 0) 1 ch
    have hlenap2 : applyStrictOp
        (kSt σ (kHeapM ((n : Nat) : Int) seed n (kadFamily n seed)
          (kadPad 8 n seed) ((n : Nat) : Int) ((n : Nat) : Int)
          ((kadFamily n seed).getD 0 0) ((kadFamily n seed).getD 0 0) 1
          false) 19)
        (.lengthOf (some (.slice (.int .int64)))) [kSliceS n]
        = .ok (.int ((n : Nat) : Int) .int,
            kSt σ (kHeapM ((n : Nat) : Int) seed n (kadFamily n seed)
              (kadPad 8 n seed) ((n : Nat) : Int) ((n : Nat) : Int)
              ((kadFamily n seed).getD 0 0) ((kadFamily n seed).getD 0 0) 1
              false) 19) :=
      applyStrictOp_len_slice (Nat.le_refl _)
    have hlen2 := stepFnIter_one (ch := ch)
      (stepFn_strict_apply (done := []) (env := kEnvC)
        (k := .strictK .lessCmp [.int (1 : Int) .int] [] kEnvC kCmpIfK)
        hlenap2)
    have hcmp2 := stepFnIter_one (ch := ch)
      (stepFn_strict_apply (done := [.int (1 : Int) .int]) (env := kEnvC)
        (k := kCmpIfK) (v := .int ((n : Nat) : Int) .int)
        (applyStrictOp_lessCmp_int
          (σ := kSt σ (kHeapM ((n : Nat) : Int) seed n (kadFamily n seed)
            (kadPad 8 n seed) ((n : Nat) : Int) ((n : Nat) : Int)
            ((kadFamily n seed).getD 0 0) ((kadFamily n seed).getD 0 0) 1
            false) 19)
          (a := (1 : Int)) (b := ((n : Nat) : Int)) (k := .int)
          (k' := .int)))
    -- the scan loop
    obtain ⟨k3, hk3, hml⟩ := kd_loop σ n seed (kadFamily n seed)
      (kadPad 8 n seed) hlenL hlrL (kadPad_length (by omega)) hlpr hcap
      (n - 1) 1 (by omega) (by omega) rfl ch
    rw [show kadBest (kadFamily n seed) 1 = (kadFamily n seed).getD 0 0
        from rfl,
      show kadCur (kadFamily n seed) 1 = (kadFamily n seed).getD 0 0
        from rfl,
      show (((1 : Nat) : Int)) = (1 : Int) from rfl] at hml
    refine ⟨10 + 1 + 42 + 25 + k1 + 25 + k2 + 1 + 6 + 1 + 3
        + (14 + 1 + 16 + 1 + 33 + 25 + 1 + 1 + k3), _, by omega,
      stepFnIter_chain hto_guard
        (stepFnIter_chain
          (stepFnIter_chain
            (stepFnIter_chain
              (stepFnIter_chain
                (stepFnIter_chain
                  (stepFnIter_chain
                    (stepFnIter_chain
                      (stepFnIter_chain hp1 (stepFnIter_one hread1))
                      hp2)
                    (stepFnIter_one hread2))
                  hp3)
                hdA)
              hlen2)
            hcmp2)
          hml), ?_⟩
    -- the readout
    have hB : (0 : Int) ≤ 2 ^ 59 + 8 := by omega
    have hbnd := kad_bounds (kadFamily n seed) (2 ^ 59 + 8) hB hlrL n
      (by omega) (by omega)
    have hnB : ((n : Nat) : Int) * (2 ^ 59 + 8) ≤ 8 * (2 ^ 59 + 8) := by
      apply Int.mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast hcap
    have hbr : -(2 ^ 63) ≤ kadBest (kadFamily n seed) n
        ∧ kadBest (kadFamily n seed) n < 2 ^ 63 := by
      obtain ⟨-, ⟨h1, h2⟩⟩ := hbnd
      omega
    have hspec := kadBest_spec (l := kadFamily n seed)
      (by rw [hlenL]; omega)
    rw [hlenL] at hspec
    have hr : loadMany
        (kSt σ (kHeapEnd ((n : Nat) : Int) seed n (kadFamily n seed)
          (kadPad 8 n seed) ((n : Nat) : Int) ((n : Nat) : Int)
          (kadBest (kadFamily n seed) n) (kadCur (kadFamily n seed) n)
          ((n : Nat) : Int)) 19)
        [.base ⟨2⟩, .base ⟨3⟩]
        = .ok [.array ⟨(kadPad 8 n seed).map (fun v => .int v .int64)⟩,
               .int (IntKind.normalize .int64 (IntKind.normalize .int64
                 (IntKind.normalize .int64
                   (kadBest (kadFamily n seed) n)))) .int64] := rfl
    rw [inorm64_of_range hbr.1 hbr.2, inorm64_of_range hbr.1 hbr.2,
      inorm64_of_range hbr.1 hbr.2] at hr
    rw [← hspec]
    exact hr

/-! ## The user-facing statements -/

/-- **THE HEADLINE (§11 harness form, S3 RELATIONAL, the wave's only
SIGNED example)**: for every `n ≤ 8` and every `seed` in the no-wrap
window `-2⁵⁹ ≤ seed ≤ 2⁵⁹`, running the Go harness
`kadane_harness_r(n, seed)` through the machine's native function
entry — empty-heap state, both int64 arguments at the call boundary —
completes normally past one fuel bound, at every
nondeterminism-choice stream, and returns TWO values: a length-`n`
value list `vals` as the fixed-cap `[8]int64` array the Go returns,
and `maxSubarraySum vals` — the MATHEMATICAL maximum over all
non-empty contiguous segments' sums of the returned data, `0` for the
empty list.

Honesty clauses, all recorded rather than hidden:

* **The claim is MATHEMATICS, not a restatement of the scan.**
  `maxSubarraySum` enumerates every non-empty contiguous segment
  (`segments`) and takes the greatest sum (`List.max?`); the theorem
  is therefore the correctness of Kadane's running-best scan against
  that maximum. The scan-shaped functions `kadCur`/`kadBest` are
  proof-side only, bridged by `kadCur_eq_maxEnd`/`kadBest_eq_maxSub`
  (via the snoc equation `maxSub_snoc`), and do not appear in this
  statement's closure.
* **`n = 0` is the SOURCE'S definition.** The Go guards the `s[0]`
  read and returns `0` on the empty slice; `maxSubarraySum [] = 0`
  states exactly that, and the theorem covers the `n = 0` run through
  the guard path (corpus row `harness-r-empty` pins it
  differentially).
* **All-negative inputs return the largest single element, never 0** —
  a property of the mathematics (every non-empty segment sum is
  maximized at some single-element segment when all elements are
  negative), inherited, not axiomatized.
* **The domain window `-2⁵⁹ ≤ seed ≤ 2⁵⁹` is a no-wrap bound**: family
  values are `±(seed + i)` with `i < 8` and the scan's `cur`/`best`
  are sums of at most 8 of them (`kad_bounds`), so no int64 operation
  wraps on this domain. Outside it the int64 additions can wrap and
  the answer is NOT the mathematical maximum; the corpus pins that
  region differentially. Attribution: the program's own arithmetic
  (machine-integer honesty, FD-E3).
* **The cap `n ≤ 8` is a toy bound.** Go's pass-by-value fragment
  cannot return unbounded data, so the harness returns
  `[kadaneCapN]int64` with `kadaneCapN = 8` (visible in the corpus
  Go); the copy loop plus zero-padding exist ONLY so the scanned
  values can cross the observation boundary.
* **`∃ vals` is still family-determined.** The witness is
  `kadFamily n seed` (`seed + i`, odd indices negated); the statement
  merely avoids SAYING so. Making the input genuine ∀-data needs the
  ghost rung-1 annotation, which is designed and not built.
* **The fuel bound `N = 227·n + 220` is a BOUND, not a measurement**:
  it is the branch-uniform worst case (odd setup iterations cost 86
  against even 66; the scan's restart/extend and best-update branches
  cost up to 88). The MEASURED step counts at `seed = 5` are
  `213, 427, 642, 845, 1060, 1263, 1478, 1681, 1896` for
  `n = 0 … 8` — input-dependent through the branch structure, so no
  affine law is quoted.
* **`∀ ch` is vacuous here and stated anyway.** The subject consumes
  no nondeterminism choice; the quantifier records that rather than
  hiding a `Choices` argument.
* **Machine idealization** as in the other entries: entry from an
  empty heap, an unbounded heap, allocation always succeeds. -/
theorem kadane_ok (n : Nat) (seed : Int) (hcap : n ≤ 8)
    (hs1 : -(2 ^ 59) ≤ seed) (hs2 : seed ≤ 2 ^ 59) :
    ∃ vals : List Int, vals.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel kadaneLowered.typeDefs.toList
            kadaneLowered.funcs kadaneHarnessRFunc
            #[.int (n : Int) .int64, .int seed .int64]
            kadaneLowered.methods ch
          = .ok { values := #[kadArr8 vals,
                              .int (maxSubarraySum vals) .int64] } := by
  refine ⟨kadFamily n seed, kadFamily_length n seed, 227 * n + 220,
    fun fuel hfuel ch => ?_⟩
  obtain ⟨k, σf, hk, hrun, hread⟩ :=
    kd_runs kdProg n seed hcap hs1 hs2
      (fun l lp siv civ =>
        kd_enterFrame_fact n ((n : Nat) : Int) seed l lp siv civ) ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  have hst : kdHSeed ((n : Nat) : Int) seed
      = kSt kdProg (kHeap0 ((n : Nat) : Int) seed) 4 := rfl
  rw [kdH_entry_eq, inorm64_nat_of_lt (by omega),
    inorm64_of_range (by omega) (by omega), hst, hfold,
    runConfig_next_stop]
  simp only [bind, Except.bind, pure, Except.pure, hread]
  rw [kadArr8, kadPad_full hcap]

/-- **The D1 run-conditioned twin**: any successful completion of the
harness entry, at any fuel and any choice stream, returns exactly those
two values — derived from `kadane_ok` through the shared
`harness_readout_of_total` bridge; nothing is re-proven. -/
theorem kadane_readout (n : Nat) (seed : Int) (hcap : n ≤ 8)
    (hs1 : -(2 ^ 59) ≤ seed) (hs2 : seed ≤ 2 ^ 59) :
    ∃ vals : List Int, vals.length = n ∧
      ∀ (fuel : Nat) (ch : Choices) (r : Result),
        runFunctionWithContextM fuel kadaneLowered.typeDefs.toList
            kadaneLowered.funcs kadaneHarnessRFunc
            #[.int (n : Int) .int64, .int seed .int64]
            kadaneLowered.methods ch
          = .ok r →
        r = { values := #[kadArr8 vals,
                          .int (maxSubarraySum vals) .int64] } := by
  obtain ⟨vals, hlen, htot⟩ := kadane_ok n seed hcap hs1 hs2
  exact ⟨vals, hlen, harness_readout_of_total htot⟩

end GoLean.Examples.Kadane
