import GoLeanProofs.Examples.InsertionSortProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Laws.StmtOps

/-!
# Verified example: in-place insertion sort — NESTED loops
(verified-examples slice 2c, 2026-08-13)

The nested-loop exemplar of the §9 memory-input form (design note
`docs/2026-08-12_example-spec-form.md` §9): the Go program is the
canonical corpus source `Corpus/coverage/exec/examples/isort/main.go`
(differentially green against `go run`, 8 oracle rows incl. duplicates
and already/reverse-sorted inputs); `isortLowered` is its pinned
frontend lowering (`scripts/check-golden`).

**Harness-ruling status (2026-08-13, design note §11 — RESTATED,
COMPLETE).** `isort_ok` is now the §11 three-phase harness headline
over `runFunctionWithContextM` (`isort_harness(n, seed)`: setup builds
the wrapped multiplicative family `s[i] = seed*(i+1)`; the call under
test `insertionSort(s)`; the TEST PHASE — sortedness scan plus the
count-based permutation check against the rebuilt family, IN GO,
inside the verified footprint — folds into the returned verdict
`ok ∈ {0,1}`; headline: verdict = 1, `isort_readout` the D1 twin).
The former memory-quantified pair is RENAMED to
`isort_framed`/`isort_framed_readout` (the gcd/minmax/binsearch/
reverse precedent) and kept green as the proof-side supporting layer —
it remains the strongest ∀xs claim shipped. Fuel bound of the
headline: `N = (92·n+160)·n + (110·n+220)·n + 285·n + 505` (quadratic:
the count loops are O(n²)).

**Harness address layout (probe-verified against the full n=4 seed=3
trace, `.tmp/his-trace1.txt`, and re-checked by every `rfl` segment)**:
0 = `n`, 1 = `seed`, 2 = the harness `$res0` (the VERDICT cell),
3 = `$c4`, 4 = the `s` BACKING, 5 = `s`, 6/7 = the setup
`i`/`$forFirst`; the subject frame 8 = the `s` param, 9 = the subject
`i`, 10 = the outer `$forFirst`, per-pass `j`/`$forFirst` pairs from
11 (2 cells/pass); then the test phase: 11+2(n-1)… in TRUE addresses —
canonically (all subject passes rebased into the frame): 11 = `ok`,
12/13 = the scan `i`/flag, 14 = `$c5`, 15 = the `t` BACKING, 16 = `t`,
17/18 = the rebuild `i`/flag, 19/20 = the count `i`/flag, and the
count pass cells TIGHT at 21 = `cs`, 22 = `ct`, 23 = `j`, 24 = flag
(4 cells/pass, retired by the second rebase layer).

**How the restatement runs (the recipe as executed, deviations
recorded)**: the subject phase is re-derived concretely at the harness
placement under the harness continuation (Reverse's route (b); the
canonical segments' step counts carried over VERBATIM — same
statements, same machine paths), with the pass frame-rebase layer
re-instantiated at threshold 11 (`ρ11`/`rebaseSim11`, retire 2). The
remainder (scan → rebuild → count) is proven as ONE canonical run from
the post-subject 11-cell state and transferred to the true
(subject-garbage-laden) placement in a single `transfer_seg11`
application at the end — the scan and rebuild allocate only
per-phase, so their segments are address-concrete; the count loops
carry the SECOND frame-rebase layer at threshold 21
(`ρ21`/`rebaseSim21`, retire 4/pass), exactly as the pickup plan
predicted. One deviation from the plan's letter: the scan loop's exit
counter is existential (`mf`) rather than pinned to `n` — the scan
starts at `i = 1`, so at `n = 0` it exits at `1 ≠ n`; the parked value
is inert and every downstream state carries it as a parameter
(`sciv`). The rebuild loop re-instantiates the setup induction at the
`t` placement (the segments could not be shared across placements —
`rfl` segments need address-concrete envs — so they are re-derived;
flagged in the worker report as the expected cost). The count inner
loop's accumulator invariant bridges to `List.count` via the in-module
`cntSpec` and closes by `sortSpec_count`.

The support corollaries (`sortSpec_sorted`, `sortSpec_count`,
`sortSpec_length`) make the "sorted permutation" reading of the
Go-computed verdict a theorem, not a naming convention.

**The nested-loop composition (route of record, with one machine-forced
deviation from the arc design).** The design called for two plain
nested strong inductions on the direct machine-step route (the
fuel-measure RULE is not needed on this route — that sugar gap remains
the WP route's, none of which is consumed here). Both inductions are
below, exactly as designed: the INNER induction (`innerLoop`, measure
`j` descending, invariant `bubbleState`) and the OUTER induction
(`isortLoop`, measure `n - (m+1)`, invariant `sortPrefix`). The
deviation: **the outer induction composes its per-pass segments through
the executable frame theorem** (`stepFnIter_sim` at a per-pass shift
renaming `ρsh (2m)`, plus a frame-REBASE step) rather than by literal
state reuse, because the machine allocates a FRESH `j`/`$forFirst` cell
pair on every outer pass (the inner `for`'s declarations re-enter their
block each pass; `nextAddr` grows by 2 per pass and the dead cells stay
in the heap — probe-verified). Reverse-style fixed-address segments
therefore cannot describe the outer loop head at a single placement;
instead each pass is proven ONCE at a tight 6-cell canonical placement
and transferred to the true (garbage-laden) placement by the frame
theorem, with the retired `j`/`$forFirst` cells REBASED into the frame
between passes (`rebaseSim`). The garbage cells are semantically inert;
the frame theorem is precisely the tool that says so. Nothing is
re-run at any framed placement.

The `&&` lowering shape (probe finding, load-bearing for §9d honesty):
`Expr.and` evaluates the left conjunct into an `.andK` continuation;
`false` short-circuits — delivering `.bool false` straight to the `if`
continuation WITHOUT evaluating the right conjunct, so at `j = 0` the
`s[j-1]` read never happens (Go's laziness, exactly). The proof's inner
exit at `j = 0` goes through that short-circuit arm.

Statement deltas against the arc-design block: NONE beyond the deltas
already in the design (`hlen : xs.length < 2 ^ 63` — Go's own `int`
domain: with completion in the statement, the driver's `len` literal
wraps negative past `2^63` and the slice-expression bounds check
panics, so the claim as drafted would be false there).

Scope honesty (the charter's two-questions separation): usability
evidence only — never machine-hardening evidence.
-/

namespace GoLean.Examples.InsertionSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-! ## The program-side statement vocabulary -/

/-- The swap block: `{ s[j-1], s[j] = s[j], s[j-1] }`. -/
abbrev isortSwapBlock : Stmt :=
  .block #[]
    #[.seqn
        #[.assignMany
            #[.addr (.indexAddr (.var "s")
                (.sub (.var "j") (.intLit 1 .int))),
              .addr (.indexAddr (.var "s") (.var "j"))]
            #[.indexGet (.var "s") (.var "j"),
              .indexGet (.var "s") (.sub (.var "j") (.intLit 1 .int))]]]

/-- The inner `for`'s condition: Go's SHORT-CIRCUIT
`j > 0 && s[j-1] > s[j]`. -/
abbrev innerCond : Expr :=
  .and (.greaterCmp (.var "j") (.intLit 0 .int))
    (.greaterCmp
      (.indexGet (.var "s") (.sub (.var "j") (.intLit 1 .int)))
      (.indexGet (.var "s") (.var "j")))

/-- The inner `for`-desugar body (its own `$forFirst`, SHADOWING the
outer one — the env carries both at different scopes). -/
abbrev innerWhileBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "j") (.sub (.var "j") (.intLit 1 .int))),
      .seqn #[],
      .ifThenElse innerCond (.seqn #[]) .breakStmt,
      isortSwapBlock]

/-- The inner `for` statement as lowered (declaration block for `j`,
then the `$forFirst` block around the while). -/
abbrev innerForBlock : Stmt :=
  .block #[]
    #[.block #[]
        #[.seqn
            #[.initialization { id := "j", typ := .int .int },
              .assign (.var "j") (.var "i")],
          .block #[]
            #[.initialization { id := "$forFirst", typ := .bool },
              .assign (.var "$forFirst") (.boolLit true),
              .while (.boolLit true) innerWhileBody]]]

/-- The outer `for`-desugar body: dispatch, exit test `i < len(s)`,
then the whole inner `for`. -/
abbrev outerWhileBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .int))),
      .seqn #[],
      .ifThenElse
        (.lessCmp (.var "i")
          (.length (.var "s") (some (.slice (.int .uint64)))))
        (.seqn #[]) .breakStmt,
      innerForBlock]

/-- The subject's `Func` record, verbatim from the pinned lowering (the
`example` pin below ties it by `rfl`). -/
def isortFunc : Func :=
  { id := { key := "insertionSort" },
    args := #[{ id := "s", typ := .slice (.int .uint64) }],
    results := #[],
    body := .block #[]
      #[.block #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .int },
                .assign (.var "i") (.intLit 1 .int)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) outerWhileBody]]],
    variadic := false,
    wrapper := false }

/-- The lowering pin: the proof subject IS the frontend's lowering. -/
example : findFunctionIn? isortLowered.funcs ⟨"insertionSort"⟩ = some isortFunc :=
  rfl

/-- The driver: `insertionSort(s)` with the slice handle over the
backing array at `base` as the literal argument. -/
def isortCall (xs : List Int) (base : Nat) : Stmt :=
  .call #[] ⟨"insertionSort"⟩
    #[.slice (.locLit (.base ⟨base⟩)) (.intLit 0 .int)
        (.intLit xs.length .int) none]

/-- The framed seed: input backing cell at `base`, arbitrary frame
`fr`, allocator at `na`. Canonical placement: `isortSeed xs 0 [] 1`. -/
def isortSeed (xs : List Int) (base : Nat) (fr : Heap) (na : Nat) :
    ExecState :=
  { types := isortLowered.typeDefs.toList,
    functions := isortLowered.funcs,
    methods := isortLowered.methods,
    heap := sliceCells xs base ++ fr, nextAddr := na }

/-! ## The pure spec layer -/

/-- Insert `v` into a (sorted) list, AFTER all elements ≤ v (Go's
strict-`>` swap keeps equal elements in place — stability). -/
def insertSpec (v : Int) : List Int → List Int
  | [] => [v]
  | w :: rest => if w ≤ v then w :: insertSpec v rest else v :: w :: rest

/-- Insertion sort: fold the input left-to-right into a sorted prefix. -/
def sortSpec (xs : List Int) : List Int :=
  xs.foldl (fun acc v => insertSpec v acc) []

private theorem mem_insertSpec {v x : Int} {p : List Int}
    (h : x ∈ insertSpec v p) : x = v ∨ x ∈ p := by
  induction p with
  | nil =>
      simp only [insertSpec, List.mem_singleton] at h
      exact .inl h
  | cons w rest ih =>
      simp only [insertSpec] at h
      split at h
      · rw [List.mem_cons] at h
        rcases h with h | h
        · exact .inr (by simp [h])
        · rcases ih h with h | h
          · exact .inl h
          · exact .inr (by simp [h])
      · rw [List.mem_cons] at h
        rcases h with h | h
        · exact .inl h
        · exact .inr h

private theorem insertSpec_length (v : Int) (p : List Int) :
    (insertSpec v p).length = p.length + 1 := by
  induction p with
  | nil => rfl
  | cons w rest ih =>
      simp only [insertSpec]
      split <;> simp [ih]

private theorem insertSpec_pairwise {v : Int} {p : List Int}
    (h : p.Pairwise (· ≤ ·)) : (insertSpec v p).Pairwise (· ≤ ·) := by
  induction p with
  | nil => simp [insertSpec]
  | cons w rest ih =>
      rw [List.pairwise_cons] at h
      obtain ⟨hw, hrest⟩ := h
      simp only [insertSpec]
      split
      · rw [List.pairwise_cons]
        refine ⟨fun x hx => ?_, ih hrest⟩
        rcases mem_insertSpec hx with rfl | hx
        · assumption
        · exact hw x hx
      · rw [List.pairwise_cons]
        refine ⟨fun x hx => ?_, by rw [List.pairwise_cons]; exact ⟨hw, hrest⟩⟩
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · exact Int.le_trans (by omega) (hw x hx)

private theorem insertSpec_count (v w : Int) (p : List Int) :
    (insertSpec v p).count w = p.count w + (if v = w then 1 else 0) := by
  induction p with
  | nil => simp [insertSpec, List.count_cons, beq_iff_eq]
  | cons u rest ih =>
      simp only [insertSpec]
      split
      · rw [List.count_cons, ih, List.count_cons]
        omega
      · simp only [List.count_cons, beq_iff_eq]

private theorem sortSpec_go_length (xs acc : List Int) :
    (xs.foldl (fun acc v => insertSpec v acc) acc).length
      = acc.length + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x rest ih =>
      simp only [List.foldl_cons, ih, insertSpec_length, List.length_cons]
      omega

/-- `sortSpec` preserves length. -/
theorem sortSpec_length (xs : List Int) : (sortSpec xs).length = xs.length := by
  simpa [sortSpec] using sortSpec_go_length xs []

private theorem sortSpec_go_count (xs acc : List Int) (w : Int) :
    (xs.foldl (fun acc v => insertSpec v acc) acc).count w
      = acc.count w + xs.count w := by
  induction xs generalizing acc with
  | nil => simp
  | cons x rest ih =>
      simp only [List.foldl_cons, ih, insertSpec_count, List.count_cons,
        beq_iff_eq]
      split <;> omega

/-- `sortSpec` is a permutation, stated first-order: every value's
multiplicity is preserved. -/
theorem sortSpec_count (xs : List Int) (v : Int) :
    (sortSpec xs).count v = xs.count v := by
  simpa [sortSpec] using sortSpec_go_count xs [] v

private theorem sortSpec_go_pairwise (xs acc : List Int)
    (h : acc.Pairwise (· ≤ ·)) :
    (xs.foldl (fun acc v => insertSpec v acc) acc).Pairwise (· ≤ ·) := by
  induction xs generalizing acc with
  | nil => simpa
  | cons x rest ih => exact ih _ (insertSpec_pairwise h)

private theorem sorted_of_pairwise {l : List Int}
    (h : l.Pairwise (· ≤ ·)) : Sorted l := by
  intro i j hij hj
  rw [List.pairwise_iff_getElem] at h
  have := h i j (by omega) hj hij
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega : i < l.length),
    List.getElem?_eq_getElem hj]
  simpa using this

/-- `sortSpec` sorts (the shared gallery `Sorted` — one definition,
`GoLean.SliceMem.Sorted`). -/
theorem sortSpec_sorted (xs : List Int) : Sorted (sortSpec xs) :=
  sorted_of_pairwise (sortSpec_go_pairwise xs [] (by simp))

/-- Membership transport (for the uint64 range hypotheses). -/
private theorem mem_sortSpec {x : Int} {xs : List Int}
    (h : x ∈ sortSpec xs) : x ∈ xs := by
  have h1 : 0 < (sortSpec xs).count x := List.count_pos_iff.mpr h
  rw [sortSpec_count] at h1
  exact List.count_pos_iff.mp h1

/-! ### sortPrefix: the outer-loop invariant's list -/

/-- The backing list after `k` elements are folded in: sorted prefix,
untouched suffix. -/
def sortPrefix (xs : List Int) (k : Nat) : List Int :=
  sortSpec (xs.take k) ++ xs.drop k

private theorem sortPrefix_one (xs : List Int) : sortPrefix xs 1 = xs := by
  cases xs with
  | nil => rfl
  | cons x rest => simp [sortPrefix, sortSpec, insertSpec, List.take_succ_cons,
      List.drop_succ_cons]

private theorem sortPrefix_full {xs : List Int} {k : Nat}
    (h : xs.length ≤ k) : sortPrefix xs k = sortSpec xs := by
  rw [sortPrefix, List.take_of_length_le h, List.drop_of_length_le h,
    List.append_nil]

/-- The fold step: the next element inserts into the sorted prefix. -/
private theorem sortSpec_take_succ {xs : List Int} {k : Nat}
    (h : k < xs.length) :
    sortSpec (xs.take (k + 1))
      = insertSpec (xs.getD k 0) (sortSpec (xs.take k)) := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  show sortSpec (xs.take k ++ [xs[k]]) = _
  rw [sortSpec, List.foldl_append]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

private theorem sortPrefix_decomp {xs : List Int} {k : Nat}
    (h : k < xs.length) :
    sortPrefix xs k = sortSpec (xs.take k) ++ xs.getD k 0 :: xs.drop (k + 1) := by
  rw [sortPrefix, List.drop_eq_getElem_cons h, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h]
  rfl

/-! ### bubbleState: the inner-loop invariant's prefix -/

/-- The sorted prefix `p` (length i) with `v` being bubbled down: `v`
currently sits at position `j`; the elements formerly at `j..i-1` are
shifted up by one. -/
def bubbleState (p : List Int) (v : Int) (j : Nat) : List Int :=
  p.take j ++ v :: p.drop j

private theorem bubbleState_length {p : List Int} {v : Int} {j : Nat}
    (h : j ≤ p.length) :
    (bubbleState p v j).length = p.length + 1 := by
  simp [bubbleState]
  omega

private theorem bubbleState_full (p : List Int) (v : Int) :
    bubbleState p v p.length = p ++ [v] := by
  simp [bubbleState]

private theorem bubbleState_getElem?_lt {p : List Int} {v : Int} {j k : Nat}
    (hk : k < j) (hj : j ≤ p.length) :
    (bubbleState p v j)[k]? = p[k]? := by
  rw [bubbleState, List.getElem?_append_left (by simp; omega),
    List.getElem?_take_of_lt hk]

private theorem bubbleState_getElem?_eq {p : List Int} {v : Int} {j : Nat}
    (hj : j ≤ p.length) :
    (bubbleState p v j)[j]? = some v := by
  rw [bubbleState, List.getElem?_append_right (by simp; omega)]
  simp [List.length_take, Nat.min_eq_left hj]

private theorem bubbleState_getElem?_gt {p : List Int} {v : Int} {j k : Nat}
    (hk : j < k) (hj : j ≤ p.length) :
    (bubbleState p v j)[k]? = p[k - 1]? := by
  rw [bubbleState, List.getElem?_append_right (by simp; omega)]
  rw [List.length_take, Nat.min_eq_left hj]
  cases hkk : k - j with
  | zero => omega
  | succ d =>
      simp only [List.getElem?_cons_succ, List.getElem?_drop]
      congr 1
      omega

private theorem bubbleState_getD_lt {p : List Int} {v : Int} {j k : Nat}
    (hk : k < j) (hj : j ≤ p.length) :
    (bubbleState p v j).getD k 0 = p.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    bubbleState_getElem?_lt hk hj]

private theorem bubbleState_getD_eq {p : List Int} {v : Int} {j : Nat}
    (hj : j ≤ p.length) :
    (bubbleState p v j).getD j 0 = v := by
  rw [List.getD_eq_getElem?_getD, bubbleState_getElem?_eq hj]
  rfl

/-- Membership transport for bubbleState. -/
private theorem mem_bubbleState {p : List Int} {v x : Int} {j : Nat}
    (h : x ∈ bubbleState p v j) : x = v ∨ x ∈ p := by
  simp only [bubbleState, List.mem_append, List.mem_cons] at h
  rcases h with h | h | h
  · exact .inr (List.mem_of_mem_take h)
  · exact .inl h
  · exact .inr (List.mem_of_mem_drop h)

/-- **One machine swap advances the bubble**: writing `v` at `j-1` and
the old `p[j-1]` at `j` is exactly the bubble at `j-1` (the machine's
store order: `s[j-1] := s[j]` then `s[j] := old s[j-1]`). -/
private theorem bubbleState_swap {p : List Int} {v : Int} {j : Nat}
    (h1 : 1 ≤ j) (hj : j ≤ p.length) :
    ((bubbleState p v j).set (j - 1) v).set j (p.getD (j - 1) 0)
      = bubbleState p v (j - 1) := by
  have hgetd : p[j - 1]? = some (p.getD (j - 1) 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  apply List.ext_getElem?
  intro k
  by_cases hk : k < p.length + 1
  · rw [List.getElem?_set, List.getElem?_set]
    simp only [List.length_set, bubbleState_length hj]
    by_cases hkj : j = k
    · subst hkj
      rw [if_pos rfl, if_pos (by omega),
        bubbleState_getElem?_gt (by omega) (by omega), hgetd]
    · rw [if_neg hkj]
      by_cases hkj1 : j - 1 = k
      · subst hkj1
        rw [if_pos rfl, if_pos (by omega),
          bubbleState_getElem?_eq (by omega)]
      · rw [if_neg hkj1]
        by_cases hlt : k < j - 1
        · rw [bubbleState_getElem?_lt hlt (by omega),
            bubbleState_getElem?_lt (by omega) hj]
        · rw [bubbleState_getElem?_gt (by omega) hj,
            bubbleState_getElem?_gt (by omega) (by omega)]
  · rw [List.getElem?_eq_none (by simp [List.length_set, bubbleState_length hj]; omega),
      List.getElem?_eq_none (by simp [bubbleState_length (by omega : j - 1 ≤ p.length)]; omega)]

/-- **At the inner exit the bubble IS the insertion**: once `j = 0` or
`p[j-1] ≤ v`, with everything from `j` up strictly greater than `v`,
the bubble equals `insertSpec v p`. -/
private theorem bubbleState_exit {p : List Int} {v : Int} {j : Nat}
    (hsort : Sorted p) (hj : j ≤ p.length)
    (hstop : j = 0 ∨ p.getD (j - 1) 0 ≤ v)
    (hgt : ∀ k, j ≤ k → k < p.length → v < p.getD k 0) :
    bubbleState p v j = insertSpec v p := by
  induction p generalizing j with
  | nil =>
      have : j = 0 := by simpa using hj
      subst this
      rfl
  | cons w rest ih =>
      cases j with
      | zero =>
          have hvw : v < w := by
            have := hgt 0 (by omega) (by simp)
            simpa using this
          simp only [bubbleState, List.drop_zero, insertSpec,
            List.take_zero, List.nil_append]
          rw [if_neg (by omega)]
      | succ jj =>
          have hwv : w ≤ v := by
            rcases hstop with h | h
            · omega
            · calc w = (w :: rest).getD 0 0 := rfl
                _ ≤ (w :: rest).getD jj 0 := by
                    cases Nat.eq_zero_or_pos jj with
                    | inl hz => rw [hz]; exact Int.le_refl _
                    | inr hpos => exact hsort 0 jj hpos (by simp at hj ⊢; omega)
                _ ≤ v := by simpa using h
          have htail : Sorted rest := by
            intro a b hab hb
            have := hsort (a + 1) (b + 1) (by omega) (by simp; omega)
            simpa using this
          show w :: bubbleState rest v jj = insertSpec v (w :: rest)
          rw [insertSpec, if_pos hwv]
          congr 1
          refine ih htail (by simpa using hj) ?_ ?_
          · rcases hstop with h | h
            · omega
            · cases jj with
              | zero => exact .inl rfl
              | succ j2 =>
                  right
                  simpa using h
          · intro k hk hk'
            have := hgt (k + 1) (by omega) (by simpa using Nat.succ_lt_succ hk')
            simpa using this

/-- Set distributes over the append at in-prefix positions (the machine
stores on the FULL backing list). -/
private theorem set_append_left {l1 l2 : List Int} {k : Nat} {x : Int}
    (h : k < l1.length) : (l1 ++ l2).set k x = l1.set k x ++ l2 := by
  induction l1 generalizing k with
  | nil => simp at h
  | cons a rest ih =>
      cases k with
      | zero => rfl
      | succ kk =>
          simp only [List.cons_append, List.set_cons_succ]
          rw [ih (by simpa using h)]

/-! ## The machine layer: canonical-placement configurations

Transcribed from the machine (probe-verified against concrete runs;
every raw segment below re-checks the transcription by `rfl`).
Canonical address layout: 0 = the backing array, 1 = the parameter `s`
(the handle), 2 = `i`, 3 = the OUTER `$forFirst`; the pass-local cells
4 = `j`, 5 = the INNER `$forFirst` exist only inside a pass at the
tight placement (the true run re-allocates them per pass at moving
addresses — the frame-rebase layer below carries that). -/

private abbrev intcell (v : Int) : HeapCell := ⟨some (.int .int), .int v .int⟩
private abbrev bcell (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
private abbrev arrCell (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n (.int .uint64)), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
private abbrev handleCell (n : Nat) : HeapCell :=
  ⟨some (.slice (.int .uint64)), .slice ⟨some (.base ⟨0⟩), 0, n, n⟩⟩
private abbrev sliceH (n : Nat) : GoValue :=
  .slice ⟨some (.base ⟨0⟩), 0, n, n⟩

private def envO : LocalEnv :=
  [[("$forFirst", .base ⟨3⟩)], [("i", .base ⟨2⟩)], [], [("s", .base ⟨1⟩)]]
private def envOMid : LocalEnv := [[("i", .base ⟨2⟩)], [], [("s", .base ⟨1⟩)]]
private def envOOut : LocalEnv := [[], [("s", .base ⟨1⟩)]]

private def headTailO : Cont :=
  .seq [] envO (.seq [] envOMid (.seq [] envOOut
    (.frame [] [] [] [] .stop false)))
/-- The OUTER loop-head configuration. -/
private def outerHeadCfg : Config :=
  .exec (.while (.boolLit true) outerWhileBody) envO headTailO
private def loopKO : Cont := .loop (.boolLit true) outerWhileBody envO headTailO
/-- The outer exit test's delivery continuation. -/
private def outerCmpCont : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envO)
    (.seq [innerForBlock] ([] :: envO) loopKO)
/-- The `len(s)` apply point inside the outer test, carrying the
already-evaluated `i` operand. -/
private def lenTestK (iv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice (.int .uint64)))) [] [] ([] :: envO)
    (.strictK .lessCmp [.int iv .int] [] ([] :: envO) outerCmpCont)

private def envI : LocalEnv :=
  [("$forFirst", .base ⟨5⟩)] :: [("j", .base ⟨4⟩)] :: [] :: [] :: envO
private def innerTail : Cont :=
  .seq [] envI
    (.seq [] ([("j", .base ⟨4⟩)] :: [] :: [] :: envO)
      (.seq [] ([] :: [] :: envO)
        (.seq [] ([] :: envO) loopKO)))
/-- The INNER loop-head configuration (tight placement). -/
private def innerHeadCfg : Config :=
  .exec (.while (.boolLit true) innerWhileBody) envI innerTail
private def loopKI : Cont := .loop (.boolLit true) innerWhileBody envI innerTail
/-- The inner test's `if` delivery continuation. -/
private def innerIfK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envI)
    (.seq [isortSwapBlock] ([] :: envI) loopKI)
/-- The short-circuit `&&` continuation: first conjunct delivers HERE;
`false` skips the index reads entirely (Go's laziness — load-bearing at
`j = 0`). -/
private def andKCont : Cont :=
  .andK (.greaterCmp
      (.indexGet (.var "s") (.sub (.var "j") (.intLit 1 .int)))
      (.indexGet (.var "s") (.var "j")))
    ([] :: envI) innerIfK
/-- The second conjunct's spine: first index read pending the second. -/
private def gcK1 : Cont :=
  .strictK .greaterCmp [] [.indexGet (.var "s") (.var "j")] ([] :: envI)
    (.boolK innerIfK)
private def gcK2 (w1 : GoValue) : Cont :=
  .strictK .greaterCmp [w1] [] ([] :: envI) (.boolK innerIfK)

private def envSw : LocalEnv := [] :: [] :: envI
private def swTail : Cont :=
  .seq [] envSw (.seq [] ([] :: envI) loopKI)
private def refj (n : Nat) (idx : Int) : TargetRef :=
  .chain (sliceH n) [.int idx .int] [.index]
private def rhsK1 (n : Nat) (idx1 jv : Int) : Cont :=
  .rhsK .vals [refj n idx1, refj n jv] []
    [.indexGet (.var "s") (.sub (.var "j") (.intLit 1 .int))]
    (.seqn #[]) envSw swTail
private def rhsK2 (n : Nat) (idx1 jv : Int) (wj : GoValue) : Cont :=
  .rhsK .vals [refj n idx1, refj n jv] [wj] [] (.seqn #[]) envSw swTail

/-- The outer-head state family, TAIL-PARAMETRIC: the four active cells
in front, an arbitrary inert tail behind (the raw dispatch/exit
segments never touch past cell 3, so one segment statement serves both
the tight 4-cell state and the post-pass 6-cell state). -/
private def σOutT (n : Nat) (l : List Int) (iv : Int) (ffv : Bool)
    (tail : Heap) (na : Nat) : ExecState :=
  { types := isortLowered.typeDefs.toList,
    functions := isortLowered.funcs,
    methods := isortLowered.methods,
    heap := (.base ⟨0⟩, arrCell n l) :: (.base ⟨1⟩, handleCell n)
      :: (.base ⟨2⟩, intcell iv) :: (.base ⟨3⟩, bcell ffv) :: tail,
    nextAddr := na }

/-- The tight 4-cell outer state (canonical pass placement). -/
private def σOut (n : Nat) (l : List Int) (iv : Int) (ffv : Bool) :
    ExecState :=
  σOutT n l iv ffv [] 4

/-- The tight 6-cell in-pass state: `j` at 4, inner `$forFirst` at 5.
The outer `$forFirst` is `false` throughout a pass. -/
private def σIn (n : Nat) (l : List Int) (iv jv : Int) (ffIv : Bool) :
    ExecState :=
  σOutT n l iv false [(.base ⟨4⟩, intcell jv), (.base ⟨5⟩, bcell ffIv)] 6

/-! ## Raw run segments (`with_unfolding_all rfl`) -/

private def entryK : Cont := .callArgsK ⟨"insertionSort"⟩ [] [] [] [] .stop

/-- Entry A: driver start → the slice-expression apply point. -/
private theorem isort_entryA_raw (xs : List Int) (ch : Choices) :
    stepFnIter 7 (isortSeed xs 0 [] 1) (.exec (isortCall xs 0) [] .stop) ch
      = .ok (.retV (.int (IntKind.normalize .int (xs.length : Int)) .int)
            (.strictK (.sliceExpr false) [.int 0 .int, .addr (.base ⟨0⟩)]
              [] [] entryK),
          isortSeed xs 0 [] 1, ch) := by
  with_unfolding_all rfl

/-- Entry B: frame entry, `i := 1`, the `$forFirst` block → the outer
loop head at the tight 4-cell state. -/
private theorem isort_entryB_raw (xs : List Int) (ch : Choices) :
    stepFnIter 31 (isortSeed xs 0 [] 1) (.retV (sliceH xs.length) entryK) ch
      = .ok (outerHeadCfg, σOut xs.length xs 1 true, ch) := by
  with_unfolding_all rfl

/-- First-pass outer dispatch: head with the flag up → the `len(s)`
apply point of the exit test (`i` unchanged, flag lowered). TAIL-
PARAMETRIC: touches only cells 0–3. -/
private theorem isort_segO0_raw (n : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 25 (σOutT n l iv true tail na) outerHeadCfg ch
      = .ok (.retV (sliceH n) (lenTestK iv),
          σOutT n l iv false tail na, ch) := by
  with_unfolding_all rfl

/-- Later-pass outer dispatch: head with the flag down → `i := i + 1`,
then the `len(s)` apply point. -/
private theorem isort_segO1_raw (n : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 29 (σOutT n l iv false tail na) outerHeadCfg ch
      = .ok (.retV (sliceH n)
            (lenTestK (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
          σOutT n l (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            false tail na, ch) := by
  with_unfolding_all rfl

/-- The outer comparison delivered: `len` value in → the test bool at
the `if` continuation. -/
private theorem isort_segOB_raw (n : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 1 (σOutT n l iv false tail na)
      (.retV (.int ((n : Nat) : Int) .int)
        (.strictK .lessCmp [.int iv .int] [] ([] :: envO) outerCmpCont)) ch
      = .ok (.retV (.bool (decide (iv < ((n : Nat) : Int)))) outerCmpCont,
          σOutT n l iv false tail na, ch) := by
  with_unfolding_all rfl

/-- Outer exit: test false → break unwinding, frame exit, the driver
terminal. The state is untouched. -/
private theorem isort_exitO_raw (n : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 8 (σOutT n l iv false tail na)
      (.retV (.bool false) outerCmpCont) ch
      = .ok (.next .stop, σOutT n l iv false tail na, ch) := by
  with_unfolding_all rfl

/-- Pass entry: outer test true → the inner `for`'s declarations
(`j := i` at 4, inner `$forFirst` at 5 — allocation, so TIGHT placement
only) → the inner loop head. -/
private theorem isort_segPA_raw (n : Nat) (l : List Int) (iv : Int)
    (ch : Choices) :
    stepFnIter 33 (σOut n l iv false) (.retV (.bool true) outerCmpCont) ch
      = .ok (innerHeadCfg, σIn n l iv (IntKind.normalize .int iv) true, ch) := by
  with_unfolding_all rfl

/-- First-pass inner dispatch: inner head with the flag up → the FIRST
conjunct (`j > 0`) delivered at the short-circuit `&&` continuation
(the second conjunct's reads have NOT run). -/
private theorem isort_segI0_raw (n : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 26 (σIn n l iv jv true) innerHeadCfg ch
      = .ok (.retV (.bool (decide (0 < jv))) andKCont,
          σIn n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Later-pass inner dispatch: `j := j - 1`, then the first conjunct at
the `&&` continuation. -/
private theorem isort_segI1_raw (n : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 30 (σIn n l iv jv false) innerHeadCfg ch
      = .ok (.retV (.bool (decide
              (0 < IntKind.normalize .int (IntKind.normalize .int (jv - 1)))))
            andKCont,
          σIn n l iv
            (IntKind.normalize .int (IntKind.normalize .int (jv - 1)))
            false, ch) := by
  with_unfolding_all rfl

/-- The `&&` SHORT-CIRCUIT arm: first conjunct false → `false` delivered
straight to the inner `if` — no index read happens (`j = 0` never
evaluates `s[j-1]`). -/
private theorem isort_andFalse_raw (n : Nat) (l : List Int) (iv jv : Int)
    (ffIv : Bool) (ch : Choices) :
    stepFnIter 1 (σIn n l iv jv ffIv) (.retV (.bool false) andKCont) ch
      = .ok (.retV (.bool false) innerIfK, σIn n l iv jv ffIv, ch) := by
  with_unfolding_all rfl

/-- Inner exit: the inner `if` sees false → break unwinds the INNER
loop only, popping back to the OUTER loop head. State untouched. -/
private theorem isort_exitI_raw (n : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 9 (σIn n l iv jv false) (.retV (.bool false) innerIfK) ch
      = .ok (outerHeadCfg, σIn n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Second conjunct, phase A: `&&` sees true → the `s[j-1]` read's
apply point (handle fetched, `j - 1` computed). -/
private theorem isort_segCA_raw (n : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 10 (σIn n l iv jv false) (.retV (.bool true) andKCont) ch
      = .ok (.retV (.int (IntKind.normalize .int (jv - 1)) .int)
            (.strictK .indexGet [sliceH n] [] ([] :: envI) gcK1),
          σIn n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Second conjunct, phase B: first element in → the `s[j]` read's
apply point. -/
private theorem isort_segCB_raw (n : Nat) (l : List Int) (iv jv : Int)
    (w1 : GoValue) (ch : Choices) :
    stepFnIter 5 (σIn n l iv jv false) (.retV w1 gcK1) ch
      = .ok (.retV (.int jv .int)
            (.strictK .indexGet [sliceH n] [] ([] :: envI) (gcK2 w1)),
          σIn n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Second conjunct, phase C: both elements in → the comparison bool
through `boolK` to the inner `if`. -/
private theorem isort_segCC_raw (n : Nat) (l : List Int) (iv jv a b : Int)
    (ch : Choices) :
    stepFnIter 2 (σIn n l iv jv false)
      (.retV (.int b .uint64) (gcK2 (.int a .uint64))) ch
      = .ok (.retV (.bool (decide (b < a))) innerIfK,
          σIn n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase A: inner `if` true → both target refs resolved → the
first rhs read's (`s[j]`) apply point. -/
private theorem isort_segSA_raw (n : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 24 (σIn n l iv jv false) (.retV (.bool true) innerIfK) ch
      = .ok (.retV (.int jv .int)
            (.strictK .indexGet [sliceH n] [] envSw
              (rhsK1 n (IntKind.normalize .int (jv - 1)) jv)),
          σIn n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase B: first rhs value in → the second rhs read's
(`s[j-1]`) apply point. -/
private theorem isort_segSB_raw (n : Nat) (l : List Int) (iv jv idx1 : Int)
    (wj : GoValue) (ch : Choices) :
    stepFnIter 9 (σIn n l iv jv false) (.retV wj (rhsK1 n idx1 jv)) ch
      = .ok (.retV (.int (IntKind.normalize .int (jv - 1)) .int)
            (.strictK .indexGet [sliceH n] [] envSw (rhsK2 n idx1 jv wj)),
          σIn n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase B → stores: both rhs values in → phase 2 begins. -/
private theorem isort_segSC_raw (n : Nat) (l : List Int) (iv jv idx1 : Int)
    (wj wi : GoValue) (ch : Choices) :
    stepFnIter 1 (σIn n l iv jv false) (.retV wi (rhsK2 n idx1 jv wj)) ch
      = .ok (.next (.storeK [refj n idx1, refj n jv] [wj, wi] (.seqn #[])
            envSw swTail),
          σIn n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap tail: stores done → back to the inner loop head. -/
private theorem isort_segSD_raw (n : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 5 (σIn n l iv jv false)
      (.next (.storeK [] [] (.seqn #[]) envSw swTail)) ch
      = .ok (innerHeadCfg, σIn n l iv jv false, ch) := by
  with_unfolding_all rfl

/-! ## Cleaned discharge facts -/

private theorem getD_append_left {l1 l2 : List Int} {k : Nat}
    (h : k < l1.length) : (l1 ++ l2).getD k 0 = l1.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h]

private theorem lookup_σIn0 (n : Nat) (l : List Int) (iv jv : Int)
    (ffIv : Bool) :
    Heap.lookup (σIn n l iv jv ffIv).heap (.base ⟨0⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := rfl

/-- One element read at the tight in-pass state (both `s[j-1]` and
`s[j]` go through this). -/
private theorem stepFn_read_σIn {n : Nat} {l : List Int} {iv jv : Int}
    {ffIv : Bool} {k : Nat} {env : LocalEnv} {K : Cont} {ch : Choices}
    (hk : k < n) (hlen : l.length = n) :
    stepFn (σIn n l iv jv ffIv)
      (.retV (.int ((k : Nat) : Int) .int)
        (.strictK .indexGet [sliceH n] [] env K)) ch
      = .ok (.retV (.int (l.getD k 0) .uint64) K, σIn n l iv jv ffIv, ch) :=
  stepFn_strict_apply
    (applyStrictOp_indexGet_slice (lookup_σIn0 n l iv jv ffIv)
      (Nat.le_refl n) hk
      (by rw [Nat.zero_add]; exact getElem?_mapU l k (by omega)))

/-- One element store at the tight in-pass state. -/
private theorem store_σIn {n : Nat} {l : List Int} {iv jv : Int}
    {ffIv : Bool} {k : Nat} {w : Int}
    (hk : k < n) (hlen : l.length = n)
    (hl : ∀ x ∈ l, 0 ≤ x ∧ x < 2 ^ 64) (hw : 0 ≤ w ∧ w < 2 ^ 64) :
    storeTarget (σIn n l iv jv ffIv) (refj n ((k : Nat) : Int))
      (.int w .uint64)
      = .ok (σIn n (l.set k w) iv jv ffIv) := by
  have h := storeTarget_slice_u64 (a := ⟨0⟩) (off := 0) (len := n) (cap := n)
    (i := k) (n := n) (ik := .int) (l := l) (w := w)
    (lookup_σIn0 n l iv jv ffIv) (Nat.le_refl n) hk (by omega) hlen hl hw
  rw [Nat.zero_add] at h
  exact h

/-! ## The INNER induction (arc design: plain strong induction on the
descending counter `j`; invariant `bubbleState`; anchored at the
first-conjunct delivery point of the short-circuit `&&`) -/

/-- **The inner loop**: from the first-conjunct delivery at counter
`jv` — backing list `bubbleState p v jv ++ suffix`, `v` bubbling down
the sorted prefix `p` — the run returns to the OUTER loop head with the
insertion complete, within `92·jv + 10` steps. `jex` is the final
(retired) counter value. -/
private theorem inner_loop (n : Nat) (ivv : Int) (p suffix : List Int)
    (v : Int) (hn : n < 2 ^ 63)
    (hlen : p.length + 1 + suffix.length = n)
    (hsort : Sorted p)
    (hrp : ∀ x ∈ p, 0 ≤ x ∧ x < 2 ^ 64)
    (hrv : 0 ≤ v ∧ v < 2 ^ 64)
    (hrs : ∀ x ∈ suffix, 0 ≤ x ∧ x < 2 ^ 64) :
    ∀ μ jv, μ = jv → jv ≤ p.length →
    (∀ k, jv ≤ k → k < p.length → v < p.getD k 0) →
    ∀ ch : Choices, ∃ (k jex : Nat),
      k ≤ 92 * jv + 10 ∧ jex ≤ p.length ∧
      stepFnIter k
        (σIn n (bubbleState p v jv ++ suffix) ivv ((jv : Nat) : Int) false)
        (.retV (.bool (decide (0 < ((jv : Nat) : Int)))) andKCont) ch
        = .ok (outerHeadCfg,
            σIn n (insertSpec v p ++ suffix) ivv ((jex : Nat) : Int) false,
            ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro jv hμ hjp hinv ch
    have hbl : (bubbleState p v jv ++ suffix).length = n := by
      rw [List.length_append, bubbleState_length hjp]; omega
    cases jv with
    | zero =>
        -- the SHORT-CIRCUIT exit: j = 0, the index reads never run
        rw [show (decide (0 < ((0 : Nat) : Int))) = false from
          decide_eq_false (by omega)]
        rw [← bubbleState_exit hsort (by omega) (.inl rfl)
          (fun k _ hk => hinv k (by omega) hk)]
        have hX0 := isort_andFalse_raw n (bubbleState p v 0 ++ suffix) ivv
          ((0 : Nat) : Int) false ch
        have hX1 := isort_exitI_raw n (bubbleState p v 0 ++ suffix) ivv
          ((0 : Nat) : Int) ch
        exact ⟨10, 0, by omega, by omega, stepFnIter_chain hX0 hX1⟩
    | succ jj =>
        have hjj : jj < p.length := by omega
        have hjj63 : jj < 2 ^ 63 := by omega
        have hrL : ∀ x ∈ bubbleState p v (jj + 1) ++ suffix,
            0 ≤ x ∧ x < 2 ^ 64 := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · rcases mem_bubbleState hx with rfl | hx
            · exact hrv
            · exact hrp x hx
          · exact hrs x hx
        rw [show (decide (0 < ((jj + 1 : Nat) : Int))) = true from
          decide_eq_true (by omega)]
        -- condition reads: s[j-1] then s[j]
        have hCA := isort_segCA_raw n (bubbleState p v (jj + 1) ++ suffix)
          ivv ((jj + 1 : Nat) : Int) ch
        rw [show (((jj + 1 : Nat) : Int) - 1) = ((jj : Nat) : Int) from by
            omega,
          inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega)]
          at hCA
        have hgd1 : (bubbleState p v (jj + 1) ++ suffix).getD jj 0
            = p.getD jj 0 := by
          rw [getD_append_left (by rw [bubbleState_length hjp]; omega),
            bubbleState_getD_lt (by omega) hjp]
        have hread1 := stepFn_read_σIn (n := n)
          (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
          (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj)
          (env := [] :: envI) (K := gcK1) (ch := ch) (by omega) hbl
        rw [hgd1] at hread1
        have hCB := isort_segCB_raw n (bubbleState p v (jj + 1) ++ suffix)
          ivv ((jj + 1 : Nat) : Int) (.int (p.getD jj 0) .uint64) ch
        have hgd2 : (bubbleState p v (jj + 1) ++ suffix).getD (jj + 1) 0
            = v := by
          rw [getD_append_left (by rw [bubbleState_length hjp]; omega),
            bubbleState_getD_eq hjp]
        have hread2 := stepFn_read_σIn (n := n)
          (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
          (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj + 1)
          (env := [] :: envI) (K := gcK2 (.int (p.getD jj 0) .uint64))
          (ch := ch) (by omega) hbl
        rw [hgd2] at hread2
        have hCC := isort_segCC_raw n (bubbleState p v (jj + 1) ++ suffix)
          ivv ((jj + 1 : Nat) : Int) (p.getD jj 0) v ch
        have h19 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain hCA (stepFnIter_one hread1)) hCB)
          (stepFnIter_one hread2)) hCC
        by_cases hcmp : v < p.getD jj 0
        · -- the element test fires: SWAP, then recurse at jj
          rw [decide_eq_true hcmp] at h19
          have hSA := isort_segSA_raw n (bubbleState p v (jj + 1) ++ suffix)
            ivv ((jj + 1 : Nat) : Int) ch
          rw [show (((jj + 1 : Nat) : Int) - 1) = ((jj : Nat) : Int) from by
              omega,
            inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega)]
            at hSA
          -- rhs read 1: s[j] (the bubbled v)
          have hgetj := stepFn_read_σIn (n := n)
            (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
            (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj + 1)
            (env := envSw)
            (K := rhsK1 n ((jj : Nat) : Int) ((jj + 1 : Nat) : Int))
            (ch := ch) (by omega) hbl
          rw [hgd2] at hgetj
          have hSB := isort_segSB_raw n (bubbleState p v (jj + 1) ++ suffix)
            ivv ((jj + 1 : Nat) : Int) ((jj : Nat) : Int)
            (.int v .uint64) ch
          rw [show (((jj + 1 : Nat) : Int) - 1) = ((jj : Nat) : Int) from by
              omega,
            inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega)]
            at hSB
          -- rhs read 2: s[j-1] (the displaced prefix element)
          have hgetj1 := stepFn_read_σIn (n := n)
            (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
            (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj)
            (env := envSw)
            (K := rhsK2 n ((jj : Nat) : Int) ((jj + 1 : Nat) : Int)
              (.int v .uint64))
            (ch := ch) (by omega) hbl
          rw [hgd1] at hgetj1
          have hSC := isort_segSC_raw n (bubbleState p v (jj + 1) ++ suffix)
            ivv ((jj + 1 : Nat) : Int) ((jj : Nat) : Int)
            (.int v .uint64) (.int (p.getD jj 0) .uint64) ch
          -- store 1: s[j-1] := v
          have hst1 := store_σIn (n := n)
            (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
            (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj)
            (w := v) (by omega) hbl hrL hrv
          have hstep1 := stepFn_store_step
            (rs := [refj n ((jj + 1 : Nat) : Int)])
            (vs := [.int (p.getD jj 0) .uint64]) (body := .seqn #[])
            (env := envSw) (k := swTail) (ch := ch) hst1
          -- store 2: s[j] := old s[j-1]
          have hrL1 : ∀ x ∈ (bubbleState p v (jj + 1) ++ suffix).set jj v,
              0 ≤ x ∧ x < 2 ^ 64 := by
            intro x hx
            rcases mem_set_of_mem hx with rfl | hx
            · exact hrv
            · exact hrL x hx
          have hst2 := store_σIn (n := n)
            (l := (bubbleState p v (jj + 1) ++ suffix).set jj v) (iv := ivv)
            (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj + 1)
            (w := p.getD jj 0) (by omega)
            (by rw [List.length_set]; exact hbl) hrL1
            (hrp _ (getD_mem hjj))
          have hstep2 := stepFn_store_step (rs := []) (vs := [])
            (body := .seqn #[]) (env := envSw) (k := swTail) (ch := ch)
            hst2
          -- the list surgery: two sets = the bubble advanced
          have hsurg : ((bubbleState p v (jj + 1) ++ suffix).set jj v).set
              (jj + 1) (p.getD jj 0)
              = bubbleState p v jj ++ suffix := by
            rw [set_append_left (by rw [bubbleState_length hjp]; omega),
              set_append_left (by
                rw [List.length_set, bubbleState_length hjp]; omega)]
            exact congrArg (· ++ suffix)
              (bubbleState_swap (by omega) hjp)
          rw [hsurg] at hstep2
          have hSD := isort_segSD_raw n (bubbleState p v jj ++ suffix) ivv
            ((jj + 1 : Nat) : Int) ch
          -- the next dispatch: j := j - 1, first conjunct delivered
          have hI1 := isort_segI1_raw n (bubbleState p v jj ++ suffix) ivv
            ((jj + 1 : Nat) : Int) ch
          rw [show (((jj + 1 : Nat) : Int) - 1) = ((jj : Nat) : Int) from by
              omega,
            inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega),
            inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega)]
            at hI1
          -- recurse
          obtain ⟨k, jex, hk, hjex, hrec⟩ := ih jj (by omega) jj rfl
            (by omega)
            (fun k hk hk' => by
              rcases Nat.eq_or_lt_of_le hk with rfl | hlt
              · exact hcmp
              · exact hinv k (by omega) hk') ch
          refine ⟨92 + k, jex, by omega, hjex, ?_⟩
          have h62 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
            (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
              (stepFnIter_chain (stepFnIter_chain h19 hSA)
                (stepFnIter_one hgetj)) hSB) (stepFnIter_one hgetj1))
              hSC) (stepFnIter_one hstep1)) (stepFnIter_one hstep2)) hSD
          exact stepFnIter_chain (stepFnIter_chain h62 hI1) hrec
        · -- the element test fails: exit with the insertion complete
          rw [decide_eq_false hcmp] at h19
          rw [← bubbleState_exit hsort (by omega)
            (.inr (Int.not_lt.mp hcmp)) hinv]
          have hX1 := isort_exitI_raw n (bubbleState p v (jj + 1) ++ suffix)
            ivv ((jj + 1 : Nat) : Int) ch
          exact ⟨28, jj + 1, by omega, by omega, stepFnIter_chain h19 hX1⟩

/-! ## One canonical pass, composed -/

/-- **One outer pass at the tight placement** (outer test true at the
4-cell state → the NEXT outer test delivery at the 6-cell state): the
pass allocates `j`/`$forFirst` at 4/5, bubbles `v` into the sorted
prefix `p` (the inner induction), and the following outer dispatch
advances `i`. `jex` is the retired inner counter's final value. -/
private theorem pass_seg (n : Nat) (p suffix : List Int) (v : Int) (m : Nat)
    (hn : n < 2 ^ 63)
    (hplen : p.length = m + 1)
    (hlen : p.length + 1 + suffix.length = n)
    (hsort : Sorted p)
    (hrp : ∀ x ∈ p, 0 ≤ x ∧ x < 2 ^ 64)
    (hrv : 0 ≤ v ∧ v < 2 ^ 64)
    (hrs : ∀ x ∈ suffix, 0 ≤ x ∧ x < 2 ^ 64)
    (ch : Choices) :
    ∃ (k jex : Nat), k ≤ 92 * n + 118 ∧ jex ≤ m + 1 ∧
      stepFnIter k (σOut n (p ++ v :: suffix) ((m + 1 : Nat) : Int) false)
        (.retV (.bool true) outerCmpCont) ch
        = .ok (.retV (.bool (decide
              (((m + 2 : Nat) : Int) < ((n : Nat) : Int)))) outerCmpCont,
            σIn n (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
              ((jex : Nat) : Int) false, ch) := by
  have hm1n : m + 2 ≤ n := by omega
  -- pass entry: allocate j := i and the inner $forFirst
  have hPA := isort_segPA_raw n (p ++ v :: suffix) ((m + 1 : Nat) : Int) ch
  rw [inorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)]
    at hPA
  -- first inner dispatch
  have hI0 := isort_segI0_raw n (p ++ v :: suffix) ((m + 1 : Nat) : Int)
    ((m + 1 : Nat) : Int) ch
  -- the inner loop, from j = i = p.length
  have hbub : bubbleState p v (m + 1) ++ suffix = p ++ v :: suffix := by
    rw [← hplen, bubbleState_full, List.append_assoc]
    rfl
  obtain ⟨kin, jex, hkin, hjex, hrun⟩ := inner_loop n ((m + 1 : Nat) : Int)
    p suffix v hn hlen hsort hrp hrv hrs (m + 1) (m + 1) rfl (by omega)
    (fun k hk hk' => by omega) ch
  rw [hbub] at hrun
  -- next outer dispatch (6-cell state; tail-parametric raw segment)
  have hO1 : stepFnIter 29
      (σIn n (insertSpec v p ++ suffix) ((m + 1 : Nat) : Int)
        ((jex : Nat) : Int) false) outerHeadCfg ch
      = .ok (.retV (sliceH n)
            (lenTestK (IntKind.normalize .int (IntKind.normalize .int
              (((m + 1 : Nat) : Int) + 1)))),
          σIn n (insertSpec v p ++ suffix)
            (IntKind.normalize .int (IntKind.normalize .int
              (((m + 1 : Nat) : Int) + 1)))
            ((jex : Nat) : Int) false, ch) :=
    isort_segO1_raw n (insertSpec v p ++ suffix) ((m + 1 : Nat) : Int)
      [(.base ⟨4⟩, intcell ((jex : Nat) : Int)), (.base ⟨5⟩, bcell false)]
      6 ch
  rw [show (((m + 1 : Nat) : Int) + 1) = ((m + 2 : Nat) : Int) from by omega,
    inorm_of_range (v := ((m + 2 : Nat) : Int)) (by omega) (by omega),
    inorm_of_range (v := ((m + 2 : Nat) : Int)) (by omega) (by omega)]
    at hO1
  -- the len(s) apply
  have hlenapp : stepFn
      (σIn n (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
        ((jex : Nat) : Int) false)
      (.retV (sliceH n) (lenTestK ((m + 2 : Nat) : Int))) ch
      = .ok (.retV (.int ((n : Nat) : Int) .int)
          (.strictK .lessCmp [.int ((m + 2 : Nat) : Int) .int] []
            ([] :: envO) outerCmpCont),
        σIn n (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
          ((jex : Nat) : Int) false, ch) :=
    stepFn_strict_apply (done := [])
      (applyStrictOp_len_slice (Nat.le_refl n))
  -- the comparison delivery
  have hOB : stepFnIter 1
      (σIn n (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
        ((jex : Nat) : Int) false)
      (.retV (.int ((n : Nat) : Int) .int)
        (.strictK .lessCmp [.int ((m + 2 : Nat) : Int) .int] []
          ([] :: envO) outerCmpCont)) ch
      = .ok (.retV (.bool (decide
            (((m + 2 : Nat) : Int) < ((n : Nat) : Int)))) outerCmpCont,
          σIn n (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
            ((jex : Nat) : Int) false, ch) :=
    isort_segOB_raw n (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
      [(.base ⟨4⟩, intcell ((jex : Nat) : Int)), (.base ⟨5⟩, bcell false)]
      6 ch
  refine ⟨33 + 26 + kin + 29 + 1 + 1, jex, by omega, by omega, ?_⟩
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain hPA hI0) hrun) hO1)
    (stepFnIter_one hlenapp)) hOB

/-! ## The per-pass frame layer

The machine re-allocates `j`/`$forFirst` on EVERY outer pass (fresh
addresses; the dead pair stays in the heap). The outer induction
therefore relates the true run to the tight canonical states through
the executable frame theorem: `ρsh d` fixes the four active cells and
shifts the pass-local region by the accumulated garbage `d = 2m`;
after each pass `rebaseSim` retires the pass's two cells INTO the
frame. -/

open GoLean.Frame

/-- The per-pass shift: identity on the active cells `0..3`, shift by
`d` on the pass-local region. -/
private def ρsh (d : Nat) : Nat → Nat := fun x => if x < 4 then x else x + d

private theorem ρsh_lt {d a : Nat} (h : a < 4) : ρsh d a = a := if_pos h
private theorem ρsh_ge {d a : Nat} (h : 4 ≤ a) : ρsh d a = a + d :=
  if_neg (by omega)

private theorem shiftSpec_ρsh (d : Nat) : ShiftSpec (ρsh d) 4 (4 + d) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    simp only [ρsh] at hxy
    split at hxy <;> split at hxy <;> omega
  · intro k
    simp only [ρsh]
    rw [if_neg (by omega)]
    omega

private theorem renCell_arr (ρ : Nat → Nat) (n : Nat) (l : List Int) :
    renameCell ρ (arrCell n l) = arrCell n l := by
  simp [renameCell, renameValue_locFree _ _ (locSup_mapU l)]

private theorem renCell_handle (d n : Nat) :
    renameCell (ρsh d) (handleCell n) = handleCell n := by
  simp [renameCell, renameValue, renameLoc, ρsh]

private theorem base_ne {x y : Nat} (h : x ≠ y) :
    (Loc.base ⟨x⟩ : Loc) ≠ .base ⟨y⟩ := by
  intro hc
  simp only [Loc.base.injEq, Addr.mk.injEq] at hc
  exact h hc

/-- Lookup distributes over heap append. -/
private theorem lookup_append (h1 h2 : Heap) (l : Loc) :
    Heap.lookup (h1 ++ h2) l
      = match Heap.lookup h1 l with
        | some c => some c
        | none => Heap.lookup h2 l := by
  induction h1 with
  | nil => simp [Heap.lookup]
  | cons p rest ih =>
      obtain ⟨k, c⟩ := p
      simp only [List.cons_append, Heap.lookup]
      split <;> simp [ih]

private theorem lookup_σOut_ge {n : Nat} {l : List Int} {iv : Int}
    {ffv : Bool} {a : Nat} (ha : 4 ≤ a) :
    Heap.lookup (σOut n l iv ffv).heap (.base ⟨a⟩) = none := by
  simp [σOut, σOutT, Heap.lookup,
    beq_false_of_ne (base_ne (show (0 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (1 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (2 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (3 : Nat) ≠ a by omega))]

private theorem lookup_σIn_ge {n : Nat} {l : List Int} {iv jv : Int}
    {ffIv : Bool} {a : Nat} (ha : 6 ≤ a) :
    Heap.lookup (σIn n l iv jv ffIv).heap (.base ⟨a⟩) = none := by
  simp [σIn, σOutT, Heap.lookup,
    beq_false_of_ne (base_ne (show (0 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (1 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (2 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (3 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (4 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (5 : Nat) ≠ a by omega))]

private theorem lookup_σOut_field (n : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) (b : Loc) (tid : TypeId) (f : String) :
    Heap.lookup (σOut n l iv ffv).heap (.field b tid f) = none := rfl

private theorem lookup_σOut_index (n : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) (b : Loc) (i : Int) :
    Heap.lookup (σOut n l iv ffv).heap (.index b i) = none := rfl

private theorem lookup_σIn_field (n : Nat) (l : List Int) (iv jv : Int)
    (ffIv : Bool) (b : Loc) (tid : TypeId) (f : String) :
    Heap.lookup (σIn n l iv jv ffIv).heap (.field b tid f) = none := rfl

private theorem lookup_σIn_index (n : Nat) (l : List Int) (iv jv : Int)
    (ffIv : Bool) (b : Loc) (i : Int) :
    Heap.lookup (σIn n l iv jv ffIv).heap (.index b i) = none := rfl

/-- The function table carries no address literals (`by decide` over
the pinned lowering), so every `ρ` fixes the bodies. -/
private theorem bodies_ρsh (ρ : Nat → Nat) :
    ∀ f ∈ (σOutT 0 [] 0 false [] 0).functions.toList,
      renameStmt ρ f.body = f.body :=
  renameBodies_id (n := 0) (fun x hx => absurd hx (Nat.not_lt_zero x))
    (by decide : funcListSup isortLowered.funcs.toList ≤ 0)

/-- Root bump by 2 above the active cells: the transport between
consecutive shifts (`ρsh (d+2) l = ρsh d (bump2 l)` on locations). -/
private def bump2 : Loc → Loc
  | .base a => .base ⟨if a.id < 4 then a.id else a.id + 2⟩
  | .field b tid f => .field (bump2 b) tid f
  | .index b i => .index (bump2 b) i

private theorem renameLoc_bump2 (d : Nat) (l : Loc) :
    renameLoc (ρsh (d + 2)) l = renameLoc (ρsh d) (bump2 l) := by
  induction l with
  | base a =>
      have h : ρsh (d + 2) a.id = ρsh d (if a.id < 4 then a.id else a.id + 2) := by
        by_cases ha : a.id < 4
        · rw [if_pos ha, ρsh_lt ha, ρsh_lt ha]
        · rw [if_neg ha, ρsh_ge (d := d + 2) (a := a.id) (by omega),
            ρsh_ge (d := d) (a := a.id + 2) (by omega)]
          omega
      simp only [renameLoc, bump2, h]
  | field b tid f ih => simp only [renameLoc, bump2, ih]
  | index b i ih => simp only [renameLoc, bump2, ih]

/-- The trivial-frame simulation at the loop entry (`m = 0`: the true
state IS the tight state). -/
private theorem frameSim_zero (n : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) :
    FrameSim (ρsh 0) 4 4 [] (σOut n l iv ffv) (σOut n l iv ffv) := by
  refine ⟨shiftSpec_ρsh 0, rfl, rfl, rfl, rfl, rfl, Nat.le_refl 4,
    ?_, ?_, fun a => rfl, bodies_ρsh (ρsh 0)⟩
  · intro loc
    match loc with
    | .base ⟨a⟩ =>
        match a with
        | 0 =>
            show Heap.lookup (σOut n l iv ffv).heap (.base ⟨ρsh 0 0⟩)
              = some (renameCell (ρsh 0) (arrCell n l))
            rw [renCell_arr]
            rfl
        | 1 =>
            show Heap.lookup (σOut n l iv ffv).heap (.base ⟨ρsh 0 1⟩)
              = some (renameCell (ρsh 0) (handleCell n))
            rw [renCell_handle 0 n]
            rfl
        | 2 => rfl
        | 3 => rfl
        | (a + 4) =>
            show Heap.lookup (σOut n l iv ffv).heap (.base ⟨ρsh 0 (a + 4)⟩)
              = _
            rw [ρsh_ge (d := 0) (a := a + 4) (by omega)]
            rw [lookup_σOut_ge (a := a + 4 + 0) (by omega)]
            rfl
    | .field b tid f => rfl
    | .index b i => rfl
  · intro loc c hc
    simp [Heap.lookup] at hc

private theorem fs_lookup_none {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (h : FrameSim ρ na₀ na fr σ σF) {l : Loc}
    (hl : Heap.lookup σ.heap l = none) :
    Heap.lookup σF.heap (renameLoc ρ l) = Heap.lookup fr (renameLoc ρ l) := by
  have h2 := h.lookup_img l
  rw [hl] at h2
  exact h2

/-- **The frame REBASE** (the outer induction's between-passes step):
the pass's retired `j`/`$forFirst` cells (canonical addresses 4/5) move
INTO the frame at their true addresses `4+d`/`5+d`, the shift widens by
2, and the canonical state drops back to the tight 4-cell shape. The
true state `σA` is untouched — this is pure re-description. -/
private theorem rebaseSim {d : Nat} {fr : Heap} {n : Nat} {l : List Int}
    {iv jv : Int} {σA : ExecState}
    (h : FrameSim (ρsh d) 4 (4 + d) fr (σIn n l iv jv false) σA) :
    FrameSim (ρsh (d + 2)) 4 (4 + (d + 2))
      (fr ++ [(.base ⟨4 + d⟩, intcell jv), (.base ⟨5 + d⟩, bcell false)])
      (σOut n l iv false) σA := by
  refine ⟨shiftSpec_ρsh (d + 2), h.types_eq, h.funcs_eq, h.methods_eq,
    h.methodSets_eq, ?_, Nat.le_refl 4, ?_, ?_, ?_, bodies_ρsh _⟩
  · -- next_eq
    have hne := h.next_eq
    rw [show (σIn n l iv jv false).nextAddr = 6 from rfl,
      ρsh_ge (d := d) (a := 6) (by omega)] at hne
    show σA.nextAddr = ρsh (d + 2) 4
    rw [ρsh_ge (d := d + 2) (a := 4) (by omega)]
    omega
  · -- lookup_img
    intro loc
    match loc with
    | .base ⟨a⟩ =>
        by_cases ha : a < 4
        · rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3)
            with rfl | rfl | rfl | rfl
          · have himg := h.lookup_some (l := .base ⟨0⟩) (c := arrCell n l) rfl
            rw [renCell_arr] at himg
            show Heap.lookup σA.heap (.base ⟨ρsh (d + 2) 0⟩)
              = some (renameCell (ρsh (d + 2)) (arrCell n l))
            rw [renCell_arr]
            exact himg
          · exact h.lookup_some (l := .base ⟨1⟩) (c := handleCell n) rfl
          · exact h.lookup_some (l := .base ⟨2⟩) (c := intcell iv) rfl
          · exact h.lookup_some (l := .base ⟨3⟩) (c := bcell false) rfl
        · have himg := fs_lookup_none h (l := .base ⟨a + 2⟩)
            (lookup_σIn_ge (by omega))
          have hren1 : renameLoc (ρsh d) (.base ⟨a + 2⟩)
              = .base ⟨a + 2 + d⟩ := by
            simp [renameLoc, ρsh_ge (d := d) (a := a + 2) (by omega)]
          rw [hren1] at himg
          have hren2 : renameLoc (ρsh (d + 2)) (.base ⟨a⟩)
              = .base ⟨a + (d + 2)⟩ := by
            simp [renameLoc, ρsh_ge (d := d + 2) (a := a) (by omega)]
          rw [hren2, lookup_σOut_ge (by omega)]
          show Heap.lookup σA.heap (.base ⟨a + (d + 2)⟩)
            = Heap.lookup (fr ++ [(.base ⟨4 + d⟩, intcell jv),
                (.base ⟨5 + d⟩, bcell false)]) (.base ⟨a + (d + 2)⟩)
          rw [show a + (d + 2) = a + 2 + d from by omega, himg,
            lookup_append]
          cases hfr : Heap.lookup fr (.base ⟨a + 2 + d⟩) with
          | some c => rfl
          | none =>
              show (none : Option HeapCell)
                = Heap.lookup [(.base ⟨4 + d⟩, intcell jv),
                    (.base ⟨5 + d⟩, bcell false)] (.base ⟨a + 2 + d⟩)
              simp [Heap.lookup,
                beq_false_of_ne (base_ne (show 4 + d ≠ a + 2 + d by omega)),
                beq_false_of_ne (base_ne (show 5 + d ≠ a + 2 + d by omega))]
    | .field b tid f =>
        have himg := fs_lookup_none h (l := bump2 (.field b tid f))
          (lookup_σIn_field n l iv jv false (bump2 b) tid f)
        rw [← renameLoc_bump2] at himg
        show Heap.lookup σA.heap (renameLoc (ρsh (d + 2)) (.field b tid f))
          = Heap.lookup (fr ++ [(.base ⟨4 + d⟩, intcell jv),
              (.base ⟨5 + d⟩, bcell false)])
            (renameLoc (ρsh (d + 2)) (.field b tid f))
        rw [himg, lookup_append]
        cases hfr : Heap.lookup fr
            (renameLoc (ρsh (d + 2)) (.field b tid f)) with
        | some c => rfl
        | none => rfl
    | .index b i =>
        have himg := fs_lookup_none h (l := bump2 (.index b i))
          (lookup_σIn_index n l iv jv false (bump2 b) i)
        rw [← renameLoc_bump2] at himg
        show Heap.lookup σA.heap (renameLoc (ρsh (d + 2)) (.index b i))
          = Heap.lookup (fr ++ [(.base ⟨4 + d⟩, intcell jv),
              (.base ⟨5 + d⟩, bcell false)])
            (renameLoc (ρsh (d + 2)) (.index b i))
        rw [himg, lookup_append]
        cases hfr : Heap.lookup fr
            (renameLoc (ρsh (d + 2)) (.index b i)) with
        | some c => rfl
        | none => rfl
  · -- frame_pres
    intro loc c hc
    rw [lookup_append] at hc
    cases hfr : Heap.lookup fr loc with
    | some c0 =>
        rw [hfr] at hc
        have hc' : some c0 = some c := hc
        injection hc' with hcc
        exact hcc ▸ h.frame_pres loc c0 hfr
    | none =>
        rw [hfr] at hc
        have hc' : Heap.lookup [(.base ⟨4 + d⟩, intcell jv),
            (.base ⟨5 + d⟩, bcell false)] loc = some c := hc
        by_cases h4 : (.base ⟨4 + d⟩ : Loc) = loc
        · subst h4
          have hcell : c = intcell jv := by
            simp [Heap.lookup] at hc'
            exact hc'.symm
          subst hcell
          exact h.lookup_some (l := .base ⟨4⟩) (c := intcell jv) rfl
        · by_cases h5 : (.base ⟨5 + d⟩ : Loc) = loc
          · subst h5
            have hcell : c = bcell false := by
              simp [Heap.lookup, beq_false_of_ne h4] at hc'
              exact hc'.symm
            subst hcell
            exact h.lookup_some (l := .base ⟨5⟩) (c := bcell false) rfl
          · exfalso
            simp [Heap.lookup, beq_false_of_ne h4, beq_false_of_ne h5] at hc'
  · -- fr_avoid
    intro a
    rw [lookup_append]
    by_cases ha : a < 4
    · rw [ρsh_lt ha]
      have h2 := h.fr_avoid a
      rw [ρsh_lt ha] at h2
      rw [h2]
      show Heap.lookup [(.base ⟨4 + d⟩, intcell jv),
          (.base ⟨5 + d⟩, bcell false)] (.base ⟨a⟩) = none
      simp [Heap.lookup,
        beq_false_of_ne (base_ne (show 4 + d ≠ a by omega)),
        beq_false_of_ne (base_ne (show 5 + d ≠ a by omega))]
    · rw [ρsh_ge (d := d + 2) (a := a) (by omega)]
      have h2 := h.fr_avoid (a + 2)
      rw [ρsh_ge (d := d) (a := a + 2) (by omega)] at h2
      rw [show a + (d + 2) = a + 2 + d from by omega, h2]
      show Heap.lookup [(.base ⟨4 + d⟩, intcell jv),
          (.base ⟨5 + d⟩, bcell false)] (.base ⟨a + 2 + d⟩) = none
      simp [Heap.lookup,
        beq_false_of_ne (base_ne (show 4 + d ≠ a + 2 + d by omega)),
        beq_false_of_ne (base_ne (show 5 + d ≠ a + 2 + d by omega))]

/-! ## Transfer plumbing: the shift fixes every anchor configuration
(all mentioned addresses are the active cells 0–3) -/

private theorem renCfg_cmp (d : Nat) (b : Bool) :
    renameConfig (ρsh d) (.retV (.bool b) outerCmpCont)
      = .retV (.bool b) outerCmpCont := by
  with_unfolding_all rfl

private theorem renCfg_stop (d : Nat) :
    renameConfig (ρsh d) (.next .stop) = .next .stop := rfl

/-- A canonical segment between shift-fixed configurations transfers to
the true placement: same fuel, same stream, related terminal states. -/
private theorem transfer_seg {d : Nat} {fr : Heap} {σC σC' σA : ExecState}
    {c c' : Config} {k : Nat} {ch : Choices}
    (hFS : FrameSim (ρsh d) 4 (4 + d) fr σC σA)
    (hrun : stepFnIter k σC c ch = .ok (c', σC', ch))
    (hc : renameConfig (ρsh d) c = c) (hc' : renameConfig (ρsh d) c' = c') :
    ∃ σA', stepFnIter k σA c ch = .ok (c', σA', ch)
      ∧ FrameSim (ρsh d) 4 (4 + d) fr σC' σA' := by
  have hsim := stepFnIter_sim k hFS c ch
  rw [hc] at hsim
  obtain ⟨rF, hrunF, htrip⟩ := hsim.ok_inv hrun
  obtain ⟨cF, σF, chF⟩ := rF
  obtain ⟨h1, h2, h3⟩ := htrip
  dsimp only at h1 h2 h3
  rw [h1, hc'] at hrunF
  rw [h3] at hrunF
  exact ⟨σF, hrunF, h2⟩

/-! ## The OUTER induction (arc design: plain strong induction on the
remaining passes, invariant `sortPrefix` — with each pass transferred
from the tight placement through the frame theorem and rebased) -/

/-- **The outer loop over the true (garbage-laden) run**: from the
outer test delivery after `m` passes — the true state `σA` related to
the tight `sortPrefix` state by the accumulated-garbage frame — the run
reaches the driver terminal with the backing cell fully sorted. -/
private theorem isort_loop (xs : List Int) (n : Nat) (hn : n = xs.length)
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (h63 : n < 2 ^ 63) :
    ∀ μ m (σA : ExecState) (fr : Heap), μ = n - (m + 1) →
    FrameSim (ρsh (2 * m)) 4 (4 + 2 * m) fr
      (σOut n (sortPrefix xs (m + 1)) ((m + 1 : Nat) : Int) false) σA →
    ∀ ch : Choices, ∃ (k : Nat) (σf : ExecState),
      k ≤ (92 * n + 160) * μ + 10 ∧
      stepFnIter k σA
        (.retV (.bool (decide (((m + 1 : Nat) : Int) < ((n : Nat) : Int))))
          outerCmpCont) ch
        = .ok (.next .stop, σf, ch)
      ∧ Heap.lookup σf.heap (.base ⟨0⟩)
          = some (arrCell n (sortSpec xs)) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m σA fr hμ hFS ch
    subst hμ
    rcases Nat.lt_or_ge (m + 1) n with hlt | hge
    · -- iterate: one more pass
      rw [show (decide (((m + 1 : Nat) : Int) < ((n : Nat) : Int))) = true
        from decide_eq_true (by omega)]
      have hplen : (sortSpec (xs.take (m + 1))).length = m + 1 := by
        rw [sortSpec_length, List.length_take]
        omega
      obtain ⟨K, jex, hK, hjex, hpass⟩ := pass_seg n
        (sortSpec (xs.take (m + 1))) (xs.drop (m + 2)) (xs.getD (m + 1) 0)
        m h63 hplen (by rw [hplen, List.length_drop]; omega)
        (sortSpec_sorted _)
        (fun x hx => hxs x (List.mem_of_mem_take (mem_sortSpec hx)))
        (hxs _ (getD_mem (by omega)))
        (fun x hx => hxs x (List.mem_of_mem_drop hx)) ch
      rw [← sortPrefix_decomp (by omega)] at hpass
      have hnext : sortPrefix xs (m + 2)
          = insertSpec (xs.getD (m + 1) 0) (sortSpec (xs.take (m + 1)))
            ++ xs.drop (m + 2) := by
        rw [sortPrefix]
        congr 1
        exact sortSpec_take_succ (k := m + 1) (by omega)
      rw [← hnext] at hpass
      obtain ⟨σA', hrunA, hFS'⟩ := transfer_seg hFS hpass
        (renCfg_cmp (2 * m) true) (renCfg_cmp (2 * m) _)
      have hFS2 := rebaseSim hFS'
      obtain ⟨k, σf, hk, hrun, hread⟩ := ih (n - (m + 2)) (by omega) (m + 1)
        σA' (fr ++ [(.base ⟨4 + 2 * m⟩, intcell ((jex : Nat) : Int)),
          (.base ⟨5 + 2 * m⟩, bcell false)]) rfl hFS2 ch
      refine ⟨K + k, σf, ?_, stepFnIter_chain hrunA hrun, hread⟩
      have hmul : (92 * n + 160) * (n - (m + 2)) + (92 * n + 160)
          = (92 * n + 160) * (n - (m + 1)) := by
        rw [← Nat.mul_succ]
        congr 1
        omega
      omega
    · -- exit
      rw [show (decide (((m + 1 : Nat) : Int) < ((n : Nat) : Int))) = false
        from decide_eq_false (by omega)]
      have hX := isort_exitO_raw n (sortPrefix xs (m + 1))
        ((m + 1 : Nat) : Int) [] 4 ch
      obtain ⟨σf, hrunA, hFS'⟩ := transfer_seg hFS hX
        (renCfg_cmp (2 * m) false) (renCfg_stop (2 * m))
      refine ⟨8, σf, by omega, hrunA, ?_⟩
      have hread := hFS'.lookup_some (l := .base ⟨0⟩)
        (c := arrCell n (sortPrefix xs (m + 1))) rfl
      rw [renCell_arr, sortPrefix_full (by omega)] at hread
      exact hread

/-! ## The canonical run, end to end -/

private theorem lookup_seed (xs : List Int) :
    Heap.lookup (isortSeed xs 0 [] 1).heap (.base ⟨0⟩)
      = some ⟨some (.array xs.length (.int .uint64)),
          .array ⟨xs.map (fun v => .int v .uint64)⟩⟩ := by
  simp [isortSeed, sliceCells, Heap.lookup]

/-- **The canonical run**: from the tight seed the driver completes at
the `.normal` terminal within `76 + (92·len + 160)·len` steps, with the
backing cell holding `sortSpec xs`. -/
private theorem isort_runs (xs : List Int)
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (hlen : xs.length < 2 ^ 63)
    (ch : Choices) :
    ∃ (k : Nat) (σf : ExecState),
      k ≤ 76 + (92 * xs.length + 160) * xs.length ∧
      stepFnIter k (isortSeed xs 0 [] 1)
        (.exec (isortCall xs 0) [] .stop) ch
        = .ok (.next .stop, σf, ch)
      ∧ Heap.lookup σf.heap (.base ⟨0⟩)
          = some (arrCell xs.length (sortSpec xs)) := by
  -- entry: driver → outer head
  have hA := isort_entryA_raw xs ch
  rw [inorm_nat_of_lt hlen] at hA
  have happ1 : applyStrictOp (isortSeed xs 0 [] 1) (.sliceExpr false)
      [.addr (.base ⟨0⟩), .int 0 .int, .int ((xs.length : Nat) : Int) .int]
      = .ok (sliceH xs.length, isortSeed xs 0 [] 1) :=
    applyStrictOp_sliceExpr_array (lookup_seed xs) (by simp)
  have hB := isort_entryB_raw xs ch
  have h8 := stepFnIter_chain hA
    (stepFnIter_one
      (stepFn_strict_apply (done := [.int 0 .int, .addr (.base ⟨0⟩)]) happ1))
  have h39 := stepFnIter_chain h8 hB
  -- first outer dispatch + test (tight 4-cell state)
  have hO0 := isort_segO0_raw xs.length xs 1 [] 4 ch
  have hlenapp : stepFn (σOutT xs.length xs 1 false [] 4)
      (.retV (sliceH xs.length) (lenTestK 1)) ch
      = .ok (.retV (.int ((xs.length : Nat) : Int) .int)
          (.strictK .lessCmp [.int 1 .int] [] ([] :: envO) outerCmpCont),
        σOutT xs.length xs 1 false [] 4, ch) :=
    stepFn_strict_apply (done := [])
      (applyStrictOp_len_slice (Nat.le_refl xs.length))
  have hOB := isort_segOB_raw xs.length xs 1 [] 4 ch
  have h66 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h39 hO0)
    (stepFnIter_one hlenapp)) hOB
  -- the outer loop from m = 0 (trivial frame: true state = tight state)
  have hFS0 : FrameSim (ρsh (2 * 0)) 4 (4 + 2 * 0) []
      (σOut xs.length (sortPrefix xs (0 + 1)) ((0 + 1 : Nat) : Int) false)
      (σOut xs.length xs 1 false) := by
    show FrameSim (ρsh 0) 4 4 []
      (σOut xs.length (sortPrefix xs 1) ((1 : Nat) : Int) false)
      (σOut xs.length xs 1 false)
    rw [sortPrefix_one]
    show FrameSim (ρsh 0) 4 4 [] (σOut xs.length xs 1 false)
      (σOut xs.length xs 1 false)
    exact frameSim_zero _ _ _ _
  obtain ⟨k, σf, hk, hrun, hread⟩ := isort_loop xs xs.length rfl hxs hlen
    (xs.length - (0 + 1)) 0 (σOut xs.length xs 1 false) [] rfl hFS0 ch
  refine ⟨66 + k, σf, ?_, stepFnIter_chain h66 hrun, hread⟩
  have hmono : (92 * xs.length + 160) * (xs.length - (0 + 1))
      ≤ (92 * xs.length + 160) * xs.length :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- **Total correctness at the canonical placement**: past fuel
`76 + (92·len + 160)·len`, at every choice stream, execution completes
normally with the sorted permutation in the backing cell. -/
private theorem isort_total_canonical (xs : List Int)
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (hlen : xs.length < 2 ^ 63) :
    ∀ fuel : Nat, 76 + (92 * xs.length + 160) * xs.length ≤ fuel →
    ∀ ch : Choices, ∃ σf : ExecState,
      execStmtLoop fuel (isortSeed xs 0 [] 1)
        (.exec (isortCall xs 0) [] .stop) ch = .ok (.normal σf, ch)
      ∧ Heap.lookup σf.heap (.base ⟨0⟩)
          = some (arrCell xs.length (sortSpec xs)) := by
  intro fuel hfuel ch
  obtain ⟨k, σf, hk, hrun, hread⟩ := isort_runs xs hxs hlen ch
  refine ⟨σf, ?_, hread⟩
  have hfold := execStmtLoop_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [hfold, execStmtLoop_next_stop]

/-! ## The framed form: the frame theorem consumed at an
input-RELOCATING renaming (reverse's layer, verbatim-adapted) -/

/-- The input-relocating renaming: `0 ↦ base`, `1 + k ↦ na + k`. -/
private def relocShift (base na : Nat) : Nat → Nat :=
  fun x => if x = 0 then base else na + (x - 1)

/-- The seed simulation: the canonical seed beside the framed seed at
an arbitrary placement, through the relocating shift. -/
private theorem isortSeedFrameSim (xs : List Int) (base : Nat) (fr : Heap)
    (na : Nat)
    (hb : Heap.lookup fr (.base ⟨base⟩) = none)
    (hwf : MachineWf
      { functions := isortLowered.funcs,
        heap := sliceCells xs base ++ fr, nextAddr := na }
      (.exec (isortCall xs base) [] .stop)) :
    FrameSim (relocShift base na) 1 na fr (isortSeed xs 0 [] 1)
      (isortSeed xs base fr na) := by
  have hs := hwf.1
  simp only [StateWf, ExecState.locSup, Heap.locSup, sliceCells,
    List.cons_append, List.nil_append, Loc.locSup, Loc.rootBase,
    Nat.max_le] at hs
  have hbase : base + 1 ≤ na := hs.1.1.1
  have hfrsup : Heap.locSup fr ≤ na := hs.1.2
  have hren0 : renameLoc (relocShift base na) (.base ⟨0⟩) = .base ⟨base⟩ := by
    simp [renameLoc, relocShift]
  have hcellid : renameCell (relocShift base na)
      (⟨some (.array xs.length (.int .uint64)),
        .array ⟨xs.map (fun v => .int v .uint64)⟩⟩ : HeapCell)
      = ⟨some (.array xs.length (.int .uint64)),
         .array ⟨xs.map (fun v => .int v .uint64)⟩⟩ := by
    simp [renameCell, renameValue_locFree _ _ (locSup_mapU xs)]
  refine ⟨⟨?_, ?_⟩, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- inj
    intro x y hxy
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
      simp only [relocShift, hx, hy, if_pos, if_neg, if_true, if_false] at hxy <;>
      omega
  · -- shift
    intro k
    simp only [relocShift, if_neg (by omega : ¬ (1 + k = 0))]
    omega
  · -- next_eq: na = ρ 1
    simp [isortSeed, relocShift]
  · -- alloc_reg
    exact Nat.le_refl 1
  · -- lookup_img
    intro l
    by_cases hl : l = .base ⟨0⟩
    · subst hl
      rw [hren0]
      simp only [isortSeed, sliceCells, List.cons_append, List.nil_append,
        Heap.lookup]
      simp [hcellid]
    · have hcanon : Heap.lookup (isortSeed xs 0 [] 1).heap l = none := by
        have hne : ((.base ⟨0⟩ : Loc) == l) = false :=
          beq_false_of_ne (fun h => hl h.symm)
        simp [isortSeed, sliceCells, Heap.lookup, hne]
      rw [hcanon]
      have hne' : ((.base ⟨base⟩ : Loc) == renameLoc (relocShift base na) l)
          = false := by
        refine beq_false_of_ne (fun hc => ?_)
        cases l with
        | base a =>
            simp only [renameLoc, Loc.base.injEq, Addr.mk.injEq] at hc
            by_cases ha : a.id = 0
            · exact hl (by
                obtain ⟨id⟩ := a
                exact congrArg (fun n => Loc.base ⟨n⟩) ha)
            · simp only [relocShift, if_neg ha] at hc
              omega
        | field b tid f => simp [renameLoc] at hc
        | index b i => simp [renameLoc] at hc
      simp only [isortSeed, sliceCells, List.cons_append, List.nil_append,
        Heap.lookup, hne']
      rfl
  · -- frame_pres
    intro l c hl
    have hne : ((.base ⟨base⟩ : Loc) == l) = false := by
      refine beq_false_of_ne (fun hc => ?_)
      rw [← hc, hb] at hl
      cases hl
    simp only [isortSeed, sliceCells, List.cons_append, List.nil_append,
      Heap.lookup, hne]
    exact hl
  · -- fr_avoid
    intro a
    by_cases ha : a = 0
    · subst ha
      simpa [relocShift] using hb
    · cases hlk : Heap.lookup fr (.base ⟨relocShift base na a⟩) with
      | none => rfl
      | some c =>
          exfalso
          have hkey := Heap.lookup_key_locSup hlk
          simp only [Loc.locSup, Loc.rootBase] at hkey
          simp only [relocShift, if_neg ha] at hkey
          omega
  · -- bodies_inv
    exact renameBodies_id (n := 0) (fun x hx => absurd hx (Nat.not_lt_zero x))
      (fs := isortLowered.funcs)
      (by decide : funcListSup isortLowered.funcs.toList ≤ 0)

/-- The driver configuration renames to the framed driver: the
relocating shift carries the `locLit` base pointer to `base`. -/
private theorem isort_cfg_ren (xs : List Int) (base na : Nat) :
    renameConfig (relocShift base na)
      (.exec (isortCall xs 0) [] .stop)
      = .exec (isortCall xs base) [] .stop := by
  simp [renameConfig, renameCont, renameEnv, renameStmt, isortCall,
    renameExprList, renameExpr, renameOptExpr, renameLoc, relocShift]

/-! ## The memory-quantified form (proof-side supporting layer per §11;
the harness restatement is the recorded gap — module header) -/

/-- **The framed total form — proof-side supporting layer per §11 (the
memory-quantified form, kept; renamed from `isort_ok` when the harness
restatement below took that name, 2026-08-13)**: *for any list `xs` of
uint64 values, wherever it lives in memory, with anything else
present: `insertionSort` completes normally — past one fuel bound, at
every nondeterminism-choice stream — the backing cell then holds a
SORTED PERMUTATION of `xs` (`sortSpec xs`; `sortSpec_sorted`,
`sortSpec_count`, `sortSpec_length` make that reading a theorem), and
no other memory is touched.* The USER-FACING headline is `isort_ok`
below (harness ruling 2026-08-13, design note §11); this
memory-quantified form stays as the supporting layer — and it remains
the strongest ∀xs claim shipped (the harness headline quantifies the
input FAMILY `isFamily n seed`).

Statement deltas against the arc-design block: none beyond the
design's own (`hlen : xs.length < 2 ^ 63` — Go's `int` domain; the
driver's `len` literal wraps negative past it and the slice bounds
check panics, so the claim as drafted would be false there).

The proof: total correctness at the TIGHT canonical placement — two
plain nested strong inductions over direct machine-step segments (the
arc design), with each outer pass transferred through the executable
frame theorem at the accumulated-garbage shift `ρsh (2m)` and REBASED
(`rebaseSim`) because the machine re-allocates the inner `j`/`$forFirst`
pair every pass — then the frame theorem ONCE MORE at the
input-relocating renaming `relocShift base na` for the ∀-placement
∀-frame form. Nothing is re-run at any framed placement. -/
theorem isort_framed (xs : List Int) (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64)
    (hlen : xs.length < 2 ^ 63)
    (base : Nat) (fr : Heap) (na : Nat)
    (hb : Heap.lookup fr (.base ⟨base⟩) = none)
    (hwf : MachineWf
      { functions := isortLowered.funcs,
        heap := sliceCells xs base ++ fr, nextAddr := na }
      (.exec (isortCall xs base) [] .stop)) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel [] (isortSeed xs base fr na) ch (isortCall xs base)
          = .ok (.normal σf, ch')
        ∧ Heap.lookup σf.heap (.base ⟨base⟩)
            = some ⟨some (.array xs.length (.int .uint64)),
                .array ⟨(sortSpec xs).map (fun v => .int v .uint64)⟩⟩
        ∧ ∀ (a : Nat) (c : HeapCell),
            Heap.lookup fr (.base ⟨a⟩) = some c →
            Heap.lookup σf.heap (.base ⟨a⟩) = some c := by
  have hSF := isortSeedFrameSim xs base fr na hb hwf
  refine ⟨76 + (92 * xs.length + 160) * xs.length, fun fuel hfuel ch => ?_⟩
  obtain ⟨σc, hrunC, hreadC⟩ :=
    isort_total_canonical xs hxs hlen fuel hfuel ch
  obtain ⟨outF, hrunF, hout⟩ := Frame.execStmtLoop_ren fuel hSF hrunC
  rw [isort_cfg_ren xs base na] at hrunF
  cases outF with
  | normal σF =>
      obtain ⟨hSF', -⟩ := hout
      refine ⟨σF, ch, hrunF, ?_, ?_⟩
      · have hlook := hSF'.lookup_some hreadC
        have hren0 : renameLoc (relocShift base na) (.base ⟨0⟩)
            = .base ⟨base⟩ := by
          simp [renameLoc, relocShift]
        have hv : renameValue (relocShift base na)
            (.array ⟨(sortSpec xs).map (fun v => .int v .uint64)⟩)
            = .array ⟨(sortSpec xs).map (fun v => .int v .uint64)⟩ :=
          renameValue_locFree _ _ (locSup_mapU (sortSpec xs))
        have hcell : renameCell (relocShift base na)
            (⟨some (.array xs.length (.int .uint64)),
              .array ⟨(sortSpec xs).map (fun v => .int v .uint64)⟩⟩ : HeapCell)
            = ⟨some (.array xs.length (.int .uint64)),
               .array ⟨(sortSpec xs).map (fun v => .int v .uint64)⟩⟩ :=
          congrArg (HeapCell.mk (some (.array xs.length (.int .uint64)))) hv
        rw [hren0, hcell] at hlook
        exact hlook
      · intro a c hac
        exact hSF'.frame_pres (.base ⟨a⟩) c hac
  | returned σF => exact hout.elim
  | broke σF => exact hout.elim
  | continued σF => exact hout.elim

/-- **The D1 run-conditioned twin of the memory-quantified form**
(proof-side supporting layer per §11; renamed from `isort_readout`
with its total twin): any normal completion, at ANY fuel and stream,
delivers the sorted permutation and frame preservation — derived from
`isort_framed`, no second walk. -/
theorem isort_framed_readout (xs : List Int)
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (hlen : xs.length < 2 ^ 63)
    (base : Nat) (fr : Heap) (na : Nat)
    (hb : Heap.lookup fr (.base ⟨base⟩) = none)
    (hwf : MachineWf
      { functions := isortLowered.funcs,
        heap := sliceCells xs base ++ fr, nextAddr := na }
      (.exec (isortCall xs base) [] .stop)) :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel [] (isortSeed xs base fr na) ch (isortCall xs base)
        = .ok (.normal σf, ch') →
      Heap.lookup σf.heap (.base ⟨base⟩)
          = some ⟨some (.array xs.length (.int .uint64)),
              .array ⟨(sortSpec xs).map (fun v => .int v .uint64)⟩⟩
        ∧ ∀ (a : Nat) (c : HeapCell),
            Heap.lookup fr (.base ⟨a⟩) = some c →
            Heap.lookup σf.heap (.base ⟨a⟩) = some c :=
  normal_readout_of_total (isort_framed xs hxs hlen base fr na hb hwf)

/-! # Harness-form groundwork (ruling 2026-08-13, §11 — the recorded
gap's completed half; module header for the gap statement)

Harness address layout (probe `.tmp/his-probe1.lean`, n=4 seed=3):
0 = `n`, 1 = `seed`, 2 = the harness `$res0` (the VERDICT cell),
3 = `$c4` (make handle), 4 = the `s` BACKING, 5 = `s`, 6/7 = the setup
`i`/`$forFirst`; the subject frame: 8 = `s` param, 9 = the subject
`i`, 10 = the outer `$forFirst`, per-pass `j`/`$forFirst` pairs from
11; then the test phase: `ok`, the sortedness scan's `i`/`ff`,
`$c5`/the `t` BACKING/`t`, the rebuild `i`/`ff`, the count loops'
`i`/`ff` + per-pass `cs`/`ct`/`j`/`ff`. -/

/-- **The input family**: the wrapped multiplicative sequence the
harness's setup phase materializes — `isFamily n seed` has entries
`(seed * (i+1)) mod 2^64` as mathematical integers; the wrap is IN the
definition, so the family needs no no-wrap hypothesis (duplicates and
non-monotone orders are exactly the interesting sort inputs). -/
def isFamily (n seed : Nat) : List Int :=
  (List.range n).map (fun i => (((seed * (i + 1)) % 2 ^ 64 : Nat) : Int))

theorem isFamily_length (n seed : Nat) : (isFamily n seed).length = n := by
  simp [isFamily]

private theorem isFamily_range (n seed : Nat) :
    ∀ v ∈ isFamily n seed, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  simp only [isFamily, List.mem_map, List.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  have := Nat.mod_lt (seed * (i + 1)) (y := 2 ^ 64) (by omega)
  omega

private theorem isFamilyZ_range {n seed i : Nat} (_hin : i ≤ n) :
    ∀ v ∈ isFamily i seed ++ List.replicate (n - i) (0 : Int),
      0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact isFamily_range i seed v hv
  · rw [List.eq_of_mem_replicate hv]
    omega

/-- The one-step family extension the setup-loop invariant consumes. -/
private theorem isFamily_set {n seed i : Nat} (hi : i < n) :
    (isFamily i seed ++ List.replicate (n - i) 0).set i
        (((seed * (i + 1)) % 2 ^ 64 : Nat) : Int)
      = isFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0 := by
  have hrep : List.replicate (n - i) (0 : Int)
      = 0 :: List.replicate (n - (i + 1)) 0 := by
    rw [show n - i = (n - (i + 1)) + 1 from by omega, List.replicate_succ]
  have hfam : isFamily (i + 1) seed
      = isFamily i seed ++ [(((seed * (i + 1)) % 2 ^ 64 : Nat) : Int)] := by
    rw [isFamily, isFamily, List.range_succ, List.map_append]
    rfl
  rw [hrep, hfam, List.append_assoc]
  have hlen : (isFamily i seed).length = i := isFamily_length i seed
  rw [List.set_append_right _ _ (by omega), hlen, Nat.sub_self]
  rfl

/-- The uint64 normalization of a `Nat` cast IS the mod-2^64 wrap (the
family's own wrap — no range hypothesis). -/
private theorem unorm_nat_mod (m : Nat) :
    IntKind.normalize .uint64 ((m : Nat) : Int)
      = (((m % 2 ^ 64 : Nat)) : Int) := by
  simp [IntKind.normalize, IntKind.bits?, IntKind.signed]

/-- The harness's `Func` record, verbatim from the pinned lowering
(the `example` pin below ties it by `rfl`). -/
def isortHarnessFunc : Func :=
  { id := { key := "isort_harness" },
    args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
              { id := "seed", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
    results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
    body := GoLean.GoCore.Stmt.block
              #[]
              #[GoLean.GoCore.Stmt.seqn
                  #[GoLean.GoCore.Stmt.initialization
                      { id := "$c4",
                        typ := GoLean.GoCore.Ty.slice
                                 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                    GoLean.GoCore.Stmt.makeSlice
                      (GoLean.GoCore.Assignee.var "$c4")
                      (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                      (GoLean.GoCore.Expr.var "n")
                      none],
                GoLean.GoCore.Stmt.seqn
                  #[GoLean.GoCore.Stmt.initialization
                      { id := "s",
                        typ := GoLean.GoCore.Ty.slice
                                 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                    GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.var "s")
                      (GoLean.GoCore.Expr.var "$c4")],
                GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                        GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "i")
                          (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))],
                    GoLean.GoCore.Stmt.block
                      #[]
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "$forFirst", typ := GoLean.GoCore.Ty.bool },
                        GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "$forFirst")
                          (GoLean.GoCore.Expr.boolLit true),
                        GoLean.GoCore.Stmt.while
                          (GoLean.GoCore.Expr.boolLit true)
                          (GoLean.GoCore.Stmt.block
                            #[]
                            #[GoLean.GoCore.Stmt.ifThenElse
                                (GoLean.GoCore.Expr.var "$forFirst")
                                (GoLean.GoCore.Stmt.assign
                                  (GoLean.GoCore.Assignee.var "$forFirst")
                                  (GoLean.GoCore.Expr.boolLit false))
                                (GoLean.GoCore.Stmt.assign
                                  (GoLean.GoCore.Assignee.var "i")
                                  (GoLean.GoCore.Expr.add
                                    (GoLean.GoCore.Expr.var "i")
                                    (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)))),
                              GoLean.GoCore.Stmt.seqn #[],
                              GoLean.GoCore.Stmt.ifThenElse
                                (GoLean.GoCore.Expr.lessCmp
                                  (GoLean.GoCore.Expr.var "i")
                                  (GoLean.GoCore.Expr.var "n"))
                                (GoLean.GoCore.Stmt.seqn #[])
                                (GoLean.GoCore.Stmt.breakStmt),
                              GoLean.GoCore.Stmt.block
                                #[]
                                #[GoLean.GoCore.Stmt.seqn
                                    #[GoLean.GoCore.Stmt.assign
                                        (GoLean.GoCore.Assignee.addr
                                          (GoLean.GoCore.Expr.indexAddr
                                            (GoLean.GoCore.Expr.var "s")
                                            (GoLean.GoCore.Expr.var "i")))
                                        (GoLean.GoCore.Expr.mul
                                          (GoLean.GoCore.Expr.var "seed")
                                          (GoLean.GoCore.Expr.add
                                            (GoLean.GoCore.Expr.var "i")
                                            (GoLean.GoCore.Expr.intLit
                                              1
                                              (GoLean.GoCore.IntKind.uint64))))]]])]],
                GoLean.GoCore.Stmt.call #[] { key := "insertionSort" } #[GoLean.GoCore.Expr.var "s"],
                GoLean.GoCore.Stmt.seqn
                  #[GoLean.GoCore.Stmt.initialization
                      { id := "ok", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                    GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.var "ok")
                      (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64))],
                GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                        GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "i")
                          (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64))],
                    GoLean.GoCore.Stmt.block
                      #[]
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "$forFirst", typ := GoLean.GoCore.Ty.bool },
                        GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "$forFirst")
                          (GoLean.GoCore.Expr.boolLit true),
                        GoLean.GoCore.Stmt.while
                          (GoLean.GoCore.Expr.boolLit true)
                          (GoLean.GoCore.Stmt.block
                            #[]
                            #[GoLean.GoCore.Stmt.ifThenElse
                                (GoLean.GoCore.Expr.var "$forFirst")
                                (GoLean.GoCore.Stmt.assign
                                  (GoLean.GoCore.Assignee.var "$forFirst")
                                  (GoLean.GoCore.Expr.boolLit false))
                                (GoLean.GoCore.Stmt.assign
                                  (GoLean.GoCore.Assignee.var "i")
                                  (GoLean.GoCore.Expr.add
                                    (GoLean.GoCore.Expr.var "i")
                                    (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)))),
                              GoLean.GoCore.Stmt.seqn #[],
                              GoLean.GoCore.Stmt.ifThenElse
                                (GoLean.GoCore.Expr.lessCmp
                                  (GoLean.GoCore.Expr.var "i")
                                  (GoLean.GoCore.Expr.var "n"))
                                (GoLean.GoCore.Stmt.seqn #[])
                                (GoLean.GoCore.Stmt.breakStmt),
                              GoLean.GoCore.Stmt.block
                                #[]
                                #[GoLean.GoCore.Stmt.ifThenElse
                                    (GoLean.GoCore.Expr.greaterCmp
                                      (GoLean.GoCore.Expr.indexGet
                                        (GoLean.GoCore.Expr.var "s")
                                        (GoLean.GoCore.Expr.sub
                                          (GoLean.GoCore.Expr.var "i")
                                          (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64))))
                                      (GoLean.GoCore.Expr.indexGet
                                        (GoLean.GoCore.Expr.var "s")
                                        (GoLean.GoCore.Expr.var "i")))
                                    (GoLean.GoCore.Stmt.block
                                      #[]
                                      #[GoLean.GoCore.Stmt.seqn
                                          #[GoLean.GoCore.Stmt.assign
                                              (GoLean.GoCore.Assignee.var "ok")
                                              (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))]])
                                    (GoLean.GoCore.Stmt.seqn #[])]])]],
                GoLean.GoCore.Stmt.seqn
                  #[GoLean.GoCore.Stmt.initialization
                      { id := "$c5",
                        typ := GoLean.GoCore.Ty.slice
                                 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                    GoLean.GoCore.Stmt.makeSlice
                      (GoLean.GoCore.Assignee.var "$c5")
                      (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                      (GoLean.GoCore.Expr.var "n")
                      none],
                GoLean.GoCore.Stmt.seqn
                  #[GoLean.GoCore.Stmt.initialization
                      { id := "t",
                        typ := GoLean.GoCore.Ty.slice
                                 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                    GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.var "t")
                      (GoLean.GoCore.Expr.var "$c5")],
                GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                        GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "i")
                          (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))],
                    GoLean.GoCore.Stmt.block
                      #[]
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "$forFirst", typ := GoLean.GoCore.Ty.bool },
                        GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "$forFirst")
                          (GoLean.GoCore.Expr.boolLit true),
                        GoLean.GoCore.Stmt.while
                          (GoLean.GoCore.Expr.boolLit true)
                          (GoLean.GoCore.Stmt.block
                            #[]
                            #[GoLean.GoCore.Stmt.ifThenElse
                                (GoLean.GoCore.Expr.var "$forFirst")
                                (GoLean.GoCore.Stmt.assign
                                  (GoLean.GoCore.Assignee.var "$forFirst")
                                  (GoLean.GoCore.Expr.boolLit false))
                                (GoLean.GoCore.Stmt.assign
                                  (GoLean.GoCore.Assignee.var "i")
                                  (GoLean.GoCore.Expr.add
                                    (GoLean.GoCore.Expr.var "i")
                                    (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)))),
                              GoLean.GoCore.Stmt.seqn #[],
                              GoLean.GoCore.Stmt.ifThenElse
                                (GoLean.GoCore.Expr.lessCmp
                                  (GoLean.GoCore.Expr.var "i")
                                  (GoLean.GoCore.Expr.var "n"))
                                (GoLean.GoCore.Stmt.seqn #[])
                                (GoLean.GoCore.Stmt.breakStmt),
                              GoLean.GoCore.Stmt.block
                                #[]
                                #[GoLean.GoCore.Stmt.seqn
                                    #[GoLean.GoCore.Stmt.assign
                                        (GoLean.GoCore.Assignee.addr
                                          (GoLean.GoCore.Expr.indexAddr
                                            (GoLean.GoCore.Expr.var "t")
                                            (GoLean.GoCore.Expr.var "i")))
                                        (GoLean.GoCore.Expr.mul
                                          (GoLean.GoCore.Expr.var "seed")
                                          (GoLean.GoCore.Expr.add
                                            (GoLean.GoCore.Expr.var "i")
                                            (GoLean.GoCore.Expr.intLit
                                              1
                                              (GoLean.GoCore.IntKind.uint64))))]]])]],
                GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                        GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "i")
                          (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))],
                    GoLean.GoCore.Stmt.block
                      #[]
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "$forFirst", typ := GoLean.GoCore.Ty.bool },
                        GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "$forFirst")
                          (GoLean.GoCore.Expr.boolLit true),
                        GoLean.GoCore.Stmt.while
                          (GoLean.GoCore.Expr.boolLit true)
                          (GoLean.GoCore.Stmt.block
                            #[]
                            #[GoLean.GoCore.Stmt.ifThenElse
                                (GoLean.GoCore.Expr.var "$forFirst")
                                (GoLean.GoCore.Stmt.assign
                                  (GoLean.GoCore.Assignee.var "$forFirst")
                                  (GoLean.GoCore.Expr.boolLit false))
                                (GoLean.GoCore.Stmt.assign
                                  (GoLean.GoCore.Assignee.var "i")
                                  (GoLean.GoCore.Expr.add
                                    (GoLean.GoCore.Expr.var "i")
                                    (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)))),
                              GoLean.GoCore.Stmt.seqn #[],
                              GoLean.GoCore.Stmt.ifThenElse
                                (GoLean.GoCore.Expr.lessCmp
                                  (GoLean.GoCore.Expr.var "i")
                                  (GoLean.GoCore.Expr.var "n"))
                                (GoLean.GoCore.Stmt.seqn #[])
                                (GoLean.GoCore.Stmt.breakStmt),
                              GoLean.GoCore.Stmt.block
                                #[]
                                #[GoLean.GoCore.Stmt.seqn
                                    #[GoLean.GoCore.Stmt.initialization
                                        { id := "cs",
                                          typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                      GoLean.GoCore.Stmt.assign
                                        (GoLean.GoCore.Assignee.var "cs")
                                        (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))],
                                  GoLean.GoCore.Stmt.seqn
                                    #[GoLean.GoCore.Stmt.initialization
                                        { id := "ct",
                                          typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                      GoLean.GoCore.Stmt.assign
                                        (GoLean.GoCore.Assignee.var "ct")
                                        (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))],
                                  GoLean.GoCore.Stmt.block
                                    #[]
                                    #[GoLean.GoCore.Stmt.seqn
                                        #[GoLean.GoCore.Stmt.initialization
                                            { id := "j",
                                              typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                          GoLean.GoCore.Stmt.assign
                                            (GoLean.GoCore.Assignee.var "j")
                                            (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))],
                                      GoLean.GoCore.Stmt.block
                                        #[]
                                        #[GoLean.GoCore.Stmt.initialization
                                            { id := "$forFirst", typ := GoLean.GoCore.Ty.bool },
                                          GoLean.GoCore.Stmt.assign
                                            (GoLean.GoCore.Assignee.var "$forFirst")
                                            (GoLean.GoCore.Expr.boolLit true),
                                          GoLean.GoCore.Stmt.while
                                            (GoLean.GoCore.Expr.boolLit true)
                                            (GoLean.GoCore.Stmt.block
                                              #[]
                                              #[GoLean.GoCore.Stmt.ifThenElse
                                                  (GoLean.GoCore.Expr.var "$forFirst")
                                                  (GoLean.GoCore.Stmt.assign
                                                    (GoLean.GoCore.Assignee.var "$forFirst")
                                                    (GoLean.GoCore.Expr.boolLit false))
                                                  (GoLean.GoCore.Stmt.assign
                                                    (GoLean.GoCore.Assignee.var "j")
                                                    (GoLean.GoCore.Expr.add
                                                      (GoLean.GoCore.Expr.var "j")
                                                      (GoLean.GoCore.Expr.intLit
                                                        1
                                                        (GoLean.GoCore.IntKind.uint64)))),
                                                GoLean.GoCore.Stmt.seqn #[],
                                                GoLean.GoCore.Stmt.ifThenElse
                                                  (GoLean.GoCore.Expr.lessCmp
                                                    (GoLean.GoCore.Expr.var "j")
                                                    (GoLean.GoCore.Expr.var "n"))
                                                  (GoLean.GoCore.Stmt.seqn #[])
                                                  (GoLean.GoCore.Stmt.breakStmt),
                                                GoLean.GoCore.Stmt.block
                                                  #[]
                                                  #[GoLean.GoCore.Stmt.ifThenElse
                                                      (GoLean.GoCore.Expr.eqCmp
                                                        (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                                        (GoLean.GoCore.Expr.indexGet
                                                          (GoLean.GoCore.Expr.var "s")
                                                          (GoLean.GoCore.Expr.var "j"))
                                                        (GoLean.GoCore.Expr.indexGet
                                                          (GoLean.GoCore.Expr.var "t")
                                                          (GoLean.GoCore.Expr.var "i")))
                                                      (GoLean.GoCore.Stmt.block
                                                        #[]
                                                        #[GoLean.GoCore.Stmt.assign
                                                            (GoLean.GoCore.Assignee.var "cs")
                                                            (GoLean.GoCore.Expr.add
                                                              (GoLean.GoCore.Expr.var "cs")
                                                              (GoLean.GoCore.Expr.intLit
                                                                1
                                                                (GoLean.GoCore.IntKind.uint64)))])
                                                      (GoLean.GoCore.Stmt.seqn #[]),
                                                    GoLean.GoCore.Stmt.ifThenElse
                                                      (GoLean.GoCore.Expr.eqCmp
                                                        (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                                        (GoLean.GoCore.Expr.indexGet
                                                          (GoLean.GoCore.Expr.var "t")
                                                          (GoLean.GoCore.Expr.var "j"))
                                                        (GoLean.GoCore.Expr.indexGet
                                                          (GoLean.GoCore.Expr.var "t")
                                                          (GoLean.GoCore.Expr.var "i")))
                                                      (GoLean.GoCore.Stmt.block
                                                        #[]
                                                        #[GoLean.GoCore.Stmt.assign
                                                            (GoLean.GoCore.Assignee.var "ct")
                                                            (GoLean.GoCore.Expr.add
                                                              (GoLean.GoCore.Expr.var "ct")
                                                              (GoLean.GoCore.Expr.intLit
                                                                1
                                                                (GoLean.GoCore.IntKind.uint64)))])
                                                      (GoLean.GoCore.Stmt.seqn #[])]])]],
                                  GoLean.GoCore.Stmt.ifThenElse
                                    (GoLean.GoCore.Expr.neqCmp
                                      (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                      (GoLean.GoCore.Expr.var "cs")
                                      (GoLean.GoCore.Expr.var "ct"))
                                    (GoLean.GoCore.Stmt.block
                                      #[]
                                      #[GoLean.GoCore.Stmt.seqn
                                          #[GoLean.GoCore.Stmt.assign
                                              (GoLean.GoCore.Assignee.var "ok")
                                              (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))]])
                                    (GoLean.GoCore.Stmt.seqn #[])]])]],
                GoLean.GoCore.Stmt.seqn
                  #[GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.var "$res0")
                      (GoLean.GoCore.Expr.var "ok"),
                    GoLean.GoCore.Stmt.returnStmt]],
    variadic := false,
    wrapper := false }

/-- The lowering pin: the proof subject IS the frontend's lowering. -/
example : findFunctionIn? isortLowered.funcs ⟨"isort_harness"⟩
    = some isortHarnessFunc := rfl


/-! ## The entry equation (§11 glue) -/

/-- The entry frame environment (probe-pinned). -/
private def hIEnv0 : LocalEnv :=
  [[("$res0", .base ⟨2⟩), ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]]

private abbrev ucell (v : Int) : HeapCell :=
  ⟨some (.int .uint64), .int v .uint64⟩
private abbrev ucellU (v : Int) : HeapCell :=
  ⟨some (.int .uint64), .int (IntKind.normalize .uint64 v) .uint64⟩

/-- The initial state `runFunctionWithContextM` builds: the two
parameters normalized at `uint64`, the (uint64) verdict cell at its
default. -/
private def σIH0 (nv sv : Int) : ExecState :=
  { types := isortLowered.typeDefs.toList,
    functions := isortLowered.funcs,
    methods := isortLowered.methods,
    heap := [(.base ⟨0⟩, ucellU nv), (.base ⟨1⟩, ucellU sv),
             (.base ⟨2⟩, ucell 0)],
    nextAddr := 3 }

/-- **The entry equation**: the native entry IS its `runConfig` loop
from the probed initial state, plus the verdict read at `.base ⟨2⟩` —
∀ fuel, ∀ choices, definitionally. -/
private theorem iharness_entry_eq (nv sv : Int) (fuel : Nat)
    (ch : Choices) :
    runFunctionWithContextM fuel isortLowered.typeDefs.toList
        isortLowered.funcs isortHarnessFunc
        #[.int nv .uint64, .int sv .uint64]
        isortLowered.methods ch
      = (do
          let r ← runConfig fuel (σIH0 nv sv)
            (.exec isortHarnessFunc.body hIEnv0
              (.frame [] [] [] [] .stop false)) ch
          return { values := (← loadMany r.1 [.base ⟨2⟩]).toArray }) := by
  with_unfolding_all rfl

/-! ## The setup phase (the family materialized — the first third of
the harness run; segment counts probe-pinned, re-checked by `rfl`) -/

/-- The `s` handle over the backing array at its fixed address 4. -/
private abbrev hIHandleCell (n : Nat) : HeapCell :=
  ⟨some (.slice (.int .uint64)), .slice ⟨some (.base ⟨4⟩), 0, n, n⟩⟩
private abbrev hISliceH (n : Nat) : GoValue :=
  .slice ⟨some (.base ⟨4⟩), 0, n, n⟩

private def hIScope0 : List (String × Loc) :=
  [("$res0", .base ⟨2⟩), ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]

/-- The cleaned start state. -/
private def σIStart (n seed : Nat) : ExecState :=
  { types := isortLowered.typeDefs.toList,
    functions := isortLowered.funcs,
    methods := isortLowered.methods,
    heap := [(.base ⟨0⟩, ucell (n : Int)), (.base ⟨1⟩, ucell (seed : Int)),
             (.base ⟨2⟩, ucell 0)],
    nextAddr := 3 }

/-- `$c4` declared (default slice), the makeSlice length delivered. -/
private def σIStartC4 (n seed : Nat) : ExecState :=
  { σIStart n seed with
    heap := (σIStart n seed).heap
      ++ [(.base ⟨3⟩, ⟨some (.slice (.int .uint64)),
            .slice ⟨none, 0, 0, 0⟩⟩)],
    nextAddr := 4 }

/-- Post-makeSlice: the handle in `$c4`, the zeroed backing at 4. -/
private def σIMkS (n seed : Nat) : ExecState :=
  { types := isortLowered.typeDefs.toList,
    functions := isortLowered.funcs,
    methods := isortLowered.methods,
    heap := [(.base ⟨0⟩, ucell (n : Int)), (.base ⟨1⟩, ucell (seed : Int)),
             (.base ⟨2⟩, ucell 0),
             (.base ⟨3⟩, hIHandleCell n),
             (.base ⟨4⟩, arrCell n (List.replicate n 0))],
    nextAddr := 5 }

private def envC4 : LocalEnv := [[("$c4", .base ⟨3⟩)], hIScope0]

/-- The harness body's top statement list (projection of the pinned
record — reducible data, so the `rfl` segments see through it). -/
private def hIBodyList : List Stmt :=
  match isortHarnessFunc.body with
  | .block _ ss => ss.toList
  | _ => []

private def hIFrame0 : Cont := .frame [] [] [] [] .stop false

/-- The continuation below the makeSlice apply. -/
private def hIAfterMsK : Cont :=
  .seq (hIBodyList.drop 1) envC4 hIFrame0

private def hIMsK : Cont :=
  .stmtOpK (.makeSlice (.int .uint64) false) 1 [.addr (.base ⟨3⟩)] []
    envC4 hIAfterMsK

/-- Entry A: harness body start → the makeSlice length delivery. -/
private theorem hseg_IA1_raw (n seed : Nat) (ch : Choices) :
    stepFnIter 10 (σIStart n seed)
      (.exec isortHarnessFunc.body hIEnv0 hIFrame0) ch
      = .ok (.retV (.int ((n : Nat) : Int) .uint64) hIMsK,
          σIStartC4 n seed, ch) := by
  with_unfolding_all rfl

/-- **The makeSlice apply at a SYMBOLIC length**: allocates the zeroed
backing at 4 and stores the handle in `$c4`. -/
private theorem hstep_ImakeSlice (n seed : Nat) (ch : Choices) :
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
private def sISU (n : Nat) (sv : Int) (l : List Int) (iv : Int)
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

private def envISU : LocalEnv :=
  [[("$forFirst", .base ⟨7⟩)], [("i", .base ⟨6⟩)],
   [("s", .base ⟨5⟩), ("$c4", .base ⟨3⟩)], hIScope0]
private def envISU2 : LocalEnv :=
  [[("i", .base ⟨6⟩)], [("s", .base ⟨5⟩), ("$c4", .base ⟨3⟩)], hIScope0]
private def envIH2 : LocalEnv :=
  [[("s", .base ⟨5⟩), ("$c4", .base ⟨3⟩)], hIScope0]

private def suITail : Cont :=
  .seq [] envISU (.seq [] envISU2
    (.seq (hIBodyList.drop 3) envIH2 hIFrame0))
/-- The setup loop-head configuration. -/
private def suIHeadCfg : Config :=
  .exec (.while (.boolLit true) isortSetupBody) envISU suITail
private def suILoopK : Cont :=
  .loop (.boolLit true) isortSetupBody envISU suITail

private def suIStoreBlk : Stmt :=
  .block #[]
    #[.seqn
        #[.assign
            (.addr (.indexAddr (.var "s") (.var "i")))
            (.mul (.var "seed")
              (.add (.var "i") (.intLit 1 .uint64)))]]

/-- The setup exit test's delivery continuation. -/
private def suICmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envISU)
    (.seq [suIStoreBlk] ([] :: envISU) suILoopK)

private def suIStoreTail : Cont :=
  .seq [] ([] :: [] :: envISU) (.seq [] ([] :: envISU) suILoopK)

/-- Entry A2: makeSlice done → `s := $c4`, `i := 0`, the `$forFirst`
block → the setup loop head. -/
private theorem hseg_IA2_raw (n seed : Nat) (ch : Choices) :
    stepFnIter 42 (σIMkS n seed) (.next hIAfterMsK) ch
      = .ok (suIHeadCfg,
          sISU n (seed : Int) (List.replicate n 0) 0 true, ch) := by
  with_unfolding_all rfl

/-- Setup first-pass dispatch: flag drops, the exit test `i < n`. -/
private theorem hsegISU_d0_raw (n : Nat) (sv iv : Int) (l : List Int)
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

/-- **The setup loop**, by induction on `n - i`: exactly `57·(n-i)`
steps materialize the wrapped multiplicative family. No no-wrap
hypothesis — the wrap is the family's own definition; only the length
domain `n < 2^63` (Go `int`, the committed subject's own bound) is
consumed, for the counter arithmetic. -/
private theorem hIsetup_loop (n seed : Nat) (hn : n < 2 ^ 63) :
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
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro i hμ hin ch
    rcases Nat.lt_or_ge i n with hlt | hge
    · rw [show (decide (((i : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by omega)]
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
        (((seed * (i + 1)) % 2 ^ 64 : Nat) : Int) hlt
        (by rw [List.length_append, isFamily_length, List.length_replicate]
            omega)
        (isFamilyZ_range (by omega))
        ⟨by omega, by
          have := Nat.mod_lt (seed * (i + 1)) (y := 2 ^ 64) (by omega)
          omega⟩
        ((i : Nat) : Int) ch
      rw [isFamily_set hlt] at h2
      have h3 := hsegISU_d1_raw n (seed : Int) ((i : Nat) : Int)
        (isFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0) ch
      rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
        unorm_of_range (by omega)
          (by omega : ((i + 1 : Nat) : Int) < 2 ^ 64),
        unorm_of_range (by omega)
          (by omega : ((i + 1 : Nat) : Int) < 2 ^ 64)] at h3
      have hrec := ih (n - (i + 1)) (by omega) (i + 1) rfl (by omega) ch
      have hc := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h1 h2)
        h3) hrec
      rw [show 22 + 1 + 34 + 57 * (n - (i + 1)) = 57 * (n - i) from by
        omega] at hc
      exact hc
    · have hEq : i = n := by omega
      subst hEq
      simp only [Nat.sub_self, Nat.mul_zero, List.replicate_zero,
        List.append_nil]
      rfl

/-! ## The subject phase at the harness placement

The committed pass/frame-rebase machinery re-derived under the harness
continuation (Reverse's route (b): concrete re-derivation — the frame
theorem maps ADDRESSES, not continuations, so the canonical subject
run cannot be transferred here). Harness subject cells: 8 = the `s`
parameter, 9 = the subject `i`, 10 = the outer `$forFirst`; the
per-pass `j`/`$forFirst` pair sits TIGHT at 11/12 and is rebased into
the frame between passes (`rebaseSim11`, threshold 11 — the port of
`rebaseSim`). All step counts carry over from the canonical segments
verbatim (same statements, same machine paths — only addresses and the
tail continuation differ); each is re-checked by `rfl` here. -/

/-- The harness continuation after the subject call (`ok := 1` on). -/
private def hAfterCallK : Cont := .seq (hIBodyList.drop 4) envIH2 hIFrame0

/-- The subject call's frame continuation (caller env saved). -/
private def hSubjFrameK : Cont := .frame [] envIH2 [] [] hAfterCallK false

private def envHO : LocalEnv :=
  [[("$forFirst", .base ⟨10⟩)], [("i", .base ⟨9⟩)], [], [("s", .base ⟨8⟩)]]
private def envHOMid : LocalEnv :=
  [[("i", .base ⟨9⟩)], [], [("s", .base ⟨8⟩)]]
private def envHOOut : LocalEnv := [[], [("s", .base ⟨8⟩)]]

private def hHeadTailO : Cont :=
  .seq [] envHO (.seq [] envHOMid (.seq [] envHOOut hSubjFrameK))
/-- The subject OUTER loop-head configuration (harness placement). -/
private def hOuterHeadCfg : Config :=
  .exec (.while (.boolLit true) outerWhileBody) envHO hHeadTailO
private def hLoopKO : Cont :=
  .loop (.boolLit true) outerWhileBody envHO hHeadTailO
private def hOuterCmpCont : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envHO)
    (.seq [innerForBlock] ([] :: envHO) hLoopKO)
private def hLenTestK (iv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice (.int .uint64)))) [] [] ([] :: envHO)
    (.strictK .lessCmp [.int iv .int] [] ([] :: envHO) hOuterCmpCont)

private def envHI : LocalEnv :=
  [("$forFirst", .base ⟨12⟩)] :: [("j", .base ⟨11⟩)] :: [] :: [] :: envHO
private def hInnerTail : Cont :=
  .seq [] envHI
    (.seq [] ([("j", .base ⟨11⟩)] :: [] :: [] :: envHO)
      (.seq [] ([] :: [] :: envHO)
        (.seq [] ([] :: envHO) hLoopKO)))
/-- The subject INNER loop-head configuration (tight placement). -/
private def hInnerHeadCfg : Config :=
  .exec (.while (.boolLit true) innerWhileBody) envHI hInnerTail
private def hLoopKI : Cont :=
  .loop (.boolLit true) innerWhileBody envHI hInnerTail
private def hInnerIfK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envHI)
    (.seq [isortSwapBlock] ([] :: envHI) hLoopKI)
private def hAndKCont : Cont :=
  .andK (.greaterCmp
      (.indexGet (.var "s") (.sub (.var "j") (.intLit 1 .int)))
      (.indexGet (.var "s") (.var "j")))
    ([] :: envHI) hInnerIfK
private def hGcK1 : Cont :=
  .strictK .greaterCmp [] [.indexGet (.var "s") (.var "j")] ([] :: envHI)
    (.boolK hInnerIfK)
private def hGcK2 (w1 : GoValue) : Cont :=
  .strictK .greaterCmp [w1] [] ([] :: envHI) (.boolK hInnerIfK)

private def envHSw : LocalEnv := [] :: [] :: envHI
private def hSwTail : Cont :=
  .seq [] envHSw (.seq [] ([] :: envHI) hLoopKI)
private def hrefj (n : Nat) (idx : Int) : TargetRef :=
  .chain (hISliceH n) [.int idx .int] [.index]
private def hRhsK1 (n : Nat) (idx1 jv : Int) : Cont :=
  .rhsK .vals [hrefj n idx1, hrefj n jv] []
    [.indexGet (.var "s") (.sub (.var "j") (.intLit 1 .int))]
    (.seqn #[]) envHSw hSwTail
private def hRhsK2 (n : Nat) (idx1 jv : Int) (wj : GoValue) : Cont :=
  .rhsK .vals [hrefj n idx1, hrefj n jv] [wj] [] (.seqn #[]) envHSw hSwTail

/-- The harness-subject state family, TAIL-PARAMETRIC: the eleven
fixed harness cells in front (setup counter parked at `n`, verdict
still 0), an arbitrary inert tail behind. -/
private def σHOutT (n seed : Nat) (l : List Int) (iv : Int) (ffv : Bool)
    (tail : Heap) (na : Nat) : ExecState :=
  { types := isortLowered.typeDefs.toList,
    functions := isortLowered.funcs,
    methods := isortLowered.methods,
    heap := (.base ⟨0⟩, ucell (n : Int)) :: (.base ⟨1⟩, ucell (seed : Int))
      :: (.base ⟨2⟩, ucell 0) :: (.base ⟨3⟩, hIHandleCell n)
      :: (.base ⟨4⟩, arrCell n l) :: (.base ⟨5⟩, hIHandleCell n)
      :: (.base ⟨6⟩, ucell ((n : Nat) : Int)) :: (.base ⟨7⟩, bcell false)
      :: (.base ⟨8⟩, hIHandleCell n) :: (.base ⟨9⟩, intcell iv)
      :: (.base ⟨10⟩, bcell ffv) :: tail,
    nextAddr := na }

/-- The tight 11-cell outer state (canonical pass placement). -/
private def σHOut (n seed : Nat) (l : List Int) (iv : Int) (ffv : Bool) :
    ExecState :=
  σHOutT n seed l iv ffv [] 11

/-- The tight 13-cell in-pass state: `j` at 11, inner `$forFirst` at 12. -/
private def σHIn (n seed : Nat) (l : List Int) (iv jv : Int) (ffIv : Bool) :
    ExecState :=
  σHOutT n seed l iv false
    [(.base ⟨11⟩, intcell jv), (.base ⟨12⟩, bcell ffIv)] 13

/-- **The bridge**: setup exit (test false) → break unwinding → the
subject call — argument read, frame entry (`s` param at 8), `i := 1`
(at 9), the `$forFirst` block (at 10) — → the subject outer loop head.
40 steps (trace 306→346). -/
private theorem hbridge_raw (n seed : Nat) (l : List Int) (ch : Choices) :
    stepFnIter 40 (sISU n (seed : Int) l ((n : Nat) : Int) false)
      (.retV (.bool false) suICmpK) ch
      = .ok (hOuterHeadCfg, σHOut n seed l 1 true, ch) := by
  with_unfolding_all rfl

/-- First-pass outer dispatch (tail-parametric; touches only 0–10). -/
private theorem hseg_O0_raw (n seed : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 25 (σHOutT n seed l iv true tail na) hOuterHeadCfg ch
      = .ok (.retV (hISliceH n) (hLenTestK iv),
          σHOutT n seed l iv false tail na, ch) := by
  with_unfolding_all rfl

/-- Later-pass outer dispatch: `i := i + 1`, then the `len(s)` apply. -/
private theorem hseg_O1_raw (n seed : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 29 (σHOutT n seed l iv false tail na) hOuterHeadCfg ch
      = .ok (.retV (hISliceH n)
            (hLenTestK (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
          σHOutT n seed l (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            false tail na, ch) := by
  with_unfolding_all rfl

/-- The outer comparison delivered. -/
private theorem hseg_OB_raw (n seed : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 1 (σHOutT n seed l iv false tail na)
      (.retV (.int ((n : Nat) : Int) .int)
        (.strictK .lessCmp [.int iv .int] [] ([] :: envHO) hOuterCmpCont)) ch
      = .ok (.retV (.bool (decide (iv < ((n : Nat) : Int)))) hOuterCmpCont,
          σHOutT n seed l iv false tail na, ch) := by
  with_unfolding_all rfl

/-- Outer exit: test false → break unwinding, subject frame exit → the
harness continuation (`.next hAfterCallK`). State untouched. -/
private theorem hseg_exitO_raw (n seed : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 8 (σHOutT n seed l iv false tail na)
      (.retV (.bool false) hOuterCmpCont) ch
      = .ok (.next hAfterCallK, σHOutT n seed l iv false tail na, ch) := by
  with_unfolding_all rfl

/-- Pass entry: outer test true → `j := i` at 11, inner `$forFirst` at
12 (allocation — TIGHT placement only) → the inner loop head. -/
private theorem hseg_PA_raw (n seed : Nat) (l : List Int) (iv : Int)
    (ch : Choices) :
    stepFnIter 33 (σHOut n seed l iv false) (.retV (.bool true) hOuterCmpCont) ch
      = .ok (hInnerHeadCfg, σHIn n seed l iv (IntKind.normalize .int iv) true, ch) := by
  with_unfolding_all rfl

/-- First-pass inner dispatch → the first conjunct at the `&&`. -/
private theorem hseg_I0_raw (n seed : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 26 (σHIn n seed l iv jv true) hInnerHeadCfg ch
      = .ok (.retV (.bool (decide (0 < jv))) hAndKCont,
          σHIn n seed l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Later-pass inner dispatch: `j := j - 1`, then the first conjunct. -/
private theorem hseg_I1_raw (n seed : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 30 (σHIn n seed l iv jv false) hInnerHeadCfg ch
      = .ok (.retV (.bool (decide
              (0 < IntKind.normalize .int (IntKind.normalize .int (jv - 1)))))
            hAndKCont,
          σHIn n seed l iv
            (IntKind.normalize .int (IntKind.normalize .int (jv - 1)))
            false, ch) := by
  with_unfolding_all rfl

/-- The `&&` short-circuit arm (`j = 0` never reads `s[j-1]`). -/
private theorem hseg_andFalse_raw (n seed : Nat) (l : List Int) (iv jv : Int)
    (ffIv : Bool) (ch : Choices) :
    stepFnIter 1 (σHIn n seed l iv jv ffIv) (.retV (.bool false) hAndKCont) ch
      = .ok (.retV (.bool false) hInnerIfK, σHIn n seed l iv jv ffIv, ch) := by
  with_unfolding_all rfl

/-- Inner exit: break unwinds the inner loop only → the outer head. -/
private theorem hseg_exitI_raw (n seed : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 9 (σHIn n seed l iv jv false) (.retV (.bool false) hInnerIfK) ch
      = .ok (hOuterHeadCfg, σHIn n seed l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Second conjunct, phase A: `&&` true → the `s[j-1]` read's apply. -/
private theorem hseg_CA_raw (n seed : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 10 (σHIn n seed l iv jv false) (.retV (.bool true) hAndKCont) ch
      = .ok (.retV (.int (IntKind.normalize .int (jv - 1)) .int)
            (.strictK .indexGet [hISliceH n] [] ([] :: envHI) hGcK1),
          σHIn n seed l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Second conjunct, phase B: first element in → the `s[j]` apply. -/
private theorem hseg_CB_raw (n seed : Nat) (l : List Int) (iv jv : Int)
    (w1 : GoValue) (ch : Choices) :
    stepFnIter 5 (σHIn n seed l iv jv false) (.retV w1 hGcK1) ch
      = .ok (.retV (.int jv .int)
            (.strictK .indexGet [hISliceH n] [] ([] :: envHI) (hGcK2 w1)),
          σHIn n seed l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Second conjunct, phase C: comparison bool through `boolK`. -/
private theorem hseg_CC_raw (n seed : Nat) (l : List Int) (iv jv a b : Int)
    (ch : Choices) :
    stepFnIter 2 (σHIn n seed l iv jv false)
      (.retV (.int b .uint64) (hGcK2 (.int a .uint64))) ch
      = .ok (.retV (.bool (decide (b < a))) hInnerIfK,
          σHIn n seed l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase A: inner `if` true → targets resolved → `s[j]` apply. -/
private theorem hseg_SA_raw (n seed : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 24 (σHIn n seed l iv jv false) (.retV (.bool true) hInnerIfK) ch
      = .ok (.retV (.int jv .int)
            (.strictK .indexGet [hISliceH n] [] envHSw
              (hRhsK1 n (IntKind.normalize .int (jv - 1)) jv)),
          σHIn n seed l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase B: first rhs value in → the `s[j-1]` apply. -/
private theorem hseg_SB_raw (n seed : Nat) (l : List Int) (iv jv idx1 : Int)
    (wj : GoValue) (ch : Choices) :
    stepFnIter 9 (σHIn n seed l iv jv false) (.retV wj (hRhsK1 n idx1 jv)) ch
      = .ok (.retV (.int (IntKind.normalize .int (jv - 1)) .int)
            (.strictK .indexGet [hISliceH n] [] envHSw (hRhsK2 n idx1 jv wj)),
          σHIn n seed l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase B → stores: both rhs values in → phase 2 begins. -/
private theorem hseg_SC_raw (n seed : Nat) (l : List Int) (iv jv idx1 : Int)
    (wj wi : GoValue) (ch : Choices) :
    stepFnIter 1 (σHIn n seed l iv jv false) (.retV wi (hRhsK2 n idx1 jv wj)) ch
      = .ok (.next (.storeK [hrefj n idx1, hrefj n jv] [wj, wi] (.seqn #[])
            envHSw hSwTail),
          σHIn n seed l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap tail: stores done → back to the inner loop head. -/
private theorem hseg_SD_raw (n seed : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 5 (σHIn n seed l iv jv false)
      (.next (.storeK [] [] (.seqn #[]) envHSw hSwTail)) ch
      = .ok (hInnerHeadCfg, σHIn n seed l iv jv false, ch) := by
  with_unfolding_all rfl

/-- The backing-cell lookup at the tight in-pass state. -/
private theorem lookup_σHIn4 (n seed : Nat) (l : List Int) (iv jv : Int)
    (ffIv : Bool) :
    Heap.lookup (σHIn n seed l iv jv ffIv).heap (.base ⟨4⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := rfl

/-- One element read at the tight in-pass state. -/
private theorem stepFn_read_σHIn {n seed : Nat} {l : List Int} {iv jv : Int}
    {ffIv : Bool} {k : Nat} {env : LocalEnv} {K : Cont} {ch : Choices}
    (hk : k < n) (hlen : l.length = n) :
    stepFn (σHIn n seed l iv jv ffIv)
      (.retV (.int ((k : Nat) : Int) .int)
        (.strictK .indexGet [hISliceH n] [] env K)) ch
      = .ok (.retV (.int (l.getD k 0) .uint64) K, σHIn n seed l iv jv ffIv, ch) :=
  stepFn_strict_apply
    (applyStrictOp_indexGet_slice (lookup_σHIn4 n seed l iv jv ffIv)
      (Nat.le_refl n) hk
      (by rw [Nat.zero_add]; exact getElem?_mapU l k (by omega)))

/-- One element store at the tight in-pass state. -/
private theorem store_σHIn {n seed : Nat} {l : List Int} {iv jv : Int}
    {ffIv : Bool} {k : Nat} {w : Int}
    (hk : k < n) (hlen : l.length = n)
    (hl : ∀ x ∈ l, 0 ≤ x ∧ x < 2 ^ 64) (hw : 0 ≤ w ∧ w < 2 ^ 64) :
    storeTarget (σHIn n seed l iv jv ffIv) (hrefj n ((k : Nat) : Int))
      (.int w .uint64)
      = .ok (σHIn n seed (l.set k w) iv jv ffIv) := by
  have h := storeTarget_slice_u64 (a := ⟨4⟩) (off := 0) (len := n) (cap := n)
    (i := k) (n := n) (ik := .int) (l := l) (w := w)
    (lookup_σHIn4 n seed l iv jv ffIv) (Nat.le_refl n) hk (by omega) hlen hl hw
  rw [Nat.zero_add] at h
  exact h

/-! ### The inner induction at the harness placement (the canonical
`inner_loop`, re-derived — same measure, same invariant, same counts) -/

/-- **The inner loop (harness placement)**: from the first-conjunct
delivery at counter `jv` the run returns to the OUTER loop head with
the insertion complete, within `92·jv + 10` steps. -/
private theorem hs_inner_loop (n seed : Nat) (ivv : Int) (p suffix : List Int)
    (v : Int) (hn : n < 2 ^ 63)
    (hlen : p.length + 1 + suffix.length = n)
    (hsort : Sorted p)
    (hrp : ∀ x ∈ p, 0 ≤ x ∧ x < 2 ^ 64)
    (hrv : 0 ≤ v ∧ v < 2 ^ 64)
    (hrs : ∀ x ∈ suffix, 0 ≤ x ∧ x < 2 ^ 64) :
    ∀ μ jv, μ = jv → jv ≤ p.length →
    (∀ k, jv ≤ k → k < p.length → v < p.getD k 0) →
    ∀ ch : Choices, ∃ (k jex : Nat),
      k ≤ 92 * jv + 10 ∧ jex ≤ p.length ∧
      stepFnIter k
        (σHIn n seed (bubbleState p v jv ++ suffix) ivv ((jv : Nat) : Int) false)
        (.retV (.bool (decide (0 < ((jv : Nat) : Int)))) hAndKCont) ch
        = .ok (hOuterHeadCfg,
            σHIn n seed (insertSpec v p ++ suffix) ivv ((jex : Nat) : Int) false,
            ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro jv hμ hjp hinv ch
    have hbl : (bubbleState p v jv ++ suffix).length = n := by
      rw [List.length_append, bubbleState_length hjp]; omega
    cases jv with
    | zero =>
        rw [show (decide (0 < ((0 : Nat) : Int))) = false from
          decide_eq_false (by omega)]
        rw [← bubbleState_exit hsort (by omega) (.inl rfl)
          (fun k _ hk => hinv k (by omega) hk)]
        have hX0 := hseg_andFalse_raw n seed (bubbleState p v 0 ++ suffix) ivv
          ((0 : Nat) : Int) false ch
        have hX1 := hseg_exitI_raw n seed (bubbleState p v 0 ++ suffix) ivv
          ((0 : Nat) : Int) ch
        exact ⟨10, 0, by omega, by omega, stepFnIter_chain hX0 hX1⟩
    | succ jj =>
        have hjj : jj < p.length := by omega
        have hrL : ∀ x ∈ bubbleState p v (jj + 1) ++ suffix,
            0 ≤ x ∧ x < 2 ^ 64 := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · rcases mem_bubbleState hx with rfl | hx
            · exact hrv
            · exact hrp x hx
          · exact hrs x hx
        rw [show (decide (0 < ((jj + 1 : Nat) : Int))) = true from
          decide_eq_true (by omega)]
        have hCA := hseg_CA_raw n seed (bubbleState p v (jj + 1) ++ suffix)
          ivv ((jj + 1 : Nat) : Int) ch
        rw [show (((jj + 1 : Nat) : Int) - 1) = ((jj : Nat) : Int) from by
            omega,
          inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega)]
          at hCA
        have hgd1 : (bubbleState p v (jj + 1) ++ suffix).getD jj 0
            = p.getD jj 0 := by
          rw [getD_append_left (by rw [bubbleState_length hjp]; omega),
            bubbleState_getD_lt (by omega) hjp]
        have hread1 := stepFn_read_σHIn (n := n) (seed := seed)
          (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
          (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj)
          (env := [] :: envHI) (K := hGcK1) (ch := ch) (by omega) hbl
        rw [hgd1] at hread1
        have hCB := hseg_CB_raw n seed (bubbleState p v (jj + 1) ++ suffix)
          ivv ((jj + 1 : Nat) : Int) (.int (p.getD jj 0) .uint64) ch
        have hgd2 : (bubbleState p v (jj + 1) ++ suffix).getD (jj + 1) 0
            = v := by
          rw [getD_append_left (by rw [bubbleState_length hjp]; omega),
            bubbleState_getD_eq hjp]
        have hread2 := stepFn_read_σHIn (n := n) (seed := seed)
          (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
          (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj + 1)
          (env := [] :: envHI) (K := hGcK2 (.int (p.getD jj 0) .uint64))
          (ch := ch) (by omega) hbl
        rw [hgd2] at hread2
        have hCC := hseg_CC_raw n seed (bubbleState p v (jj + 1) ++ suffix)
          ivv ((jj + 1 : Nat) : Int) (p.getD jj 0) v ch
        have h19 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain hCA (stepFnIter_one hread1)) hCB)
          (stepFnIter_one hread2)) hCC
        by_cases hcmp : v < p.getD jj 0
        · rw [decide_eq_true hcmp] at h19
          have hSA := hseg_SA_raw n seed (bubbleState p v (jj + 1) ++ suffix)
            ivv ((jj + 1 : Nat) : Int) ch
          rw [show (((jj + 1 : Nat) : Int) - 1) = ((jj : Nat) : Int) from by
              omega,
            inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega)]
            at hSA
          have hgetj := stepFn_read_σHIn (n := n) (seed := seed)
            (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
            (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj + 1)
            (env := envHSw)
            (K := hRhsK1 n ((jj : Nat) : Int) ((jj + 1 : Nat) : Int))
            (ch := ch) (by omega) hbl
          rw [hgd2] at hgetj
          have hSB := hseg_SB_raw n seed (bubbleState p v (jj + 1) ++ suffix)
            ivv ((jj + 1 : Nat) : Int) ((jj : Nat) : Int)
            (.int v .uint64) ch
          rw [show (((jj + 1 : Nat) : Int) - 1) = ((jj : Nat) : Int) from by
              omega,
            inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega)]
            at hSB
          have hgetj1 := stepFn_read_σHIn (n := n) (seed := seed)
            (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
            (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj)
            (env := envHSw)
            (K := hRhsK2 n ((jj : Nat) : Int) ((jj + 1 : Nat) : Int)
              (.int v .uint64))
            (ch := ch) (by omega) hbl
          rw [hgd1] at hgetj1
          have hSC := hseg_SC_raw n seed (bubbleState p v (jj + 1) ++ suffix)
            ivv ((jj + 1 : Nat) : Int) ((jj : Nat) : Int)
            (.int v .uint64) (.int (p.getD jj 0) .uint64) ch
          have hst1 := store_σHIn (n := n) (seed := seed)
            (l := bubbleState p v (jj + 1) ++ suffix) (iv := ivv)
            (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj)
            (w := v) (by omega) hbl hrL hrv
          have hstep1 := stepFn_store_step
            (rs := [hrefj n ((jj + 1 : Nat) : Int)])
            (vs := [.int (p.getD jj 0) .uint64]) (body := .seqn #[])
            (env := envHSw) (k := hSwTail) (ch := ch) hst1
          have hrL1 : ∀ x ∈ (bubbleState p v (jj + 1) ++ suffix).set jj v,
              0 ≤ x ∧ x < 2 ^ 64 := by
            intro x hx
            rcases mem_set_of_mem hx with rfl | hx
            · exact hrv
            · exact hrL x hx
          have hst2 := store_σHIn (n := n) (seed := seed)
            (l := (bubbleState p v (jj + 1) ++ suffix).set jj v) (iv := ivv)
            (jv := ((jj + 1 : Nat) : Int)) (ffIv := false) (k := jj + 1)
            (w := p.getD jj 0) (by omega)
            (by rw [List.length_set]; exact hbl) hrL1
            (hrp _ (getD_mem hjj))
          have hstep2 := stepFn_store_step (rs := []) (vs := [])
            (body := .seqn #[]) (env := envHSw) (k := hSwTail) (ch := ch)
            hst2
          have hsurg : ((bubbleState p v (jj + 1) ++ suffix).set jj v).set
              (jj + 1) (p.getD jj 0)
              = bubbleState p v jj ++ suffix := by
            rw [set_append_left (by rw [bubbleState_length hjp]; omega),
              set_append_left (by
                rw [List.length_set, bubbleState_length hjp]; omega)]
            exact congrArg (· ++ suffix)
              (bubbleState_swap (by omega) hjp)
          rw [hsurg] at hstep2
          have hSD := hseg_SD_raw n seed (bubbleState p v jj ++ suffix) ivv
            ((jj + 1 : Nat) : Int) ch
          have hI1 := hseg_I1_raw n seed (bubbleState p v jj ++ suffix) ivv
            ((jj + 1 : Nat) : Int) ch
          rw [show (((jj + 1 : Nat) : Int) - 1) = ((jj : Nat) : Int) from by
              omega,
            inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega),
            inorm_of_range (v := ((jj : Nat) : Int)) (by omega) (by omega)]
            at hI1
          obtain ⟨k, jex, hk, hjex, hrec⟩ := ih jj (by omega) jj rfl
            (by omega)
            (fun k hk hk' => by
              rcases Nat.eq_or_lt_of_le hk with rfl | hlt
              · exact hcmp
              · exact hinv k (by omega) hk') ch
          refine ⟨92 + k, jex, by omega, hjex, ?_⟩
          have h62 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
            (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
              (stepFnIter_chain (stepFnIter_chain h19 hSA)
                (stepFnIter_one hgetj)) hSB) (stepFnIter_one hgetj1))
              hSC) (stepFnIter_one hstep1)) (stepFnIter_one hstep2)) hSD
          exact stepFnIter_chain (stepFnIter_chain h62 hI1) hrec
        · rw [decide_eq_false hcmp] at h19
          rw [← bubbleState_exit hsort (by omega)
            (.inr (Int.not_lt.mp hcmp)) hinv]
          have hX1 := hseg_exitI_raw n seed (bubbleState p v (jj + 1) ++ suffix)
            ivv ((jj + 1 : Nat) : Int) ch
          exact ⟨28, jj + 1, by omega, by omega, stepFnIter_chain h19 hX1⟩

/-- **One outer pass at the tight harness placement** (outer test true
at the 11-cell state → the NEXT outer test delivery at the 13-cell
state). -/
private theorem hs_pass_seg (n seed : Nat) (p suffix : List Int) (v : Int)
    (m : Nat) (hn : n < 2 ^ 63)
    (hplen : p.length = m + 1)
    (hlen : p.length + 1 + suffix.length = n)
    (hsort : Sorted p)
    (hrp : ∀ x ∈ p, 0 ≤ x ∧ x < 2 ^ 64)
    (hrv : 0 ≤ v ∧ v < 2 ^ 64)
    (hrs : ∀ x ∈ suffix, 0 ≤ x ∧ x < 2 ^ 64)
    (ch : Choices) :
    ∃ (k jex : Nat), k ≤ 92 * n + 118 ∧ jex ≤ m + 1 ∧
      stepFnIter k (σHOut n seed (p ++ v :: suffix) ((m + 1 : Nat) : Int) false)
        (.retV (.bool true) hOuterCmpCont) ch
        = .ok (.retV (.bool (decide
              (((m + 2 : Nat) : Int) < ((n : Nat) : Int)))) hOuterCmpCont,
            σHIn n seed (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
              ((jex : Nat) : Int) false, ch) := by
  have hm1n : m + 2 ≤ n := by omega
  have hPA := hseg_PA_raw n seed (p ++ v :: suffix) ((m + 1 : Nat) : Int) ch
  rw [inorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)]
    at hPA
  have hI0 := hseg_I0_raw n seed (p ++ v :: suffix) ((m + 1 : Nat) : Int)
    ((m + 1 : Nat) : Int) ch
  have hbub : bubbleState p v (m + 1) ++ suffix = p ++ v :: suffix := by
    rw [← hplen, bubbleState_full, List.append_assoc]
    rfl
  obtain ⟨kin, jex, hkin, hjex, hrun⟩ := hs_inner_loop n seed
    ((m + 1 : Nat) : Int) p suffix v hn hlen hsort hrp hrv hrs (m + 1)
    (m + 1) rfl (by omega) (fun k hk hk' => by omega) ch
  rw [hbub] at hrun
  have hO1 : stepFnIter 29
      (σHIn n seed (insertSpec v p ++ suffix) ((m + 1 : Nat) : Int)
        ((jex : Nat) : Int) false) hOuterHeadCfg ch
      = .ok (.retV (hISliceH n)
            (hLenTestK (IntKind.normalize .int (IntKind.normalize .int
              (((m + 1 : Nat) : Int) + 1)))),
          σHIn n seed (insertSpec v p ++ suffix)
            (IntKind.normalize .int (IntKind.normalize .int
              (((m + 1 : Nat) : Int) + 1)))
            ((jex : Nat) : Int) false, ch) :=
    hseg_O1_raw n seed (insertSpec v p ++ suffix) ((m + 1 : Nat) : Int)
      [(.base ⟨11⟩, intcell ((jex : Nat) : Int)), (.base ⟨12⟩, bcell false)]
      13 ch
  rw [show (((m + 1 : Nat) : Int) + 1) = ((m + 2 : Nat) : Int) from by omega,
    inorm_of_range (v := ((m + 2 : Nat) : Int)) (by omega) (by omega),
    inorm_of_range (v := ((m + 2 : Nat) : Int)) (by omega) (by omega)]
    at hO1
  have hlenapp : stepFn
      (σHIn n seed (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
        ((jex : Nat) : Int) false)
      (.retV (hISliceH n) (hLenTestK ((m + 2 : Nat) : Int))) ch
      = .ok (.retV (.int ((n : Nat) : Int) .int)
          (.strictK .lessCmp [.int ((m + 2 : Nat) : Int) .int] []
            ([] :: envHO) hOuterCmpCont),
        σHIn n seed (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
          ((jex : Nat) : Int) false, ch) :=
    stepFn_strict_apply (done := [])
      (applyStrictOp_len_slice (Nat.le_refl n))
  have hOB : stepFnIter 1
      (σHIn n seed (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
        ((jex : Nat) : Int) false)
      (.retV (.int ((n : Nat) : Int) .int)
        (.strictK .lessCmp [.int ((m + 2 : Nat) : Int) .int] []
          ([] :: envHO) hOuterCmpCont)) ch
      = .ok (.retV (.bool (decide
            (((m + 2 : Nat) : Int) < ((n : Nat) : Int)))) hOuterCmpCont,
          σHIn n seed (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
            ((jex : Nat) : Int) false, ch) :=
    hseg_OB_raw n seed (insertSpec v p ++ suffix) ((m + 2 : Nat) : Int)
      [(.base ⟨11⟩, intcell ((jex : Nat) : Int)), (.base ⟨12⟩, bcell false)]
      13 ch
  refine ⟨33 + 26 + kin + 29 + 1 + 1, jex, by omega, by omega, ?_⟩
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain hPA hI0) hrun) hO1)
    (stepFnIter_one hlenapp)) hOB

/-! ### The per-pass frame layer at threshold 11 (the canonical
`ρsh`/`rebaseSim` layer, re-derived at the harness prefix: the eleven
fixed cells 0–10, the pass-local region from 11) -/

/-- The per-pass shift: identity on the fixed cells `0..10`, shift by
`d` on the pass-local region. -/
private def ρ11 (d : Nat) : Nat → Nat := fun x => if x < 11 then x else x + d

private theorem ρ11_lt {d a : Nat} (h : a < 11) : ρ11 d a = a := if_pos h
private theorem ρ11_ge {d a : Nat} (h : 11 ≤ a) : ρ11 d a = a + d :=
  if_neg (by omega)

private theorem shiftSpec_ρ11 (d : Nat) : ShiftSpec (ρ11 d) 11 (11 + d) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    simp only [ρ11] at hxy
    split at hxy <;> split at hxy <;> omega
  · intro k
    simp only [ρ11]
    rw [if_neg (by omega)]
    omega

private theorem renCell_handleH (d n : Nat) :
    renameCell (ρ11 d) (hIHandleCell n) = hIHandleCell n := by
  simp [renameCell, renameValue, renameLoc, ρ11]

private theorem lookup_σHOut_ge {n seed : Nat} {l : List Int} {iv : Int}
    {ffv : Bool} {a : Nat} (ha : 11 ≤ a) :
    Heap.lookup (σHOut n seed l iv ffv).heap (.base ⟨a⟩) = none := by
  simp [σHOut, σHOutT, Heap.lookup,
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
    beq_false_of_ne (base_ne (show (10 : Nat) ≠ a by omega))]

private theorem lookup_σHIn_ge {n seed : Nat} {l : List Int} {iv jv : Int}
    {ffIv : Bool} {a : Nat} (ha : 13 ≤ a) :
    Heap.lookup (σHIn n seed l iv jv ffIv).heap (.base ⟨a⟩) = none := by
  simp [σHIn, σHOutT, Heap.lookup,
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
    beq_false_of_ne (base_ne (show (12 : Nat) ≠ a by omega))]

private theorem lookup_σHOut_field (n seed : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) (b : Loc) (tid : TypeId) (f : String) :
    Heap.lookup (σHOut n seed l iv ffv).heap (.field b tid f) = none := rfl

private theorem lookup_σHOut_index (n seed : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) (b : Loc) (i : Int) :
    Heap.lookup (σHOut n seed l iv ffv).heap (.index b i) = none := rfl

private theorem lookup_σHIn_field (n seed : Nat) (l : List Int) (iv jv : Int)
    (ffIv : Bool) (b : Loc) (tid : TypeId) (f : String) :
    Heap.lookup (σHIn n seed l iv jv ffIv).heap (.field b tid f) = none := rfl

private theorem lookup_σHIn_index (n seed : Nat) (l : List Int) (iv jv : Int)
    (ffIv : Bool) (b : Loc) (i : Int) :
    Heap.lookup (σHIn n seed l iv jv ffIv).heap (.index b i) = none := rfl

/-- Root bump by 2 above the fixed cells (threshold 11). -/
private def bump2H : Loc → Loc
  | .base a => .base ⟨if a.id < 11 then a.id else a.id + 2⟩
  | .field b tid f => .field (bump2H b) tid f
  | .index b i => .index (bump2H b) i

private theorem renameLoc_bump2H (d : Nat) (l : Loc) :
    renameLoc (ρ11 (d + 2)) l = renameLoc (ρ11 d) (bump2H l) := by
  induction l with
  | base a =>
      have h : ρ11 (d + 2) a.id
          = ρ11 d (if a.id < 11 then a.id else a.id + 2) := by
        by_cases ha : a.id < 11
        · rw [if_pos ha, ρ11_lt ha, ρ11_lt ha]
        · rw [if_neg ha, ρ11_ge (d := d + 2) (a := a.id) (by omega),
            ρ11_ge (d := d) (a := a.id + 2) (by omega)]
          omega
      simp only [renameLoc, bump2H, h]
  | field b tid f ih => simp only [renameLoc, bump2H, ih]
  | index b i ih => simp only [renameLoc, bump2H, ih]

/-- The trivial-frame simulation at the subject-loop entry. -/
private theorem frameSim_zero11 (n seed : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) :
    FrameSim (ρ11 0) 11 11 [] (σHOut n seed l iv ffv)
      (σHOut n seed l iv ffv) := by
  refine ⟨shiftSpec_ρ11 0, rfl, rfl, rfl, rfl, rfl, Nat.le_refl 11,
    ?_, ?_, fun a => rfl, bodies_ρsh (ρ11 0)⟩
  · intro loc
    match loc with
    | .base ⟨a⟩ =>
        match a with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
        | 3 =>
            show Heap.lookup (σHOut n seed l iv ffv).heap (.base ⟨ρ11 0 3⟩)
              = some (renameCell (ρ11 0) (hIHandleCell n))
            rw [renCell_handleH 0 n]
            rfl
        | 4 =>
            show Heap.lookup (σHOut n seed l iv ffv).heap (.base ⟨ρ11 0 4⟩)
              = some (renameCell (ρ11 0) (arrCell n l))
            rw [renCell_arr]
            rfl
        | 5 =>
            show Heap.lookup (σHOut n seed l iv ffv).heap (.base ⟨ρ11 0 5⟩)
              = some (renameCell (ρ11 0) (hIHandleCell n))
            rw [renCell_handleH 0 n]
            rfl
        | 6 => rfl
        | 7 => rfl
        | 8 =>
            show Heap.lookup (σHOut n seed l iv ffv).heap (.base ⟨ρ11 0 8⟩)
              = some (renameCell (ρ11 0) (hIHandleCell n))
            rw [renCell_handleH 0 n]
            rfl
        | 9 => rfl
        | 10 => rfl
        | (a + 11) =>
            show Heap.lookup (σHOut n seed l iv ffv).heap
              (.base ⟨ρ11 0 (a + 11)⟩) = _
            rw [ρ11_ge (d := 0) (a := a + 11) (by omega)]
            rw [lookup_σHOut_ge (a := a + 11 + 0) (by omega)]
            rfl
    | .field b tid f => rfl
    | .index b i => rfl
  · intro loc c hc
    simp [Heap.lookup] at hc

private theorem fs_lookup_none11 {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (h : FrameSim ρ na₀ na fr σ σF) {l : Loc}
    (hl : Heap.lookup σ.heap l = none) :
    Heap.lookup σF.heap (renameLoc ρ l) = Heap.lookup fr (renameLoc ρ l) := by
  have h2 := h.lookup_img l
  rw [hl] at h2
  exact h2

/-- **The frame rebase at threshold 11**: the pass's retired
`j`/`$forFirst` cells (canonical 11/12) move INTO the frame at their
true addresses `11+d`/`12+d`. -/
private theorem rebaseSim11 {d : Nat} {fr : Heap} {n seed : Nat}
    {l : List Int} {iv jv : Int} {σA : ExecState}
    (h : FrameSim (ρ11 d) 11 (11 + d) fr (σHIn n seed l iv jv false) σA) :
    FrameSim (ρ11 (d + 2)) 11 (11 + (d + 2))
      (fr ++ [(.base ⟨11 + d⟩, intcell jv), (.base ⟨12 + d⟩, bcell false)])
      (σHOut n seed l iv false) σA := by
  refine ⟨shiftSpec_ρ11 (d + 2), h.types_eq, h.funcs_eq, h.methods_eq,
    h.methodSets_eq, ?_, Nat.le_refl 11, ?_, ?_, ?_, bodies_ρsh _⟩
  · have hne := h.next_eq
    rw [show (σHIn n seed l iv jv false).nextAddr = 13 from rfl,
      ρ11_ge (d := d) (a := 13) (by omega)] at hne
    show σA.nextAddr = ρ11 (d + 2) 11
    rw [ρ11_ge (d := d + 2) (a := 11) (by omega)]
    omega
  · intro loc
    match loc with
    | .base ⟨a⟩ =>
        by_cases ha : a < 11
        · rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5
              ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10)
            with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact h.lookup_some (l := .base ⟨0⟩) (c := ucell (n : Int)) rfl
          · exact h.lookup_some (l := .base ⟨1⟩) (c := ucell (seed : Int)) rfl
          · exact h.lookup_some (l := .base ⟨2⟩) (c := ucell 0) rfl
          · exact h.lookup_some (l := .base ⟨3⟩) (c := hIHandleCell n) rfl
          · have himg := h.lookup_some (l := .base ⟨4⟩) (c := arrCell n l) rfl
            rw [renCell_arr] at himg
            show Heap.lookup σA.heap (.base ⟨ρ11 (d + 2) 4⟩)
              = some (renameCell (ρ11 (d + 2)) (arrCell n l))
            rw [renCell_arr]
            exact himg
          · exact h.lookup_some (l := .base ⟨5⟩) (c := hIHandleCell n) rfl
          · exact h.lookup_some (l := .base ⟨6⟩)
              (c := ucell ((n : Nat) : Int)) rfl
          · exact h.lookup_some (l := .base ⟨7⟩) (c := bcell false) rfl
          · exact h.lookup_some (l := .base ⟨8⟩) (c := hIHandleCell n) rfl
          · exact h.lookup_some (l := .base ⟨9⟩) (c := intcell iv) rfl
          · exact h.lookup_some (l := .base ⟨10⟩) (c := bcell false) rfl
        · have himg := fs_lookup_none11 h (l := .base ⟨a + 2⟩)
            (lookup_σHIn_ge (by omega))
          have hren1 : renameLoc (ρ11 d) (.base ⟨a + 2⟩)
              = .base ⟨a + 2 + d⟩ := by
            simp [renameLoc, ρ11_ge (d := d) (a := a + 2) (by omega)]
          rw [hren1] at himg
          have hren2 : renameLoc (ρ11 (d + 2)) (.base ⟨a⟩)
              = .base ⟨a + (d + 2)⟩ := by
            simp [renameLoc, ρ11_ge (d := d + 2) (a := a) (by omega)]
          rw [hren2, lookup_σHOut_ge (by omega)]
          show Heap.lookup σA.heap (.base ⟨a + (d + 2)⟩)
            = Heap.lookup (fr ++ [(.base ⟨11 + d⟩, intcell jv),
                (.base ⟨12 + d⟩, bcell false)]) (.base ⟨a + (d + 2)⟩)
          rw [show a + (d + 2) = a + 2 + d from by omega, himg,
            lookup_append]
          cases hfr : Heap.lookup fr (.base ⟨a + 2 + d⟩) with
          | some c => rfl
          | none =>
              show (none : Option HeapCell)
                = Heap.lookup [(.base ⟨11 + d⟩, intcell jv),
                    (.base ⟨12 + d⟩, bcell false)] (.base ⟨a + 2 + d⟩)
              simp [Heap.lookup,
                beq_false_of_ne (base_ne (show 11 + d ≠ a + 2 + d by omega)),
                beq_false_of_ne (base_ne (show 12 + d ≠ a + 2 + d by omega))]
    | .field b tid f =>
        have himg := fs_lookup_none11 h (l := bump2H (.field b tid f))
          (lookup_σHIn_field n seed l iv jv false (bump2H b) tid f)
        rw [← renameLoc_bump2H] at himg
        show Heap.lookup σA.heap (renameLoc (ρ11 (d + 2)) (.field b tid f))
          = Heap.lookup (fr ++ [(.base ⟨11 + d⟩, intcell jv),
              (.base ⟨12 + d⟩, bcell false)])
            (renameLoc (ρ11 (d + 2)) (.field b tid f))
        rw [himg, lookup_append]
        cases hfr : Heap.lookup fr
            (renameLoc (ρ11 (d + 2)) (.field b tid f)) with
        | some c => rfl
        | none => rfl
    | .index b i =>
        have himg := fs_lookup_none11 h (l := bump2H (.index b i))
          (lookup_σHIn_index n seed l iv jv false (bump2H b) i)
        rw [← renameLoc_bump2H] at himg
        show Heap.lookup σA.heap (renameLoc (ρ11 (d + 2)) (.index b i))
          = Heap.lookup (fr ++ [(.base ⟨11 + d⟩, intcell jv),
              (.base ⟨12 + d⟩, bcell false)])
            (renameLoc (ρ11 (d + 2)) (.index b i))
        rw [himg, lookup_append]
        cases hfr : Heap.lookup fr
            (renameLoc (ρ11 (d + 2)) (.index b i)) with
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
        have hc' : Heap.lookup [(.base ⟨11 + d⟩, intcell jv),
            (.base ⟨12 + d⟩, bcell false)] loc = some c := hc
        by_cases h4 : (.base ⟨11 + d⟩ : Loc) = loc
        · subst h4
          have hcell : c = intcell jv := by
            simp [Heap.lookup] at hc'
            exact hc'.symm
          subst hcell
          exact h.lookup_some (l := .base ⟨11⟩) (c := intcell jv) rfl
        · by_cases h5 : (.base ⟨12 + d⟩ : Loc) = loc
          · subst h5
            have hcell : c = bcell false := by
              simp [Heap.lookup, beq_false_of_ne h4] at hc'
              exact hc'.symm
            subst hcell
            exact h.lookup_some (l := .base ⟨12⟩) (c := bcell false) rfl
          · exfalso
            simp [Heap.lookup, beq_false_of_ne h4, beq_false_of_ne h5] at hc'
  · intro a
    rw [lookup_append]
    by_cases ha : a < 11
    · rw [ρ11_lt ha]
      have h2 := h.fr_avoid a
      rw [ρ11_lt ha] at h2
      rw [h2]
      show Heap.lookup [(.base ⟨11 + d⟩, intcell jv),
          (.base ⟨12 + d⟩, bcell false)] (.base ⟨a⟩) = none
      simp [Heap.lookup,
        beq_false_of_ne (base_ne (show 11 + d ≠ a by omega)),
        beq_false_of_ne (base_ne (show 12 + d ≠ a by omega))]
    · rw [ρ11_ge (d := d + 2) (a := a) (by omega)]
      have h2 := h.fr_avoid (a + 2)
      rw [ρ11_ge (d := d) (a := a + 2) (by omega)] at h2
      rw [show a + (d + 2) = a + 2 + d from by omega, h2]
      show Heap.lookup [(.base ⟨11 + d⟩, intcell jv),
          (.base ⟨12 + d⟩, bcell false)] (.base ⟨a + 2 + d⟩) = none
      simp [Heap.lookup,
        beq_false_of_ne (base_ne (show 11 + d ≠ a + 2 + d by omega)),
        beq_false_of_ne (base_ne (show 12 + d ≠ a + 2 + d by omega))]

private theorem renCfg_hcmp (d : Nat) (b : Bool) :
    renameConfig (ρ11 d) (.retV (.bool b) hOuterCmpCont)
      = .retV (.bool b) hOuterCmpCont := by
  with_unfolding_all rfl

private theorem renCfg_hanchor (d : Nat) :
    renameConfig (ρ11 d) (.next hAfterCallK) = .next hAfterCallK := by
  with_unfolding_all rfl

/-- A canonical segment between shift-fixed configurations transfers
to the true placement (threshold-11 instance). -/
private theorem transfer_seg11 {d : Nat} {fr : Heap} {σC σC' σA : ExecState}
    {c c' : Config} {k : Nat} {ch : Choices}
    (hFS : FrameSim (ρ11 d) 11 (11 + d) fr σC σA)
    (hrun : stepFnIter k σC c ch = .ok (c', σC', ch))
    (hc : renameConfig (ρ11 d) c = c) (hc' : renameConfig (ρ11 d) c' = c') :
    ∃ σA', stepFnIter k σA c ch = .ok (c', σA', ch)
      ∧ FrameSim (ρ11 d) 11 (11 + d) fr σC' σA' := by
  have hsim := stepFnIter_sim k hFS c ch
  rw [hc] at hsim
  obtain ⟨rF, hrunF, htrip⟩ := hsim.ok_inv hrun
  obtain ⟨cF, σF, chF⟩ := rF
  obtain ⟨h1, h2, h3⟩ := htrip
  dsimp only at h1 h2 h3
  rw [h1, hc'] at hrunF
  rw [h3] at hrunF
  exact ⟨σF, hrunF, h2⟩

/-! ### The subject outer induction (harness placement): each pass
transferred from the tight placement, rebased, ending at the harness
anchor `.next hAfterCallK` with the surviving frame simulation -/

/-- **The subject outer loop over the true (garbage-laden) harness
run**: from the outer test delivery after `m` passes, the run reaches
the post-subject anchor with the backing fully sorted, delivering the
final frame simulation (existential shift `d`, frame `fr'`, parked
subject counter `ivF`). -/
private theorem hs_outer_loop (xs : List Int) (n seed : Nat)
    (hn : n = xs.length)
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (h63 : n < 2 ^ 63) :
    ∀ μ m (σA : ExecState) (fr : Heap), μ = n - (m + 1) →
    FrameSim (ρ11 (2 * m)) 11 (11 + 2 * m) fr
      (σHOut n seed (sortPrefix xs (m + 1)) ((m + 1 : Nat) : Int) false) σA →
    ∀ ch : Choices, ∃ (k : Nat) (σA' : ExecState) (d : Nat) (fr' : Heap)
      (ivF : Int),
      k ≤ (92 * n + 160) * μ + 10 ∧
      stepFnIter k σA
        (.retV (.bool (decide (((m + 1 : Nat) : Int) < ((n : Nat) : Int))))
          hOuterCmpCont) ch
        = .ok (.next hAfterCallK, σA', ch)
      ∧ FrameSim (ρ11 d) 11 (11 + d) fr'
          (σHOut n seed (sortSpec xs) ivF false) σA' := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m σA fr hμ hFS ch
    subst hμ
    rcases Nat.lt_or_ge (m + 1) n with hlt | hge
    · rw [show (decide (((m + 1 : Nat) : Int) < ((n : Nat) : Int))) = true
        from decide_eq_true (by exact_mod_cast (by omega : m + 1 < n))]
      have hplen : (sortSpec (xs.take (m + 1))).length = m + 1 := by
        rw [sortSpec_length, List.length_take]
        omega
      obtain ⟨K, jex, hK, hjex, hpass⟩ := hs_pass_seg n seed
        (sortSpec (xs.take (m + 1))) (xs.drop (m + 2)) (xs.getD (m + 1) 0)
        m h63 hplen (by rw [hplen, List.length_drop]; omega)
        (sortSpec_sorted _)
        (fun x hx => hxs x (List.mem_of_mem_take (mem_sortSpec hx)))
        (hxs _ (getD_mem (by omega)))
        (fun x hx => hxs x (List.mem_of_mem_drop hx)) ch
      rw [← sortPrefix_decomp (by omega)] at hpass
      have hnext : sortPrefix xs (m + 2)
          = insertSpec (xs.getD (m + 1) 0) (sortSpec (xs.take (m + 1)))
            ++ xs.drop (m + 2) := by
        rw [sortPrefix]
        congr 1
        exact sortSpec_take_succ (k := m + 1) (by omega)
      rw [← hnext] at hpass
      obtain ⟨σA', hrunA, hFS'⟩ := transfer_seg11 hFS hpass
        (renCfg_hcmp (2 * m) true) (renCfg_hcmp (2 * m) _)
      have hFS2 := rebaseSim11 hFS'
      obtain ⟨k, σA'', d, fr', ivF, hk, hrun, hFSf⟩ := ih (n - (m + 2))
        (by omega) (m + 1) σA'
        (fr ++ [(.base ⟨11 + 2 * m⟩, intcell ((jex : Nat) : Int)),
          (.base ⟨12 + 2 * m⟩, bcell false)]) rfl
        (by
          have : 2 * m + 2 = 2 * (m + 1) := by omega
          rw [← this]
          exact hFS2) ch
      refine ⟨K + k, σA'', d, fr', ivF, ?_,
        stepFnIter_chain hrunA hrun, hFSf⟩
      have hmul : (92 * n + 160) * (n - (m + 2)) + (92 * n + 160)
          = (92 * n + 160) * (n - (m + 1)) := by
        rw [← Nat.mul_succ]
        congr 1
        omega
      omega
    · rw [show (decide (((m + 1 : Nat) : Int) < ((n : Nat) : Int))) = false
        from decide_eq_false (by exact_mod_cast (by omega : ¬ (m + 1 < n)))]
      have hX := hseg_exitO_raw n seed (sortPrefix xs (m + 1))
        ((m + 1 : Nat) : Int) [] 11 ch
      obtain ⟨σA', hrunA, hFS'⟩ := transfer_seg11 hFS hX
        (renCfg_hcmp (2 * m) false) (renCfg_hanchor (2 * m))
      rw [sortPrefix_full (by omega)] at hFS'
      exact ⟨8, σA', 2 * m, fr, ((m + 1 : Nat) : Int), by omega, hrunA, hFS'⟩

/-! ## The test phase, part 1: the sortedness scan (canonical remainder
placement — `ok` at 11, scan counter at 12, flag at 13; the scan never
allocates per iteration, so its segments are address-concrete; the
whole remainder run is transferred to the true placement in ONE
`transfer_seg11` application at the end) -/

private def okScopeI : Scope :=
  [("ok", .base ⟨11⟩), ("s", .base ⟨5⟩), ("$c4", .base ⟨3⟩)]
private def envIH2ok : LocalEnv := [okScopeI, hIScope0]
private def envSC : LocalEnv :=
  [[("$forFirst", .base ⟨13⟩)], [("i", .base ⟨12⟩)], okScopeI, hIScope0]

/-- The scan loop's desugared while body (from the pinned record). -/
abbrev isortScanBody : Stmt :=
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
        #[.ifThenElse
            (.greaterCmp
              (.indexGet (.var "s")
                (.sub (.var "i") (.intLit 1 .uint64)))
              (.indexGet (.var "s") (.var "i")))
            (.block #[]
              #[.seqn #[.assign (.var "ok") (.intLit 0 .uint64)]])
            (.seqn #[])]]

private def scTail : Cont :=
  .seq [] envSC
    (.seq [] [[("i", .base ⟨12⟩)], okScopeI, hIScope0]
      (.seq (hIBodyList.drop 6) envIH2ok hIFrame0))
private def scHeadCfg : Config :=
  .exec (.while (.boolLit true) isortScanBody) envSC scTail
private def scLoopK : Cont :=
  .loop (.boolLit true) isortScanBody envSC scTail
private def scChkBlk : Stmt :=
  .block #[]
    #[.ifThenElse
        (.greaterCmp
          (.indexGet (.var "s") (.sub (.var "i") (.intLit 1 .uint64)))
          (.indexGet (.var "s") (.var "i")))
        (.block #[] #[.seqn #[.assign (.var "ok") (.intLit 0 .uint64)]])
        (.seqn #[])]
private def scCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envSC)
    (.seq [scChkBlk] ([] :: envSC) scLoopK)
private def scEnv2 : LocalEnv := [] :: [] :: envSC
private def scIfK : Cont :=
  .ifK (.block #[] #[.seqn #[.assign (.var "ok") (.intLit 0 .uint64)]])
    (.seqn #[]) scEnv2 (.seq [] scEnv2 (.seq [] ([] :: envSC) scLoopK))
private def scGcK1 : Cont :=
  .strictK .greaterCmp [] [.indexGet (.var "s") (.var "i")] scEnv2 scIfK
private def scGcK2 (w1 : GoValue) : Cont :=
  .strictK .greaterCmp [w1] [] scEnv2 scIfK

/-- The scan-phase state: `ok` pinned 1, scan counter `iv`, flag. -/
private def σSC (n seed : Nat) (ivF : Int) (l : List Int) (iv : Int)
    (ffv : Bool) : ExecState :=
  σHOutT n seed l ivF false
    [(.base ⟨11⟩, ucell 1), (.base ⟨12⟩, ucell iv), (.base ⟨13⟩, bcell ffv)]
    14

/-- Post-subject → the scan head: `ok := 1` at 11, `i := 1` at 12,
the flag at 13. 42 steps (trace 735→777). -/
private theorem hR1_raw (n seed : Nat) (ivF : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 42 (σHOut n seed l ivF false) (.next hAfterCallK) ch
      = .ok (scHeadCfg, σSC n seed ivF l 1 true, ch) := by
  with_unfolding_all rfl

/-- Scan first-pass dispatch. -/
private theorem hsc_d0_raw (n seed : Nat) (ivF : Int) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 25 (σSC n seed ivF l iv true) scHeadCfg ch
      = .ok (.retV (.bool (decide (iv < ((n : Nat) : Int)))) scCmpK,
          σSC n seed ivF l iv false, ch) := by
  with_unfolding_all rfl

/-- Scan later-pass dispatch: `i++`, then the exit test. -/
private theorem hsc_d1_raw (n seed : Nat) (ivF : Int) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 29 (σSC n seed ivF l iv false) scHeadCfg ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < ((n : Nat) : Int)))) scCmpK,
          σSC n seed ivF l
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false, ch) := by
  with_unfolding_all rfl

/-- Scan check phase 1: test true → the `s[i-1]` read's apply point. -/
private theorem hsc_B1_raw (n seed : Nat) (ivF : Int) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 15 (σSC n seed ivF l iv false) (.retV (.bool true) scCmpK) ch
      = .ok (.retV (.int (IntKind.normalize .uint64 (iv - 1)) .uint64)
            (.strictK .indexGet [hISliceH n] [] scEnv2 scGcK1),
          σSC n seed ivF l iv false, ch) := by
  with_unfolding_all rfl

/-- Scan check phase 2: first element in → the `s[i]` apply. -/
private theorem hsc_B2_raw (n seed : Nat) (ivF : Int) (l : List Int)
    (iv : Int) (w1 : GoValue) (ch : Choices) :
    stepFnIter 5 (σSC n seed ivF l iv false) (.retV w1 scGcK1) ch
      = .ok (.retV (.int iv .uint64)
            (.strictK .indexGet [hISliceH n] [] scEnv2 (scGcK2 w1)),
          σSC n seed ivF l iv false, ch) := by
  with_unfolding_all rfl

/-- Scan check phase 3: comparison delivered at the `if`. -/
private theorem hsc_B3_raw (n seed : Nat) (ivF : Int) (l : List Int)
    (iv a b : Int) (ch : Choices) :
    stepFnIter 1 (σSC n seed ivF l iv false)
      (.retV (.int b .uint64) (scGcK2 (.int a .uint64))) ch
      = .ok (.retV (.bool (decide (b < a))) scIfK,
          σSC n seed ivF l iv false, ch) := by
  with_unfolding_all rfl

/-- Scan check phase 4 (the sorted case): else branch drains to the
loop head. -/
private theorem hsc_B4_raw (n seed : Nat) (ivF : Int) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 5 (σSC n seed ivF l iv false) (.retV (.bool false) scIfK) ch
      = .ok (scHeadCfg, σSC n seed ivF l iv false, ch) := by
  with_unfolding_all rfl

/-- One scan element read (`ik = .uint64` indices). -/
private theorem stepFn_read_σSC {n seed : Nat} {ivF : Int} {l : List Int}
    {iv : Int} {k : Nat} {K : Cont} {ch : Choices}
    (hk : k < n) (hlen : l.length = n) :
    stepFn (σSC n seed ivF l iv false)
      (.retV (.int ((k : Nat) : Int) .uint64)
        (.strictK .indexGet [hISliceH n] [] scEnv2 K)) ch
      = .ok (.retV (.int (l.getD k 0) .uint64) K,
          σSC n seed ivF l iv false, ch) :=
  stepFn_strict_apply
    (applyStrictOp_indexGet_slice (ik := .uint64) rfl
      (Nat.le_refl n) hk
      (by rw [Nat.zero_add]; exact getElem?_mapU l k (by omega)))

/-- One scan iteration from the exit-test's true delivery at `m ≥ 1`:
read `s[m-1]` and `s[m]` (sorted, so the check does NOT fire), return
to the head, dispatch, deliver the next test. 57 steps. -/
private theorem hsc_iter (n seed : Nat) (hn : n < 2 ^ 63) (ivF : Int)
    (l : List Int) (m : Nat) (h1 : 1 ≤ m) (hm : m < n)
    (hlen : l.length = n) (hsort : Sorted l)
    (ch : Choices) :
    stepFnIter 57 (σSC n seed ivF l ((m : Nat) : Int) false)
      (.retV (.bool true) scCmpK) ch
      = .ok (.retV (.bool (decide (((m + 1 : Nat) : Int) < ((n : Nat) : Int))))
            scCmpK,
          σSC n seed ivF l ((m + 1 : Nat) : Int) false, ch) := by
  have hB1 := hsc_B1_raw n seed ivF l ((m : Nat) : Int) ch
  rw [show (((m : Nat) : Int) - 1) = ((m - 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m - 1 : Nat) : Int)) (by omega) (by omega)] at hB1
  have hread1 := stepFn_read_σSC (n := n) (seed := seed) (ivF := ivF)
    (l := l) (iv := ((m : Nat) : Int)) (k := m - 1) (K := scGcK1)
    (ch := ch) (by omega) hlen
  have hB2 := hsc_B2_raw n seed ivF l ((m : Nat) : Int)
    (.int (l.getD (m - 1) 0) .uint64) ch
  have hread2 := stepFn_read_σSC (n := n) (seed := seed) (ivF := ivF)
    (l := l) (iv := ((m : Nat) : Int)) (k := m)
    (K := scGcK2 (.int (l.getD (m - 1) 0) .uint64)) (ch := ch) (by omega) hlen
  have hB3 := hsc_B3_raw n seed ivF l ((m : Nat) : Int)
    (l.getD (m - 1) 0) (l.getD m 0) ch
  rw [show (decide (l.getD m 0 < l.getD (m - 1) 0)) = false from
    decide_eq_false (by
      have := hsort (m - 1) m (by omega) (by omega)
      omega)] at hB3
  have hB4 := hsc_B4_raw n seed ivF l ((m : Nat) : Int) ch
  have hd1 := hsc_d1_raw n seed ivF l ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)] at hd1
  have h1' := stepFnIter_chain hB1 (stepFnIter_one hread1)
  have h2 := stepFnIter_chain h1' hB2
  have h3 := stepFnIter_chain h2 (stepFnIter_one hread2)
  have h4 := stepFnIter_chain h3 hB3
  have h5 := stepFnIter_chain h4 hB4
  exact stepFnIter_chain h5 hd1

/-- **The scan loop**: from the exit-test delivery at `m ≥ 1` the run
reaches the exit-test's FALSE delivery at some final counter `mf`,
within `57·μ` steps (uniform in `n = 0` — the first test already
fails there). -/
private theorem hscan_loop (n seed : Nat) (hn : n < 2 ^ 63) (ivF : Int)
    (l : List Int) (hlen : l.length = n) (hsort : Sorted l) :
    ∀ μ m, μ = n - m → 1 ≤ m → ∀ ch : Choices,
    ∃ (k mf : Nat), k ≤ 57 * μ ∧ 1 ≤ mf ∧
      stepFnIter k (σSC n seed ivF l ((m : Nat) : Int) false)
        (.retV (.bool (decide (((m : Nat) : Int) < ((n : Nat) : Int))))
          scCmpK) ch
        = .ok (.retV (.bool false) scCmpK,
            σSC n seed ivF l ((mf : Nat) : Int) false, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hμ h1 ch
    rcases Nat.lt_or_ge m n with hlt | hge
    · rw [show (decide (((m : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      obtain ⟨k, mf, hk, hmf, hrun⟩ := ih (n - (m + 1)) (by omega) (m + 1)
        rfl (by omega) ch
      exact ⟨57 + k, mf, by omega, hmf,
        stepFnIter_chain (hsc_iter n seed hn ivF l m h1 hlt hlen hsort ch)
          hrun⟩
    · rw [show (decide (((m : Nat) : Int) < ((n : Nat) : Int))) = false from
        decide_eq_false (by exact_mod_cast (by omega : ¬ (m < n)))]
      exact ⟨0, m, by omega, h1, rfl⟩

/-! ## The test phase, part 2: the rebuild (`t := make; t[i] = seed*(i+1)`
— the setup machinery re-instantiated at the `t` placement, cells
14–18, backing at 15) -/

private def c5Scope : Scope :=
  [("$c5", .base ⟨14⟩), ("ok", .base ⟨11⟩), ("s", .base ⟨5⟩),
   ("$c4", .base ⟨3⟩)]
private def envC5 : LocalEnv := [c5Scope, hIScope0]
private def hIAfterMs2K : Cont := .seq (hIBodyList.drop 7) envC5 hIFrame0
private def hIMs2K : Cont :=
  .stmtOpK (.makeSlice (.int .uint64) false) 1 [.addr (.base ⟨14⟩)] []
    envC5 hIAfterMs2K

/-- The `t` handle over the backing array at its fixed address 15. -/
private abbrev hTHandleCell (n : Nat) : HeapCell :=
  ⟨some (.slice (.int .uint64)), .slice ⟨some (.base ⟨15⟩), 0, n, n⟩⟩
private abbrev hTSliceH (n : Nat) : GoValue :=
  .slice ⟨some (.base ⟨15⟩), 0, n, n⟩

/-- Pre-makeSlice: `$c5` declared (default slice) at 14. -/
private def σSCc5 (n seed : Nat) (ivF : Int) (l : List Int) (sciv : Int) :
    ExecState :=
  σHOutT n seed l ivF false
    [(.base ⟨11⟩, ucell 1), (.base ⟨12⟩, ucell sciv), (.base ⟨13⟩, bcell false),
     (.base ⟨14⟩, ⟨some (.slice (.int .uint64)), .slice ⟨none, 0, 0, 0⟩⟩)]
    15

/-- Post-makeSlice: the `t` backing (zeroed) at 15, the handle in 14. -/
private def σMs2 (n seed : Nat) (ivF : Int) (l : List Int) (sciv : Int) :
    ExecState :=
  σHOutT n seed l ivF false
    [(.base ⟨11⟩, ucell 1), (.base ⟨12⟩, ucell sciv), (.base ⟨13⟩, bcell false),
     (.base ⟨14⟩, hTHandleCell n),
     (.base ⟨15⟩, arrCell n (List.replicate n 0))]
    16

/-- Scan exit: test false → break unwinding → `$c5` declared → the
second makeSlice's length delivered. 15 steps (trace 973→988). -/
private theorem hsc_X_raw (n seed : Nat) (ivF : Int) (l : List Int)
    (sciv : Int) (ch : Choices) :
    stepFnIter 15 (σSC n seed ivF l sciv false)
      (.retV (.bool false) scCmpK) ch
      = .ok (.retV (.int ((n : Nat) : Int) .uint64) hIMs2K,
          σSCc5 n seed ivF l sciv, ch) := by
  with_unfolding_all rfl

/-- **The second makeSlice apply at symbolic length** (the `t`
backing). -/
private theorem hstep_Ims2 (n seed : Nat) (ivF : Int) (l : List Int)
    (sciv : Int) (ch : Choices) :
    stepFn (σSCc5 n seed ivF l sciv)
      (.retV (.int ((n : Nat) : Int) .uint64) hIMs2K) ch
      = .ok (.next hIAfterMs2K, σMs2 n seed ivF l sciv, ch) := by
  have hb := GoLean.Iris.buildDefaultArrayValue_int (σSCc5 n seed ivF l sciv)
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
  have happly : applyStmtOp (σSCc5 n seed ivF l sciv) ch
      (.makeSlice (.int .uint64) false) 1
      [.addr (.base ⟨14⟩), .int ((n : Nat) : Int) .uint64]
      = .ok (σMs2 n seed ivF l sciv, ch) := by
    simp only [applyStmtOp, applyStmtOpCore, valueAsInt, valueAsLoc,
      hnn1, hnn2, hb, Bind.bind, Except.bind, pure, Except.pure]
    rw [if_neg (Nat.lt_irrefl n)]
    with_unfolding_all rfl
  exact stepFn_stmtOp_apply
    (done := [.addr (.base ⟨14⟩)]) (v := .int ((n : Nat) : Int) .uint64)
    happly

private def tScope : Scope :=
  [("t", .base ⟨16⟩), ("$c5", .base ⟨14⟩), ("ok", .base ⟨11⟩),
   ("s", .base ⟨5⟩), ("$c4", .base ⟨3⟩)]
private def envT : LocalEnv := [tScope, hIScope0]
private def envRB : LocalEnv :=
  [[("$forFirst", .base ⟨18⟩)], [("i", .base ⟨17⟩)], tScope, hIScope0]

/-- The rebuild loop's desugared body (the multiplicative store to `t`). -/
abbrev isortRebuildBody : Stmt :=
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
                (.addr (.indexAddr (.var "t") (.var "i")))
                (.mul (.var "seed")
                  (.add (.var "i") (.intLit 1 .uint64)))]]]

private def rbTail : Cont :=
  .seq [] envRB
    (.seq [] [[("i", .base ⟨17⟩)], tScope, hIScope0]
      (.seq (hIBodyList.drop 9) envT hIFrame0))
private def rbHeadCfg : Config :=
  .exec (.while (.boolLit true) isortRebuildBody) envRB rbTail
private def rbLoopK : Cont :=
  .loop (.boolLit true) isortRebuildBody envRB rbTail
private def rbStoreBlk : Stmt :=
  .block #[]
    #[.seqn
        #[.assign
            (.addr (.indexAddr (.var "t") (.var "i")))
            (.mul (.var "seed")
              (.add (.var "i") (.intLit 1 .uint64)))]]
private def rbCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envRB)
    (.seq [rbStoreBlk] ([] :: envRB) rbLoopK)
private def rbStoreTail : Cont :=
  .seq [] ([] :: [] :: envRB) (.seq [] ([] :: envRB) rbLoopK)

/-- The rebuild-loop state family (fixed cells 0–18). -/
private def σRB (n seed : Nat) (ivF sciv : Int) (l tl : List Int) (iv : Int)
    (ffv : Bool) : ExecState :=
  σHOutT n seed l ivF false
    [(.base ⟨11⟩, ucell 1), (.base ⟨12⟩, ucell sciv), (.base ⟨13⟩, bcell false),
     (.base ⟨14⟩, hTHandleCell n), (.base ⟨15⟩, arrCell n tl),
     (.base ⟨16⟩, hTHandleCell n), (.base ⟨17⟩, ucell iv),
     (.base ⟨18⟩, bcell ffv)]
    19

/-- makeSlice done → `t := $c5`, `i := 0`, the flag block → the rebuild
loop head. 42 steps (trace 989→1031). -/
private theorem hR2_raw (n seed : Nat) (ivF : Int) (l : List Int)
    (sciv : Int) (ch : Choices) :
    stepFnIter 42 (σMs2 n seed ivF l sciv) (.next hIAfterMs2K) ch
      = .ok (rbHeadCfg,
          σRB n seed ivF sciv l (List.replicate n 0) 0 true, ch) := by
  with_unfolding_all rfl

/-- Rebuild first-pass dispatch. -/
private theorem hrb_d0_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 25 (σRB n seed ivF sciv l tl iv true) rbHeadCfg ch
      = .ok (.retV (.bool (decide (iv < ((n : Nat) : Int)))) rbCmpK,
          σRB n seed ivF sciv l tl iv false, ch) := by
  with_unfolding_all rfl

/-- Rebuild body: test true → the store point of `t[i] = seed*(i+1)`. -/
private theorem hrb_body_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 22 (σRB n seed ivF sciv l tl iv false)
      (.retV (.bool true) rbCmpK) ch
      = .ok (.next (.storeK
            [.chain (hTSliceH n) [.int iv .uint64] [.index]]
            [.int (IntKind.normalize .uint64
                (((seed : Nat) : Int) * IntKind.normalize .uint64 (iv + 1)))
              .uint64]
            (.seqn #[]) ([] :: [] :: envRB) rbStoreTail),
          σRB n seed ivF sciv l tl iv false, ch) := by
  with_unfolding_all rfl

/-- The rebuild element store, cleaned. -/
private theorem hstep_rbstore (n seed : Nat) (ivF sciv : Int)
    (l tl : List Int) (i : Nat) (w : Int) (hi : i < n) (hlen : tl.length = n)
    (hl : ∀ v ∈ tl, 0 ≤ v ∧ v < 2 ^ 64) (hw : 0 ≤ w ∧ w < 2 ^ 64)
    (iv : Int) (ch : Choices) :
    stepFnIter 1 (σRB n seed ivF sciv l tl iv false)
      (.next (.storeK [.chain (hTSliceH n) [.int ((i : Nat) : Int) .uint64]
          [.index]]
        [.int w .uint64] (.seqn #[]) ([] :: [] :: envRB) rbStoreTail))
      ch
      = .ok (.next (.storeK [] [] (.seqn #[]) ([] :: [] :: envRB)
            rbStoreTail),
          σRB n seed ivF sciv l (tl.set i w) iv false, ch) := by
  have hstore := storeTarget_slice_u64 (σ := σRB n seed ivF sciv l tl iv false)
    (a := ⟨15⟩) (off := 0) (len := n) (cap := n) (i := i) (n := n)
    (ik := .uint64) (l := tl) (w := w) rfl (Nat.le_refl n) hi
    (by omega) hlen hl hw
  rw [Nat.zero_add] at hstore
  exact stepFnIter_one (stepFn_store_step hstore)

/-- Rebuild dispatch (later passes): store done → head → `i := i + 1`
→ the exit test delivery. -/
private theorem hrb_d1_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 34 (σRB n seed ivF sciv l tl iv false)
      (.next (.storeK [] [] (.seqn #[]) ([] :: [] :: envRB)
        rbStoreTail)) ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < ((n : Nat) : Int)))) rbCmpK,
          σRB n seed ivF sciv l tl
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false, ch) := by
  with_unfolding_all rfl

/-- **The rebuild loop**: exactly `57·(n-i)` steps re-materialize the
wrapped multiplicative family at the `t` placement (the setup
induction, re-instantiated). -/
private theorem hrebuild_loop (n seed : Nat) (hn : n < 2 ^ 63)
    (ivF sciv : Int) (l : List Int) :
    ∀ μ i, μ = n - i → i ≤ n → ∀ ch : Choices,
    stepFnIter (57 * (n - i))
      (σRB n seed ivF sciv l (isFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false)
      (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
        rbCmpK) ch
      = .ok (.retV (.bool (decide (((n : Nat) : Int) < ((n : Nat) : Int))))
            rbCmpK,
          σRB n seed ivF sciv l (isFamily n seed) ((n : Nat) : Int) false,
          ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro i hμ hin ch
    rcases Nat.lt_or_ge i n with hlt | hge
    · rw [show (decide (((i : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      have h1 := hrb_body_raw n seed ivF sciv l
        (isFamily i seed ++ List.replicate (n - i) 0) ((i : Nat) : Int) ch
      rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
        unorm_of_range (by omega)
          (by omega : ((i + 1 : Nat) : Int) < 2 ^ 64),
        show ((seed : Nat) : Int) * ((i + 1 : Nat) : Int)
          = ((seed * (i + 1) : Nat) : Int) from
          (Int.natCast_mul seed (i + 1)).symm,
        unorm_nat_mod (seed * (i + 1))] at h1
      have h2 := hstep_rbstore n seed ivF sciv l
        (isFamily i seed ++ List.replicate (n - i) 0) i
        (((seed * (i + 1)) % 2 ^ 64 : Nat) : Int) hlt
        (by rw [List.length_append, isFamily_length, List.length_replicate]
            omega)
        (isFamilyZ_range (by omega))
        ⟨by omega, by
          have := Nat.mod_lt (seed * (i + 1)) (y := 2 ^ 64) (by omega)
          omega⟩
        ((i : Nat) : Int) ch
      rw [isFamily_set hlt] at h2
      have h3 := hrb_d1_raw n seed ivF sciv l
        (isFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
        ((i : Nat) : Int) ch
      rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
        unorm_of_range (by omega)
          (by omega : ((i + 1 : Nat) : Int) < 2 ^ 64),
        unorm_of_range (by omega)
          (by omega : ((i + 1 : Nat) : Int) < 2 ^ 64)] at h3
      have hrec := ih (n - (i + 1)) (by omega) (i + 1) rfl (by omega) ch
      have hc := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h1 h2)
        h3) hrec
      rw [show 22 + 1 + 34 + 57 * (n - (i + 1)) = 57 * (n - i) from by
        omega] at hc
      exact hc
    · have hEq : i = n := by omega
      subst hEq
      simp only [Nat.sub_self, Nat.mul_zero, List.replicate_zero,
        List.append_nil]
      rfl

/-! ## The test phase, part 3: the O(n²) count loops (the permutation
check). The outer count loop re-allocates `cs`/`ct`/`j`/`$forFirst`
every pass — the SECOND frame-rebase layer (threshold 21, retire FOUR
cells per pass). Count cells: 19 = the count `i`, 20 = its flag;
tight pass placement 21 = `cs`, 22 = `ct`, 23 = `j`, 24 = its flag. -/

private def envCNT : LocalEnv :=
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

private def cntTail : Cont :=
  .seq [] envCNT
    (.seq [] [[("i", .base ⟨19⟩)], tScope, hIScope0]
      (.seq (hIBodyList.drop 10) envT hIFrame0))
private def cntHeadCfg : Config :=
  .exec (.while (.boolLit true) isortCountOuterBody) envCNT cntTail
private def cntLoopK : Cont :=
  .loop (.boolLit true) isortCountOuterBody envCNT cntTail
private def cntCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envCNT)
    (.seq [isortCountPassBlk] ([] :: envCNT) cntLoopK)

private def envP : LocalEnv :=
  [("ct", .base ⟨22⟩), ("cs", .base ⟨21⟩)] :: [] :: envCNT
private def envCJ : LocalEnv :=
  [("$forFirst", .base ⟨24⟩)] :: [("j", .base ⟨23⟩)] :: envP
private def cntNeqIf : Stmt :=
  .ifThenElse (.neqCmp (.int .uint64) (.var "cs") (.var "ct"))
    (.block #[] #[.seqn #[.assign (.var "ok") (.intLit 0 .uint64)]])
    (.seqn #[])
private def cntInTail : Cont :=
  .seq [] envCJ
    (.seq [] ([("j", .base ⟨23⟩)] :: envP)
      (.seq [cntNeqIf] envP (.seq [] ([] :: envCNT) cntLoopK)))
private def cntInHeadCfg : Config :=
  .exec (.while (.boolLit true) isortCountInnerBody) envCJ cntInTail
private def cntInLoopK : Cont :=
  .loop (.boolLit true) isortCountInnerBody envCJ cntInTail
private def cntChkBlk : Stmt :=
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
private def cntInCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envCJ)
    (.seq [cntChkBlk] ([] :: envCJ) cntInLoopK)
private def env2C : LocalEnv := [] :: [] :: envCJ
private def cntIf2Stmt : Stmt :=
  .ifThenElse
    (.eqCmp (.int .uint64)
      (.indexGet (.var "t") (.var "j"))
      (.indexGet (.var "t") (.var "i")))
    (.block #[]
      #[.assign (.var "ct") (.add (.var "ct") (.intLit 1 .uint64))])
    (.seqn #[])
private def cntIf1K : Cont :=
  .ifK (.block #[]
      #[.assign (.var "cs") (.add (.var "cs") (.intLit 1 .uint64))])
    (.seqn #[]) env2C
    (.seq [cntIf2Stmt] env2C (.seq [] ([] :: envCJ) cntInLoopK))
private def cntIf2K : Cont :=
  .ifK (.block #[]
      #[.assign (.var "ct") (.add (.var "ct") (.intLit 1 .uint64))])
    (.seqn #[]) env2C
    (.seq [] env2C (.seq [] ([] :: envCJ) cntInLoopK))
private def cntEq1K1 : Cont :=
  .strictK (.eqCmp (.int .uint64)) []
    [.indexGet (.var "t") (.var "i")] env2C cntIf1K
private def cntEq1K2 (w : GoValue) : Cont :=
  .strictK (.eqCmp (.int .uint64)) [w] [] env2C cntIf1K
private def cntEq2K1 : Cont :=
  .strictK (.eqCmp (.int .uint64)) []
    [.indexGet (.var "t") (.var "i")] env2C cntIf2K
private def cntEq2K2 (w : GoValue) : Cont :=
  .strictK (.eqCmp (.int .uint64)) [w] [] env2C cntIf2K
private def cntNeqIfK : Cont :=
  .ifK (.block #[] #[.seqn #[.assign (.var "ok") (.intLit 0 .uint64)]])
    (.seqn #[]) envP (.seq [] envP (.seq [] ([] :: envCNT) cntLoopK))

/-- The count-phase outer state family, TAIL-PARAMETRIC (fixed cells
0–20: the harness cells, the parked scan/rebuild counters, the count
counter at 19 and flag at 20). -/
private def σCntOutT (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ : Int) (ffv : Bool) (tail : Heap) (na : Nat) : ExecState :=
  σHOutT n seed l ivF false
    ([(.base ⟨11⟩, ucell 1), (.base ⟨12⟩, ucell sciv),
      (.base ⟨13⟩, bcell false), (.base ⟨14⟩, hTHandleCell n),
      (.base ⟨15⟩, arrCell n tl), (.base ⟨16⟩, hTHandleCell n),
      (.base ⟨17⟩, ucell ((n : Nat) : Int)), (.base ⟨18⟩, bcell false),
      (.base ⟨19⟩, ucell civ), (.base ⟨20⟩, bcell ffv)] ++ tail)
    na

/-- The tight 21-cell count-outer state. -/
private def σCntOut (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ : Int) (ffv : Bool) : ExecState :=
  σCntOutT n seed ivF sciv l tl civ ffv [] 21

/-- The tight 25-cell in-pass count state (`cs`/`ct`/`j`/flag at
21–24). -/
private def σCntIn (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
    (civ csv ctv jv : Int) (jffv : Bool) : ExecState :=
  σCntOutT n seed ivF sciv l tl civ false
    [(.base ⟨21⟩, ucell csv), (.base ⟨22⟩, ucell ctv),
     (.base ⟨23⟩, ucell jv), (.base ⟨24⟩, bcell jffv)]
    25

/-- The terminal state: verdict 1 delivered to the result cell 2. -/
private def σCntEnd (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
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
private theorem hcnt_entry_raw (n seed : Nat) (ivF sciv : Int)
    (l tl : List Int) (ch : Choices) :
    stepFnIter 35 (σRB n seed ivF sciv l tl ((n : Nat) : Int) false)
      (.retV (.bool false) rbCmpK) ch
      = .ok (cntHeadCfg, σCntOut n seed ivF sciv l tl 0 true, ch) := by
  with_unfolding_all rfl

/-- Count outer first-pass dispatch (tail-parametric). -/
private theorem hcnt_d0_raw (n seed : Nat) (ivF sciv : Int) (l tl : List Int)
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
private def cntSpec (v : Int) : List Int → Nat
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

private theorem cntSpec_eq_count (v : Int) (l : List Int) :
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

private def ρ21 (d : Nat) : Nat → Nat := fun x => if x < 21 then x else x + d

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
private def bump4C : Loc → Loc
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
private theorem frameSim_zero21 (n seed : Nat) (ivF sciv : Int)
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
private theorem hcnt_outer_loop (n seed : Nat) (h63 : n < 2 ^ 63)
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

/-! ## Composition: the remainder run, the full harness run, and the
§11 headline -/

private theorem renCfg_stop11 (d : Nat) :
    renameConfig (ρ11 d) (.next .stop) = .next .stop := rfl

/-- **The remainder run** (post-subject, canonical placement): from the
post-subject anchor the scan, rebuild, and count phases run to the
DRIVER TERMINAL with the verdict 1 in the result cell — within
`(110·n + 220)·n + 114·n + 350` steps. -/
private theorem hremainder_runs (n seed : Nat) (hn : n < 2 ^ 63) (ivF : Int)
    (ch : Choices) :
    ∃ (k : Nat) (σf : ExecState),
      k ≤ (110 * n + 220) * n + 114 * n + 350 ∧
      stepFnIter k (σHOut n seed (sortSpec (isFamily n seed)) ivF false)
        (.next hAfterCallK) ch
        = .ok (.next .stop, σf, ch)
      ∧ Heap.lookup σf.heap (.base ⟨2⟩) = some (ucell 1) := by
  have hll : (sortSpec (isFamily n seed)).length = n := by
    rw [sortSpec_length, isFamily_length]
  have htl : (isFamily n seed).length = n := isFamily_length n seed
  have hsort := sortSpec_sorted (isFamily n seed)
  have hcount : ∀ v, cntSpec v (sortSpec (isFamily n seed))
      = cntSpec v (isFamily n seed) := fun v => by
    rw [cntSpec_eq_count, cntSpec_eq_count, sortSpec_count]
  -- the scan
  have hR1 := hR1_raw n seed ivF (sortSpec (isFamily n seed)) ch
  have hd0 := hsc_d0_raw n seed ivF (sortSpec (isFamily n seed)) 1 ch
  obtain ⟨k1, mf, hk1, hmf, hscan⟩ := hscan_loop n seed hn ivF
    (sortSpec (isFamily n seed)) hll hsort (n - 1) 1 rfl (by omega) ch
  rw [show ((1 : Nat) : Int) = (1 : Int) from rfl] at hscan
  -- scan exit → the second makeSlice → the rebuild entry
  have hX := hsc_X_raw n seed ivF (sortSpec (isFamily n seed))
    ((mf : Nat) : Int) ch
  have hms := hstep_Ims2 n seed ivF (sortSpec (isFamily n seed))
    ((mf : Nat) : Int) ch
  have hR2 := hR2_raw n seed ivF (sortSpec (isFamily n seed))
    ((mf : Nat) : Int) ch
  have hrb0 := hrb_d0_raw n seed ivF ((mf : Nat) : Int)
    (sortSpec (isFamily n seed)) (List.replicate n 0) 0 ch
  have hrb := hrebuild_loop n seed hn ivF ((mf : Nat) : Int)
    (sortSpec (isFamily n seed)) (n - 0) 0 rfl (by omega) ch
  rw [show isFamily 0 seed ++ List.replicate (n - 0) (0 : Int)
        = List.replicate n 0 from by simp [isFamily],
    show ((0 : Nat) : Int) = (0 : Int) from rfl] at hrb
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hrb
  -- the count entry
  have hce := hcnt_entry_raw n seed ivF ((mf : Nat) : Int)
    (sortSpec (isFamily n seed)) (isFamily n seed) ch
  have hcd0 := hcnt_d0_raw n seed ivF ((mf : Nat) : Int)
    (sortSpec (isFamily n seed)) (isFamily n seed) 0 [] 21 ch
  -- the count loop
  obtain ⟨k2, σf, hk2, hcout, hread⟩ := hcnt_outer_loop n seed hn ivF
    ((mf : Nat) : Int) (sortSpec (isFamily n seed)) (isFamily n seed)
    hll htl hcount (n - 0) 0
    (σCntOut n seed ivF ((mf : Nat) : Int) (sortSpec (isFamily n seed))
      (isFamily n seed) 0 false) [] rfl (by omega)
    (frameSim_zero21 n seed ivF ((mf : Nat) : Int)
      (sortSpec (isFamily n seed)) (isFamily n seed) 0 false) ch
  rw [show ((0 : Nat) : Int) = (0 : Int) from rfl] at hcout
  -- the chain
  have h1 := stepFnIter_chain hR1 hd0
  have h2 := stepFnIter_chain h1 hscan
  have h3 := stepFnIter_chain h2 hX
  have h4 := stepFnIter_chain h3 (stepFnIter_one hms)
  have h5 := stepFnIter_chain h4 hR2
  have h6 := stepFnIter_chain h5 hrb0
  have h7 := stepFnIter_chain h6 hrb
  have h8 := stepFnIter_chain h7 hce
  have h9 := stepFnIter_chain h8 hcd0
  have h10 := stepFnIter_chain h9 hcout
  refine ⟨42 + 25 + k1 + 15 + 1 + 42 + 25 + 57 * (n - 0) + 35 + 25 + k2,
    σf, ?_, h10, hread⟩
  have hmulc : (110 * n + 220) * (n - 0) ≤ (110 * n + 220) * n :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- **The full harness run**: from the cleaned prelude state, the
whole three-phase harness completes at the driver terminal with the
verdict 1 in the result cell — within
`(92·n+160)·n + (110·n+220)·n + 285·n + 505` steps. -/
private theorem isortH_runs (n seed : Nat) (hn : n < 2 ^ 63)
    (ch : Choices) :
    ∃ (k : Nat) (σf : ExecState),
      k ≤ (92 * n + 160) * n + (110 * n + 220) * n + 285 * n + 505 ∧
      stepFnIter k (σIStart n seed)
        (.exec isortHarnessFunc.body hIEnv0 (.frame [] [] [] [] .stop false))
        ch
        = .ok (.next .stop, σf, ch)
      ∧ Heap.lookup σf.heap (.base ⟨2⟩) = some (ucell 1) := by
  -- the prelude → the setup loop
  have hA1 := hseg_IA1_raw n seed ch
  have hmk := hstep_ImakeSlice n seed ch
  have hA2 := hseg_IA2_raw n seed ch
  have hd0 := hsegISU_d0_raw n (seed : Int) 0 (List.replicate n 0) ch
  have hsetup := hIsetup_loop n seed hn (n - 0) 0 rfl (by omega) ch
  rw [show isFamily 0 seed ++ List.replicate (n - 0) (0 : Int)
        = List.replicate n 0 from by simp [isFamily],
    show ((0 : Nat) : Int) = (0 : Int) from rfl] at hsetup
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hsetup
  -- the bridge into the subject
  have hbr := hbridge_raw n seed (isFamily n seed) ch
  have hO0 := hseg_O0_raw n seed (isFamily n seed) 1 [] 11 ch
  have hlenapp : stepFn (σHOutT n seed (isFamily n seed) 1 false [] 11)
      (.retV (hISliceH n) (hLenTestK 1)) ch
      = .ok (.retV (.int ((n : Nat) : Int) .int)
          (.strictK .lessCmp [.int 1 .int] [] ([] :: envHO) hOuterCmpCont),
        σHOutT n seed (isFamily n seed) 1 false [] 11, ch) :=
    stepFn_strict_apply (done := [])
      (applyStrictOp_len_slice (Nat.le_refl n))
  have hOB := hseg_OB_raw n seed (isFamily n seed) 1 [] 11 ch
  -- the subject loop from pass 0 (trivial frame)
  have hFS0 : FrameSim (ρ11 (2 * 0)) 11 (11 + 2 * 0) []
      (σHOut n seed (sortPrefix (isFamily n seed) (0 + 1))
        ((0 + 1 : Nat) : Int) false)
      (σHOut n seed (isFamily n seed) 1 false) := by
    show FrameSim (ρ11 0) 11 11 []
      (σHOut n seed (sortPrefix (isFamily n seed) 1) ((1 : Nat) : Int) false)
      (σHOut n seed (isFamily n seed) 1 false)
    rw [sortPrefix_one]
    exact frameSim_zero11 n seed (isFamily n seed) 1 false
  obtain ⟨k1, σA', d, fr', ivF, hk1, hsubj, hFSd⟩ := hs_outer_loop
    (isFamily n seed) n seed (isFamily_length n seed).symm
    (isFamily_range n seed) hn (n - (0 + 1)) 0
    (σHOut n seed (isFamily n seed) 1 false) [] rfl hFS0 ch
  rw [show ((0 + 1 : Nat) : Int) = (1 : Int) from rfl] at hsubj
  -- the remainder, transferred through the surviving frame simulation
  obtain ⟨k2, σR, hk2, hrem, hreadR⟩ := hremainder_runs n seed hn ivF ch
  obtain ⟨σf, hrunT, hFSf⟩ := transfer_seg11 hFSd hrem
    (renCfg_hanchor d) (renCfg_stop11 d)
  have hread := hFSf.lookup_some (l := .base ⟨2⟩) (c := ucell 1) hreadR
  have hren : renameLoc (ρ11 d) (.base ⟨2⟩) = .base ⟨2⟩ := by
    simp [renameLoc, ρ11]
  rw [hren] at hread
  -- the chain
  have h1 := stepFnIter_chain hA1 (stepFnIter_one hmk)
  have h2 := stepFnIter_chain h1 hA2
  have h3 := stepFnIter_chain h2 hd0
  have h4 := stepFnIter_chain h3 hsetup
  have h5 := stepFnIter_chain h4 hbr
  have h6 := stepFnIter_chain h5 hO0
  have h7 := stepFnIter_chain h6 (stepFnIter_one hlenapp)
  have h8 := stepFnIter_chain h7 hOB
  have h9 := stepFnIter_chain h8 hsubj
  have h10 := stepFnIter_chain h9 hrunT
  refine ⟨10 + 1 + 42 + 25 + 57 * (n - 0) + 40 + 25 + 1 + 1 + k1 + k2,
    σf, ?_, h10, hread⟩
  have hmuls : (92 * n + 160) * (n - (0 + 1)) ≤ (92 * n + 160) * n :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## The user-facing statement (§11) -/

/-- **THE HEADLINE (§11 harness form)**: for every `n < 2^63` (Go's
`int` domain for lengths — `make([]uint64, n)` panics past it) and
every `seed < 2^64` (the full uint64 domain), running the three-phase
Go harness `isort_harness(n, seed)` through the machine's native
function entry — empty-heap state, both arguments at the call
boundary — completes normally past one fuel bound
(`N = (92·n+160)·n + (110·n+220)·n + 285·n + 505` — quadratic: the
count loops are O(n²)), at every nondeterminism-choice stream, and
RETURNS the verdict 1: the test phase, IN GO and inside the verified
footprint, checked that `insertionSort` left the wrapped
multiplicative family `[seed·1, seed·2, …, seed·n] (mod 2^64)` sorted
AND a permutation of the rebuilt family (the count-based check, both
directions folded into `ok`).

INPUT-FAMILY HONESTY (§11, recorded): the quantification is over the
scalars `(n, seed)` — the input family `isFamily n seed`, honestly
weaker than ∀xs over arbitrary slice contents (the choice-consuming
input pick is designed, not built; `isort_framed` above keeps the ∀xs
claim proof-side). The wrapping family is deliberate: `seed·(i+1)`
wraps at `2^64`, so the family covers duplicates and non-monotone
orders — exactly the interesting sort inputs — and the corpus oracle
rows exercise the same harness at concrete arguments. -/
theorem isort_ok (n seed : Nat) (hn : n < 2 ^ 63) (hseed : seed < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel isortLowered.typeDefs.toList
          isortLowered.funcs isortHarnessFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
          isortLowered.methods ch
        = .ok { values := #[.int 1 .uint64] } := by
  refine ⟨(92 * n + 160) * n + (110 * n + 220) * n + 285 * n + 505,
    fun fuel hfuel ch => ?_⟩
  obtain ⟨k, σf, hk, hrun, hlook⟩ := isortH_runs n seed hn ch
  have hσ : σIH0 ((n : Nat) : Int) ((seed : Nat) : Int) = σIStart n seed := by
    simp only [σIH0, σIStart, ucellU, ucell,
      unorm_of_range (v := ((n : Nat) : Int)) (by omega) (by omega),
      unorm_of_range (v := ((seed : Nat) : Int)) (by omega) (by omega)]
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [iharness_entry_eq, hσ, hfold, runConfig_next_stop]
  have hload : loadMany σf [.base ⟨2⟩] = .ok [.int 1 .uint64] := by
    simp [loadMany, loadLoc, hlook, ucell, pure, Except.pure, Bind.bind,
      Except.bind]
  simp [hload, Bind.bind, Except.bind, pure, Except.pure]

/-- **The D1 run-conditioned twin**: any successful completion of the
harness entry, at any fuel and any choice stream, returns the verdict
1 — derived from `isort_ok` via `harness_readout_of_total`. -/
theorem isort_readout (n seed : Nat) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) :
    ∀ (fuel : Nat) (ch : Choices) (r : Result),
      runFunctionWithContextM fuel isortLowered.typeDefs.toList
          isortLowered.funcs isortHarnessFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
          isortLowered.methods ch
        = .ok r →
      r = { values := #[.int 1 .uint64] } :=
  harness_readout_of_total (isort_ok n seed hn hseed)

end GoLean.Examples.InsertionSort
