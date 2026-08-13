import GoLeanProofs.Examples.InsertionSortProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId

/-!
# Verified example: in-place insertion sort — NESTED loops
(verified-examples slice 2c, 2026-08-13)

The nested-loop exemplar of the §9 memory-input form (design note
`docs/2026-08-12_example-spec-form.md` §9): the Go program is the
canonical corpus source `Corpus/coverage/exec/examples/isort/main.go`
(differentially green against `go run`, 8 oracle rows incl. duplicates
and already/reverse-sorted inputs); `isortLowered` is its pinned
frontend lowering (`scripts/check-golden`).

The user-facing statement is `isort_ok` — reverse's §9e headline shape
on the sorting claim: the backing cell ends holding `sortSpec xs`, a
readable structural insertion sort whose support corollaries
(`sortSpec_sorted`, `sortSpec_count`, `sortSpec_length`) make the
"sorted permutation" reading a theorem, not a naming convention.

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

/-! ## Generic single-step glue (private copies — reverse's pattern) -/

private theorem stepFnIter_one {σ : ExecState} {c : Config} {ch : Choices}
    {r : Config × ExecState × Choices}
    (h : stepFn σ c ch = .ok r) : stepFnIter 1 σ c ch = .ok r := by
  obtain ⟨c', σ', ch'⟩ := r
  simp [stepFnIter, h, Bind.bind, Except.bind]

/-- The strict-apply machine step, conditioned on the op fact. -/
private theorem stepFn_strict_apply {σ σ' : ExecState} {op : StrictOp}
    {done : List GoValue} {v out : GoValue} {env : LocalEnv} {k : Cont}
    {ch : Choices}
    (h : applyStrictOp σ op (v :: done).reverse = .ok (out, σ')) :
    stepFn σ (.retV v (.strictK op done [] env k)) ch
      = .ok (.retV out k, σ', ch) := by
  simp only [stepFn]
  rw [h]
  rfl

/-- The phase-2 store machine step, conditioned on the store fact. -/
private theorem stepFn_store_step {σ σ' : ExecState} {r : TargetRef}
    {val : GoValue} {rs : List TargetRef} {vs : List GoValue} {body : Stmt}
    {env : LocalEnv} {k : Cont} {ch : Choices}
    (h : storeTarget σ r val = .ok σ') :
    stepFn σ (.next (.storeK (r :: rs) (val :: vs) body env k)) ch
      = .ok (.next (.storeK rs vs body env k), σ', ch) := by
  simp only [stepFn]
  rw [h]
  rfl

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

private theorem getD_mem {xs : List Int} {k : Nat} (hk : k < xs.length) :
    xs.getD k 0 ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  exact List.getElem_mem hk

private theorem mem_set_of_mem {l : List Int} {i : Nat} {w v : Int}
    (h : v ∈ l.set i w) : v = w ∨ v ∈ l := by
  induction l generalizing i with
  | nil => simp [List.set] at h
  | cons x rest ih =>
      cases i with
      | zero =>
          simp only [List.set, List.mem_cons] at h
          rcases h with h | h
          · exact .inl h
          · exact .inr (by simp [h])
      | succ n =>
          simp only [List.set, List.mem_cons] at h
          rcases h with h | h
          · exact .inr (by simp [h])
          · rcases ih h with h | h
            · exact .inl h
            · exact .inr (by simp [h])

private theorem getElem?_mapU (l : List Int) (k : Nat) (hk : k < l.length) :
    (⟨l.map (fun v => .int v .uint64)⟩ : Array GoValue)[k]?
      = some (.int (l.getD k 0) .uint64) := by
  simp [List.getElem?_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk]

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

/-- Loc-freedom of the wrapped-integer backing array. -/
private theorem locSup_mapU (l : List Int) :
    GoValue.locSup (.array ⟨l.map (fun v => .int v .uint64)⟩) = 0 := by
  show goValueListSup (l.map (fun v => .int v .uint64)) = 0
  induction l with
  | nil => rfl
  | cons v rest ih => simpa [goValueListSup, GoValue.locSup] using ih

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

/-! ## The headline -/

/-- **THE HEADLINE** (verified-examples slice 2c; the §9 memory-input
form on the nested-loop subject): *for any list `xs` of uint64 values,
wherever it lives in memory, with anything else present:
`insertionSort` completes normally — past one fuel bound, at every
nondeterminism-choice stream — the backing cell then holds a SORTED
PERMUTATION of `xs` (`sortSpec xs`; `sortSpec_sorted`,
`sortSpec_count`, `sortSpec_length` make that reading a theorem), and
no other memory is touched.*

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
theorem isort_ok (xs : List Int) (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64)
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

/-- **The D1 run-conditioned twin**: any normal completion, at ANY fuel
and stream, delivers the sorted permutation and frame preservation —
derived from the total headline, no second walk. -/
theorem isort_readout (xs : List Int)
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
  normal_readout_of_total (isort_ok xs hxs hlen base fr na hb hwf)

end GoLean.Examples.InsertionSort
