import GoLeanProofs.Examples.DedupAdjacentProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.EntryEq
import GoLeanProofs.Laws.StmtOps

/-!
# DedupAdjacent — the `dedup` example (Gallery Campaign G1, proof lane A)

Go source: `Corpus/coverage/exec/examples/dedup/main.go` (13 rows,
differentially green against `go run`). The lowering is pinned by
`scripts/check-golden` against `baselines/golden/dedup-lowered.repr`
and carried in `GoLeanProofs.Examples.DedupAdjacentProgram`.

The subject `dedupAdjacent(s []uint64) []uint64` compacts its slice IN
PLACE with a two-pointer walk and returns the surviving prefix
`s[:k]`. **The dedup is ADJACENT-only** — the single most important
thing to read correctly: only runs of EQUAL NEIGHBOURS collapse, so
`1,2,1,2` survives whole. The corpus row `four-alternating` pins
exactly that on the oracle side, because it is the classic misreading;
the specification `dedupAdj` below is the adjacent-only one, stated as
mathematics over `List Int` — keep an element iff it is FIRST or
differs from the last KEPT one — never as a restatement of the
two-pointer loop.

The harness is the S3 RELATIONAL shape: setup builds the family
`s[i] = seed + i/2` (integer division, so ADJACENT PAIRS REPEAT — the
family exercises both branches), `pre` snapshots it, the subject
compacts, `post` holds the surviving prefix zero-padded to the fixed
cap 8, and the third value is its length. The postcondition is a
relation over the RETURNED data `(pre, post, k)`:
`post = dedupAdj pre` (zero-padded) and `k = (dedupAdj pre).length` —
no family function appears inside the claim.

THE HEADLINE (`dedup_ok`) is stated HERE, in the root, so the
aggregator's `import GoLeanProofs.Examples.DedupAdjacent` reaches it
by name (the C-H4/C-H5 shape).

## The in-place invariant (the whole proof, stated early)

After the subject's loop has processed the first `i` elements with `k`
kept, the backing list `l` satisfies

* `l.take k = dedupAdj (orig.take i)` — the kept prefix is the answer
  so far,
* `l.drop i = orig.drop i` — the tail from `i` on is untouched
  original,
* `k = (dedupAdj (orig.take i)).length ≤ i`.

Positions in `[k, i)` are STALE — old values the walk left behind —
but they are never read again: the guard reads only `s[i]` (in the
untouched tail) and `s[k-1]` (in the kept prefix, `k-1 < k`), and the
write lands at `s[k]` with `k ≤ i`. The invariant never has to say
what the stale region holds, which is why the loop lemma can carry the
backing list existentially.
-/

namespace GoLean.Examples.DedupAdjacent

open GoLean GoLean.GoCore

/-- The harness `Func`, verbatim from the pinned lowering (the pin below
ties it by `rfl`). -/
def dedupHarnessRFunc : Func :=
{ id := { key := "dedup_harness_r" },
  args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
            { id := "seed", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
  results := #[{ id := "$res0",
                 typ := GoLean.GoCore.Ty.array 8 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
               { id := "$res1",
                 typ := GoLean.GoCore.Ty.array 8 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
               { id := "$res2", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
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
                                      (GoLean.GoCore.Expr.add
                                        (GoLean.GoCore.Expr.var "seed")
                                        (GoLean.GoCore.Expr.div
                                          (GoLean.GoCore.Expr.var "i")
                                          (GoLean.GoCore.Expr.intLit
                                            2
                                            (GoLean.GoCore.IntKind.uint64))))]]])]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "pre",
                      typ := GoLean.GoCore.Ty.array
                               8
                               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) }],
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
                                          (GoLean.GoCore.Expr.ref "pre")
                                          (GoLean.GoCore.Expr.var "i")))
                                      (GoLean.GoCore.Expr.indexGet
                                        (GoLean.GoCore.Expr.var "s")
                                        (GoLean.GoCore.Expr.var "i"))]]])]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "r",
                      typ := GoLean.GoCore.Ty.slice
                               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "r"]
                    { key := "dedupAdjacent" }
                    #[GoLean.GoCore.Expr.var "s"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "post",
                      typ := GoLean.GoCore.Ty.array
                               8
                               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) }],
              GoLean.GoCore.Stmt.block
                #[]
                #[GoLean.GoCore.Stmt.seqn
                    #[GoLean.GoCore.Stmt.initialization
                        { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                      GoLean.GoCore.Stmt.assign
                        (GoLean.GoCore.Assignee.var "i")
                        (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
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
                                  (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))),
                            GoLean.GoCore.Stmt.seqn #[],
                            GoLean.GoCore.Stmt.ifThenElse
                              (GoLean.GoCore.Expr.lessCmp
                                (GoLean.GoCore.Expr.var "i")
                                (GoLean.GoCore.Expr.length
                                  (GoLean.GoCore.Expr.var "r")
                                  (some (GoLean.GoCore.Ty.slice
                                     (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))))))
                              (GoLean.GoCore.Stmt.seqn #[])
                              (GoLean.GoCore.Stmt.breakStmt),
                            GoLean.GoCore.Stmt.block
                              #[]
                              #[GoLean.GoCore.Stmt.seqn
                                  #[GoLean.GoCore.Stmt.assign
                                      (GoLean.GoCore.Assignee.addr
                                        (GoLean.GoCore.Expr.indexAddr
                                          (GoLean.GoCore.Expr.ref "post")
                                          (GoLean.GoCore.Expr.var "i")))
                                      (GoLean.GoCore.Expr.indexGet
                                        (GoLean.GoCore.Expr.var "r")
                                        (GoLean.GoCore.Expr.var "i"))]]])]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res0")
                    (GoLean.GoCore.Expr.var "pre"),
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res1")
                    (GoLean.GoCore.Expr.var "post"),
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res2")
                    (GoLean.GoCore.Expr.convert
                      (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                      (GoLean.GoCore.Expr.length
                        (GoLean.GoCore.Expr.var "r")
                        (some (GoLean.GoCore.Ty.slice
                           (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))))),
                  GoLean.GoCore.Stmt.returnStmt]],
  variadic := false,
  wrapper := false }

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem dedupHarnessRFunc_pin :
    findFunctionIn? dedupLowered.funcs ⟨"dedup_harness_r"⟩
    = some dedupHarnessRFunc := rfl

open GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

abbrev tU64 : Ty := .int .uint64

/-! ## The subject `Func`, restated readable, and its pin -/

/-- The SUBJECT `Func`, verbatim from the pinned lowering (the pin
below ties it by `rfl`): the in-place two-pointer compaction. The
`k == 0` disjunct short-circuits the `s[k-1]` read — `Expr.or` is
lazy, so the guard never indexes out of range. -/
def dedupAdjacentFunc : Func :=
  { id := { key := "dedupAdjacent" },
    args := #[{ id := "s", typ := .slice tU64 }],
    results := #[{ id := "$res0", typ := .slice tU64 }],
    body := .block #[]
      #[.seqn #[.initialization { id := "k", typ := .int .int },
                .assign (.var "k") (.intLit 0 .int)],
        .block #[]
          #[.seqn #[.initialization { id := "i", typ := .int .int },
                    .assign (.var "i") (.intLit 0 .int)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) sjBody]],
        .seqn #[.assign (.var "$res0")
                  (.slice (.var "s") (.intLit 0 .int) (.var "k") none),
                .returnStmt]],
    variadic := false,
    wrapper := false }
  where
    /-- The guard, with the SHORT-CIRCUIT `or`: `k == 0` first, and
    only on its failure the `s[i] != s[k-1]` comparison. -/
    sjGuard : Expr :=
      .or (.eqCmp (.int .int) (.var "k") (.intLit 0 .int))
        (.neqCmp (.int .uint64)
          (.indexGet (.var "s") (.var "i"))
          (.indexGet (.var "s")
            (.sub (.var "k") (.intLit 1 .int))))
    /-- The keep branch: `s[k] = s[i]; k++`. -/
    sjKeep : Stmt :=
      .block #[]
        #[.seqn #[.assign
              (.addr (.indexAddr (.var "s") (.var "k")))
              (.indexGet (.var "s") (.var "i"))],
          .assign (.var "k")
            (.add (.var "k") (.intLit 1 .int))]
    /-- The loop's user block: the guarded keep. -/
    sjIfStmt : Stmt :=
      .block #[] #[.ifThenElse sjGuard sjKeep (.seqn #[])]
    /-- The desugared `for` body: `$forFirst` dispatch, exit test on
    `len(s)`, the guarded keep. -/
    sjBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "i") (.add (.var "i") (.intLit 1 .int))),
          .seqn #[],
          .ifThenElse
            (.lessCmp (.var "i")
              (.length (.var "s") (some (.slice tU64))))
            (.seqn #[]) .breakStmt,
          sjIfStmt]

/-- The lowering pin: the proof subject IS the frontend's lowering. -/
theorem dedupAdjacent_pin :
    findFunctionIn? dedupLowered.funcs ⟨"dedupAdjacent"⟩
    = some dedupAdjacentFunc := rfl

/-! ## The statement vocabulary: the ADJACENT-only dedup, as mathematics

`dedupAdj` keeps an element iff it is FIRST or differs from the last
KEPT one. For adjacent runs the last kept element is exactly the
predecessor, so the recursion below carries the predecessor — never an
index, never a second pointer, never a mutation. `1,2,1,2` maps to
itself; only runs of equal neighbours collapse. -/

/-- The tail of the dedup after a kept `prev`: drop an element iff it
equals the last kept one (which is always the immediate predecessor). -/
def dedupAdjTail (prev : Int) : List Int → List Int
  | [] => []
  | x :: xs => if x = prev then dedupAdjTail x xs
               else x :: dedupAdjTail x xs

/-- **The specification**: adjacent-only deduplication. The first
element is always kept; every later element is kept iff it differs
from the last kept one. -/
def dedupAdj : List Int → List Int
  | [] => []
  | x :: xs => x :: dedupAdjTail x xs

@[simp] theorem dedupAdj_nil : dedupAdj [] = [] := rfl

theorem dedupAdjTail_getLast? (xs : List Int) :
    ∀ prev : Int, (prev :: dedupAdjTail prev xs).getLast?
      = (prev :: xs).getLast? := by
  induction xs with
  | nil => intro prev; rfl
  | cons x xs ih =>
      intro prev
      show (prev :: dedupAdjTail prev (x :: xs)).getLast? = _
      simp only [dedupAdjTail]
      by_cases hx : x = prev
      · rw [if_pos hx]
        subst hx
        rw [List.getLast?_cons_cons]
        exact ih x
      · rw [if_neg hx, List.getLast?_cons_cons, List.getLast?_cons_cons]
        exact ih x

/-- The last KEPT element is the list's own last element — the bridge
between the machine's `s[k-1]` read and the snoc characterization. -/
theorem dedupAdj_getLast? (xs : List Int) :
    (dedupAdj xs).getLast? = xs.getLast? := by
  cases xs with
  | nil => rfl
  | cons x xs => exact dedupAdjTail_getLast? xs x

theorem dedupAdjTail_snoc (xs : List Int) (y : Int) :
    ∀ prev : Int, dedupAdjTail prev (xs ++ [y])
      = dedupAdjTail prev xs
        ++ (if (prev :: xs).getLast? = some y then [] else [y]) := by
  induction xs with
  | nil =>
      intro prev
      show dedupAdjTail prev [y] = _
      simp only [dedupAdjTail, List.getLast?_singleton, List.nil_append,
        Option.some.injEq]
      by_cases hy : y = prev
      · subst hy; simp
      · rw [if_neg hy, if_neg (fun h => hy h.symm)]
  | cons x xs ih =>
      intro prev
      show dedupAdjTail prev (x :: (xs ++ [y])) = _
      simp only [dedupAdjTail, List.getLast?_cons_cons]
      by_cases hx : x = prev
      · rw [if_pos hx, if_pos hx, ih x]
      · rw [if_neg hx, if_neg hx, ih x, List.cons_append]

/-- **The snoc characterization** — what one loop iteration does to
the answer: appending `y` keeps it iff it differs from the last
element (equivalently, by `dedupAdj_getLast?`, the last KEPT one). -/
theorem dedupAdj_snoc (xs : List Int) (y : Int) :
    dedupAdj (xs ++ [y])
      = if xs.getLast? = some y then dedupAdj xs
        else dedupAdj xs ++ [y] := by
  cases xs with
  | nil => simp [dedupAdj, dedupAdjTail]
  | cons x xs =>
      show dedupAdj (x :: (xs ++ [y])) = _
      rw [dedupAdj, dedupAdjTail_snoc xs y x, dedupAdj]
      by_cases hl : (x :: xs).getLast? = some y
      · rw [if_pos hl, if_pos hl, List.append_nil]
      · rw [if_neg hl, if_neg hl, List.cons_append]

theorem dedupAdjTail_length_le (xs : List Int) :
    ∀ prev : Int, (dedupAdjTail prev xs).length ≤ xs.length := by
  induction xs with
  | nil => intro _; exact Nat.le_refl 0
  | cons x xs ih =>
      intro prev
      rw [dedupAdjTail]
      by_cases hx : x = prev
      · rw [if_pos hx]
        exact Nat.le_succ_of_le (ih x)
      · rw [if_neg hx]
        simpa using ih x

theorem dedupAdj_length_le (xs : List Int) :
    (dedupAdj xs).length ≤ xs.length := by
  cases xs with
  | nil => exact Nat.le_refl 0
  | cons x xs => simpa [dedupAdj] using dedupAdjTail_length_le xs x

theorem dedupAdj_ne_nil {xs : List Int} (h : xs ≠ []) :
    dedupAdj xs ≠ [] := by
  cases xs with
  | nil => exact absurd rfl h
  | cons x xs => simp [dedupAdj]

theorem dedupAdjTail_mem {xs : List Int} :
    ∀ {prev v : Int}, v ∈ dedupAdjTail prev xs → v ∈ xs := by
  induction xs with
  | nil => intro _ _ h; cases h
  | cons x xs ih =>
      intro prev v h
      rw [dedupAdjTail] at h
      by_cases hx : x = prev
      · rw [if_pos hx] at h
        exact List.mem_cons_of_mem x (ih h)
      · rw [if_neg hx] at h
        rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem x (ih h)

/-- Every survivor is one of the originals (range transport). -/
theorem dedupAdj_mem {xs : List Int} {v : Int} (h : v ∈ dedupAdj xs) :
    v ∈ xs := by
  cases xs with
  | nil => cases h
  | cons x xs =>
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem x (dedupAdjTail_mem h)

/-- `getLast?` as the house total-read at the last index. -/
theorem getLast?_eq_getD {l : List Int} (h : l ≠ []) :
    l.getLast? = some (l.getD (l.length - 1) 0) := by
  have hpos : 0 < l.length := List.length_pos_iff.mpr h
  rw [List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega)]
  rfl

/-! ## The setup family: `s[i] = seed + i/2`, wrapped at uint64

GAP-WITNESS (kit gap, reported): `SliceMem.familyMod` is the
`seed + i % k` family and does NOT fit this harness (`seed + i / 2`).
The shape wanted in the kit is `familyDiv (k n seed : Nat)` with the
same lemma family (`length`/`range`/`succ`/`set`/`getD`); the local
`ddFamily` below is its `k = 2` instance, mirroring the `familyMod`
proofs verbatim. The wrap is part of the family BY DESIGN, so
wrap-boundary seeds are covered. -/

/-- The harness setup family: `fam[i] = (seed + i/2) % 2^64` —
integer division, so ADJACENT PAIRS REPEAT. -/
def ddFamily (n seed : Nat) : List Int :=
  (List.range n).map (fun i => (((seed + i / 2) % 2 ^ 64 : Nat) : Int))

theorem ddFamily_length (n seed : Nat) : (ddFamily n seed).length = n :=
  familyF_length (· / 2) n seed

theorem ddFamily_range (n seed : Nat) :
    ∀ v ∈ ddFamily n seed, 0 ≤ v ∧ v < 2 ^ 64 :=
  familyF_range (· / 2) n seed

theorem ddFamilyZ_range {n seed i : Nat} :
    ∀ v ∈ ddFamily i seed ++ List.replicate (n - i) (0 : Int),
      0 ≤ v ∧ v < 2 ^ 64 :=
  familyFZ_range (f := (· / 2))

theorem ddFamily_succ (i seed : Nat) :
    ddFamily (i + 1) seed
      = ddFamily i seed ++ [(((seed + i / 2) % 2 ^ 64 : Nat) : Int)] :=
  familyF_succ (· / 2) i seed

/-- One setup store advances the family prefix. -/
theorem ddFamily_set {n seed i : Nat} (hi : i < n) :
    (ddFamily i seed ++ List.replicate (n - i) 0).set i
        (((seed + i / 2) % 2 ^ 64 : Nat) : Int)
      = ddFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0 :=
  familyF_set (f := (· / 2)) hi

/-- The family's element at an in-range index. -/
theorem ddFamily_getD {n seed m : Nat} (hm : m < n) :
    (ddFamily n seed).getD m 0
      = (((seed + m / 2) % 2 ^ 64 : Nat) : Int) :=
  familyF_getD (f := (· / 2)) hm

/-- The `pre` copy-loop invariant list: the family prefix, zero tail
(the kit's `prefixPad` at the local family). -/
def ddPre (m seed : Nat) : List Int :=
  prefixPad ddFamily 8 m seed

theorem ddPre_length {m seed : Nat} (h : m ≤ 8) :
    (ddPre m seed).length = 8 :=
  prefixPad_length (ddFamily_length m seed) h

theorem ddPre_range {m seed : Nat} :
    ∀ v ∈ ddPre m seed, 0 ≤ v ∧ v < 2 ^ 64 :=
  prefixPad_range (ddFamily_range m seed)

theorem ddPre_set {seed m : Nat} (hm : m < 8) :
    (ddPre m seed).set m (((seed + m / 2) % 2 ^ 64 : Nat) : Int)
      = ddPre (m + 1) seed :=
  ddFamily_set hm

theorem ddPre_full {n seed : Nat} :
    ddPre n seed
      = ddFamily n seed
          ++ List.replicate (8 - (ddFamily n seed).length) 0 :=
  prefixPad_full (ddFamily_length n seed)

/-- The `post` copy-loop invariant list: the surviving prefix of the
answer, zero tail. -/
def ddPost (vals : List Int) (m : Nat) : List Int :=
  (dedupAdj vals).take m ++ List.replicate (8 - m) 0

theorem ddPost_length {vals : List Int} {m : Nat}
    (hm : m ≤ (dedupAdj vals).length) (hcap : m ≤ 8) :
    (ddPost vals m).length = 8 := by
  rw [ddPost, List.length_append, List.length_take_of_le hm,
    List.length_replicate]
  omega

theorem ddPost_range {vals : List Int} {m : Nat}
    (hr : ∀ v ∈ vals, 0 ≤ v ∧ v < 2 ^ 64) :
    ∀ v ∈ ddPost vals m, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hr v (dedupAdj_mem (List.mem_of_mem_take hv))
  · rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
    omega

theorem ddPost_set {vals : List Int} {m : Nat}
    (hm : m < (dedupAdj vals).length) (hcap : m < 8) :
    (ddPost vals m).set m ((dedupAdj vals).getD m 0)
      = ddPost vals (m + 1) := by
  have hlen : ((dedupAdj vals).take m).length = m :=
    List.length_take_of_le (by omega)
  have hnm : 8 - m = (8 - (m + 1)) + 1 := by omega
  rw [ddPost, List.set_append_right _ _ (by omega), hlen, Nat.sub_self,
    hnm, List.replicate_succ, List.set_cons_zero, ddPost]
  have htake : (dedupAdj vals).take (m + 1)
      = (dedupAdj vals).take m ++ [(dedupAdj vals).getD m 0] := by
    rw [List.take_add_one, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hm]
    rfl
  rw [htake]
  simp

theorem ddPost_full {vals : List Int} :
    ddPost vals (dedupAdj vals).length
      = dedupAdj vals
          ++ List.replicate (8 - (dedupAdj vals).length) 0 := by
  rw [ddPost, List.take_of_length_le (Nat.le_refl _)]

/-- The returned fixed-cap array: the list, zero-padded to the
harness's `dedupCapN = 8` slots. Statement vocabulary — deliberately
NOT shared with the identically shaped `histArr8`/`goArr8`s, since
unifying them would change what these statements say (the §11 closure
rule). -/
def ddArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map
    (fun v => .int v .uint64)⟩

/-! ## The executable op facts (WP arc s1 lift 1: LIFTED to
`SliceMem`'s completed integer family — the four unpinned locals
(`eqCmp`/`neqCmp`/`sub`/`convert`) are deleted, their call sites
resolving to the kit through the module's `open GoLean.SliceMem`; the
pinned `applyStrictOp_div_u64` survives as a delegation, zero proof
lines.) -/

theorem applyStrictOp_div_u64 {σ : ExecState} {a b : Nat}
    (hb : 0 < b) (ha : a < 2 ^ 64) :
    applyStrictOp σ .div [.int (a : Int) .uint64, .int (b : Int) .uint64]
      = .ok (.int ((a / b : Nat) : Int) .uint64, σ) :=
  SliceMem.applyStrictOp_div_u64 hb ha

/-- GAP-WITNESS (kit gap, reported): the two-index slice expression
`s[0:kv]` over a SLICE base (the kit's `applyStrictOp_sliceExpr_array`
covers only the pointer-to-array base): length becomes `kv`, the
capacity stays. -/
theorem applyStrictOp_sliceExpr_slice {σ : ExecState} {b : Loc}
    {n kv : Nat} {k1 k2 : IntKind} (hk : kv ≤ n) :
    applyStrictOp σ (.sliceExpr false)
      [.slice ⟨some b, 0, n, n⟩, .int 0 k1, .int (kv : Nat) k2]
      = .ok (.slice ⟨some b, 0, kv, n⟩, σ) := by
  simp only [applyStrictOp, valueAsInt, applySlice, sliceFromSlice,
    validateSlice, checkSliceBounds, Bind.bind, Except.bind, pure,
    Except.pure]
  rw [if_neg (by omega)]
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (by omega), if_neg (by exact_mod_cast Nat.not_lt.mpr hk),
    if_neg (by omega), if_neg (by omega)]
  simp

/-! ## Machine layer: heap cells, statement pieces, environments,
continuations, heap fronts

Address layout (probe-measured at `(n, seed) = (5, 900001)`;
`.tmp/ddprobe.lean` traced every step, and every raw segment below
re-checks the transcription by `rfl`):

```
0 = n          1 = seed        2 = $res0 (pre [8])
3 = $res1 (post [8])           4 = $res2 (k, u64)
5 = $c4 handle 6 = backing (n) 7 = s handle
8 = setup i    9 = setup flag  10 = pre array [8]
11 = copy i    12 = copy flag  13 = r (slice)
-- the `dedupAdjacent` frame --
14 = s param   15 = its $res0  16 = k   17 = i   18 = flag
-- after the return --
19 = post array [8]            20 = post i   21 = post flag
```

The subject allocates NOTHING per iteration, so every address is a
fixed constant and no dead-tail (`DeadFrom`) reasoning is needed
anywhere in this example. -/

abbrev u64cell (v : Int) : HeapCell := ⟨some tU64, .int v .uint64⟩
abbrev icell (v : Int) : HeapCell := ⟨some (.int .int), .int v .int⟩
abbrev bcell (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
abbrev arrCell (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n tU64), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev zeros8 : List Int := List.replicate 8 0

abbrev dSliceV (n : Nat) : GoValue := .slice ⟨some (.base ⟨6⟩), 0, n, n⟩
abbrev dHandleV (n : Nat) : HeapCell := ⟨some (.slice tU64), dSliceV n⟩
abbrev rSliceV (kk n : Nat) : GoValue := .slice ⟨some (.base ⟨6⟩), 0, kk, n⟩
abbrev rHandleV (kk n : Nat) : HeapCell := ⟨some (.slice tU64), rSliceV kk n⟩
abbrev dNilSlice : HeapCell := ⟨some (.slice tU64), .slice ⟨none, 0, 0, 0⟩⟩

/-- The PROGRAM-generic state form. -/
abbrev dSt (σ : ExecState) (H : Heap) (na : Nat) : ExecState :=
  { σ with heap := H, nextAddr := na }

/-! ### The harness body's top-level statement pieces -/

def dsuBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[]) .breakStmt,
      .block #[]
        #[.seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
            (.add (.var "seed")
              (.div (.var "i") (.intLit 2 .uint64)))]]]

def dcpBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[]) .breakStmt,
      .block #[]
        #[.seqn #[.assign (.addr (.indexAddr (.ref "pre") (.var "i")))
            (.indexGet (.var "s") (.var "i"))]]]

def dpoBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .int))),
      .seqn #[],
      .ifThenElse
        (.lessCmp (.var "i") (.length (.var "r") (some (.slice tU64))))
        (.seqn #[]) .breakStmt,
      .block #[]
        #[.seqn #[.assign (.addr (.indexAddr (.ref "post") (.var "i")))
            (.indexGet (.var "r") (.var "i"))]]]

def dS2 : Stmt :=
  .seqn #[.initialization { id := "s", typ := .slice tU64 },
          .assign (.var "s") (.var "$c4")]
def dS3 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := tU64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) dsuBody]]
def dS4 : Stmt :=
  .seqn #[.initialization { id := "pre", typ := .array 8 tU64 }]
def dS5 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := tU64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) dcpBody]]
def dS6 : Stmt :=
  .seqn #[.initialization { id := "r", typ := .slice tU64 },
          .call #[.var "r"] ⟨"dedupAdjacent"⟩ #[.var "s"]]
def dS7 : Stmt :=
  .seqn #[.initialization { id := "post", typ := .array 8 tU64 }]
def dS8 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .int },
              .assign (.var "i") (.intLit 0 .int)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) dpoBody]]
def dS9 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "pre"),
          .assign (.var "$res1") (.var "post"),
          .assign (.var "$res2")
            (.convert tU64 (.length (.var "r") (some (.slice tU64)))),
          .returnStmt]

/-! ### Environments -/

def baseEnvD : Scope :=
  [("$res2", .base ⟨4⟩), ("$res1", .base ⟨3⟩), ("$res0", .base ⟨2⟩),
   ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]
def envC4D : LocalEnv := [[("$c4", .base ⟨5⟩)], baseEnvD]
def sScopeD : Scope := [("s", .base ⟨7⟩), ("$c4", .base ⟨5⟩)]
def preScopeD : Scope :=
  [("pre", .base ⟨10⟩), ("s", .base ⟨7⟩), ("$c4", .base ⟨5⟩)]
def callScopeD : Scope :=
  [("r", .base ⟨13⟩), ("pre", .base ⟨10⟩), ("s", .base ⟨7⟩),
   ("$c4", .base ⟨5⟩)]
def callEnvD : LocalEnv := [callScopeD, baseEnvD]
def poScopeD : Scope := ("post", .base ⟨19⟩) :: callScopeD

def suEnvD : LocalEnv :=
  [[("$forFirst", .base ⟨9⟩)], [("i", .base ⟨8⟩)], sScopeD, baseEnvD]
def suEnvD2 : LocalEnv := [] :: [] :: suEnvD
def cpEnvD : LocalEnv :=
  [[("$forFirst", .base ⟨12⟩)], [("i", .base ⟨11⟩)], preScopeD, baseEnvD]
def cpEnvD2 : LocalEnv := [] :: [] :: cpEnvD
def poEnvD : LocalEnv :=
  [[("$forFirst", .base ⟨21⟩)], [("i", .base ⟨20⟩)], poScopeD, baseEnvD]
def poEnvD2 : LocalEnv := [] :: [] :: poEnvD

/-! ### Harness continuations -/

abbrev dBarrier : Cont := .frame [] [] [] [] .stop

def dTailAfterSetup : Cont :=
  .seq [dS4, dS5, dS6, dS7, dS8, dS9] [sScopeD, baseEnvD] dBarrier
def suHeadTailD : Cont :=
  .seq [] suEnvD
    (.seq [] [[("i", .base ⟨8⟩)], sScopeD, baseEnvD] dTailAfterSetup)
def suHeadCfgD : Config :=
  .exec (.while (.boolLit true) dsuBody) suEnvD suHeadTailD
def suLoopKD : Cont := .loop (.boolLit true) dsuBody suEnvD suHeadTailD
def suStoreBlockD : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
        (.add (.var "seed") (.div (.var "i") (.intLit 2 .uint64)))]]
def suCmpKD : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: suEnvD)
    (.seq [suStoreBlockD] ([] :: suEnvD) suLoopKD)
def suRefD (n : Nat) (iv : Int) : TargetRef :=
  .chain (dSliceV n) [.int iv .uint64] [.index]
def suStTailD : Cont :=
  .seq [] suEnvD2 (.seq [] ([] :: suEnvD) suLoopKD)
def suRhsKD (n : Nat) (iv : Int) : Cont :=
  .rhsK .vals [suRefD n iv] [] [] (.seqn #[]) suEnvD2 suStTailD
def suAddKD (n : Nat) (sv iv : Int) : Cont :=
  .strictK .add [.int sv .uint64] [] suEnvD2 (suRhsKD n iv)
def suDivKD (n : Nat) (sv iv : Int) : Cont :=
  .strictK .div [.int iv .uint64] [] suEnvD2 (suAddKD n sv iv)

def dTailAfterCopy : Cont :=
  .seq [dS6, dS7, dS8, dS9] [preScopeD, baseEnvD] dBarrier
def cpHeadTailD : Cont :=
  .seq [] cpEnvD
    (.seq [] [[("i", .base ⟨11⟩)], preScopeD, baseEnvD] dTailAfterCopy)
def cpHeadCfgD : Config :=
  .exec (.while (.boolLit true) dcpBody) cpEnvD cpHeadTailD
def cpLoopKD : Cont := .loop (.boolLit true) dcpBody cpEnvD cpHeadTailD
def cpStoreBlockD : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.ref "pre") (.var "i")))
        (.indexGet (.var "s") (.var "i"))]]
def cpCmpKD : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: cpEnvD)
    (.seq [cpStoreBlockD] ([] :: cpEnvD) cpLoopKD)
def cpRefD (iv : Int) : TargetRef :=
  .chain (.addr (.base ⟨10⟩)) [.int iv .uint64] [.index]
def cpStTailD : Cont :=
  .seq [] cpEnvD2 (.seq [] ([] :: cpEnvD) cpLoopKD)
def cpRhsKD (iv : Int) : Cont :=
  .rhsK .vals [cpRefD iv] [] [] (.seqn #[]) cpEnvD2 cpStTailD

/-! ### The call and the subject's continuations -/

def dAfterCall : Cont := .seq [dS7, dS8, dS9] callEnvD dBarrier
def dCallPlans : List (TargetShape × List Expr) :=
  [(.chain [], [.ref "r"])]
def dCallArgsK : Cont :=
  .callArgsK ⟨"dedupAdjacent"⟩ dCallPlans [] [] callEnvD dAfterCall
def frameKD : Cont :=
  .frame dCallPlans callEnvD [.base ⟨15⟩] [] dAfterCall
def sjFrameEnv : LocalEnv :=
  [[("$res0", .base ⟨15⟩), ("s", .base ⟨14⟩)]]

def sjScope0 : Scope := [("$res0", .base ⟨15⟩), ("s", .base ⟨14⟩)]
def sjEnvK : LocalEnv :=
  [[("$forFirst", .base ⟨18⟩)], [("i", .base ⟨17⟩)],
   [("k", .base ⟨16⟩)], sjScope0]
def sjEnvB : LocalEnv := [] :: sjEnvK
def sjEnvG : LocalEnv := [] :: sjEnvB
def sjEnvKp : LocalEnv := [] :: sjEnvG

abbrev sjBody : Stmt := dedupAdjacentFunc.sjBody
abbrev sjIfStmt : Stmt := dedupAdjacentFunc.sjIfStmt
abbrev sjKeep : Stmt := dedupAdjacentFunc.sjKeep
abbrev sjNeqExpr : Expr :=
  .neqCmp (.int .uint64)
    (.indexGet (.var "s") (.var "i"))
    (.indexGet (.var "s") (.sub (.var "k") (.intLit 1 .int)))
abbrev sjKAsgn : Stmt :=
  .assign (.var "k") (.add (.var "k") (.intLit 1 .int))
abbrev sjEpi : Stmt :=
  .seqn #[.assign (.var "$res0")
            (.slice (.var "s") (.intLit 0 .int) (.var "k") none),
          .returnStmt]

def sjTail3 : Cont := .seq [sjEpi] [[("k", .base ⟨16⟩)], sjScope0] frameKD
def sjHeadTail : Cont :=
  .seq [] sjEnvK
    (.seq [] [[("i", .base ⟨17⟩)], [("k", .base ⟨16⟩)], sjScope0] sjTail3)
def sjHeadCfg : Config :=
  .exec (.while (.boolLit true) sjBody) sjEnvK sjHeadTail
def sjLoopK : Cont := .loop (.boolLit true) sjBody sjEnvK sjHeadTail
def sjCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt sjEnvB (.seq [sjIfStmt] sjEnvB sjLoopK)
def sjLenK (iv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice tU64))) [] [] sjEnvB
    (.strictK .lessCmp [.int iv .int] [] sjEnvB sjCmpK)
def sjIfTail : Cont := .seq [] sjEnvG (.seq [] sjEnvB sjLoopK)
def sjIfK : Cont := .ifK sjKeep (.seqn #[]) sjEnvG sjIfTail
def sjOrK : Cont := .orK sjNeqExpr sjEnvG sjIfK
def sjEqK (kv : Int) : Cont :=
  .strictK (.eqCmp (.int .int)) [.int kv .int] [] sjEnvG sjOrK
def sjNeq1K : Cont :=
  .strictK (.neqCmp tU64) []
    [.indexGet (.var "s") (.sub (.var "k") (.intLit 1 .int))] sjEnvG
    (.boolK sjIfK)
def sjIdx1K (n : Nat) : Cont :=
  .strictK .indexGet [dSliceV n] [] sjEnvG sjNeq1K
def sjNeq2K (x : GoValue) : Cont :=
  .strictK (.neqCmp tU64) [x] [] sjEnvG (.boolK sjIfK)
def sjIdx2K (n : Nat) (x : GoValue) : Cont :=
  .strictK .indexGet [dSliceV n] [] sjEnvG (sjNeq2K x)
def sjSubK (n : Nat) (x : GoValue) (kv : Int) : Cont :=
  .strictK .sub [.int kv .int] [] sjEnvG (sjIdx2K n x)

def sjKeepRef (n : Nat) (kv : Int) : TargetRef :=
  .chain (dSliceV n) [.int kv .int] [.index]
def sjKeepStTail : Cont := .seq [sjKAsgn] sjEnvKp sjIfTail
def sjKeepRhsK (n : Nat) (kv : Int) : Cont :=
  .rhsK .vals [sjKeepRef n kv] [] [] (.seqn #[]) sjEnvKp sjKeepStTail
def sjKeepIdxK (n : Nat) (kv : Int) : Cont :=
  .strictK .indexGet [dSliceV n] [] sjEnvKp (sjKeepRhsK n kv)

/-! ### The subject's exit and the post loop -/

def sjEnv0 : LocalEnv := [[("k", .base ⟨16⟩)], sjScope0]
def sjResRhsK : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨15⟩)) [] []] [] [] (.seqn #[]) sjEnv0
    (.seq [.returnStmt] sjEnv0 frameKD)
def sjSliceK (n : Nat) : Cont :=
  .strictK (.sliceExpr false) [.int 0 .int, dSliceV n] [] sjEnv0 sjResRhsK

def dTailAfterPost : Cont := .seq [dS9] [poScopeD, baseEnvD] dBarrier
def poHeadTailD : Cont :=
  .seq [] poEnvD
    (.seq [] [[("i", .base ⟨20⟩)], poScopeD, baseEnvD] dTailAfterPost)
def poHeadCfgD : Config :=
  .exec (.while (.boolLit true) dpoBody) poEnvD poHeadTailD
def poLoopKD : Cont := .loop (.boolLit true) dpoBody poEnvD poHeadTailD
def poStoreBlockD : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.ref "post") (.var "i")))
        (.indexGet (.var "r") (.var "i"))]]
def poCmpKD : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: poEnvD)
    (.seq [poStoreBlockD] ([] :: poEnvD) poLoopKD)
def poLenK (iv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice tU64))) [] [] ([] :: poEnvD)
    (.strictK .lessCmp [.int iv .int] [] ([] :: poEnvD) poCmpKD)
def poRefD (iv : Int) : TargetRef :=
  .chain (.addr (.base ⟨19⟩)) [.int iv .int] [.index]
def poStTailD : Cont :=
  .seq [] poEnvD2 (.seq [] ([] :: poEnvD) poLoopKD)
def poRhsKD (iv : Int) : Cont :=
  .rhsK .vals [poRefD iv] [] [] (.seqn #[]) poEnvD2 poStTailD

/-! ### The epilogue's continuations -/

abbrev dConvExpr : Expr :=
  .convert tU64 (.length (.var "r") (some (.slice tU64)))
def epiEnv : LocalEnv := [poScopeD, baseEnvD]
def epiRest1 : List Stmt :=
  [.assign (.var "$res1") (.var "post"),
   .assign (.var "$res2") dConvExpr, .returnStmt]
def epiRest2 : List Stmt :=
  [.assign (.var "$res2") dConvExpr, .returnStmt]
def epiRhsK2 : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨4⟩)) [] []] [] [] (.seqn #[]) epiEnv
    (.seq [.returnStmt] epiEnv dBarrier)
def epiLenK : Cont :=
  .strictK (.lengthOf (some (.slice tU64))) [] [] epiEnv
    (.strictK (.convert tU64) [] [] epiEnv epiRhsK2)

/-! ### Heap fronts -/

def dHeap0 (nv sv : Int) : Heap :=
  [(.base ⟨0⟩, u64cell nv), (.base ⟨1⟩, u64cell sv),
   (.base ⟨2⟩, arrCell 8 zeros8), (.base ⟨3⟩, arrCell 8 zeros8),
   (.base ⟨4⟩, u64cell 0)]
def dHeapC4 (nv sv : Int) : Heap :=
  dHeap0 nv sv ++ [(.base ⟨5⟩, dNilSlice)]
def dHeapMake (nv sv : Int) (n : Nat) : Heap :=
  dHeap0 nv sv
    ++ [(.base ⟨5⟩, dHandleV n), (.base ⟨6⟩, arrCell n (List.replicate n 0))]
def dHeapSu (nv sv : Int) (n : Nat) (l : List Int) (iv : Int) (ff : Bool) :
    Heap :=
  dHeap0 nv sv
    ++ [(.base ⟨5⟩, dHandleV n), (.base ⟨6⟩, arrCell n l),
        (.base ⟨7⟩, dHandleV n), (.base ⟨8⟩, u64cell iv),
        (.base ⟨9⟩, bcell ff)]
def dHeapCp (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (ff : Bool) : Heap :=
  dHeapSu nv sv n l siv false
    ++ [(.base ⟨10⟩, arrCell 8 lp), (.base ⟨11⟩, u64cell civ),
        (.base ⟨12⟩, bcell ff)]
def dHeapCall (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int) :
    Heap :=
  dHeapCp nv sv n l lp siv civ false ++ [(.base ⟨13⟩, dNilSlice)]
def dHeapFrame (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int) :
    Heap :=
  dHeapCall nv sv n l lp siv civ
    ++ [(.base ⟨14⟩, dHandleV n), (.base ⟨15⟩, dNilSlice)]
def dHeapSj (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ kv iv : Int)
    (ff : Bool) : Heap :=
  dHeapFrame nv sv n l lp siv civ
    ++ [(.base ⟨16⟩, icell kv), (.base ⟨17⟩, icell iv),
        (.base ⟨18⟩, bcell ff)]

/-- The post-phase front: the subject frame's cells are dead but
present; `r` (13) and the subject's `$res0` (15) hold the surviving
prefix's handle. -/
def dHeapPo (nv sv : Int) (n : Nat) (l lp po : List Int) (siv civ : Int)
    (kk : Nat) (kv sjiv iv : Int) (ff : Bool) : Heap :=
  dHeapCp nv sv n l lp siv civ false
    ++ [(.base ⟨13⟩, rHandleV kk n), (.base ⟨14⟩, dHandleV n),
        (.base ⟨15⟩, rHandleV kk n), (.base ⟨16⟩, icell kv),
        (.base ⟨17⟩, icell sjiv), (.base ⟨18⟩, bcell false),
        (.base ⟨19⟩, arrCell 8 po), (.base ⟨20⟩, icell iv),
        (.base ⟨21⟩, bcell ff)]

/-- The epilogue-phase front, with the three harness result cells
(2/3/4) generalized — the terminal front is its `(lp, po, kk)`
instance. -/
def dHeapEndG (nv sv : Int) (n : Nat) (l lp po c2 c3 : List Int)
    (c4 : Int) (siv civ : Int) (kk : Nat) (kv sjiv iv : Int) : Heap :=
  [(.base ⟨0⟩, u64cell nv), (.base ⟨1⟩, u64cell sv),
   (.base ⟨2⟩, arrCell 8 c2), (.base ⟨3⟩, arrCell 8 c3),
   (.base ⟨4⟩, u64cell c4),
   (.base ⟨5⟩, dHandleV n), (.base ⟨6⟩, arrCell n l),
   (.base ⟨7⟩, dHandleV n), (.base ⟨8⟩, u64cell siv),
   (.base ⟨9⟩, bcell false),
   (.base ⟨10⟩, arrCell 8 lp), (.base ⟨11⟩, u64cell civ),
   (.base ⟨12⟩, bcell false),
   (.base ⟨13⟩, rHandleV kk n), (.base ⟨14⟩, dHandleV n),
   (.base ⟨15⟩, rHandleV kk n), (.base ⟨16⟩, icell kv),
   (.base ⟨17⟩, icell sjiv), (.base ⟨18⟩, bcell false),
   (.base ⟨19⟩, arrCell 8 po), (.base ⟨20⟩, icell iv),
   (.base ⟨21⟩, bcell false)]

/-- The terminal front: the harness result cells hold the three
returned values. -/
abbrev dHeapEnd (nv sv : Int) (n : Nat) (l lp po : List Int)
    (siv civ : Int) (kk : Nat) (kv sjiv iv : Int) : Heap :=
  dHeapEndG nv sv n l lp po lp po ((kk : Nat) : Int) siv civ kk kv sjiv iv

/-! ## The pinned program and the entry equation -/

/-- The pinned program as an empty-heap state — with the
`derive_entry_eq` invocation below, one of the two places this module
unfolds `dedupLowered` (the other: the `enterFrame` discharge). -/
def ddProg : ExecState :=
  { types := dedupLowered.typeDefs.toList,
    functions := dedupLowered.funcs,
    methods := dedupLowered.methods,
    heap := [], nextAddr := 0 }

derive_entry_eq dd_entry_eq dedupLowered dedupHarnessRFunc ddSeed ddC0 ddProg

/-! ## Heap-lookup facts (concrete fronts, symbolic values) -/

theorem lookup_suD (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ff : Bool) (na : Nat) :
    Heap.lookup (dSt σ (dHeapSu nv sv n l iv ff) na).heap (.base ⟨6⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [dHeapSu, dHeap0, Heap.lookup]

theorem lookup_cpS_D (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ff : Bool) (na : Nat) :
    Heap.lookup (dSt σ (dHeapCp nv sv n l lp siv civ ff) na).heap
        (.base ⟨6⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [dHeapCp, dHeapSu, dHeap0, Heap.lookup]

theorem lookup_cpPre_D (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ff : Bool) (na : Nat) :
    Heap.lookup (dSt σ (dHeapCp nv sv n l lp siv civ ff) na).heap
        (.base ⟨10⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨lp.map (fun v => .int v .uint64)⟩⟩ := by
  simp [dHeapCp, dHeapSu, dHeap0, Heap.lookup]

/-! ## Raw run segments — PROGRAM-generic throughout -/

/-- Entry A: body start → the `$c4` makeSlice apply point. 10 steps. -/
theorem d_E1_raw (σ : ExecState) (nv sv : Int) (ch : Choices) :
    stepFnIter 10 (dSt σ (dHeap0 nv sv) 5) ddC0 ch
      = .ok (.retV (.int nv .uint64)
          (.stmtOpK (.makeSlice tU64 false) 1
            [.addr (.base ⟨5⟩)] [] envC4D
            (.seq [dS2, dS3, dS4, dS5, dS6, dS7, dS8, dS9] envC4D
              dBarrier)),
        dSt σ (dHeapC4 nv sv) 6, ch) := by
  with_unfolding_all rfl

/-- `make([]uint64, n)` at SYMBOLIC `n`. -/
theorem d_make_apply (σ : ExecState) (nv sv : Int) (n : Nat)
    (ch : Choices) :
    applyStmtOp (dSt σ (dHeapC4 nv sv) 6) ch (.makeSlice tU64 false) 1
      [.addr (.base ⟨5⟩), .int (n : Nat) .uint64]
      = .ok (dSt σ (dHeapMake nv sv n) 7, ch) := by
  have hnn1 := natFromNonneg_cast
    "runtime error: makeslice: len out of range" n
  have hnn2 := natFromNonneg_cast
    "runtime error: makeslice: cap out of range" n
  have hb := GoLean.Iris.buildDefaultArrayValue_int
    (dSt σ (dHeapC4 nv sv) 6) .uint64 n
  have harr : (List.replicate n (GoValue.int 0 .uint64)).toArray
      = (⟨(List.replicate n (0 : Int)).map
          (fun v => GoValue.int v .uint64)⟩ : Array GoValue) := by
    simp [List.map_replicate]
  rw [harr] at hb
  simp only [applyStmtOp, applyStmtOpCore, valueAsInt, valueAsLoc,
    hnn1, hnn2, hb, Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (Nat.lt_irrefl n)]
  with_unfolding_all rfl

/-- Entry B: `s := $c4`, the setup counter and flag → the setup loop
head. 42 steps. -/
theorem d_E2_raw (σ : ExecState) (nv sv : Int) (n : Nat) (ch : Choices) :
    stepFnIter 42 (dSt σ (dHeapMake nv sv n) 7)
      (.next (.seq [dS2, dS3, dS4, dS5, dS6, dS7, dS8, dS9] envC4D
        dBarrier)) ch
      = .ok (suHeadCfgD,
          dSt σ (dHeapSu nv sv n (List.replicate n 0) 0 true) 10, ch) := by
  with_unfolding_all rfl

/-! ### The setup loop -/

theorem su_A0_rawD (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 25 (dSt σ (dHeapSu nv sv n l iv true) 10) suHeadCfgD ch
      = .ok (.retV (.bool (decide (iv < nv))) suCmpKD,
          dSt σ (dHeapSu nv sv n l iv false) 10, ch) := by
  with_unfolding_all rfl

theorem su_A1_rawD (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 29 (dSt σ (dHeapSu nv sv n l iv false) 10) suHeadCfgD ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < nv))) suCmpKD,
          dSt σ (dHeapSu nv sv n l
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false) 10, ch) := by
  with_unfolding_all rfl

/-- Setup fill phase A: test true → the `/` apply point. 19 steps. -/
theorem su_B1a_rawD (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 19 (dSt σ (dHeapSu nv sv n l iv false) 10)
      (.retV (.bool true) suCmpKD) ch
      = .ok (.retV (.int 2 .uint64) (suDivKD n sv iv),
          dSt σ (dHeapSu nv sv n l iv false) 10, ch) := by
  with_unfolding_all rfl

/-- Setup fill phase B: the `/` result → the add → the element-store
point. 2 steps. -/
theorem su_B1b_rawD (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv rv : Int) (ch : Choices) :
    stepFnIter 2 (dSt σ (dHeapSu nv sv n l iv false) 10)
      (.retV (.int rv .uint64) (suAddKD n sv iv)) ch
      = .ok (.next (.storeK [suRefD n iv]
            [.int (IntKind.normalize .uint64 (sv + rv)) .uint64]
            (.seqn #[]) suEnvD2 suStTailD),
          dSt σ (dHeapSu nv sv n l iv false) 10, ch) := by
  with_unfolding_all rfl

theorem su_D_rawD (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 5 (dSt σ (dHeapSu nv sv n l iv false) 10)
      (.next (.storeK [] [] (.seqn #[]) suEnvD2 suStTailD)) ch
      = .ok (suHeadCfgD, dSt σ (dHeapSu nv sv n l iv false) 10, ch) := by
  with_unfolding_all rfl

/-- Setup exit: test false → `var pre` declared and the copy loop
head. 39 steps. -/
theorem su_X_rawD (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 39 (dSt σ (dHeapSu nv sv n l iv false) 10)
      (.retV (.bool false) suCmpKD) ch
      = .ok (cpHeadCfgD,
          dSt σ (dHeapCp nv sv n l zeros8 iv 0 true) 13, ch) := by
  with_unfolding_all rfl

/-- One setup iteration from the exit test's true delivery at `i`. 57
steps. -/
theorem su_iterD (σ : ExecState) (n seed i : Nat) (hn : n < 2 ^ 63)
    (hi : i < n) (ch : Choices) :
    stepFnIter 57
      (dSt σ (dHeapSu ((n : Nat) : Int) ((seed : Nat) : Int)
        n (ddFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false) 10)
      (.retV (.bool true) suCmpKD) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) suCmpKD,
          dSt σ (dHeapSu ((n : Nat) : Int) ((seed : Nat) : Int)
            n (ddFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
            ((i + 1 : Nat) : Int) false) 10, ch) := by
  have hB1a := su_B1a_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (ddFamily i seed ++ List.replicate (n - i) 0) ((i : Nat) : Int) ch
  have hdiv := stepFnIter_one (stepFn_strict_apply
    (done := [.int ((i : Nat) : Int) .uint64]) (env := suEnvD2)
    (k := suAddKD n ((seed : Nat) : Int) ((i : Nat) : Int)) (ch := ch)
    (applyStrictOp_div_u64
      (σ := dSt σ (dHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
        (ddFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false) 10)
      (a := i) (b := 2) (by omega) (by omega)))
  have h1 := stepFnIter_chain hB1a hdiv
  have hB1b := su_B1b_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (ddFamily i seed ++ List.replicate (n - i) 0)
    ((i : Nat) : Int) ((i / 2 : Nat) : Int) ch
  rw [unorm_add_nat seed (i / 2)] at hB1b
  have h2 := stepFnIter_chain h1 hB1b
  have hw : (0 : Int) ≤ (((seed + i / 2) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + i / 2) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + i / 2) (y := 2 ^ 64) (by omega)
    omega
  have hst := storeTarget_slice_u64
    (σ := dSt σ (dHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
      (ddFamily i seed ++ List.replicate (n - i) 0)
      ((i : Nat) : Int) false) 10)
    (a := ⟨6⟩) (off := 0) (len := n) (cap := n) (i := i) (n := n)
    (ik := .uint64) (l := ddFamily i seed ++ List.replicate (n - i) 0)
    (w := (((seed + i / 2) % 2 ^ 64 : Nat) : Int))
    (lookup_suD σ ((n : Nat) : Int) ((seed : Nat) : Int) n
      (ddFamily i seed ++ List.replicate (n - i) 0) ((i : Nat) : Int)
      false 10)
    (Nat.le_refl n) hi
    (by rw [List.length_append, ddFamily_length, List.length_replicate]
        omega)
    (by rw [List.length_append, ddFamily_length, List.length_replicate]
        omega)
    ddFamilyZ_range hw
  rw [Nat.zero_add, ddFamily_set hi] at hst
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hst))
  have hD := su_D_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (ddFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
    ((i : Nat) : Int) ch
  have h4 := stepFnIter_chain h3 hD
  have hA1 := su_A1_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (ddFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
    ((i : Nat) : Int) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  exact stepFnIter_chain h4 hA1

/-- **The setup loop**, by the P5 iteration schema: exactly `57·(n−i)`
steps materialize the wrapped `seed + i/2` family. -/
theorem su_loopD (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 63) :
    ∀ i, i ≤ n → ∀ ch : Choices,
    stepFnIter (57 * (n - i))
      (dSt σ (dHeapSu ((n : Nat) : Int) ((seed : Nat) : Int)
        n (ddFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false) 10)
      (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
        suCmpKD) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) suCmpKD,
          dSt σ (dHeapSu ((n : Nat) : Int) ((seed : Nat) : Int)
            n (ddFamily n seed) ((n : Nat) : Int) false) 10, ch) := by
  intro i hin ch
  have hgen := stepFnIter_iterate (c := 57) (n := n)
    (T := fun j => dSt σ (dHeapSu ((n : Nat) : Int) ((seed : Nat) : Int)
      n (ddFamily j seed ++ List.replicate (n - j) 0)
      ((j : Nat) : Int) false) 10)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int)
      < ((n : Nat) : Int)))) suCmpKD)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact su_iterD σ n seed j hn hj ch')
    i hin ch
  simpa using hgen

/-! ### The copy loop -/

theorem cp_A0_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 25 (dSt σ (dHeapCp nv sv n l lp siv civ true) 13)
      cpHeadCfgD ch
      = .ok (.retV (.bool (decide (civ < nv))) cpCmpKD,
          dSt σ (dHeapCp nv sv n l lp siv civ false) 13, ch) := by
  with_unfolding_all rfl

theorem cp_A1_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 29 (dSt σ (dHeapCp nv sv n l lp siv civ false) 13)
      cpHeadCfgD ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1))
              < nv))) cpCmpKD,
          dSt σ (dHeapCp nv sv n l lp siv
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1)))
            false) 13, ch) := by
  with_unfolding_all rfl

/-- Copy phase 1: test true → the `pre[i]` target banked, the `s[i]`
read at its apply point. 16 steps. -/
theorem cp_B1_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 16 (dSt σ (dHeapCp nv sv n l lp siv civ false) 13)
      (.retV (.bool true) cpCmpKD) ch
      = .ok (.retV (.int civ .uint64)
            (.strictK .indexGet [dSliceV n] [] cpEnvD2 (cpRhsKD civ)),
          dSt σ (dHeapCp nv sv n l lp siv civ false) 13, ch) := by
  with_unfolding_all rfl

theorem cp_B2_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1 (dSt σ (dHeapCp nv sv n l lp siv civ false) 13)
      (.retV w (cpRhsKD civ)) ch
      = .ok (.next (.storeK [cpRefD civ] [w] (.seqn #[]) cpEnvD2 cpStTailD),
          dSt σ (dHeapCp nv sv n l lp siv civ false) 13, ch) := by
  with_unfolding_all rfl

theorem cp_D_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 5 (dSt σ (dHeapCp nv sv n l lp siv civ false) 13)
      (.next (.storeK [] [] (.seqn #[]) cpEnvD2 cpStTailD)) ch
      = .ok (cpHeadCfgD, dSt σ (dHeapCp nv sv n l lp siv civ false) 13,
          ch) := by
  with_unfolding_all rfl

/-- One copy iteration from the exit test's true delivery at `m`. 53
steps. -/
theorem cp_iterD (σ : ExecState) (n seed : Nat) (siv : Int) (m : Nat)
    (hn : n < 2 ^ 63) (hcap : n ≤ 8) (hm : m < n) (ch : Choices) :
    stepFnIter 53
      (dSt σ (dHeapCp ((n : Nat) : Int) ((seed : Nat) : Int)
        n (ddFamily n seed) (ddPre m seed) siv ((m : Nat) : Int) false) 13)
      (.retV (.bool true) cpCmpKD) ch
      = .ok (.retV (.bool (decide
            (((m + 1 : Nat) : Int) < ((n : Nat) : Int)))) cpCmpKD,
          dSt σ (dHeapCp ((n : Nat) : Int) ((seed : Nat) : Int)
            n (ddFamily n seed) (ddPre (m + 1) seed) siv
            ((m + 1 : Nat) : Int) false) 13, ch) := by
  have hB1 := cp_B1_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (ddFamily n seed) (ddPre m seed) siv ((m : Nat) : Int) ch
  have hget : (⟨(ddFamily n seed).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + m]?
      = some (.int (((seed + m / 2) % 2 ^ 64 : Nat) : Int) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by rw [ddFamily_length]; omega),
      ddFamily_getD hm]
  have hread := stepFn_strict_apply (done := [dSliceV n]) (env := cpEnvD2)
    (k := cpRhsKD ((m : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .uint64)
      (lookup_cpS_D σ ((n : Nat) : Int) ((seed : Nat) : Int) n
        (ddFamily n seed) (ddPre m seed) siv ((m : Nat) : Int) false 13)
      (Nat.le_refl n) hm hget)
  have hB2 := cp_B2_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (ddFamily n seed) (ddPre m seed) siv ((m : Nat) : Int)
    (.int (((seed + m / 2) % 2 ^ 64 : Nat) : Int) .uint64) ch
  have hw : (0 : Int) ≤ (((seed + m / 2) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + m / 2) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + m / 2) (y := 2 ^ 64) (by omega)
    omega
  have hst := storeTarget_arrayLocal_u64 (a := ⟨10⟩) (N := 8) (i := m)
    (ik := .uint64) (l := ddPre m seed)
    (w := (((seed + m / 2) % 2 ^ 64 : Nat) : Int))
    (lookup_cpPre_D σ ((n : Nat) : Int) ((seed : Nat) : Int) n
      (ddFamily n seed) (ddPre m seed) siv ((m : Nat) : Int) false 13)
    (by rw [ddPre_length (by omega)]; omega)
    (ddPre_length (by omega)) ddPre_range hw
  rw [ddPre_set (by omega : m < 8)] at hst
  have hstore : storeTarget
      (dSt σ (dHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
        (ddFamily n seed) (ddPre m seed) siv ((m : Nat) : Int) false) 13)
      (cpRefD ((m : Nat) : Int))
      (.int (((seed + m / 2) % 2 ^ 64 : Nat) : Int) .uint64)
      = .ok (dSt σ (dHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
          (ddFamily n seed) (ddPre (m + 1) seed) siv ((m : Nat) : Int)
          false) 13) := hst
  have hD := cp_D_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (ddFamily n seed) (ddPre (m + 1) seed) siv ((m : Nat) : Int) ch
  have hA1 := cp_A1_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (ddFamily n seed) (ddPre (m + 1) seed) siv ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  have h1 := stepFnIter_chain hB1 (stepFnIter_one hread)
  have h2 := stepFnIter_chain h1 hB2
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hstore))
  exact stepFnIter_chain (stepFnIter_chain h3 hD) hA1

/-- **The copy loop**: exactly `53·(n−m)` steps snapshot the family
into `pre`. -/
theorem cp_loopD (σ : ExecState) (n seed : Nat) (siv : Int)
    (hn : n < 2 ^ 63) (hcap : n ≤ 8) :
    ∀ m, m ≤ n → ∀ ch : Choices,
    stepFnIter (53 * (n - m))
      (dSt σ (dHeapCp ((n : Nat) : Int) ((seed : Nat) : Int)
        n (ddFamily n seed) (ddPre m seed) siv ((m : Nat) : Int) false) 13)
      (.retV (.bool (decide (((m : Nat) : Int) < ((n : Nat) : Int))))
        cpCmpKD) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) cpCmpKD,
          dSt σ (dHeapCp ((n : Nat) : Int) ((seed : Nat) : Int)
            n (ddFamily n seed) (ddPre n seed) siv ((n : Nat) : Int)
            false) 13, ch) := by
  intro m hmn ch
  have hgen := stepFnIter_iterate (c := 53) (n := n)
    (T := fun j => dSt σ (dHeapCp ((n : Nat) : Int) ((seed : Nat) : Int)
      n (ddFamily n seed) (ddPre j seed) siv ((j : Nat) : Int) false) 13)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int)
      < ((n : Nat) : Int)))) cpCmpKD)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact cp_iterD σ n seed siv j hn hcap hj ch')
    m hmn ch
  simpa using hgen

/-- Copy exit: test false → `var r` declared and the `dedupAdjacent(s)`
argument delivered at the drained `callArgsK`. 13 steps. -/
theorem cp_X_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 13 (dSt σ (dHeapCp nv sv n l lp siv civ false) 13)
      (.retV (.bool false) cpCmpKD) ch
      = .ok (.retV (dSliceV n) dCallArgsK,
          dSt σ (dHeapCall nv sv n l lp siv civ) 14, ch) := by
  with_unfolding_all rfl

/-! ### The subject: frame entry, prologue, dispatch, guard, branches -/

/-- The `enterFrame` discharge at the pinned program: the second and
last unfolding of `dedupLowered` in this example (the slice parameter
normalizes to itself, so no side condition is needed). -/
theorem d_enterFrame_fact (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) :
    enterFrame (dSt ddProg (dHeapCall nv sv n l lp siv civ) 14)
        ⟨"dedupAdjacent"⟩ [dSliceV n]
      = .ok (dedupAdjacentFunc, sjFrameEnv, [.base ⟨15⟩],
          dSt ddProg (dHeapFrame nv sv n l lp siv civ) 16) := by
  with_unfolding_all rfl

/-- The subject prologue: `k := 0`, `i := 0`, the flag → the subject's
loop head. 43 steps, program-free given the frame entry. -/
theorem sj_prologue_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ch : Choices) :
    stepFnIter 43 (dSt σ (dHeapFrame nv sv n l lp siv civ) 16)
      (.exec dedupAdjacentFunc.body sjFrameEnv frameKD) ch
      = .ok (sjHeadCfg,
          dSt σ (dHeapSj nv sv n l lp siv civ 0 0 true) 19, ch) := by
  with_unfolding_all rfl

theorem sj_A0_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ kv iv : Int) (ch : Choices) :
    stepFnIter 25 (dSt σ (dHeapSj nv sv n l lp siv civ kv iv true) 19)
      sjHeadCfg ch
      = .ok (.retV (dSliceV n) (sjLenK iv),
          dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19, ch) := by
  with_unfolding_all rfl

theorem sj_A1_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ kv iv : Int) (ch : Choices) :
    stepFnIter 29 (dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19)
      sjHeadCfg ch
      = .ok (.retV (dSliceV n)
            (sjLenK (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
          dSt σ (dHeapSj nv sv n l lp siv civ kv
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            false) 19, ch) := by
  with_unfolding_all rfl

/-- The exit-test comparison at symbolic operands. 1 step. -/
theorem sj_cmp_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ kv iv : Int) (L jv : Int) (ch : Choices) :
    stepFnIter 1 (dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19)
      (.retV (.int L .int) (.strictK .lessCmp [.int jv .int] [] sjEnvB sjCmpK))
      ch
      = .ok (.retV (.bool (decide (jv < L))) sjCmpK,
          dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19, ch) := by
  with_unfolding_all rfl

/-- Guard phase B1: test true → the `k == 0` apply point (the `k` read
banked, the literal delivered). 11 steps. -/
theorem sj_B1_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ kv iv : Int) (ch : Choices) :
    stepFnIter 11 (dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19)
      (.retV (.bool true) sjCmpK) ch
      = .ok (.retV (.int 0 .int) (sjEqK kv),
          dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19, ch) := by
  with_unfolding_all rfl

/-- The SHORT-CIRCUIT: `k == 0` TRUE consumes the `or` without ever
evaluating the `s[k-1]` read. 1 step. -/
theorem sj_orT_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ kv iv : Int) (ch : Choices) :
    stepFnIter 1 (dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19)
      (.retV (.bool true) sjOrK) ch
      = .ok (.retV (.bool true) sjIfK,
          dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19, ch) := by
  with_unfolding_all rfl

/-- `k == 0` FALSE: the `or` evaluates its right disjunct — up to the
`s[i]` read's apply point. 6 steps. -/
theorem sj_orF_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ kv iv : Int) (ch : Choices) :
    stepFnIter 6 (dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19)
      (.retV (.bool false) sjOrK) ch
      = .ok (.retV (.int iv .int) (sjIdx1K n),
          dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19, ch) := by
  with_unfolding_all rfl

/-- The `s[i]` value delivered → the `k - 1` apply point. 8 steps. -/
theorem sj_neq2_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ kv iv : Int) (x : GoValue) (ch : Choices) :
    stepFnIter 8 (dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19)
      (.retV x sjNeq1K) ch
      = .ok (.retV (.int 1 .int) (sjSubK n x kv),
          dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19, ch) := by
  with_unfolding_all rfl

/-- The `boolK` forward: the right disjunct's value IS the `or`'s. 1
step, symbolic in the boolean. -/
theorem sj_boolK_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ kv iv : Int) (b : Bool) (ch : Choices) :
    stepFnIter 1 (dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19)
      (.retV (.bool b) (.boolK sjIfK)) ch
      = .ok (.retV (.bool b) sjIfK,
          dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19, ch) := by
  with_unfolding_all rfl

/-- KEEP phase C1: guard true → the `s[k]` target banked, the `s[i]`
re-read at its apply point. 14 steps. -/
theorem sj_C1_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ kv iv : Int) (ch : Choices) :
    stepFnIter 14 (dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19)
      (.retV (.bool true) sjIfK) ch
      = .ok (.retV (.int iv .int) (sjKeepIdxK n kv),
          dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19, ch) := by
  with_unfolding_all rfl

/-- KEEP phase C2: the read value → the element-store point. 1 step. -/
theorem sj_C2_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ kv iv : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1 (dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19)
      (.retV w (sjKeepRhsK n kv)) ch
      = .ok (.next (.storeK [sjKeepRef n kv] [w] (.seqn #[]) sjEnvKp
            sjKeepStTail),
          dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19, ch) := by
  with_unfolding_all rfl

/-- KEEP phase C3: the store drains → `k++` → the loop head. 19
steps. -/
theorem sj_C3_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ kv iv : Int) (ch : Choices) :
    stepFnIter 19 (dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19)
      (.next (.storeK [] [] (.seqn #[]) sjEnvKp sjKeepStTail)) ch
      = .ok (sjHeadCfg,
          dSt σ (dHeapSj nv sv n l lp siv civ
            (IntKind.normalize .int (IntKind.normalize .int (kv + 1)))
            iv false) 19, ch) := by
  with_unfolding_all rfl

/-- SKIP: guard false → straight back to the loop head. 5 steps. -/
theorem sj_skip_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ kv iv : Int) (ch : Choices) :
    stepFnIter 5 (dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19)
      (.retV (.bool false) sjIfK) ch
      = .ok (sjHeadCfg,
          dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19, ch) := by
  with_unfolding_all rfl

/-- Subject exit phase X1: test false → break unwinding → the
`s[0:k]` slice-expression apply point (the `k` read delivered). 18
steps. -/
theorem sj_X1_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ kv iv : Int) (ch : Choices) :
    stepFnIter 18 (dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19)
      (.retV (.bool false) sjCmpK) ch
      = .ok (.retV (.int kv .int) (sjSliceK n),
          dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19, ch) := by
  with_unfolding_all rfl

/-- Subject exit phase X2: the surviving-prefix handle delivered → the
subject's `$res0` store, the return, the frame's write-back into `r`,
the `post` declarations — the post loop head. 46 steps. -/
theorem sj_X2_rawD (σ : ExecState) (nv sv : Int) (n kk : Nat)
    (l lp : List Int) (siv civ kv iv : Int) (ch : Choices) :
    stepFnIter 46 (dSt σ (dHeapSj nv sv n l lp siv civ kv iv false) 19)
      (.retV (rSliceV kk n) sjResRhsK) ch
      = .ok (poHeadCfgD,
          dSt σ (dHeapPo nv sv n l lp zeros8 siv civ kk kv iv 0 true) 22,
          ch) := by
  with_unfolding_all rfl

/-! ### The post loop (`post[i] = r[i]`, `i < len(r)`, `int` counter) -/

theorem lookup_poS_D (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp po : List Int) (siv civ : Int) (kk : Nat) (kv sjiv iv : Int)
    (ff : Bool) (na : Nat) :
    Heap.lookup
        (dSt σ (dHeapPo nv sv n l lp po siv civ kk kv sjiv iv ff) na).heap
        (.base ⟨6⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [dHeapPo, dHeapCp, dHeapSu, dHeap0, Heap.lookup]

theorem lookup_poPost_D (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp po : List Int) (siv civ : Int) (kk : Nat) (kv sjiv iv : Int)
    (ff : Bool) (na : Nat) :
    Heap.lookup
        (dSt σ (dHeapPo nv sv n l lp po siv civ kk kv sjiv iv ff) na).heap
        (.base ⟨19⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨po.map (fun v => .int v .uint64)⟩⟩ := by
  simp [dHeapPo, dHeapCp, dHeapSu, dHeap0, Heap.lookup]

theorem po_A0_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp po : List Int) (siv civ : Int) (kk : Nat) (kv sjiv iv : Int)
    (ch : Choices) :
    stepFnIter 25
      (dSt σ (dHeapPo nv sv n l lp po siv civ kk kv sjiv iv true) 22)
      poHeadCfgD ch
      = .ok (.retV (rSliceV kk n) (poLenK iv),
          dSt σ (dHeapPo nv sv n l lp po siv civ kk kv sjiv iv false) 22,
          ch) := by
  with_unfolding_all rfl

theorem po_A1_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp po : List Int) (siv civ : Int) (kk : Nat) (kv sjiv iv : Int)
    (ch : Choices) :
    stepFnIter 29
      (dSt σ (dHeapPo nv sv n l lp po siv civ kk kv sjiv iv false) 22)
      poHeadCfgD ch
      = .ok (.retV (rSliceV kk n)
            (poLenK (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
          dSt σ (dHeapPo nv sv n l lp po siv civ kk kv sjiv
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            false) 22, ch) := by
  with_unfolding_all rfl

theorem po_cmp_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp po : List Int) (siv civ : Int) (kk : Nat) (kv sjiv iv : Int)
    (L jv : Int) (ch : Choices) :
    stepFnIter 1
      (dSt σ (dHeapPo nv sv n l lp po siv civ kk kv sjiv iv false) 22)
      (.retV (.int L .int)
        (.strictK .lessCmp [.int jv .int] [] ([] :: poEnvD) poCmpKD)) ch
      = .ok (.retV (.bool (decide (jv < L))) poCmpKD,
          dSt σ (dHeapPo nv sv n l lp po siv civ kk kv sjiv iv false) 22,
          ch) := by
  with_unfolding_all rfl

/-- Post phase 1: test true → the `post[i]` target banked, the `r[i]`
read at its apply point. 16 steps. -/
theorem po_B1_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp po : List Int) (siv civ : Int) (kk : Nat) (kv sjiv iv : Int)
    (ch : Choices) :
    stepFnIter 16
      (dSt σ (dHeapPo nv sv n l lp po siv civ kk kv sjiv iv false) 22)
      (.retV (.bool true) poCmpKD) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [rSliceV kk n] [] poEnvD2 (poRhsKD iv)),
          dSt σ (dHeapPo nv sv n l lp po siv civ kk kv sjiv iv false) 22,
          ch) := by
  with_unfolding_all rfl

theorem po_B2_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp po : List Int) (siv civ : Int) (kk : Nat) (kv sjiv iv : Int)
    (w : GoValue) (ch : Choices) :
    stepFnIter 1
      (dSt σ (dHeapPo nv sv n l lp po siv civ kk kv sjiv iv false) 22)
      (.retV w (poRhsKD iv)) ch
      = .ok (.next (.storeK [poRefD iv] [w] (.seqn #[]) poEnvD2 poStTailD),
          dSt σ (dHeapPo nv sv n l lp po siv civ kk kv sjiv iv false) 22,
          ch) := by
  with_unfolding_all rfl

theorem po_D_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp po : List Int) (siv civ : Int) (kk : Nat) (kv sjiv iv : Int)
    (ch : Choices) :
    stepFnIter 5
      (dSt σ (dHeapPo nv sv n l lp po siv civ kk kv sjiv iv false) 22)
      (.next (.storeK [] [] (.seqn #[]) poEnvD2 poStTailD)) ch
      = .ok (poHeadCfgD,
          dSt σ (dHeapPo nv sv n l lp po siv civ kk kv sjiv iv false) 22,
          ch) := by
  with_unfolding_all rfl

/-! ### The epilogue -/

/-- Epilogue phase 1: post-loop exit → the `pre` array read banked at
its store point. 14 steps. -/
theorem epi1_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp po : List Int) (siv civ : Int) (kk : Nat) (kv sjiv iv : Int)
    (ch : Choices) :
    stepFnIter 14
      (dSt σ (dHeapPo nv sv n l lp po siv civ kk kv sjiv iv false) 22)
      (.retV (.bool false) poCmpKD) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨2⟩)) [] []]
            [.array ⟨lp.map (fun v => .int v .uint64)⟩] (.seqn #[]) epiEnv
            (.seq epiRest1 epiEnv dBarrier)),
          dSt σ (dHeapPo nv sv n l lp po siv civ kk kv sjiv iv false) 22,
          ch) := by
  with_unfolding_all rfl

/-- Epilogue phase 2: the `$res0` store drained → the `post` array
read banked at its store point. 8 steps. -/
theorem epi2_rawD (σ : ExecState) (H : Heap) (po : List Int)
    (ch : Choices)
    (hlook : Heap.lookup H (.base ⟨19⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨po.map (fun v => .int v .uint64)⟩⟩) :
    stepFnIter 8 (dSt σ H 22)
      (.next (.storeK [] [] (.seqn #[]) epiEnv
        (.seq epiRest1 epiEnv dBarrier))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨3⟩)) [] []]
            [.array ⟨po.map (fun v => .int v .uint64)⟩] (.seqn #[]) epiEnv
            (.seq epiRest2 epiEnv dBarrier)),
          dSt σ H 22, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil (σ := dSt σ H 22)
    (body := .seqn #[]) (env := epiEnv)
    (k := .seq epiRest1 epiEnv dBarrier) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice (σ := dSt σ H 22)
    (ss := #[]) (env := epiEnv) (rest := epiRest1) (k := dBarrier)
    (ch := ch))
  have h3 : stepFnIter 4 (dSt σ H 22)
      (.next (.seq ((#[] : Array Stmt).toList ++ epiRest1) epiEnv dBarrier))
      ch
      = .ok (.evalE (.var "post") epiEnv
            (.rhsK .vals [.chain (.addr (.base ⟨3⟩)) [] []] [] []
              (.seqn #[]) epiEnv (.seq epiRest2 epiEnv dBarrier)),
          dSt σ H 22, ch) := by
    with_unfolding_all rfl
  have h4 := stepFnIter_one (stepFn_var (σ := dSt σ H 22)
    (x := "post") (env := epiEnv) (a := ⟨19⟩)
    (k := .rhsK .vals [.chain (.addr (.base ⟨3⟩)) [] []] [] []
      (.seqn #[]) epiEnv (.seq epiRest2 epiEnv dBarrier))
    (ch := ch)
    (c := ⟨some (.array 8 tU64), .array ⟨po.map (fun v => .int v .uint64)⟩⟩)
    rfl hlook)
  have h5 : stepFnIter 1 (dSt σ H 22)
      (.retV (.array ⟨po.map (fun v => .int v .uint64)⟩)
        (.rhsK .vals [.chain (.addr (.base ⟨3⟩)) [] []] [] []
          (.seqn #[]) epiEnv (.seq epiRest2 epiEnv dBarrier))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨3⟩)) [] []]
            [.array ⟨po.map (fun v => .int v .uint64)⟩] (.seqn #[]) epiEnv
            (.seq epiRest2 epiEnv dBarrier)),
          dSt σ H 22, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h1 h2) h3) h4) h5

/-- Epilogue phase 3: the `$res1` store drained → the `len(r)` read at
its apply point inside the conversion. 9 steps. -/
theorem epi3_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp po c2 : List Int) (siv civ : Int) (kk : Nat) (kv sjiv iv : Int)
    (ch : Choices) :
    stepFnIter 9
      (dSt σ (dHeapEndG nv sv n l lp po c2 po 0 siv civ kk kv sjiv iv) 22)
      (.next (.storeK [] [] (.seqn #[]) epiEnv
        (.seq epiRest2 epiEnv dBarrier))) ch
      = .ok (.retV (rSliceV kk n) epiLenK,
          dSt σ (dHeapEndG nv sv n l lp po c2 po 0 siv civ kk kv sjiv iv)
            22, ch) := by
  with_unfolding_all rfl

/-- Epilogue phase 4: the converted length delivered → its store
point. 1 step. -/
theorem epi4_rawD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp po c2 : List Int) (siv civ : Int) (kk : Nat) (kv sjiv iv : Int)
    (w : GoValue) (ch : Choices) :
    stepFnIter 1
      (dSt σ (dHeapEndG nv sv n l lp po c2 po 0 siv civ kk kv sjiv iv) 22)
      (.retV w epiRhsK2) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨4⟩)) [] []] [w]
            (.seqn #[]) epiEnv (.seq [.returnStmt] epiEnv dBarrier)),
          dSt σ (dHeapEndG nv sv n l lp po c2 po 0 siv civ kk kv sjiv iv)
            22, ch) := by
  with_unfolding_all rfl

/-- Epilogue phase 5: the `$res2` store drained → the return — the
driver terminal. 6 steps. -/
theorem epi5_rawD (σ : ExecState) (H : Heap) (ch : Choices) :
    stepFnIter 6 (dSt σ H 22)
      (.next (.storeK [] [] (.seqn #[]) epiEnv
        (.seq [.returnStmt] epiEnv dBarrier))) ch
      = .ok (.next .stop, dSt σ H 22, ch) := by
  with_unfolding_all rfl

/-! ## Pure bridges between the machine reads and the invariant -/

private theorem getD_eq_of_drop_eq {l orig : List Int} {i : Nat}
    (h : l.drop i = orig.drop i) :
    l.getD i 0 = orig.getD i 0 := by
  have h0 : l[i]? = orig[i]? := by
    have := congrArg (fun t => t[0]?) h
    simpa [List.getElem?_drop] using this
  simp [List.getD_eq_getElem?_getD, h0]

private theorem take_set_prefix {l d : List Int} {kv : Nat} {x : Int}
    (hk : kv < l.length) (htake : l.take kv = d) :
    (l.set kv x).take (kv + 1) = d ++ [x] := by
  rw [List.take_add_one, List.take_set, List.getElem?_set_self hk,
    show (l.take kv).set kv x = l.take kv from
      List.set_eq_of_length_le (by simpa using Nat.min_le_left kv l.length),
    htake]
  rfl

private theorem drop_set_high {l : List Int} {kv j : Nat} {x : Int}
    (h : kv < j) : (l.set kv x).drop j = l.drop j := by
  rw [List.drop_set, if_pos h]

private theorem drop_succ_of_drop_eq {l orig : List Int} {i : Nat}
    (h : l.drop i = orig.drop i) :
    l.drop (i + 1) = orig.drop (i + 1) := by
  have := congrArg (List.drop 1) h
  simpa [List.drop_drop] using this

private theorem take_succ_getD {orig : List Int} {i : Nat}
    (hi : i < orig.length) :
    orig.take (i + 1) = orig.take i ++ [orig.getD i 0] := by
  rw [List.take_add_one, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi]
  rfl

private theorem getD_take {l : List Int} {kv j : Nat} (hj : j < kv) :
    (l.take kv).getD j 0 = l.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hj]

/-! ## The subject loop: branch composites and the induction -/

theorem lookup_sjD (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ kv iv : Int) (ff : Bool) (na : Nat) :
    Heap.lookup (dSt σ (dHeapSj nv sv n l lp siv civ kv iv ff) na).heap
        (.base ⟨6⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [dHeapSj, dHeapFrame, dHeapCall, dHeapCp, dHeapSu, dHeap0,
    Heap.lookup]

/-- The subject-phase state at `Nat`-cast counters. -/
abbrev σSjN (σ : ExecState) (nv sv siv civ : Int) (n : Nat)
    (l lp : List Int) (kv i : Nat) : ExecState :=
  dSt σ (dHeapSj nv sv n l lp siv civ ((kv : Nat) : Int)
    ((i : Nat) : Int) false) 19

/-- The shared KEEP tail, from the guard's TRUE delivery at `ifK`:
`s[k] = s[i]; k++`, the next dispatch, the next exit test. 67 steps. -/
theorem sj_keep_tail (σ : ExecState) (nv sv siv civ : Int) (n : Nat)
    (l lp : List Int) (kv i : Nat) (hn : n ≤ 8) (hlen : l.length = n)
    (hkle : kv ≤ i) (hi : i < n)
    (hrange : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64) (ch : Choices) :
    stepFnIter 67 (σSjN σ nv sv siv civ n l lp kv i)
      (.retV (.bool true) sjIfK) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) sjCmpK,
          σSjN σ nv sv siv civ n (l.set kv (l.getD i 0)) lp (kv + 1)
            (i + 1), ch) := by
  have hxr : 0 ≤ l.getD i 0 ∧ l.getD i 0 < 2 ^ 64 :=
    hrange _ (getD_mem (by omega))
  have hC1 := sj_C1_rawD σ nv sv n l lp siv civ ((kv : Nat) : Int)
    ((i : Nat) : Int) ch
  have hget : (⟨l.map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + i]? = some (.int (l.getD i 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega)]
  have hread := stepFn_strict_apply (done := [dSliceV n]) (env := sjEnvKp)
    (k := sjKeepRhsK n ((kv : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .int)
      (lookup_sjD σ nv sv n l lp siv civ ((kv : Nat) : Int)
        ((i : Nat) : Int) false 19)
      (Nat.le_refl n) hi hget)
  have hC2 := sj_C2_rawD σ nv sv n l lp siv civ ((kv : Nat) : Int)
    ((i : Nat) : Int) (.int (l.getD i 0) .uint64) ch
  have hst := storeTarget_slice_u64
    (σ := σSjN σ nv sv siv civ n l lp kv i)
    (a := ⟨6⟩) (off := 0) (len := n) (cap := n) (i := kv) (n := n)
    (ik := .int) (l := l) (w := l.getD i 0)
    (lookup_sjD σ nv sv n l lp siv civ ((kv : Nat) : Int)
      ((i : Nat) : Int) false 19)
    (Nat.le_refl n) (by omega) (by omega) hlen hrange hxr
  rw [Nat.zero_add] at hst
  have hstore : storeTarget (σSjN σ nv sv siv civ n l lp kv i)
      (sjKeepRef n ((kv : Nat) : Int)) (.int (l.getD i 0) .uint64)
      = .ok (σSjN σ nv sv siv civ n (l.set kv (l.getD i 0)) lp kv i) := hst
  have hC3 := sj_C3_rawD σ nv sv n (l.set kv (l.getD i 0)) lp siv civ
    ((kv : Nat) : Int) ((i : Nat) : Int) ch
  rw [show ((kv : Nat) : Int) + 1 = ((kv + 1 : Nat) : Int) from by omega,
    inorm_nat_of_lt (by omega), inorm_nat_of_lt (by omega)] at hC3
  have hA1 := sj_A1_rawD σ nv sv n (l.set kv (l.getD i 0)) lp siv civ
    ((kv + 1 : Nat) : Int) ((i : Nat) : Int) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    inorm_nat_of_lt (by omega), inorm_nat_of_lt (by omega)] at hA1
  have hlen' : stepFn
      (σSjN σ nv sv siv civ n (l.set kv (l.getD i 0)) lp (kv + 1) (i + 1))
      (.retV (dSliceV n) (sjLenK ((i + 1 : Nat) : Int))) ch
      = .ok (.retV (.int ((n : Nat) : Int) .int)
          (.strictK .lessCmp [.int ((i + 1 : Nat) : Int) .int] [] sjEnvB
            sjCmpK),
        σSjN σ nv sv siv civ n (l.set kv (l.getD i 0)) lp (kv + 1) (i + 1),
        ch) :=
    stepFn_strict_apply (done := [])
      (applyStrictOp_len_slice (elem := tU64) (Nat.le_refl n))
  have hcmp := sj_cmp_rawD σ nv sv n (l.set kv (l.getD i 0)) lp siv civ
    ((kv + 1 : Nat) : Int) ((i + 1 : Nat) : Int) ((n : Nat) : Int)
    ((i + 1 : Nat) : Int) ch
  show stepFnIter (14 + 1 + 1 + 1 + 19 + 29 + 1 + 1) _ _ _ = _
  exact stepFnIter_chain
    (stepFnIter_chain
      (stepFnIter_chain
        (stepFnIter_chain
          (stepFnIter_chain
            (stepFnIter_chain
              (stepFnIter_chain hC1 (stepFnIter_one hread)) hC2)
            (stepFnIter_one (stepFn_store_step hstore)))
          hC3)
        hA1)
      (stepFnIter_one hlen'))
    hcmp

/-- One KEEP iteration on the SHORT-CIRCUIT path (`k == 0`; the
`s[k-1]` read never happens). 80 steps test-to-test. -/
theorem sj_iter_keep0 (σ : ExecState) (nv sv siv civ : Int) (n : Nat)
    (l lp : List Int) (i : Nat) (hn : n ≤ 8) (hlen : l.length = n)
    (hi : i < n) (hrange : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64) (ch : Choices) :
    stepFnIter 80 (σSjN σ nv sv siv civ n l lp 0 i)
      (.retV (.bool true) sjCmpK) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) sjCmpK,
          σSjN σ nv sv siv civ n (l.set 0 (l.getD i 0)) lp 1 (i + 1),
          ch) := by
  have hB1 := sj_B1_rawD σ nv sv n l lp siv civ (((0 : Nat)) : Int)
    ((i : Nat) : Int) ch
  have heq := stepFnIter_one (stepFn_strict_apply
    (done := [.int (((0 : Nat)) : Int) .int]) (env := sjEnvG)
    (k := sjOrK) (ch := ch)
    (applyStrictOp_eqCmp_int
      (σ := σSjN σ nv sv siv civ n l lp 0 i) (k := .int)
      (a := (((0 : Nat)) : Int)) (b := 0) (k1 := .int) (k2 := .int)))
  rw [show ((((0 : Nat)) : Int) == 0) = true from by decide] at heq
  have hor := sj_orT_rawD σ nv sv n l lp siv civ (((0 : Nat)) : Int)
    ((i : Nat) : Int) ch
  have htail := sj_keep_tail σ nv sv siv civ n l lp 0 i hn hlen
    (by omega) hi hrange ch
  show stepFnIter (11 + 1 + 1 + 67) _ _ _ = _
  exact stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain hB1 heq) hor) htail

/-- The shared guard evaluation on the `k ≠ 0` path: from the exit
test's TRUE delivery to the guard's boolean at `ifK`, where the
boolean is `s[i] != s[k-1]` on the REAL reads. 31 steps. -/
theorem sj_guard_ne (σ : ExecState) (nv sv siv civ : Int) (n : Nat)
    (l lp : List Int) (kv i : Nat) (hn : n ≤ 8) (hlen : l.length = n)
    (hkv : 1 ≤ kv) (hkle : kv ≤ i) (hi : i < n) (ch : Choices) :
    stepFnIter 31 (σSjN σ nv sv siv civ n l lp kv i)
      (.retV (.bool true) sjCmpK) ch
      = .ok (.retV (.bool (!(l.getD i 0 == l.getD (kv - 1) 0))) sjIfK,
          σSjN σ nv sv siv civ n l lp kv i, ch) := by
  have hB1 := sj_B1_rawD σ nv sv n l lp siv civ ((kv : Nat) : Int)
    ((i : Nat) : Int) ch
  have heq := stepFnIter_one (stepFn_strict_apply
    (done := [.int ((kv : Nat) : Int) .int]) (env := sjEnvG)
    (k := sjOrK) (ch := ch)
    (applyStrictOp_eqCmp_int
      (σ := σSjN σ nv sv siv civ n l lp kv i) (k := .int)
      (a := ((kv : Nat) : Int)) (b := 0) (k1 := .int) (k2 := .int)))
  rw [show (((kv : Nat) : Int) == 0) = false from by
    simp only [beq_eq_false_iff_ne, ne_eq, Int.natCast_eq_zero]
    omega] at heq
  have hor := sj_orF_rawD σ nv sv n l lp siv civ ((kv : Nat) : Int)
    ((i : Nat) : Int) ch
  have hget1 : (⟨l.map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + i]? = some (.int (l.getD i 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega)]
  have hread1 := stepFn_strict_apply (done := [dSliceV n]) (env := sjEnvG)
    (k := sjNeq1K) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .int)
      (lookup_sjD σ nv sv n l lp siv civ ((kv : Nat) : Int)
        ((i : Nat) : Int) false 19)
      (Nat.le_refl n) hi hget1)
  have hN2 := sj_neq2_rawD σ nv sv n l lp siv civ ((kv : Nat) : Int)
    ((i : Nat) : Int) (.int (l.getD i 0) .uint64) ch
  have hsub := stepFnIter_one (stepFn_strict_apply
    (done := [.int ((kv : Nat) : Int) .int]) (env := sjEnvG)
    (k := sjIdx2K n (.int (l.getD i 0) .uint64)) (ch := ch)
    (applyStrictOp_sub_int
      (σ := σSjN σ nv sv siv civ n l lp kv i) (a := kv) hkv (by omega)))
  have hget2 : (⟨l.map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + (kv - 1)]?
      = some (.int (l.getD (kv - 1) 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega)]
  have hread2 := stepFn_strict_apply (done := [dSliceV n]) (env := sjEnvG)
    (k := sjNeq2K (.int (l.getD i 0) .uint64)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .int)
      (lookup_sjD σ nv sv n l lp siv civ ((kv : Nat) : Int)
        ((i : Nat) : Int) false 19)
      (Nat.le_refl n) (by omega) hget2)
  have hneq := stepFnIter_one (stepFn_strict_apply
    (done := [.int (l.getD i 0) .uint64]) (env := sjEnvG)
    (k := .boolK sjIfK) (ch := ch)
    (applyStrictOp_neqCmp_int
      (σ := σSjN σ nv sv siv civ n l lp kv i) (k := .uint64)
      (a := l.getD i 0) (b := l.getD (kv - 1) 0)
      (k1 := .uint64) (k2 := .uint64)))
  have hbk := sj_boolK_rawD σ nv sv n l lp siv civ ((kv : Nat) : Int)
    ((i : Nat) : Int) (!(l.getD i 0 == l.getD (kv - 1) 0)) ch
  show stepFnIter (11 + 1 + 6 + 1 + 8 + 1 + 1 + 1 + 1) _ _ _ = _
  exact stepFnIter_chain
    (stepFnIter_chain
      (stepFnIter_chain
        (stepFnIter_chain
          (stepFnIter_chain
            (stepFnIter_chain
              (stepFnIter_chain (stepFnIter_chain hB1 heq) hor)
              (stepFnIter_one hread1))
            hN2)
          hsub)
        (stepFnIter_one hread2))
      hneq)
    hbk

/-- One KEEP iteration on the `k ≠ 0` path (`s[i] ≠ s[k-1]`). 98
steps test-to-test. -/
theorem sj_iter_keep (σ : ExecState) (nv sv siv civ : Int) (n : Nat)
    (l lp : List Int) (kv i : Nat) (hn : n ≤ 8) (hlen : l.length = n)
    (hkv : 1 ≤ kv) (hkle : kv ≤ i) (hi : i < n)
    (hrange : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64)
    (hne : l.getD i 0 ≠ l.getD (kv - 1) 0) (ch : Choices) :
    stepFnIter 98 (σSjN σ nv sv siv civ n l lp kv i)
      (.retV (.bool true) sjCmpK) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) sjCmpK,
          σSjN σ nv sv siv civ n (l.set kv (l.getD i 0)) lp (kv + 1)
            (i + 1), ch) := by
  have hg := sj_guard_ne σ nv sv siv civ n l lp kv i hn hlen hkv hkle hi ch
  rw [show (!(l.getD i 0 == l.getD (kv - 1) 0)) = true from by
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne,
      ne_eq]
    exact hne] at hg
  have htail := sj_keep_tail σ nv sv siv civ n l lp kv i hn hlen
    (by omega) hi hrange ch
  show stepFnIter (31 + 67) _ _ _ = _
  exact stepFnIter_chain hg htail

/-- One SKIP iteration (`k ≠ 0`, `s[i] = s[k-1]`): nothing moves but
the counter. 67 steps test-to-test. -/
theorem sj_iter_skip (σ : ExecState) (nv sv siv civ : Int) (n : Nat)
    (l lp : List Int) (kv i : Nat) (hn : n ≤ 8) (hlen : l.length = n)
    (hkv : 1 ≤ kv) (hkle : kv ≤ i) (hi : i < n)
    (heq : l.getD i 0 = l.getD (kv - 1) 0) (ch : Choices) :
    stepFnIter 67 (σSjN σ nv sv siv civ n l lp kv i)
      (.retV (.bool true) sjCmpK) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) sjCmpK,
          σSjN σ nv sv siv civ n l lp kv (i + 1), ch) := by
  have hg := sj_guard_ne σ nv sv siv civ n l lp kv i hn hlen hkv hkle hi ch
  rw [show (!(l.getD i 0 == l.getD (kv - 1) 0)) = false from by
    rw [heq]
    simp] at hg
  have hskip := sj_skip_rawD σ nv sv n l lp siv civ ((kv : Nat) : Int)
    ((i : Nat) : Int) ch
  have hA1 := sj_A1_rawD σ nv sv n l lp siv civ ((kv : Nat) : Int)
    ((i : Nat) : Int) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    inorm_nat_of_lt (by omega), inorm_nat_of_lt (by omega)] at hA1
  have hlen' : stepFn (σSjN σ nv sv siv civ n l lp kv (i + 1))
      (.retV (dSliceV n) (sjLenK ((i + 1 : Nat) : Int))) ch
      = .ok (.retV (.int ((n : Nat) : Int) .int)
          (.strictK .lessCmp [.int ((i + 1 : Nat) : Int) .int] [] sjEnvB
            sjCmpK),
        σSjN σ nv sv siv civ n l lp kv (i + 1), ch) :=
    stepFn_strict_apply (done := [])
      (applyStrictOp_len_slice (elem := tU64) (Nat.le_refl n))
  have hcmp := sj_cmp_rawD σ nv sv n l lp siv civ ((kv : Nat) : Int)
    ((i + 1 : Nat) : Int) ((n : Nat) : Int) ((i + 1 : Nat) : Int) ch
  show stepFnIter (31 + 5 + 29 + 1 + 1) _ _ _ = _
  exact stepFnIter_chain
    (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain hg hskip) hA1)
      (stepFnIter_one hlen'))
    hcmp

/-- **The subject loop**, by strong induction on the remaining
measure, carrying the in-place invariant from the module docstring —
the backing list is EXISTENTIAL in the conclusion, because the stale
region `[k, i)` is never read and never has to be described. Within
`98·μ` steps (98 = the widest branch, the `k ≠ 0` keep) the loop
reaches the exit test at `i = n` with the kept prefix equal to
`dedupAdj orig`. -/
theorem sj_loopD (σ : ExecState) (nv sv siv civ : Int) (n : Nat)
    (orig lp : List Int) (hn : n ≤ 8) (hlen : orig.length = n) :
    ∀ μ i, i + μ = n →
    ∀ l : List Int, l.length = n → l.drop i = orig.drop i →
      l.take (dedupAdj (orig.take i)).length = dedupAdj (orig.take i) →
      (∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64) →
    ∀ ch : Choices,
    ∃ (k : Nat) (l' : List Int), k ≤ 98 * μ ∧ l'.length = n ∧
      l'.take (dedupAdj orig).length = dedupAdj orig ∧
      (∀ v ∈ l', 0 ≤ v ∧ v < 2 ^ 64) ∧
      stepFnIter k
        (σSjN σ nv sv siv civ n l lp (dedupAdj (orig.take i)).length i)
        (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
          sjCmpK) ch
        = .ok (.retV (.bool (decide
              (((n : Nat) : Int) < ((n : Nat) : Int)))) sjCmpK,
            σSjN σ nv sv siv civ n l' lp (dedupAdj orig).length n, ch) := by
  intro μ
  induction μ with
  | zero =>
    intro i hi l hl hdrop htake hrange ch
    have hin : i = n := by omega
    subst hin
    have horig : orig.take i = orig := List.take_of_length_le (by omega)
    rw [horig] at htake
    refine ⟨0, l, by omega, hl, htake, hrange, ?_⟩
    rw [horig]
    rfl
  | succ μ' ih =>
    intro i hi l hl hdrop htake hrange ch
    have hilt : i < n := by omega
    rw [show (decide (((i : Nat) : Int) < ((n : Nat) : Int))) = true from
      decide_eq_true (by exact_mod_cast hilt)]
    have hkle : (dedupAdj (orig.take i)).length ≤ i :=
      Nat.le_trans (dedupAdj_length_le _) (by rw [List.length_take]; omega)
    have hxl : l.getD i 0 = orig.getD i 0 := getD_eq_of_drop_eq hdrop
    have htake1 : orig.take (i + 1)
        = orig.take i ++ [orig.getD i 0] := take_succ_getD (by omega)
    by_cases hk0 : (dedupAdj (orig.take i)).length = 0
    · -- the SHORT-CIRCUIT keep: `k = 0`, so `s[k-1]` is never read
      have hd : dedupAdj (orig.take i) = [] :=
        List.eq_nil_of_length_eq_zero hk0
      have hp : orig.take i = [] := by
        cases hq : orig.take i with
        | nil => rfl
        | cons a t =>
            rw [hq] at hd
            exact absurd hd (dedupAdj_ne_nil (by simp))
      have hsnoc : dedupAdj (orig.take (i + 1))
          = [orig.getD i 0] := by
        rw [htake1, dedupAdj_snoc, hp]
        simp
      have hmach := sj_iter_keep0 σ nv sv siv civ n l lp i hn hl hilt
        hrange ch
      rw [hxl] at hmach
      have hl' : (l.set 0 (orig.getD i 0)).length = n := by simp [hl]
      have hdrop' : (l.set 0 (orig.getD i 0)).drop (i + 1)
          = orig.drop (i + 1) := by
        rw [drop_set_high (by omega), drop_succ_of_drop_eq hdrop]
      have htake' : (l.set 0 (orig.getD i 0)).take
            (dedupAdj (orig.take (i + 1))).length
          = dedupAdj (orig.take (i + 1)) := by
        rw [hsnoc]
        exact take_set_prefix (kv := 0) (by omega) rfl
      have hrange' : ∀ v ∈ l.set 0 (orig.getD i 0),
          0 ≤ v ∧ v < 2 ^ 64 := by
        intro v hv
        rcases mem_set_of_mem hv with rfl | hv
        · rw [← hxl]; exact hrange _ (getD_mem (by omega))
        · exact hrange v hv
      obtain ⟨k, l', hk, hl'', htake'', hrange'', hrun⟩ :=
        ih (i + 1) (by omega) (l.set 0 (orig.getD i 0)) hl' hdrop'
          htake' hrange' ch
      refine ⟨80 + k, l', by omega, hl'', htake'', hrange'', ?_⟩
      rw [show (dedupAdj (orig.take i)).length = 0 from hk0]
      rw [show (dedupAdj (orig.take (i + 1))).length = 1 from
        (by rw [hsnoc]; rfl)] at hrun
      exact stepFnIter_chain hmach hrun
    · -- `k ≠ 0`: the guard really compares `s[i]` with `s[k-1]`
      have hd_ne : dedupAdj (orig.take i) ≠ [] := by
        intro hc; exact hk0 (by rw [hc]; rfl)
      have hyl : l.getD ((dedupAdj (orig.take i)).length - 1) 0
          = (dedupAdj (orig.take i)).getD
              ((dedupAdj (orig.take i)).length - 1) 0 := by
        rw [← getD_take (l := l) (kv := (dedupAdj (orig.take i)).length)
          (by omega), htake]
      have hlast : (orig.take i).getLast?
          = some ((dedupAdj (orig.take i)).getD
              ((dedupAdj (orig.take i)).length - 1) 0) := by
        rw [← dedupAdj_getLast?]
        exact getLast?_eq_getD hd_ne
      by_cases hxy : orig.getD i 0
          = (dedupAdj (orig.take i)).getD
              ((dedupAdj (orig.take i)).length - 1) 0
      · -- SKIP: the element equals the last kept one
        have hsnoc : dedupAdj (orig.take (i + 1))
            = dedupAdj (orig.take i) := by
          rw [htake1, dedupAdj_snoc, if_pos (by rw [hlast, hxy])]
        have hmach := sj_iter_skip σ nv sv siv civ n l lp
          (dedupAdj (orig.take i)).length i hn hl
          (by omega) hkle hilt (by rw [hxl, hyl, hxy]) ch
        obtain ⟨k, l', hk, hl'', htake'', hrange'', hrun⟩ :=
          ih (i + 1) (by omega) l hl (drop_succ_of_drop_eq hdrop)
            (by rw [hsnoc]; exact htake) hrange ch
        refine ⟨67 + k, l', by omega, hl'', htake'', hrange'', ?_⟩
        rw [show (dedupAdj (orig.take (i + 1))).length
            = (dedupAdj (orig.take i)).length from by rw [hsnoc]] at hrun
        exact stepFnIter_chain hmach hrun
      · -- KEEP: the element differs from the last kept one
        have hsnoc : dedupAdj (orig.take (i + 1))
            = dedupAdj (orig.take i) ++ [orig.getD i 0] := by
          rw [htake1, dedupAdj_snoc, if_neg (by
            rw [hlast]
            intro hc
            exact hxy (by injection hc with h; exact h.symm))]
        have hmach := sj_iter_keep σ nv sv siv civ n l lp
          (dedupAdj (orig.take i)).length i hn hl
          (by omega) hkle hilt hrange
          (by rw [hxl, hyl]; exact hxy) ch
        rw [hxl] at hmach
        have hl' : (l.set (dedupAdj (orig.take i)).length
            (orig.getD i 0)).length = n := by simp [hl]
        have hdrop' : (l.set (dedupAdj (orig.take i)).length
              (orig.getD i 0)).drop (i + 1)
            = orig.drop (i + 1) := by
          rw [drop_set_high (by omega), drop_succ_of_drop_eq hdrop]
        have htake' : (l.set (dedupAdj (orig.take i)).length
              (orig.getD i 0)).take
              (dedupAdj (orig.take (i + 1))).length
            = dedupAdj (orig.take (i + 1)) := by
          rw [hsnoc, List.length_append]
          exact take_set_prefix (by omega) htake
        have hrange' : ∀ v ∈ l.set (dedupAdj (orig.take i)).length
            (orig.getD i 0), 0 ≤ v ∧ v < 2 ^ 64 := by
          intro v hv
          rcases mem_set_of_mem hv with rfl | hv
          · rw [← hxl]; exact hrange _ (getD_mem (by omega))
          · exact hrange v hv
        obtain ⟨k, l', hk, hl'', htake'', hrange'', hrun⟩ :=
          ih (i + 1) (by omega)
            (l.set (dedupAdj (orig.take i)).length (orig.getD i 0)) hl'
            hdrop' htake' hrange' ch
        refine ⟨98 + k, l', by omega, hl'', htake'', hrange'', ?_⟩
        rw [show (dedupAdj (orig.take (i + 1))).length
            = (dedupAdj (orig.take i)).length + 1 from
          (by rw [hsnoc, List.length_append]; rfl)] at hrun
        exact stepFnIter_chain hmach hrun

/-! ## The post loop's induction -/

/-- The post-phase state at `Nat`-cast counters. -/
abbrev σPoN (σ : ExecState) (nv sv siv civ : Int) (n : Nat)
    (l lp po : List Int) (kk : Nat) (kvI sjivI : Int) (m : Nat) :
    ExecState :=
  dSt σ (dHeapPo nv sv n l lp po siv civ kk kvI sjivI ((m : Nat) : Int)
    false) 22

/-- One post-copy iteration from the exit test's true delivery at `m`.
55 steps. -/
theorem po_iterD (σ : ExecState) (nv sv siv civ kvI sjivI : Int)
    (n : Nat) (vals l lp : List Int) (m : Nat) (hn : n ≤ 8)
    (hlen : l.length = n)
    (htake : l.take (dedupAdj vals).length = dedupAdj vals)
    (hkk : (dedupAdj vals).length ≤ n)
    (hm : m < (dedupAdj vals).length)
    (hvals : ∀ v ∈ vals, 0 ≤ v ∧ v < 2 ^ 64) (ch : Choices) :
    stepFnIter 55
      (σPoN σ nv sv siv civ n l lp (ddPost vals m) (dedupAdj vals).length
        kvI sjivI m)
      (.retV (.bool true) poCmpKD) ch
      = .ok (.retV (.bool (decide
            (((m + 1 : Nat) : Int)
              < (((dedupAdj vals).length : Nat) : Int)))) poCmpKD,
          σPoN σ nv sv siv civ n l lp (ddPost vals (m + 1))
            (dedupAdj vals).length kvI sjivI (m + 1), ch) := by
  have hw : (dedupAdj vals).getD m 0 ∈ vals :=
    dedupAdj_mem (getD_mem hm)
  have hwr : (0 : Int) ≤ (dedupAdj vals).getD m 0
      ∧ (dedupAdj vals).getD m 0 < 2 ^ 64 := hvals _ hw
  have hB1 := po_B1_rawD σ nv sv n l lp (ddPost vals m) siv civ
    (dedupAdj vals).length kvI sjivI ((m : Nat) : Int) ch
  have hlm : l.getD m 0 = (dedupAdj vals).getD m 0 := by
    rw [← getD_take (l := l) (kv := (dedupAdj vals).length) hm, htake]
  have hget : (⟨l.map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + m]?
      = some (.int ((dedupAdj vals).getD m 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega), hlm]
  have hread := stepFn_strict_apply (done := [rSliceV (dedupAdj vals).length n])
    (env := poEnvD2) (k := poRhsKD ((m : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .int)
      (lookup_poS_D σ nv sv n l lp (ddPost vals m) siv civ
        (dedupAdj vals).length kvI sjivI ((m : Nat) : Int) false 22)
      hkk hm hget)
  have hB2 := po_B2_rawD σ nv sv n l lp (ddPost vals m) siv civ
    (dedupAdj vals).length kvI sjivI ((m : Nat) : Int)
    (.int ((dedupAdj vals).getD m 0) .uint64) ch
  have hst := storeTarget_arrayLocal_u64 (a := ⟨19⟩) (N := 8) (i := m)
    (ik := .int) (l := ddPost vals m) (w := (dedupAdj vals).getD m 0)
    (lookup_poPost_D σ nv sv n l lp (ddPost vals m) siv civ
      (dedupAdj vals).length kvI sjivI ((m : Nat) : Int) false 22)
    (by rw [ddPost_length (by omega) (by omega)]; omega)
    (ddPost_length (by omega) (by omega)) (ddPost_range hvals) hwr
  rw [ddPost_set hm (by omega)] at hst
  have hstore : storeTarget
      (σPoN σ nv sv siv civ n l lp (ddPost vals m) (dedupAdj vals).length
        kvI sjivI m)
      (poRefD ((m : Nat) : Int)) (.int ((dedupAdj vals).getD m 0) .uint64)
      = .ok (σPoN σ nv sv siv civ n l lp (ddPost vals (m + 1))
          (dedupAdj vals).length kvI sjivI m) := hst
  have hD := po_D_rawD σ nv sv n l lp (ddPost vals (m + 1)) siv civ
    (dedupAdj vals).length kvI sjivI ((m : Nat) : Int) ch
  have hA1 := po_A1_rawD σ nv sv n l lp (ddPost vals (m + 1)) siv civ
    (dedupAdj vals).length kvI sjivI ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    inorm_nat_of_lt (by omega), inorm_nat_of_lt (by omega)] at hA1
  have hlen' : stepFn
      (σPoN σ nv sv siv civ n l lp (ddPost vals (m + 1))
        (dedupAdj vals).length kvI sjivI (m + 1))
      (.retV (rSliceV (dedupAdj vals).length n)
        (poLenK ((m + 1 : Nat) : Int))) ch
      = .ok (.retV (.int (((dedupAdj vals).length : Nat) : Int) .int)
          (.strictK .lessCmp [.int ((m + 1 : Nat) : Int) .int] []
            ([] :: poEnvD) poCmpKD),
        σPoN σ nv sv siv civ n l lp (ddPost vals (m + 1))
          (dedupAdj vals).length kvI sjivI (m + 1), ch) :=
    stepFn_strict_apply (done := [])
      (applyStrictOp_len_slice (elem := tU64) hkk)
  have hcmp := po_cmp_rawD σ nv sv n l lp (ddPost vals (m + 1)) siv civ
    (dedupAdj vals).length kvI sjivI ((m + 1 : Nat) : Int)
    (((dedupAdj vals).length : Nat) : Int) ((m + 1 : Nat) : Int) ch
  show stepFnIter (16 + 1 + 1 + 1 + 5 + 29 + 1 + 1) _ _ _ = _
  exact stepFnIter_chain
    (stepFnIter_chain
      (stepFnIter_chain
        (stepFnIter_chain
          (stepFnIter_chain
            (stepFnIter_chain
              (stepFnIter_chain hB1 (stepFnIter_one hread)) hB2)
            (stepFnIter_one (stepFn_store_step hstore)))
          hD)
        hA1)
      (stepFnIter_one hlen'))
    hcmp

/-- **The post loop**: exactly `55·kk` steps copy the surviving prefix
into `post`. -/
theorem po_loopD (σ : ExecState) (nv sv siv civ kvI sjivI : Int)
    (n : Nat) (vals l lp : List Int) (hn : n ≤ 8) (hlen : l.length = n)
    (htake : l.take (dedupAdj vals).length = dedupAdj vals)
    (hkk : (dedupAdj vals).length ≤ n)
    (hvals : ∀ v ∈ vals, 0 ≤ v ∧ v < 2 ^ 64) (ch : Choices) :
    stepFnIter (55 * (dedupAdj vals).length)
      (σPoN σ nv sv siv civ n l lp (ddPost vals 0) (dedupAdj vals).length
        kvI sjivI 0)
      (.retV (.bool (decide ((((0 : Nat)) : Int)
        < (((dedupAdj vals).length : Nat) : Int)))) poCmpKD) ch
      = .ok (.retV (.bool (decide
            ((((dedupAdj vals).length : Nat) : Int)
              < (((dedupAdj vals).length : Nat) : Int)))) poCmpKD,
          σPoN σ nv sv siv civ n l lp (ddPost vals (dedupAdj vals).length)
            (dedupAdj vals).length kvI sjivI (dedupAdj vals).length,
          ch) := by
  have hgen := stepFnIter_iterate (c := 55) (n := (dedupAdj vals).length)
    (T := fun j => σPoN σ nv sv siv civ n l lp (ddPost vals j)
      (dedupAdj vals).length kvI sjivI j)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int)
      < (((dedupAdj vals).length : Nat) : Int)))) poCmpKD)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int)
          < (((dedupAdj vals).length : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact po_iterD σ nv sv siv civ kvI sjivI n vals l lp j hn hlen
        htake hkk hj hvals ch')
    0 (by omega) ch
  simpa using hgen

/-! ## The run, end to end -/

/-- **The harness run, PROGRAM-generic**: within `263·n + 361` steps
the harness reaches the driver terminal with the family in `$res0`,
its adjacent-dedup (zero-padded) in `$res1`, and the surviving
prefix's length in `$res2`. -/
theorem dd_runs_generic (σ : ExecState) (n seed : Nat) (hcap : n ≤ 8)
    (henter : ∀ (l lp : List Int) (siv civ : Int),
      enterFrame (dSt σ (dHeapCall ((n : Nat) : Int) ((seed : Nat) : Int)
          n l lp siv civ) 14) ⟨"dedupAdjacent"⟩ [dSliceV n]
        = .ok (dedupAdjacentFunc, sjFrameEnv, [.base ⟨15⟩],
            dSt σ (dHeapFrame ((n : Nat) : Int) ((seed : Nat) : Int)
              n l lp siv civ) 16))
    (ch : Choices) :
    ∃ (k : Nat) (l' : List Int), k ≤ 263 * n + 361 ∧
      stepFnIter k
        (dSt σ (dHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)) 5) ddC0 ch
      = .ok (.next .stop,
          dSt σ (dHeapEnd ((n : Nat) : Int) ((seed : Nat) : Int) n l'
            (ddPre n seed)
            (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
            ((n : Nat) : Int) ((n : Nat) : Int)
            (dedupAdj (ddFamily n seed)).length
            (((dedupAdj (ddFamily n seed)).length : Nat) : Int)
            ((n : Nat) : Int)
            (((dedupAdj (ddFamily n seed)).length : Nat) : Int)) 22,
          ch) := by
  have hkkn : (dedupAdj (ddFamily n seed)).length ≤ n :=
    Nat.le_trans (dedupAdj_length_le _) (Nat.le_of_eq (ddFamily_length n seed))
  have hf : (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false :=
    decide_eq_false (by omega)
  -- entry
  have hE1 := d_E1_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) ch
  have hmk := stepFnIter_one (stepFn_makeSlice_u64_step
    (env := envC4D)
    (k := .seq [dS2, dS3, dS4, dS5, dS6, dS7, dS8, dS9] envC4D dBarrier)
    (d_make_apply σ ((n : Nat) : Int) ((seed : Nat) : Int) n ch))
  have hE2 := d_E2_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) n ch
  -- setup loop
  have hsuA0 := su_A0_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (List.replicate n 0) 0 ch
  have hsuLoop := su_loopD σ n seed (by omega) 0 (by omega) ch
  rw [hf] at hsuLoop
  have hsuX := su_X_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (ddFamily n seed) ((n : Nat) : Int) ch
  -- copy loop
  have hcpA0 := cp_A0_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (ddFamily n seed) zeros8 ((n : Nat) : Int) 0 ch
  have hcpLoop := cp_loopD σ n seed ((n : Nat) : Int) (by omega) hcap 0
    (by omega) ch
  rw [hf] at hcpLoop
  have hcpX := cp_X_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (ddFamily n seed) (ddPre n seed) ((n : Nat) : Int) ((n : Nat) : Int) ch
  -- the call
  have hent := stepFnIter_one
    (stepFn_call_enter (plans := dCallPlans) (env := callEnvD)
      (k := dAfterCall) (vals := []) (v := dSliceV n) (ch := ch)
      (henter (ddFamily n seed) (ddPre n seed) ((n : Nat) : Int)
        ((n : Nat) : Int)))
  have hpro := sj_prologue_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (ddFamily n seed) (ddPre n seed) ((n : Nat) : Int) ((n : Nat) : Int) ch
  -- subject loop
  have hsjA0 := sj_A0_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (ddFamily n seed) (ddPre n seed) ((n : Nat) : Int) ((n : Nat) : Int)
    0 0 ch
  have hsjLen := stepFnIter_one (stepFn_strict_apply (done := [])
    (env := sjEnvB)
    (k := .strictK .lessCmp [.int 0 .int] [] sjEnvB sjCmpK) (ch := ch)
    (applyStrictOp_len_slice
      (σ := dSt σ (dHeapSj ((n : Nat) : Int) ((seed : Nat) : Int) n
        (ddFamily n seed) (ddPre n seed) ((n : Nat) : Int)
        ((n : Nat) : Int) 0 0 false) 19)
      (b := .base ⟨6⟩) (off := 0) (elem := tU64) (Nat.le_refl n)))
  have hsjCmp := sj_cmp_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (ddFamily n seed) (ddPre n seed) ((n : Nat) : Int) ((n : Nat) : Int)
    0 0 ((n : Nat) : Int) 0 ch
  obtain ⟨k1, l', hk1, hl', htake', hrange', hsjLoop⟩ :=
    sj_loopD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((n : Nat) : Int)
      ((n : Nat) : Int) n (ddFamily n seed) (ddPre n seed) hcap
      (ddFamily_length n seed) n 0 (by omega) (ddFamily n seed)
      (ddFamily_length n seed) rfl rfl (ddFamily_range n seed) ch
  rw [hf] at hsjLoop
  -- subject exit
  have hsjX1 := sj_X1_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n l'
    (ddPre n seed) ((n : Nat) : Int) ((n : Nat) : Int)
    (((dedupAdj (ddFamily n seed)).length : Nat) : Int) ((n : Nat) : Int)
    ch
  have hslice := stepFnIter_one (stepFn_strict_apply
    (done := [.int 0 .int, dSliceV n]) (env := sjEnv0) (k := sjResRhsK)
    (ch := ch)
    (applyStrictOp_sliceExpr_slice
      (σ := dSt σ (dHeapSj ((n : Nat) : Int) ((seed : Nat) : Int) n l'
        (ddPre n seed) ((n : Nat) : Int) ((n : Nat) : Int)
        (((dedupAdj (ddFamily n seed)).length : Nat) : Int)
        ((n : Nat) : Int) false) 19)
      (b := .base ⟨6⟩) (k1 := .int) (k2 := .int) hkkn))
  have hsjX2 := sj_X2_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n
    (dedupAdj (ddFamily n seed)).length l' (ddPre n seed)
    ((n : Nat) : Int) ((n : Nat) : Int)
    (((dedupAdj (ddFamily n seed)).length : Nat) : Int) ((n : Nat) : Int)
    ch
  -- post loop
  have hpoA0 := po_A0_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n l'
    (ddPre n seed) zeros8 ((n : Nat) : Int) ((n : Nat) : Int)
    (dedupAdj (ddFamily n seed)).length
    (((dedupAdj (ddFamily n seed)).length : Nat) : Int) ((n : Nat) : Int)
    0 ch
  have hpoLen := stepFnIter_one (stepFn_strict_apply (done := [])
    (env := [] :: poEnvD)
    (k := .strictK .lessCmp [.int 0 .int] [] ([] :: poEnvD) poCmpKD)
    (ch := ch)
    (applyStrictOp_len_slice
      (σ := dSt σ (dHeapPo ((n : Nat) : Int) ((seed : Nat) : Int) n l'
        (ddPre n seed) zeros8 ((n : Nat) : Int) ((n : Nat) : Int)
        (dedupAdj (ddFamily n seed)).length
        (((dedupAdj (ddFamily n seed)).length : Nat) : Int)
        ((n : Nat) : Int) 0 false) 22)
      (b := .base ⟨6⟩) (off := 0) (elem := tU64) hkkn))
  have hpoCmp := po_cmp_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n l'
    (ddPre n seed) zeros8 ((n : Nat) : Int) ((n : Nat) : Int)
    (dedupAdj (ddFamily n seed)).length
    (((dedupAdj (ddFamily n seed)).length : Nat) : Int) ((n : Nat) : Int)
    0 (((dedupAdj (ddFamily n seed)).length : Nat) : Int) 0 ch
  have hpoLoop := po_loopD σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((n : Nat) : Int) ((n : Nat) : Int)
    (((dedupAdj (ddFamily n seed)).length : Nat) : Int) ((n : Nat) : Int)
    n (ddFamily n seed) l' (ddPre n seed) hcap hl' htake' hkkn
    (ddFamily_range n seed) ch
  rw [show (decide ((((dedupAdj (ddFamily n seed)).length : Nat) : Int)
      < (((dedupAdj (ddFamily n seed)).length : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hpoLoop
  -- epilogue
  have hepi1 := epi1_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n l'
    (ddPre n seed)
    (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
    ((n : Nat) : Int) ((n : Nat) : Int)
    (dedupAdj (ddFamily n seed)).length
    (((dedupAdj (ddFamily n seed)).length : Nat) : Int) ((n : Nat) : Int)
    (((dedupAdj (ddFamily n seed)).length : Nat) : Int) ch
  have hlook2 : Heap.lookup
      (dSt σ (dHeapPo ((n : Nat) : Int) ((seed : Nat) : Int) n l'
        (ddPre n seed)
        (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
        ((n : Nat) : Int) ((n : Nat) : Int)
        (dedupAdj (ddFamily n seed)).length
        (((dedupAdj (ddFamily n seed)).length : Nat) : Int)
        ((n : Nat) : Int)
        (((dedupAdj (ddFamily n seed)).length : Nat) : Int) false) 22).heap
      (.base ⟨2⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun v => .int v .uint64)⟩⟩ := by
    simp [dHeapPo, dHeapCp, dHeapSu, dHeap0, Heap.lookup]
  have hst2 : storeTarget
      (dSt σ (dHeapPo ((n : Nat) : Int) ((seed : Nat) : Int) n l'
        (ddPre n seed)
        (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
        ((n : Nat) : Int) ((n : Nat) : Int)
        (dedupAdj (ddFamily n seed)).length
        (((dedupAdj (ddFamily n seed)).length : Nat) : Int)
        ((n : Nat) : Int)
        (((dedupAdj (ddFamily n seed)).length : Nat) : Int) false) 22)
      (.chain (.addr (.base ⟨2⟩)) [] [])
      (.array ⟨(ddPre n seed).map (fun v => .int v .uint64)⟩)
      = .ok (dSt σ (dHeapEndG ((n : Nat) : Int) ((seed : Nat) : Int) n l'
          (ddPre n seed)
          (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
          (ddPre n seed) zeros8 0 ((n : Nat) : Int) ((n : Nat) : Int)
          (dedupAdj (ddFamily n seed)).length
          (((dedupAdj (ddFamily n seed)).length : Nat) : Int)
          ((n : Nat) : Int)
          (((dedupAdj (ddFamily n seed)).length : Nat) : Int)) 22) :=
    storeTarget_addr hlook2
      (normalizeValueForTy_arr_u64 (ddPre_length hcap) ddPre_range)
  have hepi2 := epi2_rawD σ
    (dHeapEndG ((n : Nat) : Int) ((seed : Nat) : Int) n l'
      (ddPre n seed)
      (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
      (ddPre n seed) zeros8 0 ((n : Nat) : Int) ((n : Nat) : Int)
      (dedupAdj (ddFamily n seed)).length
      (((dedupAdj (ddFamily n seed)).length : Nat) : Int)
      ((n : Nat) : Int)
      (((dedupAdj (ddFamily n seed)).length : Nat) : Int))
    (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length) ch
    (by simp [dHeapEndG, Heap.lookup])
  have hlook3 : Heap.lookup
      (dSt σ (dHeapEndG ((n : Nat) : Int) ((seed : Nat) : Int) n l'
        (ddPre n seed)
        (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
        (ddPre n seed) zeros8 0 ((n : Nat) : Int) ((n : Nat) : Int)
        (dedupAdj (ddFamily n seed)).length
        (((dedupAdj (ddFamily n seed)).length : Nat) : Int)
        ((n : Nat) : Int)
        (((dedupAdj (ddFamily n seed)).length : Nat) : Int)) 22).heap
      (.base ⟨3⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun v => .int v .uint64)⟩⟩ := by
    simp [dHeapEndG, Heap.lookup]
  have hst3 : storeTarget
      (dSt σ (dHeapEndG ((n : Nat) : Int) ((seed : Nat) : Int) n l'
        (ddPre n seed)
        (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
        (ddPre n seed) zeros8 0 ((n : Nat) : Int) ((n : Nat) : Int)
        (dedupAdj (ddFamily n seed)).length
        (((dedupAdj (ddFamily n seed)).length : Nat) : Int)
        ((n : Nat) : Int)
        (((dedupAdj (ddFamily n seed)).length : Nat) : Int)) 22)
      (.chain (.addr (.base ⟨3⟩)) [] [])
      (.array ⟨(ddPost (ddFamily n seed)
          (dedupAdj (ddFamily n seed)).length).map
        (fun v => .int v .uint64)⟩)
      = .ok (dSt σ (dHeapEndG ((n : Nat) : Int) ((seed : Nat) : Int) n l'
          (ddPre n seed)
          (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
          (ddPre n seed)
          (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
          0 ((n : Nat) : Int) ((n : Nat) : Int)
          (dedupAdj (ddFamily n seed)).length
          (((dedupAdj (ddFamily n seed)).length : Nat) : Int)
          ((n : Nat) : Int)
          (((dedupAdj (ddFamily n seed)).length : Nat) : Int)) 22) :=
    storeTarget_addr hlook3
      (normalizeValueForTy_arr_u64
        (ddPost_length (Nat.le_refl _) (by omega))
        (ddPost_range (ddFamily_range n seed)))
  have hepi3 := epi3_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n l'
    (ddPre n seed)
    (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
    (ddPre n seed) ((n : Nat) : Int) ((n : Nat) : Int)
    (dedupAdj (ddFamily n seed)).length
    (((dedupAdj (ddFamily n seed)).length : Nat) : Int) ((n : Nat) : Int)
    (((dedupAdj (ddFamily n seed)).length : Nat) : Int) ch
  have hepiLen := stepFnIter_one (stepFn_strict_apply (done := [])
    (env := epiEnv)
    (k := .strictK (.convert tU64) [] [] epiEnv epiRhsK2) (ch := ch)
    (applyStrictOp_len_slice
      (σ := dSt σ (dHeapEndG ((n : Nat) : Int) ((seed : Nat) : Int) n l'
        (ddPre n seed)
        (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
        (ddPre n seed)
        (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
        0 ((n : Nat) : Int) ((n : Nat) : Int)
        (dedupAdj (ddFamily n seed)).length
        (((dedupAdj (ddFamily n seed)).length : Nat) : Int)
        ((n : Nat) : Int)
        (((dedupAdj (ddFamily n seed)).length : Nat) : Int)) 22)
      (b := .base ⟨6⟩) (off := 0) (elem := tU64) hkkn))
  have hconv := stepFnIter_one (stepFn_strict_apply (done := [])
    (env := epiEnv) (k := epiRhsK2) (ch := ch)
    (applyStrictOp_convert_u64
      (σ := dSt σ (dHeapEndG ((n : Nat) : Int) ((seed : Nat) : Int) n l'
        (ddPre n seed)
        (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
        (ddPre n seed)
        (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
        0 ((n : Nat) : Int) ((n : Nat) : Int)
        (dedupAdj (ddFamily n seed)).length
        (((dedupAdj (ddFamily n seed)).length : Nat) : Int)
        ((n : Nat) : Int)
        (((dedupAdj (ddFamily n seed)).length : Nat) : Int)) 22)
      (a := (dedupAdj (ddFamily n seed)).length) (k := .int)
      (by omega)))
  have hepi4 := epi4_rawD σ ((n : Nat) : Int) ((seed : Nat) : Int) n l'
    (ddPre n seed)
    (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
    (ddPre n seed) ((n : Nat) : Int) ((n : Nat) : Int)
    (dedupAdj (ddFamily n seed)).length
    (((dedupAdj (ddFamily n seed)).length : Nat) : Int) ((n : Nat) : Int)
    (((dedupAdj (ddFamily n seed)).length : Nat) : Int)
    (.int (((dedupAdj (ddFamily n seed)).length : Nat) : Int) .uint64) ch
  have hlook4 : Heap.lookup
      (dSt σ (dHeapEndG ((n : Nat) : Int) ((seed : Nat) : Int) n l'
        (ddPre n seed)
        (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
        (ddPre n seed)
        (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
        0 ((n : Nat) : Int) ((n : Nat) : Int)
        (dedupAdj (ddFamily n seed)).length
        (((dedupAdj (ddFamily n seed)).length : Nat) : Int)
        ((n : Nat) : Int)
        (((dedupAdj (ddFamily n seed)).length : Nat) : Int)) 22).heap
      (.base ⟨4⟩)
      = some ⟨some tU64, .int 0 .uint64⟩ := by
    simp [dHeapEndG, Heap.lookup]
  have hst4 : storeTarget
      (dSt σ (dHeapEndG ((n : Nat) : Int) ((seed : Nat) : Int) n l'
        (ddPre n seed)
        (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
        (ddPre n seed)
        (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
        0 ((n : Nat) : Int) ((n : Nat) : Int)
        (dedupAdj (ddFamily n seed)).length
        (((dedupAdj (ddFamily n seed)).length : Nat) : Int)
        ((n : Nat) : Int)
        (((dedupAdj (ddFamily n seed)).length : Nat) : Int)) 22)
      (.chain (.addr (.base ⟨4⟩)) [] [])
      (.int (((dedupAdj (ddFamily n seed)).length : Nat) : Int) .uint64)
      = .ok (dSt σ (dHeapEnd ((n : Nat) : Int) ((seed : Nat) : Int) n l'
          (ddPre n seed)
          (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
          ((n : Nat) : Int) ((n : Nat) : Int)
          (dedupAdj (ddFamily n seed)).length
          (((dedupAdj (ddFamily n seed)).length : Nat) : Int)
          ((n : Nat) : Int)
          (((dedupAdj (ddFamily n seed)).length : Nat) : Int)) 22) :=
    storeTarget_addr hlook4
      (by
        simp only [normalizeValueForTy, normalizeValueForTyFuel,
          typeResolutionFuel]
        rw [unorm_nat_of_lt (by omega :
          (dedupAdj (ddFamily n seed)).length < 2 ^ 64)]
        rfl)
  have hepi5 := epi5_rawD σ
    (dHeapEnd ((n : Nat) : Int) ((seed : Nat) : Int) n l'
      (ddPre n seed)
      (ddPost (ddFamily n seed) (dedupAdj (ddFamily n seed)).length)
      ((n : Nat) : Int) ((n : Nat) : Int)
      (dedupAdj (ddFamily n seed)).length
      (((dedupAdj (ddFamily n seed)).length : Nat) : Int)
      ((n : Nat) : Int)
      (((dedupAdj (ddFamily n seed)).length : Nat) : Int)) ch
  -- assemble
  have hall :=
    stepFnIter_chain
      (stepFnIter_chain
        (stepFnIter_chain
          (stepFnIter_chain
            (stepFnIter_chain
              (stepFnIter_chain
                (stepFnIter_chain
                  (stepFnIter_chain
                    (stepFnIter_chain
                      (stepFnIter_chain
                        (stepFnIter_chain
                          (stepFnIter_chain
                            (stepFnIter_chain
                              (stepFnIter_chain
                                (stepFnIter_chain
                                  (stepFnIter_chain
                                    (stepFnIter_chain
                                      (stepFnIter_chain
                                        (stepFnIter_chain
                                          (stepFnIter_chain
                                            (stepFnIter_chain
                                              (stepFnIter_chain
                                                (stepFnIter_chain
                                                  (stepFnIter_chain
                                                    (stepFnIter_chain
                                                      (stepFnIter_chain
                                                        (stepFnIter_chain
                                                          (stepFnIter_chain
                                                            (stepFnIter_chain
                                                              hE1 hmk)
                                                            hE2)
                                                          hsuA0)
                                                        hsuLoop)
                                                      hsuX)
                                                    hcpA0)
                                                  hcpLoop)
                                                hcpX)
                                              hent)
                                            hpro)
                                          hsjA0)
                                        hsjLen)
                                      hsjCmp)
                                    hsjLoop)
                                  hsjX1)
                                hslice)
                              hsjX2)
                            hpoA0)
                          hpoLen)
                        hpoCmp)
                      hpoLoop)
                    hepi1)
                  (stepFnIter_one (stepFn_store_step hst2)))
                hepi2)
              (stepFnIter_one (stepFn_store_step hst3)))
            hepi3)
          hepiLen)
        hconv)
      (stepFnIter_chain
        (stepFnIter_chain hepi4
          (stepFnIter_one (stepFn_store_step hst4)))
        hepi5)
  refine ⟨_, l', ?_, hall⟩
  have h1 : 55 * (dedupAdj (ddFamily n seed)).length ≤ 55 * n :=
    Nat.mul_le_mul_left 55 hkkn
  omega

/-! ## The user-facing statements -/

/-- **THE HEADLINE (§11 harness form, S3 RELATIONAL)**: for every
`n ≤ 8` and every `seed < 2⁶⁴`, running the Go harness
`dedup_harness_r(n, seed)` through the machine's native function
entry — empty-heap state, both arguments at the call boundary —
completes normally past one fuel bound, at every
nondeterminism-choice stream, and returns THREE values: a length-`n`
value list `vals` as the fixed-cap array the Go returns, its
ADJACENT-only deduplication `dedupAdj vals` zero-padded to the same
cap, and the number of survivors. The postcondition is a relation over
the RETURNED data — `post = dedupAdj pre`, `k = (dedupAdj pre).length`
— with no family function inside the claim.

Honesty clauses, all recorded rather than hidden:

* **ADJACENT-only is the claim's headline point.** `dedupAdj` keeps an
  element iff it is FIRST or differs from the last KEPT one — so only
  runs of equal NEIGHBOURS collapse, and `1,2,1,2` maps to itself.
  That is the mathematics of the Go subject (the classic misreading is
  "removes all duplicates"); the corpus row `four-alternating` pins it
  differentially, and `dedupAdj` is a recursion over `List Int`, never
  a restatement of the two-pointer loop. The machine bridge is the
  in-place invariant of the module docstring, proved in `sj_loopD`.
* **`∃ vals` is family-determined.** The witness is
  `ddFamily n seed` — `vals[i] = seed + i/2` wrapped at uint64, so
  ADJACENT PAIRS REPEAT and both branches of the subject run on every
  `n ≥ 3`. The statement merely avoids SAYING so; making the input
  genuine ∀-data needs the ghost rung-1 annotation, which is designed
  and not built.
* **The cap `n ≤ 8` is a toy bound.** Go's pass-by-value fragment
  cannot return unbounded data, so the harness returns
  `[dedupCapN]uint64` with `dedupCapN = 8` (visible in the corpus Go)
  and the copy loops plus zero-padding exist ONLY so the data can
  cross the observation boundary.
* **The wrap is part of the family.** `seed + i/2` wraps at `2⁶⁴` BY
  DESIGN (`% 2⁶⁴` in `ddFamily`), so wrap-boundary seeds are covered,
  not excluded.
* **`∀ ch` is vacuous here and stated anyway.** The subject consumes
  no nondeterminism choice; the quantifier records that rather than
  hiding a `Choices` argument.
* **The fuel bound `N = 263·n + 361` is a BOUND, not a measurement**
  — 263 charges every element the widest (keep, `k ≠ 0`) subject
  branch plus a full post-copy slot. The MEASURED step count is
  `361` at `n = 0` and `177·n + 86·K + 343` for `n ≥ 1`, where
  `K = (dedupAdj vals).length` = the survivor count (probe-verified at
  `n = 0, 1, 5, 8`: 361, 606, 1486, 2103 — for the family
  `K = ⌈n/2⌉`). Neither number is presented as the other.
* **Machine idealization** as in the other entries: entry from an
  empty heap, an unbounded heap, allocation always succeeds. -/
theorem dedup_ok (n seed : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64) :
    ∃ vals : List Int, vals.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel dedupLowered.typeDefs.toList
            dedupLowered.funcs dedupHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            dedupLowered.methods ch
          = .ok { values := #[ddArr8 vals, ddArr8 (dedupAdj vals),
              .int ((dedupAdj vals).length : Nat) .uint64] } := by
  refine ⟨ddFamily n seed, ddFamily_length n seed, 263 * n + 361,
    fun fuel hfuel ch => ?_⟩
  rw [dd_entry_eq (n : Int) (seed : Int) fuel ch,
    unorm_nat_of_lt (show n < 2 ^ 64 by omega), unorm_nat_of_lt hseed]
  obtain ⟨k, l', hk, hrun⟩ := dd_runs_generic ddProg n seed hcap
    (fun l lp siv civ => d_enterFrame_fact ((n : Nat) : Int)
      ((seed : Nat) : Int) n l lp siv civ) ch
  have hseed_eq : ddSeed ((n : Nat) : Int) ((seed : Nat) : Int)
      = dSt ddProg (dHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)) 5 := rfl
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [hseed_eq, hfold, runConfig_next_stop]
  show (Except.ok { values :=
      #[.array ⟨(ddPre n seed).map (fun v => .int v .uint64)⟩,
        .array ⟨(ddPost (ddFamily n seed)
            (dedupAdj (ddFamily n seed)).length).map
          (fun v => .int v .uint64)⟩,
        .int (((dedupAdj (ddFamily n seed)).length : Nat) : Int)
          .uint64] } : Except GoError Result) = _
  rw [ddArr8, ddArr8, ← ddPre_full, ← ddPost_full]

/-- **The D1 run-conditioned twin**: any successful completion of the
harness entry returns those three values — derived from `dedup_ok`
through the shared `harness_readout_of_total` bridge; nothing is
re-proven. -/
theorem dedup_readout (n seed : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) :
    ∃ vals : List Int, vals.length = n ∧
      ∀ (fuel : Nat) (ch : Choices) (r : Result),
        runFunctionWithContextM fuel dedupLowered.typeDefs.toList
            dedupLowered.funcs dedupHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            dedupLowered.methods ch
          = .ok r →
        r = { values := #[ddArr8 vals, ddArr8 (dedupAdj vals),
            .int ((dedupAdj vals).length : Nat) .uint64] } := by
  obtain ⟨vals, hlen, htot⟩ := dedup_ok n seed hcap hseed
  exact ⟨vals, hlen, harness_readout_of_total htot⟩

end GoLean.Examples.DedupAdjacent
