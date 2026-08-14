import GoLeanProofs.Examples.BinSearchProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Laws.StmtOps

/-!
# Verified example: binary search (verified-examples slice 2c, 2026-08-13)

The Go program is the canonical corpus source
`Corpus/coverage/exec/examples/binsearch/main.go` (differentially green
against `go run`, incl. the duplicates-lower-bound and int64-boundary
rows); `searchLowered` is its pinned frontend lowering
(`scripts/check-golden`).

The user-facing statement is `search_ok` (harness form, ruling
2026-08-13 — `docs/2026-08-12_example-spec-form.md` §11): the fixed
three-phase Go harness `search_harness(n, seed, t)` — setup
materializes the sorted family `s[i] = seed + 2*i`, the call under
test is `search(s, t)`, the returned index is the observable — stated
over the machine's native function entry `runFunctionWithContextM`,
termination + returned values only, quantified over the `GoValue`
arguments. No heap readback, no frame clause is user-facing.

The memory-quantified form (`search_framed`: ∀ sorted `xs`, wherever
the input lives, with anything else present, result + backing +
frame-preservation clauses) remains below as the PROOF-SIDE supporting
layer per §11 — it carries the ∀xs claim the scalar-parameterized
harness family is honestly weaker than.

**The `2^62` domain bound is the example's teaching point** (Bloch
2006, "Nearly all binary searches ... are broken"): the subject
computes `mid := (lo + hi) / 2`, and Go evaluates `lo + hi` in `int`.
At lengths at or beyond `2^62` the sum `lo + hi` can reach `2^63` and
WRAP NEGATIVE, so the classic midpoint overflow bug is REAL in this
program; below `2^62` we prove `lo + hi < 2^63` throughout (from
`lo ≤ hi ≤ len`), so Go's own arithmetic never wraps. The bound is the
program's honest domain, not a proof-method limit. (Boundary note,
verified while proving: the midpoint is computed only under the loop's
strict `lo < hi`, so `lo + hi ≤ 2·len − 1` — the first length at which
the sum can reach `2^63` is therefore `2^62 + 1`, and `len = 2^62`
itself would still be safe; the stated `< 2^62` domain is the clean
power-of-two bound sitting one step inside the exact boundary.)

**The short-circuit `&&` is the second teaching point**: the post-loop
guard `lo < len(s) && s[lo] == target` lowers to `Expr.and`, whose
machine shape (probed) is lazy — the left operand delivers into an
`andK` frame, and a `false` left result returns `.bool false` WITHOUT
evaluating the right operand. When `lo = len(s)` the read `s[lo]` —
which would be out of bounds — never happens; the proof's exit path
walks exactly that laziness.

Proof route (the reverse exemplar's): direct machine-step segments
(`with_unfolding_all rfl` between data-dependent branch points), one
strong induction on the interval width `hi - lo` carrying BOTH the
value half (the invariant pins `findSpec`) and the completion half
(explicit fuel bound `123 + 75·len`), then the executable frame
theorem transfers the canonical run to every admissible framed
placement through an input-RELOCATING renaming. A per-iteration
novelty vs reverse: the loop body DECLARES `mid` each pass, so every
iteration allocates a fresh cell at a SYMBOLIC address — the loop
states carry an abstract garbage suffix `g` (dead `mid` cells) with a
freshness invariant, and the four `mid`-cell touches per iteration
(alloc, store, two loads) are conditioned single-step lemmas between
the `rfl` segments.

Statement deltas vs the design block: none — the statement proved is
the one specified (the `2^62` bound and both `hf0`/`hfb` disjointness
hypotheses were in the spec).

Scope honesty (charter): usability evidence for the reasoning layer —
never machine-hardening evidence.
-/

namespace GoLean.Examples.BinSearch

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-! ## The mathematical reference -/

/-- **The specification function**: index of the FIRST occurrence of
`t` in `xs`, or `-1` — defined the way a functional programmer would
write it, by structural recursion on the list. The theorems below say
the Go program computes THIS function. -/
def findSpec (xs : List Int) (t : Int) : Int :=
  match xs with
  | [] => -1
  | v :: rest =>
      if v = t then 0
      else if findSpec rest t < 0 then -1 else findSpec rest t + 1

/-- On a hit, `findSpec` is the first index holding `t`. -/
private theorem findSpec_eq_first : ∀ (xs : List Int) (t : Int) (L : Nat),
    L < xs.length → xs.getD L 0 = t → (∀ k, k < L → xs.getD k 0 ≠ t) →
    findSpec xs t = L
  | [], _, L, hL, _, _ => absurd hL (by simp)
  | v :: rest, t, 0, _, hget, _ => by
      simp only [List.getD_cons_zero] at hget
      simp [findSpec, hget]
  | v :: rest, t, L + 1, hL, hget, hbef => by
      have hv : v ≠ t := by
        have h0 := hbef 0 (by omega)
        simpa using h0
      have hrest : findSpec rest t = (L : Int) :=
        findSpec_eq_first rest t L (by simpa using hL)
          (by simpa using hget)
          (fun k hk => by
            have hk1 := hbef (k + 1) (by omega)
            simpa using hk1)
      simp only [findSpec, if_neg hv, hrest]
      rw [if_neg (by omega)]
      omega

/-- On a total miss, `findSpec` is `-1`. -/
private theorem findSpec_eq_neg : ∀ (xs : List Int) (t : Int),
    (∀ k, k < xs.length → xs.getD k 0 ≠ t) → findSpec xs t = -1
  | [], _, _ => rfl
  | v :: rest, t, hall => by
      have hv : v ≠ t := by
        have h0 := hall 0 (by simp)
        simpa using h0
      have hrest : findSpec rest t = -1 :=
        findSpec_eq_neg rest t (fun k hk => by
          have hk1 := hall (k + 1) (by simpa using hk)
          simpa using hk1)
      simp [findSpec, if_neg hv, hrest]

/-! ### The three exit-shape consumers (the loop invariant at `lo = hi`
determines `findSpec`) -/

/-- Found: `s[L] = t` with everything below strictly smaller. -/
private theorem findSpec_found {xs : List Int} {t : Int} {L : Nat}
    (hL : L < xs.length) (hget : xs.getD L 0 = t)
    (hlow : ∀ k, k < L → xs.getD k 0 < t) :
    findSpec xs t = L :=
  findSpec_eq_first xs t L hL hget
    (fun k hk => by have := hlow k hk; omega)

/-- Miss at the right end: every element is below `t`. -/
private theorem findSpec_miss_end {xs : List Int} {t : Int}
    (hlow : ∀ k, k < xs.length → xs.getD k 0 < t) :
    findSpec xs t = -1 :=
  findSpec_eq_neg xs t (fun k hk => by have := hlow k hk; omega)

/-- Miss in bounds: `t ≤ s[L] ≠ t`, everything below strictly smaller,
everything at or above `L` at least `t` — sortedness pushes the strict
gap at `L` up through the tail. -/
private theorem findSpec_miss_inbounds {xs : List Int} {t : Int} {L : Nat}
    (hs : Sorted xs) (hL : L < xs.length) (hne : xs.getD L 0 ≠ t)
    (hlow : ∀ k, k < L → xs.getD k 0 < t)
    (hhigh : ∀ k, L ≤ k → k < xs.length → t ≤ xs.getD k 0) :
    findSpec xs t = -1 := by
  have hLt : t < xs.getD L 0 := by
    have := hhigh L (Nat.le_refl _) hL
    omega
  refine findSpec_eq_neg xs t (fun k hk => ?_)
  rcases Nat.lt_or_ge k L with hkL | hkL
  · have := hlow k hkL
    omega
  · rcases Nat.eq_or_lt_of_le hkL with rfl | hkL'
    · exact hne
    · have hmono := hs L k hkL' hk
      omega

/-! ### The invariant-maintenance steps (sortedness at the probe) -/

/-- `s[mid] < t` pushes the lower frontier past `mid`. -/
private theorem inv_lo_step {xs : List Int} {t : Int} {mid : Nat}
    (hs : Sorted xs) (hmid : xs.getD mid 0 < t) (hmlen : mid < xs.length) :
    ∀ k, k < mid + 1 → xs.getD k 0 < t := by
  intro k hk
  rcases Nat.lt_or_ge k mid with hkm | hkm
  · have := hs k mid hkm hmlen
    omega
  · have : k = mid := by omega
    subst this
    exact hmid

/-- `t ≤ s[mid]` pulls the upper frontier down to `mid`. -/
private theorem inv_hi_step {xs : List Int} {t : Int} {mid : Nat}
    (hs : Sorted xs) (hmid : t ≤ xs.getD mid 0) :
    ∀ k, mid ≤ k → k < xs.length → t ≤ xs.getD k 0 := by
  intro k hkm hk
  rcases Nat.eq_or_lt_of_le hkm with rfl | hkm'
  · exact hmid
  · have := hs mid k hkm' hk
    omega

/-! ## Machine-integer cleaning: the midpoint arithmetic

`mid := (lo + hi) / 2` computes, on the machine, a truncated `Int`
division of the (normalized) `int` sum by the literal `2`. Below the
`2^62` length bound the sum stays below `2^63`, every normalization is
the identity, and the truncated division of nonnegatives is `Nat`
division — this lemma is the WHOLE overflow story. -/

private theorem tdiv_nat (a b : Nat) :
    Int.tdiv ((a : Nat) : Int) ((b : Nat) : Int) = ((a / b : Nat) : Int) :=
  rfl

private theorem mid_clean {lo hi : Nat} (h : lo + hi < 2 ^ 63) :
    IntKind.normalize .int
        (Int.tdiv (IntKind.normalize .int ((lo : Int) + (hi : Int))) 2)
      = (((lo + hi) / 2 : Nat) : Int) := by
  have hsum : (lo : Int) + (hi : Int) = ((lo + hi : Nat) : Int) := by omega
  rw [hsum, inorm_nat_of_lt h,
    show (2 : Int) = ((2 : Nat) : Int) from rfl, tdiv_nat,
    inorm_nat_of_lt (by omega)]

/-! ## The program-side statement vocabulary -/

/-- The caller environment: the harness result cell the differential
runner also reads. -/
def searchEnv : LocalEnv := [[("$callres", .base ⟨0⟩)]]

/-- The result cell: a zeroed Go `int`. -/
def resCell : Heap := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)]

/-- The driver: `$callres = search(s, target)` with the slice handle
over the backing array at `base` and the target as literal arguments —
the argument-as-quantifier convention on a memory-backed value plus a
scalar. -/
def searchCall (xs : List Int) (base : Nat) (t : Int) : Stmt :=
  .call #[.var "$callres"] ⟨"search"⟩
    #[.slice (.locLit (.base ⟨base⟩)) (.intLit 0 .int)
        (.intLit xs.length .int) none,
      .intLit t .uint64]

/-- The framed seed: result cell, input backing cell at `base`, an
arbitrary frame `fr`, allocator at `na`. The canonical placement is
`searchSeed xs 1 [] 2` — TIGHT (dom = {0, 1}, na₀ = 2). -/
def searchSeed (xs : List Int) (base : Nat) (fr : Heap) (na : Nat) :
    ExecState :=
  { types := searchLowered.typeDefs.toList,
    functions := searchLowered.funcs,
    methods := searchLowered.methods,
    heap := resCell ++ sliceCells xs base ++ fr, nextAddr := na }

/-! ### The lowering, transcribed (pinned by `rfl` below) -/

/-- `mid := (lo + hi) / 2`. -/
abbrev midAssign : Stmt :=
  .assign (.var "mid")
    (.div (.add (.var "lo") (.var "hi")) (.intLit 2 .int))

/-- The probe dispatch: `if s[mid] < target { lo = mid + 1 } else { hi = mid }`. -/
abbrev innerIf : Stmt :=
  .ifThenElse
    (.lessCmp (.indexGet (.var "s") (.var "mid")) (.var "target"))
    (.block #[]
      #[.seqn #[.assign (.var "lo")
          (.add (.var "mid") (.intLit 1 .int))]])
    (.block #[]
      #[.seqn #[.assign (.var "hi") (.var "mid")]])

/-- The loop-tail block: declare-and-set `mid`, then the probe. The
`initialization` HERE is what makes each iteration allocate. -/
abbrev midBlock : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "mid", typ := .int .int }, midAssign],
      innerIf]

/-- The frontend's `for`-desugar body (no post statement — the
dispatch's else branch is the empty `.seqn #[]`). -/
abbrev searchWhileBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.seqn #[]),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "lo") (.var "hi"))
        (.seqn #[])
        .breakStmt,
      midBlock]

/-- The post-loop guard: Go's SHORT-CIRCUIT `&&` (`Expr.and`) — the
machine must not read `s[lo]` when `lo = len(s)`. -/
abbrev postIf : Stmt :=
  .ifThenElse
    (.and
      (.lessCmp (.var "lo")
        (.length (.var "s") (some (.slice (.int .uint64)))))
      (.eqCmp (.int .uint64)
        (.indexGet (.var "s") (.var "lo"))
        (.var "target")))
    (.block #[]
      #[.seqn #[.assign (.var "$res0") (.var "lo"), .returnStmt]])
    (.seqn #[])

/-- The fallthrough: `return -1`. -/
abbrev tailSeqn : Stmt :=
  .seqn #[.assign (.var "$res0") (.intLit (-1) .int), .returnStmt]

/-- The subject's `Func` record, verbatim from the pinned lowering (the
`example` pin below ties it by `rfl`). -/
def searchFunc : Func :=
  { id := { key := "search" },
    args := #[{ id := "s", typ := .slice (.int .uint64) },
              { id := "target", typ := .int .uint64 }],
    results := #[{ id := "$res0", typ := .int .int }],
    body := .block
      #[]
      #[.seqn
          #[.initialization { id := "lo", typ := .int .int },
            .initialization { id := "hi", typ := .int .int },
            .assignMany
              #[.var "lo", .var "hi"]
              #[.intLit 0 .int,
                .length (.var "s") (some (.slice (.int .uint64)))]],
        .block
          #[]
          #[.initialization { id := "$forFirst", typ := .bool },
            .assign (.var "$forFirst") (.boolLit true),
            .while (.boolLit true) searchWhileBody],
        postIf,
        tailSeqn],
    variadic := false,
    wrapper := false }

/-- The lowering pin: the proof subject IS the frontend's lowering. -/
example : findFunctionIn? searchLowered.funcs ⟨"search"⟩ = some searchFunc :=
  rfl

/-! ## The machine layer: canonical-placement configurations

Transcribed from the machine (probe-verified against concrete runs;
every raw segment below re-checks the transcription by `rfl`).
Address layout at the canonical placement: 0 = the result cell,
1 = the backing array, 2 = the parameter `s` (the handle),
3 = `target`, 4 = `$res0`, 5 = `lo`, 6 = `hi`, 7 = `$forFirst`;
the loop is entered with the allocator at 8, and each iteration
allocates one dead `mid` cell (8, 9, …) — the garbage suffix `g`. -/

private abbrev icell (v : Int) : HeapCell := ⟨some (.int .int), .int v .int⟩
private abbrev ucell (v : Int) : HeapCell :=
  ⟨some (.int .uint64), .int v .uint64⟩
private abbrev bcell (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
private abbrev arrCell (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n (.int .uint64)), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
private abbrev handleCell (n : Nat) : HeapCell :=
  ⟨some (.slice (.int .uint64)), .slice ⟨some (.base ⟨1⟩), 0, n, n⟩⟩
private abbrev sliceH (n : Nat) : GoValue :=
  .slice ⟨some (.base ⟨1⟩), 0, n, n⟩

private def envArgs : LocalEnv :=
  [[("$res0", .base ⟨4⟩), ("target", .base ⟨3⟩), ("s", .base ⟨2⟩)]]
private def envMid2 : LocalEnv :=
  [("hi", .base ⟨6⟩), ("lo", .base ⟨5⟩)] :: envArgs
private def envIn : LocalEnv := [("$forFirst", .base ⟨7⟩)] :: envMid2

private def frameK : Cont :=
  .frame [(.chain [], [.ref "$callres"])] searchEnv [.base ⟨4⟩] [] .stop false
private def headTail : Cont :=
  .seq [] envIn (.seq [postIf, tailSeqn] envMid2 frameK)
/-- The loop-head configuration. -/
private def headCfg : Config :=
  .exec (.while (.boolLit true) searchWhileBody) envIn headTail
private def loopK : Cont :=
  .loop (.boolLit true) searchWhileBody envIn headTail
/-- The exit test's delivery continuation (segment split point). -/
private def cmpCont : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envIn)
    (.seq [midBlock] ([] :: envIn) loopK)
private def envIter : LocalEnv := [] :: [] :: envIn
private def envMidd (na : Nat) : LocalEnv :=
  [("mid", .base ⟨na⟩)] :: [] :: envIn
private def iterK : Cont := .seq [] ([] :: envIn) loopK

/-- The loop-state family: the eight canonical cells (result `r0`,
backing, handle, target, `$res0` = `res`, `lo`, `hi`, `$forFirst`)
plus the dead-`mid`-cell garbage suffix `g`, allocator at `na`. -/
private def sP (n : Nat) (xs : List Int) (t r0 res lo hi : Int) (ff : Bool)
    (g : Heap) (na : Nat) : ExecState :=
  { types := searchLowered.typeDefs.toList,
    functions := searchLowered.funcs,
    methods := searchLowered.methods,
    heap := (.base ⟨0⟩, icell r0) :: (.base ⟨1⟩, arrCell n xs)
      :: (.base ⟨2⟩, handleCell n) :: (.base ⟨3⟩, ucell t)
      :: (.base ⟨4⟩, icell res) :: (.base ⟨5⟩, icell lo)
      :: (.base ⟨6⟩, icell hi) :: (.base ⟨7⟩, bcell ff) :: g,
    nextAddr := na }

/-! ## Heap plumbing (the garbage suffix's algebra) -/

private theorem lookup_append_of_none {p q : Heap} {l : Loc}
    (h : Heap.lookup p l = none) :
    Heap.lookup (p ++ q) l = Heap.lookup q l := by
  induction p with
  | nil => rfl
  | cons e rest ih =>
      obtain ⟨k, c⟩ := e
      simp only [Heap.lookup, List.cons_append] at h ⊢
      by_cases hk : (k == l) = true
      · rw [if_pos hk] at h
        cases h
      · rw [if_neg hk] at h ⊢
        exact ih h

private theorem set_append_of_none {p q : Heap} {l : Loc} {c : HeapCell}
    (h : Heap.lookup p l = none) :
    Heap.set (p ++ q) l c = p ++ Heap.set q l c := by
  induction p with
  | nil => rfl
  | cons e rest ih =>
      obtain ⟨k, c₀⟩ := e
      simp only [Heap.lookup] at h
      by_cases hk : (k == l) = true
      · rw [if_pos hk] at h
        cases h
      · rw [if_neg hk] at h
        simp only [List.cons_append, Heap.set, if_neg hk, ih h]

/-- Lookups above the canonical prefix fall through to the garbage. -/
private theorem lookup_sP_high {n : Nat} {xs : List Int}
    {t r0 res lo hi : Int} {ff : Bool} {g : Heap} {na a : Nat}
    (ha : 8 ≤ a) :
    Heap.lookup (sP n xs t r0 res lo hi ff g na).heap (.base ⟨a⟩)
      = Heap.lookup g (.base ⟨a⟩) := by
  simp only [sP, Heap.lookup,
    base_beq_false (show (0 : Nat) ≠ a by omega),
    base_beq_false (show (1 : Nat) ≠ a by omega),
    base_beq_false (show (2 : Nat) ≠ a by omega),
    base_beq_false (show (3 : Nat) ≠ a by omega),
    base_beq_false (show (4 : Nat) ≠ a by omega),
    base_beq_false (show (5 : Nat) ≠ a by omega),
    base_beq_false (show (6 : Nat) ≠ a by omega),
    base_beq_false (show (7 : Nat) ≠ a by omega),
    Bool.false_eq_true, if_false]

/-- Setting a cell above the canonical prefix rewrites only the
garbage. -/
private theorem set_sP_high {n : Nat} {xs : List Int}
    {t r0 res lo hi : Int} {ff : Bool} {g : Heap} {na a : Nat}
    (ha : 8 ≤ a) (c : HeapCell) :
    Heap.set (sP n xs t r0 res lo hi ff g na).heap (.base ⟨a⟩) c
      = (sP n xs t r0 res lo hi ff (Heap.set g (.base ⟨a⟩) c) na).heap := by
  simp only [sP, Heap.set,
    base_beq_false (show (0 : Nat) ≠ a by omega),
    base_beq_false (show (1 : Nat) ≠ a by omega),
    base_beq_false (show (2 : Nat) ≠ a by omega),
    base_beq_false (show (3 : Nat) ≠ a by omega),
    base_beq_false (show (4 : Nat) ≠ a by omega),
    base_beq_false (show (5 : Nat) ≠ a by omega),
    base_beq_false (show (6 : Nat) ≠ a by omega),
    base_beq_false (show (7 : Nat) ≠ a by omega),
    Bool.false_eq_true, if_false]

/-- The backing-cell lookup (any loop state). -/
private theorem lookup_sP_backing {n : Nat} {xs : List Int}
    {t r0 res lo hi : Int} {ff : Bool} {g : Heap} {na : Nat} :
    Heap.lookup (sP n xs t r0 res lo hi ff g na).heap (.base ⟨1⟩)
      = some (arrCell n xs) := by
  simp [sP, Heap.lookup]

/-- The result-cell lookup (any loop state). -/
private theorem lookup_sP_res {n : Nat} {xs : List Int}
    {t r0 res lo hi : Int} {ff : Bool} {g : Heap} {na : Nat} :
    Heap.lookup (sP n xs t r0 res lo hi ff g na).heap (.base ⟨0⟩)
      = some (icell r0) := by
  simp [sP, Heap.lookup]

/-- The base-address int store fact (the `mid` cell's store — replayed
by `storeTarget` through the trivial chain, normalized at the cell's
declared `int` type). -/
private theorem storeTarget_base_int {σ : ExecState} {A : Addr}
    {w : GoValue} {ik : IntKind} (m : Int)
    (hlook : Heap.lookup σ.heap (.base A) = some ⟨some (.int .int), w⟩) :
    storeTarget σ (.chain (.addr (.base A)) [] []) (.int m ik)
      = .ok { σ with
          heap := Heap.set σ.heap (.base A)
            ⟨some (.int .int), .int (IntKind.normalize .int m) .int⟩ } := by
  simp only [storeTarget, resolveChain, valueAsLoc, pure, Except.pure,
    Bind.bind, Except.bind, storeLoc, hlook]
  simp only [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel]
  rfl

/-- The `mid` declaration's allocation step (concrete configuration,
symbolic state): the fresh cell goes in at `.base ⟨nextAddr⟩` — in
`Heap.set` form here; the caller rewrites with `set_fresh`. -/
private theorem stepFn_init_mid (σ : ExecState) (ch : Choices) :
    stepFn σ (.exec (.initialization { id := "mid", typ := .int .int })
        envIter (.seq [midAssign, innerIf] envIter iterK)) ch
      = .ok (.next (.seq [midAssign, innerIf]
            (envMidd σ.nextAddr) iterK),
          { σ with
            heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
              ⟨some (.int .int), .int 0 .int⟩,
            nextAddr := σ.nextAddr + 1 }, ch) := by
  with_unfolding_all rfl

/-! ## Raw run segments (`with_unfolding_all rfl` — pure definitional
evaluation with the data symbolic; the segments split exactly at the
data-dependent points: the strict applies on heap data, the `mid`-cell
touches, the branch deliveries). -/

/-- Later-pass dispatch (the flag is down; the else branch is the empty
`.seqn #[]` — no post statement): head → the exit-test delivery. -/
private theorem seg_dispatch1_raw (n : Nat) (xs : List Int)
    (t lo hi : Int) (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 18 (sP n xs t 0 0 lo hi false g na) headCfg ch
      = .ok (.retV (.bool (decide (lo < hi))) cmpCont,
          sP n xs t 0 0 lo hi false g na, ch) := by
  with_unfolding_all rfl

/-- First-pass dispatch: the flag drops, then the exit test. -/
private theorem seg_dispatch0_raw (n : Nat) (xs : List Int)
    (t lo hi : Int) (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 25 (sP n xs t 0 0 lo hi true g na) headCfg ch
      = .ok (.retV (.bool (decide (lo < hi))) cmpCont,
          sP n xs t 0 0 lo hi false g na, ch) := by
  with_unfolding_all rfl

/-! ### Entry segments (canonical placement: base = 1, fr = [], na = 2) -/

private def entryCallK (t : Int) : Cont :=
  .callArgsK ⟨"search"⟩ [(.chain [], [.ref "$callres"])] []
    [.intLit t .uint64] searchEnv .stop

/-- Entry A: driver start → the slice-expression apply point. -/
private theorem seg_entryA_raw (xs : List Int) (t : Int) (ch : Choices) :
    stepFnIter 7 (searchSeed xs 1 [] 2)
      (.exec (searchCall xs 1 t) searchEnv .stop) ch
      = .ok (.retV (.int (IntKind.normalize .int (xs.length : Int)) .int)
            (.strictK (.sliceExpr false) [.int 0 .int, .addr (.base ⟨1⟩)]
              [] searchEnv (entryCallK t)),
          searchSeed xs 1 [] 2, ch) := by
  with_unfolding_all rfl

/-- Entry B: the handle delivered → the target-literal delivery. -/
private theorem seg_entryB_raw (xs : List Int) (t : Int) (ch : Choices) :
    stepFnIter 2 (searchSeed xs 1 [] 2)
      (.retV (sliceH xs.length) (entryCallK t)) ch
      = .ok (.retV (.int (IntKind.normalize .uint64 t) .uint64)
            (.callArgsK ⟨"search"⟩ [(.chain [], [.ref "$callres"])]
              [sliceH xs.length] [] searchEnv .stop),
          searchSeed xs 1 [] 2, ch) := by
  with_unfolding_all rfl

private def ffBlock : Stmt :=
  .block #[]
    #[.initialization { id := "$forFirst", typ := .bool },
      .assign (.var "$forFirst") (.boolLit true),
      .while (.boolLit true) searchWhileBody]

private def entryTail : Cont :=
  .seq [ffBlock, postIf, tailSeqn] envMid2 frameK
private def entryRhsK : Cont :=
  .rhsK .vals
    [.chain (.addr (.base ⟨5⟩)) [] [], .chain (.addr (.base ⟨6⟩)) [] []]
    [.int 0 .int] [] (.seqn #[]) envMid2 entryTail

/-- The mid-entry state: frame entered (`s`/`target`/`$res0`
allocated), `lo`/`hi` at defaults; the stored target still carries its
frame-entry normalization. -/
private def σEntry (xs : List Int) (tq : Int) : ExecState :=
  { types := searchLowered.typeDefs.toList,
    functions := searchLowered.funcs,
    methods := searchLowered.methods,
    heap := [(.base ⟨0⟩, icell 0), (.base ⟨1⟩, arrCell xs.length xs),
             (.base ⟨2⟩, handleCell xs.length), (.base ⟨3⟩, ucell tq),
             (.base ⟨4⟩, icell 0), (.base ⟨5⟩, icell 0),
             (.base ⟨6⟩, icell 0)],
    nextAddr := 7 }

/-- Entry C: frame entry, `lo`/`hi` declaration, the `len(s)` operand
walk → the `lengthOf` apply point. -/
private theorem seg_entryC_raw (xs : List Int) (tv : Int) (ch : Choices) :
    stepFnIter 18 (searchSeed xs 1 [] 2)
      (.retV (.int tv .uint64)
        (.callArgsK ⟨"search"⟩ [(.chain [], [.ref "$callres"])]
          [sliceH xs.length] [] searchEnv .stop)) ch
      = .ok (.retV (sliceH xs.length)
            (.strictK (.lengthOf (some (.slice (.int .uint64)))) [] []
              envMid2 entryRhsK),
          σEntry xs (IntKind.normalize .uint64 tv), ch) := by
  with_unfolding_all rfl

/-- Entry D: `lo, hi = 0, len(s)` stores, the `$forFirst` block → the
loop head. -/
private theorem seg_entryD_raw (xs : List Int) (tq hv : Int) (ch : Choices) :
    stepFnIter 19 (σEntry xs tq) (.retV (.int hv .int) entryRhsK) ch
      = .ok (headCfg,
          sP xs.length xs tq 0 0 0 (IntKind.normalize .int hv) true [] 8,
          ch) := by
  with_unfolding_all rfl

/-! ### Iteration segments -/

/-- Test true → the `mid` declaration (the per-iteration allocation
point). -/
private theorem seg_iter1_raw (n : Nat) (xs : List Int) (t lo hi : Int)
    (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 7 (sP n xs t 0 0 lo hi false g na)
      (.retV (.bool true) cmpCont) ch
      = .ok (.exec (.initialization { id := "mid", typ := .int .int })
            envIter (.seq [midAssign, innerIf] envIter iterK),
          sP n xs t 0 0 lo hi false g na, ch) := by
  with_unfolding_all rfl

/-- The `mid` allocation, cleaned: the fresh cell APPENDS to the
garbage suffix (the freshness invariant is what makes the append
form provable). -/
private theorem step_alloc_mid (n : Nat) (xs : List Int) (t lo hi : Int)
    (g : Heap) (na : Nat) (ch : Choices) (hna : 8 ≤ na)
    (hg : Heap.lookup g (.base ⟨na⟩) = none) :
    stepFnIter 1 (sP n xs t 0 0 lo hi false g na)
      (.exec (.initialization { id := "mid", typ := .int .int })
        envIter (.seq [midAssign, innerIf] envIter iterK)) ch
      = .ok (.next (.seq [midAssign, innerIf] (envMidd na) iterK),
          sP n xs t 0 0 lo hi false (g ++ [(.base ⟨na⟩, icell 0)])
            (na + 1), ch) := by
  have h := stepFn_init_mid (sP n xs t 0 0 lo hi false g na) ch
  rw [show (sP n xs t 0 0 lo hi false g na).nextAddr = na from rfl,
    set_sP_high hna, set_fresh hg] at h
  exact stepFnIter_one h

/-- `mid = (lo + hi) / 2`: the target address, the sum, the truncated
division by the LITERAL 2 (its zero-check reduces away) → the store
point. -/
private theorem seg_iter2_raw (n : Nat) (xs : List Int) (t lo hi : Int)
    (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 14 (sP n xs t 0 0 lo hi false G na')
      (.next (.seq [midAssign, innerIf] (envMidd ma) iterK)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨ma⟩)) [] []]
            [.int (IntKind.normalize .int
                (Int.tdiv (IntKind.normalize .int (lo + hi)) 2)) .int]
            (.seqn #[]) (envMidd ma) (.seq [innerIf] (envMidd ma) iterK)),
          sP n xs t 0 0 lo hi false G na', ch) := by
  with_unfolding_all rfl

/-- The `mid` store, cleaned: lands in the appended cell, normalized at
the declared `int` type. -/
private theorem step_store_mid (n : Nat) (xs : List Int)
    (t lo hi w m : Int) (ik : IntKind) (g : Heap) (na' ma : Nat)
    (K : Cont) (ch : Choices) (hma : 8 ≤ ma)
    (hg : Heap.lookup g (.base ⟨ma⟩) = none) :
    stepFnIter 1
      (sP n xs t 0 0 lo hi false (g ++ [(.base ⟨ma⟩, icell w)]) na')
      (.next (.storeK [.chain (.addr (.base ⟨ma⟩)) [] []] [.int m ik]
        (.seqn #[]) (envMidd ma) K)) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envMidd ma) K),
          sP n xs t 0 0 lo hi false
            (g ++ [(.base ⟨ma⟩, icell (IntKind.normalize .int m))]) na',
          ch) := by
  have hlook : Heap.lookup
      (sP n xs t 0 0 lo hi false (g ++ [(.base ⟨ma⟩, icell w)]) na').heap
      (.base ⟨ma⟩) = some ⟨some (.int .int), .int w .int⟩ := by
    rw [lookup_sP_high hma, lookup_append_of_none hg, lookup_singleton_self]
  have hstore := storeTarget_base_int (σ := sP n xs t 0 0 lo hi false
    (g ++ [(.base ⟨ma⟩, icell w)]) na') (A := ⟨ma⟩) (ik := ik) m hlook
  rw [set_sP_high hma, set_append_of_none hg, set_singleton_self] at hstore
  exact stepFnIter_one (stepFn_store_step hstore)

private def thenBlk : Stmt :=
  .block #[] #[.seqn #[.assign (.var "lo")
    (.add (.var "mid") (.intLit 1 .int))]]
private def elseBlk : Stmt :=
  .block #[] #[.seqn #[.assign (.var "hi") (.var "mid")]]
/-- The continuation below the probe's `if`. -/
private def K1 (ma : Nat) : Cont := .seq [] (envMidd ma) iterK
/-- The probe dispatch's delivery continuation. -/
private def innerIfK (ma : Nat) : Cont :=
  .ifK thenBlk elseBlk (envMidd ma) (K1 ma)

/-- Store done → the empty-`seqn` splice point. -/
private theorem seg_iter3a_raw (n : Nat) (xs : List Int) (t lo hi : Int)
    (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 1 (sP n xs t 0 0 lo hi false G na')
      (.next (.storeK [] [] (.seqn #[]) (envMidd ma)
        (.seq [innerIf] (envMidd ma) iterK))) ch
      = .ok (.exec (.seqn #[]) (envMidd ma)
            (.seq [innerIf] (envMidd ma) iterK),
          sP n xs t 0 0 lo hi false G na', ch) := by
  with_unfolding_all rfl

/-- Spliced → the probe read's `mid` operand (`s[mid]`). -/
private theorem seg_iter3b_raw (n : Nat) (xs : List Int) (t lo hi : Int)
    (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 6 (sP n xs t 0 0 lo hi false G na')
      (.next (.seq [innerIf] (envMidd ma) iterK)) ch
      = .ok (.evalE (.var "mid") (envMidd ma)
            (.strictK .indexGet [sliceH n] [] (envMidd ma)
              (.strictK .lessCmp [] [.var "target"] (envMidd ma)
                (innerIfK ma))),
          sP n xs t 0 0 lo hi false G na', ch) := by
  with_unfolding_all rfl

/-- Store done → the probe read's `mid` operand, composed across the
splice. -/
private theorem seg_iter3 (n : Nat) (xs : List Int) (t lo hi : Int)
    (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 8 (sP n xs t 0 0 lo hi false G na')
      (.next (.storeK [] [] (.seqn #[]) (envMidd ma)
        (.seq [innerIf] (envMidd ma) iterK))) ch
      = .ok (.evalE (.var "mid") (envMidd ma)
            (.strictK .indexGet [sliceH n] [] (envMidd ma)
              (.strictK .lessCmp [] [.var "target"] (envMidd ma)
                (innerIfK ma))),
          sP n xs t 0 0 lo hi false G na', ch) :=
  stepFnIter_chain
    (stepFnIter_chain (seg_iter3a_raw n xs t lo hi G na' ma ch)
      (stepFnIter_one stepFn_seqn_splice))
    (seg_iter3b_raw n xs t lo hi G na' ma ch)

/-- A `mid` read, cleaned (both the index operand and the branch
operands read through the symbolic cell address). -/
private theorem step_load_mid (n : Nat) (xs : List Int)
    (t lo hi mv : Int) (g : Heap) (na' ma : Nat) (env : LocalEnv) (K : Cont)
    (ch : Choices) (hma : 8 ≤ ma)
    (hg : Heap.lookup g (.base ⟨ma⟩) = none)
    (henv : LocalEnv.lookup env "mid" = some (.base ⟨ma⟩)) :
    stepFnIter 1
      (sP n xs t 0 0 lo hi false (g ++ [(.base ⟨ma⟩, icell mv)]) na')
      (.evalE (.var "mid") env K) ch
      = .ok (.retV (.int mv .int) K,
          sP n xs t 0 0 lo hi false (g ++ [(.base ⟨ma⟩, icell mv)]) na',
          ch) := by
  have hlook : Heap.lookup
      (sP n xs t 0 0 lo hi false (g ++ [(.base ⟨ma⟩, icell mv)]) na').heap
      (.base ⟨ma⟩) = some (icell mv) := by
    rw [lookup_sP_high hma, lookup_append_of_none hg, lookup_singleton_self]
  exact stepFnIter_one (stepFn_var henv hlook)

/-- Element delivered → the probe comparison's delivery (`target` read,
`<` applied). -/
private theorem seg_iter4_raw (n : Nat) (xs : List Int) (t lo hi wv : Int)
    (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 3 (sP n xs t 0 0 lo hi false G na')
      (.retV (.int wv .uint64)
        (.strictK .lessCmp [] [.var "target"] (envMidd ma)
          (innerIfK ma))) ch
      = .ok (.retV (.bool (decide (wv < t))) (innerIfK ma),
          sP n xs t 0 0 lo hi false G na', ch) := by
  with_unfolding_all rfl

private def envPush (ma : Nat) : LocalEnv := [] :: envMidd ma
private def loRhsK (ma : Nat) : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] [] (.seqn #[])
    (envPush ma)
    (.seq [] (envPush ma) (.seq [] (envMidd ma) iterK))
private def hiRhsK (ma : Nat) : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨6⟩)) [] []] [] [] (.seqn #[])
    (envPush ma)
    (.seq [] (envPush ma) (.seq [] (envMidd ma) iterK))

/-- Probe true → the then-block's `seqn` splice point. -/
private theorem seg_iter5a1_raw (n : Nat) (xs : List Int) (t lo hi : Int)
    (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 3 (sP n xs t 0 0 lo hi false G na')
      (.retV (.bool true) (innerIfK ma)) ch
      = .ok (.exec (.seqn #[.assign (.var "lo")
              (.add (.var "mid") (.intLit 1 .int))]) (envPush ma)
            (.seq [] (envPush ma) (K1 ma)),
          sP n xs t 0 0 lo hi false G na', ch) := by
  with_unfolding_all rfl

/-- Spliced → `lo = mid + 1`'s `mid` operand. -/
private theorem seg_iter5a2_raw (n : Nat) (xs : List Int) (t lo hi : Int)
    (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 5 (sP n xs t 0 0 lo hi false G na')
      (.next (.seq [.assign (.var "lo")
        (.add (.var "mid") (.intLit 1 .int))] (envPush ma) (K1 ma))) ch
      = .ok (.evalE (.var "mid") (envPush ma)
            (.strictK .add [] [.intLit 1 .int] (envPush ma) (loRhsK ma)),
          sP n xs t 0 0 lo hi false G na', ch) := by
  with_unfolding_all rfl

/-- Probe true → `lo = mid + 1`'s `mid` operand, composed. -/
private theorem seg_iter5a (n : Nat) (xs : List Int) (t lo hi : Int)
    (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 9 (sP n xs t 0 0 lo hi false G na')
      (.retV (.bool true) (innerIfK ma)) ch
      = .ok (.evalE (.var "mid") (envPush ma)
            (.strictK .add [] [.intLit 1 .int] (envPush ma) (loRhsK ma)),
          sP n xs t 0 0 lo hi false G na', ch) :=
  stepFnIter_chain
    (stepFnIter_chain (seg_iter5a1_raw n xs t lo hi G na' ma ch)
      (stepFnIter_one stepFn_seqn_splice))
    (seg_iter5a2_raw n xs t lo hi G na' ma ch)

/-- `mid` delivered → `+ 1`, the `lo` store → the then-block's closing
splice point. -/
private theorem seg_iter6a1_raw (n : Nat) (xs : List Int) (t lo hi mv : Int)
    (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 6 (sP n xs t 0 0 lo hi false G na')
      (.retV (.int mv .int)
        (.strictK .add [] [.intLit 1 .int] (envPush ma) (loRhsK ma))) ch
      = .ok (.exec (.seqn #[]) (envPush ma) (.seq [] (envPush ma) (K1 ma)),
          sP n xs t 0 0
            (IntKind.normalize .int (IntKind.normalize .int (mv + 1))) hi
            false G na', ch) := by
  with_unfolding_all rfl

/-- Scope exits → the loop head (shared by both branches). -/
private theorem seg_iter_tail_raw (n : Nat) (xs : List Int) (t lo hi : Int)
    (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 4 (sP n xs t 0 0 lo hi false G na')
      (.next (.seq [] (envPush ma) (K1 ma))) ch
      = .ok (headCfg, sP n xs t 0 0 lo hi false G na', ch) := by
  with_unfolding_all rfl

/-- `mid` delivered → `+ 1`, the `lo` store, scope exits → the loop
head, composed. -/
private theorem seg_iter6a (n : Nat) (xs : List Int) (t lo hi mv : Int)
    (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 11 (sP n xs t 0 0 lo hi false G na')
      (.retV (.int mv .int)
        (.strictK .add [] [.intLit 1 .int] (envPush ma) (loRhsK ma))) ch
      = .ok (headCfg,
          sP n xs t 0 0
            (IntKind.normalize .int (IntKind.normalize .int (mv + 1))) hi
            false G na', ch) :=
  stepFnIter_chain
    (stepFnIter_chain (seg_iter6a1_raw n xs t lo hi mv G na' ma ch)
      (stepFnIter_one stepFn_seqn_splice))
    (seg_iter_tail_raw n xs t
      (IntKind.normalize .int (IntKind.normalize .int (mv + 1))) hi
      G na' ma ch)

/-- Probe false → the else-block's `seqn` splice point. -/
private theorem seg_iter5b1_raw (n : Nat) (xs : List Int) (t lo hi : Int)
    (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 3 (sP n xs t 0 0 lo hi false G na')
      (.retV (.bool false) (innerIfK ma)) ch
      = .ok (.exec (.seqn #[.assign (.var "hi") (.var "mid")]) (envPush ma)
            (.seq [] (envPush ma) (K1 ma)),
          sP n xs t 0 0 lo hi false G na', ch) := by
  with_unfolding_all rfl

/-- Spliced → `hi = mid`'s `mid` operand. -/
private theorem seg_iter5b2_raw (n : Nat) (xs : List Int) (t lo hi : Int)
    (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 4 (sP n xs t 0 0 lo hi false G na')
      (.next (.seq [.assign (.var "hi") (.var "mid")] (envPush ma)
        (K1 ma))) ch
      = .ok (.evalE (.var "mid") (envPush ma) (hiRhsK ma),
          sP n xs t 0 0 lo hi false G na', ch) := by
  with_unfolding_all rfl

/-- Probe false → `hi = mid`'s `mid` operand, composed. -/
private theorem seg_iter5b (n : Nat) (xs : List Int) (t lo hi : Int)
    (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 8 (sP n xs t 0 0 lo hi false G na')
      (.retV (.bool false) (innerIfK ma)) ch
      = .ok (.evalE (.var "mid") (envPush ma) (hiRhsK ma),
          sP n xs t 0 0 lo hi false G na', ch) :=
  stepFnIter_chain
    (stepFnIter_chain (seg_iter5b1_raw n xs t lo hi G na' ma ch)
      (stepFnIter_one stepFn_seqn_splice))
    (seg_iter5b2_raw n xs t lo hi G na' ma ch)

/-- `mid` delivered → the `hi` store → the else-block's closing splice
point. -/
private theorem seg_iter6b1_raw (n : Nat) (xs : List Int) (t lo hi mv : Int)
    (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 3 (sP n xs t 0 0 lo hi false G na')
      (.retV (.int mv .int) (hiRhsK ma)) ch
      = .ok (.exec (.seqn #[]) (envPush ma) (.seq [] (envPush ma) (K1 ma)),
          sP n xs t 0 0 lo (IntKind.normalize .int mv) false G na', ch) := by
  with_unfolding_all rfl

/-- `mid` delivered → the `hi` store, scope exits → the loop head,
composed. -/
private theorem seg_iter6b (n : Nat) (xs : List Int) (t lo hi mv : Int)
    (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 8 (sP n xs t 0 0 lo hi false G na')
      (.retV (.int mv .int) (hiRhsK ma)) ch
      = .ok (headCfg,
          sP n xs t 0 0 lo (IntKind.normalize .int mv) false G na', ch) :=
  stepFnIter_chain
    (stepFnIter_chain (seg_iter6b1_raw n xs t lo hi mv G na' ma ch)
      (stepFnIter_one stepFn_seqn_splice))
    (seg_iter_tail_raw n xs t lo (IntKind.normalize .int mv) G na' ma ch)

/-! ### Exit segments (the post-loop short-circuit guard) -/

private def foundBlk : Stmt :=
  .block #[] #[.seqn #[.assign (.var "$res0") (.var "lo"), .returnStmt]]
private def eqExpr : Expr :=
  .eqCmp (.int .uint64) (.indexGet (.var "s") (.var "lo")) (.var "target")
/-- The post-loop `if`'s delivery continuation. -/
private def postIfK : Cont :=
  .ifK foundBlk (.seqn #[]) envMid2 (.seq [tailSeqn] envMid2 frameK)
/-- The `&&`'s left-operand delivery continuation — `Expr.and`'s
machine shape: a `false` left result short-circuits HERE, never
evaluating `s[lo]`. -/
private def postAndK : Cont := .andK eqExpr envMid2 postIfK

/-- Test false → break unwinding → the guard's `lo < len(s)` walk →
the `lengthOf` apply point. -/
private theorem seg_exit1_raw (n : Nat) (xs : List Int) (t lo hi : Int)
    (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 13 (sP n xs t 0 0 lo hi false g na)
      (.retV (.bool false) cmpCont) ch
      = .ok (.retV (sliceH n)
            (.strictK (.lengthOf (some (.slice (.int .uint64)))) [] []
              envMid2
              (.strictK .lessCmp [.int lo .int] [] envMid2 postAndK)),
          sP n xs t 0 0 lo hi false g na, ch) := by
  with_unfolding_all rfl

/-- The `<` apply at the guard (pure). -/
private theorem seg_exit2_raw (n : Nat) (xs : List Int) (t lo hi lv nv : Int)
    (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 1 (sP n xs t 0 0 lo hi false g na)
      (.retV (.int nv .int)
        (.strictK .lessCmp [.int lv .int] [] envMid2 postAndK)) ch
      = .ok (.retV (.bool (decide (lv < nv))) postAndK,
          sP n xs t 0 0 lo hi false g na, ch) := by
  with_unfolding_all rfl

/-- **The short-circuit, false arm** (`lo = len(s)`): the `&&` delivers
`false` WITHOUT evaluating `s[lo]`, the guard falls through, `-1` is
returned through the frame exit. The out-of-bounds read never
happens — this segment IS that fact. -/
private theorem seg_exitEnd_raw (n : Nat) (xs : List Int) (t lo hi : Int)
    (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 24 (sP n xs t 0 0 lo hi false g na)
      (.retV (.bool false) postAndK) ch
      = .ok (.next .stop, sP n xs t (-1) (-1) lo hi false g na, ch) := by
  with_unfolding_all rfl

/-- The short-circuit, true arm: on into `s[lo] == target` — the `lo`
read (a concrete cell) up to the `indexGet` apply point. -/
private theorem seg_exit3_raw (n : Nat) (xs : List Int) (t lo hi : Int)
    (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 6 (sP n xs t 0 0 lo hi false g na)
      (.retV (.bool true) postAndK) ch
      = .ok (.retV (.int lo .int)
            (.strictK .indexGet [sliceH n] [] envMid2
              (.strictK (.eqCmp (.int .uint64)) [] [.var "target"] envMid2
                (.boolK postIfK))),
          sP n xs t 0 0 lo hi false g na, ch) := by
  with_unfolding_all rfl

/-- Element delivered → the `==` delivery at the guard's `if`. -/
private theorem seg_exit4_raw (n : Nat) (xs : List Int) (t lo hi wv : Int)
    (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 4 (sP n xs t 0 0 lo hi false g na)
      (.retV (.int wv .uint64)
        (.strictK (.eqCmp (.int .uint64)) [] [.var "target"] envMid2
          (.boolK postIfK))) ch
      = .ok (.retV (.bool (wv == t)) postIfK,
          sP n xs t 0 0 lo hi false g na, ch) := by
  with_unfolding_all rfl

/-- Hit: `$res0 = lo; return`, frame exit stores into the result
cell. -/
private theorem seg_exitFound_raw (n : Nat) (xs : List Int) (t lo hi : Int)
    (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 24 (sP n xs t 0 0 lo hi false g na)
      (.retV (.bool true) postIfK) ch
      = .ok (.next .stop,
          sP n xs t (IntKind.normalize .int (IntKind.normalize .int lo))
            (IntKind.normalize .int lo) lo hi false g na, ch) := by
  with_unfolding_all rfl

/-- In-bounds miss: fall through to `return -1`. -/
private theorem seg_exitMiss_raw (n : Nat) (xs : List Int) (t lo hi : Int)
    (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 23 (sP n xs t 0 0 lo hi false g na)
      (.retV (.bool false) postIfK) ch
      = .ok (.next .stop, sP n xs t (-1) (-1) lo hi false g na, ch) := by
  with_unfolding_all rfl

/-! ## Cleaned segments and the loop induction -/

private theorem lookup_single_none {A a : Nat} {c : HeapCell} (h : A ≠ a) :
    Heap.lookup [(.base ⟨A⟩, c)] (.base ⟨a⟩) = none := by
  simp [Heap.lookup, base_beq_false h]

/-- **One iteration, cleaned**: exit-test-true delivery at interval
`(lo, hi)` → the NEXT exit-test delivery, with the interval strictly
narrowed, the invariant re-established, and one dead `mid` cell
appended to the garbage. -/
private theorem search_iter (xs : List Int) (t : Int) (lo hi : Nat)
    (hsorted : Sorted xs) (hlen : xs.length < 2 ^ 62)
    (hlohi : lo < hi) (hhil : hi ≤ xs.length)
    (hlow : ∀ k, k < lo → xs.getD k 0 < t)
    (hhigh : ∀ k, hi ≤ k → k < xs.length → t ≤ xs.getD k 0)
    (g : Heap) (na : Nat) (hna : 8 ≤ na)
    (hg : ∀ a, na ≤ a → Heap.lookup g (.base ⟨a⟩) = none)
    (ch : Choices) :
    ∃ (k lo' hi' : Nat),
      k ≤ 75 ∧ lo ≤ lo' ∧ hi' ≤ hi ∧ hi' - lo' < hi - lo ∧ lo' ≤ hi' ∧
      (∀ j, j < lo' → xs.getD j 0 < t) ∧
      (∀ j, hi' ≤ j → j < xs.length → t ≤ xs.getD j 0) ∧
      stepFnIter k (sP xs.length xs t 0 0 (lo : Int) (hi : Int) false g na)
        (.retV (.bool true) cmpCont) ch
        = .ok (.retV (.bool (decide ((lo' : Int) < (hi' : Int)))) cmpCont,
            sP xs.length xs t 0 0 (lo' : Int) (hi' : Int) false
              (g ++ [(.base ⟨na⟩, icell (((lo + hi) / 2 : Nat) : Int))])
              (na + 1), ch) := by
  obtain ⟨mid, hmiddef⟩ : ∃ m, (lo + hi) / 2 = m := ⟨_, rfl⟩
  rw [hmiddef]
  have hmlo : lo ≤ mid :=
    hmiddef ▸ (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hmhi : mid < hi :=
    hmiddef ▸ (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
  have hmlen : mid < xs.length := by omega
  have hsum : lo + hi < 2 ^ 63 := by omega
  have hmid63 : mid < 2 ^ 63 := by omega
  -- to the mid declaration
  have h1 := seg_iter1_raw xs.length xs t (lo : Int) (hi : Int) g na ch
  -- the allocation
  have h2 := step_alloc_mid xs.length xs t (lo : Int) (hi : Int) g na ch hna
    (hg na (Nat.le_refl na))
  -- the midpoint arithmetic
  have h3 := seg_iter2_raw xs.length xs t (lo : Int) (hi : Int)
    (g ++ [(.base ⟨na⟩, icell 0)]) (na + 1) na ch
  rw [mid_clean hsum, hmiddef] at h3
  -- the mid store
  have h4 := step_store_mid xs.length xs t (lo : Int) (hi : Int) 0
    ((mid : Nat) : Int) .int g (na + 1) na
    (.seq [innerIf] (envMidd na) iterK) ch hna (hg na (Nat.le_refl na))
  rw [inorm_nat_of_lt hmid63] at h4
  -- to the probe read
  have h5 := seg_iter3 xs.length xs t (lo : Int) (hi : Int)
    (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1) na ch
  -- the mid read at the index position
  have h6 := step_load_mid xs.length xs t (lo : Int) (hi : Int) ((mid : Nat) : Int)
    g (na + 1) na (envMidd na)
    (.strictK .indexGet [sliceH xs.length] [] (envMidd na)
      (.strictK .lessCmp [] [.var "target"] (envMidd na) (innerIfK na)))
    ch hna (hg na (Nat.le_refl na)) rfl
  -- the indexGet apply
  have hget : (⟨xs.map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + mid]? = some (.int (xs.getD mid 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega)]
  have h7 : stepFn
      (sP xs.length xs t 0 0 (lo : Int) (hi : Int) false
        (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1))
      (.retV (.int (mid : Nat) .int)
        (.strictK .indexGet [sliceH xs.length] [] (envMidd na)
          (.strictK .lessCmp [] [.var "target"] (envMidd na)
            (innerIfK na)))) ch
      = .ok (.retV (.int (xs.getD mid 0) .uint64)
          (.strictK .lessCmp [] [.var "target"] (envMidd na) (innerIfK na)),
        sP xs.length xs t 0 0 (lo : Int) (hi : Int) false
          (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1), ch) :=
    stepFn_strict_apply
      (applyStrictOp_indexGet_slice lookup_sP_backing (Nat.le_refl xs.length)
        hmlen hget)
  -- to the probe delivery
  have h8 := seg_iter4_raw xs.length xs t (lo : Int) (hi : Int) (xs.getD mid 0)
    (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1) na ch
  -- chain the shared prefix
  have hc2 := stepFnIter_chain h1 h2
  have hc3 := stepFnIter_chain hc2 h3
  have hc4 := stepFnIter_chain hc3 h4
  have hc5 := stepFnIter_chain hc4 h5
  have hc6 := stepFnIter_chain hc5 h6
  have hc7 := stepFnIter_chain hc6 (stepFnIter_one h7)
  have hpre8 := stepFnIter_chain hc7 h8
  -- branch on the probe
  rcases Int.lt_or_le (xs.getD mid 0) t with hprobe | hprobe
  · -- s[mid] < t: lo := mid + 1
    rw [show (decide (xs.getD mid 0 < t)) = true from decide_eq_true hprobe]
      at hpre8
    have h9 := seg_iter5a xs.length xs t (lo : Int) (hi : Int)
      (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1) na ch
    have h10 := step_load_mid xs.length xs t (lo : Int) (hi : Int)
      ((mid : Nat) : Int) g (na + 1) na (envPush na)
      (.strictK .add [] [.intLit 1 .int] (envPush na) (loRhsK na)) ch hna
      (hg na (Nat.le_refl na)) rfl
    have h11 := seg_iter6a xs.length xs t (lo : Int) (hi : Int) ((mid : Nat) : Int)
      (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1) na ch
    rw [show ((mid : Int) + 1) = ((mid + 1 : Nat) : Int) from by omega,
      inorm_nat_of_lt (by omega : mid + 1 < 2 ^ 63),
      inorm_nat_of_lt (by omega : mid + 1 < 2 ^ 63)] at h11
    have h12 := seg_dispatch1_raw xs.length xs t ((mid + 1 : Nat) : Int) (hi : Int)
      (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1) ch
    have hc9 := stepFnIter_chain hpre8 h9
    have hc10 := stepFnIter_chain hc9 h10
    have hc11 := stepFnIter_chain hc10 h11
    have hc12 := stepFnIter_chain hc11 h12
    refine ⟨57 + 18, mid + 1, hi, by omega, by omega, Nat.le_refl _,
      by omega, by omega, inv_lo_step hsorted hprobe hmlen, hhigh, ?_⟩
    exact hc12
  · -- t ≤ s[mid]: hi := mid
    rw [show (decide (xs.getD mid 0 < t)) = false from
      decide_eq_false (by omega)] at hpre8
    have h9 := seg_iter5b xs.length xs t (lo : Int) (hi : Int)
      (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1) na ch
    have h10 := step_load_mid xs.length xs t (lo : Int) (hi : Int)
      ((mid : Nat) : Int) g (na + 1) na (envPush na) (hiRhsK na) ch hna
      (hg na (Nat.le_refl na)) rfl
    have h11 := seg_iter6b xs.length xs t (lo : Int) (hi : Int) ((mid : Nat) : Int)
      (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1) na ch
    rw [inorm_nat_of_lt hmid63] at h11
    have h12 := seg_dispatch1_raw xs.length xs t (lo : Int) ((mid : Nat) : Int)
      (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1) ch
    have hc9 := stepFnIter_chain hpre8 h9
    have hc10 := stepFnIter_chain hc9 h10
    have hc11 := stepFnIter_chain hc10 h11
    have hc12 := stepFnIter_chain hc11 h12
    refine ⟨53 + 18, lo, mid, by omega, Nat.le_refl _, by omega,
      by omega, by omega, hlow, inv_hi_step hsorted hprobe, ?_⟩
    exact hc12

/-- **The exit, cleaned**: exit-test-false delivery at `lo = hi = L` →
the driver terminal, with `findSpec` pinned by the invariant (the
`L = len` case walks the `&&`'s short-circuit: `s[L]` is never
read). -/
private theorem search_exit (xs : List Int) (t : Int) (L : Nat)
    (hsorted : Sorted xs) (hlen : xs.length < 2 ^ 62)
    (hL : L ≤ xs.length)
    (hlow : ∀ k, k < L → xs.getD k 0 < t)
    (hhigh : ∀ k, L ≤ k → k < xs.length → t ≤ xs.getD k 0)
    (g : Heap) (na : Nat) (ch : Choices) :
    ∃ (k : Nat) (σf : ExecState),
      k ≤ 50 ∧
      stepFnIter k (sP xs.length xs t 0 0 (L : Int) (L : Int) false g na)
        (.retV (.bool false) cmpCont) ch
        = .ok (.next .stop, σf, ch)
      ∧ Heap.lookup σf.heap (.base ⟨0⟩) = some (icell (findSpec xs t))
      ∧ Heap.lookup σf.heap (.base ⟨1⟩) = some (arrCell xs.length xs) := by
  have h1 := seg_exit1_raw xs.length xs t (L : Int) (L : Int) g na ch
  have h2 : stepFn (sP xs.length xs t 0 0 (L : Int) (L : Int) false g na)
      (.retV (sliceH xs.length)
        (.strictK (.lengthOf (some (.slice (.int .uint64)))) [] [] envMid2
          (.strictK .lessCmp [.int (L : Int) .int] [] envMid2 postAndK)))
      ch
      = .ok (.retV (.int (xs.length : Nat) .int)
          (.strictK .lessCmp [.int (L : Int) .int] [] envMid2 postAndK),
        sP xs.length xs t 0 0 (L : Int) (L : Int) false g na, ch) :=
    stepFn_strict_apply (applyStrictOp_len_slice (Nat.le_refl xs.length))
  have h3 := seg_exit2_raw xs.length xs t (L : Int) (L : Int) (L : Int)
    ((xs.length : Nat) : Int) g na ch
  have hpre := stepFnIter_chain (stepFnIter_chain h1 (stepFnIter_one h2)) h3
  rcases Nat.lt_or_ge L xs.length with hLn | hLn
  · -- in bounds: the `&&` proceeds into `s[L] == target`
    rw [show (decide ((L : Int) < ((xs.length : Nat) : Int))) = true from
      decide_eq_true (by omega)] at hpre
    have h4 := seg_exit3_raw xs.length xs t (L : Int) (L : Int) g na ch
    have hget : (⟨xs.map (fun v => .int v .uint64)⟩ :
        Array GoValue)[0 + L]? = some (.int (xs.getD L 0) .uint64) := by
      rw [Nat.zero_add, getElem?_mapU _ _ (by omega)]
    have h5 : stepFn (sP xs.length xs t 0 0 (L : Int) (L : Int) false g na)
        (.retV (.int (L : Nat) .int)
          (.strictK .indexGet [sliceH xs.length] [] envMid2
            (.strictK (.eqCmp (.int .uint64)) [] [.var "target"] envMid2
              (.boolK postIfK)))) ch
        = .ok (.retV (.int (xs.getD L 0) .uint64)
            (.strictK (.eqCmp (.int .uint64)) [] [.var "target"] envMid2
              (.boolK postIfK)),
          sP xs.length xs t 0 0 (L : Int) (L : Int) false g na, ch) :=
      stepFn_strict_apply
        (applyStrictOp_indexGet_slice lookup_sP_backing (Nat.le_refl xs.length)
          hLn hget)
    have h6 := seg_exit4_raw xs.length xs t (L : Int) (L : Int) (xs.getD L 0)
      g na ch
    have hpre6 := stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain hpre h4) (stepFnIter_one h5)) h6
    by_cases heq : xs.getD L 0 = t
    · -- found
      rw [show (xs.getD L 0 == t) = true from beq_iff_eq.mpr heq] at hpre6
      have h7 := seg_exitFound_raw xs.length xs t (L : Int) (L : Int) g na ch
      rw [inorm_nat_of_lt (by omega : L < 2 ^ 63),
        inorm_nat_of_lt (by omega : L < 2 ^ 63)] at h7
      refine ⟨15 + 6 + 1 + 4 + 24, _, by omega,
        stepFnIter_chain hpre6 h7, ?_, ?_⟩
      · rw [findSpec_found hLn heq hlow]
        exact lookup_sP_res
      · exact lookup_sP_backing
    · -- in-bounds miss
      rw [show (xs.getD L 0 == t) = false from beq_false_of_ne heq] at hpre6
      have h7 := seg_exitMiss_raw xs.length xs t (L : Int) (L : Int) g na ch
      refine ⟨15 + 6 + 1 + 4 + 23, _, by omega,
        stepFnIter_chain hpre6 h7, ?_, ?_⟩
      · rw [findSpec_miss_inbounds hsorted hLn heq hlow hhigh]
        exact lookup_sP_res
      · exact lookup_sP_backing
  · -- L = len: the short-circuit — `s[L]` is never read
    rw [show (decide ((L : Int) < ((xs.length : Nat) : Int))) = false from
      decide_eq_false (by omega)] at hpre
    have h4 := seg_exitEnd_raw xs.length xs t (L : Int) (L : Int) g na ch
    refine ⟨15 + 24, _, by omega, stepFnIter_chain hpre h4, ?_, ?_⟩
    · rw [findSpec_miss_end (fun k hk => hlow k (by omega))]
      exact lookup_sP_res
    · exact lookup_sP_backing

/-- **The loop**, by strong induction on the interval width
`μ = hi - lo` (the value half and the completion half from the one
induction): from the exit-test delivery, the run reaches the driver
terminal within `75μ + 50` steps with `findSpec` in the result cell
and the backing array untouched. -/
private theorem search_loop (xs : List Int) (t : Int)
    (hsorted : Sorted xs) (hlen : xs.length < 2 ^ 62) :
    ∀ μ lo hi, μ = hi - lo → lo ≤ hi → hi ≤ xs.length →
    (∀ k, k < lo → xs.getD k 0 < t) →
    (∀ k, hi ≤ k → k < xs.length → t ≤ xs.getD k 0) →
    ∀ g na, 8 ≤ na → (∀ a, na ≤ a → Heap.lookup g (.base ⟨a⟩) = none) →
    ∀ ch : Choices, ∃ (k : Nat) (σf : ExecState),
      k ≤ 75 * μ + 50 ∧
      stepFnIter k (sP xs.length xs t 0 0 (lo : Int) (hi : Int) false g na)
        (.retV (.bool (decide ((lo : Int) < (hi : Int)))) cmpCont) ch
        = .ok (.next .stop, σf, ch)
      ∧ Heap.lookup σf.heap (.base ⟨0⟩) = some (icell (findSpec xs t))
      ∧ Heap.lookup σf.heap (.base ⟨1⟩) = some (arrCell xs.length xs) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro lo hi hμ hlohi hhil hlow hhigh g na hna hg ch
    rcases Nat.lt_or_ge lo hi with hlt | hge
    · -- iterate
      rw [show (decide ((lo : Int) < (hi : Int))) = true from
        decide_eq_true (by omega)]
      obtain ⟨k₁, lo', hi', hk₁, hlo', hhi', hdec, hle', hlow', hhigh',
        hrun₁⟩ := search_iter xs t lo hi hsorted hlen hlt hhil hlow
          hhigh g na hna hg ch
      have hg' : ∀ a, na + 1 ≤ a →
          Heap.lookup (g ++ [(.base ⟨na⟩,
            icell (((lo + hi) / 2 : Nat) : Int))]) (.base ⟨a⟩) = none := by
        intro a ha
        rw [lookup_append_of_none (hg a (by omega)),
          lookup_single_none (by omega)]
      obtain ⟨k₂, σf, hk₂, hrun₂, hres, hback⟩ := ih (hi' - lo') (by omega)
        lo' hi' rfl hle' (by omega) hlow' hhigh'
        (g ++ [(.base ⟨na⟩, icell (((lo + hi) / 2 : Nat) : Int))]) (na + 1)
        (by omega) hg' ch
      exact ⟨k₁ + k₂, σf, by omega, stepFnIter_chain hrun₁ hrun₂,
        hres, hback⟩
    · -- exit: lo = hi
      have hEq : lo = hi := by omega
      subst hEq
      rw [show (decide ((lo : Int) < (lo : Int))) = false from
        decide_eq_false (by omega)]
      obtain ⟨k, σf, hk, hrun, hres, hback⟩ := search_exit xs t lo hsorted
        hlen (by omega) hlow (fun j hj hjn => hhigh j (by omega) hjn) g na ch
      exact ⟨k, σf, by omega, hrun, hres, hback⟩

/-! ## The entry and the canonical-placement total run -/

private theorem lookup_seed_backing (xs : List Int) :
    Heap.lookup (searchSeed xs 1 [] 2).heap (.base ⟨1⟩)
      = some ⟨some (.array xs.length (.int .uint64)),
          .array ⟨xs.map (fun v => .int v .uint64)⟩⟩ := by
  simp [searchSeed, resCell, sliceCells, Heap.lookup]

/-- **The entry, cleaned**: canonical seed → the first exit-test
delivery at `(0, len)` within 73 steps. -/
private theorem search_entry (xs : List Int) (t : Int)
    (ht : 0 ≤ t ∧ t < 2 ^ 64) (hlen : xs.length < 2 ^ 62) (ch : Choices) :
    stepFnIter 73 (searchSeed xs 1 [] 2)
      (.exec (searchCall xs 1 t) searchEnv .stop) ch
      = .ok (.retV (.bool (decide ((0 : Int) < (xs.length : Int)))) cmpCont,
          sP xs.length xs t 0 0 0 (xs.length : Int) false [] 8, ch) := by
  have hA := seg_entryA_raw xs t ch
  rw [inorm_nat_of_lt (by omega : xs.length < 2 ^ 63)] at hA
  have happ1 : applyStrictOp (searchSeed xs 1 [] 2) (.sliceExpr false)
      [.addr (.base ⟨1⟩), .int 0 .int, .int ((xs.length : Nat) : Int) .int]
      = .ok (sliceH xs.length, searchSeed xs 1 [] 2) :=
    applyStrictOp_sliceExpr_array (lookup_seed_backing xs) (by simp)
  have hB := seg_entryB_raw xs t ch
  rw [unorm_of_range ht.1 ht.2] at hB
  have hC := seg_entryC_raw xs t ch
  rw [unorm_of_range ht.1 ht.2] at hC
  have happ2 : applyStrictOp (σEntry xs t)
      (.lengthOf (some (.slice (.int .uint64)))) [sliceH xs.length]
      = .ok (.int ((xs.length : Nat) : Int) .int, σEntry xs t) :=
    applyStrictOp_len_slice (Nat.le_refl _)
  have hD := seg_entryD_raw xs t ((xs.length : Nat) : Int) ch
  rw [inorm_nat_of_lt (by omega : xs.length < 2 ^ 63)] at hD
  have hE := seg_dispatch0_raw xs.length xs t 0 (xs.length : Int) [] 8 ch
  have h8 := stepFnIter_chain hA
    (stepFnIter_one
      (stepFn_strict_apply (done := [.int 0 .int, .addr (.base ⟨1⟩)]) happ1))
  have h10 := stepFnIter_chain h8 hB
  have h28 := stepFnIter_chain h10 hC
  have h29 := stepFnIter_chain h28
    (stepFnIter_one (stepFn_strict_apply (done := []) happ2))
  have h48 := stepFnIter_chain h29 hD
  exact stepFnIter_chain h48 hE

/-- **The canonical run, end to end**: from the canonical seed the
driver completes at the `.next .stop` terminal within `123 + 75·len`
steps, with `findSpec` in the result cell and the backing array
untouched. -/
private theorem search_runs (xs : List Int) (t : Int)
    (ht : 0 ≤ t ∧ t < 2 ^ 64)
    (hsorted : Sorted xs) (hlen : xs.length < 2 ^ 62) (ch : Choices) :
    ∃ (k : Nat) (σf : ExecState), k ≤ 123 + 75 * xs.length ∧
      stepFnIter k (searchSeed xs 1 [] 2)
        (.exec (searchCall xs 1 t) searchEnv .stop) ch
        = .ok (.next .stop, σf, ch)
      ∧ Heap.lookup σf.heap (.base ⟨0⟩) = some (icell (findSpec xs t))
      ∧ Heap.lookup σf.heap (.base ⟨1⟩) = some (arrCell xs.length xs) := by
  have hE := search_entry xs t ht hlen ch
  obtain ⟨k, σf, hk, hrun, hres, hback⟩ := search_loop xs t hsorted hlen
    xs.length 0 xs.length (by omega) (by omega) (Nat.le_refl _)
    (fun k hk => absurd hk (by omega))
    (fun k hk hk' => absurd (Nat.lt_of_le_of_lt hk hk') (by omega))
    [] 8 (by omega) (fun a _ => rfl) ch
  refine ⟨73 + k, σf, by omega, ?_, hres, hback⟩
  exact stepFnIter_chain hE hrun

/-- **Total correctness at the canonical placement**: past fuel
`123 + 75·len`, at every choice stream, execution completes normally
with `findSpec` in the result cell and the backing array untouched. -/
private theorem search_total_canonical (xs : List Int) (t : Int)
    (ht : 0 ≤ t ∧ t < 2 ^ 64)
    (hsorted : Sorted xs) (hlen : xs.length < 2 ^ 62) :
    ∀ fuel : Nat, 123 + 75 * xs.length ≤ fuel → ∀ ch : Choices,
      ∃ σf : ExecState,
        execStmtLoop fuel (searchSeed xs 1 [] 2)
          (.exec (searchCall xs 1 t) searchEnv .stop) ch
          = .ok (.normal σf, ch)
        ∧ Heap.lookup σf.heap (.base ⟨0⟩) = some (icell (findSpec xs t))
        ∧ Heap.lookup σf.heap (.base ⟨1⟩)
            = some (arrCell xs.length xs) := by
  intro fuel hfuel ch
  obtain ⟨k, σf, hk, hrun, hres, hback⟩ :=
    search_runs xs t ht hsorted hlen ch
  refine ⟨σf, ?_, hres, hback⟩
  have hfold := execStmtLoop_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [hfold, execStmtLoop_next_stop]

/-! ## The framed form: the frame theorem consumed at an
input-RELOCATING renaming

The ∀-placement (`base`) quantifier is realized by the GENERALIZED `ρ`
(any `ShiftSpec` injection): `relocS base na` FIXES the result cell
(`0 ↦ 0`), RELOCATES the input backing cell (`1 ↦ base`), and shifts
the canonical fresh region (`[2, ∞) ↦ [na, ∞)`). The canonical seed is
TIGHT (dom = {0, 1}, na₀ = 2), exactly what `fr_avoid`'s seed
discharge needs. -/

open GoLean.Frame

/-- The relocating renaming: `0 ↦ 0`, `1 ↦ base`, `2 + k ↦ na + k`. -/
private def relocS (base na : Nat) : Nat → Nat :=
  fun x => if x = 0 then 0 else if x = 1 then base else na + (x - 2)

/-- The seed simulation: the canonical seed beside the framed seed at
an arbitrary admissible placement, through the relocating renaming. -/
private theorem searchSeedFrameSim (xs : List Int) (t : Int) (base : Nat)
    (fr : Heap) (na : Nat) (hb0 : base ≠ 0)
    (hfb : Heap.lookup fr (.base ⟨base⟩) = none)
    (hf0 : Heap.lookup fr (.base ⟨0⟩) = none)
    (hwf : MachineWf
      { functions := searchLowered.funcs,
        heap := resCell ++ sliceCells xs base ++ fr, nextAddr := na }
      (.exec (searchCall xs base t) searchEnv .stop)) :
    FrameSim (relocS base na) 2 na fr (searchSeed xs 1 [] 2)
      (searchSeed xs base fr na) := by
  have hs := hwf.1
  simp only [StateWf, ExecState.locSup, Heap.locSup, resCell, sliceCells,
    List.cons_append, List.nil_append, Loc.locSup, Loc.rootBase,
    Nat.max_le] at hs
  have hbase : base + 1 ≤ na := by omega
  have hfrsup : Heap.locSup fr ≤ na := by omega
  have h2na : 2 ≤ na := by omega
  have hren0 : renameLoc (relocS base na) (.base ⟨0⟩) = .base ⟨0⟩ := by
    simp [renameLoc, relocS]
  have hren1 : renameLoc (relocS base na) (.base ⟨1⟩) = .base ⟨base⟩ := by
    simp [renameLoc, relocS]
  have hcellarr : renameCell (relocS base na)
      (⟨some (.array xs.length (.int .uint64)),
        .array ⟨xs.map (fun v => .int v .uint64)⟩⟩ : HeapCell)
      = ⟨some (.array xs.length (.int .uint64)),
         .array ⟨xs.map (fun v => .int v .uint64)⟩⟩ := by
    simp [renameCell, renameValue_locFree _ _ (locSup_mapU xs)]
  refine ⟨⟨?_, ?_⟩, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- inj
    intro x y hxy
    simp only [relocS] at hxy
    split at hxy <;> split at hxy <;>
      first
        | omega
        | (split at hxy <;> first | omega | (split at hxy <;> omega))
  · -- shift
    intro k
    simp only [relocS, if_neg (by omega : ¬ (2 + k = 0)),
      if_neg (by omega : ¬ (2 + k = 1))]
    omega
  · -- next_eq: na = ρ 2
    simp [searchSeed, relocS]
  · -- alloc_reg
    exact Nat.le_refl 2
  · -- lookup_img
    intro l
    by_cases hl0 : l = .base ⟨0⟩
    · subst hl0
      rw [hren0]
      simp only [searchSeed, resCell, sliceCells, List.cons_append,
        List.nil_append, Heap.lookup]
      simp [renameCell, renameValue]
    · by_cases hl1 : l = .base ⟨1⟩
      · subst hl1
        rw [hren1]
        have hne : ((.base ⟨0⟩ : Loc) == .base ⟨base⟩) = false :=
          beq_false_of_ne (by simpa using fun h => hb0 h.symm)
        simp only [searchSeed, resCell, sliceCells, List.cons_append,
          List.nil_append, Heap.lookup, hne, Bool.false_eq_true, if_false,
          beq_self_eq_true, if_true, if_pos]
        simp [hcellarr]
      · have hcanon : Heap.lookup (searchSeed xs 1 [] 2).heap l = none := by
          have hne0 : ((.base ⟨0⟩ : Loc) == l) = false :=
            beq_false_of_ne (fun h => hl0 h.symm)
          have hne1 : ((.base ⟨1⟩ : Loc) == l) = false :=
            beq_false_of_ne (fun h => hl1 h.symm)
          simp [searchSeed, resCell, sliceCells, Heap.lookup, hne0, hne1]
        rw [hcanon]
        have hne0' : ((.base ⟨0⟩ : Loc) == renameLoc (relocS base na) l)
            = false := by
          refine beq_false_of_ne (fun hc => ?_)
          cases l with
          | base a =>
              simp only [renameLoc, Loc.base.injEq, Addr.mk.injEq] at hc
              by_cases ha0 : a.id = 0
              · exact hl0 (by
                  obtain ⟨id⟩ := a
                  exact congrArg (fun n => Loc.base ⟨n⟩) ha0)
              · by_cases ha1 : a.id = 1
                · simp only [relocS, if_neg ha0, if_pos ha1] at hc
                  exact hb0 hc.symm
                · simp only [relocS, if_neg ha0, if_neg ha1] at hc
                  omega
          | field b tid f => simp [renameLoc] at hc
          | index b i => simp [renameLoc] at hc
        have hneb' : ((.base ⟨base⟩ : Loc) == renameLoc (relocS base na) l)
            = false := by
          refine beq_false_of_ne (fun hc => ?_)
          cases l with
          | base a =>
              simp only [renameLoc, Loc.base.injEq, Addr.mk.injEq] at hc
              by_cases ha0 : a.id = 0
              · simp only [relocS, if_pos ha0] at hc
                exact hb0 hc
              · by_cases ha1 : a.id = 1
                · exact hl1 (by
                    obtain ⟨id⟩ := a
                    exact congrArg (fun n => Loc.base ⟨n⟩) ha1)
                · simp only [relocS, if_neg ha0, if_neg ha1] at hc
                  omega
          | field b tid f => simp [renameLoc] at hc
          | index b i => simp [renameLoc] at hc
        simp only [searchSeed, resCell, sliceCells, List.cons_append,
          List.nil_append, Heap.lookup, hne0', hneb', Bool.false_eq_true,
          if_false]
  · -- frame_pres
    intro l c hl
    have hne0 : ((.base ⟨0⟩ : Loc) == l) = false := by
      refine beq_false_of_ne (fun hc => ?_)
      rw [← hc, hf0] at hl
      cases hl
    have hneb : ((.base ⟨base⟩ : Loc) == l) = false := by
      refine beq_false_of_ne (fun hc => ?_)
      rw [← hc, hfb] at hl
      cases hl
    simp only [searchSeed, resCell, sliceCells, List.cons_append,
      List.nil_append, Heap.lookup, hne0, hneb, Bool.false_eq_true,
      if_false]
    exact hl
  · -- fr_avoid
    intro a
    by_cases ha0 : a = 0
    · subst ha0
      simpa [relocS] using hf0
    · by_cases ha1 : a = 1
      · subst ha1
        simpa [relocS, ha0] using hfb
      · cases hlk : Heap.lookup fr (.base ⟨relocS base na a⟩) with
        | none => rfl
        | some c =>
            exfalso
            have hkey := Heap.lookup_key_locSup hlk
            simp only [Loc.locSup, Loc.rootBase] at hkey
            simp only [relocS, if_neg ha0, if_neg ha1] at hkey
            omega
  · -- bodies_inv
    exact renameBodies_id (n := 0) (fun x hx => absurd hx (Nat.not_lt_zero x))
      (fs := searchLowered.funcs)
      (by decide : funcListSup searchLowered.funcs.toList ≤ 0)

/-- The driver configuration renames to the framed driver: the
relocating renaming carries the `locLit` backing pointer to `base` and
fixes the result cell — the ∀-placement realization. -/
private theorem search_cfg_ren (xs : List Int) (t : Int) (base na : Nat) :
    renameConfig (relocS base na)
      (.exec (searchCall xs 1 t) searchEnv .stop)
      = .exec (searchCall xs base t) searchEnv .stop := by
  simp [renameConfig, renameCont, renameEnv, renameScope, renameStmt,
    searchCall, searchEnv, renameExprList, renameExpr, renameOptExpr,
    renameAssignee, renameLoc, relocS]

private theorem loadLoc_of_lookup {σ : ExecState} {a : Addr} {c : HeapCell}
    (h : Heap.lookup σ.heap (.base a) = some c) :
    loadLoc σ (.base a) = .ok c.value := by
  unfold loadLoc
  rw [h]
  rfl

/-! ## The memory-quantified form (proof-side supporting layer per §11) -/

/-- **The memory-quantified total-correctness form** — since the
harness ruling (2026-08-13, `docs/2026-08-12_example-spec-form.md`
§11) this is the PROOF-SIDE SUPPORTING LAYER, not the user-facing
headline (that is `search_ok` below, stated over the machine's native
function entry `runFunctionWithContextM`): *for any SORTED list `xs`
of uint64 values of length below `2^62`, any in-range target `t`,
wherever the input lives in memory (`base`), with anything else
present (`fr`): the driver `$callres = search(s, target)` completes
normally — past one fuel bound, at every nondeterminism-choice
stream — the result cell then holds the index of the FIRST occurrence
of `t` (or `-1`), the backing array is unchanged, and no other memory
is touched.*

THE `2^62` BOUND IS THE EXAMPLE'S TEACHING POINT (module docstring):
`mid := (lo + hi) / 2` computes `lo + hi` in Go `int`; at lengths at or
beyond `2^62` the sum can reach `2^63` and WRAP NEGATIVE — the classic
"nearly all binary searches are broken" overflow bug (Bloch 2006).
Below the bound the proof carries `lo + hi < 2^63` through every
iteration (from `lo ≤ hi ≤ len`), so the bound is Go's own arithmetic
domain, not a proof-method limit.

The frame layer here (∀-placement `base`, ∀-frame `fr`) remains the
proof-side ∀-placement engine; per §11 nothing heap-quantified is
user-facing.

The proof: total correctness at the TIGHT canonical placement
(result cell at 0, backing at 1 — direct machine-step segments +
strong induction on the interval width `hi - lo`), then the executable
frame theorem's success-run transfer at the input-RELOCATING renaming
`relocS base na` (fixes 0, carries 1 to `base`); nothing is re-run at
the framed placement. The fuel bound is `123 + 75·len` — linear, from
the ≤-halving loop bounded by its iteration count ≤ len. -/
theorem search_framed (xs : List Int) (t : Int)
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (ht : 0 ≤ t ∧ t < 2 ^ 64)
    (hsorted : GoLean.SliceMem.Sorted xs)
    (hlen : xs.length < 2 ^ 62)
    (base : Nat) (hb0 : base ≠ 0)
    (fr : Heap) (na : Nat)
    (hfb : Heap.lookup fr (.base ⟨base⟩) = none)
    (hf0 : Heap.lookup fr (.base ⟨0⟩) = none)
    (hwf : MachineWf
      { functions := searchLowered.funcs,
        heap := resCell ++ sliceCells xs base ++ fr, nextAddr := na }
      (.exec (searchCall xs base t) searchEnv .stop)) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel searchEnv (searchSeed xs base fr na) ch
            (searchCall xs base t)
          = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int (findSpec xs t) .int)
        ∧ Heap.lookup σf.heap (.base ⟨base⟩)
            = some ⟨some (.array xs.length (.int .uint64)),
                .array ⟨xs.map (fun v => .int v .uint64)⟩⟩
        ∧ ∀ (a : Nat) (c : HeapCell),
            Heap.lookup fr (.base ⟨a⟩) = some c →
            Heap.lookup σf.heap (.base ⟨a⟩) = some c := by
  -- `hxs` (element range) is NOT consumed by the machine proof: the
  -- program never writes the backing array, and the machine's `<`/`==`
  -- on int values are kind-agnostic — the hypothesis stays in the
  -- statement as the honest uint64-domain restriction of the claim.
  have _hxs_recorded := hxs
  have hSF := searchSeedFrameSim xs t base fr na hb0 hfb hf0 hwf
  refine ⟨123 + 75 * xs.length, fun fuel hfuel ch => ?_⟩
  obtain ⟨σc, hrunC, hresC, hbackC⟩ :=
    search_total_canonical xs t ht hsorted hlen fuel hfuel ch
  obtain ⟨outF, hrunF, hout⟩ := Frame.execStmtLoop_ren fuel hSF hrunC
  rw [search_cfg_ren xs t base na] at hrunF
  cases outF with
  | normal σF =>
      obtain ⟨hSF', -⟩ := hout
      refine ⟨σF, ch, hrunF, ?_, ?_, ?_⟩
      · have hlook := hSF'.lookup_some hresC
        rw [show renameLoc (relocS base na) (.base ⟨0⟩) = .base ⟨0⟩ from
          by simp [renameLoc, relocS]] at hlook
        rw [show renameCell (relocS base na) (icell (findSpec xs t))
            = icell (findSpec xs t) from by simp [renameCell, renameValue]]
          at hlook
        exact loadLoc_of_lookup hlook
      · have hlook := hSF'.lookup_some hbackC
        rw [show renameLoc (relocS base na) (.base ⟨1⟩) = .base ⟨base⟩ from
          by simp [renameLoc, relocS]] at hlook
        rw [show renameCell (relocS base na) (arrCell xs.length xs)
            = arrCell xs.length xs from by
          simp [renameCell, arrCell,
            renameValue_locFree _ _ (locSup_mapU xs)]] at hlook
        exact hlook
      · intro a c hac
        exact hSF'.frame_pres (.base ⟨a⟩) c hac
  | returned σF => exact hout.elim
  | broke σF => exact hout.elim
  | continued σF => exact hout.elim

/-- **The D1 run-conditioned readout twin of the framed form** (proof-
side supporting layer per §11): any normal completion at ANY fuel and
stream from the framed seed delivers the `search_framed` value
clauses — derived from the total form via `normal_readout_of_total`,
no second walk. -/
theorem search_framed_readout (xs : List Int) (t : Int)
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (ht : 0 ≤ t ∧ t < 2 ^ 64)
    (hsorted : GoLean.SliceMem.Sorted xs)
    (hlen : xs.length < 2 ^ 62)
    (base : Nat) (hb0 : base ≠ 0)
    (fr : Heap) (na : Nat)
    (hfb : Heap.lookup fr (.base ⟨base⟩) = none)
    (hf0 : Heap.lookup fr (.base ⟨0⟩) = none)
    (hwf : MachineWf
      { functions := searchLowered.funcs,
        heap := resCell ++ sliceCells xs base ++ fr, nextAddr := na }
      (.exec (searchCall xs base t) searchEnv .stop)) :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel searchEnv (searchSeed xs base fr na) ch
          (searchCall xs base t)
        = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int (findSpec xs t) .int)
      ∧ Heap.lookup σf.heap (.base ⟨base⟩)
          = some ⟨some (.array xs.length (.int .uint64)),
              .array ⟨xs.map (fun v => .int v .uint64)⟩⟩
      ∧ ∀ (a : Nat) (c : HeapCell),
          Heap.lookup fr (.base ⟨a⟩) = some c →
          Heap.lookup σf.heap (.base ⟨a⟩) = some c :=
  normal_readout_of_total
    (search_framed xs t hxs ht hsorted hlen base hb0 fr na hfb hf0 hwf)

/-! # The harness form (THE HEADLINE per the 2026-08-13 ruling, §11)

The user-facing statement quantifies over `GoValue` ARGUMENTS at the
machine's native function entry `runFunctionWithContextM` and observes
ONLY termination + returned values. The fixed Go harness
(`Corpus/coverage/exec/examples/binsearch/main.go`, `search_harness`)
has the three §11 phases: SETUP builds the sorted input family
`s[i] = seed + 2*i` from the scalar parameters (no wrap under
`hnowrap`, so the family is genuinely sorted, with gaps so the
raw-target parameter covers found, not-found-in-range and
not-found-past-the-end); the CALL under test is `search(s, t)`; the
TEST phase is the identity — the returned index is the observable.

Input-family honesty (§11): scalar-parameterized setup gives the
`bsFamily` INPUT FAMILY, honestly weaker than ∀xs over slice
contents — the ∀-slice mechanism (choice-consuming input pick) is
designed, not built. The proof-side `search_framed` above carries the
∀xs claim in the memory-quantified (non-user-facing) form.

Harness address layout (probe `.tmp/hbs-probe1.lean`): 0 = `n`,
1 = `seed`, 2 = `t`, 3 = the harness `$res0`, 4 = `$c6` (the make
handle), 5 = the BACKING ARRAY, 6 = `s`, 7 = the setup `i`, 8 = the
setup `$forFirst`, 9 = `$c7` (the call result), then the subject
frame: 10 = `s` param, 11 = `target`, 12 = the subject `$res0`,
13 = `lo`, 14 = `hi`, 15 = the subject `$forFirst`, and the dead
per-iteration `mid` cells from 16 up (the garbage suffix `g`). -/

/-- **The input family**: the sorted, gapped sequence the harness's
setup phase materializes — `bsFamily n seed = [seed, seed+2, …,
seed+2(n-1)]` (as mathematical integers; `hnowrap` in the headline is
what makes the machine's wrapped uint64 stores agree with it). -/
def bsFamily (n seed : Nat) : List Int :=
  (List.range n).map (fun i => ((seed + 2 * i : Nat) : Int))

theorem bsFamily_length (n seed : Nat) : (bsFamily n seed).length = n := by
  simp [bsFamily]

private theorem bsFamily_getD {n seed k : Nat} (hk : k < n) :
    (bsFamily n seed).getD k 0 = ((seed + 2 * k : Nat) : Int) := by
  rw [bsFamily, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk]
  rfl

/-- The family is sorted outright (monotone `Nat` sums, no wrap at the
list level; `hnowrap` is what ties the MACHINE's stores to it). -/
theorem bsFamily_sorted (n seed : Nat) : Sorted (bsFamily n seed) := by
  intro i j hij hj
  rw [bsFamily_length] at hj
  rw [bsFamily_getD (by omega), bsFamily_getD hj]
  omega

/-- The one-step family extension the setup-loop invariant consumes:
storing `seed + 2*i` at position `i` of `family-prefix ++ zeros`. -/
private theorem bsFamily_set {n seed i : Nat} (hi : i < n) :
    (bsFamily i seed ++ List.replicate (n - i) 0).set i
        ((seed + 2 * i : Nat) : Int)
      = bsFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0 := by
  have hrep : List.replicate (n - i) (0 : Int)
      = 0 :: List.replicate (n - (i + 1)) 0 := by
    rw [show n - i = (n - (i + 1)) + 1 from by omega, List.replicate_succ]
  have hfam : bsFamily (i + 1) seed
      = bsFamily i seed ++ [((seed + 2 * i : Nat) : Int)] := by
    rw [bsFamily, bsFamily, List.range_succ, List.map_append]
    rfl
  rw [hrep, hfam, List.append_assoc]
  have hlen : (bsFamily i seed).length = i := bsFamily_length i seed
  rw [List.set_append_right _ _ (by omega), hlen, Nat.sub_self]
  rfl

private theorem bsFamilyZ_range {n seed i : Nat}
    (hnw : seed + 2 * n < 2 ^ 64) (hin : i ≤ n) :
    ∀ v ∈ bsFamily i seed ++ List.replicate (n - i) (0 : Int),
      0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · simp only [bsFamily, List.mem_map, List.mem_range] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    omega
  · rw [List.eq_of_mem_replicate hv]
    omega

/-! ## The harness lowering, transcribed (pinned by `rfl`) -/

/-- The setup loop's `for`-desugar body: dispatch (`i++` on later
passes), exit test `i < n`, the store `s[i] = seed + 2*i`. -/
abbrev setupBody : Stmt :=
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
                (.add (.var "seed")
                  (.mul (.intLit 2 .uint64) (.var "i")))]]]

/-- The harness's `Func` record, verbatim from the pinned lowering (the
`example` pin below ties it by `rfl`). -/
def searchHarnessFunc : Func :=
  { id := { key := "search_harness" },
    args := #[{ id := "n", typ := .int .uint64 },
              { id := "seed", typ := .int .uint64 },
              { id := "t", typ := .int .uint64 }],
    results := #[{ id := "$res0", typ := .int .int }],
    body := .block #[]
      #[.seqn
          #[.initialization { id := "$c6", typ := .slice (.int .uint64) },
            .makeSlice (.var "$c6") (.int .uint64) (.var "n") none],
        .seqn
          #[.initialization { id := "s", typ := .slice (.int .uint64) },
            .assign (.var "s") (.var "$c6")],
        .block #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .uint64 },
                .assign (.var "i") (.intLit 0 .uint64)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) setupBody]],
        .seqn
          #[.initialization { id := "$c7", typ := .int .int },
            .call #[.var "$c7"] ⟨"search"⟩ #[.var "s", .var "t"]],
        .seqn
          #[.assign (.var "$res0") (.var "$c7"),
            .returnStmt]],
    variadic := false,
    wrapper := false }

/-- The lowering pin: the proof subject IS the frontend's lowering. -/
theorem searchHarness_pin :
    findFunctionIn? searchLowered.funcs ⟨"search_harness"⟩
    = some searchHarnessFunc := rfl

/-! ## The entry equation (the §11 glue: `runFunctionWithContextM`
unfolded to its `runConfig` loop at the probed initial state) -/

/-- The entry frame environment (probe-pinned). -/
private def hEnv0 : LocalEnv :=
  [[("$res0", .base ⟨3⟩), ("t", .base ⟨2⟩), ("seed", .base ⟨1⟩),
    ("n", .base ⟨0⟩)]]

private abbrev ucellU (v : Int) : HeapCell :=
  ⟨some (.int .uint64), .int (IntKind.normalize .uint64 v) .uint64⟩

/-- The initial state `runFunctionWithContextM` builds: the three
parameters normalized at `uint64`, the result cell at its `int`
default. -/
private def σH0 (nv sv tv : Int) : ExecState :=
  { types := searchLowered.typeDefs.toList,
    functions := searchLowered.funcs,
    methods := searchLowered.methods,
    heap := [(.base ⟨0⟩, ucellU nv), (.base ⟨1⟩, ucellU sv),
             (.base ⟨2⟩, ucellU tv), (.base ⟨3⟩, icell 0)],
    nextAddr := 4 }

/-- **The entry equation**: the native entry IS its `runConfig` loop
from the probed initial state, plus the result read at `.base ⟨3⟩` —
∀ fuel, ∀ choices, definitionally (the prelude — arity check,
`bindParams`, `allocDecls`, `pinResultLocs` — is fuel-independent). -/
private theorem harness_entry_eq (nv sv tv : Int) (fuel : Nat)
    (ch : Choices) :
    runFunctionWithContextM fuel searchLowered.typeDefs.toList
        searchLowered.funcs searchHarnessFunc
        #[.int nv .uint64, .int sv .uint64, .int tv .uint64]
        searchLowered.methods ch
      = (do
          let r ← runConfig fuel (σH0 nv sv tv)
            (.exec searchHarnessFunc.body hEnv0
              (.frame [] [] [] [] .stop false)) ch
          return { values := (← loadMany r.1 [.base ⟨3⟩]).toArray }) := by
  with_unfolding_all rfl

/-! ## The harness machine layer (probe-verified; every raw segment
below re-checks the transcription by `rfl`) -/

/-- The handle over the backing array at its fixed address 5. -/
private abbrev hHandleCell (n : Nat) : HeapCell :=
  ⟨some (.slice (.int .uint64)), .slice ⟨some (.base ⟨5⟩), 0, n, n⟩⟩
private abbrev hSliceH (n : Nat) : GoValue :=
  .slice ⟨some (.base ⟨5⟩), 0, n, n⟩

private def hScope0 : List (String × Loc) :=
  [("$res0", .base ⟨3⟩), ("t", .base ⟨2⟩), ("seed", .base ⟨1⟩),
   ("n", .base ⟨0⟩)]

/-- The cleaned start state (the entry equation's `σH0` after the
range hypotheses collapse the parameter normalizations). -/
private def σStart (n seed : Nat) (tv : Int) : ExecState :=
  { types := searchLowered.typeDefs.toList,
    functions := searchLowered.funcs,
    methods := searchLowered.methods,
    heap := [(.base ⟨0⟩, ucell (n : Int)), (.base ⟨1⟩, ucell (seed : Int)),
             (.base ⟨2⟩, ucell tv), (.base ⟨3⟩, icell 0)],
    nextAddr := 4 }

/-- `$c6` declared (default slice), the makeSlice length delivered. -/
private def σStartC6 (n seed : Nat) (tv : Int) : ExecState :=
  { σStart n seed tv with
    heap := (σStart n seed tv).heap
      ++ [(.base ⟨4⟩, ⟨some (.slice (.int .uint64)),
            .slice ⟨none, 0, 0, 0⟩⟩)],
    nextAddr := 5 }

/-- Post-makeSlice: the handle in `$c6`, the zeroed backing at 5. -/
private def σMkS (n seed : Nat) (tv : Int) : ExecState :=
  { types := searchLowered.typeDefs.toList,
    functions := searchLowered.funcs,
    methods := searchLowered.methods,
    heap := [(.base ⟨0⟩, ucell (n : Int)), (.base ⟨1⟩, ucell (seed : Int)),
             (.base ⟨2⟩, ucell tv), (.base ⟨3⟩, icell 0),
             (.base ⟨4⟩, hHandleCell n),
             (.base ⟨5⟩, arrCell n (List.replicate n 0))],
    nextAddr := 6 }

private def envC6 : LocalEnv := [[("$c6", .base ⟨4⟩)], hScope0]

private def stmtDeclS : Stmt :=
  .seqn #[.initialization { id := "s", typ := .slice (.int .uint64) },
          .assign (.var "s") (.var "$c6")]
private def stmtSetupBlock : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .uint64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) setupBody]]
private def stmtCallC7 : Stmt :=
  .seqn #[.initialization { id := "$c7", typ := .int .int },
          .call #[.var "$c7"] ⟨"search"⟩ #[.var "s", .var "t"]]
private def stmtRetRes : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "$c7"), .returnStmt]

private def hFrame0 : Cont := .frame [] [] [] [] .stop false

/-- The continuation below the makeSlice apply. -/
private def hAfterMsK : Cont :=
  .seq [stmtDeclS, stmtSetupBlock, stmtCallC7, stmtRetRes] envC6 hFrame0

private def hMsK : Cont :=
  .stmtOpK (.makeSlice (.int .uint64) false) 1 [.addr (.base ⟨4⟩)] []
    envC6 hAfterMsK

/-- Entry A: harness body start → the makeSlice length delivery (the
`$c6` declaration, the target ref, the `var n` read). -/
private theorem hseg_A1_raw (n seed : Nat) (tv : Int) (ch : Choices) :
    stepFnIter 10 (σStart n seed tv)
      (.exec searchHarnessFunc.body hEnv0 hFrame0) ch
      = .ok (.retV (.int ((n : Nat) : Int) .uint64) hMsK,
          σStartC6 n seed tv, ch) := by
  with_unfolding_all rfl

/-- **The makeSlice apply at a SYMBOLIC length** (conditioned only on
the length being a `Nat` cast — the bounds checks and `Int.toNat`
cannot reduce on an open term): allocates the zeroed backing at 5 and
stores the handle in `$c6`. -/
private theorem hstep_makeSlice (n seed : Nat) (tv : Int) (ch : Choices) :
    stepFn (σStartC6 n seed tv)
      (.retV (.int ((n : Nat) : Int) .uint64) hMsK) ch
      = .ok (.next hAfterMsK, σMkS n seed tv, ch) := by
  have hb := GoLean.Iris.buildDefaultArrayValue_int (σStartC6 n seed tv)
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
  have happly : applyStmtOp (σStartC6 n seed tv) ch
      (.makeSlice (.int .uint64) false) 1
      [.addr (.base ⟨4⟩), .int ((n : Nat) : Int) .uint64]
      = .ok (σMkS n seed tv, ch) := by
    simp only [applyStmtOp, applyStmtOpCore, valueAsInt, valueAsLoc,
      hnn1, hnn2, hb, Bind.bind, Except.bind, pure, Except.pure]
    rw [if_neg (Nat.lt_irrefl n)]
    with_unfolding_all rfl
  exact stepFn_stmtOp_apply
    (done := [.addr (.base ⟨4⟩)]) (v := .int ((n : Nat) : Int) .uint64)
    happly

/-! ### The setup loop -/

/-- The setup-loop state family: the nine fixed cells (parameters,
harness result, `$c6`, the BACKING at 5, `s`, `i`, `$forFirst`);
`l` the backing list, `iv` the counter value. The setup loop never
allocates — reverse's fixed-address shape. -/
private def sSU (n : Nat) (sv tv : Int) (l : List Int) (iv : Int)
    (ff : Bool) : ExecState :=
  { types := searchLowered.typeDefs.toList,
    functions := searchLowered.funcs,
    methods := searchLowered.methods,
    heap := [(.base ⟨0⟩, ucell (n : Int)), (.base ⟨1⟩, ucell sv),
             (.base ⟨2⟩, ucell tv), (.base ⟨3⟩, icell 0),
             (.base ⟨4⟩, hHandleCell n), (.base ⟨5⟩, arrCell n l),
             (.base ⟨6⟩, hHandleCell n), (.base ⟨7⟩, ucell iv),
             (.base ⟨8⟩, bcell ff)],
    nextAddr := 9 }

private def envSU : LocalEnv :=
  [[("$forFirst", .base ⟨8⟩)], [("i", .base ⟨7⟩)],
   [("s", .base ⟨6⟩), ("$c6", .base ⟨4⟩)], hScope0]
private def envSU2 : LocalEnv :=
  [[("i", .base ⟨7⟩)], [("s", .base ⟨6⟩), ("$c6", .base ⟨4⟩)], hScope0]
private def envH2 : LocalEnv :=
  [[("s", .base ⟨6⟩), ("$c6", .base ⟨4⟩)], hScope0]

private def suTail : Cont :=
  .seq [] envSU (.seq [] envSU2
    (.seq [stmtCallC7, stmtRetRes] envH2 hFrame0))
/-- The setup loop-head configuration. -/
private def suHeadCfg : Config :=
  .exec (.while (.boolLit true) setupBody) envSU suTail
private def suLoopK : Cont := .loop (.boolLit true) setupBody envSU suTail

private def suStoreBlk : Stmt :=
  .block #[]
    #[.seqn
        #[.assign
            (.addr (.indexAddr (.var "s") (.var "i")))
            (.add (.var "seed")
              (.mul (.intLit 2 .uint64) (.var "i")))]]

/-- The setup exit test's delivery continuation. -/
private def suCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envSU)
    (.seq [suStoreBlk] ([] :: envSU) suLoopK)

private def suStoreTail : Cont :=
  .seq [] ([] :: [] :: envSU) (.seq [] ([] :: envSU) suLoopK)

/-- Entry A2: makeSlice done → `s := $c6`, `i := 0`, the `$forFirst`
block → the setup loop head. -/
private theorem hseg_A2_raw (n seed : Nat) (tv : Int) (ch : Choices) :
    stepFnIter 42 (σMkS n seed tv) (.next hAfterMsK) ch
      = .ok (suHeadCfg,
          sSU n (seed : Int) tv (List.replicate n 0) 0 true, ch) := by
  with_unfolding_all rfl

/-- Setup first-pass dispatch: flag drops, the exit test `i < n` reads
`i` (cell 7) and `n` (cell 0). -/
private theorem hsegSU_d0_raw (n : Nat) (sv tv iv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 25 (sSU n sv tv l iv true) suHeadCfg ch
      = .ok (.retV (.bool (decide (iv < ((n : Nat) : Int)))) suCmpK,
          sSU n sv tv l iv false, ch) := by
  with_unfolding_all rfl

/-- Setup body: test true → the store point of `s[i] = seed + 2*i`
(target chain resolved, `seed`/`2`/`i` read, `*` and `+` applied at
uint64). -/
private theorem hsegSU_body_raw (n : Nat) (sv tv iv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 22 (sSU n sv tv l iv false) (.retV (.bool true) suCmpK) ch
      = .ok (.next (.storeK
            [.chain (hSliceH n) [.int iv .uint64] [.index]]
            [.int (IntKind.normalize .uint64
                (sv + IntKind.normalize .uint64 (2 * iv))) .uint64]
            (.seqn #[]) ([] :: [] :: envSU) suStoreTail),
          sSU n sv tv l iv false, ch) := by
  with_unfolding_all rfl

/-- The setup element store, cleaned (`storeTarget` replays the chain;
bounds check at store time): the backing list at position `i` set. -/
private theorem hstep_store_setup (n : Nat) (sv tv : Int) (l : List Int)
    (i : Nat) (w : Int) (hi : i < n) (hlen : l.length = n)
    (hl : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64) (hw : 0 ≤ w ∧ w < 2 ^ 64)
    (iv : Int) (ch : Choices) :
    stepFnIter 1 (sSU n sv tv l iv false)
      (.next (.storeK [.chain (hSliceH n) [.int ((i : Nat) : Int) .uint64]
          [.index]]
        [.int w .uint64] (.seqn #[]) ([] :: [] :: envSU) suStoreTail)) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) ([] :: [] :: envSU)
            suStoreTail),
          sSU n sv tv (l.set i w) iv false, ch) := by
  have hstore := storeTarget_slice_u64 (σ := sSU n sv tv l iv false)
    (a := ⟨5⟩) (off := 0) (len := n) (cap := n) (i := i) (n := n)
    (ik := .uint64) (l := l) (w := w) rfl (Nat.le_refl n) hi
    (by omega) hlen hl hw
  rw [Nat.zero_add] at hstore
  exact stepFnIter_one (stepFn_store_step hstore)

/-- Setup dispatch (later passes): store done → scope exits → the loop
head → `i := i + 1` → the exit test delivery. -/
private theorem hsegSU_d1_raw (n : Nat) (sv tv iv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 34 (sSU n sv tv l iv false)
      (.next (.storeK [] [] (.seqn #[]) ([] :: [] :: envSU)
        suStoreTail)) ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < ((n : Nat) : Int)))) suCmpK,
          sSU n sv tv l
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false, ch) := by
  with_unfolding_all rfl

/-- **The setup loop**, by induction on `n - i`: from the exit-test
delivery at counter `i`, backing `bsFamily i seed ++ zeros`, exactly
`57·(n-i)` steps reach the exit-test delivery at counter `n` with the
family fully materialized. The `hnowrap` hypothesis is what collapses
every store's uint64 normalization onto the mathematical family. -/
private theorem hsetup_loop (n seed : Nat) (tv : Int)
    (hn : n < 2 ^ 62) (hnw : seed + 2 * n < 2 ^ 64) :
    ∀ μ i, μ = n - i → i ≤ n → ∀ ch : Choices,
    stepFnIter (57 * (n - i))
      (sSU n (seed : Int) tv (bsFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false)
      (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
        suCmpK) ch
      = .ok (.retV (.bool (decide (((n : Nat) : Int) < ((n : Nat) : Int))))
            suCmpK,
          sSU n (seed : Int) tv (bsFamily n seed) ((n : Nat) : Int) false,
          ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro i hμ hin ch
    rcases Nat.lt_or_ge i n with hlt | hge
    · -- one more store
      rw [show (decide (((i : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by omega)]
      have h1 := hsegSU_body_raw n (seed : Int) tv ((i : Nat) : Int)
        (bsFamily i seed ++ List.replicate (n - i) 0) ch
      -- clean the stored value: seed + 2*i, no wrap
      have hmul : (2 : Int) * ((i : Nat) : Int) = ((2 * i : Nat) : Int) := by
        omega
      rw [hmul, unorm_of_range (by omega) (by omega : ((2 * i : Nat) : Int) < 2 ^ 64),
        show ((seed : Nat) : Int) + ((2 * i : Nat) : Int)
          = ((seed + 2 * i : Nat) : Int) from by omega,
        unorm_of_range (by omega)
          (by omega : ((seed + 2 * i : Nat) : Int) < 2 ^ 64)] at h1
      have h2 := hstep_store_setup n (seed : Int) tv
        (bsFamily i seed ++ List.replicate (n - i) 0) i
        ((seed + 2 * i : Nat) : Int) hlt
        (by rw [List.length_append, bsFamily_length, List.length_replicate]
            omega)
        (bsFamilyZ_range hnw (by omega))
        ⟨by omega, by omega⟩ ((i : Nat) : Int) ch
      rw [bsFamily_set hlt] at h2
      have h3 := hsegSU_d1_raw n (seed : Int) tv ((i : Nat) : Int)
        (bsFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0) ch
      rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
        unorm_of_range (by omega) (by omega : ((i + 1 : Nat) : Int) < 2 ^ 64),
        unorm_of_range (by omega)
          (by omega : ((i + 1 : Nat) : Int) < 2 ^ 64)] at h3
      have hrec := ih (n - (i + 1)) (by omega) (i + 1) rfl (by omega) ch
      have hc := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h1 h2)
        h3) hrec
      rw [show 22 + 1 + 34 + 57 * (n - (i + 1)) = 57 * (n - i) from by
        omega] at hc
      exact hc
    · -- i = n: zero further steps
      have hEq : i = n := by omega
      subst hEq
      simp only [Nat.sub_self, Nat.mul_zero, List.replicate_zero,
        List.append_nil]
      rfl

/-! ## The subject phase at the harness placement

The `search` frame inside the harness run: the committed canonical
segments re-derived at the harness address layout (subject cells
9–15, `mid` garbage from 16) with the harness continuation below the
subject frame (the committed forms sit above with `.stop`; the frame
exit here continues into `$res0 = $c7; return`). -/

private def envH2C7 : LocalEnv :=
  [[("$c7", .base ⟨9⟩), ("s", .base ⟨6⟩), ("$c6", .base ⟨4⟩)], hScope0]
/-- The harness tail below the subject frame. -/
private def hRetK : Cont := .seq [stmtRetRes] envH2C7 hFrame0
/-- The subject's frame continuation (targets `$c7`, pinned result at
12, the harness tail below). -/
private def hFrameK : Cont :=
  .frame [(.chain [], [.ref "$c7"])] envH2C7 [.base ⟨12⟩] [] hRetK false

private def hEnvArgs : LocalEnv :=
  [[("$res0", .base ⟨12⟩), ("target", .base ⟨11⟩), ("s", .base ⟨10⟩)]]
private def hEnvMid2 : LocalEnv :=
  [("hi", .base ⟨14⟩), ("lo", .base ⟨13⟩)] :: hEnvArgs
private def hEnvIn : LocalEnv := [("$forFirst", .base ⟨15⟩)] :: hEnvMid2

private def hHeadTail : Cont :=
  .seq [] hEnvIn (.seq [postIf, tailSeqn] hEnvMid2 hFrameK)
/-- The subject loop-head configuration (harness placement). -/
private def hHeadCfg : Config :=
  .exec (.while (.boolLit true) searchWhileBody) hEnvIn hHeadTail
private def hLoopK : Cont :=
  .loop (.boolLit true) searchWhileBody hEnvIn hHeadTail
/-- The subject exit test's delivery continuation. -/
private def hCmpCont : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: hEnvIn)
    (.seq [midBlock] ([] :: hEnvIn) hLoopK)
private def hEnvIter : LocalEnv := [] :: [] :: hEnvIn
private def hEnvMidd (na : Nat) : LocalEnv :=
  [("mid", .base ⟨na⟩)] :: [] :: hEnvIn
private def hIterK : Cont := .seq [] ([] :: hEnvIn) hLoopK

/-- The subject-phase state family at the harness placement: the nine
harness cells (0–8, inert during the subject phase — the setup counter
rests at `n`), the call-result cell `$c7` at 9 (`r0`), the subject
frame (handle 10, target 11, `$res0` 12 = `res`, `lo` 13, `hi` 14,
`$forFirst` 15), the dead-`mid` garbage suffix `g`, allocator `na`.
`h3` is the harness `$res0` (written only by the final tail). -/
private def hsP (n : Nat) (sv : Int) (xs : List Int)
    (t h3 r0 res lo hi : Int) (ff : Bool) (g : Heap) (na : Nat) :
    ExecState :=
  { types := searchLowered.typeDefs.toList,
    functions := searchLowered.funcs,
    methods := searchLowered.methods,
    heap := (.base ⟨0⟩, ucell (n : Int)) :: (.base ⟨1⟩, ucell sv)
      :: (.base ⟨2⟩, ucell t) :: (.base ⟨3⟩, icell h3)
      :: (.base ⟨4⟩, hHandleCell n) :: (.base ⟨5⟩, arrCell n xs)
      :: (.base ⟨6⟩, hHandleCell n) :: (.base ⟨7⟩, ucell (n : Int))
      :: (.base ⟨8⟩, bcell false) :: (.base ⟨9⟩, icell r0)
      :: (.base ⟨10⟩, hHandleCell n) :: (.base ⟨11⟩, ucell t)
      :: (.base ⟨12⟩, icell res) :: (.base ⟨13⟩, icell lo)
      :: (.base ⟨14⟩, icell hi) :: (.base ⟨15⟩, bcell ff) :: g,
    nextAddr := na }

/-! ### Heap plumbing at the harness placement -/

/-- Lookups above the sixteen fixed cells fall through to the
garbage. -/
private theorem lookup_hsP_high {n : Nat} {sv : Int} {xs : List Int}
    {t h3 r0 res lo hi : Int} {ff : Bool} {g : Heap} {na a : Nat}
    (ha : 16 ≤ a) :
    Heap.lookup (hsP n sv xs t h3 r0 res lo hi ff g na).heap (.base ⟨a⟩)
      = Heap.lookup g (.base ⟨a⟩) := by
  simp only [hsP, Heap.lookup,
    base_beq_false (show (0 : Nat) ≠ a by omega),
    base_beq_false (show (1 : Nat) ≠ a by omega),
    base_beq_false (show (2 : Nat) ≠ a by omega),
    base_beq_false (show (3 : Nat) ≠ a by omega),
    base_beq_false (show (4 : Nat) ≠ a by omega),
    base_beq_false (show (5 : Nat) ≠ a by omega),
    base_beq_false (show (6 : Nat) ≠ a by omega),
    base_beq_false (show (7 : Nat) ≠ a by omega),
    base_beq_false (show (8 : Nat) ≠ a by omega),
    base_beq_false (show (9 : Nat) ≠ a by omega),
    base_beq_false (show (10 : Nat) ≠ a by omega),
    base_beq_false (show (11 : Nat) ≠ a by omega),
    base_beq_false (show (12 : Nat) ≠ a by omega),
    base_beq_false (show (13 : Nat) ≠ a by omega),
    base_beq_false (show (14 : Nat) ≠ a by omega),
    base_beq_false (show (15 : Nat) ≠ a by omega),
    Bool.false_eq_true, if_false]

/-- Setting a cell above the sixteen fixed cells rewrites only the
garbage. -/
private theorem set_hsP_high {n : Nat} {sv : Int} {xs : List Int}
    {t h3 r0 res lo hi : Int} {ff : Bool} {g : Heap} {na a : Nat}
    (ha : 16 ≤ a) (c : HeapCell) :
    Heap.set (hsP n sv xs t h3 r0 res lo hi ff g na).heap (.base ⟨a⟩) c
      = (hsP n sv xs t h3 r0 res lo hi ff (Heap.set g (.base ⟨a⟩) c)
          na).heap := by
  simp only [hsP, Heap.set,
    base_beq_false (show (0 : Nat) ≠ a by omega),
    base_beq_false (show (1 : Nat) ≠ a by omega),
    base_beq_false (show (2 : Nat) ≠ a by omega),
    base_beq_false (show (3 : Nat) ≠ a by omega),
    base_beq_false (show (4 : Nat) ≠ a by omega),
    base_beq_false (show (5 : Nat) ≠ a by omega),
    base_beq_false (show (6 : Nat) ≠ a by omega),
    base_beq_false (show (7 : Nat) ≠ a by omega),
    base_beq_false (show (8 : Nat) ≠ a by omega),
    base_beq_false (show (9 : Nat) ≠ a by omega),
    base_beq_false (show (10 : Nat) ≠ a by omega),
    base_beq_false (show (11 : Nat) ≠ a by omega),
    base_beq_false (show (12 : Nat) ≠ a by omega),
    base_beq_false (show (13 : Nat) ≠ a by omega),
    base_beq_false (show (14 : Nat) ≠ a by omega),
    base_beq_false (show (15 : Nat) ≠ a by omega),
    Bool.false_eq_true, if_false]

/-- The backing-cell lookup (cell 5, any subject state). -/
private theorem lookup_hsP_backing {n : Nat} {sv : Int} {xs : List Int}
    {t h3 r0 res lo hi : Int} {ff : Bool} {g : Heap} {na : Nat} :
    Heap.lookup (hsP n sv xs t h3 r0 res lo hi ff g na).heap (.base ⟨5⟩)
      = some (arrCell n xs) := by
  simp [hsP, Heap.lookup]

/-- The harness result-cell lookup (cell 3, any subject state). -/
private theorem lookup_hsP_h3 {n : Nat} {sv : Int} {xs : List Int}
    {t h3 r0 res lo hi : Int} {ff : Bool} {g : Heap} {na : Nat} :
    Heap.lookup (hsP n sv xs t h3 r0 res lo hi ff g na).heap (.base ⟨3⟩)
      = some (icell h3) := by
  simp [hsP, Heap.lookup]

/-- The `mid` declaration's allocation step at the harness placement
(concrete configuration, symbolic state). -/
private theorem hstep_init_mid (σ : ExecState) (ch : Choices) :
    stepFn σ (.exec (.initialization { id := "mid", typ := .int .int })
        hEnvIter (.seq [midAssign, innerIf] hEnvIter hIterK)) ch
      = .ok (.next (.seq [midAssign, innerIf]
            (hEnvMidd σ.nextAddr) hIterK),
          { σ with
            heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
              ⟨some (.int .int), .int 0 .int⟩,
            nextAddr := σ.nextAddr + 1 }, ch) := by
  with_unfolding_all rfl

/-! ### Exit-to-subject segments (setup done → the subject loop head) -/

/-- `$c7` declared, the call's `s`/`t` operands read: the state at the
frame-entry point. -/
private def σCallArgs (n : Nat) (sv tv : Int) (l : List Int) : ExecState :=
  { types := searchLowered.typeDefs.toList,
    functions := searchLowered.funcs,
    methods := searchLowered.methods,
    heap := [(.base ⟨0⟩, ucell (n : Int)), (.base ⟨1⟩, ucell sv),
             (.base ⟨2⟩, ucell tv), (.base ⟨3⟩, icell 0),
             (.base ⟨4⟩, hHandleCell n), (.base ⟨5⟩, arrCell n l),
             (.base ⟨6⟩, hHandleCell n), (.base ⟨7⟩, ucell ((n : Nat) : Int)),
             (.base ⟨8⟩, bcell false), (.base ⟨9⟩, icell 0)],
    nextAddr := 10 }

/-- The subject frame entered (`s`/`target`/`$res0`/`lo`/`hi`
allocated at 10–14): the state at the `len(s)` apply point. `tq` is
the target cell's value — the frame entry writes
`IntKind.normalize .uint64 tv` there (segment X1's output); the
in-range hypothesis collapses it back onto `tv` before segment X2. -/
private def σHEntry (n : Nat) (sv tv tq : Int) (l : List Int) :
    ExecState :=
  { types := searchLowered.typeDefs.toList,
    functions := searchLowered.funcs,
    methods := searchLowered.methods,
    heap := [(.base ⟨0⟩, ucell (n : Int)), (.base ⟨1⟩, ucell sv),
             (.base ⟨2⟩, ucell tv), (.base ⟨3⟩, icell 0),
             (.base ⟨4⟩, hHandleCell n), (.base ⟨5⟩, arrCell n l),
             (.base ⟨6⟩, hHandleCell n), (.base ⟨7⟩, ucell ((n : Nat) : Int)),
             (.base ⟨8⟩, bcell false), (.base ⟨9⟩, icell 0),
             (.base ⟨10⟩, hHandleCell n),
             (.base ⟨11⟩, ucell tq),
             (.base ⟨12⟩, icell 0), (.base ⟨13⟩, icell 0),
             (.base ⟨14⟩, icell 0)],
    nextAddr := 15 }

private def hEntryTail : Cont :=
  .seq [ffBlock, postIf, tailSeqn] hEnvMid2 hFrameK
private def hEntryRhsK : Cont :=
  .rhsK .vals
    [.chain (.addr (.base ⟨13⟩)) [] [], .chain (.addr (.base ⟨14⟩)) [] []]
    [.int 0 .int] [] (.seqn #[]) hEnvMid2 hEntryTail

/-- Exit-to-subject A: setup test false → break unwinding → `$c7`
declaration → the call's operand reads → frame entry → `lo`/`hi`
declaration → the `len(s)` operand walk → the `lengthOf` apply point.
(The frame-entry step itself is definitional: parameter normalization
on a `.slice` value is the identity arm, and the target's uint64
re-normalization stays symbolic in the output state.) -/
private theorem hseg_X1_raw (n : Nat) (sv tv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 33
      (sSU n sv tv l ((n : Nat) : Int) false)
      (.retV (.bool false) suCmpK) ch
      = .ok (.retV (hSliceH n)
            (.strictK (.lengthOf (some (.slice (.int .uint64)))) [] []
              hEnvMid2 hEntryRhsK),
          σHEntry n sv tv (IntKind.normalize .uint64 tv) l, ch) := by
  with_unfolding_all rfl

/-- Exit-to-subject B: `lo, hi = 0, len(s)` stores, the `$forFirst`
block → the subject loop head at the harness placement (stated at the
CLEANED target — both target cells hold the same raw `t`). -/
private theorem hseg_X2_raw (n : Nat) (sv t : Int) (l : List Int)
    (hv : Int) (ch : Choices) :
    stepFnIter 19 (σHEntry n sv t t l) (.retV (.int hv .int) hEntryRhsK)
      ch
      = .ok (hHeadCfg,
          hsP n sv l t 0 0 0 0
            (IntKind.normalize .int hv) true [] 16, ch) := by
  with_unfolding_all rfl

/-! ### Subject dispatch/iteration/exit segments (harness placement) -/

/-- First-pass dispatch: the flag drops, then the exit test. -/
private theorem hseg_dispatch0_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 25 (hsP n sv xs t 0 0 0 lo hi true g na) hHeadCfg ch
      = .ok (.retV (.bool (decide (lo < hi))) hCmpCont,
          hsP n sv xs t 0 0 0 lo hi false g na, ch) := by
  with_unfolding_all rfl

/-- Later-pass dispatch (the flag is down). -/
private theorem hseg_dispatch1_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 18 (hsP n sv xs t 0 0 0 lo hi false g na) hHeadCfg ch
      = .ok (.retV (.bool (decide (lo < hi))) hCmpCont,
          hsP n sv xs t 0 0 0 lo hi false g na, ch) := by
  with_unfolding_all rfl

/-- Test true → the `mid` declaration (the per-iteration allocation
point). -/
private theorem hseg_iter1_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 7 (hsP n sv xs t 0 0 0 lo hi false g na)
      (.retV (.bool true) hCmpCont) ch
      = .ok (.exec (.initialization { id := "mid", typ := .int .int })
            hEnvIter (.seq [midAssign, innerIf] hEnvIter hIterK),
          hsP n sv xs t 0 0 0 lo hi false g na, ch) := by
  with_unfolding_all rfl

/-- The `mid` allocation, cleaned: the fresh cell APPENDS to the
garbage suffix. -/
private theorem hstep_alloc_mid (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (g : Heap) (na : Nat) (ch : Choices) (hna : 16 ≤ na)
    (hg : Heap.lookup g (.base ⟨na⟩) = none) :
    stepFnIter 1 (hsP n sv xs t 0 0 0 lo hi false g na)
      (.exec (.initialization { id := "mid", typ := .int .int })
        hEnvIter (.seq [midAssign, innerIf] hEnvIter hIterK)) ch
      = .ok (.next (.seq [midAssign, innerIf] (hEnvMidd na) hIterK),
          hsP n sv xs t 0 0 0 lo hi false (g ++ [(.base ⟨na⟩, icell 0)])
            (na + 1), ch) := by
  have h := hstep_init_mid (hsP n sv xs t 0 0 0 lo hi false g na) ch
  rw [show (hsP n sv xs t 0 0 0 lo hi false g na).nextAddr = na from rfl,
    set_hsP_high hna, set_fresh hg] at h
  exact stepFnIter_one h

/-- `mid = (lo + hi) / 2` → the store point. -/
private theorem hseg_iter2_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 14 (hsP n sv xs t 0 0 0 lo hi false G na')
      (.next (.seq [midAssign, innerIf] (hEnvMidd ma) hIterK)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨ma⟩)) [] []]
            [.int (IntKind.normalize .int
                (Int.tdiv (IntKind.normalize .int (lo + hi)) 2)) .int]
            (.seqn #[]) (hEnvMidd ma)
            (.seq [innerIf] (hEnvMidd ma) hIterK)),
          hsP n sv xs t 0 0 0 lo hi false G na', ch) := by
  with_unfolding_all rfl

/-- The `mid` store, cleaned: lands in the appended cell. -/
private theorem hstep_store_mid (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi w m : Int) (ik : IntKind) (g : Heap) (na' ma : Nat)
    (K : Cont) (ch : Choices) (hma : 16 ≤ ma)
    (hg : Heap.lookup g (.base ⟨ma⟩) = none) :
    stepFnIter 1
      (hsP n sv xs t 0 0 0 lo hi false (g ++ [(.base ⟨ma⟩, icell w)]) na')
      (.next (.storeK [.chain (.addr (.base ⟨ma⟩)) [] []] [.int m ik]
        (.seqn #[]) (hEnvMidd ma) K)) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (hEnvMidd ma) K),
          hsP n sv xs t 0 0 0 lo hi false
            (g ++ [(.base ⟨ma⟩, icell (IntKind.normalize .int m))]) na',
          ch) := by
  have hlook : Heap.lookup
      (hsP n sv xs t 0 0 0 lo hi false
        (g ++ [(.base ⟨ma⟩, icell w)]) na').heap
      (.base ⟨ma⟩) = some ⟨some (.int .int), .int w .int⟩ := by
    rw [lookup_hsP_high hma, lookup_append_of_none hg, lookup_singleton_self]
  have hstore := storeTarget_base_int (ik := ik) m hlook
  rw [set_hsP_high hma, set_append_of_none hg, set_singleton_self] at hstore
  exact stepFnIter_one (stepFn_store_step hstore)

/-- The continuation below the probe's `if` (harness placement). -/
private def hK1 (ma : Nat) : Cont := .seq [] (hEnvMidd ma) hIterK
/-- The probe dispatch's delivery continuation. -/
private def hInnerIfK (ma : Nat) : Cont :=
  .ifK thenBlk elseBlk (hEnvMidd ma) (hK1 ma)
private def hEnvPush (ma : Nat) : LocalEnv := [] :: hEnvMidd ma
private def hLoRhsK (ma : Nat) : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨13⟩)) [] []] [] [] (.seqn #[])
    (hEnvPush ma)
    (.seq [] (hEnvPush ma) (.seq [] (hEnvMidd ma) hIterK))
private def hHiRhsK (ma : Nat) : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨14⟩)) [] []] [] [] (.seqn #[])
    (hEnvPush ma)
    (.seq [] (hEnvPush ma) (.seq [] (hEnvMidd ma) hIterK))

/-- Store done → the empty-`seqn` splice point. -/
private theorem hseg_iter3a_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 1 (hsP n sv xs t 0 0 0 lo hi false G na')
      (.next (.storeK [] [] (.seqn #[]) (hEnvMidd ma)
        (.seq [innerIf] (hEnvMidd ma) hIterK))) ch
      = .ok (.exec (.seqn #[]) (hEnvMidd ma)
            (.seq [innerIf] (hEnvMidd ma) hIterK),
          hsP n sv xs t 0 0 0 lo hi false G na', ch) := by
  with_unfolding_all rfl

/-- Spliced → the probe read's `mid` operand (`s[mid]`). -/
private theorem hseg_iter3b_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 6 (hsP n sv xs t 0 0 0 lo hi false G na')
      (.next (.seq [innerIf] (hEnvMidd ma) hIterK)) ch
      = .ok (.evalE (.var "mid") (hEnvMidd ma)
            (.strictK .indexGet [hSliceH n] [] (hEnvMidd ma)
              (.strictK .lessCmp [] [.var "target"] (hEnvMidd ma)
                (hInnerIfK ma))),
          hsP n sv xs t 0 0 0 lo hi false G na', ch) := by
  with_unfolding_all rfl

/-- Store done → the probe read's `mid` operand, composed. -/
private theorem hseg_iter3 (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 8 (hsP n sv xs t 0 0 0 lo hi false G na')
      (.next (.storeK [] [] (.seqn #[]) (hEnvMidd ma)
        (.seq [innerIf] (hEnvMidd ma) hIterK))) ch
      = .ok (.evalE (.var "mid") (hEnvMidd ma)
            (.strictK .indexGet [hSliceH n] [] (hEnvMidd ma)
              (.strictK .lessCmp [] [.var "target"] (hEnvMidd ma)
                (hInnerIfK ma))),
          hsP n sv xs t 0 0 0 lo hi false G na', ch) :=
  stepFnIter_chain
    (stepFnIter_chain (hseg_iter3a_raw n sv xs t lo hi G na' ma ch)
      (stepFnIter_one stepFn_seqn_splice))
    (hseg_iter3b_raw n sv xs t lo hi G na' ma ch)

/-- A `mid` read, cleaned (symbolic cell address). -/
private theorem hstep_load_mid (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi mv : Int) (g : Heap) (na' ma : Nat) (env : LocalEnv)
    (K : Cont) (ch : Choices) (hma : 16 ≤ ma)
    (hg : Heap.lookup g (.base ⟨ma⟩) = none)
    (henv : LocalEnv.lookup env "mid" = some (.base ⟨ma⟩)) :
    stepFnIter 1
      (hsP n sv xs t 0 0 0 lo hi false (g ++ [(.base ⟨ma⟩, icell mv)]) na')
      (.evalE (.var "mid") env K) ch
      = .ok (.retV (.int mv .int) K,
          hsP n sv xs t 0 0 0 lo hi false
            (g ++ [(.base ⟨ma⟩, icell mv)]) na', ch) := by
  have hlook : Heap.lookup
      (hsP n sv xs t 0 0 0 lo hi false
        (g ++ [(.base ⟨ma⟩, icell mv)]) na').heap
      (.base ⟨ma⟩) = some (icell mv) := by
    rw [lookup_hsP_high hma, lookup_append_of_none hg, lookup_singleton_self]
  exact stepFnIter_one (stepFn_var henv hlook)

/-- Element delivered → the probe comparison's delivery. -/
private theorem hseg_iter4_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi wv : Int) (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 3 (hsP n sv xs t 0 0 0 lo hi false G na')
      (.retV (.int wv .uint64)
        (.strictK .lessCmp [] [.var "target"] (hEnvMidd ma)
          (hInnerIfK ma))) ch
      = .ok (.retV (.bool (decide (wv < t))) (hInnerIfK ma),
          hsP n sv xs t 0 0 0 lo hi false G na', ch) := by
  with_unfolding_all rfl

/-- Probe true → the then-block's `seqn` splice point. -/
private theorem hseg_iter5a1_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 3 (hsP n sv xs t 0 0 0 lo hi false G na')
      (.retV (.bool true) (hInnerIfK ma)) ch
      = .ok (.exec (.seqn #[.assign (.var "lo")
              (.add (.var "mid") (.intLit 1 .int))]) (hEnvPush ma)
            (.seq [] (hEnvPush ma) (hK1 ma)),
          hsP n sv xs t 0 0 0 lo hi false G na', ch) := by
  with_unfolding_all rfl

/-- Spliced → `lo = mid + 1`'s `mid` operand. -/
private theorem hseg_iter5a2_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 5 (hsP n sv xs t 0 0 0 lo hi false G na')
      (.next (.seq [.assign (.var "lo")
        (.add (.var "mid") (.intLit 1 .int))] (hEnvPush ma) (hK1 ma))) ch
      = .ok (.evalE (.var "mid") (hEnvPush ma)
            (.strictK .add [] [.intLit 1 .int] (hEnvPush ma)
              (hLoRhsK ma)),
          hsP n sv xs t 0 0 0 lo hi false G na', ch) := by
  with_unfolding_all rfl

/-- Probe true → `lo = mid + 1`'s `mid` operand, composed. -/
private theorem hseg_iter5a (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 9 (hsP n sv xs t 0 0 0 lo hi false G na')
      (.retV (.bool true) (hInnerIfK ma)) ch
      = .ok (.evalE (.var "mid") (hEnvPush ma)
            (.strictK .add [] [.intLit 1 .int] (hEnvPush ma)
              (hLoRhsK ma)),
          hsP n sv xs t 0 0 0 lo hi false G na', ch) :=
  stepFnIter_chain
    (stepFnIter_chain (hseg_iter5a1_raw n sv xs t lo hi G na' ma ch)
      (stepFnIter_one stepFn_seqn_splice))
    (hseg_iter5a2_raw n sv xs t lo hi G na' ma ch)

/-- `mid` delivered → `+ 1`, the `lo` store → the then-block's closing
splice point. -/
private theorem hseg_iter6a1_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi mv : Int) (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 6 (hsP n sv xs t 0 0 0 lo hi false G na')
      (.retV (.int mv .int)
        (.strictK .add [] [.intLit 1 .int] (hEnvPush ma)
          (hLoRhsK ma))) ch
      = .ok (.exec (.seqn #[]) (hEnvPush ma)
            (.seq [] (hEnvPush ma) (hK1 ma)),
          hsP n sv xs t 0 0 0
            (IntKind.normalize .int (IntKind.normalize .int (mv + 1))) hi
            false G na', ch) := by
  with_unfolding_all rfl

/-- Scope exits → the loop head (shared by both branches). -/
private theorem hseg_iter_tail_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 4 (hsP n sv xs t 0 0 0 lo hi false G na')
      (.next (.seq [] (hEnvPush ma) (hK1 ma))) ch
      = .ok (hHeadCfg, hsP n sv xs t 0 0 0 lo hi false G na', ch) := by
  with_unfolding_all rfl

/-- `mid` delivered → `+ 1`, the `lo` store, scope exits → the loop
head, composed. -/
private theorem hseg_iter6a (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi mv : Int) (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 11 (hsP n sv xs t 0 0 0 lo hi false G na')
      (.retV (.int mv .int)
        (.strictK .add [] [.intLit 1 .int] (hEnvPush ma)
          (hLoRhsK ma))) ch
      = .ok (hHeadCfg,
          hsP n sv xs t 0 0 0
            (IntKind.normalize .int (IntKind.normalize .int (mv + 1))) hi
            false G na', ch) :=
  stepFnIter_chain
    (stepFnIter_chain (hseg_iter6a1_raw n sv xs t lo hi mv G na' ma ch)
      (stepFnIter_one stepFn_seqn_splice))
    (hseg_iter_tail_raw n sv xs t
      (IntKind.normalize .int (IntKind.normalize .int (mv + 1))) hi
      G na' ma ch)

/-- Probe false → the else-block's `seqn` splice point. -/
private theorem hseg_iter5b1_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 3 (hsP n sv xs t 0 0 0 lo hi false G na')
      (.retV (.bool false) (hInnerIfK ma)) ch
      = .ok (.exec (.seqn #[.assign (.var "hi") (.var "mid")])
            (hEnvPush ma) (.seq [] (hEnvPush ma) (hK1 ma)),
          hsP n sv xs t 0 0 0 lo hi false G na', ch) := by
  with_unfolding_all rfl

/-- Spliced → `hi = mid`'s `mid` operand. -/
private theorem hseg_iter5b2_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 4 (hsP n sv xs t 0 0 0 lo hi false G na')
      (.next (.seq [.assign (.var "hi") (.var "mid")] (hEnvPush ma)
        (hK1 ma))) ch
      = .ok (.evalE (.var "mid") (hEnvPush ma) (hHiRhsK ma),
          hsP n sv xs t 0 0 0 lo hi false G na', ch) := by
  with_unfolding_all rfl

/-- Probe false → `hi = mid`'s `mid` operand, composed. -/
private theorem hseg_iter5b (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 8 (hsP n sv xs t 0 0 0 lo hi false G na')
      (.retV (.bool false) (hInnerIfK ma)) ch
      = .ok (.evalE (.var "mid") (hEnvPush ma) (hHiRhsK ma),
          hsP n sv xs t 0 0 0 lo hi false G na', ch) :=
  stepFnIter_chain
    (stepFnIter_chain (hseg_iter5b1_raw n sv xs t lo hi G na' ma ch)
      (stepFnIter_one stepFn_seqn_splice))
    (hseg_iter5b2_raw n sv xs t lo hi G na' ma ch)

/-- `mid` delivered → the `hi` store → the else-block's closing splice
point. -/
private theorem hseg_iter6b1_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi mv : Int) (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 3 (hsP n sv xs t 0 0 0 lo hi false G na')
      (.retV (.int mv .int) (hHiRhsK ma)) ch
      = .ok (.exec (.seqn #[]) (hEnvPush ma)
            (.seq [] (hEnvPush ma) (hK1 ma)),
          hsP n sv xs t 0 0 0 lo (IntKind.normalize .int mv) false G na',
          ch) := by
  with_unfolding_all rfl

/-- `mid` delivered → the `hi` store, scope exits → the loop head,
composed. -/
private theorem hseg_iter6b (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi mv : Int) (G : Heap) (na' ma : Nat) (ch : Choices) :
    stepFnIter 8 (hsP n sv xs t 0 0 0 lo hi false G na')
      (.retV (.int mv .int) (hHiRhsK ma)) ch
      = .ok (hHeadCfg,
          hsP n sv xs t 0 0 0 lo (IntKind.normalize .int mv) false G na',
          ch) :=
  stepFnIter_chain
    (stepFnIter_chain (hseg_iter6b1_raw n sv xs t lo hi mv G na' ma ch)
      (stepFnIter_one stepFn_seqn_splice))
    (hseg_iter_tail_raw n sv xs t lo (IntKind.normalize .int mv)
      G na' ma ch)

/-! ### Exit segments (the post-loop short-circuit guard, extended
through the harness tail `$c7`-store → `$res0 = $c7` → `return`) -/

/-- The post-loop `if`'s delivery continuation (harness placement). -/
private def hPostIfK : Cont :=
  .ifK foundBlk (.seqn #[]) hEnvMid2 (.seq [tailSeqn] hEnvMid2 hFrameK)
/-- The `&&`'s left-operand delivery continuation. -/
private def hPostAndK : Cont := .andK eqExpr hEnvMid2 hPostIfK

/-- Test false → break unwinding → the guard's `lo < len(s)` walk →
the `lengthOf` apply point. -/
private theorem hseg_exit1_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 13 (hsP n sv xs t 0 0 0 lo hi false g na)
      (.retV (.bool false) hCmpCont) ch
      = .ok (.retV (hSliceH n)
            (.strictK (.lengthOf (some (.slice (.int .uint64)))) [] []
              hEnvMid2
              (.strictK .lessCmp [.int lo .int] [] hEnvMid2 hPostAndK)),
          hsP n sv xs t 0 0 0 lo hi false g na, ch) := by
  with_unfolding_all rfl

/-- The `<` apply at the guard (pure). -/
private theorem hseg_exit2_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi lv nv : Int) (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 1 (hsP n sv xs t 0 0 0 lo hi false g na)
      (.retV (.int nv .int)
        (.strictK .lessCmp [.int lv .int] [] hEnvMid2 hPostAndK)) ch
      = .ok (.retV (.bool (decide (lv < nv))) hPostAndK,
          hsP n sv xs t 0 0 0 lo hi false g na, ch) := by
  with_unfolding_all rfl

/-- **The short-circuit, false arm** (`lo = len(s)`): the `&&`
delivers `false` WITHOUT evaluating `s[lo]`, the guard falls through,
`-1` returns through the subject frame INTO the harness tail — the
`$c7` store, `$res0 = $c7`, the harness `return` — to the driver
terminal. -/
private theorem hseg_exitEnd_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 38 (hsP n sv xs t 0 0 0 lo hi false g na)
      (.retV (.bool false) hPostAndK) ch
      = .ok (.next .stop,
          hsP n sv xs t (-1) (-1) (-1) lo hi false g na, ch) := by
  with_unfolding_all rfl

/-- The short-circuit, true arm: on into `s[lo] == target` — the `lo`
read up to the `indexGet` apply point. -/
private theorem hseg_exit3_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 6 (hsP n sv xs t 0 0 0 lo hi false g na)
      (.retV (.bool true) hPostAndK) ch
      = .ok (.retV (.int lo .int)
            (.strictK .indexGet [hSliceH n] [] hEnvMid2
              (.strictK (.eqCmp (.int .uint64)) [] [.var "target"]
                hEnvMid2 (.boolK hPostIfK))),
          hsP n sv xs t 0 0 0 lo hi false g na, ch) := by
  with_unfolding_all rfl

/-- Element delivered → the `==` delivery at the guard's `if`. -/
private theorem hseg_exit4_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi wv : Int) (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 4 (hsP n sv xs t 0 0 0 lo hi false g na)
      (.retV (.int wv .uint64)
        (.strictK (.eqCmp (.int .uint64)) [] [.var "target"] hEnvMid2
          (.boolK hPostIfK))) ch
      = .ok (.retV (.bool (wv == t)) hPostIfK,
          hsP n sv xs t 0 0 0 lo hi false g na, ch) := by
  with_unfolding_all rfl

/-- Hit: `$res0 = lo; return`, frame exit stores into `$c7`, the
harness tail runs to the driver terminal. The result value crosses
THREE normalizing stores (`$res0`, the `$c7` target write-back, the
harness `$res0`). -/
private theorem hseg_exitFound_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 38 (hsP n sv xs t 0 0 0 lo hi false g na)
      (.retV (.bool true) hPostIfK) ch
      = .ok (.next .stop,
          hsP n sv xs t
            (IntKind.normalize .int (IntKind.normalize .int
              (IntKind.normalize .int lo)))
            (IntKind.normalize .int (IntKind.normalize .int lo))
            (IntKind.normalize .int lo) lo hi false g na, ch) := by
  with_unfolding_all rfl

/-- In-bounds miss: fall through to `return -1`, through the harness
tail to the driver terminal. -/
private theorem hseg_exitMiss_raw (n : Nat) (sv : Int) (xs : List Int)
    (t lo hi : Int) (g : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 37 (hsP n sv xs t 0 0 0 lo hi false g na)
      (.retV (.bool false) hPostIfK) ch
      = .ok (.next .stop,
          hsP n sv xs t (-1) (-1) (-1) lo hi false g na, ch) := by
  with_unfolding_all rfl

/-! ## The subject inductions at the harness placement (the committed
canonical inductions, re-plumbed over the harness segments) -/

/-- **One iteration, cleaned** (harness placement): exit-test-true
delivery at interval `(lo, hi)` → the NEXT exit-test delivery, with
the interval strictly narrowed, the invariant re-established, and one
dead `mid` cell appended to the garbage. -/
private theorem hsearch_iter (sv : Int) (xs : List Int) (t : Int)
    (lo hi : Nat)
    (hsorted : Sorted xs) (hlen : xs.length < 2 ^ 62)
    (hlohi : lo < hi) (hhil : hi ≤ xs.length)
    (hlow : ∀ k, k < lo → xs.getD k 0 < t)
    (hhigh : ∀ k, hi ≤ k → k < xs.length → t ≤ xs.getD k 0)
    (g : Heap) (na : Nat) (hna : 16 ≤ na)
    (hg : ∀ a, na ≤ a → Heap.lookup g (.base ⟨a⟩) = none)
    (ch : Choices) :
    ∃ (k lo' hi' : Nat),
      k ≤ 75 ∧ lo ≤ lo' ∧ hi' ≤ hi ∧ hi' - lo' < hi - lo ∧ lo' ≤ hi' ∧
      (∀ j, j < lo' → xs.getD j 0 < t) ∧
      (∀ j, hi' ≤ j → j < xs.length → t ≤ xs.getD j 0) ∧
      stepFnIter k
        (hsP xs.length sv xs t 0 0 0 (lo : Int) (hi : Int) false g na)
        (.retV (.bool true) hCmpCont) ch
        = .ok (.retV (.bool (decide ((lo' : Int) < (hi' : Int)))) hCmpCont,
            hsP xs.length sv xs t 0 0 0 (lo' : Int) (hi' : Int) false
              (g ++ [(.base ⟨na⟩, icell (((lo + hi) / 2 : Nat) : Int))])
              (na + 1), ch) := by
  obtain ⟨mid, hmiddef⟩ : ∃ m, (lo + hi) / 2 = m := ⟨_, rfl⟩
  rw [hmiddef]
  have hmlo : lo ≤ mid :=
    hmiddef ▸ (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hmhi : mid < hi :=
    hmiddef ▸ (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
  have hmlen : mid < xs.length := by omega
  have hsum : lo + hi < 2 ^ 63 := by omega
  have hmid63 : mid < 2 ^ 63 := by omega
  -- to the mid declaration
  have h1 := hseg_iter1_raw xs.length sv xs t (lo : Int) (hi : Int) g na ch
  -- the allocation
  have h2 := hstep_alloc_mid xs.length sv xs t (lo : Int) (hi : Int) g na
    ch hna (hg na (Nat.le_refl na))
  -- the midpoint arithmetic
  have h3 := hseg_iter2_raw xs.length sv xs t (lo : Int) (hi : Int)
    (g ++ [(.base ⟨na⟩, icell 0)]) (na + 1) na ch
  rw [mid_clean hsum, hmiddef] at h3
  -- the mid store
  have h4 := hstep_store_mid xs.length sv xs t (lo : Int) (hi : Int) 0
    ((mid : Nat) : Int) .int g (na + 1) na
    (.seq [innerIf] (hEnvMidd na) hIterK) ch hna (hg na (Nat.le_refl na))
  rw [inorm_nat_of_lt hmid63] at h4
  -- to the probe read
  have h5 := hseg_iter3 xs.length sv xs t (lo : Int) (hi : Int)
    (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1) na ch
  -- the mid read at the index position
  have h6 := hstep_load_mid xs.length sv xs t (lo : Int) (hi : Int)
    ((mid : Nat) : Int) g (na + 1) na (hEnvMidd na)
    (.strictK .indexGet [hSliceH xs.length] [] (hEnvMidd na)
      (.strictK .lessCmp [] [.var "target"] (hEnvMidd na) (hInnerIfK na)))
    ch hna (hg na (Nat.le_refl na)) rfl
  -- the indexGet apply
  have hget : (⟨xs.map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + mid]? = some (.int (xs.getD mid 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega)]
  have h7 : stepFn
      (hsP xs.length sv xs t 0 0 0 (lo : Int) (hi : Int) false
        (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1))
      (.retV (.int (mid : Nat) .int)
        (.strictK .indexGet [hSliceH xs.length] [] (hEnvMidd na)
          (.strictK .lessCmp [] [.var "target"] (hEnvMidd na)
            (hInnerIfK na)))) ch
      = .ok (.retV (.int (xs.getD mid 0) .uint64)
          (.strictK .lessCmp [] [.var "target"] (hEnvMidd na)
            (hInnerIfK na)),
        hsP xs.length sv xs t 0 0 0 (lo : Int) (hi : Int) false
          (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1), ch) :=
    stepFn_strict_apply
      (applyStrictOp_indexGet_slice lookup_hsP_backing
        (Nat.le_refl xs.length) hmlen hget)
  -- to the probe delivery
  have h8 := hseg_iter4_raw xs.length sv xs t (lo : Int) (hi : Int)
    (xs.getD mid 0) (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1) na ch
  -- chain the shared prefix
  have hc2 := stepFnIter_chain h1 h2
  have hc3 := stepFnIter_chain hc2 h3
  have hc4 := stepFnIter_chain hc3 h4
  have hc5 := stepFnIter_chain hc4 h5
  have hc6 := stepFnIter_chain hc5 h6
  have hc7 := stepFnIter_chain hc6 (stepFnIter_one h7)
  have hpre8 := stepFnIter_chain hc7 h8
  -- branch on the probe
  rcases Int.lt_or_le (xs.getD mid 0) t with hprobe | hprobe
  · -- s[mid] < t: lo := mid + 1
    rw [show (decide (xs.getD mid 0 < t)) = true from decide_eq_true hprobe]
      at hpre8
    have h9 := hseg_iter5a xs.length sv xs t (lo : Int) (hi : Int)
      (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1) na ch
    have h10 := hstep_load_mid xs.length sv xs t (lo : Int) (hi : Int)
      ((mid : Nat) : Int) g (na + 1) na (hEnvPush na)
      (.strictK .add [] [.intLit 1 .int] (hEnvPush na) (hLoRhsK na)) ch hna
      (hg na (Nat.le_refl na)) rfl
    have h11 := hseg_iter6a xs.length sv xs t (lo : Int) (hi : Int)
      ((mid : Nat) : Int)
      (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1) na ch
    rw [show ((mid : Int) + 1) = ((mid + 1 : Nat) : Int) from by omega,
      inorm_nat_of_lt (by omega : mid + 1 < 2 ^ 63),
      inorm_nat_of_lt (by omega : mid + 1 < 2 ^ 63)] at h11
    have h12 := hseg_dispatch1_raw xs.length sv xs t
      ((mid + 1 : Nat) : Int) (hi : Int)
      (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1) ch
    have hc9 := stepFnIter_chain hpre8 h9
    have hc10 := stepFnIter_chain hc9 h10
    have hc11 := stepFnIter_chain hc10 h11
    have hc12 := stepFnIter_chain hc11 h12
    refine ⟨57 + 18, mid + 1, hi, by omega, by omega, Nat.le_refl _,
      by omega, by omega, inv_lo_step hsorted hprobe hmlen, hhigh, ?_⟩
    exact hc12
  · -- t ≤ s[mid]: hi := mid
    rw [show (decide (xs.getD mid 0 < t)) = false from
      decide_eq_false (by omega)] at hpre8
    have h9 := hseg_iter5b xs.length sv xs t (lo : Int) (hi : Int)
      (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1) na ch
    have h10 := hstep_load_mid xs.length sv xs t (lo : Int) (hi : Int)
      ((mid : Nat) : Int) g (na + 1) na (hEnvPush na) (hHiRhsK na) ch hna
      (hg na (Nat.le_refl na)) rfl
    have h11 := hseg_iter6b xs.length sv xs t (lo : Int) (hi : Int)
      ((mid : Nat) : Int)
      (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1) na ch
    rw [inorm_nat_of_lt hmid63] at h11
    have h12 := hseg_dispatch1_raw xs.length sv xs t (lo : Int)
      ((mid : Nat) : Int)
      (g ++ [(.base ⟨na⟩, icell (mid : Int))]) (na + 1) ch
    have hc9 := stepFnIter_chain hpre8 h9
    have hc10 := stepFnIter_chain hc9 h10
    have hc11 := stepFnIter_chain hc10 h11
    have hc12 := stepFnIter_chain hc11 h12
    refine ⟨53 + 18, lo, mid, by omega, Nat.le_refl _, by omega,
      by omega, by omega, hlow, inv_hi_step hsorted hprobe, ?_⟩
    exact hc12

/-- **The exit, cleaned** (harness placement): exit-test-false delivery
at `lo = hi = L` → the DRIVER terminal `.next .stop` through the
subject frame exit AND the harness tail, with `findSpec` pinned in the
harness result cell (`.base ⟨3⟩`) by the invariant. The `L = len` case
walks the `&&`'s short-circuit: `s[L]` is never read. -/
private theorem hsearch_exit (sv : Int) (xs : List Int) (t : Int) (L : Nat)
    (hsorted : Sorted xs) (hlen : xs.length < 2 ^ 62)
    (hL : L ≤ xs.length)
    (hlow : ∀ k, k < L → xs.getD k 0 < t)
    (hhigh : ∀ k, L ≤ k → k < xs.length → t ≤ xs.getD k 0)
    (g : Heap) (na : Nat) (ch : Choices) :
    ∃ (k : Nat) (σf : ExecState),
      k ≤ 64 ∧
      stepFnIter k
        (hsP xs.length sv xs t 0 0 0 (L : Int) (L : Int) false g na)
        (.retV (.bool false) hCmpCont) ch
        = .ok (.next .stop, σf, ch)
      ∧ Heap.lookup σf.heap (.base ⟨3⟩) = some (icell (findSpec xs t)) := by
  have h1 := hseg_exit1_raw xs.length sv xs t (L : Int) (L : Int) g na ch
  have h2 : stepFn
      (hsP xs.length sv xs t 0 0 0 (L : Int) (L : Int) false g na)
      (.retV (hSliceH xs.length)
        (.strictK (.lengthOf (some (.slice (.int .uint64)))) [] [] hEnvMid2
          (.strictK .lessCmp [.int (L : Int) .int] [] hEnvMid2
            hPostAndK))) ch
      = .ok (.retV (.int (xs.length : Nat) .int)
          (.strictK .lessCmp [.int (L : Int) .int] [] hEnvMid2 hPostAndK),
        hsP xs.length sv xs t 0 0 0 (L : Int) (L : Int) false g na, ch) :=
    stepFn_strict_apply (applyStrictOp_len_slice (Nat.le_refl xs.length))
  have h3 := hseg_exit2_raw xs.length sv xs t (L : Int) (L : Int) (L : Int)
    ((xs.length : Nat) : Int) g na ch
  have hpre := stepFnIter_chain (stepFnIter_chain h1 (stepFnIter_one h2)) h3
  rcases Nat.lt_or_ge L xs.length with hLn | hLn
  · -- in bounds: the `&&` proceeds into `s[L] == target`
    rw [show (decide ((L : Int) < ((xs.length : Nat) : Int))) = true from
      decide_eq_true (by omega)] at hpre
    have h4 := hseg_exit3_raw xs.length sv xs t (L : Int) (L : Int) g na ch
    have hget : (⟨xs.map (fun v => .int v .uint64)⟩ :
        Array GoValue)[0 + L]? = some (.int (xs.getD L 0) .uint64) := by
      rw [Nat.zero_add, getElem?_mapU _ _ (by omega)]
    have h5 : stepFn
        (hsP xs.length sv xs t 0 0 0 (L : Int) (L : Int) false g na)
        (.retV (.int (L : Nat) .int)
          (.strictK .indexGet [hSliceH xs.length] [] hEnvMid2
            (.strictK (.eqCmp (.int .uint64)) [] [.var "target"] hEnvMid2
              (.boolK hPostIfK)))) ch
        = .ok (.retV (.int (xs.getD L 0) .uint64)
            (.strictK (.eqCmp (.int .uint64)) [] [.var "target"] hEnvMid2
              (.boolK hPostIfK)),
          hsP xs.length sv xs t 0 0 0 (L : Int) (L : Int) false g na,
          ch) :=
      stepFn_strict_apply
        (applyStrictOp_indexGet_slice lookup_hsP_backing
          (Nat.le_refl xs.length) hLn hget)
    have h6 := hseg_exit4_raw xs.length sv xs t (L : Int) (L : Int)
      (xs.getD L 0) g na ch
    have hpre6 := stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain hpre h4) (stepFnIter_one h5)) h6
    by_cases heq : xs.getD L 0 = t
    · -- found
      rw [show (xs.getD L 0 == t) = true from beq_iff_eq.mpr heq] at hpre6
      have h7 := hseg_exitFound_raw xs.length sv xs t (L : Int) (L : Int)
        g na ch
      rw [inorm_nat_of_lt (by omega : L < 2 ^ 63),
        inorm_nat_of_lt (by omega : L < 2 ^ 63),
        inorm_nat_of_lt (by omega : L < 2 ^ 63)] at h7
      refine ⟨15 + 6 + 1 + 4 + 38, _, by omega,
        stepFnIter_chain hpre6 h7, ?_⟩
      rw [findSpec_found hLn heq hlow]
      exact lookup_hsP_h3
    · -- in-bounds miss
      rw [show (xs.getD L 0 == t) = false from beq_false_of_ne heq] at hpre6
      have h7 := hseg_exitMiss_raw xs.length sv xs t (L : Int) (L : Int)
        g na ch
      refine ⟨15 + 6 + 1 + 4 + 37, _, by omega,
        stepFnIter_chain hpre6 h7, ?_⟩
      rw [findSpec_miss_inbounds hsorted hLn heq hlow hhigh]
      exact lookup_hsP_h3
  · -- L = len: the short-circuit — `s[L]` is never read
    rw [show (decide ((L : Int) < ((xs.length : Nat) : Int))) = false from
      decide_eq_false (by omega)] at hpre
    have h4 := hseg_exitEnd_raw xs.length sv xs t (L : Int) (L : Int) g na
      ch
    refine ⟨15 + 38, _, by omega, stepFnIter_chain hpre h4, ?_⟩
    rw [findSpec_miss_end (fun k hk => hlow k (by omega))]
    exact lookup_hsP_h3

/-- **The subject loop at the harness placement**, by strong induction
on the interval width: from the exit-test delivery, the run reaches the
DRIVER terminal within `75μ + 64` steps with `findSpec` in the harness
result cell. -/
private theorem hsearch_loop (sv : Int) (xs : List Int) (t : Int)
    (hsorted : Sorted xs) (hlen : xs.length < 2 ^ 62) :
    ∀ μ lo hi, μ = hi - lo → lo ≤ hi → hi ≤ xs.length →
    (∀ k, k < lo → xs.getD k 0 < t) →
    (∀ k, hi ≤ k → k < xs.length → t ≤ xs.getD k 0) →
    ∀ g na, 16 ≤ na → (∀ a, na ≤ a → Heap.lookup g (.base ⟨a⟩) = none) →
    ∀ ch : Choices, ∃ (k : Nat) (σf : ExecState),
      k ≤ 75 * μ + 64 ∧
      stepFnIter k
        (hsP xs.length sv xs t 0 0 0 (lo : Int) (hi : Int) false g na)
        (.retV (.bool (decide ((lo : Int) < (hi : Int)))) hCmpCont) ch
        = .ok (.next .stop, σf, ch)
      ∧ Heap.lookup σf.heap (.base ⟨3⟩) = some (icell (findSpec xs t)) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro lo hi hμ hlohi hhil hlow hhigh g na hna hg ch
    rcases Nat.lt_or_ge lo hi with hlt | hge
    · -- iterate
      rw [show (decide ((lo : Int) < (hi : Int))) = true from
        decide_eq_true (by omega)]
      obtain ⟨k₁, lo', hi', hk₁, hlo', hhi', hdec, hle', hlow', hhigh',
        hrun₁⟩ := hsearch_iter sv xs t lo hi hsorted hlen hlt hhil hlow
          hhigh g na hna hg ch
      have hg' : ∀ a, na + 1 ≤ a →
          Heap.lookup (g ++ [(.base ⟨na⟩,
            icell (((lo + hi) / 2 : Nat) : Int))]) (.base ⟨a⟩) = none := by
        intro a ha
        rw [lookup_append_of_none (hg a (by omega)),
          lookup_single_none (by omega)]
      obtain ⟨k₂, σf, hk₂, hrun₂, hres⟩ := ih (hi' - lo') (by omega)
        lo' hi' rfl hle' (by omega) hlow' hhigh'
        (g ++ [(.base ⟨na⟩, icell (((lo + hi) / 2 : Nat) : Int))]) (na + 1)
        (by omega) hg' ch
      exact ⟨k₁ + k₂, σf, by omega, stepFnIter_chain hrun₁ hrun₂, hres⟩
    · -- exit: lo = hi
      have hEq : lo = hi := by omega
      subst hEq
      rw [show (decide ((lo : Int) < (lo : Int))) = false from
        decide_eq_false (by omega)]
      obtain ⟨k, σf, hk, hrun, hres⟩ := hsearch_exit sv xs t lo hsorted
        hlen (by omega) hlow (fun j hj hjn => hhigh j (by omega) hjn) g na
        ch
      exact ⟨k, σf, by omega, hrun, hres⟩

/-! ## The harness run, end to end, and THE HEADLINE -/

/-- **The harness run, end to end**: from the cleaned start state the
whole three-phase run — setup loop, `search`, result plumbing —
reaches the driver terminal within `220 + 132·n` steps with
`findSpec (bsFamily n seed) t` in the harness result cell. -/
private theorem hsearch_runs (n seed : Nat) (t : Int)
    (hn : n < 2 ^ 62) (hnw : seed + 2 * n < 2 ^ 64)
    (ht : 0 ≤ t ∧ t < 2 ^ 64) (ch : Choices) :
    ∃ (k : Nat) (σf : ExecState), k ≤ 220 + 132 * n ∧
      stepFnIter k (σStart n seed t)
        (.exec searchHarnessFunc.body hEnv0 hFrame0) ch
        = .ok (.next .stop, σf, ch)
      ∧ Heap.lookup σf.heap (.base ⟨3⟩)
          = some (icell (findSpec (bsFamily n seed) t)) := by
  -- prelude: to the setup loop head
  have hA1 := hseg_A1_raw n seed t ch
  have hMS := stepFnIter_one (hstep_makeSlice n seed t ch)
  have hA2 := hseg_A2_raw n seed t ch
  -- setup dispatch + loop
  have hd0 := hsegSU_d0_raw n (seed : Int) t 0 (List.replicate n 0) ch
  have hloop := hsetup_loop n seed t hn hnw (n - 0) 0 rfl (by omega) ch
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hloop
  -- into the subject
  have hX1 := hseg_X1_raw n (seed : Int) t (bsFamily n seed) ch
  rw [unorm_of_range ht.1 ht.2] at hX1
  have happlyLen : applyStrictOp
      (σHEntry n (seed : Int) t t (bsFamily n seed))
      (.lengthOf (some (.slice (.int .uint64)))) [hSliceH n]
      = .ok (.int ((n : Nat) : Int) .int,
          σHEntry n (seed : Int) t t (bsFamily n seed)) :=
    applyStrictOp_len_slice (Nat.le_refl n)
  have hLen := stepFnIter_one
    (stepFn_strict_apply (done := []) (env := hEnvMid2) (k := hEntryRhsK)
      (ch := ch) happlyLen)
  have hX2 := hseg_X2_raw n (seed : Int) t (bsFamily n seed)
    ((n : Nat) : Int) ch
  rw [inorm_nat_of_lt (by omega : n < 2 ^ 63)] at hX2
  have hd0' := hseg_dispatch0_raw n (seed : Int) (bsFamily n seed) t
    0 ((n : Nat) : Int) [] 16 ch
  -- chain the prelude
  have hc1 := stepFnIter_chain hA1 hMS
  have hc2 := stepFnIter_chain hc1 hA2
  have hc3 := stepFnIter_chain hc2 hd0
  have hc4 := stepFnIter_chain hc3 hloop
  have hc5 := stepFnIter_chain hc4 hX1
  have hc6 := stepFnIter_chain hc5 hLen
  have hc7 := stepFnIter_chain hc6 hX2
  have hc8 := stepFnIter_chain hc7 hd0'
  -- the subject loop from (0, n)
  have hlen' : (bsFamily n seed).length < 2 ^ 62 := by
    rw [bsFamily_length]; omega
  obtain ⟨k, σf, hk, hrun, hres⟩ := hsearch_loop (seed : Int)
    (bsFamily n seed) t (bsFamily_sorted n seed) hlen'
    (bsFamily n seed).length 0 (bsFamily n seed).length
    (by omega) (by omega) (Nat.le_refl _)
    (fun k hk => absurd hk (by omega))
    (fun k hk hk' => absurd (Nat.lt_of_le_of_lt hk hk') (by omega))
    [] 16 (by omega) (fun a _ => rfl) ch
  rw [bsFamily_length] at hrun hk
  refine ⟨(10 + 1 + 42 + 25 + 57 * (n - 0) + 33 + 1 + 19 + 25) + k, σf,
    by omega, ?_, hres⟩
  exact stepFnIter_chain hc8 hrun

/-- **THE HEADLINE** (harness form, ruling 2026-08-13, design note
§11): the fixed three-phase Go harness `search_harness(n, seed, t)` —
setup materializes the sorted family `s[i] = seed + 2*i`, the call
under test is `search(s, t)`, the returned index is the observable —
observed ONLY through the machine's native function entry
`runFunctionWithContextM`, terminates past one fuel bound at EVERY
nondeterminism-choice stream and returns EXACTLY
`findSpec (bsFamily n seed) t`: the index of the first occurrence of
`t` in the family, or `-1`.

Hypotheses, honestly: `hn : n < 2^62` is the SUBJECT's own domain —
the Bloch midpoint-overflow bound (`mid := (lo+hi)/2` computes
`lo + hi` in Go `int`, which can reach `2^63` and wrap negative at
lengths ≥ 2^62; the bound is the program's arithmetic domain,
unchanged by the harness). `hnowrap` makes the setup family genuinely
sorted (no uint64 wrap, so the machine's stores agree with the
mathematical `bsFamily`); `ht` is the target's uint64 range. The raw
target parameter covers found, in-range miss (the family has gaps)
and past-the-end miss — the proof walks Go's short-circuit `&&` on
the last.

Input-family honesty (§11): the scalar-parameterized setup gives the
`bsFamily` input FAMILY, honestly weaker than ∀-slice-contents; the
proof-side `search_framed` carries the ∀xs memory-quantified form.

Fuel: linear — `220 + 132·n` (57·n setup + 75·n subject + constant
plumbing). -/
theorem search_ok (n seed : Nat) (t : Int)
    (hn : n < 2 ^ 62) (hnowrap : seed + 2 * n < 2 ^ 64)
    (ht : 0 ≤ t ∧ t < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel searchLowered.typeDefs.toList
          searchLowered.funcs searchHarnessFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
            .int t .uint64]
          searchLowered.methods ch
        = .ok { values := #[.int (findSpec (bsFamily n seed) t) .int] } := by
  refine ⟨220 + 132 * n, fun fuel hfuel ch => ?_⟩
  obtain ⟨k, σf, hk, hrun, hres⟩ := hsearch_runs n seed t hn hnowrap ht ch
  rw [harness_entry_eq]
  have hσ0 : σH0 ((n : Nat) : Int) ((seed : Nat) : Int) t
      = σStart n seed t := by
    simp only [σH0, σStart, ucellU, ucell,
      unorm_of_range (by omega : (0 : Int) ≤ ((n : Nat) : Int))
        (by omega : ((n : Nat) : Int) < 2 ^ 64),
      unorm_of_range (by omega : (0 : Int) ≤ ((seed : Nat) : Int))
        (by omega : ((seed : Nat) : Int) < 2 ^ 64),
      unorm_of_range ht.1 ht.2]
  rw [hσ0]
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  simp only [hFrame0] at hfold
  rw [hfold, runConfig_next_stop]
  have hload : loadMany σf [.base ⟨3⟩]
      = .ok [.int (findSpec (bsFamily n seed) t) .int] := by
    simp only [loadMany, loadLoc, hres]
    rfl
  simp only [Bind.bind, Except.bind, hload]
  rfl

end GoLean.Examples.BinSearch
