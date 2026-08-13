import GoLeanProofs.Examples.ReverseProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId

/-!
# Verified example: in-place slice reversal (verified-examples slice 2b,
2026-08-13)

The §9e memory-input exemplar (design note
`docs/2026-08-12_example-spec-form.md` §9): the Go program is the
canonical corpus source `Corpus/coverage/exec/examples/reverse/main.go`
(5/5 differentially green against `go run`); `reverseLowered` is its
pinned frontend lowering (`scripts/check-golden`, both links).

The user-facing statement is `reverse_ok` — the §9e headline with the
completion split CLOSED: the executable frame theorem
(`docs/2026-08-13_executable-frame-theorem.md`; `Frame/`) landed, so
the ∃N completion clause holds at EVERY admissible framed placement,
transferred from the canonical run — nothing is re-run at a framed
placement. Statement deltas against the §9e block, both recorded
honestly in the docstring of `reverse_ok`:

* `hlen : xs.length < 2 ^ 63` was ADDED. §9e was drafted with the
  completion clause split off; with completion IN the statement the
  driver's slice expression `(&arr)[0:len]` evaluates `len` as a Go
  `int` literal, and a length at or beyond `2^63` wraps NEGATIVE and
  panics the bounds check — the claim as drafted is FALSE there. The
  bound is Go's own `int` domain, not a proof-method limit.
* The ∀-placement (`base`) quantifier is realized by the GENERALIZED
  renaming of the frame theorem (any `ShiftSpec` injection — build
  handoff §3 finding 1): the canonical run at `base = 0` transfers
  through `ρ := fun x => if x = 0 then base else na + (x - 1)`, which
  RELOCATES the input cell. No base-symbolic segment is ever run.

**Proof-route decision (recorded, per the arc instructions)**: the
whole proof is DIRECT MACHINE-STEP SEGMENT reasoning (the fib
termination style), not an Iris WP walk. The §9e slice-index WP laws
exist and are witnessed (`Laws/Slice.lean`); reverse itself does not
consume them, because the segment route delivers the value half and
the completion half from ONE induction (the segments pin the exact
loop-head state, array contents included), where the WP route would
add a second, separate walk for the value half alone. The shared
discharge layer (`SliceMem`) is the same for both routes, so nothing
is duplicated.

Scope honesty (the charter's two-questions separation): usability
evidence only — the reasoning layer carrying a natural memory-input
spec through a real program — never machine-hardening evidence.
-/

namespace GoLean.Examples.Reverse

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-! ## The program-side statement vocabulary -/

/-- The swap block: `{ s[i], s[j] = s[j], s[i] }`. -/
abbrev revSwapBlock : Stmt :=
  .block
    #[]
    #[.seqn
        #[.assignMany
            #[.addr (.indexAddr (.var "s") (.var "i")),
              .addr (.indexAddr (.var "s") (.var "j"))]
            #[.indexGet (.var "s") (.var "j"),
              .indexGet (.var "s") (.var "i")]]]

/-- The frontend's `for`-desugar body: the `$forFirst` dispatch (post
statement `i, j = i+1, j-1` on later passes), the exit test ending in
`break`, the swap block. -/
abbrev revWhileBody : Stmt :=
  .block
    #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.seqn
          #[.assignMany
              #[.var "i", .var "j"]
              #[.add (.var "i") (.intLit 1 .int),
                .sub (.var "j") (.intLit 1 .int)]]),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "j"))
        (.seqn #[])
        .breakStmt,
      revSwapBlock]

/-- The subject's `Func` record, verbatim from the pinned lowering (the
`example` pin below ties it by `rfl`). -/
def reverseFunc : Func :=
  { id := { key := "reverse" },
    args := #[{ id := "s", typ := .slice (.int .uint64) }],
    results := #[],
    body := .block
      #[]
      #[.block
          #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .int },
                .initialization { id := "j", typ := .int .int },
                .assignMany
                  #[.var "i", .var "j"]
                  #[.intLit 0 .int,
                    .sub (.length (.var "s") (some (.slice (.int .uint64))))
                      (.intLit 1 .int)]],
            .block
              #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) revWhileBody]]],
    variadic := false,
    wrapper := false }

/-- The lowering pin: the proof subject IS the frontend's lowering. -/
example : findFunctionIn? reverseLowered.funcs ⟨"reverse"⟩ = some reverseFunc :=
  rfl

/-- The driver: `reverse(s)` with the slice handle over the backing
array at `base` as the literal argument — the §9e
argument-as-quantifier convention lifted to a memory-backed value: a
slice expression over a `locLit` pointer-to-array base yields the
handle via `sliceFromArray`. -/
def reverseCall (xs : List Int) (base : Nat) : Stmt :=
  .call #[] ⟨"reverse"⟩
    #[.slice (.locLit (.base ⟨base⟩)) (.intLit 0 .int)
        (.intLit xs.length .int) none]

/-- The framed seed: the input's backing cell (`sliceCells`) at `base`,
an arbitrary frame `fr`, allocator at `na`. The canonical placement is
`reverseSeed xs 0 [] 1` — TIGHT (dom = {0}, na₀ = 1), as the frame
theorem's seed discharge requires. -/
def reverseSeed (xs : List Int) (base : Nat) (fr : Heap) (na : Nat) :
    ExecState :=
  { types := reverseLowered.typeDefs.toList,
    functions := reverseLowered.funcs,
    methods := reverseLowered.methods,
    heap := sliceCells xs base ++ fr, nextAddr := na }

/-! ## The pure surgery layer: the two-pointer partial reversal -/

/-- The list after `m` two-pointer swap iterations: positions below `m`
and at or above `length - m` hold the REVERSED elements; the middle is
still the original. -/
private def revSwap (xs : List Int) (m : Nat) : List Int :=
  (List.range xs.length).map fun k =>
    if k < m ∨ xs.length - m ≤ k then xs.getD (xs.length - 1 - k) 0
    else xs.getD k 0

private theorem length_revSwap (xs : List Int) (m : Nat) :
    (revSwap xs m).length = xs.length := by
  simp [revSwap]

private theorem getElem?_revSwap (xs : List Int) (m k : Nat)
    (hk : k < xs.length) :
    (revSwap xs m)[k]? =
      some (if k < m ∨ xs.length - m ≤ k then xs.getD (xs.length - 1 - k) 0
        else xs.getD k 0) := by
  simp [revSwap, List.getElem?_map, List.getElem?_range, hk]

private theorem getD_revSwap (xs : List Int) (m k : Nat)
    (hk : k < xs.length) :
    (revSwap xs m).getD k 0 =
      if k < m ∨ xs.length - m ≤ k then xs.getD (xs.length - 1 - k) 0
      else xs.getD k 0 := by
  simp [List.getD, getElem?_revSwap xs m k hk]

private theorem revSwap_zero (xs : List Int) : revSwap xs 0 = xs := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < xs.length
  · rw [getElem?_revSwap xs 0 k hk, if_neg (by omega),
      List.getElem?_eq_getElem hk]
    simp [List.getD, List.getElem?_eq_getElem hk]
  · rw [List.getElem?_eq_none (by simp [length_revSwap]; omega),
      List.getElem?_eq_none (by omega)]

/-- Every element of the partial reversal is an element of the input
(the range hypotheses transport). -/
private theorem mem_revSwap {xs : List Int} {m : Nat} {v : Int}
    (h : v ∈ revSwap xs m) : v ∈ xs := by
  simp only [revSwap, List.mem_map, List.mem_range] at h
  obtain ⟨k, hk, hv⟩ := h
  have hget : ∀ j, j < xs.length → xs.getD j 0 ∈ xs := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  split at hv
  · exact hv ▸ hget _ (by omega)
  · exact hv ▸ hget _ hk

/-- The untouched middle: while `m < length - 1 - m`, positions `m` and
`length - 1 - m` still hold the ORIGINAL elements. -/
private theorem getD_revSwap_lo {xs : List Int} {m : Nat}
    (h : 2 * m + 1 < xs.length) :
    (revSwap xs m).getD m 0 = xs.getD m 0 := by
  rw [getD_revSwap xs m m (by omega), if_neg (by omega)]

private theorem getD_revSwap_hi {xs : List Int} {m : Nat}
    (h : 2 * m + 1 < xs.length) :
    (revSwap xs m).getD (xs.length - 1 - m) 0
      = xs.getD (xs.length - 1 - m) 0 := by
  rw [getD_revSwap xs m _ (by omega), if_neg (by omega)]

/-- **One machine swap advances the partial reversal**: setting position
`m` to the (still-original) element at `length - 1 - m` and vice versa
is exactly `revSwap` at `m + 1`. -/
private theorem revSwap_step {xs : List Int} {m : Nat}
    (h : 2 * m + 1 < xs.length) :
    ((revSwap xs m).set m (xs.getD (xs.length - 1 - m) 0)).set
        (xs.length - 1 - m) (xs.getD m 0)
      = revSwap xs (m + 1) := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < xs.length
  · rw [List.getElem?_set, List.getElem?_set]
    simp only [List.length_set, length_revSwap]
    rw [getElem?_revSwap xs (m + 1) k hk]
    by_cases hkj : xs.length - 1 - m = k
    · rw [if_pos hkj]
      rw [if_pos (by omega : xs.length - 1 - m < xs.length)]
      rw [if_pos (by omega : k < m + 1 ∨ xs.length - (m + 1) ≤ k)]
      congr 2
      omega
    · rw [if_neg hkj]
      by_cases hki : m = k
      · rw [if_pos hki, if_pos (by omega), if_pos (by omega)]
        congr 2
        omega
      · rw [if_neg hki, getElem?_revSwap xs m k hk]
        congr 1
        by_cases hcond : k < m ∨ xs.length - m ≤ k
        · rw [if_pos hcond, if_pos (by omega)]
        · rw [if_neg hcond, if_neg (by omega)]
  · rw [List.getElem?_eq_none (by simp [length_revSwap]; omega),
      List.getElem?_eq_none (by simp [length_revSwap]; omega)]

/-- **At the exit test's failure the reversal is complete**: once
`length ≤ 2m + 1` (i.e. `i ≥ j`), the partial reversal IS the
reversal. -/
private theorem revSwap_reverse {xs : List Int} {m : Nat}
    (h : xs.length ≤ 2 * m + 1) :
    revSwap xs m = xs.reverse := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < xs.length
  · rw [getElem?_revSwap xs m k hk,
      List.getElem?_reverse (by omega),
      List.getElem?_eq_getElem (by omega : xs.length - 1 - k < xs.length)]
    by_cases hcond : k < m ∨ xs.length - m ≤ k
    · rw [if_pos hcond]
      simp [List.getD, List.getElem?_eq_getElem
        (by omega : xs.length - 1 - k < xs.length)]
    · rw [if_neg hcond]
      have hkm : xs.length - 1 - k = k := by omega
      simp only [hkm]
      simp [List.getD, List.getElem?_eq_getElem hk]
  · rw [List.getElem?_eq_none (by simp [length_revSwap]; omega),
      List.getElem?_eq_none (by simp; omega)]

/-! ## The machine layer: canonical-placement configurations

Transcribed from the machine (probe-verified against a concrete run;
every raw segment below re-checks the transcription by `rfl`).
Address layout at the canonical placement: 0 = the backing array,
1 = the parameter `s` (the handle), 2 = `i`, 3 = `j`, 4 = `$forFirst`;
allocator parked at 5 for the whole loop. -/

private abbrev intcell (v : Int) : HeapCell := ⟨some (.int .int), .int v .int⟩
private abbrev bcell (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
private abbrev arrCell (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n (.int .uint64)), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
private abbrev handleCell (n : Nat) : HeapCell :=
  ⟨some (.slice (.int .uint64)), .slice ⟨some (.base ⟨0⟩), 0, n, n⟩⟩
private abbrev sliceH (n : Nat) : GoValue :=
  .slice ⟨some (.base ⟨0⟩), 0, n, n⟩

private def envIn : LocalEnv :=
  [[("$forFirst", .base ⟨4⟩)],
   [("j", .base ⟨3⟩), ("i", .base ⟨2⟩)], [], [("s", .base ⟨1⟩)]]
private def envMid : LocalEnv :=
  [[("j", .base ⟨3⟩), ("i", .base ⟨2⟩)], [], [("s", .base ⟨1⟩)]]
private def envOut : LocalEnv := [[], [("s", .base ⟨1⟩)]]
private def envIn2 : LocalEnv := [] :: [] :: envIn

private def headTail : Cont :=
  .seq [] envIn (.seq [] envMid (.seq [] envOut (.frame [] [] [] [] .stop false)))
/-- The loop-head configuration. -/
private def revHeadCfg : Config :=
  .exec (.while (.boolLit true) revWhileBody) envIn headTail
private def loopK : Cont := .loop (.boolLit true) revWhileBody envIn headTail
/-- The exit test's delivery continuation (segment split point). -/
private def revCmpCont : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envIn)
    (.seq [revSwapBlock] ([] :: envIn) loopK)

private def swTail : Cont :=
  .seq [] envIn2 (.seq [] ([] :: envIn) loopK)
private def refv (n : Nat) (v : Int) : TargetRef :=
  .chain (sliceH n) [.int v .int] [.index]
private def rhsK1 (n : Nat) (iv jv : Int) : Cont :=
  .rhsK .vals [refv n iv, refv n jv] [] [.indexGet (.var "s") (.var "i")]
    (.seqn #[]) envIn2 swTail
private def rhsK2 (n : Nat) (iv jv : Int) (wj : GoValue) : Cont :=
  .rhsK .vals [refv n iv, refv n jv] [wj] [] (.seqn #[]) envIn2 swTail

/-- The in-loop state: backing list `l`, counters `iv`/`jv`, the
`$forFirst` flag. -/
private def revStateP (n : Nat) (l : List Int) (iv jv : Int) (ffv : Bool) :
    ExecState :=
  { types := reverseLowered.typeDefs.toList,
    functions := reverseLowered.funcs,
    methods := reverseLowered.methods,
    heap := [(.base ⟨0⟩, arrCell n l), (.base ⟨1⟩, handleCell n),
             (.base ⟨2⟩, intcell iv), (.base ⟨3⟩, intcell jv),
             (.base ⟨4⟩, bcell ffv)],
    nextAddr := 5 }

/-- The exit-test state after the dispatch of iteration `m`. -/
private def cmpState (xs : List Int) (m : Nat) : ExecState :=
  revStateP xs.length (revSwap xs m) (m : Nat)
    ((xs.length - 1 - m : Nat) : Int) false

/-! ## Generic single-step lemmas (the branchy steps' glue) -/

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

/-! ## Raw run segments (`with_unfolding_all rfl` — pure definitional
evaluation of the interpreter with the list content and counters
symbolic; the segments split exactly at the data-dependent branch
points: the two entry strict-applies, the exit test, the two
index reads, the two element stores). -/

private def entryK : Cont := .callArgsK ⟨"reverse"⟩ [] [] [] [] .stop

/-- Entry A: driver start → the slice-expression apply point. -/
private theorem rev_entryA_raw (xs : List Int) (ch : Choices) :
    stepFnIter 7 (reverseSeed xs 0 [] 1) (.exec (reverseCall xs 0) [] .stop) ch
      = .ok (.retV (.int (IntKind.normalize .int (xs.length : Int)) .int)
            (.strictK (.sliceExpr false) [.int 0 .int, .addr (.base ⟨0⟩)]
              [] [] entryK),
          reverseSeed xs 0 [] 1, ch) := by
  with_unfolding_all rfl

private def ffBlock : Stmt :=
  .block #[]
    #[.initialization { id := "$forFirst", typ := .bool },
      .assign (.var "$forFirst") (.boolLit true),
      .while (.boolLit true) revWhileBody]
private def entryTail : Cont :=
  .seq [ffBlock] envMid (.seq [] envOut (.frame [] [] [] [] .stop false))
private def entryRhsK : Cont :=
  .rhsK .vals
    [.chain (.addr (.base ⟨2⟩)) [] [], .chain (.addr (.base ⟨3⟩)) [] []]
    [.int 0 .int] [] (.seqn #[]) envMid entryTail

/-- The mid-entry state: frame entered, `i`/`j` allocated at defaults. -/
private def σEntry (xs : List Int) : ExecState :=
  { types := reverseLowered.typeDefs.toList,
    functions := reverseLowered.funcs,
    methods := reverseLowered.methods,
    heap := [(.base ⟨0⟩, arrCell xs.length xs),
             (.base ⟨1⟩, handleCell xs.length),
             (.base ⟨2⟩, intcell 0), (.base ⟨3⟩, intcell 0)],
    nextAddr := 4 }

/-- Entry B: frame entry, `i`/`j` declaration, `len(s)` operand walk →
the `lengthOf` apply point. -/
private theorem rev_entryB_raw (xs : List Int) (ch : Choices) :
    stepFnIter 21 (reverseSeed xs 0 [] 1)
      (.retV (sliceH xs.length) entryK) ch
      = .ok (.retV (sliceH xs.length)
            (.strictK (.lengthOf (some (.slice (.int .uint64)))) [] [] envMid
              (.strictK .sub [] [.intLit 1 .int] envMid entryRhsK)),
          σEntry xs, ch) := by
  with_unfolding_all rfl

/-- Entry C: `- 1`, the `i, j` stores, the `$forFirst` block → the loop
head. -/
private theorem rev_entryC_raw (xs : List Int) (ch : Choices) :
    stepFnIter 22 (σEntry xs)
      (.retV (.int ((xs.length : Nat) : Int) .int)
        (.strictK .sub [] [.intLit 1 .int] envMid entryRhsK)) ch
      = .ok (revHeadCfg,
          revStateP xs.length xs 0
            (IntKind.normalize .int
              (IntKind.normalize .int ((xs.length : Int) - 1))) true, ch) := by
  with_unfolding_all rfl

/-- First-pass dispatch: head with the flag up → the exit test (the
counters unchanged). -/
private theorem rev_segA0_raw (n : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 25 (revStateP n l iv jv true) revHeadCfg ch
      = .ok (.retV (.bool (decide (iv < jv))) revCmpCont,
          revStateP n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Later-pass dispatch: head with the flag down → `i, j = i+1, j-1`,
then the exit test. -/
private theorem rev_segA1_raw (n : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 40 (revStateP n l iv jv false) revHeadCfg ch
      = .ok (.retV (.bool (decide
              (IntKind.normalize .int (IntKind.normalize .int (iv + 1))
                < IntKind.normalize .int (IntKind.normalize .int (jv - 1)))))
            revCmpCont,
          revStateP n l
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            (IntKind.normalize .int (IntKind.normalize .int (jv - 1)))
            false, ch) := by
  with_unfolding_all rfl

/-- Swap phase 1a: test true → both targets' operands → the first
index-read apply point (`s[j]`). -/
private theorem rev_swapA_raw (n : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 20 (revStateP n l iv jv false) (.retV (.bool true) revCmpCont)
      ch
      = .ok (.retV (.int jv .int)
            (.strictK .indexGet [sliceH n] [] envIn2 (rhsK1 n iv jv)),
          revStateP n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase 1b: first element read delivered → the second index-read
apply point (`s[i]`). -/
private theorem rev_swapB_raw (n : Nat) (l : List Int) (iv jv : Int)
    (wj : GoValue) (ch : Choices) :
    stepFnIter 5 (revStateP n l iv jv false) (.retV wj (rhsK1 n iv jv)) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [sliceH n] [] envIn2 (rhsK2 n iv jv wj)),
          revStateP n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase 1 → 2: both reads done, the identity value source fires,
phase 2 begins. -/
private theorem rev_swapC_raw (n : Nat) (l : List Int) (iv jv : Int)
    (wj wi : GoValue) (ch : Choices) :
    stepFnIter 1 (revStateP n l iv jv false) (.retV wi (rhsK2 n iv jv wj)) ch
      = .ok (.next (.storeK [refv n iv, refv n jv] [wj, wi] (.seqn #[])
            envIn2 swTail),
          revStateP n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap tail: stores done → back to the loop head. -/
private theorem rev_swapD_raw (n : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 5 (revStateP n l iv jv false)
      (.next (.storeK [] [] (.seqn #[]) envIn2 swTail)) ch
      = .ok (revHeadCfg, revStateP n l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Exit: test false → break unwinding, frame exit, the driver
terminal. The state is untouched. -/
private theorem rev_exit_raw (n : Nat) (l : List Int) (iv jv : Int)
    (ch : Choices) :
    stepFnIter 8 (revStateP n l iv jv false) (.retV (.bool false) revCmpCont)
      ch
      = .ok (.next .stop, revStateP n l iv jv false, ch) := by
  with_unfolding_all rfl

/-! ## Cleaned segments and the loop induction -/

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

/-- The canonical seed's backing-cell lookup. -/
private theorem lookup_seed (xs : List Int) :
    Heap.lookup (reverseSeed xs 0 [] 1).heap (.base ⟨0⟩)
      = some ⟨some (.array xs.length (.int .uint64)),
          .array ⟨xs.map (fun v => .int v .uint64)⟩⟩ := by
  simp [reverseSeed, sliceCells, Heap.lookup]

private theorem lookup_state (n : Nat) (l : List Int) (iv jv : Int)
    (ffv : Bool) :
    Heap.lookup (revStateP n l iv jv ffv).heap (.base ⟨0⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [revStateP, Heap.lookup, arrCell]

/-- **The entry, cleaned**: seed → the loop head at iteration 0 within
52 steps (`hlen` cleans the wrapped `len(s) - 1`). -/
private theorem rev_entry (xs : List Int) (hlen : xs.length < 2 ^ 63)
    (ch : Choices) :
    stepFnIter 52 (reverseSeed xs 0 [] 1)
      (.exec (reverseCall xs 0) [] .stop) ch
      = .ok (revHeadCfg,
          revStateP xs.length xs 0 ((xs.length : Int) - 1) true, ch) := by
  have hA := rev_entryA_raw xs ch
  rw [inorm_nat_of_lt hlen] at hA
  have happ1 : applyStrictOp (reverseSeed xs 0 [] 1) (.sliceExpr false)
      [.addr (.base ⟨0⟩), .int 0 .int, .int ((xs.length : Nat) : Int) .int]
      = .ok (sliceH xs.length, reverseSeed xs 0 [] 1) :=
    applyStrictOp_sliceExpr_array (lookup_seed xs) (by simp)
  have hB := rev_entryB_raw xs ch
  have happ2 : applyStrictOp (σEntry xs)
      (.lengthOf (some (.slice (.int .uint64)))) [sliceH xs.length]
      = .ok (.int ((xs.length : Nat) : Int) .int, σEntry xs) :=
    applyStrictOp_len_slice (Nat.le_refl _)
  have hC := rev_entryC_raw xs ch
  have hr1 : -(2 ^ 63) ≤ (xs.length : Int) - 1 := by omega
  have hr2 : (xs.length : Int) - 1 < 2 ^ 63 := by omega
  rw [inorm_of_range hr1 hr2, inorm_of_range hr1 hr2] at hC
  have h8 := stepFnIter_chain hA
    (stepFnIter_one
      (stepFn_strict_apply (done := [.int 0 .int, .addr (.base ⟨0⟩)]) happ1))
  have h29 := stepFnIter_chain h8 hB
  have h30 := stepFnIter_chain h29
    (stepFnIter_one (stepFn_strict_apply (done := []) happ2))
  exact stepFnIter_chain h30 hC

/-- **One swap, cleaned**: exit test true at iteration `m` → the loop
head with the partial reversal advanced, within 35 steps. -/
private theorem rev_swap_seg (xs : List Int) (m : Nat)
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64)
    (hm : 2 * m + 1 < xs.length) (ch : Choices) :
    stepFnIter 35 (cmpState xs m) (.retV (.bool true) revCmpCont) ch
      = .ok (revHeadCfg,
          revStateP xs.length (revSwap xs (m + 1)) (m : Nat)
            ((xs.length - 1 - m : Nat) : Int) false, ch) := by
  have hlenm : (revSwap xs m).length = xs.length := length_revSwap xs m
  have hrangeSwap : ∀ v ∈ revSwap xs m, 0 ≤ v ∧ v < 2 ^ 64 :=
    fun v hv => hxs v (mem_revSwap hv)
  have hwj_range : 0 ≤ xs.getD (xs.length - 1 - m) 0
      ∧ xs.getD (xs.length - 1 - m) 0 < 2 ^ 64 :=
    hxs _ (getD_mem (by omega))
  have hwi_range : 0 ≤ xs.getD m 0 ∧ xs.getD m 0 < 2 ^ 64 :=
    hxs _ (getD_mem (by omega))
  -- phase 1a: to the s[j] read
  have hA := rev_swapA_raw xs.length (revSwap xs m) (m : Nat)
    ((xs.length - 1 - m : Nat) : Int) ch
  -- the s[j] read
  have hget_j : (⟨(revSwap xs m).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + (xs.length - 1 - m)]?
      = some (.int (xs.getD (xs.length - 1 - m) 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by rw [length_revSwap]; omega),
      getD_revSwap_hi hm]
  have hread_j : stepFn
      (revStateP xs.length (revSwap xs m) (m : Nat)
        ((xs.length - 1 - m : Nat) : Int) false)
      (.retV (.int ((xs.length - 1 - m : Nat) : Int) .int)
        (.strictK .indexGet [sliceH xs.length] [] envIn2
          (rhsK1 xs.length (m : Nat) ((xs.length - 1 - m : Nat) : Int)))) ch
      = .ok (.retV (.int (xs.getD (xs.length - 1 - m) 0) .uint64)
          (rhsK1 xs.length (m : Nat) ((xs.length - 1 - m : Nat) : Int)),
        revStateP xs.length (revSwap xs m) (m : Nat)
          ((xs.length - 1 - m : Nat) : Int) false, ch) :=
    stepFn_strict_apply
      (applyStrictOp_indexGet_slice
        (lookup_state xs.length (revSwap xs m) (m : Nat)
          ((xs.length - 1 - m : Nat) : Int) false)
        (Nat.le_refl xs.length) (by omega : xs.length - 1 - m < xs.length)
        hget_j)
  -- phase 1b: to the s[i] read
  have hB := rev_swapB_raw xs.length (revSwap xs m) (m : Nat)
    ((xs.length - 1 - m : Nat) : Int)
    (.int (xs.getD (xs.length - 1 - m) 0) .uint64) ch
  have hget_i : (⟨(revSwap xs m).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + m]? = some (.int (xs.getD m 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by rw [length_revSwap]; omega),
      getD_revSwap_lo hm]
  have hread_i : stepFn
      (revStateP xs.length (revSwap xs m) (m : Nat)
        ((xs.length - 1 - m : Nat) : Int) false)
      (.retV (.int ((m : Nat) : Int) .int)
        (.strictK .indexGet [sliceH xs.length] [] envIn2
          (rhsK2 xs.length (m : Nat) ((xs.length - 1 - m : Nat) : Int)
            (.int (xs.getD (xs.length - 1 - m) 0) .uint64)))) ch
      = .ok (.retV (.int (xs.getD m 0) .uint64)
          (rhsK2 xs.length (m : Nat) ((xs.length - 1 - m : Nat) : Int)
            (.int (xs.getD (xs.length - 1 - m) 0) .uint64)),
        revStateP xs.length (revSwap xs m) (m : Nat)
          ((xs.length - 1 - m : Nat) : Int) false, ch) :=
    stepFn_strict_apply
      (applyStrictOp_indexGet_slice
        (lookup_state xs.length (revSwap xs m) (m : Nat)
          ((xs.length - 1 - m : Nat) : Int) false)
        (Nat.le_refl xs.length) (by omega : m < xs.length) hget_i)
  -- phase 1 → 2
  have hC := rev_swapC_raw xs.length (revSwap xs m) (m : Nat)
    ((xs.length - 1 - m : Nat) : Int)
    (.int (xs.getD (xs.length - 1 - m) 0) .uint64)
    (.int (xs.getD m 0) .uint64) ch
  -- store 1: s[i] := old s[j]
  have hst1 := storeTarget_slice_u64 (a := ⟨0⟩) (off := 0) (len := xs.length)
    (cap := xs.length) (i := m) (n := xs.length) (ik := .int)
    (l := revSwap xs m) (w := xs.getD (xs.length - 1 - m) 0)
    (lookup_state xs.length (revSwap xs m) (m : Nat)
      ((xs.length - 1 - m : Nat) : Int) false)
    (Nat.le_refl _) (by omega) (by omega) hlenm hrangeSwap hwj_range
  rw [Nat.zero_add] at hst1
  have hstore1 : storeTarget (cmpState xs m) (refv xs.length ((m : Nat) : Int))
      (.int (xs.getD (xs.length - 1 - m) 0) .uint64)
      = .ok (revStateP xs.length
          ((revSwap xs m).set m (xs.getD (xs.length - 1 - m) 0)) (m : Nat)
          ((xs.length - 1 - m : Nat) : Int) false) := hst1
  -- store 2: s[j] := old s[i]
  have hlen1 : ((revSwap xs m).set m (xs.getD (xs.length - 1 - m) 0)).length
      = xs.length := by simp [hlenm]
  have hrange1 : ∀ v ∈ (revSwap xs m).set m (xs.getD (xs.length - 1 - m) 0),
      0 ≤ v ∧ v < 2 ^ 64 := by
    intro v hv
    rcases mem_set_of_mem hv with rfl | hv
    · exact hwj_range
    · exact hrangeSwap v hv
  have hst2 := storeTarget_slice_u64 (a := ⟨0⟩) (off := 0) (len := xs.length)
    (cap := xs.length) (i := xs.length - 1 - m) (n := xs.length) (ik := .int)
    (l := (revSwap xs m).set m (xs.getD (xs.length - 1 - m) 0))
    (w := xs.getD m 0)
    (lookup_state xs.length
      ((revSwap xs m).set m (xs.getD (xs.length - 1 - m) 0)) (m : Nat)
      ((xs.length - 1 - m : Nat) : Int) false)
    (Nat.le_refl _) (by omega) (by omega) hlen1 hrange1 hwi_range
  rw [Nat.zero_add] at hst2
  have hstore2 : storeTarget
      (revStateP xs.length
        ((revSwap xs m).set m (xs.getD (xs.length - 1 - m) 0)) (m : Nat)
        ((xs.length - 1 - m : Nat) : Int) false)
      (refv xs.length ((xs.length - 1 - m : Nat) : Int))
      (.int (xs.getD m 0) .uint64)
      = .ok (revStateP xs.length (revSwap xs (m + 1)) (m : Nat)
          ((xs.length - 1 - m : Nat) : Int) false) := by
    rw [← revSwap_step hm]
    exact hst2
  -- the tail
  have hD := rev_swapD_raw xs.length (revSwap xs (m + 1)) (m : Nat)
    ((xs.length - 1 - m : Nat) : Int) ch
  -- chain everything
  have h1 := stepFnIter_chain hA (stepFnIter_one hread_j)
  have h2 := stepFnIter_chain h1 hB
  have h3 := stepFnIter_chain h2 (stepFnIter_one hread_i)
  have h4 := stepFnIter_chain h3 hC
  have h5 := stepFnIter_chain h4 (stepFnIter_one (stepFn_store_step hstore1))
  have h6 := stepFnIter_chain h5 (stepFnIter_one (stepFn_store_step hstore2))
  exact stepFnIter_chain h6 hD

/-- **The later-pass dispatch, cleaned**: from the head after iteration
`m` (counters still at `m`, `len - 1 - m`), `i, j = i+1, j-1` runs and
the exit test delivers, within 40 steps. -/
private theorem rev_dispatch (xs : List Int) (m : Nat)
    (hlen : xs.length < 2 ^ 63) (hm : 2 * m + 1 < xs.length) (ch : Choices) :
    stepFnIter 40
      (revStateP xs.length (revSwap xs (m + 1)) (m : Nat)
        ((xs.length - 1 - m : Nat) : Int) false) revHeadCfg ch
      = .ok (.retV (.bool (decide (((m + 1 : Nat) : Int)
              < ((xs.length - 1 - (m + 1) : Nat) : Int)))) revCmpCont,
          cmpState xs (m + 1), ch) := by
  have hA := rev_segA1_raw xs.length (revSwap xs (m + 1)) (m : Nat)
    ((xs.length - 1 - m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    show ((xs.length - 1 - m : Nat) : Int) - 1
      = ((xs.length - 1 - (m + 1) : Nat) : Int) from by omega] at hA
  rw [inorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    inorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    inorm_of_range (v := ((xs.length - 1 - (m + 1) : Nat) : Int))
      (by omega) (by omega),
    inorm_of_range (v := ((xs.length - 1 - (m + 1) : Nat) : Int))
      (by omega) (by omega)] at hA
  exact hA

/-- **The loop**, by strong induction on the remaining measure
`μ = (len - 1) - 2m` (decreases by 2 per iteration — the ≤-decrease
shape of the fuel-measure doctrine, realized directly because the
induction also pins the exact terminal state): from the exit-test
delivery of iteration `m`, the run reaches the driver terminal within
`75μ + 8` steps, at a final iteration count `m'` past the crossing
point — where the partial reversal IS the reversal. -/
private theorem rev_loop (xs : List Int) (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64)
    (hlen : xs.length < 2 ^ 63) :
    ∀ μ m, μ = (xs.length - 1) - 2 * m →
    ∀ ch : Choices, ∃ (k m' : Nat),
      k ≤ 75 * μ + 8 ∧ xs.length ≤ 2 * m' + 1 ∧
      stepFnIter k (cmpState xs m)
        (.retV (.bool (decide ((m : Int)
          < ((xs.length - 1 - m : Nat) : Int)))) revCmpCont) ch
        = .ok (.next .stop, cmpState xs m', ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hμ ch
    rcases Nat.lt_or_ge (2 * m + 1) xs.length with hlt | hge
    · -- iterate
      rw [show (decide ((m : Int) < ((xs.length - 1 - m : Nat) : Int)))
          = true from decide_eq_true (by omega)]
      obtain ⟨k, m', hk, hm', hrun⟩ := ih ((xs.length - 1) - 2 * (m + 1))
        (by omega) (m + 1) rfl ch
      refine ⟨35 + 40 + k, m', by omega, hm', ?_⟩
      exact stepFnIter_chain
        (stepFnIter_chain (rev_swap_seg xs m hxs hlt ch)
          (rev_dispatch xs m hlen hlt ch)) hrun
    · -- exit
      rw [show (decide ((m : Int) < ((xs.length - 1 - m : Nat) : Int)))
          = false from decide_eq_false (by omega)]
      exact ⟨8, m, by omega, by omega,
        rev_exit_raw xs.length (revSwap xs m) ((m : Nat) : Int)
          ((xs.length - 1 - m : Nat) : Int) ch⟩

private theorem reverse_short {xs : List Int} (h : xs.length ≤ 1) :
    xs.reverse = xs := by
  match xs, h with
  | [], _ => rfl
  | [a], _ => rfl

/-- **The canonical run, end to end**: from the canonical seed the
driver completes at the `.normal` terminal within `85 + 75·len` steps,
with the backing cell holding the reversal. -/
private theorem rev_runs (xs : List Int)
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (hlen : xs.length < 2 ^ 63)
    (ch : Choices) :
    ∃ (k : Nat) (σf : ExecState), k ≤ 85 + 75 * xs.length ∧
      stepFnIter k (reverseSeed xs 0 [] 1)
        (.exec (reverseCall xs 0) [] .stop) ch
        = .ok (.next .stop, σf, ch)
      ∧ Heap.lookup σf.heap (.base ⟨0⟩)
          = some ⟨some (.array xs.length (.int .uint64)),
              .array ⟨xs.reverse.map (fun v => .int v .uint64)⟩⟩ := by
  have hE := rev_entry xs hlen ch
  have hA0 := rev_segA0_raw xs.length xs 0 ((xs.length : Int) - 1) ch
  have h77 := stepFnIter_chain hE hA0
  rcases Nat.lt_or_ge xs.length 2 with hshort | hlong
  · -- len ≤ 1: the first test already fails; nothing swaps
    rw [show (decide ((0 : Int) < (xs.length : Int) - 1)) = false from
      decide_eq_false (by omega)] at h77
    have hX := rev_exit_raw xs.length xs 0 ((xs.length : Int) - 1) ch
    refine ⟨85, _, by omega, stepFnIter_chain h77 hX, ?_⟩
    rw [reverse_short (by omega)]
    exact lookup_state xs.length xs 0 ((xs.length : Int) - 1) false
  · -- len ≥ 2: enter the loop at iteration 0
    have h77' : stepFnIter 77 (reverseSeed xs 0 [] 1)
        (.exec (reverseCall xs 0) [] .stop) ch
        = Except.ok (.retV (.bool (decide (((0 : Nat) : Int)
            < ((xs.length - 1 - 0 : Nat) : Int)))) revCmpCont,
          cmpState xs 0, ch) := by
      show stepFnIter 77 (reverseSeed xs 0 [] 1)
        (.exec (reverseCall xs 0) [] .stop) ch
        = Except.ok (.retV (.bool (decide (((0 : Nat) : Int)
            < ((xs.length - 1 - 0 : Nat) : Int)))) revCmpCont,
          revStateP xs.length (revSwap xs 0) ((0 : Nat) : Int)
            ((xs.length - 1 - 0 : Nat) : Int) false, ch)
      rw [revSwap_zero,
        show (((xs.length - 1 - 0 : Nat) : Int))
          = (xs.length : Int) - 1 from by omega]
      exact h77
    obtain ⟨k, m', hk, hm', hrun⟩ := rev_loop xs hxs hlen
      ((xs.length - 1) - 2 * 0) 0 rfl ch
    refine ⟨77 + k, cmpState xs m', by omega,
      stepFnIter_chain h77' hrun, ?_⟩
    show Heap.lookup (revStateP xs.length (revSwap xs m') ((m' : Nat) : Int)
      ((xs.length - 1 - m' : Nat) : Int) false).heap _ = _
    rw [lookup_state, revSwap_reverse hm']

/-! ## The canonical-placement total run -/

/-- **Total correctness at the canonical placement**: past fuel
`85 + 75·len`, at every choice stream, execution completes normally
with the reversal in the backing cell. -/
private theorem reverse_total_canonical (xs : List Int)
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (hlen : xs.length < 2 ^ 63) :
    ∀ fuel : Nat, 85 + 75 * xs.length ≤ fuel → ∀ ch : Choices,
      ∃ σf : ExecState,
        execStmtLoop fuel (reverseSeed xs 0 [] 1)
          (.exec (reverseCall xs 0) [] .stop) ch = .ok (.normal σf, ch)
        ∧ Heap.lookup σf.heap (.base ⟨0⟩)
            = some ⟨some (.array xs.length (.int .uint64)),
                .array ⟨xs.reverse.map (fun v => .int v .uint64)⟩⟩ := by
  intro fuel hfuel ch
  obtain ⟨k, σf, hk, hrun, hread⟩ := rev_runs xs hxs hlen ch
  refine ⟨σf, ?_, hread⟩
  have hfold := execStmtLoop_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [hfold, execStmtLoop_next_stop]

/-! ## The framed form: the frame theorem consumed at an
input-RELOCATING renaming

The ∀-placement (`base`) quantifier is realized by the GENERALIZED `ρ`
(frame-theorem build handoff §3 finding 1 — any `ShiftSpec` injection,
not just the uniform shift): `relocShift base na` maps the canonical
input cell `0` to `base` and the canonical fresh region `[1, ∞)` to
`[na, ∞)`. The canonical seed is TIGHT (dom = {0}, na₀ = 1), exactly
what `fr_avoid`'s seed discharge needs. -/

open GoLean.Frame

/-- The input-relocating renaming: `0 ↦ base`, `1 + k ↦ na + k`. -/
private def relocShift (base na : Nat) : Nat → Nat :=
  fun x => if x = 0 then base else na + (x - 1)

/-- Loc-freedom of the wrapped-integer backing array (the rename
identity's premise). -/
private theorem locSup_mapU (l : List Int) :
    GoValue.locSup (.array ⟨l.map (fun v => .int v .uint64)⟩) = 0 := by
  show goValueListSup (l.map (fun v => .int v .uint64)) = 0
  induction l with
  | nil => rfl
  | cons v rest ih => simpa [goValueListSup, GoValue.locSup] using ih

/-- The seed simulation: reverse's canonical seed beside the framed
seed at an arbitrary placement, through the relocating shift. -/
private theorem revSeedFrameSim (xs : List Int) (base : Nat) (fr : Heap)
    (na : Nat)
    (hb : Heap.lookup fr (.base ⟨base⟩) = none)
    (hwf : MachineWf
      { functions := reverseLowered.funcs,
        heap := sliceCells xs base ++ fr, nextAddr := na }
      (.exec (reverseCall xs base) [] .stop)) :
    FrameSim (relocShift base na) 1 na fr (reverseSeed xs 0 [] 1)
      (reverseSeed xs base fr na) := by
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
    simp [reverseSeed, relocShift]
  · -- alloc_reg
    exact Nat.le_refl 1
  · -- lookup_img
    intro l
    by_cases hl : l = .base ⟨0⟩
    · subst hl
      rw [hren0]
      simp only [reverseSeed, sliceCells, List.cons_append, List.nil_append,
        Heap.lookup]
      simp [hcellid]
    · have hcanon : Heap.lookup (reverseSeed xs 0 [] 1).heap l = none := by
        have hne : ((.base ⟨0⟩ : Loc) == l) = false :=
          beq_false_of_ne (fun h => hl h.symm)
        simp [reverseSeed, sliceCells, Heap.lookup, hne]
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
      simp only [reverseSeed, sliceCells, List.cons_append, List.nil_append,
        Heap.lookup, hne']
      rfl
  · -- frame_pres
    intro l c hl
    have hne : ((.base ⟨base⟩ : Loc) == l) = false := by
      refine beq_false_of_ne (fun hc => ?_)
      rw [← hc, hb] at hl
      cases hl
    simp only [reverseSeed, sliceCells, List.cons_append, List.nil_append,
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
      (fs := reverseLowered.funcs)
      (by decide : funcListSup reverseLowered.funcs.toList ≤ 0)

/-- The driver configuration renames to the framed driver: the
relocating shift carries the `locLit` base pointer to `base` — the
∀-placement realization. -/
private theorem rev_cfg_ren (xs : List Int) (base na : Nat) :
    renameConfig (relocShift base na)
      (.exec (reverseCall xs 0) [] .stop)
      = .exec (reverseCall xs base) [] .stop := by
  simp [renameConfig, renameCont, renameEnv, renameStmt, reverseCall,
    renameExprList, renameExpr, renameOptExpr, renameLoc, relocShift]

/-! ## The §9e headline -/

/-- **THE §9e HEADLINE, completion split closed** (design note
`docs/2026-08-12_example-spec-form.md` §9e; the frame theorem supplies
the ∀-frame completion): *for any list `xs` of uint64 values, wherever
it lives in memory, with anything else present: `reverse` completes
normally — past one fuel bound, at every nondeterminism-choice
stream — the backing cell then holds `xs` reversed, and no other
memory is touched.*

Recorded statement deltas against the §9e draft (module docstring for
the full reasoning): `hlen : xs.length < 2 ^ 63` added — with the
completion clause IN the statement the draft is FALSE at lengths past
Go's `int` domain (the driver's `len` literal wraps negative and the
slice-expression bounds check panics); the bound is Go's own `int`
range, not a proof-method limit.

The proof: total correctness at the TIGHT canonical placement
(`base = 0`, empty frame — direct machine-step segments +
strong induction on the two-pointer measure `(len-1) - 2m`), then the
executable frame theorem's success-run transfer `execStmtLoop_ren` at
the input-RELOCATING renaming `relocShift base na` (any-`ShiftSpec`
generality; nothing is re-run at the framed placement). Value readout
transfers through the terminal `FrameSim`'s pointwise heap
characterization; frame preservation is its `frame_pres` clause
verbatim. -/
theorem reverse_ok (xs : List Int) (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64)
    (hlen : xs.length < 2 ^ 63)
    (base : Nat) (fr : Heap) (na : Nat)
    (hb : Heap.lookup fr (.base ⟨base⟩) = none)
    (hwf : MachineWf
      { functions := reverseLowered.funcs,
        heap := sliceCells xs base ++ fr, nextAddr := na }
      (.exec (reverseCall xs base) [] .stop)) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel [] (reverseSeed xs base fr na) ch
            (reverseCall xs base)
          = .ok (.normal σf, ch')
        ∧ Heap.lookup σf.heap (.base ⟨base⟩)
            = some ⟨some (.array xs.length (.int .uint64)),
                .array ⟨xs.reverse.map (fun v => .int v .uint64)⟩⟩
        ∧ ∀ (a : Nat) (c : HeapCell),
            Heap.lookup fr (.base ⟨a⟩) = some c →
            Heap.lookup σf.heap (.base ⟨a⟩) = some c := by
  have hSF := revSeedFrameSim xs base fr na hb hwf
  refine ⟨85 + 75 * xs.length, fun fuel hfuel ch => ?_⟩
  obtain ⟨σc, hrunC, hreadC⟩ :=
    reverse_total_canonical xs hxs hlen fuel hfuel ch
  obtain ⟨outF, hrunF, hout⟩ := Frame.execStmtLoop_ren fuel hSF hrunC
  rw [rev_cfg_ren xs base na] at hrunF
  cases outF with
  | normal σF =>
      obtain ⟨hSF', -⟩ := hout
      refine ⟨σF, ch, hrunF, ?_, ?_⟩
      · have hlook := hSF'.lookup_some hreadC
        have hren0 : renameLoc (relocShift base na) (.base ⟨0⟩)
            = .base ⟨base⟩ := by
          simp [renameLoc, relocShift]
        have hv : renameValue (relocShift base na)
            (.array ⟨xs.reverse.map (fun v => .int v .uint64)⟩)
            = .array ⟨xs.reverse.map (fun v => .int v .uint64)⟩ :=
          renameValue_locFree _ _ (locSup_mapU xs.reverse)
        have hcell : renameCell (relocShift base na)
            (⟨some (.array xs.length (.int .uint64)),
              .array ⟨xs.reverse.map (fun v => .int v .uint64)⟩⟩ : HeapCell)
            = ⟨some (.array xs.length (.int .uint64)),
               .array ⟨xs.reverse.map (fun v => .int v .uint64)⟩⟩ :=
          congrArg (HeapCell.mk (some (.array xs.length (.int .uint64)))) hv
        rw [hren0, hcell] at hlook
        exact hlook
      · intro a c hac
        exact hSF'.frame_pres (.base ⟨a⟩) c hac
  | returned σF => exact hout.elim
  | broke σF => exact hout.elim
  | continued σF => exact hout.elim

end GoLean.Examples.Reverse
