import GoLeanProofs.Examples.ReverseProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Examples.Targets

/-!
# Verified example: in-place slice reversal (verified-examples slice 2b,
2026-08-13)

The §9e memory-input exemplar (design note
`docs/2026-08-12_example-spec-form.md` §9): the Go program is the
canonical corpus source `Corpus/coverage/exec/examples/reverse/main.go`
(5/5 differentially green against `go run`); `reverseLowered` is its
pinned frontend lowering (`scripts/check-golden`, both links).

**WHERE THE HEADLINE LIVES — read this first** (examples phase-2 slice
1 swap, 2026-08-14; recorded here in the audit response, 2026-08-15,
which found this module claiming a headline it no longer declares).
The DESIGNATED gallery headline `reverse_ok` is now the S1
COPY-RELATIONAL form over `reverse_harness_v`, and it is declared in
the swap shard `GoLeanProofs.Examples.Reverse.HarnessV` — not here.
What THIS module declares is the previous headline, kept unweakened
and renamed `reverse_ok_v1` (with `reverse_readout_v1`), plus the
memory-quantified `reverse_framed`.

The shard IMPORTS this module, so the reach is one-way: importing
`GoLeanProofs.Examples.Reverse` does not give you `reverse_ok`, while
importing `GoLeanProofs.Examples.Reverse.HarnessV` gives you both.
Import the shard. The re-export that would make this module the single
entry point is not expressible while the shard imports it — Lean's
import graph is acyclic — so it waits on splitting this module's
proofs into a `Core` shard, recorded as a post-merge follow-up in
`docs/2026-08-15_phase2-premerge-audit.md` (C-H4/C-H5). The aggregator
`GoLeanProofs.lean` imports both, so nothing is outside the audited
build.

The paragraph below describes `reverse_ok_v1` — it was written when
that theorem held the `reverse_ok` name, and the name is the only
thing that changed: the previous user-facing statement was THE HARNESS
FORM (harness ruling 2026-08-13, design note §11): the three-phase Go
harness
`reverse_harness(n, seed)` (setup: `s := make([]uint64, n)` filled
with `s[i] = seed + i`; call under test: `reverse(s)`; test: an
element-wise check of the reversal folding into the returned verdict
`ok ∈ {0, 1}`), stated through the machine's native function entry
`runFunctionWithContextM` — termination + returned values only, no
cell/seed/env vocabulary. The §9e memory-quantified headline is KEPT
as the proof-side supporting layer under the name `reverse_framed`
(§11 status note: framed forms are the reserve layer; the harness
restatement takes the `reverse_ok` name).

`reverse_framed` (the old §9e headline) closed the completion split
with the executable frame theorem
(`docs/2026-08-13_executable-frame-theorem.md`; `Frame/`): the ∃N
completion clause holds at EVERY admissible framed placement,
transferred from the canonical run — nothing is re-run at a framed
placement. Statement deltas against the §9e block, both recorded
honestly in the docstring of `reverse_framed`:

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
def revSwap (xs : List Int) (m : Nat) : List Int :=
  (List.range xs.length).map fun k =>
    if k < m ∨ xs.length - m ≤ k then xs.getD (xs.length - 1 - k) 0
    else xs.getD k 0

theorem length_revSwap (xs : List Int) (m : Nat) :
    (revSwap xs m).length = xs.length := by
  simp [revSwap]

theorem getElem?_revSwap (xs : List Int) (m k : Nat)
    (hk : k < xs.length) :
    (revSwap xs m)[k]? =
      some (if k < m ∨ xs.length - m ≤ k then xs.getD (xs.length - 1 - k) 0
        else xs.getD k 0) := by
  simp [revSwap, List.getElem?_map, List.getElem?_range, hk]

theorem getD_revSwap (xs : List Int) (m k : Nat)
    (hk : k < xs.length) :
    (revSwap xs m).getD k 0 =
      if k < m ∨ xs.length - m ≤ k then xs.getD (xs.length - 1 - k) 0
      else xs.getD k 0 := by
  simp [List.getD, getElem?_revSwap xs m k hk]

theorem revSwap_zero (xs : List Int) : revSwap xs 0 = xs := by
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
theorem mem_revSwap {xs : List Int} {m : Nat} {v : Int}
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
theorem getD_revSwap_lo {xs : List Int} {m : Nat}
    (h : 2 * m + 1 < xs.length) :
    (revSwap xs m).getD m 0 = xs.getD m 0 := by
  rw [getD_revSwap xs m m (by omega), if_neg (by omega)]

theorem getD_revSwap_hi {xs : List Int} {m : Nat}
    (h : 2 * m + 1 < xs.length) :
    (revSwap xs m).getD (xs.length - 1 - m) 0
      = xs.getD (xs.length - 1 - m) 0 := by
  rw [getD_revSwap xs m _ (by omega), if_neg (by omega)]

/-- **One machine swap advances the partial reversal**: setting position
`m` to the (still-original) element at `length - 1 - m` and vice versa
is exactly `revSwap` at `m + 1`. -/
theorem revSwap_step {xs : List Int} {m : Nat}
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
theorem revSwap_reverse {xs : List Int} {m : Nat}
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

def ffBlock : Stmt :=
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

theorem reverse_short {xs : List Int} (h : xs.length ≤ 1) :
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

/-! ## The §9e memory-quantified form (proof-side supporting layer per
§11 — kept; the user-facing statement is the harness `reverse_ok`
below) -/

/-- **Proof-side supporting layer per §11 (the memory-quantified form,
kept)** — the §9e headline, completion split closed (design note
`docs/2026-08-12_example-spec-form.md` §9e; the frame theorem supplies
the ∀-frame completion): *for any list `xs` of uint64 values, wherever
it lives in memory, with anything else present: `reverse` completes
normally — past one fuel bound, at every nondeterminism-choice
stream — the backing cell then holds `xs` reversed, and no other
memory is touched.* Genuinely ∀-input over the slice contents — the
memory-quantified reserve form the harness headline's input FAMILY
does not subsume; kept per the §11 status ruling.

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
theorem reverse_framed (xs : List Int) (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64)
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

/-! ## The harness restatement (THE HARNESS RULING, 2026-08-13 —
design note §11: the final user-facing form)

The user-facing statement `reverse_ok` states the three-phase Go
harness `reverse_harness(n, seed)` through the machine's NATIVE
function entry `runFunctionWithContextM`:

* **setup** (`setup_reverse_state`): `s := make([]uint64, n)`, then
  `for i { s[i] = seed + i }` — builds all memory the test needs from
  the scalar parameters;
* **the call under test**: `reverse(s)`;
* **test** (`test_reverse_state`): `for i { if s[i] != seed+((n-1)-i)
  { ok = 0 } }` — the memory ANALYSIS happens IN GO, inside the
  verified footprint, folding into the returned verdict `ok ∈ {0,1}`.

The statement observes termination + the returned verdict only: no
`loadLoc`, no cell/seed/env vocabulary (§11 ruling (2)); framing is
implicit in the empty-heap entry (§11 ruling (3)); quantification is
over instantiated `GoValue` arguments at the call boundary (§11
ruling (1) — no AST splicing, no program families).

**INPUT-FAMILY HONESTY (recorded per §11's variable-size-inputs
ruling)**: the quantification is over the SCALARS `(n, seed)` — i.e.
over the input family `revFamily n seed = [seed, seed+1, …,
seed+(n-1)] (mod 2^64)`, honestly WEAKER than ∀xs over arbitrary
slice contents (the designed-not-built choice-consuming input pick,
§11; until it lands, setup loops parameterized by scalars give input
FAMILIES). The ∀xs claim remains available proof-side as
`reverse_framed`. The WRAPPING family is deliberate: `seed + i` wraps
at `2^64`, so the family covers wrap boundaries — matching the corpus
rows, which exercise the harness at concrete arguments including a
near-`2^63` seed.

Proof route (the fib harness pattern + three loops): the entry
equation (`revH_entry_eq`, `with_unfolding_all rfl`); the makeSlice
step at SYMBOLIC `n` (`buildDefaultArrayValue_int` supplies the
replicate-shaped backing); one strong induction per loop — the setup
loop (invariant: backing = family-prefix ++ zeros), the reverse
two-pointer loop (the `revSwap` machinery above, re-derived at the
harness address layout), the test loop (invariant: backing = the
reversed family, verdict pinned 1) — each pinning the exact machine
state; `runConfig_of_stepFnIter` + `runConfig_next_stop` fold the
run and the readback computes definitionally. -/

/-- **The input family**: the slice contents the setup phase builds
from `(n, seed)` — `n` consecutive uint64 values from `seed`, wrapped
at `2^64` (Go's uint64 addition; the wrap is part of the family by
design). -/
def revFamily (n seed : Nat) : List Int :=
  (List.range n).map (fun i => (((seed + i) % 2 ^ 64 : Nat) : Int))

-- HOISTED to `GoLeanProofs/Examples/Targets.lean` (designation, 2026-08-14):
-- `reverseHarnessFunc` is statement vocabulary of a DESIGNATED gallery headline, so it must
-- live in a def-only module inside the Comparator Challenge's trusted import
-- closure. The definition is unchanged and still visible here via the import.

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem reverseHarness_pin :
    findFunctionIn? reverseLowered.funcs ⟨"reverse_harness"⟩
    = some reverseHarnessFunc := rfl

/-! ### The pure layer: the family, the setup prefix, the test reads -/

theorem length_revFamily (n seed : Nat) :
    (revFamily n seed).length = n := by
  simp [revFamily]

theorem mem_revFamily {n seed : Nat} {v : Int}
    (h : v ∈ revFamily n seed) : 0 ≤ v ∧ v < 2 ^ 64 := by
  simp only [revFamily, List.mem_map, List.mem_range] at h
  obtain ⟨i, -, rfl⟩ := h
  have : (seed + i) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by omega)
  omega

/-- The setup loop's backing after `m` fill iterations: the family
prefix, then still-zero slots. -/
def suList (n seed m : Nat) : List Int :=
  revFamily m seed ++ List.replicate (n - m) 0

theorem suList_zero (n seed : Nat) :
    suList n seed 0 = List.replicate n 0 := by
  simp [suList, revFamily]

theorem length_suList {n seed m : Nat} (hm : m ≤ n) :
    (suList n seed m).length = n := by
  simp [suList, length_revFamily]
  omega

theorem mem_suList {n seed m : Nat} {v : Int}
    (h : v ∈ suList n seed m) : 0 ≤ v ∧ v < 2 ^ 64 := by
  simp only [suList, List.mem_append, List.mem_replicate] at h
  rcases h with h | h
  · exact mem_revFamily h
  · omega

theorem revFamily_succ (m seed : Nat) :
    revFamily (m + 1) seed
      = revFamily m seed ++ [(((seed + m) % 2 ^ 64 : Nat) : Int)] := by
  simp [revFamily, List.range_succ]

/-- One fill store advances the prefix. -/
theorem suList_set {n seed m : Nat} (hm : m < n) :
    (suList n seed m).set m (((seed + m) % 2 ^ 64 : Nat) : Int)
      = suList n seed (m + 1) := by
  have hlen : (revFamily m seed).length = m := length_revFamily m seed
  have hnm : n - m = (n - (m + 1)) + 1 := by omega
  rw [suList, List.set_append_right _ _ (by omega), hlen, Nat.sub_self,
    hnm, List.replicate_succ, List.set_cons_zero, suList, revFamily_succ]
  simp

theorem suList_full (n seed : Nat) :
    suList n seed n = revFamily n seed := by
  simp [suList]

/-- The test loop's element read: position `m` of the REVERSED family
holds `seed + (n-1-m)`, wrapped. -/
theorem getD_reverse_revFamily {n seed m : Nat} (hm : m < n) :
    (revFamily n seed).reverse.getD m 0
      = (((seed + (n - 1 - m)) % 2 ^ 64 : Nat) : Int) := by
  have hlen : (revFamily n seed).length = n := length_revFamily n seed
  have hrev : (revFamily n seed).reverse[m]?
      = (revFamily n seed)[n - 1 - m]? := by
    rw [List.getElem?_reverse (by omega), hlen]
  rw [List.getD, hrev]
  simp only [revFamily, List.getElem?_map, List.getElem?_range
    (by omega : n - 1 - m < n)]
  rfl

/-! ### The machine layer: harness address layout (probe-verified;
every raw segment re-checks the transcription by `rfl`).

Addresses: 0 = `n`, 1 = `seed`, 2 = `$res0`, 3 = `$c4` (the slice
handle), 4 = the backing array, 5 = `s`, 6 = the setup counter,
7 = the setup flag, 8 = reverse's `s` parameter, 9/10 = reverse's
`i`/`j`, 11 = reverse's flag, 12 = `ok`, 13 = the test counter,
14 = the test flag. -/

private abbrev hu64 (v : Int) : HeapCell := ⟨some (.int .uint64), .int v .uint64⟩
/-- The harness slice handle: backing at 4, offset 0, len = cap = `n`. -/
private abbrev hSlice (n : Nat) : GoValue := .slice ⟨some (.base ⟨4⟩), 0, n, n⟩
private abbrev hSliceCell (n : Nat) : HeapCell :=
  ⟨some (.slice (.int .uint64)), hSlice n⟩
private abbrev hArrCell (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n (.int .uint64)), .array ⟨l.map (fun v => .int v .uint64)⟩⟩

private def baseEnvH : Scope :=
  [("$res0", .base ⟨2⟩), ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]

/-- The machine entry's post-prelude state: the three frame cells the
prelude allocates from the EMPTY heap. -/
private def revHSeed (nv sv : Int) : ExecState :=
  { types := reverseLowered.typeDefs.toList,
    functions := reverseLowered.funcs,
    methods := reverseLowered.methods,
    heap := [(.base ⟨0⟩, hu64 nv), (.base ⟨1⟩, hu64 sv),
             (.base ⟨2⟩, hu64 0)],
    nextAddr := 3 }

/-- The post-prelude configuration. -/
private def revHC₀ : Config :=
  .exec reverseHarnessFunc.body [[("$res0", .base ⟨2⟩),
    ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]] (.frame [] [] [] [] .stop)

/-- **The entry equation** (the §11 glue, reverse instance): the
machine entry IS its post-prelude `runConfig` form — pure
`with_unfolding_all rfl` at fully symbolic `n`, `seed`, `fuel`, `ch`. -/
private theorem revH_entry_eq (n seed fuel : Nat) (ch : Choices) :
    runFunctionWithContextM fuel reverseLowered.typeDefs.toList
        reverseLowered.funcs reverseHarnessFunc
        #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
        reverseLowered.methods ch
      = (do
          let (sF, _) ← runConfig fuel
            (revHSeed (IntKind.normalize .uint64 (n : Int))
              (IntKind.normalize .uint64 (seed : Int))) revHC₀ ch
          return { values := (← loadMany sF [Loc.base ⟨2⟩]).toArray }) := by
  with_unfolding_all rfl

/-! ### Harness statement pieces and continuations (probe-verified) -/

private def hS2 : Stmt :=
  .seqn #[.initialization { id := "s", typ := .slice (.int .uint64) },
          .assign (.var "s") (.var "$c4")]
private def hS3 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .uint64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) reverseHarnessFunc.suBody]]
private def hS4 : Stmt := .call #[] ⟨"reverse"⟩ #[.var "s"]
private def hS5 : Stmt :=
  .seqn #[.initialization { id := "ok", typ := .int .uint64 },
          .assign (.var "ok") (.intLit 1 .uint64)]
private def hS6 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .uint64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) reverseHarnessFunc.tstBody]]
private def hS7 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "ok"), .returnStmt]

private def envC4H : LocalEnv := [[("$c4", .base ⟨3⟩)], baseEnvH]
private def sScopeH : Scope := [("s", .base ⟨5⟩), ("$c4", .base ⟨3⟩)]
private def suEnv : LocalEnv :=
  [[("$forFirst", .base ⟨7⟩)], [("i", .base ⟨6⟩)], sScopeH, baseEnvH]
private def suEnv2 : LocalEnv := [] :: [] :: suEnv

/-- The setup-loop head continuation. -/
private def suHeadTail : Cont :=
  .seq [] suEnv
    (.seq [] [[("i", .base ⟨6⟩)], sScopeH, baseEnvH]
      (.seq [hS4, hS5, hS6, hS7] [sScopeH, baseEnvH]
        (.frame [] [] [] [] .stop)))
private def suHeadCfg : Config :=
  .exec (.while (.boolLit true) reverseHarnessFunc.suBody) suEnv suHeadTail
private def suLoopK : Cont :=
  .loop (.boolLit true) reverseHarnessFunc.suBody suEnv suHeadTail
private def suStoreBlock : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
        (.add (.var "seed") (.var "i"))]]
private def suCmpCont : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: suEnv)
    (.seq [suStoreBlock] ([] :: suEnv) suLoopK)
private def suRef (n : Nat) (iv : Int) : TargetRef :=
  .chain (hSlice n) [.int iv .uint64] [.index]
private def suSwTail : Cont := .seq [] suEnv2 (.seq [] ([] :: suEnv) suLoopK)

/-- Reverse-phase continuations (the standalone module's tower with the
harness addresses, sitting on the after-call continuation). -/
private def revEnvInH : LocalEnv :=
  [[("$forFirst", .base ⟨11⟩)], [("j", .base ⟨10⟩), ("i", .base ⟨9⟩)],
   [], [("s", .base ⟨8⟩)]]
private def revEnvMidH : LocalEnv :=
  [[("j", .base ⟨10⟩), ("i", .base ⟨9⟩)], [], [("s", .base ⟨8⟩)]]
private def revEnvOutH : LocalEnv := [[], [("s", .base ⟨8⟩)]]
private def revHAfterCall : Cont :=
  .seq [hS5, hS6, hS7] [sScopeH, baseEnvH] (.frame [] [] [] [] .stop)
private def revFrameH : Cont :=
  .frame [] [sScopeH, baseEnvH] [] [] revHAfterCall false
private def revHHeadTail : Cont :=
  .seq [] revEnvInH (.seq [] revEnvMidH (.seq [] revEnvOutH revFrameH))
private def revHHeadCfg : Config :=
  .exec (.while (.boolLit true) revWhileBody) revEnvInH revHHeadTail
private def revHLoopK : Cont :=
  .loop (.boolLit true) revWhileBody revEnvInH revHHeadTail
private def revHCmpCont : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: revEnvInH)
    (.seq [revSwapBlock] ([] :: revEnvInH) revHLoopK)
private def envIn2H : LocalEnv := [] :: [] :: revEnvInH
private def swTailH : Cont :=
  .seq [] envIn2H (.seq [] ([] :: revEnvInH) revHLoopK)
private def hRefv (n : Nat) (v : Int) : TargetRef :=
  .chain (hSlice n) [.int v .int] [.index]
private def hRhsK1 (n : Nat) (iv jv : Int) : Cont :=
  .rhsK .vals [hRefv n iv, hRefv n jv] [] [.indexGet (.var "s") (.var "i")]
    (.seqn #[]) envIn2H swTailH
private def hRhsK2 (n : Nat) (iv jv : Int) (wj : GoValue) : Cont :=
  .rhsK .vals [hRefv n iv, hRefv n jv] [wj] [] (.seqn #[]) envIn2H swTailH
private def entryRhsKH : Cont :=
  .rhsK .vals
    [.chain (.addr (.base ⟨9⟩)) [] [], .chain (.addr (.base ⟨10⟩)) [] []]
    [.int 0 .int] [] (.seqn #[]) revEnvMidH
    (.seq [ffBlock] revEnvMidH (.seq [] revEnvOutH revFrameH))

/-- Test-phase continuations. -/
private def okScopeH : Scope :=
  [("ok", .base ⟨12⟩), ("s", .base ⟨5⟩), ("$c4", .base ⟨3⟩)]
private def tstEnv : LocalEnv :=
  [[("$forFirst", .base ⟨14⟩)], [("i", .base ⟨13⟩)], okScopeH, baseEnvH]
private def tstEnv2 : LocalEnv := [] :: [] :: tstEnv
private def tstHeadTail : Cont :=
  .seq [] tstEnv
    (.seq [] [[("i", .base ⟨13⟩)], okScopeH, baseEnvH]
      (.seq [hS7] [okScopeH, baseEnvH] (.frame [] [] [] [] .stop)))
private def tstHeadCfg : Config :=
  .exec (.while (.boolLit true) reverseHarnessFunc.tstBody) tstEnv tstHeadTail
private def tstLoopK : Cont :=
  .loop (.boolLit true) reverseHarnessFunc.tstBody tstEnv tstHeadTail
private def tstAddExpr : Expr :=
  .add (.var "seed")
    (.sub (.sub (.var "n") (.intLit 1 .uint64)) (.var "i"))
private def tstCheckBlock : Stmt :=
  .block #[]
    #[.ifThenElse
        (.neqCmp (.int .uint64) (.indexGet (.var "s") (.var "i")) tstAddExpr)
        (.block #[] #[.seqn #[.assign (.var "ok") (.intLit 0 .uint64)]])
        (.seqn #[])]
private def tstCmpCont : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: tstEnv)
    (.seq [tstCheckBlock] ([] :: tstEnv) tstLoopK)
private def tstIfK : Cont :=
  .ifK (.block #[] #[.seqn #[.assign (.var "ok") (.intLit 0 .uint64)]])
    (.seqn #[]) tstEnv2 (.seq [] tstEnv2 (.seq [] ([] :: tstEnv) tstLoopK))
private def tstNeqK : Cont :=
  .strictK (.neqCmp (.int .uint64)) [] [tstAddExpr] tstEnv2 tstIfK

/-! ### State families (harness layout) -/

private def σE1st (n seed : Nat) : ExecState :=
  { types := reverseLowered.typeDefs.toList,
    functions := reverseLowered.funcs,
    methods := reverseLowered.methods,
    heap := [(.base ⟨0⟩, hu64 (n : Int)), (.base ⟨1⟩, hu64 (seed : Int)),
             (.base ⟨2⟩, hu64 0),
             (.base ⟨3⟩, ⟨some (.slice (.int .uint64)),
               .slice ⟨none, 0, 0, 0⟩⟩)],
    nextAddr := 4 }

private def σMake (n seed : Nat) : ExecState :=
  { types := reverseLowered.typeDefs.toList,
    functions := reverseLowered.funcs,
    methods := reverseLowered.methods,
    heap := [(.base ⟨0⟩, hu64 (n : Int)), (.base ⟨1⟩, hu64 (seed : Int)),
             (.base ⟨2⟩, hu64 0), (.base ⟨3⟩, hSliceCell n),
             (.base ⟨4⟩, hArrCell n (List.replicate n 0))],
    nextAddr := 5 }

/-- The setup-loop state: backing list `l`, counter `iv`, flag. -/
private def suState (n seed : Nat) (l : List Int) (iv : Int) (ffv : Bool) :
    ExecState :=
  { types := reverseLowered.typeDefs.toList,
    functions := reverseLowered.funcs,
    methods := reverseLowered.methods,
    heap := [(.base ⟨0⟩, hu64 (n : Int)), (.base ⟨1⟩, hu64 (seed : Int)),
             (.base ⟨2⟩, hu64 0), (.base ⟨3⟩, hSliceCell n),
             (.base ⟨4⟩, hArrCell n l), (.base ⟨5⟩, hSliceCell n),
             (.base ⟨6⟩, hu64 iv), (.base ⟨7⟩, bcell ffv)],
    nextAddr := 8 }

/-- Mid reverse-entry: reverse's `s` bound, `i`/`j` at defaults. -/
private def σRevEntry (n seed : Nat) (l : List Int) (siv : Int) : ExecState :=
  { types := reverseLowered.typeDefs.toList,
    functions := reverseLowered.funcs,
    methods := reverseLowered.methods,
    heap := [(.base ⟨0⟩, hu64 (n : Int)), (.base ⟨1⟩, hu64 (seed : Int)),
             (.base ⟨2⟩, hu64 0), (.base ⟨3⟩, hSliceCell n),
             (.base ⟨4⟩, hArrCell n l), (.base ⟨5⟩, hSliceCell n),
             (.base ⟨6⟩, hu64 siv), (.base ⟨7⟩, bcell false),
             (.base ⟨8⟩, hSliceCell n), (.base ⟨9⟩, intcell 0),
             (.base ⟨10⟩, intcell 0)],
    nextAddr := 11 }

/-- The reverse-phase in-loop state (`siv` = the parked setup counter). -/
private def hrevState (n seed : Nat) (siv : Int) (l : List Int)
    (iv jv : Int) (ffv : Bool) : ExecState :=
  { types := reverseLowered.typeDefs.toList,
    functions := reverseLowered.funcs,
    methods := reverseLowered.methods,
    heap := [(.base ⟨0⟩, hu64 (n : Int)), (.base ⟨1⟩, hu64 (seed : Int)),
             (.base ⟨2⟩, hu64 0), (.base ⟨3⟩, hSliceCell n),
             (.base ⟨4⟩, hArrCell n l), (.base ⟨5⟩, hSliceCell n),
             (.base ⟨6⟩, hu64 siv), (.base ⟨7⟩, bcell false),
             (.base ⟨8⟩, hSliceCell n), (.base ⟨9⟩, intcell iv),
             (.base ⟨10⟩, intcell jv), (.base ⟨11⟩, bcell ffv)],
    nextAddr := 12 }

/-- The test-phase in-loop state (`rif`/`rjf` = reverse's parked final
counters — inert; the verdict cell 12 is pinned 1). -/
private def tstState (n seed : Nat) (siv rif rjf : Int) (l : List Int)
    (iv : Int) (ffv : Bool) : ExecState :=
  { types := reverseLowered.typeDefs.toList,
    functions := reverseLowered.funcs,
    methods := reverseLowered.methods,
    heap := [(.base ⟨0⟩, hu64 (n : Int)), (.base ⟨1⟩, hu64 (seed : Int)),
             (.base ⟨2⟩, hu64 0), (.base ⟨3⟩, hSliceCell n),
             (.base ⟨4⟩, hArrCell n l), (.base ⟨5⟩, hSliceCell n),
             (.base ⟨6⟩, hu64 siv), (.base ⟨7⟩, bcell false),
             (.base ⟨8⟩, hSliceCell n), (.base ⟨9⟩, intcell rif),
             (.base ⟨10⟩, intcell rjf), (.base ⟨11⟩, bcell false),
             (.base ⟨12⟩, hu64 1), (.base ⟨13⟩, hu64 iv),
             (.base ⟨14⟩, bcell ffv)],
    nextAddr := 15 }

/-- The terminal state: verdict 1 delivered to the result cell. -/
private def tstEndState (n seed : Nat) (siv rif rjf : Int) (l : List Int)
    (iv : Int) : ExecState :=
  { types := reverseLowered.typeDefs.toList,
    functions := reverseLowered.funcs,
    methods := reverseLowered.methods,
    heap := [(.base ⟨0⟩, hu64 (n : Int)), (.base ⟨1⟩, hu64 (seed : Int)),
             (.base ⟨2⟩, hu64 1), (.base ⟨3⟩, hSliceCell n),
             (.base ⟨4⟩, hArrCell n l), (.base ⟨5⟩, hSliceCell n),
             (.base ⟨6⟩, hu64 siv), (.base ⟨7⟩, bcell false),
             (.base ⟨8⟩, hSliceCell n), (.base ⟨9⟩, intcell rif),
             (.base ⟨10⟩, intcell rjf), (.base ⟨11⟩, bcell false),
             (.base ⟨12⟩, hu64 1), (.base ⟨13⟩, hu64 iv),
             (.base ⟨14⟩, bcell false)],
    nextAddr := 15 }

/-! ### Raw run segments (`with_unfolding_all rfl`; splits at the
data-dependent points: the makeSlice apply, each loop's exit test,
the setup store, the two swap reads and stores, the test read, the
check-if delivery). -/

private theorem revH_E1_raw (nv sv : Int) (ch : Choices) :
    stepFnIter 10 (revHSeed nv sv) revHC₀ ch
      = .ok (.retV (.int nv .uint64)
          (.stmtOpK (.makeSlice (.int .uint64) false) 1
            [.addr (.base ⟨3⟩)] [] envC4H
            (.seq [hS2, hS3, hS4, hS5, hS6, hS7] envC4H
              (.frame [] [] [] [] .stop))),
        { types := reverseLowered.typeDefs.toList,
          functions := reverseLowered.funcs,
          methods := reverseLowered.methods,
          heap := [(.base ⟨0⟩, hu64 nv), (.base ⟨1⟩, hu64 sv),
                   (.base ⟨2⟩, hu64 0),
                   (.base ⟨3⟩, ⟨some (.slice (.int .uint64)),
                     .slice ⟨none, 0, 0, 0⟩⟩)],
          nextAddr := 4 }, ch) := by
  with_unfolding_all rfl

/-- **The makeSlice apply at SYMBOLIC `n`** — the one entry-phase
branch point (the machine's non-negativity check on the length). The
backing is `n` zeros (`buildDefaultArrayValue_int`). -/
private theorem revH_make_apply (n seed : Nat) (hn : n < 2 ^ 63)
    (ch : Choices) :
    applyStmtOp (σE1st n seed) ch (.makeSlice (.int .uint64) false) 1
      [.addr (.base ⟨3⟩), .int (n : Nat) .uint64]
      = .ok (σMake n seed, ch) := by
  have hnat : ∀ s : String,
      natFromNonnegativeInt s ((n : Nat) : Int) = .ok n := by
    intro s
    simp only [natFromNonnegativeInt]
    rw [if_neg (by omega : ¬ (((n : Nat) : Int) < 0))]
    rfl
  have hback := GoLean.Iris.buildDefaultArrayValue_int (σE1st n seed) .uint64 n
  simp only [applyStmtOp, applyStmtOpCore, valueAsInt, Bind.bind,
    Except.bind, pure, Except.pure, hnat, hback]
  rw [if_neg (by omega : ¬ (n < n))]
  simp only [ExecState.alloc, ExecState.freshLoc, valueAsLoc, Except.bind,
    storeLoc, Heap.lookup, normalizeValueForTy, normalizeValueForTyFuel,
    typeResolutionFuel, Heap.set, pure, Except.pure, σE1st, σMake,
    hArrCell, hSliceCell, hSlice, hu64, List.map_replicate]
  rfl

/-- The makeSlice machine step, conditioned on the apply fact. -/
private theorem stepFn_makeSlice_step {σ σ' : ExecState} {n : Nat}
    {tv : GoValue} {env : LocalEnv} {k : Cont} {ch : Choices}
    (happly : applyStmtOp σ ch (.makeSlice (.int .uint64) false) 1
      [tv, .int (n : Nat) .uint64] = .ok (σ', ch)) :
    stepFn σ (.retV (.int (n : Nat) .uint64)
      (.stmtOpK (.makeSlice (.int .uint64) false) 1 [tv] [] env k)) ch
      = .ok (.next k, σ', ch) := by
  simp only [stepFn, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append]
  rw [happly]
  rfl

private theorem revH_E2_raw (n seed : Nat) (ch : Choices) :
    stepFnIter 42 (σMake n seed)
      (.next (.seq [hS2, hS3, hS4, hS5, hS6, hS7] envC4H
        (.frame [] [] [] [] .stop))) ch
      = .ok (suHeadCfg, suState n seed (List.replicate n 0) 0 true, ch) := by
  with_unfolding_all rfl

/-- Setup first-pass dispatch: head with the flag up → the exit test. -/
private theorem su_A0_raw (n seed : Nat) (l : List Int) (iv : Int)
    (ch : Choices) :
    stepFnIter 25 (suState n seed l iv true) suHeadCfg ch
      = .ok (.retV (.bool (decide (iv < (n : Int)))) suCmpCont,
          suState n seed l iv false, ch) := by
  with_unfolding_all rfl

/-- Setup later-pass dispatch: `i++`, then the exit test. -/
private theorem su_A1_raw (n seed : Nat) (l : List Int) (iv : Int)
    (ch : Choices) :
    stepFnIter 29 (suState n seed l iv false) suHeadCfg ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < (n : Int)))) suCmpCont,
          suState n seed l
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false, ch) := by
  with_unfolding_all rfl

/-- Setup fill phase 1: test true → target + RHS evaluated, the store
pending (`seed + i`, wrapped once by the add). -/
private theorem su_B1_raw (n seed : Nat) (l : List Int) (iv : Int)
    (ch : Choices) :
    stepFnIter 18 (suState n seed l iv false) (.retV (.bool true) suCmpCont)
      ch
      = .ok (.next (.storeK [suRef n iv]
            [.int (IntKind.normalize .uint64 ((seed : Int) + iv)) .uint64]
            (.seqn #[]) suEnv2 suSwTail),
          suState n seed l iv false, ch) := by
  with_unfolding_all rfl

/-- Setup fill tail: store done → back to the loop head. -/
private theorem su_D_raw (n seed : Nat) (l : List Int) (iv : Int)
    (ch : Choices) :
    stepFnIter 5 (suState n seed l iv false)
      (.next (.storeK [] [] (.seqn #[]) suEnv2 suSwTail)) ch
      = .ok (suHeadCfg, suState n seed l iv false, ch) := by
  with_unfolding_all rfl

/-- Setup exit → the reverse call's frame entered, `i`/`j` declared,
`len(s)` at its apply point. -/
private theorem su_X_raw (n seed : Nat) (l : List Int) (iv : Int)
    (ch : Choices) :
    stepFnIter 30 (suState n seed l iv false) (.retV (.bool false) suCmpCont)
      ch
      = .ok (.retV (hSlice n)
          (.strictK (.lengthOf (some (.slice (.int .uint64)))) [] []
            revEnvMidH (.strictK .sub [] [.intLit 1 .int] revEnvMidH
              entryRhsKH)),
        σRevEntry n seed l iv, ch) := by
  with_unfolding_all rfl

/-- Reverse entry tail: `len - 1` delivered → `i, j` stored, the flag
block run, the reverse loop head. -/
private theorem su_Y_raw (n seed : Nat) (l : List Int) (siv : Int)
    (ch : Choices) :
    stepFnIter 22 (σRevEntry n seed l siv)
      (.retV (.int (n : Nat) .int)
        (.strictK .sub [] [.intLit 1 .int] revEnvMidH entryRhsKH)) ch
      = .ok (revHHeadCfg,
          hrevState n seed siv l 0
            (IntKind.normalize .int
              (IntKind.normalize .int ((n : Int) - 1))) true, ch) := by
  with_unfolding_all rfl

/-- Reverse first-pass dispatch. -/
private theorem rh_A0_raw (n seed : Nat) (siv : Int) (l : List Int)
    (iv jv : Int) (ch : Choices) :
    stepFnIter 25 (hrevState n seed siv l iv jv true) revHHeadCfg ch
      = .ok (.retV (.bool (decide (iv < jv))) revHCmpCont,
          hrevState n seed siv l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Reverse later-pass dispatch: `i, j = i+1, j-1`, then the test. -/
private theorem rh_A1_raw (n seed : Nat) (siv : Int) (l : List Int)
    (iv jv : Int) (ch : Choices) :
    stepFnIter 40 (hrevState n seed siv l iv jv false) revHHeadCfg ch
      = .ok (.retV (.bool (decide
              (IntKind.normalize .int (IntKind.normalize .int (iv + 1))
                < IntKind.normalize .int (IntKind.normalize .int (jv - 1)))))
            revHCmpCont,
          hrevState n seed siv l
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            (IntKind.normalize .int (IntKind.normalize .int (jv - 1)))
            false, ch) := by
  with_unfolding_all rfl

/-- Swap phase 1a: test true → the first index-read apply (`s[j]`). -/
private theorem rh_swapA_raw (n seed : Nat) (siv : Int) (l : List Int)
    (iv jv : Int) (ch : Choices) :
    stepFnIter 20 (hrevState n seed siv l iv jv false)
      (.retV (.bool true) revHCmpCont) ch
      = .ok (.retV (.int jv .int)
            (.strictK .indexGet [hSlice n] [] envIn2H (hRhsK1 n iv jv)),
          hrevState n seed siv l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase 1b: first read delivered → the second read apply. -/
private theorem rh_swapB_raw (n seed : Nat) (siv : Int) (l : List Int)
    (iv jv : Int) (wj : GoValue) (ch : Choices) :
    stepFnIter 5 (hrevState n seed siv l iv jv false)
      (.retV wj (hRhsK1 n iv jv)) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [hSlice n] [] envIn2H (hRhsK2 n iv jv wj)),
          hrevState n seed siv l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase 1 → 2: both reads banked, the stores begin. -/
private theorem rh_swapC_raw (n seed : Nat) (siv : Int) (l : List Int)
    (iv jv : Int) (wj wi : GoValue) (ch : Choices) :
    stepFnIter 1 (hrevState n seed siv l iv jv false)
      (.retV wi (hRhsK2 n iv jv wj)) ch
      = .ok (.next (.storeK [hRefv n iv, hRefv n jv] [wj, wi] (.seqn #[])
            envIn2H swTailH),
          hrevState n seed siv l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap tail: stores done → back to the loop head. -/
private theorem rh_swapD_raw (n seed : Nat) (siv : Int) (l : List Int)
    (iv jv : Int) (ch : Choices) :
    stepFnIter 5 (hrevState n seed siv l iv jv false)
      (.next (.storeK [] [] (.seqn #[]) envIn2H swTailH)) ch
      = .ok (revHHeadCfg, hrevState n seed siv l iv jv false, ch) := by
  with_unfolding_all rfl

/-- Reverse exit → frame exit, `ok := 1`, the test loop's counter and
flag declared, the test loop head. -/
private theorem rh_X_raw (n seed : Nat) (siv : Int) (l : List Int)
    (iv jv : Int) (ch : Choices) :
    stepFnIter 50 (hrevState n seed siv l iv jv false)
      (.retV (.bool false) revHCmpCont) ch
      = .ok (tstHeadCfg, tstState n seed siv iv jv l 0 true, ch) := by
  with_unfolding_all rfl

/-- Test first-pass dispatch. -/
private theorem tst_A0_raw (n seed : Nat) (siv rif rjf : Int)
    (l : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 25 (tstState n seed siv rif rjf l iv true) tstHeadCfg ch
      = .ok (.retV (.bool (decide (iv < (n : Int)))) tstCmpCont,
          tstState n seed siv rif rjf l iv false, ch) := by
  with_unfolding_all rfl

/-- Test later-pass dispatch: `i++`, then the exit test. -/
private theorem tst_A1_raw (n seed : Nat) (siv rif rjf : Int)
    (l : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 29 (tstState n seed siv rif rjf l iv false) tstHeadCfg ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < (n : Int)))) tstCmpCont,
          tstState n seed siv rif rjf l
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false, ch) := by
  with_unfolding_all rfl

/-- Test check phase 1: test true → the element read apply (`s[i]`). -/
private theorem tst_B1_raw (n seed : Nat) (siv rif rjf : Int)
    (l : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 11 (tstState n seed siv rif rjf l iv false)
      (.retV (.bool true) tstCmpCont) ch
      = .ok (.retV (.int iv .uint64)
            (.strictK .indexGet [hSlice n] [] tstEnv2 tstNeqK),
          tstState n seed siv rif rjf l iv false, ch) := by
  with_unfolding_all rfl

/-- Test check phase 2: element banked → the expected value computed
(`seed + ((n-1) - i)`, uint64-wrapped) and the `!=` delivered. -/
private theorem tst_B2_raw (n seed : Nat) (siv rif rjf : Int)
    (l : List Int) (iv wv : Int) (ch : Choices) :
    stepFnIter 15 (tstState n seed siv rif rjf l iv false)
      (.retV (.int wv .uint64) tstNeqK) ch
      = .ok (.retV (.bool (!(wv ==
            IntKind.normalize .uint64 ((seed : Int) +
              IntKind.normalize .uint64
                (IntKind.normalize .uint64 ((n : Int) - 1) - iv)))))
            tstIfK,
          tstState n seed siv rif rjf l iv false, ch) := by
  with_unfolding_all rfl

/-- Test check phase 3 (the equal case): the else branch drains back to
the loop head. -/
private theorem tst_B3_raw (n seed : Nat) (siv rif rjf : Int)
    (l : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 5 (tstState n seed siv rif rjf l iv false)
      (.retV (.bool false) tstIfK) ch
      = .ok (tstHeadCfg, tstState n seed siv rif rjf l iv false, ch) := by
  with_unfolding_all rfl

/-- Test exit: verdict 1 to the result cell, return, barrier exit —
the driver terminal, terminal state pinned. -/
private theorem tst_X_raw (n seed : Nat) (siv rif rjf : Int)
    (l : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 21 (tstState n seed siv rif rjf l iv false)
      (.retV (.bool false) tstCmpCont) ch
      = .ok (.next .stop, tstEndState n seed siv rif rjf l iv, ch) := by
  with_unfolding_all rfl

/-! ### The backing-cell lookups (the conditioned steps' premises) -/

private theorem lookup_su (n seed : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) :
    Heap.lookup (suState n seed l iv ffv).heap (.base ⟨4⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [suState, Heap.lookup, hArrCell]

private theorem lookup_hrev (n seed : Nat) (siv : Int) (l : List Int)
    (iv jv : Int) (ffv : Bool) :
    Heap.lookup (hrevState n seed siv l iv jv ffv).heap (.base ⟨4⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [hrevState, Heap.lookup, hArrCell]

private theorem lookup_tst (n seed : Nat) (siv rif rjf : Int)
    (l : List Int) (iv : Int) (ffv : Bool) :
    Heap.lookup (tstState n seed siv rif rjf l iv ffv).heap (.base ⟨4⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [tstState, Heap.lookup, hArrCell]

/-! ### The setup loop: one fill iteration, then the induction -/

/-- One setup iteration from the exit-test's true delivery at `m`:
fill `s[m] = seed + m` (wrapped), return to the head, dispatch, and
deliver the next test — the family prefix advanced. 53 steps. -/
private theorem su_iter (n seed : Nat) (_hseed : seed < 2 ^ 64)
    (m : Nat) (hn64 : n < 2 ^ 64) (hm : m < n) (ch : Choices) :
    stepFnIter 53 (suState n seed (suList n seed m) ((m : Nat) : Int) false)
      (.retV (.bool true) suCmpCont) ch
      = .ok (.retV (.bool (decide (((m + 1 : Nat) : Int) < (n : Int))))
            suCmpCont,
          suState n seed (suList n seed (m + 1)) ((m + 1 : Nat) : Int) false,
          ch) := by
  have hB1 := su_B1_raw n seed (suList n seed m) ((m : Nat) : Int) ch
  rw [unorm_add_nat seed m] at hB1
  have hw : (0 : Int) ≤ (((seed + m) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + m) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + m) (y := 2 ^ 64) (by omega)
    omega
  have hst := storeTarget_slice_u64 (a := ⟨4⟩) (off := 0) (len := n)
    (cap := n) (i := m) (n := n) (ik := .uint64) (l := suList n seed m)
    (w := (((seed + m) % 2 ^ 64 : Nat) : Int))
    (lookup_su n seed (suList n seed m) ((m : Nat) : Int) false)
    (Nat.le_refl _) hm (by rw [length_suList (by omega)]; omega)
    (length_suList (by omega)) (fun v hv => mem_suList hv) hw
  rw [Nat.zero_add, suList_set hm] at hst
  have hstore : storeTarget
      (suState n seed (suList n seed m) ((m : Nat) : Int) false)
      (suRef n ((m : Nat) : Int))
      (.int (((seed + m) % 2 ^ 64 : Nat) : Int) .uint64)
      = .ok (suState n seed (suList n seed (m + 1)) ((m : Nat) : Int)
          false) := hst
  have hD := su_D_raw n seed (suList n seed (m + 1)) ((m : Nat) : Int) ch
  have hA1 := su_A1_raw n seed (suList n seed (m + 1)) ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hB1
    (stepFnIter_one (stepFn_store_step hstore))) hD) hA1

/-- **The setup loop**, by strong induction on the remaining measure:
from the exit-test delivery at `m` the run reaches the REVERSE LOOP
HEAD with the full family in the backing array, within `53·μ + 53`
steps (the base case runs the setup exit, the call's frame entry and
reverse's prologue). -/
private theorem su_loop (n seed : Nat) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) :
    ∀ μ m : Nat, m + μ = n → ∀ ch : Choices,
    ∃ k : Nat, k ≤ 53 * μ + 53 ∧
      stepFnIter k (suState n seed (suList n seed m) ((m : Nat) : Int) false)
        (.retV (.bool (decide (((m : Nat) : Int) < (n : Int)))) suCmpCont) ch
        = .ok (revHHeadCfg,
            hrevState n seed ((n : Nat) : Int) (revFamily n seed) 0
              ((n : Int) - 1) true, ch) := by
  -- The P5 iterate-then-exit schema (`stepFnIter_iterate_exit`) at
  -- `su_iter` + the exit tower; the `strongRecOn` boilerplate deleted
  -- (G0 item 3a P6 rollback). Statement unchanged.
  intro μ m hm ch
  have hexit : ∀ ch' : Choices, stepFnIter 53
      (suState n seed (suList n seed n) ((n : Nat) : Int) false)
      (.retV (.bool (decide (((n : Nat) : Int) < (n : Int)))) suCmpCont) ch'
      = .ok (revHHeadCfg,
          hrevState n seed ((n : Nat) : Int) (revFamily n seed) 0
            ((n : Int) - 1) true, ch') := by
    intro ch'
    rw [show (decide (((n : Nat) : Int) < (n : Int))) = false from
      decide_eq_false (by omega)]
    have hX := su_X_raw n seed (suList n seed n) ((n : Nat) : Int) ch'
    rw [suList_full] at hX
    have happ : applyStrictOp
        (σRevEntry n seed (revFamily n seed) ((n : Nat) : Int))
        (.lengthOf (some (.slice (.int .uint64)))) [hSlice n]
        = .ok (.int (n : Nat) .int,
            σRevEntry n seed (revFamily n seed) ((n : Nat) : Int)) :=
      applyStrictOp_len_slice (Nat.le_refl n)
    have hlen := stepFnIter_one (ch := ch') (stepFn_strict_apply
      (done := []) (env := revEnvMidH)
      (k := .strictK .sub [] [.intLit 1 .int] revEnvMidH entryRhsKH) happ)
    have hY := su_Y_raw n seed (revFamily n seed) ((n : Nat) : Int) ch'
    rw [inorm_of_range (v := (n : Int) - 1) (by omega) (by omega),
      inorm_of_range (v := (n : Int) - 1) (by omega) (by omega)] at hY
    rw [suList_full]
    exact stepFnIter_chain (stepFnIter_chain hX hlen) hY
  refine ⟨53 * (n - m) + 53, by omega, ?_⟩
  exact stepFnIter_iterate_exit (c := 53) (e := 53) (n := n)
    (T := fun j => suState n seed (suList n seed j) ((j : Nat) : Int) false)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int) < (n : Int))))
      suCmpCont)
    (fun j hj ch'' => by
      rw [show (decide (((j : Nat) : Int) < (n : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact su_iter n seed hseed j (by omega) hj ch'')
    hexit m (by omega) ch

/-! ### The reverse loop: the two-pointer induction at the harness
layout (the standalone module's `revSwap` machinery re-consumed) -/

/-- The reverse-phase exit-test delivery state at iteration `m`. -/
private abbrev hrevCmpState (n seed : Nat) (siv : Int) (m : Nat) :
    ExecState :=
  hrevState n seed siv (revSwap (revFamily n seed) m) ((m : Nat) : Int)
    ((n - 1 - m : Nat) : Int) false

/-- One swap at the harness layout: 35 steps from the true test back
to the head, the partial reversal advanced. -/
private theorem rh_swap_seg (n seed : Nat) (siv : Int) (m : Nat)
    (_hseed : seed < 2 ^ 64) (hm : 2 * m + 1 < n) (ch : Choices) :
    stepFnIter 35 (hrevCmpState n seed siv m)
      (.retV (.bool true) revHCmpCont) ch
      = .ok (revHHeadCfg,
          hrevState n seed siv (revSwap (revFamily n seed) (m + 1))
            ((m : Nat) : Int) ((n - 1 - m : Nat) : Int) false, ch) := by
  have hxs : ∀ v ∈ revFamily n seed, 0 ≤ v ∧ v < 2 ^ 64 :=
    fun v hv => mem_revFamily hv
  have hlenxs : (revFamily n seed).length = n := length_revFamily n seed
  have hlenm : (revSwap (revFamily n seed) m).length = n := by
    rw [length_revSwap, hlenxs]
  have hrangeSwap : ∀ v ∈ revSwap (revFamily n seed) m, 0 ≤ v ∧ v < 2 ^ 64 :=
    fun v hv => hxs v (mem_revSwap hv)
  have hwj_range : 0 ≤ (revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0
      ∧ (revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0 < 2 ^ 64 :=
    hxs _ (getD_mem (by omega))
  have hwi_range : 0 ≤ (revFamily n seed).getD m 0
      ∧ (revFamily n seed).getD m 0 < 2 ^ 64 :=
    hxs _ (getD_mem (by omega))
  have hA := rh_swapA_raw n seed siv (revSwap (revFamily n seed) m)
    ((m : Nat) : Int) ((n - 1 - m : Nat) : Int) ch
  -- the s[j] read
  have hget_j : (⟨(revSwap (revFamily n seed) m).map
      (fun v => .int v .uint64)⟩ : Array GoValue)[0 + (n - 1 - m)]?
      = some (.int ((revFamily n seed).getD
          ((revFamily n seed).length - 1 - m) 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega),
      show n - 1 - m = (revFamily n seed).length - 1 - m from by omega,
      getD_revSwap_hi (by omega)]
  have hread_j := stepFn_strict_apply (done := [hSlice n])
    (env := envIn2H)
    (k := hRhsK1 n ((m : Nat) : Int) ((n - 1 - m : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .int)
      (lookup_hrev n seed siv (revSwap (revFamily n seed) m)
        ((m : Nat) : Int) ((n - 1 - m : Nat) : Int) false)
      (Nat.le_refl n) (by omega : n - 1 - m < n) hget_j)
  have hB := rh_swapB_raw n seed siv (revSwap (revFamily n seed) m)
    ((m : Nat) : Int) ((n - 1 - m : Nat) : Int)
    (.int ((revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0)
      .uint64) ch
  have hget_i : (⟨(revSwap (revFamily n seed) m).map
      (fun v => .int v .uint64)⟩ : Array GoValue)[0 + m]?
      = some (.int ((revFamily n seed).getD m 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega),
      getD_revSwap_lo (by omega)]
  have hread_i := stepFn_strict_apply (done := [hSlice n])
    (env := envIn2H)
    (k := hRhsK2 n ((m : Nat) : Int) ((n - 1 - m : Nat) : Int)
      (.int ((revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0)
        .uint64)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .int)
      (lookup_hrev n seed siv (revSwap (revFamily n seed) m)
        ((m : Nat) : Int) ((n - 1 - m : Nat) : Int) false)
      (Nat.le_refl n) (by omega : m < n) hget_i)
  have hC := rh_swapC_raw n seed siv (revSwap (revFamily n seed) m)
    ((m : Nat) : Int) ((n - 1 - m : Nat) : Int)
    (.int ((revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0)
      .uint64)
    (.int ((revFamily n seed).getD m 0) .uint64) ch
  -- store 1: s[i] := old s[j]
  have hst1 := storeTarget_slice_u64 (a := ⟨4⟩) (off := 0) (len := n)
    (cap := n) (i := m) (n := n) (ik := .int) (l := revSwap (revFamily n seed) m)
    (w := (revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0)
    (lookup_hrev n seed siv (revSwap (revFamily n seed) m) ((m : Nat) : Int)
      ((n - 1 - m : Nat) : Int) false)
    (Nat.le_refl _) (by omega) (by omega) hlenm hrangeSwap hwj_range
  rw [Nat.zero_add] at hst1
  have hstore1 : storeTarget (hrevCmpState n seed siv m)
      (hRefv n ((m : Nat) : Int))
      (.int ((revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0) .uint64)
      = .ok (hrevState n seed siv
          ((revSwap (revFamily n seed) m).set m ((revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0))
          ((m : Nat) : Int) ((n - 1 - m : Nat) : Int) false) := hst1
  -- store 2: s[j] := old s[i]
  have hlen1 : ((revSwap (revFamily n seed) m).set m ((revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0)).length
      = n := by simp [hlenm]
  have hrange1 : ∀ v ∈ (revSwap (revFamily n seed) m).set m ((revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0),
      0 ≤ v ∧ v < 2 ^ 64 := by
    intro v hv
    rcases mem_set_of_mem hv with rfl | hv
    · exact hwj_range
    · exact hrangeSwap v hv
  have hst2 := storeTarget_slice_u64 (a := ⟨4⟩) (off := 0) (len := n)
    (cap := n) (i := n - 1 - m) (n := n) (ik := .int)
    (l := (revSwap (revFamily n seed) m).set m ((revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0))
    (w := (revFamily n seed).getD m 0)
    (lookup_hrev n seed siv
      ((revSwap (revFamily n seed) m).set m ((revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0))
      ((m : Nat) : Int) ((n - 1 - m : Nat) : Int) false)
    (Nat.le_refl _) (by omega) (by omega) hlen1 hrange1 hwi_range
  rw [Nat.zero_add] at hst2
  have hstore2 : storeTarget
      (hrevState n seed siv
        ((revSwap (revFamily n seed) m).set m ((revFamily n seed).getD ((revFamily n seed).length - 1 - m) 0))
        ((m : Nat) : Int) ((n - 1 - m : Nat) : Int) false)
      (hRefv n ((n - 1 - m : Nat) : Int)) (.int ((revFamily n seed).getD m 0) .uint64)
      = .ok (hrevState n seed siv (revSwap (revFamily n seed) (m + 1)) ((m : Nat) : Int)
          ((n - 1 - m : Nat) : Int) false) := by
    rw [show n - 1 - m = (revFamily n seed).length - 1 - m from by omega] at hst2 ⊢
    rw [← revSwap_step (by omega)]
    exact hst2
  have hD := rh_swapD_raw n seed siv (revSwap (revFamily n seed) (m + 1)) ((m : Nat) : Int)
    ((n - 1 - m : Nat) : Int) ch
  have h1 := stepFnIter_chain hA (stepFnIter_one hread_j)
  have h2 := stepFnIter_chain h1 hB
  have h3 := stepFnIter_chain h2 (stepFnIter_one hread_i)
  have h4 := stepFnIter_chain h3 hC
  have h5 := stepFnIter_chain h4
    (stepFnIter_one (stepFn_store_step hstore1))
  have h6 := stepFnIter_chain h5
    (stepFnIter_one (stepFn_store_step hstore2))
  exact stepFnIter_chain h6 hD

/-- The later-pass dispatch, cleaned: counters advance to
`(m+1, n-1-(m+1))` and the next test delivers. -/
private theorem rh_dispatch (n seed : Nat) (siv : Int) (m : Nat)
    (hn : n < 2 ^ 63) (hm : 2 * m + 1 < n) (ch : Choices) :
    stepFnIter 40 (hrevState n seed siv (revSwap (revFamily n seed) (m + 1))
        ((m : Nat) : Int) ((n - 1 - m : Nat) : Int) false) revHHeadCfg ch
      = .ok (.retV (.bool (decide (((m + 1 : Nat) : Int)
              < ((n - 1 - (m + 1) : Nat) : Int)))) revHCmpCont,
          hrevCmpState n seed siv (m + 1), ch) := by
  have hA := rh_A1_raw n seed siv (revSwap (revFamily n seed) (m + 1))
    ((m : Nat) : Int) ((n - 1 - m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    show ((n - 1 - m : Nat) : Int) - 1
      = ((n - 1 - (m + 1) : Nat) : Int) from by omega] at hA
  rw [inorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    inorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    inorm_of_range (v := ((n - 1 - (m + 1) : Nat) : Int))
      (by omega) (by omega),
    inorm_of_range (v := ((n - 1 - (m + 1) : Nat) : Int))
      (by omega) (by omega)] at hA
  exact hA

/-- **The reverse loop**, by strong induction on `(n-1) - 2m`: from
the exit-test delivery at iteration `m`, the run reaches the TEST LOOP
HEAD — the reversal complete in the backing array, the verdict cell
initialized to 1 — within `75·μ + 50` steps, at some final iteration
count `m'` past the crossing point. -/
private theorem rh_loop (n seed : Nat) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) (siv : Int) :
    ∀ μ m : Nat, μ = (n - 1) - 2 * m → ∀ ch : Choices,
    ∃ (k m' : Nat), k ≤ 75 * μ + 50 ∧ n ≤ 2 * m' + 1 ∧
      stepFnIter k (hrevCmpState n seed siv m)
        (.retV (.bool (decide (((m : Nat) : Int)
          < ((n - 1 - m : Nat) : Int)))) revHCmpCont) ch
        = .ok (tstHeadCfg,
            tstState n seed siv ((m' : Nat) : Int)
              ((n - 1 - m' : Nat) : Int)
              (revSwap (revFamily n seed) m') 0 true, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hμ ch
    rcases Nat.lt_or_ge (2 * m + 1) n with hlt | hge
    · rw [show (decide (((m : Nat) : Int) < ((n - 1 - m : Nat) : Int)))
          = true from decide_eq_true (by
            have : m < n - 1 - m := by omega
            exact_mod_cast this)]
      obtain ⟨k, m', hk, hm', hrun⟩ := ih ((n - 1) - 2 * (m + 1))
        (by omega) (m + 1) rfl ch
      refine ⟨35 + 40 + k, m', by omega, hm', ?_⟩
      exact stepFnIter_chain
        (stepFnIter_chain (rh_swap_seg n seed siv m hseed hlt ch)
          (rh_dispatch n seed siv m hn hlt ch)) hrun
    · rw [show (decide (((m : Nat) : Int) < ((n - 1 - m : Nat) : Int)))
          = false from decide_eq_false (by
            have : ¬ (m < n - 1 - m) := by omega
            exact_mod_cast this)]
      exact ⟨50, m, by omega, by omega,
        rh_X_raw n seed siv (revSwap (revFamily n seed) m) ((m : Nat) : Int)
          ((n - 1 - m : Nat) : Int) ch⟩

/-! ### The test loop: one verified read per iteration -/

/-- One test iteration from the exit-test's true delivery at `m`: read
`s[m]` (the reversed family's element), compute the expected value in
Go's wrapping uint64 arithmetic, find them EQUAL (the verdict stays
1), return to the head, dispatch, deliver the next test. 61 steps. -/
private theorem tst_iter (n seed : Nat) (hn : n < 2 ^ 63)
    (_hseed : seed < 2 ^ 64) (siv rif rjf : Int) (m : Nat) (hm : m < n)
    (ch : Choices) :
    stepFnIter 61 (tstState n seed siv rif rjf
        ((revFamily n seed).reverse) ((m : Nat) : Int) false)
      (.retV (.bool true) tstCmpCont) ch
      = .ok (.retV (.bool (decide (((m + 1 : Nat) : Int) < (n : Int))))
            tstCmpCont,
          tstState n seed siv rif rjf ((revFamily n seed).reverse)
            ((m + 1 : Nat) : Int) false, ch) := by
  have hB1 := tst_B1_raw n seed siv rif rjf ((revFamily n seed).reverse)
    ((m : Nat) : Int) ch
  -- the element read: position m of the reversed family
  have hget : (⟨((revFamily n seed).reverse).map
      (fun v => .int v .uint64)⟩ : Array GoValue)[0 + m]?
      = some (.int ((((seed + (n - 1 - m)) % 2 ^ 64 : Nat)) : Int)
          .uint64) := by
    rw [Nat.zero_add,
      getElem?_mapU _ _ (by rw [List.length_reverse, length_revFamily]; omega),
      getD_reverse_revFamily hm]
  have hread := stepFn_strict_apply (done := [hSlice n])
    (env := tstEnv2) (k := tstNeqK) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .uint64)
      (lookup_tst n seed siv rif rjf ((revFamily n seed).reverse)
        ((m : Nat) : Int) false)
      (Nat.le_refl n) hm hget)
  have hB2 := tst_B2_raw n seed siv rif rjf ((revFamily n seed).reverse)
    ((m : Nat) : Int) ((((seed + (n - 1 - m)) % 2 ^ 64 : Nat)) : Int) ch
  rw [show IntKind.normalize .uint64 ((n : Int) - 1)
        = ((n - 1 : Nat) : Int) from by
      rw [show (n : Int) - 1 = ((n - 1 : Nat) : Int) from by omega]
      exact unorm_of_range (by omega) (by omega),
    show IntKind.normalize .uint64 (((n - 1 : Nat) : Int) - ((m : Nat) : Int))
        = ((n - 1 - m : Nat) : Int) from by
      rw [show ((n - 1 : Nat) : Int) - ((m : Nat) : Int)
          = ((n - 1 - m : Nat) : Int) from by omega]
      exact unorm_of_range (by omega) (by omega),
    unorm_add_nat seed (n - 1 - m),
    show ((((seed + (n - 1 - m)) % 2 ^ 64 : Nat) : Int) ==
        (((seed + (n - 1 - m)) % 2 ^ 64 : Nat) : Int)) = true from
      beq_self_eq_true _,
    Bool.not_true] at hB2
  have hB3 := tst_B3_raw n seed siv rif rjf ((revFamily n seed).reverse)
    ((m : Nat) : Int) ch
  have hA1 := tst_A1_raw n seed siv rif rjf ((revFamily n seed).reverse)
    ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  have h1 := stepFnIter_chain hB1 (stepFnIter_one hread)
  have h2 := stepFnIter_chain h1 hB2
  have h3 := stepFnIter_chain h2 hB3
  exact stepFnIter_chain h3 hA1

/-- **The test loop**: from the exit-test delivery at `m`, the run
reaches the driver terminal with the verdict 1 delivered, within
`61·μ + 21` steps. -/
private theorem tst_loop (n seed : Nat) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) (siv rif rjf : Int) :
    ∀ μ m : Nat, m + μ = n → ∀ ch : Choices,
    ∃ k : Nat, k ≤ 61 * μ + 21 ∧
      stepFnIter k (tstState n seed siv rif rjf
          ((revFamily n seed).reverse) ((m : Nat) : Int) false)
        (.retV (.bool (decide (((m : Nat) : Int) < (n : Int)))) tstCmpCont)
        ch
        = .ok (.next .stop,
            tstEndState n seed siv rif rjf ((revFamily n seed).reverse)
              ((n : Nat) : Int), ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hm ch
    rcases Nat.lt_or_ge m n with hlt | hge
    · rw [show (decide (((m : Nat) : Int) < (n : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      obtain ⟨k, hk, hrun⟩ := ih (μ - 1) (by omega) (m + 1) (by omega) ch
      exact ⟨61 + k, by omega, stepFnIter_chain
        (tst_iter n seed hn hseed siv rif rjf m hlt ch) hrun⟩
    · have hmn : m = n := by omega
      subst hmn
      rw [show (decide (((m : Nat) : Int) < (m : Int))) = false from
        decide_eq_false (by omega)]
      exact ⟨21, by omega, tst_X_raw m seed siv rif rjf
        ((revFamily m seed).reverse) ((m : Nat) : Int) ch⟩

/-! ### The canonical run, end to end -/

/-- **The harness run**: from the post-prelude state, the harness
completes at the driver terminal within `189·n + 260` steps —
terminal state pinned up to reverse's parked final counters, verdict
1 in the result cell. -/
private theorem revH_runs (n seed : Nat) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) (ch : Choices) :
    ∃ (k : Nat) (rif rjf : Int), k ≤ 189 * n + 260 ∧
      stepFnIter k (revHSeed (n : Int) (seed : Int)) revHC₀ ch
        = .ok (.next .stop,
            tstEndState n seed ((n : Nat) : Int) rif rjf
              ((revFamily n seed).reverse) ((n : Nat) : Int), ch) := by
  -- entry: prelude state → the setup loop head
  have hE1 := revH_E1_raw (n : Int) (seed : Int) ch
  have hmk := stepFnIter_one
    (stepFn_makeSlice_step (env := envC4H)
      (k := .seq [hS2, hS3, hS4, hS5, hS6, hS7] envC4H
        (.frame [] [] [] [] .stop))
      (revH_make_apply n seed hn ch))
  have hE2 := revH_E2_raw n seed ch
  have hA0 := su_A0_raw n seed (List.replicate n 0) 0 ch
  obtain ⟨k1, hk1, hsu⟩ := su_loop n seed hn hseed n 0 (by omega) ch
  rw [suList_zero, show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hsu
  have hentry := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hE1 hmk) hE2) hA0) hsu
  -- the reverse phase's first test
  have hrA0 := rh_A0_raw n seed ((n : Nat) : Int) (revFamily n seed) 0
    ((n : Int) - 1) ch
  rcases Nat.lt_or_ge n 2 with hshort | hlong
  · -- n ≤ 1: the first test fails; nothing swaps
    rw [show (decide ((0 : Int) < (n : Int) - 1)) = false from
      decide_eq_false (by omega)] at hrA0
    have hX := rh_X_raw n seed ((n : Nat) : Int) (revFamily n seed) 0
      ((n : Int) - 1) ch
    have hrevshort : (revFamily n seed).reverse = revFamily n seed :=
      reverse_short (by rw [length_revFamily]; omega)
    have htA0 := tst_A0_raw n seed ((n : Nat) : Int) 0 ((n : Int) - 1)
      (revFamily n seed) 0 ch
    obtain ⟨k2, hk2, htst⟩ := tst_loop n seed hn hseed ((n : Nat) : Int) 0
      ((n : Int) - 1) n 0 (by omega) ch
    rw [hrevshort, show (((0 : Nat) : Int)) = (0 : Int) from rfl] at htst
    refine ⟨10 + 1 + 42 + 25 + k1 + (25 + 50 + 25 + k2), 0, (n : Int) - 1,
      by omega, ?_⟩
    rw [hrevshort]
    exact stepFnIter_chain hentry (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain hrA0 hX) htA0) htst)
  · -- n ≥ 2: enter the two-pointer loop at iteration 0
    rw [show (decide ((0 : Int) < (n : Int) - 1)) = true from
      decide_eq_true (by omega)] at hrA0
    obtain ⟨k2, m', hk2, hm', hrh⟩ := rh_loop n seed hn hseed
      ((n : Nat) : Int) ((n - 1) - 2 * 0) 0 rfl ch
    simp only [hrevCmpState] at hrh
    rw [show revSwap (revFamily n seed) 0 = revFamily n seed from
        revSwap_zero _,
      show (((0 : Nat) : Int)) = (0 : Int) from rfl,
      show ((n - 1 - 0 : Nat) : Int) = (n : Int) - 1 from by omega,
      show (decide ((0 : Int) < (n : Int) - 1)) = true from
        decide_eq_true (by omega)] at hrh
    have hrev := stepFnIter_chain hrA0 hrh
    -- the reversal is complete at the crossing point
    rw [revSwap_reverse (by rw [length_revFamily]; omega)] at hrev
    have htA0 := tst_A0_raw n seed ((n : Nat) : Int) ((m' : Nat) : Int)
      ((n - 1 - m' : Nat) : Int) ((revFamily n seed).reverse) 0 ch
    obtain ⟨k3, hk3, htst⟩ := tst_loop n seed hn hseed ((n : Nat) : Int)
      ((m' : Nat) : Int) ((n - 1 - m' : Nat) : Int) n 0 (by omega) ch
    rw [show (((0 : Nat) : Int)) = (0 : Int) from rfl] at htst
    refine ⟨10 + 1 + 42 + 25 + k1 + (25 + k2 + 25 + k3),
      ((m' : Nat) : Int), ((n - 1 - m' : Nat) : Int), by omega, ?_⟩
    exact stepFnIter_chain hentry (stepFnIter_chain (stepFnIter_chain
      hrev htA0) htst)

/-! ### The user-facing statement (§11) -/

/-- **THE HEADLINE (§11 harness form)**: for every `n < 2^63` (Go's
`int` domain for lengths — `make([]uint64, n)` panics past it) and
every `seed < 2^64` (the full uint64 domain), running the three-phase
Go harness `reverse_harness(n, seed)` through the machine's native
function entry — empty-heap state, both arguments at the call
boundary — completes normally past one fuel bound, at every
nondeterminism-choice stream, and RETURNS the verdict 1: the test
phase, IN GO and inside the verified footprint, checked element-wise
that `reverse` turned `[seed, seed+1, …, seed+(n-1)] (mod 2^64)` into
its reversal.

INPUT-FAMILY HONESTY (§11, recorded): the quantification is over the
scalars `(n, seed)` — the input family `revFamily n seed`, honestly
weaker than ∀xs over arbitrary contents (the choice-consuming input
pick is designed, not built; `reverse_framed` above keeps the ∀xs
claim proof-side). The wrapping family is deliberate: `seed + i`
wraps at `2^64`, so the family covers wrap boundaries — the corpus
oracle rows exercise the same harness at concrete arguments,
including a near-`2^63` seed. -/
theorem reverse_ok_v1 (n seed : Nat) (hn : n < 2 ^ 63) (hseed : seed < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel reverseLowered.typeDefs.toList
          reverseLowered.funcs reverseHarnessFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
          reverseLowered.methods ch
        = .ok { values := #[.int 1 .uint64] } := by
  refine ⟨189 * n + 260, fun fuel hfuel ch => ?_⟩
  obtain ⟨k, rif, rjf, hk, hrun⟩ := revH_runs n seed hn hseed ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [revH_entry_eq, unorm_of_range (v := (n : Int)) (by omega) (by omega),
    unorm_of_range (v := (seed : Int)) (by omega) (by omega),
    hfold, runConfig_next_stop]
  with_unfolding_all rfl

/-- **The D1 run-conditioned twin**: any successful completion of the
harness entry, at any fuel and any choice stream, returns the verdict
1 — derived from `reverse_ok` via `harness_readout_of_total` (the
total headline already determines every completion). -/
theorem reverse_readout_v1 (n seed : Nat) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) :
    ∀ (fuel : Nat) (ch : Choices) (r : Result),
      runFunctionWithContextM fuel reverseLowered.typeDefs.toList
          reverseLowered.funcs reverseHarnessFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
          reverseLowered.methods ch
        = .ok r →
      r = { values := #[.int 1 .uint64] } :=
  harness_readout_of_total (reverse_ok_v1 n seed hn hseed)

end GoLean.Examples.Reverse
