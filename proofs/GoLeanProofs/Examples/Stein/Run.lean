import GoLeanProofs.Examples.SteinProgram
import GoLeanProofs.Examples.Stein.Pure
import GoLeanProofs.SliceMem
import GoLeanProofs.StepKit
import GoLeanProofs.FuelMeasure
import GoLeanProofs.EntryEq

/-!
# Stein — Run: the machine-execution half of the binary-GCD example

The machine walk of `stein_harness(a, b)` through the pinned lowering
(`SteinProgram`), phase by phase against the pure branch equations of
`Examples/Stein/Pure.lean`, ending in the public run theorem
`stein_runs`: from the machine entry's post-prelude seed, execution
reaches the entry terminal within `steinFuel a b` steps with
`Nat.gcd a b` in the harness result cell.

## Address layout (probe-verified, tracer `.tmp/stein-trace-12-18.txt`)

The harness prelude: `a`@0, `b`@1, harness `$res0`@2; harness body:
`r`@3. The `steinGCD` frame: `a`@4, `b`@5, `$res0`@6; then `shift`@7
and loop 1's `$forFirst`@8 — allocator at 9 at the loop-1 head. Every
loop iteration then GROWS the heap: each `isEven(x)` call allocates its
caller's `$cN` condition cell plus a 2-cell frame (`x`, `$res0`), and
loops 2/3 allocate their own `$forFirst` cells at run-dependent
addresses (loop 3's INNER loop allocates a fresh one per OUTER
iteration). No concrete heap shape exists at any loop head, so the
proof is in the footprint style (the FibMemo/Rec route): states are
`stSt h na` over an abstract heap, reads are `Heap.lookup` hypotheses,
writes are `Heap.set`, allocations append, and whole-heap freshness
rides as `FreshFrom h na`.

## Phase structure (each loop proved by strong induction against the
matching pure function's branch equations)

* entry + the two early-return guards (`a = 0` → `b`, `b = 0` → `a`) —
  concrete-heap `with_unfolding_all rfl` segments;
* LOOP 1 (strip shared twos, counting in `shift`) ↔ `commonTwos`;
* LOOP 2 (strip `a`'s twos) ↔ `stripTwos`;
* LOOP 3 (outer subtract loop, inner strip of `b`) ↔ `steinSub` with
  the inner induction against `stripTwos`;
* epilogue `$res0 = a << shift` + the two frame exits, reassembled via
  `steinSpec_eq_gcd`.

The fuel bound `steinFuel` is a BOUND, not a measurement — an affine
form in `a + b` (docstring at the def).

## Kit notes (recorded, not worked around silently)

* The `fmSt`/`FreshFrom`/`lookup_set_*` footprint vocabulary is
  re-declared privately here (fourth consumer counting FibMemo's and
  the wordcount/histogram shards) — the "recursive-call frame
  induction" pack in `Examples/FibMemo/Rec.lean`'s kit-candidate note
  now has a second full consumer and is ripe for a `StepKit` lift.
* `st_frame_exit_step` is a private variant of FibMemo's
  `fm_frame_exit_step`: the kit has no frame-exit step, and the lemma
  must take a CONCRETE `.base` result address (`loadLoc` is stuck at a
  generic `Loc`).
* Pitfall (cost a debugging round): `Heap` is an `abbrev` for
  `List (Loc × HeapCell)`, so dot-notation `.set` on an APPEND
  (`(h ++ l).set …`) resolves to `List.set`, not `Heap.set` — spell
  `Heap.set` explicitly on append-shaped heaps.
-/

namespace GoLean.Examples.Stein

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Vocabulary (the footprint-style privates; the `fmSt`/`FreshFrom`
vocabulary re-declared privately per the kit-gap note in
`Examples/FibMemo/Rec.lean` — a recursive-frame pack has one consumer
per module today and is NOT yet lifted to `StepKit`) -/

private abbrev tU : Ty := .int .uint64

/-- uint64 cell -/
private abbrev u64c (v : Int) : HeapCell := ⟨some tU, .int v .uint64⟩
/-- bool cell -/
private abbrev bcc (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩

/-- The machine state of the `stein` program at heap `h`, next address
`na` — the footprint style's single state former. -/
private def stSt (h : Heap) (na : Nat) : ExecState :=
  { types := steinLowered.typeDefs.toList,
    functions := steinLowered.funcs,
    methods := steinLowered.methods,
    heap := h, nextAddr := na }

/-- Whole-heap freshness at and above `na`. -/
private def FreshFrom (h : Heap) (na : Nat) : Prop :=
  ∀ x : Nat, na ≤ x → Heap.lookup h (.base ⟨x⟩) = none

private theorem FreshFrom.mono {h : Heap} {na na' : Nat} (hle : na ≤ na')
    (hf : FreshFrom h na) : FreshFrom h na' :=
  fun x hx => hf x (by omega)

private theorem FreshFrom.push {h : Heap} {na : Nat} {c : HeapCell}
    (hf : FreshFrom h na) :
    FreshFrom (h ++ [(.base ⟨na⟩, c)]) (na + 1) := by
  intro x hx
  rw [lookup_append_right (hf x (by omega)),
    lookup_cons_ne (base_beq_false (by omega : na ≠ x))]
  rfl

private theorem FreshFrom.push3 {h : Heap} {na : Nat} {c c' c'' : HeapCell}
    (hf : FreshFrom h na) :
    FreshFrom (h ++ [(.base ⟨na⟩, c), (.base ⟨na + 1⟩, c'),
      (.base ⟨na + 2⟩, c'')]) (na + 3) := by
  intro x hx
  rw [lookup_append_right (hf x (by omega)),
    lookup_cons_ne (base_beq_false (by omega : na ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ x))]
  rfl

/-- A `set` below the boundary preserves freshness. -/
private theorem FreshFrom.set {h : Heap} {na a : Nat} {c : HeapCell}
    (hf : FreshFrom h na) (ha : a < na) :
    FreshFrom (Heap.set h (.base ⟨a⟩) c) na := by
  intro x hx
  rw [Machine.Heap.lookup_set_ne
    (by simp only [ne_eq, Loc.base.injEq, Addr.mk.injEq]; omega
      : (Loc.base ⟨a⟩ : Loc) ≠ .base ⟨x⟩)]
  exact hf x hx

/-- A present cell sits below the freshness boundary. -/
private theorem FreshFrom.lt_of_lookup {h : Heap} {na a : Nat}
    {c : HeapCell} (hf : FreshFrom h na)
    (hl : Heap.lookup h (.base ⟨a⟩) = some c) : a < na := by
  cases Nat.lt_or_ge a na with
  | inl h => exact h
  | inr h => rw [hf a h] at hl; cases hl

/-- Lookup through a `set` at a DIFFERENT base address. -/
private theorem lookup_set_other {h : Heap} {a x : Nat} {c : HeapCell}
    (hne : a ≠ x) :
    Heap.lookup (Heap.set h (.base ⟨a⟩) c) (.base ⟨x⟩)
      = Heap.lookup h (.base ⟨x⟩) :=
  Machine.Heap.lookup_set_ne
    (by simp only [ne_eq, Loc.base.injEq, Addr.mk.injEq]; omega)

/-- Lookup at the `set` address itself. -/
private theorem lookup_set_self {h : Heap} {l : Loc} {c : HeapCell} :
    Heap.lookup (Heap.set h l c) l = some c := by
  induction h with
  | nil => simp [Heap.set, Heap.lookup]
  | cons p rest ih =>
      obtain ⟨loc, old⟩ := p
      simp only [Heap.set]
      cases hb : (loc == l) with
      | true => simp [Heap.lookup, eq_of_beq hb]
      | false => simp [Heap.lookup, hb, ih]

/-- `Heap.set` skips a mismatching head cell. -/
private theorem set_cons_ne {l needle : Loc} {c₀ c : HeapCell} {rest : Heap}
    (hne : (l == needle) = false) :
    Heap.set ((l, c₀) :: rest) needle c
      = (l, c₀) :: Heap.set rest needle c := by
  simp [Heap.set, hne]

/-- `Heap.set` replaces a matching head cell. -/
private theorem set_cons_self {l : Loc} {c c' : HeapCell} {rest : Heap} :
    Heap.set ((l, c) :: rest) l c' = (l, c') :: rest := by
  simp [Heap.set]

private theorem lookup_cons_self {l : Loc} {c : HeapCell} {rest : Heap} :
    Heap.lookup ((l, c) :: rest) l = some c := by
  simp [Heap.lookup]

/-! ## The pinned callee `Func`s, transcribed

`steinHarnessFuncRun` is the harness transcription for THIS module's
`derive_entry_eq` (the root `Examples/Stein.lean` carries its own
`steinHarnessFunc`, byte-identical — this module must not import the
root, which imports it; the two are tied to the same lowering entry by
`rfl` pins, so the root bridges by `rfl`). -/

def steinHarnessFuncRun : Func :=
  { id := { key := "stein_harness" },
    args := #[{ id := "a", typ := tU }, { id := "b", typ := tU }],
    results := #[{ id := "$res0", typ := tU }],
    body := .block #[]
      #[.seqn #[.initialization { id := "r", typ := tU },
                .call #[.var "r"] ⟨"steinGCD"⟩ #[.var "a", .var "b"]],
        .seqn #[.assign (.var "$res0") (.var "r"), .returnStmt]],
    variadic := false, wrapper := false }

/-- The lowering pin: the transcription IS the frontend's harness. -/
theorem steinHarnessFuncRun_pin :
    findFunctionIn? steinLowered.funcs ⟨"stein_harness"⟩
      = some steinHarnessFuncRun := rfl

private def isEvenFunc : Func :=
  { id := { key := "isEven" },
    args := #[{ id := "x", typ := tU }],
    results := #[{ id := "$res0", typ := .bool }],
    body := .block #[]
      #[.seqn #[.assign (.var "$res0")
                  (.eqCmp tU (.mod (.var "x") (.intLit 2 .uint64))
                    (.intLit 0 .uint64)),
                .returnStmt]],
    variadic := false, wrapper := false }

private theorem isEvenFunc_pin :
    findFunctionIn? steinLowered.funcs ⟨"isEven"⟩ = some isEvenFunc := rfl

/-! ### The `steinGCD` body pieces, named (transcribed from the pinned
lowering; the pin below ties the whole `Func`) -/

/-- The shared `for`-loop first-iteration dispatch. -/
private abbrev lpDispatch : Stmt :=
  .ifThenElse (.var "$forFirst")
    (.assign (.var "$forFirst") (.boolLit false)) (.seqn #[])

private abbrev guard1 : Stmt :=
  .ifThenElse (.eqCmp tU (.var "a") (.intLit 0 .uint64))
    (.block #[] #[.seqn #[.assign (.var "$res0") (.var "b"), .returnStmt]])
    (.seqn #[])

private abbrev guard2 : Stmt :=
  .ifThenElse (.eqCmp tU (.var "b") (.intLit 0 .uint64))
    (.block #[] #[.seqn #[.assign (.var "$res0") (.var "a"), .returnStmt]])
    (.seqn #[])

private abbrev shiftSeqn : Stmt :=
  .seqn #[.initialization { id := "shift", typ := tU },
          .assign (.var "shift") (.intLit 0 .uint64)]

/-- The isEven call pair: `$cN := isEven(xv)` (init + call). -/
private abbrev ieSeqn (tv xv : String) : Stmt :=
  .seqn #[.initialization { id := tv, typ := .bool },
          .call #[.var tv] ⟨"isEven"⟩ #[.var xv]]

private abbrev c0Seqn : Stmt := ieSeqn "$c0" "a"
private abbrev c1Seqn : Stmt := ieSeqn "$c1" "b"
private abbrev c3Seqn : Stmt := ieSeqn "$c3" "a"
private abbrev c4Seqn : Stmt := ieSeqn "$c4" "b"

private abbrev c2Seqn : Stmt :=
  .seqn #[.initialization { id := "$c2", typ := .bool },
          .assign (.var "$c2") (.var "$c0")]

private abbrev c2AsgSeqn : Stmt :=
  .seqn #[.assign (.var "$c2") (.var "$c1")]

private abbrev c1Blk : Stmt := .block #[] #[c1Seqn, c2AsgSeqn]

/-- Loop 1's condPre: `$c0 := isEven(a); $c2 := $c0; if $c2 { $c1 :=
isEven(b); $c2 = $c1 }` — the frontend's normalization of the
short-circuit `isEven(a) && isEven(b)`. -/
private abbrev condSeqn1 : Stmt :=
  .seqn #[c0Seqn, c2Seqn, .ifThenElse (.var "$c2") c1Blk (.seqn #[])]

private abbrev innerIf1 : Stmt := .ifThenElse (.var "$c2") c1Blk (.seqn #[])

private abbrev exitIf1 : Stmt :=
  .ifThenElse (.var "$c2") (.seqn #[]) .breakStmt

private abbrev asgHalf (x : String) : Stmt :=
  .assign (.var x) (.div (.var x) (.intLit 2 .uint64))

private abbrev asgShiftInc : Stmt :=
  .assign (.var "shift") (.add (.var "shift") (.intLit 1 .uint64))

private abbrev iter1Blk : Stmt :=
  .block #[] #[asgHalf "a", asgHalf "b", asgShiftInc]

private abbrev body1 : Stmt :=
  .block #[] #[lpDispatch, condSeqn1, exitIf1, iter1Blk]

private abbrev ffInit : Stmt :=
  .initialization { id := "$forFirst", typ := .bool }
private abbrev ffTrue : Stmt :=
  .assign (.var "$forFirst") (.boolLit true)

private abbrev block1 : Stmt :=
  .block #[] #[ffInit, ffTrue, .while (.boolLit true) body1]

private abbrev condSeqn2 : Stmt := .seqn #[c3Seqn]
private abbrev exitIf2 : Stmt :=
  .ifThenElse (.var "$c3") (.seqn #[]) .breakStmt
private abbrev iter2Blk : Stmt := .block #[] #[asgHalf "a"]
private abbrev body2 : Stmt :=
  .block #[] #[lpDispatch, condSeqn2, exitIf2, iter2Blk]
private abbrev block2 : Stmt :=
  .block #[] #[ffInit, ffTrue, .while (.boolLit true) body2]

private abbrev condSeqn3i : Stmt := .seqn #[c4Seqn]
private abbrev exitIf3i : Stmt :=
  .ifThenElse (.var "$c4") (.seqn #[]) .breakStmt
private abbrev iter3iBlk : Stmt := .block #[] #[asgHalf "b"]
private abbrev body3i : Stmt :=
  .block #[] #[lpDispatch, condSeqn3i, exitIf3i, iter3iBlk]
private abbrev block3i : Stmt :=
  .block #[] #[ffInit, ffTrue, .while (.boolLit true) body3i]

private abbrev swapSeqn : Stmt :=
  .seqn #[.assignMany #[.var "a", .var "b"] #[.var "b", .var "a"]]
private abbrev swapIf : Stmt :=
  .ifThenElse (.greaterCmp (.var "a") (.var "b"))
    (.block #[] #[swapSeqn]) (.seqn #[])
private abbrev subSeqn : Stmt :=
  .seqn #[.assign (.var "b") (.sub (.var "b") (.var "a"))]
private abbrev brkIf : Stmt :=
  .ifThenElse (.eqCmp tU (.var "b") (.intLit 0 .uint64))
    (.block #[] #[.breakStmt]) (.seqn #[])

private abbrev body3Blk : Stmt :=
  .block #[] #[block3i, swapIf, subSeqn, brkIf]
private abbrev body3 : Stmt :=
  .block #[] #[lpDispatch, .seqn #[],
    .ifThenElse (.boolLit true) (.seqn #[]) .breakStmt, body3Blk]
private abbrev block3 : Stmt :=
  .block #[] #[ffInit, ffTrue, .while (.boolLit true) body3]

private abbrev epiSeqn : Stmt :=
  .seqn #[.assign (.var "$res0")
            (.shiftLeft (.var "a") (.var "shift")),
          .returnStmt]

private def steinGCDFunc : Func :=
  { id := { key := "steinGCD" },
    args := #[{ id := "a", typ := tU }, { id := "b", typ := tU }],
    results := #[{ id := "$res0", typ := tU }],
    body := .block #[]
      #[guard1, guard2, shiftSeqn, block1, block2, block3, epiSeqn],
    variadic := false, wrapper := false }

private theorem steinGCDFunc_pin :
    findFunctionIn? steinLowered.funcs ⟨"steinGCD"⟩ = some steinGCDFunc :=
  rfl

/-! ## The entry equation (P4 macro) -/

derive_entry_eq stein_entry_eq steinLowered steinHarnessFuncRun stSeed stC0

/-! ## Environments and continuations (transcribed from the machine,
probe-verified via the tracer snaps; every raw segment below re-checks
the transcription by `rfl`) -/

/-- The harness scope at the call point (`r` declared). -/
private def envH : LocalEnv :=
  [[("r", .base ⟨3⟩)],
   [("$res0", .base ⟨2⟩), ("b", .base ⟨1⟩), ("a", .base ⟨0⟩)]]

/-- The `steinGCD` frame scope. -/
private def frScope : Scope :=
  [("$res0", .base ⟨6⟩), ("b", .base ⟨5⟩), ("a", .base ⟨4⟩)]

private def envG : LocalEnv := [frScope]
/-- The gcd body block env. -/
private def envG2 : LocalEnv := [] :: envG
/-- … after `shift` declares. -/
private def envSh : LocalEnv := [[("shift", .base ⟨7⟩)], frScope]

/-- A loop scope: `$forFirst` at `f` over `shift`@7 over the frame. -/
private def envLp (f : Nat) : LocalEnv :=
  [[("$forFirst", .base ⟨f⟩)], [("shift", .base ⟨7⟩)], frScope]

/-- The harness epilogue statement. -/
private abbrev harnessEpi : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "r"), .returnStmt]

/-- The continuation below the whole `steinGCD` frame: deliver `$res0`@6
into `r`@3, run the harness epilogue, exit through the entry barrier. -/
private def KframeTail : Cont :=
  .frame [(.chain [], [.ref "r"])] envH [.base ⟨6⟩] []
    (.seq [harnessEpi] envH (.frame [] [] [] [] .stop false)) false

/-- What remains of the gcd body after loop 1 / 2 / 3 (the governing
sequence's env carries `shift`@7 once `shiftSeqn`'s init ran). -/
private def K1after : Cont :=
  .seq [block2, block3, epiSeqn] envSh KframeTail
private def K2after : Cont := .seq [block3, epiSeqn] envSh KframeTail
private def K3after : Cont := .seq [epiSeqn] envSh KframeTail

/-- Generalized loop pieces (env parametric — loop 3's inner loop runs
at a deeper env than `envLp`). -/
private def loopKg (b : Stmt) (env : LocalEnv) (K : Cont) : Cont :=
  .loop (.boolLit true) b env (.seq [] env K)
private def lpHeadg (b : Stmt) (env : LocalEnv) (K : Cont) : Config :=
  .exec (.while (.boolLit true) b) env (.seq [] env K)
/-- The post-dispatch common point of a loop: the three per-iteration
statements queued under the loop's body scope. -/
private def lpPostg (b : Stmt) (env : LocalEnv) (sA sB sC : Stmt)
    (K : Cont) : Config :=
  .next (.seq [sA, sB, sC] ([] :: env) (loopKg b env K))

/-- Loop 1's fixed pieces (flag always at 8). -/
private def loopK1 : Cont := loopKg body1 (envLp 8) K1after
private def l1Head : Config := lpHeadg body1 (envLp 8) K1after
private def l1Post : Config :=
  lpPostg body1 (envLp 8) condSeqn1 exitIf1 iter1Blk K1after
/-- The loop-1 exit configuration (what `breaking` lands on). -/
private def l1Exit : Config := .next (.seq [] (envLp 8) K1after)

private def loopK2 (f : Nat) : Cont := loopKg body2 (envLp f) K2after
private def l2Head (f : Nat) : Config := lpHeadg body2 (envLp f) K2after
private def l2Post (f : Nat) : Config :=
  lpPostg body2 (envLp f) condSeqn2 exitIf2 iter2Blk K2after
private def l2Exit (f : Nat) : Config := .next (.seq [] (envLp f) K2after)

private abbrev ifTrueStmt : Stmt :=
  .ifThenElse (.boolLit true) (.seqn #[]) .breakStmt
private def loopK3 (f : Nat) : Cont := loopKg body3 (envLp f) K3after
private def l3Head (f : Nat) : Config := lpHeadg body3 (envLp f) K3after
private def l3Post (f : Nat) : Config :=
  lpPostg body3 (envLp f) (.seqn #[]) ifTrueStmt body3Blk K3after
private def l3Exit (f : Nat) : Config := .next (.seq [] (envLp f) K3after)

/-! ## Machine-integer / executable op facts (private; the mod/div
facts keep the LITERAL divisor spelling the lowering produces) -/

private theorem unorm_cast (n : Nat) (hn : n < 2 ^ 64) :
    IntKind.normalize .uint64 ((n : Nat) : Int) = ((n : Nat) : Int) :=
  unorm_nat_of_lt hn

/-- `n % 2` at the literal divisor. -/
private theorem applyStrictOp_mod2 {σ : ExecState} {n : Nat} :
    applyStrictOp σ .mod [.int (n : Int) .uint64, .int 2 .uint64]
      = .ok (.int ((n % 2 : Nat) : Int) .uint64, σ) := by
  have h := applyStrictOp_mod_u64 (σ := σ) (a := n) (b := 2)
    (by omega) (by decide)
  have h2 : ((2 : Nat) : Int) = (2 : Int) := rfl
  rw [h2] at h
  exact h

/-- `n / 2` at the literal divisor. -/
private theorem applyStrictOp_div2 {σ : ExecState} {n : Nat}
    (hn : n < 2 ^ 64) :
    applyStrictOp σ .div [.int (n : Int) .uint64, .int 2 .uint64]
      = .ok (.int ((n / 2 : Nat) : Int) .uint64, σ) := by
  have h2 : (((2 : Int)) == 0) = false := by decide
  have htdiv : Int.tdiv (n : Int) 2 = ((n / 2 : Nat) : Int) := rfl
  have hnorm : IntKind.normalize .uint64 ((n / 2 : Nat) : Int)
      = ((n / 2 : Nat) : Int) := unorm_nat_of_lt (by omega)
  simp only [applyStrictOp, valueAsInt, h2, intBinaryResult,
    valueAsIntValue, htdiv, IntKind.compatibleResult,
    Bool.false_eq_true, if_false, Bind.bind, Except.bind, pure,
    Except.pure]
  simp only [show (IntKind.uint64 == IntKind.uint64) = true from rfl,
    if_true, hnorm]

/-- `s + 1` at the literal increment (no wrap under the bound). -/
private theorem applyStrictOp_add1 {σ : ExecState} {s : Nat}
    (hs : s + 1 < 2 ^ 64) :
    applyStrictOp σ .add [.int (s : Int) .uint64, .int 1 .uint64]
      = .ok (.int ((s + 1 : Nat) : Int) .uint64, σ) := by
  have hcast : (s : Int) + 1 = ((s + 1 : Nat) : Int) := by omega
  have hnorm : IntKind.normalize .uint64 ((s + 1 : Nat) : Int)
      = ((s + 1 : Nat) : Int) := unorm_nat_of_lt hs
  simp only [applyStrictOp, intBinaryResult, valueAsIntValue,
    IntKind.compatibleResult, Bind.bind, Except.bind, pure, Except.pure,
    hcast]
  simp only [show (IntKind.uint64 == IntKind.uint64) = true from rfl,
    if_true, hnorm]

/-- `b - a` at `a ≤ b` (no wrap). -/
private theorem applyStrictOp_subNat {σ : ExecState} {a b : Nat}
    (hab : a ≤ b) (hb : b < 2 ^ 64) :
    applyStrictOp σ .sub [.int (b : Int) .uint64, .int (a : Int) .uint64]
      = .ok (.int ((b - a : Nat) : Int) .uint64, σ) := by
  have hcast : (b : Int) - (a : Int) = ((b - a : Nat) : Int) := by omega
  have hnorm : IntKind.normalize .uint64 ((b - a : Nat) : Int)
      = ((b - a : Nat) : Int) := unorm_nat_of_lt (by omega)
  simp only [applyStrictOp, intBinaryResult, valueAsIntValue,
    IntKind.compatibleResult, Bind.bind, Except.bind, pure, Except.pure,
    hcast]
  simp only [show (IntKind.uint64 == IntKind.uint64) = true from rfl,
    if_true, hnorm]

/-- `a << s` under the no-overflow hypothesis. -/
private theorem applyStrictOp_shl {σ : ExecState} {a s : Nat}
    (hres : a * 2 ^ s < 2 ^ 64) :
    applyStrictOp σ .shiftLeft
        [.int (a : Int) .uint64, .int (s : Int) .uint64]
      = .ok (.int ((a * 2 ^ s : Nat) : Int) .uint64, σ) := by
  have hneg : (decide ((s : Int) < 0)) = false := by
    simp
  have htoNat : ((s : Int)).toNat = s := Int.toNat_natCast s
  have hcast : (a : Int) * (2 : Int) ^ ((s : Int)).toNat
      = ((a * 2 ^ s : Nat) : Int) := by
    rw [htoNat, Int.natCast_mul, Int.natCast_pow]
    rfl
  have hnorm : IntKind.normalize .uint64 ((a * 2 ^ s : Nat) : Int)
      = ((a * 2 ^ s : Nat) : Int) := unorm_nat_of_lt hres
  simp only [applyStrictOp, intShiftLeftResult, valueAsIntValue,
    shiftCountNat, valueAsInt, Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (show ¬((s : Int) < 0) by omega)]
  simp only [htoNat]
  rw [show (a : Int) * 2 ^ s = ((a * 2 ^ s : Nat) : Int) from by
    rw [Int.natCast_mul, Int.natCast_pow]; rfl]
  rw [hnorm]

/-- The parity Bool the isEven body delivers, cleaned. -/
private theorem beq_mod2_zero (n : Nat) :
    ((((n % 2 : Nat) : Int)) == 0) = decide (n % 2 = 0) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

/-- A positive Nat cast compares ≠ 0. -/
private theorem beq_cast_zero_pos {n : Nat} (hn : 1 ≤ n) :
    (((n : Nat) : Int) == 0) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq, Int.natCast_eq_zero]
  omega

private theorem beq_cast_zero_zero :
    (((0 : Nat) : Int) == 0) = true := by decide

/-- Bool-valued normalization for stores into bool cells. -/
private theorem normBool (σ : ExecState) (b : Bool) :
    normalizeValueForTy σ .bool (.bool b) = .ok (.bool b) := by
  simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel]

/-- uint64-valued normalization for stores, at an in-range Nat cast. -/
private theorem normU64 (σ : ExecState) {n : Nat} (hn : n < 2 ^ 64) :
    normalizeValueForTy σ tU (.int ((n : Nat) : Int) .uint64)
      = .ok (.int ((n : Nat) : Int) .uint64) := by
  simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
    unorm_nat_of_lt hn]

/-! ## Pure support facts (loop bounds and gcd-range plumbing) -/

/-- `commonTwos` never exceeds its first argument (founds the shift
bound). -/
private theorem commonTwos_le_left (a b : Nat) : commonTwos a b ≤ a := by
  by_cases h : a ≠ 0 ∧ a % 2 = 0 ∧ b % 2 = 0
  · rw [commonTwos.eq_def, if_pos h]
    have := commonTwos_le_left (a / 2) (b / 2)
    omega
  · rw [commonTwos.eq_def, if_neg h]
    omega
termination_by a
decreasing_by omega

/-- The stripped shared power stays inside `a`. -/
private theorem commonTwos_pow_le_left (a b : Nat) (ha : a ≠ 0) :
    2 ^ commonTwos a b ≤ a := by
  by_cases h : a ≠ 0 ∧ a % 2 = 0 ∧ b % 2 = 0
  · rw [commonTwos.eq_def, if_pos h]
    have hrec := commonTwos_pow_le_left (a / 2) (b / 2) (by omega)
    rw [Nat.pow_succ]
    omega
  · rw [commonTwos.eq_def, if_neg h]
    omega
termination_by a
decreasing_by omega

/-- … and inside `b`. -/
private theorem commonTwos_pow_le_right (a b : Nat) (hb : b ≠ 0) :
    2 ^ commonTwos a b ≤ b := by
  by_cases h : a ≠ 0 ∧ a % 2 = 0 ∧ b % 2 = 0
  · rw [commonTwos.eq_def, if_pos h]
    have hrec := commonTwos_pow_le_right (a / 2) (b / 2) (by omega)
    rw [Nat.pow_succ]
    omega
  · rw [commonTwos.eq_def, if_neg h]
    omega
termination_by a
decreasing_by omega

/-! ## Generic machine-step helpers (footprint style) -/

/-- The `.ref` evaluation step (env-only). -/
private theorem st_ref_step {σ : ExecState} {x : String} {env : LocalEnv}
    {l : Loc} {k : Cont} {ch : Choices}
    (henv : LocalEnv.lookup env x = some l) :
    stepFn σ (.evalE (.ref x) env k) ch = .ok (.retV (.addr l) k, σ, ch) := by
  simp only [stepFn, henv, pure, Except.pure]

/-- Declaring binds at the top for lookup. -/
private theorem lookup_declare_self (env : LocalEnv) (x : String) (l : Loc) :
    LocalEnv.lookup (env.declare x l) x = some l := by
  cases env with
  | nil => simp [LocalEnv.declare, LocalEnv.lookup, Scope.lookup]
  | cons sc rest => simp [LocalEnv.declare, LocalEnv.lookup, Scope.lookup]

/-- The one-result frame every call site here builds (`isEven` and
`steinGCD` both deliver through this shape). -/
private def frameK1 (tv : String) (envC : LocalEnv) (rl : Loc)
    (rest : List Stmt) (K : Cont) : Cont :=
  .frame [(.chain [], [.ref tv])] envC [rl] [] (.seq rest envC K) false

/-- The frame-exit head step: read the pinned result cell, open the
caller-target spine. -/
private theorem st_frame_exit_step {σ : ExecState} {tv : String}
    {envC : LocalEnv} {rA : Nat} {rest : List Stmt} {K : Cont}
    {c : HeapCell} {ch : Choices}
    (hres : Heap.lookup σ.heap (.base ⟨rA⟩) = some c) :
    stepFn σ (.returning (frameK1 tv envC (.base ⟨rA⟩) rest K)) ch
      = .ok (.evalE (.ref tv) envC
          (.tgtOpK (.chain []) [] [] [] [] .vals [] [c.value]
            (.seqn #[]) envC (.seq rest envC K)), σ, ch) := by
  simp only [stepFn, frameK1, loadMany, loadLoc, hres, Bind.bind,
    Except.bind, pure, Except.pure]

/-! ## Entry and the early-return guards (concrete heap; raw
`with_unfolding_all rfl` segments split at the two guard deliveries) -/

/-- The 7-cell heap after the `steinGCD` frame is entered. -/
private def h7 (a0 b0 a4 b5 : Int) : Heap :=
  [(.base ⟨0⟩, u64c a0), (.base ⟨1⟩, u64c b0), (.base ⟨2⟩, u64c 0),
   (.base ⟨3⟩, u64c 0), (.base ⟨4⟩, u64c a4), (.base ⟨5⟩, u64c b5),
   (.base ⟨6⟩, u64c 0)]

private abbrev g1Then : Stmt :=
  .block #[] #[.seqn #[.assign (.var "$res0") (.var "b"), .returnStmt]]
private abbrev g2Then : Stmt :=
  .block #[] #[.seqn #[.assign (.var "$res0") (.var "a"), .returnStmt]]

/-- The `a == 0` delivery continuation. -/
private def g1K : Cont :=
  .ifK g1Then (.seqn #[]) envG2
    (.seq [guard2, shiftSeqn, block1, block2, block3, epiSeqn] envG2
      KframeTail)

/-- The `b == 0` delivery continuation. -/
private def g2K : Cont :=
  .ifK g2Then (.seqn #[]) envG2
    (.seq [shiftSeqn, block1, block2, block3, epiSeqn] envG2 KframeTail)

/-- Entry: post-prelude seed → the `a == 0` guard delivery. 19 steps
(harness body, `r` alloc, the `steinGCD` call, frame entry, guard-1
operand walk). -/
private theorem st_entry (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (ch : Choices) :
    stepFnIter 19 (stSeed (a : Int) (b : Int)) stC0 ch
      = .ok (.retV (.bool (((a : Nat) : Int) == 0)) g1K,
          stSt (h7 (a : Int) (b : Int) (a : Int) (b : Int)) 7, ch) := by
  have hraw : stepFnIter 19 (stSeed (a : Int) (b : Int)) stC0 ch
      = .ok (.retV (.bool (IntKind.normalize .uint64 (a : Int) == 0)) g1K,
          stSt (h7 (a : Int) (b : Int)
            (IntKind.normalize .uint64 (a : Int))
            (IntKind.normalize .uint64 (b : Int))) 7, ch) := by
    with_unfolding_all rfl
  rw [unorm_nat_of_lt ha, unorm_nat_of_lt hb] at hraw
  exact hraw

/-- Early exit A (`a = 0`): guard-1 true → `$res0 = b`, return, both
frame exits, terminal. 38 steps. -/
private theorem st_exitA (a0 b0 a4 : Int) (b : Nat) (hb : b < 2 ^ 64)
    (ch : Choices) :
    stepFnIter 38 (stSt (h7 a0 b0 a4 (b : Int)) 7)
      (.retV (.bool true) g1K) ch
      = .ok (.next .stop,
          stSt [(.base ⟨0⟩, u64c a0), (.base ⟨1⟩, u64c b0),
                (.base ⟨2⟩, u64c (b : Int)), (.base ⟨3⟩, u64c (b : Int)),
                (.base ⟨4⟩, u64c a4), (.base ⟨5⟩, u64c (b : Int)),
                (.base ⟨6⟩, u64c (b : Int))] 7, ch) := by
  have hraw : stepFnIter 38 (stSt (h7 a0 b0 a4 (b : Int)) 7)
      (.retV (.bool true) g1K) ch
      = .ok (.next .stop,
          stSt [(.base ⟨0⟩, u64c a0), (.base ⟨1⟩, u64c b0),
                (.base ⟨2⟩,
                 u64c (IntKind.normalize .uint64 (IntKind.normalize .uint64
                   (IntKind.normalize .uint64 (b : Int))))),
                (.base ⟨3⟩,
                 u64c (IntKind.normalize .uint64
                   (IntKind.normalize .uint64 (b : Int)))),
                (.base ⟨4⟩, u64c a4), (.base ⟨5⟩, u64c (b : Int)),
                (.base ⟨6⟩, u64c (IntKind.normalize .uint64 (b : Int)))] 7,
          ch) := by
    with_unfolding_all rfl
  rw [unorm_nat_of_lt hb, unorm_nat_of_lt hb, unorm_nat_of_lt hb] at hraw
  exact hraw

/-- Guard-1 false → the `b == 0` delivery. 9 steps; reads `b`@5. -/
private theorem st_g2seg (a0 b0 a4 b5 : Int) (ch : Choices) :
    stepFnIter 9 (stSt (h7 a0 b0 a4 b5) 7) (.retV (.bool false) g1K) ch
      = .ok (.retV (.bool (b5 == 0)) g2K, stSt (h7 a0 b0 a4 b5) 7, ch) := by
  with_unfolding_all rfl

/-- Early exit B (`b = 0`): guard-2 true → `$res0 = a`, return, both
frame exits, terminal. 38 steps. -/
private theorem st_exitB (a0 b0 b5 : Int) (a : Nat) (ha : a < 2 ^ 64)
    (ch : Choices) :
    stepFnIter 38 (stSt (h7 a0 b0 (a : Int) b5) 7)
      (.retV (.bool true) g2K) ch
      = .ok (.next .stop,
          stSt [(.base ⟨0⟩, u64c a0), (.base ⟨1⟩, u64c b0),
                (.base ⟨2⟩, u64c (a : Int)), (.base ⟨3⟩, u64c (a : Int)),
                (.base ⟨4⟩, u64c (a : Int)), (.base ⟨5⟩, u64c b5),
                (.base ⟨6⟩, u64c (a : Int))] 7, ch) := by
  have hraw : stepFnIter 38 (stSt (h7 a0 b0 (a : Int) b5) 7)
      (.retV (.bool true) g2K) ch
      = .ok (.next .stop,
          stSt [(.base ⟨0⟩, u64c a0), (.base ⟨1⟩, u64c b0),
                (.base ⟨2⟩,
                 u64c (IntKind.normalize .uint64 (IntKind.normalize .uint64
                   (IntKind.normalize .uint64 (a : Int))))),
                (.base ⟨3⟩,
                 u64c (IntKind.normalize .uint64
                   (IntKind.normalize .uint64 (a : Int)))),
                (.base ⟨4⟩, u64c (a : Int)), (.base ⟨5⟩, u64c b5),
                (.base ⟨6⟩, u64c (IntKind.normalize .uint64 (a : Int)))] 7,
          ch) := by
    with_unfolding_all rfl
  rw [unorm_nat_of_lt ha, unorm_nat_of_lt ha, unorm_nat_of_lt ha] at hraw
  exact hraw

/-- The 9-cell heap at the loop-1 head. -/
private def h9 (a0 b0 a4 b5 : Int) (sv : Int) (ff : Bool) : Heap :=
  [(.base ⟨0⟩, u64c a0), (.base ⟨1⟩, u64c b0), (.base ⟨2⟩, u64c 0),
   (.base ⟨3⟩, u64c 0), (.base ⟨4⟩, u64c a4), (.base ⟨5⟩, u64c b5),
   (.base ⟨6⟩, u64c 0), (.base ⟨7⟩, u64c sv), (.base ⟨8⟩, bcc ff)]

/-- Guard-2 false → the loop-1 head (shift and `$forFirst` allocated,
flag up). 29 steps. -/
private theorem st_toLoop1 (a0 b0 a4 b5 : Int) (ch : Choices) :
    stepFnIter 29 (stSt (h7 a0 b0 a4 b5) 7) (.retV (.bool false) g2K) ch
      = .ok (l1Head, stSt (h9 a0 b0 a4 b5 0 true) 9, ch) := by
  with_unfolding_all rfl

/-- Freshness of the loop-1 entry heap. -/
private theorem h9_fresh (a0 b0 a4 b5 sv : Int) (ff : Bool) :
    FreshFrom (h9 a0 b0 a4 b5 sv ff) 9 := by
  intro x hx
  simp only [h9]
  rw [lookup_cons_ne (base_beq_false (by omega : 0 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 1 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 2 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 3 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 4 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 5 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 6 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 7 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 8 ≠ x))]
  rfl

/-! ## The `isEven` call span (continuation-parametric; instantiated at
all four call sites) -/

/-- The isEven frame env. -/
private def ieEnv (f : Nat) : LocalEnv :=
  [[("$res0", .base ⟨f + 1⟩), ("x", .base ⟨f⟩)]]
private def ieEnv2 (f : Nat) : LocalEnv := [] :: ieEnv f

/-- Raw `enterFrame` reduct at a symbolic heap. -/
private theorem ie_enterFrame_raw (h : Heap) (na : Nat) (v : Int) :
    enterFrame (stSt h na) ⟨"isEven"⟩ [.int v .uint64]
      = .ok (isEvenFunc, ieEnv na, [.base ⟨na + 1⟩],
          stSt ((h.set (.base ⟨na⟩)
              (u64c (IntKind.normalize .uint64 v))).set
              (.base ⟨na + 1⟩) (bcc false)) (na + 2)) := by
  with_unfolding_all rfl

/-- Entering `isEven(n)` on a fresh-from-`na` heap appends the 2-cell
frame. -/
private theorem ie_enterFrame (h : Heap) (na : Nat) (n : Nat)
    (hn : n < 2 ^ 64) (hf : FreshFrom h na) :
    enterFrame (stSt h na) ⟨"isEven"⟩ [.int (n : Int) .uint64]
      = .ok (isEvenFunc, ieEnv na, [.base ⟨na + 1⟩],
          stSt (h ++ [(.base ⟨na⟩, u64c (n : Int)),
                      (.base ⟨na + 1⟩, bcc false)]) (na + 2)) := by
  have hraw := ie_enterFrame_raw h na (n : Int)
  rw [unorm_nat_of_lt hn] at hraw
  rw [set_fresh (hf na (by omega))] at hraw
  rw [set_fresh (show Heap.lookup (h ++ [(.base ⟨na⟩, u64c (n : Int))])
      (.base ⟨na + 1⟩) = none from by
    rw [lookup_append_right (hf (na + 1) (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na ≠ na + 1))]
    rfl)] at hraw
  simpa [List.append_assoc] using hraw

/-- The isEven span's three heap stages. -/
private def ieH1 (h : Heap) (na : Nat) (n : Int) : Heap :=
  h ++ [(.base ⟨na⟩, u64c n), (.base ⟨na + 1⟩, bcc false)]
private def ieH2 (h : Heap) (na : Nat) (n : Int) (v : Bool) : Heap :=
  (ieH1 h na n).set (.base ⟨na + 1⟩) (bcc v)
private def ieH3 (h : Heap) (na tA : Nat) (n : Int) (v : Bool) : Heap :=
  (ieH2 h na n v).set (.base ⟨tA⟩) (bcc v)

/-- **The isEven CALL span** (32 steps): from the call statement's
execution to the caller's resumption. The caller's target cell `tA`
receives `decide (n % 2 = 0)`; the 2-cell frame goes dead at
`na`/`na+1`. -/
private theorem st_ieCall (h : Heap) (na : Nat) (n sA tA : Nat)
    (oldb : Bool) (tv xv : String) (envC : LocalEnv) (rest : List Stmt)
    (K : Cont) (ch : Choices) (hn : n < 2 ^ 64)
    (henvX : LocalEnv.lookup envC xv = some (.base ⟨sA⟩))
    (henvT : LocalEnv.lookup envC tv = some (.base ⟨tA⟩))
    (hsrc : Heap.lookup h (.base ⟨sA⟩) = some (u64c (n : Int)))
    (htgt : Heap.lookup h (.base ⟨tA⟩) = some (bcc oldb))
    (hfr : FreshFrom h na) :
    stepFnIter 32 (stSt h na)
      (.exec (.call #[.var tv] ⟨"isEven"⟩ #[.var xv]) envC
        (.seq rest envC K)) ch
      = .ok (.next (.seq rest envC K),
          stSt ((h.set (.base ⟨tA⟩) (bcc (decide (n % 2 = 0))))
              ++ [(.base ⟨na⟩, u64c (n : Int)),
                  (.base ⟨na + 1⟩, bcc (decide (n % 2 = 0)))]) (na + 2),
          ch) := by
  show stepFnIter (1 + 1 + 1 + 2 + 1 + 4 + 2 + 1 + 2 + 1 + 4 + 1 + 1 + 1
    + 3 + 1 + 1 + 1 + 1 + 1 + 1) _ _ _ = _
  -- 1: call planning
  have hP : stepFnIter 1 (stSt h na)
      (.exec (.call #[.var tv] ⟨"isEven"⟩ #[.var xv]) envC
        (.seq rest envC K)) ch
      = .ok (.evalE (.var xv) envC
          (.callArgsK ⟨"isEven"⟩ [(.chain [], [.ref tv])] [] [] envC
            (.seq rest envC K)),
        stSt h na, ch) := by
    with_unfolding_all rfl
  -- 2: the argument read
  have hArg : stepFnIter 1 (stSt h na)
      (.evalE (.var xv) envC
        (.callArgsK ⟨"isEven"⟩ [(.chain [], [.ref tv])] [] [] envC
          (.seq rest envC K))) ch
      = .ok (.retV (.int (n : Int) .uint64)
          (.callArgsK ⟨"isEven"⟩ [(.chain [], [.ref tv])] [] [] envC
            (.seq rest envC K)),
        stSt h na, ch) :=
    stepFnIter_one (stepFn_var (σ := stSt h na) (x := xv)
      (env := envC) (a := ⟨sA⟩)
      (k := .callArgsK ⟨"isEven"⟩ [(.chain [], [.ref tv])] [] [] envC
        (.seq rest envC K))
      (ch := ch) (c := u64c (n : Int)) henvX hsrc)
  -- 3: frame entry
  have hEnter : stepFnIter 1 (stSt h na)
      (.retV (.int (n : Int) .uint64)
        (.callArgsK ⟨"isEven"⟩ [(.chain [], [.ref tv])] [] [] envC
          (.seq rest envC K))) ch
      = .ok (.exec isEvenFunc.body (ieEnv na)
          (frameK1 tv envC (.base ⟨na + 1⟩) rest K),
        stSt (ieH1 h na (n : Int)) (na + 2), ch) :=
    stepFnIter_one (stepFn_call_enter
      (σ := stSt h na) (fid := ⟨"isEven"⟩) (v := .int (n : Int) .uint64)
      (vals := []) (plans := [(.chain [], [.ref tv])]) (env := envC)
      (k := .seq rest envC K) (ch := ch)
      (ie_enterFrame h na n hn hfr))
  -- 4: body block entry + seq pop (2 steps, env-structural)
  have hB1 : stepFnIter 2 (stSt (ieH1 h na (n : Int)) (na + 2))
      (.exec isEvenFunc.body (ieEnv na)
        (frameK1 tv envC (.base ⟨na + 1⟩) rest K)) ch
      = .ok (.exec (.seqn #[.assign (.var "$res0")
              (.eqCmp tU (.mod (.var "x") (.intLit 2 .uint64))
                (.intLit 0 .uint64)), .returnStmt]) (ieEnv2 na)
            (.seq [] (ieEnv2 na) (frameK1 tv envC (.base ⟨na + 1⟩) rest K)),
          stSt (ieH1 h na (n : Int)) (na + 2), ch) := by
    with_unfolding_all rfl
  -- 5: splice
  have hB2 : stepFnIter 1 (stSt (ieH1 h na (n : Int)) (na + 2))
      (.exec (.seqn #[.assign (.var "$res0")
          (.eqCmp tU (.mod (.var "x") (.intLit 2 .uint64))
            (.intLit 0 .uint64)), .returnStmt]) (ieEnv2 na)
        (.seq [] (ieEnv2 na) (frameK1 tv envC (.base ⟨na + 1⟩) rest K))) ch
      = .ok (.next (.seq [.assign (.var "$res0")
              (.eqCmp tU (.mod (.var "x") (.intLit 2 .uint64))
                (.intLit 0 .uint64)), .returnStmt] (ieEnv2 na)
            (frameK1 tv envC (.base ⟨na + 1⟩) rest K)),
          stSt (ieH1 h na (n : Int)) (na + 2), ch) :=
    stepFnIter_one (stepFn_seqn_splice (σ := stSt (ieH1 h na (n : Int)) (na + 2))
      (ss := #[.assign (.var "$res0")
        (.eqCmp tU (.mod (.var "x") (.intLit 2 .uint64))
          (.intLit 0 .uint64)), .returnStmt])
      (env := ieEnv2 na) (rest := [])
      (k := frameK1 tv envC (.base ⟨na + 1⟩) rest K) (ch := ch))
  -- 6: pop, assign planning, target ref, target completion (4 steps)
  have hB3 : stepFnIter 4 (stSt (ieH1 h na (n : Int)) (na + 2))
      (.next (.seq [.assign (.var "$res0")
          (.eqCmp tU (.mod (.var "x") (.intLit 2 .uint64))
            (.intLit 0 .uint64)), .returnStmt] (ieEnv2 na)
        (frameK1 tv envC (.base ⟨na + 1⟩) rest K))) ch
      = .ok (.evalE (.eqCmp tU (.mod (.var "x") (.intLit 2 .uint64))
              (.intLit 0 .uint64)) (ieEnv2 na)
            (.rhsK .vals [.chain (.addr (.base ⟨na + 1⟩)) [] []] [] []
              (.seqn #[]) (ieEnv2 na)
              (.seq [.returnStmt] (ieEnv2 na)
                (frameK1 tv envC (.base ⟨na + 1⟩) rest K))),
          stSt (ieH1 h na (n : Int)) (na + 2), ch) := by
    with_unfolding_all rfl
  -- 7: eqCmp + mod planning (2 steps)
  have hB4 : stepFnIter 2 (stSt (ieH1 h na (n : Int)) (na + 2))
      (.evalE (.eqCmp tU (.mod (.var "x") (.intLit 2 .uint64))
          (.intLit 0 .uint64)) (ieEnv2 na)
        (.rhsK .vals [.chain (.addr (.base ⟨na + 1⟩)) [] []] [] []
          (.seqn #[]) (ieEnv2 na)
          (.seq [.returnStmt] (ieEnv2 na)
            (frameK1 tv envC (.base ⟨na + 1⟩) rest K)))) ch
      = .ok (.evalE (.var "x") (ieEnv2 na)
            (.strictK .mod [] [.intLit 2 .uint64] (ieEnv2 na)
              (.strictK (.eqCmp tU) [] [.intLit 0 .uint64] (ieEnv2 na)
                (.rhsK .vals [.chain (.addr (.base ⟨na + 1⟩)) [] []] [] []
                  (.seqn #[]) (ieEnv2 na)
                  (.seq [.returnStmt] (ieEnv2 na)
                    (frameK1 tv envC (.base ⟨na + 1⟩) rest K))))),
          stSt (ieH1 h na (n : Int)) (na + 2), ch) := by
    with_unfolding_all rfl
  -- 8: read `x` at the frame cell
  have hxread : Heap.lookup (ieH1 h na (n : Int)) (.base ⟨na⟩)
      = some (u64c (n : Int)) := by
    simp only [ieH1]
    rw [lookup_append_right (hfr na (by omega))]
    exact lookup_cons_self
  have hB5 : stepFnIter 1 (stSt (ieH1 h na (n : Int)) (na + 2))
      (.evalE (.var "x") (ieEnv2 na)
        (.strictK .mod [] [.intLit 2 .uint64] (ieEnv2 na)
          (.strictK (.eqCmp tU) [] [.intLit 0 .uint64] (ieEnv2 na)
            (.rhsK .vals [.chain (.addr (.base ⟨na + 1⟩)) [] []] [] []
              (.seqn #[]) (ieEnv2 na)
              (.seq [.returnStmt] (ieEnv2 na)
                (frameK1 tv envC (.base ⟨na + 1⟩) rest K)))))) ch
      = .ok (.retV (.int (n : Int) .uint64)
            (.strictK .mod [] [.intLit 2 .uint64] (ieEnv2 na)
              (.strictK (.eqCmp tU) [] [.intLit 0 .uint64] (ieEnv2 na)
                (.rhsK .vals [.chain (.addr (.base ⟨na + 1⟩)) [] []] [] []
                  (.seqn #[]) (ieEnv2 na)
                  (.seq [.returnStmt] (ieEnv2 na)
                    (frameK1 tv envC (.base ⟨na + 1⟩) rest K))))),
          stSt (ieH1 h na (n : Int)) (na + 2), ch) :=
    stepFnIter_one (stepFn_var (σ := stSt (ieH1 h na (n : Int)) (na + 2))
      (x := "x") (env := ieEnv2 na) (a := ⟨na⟩)
      (k := .strictK .mod [] [.intLit 2 .uint64] (ieEnv2 na)
        (.strictK (.eqCmp tU) [] [.intLit 0 .uint64] (ieEnv2 na)
          (.rhsK .vals [.chain (.addr (.base ⟨na + 1⟩)) [] []] [] []
            (.seqn #[]) (ieEnv2 na)
            (.seq [.returnStmt] (ieEnv2 na)
              (frameK1 tv envC (.base ⟨na + 1⟩) rest K)))))
      (ch := ch) (c := u64c (n : Int)) rfl hxread)
  -- 9: the literal-2 operand (2 steps)
  have hB6 : stepFnIter 2 (stSt (ieH1 h na (n : Int)) (na + 2))
      (.retV (.int (n : Int) .uint64)
        (.strictK .mod [] [.intLit 2 .uint64] (ieEnv2 na)
          (.strictK (.eqCmp tU) [] [.intLit 0 .uint64] (ieEnv2 na)
            (.rhsK .vals [.chain (.addr (.base ⟨na + 1⟩)) [] []] [] []
              (.seqn #[]) (ieEnv2 na)
              (.seq [.returnStmt] (ieEnv2 na)
                (frameK1 tv envC (.base ⟨na + 1⟩) rest K)))))) ch
      = .ok (.retV (.int 2 .uint64)
            (.strictK .mod [.int (n : Int) .uint64] [] (ieEnv2 na)
              (.strictK (.eqCmp tU) [] [.intLit 0 .uint64] (ieEnv2 na)
                (.rhsK .vals [.chain (.addr (.base ⟨na + 1⟩)) [] []] [] []
                  (.seqn #[]) (ieEnv2 na)
                  (.seq [.returnStmt] (ieEnv2 na)
                    (frameK1 tv envC (.base ⟨na + 1⟩) rest K))))),
          stSt (ieH1 h na (n : Int)) (na + 2), ch) := by
    with_unfolding_all rfl
  -- 10: the mod apply
  have hB7 : stepFnIter 1 (stSt (ieH1 h na (n : Int)) (na + 2))
      (.retV (.int 2 .uint64)
        (.strictK .mod [.int (n : Int) .uint64] [] (ieEnv2 na)
          (.strictK (.eqCmp tU) [] [.intLit 0 .uint64] (ieEnv2 na)
            (.rhsK .vals [.chain (.addr (.base ⟨na + 1⟩)) [] []] [] []
              (.seqn #[]) (ieEnv2 na)
              (.seq [.returnStmt] (ieEnv2 na)
                (frameK1 tv envC (.base ⟨na + 1⟩) rest K)))))) ch
      = .ok (.retV (.int ((n % 2 : Nat) : Int) .uint64)
            (.strictK (.eqCmp tU) [] [.intLit 0 .uint64] (ieEnv2 na)
              (.rhsK .vals [.chain (.addr (.base ⟨na + 1⟩)) [] []] [] []
                (.seqn #[]) (ieEnv2 na)
                (.seq [.returnStmt] (ieEnv2 na)
                  (frameK1 tv envC (.base ⟨na + 1⟩) rest K)))),
          stSt (ieH1 h na (n : Int)) (na + 2), ch) :=
    stepFnIter_one (stepFn_strict_apply
      (σ := stSt (ieH1 h na (n : Int)) (na + 2))
      (σ' := stSt (ieH1 h na (n : Int)) (na + 2)) (op := .mod)
      (done := [.int (n : Int) .uint64]) (v := .int 2 .uint64)
      (out := .int ((n % 2 : Nat) : Int) .uint64)
      (env := ieEnv2 na)
      (k := .strictK (.eqCmp tU) [] [.intLit 0 .uint64] (ieEnv2 na)
        (.rhsK .vals [.chain (.addr (.base ⟨na + 1⟩)) [] []] [] []
          (.seqn #[]) (ieEnv2 na)
          (.seq [.returnStmt] (ieEnv2 na)
            (frameK1 tv envC (.base ⟨na + 1⟩) rest K))))
      (ch := ch) applyStrictOp_mod2)
  -- 11: the literal-0 operand + the eq apply + the rhs drain (4 steps)
  have hB8 : stepFnIter 4 (stSt (ieH1 h na (n : Int)) (na + 2))
      (.retV (.int ((n % 2 : Nat) : Int) .uint64)
        (.strictK (.eqCmp tU) [] [.intLit 0 .uint64] (ieEnv2 na)
          (.rhsK .vals [.chain (.addr (.base ⟨na + 1⟩)) [] []] [] []
            (.seqn #[]) (ieEnv2 na)
            (.seq [.returnStmt] (ieEnv2 na)
              (frameK1 tv envC (.base ⟨na + 1⟩) rest K))))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na + 1⟩)) [] []]
            [.bool (((n % 2 : Nat) : Int) == 0)] (.seqn #[]) (ieEnv2 na)
            (.seq [.returnStmt] (ieEnv2 na)
              (frameK1 tv envC (.base ⟨na + 1⟩) rest K))),
          stSt (ieH1 h na (n : Int)) (na + 2), ch) := by
    with_unfolding_all rfl
  -- 12: the `$res0` store (bool cell at na+1)
  have hresLook : Heap.lookup (ieH1 h na (n : Int)) (.base ⟨na + 1⟩)
      = some (bcc false) := by
    simp only [ieH1]
    rw [lookup_append_right (hfr (na + 1) (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na ≠ na + 1))]
    exact lookup_cons_self
  have hB9 : stepFnIter 1 (stSt (ieH1 h na (n : Int)) (na + 2))
      (.next (.storeK [.chain (.addr (.base ⟨na + 1⟩)) [] []]
        [.bool (((n % 2 : Nat) : Int) == 0)] (.seqn #[]) (ieEnv2 na)
        (.seq [.returnStmt] (ieEnv2 na)
          (frameK1 tv envC (.base ⟨na + 1⟩) rest K)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (ieEnv2 na)
            (.seq [.returnStmt] (ieEnv2 na)
              (frameK1 tv envC (.base ⟨na + 1⟩) rest K))),
          stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2),
          ch) :=
    stepFnIter_one (stepFn_store_step
      (σ := stSt (ieH1 h na (n : Int)) (na + 2))
      (σ' := stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2))
      (r := .chain (.addr (.base ⟨na + 1⟩)) [] [])
      (val := .bool (((n % 2 : Nat) : Int) == 0))
      (rs := []) (vs := []) (body := .seqn #[]) (env := ieEnv2 na)
      (k := .seq [.returnStmt] (ieEnv2 na)
        (frameK1 tv envC (.base ⟨na + 1⟩) rest K))
      (ch := ch)
      (storeTarget_addr hresLook (normBool _ _)))
  -- 13: drained store → the empty body seqn (1 step)
  have hB10 : stepFnIter 1
      (stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2))
      (.next (.storeK [] [] (.seqn #[]) (ieEnv2 na)
        (.seq [.returnStmt] (ieEnv2 na)
          (frameK1 tv envC (.base ⟨na + 1⟩) rest K)))) ch
      = .ok (.exec (.seqn #[]) (ieEnv2 na)
            (.seq [.returnStmt] (ieEnv2 na)
              (frameK1 tv envC (.base ⟨na + 1⟩) rest K)),
          stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2),
          ch) :=
    stepFnIter_one (stepFn_storeK_nil
      (σ := stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2))
      (body := .seqn #[]) (env := ieEnv2 na)
      (k := .seq [.returnStmt] (ieEnv2 na)
        (frameK1 tv envC (.base ⟨na + 1⟩) rest K)) (ch := ch))
  -- 14: splice the empty seqn
  have hB11 : stepFnIter 1
      (stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2))
      (.exec (.seqn #[]) (ieEnv2 na)
        (.seq [.returnStmt] (ieEnv2 na)
          (frameK1 tv envC (.base ⟨na + 1⟩) rest K))) ch
      = .ok (.next (.seq [.returnStmt] (ieEnv2 na)
            (frameK1 tv envC (.base ⟨na + 1⟩) rest K)),
          stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2),
          ch) :=
    stepFnIter_one (stepFn_seqn_splice
      (σ := stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2))
      (ss := #[]) (env := ieEnv2 na) (rest := [.returnStmt])
      (k := frameK1 tv envC (.base ⟨na + 1⟩) rest K) (ch := ch))
  -- 15: pop, return, unwind to the frame (3 steps)
  have hB12 : stepFnIter 3
      (stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2))
      (.next (.seq [.returnStmt] (ieEnv2 na)
        (frameK1 tv envC (.base ⟨na + 1⟩) rest K))) ch
      = .ok (.returning (frameK1 tv envC (.base ⟨na + 1⟩) rest K),
          stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2),
          ch) := by
    with_unfolding_all rfl
  -- 16: the frame exit reads the pinned result
  have hB13 : stepFnIter 1
      (stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2))
      (.returning (frameK1 tv envC (.base ⟨na + 1⟩) rest K)) ch
      = .ok (.evalE (.ref tv) envC
            (.tgtOpK (.chain []) [] [] [] [] .vals []
              [.bool (((n % 2 : Nat) : Int) == 0)] (.seqn #[]) envC
              (.seq rest envC K)),
          stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2),
          ch) :=
    stepFnIter_one (st_frame_exit_step
      (σ := stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2))
      (tv := tv) (envC := envC) (rA := na + 1) (rest := rest)
      (K := K) (c := bcc (((n % 2 : Nat) : Int) == 0)) (ch := ch)
      lookup_set_self)
  -- 17: the caller-target ref
  have hB14 : stepFnIter 1
      (stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2))
      (.evalE (.ref tv) envC
        (.tgtOpK (.chain []) [] [] [] [] .vals []
          [.bool (((n % 2 : Nat) : Int) == 0)] (.seqn #[]) envC
          (.seq rest envC K))) ch
      = .ok (.retV (.addr (.base ⟨tA⟩))
            (.tgtOpK (.chain []) [] [] [] [] .vals []
              [.bool (((n % 2 : Nat) : Int) == 0)] (.seqn #[]) envC
              (.seq rest envC K)),
          stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2),
          ch) :=
    stepFnIter_one (st_ref_step
      (σ := stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2))
      (x := tv) (env := envC) (l := .base ⟨tA⟩)
      (k := .tgtOpK (.chain []) [] [] [] [] .vals []
        [.bool (((n % 2 : Nat) : Int) == 0)] (.seqn #[]) envC
        (.seq rest envC K))
      (ch := ch) henvT)
  -- 18: target completion (1 step)
  have hB15 : stepFnIter 1
      (stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2))
      (.retV (.addr (.base ⟨tA⟩))
        (.tgtOpK (.chain []) [] [] [] [] .vals []
          [.bool (((n % 2 : Nat) : Int) == 0)] (.seqn #[]) envC
          (.seq rest envC K))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨tA⟩)) [] []]
            [.bool (((n % 2 : Nat) : Int) == 0)] (.seqn #[]) envC
            (.seq rest envC K)),
          stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2),
          ch) := by
    with_unfolding_all rfl
  -- 19: the store into the caller's target cell
  have htgtLook : Heap.lookup
      (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0))
      (.base ⟨tA⟩) = some (bcc oldb) := by
    have htA : tA < na := hfr.lt_of_lookup htgt
    simp only [ieH2]
    rw [lookup_set_other (by omega : na + 1 ≠ tA)]
    simp only [ieH1]
    exact lookup_append_left htgt
  have hB16 : stepFnIter 1
      (stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2))
      (.next (.storeK [.chain (.addr (.base ⟨tA⟩)) [] []]
        [.bool (((n % 2 : Nat) : Int) == 0)] (.seqn #[]) envC
        (.seq rest envC K))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) envC (.seq rest envC K)),
          stSt (ieH3 h na tA (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2),
          ch) :=
    stepFnIter_one (stepFn_store_step
      (σ := stSt (ieH2 h na (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2))
      (σ' := stSt (ieH3 h na tA (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2))
      (r := .chain (.addr (.base ⟨tA⟩)) [] [])
      (val := .bool (((n % 2 : Nat) : Int) == 0))
      (rs := []) (vs := []) (body := .seqn #[]) (env := envC)
      (k := .seq rest envC K) (ch := ch)
      (storeTarget_addr htgtLook (normBool _ _)))
  -- 20: drained store → the empty statement (1 step)
  have hB17 : stepFnIter 1
      (stSt (ieH3 h na tA (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2))
      (.next (.storeK [] [] (.seqn #[]) envC (.seq rest envC K))) ch
      = .ok (.exec (.seqn #[]) envC (.seq rest envC K),
          stSt (ieH3 h na tA (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2),
          ch) :=
    stepFnIter_one (stepFn_storeK_nil
      (σ := stSt (ieH3 h na tA (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2))
      (body := .seqn #[]) (env := envC) (k := .seq rest envC K) (ch := ch))
  -- 21: splice the empty seqn into the caller's sequence
  have hB18 : stepFnIter 1
      (stSt (ieH3 h na tA (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2))
      (.exec (.seqn #[]) envC (.seq rest envC K)) ch
      = .ok (.next (.seq rest envC K),
          stSt (ieH3 h na tA (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2),
          ch) :=
    stepFnIter_one (stepFn_seqn_splice
      (σ := stSt (ieH3 h na tA (n : Int) (((n % 2 : Nat) : Int) == 0)) (na + 2))
      (ss := #[]) (env := envC) (rest := rest) (k := K) (ch := ch))
  -- assemble, then rewrite the heap into its canonical append form
  have hheap : ieH3 h na tA (n : Int) (((n % 2 : Nat) : Int) == 0)
      = (h.set (.base ⟨tA⟩) (bcc (((n % 2 : Nat) : Int) == 0)))
        ++ [(.base ⟨na⟩, u64c (n : Int)),
            (.base ⟨na + 1⟩, bcc (((n % 2 : Nat) : Int) == 0))] := by
    have htA : tA < na := hfr.lt_of_lookup htgt
    simp only [ieH3, ieH2, ieH1]
    rw [set_append_right (hfr (na + 1) (by omega)),
      set_cons_ne (base_beq_false (by omega : na ≠ na + 1)),
      set_singleton_self,
      set_append_left htgt]
  have hres := (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hP hArg) hEnter) hB1) hB2) hB3) hB4) hB5) hB6) hB7) hB8) hB9) hB10) hB11) hB12) hB13) hB14) hB15) hB16) hB17) hB18)
  rw [hheap] at hres
  rw [beq_mod2_zero] at hres
  exact hres

/-- **The isEven CALL PAIR span** (36 steps): `$cN := isEven(xv)` —
init + call, from the pair seqn's execution to the caller's resumption
with the declared env. Appends exactly three cells: the condition cell
at `na`, the dead frame at `na+1`/`na+2`. -/
private theorem st_ieSeq (h : Heap) (na : Nat) (n sA : Nat)
    (tv xv : String) (envC : LocalEnv) (rest : List Stmt) (K : Cont)
    (ch : Choices) (hn : n < 2 ^ 64)
    (henvX : LocalEnv.lookup (envC.declare tv (.base ⟨na⟩)) xv
      = some (.base ⟨sA⟩))
    (hsrc : Heap.lookup h (.base ⟨sA⟩) = some (u64c (n : Int)))
    (hfr : FreshFrom h na) :
    stepFnIter 36 (stSt h na)
      (.exec (ieSeqn tv xv) envC (.seq rest envC K)) ch
      = .ok (.next (.seq rest (envC.declare tv (.base ⟨na⟩)) K),
          stSt (h ++ [(.base ⟨na⟩, bcc (decide (n % 2 = 0))),
                      (.base ⟨na + 1⟩, u64c (n : Int)),
                      (.base ⟨na + 2⟩, bcc (decide (n % 2 = 0)))]) (na + 3),
          ch) := by
  show stepFnIter (1 + 1 + 1 + 1 + 32) _ _ _ = _
  -- splice the pair into the governing sequence
  have hS1 : stepFnIter 1 (stSt h na)
      (.exec (ieSeqn tv xv) envC (.seq rest envC K)) ch
      = .ok (.next (.seq (.initialization { id := tv, typ := .bool }
              :: .call #[.var tv] ⟨"isEven"⟩ #[.var xv] :: rest) envC K),
          stSt h na, ch) :=
    stepFnIter_one (stepFn_seqn_splice (σ := stSt h na)
      (ss := #[.initialization { id := tv, typ := .bool },
               .call #[.var tv] ⟨"isEven"⟩ #[.var xv]])
      (env := envC) (rest := rest) (k := K) (ch := ch))
  -- pop the init
  have hS2 : stepFnIter 1 (stSt h na)
      (.next (.seq (.initialization { id := tv, typ := .bool }
          :: .call #[.var tv] ⟨"isEven"⟩ #[.var xv] :: rest) envC K)) ch
      = .ok (.exec (.initialization { id := tv, typ := .bool }) envC
            (.seq (.call #[.var tv] ⟨"isEven"⟩ #[.var xv] :: rest) envC K),
          stSt h na, ch) :=
    stepFnIter_one (stepFn_seq_pop (σ := stSt h na))
  -- the allocation
  have hS3 : stepFnIter 1 (stSt h na)
      (.exec (.initialization { id := tv, typ := .bool }) envC
        (.seq (.call #[.var tv] ⟨"isEven"⟩ #[.var xv] :: rest) envC K)) ch
      = .ok (.next (.seq (.call #[.var tv] ⟨"isEven"⟩ #[.var xv] :: rest)
            (envC.declare tv (.base ⟨na⟩)) K),
          stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1), ch) := by
    have hstep := stepFn_init_seq (σ := stSt h na)
      (p := { id := tv, typ := .bool })
      (rest := .call #[.var tv] ⟨"isEven"⟩ #[.var xv] :: rest)
      (env := envC) (k := K) (ch := ch) (v := .bool false)
      (by with_unfolding_all rfl)
    rw [show Heap.set (stSt h na).heap (.base ⟨(stSt h na).nextAddr⟩)
        ⟨some Ty.bool, .bool false⟩ = h ++ [(.base ⟨na⟩, bcc false)] from
      set_fresh (hfr na (by omega))] at hstep
    exact stepFnIter_one hstep
  -- pop the call
  have hS4 : stepFnIter 1 (stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (.next (.seq (.call #[.var tv] ⟨"isEven"⟩ #[.var xv] :: rest)
        (envC.declare tv (.base ⟨na⟩)) K)) ch
      = .ok (.exec (.call #[.var tv] ⟨"isEven"⟩ #[.var xv])
            (envC.declare tv (.base ⟨na⟩))
            (.seq rest (envC.declare tv (.base ⟨na⟩)) K),
          stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1), ch) :=
    stepFnIter_one (stepFn_seq_pop
      (σ := stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1)))
  -- the call span
  have hCall := st_ieCall (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1) n sA na
    false tv xv (envC.declare tv (.base ⟨na⟩)) rest K ch hn
    henvX (lookup_declare_self envC tv (.base ⟨na⟩))
    (lookup_append_left hsrc)
    (by
      rw [lookup_append_right (hfr na (by omega))]
      exact lookup_cons_self)
    (by
      intro x hx
      rw [lookup_append_right (hfr x (by omega)),
        lookup_cons_ne (base_beq_false (by omega : na ≠ x))]
      rfl)
  rw [show Heap.set (h ++ [(.base ⟨na⟩, bcc false)]) (.base ⟨na⟩)
      (bcc (decide (n % 2 = 0)))
      = h ++ [(.base ⟨na⟩, bcc (decide (n % 2 = 0)))] from by
    rw [set_append_right (hfr na (by omega)), set_singleton_self]] at hCall
  rw [show (h ++ [(.base ⟨na⟩, bcc (decide (n % 2 = 0)))])
        ++ [(.base ⟨na + 1⟩, u64c (n : Int)),
            (.base ⟨na + 1 + 1⟩, bcc (decide (n % 2 = 0)))]
      = h ++ [(.base ⟨na⟩, bcc (decide (n % 2 = 0))),
              (.base ⟨na + 1⟩, u64c (n : Int)),
              (.base ⟨na + 2⟩, bcc (decide (n % 2 = 0)))] from by
    rw [List.append_assoc]
    with_unfolding_all rfl] at hCall
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hS1 hS2) hS3) hS4) hCall

/-! ## Generic loop machinery (all four loops share the dispatch and
per-statement shapes; `env` parametric, flag address by hypothesis) -/

private theorem lookup_pushScope (env : LocalEnv) (x : String) :
    LocalEnv.lookup ([] :: env) x = LocalEnv.lookup env x := rfl

/-- Loop dispatch, first pass (flag up): head → the post-dispatch
point, flag written down. 16 steps. -/
private theorem lp_disp_t (h : Heap) (na fA : Nat) (sA sB sC : Stmt)
    (env : LocalEnv) (K : Cont) (ch : Choices)
    (henv : LocalEnv.lookup env "$forFirst" = some (.base ⟨fA⟩))
    (hff : Heap.lookup h (.base ⟨fA⟩) = some (bcc true)) :
    stepFnIter 16 (stSt h na)
      (lpHeadg (.block #[] #[lpDispatch, sA, sB, sC]) env K) ch
      = .ok (lpPostg (.block #[] #[lpDispatch, sA, sB, sC]) env sA sB sC K,
          stSt (h.set (.base ⟨fA⟩) (bcc false)) na, ch) := by
  show stepFnIter (6 + 1 + 2 + 1 + 3 + 1 + 1 + 1) _ _ _ = _
  have hA : stepFnIter 6 (stSt h na)
      (lpHeadg (.block #[] #[lpDispatch, sA, sB, sC]) env K) ch
      = .ok (.evalE (.var "$forFirst") ([] :: env)
            (.ifK (.assign (.var "$forFirst") (.boolLit false)) (.seqn #[])
              ([] :: env)
              (.seq [sA, sB, sC] ([] :: env)
                (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have hV : stepFnIter 1 (stSt h na)
      (.evalE (.var "$forFirst") ([] :: env)
        (.ifK (.assign (.var "$forFirst") (.boolLit false)) (.seqn #[])
          ([] :: env)
          (.seq [sA, sB, sC] ([] :: env)
            (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K)))) ch
      = .ok (.retV (.bool true)
            (.ifK (.assign (.var "$forFirst") (.boolLit false)) (.seqn #[])
              ([] :: env)
              (.seq [sA, sB, sC] ([] :: env)
                (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K))),
          stSt h na, ch) :=
    stepFnIter_one (stepFn_var (σ := stSt h na) (x := "$forFirst")
      (env := [] :: env) (a := ⟨fA⟩)
      (k := .ifK (.assign (.var "$forFirst") (.boolLit false)) (.seqn #[])
        ([] :: env)
        (.seq [sA, sB, sC] ([] :: env)
          (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K)))
      (ch := ch) (c := bcc true) henv hff)
  have hB : stepFnIter 2 (stSt h na)
      (.retV (.bool true)
        (.ifK (.assign (.var "$forFirst") (.boolLit false)) (.seqn #[])
          ([] :: env)
          (.seq [sA, sB, sC] ([] :: env)
            (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K)))) ch
      = .ok (.evalE (.ref "$forFirst") ([] :: env)
            (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit false] []
              (.seqn #[]) ([] :: env)
              (.seq [sA, sB, sC] ([] :: env)
                (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have hR : stepFnIter 1 (stSt h na)
      (.evalE (.ref "$forFirst") ([] :: env)
        (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit false] []
          (.seqn #[]) ([] :: env)
          (.seq [sA, sB, sC] ([] :: env)
            (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K)))) ch
      = .ok (.retV (.addr (.base ⟨fA⟩))
            (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit false] []
              (.seqn #[]) ([] :: env)
              (.seq [sA, sB, sC] ([] :: env)
                (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K))),
          stSt h na, ch) :=
    stepFnIter_one (st_ref_step (σ := stSt h na) (x := "$forFirst")
      (env := [] :: env) (l := .base ⟨fA⟩)
      (k := .tgtOpK (.chain []) [] [] [] [] .vals [.boolLit false] []
        (.seqn #[]) ([] :: env)
        (.seq [sA, sB, sC] ([] :: env)
          (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K)))
      (ch := ch) henv)
  have hC : stepFnIter 3 (stSt h na)
      (.retV (.addr (.base ⟨fA⟩))
        (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit false] []
          (.seqn #[]) ([] :: env)
          (.seq [sA, sB, sC] ([] :: env)
            (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨fA⟩)) [] []]
            [.bool false] (.seqn #[]) ([] :: env)
            (.seq [sA, sB, sC] ([] :: env)
              (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have hSt : stepFnIter 1 (stSt h na)
      (.next (.storeK [.chain (.addr (.base ⟨fA⟩)) [] []]
        [.bool false] (.seqn #[]) ([] :: env)
        (.seq [sA, sB, sC] ([] :: env)
          (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) ([] :: env)
            (.seq [sA, sB, sC] ([] :: env)
              (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K))),
          stSt (h.set (.base ⟨fA⟩) (bcc false)) na, ch) :=
    stepFnIter_one (stepFn_store_step (σ := stSt h na)
      (σ' := stSt (h.set (.base ⟨fA⟩) (bcc false)) na)
      (r := .chain (.addr (.base ⟨fA⟩)) [] []) (val := .bool false)
      (rs := []) (vs := []) (body := .seqn #[]) (env := [] :: env)
      (k := .seq [sA, sB, sC] ([] :: env)
        (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K))
      (ch := ch) (storeTarget_addr hff (normBool _ _)))
  have hN : stepFnIter 1 (stSt (h.set (.base ⟨fA⟩) (bcc false)) na)
      (.next (.storeK [] [] (.seqn #[]) ([] :: env)
        (.seq [sA, sB, sC] ([] :: env)
          (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K)))) ch
      = .ok (.exec (.seqn #[]) ([] :: env)
            (.seq [sA, sB, sC] ([] :: env)
              (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K)),
          stSt (h.set (.base ⟨fA⟩) (bcc false)) na, ch) :=
    stepFnIter_one (stepFn_storeK_nil
      (σ := stSt (h.set (.base ⟨fA⟩) (bcc false)) na)
      (body := .seqn #[]) (env := [] :: env)
      (k := .seq [sA, sB, sC] ([] :: env)
        (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K)) (ch := ch))
  have hSp : stepFnIter 1 (stSt (h.set (.base ⟨fA⟩) (bcc false)) na)
      (.exec (.seqn #[]) ([] :: env)
        (.seq [sA, sB, sC] ([] :: env)
          (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K))) ch
      = .ok (lpPostg (.block #[] #[lpDispatch, sA, sB, sC]) env sA sB sC K,
          stSt (h.set (.base ⟨fA⟩) (bcc false)) na, ch) :=
    stepFnIter_one (stepFn_seqn_splice
      (σ := stSt (h.set (.base ⟨fA⟩) (bcc false)) na)
      (ss := #[]) (env := [] :: env) (rest := [sA, sB, sC])
      (k := loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain hA hV) hB) hR) hC) hSt) hN) hSp

/-- Loop dispatch, later passes (flag down): head → the post-dispatch
point. 9 steps, heap untouched. -/
private theorem lp_disp_f (h : Heap) (na fA : Nat) (sA sB sC : Stmt)
    (env : LocalEnv) (K : Cont) (ch : Choices)
    (henv : LocalEnv.lookup env "$forFirst" = some (.base ⟨fA⟩))
    (hff : Heap.lookup h (.base ⟨fA⟩) = some (bcc false)) :
    stepFnIter 9 (stSt h na)
      (lpHeadg (.block #[] #[lpDispatch, sA, sB, sC]) env K) ch
      = .ok (lpPostg (.block #[] #[lpDispatch, sA, sB, sC]) env sA sB sC K,
          stSt h na, ch) := by
  show stepFnIter (6 + 1 + 1 + 1) _ _ _ = _
  have hA : stepFnIter 6 (stSt h na)
      (lpHeadg (.block #[] #[lpDispatch, sA, sB, sC]) env K) ch
      = .ok (.evalE (.var "$forFirst") ([] :: env)
            (.ifK (.assign (.var "$forFirst") (.boolLit false)) (.seqn #[])
              ([] :: env)
              (.seq [sA, sB, sC] ([] :: env)
                (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have hV : stepFnIter 1 (stSt h na)
      (.evalE (.var "$forFirst") ([] :: env)
        (.ifK (.assign (.var "$forFirst") (.boolLit false)) (.seqn #[])
          ([] :: env)
          (.seq [sA, sB, sC] ([] :: env)
            (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K)))) ch
      = .ok (.retV (.bool false)
            (.ifK (.assign (.var "$forFirst") (.boolLit false)) (.seqn #[])
              ([] :: env)
              (.seq [sA, sB, sC] ([] :: env)
                (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K))),
          stSt h na, ch) :=
    stepFnIter_one (stepFn_var (σ := stSt h na) (x := "$forFirst")
      (env := [] :: env) (a := ⟨fA⟩)
      (k := .ifK (.assign (.var "$forFirst") (.boolLit false)) (.seqn #[])
        ([] :: env)
        (.seq [sA, sB, sC] ([] :: env)
          (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K)))
      (ch := ch) (c := bcc false) henv hff)
  have hB : stepFnIter 1 (stSt h na)
      (.retV (.bool false)
        (.ifK (.assign (.var "$forFirst") (.boolLit false)) (.seqn #[])
          ([] :: env)
          (.seq [sA, sB, sC] ([] :: env)
            (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K)))) ch
      = .ok (.exec (.seqn #[]) ([] :: env)
            (.seq [sA, sB, sC] ([] :: env)
              (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K)),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have hSp : stepFnIter 1 (stSt h na)
      (.exec (.seqn #[]) ([] :: env)
        (.seq [sA, sB, sC] ([] :: env)
          (loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K))) ch
      = .ok (lpPostg (.block #[] #[lpDispatch, sA, sB, sC]) env sA sB sC K,
          stSt h na, ch) :=
    stepFnIter_one (stepFn_seqn_splice (σ := stSt h na)
      (ss := #[]) (env := [] :: env) (rest := [sA, sB, sC])
      (k := loopKg (.block #[] #[lpDispatch, sA, sB, sC]) env K) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hA hV) hB) hSp

/-- Generic `if (var x)` delivery: pop + plan + flag read. 3 steps. -/
private theorem seg_ifVar (h : Heap) (na : Nat) (x : String)
    (env : LocalEnv) (aX : Nat) (v : Bool) (t e : Stmt)
    (rest' : List Stmt) (k : Cont) (ch : Choices)
    (henv : LocalEnv.lookup env x = some (.base ⟨aX⟩))
    (hx : Heap.lookup h (.base ⟨aX⟩) = some (bcc v)) :
    stepFnIter 3 (stSt h na)
      (.next (.seq (.ifThenElse (.var x) t e :: rest') env k)) ch
      = .ok (.retV (.bool v) (.ifK t e env (.seq rest' env k)),
          stSt h na, ch) := by
  show stepFnIter (1 + 1 + 1) _ _ _ = _
  have h1 := stepFnIter_one (stepFn_seq_pop (σ := stSt h na)
    (t := .ifThenElse (.var x) t e) (rest := rest') (env := env) (k := k)
    (ch := ch))
  have h2 : stepFnIter 1 (stSt h na)
      (.exec (.ifThenElse (.var x) t e) env (.seq rest' env k)) ch
      = .ok (.evalE (.var x) env (.ifK t e env (.seq rest' env k)),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have h3 := stepFnIter_one (stepFn_var (σ := stSt h na) (x := x)
    (env := env) (a := ⟨aX⟩) (k := .ifK t e env (.seq rest' env k))
    (ch := ch) (c := bcc v) henv hx)
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- Generic `x := x / 2` under a pushed iteration scope: pop through
store. 13 steps; ends back at the governing sequence. -/
private theorem seg_asgHalf (h : Heap) (na : Nat) (x : String)
    (env : LocalEnv) (aX : Nat) (n : Nat) (rest' : List Stmt) (k : Cont)
    (ch : Choices) (hn : n < 2 ^ 64)
    (henv : LocalEnv.lookup env x = some (.base ⟨aX⟩))
    (hx : Heap.lookup h (.base ⟨aX⟩) = some (u64c (n : Int))) :
    stepFnIter 13 (stSt h na)
      (.next (.seq (asgHalf x :: rest') env k)) ch
      = .ok (.next (.seq rest' env k),
          stSt (h.set (.base ⟨aX⟩) (u64c ((n / 2 : Nat) : Int))) na, ch) := by
  show stepFnIter (1 + 1 + 1 + 1 + 1 + 1 + 2 + 1 + 1 + 1 + 1 + 1) _ _ _ = _
  have h1 := stepFnIter_one (stepFn_seq_pop (σ := stSt h na)
    (t := asgHalf x) (rest := rest') (env := env) (k := k) (ch := ch))
  have h2 : stepFnIter 1 (stSt h na)
      (.exec (asgHalf x) env (.seq rest' env k)) ch
      = .ok (.evalE (.ref x) env
            (.tgtOpK (.chain []) [] [] [] []
              .vals [.div (.var x) (.intLit 2 .uint64)] [] (.seqn #[]) env
              (.seq rest' env k)),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have h3 := stepFnIter_one (st_ref_step (σ := stSt h na) (x := x)
    (env := env) (l := .base ⟨aX⟩)
    (k := .tgtOpK (.chain []) [] [] [] []
      .vals [.div (.var x) (.intLit 2 .uint64)] [] (.seqn #[]) env
      (.seq rest' env k)) (ch := ch) henv)
  have h4 : stepFnIter 1 (stSt h na)
      (.retV (.addr (.base ⟨aX⟩))
        (.tgtOpK (.chain []) [] [] [] []
          .vals [.div (.var x) (.intLit 2 .uint64)] [] (.seqn #[]) env
          (.seq rest' env k))) ch
      = .ok (.evalE (.div (.var x) (.intLit 2 .uint64)) env
            (.rhsK .vals [.chain (.addr (.base ⟨aX⟩)) [] []] [] []
              (.seqn #[]) env (.seq rest' env k)),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have h5 : stepFnIter 1 (stSt h na)
      (.evalE (.div (.var x) (.intLit 2 .uint64)) env
        (.rhsK .vals [.chain (.addr (.base ⟨aX⟩)) [] []] [] []
          (.seqn #[]) env (.seq rest' env k))) ch
      = .ok (.evalE (.var x) env
            (.strictK .div [] [.intLit 2 .uint64] env
              (.rhsK .vals [.chain (.addr (.base ⟨aX⟩)) [] []] [] []
                (.seqn #[]) env (.seq rest' env k))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have h6 := stepFnIter_one (stepFn_var (σ := stSt h na) (x := x)
    (env := env) (a := ⟨aX⟩)
    (k := .strictK .div [] [.intLit 2 .uint64] env
      (.rhsK .vals [.chain (.addr (.base ⟨aX⟩)) [] []] [] []
        (.seqn #[]) env (.seq rest' env k)))
    (ch := ch) (c := u64c (n : Int)) henv hx)
  have h7 : stepFnIter 2 (stSt h na)
      (.retV (.int (n : Int) .uint64)
        (.strictK .div [] [.intLit 2 .uint64] env
          (.rhsK .vals [.chain (.addr (.base ⟨aX⟩)) [] []] [] []
            (.seqn #[]) env (.seq rest' env k)))) ch
      = .ok (.retV (.int 2 .uint64)
            (.strictK .div [.int (n : Int) .uint64] [] env
              (.rhsK .vals [.chain (.addr (.base ⟨aX⟩)) [] []] [] []
                (.seqn #[]) env (.seq rest' env k))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have h8 := stepFnIter_one (stepFn_strict_apply (σ := stSt h na)
    (σ' := stSt h na) (op := .div) (done := [.int (n : Int) .uint64])
    (v := .int 2 .uint64) (out := .int ((n / 2 : Nat) : Int) .uint64)
    (env := env)
    (k := .rhsK .vals [.chain (.addr (.base ⟨aX⟩)) [] []] [] []
      (.seqn #[]) env (.seq rest' env k))
    (ch := ch) (applyStrictOp_div2 hn))
  have h9 : stepFnIter 1 (stSt h na)
      (.retV (.int ((n / 2 : Nat) : Int) .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨aX⟩)) [] []] [] []
          (.seqn #[]) env (.seq rest' env k))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨aX⟩)) [] []]
            [.int ((n / 2 : Nat) : Int) .uint64] (.seqn #[]) env
            (.seq rest' env k)),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have h10 := stepFnIter_one (stepFn_store_step (σ := stSt h na)
    (σ' := stSt (h.set (.base ⟨aX⟩) (u64c ((n / 2 : Nat) : Int))) na)
    (r := .chain (.addr (.base ⟨aX⟩)) [] [])
    (val := .int ((n / 2 : Nat) : Int) .uint64)
    (rs := []) (vs := []) (body := .seqn #[]) (env := env)
    (k := .seq rest' env k) (ch := ch)
    (storeTarget_addr hx (normU64 _ (by omega))))
  have h11 := stepFnIter_one (stepFn_storeK_nil
    (σ := stSt (h.set (.base ⟨aX⟩) (u64c ((n / 2 : Nat) : Int))) na)
    (body := .seqn #[]) (env := env) (k := .seq rest' env k) (ch := ch))
  have h12 := stepFnIter_one (stepFn_seqn_splice
    (σ := stSt (h.set (.base ⟨aX⟩) (u64c ((n / 2 : Nat) : Int))) na)
    (ss := #[]) (env := env) (rest := rest') (k := k) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4) h5) h6) h7)
          h8) h9) h10) h11) h12

/-- Generic `shift := shift + 1` (same 13-step shape as `seg_asgHalf`). -/
private theorem seg_asgShiftInc (h : Heap) (na : Nat) (env : LocalEnv)
    (aX : Nat) (s : Nat) (rest' : List Stmt) (k : Cont) (ch : Choices)
    (hs : s + 1 < 2 ^ 64)
    (henv : LocalEnv.lookup env "shift" = some (.base ⟨aX⟩))
    (hx : Heap.lookup h (.base ⟨aX⟩) = some (u64c (s : Int))) :
    stepFnIter 13 (stSt h na)
      (.next (.seq (asgShiftInc :: rest') env k)) ch
      = .ok (.next (.seq rest' env k),
          stSt (h.set (.base ⟨aX⟩) (u64c ((s + 1 : Nat) : Int))) na, ch) := by
  show stepFnIter (1 + 1 + 1 + 1 + 1 + 1 + 2 + 1 + 1 + 1 + 1 + 1) _ _ _ = _
  have h1 := stepFnIter_one (stepFn_seq_pop (σ := stSt h na)
    (t := asgShiftInc) (rest := rest') (env := env) (k := k) (ch := ch))
  have h2 : stepFnIter 1 (stSt h na)
      (.exec asgShiftInc env (.seq rest' env k)) ch
      = .ok (.evalE (.ref "shift") env
            (.tgtOpK (.chain []) [] [] [] []
              .vals [.add (.var "shift") (.intLit 1 .uint64)] []
              (.seqn #[]) env (.seq rest' env k)),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have h3 := stepFnIter_one (st_ref_step (σ := stSt h na) (x := "shift")
    (env := env) (l := .base ⟨aX⟩)
    (k := .tgtOpK (.chain []) [] [] [] []
      .vals [.add (.var "shift") (.intLit 1 .uint64)] []
      (.seqn #[]) env (.seq rest' env k)) (ch := ch) henv)
  have h4 : stepFnIter 1 (stSt h na)
      (.retV (.addr (.base ⟨aX⟩))
        (.tgtOpK (.chain []) [] [] [] []
          .vals [.add (.var "shift") (.intLit 1 .uint64)] []
          (.seqn #[]) env (.seq rest' env k))) ch
      = .ok (.evalE (.add (.var "shift") (.intLit 1 .uint64)) env
            (.rhsK .vals [.chain (.addr (.base ⟨aX⟩)) [] []] [] []
              (.seqn #[]) env (.seq rest' env k)),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have h5 : stepFnIter 1 (stSt h na)
      (.evalE (.add (.var "shift") (.intLit 1 .uint64)) env
        (.rhsK .vals [.chain (.addr (.base ⟨aX⟩)) [] []] [] []
          (.seqn #[]) env (.seq rest' env k))) ch
      = .ok (.evalE (.var "shift") env
            (.strictK .add [] [.intLit 1 .uint64] env
              (.rhsK .vals [.chain (.addr (.base ⟨aX⟩)) [] []] [] []
                (.seqn #[]) env (.seq rest' env k))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have h6 := stepFnIter_one (stepFn_var (σ := stSt h na) (x := "shift")
    (env := env) (a := ⟨aX⟩)
    (k := .strictK .add [] [.intLit 1 .uint64] env
      (.rhsK .vals [.chain (.addr (.base ⟨aX⟩)) [] []] [] []
        (.seqn #[]) env (.seq rest' env k)))
    (ch := ch) (c := u64c (s : Int)) henv hx)
  have h7 : stepFnIter 2 (stSt h na)
      (.retV (.int (s : Int) .uint64)
        (.strictK .add [] [.intLit 1 .uint64] env
          (.rhsK .vals [.chain (.addr (.base ⟨aX⟩)) [] []] [] []
            (.seqn #[]) env (.seq rest' env k)))) ch
      = .ok (.retV (.int 1 .uint64)
            (.strictK .add [.int (s : Int) .uint64] [] env
              (.rhsK .vals [.chain (.addr (.base ⟨aX⟩)) [] []] [] []
                (.seqn #[]) env (.seq rest' env k))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have h8 := stepFnIter_one (stepFn_strict_apply (σ := stSt h na)
    (σ' := stSt h na) (op := .add) (done := [.int (s : Int) .uint64])
    (v := .int 1 .uint64) (out := .int ((s + 1 : Nat) : Int) .uint64)
    (env := env)
    (k := .rhsK .vals [.chain (.addr (.base ⟨aX⟩)) [] []] [] []
      (.seqn #[]) env (.seq rest' env k))
    (ch := ch) (applyStrictOp_add1 hs))
  have h9 : stepFnIter 1 (stSt h na)
      (.retV (.int ((s + 1 : Nat) : Int) .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨aX⟩)) [] []] [] []
          (.seqn #[]) env (.seq rest' env k))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨aX⟩)) [] []]
            [.int ((s + 1 : Nat) : Int) .uint64] (.seqn #[]) env
            (.seq rest' env k)),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have h10 := stepFnIter_one (stepFn_store_step (σ := stSt h na)
    (σ' := stSt (h.set (.base ⟨aX⟩) (u64c ((s + 1 : Nat) : Int))) na)
    (r := .chain (.addr (.base ⟨aX⟩)) [] [])
    (val := .int ((s + 1 : Nat) : Int) .uint64)
    (rs := []) (vs := []) (body := .seqn #[]) (env := env)
    (k := .seq rest' env k) (ch := ch)
    (storeTarget_addr hx (normU64 _ (by omega))))
  have h11 := stepFnIter_one (stepFn_storeK_nil
    (σ := stSt (h.set (.base ⟨aX⟩) (u64c ((s + 1 : Nat) : Int))) na)
    (body := .seqn #[]) (env := env) (k := .seq rest' env k) (ch := ch))
  have h12 := stepFnIter_one (stepFn_seqn_splice
    (σ := stSt (h.set (.base ⟨aX⟩) (u64c ((s + 1 : Nat) : Int))) na)
    (ss := #[]) (env := env) (rest := rest') (k := k) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4) h5) h6) h7)
          h8) h9) h10) h11) h12

/-! ## Loop 1 (↔ `commonTwos`) -/

private def envL1c0 (n0 : Nat) : LocalEnv :=
  [("$c0", .base ⟨n0⟩)] :: envLp 8
private def envL1c2 (n0 n2 : Nat) : LocalEnv :=
  [("$c2", .base ⟨n2⟩), ("$c0", .base ⟨n0⟩)] :: envLp 8
private def envL1c1 (n0 n2 n1 : Nat) : LocalEnv :=
  [("$c1", .base ⟨n1⟩)] :: envL1c2 n0 n2

/-- Post-dispatch → the `$c0 := isEven(a)` pair. 3 steps. -/
private theorem l1_toC0 (σ : ExecState) (ch : Choices) :
    stepFnIter 3 σ l1Post ch
      = .ok (.exec c0Seqn ([] :: envLp 8)
            (.seq [c2Seqn, innerIf1, exitIf1, iter1Blk] ([] :: envLp 8)
              loopK1),
          σ, ch) := by
  with_unfolding_all rfl

/-- `$c2 := $c0` (init + copy). 13 steps; appends the `$c2` cell. -/
private theorem l1_c2seg (g : Heap) (na n0 : Nat) (e : Bool) (ch : Choices)
    (hc0 : Heap.lookup g (.base ⟨n0⟩) = some (bcc e))
    (hfr : FreshFrom g na) :
    stepFnIter 13 (stSt g na)
      (.next (.seq [c2Seqn, innerIf1, exitIf1, iter1Blk] (envL1c0 n0)
        loopK1)) ch
      = .ok (.next (.seq [innerIf1, exitIf1, iter1Blk] (envL1c2 n0 na)
            loopK1),
          stSt (g ++ [(.base ⟨na⟩, bcc e)]) (na + 1), ch) := by
  show stepFnIter (1 + 1 + 1 + 1 + 1 + 3 + 1 + 1 + 1 + 1 + 1) _ _ _ = _
  have p1 := stepFnIter_one (stepFn_seq_pop (σ := stSt g na)
    (t := c2Seqn) (rest := [innerIf1, exitIf1, iter1Blk])
    (env := envL1c0 n0) (k := loopK1) (ch := ch))
  have p2 : stepFnIter 1 (stSt g na)
      (.exec c2Seqn (envL1c0 n0)
        (.seq [innerIf1, exitIf1, iter1Blk] (envL1c0 n0) loopK1)) ch
      = .ok (.next (.seq (.initialization { id := "$c2", typ := .bool }
              :: .assign (.var "$c2") (.var "$c0")
              :: [innerIf1, exitIf1, iter1Blk]) (envL1c0 n0) loopK1),
          stSt g na, ch) :=
    stepFnIter_one (stepFn_seqn_splice (σ := stSt g na)
      (ss := #[.initialization { id := "$c2", typ := .bool },
               .assign (.var "$c2") (.var "$c0")])
      (env := envL1c0 n0) (rest := [innerIf1, exitIf1, iter1Blk])
      (k := loopK1) (ch := ch))
  have p3 := stepFnIter_one (stepFn_seq_pop (σ := stSt g na)
    (t := .initialization { id := "$c2", typ := .bool })
    (rest := .assign (.var "$c2") (.var "$c0")
      :: [innerIf1, exitIf1, iter1Blk])
    (env := envL1c0 n0) (k := loopK1) (ch := ch))
  have p4 : stepFnIter 1 (stSt g na)
      (.exec (.initialization { id := "$c2", typ := .bool }) (envL1c0 n0)
        (.seq (.assign (.var "$c2") (.var "$c0")
          :: [innerIf1, exitIf1, iter1Blk]) (envL1c0 n0) loopK1)) ch
      = .ok (.next (.seq (.assign (.var "$c2") (.var "$c0")
              :: [innerIf1, exitIf1, iter1Blk]) (envL1c2 n0 na) loopK1),
          stSt (g ++ [(.base ⟨na⟩, bcc false)]) (na + 1), ch) := by
    have hstep := stepFn_init_seq (σ := stSt g na)
      (p := { id := "$c2", typ := .bool })
      (rest := .assign (.var "$c2") (.var "$c0")
        :: [innerIf1, exitIf1, iter1Blk])
      (env := envL1c0 n0) (k := loopK1) (ch := ch) (v := .bool false)
      (by with_unfolding_all rfl)
    rw [show Heap.set (stSt g na).heap (.base ⟨(stSt g na).nextAddr⟩)
        ⟨some Ty.bool, .bool false⟩ = g ++ [(.base ⟨na⟩, bcc false)] from
      set_fresh (hfr na (by omega))] at hstep
    exact stepFnIter_one hstep
  have p5 := stepFnIter_one (stepFn_seq_pop
    (σ := stSt (g ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
    (t := .assign (.var "$c2") (.var "$c0"))
    (rest := [innerIf1, exitIf1, iter1Blk])
    (env := envL1c2 n0 na) (k := loopK1) (ch := ch))
  have p6 : stepFnIter 3 (stSt (g ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (.exec (.assign (.var "$c2") (.var "$c0")) (envL1c2 n0 na)
        (.seq [innerIf1, exitIf1, iter1Blk] (envL1c2 n0 na) loopK1)) ch
      = .ok (.evalE (.var "$c0") (envL1c2 n0 na)
            (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
              (.seqn #[]) (envL1c2 n0 na)
              (.seq [innerIf1, exitIf1, iter1Blk] (envL1c2 n0 na) loopK1)),
          stSt (g ++ [(.base ⟨na⟩, bcc false)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have p7 : stepFnIter 1 (stSt (g ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (.evalE (.var "$c0") (envL1c2 n0 na)
        (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
          (.seqn #[]) (envL1c2 n0 na)
          (.seq [innerIf1, exitIf1, iter1Blk] (envL1c2 n0 na) loopK1))) ch
      = .ok (.retV (.bool e)
            (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
              (.seqn #[]) (envL1c2 n0 na)
              (.seq [innerIf1, exitIf1, iter1Blk] (envL1c2 n0 na) loopK1)),
          stSt (g ++ [(.base ⟨na⟩, bcc false)]) (na + 1), ch) :=
    stepFnIter_one (stepFn_var
      (σ := stSt (g ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (x := "$c0") (env := envL1c2 n0 na) (a := ⟨n0⟩)
      (k := .rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
        (.seqn #[]) (envL1c2 n0 na)
        (.seq [innerIf1, exitIf1, iter1Blk] (envL1c2 n0 na) loopK1))
      (ch := ch) (c := bcc e) rfl (lookup_append_left hc0))
  have p8 : stepFnIter 1 (stSt (g ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (.retV (.bool e)
        (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
          (.seqn #[]) (envL1c2 n0 na)
          (.seq [innerIf1, exitIf1, iter1Blk] (envL1c2 n0 na) loopK1))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
            [.bool e] (.seqn #[]) (envL1c2 n0 na)
            (.seq [innerIf1, exitIf1, iter1Blk] (envL1c2 n0 na) loopK1)),
          stSt (g ++ [(.base ⟨na⟩, bcc false)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have hc2cell : Heap.lookup (g ++ [(.base ⟨na⟩, bcc false)])
      (.base ⟨na⟩) = some (bcc false) := by
    rw [lookup_append_right (hfr na (by omega))]
    exact lookup_cons_self
  have p9 : stepFnIter 1 (stSt (g ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
        [.bool e] (.seqn #[]) (envL1c2 n0 na)
        (.seq [innerIf1, exitIf1, iter1Blk] (envL1c2 n0 na) loopK1))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envL1c2 n0 na)
            (.seq [innerIf1, exitIf1, iter1Blk] (envL1c2 n0 na) loopK1)),
          stSt (g ++ [(.base ⟨na⟩, bcc e)]) (na + 1), ch) := by
    have hstore := stepFn_store_step
      (σ := stSt (g ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (σ' := { stSt (g ++ [(.base ⟨na⟩, bcc false)]) (na + 1) with
        heap := Heap.set (g ++ [(.base ⟨na⟩, bcc false)]) (.base ⟨na⟩)
          (bcc e) })
      (r := .chain (.addr (.base ⟨na⟩)) [] []) (val := .bool e)
      (rs := []) (vs := []) (body := .seqn #[]) (env := envL1c2 n0 na)
      (k := .seq [innerIf1, exitIf1, iter1Blk] (envL1c2 n0 na) loopK1)
      (ch := ch) (storeTarget_addr hc2cell (normBool _ _))
    rw [show Heap.set (g ++ [(.base ⟨na⟩, bcc false)]) (.base ⟨na⟩) (bcc e)
        = g ++ [(.base ⟨na⟩, bcc e)] from by
      rw [set_append_right (hfr na (by omega)), set_singleton_self]]
      at hstore
    exact stepFnIter_one hstore
  have p10 := stepFnIter_one (stepFn_storeK_nil
    (σ := stSt (g ++ [(.base ⟨na⟩, bcc e)]) (na + 1))
    (body := .seqn #[]) (env := envL1c2 n0 na)
    (k := .seq [innerIf1, exitIf1, iter1Blk] (envL1c2 n0 na) loopK1)
    (ch := ch))
  have p11 := stepFnIter_one (stepFn_seqn_splice
    (σ := stSt (g ++ [(.base ⟨na⟩, bcc e)]) (na + 1))
    (ss := #[]) (env := envL1c2 n0 na)
    (rest := [innerIf1, exitIf1, iter1Blk]) (k := loopK1) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain p1 p2) p3) p4) p5) p6) p7) p8) p9) p10) p11

/-- Inner-if TRUE → the `$c1 := isEven(b)` pair. 3 steps. -/
private theorem l1_c1entry (σ : ExecState) (n0 n2 : Nat) (ch : Choices) :
    stepFnIter 3 σ
      (.retV (.bool true)
        (.ifK c1Blk (.seqn #[]) (envL1c2 n0 n2)
          (.seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1))) ch
      = .ok (.exec c1Seqn ([] :: envL1c2 n0 n2)
            (.seq [c2AsgSeqn] ([] :: envL1c2 n0 n2)
              (.seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1)),
          σ, ch) := by
  with_unfolding_all rfl

/-- Inner-if FALSE (short-circuit: `isEven(b)` never runs). 2 steps. -/
private theorem l1_skip (σ : ExecState) (n0 n2 : Nat) (ch : Choices) :
    stepFnIter 2 σ
      (.retV (.bool false)
        (.ifK c1Blk (.seqn #[]) (envL1c2 n0 n2)
          (.seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1))) ch
      = .ok (.next (.seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1),
          σ, ch) := by
  show stepFnIter (1 + 1) _ _ _ = _
  have q1 : stepFnIter 1 σ
      (.retV (.bool false)
        (.ifK c1Blk (.seqn #[]) (envL1c2 n0 n2)
          (.seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1))) ch
      = .ok (.exec (.seqn #[]) (envL1c2 n0 n2)
            (.seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1),
          σ, ch) := by
    with_unfolding_all rfl
  have q2 := stepFnIter_one (stepFn_seqn_splice (σ := σ)
    (ss := #[]) (env := envL1c2 n0 n2) (rest := [exitIf1, iter1Blk])
    (k := loopK1) (ch := ch))
  exact stepFnIter_chain q1 q2

/-- `$c2 := $c1` after the second isEven call. 12 steps (writes the
`$c2` cell, pops the then-block scope). -/
private theorem l1_c2asg (g : Heap) (n0 n2 n1 na : Nat) (e eOld : Bool)
    (ch : Choices)
    (hc1 : Heap.lookup g (.base ⟨n1⟩) = some (bcc e))
    (hc2 : Heap.lookup g (.base ⟨n2⟩) = some (bcc eOld)) :
    stepFnIter 12 (stSt g na)
      (.next (.seq [c2AsgSeqn] (envL1c1 n0 n2 n1)
        (.seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1))) ch
      = .ok (.next (.seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1),
          stSt (g.set (.base ⟨n2⟩) (bcc e)) na, ch) := by
  show stepFnIter (1 + 1 + 1 + 3 + 1 + 1 + 1 + 1 + 1 + 1) _ _ _ = _
  have p1 := stepFnIter_one (stepFn_seq_pop (σ := stSt g na)
    (t := c2AsgSeqn) (rest := []) (env := envL1c1 n0 n2 n1)
    (k := .seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1) (ch := ch))
  have p2 := stepFnIter_one (stepFn_seqn_splice (σ := stSt g na)
    (ss := #[.assign (.var "$c2") (.var "$c1")])
    (env := envL1c1 n0 n2 n1) (rest := [])
    (k := .seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1) (ch := ch))
  have p3 := stepFnIter_one (stepFn_seq_pop (σ := stSt g na)
    (t := .assign (.var "$c2") (.var "$c1")) (rest := [])
    (env := envL1c1 n0 n2 n1)
    (k := .seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1) (ch := ch))
  have p4 : stepFnIter 3 (stSt g na)
      (.exec (.assign (.var "$c2") (.var "$c1")) (envL1c1 n0 n2 n1)
        (.seq [] (envL1c1 n0 n2 n1)
          (.seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1))) ch
      = .ok (.evalE (.var "$c1") (envL1c1 n0 n2 n1)
            (.rhsK .vals [.chain (.addr (.base ⟨n2⟩)) [] []] [] []
              (.seqn #[]) (envL1c1 n0 n2 n1)
              (.seq [] (envL1c1 n0 n2 n1)
                (.seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1))),
          stSt g na, ch) := by
    with_unfolding_all rfl
  have p5 := stepFnIter_one (stepFn_var (σ := stSt g na)
    (x := "$c1") (env := envL1c1 n0 n2 n1) (a := ⟨n1⟩)
    (k := .rhsK .vals [.chain (.addr (.base ⟨n2⟩)) [] []] [] []
      (.seqn #[]) (envL1c1 n0 n2 n1)
      (.seq [] (envL1c1 n0 n2 n1)
        (.seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1)))
    (ch := ch) (c := bcc e) rfl hc1)
  have p6 : stepFnIter 1 (stSt g na)
      (.retV (.bool e)
        (.rhsK .vals [.chain (.addr (.base ⟨n2⟩)) [] []] [] []
          (.seqn #[]) (envL1c1 n0 n2 n1)
          (.seq [] (envL1c1 n0 n2 n1)
            (.seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨n2⟩)) [] []]
            [.bool e] (.seqn #[]) (envL1c1 n0 n2 n1)
            (.seq [] (envL1c1 n0 n2 n1)
              (.seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1))),
          stSt g na, ch) := by
    with_unfolding_all rfl
  have p7 := stepFnIter_one (stepFn_store_step (σ := stSt g na)
    (σ' := stSt (g.set (.base ⟨n2⟩) (bcc e)) na)
    (r := .chain (.addr (.base ⟨n2⟩)) [] []) (val := .bool e)
    (rs := []) (vs := []) (body := .seqn #[]) (env := envL1c1 n0 n2 n1)
    (k := .seq [] (envL1c1 n0 n2 n1)
      (.seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1))
    (ch := ch) (storeTarget_addr hc2 (normBool _ _)))
  have p8 := stepFnIter_one (stepFn_storeK_nil
    (σ := stSt (g.set (.base ⟨n2⟩) (bcc e)) na)
    (body := .seqn #[]) (env := envL1c1 n0 n2 n1)
    (k := .seq [] (envL1c1 n0 n2 n1)
      (.seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1)) (ch := ch))
  have p9 := stepFnIter_one (stepFn_seqn_splice
    (σ := stSt (g.set (.base ⟨n2⟩) (bcc e)) na)
    (ss := #[]) (env := envL1c1 n0 n2 n1) (rest := [])
    (k := .seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1) (ch := ch))
  have p10 : stepFnIter 1 (stSt (g.set (.base ⟨n2⟩) (bcc e)) na)
      (.next (.seq [] (envL1c1 n0 n2 n1)
        (.seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1))) ch
      = .ok (.next (.seq [exitIf1, iter1Blk] (envL1c2 n0 n2) loopK1),
          stSt (g.set (.base ⟨n2⟩) (bcc e)) na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain p1 p2) p3)
        p4) p5) p6) p7) p8) p9) p10

/-- Exit-if TRUE → the iteration block's entry. 4 steps (incl. the
block scope push). -/
private theorem l1_toIter (σ : ExecState) (n0 n2 : Nat) (ch : Choices) :
    stepFnIter 4 σ
      (.retV (.bool true)
        (.ifK (.seqn #[]) .breakStmt (envL1c2 n0 n2)
          (.seq [iter1Blk] (envL1c2 n0 n2) loopK1))) ch
      = .ok (.next (.seq [asgHalf "a", asgHalf "b", asgShiftInc]
            ([] :: envL1c2 n0 n2)
            (.seq [] (envL1c2 n0 n2) loopK1)),
          σ, ch) := by
  show stepFnIter (1 + 1 + 1 + 1) _ _ _ = _
  have q1 : stepFnIter 1 σ
      (.retV (.bool true)
        (.ifK (.seqn #[]) .breakStmt (envL1c2 n0 n2)
          (.seq [iter1Blk] (envL1c2 n0 n2) loopK1))) ch
      = .ok (.exec (.seqn #[]) (envL1c2 n0 n2)
            (.seq [iter1Blk] (envL1c2 n0 n2) loopK1), σ, ch) := by
    with_unfolding_all rfl
  have q2 := stepFnIter_one (stepFn_seqn_splice (σ := σ)
    (ss := #[]) (env := envL1c2 n0 n2) (rest := [iter1Blk])
    (k := loopK1) (ch := ch))
  have q3 := stepFnIter_one (stepFn_seq_pop (σ := σ)
    (t := iter1Blk) (rest := []) (env := envL1c2 n0 n2) (k := loopK1)
    (ch := ch))
  have q4 : stepFnIter 1 σ
      (.exec iter1Blk (envL1c2 n0 n2)
        (.seq [] (envL1c2 n0 n2) loopK1)) ch
      = .ok (.next (.seq [asgHalf "a", asgHalf "b", asgShiftInc]
            ([] :: envL1c2 n0 n2)
            (.seq [] (envL1c2 n0 n2) loopK1)),
          σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain q1 q2) q3) q4

/-- Iteration-block tail: scope pops and the loop retest. 3 steps. -/
private theorem l1_iterTail (σ : ExecState) (n0 n2 : Nat) (ch : Choices) :
    stepFnIter 3 σ
      (.next (.seq [] ([] :: envL1c2 n0 n2)
        (.seq [] (envL1c2 n0 n2) loopK1))) ch
      = .ok (l1Head, σ, ch) := by
  with_unfolding_all rfl

/-- Exit-if FALSE → break unwinds to the after-loop point. 4 steps. -/
private theorem l1_break (σ : ExecState) (n0 n2 : Nat) (ch : Choices) :
    stepFnIter 4 σ
      (.retV (.bool false)
        (.ifK (.seqn #[]) .breakStmt (envL1c2 n0 n2)
          (.seq [iter1Blk] (envL1c2 n0 n2) loopK1))) ch
      = .ok (l1Exit, σ, ch) := by
  with_unfolding_all rfl

/-- **One both-even loop-1 iteration**: post-dispatch point back to the
post-dispatch point. 164 steps; cells 4/5/7 halved/halved/incremented,
seven fresh cells appended, everything else preserved. -/
private theorem l1_iter_even (h : Heap) (na av bv sv : Nat) (ch : Choices)
    (hav64 : av < 2 ^ 64) (hbv64 : bv < 2 ^ 64) (hsv1 : sv + 1 < 2 ^ 64)
    (hae : av % 2 = 0) (hbe : bv % 2 = 0)
    (h4 : Heap.lookup h (.base ⟨4⟩) = some (u64c (av : Int)))
    (h5 : Heap.lookup h (.base ⟨5⟩) = some (u64c (bv : Int)))
    (h7 : Heap.lookup h (.base ⟨7⟩) = some (u64c (sv : Int)))
    (h8 : Heap.lookup h (.base ⟨8⟩) = some (bcc false))
    (hfr : FreshFrom h na) :
    ∃ h' : Heap,
      stepFnIter 164 (stSt h na) l1Post ch
        = .ok (l1Post, stSt h' (na + 7), ch)
      ∧ Heap.lookup h' (.base ⟨4⟩) = some (u64c ((av / 2 : Nat) : Int))
      ∧ Heap.lookup h' (.base ⟨5⟩) = some (u64c ((bv / 2 : Nat) : Int))
      ∧ Heap.lookup h' (.base ⟨7⟩) = some (u64c ((sv + 1 : Nat) : Int))
      ∧ Heap.lookup h' (.base ⟨8⟩) = some (bcc false)
      ∧ (∀ (x : Nat) (c : HeapCell), x ≠ 4 → x ≠ 5 → x ≠ 7 →
          Heap.lookup h (.base ⟨x⟩) = some c →
          Heap.lookup h' (.base ⟨x⟩) = some c)
      ∧ FreshFrom h' (na + 7) := by
  have hEa : decide (av % 2 = 0) = true := by simp [hae]
  have hEb : decide (bv % 2 = 0) = true := by simp [hbe]
  have h4lt : 4 < na := hfr.lt_of_lookup h4
  have h5lt : 5 < na := hfr.lt_of_lookup h5
  have h7lt : 7 < na := hfr.lt_of_lookup h7
  have h8lt : 8 < na := hfr.lt_of_lookup h8
  -- A: to the c0 pair
  have s1 := l1_toC0 (stSt h na) ch
  -- B: the c0 span
  have s2 : stepFnIter 36 (stSt h na)
      (.exec c0Seqn ([] :: envLp 8)
        (.seq [c2Seqn, innerIf1, exitIf1, iter1Blk] ([] :: envLp 8)
          loopK1)) ch
      = .ok (.next (.seq [c2Seqn, innerIf1, exitIf1, iter1Blk]
            (envL1c0 na) loopK1),
          stSt (h ++ [(.base ⟨na⟩, bcc true),
                      (.base ⟨na + 1⟩, u64c (av : Int)),
                      (.base ⟨na + 2⟩, bcc true)]) (na + 3), ch) := by
    have hspan := st_ieSeq h na av 4 "$c0" "a" ([] :: envLp 8)
      [c2Seqn, innerIf1, exitIf1, iter1Blk] loopK1 ch hav64 rfl h4 hfr
    rw [hEa] at hspan
    exact hspan
  have hfr1 : FreshFrom (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      (na + 3) := hfr.push3
  -- C: the c2 copy
  have hc0A : Heap.lookup (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      (.base ⟨na⟩) = some (bcc true) := by
    rw [lookup_append_right (hfr na (by omega))]
    exact lookup_cons_self
  have s3 := l1_c2seg (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
    (na + 3) na true ch hc0A hfr1
  have hfr2 : FreshFrom ((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)]) (na + 4) := hfr1.push
  have hc2B : Heap.lookup ((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)]) (.base ⟨na + 3⟩)
      = some (bcc true) := by
    rw [lookup_append_right (hfr1 (na + 3) (by omega))]
    exact lookup_cons_self
  -- D: inner-if delivery (true)
  have s4 := seg_ifVar ((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)]) (na + 4) "$c2"
    (envL1c2 na (na + 3)) (na + 3) true c1Blk (.seqn #[])
    [exitIf1, iter1Blk] loopK1 ch rfl hc2B
  -- E: into the c1 pair
  have s5 := l1_c1entry (stSt ((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)]) (na + 4)) na (na + 3) ch
  -- F: the c1 span
  have h5B : Heap.lookup ((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)]) (.base ⟨5⟩)
      = some (u64c (bv : Int)) :=
    lookup_append_left (lookup_append_left h5)
  have s6 : stepFnIter 36 (stSt ((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)]) (na + 4))
      (.exec c1Seqn ([] :: envL1c2 na (na + 3))
        (.seq [c2AsgSeqn] ([] :: envL1c2 na (na + 3))
          (.seq [exitIf1, iter1Blk] (envL1c2 na (na + 3)) loopK1))) ch
      = .ok (.next (.seq [c2AsgSeqn] (envL1c1 na (na + 3) (na + 4))
            (.seq [exitIf1, iter1Blk] (envL1c2 na (na + 3)) loopK1)),
          stSt (((h ++ [(.base ⟨na⟩, bcc true),
              (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
              ++ [(.base ⟨na + 3⟩, bcc true)])
            ++ [(.base ⟨na + 4⟩, bcc true),
                (.base ⟨na + 5⟩, u64c (bv : Int)),
                (.base ⟨na + 6⟩, bcc true)]) (na + 7), ch) := by
    have hspan := st_ieSeq ((h ++ [(.base ⟨na⟩, bcc true),
        (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
        ++ [(.base ⟨na + 3⟩, bcc true)]) (na + 4) bv 5 "$c1" "b"
      ([] :: envL1c2 na (na + 3)) [c2AsgSeqn]
      (.seq [exitIf1, iter1Blk] (envL1c2 na (na + 3)) loopK1) ch hbv64
      rfl h5B hfr2
    rw [hEb] at hspan
    exact hspan
  have hfr3 : FreshFrom (((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc true), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc true)]) (na + 7) := hfr2.push3
  have hc1C : Heap.lookup (((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc true), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc true)]) (.base ⟨na + 4⟩)
      = some (bcc true) := by
    rw [lookup_append_right (hfr2 (na + 4) (by omega))]
    exact lookup_cons_self
  have hc2C : Heap.lookup (((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc true), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc true)]) (.base ⟨na + 3⟩)
      = some (bcc true) := lookup_append_left hc2B
  -- G: `$c2 := $c1`
  have s7 := l1_c2asg (((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc true), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc true)]) na (na + 3) (na + 4) (na + 7)
    true true ch hc1C hc2C
  have hCset : Heap.set (((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc true), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc true)]) (.base ⟨na + 3⟩) (bcc true)
      = ((h ++ [(.base ⟨na⟩, bcc true),
          (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
          ++ [(.base ⟨na + 3⟩, bcc true)])
        ++ [(.base ⟨na + 4⟩, bcc true), (.base ⟨na + 5⟩, u64c (bv : Int)),
            (.base ⟨na + 6⟩, bcc true)] := by
    rw [set_append_left hc2B,
      set_append_right (hfr1 (na + 3) (by omega)), set_singleton_self]
  rw [hCset] at s7
  -- H: exit-if delivery (true)
  have s8 := seg_ifVar (((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc true), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc true)]) (na + 7) "$c2"
    (envL1c2 na (na + 3)) (na + 3) true (.seqn #[]) .breakStmt
    [iter1Blk] loopK1 ch rfl hc2C
  -- I: into the iteration block
  have s9 := l1_toIter (stSt (((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc true), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc true)]) (na + 7)) na (na + 3) ch
  -- J: the three assignments
  have h4C : Heap.lookup (((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc true), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc true)]) (.base ⟨4⟩)
      = some (u64c (av : Int)) :=
    lookup_append_left (lookup_append_left (lookup_append_left h4))
  have s10 := seg_asgHalf (((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc true), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc true)]) (na + 7) "a"
    ([] :: envL1c2 na (na + 3)) 4 av
    [asgHalf "b", asgShiftInc] (.seq [] (envL1c2 na (na + 3)) loopK1) ch
    hav64 rfl h4C
  have h5C1 : Heap.lookup (Heap.set (((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc true), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc true)]) (.base ⟨4⟩)
      (u64c ((av / 2 : Nat) : Int)))
      (.base ⟨5⟩) = some (u64c (bv : Int)) := by
    rw [lookup_set_other (by omega : 4 ≠ 5)]
    exact lookup_append_left (lookup_append_left (lookup_append_left h5))
  have s11 := seg_asgHalf (Heap.set (((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc true), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc true)]) (.base ⟨4⟩)
      (u64c ((av / 2 : Nat) : Int)))
    (na + 7) "b" ([] :: envL1c2 na (na + 3)) 5 bv [asgShiftInc]
    (.seq [] (envL1c2 na (na + 3)) loopK1) ch hbv64 rfl h5C1
  have h7C2 : Heap.lookup (Heap.set (Heap.set (((h
      ++ [(.base ⟨na⟩, bcc true), (.base ⟨na + 1⟩, u64c (av : Int)),
          (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc true), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc true)]) (.base ⟨4⟩)
      (u64c ((av / 2 : Nat) : Int))) (.base ⟨5⟩)
      (u64c ((bv / 2 : Nat) : Int)))
      (.base ⟨7⟩) = some (u64c (sv : Int)) := by
    rw [lookup_set_other (by omega : 5 ≠ 7),
      lookup_set_other (by omega : 4 ≠ 7)]
    exact lookup_append_left (lookup_append_left (lookup_append_left h7))
  have s12 := seg_asgShiftInc (Heap.set (Heap.set (((h
      ++ [(.base ⟨na⟩, bcc true), (.base ⟨na + 1⟩, u64c (av : Int)),
          (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc true), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc true)]) (.base ⟨4⟩)
      (u64c ((av / 2 : Nat) : Int))) (.base ⟨5⟩)
      (u64c ((bv / 2 : Nat) : Int)))
    (na + 7) ([] :: envL1c2 na (na + 3)) 7 sv []
    (.seq [] (envL1c2 na (na + 3)) loopK1) ch hsv1 rfl h7C2
  -- K: tail + retest, then the flag-false dispatch
  have s13 := l1_iterTail
    (stSt (Heap.set (Heap.set (Heap.set (((h
        ++ [(.base ⟨na⟩, bcc true), (.base ⟨na + 1⟩, u64c (av : Int)),
            (.base ⟨na + 2⟩, bcc true)])
        ++ [(.base ⟨na + 3⟩, bcc true)])
        ++ [(.base ⟨na + 4⟩, bcc true), (.base ⟨na + 5⟩, u64c (bv : Int)),
            (.base ⟨na + 6⟩, bcc true)]) (.base ⟨4⟩)
        (u64c ((av / 2 : Nat) : Int))) (.base ⟨5⟩)
        (u64c ((bv / 2 : Nat) : Int))) (.base ⟨7⟩)
        (u64c ((sv + 1 : Nat) : Int))) (na + 7)) na (na + 3) ch
  have h8H : Heap.lookup (Heap.set (Heap.set (Heap.set (((h
      ++ [(.base ⟨na⟩, bcc true), (.base ⟨na + 1⟩, u64c (av : Int)),
          (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc true), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc true)]) (.base ⟨4⟩)
      (u64c ((av / 2 : Nat) : Int))) (.base ⟨5⟩)
      (u64c ((bv / 2 : Nat) : Int))) (.base ⟨7⟩)
      (u64c ((sv + 1 : Nat) : Int)))
      (.base ⟨8⟩) = some (bcc false) := by
    rw [lookup_set_other (by omega : 7 ≠ 8),
      lookup_set_other (by omega : 5 ≠ 8),
      lookup_set_other (by omega : 4 ≠ 8)]
    exact lookup_append_left (lookup_append_left (lookup_append_left h8))
  have s14 := lp_disp_f (Heap.set (Heap.set (Heap.set (((h
      ++ [(.base ⟨na⟩, bcc true), (.base ⟨na + 1⟩, u64c (av : Int)),
          (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc true), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc true)]) (.base ⟨4⟩)
      (u64c ((av / 2 : Nat) : Int))) (.base ⟨5⟩)
      (u64c ((bv / 2 : Nat) : Int))) (.base ⟨7⟩)
      (u64c ((sv + 1 : Nat) : Int)))
    (na + 7) 8 condSeqn1 exitIf1 iter1Blk (envLp 8) K1after ch rfl h8H
  -- assemble
  refine ⟨Heap.set (Heap.set (Heap.set (((h
      ++ [(.base ⟨na⟩, bcc true), (.base ⟨na + 1⟩, u64c (av : Int)),
          (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc true), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc true)]) (.base ⟨4⟩)
      (u64c ((av / 2 : Nat) : Int))) (.base ⟨5⟩)
      (u64c ((bv / 2 : Nat) : Int))) (.base ⟨7⟩)
      (u64c ((sv + 1 : Nat) : Int)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show stepFnIter (3 + 36 + 13 + 3 + 3 + 36 + 12 + 3 + 4 + 13 + 13 + 13
      + 3 + 9) _ _ _ = _
    exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
            (stepFnIter_chain s1 s2) s3) s4) s5) s6) s7) s8) s9) s10)
              s11) s12) s13) s14
  · rw [lookup_set_other (by omega : 7 ≠ 4),
      lookup_set_other (by omega : 5 ≠ 4)]
    exact lookup_set_self
  · rw [lookup_set_other (by omega : 7 ≠ 5)]
    exact lookup_set_self
  · exact lookup_set_self
  · exact h8H
  · intro x c hx4 hx5 hx7 hc
    rw [lookup_set_other (by omega : 7 ≠ x),
      lookup_set_other (by omega : 5 ≠ x),
      lookup_set_other (by omega : 4 ≠ x)]
    exact lookup_append_left (lookup_append_left (lookup_append_left hc))
  · exact ((hfr3.set (by omega)).set (by omega)).set (by omega)


/-- **Loop-1 exit, short-circuit** (`a` odd — `isEven(b)` never runs):
post-dispatch point → the after-loop point. 64 steps, four cells
appended, nothing else touched. -/
private theorem l1_exit_short (h : Heap) (na av : Nat) (ch : Choices)
    (hav64 : av < 2 ^ 64) (hao : av % 2 = 1)
    (h4 : Heap.lookup h (.base ⟨4⟩) = some (u64c (av : Int)))
    (hfr : FreshFrom h na) :
    ∃ h' : Heap,
      stepFnIter 64 (stSt h na) l1Post ch
        = .ok (l1Exit, stSt h' (na + 4), ch)
      ∧ (∀ (x : Nat) (c : HeapCell),
          Heap.lookup h (.base ⟨x⟩) = some c →
          Heap.lookup h' (.base ⟨x⟩) = some c)
      ∧ FreshFrom h' (na + 4) := by
  have hEa : decide (av % 2 = 0) = false := by simp; omega
  have s1 := l1_toC0 (stSt h na) ch
  have s2 : stepFnIter 36 (stSt h na)
      (.exec c0Seqn ([] :: envLp 8)
        (.seq [c2Seqn, innerIf1, exitIf1, iter1Blk] ([] :: envLp 8)
          loopK1)) ch
      = .ok (.next (.seq [c2Seqn, innerIf1, exitIf1, iter1Blk]
            (envL1c0 na) loopK1),
          stSt (h ++ [(.base ⟨na⟩, bcc false),
                      (.base ⟨na + 1⟩, u64c (av : Int)),
                      (.base ⟨na + 2⟩, bcc false)]) (na + 3), ch) := by
    have hspan := st_ieSeq h na av 4 "$c0" "a" ([] :: envLp 8)
      [c2Seqn, innerIf1, exitIf1, iter1Blk] loopK1 ch hav64 rfl h4 hfr
    rw [hEa] at hspan
    exact hspan
  have hfr1 : FreshFrom (h ++ [(.base ⟨na⟩, bcc false),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc false)])
      (na + 3) := hfr.push3
  have hc0A : Heap.lookup (h ++ [(.base ⟨na⟩, bcc false),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc false)])
      (.base ⟨na⟩) = some (bcc false) := by
    rw [lookup_append_right (hfr na (by omega))]
    exact lookup_cons_self
  have s3 := l1_c2seg (h ++ [(.base ⟨na⟩, bcc false),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc false)])
    (na + 3) na false ch hc0A hfr1
  have hc2B : Heap.lookup ((h ++ [(.base ⟨na⟩, bcc false),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc false)])
      ++ [(.base ⟨na + 3⟩, bcc false)]) (.base ⟨na + 3⟩)
      = some (bcc false) := by
    rw [lookup_append_right (hfr1 (na + 3) (by omega))]
    exact lookup_cons_self
  have s4 := seg_ifVar ((h ++ [(.base ⟨na⟩, bcc false),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc false)])
      ++ [(.base ⟨na + 3⟩, bcc false)]) (na + 4) "$c2"
    (envL1c2 na (na + 3)) (na + 3) false c1Blk (.seqn #[])
    [exitIf1, iter1Blk] loopK1 ch rfl hc2B
  have s5 := l1_skip (stSt ((h ++ [(.base ⟨na⟩, bcc false),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc false)])
      ++ [(.base ⟨na + 3⟩, bcc false)]) (na + 4)) na (na + 3) ch
  have s6 := seg_ifVar ((h ++ [(.base ⟨na⟩, bcc false),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc false)])
      ++ [(.base ⟨na + 3⟩, bcc false)]) (na + 4) "$c2"
    (envL1c2 na (na + 3)) (na + 3) false (.seqn #[]) .breakStmt
    [iter1Blk] loopK1 ch rfl hc2B
  have s7 := l1_break (stSt ((h ++ [(.base ⟨na⟩, bcc false),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc false)])
      ++ [(.base ⟨na + 3⟩, bcc false)]) (na + 4)) na (na + 3) ch
  refine ⟨(h ++ [(.base ⟨na⟩, bcc false),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc false)])
      ++ [(.base ⟨na + 3⟩, bcc false)], ?_, ?_, ?_⟩
  · show stepFnIter (3 + 36 + 13 + 3 + 2 + 3 + 4) _ _ _ = _
    exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain s1 s2) s3)
        s4) s5) s6) s7
  · intro x c hc
    exact lookup_append_left (lookup_append_left hc)
  · exact hfr1.push

/-- **Loop-1 exit, both tests run** (`a` even, `b` odd): post-dispatch
point → the after-loop point. 113 steps, seven cells appended. -/
private theorem l1_exit_long (h : Heap) (na av bv : Nat) (ch : Choices)
    (hav64 : av < 2 ^ 64) (hbv64 : bv < 2 ^ 64)
    (hae : av % 2 = 0) (hbo : bv % 2 = 1)
    (h4 : Heap.lookup h (.base ⟨4⟩) = some (u64c (av : Int)))
    (h5 : Heap.lookup h (.base ⟨5⟩) = some (u64c (bv : Int)))
    (hfr : FreshFrom h na) :
    ∃ h' : Heap,
      stepFnIter 113 (stSt h na) l1Post ch
        = .ok (l1Exit, stSt h' (na + 7), ch)
      ∧ (∀ (x : Nat) (c : HeapCell),
          Heap.lookup h (.base ⟨x⟩) = some c →
          Heap.lookup h' (.base ⟨x⟩) = some c)
      ∧ FreshFrom h' (na + 7) := by
  have hEa : decide (av % 2 = 0) = true := by simp [hae]
  have hEb : decide (bv % 2 = 0) = false := by simp; omega
  have s1 := l1_toC0 (stSt h na) ch
  have s2 : stepFnIter 36 (stSt h na)
      (.exec c0Seqn ([] :: envLp 8)
        (.seq [c2Seqn, innerIf1, exitIf1, iter1Blk] ([] :: envLp 8)
          loopK1)) ch
      = .ok (.next (.seq [c2Seqn, innerIf1, exitIf1, iter1Blk]
            (envL1c0 na) loopK1),
          stSt (h ++ [(.base ⟨na⟩, bcc true),
                      (.base ⟨na + 1⟩, u64c (av : Int)),
                      (.base ⟨na + 2⟩, bcc true)]) (na + 3), ch) := by
    have hspan := st_ieSeq h na av 4 "$c0" "a" ([] :: envLp 8)
      [c2Seqn, innerIf1, exitIf1, iter1Blk] loopK1 ch hav64 rfl h4 hfr
    rw [hEa] at hspan
    exact hspan
  have hfr1 : FreshFrom (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      (na + 3) := hfr.push3
  have hc0A : Heap.lookup (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      (.base ⟨na⟩) = some (bcc true) := by
    rw [lookup_append_right (hfr na (by omega))]
    exact lookup_cons_self
  have s3 := l1_c2seg (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
    (na + 3) na true ch hc0A hfr1
  have hfr2 : FreshFrom ((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)]) (na + 4) := hfr1.push
  have hc2B : Heap.lookup ((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)]) (.base ⟨na + 3⟩)
      = some (bcc true) := by
    rw [lookup_append_right (hfr1 (na + 3) (by omega))]
    exact lookup_cons_self
  have s4 := seg_ifVar ((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)]) (na + 4) "$c2"
    (envL1c2 na (na + 3)) (na + 3) true c1Blk (.seqn #[])
    [exitIf1, iter1Blk] loopK1 ch rfl hc2B
  have s5 := l1_c1entry (stSt ((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)]) (na + 4)) na (na + 3) ch
  have h5B : Heap.lookup ((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)]) (.base ⟨5⟩)
      = some (u64c (bv : Int)) :=
    lookup_append_left (lookup_append_left h5)
  have s6 : stepFnIter 36 (stSt ((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)]) (na + 4))
      (.exec c1Seqn ([] :: envL1c2 na (na + 3))
        (.seq [c2AsgSeqn] ([] :: envL1c2 na (na + 3))
          (.seq [exitIf1, iter1Blk] (envL1c2 na (na + 3)) loopK1))) ch
      = .ok (.next (.seq [c2AsgSeqn] (envL1c1 na (na + 3) (na + 4))
            (.seq [exitIf1, iter1Blk] (envL1c2 na (na + 3)) loopK1)),
          stSt (((h ++ [(.base ⟨na⟩, bcc true),
              (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
              ++ [(.base ⟨na + 3⟩, bcc true)])
            ++ [(.base ⟨na + 4⟩, bcc false),
                (.base ⟨na + 5⟩, u64c (bv : Int)),
                (.base ⟨na + 6⟩, bcc false)]) (na + 7), ch) := by
    have hspan := st_ieSeq ((h ++ [(.base ⟨na⟩, bcc true),
        (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
        ++ [(.base ⟨na + 3⟩, bcc true)]) (na + 4) bv 5 "$c1" "b"
      ([] :: envL1c2 na (na + 3)) [c2AsgSeqn]
      (.seq [exitIf1, iter1Blk] (envL1c2 na (na + 3)) loopK1) ch hbv64
      rfl h5B hfr2
    rw [hEb] at hspan
    exact hspan
  have hc1C : Heap.lookup (((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc false), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc false)]) (.base ⟨na + 4⟩)
      = some (bcc false) := by
    rw [lookup_append_right (hfr2 (na + 4) (by omega))]
    exact lookup_cons_self
  have hc2C : Heap.lookup (((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc false), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc false)]) (.base ⟨na + 3⟩)
      = some (bcc true) := lookup_append_left hc2B
  have s7 := l1_c2asg (((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc false), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc false)]) na (na + 3) (na + 4) (na + 7)
    false true ch hc1C hc2C
  have hCset : Heap.set (((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc true)])
      ++ [(.base ⟨na + 4⟩, bcc false), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc false)]) (.base ⟨na + 3⟩) (bcc false)
      = ((h ++ [(.base ⟨na⟩, bcc true),
          (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
          ++ [(.base ⟨na + 3⟩, bcc false)])
        ++ [(.base ⟨na + 4⟩, bcc false), (.base ⟨na + 5⟩, u64c (bv : Int)),
            (.base ⟨na + 6⟩, bcc false)] := by
    rw [set_append_left hc2B,
      set_append_right (hfr1 (na + 3) (by omega)), set_singleton_self]
  rw [hCset] at s7
  have hc2D : Heap.lookup (((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc false)])
      ++ [(.base ⟨na + 4⟩, bcc false), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc false)]) (.base ⟨na + 3⟩)
      = some (bcc false) := by
    refine lookup_append_left ?_
    rw [lookup_append_right (hfr1 (na + 3) (by omega))]
    exact lookup_cons_self
  have s8 := seg_ifVar (((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc false)])
      ++ [(.base ⟨na + 4⟩, bcc false), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc false)]) (na + 7) "$c2"
    (envL1c2 na (na + 3)) (na + 3) false (.seqn #[]) .breakStmt
    [iter1Blk] loopK1 ch rfl hc2D
  have s9 := l1_break (stSt (((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc false)])
      ++ [(.base ⟨na + 4⟩, bcc false), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc false)]) (na + 7)) na (na + 3) ch
  refine ⟨((h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      ++ [(.base ⟨na + 3⟩, bcc false)])
      ++ [(.base ⟨na + 4⟩, bcc false), (.base ⟨na + 5⟩, u64c (bv : Int)),
          (.base ⟨na + 6⟩, bcc false)], ?_, ?_, ?_⟩
  · show stepFnIter (3 + 36 + 13 + 3 + 3 + 36 + 12 + 3 + 4) _ _ _ = _
    exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain s1 s2) s3) s4) s5) s6) s7)
          s8) s9
  · intro x c hc
    exact lookup_append_left (lookup_append_left (lookup_append_left hc))
  · exact hfr1.push.push3

/-- **LOOP 1**, by strong induction on `av + bv`, against
`commonTwos`'s branch equations: from the post-dispatch point at cells
`(av, bv, sv)`, the run reaches the after-loop point with the shared
twos stripped and counted. -/
private theorem l1_run : ∀ μ av bv sv : Nat, av + bv = μ →
    1 ≤ av → 1 ≤ bv → av < 2 ^ 64 → bv < 2 ^ 64 →
    sv + commonTwos av bv < 2 ^ 64 →
    ∀ (h : Heap) (na : Nat) (ch : Choices),
    Heap.lookup h (.base ⟨4⟩) = some (u64c (av : Int)) →
    Heap.lookup h (.base ⟨5⟩) = some (u64c (bv : Int)) →
    Heap.lookup h (.base ⟨7⟩) = some (u64c (sv : Int)) →
    Heap.lookup h (.base ⟨8⟩) = some (bcc false) →
    FreshFrom h na →
    ∃ (k : Nat) (h' : Heap) (na' : Nat), k ≤ 164 * μ + 120 ∧
      stepFnIter k (stSt h na) l1Post ch = .ok (l1Exit, stSt h' na', ch)
      ∧ Heap.lookup h' (.base ⟨4⟩)
          = some (u64c ((av / 2 ^ commonTwos av bv : Nat) : Int))
      ∧ Heap.lookup h' (.base ⟨5⟩)
          = some (u64c ((bv / 2 ^ commonTwos av bv : Nat) : Int))
      ∧ Heap.lookup h' (.base ⟨7⟩)
          = some (u64c ((sv + commonTwos av bv : Nat) : Int))
      ∧ (∀ (x : Nat) (c : HeapCell), x ≠ 4 → x ≠ 5 → x ≠ 7 →
          Heap.lookup h (.base ⟨x⟩) = some c →
          Heap.lookup h' (.base ⟨x⟩) = some c)
      ∧ FreshFrom h' na' ∧ na ≤ na' := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro av bv sv hμ hav hbv hav64 hbv64 hsv h na ch h4 h5 h7 h8 hfr
    by_cases hae : av % 2 = 0
    · by_cases hbe : bv % 2 = 0
      · -- both even: one iteration, then recurse at the halves
        have hct := commonTwos_even av bv (by omega) hae hbe
        obtain ⟨H, hrun, H4, H5, H7, H8, Hpres, Hfr⟩ :=
          l1_iter_even h na av bv sv ch hav64 hbv64 (by omega) hae hbe
            h4 h5 h7 h8 hfr
        obtain ⟨k, h', na', hk, hrun', h4', h5', h7', hpres', hfr', hna'⟩ :=
          ih (av / 2 + bv / 2) (by omega) (av / 2) (bv / 2) (sv + 1) rfl
            (by omega) (by omega) (by omega) (by omega) (by omega)
            H (na + 7) ch H4 H5 H7 H8 Hfr
        have hdivA : av / 2 ^ commonTwos av bv
            = av / 2 / 2 ^ commonTwos (av / 2) (bv / 2) := by
          rw [hct, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
        have hdivB : bv / 2 ^ commonTwos av bv
            = bv / 2 / 2 ^ commonTwos (av / 2) (bv / 2) := by
          rw [hct, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
        have hshift : sv + commonTwos av bv
            = sv + 1 + commonTwos (av / 2) (bv / 2) := by
          rw [hct]; omega
        refine ⟨164 + k, h', na', by omega,
          stepFnIter_chain hrun hrun', ?_, ?_, ?_, ?_, hfr', by omega⟩
        · rw [hdivA]; exact h4'
        · rw [hdivB]; exact h5'
        · rw [hshift]; exact h7'
        · intro x c hx4 hx5 hx7 hc
          exact hpres' x c hx4 hx5 hx7 (Hpres x c hx4 hx5 hx7 hc)
      · -- `b` odd: the long exit; no shared twos
        have hct0 : commonTwos av bv = 0 :=
          commonTwos_odd_right av bv (by omega)
        obtain ⟨h', hrun, hpres, hfr'⟩ :=
          l1_exit_long h na av bv ch hav64 hbv64 hae (by omega) h4 h5 hfr
        refine ⟨113, h', na + 7, by omega, hrun, ?_, ?_, ?_, ?_, hfr',
          by omega⟩
        · simp only [hct0, Nat.pow_zero, Nat.div_one]
          exact hpres 4 _ h4
        · simp only [hct0, Nat.pow_zero, Nat.div_one]
          exact hpres 5 _ h5
        · simp only [hct0, Nat.add_zero]
          exact hpres 7 _ h7
        · exact fun x c _ _ _ hc => hpres x c hc
    · -- `a` odd: the short-circuit exit; no shared twos
      have hct0 : commonTwos av bv = 0 :=
        commonTwos_odd_left av bv (by omega)
      obtain ⟨h', hrun, hpres, hfr'⟩ :=
        l1_exit_short h na av ch hav64 (by omega) h4 hfr
      refine ⟨64, h', na + 4, by omega, hrun, ?_, ?_, ?_, ?_, hfr',
        by omega⟩
      · simp only [hct0, Nat.pow_zero, Nat.div_one]
        exact hpres 4 _ h4
      · simp only [hct0, Nat.pow_zero, Nat.div_one]
        exact hpres 5 _ h5
      · simp only [hct0, Nat.add_zero]
        exact hpres 7 _ h7
      · exact fun x c _ _ _ hc => hpres x c hc

/-! ## Loop 2 (↔ `stripTwos` on `a`) -/

private def envL2c3 (f n3 : Nat) : LocalEnv :=
  [("$c3", .base ⟨n3⟩)] :: envLp f

/-- Loop-1 exit → the loop-2 head: `block2` entry, the fresh
`$forFirst` allocation and raise. 15 steps. -/
private theorem l1_to_l2 (h : Heap) (na : Nat) (ch : Choices)
    (hfr : FreshFrom h na) :
    stepFnIter 15 (stSt h na) l1Exit ch
      = .ok (l2Head na, stSt (h ++ [(.base ⟨na⟩, bcc true)]) (na + 1),
          ch) := by
  show stepFnIter (4 + 1 + 1 + 2 + 1 + 2 + 1 + 1 + 1 + 1) _ _ _ = _
  have s1 : stepFnIter 4 (stSt h na) l1Exit ch
      = .ok (.exec (.initialization { id := "$forFirst", typ := .bool })
            ([] :: envSh)
            (.seq [ffTrue, .while (.boolLit true) body2] ([] :: envSh)
              K2after),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have s2 : stepFnIter 1 (stSt h na)
      (.exec (.initialization { id := "$forFirst", typ := .bool })
        ([] :: envSh)
        (.seq [ffTrue, .while (.boolLit true) body2] ([] :: envSh)
          K2after)) ch
      = .ok (.next (.seq [ffTrue, .while (.boolLit true) body2]
            (envLp na) K2after),
          stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1), ch) := by
    have hstep := stepFn_init_seq (σ := stSt h na)
      (p := { id := "$forFirst", typ := .bool })
      (rest := [ffTrue, .while (.boolLit true) body2])
      (env := [] :: envSh) (k := K2after) (ch := ch) (v := .bool false)
      (by with_unfolding_all rfl)
    rw [show Heap.set (stSt h na).heap (.base ⟨(stSt h na).nextAddr⟩)
        ⟨some Ty.bool, .bool false⟩ = h ++ [(.base ⟨na⟩, bcc false)] from
      set_fresh (hfr na (by omega))] at hstep
    exact stepFnIter_one hstep
  have s3 := stepFnIter_one (stepFn_seq_pop
    (σ := stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
    (t := ffTrue) (rest := [.while (.boolLit true) body2])
    (env := envLp na) (k := K2after) (ch := ch))
  have s4 : stepFnIter 2 (stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (.exec ffTrue (envLp na)
        (.seq [.while (.boolLit true) body2] (envLp na) K2after)) ch
      = .ok (.retV (.addr (.base ⟨na⟩))
            (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit true] []
              (.seqn #[]) (envLp na)
              (.seq [.while (.boolLit true) body2] (envLp na) K2after)),
          stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have s5 : stepFnIter 1 (stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (.retV (.addr (.base ⟨na⟩))
        (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit true] []
          (.seqn #[]) (envLp na)
          (.seq [.while (.boolLit true) body2] (envLp na) K2after))) ch
      = .ok (.evalE (.boolLit true) (envLp na)
            (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
              (.seqn #[]) (envLp na)
              (.seq [.while (.boolLit true) body2] (envLp na) K2after)),
          stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have s6 : stepFnIter 2 (stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (.evalE (.boolLit true) (envLp na)
        (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
          (.seqn #[]) (envLp na)
          (.seq [.while (.boolLit true) body2] (envLp na) K2after))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
            [.bool true] (.seqn #[]) (envLp na)
            (.seq [.while (.boolLit true) body2] (envLp na) K2after)),
          stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have hffcell : Heap.lookup (h ++ [(.base ⟨na⟩, bcc false)])
      (.base ⟨na⟩) = some (bcc false) := by
    rw [lookup_append_right (hfr na (by omega))]
    exact lookup_cons_self
  have s7 : stepFnIter 1 (stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
        [.bool true] (.seqn #[]) (envLp na)
        (.seq [.while (.boolLit true) body2] (envLp na) K2after))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envLp na)
            (.seq [.while (.boolLit true) body2] (envLp na) K2after)),
          stSt (h ++ [(.base ⟨na⟩, bcc true)]) (na + 1), ch) := by
    have hstore := stepFn_store_step
      (σ := stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (σ' := { stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1) with
        heap := Heap.set (h ++ [(.base ⟨na⟩, bcc false)]) (.base ⟨na⟩)
          (bcc true) })
      (r := .chain (.addr (.base ⟨na⟩)) [] []) (val := .bool true)
      (rs := []) (vs := []) (body := .seqn #[]) (env := envLp na)
      (k := .seq [.while (.boolLit true) body2] (envLp na) K2after)
      (ch := ch) (storeTarget_addr hffcell (normBool _ _))
    rw [show Heap.set (h ++ [(.base ⟨na⟩, bcc false)]) (.base ⟨na⟩)
        (bcc true) = h ++ [(.base ⟨na⟩, bcc true)] from by
      rw [set_append_right (hfr na (by omega)), set_singleton_self]]
      at hstore
    exact stepFnIter_one hstore
  have s8 := stepFnIter_one (stepFn_storeK_nil
    (σ := stSt (h ++ [(.base ⟨na⟩, bcc true)]) (na + 1))
    (body := .seqn #[]) (env := envLp na)
    (k := .seq [.while (.boolLit true) body2] (envLp na) K2after)
    (ch := ch))
  have s9 := stepFnIter_one (stepFn_seqn_splice
    (σ := stSt (h ++ [(.base ⟨na⟩, bcc true)]) (na + 1))
    (ss := #[]) (env := envLp na)
    (rest := [.while (.boolLit true) body2]) (k := K2after) (ch := ch))
  have s10 := stepFnIter_one (stepFn_seq_pop
    (σ := stSt (h ++ [(.base ⟨na⟩, bcc true)]) (na + 1))
    (t := .while (.boolLit true) body2) (rest := [])
    (env := envLp na) (k := K2after) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain s1 s2) s3)
        s4) s5) s6) s7) s8) s9) s10

/-- Post-dispatch → the `$c3 := isEven(a)` pair. 3 steps. -/
private theorem l2_toC3 (σ : ExecState) (f : Nat) (ch : Choices) :
    stepFnIter 3 σ (l2Post f) ch
      = .ok (.exec c3Seqn ([] :: envLp f)
            (.seq [exitIf2, iter2Blk] ([] :: envLp f) (loopK2 f)),
          σ, ch) := by
  show stepFnIter (1 + 1 + 1) _ _ _ = _
  have q1 := stepFnIter_one (stepFn_seq_pop (σ := σ)
    (t := condSeqn2) (rest := [exitIf2, iter2Blk]) (env := [] :: envLp f)
    (k := loopKg body2 (envLp f) K2after) (ch := ch))
  have q2 := stepFnIter_one (stepFn_seqn_splice (σ := σ)
    (ss := #[c3Seqn]) (env := [] :: envLp f)
    (rest := [exitIf2, iter2Blk])
    (k := loopKg body2 (envLp f) K2after) (ch := ch))
  have q3 := stepFnIter_one (stepFn_seq_pop (σ := σ)
    (t := c3Seqn) (rest := [exitIf2, iter2Blk]) (env := [] :: envLp f)
    (k := loopKg body2 (envLp f) K2after) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain q1 q2) q3

/-- Exit-if TRUE → the halving block queued. 4 steps. -/
private theorem l2_toIter (σ : ExecState) (f n3 : Nat) (ch : Choices) :
    stepFnIter 4 σ
      (.retV (.bool true)
        (.ifK (.seqn #[]) .breakStmt (envL2c3 f n3)
          (.seq [iter2Blk] (envL2c3 f n3) (loopK2 f)))) ch
      = .ok (.next (.seq [asgHalf "a"] ([] :: envL2c3 f n3)
            (.seq [] (envL2c3 f n3) (loopK2 f))),
          σ, ch) := by
  show stepFnIter (1 + 1 + 1 + 1) _ _ _ = _
  have q1 : stepFnIter 1 σ
      (.retV (.bool true)
        (.ifK (.seqn #[]) .breakStmt (envL2c3 f n3)
          (.seq [iter2Blk] (envL2c3 f n3) (loopK2 f)))) ch
      = .ok (.exec (.seqn #[]) (envL2c3 f n3)
            (.seq [iter2Blk] (envL2c3 f n3) (loopK2 f)), σ, ch) := by
    with_unfolding_all rfl
  have q2 := stepFnIter_one (stepFn_seqn_splice (σ := σ)
    (ss := #[]) (env := envL2c3 f n3) (rest := [iter2Blk])
    (k := loopK2 f) (ch := ch))
  have q3 := stepFnIter_one (stepFn_seq_pop (σ := σ)
    (t := iter2Blk) (rest := []) (env := envL2c3 f n3) (k := loopK2 f)
    (ch := ch))
  have q4 : stepFnIter 1 σ
      (.exec iter2Blk (envL2c3 f n3)
        (.seq [] (envL2c3 f n3) (loopK2 f))) ch
      = .ok (.next (.seq [asgHalf "a"] ([] :: envL2c3 f n3)
            (.seq [] (envL2c3 f n3) (loopK2 f))),
          σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain q1 q2) q3) q4

/-- Iteration tail: scope pops and the retest. 3 steps. -/
private theorem l2_iterTail (σ : ExecState) (f n3 : Nat) (ch : Choices) :
    stepFnIter 3 σ
      (.next (.seq [] ([] :: envL2c3 f n3)
        (.seq [] (envL2c3 f n3) (loopK2 f)))) ch
      = .ok (l2Head f, σ, ch) := by
  with_unfolding_all rfl

/-- Exit-if FALSE → break unwinds past the loop and the block. 5
steps. -/
private theorem l2_break (σ : ExecState) (f n3 : Nat) (ch : Choices) :
    stepFnIter 5 σ
      (.retV (.bool false)
        (.ifK (.seqn #[]) .breakStmt (envL2c3 f n3)
          (.seq [iter2Blk] (envL2c3 f n3) (loopK2 f)))) ch
      = .ok (.next K2after, σ, ch) := by
  with_unfolding_all rfl

/-- **One even loop-2 iteration**: post-dispatch → post-dispatch. 71
steps; cell 4 halved, three cells appended. -/
private theorem l2_iter_even (h : Heap) (f na av : Nat) (ch : Choices)
    (hav64 : av < 2 ^ 64) (hae : av % 2 = 0)
    (h4 : Heap.lookup h (.base ⟨4⟩) = some (u64c (av : Int)))
    (hff : Heap.lookup h (.base ⟨f⟩) = some (bcc false))
    (hfr : FreshFrom h na) :
    ∃ h' : Heap,
      stepFnIter 71 (stSt h na) (l2Post f) ch
        = .ok (l2Post f, stSt h' (na + 3), ch)
      ∧ Heap.lookup h' (.base ⟨4⟩) = some (u64c ((av / 2 : Nat) : Int))
      ∧ Heap.lookup h' (.base ⟨f⟩) = some (bcc false)
      ∧ (∀ (x : Nat) (c : HeapCell), x ≠ 4 →
          Heap.lookup h (.base ⟨x⟩) = some c →
          Heap.lookup h' (.base ⟨x⟩) = some c)
      ∧ FreshFrom h' (na + 3) := by
  have hEa : decide (av % 2 = 0) = true := by simp [hae]
  have h4lt : 4 < na := hfr.lt_of_lookup h4
  have s1 := l2_toC3 (stSt h na) f ch
  have s2 : stepFnIter 36 (stSt h na)
      (.exec c3Seqn ([] :: envLp f)
        (.seq [exitIf2, iter2Blk] ([] :: envLp f) (loopK2 f))) ch
      = .ok (.next (.seq [exitIf2, iter2Blk] (envL2c3 f na) (loopK2 f)),
          stSt (h ++ [(.base ⟨na⟩, bcc true),
                      (.base ⟨na + 1⟩, u64c (av : Int)),
                      (.base ⟨na + 2⟩, bcc true)]) (na + 3), ch) := by
    have hspan := st_ieSeq h na av 4 "$c3" "a" ([] :: envLp f)
      [exitIf2, iter2Blk] (loopK2 f) ch hav64 rfl h4 hfr
    rw [hEa] at hspan
    exact hspan
  have hc3A : Heap.lookup (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      (.base ⟨na⟩) = some (bcc true) := by
    rw [lookup_append_right (hfr na (by omega))]
    exact lookup_cons_self
  have s3 := seg_ifVar (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
    (na + 3) "$c3" (envL2c3 f na) na true (.seqn #[]) .breakStmt
    [iter2Blk] (loopK2 f) ch rfl hc3A
  have s4 := l2_toIter (stSt (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
    (na + 3)) f na ch
  have h4A : Heap.lookup (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      (.base ⟨4⟩) = some (u64c (av : Int)) := lookup_append_left h4
  have s5 := seg_asgHalf (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
    (na + 3) "a" ([] :: envL2c3 f na) 4 av []
    (.seq [] (envL2c3 f na) (loopK2 f)) ch hav64 rfl h4A
  have s6 := l2_iterTail (stSt (Heap.set (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      (.base ⟨4⟩) (u64c ((av / 2 : Nat) : Int))) (na + 3)) f na ch
  have hffH : Heap.lookup (Heap.set (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      (.base ⟨4⟩) (u64c ((av / 2 : Nat) : Int)))
      (.base ⟨f⟩) = some (bcc false) := by
    have hf4 : 4 ≠ f := by
      intro hcon
      rw [← hcon] at hff
      rw [h4] at hff
      cases hff
    rw [lookup_set_other hf4]
    exact lookup_append_left hff
  have s7 := lp_disp_f (Heap.set (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      (.base ⟨4⟩) (u64c ((av / 2 : Nat) : Int)))
    (na + 3) f condSeqn2 exitIf2 iter2Blk (envLp f) K2after ch rfl hffH
  refine ⟨Heap.set (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc true)])
      (.base ⟨4⟩) (u64c ((av / 2 : Nat) : Int)), ?_, ?_, hffH, ?_, ?_⟩
  · show stepFnIter (3 + 36 + 3 + 4 + 13 + 3 + 9) _ _ _ = _
    exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain s1 s2) s3)
        s4) s5) s6) s7
  · exact lookup_set_self
  · intro x c hx4 hc
    rw [lookup_set_other (by omega : 4 ≠ x)]
    exact lookup_append_left hc
  · exact (hfr.push3).set (by omega)

/-- **Loop-2 exit** (`a` odd): post-dispatch → the after-loop point.
47 steps. -/
private theorem l2_exit_odd (h : Heap) (f na av : Nat) (ch : Choices)
    (hav64 : av < 2 ^ 64) (hao : av % 2 = 1)
    (h4 : Heap.lookup h (.base ⟨4⟩) = some (u64c (av : Int)))
    (hfr : FreshFrom h na) :
    ∃ h' : Heap,
      stepFnIter 47 (stSt h na) (l2Post f) ch
        = .ok (.next K2after, stSt h' (na + 3), ch)
      ∧ (∀ (x : Nat) (c : HeapCell),
          Heap.lookup h (.base ⟨x⟩) = some c →
          Heap.lookup h' (.base ⟨x⟩) = some c)
      ∧ FreshFrom h' (na + 3) := by
  have hEa : decide (av % 2 = 0) = false := by simp; omega
  have s1 := l2_toC3 (stSt h na) f ch
  have s2 : stepFnIter 36 (stSt h na)
      (.exec c3Seqn ([] :: envLp f)
        (.seq [exitIf2, iter2Blk] ([] :: envLp f) (loopK2 f))) ch
      = .ok (.next (.seq [exitIf2, iter2Blk] (envL2c3 f na) (loopK2 f)),
          stSt (h ++ [(.base ⟨na⟩, bcc false),
                      (.base ⟨na + 1⟩, u64c (av : Int)),
                      (.base ⟨na + 2⟩, bcc false)]) (na + 3), ch) := by
    have hspan := st_ieSeq h na av 4 "$c3" "a" ([] :: envLp f)
      [exitIf2, iter2Blk] (loopK2 f) ch hav64 rfl h4 hfr
    rw [hEa] at hspan
    exact hspan
  have hc3A : Heap.lookup (h ++ [(.base ⟨na⟩, bcc false),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc false)])
      (.base ⟨na⟩) = some (bcc false) := by
    rw [lookup_append_right (hfr na (by omega))]
    exact lookup_cons_self
  have s3 := seg_ifVar (h ++ [(.base ⟨na⟩, bcc false),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc false)])
    (na + 3) "$c3" (envL2c3 f na) na false (.seqn #[]) .breakStmt
    [iter2Blk] (loopK2 f) ch rfl hc3A
  have s4 := l2_break (stSt (h ++ [(.base ⟨na⟩, bcc false),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc false)])
    (na + 3)) f na ch
  refine ⟨h ++ [(.base ⟨na⟩, bcc false),
      (.base ⟨na + 1⟩, u64c (av : Int)), (.base ⟨na + 2⟩, bcc false)],
    ?_, ?_, ?_⟩
  · show stepFnIter (3 + 36 + 3 + 5) _ _ _ = _
    exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain s1 s2) s3)
      s4
  · intro x c hc
    exact lookup_append_left hc
  · exact hfr.push3

/-- **LOOP 2**, by strong induction on `av`, against `stripTwos`'s
branch equations. -/
private theorem l2_run : ∀ μ av : Nat, av = μ →
    1 ≤ av → av < 2 ^ 64 →
    ∀ (f : Nat) (h : Heap) (na : Nat) (ch : Choices),
    Heap.lookup h (.base ⟨4⟩) = some (u64c (av : Int)) →
    Heap.lookup h (.base ⟨f⟩) = some (bcc false) →
    FreshFrom h na →
    ∃ (k : Nat) (h' : Heap) (na' : Nat), k ≤ 71 * μ + 50 ∧
      stepFnIter k (stSt h na) (l2Post f) ch
        = .ok (.next K2after, stSt h' na', ch)
      ∧ Heap.lookup h' (.base ⟨4⟩)
          = some (u64c ((stripTwos av : Nat) : Int))
      ∧ (∀ (x : Nat) (c : HeapCell), x ≠ 4 →
          Heap.lookup h (.base ⟨x⟩) = some c →
          Heap.lookup h' (.base ⟨x⟩) = some c)
      ∧ FreshFrom h' na' ∧ na ≤ na' := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro av hμ hav hav64 f h na ch h4 hff hfr
    by_cases hae : av % 2 = 0
    · -- even: iterate, then recurse at the half
      have hstrip := stripTwos_even av (by omega) hae
      obtain ⟨H, hrun, H4, Hff, Hpres, Hfr⟩ :=
        l2_iter_even h f na av ch hav64 hae h4 hff hfr
      obtain ⟨k, h', na', hk, hrun', h4', hpres', hfr', hna'⟩ :=
        ih (av / 2) (by omega) (av / 2) rfl (by omega) (by omega)
          f H (na + 3) ch H4 Hff Hfr
      refine ⟨71 + k, h', na', by omega,
        stepFnIter_chain hrun hrun', ?_, ?_, hfr', by omega⟩
      · rw [hstrip]; exact h4'
      · intro x c hx4 hc
        exact hpres' x c hx4 (Hpres x c hx4 hc)
    · -- odd: exit
      have hstrip : stripTwos av = av := stripTwos_odd av (by omega)
      obtain ⟨h', hrun, hpres, hfr'⟩ :=
        l2_exit_odd h f na av ch hav64 (by omega) h4 hfr
      refine ⟨47, h', na + 3, by omega, hrun, ?_, ?_, hfr', by omega⟩
      · rw [hstrip]; exact hpres 4 _ h4
      · exact fun x c _ hc => hpres x c hc

/-! ## Loop 3 (outer subtract loop ↔ `steinSub`; inner strip ↔
`stripTwos`) -/

private def envC3 (f : Nat) : LocalEnv := [] :: [] :: envLp f
/-- The continuation below the inner strip loop: the swap/sub/test
tail, then the outer loop's scopes. -/
private def K3i (f : Nat) : Cont :=
  .seq [swapIf, subSeqn, brkIf] (envC3 f)
    (.seq [] ([] :: envLp f) (loopK3 f))
private def envLp3i (fi f : Nat) : LocalEnv :=
  [("$forFirst", .base ⟨fi⟩)] :: [] :: [] :: envLp f
private def loopK3i (fi f : Nat) : Cont :=
  loopKg body3i (envLp3i fi f) (K3i f)
private def l3iHead (fi f : Nat) : Config :=
  lpHeadg body3i (envLp3i fi f) (K3i f)
private def l3iPost (fi f : Nat) : Config :=
  lpPostg body3i (envLp3i fi f) condSeqn3i exitIf3i iter3iBlk (K3i f)
private def envL3c4 (fi f n4 : Nat) : LocalEnv :=
  [("$c4", .base ⟨n4⟩)] :: envLp3i fi f

/-- Loop-2 exit continuation → the loop-3 (outer) head. 14 steps. -/
private theorem l2_to_l3 (h : Heap) (na : Nat) (ch : Choices)
    (hfr : FreshFrom h na) :
    stepFnIter 14 (stSt h na) (.next K2after) ch
      = .ok (l3Head na, stSt (h ++ [(.base ⟨na⟩, bcc true)]) (na + 1),
          ch) := by
  show stepFnIter (3 + 1 + 1 + 2 + 1 + 2 + 1 + 1 + 1 + 1) _ _ _ = _
  have s1 : stepFnIter 3 (stSt h na) (.next K2after) ch
      = .ok (.exec (.initialization { id := "$forFirst", typ := .bool })
            ([] :: envSh)
            (.seq [ffTrue, .while (.boolLit true) body3] ([] :: envSh)
              K3after),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have s2 : stepFnIter 1 (stSt h na)
      (.exec (.initialization { id := "$forFirst", typ := .bool })
        ([] :: envSh)
        (.seq [ffTrue, .while (.boolLit true) body3] ([] :: envSh)
          K3after)) ch
      = .ok (.next (.seq [ffTrue, .while (.boolLit true) body3]
            (envLp na) K3after),
          stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1), ch) := by
    have hstep := stepFn_init_seq (σ := stSt h na)
      (p := { id := "$forFirst", typ := .bool })
      (rest := [ffTrue, .while (.boolLit true) body3])
      (env := [] :: envSh) (k := K3after) (ch := ch) (v := .bool false)
      (by with_unfolding_all rfl)
    rw [show Heap.set (stSt h na).heap (.base ⟨(stSt h na).nextAddr⟩)
        ⟨some Ty.bool, .bool false⟩ = h ++ [(.base ⟨na⟩, bcc false)] from
      set_fresh (hfr na (by omega))] at hstep
    exact stepFnIter_one hstep
  have s3 := stepFnIter_one (stepFn_seq_pop
    (σ := stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
    (t := ffTrue) (rest := [.while (.boolLit true) body3])
    (env := envLp na) (k := K3after) (ch := ch))
  have s4 : stepFnIter 2 (stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (.exec ffTrue (envLp na)
        (.seq [.while (.boolLit true) body3] (envLp na) K3after)) ch
      = .ok (.retV (.addr (.base ⟨na⟩))
            (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit true] []
              (.seqn #[]) (envLp na)
              (.seq [.while (.boolLit true) body3] (envLp na) K3after)),
          stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have s5 : stepFnIter 1 (stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (.retV (.addr (.base ⟨na⟩))
        (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit true] []
          (.seqn #[]) (envLp na)
          (.seq [.while (.boolLit true) body3] (envLp na) K3after))) ch
      = .ok (.evalE (.boolLit true) (envLp na)
            (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
              (.seqn #[]) (envLp na)
              (.seq [.while (.boolLit true) body3] (envLp na) K3after)),
          stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have s6 : stepFnIter 2 (stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (.evalE (.boolLit true) (envLp na)
        (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
          (.seqn #[]) (envLp na)
          (.seq [.while (.boolLit true) body3] (envLp na) K3after))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
            [.bool true] (.seqn #[]) (envLp na)
            (.seq [.while (.boolLit true) body3] (envLp na) K3after)),
          stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have hffcell : Heap.lookup (h ++ [(.base ⟨na⟩, bcc false)])
      (.base ⟨na⟩) = some (bcc false) := by
    rw [lookup_append_right (hfr na (by omega))]
    exact lookup_cons_self
  have s7 : stepFnIter 1 (stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
        [.bool true] (.seqn #[]) (envLp na)
        (.seq [.while (.boolLit true) body3] (envLp na) K3after))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envLp na)
            (.seq [.while (.boolLit true) body3] (envLp na) K3after)),
          stSt (h ++ [(.base ⟨na⟩, bcc true)]) (na + 1), ch) := by
    have hstore := stepFn_store_step
      (σ := stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (σ' := { stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1) with
        heap := Heap.set (h ++ [(.base ⟨na⟩, bcc false)]) (.base ⟨na⟩)
          (bcc true) })
      (r := .chain (.addr (.base ⟨na⟩)) [] []) (val := .bool true)
      (rs := []) (vs := []) (body := .seqn #[]) (env := envLp na)
      (k := .seq [.while (.boolLit true) body3] (envLp na) K3after)
      (ch := ch) (storeTarget_addr hffcell (normBool _ _))
    rw [show Heap.set (h ++ [(.base ⟨na⟩, bcc false)]) (.base ⟨na⟩)
        (bcc true) = h ++ [(.base ⟨na⟩, bcc true)] from by
      rw [set_append_right (hfr na (by omega)), set_singleton_self]]
      at hstore
    exact stepFnIter_one hstore
  have s8 := stepFnIter_one (stepFn_storeK_nil
    (σ := stSt (h ++ [(.base ⟨na⟩, bcc true)]) (na + 1))
    (body := .seqn #[]) (env := envLp na)
    (k := .seq [.while (.boolLit true) body3] (envLp na) K3after)
    (ch := ch))
  have s9 := stepFnIter_one (stepFn_seqn_splice
    (σ := stSt (h ++ [(.base ⟨na⟩, bcc true)]) (na + 1))
    (ss := #[]) (env := envLp na)
    (rest := [.while (.boolLit true) body3]) (k := K3after) (ch := ch))
  have s10 := stepFnIter_one (stepFn_seq_pop
    (σ := stSt (h ++ [(.base ⟨na⟩, bcc true)]) (na + 1))
    (t := .while (.boolLit true) body3) (rest := [])
    (env := envLp na) (k := K3after) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain s1 s2) s3)
        s4) s5) s6) s7) s8) s9) s10

/-- Outer post-dispatch → the inner block's execution point. 10
steps. -/
private theorem l3_preamble (σ : ExecState) (f : Nat) (ch : Choices) :
    stepFnIter 10 σ (l3Post f) ch
      = .ok (.exec block3i (envC3 f) (K3i f), σ, ch) := by
  show stepFnIter (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ _ _ = _
  have q1 := stepFnIter_one (stepFn_seq_pop (σ := σ)
    (t := .seqn #[]) (rest := [ifTrueStmt, body3Blk])
    (env := [] :: envLp f) (k := loopKg body3 (envLp f) K3after)
    (ch := ch))
  have q2 := stepFnIter_one (stepFn_seqn_splice (σ := σ)
    (ss := #[]) (env := [] :: envLp f) (rest := [ifTrueStmt, body3Blk])
    (k := loopKg body3 (envLp f) K3after) (ch := ch))
  have q3 := stepFnIter_one (stepFn_seq_pop (σ := σ)
    (t := ifTrueStmt) (rest := [body3Blk]) (env := [] :: envLp f)
    (k := loopKg body3 (envLp f) K3after) (ch := ch))
  have q4 : stepFnIter 1 σ
      (.exec ifTrueStmt ([] :: envLp f)
        (.seq [body3Blk] ([] :: envLp f)
          (loopKg body3 (envLp f) K3after))) ch
      = .ok (.evalE (.boolLit true) ([] :: envLp f)
            (.ifK (.seqn #[]) .breakStmt ([] :: envLp f)
              (.seq [body3Blk] ([] :: envLp f)
                (loopKg body3 (envLp f) K3after))), σ, ch) := by
    with_unfolding_all rfl
  have q5 : stepFnIter 1 σ
      (.evalE (.boolLit true) ([] :: envLp f)
        (.ifK (.seqn #[]) .breakStmt ([] :: envLp f)
          (.seq [body3Blk] ([] :: envLp f)
            (loopKg body3 (envLp f) K3after)))) ch
      = .ok (.retV (.bool true)
            (.ifK (.seqn #[]) .breakStmt ([] :: envLp f)
              (.seq [body3Blk] ([] :: envLp f)
                (loopKg body3 (envLp f) K3after))), σ, ch) := by
    with_unfolding_all rfl
  have q6 : stepFnIter 1 σ
      (.retV (.bool true)
        (.ifK (.seqn #[]) .breakStmt ([] :: envLp f)
          (.seq [body3Blk] ([] :: envLp f)
            (loopKg body3 (envLp f) K3after)))) ch
      = .ok (.exec (.seqn #[]) ([] :: envLp f)
            (.seq [body3Blk] ([] :: envLp f)
              (loopKg body3 (envLp f) K3after)), σ, ch) := by
    with_unfolding_all rfl
  have q7 := stepFnIter_one (stepFn_seqn_splice (σ := σ)
    (ss := #[]) (env := [] :: envLp f) (rest := [body3Blk])
    (k := loopKg body3 (envLp f) K3after) (ch := ch))
  have q8 := stepFnIter_one (stepFn_seq_pop (σ := σ)
    (t := body3Blk) (rest := []) (env := [] :: envLp f)
    (k := loopKg body3 (envLp f) K3after) (ch := ch))
  have q9 : stepFnIter 1 σ
      (.exec body3Blk ([] :: envLp f)
        (.seq [] ([] :: envLp f) (loopKg body3 (envLp f) K3after))) ch
      = .ok (.next (.seq [block3i, swapIf, subSeqn, brkIf] (envC3 f)
            (.seq [] ([] :: envLp f) (loopKg body3 (envLp f) K3after))),
          σ, ch) := by
    with_unfolding_all rfl
  have q10 := stepFnIter_one (stepFn_seq_pop (σ := σ)
    (t := block3i) (rest := [swapIf, subSeqn, brkIf]) (env := envC3 f)
    (k := .seq [] ([] :: envLp f) (loopKg body3 (envLp f) K3after))
    (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain q1 q2) q3)
        q4) q5) q6) q7) q8) q9) q10

/-- The inner block's entry: fresh `$forFirst` allocated and raised,
the inner head reached. 13 steps. -/
private theorem l3i_entry (h : Heap) (f na : Nat) (ch : Choices)
    (hfr : FreshFrom h na) :
    stepFnIter 13 (stSt h na) (.exec block3i (envC3 f) (K3i f)) ch
      = .ok (l3iHead na f, stSt (h ++ [(.base ⟨na⟩, bcc true)]) (na + 1),
          ch) := by
  show stepFnIter (1 + 1 + 1 + 1 + 2 + 1 + 2 + 1 + 1 + 1 + 1) _ _ _ = _
  have s0 : stepFnIter 1 (stSt h na)
      (.exec block3i (envC3 f) (K3i f)) ch
      = .ok (.next (.seq [ffInit, ffTrue, .while (.boolLit true) body3i]
            ([] :: envC3 f) (K3i f)),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have s1 := stepFnIter_one (stepFn_seq_pop (σ := stSt h na)
    (t := ffInit) (rest := [ffTrue, .while (.boolLit true) body3i])
    (env := [] :: envC3 f) (k := K3i f) (ch := ch))
  have s2 : stepFnIter 1 (stSt h na)
      (.exec ffInit ([] :: envC3 f)
        (.seq [ffTrue, .while (.boolLit true) body3i] ([] :: envC3 f)
          (K3i f))) ch
      = .ok (.next (.seq [ffTrue, .while (.boolLit true) body3i]
            (envLp3i na f) (K3i f)),
          stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1), ch) := by
    have hstep := stepFn_init_seq (σ := stSt h na)
      (p := { id := "$forFirst", typ := .bool })
      (rest := [ffTrue, .while (.boolLit true) body3i])
      (env := [] :: envC3 f) (k := K3i f) (ch := ch) (v := .bool false)
      (by with_unfolding_all rfl)
    rw [show Heap.set (stSt h na).heap (.base ⟨(stSt h na).nextAddr⟩)
        ⟨some Ty.bool, .bool false⟩ = h ++ [(.base ⟨na⟩, bcc false)] from
      set_fresh (hfr na (by omega))] at hstep
    exact stepFnIter_one hstep
  have s3 := stepFnIter_one (stepFn_seq_pop
    (σ := stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
    (t := ffTrue) (rest := [.while (.boolLit true) body3i])
    (env := envLp3i na f) (k := K3i f) (ch := ch))
  have s4 : stepFnIter 2 (stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (.exec ffTrue (envLp3i na f)
        (.seq [.while (.boolLit true) body3i] (envLp3i na f) (K3i f))) ch
      = .ok (.retV (.addr (.base ⟨na⟩))
            (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit true] []
              (.seqn #[]) (envLp3i na f)
              (.seq [.while (.boolLit true) body3i] (envLp3i na f)
                (K3i f))),
          stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have s5 : stepFnIter 1 (stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (.retV (.addr (.base ⟨na⟩))
        (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit true] []
          (.seqn #[]) (envLp3i na f)
          (.seq [.while (.boolLit true) body3i] (envLp3i na f)
            (K3i f)))) ch
      = .ok (.evalE (.boolLit true) (envLp3i na f)
            (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
              (.seqn #[]) (envLp3i na f)
              (.seq [.while (.boolLit true) body3i] (envLp3i na f)
                (K3i f))),
          stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have s6 : stepFnIter 2 (stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (.evalE (.boolLit true) (envLp3i na f)
        (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
          (.seqn #[]) (envLp3i na f)
          (.seq [.while (.boolLit true) body3i] (envLp3i na f)
            (K3i f)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
            [.bool true] (.seqn #[]) (envLp3i na f)
            (.seq [.while (.boolLit true) body3i] (envLp3i na f)
              (K3i f))),
          stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have hffcell : Heap.lookup (h ++ [(.base ⟨na⟩, bcc false)])
      (.base ⟨na⟩) = some (bcc false) := by
    rw [lookup_append_right (hfr na (by omega))]
    exact lookup_cons_self
  have s7 : stepFnIter 1 (stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
        [.bool true] (.seqn #[]) (envLp3i na f)
        (.seq [.while (.boolLit true) body3i] (envLp3i na f)
          (K3i f)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envLp3i na f)
            (.seq [.while (.boolLit true) body3i] (envLp3i na f)
              (K3i f))),
          stSt (h ++ [(.base ⟨na⟩, bcc true)]) (na + 1), ch) := by
    have hstore := stepFn_store_step
      (σ := stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1))
      (σ' := { stSt (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1) with
        heap := Heap.set (h ++ [(.base ⟨na⟩, bcc false)]) (.base ⟨na⟩)
          (bcc true) })
      (r := .chain (.addr (.base ⟨na⟩)) [] []) (val := .bool true)
      (rs := []) (vs := []) (body := .seqn #[]) (env := envLp3i na f)
      (k := .seq [.while (.boolLit true) body3i] (envLp3i na f) (K3i f))
      (ch := ch) (storeTarget_addr hffcell (normBool _ _))
    rw [show Heap.set (h ++ [(.base ⟨na⟩, bcc false)]) (.base ⟨na⟩)
        (bcc true) = h ++ [(.base ⟨na⟩, bcc true)] from by
      rw [set_append_right (hfr na (by omega)), set_singleton_self]]
      at hstore
    exact stepFnIter_one hstore
  have s8 := stepFnIter_one (stepFn_storeK_nil
    (σ := stSt (h ++ [(.base ⟨na⟩, bcc true)]) (na + 1))
    (body := .seqn #[]) (env := envLp3i na f)
    (k := .seq [.while (.boolLit true) body3i] (envLp3i na f) (K3i f))
    (ch := ch))
  have s9 := stepFnIter_one (stepFn_seqn_splice
    (σ := stSt (h ++ [(.base ⟨na⟩, bcc true)]) (na + 1))
    (ss := #[]) (env := envLp3i na f)
    (rest := [.while (.boolLit true) body3i]) (k := K3i f) (ch := ch))
  have s10 := stepFnIter_one (stepFn_seq_pop
    (σ := stSt (h ++ [(.base ⟨na⟩, bcc true)]) (na + 1))
    (t := .while (.boolLit true) body3i) (rest := [])
    (env := envLp3i na f) (k := K3i f) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain s0 s1) s2) s3) s4) s5) s6) s7) s8) s9) s10

/-- Inner post-dispatch → the `$c4 := isEven(b)` pair. 3 steps. -/
private theorem l3i_toC4 (σ : ExecState) (fi f : Nat) (ch : Choices) :
    stepFnIter 3 σ (l3iPost fi f) ch
      = .ok (.exec c4Seqn ([] :: envLp3i fi f)
            (.seq [exitIf3i, iter3iBlk] ([] :: envLp3i fi f)
              (loopK3i fi f)),
          σ, ch) := by
  show stepFnIter (1 + 1 + 1) _ _ _ = _
  have q1 := stepFnIter_one (stepFn_seq_pop (σ := σ)
    (t := condSeqn3i) (rest := [exitIf3i, iter3iBlk])
    (env := [] :: envLp3i fi f) (k := loopK3i fi f) (ch := ch))
  have q2 := stepFnIter_one (stepFn_seqn_splice (σ := σ)
    (ss := #[c4Seqn]) (env := [] :: envLp3i fi f)
    (rest := [exitIf3i, iter3iBlk]) (k := loopK3i fi f) (ch := ch))
  have q3 := stepFnIter_one (stepFn_seq_pop (σ := σ)
    (t := c4Seqn) (rest := [exitIf3i, iter3iBlk])
    (env := [] :: envLp3i fi f) (k := loopK3i fi f) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain q1 q2) q3

/-- Inner exit-if TRUE → the halving block queued. 4 steps. -/
private theorem l3i_toIter (σ : ExecState) (fi f n4 : Nat) (ch : Choices) :
    stepFnIter 4 σ
      (.retV (.bool true)
        (.ifK (.seqn #[]) .breakStmt (envL3c4 fi f n4)
          (.seq [iter3iBlk] (envL3c4 fi f n4) (loopK3i fi f)))) ch
      = .ok (.next (.seq [asgHalf "b"] ([] :: envL3c4 fi f n4)
            (.seq [] (envL3c4 fi f n4) (loopK3i fi f))),
          σ, ch) := by
  show stepFnIter (1 + 1 + 1 + 1) _ _ _ = _
  have q1 : stepFnIter 1 σ
      (.retV (.bool true)
        (.ifK (.seqn #[]) .breakStmt (envL3c4 fi f n4)
          (.seq [iter3iBlk] (envL3c4 fi f n4) (loopK3i fi f)))) ch
      = .ok (.exec (.seqn #[]) (envL3c4 fi f n4)
            (.seq [iter3iBlk] (envL3c4 fi f n4) (loopK3i fi f)),
          σ, ch) := by
    with_unfolding_all rfl
  have q2 := stepFnIter_one (stepFn_seqn_splice (σ := σ)
    (ss := #[]) (env := envL3c4 fi f n4) (rest := [iter3iBlk])
    (k := loopK3i fi f) (ch := ch))
  have q3 := stepFnIter_one (stepFn_seq_pop (σ := σ)
    (t := iter3iBlk) (rest := []) (env := envL3c4 fi f n4)
    (k := loopK3i fi f) (ch := ch))
  have q4 : stepFnIter 1 σ
      (.exec iter3iBlk (envL3c4 fi f n4)
        (.seq [] (envL3c4 fi f n4) (loopK3i fi f))) ch
      = .ok (.next (.seq [asgHalf "b"] ([] :: envL3c4 fi f n4)
            (.seq [] (envL3c4 fi f n4) (loopK3i fi f))),
          σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain q1 q2) q3) q4

/-- Inner iteration tail. 3 steps. -/
private theorem l3i_iterTail (σ : ExecState) (fi f n4 : Nat)
    (ch : Choices) :
    stepFnIter 3 σ
      (.next (.seq [] ([] :: envL3c4 fi f n4)
        (.seq [] (envL3c4 fi f n4) (loopK3i fi f)))) ch
      = .ok (l3iHead fi f, σ, ch) := by
  with_unfolding_all rfl

/-- Inner exit-if FALSE → break unwinds to the swap/sub tail. 5
steps. -/
private theorem l3i_break (σ : ExecState) (fi f n4 : Nat) (ch : Choices) :
    stepFnIter 5 σ
      (.retV (.bool false)
        (.ifK (.seqn #[]) .breakStmt (envL3c4 fi f n4)
          (.seq [iter3iBlk] (envL3c4 fi f n4) (loopK3i fi f)))) ch
      = .ok (.next (K3i f), σ, ch) := by
  with_unfolding_all rfl

/-- **One even inner-strip iteration**. 71 steps; cell 5 halved. -/
private theorem l3i_iter_even (h : Heap) (fi f na bv : Nat) (ch : Choices)
    (hbv64 : bv < 2 ^ 64) (hbe : bv % 2 = 0)
    (h5 : Heap.lookup h (.base ⟨5⟩) = some (u64c (bv : Int)))
    (hff : Heap.lookup h (.base ⟨fi⟩) = some (bcc false))
    (hfr : FreshFrom h na) :
    ∃ h' : Heap,
      stepFnIter 71 (stSt h na) (l3iPost fi f) ch
        = .ok (l3iPost fi f, stSt h' (na + 3), ch)
      ∧ Heap.lookup h' (.base ⟨5⟩) = some (u64c ((bv / 2 : Nat) : Int))
      ∧ Heap.lookup h' (.base ⟨fi⟩) = some (bcc false)
      ∧ (∀ (x : Nat) (c : HeapCell), x ≠ 5 →
          Heap.lookup h (.base ⟨x⟩) = some c →
          Heap.lookup h' (.base ⟨x⟩) = some c)
      ∧ FreshFrom h' (na + 3) := by
  have hEb : decide (bv % 2 = 0) = true := by simp [hbe]
  have h5lt : 5 < na := hfr.lt_of_lookup h5
  have s1 := l3i_toC4 (stSt h na) fi f ch
  have s2 : stepFnIter 36 (stSt h na)
      (.exec c4Seqn ([] :: envLp3i fi f)
        (.seq [exitIf3i, iter3iBlk] ([] :: envLp3i fi f)
          (loopK3i fi f))) ch
      = .ok (.next (.seq [exitIf3i, iter3iBlk] (envL3c4 fi f na)
            (loopK3i fi f)),
          stSt (h ++ [(.base ⟨na⟩, bcc true),
                      (.base ⟨na + 1⟩, u64c (bv : Int)),
                      (.base ⟨na + 2⟩, bcc true)]) (na + 3), ch) := by
    have hspan := st_ieSeq h na bv 5 "$c4" "b" ([] :: envLp3i fi f)
      [exitIf3i, iter3iBlk] (loopK3i fi f) ch hbv64 rfl h5 hfr
    rw [hEb] at hspan
    exact hspan
  have hc4A : Heap.lookup (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (bv : Int)), (.base ⟨na + 2⟩, bcc true)])
      (.base ⟨na⟩) = some (bcc true) := by
    rw [lookup_append_right (hfr na (by omega))]
    exact lookup_cons_self
  have s3 := seg_ifVar (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (bv : Int)), (.base ⟨na + 2⟩, bcc true)])
    (na + 3) "$c4" (envL3c4 fi f na) na true (.seqn #[]) .breakStmt
    [iter3iBlk] (loopK3i fi f) ch rfl hc4A
  have s4 := l3i_toIter (stSt (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (bv : Int)), (.base ⟨na + 2⟩, bcc true)])
    (na + 3)) fi f na ch
  have h5A : Heap.lookup (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (bv : Int)), (.base ⟨na + 2⟩, bcc true)])
      (.base ⟨5⟩) = some (u64c (bv : Int)) := lookup_append_left h5
  have s5 := seg_asgHalf (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (bv : Int)), (.base ⟨na + 2⟩, bcc true)])
    (na + 3) "b" ([] :: envL3c4 fi f na) 5 bv []
    (.seq [] (envL3c4 fi f na) (loopK3i fi f)) ch hbv64 rfl h5A
  have s6 := l3i_iterTail (stSt (Heap.set (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (bv : Int)), (.base ⟨na + 2⟩, bcc true)])
      (.base ⟨5⟩) (u64c ((bv / 2 : Nat) : Int))) (na + 3)) fi f na ch
  have hffH : Heap.lookup (Heap.set (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (bv : Int)), (.base ⟨na + 2⟩, bcc true)])
      (.base ⟨5⟩) (u64c ((bv / 2 : Nat) : Int)))
      (.base ⟨fi⟩) = some (bcc false) := by
    have hf5 : 5 ≠ fi := by
      intro hcon
      rw [← hcon] at hff
      rw [h5] at hff
      cases hff
    rw [lookup_set_other hf5]
    exact lookup_append_left hff
  have s7 := lp_disp_f (Heap.set (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (bv : Int)), (.base ⟨na + 2⟩, bcc true)])
      (.base ⟨5⟩) (u64c ((bv / 2 : Nat) : Int)))
    (na + 3) fi condSeqn3i exitIf3i iter3iBlk (envLp3i fi f) (K3i f) ch
    rfl hffH
  refine ⟨Heap.set (h ++ [(.base ⟨na⟩, bcc true),
      (.base ⟨na + 1⟩, u64c (bv : Int)), (.base ⟨na + 2⟩, bcc true)])
      (.base ⟨5⟩) (u64c ((bv / 2 : Nat) : Int)), ?_, ?_, hffH, ?_, ?_⟩
  · show stepFnIter (3 + 36 + 3 + 4 + 13 + 3 + 9) _ _ _ = _
    exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain s1 s2) s3)
        s4) s5) s6) s7
  · exact lookup_set_self
  · intro x c hx5 hc
    rw [lookup_set_other (by omega : 5 ≠ x)]
    exact lookup_append_left hc
  · exact (hfr.push3).set (by omega)

/-- **Inner-strip exit** (`b` odd). 47 steps. -/
private theorem l3i_exit_odd (h : Heap) (fi f na bv : Nat) (ch : Choices)
    (hbv64 : bv < 2 ^ 64) (hbo : bv % 2 = 1)
    (h5 : Heap.lookup h (.base ⟨5⟩) = some (u64c (bv : Int)))
    (hfr : FreshFrom h na) :
    ∃ h' : Heap,
      stepFnIter 47 (stSt h na) (l3iPost fi f) ch
        = .ok (.next (K3i f), stSt h' (na + 3), ch)
      ∧ (∀ (x : Nat) (c : HeapCell),
          Heap.lookup h (.base ⟨x⟩) = some c →
          Heap.lookup h' (.base ⟨x⟩) = some c)
      ∧ FreshFrom h' (na + 3) := by
  have hEb : decide (bv % 2 = 0) = false := by simp; omega
  have s1 := l3i_toC4 (stSt h na) fi f ch
  have s2 : stepFnIter 36 (stSt h na)
      (.exec c4Seqn ([] :: envLp3i fi f)
        (.seq [exitIf3i, iter3iBlk] ([] :: envLp3i fi f)
          (loopK3i fi f))) ch
      = .ok (.next (.seq [exitIf3i, iter3iBlk] (envL3c4 fi f na)
            (loopK3i fi f)),
          stSt (h ++ [(.base ⟨na⟩, bcc false),
                      (.base ⟨na + 1⟩, u64c (bv : Int)),
                      (.base ⟨na + 2⟩, bcc false)]) (na + 3), ch) := by
    have hspan := st_ieSeq h na bv 5 "$c4" "b" ([] :: envLp3i fi f)
      [exitIf3i, iter3iBlk] (loopK3i fi f) ch hbv64 rfl h5 hfr
    rw [hEb] at hspan
    exact hspan
  have hc4A : Heap.lookup (h ++ [(.base ⟨na⟩, bcc false),
      (.base ⟨na + 1⟩, u64c (bv : Int)), (.base ⟨na + 2⟩, bcc false)])
      (.base ⟨na⟩) = some (bcc false) := by
    rw [lookup_append_right (hfr na (by omega))]
    exact lookup_cons_self
  have s3 := seg_ifVar (h ++ [(.base ⟨na⟩, bcc false),
      (.base ⟨na + 1⟩, u64c (bv : Int)), (.base ⟨na + 2⟩, bcc false)])
    (na + 3) "$c4" (envL3c4 fi f na) na false (.seqn #[]) .breakStmt
    [iter3iBlk] (loopK3i fi f) ch rfl hc4A
  have s4 := l3i_break (stSt (h ++ [(.base ⟨na⟩, bcc false),
      (.base ⟨na + 1⟩, u64c (bv : Int)), (.base ⟨na + 2⟩, bcc false)])
    (na + 3)) fi f na ch
  refine ⟨h ++ [(.base ⟨na⟩, bcc false),
      (.base ⟨na + 1⟩, u64c (bv : Int)), (.base ⟨na + 2⟩, bcc false)],
    ?_, ?_, ?_⟩
  · show stepFnIter (3 + 36 + 3 + 5) _ _ _ = _
    exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain s1 s2) s3)
      s4
  · intro x c hc
    exact lookup_append_left hc
  · exact hfr.push3

/-- **The INNER strip loop**, by strong induction on `bv`; the bound
is in the STRIPPED amount so the outer measure argument stays
affine. -/
private theorem l3i_run : ∀ μ bv : Nat, bv = μ →
    1 ≤ bv → bv < 2 ^ 64 →
    ∀ (fi f : Nat) (h : Heap) (na : Nat) (ch : Choices),
    Heap.lookup h (.base ⟨5⟩) = some (u64c (bv : Int)) →
    Heap.lookup h (.base ⟨fi⟩) = some (bcc false) →
    FreshFrom h na →
    ∃ (k : Nat) (h' : Heap) (na' : Nat),
      k ≤ 71 * (bv - stripTwos bv) + 50 ∧
      stepFnIter k (stSt h na) (l3iPost fi f) ch
        = .ok (.next (K3i f), stSt h' na', ch)
      ∧ Heap.lookup h' (.base ⟨5⟩)
          = some (u64c ((stripTwos bv : Nat) : Int))
      ∧ (∀ (x : Nat) (c : HeapCell), x ≠ 5 →
          Heap.lookup h (.base ⟨x⟩) = some c →
          Heap.lookup h' (.base ⟨x⟩) = some c)
      ∧ FreshFrom h' na' ∧ na ≤ na' := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro bv hμ hbv hbv64 fi f h na ch h5 hff hfr
    by_cases hbe : bv % 2 = 0
    · have hstrip := stripTwos_even bv (by omega) hbe
      have hle2 := stripTwos_le (bv / 2)
      obtain ⟨H, hrun, H5, Hff, Hpres, Hfr⟩ :=
        l3i_iter_even h fi f na bv ch hbv64 hbe h5 hff hfr
      obtain ⟨k, h', na', hk, hrun', h5', hpres', hfr', hna'⟩ :=
        ih (bv / 2) (by omega) (bv / 2) rfl (by omega) (by omega)
          fi f H (na + 3) ch H5 Hff Hfr
      refine ⟨71 + k, h', na', by rw [hstrip]; omega,
        stepFnIter_chain hrun hrun', ?_, ?_, hfr', by omega⟩
      · rw [hstrip]; exact h5'
      · intro x c hx5 hc
        exact hpres' x c hx5 (Hpres x c hx5 hc)
    · have hstrip : stripTwos bv = bv := stripTwos_odd bv (by omega)
      obtain ⟨h', hrun, hpres, hfr'⟩ :=
        l3i_exit_odd h fi f na bv ch hbv64 (by omega) h5 hfr
      refine ⟨47, h', na + 3, by omega, hrun, ?_, ?_, hfr', by omega⟩
      · rw [hstrip]; exact hpres 5 _ h5
      · exact fun x c _ hc => hpres x c hc

/-! ### The outer tail: swap-if, subtract, break test -/

private def K3o (f : Nat) : Cont :=
  .seq [] ([] :: envLp f) (loopK3 f)
private abbrev swapThen : Stmt := .block #[] #[swapSeqn]
private abbrev brkThen : Stmt := .block #[] #[.breakStmt]
private abbrev asgSub : Stmt :=
  .assign (.var "b") (.sub (.var "b") (.var "a"))

/-- The `a > b` delivery. 7 steps; reads cells 4 and 5. -/
private theorem l3_gtDeliver (h : Heap) (f na : Nat) (av bv : Nat)
    (ch : Choices)
    (h4 : Heap.lookup h (.base ⟨4⟩) = some (u64c (av : Int)))
    (h5 : Heap.lookup h (.base ⟨5⟩) = some (u64c (bv : Int))) :
    stepFnIter 7 (stSt h na) (.next (K3i f)) ch
      = .ok (.retV (.bool (decide ((av : Int) > (bv : Int))))
            (.ifK swapThen (.seqn #[]) (envC3 f)
              (.seq [subSeqn, brkIf] (envC3 f) (K3o f))),
          stSt h na, ch) := by
  show stepFnIter (1 + 1 + 1 + 1 + 1 + 1 + 1) _ _ _ = _
  have q1 := stepFnIter_one (stepFn_seq_pop (σ := stSt h na)
    (t := swapIf) (rest := [subSeqn, brkIf]) (env := envC3 f)
    (k := K3o f) (ch := ch))
  have q2 : stepFnIter 1 (stSt h na)
      (.exec swapIf (envC3 f)
        (.seq [subSeqn, brkIf] (envC3 f) (K3o f))) ch
      = .ok (.evalE (.greaterCmp (.var "a") (.var "b")) (envC3 f)
            (.ifK swapThen (.seqn #[]) (envC3 f)
              (.seq [subSeqn, brkIf] (envC3 f) (K3o f))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have q3 : stepFnIter 1 (stSt h na)
      (.evalE (.greaterCmp (.var "a") (.var "b")) (envC3 f)
        (.ifK swapThen (.seqn #[]) (envC3 f)
          (.seq [subSeqn, brkIf] (envC3 f) (K3o f)))) ch
      = .ok (.evalE (.var "a") (envC3 f)
            (.strictK .greaterCmp [] [.var "b"] (envC3 f)
              (.ifK swapThen (.seqn #[]) (envC3 f)
                (.seq [subSeqn, brkIf] (envC3 f) (K3o f)))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have q4 := stepFnIter_one (stepFn_var (σ := stSt h na) (x := "a")
    (env := envC3 f) (a := ⟨4⟩)
    (k := .strictK .greaterCmp [] [.var "b"] (envC3 f)
      (.ifK swapThen (.seqn #[]) (envC3 f)
        (.seq [subSeqn, brkIf] (envC3 f) (K3o f))))
    (ch := ch) (c := u64c (av : Int)) rfl h4)
  have q5 : stepFnIter 1 (stSt h na)
      (.retV (.int (av : Int) .uint64)
        (.strictK .greaterCmp [] [.var "b"] (envC3 f)
          (.ifK swapThen (.seqn #[]) (envC3 f)
            (.seq [subSeqn, brkIf] (envC3 f) (K3o f))))) ch
      = .ok (.evalE (.var "b") (envC3 f)
            (.strictK .greaterCmp [.int (av : Int) .uint64] [] (envC3 f)
              (.ifK swapThen (.seqn #[]) (envC3 f)
                (.seq [subSeqn, brkIf] (envC3 f) (K3o f)))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have q6 := stepFnIter_one (stepFn_var (σ := stSt h na) (x := "b")
    (env := envC3 f) (a := ⟨5⟩)
    (k := .strictK .greaterCmp [.int (av : Int) .uint64] [] (envC3 f)
      (.ifK swapThen (.seqn #[]) (envC3 f)
        (.seq [subSeqn, brkIf] (envC3 f) (K3o f))))
    (ch := ch) (c := u64c (bv : Int)) rfl h5)
  have q7 : stepFnIter 1 (stSt h na)
      (.retV (.int (bv : Int) .uint64)
        (.strictK .greaterCmp [.int (av : Int) .uint64] [] (envC3 f)
          (.ifK swapThen (.seqn #[]) (envC3 f)
            (.seq [subSeqn, brkIf] (envC3 f) (K3o f))))) ch
      = .ok (.retV (.bool (decide ((av : Int) > (bv : Int))))
            (.ifK swapThen (.seqn #[]) (envC3 f)
              (.seq [subSeqn, brkIf] (envC3 f) (K3o f))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain q1 q2) q3) q4)
      q5) q6) q7

/-- Swap taken (`a > b`): `a, b = b, a`. 19 steps; writes cells 4, 5. -/
private theorem l3_swapT (h : Heap) (f na : Nat) (av bv : Nat)
    (ch : Choices) (hav64 : av < 2 ^ 64) (hbv64 : bv < 2 ^ 64)
    (h4 : Heap.lookup h (.base ⟨4⟩) = some (u64c (av : Int)))
    (h5 : Heap.lookup h (.base ⟨5⟩) = some (u64c (bv : Int))) :
    stepFnIter 19 (stSt h na)
      (.retV (.bool true)
        (.ifK swapThen (.seqn #[]) (envC3 f)
          (.seq [subSeqn, brkIf] (envC3 f) (K3o f)))) ch
      = .ok (.next (.seq [subSeqn, brkIf] (envC3 f) (K3o f)),
          stSt ((h.set (.base ⟨4⟩) (u64c (bv : Int))).set (.base ⟨5⟩)
            (u64c (av : Int))) na, ch) := by
  show stepFnIter (1 + 1 + 1 + 1 + 1 + 5 + 1 + 1 + 1 + 1 + 1 + 1 + 1
    + 1 + 1) _ _ _ = _
  have q1 : stepFnIter 1 (stSt h na)
      (.retV (.bool true)
        (.ifK swapThen (.seqn #[]) (envC3 f)
          (.seq [subSeqn, brkIf] (envC3 f) (K3o f)))) ch
      = .ok (.exec swapThen (envC3 f)
            (.seq [subSeqn, brkIf] (envC3 f) (K3o f)),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have q2 : stepFnIter 1 (stSt h na)
      (.exec swapThen (envC3 f)
        (.seq [subSeqn, brkIf] (envC3 f) (K3o f))) ch
      = .ok (.next (.seq [swapSeqn] ([] :: envC3 f)
            (.seq [subSeqn, brkIf] (envC3 f) (K3o f))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have q3 := stepFnIter_one (stepFn_seq_pop (σ := stSt h na)
    (t := swapSeqn) (rest := []) (env := [] :: envC3 f)
    (k := .seq [subSeqn, brkIf] (envC3 f) (K3o f)) (ch := ch))
  have q4 := stepFnIter_one (stepFn_seqn_splice (σ := stSt h na)
    (ss := #[.assignMany #[.var "a", .var "b"] #[.var "b", .var "a"]])
    (env := [] :: envC3 f) (rest := [])
    (k := .seq [subSeqn, brkIf] (envC3 f) (K3o f)) (ch := ch))
  have q5 := stepFnIter_one (stepFn_seq_pop (σ := stSt h na)
    (t := .assignMany #[.var "a", .var "b"] #[.var "b", .var "a"])
    (rest := []) (env := [] :: envC3 f)
    (k := .seq [subSeqn, brkIf] (envC3 f) (K3o f)) (ch := ch))
  have q6 : stepFnIter 5 (stSt h na)
      (.exec (.assignMany #[.var "a", .var "b"] #[.var "b", .var "a"])
        ([] :: envC3 f)
        (.seq [] ([] :: envC3 f)
          (.seq [subSeqn, brkIf] (envC3 f) (K3o f)))) ch
      = .ok (.evalE (.var "b") ([] :: envC3 f)
            (.rhsK .vals [.chain (.addr (.base ⟨4⟩)) [] [],
                          .chain (.addr (.base ⟨5⟩)) [] []]
              [] [.var "a"] (.seqn #[]) ([] :: envC3 f)
              (.seq [] ([] :: envC3 f)
                (.seq [subSeqn, brkIf] (envC3 f) (K3o f)))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have q7 := stepFnIter_one (stepFn_var (σ := stSt h na) (x := "b")
    (env := [] :: envC3 f) (a := ⟨5⟩)
    (k := .rhsK .vals [.chain (.addr (.base ⟨4⟩)) [] [],
                       .chain (.addr (.base ⟨5⟩)) [] []]
      [] [.var "a"] (.seqn #[]) ([] :: envC3 f)
      (.seq [] ([] :: envC3 f)
        (.seq [subSeqn, brkIf] (envC3 f) (K3o f))))
    (ch := ch) (c := u64c (bv : Int)) rfl h5)
  have q8 : stepFnIter 1 (stSt h na)
      (.retV (.int (bv : Int) .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨4⟩)) [] [],
                      .chain (.addr (.base ⟨5⟩)) [] []]
          [] [.var "a"] (.seqn #[]) ([] :: envC3 f)
          (.seq [] ([] :: envC3 f)
            (.seq [subSeqn, brkIf] (envC3 f) (K3o f))))) ch
      = .ok (.evalE (.var "a") ([] :: envC3 f)
            (.rhsK .vals [.chain (.addr (.base ⟨4⟩)) [] [],
                          .chain (.addr (.base ⟨5⟩)) [] []]
              [.int (bv : Int) .uint64] [] (.seqn #[]) ([] :: envC3 f)
              (.seq [] ([] :: envC3 f)
                (.seq [subSeqn, brkIf] (envC3 f) (K3o f)))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have q9 := stepFnIter_one (stepFn_var (σ := stSt h na) (x := "a")
    (env := [] :: envC3 f) (a := ⟨4⟩)
    (k := .rhsK .vals [.chain (.addr (.base ⟨4⟩)) [] [],
                       .chain (.addr (.base ⟨5⟩)) [] []]
      [.int (bv : Int) .uint64] [] (.seqn #[]) ([] :: envC3 f)
      (.seq [] ([] :: envC3 f)
        (.seq [subSeqn, brkIf] (envC3 f) (K3o f))))
    (ch := ch) (c := u64c (av : Int)) rfl h4)
  have q10 : stepFnIter 1 (stSt h na)
      (.retV (.int (av : Int) .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨4⟩)) [] [],
                      .chain (.addr (.base ⟨5⟩)) [] []]
          [.int (bv : Int) .uint64] [] (.seqn #[]) ([] :: envC3 f)
          (.seq [] ([] :: envC3 f)
            (.seq [subSeqn, brkIf] (envC3 f) (K3o f))))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨4⟩)) [] [],
                            .chain (.addr (.base ⟨5⟩)) [] []]
            [.int (bv : Int) .uint64, .int (av : Int) .uint64]
            (.seqn #[]) ([] :: envC3 f)
            (.seq [] ([] :: envC3 f)
              (.seq [subSeqn, brkIf] (envC3 f) (K3o f)))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have q11 := stepFnIter_one (stepFn_store_step (σ := stSt h na)
    (σ' := stSt (h.set (.base ⟨4⟩) (u64c (bv : Int))) na)
    (r := .chain (.addr (.base ⟨4⟩)) [] [])
    (val := .int (bv : Int) .uint64)
    (rs := [.chain (.addr (.base ⟨5⟩)) [] []])
    (vs := [.int (av : Int) .uint64])
    (body := .seqn #[]) (env := [] :: envC3 f)
    (k := .seq [] ([] :: envC3 f)
      (.seq [subSeqn, brkIf] (envC3 f) (K3o f)))
    (ch := ch) (storeTarget_addr h4 (normU64 _ hbv64)))
  have h5' : Heap.lookup (h.set (.base ⟨4⟩) (u64c (bv : Int)))
      (.base ⟨5⟩) = some (u64c (bv : Int)) := by
    rw [lookup_set_other (by omega : 4 ≠ 5)]
    exact h5
  have q12 := stepFnIter_one (stepFn_store_step
    (σ := stSt (h.set (.base ⟨4⟩) (u64c (bv : Int))) na)
    (σ' := stSt ((h.set (.base ⟨4⟩) (u64c (bv : Int))).set (.base ⟨5⟩)
      (u64c (av : Int))) na)
    (r := .chain (.addr (.base ⟨5⟩)) [] [])
    (val := .int (av : Int) .uint64) (rs := []) (vs := [])
    (body := .seqn #[]) (env := [] :: envC3 f)
    (k := .seq [] ([] :: envC3 f)
      (.seq [subSeqn, brkIf] (envC3 f) (K3o f)))
    (ch := ch) (storeTarget_addr h5' (normU64 _ hav64)))
  have q13 := stepFnIter_one (stepFn_storeK_nil
    (σ := stSt ((h.set (.base ⟨4⟩) (u64c (bv : Int))).set (.base ⟨5⟩)
      (u64c (av : Int))) na)
    (body := .seqn #[]) (env := [] :: envC3 f)
    (k := .seq [] ([] :: envC3 f)
      (.seq [subSeqn, brkIf] (envC3 f) (K3o f))) (ch := ch))
  have q14 := stepFnIter_one (stepFn_seqn_splice
    (σ := stSt ((h.set (.base ⟨4⟩) (u64c (bv : Int))).set (.base ⟨5⟩)
      (u64c (av : Int))) na)
    (ss := #[]) (env := [] :: envC3 f) (rest := [])
    (k := .seq [subSeqn, brkIf] (envC3 f) (K3o f)) (ch := ch))
  have q15 : stepFnIter 1
      (stSt ((h.set (.base ⟨4⟩) (u64c (bv : Int))).set (.base ⟨5⟩)
        (u64c (av : Int))) na)
      (.next (.seq [] ([] :: envC3 f)
        (.seq [subSeqn, brkIf] (envC3 f) (K3o f)))) ch
      = .ok (.next (.seq [subSeqn, brkIf] (envC3 f) (K3o f)),
          stSt ((h.set (.base ⟨4⟩) (u64c (bv : Int))).set (.base ⟨5⟩)
            (u64c (av : Int))) na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain q1 q2) q3) q4) q5) q6)
            q7) q8) q9) q10) q11) q12) q13) q14) q15

/-- Swap skipped (`a ≤ b`). 2 steps. -/
private theorem l3_swapF (σ : ExecState) (f : Nat) (ch : Choices) :
    stepFnIter 2 σ
      (.retV (.bool false)
        (.ifK swapThen (.seqn #[]) (envC3 f)
          (.seq [subSeqn, brkIf] (envC3 f) (K3o f)))) ch
      = .ok (.next (.seq [subSeqn, brkIf] (envC3 f) (K3o f)), σ, ch) := by
  show stepFnIter (1 + 1) _ _ _ = _
  have q1 : stepFnIter 1 σ
      (.retV (.bool false)
        (.ifK swapThen (.seqn #[]) (envC3 f)
          (.seq [subSeqn, brkIf] (envC3 f) (K3o f)))) ch
      = .ok (.exec (.seqn #[]) (envC3 f)
            (.seq [subSeqn, brkIf] (envC3 f) (K3o f)), σ, ch) := by
    with_unfolding_all rfl
  have q2 := stepFnIter_one (stepFn_seqn_splice (σ := σ)
    (ss := #[]) (env := envC3 f) (rest := [subSeqn, brkIf])
    (k := K3o f) (ch := ch))
  exact stepFnIter_chain q1 q2

/-- `b = b - a` (through the wrapping seqn). 15 steps; `lo ≤ hi` so no
wrap. -/
private theorem l3_sub (h : Heap) (f na : Nat) (lo hi : Nat)
    (ch : Choices) (hlohi : lo ≤ hi) (hhi64 : hi < 2 ^ 64)
    (h4 : Heap.lookup h (.base ⟨4⟩) = some (u64c (lo : Int)))
    (h5 : Heap.lookup h (.base ⟨5⟩) = some (u64c (hi : Int))) :
    stepFnIter 15 (stSt h na)
      (.next (.seq [subSeqn, brkIf] (envC3 f) (K3o f))) ch
      = .ok (.next (.seq [brkIf] (envC3 f) (K3o f)),
          stSt (h.set (.base ⟨5⟩) (u64c ((hi - lo : Nat) : Int))) na,
          ch) := by
  show stepFnIter (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1
    + 1 + 1) _ _ _ = _
  have q1 := stepFnIter_one (stepFn_seq_pop (σ := stSt h na)
    (t := subSeqn) (rest := [brkIf]) (env := envC3 f) (k := K3o f)
    (ch := ch))
  have q2 := stepFnIter_one (stepFn_seqn_splice (σ := stSt h na)
    (ss := #[asgSub]) (env := envC3 f) (rest := [brkIf])
    (k := K3o f) (ch := ch))
  have q3 := stepFnIter_one (stepFn_seq_pop (σ := stSt h na)
    (t := asgSub) (rest := [brkIf]) (env := envC3 f) (k := K3o f)
    (ch := ch))
  have q4 : stepFnIter 1 (stSt h na)
      (.exec asgSub (envC3 f) (.seq [brkIf] (envC3 f) (K3o f))) ch
      = .ok (.evalE (.ref "b") (envC3 f)
            (.tgtOpK (.chain []) [] [] [] []
              .vals [.sub (.var "b") (.var "a")] [] (.seqn #[]) (envC3 f)
              (.seq [brkIf] (envC3 f) (K3o f))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have q5 : stepFnIter 1 (stSt h na)
      (.evalE (.ref "b") (envC3 f)
        (.tgtOpK (.chain []) [] [] [] []
          .vals [.sub (.var "b") (.var "a")] [] (.seqn #[]) (envC3 f)
          (.seq [brkIf] (envC3 f) (K3o f)))) ch
      = .ok (.retV (.addr (.base ⟨5⟩))
            (.tgtOpK (.chain []) [] [] [] []
              .vals [.sub (.var "b") (.var "a")] [] (.seqn #[]) (envC3 f)
              (.seq [brkIf] (envC3 f) (K3o f))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have q6 : stepFnIter 1 (stSt h na)
      (.retV (.addr (.base ⟨5⟩))
        (.tgtOpK (.chain []) [] [] [] []
          .vals [.sub (.var "b") (.var "a")] [] (.seqn #[]) (envC3 f)
          (.seq [brkIf] (envC3 f) (K3o f)))) ch
      = .ok (.evalE (.sub (.var "b") (.var "a")) (envC3 f)
            (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
              (.seqn #[]) (envC3 f)
              (.seq [brkIf] (envC3 f) (K3o f))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have q7 : stepFnIter 1 (stSt h na)
      (.evalE (.sub (.var "b") (.var "a")) (envC3 f)
        (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
          (.seqn #[]) (envC3 f)
          (.seq [brkIf] (envC3 f) (K3o f)))) ch
      = .ok (.evalE (.var "b") (envC3 f)
            (.strictK .sub [] [.var "a"] (envC3 f)
              (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
                (.seqn #[]) (envC3 f)
                (.seq [brkIf] (envC3 f) (K3o f)))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have q8 := stepFnIter_one (stepFn_var (σ := stSt h na) (x := "b")
    (env := envC3 f) (a := ⟨5⟩)
    (k := .strictK .sub [] [.var "a"] (envC3 f)
      (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
        (.seqn #[]) (envC3 f)
        (.seq [brkIf] (envC3 f) (K3o f))))
    (ch := ch) (c := u64c (hi : Int)) rfl h5)
  have q9 : stepFnIter 1 (stSt h na)
      (.retV (.int (hi : Int) .uint64)
        (.strictK .sub [] [.var "a"] (envC3 f)
          (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
            (.seqn #[]) (envC3 f)
            (.seq [brkIf] (envC3 f) (K3o f))))) ch
      = .ok (.evalE (.var "a") (envC3 f)
            (.strictK .sub [.int (hi : Int) .uint64] [] (envC3 f)
              (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
                (.seqn #[]) (envC3 f)
                (.seq [brkIf] (envC3 f) (K3o f)))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have q10 := stepFnIter_one (stepFn_var (σ := stSt h na) (x := "a")
    (env := envC3 f) (a := ⟨4⟩)
    (k := .strictK .sub [.int (hi : Int) .uint64] [] (envC3 f)
      (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
        (.seqn #[]) (envC3 f)
        (.seq [brkIf] (envC3 f) (K3o f))))
    (ch := ch) (c := u64c (lo : Int)) rfl h4)
  have q11 := stepFnIter_one (stepFn_strict_apply (σ := stSt h na)
    (σ' := stSt h na) (op := .sub) (done := [.int (hi : Int) .uint64])
    (v := .int (lo : Int) .uint64)
    (out := .int ((hi - lo : Nat) : Int) .uint64)
    (env := envC3 f)
    (k := .rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
      (.seqn #[]) (envC3 f)
      (.seq [brkIf] (envC3 f) (K3o f)))
    (ch := ch) (applyStrictOp_subNat hlohi hhi64))
  have q12 : stepFnIter 1 (stSt h na)
      (.retV (.int ((hi - lo : Nat) : Int) .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
          (.seqn #[]) (envC3 f)
          (.seq [brkIf] (envC3 f) (K3o f)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨5⟩)) [] []]
            [.int ((hi - lo : Nat) : Int) .uint64] (.seqn #[]) (envC3 f)
            (.seq [brkIf] (envC3 f) (K3o f))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have q13 := stepFnIter_one (stepFn_store_step (σ := stSt h na)
    (σ' := stSt (h.set (.base ⟨5⟩) (u64c ((hi - lo : Nat) : Int))) na)
    (r := .chain (.addr (.base ⟨5⟩)) [] [])
    (val := .int ((hi - lo : Nat) : Int) .uint64)
    (rs := []) (vs := []) (body := .seqn #[]) (env := envC3 f)
    (k := .seq [brkIf] (envC3 f) (K3o f)) (ch := ch)
    (storeTarget_addr h5 (normU64 _ (by omega))))
  have q14 := stepFnIter_one (stepFn_storeK_nil
    (σ := stSt (h.set (.base ⟨5⟩) (u64c ((hi - lo : Nat) : Int))) na)
    (body := .seqn #[]) (env := envC3 f)
    (k := .seq [brkIf] (envC3 f) (K3o f)) (ch := ch))
  have q15 := stepFnIter_one (stepFn_seqn_splice
    (σ := stSt (h.set (.base ⟨5⟩) (u64c ((hi - lo : Nat) : Int))) na)
    (ss := #[]) (env := envC3 f) (rest := [brkIf]) (k := K3o f)
    (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain q1 q2) q3) q4) q5) q6)
            q7) q8) q9) q10) q11) q12) q13) q14) q15

/-- The `b == 0` delivery. 7 steps; reads cell 5. -/
private theorem l3_brkDeliver (h : Heap) (f na : Nat) (bd : Nat)
    (ch : Choices)
    (h5 : Heap.lookup h (.base ⟨5⟩) = some (u64c (bd : Int))) :
    stepFnIter 7 (stSt h na)
      (.next (.seq [brkIf] (envC3 f) (K3o f))) ch
      = .ok (.retV (.bool (((bd : Nat) : Int) == 0))
            (.ifK brkThen (.seqn #[]) (envC3 f)
              (.seq [] (envC3 f) (K3o f))),
          stSt h na, ch) := by
  show stepFnIter (1 + 1 + 1 + 1 + 3) _ _ _ = _
  have q1 := stepFnIter_one (stepFn_seq_pop (σ := stSt h na)
    (t := brkIf) (rest := []) (env := envC3 f) (k := K3o f) (ch := ch))
  have q2 : stepFnIter 1 (stSt h na)
      (.exec brkIf (envC3 f) (.seq [] (envC3 f) (K3o f))) ch
      = .ok (.evalE (.eqCmp tU (.var "b") (.intLit 0 .uint64)) (envC3 f)
            (.ifK brkThen (.seqn #[]) (envC3 f)
              (.seq [] (envC3 f) (K3o f))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have q3 : stepFnIter 1 (stSt h na)
      (.evalE (.eqCmp tU (.var "b") (.intLit 0 .uint64)) (envC3 f)
        (.ifK brkThen (.seqn #[]) (envC3 f)
          (.seq [] (envC3 f) (K3o f)))) ch
      = .ok (.evalE (.var "b") (envC3 f)
            (.strictK (.eqCmp tU) [] [.intLit 0 .uint64] (envC3 f)
              (.ifK brkThen (.seqn #[]) (envC3 f)
                (.seq [] (envC3 f) (K3o f)))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have q4 := stepFnIter_one (stepFn_var (σ := stSt h na) (x := "b")
    (env := envC3 f) (a := ⟨5⟩)
    (k := .strictK (.eqCmp tU) [] [.intLit 0 .uint64] (envC3 f)
      (.ifK brkThen (.seqn #[]) (envC3 f)
        (.seq [] (envC3 f) (K3o f))))
    (ch := ch) (c := u64c (bd : Int)) rfl h5)
  have q5 : stepFnIter 3 (stSt h na)
      (.retV (.int (bd : Int) .uint64)
        (.strictK (.eqCmp tU) [] [.intLit 0 .uint64] (envC3 f)
          (.ifK brkThen (.seqn #[]) (envC3 f)
            (.seq [] (envC3 f) (K3o f))))) ch
      = .ok (.retV (.bool (((bd : Nat) : Int) == 0))
            (.ifK brkThen (.seqn #[]) (envC3 f)
              (.seq [] (envC3 f) (K3o f))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain q1 q2) q3) q4) q5

/-- Test FALSE → drain back to the outer head. 5 steps. -/
private theorem l3_cont (σ : ExecState) (f : Nat) (ch : Choices) :
    stepFnIter 5 σ
      (.retV (.bool false)
        (.ifK brkThen (.seqn #[]) (envC3 f)
          (.seq [] (envC3 f) (K3o f)))) ch
      = .ok (l3Head f, σ, ch) := by
  show stepFnIter (1 + 1 + 3) _ _ _ = _
  have q1 : stepFnIter 1 σ
      (.retV (.bool false)
        (.ifK brkThen (.seqn #[]) (envC3 f)
          (.seq [] (envC3 f) (K3o f)))) ch
      = .ok (.exec (.seqn #[]) (envC3 f) (.seq [] (envC3 f) (K3o f)),
          σ, ch) := by
    with_unfolding_all rfl
  have q2 := stepFnIter_one (stepFn_seqn_splice (σ := σ)
    (ss := #[]) (env := envC3 f) (rest := []) (k := K3o f) (ch := ch))
  have q3 : stepFnIter 3 σ (.next (.seq [] (envC3 f) (K3o f))) ch
      = .ok (l3Head f, σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain q1 q2) q3

/-- Test TRUE → break out of the outer loop. 9 steps. -/
private theorem l3_brkOut (σ : ExecState) (f : Nat) (ch : Choices) :
    stepFnIter 9 σ
      (.retV (.bool true)
        (.ifK brkThen (.seqn #[]) (envC3 f)
          (.seq [] (envC3 f) (K3o f)))) ch
      = .ok (.next K3after, σ, ch) := by
  with_unfolding_all rfl

/-- **One outer-iteration body**, up to the `b == 0` delivery: inner
strip, order, subtract. The machine pair lands on
`(min av sb, max av sb − min av sb)` with `sb := stripTwos bv` —
exactly `steinSub`'s branch data. -/
private theorem l3_body (h : Heap) (f na av bv : Nat) (ch : Choices)
    (hao : av % 2 = 1) (hbv : 1 ≤ bv)
    (hav64 : av < 2 ^ 64) (hbv64 : bv < 2 ^ 64)
    (h4 : Heap.lookup h (.base ⟨4⟩) = some (u64c (av : Int)))
    (h5 : Heap.lookup h (.base ⟨5⟩) = some (u64c (bv : Int)))
    (hff : Heap.lookup h (.base ⟨f⟩) = some (bcc false))
    (hfr : FreshFrom h na) :
    ∃ (k : Nat) (h' : Heap) (na' : Nat),
      k ≤ 71 * (bv - stripTwos bv) + 140 ∧
      stepFnIter k (stSt h na) (l3Post f) ch
        = .ok (.retV (.bool (((max av (stripTwos bv)
              - min av (stripTwos bv) : Nat) : Int) == 0))
            (.ifK brkThen (.seqn #[]) (envC3 f)
              (.seq [] (envC3 f) (K3o f))),
          stSt h' na', ch)
      ∧ Heap.lookup h' (.base ⟨4⟩)
          = some (u64c ((min av (stripTwos bv) : Nat) : Int))
      ∧ Heap.lookup h' (.base ⟨5⟩)
          = some (u64c ((max av (stripTwos bv)
              - min av (stripTwos bv) : Nat) : Int))
      ∧ Heap.lookup h' (.base ⟨f⟩) = some (bcc false)
      ∧ (∀ (x : Nat) (c : HeapCell), x ≠ 4 → x ≠ 5 →
          Heap.lookup h (.base ⟨x⟩) = some c →
          Heap.lookup h' (.base ⟨x⟩) = some c)
      ∧ FreshFrom h' na' ∧ na ≤ na' := by
  have h4lt : 4 < na := hfr.lt_of_lookup h4
  have h5lt : 5 < na := hfr.lt_of_lookup h5
  have hsb1 : 1 ≤ stripTwos bv := by
    have := stripTwos_ne_zero bv (by omega)
    omega
  have hsble : stripTwos bv ≤ bv := stripTwos_le bv
  have hf4 : 4 ≠ f := by
    intro hcon; rw [← hcon] at hff; rw [h4] at hff; cases hff
  have hf5 : 5 ≠ f := by
    intro hcon; rw [← hcon] at hff; rw [h5] at hff; cases hff
  -- preamble + inner entry + inner first dispatch
  have s1 := l3_preamble (stSt h na) f ch
  have s2 := l3i_entry h f na ch hfr
  have hffi : Heap.lookup (h ++ [(.base ⟨na⟩, bcc true)]) (.base ⟨na⟩)
      = some (bcc true) := by
    rw [lookup_append_right (hfr na (by omega))]
    exact lookup_cons_self
  have s3 := lp_disp_t (h ++ [(.base ⟨na⟩, bcc true)]) (na + 1) na
    condSeqn3i exitIf3i iter3iBlk (envLp3i na f) (K3i f) ch rfl hffi
  rw [show Heap.set (h ++ [(.base ⟨na⟩, bcc true)]) (.base ⟨na⟩)
      (bcc false) = h ++ [(.base ⟨na⟩, bcc false)] from by
    rw [set_append_right (hfr na (by omega)), set_singleton_self]] at s3
  -- the inner strip loop
  obtain ⟨ki, h3, na3, hki, hruni, H5i, hpresI, hfrI, hnaI⟩ :=
    l3i_run bv bv rfl (by omega) hbv64 na f
      (h ++ [(.base ⟨na⟩, bcc false)]) (na + 1) ch
      (lookup_append_left h5)
      (by rw [lookup_append_right (hfr na (by omega))]
          exact lookup_cons_self)
      (hfr.push)
  have H4i : Heap.lookup h3 (.base ⟨4⟩) = some (u64c (av : Int)) :=
    hpresI 4 _ (by omega) (lookup_append_left h4)
  have Hffi : Heap.lookup h3 (.base ⟨f⟩) = some (bcc false) :=
    hpresI f _ (by omega) (lookup_append_left hff)
  -- the ordering test
  have s4 := l3_gtDeliver h3 f na3 av (stripTwos bv) ch H4i H5i
  by_cases hlt : stripTwos bv < av
  · -- swap taken: the pair becomes (sb, av)
    have hgtE : (decide ((av : Int) > ((stripTwos bv : Nat) : Int)))
        = true := decide_eq_true (by omega)
    rw [hgtE] at s4
    have s5 := l3_swapT h3 f na3 av (stripTwos bv) ch hav64 (by omega)
      H4i H5i
    have h4s : Heap.lookup ((h3.set (.base ⟨4⟩)
        (u64c ((stripTwos bv : Nat) : Int))).set (.base ⟨5⟩)
        (u64c (av : Int))) (.base ⟨4⟩)
        = some (u64c ((stripTwos bv : Nat) : Int)) := by
      rw [lookup_set_other (by omega : 5 ≠ 4)]
      exact lookup_set_self
    have s6 := l3_sub ((h3.set (.base ⟨4⟩)
        (u64c ((stripTwos bv : Nat) : Int))).set (.base ⟨5⟩)
        (u64c (av : Int))) f na3 (stripTwos bv) av ch (by omega) hav64
      h4s lookup_set_self
    have s7 := l3_brkDeliver (((h3.set (.base ⟨4⟩)
        (u64c ((stripTwos bv : Nat) : Int))).set (.base ⟨5⟩)
        (u64c (av : Int))).set (.base ⟨5⟩)
        (u64c ((av - stripTwos bv : Nat) : Int))) f na3
      (av - stripTwos bv) ch lookup_set_self
    have hmin : min av (stripTwos bv) = stripTwos bv :=
      Nat.min_eq_right (by omega)
    have hmax : max av (stripTwos bv) = av :=
      Nat.max_eq_left (by omega)
    refine ⟨10 + 13 + 16 + ki + 7 + 19 + 15 + 7,
      ((h3.set (.base ⟨4⟩) (u64c ((stripTwos bv : Nat) : Int))).set
        (.base ⟨5⟩) (u64c (av : Int))).set (.base ⟨5⟩)
        (u64c ((av - stripTwos bv : Nat) : Int)),
      na3, by omega, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
    · rw [hmin, hmax]
      exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain s1 s2) s3) hruni) s4) s5) s6) s7
    · rw [hmin]
      rw [lookup_set_other (by omega : 5 ≠ 4),
        lookup_set_other (by omega : 5 ≠ 4)]
      exact lookup_set_self
    · rw [hmin, hmax]
      exact lookup_set_self
    · rw [lookup_set_other (by omega : 5 ≠ f)]
      rw [lookup_set_other (by omega : 5 ≠ f),
        lookup_set_other (by omega : 4 ≠ f)]
      exact Hffi
    · intro x c hx4 hx5 hc
      rw [lookup_set_other (by omega : 5 ≠ x),
        lookup_set_other (by omega : 5 ≠ x),
        lookup_set_other (by omega : 4 ≠ x)]
      exact hpresI x c (by omega) (lookup_append_left hc)
    · exact ((hfrI.set (by omega)).set (by omega)).set (by omega)
  · -- swap skipped: the pair stays (av, sb)
    have hgtE : (decide ((av : Int) > ((stripTwos bv : Nat) : Int)))
        = false := decide_eq_false (by omega)
    rw [hgtE] at s4
    have s5 := l3_swapF (stSt h3 na3) f ch
    have s6 := l3_sub h3 f na3 av (stripTwos bv) ch (by omega)
      (by omega) H4i H5i
    have s7 := l3_brkDeliver (h3.set (.base ⟨5⟩)
        (u64c ((stripTwos bv - av : Nat) : Int))) f na3
      (stripTwos bv - av) ch lookup_set_self
    have hmin : min av (stripTwos bv) = av := Nat.min_eq_left (by omega)
    have hmax : max av (stripTwos bv) = stripTwos bv :=
      Nat.max_eq_right (by omega)
    refine ⟨10 + 13 + 16 + ki + 7 + 2 + 15 + 7,
      h3.set (.base ⟨5⟩) (u64c ((stripTwos bv - av : Nat) : Int)),
      na3, by omega, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
    · rw [hmin, hmax]
      exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain s1 s2) s3) hruni) s4) s5) s6) s7
    · rw [hmin]
      rw [lookup_set_other (by omega : 5 ≠ 4)]
      exact H4i
    · rw [hmin, hmax]
      exact lookup_set_self
    · rw [lookup_set_other (by omega : 5 ≠ f)]
      exact Hffi
    · intro x c hx4 hx5 hc
      rw [lookup_set_other (by omega : 5 ≠ x)]
      exact hpresI x c (by omega) (lookup_append_left hc)
    · exact hfrI.set (by omega)

/-- **LOOP 3 (the subtract loop)**, by strong induction on `av + bv`,
against `steinSub`'s branch equations. -/
private theorem l3_run : ∀ μ av bv : Nat, av + bv = μ →
    av % 2 = 1 → 1 ≤ bv → av < 2 ^ 64 → bv < 2 ^ 64 →
    ∀ (f : Nat) (h : Heap) (na : Nat) (ch : Choices),
    Heap.lookup h (.base ⟨4⟩) = some (u64c (av : Int)) →
    Heap.lookup h (.base ⟨5⟩) = some (u64c (bv : Int)) →
    Heap.lookup h (.base ⟨f⟩) = some (bcc false) →
    FreshFrom h na →
    ∃ (k : Nat) (h' : Heap) (na' : Nat), k ≤ 240 * μ + 240 ∧
      stepFnIter k (stSt h na) (l3Post f) ch
        = .ok (.next K3after, stSt h' na', ch)
      ∧ Heap.lookup h' (.base ⟨4⟩)
          = some (u64c ((steinSub av bv : Nat) : Int))
      ∧ (∀ (x : Nat) (c : HeapCell), x ≠ 4 → x ≠ 5 →
          Heap.lookup h (.base ⟨x⟩) = some c →
          Heap.lookup h' (.base ⟨x⟩) = some c)
      ∧ FreshFrom h' na' ∧ na ≤ na' := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro av bv hμ hao hbv hav64 hbv64 f h na ch h4 h5 hff hfr
    have hsb1 : 1 ≤ stripTwos bv := by
      have := stripTwos_ne_zero bv (by omega)
      omega
    have hsble : stripTwos bv ≤ bv := stripTwos_le bv
    have hsbodd : stripTwos bv % 2 = 1 :=
      stripTwos_odd_result bv (by omega)
    obtain ⟨k₁, h₁, na₁, hk₁, hrun₁, H4, H5, Hff, Hpres, Hfr, hna₁⟩ :=
      l3_body h f na av bv ch hao hbv hav64 hbv64 h4 h5 hff hfr
    have hminpos : ¬(min av (stripTwos bv) = 0) := by omega
    by_cases hz : max av (stripTwos bv) - min av (stripTwos bv) = 0
    · -- equal cores: break out; `steinSub` stops at the min
      rw [hz, beq_cast_zero_zero] at hrun₁
      have s2 := l3_brkOut (stSt h₁ na₁) f ch
      have hstop := steinSub_stop_eq av bv hminpos hz
      refine ⟨k₁ + 9, h₁, na₁, by omega,
        stepFnIter_chain hrun₁ s2, ?_, ?_, Hfr, by omega⟩
      · rw [hstop]; exact H4
      · exact fun x c hx4 hx5 hc => Hpres x c hx4 hx5 hc
    · -- subtract and loop at the strictly smaller measure
      rw [beq_cast_zero_pos (by omega)] at hrun₁
      have s2 := l3_cont (stSt h₁ na₁) f ch
      have s3 := lp_disp_f h₁ na₁ f (.seqn #[]) ifTrueStmt body3Blk
        (envLp f) K3after ch rfl Hff
      have hmono : min av (stripTwos bv)
          + (max av (stripTwos bv) - min av (stripTwos bv)) < μ := by
        omega
      have hstep := steinSub_step av bv hminpos hz
      obtain ⟨k₂, h₂, na₂, hk₂, hrun₂, h4₂, hpres₂, hfr₂, hna₂⟩ :=
        ih (min av (stripTwos bv)
            + (max av (stripTwos bv) - min av (stripTwos bv)))
          hmono (min av (stripTwos bv))
          (max av (stripTwos bv) - min av (stripTwos bv)) rfl
          (by omega) (by omega) (by omega) (by omega)
          f h₁ na₁ ch H4 H5 Hff Hfr
      have hdec : 1 + (bv - stripTwos bv)
          ≤ av + bv - (min av (stripTwos bv)
            + (max av (stripTwos bv) - min av (stripTwos bv))) := by
        omega
      refine ⟨k₁ + 5 + 9 + k₂, h₂, na₂, by omega,
        stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hrun₁ s2)
          s3) hrun₂, ?_, ?_, hfr₂, by omega⟩
      · rw [hstep]; exact h4₂
      · intro x c hx4 hx5 hc
        exact hpres₂ x c hx4 hx5 (Hpres x c hx4 hx5 hc)

/-! ## The epilogue: `$res0 = a << shift`, both frame exits, terminal -/

/-- From the after-loop-3 point to the machine terminal. 39 steps;
delivers `a' << shift` through cells 6 → 3 → 2. -/
private theorem st_epilogue (h : Heap) (na : Nat) (a' sv : Nat)
    (o6 o3 o2 : Int) (ch : Choices)
    (hg : a' * 2 ^ sv < 2 ^ 64)
    (h4 : Heap.lookup h (.base ⟨4⟩) = some (u64c (a' : Int)))
    (h7 : Heap.lookup h (.base ⟨7⟩) = some (u64c (sv : Int)))
    (h6 : Heap.lookup h (.base ⟨6⟩) = some (u64c o6))
    (h3 : Heap.lookup h (.base ⟨3⟩) = some (u64c o3))
    (h2 : Heap.lookup h (.base ⟨2⟩) = some (u64c o2)) :
    stepFnIter 39 (stSt h na) (.next K3after) ch
      = .ok (.next .stop,
          stSt (((h.set (.base ⟨6⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))).set
              (.base ⟨3⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))).set
              (.base ⟨2⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na, ch) := by
  show stepFnIter (2 + 5 + 1 + 1 + 1 + 1 + 1 + 1 + 2 + 3 + 1 + 2 + 1
    + 2 + 2 + 4 + 1 + 1 + 1 + 6) _ _ _ = _
  have e1 : stepFnIter 2 (stSt h na) (.next K3after) ch
      = .ok (.next (.seq [.assign (.var "$res0")
              (.shiftLeft (.var "a") (.var "shift")), .returnStmt]
            envSh KframeTail),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have e2 : stepFnIter 5 (stSt h na)
      (.next (.seq [.assign (.var "$res0")
          (.shiftLeft (.var "a") (.var "shift")), .returnStmt]
        envSh KframeTail)) ch
      = .ok (.evalE (.var "a") envSh
            (.strictK .shiftLeft [] [.var "shift"] envSh
              (.rhsK .vals [.chain (.addr (.base ⟨6⟩)) [] []] [] []
                (.seqn #[]) envSh
                (.seq [.returnStmt] envSh KframeTail))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have e3 := stepFnIter_one (stepFn_var (σ := stSt h na) (x := "a")
    (env := envSh) (a := ⟨4⟩)
    (k := .strictK .shiftLeft [] [.var "shift"] envSh
      (.rhsK .vals [.chain (.addr (.base ⟨6⟩)) [] []] [] []
        (.seqn #[]) envSh (.seq [.returnStmt] envSh KframeTail)))
    (ch := ch) (c := u64c (a' : Int)) rfl h4)
  have e4 : stepFnIter 1 (stSt h na)
      (.retV (.int (a' : Int) .uint64)
        (.strictK .shiftLeft [] [.var "shift"] envSh
          (.rhsK .vals [.chain (.addr (.base ⟨6⟩)) [] []] [] []
            (.seqn #[]) envSh (.seq [.returnStmt] envSh KframeTail)))) ch
      = .ok (.evalE (.var "shift") envSh
            (.strictK .shiftLeft [.int (a' : Int) .uint64] [] envSh
              (.rhsK .vals [.chain (.addr (.base ⟨6⟩)) [] []] [] []
                (.seqn #[]) envSh
                (.seq [.returnStmt] envSh KframeTail))),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have e5 := stepFnIter_one (stepFn_var (σ := stSt h na) (x := "shift")
    (env := envSh) (a := ⟨7⟩)
    (k := .strictK .shiftLeft [.int (a' : Int) .uint64] [] envSh
      (.rhsK .vals [.chain (.addr (.base ⟨6⟩)) [] []] [] []
        (.seqn #[]) envSh (.seq [.returnStmt] envSh KframeTail)))
    (ch := ch) (c := u64c (sv : Int)) rfl h7)
  have e6 := stepFnIter_one (stepFn_strict_apply (σ := stSt h na)
    (σ' := stSt h na) (op := .shiftLeft)
    (done := [.int (a' : Int) .uint64]) (v := .int (sv : Int) .uint64)
    (out := .int ((a' * 2 ^ sv : Nat) : Int) .uint64)
    (env := envSh)
    (k := .rhsK .vals [.chain (.addr (.base ⟨6⟩)) [] []] [] []
      (.seqn #[]) envSh (.seq [.returnStmt] envSh KframeTail))
    (ch := ch) (applyStrictOp_shl hg))
  have e7 : stepFnIter 1 (stSt h na)
      (.retV (.int ((a' * 2 ^ sv : Nat) : Int) .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨6⟩)) [] []] [] []
          (.seqn #[]) envSh (.seq [.returnStmt] envSh KframeTail))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨6⟩)) [] []]
            [.int ((a' * 2 ^ sv : Nat) : Int) .uint64] (.seqn #[]) envSh
            (.seq [.returnStmt] envSh KframeTail)),
          stSt h na, ch) := by
    with_unfolding_all rfl
  have e8 := stepFnIter_one (stepFn_store_step (σ := stSt h na)
    (σ' := stSt (h.set (.base ⟨6⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na)
    (r := .chain (.addr (.base ⟨6⟩)) [] [])
    (val := .int ((a' * 2 ^ sv : Nat) : Int) .uint64)
    (rs := []) (vs := []) (body := .seqn #[]) (env := envSh)
    (k := .seq [.returnStmt] envSh KframeTail) (ch := ch)
    (storeTarget_addr h6 (normU64 _ hg)))
  have e9 : stepFnIter 2
      (stSt (h.set (.base ⟨6⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na)
      (.next (.storeK [] [] (.seqn #[]) envSh
        (.seq [.returnStmt] envSh KframeTail))) ch
      = .ok (.next (.seq [.returnStmt] envSh KframeTail),
          stSt (h.set (.base ⟨6⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na,
          ch) := by
    with_unfolding_all rfl
  have e10 : stepFnIter 3
      (stSt (h.set (.base ⟨6⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na)
      (.next (.seq [.returnStmt] envSh KframeTail)) ch
      = .ok (.returning KframeTail,
          stSt (h.set (.base ⟨6⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na,
          ch) := by
    with_unfolding_all rfl
  have e11 : stepFnIter 1
      (stSt (h.set (.base ⟨6⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na)
      (.returning KframeTail) ch
      = .ok (.evalE (.ref "r") envH
            (.tgtOpK (.chain []) [] [] [] [] .vals []
              [.int ((a' * 2 ^ sv : Nat) : Int) .uint64] (.seqn #[]) envH
              (.seq [harnessEpi] envH (.frame [] [] [] [] .stop false))),
          stSt (h.set (.base ⟨6⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na,
          ch) :=
    stepFnIter_one (st_frame_exit_step
      (σ := stSt (h.set (.base ⟨6⟩)
        (u64c ((a' * 2 ^ sv : Nat) : Int))) na)
      (tv := "r") (envC := envH) (rA := 6) (rest := [harnessEpi])
      (K := .frame [] [] [] [] .stop false)
      (c := u64c ((a' * 2 ^ sv : Nat) : Int)) (ch := ch)
      lookup_set_self)
  have e12 : stepFnIter 2
      (stSt (h.set (.base ⟨6⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na)
      (.evalE (.ref "r") envH
        (.tgtOpK (.chain []) [] [] [] [] .vals []
          [.int ((a' * 2 ^ sv : Nat) : Int) .uint64] (.seqn #[]) envH
          (.seq [harnessEpi] envH (.frame [] [] [] [] .stop false)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨3⟩)) [] []]
            [.int ((a' * 2 ^ sv : Nat) : Int) .uint64] (.seqn #[]) envH
            (.seq [harnessEpi] envH (.frame [] [] [] [] .stop false))),
          stSt (h.set (.base ⟨6⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na,
          ch) := by
    with_unfolding_all rfl
  have h3' : Heap.lookup (h.set (.base ⟨6⟩)
      (u64c ((a' * 2 ^ sv : Nat) : Int))) (.base ⟨3⟩)
      = some (u64c o3) := by
    rw [lookup_set_other (by omega : 6 ≠ 3)]
    exact h3
  have e13 := stepFnIter_one (stepFn_store_step
    (σ := stSt (h.set (.base ⟨6⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na)
    (σ' := stSt ((h.set (.base ⟨6⟩)
      (u64c ((a' * 2 ^ sv : Nat) : Int))).set (.base ⟨3⟩)
      (u64c ((a' * 2 ^ sv : Nat) : Int))) na)
    (r := .chain (.addr (.base ⟨3⟩)) [] [])
    (val := .int ((a' * 2 ^ sv : Nat) : Int) .uint64)
    (rs := []) (vs := []) (body := .seqn #[]) (env := envH)
    (k := .seq [harnessEpi] envH (.frame [] [] [] [] .stop false))
    (ch := ch) (storeTarget_addr h3' (normU64 _ hg)))
  have e14 : stepFnIter 2
      (stSt ((h.set (.base ⟨6⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))).set
        (.base ⟨3⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na)
      (.next (.storeK [] [] (.seqn #[]) envH
        (.seq [harnessEpi] envH (.frame [] [] [] [] .stop false)))) ch
      = .ok (.next (.seq [harnessEpi] envH
            (.frame [] [] [] [] .stop false)),
          stSt ((h.set (.base ⟨6⟩)
            (u64c ((a' * 2 ^ sv : Nat) : Int))).set
            (.base ⟨3⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na, ch) := by
    with_unfolding_all rfl
  have e15 : stepFnIter 2
      (stSt ((h.set (.base ⟨6⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))).set
        (.base ⟨3⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na)
      (.next (.seq [harnessEpi] envH
        (.frame [] [] [] [] .stop false))) ch
      = .ok (.next (.seq [.assign (.var "$res0") (.var "r"), .returnStmt]
            envH (.frame [] [] [] [] .stop false)),
          stSt ((h.set (.base ⟨6⟩)
            (u64c ((a' * 2 ^ sv : Nat) : Int))).set
            (.base ⟨3⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na, ch) := by
    with_unfolding_all rfl
  have e16 : stepFnIter 4
      (stSt ((h.set (.base ⟨6⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))).set
        (.base ⟨3⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na)
      (.next (.seq [.assign (.var "$res0") (.var "r"), .returnStmt]
        envH (.frame [] [] [] [] .stop false))) ch
      = .ok (.evalE (.var "r") envH
            (.rhsK .vals [.chain (.addr (.base ⟨2⟩)) [] []] [] []
              (.seqn #[]) envH
              (.seq [.returnStmt] envH (.frame [] [] [] [] .stop false))),
          stSt ((h.set (.base ⟨6⟩)
            (u64c ((a' * 2 ^ sv : Nat) : Int))).set
            (.base ⟨3⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na, ch) := by
    with_unfolding_all rfl
  have e17 := stepFnIter_one (stepFn_var
    (σ := stSt ((h.set (.base ⟨6⟩)
      (u64c ((a' * 2 ^ sv : Nat) : Int))).set
      (.base ⟨3⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na)
    (x := "r") (env := envH) (a := ⟨3⟩)
    (k := .rhsK .vals [.chain (.addr (.base ⟨2⟩)) [] []] [] []
      (.seqn #[]) envH
      (.seq [.returnStmt] envH (.frame [] [] [] [] .stop false)))
    (ch := ch) (c := u64c ((a' * 2 ^ sv : Nat) : Int)) rfl
    lookup_set_self)
  have e18 : stepFnIter 1
      (stSt ((h.set (.base ⟨6⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))).set
        (.base ⟨3⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na)
      (.retV (.int ((a' * 2 ^ sv : Nat) : Int) .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨2⟩)) [] []] [] []
          (.seqn #[]) envH
          (.seq [.returnStmt] envH (.frame [] [] [] [] .stop false)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨2⟩)) [] []]
            [.int ((a' * 2 ^ sv : Nat) : Int) .uint64] (.seqn #[]) envH
            (.seq [.returnStmt] envH (.frame [] [] [] [] .stop false))),
          stSt ((h.set (.base ⟨6⟩)
            (u64c ((a' * 2 ^ sv : Nat) : Int))).set
            (.base ⟨3⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na, ch) := by
    with_unfolding_all rfl
  have h2' : Heap.lookup ((h.set (.base ⟨6⟩)
      (u64c ((a' * 2 ^ sv : Nat) : Int))).set (.base ⟨3⟩)
      (u64c ((a' * 2 ^ sv : Nat) : Int))) (.base ⟨2⟩)
      = some (u64c o2) := by
    rw [lookup_set_other (by omega : 3 ≠ 2),
      lookup_set_other (by omega : 6 ≠ 2)]
    exact h2
  have e19 := stepFnIter_one (stepFn_store_step
    (σ := stSt ((h.set (.base ⟨6⟩)
      (u64c ((a' * 2 ^ sv : Nat) : Int))).set
      (.base ⟨3⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na)
    (σ' := stSt (((h.set (.base ⟨6⟩)
      (u64c ((a' * 2 ^ sv : Nat) : Int))).set
      (.base ⟨3⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))).set
      (.base ⟨2⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na)
    (r := .chain (.addr (.base ⟨2⟩)) [] [])
    (val := .int ((a' * 2 ^ sv : Nat) : Int) .uint64)
    (rs := []) (vs := []) (body := .seqn #[]) (env := envH)
    (k := .seq [.returnStmt] envH (.frame [] [] [] [] .stop false))
    (ch := ch) (storeTarget_addr h2' (normU64 _ hg)))
  have e20 : stepFnIter 6
      (stSt (((h.set (.base ⟨6⟩)
        (u64c ((a' * 2 ^ sv : Nat) : Int))).set
        (.base ⟨3⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))).set
        (.base ⟨2⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na)
      (.next (.storeK [] [] (.seqn #[]) envH
        (.seq [.returnStmt] envH (.frame [] [] [] [] .stop false)))) ch
      = .ok (.next .stop,
          stSt (((h.set (.base ⟨6⟩)
            (u64c ((a' * 2 ^ sv : Nat) : Int))).set
            (.base ⟨3⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))).set
            (.base ⟨2⟩) (u64c ((a' * 2 ^ sv : Nat) : Int))) na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
            (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
              (stepFnIter_chain e1 e2) e3) e4) e5) e6) e7) e8) e9)
                e10) e11) e12) e13) e14) e15) e16) e17) e18) e19) e20

/-! ## The public run theorem -/

/-- Fuel bound for `stein_runs` — an explicit affine form, and a
BOUND, not a measurement. Every iteration of every loop strictly
decreases the machine pair's sum (loop 1 halves both components,
loop 2 halves `a`, loop 3's outer iteration drops `a + b` to
`max a (stripTwos b)`), so total loop work is linear in `a + b`; the
per-lemma bounds composed here are `164·(a+b) + 120` (loop 1),
`71·a + 50` (loop 2), `240·(a+b) + 240` (loop 3, inner strips folded
into the affine measure), plus 173 steps of entry/guard/bridge/
dispatch/epilogue constants. `600 + 480·(a+b)` dominates the sum with
room; the measured (12, 18) run is 896 steps against a bound of
15 000. -/
def steinFuel (a b : Nat) : Nat := 600 + 480 * (a + b)

/-- **The machine run, end to end**: from the machine entry's
post-prelude seed (`derive_entry_eq`'s `stSeed`/`stC0`), the
`stein_harness(a, b)` run reaches the entry terminal within
`steinFuel a b` steps, with `Nat.gcd a b` in the harness result
cell. -/
theorem stein_runs (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (ch : Choices) :
    ∃ (k : Nat) (σf : ExecState), k ≤ steinFuel a b ∧
      stepFnIter k (stSeed (a : Int) (b : Int)) stC0 ch
        = .ok (.next .stop, σf, ch)
      ∧ loadMany σf [.base ⟨2⟩]
          = .ok [.int ((Nat.gcd a b : Nat) : Int) .uint64] := by
  by_cases ha0 : a = 0
  · -- early return A: gcd 0 b = b
    subst ha0
    have hE := st_entry 0 b (by omega) hb ch
    rw [beq_cast_zero_zero] at hE
    have hX := st_exitA ((0 : Nat) : Int) (b : Int) ((0 : Nat) : Int) b
      hb ch
    refine ⟨19 + 38, _, by simp only [steinFuel]; omega,
      stepFnIter_chain hE hX, ?_⟩
    rw [Nat.gcd_zero_left]
    with_unfolding_all rfl
  by_cases hb0 : b = 0
  · -- early return B: gcd a 0 = a
    subst hb0
    have hE := st_entry a 0 ha (by omega) ch
    rw [beq_cast_zero_pos (by omega)] at hE
    have hG := st_g2seg (a : Int) ((0 : Nat) : Int) (a : Int)
      ((0 : Nat) : Int) ch
    rw [beq_cast_zero_zero] at hG
    have hX := st_exitB (a : Int) ((0 : Nat) : Int) ((0 : Nat) : Int) a
      ha ch
    refine ⟨19 + 9 + 38, _, by simp only [steinFuel]; omega,
      stepFnIter_chain (stepFnIter_chain hE hG) hX, ?_⟩
    rw [Nat.gcd_zero_right]
    with_unfolding_all rfl
  -- the main path: a ≥ 1, b ≥ 1
  have hE := st_entry a b ha hb ch
  rw [beq_cast_zero_pos (by omega)] at hE
  have hG := st_g2seg (a : Int) (b : Int) (a : Int) (b : Int) ch
  rw [beq_cast_zero_pos (by omega)] at hG
  have hT := st_toLoop1 (a : Int) (b : Int) (a : Int) (b : Int) ch
  -- loop 1: first dispatch (flag up), then the induction
  have hD1 := lp_disp_t (h9 (a : Int) (b : Int) (a : Int) (b : Int) 0 true)
    9 8 condSeqn1 exitIf1 iter1Blk (envLp 8) K1after ch rfl
    (by with_unfolding_all rfl)
  rw [show Heap.set (h9 (a : Int) (b : Int) (a : Int) (b : Int) 0 true)
      (.base ⟨8⟩) (bcc false)
      = h9 (a : Int) (b : Int) (a : Int) (b : Int) 0 false from by
    with_unfolding_all rfl] at hD1
  have hcle := commonTwos_le_left a b
  obtain ⟨k1, h1, na1, hk1, hrun1, h4₁, h5₁, h7₁, hpres₁, hfr₁, hna₁⟩ :=
    l1_run (a + b) a b 0 rfl (by omega) (by omega) ha hb (by omega)
      (h9 (a : Int) (b : Int) (a : Int) (b : Int) 0 false) 9 ch
      (by with_unfolding_all rfl) (by with_unfolding_all rfl)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl)
      (h9_fresh _ _ _ _ _ _)
  rw [Nat.zero_add] at h7₁
  -- the stripped pair
  have hpowA := commonTwos_pow_le_left a b ha0
  have hpowB := commonTwos_pow_le_right a b hb0
  have ha1pos : 1 ≤ a / 2 ^ commonTwos a b :=
    Nat.div_pos hpowA (Nat.pow_pos (by omega))
  have hb1pos : 1 ≤ b / 2 ^ commonTwos a b :=
    Nat.div_pos hpowB (Nat.pow_pos (by omega))
  have ha1le : a / 2 ^ commonTwos a b ≤ a := Nat.div_le_self _ _
  have hb1le : b / 2 ^ commonTwos a b ≤ b := Nat.div_le_self _ _
  -- into loop 2
  have hB2 := l1_to_l2 h1 na1 ch hfr₁
  have hD2 := lp_disp_t (h1 ++ [(.base ⟨na1⟩, bcc true)]) (na1 + 1) na1
    condSeqn2 exitIf2 iter2Blk (envLp na1) K2after ch rfl
    (by rw [lookup_append_right (hfr₁ na1 (by omega))]
        exact lookup_cons_self)
  rw [show Heap.set (h1 ++ [(.base ⟨na1⟩, bcc true)]) (.base ⟨na1⟩)
      (bcc false) = h1 ++ [(.base ⟨na1⟩, bcc false)] from by
    rw [set_append_right (hfr₁ na1 (by omega)), set_singleton_self]]
    at hD2
  obtain ⟨k2, h2, na2, hk2, hrun2, h4₂, hpres₂, hfr₂, hna₂⟩ :=
    l2_run (a / 2 ^ commonTwos a b) (a / 2 ^ commonTwos a b) rfl
      ha1pos (by omega) na1 (h1 ++ [(.base ⟨na1⟩, bcc false)]) (na1 + 1)
      ch (lookup_append_left h4₁)
      (by rw [lookup_append_right (hfr₁ na1 (by omega))]
          exact lookup_cons_self)
      (hfr₁.push)
  -- into loop 3
  have hstA : 1 ≤ stripTwos (a / 2 ^ commonTwos a b) := by
    have := stripTwos_ne_zero (a / 2 ^ commonTwos a b) (by omega)
    omega
  have hstAle : stripTwos (a / 2 ^ commonTwos a b)
      ≤ a / 2 ^ commonTwos a b := stripTwos_le _
  have hB3 := l2_to_l3 h2 na2 ch hfr₂
  have hD3 := lp_disp_t (h2 ++ [(.base ⟨na2⟩, bcc true)]) (na2 + 1) na2
    (.seqn #[]) ifTrueStmt body3Blk (envLp na2) K3after ch rfl
    (by rw [lookup_append_right (hfr₂ na2 (by omega))]
        exact lookup_cons_self)
  rw [show Heap.set (h2 ++ [(.base ⟨na2⟩, bcc true)]) (.base ⟨na2⟩)
      (bcc false) = h2 ++ [(.base ⟨na2⟩, bcc false)] from by
    rw [set_append_right (hfr₂ na2 (by omega)), set_singleton_self]]
    at hD3
  have h5₂ : Heap.lookup h2 (.base ⟨5⟩)
      = some (u64c ((b / 2 ^ commonTwos a b : Nat) : Int)) :=
    hpres₂ 5 _ (by omega) (lookup_append_left h5₁)
  obtain ⟨k3, h3, na3, hk3, hrun3, h4₃, hpres₃, hfr₃, hna₃⟩ :=
    l3_run (stripTwos (a / 2 ^ commonTwos a b) + b / 2 ^ commonTwos a b)
      (stripTwos (a / 2 ^ commonTwos a b)) (b / 2 ^ commonTwos a b) rfl
      (stripTwos_odd_result _ (by omega)) hb1pos (by omega) (by omega)
      na2 (h2 ++ [(.base ⟨na2⟩, bcc false)]) (na2 + 1) ch
      (lookup_append_left h4₂)
      (lookup_append_left h5₂)
      (by rw [lookup_append_right (hfr₂ na2 (by omega))]
          exact lookup_cons_self)
      (hfr₂.push)
  -- the value story: the reassembled result IS the gcd
  have hspec : steinSpec a b
      = 2 ^ commonTwos a b
        * steinSub (stripTwos (a / 2 ^ commonTwos a b))
            (b / 2 ^ commonTwos a b) := by
    simp only [steinSpec]
    rw [if_neg ha0, if_neg hb0]
  have hgcd : steinSub (stripTwos (a / 2 ^ commonTwos a b))
        (b / 2 ^ commonTwos a b) * 2 ^ commonTwos a b
      = Nat.gcd a b := by
    rw [Nat.mul_comm, ← hspec, steinSpec_eq_gcd]
  have hglt : Nat.gcd a b < 2 ^ 64 := by
    have := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left a b)
    omega
  -- the epilogue's remaining cell facts, threaded through the loops
  have h7₃ : Heap.lookup h3 (.base ⟨7⟩)
      = some (u64c ((commonTwos a b : Nat) : Int)) :=
    hpres₃ 7 _ (by omega) (by omega)
      (lookup_append_left (hpres₂ 7 _ (by omega)
        (lookup_append_left h7₁)))
  have h6₃ : Heap.lookup h3 (.base ⟨6⟩) = some (u64c 0) :=
    hpres₃ 6 _ (by omega) (by omega)
      (lookup_append_left (hpres₂ 6 _ (by omega)
        (lookup_append_left (hpres₁ 6 _ (by omega) (by omega) (by omega)
          (by with_unfolding_all rfl)))))
  have h3₃ : Heap.lookup h3 (.base ⟨3⟩) = some (u64c 0) :=
    hpres₃ 3 _ (by omega) (by omega)
      (lookup_append_left (hpres₂ 3 _ (by omega)
        (lookup_append_left (hpres₁ 3 _ (by omega) (by omega) (by omega)
          (by with_unfolding_all rfl)))))
  have h2₃ : Heap.lookup h3 (.base ⟨2⟩) = some (u64c 0) :=
    hpres₃ 2 _ (by omega) (by omega)
      (lookup_append_left (hpres₂ 2 _ (by omega)
        (lookup_append_left (hpres₁ 2 _ (by omega) (by omega) (by omega)
          (by with_unfolding_all rfl)))))
  have hEpi := st_epilogue h3 na3
    (steinSub (stripTwos (a / 2 ^ commonTwos a b))
      (b / 2 ^ commonTwos a b))
    (commonTwos a b) 0 0 0 ch (by rw [hgcd]; omega)
    h4₃ h7₃ h6₃ h3₃ h2₃
  rw [hgcd] at hEpi
  -- assemble
  refine ⟨19 + 9 + 29 + 16 + k1 + 15 + 16 + k2 + 14 + 16 + k3 + 39,
    stSt (((h3.set (.base ⟨6⟩)
        (u64c ((Nat.gcd a b : Nat) : Int))).set
        (.base ⟨3⟩) (u64c ((Nat.gcd a b : Nat) : Int))).set
        (.base ⟨2⟩) (u64c ((Nat.gcd a b : Nat) : Int))) na3,
    ?_, ?_, ?_⟩
  · show _ ≤ 600 + 480 * (a + b)
    omega
  · exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain hE hG) hT) hD1) hrun1)
            hB2) hD2) hrun2) hB3) hD3) hrun3) hEpi
  · simp only [loadMany, loadLoc, stSt, lookup_set_self, Bind.bind,
      Except.bind, pure, Except.pure]

end GoLean.Examples.Stein
