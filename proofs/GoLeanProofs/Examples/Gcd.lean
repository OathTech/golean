import GoLeanProofs.Examples.GcdProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId

/-!
# Verified example: Euclid's gcd (verified-examples slice 2c, 2026-08-13)

The argument-input scale-out example over the settled memory-quantified
form (design note `docs/2026-08-12_example-spec-form.md` §9): the Go
program is the canonical corpus source
`Corpus/coverage/exec/examples/gcd/main.go` (7/7 differentially green
against `go run`, incl. the int64-boundary pair); `gcdLowered` is its
pinned frontend lowering (`scripts/check-golden`, both links).

The user-facing statements are `gcd_ok` — the framed TOTAL headline:
*for every `a, b` in the full uint64 × uint64 domain, with ANYTHING
else in memory: `gcd(a, b)` completes normally — past one fuel bound,
at every nondeterminism-choice stream — returns exactly `Nat.gcd a b`,
and touches nothing but its result cell* — and `gcd_readout`, its D1
run-conditioned twin.

**The arithmetic treatment, recorded** (fib's "both theorems"
question): fib ships a bounded exact claim AND a full-domain wrapped
claim because `a + b` overflows. gcd's arithmetic CANNOT wrap — the
loop computes `a % b` with `0 ≤ a % b < b < 2^64`, and the result
`Nat.gcd a b ≤ max a b < 2^64` — so the pair COLLAPSES into one
full-domain EXACT claim. Nothing is hidden by the collapse;
machine-integer honesty (FD-E3) here is precisely the observation that
no wrap exists to state.

**Proof-route decision (recorded)**: direct machine-step segments carry
BOTH halves from one strong induction on the `b`-value (reverse's route
lesson) — the induction pins the exact loop-head state, so value and
completion come from the same segments; the fuel-measure doctrine's
≤-decrease shape is realized directly by strong induction (`a % b < b`,
the NON-UNIT decrease the §5c sketch predicted needs no rule variant).
The one data-dependent step inside an iteration is the `%` apply (the
divide-by-zero check branches on the divisor), discharged by the
private executable fact `applyStrictOp_mod_u64` — exactly §5c's
prediction ("the `unorm` family extended to `emod`, nothing
structural"). The Iris WP laws are general machinery, deliberately not
consumed here.

Scope honesty (the charter's two-questions separation): usability
evidence only — never machine-hardening evidence.
-/

namespace GoLean.Examples.Gcd

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-! ## The program-side statement vocabulary -/

/-- The user-iteration block of the desugared loop: `a, b = b, a%b`. -/
abbrev gcdIterBlock : Stmt :=
  .block
    #[]
    #[.seqn
        #[.assignMany
            #[.var "a", .var "b"]
            #[.var "b", .mod (.var "a") (.var "b")]]]

/-- The frontend's `for`-desugar body: the `$forFirst` dispatch (no post
statement — the else branch is empty), the exit test `b != 0` ending in
`break`, the user block. -/
abbrev gcdWhileBody : Stmt :=
  .block
    #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.seqn #[]),
      .seqn #[],
      .ifThenElse (.neqCmp (.int .uint64) (.var "b") (.intLit 0 .uint64))
        (.seqn #[])
        .breakStmt,
      gcdIterBlock]

/-- The subject's `Func` record, verbatim from the pinned lowering (the
`example` pin below ties it by `rfl`). -/
def gcdFunc : Func :=
  { id := { key := "gcd" },
    args := #[{ id := "a", typ := .int .uint64 },
              { id := "b", typ := .int .uint64 }],
    results := #[{ id := "$res0", typ := .int .uint64 }],
    body := .block
      #[]
      #[.block
          #[]
          #[.initialization { id := "$forFirst", typ := .bool },
            .assign (.var "$forFirst") (.boolLit true),
            .while (.boolLit true) gcdWhileBody],
        .seqn
          #[.assign (.var "$res0") (.var "a"),
            .returnStmt]],
    variadic := false,
    wrapper := false }

/-- The lowering pin: the proof subject IS the frontend's lowering. -/
example : findFunctionIn? gcdLowered.funcs ⟨"gcd"⟩ = some gcdFunc := rfl

/-- The harness cell the differential runner also reads. -/
def gcdEnv : LocalEnv := [[("$callres", Loc.base ⟨0⟩)]]

/-- The canonical seeded initial state: the pinned program, one zeroed
uint64 result cell — TIGHT (dom = {0}, na₀ = 1), as the frame theorem's
seed discharge requires. -/
def gcdSeed : ExecState :=
  { types := gcdLowered.typeDefs.toList, functions := gcdLowered.funcs,
    methods := gcdLowered.methods,
    heap := [(.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)],
    nextAddr := 1 }

/-- The framed seed: the result cell plus an arbitrary frame `fr`,
allocator at `na`. -/
def gcdSeedFr (fr : Heap) (na : Nat) : ExecState :=
  { types := gcdLowered.typeDefs.toList, functions := gcdLowered.funcs,
    methods := gcdLowered.methods,
    heap := (.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩) :: fr,
    nextAddr := na }

/-- The driver: `$callres = gcd(a, b)` — both inputs enter as the
call's literal arguments, where the ∀-quantifiers bind. -/
def gcdCall (a b : Nat) : Stmt :=
  .call #[.var "$callres"] ⟨"gcd"⟩
    #[.intLit (a : Int) .uint64, .intLit (b : Int) .uint64]

/-! ## Machine-layer configurations

Transcribed from the machine (probe-verified against a concrete run;
every raw segment below re-checks the transcription by `rfl`). Address
layout: 0 = `$callres`, 1 = `a`, 2 = `b`, 3 = `$res0`,
4 = `$forFirst`; allocator parked at 5 for the whole loop. -/

private abbrev u64cell (v : Int) : HeapCell :=
  ⟨some (.int .uint64), .int v .uint64⟩
private abbrev bcell (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩

private def envIn : LocalEnv :=
  [[("$forFirst", .base ⟨4⟩)], [],
   [("$res0", .base ⟨3⟩), ("b", .base ⟨2⟩), ("a", .base ⟨1⟩)]]
private def envOut : LocalEnv :=
  [[], [("$res0", .base ⟨3⟩), ("b", .base ⟨2⟩), ("a", .base ⟨1⟩)]]
private def envIn2 : LocalEnv := [] :: [] :: envIn

private def headTail : Cont :=
  .seq [] envIn
    (.seq [.seqn #[.assign (.var "$res0") (.var "a"), .returnStmt]] envOut
      (.frame [(.chain [], [.ref "$callres"])] [[("$callres", .base ⟨0⟩)]]
        [.base ⟨3⟩] [] .stop false))

/-- The loop-head configuration. -/
private def gcdHeadCfg : Config :=
  .exec (.while (.boolLit true) gcdWhileBody) envIn headTail
private def loopK : Cont := .loop (.boolLit true) gcdWhileBody envIn headTail
/-- The exit test's delivery continuation (segment split point). -/
private def gcdCmpCont : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envIn)
    (.seq [gcdIterBlock] ([] :: envIn) loopK)

/-- The rhsK context at the `%` apply point (both targets checked, the
first RHS value `b` banked). -/
private def modTail (bv : Int) : Cont :=
  .rhsK .vals
    [.chain (.addr (.base ⟨1⟩)) [] [], .chain (.addr (.base ⟨2⟩)) [] []]
    [.int bv .uint64] [] (.seqn #[]) envIn2
    (.seq [] envIn2 (.seq [] ([] :: envIn) loopK))

/-- The in-loop state: pair cells `av`/`bv`, the `$forFirst` flag. -/
private def gcdStateP (av bv : Int) (ffv : Bool) : ExecState :=
  { types := gcdLowered.typeDefs.toList, functions := gcdLowered.funcs,
    methods := gcdLowered.methods,
    heap := [(.base ⟨0⟩, u64cell 0), (.base ⟨1⟩, u64cell av),
             (.base ⟨2⟩, u64cell bv), (.base ⟨3⟩, u64cell 0),
             (.base ⟨4⟩, bcell ffv)],
    nextAddr := 5 }

/-- The terminal state: gcd delivered to the harness cell (and still in
`a`/`$res0`; `b` drained to 0, the flag down). -/
private def gcdEndState (g : Int) : ExecState :=
  { types := gcdLowered.typeDefs.toList, functions := gcdLowered.funcs,
    methods := gcdLowered.methods,
    heap := [(.base ⟨0⟩, u64cell g), (.base ⟨1⟩, u64cell g),
             (.base ⟨2⟩, u64cell 0), (.base ⟨3⟩, u64cell g),
             (.base ⟨4⟩, bcell false)],
    nextAddr := 5 }

/-! ## Machine-integer normal forms and the `%` executable fact -/

private theorem unorm_nat_of_lt {x : Nat} (h : x < 2 ^ 64) :
    IntKind.normalize .uint64 (x : Int) = (x : Int) :=
  unorm_of_range (by omega) (by exact_mod_cast h)

/-- The generic single-step glue (reverse's `stepFnIter_one`). -/
private theorem stepFnIter_one {σ : ExecState} {c : Config} {ch : Choices}
    {r : Config × ExecState × Choices}
    (h : stepFn σ c ch = .ok r) : stepFnIter 1 σ c ch = .ok r := by
  obtain ⟨c', σ', ch'⟩ := r
  simp [stepFnIter, h, Bind.bind, Except.bind]

/-- The strict-apply machine step, conditioned on the op fact
(reverse's `stepFn_strict_apply`). -/
private theorem stepFn_strict_apply {σ σ' : ExecState} {op : StrictOp}
    {done : List GoValue} {v out : GoValue} {env : LocalEnv} {k : Cont}
    {ch : Choices}
    (h : applyStrictOp σ op (v :: done).reverse = .ok (out, σ')) :
    stepFn σ (.retV v (.strictK op done [] env k)) ch
      = .ok (.retV out k, σ', ch) := by
  simp only [stepFn]
  rw [h]
  rfl

/-- **The `%` executable fact** (§5c's predicted `emod` extension of
the `unorm` family): uint64 `%` at a positive divisor is Nat `%`,
wrapped nowhere — the divide-by-zero check is the one data-dependent
branch inside a gcd iteration, and this fact discharges it. -/
private theorem applyStrictOp_mod_u64 {σ : ExecState} {a b : Nat}
    (hb : 0 < b) (hb64 : b < 2 ^ 64) :
    applyStrictOp σ .mod [.int (a : Int) .uint64, .int (b : Int) .uint64]
      = .ok (.int ((a % b : Nat) : Int) .uint64, σ) := by
  have hbne : (((b : Nat) : Int) == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, Int.natCast_eq_zero]
    omega
  have htmod : Int.tmod (a : Int) (b : Int) = ((a % b : Nat) : Int) := rfl
  have hnorm : IntKind.normalize .uint64 ((a % b : Nat) : Int)
      = ((a % b : Nat) : Int) :=
    unorm_nat_of_lt (by
      have : a % b < b := Nat.mod_lt _ hb
      omega)
  simp only [applyStrictOp, valueAsInt, hbne, intBinaryResult,
    valueAsIntValue, htmod, IntKind.compatibleResult,
    Bool.false_eq_true, if_false, Bind.bind, Except.bind, pure, Except.pure]
  simp only [show (IntKind.uint64 == IntKind.uint64) = true from rfl,
    if_true, hnorm]

/-! ## Raw run segments (`with_unfolding_all rfl` — pure definitional
evaluation of the interpreter with the pair values symbolic; splits at
the data-dependent points: the exit test's ifK consumption and the `%`
apply). -/

/-- Entry: driver start → the loop head (frame entry, `$forFirst`
block; params land normalized). 20 steps. -/
private theorem gcd_entry_raw (a b : Nat) (ch : Choices) :
    stepFnIter 20 gcdSeed (.exec (gcdCall a b) gcdEnv .stop) ch
      = .ok (gcdHeadCfg,
          gcdStateP
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (a : Int)))
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (b : Int)))
            true, ch) := by
  with_unfolding_all rfl

/-- First-pass dispatch: head with the flag up → the exit-test
delivery. 25 steps; the `b != 0` result rides symbolically. -/
private theorem gcd_segA0_raw (av bv : Int) (ch : Choices) :
    stepFnIter 25 (gcdStateP av bv true) gcdHeadCfg ch
      = .ok (.retV (.bool (!(bv == 0))) gcdCmpCont,
          gcdStateP av bv false, ch) := by
  with_unfolding_all rfl

/-- Later-pass dispatch: head with the flag down → the exit-test
delivery. 18 steps (the dispatch else-branch is empty — no post
statement). -/
private theorem gcd_segA1_raw (av bv : Int) (ch : Choices) :
    stepFnIter 18 (gcdStateP av bv false) gcdHeadCfg ch
      = .ok (.retV (.bool (!(bv == 0))) gcdCmpCont,
          gcdStateP av bv false, ch) := by
  with_unfolding_all rfl

/-- Iteration phase 1: test true → both targets' operands and the
first RHS (`b`), up to the `%` apply point. 18 steps. -/
private theorem gcd_segB1_raw (av bv : Int) (ch : Choices) :
    stepFnIter 18 (gcdStateP av bv false) (.retV (.bool true) gcdCmpCont) ch
      = .ok (.retV (.int bv .uint64)
            (.strictK .mod [.int av .uint64] [] envIn2 (modTail bv)),
          gcdStateP av bv false, ch) := by
  with_unfolding_all rfl

/-- Iteration phase 2: `%` delivered → the two stores
(`a := b, b := a%b`, wrapped at the cells' uint64 type) and the drain
back to the loop head. 8 steps. -/
private theorem gcd_segB2_raw (av bv mv : Int) (ch : Choices) :
    stepFnIter 8 (gcdStateP av bv false) (.retV (.int mv .uint64) (modTail bv))
      ch
      = .ok (gcdHeadCfg,
          gcdStateP (IntKind.normalize .uint64 bv)
            (IntKind.normalize .uint64 mv) false, ch) := by
  with_unfolding_all rfl

/-- Exit: test false → break unwinding, `$res0 = a`, `return`, frame
exit into the harness cell. 26 steps. -/
private theorem gcd_exit_raw (av bv : Int) (ch : Choices) :
    stepFnIter 26 (gcdStateP av bv false) (.retV (.bool false) gcdCmpCont) ch
      = .ok (.next .stop,
          { types := gcdLowered.typeDefs.toList,
            functions := gcdLowered.funcs, methods := gcdLowered.methods,
            heap := [(.base ⟨0⟩,
                u64cell (IntKind.normalize .uint64
                  (IntKind.normalize .uint64 av))),
              (.base ⟨1⟩, u64cell av), (.base ⟨2⟩, u64cell bv),
              (.base ⟨3⟩, u64cell (IntKind.normalize .uint64 av)),
              (.base ⟨4⟩, bcell false)],
            nextAddr := 5 }, ch) := by
  with_unfolding_all rfl

/-! ## The loop induction (value + completion from one strong
induction on the `b`-value — the ≤-decrease measure realized directly;
`a % b < b` is the non-unit decrease) -/

/-- The exit, cleaned: at `b = 0` the run terminates with
`a = Nat.gcd a 0` everywhere it should be. -/
private theorem gcd_exit (a : Nat) (ha : a < 2 ^ 64) (ch : Choices) :
    stepFnIter 26 (gcdStateP (a : Int) ((0 : Nat) : Int) false)
      (.retV (.bool false) gcdCmpCont) ch
      = .ok (.next .stop, gcdEndState (a : Int), ch) := by
  have h := gcd_exit_raw (a : Int) ((0 : Nat) : Int) ch
  rw [unorm_nat_of_lt ha, unorm_nat_of_lt ha] at h
  exact h

/-- **The loop**, by strong induction on the `b`-value: from the
exit-test delivery at pair `(a, b)`, the run reaches the driver
terminal with `Nat.gcd a b` delivered, within `45·b + 26` steps. -/
private theorem gcd_loop :
    ∀ μ : Nat, ∀ a b : Nat, b = μ → a < 2 ^ 64 → b < 2 ^ 64 →
    ∀ ch : Choices, ∃ k : Nat, k ≤ 45 * μ + 26 ∧
      stepFnIter k (gcdStateP (a : Int) (b : Int) false)
        (.retV (.bool (!((b : Int) == 0))) gcdCmpCont) ch
        = .ok (.next .stop, gcdEndState ((Nat.gcd a b : Nat) : Int), ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro a b hbμ ha hb ch
    rcases Nat.eq_zero_or_pos b with hz | hpos
    · -- exit: b = 0, gcd a 0 = a
      subst hz
      rw [show (!(((0 : Nat) : Int) == 0)) = false from by simp]
      refine ⟨26, by omega, ?_⟩
      rw [Nat.gcd_zero_right]
      exact gcd_exit a ha ch
    · -- iterate: (a, b) → (b, a % b)
      have hbne : (((b : Nat) : Int) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq, Int.natCast_eq_zero]
        omega
      rw [show (!(((b : Nat) : Int) == 0)) = true from by
        rw [hbne]; rfl]
      have hmod : a % b < b := Nat.mod_lt _ hpos
      -- phase 1 to the % apply
      have hB1 := gcd_segB1_raw (a : Int) (b : Int) ch
      -- the % apply, conditioned
      have happly : stepFn (gcdStateP (a : Int) (b : Int) false)
          (.retV (.int (b : Int) .uint64)
            (.strictK .mod [.int (a : Int) .uint64] [] envIn2
              (modTail (b : Int)))) ch
          = .ok (.retV (.int ((a % b : Nat) : Int) .uint64)
              (modTail (b : Int)),
            gcdStateP (a : Int) (b : Int) false, ch) :=
        stepFn_strict_apply (done := [.int (a : Int) .uint64])
          (applyStrictOp_mod_u64 hpos hb)
      -- phase 2: stores, cleaned
      have hB2 := gcd_segB2_raw (a : Int) (b : Int) ((a % b : Nat) : Int) ch
      rw [unorm_nat_of_lt hb, unorm_nat_of_lt (by omega : a % b < 2 ^ 64)]
        at hB2
      -- next dispatch
      have hA1 := gcd_segA1_raw (b : Int) ((a % b : Nat) : Int) ch
      -- recurse at the strictly smaller measure
      obtain ⟨k, hk, hrun⟩ := ih (a % b) (by omega) b (a % b) rfl hb
        (by omega) ch
      -- gcd (b, a % b) = gcd (a, b)
      rw [show Nat.gcd b (a % b) = Nat.gcd a b from by
        rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec b a, Nat.gcd_comm b a]]
        at hrun
      refine ⟨18 + 1 + 8 + 18 + k, by omega, ?_⟩
      exact stepFnIter_chain
        (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain hB1 (stepFnIter_one happly))
            hB2)
          hA1)
        hrun

/-- **The canonical run, end to end**: from the canonical seed the
driver completes at the `.normal` terminal within `71 + 45·b` steps,
with `Nat.gcd a b` in the harness cell. -/
private theorem gcd_runs (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (ch : Choices) :
    ∃ k : Nat, k ≤ 71 + 45 * b ∧
      stepFnIter k gcdSeed (.exec (gcdCall a b) gcdEnv .stop) ch
        = .ok (.next .stop, gcdEndState ((Nat.gcd a b : Nat) : Int), ch) := by
  have hE := gcd_entry_raw a b ch
  rw [unorm_nat_of_lt ha, unorm_nat_of_lt ha, unorm_nat_of_lt hb,
    unorm_nat_of_lt hb] at hE
  have hA0 := gcd_segA0_raw (a : Int) (b : Int) ch
  obtain ⟨k, hk, hrun⟩ := gcd_loop b a b rfl ha hb ch
  exact ⟨20 + 25 + k, by omega,
    stepFnIter_chain (stepFnIter_chain hE hA0) hrun⟩

/-- **Total correctness at the canonical seed**: past fuel `71 + 45·b`,
at every choice stream, execution completes normally with `Nat.gcd a b`
in the result cell. -/
private theorem gcd_total_canonical (a b : Nat) (ha : a < 2 ^ 64)
    (hb : b < 2 ^ 64) :
    ∀ fuel : Nat, 71 + 45 * b ≤ fuel → ∀ ch : Choices,
      execStmtLoop fuel gcdSeed (.exec (gcdCall a b) gcdEnv .stop) ch
        = .ok (.normal (gcdEndState ((Nat.gcd a b : Nat) : Int)), ch) := by
  intro fuel hfuel ch
  obtain ⟨k, hk, hrun⟩ := gcd_runs a b ha hb ch
  have hfold := execStmtLoop_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [hfold, execStmtLoop_next_stop]

/-! ## The framed form: the frame theorem consumed at the uniform
shift (the fib pattern verbatim — same one-cell tight canonical seed,
dom = {0}, na₀ = 1) -/

open GoLean.Frame

/-- The seed simulation: gcd's canonical seed beside the framed seed,
through the uniform shift `[1, ∞) ≃ [na, ∞)`. -/
private theorem gcdSeedFrameSim (a b : Nat) (fr : Heap) (na : Nat)
    (hfr : Heap.lookup fr (.base ⟨0⟩) = none)
    (hwf : MachineWf
      { functions := gcdLowered.funcs,
        heap := (.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩) :: fr,
        nextAddr := na }
      (.exec (gcdCall a b) gcdEnv .stop)) :
    FrameSim (uniformShift 1 na) 1 na fr gcdSeed (gcdSeedFr fr na) := by
  have h1na : 1 ≤ na := by
    have hs := hwf.1
    simp only [StateWf, ExecState.locSup, Heap.locSup, Loc.locSup,
      Loc.rootBase, Nat.max_le] at hs
    omega
  have hfrsup : Heap.locSup fr ≤ na := by
    have hs := hwf.1
    simp only [StateWf, ExecState.locSup, Heap.locSup, Nat.max_le] at hs
    omega
  have hren0 : renameLoc (uniformShift 1 na) (.base ⟨0⟩) = .base ⟨0⟩ := by
    simp [renameLoc, uniformShift]
  refine ⟨uniformShift_spec h1na, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- next_eq: na = ρ 1
    simp [gcdSeedFr, gcdSeed, uniformShift]
  · -- alloc_reg
    exact Nat.le_refl 1
  · -- lookup_img
    intro l
    by_cases hl : l = .base ⟨0⟩
    · subst hl
      rw [hren0]
      simp [gcdSeedFr, gcdSeed, Heap.lookup, renameCell, renameValue]
    · have hcanon : Heap.lookup gcdSeed.heap l = none := by
        have hne : ((.base ⟨0⟩ : Loc) == l) = false :=
          beq_false_of_ne (fun h => hl h.symm)
        simp [gcdSeed, Heap.lookup, hne]
      rw [hcanon]
      have hne' : ((.base ⟨0⟩ : Loc) == renameLoc (uniformShift 1 na) l)
          = false := by
        refine beq_false_of_ne (fun hc => ?_)
        cases l with
        | base a' =>
            simp only [renameLoc, Loc.base.injEq, Addr.mk.injEq] at hc
            have : a'.id = 0 := by
              by_cases ha' : a'.id < 1
              · omega
              · exfalso
                simp only [uniformShift, if_neg (by omega)] at hc
                omega
            exact hl (by cases a'; simp_all)
        | field b' tid f => simp [renameLoc] at hc
        | index b' i => simp [renameLoc] at hc
      simp [gcdSeedFr, Heap.lookup, hne']
  · -- frame_pres
    intro l c hl
    have hne : ((.base ⟨0⟩ : Loc) == l) = false := by
      refine beq_false_of_ne (fun hc => ?_)
      rw [← hc, hfr] at hl
      cases hl
    simp [gcdSeedFr, Heap.lookup, hne]
    exact hl
  · -- fr_avoid
    intro a'
    by_cases ha' : a' < 1
    · have : a' = 0 := by omega
      subst this
      simpa [uniformShift] using hfr
    · cases hlk : Heap.lookup fr (.base ⟨uniformShift 1 na a'⟩) with
      | none => rfl
      | some c =>
          exfalso
          have hkey := Heap.lookup_key_locSup hlk
          simp only [Loc.locSup, Loc.rootBase] at hkey
          simp only [uniformShift, if_neg ha'] at hkey
          omega
  · -- bodies_inv
    exact renameBodies_id (fun x hx => uniformShift_low hx)
      (n := 1) (by decide)

/-- The driver configuration is ρ-invariant (literal arguments,
below-`na₀` env). -/
private theorem gcd_cfg_ren (a b na : Nat) :
    renameConfig (uniformShift 1 na) (.exec (gcdCall a b) gcdEnv .stop)
      = .exec (gcdCall a b) gcdEnv .stop := by
  have hstmt : renameStmt (uniformShift 1 na) (gcdCall a b) = gcdCall a b :=
    Frame.renameStmt_id (n := 1) (fun x hx => Frame.uniformShift_low hx)
      _ (by
        simp [gcdCall, Stmt.locSup, assigneeListSup, Assignee.locSup,
          exprListSup, Expr.locSup])
  have henv : renameEnv (uniformShift 1 na) gcdEnv = gcdEnv :=
    Frame.renameEnv_id (n := 1) (fun x hx => Frame.uniformShift_low hx)
      _ (by
        simp [gcdEnv, LocalEnv.locSup, Scope.locSup, Loc.locSup,
          Loc.rootBase])
  simp [renameConfig, renameCont, hstmt, henv]

/-! ## The user-facing statements -/

/-- **The framed total form — proof-side supporting layer per §11 (the
memory-quantified form, kept)**: for every `a, b` in the full
uint64 × uint64 domain, every disjoint frame, and every admissible
allocator bound, execution of `$callres = gcd(a, b)` from the framed
seed completes normally — past one fuel bound, at every
nondeterminism-choice stream — with EXACTLY `Nat.gcd a b` in the
result cell, and every frame cell preserved verbatim. The USER-FACING
headline is `gcd_ok` below (harness ruling 2026-08-13, design note
§11); this memory-quantified form stays as the supporting layer.

No overflow condition appears because none exists: `a % b` and
`Nat.gcd a b` stay below `2^64` on the whole domain (the module
docstring records why fib's bounded/wrapped pair collapses here). -/
theorem gcd_framed (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (fr : Heap) (na : Nat)
    (hfr : Heap.lookup fr (.base ⟨0⟩) = none)
    (hwf : MachineWf
      { functions := gcdLowered.funcs,
        heap := (.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩) :: fr,
        nextAddr := na }
      (.exec (gcdCall a b) gcdEnv .stop)) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel gcdEnv (gcdSeedFr fr na) ch (gcdCall a b)
          = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩)
            = .ok (.int ((Nat.gcd a b : Nat) : Int) .uint64)
        ∧ ∀ (addr : Nat) (c : HeapCell),
            Heap.lookup fr (.base ⟨addr⟩) = some c →
            Heap.lookup σf.heap (.base ⟨addr⟩) = some c := by
  have hSF := gcdSeedFrameSim a b fr na hfr hwf
  refine ⟨71 + 45 * b, fun fuel hfuel ch => ?_⟩
  have hrunC := gcd_total_canonical a b ha hb fuel hfuel ch
  obtain ⟨outF, hrunF, hout⟩ := Frame.execStmtLoop_ren fuel hSF hrunC
  rw [gcd_cfg_ren a b na] at hrunF
  cases outF with
  | normal σF =>
      obtain ⟨hSF', -⟩ := hout
      refine ⟨σF, ch, hrunF, ?_, ?_⟩
      · have hreadC : loadLoc (gcdEndState ((Nat.gcd a b : Nat) : Int))
            (.base ⟨0⟩)
            = .ok (.int ((Nat.gcd a b : Nat) : Int) .uint64) := by
          simp [gcdEndState, loadLoc, Heap.lookup]
        have hload := Frame.loadLoc_sim hSF' (.base ⟨0⟩)
        obtain ⟨vF, hvF, hrel⟩ := hload.ok_inv hreadC
        have hren0 : renameLoc (uniformShift 1 na) (.base ⟨0⟩)
            = .base ⟨0⟩ := by simp [renameLoc, uniformShift]
        rw [hren0] at hvF
        rw [hvF, hrel]
        simp [renameValue]
      · intro addr c hac
        exact hSF'.frame_pres (.base ⟨addr⟩) c hac
  | returned σF => exact hout.elim
  | broke σF => exact hout.elim
  | continued σF => exact hout.elim

/-- **The framed D1 run-conditioned twin — proof-side supporting layer
per §11 (the memory-quantified form, kept)**: any normal completion of
the framed driver, at any fuel and any choice stream, delivers exactly
`Nat.gcd a b` and preserves the frame — derived from `gcd_framed` via
`normal_readout_of_total` (a total claim already determines every
normal completion; nothing is re-proven). -/
theorem gcd_framed_readout (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (fr : Heap) (na : Nat)
    (hfr : Heap.lookup fr (.base ⟨0⟩) = none)
    (hwf : MachineWf
      { functions := gcdLowered.funcs,
        heap := (.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩) :: fr,
        nextAddr := na }
      (.exec (gcdCall a b) gcdEnv .stop)) :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel gcdEnv (gcdSeedFr fr na) ch (gcdCall a b)
        = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩)
          = .ok (.int ((Nat.gcd a b : Nat) : Int) .uint64)
        ∧ ∀ (addr : Nat) (c : HeapCell),
            Heap.lookup fr (.base ⟨addr⟩) = some c →
            Heap.lookup σf.heap (.base ⟨addr⟩) = some c :=
  normal_readout_of_total (gcd_framed a b ha hb fr na hfr hwf)

/-! ## The harness restatement (harness ruling 2026-08-13, design note
`docs/2026-08-12_example-spec-form.md` §11)

The USER-FACING form: one fixed three-phase Go harness
(`gcd_harness(a, b uint64) uint64 { r := gcd(a, b); return r }` — setup
and test phases are identities: argument-input subject, returned data
is the observable), stated over the machine's native function entry
`runFunctionWithContextM`. The statement observes ONLY termination +
the returned values — no heap readback, no seed/cell/frame vocabulary.
The implicit framing property is inherent in the empty-heap entry (the
entry builds its own state from the arguments). The canonical-run
segments and the `b`-value strong induction below re-derive the loop
walk at the harness's address layout (params at 0/1, harness result at
2, `r` at 3, the gcd frame at 4–7); the `%` executable fact and the
pure gcd-recursion step port verbatim from the framed layer above. -/

/-- The harness's `Func` record, verbatim from the pinned lowering (the
`example` pin below ties it by `rfl`). -/
def gcdHarnessFunc : Func :=
  { id := { key := "gcd_harness" },
    args := #[{ id := "a", typ := .int .uint64 },
              { id := "b", typ := .int .uint64 }],
    results := #[{ id := "$res0", typ := .int .uint64 }],
    body := .block
      #[]
      #[.seqn
          #[.initialization { id := "r", typ := .int .uint64 },
            .call #[.var "r"] ⟨"gcd"⟩ #[.var "a", .var "b"]],
        .seqn
          #[.assign (.var "$res0") (.var "r"),
            .returnStmt]],
    variadic := false,
    wrapper := false }

/-- The lowering pin: the harness in the theorem IS the frontend's
lowering of the corpus harness. -/
example : findFunctionIn? gcdLowered.funcs ⟨"gcd_harness"⟩
    = some gcdHarnessFunc := rfl

/-! ### Machine-layer configurations at the harness layout

Probe-verified (tracer `.tmp/hgcd-probe2.lean`); every raw segment
below re-checks the transcription by `rfl`. Address layout: 0 = `a`,
1 = `b` (the harness parameters), 2 = the harness `$res0`, 3 = `r`,
4 = `a`, 5 = `b`, 6 = `$res0`, 7 = `$forFirst` (the gcd frame);
allocator parked at 8 for the whole loop. -/

/-- The entry's frame environment (bindParams + allocDecls). -/
private def hEnv₀ : LocalEnv :=
  [[("$res0", .base ⟨2⟩), ("b", .base ⟨1⟩), ("a", .base ⟨0⟩)]]
/-- The harness scope at the call point (`r` declared). -/
private def hEnvH : LocalEnv :=
  [[("r", .base ⟨3⟩)],
   [("$res0", .base ⟨2⟩), ("b", .base ⟨1⟩), ("a", .base ⟨0⟩)]]
private def hEnvIn : LocalEnv :=
  [[("$forFirst", .base ⟨7⟩)], [],
   [("$res0", .base ⟨6⟩), ("b", .base ⟨5⟩), ("a", .base ⟨4⟩)]]
private def hEnvOut : LocalEnv :=
  [[], [("$res0", .base ⟨6⟩), ("b", .base ⟨5⟩), ("a", .base ⟨4⟩)]]
private def hEnvIn2 : LocalEnv := [] :: [] :: hEnvIn

/-- The continuation below the gcd loop head: the gcd epilogue, the
call frame delivering into `r`, the harness epilogue, the entry's pure
barrier frame. -/
private def hHeadTail : Cont :=
  .seq [] hEnvIn
    (.seq [.seqn #[.assign (.var "$res0") (.var "a"), .returnStmt]] hEnvOut
      (.frame [(.chain [], [.ref "r"])] hEnvH [.base ⟨6⟩] []
        (.seq [.seqn #[.assign (.var "$res0") (.var "r"), .returnStmt]]
          hEnvH
          (.frame [] [] [] [] .stop false))
        false))

/-- The loop-head configuration at the harness layout. -/
private def hHeadCfg : Config :=
  .exec (.while (.boolLit true) gcdWhileBody) hEnvIn hHeadTail
private def hLoopK : Cont := .loop (.boolLit true) gcdWhileBody hEnvIn hHeadTail
/-- The exit test's delivery continuation (segment split point). -/
private def hCmpCont : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: hEnvIn)
    (.seq [gcdIterBlock] ([] :: hEnvIn) hLoopK)

/-- The rhsK context at the `%` apply point. -/
private def hModTail (bv : Int) : Cont :=
  .rhsK .vals
    [.chain (.addr (.base ⟨4⟩)) [] [], .chain (.addr (.base ⟨5⟩)) [] []]
    [.int bv .uint64] [] (.seqn #[]) hEnvIn2
    (.seq [] hEnvIn2 (.seq [] ([] :: hEnvIn) hLoopK))

/-- The entry seed: the two bound parameters and the zeroed harness
result cell (the state `runFunctionWithContextM`'s prelude builds). -/
private def hSeedI (av bv : Int) : ExecState :=
  { types := gcdLowered.typeDefs.toList, functions := gcdLowered.funcs,
    methods := gcdLowered.methods,
    heap := [(.base ⟨0⟩, u64cell av), (.base ⟨1⟩, u64cell bv),
             (.base ⟨2⟩, u64cell 0)],
    nextAddr := 3 }

/-- The harness-body start configuration (the prelude's `c₀`). -/
private def hc₀ : Config :=
  .exec gcdHarnessFunc.body hEnv₀ (.frame [] [] [] [] .stop false)

/-- The in-loop state: harness cells fixed (`a₀`/`b₀` in the parameter
cells), pair cells `av`/`bv`, the `$forFirst` flag. -/
private def hStateP (a₀ b₀ av bv : Int) (ffv : Bool) : ExecState :=
  { types := gcdLowered.typeDefs.toList, functions := gcdLowered.funcs,
    methods := gcdLowered.methods,
    heap := [(.base ⟨0⟩, u64cell a₀), (.base ⟨1⟩, u64cell b₀),
             (.base ⟨2⟩, u64cell 0), (.base ⟨3⟩, u64cell 0),
             (.base ⟨4⟩, u64cell av), (.base ⟨5⟩, u64cell bv),
             (.base ⟨6⟩, u64cell 0), (.base ⟨7⟩, bcell ffv)],
    nextAddr := 8 }

/-- The terminal state: gcd delivered through `$res0` → `r` → the
harness `$res0` (cells 6, 3, 2), the pair drained. -/
private def hEndState (a₀ b₀ g : Int) : ExecState :=
  { types := gcdLowered.typeDefs.toList, functions := gcdLowered.funcs,
    methods := gcdLowered.methods,
    heap := [(.base ⟨0⟩, u64cell a₀), (.base ⟨1⟩, u64cell b₀),
             (.base ⟨2⟩, u64cell g), (.base ⟨3⟩, u64cell g),
             (.base ⟨4⟩, u64cell g), (.base ⟨5⟩, u64cell 0),
             (.base ⟨6⟩, u64cell g), (.base ⟨7⟩, bcell false)],
    nextAddr := 8 }

/-! ### The entry equation and the raw run segments -/

/-- **The entry equation**: `runFunctionWithContextM` on the harness at
symbolic arguments IS `runConfig` from the prelude-built seed plus the
result-location readback — the prelude (arity check, `bindParams`,
`allocDecls`, `pinResultLocs`) is fuel-independent and definitional at
the concrete shapes; the parameters land once-normalized. -/
private theorem gcdh_entry_eq (a b : Nat) (fuel : Nat) (ch : Choices) :
    runFunctionWithContextM fuel gcdLowered.typeDefs.toList
        gcdLowered.funcs gcdHarnessFunc
        #[.int (a : Int) .uint64, .int (b : Int) .uint64]
        gcdLowered.methods ch
      = (do
          let (sF, _) ← runConfig fuel
            (hSeedI (IntKind.normalize .uint64 (a : Int))
              (IntKind.normalize .uint64 (b : Int)))
            hc₀ ch
          return { values := (← loadMany sF [.base ⟨2⟩]).toArray }) := by
  with_unfolding_all rfl

/-- Entry: harness-body start → the gcd loop head (`r` declaration,
call frame entry — the arguments re-normalize at the parameter cells —
and the `$forFirst` block). 26 steps. -/
private theorem gcdh_entry_raw (av bv : Int) (ch : Choices) :
    stepFnIter 26 (hSeedI av bv) hc₀ ch
      = .ok (hHeadCfg,
          hStateP av bv (IntKind.normalize .uint64 av)
            (IntKind.normalize .uint64 bv) true, ch) := by
  with_unfolding_all rfl

/-- First-pass dispatch: head with the flag up → the exit-test
delivery. 25 steps. -/
private theorem gcdh_segA0_raw (a₀ b₀ av bv : Int) (ch : Choices) :
    stepFnIter 25 (hStateP a₀ b₀ av bv true) hHeadCfg ch
      = .ok (.retV (.bool (!(bv == 0))) hCmpCont,
          hStateP a₀ b₀ av bv false, ch) := by
  with_unfolding_all rfl

/-- Later-pass dispatch: head with the flag down → the exit-test
delivery. 18 steps. -/
private theorem gcdh_segA1_raw (a₀ b₀ av bv : Int) (ch : Choices) :
    stepFnIter 18 (hStateP a₀ b₀ av bv false) hHeadCfg ch
      = .ok (.retV (.bool (!(bv == 0))) hCmpCont,
          hStateP a₀ b₀ av bv false, ch) := by
  with_unfolding_all rfl

/-- Iteration phase 1: test true → up to the `%` apply point. 18
steps. -/
private theorem gcdh_segB1_raw (a₀ b₀ av bv : Int) (ch : Choices) :
    stepFnIter 18 (hStateP a₀ b₀ av bv false) (.retV (.bool true) hCmpCont) ch
      = .ok (.retV (.int bv .uint64)
            (.strictK .mod [.int av .uint64] [] hEnvIn2 (hModTail bv)),
          hStateP a₀ b₀ av bv false, ch) := by
  with_unfolding_all rfl

/-- Iteration phase 2: `%` delivered → the two stores and the drain
back to the loop head. 8 steps. -/
private theorem gcdh_segB2_raw (a₀ b₀ av bv mv : Int) (ch : Choices) :
    stepFnIter 8 (hStateP a₀ b₀ av bv false)
      (.retV (.int mv .uint64) (hModTail bv)) ch
      = .ok (hHeadCfg,
          hStateP a₀ b₀ (IntKind.normalize .uint64 bv)
            (IntKind.normalize .uint64 mv) false, ch) := by
  with_unfolding_all rfl

/-- Exit: test false → break unwinding, the gcd epilogue, the frame
exit into `r`, the harness epilogue (`$res0 = r; return`), the entry
barrier → the entry terminal. 40 steps; each store re-normalizes. -/
private theorem gcdh_exit_raw (a₀ b₀ av bv : Int) (ch : Choices) :
    stepFnIter 40 (hStateP a₀ b₀ av bv false) (.retV (.bool false) hCmpCont)
      ch
      = .ok (.next .stop,
          { types := gcdLowered.typeDefs.toList,
            functions := gcdLowered.funcs, methods := gcdLowered.methods,
            heap := [(.base ⟨0⟩, u64cell a₀), (.base ⟨1⟩, u64cell b₀),
              (.base ⟨2⟩,
               u64cell (IntKind.normalize .uint64 (IntKind.normalize .uint64
                 (IntKind.normalize .uint64 av)))),
              (.base ⟨3⟩,
               u64cell (IntKind.normalize .uint64
                 (IntKind.normalize .uint64 av))),
              (.base ⟨4⟩, u64cell av), (.base ⟨5⟩, u64cell bv),
              (.base ⟨6⟩, u64cell (IntKind.normalize .uint64 av)),
              (.base ⟨7⟩, bcell false)],
            nextAddr := 8 }, ch) := by
  with_unfolding_all rfl

/-! ### The loop induction (the framed layer's `b`-value strong
induction, at the harness layout) -/

/-- The exit, cleaned: at `b = 0` the run terminates with
`a = Nat.gcd a 0` delivered through all three result cells. -/
private theorem gcdh_exit (a₀ b₀ : Int) (a : Nat) (ha : a < 2 ^ 64)
    (ch : Choices) :
    stepFnIter 40 (hStateP a₀ b₀ (a : Int) ((0 : Nat) : Int) false)
      (.retV (.bool false) hCmpCont) ch
      = .ok (.next .stop, hEndState a₀ b₀ (a : Int), ch) := by
  have h := gcdh_exit_raw a₀ b₀ (a : Int) ((0 : Nat) : Int) ch
  rw [unorm_nat_of_lt ha, unorm_nat_of_lt ha, unorm_nat_of_lt ha] at h
  exact h

/-- **The loop**, by strong induction on the `b`-value: from the
exit-test delivery at pair `(a, b)`, the run reaches the entry terminal
with `Nat.gcd a b` delivered, within `45·b + 40` steps. -/
private theorem gcdh_loop (a₀ b₀ : Int) :
    ∀ μ : Nat, ∀ a b : Nat, b = μ → a < 2 ^ 64 → b < 2 ^ 64 →
    ∀ ch : Choices, ∃ k : Nat, k ≤ 45 * μ + 40 ∧
      stepFnIter k (hStateP a₀ b₀ (a : Int) (b : Int) false)
        (.retV (.bool (!((b : Int) == 0))) hCmpCont) ch
        = .ok (.next .stop, hEndState a₀ b₀ ((Nat.gcd a b : Nat) : Int),
            ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro a b hbμ ha hb ch
    rcases Nat.eq_zero_or_pos b with hz | hpos
    · -- exit: b = 0, gcd a 0 = a
      subst hz
      rw [show (!(((0 : Nat) : Int) == 0)) = false from by simp]
      refine ⟨40, by omega, ?_⟩
      rw [Nat.gcd_zero_right]
      exact gcdh_exit a₀ b₀ a ha ch
    · -- iterate: (a, b) → (b, a % b)
      have hbne : (((b : Nat) : Int) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq, Int.natCast_eq_zero]
        omega
      rw [show (!(((b : Nat) : Int) == 0)) = true from by
        rw [hbne]; rfl]
      have hmod : a % b < b := Nat.mod_lt _ hpos
      have hB1 := gcdh_segB1_raw a₀ b₀ (a : Int) (b : Int) ch
      have happly : stepFn (hStateP a₀ b₀ (a : Int) (b : Int) false)
          (.retV (.int (b : Int) .uint64)
            (.strictK .mod [.int (a : Int) .uint64] [] hEnvIn2
              (hModTail (b : Int)))) ch
          = .ok (.retV (.int ((a % b : Nat) : Int) .uint64)
              (hModTail (b : Int)),
            hStateP a₀ b₀ (a : Int) (b : Int) false, ch) :=
        stepFn_strict_apply (done := [.int (a : Int) .uint64])
          (applyStrictOp_mod_u64 hpos hb)
      have hB2 := gcdh_segB2_raw a₀ b₀ (a : Int) (b : Int)
        ((a % b : Nat) : Int) ch
      rw [unorm_nat_of_lt hb, unorm_nat_of_lt (by omega : a % b < 2 ^ 64)]
        at hB2
      have hA1 := gcdh_segA1_raw a₀ b₀ (b : Int) ((a % b : Nat) : Int) ch
      obtain ⟨k, hk, hrun⟩ := ih (a % b) (by omega) b (a % b) rfl hb
        (by omega) ch
      rw [show Nat.gcd b (a % b) = Nat.gcd a b from by
        rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec b a, Nat.gcd_comm b a]]
        at hrun
      refine ⟨18 + 1 + 8 + 18 + k, by omega, ?_⟩
      exact stepFnIter_chain
        (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain hB1 (stepFnIter_one happly))
            hB2)
          hA1)
        hrun

/-- **The harness run, end to end**: from the entry seed the run
reaches the entry terminal within `91 + 45·b` steps, with `Nat.gcd a b`
in the harness result cell. -/
private theorem gcdh_runs (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (ch : Choices) :
    ∃ k : Nat, k ≤ 91 + 45 * b ∧
      stepFnIter k (hSeedI (a : Int) (b : Int)) hc₀ ch
        = .ok (.next .stop,
            hEndState (a : Int) (b : Int) ((Nat.gcd a b : Nat) : Int), ch) := by
  have hE := gcdh_entry_raw (a : Int) (b : Int) ch
  rw [unorm_nat_of_lt ha, unorm_nat_of_lt hb] at hE
  have hA0 := gcdh_segA0_raw (a : Int) (b : Int) (a : Int) (b : Int) ch
  obtain ⟨k, hk, hrun⟩ := gcdh_loop (a : Int) (b : Int) b a b rfl ha hb ch
  exact ⟨26 + 25 + k, by omega,
    stepFnIter_chain (stepFnIter_chain hE hA0) hrun⟩

/-! ### The user-facing headline -/

/-- **THE HEADLINE** (harness ruling 2026-08-13, design note §11): *for
every `a, b` in the full uint64 × uint64 domain, `gcd_harness(a, b)` —
the fixed three-phase Go harness whose setup and test phases are
identities — completes normally through the machine's native function
entry, past one fuel bound, at every nondeterminism-choice stream, and
returns exactly `Nat.gcd a b`.*

The statement observes termination + the returned values only: no heap
readback, no seed/cell/frame vocabulary (the implicit framing property
is inherent in the empty-heap entry). No overflow condition appears
because none exists: `a % b` and `Nat.gcd a b` stay below `2^64` on the
whole domain, so fib's bounded/wrapped pair collapses into one
full-domain exact claim. The memory-quantified form is kept beneath as
`gcd_framed` (proof-side supporting layer). -/
theorem gcd_ok (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel gcdLowered.typeDefs.toList
          gcdLowered.funcs gcdHarnessFunc
          #[.int (a : Int) .uint64, .int (b : Int) .uint64]
          gcdLowered.methods ch
        = .ok { values := #[.int ((Nat.gcd a b : Nat) : Int) .uint64] } := by
  refine ⟨91 + 45 * b, fun fuel hfuel ch => ?_⟩
  rw [gcdh_entry_eq a b fuel ch, unorm_nat_of_lt ha, unorm_nat_of_lt hb]
  obtain ⟨k, hk, hrun⟩ := gcdh_runs a b ha hb ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [hfold, runConfig_next_stop]
  rfl

/-- **The D1 run-conditioned twin of the harness headline**: ANY
successful completion of the harness entry, at any fuel and any choice
stream, returns exactly `Nat.gcd a b` — derived from `gcd_ok` via the
shared `harness_readout_of_total` bridge (the `.ok`-equation headline
already determines every successful run; nothing is re-proven). -/
theorem gcd_readout (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ∀ (fuel : Nat) (ch : Choices) (r : Result),
      runFunctionWithContextM fuel gcdLowered.typeDefs.toList
          gcdLowered.funcs gcdHarnessFunc
          #[.int (a : Int) .uint64, .int (b : Int) .uint64]
          gcdLowered.methods ch
        = .ok r →
      r = { values := #[.int ((Nat.gcd a b : Nat) : Int) .uint64] } :=
  harness_readout_of_total (gcd_ok a b ha hb)

end GoLean.Examples.Gcd
