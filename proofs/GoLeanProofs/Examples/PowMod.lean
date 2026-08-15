import GoLeanProofs.Examples.PowModProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.EntryEq

/-!
# PowMod — exponentiation by squaring, modulo `m` (Gallery Campaign G1)

Go source: `Corpus/coverage/exec/examples/powmod/main.go` (13 rows,
differentially green against `go run`). The lowering is pinned by
`scripts/check-golden` against `baselines/golden/powmod-lowered.repr`
and carried in `GoLeanProofs.Examples.PowModProgram`.

The subject is right-to-left binary exponentiation: `result` accumulates
the odd bits, `base` squares, `exp` halves, everything reduced `% mod`.
The harness is the S2 SCALAR three-phase shape (`powmod_harness(base,
exp, mod) { r := powMod(base, exp, mod); return r }` — setup and test
are identities, the returned scalar IS the observable), the same shape
`gcd` uses and for the same reason: with a scalar in and a scalar out an
S3 relational harness would degenerate, because the pre-state IS the
argument list.

THE HEADLINE is stated HERE, in the root, so the aggregator's
`import GoLeanProofs.Examples.PowMod` reaches it by name (the C-H4/C-H5
shape, adopted from birth).
-/

namespace GoLean.Examples.PowMod

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- The harness `Func`, verbatim from the pinned lowering (the pin below
ties it by `rfl`). -/
def powmodHarnessFunc : Func :=
{ id := { key := "powmod_harness" },
  args := #[{ id := "base", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
            { id := "exp", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
            { id := "mod", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
  results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
  body := GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "r", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "r"]
                    { key := "powMod" }
                    #[GoLean.GoCore.Expr.var "base", GoLean.GoCore.Expr.var "exp",
                      GoLean.GoCore.Expr.var "mod"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res0")
                    (GoLean.GoCore.Expr.var "r"),
                  GoLean.GoCore.Stmt.returnStmt]],
  variadic := false,
  wrapper := false }

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem powmodHarnessFunc_pin :
    findFunctionIn? powmodLowered.funcs ⟨"powmod_harness"⟩
    = some powmodHarnessFunc := rfl

/-! ## The statement vocabulary

`powModAnswer` is the whole postcondition: outside the `mod = 0` guard
the answer is the MATHEMATICAL `base ^ exp mod m` — not a restatement of
the loop. The `mod = 1` guard needs no case of its own, because Go's
guard and the mathematics agree there (`x ^ n % 1 = 0`); the `mod = 0`
case is the source's own documented definition, chosen over the division
panic `% 0` would raise. -/

/-- The answer the Go subject computes, stated mathematically. -/
def powModAnswer (base exp mod : Nat) : Nat :=
  if mod = 0 then 0 else base ^ exp % mod



abbrev pmZeroBlock : Stmt :=
  .block #[] #[.seqn #[.assign (.var "$res0") (.intLit 0 .uint64), .returnStmt]]
abbrev pmGuard (c : Int) : Stmt :=
  .ifThenElse (.eqCmp (.int .uint64) (.var "mod") (.intLit c .uint64))
    pmZeroBlock (.seqn #[])
abbrev pmResultInit : Stmt :=
  .seqn #[.initialization { id := "result", typ := .int .uint64 },
          .assign (.var "result") (.intLit 1 .uint64)]
abbrev pmBaseReduce : Stmt :=
  .seqn #[.assign (.var "base") (.mod (.var "base") (.var "mod"))]
abbrev pmResAsgn : Stmt :=
  .seqn #[.assign (.var "result")
    (.mod (.mul (.var "result") (.var "base")) (.var "mod"))]
abbrev pmResBlock : Stmt := .block #[] #[pmResAsgn]
abbrev pmBaseAsgn : Stmt :=
  .seqn #[.assign (.var "base") (.mod (.mul (.var "base") (.var "base")) (.var "mod"))]
abbrev pmExpAsgn : Stmt :=
  .seqn #[.assign (.var "exp") (.div (.var "exp") (.intLit 2 .uint64))]
abbrev pmUserBlock : Stmt :=
  .block #[]
    #[.ifThenElse
        (.eqCmp (.int .uint64) (.mod (.var "exp") (.intLit 2 .uint64))
          (.intLit 1 .uint64))
        pmResBlock (.seqn #[]),
      pmBaseAsgn, pmExpAsgn]
abbrev pmWhileBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false)) (.seqn #[]),
      .seqn #[],
      .ifThenElse (.greaterCmp (.var "exp") (.intLit 0 .uint64))
        (.seqn #[]) .breakStmt,
      pmUserBlock]
abbrev pmLoopBlock : Stmt :=
  .block #[]
    #[.initialization { id := "$forFirst", typ := .bool },
      .assign (.var "$forFirst") (.boolLit true),
      .while (.boolLit true) pmWhileBody]
abbrev pmEpilogue : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "result"), .returnStmt]

def powModFunc : Func :=
  { id := { key := "powMod" },
    args := #[{ id := "base", typ := .int .uint64 },
              { id := "exp", typ := .int .uint64 },
              { id := "mod", typ := .int .uint64 }],
    results := #[{ id := "$res0", typ := .int .uint64 }],
    body := .block #[]
      #[pmGuard 0, pmGuard 1, pmResultInit, pmBaseReduce, pmLoopBlock, pmEpilogue],
    variadic := false, wrapper := false }

theorem powMod_pin : findFunctionIn? powmodLowered.funcs ⟨"powMod"⟩ = some powModFunc := rfl

/-! ## Address layout -/

private abbrev u64cell (v : Int) : HeapCell := ⟨some (.int .uint64), .int v .uint64⟩
private abbrev bcell (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩

private def hEnvH : LocalEnv :=
  [[("r", .base ⟨4⟩)],
   [("$res0", .base ⟨3⟩), ("mod", .base ⟨2⟩), ("exp", .base ⟨1⟩), ("base", .base ⟨0⟩)]]
private def pEnvP : LocalEnv :=
  [[("$res0", .base ⟨8⟩), ("mod", .base ⟨7⟩), ("exp", .base ⟨6⟩), ("base", .base ⟨5⟩)]]
private def pEnvG : LocalEnv := [] :: pEnvP
private def pEnvR : LocalEnv := [("result", .base ⟨9⟩)] :: pEnvP
private def pEnvIn : LocalEnv := [("$forFirst", .base ⟨10⟩)] :: pEnvR
private def pEnvB1 : LocalEnv := [] :: pEnvIn
private def pEnvB2 : LocalEnv := [] :: pEnvB1
private def pEnvB3 : LocalEnv := [] :: pEnvB2

private def hEpilogue : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "r"), .returnStmt]
private def pmCallK : Cont :=
  .frame [(.chain [], [.ref "r"])] hEnvH [.base ⟨8⟩] []
    (.seq [hEpilogue] hEnvH (.frame [] [] [] [] .stop false)) false
private def pmBodyK : Cont := .seq [pmEpilogue] pEnvR pmCallK
private def pmHeadTail : Cont := .seq [] pEnvIn pmBodyK
private def pmHeadCfg : Config := .exec (.while (.boolLit true) pmWhileBody) pEnvIn pmHeadTail
private def pmLoopK : Cont := .loop (.boolLit true) pmWhileBody pEnvIn pmHeadTail
private def pmCmpCont : Cont :=
  .ifK (.seqn #[]) .breakStmt pEnvB1 (.seq [pmUserBlock] pEnvB1 pmLoopK)
private def pmBodyEnd : Cont := .seq [] pEnvB1 pmLoopK
private def pmTail2 : Cont := .seq [pmBaseAsgn, pmExpAsgn] pEnvB2 pmBodyEnd
private def pmIfK : Cont := .ifK pmResBlock (.seqn #[]) pEnvB2 pmTail2
private def pmEqK : Cont :=
  .strictK (.eqCmp (.int .uint64)) [] [.intLit 1 .uint64] pEnvB2 pmIfK
private def pmExpModK (ev : Int) : Cont := .strictK .mod [.int ev .uint64] [] pEnvB2 pmEqK
private def pmResRhsK : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨9⟩)) [] []] [] [] (.seqn #[]) pEnvB3
    (.seq [] pEnvB3 pmTail2)
private def pmResModK (v : Int) : Cont := .strictK .mod [.int v .uint64] [] pEnvB3 pmResRhsK
private def pmResMulK (rv : Int) : Cont :=
  .strictK .mul [.int rv .uint64] []
    pEnvB3 (.strictK .mod [] [.var "mod"] pEnvB3 pmResRhsK)
private def pmBaseRhsK : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] [] (.seqn #[]) pEnvB2
    (.seq [pmExpAsgn] pEnvB2 pmBodyEnd)
private def pmBaseModK (v : Int) : Cont := .strictK .mod [.int v .uint64] [] pEnvB2 pmBaseRhsK
private def pmBaseMulK (bv : Int) : Cont :=
  .strictK .mul [.int bv .uint64] []
    pEnvB2 (.strictK .mod [] [.var "mod"] pEnvB2 pmBaseRhsK)
private def pmExpRhsK : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨6⟩)) [] []] [] [] (.seqn #[]) pEnvB2
    (.seq [] pEnvB2 pmBodyEnd)
private def pmExpDivK (ev : Int) : Cont := .strictK .div [.int ev .uint64] [] pEnvB2 pmExpRhsK

derive_entry_eq pm_entry_eq powmodLowered powmodHarnessFunc pmSeed pmC0

private def pmStateP (b₀ e₀ m₀ mv rv bv ev : Int) (ff : Bool) : ExecState :=
  { types := powmodLowered.typeDefs.toList, functions := powmodLowered.funcs,
    methods := powmodLowered.methods,
    heap := [(.base ⟨0⟩, u64cell b₀), (.base ⟨1⟩, u64cell e₀), (.base ⟨2⟩, u64cell m₀),
             (.base ⟨3⟩, u64cell 0), (.base ⟨4⟩, u64cell 0),
             (.base ⟨5⟩, u64cell bv), (.base ⟨6⟩, u64cell ev), (.base ⟨7⟩, u64cell mv),
             (.base ⟨8⟩, u64cell 0), (.base ⟨9⟩, u64cell rv), (.base ⟨10⟩, bcell ff)],
    nextAddr := 11 }

/-! ## Entry-side continuations and states -/

private def pmGuardK (rest : List Stmt) : Cont :=
  .ifK pmZeroBlock (.seqn #[]) pEnvG (.seq rest pEnvG pmCallK)
private def pmEntryRhsK : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] [] (.seqn #[]) pEnvR
    (.seq [pmLoopBlock, pmEpilogue] pEnvR pmCallK)
private def pmEntryModK (bv : Int) : Cont :=
  .strictK .mod [.int bv .uint64] [] pEnvR pmEntryRhsK

private def pmStateG (b₀ e₀ m₀ bv ev mv : Int) : ExecState :=
  { types := powmodLowered.typeDefs.toList, functions := powmodLowered.funcs,
    methods := powmodLowered.methods,
    heap := [(.base ⟨0⟩, u64cell b₀), (.base ⟨1⟩, u64cell e₀), (.base ⟨2⟩, u64cell m₀),
             (.base ⟨3⟩, u64cell 0), (.base ⟨4⟩, u64cell 0),
             (.base ⟨5⟩, u64cell bv), (.base ⟨6⟩, u64cell ev), (.base ⟨7⟩, u64cell mv),
             (.base ⟨8⟩, u64cell 0)],
    nextAddr := 9 }

private def pmStateR (b₀ e₀ m₀ bv ev mv rv : Int) : ExecState :=
  { types := powmodLowered.typeDefs.toList, functions := powmodLowered.funcs,
    methods := powmodLowered.methods,
    heap := [(.base ⟨0⟩, u64cell b₀), (.base ⟨1⟩, u64cell e₀), (.base ⟨2⟩, u64cell m₀),
             (.base ⟨3⟩, u64cell 0), (.base ⟨4⟩, u64cell 0),
             (.base ⟨5⟩, u64cell bv), (.base ⟨6⟩, u64cell ev), (.base ⟨7⟩, u64cell mv),
             (.base ⟨8⟩, u64cell 0), (.base ⟨9⟩, u64cell rv)],
    nextAddr := 10 }

/-! ## Raw segments (`with_unfolding_all rfl`: pure definitional evaluation
of the interpreter at symbolic values; splits exactly at the
data-dependent points — the three `ifK` consumptions and the six
`applyStrictOp` steps). -/

/-- Entry → the `mod == 0` guard's delivery. 21 steps. -/
private theorem pm_segE0 (b e m : Int) (ch : Choices) :
    stepFnIter 21 (pmSeed b e m) pmC0 ch
      = .ok (.retV (.bool (decide (IntKind.normalize .uint64 m = 0)))
            (pmGuardK [pmGuard 1, pmResultInit, pmBaseReduce, pmLoopBlock, pmEpilogue]),
          pmStateG b e m (IntKind.normalize .uint64 b) (IntKind.normalize .uint64 e)
            (IntKind.normalize .uint64 m), ch) := by
  with_unfolding_all rfl

/-- `mod == 0` guard FALSE → the `mod == 1` guard's delivery. 9 steps. -/
private theorem pm_segE1 (b₀ e₀ m₀ bv ev mv : Int) (ch : Choices) :
    stepFnIter 9 (pmStateG b₀ e₀ m₀ bv ev mv)
      (.retV (.bool false)
        (pmGuardK [pmGuard 1, pmResultInit, pmBaseReduce, pmLoopBlock, pmEpilogue])) ch
      = .ok (.retV (.bool (decide (mv = 1)))
            (pmGuardK [pmResultInit, pmBaseReduce, pmLoopBlock, pmEpilogue]),
          pmStateG b₀ e₀ m₀ bv ev mv, ch) := by
  with_unfolding_all rfl

/-- Either guard TRUE → `$res0 = 0`, return, frame exit, harness epilogue,
the entry terminal. 38 steps from either guard. -/
private theorem pm_segE0T (b₀ e₀ m₀ bv ev mv : Int) (rest : List Stmt) (ch : Choices) :
    stepFnIter 38 (pmStateG b₀ e₀ m₀ bv ev mv)
      (.retV (.bool true) (pmGuardK rest)) ch
      = .ok (.next .stop,
          { types := powmodLowered.typeDefs.toList, functions := powmodLowered.funcs,
            methods := powmodLowered.methods,
            heap := [(.base ⟨0⟩, u64cell b₀), (.base ⟨1⟩, u64cell e₀),
                     (.base ⟨2⟩, u64cell m₀), (.base ⟨3⟩, u64cell 0),
                     (.base ⟨4⟩, u64cell 0), (.base ⟨5⟩, u64cell bv),
                     (.base ⟨6⟩, u64cell ev), (.base ⟨7⟩, u64cell mv),
                     (.base ⟨8⟩, u64cell 0)],
            nextAddr := 9 }, ch) := by
  with_unfolding_all rfl

/-- `mod == 1` guard FALSE → `result := 1`, then the `base % mod` apply
point. 25 steps. -/
private theorem pm_segE2 (b₀ e₀ m₀ bv ev mv : Int) (ch : Choices) :
    stepFnIter 25 (pmStateG b₀ e₀ m₀ bv ev mv)
      (.retV (.bool false) (pmGuardK [pmResultInit, pmBaseReduce, pmLoopBlock, pmEpilogue]))
      ch
      = .ok (.retV (.int mv .uint64) (pmEntryModK bv),
          pmStateR b₀ e₀ m₀ bv ev mv (IntKind.normalize .uint64 1), ch) := by
  with_unfolding_all rfl

/-- `base % mod` delivered → the store and the `$forFirst` block, up to
the loop head. 18 steps. -/
private theorem pm_segE3 (b₀ e₀ m₀ bv ev mv rv nv : Int) (ch : Choices) :
    stepFnIter 18 (pmStateR b₀ e₀ m₀ bv ev mv rv)
      (.retV (.int nv .uint64) pmEntryRhsK) ch
      = .ok (pmHeadCfg,
          pmStateP b₀ e₀ m₀ mv rv (IntKind.normalize .uint64 nv) ev true, ch) := by
  with_unfolding_all rfl

/-- First-pass dispatch (flag up) → the exit test's delivery. 25 steps. -/
private theorem pm_segA0 (b₀ e₀ m₀ mv rv bv ev : Int) (ch : Choices) :
    stepFnIter 25 (pmStateP b₀ e₀ m₀ mv rv bv ev true) pmHeadCfg ch
      = .ok (.retV (.bool (decide (0 < ev))) pmCmpCont,
          pmStateP b₀ e₀ m₀ mv rv bv ev false, ch) := by
  with_unfolding_all rfl

/-- Later-pass dispatch (flag down) → the exit test's delivery. 18 steps. -/
private theorem pm_segA1 (b₀ e₀ m₀ mv rv bv ev : Int) (ch : Choices) :
    stepFnIter 18 (pmStateP b₀ e₀ m₀ mv rv bv ev false) pmHeadCfg ch
      = .ok (.retV (.bool (decide (0 < ev))) pmCmpCont,
          pmStateP b₀ e₀ m₀ mv rv bv ev false, ch) := by
  with_unfolding_all rfl

/-- Exit: test false → break unwinding, `$res0 = result`, return, the call
frame's exit into `r`, the harness epilogue, the entry terminal. 40 steps. -/
private theorem pm_exit_raw (b₀ e₀ m₀ mv rv bv ev : Int) (ch : Choices) :
    stepFnIter 40 (pmStateP b₀ e₀ m₀ mv rv bv ev false)
      (.retV (.bool false) pmCmpCont) ch
      = .ok (.next .stop,
          { types := powmodLowered.typeDefs.toList, functions := powmodLowered.funcs,
            methods := powmodLowered.methods,
            heap := [(.base ⟨0⟩, u64cell b₀), (.base ⟨1⟩, u64cell e₀),
                     (.base ⟨2⟩, u64cell m₀),
                     (.base ⟨3⟩,
                      u64cell (IntKind.normalize .uint64
                        (IntKind.normalize .uint64 (IntKind.normalize .uint64 rv)))),
                     (.base ⟨4⟩,
                      u64cell (IntKind.normalize .uint64 (IntKind.normalize .uint64 rv))),
                     (.base ⟨5⟩, u64cell bv), (.base ⟨6⟩, u64cell ev),
                     (.base ⟨7⟩, u64cell mv),
                     (.base ⟨8⟩, u64cell (IntKind.normalize .uint64 rv)),
                     (.base ⟨9⟩, u64cell rv), (.base ⟨10⟩, bcell false)],
            nextAddr := 11 }, ch) := by
  with_unfolding_all rfl

/-- Iteration phase A: test true → the `exp % 2` apply point. 11 steps. -/
private theorem pm_iterA (b₀ e₀ m₀ mv rv bv ev : Int) (ch : Choices) :
    stepFnIter 11 (pmStateP b₀ e₀ m₀ mv rv bv ev false)
      (.retV (.bool true) pmCmpCont) ch
      = .ok (.retV (.int 2 .uint64) (pmExpModK ev),
          pmStateP b₀ e₀ m₀ mv rv bv ev false, ch) := by
  with_unfolding_all rfl

/-- Iteration phase B: `exp % 2` delivered → the `== 1` test's delivery.
3 steps. -/
private theorem pm_iterB (b₀ e₀ m₀ mv rv bv ev q : Int) (ch : Choices) :
    stepFnIter 3 (pmStateP b₀ e₀ m₀ mv rv bv ev false)
      (.retV (.int q .uint64) pmEqK) ch
      = .ok (.retV (.bool (decide (q = 1))) pmIfK,
          pmStateP b₀ e₀ m₀ mv rv bv ev false, ch) := by
  with_unfolding_all rfl

/-- Odd branch, phase C1: the `result * base` apply point. 13 steps. -/
private theorem pm_iterC1 (b₀ e₀ m₀ mv rv bv ev : Int) (ch : Choices) :
    stepFnIter 13 (pmStateP b₀ e₀ m₀ mv rv bv ev false)
      (.retV (.bool true) pmIfK) ch
      = .ok (.retV (.int bv .uint64) (pmResMulK rv),
          pmStateP b₀ e₀ m₀ mv rv bv ev false, ch) := by
  with_unfolding_all rfl

/-- Odd branch, phase C2: the product delivered → the `% mod` apply point.
2 steps. -/
private theorem pm_iterC2 (b₀ e₀ m₀ mv rv bv ev p : Int) (ch : Choices) :
    stepFnIter 2 (pmStateP b₀ e₀ m₀ mv rv bv ev false)
      (.retV (.int p .uint64) (.strictK .mod [] [.var "mod"] pEnvB3 pmResRhsK)) ch
      = .ok (.retV (.int mv .uint64) (pmResModK p),
          pmStateP b₀ e₀ m₀ mv rv bv ev false, ch) := by
  with_unfolding_all rfl

/-- Odd branch, phase C3: the new `result` stored → the `base * base`
apply point. 16 steps. -/
private theorem pm_iterC3 (b₀ e₀ m₀ mv rv bv ev nv : Int) (ch : Choices) :
    stepFnIter 16 (pmStateP b₀ e₀ m₀ mv rv bv ev false)
      (.retV (.int nv .uint64) pmResRhsK) ch
      = .ok (.retV (.int bv .uint64) (pmBaseMulK bv),
          pmStateP b₀ e₀ m₀ mv (IntKind.normalize .uint64 nv) bv ev false, ch) := by
  with_unfolding_all rfl

/-- Even branch: straight to the `base * base` apply point. 13 steps. -/
private theorem pm_iterD (b₀ e₀ m₀ mv rv bv ev : Int) (ch : Choices) :
    stepFnIter 13 (pmStateP b₀ e₀ m₀ mv rv bv ev false)
      (.retV (.bool false) pmIfK) ch
      = .ok (.retV (.int bv .uint64) (pmBaseMulK bv),
          pmStateP b₀ e₀ m₀ mv rv bv ev false, ch) := by
  with_unfolding_all rfl

/-- Phase E: the square delivered → the `% mod` apply point. 2 steps. -/
private theorem pm_iterE (b₀ e₀ m₀ mv rv bv ev p : Int) (ch : Choices) :
    stepFnIter 2 (pmStateP b₀ e₀ m₀ mv rv bv ev false)
      (.retV (.int p .uint64) (.strictK .mod [] [.var "mod"] pEnvB2 pmBaseRhsK)) ch
      = .ok (.retV (.int mv .uint64) (pmBaseModK p),
          pmStateP b₀ e₀ m₀ mv rv bv ev false, ch) := by
  with_unfolding_all rfl

/-- Phase F: the new `base` stored → the `exp / 2` apply point. 14 steps. -/
private theorem pm_iterF (b₀ e₀ m₀ mv rv bv ev nv : Int) (ch : Choices) :
    stepFnIter 14 (pmStateP b₀ e₀ m₀ mv rv bv ev false)
      (.retV (.int nv .uint64) pmBaseRhsK) ch
      = .ok (.retV (.int 2 .uint64) (pmExpDivK ev),
          pmStateP b₀ e₀ m₀ mv rv (IntKind.normalize .uint64 nv) ev false, ch) := by
  with_unfolding_all rfl

/-- Phase G: the halved `exp` stored → back at the loop head. 7 steps. -/
private theorem pm_iterG (b₀ e₀ m₀ mv rv bv ev nv : Int) (ch : Choices) :
    stepFnIter 7 (pmStateP b₀ e₀ m₀ mv rv bv ev false)
      (.retV (.int nv .uint64) pmExpRhsK) ch
      = .ok (pmHeadCfg,
          pmStateP b₀ e₀ m₀ mv rv bv (IntKind.normalize .uint64 nv) false, ch) := by
  with_unfolding_all rfl

/-- GAP-WITNESS (kit gap A1): uint64 `*` below the wrap threshold. -/
theorem applyStrictOp_mul_u64 {σ : ExecState} {a b : Nat} (h : a * b < 2 ^ 64) :
    applyStrictOp σ .mul [.int (a : Int) .uint64, .int (b : Int) .uint64]
      = .ok (.int ((a * b : Nat) : Int) .uint64, σ) := by
  have hraw : applyStrictOp σ .mul [.int (a : Int) .uint64, .int (b : Int) .uint64]
      = .ok (.int (IntKind.normalize .uint64 ((a : Int) * (b : Int))) .uint64, σ) := rfl
  have hc : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by push_cast; rfl
  rw [hraw, ← hc, unorm_nat_of_lt h]

/-- GAP-WITNESS (kit gap A2): uint64 `/` at a positive divisor. -/
theorem applyStrictOp_div_u64 {σ : ExecState} {a b : Nat}
    (hb : 0 < b) (ha : a < 2 ^ 64) :
    applyStrictOp σ .div [.int (a : Int) .uint64, .int (b : Int) .uint64]
      = .ok (.int ((a / b : Nat) : Int) .uint64, σ) := by
  have hbne : (((b : Nat) : Int) == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, Int.natCast_eq_zero]; omega
  have htdiv : Int.tdiv (a : Int) (b : Int) = ((a / b : Nat) : Int) := rfl
  have hnorm : IntKind.normalize .uint64 ((a / b : Nat) : Int) = ((a / b : Nat) : Int) :=
    unorm_nat_of_lt (by have := Nat.div_le_self a b; omega)
  simp only [applyStrictOp, valueAsInt, hbne, intBinaryResult,
    valueAsIntValue, htdiv, IntKind.compatibleResult,
    Bool.false_eq_true, if_false, Bind.bind, Except.bind, pure, Except.pure]
  simp only [show (IntKind.uint64 == IntKind.uint64) = true from rfl, if_true, hnorm]


/-- The Go loop's own recursion. -/
def powLoop (m r b e : Nat) : Nat :=
  if h : e = 0 then r
  else powLoop m (if e % 2 = 1 then r * b % m else r) (b * b % m) (e / 2)
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)

/-- `powLoop`'s base equation, isolated so the well-founded unfolding is
paid once rather than at every consumer. -/
theorem powLoop_zero (m r b : Nat) : powLoop m r b 0 = r := by
  rw [powLoop]; simp

/-- `powLoop`'s step equation, isolated for the same reason. -/
theorem powLoop_step (m r b e : Nat) (he : e ≠ 0) :
    powLoop m r b e
      = powLoop m (if e % 2 = 1 then r * b % m else r) (b * b % m) (e / 2) := by
  rw [powLoop]; simp only [dif_neg he]

theorem powLoop_eq (m : Nat) (hm : 0 < m) :
    ∀ e r b : Nat, r < m → powLoop m r b e = (r * b ^ e) % m := by
  have key : ∀ x y : Nat, (x % m * y) % m = (x * y) % m := by
    intro x y; simp [Nat.mul_mod]
  have keyR : ∀ x y : Nat, (x * (y % m)) % m = (x * y) % m := by
    intro x y; simp [Nat.mul_mod]
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro r b hr
    by_cases he : e = 0
    · subst he; rw [powLoop_zero]; simp [Nat.mod_eq_of_lt hr]
    · rw [powLoop_step m r b e he]
      have hpos : 0 < e := Nat.pos_of_ne_zero he
      have hlt : e / 2 < e := Nat.div_lt_self hpos (by omega)
      have hr' : (if e % 2 = 1 then r * b % m else r) < m := by
        split
        · exact Nat.mod_lt _ hm
        · exact hr
      rw [ih (e / 2) hlt _ (b * b % m) hr']
      have hb2 : ∀ k : Nat, (b * b) ^ k = b ^ (2 * k) := by
        intro k; rw [Nat.pow_mul]; congr 1; rw [Nat.pow_succ, Nat.pow_one]
      have hpw : (b * b % m) ^ (e / 2) % m = b ^ (2 * (e / 2)) % m := by
        rw [← Nat.pow_mod, hb2]
      have hstep : ∀ R : Nat,
          (R * (b * b % m) ^ (e / 2)) % m = (R * b ^ (2 * (e / 2))) % m := by
        intro R; rw [← keyR R ((b * b % m) ^ (e / 2)), hpw, keyR]
      by_cases hodd : e % 2 = 1
      · have hbe : b ^ (2 * (e / 2)) * b = b ^ e := by
          rw [← Nat.pow_succ]; congr 1; omega
        rw [if_pos hodd, hstep, key]
        congr 1
        rw [← hbe, Nat.mul_assoc, Nat.mul_comm b (b ^ (2 * (e / 2)))]
      · have he2 : 2 * (e / 2) = e := by omega
        rw [if_neg hodd, hstep, he2]


/-! ## The loop induction

The measure is the EXPONENT'S BIT COUNT, not the exponent: `exp`
halves, so an `exp < 2 ^ d` hypothesis carries the induction with `d`
levels and the whole uint64 domain is covered at `d = 64`. That is why
the shipped fuel bound is a CONSTANT rather than a function of the
arguments. -/

private def pmEndState (b₀ e₀ m₀ mv bv ev g : Int) : ExecState :=
  { types := powmodLowered.typeDefs.toList, functions := powmodLowered.funcs,
    methods := powmodLowered.methods,
    heap := [(.base ⟨0⟩, u64cell b₀), (.base ⟨1⟩, u64cell e₀), (.base ⟨2⟩, u64cell m₀),
             (.base ⟨3⟩, u64cell g), (.base ⟨4⟩, u64cell g),
             (.base ⟨5⟩, u64cell bv), (.base ⟨6⟩, u64cell ev), (.base ⟨7⟩, u64cell mv),
             (.base ⟨8⟩, u64cell g), (.base ⟨9⟩, u64cell g), (.base ⟨10⟩, bcell false)],
    nextAddr := 11 }

/-- The exit, cleaned: an in-range `result` re-normalizes to itself
through all three result cells. -/
private theorem pm_exit (b₀ e₀ m₀ mv bv ev : Int) (r : Nat) (hr : r < 2 ^ 64)
    (ch : Choices) :
    stepFnIter 40 (pmStateP b₀ e₀ m₀ mv (r : Int) bv ev false)
      (.retV (.bool false) pmCmpCont) ch
      = .ok (.next .stop, pmEndState b₀ e₀ m₀ mv bv ev (r : Int), ch) := by
  have h := pm_exit_raw b₀ e₀ m₀ mv (r : Int) bv ev ch
  simp only [unorm_nat_of_lt hr] at h
  exact h

/-- The shared tail of BOTH iteration branches: from the `base * base`
apply point through the squaring, the halving and the next dispatch, to
the exit test's delivery. 44 steps. -/
private theorem pm_iter_tail (b₀ e₀ m₀ : Int) (m : Nat) (hm : 0 < m) (hm64 : m < 2 ^ 64)
    (r b e : Nat) (hbb : b * b < 2 ^ 64) (he64 : e < 2 ^ 64) (ch : Choices) :
    stepFnIter 44 (pmStateP b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int) false)
      (.retV (.int (b : Int) .uint64) (pmBaseMulK (b : Int))) ch
      = .ok (.retV (.bool (decide (0 < (((e / 2 : Nat)) : Int)))) pmCmpCont,
          pmStateP b₀ e₀ m₀ (m : Int) (r : Int) (((b * b % m : Nat)) : Int)
            (((e / 2 : Nat)) : Int) false, ch) := by
  show stepFnIter (1 + 2 + 1 + 14 + 1 + 7 + 18) _ _ _ = _
  have hmul : stepFn (pmStateP b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int) false)
      (.retV (.int (b : Int) .uint64) (pmBaseMulK (b : Int))) ch
      = .ok (.retV (.int ((b * b : Nat) : Int) .uint64)
          (.strictK .mod [] [.var "mod"] pEnvB2 pmBaseRhsK),
        pmStateP b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int) false, ch) :=
    stepFn_strict_apply (done := [.int (b : Int) .uint64]) (applyStrictOp_mul_u64 hbb)
  have hE := pm_iterE b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int)
    ((b * b : Nat) : Int) ch
  have hmod : stepFn (pmStateP b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int) false)
      (.retV (.int (m : Int) .uint64) (pmBaseModK ((b * b : Nat) : Int))) ch
      = .ok (.retV (.int ((b * b % m : Nat) : Int) .uint64) pmBaseRhsK,
        pmStateP b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int) false, ch) :=
    stepFn_strict_apply (done := [.int ((b * b : Nat) : Int) .uint64])
      (applyStrictOp_mod_u64 hm hm64)
  have hF := pm_iterF b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int)
    ((b * b % m : Nat) : Int) ch
  rw [unorm_nat_of_lt (Nat.lt_trans (Nat.mod_lt (b * b) hm) hm64)] at hF
  have hdiv : stepFn (pmStateP b₀ e₀ m₀ (m : Int) (r : Int)
        ((b * b % m : Nat) : Int) (e : Int) false)
      (.retV (.int 2 .uint64) (pmExpDivK (e : Int))) ch
      = .ok (.retV (.int ((e / 2 : Nat) : Int) .uint64) pmExpRhsK,
        pmStateP b₀ e₀ m₀ (m : Int) (r : Int) ((b * b % m : Nat) : Int) (e : Int) false,
        ch) :=
    stepFn_strict_apply (done := [.int (e : Int) .uint64])
      (applyStrictOp_div_u64 (b := 2) (by omega) he64)
  have hG := pm_iterG b₀ e₀ m₀ (m : Int) (r : Int) ((b * b % m : Nat) : Int) (e : Int)
    ((e / 2 : Nat) : Int) ch
  rw [unorm_nat_of_lt (by omega : e / 2 < 2 ^ 64)] at hG
  have hA1 := pm_segA1 b₀ e₀ m₀ (m : Int) (r : Int) ((b * b % m : Nat) : Int)
    ((e / 2 : Nat) : Int) ch
  exact stepFnIter_chain
    (stepFnIter_chain
      (stepFnIter_chain
        (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_one hmul) hE)
            (stepFnIter_one hmod))
          hF)
        (stepFnIter_one hdiv))
      hG)
    hA1

/-- **The loop**, by induction on the exponent's BIT BUDGET `d`: from
the exit test's delivery at `(result, base, exp) = (r, b, e)` with
`e < 2 ^ d`, the run reaches the entry terminal with `powLoop m r b e`
delivered, within `92·d + 40` steps. -/
private theorem pm_loop (b₀ e₀ m₀ : Int) (m : Nat) (hm : 0 < m) (hm64 : m < 2 ^ 64)
    (hnw : (m - 1) * (m - 1) < 2 ^ 64) :
    ∀ d : Nat, ∀ r b e : Nat, e < 2 ^ d → r < m → b < m → e < 2 ^ 64 →
    ∀ ch : Choices, ∃ k : Nat, ∃ bv ev : Int, k ≤ 92 * d + 40 ∧
      stepFnIter k (pmStateP b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int) false)
        (.retV (.bool (decide (0 < ((e : Nat) : Int)))) pmCmpCont) ch
        = .ok (.next .stop,
            pmEndState b₀ e₀ m₀ (m : Int) bv ev ((powLoop m r b e : Nat) : Int), ch) := by
  have hsq : ∀ x : Nat, x < m → x * x < 2 ^ 64 := by
    intro x hx
    have : x * x ≤ (m - 1) * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  intro d
  induction d with
  | zero =>
    intro r b e he hr hb he64 ch
    have hz : e = 0 := by simpa using he
    subst hz
    refine ⟨40, (b : Int), ((0 : Nat) : Int), by omega, ?_⟩
    rw [show (decide (0 < (((0 : Nat)) : Int))) = false from by decide, powLoop_zero]
    exact pm_exit b₀ e₀ m₀ (m : Int) (b : Int) ((0 : Nat) : Int) r (by omega) ch
  | succ d ih =>
    intro r b e he hr hb he64 ch
    rcases Nat.eq_zero_or_pos e with hz | hpos
    · subst hz
      refine ⟨40, (b : Int), ((0 : Nat) : Int), by omega, ?_⟩
      rw [show (decide (0 < (((0 : Nat)) : Int))) = false from by decide, powLoop_zero]
      exact pm_exit b₀ e₀ m₀ (m : Int) (b : Int) ((0 : Nat) : Int) r (by omega) ch
    · have htrue : (decide (0 < ((e : Nat) : Int))) = true := by
        simp only [decide_eq_true_eq]; exact_mod_cast hpos
      rw [htrue]
      have hA := pm_iterA b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int) ch
      have hmod2 : stepFn (pmStateP b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int) false)
          (.retV (.int 2 .uint64) (pmExpModK (e : Int))) ch
          = .ok (.retV (.int ((e % 2 : Nat) : Int) .uint64) pmEqK,
            pmStateP b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int) false, ch) :=
        stepFn_strict_apply (done := [.int (e : Int) .uint64])
          (applyStrictOp_mod_u64 (b := 2) (by omega) (by omega))
      have hB := pm_iterB b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int)
        ((e % 2 : Nat) : Int) ch
      have hehalf : e / 2 < 2 ^ d := by
        have h2 : e < 2 ^ (d + 1) := he
        rw [Nat.pow_succ] at h2
        omega
      by_cases hodd : e % 2 = 1
      · -- ODD: the result accumulates one factor of `base`
        have hdec : (decide ((((e % 2 : Nat)) : Int) = 1)) = true := by
          rw [hodd]; decide
        rw [hdec] at hB
        have hrb : r * b < 2 ^ 64 := by
          have : r * b ≤ (m - 1) * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
          omega
        have hC1 := pm_iterC1 b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int) ch
        have hmul : stepFn (pmStateP b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int) false)
            (.retV (.int (b : Int) .uint64) (pmResMulK (r : Int))) ch
            = .ok (.retV (.int ((r * b : Nat) : Int) .uint64)
                (.strictK .mod [] [.var "mod"] pEnvB3 pmResRhsK),
              pmStateP b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int) false, ch) :=
          stepFn_strict_apply (done := [.int (r : Int) .uint64])
            (applyStrictOp_mul_u64 hrb)
        have hC2 := pm_iterC2 b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int)
          ((r * b : Nat) : Int) ch
        have hmod : stepFn (pmStateP b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int) false)
            (.retV (.int (m : Int) .uint64) (pmResModK ((r * b : Nat) : Int))) ch
            = .ok (.retV (.int ((r * b % m : Nat) : Int) .uint64) pmResRhsK,
              pmStateP b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int) false, ch) :=
          stepFn_strict_apply (done := [.int ((r * b : Nat) : Int) .uint64])
            (applyStrictOp_mod_u64 hm hm64)
        have hC3 := pm_iterC3 b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int)
          ((r * b % m : Nat) : Int) ch
        rw [unorm_nat_of_lt (Nat.lt_trans (Nat.mod_lt (r * b) hm) hm64)] at hC3
        have hT := pm_iter_tail b₀ e₀ m₀ m hm hm64 (r * b % m) b e (hsq b hb) he64 ch
        obtain ⟨k, bv, ev, hk, hrun⟩ :=
          ih (r * b % m) (b * b % m) (e / 2) hehalf
            (Nat.mod_lt _ hm) (Nat.mod_lt _ hm) (by omega) ch
        refine ⟨11 + 1 + 3 + 13 + 1 + 2 + 1 + 16 + 44 + k, bv, ev, by omega, ?_⟩
        rw [powLoop_step m r b e (by omega), if_pos hodd]
        exact stepFnIter_chain
          (stepFnIter_chain
            (stepFnIter_chain
              (stepFnIter_chain
                (stepFnIter_chain
                  (stepFnIter_chain
                    (stepFnIter_chain
                      (stepFnIter_chain (stepFnIter_chain hA (stepFnIter_one hmod2)) hB)
                      hC1)
                    (stepFnIter_one hmul))
                  hC2)
                (stepFnIter_one hmod))
              hC3)
            hT)
          hrun
      · -- EVEN: the result is untouched this pass
        have h0 : e % 2 = 0 := by omega
        have hdec : (decide ((((e % 2 : Nat)) : Int) = 1)) = false := by
          rw [h0]; decide
        rw [hdec] at hB
        have hD := pm_iterD b₀ e₀ m₀ (m : Int) (r : Int) (b : Int) (e : Int) ch
        have hT := pm_iter_tail b₀ e₀ m₀ m hm hm64 r b e (hsq b hb) he64 ch
        obtain ⟨k, bv, ev, hk, hrun⟩ :=
          ih r (b * b % m) (e / 2) hehalf hr (Nat.mod_lt _ hm) (by omega) ch
        refine ⟨11 + 1 + 3 + 13 + 44 + k, bv, ev, by omega, ?_⟩
        rw [powLoop_step m r b e (by omega), if_neg hodd]
        exact stepFnIter_chain
          (stepFnIter_chain
            (stepFnIter_chain
              (stepFnIter_chain (stepFnIter_chain hA (stepFnIter_one hmod2)) hB)
              hD)
            hT)
          hrun

/-! ## The end-to-end run and the headline -/

/-- The guard terminal (both `mod = 0` and `mod = 1` reach it): the
harness result cell holds `0`. -/
private def pmGuardEnd (b₀ e₀ m₀ bv ev mv : Int) : ExecState :=
  { types := powmodLowered.typeDefs.toList, functions := powmodLowered.funcs,
    methods := powmodLowered.methods,
    heap := [(.base ⟨0⟩, u64cell b₀), (.base ⟨1⟩, u64cell e₀), (.base ⟨2⟩, u64cell m₀),
             (.base ⟨3⟩, u64cell 0), (.base ⟨4⟩, u64cell 0), (.base ⟨5⟩, u64cell bv),
             (.base ⟨6⟩, u64cell ev), (.base ⟨7⟩, u64cell mv), (.base ⟨8⟩, u64cell 0)],
    nextAddr := 9 }

/-- **The run, end to end**: from the machine entry's post-prelude seed
the harness reaches the entry terminal within `6027` steps — a CONSTANT
over the whole domain, because the exponent halves — with
`powModAnswer base exp mod` in the harness result cell. -/
private theorem pm_runs (base exp mod : Nat) (hb : base < 2 ^ 64) (he : exp < 2 ^ 64)
    (hm : mod < 2 ^ 64) (hnw : (mod - 1) * (mod - 1) < 2 ^ 64) (ch : Choices) :
    ∃ k : Nat, ∃ σf : ExecState, k ≤ 6027 ∧
      stepFnIter k (pmSeed (base : Int) (exp : Int) (mod : Int)) pmC0 ch
        = .ok (.next .stop, σf, ch)
      ∧ loadMany σf [.base ⟨3⟩]
          = .ok [.int ((powModAnswer base exp mod : Nat) : Int) .uint64] := by
  have hE0 := pm_segE0 (base : Int) (exp : Int) (mod : Int) ch
  rw [unorm_nat_of_lt hb, unorm_nat_of_lt he, unorm_nat_of_lt hm] at hE0
  by_cases hm0 : mod = 0
  · -- `mod == 0`: the source's own documented answer, 0
    subst hm0
    rw [show (decide ((((0 : Nat)) : Int) = 0)) = true from by decide] at hE0
    refine ⟨21 + 38, _, by omega,
      stepFnIter_chain hE0
        (pm_segE0T (base : Int) (exp : Int) ((0 : Nat) : Int) (base : Int) (exp : Int)
          ((0 : Nat) : Int) _ ch), ?_⟩
    simp only [powModAnswer, if_pos rfl]
    rfl
  · have hne : (decide ((((mod : Nat)) : Int) = 0)) = false := by
      simp only [decide_eq_false_iff_not, ne_eq, Int.natCast_eq_zero]
      omega
    rw [hne] at hE0
    have hE1 := pm_segE1 (base : Int) (exp : Int) (mod : Int) (base : Int) (exp : Int)
      (mod : Int) ch
    by_cases hm1 : mod = 1
    · -- `mod == 1`: the guard and the mathematics agree (`x ^ n % 1 = 0`)
      subst hm1
      rw [show (decide ((((1 : Nat)) : Int) = 1)) = true from by decide] at hE1
      refine ⟨21 + 9 + 38, _, by omega,
        stepFnIter_chain (stepFnIter_chain hE0 hE1)
          (pm_segE0T (base : Int) (exp : Int) ((1 : Nat) : Int) (base : Int) (exp : Int)
            ((1 : Nat) : Int) _ ch), ?_⟩
      have h1 : powModAnswer base exp 1 = 0 := by
        rw [powModAnswer, if_neg hm0, Nat.mod_one]
      rw [h1]
      rfl
    · -- the real loop: `mod ≥ 2`
      have hm2 : 2 ≤ mod := by omega
      have hmpos : 0 < mod := by omega
      rw [show (decide ((((mod : Nat)) : Int) = 1)) = false from by
        simp only [decide_eq_false_iff_not]
        intro hc
        exact hm1 (by exact_mod_cast hc)] at hE1
      have hE2 := pm_segE2 (base : Int) (exp : Int) (mod : Int) (base : Int) (exp : Int)
        (mod : Int) ch
      rw [show IntKind.normalize .uint64 1 = ((1 : Nat) : Int) from by decide] at hE2
      have hmodapply :
          stepFn (pmStateR (base : Int) (exp : Int) (mod : Int) (base : Int) (exp : Int)
              (mod : Int) ((1 : Nat) : Int))
            (.retV (.int (mod : Int) .uint64) (pmEntryModK (base : Int))) ch
            = .ok (.retV (.int ((base % mod : Nat) : Int) .uint64) pmEntryRhsK,
              pmStateR (base : Int) (exp : Int) (mod : Int) (base : Int) (exp : Int)
                (mod : Int) ((1 : Nat) : Int), ch) :=
        stepFn_strict_apply (done := [.int (base : Int) .uint64])
          (applyStrictOp_mod_u64 hmpos hm)
      have hE3 := pm_segE3 (base : Int) (exp : Int) (mod : Int) (base : Int) (exp : Int)
        (mod : Int) ((1 : Nat) : Int) ((base % mod : Nat) : Int) ch
      rw [unorm_nat_of_lt (Nat.lt_trans (Nat.mod_lt base hmpos) hm)] at hE3
      have hA0 := pm_segA0 (base : Int) (exp : Int) (mod : Int) (mod : Int)
        ((1 : Nat) : Int) ((base % mod : Nat) : Int) (exp : Int) ch
      obtain ⟨k, bv, ev, hk, hloop⟩ :=
        pm_loop (base : Int) (exp : Int) (mod : Int) mod hmpos hm hnw 64
          1 (base % mod) exp (by omega) (by omega) (Nat.mod_lt base hmpos) he ch
      refine ⟨21 + 9 + 25 + 1 + 18 + 25 + k, _, by omega,
        stepFnIter_chain
          (stepFnIter_chain
            (stepFnIter_chain
              (stepFnIter_chain
                (stepFnIter_chain (stepFnIter_chain hE0 hE1) hE2)
                (stepFnIter_one hmodapply))
              hE3)
            hA0)
          hloop, ?_⟩
      have hans : powLoop mod 1 (base % mod) exp = powModAnswer base exp mod := by
        rw [powLoop_eq mod hmpos exp 1 (base % mod) (by omega), powModAnswer,
          if_neg hm0, Nat.one_mul, ← Nat.pow_mod]
      rw [hans]
      rfl

/-! ## The user-facing statements -/

/-- **THE HEADLINE (§11 harness form, S2 SCALAR)**: for every `base` and
`exp` in the full uint64 domain and every `mod` whose arithmetic cannot
wrap — the source's OWN no-wrap condition `(mod−1)² < 2⁶⁴`, quoted from
the Go comment — running `powmod_harness(base, exp, mod)` through the
machine's native function entry completes normally past ONE fuel bound,
at every nondeterminism-choice stream, and returns exactly
`powModAnswer base exp mod` — that is, `base ^ exp mod m`, with `0` on
the `mod = 0` guard.

Honesty clauses, recorded rather than hidden:

* **The claim is MATHEMATICS, not a restatement of the loop.** The
  postcondition is `base ^ exp % mod` — natural-number exponentiation —
  so the theorem is the correctness of exponentiation by squaring, not
  "the program computes what the program computes". `powLoop`, which
  does mirror the loop, is proof-side only and is bridged to the
  mathematics by `powLoop_eq`.
* **`mod = 1` needs no case.** Go's second guard returns `0`, and
  `base ^ exp % 1 = 0`; the statement covers it through the general
  branch, so nothing is special-cased that the mathematics does not
  already say.
* **`mod = 0` is the SOURCE'S definition, not a mathematical fact.**
  Go's `% 0` panics; this program documents and returns `0` instead, and
  `powModAnswer` says exactly that. Attribution: the program's own
  arithmetic.
* **The domain bound `(mod−1)² < 2⁶⁴` is the wrap threshold**, quoted
  from the Go source comment; equivalently `mod ≤ 2³²`. Outside it the
  uint64 multiplies wrap and the answer is NOT `base ^ exp mod m`, and
  this theorem deliberately does not claim it. Of the 13 corpus rows
  exactly ONE — `wrap` (`mod = 2⁶³ − 1`) — lies outside; the other 12,
  `harness-extreme` (`base = 2⁶³ − 1`, `exp = 2⁶³ − 2`,
  `mod = 999999937`) included, are inside the theorem's domain.
  Attribution: the program's own arithmetic (machine-integer honesty,
  FD-E3).
* **The fuel bound is a CONSTANT, 6027, over the whole domain** — the
  exponent halves, so 64 iterations bound every `exp < 2⁶⁴`. It is a
  BOUND, not a measurement: the measured step count is
  `139 + 72·bits(exp) + 20·popcount(exp)` (probe-verified; `139` at
  `exp = 0`, `6027` at `exp = 2⁶⁴−1`, where the two coincide), and
  `59`/`68` on the `mod = 0`/`mod = 1` guards.
* **`∀ ch` is vacuous here and stated anyway.** The subject consumes no
  nondeterminism choice; the quantifier records that, rather than
  hiding a `Choices` argument.
* **Machine idealization** as in the other entries: entry from an empty
  heap, an unbounded heap, allocation always succeeds. -/
theorem powmod_ok (base exp mod : Nat) (hb : base < 2 ^ 64) (he : exp < 2 ^ 64)
    (hm : mod < 2 ^ 64) (hnw : (mod - 1) * (mod - 1) < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel powmodLowered.typeDefs.toList
          powmodLowered.funcs powmodHarnessFunc
          #[.int (base : Int) .uint64, .int (exp : Int) .uint64,
            .int (mod : Int) .uint64]
          powmodLowered.methods ch
        = .ok { values := #[.int ((powModAnswer base exp mod : Nat) : Int) .uint64] } := by
  refine ⟨6027, fun fuel hfuel ch => ?_⟩
  rw [pm_entry_eq (base : Int) (exp : Int) (mod : Int) fuel ch,
    unorm_nat_of_lt hb, unorm_nat_of_lt he, unorm_nat_of_lt hm]
  obtain ⟨k, σf, hk, hrun, hread⟩ := pm_runs base exp mod hb he hm hnw ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [hfold, runConfig_next_stop]
  simp only [bind, Except.bind, pure, Except.pure, hread]

/-- **The D1 run-conditioned twin**: ANY successful completion of the
harness entry, at any fuel and any choice stream, returns exactly
`powModAnswer base exp mod` — derived from `powmod_ok` through the
shared `harness_readout_of_total` bridge; nothing is re-proven. -/
theorem powmod_readout (base exp mod : Nat) (hb : base < 2 ^ 64) (he : exp < 2 ^ 64)
    (hm : mod < 2 ^ 64) (hnw : (mod - 1) * (mod - 1) < 2 ^ 64) :
    ∀ (fuel : Nat) (ch : Choices) (r : Result),
      runFunctionWithContextM fuel powmodLowered.typeDefs.toList
          powmodLowered.funcs powmodHarnessFunc
          #[.int (base : Int) .uint64, .int (exp : Int) .uint64,
            .int (mod : Int) .uint64]
          powmodLowered.methods ch
        = .ok r →
      r = { values := #[.int ((powModAnswer base exp mod : Nat) : Int) .uint64] } :=
  harness_readout_of_total (powmod_ok base exp mod hb he hm hnw)

end GoLean.Examples.PowMod
