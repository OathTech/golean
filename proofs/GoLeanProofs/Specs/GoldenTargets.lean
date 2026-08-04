import GoLeanProofs.Surface
import GoLeanProofs.Specs.GoldenProgram

/-!
# The golden step-0 target statements (spec-surface arc)

The step-0 intended statements over the PINNED golden lowering
(`GoldenSlice.sliceLowered`) — relocated out of `Surface.lean` at the
proof-automation close-out (layering doctrine,
`docs/2026-08-01_tcb-and-layering-doctrine.md` §2): `Surface.lean` is the
GENERAL spec surface (heaplets, `HProp`, the judgments) and may not
depend on a `Specs/*` pin; the statements that name a pinned program are
target-layer and live here. Namespace unchanged (`GoLean.Surface`), so
every existing name survives.

**Iris-free like the surface itself**: this module's imports are exactly
`Surface` (GoCore + Std only) and the pure program pin `GoldenProgram` —
it is in the `scripts/ci` surface-purity scan.

Status honesty: the `*_statement` definitions are **stated step-0
targets, not theorems**. Each is a theorem only where a discharge names
it (`Specs/GoldenSurface.lean`); nothing in this file or its docstrings
claims otherwise.
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Surface

/-! ## Step-0 intended statements (the spec-surface arc's targets)

Stated FIRST, per the widening loop (`docs/2026-07-21_widening-loop.md`):
these are the proofs the arc's machinery must discharge, plus the negative
twin that must also hold. They are `def ... : Prop` — **targets, not
results**. -/

/-- The designated output cell: base address `0`, an int cell holding 0 —
seeded in the initial state and named by the driver's environment. This is
the observable-naming convention of design-note D5: the harness owns the
observable cells; the subject runs against them (mirroring how the
differential runner writes results into caller cells). -/
def outCell0 : HProp := .pointsTo 0 ⟨some (.int .int), .int 0 .int⟩

/-- ... and the same cell holding 2 (the intended final value). -/
def outCell2 : HProp := .pointsTo 0 ⟨some (.int .int), .int 2 .int⟩

/-- The seeded driver: call the subject function straight into the owned
output cell (no allocation in the driver — the whole point: the observable's
address is pinned by construction, not chosen by the machine). -/
abbrev goldenDriver : Stmt := .call #[.var "r"] ⟨"incViaCall"⟩ #[]

/-- The driver environment: `r` names the output cell. -/
abbrev outEnv : LocalEnv := [[("r", .base ⟨0⟩)]]

open GoLean.Iris.GoldenSlice in
/-- **Step-0 target A (SL register): the golden triple.**
`{r ↦ 0} r = incViaCall() {r ↦ 2}` over the frontend's actual lowering —
the pinned-observable form that (unlike the existential `*_computes`
theorems) IS entitled to the name "lowering target" once proven. -/
def goldenTriple_statement : Prop :=
  GoTriple sliceLowered.typeDefs.toList sliceLowered.funcs
    sliceLowered.methods outEnv outCell0 goldenDriver outCell2

open GoLean.Iris.GoldenSlice in
/-- **Step-0 target A′: the full golden spec** — the frame-closed triple
plus progress, as one judgment: safe non-panicking execution that delivers
`r ↦ 2` and touches nothing outside its footprint. -/
def goldenSpec_statement : Prop :=
  GoSpec sliceLowered.typeDefs.toList sliceLowered.funcs
    sliceLowered.methods outEnv outCell0 goldenDriver outCell2

open GoLean.Iris.GoldenSlice in
/-- **Step-0 target A″: the golden FUNCTION spec** — the form an engineer
reads: "`incViaCall()` takes no arguments, needs no heap, and returns 2" —
∀-quantified over the caller's target cell, its prior value, and the
frame. -/
def goldenFuncSpec_statement : Prop :=
  GoFuncSpec sliceLowered.typeDefs.toList sliceLowered.funcs
    sliceLowered.methods ⟨"incViaCall"⟩ .int #[] .emp
    (fun n => .pure (n = 2))

open GoLean.Iris.GoldenSlice in
/-- The concrete seeded initial state for the system-register statements:
golden functions, the output cell at address 0, `r` bound to it. -/
def goldenOut : ExecState :=
  { types := sliceLowered.typeDefs.toList,
    functions := sliceLowered.funcs,
    methods := sliceLowered.methods,
    heap := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)],
    nextAddr := 1 }

/-- **Step-0 target B (system register, plain predicate — the Verdi
register): the output cell holds 2.** No `∃`, no SL, no Iris: the
designated observable, by address, in every terminating run. -/
def goldenReturnsTwo_statement : Prop :=
  ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
    execStmt fuel outEnv goldenOut ch goldenDriver = .ok (.normal σf, ch') →
    loadLoc σf (.base ⟨0⟩) = .ok (.int 2 .int)

open GoLean.Iris.GoldenSlice in
/-- **Step-0 target C (arc `invariant-readout`): the golden register
invariant.** At EVERY relation-reachable configuration of the seeded
golden driver — mid-call included — the output cell holds `int 0` or
`int 2`: never 1, never garbage, never retyped. The miniature of a Verdi
register invariant ("the register only ever holds values the state machine
permits"); chosen so the physical invariant needs no ghost state (the
single write-step goes 0 → 2 atomically). A statement `GoTriple`
structurally cannot make (terminal states only) and `ProgressExec` does not
(never-stuck only). -/
def goldenInvariant_statement : Prop :=
  GoInvariant sliceLowered.typeDefs.toList sliceLowered.funcs
    sliceLowered.methods outEnv outCell0 goldenDriver
    (.ex fun (n : Int) =>
      .sep (.pointsTo 0 ⟨some (.int .int), .int n .int⟩)
        (.pure (n = 0 ∨ n = 2)))

/-- **Step-0 negative twin: the output cell provably does NOT hold 3** in
any terminating run. Once target B is proven this is a two-line corollary
(`.ok`-injectivity + `2 ≠ 3`) — which is exactly the design-note point that
pinning observables collapses the refutation twins from design problems to
corollaries. Guards against spec-layer trivialization. -/
def goldenNotThree_statement : Prop :=
  ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
    execStmt fuel outEnv goldenOut ch goldenDriver = .ok (.normal σf, ch') →
    ¬ loadLoc σf (.base ⟨0⟩) = .ok (.int 3 .int)

end GoLean.Surface
