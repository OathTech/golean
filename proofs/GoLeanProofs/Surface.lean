import GoLean.GoCore.Eval
import GoLeanProofs.Specs.GoldenSlice
import Std.Data.ExtTreeMap

/-!
# The native spec surface (Layer S)

Design of record: `docs/2026-07-21_native-spec-surface.md`. This module is
the specification language humans read: heaplets, a deep-embedded assertion
language `HProp` with standard heaplet satisfaction, the `GoTriple` judgment
over interpreter (`execStmt`) runs, and the spec-surface arc's **step-0
intended statements** (widening loop: targets stated before the machinery
that discharges them).

**STRUCTURAL RULE (D1, the vocabulary criterion): this module and its
transitive imports are Iris-free** — no `IProp`, no `WP`, no masks, credits,
or ghost state, ever. `scripts/ci` lints the direct imports. The Iris side
consumes these definitions through the boundary layer (reflection/extraction,
staged §5 of the design note); nothing here may ever import it.

Status honesty: the `*_statement` definitions at the bottom are **stated
step-0 targets, not theorems**. Each becomes a theorem only when the generic
exit theorem (`goTriple_of_wp`, boundary layer) discharges it; nothing in
this file or its docstrings claims otherwise.
-/

open GoLean GoLean.GoCore

namespace GoLean.Surface

/-! ## Heaplets -/

/-- A heaplet: a finite fragment of the base-addressed heap. Pure data
(`Std.ExtTreeMap`), keyed by base address — the surface twin of the
Iris side's `GoHeapF HeapCell` (definitionally the same map type; the
boundary layer holds the kernel-checked agreement with `heapToMap`). -/
abbrev Heaplet := Std.ExtTreeMap Nat HeapCell compare

/-- Project the interpreter's association-list heap to a heaplet. Right
fold, head wins on key clash — the same fold as the Iris side's
`heapToMap`, so both match `Heap.lookup`'s first-match walk; the boundary
layer pins the agreement. -/
def heapletOf (h : Heap) : Heaplet :=
  h.foldr (fun (p : Loc × HeapCell) m =>
    match p.1 with
    | .base a => m.insert a.id p.2
    | _ => m) ∅

/-- Sub-heaplet: every binding of `h₁` is a binding of `h₂`. -/
def Heaplet.sub (h₁ h₂ : Heaplet) : Prop :=
  ∀ k c, h₁.get? k = some c → h₂.get? k = some c

/-! ## The assertion language

Deep-embedded so the boundary crossings (reflection in, extraction out) are
proven ONCE by induction on this syntax — never per-program (design note
D2: the surface is a readout format, not a logic; there is deliberately no
native frame rule and composition happens Iris-side). -/

/-- Surface assertions over heaplets. -/
inductive HProp : Type 1 where
  /-- The empty heaplet. -/
  | emp
  /-- A pure fact (on the empty heaplet — affine convention). -/
  | pure (φ : Prop)
  /-- Exactly one cell: base address `ℓ` holds `c`. -/
  | pointsTo (ℓ : Nat) (c : HeapCell)
  /-- Disjoint split. -/
  | sep (P Q : HProp)
  /-- Existential. -/
  | ex {α : Type} (f : α → HProp)

/-- Standard heaplet satisfaction. The `sep` split is characterized by
`get?` (disjointness + exact cover), which pins the split extensionally
without needing a union operation. -/
def sat (h : Heaplet) : HProp → Prop
  | .emp => h = ∅
  | .pure φ => φ ∧ h = ∅
  | .pointsTo ℓ c => h = (∅ : Heaplet).insert ℓ c
  | .sep P Q =>
      ∃ h₁ h₂ : Heaplet, sat h₁ P ∧ sat h₂ Q
        ∧ (∀ k, h₁.get? k = none ∨ h₂.get? k = none)
        ∧ (∀ k c, h.get? k = some c ↔ (h₁.get? k = some c ∨ h₂.get? k = some c))
  | .ex f => ∃ a, sat h (f a)

/-! Cheap non-triviality guards for `sat` (satisfaable and refutable). -/

example : sat (∅ : Heaplet) .emp := rfl
example {ℓ : Nat} {c : HeapCell} :
    sat ((∅ : Heaplet).insert ℓ c) (.pointsTo ℓ c) := rfl
example : ¬ sat (∅ : Heaplet) (.pure False) := fun h => h.1

/-! ## The triple -/

/-- Heap-model wellformedness at the surface: base addresses at or beyond
`na` are unallocated (statement-level restatement of the bridge's `HeapWf`;
the boundary layer holds the agreement). -/
def HeapBounded (hp : Heap) (na : Nat) : Prop :=
  ∀ n : Nat, na ≤ n → Heap.lookup hp (.base ⟨n⟩) = none

/-- **The surface Hoare judgment** (v1 per the design note): over any
well-formed initial state whose function table is `funcs`, whose locals are
`env₀`, and whose heap satisfies `P` *exactly* (D4: exact footprint — `P`
describes the whole initial heap), every terminating `execStmt` run of
`prog` — under ANY nondeterminism choices — ends in a state some sub-heaplet
of which satisfies `Q` (D3: intuitionistic postcondition; dead-frame cells
are framed away). `types`/`methods` sit at their empty defaults (v1 fragment
scope), and the initial heap carries the fragment-scope side condition
(`Correspondence.HeapFrag` — interpreter-level vocabulary: cells hold
fragment values; a `sat` projection cannot see non-base or shadowed
association-list entries, so this is stated on the raw heap; it weakens as
the fragment widens). Partial correctness: progress/never-stuck is a
separate companion judgment, per the design note. -/
def GoTriple (funcs : Array Func) (env₀ : LocalEnv) (P : HProp) (prog : Stmt)
    (Q : HProp) : Prop :=
  ∀ (hp : Heap) (na : Nat), HeapBounded hp na →
    Correspondence.HeapFrag { heap := hp } →
    sat (heapletOf hp) P →
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel { functions := funcs, locals := env₀, heap := hp, nextAddr := na }
          ch prog = .ok (.normal σf, ch') →
      ∃ h : Heaplet, h.sub (heapletOf σf.heap) ∧ sat h Q

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
  GoTriple sliceLowered.funcs outEnv outCell0 goldenDriver outCell2

open GoLean.Iris.GoldenSlice in
/-- The concrete seeded initial state for the system-register statements:
golden functions, the output cell at address 0, `r` bound to it. -/
def goldenOut : ExecState :=
  { functions := sliceLowered.funcs,
    locals := outEnv,
    heap := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)],
    nextAddr := 1 }

/-- **Step-0 target B (system register, plain predicate — the Verdi
register): the output cell holds 2.** No `∃`, no SL, no Iris: the
designated observable, by address, in every terminating run. -/
def goldenReturnsTwo_statement : Prop :=
  ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
    execStmt fuel goldenOut ch goldenDriver = .ok (.normal σf, ch') →
    loadLoc σf (.base ⟨0⟩) = .ok (.int 2 .int)

/-- **Step-0 negative twin: the output cell provably does NOT hold 3** in
any terminating run. Once target B is proven this is a two-line corollary
(`.ok`-injectivity + `2 ≠ 3`) — which is exactly the design-note point that
pinning observables collapses the refutation twins from design problems to
corollaries. Guards against spec-layer trivialization. -/
def goldenNotThree_statement : Prop :=
  ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
    execStmt fuel goldenOut ch goldenDriver = .ok (.normal σf, ch') →
    ¬ loadLoc σf (.base ⟨0⟩) = .ok (.int 3 .int)

end GoLean.Surface
