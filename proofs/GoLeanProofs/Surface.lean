import GoLean.GoCore.MachineSound
import GoLeanProofs.Specs.GoldenProgram
import Std.Data.ExtTreeMap

/-!
# The native spec surface (Layer S)

Design of record: `docs/2026-07-21_native-spec-surface.md`. This module is
the specification language humans read: heaplets, a deep-embedded assertion
language `HProp` with standard heaplet satisfaction, the `GoTriple` judgment
over `execStmt` runs (the F4 §2 wrapper: fuel-bounded iteration of the
machine's `stepFn` under the old name and result shape — not a shim), and the spec-surface arc's **step-0
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

open GoLean GoLean.GoCore GoLean.GoCore.Machine

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

/-- An admissible framed initial state for `P`: well-formed (`bounded`),
and its heaplet splits into the `P`-footprint `hP` and a frame `F` — the
cells the program is NOT given. `F` is the "in any heap where the
footprint is allocated" quantifier of a quantified testcase
(`docs/2026-07-21_spec-space.md` §2). (Reshape R3: the old `frag`
fragment-scoping field — `Correspondence.HeapFrag` — is RETIRED: the
machine's soundness theorems are total over the full fragment, so the
side-condition it discharged no longer exists. Statements got strictly
stronger.) -/
structure InitialSplit (P : HProp) (hp : Heap) (na : Nat)
    (hP F : Heaplet) : Prop where
  bounded : HeapBounded hp na
  disj : ∀ k, hP.get? k = none ∨ F.get? k = none
  cover : ∀ k c, (heapletOf hp).get? k = some c
    ↔ (hP.get? k = some c ∨ F.get? k = some c)
  sat_pre : sat hP P

/-- **The surface Hoare judgment — FRAME-CLOSED** (the quantified-testcase
form: "give the program any inputs, in ANY heap where the `P`-cells are
allocated"). Over any admissible initial state whose heaplet is
`P`-footprint ⊎ frame `F`, every terminating `execStmt` run of `prog` —
under ANY nondeterminism choices — ends in a state where (a) some
`Q`-satisfying heaplet exists DISJOINT from `F`, and (b) **every binding
of `F` is intact in the final heap** (net frame preservation — precisely
`F.sub`; as a terminal-state judgment this is the strongest observable
form: it does not, and cannot, speak about intermediate configurations).
(b) is the separation in separation logic: without it a triple is a
statement about hermetic laboratory heaps, not call sites, and
pointer-returning contracts could not promise freshness. Intuitionistic on the `Q` side (dead-frame
cells framed away); `types`/`methods` at their empty defaults (v1 fragment
scope); partial correctness — `Progress` below is the companion, and
`GoSpec` bundles both. -/
def GoTriple (funcs : Array Func) (env₀ : LocalEnv) (P : HProp) (prog : Stmt)
    (Q : HProp) : Prop :=
  ∀ (hp : Heap) (na : Nat) (hP F : Heaplet), InitialSplit P hp na hP F →
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel env₀ { functions := funcs, heap := hp, nextAddr := na }
          ch prog = .ok (.normal σf, ch') →
      ∃ hQ : Heaplet, (∀ k, hQ.get? k = none ∨ F.get? k = none)
        ∧ hQ.sub (heapletOf σf.heap) ∧ F.sub (heapletOf σf.heap) ∧ sat hQ Q

/-- **The progress companion**: from any admissible framed initial state,
every relation-reachable configuration is either the terminal value or can
step — never stuck. Stated over the trusted relation (`Steps`/`Step`,
Iris-free). Scope note (tracked as #24): a `.panicked` terminal counts as
stuck in this reading, so for programs whose WP is provable this also
implies no reachable panics — the guarantee reads "safe, non-panicking
execution". -/
def Progress (funcs : Array Func) (env₀ : LocalEnv) (P : HProp)
    (prog : Stmt) : Prop :=
  ∀ (hp : Heap) (na : Nat) (hP F : Heaplet), InitialSplit P hp na hP F →
    ∀ (c' : Config) (σ' : ExecState),
      Steps (.exec prog env₀ .stop)
        { functions := funcs, heap := hp, nextAddr := na } c' σ' →
      c' = .next .stop ∨ ∃ (c'' : Config) (σ'' : ExecState), Step c' σ' c'' σ''

/-- **The invariance judgment** (arc `invariant-readout`, design of record
`docs/2026-07-22_invariant-readout-design.md`): from any admissible framed
initial state, EVERY relation-reachable configuration — mid-call,
mid-expression, wherever control is — has a sub-heaplet satisfying `I`.

Tradition honesty (design note §1): this is NOT a separation-logic notion
— Reynolds/O'Hearn triples speak only of terminal states. It is
**Verdi-style invariance over the transition system** (`Rel.Step`), the
native shape of safety properties of non-terminating programs (for which
`GoTriple` is vacuous). `HProp` is only the assertion language; the
sub-heaplet reading is `I ∗ true` — the rest of the heap (the program's
working state) may be in any mid-computation shape, which is what makes
invariance provable at all (§3: `I` is the protocol-governed portion of
the state, never the whole mutated footprint). -/
def GoInvariant (funcs : Array Func) (env₀ : LocalEnv) (P : HProp)
    (prog : Stmt) (I : HProp) : Prop :=
  ∀ (hp : Heap) (na : Nat) (hP F : Heaplet), InitialSplit P hp na hP F →
    ∀ (c' : Config) (σ' : ExecState),
      Steps (.exec prog env₀ .stop)
        { functions := funcs, heap := hp, nextAddr := na } c' σ' →
      ∃ hI : Heaplet, hI.sub (heapletOf σ'.heap) ∧ sat hI I

/-- Precondition strengthening for `GoInvariant` (surface-level, Iris-free):
a stronger precondition proves the same invariance. Only `sat_pre` in
`InitialSplit` mentions `P`, so this is a two-line record update. Used by
discharges whose stated precondition (e.g. "the cell holds 0") entails the
exit theorem's canonical `I ∗ P'` shape ("the cell satisfies I"). -/
theorem goInvariant_mono_pre {funcs env₀ prog} {P Q I : HProp}
    (h : ∀ hp : Heaplet, sat hp P → sat hp Q)
    (hinv : GoInvariant funcs env₀ Q prog I) :
    GoInvariant funcs env₀ P prog I :=
  fun hp na hP F hin c' σ' hsteps =>
    hinv hp na hP F { hin with sat_pre := h hP hin.sat_pre } c' σ' hsteps

/-- **The full surface judgment**: the frame-closed triple AND progress —
"runs safely, and every terminating run delivers `Q` with the frame's
bindings intact". This is the form specs should be stated in; a triple
alone is satisfiable by a program that always crashes. -/
def GoSpec (funcs : Array Func) (env₀ : LocalEnv) (P : HProp) (prog : Stmt)
    (Q : HProp) : Prop :=
  GoTriple funcs env₀ P prog Q ∧ Progress funcs env₀ P prog

/-- **The function-level quantified-testcase form** (v1: unary int result;
`(T, error)` returns are queued behind the interface widening —
`docs/2026-07-21_spec-space.md` §6). `GoFuncSpec funcs fid kind args P Q`
reads: *calling `fid(args)` in any admissible heap satisfying `P` — with
any frame, into any caller target cell with any prior value — terminates
only in states where the target cell received some `n` with `Q n`, beside
`P`'s leftovers, the frame's bindings intact.* The return value is observed
exactly where Go's call protocol delivers it: the caller's target cell,
written at frame exit from the callee's named result locals — the same
values `collectResults`/the differential runner reads, and the binding
point that stays correct when `defer` (which may mutate named results
after `return`) enters the fragment. -/
def GoFuncSpec (funcs : Array Func) (fid : FuncId) (kind : IntKind)
    (args : Array Expr) (P : HProp) (Q : Int → HProp) : Prop :=
  ∀ (ra : Nat) (w : GoValue),
    GoSpec funcs [[("$callres", Loc.base ⟨ra⟩)]]
      (.sep (.pointsTo ra ⟨some (.int kind), w⟩) P)
      (.call #[.var "$callres"] fid args)
      (.ex fun (n : Int) =>
        .sep (.pointsTo ra ⟨some (.int kind), .int n kind⟩) (Q n))

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
/-- **Step-0 target A′: the full golden spec** — the frame-closed triple
plus progress, as one judgment: safe non-panicking execution that delivers
`r ↦ 2` and touches nothing outside its footprint. -/
def goldenSpec_statement : Prop :=
  GoSpec sliceLowered.funcs outEnv outCell0 goldenDriver outCell2

open GoLean.Iris.GoldenSlice in
/-- **Step-0 target A″: the golden FUNCTION spec** — the form an engineer
reads: "`incViaCall()` takes no arguments, needs no heap, and returns 2" —
∀-quantified over the caller's target cell, its prior value, and the
frame. -/
def goldenFuncSpec_statement : Prop :=
  GoFuncSpec sliceLowered.funcs ⟨"incViaCall"⟩ .int #[] .emp
    (fun n => .pure (n = 2))

open GoLean.Iris.GoldenSlice in
/-- The concrete seeded initial state for the system-register statements:
golden functions, the output cell at address 0, `r` bound to it. -/
def goldenOut : ExecState :=
  { functions := sliceLowered.funcs,
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
structurally cannot make (terminal states only) and `Progress` does not
(never-stuck only). -/
def goldenInvariant_statement : Prop :=
  GoInvariant sliceLowered.funcs outEnv outCell0 goldenDriver
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
