import GoLean.GoCore.MachineSound
import Std.Data.ExtTreeMap

/-!
# The native spec surface (Layer S)

Design of record: `docs/2026-07-21_native-spec-surface.md`. This module is
the specification language humans read: heaplets, a deep-embedded assertion
language `HProp` with standard heaplet satisfaction, the `GoTriple` judgment
over `execStmt` runs (the F4 §2 wrapper: fuel-bounded iteration of the
machine's `stepFn` under the old name and result shape — not a shim), and
the progress/invariance companions.

**STRUCTURAL RULE (D1, the vocabulary criterion): this module and its
transitive imports are Iris-free** — no `IProp`, no `WP`, no masks, credits,
or ghost state, ever. `scripts/ci` lints the direct imports. The Iris side
consumes these definitions through the boundary layer (reflection/extraction,
staged §5 of the design note); nothing here may ever import it.

**LAYERING (proof-automation close-out, 2026-08-01)**: this module is
GENERAL — no pinned program appears. The spec-surface arc's step-0
statements over the golden lowering, which used to close this file,
moved to `Specs/GoldenTargets.lean` (same `GoLean.Surface` namespace, so
every name survived); target-naming statements are target-layer and a
general module may not import `Specs/*` (`scripts/ci` lints the
direction).
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

/-- An admissible framed initial state for `P`: well-formed (`bounded`,
`wf`), and its heaplet splits into the `P`-footprint `hP` and a frame `F`
— the cells the program is NOT given. `F` is the "in any heap where the
footprint is allocated" quantifier of a quantified testcase
(`docs/2026-07-21_spec-space.md` §2). (Reshape R3: the old `frag`
fragment-scoping field — `Correspondence.HeapFrag` — is RETIRED: the
machine's soundness theorems are total over the full fragment, so the
side-condition it discharged no longer exists. Statements got strictly
stronger.)

The `wf` conjunct (sem-adequacy arc StateWf decision, 2026-08-04;
`docs/2026-08-03_sem-adequacy-arc.md` slice-3 entry): admissible initial
states are LEGITIMATE machine states — every location's root base id lies
strictly below the allocator's `nextAddr`, wherever that location occurs:
in the heap (keys and stored values), in the initial environment `env₀`,
in the program text (`Expr.locLit`), and in the function bodies of
`funcs`. This is `Machine.MachineWf` over the seeded state and the
initial configuration `.exec prog env₀ .stop`; at concrete seeds it is
discharged by `decide` (the checker is kernel-reducible). The `ExecState`
record literal omits `types`/`methods` (their defaults): the loc
components provably ignore them — `ExecState.locSup` inspects only
`heap` and `functions` — and `MachineWf`'s map-iteration typing
component (sem-adequacy slice 3, 2026-08-04), though `types`-dependent
in general, is trivially true at the initial configuration (an `.exec`
over `.stop` carries no `mapIterK`), so the omission stays
definitionally interchangeable with a literal that includes them
(`progressExec_of_progress` transports it). -/
structure InitialSplit (P : HProp) (hp : Heap) (na : Nat)
    (hP F : Heaplet) (funcs : Array Func) (env₀ : LocalEnv) (prog : Stmt) : Prop where
  bounded : HeapBounded hp na
  disj : ∀ k, hP.get? k = none ∨ F.get? k = none
  cover : ∀ k c, (heapletOf hp).get? k = some c
    ↔ (hP.get? k = some c ∨ F.get? k = some c)
  sat_pre : sat hP P
  wf : Machine.MachineWf { functions := funcs, heap := hp, nextAddr := na }
    (.exec prog env₀ .stop)

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
cells framed away); the type environment is the PROGRAM's `typeDefs`
(pinned explicitly since the quorum pilot — every named Go type resolves
through it, so leaving it empty silently restricted the judgment to
programs with no named types); the METHOD TABLE is the program's
`methods`, pinned the same way and for the same reason (quorum pilot
phase 4, 2026-07-31: `enterFrame` consults it on every call — an empty
default silently restricted every surface judgment to programs with no
methods, i.e. no interface dispatch, which is exactly the fragment the
raft target lives in; the executable driver seeds `program.methods`,
`StepFn.runFunctionWithContextM`); partial correctness — `Progress` below is the companion, and
`GoSpec` bundles both. -/
def GoTriple (types : TypeEnv) (funcs : Array Func) (methods : Array MethodInfo)
    (env₀ : LocalEnv)
    (P : HProp) (prog : Stmt) (Q : HProp) : Prop :=
  ∀ (hp : Heap) (na : Nat) (hP F : Heaplet), InitialSplit P hp na hP F funcs env₀ prog →
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel env₀
          { types := types, functions := funcs, methods := methods,
            heap := hp, nextAddr := na }
          ch prog = .ok (.normal σf, ch') →
      ∃ hQ : Heaplet, (∀ k, hQ.get? k = none ∨ F.get? k = none)
        ∧ hQ.sub (heapletOf σf.heap) ∧ F.sub (heapletOf σf.heap) ∧ sat hQ Q

/-- **The progress companion**: from any admissible framed initial state,
every relation-reachable configuration is either the terminal value or can
step — never stuck. Stated over the trusted relation (`Steps`/`Step`,
Iris-free). Scope note (tracked as #24, sharpened by the unwinding arc,
`docs/2026-07-25_unwinding-arc.md`): `.panicked` — the terminal an
UNRECOVERED panic chain reaches at `.stop` — counts as stuck in this
reading, while a `.panicking` configuration mid-unwind can step (defers
run, `recover` may cancel it). So for programs whose WP is provable this
implies no reachable *unrecovered* panics — the guarantee reads "safe
execution that never aborts on a panic"; a recovered panic is an ordinary
control path inside it. -/
def Progress (types : TypeEnv) (funcs : Array Func) (methods : Array MethodInfo)
    (env₀ : LocalEnv)
    (P : HProp) (prog : Stmt) : Prop :=
  ∀ (hp : Heap) (na : Nat) (hP F : Heaplet), InitialSplit P hp na hP F funcs env₀ prog →
    ∀ (c' : Config) (σ' : ExecState),
      Steps (.exec prog env₀ .stop)
        { types := types, functions := funcs, methods := methods,
          heap := hp, nextAddr := na }
        c' σ' →
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
def GoInvariant (types : TypeEnv) (funcs : Array Func) (methods : Array MethodInfo)
    (env₀ : LocalEnv)
    (P : HProp) (prog : Stmt) (I : HProp) : Prop :=
  ∀ (hp : Heap) (na : Nat) (hP F : Heaplet), InitialSplit P hp na hP F funcs env₀ prog →
    ∀ (c' : Config) (σ' : ExecState),
      Steps (.exec prog env₀ .stop)
        { types := types, functions := funcs, methods := methods,
          heap := hp, nextAddr := na }
        c' σ' →
      ∃ hI : Heaplet, hI.sub (heapletOf σ'.heap) ∧ sat hI I

/-- Precondition strengthening for `GoInvariant` (surface-level, Iris-free):
a stronger precondition proves the same invariance. Only `sat_pre` in
`InitialSplit` mentions `P`, so this is a two-line record update. Used by
discharges whose stated precondition (e.g. "the cell holds 0") entails the
exit theorem's canonical `I ∗ P'` shape ("the cell satisfies I"). -/
theorem goInvariant_mono_pre {types funcs methods env₀ prog} {P Q I : HProp}
    (h : ∀ hp : Heaplet, sat hp P → sat hp Q)
    (hinv : GoInvariant types funcs methods env₀ Q prog I) :
    GoInvariant types funcs methods env₀ P prog I :=
  fun hp na hP F hin c' σ' hsteps =>
    hinv hp na hP F { hin with sat_pre := h hP hin.sat_pre } c' σ' hsteps

/-- **The full surface judgment**: the frame-closed triple AND progress —
"runs safely, and every terminating run delivers `Q` with the frame's
bindings intact". This is the form specs should be stated in; a triple
alone is satisfiable by a program that always crashes. -/
def GoSpec (types : TypeEnv) (funcs : Array Func) (methods : Array MethodInfo)
    (env₀ : LocalEnv)
    (P : HProp) (prog : Stmt) (Q : HProp) : Prop :=
  GoTriple types funcs methods env₀ P prog Q
    ∧ Progress types funcs methods env₀ P prog

/-- **The function-level quantified-testcase form** (v1: unary int result;
`(T, error)` returns are queued behind the interface widening —
`docs/2026-07-21_spec-space.md` §6). `GoFuncSpec funcs fid kind args P Q`
reads: *calling `fid(args)` in any admissible heap satisfying `P` — with
any frame, into any caller target cell with any prior value — terminates
only in states where the target cell received some `n` with `Q n`, beside
`P`'s leftovers, the frame's bindings intact.* The return value is observed
exactly where Go's call protocol delivers it: the caller's target cell,
written at frame exit from the callee's pinned result locations
(`Step.frameReturn`/`frameFall` copy `loadMany results` into the targets,
`Machine.lean`) — the same values the differential runner reads (its
driver `runFunctionWithContextM` runs the subject under a targetless
frame and loads the same pinned result locations from the terminal
state, `StepFn.lean`; citation corrected 2026-07-30, pre-merge audit —
the earlier text named a `collectResults` function that does not exist).
This binding point stays correct when `defer` (which may mutate named
results after `return`) enters the fragment. -/
def GoFuncSpec (types : TypeEnv) (funcs : Array Func) (methods : Array MethodInfo)
    (fid : FuncId)
    (kind : IntKind) (args : Array Expr) (P : HProp) (Q : Int → HProp) : Prop :=
  ∀ (ra : Nat) (w : GoValue),
    GoSpec types funcs methods [[("$callres", Loc.base ⟨ra⟩)]]
      (.sep (.pointsTo ra ⟨some (.int kind), w⟩) P)
      (.call #[.var "$callres"] fid args)
      (.ex fun (n : Int) =>
        .sep (.pointsTo ra ⟨some (.int kind), .int n kind⟩) (Q n))

/-! ## The sem() idiom's first-class notions (sem-adequacy arc slice 3,
2026-08-03; plan of record `docs/2026-08-03_sem-adequacy-arc.md`)

Termination and safety as INTERPRETER-level notions — no Iris, no
relation: the statement language is `execStmt` alone. `Progress` above
(relation-quantified) remains during the transition and is retired at the
arc's eviction slice. -/

/-- **Termination, interpreter-level**: the run from `σ₀` completes —
one fuel bound works for EVERY choices stream (uniform: the machine's
branching is finite — a map pick is bounded by the snapshot size, a spill
choice only sizes a capacity — so a per-stream bound lifts to a uniform
one; taking the uniform form keeps the notion a single `∃`).
"Completes" means the bounded iteration reaches `.ok` at ANY of the four
unwound terminals; which terminal — and with what state — is a
postcondition's business, not termination's. Discharge routes: kernel
evaluation at one fuel (`decide +kernel` on a primitive projection —
slice-1 spike) plus `execStmt_mono` lifts to all larger fuels. -/
def Terminates (env₀ : LocalEnv) (σ₀ : ExecState) (prog : Stmt) : Prop :=
  ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
    ∃ (out : ExecOutcome) (ch' : Choices),
      execStmt fuel env₀ σ₀ ch prog = .ok (out, ch')

/-- **Safety, interpreter-level** (the arc's replacement for the
relation-quantified `Progress`): from any admissible framed initial
state, EVERY bounded run ends `.ok` or `.fuelOut` — never stuck, never an
unrecovered panic, never `unsupported`, never an internal error. Read
with `GoTriple`: "however long you run it, it has either finished
cleanly or merely not finished yet." -/
def ProgressExec (types : TypeEnv) (funcs : Array Func)
    (methods : Array MethodInfo) (env₀ : LocalEnv)
    (P : HProp) (prog : Stmt) : Prop :=
  ∀ (hp : Heap) (na : Nat) (hP F : Heaplet), InitialSplit P hp na hP F funcs env₀ prog →
    ∀ (fuel : Nat) (ch : Choices),
      (∃ (out : ExecOutcome) (ch' : Choices),
        execStmt fuel env₀
          { types := types, functions := funcs, methods := methods,
            heap := hp, nextAddr := na }
          ch prog = .ok (out, ch'))
      ∨ execStmt fuel env₀
          { types := types, functions := funcs, methods := methods,
            heap := hp, nextAddr := na }
          ch prog = .error .fuelOut

/-- **The TOTAL surface judgment** — the sem() idiom's headline default:
triple + interpreter-level safety + proven termination from every
admissible initial state. Strictly stronger than `GoSpec`: a diverging
program satisfies a `GoSpec` vacuously on the triple side; it cannot
satisfy this. -/
def GoSpecT (types : TypeEnv) (funcs : Array Func)
    (methods : Array MethodInfo) (env₀ : LocalEnv)
    (P : HProp) (prog : Stmt) (Q : HProp) : Prop :=
  GoTriple types funcs methods env₀ P prog Q
    ∧ ProgressExec types funcs methods env₀ P prog
    ∧ ∀ (hp : Heap) (na : Nat) (hP F : Heaplet), InitialSplit P hp na hP F funcs env₀ prog →
        Terminates env₀
          { types := types, functions := funcs, methods := methods,
            heap := hp, nextAddr := na }
          prog

/-- **Relation-Progress transports to interpreter-side safety** (the
sem-adequacy slice-3 kit's surface-level theorem): the relation-quantified
`Progress` implies `ProgressExec`. `InitialSplit`'s `wf` field supplies
the machine well-formedness the ∀-choices kit needs (`MachineWf` at the
typeless seed transfers to the seeded state definitionally on the loc
components; the map-iteration typing component is trivially true at the
initial configuration, which carries no `mapIterK`), and
`execStmt fuel env₀ σ ch prog = execStmtLoop fuel σ (.exec prog env₀
.stop) ch` holds definitionally. -/
theorem progressExec_of_progress {types : TypeEnv} {funcs : Array Func}
    {methods : Array MethodInfo} {env₀ : LocalEnv} {P : HProp} {prog : Stmt}
    (h : Progress types funcs methods env₀ P prog) :
    ProgressExec types funcs methods env₀ P prog := by
  intro hp na hP F hin fuel ch
  obtain ⟨hs, hc, _⟩ := hin.wf
  have hwf : Machine.MachineWf
      { types := types, functions := funcs, methods := methods,
        heap := hp, nextAddr := na } (.exec prog env₀ .stop) :=
    ⟨hs, hc, rfl⟩
  exact execStmtLoop_ok_or_fuelOut (h hp na hP F hin) hwf fuel ch

/-- **The user-form specification — ⟨P terminates⟩ ∧ ⟨pre⟩ → post — as a
genuinely DERIVED case** (statement corrected at the 2026-08-04
sub-branch audit: the first version was an eta-expansion of `GoSpecT.1`
that never touched `Terminates`, so the plan-of-record's "the sketch
form is a supported case" was NOT the checked fact it claimed to be).
What a total judgment actually yields at every admissible initial state:
the run COMPLETES past some fuel bound on every choices stream, and any
completion at the `.normal` terminal satisfies the postcondition beside
the intact frame. The completion outcome is quantified, not pinned to
`.normal` — `Terminates` deliberately does not choose the terminal (a
bare `return`-ending program completes at `.returned`); the driver
statements of the headline family end `.normal`, and their retrofits
will pin that per-program, not here. -/
theorem goSpecT_terminates_and_post {types funcs methods env₀}
    {P Q : HProp} {prog : Stmt}
    (h : GoSpecT types funcs methods env₀ P prog Q) :
    ∀ (hp : Heap) (na : Nat) (hP F : Heaplet),
      InitialSplit P hp na hP F funcs env₀ prog →
      (∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        ∃ (out : ExecOutcome) (ch' : Choices),
          execStmt fuel env₀
            { types := types, functions := funcs, methods := methods,
              heap := hp, nextAddr := na } ch prog = .ok (out, ch'))
      ∧ (∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
          execStmt fuel env₀
              { types := types, functions := funcs, methods := methods,
                heap := hp, nextAddr := na }
              ch prog = .ok (.normal σf, ch') →
          ∃ hQ : Heaplet, (∀ k, hQ.get? k = none ∨ F.get? k = none)
            ∧ hQ.sub (heapletOf σf.heap) ∧ F.sub (heapletOf σf.heap)
            ∧ sat hQ Q) :=
  fun hp na hP F hin =>
    ⟨h.2.2 hp na hP F hin, fun fuel ch σf ch' hrun =>
      h.1 hp na hP F hin fuel ch σf ch' hrun⟩

end GoLean.Surface
