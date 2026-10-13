import GoLean.GoCore.StepFn
import GoLean.GoCore.Seed
import GoLean.GoCore.SeedPool
import GoLean.GoCore.StateWf
import GoLean.GoCore.ExecutionStatement

/-!
# The SETUP EQUATIONS — statements (the logic team's G-R1–G-R4, 2026-10-05)

[AGENT worker, lane `core/setup-equations-1005`] 2026-10-05, under [USER] Mike 2026-10-05 «(1) Go
ahead» (relayed by the [AGENT] coordinator; scheduled after train r66). The request, verbatim:
`docs/2026-10-05_note-from-logic-team-setup-equations.md`; the requesters' design: golean-logic
branch `design/globals-init-1005`, `docs/2026-10-05_globals-init-design.md` §3.1, §5–§6, §9. The
lane's note: `docs/2026-10-05_setup-equations.md`.

Every statement here is a `def <name>_stmt : Prop` (the `ExecutionStatement`/`PoolStatement`
grain: it elaborates with no proof). G-R1–G-R3 are PROVED in `SetupSound.lean` as
`theorem <name> : <name>_stmt`, the statements unchanged, and pinned WRITTEN OUT in
`BridgeSet.lean` (RE-PIN 12, rows 512–520). G-R4 (`runInitConfig_eq_execStmtLoop_stmt`) was
STATED first and sent to the logic team for review (the [AGENT] coordinator's committed reply in
the request note); APPROVED 2026-10-05 with four answers (the golean-logic coordinator, by
cross-session message, relayed by the [AGENT] coordinator; verbatim in the lane's note §3): (a) the
no-blocked premise DROPPED, (b) the guard spelling `initPrintRefusal? c' = none` and the bound
`n ≤ fuel` kept, (c) the `run_*_iff`-style corollaries for `runInitConfig` added, (d) the
`runPkgInitM`/`markInitPhase` wrapper equation added. Phase 3 proves them all (`SetupSound.lean`;
RE-PIN 13, rows 521–527).

These internal correspondence statements preserve the setup semantics.
Their empty-store specializations are checked as `example`s at the end of
`SetupSound.lean`; the former public equation API was retired with the
relational-surface refactor. `zeroCell` reads `Store.alloc`'s result on a zero
value and is used to state the seeding equation.

The controls at the end are `rfl` after `#eval` (the #eval-first rule): a one-global program with
an initializer, and the print position where the two loops of G-R4 DISAGREE (its premise is
load-bearing).
-/

namespace GoLean.GoCore.SetupStatement

open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.GoCore.ExecutionStatement (Prefix Blocked Finish ZeroCost)

/-! ## G-R2 — seeding -/

/-- The ZERO CELL of a package-level variable: its type's zero value (`defaultValue`) at its
declared type. A zero value is already normal at its type (`defaultValue_isNormal`,
`MachineSound.lean`), so `Store.alloc`'s normalization at seeding returns it unchanged — the seeded
cell IS this cell (`seedGlobals_cells`); the design's `GlobalsZero` names the same cell
(`.value g.typ (zero g.typ)`, golean-logic design §3.1). -/
def zeroCell (ctx : ProgramCtx) (g : GlobalDef) : Except Stop HeapCell :=
  (HeapCell.value g.typ ·) <$> defaultValue ctx g.typ

/-- **G-R2, the seeding equation.** Seeding from the fresh store IS the zero cells of the globals, in
order — global `i` at `.base ⟨i⟩`, a dense heap's index being its address — as ONE equation over
`Except`: a global whose zero value is refused (`defaultValue` on an unsupported or interface type)
refuses seeding with that refusal, in global order; otherwise the seeded store's heap is exactly
the list of zero cells. The address check inside `seedGlobals` (`loc != .base ⟨i⟩`) never fires
from the fresh store — that is part of what the equation says. -/
def seedGlobals_cells_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (globals : Array GlobalDef),
    seedGlobals ctx {} globals
      = (fun cells => ({ heap := cells.toArray } : Store)) <$> globals.toList.mapM (zeroCell ctx)

/-- G-R2, the pointwise reading: on a successful seeding, global `i` is at `.base ⟨i⟩`, holding its
type's zero value at its declared type. -/
def seedGlobals_cell_stmt : Prop :=
  ∀ {ctx : ProgramCtx} {globals : Array GlobalDef} {s₀ : Store},
    seedGlobals ctx {} globals = .ok s₀ →
    ∀ (i : Nat) (hi : i < globals.size), ∃ z : GoValue,
      defaultValue ctx globals[i].typ = .ok z
        ∧ Heap.lookup s₀.heap (.base ⟨i⟩) = some (.value globals[i].typ z)

/-- G-R2: a seeded heap has exactly one cell per global (so `globals.size ≤ σ.heap.size` at the
seeded store — the design's §3.3 conjunct at its base). -/
def seedGlobals_heap_size_stmt : Prop :=
  ∀ {ctx : ProgramCtx} {globals : Array GlobalDef} {s₀ : Store},
    seedGlobals ctx {} globals = .ok s₀ → s₀.heap.size = globals.size

/-- **G-R2, `seedGlobals_wf`.** A seeded store is well-formed — UNCONDITIONALLY: a zero value carries
no location (`defaultValue_locSup`) and is normal at its type (`defaultValue_isNormal`). So the
`StateWf` check `runProgramSetupM` runs after seeding can never fire, and the general setup equation
(G-R1) carries no `StateWf` premise: the design's `SeedPlan` reduces to «`seedGlobals` succeeds». -/
def seedGlobals_wf_stmt : Prop :=
  ∀ {ctx : ProgramCtx} {globals : Array GlobalDef} {s₀ : Store},
    seedGlobals ctx {} globals = .ok s₀ → StateWf ctx s₀

/-! ## G-R1 — the general setup equation -/

/-- **G-R1, the general setup equation** — `runProgramSetup_noInit`'s shape with its two
program-level premises (`globals = #[]`, no `$pkginit`) replaced by the two phases' RESULTS: the
subject found by name, its arity matched, the type table's reserved prefix in place; then
SEEDING (`seedGlobals` from the empty store — its `StateWf` check is discharged by `seedGlobals_wf`,
so it is not a premise), PACKAGE INITIALIZATION (`runPkgInitM` over the seeded store, consuming from
the tape), the ARGUMENT BIND (`bindParams` over the POST-INIT store `s₁`) and the RESULT
DECLARATIONS (`allocDecls`, `pinResultLocs`), as one rewrite. The entry configuration runs the
body in the frame environment under a targetless barrier frame naming the subject, over the store
after binding, with the tape the init phase left. The layout of `s₃` over `s₁` is
`setup_lookup_arg_from` / `_result_from`, `setup_resultLocs_from`, `setup_heap_size_from`;
`runProgramSetup_noInit` is this at `globals = #[]` and no `$pkginit` (`seedGlobals_nil`,
`runPkgInitM_none`). -/
def runProgramSetup_init_stmt : Prop :=
  ∀ {fuel : Nat} {program : Program} {name : String} {args : Array GoValue} {choices : Choices}
    {func : Func} {s₀ s₁ : Store} {choices₁ : Choices} {env frameEnv : LocalEnv} {s₂ s₃ : Store}
    {resultLocs : List Loc},
    findFunctionIn? program.funcs ⟨name⟩ = some func → func.args.size = args.size →
    program.typeDefs.hasReservedPrefix = true →
    seedGlobals ⟨program⟩ {} program.globals = .ok s₀ →
    runPkgInitM ⟨program⟩ fuel s₀ choices = .ok (s₁, choices₁) →
    bindParams ⟨program⟩ [] s₁ func.args.toList args.toList = .ok (env, s₂) →
    allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃) →
    pinResultLocs frameEnv func.results.toList = .ok resultLocs →
    runProgramSetupM fuel program name args choices
      = .ok (⟨program⟩, .exec func.body frameEnv (.frame [] [] [] [] .stop func.id), s₃, resultLocs,
          choices₁)

/-! ## G-R3 — the entry layout from a pre-bind store

Layout over an arbitrary pre-bind store `s₁` (the post-init store): the cells
are `entrySlot s₁ k = .base ⟨s₁.heap.size + k⟩` (`Machine.lean`, the C4 D8 layout
function) — the same slots frame entry allocates (`frameEntry_lookup_arg`/`_result`). -/

/-- **G-R3, the argument layout.** Parameter `i` is bound to the `i`-th cell the entry allocates from
`s₁`, under the signature's ids pairwise distinct. `setup_lookup_arg` is this at `s₁ = {}`. -/
def setup_lookup_arg_from_stmt : Prop :=
  ∀ {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv}
    {s₁ s₂ s₃ : Store},
    bindParams ⟨program⟩ [] s₁ func.args.toList args.toList = .ok (env, s₂) →
    allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃) →
    namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true →
    ∀ (i : Nat) (hi : i < func.args.size),
      LocalEnv.lookup frameEnv func.args[i].id = some (entrySlot s₁ i)

/-- **G-R3, the result layout.** Result `j` is bound to the cell after all the parameters.
`setup_lookup_result` is this at `s₁ = {}`. -/
def setup_lookup_result_from_stmt : Prop :=
  ∀ {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv}
    {s₁ s₂ s₃ : Store},
    bindParams ⟨program⟩ [] s₁ func.args.toList args.toList = .ok (env, s₂) →
    allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃) →
    namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true →
    ∀ (j : Nat) (hj : j < func.results.size),
      LocalEnv.lookup frameEnv func.results[j].id = some (entrySlot s₁ (func.args.size + j))

/-- **G-R3, the pinned result locations** are exactly the result cells, in order.
`setup_resultLocs` is this at `s₁ = {}`. -/
def setup_resultLocs_from_stmt : Prop :=
  ∀ {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv}
    {s₁ s₂ s₃ : Store} {resultLocs : List Loc},
    bindParams ⟨program⟩ [] s₁ func.args.toList args.toList = .ok (env, s₂) →
    allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃) →
    namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true →
    pinResultLocs frameEnv func.results.toList = .ok resultLocs →
    resultLocs = (List.range func.results.size).map (fun j => entrySlot s₁ (func.args.size + j))

/-- **G-R3, the heap after the bind** holds the pre-bind store's cells, then the parameter and result
cells. `setup_heap_size` is this at `s₁ = {}`. -/
def setup_heap_size_from_stmt : Prop :=
  ∀ {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv}
    {s₁ s₂ s₃ : Store},
    bindParams ⟨program⟩ [] s₁ func.args.toList args.toList = .ok (env, s₂) →
    allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃) →
    s₃.heap.size = s₁.heap.size + func.args.size + func.results.size

/-! ## G-R4 — the init loop and the entry loop

The premise shared by every statement of this section — NO PRINT POSITION REACHED: for every
configuration the run reaches within the fuel (`Prefix ctx n σ c ch ls σ' c' ch'`, `n ≤ fuel` —
the configuration at step `fuel` IS inspected by the guard, before the fuel-out), the init-phase
guard is silent, `initPrintRefusal? c' = none` (equivalently `printOut? c' = none`; the guard reads
nothing else). The design's init mode carries exactly this side condition on `Prim.step` (golean-logic
design §5.2); the logic team's answer (b) keeps the spelling and the bound. -/

/-- **G-R4 (approved as stated minus the no-blocked premise; answer (a)).** `runInitConfig` is
`execStmtLoop` with ONE extra guard — the init-phase print refusal, consulted before the fuel match
on every configuration that is neither `.next .stop` nor blocked — so under the no-print premise the
two loops are EQUAL. No premise on blocked configurations: both loops classify a blocked
configuration as `.deadlock` before any guard, and `stepFn` itself throws on one, so no `Prefix`
passes through a blocked configuration — the equation holds without it (the request had named it;
dropped at the requesters' answer (a): «the theorem is stronger and cleaner without it»). -/
def runInitConfig_eq_execStmtLoop_stmt : Prop :=
  ∀ {ctx : ProgramCtx} {fuel : Nat} {σ : Store} {c : Config} {ch : Choices},
    (∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n σ c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) →
    runInitConfig ctx fuel σ c ch = execStmtLoop ctx fuel σ c ch

/-! ### The `run_*_iff` corollaries for the init loop (answer (c))

`ExecutionStatement.lean`'s `run_ok_iff` / `run_panic_iff` / `run_deadlock_iff` / `run_fuelOut_iff`
for `runInitConfig`, under the no-print premise — the same right-hand sides (`Prefix`, `Finish`,
`ZeroCost`), so the logic team's init-prefix adequacy composes with the existing `Prefix`/`Finish`
statements through them. Each is G-R4 followed by the sequential statement. -/

/-- Normal completion of the init loop: a prefix of length `n ≤ fuel` to `.next .stop` (cost 0). -/
def runInitConfig_ok_iff_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s sf : Store) (c : Config) (ch chf : Choices),
    (∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) →
    (runInitConfig ctx fuel s c ch = .ok (sf, chf) ↔
      ∃ n, n ≤ fuel ∧ ∃ ls, Prefix ctx n s c ch ls sf (.next .stop) chf)

/-- The init loop's panic terminal (an initializer's unrecovered panic kills the program before
`main`): prefix length plus the abort's cost 1 within the fuel; `markInitPhase` leaves it unmarked. -/
def runInitConfig_panic_iff_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices) (t : String),
    (∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) →
    (runInitConfig ctx fuel s c ch = .error (.terminal (.panic t)) ↔
      ∃ (n : Nat) (ls : List StepLabel) (sf : Store) (cf : Config) (chf ch'' : Choices)
        (rec : List PickRecord),
        n + 1 ≤ fuel ∧ Prefix ctx n s c ch ls sf cf chf ∧
          Finish ctx sf cf chf rec (.aborted t sf ch'') 1)

/-- The init loop's deadlock: a blocked endpoint at `n ≤ fuel` (cost 0). -/
def runInitConfig_deadlock_iff_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices),
    (∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) →
    (runInitConfig ctx fuel s c ch = .error (.terminal .deadlock) ↔
      ∃ n, n ≤ fuel ∧ ∃ (ls : List StepLabel) (sf : Store) (cf : Config) (chf : Choices),
        Prefix ctx n s c ch ls sf cf chf ∧ Finish ctx sf cf chf [] (.deadlock sf chf) 0)

/-- The init loop's fuel-out: the fixed tape's prefix of length exactly `fuel`, ending at a
configuration that is not zero-cost (`markInitPhase` leaves `fuelOut` unmarked — an init-phase
fuel exhaustion is indistinguishable from the subject's by design). -/
def runInitConfig_fuelOut_iff_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices),
    (∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) →
    (runInitConfig ctx fuel s c ch = .error .fuelOut ↔
      ∃ (ls : List StepLabel) (sf : Store) (cf : Config) (chf : Choices),
        Prefix ctx fuel s c ch ls sf cf chf ∧ ¬ ZeroCost cf)

/-! ### The `runPkgInitM` wrapper (answer (d))

`runPkgInitM` with a `$pkginit` PRESENT, in terms of `runInitConfig` on the init configuration —
the link from G-R1's premise (`runPkgInitM ⟨program⟩ fuel s₀ choices = .ok (s₁, choices₁)`) to
`runInitConfig`, and through G-R4 to `execStmtLoop`. The absent-initializer
case is an internal helper in `SetupSound.lean`. -/

/-- **The wrapper equation.** With `$pkginit` found, nullary and resultless (the design's
`Definition ctx hI [] [] Dinit`), `runPkgInitM` IS `runInitConfig` on the init configuration — the
body under a targetless barrier frame naming `$pkginit`, the empty environment — with the error
re-labelled by `markInitPhase` (`stuck`/`unsupported`/`internal` get the `package init:` prefix;
`fuelOut` and the terminals pass unmarked). -/
def runPkgInitM_some_stmt : Prop :=
  ∀ {ctx : ProgramCtx} {fuel : Nat} {s : Store} {ch : Choices} {initF : Func},
    findFunctionIn? ctx.functions pkgInitFuncId = some initF →
    initF.args.size = 0 → initF.results.size = 0 →
    runPkgInitM ctx fuel s ch
      = (runInitConfig ctx fuel s (.exec initF.body [] (.frame [] [] [] [] .stop initF.id)) ch).mapError
          markInitPhase

/-- The wrapper's SUCCESS link — the form G-R1's premise composes with: `runPkgInitM` succeeds with
`(s₁, ch₁)` iff `runInitConfig` on the init configuration does (`markInitPhase` touches errors
only). -/
def runPkgInitM_ok_iff_stmt : Prop :=
  ∀ {ctx : ProgramCtx} {fuel : Nat} {s s₁ : Store} {ch ch₁ : Choices} {initF : Func},
    findFunctionIn? ctx.functions pkgInitFuncId = some initF →
    initF.args.size = 0 → initF.results.size = 0 →
    (runPkgInitM ctx fuel s ch = .ok (s₁, ch₁) ↔
      runInitConfig ctx fuel s (.exec initF.body [] (.frame [] [] [] [] .stop initF.id)) ch
        = .ok (s₁, ch₁))

/-! ## Controls (`#eval` first — the probe's results are what the `rfl`s below pin) -/

section Controls

/-- The initializer of the control program: `g = 7` (global cell 0). -/
def initControlBody : Stmt := .assign (.addr (.global 0)) (.intLit 7 .int)

/-- `var g int`; `func init() { g = 7 }`; `func F() (z int) { z = g }` — one global, one
initializer writing it, the subject reading it. -/
def initControl : Program := {
  funcs := #[
    { id := ⟨"F"⟩, args := #[], results := #[{ id := 1, typ := .int }],
      body := .assign (.var 1) (.deref (.global 0) .int) },
    { id := pkgInitFuncId, args := #[], results := #[], body := initControlBody } ],
  globals := #[{ name := "g", typ := .int }] }

/-- The seeded store of the control: ONE zero cell at `.base ⟨0⟩` (the shape `seedGlobals_cells`
states, by evaluation). -/
example : seedGlobals ⟨initControl⟩ {} initControl.globals
    = .ok { heap := #[.value .int (.int 0 .int)] } := rfl

set_option maxRecDepth 8192 in
/-- The whole run: the initializer's write is what the subject reads. Fuel 12 is the least that
completes (each phase is bounded separately: the initializer takes 10 steps, the subject 12); the
elaborator's default recursion depth is too small for this one reduction, so it is raised locally. -/
example : runProgramM 12 initControl "F" #[] = .ok { values := #[.int 7 .int] } := rfl

/-- The init configuration `runPkgInitM` builds for the control. -/
def initControlConfig : Config := .exec initControlBody [] (.frame [] [] [] [] .stop pkgInitFuncId)

/-- G-R4 at the control, positive: no print position on the initializer's path, so the init
loop and the entry loop AGREE — at the fuel the body needs (10
steps: both reach `.next .stop` with the written cell), at fuel 9 (both fuel out) and at 0. -/
example : runInitConfig ⟨initControl⟩ 10 { heap := #[.value .int (.int 0 .int)] } initControlConfig []
    = execStmtLoop ⟨initControl⟩ 10 { heap := #[.value .int (.int 0 .int)] } initControlConfig [] :=
  rfl
example : runInitConfig ⟨initControl⟩ 10 { heap := #[.value .int (.int 0 .int)] } initControlConfig []
    = .ok ({ heap := #[.value .int (.int 7 .int)] }, []) := rfl
example : runInitConfig ⟨initControl⟩ 9 { heap := #[.value .int (.int 0 .int)] } initControlConfig []
    = execStmtLoop ⟨initControl⟩ 9 { heap := #[.value .int (.int 0 .int)] } initControlConfig [] :=
  rfl
example : runInitConfig ⟨initControl⟩ 9 { heap := #[.value .int (.int 0 .int)] } initControlConfig []
    = .error .fuelOut := rfl
example : runInitConfig ⟨initControl⟩ 0 { heap := #[.value .int (.int 0 .int)] } initControlConfig []
    = execStmtLoop ⟨initControl⟩ 0 { heap := #[.value .int (.int 0 .int)] } initControlConfig [] :=
  rfl

/-- The wrapper at the control: `runPkgInitM` IS `runInitConfig` on the init configuration (success
passes through `markInitPhase` unmarked). -/
example : runPkgInitM ⟨initControl⟩ 10 { heap := #[.value .int (.int 0 .int)] } []
    = runInitConfig ⟨initControl⟩ 10 { heap := #[.value .int (.int 0 .int)] } initControlConfig [] :=
  rfl
example : runPkgInitM ⟨initControl⟩ 10 { heap := #[.value .int (.int 0 .int)] } []
    = .ok ({ heap := #[.value .int (.int 7 .int)] }, []) := rfl

/-- A `println(1)` at its apply position: the one operand delivered, no targets, nothing pending. -/
def printPosition : Config := .retV (.int 1 .int) (.stmtOpK (.print true) 0 [] [] [] .stop)

/-- G-R4 at the control, NEGATIVE — the no-print premise is load-bearing: at the print position the
init loop REFUSES by name (the init-phase refusal, `initPrintRefusal?`) while the entry loop steps
through to `.next .stop` (the print's bytes ride the step label, which this driver drops — exactly
what the init guard exists to refuse). The two sides differ, so no premise-free equation holds. -/
example : initPrintRefusal? printPosition = some (Stop.unsupported "print/println during package initialization: the init phase runs on the sequential driver, which has no output event channel (the pool driver folds StepEvent.out) — refused rather than dropping the bytes (stdlib slice 3; row builtins/print/in-init)") :=
  rfl
example : runInitConfig ⟨initControl⟩ 4 {} printPosition []
    = .error ((initPrintRefusal? printPosition).getD .fuelOut) := rfl
example : execStmtLoop ⟨initControl⟩ 4 {} printPosition [] = .ok ({}, []) := rfl

end Controls

/-! ## The SEEDED entry — S1–S6 (slice A of the seeded-heap design, 2026-10-12)

`docs/2026-10-09_seeded-heap-design.md` §4, [USER] Mike 2026-10-12 (GO; D4: no runtime `StateWf`
re-assert — S5 is the check). Names are the owed BridgeSet rows (RE-PIN 17). ADDITIVE: every earlier
statement is unchanged. `b := s₁.heap.size` is the post-init allocator bound, `n := seed.size`; the
seed's slot `k` is `.base ⟨b + k⟩ = entrySlot s₁ k`. RE-PIN 19 (2026-10-12) re-pinned the three S6
statements only: `SeededReadout` carries `base` (= `b`), read off the setup's slots by `seedBase`. -/

/-- **S1, the seeded setup equation** (G-R1's sibling, the same premise shape, NO `StateWf` premise —
D4): under the ten premises, the seeded entry IS the entry configuration over the store after
binding, with the seed slots and the tape the init phase left. -/
def runProgramSetupSeeded_init_stmt : Prop :=
  ∀ {fuel : Nat} {program : Program} {name : String} {seed : Array SeedCell} {args : Array SeedArg}
    {choices : Choices} {func : Func} {s₀ s₁ : Store} {choices₁ : Choices} {sS : Store}
    {slots : Array Loc} {vals : Array GoValue} {env frameEnv : LocalEnv} {s₂ s₃ : Store}
    {resultLocs : List Loc},
    findFunctionIn? program.funcs ⟨name⟩ = some func → func.args.size = args.size →
    program.typeDefs.hasReservedPrefix = true →
    seedGlobals ⟨program⟩ {} program.globals = .ok s₀ →
    runPkgInitM ⟨program⟩ fuel s₀ choices = .ok (s₁, choices₁) →
    seedCells ⟨program⟩ s₁ seed = .ok (sS, slots) →
    resolveSeedArgs program.typeDefs s₁.heap.size seed func.args args = .ok vals →
    bindParams ⟨program⟩ [] sS func.args.toList vals.toList = .ok (env, s₂) →
    allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃) →
    pinResultLocs frameEnv func.results.toList = .ok resultLocs →
    runProgramSetupSeededM fuel program name seed args choices
      = .ok (⟨program⟩, .exec func.body frameEnv (.frame [] [] [] [] .stop func.id), s₃, resultLocs,
          slots, choices₁)

/-- **S2, seed cell `k` at its slot**: the slot list names `.base ⟨b + k⟩`, the cell's value resolves
and normalizes at its declared type, and the seeded store holds that normal value there. -/
def seedCells_cell_stmt : Prop :=
  ∀ {ctx : ProgramCtx} {s₁ : Store} {seed : Array SeedCell} {sS : Store} {locs : Array Loc},
    seedCells ctx s₁ seed = .ok (sS, locs) → ∀ (k : Nat) (hk : k < seed.size),
      locs[k]? = some (.base ⟨s₁.heap.size + k⟩) ∧
      ∃ v w, resolveSeedValue ctx.types s₁.heap.size seed seed[k].typ seed[k].value = .ok v
        ∧ normalizeValueForTy ctx seed[k].typ v = .ok w
        ∧ Heap.lookup sS.heap (.base ⟨s₁.heap.size + k⟩) = some (.value seed[k].typ w)

/-- **S2, the frame below `b`**: seeding touches no cell of the post-init store. -/
def seedCells_frame_stmt : Prop :=
  ∀ {ctx : ProgramCtx} {s₁ : Store} {seed : Array SeedCell} {sS : Store} {locs : Array Loc},
    seedCells ctx s₁ seed = .ok (sS, locs) → ∀ j, j < s₁.heap.size → sS.heap[j]? = s₁.heap[j]?

/-- **S2, the slot list**: the seed's slots are `b, b + 1, …, b + n − 1`, in order. -/
def seedCells_locs_stmt : Prop :=
  ∀ {ctx : ProgramCtx} {s₁ : Store} {seed : Array SeedCell} {sS : Store} {locs : Array Loc},
    seedCells ctx s₁ seed = .ok (sS, locs) →
    locs = ((List.range seed.size).map (fun k => Loc.base ⟨s₁.heap.size + k⟩)).toArray

/-- **S3, the heap size**: exactly `n` cells are added. The entry layout is then G-R3 at the
pre-bind store `sS` (`setup_lookup_arg_from` and its siblings apply verbatim with `s₁ := sS`). -/
def seedCells_heap_size_stmt : Prop :=
  ∀ {ctx : ProgramCtx} {s₁ : Store} {seed : Array SeedCell} {sS : Store} {locs : Array Loc},
    seedCells ctx s₁ seed = .ok (sS, locs) → sS.heap.size = s₁.heap.size + seed.size

/-- **S4, empty-seed erasure** — ONE `Except` equation, errors included: the seeded entry with no
cells and scalar arguments IS `runProgramSetupM` (with an empty slot list). What ties the seeded
entry to G-R1 and `runProgramSetup_noInit`. -/
def runProgramSetupSeeded_empty_stmt : Prop :=
  ∀ (fuel : Nat) (program : Program) (name : String) (args : Array GoValue) (choices : Choices),
    runProgramSetupSeededM fuel program name #[] (args.map SeedArg.scalar) choices
      = (fun (pctx, c, s, locs, ch) => (pctx, c, s, locs, (#[] : Array Loc), ch)) <$>
          runProgramSetupM fuel program name args choices

/-- **S5, `seed_wf`**: seeding preserves state well-formedness (phase 1 allocates zero values,
phase 2 stores values whose every location the resolver bounded by `b + n`). -/
def seedCells_wf_stmt : Prop :=
  ∀ {ctx : ProgramCtx} {s₁ : Store} {seed : Array SeedCell} {sS : Store} {locs : Array Loc},
    StateWf ctx s₁ → seedCells ctx s₁ seed = .ok (sS, locs) → StateWf ctx sS

/-- **S5, the bound store**: from a well-formed post-init store, through seeding, argument
resolution, parameter binding and result allocation, the entry store is well-formed. The one
premise beyond the design's: every SCALAR argument is loc-free ([AGENT] refinement, D5 — scalars
pass the core unchecked; the CLI's `entryArgValues` produces only ints and bools, which are). -/
def runProgramSetupSeeded_wf_stmt : Prop :=
  ∀ {ctx : ProgramCtx} {s₁ sS : Store} {seed : Array SeedCell} {slots : Array Loc}
    {params : Array Param} {args : Array SeedArg} {vals : Array GoValue} {env frameEnv : LocalEnv}
    {s₂ s₃ : Store} {results : List Param},
    StateWf ctx s₁ → (∀ v, SeedArg.scalar v ∈ args → GoValue.locSup v = 0) →
    seedCells ctx s₁ seed = .ok (sS, slots) →
    resolveSeedArgs ctx.types s₁.heap.size seed params args = .ok vals →
    bindParams ctx [] sS params.toList vals.toList = .ok (env, s₂) →
    allocDecls ctx env s₂ results = .ok (frameEnv, s₃) →
    StateWf ctx s₃

/-- **S6, the seeded run**: the definition, unfolded (the `runProgramM` shape): the seeded setup,
the seed's base read off its slot list (`seedBase` — RE-PIN 19: the readout carries `base`, the
post-init bound the cells were placed from, so a consumer of the readout needs no second setup),
the run, the results, the final seed cells. -/
def runProgramSeededM_eq_stmt : Prop :=
  ∀ (fuel : Nat) (program : Program) (name : String) (seed : Array SeedCell) (args : Array SeedArg)
    (choices : Choices),
    runProgramSeededM fuel program name seed args choices
      = (runProgramSetupSeededM fuel program name seed args choices >>=
          fun (pctx, c₀, s₃, resultLocs, slots, choices₁) =>
            seedBase slots >>= fun base =>
              runConfig pctx fuel s₃ c₀ choices₁ >>= fun (sF, _) =>
                loadMany pctx sF resultLocs >>= fun values =>
                  loadMany pctx sF slots.toList >>= fun finals =>
                    pure { readout := { values := values.toArray }, base := base,
                           seedFinal := finals.toArray })

/-- **S6 on the pool: erasure.** With no cells and scalar arguments the seeded pool entry IS
`runProgramPoolOutM` with base 0 (no slot — `seedBase #[]`) and an empty final seed (one `Except`
equation, errors and output included). -/
def runProgramPoolSeeded_empty_stmt : Prop :=
  ∀ (fuel : Nat) (program : Program) (name : String) (args : Array GoValue) (choices : Choices),
    runProgramPoolSeededOutM fuel program name #[] (args.map SeedArg.scalar) choices
      = (fun r : Readout => ({ readout := r, base := 0, seedFinal := #[] } : SeededReadout)) <$>
          runProgramPoolOutM fuel program name args choices

/-- **S6, erasure of the run**: with no cells and scalar arguments the seeded run IS `runProgramM`
with base 0 and an empty final seed. -/
def runProgramSeededM_empty_stmt : Prop :=
  ∀ (fuel : Nat) (program : Program) (name : String) (args : Array GoValue) (choices : Choices),
    runProgramSeededM fuel program name #[] (args.map SeedArg.scalar) choices
      = (fun r : Readout => ({ readout := r, base := 0, seedFinal := #[] } : SeededReadout)) <$>
          runProgramM fuel program name args choices

/-! ## Controls for the seeded entry (`#eval` first — the probe's results are what the `rfl`s pin) -/

section SeededControls

/-- A context with no program text and the bare reserved type table. -/
def seedCtx0 : ProgramCtx := ⟨{ funcs := #[] }⟩

/-- `type Node struct { next *Node }` at table index 2 (after the two reserved entries). -/
def seedNodeTypes : TypeEnv := TypeEnv.reserved.push (⟨"main.Node"⟩, .struct #[⟨"next", .pointer (.defined 2), false⟩])

def seedCtxNode : ProgramCtx := ⟨{ funcs := #[], typeDefs := seedNodeTypes }⟩

/-- An `int` cell holding 41 and a `*int` cell pointing at it. -/
def seedA : Array SeedCell := #[⟨.int .int, .int 41⟩, ⟨.pointer (.int .int), .ref 0 []⟩]

/-- From the empty store: cell 0 at base 0, the pointer resolved to it. -/
example : seedCells seedCtx0 {} seedA
    = .ok ({ heap := #[.value (.int .int) (.int 41 .int),
                        .value (.pointer (.int .int)) (.addr (.base ⟨0⟩))] },
           #[.base ⟨0⟩, .base ⟨1⟩]) := rfl

/-- From a one-cell store (`b = 1`): the same seed lands at bases 1 and 2 and the pointer resolves
seed-RELATIVE, to base 1 — the cell below is untouched. -/
example : seedCells seedCtx0 { heap := #[.value .bool (.bool true)] } seedA
    = .ok ({ heap := #[.value .bool (.bool true),
                        .value (.int .int) (.int 41 .int),
                        .value (.pointer (.int .int)) (.addr (.base ⟨1⟩))] },
           #[.base ⟨1⟩, .base ⟨2⟩]) := rfl

/-- A path into an array cell: `&c0[1]`. -/
example : seedCells seedCtx0 {} #[⟨.array 2 (.int .int), .array [.int 5, .int 7]⟩,
                                   ⟨.pointer (.int .int), .ref 0 [.index 1]⟩]
    = .ok ({ heap := #[.value (.array 2 (.int .int)) (.array #[.int 5 .int, .int 7 .int]),
                        .value (.pointer (.int .int)) (.addr (.index (.base ⟨0⟩) 1))] },
           #[.base ⟨0⟩, .base ⟨1⟩]) := rfl

/-- A CYCLE between two struct cells, and a pointer to a field (`&c0.next`): the very locations the
machine's own `&c.f` evaluates to. -/
example : seedCells seedCtxNode {} #[⟨.defined 2, .struct [("next", .ref 1 [])]⟩,
                                      ⟨.defined 2, .struct [("next", .ref 0 [])]⟩,
                                      ⟨.pointer (.pointer (.defined 2)), .ref 0 [.field "next"]⟩]
    = .ok ({ heap := #[.value (.defined 2) (.struct ⟨"main.Node"⟩ #[("next", .addr (.base ⟨1⟩))]),
                        .value (.defined 2) (.struct ⟨"main.Node"⟩ #[("next", .addr (.base ⟨0⟩))]),
                        .value (.pointer (.pointer (.defined 2)))
                          (.addr (.field (.base ⟨0⟩) ⟨"main.Node"⟩ "next"))] },
           #[.base ⟨0⟩, .base ⟨1⟩, .base ⟨2⟩]) := rfl

/-- The refusal catalogue (design §3), each BY NAME, each naming its cell. -/
example : seedCells seedCtx0 {} #[⟨.int .int, .ref 5 []⟩]
    = .error (.stuck "seed: cell 0: ref at type int — a pointer type expected") := rfl
example : seedCells seedCtx0 {} #[⟨.pointer (.int .int), .ref 5 []⟩]
    = .error (.stuck "seed: cell 0: ref to cell 5 out of range (1 cells)") := rfl
example : seedCells seedCtx0 {} #[⟨.int .int8, .int 300⟩]
    = .error (.stuck "seed: cell 0: int 300 out of range for int8") := rfl
example : seedCells seedCtx0 {} #[⟨.array 2 (.int .int), .array [.int 5]⟩]
    = .error (.stuck "seed: cell 0: expected array(2), got 1 element(s)") := rfl
example : seedCells seedCtxNode {} #[⟨.defined 2, .struct []⟩]
    = .error (.stuck "seed: cell 0: struct main.Node: missing field next") := rfl
example : seedCells seedCtxNode {} #[⟨.defined 2, .struct [("next", .nil), ("next", .nil)]⟩]
    = .error (.stuck "seed: cell 0: struct main.Node: duplicate field next") := rfl
example : seedCells seedCtxNode {} #[⟨.defined 2, .struct [("nxt", .nil)]⟩]
    = .error (.stuck "seed: cell 0: struct main.Node: unknown field nxt") := rfl
example : seedCells seedCtx0 {} #[⟨.array 2 .bool, .array [.bool true, .bool false]⟩,
                                   ⟨.pointer (.int .int), .ref 0 [.index 1]⟩]
    = .error (.stuck "seed: cell 1: ref 0[1] has type *bool, *int expected") := rfl
example : seedCells ⟨{ funcs := #[], typeDefs := TypeEnv.reserved.push (⟨"main.B"⟩, .struct #[⟨"_", .int .int, false⟩]) }⟩ {}
    #[⟨.defined 2, .struct [("_", .int 1)]⟩]
    = .error (.stuck "seed: cell 0: struct main.B: a blank field (_) cannot be seeded (not in golean-seed-v1)") := rfl
example : seedCells seedCtx0 {} #[⟨.string, .int 1⟩]
    = .error (.stuck "seed: cell 0: int value at type string — an integer type expected") := rfl

/-- Arguments: a reference at a pointer parameter, a scalar passed through unchecked. -/
example : resolveSeedArgs seedCtx0.types 0 seedA
    #[{ id := 0, typ := .pointer (.int .int) }, { id := 1, typ := .int .int }]
    #[.ref 0 [], .scalar (.int 3 .int)]
    = .ok #[.addr (.base ⟨0⟩), .int 3 .int] := rfl
example : resolveSeedArgs seedCtx0.types 0 seedA #[{ id := 0, typ := .int .int }] #[.nil]
    = .error (.stuck "seed: argument 0: nil at non-pointer type int (v1: nil only at pointer types)") := rfl

/-- The seed-relative readout: inside the seed with its path; outside; a negative index. -/
example : seedRelative? 3 2 (.field (.base ⟨4⟩) ⟨"main.Node"⟩ "next") = some (1, [.field "next"]) := rfl
example : seedRelative? 3 2 (.base ⟨5⟩) = none := rfl
example : seedRelative? 3 2 (.index (.base ⟨3⟩) (-1)) = none := rfl

set_option maxRecDepth 8192 in
/-- S4/S6 at the control program: the empty seed with no arguments IS the ordinary run, with base 0
and an empty final seed (the instance of `runProgramSeededM_empty_stmt` by evaluation). -/
example : runProgramSeededM 12 initControl "F" #[] #[]
    = .ok { readout := { values := #[.int 7 .int] }, base := 0, seedFinal := #[] } := rfl

/-- The base off a slot list (RE-PIN 19): the empty seed's is 0; otherwise slot 0's address; a
non-base slot (impossible by S2) refuses by name. -/
example : seedBase #[] = .ok 0 := rfl
example : seedBase #[.base ⟨3⟩, .base ⟨4⟩] = .ok 3 := rfl
example : seedBase #[.index (.base ⟨3⟩) 0]
    = .error (.internal "seed: slot 0 is not a base address") := rfl

set_option maxRecDepth 8192 in
/-- S6 at the control program with ONE seed cell and no arguments: the cell lands at base 1 — after
the one global, which the initializer writes before the seed is placed — and the readout carries
that base beside the cell's final value (the run reads the global, never the cell). -/
example : runProgramSeededM 12 initControl "F" #[⟨.int .int, .int 41⟩] #[]
    = .ok { readout := { values := #[.int 7 .int] }, base := 1, seedFinal := #[.int 41 .int] } := rfl

/-- The arity refusal is the ordinary entry's, byte for byte (the shared prefix S4 relies on). -/
example : runProgramSetupSeededM 12 initControl "F" #[] #[.nil]
    = .error (.stuck "expected 0 argument(s), got 1") := rfl

end SeededControls

end GoLean.GoCore.SetupStatement
