import GoLean.GoCore.StepFn
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

ADDITIVE. The pinned `runProgramSetup_noInit` and the `{}`-store `setup_lookup_arg` /
`setup_lookup_result` / `setup_resultLocs` / `setup_heap_size` of `Equations.lean` are unchanged
(statements and proofs); each is the instance of its general form here at the empty store — shown
as `example`s at the end of `SetupSound.lean`. No definition of the interpreter, the drivers or the
setup functions changes; the one new definition is `zeroCell` (a reading of `Store.alloc`'s result
on a zero value, used to STATE the seeding equation).

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

The four `{}`-store lemmas of `Equations.lean` over an ARBITRARY pre-bind store `s₁` (the post-init
store): the cells are `entrySlot s₁ k = .base ⟨s₁.heap.size + k⟩` (`Machine.lean`, the C4 D8 layout
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
`runInitConfig`, and through G-R4 to `execStmtLoop`. The twin of `Equations.lean`'s
`runPkgInitM_none`. -/

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

end GoLean.GoCore.SetupStatement
