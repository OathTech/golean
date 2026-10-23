# The GoLean semantics — an overview for someone who will reason against it

Living document, written 2026-10-12 ([AGENT], lane `docs/release-docs-1012`; release-readiness
item 11). It summarises the semantics and points at the Lean name or file that makes each claim
true. The Lean source is authoritative. Amended 2026-10-20 ([AGENT], lane
`core/retire-relation-1020`): the relational layer this page described — the step relation and
its coherence proofs, the pool relation, the pinned statement set `BridgeSet.lean` — was retired
from the build by the [USER] ruling of 2026-10-20; the last main carrying it is the tag
`relational/last-main-2026-10-20`, and the archive-library entry is in `docs/ARCHIVE.md`. The
design records this page summarises are `docs/2026-09-24_execution-statement.md` and
`docs/2026-09-28_step-label.md` (`docs/2026-10-04_pool-relation-spec.md` describes the retired
pool half). All Lean files are under `GoLean/GoCore/` unless the path says otherwise. The scope statement is `CLAUDE.md`, «What this repo provides, and does not».

## 1. GoCore, the language

GoCore is a small, typed, imperative core language with goroutines, channels, `select`, the
`sync` primitives, maps, slices, interfaces, `defer`/`panic`/`recover`, and Go's runtime panics
(`Syntax.lean`: `Expr`, `Stmt`, `Func`, `Program`). Calls are statements, not expressions. Locals
are numbered per function (`VarId`, with a checked name table `Func.locals`). Types live in a
dependency-ordered table indexed by `Ty.defined` (`TypeEnv`, accepted only if
`TypeEnv.WellFounded`). A Go program reaches GoCore through the native frontend and the decoder
`GoLean/NativeToIR.lean` (wire format: `docs/cli.md` §3). **That lowering has no correctness
theorem.** It is validated differentially, and whoever consumes a GoCore program inherits this
trust assumption. A run's static context (the program's tables) is a `ProgramCtx`
(`ProgramCtx.lean`), and every step function below is parametrised by it.

## 2. The machine and the executable step

**State.** A configuration (`Config`, `Machine.lean`) is the control state of one goroutine.
`exec stmt env k` runs a statement, `evalE e env k` evaluates an expression, and `retV v k`
delivers a value. `next k` moves to the next frame and `signal sg k` carries
`break`/`continue`/`return` outward. `panicking chain k` is unwinding, and four `blocked…`
forms represent a goroutine waiting on a channel, a `select` or a sync primitive. The
continuation is a list of frames (`Cont := List Frame`). Memory is a `Store` (`Store.lean`):
a heap of cells addressed by `Loc`, allocated by `Store.alloc`. The stack holds no hidden state.
Each step is at memory-operation granularity.

**The executable.** `stepFn ctx s c ch` (`StepFn.lean`) takes one step from configuration `c`
with store `s` and choice tape `ch`. It returns either
`.ok (c', s', ch', label)` or `.error stop`. It is total: there is no `partial` anywhere in
`GoLean/GoCore/`, and the gate's escape-hatch scan in `scripts/ci` enforces this.

**The relation — retired.** A fuel-free, choice-free step relation `Step ctx c s c' s' l`
(`Machine.lean`), proved equivalent to `stepFn` per step in both directions (`stepFn_sound`,
`step_complete`, `MachineSound.lean`), with well-formedness preservation along it, lived here
until 2026-10-20, when the [USER] ruled the relational layer retired from the build: the last
main carrying it is the tag `relational/last-main-2026-10-20`, and `docs/ARCHIVE.md` has the
archive-library entry. What remains of its support is `StepFnFacts.lean`, the kept part of
`MachineSound.lean` (unchanged): the `NoPanic` discipline of the write path, the apply
inversions, and the stream lemmas — the consumption projection `seqConsumption`
(`Machine.lean`) names the site and bound of every tape consultation a step makes, and the
`stepFn_consumption_*` theorems tie it to the executable. The executable predicates naming the
consuming shapes (`consumesSelect`, `consumesAppendSlice`, …) are in `Consumes.lean`.

**Well-formedness.** `StateWf` (`StateWf.lean`) states the store invariants, such as declared
types and normal heap shapes; the setup path decides it (`StepFn.lean`), and `MachineWf` /
`MultiWf` (`Multi.lean`) are built on it.

## 3. The labelled step

Every step carries a label `StepLabel := { trace, picks, out }` (`Ops.lean`):

- `trace : AccessTrace` lists the memory accesses the step performed, emitted by the memory
  module's operations (`Mem.load`, `Mem.store`, …).
- `picks : List PickRecord` lists every tape consultation of bound > 1 that the step kept, as
  `⟨site, bound, pick⟩` records (`PickRecord`, `Choices.consumeAtE`, `State.lean`).
- `out : List GoString` lists the bytes a `print`/`println` step wrote to fd 2.

A pure step's label is `⟨[], [], []⟩`. A run's observation of its labels is the per-field fold
`StepLabel.fold`, and pure steps contribute nothing to it (`StepLabel.fold_silent`). A step has
no interleaving between channels. This is a documented limitation, not an invented order.

## 4. The sequential driver: prefixes and the five endings

The sequential driver is `execStmtLoop ctx fuel s c ch` (`StepFn.lean`). It iterates `stepFn`
until the configuration is terminal, the goroutine blocks, a stop occurs, or the fuel runs out.
Its proof-level counterpart (statements in `ExecutionStatement.lean`, proofs in `Prefix.lean`;
kept on main as a supported surface for the raft-proofs repository) has the following parts:

- **`Prefix ctx n s c ch ls sf cf chf`** is the counted, choice-threaded prefix closure: `n`
  executable steps, one label per step, threading the tape exactly as `stepFn` does. It holds
  for arbitrary endpoints and is independent of termination. Its algebra is `prefix_refl`,
  `prefix_comp`, `prefix_split`, `prefix_erase_trace` (to the counted `Trace`, `Trace.lean`) and
  `prefix_iter` (exact agreement with `stepFnIter`).
- **`Finish`** is how the driver classifies an endpoint. It has five constructors, and these are
  the **five endings**:
  - `normal` at `.next .stop`
  - `blocked`, the sequential deadlock (`Blocked`)
  - `aborted`, an unrecovered panic reaching `.stop` (`Config.abort?`), rendered by `abortMsg`
  - `abortRefused`, where the renderer refuses
  - `fatal`, an unrecoverable runtime throw

  Each ending carries its finishing cost (0 or 1) and the residual tape (`FinishOutcome`).
- **`LRun`** is a completed labelled run, derived from `Prefix` + `Finish`.
- **The classification.** `classification` says every run of `execStmtLoop` is exactly one of
  `ClassOk`, `ClassTerminal`, `ClassFuelOut` and `ClassRefusal`, with no premise.
  `classification_wf` says that under `StateWf` and the domain premise `NoRefusal`, only the
  first three remain.
- **Fuel bridges.** `run_ok_iff`, `run_panic_iff`, `run_deadlock_iff` and `run_fuelOut_iff`
  relate a fuelled result to a prefix within that fuel.
- **Replay by record.** `replays` re-draws a label's `picks` on a fresh tape through the same
  `Choices.consumeAtE` (`finish_replay`, `replay_coverage`).
- **`NoRefusal`** is the domain premise: no reachable non-zero-cost configuration refuses, and no
  reachable abort's renderer refuses.

Whole-program setup (seeding globals, the package initializer, binding the entry's arguments)
is `runProgramSetupM` / `seedGlobals` (`StepFn.lean`); its no-globals, no-initializer case is the
equation `runProgramSetup_noInit` (`Equations.lean`). The general setup equations and the
seeded-heap statements (`SetupStatement.lean`/`SetupSound.lean`) were retired with the
relational layer. The package initialiser's own driver `runInitConfig` (the loop with the init-phase
print guard `initPrintRefusal?`) is related to this surface by `GoLean/GoCore/InitDriverFacts.lean`
(2026-10-21, raft-proofs G11): `runInitConfig_cases` says, with no premise, that the init loop either
equals `execStmtLoop` (no configuration reachable within the fuel is a print position) or refuses by
name at a reachable print position, so a successful initialisation is a `Prefix` of `$pkginit`'s body
to `.next .stop` (`runInitConfig_ok_prefix`, `runPkgInitM_ok_cases`); under the no-print premise the
G-R4 family of 2026-10-05 holds as then stated (`runInitConfig_eq_execStmtLoop`, the four
`runInitConfig_*_iff`, `runPkgInitM_some`/`_ok_iff`). The converse from one witnessed run is
`runPkgInitM_ok_of_prefix_silent`: a `Prefix` of `$pkginit`'s body to `.next .stop` within the fuel
whose labels all have `out = []` is a successful `runPkgInitM` (through `stepFn_out_of_printOut?` —
a successful step at a print position carries its bytes on the label — and `stepFn`'s functionality;
the `Prefix` determinism laws `prefix_det`/`prefix_det_le` ship beside it for the customer and are
not used by it). Scope: the converse delivers `runPkgInitM … = .ok (s₁, ch₁)`; the customer's
`Seeded` is over `runProgramSetupSeededM`, which after `runPkgInitM` continues with `seedCells`,
`resolveSeedArgs`, `bindParams`, `allocDecls` and `pinResultLocs` and has no equation on main — G11
as asked is met, and the remaining distance to `Seeded` is their R8 symbolic work as their design
prices it. Stated gap: the opposite direction, from a successful init run to silent labels,
would need the off-apply emptiness lemma `printOut? c = none → stepFn ctx s c ch = .ok (c', s', ch', l)
→ l.out = []`, a whole-`stepFn` case analysis that is not on main; what a successful run gives is the
config-form `runInitConfig_ok_noPrint`.

## 5. The goroutine pool

Goroutines run on a pool (`MultiConfig`, `Multi.lean`). One pool step, `stepMulti`, returns a
`StepEvent := { who, action, label }`: which goroutine stepped, what kind of step the pool took
(including spawns and channel pairings), and the full `StepLabel`. The whole-program drivers are
`execProgLoop` / `execProgLoopOut`, and `runProgramPoolOutM` is the one `golean native-json-run`
calls. The relational half — the labelled pool relation `StepML`, its 48 frozen statements and
their proofs — was retired with the relational layer on 2026-10-20 (tag
`relational/last-main-2026-10-20`, `docs/ARCHIVE.md`); no relation-level pool theorem is in the
build. What IS in the build, relation-free and over the executable driver only (restored
2026-10-21, fix round F1): the **single-goroutine bridge** — `execProgLoop_single` and
`single_embedding` (a one-goroutine pool run of `execProgLoop` is the sequential run at fuel plus
`seqOpCount`), `stepMulti_single`/`stepThread_single`, `execProgLoop_aborted` (`PoolFacts.lean`);
the sequential-to-pool **projections** carrying output and terminals across
(`execProgLoopOut_single_wide`/`_prefix`/`_terminal`, `pool_run_single_prefix`, `seqOut_of_prefix`;
`PoolProjection.lean`); and the driver trace and **observation vocabulary** (`Pool.Run`,
`run_iff`, `ProgramRun`, `program_run_iff`, `Observation`, `observation_iff`,
`refusal_is_not_observation`, `fuel_is_not_observation`; `PoolFacts.lean`). The chain
`Prefix → execStmtLoop (run_ok_iff) → execProgLoop (single_embedding) → runProgramPoolOutM
(program_bridge)` therefore holds end to end for one goroutine. The bridge from `execProgLoop` to
the CLI's output-folding driver `execProgLoopOut` (raft-proofs G9) is `execProgLoopOut_snd`
(`Multi.lean`): the outcome component of `execProgLoopOut` IS `execProgLoop`; the output content on
one goroutine is `execProgLoopOut_single_prefix` (the `Prefix` labels' fold). `execProgLoopOut_snd`
(on main since 2026-09-05, commit `6a73d02d`) is pinned and required since 2026-10-21;
`execProgLoopOut_single_prefix`, `execProgLoopOut_single` and `seqOut_of_prefix` are required by the
core audit (by name, not pinned — their statements live in the kept module `PoolProjection.lean`). An accumulator law was added beside them: `execProgLoopOut_acc`
(`PoolFacts.lean`: the output component is the accumulator followed by the run's own fold from the
empty string — the fold only appends; the CLI always starts from `GoString.empty`) and its pair form
`execProgLoopOut_eq_execProgLoop`.

## 6. The choice tape

Where Go permits several behaviours, the machine consults a **choice site**. The census is
the datatype `ChoiceSite` (`State.lean`): map iteration, append and conversion capacity, the
scheduler at boundaries, post-op and back-edge preemption, the main-exit window, `select`
clause and waiter picks, `TryLock`'s spurious failure, unsequenced panic order, the `unseq`
scheduler, a panic-text pair, the re-panic marker, and `rand.Intn`. Every consultation goes
through **one** combinator, `Choices.consumeAt site bound`. It pops the tape only when
`bound ≥ 2`; a bound-≤-1 consult is inert (`Choices.consumeAt_le_one`). The tape is a plain
`List Nat` (`Choices`), and it is threaded outside the `Store`.

- **Slot 0 is the canonical member** (`ChoiceSite.canonicalSlot0`, one documented row per
  site). The empty or exhausted tape therefore gives the machine's default behaviour, usually
  gc's realized point.
- **Replay is by record.** A label's `picks` can be re-drawn exactly (`replays`, §4).
- **What the tape does not cover.** The tape covers only points classified (a) ENVELOPED in the
  latitude inventory (`docs/2026-08-11_latitude-inventory.md`). Points classified (b) PINNED
  or (b-n) NARROWED are fixed to one behaviour; some are known to differ from gc (E3, E7, R19).
  Points classified (d) UNKNOWN are not analysed. Allocation is deterministic, so location ids
  are not a choice. The platform is fixed (§9). The tape's raw pop wraps out-of-range entries
  and ignores leftovers (`docs/cli.md` §6.1).

## 7. The observation and the differential

A run returns a `Readout` (`State.lean`: the result values and the program's fd-2 output), or
a `Stop` with the output printed so far. The CLI renders this as `golean-observation-v1`
(`docs/cli.md` §4). The differential runs each corpus row under `go run` at go1.26.5 and under
the interpreter, then compares the two observations with `golean observation-eq`. A row runs
in one of four lanes (`docs/coverage-suite-structure.md`). **Strict** compares one Go run with
the default-tape run, checking invariance across several tapes. **Membership** requires every
Go sample to be a member of the enumerated set (`golean coverage-observations`).
**Confluent** certifies that the set has one member, then compares strictly. **Racy**
certifies that every enumerated path ends in the race refusal (`--expect-status race`). In proof vocabulary, an observation is `Obs`/`SlowObs` (`EnumSpec.lean`); refusals and
fuel-out are not observations (`Stop.status`, §8). The evidence
relation is observed ⊆ modeled ⊆ permitted. The differential tests the left inclusion. The
right inclusion is argued in the latitude inventory, row by row, at the rule sites (§11 of the
inventory).

## 8. Stops: Go behaviour versus apparatus

`Stop` (`Value.lean`) is one of three things: `refusal`, `terminal` or `fuelOut`. Its status
words come from `Stop.status`.

| class | constructor | status | is it Go behaviour? |
|---|---|---|---|
| terminal | `Terminal.panic` | `panic` | yes: an unrecovered run-time panic |
| terminal | `Terminal.fatal` | `fatal` | yes: an unrecoverable throw (sync misuse) |
| terminal | `Terminal.deadlock` | `deadlock` | yes: gc's detector (latitude C9, pinned) |
| terminal | `Terminal.raceDetected` | `race` | the program is racy; refused per run by doctrine, oracle `go run -race` |
| refusal | `Refusal.unsupported` | `unsupported` | no: the named frontier of the model |
| refusal | `Refusal.stuck` | `stuck` | no: the program is outside the lowering contract (a frontend bug) |
| refusal | `Refusal.internal` | `error` | no: a machine invariant broke (a machine bug) |
| — | `Stop.fuelOut` | `fuel-out` | no: the bounded run ended first (a model artifact) |

A refusal has no successor (`Finish.abortRefused`, `ClassRefusal`), so the `Prefix` theorems are
partial-correctness statements across a refusal. A refusal is never counted as a pass.

## 9. The customer surface and the re-pin offer

The pinned statement set `BridgeSet.lean` (one `example` per pinned statement, 605 `example`s at the
end) left the build with the relational layer on 2026-10-20 (tag
`relational/last-main-2026-10-20`, `docs/ARCHIVE.md`). The surface kept on main is
`Prefix`/`Finish` (§4) and the `stepFn_eqns` equation library (`Equations.lean`,
`EquationsAttr.lean`), gated by `scripts/check-equations`: the client `Tests/EquationClient.lean`
proves its facts from the equations alone, every equation is enrolled, and `stepFn` is never
unfolded. Two additions for the raft-proofs customer (backlog row 47, 2026-10-21), each pinned
verbatim in `Tests/GoCoreContract.lean` §D and required by the core audit: `runInitConfig_cases`
(`InitDriverFacts.lean`) relates the initialiser's driver to `execStmtLoop` and `Prefix` up to the
init-phase print refusal, with no premise, so the seeded entry's initialisation is a `Prefix`
(G11), with `runPkgInitM_ok_of_prefix_silent` as the converse from one witnessed silent run;
`execProgLoopOut_snd` (`Multi.lean`) is the G9 bridge — the outcome of the CLI's output-folding driver
is `execProgLoop` — now pinned, with `execProgLoopOut_acc`/`execProgLoopOut_eq_execProgLoop`
(`PoolFacts.lean`) as an accumulator law beside it. A third addition (backlog row 48, 2026-10-23,
raft-proofs G16): `GoLean/GoCore/TableMonotonicity.lean` — the sub-table relation
`ProgramCtx.SubTables` (the same `typeDefs`, `globals`, `typeDisplays` and `methodSets`; `funcs`,
`methods` and `promotions` sublists of the whole's; the whole's key discipline, which the decoder
enforces; three closures of the slice, named in the module header) and `stepFn_mono`,
`prefix_mono`, `finish_aborted_mono`, `execStmtLoop_ok_mono`, `execStmtLoop_panic_mono`: a
successful step, a labelled run, an abort's finish and the sequential driver's completion or
panic under a slice of the tables are the same under the whole — pinned in
`Tests/GoCoreContract.lean` §D with the lookups and the frame-entry funnel it rests on, required
by the core audit. Refusals are not claimed (a slice refuses where the whole dispatches).

Since 2026-10-23 (release-readiness row 43, [USER]-ruled) that kept surface is a COMPARATOR
CONTRACT: `Contract/Challenge.lean` restates all 349 of its theorems — every theorem of
`Equations.lean` (296; 232 of them `@[stepFn_eqns]` simp-set members — the `signalStep_*` rows,
`runProgramSetup_noInit`, the `allocDecls_*`/`bindParams_*`/`setup_*` facts and the rest are plain
theorems of the module), the 27 public theorems of `InitDriverFacts.lean` (G11), the five
`Prefix`/`Finish` laws above, the six output-fold statements, `enterFrame_declared` and the fourteen
`Choices.consumeAt*` laws (the list, read from the built environment: `scripts/contract-names.lean`)
— as frozen text with `sorry` holes, under alias names `GoLean.Contract.<rest>`; the generated
`GoLean/Contract/Solution.lean` presents GoLean's own theorems under the same names with their own
types; and `lake comparator` (`comparator.json` at the root; the `--diff`-tier speedbump
`scripts/check-comparator`, the claim-point run of `docs/release.md` §3) judges that each statement
is syntactically what the challenge says (Lake's comparison of the two exports; binder names and
binder annotations ignored), on standard axioms, with the solution replayed through the kernel. An
edit to a kept theorem's statement is a mismatch naming the theorem; the challenge is updated
deliberately, with a changelog row. The limit: in-repo the frozen text is re-elaborated against the
LIVE definitions, so a drift that enters through a definition's signature (an inserted implicit or
default argument, an `abbrev`) moves both sides and is caught only across a pin, by the consumer's
`--challenge-from-export` route (`scripts/contract-export`); definitions (`Prefix`, `Finish`,
`replays`, `stepFn`) are shared by both sides in-repo, not frozen. The §D pins of
`Tests/GoCoreContract.lean` stay as the build-time text witness of the same set.

The logic repository pins a commit, currently the tag `logic-offer/2026-10-03`. Each change that
affects a consumer-visible behaviour or the kept surface is a line in the post-offer changelog
(`docs/changelog/20d3946d-WINDOW.md`), including this retirement; a re-pin past it must drop
the relational imports. The last offer is `docs/2026-10-03_offer-to-logic-team.md`.

## 10. Stated limits

- **Setup is a premise.** Whole-program setup is not derived from the step; its no-globals,
  no-initializer case is the equation `runProgramSetup_noInit`, and the general setup
  equations were retired with the relational layer.
- **Printing during package initialization is refused** (`initPrintRefusal?`, `Machine.lean`).
- **`NoRefusal` and the sequential classification apply to the sequential driver only.** A `go`
  statement leaves that domain; no pool-level statement is in the build (§5).
- **Concurrency granularity.** The machine steps at its own granularity. Some wide operations
  are single steps (latitude inventory U-5). Reducing this to Go's access granularity is an
  explicit open obligation, not a theorem (the `NPDRF.lean` statement of the registry-point
  reduction left with the relational layer; the 2026-10-03 offer already listed it as unusable,
  its limit 9).
- **Fixed platform.** The one instance is `Platform.gcAmd64` (`Platform.lean`): gc on
  linux/amd64, with 64-bit `int`, gc's layout, and per-op float rounding. Portability is a
  separate contract (latitude inventory §11).
- **The lowering carries no correctness theorem** (§1).
- The full limit list given to the consumer is in `docs/2026-10-03_offer-to-logic-team.md` §4,
  as amended by the post-offer changelog. Open fidelity bugs are in `docs/BUGS.md`.
