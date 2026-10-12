# The GoLean semantics — an overview for someone who will reason against it

Living document, written 2026-10-12 ([AGENT], lane `docs/release-docs-1012`; release-readiness
item 11). It summarises the semantics and points at the Lean name or file that makes each claim
true. The Lean source is authoritative. The pinned statements are in
`GoLean/GoCore/BridgeSet.lean`, and the design records this page summarises are
`docs/2026-09-24_execution-statement.md`, `docs/2026-09-28_step-label.md` and
`docs/2026-10-04_pool-relation-spec.md`. All Lean files are under `GoLean/GoCore/` unless the
path says otherwise. The scope statement is `CLAUDE.md`, «What this repo provides, and does not».

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
(`ProgramCtx.lean`), and every step function and relation below is parametrised by it.

## 2. The machine and the step relation

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

**The relation.** `Step ctx c s c' s' l` (`Machine.lean`) is the fuel-free, choice-free
inductive step relation. Where Go permits several behaviours, the relation's rules range over
all of them, and the executable selects one member using the tape (§6). The two are proved
equivalent per step (`MachineSound.lean`):

- `stepFn_sound`: if `stepFn ctx s c ch = .ok (c', s', ch', l)`, then `Step ctx c s c' s' l`.
- `step_complete`: if `Step ctx c s c' s' l`, then there exist `ch, ch'` such that
  `stepFn ctx s c ch = .ok (c', s', ch', l)`.

They share their operational core. Strict operators go through one generic frame whose
`applyStrictOp` is the same function on both sides (the `Machine.lean` header). The
consumption projection `seqConsumption` names the site and bound of every tape consultation a
step makes, and the `stepFn_consumption_*` theorems tie it to the executable.

**Well-formedness.** `StateWf` (`StateWf.lean`) states the store invariants, such as declared
types and normal heap shapes. `step_preserves_wf` preserves the machine-level invariant
`MachineWf` across a step.

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
Its relational counterpart (statements in `ExecutionStatement.lean`, proofs in `Prefix.lean`)
has the following parts:

- **`Prefix ctx n s c ch ls sf cf chf`** is the counted, choice-threaded prefix closure: `n`
  executable steps, one label per step, threading the tape exactly as `stepFn` does. It holds
  for arbitrary endpoints and is independent of termination. Its algebra is `prefix_refl`,
  `prefix_comp`, `prefix_split`, `prefix_erase_trace`, `prefix_erase_steps` and `prefix_iter`.
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
is `runProgramSetupM` / `seedGlobals` (`StepFn.lean`), with equations in
`SetupStatement.lean`/`SetupSound.lean` and `runProgramSetup_noInit` (`Equations.lean`).

## 5. The goroutine pool

Goroutines run on a pool (`MultiConfig`, `Multi.lean`). One pool step, `stepMulti`, returns a
`StepEvent := { who, action, label }`: which goroutine stepped, what kind of step the pool took
(including spawns and channel pairings), and the full `StepLabel`. The whole-program drivers are
`execProgLoop` / `execProgLoopOut`, and `runProgramPoolOutM` is the one `golean native-json-run`
calls. The relational half (`PoolStep.lean` definitions, `PoolStatement.lean` the 48 frozen
statements, `PoolSound.lean` their proofs, frozen by `scripts/check-pool-spec`) has these parts:

- **`StepML ctx m m' ev`** is the scheduler relation labelled by the executable's own event.
  `stepML_sound` and `stepML_complete` relate it to `stepMulti` per step. `StepsML` is its
  closure. The older trace-labelled `StepM` is its projection (`stepML_erase`).
- **Scheduling is a pick.** At a registry boundary (`MultiConfig.schedMenu?`) the rule premise
  `SchedSlot` names the menu slot that runs, and the event's `picks` begins with that record
  (`schedRecord`). Context switches happen only at boundaries (`stepML_switch_boundary`).
  Attribution and the frame law are `stepML_who_runnable` and `stepML_frame`.
- **Deadlock** has its own predicate, `PoolDeadlock`. The relation is silent on a deadlocked
  pool (`asleep_silent`). It differs from the sequential `Blocked` (`singleton_deadlock`).
- **The driver** is modelled by `PoolPrefix` (the counted closure of the driver loop: the gate
  `Continue`, then `stepMulti`, then the race detector) and by `PoolFinish`, which classifies
  with terminal priority (an aborted goroutine first, then main's exit, then deadlock).
  `pool_classification` and the `pool_run_*_iff` fuel bridges are the counterparts of §4, and
  `stepMulti_replay` / `poolPrefix_replay` give replay by record.
- **Single goroutine.** `stepML_single_sound`, `stepML_single_complete`, `singleton_run` and the
  `singleton_finish_*` family show that a one-goroutine pool is the sequential machine.
  `PoolProjection.lean` (`execProgLoopOut_single_wide` and its siblings) carries output and
  terminals across.

**Not a theorem:** «every relational run is some tape's prefix». The relation can step past an
aborted goroutine, whereas the driver classifies the abort first. The statement holds per step,
and for runs that pass the driver's gate.

## 6. The choice tape

Where Go permits several behaviours, the machine consults a **choice site**. The census is
the datatype `ChoiceSite` (`State.lean`): map iteration, append and conversion capacity, the
scheduler at boundaries, post-op and back-edge preemption, the main-exit window, `select`
clause and waiter picks, `TryLock`'s spurious failure, unsequenced panic order, the `unseq`
scheduler, a panic-text pair, the re-panic marker, and `rand.Intn`. Every consultation goes
through **one** combinator, `Choices.consumeAt site bound`. It pops the tape only when
`bound ≥ 2`; a bound-≤-1 consult is inert (`Choices.consumeAt_le_one`). The tape is a plain
`List Nat` (`Choices`), and it is threaded outside the `Store`, so the relation never mentions
it.

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
certifies that every enumerated path ends in the race refusal (`--expect-status race`). In proof vocabulary, a terminal observation is `Observation` (`ProgramTrace.lean`,
with `observation_iff`) and `Obs`/`SlowObs` (`EnumSpec.lean`), and refusals and fuel-out are
not observations (`refusal_is_not_observation`, `fuel_is_not_observation`). The evidence
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

A refusal has no relation successor, so the theorems are partial-correctness statements across
a refusal. A refusal is never counted as a pass.

## 9. The pinned statement set and the re-pin offer

`BridgeSet.lean` contains one `example` per pinned statement, with binders written out, and
it is imported by the default build. If a pinned type drifts, the build fails. There are
currently 590 rows. The device does not catch a changed binder annotation, or a changed
definition with an unchanged type (the file header says so). The semantic equations are
gated separately (`scripts/check-equations`).

The set is the consumer's interface. The logic repository pins a commit, currently the tag
`logic-offer/2026-10-03`. Changes accumulate on `main` behind that pin. Each change that
affects a pinned row or a consumer-visible behaviour is a line in the post-offer changelog
(`docs/changelog/20d3946d-WINDOW.md`), and the rows ship together as the next batched **re-pin
offer**. The diff of `BridgeSet.lean` between two pins is the interface diff. The last offer is
`docs/2026-10-03_offer-to-logic-team.md`.

## 10. Stated limits

- **Setup is a premise.** Whole-program setup is stated by equations, not derived from the
  relation. Its no-globals, no-initializer case is the pinned `runProgramSetup_noInit`.
- **Printing during package initialization is refused** (`initPrintRefusal?`, `Machine.lean`).
- **`NoRefusal` and the sequential classification apply to the sequential driver only.** A `go`
  statement leaves that domain, and the pool results of §5 cover it instead.
- **Concurrency granularity.** The machine steps at its own granularity. Some wide operations
  are single steps (latitude inventory U-5). Reducing this to Go's access granularity is an
  explicit open obligation, not a theorem. `NPDRF.lean` states the registry-point reduction
  (only its easy inclusion, `stepM_le_stepMFine`, is proved), and the 2026-10-03 offer lists the
  NPDRF reduction as unusable (its limit 9).
- **Fixed platform.** The one instance is `Platform.gcAmd64` (`Platform.lean`): gc on
  linux/amd64, with 64-bit `int`, gc's layout, and per-op float rounding. Portability is a
  separate contract (latitude inventory §11).
- **The lowering carries no correctness theorem** (§1).
- The full limit list given to the consumer is in `docs/2026-10-03_offer-to-logic-team.md` §4,
  as amended by the post-offer changelog. Open fidelity bugs are in `docs/BUGS.md`.
