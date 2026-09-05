# Gate A1 — contract experiment and decisions

Status: [AGENT] implementation and recommendations under the user's Gate A1
commission. Branch `gate-a1-contract`, based on
`79019a74c1e1c1418293d380d1fcfbd9ae489980`. No new [USER] architecture ruling
is claimed. The package is `spikes/gate-a1/`; its check is independent of the
default dependency graph. Gate A1 is a bounded experiment, not all of Gate A
and not a consumer pin.

## Result and recommendation

**Use the present machine to develop the consumer contract now. Keep a bare
Iris `Language` and continuation-aware rules; do not promise generic evaluation
contexts. Use a driver trace that retains choice, detector, output and exit
information for whole-program observation claims.** This experiment required
no runtime refactor. The original I5 sketches should be replaced by the
checked statements here as working candidates, with the limitations below.

The current machine is not inherently inaccessible to a thin customer. What
is missing is a convenient, stable collection of semantic laws, typed
admission and compositional rules. Changing the continuation representation
alone would not provide those. The consumer's laws should guide any such
refactor and remain as regression tests afterward.

## Reference experiments examined

The parked reasoning branch and `g-bind` both resolve to
`7440bf705a87b052243ff36280b677f4100b6a66`. I read the relevant definitions
and contracts in `proofs/GoLeanProofs/Lang.lean`, `Laws/Bind.lean`,
`Frame/Plug.lean`, and the `LangC`, `LangD`, and `Adequacy` module introductions.
The existing `u0-iris` worktree also supplied local dependency build caches.
I did not rebuild the parked proof product or claim those older proofs apply
unchanged to this machine.

Important lessons from that source:

- A bare sequential Iris instance was already available. It is a small
  adapter, not a reason to restore the entire parked reasoning product.
- The old bind proof explicitly rejected unconditional context laws and used
  recovery, barrier, map-iteration and panic-drain premises. Some concern
  current semantic obligations; others reflect an older implementation.
  For example, current map-entry stamps have changed the old cross-context
  pruning problem. Porting all those premises without rechecking would be wrong.
- The concurrent experiments already encountered two-thread channel pairing
  versus Iris's single-thread primitive-step interface. The decomposed
  experiment used a simulation and a wider proof-layer envelope. A compiling
  per-thread instance alone did not establish full concurrent adequacy.

The sibling project was found at
`/home/dev/projects/cerberus-lean-proj/refined-cerberus`, revision
`8eeaf924ad630557458dcd99e164ddbd03d1d2f3`, clean when inspected. I read its
architecture and relevant parts of `CerberusHeapLang/Lang.lean`, `Wps.lean`,
`Adequacy.lean`, and `Audit.lean`. It separates a continuation/label-aware
statement judgment from the bare Iris language and distinguishes partial
and total driver claims. Its module-origin axiom check informed this spike's
small build-time check. It uses a different Iris revision; this spike keeps
the GoLean archival pin rather than silently upgrading it. No sibling files
were modified or dependencies added to its workspace.

## What is now proved

All names below live under `GoLean.GateA1`. They are ordinary Lean theorems;
the evaluation probes are not their proof evidence.

**Sequential prefixes and completion (`Trace.lean`).** `Trace n s c ch sf cf
chf` records exactly `n` successful calls to the existing `stepFn`, threading
one initial stream to its residual. `iter_iff_trace` proves equivalence with
the existing `stepFnIter`. `Trace.erase` gives existing `Steps` reachability.
The successful-run theorem is:

```lean
execStmtLoop fuel s c ch = .ok (sf, chf) ↔
  ∃ n, n ≤ fuel ∧ Trace n s c ch sf (.next .stop) chf
```

It fixes the stream on both sides and accounts for terminal checks preceding
fuel checks. The existential version quantifies over streams on both sides.
There is no assertion that arbitrary per-step existential stream witnesses
compose into a single executable stream. That converse of erasure remains a
distinct obligation; the present trace retains the necessary evidence.

**Pool and whole-program outcomes (`PoolTrace`, `ProgramTrace`).** `Pool.Run`
is a fuel-indexed inductive trace for the existing `execProgLoopOut`. Its
constructors distinguish pre-step termination, exhaustion, step failure,
detector rejection, and successful stepping. Each step retains the incoming
pool, detector, choices, output accumulator and successful successor data.
`front` factors the driver's pre-fuel policy, including the L5 exit choice;
`unfold_driver` proves that factoring against the actual driver. `run_iff`
proves both directions for every outcome, not only success.

`ProgramRun` adds the actual `runProgramSetupM` and `loadMany` seams. It
distinguishes setup failure, loop failure, readout failure and normal readout.
`program_run_iff` proves:

```lean
runProgramPoolOutM fuel p name args ch = result ↔
  Pool.ProgramRun fuel p name args ch result
```

This includes the real program entry, not just execution from an assumed
initialized state. **Setup is an executable premise, not a proved static
admission theorem.** The same fuel parameter is supplied separately to setup
and subject execution, as in today's implementation. It is not a single
whole-program step counter. A consumer must not silently interpret it as one.

`Pool.Observation` preserves normal readout or terminal reason plus output.
`observationOf` returns none for refusals and fuel exhaustion.
`Pool.observation_iff` proves the finite observation-set bridge with
existential fuel/choices on both sides. Neither that existential theorem nor
the bare Iris WP asserts termination, fairness, divergence equivalence, or
that every stream produces a Go observation.

The pool trace is deliberately close to the executable control flow. Its
proof establishes a usable exact contract, not independent validation of
Go's scheduler or race model. `Run.success_reaches` erases successful traces
to the current `StepM` closure. The reverse is not claimed: erasure loses
the detector, exit choices and output. The plan's name `StepsM` was a sketch;
the current core has `StepM` but no closure exported under that name.

**Adversarial examples (`Counterexamples`, `Examples`).**

- Recovery under a bare frame yields nil; adding the panic-resume frame
  yields the payload and marks the handler. The corresponding transported
  bare successor is *not* a `Step`. These are kernel-checked facts, upgrading
  the earlier compiled audit probes.
- The actual `.unseqPanic` site admits defer and raise. A fixed `[0]` stream
  cannot realize the raised successor. Both real pool outcomes are proved:
  normal completion under `[0]`, panic under `[1]`, preserving an arbitrary
  preexisting output accumulator. The witnesses start at a machine control
  state; they are not certificates of a frontend translation.
- The sequential raised path exhausts at one unit of fuel and aborts with
  two. This catches the terminal/fuel distinction in the rejected sketch.
- A hand-authored GoCore program prints `before\n` and then panics `boom`.
  `print_before_panic` proves the complete `runProgramPoolOutM` result,
  including bytes, and `print_before_panic_trace` constructs its relational
  witness. This checks actual emitted output, not only propagation of an
  assumed prefix. Its panic payload explicitly includes the required `any`
  conversion; an initial unboxed experiment correctly refused and was fixed
  as malformed test IR, not treated as a semantics bug.
- `StateWf` still admits the ill-typed bool/int cell. No strengthening of
  that invariant is claimed here.

**Thin customer (`Language`, `Examples`).** The instance uses `Config`,
`ExecState`, the existing `Step`, unit values at `.next .stop`, no forks and
no observation events. It proves `val_stuck`. This is a sequential/control
adapter: it does not claim output or concurrent adequacy. In particular,
sequential `Step` can validate printing without representing the pool's output
event; its observation-free instance must not certify I/O assertions.

`pure_of_stepFn` derives Iris pure steps from state-preserving,
stream-oblivious executable steps, using both existing correspondence
theorems. `wp_recover` carries the exact continuation transformation. The
complete `recoverCheck` example checks the returned value against nil, selects
the successful branch, exits the deferred frame and resumes normally.
`recover_check_exec` establishes seven pure Iris steps;
`recover_check_runs` independently reaches normal completion in the actual
sequential driver for every state and every stream. `wp_recover_check`
uses Iris's public pure-step and value rules to reduce the consumer's
obligation to its postcondition, with explicit later credits.

The WP rule is polymorphic in the customer's `IrisGS_gen`; this spike does
not construct heap ghost resources or prove general Iris adequacy. The
concrete execution and pure-step witnesses make the example non-vacuous
without claiming a complete separation logic. No generic `Language.Context`
or `EctxLanguage` instance is supplied.

## Proposed interface and admission boundary

For the next sequential consumer milestone, propose **partial correctness
of normally returning, explicitly supported programs**, with recoverable
panics permitted internally. Separate contracts can reason about terminal
observations, using the full output-bearing driver. Uncaught panic is a Go
observation in that driver, but a stuck non-value in this bare sequential
Iris instance; a `NotStuck` proof through this instance must exclude it.
Do not conflate those two interfaces.

This is a proposed proof scope, not a claim that all sequential Go is now a
supported profile. Admission still needs the following independently named
predicates and proof obligations:

| Predicate/obligation | Meaning and current status |
|---|---|
| `WireWellFormed` | Required metadata, valid references, constructor arities and table bounds; decoding must establish these. Not implemented by A1 |
| `ProgramWellTyped` | Heap/operand types, function signatures, method metadata and value normalization; `StateWf` is insufficient. Not implemented by A1 |
| Valid entry and arguments | Existing function, correct arity, values valid at parameter types, well-formed captured values; not just successful lookup. Setup checks only part |
| Supported execution domain | Explicit feature/extern/profile policy, including reachable quarantined declarations and initialization. A syntactic absence-of-refusal scan is insufficient |
| Preservation/progress | Admitted executions preserve the domain and either step or reach classified outcomes; not proved by A1 |
| Refusal freedom | Must quantify over valid entry/arguments, admitted states and the declared support policy. Do not fill the old `Accepted P → ...` sketch with trivial predicates |

The C2 bound theorem, allocation normalization and full admission enforcement
remain Gate B work after their statements are fixed. The reflection descriptor
algebra is a separate pre-reflection investigation; this adapter needed no
reflection facility. These tasks should not be hidden inside a supposedly
small I5 proof estimate.

## Consequences for the next task

1. **Keep these checks alive while doing B7/C1.** Program context/store and
   explicit access traces remain justified changes. Their acceptance includes
   rebuilding this package, not preserving a constructor count. No core
   refactor was necessary to get these first contracts.
2. **Next, exercise actual entry and composition (A2), before C3.** Use the
   archived bind work and Cerberus's continuation/label-aware approach as
   references. A small call/return plus defer/recover composition example
   should precede any claim of generic bind. Include named-result readout
   and actual entry/defer setup, not only a constructed continuation.
   Revalidate which old premises are still needed; do not mechanically port them.
3. **Scope admission as its own assurance task (A3).** First scope the
   supported sequential domain and formalize entry/value/table validity,
   including the C2 bound. Supply a typed heap invariant and its checks
   before promising refusal-free execution. It is separate from a generic
   Iris heap logic, which remains the customer's work.
4. **Do not offer a concurrent pin from these bridges.** They certify the
   current policy, not its Go adequacy. Access granularity, detector soundness,
   scheduler reduction and two-thread pairing remain explicit Gate D items.
5. **Replace the operative plan rather than adding another exception layer.**
   I5 now has proved candidate bridges; general typed refusal freedom,
   context composition and consumer adequacy are still distinct open rows.

Recommendations (1)–(5) are [AGENT]. This lane changes no master-plan ruling.
The subsequent [adversarial review and next-phase proposal](2026-09-05_gate-a1-review-and-next-phase.md)
gives the proposed task order and acceptance tests in more detail.

## Validation and limitations

The separate `check` command builds the core and spike and freshly elaborates
every proof module, followed by evaluation probes. The axiom check examines
all constants after importing the complete spike modules, including the
aggregate, probes, and generated/private declarations,
and allows only `propext`, `Classical.choice` and `Quot.sound`. Required theorem
exports are checked by name. This check supplements the Lean kernel; it is
not a theorem of external Go fidelity. Adversarial review exposed a gap in
the original in-module audit; the repaired external harness rejects three
compiled poisoned-module fixtures and was independently re-reviewed.

Builds are capped with the existing `scripts/capped`. Incremental core and
dependency caches were copied into the isolated worktree; no shared build
directory is written by the spike. The evidence records this as an incremental
build plus fresh elaboration, not a clean-room bootstrap. No runtime, frontend,
corpus, baseline or ordinary CI-policy change was made. No full differential,
slow-tier recertification, detector campaign or parked proof rebuild is claimed.

The evidence directory is
`docs/evidence/2026-09-05_gate-a1-contract/`. Its final check transcript,
fingerprint, probe output and gate-negative test record are the validation
record; `spikes/gate-a1/README.md` is the reproduction entry point.
