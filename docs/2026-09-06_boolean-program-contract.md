# Admitted Boolean programs: actual setup, execution and readout

> [AGENT] 2026-09-08: historical contract note selected from committed
> `typed-consumer-sprint` at `7edc298f`. The landed definitions and theorem
> statements on main take precedence; current compatibility and limits are
> recorded in `docs/2026-09-08_typed-test-gates-landing.md`. Validation
> counts below belong to the original sprint. Unlanded references are
> identified as paths at that source commit, not as files present on main.


[AGENT], 2026-09-06. Implementation checkpoint for O1 of the approved typed
consumer sprint. The public contract composes the independently reviewed
exact initialization (`7edc298f:docs/2026-09-06_boolean-initialization.md`, historical) and
runtime invariant (`7edc298f:docs/2026-09-06_boolean-runtime-invariant.md`, historical). The full proof
implementation and its public promotion have separate independent reviews.
Fresh public-interface, runtime, ordinary CI, admission/native-fixture and
A1/A2 customer gates pass. Exact evidence is retained in
the public-program integration record (`7edc298f:docs/evidence/2026-09-06_boolean-program-integration/README.md`, historical).
B7 migration and final sprint integration review remain required.

## Contract and its domain

The admission predicate remains `BooleanTyping.TypedBooleanAdmission`, with
its independent syntax/scoping judgment and total checker equivalence. It
checks every function body, signature and declared return policy, together
with A3a's indices and initial argument shape. The old `BooleanAdmission`
still accepts its documented unbound counterexample and does not supply the
new control invariant. No native-name convention or artifact whitelist is
an admission premise.

The semantic chain now starts at arbitrary admitted argument arrays and the
real `runProgramSetupM`. Setup constructs Boolean cells and actual binding
lookups, the typed entry control and the existing machine address bounds.
The canonical setup version additionally identifies exact argument values,
false result defaults, arithmetic locations and distinct result pins through
the preceding exact-initialization API. No setup-success premise is used.

`Inv.step` covers every relational successor; `Inv.steps` propagates that
fact to reachability and `Inv.reachable_progress` supplies the next semantic
step or the sole normal terminal. The actual sequential `runConfig` may
exhaust its chosen fuel but cannot refuse in this domain. The new pool
bridge proves equality with the actual output-folding singleton driver at
the same fuel, state, initial stream and output prefix. It also pins each
pool step's event to a private step with empty picks and output. A singleton
scheduler consultation consumes nothing even if its control is at a
boundary; the proof does not generalize that fact to multi-thread pools.

This reaches `runProgramPoolOutM`, the shipped whole-program driver. It either
reads a Boolean list of the selected function's declared result arity with
empty output, or returns explicit fuel exhaustion with empty output. Panic,
other terminals and model refusals are not alternate meanings of success.
The empty output claim here follows the pool's event fold; it is stronger
than observing that `runProgramM` defaults its output field to empty.

## Claim and assumption ledger

Names below are in `GoLean.GoCore.BooleanRuntime`. Each theorem is proved in
the public modules `BooleanProgram.lean` and `BooleanPool.lean`, together with
the preceding invariant modules, over the existing total core.
They import neither Iris nor the frontend. The permitted foundational axiom
set remains `propext`, `Classical.choice`, `Quot.sound`.

| Public theorem or family | Domain, quantifiers, resource and observation contract |
|---|---|
| `setup_typed` | Strong admission for an arbitrary argument array, arbitrary setup fuel and initial choices implies actual selected-function setup and `Inv`, with result arity. Setup returns the entire original stream. |
| `setup_typed_exact_inv` | The same invariant for the exact canonical environment/state/pins and actual supplied Boolean values. The argument-count equality is retained. |
| `runProgram_typed` | Every admitted program, fuel and choice stream: actual sequential driver Boolean results at the declared arity or fuel-out. Its default output field alone is not the shipped-output proof. |
| `Control.not_blocked`, `no_abort`, `no_spawn`, `no_select`, `no_registry`, `no_flag`, `no_seq_consumption` | Structural control facts excluding the pool's park, spawn, abort, select and registry interception sites. They do not assume a future successful step. The sequential consumption projection is exactly `none`. |
| `Control.terminal_iff`, `main_outcome`, `runConfig_zero` | Driver classification of typed control, including terminal-before-fuel behavior and exhaustion of a nonterminal at zero fuel. No assumption of at least one unit of fuel. |
| `Control.singleton_thread`, `singleton_step` | Exact existing thread/pool-step equations against `stepFn`, including unchanged flags and an event with no picks/output. The step theorem explicitly excludes normal terminal control. It does not claim a generic pool converse. |
| `Inv.pool_eq_runConfig` | The output-folding singleton driver equals `(prefix, runConfig result)` for every fuel, input choice stream, detector state and initial byte prefix. It preserves the entire result/error, residual choices and prefix; fuel and output are not erased. |
| `runProgramPool_eq_sequential` | Actual admitted whole-program driver equality, lifting every sequential error with an empty output prefix. This includes the real shared setup and `loadMany` readout. |
| `runProgramPool_typed`, `runProgramPool_no_refusal` | Shipped-driver Boolean results at the selected signature's result arity, or explicit fuel-out. Both have empty output; every model refusal is excluded. Uniform over each supplied stream, without existentially reselecting choices. |
| `Inv.success_contract` | Given a normal `runConfig` result, derives a counted `Trace` of length at most fuel, the typed final invariant, actual Boolean `loadMany`, the unchanged original stream, and actual output-folding `Pool.Run`. This is a partial-correctness extraction theorem; the separate generic safety theorem has no run-success premise. |

Setup requires no positive fuel because this profile excludes globals and
package initializers. The finite-array allocator has no modeled allocation
quota; exact append/bounds proofs establish the existing machine's resource
obligations, not host-memory availability. The current platform/default and
program tables remain in `ExecState`; B7 must transport these contracts and
make immutable context/platform explicit. No second-architecture fidelity
claim follows from Boolean typing.

No general termination theorem or universal sufficient-fuel bound is claimed.
The native regression family supplies concrete bounds (64 or 128) and checks
both Boolean inputs where applicable. A functional customer may provide a
separate program-specific termination/resource witness. Calling a premise
containing its desired execution “sufficient fuel” would not discharge that
obligation. Iris ownership is a downstream resource: these semantic facts
describe actual cells and bindings but do not manufacture separation logic
resources.

## Challenges and remaining work

Seven kernel regressions cover strong admission of both Boolean
argument values, argument-dependent result readout through the shipped
driver, zero-fuel exhaustion, nested shadowing, branch return, legal reading
of zero-initialized locals/results, and terminal classification at zero fuel
with a prefix containing NUL, SOH, LF and CR and an arbitrary residual tape.
The artifact's native emission/lowering equality and differential cases
remain tested frontend correspondence, not a compiler correctness theorem.
The old binding, allocation and A1 context/choice/output counterexamples are
retained by their existing gates.

The public-interface gate checks 65 required exports and 12,196 declarations;
all twelve compiled poisons are rejected. The runtime gate checks 44 exports
and 12,135 declarations with six compiled negative controls, including private
declarations in both new modules and a trailing private test failure. Fresh
ordinary CI passes, as do full admission (1/1 differentials), native Boolean
artifact checks (3/3), A1 and A2 (fresh artifact and 3/3). All checks retain
the foundational axiom allowance and source-origin audit selection.

The preceding renderer integration's fresh full 3,607-case/394-negative run
is explicitly reused for this proof/API increment: its executable runtime
and frontend are unchanged. Its original dirty-source metadata is preserved;
it is not relabeled as a fresh full run of the new public proofs. The new
proofs and expanded audits have their own fresh gates and exact source hashes.

O2's independently checked recovery profile, reusable call/unwind logic and
both customers, the remaining panic rendering/observer obligations, B7/I1,
the C1 handoff and the closing decision packet remain mandatory. This O1
increment does not declare all of Gate A complete or the interface stable.
