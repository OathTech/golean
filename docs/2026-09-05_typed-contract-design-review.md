# Typed-consumer sprint: independent contract design review

> [Landing note, 2026-09-07, [AGENT] chunk L6 — landing audit B R21.] The
> "2026-09-06 corrigendum" paragraph immediately below was written INTO this
> sealed review artifact by the same lane that raised the finding it
> retracts (charter §6: the implementer cannot waive its own finding; a
> retraction belongs in a separate dated disposition, not in the sealed
> text). It is kept as landed by L1 so the artifact's history is visible,
> and is to be read as the sprint lane's later opinion, not as the
> reviewer's finding. The DISPOSITION of the boxing-identity item is landing
> chunk L3's (`docs/2026-09-07_land-panic-text-tape.md` §1.1, §2.2): the
> `[recovered, repanicked]` marker is deterministic in gc's eface identity,
> which the machine does not carry, so it is reified as `ChoiceSite.repanicCollapse`
> with both members gc-certified — an [AGENT] extension of BUG-087's ruling
> SHAPE under R-1, RULED [USER] 2026-09-07 at the round-24 merge sign-off
> (relayed; `docs/2026-08-31_qrow-rulings.md`). The
> corrigendum's link `2026-09-06_panic-rendering-repair.md` is a sprint note
> not on main (archive branch `typed-consumer-sprint` @ `7edc298f`).

**2026-09-06 corrigendum:** the existing R-1 user ruling already supplies
authority for a conforming rendering member; the boxing discussion below
overstates the need for a new policy decision. See the
[dated correction and separate renderer repair](2026-09-06_panic-rendering-repair.md)
for that disposition and the additional control-byte observer evidence.
The original kernel/Go probes below remain historical evidence unchanged.

[AGENT] independent reviewer `typed_contract_review`, 2026-09-05.
Baseline: `10fefeb3e6fbb3f7cb6630b8b559a9a7e7915e97`, whose runtime is
unchanged from main `471956831251e428df3a64c5b8fc7fb79cbebbfc`.
Authority and required outcomes: [approved sprint charter](2026-09-05_typed-consumer-sprint-charter.md).

**Scope: early O1/O2 statement and machine-feasibility review, not a final
implementation review.** The findings below constrain the new contracts;
they do not waive any charter outcome. No runtime source, main branch,
dependency pin, or sibling checkout was modified. Review probes use the
kickoff machine and its copied build cache.

Concrete statement set reviewed: `docs/2026-09-05_boolean-runtime-contract-design.md`
at integration commit `c53bb6a774f5cd9d05cb7c28e76a267f5e0afcf1`. It already
incorporates the sequence and hidden-binding corrections reported below.
**Disposition: the O1 candidate is suitable to implement and prove; no
remaining false statement or circular premise was found in that candidate.
O2 completion remains blocked by its disclosed rendering/identity obligations
until repaired or resolved.** This is not a statement that O1 proofs exist
or that O2 work must stop wholesale.

## Findings that change the implementation

### R1. Sequences must export declarations; blocks restore scope

The initial static proposal discarded declaration effects at `.seqn`.
That is incorrect for this machine. `Machine.seqCont` splices the inner
statement list into the governing `.seq` when their environments agree.
Only `.block` creates a scope. The following shapes distinguish the rules:

```text
seqn [seqn [initialization x]; use x]          -- x is in scope
seqn [seqn [initialization x]; initialization x] -- same-scope duplicate
seqn [block [] [initialization x]; use x]     -- x escaped its block
```

Here `use x` means an otherwise well-typed assignment reading `x`, and the
outer scope initially lacks `x`. Forgetting the inner sequence's extension
rejects the first case and can accept the second. The third must reject.
The reviewer reported this before implementation; the static author changed
the proposal to thread `afterStmt`/`afterStmts`, with blocks restoring their
input context. The final judgment/checker and regressions still require
implementation review.

`.initialization` has another contextual premise: its current environment
must equal the governing sequence's environment. A statement at the root
or as an unwrapped branch arm need not have that shape. Admission must
establish list-head placement; runtime typing must preserve the equality.
Proving only that the declaration's type is Boolean cannot establish
progress. Relevant definitions: `Machine.seqCont`, `Step.seqn`, `seqNext`,
`block`, `initialization`, and `StepFn`'s initialization arm.

### R2. Abort shape does not imply a supported terminal observation

The existing string-panic renderer refuses valid Go strings. Independent
kernel probes establish:

- UTF-8 bytes `c3 a9` ("é"), a newline, and raw byte `ff` each cause
  `renderPanicPayload` to return `none`.
- The non-ASCII panic nevertheless satisfies `Config.abort? = some ...`.
- Its `abortMsg` has no successful message result.
- A chain whose first payload was recovered and whose next payload is
  structurally equal is also unrenderable, even for ASCII strings.

The [probe source and results](evidence/2026-09-05_typed-contract-design-review/README.md)
include eleven kernel-checked facts and five direct Go probes. With the pinned
Go 1.26.5 oracle, the first panic lines were:

| Go source shape | First line, preserving raw bytes where needed |
|---|---|
| `panic("é")` | `panic: é` |
| `panic("a\nb")` | `panic: a` |
| `panic("\xff")` | `panic: ` followed by byte `ff` |
| recover, then panic with the same literal | `panic: same [recovered, repanicked]` |
| recover multiline `"a\nb"`, then panic `"other"` | `panic: a` |

These are direct Go/renderer probes, not complete frontend-to-interpreter
differential cases. Their narrow claim is sufficient to refute replacing
terminal renderability with the abort-shape predicate.

**Consequences for O2:** a profile admitting these operations cannot obtain
the charter's refusal-freedom conclusion by classifying every irreducible
panic configuration as a terminal success. It needs a justified repair or a
critical decision, with required work reported incomplete where blocked.
Adding ASCII-only or no-repanic restrictions merely to discharge the proof
would silently narrow the approved minimum surface.

The repair boundaries differ:

1. **Valid UTF-8 and newline formatting:** the existing observer compares
   the first panic line (`scripts/diff-coverage`, `panic_message`). Go's
   `runtime/error.go:printindented` preserves payload bytes and inserts a
   tab after each newline. Supporting valid UTF-8 and projecting that first
   line is determined by existing policy and is a candidate K3 repair.
   Compute the projection after accounting for suffix placement: truncating
   `"a\nb"` to `"a"` and then appending `" [recovered]"` gives a wrong first
   line. Prove the renderer projection and add a fresh differential case
   before treating this as fixed.
2. **Invalid UTF-8:** Go strings are arbitrary byte sequences. `GoString`
   can represent them, but `Terminal.panic` currently contains a Lean
   `String`, and the observation JSON uses strings. Lossy replacement is not
   faithful byte preservation. A representation/observer decision must be
   made explicitly; the current output encoder similarly refuses invalid
   UTF-8 rather than silently substituting text. This review does not
   authorize a new byte observation format or a reduced profile.
3. **Equal recovered/repanicked payloads:** Go's runtime compares interface
   type/data-word identity before collapsing panic reports. `GoValue`
   structural equality does not supply that identity. The current refusal
   is the documented BUG-004 boundary. A constant-literal probe is one
   realization, not permission to replace the identity check with value
   equality for all admitted programs. An identity representation or an
   explicit permitted-behavior argument needs its own design review; a
   genuinely unresolved policy choice follows the charter's closing-decision
   procedure.

The pinned local Go specification's `Handling_panics` section describes
termination and reporting of the panic argument; `String_types` defines
strings as byte sequences. Its runtime sources determine the probed oracle's
formatting. Source hashes are recorded in the evidence manifest.

### R3. Successful normalization is not a value typing judgment

The reviewer kernel-checked, for arbitrary `s`:

```lean
normalizeValueForTy s .bool (.int 7) = .ok (.int 7)
```

The normalizer's fallback accepts this value. `ExecState.alloc` itself also
does not normalize. Therefore neither a successful normalization premise,
nor an allocation's declared `.bool`, nor `StateWf`, proves that a cell
contains a Boolean. Keep a separate constructor-based value/store judgment.
The O1 proof can establish normalization identity for Boolean inputs and
zero-value correctness without changing this broader runtime function.
Any general normalizer repair belongs in a separate fidelity change.

### R4. The driver pins results outside its barrier frame

`runProgramSetupM` binds parameters, allocates results and returns their
locations separately. It starts the body under
`.frame [] [] [] [] .stop`; the frame contains no result roots. The generic
runtime invariant and readout theorem must carry the returned roots through
every step. Looking up result names in the final environment is both
unnecessary and wrong under shadowing: the continuation discards lexical
environments, and named result readout uses the original roots.

The setup theorem should establish the roots' order, types and distinctness,
their initial zero values, and disjointness from parameter cells. A statement
that some Boolean result cells exist somewhere is not sufficient to justify
the actual driver's `loadMany`.

### R5. Boolean surface expressions still produce address-valued machine states

Single assignment goes through `targetPlan`, `.ref`, `tgtOpK`, `rhsK` and
`storeK`. Even with only Boolean variables and Boolean surface expressions,
the machine delivers `.addr (.base ...)` as an intermediate value. A runtime
invariant asserting every `.retV` carries a Boolean cannot be preserved.
Distinguish the sorts expected by continuations: Boolean value versus a
valid root address of a Boolean cell. Track operand arities/order and the
target/value count through the assignment spine.

### R6. Calls and recovery require more than typed environments and heaps

An O2 invariant needs at least the following distinctions:

| Runtime component | Required fact |
|---|---|
| Program context | Every callable `FuncId` resolves to the checked signature/body; context remains tied to the admitted program. |
| Root locations | The referenced root is a value cell of the promised type; mere address boundedness does not exclude payload cells or a wrong value type. |
| Captures | Captured Boolean references refer to live Boolean root cells. Alias between handlers is permitted and needed. |
| Function values | Target identity, capture types/count and remaining argument signature match; normalization alone cannot check them. |
| Call arguments | Evaluated prefixes and pending operands have the right types and order; captures precede explicit arguments at `enterFrame`. |
| Ordinary call frame | Pinned result count/types match the caller's target plans; target expressions are typed in the saved caller environment. |
| Deferred frame | The callee is checked, but its result locations are intentionally discarded. Do not apply ordinary-result-target equality to this frame. |
| Driver barrier | Its frame is targetless/resultless while driver-owned readout roots remain external. |
| Deferred-call chain | Registration evaluated callee/arguments already; entries are valid invocations in LIFO order and attached to a real enclosing call frame. |
| Panic state/marker | Chains are nonempty, payloads have the admitted representation, and recovered flags/marker positions support the terminal contract. |
| Recovery | The value and the rebuilt continuation returned by `recoverResult` are both typed; marking a suspended chain is the semantic effect. |
| Return signal | Only `.ret` occurs in this profile; a well-shaped call frame eventually catches it. A signal at `.stop` is a refusal. |

Ordinary targetless frames with pinned results have no exit rule. Deferred
invocations intentionally replace the returned result-location list by `[]`;
the top-level driver does likewise for a different reason. A frame invariant
that conflates those three roles either accepts a stuck ordinary call or
rejects required driver/defer states.

`recover()` outside the effective direct deferred handler is valid and yields
nil. The second fixture must exercise it. Its typing rule must allow both
nil and a supported boxed payload, while its functional rule distinguishes
the actual continuation walk. A second `recover()` in the same handler must
observe the recovered flag. No unconditional context substitution law may
be introduced to avoid proving that update.

Captured pointers need a stronger runtime fact than their Go type:
`.pointer .bool` has `.nil` as its zero value. A safe root-reference rule
must derive non-null/live-root information from capture construction or an
explicit call precondition; it cannot derive it merely from type equality.
For aliases, semantic typing shares facts about one cell. Iris resources
provide the separate exclusivity needed to write that cell; handing each of
two deferred handlers independent full ownership simultaneously is invalid.

### R7. Visible lookup coverage misses hidden environment locations

The first concrete `BooleanStore.lean` draft defined `EnvRoots` by
`forall name loc, env.lookup name = some loc -> BoolRoot state loc`, with a
comment claiming coverage of saved outer scopes. This does not see shadowed
bindings. The reviewer kernel-checked the following counterexample over the
kickoff machine:

```text
heap = [value bool false]
env  = [[("x", base 0)], [("x", base 999)]]
```

Every successful lookup finds the valid Boolean root at 0, yet the environment
contains an out-of-bounds location. In particular `LocalEnv.locSup env` exceeds
the heap bound, so the proposed visible-root property does not establish
`MachineWf`. A same-scope hidden duplicate has the same problem.

Strengthen the property to quantify over every stored binding occurrence
and derive its lookup consequence, or carry a separately proved structural
environment bound. The draft store lemmas themselves did not claim the
false implication; this finding concerns using their current predicates as
the complete invariant and their overly broad comment. It was sent to the
runtime author while the draft was still being developed. The initial
`NamesPresent`/`allocDecls_bool` lemmas also intentionally provide existence,
not exact initial-value/identity/order/distinctness facts; the full setup
contract needs those additional facts.

Before this review was finalized, the runtime author strengthened `EnvRoots`
to every binding occurrence in every scope and proved a separate
`EnvRoots.lookup` consequence. The reviewer inspected that revised definition
and lookup lemma. This resolves R7's predicate/comment defect at design level;
the complete `inv_machineWf` theorem is still an implementation obligation.

## Minimum precise contract statements

The following are schematic interfaces, not claims that these Lean names
already exist. They make the promised quantifiers and dependencies explicit.
Equivalent proof decompositions are acceptable; erasing an obligation is not.

### Admission and initialization

Define `TypedProgram` independently of execution, checking every body and
signature. Define `Entry` separately using actual lookup and independently
typed initial arguments. Require a new checker/judgment equivalence; leave
A3a `BooleanAdmission` and its unbound counterexample unchanged.

For O1's no-globals/no-initializer profile, setup should work for **every**
fuel and choice stream; setup itself has no fuel-consuming phase left:

```text
TypedAdmission p name args ->
  forall fuel choices, exists f env state resultLocs,
    findFunctionIn? p.funcs name = some f /\
    runProgramSetupM fuel p name args choices =
      ok (exec f.body env (frame [] [] [] [] stop), state, resultLocs, choices) /\
    InitialBindings p f args env state resultLocs /\
    RuntimeInvariant p f.results resultLocs
      (exec f.body env (frame [] [] [] [] stop)) state
```

`InitialBindings` must identify the actual parameter values and declared
result zeros, fresh locations/order, lookup behavior and immutable context.
The fresh driver state is not an arbitrary supplied heap. Auxiliary lemmas
may be parametric over a prior heap, but the headline setup theorem must
discharge their premises from the actual driver's initial state.

The dense allocator appends to an unbounded Lean array in this Boolean
path. Do not invent an allocation-capacity premise it never consults.
If later platform/allocation work adds such a premise, state it independently
and prove the bound, rather than defining capacity as successful execution.

For O2, make the permitted entry value sorts explicit. Captured-reference
helper signatures can be checked and safely called internally even when
those helpers are not legal fresh-driver entries with externally supplied
addresses. Prove every admitted entry's setup; do not assume fresh external
references point into an empty heap.

### Invariant, preservation and progress

The Boolean proposal's all-Boolean heap plus environment coverage is a
workable store foundation. Environment coverage must describe actual lookup
at valid roots; continuation typing must supply every saved environment,
expected value sort and pending statement/operand obligation. Pinned driver
result roots are permanent invariant parameters.

```text
RuntimeInvariant p resultTypes resultLocs c state ->
  Step c state c' state' ->
  RuntimeInvariant p resultTypes resultLocs c' state'
```

This quantifies over **every** relational successor. If an existential heap
typing map is used, allocation extends it and proves old locations retain
their types. Defining the invariant merely as reachability makes this
closure tautological and does not supply the required typing/progress facts.
Defining it as all-future safety merely moves the goal into setup. A
reachable index is permissible as extra bookkeeping only when independent
structural facts and their initialization/projection proofs do the work.

The terminal-aware progress conclusion must be at least:

```text
RuntimeInvariant ... c state ->
  c = next stop \/
  (exists first rest message,
    c.abort? = some (first, rest) /\ abortMsg state first rest = ok message) \/
  exists c' state', Step c state c' state'
```

For O1 the abort disjunct is impossible. For O2, it requires renderability,
not just nonempty panic shape. Empty panic chains and other relation-silent
control shapes are excluded by the invariant, not classified as success.

Derive `MachineWf` from the new invariant. Existing
`step_complete_any_wf` supplies executable progress for every choice stream
from relational progress, potentially choosing a different successor.
`stepFn_sound` plus all-successor preservation then carries the invariant.
Ordinary `step_complete` supplies only an existential stream; it cannot by
itself justify a universal executable safety claim.

For O1, the existing `execStmtLoop_ok_or_fuelOut` can be instantiated after
proving its reachable-progress premise. That premise must not remain as an
unproved public admission assumption. O2 needs a terminal-aware extension:
the old theorem excludes unrecovered panic by design. An abort configuration
still requires a driver iteration to render; zero remaining fuel can report
exhaustion there. Do not turn an abort-shape witness into a zero-fuel panic
observation.

### Readout, whole-driver outcome and bounds

Prove successful `loadMany state resultLocs` and result-type/length agreement
from the preserved external result-root invariant at normal termination.
This rules out readout refusal separately from step refusal. Connect that
lemma through the real program driver, not an invented loop around `Step`.

The quantified executable safety statement should classify each bounded
run under each choice stream as a typed normal result, an admitted Go
terminal observation, or fuel exhaustion. Refusal is not an allowed fourth
success class. Keep residual choices in trace statements. Neither existential
erased reachability nor a successful selected stream proves this statement.

The final customer theorem refers to the output-bearing pool driver.
Sequential readout alone does not establish that theorem. Derive the
singleton/no-registry-boundary transfer obligations structurally for the
profiles, or supply the explicit separate witnesses permitted by the
charter. Preserve byte output and the panic/refusal/exhaustion distinction.

Finite syntax and an acyclic direct-call graph can support a usable resource
bound, but acyclicity must include closure targets and deferred invocations,
not only immediate `Stmt.call` edges. Independent bounded termination
witnesses are permitted. A bound defined as the least fuel at which the
desired whole run succeeds, without a separate existence proof, is circular.

## Scope and negative-case acceptance criteria

The static author proposes checking GoCore's actual `.block` scope even for
a function's outer body block. Go's source parameters/results share the
function-body lexical scope, but GoCore's constructor creates a runtime scope
and has no tag distinguishing that source role. This distinction must remain
explicit: the proposed judgment proves scoped GoCore typing, not equivalence
to `go/types`' source declaration rules. Native fixture comparison is the
tested bridge. Source name-generation conventions cannot fill this gap as
semantic axioms.

Fresh formal storage keys can conservatively exclude valid source signatures
with repeated blank parameters if the emitter retains `_` keys. Report those
as out of the declared profile, not malformed Go. Within each actual admitted
IR scope, duplicate declarations must still reject. Resultful fallthrough
also requires an explicit structural return policy even though the machine
allows it operationally. A valid declared but never assigned Boolean is
zero-initialized and must remain admissible.

Minimum adversarial coverage before implementation acceptance:

- nested-sequence extension, same-scope duplicate after sequence, block escape;
- root/branch-arm declaration without a governing sequence;
- unbound reads and writes, duplicate formal storage keys, resultful fallthrough;
- legal nested shadowing, parameter-dependent result, both-branch result,
  zero-initialized local and named result;
- invalid capture count/type, wrong direct-call arity/results, dangling or nil
  purported root captures, shared live capture roots;
- ordinary result-bearing call versus result-discarding deferred call;
- direct recovery, ineffective nested-call recovery, repeated recovery, LIFO
  alias-sensitive handlers, panic during unwind and actual terminal rendering;
- fuel immediately before abort rendering, normal readout from the original
  named-result cell after shadowing, preserved A1 choice/output counterexamples.

## References inspected and transferable lessons

No reference was added as a build dependency or rebuilt by this review.

| Checkout and revision | Files inspected | Relevant lesson |
|---|---|---|
| refined-cerberus `c2ebeb7915da06461aa2bed8f898a7ca59c883b2` | `cerberus-heaplang/CerberusHeapLang/{Wps,EnvLaws,Adequacy,TotalAdequacy}.lean` | Use actual environment lookup laws; separate procedure specifications and ambient control; close adequacy over the shipped driver; separate all-fuel safety from a total budget theorem. |
| RefinedC `25f706d417df2b18b23c5cbadde46468c1b1262c` | `theories/caesium/lifting.v` | Lifting carries a coherent state interpretation and quantifies over every operational successor; runtime typing/ownership are distinct obligations. |
| BRiCk `eee838e797ee636dd1f3de451ef7b2751018f313` | `rocq-skylabs-brick/theories/lang/cpp/logic/wp.v` | Statement exits have explicit continuation predicates; the inspected logic explicitly does not model C++ exceptions, so it supplies no Go recover law. |
| Archived GoLean `7440bf705a87b052243ff36280b677f4100b6a66` | `proofs/GoLeanProofs/Laws/Bind.lean`, `Frame/Plug.lean` | The old bind proof was barrier/context-premised. Its map-pruning and old panic-terminal premises belong to an older machine; neither an unconditional bind law nor all old premises can be copied. |

The existing [A1 contract report](2026-09-05_gate-a1-contract.md),
[A2 independent review](2026-09-05_iris-customer-review.md), and
[interface review](2026-09-05_semantic-interface-review.md) were also checked.
They already distinguish ordinary Iris framing from Go continuation
transport, prove selected customer behavior through actual readout, and
disclose missing generic typing/setup. Their PASS results do not establish
the sprint's stronger contracts.

## Review disposition

O1 is feasible on the inspected machine without changing Boolean execution.
The sequence-effect correction and the richer continuation invariant are
necessary and are represented in the reviewed candidate. It correctly
requires `inv_machineWf`, all-successor `inv_step`, a universal setup result,
and a derived reachable-progress premise rather than an assumed one.

The following remain **implementation acceptance obligations**, not requests
to change that candidate's direction: prove exact parameter/result initial
values and fresh-root identity/order; implement structural bounds for hidden
bindings; prove sequence cursor/effect and continuation-spine preservation;
establish actual-driver readout/output transfer; and run the full admission,
consumer and adversarial gates. `BoolHeap`/`EnvRoots` helpers alone do not
close any of these larger obligations.

O2 has concrete **blocking completion findings**: terminal renderability for
the approved string-panic surface and the known equal-payload identity
boundary. These must be
resolved or reported as critical unresolved work; they cannot be hidden
behind a weaker progress predicate. No final proof implementation is
approved by this document. Later reviews must inspect the actual exported
statements, proofs, full profiles and customer reuse against these criteria.

### Initial static-source follow-up

The reviewer also read the first implemented `BooleanTyping.lean`, its new
tests/artifact fixture and gate script in the author's worktree. This was a
source review while the author was still running gates; it is not a final
static-lane PASS. No additional defect was identified in the independent
typing/checker definitions, sequence effects, branch restrictions or return
policy. The tests include the sequence counterexamples above.

Two follow-ups were requested before acceptance: (1) strengthen the native
shadow fixture to read the outer `x` in inner `x := !x`, so it challenges
initializer scope instead of only block exit; the emitter already contains
the required shadow-capture hoist, so initialization-before-assignment alone
is not a demonstrated bug; (2) extend the post-import dependency audit and
compiled poison controls to the new module and test helpers, since the first
dedicated gate only built and elaborated them. Their eventual results belong
in the implementation evidence and subsequent review.

The integrator explicitly owns public-facade promotion, all new module-origin
selectors, export audits and compiled poison controls for the combined
static/runtime/setup surface. This is an **owed integration obligation, not
a waiver**. A branch-ready static increment can be reviewed within that
boundary, but it must not be advertised as complete O1/O3. A source-text CI
scan is not a substitute for the post-import dependency audit.

Follow-up evidence: the static author strengthened the shadow fixture and
ran its full dedicated gate. The reviewer inspected
`typed-boolean/artifacts/boolean-typing/static-gate-final.log`: fresh complete
native-artifact comparison passed, `Shadow` returned false as Go requires,
and all three executable differential cases passed. This closes the
initializer-scope witness request for that tested artifact; no fidelity bug
was found there. The author is also adding a static post-import audit and
poison controls; those later changes are outside this initial source review
and do not remove the integrator's final combined-surface audit obligation.
