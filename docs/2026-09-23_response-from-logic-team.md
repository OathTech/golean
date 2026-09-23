<!-- VERBATIM COPY for GoLean's records. Source: golean-logic repo, branch docs/upstream-response-0923, commit a9950b2, file docs/2026-09-23_response-to-golean-proposal.md, sha256 a1008badba858724bfc3f1f32a117ca81c50fee19fb1869aec37898fd86c5067. Copied unchanged by the [AGENT] coordinator 2026-09-23; provenance tags inside are the logic team's own ([USER] = their user, [AGENT] = their agent). Answers the proposal docs/2026-09-23_proposal-to-logic-team.md (this branch @ 6f1256f6). -->

# Logic team's response to the GoLean transition proposal

2026-09-23. To the GoLean semantics team.

**[USER]** Requested a response endorsing the plan or requesting changes,
including anticipated needs of the Go-to-Raft-mirror proof.
Subsequently clarified that the reasoning structures must be general: Raft
is the first target and challenge, not the model for the logic's design.
**[AGENT]** The recommendations below are the logic team's technical response;
they do not create new user rulings, dispatch implementation, or authorize a
merge, push or dependency change.

## Recommendation

We endorse **one batched breaking window and one downstream re-pin**, the
shared sequential/pool event label, native method promotion, numeric locals,
and the continuation cleanup. We also support block-entry allocation, subject
to the lifetime and observation conditions below. Please revise the execution
statement before implementing it: the proposed `LRun` loses the state at
failure, omits terminal choice consumption, and cannot express unfinished
prefixes. Those are material gaps for our intended simulation, not optional
conveniences.

Use **E6 → label and execution bridges → P → C3 → B6 → C4** as the dependency
order, with E6 opening the window. This agrees with your later rulings
addendum, which supersedes the note's recommendation to put E6 outside it.
Independent preparatory work can overlap; dependent changes need a combined
candidate. C3 is a useful simplification, not a prerequisite for our CPS bind.

The aim is to prove that every admitted concrete Go execution has matching
behavior in the hand-written functional mirror, then use the mirror's safety
theorems and our adequacy result. This requires more than agreement on normal
final values. We need ownership-preserving calls, retained effects on failure,
and observations at the right execution prefixes. Reverse realization can be
useful, but equivalence of all mirror behaviors and all Go behaviors is not a
precondition for the forward safety result.

The reusable structure is **owned concrete state → functional model →
execution property via adequacy**. The abstract state type, representation
predicate, model computation, environment contract and observation projection
are client parameters. No Raft state, protocol phase, field name or event
vocabulary should be built into GoLean or this logic. The examples below
exercise general requirements: framing, effects, callbacks, exceptional
outcomes and prefix refinement. Another functional model should use the same
interfaces without requiring a core change.

Allow concrete administrative steps to stutter between meaningful source
boundaries. A functional mirror need not reproduce the machine's stack,
addresses or each evaluation step. The representation and simulation proofs
justify that abstraction, including which intermediate effects remain
observable; it is not obtained by equating the two state types.

## 1. What we depend on today

Our accepted F2 baseline is logic `b2c37c1492a16de317de40b2c487f478c8b9c6a1`,
still pinned to GoLean `61958f2ee03047d13fec320266be22a1a759075c`.
We agree with your diagnosis of the direct `stepFn`, continuation, frame-entry,
heap and decoder dependencies. Current record ownership is restricted to
one-field records, and checked function admission excludes methods. Those
are limitations of our present logic, not requests to restrict your semantics.

One correction to the prioritization: the live F0–F2 backend is
`L:Logic/Language.lean`'s **refusal-observing `Safe` adapter**. It includes an
error-to-fault transition for every executable choice tape. Its adequacy and
`L:Logic/ProgramAdequacy.lean:closed_program` already exclude non-fuel errors
without assuming successful execution for our initialized bounded fragment.
The older `L:Readout.lean:adequate_program_result` still has the `hr`/`hop`
premises you cite; it is not the strongest current closing theorem. The open
work is permitted terminal outcomes, observable prefixes and the broader
program/pool bridge. Please retain universal refusal exclusion when porting
the current clients; relational existence of one successful successor is weaker.

All fourteen native fixture directories should be re-lowered. Your claim that
none triggers `unseq` remains a hypothesis until that check, including our
generated positive variants. In particular, do not equate our currently
admitted source fragment with every feature present in the fixture corpus:
general panic/recovery remains future work in the live source calculus.

## 2. Required changes to the execution statement

We want the small-step `Step` and a counted, choice-threaded **labelled prefix
closure with arbitrary endpoints** as the primary proof interface. Define
completed runs by closing such a prefix with a classified outcome. `LRun` can
be a useful derived interface; it should not be the only carrier, or replace
the one-step relation underlying Iris.

The shape below is a specification sketch, not Lean code or a new interpreter:

```text
Prefix ctx n (c, s, ch) labels (c', s', ch')
Finish ctx (c', s', ch') terminalLabel outcome
```

`Prefix` needs reflexivity, composition/splitting, exact executable iteration
agreement, and erasure to existing reachability. `Finish` needs the actual
driver's classification and any final effects/choices. Five corrections matter:

1. **Retain the endpoint state and residual choices on failure.** A panic
   outcome must expose the store after preceding writes, not just a rendered
   `Terminal`. An enriched proof carrier with a projection to today's runner
   result suffices; the CLI need not expose its heap. The mirror uses
   `ExceptT Fault (StateM Context)`: `Progress.SentEntries` writes `Next`
   before `Inflights.Add` can panic. That write must survive our proof.
2. **Account for terminal work.** On current main, `stepFn`'s abort arm calls
   `abortConsult`, may consume a `repanicCollapse` choice, and calls the
   fallible `abortMsg`. `Config.abort? = some ...` alone does not establish a
   renderable terminal. A zero-step `aborted` constructor with no final pick
   or rendering premise is insufficient. Include these events in the enriched
   terminal result or a separate proved terminal transition. Cover named fatal
   outcomes/deadlock where claimed; sequential blocking and pool deadlock have
   different environmental conditions.
3. **State exact fuel conventions and prove prefixes independently of
   termination.** The proposed terminal iff lacks a fuel bound. Currently a
   normal/blocked configuration is classified before the fuel check, whereas
   an abort requires a positive-fuel `stepFn` call. Preserve that distinction
   or disclose a deliberate change. Replace “fuel-out iff every run is
   longer” with a statement about the fixed tape's actual executable prefix
   and absence of classification within the budget. Quantifying only over
   completed runs is vacuous for divergence. Earlier observations must remain
   available when a later computation exhausts fuel or never returns.
4. **Replay choices, not just a number of pops.** Connect every recorded
   site/bound/value to the actual consultation, including modulo selection,
   empty-tape default, bound-≤1 no-consumption behavior, and terminal draws.
   A list of picks is not literally a count of removed list elements when the
   input tape is empty. Prove that no unrecorded consultation can affect a
   step. Empty picks alone is not a tape-independence theorem without that
   coverage result. Provide exact fixed-tape soundness/completeness, and the
   relation-to-executable witness direction needed for arbitrary legal steps.
5. **Keep refusal separate and prove the bridge without hiding it.** Prefer
   unconditional interpreter/prefix correspondence that reports refusal,
   terminal and fuel separately, followed by a corollary using a proved
   reachable-state domain invariant. Do not require “all executions succeed”
   to connect adequacy to the interpreter. `StateWf` supplies heap invariants;
   it does not alone establish support for arbitrary syntax, call targets or
   rendering. Our fragment rules will discharge the appropriate domain facts.

For the program theorem, keep initialization, result-location readout, output
and residual choices in one composable account. Supply a clearly scoped
single-goroutine embedding first. If administrative pool steps change the
budget, use a proved cost translation or stuttering relation; do not silently
assert equal fuel. A structural “no registry interaction” premise is useful
for the first domain, but full single-goroutine registry support remains a
separate obligation. Full concurrent scheduling need not block this window.

## 3. Labels and client-defined observations

The record **`{trace, picks, out}` is sufficient for our planned clients**,
with ordered contents in each field and ordered labels across steps. We do
not presently need a total interleaving of all three channels inside one
step. Document that limitation rather than invent an instrumentation order.
Prove the sequential-to-pool projections, including attribution and terminal
events, and preserve the old silent projection. A later Iris adapter can
project a silent label to `[]`; emitting `[emptyLabel]` at every step would
break the current notion of an observation-free pure step.

Memory accesses and scheduler picks are semantic evidence, not automatically
the public observations of the Go library. In particular, **Ready is not
stdout**. The mirror observes the actual batch returned after `acceptReady`,
before persistence, reports and `Advance`. The logic must derive its abstract
event from that returned value and ownership at a real execution boundary.
Please provide inspectable configuration/store endpoints, return/result
readout and generic call/return boundaries from which we can prove this cut.
There is no request for a Raft-specific `Ready` event in GoCore. A ghost log
or `StepLabel.out` alone would not establish the required correspondence.

Initialization also needs an explicit scope. Today's `initPrintRefusal?`
deliberately refuses printing during package initialization. Adding output to
sequential steps does not itself remove that restriction or connect setup's
output/choices to the program trace. State whether the new bridge includes
these effects; otherwise retain the named limitation. Our first helper can
use the existing restricted initialization profile.

## 4. Conditions on the representation changes

**P / methods.** Preserve receiver evaluation once, pointer versus value
receiver adjustment/copying, embedded-field traversal and nil behavior,
package-qualified method identity, and method-value receiver capture at
creation rather than invocation. Keep direct-recover eligibility and deferred
receiver/argument capture correct when wrappers disappear. Expose declaration
lookup and the resolved receiver path/entry equations: our upcoming direct
`Progress.MaybeUpdate` proof should use ordinary call rules, not prove a
whole dispatch engine again. Promotion itself is not required by that pilot,
but its refactor must preserve the direct path.

**B6 / numeric locals.** Endorse declaration IDs with a debug/source table.
Distinguish a lexical ID from each activation's heap location. Recursion,
re-entered blocks, loop variables and escaping captures still require fresh
runtime identities where source semantics does. Preserve shadowing, same-block
short-declaration reuse, argument/result slots and capture mappings. Do not
make numeric IDs stable across source edits an API promise; provide checked
metadata so our source admission reconstructs bindings after renumbering.
Our logical names remain separate from runtime slots.

**C4 / block allocation.** Allocation of storage and execution of an
initializer must stay separate: initializer calls, reads, failures and binding
visibility remain at the correct source point. Preserve captured/escaped
cells after lexical exit, distinct dynamic activations, defer references,
named result storage and the specified per-iteration variable behavior.
Please expose block layout/allocation, lookup preservation, zero-value/type
normalization and freshness/frame lemmas so we can replace `initialCells`,
`declareRoots` and result-address arithmetic compositionally.

“Up to heap isomorphism” needs a scoped statement: hoisting can create unused
cells before an early return, so intermediate heaps may require an injection
with extra private cells and stuttering, not a bijection of their whole
contents. State which observable domain admits address renaming; audit any
address-sensitive formatting/conversion or other escape before making a
global preservation claim. Pointer equality and aliasing must be preserved.
We can accommodate changed allocation order and fuel; a changelog alone does
not justify lifetime or observation changes.

**C1 / memory.** Please expose the normalization premise of allocation and
the concrete read/write/frame laws of the memory module. Our resources own
heap cells; native data operations must keep their relation to those cells.
Whole-record ownership is a reasonable first policy. We do not need fine
field permissions immediately, but later slice borrowing needs the relation
between headers, backing storage, sublocations and disjoint updates. Avoid
making the first migration depend on an unexplained global well-formedness
assumption in every client; give the initialization/preservation lemmas and
local operation premises from which the logic maintains it.

## 5. General simulation requirements, exercised first by Raft

These are prioritized semantic interfaces and corpus requests, not a demand
to implement all Raft or F3/F4 features in this window. GoLean owns executable
semantics and their mathematical bridge; this repo owns generic SL rules and
adequacy; downstream proofs own Raft representations and the simulation.
The mirror cleanup can finish without acquiring new Go proof obligations.
Use small non-Raft fixtures for generic logic acceptance, then instantiate
the same rules on the actual downstream code. Passing a miniature fixture
must not be reported as a proof of the Raft implementation.

| Priority / client | What the proof will test | Request to GoLean |
| --- | --- | --- |
| First: `Progress.MaybeUpdate` | Multi-field receiver related to a functional value; stale/equal input unchanged; Boolean result; Match/Next/pause updates; maximum UInt64 wrap; Inflights and unrelated state framed; two successive calls from initialized ownership. | Direct method entry/readout, field paths/copies, declared integer widths and wrapping arithmetic, allocation/normalization/frame laws. Lower the actual helper and dependencies before deciding the necessary fragment. |
| First exceptional test: `SentEntries` | `Next` remains updated if `Inflights.Add` panics; later pause update does not execute; deferred cleanup still follows Go control. | Prefix endpoints and terminal state, exact call/return/unwind/terminal equations. Keep Go returned errors, panic and tool refusal distinct. |
| E2: `readOnly.recvAck` | Nil/empty context does nothing; ≥8 bytes decode little-endian; missing map key defaults to zero; max update; input bytes and unrelated entries preserved. | Bounded slice reads, lengths/bounds and byte-to-word shifts/conversions, actual `encoding/binary` call handling, map lookup/store and nil-map behavior. Lengths 1–7 remain an explicit panic case: the present mirror refuses them, so an initial restricted-domain theorem must say so. |
| Early design: Ready return then failure | Observe the returned committed batch before a later failure or unfinished operation; internal `commitTo` is not that observation. | Generic return/result and labelled prefix bridges, without requiring eventual completion; copying/borrowing behavior of returned slices remains explicit. |
| Next: slice/ring-buffer helpers | Header copies share backing; append may reuse or replace backing; reslicing retains aliases; copies may overlap; inactive inflight slots and wrapping cursors matter. | Concrete header/backing and path equations, length/capacity/nil distinctions, bounds failures and access labels. We prove when a list-valued abstraction can forget capacity or allocation identity. |
| Next: callbacks, Storage and timers | Stored step/tick dispatch, visitor callbacks that can mutate/fail, Storage request/reply/error identity, randomized timeout draws. | Generic call-target identity and effect boundaries, inspectable interface/function-value dispatch, explicit supported external-call contracts or named refusals. No replacement of real bodies by assumed postconditions. |
| Later: loops and concurrent integration | Symbolic lengths, map iteration, recursion, Ready/persistence scheduling and asynchronous storage. | Stable loop/return/choice semantics now; stronger iteration/pool/access-granularity proofs when those clients arrive. No termination, fairness or full-Go concurrency claim from the current bounded clients. |

Two cross-cutting requirements deserve attention now:

- **Aliasing must be proved away or represented.** The mirror uses immutable
  Progress values and lists for maps/slices, and does not model arbitrary
  shared mutable receiver graphs. Our representations must establish the
  ownership/borrow conditions under which these values are faithful. Native
  pointer, map and slice sharing must stay real in GoLean. Preserve nil versus
  empty where observed, unique-key map updates, and exact byte content. We
  cannot assume that every pointer reachable from a receiver is exclusively
  owned, nor duplicate an owned graph when the mirror copies a value.
- **Couple choices by meaning, not raw tape equality.** The mirror's timeout
  draws carry node/operation/occurrence/site/bound/value. GoLean's `Choices`
  also drives unrelated evaluation and scheduler choices, defaults to zero
  on exhaustion, and suppresses bound-≤1 records. These are different
  protocols; randomness from `globalRand.Intn` also needs an explicit supported
  implementation/environment contract, not an assumed scheduler pick.
  Preserve enough call and choice evidence to construct the matching mirror
  draws, including deterministic bound-one calls. Quantify over every allowed
  concrete choice/environment execution, then exhibit a matching mirror run.
  Map traversal can be erased only after an order-insensitivity proof; the
  mirror's sorted `Visit` also rereads values after callbacks.

The first initialized pilot must construct a satisfiable representation and
export a theorem on actual GoLean executions through adequacy. A theorem
assuming an arbitrary `Rep` or an arbitrary source-call relation would not
test this bridge. Native lowering fidelity, the logic theorem and the
mirror-to-protocol theorem retain separately stated pins and assumptions.
Interpreter/relation agreement alone is not a proof of the Go frontend or
compiler, and the final end-to-end claim must disclose that boundary.

## 6. Stable declarations, equations and migration evidence

**Yes to `BridgeSet.lean` and yes to equation lemmas over the final labelled
interface.** Keep the proposed set and add these families, selecting concrete
names as their final statements settle:

- `stepFn`, `stepFnIter`, `iter_iff_trace`, and new labelled prefix
  composition/erasure/executable correspondence; terminal classification,
  rendering/consumption and output-projection bridges.
- `runProgramM`, `runProgramPoolOutM`, their setup/readout composition and
  the precise sequential/pool cost or stuttering correspondence.
- `Choices.consumeAtE` and its replay/projection laws; exact per-step and
  terminal consultation coverage.
- `loadLoc`, `storeLoc`, `Store.alloc`, `normalizeValueForTy`, their
  lookup/frame/freshness/normalization laws; C4 block-entry/environment laws.
- Final method resolution/receiver-entry, parameter/result/capture layout,
  `pushDefer`, frame exit and recovery boundary contracts. Retired wrapper
  helpers need named replacements in the migration table, not fake aliases.

Prioritize equations for call/frame entry and exit, defer registration and
draining, return and panic/recover; then sequence/block/local initialization,
branches, scalar loads/stores, record/map operations and allocation. Use
symbolic continuation/environment/state parameters and explicit operation
premises. Provide a named rewrite set or `simp only` examples rather than
uncontrolled global unfolding. We do not ask you to prove our Iris rules.

Statement examples catch type drift; they do not detect changed definitions
with the same type. Gate the **semantic equations** and a small independent
consumer too, and include all fixtures/imports in the gate. No proof holes,
extra axioms or decision bypasses. At the re-pin offer, include changed
constructors, wire schemas, choices, allocations, fuel, refusals and theorem
premises, plus the normal differential/certification receipt.

Start the statement and inventory work now; update the changelog through the
window and freeze its exact target commit at close. An isolated clone dry run
is useful within the owner's access policy, using independent dependency
checkouts/caches and capped builds. First inventory the fourteen fixtures and
variants against the new lowering, then report build breakage honestly. A
successful port is accepted on our side only after `scripts/check`, the
initialized/all-choice theorems, native edit/mutation controls and all three
isolated consumers pass. A dry-run `lake build` is useful evidence, not that
acceptance gate. Leave the historical package's separate pin and status intact.

## 7. Direct answers to your ten questions

| Question | Response |
| --- | --- |
| 1. Window/order | Endorse the batch, with the semantic conditions above. E6 first, then label/bridges → P → C3 → B6 → C4. |
| 2. E6 placement | Inside the window as its first item, as your later addendum proposes; no extra re-pin or artificial delay. |
| 3. Label | Shared `{trace, picks, out}` record; exact per-channel order, terminal effects and projections. Ready observations use proved execution cuts, not printed bytes. |
| 4. Stable set | Keep your list and add the prefix, terminal, choice, memory and entry/layout families in §6. Pin statements and equations, not only names/types. |
| 5. Equations | Yes, over the final labelled shape; prioritize control/calls/defer and owned-memory operations. |
| 6. First bridge | Sequential terminal-aware prefixes together, then initialized single-goroutine readout/embedding. Full pool later. Keep `Step` primitive; derive `LRun` from a prefix closure. |
| 7. Records timing | Now for the contract and inventory; final exact changelog and evidence at the offer. |
| 8. Deferrals | Agree on NaN, parked typed profiles and no upstream Iris `Language` spike. Correct the proposed confluence claim; retain the concurrency reduction debt explicitly, as below. |
| 9. Corpus | Keep the current corpus and add the staged examples in §5. Slices/bytes and direct methods are near-term; broader strings, interfaces/callbacks, loops and `range` follow actual lowering needs. Goroutines/select are later, not assumed necessary for `recvAck`. |
| 10. Re-pin timing | Recommend a dedicated migration after the completed offer, preferably before the actual receiver/E2 simulation proof, with the helper as the first consumer of the new pin. Continue independent design or bounded generic work meanwhile. No calendar deadline or interim pin is agreed; revisit only if a concrete pilot blocker makes waiting more expensive than a second port. |

The proposed **“DRF `unseq` confluence” is false without additional
independence hypotheses**. Your own `Tests/unseq-wire/src/w1/main.go` has one
goroutine, a mutating closure and an unordered read, with permitted results
`{1, 2}`. Defer a correctly scoped commutation/confluence theorem, and preserve
the actual choices meanwhile. A deterministic mirror needs a per-client
independence argument or explicit matching nondeterminism even before F4.

Deferring access-granularity reduction is acceptable for the owned sequential
pilot. It is not irrelevant to the eventual end-to-end result. Keep
`NPDRFReduction` explicitly unusable as presently stated; before claiming
concurrent concrete-Go coverage, supply a sound observational reduction or
use the finer semantics directly with an adequate bridge. Registry-scheduled
agreement or a differential corpus alone does not close that obligation.

## Inspection record

This response is based on read-only local source inspection, not a re-pin,
fresh lowering, build, universal fidelity proof or newly proved theorem.

- GoLean proposal/rulings branch `docs/roadmap-customer-alignment-0922` at
  `6f1256f6af24f7991839ffd274e5325964e4ceaf`; note
  `docs/2026-09-23_proposal-to-logic-team.md`, SHA-256
  `523f39f850ab340ef6b610595f3fc4298ff5a300bdc214810b601d9846367605`.
- GoLean main inspected at `9269912e639c7c099d4766a943ece9e39bdafb3c`.
  `G:` means its `GoLean/GoCore/`: `StepFn.lean` (`stepFn`,
  `execStmtLoop`, `initPrintRefusal?`), `Trace.lean`, `Machine.lean`
  (`Config.abort?`, `abortConsult`, `abortMsg`, `abortLeftover`),
  `State.lean` (`Choices.consume`, `consumeAtE`), `Ops.lean`,
  `StateWf.lean`, `Multi.lean`, `ProgramTrace.lean`, `NPDRF.lean`.
  Upstream plans and `Tests/unseq-wire/src/w1/main.go` are repository-relative.
- `L:` means logic `packages/golean-iris/GoLeanIris/` at the baseline above.
  Additional anchors: `Logic/Source.lean`, `Logic/Binding.lean`,
  `Logic/FunctionInterface.lean:Checks`, `Data/Record.lean:Schema`,
  `Logic/AllocationRules.lean`, `Call.lean`, `Logic/Readback.lean` and
  `Logic/ProgramSetup.lean`.
- Raft mirror primary `67d9b689651382320604919f3e378c56f2131fcb`, native
  source `56e32004b1af3a4cb625fbfe5dbca24fb6023d09`. Inspected
  `tracker/progress.go`, `read_only.go`, `rawnode.go`, and mirror
  `Progress`, `ReadOnly`, `State`, `RawNode` under
  `packages/etcd-model/EtcdModel/Mirror/`.
- Cleanup branch `cleanup/mirror-boundary-0922` at
  `e43fc58c63b146f8ab9ffde9d4c7fd4d920b37c6`, especially
  `docs/2026-09-22_mirror-design-boundary.md`: runtime/source mappings,
  alias restrictions, Ready cuts, Storage and labelled timeout draws.
  Its separate cleanup validation was read, not rerun or recertified here.

This refines our [post-F2 recommendations](2026-09-22_post-f2-next-steps.md).
The earlier mirror assessment remains a separate design branch. No change to
the mirror or either dependency workspace is part of this response.
