GoLean whole-project review — 11 September 2026

[AGENT] Read-only assessment of main at `bf721a4c28864a9c23c33dba5b9c1cc934bd24e7`. Recommendations in this report are proposals, not user decisions or authorizations. The investigation changed no tracked source, baseline, charter, branch, or reference.

[USER] Publication requested on 2026-09-11: “Can you land your review on main in an appropriate location?” [AGENT] This documentation landing preserves the assessment and compact reproduction records; it does not adopt the proposed roadmap. Links and reproduction instructions have been made portable for the tracked copy. Findings and measurements retain their original audit scope.

**1. Overall assessment.** GoLean is a substantial executable semantics research implementation with unusually strong regression and proof infrastructure. It is not yet a broadly usable Go implementation or a stable semantic foundation for general Iris reasoning. The remaining work includes correctness and interface design, not merely adding the last unsupported syntax forms.

The strongest assets are the total core machine, explicit nondeterministic choices, both directions of single-step executable/relation correspondence, substantial concrete Go regression coverage, checked observation-set enumeration for a restricted fragment, and actual Iris proofs over two small programs. These are valuable foundations worth preserving.

The largest obstacles are:

- The source-to-core boundary can accept a different program from the one Go builds. This audit reproduced three filename-selection mismatches and a module-language-version mismatch.
- Evaluation-order rewrites still produce wrong observations, and several modeled choices are narrower than Go permits.
- The concurrency model lacks the reduction and memory-access correspondence needed to transfer general concurrent reasoning to real Go.
- Typed safety and customer adequacy exist for very small profiles; they are not general Go admission or a stable reasoning interface.
- Ordinary module loading, major language constructs, reflection, much of the standard library, and external effects remain incomplete.
- Modest aggregate workloads can already be impractical to execute.

My recommendation is a phase centered on a truthful acceptance contract, semantic fidelity, a generalizable customer interface, and representative workloads. Continuing chiefly by making individual corpus rows green would miss the most important completion risks.

**2. What this review established, and how.** I used planning documents to locate questions, then checked implementation, theorem statements, runners, current manifests, and recorded evidence. A recorded result is labeled as such. A local test performed during this review is labeled fresh. Neither a previous plan's completion label nor a function's existence is treated as proof that its intended contract holds.

Fresh checks and measurements:

| Check | Result and scope |
|---|---|
| Source snapshot and tracked cleanliness | main at bf721a4c; clean at the beginning and after the investigation |
| Current corpus manifest against baseline | 3,665 IDs, exactly matching the tracked executable baseline; 1,349 distinct case directories |
| Certificate provenance | python3 tools/certification.py check-records passed; one slow-tier record; current source/build/claim inputs match |
| Existing evaluator binary | All 207 checks passed, including the 33,004-vector floating-point test; the evaluator binary was not rebuilt for this audit |
| Fresh Go unit tests | go test -count=1 passed for tools/nativefrontend, tools/coverageharness, and tools/lowerdiag; respectively 125, 26, and 19 top-level Test declarations in source, with further subtests |
| Fresh Lean source elaboration | Tests.InterfaceContract, Tests.RecoveryTerminal, Tests.MethodIdentity, and Tests.BooleanTyping passed against installed compiled dependencies |
| Post-import semantic interface audit | 110 required exports and 15,802 constants checked; dependencies limited to the admitted classical axiom trio |
| Test-library ownership | 37 Tests Lean modules, 15 declared libraries, 14 named CI steps; current ownership registry covers them |
| Source escape scan | No sorry, new axiom declaration, native_decide, unsafe implementation, or implemented_by hit after comment/string filtering in the inspected product sources; no partial declaration in GoCore |
| Fresh source probes | Four input-boundary mismatches, three explicit feature refusals, and positive controls described below |
| Fresh wire mutations | Duplicate schema keys and absent resultTypes accepted by the production entry |
| Fresh performance probe | Byte-append loop measurements below; 4,000 iterations exceeded a 30-second subprocess limit |

I did not run a fresh full scripts/ci --slow, re-enumerate the entire corpus, rebuild the compiler distribution, re-bootstrap the two Iris packages, or rerun every historical workload/fuzz campaign. The Iris packages have no .lake directory in this checkout, so their end-to-end validation here is source review plus existing evidence, not a fresh customer build. This is a project-wide subsystem review and focused adversarial investigation, not a claim to have independently checked every proof line or exhausted every Go program.

An initial fresh Go build failed because the nono OS sandbox allows writing external /tmp but not reading it. Restoring the configured, permitted repository .tmp scratch location resolved the build setup issue; the subsequent tests passed. This infrastructure failure is not counted as a project test failure.

**3. Current measured coverage.** The baseline records regression expectations; it does not define which fraction of Go is implemented.

| Executable lane | Rows | Recorded PASS | Recorded FAIL | Meaning of a PASS |
|---|---:|---:|---:|---|
| Strict | 3,398 | 3,152 | 246 | Agreement under the runner's chosen observations and choice-stream checks |
| Membership | 141 | 141 | 0 | Sampled Go outcomes belong to the modeled set under the row's enumeration contract |
| Confluent | 90 | 89 | 1 | The row's supported enumeration establishes the claimed singleton behavior |
| Racy | 36 | 35 | 1 | Expected race rejection; not successful interpretation of a racy Go program |
| Total | 3,665 | 3,417 | 248 | Mixed contracts, not a whole-language percentage |
| Compile-negative, separate | 394 | 394 | 0 | The Go compiler rejects the invalid fixture with the expected diagnostic substring |

Of the 248 executable failures, 194 are frontend-export failures, 32 are Lean-observation failures, 10 are differential failures, 10 are Go-observation failures, one combines Lean-observation and differential failure, and one is a confluence failure. The 35 race-rejection passes should be kept separate from the 3,382 other passing cases when describing execution support.

The suite includes useful independent material: the imported-goose prefix has 176 rows, 174 passing; spec-example prefixes have 291 rows, 272 passing; the noodler prefix has 567 rows, 548 passing. These counts are derived from current baseline IDs, not whole-program or code-coverage claims. Many rows share a source package and vary entry point, input, or observation.

The language ledger accounts for 158 specification heading anchors through 149 physical table rows, with ten historical version appendix anchors grouped together; the memory-model table has 18 rows. This is a useful classification inventory. It is not proof of language completeness. Its grades mix runtime evidence, known gaps, static checking delegated to go/types, and prose-only sections. In particular, upstream type checking cannot validate that the later lowering preserves a program.

The negative runner invokes go build and never invokes the GoLean frontend or decoder. Its 394 passes therefore provide no direct evidence about GoLean's invalid-input rejection. This is visible in the current implementation, not just an old audit observation. [Baseline](../baselines/native-full.tsv), [negative runner](../scripts/coverage-negative#L183), [ledger accounting](language-coverage-ledger.md#L103).

**4. Fresh high-priority findings at the source boundary.**

**F1 — Source-file selection silently changes the program.** The native frontend calls parser.ParseDir with a filter that accepts every .go file except *_test.go. Its later build-constraint check examines comment directives; it does not implement filename-based selection or Go's ignored-file convention.

This source returned 1 under the pinned Go compiler on Linux and 2 under the freshly built frontend plus the provenance-checked GoLean executable:

```go
// main.go
package main

var x = 1

func probe() int { return x }
func main() { println(probe()) }
```

```go
// extra_windows.go
package main

func init() { x = 2 }
```

The same mismatch occurred with the second file named _ignored.go and .hidden.go. All three GoLean runs exited successfully and reported an integer value of 2. There was no unsupported/refusal warning.

This is a frontend wrong acceptance, independent of whether the core interpreter correctly executes its input. It also contradicts any broad inference that the current build-constraint refusals make source selection fail closed. Imported source packages use the same general parsing approach and should be included when fixing the family.

Required repair: obtain the selected file set from a pinned Go build context, or refuse directories requiring unsupported selection before emission. Test excluded files that contain executable init effects, conflicting declarations, invalid syntax, and imports; a mere duplicate-name rejection would not detect the wrong-answer example above. Record selected files, target, tags, and language versions in the source manifest used by lowering and provenance. [Entry and filter](../tools/nativefrontend/main.go#L119), [filter definition](../tools/nativefrontend/main.go#L199), [constraint check](../tools/nativefrontend/langversion.go#L158), [local-package parser](../tools/nativefrontend/load.go#L240).

**F2 — A module's language version is ignored.** With go.mod declaring go 1.21, a three-iteration loop capturing i into three closures returns 9 in Go and 3 in GoLean. Changing only the directive to go 1.26 makes both return 3. Both runs use the installed go1.26.5 toolchain.

```go
func probe() int {
    var fs []func() int
    for i := 0; i < 3; i++ {
        fs = append(fs, func() int { return i })
    }
    return fs[0]() + fs[1]() + fs[2]()
}
```

The frontend derives GoVersion from its embedded pinned-toolchain table, rather than from the package's module context. This is consistent with implementing only the Go 1.26 language, but the CLI currently accepts the older module directory and changes its meaning. A single-version product must reject that input explicitly; a general Go loader must preserve per-package language versions. The compatibility significance of the loop change is documented by the [Go project](https://go.dev/blog/loopvar-preview). [Version selection](../tools/nativefrontend/langversion.go#L63).

**F3 — Production decoding does not enforce the stronger wire boundary already prototyped elsewhere.** The CLI still uses Lean.Json.parse. Object keys are stored in a map, so duplicate keys disappear before the schema validators see them. A generated valid wire prefixed with a second, conflicting schema field was accepted and executed.

Removing the resultTypes vector from a call assigned to the blank identifier was also accepted. NativeToIR reconstructs the discard temporary as int through resultTypes[i]?.getD .int. The demonstration used an integer-returning function and still returned 42; it demonstrates unvalidated semantic metadata reconstruction, not a newly demonstrated wrong result for valid frontend output.

StrictJsonParse already rejects duplicate keys and malformed surrogate encodings for the separate declaration path. It explicitly states that it is not wired into production NativeToIR. Completing that integration and making required type/vector relationships explicit is more valuable than counting declaration-wire tests as production-input safety. Add production-byte-input mutation tests, not just tests on an already parsed Json value. [Production parse](../GoLean/CLI.lean#L469), [discard typing](../GoLean/NativeToIR.lean#L1485), [second call path](../GoLean/NativeToIR.lean#L1570), [strict parser scope](../GoLean/StrictJsonParse.lean#L4).

These findings are not added to BUGS.md because this was a read-only audit. Compact source inputs and reproduction instructions are published with the [audit evidence](evidence/2026-09-11_project-review/README.md); generated wires remain local scratch artifacts.

**5. Frontend and executable-language completeness.** The frontend has real breadth: native parsing and go/types checking, constant handling, monomorphization, package-local imports, method sets, interface boxing, closures, initializers, loops, labels, multi-assignment, and substantial defer/recover lowering. A fresh Go 1.26 new(42) probe returned 42 on both sides. Modern syntax support should be assessed construct by construct rather than assumed absent.

Its principal structural limitation is that lowering combines many semantic responsibilities in one large emitter. emit.go is about 12,000 lines; all nativefrontend Go files together are about 28,000 lines. This makes evaluation-order, temporary-binding, receiver-adaptation, and declaration-quarantine interactions difficult to review locally.

| Area | Current implementation/evidence | Material gap |
|---|---|---|
| Integers, Boolean values, strings | Width normalization, byte-based Go strings, constants, conversions, operators and many regressions | General typed invariants do not yet cover this full numeric/string domain |
| Floating point | Total software arithmetic with explicit bit patterns; extensive oracle vectors | Fusion/extra precision are narrowed; NaN payloads and out-of-range conversions have explicit limitations |
| Complex numbers | Separate declaration vocabulary can describe them | Executable frontend/runtime support remains incomplete; fresh ordinary complex arithmetic refused |
| Arrays and slices | Copying, aliases, slicing, append, conversions, overlap-sensitive operations | Successful slice-to-array-pointer views remain missing; performance and path-level reasoning are weak |
| Maps | Typed keys, comparability checks, NaNs, mutation-aware iteration identities and choices | Some imported named key types lack the needed declarations; general map ownership and abstraction laws are absent |
| Structs and named types | Declared structures and many conversions/embeddings | Anonymous nonempty struct types still refuse, including a fresh one-field example |
| Functions and generics | Higher-order values, closures, monomorphized generic functions/types, many method cases | Local-type instantiation identity, some signature/type families, tuple boxing, and call/short-circuit combinations remain restricted |
| Methods and interfaces | Full package/name member identity now flows through dispatch and method matching | Broader TypeId identity still depends on frontend string grammar; promotion wrappers remain a semantic/interface coupling |
| Statements and control | If/switch, ordinary loops/ranges, assignments, labels, panic/defer/recover | Range-over-function refused in a fresh probe; several goto lifetime/scope cases, nonidentifier range targets, builtin go/defer forms and short-circuit effect shapes remain unsupported |
| Initialization | Global seeding and synthesized package initialization; many ordering fixtures | File selection, module versions, static-init pruning, hidden-dependency order, init-time spawn and terminal observation remain incomplete |
| Packages | Case-relative source packages plus selected stdlib source | No ordinary module/workspace resolver; dotted local import paths are explicitly refused |
| External effects | A limited print-output facility and special library primitives | No general filesystem/network/time/process/environment API capable of running ordinary applications |

Some unsupported bodies are emitted as quarantined declarations and refuse only when reached. That is useful for exploring large libraries, but EXPORT-OK is not whole-program admission. A program can export successfully while important normal or error paths remain unusable. The fresh anonymous-struct, complex, and iterator probes all exported and then refused with a frontend-quarantined cause.

The current evaluation-order strategy is particularly important. Calls and receives are hoisted; additional probes recover some early-panic possibilities, but successful probe values can be discarded and reevaluated after mutation. BUG-101 and BUG-104 show that preserving one panic axis does not preserve value capture or the ordering of effects. Fix the family with an explicit evaluation/dependency model and tests combining value capture, ordered effects, short-circuiting, lvalue evaluation, and multiple failures. Do not presume that more local guards can establish the complete contract. [Emitter](../tools/nativefrontend/emit.go#L5263), [executable type boundary](../tools/nativefrontend/wire.go#L735), [package loader](../tools/nativefrontend/load.go#L161).

**6. Core machine architecture and semantic fidelity.** The semantic core is a total, explicit control-and-continuation machine. Program context and heap currently share ExecState. The heap is an Array HeapCell, addresses are indices, and only allocation creates cells. Value, map-payload, and channel-payload cells are distinguished. Root writes check bounds and normalize against the declared type. These are meaningful improvements over an untyped or association-list store.

Structural totality is not a proof that arbitrary Go programs terminate. Execution drivers take fuel; exhaustion is an explicit tool result. Likewise, a total implementation of a helper is not itself proof that the helper implements Go correctly.

The shared premise functions used by stepFn and Step are a sound engineering choice for coherence: they prevent a large class of interpreter/relation drift. They also mean the coherence proofs cannot discover an incorrect shared arithmetic operation, panic rule, or lowering policy. Independent Go/spec validation remains necessary.

Several invariants are narrower than their names might suggest. StateWf bounds locations; MachineWf adds configuration bounds and normalized map-iteration state. Neither is general operand typing, heap typing, function-signature validity, or progress for arbitrary source programs. FloatBits also contains fixed-budget helper loops whose unreachable-exhaustion arguments are explained in comments; the general width/domain and bound theorems should be part of the long-term numeric contract. [State representation](../GoLean/GoCore/State.lean#L68), [well-formedness](../GoLean/GoCore/StateWf.lean#L645), [float helper bounds](../GoLean/GoCore/FloatBits.lean#L88).

The full-latitude doctrine is not achieved today:

- Platform is presently instantiated as gcAmd64; integer widths, layout, allocation thresholds, and some synchronization sizes are target-specific.
- Floating-point arithmetic selects per-operation rounding without fused operations or additional precision; generated NaNs are canonicalized.
- Append capacity is an interval around a growth policy, not every capacity allowed by the language. The source explicitly describes this as a subset.
- Zero-size pointer identity and some initialization/evaluation-order choices still differ from the oracle or require restrictions.
- Select/scheduler choices are explored at the machine's chosen boundaries; they do not establish full Go interleaving coverage.
- A finite List Nat choice tape with a default after exhaustion represents finite execution choices conveniently; it is not by itself an infinite fair scheduler or a liveness semantics.

There should be two explicit contracts: portable language semantics with its allowed choices, and target-specific execution compatibility. An observation being allowed by the Go specification does not automatically make a model complete for the chosen gc target; conversely, matching one gc realization does not justify universal portability.

For a declared source domain and observer, the desired evidence relationship is:

    observed Go outcomes ⊆ modeled outcomes ⊆ permitted Go outcomes

Differential sampling attacks the left inclusion. Specification arguments, independent litmus tests and semantic laws attack the right. Safety proofs transfer to a real target only when its behaviors are included in the model, with refusal and observation scope handled explicitly. A universal theorem over an under-approximation can miss real executions. [Platform](../GoLean/GoCore/Platform.lean#L14), [float envelope](../GoLean/GoCore/FloatBits.lean#L25), [append envelope](../GoLean/GoCore/Ops.lean#L2353).

**7. The relational semantics is substantial, but its end-to-end contract is incomplete.** Calling it merely a half-built wrapper understates what is proved. Calling it a complete reasoning semantics would overstate its composition and external fidelity.

| Contract | Current status | Limitation |
|---|---|---|
| Successful executable step implies Step | Proved: stepFn_sound | Successful transitions only; shared premises do not independently validate Go |
| Step implies an executable step for some choices | Proved: step_complete | One-step existential choices do not alone compose into one tape for an entire relation trace |
| Successful pool step implies StepM | Proved: stepMulti_sound | Driver race detection, output accumulation and terminal policy are additional structure |
| StepM implies executable pool step | Proved: stepM_complete | Same one-step/composition distinction |
| Structural machine invariants are preserved | Proved through StateWf/MultiWf soundness modules | Not general typed progress |
| Fixed-tape counted sequential trace corresponds to iteration/run | Proved: iter_iff_trace and run_ok_iff | Trace is defined from stepFn success; erasure to Steps has no general converse here |
| Pool/program driver corresponds to a proof trace and observations | Proved: Pool.run_iff, program_run_iff, observation_iff | The traces describe the driver, rather than completing a general labeled-relation-to-driver bridge |
| Full registry-scheduler reduction to fine execution | Not proved | The existing NPDRFReduction proposition is explicitly refutable as written |
| General continuation composition laws | Not supplied by the public interface | recover depends on continuation context |
| General Go admission and refusal freedom | Not established | Only the two small typed profiles provide stronger contracts |

The decisive next relational deliverable is a stated, reviewable simulation contract that includes initialization, step labels, choice consumption, memory effects, output, terminal priority, result readout, and the relevant refusal/domain hypotheses. Then prove both directions for finite observations in that stated scope.

There is no end-to-end frontend-correctness theorem connecting a Go source program to its emitted core program. The frontend is intentionally trusted and differentially validated. A customer proof about a core Program therefore needs an explicit, reproducible binding to the selected source, imports, lowering configuration and generated artifact, plus that frontend trust assumption. Core execution/relation coherence alone does not establish the source-level claim.

Refusals and uncaught aborts have no successful sequential Step successor. The current bare Iris adapter consequently treats them as stuck. That is an honest partial-correctness boundary, but it needs to be explicit in any customer proof about panic behavior or absence of runtime faults.

Source: [single-step soundness](../GoLean/GoCore/MachineSound.lean#L172), [single-step completeness](../GoLean/GoCore/MachineSound.lean#L506), [pool coherence](../GoLean/GoCore/MultiSound.lean#L1172), [trace](../GoLean/GoCore/Trace.lean#L10), [pool trace](../GoLean/GoCore/PoolTrace.lean), [program observation contract](../GoLean/GoCore/ProgramTrace.lean#L59).

**8. Typed admission and Iris customer readiness.** The current facade is experimental and mostly re-exports representations and theorems. Its detailed caveats are justified by the source.

There are three materially different admission claims:

- The original Boolean syntax admission checks indices, entry conditions and a small syntax policy. It is deliberately weaker than lexical typing and can admit a program that later refuses.
- TypedBooleanAdmission checks Boolean bindings, scope and return structure. Its whole-program theorem permits Boolean result vectors of the declared arity or fuel exhaustion, with empty output. It excludes loops, ordinary calls, integers, aggregates, concurrency, and general I/O.
- RecoveryAdmission adds a bounded language of Boolean cells, live Boolean root references, empty-interface payloads, known calls/closures, defer, and string panic/recover. It checks a finite acyclic call/defer graph. It does not admit arbitrary recursion or function values stored anywhere in the heap. Its whole-driver theorem permits typed success, an anchored string-panic observation, one named invalid-first-line-UTF-8 refusal, or fuel exhaustion.

These are real preservation/progress and driver theorems. They are also very far from admission for almost any Go program. The 12 Boolean and 44 Recovery core files contain about 8,197 lines altogether. Further effort should favor a reusable typing/admission architecture rather than a fresh parallel invariant family for each tiny fixture. Small profiles should remain regressions and milestones within that architecture. [Boolean grammar](../GoLean/GoCore/BooleanTyping.lean#L94), [Boolean driver theorem](../GoLean/GoCore/BooleanPool.lean#L161), [recovery grammar](../GoLean/GoCore/RecoveryStatements.lean#L112), [call graph](../GoLean/GoCore/RecoveryGraph.lean), [terminal contract](../GoLean/GoCore/RecoveryTerminal.lean#L205).

The two opt-in Iris packages demonstrate more than a schematic Language instance. gate-a1 wraps the actual sequential Step relation. iris-customer projects the dense heap into Iris gen_heap, allocates concrete ghost resources, supports fractional reads and exclusive writes, supplies call/allocation/unwind rules, and obtains result facts through Iris adequacy and the executable driver. Current code also has shared-capture examples and reusable call-site rules; the older README's description of only program-specific helper rules is incomplete.

However, the customer still imports machine representations and unfolds operations. Ownership is at root-cell granularity; there is no general split-field/slice-region ownership contract, concurrent instance, general recursive function-specification interface, or I/O adequacy. Generic lifting often assumes a successful stream-preserving step for every tape. That is useful within these examples but is not a rule for arbitrary nondeterministic operations. Successful-run all-choice theorems exist for the typed recovery profile; it would be wrong to dismiss the current customer as only an empty-tape calculation.

The main composition problem is semantic, not just representational. recoverResult inspects the continuation. Appending an arbitrary continuation can change a recover result. Changing Cont to a list does not prove a generic bind law. A customer-facing solution must either expose an admissible context class with proved laws, retain continuation-explicit rules, or restructure the relevant language interface under a proved correspondence.

The memory contract needs similar care: writing an array element recursively stores and normalizes the containing root cell. A disjoint-path frame theorem requires normalized/typed storage premises; raw location boundedness is insufficient. Existing cross-root mover lemmas do not establish same-root field/element separation.

Keep Iris resources, WP automation and application proofs downstream. Keep semantic states, access/observation events, validity predicates, simulation theorems and frame/commutation laws here. Retain a thin, separately built customer that actively tests those exports. [Facade](../GoLean/Interface.lean), [Language adapter](../spikes/gate-a1/GateA1/Language.lean#L26), [generic call rule](../spikes/iris-customer/GoLeanIris/Call.lean#L64), [typed adequacy transfer](../spikes/iris-customer/GoLeanIris/Readout.lean#L125), [root write semantics](../GoLean/GoCore/Ops.lean#L1367).

**9. Concurrency is the largest external soundness obligation.** The pool machine implements meaningful behavior: goroutine creation, blocking/rendezvous channels, buffered channels, close/wake behavior, selects, Mutex/RWMutex/WaitGroup/Once, TryLock choices, and integer atomics. The detector tracks happens-before information and access footprints. This is a substantial implementation, not a stub.

But scheduling is restricted to registered boundaries, completions, and back-edges. StepMFine relaxes scheduling to arbitrary machine steps; it still uses this machine's granularity. Neither layer directly supplies the missing correspondence to Go's relevant memory accesses, especially for bulk operations.

NPDRFReduction is a Prop-valued definition, not a theorem or axiom. Its whole-state result comparison is acknowledged to be false because main can exit with other goroutines partway through private computation. The easy coarse-to-fine inclusion is proved. The fine-to-coarse result needed for a reduction is not. Other remaining issues include allocation up to address renaming and same-root path commutation. There is no NPDRFReductionV2 or checked refutation theorem at this tip.

The detector's access set is a separate per-shape table. A step can be internally coherent with that table while both disagree with Go's accesses. Emitting semantically classified access events from a shared memory layer can reduce duplication, but blindly logging all internal heap loads would introduce false accesses: address formation, metadata inspection, and synchronization storage must be distinguished from program memory events.

DRF-SC is the right foundation for a safe-Go concurrent profile. The Go memory model gives data-race-free programs sequentially consistent behavior and permits reporting a race and terminating. That does not prove that this detector recognizes the relevant races or that this scheduler preserves all required outcomes. [Go memory model](https://go.dev/ref/mem), [scheduler](../GoLean/GoCore/Multi.lean#L1495), [draft reduction](../GoLean/GoCore/NPDRF.lean#L438), [access table](../GoLean/GoCore/Race.lean#L1532).

Remaining executable concurrency gaps include select-to-select rendezvous, sync.Cond, atomic.Value/Bool/Pointer, go during initialization, runtime.Goexit, some composite-path over-refusal, and broader concurrent output. Existing successful integer-atomic examples do not cover all sync/atomic APIs.

Race rejection must be advertised as a checked-profile boundary, not coverage of all legal outcomes of racy Go. Likewise, bounded exploration cannot establish fairness or termination. Keep concurrent safety, finite may-observations, divergence, and liveness claims separate.

**10. Library and environment coverage.** Source-through lowering is a sound direction for library coverage because it exercises ordinary Go bodies and avoids inventing a second implementation of each library function.

The actual allowlist contains 13 packages, including internal support packages: strings, strconv, internal/strconv, internal/stringslite, internal/bytealg, unicode, unicode/utf8, math/bits, errors, bytes, slices, cmp, and encoding/binary. The current source pin contains 61 files. This is package admission, not full-function support.

There are five upstream-file substitution rows and five expression overlays, plus five consequential import changes. The overlays cover unsafe/runtime idioms in string cloning, errors.Join rendering and strings.Builder. Their correctness depends on stated observational premises; adding unsafe operations, address observations or new library uses can invalidate those premises and must trigger review.

Six fmt entry points still use injected/desugared code: Sprintf, Errorf, Fprintf, Fprint, Sprint and Sprintln. Errorf retains a synthetic error type. Source-through errors.Is/As and reflective parts of encoding/binary remain blocked by reflection-related support. An imported package may type-check through export data while executable bodies are missing or quarantined.

General reflection is a major practical dependency, but it should be built on one explicit type-descriptor/identity contract, not another set of string-parsing conventions. Anonymous structures, tags, recursive types, unexported member identity, addressability, method sets, and construction/mutation requirements must be handled coherently.

Filesystem, network, clocks, process exit, environment state and foreign calls need an explicit external-effect interface with a runnable host implementation and a reasoning contract. Treating these as forever excluded would substantially weaken the phrase almost any Go program. Exact runtime garbage-collector internals need not be copied for a safe subset, but observable finalizer/weak-reference/unsafe behaviors cannot be silently covered by an abstract never-free heap.

I would prioritize module loading, general source/type identity, common pure library paths, reflection-dependent libraries, and useful external effects before treating the last 20 complex-number cases as the sole measure of language completion. Complex arithmetic still needs an explicit completion slot. [Library admission](../tools/nativefrontend/stdlibsource.go#L75), [overlays](../tools/nativefrontend/stdlib-overlay.tsv), [fmt injection](../tools/nativefrontend/stdlibshim.go#L168), [library register](../tools/nativefrontend/stdlibregister.go).

**11. Experiments and their proper evidential role.**

| Experiment/asset | What it demonstrates | What it does not demonstrate |
|---|---|---|
| Imported-goose fixtures | Independent source cases, with verbatim/pin guards and real differential checks | Verification of Goose/Perennial programs or general Go compatibility |
| Spec examples, semantic-edge cases and noodler | Good sources of focused counterexamples and interaction regressions | Exhaustive behavior within a spec heading |
| Cedar census and functional drivers | A realistic dependency surface; package/member-identity pressure | Working Cedar authorization merely because library exports succeed |
| raftsubject and machine twin | Selected and derived Raft components can exercise a large core program; useful schedule-driven state-machine tests | Running an unmodified concurrent etcd application or its deployment environment |
| raftharness | Native Go chaos/concurrency tests and executable safety assertions | Interpreter execution; the README explicitly separates it from the machine twin |
| gate-a1 and iris-customer | Actual current-machine adapter, ownership and adequacy experiments | A general upstream/downstream reasoning API |
| Declaration/I1 spike | Positive type identities and a stricter serialization boundary, now partly reused by method identity | General executable type admission or production parser integration |
| Parked reasoning branch and unmerged typed branches | Potential reusable proof patterns, regression cases, design lessons and experiments | Current mainline guarantees; each needs revalidation against current semantics |

The latest inspected Cedar audit-fix receipt is from clean source 20e412ba: 34 cases, 25 EXPORT-OK, eight FRONTEND-REFUSED, one MACHINE-REFUSED; 1,560 of 1,671 static declarations classified as lowering. The package subset improved to 22/22 exports, but the nine functional-driver cases do not establish completed functional execution. Export and declaration percentages conceal reached stubs and failing error paths. The appropriate next Cedar target is one genuine functional driver, with success, error and boundary cases.

Raft's derived tree rewrites import paths and replaces or generates some protobuf-related machinery; the twin uses explicit schedules and RawNode-style driving. Those transformations need their own fidelity evidence. A pinned wire only certifies that the derived artifact is unchanged. It does not prove that the native concurrent harness and the machine twin have the same behaviors.

Existing plans contain stale descriptions even of these assets: for example, the raftsubject README describes protobuf codec methods as absent while current derivation tooling includes a generated codec. Audit the current derivation and reachable workload, rather than continuing from that prose.

Use a small permanent set of externally chosen workloads as acceptance tests: a pure algorithmic module, a real parser/serializer or policy component, and a concurrent component with shared ownership and synchronization. Keep original dependency/module context and normal/error/boundary paths visible. [Cedar receipt](evidence/2026-09-08_method-identity/audit-fix-cedar.json), [Raft tooling](../tools/raftsubject/README.md), [native harness](../raftharness/README.md).

**12. Differential and certification apparatus.** The apparatus is one of the project's strongest parts. It distinguishes refusal from a successful Go observation, tracks known failures explicitly, authenticates many terminal reports through a same-run crash channel, checks binary/source provenance, and contains meaningful negative controls.

The checked dedup path is especially valuable. checkCert_slowObs proves equality between accepted certificate members and SlowObs, assuming sound node equality. The optimized search itself is not trusted to establish completeness; a total checker validates its graph and witnesses. This is stronger than merely trusting the enumerator's printed count.

Its scope still matters:

- SlowObs is defined from the current interpreter driver, not from an independent full-Go relation.
- EnumSpec.Obs omits output. The dedup engine explicitly refuses output-producing steps, preventing that omission from silently certifying output behavior.
- The checker supports a restricted set of step/choice shapes. Fatal and deadlock members remain unsupported in the engine/checker paths.
- Of 231 membership/confluent rows, 23 explicitly select engine=dedup; 208 use the default engine. Four rows declare nonterm accounting. Those contracts must not all be described as the same machine-checked theorem.
- Only one row is tier=slow with a tracked certification record. Its six-member set was certified at 5e73b561 with a clean receipt. The fresh provenance check confirms compatibility with current inputs; it is not fresh enumeration.
- Go samples establish observed membership. A member not sampled on Go has not thereby been shown impossible or possible on Go.
- A fuel-exhausted branch is a bound result; it is not a proof of divergence.

The observation harness has a materially improved byte-output and terminal-classification design. Its known scope still excludes full multiline panic text, invalid first-line UTF-8, some pre-main abort authentication, fatal errors during unwinding, and some output-plus-race cases. Recovery strings, concrete runtime-error types, and user-defined Error/String methods at abort need semantic and observer work together.

Ordinary GitHub push/PR checks invoke the fast gate with GOLEAN_ALLOW_NO_DIFF=1. On a fresh runner, green therefore covers builds, unit checks and static/pin checks, not a freshly executed corpus. The scheduled/manual path performs the full differential. The local merge protocol is stricter, but a general external green-CI claim still needs the scope caption.

Recommended strengthening: make fresh runtime-change differential evidence a required merge artifact/check, preserve the new source/build provenance, add a true frontend/decoder negative lane, and keep independently authored mutation tests for observer failures. A source fingerprint prevents stale reuse; it cannot turn an incomplete observer or unsupported scheduler into a stronger semantic claim. [Checker theorem](../GoLean/GoCore/EnumDedupSound.lean#L915), [observation set](../GoLean/GoCore/EnumSpec.lean#L44), [output refusal](../GoLean/EnumDedup.lean#L280), [provenance](../tools/certification.py#L230), [workflow](../.github/workflows/lean_action_ci.yml#L20).

**13. Performance, maintainability and operational sustainability.** Practical completion requires programs of useful size to execute, not just elaborate.

Fresh single-run results for:

```go
func probe(n int) int {
    var xs []byte
    for i := 0; i < n; i++ {
        xs = append(xs, byte(i))
    }
    return len(xs)
}
```

| Appends | GoLean wall time |
|---:|---:|
| 100 | 0.0262 s |
| 500 | 0.1500 s |
| 1,000 | 0.7625 s |
| 2,000 | 4.4939 s |
| 4,000 | Exceeded 30 s; subprocess timed out |

Each completed execution returned the right length. Times include process startup, JSON decoding and execution, with the wire already generated. These are one run per size, not a controlled asymptotic benchmark or a comparison against native-Go runtime. The last row is a lower bound, not a completed runtime.

The current implementation provides a plausible cost mechanism: an in-place append stores an indexed backing-array element; storeLoc recursively reconstructs/stores the root, then normalizeValueForTy traverses the declared aggregate. Whole-array work can therefore recur for each element update. This warrants profiling and a representation/refinement design. It does not justify simply repeating BUG-090's obsolete association-list explanation.

Other scaling risks include linear lookup in various name/map tables, materializing full backing capacities, retaining old states during exploration, and large certificate graphs. The recorded slow example used roughly 6.19 million nodes and 6.57 million edges for six observations. Correctness-preserving optimization should separate semantic simplicity from efficient execution: prove/refine optimized storage, memoized immutable context and search representations against the same public semantics.

The project has around 51,000 Lean lines under GoLean, with large Machine, MachineSound, StateWf and Ops modules. Representation changes can trigger widespread proof edits. Split immutable context from mutable storage if that makes the exported laws and execution cost better; avoid using the refactor itself as evidence of semantic progress.

The operational cap, test ownership receipts, certificate provenance and evidence-size gates are worth retaining. Audit scripts still include whole compiled-tree copies into per-run scratch directories, and many historical worktrees/caches remain. Storage growth needs an explicit lifecycle and shared immutable dependencies. Cleanup would require separate authorization and was not done during this audit. [Append update](../GoLean/GoCore/Machine.lean#L1330), [aggregate root write](../GoLean/GoCore/Ops.lean#L1367), [retained-copy audit](../scripts/check-interface.py#L59).

**14. All currently open BUG entries, interpreted by kind.** The current file has 16 entries whose Status begins open. They should not be scheduled as 16 equivalent fixes. Some are wrong answers, some coverage boundaries, some apparatus limits, and some performance or enumeration issues.

| BUG | Current concern | Treatment |
|---|---|---|
| 061 | Static-init pruning can schedule initialization work differently from gc | Initialization fidelity |
| 041 | Dynamic composite-path reads can over-report races | Access semantics and typed path precision |
| 008 | Imported named type declarations/comparability incomplete | Type/import boundary |
| 004 | Abort payload identity, invalid byte text, defined-type methods | Panic semantics plus observation contract |
| 002 | Machine-operation granularity versus concurrent Go | Reference concurrency model and reduction |
| 065 | Worker-pool confluence certification beyond current tractability | Search/performance; no silent budget relaxation |
| 090 | Aggregate/allocation performance | Re-measure current implementation; retire stale heap diagnosis |
| 093 | print/println operand, init, and output limitations | Output/library support |
| 094 | Produced NaN payload versus bit-observation mismatch/refusal | Numeric latitude and target contract |
| 099 | Synthetic recovered runtime-error dynamic type | Observable type/panic fidelity |
| 100 | Local defined type as generic-type argument refused | Identity and supported-source scope |
| 101 | Successful early operand value discarded before reevaluation | Evaluation-order family repair |
| 102 | Explicit E13 boundary refusals for unmodeled combinations | Widen after the evaluation model is sound |
| 104 | Compound-assignment target failure precedes ordered RHS effects incorrectly | Evaluation-order family repair |
| 106 | Fatal error during panic unwinding cannot be authenticated | Oracle observation |
| 107 | Pre-main terminal report lacks authenticated hook | Oracle initialization observation |

The ten baseline differential failures also include explicitly documented initialization and zero-size-pointer divergences. A release claim must classify those individually as corrected behavior, intentionally excluded source/target scope, or a spec/oracle discrepancy with evidence. They must not disappear under a blanket expected-red label.

The new F1/F2 source mismatches and F3 wire-boundary observations in this report are additional to that register. [Current BUG register](BUGS.md).

**15. A completion contract that matches the intended product.** I would define completed by explicit offers, rather than by having no remaining named work packages.

| Axis | Required completed-state property |
|---|---|
| Source identity | The actual package/module file set, dependency graph, language versions and build context are preserved or explicitly rejected |
| Executable breadth | Nearly all agreed pure-Go language constructs and representative real modules execute; remaining exclusions are narrow and visible |
| Libraries/environment | Required ordinary stdlib/dependency paths and external effects have executable implementations and stated semantic contracts |
| Fidelity | No known wrong answers inside the advertised profile; modeled nondeterminism covers the supported target behaviors and has an argued Go upper bound |
| Typed domain | A reusable admission/validity contract covers the advertised core language, with initialization, preservation and an explicit progress/refusal result |
| Relation coherence | The exported labeled relation and actual drivers agree for the claimed observations, terminals and choice streams |
| Concurrent transfer | Access granularity, races and scheduling reduction are proved or remain explicit restrictions; no general concurrent claim depends on an unproved draft |
| Customer utility | An independently maintained Iris customer proves representative source-derived sequential and concurrent examples through the public semantic API |
| Practical execution | Published workload-scale runtime/memory targets are met, with explicit bound failures and no unsupported result counted as success |
| Release evidence | Fresh full differential evidence, appropriate proof/customer checks, negative controls and content-bound provenance at the released inputs |

“Almost any Go program” needs a declared interpretation. Pure Go with ordinary modules and an explicit host-effect model is a credible staged target. Cgo, assembly, unsafe layout, runtime introspection and every platform-specific syscall are a much larger compatibility undertaking. Either commit to those extensions as a later tier, or describe the completed product as broad safe-Go semantics rather than implying those programs already fit. Rejecting unsupported inputs is the right current behavior, but a refusal is still a breadth gap.

Portability should also be explicit: a Go 1.26 language contract, one or more target/platform instances, and a version-upgrade process. Do not float the existing oracle to make a mismatch disappear. Supporting an older module's semantics is a different task from merely installing a newer compiler.

**16. Proposed roadmap, ordered by demonstrable exits.** This sequence is my recommendation from the current evidence. It does not inherit historical estimates, branch completion labels, or design decisions by implication. Existing named user design gates still require the appropriate review before implementation.

1. **Establish and enforce the source/observation contract.** Fix or explicitly reject F1/F2, use the production strict byte parser, remove unsupported type-data defaults, and implement a native-frontend/decoder negative lane. Classify every current differential mismatch and observation exclusion. Exit: the fresh counterexamples are permanent tests; no accepted input silently changes file set or language mode; wire rejection is tested through the real CLI; the supported-profile document can be checked against executable admission behavior.

2. **Repair semantic families and define the public reference interface.** Design one expression evaluation/ordering model that handles values, effects and failures; close BUG-101/104 through that model. State labeled sequential and pool transitions, terminal/output observations and driver simulations. Define immutable program/type context and a typed memory/access contract; choose representation changes because they help those laws. Exit: family-level interaction tests, reviewed semantic statements, preserved per-step coherence, and a demonstrated path-level memory law on admitted normalized storage.

3. **Complete a useful sequential reasoning offer.** Generalize admission to integer/string operations, aggregates, pointers, calls, recursion and ordinary control flow in deliberate increments. Prove initialization/preservation/progress contracts for that offer, and resolve continuation composition with explicit laws. Have the external customer prove a nontrivial source-derived routine with calls, aliasing and an exceptional path using public exports. Exit: the customer no longer needs private evaluator unfolding for routine rules; its source artifact and input context are bound to the proof; the actual driver receives the promised observation theorem. Termination remains a separate program property.

4. **Make real modules and libraries work end to end.** Implement module-aware loading and structural identity; close anonymous structures, tuple boxing, iterator ranges and the most consequential control-flow gaps. Extend source-through libraries, introduce a reviewed descriptor/reflection interface, retire fmt injection where feasible, and provide an external-effect adapter. Choose one Cedar functional driver or another similarly demanding workload and preserve its genuine error paths. Exit: several independently chosen modules run through the ordinary entry point without import rewrites, dead-body substitutions, or success-only demonstrations; remaining exclusions are measurable. Complete complex arithmetic and other smaller language gaps within this stage's explicit checklist.

5. **Establish a sound concurrent offer.** Specify a reference event/step model at the granularity required by Go. Replace the refutable reduction target with a reviewed observable-state statement, including allocation renaming and main exit. Prove the needed access/commutation/detector results; implement remaining important synchronization forms. Add a concurrent Iris adapter and ownership-transfer example. Exit: an explicit theorem chain or clearly restricted reference-execution contract connects the customer's concurrent safety theorem to the executable and target Go behaviors. If the coarse reduction proves too costly, shipping a slower faithful reference scheduler is preferable to leaving the transfer premise implicit.

6. **Meet workload-scale performance and confidence targets.** Start profiling now; land semantic-preserving optimizations alongside the appropriate stages. Benchmark scalar loops, allocations, aggregate updates, string/slice libraries, realistic modules and choice exploration. Add sustained generated/metamorphic tests and upstream compiler regression cases; use a second compatible oracle target/implementation when available, without repinning by accident. Exit: documented runtime/memory budgets on fixed workloads; fresh full evidence; meaningful mutation sensitivity for the frontend, observer, detector and certifier.

7. **Stabilize the customer pin and release protocol.** Publish the exact interface, domain, platform parameters, observation equivalence, remaining assumptions and versioning rules. Require the independent customer and full differential evidence at semantic releases, with current fingerprints. Exit: a consumer can pin a revision and understand precisely what theorem transfers to which Go programs and executions, without reconstructing history from planning documents.

The first concrete work items I would commission are F1/F2/F3 regression-and-boundary repairs; an evaluation-order family design and prototype; a public sequential transition/observation/admission contract; profiling of the demonstrated append workload; and one real functional-driver acceptance target. The concurrency reference statement can be developed alongside these, but its proof should not begin against the refutable current proposition.

Avoid three tempting substitutes for completion: making more export-only cases green, accumulating more tiny fixture-specific proof layers, and undertaking a large representation refactor without a customer law or measured performance improvement attached.

**17. Reporting and planning discipline for the next phase.** The existing project is unusually candid about many limitations, but its documentation volume and append-only status updates now make the current truth expensive to reconstruct. This audit found both pessimistic stale claims (association-list heap, incomplete descriptions of customer rules) and misleadingly reassuring labels (a positive export, a negative-suite pass, or a fast CI green read as a stronger guarantee).

Maintain one generated or mechanically reconciled current-state inventory with distinct fields for source acceptance, reached execution, differential outcome, explored choices, proof domain, customer use, and evidence freshness. Keep decisions and historical argumentation in their existing records, but do not use those records as mutable completion dashboards. A closed bug should point to a live regression; a design choice should point to the active code contract; an open wrong answer should prevent an in-profile completion claim.

The next phase should be judged by a few complete chains: real source and build context, admitted core program, faithful execution, exported relation, customer proof, and an observation that the pinned Go implementation can actually exhibit. The current project has strong pieces of that chain. Completing their contracts and connections is the direction that best serves both accurate execution and Iris-based reasoning.


**Audit artifacts.** The [evidence README](evidence/2026-09-11_project-review/README.md) records provenance, conclusions and portable reproduction commands. [Captured initial probe results](evidence/2026-09-11_project-review/probe-results.json) contain the three filename mismatches, modern-new positive control, three reached feature refusals and discarded-call control. [Probe inputs](evidence/2026-09-11_project-review/probe-inputs.json) retain the small source files for those cases, the module-version pair and the append workload. Generated wires, binaries and caches are not part of this documentation landing. No findings were added to the BUG register and no permanent regressions or fixes were installed.
