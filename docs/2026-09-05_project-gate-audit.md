# GoLean project gate audit — 2026-09-05

Status: independent [AGENT] assessment commissioned by the user in this session. Recommendations below are proposals, not recorded user decisions. Audited source: `75dcb6d14c279fc7149ee626063b24ab76e2fa1f`. No runtime, frontend, corpus, baseline, or policy changes were made for this review.

## Decision

**Continue the project, retain GoCore and the native frontend, but revise the next-phase plan before treating it as a verification-consumer release plan.** The project has a substantial executable model, unusually strong failure accounting, useful correspondence proofs, and a differential corpus whose recorded results I reproduced. It is a credible research foundation. It is not yet a generally faithful, portable Go model on which a consumer should base unqualified Go verification claims.

The master plan is `docs/2026-09-05_master-plan.md`. It is a useful inventory and dependency map. Its strongest decisions are the program/store split, explicit memory operations and access traces, removal of arbitrary type-resolution fuel, and a stable consumer contract. Its weakest points are that the proposed consumer contract contains false theorem shapes, concurrency adequacy remains outside the effective release gate, and several completion criteria measure accounting rather than fidelity. More detail about sessions and historical rulings will not repair these issues; small, executable contract experiments and stronger acceptance criteria will.

I recommend a **conditional next-phase go**, and **no consumer pin under the current G-PIN criteria**. Begin with contract validation, typed admission, semantic identity, and the already diagnosed wrong answers. Continue memory-interface work. Put broad reflection/JSON expansion behind a real consumer milestone and a type-representation review. This is a change of sequencing and assurance architecture, not a recommendation to start over.

## Scope and evidence

The review covered the charter and current master plan; the reasoning-surface, C2, reflection, latitude, and library plans; representative interpreter/rule pairs; memory and type representations; scheduling and race-detection boundaries; the native emitter, identity and loading boundary, and Lean decoder; differential comparison and enumeration; negative testing; CI; baseline/bug accounting; and downstream-subject evidence. The C2 design note was read end to end. Ten landed commits were inspected by changeset inventory and matched to present implementation: `1ebd7465`, `dfe763f9`, `50e3ea41`, `e58eff5e`, `75d29186`, `1a82f305`, `21bb79f7`, `1b3796c6`, `2fb7d54d`, `249dc607`. This was not an exhaustive line-by-line verification of every file or every historical ruling.

Validation ran on the initially clean primary checkout at the audited SHA, using its existing dependencies and incremental build artifacts. The report has a separate worktree/branch, `review/project-audit-20260905`, at the same SHA. This deliberately differs from the plan's fresh-worktree gate recipe: the run is a current-source incremental gate, not a clean-room bootstrap test. No changes to source were needed to investigate the contract counterexamples.

Reproduced baseline counts:

| Result/stage | Cases | Meaning |
|---|---:|---|
| PASS, ordinary differential (`-`) | 3,103 | Agreement under the strict lane's checks |
| PASS, confluent | 88 | Confluent-lane checks |
| PASS, membership | 121 | Sampled Go observations belong to the tested model set |
| PASS, racy | 35 | Race-lane success, not ordinary execution equivalence |
| FAIL, frontend-export | 198 | Source does not reach executable comparison |
| FAIL, lean-observation | 35 | Model-side observation failure |
| FAIL, differential | 10 | Recorded mismatches |
| FAIL, confluent / go-observation / alternating stage | 3 | One each |
| **Total** | **3,593** | **3,347 PASS, 246 FAIL** |

The separate negative baseline has 394 PASS. Its meaning is narrower than frontend rejection correctness (finding F9). The source-level audit probes reproduce continuation-sensitive recovery and the weakness of `StateWf`; a printing probe confirms the dedup engine refuses output-bearing execution rather than silently certifying output it does not represent.

`python3 tools/reconcile-records` reproduced two MEDIUM findings: 78 version-citation sites needing contextual review, and FR-7 citing `=` instead of a case ID. It reported 104 bug entries, 16 open, 88 fixed, and 14 untriaged fidelity failures (10 coverage, 4 latitude, 0 classified as untriaged wrong answers). These numbers are measurements of the records, not a bound on undiscovered bugs.

Commands and final gate status are recorded in the evidence appendix below. No whole detector campaign, new cross-compiler campaign, fresh Cedar census, parked proof rebuild, or full slow-tier recertification is claimed.

## What is working

**The executable architecture is worth keeping.** `StepFn.lean` implements explicit machine steps rather than a monolithic host-language evaluator. `Machine.lean` gives relational rule shapes, and `MachineSound.lean` proves `stepFn_sound` and `step_complete` (lines 172 and 506). The shared premise functions make drift detectable and the correspondence manageable. The proof is internal consistency between two descriptions sharing operations; it is not a proof that those operations implement Go. That distinction is essential, but the internal consistency is valuable.

**Failure classes are explicit.** `Value.lean:199–254` separates unsupported/malformed/internal refusals, Go terminals, and fuel exhaustion. The decoder rejects unknown node kinds and checks fields with `StrictJson`. Typed heap-cell constructors separate values from map/channel payloads (`State.lean:30`). The current emitter's quarantine mechanism allows unrelated declarations to survive while calls to unsupported declarations fail visibly. These are strong foundations for honest partial support.

**Several recent changes reduce semantic accidents.** The dense heap eliminates phantom writes to absent roots; dependency-ordered type tables remove arbitrary 1,024-level type budgets; map-entry stamps express deletion/recreation identity; explicit signals consolidate control transfer; choice-site records make nondeterminism inspectable. C2's note also discloses unproved bound sufficiency, diagnostic changes, and excluded trace rows. That disclosure is useful, even though some debts should have stronger gates.

**The testing apparatus does more than compare happy-path integers.** It distinguishes frontend and semantic failures, models panic observations, checks oracle versions, exercises nondeterministic streams, compares membership sets, validates stale wire/parameter certificates, and tests failures of the apparatus itself. The dedup engine's total checker and `checkCert_slowObs` theorem are particularly good architecture: expensive search can be outside the semantic trust boundary while a small checker validates its claim. Its supported fragment and observation vocabulary remain limited.

**Real-language breadth is substantial.** Closures, defer/recover, interfaces, typed nils, integer widths, floating-point bit operations, slices, maps, channels, synchronization, package initialization, and generics all have implementation and test investment. This is far beyond a toy deep embedding. The remaining problem is assurance across interactions, not absence of a semantic core.

## Findings, ordered by effect on the next gate

### F1 — High: the completion criteria permit a fidelity claim stronger than the evidence

The master plan §1.7 calls E2 “Differential lower bound holds on the whole corpus,” tested by `wrong-answer 0/0`. But that counter is **unexplained wrong-answer rows**, not all wrong answers. The same plan §3.G records BUG-099, BUG-101, and BUG-104 as open wrong answers, and the baseline contains ten differential failures. E3 demonstrates classification; E4 demonstrates that spec headings have categories; E6 permits known pins as long as a debt is queued. None establishes coverage of all required behaviors.

The document is candid in its detailed sections. The defect is the promotion of those accounting results into an E1–E7 fidelity floor. A reader can reasonably leave with a stronger conclusion than the detailed evidence supports. “All latitude included” is likewise an aspiration, while the inventory still has pinned, narrowed, unknown, and refused axes.

**Change:** publish three separate release predicates: (1) no unclassified failures, (2) zero known wrong answers within an explicitly named supported profile, and (3) a justified behavioral envelope for that profile. Count open wrong-answer cases and guarded wrong-answer classes alongside untriaged ones. Keep intentional red tests; do not change their expected Go behavior to make a release green. A conditional research snapshot is useful, but label it that way.

### F2 — Blocker for G-PIN: the driver/relation bridge is not a valid contract as written

Reasoning-surface plan §1.6 proposes:

```text
run P e a fuel ch = ok r ↔ ∃ m, StepsM (init P e a) m ∧ ...
```

The left side fixes `ch`; the right side existentially selects an arbitrary nondeterministic path. A two-result program immediately defeats the reverse implication: the relation reaches result B, while the specified stream selects A. The terminal equivalence also omits the fuel bound. Furthermore, current `StepM` does not carry `RaceState`, whereas `execProgLoop` runs `raceUpdate` on each step (`Multi.lean:2149,2392`). Erased pool reachability alone is not the driver's full acceptance condition. Output prefixes also require a trace-bearing relation or an explicit projection theorem.

These signatures are explicitly unelaborated sketches, so this is **not an unsound theorem in the repository**. They nevertheless define the proposed pin and estimate I5 as a late, short task. The needed correction affects the entire consumer contract.

**Change:** state and elaborate separate bridges: fixed-stream execution to a stream-labelled trace; and `∃ fuel ch, run ... = observation` iff a suitable finite, detector-valid, observation-bearing trace exists. Account explicitly for initialization, terminal priority, main exit, output, and the cost convention. Prove a two-choice example in each direction before scheduling the bridge as routine work. Do not assume per-step existential stream witnesses compose into one run without a composition argument.

### F3 — Blocker for G-PIN: a list of frames does not establish a generic Iris context instance

Reasoning-surface plan §1.7 promises unconditional `step_fill`, `step_fill_inv`, and an `EctxLanguage` instance, then permits a recover-specific side condition. Those are different contracts. The pinned Iris `Language.Context` requires unconditional step transport for its chosen context; an extra recovery premise cannot simply be inserted into the existing class. [Pinned Iris context laws](https://raw.githubusercontent.com/leanprover-community/iris-lean/e7a0a43814c4f1154ca0c8049883ca56c2288b86/Iris/Iris/ProgramLogic/Language.lean), lines 250–259.

Reproduction using the current core (`ContractProbes.lean` in this review's evidence): `recoverResult` below an ordinary frame ending at `.stop` returns nil. With a `panicResumeK` appended below the same frame, it returns the panic payload and marks the outer chain recovered. This changes both the returned value and the continuation. Appending frames therefore does not preserve the recover step. See `Machine.lean:2657–2690` and `StepFn.lean:386`.

The issue affects forward transport as well as the inverse law mentioned by the plan. Boundary-crossing signals and panic handling deserve the same adversarial treatment. Changing the representation to `List Frame` is still useful; it does not solve context sensitivity.

**Change:** run a consumer contract spike now. Either restrict the admissible context class, provide explicit continuation/handler-sensitive bind rules, or redesign the semantic interface so the needed locality laws actually hold. A basic Iris `Language` interface can be useful without a generic `EctxLanguage` instance. Require worked examples with nested defer/recover, labelled control flow, and frame-local allocation. Keep this adapter test outside the shipped semantics dependency graph if necessary; do not postpone discovering whether the consumer fits until after the refactor.

### F4 — High: concurrent proof readiness still depends on an unvalidated reduction

`NPDRF.lean` is commendably explicit: its reduction proposition is a draft, refutable as written because of main-exit effects, and separate from machine-step-to-Go granularity. `schedPick` (`Multi.lean:2367`) restricts switching to designated boundaries. `Race.lean:1532` reconstructs memory accesses in a separate table. These choices are semantic commitments, not merely executable optimizations when a consumer takes the relation as its language.

The detector experiment's zero observed HOLE cells does not prove that the detector follows the Go memory model exactly. Its own recorded campaign includes uncertified rows and a known over-refusal. Shared access tables can make the detector and an internal race predicate agree while both miss an access. C1 removes the duplication between memory execution and footprint extraction, but equivalence to the **old table** alone cannot establish the table's external correctness.

Go's DRF-SC guarantee is about programs with no racy executions and memory operations satisfying the language's sequencing rules. It is not permission to declare a restricted schedule search race-free and transfer arbitrary invariants. [Go memory model](https://go.dev/ref/mem), especially requirements 1–3 and DRF-SC.

**Change:** establish a clearly scoped reference step/event model at the required access granularity; distinguish it from the efficient scheduler and exploration engine. Either prove the reduction for the actual observable projection, or expose the reduction and DRF conditions as explicit unresolved transfer assumptions. Move the granularity/reduction acceptance decision before a concurrent consumer pin. A sequential consumer milestone can proceed independently. Do not require a full weak-memory model for racy programs to make this progress.

### F5 — High: `Accepted` and `StateWf` do not yet support the promised refusal-free execution claim

`StateWf` is `ExecState.locSup σ ≤ σ.nextAddr` (`StateWf.lean:645`). The audit probe constructs a `.bool` cell containing `.int 7`; `decide (StateWf illTyped)` returns `true`. This is not a preservation-proof bug: the invariant proves exactly its narrow statement. It does not establish heap typing, valid field/index paths, interface-box validity, function arity, or complete method metadata. `State.lean:25` also records that allocation does not normalize values.

The proposed `run_refusal_free` varies between §1.5 and §1.9, and neither sketch adequately specifies a valid entry and typed argument boundary. More fundamentally, quarantined code permits partial exports, whereas the target `Accepted` rejects refusal markers. Syntactic acceptance, structurally valid IR, and “every reachable operation supported” are different predicates. Admitting an unused quarantined declaration is useful; silently turning its absence from one run into a total program guarantee is not.

**Change:** define `WireWellFormed`, `ProgramWellTyped`, valid entry/arguments, and a feature/extern support contract separately. Prove that decoding yields the claimed structural invariants. Make runtime typing a preserved invariant or establish an equivalent checked boundary sufficient for progress. State the strongest refusal-free result justified by those premises; do not publish it as an assumed promise with no measurable discharge plan. Prioritize allocation normalization, the C2 bound theorem, and representative progress lemmas before reflection multiplies the consumers.

### F6 — High: evaluation-order repair needs a general semantic design, not an indefinite chain of hoisting patches

E13's explicit `unseqPanic` choice and relational rules obey the merge invariant. However, `probeK` deliberately discards a successful early value (`Machine.lean:4681`) and may defer a panic for residual reevaluation (`StepFn.lean:155`). BUG-101 documents the resulting missing value behavior when a sibling call mutates the operand's source. BUG-104 documents another hoist/panic ordering violation. These are evidence of a family-level abstraction problem, not just isolated missed syntax cases.

The Go emitter has roughly 12,000 lines in `emit.go`, plus additional desugaring modules. Its order transformations now carry much of the language semantics. A typed wire validates the output's shape; it does not establish that moving an evaluation preserved source behavior. The SpecTec obligation inventory is useful, but no working translation-validation pipeline currently closes that boundary.

**Change:** specify expression evaluation as a dependency/ordering relation over value production, effects, and failure. Decide how lowering preserves all permitted outcomes and excludes forbidden ones. This might use explicit ordered regions and unordered operands; it does not require allowing arbitrary interleavings everywhere. A bounded prototype should cover calls, receives, short circuiting, multiassignment, mutation, and multiple panics. Add generated/metamorphic interaction tests and minimized counterexamples. Implement one small translation certificate before making the external SpecTec route the sole long-term assurance answer.

### F7 — High: gc naming is still restricting semantic identity and realistic package support

The recent identity/display split is progress, but `TypeId.unqualified` still parses the minted key (`Value.lean:522`). `keyPathHazard` rejects dots and escaped path bytes (`identity.go:131` onward); `load.go:209` tells callers to vendor at a dot-free path. That is an avoidable representation constraint on ordinary module paths.

The C6 “impossibility” classification is too broad. `localTypeInstantiationRefused` in `Corpus/coverage/exec/scoping/local-type-identity/main.go` constructs a `box[score]` and returns integer 4. It does not observe a compiler-generated name at all. Exact reproduction of gc's type-display counter is not a prerequisite to modeling that computation or its type identity. This is a documented refusal, not a hidden wrong answer, but the rationale risks making a temporary encoding choice permanent.

**Change:** use opaque/interned semantic IDs with explicit package, declaration/scope, and instantiation structure. Store display metadata separately and classify implementation-specific display operations at their point of observation. Never fabricate a gc name; if an exact-display profile cannot support an operation, refuse that operation explicitly. Revisit the C6 permanent-exclusion proposal. Add a module-aware source manifest that records selected files, language version, imports, and package identities without requiring semantic path rewriting.

### F8 — High: cached observation sets are not invalidated by the full semantic dependency set

The slow-tier cached path validates wire hash and row parameters (`scripts/diff-coverage:1779–1805`) and checks four current-driver streams against the saved set. The mandatory post-merge recertification trigger is changes to `wire.go` or `NativeToIR.lean`. A change only to `StepFn`, `Ops`, `Multi`, the checker, or observation projection can alter an unsampled result without changing wire bytes. A stale set can then mask a narrowing or miss a widening until the nightly slow run.

The code discloses this as `CERTIFIED-CACHED`; this is not a finding that today's saved set is wrong. It is a release-gate gap: the provenance checked is insufficient to establish the saved claim about the current interpreter.

**Change:** bind certificates to a semantic-source/build fingerprint, Lean toolchain, observation schema, and relevant checker/enumerator version as well as wire and parameters. Recertify on those changes, or replay a retained proof certificate against the current checked semantics where supported. Make stale certification a release-blocking result. Four samples remain a useful smoke test, not certificate reuse justification.

### F9 — Medium: the negative suite validates Go fixtures, not frontend rejection correctness

`scripts/coverage-negative:195–211` runs `go build` and checks a diagnostic substring. It never invokes the native frontend or decoder. Thus 394 PASS means the intended negative sources are rejected by the Go oracle. It does not demonstrate that GoLean rejects each invalid source for a suitable reason. Frontend unit tests do cover some rejection cases; the suite's aggregate claim should remain distinct.

**Change:** retain the oracle fixture check and add a separate frontend rejection leg. Distinguish type error, unsupported valid syntax, parser failure, and infrastructure failure. Add malformed-wire tests for missing types, invalid indices, duplicate IDs, bad method records, and arity; the current decoder's `.getD .int` discard-temp fallback (`NativeToIR.lean:1507,1584`) is an example of a boundary that should require metadata or derive it from a validated callee signature.

### F10 — High: the reference model should own its semantic relation and coherence laws

The charter says the relation and soundness modules are destined for extraction into the reasoning product, while the merge invariant requires them to keep pace with the executable. The master plan also needs their theorems for the public interface. Extracting the semantic relation makes coordinated evolution harder precisely where the project needs the strongest gate.

**Change of direction recommended:** keep the semantic transition relation, observations, invariants needed to state its domain, and executable/relation coherence in this repository (optionally separate Lean targets). Keep Iris resources, WP rules, program proofs, tactics, and consumer-specific ghost state downstream. “No Go verification claims” is a useful product statement; “no proofs here” is not a useful architectural boundary. The existing checker and soundness proofs already demonstrate why. This revises the proposed extraction, not the decision to keep Iris as a separate customer.

### F11 — Medium: source-through is the right default, but reflection is a major semantic expansion

The source-through library policy and byte-pinned overlays reduce invented behavior. Retiring the remaining six fmt shims is worthwhile. However, “facility” versus “shim” and numeric caps do not measure semantic trust: the reflection memo proposes substantial replacement Go text and new machine operations. Addressability, mutability, unexported fields, descriptor identity, nil/invalid values, tags, and dynamic methods must each be correct.

There is a concrete representation question before T1: G6 §4.2 offers `typeDesc (t : Ty)` or an index after C2, while the consumer plan commits to `typeDesc (idx : TypeIdx)`. C2 indexes declared types; builtin and composite `Ty` values are not all declarations. `TypeOf(1)` and `TypeOf([]int{})` require a descriptor scheme covering those types. A declaration index is not automatically a universal type descriptor.

**Change:** gate T1 on a small type/descriptor algebra and addressability tests, including builtin, unnamed composite, recursive, defined, and interface types. Retain a modest `reflectlite` slice if it unlocks the selected consumer. Stage full fmt/JSON after that consumer actually runs. Track semantic obligations and replacement-code surface, not only category counts. Source-through proves nothing by itself about the runtime operations it invokes.

### F12 — Medium: portability and independent evidence need executable commitments

`Platform.lean` has one actual `gcAmd64` instance and a global `platform`. `FloatBits.lean` deliberately models non-fused arithmetic and a restricted NaN policy. Those are useful stated profiles, not full portability. Static 386 acceptance does not validate 32-bit execution. A version sweep with one compiler cannot detect cross-version differences.

Likewise, many handwritten rows and fuzz cases share the same emitter, observation codec, and pinned gc oracle. They are valuable but correlated evidence. The master plan reports no Cedar functional MATCH and only a wire pin for the raft twin in this repo; percentage of declarations emitted is not end-to-end correctness.

**Change:** choose one real end-to-end workload and make its normal, error, and boundary paths a next-phase milestone. Add scheduled external tests on fragment/order changes, a second oracle configuration, and a second execution platform when available. Report accepted executions and newly exposed interactions, not just cumulative row counts. Retain imported source hashes and record transformations applied to downstream subjects. Separate language-profile guarantees from gc-compatible diagnostics, allocation limits, and floating-point policy.

### F13 — Medium: planning and gate records are consuming auditability

The master plan is 1,681 lines and explicitly supersedes nothing; its consumer plan is 1,821 lines. `README.md` sends newcomers to older architecture/roadmap documents instead of the plan of record. `AGENTS.md` points to a Gobra-era operating guide and a July handoff as current instructions. The master plan itself retains old numbers and a stale twin hash in §2.5 despite a corrected snapshot elsewhere. The reported reconciler findings are not the whole documentation-drift surface.

The many records are evidence of care, but duplicated current-state prose creates ambiguity about which claim is binding. Adversarial review rounds repeatedly finding wrong-answer and fail-open defects also suggest that more retrospective prose is not sufficient preventive control.

**Change:** one short current contract, one generated status/obligation table, and immutable per-change evidence manifests. Archive historical operating instructions and redirect every entry point. Generate current counters and dependency views. Keep rationales, but remove repeated narratives from executable scripts and baseline headers where a concise invariant and document pointer suffice. Use release names such as `baseline-compatible` versus `supported-profile-conformant`; a generic green gate should not require reading thousands of lines to interpret.

## Assessment by subsystem

| Subsystem | Assessment | Next evidence needed |
|---|---|---|
| Scalar/runtime operations | Substantial, testable implementation; integer-width and softfloat discipline are strengths | Generated boundary interactions; explicit platform/float profile |
| Type identity/interfaces | Good direction, incomplete separation of identity, display, and method provenance | F7 identity tests; structural type/descriptor coverage; BUG-098/099 closure |
| Heap/locations | Dense typed-cell representation is a sound engineering direction | Typed validity and progress; same-root disjointness; aliasing/views; allocation normalization |
| Control/defer/recover | Explicit machine and paired rules are valuable | Consumer-safe context contract; nested nonlocal-control tests |
| Evaluation order/frontend | Largest concentration of semantic transformation risk | Family-level ordering model; translation-validation prototype; interaction generation |
| Concurrency/sync/atomics | Meaningful implementation with explicit choices and HB bookkeeping | Fine/reference correspondence, exact domain of race claims, concurrent consumer contract |
| Enumeration | Strong checker architecture within a restricted fragment; DFS and caching remain additional trust surfaces | Claim-specific certificate provenance, trace/output support, optimized/reference comparison |
| Standard library | Source-through and pinning are preferable to accumulating replacements | T1 descriptor gate; consumer-driven admissions; eventual fmt retirement |
| Validation/CI | Robust baseline regression machinery; fresh corpus results reproduced | Semantic certificate invalidation, frontend negative leg, independent cadence |
| Consumer readiness | Not ready under the stated pin contract | Correct theorem signatures, admission premises, live adapter examples |
| Real-world reach | Promising static coverage, incomplete functional evidence | One reproducible end-to-end subject with meaningful error-path behavior |
| Documentation/process | Excellent historical traceability; weak current-state compression | One authoritative current contract and machine-generated evidence index |

## Revised next-phase plan

The master plan's own exit checklist needs these qualifications:

| Criterion | Audit disposition |
|---|---|
| E1 total/sorry-free core | Escape-hatch scans and build pass; totality does not imply semantic correctness |
| E2 whole-corpus lower bound | Not established literally; the zero counter measures untriaged wrong answers (F1) |
| E3 every red rowed | Baseline/bug checks and accounting reproduced; not a fidelity certificate |
| E4 spec sections classified | Classification is useful inventory, not tests of all normative clauses |
| E5 choice census matches code | Reconciler agrees; matching known constructors does not discover omitted latitude |
| E6 pins have obligations | A debt-management condition, insufficient for an all-latitude release |
| E7 exact go_mem race refusal | Not established by the sampled detector campaign; F4 remains |
| E8 consumer interface | Not met; F2/F3/F5 must change its contract before implementation |
| E9 sequential frontier | Not met; open rows remain |
| E10 no injected library text | Not met; six fmt shims remain, and facility replacements need explicit scope (F11) |
| E11 downstream subjects | Wire pin reproduced; no current end-to-end Cedar result independently established |
| E12 oracle cadence | Scripts/workflow exist; second configuration and campaign cadence remain incomplete |
| E13 post-reshape assessment | Future work; require an open-ended reassessment, not a predetermined unchanged result |


### Gate A — make the consumer contract real

Before broad restructuring, elaborate corrected interface signatures and prove small contract examples. Required artifacts: stream-quantified bridges; the allowed context class and its laws; observation/terminal/output policy; typed entry and admission predicates; declaration versus universal type-descriptor decision. Demonstrate recover and nondeterminism counterexamples against the rejected contracts. Produce a minimal downstream adapter exercise without adding Iris to this package's default dependencies.

**Exit:** no false or ambiguous signature remains in the proposed pin; each unproved result has an exact statement, prerequisites, owner, and explicit effect on consumer claims. “A theorem target exists” is not the same status as “the theorem is provided.” Estimate subsequent work only after this gate.

### Gate B — repair fidelity families and consolidate memory

Continue B7 and C1, with actual emitted accesses and reviewed `peek` uses. Fix BUG-098/103/104 and give BUG-099 a concrete owner. Resolve BUG-101 within the evaluation-order design rather than deferring the value axis indefinitely. Replace key-grammar restrictions with semantic identity metadata. Prove the C2 bound property and strengthen allocation/admission checks. B6/C3 remain reasonable implementation tasks, but their value is measured by the corrected consumer laws, not constructor counts.

**Exit:** the named supported sequential profile has zero known wrong answers; generated ordering/aliasing/exception tests pass; memory traces cover every modeled user access; invalid admission is rejected explicitly. Known unsupported profiles remain visible reds.

### Gate C — demonstrate utility and independent agreement

Select the smallest genuine Cedar functional driver or an appropriate raft component, not merely its wire emission. Admit only the library facilities it needs, beginning with the vetted T1 surface if applicable. Exercise normal and failure paths. Run the second-oracle and upstream-test lanes on the relevant features, and add the frontend negative leg. Make certificate provenance cover all semantic dependencies.

**Exit:** repeatable end-to-end differential success on a real target and a consumer proof/example using the public interface without unfolding implementation internals. Report residual assumptions prominently.

### Gate D — separate sequential and concurrent pin offers

A sequential pin can be useful before full concurrent reduction is proved. A concurrent pin must resolve or explicitly scope the reference granularity, DRF domain, race treatment, main-exit observations, and scheduler reduction. Keep the corresponding semantic definitions and coherence tests here. Consumers may knowingly accept an experimental conditional contract, but that is a different release from a trustworthy Go-transfer guarantee.

**Exit:** the pin records source/profile/toolchain fingerprints, exact observation equivalence, supported domains, proved bridges, remaining assumptions, live consumer tests, and fresh certification for affected semantics. The next assessment should search for changed obligations; do not set its expected answer to “unchanged.”

The master plan's 17–22-session critical-path and 28–38-session total estimates are useful guesses for mechanical refactoring. They are not credible assurance estimates while Gates A and D remain unresolved. Use ranges after the prototypes, and reserve capacity for counterexamples, changed predicates, and rerunning independent tests. I would not launch the whole proposed four-lane wave unchanged.

## Evidence appendix

Run environment: Linux/amd64; Go 1.26.5; Lean 4.32.2 at `f3b06c705e6c85f5314019d5d3baab0fec5b580c`; Lake 5.0.0. Initial working tree clean. The earlier nested Bubblewrap startup failure was resolved by removing the inner sandbox; ordinary tool execution succeeded. A direct Go unit-test attempt using the repository's macOS `/private/tmp/go-build` convention failed on this Linux sandbox; the successful unit run used the workspace cache below. This is an environment adjustment, not a semantic test change.

Commands:

```sh
TMPDIR=/home/dev/projects/golean/.tmp/audit-20260905 scripts/capped scripts/ci --diff
GO111MODULE=off GOCACHE=/home/dev/projects/golean/.tmp/audit-20260905/go-build \
  go test ./tools/nativefrontend ./tools/lowerdiag ./tools/coverageharness
python3 tools/reconcile-records
scripts/capped lake env lean .tmp/audit-20260905/ContractProbes.lean
```

**Final gate result: PASS, exit 0.** The core build was warning-free. The three Go packages passed. Interpreter evaluation tests reported 198 ok, 0 fail. The full differential run reported 3,593 cases, 3,347 pass, 246 fail, export_status=0; the baseline comparison was FULL 3593/3593 with no regression. The negative run reported 394 pass, 0 fail. Slow-tier sets were cached under the documented `--diff` policy; this is not `--slow` recertification. The complete gate log is `.tmp/audit-20260905/ci-diff.log` in the primary checkout; its final summary, result metadata, artifact hashes, and reproduction probes are preserved in [the evidence directory](evidence/2026-09-05_project-gate-audit/README.md).

The contract probe prints nil, then an interface containing the runtime panic payload, then `true` for address-boundedness of an ill-typed cell. It is a compiled evaluation probe, not a claimed kernel proof of a counterexample theorem. The print probe, emitted with a freshly built current frontend, returns `audit-output\n` and integer 7 through `native-json-run`; `coverage-observations --engine dedup` exits 1 naming the output event. A first attempt used an old preexisting `artifacts/nativefrontend` binary and refused statement-position println; that attempt was discarded, not used as evidence about current source.

Primary external sources consulted were the Go specification and memory model and the exact parked Iris dependency revision. Project-specific claims above are grounded in the audited local code and records. No remote CI-run history was inspected, and scheduled workflow presence is not evidence that a recent remote run succeeded.
