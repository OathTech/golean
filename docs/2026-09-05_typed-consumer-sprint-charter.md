> **Landing preface ([AGENT] landing chunk L6 `land/sprint-records`,
> 2026-09-07).** Below this preface is the sprint charter VERBATIM as
> committed on branch `typed-consumer-sprint` at `7edc298f`
> (`docs/2026-09-05_typed-consumer-sprint-charter.md`; sprint commits
> `10fefeb3`, `5a4aca9e`); not a character of it is edited. Provenance of
> its [USER] statements (landing audit B, R18): the approval «Agree with
> all 5» and the K4 clarification «merges *to main* are always
> user-approved. Feature branches can be merged to by agents, when standign
> approval is given by the user» (§2, typo included) were received by the
> [AGENT] coordinator on 2026-09-05 and RELAYED into this document — cite
> as relayed, not firsthand; the status line's "The [USER] clarified K4:
> …" is the coordinator's paraphrase of that same relayed statement. The
> standing approval K4 grants is SPRINT-SCOPED (feature/sprint-branch
> integration for this sprint only) and is not a standing permission of
> any kind on main: every merge to main in the landing was a separate
> at-that-moment [USER] sign-off. The sprint this charter authorized was
> PAUSED BY THE USER on 2026-09-06 (`docs/2026-09-06_typed-sprint-pause-state.md`)
> and its work landed on main in reviewed chunks on 2026-09-07 under the
> 2026-09-07 ruling (`docs/2026-09-07_typed-sprint-landing-plan.md`); the
> FINAL status of O1–O5 is in `docs/2026-09-05_typed-consumer-sprint-handoff.md`
> and the roadmap disposition in `docs/2026-09-05_master-plan.md` §7.8. The
> charter's relative links resolve against `docs/` as on the branch
> (`2026-09-05_master-plan.md`, `agent-sandbox.md`, `../CLAUDE.md`,
> `../AGENTS.md`, `../GoLean/Interface.lean`,
> `../spikes/iris-customer/GoLeanIris/Program.lean` all exist on main).

# Long-cycle charter: a typed sequential contract, exercised by Iris

**Status: APPROVED — [USER], 2026-09-05.** K1–K5 are approved for execution.
The [USER] clarified K4: merges to main always require user approval;
agents may merge into feature branches under standing user approval.
This sprint has that standing approval for internal integration and reviews.
No merge to main or push is authorized by the kickoff approval.

**Starting point:** `main` at `47195683`. Plan of record:
[master plan §7.4.1](2026-09-05_master-plan.md#741-executed-consumer-contract-increments-2026-09-05).
Standing authority: [CLAUDE.md](../CLAUDE.md) and [AGENTS.md](../AGENTS.md).

## 1. Mission and outcome

Build a reusable, auditable contract connecting an admitted GoCore program
to its initialized machine, typed execution, and observable results. Exercise
that contract through the thin Iris customer, then preserve it through the
context/store separation that prepares GoLean for the memory work.

At completion, a reviewer should be able to follow this chain through named
definitions, kernel-checked theorems, and reproducible evidence:

> A native Go fixture lowers to this exact artifact → a separately defined
> admission judgment accepts it → the real driver establishes the runtime
> invariant → semantic steps preserve that invariant → reusable customer
> rules establish a result → the real driver reads out that result and output.

The first arrow remains a tested frontend correspondence, not a proved Go
compiler correctness theorem. Each later arrow must state its own domain,
resource bounds, choice assumptions, and terminal policy. A proof about the
model is evidence about the model; Go fidelity also requires specification
arguments and differential observations.

This is an outcome-based, multi-session block. There is no invented session,
token, or calendar deadline and no success declaration based on elapsed
effort. The agent may restructure the implementation after learning from the
first proofs. It may not silently reduce the promised outcomes.

| Required outcome | Observable completion criterion |
|---|---|
| O1. Typed Boolean contract | A new admission judgment and checker reject the existing unbound-variable counterexample; generic setup, preservation, progress, and typed readout theorems cover the declared Boolean profile. |
| O2. Typed recovery customer | An explicitly bounded extension covers the existing A2 program and a second independent fixture; both use shared admission/setup and call/capture/unwind contracts rather than bespoke entry-state assumptions. |
| O3. Evidence that can challenge the contract | Positive and negative admission tests, semantic counterexamples, Go differential cases, dependency audits, and independent adversarial reviews check the actual claims and their limits. |
| O4. B7 and its I1 companion | Immutable program/platform context is separated from mutable state; refusal markers move out of executable IR as planned; the contracts and customers survive, with the preservation evidence specified in §4. |
| O5. A branch ready for the closing decision | Integrated source, reproducible gates, reviews, claim/assumption ledger, and an updated roadmap are available at a named commit. Main is unchanged. |

All five are mandatory. Partial work remains useful, but is reported as
partial. C1 implementation, a stable pin, and completion of all of Gate A
are not completion criteria for this block.

## 2. Critical decisions to settle once, before kickoff

The [USER] approved all five defaults: “Agree with all 5.” This authorizes
the bounded sprint, including parallel agent work and the specified
independent reviews. K4 was clarified in the same message: “merges *to main*
are always user-approved. Feature branches can be merged to by agents, when
standign approval is given by the user”. The table below records the approved
defaults; its recommendation explanations are retained as rationale.

| Decision | Recommended ruling | Why it belongs at kickoff |
|---|---|---|
| K1. Scope and order | Commit to O1–O5: Boolean contract, restricted recovery contract, then B7/I1. Produce a C1 handoff but leave its implementation for the next block. | This sets the ambition and prevents a second memory-semantics project from absorbing the contract work. |
| K2. Supported domain | Approve the two minimum profiles in §3, opt-in admission, explicit resource premises, and terminal-aware safety. Require the specified witnesses; agents may strengthen auxiliary invariants, but may not exclude required witnesses or weaken outcomes. | The domain of the theorem is a product decision. A broad theorem name must not conceal a smaller promise. |
| K3. Change authority | Authorize representation changes and fidelity repairs needed by these outcomes when existing Go rules and project rulings determine the behavior. Require a separate, reviewed repair with a failing regression first. Defer new semantic-policy choices and changes to the trusted base. | This permits real implementation work without licensing arbitrary decisions about Go latitude or proof assumptions. |
| K4. Internal reviews and integration | Standing approval covers the review scope in §6, separate implementation worktrees, and merges into feature/sprint branches after gates pass. Internal checkpoints are agent-reviewed acceptance checks; no routine user audit ask is needed between them. Every merge to main requires explicit user approval. | This gives agents authority for internal integration while keeping the user in control of main. |
| K5. Closing authority | Reserve main merge, push, release/pin claims, scope reductions, and unresolved critical choices for the user at the closing review. Keep the current toolchain pins and build/sandbox protections. | The sprint can finish autonomously with a concrete result while preserving control over product commitments and publication. |

K4 changes only the internal review/integration workflow for this approved
sprint. It does not waive validation, permit self-approval, settle any other
named design gate, or waive [CLAUDE.md](../CLAUDE.md)'s requirement to merge
to main only on “explicit at-that-moment sign-off.” Unresolved named design
gates remain hard stops for the work that depends on them. If one becomes
necessary, use §7; do not reinterpret it as an ordinary implementation choice.

## 3. Required semantic and consumer contracts

### 3.1 O1: scope and type the Boolean fragment

Preserve A3a's honest meaning. Its `BooleanAdmission` establishes indices,
entry argument shape, and syntax, and deliberately accepts an unbound-variable
counterexample. Introduce a separately named stronger predicate; do not
retroactively label A3a a typing theorem. Representation changes later in the
sprint must preserve these distinctions and carry migration regressions.

The stronger profile must support Boolean parameters and named results,
Boolean literals and operators, assignments, local initialization, nested
blocks, sequencing, branches, and returns. Check the whole admitted program,
not only the selected entry. Define binding, legal shadowing, initializer
scope, result scope, and return obligations against the actual GoCore
constructors and lookup behavior. Native name generation is not a semantic
typing rule. Reject duplicate declarations where invalid, escaped locals,
unbound reads/writes, and ill-typed argument/result use.

Minimum positive witnesses include an argument-dependent function, nested
scope with legal shadowing, and both branches producing a named result.
Include a valid zero-initialized local/result case: Go does not generally
require assignment before reading a declared variable. Distinguish zero
initialization from a missing binding. Reject invalid fall-through according
to the profile's declared function/return policy; do not import a false
definite-assignment discipline from another language.

Required proofs are generic over programs in the profile:

1. An independently defined typing/admission judgment and a total executable
   checker, with soundness and completeness for that judgment. Define error
   cases clearly enough to distinguish out-of-profile input from malformed
   input. Neither the judgment nor checker may be defined by running the
   program and observing success.
2. An entry/setup theorem for the actual `runProgramSetupM` path. Under
   admission and explicit, independently checkable initial-resource
   hypotheses, setup succeeds and establishes parameter bindings, result
   cells, initialized values, valid locations, and the typed machine
   invariant. A premise saying setup already succeeded is not this theorem.
3. A runtime invariant covering the environment, store, current computation,
   and continuations; preservation for every permitted relational successor
   in the stated domain, with a corresponding interpreter result through the
   coherence theorems. Preservation must address the continuation changes,
   not just the heap after a selected expression.
4. Progress and readout contracts: a reachable nonterminal state has a legal
   semantic continuation, and normal termination permits the actual driver
   readout at the declared result types. Interpreter exhaustion is reported
   separately and is not termination or a successful execution.

### 3.2 O2: extend to a small family with recovery

Build a second named profile extending the Boolean foundation far enough to
admit the complete existing
[A2 artifact](../spikes/iris-customer/GoLeanIris/Program.lean). Its minimum
surface is finite, sequential code with direct calls, statically identified
closure targets, captured Boolean root-cell references, local initialization,
named results, deferred calls, explicit string panic payloads boxed in an
empty interface, comparison with nil, and recovery calls with their dynamic
direct-deferred-handler condition. The normal and uncaught-panic A2 entries
remain controls.

The profile may exclude recursive call graphs, arbitrary higher-order
dispatch, loops, globals/package initialization, methods, general interface
operations, arbitrary pointer arithmetic/paths, concurrency, and inspection
of runtime-generated error payloads. Those exclusions must be structural,
checkable restrictions. They must not be hidden assumptions about paths a
fixture happens not to execute. Check all function/closure bodies, signatures,
capture environments, return destinations, and deferred-call registration.

Give this extension its own total checker and judgment/checker equivalence,
and the same generic setup and runtime obligations as O1. Supply
preservation for their admitted call, return, capture, defer, panic, and
recover transitions, and terminal-aware progress/readout for this profile.
All required operations must be covered; admitting their syntax alone does
not satisfy O2. State precisely what ownership facts are semantic runtime
facts and what additional resources the Iris customer must provide.

Uncaught Go panic is a legitimate terminal outcome. Distinguish it from a
model refusal and from fuel exhaustion. The current Iris adapter treats
uncaught panic as stuck; do not claim universal Iris `NotStuck` from typing.
Retain normal/recovered `NotStuck` customer proofs with their appropriate
preconditions, and account for uncaught panic through the semantic terminal
observation contract. A broader adapter policy would need its own explicit
design argument, not a relabeling to make a theorem pass.

Refactor the existing recovery proof to use generic entry/setup contracts
and reusable customer rules. Add a separately written native Go fixture with
an input-dependent result, an ordinary helper call, and two deferred handlers
sharing a captured result cell. Their order must affect the result; include
normal and recovered paths and a negative control where a recovery call
outside the effective direct-handler context returns nil. That call is valid
Go, not a static typing error; the profile must admit this control. This
exercises call composition, aliasing, and unwind order beyond the original
straight-line example.

The second fixture must reuse the same admission, setup, and call/unwind
rules without changing their statements for that fixture. Program-specific
functional arguments and bounded termination witnesses are allowed. An
exact artifact whitelist, a premise containing the desired whole execution,
or a complete concrete trace substituted for reusable WP rules is not reuse.
Retain explicit output and final `loadMany`/driver connections.

### 3.3 Bounds, assumptions, and interface discipline

Use the existing corrected choice-sensitive bridges. Preserve choice
consumption and residual choices, not only final values. State whether each
result is about a fixed legal choice stream, all legal choices, or existence
of a run; do not silently exchange those quantifiers. Do not introduce an
unconditional evaluation-context or converse pool-reachability law.

Fuel, allocation capacity, platform, and admissible initial-state hypotheses
must be visible. Prove that admission/driver setup supplies the relevant
invariants; do not assume the whole future execution is safe. Where enough
fuel is required, provide a usable bound or a separate termination/resource
obligation, rather than disguising execution success as “sufficient fuel.”
No general unbounded-termination theorem is required by this charter.

Expose the reusable semantic contracts through
[GoLean/Interface.lean](../GoLean/Interface.lean). Keep Iris resources, WP
proofs, and tactics in the opt-in spike. The second customer's entry,
composition, and readout proofs should use the exposed contracts. If adapter
implementation still needs machine constructors, isolate and inventory that
dependency; do not call the interface stable or hide a new whole-machine
unfolding in an example's helper lemma.

## 4. O4: test the contract through B7, then prepare C1

After the first generic setup/invariant contract is established, implement
the planned `ProgramCtx`/`Store` separation. Move immutable program/type/
method/platform context out of the mutable execution state; remove repeated
context-equality premises where the representation now enforces constancy.
Keep platform parameters explicit and preserve the driver's existing default.
Develop against both live customers as the recovery work matures; integrate
only once all required contracts and customers pass on the final shape.

Treat the pure representation change and I1 refusal-marker relocation as
separate reviewable changes with separate measurements:

- **B7 representation:** state the old/new state correspondence and prove
  transition/driver correspondence with matching choices and observations.
  Carry the relational premises, invariants, soundness/completeness results,
  terminal classifications, and output through the change. Compare the whole
  executable corpus before/after: zero status drift and byte-identical
  captured observation/choice traces. Normalize representation-only internal
  dumps through the declared correspondence, not by dropping semantic data.
- **I1 companion:** remove the planned refusal markers from executable IR,
  moving rejection to the frontend/lowering boundary and the reserved opaque
  runtime-error information into the appropriate context fact. Preserve the
  accepted-program meaning, reserved-prefix invariant, and legitimate runtime
  errors. Add frontend/lowering negative tests that actually invoke GoLean.
  A Go compiler rejecting bad source is not evidence of GoLean's rejection.
  Record every intended earlier-stage refusal with old/new stage, case id,
  cause, and preserved support boundary. These declared stage movements are
  distinct from B7's zero-drift claim; no passing Go case may become a refusal
  merely to ease the refactor.

Do not bundle a fix for a discovered semantic mismatch into representation
equivalence. Preserve a red regression, isolate the repair, and establish
its justified behavior before resuming the equivalence argument. If I1
cannot be separated from an unresolved descriptor-algebra decision, freeze
that slice and use §7; report O4 as incomplete rather than renaming B7 alone
as the complete planned package.

C1's deliverable here is a concrete handoff: the resulting context/store API,
an inventory of memory operations and access-reporting sites, invariants the
customer actually needs, and the exact correspondence obligations for the
emitted access trace. Preserve the existing G-C1 ruling: equality is audited
arm by arm; an erroneous old footprint becomes a detector bug with a failing
regression first. Do not start C1, retire `stepAccesses`, alter access
granularity, or make a concurrent adequacy claim within this block.

## 5. Work organization and delegated decisions

Use one sprint integration branch with a designated integrator; keep the
primary checkout clean on main. Each writer owns a separate worktree and a
bounded responsibility. No agent writes into another agent's worktree.
Snapshot refs before rebases or other risky git operations. Do not merge or
cherry-pick archival work without reviewing it against the current machine.

The default dependency order is:

1. **Preflight:** pin the actual starting commit/toolchains; reproduce the
   admission/interface/A1/A2 gates and establish the full differential
   baseline used for B7. Write a constructor/profile coverage matrix and the
   candidate theorem statements before implementation.
2. **Boolean foundation:** admission, setup, invariant, preservation/progress,
   and readout. Independently review the statements and their assumptions
   early enough to avoid proving the wrong contract.
3. **Parallel work where useful:** extend recovery contracts/customer rules;
   implement B7 against the agreed Boolean contract; independently develop
   adversarial fixtures/evidence checks. Runtime fidelity fixes can use a
   separate lane only when their intended semantics are already determined.
4. **Integration:** migrate both profiles and customers to the new context,
   finish I1, resolve cross-lane findings, run the final gates and final
   adversarial review, then prepare the closing packet.

The agent chooses module names, proof decomposition, data structures within
the approved representation, checker algorithms, precise supporting
invariants, ordinary error messages, regression cases, lane allocation, and
the order of independent tasks. It can fix review findings, rebase, and
re-run affected gates without asking the user. Record consequential choices
as [AGENT] decisions with their rationale and evidence.

Use `~/cerberus-lean-proj/refined-cerberus/`, Brick, RefinedC, and the archived
GoLean reasoning experiments as design references when accessible. Locate
reference checkouts from the environment and record their revisions; these
are references, not new build dependencies. Prefer concrete lessons about
initialization, ownership, evaluation contexts, and adequacy boundaries. They
do not supply Go's semantics or justify importing their assumptions without
a proof.

Update a tracked sprint handoff and decision/claim ledger after each
integrated milestone and before handing work to another session. Include
branch/tip, next action, failed attempts, blockers, exact gate commands, and
artifact hashes. Report progress without requiring an answer. Context loss
or a session boundary must not reset scope, approvals, or known failures.

## 6. O3 and O5: evidence, review, and completion

### Required evidence

- **Claims ledger:** for each public theorem or advertised guarantee, list
  definition/theorem name, source path, profile, choice quantifier, resource
  premises, terminal/output policy, and status: proved, tested, assumed, or
  deferred. Give each assumption its intended discharge or downstream owner.
  A kernel proof of a checker agreeing with itself is not evidence that its
  domain is the right one.
- **Positive and adversarial cases:** cover legal scope/zero initialization,
  invalid bindings/captures/signatures, call/result typing, LIFO defer order,
  panic/recovery boundaries, and actual readout. Preserve all A1 context,
  choice, terminal, and output counterexamples. Keep the old accepted A3a
  unbound example and its rejection by the new typed profile side by side.
- **Go fidelity:** fresh native artifact checks and focused Go-vs-Lean runs
  for both customer families; exercise the relevant legal nondeterminism.
  Attach pinned specification rationale to new semantic rules and suspected
  fixes. Account for both observed Go behavior being modeled and every
  advertised modeled behavior being permitted by Go. Green samples alone
  do not prove the latter.
- **Kernel/dependency audits:** extend the current interface/admission and
  spike audits to all new public contracts and supporting local modules.
  Keep the current allowed foundational axioms (`propext`, `Classical.choice`,
  `Quot.sound`), the prohibitions on proof escape hatches, and the total-core
  policy. Check for new frontend/Iris imports into the semantic facade.
  Retain compiled negative controls that show the audit rejects an injected
  forbidden declaration, including an unused one.
- **Integration gates:** obey the standing per-commit CI rules; use focused
  slices during iteration. Run capped `lake build`, `scripts/ci --diff`, the
  full admission check, interface/A1 checks, and the Iris spike gate on the
  final runtime source. If wire/lowering changes, run `scripts/ci --slow`
  and refresh the certification record as required by the standing train
  rule, including at a subsequently authorized merged tip. Report cached
  certificates as cached and bind fresh evidence to its actual source.
  Changes touching detector inputs also require the relevant detector gate;
  a sampled campaign must not be presented as a full detector proof.

Run Lean/Lake via `scripts/capped`, within the existing resource envelope.
Follow [agent-sandbox.md](agent-sandbox.md) for caches and scratch. Do not
weaken caps, float dependency/toolchain pins, alter sandbox permissions, or
delete worktrees/scratch to get past a failure without applicable authority.
Avoid repeating a full expensive gate without a source change, failure, or
unresolved concern; reuse may be appropriate during iteration but must be
explicit. Final evidence must cover the final source, not a neighboring tip.

Report every corpus status change by stage. Known failing cases are not
passes; `unsupported`, `stuck`, lowering failure, and exhaustion never count
as Go conformance. Do not re-pin a baseline to hide regressions. Existing
out-of-profile bugs remain visible, with a precise explanation of why the
new profile excludes them. In-profile wrong answers block completion.

### Independent review, preauthorized at kickoff

Use reviewers other than the author of the relevant slice. Review both
statements and implementation; reviewers should try to construct admitted
bad programs and false uses of the exported theorems. The minimum scopes are:

1. **Admission and proof boundary:** vacuity, circular premises, scope and
   capture bugs, initialization/readout, all-successor preservation,
   choice quantifiers, fuel, and terminal/refusal distinctions.
2. **Go fidelity and B7/I1:** preservation correspondence, raw-name leakage,
   accepted/rejected boundary, frontend negative controls, observation/choice
   traces, runtime-error metadata, and interpreter/relation agreement.
3. **Customer and final integration:** actual reuse in both fixtures, Iris
   resource initialization, admissible call/unwind contexts, genuine driver
   observations, source-bound audit coverage, and reproducibility at the
   final integrated tip.

Resolve blocking findings and rerun affected checks. A justified disposition
must cite evidence and receive independent review; the implementer cannot
waive its own finding. A reviewer need not demand user input for ordinary
fixes inside the charter. A finding requiring a critical decision follows §7.

### Completion and closing packet

Declare **COMPLETE** only when O1–O5 are met, all required gates pass, and no
blocking review finding remains. Deliver:

- A named integration commit and ordered, reviewable changes, with the
  worktree state recorded and primary main clean.
- The claim/assumption ledger, profile definitions and examples, exact gate
  results, source/toolchain fingerprints, artifact hashes, and final reviews.
- A short migration note explaining what a downstream customer now consumes
  and what still depends on the experimental machine representation.
- Master-plan and handoff updates identifying discharged obligations and
  remaining Gate A/B/C/D work. No “Gate A complete” or stable-pin claim from
  this sprint alone.
- The C1 handoff and a closing decision packet for deferred critical issues,
  recommended next block, and a separate main-merge proposal.

If required work remains, use **PARTIAL — CRITICAL DECISION DEFERRED** or
**INCOMPLETE**, enumerate the unmet outcomes and preserve the independently
useful completed slices. Never turn a deferred obligation into a completed
one by changing its label, replacing a proof with tests, or narrowing the
required profile after the fact.

## 7. Critical issues discovered during the sprint

An issue is critical if resolving it would change promised outcomes or the
minimum supported profile, weaken a theorem/gate, alter the trusted base,
choose among unresolved interpretations of Go latitude, change observation
or terminal policy, require an unruled architecture gate, change public
release commitments, or take an action outside the approved authority.
Difficulty, a larger-than-expected proof, a failed test, or an ordinary
implementation tradeoff is not by itself a critical decision.

On discovering a critical issue:

1. Record the smallest reproducer, affected claim and dependent work,
   relevant rule/specification, alternatives, recommendation, and cost of
   deferral in the tracked decision ledger.
2. Freeze the dependent slice. Preserve the last justified implementation;
   do not select a new policy by changing the checker or expected output.
3. Continue independent work that remains valid under all recorded options.
   Update the user with the finding and its effect without requesting a
   routine mid-sprint decision.
4. Present the decision at the closing review. If it blocks all meaningful
   authorized progress, end the block early with the partial result and a
   concrete decision packet. This is the closing review, not an indefinite
   wait for an absent user or permission to self-adjudicate the issue.

Immediate contact is reserved for a user response strictly necessary to
protect ongoing work or resolve an external access/approval boundary that
cannot safely be deferred. Otherwise the expected interaction pattern is
**one kickoff approval, autonomous work with progress reports, one closing
review**. Closing decisions include main-merge/push authority, acceptance of
any proposed scope change, and the next charter; none is presumed here.

## 8. Effect on the overall GoLean plan

This block turns Gate A's admission and consumer requirements into a tested
engineering contract and completes the B7/I1 prerequisite for C1. It gives
the memory work invariants and real customers that can detect a damaged
proof interface, in addition to differential tests detecting changed
observations. It does not postpone B7 until Go has a complete formal type
system, or grow the spike into the downstream verification product.

The next block should implement C1 against this contract, preserving the
existing trace-equality/detector obligations and extending the supported
profile only when a concrete consumer requires it. Descriptor algebra,
broader fidelity families, general composition, Cedar/raft customer work,
and the distinct sequential/concurrent pin criteria remain visible roadmap
items. Bugs such as BUG-098, BUG-099, BUG-101, and BUG-104 are not discharged
by improved admission or by excluding them from these profiles.

The progress measure is the length and quality of the audited chain from
input to observation: fewer unexplained premises, more reusable proved
contracts, and stronger evidence for Go fidelity. The number of new accepted
constructors or the size of the Iris library is not the target.
