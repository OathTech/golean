# Gate A1 adversarial review and proposed next phase

[AGENT], 2026-09-05. Prepared at the user's request for an adversarial
subagent review and a plan for integrating A1 into GoLean. Base:
`79019a74c1e1c1418293d380d1fcfbd9ae489980`, branch `gate-a1-contract`.
Recommendations below are proposals, not new [USER] rulings, a merge
authorization, or a claim that the whole of Gate A has passed.

Read alongside the [A1 contract note](2026-09-05_gate-a1-contract.md),
[master plan §7](2026-09-05_master-plan.md),
and [validation evidence](evidence/2026-09-05_gate-a1-contract/README.md).

## Review and disposition

An independent subagent read every spike module, checked the proofs against
the current drivers, freshly elaborated six modules, checked the original
20 artifact hashes, and verified exact, tracked-clean dependency revisions.
It found no false theorem or driver-bridge discrepancy. It did not run the
full differential corpus or a clean dependency bootstrap.

**Final verdict: the bounded A1 experiment is ready for integration.**
The reviewer approved the R1 repair after inspecting its source and the
successful gate transcript. The normal core and spike builds passed, the
post-import audit checked 529 constants, and all three negative regressions
were rejected for the intended reason. No residual A1 blocker was found.

**R1 — medium severity, fixed and re-reviewed: incomplete axiom audit.**
The original audit ran during elaboration of `GateA1/Audit.lean`; declarations
after the scan were absent from its environment. The aggregate `GateA1.lean`
was also outside the scan. The lexical guard omitted the aggregate and
missed `private axiom`. The reviewer appended a private axiom of `False`
and a theorem using it; elaboration still exited 0 and printed the ordinary
audit success. This was a hole in the gate's claimed coverage, not evidence
that the delivered theorems used an illicit axiom.

Repair: `Audit.lean` now defines an audit action. A generated external
harness imports the complete modules, including the aggregate and probes,
before invoking it. Module inventory drift fails explicitly; lexical checks
cover the aggregate and private declarations. Dependency revisions and
tracked cleanliness are checked after dependency installation as well as
before the build. Three compiled negative fixtures test a trailing private
axiom in `Audit`, a private axiom in the aggregate, and a trailing private
proof using `sorry`. Each must compile, then fail the external audit with
exit 1 and the named forbidden axiom. Fixture compilation failure cannot
count as a successful rejection. These tests leave the live package untouched.

**R2 — open integration obligation: connect the two execution views.**
The Iris instance uses unlabeled sequential `Step`; `ProgramRun` models the
output-bearing, detector-checked pool driver. There is no general theorem
transferring an Iris WP into a full-program observation or result readout.
The exact graph of an executable driver does not itself establish that
transfer, Go fidelity, or all permitted nondeterministic behavior.

**R3 — open integration obligation: exercise real entry and composition.**
The seven-step recovery example starts inside a constructed continuation.
Its finite execution is real, but it does not establish entry, function
calls, registration of a defer, heap ownership, or result-cell readout.
The next experiment should cover those boundaries before a general
composition interface is promised. R2 and R3 were disclosed A1 limits;
the reviewer did not classify them as additional A1 blockers.

## What the result changes

A1 establishes that today's machine supports useful, checked consumer
experiments. A representation rewrite is not a prerequisite for the first
bridge or recovery rule. It also demonstrates why representation changes
cannot manufacture false context laws: recovery observes the continuation.

The organizing principle should therefore be **contracts demonstrated on
executions, followed by refactors that preserve those contracts**. Keep
GoCore, the native frontend, and differential testing. Keep the semantic
relations and coherence proofs in this repository. Keep the full Iris
resource logic downstream. The evidence does not justify restarting the
semantics or reviving an archived machine as the production foundation.

A1 narrows uncertainty about executable correspondence and a thin adapter.
It does not reduce the outstanding evidence required for evaluation order,
semantic identity, typed admission, refusal freedom, race treatment, or
the Go behavioral envelope. Kernel checking and oracle agreement remain
different evidence, both needed.

## Integration boundary

First retain the reviewed A1 package and evidence as a reproducible
experiment. Then promote only the semantics-owned portion in a small
follow-up worktree; avoid bundling this with B7 or a continuation rewrite.

| Material | Proposed destination | Acceptance condition |
|---|---|---|
| `Trace`, `PoolTrace`, `ProgramTrace` | Experimental modules under `GoLean/GoCore/`, with a small `GoLean/Interface.lean` facade | No Iris dependency; existing statements and counterexamples still elaborate; facade documents exact domains and omissions |
| Semantic counterexamples and driver examples | Core proof regressions, separated from Iris examples | Fixed-stream and recover refutations remain explicit; real print-before-panic result retains its output prefix |
| `Language` and Iris recovery rules | Separate spike package | Consume the facade where it has an API; document every remaining internal import/unfold as API debt |
| Axiom audit and source/dependency provenance | A separate consumer check, with semantics-only checks available to the normal build | Every promoted theorem is covered; imports do not silently remove audit coverage |
| Iris resources, separation rules, general adequacy and application proofs | Downstream reasoning project | Not prerequisites for shipping a semantics-only package; required before the corresponding customer verification claim |

The facade is experimental until its admitted domain and observation
contract are established. A new file named `Interface.lean` is not a
consumer release. Initially it may expose low-level configuration and trace
types; do not advertise representation independence while consumers still
unfold them. Migration should preserve the dependency audit's coverage when
module names change: the current `GateA1` origin filter is spike-specific.

Keep the consumer package outside the default Lake/`scripts/ci` dependency
graph, as the charter requires. Run its separate gate on any lane changing
the machine, driver, observations, resource boundary, or Lean/Iris pin.
Core promotion follows ordinary core checks; runtime changes additionally
need the relevant differential evidence. Reproduce dependency installation
from the portable manifest when network access permits; current evidence
uses exact local pins and does not certify a clean bootstrap.

## Proposed task order and completion criteria

| Task | Deliverable and exit test | Deliberate boundary |
|---|---|---|
| **A1 integration** | Land the reviewed experiment after approval; promote the semantics-owned bridges and expose an experimental facade in a separate small change; preserve the separate customer gate | Does not close all Gate A, I5, or G-PIN |
| **A2: minimal Iris logic and entry-to-readout example** | One small valid Go function with a helper call, a registered defer, a panic recovered by that defer, and a non-unit named result affected by recovery; compare Go and GoLean, prove its current-machine entry/composition/readout contract, and derive an Iris-facing result through the facade | An explicitly bounded theorem; no claim of general Iris adequacy from one example |
| **A3: admission boundary** | Separate structural program validity, entry/argument validity, supported-feature policy, and typed runtime states; implement a first checker with soundness for its exact predicate, positive witnesses, and malformed-input rejections | Full Go typing, global preservation, and refusal freedom are separate obligations, not implicit consequences of the checker |
| **B7 then C1** | Keep the planned context/store separation and emitted memory-access work; rebuild the consumer experiment across each change and retain existing differential/detector obligations | A1 does not certify race-detector soundness or Go scheduling adequacy |
| **Composition decision before C3** | Use A2's concrete continuations to specify a valid statement/call composition rule; prove its preservation and inversion conditions for the admitted frames, including recovery | A failed generic context law is rejected; a list representation is not its proof |
| **Gate C utility, then scoped Gate D offer** | A genuine workload's normal, error and boundary paths, independently checked observations, and a consumer proof through the public interface; all release assumptions and provenance explicit | Sequential and concurrent claims remain separate |

**Recommended first new semantic task: A2.** It directly addresses the
reviewer's two open integration obligations and can constrain the interface
before broad refactoring. Specify its statement before implementing it.
This means building a small piece of a logic over GoLean using Iris: a
state interpretation, result-cell ownership, and just the lifting and
composition rules needed by the example. It is a logic-construction task,
not merely a new test fixture. Instantiate the resources for the example
and connect its Iris postcondition to actual execution/readout; an abstract
WP rule with no demonstrated usable interpretation is insufficient.
Use real native lowering for the differential leg; keep a checked GoCore
artifact for the Lean proof. Record the lowering/source fingerprint and
explicitly retain the frontend-correctness assumption. Do not replace an
entry/call proof with another constructed mid-execution continuation.

A2 should start with a concrete sequential, no-spawn, no-I/O example and
normal return after recovery. Separately retain A1's terminal/output tests.
Track at least normal call return, deferred recovery changing the named
result, and a no-recovery panic control. Prove only the minimal composition
and result-cell operations needed by that example. A small classical
Reynolds/O'Hearn assertion layer may exercise the heap boundary, following
the sibling Cerberus project's approach, as an intermediate artifact. It
does not alone close A2's Iris integration objective. The final exercise
must include an Iris-facing result and its explicit execution/readout
connection. A general Iris heap logic stays downstream. Record exactly
whether each result is an Iris theorem, a classical semantic triple, or an
executable theorem; do not substitute one label for another.

The existing `execProg_single_eq_execStmt` is a starting point for the
transfer investigation, not the missing theorem: it begins at
`.exec prog env .stop`, restricts to `transferable` outcomes, shifts fuel by
`seqOpCount`, and does not establish output/readout adequacy for arbitrary
entry configurations. A2 must handle its actual `runProgramSetupM` result
and show why the single-thread detector/output policy is harmless for the
chosen execution. If a general transfer needs stronger hypotheses, keep
them explicit and prove a concrete witness rather than assume them silently.

A3 may start as an independent design task while A2 proceeds. Its first
implementation should be small enough to audit: table/reference bounds,
reserved entries, function entry and argument shape, plus an explicit
initial supported value fragment. `WireWellFormed` concerns the decoder
boundary; `ProgramWellFormed` concerns the resulting GoCore program; neither
means `ProgramWellTyped`. A support checker must account for initialization
and reachable calls and fail visibly outside its proved fragment. Do not
define acceptance as “execution succeeds” or refusal freedom as the absence
of a refusal constructor in syntax. Keep the eventual broad sequential
language goal separate from the first consumer proof's small domain.

## Changes proposed to the overall master plan

1. **Split Gate A into measurable rows.** A1 is a reviewed contract
   experiment; A2 owns composition and entry/readout utility; A3 owns
   admission statements/checks; the descriptor-algebra decision remains a
   separate pre-reflection task. General adequacy and preservation have
   their own exact statements and owners. Do not size all this as one I5
   finishing task.
2. **Make I5 incremental.** Publish experimental proved contracts early,
   exercise them during B7/C1, and harden the facade when the domain and
   consumer tests justify it. Retire the rejected fixed-choice/`Steps`
   and unconditional `fill` signatures in the operative plan.
3. **Reassess C3's justification and pin prerequisite.** Preserve the
   existing [USER] ruling until revised. Propose re-approval on concrete
   benefits such as structural cases and maintainable composition proofs;
   remove the claim that flattening continuations delivers generic
   `EctxLanguage` laws. A2 should supply evidence for that decision.
4. **Keep fidelity repairs moving.** BUG-098/103/104, BUG-099 ownership,
   the evaluation-order design/BUG-101, semantic identity, decoder metadata,
   and certificate provenance retain their places. A consumer theorem
   about the current interpreter is not evidence that these bugs vanished.
   Certificates tied to semantic-source changes should precede a broad
   refactor campaign that would otherwise leave stale certification green.
5. **Retain the proposed reflection hold and sequential-first milestone.**
   A1 supplies no reason to accelerate `reflectlite` or a concurrent pin.
   These remain proposals where the master plan records pending [USER]
   decisions. Concurrent reference granularity, race treatment and reduction
   remain Gate D obligations regardless of A1's exact pool bridge.
6. **Replace obsolete operative text when this sequence is adopted.**
   Update §3.A and §7.4 plus the reasoning-surface signature list together;
   use one short current contract and an obligation table with theorem,
   prerequisites, owner, evidence and affected claim. Preserve historical
   decisions as history. Do not append another contradictory roadmap or
   reuse the old session estimates as assurance estimates.

The next release discussion should distinguish: a research snapshot; a
named sequential profile with justified behavior and no known wrong answers;
and a concurrent consumer offer with explicit concurrency assumptions.
Neither this review nor A1 authorizes the latter two claims. The immediate
decision is whether to adopt this task sequence; merge and push remain
separate approvals under the existing charter.
