# Batched-window charter: project and execution-readiness review

2026-09-23. [USER] Requested review of the window charter for the overall GoLean
project. [AGENT] Reviewed `docs/roadmap-customer-alignment-0922` at `e8758442`
against main `9269912e`, in the separate `review/batched-window-charter-0923`
worktree. Scope: the proposed charter, user-ruling provenance, the logic team's
response, standing project/architecture rules, E6's recorded residue, and the
current interpreter definitions needed to check the proposed contracts.

**Verdict: support the direction; revise three points before treating this as
an execution-ready charter.** F1 leaves the first mandatory milestone without
a complete work breakdown. F2 needs an exact fuel predicate. F3 prescribes an
inventory procedure that cannot produce its promised evidence. These are
planning findings, not new runtime regressions. No implementation is dispatched
or merge/push authorized by this review.

## F1 — P1: E6's retirement exit is broader than its listed work

Location: [charter row 1](2026-09-23_batched-window-charter.md), line 31;
dependent sequencing at lines 117–124.

E6 is the mandatory first item, estimated at 2–3 sessions, with retirement only
at whole-corpus plus twin census zero. Its concrete work list names the trigger
refinement, non-main units and two decoder checks. The referenced
[E5 handoff](2026-09-22_unseq-stage-e5-handoff.md), lines 82–103, also identifies
five emitters requiring other grammar work: three element-address cases and
two `recover()` cases in lifted bodies. Nine further singleton emitters need
per-function dispositions. They are separate rows from the 23 corpus/non-main
and 21 panic-vs-panic rows; the handoff calls for later shape families.

The retained emission record names `addrIndexLeftLenHoist`,
`addrAssertLeftCall`, `arrayBaseTargetVsLen`, `recoverAssertVsLen$lit0`, and
`recoverAssertVsCallW$lit2`. The current frontend still explicitly rejects
element-address operands in `unseqAddrOperandRefusal`, at
`tools/nativefrontend/unseq.go:524`. Changing the package boundary or trigger
does not by itself implement that operand. The decoder consistency fixes and
status-set apparatus likewise do not close this grammar gap.

Consequently the stated work does not establish the prerequisite for retiring
the legacy forms. Referencing a handoff that describes these as deferred is not
a sufficiently clear commission to implement them inside E6. This matters to
the entire window: either it stalls before the label work, or an implementer
silently grows the scope or weakens the zero criterion.

**Requested revision:** split E6 into named prerequisite slices, covering every
residual emitter class, followed by the retirement slice. Give the five shape
cases and nine singleton cases explicit dispositions and update the estimate
after that accounting. Preserve the ruled whole-corpus/twin exit. Require a
fresh emission census plus behavioral preservation evidence; zero achieved by
dropping/refusing previously covered programs or silently choosing one allowed
evaluation order is not success. No new grammar widening is authorized merely
by this review.

## F2 — P2: distinguish zero-cost classification from abort completion

Location: [charter execution statement](2026-09-23_batched-window-charter.md),
lines 44–60, especially `Prefix fuel ... ∧ ¬ classified c'`.

The prose correctly says normal/blocked classification precedes the fuel match
and abort costs one additional step. But `classified` is not defined, while
the preceding `Finish` sketch includes aborted configurations. If it means
“has a Finish,” the displayed fuel-out equivalence is false: a renderable abort
has a Finish, yet the interpreter returns fuel-out when the budget is zero.
This is a precision gap in the sketch, not a disagreement with its stated
intention or a defect in the current interpreter.

The [Lean witness](evidence/2026-09-23_batched-window-review/FuelBoundary.lean)
checks that the same configuration has `abort? = some ...`, returns `fuelOut`
at fuel zero, and returns the panic terminal at fuel one. It also proves normal
completion succeeds at zero. These are the current `execStmtLoop` rules at
`GoLean/GoCore/StepFn.lean:1012`.

**Requested revision:** define a predicate for the driver's *zero-cost*
classification (normal and the four blocked forms), and use its negation in
the fuel-out theorem. Track the finishing cost explicitly: zero for those
classifications; one for the abort call, including renderer refusal. A completed
prefix bridge then bounds prefix length plus finishing cost, while fuel-out
describes the actual fuel-length prefix without a zero-cost finish. Include
boundary controls for abort/rendering refusal at zero versus one and normal/
blocked completion at zero. Keep the existing fuel convention.

## F3 — P2: use retained frontend output for the fixture inventory

Location: [charter row 0](2026-09-23_batched-window-charter.md), line 30:
`scripts/lower-diagnose; grep "stmt":"unseq"`.

`scripts/lower-diagnose` is explicitly a diagnostic, not a retained lowering.
At lines 114–122 it emits a temporary probe wire, reads it for quarantined
declarations, then deletes it. Its reports therefore cannot establish absence
of `unseq` nodes. Grepping a report and finding none could incorrectly confirm
the very “none enters a graph” hypothesis the charter rightly refuses to
assume. The direct `--unseq-census` mode is useful additional evidence but is
documented as a main-unit census, not a replacement for inspecting the complete
emitted program.

**Requested revision:** run the pinned production frontend with an explicit
owned scratch `--out` for each of the fourteen fixtures and generated positive
variants, record source/frontend pins and export status, and recursively count
actual JSON statement nodes. Distinguish failed export from successful output
with zero graphs. Use `lower-diagnose` to explain failures, not to certify graph
absence. Keep counts/provenance in the report; bulky wires can remain scratch.

## Project-goal assessment

The revised charter otherwise makes the right corrections. Prefixes with
arbitrary endpoints preserve observations before later failure or divergence;
terminal store/tape and the repanic draw are retained; labelled replay needs
coverage, not merely a count of tape elements. Refusal remains visible in an
unconditional bridge before any fragment-specific exclusion theorem. These
are GoLean semantics/coherence work and belong here under the standing charter.

The shared `{trace, picks, out}` shape and preservation of silent projections
are appropriate. The labels are semantic evidence; the downstream proof still
derives Ready or other library observations from real execution boundaries.
There is no need for Raft events, Iris rules, owned-heap predicates or a new
reasoning facade in GoCore. The staged corpus exercises general Go features;
a customer can guide priorities without determining what the language means.

The explicit conditions on methods, lexical versus dynamic identity, captures,
and initialization order protect fidelity during P/B6/C4. C4's injection with
private extra cells is a better intermediate-state claim than a whole-heap
bijection. The escape audit and G-C4 stop remain essential: a scoped theorem
does not authorize changing address-sensitive observations already supported
by GoLean. An observed mismatch must be resolved or separately ruled, not
declared outside the new theorem after the fact.

The two advertised boundary tensions are manageable. A small independent
semantic-equation client, using only GoCore and exercising symbolic state and
continuations, is a regression test; it need not revive typed profiles or an
Iris `Language` adapter. Keep it in the test/contract graph with exhaustive
enrollment and no runtime dependency on it. The C4 scope correction refines a
proof statement while retaining the original behavioral gate; it must not
weaken the intended behavior preservation.

One window/offer, per-item gates/audits, serial ownership of core edits and a
live migration record are sensible. Keep the statement and semantic-equation
checks separate: names/types alone cannot catch behavior changing underneath
the same signature. The toy client must use the supported equations rather
than simply restating their types or unfolding the implementation again.

The full end-to-end obligation remains larger than this window. The proposed
program bridge assumes successful setup, retains the init-print refusal, and
defers full pool/registry coverage. State those limits in the final offer and
any eventual CLAUDE.md edit; preserve existing unconditional program error
accounting and coherence while reshaping labels. Do not mark the entire owed
simulation discharged by the restricted sequential result. Deferring NaN and
the concurrency reduction is an explicit scope decision; their fidelity debts
remain. Withdrawing unqualified `unseq` confluence and keeping the current
NPDRF draft unusable are correct.

## Validation and disposition

Read the candidate's five-document diff, standing charter/architecture, actual
fuel/abort/choice/program definitions, E6 source and recorded emission census,
and diagnostic tool implementation. Candidate production code is identical to
main `9269912e`. The fuel witness was freshly checked with capped Lean 4.32.2,
using main's existing build artifacts; no cold rebuild, full `scripts/ci`, new
corpus run or fresh fourteen-fixture lowering is claimed. The witness output
is `fuelOut` followed by the panic terminal. The review does not port the logic
repo or rerun its acceptance suite.

[AGENT] Recommendation: retain the architecture/order as the intended program,
correct F1–F3, then approve/dispatch against the revised work breakdown and exact
contracts. The records/inventory work is useful immediately once commissioned;
this review itself grants no new authorization. Evidence, source pins and the
small witness are retained on this review branch; the author's branch and
primary main are unchanged.
