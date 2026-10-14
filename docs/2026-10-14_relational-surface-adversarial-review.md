# Adversarial review of the first relational interface

Reviewed commit: `d30107b2c51416d1f74db58b7883b21bbc033d26`.
Parent: `b49739eae94a54aed1ac4a686f47831e6c6c19e4`.

Provenance: [AGENT] 2026-10-14, independent subagent
`adversarial_relational_review`, commissioned by the [USER]. The reviewer
received the project goals, request and source locations, and areas of
interest, without the implementation conversation or a prescribed verdict.
The report below preserves its returned findings and validation account.
Line references refer to the reviewed commit. Saving this report makes no
implementation change and does not authorize a merge or push.

## Verdict

**Ready for a deliberately small downstream demo; not ready to replace the
existing logic adapter or adequacy roots.** I found no incorrect exported
theorem or executable semantic regression in this commit. The limitations
are mostly accurately disclosed. The demo should test whether these initial
abstractions help a representative proof, and report missing laws rather
than reconstruct the removed executable API.

## Findings ordered by impact

### 1 General refusal sensitive safety and complete program execution

**The new interface still cannot express general refusal-sensitive safety
or complete program execution. This blocks general migration, not an
exploratory demo.**

`GoLean/GoCore/RelationalOutcome.lean:24–48` represents normal completion,
deadlock, panic and rendering refusal, but excludes fatal failures and
ordinary operation refusals. `GoLean/GoCore/RelationalFault.lean:16–29` adds
six selected fault sites; it is not a complementary classification of all
unsuccessful transitions. `GoLean/GoCore/RelationalProgram.lean:28–37`
represents successful setup, initialization, body execution and successful
readback only.

Consequently, a universal property over `ProgramNormal` can transfer to
successful executable results, but does not establish that other executions
avoid refusal. `PickFreeProgress`
(`GoLean/GoCore/RelationalFault.lean:62–75`) is a sound useful replacement on
its stated deterministic domain; it requires every reachable nonterminal
point to have a pick-free step and excludes admitted panic as well as
faults. It must be established for the demo, not silently substituted for
the existing logic's domain.

The docs acknowledge this correctly. P1/P2/P6/P11 remain materially
unfinished, including the request's clear-property ambition of actual
outcome classification. Prioritize these before claiming initialized-program
adequacy or migrating an existing all-behaviours guarantee.

### 2 Observation coverage and compatibility

**Observation soundness is present, but observation coverage and compatibility
are not. This blocks replacing the audited observer.**

`GoLean/GoCore/RelationalObservation.lean:24–46` lists seven concrete entry
sites; `Enters.transition` and `Enters.all_successors` at lines 77 and 87
prove that a witnessed entry is real and uniquely determines successful
successors. They do not prove every actual body entry is represented.

`ReturnsDiscarded` at lines 110–119 handles only frames with no targets or
result locations. Ordinary result-bearing caller returns and panic-printing
returns are absent. The downstream `Logic/Observation.lean` observes those
paths, and `Logic/Observer.lean` allows observers to inspect the pre-store.
The new events correctly preserve pre-store and supplied arguments, and
correctly distinguish discarded-result return events from final readback.

The explicit warning against retiring the downstream census is necessary
and correct. A later compatibility projection needs both coverage directions,
ordered event preservation, and the existing return payload convention.

### 3 Usefulness for realistic rule derivation

**The useful abstraction is presently concentrated in a very small control
fragment; realistic rule derivation remains untested.**

`GoLean/GoCore/RelationalControl.lean:65–136` packages literals, Boolean
conditionals, sequencing and block allocation. These are usable symbolic
laws rather than a global executable equation catalogue. However, successful
local reads, assignment, dereference, arithmetic, ordinary return statements,
panic/recover and `unseq` do not yet have equivalent construct contracts.

The memory laws are operation-level facts; they do not connect a source
assignment or dereference to its full semantic transition. `LocalEntry`
(`GoLean/GoCore/RelationalEntry.lean:24–41`) still exposes
binding/allocation/pinning equations, while `EntrySite` exposes the actual
continuation constructors and caller-target plans. `Continuation`
(`GoLean/GoCore/RelationalControl.lean:23–25`) is a wrapper around `Cont`,
not a representation-independent control interface.

The current contract test (`Tests/RelationalContracts.lean:12–25`) proves
entry into the selected branch of a literal conditional; it does not execute
a branch or complete a function. That is appropriate as an upstream semantic
check, but offers little evidence yet for the velocity goal. For example,
the existing downstream F1 `Set` proof needs ordinary variable/load/store
rules beyond this surface. A small representative port should expose
precisely those obligations. Requiring the entire library beforehand would
contradict the agreed iteration workflow.

### 4 Locality and sequentialization

**The locality/sequentialization contribution is sound but elementary; it
cannot yet support framing or `unseq` replacement.**

`GoLean/GoCore/RelationalMemory.lean` proves whole-root support for successful
primitive writes, fresh allocation above the old heap bound, and commutation
of writes to distinct existing roots with fixed normalized values. These
statements correctly avoid confusing race instrumentation with operational
footprint.

They do not establish a whole-step support contract, control-reference
validity under context extension, allocation renaming, or schedule safety.
`root_writes_commute` therefore cannot justify replacing a WP proof by a
sequentialized proof. This is a legitimate iteration obligation, and the
documentation states the restriction accurately.

## Positive conclusions from the proofs and deletions

- `Run` is genuinely a labelled closure of `Step`. Its realization theorem
  stitches one tape while preserving exact labels and permitting any residual
  tape.
- Recorded-choice determinism does not incorrectly claim that all choice
  alternatives succeed. Pick-free uniqueness and exclusion of executable
  stopping errors are separately proved.
- Fuel accounting is faithful: normal/blocked finishes cost zero, panic
  rendering costs one, and exhaustion describes an actual prefix ending
  outside zero-cost completion. Initialization and subject execution retain
  separate fuel bounds.
- Initialization's print guard precedes zero-fuel failure, and the successful
  init relation checks the guard along the actual path.
- Local execution starts from an arbitrary supplied store; normally finished
  bodies can still have failing readback.
- No interpreter, store, frontend, choice implementation or baseline
  definition changed in the reviewed diff. The large deletions remove the
  requested equation interface, its pins/client/checker, and associated audit
  references. Three required setup helper proofs were retained privately in
  `SetupSound`; useful machine/slot/return/pool facts remain. The resulting
  break for the old equation consumer is explicitly requested and does not
  invalidate its old pinned development.

## Validation performed by the reviewer

- Verified reviewed HEAD is
  `d30107b2c51416d1f74db58b7883b21bbc033d26`; worktree was clean before and
  after review.
- Verified the downstream quarry checkout is
  `f0afcbf7e7a0ad7c19087cc3f73429c57ca94c51`.
- Read the authoritative request, companion asks/identity note and
  execution-log rulings, new relational modules, relevant downstream
  adapter/observation/proof examples, and implementation/deletion diffs.
- Ran `LEAN_NUM_THREADS=4 capped lake build GoLean.Relational Tests.RelationalContracts Tests.GoCoreAudit`:
  exit 0, 65 jobs. This reused existing build artifacts; printed headline
  axiom results contained only `propext`, `Classical.choice`, and `Quot.sound`.
- Ran `LEAN_NUM_THREADS=4 capped lake env leanchecker --verbose GoLean`:
  exit 0, replayed 79 GoLean modules, including the new relational
  implementation and dependencies.
- An earlier narrower `leanchecker --verbose GoLean.Relational` invocation
  also passed, but replayed only the facade; I did not treat it as sufficient
  and ran the full prefix above.
- Searched the added relational sources for `sorry`, project axioms,
  `native_decide`, `implemented_by`, `@[extern]`, `unsafe`, and
  `debug.skipKernelTC`: no matches.
- I did **not** independently rerun the full differential CI. Its recorded
  run remains the implementer's evidence, not mine.

No files were edited, no permanent review artifact was created, and no merge
or push was performed during the review. This file is the subsequent
user-requested preservation of that report. All four findings remain open
follow-up work; none is represented as fixed by saving the report.
