# Second review: make the evaluation-order plan executable

[AGENT] Review, 2026-09-16, requested directly by [USER], with the objective of
improving the implementing agent's probability of success. Target:
`9a8ed328711969455bfe1d823c65e858cb919e3a`, specifically
`docs/2026-09-16_evaluation-order-model-v2.md` and its reference spike.
Code references are at its base, `433e7490`. Review branch:
`review/eval-order-model-v2-0916`, off that main tip.

## Recommendation

**Keep the graph architecture; revise the first implementation slice.** V2
addresses the main structural objections in the [first review](2026-09-15_evaluation-order-model-review.md):
values are produced once, independent occurrences can run at intermediate
positions, and compound assignments share a target. The reference model is
useful, its tracked output reproduces, and the cost claims are now scoped
honestly. The user-approved `unseq` mechanism does not need another mechanism
decision.

The next best step is a small, complete implementation of the scheduler and its
adapters, followed by controlled frontend migration. S1 currently combines new
syntax, runtime storage, control flow, proofs, lowering, enumeration, removal
of the old mechanism, and corpus-wide migration. That makes a late discovery
in any one interface expensive to repair.

Two semantic corrections are needed first: the read-order reduction is false
as stated, and guards need completion/skip semantics. Then settle the occurrence
payload and storage contracts before changing the emitter. Do not make the
first successful build depend on full-corpus re-enumeration.

All recommendations below are [AGENT] proposals. Existing named user gates
remain pending; this review neither rules them nor authorizes implementation.
“Before” in the execution plan describes engineering dependencies, not a new
set of user approval gates.

## 1. Corrections that materially affect execution

### R1 — High: remove the proposed read-order reduction

**Target:** §3, lines 176–180; S2's reduction lemma.

Two reads commute when executed consecutively against the same state. Adding
an ordering edge between them can nevertheless remove placements on opposite
sides of an intervening event:

```go
x, y := 0, 0
mut := func() int { x = 1; y = 2; return 0 }
v := x + y + mut()
```

The full graph permits `{0, 1, 2, 3}`. Adding `read(x) → read(y)` removes
`1`, whose order is `read(y); mut(); read(x)`. Neither read can fail. This
refutes the proposed condition even in the reference fragment. The absence
of a newly added edge *to the event* does not preserve interleavings with it.

**Action:** delete the unconditional reduction recommendation. Start with
unreduced graphs. Introduce an optimization only with a preservation argument
that accounts for all intervening writes, effects and failures. For an early
implementation, fold constants and operations already forced by dependencies;
do not impose an order between distinct mutable reads to control cost.

The obligation must precede **using** the optimization, rather than merely
retiring a latitude pin that relies on it. Keep this example as an exact-set
regression. The [review experiment](evidence/2026-09-16_eval-order-v2-review/README.md)
reproduces the lost member using the reviewed enumerator unchanged.

### R2 — High: distinguish deciding a guard, completing its logical operation, and skipping a region

**Target:** §1 E1/G and executions; §3 readiness, guard completion and list order.

There are two related gaps.

**A skipped event cannot remain a prerequisite.** In
`sink(z || h(), k())`, E1 places the conditional `h` before `k` when `h`
runs. With `z == true`, the region is absent, so `h` never assigns its binder.
Encoding the edge as an ordinary prerequisite makes the proposed ready rule
wait forever. The reviewed enumerator reports
`no ready occurrence among ['K'] (cycle)` on this encoding. The graph is not
cyclic; the predecessor was skipped. X2 does not test this situation because
its later call consumes the guard's joined output instead of depending on a
skipped sibling event.

**The guard decision is not the completed logical operation.** Consider:

```go
b, left := false, false
change := func() int { b = true; return 0 }
sink(left || b, change())
```

The ordered binary logical operation must finish before the later `change`
call. Ordering only the decision guard before that call lets the RHS read of
`b` run after the mutation. The graph then gives `{false, true}`, instead of
the singleton `{false}`. The pinned Go probe returns `false` with both tested
compiler flag settings; the ordering requirement comes from
spec#Order_of_evaluation and spec#Logical_operators, not from that single draw.

**Action:** specify a guard-entry node and a logical-result/completion node
(or an equivalent structured region protocol). A disabled branch produces its
short-circuit result and completes the region; an enabled branch completes
only after its required result is available. Anchor the ordered logical
operation at completion. Represent order prerequisites separately from value
dependencies: a skipped event can discharge the former, but cannot invent a
value for the latter. Reject a use of a value confined to a skipped branch
unless it passes through a valid join.

Specify three scheduler cases explicitly:

- no pending active work: complete the region/sweep;
- nonempty ready set: select an occurrence;
- pending active work with no ready occurrence: named malformed-graph refusal.

Also give all nodes a stable canonical rank, including region nodes. Appending
newly enabled nodes to the end of `pending` must not silently redefine their
canonical priority. Test nested guards, both short-circuit outcomes, a later
call, an earlier call, and an event consuming the joined result. Require exact
sets, expected traces and absence of stuck outcomes.

### R3 — High: replace arbitrary bodies with a precise occurrence contract

**Target:** §1 READ/OP/EVENT; §3 wire and decoder, lines 109–128.

A graph does not expose evaluation order if an occurrence body can hide a
second mutable read, failing operation or call argument evaluation. Conversely,
a checker cannot validate a body's effects solely from `kind:"op"` and a type
annotation. The current `decodeExpr` returns `Expr`, not a checked expression
paired with an inferred type (`GoLean/NativeToIR.lean:404`). “Its body's
decoded type” and “then type-checks” are substantial new work, not existing
decoder helpers that the implementer can call.

**Action:** define a small internal normal form before adding the wire schema.
Its operands should be constants, explicitly admitted stable reads, or typed
slot references. Specify the permitted head and effects of each occurrence:

| Kind | Contract needed before coding its adapter |
|---|---|
| Read | Exact source-memory read, using already selected operands; whether it can panic |
| Pure operation | Computation on supplied values; no hidden heap read/allocation/recover |
| Allocation/conversion | Separate payload selection from allocation; declare memory reads and allocation effects |
| Invocation/receive | Already evaluated callee/channel/arguments; one invocation/communication; zero, one or multiple result slots |
| Target plan | Frozen operands plus deferred checks; a separate target result sort |
| Guard/join | Branch activation, conditional dependencies, exactly one logical result |
| Completion | Stores/control transfer using results; no rerun of source expressions |

Examples requiring classification: `string(b)` and slice-to-array conversion
read backing storage; `[]byte(s)` allocates; interface equality may fail;
`recover()` changes the continuation. None should be treated as pure just
because it is spelled as an expression. An allocation being “event-like” must
not automatically give it E1 call-order edges.

Zero-result calls and `print` still complete order prerequisites. A
multi-result call or comma-ok receive is one occurrence, with multiple outputs;
splitting it into multiple invocations would duplicate effects. Either support
these in the first migrated fragment or refuse them explicitly at that boundary
while their existing lowering remains available outside it.

Test the decoder with unknown references, cycles, duplicate results, type/sort
mismatches, hidden reads in pure nodes, and invalid branch joins. Do not require
the first slice to invent a full GoCore type checker: bound its admitted grammar
and make every additional head an explicit adapter with a validation rule.

### R4 — High: settle result storage, source scope and target freezing before integrating calls

**Target:** §3 ENTER, occurrence completion, EXIT and lvalue identity.

The proposed representation is not directly available in the current core:

- `LocalEnv` maps names to `Loc`; `HeapCell.value` holds a declared type and an
  actual `GoValue`. Neither represents an unassigned slot
  (`State.lean:9`, `:28`, `:127`).
- `TargetRef` is a distinct machine type, not a `GoValue`
  (`Machine.lean:1554`). It cannot be stored as an ordinary local value without
  another representation decision.
- ENTER predeclares `$u2`, but the sample event also has `define:true`.
  The existing decoder inserts `.initialization`, which allocates a new binding
  in a statement sequence (`NativeToIR.lean:1522` onward;
  `StepFn.lean:200`). Reusing that body unchanged would not mean “fill the
  slot ENTER allocated.”
- Source declarations in `then` need to remain visible after the sweep. If
  `x := a + f()` declares `x` in the disposable temporary scope, restoring the
  outer environment loses the declaration. Initializations extend their
  immediate sequence's environment in the current machine.

**Action:** write down the runtime record now: static graph, active/done/skipped
status, value results, target results, caller environment, canonical rank and
completion. Keep “event completed” separate from “produced a value.” A practical
option to prototype is preallocated typed value cells with a separate
assignment bitmap, plus a continuation-owned target table. A control-only slot
table is also possible, but its call-result adapter must be demonstrated. Do
not extend the source-language value/heap universe merely to hide scheduler
bookkeeping in it.

Occurrence event bodies must write predeclared result destinations, not
redeclare them. Allocate source declarations in their source scope; temporary
scope disposal must discard only scheduler temporaries. Include `x := ...;
use(x)`, shadowing, escaped closures, loops and recursion in the adapter tests.

**Target identity needs a stronger invariant than sharing a `TargetRef` value.**
`resolveChain` may read state while replaying a target plan; in particular,
`indexTargetLoc` accepts an address of a cell containing a slice and loads its
current header (`Machine.lean:226`, `:1613`). The new adapter must freeze the
slice/map/pointer operands whose evaluation it claims to have completed. A
shared plan that rereads a rebound slice variable at the store is not a shared
element identity. Test slice/map replacement and pointer redirection, with the
old storage retained so both writes can be observed. Preserve the existing
phase-2 placement of plain-assignment checks while sharing compound targets.

This is a bounded representation/adaptation task. Prove its invariants in a
small hand-built node before asking the emitter to produce thousands of them.

### R5 — High execution risk: budget for a working enumeration path, not just flags

**Target:** §3 ENTER's diamond claim and file list; §6 measurements; §7 S1.

Predeclaring slots consistently may help equal states merge, but it does not
make the certified deduplication engine understand the new scheduling choice.
Currently `EnumDedupCheck.innerVecs` rejects `unseqPanic`, while
`MultiStreams.poolThreadOblivious` marks it non-oblivious; replacing those
exclusion flags with `unseqNext` would still reject every new wide pick. An
implementation that intends deduplication needs the branch-vector construction
and its checker/soundness support, not only the new constructor and flag
(`EnumDedupCheck.lean:101–129`, `EnumDedupSound.lean:320`,
`EnumDedup.lean:138`).

The default enumerator can be correct yet impractical. Even two successful,
outcome-equivalent orders repeated across many sweeps create a product of path
choices. Unlike the current panic-only probes, new picks can occur on every
ordinary successful iteration. R1's false reduction cannot be the escape hatch.

**Action:** make one measured enumeration route part of the first vertical
slice. Either certify `unseqNext` branches in deduplication, or explicitly use
the default enumerator on a bounded pilot and demonstrate its budget before
expanding emission. Include repeated sweeps, a wide argument list, and a loop;
measure unique states as well as paths, runtime, RSS and consumed picks. Treat
the full twin as a later acceptance workload, not the first feedback loop.

Use one `ready` calculation for execution, `Step` premises and
`seqConsumption`. Prove the accountant exposes exactly the scheduler's bound.
Validate the actual pool/CLI path used by the corpus: “sequential model” does
not exempt new continuations from the pool driver or output/race-access
plumbing. A new checked-read adapter must preserve the accesses currently
reported by `Race.strictOpAccesses` (`Race.lean:506`, `:1545`). No new concurrency
claim is needed to avoid regressing existing consumers.

When auditing lane moves, keep these cases distinct:

- differing observations across tapes require a suitable nondeterministic lane;
- identical observations but insufficient stream coverage may use the existing
  strict `depth=N` policy or certified confluence;
- a budget-exhausted enumeration is a refusal, not evidence that the set is
  singleton or that an unexpected set should be re-pinned.

`depth=N` does not make a genuinely varying strict row pass. Also remove §3's
“none on status” assurance: BUG-101 already has both normal and panic members.
Compare full observations and identify intended changes explicitly.

### R6 — Medium, pending design choice: isolate header evaluation from the element access

**Target:** §1 READ; §5 N1.

N1 currently combines a slice variable's header read with its later checked
element access. This loses an elementary placement:

```go
a := []int{10}
f := func() int { a = []int{20}; return 0 }
v := a[f()]
```

If the header is read independently, the graph gives `{10, 20}`. Requiring the
whole header/check/load occurrence to follow `f` gives only `{20}`. Both
graphs were enumerated; gc gave `20`. The other member is derived from the
operand-order interpretation, not claimed as a measured gc result.

**Recommendation for N1:** have base/header and index producers, then one
checked access on those values. This matches the existing
`strictPlan (.indexGet b i)` / `applyStrictOp .indexGet [b,i]` split
(`Machine.lean:183`, `:439`). It does not require splitting the bounds check
from the final element load or settling finer concurrent memory granularity.

If the narrower fused read is deliberately selected, retain that narrowing
in the model, reference generator and inventory. Do not simultaneously describe
the P(ii) rollout as a complete value envelope on these rows. The current core
implementation is not evidence that reading a variable's header and accessing
an element are already one indivisible evaluation.

## 2. Replace “S1 exactly” with verifiable stages

The following sequence is intended to reduce rework. Keep one writer for the
core while changing its types and proofs. Preserve the charter's per-commit
runtime gate and interpreter/relation merge invariant at every landing.

| Stage | Deliverable | Exit evidence |
|---|---|---|
| A. Repair the executable design | R1/R2 regressions; precise occurrence grammar, result sorts, region joins and runtime record; resolve the existing user gates needed by the selected fragment | Reference sets and negative cases pass; one source example has a complete graph, wire sketch, canonical order and result mapping |
| B. Implement a small scheduler | New syntax, continuation state, ready/pick/completion, slot lifetime; hand-built graphs; total rules and `stepFn` cases together | Successful and failing runs match the reference; arbitrary legal schedules have replay tapes; malformed/no-ready graphs refuse; singleton picks do not consume |
| C. Connect one native fragment | Decoder validation and source-to-graph lowering for a stated grammar; normal/call/return/target adapters | Source → actual frontend bytes → strict decoder → executable machine → exact observed sets; decoder mutations reject; original source declarations survive completion |
| D. Make exploration economical | Correct branch accounting and the chosen enumeration engine; scope/deallocation representation measured on repeated sweeps | A small workload ladder closes within recorded budgets; exact-set and accountant checks still pass; no outcome-losing ordering optimization |
| E. Migrate the families | Expand by operand and statement family; BUG-101/104, assignment targets, guards, receivers and allocations; remove legacy code after its callers are migrated | Per-family full gate/differential evidence, named set changes, updated pins/ledgers; full corpus and required certified workloads pass at the final coverage boundary |

Stages B–D should overlap only in small implementation increments, not by
having multiple writers alter shared core signatures. Cost feedback starts in
B; D is the condition for broad rollout. The known positional proof-case
fragility argues for small, buildable changes. Do not bundle a general proof
refactor into the semantics migration just to make those edits prettier.

Temporary coexistence with the current probe implementation is compatible
with retiring it as the chosen design. Define a syntax-based migration boundary
for an **entire sweep**: old lowering or graph lowering, never a mixture that
executes an operand twice or drops an edge. No fixture-name dispatch. Remove
`unseqProbe`/`probeK`/`unseqPanic` only after all admitted callers, tests and
consumers have moved. This avoids coupling the first scheduler patch to every
structural allocation and existing wire pin.

### Correct the slice promises

- **P(i)-only S1 cannot pass W1 and W6 as graph-envelope regressions.** Their
  distinguishing reads are P(ii). Choose a minimal P(ii) pilot once the width
  gate is ruled, or leave those as reference-only tests until S2. Do not label
  a narrower machine's missing members a failure of the scheduler.
- **BUG-101 needs more than the integer spike.** Include assertion success
  followed by mutation to failure, and the slice-value witness. BUG-104 needs
  stable shared target operands through calls and observable stores. Add these
  to the native pilot before predicting their baseline flips.
- **Generate tests alongside each adapter.** Waiting until S4 for all generated
  interactions allows emitter assumptions to become entrenched. Begin with a
  small exhaustive fragment; expand pairwise coverage after its source and
  reference representations are established.
- **Move the mechanism theorem forward.** Establish enough scheduler
  soundness/completeness during B to constrain the representation. Postponing
  it until after the emitter and all families migrate risks proving the wrong
  execution contract.
- **Keep estimates conditional.** Replace fixed session counts and the
  unmeasured “months” alternative with dependencies and results from B–D.
  S1 before B7 remains a reasonable proposal once these stages are bounded,
  not an execution guarantee. S2/S3 also touch core adapters/checkers; scheduling
  them “beside P” needs explicit file ownership and compatible interfaces.

## 3. Minimum acceptance matrix

This is a bounded starting suite, not a demand to solve every Go feature before
the pilot. A row outside the selected fragment must be labeled deferred or
explicitly refused at that boundary, never counted as validated.

| Family | Required discriminators |
|---|---|
| Read placement | W1/W2/W6; both lexical sides; header before an index-producing call; R1's lost-member witness |
| Logical regions | Skip/right-run; nested guards; later sibling call; pure RHS read before a later call; no use of disabled data |
| Target identity | W3 plus slice/map replacement, pointer redirection and cell mutation with stable address; no hybrid read/store |
| Phase checks | Phase-1 operand panic stores nothing; first phase-2 store persists when the second store panics; compound read failure versus RHS event |
| Dynamic state | W5, recursion, repeated nested calls, source short declarations and escaped closures; no stale result slots |
| Invocation results | Zero-result call, one result, two results, comma-ok receive; effect occurs once; supplied arguments are not reread |
| Failure/control | Callee recovers and returns; callee panic escapes and cancels pending work; deferred recover inside a migrated sweep; blocked receive stays distinct from panic |
| Infrastructure | New choice plus an existing choice site; exact accounting; canonical replay; unsupported/malformed graphs and budgets refuse by name |

Record for each accepted fixture: source shape, graph, expected observation set,
forbidden members, oracle draws, actual lowered-machine set, canonical draw and
budget. Keep the source graph independent of the emitter's generated edges.
Mutate at least one data, lexical, guard and phase edge and show that the
validation detects the resulting error. A successful handwritten graph alone
does not validate lowering.

## 4. Tighten the claims and proof obligations

**Mechanism theorem.** The phrase “every trajectory is a linear extension” must
account for early panic and skipped regions. State soundness for the executed
occurrence trace: a successful trace completes the active graph; an escaping
panic is a legal prefix ending at that failure, with no later effect. State
completeness for legal finite successful/failing executions, including the
occurrences' own nondeterministic behavior and any internal choice consumption.
There can be several tapes/step traces for one occurrence order; “one pick
sequence each” is not generally true once calls or allocations consume choices.

Include invariant preservation, no double execution, dominance of consumed
values, region progress, target consistency and freshness. These are practical
proof interfaces for the implementation, not merely a final metatheorem.

**Translation certificate.** §7(b) proves properties of the supplied wire
graph. It cannot detect a frontend that omits a required edge or adds a
forbidden one. Call it the *wire scheduler theorem*. The source-to-wire
certificate obligation remains separate: specify a small source fragment and
either a checked source/graph correspondence certificate or a preservation
theorem for that fragment's lowering. Finite generated-set comparisons remain
tests. If the plan substitutes those tests for the accepted translation
certificate, propose that as a plan change explicitly; do not relabel the
scheduler theorem to imply that the boundary has been covered.

**Evidence labels.** §3 says mechanism equality is “tested by the §2 equality.”
There is no lowered machine in this spike. Distinguish “reference graph checks
pass” from “machine equals reference,” which is still an exit criterion.
Similarly, the X3 empty-channel branch raises the spike's `Panic` exception,
although blocking is declared outside the fragment. Make that branch a distinct
refusal/blocked outcome before adding empty-channel tests; the current buffered
witness does not exercise it.

**Canonical compatibility.** Promise observation compatibility on specified
rows, not byte-identical machine trajectories after adding steps, slots and
allocations. Define canonical rank independently of dynamic list append order
and list every intended change. Fuel, allocation count and stream indices can
change even when the final output does not.

**Cerberus reference.** Keep “Cerberus-shaped.” The pinned
[Core syntax](https://github.com/rems-project/cerberus/blob/b9aeedcb4dd438763b0eef7f95ac19e93875d7de/frontend/model/core.lem#L320)
contains unsequenced expressions and separate sequencing forms; the cited
[reduction](https://github.com/rems-project/cerberus/blob/b9aeedcb4dd438763b0eef7f95ac19e93875d7de/frontend/model/core_run.lem#L1372)
selects an eligible expression under a continuation. It does not itself prove
the proposed Go occurrence graph, whole-occurrence granularity, E1 edges or
guard joins correct. Replace “exactly” with an explicit adaptation statement.
This preserves the approved architectural choice while making its Go-specific
obligations visible.

## 5. Disposition of the first review and the next handoff

| First review | Second-pass assessment |
|---|---|
| F1/F2/F4/F6: placements, dependencies, failures, intermediate values | Addressed in the handwritten examples; retain as native exact-set regressions; R2/R6 qualify the general claim |
| F3/F5: target identity and dynamic lifetime | Correct design intent; representation and adapters remain to establish under R4 |
| F7: tapes/observability | Much clearer; remove R1's invalid reduction and qualify canonical/equality claims |
| F8: census | Correctly relabeled; dynamic cost remains an experiment, not a bound |
| F9: semantic contract and validation | Improved; guard semantics, actual machine comparison and source-to-wire certification remain open |

The next implementation handoff should contain the **selected grammar**, the
runtime record and operation table, repaired guard protocol, exact acceptance
sets, the first proof statements, an enumeration route, and the syntax-based
migration boundary. It should identify which existing user gates were actually
ruled. It should not say “S1 exactly” while these choices are left to the agent
to discover during a corpus-wide rewrite.

## Validation and scope

[AGENT] Read the v2 note and complete spike at `9a8ed328`, the first review,
the mechanism ruling, relevant current core/decoder/enumerator code, the pinned
Go clauses, and Cerberus sources. Local Cerberus HEAD was verified as
`b9aeedcb4dd438763b0eef7f95ac19e93875d7de`; public pinned links were also checked.
Go source pin: `c19862e5f8415b4f24b189d065ed739517c548ba`.

Re-ran the original reference enumerator: exit 0, output byte-identical to its
tracked `outcomes.txt`. Added four graph experiments and four Go probes in
[the review evidence](evidence/2026-09-16_eval-order-v2-review/README.md).
The graph experiments reproduce the reduction loss, skipped dependency,
logical-completion distinction and header narrowing. Go 1.26.5 default and
`-N -l` runs both exited 0 with identical draws. Those draws do not establish
the other permitted members. Commands, versions and output are tracked there.

No new core implementation, full CI run, Lean build or differential
re-certification was performed. This review and its small evidence scripts are
records only; the implementation plan remains a separate candidate.

Records checks passed: `git diff --cached --check`, `scripts/check-agents-alias`,
`scripts/check-evidence-size`, and `scripts/check-spec-anchors` (840 spec,
255 memory-model and 26 library citations at the pin). The anchor checker's
existing binary-file diagnostic for `docs/BUGS.md` was visible. Local link
targets and code fences were checked; re-executing all three evidence commands
matched `results.txt` exactly. These are focused records checks, not a full
CI or merge-certification claim.
