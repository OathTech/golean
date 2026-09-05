# A2 — a minimal Iris test customer for GoLean

[AGENT] implementation plan under the [USER] request of 2026-09-05 to
plan and build a simple Iris-based logic, using refined-cerberus, BRiCk
and RefinedC as references. Base: `8db2d6da`. Worktree/branch:
`gate-a2-iris`. No merge or push is authorized for this new work.

## Purpose and boundary

Build enough separation logic to expose semantic-interface problems through
real program proofs. The operational authority is GoLean's existing machine
and program driver. The customer derives rules from those semantics; it does
not implement a second Go interpreter. Iris remains outside the default
semantics dependency graph, in `spikes/iris-customer/`.

Use the A1 bare `Language` instance and exact trace bridges as the initial
experimental dependency. Keep continuations explicit: recovery inspects and
changes them. No unconditional context-transport or `EctxLanguage` promise.
Normal sequential return is the first proof contract; uncaught panic stays
an explicit separate observation and is excluded by `NotStuck` WP proofs.

## Implementation sequence and exit tests

1. Connect `gen_heap` to the real dense array of `HeapCell`s. Prove lookup,
   update and fresh-allocation correspondence. Pin all immutable execution
   context fields in the state interpretation; do not mislabel the address
   bound as a typing invariant.
2. Supply fractional cell ownership, read/write/allocation lifting, frame
   and consequence rules, and explicit-continuation control rules. Prove a
   small framed heap example before the full call/defer example.
3. Instantiate the ghost resources and prove adequacy with initial heap
   ownership and final-state readout. The exported result must concern
   actual GoLean execution, not only Iris's own transition closure.
4. Exercise actual function entry, helper calls, defer registration, recovery
   and named-result readout. Include normal-return and uncaught-panic
   controls. Compare a real Go source fixture through the native frontend;
   record exactly how its GoCore artifact relates to the proof program.
5. Connect the Iris postcondition to the actual program driver for the
   chosen example, including the single-thread detector, choice and output
   policy. State exact restrictions wherever a general transfer is absent.
6. Run the normal core build, dedicated package/axiom gate and focused
   differential tests. Record proofs, remaining gaps and lessons for B7/C1,
   admission and composition. No claim of general Go verification follows
   from this small customer.

## Reference decisions

- refined-cerberus (`/home/dev/projects/cerberus-lean-proj/refined-cerberus`):
  its `cerberus-heaplang` logic connects ownership to engine memory and ends
  adequacy in the shipped driver. Follow that dependency direction. Its
  C byte/provenance model and broad statement judgments are not Go rules.
  Inspected at `8eeaf924ad630557458dcd99e164ddbd03d1d2f3`; its later
  `c2ebeb7915da06461aa2bed8f898a7ca59c883b2` only adds a status document.
- RefinedC, local pin `25f706d417df2b18b23c5cbadde46468c1b1262c`:
  `theories/caesium/lifting.v` derives lifting from operational steps and a
  coherent state interpretation. Reuse the design separation between memory
  ownership and program context, rather than copying its C memory policy.
- BRiCk, local pin `eee838e797ee636dd1f3de451ef7b2751018f313`:
  `rocq-skylabs-brick/theories/lang/cpp/logic/wp.v` makes statement exit
  continuations explicit. Go panic/recover requires its own continuation
  rules; BRiCk's documented absence of C++ exceptions is not transferable.
- Archived GoLean reasoning, `7440bf705a87b052243ff36280b677f4100b6a66`:
  `Ghost`, `HeapBridge`, `Lifting`, `Adequacy` provide a proof quarry at the
  same Iris pin. The old association-list heap and incomplete context pins
  must be replaced with current-machine facts, not ported as assumptions.
- Iris pin remains A1's `e7a0a43814c4f1154ca0c8049883ca56c2288b86`,
  Lean 4.32.2. Every exported proof is audited for transitive axioms against
  the classical trio. Actual ghost-resource initialization is required;
  an abstract WP with no demonstrated interpretation is insufficient.

## Parallel work

The independent `bug103-array-conversion` worktree fixes the known missing
array-target conversion arm. It owns that runtime fix, its regressions and
evidence, and does not modify the customer package. The customer stays on
the base until a deliberate integration decision. Heavy validation runs are
coordinated; every Lean/Lake process uses `scripts/capped`.

## Explicit limits

No generic type-admission checker or typing preservation, concurrent
adequacy, reflection expansion, semantic identity redesign, or complete
source-to-GoCore compiler proof is included. A differential check is evidence
for the source-to-model link, not a formal translation theorem. Restrictions
must stay visible in theorem statements and the final evidence record.

## Implemented result and assessment

[AGENT] The bounded A2 implementation is complete, with the separate gate
green and [independent adversarial review PASS](2026-09-05_iris-customer-review.md);
integration remains owed. The review required no code changes. This is
not a declaration that the whole of Gate A has passed. The implementation is
in `spikes/iris-customer/`; its README is the theorem and module map.

The customer proves `Recovered` returns `true` with empty output through
`runProgramPoolOutM 60`. Its actual setup enters the native-lowered body with
the named result allocated. The Iris proof follows capture evaluation, defer
registration, entry to `fail`, panic unwinding, deferred closure entry and
parameter allocation, recovery-local allocation, `recover()` marking the
suspended panic, interface-vs-nil comparison, pointer load, named-result store
and frame exits. The result goes through initialized Iris resources and
actual `loadMany` readout. Separate kernel computations establish the bounded
successful execution, no registry boundary steps and silence. Neither WP
nor differential testing is mislabeled as a termination proof.

Normal return has its own WP and instantiated readout theorem. An arbitrary
second heap cell is preserved in `framed_normal_adequate`. The no-defer control
has an explicit whole-program panic theorem. Native emission/lowering matches
the checked-in artifact, and the three Go-vs-Lean observations agree. Evidence:
`docs/evidence/2026-09-05_iris-customer/README.md`.

### What this tells us about GoLean

1. **Keep the current machine and executable/relational co-design.** The
   existing total semantics supports real Iris ownership and entry-to-readout
   reasoning. There is no evidence here for restarting the semantics or
   returning to an archived machine. The current dense heap also makes fresh
   allocation correspondence simpler than the archived association-list heap.
2. **Promote a small semantics-owned interface next.** The useful boundary
   now has evidence: exact traces, `step_complete`/`stepFn_sound`, terminal
   configuration, heap lookup/update/append, `enterFrame`, recovery's explicit
   continuation transformation, and singleton pool conservation plus output
   projection. `ContextEq`, ghost resources, WP and program proofs stay in
   the customer. A1 promotion remains a separate small task; this change
   deliberately consumes the reviewed A1 package directly.
3. **Preserve B7/C1, with customer acceptance tests.** `ContextEq` currently
   pins all five immutable fields using a whole-state equality modulo heap.
   B7's context/store split should make this explicit without weakening it.
   C1's observable memory accesses must preserve actual load/store behavior
   and detector obligations. Run both core gates and this customer gate on
   each relevant semantic refactor; it remains outside the default graph.
4. **A3 is still necessary.** Cell ownership is not static typing. The proof
   can intentionally quantify over an arbitrary previous value in a result
   cell that is overwritten before any read. This is a valid local theorem,
   not an admission theorem for arbitrary GoCore. Separate structural table
   validity, supported features, valid entry/arguments and typed states. Start
   with a checker for a precisely stated small predicate, positive witnesses
   and malformed-input rejection; do not define acceptance by successful
   execution or call normalization a type checker.
5. **Use explicit continuations before promising general composition.**
   `wp_recover_assignment` exposes the assignment, sequence, non-wrapper
   deferred frame and suspended panic it crosses. This is a checked useful
   rule, but it is not a generic statement/call-specification system. The
   example still follows concrete control steps and has program-specific
   helper/deferred-entry lemmas. C3 should be justified by maintainability and
   admissible composition laws, not a claim that lists imply `EctxLanguage`.
6. **Keep the full-program transfer's scope exact.** The lower-level
   `execProgLoop_single` supports arbitrary starting configurations, unlike
   its statement wrapper. Together with `execProgLoopOut_snd` it transfers
   this example's Iris result through the real singleton detector and output
   driver. It needs a successful sequential witness and handles the pool's
   extra registry-step fuel explicitly (zero here). General all-outcome,
   all-stream labeled or concurrent adequacy remains open.

### Proposed next tasks, in order

| Task | Reviewable completion test |
|---|---|
| Review and retain A2 | Adversarially inspect ownership initialization, concrete result dependency on Iris, source/artifact link, pool/output restrictions and gate rejection tests; no merge without sign-off |
| Promote A1 semantic bridges and an experimental facade | No Iris imports in GoLean; A1 and A2 gates still pass; exact domains and remaining internal dependencies listed |
| Specify and implement the first A3 admission slice | Checker soundness for its named predicate, admitted witness and malformed-input negatives; explicit separation from full typing/preservation |
| B7, then C1 | Existing differential/detector gates plus the unchanged customer assertions; no silent loss of immutable context or observational obligations |
| Revisit composition/C3 with a second client proof | A reusable call/statement rule with stated admissible continuations, exercised beyond this one concrete recovery path |

These are [AGENT] recommendations. Existing [USER] design rulings and hard
gates are not overridden. The independent BUG-103 fix is branch
`bug103-array-conversion`, commit `7b7bc42c3f77154099ccbb3c6f6a302a8d1987d4`;
it was validated against a full 3,598-case measurement with no unrelated
result changes. It is not a dependency of A2 and has not been merged into
this lane. Its note and evidence live on that branch.
