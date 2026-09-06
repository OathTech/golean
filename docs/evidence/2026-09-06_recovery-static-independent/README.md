# Independent review of the recovery static foundation

[AGENT], root integrator, 2026-09-06. The reviewer did not author the six
recovery static modules. Source reviewed: the frozen `typed-recovery`
implementation based on `fadcb0c3`, identified by `sources.sha256`. This is
an implementation review of the static increment only.

**Verdict: CHANGES REQUIRED for diagnostic separation (RS-1).** The review
found no counterexample to the independently defined judgments or their
checker equivalence. Runtime preservation, setup, panic rendering, and the
Iris customer are still owed and receive no acceptance from this review.

## Evidence and scope

The reviewer read all six complete source modules, the two claim/design
notes, the 37 challenge declarations, both native artifacts and their
checking apparatus, the second native source and five pinned results, the
post-import audit and all four compiled poison controls, and the author's
final full dedicated gate and ordinary CI logs. The author's CI explicitly
reuses the original 3,598-case executable record; it is not a fresh broad
runtime campaign.

`Review.lean` concatenates the exact six source bodies, omitting only their
imports, after importing the integration branch's existing Boolean typing,
operations and Lean infrastructure. It imports no author-built recovery
olean. Thirteen independently written kernel probes challenge:

- first-match binding within one mixed-sort scope;
- rejection of nil assignment to a live-root parameter and acceptance of
  another live Boolean alias;
- rejected zero-initialized pointer results, admitted payload results, and
  recovery nested inside a Boolean condition outside a deferred handler;
- a missing callee and a mixed direct/deferred cycle in unreachable code;
- a maximal three-function call/closure/defer chain in reversed table order;
- duplicate function IDs and external pointer arguments;
- restoration of a hidden payload binding after a Boolean shadowing block;
- arbitrary byte arrays as explicit string panic payloads;
- the diagnostic collision described below.

Fresh elaboration of the complete source and probes passed without warnings:

```text
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped lake env lean docs/evidence/2026-09-06_recovery-static-independent/Review.lean
```

`review-final.log` records the final run's audit of 4,999 imported/local
declarations with only `propext`, `Classical.choice`, and `Quot.sound`
allowed. This audit covers the concatenated source and probes, including
unused declarations. The original 12-probe run is retained as `review.log`;
the final run adds the diagnostic reproducer. These are supplemental checks,
not a replacement for the author's compiled poison gate or final integration
gates. `Probes.body` records the independently authored part separately.

## RS-1: distinguish unsupported body syntax from malformed bodies

`RecoveryAdmission.lean` reports `Error.body fid` both for a valid Go panic
whose boxed payload is Boolean (outside this explicit string-payload
profile) and for an unbound Boolean write (a malformed GoCore body). Its
message lists both possibilities. The final kernel probe proves the exact
same returned error for those distinct causes.

The charter's O1 diagnostic requirement distinguishes outside-profile input
from malformed input; O2 should preserve that audit discipline as it extends
the foundation. O1 already separates syntax/placement from scoped bindings.
Keep the recovery admission judgment and accepted domain unchanged. Add a
total structural surface/placement discriminator, prove that every typed
statement passes it, and distinguish its diagnostic from subsequent
binding/sort/call-vector failure. Equivalent diagnostic implementations are
acceptable; no requested change licenses narrowing the profile. Add paired
kernel controls for a supported malformed body and valid outside-profile
syntax, retain all existing positives, and rerun the affected static gate.

This is a bounded, ordinary implementation finding. It does not require a
user policy ruling or block independent runtime-proof development. The
reviewer must inspect the fix before issuing a final static PASS.

## Boundaries retained

The root refinement is stronger than a Go pointer type and requires the
future runtime invariant to establish live Boolean cells; parameter type
classification alone does not prove liveness. Exact ordered signatures,
capture prefixes, ordinary result vectors and deferred result discarding
are checked independently of function bodies. All bodies and syntactic
call/defer edges are checked, including unreachable and uncalled ones.
The no-cycle theorem is an actual strict-depth argument. Checker equivalence
is with the declared table-size-bounded call-tree judgment; the separate
graph-theoretic completeness result for arbitrary finite DAGs is not claimed.

The full original A2 artifact and second native fixture meet the static
minimum. In the latter, the indirect recovery precedes direct recovery
while a panic may still be active; both defer-order and effective-directness
controls change the Boolean result. Shared semantic aliases do not supply
duplicated exclusive Iris ownership. Arbitrary bytes and equal explicit
string re-panic remain admitted; the separate observer/R-1 work cannot be
discharged by restricting those tests or by this static review.
