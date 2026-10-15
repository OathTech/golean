# Observed assignment, entry and delivery phases

This additive increment supplies the three exact RD8 phase requests at frozen
logic implementation `3c9be98f8de86f04c4cec53d75490199718da066`, reviewed at
`621316254d5a32c1489593ad0e7b8c26122df0e4`. Private applications close both
unchanged `CalleeTarget` and `CallerTarget`, and the actual `hist_code`,
`adequate`, `caller_prefix` and `outcomes` with no pending phase-law parameters.
Ordinary downstream uptake remains the logic team's work. No live migration,
full replacement landing, executed-renderer correspondence or concurrent
adequacy is claimed.

I2 stays independently consumable at implementation
`4731d491999e113e5016ad975d1747614d100bd4`, reviewed handoff
`8bcaef3764257ed262a7801be2cf6484cab4dfaa`. This increment is based on that
handoff; its older frozen O1/U1 consumers are kept separately. Runtime sources
and behavior are unchanged. No main merge, push, live pin or peer write.

## Decisions and source binding

[USER] 2026-10-15, relayed in `2026-10-15_rd8-observed-phase-relay.md`:
discharge the exact three semantic refinements and their actual guarded
caller/adequacy uses, additively after I2; preserve the older acceptance and
all inherited trust findings. The relay is in the read-only logic brief lane.

[AGENT] 2026-10-15: reuse U1's `StorePathFor`/`ReadOnlyExprFor`, add matching
policy-carrying effects/ordered writes/operand lists, and specialize their
source policy to empty semantic boundary events. Keep the old erased APIs at
their original domain: an arbitrary erased read-only operand can be eventful.
The stronger proofs retain concrete intermediate controls internally rather
than inferring silence from endpoints or empty base labels.

Frozen private package: all 137 original files other than generated Lake
config/manifest match immutable objects; all 128 original Lean files are
unchanged. `ObservedPhaseRequests.lean` SHA-256:
`8ab37816f07b289cb1744b074e79a38132a3244d8b0a73b34aa18e741045ae50`.
Original provenance and dependency pins remain intact; private Lake wiring
alone selects the candidate GoLean checkout. Dependencies are independently
cloned, with copied caches from explicit read-only seeds: Iris `e7a0a438`,
Batteries `023ce7d6`, Qq `38d591e7`, Lean 4.32.2.

## Public laws and private adapters

All public names below are under `GoLean.GoCore.Relational`, exported through
`GoLean.Relational`. No customer module or Iris representation enters GoLean.

| Exact frozen request | Public semantic law | Private adapter |
| --- | --- | --- |
| `RelationalCodeX.Observed.AssignmentQuiet` | `Observed.variable_assignment_phases` | `PhaseAcceptance.assignment` |
| `RelationalCodeX.Observed.VariableEntryObserved` | `Observed.SavedCaller.entry_phases` | `PhaseAcceptance.entry` |
| `RelationalCodeX.Observed.DeliveryObserved` | `Observed.CallBoundary.delivery_phases` | `PhaseAcceptance.delivery` |

`StoreEffectFor` adds a source policy only under its actual store operation.
`OrderedWritesFor` composes policy-carrying preparation and ordered effects;
`OperandPathsFor` composes policy-carrying expression paths. All have checked
erasure into the existing semantic carriers. `Observed.StorePath` specializes
the existing path carrier to `∀ s, fact s → Boundary.events ctx ⟨c,s⟩ = []`.
Its weakening changes both the fact and conditional policy. Existing path
composition remains available; reflexivity imposes no endpoint policy.

Observed variable/reference/integer-add expression laws support general RHS
assignment and arbitrary operand lists. `pointer_rhs_phases`,
`variable_expression_phases` and `pointer_assignment_phases` expose the same
write boundary with intermediate event facts. This is sufficient compositional
expression support, not completeness for all event-free Go expressions.

Entry preparation is uniform over supplied stores, resolved functions and
activations. Lookup, non-method, arity and `LocalEntry` premises justify the
actual `Enters` effect, resolved id, original supplied values and pre-store.
Zero and multiple arguments are covered; the frozen one-variable request is
a corollary. The callee body is unrestricted.

Delivery covers both normal exits, arbitrary result lists and bound-variable
destinations, including repeated and interior locations. `Boundary.Returns`
records the snapshot **before** destination evaluation and every write.
Subsequent paths need only `True`; each write needs its own `storeLoc` result.
Aliasing cannot force stale readback after an update. `ResultSlots` remains
derived from activation by the unchanged downstream rule. The semantic
`CallBoundary` domain has no pending defers, as before.

All traversed sources retain nonterminal/init admission, actual transition
labels and pick freedom. No whole-run success, global well-formedness, final
tail silence or following termination premise is added. Finite paths remain
compositional steps rather than atomic effects. Broader interference transport
and concurrent/infinite adequacy remain separate work.

## Exact consumer and actual proof use

`PhaseAcceptance.callee : CalleeTarget` supplies assignment to the unchanged
callee proof; `PhaseAcceptance.caller : CallerTarget` supplies entry/delivery
to the unchanged caller proof. The latter consumes the callee's logical
contract; it does not reach `identity_body` or `callee_acceptance`.

`CallerAcceptance.lean` repeats the four original actual-caller theorem
headers verbatim, with only the three law variables discharged. It retains
the symbolic Boolean and exact `[call [v], returned [v]]` history, including
the call-only prefix admitted by the invariant. Contract assembly remains
outside the caller. Original StringPlain, lookup/method, setup, fuel/tape,
normal/panic witness and fuel-exhaustion alternatives are unchanged.

Checked proof-value closure links the adapters to public phase laws and
actual variable reads; the caller to the guarded call rule, O1 agreement and
activation-derived result-slot validity; and adequacy/prefix/outcomes to their
original general roots. The frozen pure-return counterexample remains valid.
Empty base labels and equal endpoint stores are never used to infer silence.

Client work still includes source applicability, typed layouts and ownership,
resource splitting/reassembly, observer projection/invariants, pure logical
consequences and continuations. This upstream acceptance supplies the missing
semantic laws; it does not itself record ordinary downstream R1 completion
or replace downstream R2/U1 uptake.

## Validation and independent review

All Lean/heavy commands use `capped`, `LEAN_NUM_THREADS=2`, private temporary
state and independent caches. Exact reproduction is in
`experiments/2026-10-15-observed-phases/README.md`.

- Full `scripts/ci --diff`: **PASS**, exit 0, 902 seconds. Warning-free
  upstream build: 261 jobs; exact kernel replay: 113 GoLean modules; core
  totality/axiom audit and all 396 interpreter tests pass. Fresh differential
  corpus: 4,025 rows, 3,767 PASS/258 tracked FAIL, no baseline regression.
  Fresh negative corpus: all 415 rows match. Frontend, wire, method,
  declaration and whole-tape scheduler checks pass. The one initial memory
  inventory speedbump red is dispositioned below; every other speedbump passes.
- New public facade build: PASS, 77 jobs. Frozen new package build: PASS,
  456 jobs; subsequent `PhaseAudit` build: PASS, 420 jobs. Direct audit
  elaboration reports 24 new headline axiom checks and 27,065 declarations,
  standard axioms only. Nine positive/negative proof-value closure checks pass.
- New package exact kernel replay: PASS, exit 0, **450 modules**: 113 GoLean,
  128 unchanged local modules plus three acceptance/audit modules, and 206
  dependency modules (174 Iris, 18 Batteries, 14 Qq). Every expected module
  occurs exactly once; all source modules have matching built/replayed outputs.
  Additional `leanchecker --fresh --verbose PhaseAudit`: PASS, exit 0.
- Separate old I2 package: PASS, 449 build jobs. Joint audit: 26,898 declarations
  plus 120 integration/example helpers, standard axioms only. Exact replay:
  PASS, exit 0, **442 modules** (113 GoLean, 123 local, 206 dependencies).
  All original package files match the older immutable `5e8ed98` objects,
  except private Lake wiring/manifest; O1/U1/joint adapters remain unchanged.
- Both combined implementation inventories remain **FAIL, 21**, with exact
  name-set equality to I2, not just matching counts.
- Fresh alias control: PASS, actual outcomes exactly `{-2, 7}`, eight leaves,
  behavior certificate 226 nodes/231 edges. This preserves the distinct alias
  behavior and is not used as the general traversal proof.

Earlier failed commands are not counted as passes: initial new-law compilation
exposed argument-list reassociation and source-policy simplification issues,
which were fixed; the first audit wrongly expected `read_root` where the
semantic law actually consumes `read_variable`; an early alias run lacked its
not-yet-built Tests import; and `leanchecker --fresh` rejected multiple roots,
so its reproduction uses the single `PhaseAudit` root. None required changing
the frozen request or target.

The CI memory-callsite speedbump initially failed on one new
`OrderedWritesFor`/`storeLoc` premise. Its new inventory row classifies the
Prop-level premise as NO EXECUTION and retains the existing emitting write
label. The exact speedbump rerun passes all 89 rows. This was the only change
to the pre-validation 4,398-file source/configuration freeze; all Lean source
bytes remain identical. Both before/after inventories are retained only during
work for final commit binding.
CI's corpus metadata correctly reports a dirty tree: it certifies those
tested bytes, not the pre-increment HEAD. The immutable handoff binds that
source/configuration freeze to the implementation commit instead of claiming
a clean-commit run. No baseline or gate was weakened.

Fresh independent review found no new semantic/acceptance blocker. It checked
all three exact requests, both targets, the four unchanged caller headers,
an eventful final-tail example, thirteen proof-body inclusion/exclusion edges,
and complete type/value exclusion of the ten named inherited logic helper and
parent endpoints from five new result roots. Its separate five-module replay
and headline axiom checks pass. It also independently checked the inventory
repair. These are reviewer checks; the full CI and whole-package replay above
are author evidence. The committed review records final immutable binding and
its own precise scope.

## Trust findings retained

The implementation scan is **FAIL: 21 unwaived findings**, the same 16 upstream
plus five frozen logic findings. The complete name inventory is retained in
`2026-10-15_relational-o1-u1-integration-review.md`, under “Fresh implementation
findings”; this increment must match that exact set, not merely its count.
Successful standard-axiom checks and kernel replay do not waive the scan.

- T1 `GoLean.IrisCustomer.pathTags_persistent._unsafe_rec`: the frozen independent
  diagnosis finds a kernel theorem parent, erased helper and no helper edge in
  that proof. No demonstrated logical defect in that inspected scope; the
  failed inventory entry remains unwaived.
- T2/T3 `GoLean.Logic.Source.instReprScalarTy.repr_1/2._unsafe_rec`: unresolved
  compiler-selected scalar/field renderer correspondence.
- T4/T5 `GoLean.Logic.Source.instReprFieldTys.repr_1/2._unsafe_rec`: unresolved
  corresponding mutual renderer implementations. No current checked logical
  or artifact dependence was demonstrated by the frozen scoped diagnosis.
- All sixteen upstream findings remain open, including load-bearing GoCore
  rendering. Neither the diagnosis of the five logic findings nor the new
  phase laws certifies those executed renderers.

The inherited Memory unused-`h` warning and historical live **35 NOT-PUBLIC**
failure remain separate. No live check is rerun or relabeled as fresh evidence.
