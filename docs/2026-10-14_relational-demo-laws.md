# Relational laws requested by the first logic demo

## Request and implementation

[USER] 2026-10-14: implement the next relational-interface iteration from
the logic demo's concrete `ReadVariableLaw`, `SequenceSpliceLaw` and
`AssignPointerVariablesLaw` requests. Preserve symbolic binders, actual
labels, pick-free guarantees and operation-derived premises. Check the
downstream acceptance examples read-only; no merge or push.

The request is `docs/2026-10-14_relational-demo-stage.md` in
`golean-logic/.claude/worktrees/relational-demo`. Exact statements and
acceptance are under its `experiments/2026-10-14_relational-demo/RelationalDemo/`.
Those sources are staged downstream rather than committed. The checked
`Requests.lean` SHA-256 is
`094044792f9fddaf10286193697c2c424d7e707ee65277890a85a0473ed41a05`;
`Acceptance.lean` is
`84a3222fac13ce257eba52753a1a4b9e258ea54fd4239880cf4546c9de55e485`.

[AGENT] 2026-10-14: continue the existing refactor branch from `ee1392b4`,
preserving the demo's first-cut ancestry. Add the read/splice laws to
`RelationalControl` and the assignment contract in `RelationalAssignment`,
exported by `GoLean.Relational`. Keep target/RHS/commit and empty-sequence
cleanup details private to the upstream proofs. No evaluator, relation,
memory-operation implementation or differential baseline changes.

All three requested propositions are true as written. Open
`GoLean.GoCore.Relational` after importing `GoLean.Relational`:

| Downstream request | Upstream theorem | Source |
| --- | --- | --- |
| `ReadVariableLaw` (RQ1) | `read_variable` | `GoLean/GoCore/RelationalControl.lean` |
| `SequenceSpliceLaw` (RQ2) | `sequence_splice` | `GoLean/GoCore/RelationalControl.lean` |
| `AssignPointerVariablesLaw` (RQ3) | `assign_pointer_variables` | `GoLean/GoCore/RelationalAssignment.lean` |

The binders and premises match directly: no wrapper changes the requested
domains. The variable-read witness retains the continuation's projected
access trace. Assignment reads the pointer and RHS before writing, so it
does not require the target to be distinct from either slot, and the target
remains an arbitrary `Loc`. Its write premise fixes the final store.
Sequence cleanup takes one or two steps according to the governing
continuation; the existential label list retains those actual steps, with
empty picks and output at every step. Memory-access labels are not erased.

## Acceptance check

The GoLean-only dependency closure was copied byte-for-byte into a local
scratch Lake package: `Fixture`, `Segments`, `Control`, `Activation`,
`Memory`, `Boundary`, `Requests` and `Acceptance`. It requires this GoLean
worktree by a local path. The aggregate `RelationalDemo.lean`, Iris imports,
and the downstream audit module were not used.

`AcceptanceCheck.lean` imports `RelationalDemo.Acceptance` and checks the
exact requested propositions:

```lean
open GoLean.GoCore.Relational RelationalDemo

theorem rq1 : Requests.ReadVariableLaw := read_variable
theorem rq2 : Requests.SequenceSpliceLaw := sequence_splice
theorem rq3 : Requests.AssignPointerVariablesLaw := assign_pointer_variables
```

It also checks symbolic wrappers of `Requests.read_set_parameters rq1` and
`Requests.set_root_acceptance rq2 rq3`, with their remaining binders and
conclusions written out unchanged. The latter has no law parameter: only
the original context, store, Boolean values, root-cell lookup and
distinct-root premises remain. It proves `PickFreeProgress` and a finite
pick-free `LocalNormalRun`, empty readback, the new target Boolean and the
unchanged framed cell. Every wrapper's `#print axioms` reports only
`propext`, `Classical.choice` and `Quot.sound`.

The complete symbolic wrappers are:

```lean
open GoLean GoLean.GoCore

theorem read_parameters
    (ctx : ProgramCtx) (s : Store) (target : Loc) (v : Bool) (k : Continuation) :
    (∃ tr, Transition ctx
      (expression (.var 0) (setActivation s target v).locals k (setActivation s target v).store)
      ⟨tr, [], []⟩ (returned (.addr target) k (setActivation s target v).store)) ∧
    (∃ tr, Transition ctx
      (expression (.var 1) (setActivation s target v).locals k (setActivation s target v).store)
      ⟨tr, [], []⟩ (returned (.bool v) k (setActivation s target v).store)) :=
  Requests.read_set_parameters rq1 ctx s target v k

theorem set_root
    (ctx : ProgramCtx) (s : Store) (a b : Addr) (old v framed : Bool)
    (ha : Heap.lookup s.heap (.base a) = some (.value .bool (.bool old)))
    (hb : Heap.lookup s.heap (.base b) = some (.value .bool (.bool framed)))
    (different : b.id ≠ a.id) :
    PickFreeProgress ctx (activationPoint setFunction (setActivation s (.base a) v)) ∧
    ∃ ls t, LocalNormalRun ctx setFunction [.addr (.base a), .bool v] s ls t (.ok []) ∧
      (∀ label ∈ ls, label.picks = []) ∧
      loadRoot ctx t (.base a) = .ok (.bool v) ∧
      Heap.lookup t.heap (.base b) = some (.value .bool (.bool framed)) :=
  Requests.set_root_acceptance rq2 rq3 ctx s a b old v framed ha hb different

#print axioms rq1
#print axioms rq2
#print axioms rq3
#print axioms read_parameters
#print axioms set_root
```

To reproduce, copy those eight files to a scratch package with this
`lakefile.toml` (adjust the relative GoLean path to the checked checkout),
copy GoLean's `lean-toolchain`, and put the snippets above after
`import RelationalDemo.Acceptance` in `AcceptanceCheck.lean`:

```toml
name = "relational-acceptance"
version = "0.1.0"
defaultTargets = ["RelationalDemo", "AcceptanceCheck"]

[[require]]
name = "golean"
path = "../.."

[[lean_lib]]
name = "RelationalDemo"
globs = ["RelationalDemo.+"]

[[lean_lib]]
name = "AcceptanceCheck"
```

```sh
LEAN_NUM_THREADS=2 capped lake build
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose GoLean RelationalDemo AcceptanceCheck
```

These imports exercise only the new GoLean exports; permanent upstream
modules do not import or copy downstream modules. Raw build/replay logs and
scratch copies are ephemeral.

## Validation

The targeted upstream build and all three headline axiom checks pass.
The scratch package builds the eight unchanged downstream modules and the
explicit acceptance wrappers without Iris (55 jobs on its initial build).
The acceptance wrappers have only the standard classical trio of axioms.
Kernel replay with the command above passed for exactly 89 source modules:
80 GoLean modules, eight `RelationalDemo` modules and `AcceptanceCheck`;
comparison against the source set found no missing or stale module.
That original validation used four Lean threads; the reproduction commands
above now use two, as required by the subsequent coordination charter.

`capped scripts/ci --diff` passed in 742 seconds: every target built
warning-free, the core totality/axiom audit and 396 eval tests passed,
frontend/Go/boundary and exhaustive scheduler checks passed, and every
speedbump was green. All 3,989 fresh differential rows (3,749 PASS and 240
known FAIL with classified causes) and all 405 negative rows matched their
unchanged baselines. The full run's metadata records the pre-commit dirty
worktree; only documentation was finalized after it. No failure was waived.

## Scope of the result

This discharges the three demonstrated semantic gaps, including both law
premises of `Requests.set_root_acceptance`. The acceptance result is still
the downstream semantic prerequisite, not the F1 ownership theorem or a
completed Iris adapter. General interior-location ownership/frame rules,
the final callable lookup/dispatch boundary and downstream live validation
remain downstream work as identified in the demo's result review.

The earlier upstream review's construct-usability finding is addressed for
these three specific requests; it is not closed for all constructs. The
general refusal/outcome, observation-coverage and locality/sequentialization
follow-ups remain open. No new `MachineWf`, refusal-freedom, typing or
non-aliasing assumption is imposed on the requested laws.

## Coordination and independent audit

[USER] 2026-10-14: continue under the paired coordination charter in
`golean-logic/.claude/worktrees/relational-demo-brief/docs/2026-10-14_golean-coordination-charter.md`;
commission a fresh independent audit of
`b25a47ef60984e2da16f80dedc0a1d5945806b8f`, disposition its findings, and
respond to concrete logic requests in checked batches. Do not merge, push
or modify the logic worker's tree. Logic owns the F1 ownership proof and
reuse example; upstream supplies their demonstrated missing semantic facts.

The reviewed implementation pin is the full `b25a47ef` commit above. The
request and acceptance hashes still match the first batch's recorded
inputs. At the first audit, the downstream stage record contained RQ1–RQ3;
no further concrete request had then been handed off. Reading concurrent downstream work
does not itself constitute a new request or a validation result.

The fresh reviewer `relational_laws_audit` received the goals, sources and
audit brief without the implementation conversation or a prescribed verdict.
Its complete report is preserved in
[the independent audit](2026-10-14-relational-laws-independent-audit.md).
It found **no new correctness, trust or acceptance defect** at the exact
implementation pin. The review ran in a separate worktree with independently
copied caches and frozen downstream inputs; its report records all eight
input hashes. It reproduced the unchanged acceptance, all five headline
axiom checks, exact 89-module source/replay equality and the core audit.
Supplemental checks discharge actual interior-write and coincident-slot
operation premises; these are separate from downstream acceptance.

### Dispositions

[AGENT] 2026-10-14: retain the implementation unchanged after this audit.
There is no new defect requiring a fix or waiver. Account for each numbered
review conclusion and its limits as follows:

| Review item | Disposition |
| --- | --- |
| 1, exact types/domains | Checked by the unchanged `rq1`/`rq2`/`rq3` assignments. Binding-slot reads retain `loadRoot`'s domain; the write target remains arbitrary `Loc`. No statement or premise change. |
| 2, actual labels | Retain the actual ordered transitions and per-step pick/output guarantees. Existential traces are not silence or a fixed footprint theorem. No correction required. |
| 3, aliasing/interior/cleanup | Checked by the proof and separate non-vacuity examples. The endpoint is `resumed k t`; no caller-tail execution is claimed. No correction required. |
| 4, acceptance/safety | The symbolic acceptance derives operation success and progress. Fuel exhaustion remains possible in `PickFreeProgress.run`; this is not a general choiceful safety result. No correction required. |
| 5, exports/trust/behavior | Facade, core audit, headline axioms and complete kernel replay passed. No executable implementation or baseline changed. No correction required. |
| 6, remaining scope | Open: downstream ownership, interior separation/framing, callable integration and reuse; upstream general failure/outcome coverage, observation coverage, and locality/sequentialization. No blanket migration or demo-completion claim. Follow concrete missing-law requests under the coordination charter. |

The review did not independently rerun full differential CI or authenticate
the removed ephemeral metadata of the historical pre-commit run. That run
remains the original implementer's evidence with its recorded scope; the
independent checks are the clean-pin acceptance, axiom audit and replay
reported above. No gate is waived, and the applicable fresh CI and audit
requirements still apply to the actual tree proposed for merge.

### First-batch dispatch to logic

Use immutable implementation pin
`b25a47ef60984e2da16f80dedc0a1d5945806b8f`. With `import GoLean.Relational`,
namespace `GoLean.GoCore.Relational`, RQ1 maps to `read_variable`, RQ2 to
`sequence_splice`, RQ3 to `assign_pointer_variables`. No domain, premise or
label changes. The unchanged GoLean-only acceptance closure plus the
explicit wrappers above passes `LEAN_NUM_THREADS=2 capped lake build` and
`LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose GoLean RelationalDemo AcceptanceCheck`
in independent scratch. Fresh adversarial audit found no new defects.
The commit recording this audit changes documentation only; the audited
semantic source remains exactly the implementation pin. Continue F1
ownership/callable integration and the reuse example; hand off any concrete
missing semantic laws with exact inputs and failed use sites. Upstream is
ready for the next request. No merge or push has been performed.

## RD3: reusable source calls and normal result delivery

The next requested batch is implemented through `SavedCaller`, `CallBoundary`
and `NormalExit`, with `SavedCaller.enter`, `CallBoundary.deliver` and the
composed `SavedCaller.invoke`. Supporting source laws are `reference`,
`assign_variable`, `return_start` and `return_sequence`. All are under
`GoLean.GoCore.Relational`, available through `GoLean.Relational`.

`LocalEntry.resultSlots` proves root result-slot validity from successful
activation alone, without a distinct-name, typing or `MachineWf` premise.
`Readback.traced` supplies the frame-read bridge. The composed call rule
uses these internally. Pointer arguments and caller destinations retain
arbitrary locations; writes preserve their specified order and allow aliases.
No executable semantics or baseline changed.

The original delivery proposition is false for interior pinned result cells,
as the relay's checked counterexample explains. The corrected six propositions
are discharged exactly. See [the RD3 handoff](2026-10-14_relational-call-acceptance.md)
for frozen inputs, compatibility proofs, reproducible acceptance and migration
instructions. Additional semantic callers use the same `invoke` rule for the
existing Set body theorem and a nonempty-result explicit-return identity.
The downstream Iris callers still require uptake and revalidation; no peer
worktree was modified.
