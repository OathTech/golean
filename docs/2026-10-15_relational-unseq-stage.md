# U1 restricted unseq sequentialization

Baseline: audited I1 `5d8e53e9f1a046fb645fce49901de714591e0819`.
Lane: `spike/relational-unseq-1015` in `.claude/worktrees/relational-unseq-1015`.
Private build/scratch state; all Lean jobs use `LEAN_NUM_THREADS=2` and `capped`.
The concurrency and D1 trees/pins are preserved.

## Decisions and intended theorem domain

- [USER] 2026-10-15: execute the relayed U1 charter from audited I1, obtain
  independent review, relay through the user; no main merge, push, live repin,
  peer writes or global changes.
- [AGENT] 2026-10-15: start with finite, topologically ranked graphs of
  deterministic, non-allocating expression occurrences and no phase-2 stores
  or guards. Each occurrence writes its own fresh binder; shared read inputs
  and earlier binder dependencies are allowed. Occurrence bodies remain
  sequences of real machine steps. Entry allocation is accounted for separately.

The observation equivalence is identical completion control and
store, with silence required explicitly for a parameterized client observation.
Actual ordered labels, accesses and scheduler choices remain available and
are not equated between permutations. Internal expression choices are excluded
from this first class. A finite-prefix/all-successor interface must expose
intermediate progress, admission and store facts; an endpoint equation alone
does not meet U1.

The graph order must imply scheduler progress and production of every consumed
binder. `wellFormed?` and actual entry checks remain separate obligations.
Root support is conservative and includes operational reads/checks, not merely
race events. Same-bound agreement is not allocator context extension.

## Inputs and status

Read-only logic handoff: `97426cab7c87ca52a5e3c480c9cb9b30ac534dde`, implementation
`f314a4f7ce69f8e5dc1c835298d4f1a2832a996f`. Read CLDD §5.5, `UnseqRules`,
`UnseqIndep` and `UnseqExecution`. The latter's positive occurrence judgments
remain hypotheses. I1 supplies finite `Run` composition and `StorePath` but
not sweep composition/progress through occurrence bodies.

RD8 implementation `5e8ed98ad68c31fa01ad879ed48b9ac8440ddb42`, reviewed handoff
`eba7d3bdaa7786cfc6daad949cd3217185e2c867`, supplies the frozen acceptance.
The four immutable Unseq files and all other Lean inputs are copied byte-exact
into private scratch. `U1RD8.simulation : RelationalCodeX.Sweep.SimulationLaw`
and `U1RD8.closed_guarded : RelationalCodeX.Sweep.GuardedTarget` are closed,
checked local adapter results. O1 remains independent; no O1 uptake is claimed.

[USER] 2026-10-15: consume the reviewed RD8 request without changing its frozen
inputs; keep general U1 primary and Plan/memory-skeleton/legacy Quiet downstream.
[AGENT] 2026-10-15: factor a store-uniform all-ready traversal, carrying actual
expression paths and a separate source-control policy. Both public safety and
the local resource adapter interpret this traversal. A whole-heap `At` premise
cannot be inferred from the client's finite owned rows, so the traversal's
status predicate is general.

The 16 inherited implementation findings remain open and unwaived. No lawfulness
of derived syntax equality is assumed. Richer occurrence kinds, internal choices,
cleanup/failure effects, allocation renaming and concurrent transport remain
outside this checkpoint. Prefix interfaces must leave the arbitrary tail free
to continue forever.

## Proved interface and source instance

The public `GoLean.Relational` facade exports the following layers. No
operational definitions, driver, runtime, existing theorem statements or
standing practices are modified.

| Layer | Laws and precise scope |
| --- | --- |
| Operational locality | `loadLoc_agrees` preserves the complete read result, including failure, from agreement at the root of an arbitrary location. `write_preserves_load` derives that agreement after a successful write at a different root. `AgreeOn` additionally records equal heap sizes; these are not cross-bound context-extension theorems. |
| Graph progress | `Ranked` requires dependency producers and named order predecessors to have smaller indices, no regions, and a producer for every declared cell. `Ranked.progress` supplies a ready least-active occurrence in any non-settled binary status. Empty phase-2 stores plus settled binary status supplies every completion consumer, including the arbitrary body. |
| Allocation and heap | `HeapDomain.ofAllocation` consumes actual successful `allocDecls` and scalar default/normalization equations. `At` fixes the allocator bound, fresh binder interval and every cell outside it. A done binder contains its specified result; other binders retain defaults. `At.write` proves the actual normalized write and preserves this invariant. |
| Real finite segments | `SafeUntil` requires admission, successful `stepFn` on every tape, and closure under every actual labelled transition until the boundary. `SegmentPrefix` retains every actual step and stops before executing the post-boundary body. `eventually` excludes an infinite execution remaining inside the segment. No whole-program termination follows. |
| Occurrence composition | `Domain.occurrence` uses `ReadOnlyExpr`/`StorePath` over every heap satisfying `At`, real dispatch, expression steps and binder write. The premise is a compositional operational expression law, not a semantic diamond or an Iris judgment. Expression steps are pick-free. |
| All schedules | `Ranked.traversal` uses active-count induction to carry every ready branch and its actual expression path. `Domain.all_schedules` interprets that same traversal into `SafeUntil`. `prefix_memory` and `prefix_progress` expose heap facts, admission and all-tape progress at arbitrary intermediate steps. The existential status in `MemInvariant` is a heap fact; it is not asserted to reconstruct arbitrary intermediate control. |
| Resource-usable intermediate structure | `StorePathFor` retains an explicit policy at every traversed source; `ReadOnlyExprFor.variable` and `.add_int` derive actual source steps. `Traversal` accepts arbitrary status-indexed store facts. `scheduler_cover` retains every tape/label/replay, `binder_effect` is a store-uniform owned-root update, and `completion_path` retains the real completion steps. No Iris representation or legacy observer enters the public surface. |
| Canonical execution | `Domain.canonical` chooses the least active occurrence, respecting all dependencies/order edges, and constructs an actual `Run` with exact scheduler pick records. `sequentialization` combines this with intermediate facts and equality of every completed segment endpoint. It does not equate ordered labels between schedules. |
| Entry and tail | `Domain.enter` and `canonical_entry` retain actual `wellFormed?`, `unseqEntryCheck?`, `allocDecls`, and the required `.seq` tail. Allocation is its own visible step. The body and saved continuation are unrestricted after completion. |
| Observations | `SafeUntil.output` proves actual byte-output silence from admission and transition rules. `observe` supports uniform projections; `observe_prefix` requires silence only on reachable pre-boundary steps for control-sensitive projections. No arbitrary observer is declared silent. Completion-state projections agree by state equality. |

The family has one fresh value binder per occurrence. It covers any finite DAG
presented in topological index order, with read sharing and dependent consumers;
graphs in another order require reindexing, and guard/region graphs are outside
this checkpoint. The actual source expression at each occurrence must satisfy
`ReadOnlyExpr` uniformly over **all** binary ready-state heaps, not just heaps
from one successful trace. Every expression-internal choice is excluded by its
pick-free path. Scheduler choices remain nondeterministic and recorded.

`U1.Symbolic.domain` discharges these premises for arbitrary program metadata,
stores, valid input roots and uint64 integer values. Its actual graph computes
`sum = x + y`, `copy = x`, and `less = sum < copy`. The first two occurrences
share `x`; the third consumes both results. Inputs may even alias, subject to
their supplied value facts. Integer normalization is explicit. `from_entry`
and `canonical` include actual admission and one-time allocation. There is no
schedule enumeration or status table, and no occurrence judgment is left as
a hypothesis.

`U1.Controls` checks an aliased write/read changing the read result, actual
print operations with no heap/access effect but order-sensitive bytes, and
actual successful allocations at unequal bounds returning different roots.
Allocation-renaming transport remains open. These controls are diagnostics,
not additional gates. `AliasControl.lean` adds a fresh actual source program:
an unordered function invocation writes the same root that its sibling reads,
with a dependent sum and actual phase-2 result store. The existing pool explorer
retains exactly {-2, 7}; the separate verified certificate checker accepts the
same set (8 explorer leaves; 226 certificate nodes, 231 edges). This executable
negative control is not the general sequentialization proof; only it enumerates
a finite fixture's schedules. Invocation/alias effects are outside U1's domain.

## Compatibility and remaining acceptance

The pool relation, attribution, driver gates, labels, race detector and runtime
are unchanged from I1. This sequential theorem does not establish stability
under another goroutine's writes or lift a segment atomically into the pool.
It leaves those real step boundaries available for a future interference proof.
Finite segment termination is compatible with an infinite following tail.

The initial-domain result does not close P4/P5/P13 generally. Richer occurrence
kinds, guards, phase-2 stores, internal nondeterminism, failure/cleanup effects,
renaming across allocator bounds, and concurrent transport remain open.
The exact RD8 semantic constraint and original guarded target compile through
the checked local adapter described below. This establishes the first restricted
U1 candidate, not completion of the full replacement interface or live downstream
integration. The frozen logic's live `35 NOT-PUBLIC` failure remains open and was
not rerun or reclassified by this experiment.

The 16 inherited implementation findings are individually dispositioned in
`2026-10-15_relational-integration-stage.md` under the declaration-prefix table.
All 16 dispositions remain **open and unwaived** here: two generated syntax
equality implementations, five core/seed renderers and the nine declaration
renderer implementations (the table, not these group labels, is authoritative).
U1 does not introduce an equality-lawfulness assumption or replace their
disposition with a green build. The fresh exhaustive audit must still report
the implementation scan as FAIL separately from the kernel-axiom result.


## Reproduction

Use a fresh worktree at the immutable implementation pin recorded in the review
handoff, with its own build directory. From that worktree:

```sh
scripts/setup-deps --from /home/mike/projects/golean --only goose,go
LEAN_NUM_THREADS=2 GOTOOLCHAIN=local GOPROXY=off GOTELEMETRY=off GOENV=off \
  GOPATH="$PWD/.tmp/gopath" GOMODCACHE="$PWD/.tmp/gomodcache" \
  GOCACHE="$PWD/.tmp/gocache" capped -m 64G -- scripts/ci --diff
LEAN_NUM_THREADS=2 capped lake env lean \
  experiments/2026-10-15-program-outcomes/ProgramOutcomeConstraint.lean
```

From `experiments/2026-10-15-unseq-compatibility`:

```sh
LEAN_NUM_THREADS=2 capped lake build
LEAN_NUM_THREADS=2 capped lake env lean U1/Audit.lean
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose U1
LEAN_NUM_THREADS=2 capped lake env leanchecker --fresh --verbose U1.Audit
```

From `experiments/2026-10-14-concurrency-compatibility` (the copy **inside this
candidate**, never the preserved historical lane):

```sh
LEAN_NUM_THREADS=2 capped lake build
LEAN_NUM_THREADS=2 capped lake env lean Concurrency/Audit.lean
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose Concurrency
LEAN_NUM_THREADS=2 capped lake env leanchecker --fresh --verbose Concurrency.Audit
```

The D1 source/control files and I1 program-outcome constraint are unchanged.
Their checks preserve the actual two positive pool executions and the
unconditional pre-pair rejection. No finite test corpus is offered as an
operational equivalence proof: the pre-existing interpreter, driver and detector sources are byte-identical to I1.

## RD8 adapter and exact dependency

`experiments/2026-10-15-unseq-rd8/U1RD8/` is experimental and outside the public
GoLean dependency graph:

| File/result | Connection |
| --- | --- |
| `Base.path_plan`, `write_at` | Interpret actual store-preserving paths and single-root updates as Plan nodes. Row permutations preserve the owned inventory. Skeleton compatibility for int64 cells is proved locally using `Memory.flattenCell_skel_flat`. |
| `Source.paths` | Derives the actual reads of source ids 0/1 and dependent add of binders 3/4 for arbitrary normalized signed int64 inputs. `ready_produced` supplies both dependent values at every ready status; source-control Quiet is proved for every observer/store/tape. These are policy-strengthened equivalents of frozen left_path/right_path/sum_path, not assumed occurrence judgments. |
| `Source.traversal` | Instantiates the general `Ranked.traversal` over finite row facts; unrelated cells are unconstrained. There is no conversion of finite ownership into whole-heap equality. |
| `Simulation.interpret` | Inducts over that traversal, consumes every carried expression path and every ready continuation, and uses the public all-tape scheduler, binder effect and completion path. Handles actual empty-sequence glue without assuming termination/silence of the arbitrary tail. |
| `simulation` | Actual entry check/allocation and the interpretation discharge exact frozen SimulationLaw. No schedule or completed-run premise. |
| `closed_guarded` | Applies frozen `guarded_acceptance` to simulation. The original guarded target is closed; real per-step laters, ownership updates and allocation come from frozen plan_wp. |

The audit checks direct proof-body dependencies: closed_guarded -> simulation
and guarded_acceptance; simulation -> traversal/interpret/real entry allocation;
traversal -> Ranked.traversal and paths; paths -> variable/add/read_root/ready_produced;
interpret -> Traversal.rec, scheduler_cover, binder_effect, completion_path,
path_plan and write_at. Public Domain.all_schedules also consumes Ranked.traversal
and the actual occurrence interpretation. Merely importing a U1 theorem would
not pass these use sites or prove the interpretation.

To reconstruct the adapter from this worktree (explicit dependency seeds are
read-only; setup independently clones exact revisions and copies caches):

```sh
python3 experiments/2026-10-15-unseq-rd8/setup.py \
  --logic-source /home/mike/projects/golean-logic \
  --seeds /home/mike/projects/golean-logic/.claude/worktrees/develop/packages/golean-iris/.lake/packages
cd .tmp/rd8
LEAN_NUM_THREADS=2 capped lake update
LEAN_NUM_THREADS=2 capped lake build U1RD8.Audit
LEAN_NUM_THREADS=2 capped lake env lean U1RD8/Audit.lean
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose U1RD8
LEAN_NUM_THREADS=2 capped lake env leanchecker --fresh --verbose U1RD8.Audit
```

No frozen source is edited. Generated package wiring points to this GoLean lane.
Exact dependency pins are the frozen pins.json: iris e7a0a43814c4f1154ca0c8049883ca56c2288b86,
batteries 023ce7d62a0531e22a5331e20b587817a80d49ff and Qq
38d591e778f100aec9762bb582f9c7f55f50e9dc. A missing seed/cache is an explicit
setup failure; the script does not fetch or build in a peer.

## Additional frozen downstream implementation findings

The wider adapter import closure reports **FAIL: 21 implementation findings**:
the existing 16 plus these five. Each remains open/unwaived, raised with the
user. They are present in byte-identical frozen sources, not newly introduced
U1 definitions. Standard-only axioms and successful kernel replay are separate
facts and do not waive implementation findings.

| Finding (full declaration suffix `_unsafe_rec`) | Disposition |
| --- | --- |
| `GoLean.IrisCustomer.pathTags_persistent._unsafe_rec` | Open, unwaived; generated partial implementation whose parent is not recognized as a transparent total definition by the scan. Frozen customer ownership code; no change or waiver here. |
| `GoLean.Logic.Source.instReprScalarTy.repr_1._unsafe_rec` | Open, unwaived; frozen generated scalar-type renderer implementation. |
| `GoLean.Logic.Source.instReprScalarTy.repr_2._unsafe_rec` | Open, unwaived; frozen generated scalar-type renderer implementation. |
| `GoLean.Logic.Source.instReprFieldTys.repr_1._unsafe_rec` | Open, unwaived; frozen generated field-type renderer implementation. |
| `GoLean.Logic.Source.instReprFieldTys.repr_2._unsafe_rec` | Open, unwaived; frozen generated field-type renderer implementation. |

The unchanged frozen `GoLeanIris/Memory.lean:1625` unused-variable warning also
remains visible. No new U1 or adapter source warning was suppressed.

## Validation

Final results and independent-review dispositions are in
`2026-10-15_relational-unseq-review.md`. Logs, private copied dependencies,
compiled artifacts and dumps are disposable; the source and reproduction
commands are the persistent evidence.
