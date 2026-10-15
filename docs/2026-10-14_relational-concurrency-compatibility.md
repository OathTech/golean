# Concurrency compatibility experiment

Baseline: `fc52512a6644c04996d327865919556107cf84ba`.
Lane: `spike/relational-concurrency-1014`; all additions are experimental.

## Decisions

- [USER] 2026-10-15: run the relayed concurrency brief independently of
  RD5/C1, at the audited pin, with isolated build state and no runtime/API
  changes, merge, push, peer writes or live repin.
- [AGENT] 2026-10-15: use a print-apply boundary between two parent reads
  and an unbuffered rendezvous for the synchronization probe. These are
  existing pool boundaries; the examples use the existing singleton
  `execProg` entry and its empty detector, then the actual spawn.

## Result and exact domain

The existing relational variable-read phase is reusable inside the actual
pool relation. Two finite, selected executions are proved through the
output-preserving driver and its real detector, with no detector-success
assumption. This is compatibility evidence, not an Iris lifting/adequacy
proof, all-schedule safety, frontend correctness or a general
sequentialization theorem.

The inputs are explicit hand-built GoCore stores and environments at the
existing `execProg` entry: one main goroutine, index 0, empty detector, a
specified tape. The actual `go` execution appends child 1 and folds its
spawn event. No detector reset occurs. The experiment does not prove the
whole-program `runProgramSetupM`/frontend admission of these fixture inputs;
`execProg` is the existing lower-level driver entry. The channel fixture's
initial store supplies an open, empty, capacity-zero channel. This is an
input condition, not a theorem about `make` or package initialization.

### Checked disjoint-memory execution

`Concurrency.Example` starts with Boolean roots x=0 and y=1, both false.
The parent spawns a child that writes true to y. Tape `[0,1]` first selects
the parent at the spawn-completion boundary, clearing its flag. The parent
reads x while preparing a print; the print-apply boundary then selects the
child. The child writes y and terminates. The parent resumes, prints its
saved false value, reads x again, and prints false again.

`accepted` is an existing `PoolPrefix` of exactly 25 iterations, including
the boundary-clear step. `labelled` projects it to existing `StepsML`.
`actual_driver` and `entry_driver` prove `execProgLoopOut`/`execProg`
completion; `one_less_fuel` proves fuel exhaustion at 24, even though both
prints have occurred. `finished` checks the cost-zero terminal
classification. `exact_events` retains the complete attributed memory/HB
trace, scheduling records, and who stepped at every iteration.

`first_read` and `second_read` consume `ReadOnlyExpr.variable` through
`variable_phase_pool`. The latter retains arbitrary values, continuations,
environments, stores, thread indices and scheduler slots. Its pool guards
are explicit `Ordinary` premises, all derived at both concrete use sites.
The phase's label is recovered using the existing read law and pick
uniqueness; the pool prepends its scheduling record rather than deleting
choices. `variable_no_switch` proves that the unflagged read source itself
cannot switch goroutines. We test a boundary **between** reads, not an
interleaving inside a read or arbitrary assignment.

`child_write` uses `write_root`; `preserved_read` uses
`read_after_disjoint_write`, derived from `write_support` and `read_root`.
This establishes heap locality separately from pool thread framing. Its
domain is distinct roots; different interior paths under the same root
are not covered. `boundary_and_change` checks the suspended parent source,
the actual scheduler menu and y's changed value.

### Checked rendezvous and HB probe

`Concurrency.Sync` starts at the same singleton driver shape. The child
writes true to x, then sends on the unbuffered channel; the parent receives
and then reads/prints x. Tape `[1]`, including the default draws after it
is exhausted, produces exactly 38 iterations. `accepted`, `actual_driver`
and `entry_driver` prove the detector-checked prefix and actual driver
result. `exact_choices` retains the three L1 draws and the post-op draw;
the two flag clears are included in the count.

`actual_pair` is the real step at index 29, attributed to sender 1 with
`.paired 0`. Its trace is the channel-object entry read followed by
`.hb (.rendezvous 0)`; no synthetic accesses are inserted. The prefix proof
composes this exact step with the preceding and following driver steps.
`detector_pair` checks the actual detector fold. `transfer_boundary`
instantiates the compiled `TransferBoundary` obligation: the sender's old
clock is pointwise below the receiver's post-clock. `paired_flags` checks
that both controls change, the issuer gains `postOp`, and the receiver has
no completion flag. `post_handoff_read` reuses the public read phase with
the changed true value; `detector36` proves detector acceptance at that read.

`read_before_handoff_rejected` is a negative detector probe at the reachable
state immediately after the child's write (prefix length 13). A hypothetical
parent read there is rejected. It is not asserted to be a schedulable pool
step. The stronger negative control immediately before pairing remains the
named proposition `PrePairRejection`, for the reason below.

## Trust finding and remaining ordering contract

At this pin, `GoLean/GoCore/Ops.lean:2698` derives `Ord` for recursive `Loc`.
The toolchain generates opaque `GoLean.GoCore.instOrdLoc.ord`, with a
`DefinitionSafety.partial` implementation named
`GoLean.GoCore.instOrdLoc.ord._unsafe_rec`. Despite its name, that
implementation is not classified `DefinitionSafety.unsafe`. There are no
kernel-visible comparison equations. `Race.shadowSet` uses this comparator
to insert or replace shadow entries. An axiom-only scan reports no axioms
for the opaque constant and therefore misses this obstacle.

`Concurrency.RootComparatorContract` compiles the missing
root-comparison law without assuming it. `Obstruction` also checks the
opaque/partial declaration classification. Checkpoint `69442fc1` records
the discovery. No runtime counterexample or detector misbehavior is claimed:
the executable comparator returns the expected order in the probes. The
finding is the missing transparent total definition/checked ordering
contract on a load-bearing detector operation.

Both positive executions avoid assuming that contract: detector checks
split over every possible result of the relevant opaque comparisons. The
resulting acceptance proofs retain the resulting shadow states, rather
than replacing them with an idealized sorted map. `equal_comparison_loses_rejection`
proves a **conditional countermodel** for `PrePairRejection`: if the opaque
comparison of roots 2 and 0 returns equal, insertion of the channel-handle
read overwrites the old x entry and the later hypothetical read is accepted.
That premise is not proved or used by either positive execution. A faithful
ordering contract must exclude it before proving general shadow-history
preservation or ownership-to-detector safety.

The closure scan additionally reports 17 partial implementations without a
transparent total parent: this comparator, derived `BEq Expr`/`BEq Stmt`,
and 14 derived representation helpers. These are reported findings, not
waived or repaired here. The scan separately counts 170 compiler-generated
partial implementations **with** transparent total kernel definitions,
including `certify`; those do not have this opacity problem. The findings
are reproduced by the audit command, not stored as a raw inventory dump.

## Consequences for the downstream bridge

- Reuse `StepML.thread`, `stepML_sound`/`complete`, `stepML_frame`,
  scheduling/menu facts, `PoolPrefix` and driver bridges. No new pool relation
  is needed. `effect_reuse` lifts an existing `StoreEffect` with its actual
  label once the ordinary-step guards and operation premise are supplied.
- `StorePath`/`ReadOnlyExpr` are store-uniform recipes for individual steps.
  Ownership must re-establish their read facts at each resumed step. The
  disjoint-root example supplies a concrete preservation argument; the
  rendezvous example instead permits a changed read. A stored pre-phase
  fact is not automatically stable under interference.
- `StoreEffect` and `OrderedWrites` retain aliases and successive actual
  stores. Their sequential compositionality carries over locally, but a
  whole-path pool lifting still needs source-by-source scheduling and
  interception obligations. We have not proved an arbitrary-path lifting,
  same-root interior frame rule, or locality from an access trace alone.
- Spawn is `StepML.spawn`, not an ordinary `stepFn` step: evaluate operands
  in the parent, enter the child's frame, append at the old pool size,
  record the spawn HB edge before child-attributed entry reads, and flag
  the parent. `stepML_spawn` and `stepML_frame` already state structural
  facts. This fixture has no child parameters, entry reads or entry panic;
  general frame allocation, captured pointers and panic paths need their
  own bridge cases.
- Rendezvous updates two existing controls in one pool step. An ordinary
  Iris fork field alone cannot encode that paired update. `pair`/`pickPair`,
  `applyPairing`, the partner exception in `stepML_frame`, and
  `stepML_paired_trace` must inform the downstream decomposition. This probe
  discards the received value; target delivery, selects, buffered handoff,
  waiter choices and lock operations remain untested.
- The state interpretation must account for shared heap, goroutine
  identities/controls, detector clocks/shadow/channel state and the
  attributed observed history. The current sequential adapter's
  `Store × history` and ordinary-step lifting are not a concurrent adapter.
  Preserve output, pick and attribution channels even for locally pick-free
  or store-preserving phases. Downstream owns Iris resources, masks,
  invariant opening, history fragments, lifting and adequacy.
- Waiting is not deadlock: the parked receiver here has a runnable sender.
  Use `PoolDeadlock` and the driver's classification. Main exit, an abort
  tombstone, the L5 exit window, races and refusals must remain visible;
  the whole pool does not finish simply when a chosen worker finishes.
- No NPDRF converse is used. At this pin `NPDRFReduction` is deprecated as
  false as stated; the proved `reachesM_le_fine` only embeds registry-point
  executions in the finer relation. Neither successful run supports a
  general sequentialization or observational-equivalence claim.

Reference constraints read: the supplied 2026-10-14 brief; the logic lane's
`RelationalCodeX/Lifting.lean`, experimental `GoLeanIris/Logic/Language.lean`,
CLDD §5.9 and relational note P12. No peer files or build state were written.

## Validation and reproduction

From `experiments/2026-10-14-concurrency-compatibility`:

```sh
LEAN_NUM_THREADS=2 capped lake build
LEAN_NUM_THREADS=2 capped lake env lean Concurrency/Audit.lean
LEAN_NUM_THREADS=2 capped lake env leanchecker --fresh --verbose Concurrency.Audit
```

The experiment has its own Lake package and depends by relative path only
on this worktree's immutable baseline sources. Both its `.lake` and the
parent worktree's `.lake` are private to this lane; no shared writable cache
is attached. `sample%` uses Lean's proof-producing CBV normalizer to expose
witness data; the acceptance theorems separately check the equations.
`certify_sound` produces the existing `PoolPrefix`, checking live driver
fronts, `stepMulti` and `raceUpdate`; it refuses terminal fronts instead of
approximating the exit window. It is proof tooling, not a replacement pool
semantics. The two executions reach terminal classification only at the end.

Fresh build and standard-axiom checks passed (20,349 declarations in the
experiment/import closure at implementation freeze; headline theorem
axioms are printed individually). The implementation/opacity report is
**FAIL with 17 findings**, as above. This failure is not reclassified as a
pass by the successful theorem checks. Kernel replay and the fresh
independent review are recorded at handoff below.

The original whole-trace `decide` proof construction was cancelled after
105 seconds (Lean exit 143), with a snapshot ref taken first. It was a
failed validation attempt. The replacement normalizes witness data and
proves detector acceptance by cases, with small checked prefix segments;
subsequent experiment builds take seconds. No native decision bypass is
used. Raw probe output, error logs and build products are disposable.

The audited baseline was rebuilt for this import closure. Its full corpus,
Go frontend tests and `scripts/ci --diff` were not rerun; no runtime code
changed and this experiment is not a main-path gate. Previous baseline
coverage is reused as baseline evidence only, not freshly recertified here.

## Handoff

Final validation on 2026-10-15: the isolated `lake build` passed (69 jobs),
the standard-axiom audit passed for 20,349 declarations, and
`lake env leanchecker --fresh --verbose Concurrency.Audit` exited 0 on the
final built experiment and its recursive import closure. The fresh replay
does not supply equations for opaque constants or repair the 17 reported
implementation findings. The implementation scan remains **FAIL**.

The [fresh independent review](2026-10-15_relational-concurrency-review.md)
examined implementation commit `ea1341cf20941c2c91d6811fab1099476e05d975`.
It independently re-elaborated both examples and the audit. Its medium
ordering-contract finding remains open and is raised for user/upstream
disposition. Both low wording findings are fixed and independently verified;
the only subsequent Lean edit corrects a documentation comment. The final
build, axiom audit and fresh replay above include that edit. Review text and
each disposition are recorded in the linked review.

Only experiment source, this stage record and its review are changed from
the audited pin. Disposable logs and isolated build products are removed at
handoff; the commands above rebuild them. Retain the reviewed branch and
worktree. No runtime/public-API change, merge, push, live repin, peer write
or global-state change was made. The result is two checked selected
executions plus explicit outstanding contracts, not general concurrent
Iris compatibility or a main-path gate.
