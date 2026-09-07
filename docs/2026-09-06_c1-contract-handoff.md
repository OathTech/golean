> **Landing header ([AGENT] landing chunk L6 `land/sprint-records`,
> 2026-09-07).** Charter §4's C1 deliverable, tracked here VERBATIM from the
> sprint worktree (`.claude/worktrees/typed-consumer-sprint/docs/2026-09-06_c1-contract-handoff.md`,
> 9,959 bytes, mtime 2026-09-06 15:48), where it was UNTRACKED (landing
> audit B R6/R16). It is a **DRAFT that was never refreshed**: the sprint
> was paused (`docs/2026-09-06_typed-sprint-pause-state.md`) before the
> "Refresh required at sprint closure" section could be executed, and the
> representation it describes did NOT land — O4 (B7 `ProgramCtx`/`Store`
> and the I1 companion) is UNIMPLEMENTED on main (`grep ProgramCtx GoLean/`
> → one deferral comment, `GoLean/GoCore/Platform.lean:19`; the B7 work is
> on branch `typed-context-store` @ `ca1e01d5`, the I1 envelope on
> `typed-i1-envelope` @ `3d49e9e9`, both unmerged and unreviewed by the
> landing). Its "final repaired `uintptr`" is the HELD chunk L5 (landing
> plan §2.5, [USER] decision D1 pending). The pause-state record lists the
> root corrections still owed to this draft ("C1 handoff draft and
> remaining obligations"). Read it as the sprint's inventory of the memory
> boundary C1 will receive, not as a description of main.

# C1 handoff from the typed-consumer sprint

[AGENT], 2026-09-06. **DRAFT: refresh against the final integration tip.**
This records the concrete memory boundary and obligations identified during
the sprint. It does not authorize C1 implementation or assert that B7/I1 is
complete. The inspected B7 representation is the 413-input structural
checkpoint `69a7710a87506fb3d4df77e5387cd8c2d56da8eb001c5d6c4da33b8d93275ec3`,
based on `ca1e01d5`, with original runtime basis `761d4e28`.
The later runtime repairs, I1 context facts and final cleanup must be folded
into this handoff before the closing packet is complete.

## Contract C1 receives

`ProgramCtx` contains `program : Program` and `platform : Platform`, with
the shipped default `gcAmd64`. Its projections supply types, functions,
methods, method sets, displays and globals. These are immutable inputs;
constructing the context supplies no admission evidence. Context-only
operations no longer take an unused Store argument.

`Store` contains only `heap : Array HeapCell`. A root address is its dense
array index; `nextAddr` is the array length. `allocCell` appends a cell;
`updateCell` requires an allocated index and preserves its existing failure
diagnostic. `HeapCell` distinguishes declared values, map payloads with
monotone per-map entry identities, and channel payloads with buffer,
capacity and closed flag. Field/index locations are paths inside a value
root, rather than independent heap keys.

Configuration, goroutine pool, race state, choices and output remain outside
Store. The driver folds output events in order. Choice consumption and the
remaining tape are part of the semantic contract, including in the
executable/relation correspondence. A memory interface must preserve these
components as well as values and heap contents.

## Operations and access-reporting sites to carry together

The table is an entrypoint inventory; the next implementation must generate
an exhaustive constructor/arm inventory at its actual starting commit.

| Family | Current semantic entrypoints | Existing access/detector seam | Required preservation |
|---|---|---|---|
| Root allocation and replacement | `Store.allocCell`, `Store.alloc`, `Store.updateCell`; `Heap.lookup` | Fresh allocation is excluded from current user-memory footprints | Dense addressing, freshness, old cells, exact errors and allocation bounds |
| Path reads and writes | `Ops.loadLoc`, `Ops.storeLoc`, chain/target resolution | `projChainTarget`, `targetWrite`, `storeTargetAccess`, `stepAccesses` | Nil/bounds/shape behavior, selected path, unchanged unrelated locations, normalization and failure order |
| Parameters, captures, results | `bindParams`, `loadMany`, actual frame/setup and result-root operations | Call/defer entry dispatch; frame-exit result reads; later per-target `storeK` writes | Aliased capture identity, typed cells, readout roots and call/return access order |
| Arrays, slices and copying | `makeSlice`, `appendSlice`, `copySlice` application arms and their Ops helpers | `stmtOpAccesses`; existing private-step granularity and append spill choice | Overlap/alias behavior, capacity choice and residual tape, exact in-place/spill result and complete footprint |
| Map data | `mapPayload?`, `storeMapPayload`, `mapEntries`, `mapLookupValue`, `mapAssignValue`, delete/clear/range | `mapAccess`, RHS application, range entry and every `mapIterK` pick including final done-check | Entry identity/counter semantics, permitted iteration choices, live-map read and mutation conflicts |
| Channel data | `chanPayload?`, `storeChanPayload`, send/receive/close/select and pool rendezvous | Existing channel synchronization and HB rules in Multi/Race | FIFO/capacity/closed state, wakeup/rendezvous choices, ordering and exact errors |
| Dynamic method entry | Dispatch/receiver adjustment and deferred-entry rules | `dispatchAccesses`, `deferEntryAccesses` | Receiver dereference when required, call/capture order and zero-argument cases |
| Atomics and synchronization | `atomicPlan`, atomic and sync application/pool rules | Atomic access kinds, `syncEntryKinds`, `syncReleaseTailKinds`, race/HB updates | Operation kind, concrete primitive words, success/failure branches and release-tail ordering |
| Private step to pool event | `stepFn`, total `Step`/`StepE`/`StepM` premises and drivers | `strictOpAccesses`, `stmtOpAccesses`, `stepAccesses`, race update | Exact ordered trace at the existing step boundary; scheduling, output and remaining choices unchanged |

The map's internal entry IDs and the heap's path representation are semantic
inputs to their respective operations. Renaming, coarsening or discarding
them is a separate change with its own proof obligation. Channel and sync
events already have dedicated ordering rules; a plain read/write list does
not replace those rules.

## Invariants the customers actually consume

The Boolean and recovery profiles obtain initialized storage, valid bindings,
parameter/result cells and the runtime invariant from admission through the
actual program setup. Structural preservation covers control and
continuations as well as storage. Their normal readout uses the actual
result roots and `loadMany`; fuel exhaustion, panic and model refusal retain
distinct meanings. The recovery extension covers captured Boolean root
references, direct calls, LIFO defers and the effective direct-recover rule.

The Iris spike maps the actual dense heap to a finite root-cell map using
`heapToMap`. `get?_heapToMap`, `heapToMap_set`, `heapToMap_push` and
`heapToMap_fresh` connect ghost ownership to real lookup/update/allocation.
Fractional ownership supports framed reads; writes require full ownership.
Two deferred handlers share one owned result root. The customer currently
owns a whole cell, including its declared type and value. It provides no
rule for splitting distinct fields of one root into independent resources.

The context-indexed language fixes `ProgramCtx` in the expression/adapter
type. The customer no longer carries ghost context equality or reflexive
context-preservation fields. The separate context-mismatch negative must
remain rejected after C1. The semantic facade remains experimental: the
final migration inventory must enumerate constructor/representation uses
still needed by the adapter separately from the reusable public contracts.

`StateWf` supplies location/configuration bounds and allocator facts; it is
not a blanket proof that every raw stored value is canonical at its type.
Raw allocation currently does not normalize. The byte-store experiments
give an explicit counterexample to optimizing a whole-root normalization
without the necessary local canonical-backing fact. Any such optimization
must establish and preserve its fact at the actual caller and prove exact
erasure; it cannot be justified by calling the existing bounds invariant
"well-typed memory".

## Required C1 proofs and tests

The existing G-C1 ruling is the authority: prove
`accesses_eq_stepAccesses` arm by arm, then retire the table. Restate
`RacyFine` and `footprintsConflict` over emitted traces; discharge the I3
`step_det_of_choiceFree` obligation; rerun
`scripts/detector-soundness --select in-scope` with the HOLE cell still zero.
These are deliverables for the next block, not claims of this sprint.

1. Freeze the precise pre-C1 runtime and access table, including the final
   repaired `uintptr`, I1 admission/context and proved performance behavior.
   Generate the complete configuration and strict/statement/atomic/sync arm
   inventory from that source. An absorbing default is not arm coverage.
2. For each memory primitive, prove exact result/store equality after
   erasing the added trace, including failure order and raw-state domain.
   Establish a separate equation for its ordered semantic access trace.
   Distinguish implementation bookkeeping reads from Go-visible accesses
   with a documented semantic argument; filtering a trace to match the old
   table is not that argument.
3. Lift those equations through operand evaluation, target resolution,
   continuation/frame changes, private steps and pool scheduling. Preserve
   all legal choices and residual tapes. Carry output and terminal readout
   through the executable and relational drivers. Do not substitute a
   successful observed run for an all-successor theorem.
4. Check equality against every old access-table arm. If an arm is wrong,
   retain its smallest failing detector regression, record a detector BUG
   and independently review the repair before changing the comparison
   basis. Do not hide a changed access granularity inside equivalence.
5. Migrate both typed contracts and Iris fixtures. Recheck fractional reads,
   exclusive writes, aliasing, allocation freshness, call/defer order,
   context mismatch, actual output/readout, panic and zero-fuel controls.
   Retain dependency-origin audits with compiled unused-declaration poisons.
6. Run the full conformance/required slow train and complete detector scope
   at the final source. Preserve separate status, observation, choice and
   access-trace comparisons; report cached evidence and bounds explicitly.

Choice-free determinism needs a stated semantic condition and an exact
observation/remaining-choice conclusion. It does not justify erasing a
permitted Go choice from an evaluator helper. General concurrent adequacy,
field-splitting ownership, native promotion and reflection remain their
separately planned work.

## Refresh required at sprint closure

Replace the provisional representation basis with the accepted integration
commit; link the final claims/assumptions and adapter migration inventories;
record the final memory/footprint entrypoint hashes; account for any changed
I1 runtime-error context fields and byte-store APIs; and identify unresolved
detector bugs with their exact witnesses. The final closing review decides
the next charter and main merge separately.
