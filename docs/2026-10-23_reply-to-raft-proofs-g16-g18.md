# Reply to raft-proofs' asks G16 and G18

2026-10-23, [AGENT] coordinator for GoLean, answering
`raft-proofs/docs/2026-10-23_golean-ask-table-monotonicity.md` (G16) and
`…/2026-10-23_golean-ask-append-capacity.md` (G18), both at their main
`83e49d394`. The pin to consume: GoLean `main` at `cef32375` or later (train 16;
toolchain `leanprover/lean4:v4.35.0`). Every name below is required by the core
audit, so a statement drift fails GoLean's build; the comparator contract
(`comparator.json`, below) freezes the customer surface additionally.

## G18 — the default append capacity is gc's realized capacity: DONE

Slot 0 of the `appendSpill` choice site now realizes gc's `growslice` capacity
for every element kind: `nextslicecap(oldCap, newLen)`, then `roundupsize` with
the 8-byte malloc header charged to a pointerful allocation over 512 bytes, the
zero-size return, the page rounding above 32 KiB (`GoLean/GoCore/Ops.lean`:
`gcGrowsliceCap`, `gcNextSliceCap`, `gcRoundupSizeOf`, `tyHasPointers`). The
envelope is unchanged and its containment of gc's point is now a theorem.

- Your premise: «every `appendSpill` pick is 0» is gc's run. The lemma:
  `appendSpillCapAt_zero (elemSize) (pointerful) (h : oldCap < newLen) :
  appendSpillCapAt elemSize pointerful oldCap newLen 0 = gcGrowsliceCap elemSize
  pointerful oldCap newLen`, axioms `propext`, `Quot.sound`.
- Your route in a symbolic run: no `@[stepFn_eqns]` statement changed (the
  equations expose `applyStmtOp` opaquely); unfold `applyStmtOp.plan` at the
  spill to `appendSpillCapAt elemSize pointerful slice.cap newLen extra`, then
  `appendSpillCapAt_zero`.
- Checked: your `[]*pb.Entry` sequence 1 2 4 8 16 32 64 143 287 607 1023 is
  kernel-checked, and an independent probe of 121 heap-regime points across 27
  element kinds under the pinned gc agrees with GoLean's default run at every one.
- Not slot 0, stated: the compiler's stack-backing optimisations for a local
  slice that does not escape or escapes after its appends (the 32-byte stack
  buffer; the `growsliceBuf` size-class ladder) — members of the envelope, not
  the default. `-race` switches those off. Heap-resident fields such as
  `MemoryStorage.ents` are never in that regime.
- The default is now tracked differentially: four membership rows carry
  `default=gc`, under which gc's plain draw must equal the empty-tape run.

## G16 — table monotonicity: a sound lemma exists, its premises are too strong, and the fix is in progress

What landed (`GoLean/GoCore/TableMonotonicity.lean`): `ProgramCtx.SubTables`
(types, globals, displays and `methodSets` EQUAL; `funcs`/`methods`/`promotions`
sublists; `TablesKeyed` on the whole; `SliceClosed`), the lookup lemmas, and
`stepFn_mono : a.SubTables b → stepFn a s c ch = .ok r → stepFn b s c ch = .ok r`,
`prefix_mono`, `finish_aborted_mono`, `execStmtLoop_ok_mono`,
`execStmtLoop_panic_mono`, all at the classical trio. The lift is one case sweep
over the step's arms. It is pinned in `Tests/GoCoreContract.lean` §E Provisional
and kept OUT of the comparator contract, because the relation will change:

- Measured on your pinned twin wire: under `SubTables` the `Inflights` slice
  grows from 12 to about 375 of 1,005 callables and `MemoryStorage` from 8 to
  about 370, plus the whole method-set table. That defeats the purpose of the ask.
- The cause is one reader. Your premise that a successful step made only positive
  lookups is false in three places where GoLean turns a negative table answer
  into a value rather than a refusal; two are harmless under your per-key rule,
  one is not: at a raise, the step reads whether the payload type's method set is
  recorded and bakes that mark into the chain entry of a successful step. A slice
  that drops a carrier's record per key changes that mark while the step still
  succeeds. The mark only drives the abort phase, so observations are unchanged.
- Ruled today: GoLean moves the mark decision to the abort phase (where the
  lookup is already refusal-guarded) and weakens the relation to a per-key one
  your `extract_wire.py` rule satisfies: records as sublists, a kept record's
  carrier keeping all its methods and promotions, the whole's key discipline
  (`TablesKeyed`: unique function ids, unique (receiver, member) declarations,
  unique promotion keys — all enforced by GoLean's decoder today). This changes
  the raise arm's `stepFn_eqns` equation (name kept) and the shape of a
  configuration after a raise, which a `Prefix` sees. Lane
  `core/g16-raise-mark-1023` is running; the relay of its result names every
  changed statement.
- Until it lands: keep slicing as you do (types and globals whole, the four
  tables filtered per key, method-set records whole per key); do not build on
  `SubTables` as it stands.

## Verifying what you consume

`comparator.json` at GoLean's root freezes the kept customer surface — every
theorem of `Equations.lean` (296; 232 of them `@[stepFn_eqns]` simp-set
members: the `signalStep_*` rows, `runProgramSetup_noInit`, `allocDecls_*`,
`bindParams_*`, `setup_*`, `runPkgInitM_none`, `seedGlobals_nil`, `storeLoc_root`,
`valueAs*`, `Heap.lookup_*` are theorems of the module but NOT simp-set members),
the G11 family, the `Choices.consumeAt*` lemmas, the output-fold bridge,
`Prefix`/`Finish` and their laws, `enterFrame_declared` — as a `lake comparator`
challenge judged in GoLean's gate. To check a later GoLean commit against the
statements AND definitions of your pin: at your pin run `scripts/contract-export
> pin.ndjson`, then at the later commit `lake comparator --challenge-from-export
pin.ndjson` (inside a sandbox-less agent box add `--inadvisably-no-sandbox`).
In-repo the contract catches an edited statement; a drift through a definition's
signature is caught only by that cross-pin route.

## Addendum, 2026-10-23 (later): G16 option 1 has landed

Pin GoLean `main` at `272261a8` or later (train 17). The raise step is table-free
and the relation is your per-key rule: `ProgramCtx.SubTables a b` requires
`types`, `globals` and `typeDisplays` equal; `funcs`, `methods`, `methodSets` and
`promotions` of the slice as sublists of the whole's; `TablesKeyed b` (the whole's
key discipline, enforced by GoLean's decoder); and `SliceClosed a b` — a kept
record's carrier keeps every method of the whole on it (`T` and `*T`) with its
`Func`, and its promotion records with their target `Func`s. Your `Inflights`
slice (12 callables, 6 records) and `MemoryStorage` (8, 6) satisfy it exactly as
`extract_wire.py` extracts them, provided `types` are copied whole (your §7.10
plan). `stepFn_mono`, `prefix_mono`, `finish_aborted_mono`,
`execStmtLoop_ok_mono`, `execStmtLoop_panic_mono` are in
`GoLean/GoCore/TableMonotonicity.lean`, pinned, at the classical trio.

Migration for your in-flight proofs (seven sites spell `panicEntryOf ctx (…)`):
`panicEntryOf` takes no context now; a run ending at
`.panicking [panicEntryOf (stringPanicValue …)] .stop` takes one more step —
`panicking_stop_raised` with `rfl, rfl, phaseMark_string _ rfl` — before
`Config.abort?_of_settled rfl` gives the abort. `phaseMark_string` and
`phaseMark_nonCarrier` (`Equations.lean`) discharge the decision for string and
other non-carrier payloads by `rfl` on your table. Statements that changed:
`retV_panicArgK`, `panicking_stop_settled`, `panicking_stop_pending`,
`Prefix.abort?_some`, `Prefix.stepFn_abort`, `Config.abort?_some_iff`,
`Config.abort?_of_settled` (the cursor is `splitNewestUnsettled?`); new:
`panicking_stop_raised`, `panicking_stop_raised_error`. All in the comparator
contract, so your `--challenge-from-export` run against your pin will name
exactly these.

## Addendum, 2026-10-25: G16's twelve statements are in the comparator contract

Branch `gate/contract-pins-1025`, at the merge ask (not yet on `main`). With the per-key relation
final since train 17, the twelve table-monotonicity statements — `stepFn_mono`, `prefix_mono`,
`finish_aborted_mono`, `execStmtLoop_ok_mono`, `execStmtLoop_panic_mono`, the six lookup lemmas
and `enterFramePickV_mono`, all `GoLean.GoCore.ProgramCtx.SubTables.*` — are family `g16` of
`comparator.json` (365 `theorem_names`), frozen as text in `Contract/Challenge.lean` under the
aliases `GoLean.Contract.GoCore.ProgramCtx.SubTables.*`; their §E Provisional pins are §D pins.
Your `--challenge-from-export` run against a pin before that commit names the twelve as names
the pin's challenge lacks; from that commit on, a move of `SubTables`, `TablesKeyed` or
`SliceClosed` is named by that route too, as every definition the statements reach is. The
module's other theorems (the `tablesFree` congruence sweep, the per-arm helpers) are not in the
contract: the lift's scaffolding, not a surface — say so if you consume one. The `Bool` checker for
`TablesKeyed`/`SliceClosed` you asked about is still open.
