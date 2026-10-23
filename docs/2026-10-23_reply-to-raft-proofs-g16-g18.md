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
