# Reply to raft-proofs' ask G21: the normal form is shape-checked, the spill is budgeted

2026-10-27, [AGENT] lane `core/g21-normal-form-spill-1026` for GoLean, answering
`raft-proofs/docs/2026-10-26_golean-ask-normal-form-and-spill-budget.md` (G21, at your
`bad919b0` pin; relayed by the [USER] 2026-10-26). The pin to consume: GoLean `main` at
`91cd6c92` or later (toolchain
`leanprover/lean4:v4.35.0`). Earlier replies: `docs/2026-10-21_reply-to-raft-proofs.md`
(G9–G11), `docs/2026-10-23_reply-to-raft-proofs-g16-g18.md` (G16, G18),
`docs/2026-10-26_note-to-raft-proofs.md` (G19, BUG-131, BUG-132). Both halves of G21 are
done; no comparator-contract statement changed (`comparator.json` still freezes 385
statements and `scripts/gen-contract --check` is green with no regeneration), and no row of
the differential corpus changed its answer.

## G21 (1) — `isNormalForTyTy`'s fall-through is closed: DONE

`isNormalForTyTy` (`GoLean/GoCore/Ops.lean`) ended in `| _, _ => true`; the five `Ty`
constructors that reached it are exactly `.bool`, `.string`, `.slice`, `.map` and `.pointer`
(every other constructor — `int`, `float`, `array`, `chan`, `funcType`, `interface`,
`defined`, `unsupported`, `sync` — already had an arm). Each now has its own arms, and the
normalizer's matching fall-through (`normalizeValueForTyTy`'s `| _, value => return value`)
is replaced arm for arm, so the two stay in lockstep as the chan and sync arms already were.
Which constructors are legitimate at each type was measured, not guessed: every producer was
read (`defaultValueTy`, the typed nil literal `.nilLit`, the conversion arms, the seed loader
`Seed.lean`, the wire decoder's nil typing in `tools/nativefrontend/emit.go`), and the full
corpus ran unchanged.

| Type | `isNormalForTyTy` admits | the normalizer | evidence |
|---|---|---|---|
| `.bool` | `.bool _` | `.bool b` unchanged; else `stuck "expected bool value, got …"` | `defaultValueTy .bool = .bool false`; the seed loader's `.bool` arm; no other producer |
| `.string` | `.string _` | `.string s` unchanged; else `stuck "expected string value, got …"` | `defaultValueTy .string = .string empty`; every string operation builds a `.string` |
| `.slice _` | `.slice _` | `.slice sv` unchanged; a raw `.nil` becomes `.slice {base := none, offset := 0, len := 0, cap := 0}`; else `stuck "expected slice value, got …"` | `defaultValueTy`, `.nilLit (some (.slice _))` and the conversion arm (`[]T(nil)`, delta-review D3) all produce that nil slice; the frontend types every untyped `nil` in a slice slot (`emit.go`, the `*types.Slice` case) |
| `.map _ _` | `.map _` | `.map mv` unchanged; a raw `.nil` becomes `.map {base := none}`; else `stuck "expected map value, got …"` | the same three producers at map type; the frontend's `*types.Map` case |
| `.pointer _` | `.addr _`, `.nil` | both unchanged; else `stuck "expected pointer value, got …"` | `defaultValueTy .pointer = .nil`; `.nilLit (some (.pointer _)) = .nil`; the seed loader's `ref` resolves to `.addr`, its `nil` only at pointer types; raw nil IS the pointer representation (the conversion arm's note) |

Design points taken ([AGENT], 2026-10-27; each is one arm to switch if the owner rules
otherwise):

- **A raw `.nil` at a slice or map type is canonicalized, not refused.** This mirrors the chan
  arm (a raw `.nil` reaching a channel slot becomes the nil channel) and the conversion arm's
  rule for `[]T(nil)` / `map[K]V(nil)`: the machine's own nil representation is what the typed
  nil literal and `defaultValue` produce. The check side is unaffected: raw `.nil` is NOT
  normal at those types (so your `HeapOK` excludes it), only the normalizer's output is. No
  corpus run stores a raw `.nil` at a slice or map type (the frontend types them), so the
  choice is corpus-neutral; refusing instead would also be corpus-neutral.
- **The `.interface` arm is unchanged** (`| .interface _, value => return value` / `true`): it
  was not a fall-through, your ask did not name it, and closing it is a different question
  (an interface cell holds `.nil` or an `.interface dyn v` box whose `v` should be normal at
  `dyn` — a recursive descent at the dynamic type, not a constructor check). Say if you want
  it.
- **`Ty.stepDown` keeps its identity arms at the five types.** A path write INTO a
  `[]T`-declared cell is impossible under `HeapNormal` now; on a non-normal store the leaf
  normalization at the descended type refuses by name («expected slice value, got …»).

Re-proved with their statements unchanged (`GoLean/GoCore/StateWf.lean`):
`isNormalForTyTy_sound` (check true ⇒ the normalizer returns the value unchanged),
`normalizeValueForTyTy_isNormal` (the normalizer's output is normal — the raw-`.nil` cases
are the two new sub-cases), `normalizeValueForTyTy_locSup`, and the `writeAt_isNormal_array` /
`writeAt_isNormal_struct` congruence arms (at the five types no `.array`/`.struct` root is
normal, so those arms close by contradiction). The strictness and no-panic proofs
(`StepErrors.lean`, `StepFnFacts.lean`) are generic over the arms and needed nothing.

Pins. `Tests/GoCoreContract.lean`'s §A pin `address_bound_admits_ill_typed` asserted the
weakness (a `.bool` cell holding `.int 7` is `StateWf`); it is NOT in the comparator contract
and is inverted on the same store as `ill_typed_cell_refused : ¬ StateWf … illTyped`. The
fix-round-F3 pin `slice_cell_path_write_array` (a `[]int`-declared cell holding an array,
written through) is `slice_cell_path_write_refuses` plus `slice_cell_not_normal`; the
`iface_cell_path_write_*` pins are unchanged. `Tests/GoCoreEval.lean` `g21NormalFormTests`
pins, per type, the admitted constructors, the refusals by name of every other constructor,
the raw-`.nil` canonicalization, `HeapNormal`/`StateWf` on the three heaps your ask named (a
`.bool` cell holding an int; a `*uint8` cell holding a struct; a `[]int` cell holding an
array — all refused) and on a heap of the five zero values (admitted), `Store.alloc`'s
refusal at the cell's birth, and the path-write refusal.

For your proofs: the three counterexample heaps of DL-294 are excluded by `HeapOK` itself
now; `StateWf` is still `Store.locSup σ ≤ σ.nextAddr ∧ HeapNormal ctx σ`, decidable, and the
`stepFn`-level `StateWf` preservation theorem is still not started (your per-arm fallback
stands).

## G21 (2) — the append spill and the string conversions are budgeted: DONE

**The spill.** `appendSpillFootprintCheck ctx elem newLen newCap` (`GoLean/GoCore/Machine.lean`,
beside `sliceCapBudget`/`arrayFootprintBudget`) refuses `newCap × tyLeafCount(elem) >
arrayFootprintBudget` by name. Its place in `applyStmtOp.plan`'s spill arm, as you asked:
AFTER gc's `growslice: len out of range` panic (a request gc rejects keeps gc's panic — pinned
with crafted operands, since no gc-buildable program reaches that band), AFTER the `appendSpill`
consult, on the REALIZED capacity `newCap` (what is built), BEFORE the backing is built. The
pre-consult mirror `appendSpill?` and the consumption facts are untouched (`some` ⇔ the consult
happens, as before). No reason to place it before the consult was found; the reason to keep
it after is yours — `AllocOK` preserved by every allocation arm needs the bound on what is
BUILT — and its consequence is stated here plainly: the refusal is a function of the pick,
exactly as the allocation is. The same append can answer at the default pick (gc's realized
capacity) and refuse at an envelope pick whose realized backing is over the budget;
`g21SpillBudgetTests` pins one such pair (`[1<<20]uint8` rows, cap 1 + 1: cap 2 at the default
pick answers, the pick realizing cap 32 refuses). The text, on `make`'s template:

```
append([]T, …): a grown slice backing of 41112 elements (len 32768) of 1024 scalar elements
each materializes 42098688 scalar elements, past the interpreter's footprint budget for an
append spill (16777216 elements, arrayFootprintBudget — the realized capacity after gc's
growslice panic, the bound the make site refuses at; BUG-131 cost boundary, refused by name)
```

status `unsupported`, cause `append-footprint-budget` (`scripts/machine-causes.tsv`).

**The conversions** (your local space, (2) of BUG-131's scope sentence). `convFootprintCheck
kind n cap` refuses `cap > arrayFootprintBudget` (one leaf per byte or rune) inside
`convCapApplyAt`, after the `convCap` consult and before the backing. One thing had to move
for the guard to mean anything: the consult width `convCapWidth` was computed from
`(convElems kind value).size`, which materialized every element before any check; it now reads
`convCount kind value` (the byte count, or the code-point count), `convElems_size` relates the
two, and `convCapApplyAt` builds the elements only after the check. Text:

```
[]byte(s): a conversion backing of 16777217 elements (len 16777217) of 1 scalar element each
materializes 16777217 scalar elements, past the interpreter's footprint budget for a string
conversion (16777216 elements, arrayFootprintBudget — the realized capacity of the fresh
backing, the bound the make site refuses at; BUG-131 cost boundary, refused by name)
```

cause `conv-footprint-budget`.

**The rest of the local space**, each measured:

| door | verdict |
|---|---|
| `copy` | builds no backing — `Mem.loadRun`/`Mem.storeRun` on two existing slices, each already bounded at its own birth; nothing to guard |
| a huge slice literal, and `append` of one | a literal lowers to `Stmt.makeSlice` with its length as an `intLit` (`NativeToIR.lean`'s `slice-lit` arm and the unseq lowering), so it meets the `make` site's count bound (`sliceCapBudget`, 1<<23) and footprint guard at its construction; an append of it is then an in-budget spill or the spill guard |
| `strings.Repeat` and the other `strings.Builder` paths | source-through: `Builder.Grow` is the overlay's `MakeNoZero(n)` = `append([]byte(nil), make([]byte, n)...)`, refused at that `make` (the count bound first) |
| `make(map…, n)`, `make(chan T, n)` | allocate nothing for the hint / the capacity (BUG-131's record) |

**The kill, reproduced at the base and refused at the tip** (on the base `6a65dd6f`'s binary
and this lane's, each under `capped`): `appendOverBudget` — `make([][1024]byte, 1<<14)` (2^24
leaves, exactly the budget, admitted) then `s = append(s, s...)` — KILLED under
`CAPPED_MEM_MAX=2G` in 3.3 s where the same make alone (`make-at-budget`) answers under 2G in
1.3 s; at the tip the refusal above in 1.3 s. `[]byte(s)` of a 2^26-byte string KILLED under 4G
in 4.0 s where the string alone answers in 0.3 s; at the tip the refusal in 0.3 s. The rows
one byte past the budget RAN at the base under 2G (2.9 s / 8.9 s): the budget is the stated
bound, the kill class begins higher.

**Rows** (`Corpus/coverage/exec/arrays/`): `materialization-budget-append/` —
`append-over-budget` (2^25 leaves, over at every envelope pick) and `append-grow-over-budget`
(the new LENGTH is exactly the budget, gc's realized capacity 16736 rows is over it: the
realized capacity is what is charged) RED BY DESIGN at gc's `ok`; `append-at-budget-spill` (a
spill whose realized capacity, 13232 rows, is inside), `append-small-elem`, `append-in-place`
PASS. `materialization-budget-conv/` — `bytes-over-budget`, `runes-over-budget` (2^24 + 1) RED
BY DESIGN; `bytes-in-budget`, `runes-in-budget` PASS. All on BUG-131's Cases line; the record
there has the measurements.

## Verifying what you consume

No statement of `comparator.json` changed. Definitions whose BODY changed, which your
`--challenge-from-export` run against `bad919b0` will name (as it names every semantic
change): `normalizeValueForTyTy`, `isNormalForTyTy` (hence `HeapNormal`, `StateWf`),
`applyStmtOp.plan` (the spill arm), `convCapApplyAt`, `convCapWidth`; new: `convCount`,
`appendSpillFootprintCheck`, `convFootprintCheck`; `sliceCapBudget` and
`arrayFootprintBudget` moved earlier in `Machine.lean` with their values unchanged. Take a
fresh export at or after the landing commit; the route is the one in the 2026-10-26 note.

## Open on our side

- The `.interface` arm of the normal form (above): on request.
- The `stepFn`-level `StateWf` preservation theorem: not started.
- The Bool checker for `TablesKeyed`/`SliceClosed` (G16): on request.
