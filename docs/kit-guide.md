# The Kit Guide — you are at X, use Y, copy fixture Z

**Read this first.** The kit is the shared proof library under
`proofs/GoLeanProofs/` — `StepKit`, `SliceMem`, `MapMem`, `StringMem`,
`MapLoops`, `FuelMeasure`, `Frame/Threshold`, `EntryEq`, and the
symbolic evaluator `Sym/*` — that carries the *structure* of a gallery
proof so an example only has to supply its own content. It is
**untrusted method**: everything here is proof-side, and **no kit name
may appear in a headline statement's closure** (form note
`docs/2026-08-12_example-spec-form.md` §12b). Additions follow the §12
active-abstraction loop — ≥2 landed consumers retrofitted in the
lifting commit, measured deltas, and every new public theorem lands
with its `#print axioms` pin in `proofs/Audit/Kit.lean` in the same
commit. This guide is indexed by **proof situation**, not by module:
find your situation, take the form, copy the named fixture. Fixtures
are cited by FILE, never by line — line cites drift. Where the guide
and a module docstring disagree, the docstring is the API of record;
report the drift. Records: `docs/wp-arc-log/` (this arc, `INDEX.md`
first), `docs/gallery-campaign-log/` (the 24-example campaign that
justified the library), `docs/2026-08-16_wp-library-design.md` (the
ten reasoning principles this index realizes).

---

## 0. THE ROUTING TABLE — find your situation

| you are at … | go to |
|---|---|
| the very start: `runFunctionWithContextM` at symbolic arguments | §1 Entry |
| one machine step you cannot make `rfl` swallow | §2 One step at a time |
| a heap that is a concrete front `++` an abstract tail | §3 Heap at a symbolic split |
| "every address at or above `na` is absent" | §4 Footprint |
| **every address in my run is a fixed constant** | **skip §3 AND §4** — see §3's precondition |
| a run of steps you want to cross in one lemma | §5 Segments (raw / option / evaluator) |
| a `[]uint64` in memory — read, measure, re-slice, store | §6 Values in memory: slices |
| a `map[uint64]uint64` — read, write, snapshot, model | §7 Values in memory: maps |
| a Go string — `len`, index, `+`, `s[lo:hi]` | §8 Values: strings |
| "this `uint64` is already its own normal form" | §9 Integer normal forms + bounds |
| ∀-input setup data the harness loop builds | §10 Setup families (∀-input data) |
| `append` — in place or spilling to a fresh backing | §11 Append / growth |
| the loop swaps two elements, or counts occurrences | §12 Swap / count surgery |
| a loop whose every iteration costs the same `c` steps | §13 Counted loop |
| a loop that can leave early, or whose iterations differ in cost | §14 Two-exit loop |
| a loop with no counter — its trip count is a MEASURE of the data | §14, the third class |
| `m[k]++` folded over a slice | §15 Map count loop |
| `for k, v := range m` | §16 Map range loop |
| a loop body that ALLOCATES (addresses shift each pass) | §17 Loop-local allocation → threshold frame |
| a function call your program makes exactly once | §2 (`stepFn_call_enter`) — **not** §18; see §18's precondition |
| recursion, or one callee entered at several placements | §18 Recursion / call span |
| stitching segments into one run, with the fuel arithmetic | §19 Composition |
| "this loop terminates" without a step count | §20 Termination |
| a total headline → the run-conditioned twin the user reads | §21 Readout |
| your proof is slow, or storming | §22 The disciplines |
| the kit has no form for you | §23 Honest limits |

## The shape of every gallery proof (why the sections are ordered this way)

1. **Entry** (§1) — from the machine's function-entry API to a named
   post-prelude state and a start `Config`.
2. **Segments** (§2–§5) — cross the run in windows, each conditioned on
   the executable facts (§6–§12) it needs.
3. **Loops** (§13–§18) — a schema takes the per-iteration segment as ONE
   hypothesis and does the induction for you.
4. **Composition** (§19–§20) — chain the phases, produce the fuel bound.
5. **Readout** (§21) — turn the total run into the statement a user reads.

---

## 1. Entry

`EntryEq` generates the whole opening: the post-prelude `ExecState`
def, the start `Config` def, and the entry equation, proved
`with_unfolding_all rfl`. **You never hand-write an entry dance.**

| you are at | the form | what you owe it | fixture (copy from) |
|---|---|---|---|
| a harness with scalar-integer parameters | `derive_entry_eq <thm> <prog> <func> <stateName> <contName>` | the lowered-program constant and the harness `Func` constant; you choose the emitted names | `Examples/Fib.lean`, `Examples/Gcd.lean` |
| the same, **and your segments are spelled as a record update over a threaded state — `xSt σ H na = { σ with heap := H, nextAddr := na }`** (the concrete-front style) | the SIX-ident **program-generic** form: `derive_entry_eq … <stateName> <contName> <base>` | additionally `base`, your program-as-empty-heap state constant (`vProg`/`rProg`/`ddProg` convention). The emitted state is then the record update `{ base with heap := …, nextAddr := … }`, so the bridge to your compositional spelling is a structural `rfl` rather than a whnf of the program constant | `Examples/TwoSum/Machine.lean`, `Examples/DedupAdjacent.lean`, `Examples/RunLength/Machine.lean` |
| a harness whose results are STRINGS | the same command — the string result-default arm is in (WP arc s2 item 6); it quotes `GoString.empty` | nothing extra | `Examples/StringReverse/Machine.lean`, `Examples/WordFreq/Machine.lean` |
| a harness the macro REFUSES | hand-write it, and record the gap | the macro fails closed on non-scalar parameters and on nested aggregate result defaults; `[3][3]uint64` results are the known refusal | `Examples/MatMul.lean` (the hand-written entry, with the layout rule stated) |

**Which of the first two rows is you?** The six-ident form buys ONE
thing: it keeps the record-update structure that a `xSt σ H na`
segment vocabulary is stated over. If your segments instead take a
fully abstract `σ : ExecState` and return it untouched (§22 rule 1 in
its strongest form), or take an abstract heap `h : Heap` plus a
footprint (§4), there is no record update to preserve and the FLAT
five-ident form is the right one — `Examples/Stein/Run.lean`,
`Examples/Gcd.lean` and `Examples/Fib.lean` are all flat-form modules,
and Stein is heavily footprint-style. "Program-generic" is not a
quality ranking; it is a match to your segment spelling.

The layout is COMPUTED, not probed: parameter cells at `0…p−1` in
`bindParams` order, result cells at `p…p+r−1` at their `defaultValue`s
in `allocDecls` order, one scope in reverse-declaration order. Before
emitting, the macro runs the equation at one concrete probe point
(all-args-1, generous fuel) and requires `.ok` **and** agreement — so a
mis-derived layout fails in milliseconds instead of in the kernel
(the `#eval`-before-`decide` rule, mechanized). It is a single-point
check of a symbolic statement; the final `rfl` is still what decides.

Downstream, the emitted equation hands off to `FuelMeasure`'s
`runConfig` glue (§19) and its continuation is chained onto
`StepKit.stepFn_call_enter` (§2). 28 invocation sites today.

## 2. One step at a time

`StepKit` API group 4. Use these where a step CONSULTS something a
`rfl` window cannot cross by itself — the heap, the program tables, a
choice. Every one is stated over an abstract `σ : ExecState` and takes
the executable fact as a hypothesis whose type pins both states.

| you are at | the form | what you owe it |
|---|---|---|
| one step, already known | `stepFnIter_one` | the `stepFn` equation |
| entering a call frame | `stepFn_call_enter` | `enterFrame σ fid args = .ok (func, env, locs, σ')` |
| leaving one | `stepFn_return_frame` | the frame shape |
| a strict operator (`+`, `<`, `len`, index, …) | `stepFn_strict_apply` | `applyStrictOp σ op args = .ok (out, σ')` — from §6/§7/§8/§9 |
| a store | `stepFn_store_step` | `storeTarget … = …` — from §6 |
| a statement operator (`append`, …) | `stepFn_stmtOp_apply` | `applyStmtOp … = …` — from §11 |
| a map assignment | `stepFn_mapAssign_apply` | the `mapAssignValue` fact — §7 |
| a variable read | `stepFn_var` | the env fact |
| `make([]uint64, n)` | `stepFn_makeSlice_u64_step` | the length fact |
| splicing a `seqn` block / popping a `seq` / a `block` | `stepFn_seqn_splice`, `stepFn_seq_pop`, `stepFn_block` | the continuation shape only |
| the map-range pick | `MapMem.stepFn_pick_bind` (+ `_value`, `_novars`) | the snapshot fact; it consumes ONE choice |
| operand plumbing | `storeTarget_addr`, `loadMany_one`, `loadMany_two`, `stepFn_init_seq`, `stepFn_storeK_nil`, `stepFn_snapshot` | — |

**Fixtures:** `Examples/WordCount/EmptyRun.lean` is the exemplar of the
program-generic conditioned form (82 s / 50.8 GiB → ~86 s / 1.9 GiB and
program-size-independent when restated this way);
`Examples/DedupAdjacent.lean` shows the everyday mix (store steps and
splices interleaved with raw windows); `Examples/SliceQueue.lean` and
`Examples/SliceStack.lean` show frame entry and exit.

**Nothing in `StepKit` iterates.** If the statement mentions a step
COUNT, it belongs to `FuelMeasure` (§19).

## 3. Heap at a symbolic split

`StepKit` API groups 1–2: a heap that is a concrete front `++` an
abstract tail `D`, and one cell under `Heap.set`.

**PRECONDITION — check this before reading the table.** You need this
section only if some part of your heap is ABSTRACT to a segment: an
input-dependent number of cells, a dead remainder `D` you refuse to
describe, or a growing front. **If every address in your run is a
fixed constant — the harness allocates a bounded, statically-known set
of cells and the loop body allocates nothing — you need NOTHING from
§3 or §4.** Concrete fronts reduce inside raw `rfl` windows, and the
lookups never become a proof obligation at all. Do not build a
symbolic split you do not have; it is pure cost.

**Negative fixture (copy this decision, not a lemma):**
`Examples/DedupAdjacent.lean` allocates one backing array before the
loops and nothing after, so every address is a constant; it uses
**zero** forms from §3 and **zero** from §4, and says so in its
address-layout block. Its heap fronts are concrete lists throughout.
The positive fixtures below all have a genuinely abstract region.

| you are at | the form |
|---|---|
| a lookup that lands in the front / the tail | `lookup_append_left`, `lookup_append_right`, `lookup_append` |
| a set that lands in the front / the tail / past both | `set_append_left`, `set_append_right`, `set_fresh` |
| walking a cons cell | `lookup_cons_ne`, `lookup_cons_self`, `set_cons_ne`, `set_cons_self`, `base_beq_false` |
| a one-cell heap | `lookup_singleton_self`, `set_singleton_self` |
| the cell you just wrote / a different one | `lookup_set_self`, `lookup_set_other` |
| two writes to the same cell / to different cells | `set_set`, `set_comm` (**presence-conditioned** — the obvious unconditioned form is FALSE; that is why it ships) |
| a write that changes nothing | `set_self_of_lookup` |

**Fixtures:** `Examples/WordCount/RangeGeneric.lean`,
`Examples/SliceQueue.lean`, `Examples/WordFreq/Scan2.lean`
(front+`D` throughout); `Examples/FibMemo/Rec.lean` for `set_comm`
with its presence hypothesis.

**Lint:** L2 fires on a full-heap `Heap.lookup (front ++ D) …`
hypothesis in a composite signature — state it D-relative (§22 rule 4).
L1 fires on unqualified `.base ⟨…⟩` inside a statement (§22 rule 5).

## 4. Footprint

`StepKit` API group 3 — the idiom for recursion, dynamic allocation
and choice-dependent layouts: state the segment over a fully abstract
heap and carry "everything at or above `na` is absent".

ONE predicate under two names: **`DeadFrom`** (a dead TAIL past a
concrete front) and its `abbrev` view **`FreshFrom`** (the WHOLE heap
of a footprint-style state). Algebra: `.mono`, `.push`, `.push2`,
`.push3`, `.set`, `.lt_of_lookup` on both.

| you are at | the form |
|---|---|
| the heap grew by one/two/three fresh cells | `FreshFrom.push` / `.push2` / `.push3` |
| you wrote an existing cell | `FreshFrom.set` |
| a weaker bound suffices | `FreshFrom.mono` |
| a successful lookup ⇒ the address is below `na` | `FreshFrom.lt_of_lookup` |

**Fixtures:** `Examples/Sieve/Machine.lean`, `Examples/FibMemo/Rec.lean`,
`Examples/Stein/Run.lean`, `Examples/WordFreq/Machine.lean` (the four
`FreshFrom` consumers); `Examples/TwoSum/Subject.lean` and
`Examples/WordCount/*` for the `DeadFrom` front+tail spelling.

**PRECONDITION — §3's, and it is the same test.** A footprint is what
you carry when the heap is abstract and GROWING: recursion, dynamic
allocation, choice-dependent layout. If your subject allocates nothing
per iteration and every address is a fixed constant, you need none of
this — not even one `FreshFrom.push` for a single pre-loop allocation,
because a constant-address allocation is just a longer concrete front.
`Examples/DedupAdjacent.lean` is the worked negative case: one
`make([]uint64, n)` before the loops, and zero `FreshFrom`/`DeadFrom`
anywhere in the module. Do not carry a footprint you do not need.

## 5. Segments — raw `rfl`, the option, or the evaluator

**This is the most cost-sensitive choice in the whole library, and it
has a measured answer** (WP arc `s4.md` §S4.12, `s5.md`; every number
below from that reconciliation). A "window" is a run of `n` steps
crossed by one lemma.

**THE PER-WINDOW GUIDANCE — use this table, do not improvise:**

| your window | the route | why (measured) |
|---|---|---|
| **short (≲ 40 steps)**, either route | raw `with_unfolding_all rfl`. Do not reach for the mirror. | both routes are noise-level |
| **long, and you can state the output by hand** | raw `with_unfolding_all rfl` **plus `set_option smartUnfolding false`** | the cheapest route measured: the same 752-step window is **DNF in 620 s** at default elaboration and **0.94 s** under the option. This is lint rule L5. |
| **long, and the output is something you would have to TRANSCRIBE** (nested aggregates, accumulators, many cells) | the **evaluator transport** at DEFAULT options: `Sym.symEvalWindow_refines'` | you write only the INPUT fixture; the RHS is the run's own output (`(symEvalWindow …).2.1/2.2`), so there is no hand-transcribed output state to get wrong — the campaign's actual error class. 2.6 s at default. |
| **a file that mixes both** | MEASURE. | **THE REVERSAL:** the option is file-level and it can INVERT the transported route — the same landing goes 2.6 s → no completion in 420 s under the option, and 64 ms → 13.7 s at a 32-step window. The discriminating feature was not isolated; it is a recorded open question. Keep transported windows in their own module (matmul's shape) or drop the option and pay the 2.6 s. |
| **never** | a long raw `rfl` window at default options over a **program-embedding** state | that is the L5 and L4 pathologies stacked; it cost the campaign three whole-file elaborations at 57–117 min. Restate over an abstract `σ` with only `heap`/`nextAddr` pinned. |

**Read the attribution honestly:** on today's corpus the OPTION, not
the evaluator, buys the raw-window collapse, and the evaluator is a
wash (1.03 s vs 0.94 s) for a window raw `rfl` can state. What the
evaluator buys that no option can is structural: program-genericity by
construction (`SymState`/`SymConfig` carry no program tables at all,
so a transported window cannot embed a program), no hand-transcribed
output, a ∀ρ ∀σ ∀ch-general fact per window, and insensitivity to the
elaborator heuristic that decides the raw route's fate by three orders
of magnitude.

| you are at | the form | what you owe it |
|---|---|---|
| transporting an evaluated window | `Sym.symEvalWindow_refines'` | the step-count projection `(symEvalWindow budget S C).1 = n` (a closed evaluator run), plus the input fixture as a `SymState`/`SymConfig`; you land on your statement's spelling by a defeq `exact` |
| the ∀-form, if you want the raw theorem | `Sym.symEvalWindow_refines` | the full `symEvalWindow budget S C = (n, S', C')` equation |

**Fixture:** `Examples/MatMul.lean` — the only transported consumer
today (three 291-step segments, ~1.3 s each vs 61.4 s raw), and the
only file in the tree carrying `set_option smartUnfolding false`.
The evaluator **quits** rather than erring: a quit at step `n+1` just
yields the `n`-step fact. It quits at branches, control-feeding
equality, choice consumption, addresses computed from symbolic values,
and every program-table consult. Quit-minimality is documented, not
proven — an over-eager quit costs automation, never soundness.

## 6. Values in memory: slices

`SliceMem` API groups 1, 3, 5, 6 — what the machine COMPUTES when the
operand is a `[]uint64`. No stepping, no fuel.

| you are at | the form |
|---|---|
| naming the heap representation / the handle | `sliceCells`, `sliceVal` |
| `s[i]` | `applyStrictOp_indexGet_slice` |
| `len(s)` | `applyStrictOp_len_slice` |
| `s[lo:hi]` at an array / at a slice base | `applyStrictOp_sliceExpr_array`, `applyStrictOp_sliceExpr_slice` (the general form: result `⟨some b, off+lo, hi−lo, cap−lo⟩` under `lo ≤ hi ≤ cap`) |
| `s[i] = v` | `storeTarget_slice_u64`; for an array-typed local, `storeTarget_arrayLocal_u64` + `normalizeValueForTy_arr_u64` |
| the sortedness spec predicate | `Sorted` |
| `List Int` ↔ `GoValue` plumbing | `getElem?_mapU`, `getD_mem`, `locSup_mapU`, `mem_set_of_mem` |

These facts DISCHARGE `StepKit`'s conditioned hypotheses: you state
`h : applyStrictOp σ op args = .ok (out, σ')` there, and prove it here.

**Fixtures:** `Examples/BinSearch.lean`, `Examples/DotProduct.lean`,
`Examples/DedupAdjacent.lean` (index + store + re-slice in one proof);
`Examples/SliceQueue.lean` for the moving-offset re-slice.

## 7. Values in memory: maps

`MapMem` API groups 1–3, 5 — the map operand facts and the abstract
model they are stated against.

| you are at | the form |
|---|---|
| naming the data cell / the handle | `mapCells`, `mapVal` |
| the abstract model | `idxOf?` (key position), `cnt` (multiplicity), `setk` (update-or-append), `toEntries` (the machine encoding), with `idxOf?_none_cnt`, `idxOf?_none_setk`, `idxOf?_some_snd`, `idxOf?_some_setk` |
| model ↔ the machine's `Array` of entries | `toEntries_getElem?`, `toEntries_size`, `toEntries_eraseIdx`, `map_eraseIdx` |
| `m[k]` (with Go's zero-value-on-absent) | `applyStrictOp_mapGet` |
| `m[k] = v` | `mapAssignValue_toEntries` (update-or-append = `setk`) |
| the `range` snapshot | `snapshot_toEntries` |
| the key scan | `mapEntryIndex?_toEntries`, and its body-abstract engine `scan_generic` (body-abstract so `rw` unifies it with the do-elaborated lambda) |

**Fixtures:** `Examples/WordCount/Pure.lean` (the model),
`Examples/Histogram/CountLoop.lean`, `Examples/WordFreq/Count.lean`.

The model half for slices is plain `List Int`, which is why `SliceMem`
carries no `idxOf?`/`cnt`/`setk` layer and this module does.

## 8. Values: strings

`StringMem`. **Values only — a Go string is UNBACKED: no cell, no
handle, no allocation on `+=`.** So string ops reduce definitionally
inside raw segments and there is nothing to condition on the heap.

| you are at | the form |
|---|---|
| naming the bytes | `gs` (the `List UInt8` ↔ `GoString` bridge), `gs_nil`, `gs_append` (what turns the machine's `+` into a prefix invariant) |
| `string(rune(c))` at `c < 128` | `applyStrictOp_stringFromRune_ascii` |
| `s[i]` in bounds | `applyStrictOp_indexGet_string` |
| `len(s)` | `applyStrictOp_len_string` |
| `s[lo:hi]`, `lo ≤ hi ≤ len` | `applyStrictOp_slice_string` |

**Fixtures:** `Examples/StringReverse/Machine.lean` (whose only
conditioned steps are three `enterFrame`s and the pure strict-op
facts — no `storeTarget`/`Heap.lookup` conditioning anywhere),
`Examples/WordFreq/Scan3.lean`.

**Naming exception, recorded:** `gs` is deliberately neither
`<kind>Cells` nor `<kind>Val` — there is no heap half, and it produces
the `GoString` CONTENT a `.string` value wraps, not a handle. Every
example keeps its own definitionally-equal `gs` def because headline
statements spell it and no kit name may enter a headline closure; the
copies are zero-proof delegations.

## 9. Integer normal forms + bounds

`SliceMem` API groups 2 and 7. Machine integers carry a normalization;
most of the friction in a segment proof is showing a value is already
its own normal form.

| you are at | the form |
|---|---|
| a value in range is its own normal form | `unorm_of_range`, `inorm_of_range`, and the kind-generic pair `normalize_of_range_unsigned` / `normalize_of_range_signed` |
| a `Nat` cast below a bound | `unorm_nat_of_lt`, `inorm_nat_of_lt`, `unorm_nat` |
| the arithmetic you just did stays normal | `unorm_add_nat`, `unorm_mul_nat` |
| normalizing twice is normalizing once | `intKind_normalize_idem` |
| what a strict op COMPUTES on integers | `applyStrictOp_{lessCmp_int, add_u64, sub_int, mul_u64, div_u64, mod_u64, eqCmp_int, neqCmp_int, atMostCmp, not, convert_u64}` |
| the loop guard `decide ((i : Int) < (n : Int))` must become `true` | `Surface.decide_natCast_lt_true` (in `FuelMeasure`, group 6 — beside the schemas that need it) |

**Fixtures:** `Examples/DedupAdjacent.lean` (the `unorm_of_range`/
`unorm_add_nat` rhythm through a setup loop),
`Examples/ArrayPalindrome.lean`, `Examples/DotProduct.lean` and
`Examples/Kadane.lean` (the guard bridge, 7 retrofitted sites).

**Bound vs measured — the discipline.** A step count and a step BOUND
are different claims and the library keeps them apart. `stepFnIter_iterate`
gives an EXACT count (`c * (n − i)`); the two-exit and measure schemas
give a BOUND (`∃ k ≤ …`, `CompletesIn N`). Ship a bound AS a bound: do
not restate `∃ k ≤ B` as if it were the measured cost, and do not
tighten a bound by asserting a count you have not run. The
fuel-polynomial arithmetic at the top of a run is `omega` over the
bounds the phases actually produced. The same rule governs this
guide's own numbers: every figure in §5 is derivation-anchored in
`docs/wp-arc-log/s4.md` §S4.12.

## 10. Setup families (∀-input data)

`SliceMem` API group 8 — 50 declarations, six families, ONE shape
each: a `def`, then `_length` / `_range` / `_succ` / `_set` / `_getD`
(and a `Z`-suffixed `Int`-valued range variant where a consumer needs
one). A seventh family is predictable to add because the shape is
stated, not improvised.

| your harness builds | the family |
|---|---|
| `s[i] = seed + i % k` | `familyMod` (+ `familyModZ_range`) |
| `s[i] = f i` for ANY index function — **the general one** | `familyF` (+ `familyFZ_range`, and the bridge `familyMod_eq_familyF`) |
| an ITERATED step (LCG and friends) | `familyOf`, built on `iterStep` (+ `iterStep_lt`, `familyOfZ_range`) |
| an `Int`-valued family | `familyZ`, with its pad `padZ` |
| copy-OUT of a prefix over a family | `prefixPad` (+ `prefixPad_full`, `prefixPad_familyMod_set`, `prefixPad_familyF_set`) |
| copy-OUT of COMPUTED data | `takePad` |

**Fixtures:** `Examples/DedupAdjacent.lean` (its `ddFamily` is
`seed + i/2` — a local `def` whose whole lemma family delegates to
`familyF_*`; this is the pattern for a family shape the kit does not
name), `Examples/SortShared.lean` (`familyOf`/LCG),
`Examples/Kadane.lean` (`familyZ`/`padZ`),
`Examples/MinMax/Core.lean` and `Examples/SelectionSort/Post.lean`
(`takePad`), `Examples/TwoSum/Pure.lean` (`familyF` + `prefixPad`).

## 11. Append / growth

`SliceMem` API group 4 (the values) + `StepKit` API group 5 (the
growing heap front). Both arms of `appendSlice`: in-place (no choice
consumed) and spill (one choice consumed, a fresh backing at
`nextAddr`, capacity an existential).

| you are at | the form | what you owe it |
|---|---|---|
| spare capacity, no reallocation | `applyStmtOp_append1_inplace` | the capacity fact |
| reallocation | `applyStmtOp_append1_spill` | the realized capacity, spelled |
| reallocation, and you do NOT want to name the capacity | `applyStmtOp_append1_spill_ex` | nothing — the capacity is existential, bounded by `appendRealizedCap` with `appendRealizedCap_lower` / `_upper` |
| the backing value it built | `buildAppendBackingValue_of_norm` | the normal-form fact |
| your heap FRONT GROWS as the loop runs (no fixed front to split at) | `keysBelow` with `lookup_of_keysBelow`, `lookup_frontD_none`, `lookup_live`, `set_live`, `storeTarget_live` | the executable front bound |

The append family is element-kind generic (it landed with a
`[]string` consumer as well as `[]uint64`).

**Fixtures:** `Examples/SliceStack.lean` and `Examples/SliceQueue.lean`
(in-place), `Examples/WordFreq/Scan.lean` and
`Examples/RunLength/HarnessR.lean` (the spill existential),
`Examples/TwoSum/Machine.lean` and `Examples/Sieve/Machine.lean`
(`keysBelow`).

**Scope line, honestly:** this closes the append VOCABULARY cost. It
does not close choice-dependent LAYOUT — a run whose allocation
ADDRESSES depend on the input (rle's `n ∈ [4,8]` domain gap) is still
open; see §23.

## 12. Swap / count surgery

`SliceMem` API group 9 — the sort-lane algebra.

| you are at | the form |
|---|---|
| the loop swapped two elements | `swapList`, with `swapList_length`, `getD_swapList_fst`, `getD_swapList_snd`, `getD_swapList_other`, `count_swapList`, `range_swapList` |
| a point update | `getD_set_self`, `getD_set_ne`, `count_set_add` |

**Fixtures:** `Examples/SelectionSort/Pure.lean`,
`Examples/BubbleSort/Pure.lean`, `Examples/SelectionSort/Frame.lean`.

## 13. Counted loop

`FuelMeasure` API group 6. **The condition is uniformity: every
iteration is EXACTLY `c` steps, from `(T i, C i)` to `(T (i+1), C (i+1))`,
choice-free.** If that holds, you write one per-iteration segment and
the schema does the induction.

| you are at | the form | what you owe it |
|---|---|---|
| the loop body, uniform cost, ending back at the loop head | `stepFnIter_iterate` | ONE hypothesis: `hstep : ∀ i, i < n → ∀ ch, stepFnIter c (T i) (C i) ch = .ok (C (i+1), T (i+1), ch)`. You get `stepFnIter (c * (n − i)) (T i) (C i) ch = .ok (C n, T n, ch)`. |
| the same, plus the exit leg | `stepFnIter_iterate_exit` | additionally `hexit` at index `n`; you get `c * (n − i) + e` |
| the guard `decide ((i:Int) < (n:Int))` in your per-iteration statement | `decide_natCast_lt_true` | `i < n` as `Nat`s |

The descriptor families `T : Nat → ExecState` and `C : Nat → Config`
are the proof's actual content and are per-example — that is why the
arc assessed and TRIMMED a `go_iterate` tactic: its argument list
would have been the same nine lines (WP arc `s5.md` §S5.3).

It takes down-counting `Int`-indexed loops and shifted inner-loop miss
runs unchanged. Consumed in 20 example files.

**Fixtures:** `Examples/DotProduct.lean` (the clean single loop),
`Examples/DedupAdjacent.lean` (three instantiations at `c = 57`, `53`,
`55` — setup, copy-in, copy-out), `Examples/Kadane.lean` and
`Examples/Reverse/Core.lean` (`_exit`).

## 14. Two-exit loop

`FuelMeasure` API group 6, the bounded half. Reach for these when
`stepFnIter_iterate`'s uniformity condition FAILS — and it fails in two
common ways.

| you are at | the form | what you owe it |
|---|---|---|
| the loop leaves either at its test or by an early `return`/`break` from the body, both exits running to a common anchor | `stepFnIter_iterate_bail` | a terminal predicate `Q`, an invariant `I`, and `hstep` as a DISJUNCTION per index (bail within `b`, or iterate in exactly `c`) + `hexit` within `e`. You get `∃ k ≤ c * (n − i) + max b e`. |
| **iterations of VARIABLE cost, and/or an existential successor STATE** | `stepFnIter_iterate_bail_rel` — the relational/measure-indexed schema, and the more general of the two | a per-index state PREDICATE `S i σ` (not a function `T`), a single measure `B : Nat → Nat`, and per index either the bail or `∃ σ' c, S (i+1) σ' ∧ c + B (i+1) ≤ B i ∧ …` — the iterate branch supplies its OWN cost `c` and the descent obligation. You get `∃ k ≤ B i`. |

`stepFnIter_iterate_bail` is reproved as the special case
`S i σ := σ = T i ∧ I i`, `B i := c·(n−i) + max b e`, so the kit carries
the induction exactly once.

**When to skip straight to `_rel`:** a loop whose branches cost
different numbers of steps, whose successor heap is existential
(a growing dead region, a frame transfer), or whose per-row cost
shrinks. The constant-`c`/`max b e` bound cannot reproduce those.

**Fixtures:** `Examples/ArrayPalindrome/HarnessR.lean` and
`Examples/StringReverse/Palin.lean` (`_bail`);
`Examples/TwoSum/Subject.lean` (`_rel`, variable row cost
`100 + 57·(n−t−1)` and a growing dead region) and
`Examples/BubbleSort/Outer.lean` (`_rel`, successor states existential
through the frame transfer of §17).

Per-iteration content enters as ONE hypothesis — body and binder
shapes never appear in the schema. That is the closure rule these
schemas were designed around; keep it when you instantiate.

**THE THIRD CLASS — a loop driven by a MEASURE, not by a counter.**
Both schemas above are indexed by an `i` running to a known `n`. A
`for isEven(a) { a /= 2 }` or a `for { … break }` has no counter: its
trip count is a MEASURE of the data (`v₂(a)`, `a + b`, the remaining
list), and the honest conclusion is a BOUND, `∃ k ≤ B μ`.

* **The landed practice is a hand `Nat.strongRecOn` on the measure**,
  concluding `∃ k ≤ B μ, stepFnIter k σ chead ch = .ok (…)`. Fixtures:
  `Examples/Stein/Run.lean` (FOUR of them — the common-twos loop, the
  strip loop, the inner strip, the subtract loop, each against its own
  spec function) and `Examples/DedupAdjacent.lean`'s subject loop
  (`∃ k ≤ 98·μ`).
* **`stepFnIter_iterate_bail_rel` is the form these SHOULD reduce
  to** — its `B : Nat → Nat` is exactly a measure and its iterate
  branch supplies its own cost — by instantiating `n := μ₀` and
  indexing `S` by the measure's descent. **It has no landed
  measure-driven consumer yet** (its two retrofits, twosum and bubble,
  are counter-indexed). So: try `_rel` first and record what happens;
  fall back to the hand induction, and if you do, say why. Do not
  assume the hand induction is the right answer just because four
  landed proofs contain one — three of those five predate the schema.
* **Do NOT reach for §20 here.** `completesIn_measure_loop` is the
  measure rule, but it yields `CompletesIn`, a termination claim. If
  your headline is a step-counted harness run you need a `stepFnIter`
  equation or bound, not `CompletesIn`.

## 15. Map count loop

`MapLoops` API groups 1–3, over `MapMem` group 4's model. The `m[k]++`
tower folded over a slice.

| you are at | the form | what you owe it |
|---|---|---|
| the loop's statement vocabulary | `mhG`, `wsHG`, `asgnC1G`, `asgnReadG`, `seqnC2G`, `mapAsgnG`, with `tU64`, `tMap`, `u64cell` | **the five identifier parameters your frontend embedded: `slVar`, `mapVar`, `c1`, `c2`, `iVar`** (GAP-C1b — these `abbrev`s are generic in the names, which is what lets a second example instantiate them) |
| one iteration (53 steps, placement-generic) | `mapCountIter_generic` | — (consumed via `_at`) |
| the whole loop | `mapCountLoop_generic` | the strong induction over the remaining count, back-edge included, ending at the exit test's `false` delivery |
| placing it in YOUR example | `mapCountIter_at` — the bundled per-placement form | placement facts + raw segments in; the nine conditioned discharges are constructed inside (eight are `rfl` at every landed placement) |
| the counting MODEL | `MapMem`'s `bump`, `countsFold`, `nilMapCell`, `setk_cnt_succ`, `countsFold_{nil,append,key_mem,nodup_keys,val_le}`, `cnt_countsFold`, `cnt_of_mem_nodup`, `cnt_pos_mem`, `take_succ_getD`, `cnt_take_le` | — |

Measured payoff, the campaign's best number: Histogram `CountLoop`
825 → 376 lines, **71 s → 1.2 s** when the tower became kit
instantiation.

**Fixtures:** `Examples/Histogram/CountLoop.lean`,
`Examples/WordCount/CanonCount.lean`.

**The exit is deliberately in NEITHER module:** wordcount's exit
allocates and snapshots, histogram's does not, so each consumer chains
its own.

## 16. Map range loop

`MapLoops` API group 4 + `MapMem` group 6. Drain a snapshot one
consumed choice + one erased entry per iteration; order-independence
is phrased as a CONSERVATION invariant, never as an order.

| you are at | the form | what you owe it |
|---|---|---|
| `for k, v := range m` | `mapPickLoop_generic` | the per-iteration content as ONE hypothesis, plus a conservation invariant (the landed shapes: `distinct + ‖remaining‖ = const`; `max best (maxOf rem) = const`) |
| the pick step itself, at any binder shape | `MapMem.stepFn_pick_bind` / `_value` / `_novars` | the snapshot fact |
| list consumption bookkeeping | `consume_lt`, `eraseIdx_length_of_lt`, `mem_of_mem_eraseIdx` | — |

**Fixtures:** `Examples/WordCount/RangeGeneric.lean`,
`Examples/Histogram/HarnessR.lean`, `Examples/WordFreq/Range.lean`.

**Key-type note:** the pick loop is `δ`-abstract, but `MapMem`'s KEY
axis is `uint64`-specialized — wordfreq re-derived the family at
`List UInt8` keys (`Examples/WordFreq/Count.lean`, the `*W` mirror).
Key-generic `MapMem`/`MapLoops` is parked, not built; see §23.

## 17. Loop-local allocation → threshold frame

`Frame/Threshold` — the ADDRESS half of a loop whose body ALLOCATES.
Prove the pass once at the tight canonical placement; the executable
frame theorem transfers it to the garbage-laden placement; retired
cells are rebased into the frame between passes. It knows nothing
about values or step counts, which is exactly why the two halves
compose: a loop whose body allocates needs BOTH this and §13/§14.

| you are at | the form |
|---|---|
| the per-pass shift itself | `ρT T d` (identity below the threshold `T`, `+d` above), with `ρT_lt`, `ρT_ge`, `shiftSpec_ρT` |
| the shift is the identity at `d = 0` (loop entry) | `ρT_zero_app`, `base_ne_of_ne`, `renameLoc_ρT_zero`, `renameValue_id`, `renameCell_ρT_zero` |
| a cell holds no address, so it survives every shift | `CellFixed`, `CellFixed.of_locFree` |
| transporting between CONSECUTIVE shifts | `bumpAt T r`, `renameLoc_ρT_bump` |
| naming the retired pass-local cells | `retiredFrame`, `retiredFrame_lookup_base_none`, `_lookup_field`, `_lookup_index`, `_lookup_some_inv` |
| the loop ENTRY's trivial frame | `frameSim_seed` |
| the pass ENDED — retire its cells | **`rebaseSimT`** — the front's per-cell obligations enter as ONE hypothesis (`hfront`); the retired-cell LIST is a parameter |
| transferring a segment across the rebase | `transfer_segT` |

`hfront` and `hret` are the ONLY per-example obligations, and the
per-example residue is genuinely the fixed-cell enumeration. Before
this layer, each of the five consumers hand-wrote ~400–470 lines and a
~200-line 11/16/21-way per-cell case split; the landed call is
`refine rebaseSimT (retired := […]) h`. This is why a `go_rebase`
tactic was trimmed — the lemma ate it.

**Fixtures:** `Examples/SelectionSort/Frame.lean` (the worked
instance), `Examples/BubbleSort/Frame.lean`,
`Examples/InsertionSort/PassFrame.lean` (and `Subject.lean`,
`Count.lean` at thresholds 11 and 21).

**Gotcha (§22 rule 3 bites hardest here):** pass `retiredFrame` in the
outer inductions' frame arguments rather than an explicit cell list —
consecutive addresses `b+1+1` are NOT defeq to the examples' `17+d` /
`18+d` spellings, and a fully-pinned `have` is what keeps that from
becoming a storm.

## 18. Recursion / call span

`FuelMeasure` API group 5 + `StepKit`'s frame steps. Quantify over the
return continuation and the caller env so a strong induction on the
ARGUMENT hands each recursive instantiation the frame the machine
pushed.

**PRECONDITION — most calls do NOT need the span.** `stepFnIter_call_span`
buys you a callee theorem that is REUSABLE: its `hbody` must be stated
at an abstract `(h, na, ret-cont, caller-env)`, which is real work, and
it pays for itself only when the callee is entered at more than one
placement or recursively. **A program that calls a helper exactly once
crosses the frame with `StepKit.stepFn_call_enter` and ordinary
windows — the frame EXIT then falls out of a raw `rfl` window and you
never state `stepFn_return_frame` either.** Worked single-call
fixture: `Examples/DedupAdjacent.lean` (one `stepFn_call_enter`, no
span, no `return_frame`). Take the span when you see recursion
(`Examples/FibMemo/Rec.lean`) or one callee at several sites
(`Examples/Stein/Run.lean`, four).

| you are at | the form | what you owe it |
|---|---|---|
| a whole call — enter, body, exit | `stepFnIter_call_span` | three hypotheses: `henter : enterFrame σ fid (vals ++ [v]) = .ok (func, frameEnv, locs, σ₁)`, `hbody` (the callee's body theorem at abstract `(h, na, ret-cont, caller-env)`), `hexit`. You get `stepFnIter (1 + b + e)` from the `.retV … (.callArgsK …)` config. |
| just the entry / just the exit | `StepKit.stepFn_call_enter`, `StepKit.stepFn_return_frame` | the `enterFrame` fact / the frame shape |

The recursion pattern is the span + a footprint (§4): the callee's
theorem is stated over an abstract heap with `FreshFrom h na`, so each
recursive instantiation gets the frame it needs. fibmemo's sandwich
invariant is memo-cell content + caller target + `FreshFrom`.

**Fixtures:** `Examples/FibMemo/Rec.lean` (memoized recursion),
`Examples/Stein/Run.lean` (a 36-step `isEven` span instantiated at four
sites, including a provably-not-run short-circuit path).

## 19. Composition

`FuelMeasure` API groups 1, 4, 5. ~197+ use sites of `stepFnIter_chain`
alone; every gallery example ends here.

| you are at | the form |
|---|---|
| two adjacent segments | `stepFnIter_chain` — `stepFnIter a … → stepFnIter b … → stepFnIter (a+b) …` |
| the entry equation → a `runConfig` run | `runConfig_of_stepFnIter` (`runConfig (k + f) σ c ch = runConfig f σ' c' ch'`), `runConfig_unfold`, `runConfig_step`, `runConfig_mono`, `runFunctionWithContextM_mono` |
| the driver's terminal | `runConfig_next_stop`, `completesIn_next_stop`, `execStmtLoop_next_stop` |
| completion within a fuel bound, and its algebra — **only if your headline is a TERMINATION claim (§20); a step-counted harness run needs none of it** | `CompletesIn`, `CompletesIn.mono`, `completesIn_comp`, `execStmtLoop_of_stepFnIter` |
| **queue-shaped** glue: a `seqn` splice feeding a pop, a three-way drain, a block-then-pop — **narrow, `SliceQueue`-shaped forms; skip unless your continuation has that shape** | `stepFnIter_splice_pop`, `stepFnIter_drain3`, `stepFnIter_block_pop` |

**The everyday composition layer is exactly three names**:
`stepFnIter_chain` to join segments, `runConfig_of_stepFnIter` to fold
the whole run into the entry equation's `runConfig`, and
`runConfig_next_stop` to land on the driver's terminal. That triple
plus `omega` is the entire end-to-end assembly of a harness example
(`Examples/DedupAdjacent.lean` uses it and nothing else from this
section: 78 chains, one fold, one terminal). Reach past it only when
the row above says your shape is that shape.

**Fixtures:** every example's "the run, end to end" section —
`Examples/DedupAdjacent.lean` and `Examples/DotProduct.lean` are the
readable ones; `Examples/SliceQueue.lean` for the glue composites.

**The one mechanical trap:** chain nesting must match `+`'s LEFT
associativity, or the failure surfaces as a whnf heartbeat timeout
rather than as a type error. Keep chains to ≤ 8 links (the `Scan3`
rule); pin large opaque data by a hypothesis rather than inlining it.
The fuel polynomial at the top is `omega` over the per-phase bounds.

## 20. Termination

`FuelMeasure` API groups 1–2. Use when you must show a loop terminates
WITHOUT a step count.

| you are at | the form | what you owe it |
|---|---|---|
| a loop with a decreasing measure | `completesIn_measure_loop` | a measure-indexed state family `S : Nat → ExecState → Prop`; per iteration `∃ k σ' ch' μ', k ≤ c_iter ∧ μ' ≤ μ ∧ stepFnIter k σ chead ch = .ok (chead, σ', ch') ∧ S μ' σ'`; an exit bound at measure `0`. You get `CompletesIn (c_iter * μ + c_exit)`. No Iris, no relation, no enumeration. |
| bridging to the statement layer | `terminates_of_completesIn` | `CompletesIn N σ (.exec prog env .stop)` |

**Fixture:** `Examples/Fib.lean` — the only `CompletesIn` consumer in
the example tree today.

## 21. Readout

`FuelMeasure` API group 3. A total headline says "for large enough
fuel the run returns `r₀`"; the readout twin says "any run that
returns, returns `r₀`" — the form a user actually reads. One lemma
each, so no example walks its run twice.

| your headline is | the form |
|---|---|
| the harness route (`runFunctionWithContextM`) | `harness_readout_of_total` — from `∃ N, ∀ fuel ≥ N, ∀ ch, run … = .ok r₀` to `∀ fuel ch r, run … = .ok r → r = r₀` |
| the direct route (`execStmt`) | `normal_readout_of_total` — the same shape at `.normal σf` with a postcondition `P` |

The landed idiom is one line: `exact ⟨…, harness_readout_of_total htot⟩`.
That is why a `go_run` tactic was trimmed.

**Fixtures:** 26 files use `harness_readout_of_total` — take
`Examples/DotProduct.lean` or `Examples/DedupAdjacent.lean`;
`Examples/Gcd.lean`, `Examples/BinSearch.lean` and
`Examples/MinMax/Core.lean` use `normal_readout_of_total`.

## 22. The disciplines — read before you write a slow proof

**The storm rules live in exactly ONE place:** `StepKit`'s
`## THE FIVE RULES`. Every other module cites "StepKit rules 1–5" and
adds at most one line about which bites there. Each rule was earned by
a measured failure, not by taste.

1. **Abstract the state (`σ : ExecState`) whenever the segment does not
   read or write a heap cell.** One statement then serves every
   placement and the unifier never sees a concrete front.
2. **Where a cell IS touched, take the lookup/store fact as a
   HYPOTHESIS** and keep the address abstract. The hypothesis type pins
   the state, which makes the E-form structural instead of a discipline
   someone must remember.
3. **At every application site mentioning a big concrete state, pin the
   FULL result type on the `have`.** Measured: ~2^N in the front length,
   **52 GB at N = 16**, versus instant with the expected type pinned.
4. **State lookup hypotheses D-RELATIVE, never full-heap.**
   `Heap.lookup D (Loc.base ⟨a⟩) = some c`, never
   `Heap.lookup (front ++ D) … = …` — full-heap hypotheses make every
   instantiation re-traverse the concrete front. Cost: two honest parks.
5. **Qualify `Loc.base`** (write `Loc.base ⟨a⟩`, not `.base ⟨a⟩`) inside
   big positional arguments. Measured: **502k `BEq.beq` unfoldings, a
   50-minute storm → 12 s** after writing `Loc.base`.

Plus §5's window rule and the program-generic form for long concrete
runs (abstract `σ` with only `heap`/`nextAddr` pinned; split at each
step that genuinely consults `σ.types`/`σ.functions`/`σ.methods` — for
a first-order run that is ONLY the `enterFrame` step).

**The lint.** `scripts/proof-lint` (0.4 s, report-only, wired into
`scripts/ci` as a note-only step) flags all five as syntax:

| rule | it flags | the measured pathology |
|---|---|---|
| L1 | unqualified `.base ⟨…⟩` in a STATEMENT | rule 5 — 502k unfoldings, 50 min → 12 s |
| L2 | full-heap `Heap.lookup (front ++ D)` in a signature | rule 4 — two parks |
| L3 | unascribed `have :=` on a step lemma at a concrete-state site | rule 3 — 52 GB at N = 16. **Reported as a CENSUS, not a headline count** (552 hits on a green tree: shipped sites pin their arguments by name instead of ascribing) |
| L4 | a long `stepFnIter` window whose STATEMENT embeds the program | 82 s / 50.8 GiB → 86 s / 1.9 GiB restated |
| L5 | a long raw `with_unfolding_all rfl` window in a file with NEITHER the option NOR a transport | §5 — DNF 620 s → 0.94 s. Carries the COUNTER-NOTE: never read it as "put the option on every file" |

**DO NOT HARDEN THE LINT INTO A GATE.** It reports; it never blocks.
Every rule is a regex with a crude statement/proof split, so L1/L3 have
a real false-positive class, and L4 flags
`Examples/WordCount/EmptyRun.lean` — the exemplar of its own fix, whose
statement stays byte-identical while the proof went program-generic.
Investigate a note; never obey it. Gates are for claims that must be
true.

**Before you `decide` anything, `#eval` it.** A decision procedure that
must reduce to `False` has no reason to terminate politely — that is
the 60 GB crash. `derive_entry_eq` mechanizes this reflex for entry
equations; you owe it manually everywhere else.

## 23. Honest limits — what the kit does NOT have

Do not spend an hour looking for these. Each is recorded, not hidden.

* **Key-generic maps.** `MapMem`/`MapLoops` are `uint64`-keyed;
  `Examples/WordFreq/*` re-derived the whole family at `List UInt8`
  keys (the `*W` mirror). Parked pending a puller — and the puller
  count is now THREE: the BUG-005 (L) surgery (2026-08-19) re-derived
  the live-pick candidates/mandatory algebra a third time at the
  quorum voter encoding (`Specs/GoldenQuorumThree.candidates_cfg`/
  `mandatory_cfg`/`filter_push_int` beside `MapMem.candidates_toEntries`
  and the WordFreq `*W` forms) — a ≥2-consumer consolidation slice is
  owed (arc-log slice-4 step-3 kit obligation 3).
* **Element-kind-generic `SliceMem`.** The append family is
  element-generic; the rest of `SliceMem` is `[]uint64`. The i64/bool
  mirror families are parked.
* **Choice-dependent LAYOUT.** A run whose allocation ADDRESSES depend
  on the input (rle's `n ∈ [4,8]` domain gap; any data-dependent
  allocation) has no address-shift simulation. §11 closes the append
  vocabulary, not this.
* **Struct-cell / value-side generalization.** Parked; expected to
  matter more than key-genericity at the raft target.
* **`derive_entry_eq`'s fragment.** Scalar-integer parameters; result
  defaults quoted for scalars, arrays OF scalars, nil slices/maps, and
  strings. Nested aggregate defaults (`[3][3]uint64`) are a hard,
  named elaboration error — widen a quoter arm deliberately, never add
  a silent fallback.
* **The evaluator's fragment.** Symbolic SCALARS over a concrete heap
  skeleton: no forking, no path conditions, no symbolic map keys. It
  QUITS (yielding a shorter window) at branches, control-feeding
  equality, choice consumption, symbolic-address computation and every
  program-table consult.
* **The instantiation tactics do not exist, on purpose.**
  `go_iterate`, `go_bail`, `go_rebase`, `go_run` were assessed and
  TRIMMED with one measured reason each (`docs/wp-arc-log/s5.md`
  §S5.3): the descriptor families are per-example content, so a
  tactic's argument list would equal the lines it replaces, and
  `Frame/Threshold` + `harness_readout_of_total` already ate the
  rebase and readout work. Do not re-propose them without a new
  measurement.
* **Some vocabulary `def`s have no consumers outside their own module**
  — `SliceMem.sliceVal` and `normalize_of_range_unsigned` are named
  nowhere else in `proofs/`, because examples spell their own
  definitionally-equal copies (headline statements name them, and no
  kit name may enter a headline closure). Expect to write the copy;
  it is a zero-proof delegation.
* **The integer op roster of §9 is CLOSED, and it is short.** There is
  no shift (`<<`, `>>`), no bitwise and/or/xor, no unsigned subtraction
  fact beyond `sub_int`. `Examples/Stein/Run.lean` carries private
  `applyStrictOp_shl`/`_mod2`/`_div2`/`_add1`/`_subNat` for exactly
  this reason. Write yours privately; lift on the second consumer.
* **Short-circuit `&&`/`||` in a loop guard.** A guard like
  `for isEven(a) && isEven(b)` has TWO exit shapes of different exact
  cost, so §13's `_exit` (one exact `e`) does not fit; the landed
  answer folds both under a bound. No form names the shape.
* **Multi-value assignment (`a, b = b, a`).** No named step form; it is
  ordinary store/var steps inside a raw window. §12's `swapList` is
  LIST surgery and does not apply to two scalar locals.
* **Aliasing / handle provenance across a call.** A callee that
  returns a re-slice of its argument's backing leaves caller and
  callee handles sharing a base. §6 gives the re-sliced handle's
  computed value and §3 the cell algebra, but no form STATES "this
  returned handle shares provenance with the caller's slice" — it is
  carried by hand in the callee fact's statement.
  (`Examples/DedupAdjacent.lean`: `dSliceV`/`rSliceV` both at
  `Loc.base ⟨6⟩`.)
* **A symbolic-LENGTH concrete front.** A backing region of `n` cells
  with `n` symbolic (bounded) is neither the fixed-constant case of §3
  nor a `DeadFrom` split. The landed practice is to keep the region
  list-generic in the slice handle and let the bound stay symbolic;
  the kit names no form for it and the guide adjudicates no choice
  between that and enumerating `n`.
* **Multi-result readout glue.** §1 handles multi-result LAYOUT and
  §21 turns a total run into its readout twin, but the bridge from an
  array-typed result CELL back to the `prefixPad`/`takePad` list the
  spec is stated in is unnamed per-example glue.
* **`go_walk` is a different layer.** `Tactics/GoWalk.lean` automates
  the Iris WP walk (`docs/2026-08-01_proof-automation-arc.md`), not the
  direct segment method this guide indexes. If you are writing a
  gallery example, you want this guide.

**Adding to the kit.** Two landed consumers, retrofitted in the lifting
commit, with measured deltas and the private copies DELETED; the pin in
`proofs/Audit/Kit.lean` in the same commit; the module's PUBLIC API
group updated so the name is discoverable; and a row here. A
single-consumer shape stays a private copy in its example module with
a promotion-ledger row. If a form you want does not exist, the honest
first move is to write it privately, find the second consumer, and
then lift.
