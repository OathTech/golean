# The mirror symbolic evaluator — domain design note (WP arc, slice 4)

Status: **DESIGN GATE ARTIFACT — awaiting user review.** Per the arc
charter (`docs/2026-08-16_wp-arc-charter.md:65-110` and the hard
boundary at `:186-188`), no commutation proof starts until this note is
reviewed. Everything here is proof-land design under Route B: **GoCore
is untouched**; every new definition lives under `proofs/` in the
untrusted-method zone (`docs/2026-08-12_example-spec-form.md` §12b), no
`Sym*` name may enter a headline statement closure, verified by walker
+ deletion test (§8 below).

Basis (all cites against branch `wp-design` @ `6816b199`): the step
function `GoLean/GoCore/StepFn.lean:82` (`stepFn`) with its op tables
in `GoLean/GoCore/Machine.lean` (`applyStrictOp` :252, `applyStmtOp`
:828, `applyStmtOpCore` :664, `applyRhsOp` :1079, `storeTarget` :1057,
`enterFrame` :576) and value walks in `GoLean/GoCore/Ops.lean`; the
campaign's segment corpus (`proofs/GoLeanProofs/StepKit.lean:25-108`
E-form + program-generic rules; `Examples/Kadane.lean:1218-1290` raw
windows; `Examples/TwoSum/Machine.lean:23-60` D-relative growing heap;
`Examples/FibMemo/Rec.lean:78-130` / `Examples/Stein/Run.lean:90-140`
footprint style); the frame theorem's per-step simulation as the
effort precedent (`proofs/GoLeanProofs/Frame/StepSim.lean:260`); the
R5 T1 analysis this note supersedes for slice 4
(`docs/2026-08-16_wp-library-design.md` §2, T1).

**What the evaluator is for, in one paragraph.** Today every example's
~700–900-line segment tower is windows of the form

```
stepFnIter n (kSt σ H na) C ch = .ok (C', kSt σ H' na', ch)
```

proven `with_unfolding_all rfl` (1,517 such windows in the tree), with
symbolic scalars (`nv sv iv : Int`, flags) baked into `H` as Lean
binders and every step that inspects a symbol split out into a
conditioned kit lemma. The kernel re-derives each window by whnf over
`stepFn`'s `Except`-monad tower — the cost class that blocked matmul
(61–326 s per 291-step segment). The mirror evaluator computes the
same window ONCE, over a compact first-order symbolic state, and the
refinement theorem transports the result to a `stepFnIter` fact for
every valuation of the symbols — replacing per-window kernel reduction
of the interpreter with per-window reduction of a small, purpose-built
evaluator plus one lemma application.

---

## 1. The value operation set, and the constructor/inspection split

### 1.1 What the interpreter actually does with values (the arm walk)

Walking every arm class of `stepFn` and the functions it calls, the
complete set of operations that touch a `GoValue`, classified by what
they do with the value's *payload*:

**A. Payload-blind term production (pure constructors).**
- Literals: `.intLit` → `.int (kind.normalize v) kind`
  (`StepFn.lean:288-289`), `.boolLit`, `.stringLit`, `.locLit`,
  `.ref` → `.addr`, `funcValOf` (`Machine.lean:472`).
- Integer arithmetic: `intBinaryResult` for `+ - *`
  (`Ops.lean:1686-1694`) — reads the operands' *kinds* (concrete
  metadata) via `IntKind.compatibleResult`, then applies the op and
  `IntKind.normalize` (`Value.lean:58`) to the payloads. Result kind
  and success are payload-independent.
- `neg` (`Machine.lean:295-300`), `not` (:305).
- Comparisons *as values*: `eqCmp/neqCmp` via `valueEq`
  (`Ops.lean:1413`, int arm :1417 is `left == right`), `lessCmp`
  etc. via `valueLess/valueAtMost/...` (`Ops.lean:1652-1676`, int
  arms) — produce a `.bool` whose payload is a pure function of the
  operand payloads.
- Normalization: `normalizeValueForTyFuel` (`Ops.lean:849`) at `.int
  kind` targets — `kind.normalize` applied to the payload, kind from
  the *type* (:851); at `.bool`/most base types the catch-all (:895)
  is the identity. `coerceStoredValue` (`Ops.lean:118`) likewise:
  the target kind comes from the OLD cell's value head.
- Structural moves: building/decomposing `.array`/`.struct` at
  concrete shape (`fieldGet` `Machine.lean:350`, `structLit`,
  `arrayLit`, `coerceArray/coerceStruct`), copying cells
  (`copySlice` `Machine.lean:801`), storing values wholesale.

**B. Payload-consulting control decisions (inspections).**
- Branch feeds: `valueAsBool` (`Ops.lean:1360`) at `andK`/`orK`/
  `boolK`/`ifK`/`whileK` (`StepFn.lean:324-344`) — the payload picks
  the next configuration.
- Address material: `valueAsInt` at index positions —
  `indexTargetLoc` (`Machine.lean:209`), `sliceIndexLoc`
  (`Ops.lean:283`), `arrayGet/arraySet` (:107, :161), slice-expression
  bounds (`checkSliceBounds` :180) — the payload picks *which
  location* is read/written and *whether a panic fires*.
- Payload-dependent panic/error decisions inside otherwise-arithmetic
  ops: `div`/`mod` test `divisor == 0` (`Machine.lean:280-287`);
  shifts test `count < 0` (`shiftCountNat`, `Ops.lean:1738`);
  `makeSlice` len/cap sign checks + concrete backing construction
  (`Machine.lean:680-692`); `natFromNonnegativeInt` (`Ops.lean:168`).
- Control-feeding equality: `mapEntryIndex?`'s key scan
  (`Ops.lean:1639`) — `valueEq` results decide *which entry* is
  hit; `min/max` folds (`Machine.lean:473-493`); `sortSlice`'s
  comparison sort (:769-800); the map-snapshot self-normalization
  check `isNormalForTyFuel` (`Ops.lean:947` — `decide
  (kind.normalize value = value)` reads the payload).
- Head-shape dispatch: `valueAsLoc`/`valueAsSlice`/`valueAsMap`/
  `valueAsChan`/`deferrableCallee` (`Ops.lean:1352-1379`,
  `Machine.lean:1673`) — these read the value's *constructor*, not a
  scalar payload.
- Choice consumption: `Choices.consume` at the mapRange pick
  (`StepFn.lean:599`) and the append-spill capacity
  (`Machine.lean:863`) — not a value op, but a window-ending event.
- Program/type-table consultation: `enterFrame`
  (`Machine.lean:576` — `findFunctionIn?`, `dynamicDispatch?`),
  `TypeEnv.lookup` inside `normalizeValueForTy`/`defaultValue`/
  `convertValueToTy`/`valueEq` at `.defined` types, the interface
  machinery (`canonicalTy`, `firstUnsatisfiedMethod?`),
  `mapRangeSnapshotEntries` (`Machine.lean:914`).

The load-bearing observation: **the machine's own step decomposition
already separates the two classes.** A comparison computed into a
stored bool is an `applyStrictOp` step (class A); the branch that
consumes it is a *separate* `retV`-at-`ifK` step (class B). The
campaign's hand windows break at exactly the class-B steps —
`kd_su_A0_raw` ends at `.retV (.bool (decide (iv < nv))) kdSuCmpK`
(`Examples/Kadane.lean:1266-1271`), i.e. one step *before* the branch
inspection. The evaluator's quit points therefore reproduce the
shipped segment boundaries rather than inventing new, finer ones.

### 1.2 The subtle cases, argued

**Normalization at store time is a CONSTRUCTOR — because of the
kind/value split.** `normalizeValueForTyFuel` pattern-matches on (i)
the target `Ty`, (ii) the value's *head constructor*, (iii) at ints,
the value's *kind field* — and then transforms the payload blindly
(`kind.normalize value`). In v1 all three of (i)–(iii) are concrete
even when the payload is symbolic: a symbolic scalar is `.int t kind`
with `t` a term and `kind` a concrete `IntKind` (Kadane's cell 7 is
`ki64 iv` = `⟨some (.int .int64), .int iv .int64⟩` — the kind is
written in the heap-front definition, only `iv` is a binder). So the
normalizer emits the term `norm_int64 t` and never quits. The same
argument covers `coerceStoredValue`, `bindParams`' per-parameter
normalization at base types, and the `.bool` catch-all (identity — in
`kd_su_A0_raw` the flag store normalizes a bool through exactly that
arm). Where the *type* dispatch itself needs the type environment
(`.defined` arms, `Ops.lean:885`), that is program consultation —
quit (Q4 below) — not a payload inspection.

**Comparisons: stored = constructor, branched = quit.** Because of
the step split argued above this needs no special machinery: `eqCmp
.int`/`lessCmp` on symbolic ints are constructors emitting `SymBool`
terms (`eq t u`, `lt t u`); `valueAsBool` on a symbolic bool is the
quit. A window may therefore *compute* `decide (iv < nv)` and end;
the surrounding proof case-splits and re-enters with the flag
concrete — exactly today's `kd_su_B1_raw`/`B0` pattern. One nuance:
`valueEq` is type-directed and can itself panic (interface
comparability, `Ops.lean:1493-1504`) or consult types (`.defined`
arm). v1's constructor claim is scoped to `valueEq` at `.int`,
`.bool`, `.string`-with-concrete-payloads; every other type: compute
concretely if both operands are fully concrete, else quit.

**Division/modulo/shifts are conditional constructors.** The op is a
pure term former in the *dividend*, but `divisor == 0` (resp. `count
< 0`) is a payload inspection. Rule: the op constructs iff every
payload its control decisions read is closed (evaluable to a
literal). `t / k` at concrete `k ≠ 0`: constructor. `t / u` at
symbolic `u`: quit. This covers the corpus (the `seed+i/k` families
divide by concrete constants; nothing divides by a symbolic).

**len/cap of symbolic-length things: OUT of v1.** `SliceValue`
(`Value.lean:438`) is a concrete structure in v1 — base/offset/len/
cap all concrete `Nat`s — because symbolic lengths make *address
computation* symbolic (`sliceIndexLoc` computes `offset + i`) and
make `makeSlice`'s backing construction (`Array.replicate length`)
non-computable. Kadane's symbolic-`n` handle (`kHandle n`) and
backing (`kBack n l`) are handled instead by the **opaque-atom**
mechanism (§2): cells the window never inspects ride through as
atoms, exactly as they ride through today's `rfl` windows untouched
(heap lookup compares *keys*, never cell contents — `State.lean:94`).
`len`/`cap` of a *concrete* handle is in-fragment.

### 1.3 The typeclass split — two options, one recommendation

**Option 1a — coarse interface (machine-backend class).** Class
methods at the granularity stepFn calls: `applyStrictOp'`,
`applyStmtOp'`, `storeTarget'`, `valueAsBool'`, `enterFrame'`, …
(~15 methods). The concrete instance's methods *are* the GoCore
functions, so the drift theorem is nearly definitional. Cost: the
symbolic instance re-implements each apply-function over `SymValue`
by hand — a second transcription of `applyStrictOp`'s ~270 lines and
the `Ops.lean` walks, whose fidelity is checked only by the
commutation proofs.

**Option 1b — fine interface (scalar-domain class), RECOMMENDED.**
The class abstracts only the *scalar theory*; everything above it is
shared parametric code:

```lean
structure ScalarDom where
  IntR  : Type                  -- payload rep for .int
  BoolR : Type                  -- payload rep for .bool
  -- constructors (total)
  litI : Int → IntR
  litB : Bool → BoolR
  add sub mul : IntR → IntR → IntR
  divC modC : IntR → Int → IntR        -- concrete divisor (§1.2)
  neg : IntR → IntR
  norm : IntKind → IntR → IntR
  notB : BoolR → BoolR
  eqI ltI leI : IntR → IntR → BoolR    -- comparisons as values
  -- inspections (partial: none = quit)
  toInt?  : IntR → Option Int
  toBool? : BoolR → Option Bool
```

with the value/state/control mirror `Value' D`, `HeapCell' D`,
`Heap' D`, `ExecState' D`, `Cont' D`, `Config' D` — `GoValue`'s
grammar constructor-for-constructor with `.int`'s `Int` payload
replaced by `D.IntR` and `.bool`'s `Bool` by `D.BoolR`, plus one
extra constructor `atom (i : Nat)` (the opaque cell, γ-mapped to an
arbitrary `GoValue`). The helper functions (`normalizeValueForTy'`,
`valueEq'`, `intBinaryResult'`, `loadLoc'`, `storeLoc'`,
`applyStrictOp'`, `applyStmtOpCore'`, …) and `stepFn'` itself are
written ONCE over `D`, with every payload use routed through the
class: class-A sites call constructors, class-B sites call
`toInt?`/`toBool?` and *quit on `none`*. Program consultation is
also behind the interface (a `Tables` field on `ExecState' D`:
concrete = the four arrays, symbolic = `Unit`, with `findFunc?`/
`lookupTypeDef?` quitting — this is what makes the emitted window
program-generic, §5).

Why 1b wins: (i) there is exactly ONE transcription of the machine's
logic — the mirror — instead of two (mirror + symbolic rewrite), so
the drift theorem covers the symbolic instance's machine logic too,
not just the concrete collapse; (ii) the commutation proof decomposes
as *per-scalar-op lemmas + one induction per shared helper* (§6) —
tiny leaves, structural glue — instead of per-helper hand-rewritten
correspondence; (iii) the quit surface is auditable: `toInt?`/
`toBool?`/`findFunc?` call sites are grep-ably the complete
inspection census, which is what makes the quit catalog (§4) a
checkable claim rather than prose.

Consequence accepted with 1b: the concrete-instance equivalence is
not literally `stepFn' @ GoValue = stepFn` at shared types (the
mirror types differ from GoCore's — Route B forbids reparametrizing
`Config` in place), but an embedding-mediated equation (§6.1). The
charter's drift-gate intent (mirror drift fails the build) is fully
preserved; the spelling changes. Flagged as open question OQ3.

### 1.4 The v1 operation table (normative)

| Operation (site) | v1 classification | Symbolic behavior |
|---|---|---|
| int `+ - *` , `neg`, `norm` (applyStrictOp / normalize / coerce) | constructor | term |
| int `/ %` — concrete divisor | constructor | `divC/modC` term |
| int `/ %` — symbolic divisor; shifts by symbolic count | inspection | quit (Q5) |
| bitwise ops | out of v1 term set | quit (extensible; OQ5) |
| `eqCmp/neqCmp/lessCmp/...` at int/bool → stored value | constructor | `SymBool` term |
| `valueAsBool` at `ifK/whileK/andK/orK/boolK` | inspection | quit (Q1) |
| `valueAsInt` at index/bounds/len args | inspection | quit unless closed (Q2/Q5) |
| `normalizeValueForTy` at `.int/.bool/.string/.array/.slice/...` (non-`.defined`) | constructor | term / structural |
| `normalizeValueForTy`, `defaultValue`, `convertValueToTy`, `valueEq` at `.defined`; `toInterface`; `typeAssert` | program consult | quit (Q4) |
| heap read/write at concrete `Loc` (`loadLoc/storeLoc/Heap.set`) | structural | computes |
| array/struct get/set at concrete index/field | structural | computes |
| `enterFrame` (all call/defer entries) | program consult | quit (Q4) |
| frame EXIT (`loadMany` + tgtOpK + stores at concrete locs) | structural | computes |
| map get/assign/delete — concrete key, symbolic value | structural + constructor | computes |
| map ops — symbolic key; snapshot check on symbolic entries | inspection | quit (Q8) |
| mapRange pick; append spill | choice | quit (Q3) |
| `min/max`, `sortSlice` over symbolic elements | inspection | quit |
| strings/floats: symbolic payloads | out of v1 | concrete-only |
| panic-producing step (any) | — | quit (Q6) |
| chan/select/sync/go, blocked shapes | out of fragment | quit (Q7) |

---

## 2. The symbolic term representation

### 2.1 Deep vs shallow

**Shallow (Lean-function) representation**: `IntR := Valuation → Int`.
Evaluation is free and γ is application — but *nothing is decidable*:
the evaluator cannot ask "is this term closed?" (needed at every
conditional-constructor site: `divC` requires deciding the divisor is
a literal), cannot deduplicate, cannot display, and
`symEvalWindow S = some S'` would contain function-valued states the
kernel cannot compare or reduce through. The compute-and-emit
standing principle (charter :17-22) rules this out on its own: the
evaluator's success must be *legible at generation time*, which means
first-order data.

**Deep (inductive) representation — RECOMMENDED**:

```lean
inductive SymInt where
  | lit (n : Int)
  | var (i : Nat)
  | add (a b : SymInt) | sub (a b : SymInt) | mul (a b : SymInt)
  | divC (a : SymInt) (k : Int) | modC (a : SymInt) (k : Int)
  | neg (a : SymInt)
  | norm (kind : IntKind) (a : SymInt)
  deriving DecidableEq, Repr

inductive SymBool where
  | lit (b : Bool) | var (i : Nat)
  | not (a : SymBool)
  | eqI (a b : SymInt) | ltI (a b : SymInt) | leI (a b : SymInt)
  deriving DecidableEq, Repr
```

plus `closedI? : SymInt → Option Int` / `closedB? : SymBool → Option
Bool` (structural evaluators — these implement `toInt?`/`toBool?`:
an inspection first tries to close the term, so fully-concrete
windows never quit where today's `rfl` succeeds) and the valuation

```lean
structure Valuation where
  ints  : Nat → Int
  bools : Nat → Bool
  vals  : Nat → GoValue        -- opaque-cell atoms (§1.2, §5)

def γI (ρ : Valuation) : SymInt → Int   -- structural eval
def γB (ρ : Valuation) : SymBool → Bool
```

Everything the evaluator needs is decidable (`DecidableEq` derived,
closedness by computation), the whole state is first-order data the
kernel reduces structurally, and terms are quotable.

The op set is deliberately the *consumer-driven minimum* (the ops the
24 examples' windows exercise — §1.4); each addition costs one
constructor + one `γ` equation + one commutation leaf, so growth is
cheap and incremental. No normalization/simplification inside the
term language in v1 (no smart constructors): terms record the
machine's computation history verbatim, which keeps the commutation
lemmas one-step and keeps γ-images syntactically identical to today's
hand-written statements.

### 2.2 Display — why emitted statements stay readable

The campaign's statements are read by humans, but note *what they
contain today*: `kd_su_A1_raw` concludes with `IntKind.normalize
.int64 (IntKind.normalize .int64 (iv + 1))` (`Kadane.lean:1273-1282`)
— i.e. the γ-image of `norm .int64 (norm .int64 (add (var 2)
(lit 1)))`, spelled by hand. The evaluator's output is consumed by
instantiating the refinement theorem and then `simp [γI, γB, γState,
γConfig]` with the (simp-normal, one-equation-per-constructor) γ
definitions: the `Sym*` terms rewrite away completely, leaving
exactly the `IntKind.normalize (iv + 1)`-shaped statements the corpus
already writes. So `Sym*` never appears in a *stated* lemma unless
the author wants it to; readability is the status quo, produced
mechanically. (The slice-5 emission sugar prints the γ-image
directly.) A `Repr`-based pretty-printer for terms is still worth ~50
lines for evaluator debugging, not for lemma statements.

---

## 3. The D-relative address question (charter finding 6)

Three address disciplines coexist in the shipped corpus:

1. **Absolute concrete addresses** — the dominant style: a concrete
   heap front `[(.base ⟨0⟩, ki64 nv), …]` with cells at literal
   addresses, `nextAddr` a literal, over abstract `σ`
   (`Kadane.lean:1049-1075`; ~19 of 24 examples' machine layers,
   including the matmul snapshot, the acceptance target).
2. **Concrete front + abstract dead region `D`** — TwoSum's inner
   loop (`Examples/TwoSum/Machine.lean:44-52`): the heap is
   `front ++ D ++ live-cells`, live cells at symbolic addresses
   `⟨ja⟩, ⟨ja+1⟩` with `23 ≤ ja` and `DeadFrom D ja`; the four
   accesses to live cells per iteration go through conditioned kit
   steps (`stepFn_var`, `stepFn_store_step` — :703-741), never
   through `rfl`.
3. **Fully abstract heap** — the footprint style (fibmemo/stein):
   only `Heap.lookup` hypotheses and `FreshFrom h na`
   (`FibMemo/Rec.lean:86`, `Stein/Run.lean:96`); no skeleton at all.

**Recommendation: v1 ships style 1 — absolute addresses, whole-heap
concrete skeleton.** `SymState.heap : List (Loc × HeapCell' D)` with
concrete `Loc` keys, `nextAddr : Nat` concrete.

*What this buys:* it covers exactly the windows the corpus proves by
`with_unfolding_all rfl` today — which is the cost class the
evaluator exists to kill (GAP-RFL-COST; matmul's five reformulations
are all style-1 windows). Every heap operation reduces structurally
(key comparison on literal `Loc`s), allocation appends at the
skeleton's end at a literal address, and the drift/commutation proofs
never touch address arithmetic. It also matches the two-stage matmul
acceptance: stage (b) needs style 1 and nothing more.

*What it costs — the hard half of the gallery, stated honestly:* the
evaluator does NOT emit (a) TwoSum-class growing-heap inner loops
(style 2: live cells at symbolic offsets), (b) footprint-style
recursion segments (style 3: fibmemo/stein call spans over abstract
`h`), (c) rle-class choice-dependent layouts (already quit at Q3
regardless of addressing). Those keep their current proof styles —
conditioned kit steps, the footprint pack (slice 2's lift), the
call-span combinator — which the campaign has shown are adequate,
just costlier per line. The evaluator still serves such examples for
their *straight-line, front-resident* windows (TwoSum's outer loop
and setup are style 1).

*What D-relative v2 would need*, recorded for the re-cut decision:
- `SymAddr := | abs (n : Nat) | rel (base : Nat) (off : Nat)` with a
  decidable disequality procedure over side conditions of the shape
  `front_bound ≤ base` (the `23 ≤ ja` hypothesis becomes evaluator
  *input* — v2's "conditioned facts as inputs" lever, OQ6);
- heap = concrete front + opaque dead atom + relative live cells,
  with lookup/set routing proven through `lookup_append_right` /
  `DeadFrom` (`StepKit.lean:177,264`) instead of key comparison;
- γ additionally valuates the base and supplies the `DeadFrom`
  witness, so the refinement theorem grows two hypotheses.
None of this changes the v1 term language or the class interface —
`SymAddr` slots in where `Loc` sits in the skeleton — which is why
shipping style 1 first does not paint v2 into a corner. (The parked
address-shift simulation — charter :127-130 — is a different
mechanism for a related gap: it transports whole proofs across
layouts; D-relative v2 would make single windows layout-generic. They
are complements, and neither is in this arc.)

---

## 4. The quit-condition catalog

Complete enumeration; each entry names the machine site(s), why the
evaluator cannot proceed, and what the surrounding proof layer does at
that point instead. Mechanization: quits carry a `QuitSite` payload —
an inductive whose constructors ARE this catalog, so the catalog is
code, and each constructor's docstring carries its minimality note
(§6.4).

- **Q1 — branch on a symbolic bool.** `valueAsBool` at `ifK`,
  `whileK`, `andK`, `orK`, `boolK` (`StepFn.lean:324-344`). The next
  *configuration* depends on the payload; a window is one trace, so
  it ends. *Proof layer:* case split on the emitted `decide (…)`
  value; loop windows re-enter per-branch (today's `B0/B1` segment
  pairs), and the branch structure feeds `stepFnIter_iterate`/
  `_iterate_exit` (`FuelMeasure.lean:390,422`) or the slice-1
  `_iterate_bail` for two-exit loops.
- **Q2 — symbolic address material.** `valueAsInt` at `indexGet` /
  `indexAddr` / `sliceIndexLoc` / `arrayGet` / `arraySet` / slice
  bounds; `valueAsLoc` on anything not a concrete `.addr`. Which cell
  is touched (and whether a bounds panic fires) depends on the
  payload. *Proof layer:* the conditioned store/read kit steps
  (`stepFn_var` `StepKit.lean:373`, `stepFn_store_step` :349,
  `storeTarget_addr` :423) with `Heap.lookup`/bounds facts as
  hypotheses; the `SliceMem` family lemmas carry the per-index
  content.
- **Q3 — choice consumption.** The mapRange pick
  (`StepFn.lean:599`) and the append-spill capacity
  (`Machine.lean:863`) — the successor state depends on the stream,
  and the fragment's claim is `ch`-invariant (§5). *Proof layer:*
  `mapPickLoop_generic` (pick loops), the slice-2 GAP-APPEND spill
  lemma with its capacity existential. (Design dividend noted in the
  charter :153-157: quitting at every `Choices.consume` insulates the
  evaluator from the W3.2 `Choices` reshape except through the mirror
  itself, where the drift theorem makes the exposure a build failure.)
- **Q4 — program/type-table consultation.** `enterFrame` (call
  entry, value-call entry, both defer-drain entries), `TypeEnv.lookup`
  inside normalize/default/convert/valueEq at `.defined` types,
  `toInterface`/`typeAssert`/dispatch/method-set machinery,
  `mapRangeSnapshotEntries`. The symbolic state carries NO tables
  (that is what makes the emitted window program-generic — the
  `wc_empty_run` lesson, `StepKit.lean:75-108`). *Proof layer:* split
  the window and condition on the executable fact — 
  `stepFn_call_enter` (`StepKit.lean:309`) with
  `enterFrame σ fid args = .ok …` as hypothesis, discharged by `rfl`
  once at the concrete instantiation; same pattern for `.defined`
  normalization facts.
- **Q5 — payload-dependent success inside an op.** Symbolic divisor
  (`/ %`), symbolic shift count, symbolic `make` sizes, symbolic
  slice-expression bounds, `natFromNonnegativeInt` on a symbolic.
  Success vs panic depends on the payload. *Proof layer:* a
  conditioned apply lemma at the site (`kd_make_apply`,
  `Kadane.lean:1232-1254`, is the worked exemplar: `make([]int64,
  n)` at symbolic `n` as an `applyStmtOp` fact with the sign check
  discharged by `omega`).
- **Q6 — panic paths.** Any step whose result is `.panicking`
  (strict-op panic returns, store-time panics, nil-callee panics),
  and the whole `.panicking`/`.panicked` arm cluster
  (`StepFn.lean:85-122`). v1 windows are success-straight-line; the
  corpus proves panic behavior in the negative-spec lane, never
  inside segment windows. *Proof layer:* unchanged (NegativeSpecs
  lane; unwinding is out of the segment method entirely).
- **Q7 — concurrency surface.** `chanStK`/`selectOpsK`/`syncStK`
  applies, `goCalleeK`/`goArgsK`, the blocked/`spawned` shapes
  (`StepFn.lean:433-536, 725-744`). Out of the sequential gallery
  fragment. *Proof layer:* none exists in the campaign corpus;
  nothing regresses.
- **Q8 — symbolic map keys / symbolic snapshot entries.**
  `mapEntryIndex?`'s scan needs equality *decisions* on keys;
  `isNormalForTy` on symbolic payloads reads them (`Ops.lean:947`,
  `Machine.lean:898-921`). Concrete keys with symbolic *values* do
  NOT quit (the scan compares keys only). *Proof layer:* `MapMem`/
  `MapLoops` at concrete keys; symbolic keys are outside the
  charter's v1 scope line entirely.
- **Q9 — inspection-driven aggregates.** `min/max` folds,
  `sortSlice` over symbolic elements (comparison-driven permutation).
  *Proof layer:* per-example branch reasoning (minmax) — these are
  rare and cheap by hand.
- **Q10 — opaque-atom inspection.** Any class-B operation reaching
  an `atom` cell's content (e.g. indexing into Kadane's `kBack n l`
  backing). Riding through, being loaded to `retV`, or being stored
  wholesale does NOT quit. *Proof layer:* the conditioned lookup
  lemmas over the ridden cells (`lookup_kSu`-style,
  `Kadane.lean:1151-1156`).
- **Q11 — evaluator-internal fail-closed.** Malformed mirror states
  (arity mismatches the concrete machine would call `.internal`),
  budget exhaustion, terminal configurations. Not semantic quits;
  they produce no window rather than a shorter one.

The catalog is exhaustive against the §1.1 arm walk: every stepFn arm
either (i) touches no value/table/stream (pure control glue — the
`breaking/continuing/returning/breakingTo/continuingTo` fans and seq/
frame-exit plumbing, always in-fragment), (ii) routes through a
class-A constructor (in-fragment), or (iii) hits exactly one of
Q1–Q11.

---

## 5. SymState / SymConfig shapes, and correspondence with real proof contexts

### 5.1 The shapes

```lean
-- proofs-land, all of it
structure SymState where
  heap     : List (Loc × SymHeapCell)   -- concrete keys, v1 (§3)
  nextAddr : Nat
  -- NO types/functions/methods/methodSets: program-generic by
  -- construction; Q4 quits are what enforce it.

structure SymHeapCell where
  declaredTy : Option Ty                -- concrete (drives normalize)
  value      : SymValue

-- SymValue = Value' at the symbolic ScalarDom: GoValue's grammar with
-- .int payload := SymInt, .bool payload := SymBool, plus `atom i`.
-- SymConfig / SymCont = Config'/Cont' likewise: statements, exprs,
-- envs, Locs, TargetShapes all CONCRETE (program syntax lives in the
-- configuration and is closed); only carried VALUES (retV, strictK/
-- stmtOpK/tgtOpK/rhsK done-lists, storeK vals) go symbolic.
```

Symbolic vs concrete, explicitly: **symbolic** — int/bool payloads in
heap cells and in control-carried values; whole cells as opaque
atoms. **Concrete** — addresses and `nextAddr` (§3), all program
syntax and environments (they come from the pinned program and the
window's closed continuation), slice/map/chan handles, string/float
payloads, the choice stream (v1 windows consume none — Q3), and the
program tables (absent — Q4).

The valuation and concretization:

```lean
γV  (ρ : Valuation) : SymValue → GoValue          -- structural; atom i ↦ ρ.vals i
γH  (ρ) : List (Loc × SymHeapCell) → Heap
γS  (ρ) (σ : ExecState) (S : SymState) : ExecState :=
  { σ with heap := γH ρ S.heap, nextAddr := S.nextAddr }
γC  (ρ) : SymConfig → Config
```

`γS`'s `σ` parameter is the campaign's `(σ : ExecState)` binder made
structural: the tables ride from the ∀-quantified σ, exactly the
`kSt σ H na` form (`Kadane.lean:886-888`).

### 5.2 Correspondence with a real segment (the instantiation check)

Take the shipped window `kd_su_A0_raw` (`Examples/Kadane.lean:1266`):

```
stepFnIter 25 (kSt σ (kHeapSu nv sv n l iv true) 9) kdSuHeadCfg ch
  = .ok (.retV (.bool (decide (iv < nv))) kdSuCmpK,
         kSt σ (kHeapSu nv sv n l iv false) 9, ch)
```

Its start state as a `SymState` (heap-front cells per
`Kadane.lean:1049-1062`):

| cell | today (`kHeapSu nv sv n l iv true`) | SymState |
|---|---|---|
| 0 | `ki64 nv` | `⟨some i64, .int (var 0) .int64⟩` |
| 1 | `ki64 sv` | `⟨some i64, .int (var 1) .int64⟩` |
| 2, 3 | concrete (`kArr8 kZeros8`, `ki64 0`) | concrete (`lit` payloads) |
| 4 | `kHandle n` (symbolic-len handle) | `atom 0` |
| 5 | `kBack n l` (symbolic backing) | `atom 1` |
| 6 | `kHandle n` | `atom 2` |
| 7 | `ki64 iv` | `⟨some i64, .int (var 2) .int64⟩` |
| 8 | `kbool true` | concrete |

`nextAddr := 9`; `SymConfig :=` the closed term `kdSuHeadCfg`
verbatim. With `ρ := ⟨ints := ![nv, sv, iv], vals := ![kHandle n,
kBack n l, kHandle n]⟩`, `γS ρ σ S` is *definitionally* `kSt σ
(kHeapSu nv sv n l iv true) 9` after `simp [γ…]` — the binders of the
hand lemma are exactly the valuation's images. Running the evaluator:
25 steps, all in-fragment (scalar heap reads at cells 0/7, a
comparison constructor, a concrete-bool store to cell 8 through the
normalize catch-all; cells 4–6 ride as atoms untouched), quitting at
step 26 (Q1: `ifK` on `ltI (var 2) (var 0)`). The emitted fact
γ-instantiates to the hand lemma's statement *verbatim*, including
the `.bool (decide (iv < nv))` result and the unchanged `ch`. This is
the correspondence the emitted lemmas must hit, and (per §6.3) this
window is the proposed non-vacuity witness.

The window that CANNOT be so expressed — TwoSum's inner-loop iteration
with its `D`-region live cells — is exactly §3's recorded v1
exclusion; its outer/setup windows instantiate like Kadane's.

---

## 6. The refinement theorem, decomposition, effort, witness, quit-minimality

### 6.1 Statements (both build-gated theorems, precisely)

**The evaluator and its window driver:**

```lean
-- one mirrored step; Q* = the QuitSite inductive (§4)
def stepFnS (S : SymState) (C : SymConfig) :
    Except QuitSite (SymConfig × SymState)
-- iterate to quit/budget; n = steps completed. Total, structural.
def symEvalWindow (budget : Nat) (S : SymState) (C : SymConfig) :
    Nat × SymState × SymConfig     -- (n, S', C'); quit ends, not errs
```

**THE REFINEMENT THEOREM** (the charter's `:89` statement, over these
shapes):

```lean
theorem symEvalWindow_refines
    (budget : Nat) (S : SymState) (C : SymConfig)
    (h : symEvalWindow budget S C = (n, S', C')) :
    ∀ (ρ : Valuation) (σ : ExecState) (ch : Choices),
      stepFnIter n (γS ρ σ S) (γC ρ C) ch
        = .ok (γC ρ C', γS ρ σ S', ch)
```

Read the three quantifiers as the three fidelity claims: **∀ρ** is
the value-domain frame rule (full precision on every scalar the
window never inspects — the third γ-square member after the
address-frame theorem, charter :91-93); **∀σ** is program-genericity
(the `wc_empty_run` discipline, structural); **∀ch with ch
unchanged** is choice-freedom of the fragment (Q3). Quit produces a
shorter `n`, never an unsound claim — which is why `symEvalWindow`
needs no error channel and the theorem no side conditions.

**THE DRIFT THEOREM** (concrete-instance equivalence, in a default
build target — charter :80-83). Since Route B forbids making GoCore's
`Config` an instance of the mirror, the equation is mediated by the
concrete embedding `emb : Config' concrete → Config` (and kin), which
at the concrete `ScalarDom` (`IntR := Int`, `toInt? := some`, …) is a
structure-preserving bijection written once:

```lean
theorem stepFn'_concrete_agrees
    (σ' : ExecState' concrete) (c' : Config' concrete) (ch : Choices) :
    stepFn (embS σ') (embC c') ch
      = (stepFn' σ' c' ch).map (fun (c, σ) => (embC c, embS σ, ch)) …
```

proven arm-by-arm (`fun_cases stepFn'`), each arm `rfl`-shaped after
the per-helper embedding-commutation lemmas. Mirror drift — any arm
of `stepFn'` diverging from `stepFn` — fails this theorem, hence the
build. (OQ3 asks the user to confirm this spelling satisfies the
charter's `stepFn' @ GoValue = stepFn` clause.)

### 6.2 Commutation decomposition + honest effort estimate

Plan, in dependency order (per-op leaves → shared-code inductions →
the step theorem):

1. **Scalar leaves** (~25 one-liner lemmas): `γI ρ (add t u) = γI ρ t
   + γI ρ u`, `γB ρ (ltI t u) = decide (γI ρ t < γI ρ u)`, `closedI?
   t = some k → γI ρ t = k`, etc.
2. **Helper inductions**, one per shared parametric helper, each a
   structural induction using the leaves: `normalizeValueForTy'`,
   `coerceStoredValue'`, `valueEq'` (fragment arms), `loadLoc'`,
   `storeLoc'`, `intBinaryResult'` + comparison family,
   `applyStrictOp'` (per-arm, quit arms vacuous), `applyStmtOpCore'`
   (fragment arms), `applyRhsOp'`, `storeTarget'`/`resolveChain'`,
   `loadMany'`, `Heap'` lookup/set. Statement shape throughout:
   `f' S args = .ok r → f (γ S) (γ args) = .ok (γ r)` — success-only,
   matching `ExSim`'s success-steps-only precedent
   (`Frame/Sim.lean:39`).
3. **The step commutation**: `stepFnS S C = .ok (C₁, S₁) → ∀ρ σ ch,
   stepFn (γS ρ σ S) (γC ρ C) ch = .ok (γC ρ C₁, γS ρ σ S₁, ch)` —
   ONE `fun_cases stepFn'` walk; quit arms contribute nothing (the
   hypothesis refutes them), pure-control arms close by congruence,
   value arms by the layer-2 lemmas.
4. **The window theorem**: induction on the driver, composing 3 via
   the `stepFnIter` successor equation — ~30 lines
   (`stepFnIter_chain`'s shape, `FuelMeasure.lean:343`).

**Which arms are in v1's fragment at all** (the estimate's base):
`fun_cases stepFn` yields ~197 arms (measured: the frame theorem's
`stepFn_sim` walk reaches `case197`, `Frame/StepSim.lean`; 50 arms
needed explicit treatment there, the rest closed by a tactic
battery). Against the §4 catalog: the panic cluster (~10),
concurrency/blocked/spawned (~30), choice sites (2), and
program-consult entries (~8) all QUIT — refuted-hypothesis arms in
step 3, near-zero cost each. In-fragment: ~60 pure-control arms
(break/continue/return fans, seq/frame plumbing — congruence-only)
and ~50 value-or-heap-touching arms that need the layer-2 lemmas.
So the real proof mass is ~50 arms over ~12 helper inductions.

**Effort, grounded in the StepSim precedent**: the frame theorem's
full-fidelity walk — all ~197 arms including panic/rename arithmetic,
with its helper stack (`Frame/StrictOps.lean` 1,915 lines,
`StmtOps` 677, `ChanSync` 876, `Values` 935; `Frame/` total 10,618
lines) — was landed by campaign-era workers. This build is strictly
easier per arm (no address arithmetic; quits vacuous; the concrete
side is the identity-shaped collapse, cf. `Frame/RenameId.lean`'s 179
lines for identity-rename) but adds the mirror transcription itself.
Estimate by stage: mirror types + helpers + `stepFn'` transcription
2–3 sessions (mechanical, ~2,500–3,500 lines); kernel-cost SPIKE
(below) 0.5; drift theorem 2–4; symbolic instance + evaluator +
`QuitSite` 1–2; commutation layers 1–4 above 3–6; witness + Audit
pins + walker/deletion-test extension 1. **Total ≈ 9–16 worker
sessions** — above R5's T1 estimate (2–4 + 3–5 for probe-driven
emission), which is the price of getting a *theorem* rather than
emitted text; the fallback (§7) caps the downside.

**The mandatory early spike (schedule item, before the drift
theorem):** the whole performance thesis is that kernel-reducing
`symEvalWindow ... = (n, S', C')` by `rfl`/`decide` is cheap where
`stepFn`-whnf storms. Validate on day one of implementation: run the
evaluator on the `kd_su_A0_raw` window and a matmul-snapshot 291-step
window, `#eval` first (the CLAUDE.md decide-rule), then kernel-check,
and record the times in the arc log. Design-for-reduction rules
already applied: no `Except`/`Bind` tower in the driver (bare
products), no `BEq` typeclass indirection on hot paths (structural
`DecidableEq` on `Loc` keys), no fuel-literal towers, evaluator
specialized (`stepFnS := stepFn' symDom` unfolded by `simp` pin, the
`Ops.lean:1949-1964` sealing lesson applied in reverse). If the spike
fails the thesis, stop and take the fallback — before any commutation
proof is written.

### 6.3 The non-vacuity witness (same commit as the theorem)

Per the standing gate (CLAUDE.md; charter :85-88): the refinement
theorem ships with a discharge witness instantiating it on a REAL
window from a SHIPPED example. **Chosen witness: the Kadane setup
loop-head window** — re-derive `kd_su_A0_raw`'s statement
(§5.2) by `symEvalWindow_refines` + `rfl`-discharge of the evaluator
run + `simp [γ…]`, and prove it EQUAL to the shipped lemma's statement
(or discharge the shipped lemma itself from it, delegation-style).
Why this window: 25 steps exercising scalar heap reads, a comparison
constructor, a store through normalize, opaque-atom ride-through, and
a Q1 quit at the boundary — every v1 mechanism, nothing else, and its
hand twin stays in-tree as the direct diff. (Alternative considered:
a TwoSum outer-loop window — rejected for the witness slot because
its module context is heavier; it makes a good second consumer
instead. OQ4.) The matmul stage-(b) acceptance (charter :100-110) is
the *scale* demonstration on top, not the witness.

### 6.4 Quit-minimality: documented, not proven

An over-eager quit costs automation, never soundness (charter :94-95)
— so minimality is a documentation obligation, kept next to the code:
each `QuitSite` constructor's docstring records (i) the machine site,
(ii) whether the quit is **forced** (the successor genuinely depends
on an unvaluated symbol: Q1, Q2-symbolic-index, Q3, Q5-symbolic-
divisor) or **conservative** (a stronger evaluator could proceed
given more input: Q4 with conditioned `enterFrame` facts as inputs,
Q2 under D-relative addressing, Q8 under a decidable key theory), and
(iii) the v2 lever that would lift it, if any. The note's §4 is the
prose census; the docstrings are the maintained copy. No minimality
theorem is stated or implied, and the evaluator's docstring says so.

---

## 7. Risks and the fallback line

- **R1 — kernel cost of the evaluator run (the thesis risk).**
  Mitigation: the §6.2 spike, gated BEFORE commutation work;
  design-for-reduction rules above. Residual: if `decide`-ing a
  300-step window is slow, windows shorten (the ≤8-link chain rule
  already governs hand chains) — degraded, not dead.
- **R2 — mirror maintenance under GoCore evolution.** Every GoCore
  arm change breaks the drift theorem loudly (default build). The
  known upcoming exposure is W3.2's `Choices` reshape; Q3's
  quit-at-choice design confines it to the mirror types, a budgeted
  cost recorded in the charter (:153-157).
- **R3 — γ-terms leaking into human-facing statements.** Mitigated
  by the simp-normal γ equations (§2.2) and slice-5 emission printing
  γ-images; the witness commit is the check (its statement must be
  byte-comparable to the hand lemma).
- **R4 — fragment too small in practice** (windows quit so early the
  glue overhead eats the win). Evidence against: the quit points were
  derived from where the 24 shipped examples' hand windows *already
  break* (§1.1); the fragment ⊇ the raw-rfl class by construction.
  Measured check at matmul stage (b).
- **R5 — scope creep toward v2** (D-relative, path conditions,
  symbolic lengths, symbolic keys, conditioned-fact inputs). Each is
  named in §3/§4/OQ with its consumer; none enters v1. The charter's
  parked-list discipline applies.
- **R6 — estimate risk.** The 9–16-session estimate has one soft
  spot: the mirror transcription's size (~3k lines) is mechanical but
  wide, and transcription errors surface only at the drift theorem.
  Mitigation: transcribe with the drift theorem's per-helper
  embedding lemmas proven interleaved (helper-by-helper), not
  batched at the end.

**The fallback line (recorded, per charter :108-110):** if the spike
fails or the evaluator runs long, the interim is **probe-driven
emission** — `derive_seg` mode (a) per the R5 report
(`docs/2026-08-16_wp-library-design.md:113-120`): probe the compiled
machine, quote raw-rfl windows, emit — which mechanizes transcription
but keeps per-window kernel `rfl` cost and produces no theorem. It is
the recorded interim ONLY; the evaluator remains the arc's
deliverable, and taking the fallback is a logged judgment call plus a
user ping, not a silent re-scope.

---

## 8. Outside-the-TCB, verified

Per the charter (:95-98), two mechanized checks, landed with the
first `Sym*` module:

1. **Walker extension**: `proofs/Audit.lean`'s statement-closure
   worklist walk (:385-436, currently refusing relation and Iris
   constants in headline closures) gains a third refusal class: any
   constant from the symbolic-layer modules (one namespace,
   `GoLean.SymEval`, so the check is a prefix test). Runs in the
   default build like the existing gate.
2. **Deletion test extended**: the existing arc-cadence deletion test
   (form note `docs/2026-08-12_example-spec-form.md:434`) includes
   removing the entire symbolic layer (the `SymEval` modules + the
   drift/refinement theorems) and re-elaborating every headline
   statement. Run, not asserted, at arc end.

Plus the standing Kit-pin convention: `#guard_msgs in #print axioms`
pins in `proofs/Audit/Kit.lean` for `symEvalWindow_refines`, the
drift theorem, and the witness.

---

## 9. Recommendations, one screen

1. **Typeclass split**: fine-grained scalar-domain interface
   (`ScalarDom`: total constructors `add/sub/mul/divC/modC/neg/norm/
   notB/eqI/ltI/leI` + partial inspections `toInt?/toBool?` + table
   accessors), with ONE shared parametric mirror of the value walk
   and `stepFn'` above it (§1.3, option 1b).
2. **Terms**: deep first-order `SymInt`/`SymBool` inductives with
   derived `DecidableEq`, closedness evaluators, and simp-normal γ;
   op set = consumer-driven minimum, extensible per-constructor
   (§2).
3. **Addresses**: v1 = absolute concrete addresses, whole-heap
   concrete skeleton with opaque-atom cells; D-relative is a scoped
   v2 with its needs recorded (§3).
4. **Quits**: the Q1–Q11 catalog as a `QuitSite` inductive; quit =
   shorter window, never an error; minimality documented per
   constructor (§4, §6.4).
5. **Shapes**: `SymState` = concrete-keyed skeleton + `nextAddr`,
   NO program tables; γ parametric in the ∀σ; `∀ρ ∀σ ∀ch,
   ch-unchanged` refinement statement; Kadane `kd_su_A0_raw` as the
   same-commit witness (§5, §6).
6. **Process**: kernel-cost spike gates the build; drift theorem
   proven helper-interleaved; 9–16 sessions estimated; probe-driven
   emission is the recorded fallback (§6.2, §7).

## 10. Open questions for the user gate

- **OQ1 — class granularity.** §1.3 recommends the scalar-level
  class (1b) over the coarse machine-backend class (1a). 1a would
  cut the mirror's size roughly in half and make the drift theorem
  near-definitional, at the cost of a second hand transcription of
  the op tables checked only by commutation. Confirm 1b.
- **OQ2 — quit signalling.** Recommended: `stepFnS` returns
  `Except QuitSite …` and the *driver* converts quit into a shorter
  window (no error in `symEvalWindow`'s type). Alternative: `Option`
  with quit sites only in a debug channel — simpler types, weaker
  catalog mechanization. Confirm the `QuitSite` design.
- **OQ3 — drift-theorem spelling.** Route B makes literal
  `stepFn' @ GoValue = stepFn` untypeable; §6.1's embedding-mediated
  equation is the proposed realization of the charter clause. Confirm
  it satisfies the drift-gate intent.
- **OQ4 — witness choice.** Kadane `kd_su_A0_raw` (recommended) vs a
  TwoSum outer-loop window. Cheap to do both; the witness *slot*
  needs one.
- **OQ5 — v1 term-former set.** Bitwise/shift term formers excluded
  until a consumer appears (extensibility is one constructor + two
  lemmas each). Confirm consumer-driven growth over
  completeness-now.
- **OQ6 — conditioned facts as evaluator inputs** (accepting e.g. an
  `enterFrame` fact or `t ≠ 0` to convert a Q4/Q5 quit into a
  proceed) is deliberately OUT of v1 — it changes `symEvalWindow`'s
  type and the theorem's hypotheses. Flagging now because it is the
  main v2 axis alongside D-relative addressing; no decision needed
  beyond "not in v1".

---

## USER GATE DISCHARGED (2026-08-18)

Ruling: **approved as recommended**, all six open questions per the
operator's takes — OQ1 fine-grained `ScalarDom`; OQ2 `QuitSite`-carrying
`Except` (total driver); OQ3 the embedding-mediated drift equation
APPROVED as satisfying the charter's intent (the charter's literal
`stepFn' @ GoValue = stepFn` phrasing is amended to the embedding form
at the next wp-arc boundary — an integration TODO, recorded here);
OQ4 Kadane as the non-vacuity witness; OQ5 consumer-driven v1
term-former set; OQ6 conditioned-facts-as-inputs deferred to v2.
Slice 4's build is unblocked; the mandatory kernel-cost spike gates the
commutation walk per §6.
