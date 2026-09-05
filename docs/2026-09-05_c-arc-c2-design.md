# C-arc C2 — the well-founded, index-keyed type table (2026-09-05)

[AGENT] design note, lane `c-arc-c2`, off `main` @ `b77f3298`. Gate
**G-C2** (`docs/2026-09-04_reasoning-surface-plan.md` §3.C2, §5.4):
«Frontend emits typeDefs in dependency order with aliases inlined (twin
pin moves); `TypeEnv` becomes index-keyed and well-founded by an
`Accepted` clause decided at decode; the 14 fuel towers,
`typeResolutionFuel` and the `irreducible` seal are deleted.»

Evidence: `docs/evidence/2026-09-05_c-arc-c2/`. Records touched: §10.

## 0. Gate provenance (disclosed, as relayed)

G-C2 was RULED [USER] 2026-09-04 as recommended («let's move ahead with
the plan», the nine gates individually presented — the coordinator's
reading, disclosed in `docs/2026-09-04_c-arc-gu-design.md` §0) and
CONFIRMED [USER] 2026-09-05 («(1) approved» — item (1) of the
eight-item list the coordinator put to the [USER]; the ruling record
is `docs/2026-09-04_reasoning-surface-plan.md` §5.4, «Ruling record,
2026-09-05 (confirmation of the gate reading)», landed on `main` at
`426af905` by the `rulings-0905` merge, which this branch is rebased
onto — audit fix R14). Both quotes reached this lane by [AGENT]
coordinator relay; they are cited as relayed, never as firsthand. The twin-pin move is part of the ruled gate; it is still
recorded as a deliberate re-pin with its structural diff and reason
(§7, `scripts/check-frontend-pins` re-pin history). Standing directions
applied: the disruptive change is in scope when it buys a more useful
reasoning surface; fail closed with named causes; every gap rowed.

## 1. What the machine sees now

```lean
abbrev TypeIdx := Nat                                  -- Value.lean
inductive Ty | … | interface (id : TypeId) | defined (idx : TypeIdx) | …
abbrev TypeEnv := Array (TypeId × TypeDef)             -- Syntax.lean; Program.typeDefs IS one
inductive TypeDef | struct | interfaceDef | defined | opaqueDecl        -- `.alias` deleted
def Ty.deps : Ty → List TypeIdx        -- `.defined i ↦ [i]`, `.array _ e ↦ e.deps`, else `[]`
def TypeDef.deps : TypeDef → List TypeIdx   -- struct fields' deps / defined target's deps / []
def TypeEnv.WellFounded (t : TypeEnv) : Prop := ∀ e ∈ t.toList.zipIdx, ∀ j ∈ e.1.2.deps, j < e.2
instance : Decidable t.WellFounded                     -- the library's `List.decidableBAll`
def TypeEnv.firstViolation? : TypeEnv → Option (TypeIdx × TypeIdx)   -- the edge the refusal names
theorem TypeEnv.firstViolation?_eq_none_iff : t.firstViolation? = none ↔ t.WellFounded
def TypeEnv.reserved : TypeEnv := #[(⟨"struct{}"⟩, .struct #[]), (runtimeErrorTypeId, .opaqueDecl …)]
def TypeEnv.nameOf? (t) (i) : Option TypeId ; def TypeEnv.lookupName? (t) (id) : Option (TypeIdx × TypeDef)
```

`Ty.defined i` names table entry `i`; identity of defined types is
POSITIONAL (`Ty.eqb`: `.defined a, .defined b ↦ a == b`). The entry's
`TypeId` stays beside its body: it is read back (`nameOf?`) for every
gc-visible text (panic messages, `printanycustomtype`'s `main.T(7)`),
for the observation channel (`Ty.dynamicName`), for method-set records
and the method-carrier key, and for the two name-keyed consumers
(`structTagCompatible` on VALUE tags, `interfaceDeclaredMethods?` on an
interface name). It is never used to resolve a `Ty.defined`.

`ExecState.types : TypeEnv := #[]` is `Program.typeDefs` verbatim (the
`toList` conversion at the three driver seams is gone).

## 2. The `Accepted` clause, decided at decode

Plan §1.9 names `Accepted P` as "decoder-side: no refusal marker, method
sets complete, typeDefs well-founded (C2)". This slice lands the third
conjunct, in two parts: the first DECIDED by the decoder
(`NativeToIR.lean`, `decodeProgram`), the second CONSTRUCTED by the
decoder and DECIDED at the two driver seams (audit fix R2/R5a — the
first version of this note said "both decided by the decoder"; the
decoder never evaluated `hasReservedPrefix`, it only built the prefix):

1. **Well-foundedness.** `typeDefs.WellFounded` — every table dependency
   of entry `i` sits at an index `< i`. The decoder evaluates the core's
   own `Decidable` instance (`if !typeDefs.WellFounded then …`) and, on
   refusal, names the FIRST violating edge from `firstViolation?`:
   `program.types is not dependency-ordered — table entry 2 (main.Outer)
   depends on entry 3 (main.Inner) with 3 ≥ 2 (a forward reference or a
   cycle; indices count the two machine-reserved entries)`. The decision
   IS the Prop: `firstViolation?_eq_none_iff` ties the text to the
   predicate.
2. **The reserved prefix.** Every accepted table LEADS with
   `TypeEnv.reserved`: index 0 is the canonical anonymous empty struct
   `struct{}` (BUG-011's one unnamed struct on the wire; the frontend
   references it and never declares it — the decoder synthesized it
   before too), index 1 is the machine's runtime-error payload type
   (`$runtime.Error`) as an OPAQUE declaration. The decoder prepends the
   prefix, maps the wire's entry `k` to index `k + 2`, and refuses a wire
   TypeDef that spells a reserved key or duplicates a TypeId. The
   predicate `TypeEnv.hasReservedPrefix` (a Bool) is EVALUATED by
   `runProgramSetupM` (`StepFn.lean`) and `CLI.enumSetup` — the two
   driver seams that already assert `StateWf` — which refuse a
   `Program` that fails it BY NAME before any step runs (audit fix R2:
   `runtimeErrorTypeIdx = 1` is a machine constant, so a hand-built
   table with a user type at index 1 would otherwise have rendered a
   user value as a runtime-error abort; pinned, `C2/R2` eval tests).
   `Program.typeDefs` now DEFAULTS to `TypeEnv.reserved`, so a
   declaration-free hand-built program is accepted unchanged.

Why index 1 exists: `runtimeErrorValue msg` boxes at `.defined
runtimeErrorTypeIdx` with no state in hand (`Machine.lean`), so the
sentinel's index must be a CONSTANT of the machine, and the renderer's
first check (`idx == runtimeErrorTypeIdx`) must be meaningful in every
accepted table. The entry is opaque because that reproduces exactly the
fail-closed behaviour the ABSENT declaration produced before: every
structural use (`==`, normalization or conversion at the type, default
value, comparability) refuses by name, the method-set record is absent
so satisfaction/dispatch refuse (BUG-059's R-1 kind clause is unchanged),
and `renderPanicPayload`/`goTypeNameForMessage` read the key back
unchanged. A real `TypeDef.defined .string` there would have made
`err1 == err2` ANSWER where gc's several `runtime.Error` types make the
answer type-dependent — a semantics widening this slice does not make.

Consequences the decoder now enforces that it did not before: duplicate
`TypeId`s refuse at DECODE (the frontend's `seenTypeIds` check was the
only guard); a `named` reference with no TypeDef refuses at decode
(before: an `unknown defined type` refusal at the first USE, at run
time); an `alias` TypeDef refuses (before: decoded into `.alias`).

Hand-built tables (`Tests/GoCoreEval.lean`): every `Program` run
through a driver seam MUST lead with `TypeEnv.reserved` — the seams
refuse otherwise (R2). The S6 renderer pin caught the hazard on the
first build (its `main.T` sat at index 1 and was mistaken for the
runtime-error payload) and documents the rule beside the fix. The
ExecState-level test entries (`runFunctionWithTypesM`,
`runFunctionWithContextM` — no `Program`, no globals, no `$pkginit`)
are NOT behind the check; the one such table (`coreCellTypes`)
exercises neither a runtime error nor the renderer, and a runtime error
in such a state refuses on an out-of-range index, never mis-identifies.

## 3. The dependency-order contract on the wire

**Edges.** Exactly the positions the machine's type-directed recursions
descend into: a struct's field types and a `defined` type's target,
each read THROUGH array elements. `named` references under pointer,
slice, map, channel, function and interface types are NOT edges (Go
permits recursion only through them — `type L struct{ next *L }` — and
no type-directed walk enters them: a pointer's size is a word, its zero
value `nil`, its comparability its own). Interface and opaque
(`unsupported`) TypeDefs have no edges: their method signatures are
compared by `Ty.eqb`, never resolved. `struct{}` is always satisfied
(index 0).

**Frontend** (`tools/nativefrontend/typeorder.go`, called from
`emitProgram` after `checkWireNamedTypes` and before the method-set
record classifier): `orderTypeDefsByDependency` is a DFS post-order over
the table in its current order, visiting each entry's edges first in
their structural order (field order, array-elem descent); a gray
re-entry is a CYCLE and refuses naming the path (`main.A -> main.B ->
main.A`); a dependency on a name with no TypeDef refuses naming both
ends (the wire-integrity check before it already has); an `alias` or
unknown def kind refuses by name. No map iteration reaches the output
(BUG-091 discipline). Then `checkTypeDefOrder` re-checks the FINAL table
against the contract — the wire-integrity check extended to the order
contract, so an ordering bug can never ship a wire the decoder will
reject. Both are fail-closed refusals of the whole export.

Cycles cannot arise from valid Go (go/types rejects invalid recursive
types) and `.defined`-over-`.defined` chains cannot arise either (a
`defined` target is go/types' `Underlying()`, never a named type); the
refusals exist for hand-built and future emitter faults, and are pinned
on hand-built tables (`typeorder_test.go`).

**Determinism.** `TestEmitIsDeterministicWithTypeOrder`: a source whose
types are declared in reverse dependency order, with pointer/slice/map
self-recursion, emits byte-identical 20×, and the order is asserted
(`main.Inner < main.Mid < main.Outer`, `main.Code < main.Codes`,
`main.Ring` present, `checkTypeDefOrder` nil). The existing determinism
shapes pass `checkTypeDefOrder` too.

**Decoder** (§2): the machine's independent, fail-closed re-decision of
the same contract; the frontend's pass is not trusted, it is checked.

## 4. "Aliases inlined": identity and panic texts

A Go alias `type T = U` is identity-erasing by definition (spec §Alias
declarations). The frontend has inlined aliases at every use since G4
(`wire.go`: `types.Unalias`; `mono.go`; `identity.go`'s render), so no
wire ever carried an `alias` TypeDef; `TypeDef.alias` was reachable from
hand-built programs only. This slice DELETES it and REFUSES it at the
decoder. Consequences on the machine:

- `resolveDefinedAliases` and `canonicalTy` (S3's "canonical dynamic
  type", which resolved alias chains through the whole type structure)
  are the IDENTITY on an alias-free `Ty` and are deleted; every `Ty` on
  the machine IS its canonical form. `canonicalDynamicTy` survives as
  `checkedDynamicTy` — the fail-closed boxing check for `.unsupported`
  leaves, which is all it still did. `methodRecvDynamicTy?`,
  `concreteMethodSignature?`, `satisfiesMethodSig`, `typeAssertValue`,
  `typeAssertPanicMessage`, `methodCarrierKey?` compare types directly.
- **Identity** of a defined type is its table position; of an interface
  type its `TypeId` (unchanged — interface identity is name-keyed by
  the plan's design, and the requirement lists are looked up by name);
  of a struct VALUE its mint tag (`GoValue.struct (typeId : TypeId)`,
  unchanged) and of a field path its tag (`Loc.field … (typeId :
  TypeId) …`, unchanged, as the plan's §1.1 sketch keeps it). Where a
  value tag meets a type index — struct normalization, struct literals,
  struct conversion, struct equality — the key is read back from the
  entry (`types[i] = (name, .struct fields)`) and compared as a
  `TypeId`, exactly the comparison made before.
- **Panic texts** (BUG-059's display/identity rule): the machine renders
  a defined type by the KEY stored beside its entry, verbatim —
  `goTypeNameForMessage`, `dynamicTypeName?`, `renderPanicPayload`'s
  `main.T(7)`, `Ty.dynamicName`'s unqualified form on the observation
  channel. No gc-visible text changed (the differential and the readout
  identity in §7 are the check). BUG-059 itself — the path-vs-name
  qualifier class for multi-segment import paths — is untouched and
  still red: the display rule is "render the stored key", and the key
  the frontend mints is the path-qualified one. An index the table does
  not have renders as a VISIBLE marker (`<unknown type index i>`) or
  fails closed (`none`), never as a guessed name; unreachable on a
  decoded program (the marker class is itemized in §8, audit fix R10).
- Refusal texts that `repr` a type now print `Ty.defined 3` where they
  printed `Ty.defined { key := "main.T" }`. These are diagnostics
  (stuck/unsupported reasons); no baseline or observation carries them.

## 5. The recursion disciplines (no fuel anywhere)

The section note at the top of `Ops.lean` is the reference; in short:

**Type-directed walks — two structural layers.** `defaultValue`,
`tySizeAlign`, `tyUncomparable`, `normalizeValueForTy`, `isNormalForTy`
each split into a `…Ty` layer, STRUCTURAL on the type (only `.array`
descends into a subterm; pointer/slice/map/chan/func/interface are
leaves) which hands `.defined i` to a callback, and an `…At` layer,
STRUCTURAL on a `bound : Nat` that counts the table indices still
available to the descent: resolving index `i` consumes one, and the
body found is walked by the `…Ty` layer with the callback at the
smaller bound. The public wrapper seeds `bound := types.size`. On a
well-founded table the descent never exhausts — a dependency chain from
index `i` has at most `i + 1` entries and `i < types.size` — so the `0`
arm is reachable only from a hand-built table the decoder would have
refused. What the `0` arm does is per layer, and matches what the fuel
version did at exhaustion (no regression; audit fix R5b corrects the
first version of this paragraph, which named `typeIndexExhausted` for
all five): `defaultValueAt`, `normalizeValueForTyAt`, `tySizeAlignAt`
and `TypeEnv.resolve` (hence `convertValueToTy`/`buildStructValue`/
`valueEq`) REFUSE by name (`typeIndexExhausted` — "typeDefs not
dependency-ordered … unreachable on an accepted program" — or
`resolve`'s own text); `tyUncomparableAt` returns `none` (UNKNOWN, its
three-valued refusal arm) and `isNormalForTyAt` returns `false` (NOT
normal, which every consumer treats as a refusal to accept the value).
The bound is not a budget: it is a projection of the program
(`types.size`) and no literal appears in any equation; its
SUFFICIENCY on a well-founded table is an argument in this note (the
chain-length bound above), not a kernel fact — see §8 (unproved; the
"bound irrelevance" theorem is the owed statement; audit fix R5c). The
lockstep of the two-layer shape is what keeps the
cross-walk lemmas UNCONDITIONAL (`isNormalForTy_sound`,
`defaultValue_ok_of_normalize_ok`: both descents at the same bound).

**`TypeEnv.resolve`** (bound-structural) follows `.defined`
indirections to a `TyBody` — a non-`.defined` head, a declared struct
(name, fields), an interface declaration or an opaque declaration — and
`convertValueToTy` and `buildStructValue` are NOT recursive at all once
the body is in hand (the old fuel existed only for the alias chain).

**`valueEq` — value-structural.** Go's `==` on interfaces compares the
DYNAMIC values at a type DISCOVERED from the value, so the walk is on
the LEFT operand (a mutual block with `valueEqList`/`valueEqFields`;
array elements, struct fields and the boxed dynamic value are its
subterms), with `TypeEnv.resolve` reading the declared body at each
step. It is the one type-directed walk that is value-directed, and the
note says so.

**Nested inductives — mutual structural.** `Ty.eqb`/`Ty.eqbList`,
`Ty.mentionsUnsupported`/`…List`, `goTypeNameForMessage`/`…s`/
`…Variadic` (the variadic `...E` rendering now pattern-matches the
LAST parameter structurally instead of `getLast?`), and
`GoValue.eqb`/`eqbList`/`eqbFieldList` (arrays destructured in the
patterns: `.array ⟨a⟩`). Lean 4.32's structural recursion over nested
inductives makes the 2026-07-31 fuel workaround unnecessary; the
generated `mutual_induct` principles carry the soundness proofs
(`StateEqb.lean`).

**Kernel reducibility** — the property the 2026-08-03 de-WF restructure
bought with fuel — is kept without it: everything is `Nat.rec`/`brecOn`,
no `WellFounded.fix`, and `Ops.lean` pins closed instances by `rfl`
(`defaultValueAt` over a three-entry table, `valueEq` through an
interface box at a defined struct type) and unfolding patterns by
`simp`. The elaborator seal (`attribute [irreducible]` on the wrappers)
guarded against `whnf` diving into 1024-literal towers; there is no
literal to dive into and the seal and its post-seal pins are gone.

**`Ty.arrayInduction`** (Ops.lean) is the induction principle the
type-layer lemmas use — `Ty` is nested, so the `induction` tactic
refuses it; the principle descends the array spine only, which is the
one recursive position of every type layer.

## 6. Proofs moved arm-for-arm (invariant 5)

Every lemma that unfolded a `*Fuel` function is restated as a type-layer
lemma parametric in the `.defined` callback (with the callback's
property as hypothesis) plus an index-layer lemma by induction on the
bound, plus the wrapper: `StateWf.lean` —
`normalizeValueForTy{Ty,At,}_locSup`, `defaultValue{Ty,At,}_locSup`,
`isNormalForTy{Ty,At,}_sound`; `convertValueToTy_locSup` and
`buildStructValue_locSup` case on the resolved body (no induction).
`MachineSound.lean` — `normalizeValueForTy{Ty,At,}_congr`,
`defaultValue{Ty,At,}_ok_of_normalize{Ty,At,}_ok`,
`normalizeValueForTy{Ty,At,}_noPanic`, `defaultValue{Ty,At,}_noPanic`.
`StateEqb.lean` — `Ty.eqb_sound_all`, `GoValue.eqb_sound_all` by
`mutual_induct` (one case per match arm). `SyntaxEqb`/`MachineEqb` lose
the alias arm / switch the list comparator to the array one. The
parameterized list/field helpers (`normalizeListWith`,
`normalizeFieldsWith`, `isNormalListWith`, `defaultFieldsWith`, …) and
their lemma families are UNCHANGED — the type layer passes them the
callback-bearing layer exactly as the fuel version passed the
decremented one. Tombstones: `normalizeValueForTyFuel_locSup`,
`defaultValueFuel_locSup`, `convertValueToTyFuel_locSup`,
`isNormalForTyFuel_sound`, `buildStructValueFuel_locSup`,
`normalizeValueForTyFuel_congr`, `defaultValueFuel_ok_of_normalize_ok`,
`normalizeValueForTyFuel_noPanic`, `defaultValueFuel_noPanic`,
`Ty.eqbFuel_sound_all`, `GoValue.eqbFuel_sound` — each replaced by its
named successor above, none weakened (the wrappers' statements are
identical).

## 7. Preservation — exact, and what the evidence shows

**Argument.** On every accepted program the fuel never ran out (type
nesting ≪ 1024), so each fuel function equalled the structural
counterpart on every reachable call: the type layer's arms are the fuel
function's non-`.defined` arms verbatim; the index layer's arms are the
`.defined` arm's `TypeEnv.lookup` cases with the alias case deleted
(unreachable: no wire carried an alias) and the lookup by index instead
of by name (the decoder's name → index map is a bijection on the
accepted table, so `TypeEnv.lookup types name = some d ↔ types[idx name]
= some (name, d)`). `valueEq`'s value walk visits the same arms in the
same order with `resolve` doing what the `.defined` arm did. `Ty.eqb`
and `GoValue.eqb` agree with the fuel versions wherever the fuel
sufficed — every value a program builds. The refusals at exhaustion
("type nesting too deep", Ops.lean's old 1023-vs-1024 caveats) were
unreachable and are now unrepresentable on accepted input; the ONE new
refusal class is the decoder's (§2), pinned by eval tests (a corpus row
cannot exhibit it: the frontend orders every wire).

**Gates and measurements** (all in the evidence dir):

- `scripts/capped scripts/ci --diff` at the clean tip `166244f7`:
  **PASS**, baseline diff FULL 3498/3498 no regression, negative 394
  match, twin pin = the re-pinned bytes; ZERO drift beyond the twin pin
  (the one stage move landed inside the recorded `beside-loop`
  alternation). Tail: evidence `ci-diff.txt`; §9.
- Twin pin `4ee39f73… → d2bcb07b…`: `twin-repin/structural-diff.txt` —
  funcs/methods/methodSets/globals/fileOrder IDENTICAL; `types` is a
  PERMUTATION of the 92 entries (36 moved), byte-equal per entry; the
  pinned table had 12 order-contract violations (e.g. `raft.raftLog`
  before its field type `raft.entryEncodingSize`), the new one 0. The
  reason is the gate's: "typeDefs dependency-ordered".
- Readout byte-identity vs the pre-change binary: `choice-trace/` — the
  labeled-consumption tracer over the whole executable corpus × 6
  streams with `--golean` the `main @ b77f3298` binary (built from a
  `git archive` in `.tmp/before`) and with the tip binary, compared by
  the a-series `trace-diff.sh` on every consumption-relevant column
  INCLUDING `obsHash` (the observation JSON's hash) and
  `driverAgreement`. Both binaries read the SAME (dependency-ordered)
  wires: the old decoder is order-agnostic, so the comparison isolates
  the machine. RESULT: 20737 of 20749 (id,stream) lines byte-identical;
  the 12 that differ are the 6 streams of two baseline-FAIL rows
  (`panic-recover/panic-defined-payload-methods/{error,stringer}`,
  `unsupported` on both binaries, identical consumption) whose REFUSAL
  TEXT `repr`s the dynamic type — `Ty.defined { key := "main.payloadCode"
  }` → `Ty.defined 2` (§4's disclosed diagnostic change; not an
  observation any baseline carries). Per-site consumption totals
  identical: the choice trace has ZERO delta — types consume nothing.
  Two rows excluded on both sides and recorded (`excluded.tsv`): the
  a-series' `goroutines/send-then-spin` and the red-by-design
  `strings/trimspace-repeat/repeat-bound-refused` (30 s gate timeout;
  the tracer has none). **The whole-corpus identity claim is therefore
  MINUS this one row** (audit fix R9): `repeat-bound-refused` is a
  red-by-design refusal reached only after materializing a 16 MiB
  string — its cost is materialization, not fuel, so a tracer with no
  timeout cannot finish it in bounded time on either binary; its
  consumption identity is UNMEASURED here, and its RESULT (the refusal,
  FAIL by design) is covered by the differential gate, where it matched
  the baseline on every run. `excluded.tsv` carries both rows' reasons.
- Two tracer findings on the SAME wires under BOTH binaries, identical
  before/after, NOT this lane's: (i) the 6 driver-agreement MISMATCH
  lines on `builtins/float-bits/roundtrip-payloads` — the tracer
  compared the enumerator's refusal with an EMPTY output field against
  the engine's `RunResult` with its output prefix (`CLI.lean` `errorJson`
  defaulted `output`; a fail-open comparison). ROWED AND FIXED by the
  `c-arc-b4` lane's audit fix round (its design note
  `docs/2026-09-05_c-arc-b4-design.md` §7 item 6, `TODO.md` C-arc
  section, `docs/operational-lessons.md`); NOT duplicated here (audit
  fix R7) — when b4 lands, the six `obsHash` values on both sides of
  this lane's trace move together (the enumerator observation gains the
  prefix), and the identity verdict is unaffected. (ii) The one tracer
  ERROR line, `arrays/materialization-budget/over-budget`: BUG-078's
  DESIGNED decode-time refusal (the array exceeds the materialization
  budget), which the tracer cannot trace because there is no program to
  run — not a mismatch, not a gap.
- Eval tests: 170 ok, 0 fail (`eval-tests.txt`); 12 `C2:` pins for
  the decoder's acceptance clause, the core's `WellFounded`/
  `firstViolation?` agreement, the observation channel through the
  index, and the reserved runtime-error index, plus the 5 audit fix
  pins `C2/R1` (an unresolvable index is a carrier with the unrecordable
  key) and `C2/R2` (both driver seams refuse a prefix-less table by
  name; the `Program` default is accepted; the control runs).
- Frontend: `go test ./tools/nativefrontend` ok — the FULL package run
  with its command line (`frontend-tests.txt`, audit fix R8; the first
  record was a 5-test `-run` subset): 100 tests PASS incl. the 9
  `typeorder_test.go` tests (the duplicate-name refusal of BOTH
  `orderTypeDefsByDependency` and `checkTypeDefOrder` is pinned — the
  latter overwrote `index[name]` before audit fix R12).
- Order-change coverage (audit fix R11): `structs/decl-order-reversed/`
  — 5 rows over six types declared in REVERSE dependency order with
  array-element edges at two depths (`Grid [2][2]Cell`; `Codes`/`Raw
  [3]Code`); the source-order table violates the contract and EVERY
  entry moves (`Code, Pair, Codes, Cell, Grid, Raw` on the wire). Four
  PASS with gc (`zero-values`, `array-equality`, `interface-box`,
  `defined-array-values`: zero values, writes through every level,
  array/struct equality, boxing + assertion + interface equality,
  defined array values copied/compared/indexed); the fifth,
  `conversion-array-target`, is RED-FIRST on **BUG-103** (filed here):
  a conversion whose target's resolved shape is an ARRAY (`Raw(cs)`,
  `[3]Code(r)`) falls into `convertValueToTy`'s catch-all — the array
  arm BUG-020's fix left out, a machine gap DETECTED while writing the
  rows and rowed at detection ([USER] 2026-09-03 direction; the ledger's
  Conversions row names it). Not this slice's regression: the fuel
  version had the same catch-all. Born rows in the baseline (§9). Before
  them, 11 of 1308 emitting corpus packages moved under the reordering
  and the twin's one `array` node was the only array-edge witness.
- Lean line delta (`lean-line-delta.txt`): GoLean/ +1763 −1466, net
  +297 — the towers left, but the two-layer descents, `TypeEnv`'s
  predicates, `TyBody`/`resolve`, `valueEq`'s mutual block and the
  restated two-layer proofs arrived; a reduction was not the goal and
  is not claimed.

## 8. Deviations from the plan's sketch, and owed items

Deviations (each within G-C2 as ruled; none a design decision outside
it — the gate text speaks of an index-keyed, well-founded `TypeEnv`
with an `Accepted` clause at decode, which is what landed):

1. **The entry keeps its `TypeId`** (`Array (TypeId × TypeDef)`, not
   §1.1's `Array TypeDef`): gc-visible panic texts and the observation
   channel need the key, and interface identity and method-set records
   are name-keyed by the plan's own design. The key is never used to
   resolve a `Ty.defined`.
2. **`GoValue.struct` and `Loc.field` keep `TypeId`** — value-level
   tags, as §1.1's `Loc.field (base) (tid : TypeId) (f)` already has it.
   Making them indices would have changed readout rendering paths and
   dedup-visible values for no reasoning benefit.
3. **The reserved prefix** is not in the plan. It is forced by the
   runtime-error sentinel (§2) and makes explicit two conventions the
   machine already relied on by name (`struct{}`, `$runtime.Error`).
   The runtime-error entry borrows `TypeDef.opaqueDecl`, which plan I1
   intends to move out of the IR; when I1 lands, the entry becomes an
   import-boundary fact of `ProgramCtx` like every other opaque
   declaration. Owed to I1.
4. **`normalize`/`isNormal`/`convert` are type-directed (two layers),
   not value-structural** as §3.C2 phrased it; only `valueEq` is
   value-structural. Reason: the cross-walk lemmas (`isNormalForTy_sound`,
   `defaultValue_ok_of_normalize_ok`) relate `normalize` to `default`
   (type-only), and lockstep descents keep them unconditional — a
   value-structural `normalize` against a bound-structural `default`
   would need `WellFounded` as a hypothesis in machine lemmas the state
   does not carry. `convert` has no value recursion at all.
5. `TypeEnv.resolve`/`TyBody` are new (the plan named no resolver);
   `typeIndexExhausted` names the refusal every index layer shares.

Owed (rowed here; none blocks the gate):

- **G6 §4's two `Interface.lean` facts, recorded, not implemented:**
  (a) `GoValue.typeDesc (idx : TypeIdx)` — the one `GoValue`
  constructor the reflect facility needs (a `reflect.Type` is a Go
  value the program can hold and compare; `==` on it is index equality
  now that `Ty.defined` is positional); (b) `FieldDef.tag : String` —
  struct tags as part of struct identity, with `structTagCompatible`
  comparing WITHOUT tags (a fidelity fix riding G6-5, on a BUGS.md
  Cases line when it lands; a twin pin move). Both are §1.1 deltas the
  pin must admit; G6's memo designs against the C2 shape landed here
  (`kind`/`elemTy`/`numField`/`fieldInfo` are table lookups, not fuel
  towers). T1 (`reflectlite`) may start now.
- **Bound irrelevance as a theorem:** `types.WellFounded → i < b → i <
  b' → defaultValueAt types b i = defaultValueAt types b' i` (and the
  same for the other `…At` layers) — the statement that makes "the
  bound is not fuel" a kernel fact rather than a section-note argument;
  by strong induction on `i` with a `deps`-congruence lemma for each
  type layer. Not proved here; the reasoning repo's interface wave (I5)
  is where it pays.
- **`Accepted P` as one Prop** (plan §1.9) bundling `typeDefs.
  WellFounded ∧ typeDefs.hasReservedPrefix = true` with the decoder's
  other clauses; `run_refusal_free` stays the theorem target it was.
  Note on the second conjunct (audit R15/R2): `hasReservedPrefix` is a
  Bool whose evaluation compares a long string (the opaque entry's
  reason text), so it is NOT `decide`-cheap — the driver seams evaluate
  it as a Bool at run time, never by `decide`; the Prop form for the
  bundle is `= true`, and a kernel proof of it on a concrete table
  should go by `rfl`/`native`-free evaluation of the Bool, not by
  `decide` on a `String` equality. Owed with the bundle.
- **The `<unknown type index i>` marker class** (audit fix R10):
  `goTypeNameForMessage` (Ops.lean) and `Ty.dynamicName` (Value.lean)
  render an index the table lacks as a VISIBLE marker inside a text
  that can reach a gc-visible message or the observation channel with
  status `ok`. Refusing by name instead needs the two renderers to
  become `Except` (26 call sites for the first; the observation
  renderer `goValueJson` and its five consumers for the second) — well
  over the 20-line budget the audit set, so it is documented, not
  changed: the class is DECODE-UNREACHABLE (every `named` reference is
  minted an index < `types.size`, and no step mints an index) and
  reachable only from a hand-built `Program`; a consumer that wants the
  refusal can assert `∀ i, (Ty.defined i) mentioned ⇒ i < types.size`
  as part of the owed `Accepted` bundle, which is where it belongs.
- **The `$unresolved-type-index.<i>` marker key** (audit fix R1):
  `methodCarrierKey?` maps an unresolvable `.defined` index to this
  key so that every record query REFUSES (no record can carry a `$`
  key: the frontend mints record keys from Go identifiers and import
  paths, the decoder synthesizes only `struct{}`); `none` is again
  exactly the language's non-carriers. Same decode-unreachability;
  pinned (`C2/R1`).
- `TypeEnv.lookupName?` is a linear scan (two consumers, never on a
  `Ty.defined` path); an index by name is a cheap later addition.
- The `struct{}` escapes (`emptyStructAssignable`) still compare
  `.key == "struct{}"` on value tags; they could compare the tag against
  `types[0]`'s key. Cosmetic; unchanged.
- `scripts/check-frontend-pins` verifies the twin's BYTES, not the order
  contract directly; the contract's guards are the frontend self-check,
  the frontend unit tests and the decoder. A one-line order assertion
  in the pin script is a cheap belt-and-braces addition if wanted.
- The name → index map is built with `Std.HashMap` in the decoder
  (outside the core; the decoder is already `partial` for JSON descent).

## 9. Landing record

Lane `c-arc-c2` off `main` @ `b77f3298`. Code commit `3a229bae`
(core + decoder + frontend + twin re-pin + records); this note and the
evidence dir follow in the records commit (SHA in the evidence README).

Gate: `scripts/capped scripts/ci --diff` at the clean tip `166244f7`
(code `3a229bae`, refusal-class fix `f33d3092`, records `166244f7`) —
**RESULT: PASS**; `differential coverage summary: cases=3498 pass=3252
fail=246`; `baseline diff FULL (3498/3498, no regression)`; `negative
baseline diff (no regression)` (394); `frontend pins (realized init-order
deviation + twin wire = pinned bytes)` ok; eval tests 165 ok; the record
made on a clean tree. Tail verbatim in
`docs/evidence/2026-09-05_c-arc-c2/ci-diff.txt`. The final records
commit (this note's landing text, the evidence README's gate and trace
sections, the G6 memo pointer) is docs-only on top of the gated tip.
Branch-complete; the audit ask is the coordinator's to pose; merge/push
are the [USER]'s. Merge-protocol step 5a applies at the train: this
branch touches `tools/nativefrontend/wire.go`'s emission surface
(`emit.go`/`typeorder.go`, the typeDefs table) and
`GoLean/NativeToIR.lean`, so the train runs `scripts/ci --slow` at the
merged tip and refreshes the certification record.

**Twin-pin merge hazard — a rule for the train (audit fix R4).** The
twin pin `baselines/pins/twin-chdriver.wire.json` is a 483k-line
pretty-printed JSON. This branch's re-pin permutes the `types` table;
the `e13-b` branch's re-pin (`d531a225…`, the probe-count change) edits
`funcs` bodies. The two edits touch NON-OVERLAPPING regions, so `git
merge`/`rebase` combines them CLEANLY into a syntactically valid JSON
pin that NO frontend ever emitted (the permuted table with the other
branch's bodies is a consistent wire only if both frontends' changes
compose exactly — which is the thing to be checked, not assumed).
`scripts/check-frontend-pins` catches the discrepancy only if the gate
runs at the rebased tip and nobody "resolves" a pin FAIL by re-pinning
without re-emitting. Rule: **after every landing that touches the pin,
the pin is a FRESH EMIT from the merged frontend over the merged
subject — never a merge result** — and the train records the emit's
hash and the structural diff against the pre-merge pin (the recorded
reason is the union of the two lanes' reasons). The same rule applies
to any two lanes that re-pin concurrently.

**Audit fix round (2026-09-05, [AGENT] worker).** The adversarial audit
returned FIX-FIRST (no blocker; BEFORE/AFTER byte-identical on every
probe, all 1730 corpus packages at the wire level, and the gate; twin
pin reproduced; the decoder refuses all seven malformed classes by
name). Dispositions: R1 core (marker key, pinned), R2 core + CLI
(driver-seam refusal, `Program` default, pinned), R3 records (plan §1.1
carries the two G6 facts and the landed `typeDefs` type), R4 this
section, R5a-c this note + `Syntax.lean` docstring, R6 five stale
references fixed (§10), R7 §7 cross-reference (no duplicate row), R8
evidence re-recorded (`frontend-tests.txt` full run with command line;
`ci-diff.txt` the fix-round gate tail with its `cases=` line and
`git_dirty`; `excluded.tsv` per-row reasons; `trace-diff.sh` prints both
sides' totals untruncated, `trace-diff.txt` re-recorded from the same
artifacts), R9 §7, R10 §8 (documented; plumbing > 20 lines), R11 four
born rows (§7), R12 frontend (`checkTypeDefOrder` duplicate refusal +
unit test), R13 §10, R14 §0, R16 `StepFn.lean` (the unrenderable-abort
refusal names the payload's dynamic type by its table key beside the
`repr`). Incidental: BUG-103 filed (array-target conversions, a machine
gap the R11 rows detected; red-first row, §7/§10). Rebased onto `main` @ `426af905` first (records-only ahead;
clean). The fix-round gate tail and the tally follow in `ci-diff.txt`
and the evidence README (recorded after the run, at the clean tip).

## 10. Records touched

`docs/2026-09-04_reasoning-surface-plan.md` §5.4 (G-C2 BRANCH-COMPLETE
line); `TODO.md` (C-arc list); `docs/2026-09-03_design-hygiene-arc.md`
(landing table row); `docs/2026-09-03_grumpy-professor-review.md` (C2
status line); `docs/2026-07-18_totality-fuel-decision.md` (superseded
note for the type-directed ops); `docs/2026-08-11_latitude-inventory.md`
(R16 text: `tySizeAlign`, no fuel); `docs/BUGS.md` and
`docs/2026-08-11_essence-of-go-doctrine.md` (`tySizeAlign` pointer);
`scripts/check-frontend-pins` (re-pin history); `Platform.lean`
docstring; `docs/2026-09-04_g6-reflect-design.md` §4.5 (C2 status line
and the pointer to where its two §1.1 facts are recorded — audit fix
R13). Audit fix round additions: `docs/2026-09-04_reasoning-surface-plan.md`
§1.1 (`typeDefs : Array (TypeId × TypeDef)` as landed, with the C2
reference; the two OWED interface deltas `GoValue.typeDesc (idx :
TypeIdx)` and `FieldDef.tag : String` recorded in the pinned document
itself, [AGENT] 2026-09-05 — audit fix R3); the five stale references to
deleted names fixed (audit fix R6): `GoCore/StateEqb.lean` header (cited
`Ty.eqbFuel`/`GoValue.eqbFuel`), `GoCore/MachineEqb.lean` header and
`GoCore/SyntaxEqb.lean` header (the `GoValue.eqbFuel` mould),
`GoCore/Machine.lean` `snapshotEntriesSelfNormalizedList` docstring
(`isNormalForTyFuel`), and the live contract note
`docs/2026-08-10_method-set-record-contract.md` §2 (the method-set base
"after `resolveDefinedAliases`" → alias-free `Ty`, `.defined idx` with
the key read back, the R1 marker); `baselines/native-full.tsv` (5 born
rows — 4 PASS + 1 red-first FAIL — header block; tally 3498 → 3503 =
3256 PASS / 247 FAIL, re-derived by awk);
`Corpus/coverage/exec/structs/decl-order-reversed/` (new); `docs/BUGS.md`
(BUG-103 filed: array-target conversions, open, Cases line
`structs/decl-order-reversed/conversion-array-target`; numbered after
the unmerged `e13-b` lane's BUG-101/102 so the train has no collision);
`docs/language-coverage-ledger.md` §2 Conversions row (BUG-103 named);
`docs/evidence/2026-09-03_hygiene-a-series/choice-trace/trace-diff.sh`
(both sides' totals). No PASS → non-PASS flip: the one FAIL row is BORN
red on BUG-103's Cases line.
