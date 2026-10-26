# Review: equality, identity and ordering across value kinds vs gc (2026-10-26)

Independent review, [AGENT] reviewer, branch `review/equality-1026` off main `6e05137a`
(train 19: BUG-133's fix, `valueEq`'s pointer arm now `l.canon == r.canon`). Question
put to the review: where else does the machine decide equality, identity or ordering of
Go values, and is each decision correct with respect to Go? Method: 75 small Go programs
run on both sides (gc go1.26.5 at `/usr/local/go`, the oracle pin, with the corpus
runner's environment `GO111MODULE=off GODEBUG=panicnil=0`; the machine through
`.tmp/nativefrontend` → `golean native-json-run --function run`, and for the race
probes `golean coverage-observations --expect-status <race|ok>` over every schedule
against `go run -race`). The programs are committed beside this file under
`docs/reviews/2026-10-26-equality-probes/<name>/main.go`, with the two runners
`probe.sh` / `race.sh` (path-independent; prerequisites in their headers) so a fix lane
can turn any of them into corpus rows.

## Verdict

- **No wrong answer found.** Across every kind and route probed (§3), every value the
  machine PRINTED or RETURNED agrees with gc, every run-time panic gc raises
  (uncomparable dynamic type, unhashable key, failed assertion) the machine raises with
  the same text, and every race-location conflict/non-conflict agrees with gc's detector
  on every enumerated schedule. BUG-133's fix holds on the routes it names.
- **One real gap in BUG-133's own neighbourhood (F1, medium):** the whole-struct VALUE
  reached through a struct-pointer conversion — `*pb` for `pb := (*B)(&a)` — refuses
  by name on every value-level route (`==`, `!=`, assignment, boxing, map key, `switch`,
  parameter passing, type assertion of the box) and the whole-struct STORE through it
  (`*pb = B{…}`) refuses too; 18 probes, all `stuck`, gc prints the answer. Only the
  leaf-field routes work (the routes BUG-133 and triage L7 pinned). The refusal is
  honest but carries the wrong status word: `stuck` is defined as «the program is
  outside the lowering contract (a frontend bug)», and these programs are legal Go the
  frontend lowered correctly. BUG-133's survey sentence «ACCESS through either spelling
  already worked» is true for leaf fields only.
- **One legal spelling refused by the frontend (F2, low):** untyped `nil` as the LEFT
  operand of `==`/`!=` (`nil == p`, `nil != err`) refuses as «basic type untyped nil»
  for every operand kind; `p == nil` lowers.
- The dedup engine's representation-based state equality (`GoValue.eqb`) is safe (F4).
- Everything else that did not agree was a refusal by name the charter already records
  (§4).

## 1. The mechanism, as read (what decides equality, identity, ordering)

| decision | definition | note |
|---|---|---|
| Go `==`/`!=` at a static type | `valueEq` (`GoLean/GoCore/Ops.lean:3719`), reached from `applyStrictOp`'s `.eqCmp ty`/`.neqCmp ty` (`Machine.lean:460-461`) | value-directed walk at the operand type; the frontend carries the operand type on the wire (`emitBinary`, `tools/nativefrontend/emit.go:8684-8703`: the LEFT operand's static type, or the interface side's when one side is boxed) |
| bool / int | `l == r` on the payload | int kinds are normalized at every arithmetic site (`IntKind.normalize`), so wrap-around compares as Go |
| float | `FloatBits.feq64`/`feq32` (`FloatBits.lean:390,452`) over `fcmp64` (`:378`: NaN → unordered, ±0 equal) | never bit equality |
| string | derived `BEq GoString` (byte array); ordering `GoString.compare` (`Value.lean:873`, bytewise) | |
| ordering `< <= > >=` | `valueLess`/`valueAtMost`/`valueGreater`/`valueAtLeast` (`Ops.lean:3999-4030`): ints by `Int`, floats by `flt64`/`fle64` with `>`/`>=` as the SWAPPED `<`/`<=` (not negations), strings bytewise | |
| `min`/`max` | `Machine.lean:668-690`: floats through `floatMinMaxBits` (`Ops.lean:275`, gc/amd64's MINSD/POR lowering: NaN propagates, `min(-0,+0) = -0`), everything else a `valueLess` fold | |
| pointer | `l.canon == r.canon` (`Ops.lean:3760`; `Loc.canon` `:2841` erases the static `TypeId` of every `.field` step) | BUG-133's fix |
| channel | derived `BEq ChanValue` = the payload cell's `Option Loc` (`Value.lean:753`); direction is static (`Ty.chan dir`), not in the value | `rch == ch` is reference identity; `any(ch) == any(rch)` is the dynamic-type rule |
| map / slice / func | comparable only against nil; non-nil vs non-nil is `stuck` (unreachable from typed Go) | |
| interface box vs box | `Ops.lean:3816`: dynamic `Ty` first (`Ty.eqb`, `Value.lean:618`, structural; defined types positional), then `tyUncomparable` (`:1605`, three-valued, fail-closed on unknown) → the `comparing uncomparable type` panic, then `valueEq` at the dynamic type | |
| struct | `Ops.lean:3840-3860`: operand tags must equal the context's `TypeId` (the canonical `struct{}` assignability escape excepted), then `valueEqFields` per declared field | blank fields: the frontend never emits the operand (`emitBlankFieldZero`, `emit.go:7962`; a call operand refuses, `:7976`), so a blank field is always its zero value and compares equal — Go's rule by construction |
| array | `valueEqList` elementwise | |
| map key search | `mapEntryIndex?` (`Ops.lean:3985`): `checkKeyHashable` (`:3973`, Go's hash-time panic with both texts, `hashPanicMessage` `:3962`) then a LINEAR `valueEq` scan; insert REPLACES the key (`mapAssignValue.plan`, `Machine.lean:369`, the E10 pin) — which is what gc's `NeedKeyUpdate` does for float/interface/string keys, so `-0.0` overwriting `0.0` is observed identically | |
| type assertion / type switch | `typeAssertValue` (`Ops.lean:3499`): `dynTy == targetTy` structurally; interface targets through `dynamicImplementsInterface`; the frontend lowers a type switch to comma-ok asserts in source order (`emitTypeSwitch`, `emit.go:5066`) | |
| expression `switch` | `emitSwitch` (`emit.go:5251`): a tag temp, then `==` tests in textual order (first match), mixed interface/non-interface cases boxed as in `emitBinary` | |
| race / unseq «same location» | `locOverlap` (`Ops.lean:2817`, path prefix on CANONICAL keys), `ShadowKey.overlap` (`:2891`) | |
| dedup state equality | `GoValue.eqb` (`Value.lean:971`): fully structural (bit equality on floats, representation equality on `Loc`) | §F4 |
| observation sets | canonical-JSON structural equality (`CLI.lean:2006`), NaN canonicalized on BOTH sides before emission (`CLI.lean:388-401`, `tools/coverageharness/main.go:647-652`) | |

## 2. Findings

### F1 — the struct VALUE through a tag-compatible pointer conversion refuses on every value route, as `stuck` (medium)

Programs: `p31-misc` (the first sighting), `p33a`–`p33s` (one route each; `p33h` was an
illegal program of mine and is not kept), `p33k` the control. Header shared by all:
`type A struct{ X, Y int }; type B struct{ X, Y int }`, `a := A{1, 2}; pb := (*B)(&a)`.

| probe | program (the decisive line) | gc | GoLean |
|---|---|---|---|
| p33a | `*pb == B{1, 2}` | `true` | `stuck`: `left struct equality type mismatch: expected main.B, got main.A` |
| p33b | `B{1, 2} == *pb` | `true` | `stuck`: `right struct equality type mismatch: …` |
| p33c | `x := *pb; x == B{1, 2}` | `true true` | `stuck`: `struct value type mismatch: expected main.B, got main.A` |
| p33d | `any(*pb) == any(B{1, 2})` | `true false` | `stuck` (left struct equality …) |
| p33e | `m := map[B]int{{1, 2}: 1}; m[*pb]` | `1 1` / `2 1` | `stuck` (struct value type mismatch) |
| p33f | `switch *pb { case B{1, 2}: }` | `matched` | `stuck` |
| p33i | `pb.I == In{1}, *pb == OB{In{1}, 2}` (nested struct field) | `true true` | `stuck` (expected main.OB, got main.OA) |
| p33j | `eqB(*pb)` with `func eqB(b B) bool` | `true` | `stuck` (struct value type mismatch) |
| p33l | `*pb != B{1, 3}, pb == (*B)(&a), (*A)(pb) == &a` | `true true true` | `stuck` |
| p33m | `as := []A{{1, 2}}; pb := (*B)(&as[0]); *pb == B{1, 2}` | `true` | `stuck` |
| p33p | `var i any = *pb; i.(A) / i.(B); switch i.(type)` | `false true 1` / `B` | `stuck` |
| p33s | `*pb = B{9, 9}` alone (prints before/after) | `before` `after` | `before`, then `stuck`: `struct value type mismatch: expected main.A, got main.B` |
| p33g/n/o/q/r | anything after that store | the stored values | the same `stuck` at the store |
| p33k (control) | `b := B(a); b == B{1, 2}, A(b) == a, any(b) == any(B{1, 2})` | `true true true` | `true true true` |

Mechanism. A `.base` load returns the cell's value with its MINT tag (`loadLoc`,
`Ops.lean:2522`: the `.base` arm returns the cell verbatim; only the `.field` arm applies
`structTagCompatible`, `:2514`), so `*pb` evaluates to `.struct main.A …` at static type
`B`. Every value-level consumer then compares the tag against the static type and
refuses: `valueEq`'s struct arm (`Ops.lean:3850`, `leftType != name`), and
`normalizeStructValueWith` (`Ops.lean:2320`) at assignment, boxing, map-key
normalization, parameter binding and the store (`storeLoc`, `:2742`, writes through `writeAt` at the
cell's DECLARED type, so a `B`-tagged value refuses into an `A` cell — the store never
happens, which is why no retagging of the cell and no wrong answer follow). Triage
L7 (2026-08-19, `docs/bugfix-arc-log.md` family 5) relaxed exactly the three FIELD
checks (`fieldGet`, `loadLoc`/`storeLoc` field arms) and said so; the whole-struct
value was never in scope, and the corpus pins only the leaf routes
(`structs/tag-pointer-conversion`: `b.X++; a.X*10 + b.X`;
`pointers/identity-tag-alias/write-through`: `b.X = 9; a.X`).

Why it matters. (i) Status word: `Stop.status` defines `stuck` as «the program is
outside the lowering contract (a frontend bug)» (`docs/semantics-overview.md` §8); these
are legal programs the frontend lowered correctly — the refusal names the right cause
but the wrong class, and a reader of a `stuck` row would look for a frontend defect that
is not there. (ii) BUG-133's survey states «ACCESS through either spelling already
worked (the review's write-through control)»; the control is a leaf field, and the
whole-struct spelling — the most natural use of a converted pointer (`*pb`, passing
`*pb` to a function, `t := *pb`) — refuses. The record should say so. (iii) The fix shape
is small and keeps the «cell keeps its mint tag» invariant: at a `.base` load whose
STATIC type is a defined struct tag-compatible with the cell's tag, RETAG the loaded
value to the static type (Go's semantics: the value of `*pb` has type `B`); at a `.base`
store of a tag-compatible value, store it under the cell's mint tag. The same
`structTagCompatible` decides both. Non-struct pointer conversions (`(*MyInt)(&x)`,
`(*Arr)(&arr)`, named string/float/bool/func/chan/slice, `p34-nonstruct-ptr-conv`)
already agree on every route, because those values carry no tag.

Severity: medium — a refusal, never a wrong answer; legal Go in the fix's immediate
neighbourhood; misclassified status; an overstated record.

### F2 — untyped `nil` on the left of `==`/`!=` refuses by name (low)

Program `p15-nil-left` (`nil == p`, `nil != np`, `nil == m`, `nil == s`, `nil == f`,
`nil == i`, `nil == ch`, `nil == e` for pointer, map, slice, func, interface, channel,
error; also `case nil == np:` in a tagless switch). gc prints the eleven lines; the
machine: `unsupported` — `frontend-quarantined: basic type untyped nil`. Also the first
version of `p14-chan-eq` (`nil == nc`).

Mechanism: `emitBinary` sets `operandType` from `e.typeOf(operandTypeExpr)` with
`operandTypeExpr = b.X` unless the RIGHT side is the interface (`emit.go:8684-8703`);
for a bare `nil` left operand go/types records `untyped nil`, and `emitType` has no arm
for it (`tools/nativefrontend/wire.go:868`, `unsup("basic type %s", b)`). The right
operand's type is the Go type of the comparison and is always available. Honest
refusal; one `if`/`else` away. Severity: low (a rare spelling; `p == nil` is the idiom).

### F3 — refusals by name that are honest and already recorded (informational)

| probe | refused thing | status / text | recorded where |
|---|---|---|---|
| p25-complex | `complex128` `==` | `unsupported`: `basic type complex128` | complex is outside the modeled kinds |
| p27-reflect-sort | `reflect.DeepEqual`, `sort.Ints` | `unsupported`: `package "reflect" surface not modeled` (the first blocker) | stdlib register (neither package is source-through) |
| p28-maps-pkg | `maps.Equal` | `unsupported`: `package "maps" surface not modeled` | same |
| p29-blank-call | positional struct literal with a CALL in a blank-field slot | `unsupported`, the BUG-130 text | BUG-130 ruling |
| p30 (first cut) | a generic instantiated at a `chan` type argument | `unsupported`: `type argument outside the mangling surface: *types.Chan` | mono.go's mangling surface |
| p12/p13/p17 (first cuts) | `r.(error)` on a RECOVERED runtime error | `unsupported`, the BUG-009/BUG-053 text | BUG-009/BUG-053 (every probe that inspects a recovered runtime panic hits it; not equality-specific — the texts were checked uncaught instead, §3) |
| BUG-133's FR-13 | `(*struct{ X int })(&a)` | frontend refusal `anon-struct` | FR-13 |

### F4 — `GoValue.eqb` as the dedup engine's state equality is safe (informational)

`GoValue.eqb` (`Value.lean:971`) is strictly structural: bit equality on floats,
representation equality on `Loc` (static `TypeId` included), positional `Ty.eqb` on
box types. It is therefore FINER than Go `==` (two in-flight pointers `&a.X`/`&b.X`
under two typeIds, or two NaN payloads, are two states). A dedup merge is sound exactly
when merged states have identical futures; structural identity guarantees it, and a
finer relation can only split states (more exploration), never merge distinct ones or
drop a member. The observation SET is deduplicated by canonical JSON (`CLI.lean:2006`)
with NaN canonicalized before emission on both sides (`CLI.lean:388-401`,
`coverageharness/main.go:647`), pointer results refused unseeded and rendered as
canonical paths when seeded — so the finer state equality does not surface as a
spurious extra member either. `p37-float-readout` shows the readout form (`bits`): NaN
is the canonical `0x7FF8000000000000` and `-0.0` its sign bit, as documented (R7).

### F5 — zero-size address identity (informational, a latitude)

`p16-ptr-identity`: `new(struct{}) == new(struct{})` and `&z1 == &z2` for `[0]int`
print `false` on BOTH sides here; the spec leaves it open (R15, pinned as never-same).
Not a finding; recorded so the table is complete.

## 3. Coverage: what was probed, by kind × route

Legend: ✓ = both sides agree on every printed value / panic text / race verdict;
R = refusal by name (see F1–F3); — = not applicable in Go. Routes: `==` (also `!=`),
`<` (ordering), `sw` (expression switch on the kind), `key` (map key: insert, lookup,
delete, len, range), `box` (interface box of the kind, incl. mixed-operand comparison),
`gen` (`==` inside a generic function instantiated at the kind), `ts` (type switch /
assertion), `race` (two spellings of one cell must conflict; two cells must not).

| kind | `==` | `<` | `sw` | `key` | `box` | `gen` | `ts` | race | probes |
|---|---|---|---|---|---|---|---|---|---|
| bool, named bool | ✓ | — | ✓ | ✓ | ✓ | | | | p07, p34 |
| int8/16/32/64, uint8..64, uint, uintptr, rune, byte, named ints; overflow, wrap, MinInt/-1, shifts ≥ width | ✓ | ✓ | ✓ (incl. `1<<63` on uint64) | ✓ | ✓ (int vs int64 vs MyInt vs alias) | ✓ | ✓ (A/B/int, alias C) | | p05, p11, p17, p20, p31, p34 |
| float64/float32: NaN, ±0, ±Inf, denormals, 0.1+0.2, float32 widening | ✓ | ✓ (NaN unordered all four ways) | ✓ (NaN never matches, `-0` matches `0`, interface tag) | ✓ (NaN: distinct entries, never found, survive range-delete, `clear` removes; ±0 merge and the key UPDATES to the newer spelling; float32; struct and array keys with NaN/±0; interface keys) | ✓ (`any(1.0)==any(1)` false, float32 vs float64 boxes) | ✓ (NaN, ±0) | | | p01, p02, p03, p09, p26, p30, p31, p37 |
| `min`/`max` builtins (float NaN/±0 incl. 3-ary, float32, ints, strings, int8 ends, uint64 high bit) | ✓ | | | | | | | | p04 |
| string, named string: bytewise order, non-ASCII, invalid UTF-8 from `[]byte`, embedded NUL, `string(rune(-1))`, substrings, concatenation | ✓ | ✓ | ✓ | ✓ (from bytes, substrings, concatenation, `\xff`, empty, NUL, runes; byte mutation after keying) | ✓ (string vs MyStr) | ✓ | | | p06, p11, p21, p34 |
| pointer, named pointer: fresh allocs, `new`, globals, array/slice elements, struct vs first field, closures over one var, conversions | ✓ | — | ✓ | ✓ | ✓ (dynamic-type rule `*A`≠`*B`) | ✓ (`&a.X`/`&b.X` through the alias inside a generic) | ✓ | ✓ (r09, r10) | p16, p30, p34, p36 |
| pointer identity DYNAMICS: append spill vs in-cap, Go 1.22 per-iteration loop/range vars, shared outer var, block var, closures over the loop var, append aliasing within cap, `copy` | ✓ | | | | | | | | p36 |
| channel: same `make`, two `make`s, direction conversions (`rch == ch`, `sch == ch`), nil, MyChan | ✓ | — | ✓ | ✓ (`map[chan int]`, `map[<-chan int]`, `map[any]`) | ✓ (`any(ch)≠any(rch)`) | R (chan as a generic type argument) | ✓ (`chan int` vs `<-chan int` cases) | | p14, p17, p34 |
| map / slice / func / named ones: nil only; `s[:0]`, `[]int{}`, `append(nil…)`, `[]byte("")` | ✓ | — | | — | ✓ (typed-nil box ≠ nil) | | ✓ | ✓ (r12 map read vs write) | p10, p18, p31 |
| interface: nil vs typed nil (pointer, func, slice, map, chan, error, named pointer), mixed operand boxing both sides, identical boxes, `error` vs `any` | ✓ | — | ✓ (mixed-type cases, `case nil`) | ✓ (mixed dynamic types, nil key, pointer keys, ±0/NaN boxes) | ✓ | ✓ | ✓ | | p10, p11, p13, p20, p24, p30 |
| interface with UNCOMPARABLE dynamic type: slice, map, func, named slice, struct/array containing them, inside struct fields and array elements, reached vs short-circuited, `switch` tag/case, nil-dyn vs slice (no panic) | ✓ (panics where gc panics, `false` where gc says false) + exact texts `runtime error: comparing uncomparable type []int` / `main.WithSlice` | | ✓ | ✓ (both hash texts: `runtime error: hash of unhashable type T` on insert/lookup/delete of a non-empty map, `hash of unhashable type: T` on an empty or nil map; struct and array keys holding the box) | | ✓ | | | p12, p12m-*, p13, p13m-*, p30 |
| struct (named): equal, converted `A(B{})`, pointer/interface/chan/array/string fields, nested, embedded, map keys, `switch` | ✓ | — | ✓ | ✓ | ✓ (`any(A)≠any(B)`) | ✓ (`Pair[int]` vs `Pair[int64]`) | ✓ | ✓ (r03, r04, r07, r08) | p08, p19, p22, p30, p32 |
| struct with BLANK fields and padding, `struct{}` vs named empty, `Empty{} == struct{}{}` | ✓ | | ✓ | ✓ | ✓ | | | | p08, p31 |
| struct VALUE through a tag-compatible POINTER conversion (`*pb`) | **R (F1)** | | **R** | **R** | **R** | | **R** | ✓ (r10, through fields) | p31, p33a–s |
| array: nested, of strings/pointers/structs/bools/bytes, `[0]int`, `[100]int`, named array, map keys, `switch` | ✓ | — | ✓ | ✓ | ✓ (`any(Arr)≠any([2]int)`) | | ✓ | ✓ (r01, r02, r11) | p19, p34 |
| function-local types: same name in two functions, two blocks, a loop body, shadowing a package type, two closures, nested closure | ✓ (distinct types; same declaration same type) | | | ✓ | ✓ | | ✓ | | p32, p35 |
| type switch / assertion: identical underlying named types, alias, interface cases with identical method sets, `case nil`, multi-type clause binding, panic texts (`interface conversion: interface {} is main.B, not main.A`; `main.B is not main.I1: missing method M`) | | | | | | | ✓ | | p17, p17m-* |
| expression switch: evaluation order of case lists with side effects, first-match on duplicate non-constant cases, `fallthrough`, tagless, init statement, untyped constant tag | ✓ | | ✓ | | | | | | p20 |
| `errors.New` identity (two `New`s unequal, sentinel through a call), error map keys, `errors.Join`/`Unwrap` | ✓ | | ✓ | ✓ | ✓ | | | | p24 |
| stdlib comparison functions: `slices.Sort` (floats with NaN first and `-0`/`+0` order, strings bytewise), `slices.Equal`/`Index`/`Contains`/`Compare`/`Max`/`Min`/`IsSorted`/`BinarySearch`, `cmp.Compare`/`Less` with NaN, `strings.Compare`/`EqualFold`/`Contains`/`HasPrefix`/`Index`, `bytes.Equal`, `min` on strings | ✓ | ✓ | | | | | | | p23 |
| `reflect.DeepEqual`, `sort.Ints`, `maps.Equal` | R (F3) | | | | | | | | p27, p28 |
| complex | R (F3) | | | | | | | | p25 |
| race «same location»: whole array vs element, distinct elements (int and bool), whole struct vs field, sibling fields, slice views of one element, slice views of distinct elements, promoted vs explicit embedded path, promoted vs sibling, two pointers to one cell, struct-pointer conversion alias, map read vs write | | | | | | | | ✓ 12/12 on every enumerated schedule | r01–r12 |
| `nil` as the LEFT operand | **R (F2)** | | | | | | | | p15 |

Not probed (outside the modeled surface or the frontend's by-name refusals, noted for the
record): `unsafe`/`uintptr` address observation; `sync` struct `==` (refused by design,
`Ops.lean:3833`); multi-package type identity (`a.T` vs `b.T`: keys are package-PATH
qualified — `qualifiedTypeName`, `emit.go:5915`, through `pkgQualifier`, `tools/nativefrontend/identity.go:95`, which returns `pkg.Path()` — so no collision is possible by
construction; not run).

## 4. Disposition pointers for a fix lane

- F1: retag at the `.base` load/store under `structTagCompatible` (or, if the owner
  prefers to keep the refusal, rename its class to `unsupported` and say «whole-struct
  value through a struct-pointer conversion» in the text); add rows from `p33a`–`p33s`
  (they are single-statement programs: `pointers/identity-tag-alias` is the natural
  family); amend BUG-133's survey line.
- F2: in `emitBinary`, take `operandType` from the right operand when the left is
  untyped nil; row from `p15`.
- The remaining probes are green controls; the fix lane may keep any as rows (float map
  keys with the key-update observation `p03`, interface map-key panics `p13`/`p13m-*`,
  the race-location pairs `r01`–`r12`, the per-iteration identity dynamics `p36` are
  the ones the corpus seems thinnest on — I did not audit the corpus for duplicates).
