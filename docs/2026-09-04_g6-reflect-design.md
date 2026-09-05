# G6 — a modeled, layout-free `reflect` subset as a machine facility, or its permanent exclusion (design memo, 2026-09-04)

**Status:** DESIGN MEMO, [AGENT]-authored; nothing was decided in it.
Every decision is a numbered gate in §6 — **all five RULED [USER]
2026-09-05 as recommended ((a) each), relayed** (§6 ruling record).

**Commission (cited as relayed, not firsthand):** gate G6 of the stdlib
boundary memo (`docs/2026-09-03_stdlib-boundary-design.md` §5) — «(a)
commission a design memo (what `reflect` exposes of the type system vs of
gc's layout; which of `fmt`, `errors.Is/As`, `sort.Slice`,
`encoding/json`, `reflect.DeepEqual` it unblocks …)» — RULED [USER] Mike
2026-09-03 as recommended («(3) agree, go ahead with the plan»), with the
timing «after the first two slices land»; slices 1 and 2 landed 2026-09-03
(`docs/stdlib-admission-register.md`, slice log). The coordinator's
relayed framing for this memo (2026-09-04): the two top-level goals are
(1) a highly accurate Go semantics and (2) reasoning via an iris-lean
layer that is the customer's build. Both are weighed below.

**Repo state read:** main @ `ac45aedd`; oracle pin go1.26.5
(`deps/go/src`); the register's primitive class at 0/2 with both slots
spoken for (`print`/`println` = slice 3; the `internal/strconv` float-bits
casts posed in the slice-2 evidence README, register lines 160-175).

**Scope of this memo:** docs only. No code, no gate, no baseline, no
corpus change. Numbers below are re-derived by the commands in Appendix A
against the pinned checkouts; where a number is a static approximation it
says so.

---

## 0. Summary

1. **Demand.** Four stdlib consumers stand behind every refused
   `reflect` in the two measured targets, and they want very different
   amounts of it. `errors.Is/As` wants 8 `reflectlite` members over 4
   ops. `encoding/binary.Write/Read/Size` wants 14 members. `fmt`'s
   `printValue` wants ~25 members plus `internal/fmtsort`. `encoding/json`
   wants ~50 members including construction and mutation (`New`,
   `MakeSlice`, `MakeMap`, `Set*`, `Grow`, `SetLen`, `Addr`) and STRUCT
   TAGS — which the wire strips today (`Ops.lean:1125-1136`, "the wire
   strips tags"). cedar-go: 42 `json.Marshal/Unmarshal` call sites behind
   45 `MarshalJSON/UnmarshalJSON` methods (62 declarations, 31 sole, in
   the widened `lower-diagnose` census), 17 `errors.Is` + 3 `errors.As`
   (9-10 declarations), 1 `binary.Write`, 0 direct `reflect` outside test
   support. gotest in-scope slice: 71 of ≈1,015 files import `reflect`;
   35 use only the layout-free read tier (19 `DeepEqual` files), 9 need
   `Method/Call`, 27 need construction/headers/addresses and stay refused
   under any option here. `%v`-family verbs appear in 94 files.
2. **What `reflect` is.** A run-time view of two things the machine
   ALREADY HAS as data: the type table (`Program.typeDefs`, wire
   `TypeDef`s, `MethodSetRecord`s) and the structural value representation
   (`GoValue.interface dyn v` carries the canonical dynamic `Ty`;
   `GoValue.struct tid fields` carries the TypeId and the fields IN
   DECLARATION ORDER with names). A layout-free facility adds no semantic
   choice; it exposes existing machine data through Go-typed values. The
   layout-bound remainder (`Size/Align/Offset`, `UnsafePointer/
   UnsafeAddr`, `Value.Pointer`, `SliceHeader/StringHeader`, `MakeFunc`,
   `Call`'s ABI) is out of language and REFUSES BY NAME.
3. **Options.** (A) source-through the real `reflect` — impossible as
   written: 316 `unsafe.` sites, 267 `internal/abi` references, 42
   linknames, 66 body-less declarations in 8,740 lines; `TypeOf` IS an
   `unsafe.Pointer` cast of the eface (`abi/type.go:181-182`).
   `reflectlite` is the same shape in miniature (40 `unsafe.` sites in
   1,201 lines). (B) a machine FACILITY: ~24 machine ops in five groups,
   over which `reflect`'s API is re-implemented as OUR Go text at the
   library path — this is neither an overlay (cap 12, single-expression)
   nor a primitive (cap 2, both taken): it needs a NEW register class,
   "facility", and therefore a [USER] ruling. Full: 15-20 sessions across
   three arcs. (C) `reflectlite` only (9-10 ops, no wire change): 3-4
   sessions, unblocks `errors.Is/As` and `sort.Slice`. (D) permanent
   exclusion: cedar-go's JSON leg and every `%v` over a composite stay
   refused; the DRT harness's JSON-out leg cannot run.
4. **Reasoning surface.** A facility is a DERIVED notion over the
   consumer interface's own `Program.typeDefs` + `GoValue`: `typeOf` is
   the interface-box projection (total); kinds/fields/elements are
   `TypeDef` lookups by ORDER; `implements` is `dynamicImplementsInterface`
   (exists, `Ops.lean:908`). Two interface deltas are unavoidable: `Ty`
   becomes a program-visible value (`GoValue.typeDesc`), and `FieldDef`
   gains a `tag`. Both are §1.1 facts the plan already flagged (§4.3).
   One dependency is sequencing: method-set reads (`NumMethod`,
   `Implements` through promotion) must be built AFTER G-P changes the D2
   contract, or built twice.
5. **Recommendation ([AGENT]):** admit the facility as a new register
   class (G6-1), scoped `reflectlite`-first (G6-2), sequenced after C2 and
   G-P (G6-3); make `fmt` source-through over the facility the retirement
   path for the six remaining shims and let slice 4 be the smaller
   `strconv`-leaves step only (G6-4); `encoding/json` as the third arc,
   with its struct-tag wire change and three `sync` overlays named up
   front (G6-5).

---

## 1. Demand census

### 1.1 Method

Static counts over pinned text: `deps/go/src` @ go1.26.5 for what each
stdlib consumer calls; `deps/cedar-go` (non-test `.go`) for cedar-go's
call sites; `deps/go/test` files whose first line is exactly `// run`
(≈1,015 — the triage's in-scope slice was 1,013 single-file plain-`// run`
cases at 670d3351; this memo's filter does not exclude the 2 multi-file
edge cases, so counts are ±2) for the gotest slice. The triage's own
artifacts (`artifacts/gotest/results.tsv`) are not on this machine; the
triage's "25 reflect" is a FIRST-refusal count (a file that refuses on
`println` first is not in it), so the 71 below is the honest upper bound
of what `reflect` alone gates. Commands: Appendix A.

### 1.2 The consumers, one by one

**(a) `errors.Is`/`errors.As` — `internal/reflectlite`.** `errors/wrap.go`
at the pin uses exactly:

| line | call | facility op it needs |
|---|---|---|
| :50 | `reflectlite.TypeOf(target).Comparable()` | `typeOf`, `comparable` (a `Ty` predicate — exists in spirit: the machine already decides comparability for `==`) |
| :109 | `reflectlite.ValueOf(target)` | `valueOf` (box projection) |
| :110-111 | `typ.Kind() != Ptr`, `val.IsNil()` | `kind`, `isNil` |
| :115 | `targetType.Kind() != Interface`, `Implements(errorType)` | `kind`, `implements` |
| :123 | `TypeOf(err).AssignableTo(targetType)` | `assignableTo` |
| :124 | `targetVal.Elem().Set(ValueOf(err))` | `elem` (pointer deref → addressable Value), `set` (store through Loc) |
| :152 | `var errorType = reflectlite.TypeOf((*error)(nil)).Elem()` | `typeOf` + `elem` on a TYPE (pointer elem) — a package initializer, today poisoned per declaration (register, "Residual channels") |

Eight members; four op groups (type-of, type inspection, value read,
value write). `Set` is the only mutation and it is a store through an
addressable `Value` obtained from a pointer — `Loc`-shaped already.

**(b) `sort.Slice`/`SliceStable`/`SliceIsSorted` — `reflectlite.Swapper`
+ `ValueOf(x).Len()`** (`sort/slice.go:25-53`). `Swapper` at the pin is
`unsafe`-typed byte swapping over the slice's backing array by element
size (`reflectlite/swapper.go`); its layout-free equivalent is
`index(i)`/`index(j)`/`set` on the slice Value — 3 ops, and the panic text
`reflect: slice index out of range` (`swapper.go:25,29,70`). The facility
version is the SEMANTICS of Swapper (swap two elements), not its
realization.

**(c) `encoding/binary.Write/Read/Size`** (`binary/binary.go`): `Indirect`
×4, `TypeOf` ×5, `ValueOf` ×6, `Kind` ×7, `Len` ×7, `Field` ×5, `Index`
×4, `Elem` ×4, `Type` ×5, `Int/Uint/SetInt/SetUint` ×4 each, and the
kind constants (`Bool/Int*/Uint*/Float*/Complex*/Array/Slice/Struct/
Pointer`). Read-tier plus `SetInt/SetUint` on addressable elements; no
construction. Also reaches `var structSize sync.Map` (FR-24: poisoned
cell, readers quarantined) — so `binary.Write` needs FR-24's fix OR an
overlay of `dataSize`'s cache before reflect is even the question.
cedar-go: 1 site (`types/record.go:35`, the hash writer; census §9.2-9.3).

**(d) `fmt`'s `%v` family — `fmt/print.go` `printValue` (:767-960) +
`internal/fmtsort`.** Package-level: `ValueOf` ×6, `TypeOf` ×4,
`MakeSlice` ×1 (for `%x` on byte arrays — `:1000`-ish `fmtBytes`),
`UnsafePointer` kind ×2; Value methods: `Kind` ×10, `Type` ×9,
`IsValid` ×5, `IsNil` ×4, `Elem` ×4, `Len/Index` ×3 each, `Field` ×2,
`NumField` ×1, `CanInterface` ×2, `Interface` ×2, `Int/Uint/Float/
Complex/Bool/Bytes/String`, `CanAddr` ×1, and `UnsafePointer()` ×2
(`fmtPointer :550-556` and the depth-0 `&{…}` test `:918`). Method
detection (`Formatter`, `GoStringer`, `error`, `Stringer` — `handleMethods
:622-700`) is by TYPE ASSERTION on `p.arg`, not by reflect; it becomes
reflective only through `printValue :769` (`CanInterface() → Interface()
→ handleMethods`) for nested fields. `fmtsort.Sort` (`internal/fmtsort/
sort.go`, 154 lines) needs `MapRange`, `Kind`, the numeric/string/bool
readers, `NumField/Field`, `Len/Index`, `Elem`, `IsNil`, and
`Value.Pointer()` for pointer/chan keys and for INTERFACE keys (`:127`:
concrete types ordered by the address of their `*rtype` — layout-bound,
§5.1).

Static verb census, gotest in-scope slice: `%d` 506, `%v` 339, `%s` 183,
`%x` 94, `%q` 77, `%p` 32, `%g` 28, `%f` 19, `%#v` 14, `%T` 9 occurrences;
94 files use a `%v`/`%#v`/`%T`/`%p` verb; 14 files use `%T` or `%p`. How
many `%v` operands are composites is not decidable without the type
checker (the frontend's `fmtdesugar.go` decides it per site at emit time
and refuses the reflective remainder by name, `:210`); the honest bound is
"≤ 94 files, ≥ the 82 fmt first-refusals of the triage minus the
statement-position `Print*` ones". cedar-go: `%v` 65, `%T` 16, `%+v` 2
sites (mostly `fmt.Errorf` messages over `types.Value`s — composites).

**(e) `encoding/json` (v1 text at the pin; `v2_*.go` and `v2_inject.go`
are `//go:build goexperiment.jsonv2`, off in the oracle's build).**
`encode.go` + `decode.go`, exact `reflect` demand grouped:

| group | members (occurrences) |
|---|---|
| type inspection | `Type` (48), `Kind` (46), `Elem` (34, both Type and Value), `Key` (6), `NumField` (1), `Field` (5 — `Type.Field(i)` for `StructField.Name/Tag/Anonymous/IsExported/Index`), `Implements` (13 — `Marshaler`, `TextMarshaler`, `Unmarshaler`, `TextUnmarshaler` via `reflect.TypeFor[…]()` ×6 and `PointerTo` ×6), `NumMethod` (6 — the `any`-vs-non-empty-interface test), `Name` (4), `String` (12, error texts), `Bits` (1), `Comparable`-free |
| value read | `IsNil` (20), `IsValid` (6), `IsZero` (6, `omitzero`), `Len` (8), `Cap` (1), `Index` (3), `Int/Uint/Float/Bool/Bytes/String` readers, `Interface` (5), `CanInterface` (1), `CanAddr` (3), `Addr` (6 — pointer-receiver `MarshalJSON`), `MapRange`/`Next`/`Value` (1 each), `UnsafePointer` (2 — `ptrSeen` cycle detection at `:773`/`:856`, keyed by ADDRESS) |
| value write | `Set` (10), `SetZero` (3), `SetString` (3), `SetInt/SetUint/SetLen` (2 each), `SetFloat/SetBool/SetBytes/SetMapIndex` (1 each), `Grow` (3), `CanSet` (2), `OverflowInt/OverflowUint/OverflowFloat` |
| construction | `reflect.New` (8), `MakeSlice` (1), `MakeMap` (1), `Zero` (via `SetZero`), `reflect.TypeAssert` (7 — go1.26's generic type assertion on a Value) |
| non-reflect library dependence | `sync.Map` ×2 (`encoderCache :379`, `fieldCache :1329`), `sync.Pool` (`encodeStatePool :313`), `sync.OnceValue` (`:399`), `fmt` (18 sites, error texts), `encoding` (`TextMarshaler`), `encoding/base64`, `unicode/utf16`, `strconv`, `strings`, `slices`, `cmp`, `bytes`, `math`, `unicode/utf8` |

≈50 distinct reflect members, all four groups, plus STRUCT TAGS
(`StructField.Tag.Get("json")`, `tags.go`), plus three `sync` sites that
the out-of-scope list refuses (`sync.Map`, `sync.Pool`; `OnceValue` is
pure `sync.Once`, modeled). cedar-go: `json.Marshal` 21 + `json.Unmarshal`
21 + `json.NewDecoder` 3 + `json.MarshalIndent` 1 call sites; 45
`MarshalJSON`/`UnmarshalJSON` method declarations; census §3.4: 38
declarations (21 sole) at the case scope, 62-64 (31 sole) at the widened
`lower-diagnose` scope (§11.2, §10.3).

**(f) `reflect.DeepEqual`** (gotest: 19 occurrences in 19 files — the
single most common `reflect` use in the classic suite; cedar-go: 1, in
test support). Read tier only (`Kind`, `Len`, `Index`, `NumField`,
`Field`, `MapKeys`/`MapIndex`, `Elem`, `IsNil`, `Interface`-free
comparisons) plus cycle detection by pointer identity (`deepequal.go`'s
`visited` map keyed by `unsafe.Pointer` pairs — `Loc` identity suffices;
§4.3).

### 1.3 The tiers and what each unblocks

| tier | ops (cumulative) | stdlib members | unblocks |
|---|---|---|---|
| **T1 read-lite** | `typeOf`, `kind`, `elemTy`, `comparable`, `isNil`, `implements`, `assignableTo`, `elem` (pointer deref), `set`, `len`, `index` | `reflectlite`: `TypeOf`, `ValueOf`, `Type.{Kind,Elem,Comparable,Implements,AssignableTo,String,Name,PkgPath,NumMethod}`, `Value.{Kind,Elem,IsNil,IsValid,Len,Set,Type,CanSet}`, `Swapper` | `errors.Is/As` (cedar-go 20 sites / 9-10 decls; gotest: ubiquitous in real code, not measured), `sort.Slice*` |
| **T2 read-full** | + `numField`, `field`, `fieldName`, `fieldEmbedded`, `mapKeys`/`mapRange` (E9 site), `mapIndex`, `numMethod`, `methodName`, the scalar readers, `interface` (re-box) | `reflect.{TypeOf,ValueOf,DeepEqual}`, `Type.{Field,NumField,Key,Len,Method,NumMethod}`, `Value.{Field,Index,MapRange,MapIndex,MapKeys,Int,…,Interface,CanInterface}` | `DeepEqual` (gotest 19 files), `binary.Read/Write/Size` read paths, `fmt printValue` minus `%p` (the ≤94 gotest files' `%v` composites; cedar-go's 65 `%v`), `fmtsort` minus pointer/chan/interface-typed keys — **35 gotest files** use nothing beyond T2 |
| **T3 write+construct** | + `setInt/…`, `setMapIndex`, `setLen`, `grow`, `new`, `zero`, `makeSlice`, `makeMap`, `addr`, `canAddr`, `fieldTag` (WIRE CHANGE) | `Value.Set*`, `Addr`, `Grow`, `SetLen`, `reflect.New/Zero/MakeSlice/MakeMap`, `StructTag.Get/Lookup`, `TypeFor`, `PointerTo`, `TypeAssert` | `encoding/json` Marshal/Unmarshal (cedar-go 42 call sites / 45 methods / 62 decls), `binary.Write/Read` write paths |
| **T4 method call** | + `methodByName`, `call` (a `funcVal` invocation through the machine's own call path) | `Value.Method/MethodByName/Call`, `Type.Method` | 9 gotest files (`reflectmethod1-7.go` family) — NOT needed by any of the four stdlib consumers; `fmt` reaches methods through `Interface()` + assertion |
| **excluded** | — | `MakeFunc`, `StructOf/ArrayOf/SliceOf/MapOf/FuncOf/ChanOf`, `NewAt`, `SliceAt`, `Value.Pointer/UnsafePointer/UnsafeAddr/InterfaceData`, `Type.Size/Align/FieldAlign/Offset`, `SliceHeader/StringHeader`, `Select/Send/Recv/TrySend/TryRecv/Close`, `Value.Seq/CanSeq` (range-over-func, FR-12) | 27 gotest files stay refused by name |

---

## 2. What `reflect` IS, semantically

### 2.1 Two tables the machine already has

`reflect` in gc is a typed view of `abi.Type` descriptors that the
compiler emits and the runtime hands out through the eface/iface headers.
In the machine the same information is already first-class data:

- **The type table.** `Program.typeDefs` (wire `TypeDef`: `struct
  (fields : Array FieldDef)`, `alias`, `interfaceDef (methods : Array
  MethodSig)`, the identity-bearing named-over-non-struct form —
  `Syntax.lean:48-70`); `FieldDef = {name, typ, embedded}`
  (`Syntax.lean:15-25`); `MethodInfo = {name, funcId, recv}` and
  `MethodSetRecord = {key, coverage}` (`:471-499`; the D2 contract,
  `docs/2026-08-10_method-set-record-contract.md`). `Ty` is structural
  with `.defined id`/`.interface id` for named types (`Value.lean:535`).
- **The value representation.** `GoValue.interface (dynamic : Ty) (value)`
  carries the CANONICAL dynamic type of every boxed value (`Value.lean:
  862-869`); `GoValue.struct (typeId) (fields : Array (String × GoValue))`
  carries the TypeId and the named fields in declaration order; `array`,
  `slice {base, offset, len, cap}`, `map {base}`, `chan {base}`, `addr
  loc`, `funcVal fid captured`, the scalars with their kinds. Addressability
  is `Loc` (`base | field base tid name | index base i`).
- **Rendering.** `Ty.dynamicName` (`Value.lean:625`) already renders
  `reflect.Type.Name()`-shaped strings for the observation channel
  ("chan<- int", "map[string]int", unqualified named types); the
  qualified `Type.String()` spelling ("main.T") is `TypeId.key` (the
  `TypeId.unqualified` projection exists, `:518`).
- **Predicates.** `dynamicImplementsInterface` (`Ops.lean:908`),
  `firstUnsatisfiedMethod?` (`:869`), `satisfiesMethodSig` (`:759`),
  `concreteMethodForDynamic?` (`:704`) — interface satisfaction against
  the recorded method set, failing closed on `exported`-only coverage;
  `Ty.eqb` (`Value.lean:615`); `defaultValue` (`Ops.lean:1400`, the zero
  value at a type = `reflect.Zero`/`New`'s content); `mapIterCandidates`
  (`Machine.lean:1324`, the E9 site `MapKeys` must consume).

So a layout-free `reflect` is NOT new semantics. Every answer it gives is
a function of `(Program, GoValue, Store)` that the machine already
computes somewhere for its own purposes. What is new is (i) making those
answers AVAILABLE TO THE PROGRAM as Go values, and (ii) the API text of
`reflect` that turns them into gc's exact observable behaviour (texts,
panics, orders).

### 2.2 Layout-free vs layout-bound

| layout-free (definable from the two tables) | layout-bound / out of language (refuse by name) |
|---|---|
| `Kind` (a total function of `Ty`: `.int k ↦ Int/Int8/…`, `.defined id ↦` kind of the underlying, `.interface ↦ Interface`, `.sync ↦ Struct`) | `Size`, `Align`, `FieldAlign`, `StructField.Offset`, `Bits` on non-numeric — `Platform` facts the doctrine keeps out of the semantics (`docs/2026-08-11_essence-of-go-doctrine.md`; the plan's §1.11 keeps `Platform` out of reflect deliberately) |
| `Name`, `PkgPath`, `String` — from `TypeId.key` | `PkgPath` of an UNEXPORTED field of an IMPORTED type when the record is `exported`-only (D5) — refuse, as `firstUnsatisfiedMethod?` does today |
| `NumField`, `Field(i).{Name, Type, Anonymous, IsExported, Index}` — by ORDER in `TypeDef.struct` | `Field(i).Offset` |
| `Field(i).Tag` — NOT ON THE WIRE today (`Ops.lean:1128` "the wire strips tags"); a `FieldDef.tag : String` twin pin move (§4.4) | — |
| `Elem` (pointer/slice/array/map/chan elem `Ty`), `Key`, `Len` (array), `ChanDir`, `NumIn/In/NumOut/Out/IsVariadic` (from `.funcType`) | `In`/`Out` of a `funcVal` whose `Ty` the box did not carry (closures boxed as `any` — the frontend boxes with the static type, so this is available; refuse if a box arrives with `.unsupported`) |
| `NumMethod`, `Method(i).Name`, `MethodByName` (from `MethodSetRecord` + `MethodInfo`; ORDER = gc's sorted-by-name order, which the facility must reproduce, §5.4) | `Method(i).Func` as a callable — T4, and its `Call` is the machine's own call path (definable) but the ABI-bound `MakeFunc`/`Call` internals are not |
| `Implements`, `AssignableTo`, `ConvertibleTo`, `Comparable` — `Ty` relations the machine decides for `==`, assertion and conversion already | — |
| `ValueOf(x).Kind/Len/Cap/Index/Field/Elem/IsNil/IsZero/Int/…/String/Bool/Bytes/Interface` — projections of `GoValue` (+ `Store` for `Elem` through `addr`) | `Value.Pointer()`, `UnsafePointer()`, `UnsafeAddr()`, `InterfaceData()`, `%p` — address VALUES are `Loc`s, not integers; the machine's addresses are not gc's (BUG-070's mechanism; `docs/2026-09-04_reasoning-surface-plan.md:1138` "`%p` printing is not modeled") |
| `MapKeys`/`MapRange`/`MapIndex` — `mapIterCandidates` + the E9 choice site | — |
| `CanSet`/`CanAddr`/`Set*`/`SetMapIndex`/`SetLen`/`Grow`/`Addr` — a `Value` obtained through `Elem` of a pointer or `Index` of a slice is a `Loc`; `Set` is `storeLoc`; the flag algebra (`flagAddr`, `flagRO`) is the facility's own bookkeeping | `SetPointer`, `Grow`'s CAPACITY policy (it reuses `growslice`'s size classes — R2 append-spill latitude; the machine's envelope contains it, membership rows) |
| `New`, `Zero`, `MakeSlice`, `MakeMap`, `MakeChan`, `Append`, `Copy` — `defaultValue` + the machine's own `make`/`new`/`append` paths | `NewAt`, `SliceAt`, `StructOf/ArrayOf/SliceOf/MapOf/FuncOf/ChanOf` (they MINT types at run time — the type table would stop being a constant of the program, which §1.1 of the plan makes a type fact via B7; `ArrayOf`/`StructOf` also compute layout), `MakeFunc` (ABI trampoline), `Select/Send/Recv` (the channel module's operations exist but `Select` over a dynamic case array is a new machine step shape — defer with FR-class row, not exclude forever) |
| `DeepEqual` — a type-directed recursion over two values with `Loc`-identity cycle detection | — |

The "refuse by name" texts follow the existing convention: `unsupported
"reflect: <Member> is layout-bound (address/size/offset) and out of the
modeled language"` at the machine op, so a library body reaching it
refuses at run time naming the member (H-3 stub shape, `emit.go`).

### 2.3 One thing that is neither: type identity of anonymous structs

35 gotest files refuse today on anonymous non-empty struct types
(triage table). `reflect` makes them more visible (`reflect.TypeOf(struct{
A int }{})`), and `StructOf` mints them. A facility does not change the
frontier: an anonymous struct that the FRONTEND can name (it mints a
`TypeId` for every struct type it lowers) is a `TypeDef` like any other,
and `StructOf` stays excluded. Recorded so the arc does not inherit it as
a surprise.

---

## 3. Options

### 3.1 Option (A) — source-through the real `reflect`/`reflectlite`

Not possible as written. The census at the pin:

| package | lines (non-test) | `unsafe.` sites | `internal/abi` refs | linknames | body-less decls |
|---|---|---|---|---|---|
| `reflect` | 8,740 | 316 | 267 | 42 | 66 |
| `internal/reflectlite` | 1,201 | 40 (`type.go` 19, `value.go` 21) | throughout | 0 | 0 |

`reflect.TypeOf(i any)` is `toType(abi.TypeOf(i))` (`reflect/type.go:
1383-1385`); `abi.TypeOf` is `*(*EmptyInterface)(unsafe.Pointer(&a))`
(`internal/abi/type.go:181-182`) — the eface header read. `ValueOf` is
`unpackEface` (`value.go:158-164`), the same cast. Every `Value` method is
then pointer arithmetic on `v.ptr` guided by `abi.Type` fields (`Size_`,
`PtrBytes`, `Kind_`, `Equal`, `GCData`); `Field(i)` adds `field.Offset`
to `v.ptr`. There is no purity to census: the package's SUBJECT is the
layout. The stdlib memo's Appendix A already recorded `reflect` as
"1/42/69 (8,694 lines)" own-asm/linkname/bodyless and marked it as not
resolved by (A) (§2.1.1 table, `reflect` row). The overlay class cannot
carry it (cap 12 single-expression sites; this would be hundreds of
multi-line substitutions), and a substitution needs an UPSTREAM twin,
which does not exist (there is no `reflect` implementation in the Go tree
that does not read `abi.Type`).

**What (A) DOES contribute:** the API SURFACE and its DOCUMENTED
behaviour (panic texts, `String()` formats, method order, `DeepEqual`'s
rules) are the (b)-pins for whatever replaces the internals — the same
`godoc:` anchor scheme G3 ruled (`docs/spec-sources.md`, library docs at
the pin). And `reflect`'s own tests (`all_test.go`, 8,000+ lines) are a
free conformance corpus for a facility-backed `reflect`: run them under
`go run` against the machine as differential rows where they stay inside
the layout-free subset.

### 3.2 Option (B) — a machine FACILITY with `reflect` re-implemented over it

**Shape.** Two parts:

1. **Machine ops** (`GoCore`): a small op family over `(Program, GoValue,
   Store)`, total, each either answering or refusing by name. Inventory
   (T1-T3, T4 in brackets):

   | group | ops | count |
   |---|---|---|
   | type-of / descriptors | `typeOf : GoValue(interface box) → TypeDesc`; `typeDescOf : Ty → TypeDesc` (for `TypeFor[T]`, `PointerTo`, `Elem` on a type — the frontend emits the static `Ty` as a literal); `kind`, `elemTy`, `keyTy`, `arrayLen`, `chanDir`, `funcSig`, `nameOf` (Name/PkgPath/String) | 9 |
   | struct/method table | `numField`, `fieldInfo i → (name, ty, embedded, tag, exported)`, `numMethod`, `methodInfo i → (name, sig, funcId)` (gc's sorted order) | 4 |
   | type relations | `implements`, `assignableTo`, `convertibleTo`, `comparable` | 4 (all reuse existing `Ops` predicates) |
   | value read | `valueOf` (box → (ty, value)), `deref` (addr → Loc-bearing Value), `fieldAt`, `indexAt`, `lenOf`, `capOf`, `isNil`, `mapKeys` (E9 consumption), `mapIndex`, `rebox` (`Interface()`) | 10 |
   | value write / construct | `store` (`Set` through a Loc, with the assignability check), `setLen`, `grow`, `setMapIndex` (incl. delete on zero Value), `newAt ty` (`reflect.New`), `zeroOf ty`, `makeSlice`, `makeMap` | 8 |
   | [method call] | [`callMethod (recv, name, args)` — the machine's own call path; `Value.Call` on a `funcVal`] | [1-2] |

   ≈35 ops named this finely, ≈24 if the type-descriptor group is one
   op with a selector and the scalar readers are one. This is the same
   order as the `sync` op family. The doctrine's TCB constraint (no
   library semantics in `stepFn`) is respected: every op is a
   PROJECTION or a STORE, none is a formatting or encoding rule; the
   `reflect` behaviour (what `DeepEqual` compares, what `%v` prints,
   what a `json` tag means) lives in the Go text of part 2.

2. **The `reflect`/`reflectlite` packages re-implemented AS GO SOURCE
   against those ops** — OUR text at the library path, replacing
   `deps/go/src/reflect/*.go` wholesale for the loader (the API,
   doc-comments and panic texts copied from the pin; the bodies rewritten
   from `abi.Type` arithmetic to op calls). The ops surface in Go as a
   fenced intrinsic package (say `internal/goleanreflect`) that only the
   substitute `reflect` may import (loader-enforced, the way `unsafe` is
   refused elsewhere), so no user program can reach an op directly.
   Size estimate for the layout-free surface: `reflectlite` ≈300 lines,
   `reflect` T1-T3 ≈1,200-1,500 lines (a third of upstream's 8,740:
   `type.go`'s API half, `value.go`'s API half, `deepequal.go` nearly
   verbatim, `makefunc.go`/`abi.go`/`swapper.go`/`asm` gone).

**Why this is like the bytealg twins and unlike them.** Like: one
package's contract, a second implementation of the same API validated by
the same differential. Unlike: the twin is OURS. The register today has
no class for "our text, at a library path, more than one expression":
overlay is capped at 12 SINGLE-expression sites and byte-checked against
upstream (the substitute `reflect` has no upstream bytes to check
against); primitive is capped at 2 machine ops of library origin (both
spoken for: `print`/`println` slice 3; float-bits posed); intercept is
empty by ruling; shim is frozen and shrinking. **A reflect facility is
therefore a NEW register class — "facility": a machine op family (the
core half, trusted surface) + a substitute library package (the text
half, untrusted-but-pinned, validated by differential rows and by
upstream's own tests).** Naming it and capping it (one facility today;
any second one re-opens G8) is a [USER] ruling; this memo cannot admit it
(G6-1).

**Why not "raise the primitive cap to N".** The primitive class was
shaped for ONE op with a spec anchor (`print`'s realized format). A
reflect facility is 24-35 ops that only make sense together, plus a
package of text. Counting it as 24 primitives makes the cap meaningless;
counting it as 1 hides 1,500 lines of our text. A class with its own
description ("ops that project existing machine data + the API text that
consumes them; no op may compute a library RESULT") is the honest shape.

**Cost (sessions, [AGENT] estimate).** Core ops T1-T2: 3-4 (mostly
plumbing over existing predicates; the E9 consumption in `mapKeys` and
`Ty`-as-value are the two design points). T3 write/construct + the
struct-tag wire change (twin pin move; `structTagCompatible` audit,
§4.4): 3-4. Substitute `reflectlite` + `reflect` text: 3-4. Register
class + `check-stdlib-register` extension + corpus rows (panic texts,
`DeepEqual` matrix, upstream tests as rows): 2-3. **Total for the
facility alone: 11-15 sessions.** `fmt` and `json` over it are separate
arcs (§3.5, G6-4/G6-5). This is a LARGE arc — comparable to the sync
package arc — and the reason the [USER] gated it.

### 3.3 Option (C) — `reflectlite` only, first

T1 exactly: 9-10 ops (`typeOf`, `typeDescOf`, `kind`, `elemTy`,
`comparable`, `implements`, `assignableTo`, `valueOf`, `deref`, `isNil`,
`lenOf`, `indexAt`, `store`, `nameOf`), a ≈300-line substitute
`internal/reflectlite` (its exported surface is 40 members incl. test
hooks; `errors` and `sort` use 10), no wire change (no tags), no E9
consumption (no maps), no construction. Unblocks `errors.Is/As` (cedar-go:
20 call sites, 9-10 declarations, 5 sole; the `errorType` initializer
stops being poisoned) and `sort.Slice/SliceStable/SliceIsSorted`
(gotest: `sort.Ints` ×2 rows were the measured sort demand; `sort.Slice`
is ubiquitous in real code). It ALSO forces every structural decision of
(B) — `Ty`-as-value, the facility register class, the intrinsic-package
fence, the flag algebra for addressability — on the smallest surface,
which is the same "mechanism first, observable second" order G9 chose.
**2.5-4 sessions.** Its residual: `fmt`'s reflective remainder, `json`
and `DeepEqual` stay refused by name exactly as today.

### 3.4 Option (D) — permanent exclusion, like `unsafe`

Declare `reflect` and `internal/reflectlite` out of the modeled language.
Coverage cost, measured:

| consumer | cost |
|---|---|
| `errors.Is/As` | cedar-go: 9-10 declarations, `PartialPolicy`/`tryPartial`/`Validator.*` refuse at run (census §3.5 item 9); every real Go program using `errors.Is` refuses — and `fmt.Errorf("%w")`'s wrapped errors become unobservable through the idiomatic path |
| `encoding/json` | cedar-go: 62 declarations (31 sole), the entire codec, the DRT harness's JSON-out leg (census §7); the refinement target (`isAuthorized`) itself is `json`-free, so the PROOF is not blocked — the export of the JSON drivers is |
| `fmt` `%v` over composites, `%T`, `%+v`, `%#v` | ≤94 gotest files partly; cedar-go's 65 `%v` + 16 `%T` sites (error messages — reached only on error paths, but a refusal on an error path is a refusal of the row) |
| `reflect.DeepEqual` | 19 gotest files; the classic suite's preferred equality oracle |
| `sort.Slice*`, `binary.Read/Write/Size` | measured small (cedar-go 1 `binary.Write`), ubiquitous in real code |

What (D) buys: nothing structural is spent; the frontier stays where G5
put it (frontend `fmt` specialization at static types). What it costs
the two goals: goal (1) "highly accurate semantics" loses nothing in
FIDELITY (refusals are honest) but a large slice of REACH; goal (2) loses
the JSON-driver export that the cedar-go refinement's harness wants
(§4.4 of the plan, item 6) but not the theorem. (D) is defensible if the
customer's programs are `json`-free; cedar-go is not.

### 3.5 Comparison

| | (A) source-through | (B) full facility | (C) reflectlite-first | (D) exclude |
|---|---|---|---|---|
| feasible | NO | yes | yes | yes |
| trusted-surface delta | — | +24-35 projection/store ops, `GoValue.typeDesc`, `FieldDef.tag` | +10 ops, `GoValue.typeDesc` | none |
| our text | — | ≈1,500 lines at `reflect/` (pinned, differential-validated, upstream tests as rows) | ≈300 lines | none |
| register | — | NEW class (G6-1) | NEW class (G6-1) | none |
| unblocks | — | `errors.Is/As`, `sort.Slice`, `DeepEqual`, `binary.*`, `fmt` %v (with G6-4), `json` (with G6-5) | `errors.Is/As`, `sort.Slice` | nothing |
| sessions | — | 11-15 (+4-6 fmt, +5-7 json) | 2.5-4 | 0 |
| when | — | after C2 + G-P (§4.5) | after C2; before or after G-P (method-set reads absent in T1) | — |

---

## 4. Interaction with the reasoning surface (`docs/2026-09-04_reasoning-surface-plan.md` §1)

### 4.1 `typeOf` — total, and already there

`reflect.TypeOf(i any)` and `ValueOf(i any)` take an INTERFACE. Every
call site boxes its argument at the static type (the frontend's
`wrapInterfaceConversion`), so the op sees `GoValue.interface dyn v` or
`GoValue.nil` — `typeOf` is the projection `dyn`, total, and `TypeOf(nil)
= nil`/`ValueOf(nil) = Value{}` (the `IsValid() == false` case) falls out.
No `typeOf : GoValue → Ty` over UNBOXED values is needed or definable
(an unboxed `GoValue.int 3 .int` does not know whether it is `int` or
`type MyInt int` — the box does). Inside the facility a `Value` carries
its `Ty` alongside the `GoValue`/`Loc` (as gc's `Value` carries `typ`),
and every derived `Value` gets its `Ty` from the parent's `TypeDef`
(`Field(i).typ`, `Elem`'s `elem`), never from the payload. That is why
"layout-free" and "type-directed" are the same property (§4.3 of the
plan, item (c)).

### 4.2 `Ty` becomes a program-visible value — a §1.1 delta

A `reflect.Type` is, in gc, an interface value whose dynamic type is
`*reflect.rtype` and whose payload is a pointer to the descriptor. In
the facility, `rtype`'s single field is a machine type descriptor. That
needs ONE `GoValue` constructor — `typeDesc (t : Ty)` (or `(idx :
TypeIdx)` after C2) — the plan's §4.3 already names it as "(a)". It is a
Go value in the same sense `chan` is: the representation of an opaque
runtime object the program can hold, compare (`==` on `reflect.Type` is
descriptor identity → `Ty.eqb`), and pass. It does NOT reintroduce the
payload constructors A3 removed (it carries no addresses, no frontend
provenance); the plan's "Go values only" (§1.1) should be read as "values
a Go program can hold", which a `reflect.Type` is. **Record it in §1.1
now**, whatever G6 decides, so the pin admits it (the plan says so, §4.3
last sentence).

### 4.3 Definable downstream — a derived notion, not an axiom

Every T1-T3 op is a function of `(Program.typeDefs, Program.methods,
GoValue, Store)`, i.e. of what §1.1-1.2 export:

- `kind`, `elemTy`, `numField`, `fieldInfo`, `nameOf`: lookups in
  `typeDefs` — with C2's well-founded `TypeEnv` these are structural
  recursions (aliases inlined, `defined` resolved by index), which is why
  the plan sequences C2 BEFORE the G6 memo lands (§4.3: "or the memo
  designs against fuel"). This memo lands before C2; it designs against
  the C2 SHAPE and says so: with fuel-indexed lookups the facility's ops
  would be fourteen more towers, and `DeepEqual`'s and `printValue`'s
  recursions would carry `fuel = 1024` into every downstream lemma.
- `implements`/`assignableTo`: `dynamicImplementsInterface` +
  `Ty.eqb` + the interface/channel-direction/untyped-nil rules the
  machine already applies at assignment and assertion. The consumer can
  state `implements P t I ↔ ∀ m ∈ I.methods, ∃ f, methodOf P t m = some f
  ∧ sig f = m` from `Program.methods` alone.
- `valueOf`/`fieldAt`/`indexAt`/`deref`/`store`: projections of
  `GoValue` and `Mem.load/store` at a `Loc` — under C1 they are
  `Loc`-addressed accesses and appear in the trace like any other
  (a `reflect` write to a struct field races with a direct write to the
  same field — the detector sees both, for free).
- `mapKeys`: `mapIterCandidates` + a `PickRecord` at the E9 site — the
  consumer's `Perm`-of-draws law (G-MAPITER) covers `MapKeys` order with
  no new axiom, because it IS a map iteration.
- `DeepEqual`'s and `json`'s pointer-identity cycle checks: `Loc`
  equality (`visited : Set (Loc × Loc × Ty)`; `ptrSeen : Set Loc`) —
  definable; the `unsafe.Pointer` in upstream is only how gc names a
  `Loc`.

**Where it is NOT derivable (and must refuse):** `PkgPath`/`Name` of
unexported members of IMPORTED types whose record is `exported`-only (D5,
`Ops.lean:900-905` already refuses this class); `Value.Pointer()` and
kin (no integer address exists); `fmtsort`'s interface-key order (§5.1);
`Method(i)`'s index order for a type whose PROMOTED methods are not in
the record — which is exactly the G-P interaction:

### 4.4 Two wire/contract interactions

**(i) G-P and method sets.** Today the D2 contract says a type's record is
its FULL method set, promoted methods included, synthesized as wrapper
`Func`s by the frontend (`emit.go:5467`). G-P (RULED [USER] 2026-09-04,
plan §3.P) changes that: records carry DECLARED methods, the core
resolves promotion through the `embedded` chain. `NumMethod`,
`Method(i)`, `MethodByName`, and `Implements` through a promoted method
therefore read DIFFERENT data before and after G-P. Build the facility's
method-table group after G-P, or write it twice. T1 (`reflectlite`) has
`NumMethod` but `errors`/`sort` never call it (they call `Implements`,
which already goes through `firstUnsatisfiedMethod?` and will inherit
G-P's chain walk) — so (C) can precede G-P; T2+ should not. **G6-3.**

**(ii) Struct tags.** `FieldDef` has no tag; the frontend strips them
(`Ops.lean:1125-1136` docstring), and struct-type IDENTITY on the machine
is `FieldDef`-list equality (`structTagCompatible`). Go's rule: tags are
part of a struct type's identity (spec §Type identity: "identical …
tags"), and conversion is allowed between struct types identical
IGNORING tags (spec §Conversions). Adding `tag : String` to `FieldDef`
(twin pin move; the frontend has `types.Struct.Tag(i)` for free) makes
identity strict and requires `structTagCompatible` to compare WITHOUT
tags — i.e. the field's current name becomes accurate. Anonymous struct
types (the only ones whose identity is decided structurally rather than
by `TypeId`) are refused today, so no row flips; but it is a fidelity
FIX riding a reflect arc, and it belongs on a BUGS.md Cases line when it
lands. `encoding/json` cannot work without it (`tags.go`, `StructField.
Tag.Get("json")`). **G6-5** carries it.

### 4.5 Sequencing consequence

C2 (well-founded `TypeEnv`, ruled) → (C) `reflectlite` facility (any
time after C2; register class ruled) → G-P (ruled, after C1) → T2/T3 +
`DeepEqual` → `fmt` over the facility (G6-4) → tags + `json` (G6-5).
The plan's critical path (§5.1: (iii) → B7 → C1 → P → C3 → I5) is not
lengthened: (C) is a parallel lane after C2; T2+ slots after P, before or
parallel to C3, and touches `Interface.lean` only through the two §1.1
facts above. The facility should be COMPLETE (at whatever tier is ruled)
before G-PIN — after the pin, `GoValue.typeDesc` and `FieldDef.tag` are
two-repo changes. **This sequence is the PLAN OF RECORD since
2026-09-05** (G6-1 … G6-5 RULED as recommended, §6): T1 (`reflectlite`)
after C2 in a parallel lane; T2+ after G-P; complete before G-PIN; `fmt`
source-through after T2 (G6-4); `encoding/json` v1 last (G6-5); it is
inserted into the arc ledger `docs/2026-09-03_design-hygiene-arc.md` (v).

---

## 5. Latitude, orders, and the panics that must be reproduced

### 5.1 Orders

| site | gc at the pin | machine posture |
|---|---|---|
| `Value.MapKeys()` / `MapRange()` | map-iteration order (randomized) — `reflect` documents "unspecified order" | E9 LATITUDE: the op consumes the `mapIter` choice site; the membership lane's envelope covers it; a program whose output depends on it is enumerated like a `range` loop. `DeepEqual` is order-independent by construction (`MapIndex` on each key). |
| `encoding/json` map encoding | keys SORTED (`encode.go` `mapEncoder`: `slices.SortFunc(sv, … strings.Compare)`) after `resolveKeyName` — deterministic | derived: `MapKeys` (any order) → sort → one output. No latitude leaks. |
| `fmt` `%v` of a map | `fmtsort.Sort`: a total order over keys by kind (ints, uints, strings, floats with NaN FIRST and ±0 by `<`, complex lexicographic, bools false<true, structs/arrays lexicographic by field/element, interfaces by CONCRETE TYPE DESCRIPTOR ADDRESS then value, pointers/chans by ADDRESS, nil first) | derived for every kind but two: **pointer/chan keys** (`compare :102-107`: `cmp.Compare(aVal.Pointer(), bVal.Pointer())`) — refuse by name (`fmtsort: pointer-keyed map order is address order`); **interface-typed keys with different concrete types** (`:127`: `compare(ValueOf(a.Elem().Type()), ValueOf(b.Elem().Type()))` — the `*rtype` addresses, i.e. the linker's layout of type descriptors) — refuse by name unless all keys share one concrete type. Both are gc-realization facts, not language; a ROW records each. |
| `Type.Method(i)` / `NumMethod` order | sorted by name, exported methods only for non-interface types (`type.go` `exportedMethods`); interfaces: all methods sorted | derived from `MethodSetRecord`: sort by name; drop unexported for concrete types; D5 `exported`-only records are ALREADY exported-only. Interface types via `interfaceDef` (flattened, sorted). |
| `Type.Field(i)` order | declaration order, embedded fields in place | `TypeDef.struct` order — identical. |
| `VisibleFields` / `FieldByName` through embedding | breadth-first, depth/ambiguity rules | G-P's `resolveSelector` is the same walk; build after G-P. |
| `Value.Grow`/`Append` capacity | `growslice` size classes | R2 append-spill latitude; membership rows as for `strings.Builder.grow`. |

### 5.2 Texts

`Type.String()`: qualified for named types (`main.T`, `*main.T`,
`[]main.T`, `map[string]main.T`, `struct { A int; B string }` for
anonymous — refused anyway), unqualified builtins, `func(int) string`,
`chan<- int`, `interface {}`/`any` renders as `interface {}`.
`Type.Name()`: unqualified, `""` for unnamed. `Kind.String()`: the
`kindNames` table (`type.go`), `ptr` is `"ptr"` (not "pointer"). `%T` is
`Type.String()`. `Value.String()` on a non-string kind: `"<" +
Type().String() + " Value>"` (`value.go:2455`); on an invalid Value:
`"<invalid Value>"` (`:2451`). `fmt` prints an invalid reflect.Value as
`<invalid reflect.Value>` at depth 0 and `<nil>` nested (`print.go:
779-786`). `DeepEqual` has no text.

### 5.3 Panics (gc's exact texts, all reproduced by the substitute
package's own `panic` calls — they are LIBRARY behaviour, not machine)

| trigger | text at the pin |
|---|---|
| method on the zero `Value` | `reflect: call of reflect.Value.<M> on zero Value` (`ValueError.Error`, `value.go:179-184`); `reflectlite` names `reflectlite.Value.<M>` (`reflectlite/value.go:172-177`) except `Len`, which says `reflect.Value.Len` (`:354` — an upstream inconsistency the substitute copies) |
| kind mismatch (`Int()` on a string Value etc.) | `reflect: call of reflect.Value.<M> on <kind> Value` — NOTE `valueMethodName()` derives `<M>` from `runtime.Callers` (`value.go:186-200`); the substitute must NAME the method statically (each method knows its own name), which is what `reflectlite` already does for most (`:262,267,309,387`) |
| `Set`/`SetInt`/… on a non-addressable Value | `reflect: reflect.Value.<M> using unaddressable value` (`mustBeAssignable :257`; `reflectlite :213`) |
| `Set`/`Interface` via an unexported field | `reflect: reflect.Value.<M> using value obtained using unexported field` (`:238,257`); `Interface()` specifically: `reflect.Value.Interface: cannot return value obtained from unexported field or method` |
| `Set` with a non-assignable type | `reflect.Set: value of type <T> is not assignable to type <U>` (`value.go` `assignTo`; `reflectlite :447` same shape with its context string) |
| `Field(i)` out of range | `reflect: Field index out of range`; on a non-struct: `reflect: Field of non-struct type <T>` |
| `Elem()` on a non-pointer/interface | `reflect: call of reflect.Value.Elem on <kind> Value`; on a TYPE: `reflect: Elem of invalid type <T>` (`type.go`; `reflectlite/type.go:310`) |
| `Key/Len/NumField/In/Out/NumIn/NumOut` on the wrong type kind | `reflect: Key of non-map type <T>`, `reflect: Len of non-array type <T>`, `reflect: NumField of non-struct type <T>` … (`reflectlite/type.go:320-368` — the `reflect` versions append the type) |
| `Implements(nil)` / non-interface argument | `reflect: nil type passed to Type.Implements`, `reflect: non-interface type passed to Type.Implements` (`:392,395`); `AssignableTo(nil)`: `reflect: nil type passed to Type.AssignableTo` (`:402`) |
| `Index(i)` out of range | `reflect: slice index out of range` / `reflect: array index out of range` / `reflect: string index out of range` |
| `MapIndex`/`SetMapIndex` on a nil map (set) | `assignment to entry in nil map` — the MACHINE's own map panic text, reached through `setMapIndex` |
| `Swapper` on a non-slice | `reflect: call of Swapper on <kind> Value` (`swapper.go:20`) |
| `New(nil)` / `Zero(nil)` | `reflect: New(nil)`, `reflect: Zero(nil)` |
| `fmtsort` on a non-map | `fmtsort: not a map` (returns nil, no panic — `sort.go:50`) ; `bad type in compare: <T>` for map/func/slice keys (unreachable: not comparable) |
| `Value.Pointer/UnsafePointer/UnsafeAddr`, `Type.Size/Align`, `StructOf`… | MACHINE refusal by name (§2.2), never a panic — the doctrine's visible red |

`errors.As` adds its own: `errors: target must be a non-nil pointer`,
`errors: *target must be interface or implement error` (`wrap.go:
110-116`) — plain library text over `Kind`/`IsNil`/`Implements`.

### 5.4 `fmt`-specific behaviours the facility must let the real `fmt` reproduce

- Unexported fields print WITHOUT calling their methods: `printValue :769`
  guards `handleMethods` with `CanInterface()`; so `%v` of
  `struct{ s fmt.Stringer }` prints the struct-shape of `s`, not
  `s.String()`. The flag algebra (`flagRO` propagated by `Field(i)` on an
  unexported field) is the facility's, and this row is the test of it.
- `%v` of a pointer-to-struct at depth 0 prints `&{…}` (`:915-925`), at
  depth > 0 prints the ADDRESS (`fmtPointer`) — refuse by name at depth >
  0; depth 0 is layout-free (`&` + recursion).
- Nil-pointer receivers whose `String()`/`Error()` panics: `catchPanic`
  (`:588-620`) prints `<nil>` if the receiver is a nil pointer
  (`ValueOf(arg).Kind() == Pointer && IsNil()`), else `%!v(PANIC=String
  method: …)`. Layout-free; the recover path is the machine's.
- `%x` on `[]byte`/`[N]byte` via `MakeSlice` + `Index` copy (`fmtBytes`)
  — T3's `makeSlice`, or `Bytes()` directly on addressable arrays.

---

## 6. Recommendation and decision gates

The [AGENT] recommendation, stated once: **admit the facility as a new
register class, build it `reflectlite`-first after C2, complete it to T3
after G-P, and make it the retirement path for `fmt` and the unlock for
`json`.** The alternative worth taking seriously is (D) for `json` only —
keep T1-T2 (errors, sort, DeepEqual, fmt) and never do tags/construction
— because `json`'s marginal cost (tags on the wire + three `sync`
overlays + the largest op group + 1,500 lines of upstream `encoding/json`
text to source-through) is the largest single item here and its
customer is one harness leg, not the theorem. That split is G6-5's
option (b).

**Ruling record, 2026-09-05.** [AGENT] record; the [USER] quote was
received by the [AGENT] coordinator in conversation and RELAYED to the
recording worker (lane `rulings-0905`), so it is cited as relayed, not
firsthand (U0-incident convention). The five gates below were put to
the [USER] as items (4)–(8) of an eight-item list, each with its verbatim
text and this memo's recommendation (a); Mike replied, verbatim as
relayed: «(1) approved, (2) we should do what the standard supports, and avoid over-refusal if we can. That's what (b) means right? (3) done, (4-8) all approved as recommended» — «(4-8) all approved as recommended» rules
G6-1 … G6-5 each at option (a). Sequencing consequence: §4.5 is now the
plan of record — T1 (`reflectlite`) after C2 in a parallel lane; T2+
after G-P; the facility complete before G-PIN; `fmt` source-through after
T2 (G6-4); `encoding/json` v1 last (G6-5). Slice 4 of the stdlib plan is
NARROWED accordingly (`docs/2026-09-03_stdlib-boundary-design.md`, slice
4; `fmtdesugar.go` is an interim deleted at G6-4). Each ruling is marked
on its gate below; the gate texts and grounds are unchanged.

The gates, numbered, verbatim, with the recommendation. None was decided
in this memo; the rulings are recorded per gate.

**G6-1 — Class.** «Admit a NEW register class, `facility`: a named
machine op family whose every op is a PROJECTION of existing machine data
(`Program.typeDefs`, `Program.methods`, `GoValue`, `Store`) or a
`Loc`-addressed store, never a library result; plus ONE substitute
library package (our text at the library path, pinned by hash,
differential-validated, upstream's own tests admitted as rows) that is
the only importer of the op family's intrinsic package. Cap: 1 facility
(`reflect`); a second facility re-opens G8. `scripts/check-stdlib-register`
renders the op list and the substitute package's hash.» Options: (a)
admit the class as stated; (b) count the ops against the primitive cap
(raise 2 → N) and the text as overlay rows (raise 12 → M); (c) exclude
`reflect` permanently like `unsafe` (= §3.4 (D)). Recommendation: **(a)**.
Grounds: (b) makes both existing caps meaningless and hides 1,500 lines
of our text in a class built for one-line diffs; (c) refuses cedar-go's
codec and every `errors.Is` in real code, for no fidelity gain (refusals
are already honest). Size: the class itself 1 session (register + check).
RULED [USER] 2026-09-05 — as recommended ((a)), relayed.

**G6-2 — Scope.** «Build T1 (`reflectlite`: `errors.Is/As`, `sort.Slice*`)
first as its own slice; T2 (`reflect` read tier: `DeepEqual`, `binary`
read paths, `fmt`'s needs) second; T3 (write/construct + struct tags) only
if G6-5 is ruled (a); T4 (`Method/Call`) deferred with a frontier row
(9 gotest files); the excluded list of §2.2 refused by name permanently.»
Options: (a) as stated; (b) full T1-T3 in one arc; (c) T1 only, stop.
Recommendation: **(a)**. Grounds: T1 forces every structural decision on
the smallest surface (G9's order); T2 is where the coverage is (35 gotest
files, `fmt`); T3's cost is `json`'s and should be decided with it.
Sizes: T1 2.5-4; T2 4-5; T3 3-4 (+1 twin pin move); T4 1-2 if ever.
RULED [USER] 2026-09-05 — as recommended ((a)), relayed.

**G6-3 — Ordering.** «T1 after C2 (well-founded `TypeEnv`), in a parallel
lane; T2+ after G-P (native promotion), because `NumMethod`/`Method(i)`/
`Implements`-through-promotion read the D2 record, whose meaning G-P
changes; the two §1.1 facts (`GoValue.typeDesc`, `FieldDef.tag`) are
recorded in the reasoning-surface plan NOW and the facility is complete
at its ruled tier before G-PIN.» Options: (a) as stated; (b) T1 now,
against fuel (re-pay at C2); (c) everything after G-PIN (two-repo
changes). Recommendation: **(a)**. Grounds: plan §4.3's own sequencing
note; §5.1 of the plan shows C2 as a parallel lane from item 2, so T1
starts within weeks; (c) is the one order that makes every later step a
coordinated pin move. RULED [USER] 2026-09-05 — as recommended ((a)),
relayed.

**G6-4 — `fmt`.** «Once T2 lands, `fmt` becomes a SOURCE-THROUGH package
over the facility (`print.go`/`format.go`/`errors.go`/`internal/fmtsort`
from the pin; `sync.Pool` for `pp` OVERLAID to `newPrinter() = new(pp)`
— 1 row; `Print*` via G7's `os.Stdout`), the six remaining fmt shims
retire, and the frontend's `fmtdesugar.go` specialization is DELETED —
one `fmt` semantics, not two. Slice 4 (G5 (iii)) is therefore NARROWED
to its `strconv`-leaves step (delete `goleanShimFmtUint/Int/Hex/Bool/
Quote*` now, keep the verb×kind matrix and the dyn switch until T2), or
skipped if T2 is expected within its horizon.» Options: (a) as stated —
G5 (iii)'s specialization is an interim, retired by G6-4; (b) keep the
specialization for static sites as an optimization AND run real `fmt` at
dynamic sites (two implementations of one library — rejected on the
"no semantic choice hides in evaluator recursion" doctrine: a
specialization that disagrees with the source-through `fmt` on any row
is a bug with two candidates for blame); (c) never source-through `fmt`
(keep G5 (iii) permanently, reflective remainder refused). Recommendation:
**(a)**, with slice 4 narrowed rather than skipped (the `strconv` leaves
are an unconditional improvement). Grounds: `fmt` is 41 `reflect` sites
deep (memo §1.3 finding 3) and the only faithful `fmt` is the real one;
the `%p`/address-order remainder refuses by name at the facility ops.
Size: 4-6 sessions after T2 (source-through admission, the `pp` overlay,
the `os.Stdout` dependency on G7's slice, the corpus's 46+25 fmt rows
plus the Formatter family re-run as the regression, the desugar
deletion). It is NOT the same arc as T2 — same lane sequence, separate
gate-green points. RULED [USER] 2026-09-05 — as recommended ((a)),
relayed: slice 4 narrowed to its `strconv`-leaves step, not skipped;
`fmtdesugar.go` is an interim, deleted at G6-4.

**G6-5 — `encoding/json`.** «Admit `encoding/json` (v1 text at the pin;
the `jsonv2` experiment is off in the oracle build) as source-through
over T3, with: `FieldDef.tag` on the wire (twin pin move;
`structTagCompatible` made tag-blind per spec §Conversions — a BUGS.md
Cases line); three overlay rows for `encoderCache`/`fieldCache`
(`sync.Map` → recompute; the cache is unobservable) and `encodeStatePool`
(`sync.Pool` → `new`); `ptrSeen` cycle detection over `Loc` identity
(`UnsafePointer()` used as a set key, layout-free in effect — an op
`identityKey` that returns an opaque comparable, NOT an integer); the
`fmt` dependency satisfied by G6-4 or by the error-path texts refusing
until it lands.» Options: (a) as stated; (b) NOT admitted — T3 and tags
are never built, `json` stays refused by name, the DRT harness's JSON leg
stays off-machine; (c) admit `encoding/json/v2` instead (`jsontext` +
`v2`: newer, also `reflect`-bound, ALSO uses `unsafe` for its own
arshalers and `sync` caches; not the oracle's build — rejected: it
would pin a non-default GOEXPERIMENT). Recommendation: **(a)**, as the
LAST arc of the sequence and the one the [USER] may most reasonably
decline: it is the cedar-go unlock (62 decls / 42 call sites / the
JSON-out leg) but not the theorem's. Size: 5-7 sessions after T3
(source-through admission of `encoding/json` + `encoding` + `encoding/
base64` + `unicode/utf16`; the three overlays; the tag wire change; the
struct-identity audit; corpus rows for `Marshal`/`Unmarshal` over tagged
structs, `omitempty`/`omitzero`/`string` options, `Marshaler`/
`TextMarshaler` dispatch, map-key sorting, the `UnsupportedTypeError`/
`UnsupportedValueError` (NaN, cycles) paths, and the `%v` error texts).
RULED [USER] 2026-09-05 — as recommended ((a)), relayed: `encoding/json`
v1 admitted as the LAST arc of the sequence.

**Totals, for planning:** (C)-first path to a complete T1-T3 facility with
`fmt` and `json` = 1 + (2.5-4) + (4-5) + (3-4) + (4-6) + (5-7) ≈
**20-27 sessions** in sequence; the first tangible unlock (`errors.Is/As`)
at session ≈4; `fmt`'s six shims retired at ≈14-16; cedar-go's codec at
the end. Against the plan's C-arc (28-38 sessions at 1-3 lanes, §5.1),
this is a second lane of comparable weight; it does not sit on the
critical path but it competes for sessions. The honest alternative is
G6-2 (c) + G6-5 (b): ≈4 sessions, `errors.Is/As` and `sort.Slice`
unblocked, the rest stays a named red.

---

## Appendix A — commands (re-derivable at the pins)

```sh
# gotest in-scope slice (approximation of the triage's 1,013: first line exactly "// run")
cd deps/go/test && grep -rl --include='*.go' -m1 '^// run$' . \
  | while read f; do [ "$(head -1 "$f")" = "// run" ] && echo "$f"; done > $S/files.txt   # 1,015
xargs grep -l '"reflect"' < $S/files.txt > $S/reflect.txt                                   # 71
xargs grep -lE 'reflect\.(MakeFunc|StructOf|ArrayOf|SliceOf|MapOf|New|StringHeader|SliceHeader|PointerTo|MakeMap|MakeSlice|FuncOf|ChanOf)\b|UnsafeAddr|UnsafePointer|\.Pointer\(\)' < $S/reflect.txt   # 27
xargs grep -lE '\.Call\(|\.Method\(|MethodByName|NumMethod' < $S/reflect.txt                # 16 (9 not also in the 27)
# layout-free-only = 71 - |27 ∪ 16| = 35
xargs grep -ohE '%[-+# 0]*[0-9]*\.?[0-9]*[vTpdsqxXfgebcUot]' < $S/files.txt | sed -E 's/[0-9.]//g' | sort | uniq -c
xargs grep -lE '%[-+# 0]*[0-9.]*[vTp]' < $S/files.txt | wc -l                               # 94

# stdlib consumers at the pin
grep -n reflectlite deps/go/src/errors/wrap.go deps/go/src/sort/slice.go
grep -ohE 'reflect\.[A-Z][A-Za-z]*' deps/go/src/encoding/json/{encode,decode}.go | sort | uniq -c
grep -ohE '\.(Kind|Elem|Field|…)\(' deps/go/src/encoding/json/{encode,decode}.go | sort | uniq -c
grep -n 'sync\.\|UnsafePointer\|linkname' deps/go/src/encoding/json/{encode,decode}.go
head -8 deps/go/src/encoding/json/v2_inject.go | grep build          # //go:build goexperiment.jsonv2
grep -ohE 'reflect\.[A-Z][A-Za-z]*' deps/go/src/fmt/print.go | sort | uniq -c
sed -n 95,140p deps/go/src/internal/fmtsort/sort.go                  # pointer/chan/interface key order

# reflect's dependence on layout
cd deps/go/src/reflect && ls *.go | grep -v _test | xargs wc -l | tail -1                    # 8,740
grep -o 'unsafe\.' $(ls *.go | grep -v _test) | wc -l                                        # 316
grep -o 'abi\.' $(ls *.go | grep -v _test) | wc -l                                           # 267
grep -h 'go:linkname' $(ls *.go | grep -v _test) | wc -l                                     # 42
grep -hE '^func [a-zA-Z_]+\(.*\)[^{]*$' $(ls *.go | grep -v _test) | wc -l                   # 66 body-less
sed -n 1383,1385p type.go; sed -n 158,164p value.go; sed -n 181,182p ../internal/abi/type.go

# cedar-go demand
cd deps/cedar-go && find . -name '*.go' ! -name '*_test.go' | xargs grep -ohE 'json\.(Marshal|Unmarshal|NewDecoder|MarshalIndent)\b' | sort | uniq -c
find . -name '*.go' ! -name '*_test.go' | xargs grep -cE 'func \(.*\) (Marshal|Unmarshal)JSON' | awk -F: '{s+=$2} END {print s}'   # 45
find . -name '*.go' ! -name '*_test.go' | xargs grep -ohE 'errors\.(Is|As|Join)\b' | sort | uniq -c                                 # 17 / 3 / 48
find . -name '*.go' ! -name '*_test.go' | xargs grep -ohE '%[-+# 0]*[0-9.]*[vTp]' | sort | uniq -c                                  # %v 65, %T 16, %+v 2

# machine representation
grep -n "^inductive GoValue" -A40 GoLean/GoCore/Value.lean; sed -n 535,560p GoLean/GoCore/Value.lean
sed -n 15,25p GoLean/GoCore/Syntax.lean; sed -n 48,70p GoLean/GoCore/Syntax.lean; sed -n 471,499p GoLean/GoCore/Syntax.lean
sed -n 1125,1136p GoLean/GoCore/Ops.lean      # "the wire strips tags"
grep -n "def dynamicImplementsInterface\|def firstUnsatisfiedMethod?\|def defaultValue\b" GoLean/GoCore/Ops.lean
grep -n "def mapIterCandidates" GoLean/GoCore/Machine.lean
```

## Appendix B — provenance of the numbers not re-derived here

- "25 reflect first-refusals", "82 fmt outside the subset", 1,013 in-scope:
  `docs/2026-09-01_gotest-triage.md` (run at 670d3351; artifacts not on
  this machine). This memo's 71/35/27/16 are static import/use counts over
  the same slice definition (±2 files), a different and larger measure.
- cedar-go declaration counts (38 / 21 sole at case scope; 62-64 / 31 sole
  widened; `errors.Is/As` 9-10 / 5 sole): `docs/2026-09-03_cedar-go-
  coverage-census.md` §3.4-3.5, §10.3, §11.2 (lower-diagnose census).
- Register state (primitive 0/2, both slots spoken for; overlay 5/12; shim
  7 = fmt's six + one retired 2026-09-04): `docs/stdlib-admission-register.md`
  as of main `ac45aedd`.
- `reflect` census "1/42/69 (8,694 lines)" in the stdlib memo's Appendix A
  vs this memo's 8,740/316/267/42/66: different filters (the memo counted
  own-asm/linkname/bodyless; this one adds `unsafe.`/`abi.` sites and
  includes `abi.go`/`arena.go`-class files); both at go1.26.5.
