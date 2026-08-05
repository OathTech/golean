# Generics design note — slice 6 of the general-coverage arc (2026-08-05)

Status: DECIDED (2026-08-05) — all recommendations adopted; resolutions
recorded in §9 and binding on slice 6's implementation. Decided at
coordinator level within the arc's delegated authority (each resolution
follows from established doctrine, argued per point in §9); the whole
note is flagged for re-argument at the arc-final user-authorized audit.
Written from an isolated worktree; sources read at the paths given
(worktree paths elided — files identical to main @ branch tip). Points
are tagged **[FACT]** (verified against a primary source, cited) or
**[RECOMMENDATION]** (adopted per §9).

Charter: `docs/2026-08-04_general-coverage-arc.md` slice 6 ("design note
comparing monomorphization at the frontend (Goose-style, keeps GoCore
generic-free) vs semantic dictionaries; expected outcome is frontend
monomorphization with GoCore untouched"). Binding doctrine:
`docs/2026-08-04_nondeterminism-doctrine.md`, CLAUDE.md (fail-closed,
guardrails first, GoCore purity, one-boundary mangling), format per
`docs/2026-08-04_floats-design.md`.

Oracle toolchain: go1.26.5 linux/amd64 (`/usr/local/go`). Spec quotes are
verbatim from `/usr/local/go/doc/go_spec.html` (the go1.26.5 spec). Probes
run under `artifacts/go-probes/` (worktree), `GOCACHE` repo-local.

The headline recommendation, stated up front: **frontend monomorphization,
GoCore untouched** — the arc plan's expected outcome survives contact with
the primary sources, and the spec itself defines instantiation as
substitution (§2b). The one Lean-side change is a *rendering* fix
(`TypeId.unqualified`, §3.4), not semantics.

---

## 1. What the corpus pins (behavior inventory)

**[FACT]** 75 red rows in `baselines/native-full.tsv` are generics-blocked,
every one stage `frontend-export` (fail-closed at the frontend, correct
classification):

- 46 under `generics/` (the slice's core);
- 4 under `bools/generic-type-set/` (`and-or`, `equality`, `inference`,
  `not-defined`; `zero-value` PASSES — see below);
- 8 scattered singletons: `builtins/clear-delete-edge/{clear-generic-map,
  clear-generic-slice,delete-generic-map}`, `builtins/copy-edge/
  generic-slices`, `builtins/min-max-edge/{generic-ints,generic-strings}`,
  `new/new-expr/generic-operand`, `variadic/variadic-generic`;
- 17 double-blocked on other slices: 8 `floats/generic-type-set/*` + 9
  `complex/generic-type-set/*` (need floats/complex semantics AND this
  slice — already recorded in the floats note §1).

**[FACT]** Additionally `generics/type-parameter-channel-ops` (counted in
the 46) is double-blocked on the future channels arc: its body does
`ch <- 4; x := <-ch; len(ch); cap(ch)` on a `~chan int` type parameter
(`Corpus/coverage/exec/generics/type-parameter-channel-ops/main.go`).
Generics alone flips at most 45 of the 46. Accounting for the slice:
**57 ids flip on generics alone** (45 + 4 bools + 8 scattered), 1 waits for
channels, 17 wait for floats/complex. Exit-criteria bookkeeping should use
these numbers, mirroring the floats note's split.

**[FACT]** Why `bools/generic-type-set/zero-value` passes today: its subject
`genericBoolZeroValue` only declares `var z genericBool` (a plain defined
type) and never calls a generic function. The frontend's per-decl quarantine
(`tools/nativefrontend/emit.go:50-75`) turns each UNSUPPORTED plain function
into a fail-closed stub, so the generic helpers in the same file don't
poison it. The same mechanism explains why whole `generics/` files are red:
generic *type* declarations go through `emitGenDeclTypes`, whose errors fail
the WHOLE export (`emit.go:83-90` — no per-decl quarantine for types), and
generic *functions* fail per-decl but every red subject CALLS one.

**[FACT]** The three frontend fail-closed points that produce today's
classification: (i) `emit.go:1697-1702` — an instantiation `f[int]` parses
as an index expression; an index whose `Index` is a type fails
`unsup("generic instantiation …")`; (ii) `wire.go:120-197` — `emitType` has
no `*types.TypeParam` or `*types.Alias` arm, so both hit the `default:`
`unsup("type %T")`; (iii) generic type aliases abort `types.Config.Check`
itself in a module-less process (§2a, the `gotypesalias` quirk). All are
boundary refusals; no silent approximation was found.

What the clusters actually pin (case-by-case over the distinct behavior
classes; ids under `generics/` unless noted):

| cluster (ids) | pins |
|---|---|
| `identity`, `inference`, `zero-values`, `zero-composite` | function instantiation, explicit (`id[int]`) and inferred; `var z T` zero values at scalar, string, bool, slice, map (nil-ness of composite zeros) |
| `generic-struct`, `defined-slice-type`, `generic-map-type`, `recursive-generic-type` | instantiation of generic TYPES (struct over T, `[]T`, `map[K]V` defined forms); self-referential `genericNode[T]` with `*genericNode[T]` field |
| `type-method-dispatch`, `instantiated-method-value`, `instantiated-function-value` | methods on instantiated types (receiver-side type params — the ONLY generic-method form Go has, §2b); method values `b.Value`; function values `f := genericAdd[int]` |
| `type-set-constraint`, `constraint-embedding`, `method-constraint-call`, `method-and-type-set-constraint` | type-set constraints (`~int \| ~int8`), constraint embedding + `comparable`, method-set constraints, mixed method+type-set constraints; operations (`+`, `==`, conversions) on type-parameter operands at both builtin and defined type args |
| `comparable-constraint`, `comparable-runtime-edge/*` (8) | `comparable` satisfied by `any` and interface-carrying composites ("satisfies but does not implement", §2b); RUNTIME panic `comparing uncomparable type []int` for slice/map/func dynamic types under `==` at `T = any`, `[1]any`, struct-with-any-field; `struct-skips-interface-panic` pins field-order short-circuit (first differing field decides before the uncomparable field is reached) |
| `higher-order-inference/*` (6) | inference beyond call sites: generic function assigned to typed var, passed to concrete/generic functions, returned, named function types, partial source instantiation `hoiFirst[int]` completed by inference |
| `recursive-constraints/*` (4) | F-bounded constraints `[T Cloner[T]]`, `[T Less[T]]`, pointer-self `[T Link[T]]` at `*rcNode`, `comparable`-embedding self-reference |
| `type-parameter-{slice,map,composite-literal,conversion}-ops`, `type-parameter-channel-ops` | core-type-style operations THROUGH a type parameter (`~[]int` indexing/assignment, `~map[string]int` ops, composite literal `T{...}` at `~struct{...}`, `U(x+1)` conversion between `~int` params; channel ops — channels-arc-blocked) |
| `type-aliases/*` (5) | generic type ALIASES (`type aliasSlice[T any] = []T`, go1.24+): transparent instantiation to slice/map/struct/func types |
| `generic-interface-value` | instantiated generic INTERFACE `valueGetter[int]` as a value's static type; dispatch to a concrete impl |
| `map-slice` | two type parameters, `make([]U, len(xs))`, closure argument `func(T) U` |
| bools/floats/complex `generic-type-set/*` | the same ops/zero/inference matrix per element domain, under `~bool`, `~float32\|~float64`, `~complex64\|~complex128` |
| scattered builtins/new/variadic ids | builtins (`clear`, `delete`, `copy`, `min`, `max`, `new(expr)`, variadic `...T`) applied at `~`-constrained type parameters — pins that builtin semantics compose with instantiation |

**[FACT]** No corpus case observes an instantiated type's dynamic NAME (no
type asserts/switches/reflection on instantiated types anywhere under
`generics/` — checked by reading all 27 `main.go` files). The only
name-bearing observations are the `comparable-runtime-edge` panic texts,
which name the FIELD's dynamic type (`[]int`), already representable. The
identity/naming design in §3 is therefore currently pinned by nothing — G0
adds the missing probes.

---

## 2. The strategy decision: frontend monomorphization vs semantic dictionaries

### 2a. What go/types gives the frontend

**[FACT]** `types.Info.Instances` (doc, go1.26.5): "Instances maps
identifiers denoting generic types or functions to their type arguments and
instantiated type. … Given a generic function func F[A any](A), Instances
will map the identifier for 'F' in the call expression F(int(1)) to the
inferred type arguments [int], and resulting instantiated *Signature."
The frontend's `types.Info` does not populate it today
(`tools/nativefrontend/main.go:58-63` — add one map field).

**[FACT]** Probed on the corpus files themselves (probe:
`artifacts/go-probes/instdump/`, same parser+`types.Config.Check` pipeline
as the frontend):

- `higher-order-inference/main.go`: every use site gets a FULLY inferred
  entry — including the partial source instantiation `hoiUseFirst(hoiFirst[int])`,
  recorded as `hoiFirst [int, string]`. Inference (call-site, assignment
  target, return target, partial completion) is entirely go/types' — the
  frontend re-implements none of it.
- `generic-struct/main.go`: `box [int]` and `box [string]` recorded at the
  two literal sites with the instantiated `*types.Named`.
- `comparable-runtime-edge/main.go`: all eight sites recorded, args `[any]`,
  `[[1]any]`, `[main.genericComparableRuntimeBox]` — instantiated signatures
  are fully concrete `func(a any, b any) bool` etc.
- Derived (transitive) instantiation probe (`instdump/derived.go.txt`):
  inside generic `outer[T]`, the call `inner([]T{x,x})` is recorded as
  `inner [[]T]` — args still mention the ENCLOSING type parameter. So the
  frontend needs a substitution-closure walk (§2b, G2), not just a map read.
- **The `gotypesalias` quirk**: type-checking `generics/type-aliases/main.go`
  from a module-less binary fails with `generic type alias requires
  GODEBUG=gotypesalias=1 or unset`; with `GODEBUG=gotypesalias=1` it checks
  and records instantiated `*types.Alias` entries (`aliasSlice [int]
  main.aliasSlice[int]`, …). The nativefrontend runs under
  `GO111MODULE=off` (`main.go:5`), so it inherits this; the implementation
  must enable materialized aliases explicitly (env in the wrapper script or
  `os.Setenv` at frontend startup — decide at G-alias time, §8).

### 2b. Is full monomorphization always possible?

**[FACT — the spec defines instantiation as substitution.]**
§Instantiations: "A generic function or type is instantiated by
substituting type arguments for the type parameters. … Instantiating a type
results in a new non-generic named type; instantiating a function produces
a new non-generic function." A monomorphizing frontend is executing the
spec's own definition, not an implementation trick.

**[FACT — go/types guarantees the instantiation closure is finite.]**
`go/types/mono.go:16-19`: "This file implements a check to validate that a
Go package doesn't have unbounded recursive instantiation, which is not
compatible with compilers using static instantiation (such as
monomorphization)." It runs unconditionally on every successful check
(`go/types/check.go:553-556` — gated only on there being no prior type
error), i.e. **our own `conf.Check` call already runs it**: any package the
frontend accepts is statically instantiable, by construction. Verified live
(probe `artifacts/go-probes/genrec/`): `f[T]` calling `f[[]T]` is rejected
at compile time by `go run` with `instantiation cycle: T instantiated as
[]T` — the same error our frontend's Check would report, so both sides of
the differential refuse identically. Zero-weight cycles (plain `f[T]`
recursion, `List[T]` self-reference) are allowed and reach a fixed point —
the closure worklist dedups on the instantiation key and terminates.

**[FACT — generic methods do not exist in Go.]** Grammar:
`FunctionDecl = "func" FunctionName [ TypeParameters ] Signature …` but
`MethodDecl = "func" Receiver MethodName Signature …` (spec §Method
declarations — no TypeParameters slot). Methods get type parameters only
through the receiver: "If the receiver base type is a generic type, the
receiver specification must declare corresponding type parameters for the
method to use." So methods monomorphize WITH their receiver type — the one
feature that breaks monomorphization in other languages (virtual generic
methods) is absent by grammar.

**[FACT — generic functions/types cannot escape uninstantiated.]** "A
generic function must be instantiated before it can be called or used as a
value" (§Function declarations); "Generic types must be instantiated when
they are used" (§Type definitions); "Generic aliases must be instantiated
when they are used" (§Alias declarations). Every runtime artifact has
concrete type arguments; there is no first-class polymorphic value to
represent. Function values of generic functions (`f := genericAdd[int]`)
are values of the instantiated, monomorphic function.

Reflection would be the loophole (a `reflect.Type` of an instantiated type
leaks the instantiation lattice at runtime), and it is out of charter scope
and fail-closed globally.

**Conclusion**: for the corpus's shapes and for general spec-conforming Go
in our supported surface, full monomorphization is always possible, with
the boundary cases handled in §5 (fail closed, none silent).

### 2c. What gc itself does — and why it doesn't change the answer

**[FACT]** gc does NOT fully monomorphize: it does gcshape stenciling with
runtime dictionaries. `cmd/compile/internal/noder/reader.go:891-948`
(`shapify`): one instance per *shape* — "we simply use the type's
underlying type as its shape", collapsing all pointer type args for
basic-constraint parameters to `*byte`; shapes live in the fake package
`go.shape` (`cmd/compile/internal/types/type.go:1984-1985`). Per-instance
runtime dictionaries supply what the shape erases
(`reader.go:157-205` — "A readerDict represents an instantiated
compile-time dictionary", carrying the concrete `*runtime._type`s, itabs,
subdictionaries). Instance symbols are mangled `base[targ1,targ2]` with
`LinkString` (import-path-qualified) arg rendering (`reader.go:863-889`,
`readerDict.mangle`).

**Why this is evidence FOR frontend monomorphization, not against**: gc's
shape-sharing is a *code-size optimization* that must remain observationally
IDENTICAL to full stenciling — the dictionary exists precisely to recover
every type-arg-dependent observable (runtime type descriptors for asserts,
itabs, map key hashing) that sharing erased. The Go language exposes no way
to distinguish the two strategies (function values are not comparable;
`go.shape` names never surface in the language proper). So gc itself
warrants that instantiation strategy is semantically invisible; we can take
the semantically simplest point (full substitution, the spec's definition)
without modeling shapes or dictionaries at all. A dictionary design in
GoCore would be re-deriving gc's optimization inside the trust surface for
zero observable gain.

### 2d. The proof surface: what "GoCore untouched" is worth

**[RECOMMENDATION — adopt monomorphization; here is the quantified
benefit.]** Under frontend monomorphization:

- **Zero new `Ty`/`GoValue` constructors, zero new interpreter arms.** The
  wire schema is unchanged — instantiated functions are ordinary `funcs`
  entries, instantiated types ordinary `typeDefs` (`defined`/`struct`/
  `interface` kinds), with mangled name keys that GoCore treats as the
  opaque `TypeId`/`FuncId` strings it already has. Every proof that cases
  on `Ty` or `GoValue` (StateWf, MachineSound, the normalization-soundness
  kit, the ∀-choices kit) gains **no arms**. Contrast the floats slice,
  which honestly budgeted ~700 statement-TCB lines and arm growth across
  ~10 interpreter functions for ONE new value domain.
- **Statement TCB unchanged.** Theorem statements over generic programs are
  statements over their monomorphized GoCore programs — first-order,
  readable over the same base definitions; nothing generic enters the
  statement language. Under a dictionary design, `Ty` would need
  type-parameter binders and constraint witnesses, and every headline
  statement over a generic program would quantify them — the largest
  statement-TCB growth of any option on the table, for a feature whose
  runtime content is (per §2c) zero.
- **No new Choices sites, no envelope statements.** Instantiation is fully
  static and deterministic; the nondeterminism doctrine's obligations are
  vacuously discharged. `applyStmtOpCore` stays choices-free; the
  stream-obliviousness kit is untouched. (Stated explicitly so the
  envelope-fidelity audit dimension knows there is deliberately nothing to
  review here.)
- **The cost lands in the frontend TCB**, where it belongs: the
  substitution/closure pass is frontend code, differentially validated
  end-to-end (a wrong substitution produces a wrong answer against `go
  run`), quarantined by CLAUDE.md's GoCore-purity rule. Honest residue: the
  differential CANNOT see a go/types inference bug (gc uses the mirrored
  types2 — shared fate), but that trust is not new; it is exactly the
  class of the existing go/types folding trust recorded in the floats note
  §7. What IS new frontend trust is our substitution pass itself; §8
  mitigates by leaning on `types.Instantiate` (go/types' own subster,
  `go/types/subst.go`) wherever the API allows.

### 2e. Where monomorphization cannot reach (and what happens there)

All fail closed, none silently:

- **Unbounded instantiation**: cannot reach the frontend at all — rejected
  by go/types' mono check before emission, with the differential's Go side
  rejecting identically (§2b [FACT], probe-verified). Not our boundary to
  implement; a G0 negative case pins the shared refusal.
- **Pathological-but-finite closure growth** (multiplicative instantiation
  chains): finite by the mono check, but size is unbounded by any constant.
  **[RECOMMENDATION]** a registry cap (e.g. 10,000 instantiations) that
  fails the export loudly — defense in depth, never silent truncation.
- **Reflection over instantiated types**: out of scope globally
  (extern-policy territory); would be the one true dictionary-forcing
  feature. Fail-closed as today.
- **Type args outside the supported type surface** (anonymous non-empty
  structs/interfaces as arguments): the existing `emitType` refusals fire
  on the substituted types — same boundary, same message, nothing new.
- **Separate compilation / plugins**: monomorphization is whole-program;
  the frontend already type-checks whole programs, and the corpus is
  single-package. Multi-package targets (raft) monomorphize from the root
  package's reachable instantiations; `plugin`-style dynamic loading stays
  out of scope.

---

## 3. Identity: TypeId/FuncId for instantiations

### 3.1 What Go pins (probe `artifacts/go-probes/genid/`)

**[FACT]** For `type Pair[T any] struct{ a, b T }`, `type Inner struct{ n int }`:

```
reflect.TypeOf(Pair[int]{}).Name()        = "Pair[int]"
reflect.TypeOf(Pair[int]{}).String()      = "main.Pair[int]"
reflect.TypeOf(Pair[Inner]{}).Name()      = "Pair[main.Inner]"
reflect.TypeOf(Pair[*Inner]{}).Name()     = "Pair[*main.Inner]"
reflect.TypeOf(Pair[Pair[int]]{}).Name()  = "Pair[main.Pair[int]]"
x.(Pair[string]) panic: interface conversion: interface {} is main.Pair[int], not main.Pair[string]
```

So the dynamic-name contract for instantiated types: base name unqualified
in `Name()`, type ARGUMENTS package-qualified (by package NAME) inside the
brackets, in both `Name()` and panic texts.

**[FACT]** Structural types stay structural through instantiation: a
`[]T` returned at `T = int` type-asserts successfully as `[]int`
(`sliceAssert: true`), and `Pair[int]` from one site asserts as `Pair[int]`
from another (`pairAssert: true`, `pairAssertWrongArg: false`). The spec's
identity rule (§Type identity): "Two instantiated types are identical if
their defined types and all type arguments are identical." Identity is
per-instantiation-result, not per-instantiation-site.

### 3.2 The mangling scheme

**[RECOMMENDATION]** TypeId key for an instantiated named type =
`types.TypeString(instType, packageNameQualifier)` where
`packageNameQualifier` routes through the existing `qualifiedTypeName`
machinery — producing exactly `main.Pair[main.Inner]`, `main.box[int]`,
`main.genericNode[int]`. Properties, each argued:

- **Matches Go's observable renderings**: panic messages use the full key
  verbatim (`goTypeNameForMessage`, `Ops.lean:429` renders `.defined name
  => name.key`) — parity with `main.Pair[main.Inner]` panic text for free;
  `Name()` parity after the §3.4 fix.
- **Injective against source names**: `[` cannot occur in a Go identifier,
  so no mangled key can collide with any declared type's key. Distinct
  instantiations render distinct keys because `TypeString` is injective on
  the type surface we admit, GIVEN package-name uniqueness — which the
  existing `checkPackageNameCollisions` gate (`emit.go:1837-1856`) already
  enforces; routing arg rendering through `qualifiedTypeName` extends its
  recording to type-argument packages automatically.
- **One boundary, collision-checked** (CLAUDE.md's rule): the mangled key
  is constructed in exactly one frontend function (the instantiation
  registry's, §8 G1), which also keeps `mangled → types.Type` and fails the
  export on a key mapping to two non-`types.Identical` types — a
  belt-and-suspenders check behind the injectivity argument. The Lean
  decoder's existing duplicate-FuncId gate (`NativeToIR.lean:986-994`)
  backstops function ids.
- Same shape for **FuncId**: `genericAdd[int]`, `main.genericMethodBox[int].Value`
  for methods (receiver TypeId is the instantiated one). Lifted func
  literals inside generic functions inherit the mangled enclosing name
  (`e.curFuncName` becomes the instantiated name), so `outer[int].go1$lit0`
  and `outer[string].go1$lit0` are distinct — the same collision class the
  2026-07-25 audit found for same-named methods, handled by the same
  mechanism.
- Deliberate divergence from gc's `LinkString` (import-path) mangle
  (`reader.go:879`): our TypeIds key on package NAME everywhere; using
  paths only inside brackets would be inconsistent, and the
  name-collision gate makes names sound. Recorded as a divergence, not an
  oversight.

**[RECOMMENDATION]** Aliases never mint TypeIds: `types.Unalias` after
instantiation, so `aliasSlice[int]` emits as `[]int` directly — matching
both Go identity (aliases are transparent) and the existing frontend
comment (`emit.go:295-302`).

### 3.3 Type switches / asserts

With substitution, `[]T` at `int` IS the wire type `{kind: slice, elem:
int}` — identical to literal `[]int` by construction, so assert/switch
identity (which keys on structural `Ty.eqb`) is automatically right; only
*named* instantiations need the mangled TypeId, and those compare by key
equality exactly as defined types do today. A dictionary design would have
to prove this transparency; monomorphization gets it definitionally. G0
pins it (§8).

### 3.4 The one Lean-side change: `TypeId.unqualified`

**[FACT]** `Value.lean:156-159` strips the package qualifier with
`id.key.splitOn "." |>.getLast!`. For a mangled key this is wrong:
`"main.Pair[main.Inner]".splitOn "."` ends with `"Inner]"`, not
`"Pair[main.Inner]"` — violating the stated `reflect.Type.Name()` contract
(docstring at `Value.lean:153-155`, probe §3.1). **[RECOMMENDATION]** change
it to strip only the LEADING `<pkg>.` segment (drop through the first `.`
that precedes any `[`; for existing keys `main.T` the behavior is
identical). Rendering-only — no interpreter arm, no proof arms expected
beyond whatever directly mentions this def. Ship it in G1 with a unit eval
test; until a corpus case observes an instantiated name (G0 adds one) this
is the contract-honesty fix, not a behavior flip.

---

## 4. Semantic subtleties the monomorphizer must preserve

These are the places a naive implementation would silently diverge; each
gets a guardrail (existing or G0):

1. **Constants do NOT re-fold at the type argument.** Spec §Conversions:
   "Converting a constant to a type parameter yields a non-constant value
   of that type, with the value represented as a value of the type argument
   … the numeric value of the expression P(1.1) + 1.2 will be computed with
   the same precision as the corresponding non-constant float32 addition."
   The monomorphizer must emit over the ORIGINAL `types.Info` (where
   `Types[T(1.25)].Value == nil`), never re-typecheck substituted source —
   re-checking would turn `T(1.25)` into a typed CONSTANT and fold
   `P(1.1) + 1.2` at exact precision instead of per-op float32.
   Int-domain cases can't see this (exact); the floats/complex
   `generic-type-set` cases pin it differentially once both slices land —
   an ordering dependency to state in the slice plan (§8).
2. **`comparable` instantiated at `any` reduces to interface equality.**
   Spec §Satisfying a comparable constraint: "any satisfies (but does not
   implement) comparable … comparing operands of type parameter type may
   panic at run-time". After substitution, `a == b` at `T = any` is a plain
   interface comparison — GoCore's existing uncomparable-dynamic-type panic
   (`Ops.lean:1188-1197`, message `comparing uncomparable type …`) carries
   the whole 8-case `comparable-runtime-edge` cluster with zero new
   machinery. No constraint information survives to runtime.
3. **Selections re-resolve at the substituted receiver.** A constraint
   method call `x.Double()` inside a generic body has a `types.Selection`
   against the type parameter; the emitter must re-derive it against the
   substituted concrete type (`types.LookupFieldOrMethod`), reusing the
   existing concrete-receiver paths (`methodReceiverArg`'s pointer/value
   logic applies unchanged).
4. **Operations on type-parameter operands compute at the type argument.**
   Spec §Operators: "The operands are represented as values of the type
   argument that the type parameter is instantiated with, and the operation
   is computed with the precision of that type argument." — monomorphization
   verbatim. The per-construct type-set legality prose (slice exprs
   §3967-3969, built-ins §7401-7638, etc., post-go1.25 core-type removal)
   is entirely static: go/types has already enforced it by the time we
   emit; nothing of it survives to runtime.
5. **Zero values, composite literals, conversions, builtins** at
   substituted types route through existing machinery — all sibling
   non-generic corpus ids (`min-max-edge/defined-int`, `defined-string`,
   `clear-delete-edge/*-defined-*`, `copy-edge/defined-slices`,
   `new-expr/*`, `variadic/*`) already PASS, so the 8 scattered generic ids
   flip on instantiation alone.

---

## 5. What stays fail-closed, with reasons

- **Reflection / `reflect` on any type** — global extern policy;
  additionally the one feature that genuinely defeats monomorphization.
- **Channels through type parameters** (`type-parameter-channel-ops`) —
  monomorphizes fine, then hits the channels gap; stays `frontend-export`
  red until the channels arc, stated in the re-pin header.
- **Floats/complex generic cases** (17 ids) — double-blocked; flip when
  their domain slices land (floats decided; complex later).
- **Instantiations whose closure exceeds the registry cap** (§2e) — loud
  refusal, negative-tested if we can build a small program that trips it
  cheaply (else the cap check gets a frontend unit test).
- **Anything with type args outside the admitted type surface** — existing
  `emitType` refusals, unchanged.
- **Uninstantiated generic declarations** are simply not emitted (dead
  code, unreachable at runtime by §2b's spec facts); a G0 case pins that a
  passing subject beside an unused generic helper stays green through the
  transition.

---

## 6. Goose/Perennial comparison

**[FACT]** The arc plan's shorthand "Goose-style monomorphization" is
inaccurate about present-day Goose: current goose does NOT monomorphize.
It translates generic functions POLYMORPHICALLY — type parameters become
Gallina binders on the translated definition (`deps/goose/goose.go:
2546-2561`: `FuncUnfold` declarations parameterized over type params;
`goose.go:2196-2201` receiver type params as `fd.TypeArgs`), and every use
site resolves through a semantic environment indexed by name and type
arguments: `FuncResolve name [type-args]`
(`goose.go:766-773`, args from `ctx.info.Instances`), stepped by
Perennial's `go_func_resolve_step :: ⟦FuncResolve n ts, #()⟧ ⤳ #(functions
n ts)` (`deps/perennial/new/golang/defn/postlang.v:390`) — a
`functions : name → list go_type → val` map in the model. Receivers may not
be specialized generic types (`goose.go:2159-2164` `nope("instantiated
type argument in function with non-parameter")`); `testdata/examples/
unittest/generics/` covers generic structs, function getters, methods,
containers — roughly our corpus's shapes.

Why we should NOT copy this: it works for Goose because glang/GooseLang is
an untyped lambda calculus where `go_type` is ordinary Gallina DATA — type
passing is free, and their semantics is not executable against an oracle.
For GoCore — a deep, executable, differentially validated, kernel-reducible
interpreter with types in values — the same design is precisely the
"semantic dictionaries" option: `Ty` binders, a runtime (name × type-args)
function environment, constraint plumbing, all inside the statement TCB
(§2d's cost). Their design is the right call for their architecture and the
wrong one for ours; the divergence is deliberate and recorded here.

Where we exceed them if §2 stands: runtime `comparable`-at-`any` panics
(their `IsStrictlyComparable`-based equality lives in the floats note's
§10 findings territory), instantiated-type dynamic identity (asserts on
`Pair[int]`), F-bounded constraints, generic aliases — all differentially
validated. Where they are lighter: no whole-program requirement, and
per-package translation composes; ours re-monomorphizes per program.

---

## 7. Nondeterminism doctrine check

Generics introduce **no choice-consumption sites and no envelope
statements**: every latitude in the feature (which instantiations exist,
their identities, constraint checking) is compile-time and deterministic;
gc's shape/dictionary strategy is observation-equivalent to full stenciling
(§2c), so there is no implementation latitude to envelope. Membership lane
untouched; possibilistic scope untouched. (Recorded so the standing
envelope-fidelity audit dimension has an explicit "nothing here" to
confirm, rather than an omission to wonder about.)

---

## 8. Implementation sketch, in slices

Blast radius if the recommendation stands: **frontend-only plus one Lean
rendering fix and corpus additions.** Files: `tools/nativefrontend/main.go`
(Instances map, gotypesalias enablement), `tools/nativefrontend/emit.go`
(instantiation-aware `emitIdent`/`emitSelector`/`emitCall`/`emitIndex`,
generic-origin skip in `emitGenDeclTypes`, `curFuncName` mangle for lifted
literals), `tools/nativefrontend/wire.go` (`emitType`: `*types.TypeParam`
via the active substitution — unbound param fails closed; instantiated
`*types.Named` → mangled TypeId; `*types.Alias` → `types.Unalias`), new
`tools/nativefrontend/mono.go` (substitution, closure worklist, mangler +
registry + collision checks + cap), `GoLean/GoCore/Value.lean`
(`TypeId.unqualified` only), corpus + baseline re-pin. `NativeJson.lean`/
`NativeToIR.lean`/GoCore semantics: **zero changes** — the wire schema is
unchanged.

- **G0 — guardrails first** (no runtime code). Verify classification:
  [FACT] all 75 rows already classify `frontend-export` — correct today.
  Add missing edges, each as canonical Go that `go run` accepts:
  `generics/instantiated-type-assert` (assert `any`→`box[int]` ok /
  `box[string]` panic — pins mangled identity, panic text, and via a
  typed-struct observation the `Name()` contract, i.e. the §3.4 fix);
  `generics/structural-transparency` (`[]T`@int asserted as `[]int`;
  `map[string]T`@int as `map[string]int`); `generics/nested-instantiation`
  (`box[box[int]]`); `generics/derived-instantiation` (`outer[T]` calling
  `inner[[]T]` — pins the closure walk); `generics/self-recursive`
  (`f[T]` recursion, zero-weight cycle); `generics/generic-closure` (func
  literal inside a generic function capturing a `T`-typed variable — pins
  lambda-lifting × instantiation naming); `generics/instantiated-map-key`
  (`map[Pair[int]]int` — comparability of instantiated struct keys);
  `generics/unused-generic-helper` (passing subject beside a never-
  instantiated generic — must stay green throughout); negative-corpus
  `generics/instantiation-cycle` (both sides refuse at compile time, §2b).
  All must classify `frontend-export` (or expected-negative) before any
  implementation lands.
- **G1 — mangler + registry + `TypeId.unqualified` fix.** `mono.go`'s
  identity layer with frontend unit tests (Go-side `go test` is available
  to the frontend tree) covering §3.2's renderings against the §3.1 probe
  outputs; the Lean rendering fix with an eval test. No corpus movement.
- **G2 — function instantiation closure.** Substitution over the original
  `types.Info` (per §4.1); worklist from concrete `Instances` entries,
  substituting enclosing bindings for derived entries (§2a probe);
  `types.Instantiate` for Named/Alias/Signature nodes, a small structural
  walker for composites (mirroring unexported `go/types/subst.go`;
  investigate at implementation time whether the `NewSignatureType`+
  `Instantiate` wrapper trick lets go/types do even the composite walk —
  prefer whichever keeps more substitution inside go/types' own code).
  Flips: `identity`, `inference`, `zero-values`, `zero-composite`,
  `higher-order-inference/*`, `comparable-*`, `type-set-constraint`,
  `constraint-embedding`, `type-parameter-{slice,map,composite-literal,
  conversion}-ops`, `map-slice`, bools 4, scattered 8, G0's function-level
  cases. Full `scripts/ci --diff`; re-pin with per-cluster reasons.
- **G3 — generic types, methods, instantiated interfaces.** Instantiated
  typeDefs (struct/defined/interface kinds) from the registry; methods
  stenciled per receiver instantiation; dispatch/satisfaction tables at
  instantiated interface TypeIds. Flips: `generic-struct`,
  `defined-slice-type`, `generic-map-type`, `recursive-generic-type`,
  `type-method-dispatch`, `instantiated-{function,method}-value`,
  `method-constraint-call`, `method-and-type-set-constraint`,
  `recursive-constraints/*`, `generic-interface-value`, remaining G0 cases.
- **G4 — generic aliases** (`gotypesalias` enablement + `Unalias`
  transparency): flips `type-aliases/*` (5). Kept separate because it
  touches the type-check *configuration*, which deserves its own focused
  diff.
- Remaining red after G4: `type-parameter-channel-ops` (channels arc),
  floats/complex 17 (their slices) — stated in the final re-pin header.

Worker-model note per CLAUDE.md: this is semantics-adjacent frontend work —
Fable-class workers for G2/G3.

---

## 9. Decisions of record (2026-08-05, coordinator)

All seven resolved as recommended, with the forcing doctrine cited so
the arc-final audit can re-argue from the same ground:

1. **Strategy: frontend monomorphization, GoCore and wire schema
   untouched.** Forced by GoCore purity + the statement-TCB doctrine:
   the spec defines instantiation as substitution, go/types' mono check
   guarantees feasibility for every program the frontend accepts, and
   gc's own dictionary strategy is observation-equivalent (§2c) — so
   the dictionary alternative would grow the statement language and the
   proof surface for zero observable gain. The Goose divergence is
   deliberate and recorded (§6).
2. **Mangling: `TypeString` with package-NAME qualifier** (§3.2) —
   consistent with the existing TypeId keying and backed by the
   package-name-collision gate; the gc `LinkString` divergence is
   recorded, not accidental.
3. **`TypeId.unqualified` fix ships in G1.** A knowingly wrong renderer
   contradicts the contract-honesty rule its own docstring states; the
   fix is rendering-only and eval-tested at birth.
4. **Registry cap 10,000, tested as a frontend unit test** (a corpus
   case tripping the cap would be a pathological monster; the refusal
   itself is loud, which is what fail-closed requires).
5. **`gotypesalias`: prefer `os.Setenv` at frontend startup** (the
   binary stays self-contained; wrapper scripts stay dumb) — G4
   confirms at implementation time if the API surface disagrees.
6. **The floats-ordering dependency is accepted as stated**: arc order
   already puts floats (slice 4) before generics (slice 6), and no
   int-observable proxy for constant-non-refolding exists (§4.1). The
   floats/complex generic cases pin it differentially once both land.
7. **G0 case list: the nine proposed probes adopted** as scoped in §8.
