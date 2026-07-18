# GoCore Semantics Design

GoCore is the deep embedding we use for execution, differential testing, and
eventually verification in Lean.

Gobra is a frontend. Gobra JSON is a strict wire format. Neither Gobra IR nor
the JSON shape is the semantic center of the project. Gobra's verification
language is not part of GoCore runtime semantics.

The intended pipeline is:

```text
Go/Gobra source
  -> Gobra frontend/export
  -> Gobra JSON wire AST
  -> GobraToIR lowering
  -> GoCore deep embedding
  -> Lean execution and proof infrastructure
```

## Design Goals

- Keep GoCore close to Go's runtime behavior, not Gobra's implementation
  details.
- Keep Gobra assertions, specs, predicates, invariants, and ghost artifacts out
  of GoCore. They may be decoded fail-closed as wire data, but lowering erases
  or rejects them instead of treating them as Go behavior.
- Make unsupported semantics explicit. Surprise inputs should fail early.
- Keep the executable semantics simple enough to differential-test heavily.
- Keep the proof-facing semantics relational. The executable interpreter is a
  testing artifact and should not become the only definition of program meaning.
- Leave room for proof-oriented layers: weakest preconditions, VCGs, Iris-style
  separation logic, or generated proof helpers.
- Use reference designs from Goose and Perennial where they have already solved
  the shape of Go memory and struct reasoning.

## Semantic Authority And Executability

The project needs two related views of GoCore:

- an executable interpreter, used for differential testing and fast regression
  checks;
- a relational small-step or big-step semantics, used as the proof-facing
  semantic authority and as the future bridge to Iris-Lean.

The executable interpreter can be deterministic and convenient. It should be
treated as an implementation of the relation for supported terminating concrete
runs, not as the final semantics. This matters for Iris because proof rules are
normally stated over relations, weakest-precondition transitions, or operational
steps, not over a single recursive evaluator function.

Design consequence:

- keep syntax, values, locations, typed errors, and execution outcomes reusable
  by both views;
- avoid hiding semantic choices inside opaque interpreter recursion;
- define new features in a shape that can be mirrored as rules later;
- prove, where practical, that the executable interpreter is sound with respect
  to the relational semantics on the supported deterministic subset.

Differential testing should continue to drive feature development. The relation
does not replace executable testing; it gives us a proof-compatible statement of
what those tests are exercising.

## What We Reuse From Goose

Goose has the right high-level split:

- source/frontend translation is separate from the semantic core;
- the generated language has primitives such as allocation, load, store,
  dereference, struct literal construction, field get, and field reference;
- struct proof support is generated around typed field projections and typed
  points-to predicates.

The old Goose code uses concepts like:

- `GoAlloc` for allocating Go values;
- `![T] p` for typed load through a pointer;
- `p <-[T] v` for typed store;
- `StructFieldGet T "field" v` for projecting from a struct value;
- `StructFieldRef T "field" p` for the address of a struct field;
- generated per-struct typed points-to facts in Perennial's newer proofgen.

We should copy the architecture, not the exact surface syntax. In Lean, these
should become typed GoCore operations and proof lemmas.

## New Goose / Perennial Notes

Perennial's `new/` Goose design is more relevant than the older Goose printer
alone. It is built as:

```text
Go source
  -> Goose generated Rocq code
  -> GooseLang lambda calculus with Go-specific instructions
  -> Perennial/Iris WP and typed memory proof layer
```

Its design rule is:

- desugar Go constructs at translation time when the result is simple;
- encode sequencing, bindings, returns, breaks, and loops using the lambda core
  when possible;
- add Go-specific instructions only when the Go feature needs semantic support.

Important Go-specific instructions include:

- `GoAlloc`, `GoLoad`, and `GoStore`;
- `GoZeroVal` and `CompositeLiteral`;
- `StructFieldGet`, `StructFieldSet`, and `StructFieldRef`;
- `Index`, `IndexRef`, `Slice`, and `FullSlice`;
- `FuncResolve` and `MethodResolve`;
- map, interface, string, and channel-specific internal operations.

The struct memory model is the most important reference point. New Goose treats
primitive-like values as one heap location, but structs are decomposed by field:

- allocating a struct preallocates a base location and allocates each field at
  its `StructFieldRef` address;
- loading a struct folds over its fields, loading each field and rebuilding a
  struct value with `StructFieldSet`;
- storing a struct folds over its fields and stores each projected field value;
- generated proof support defines typed points-to predicates as separating
  conjunctions of field points-to facts.

This strongly supports using path-like locations in GoCore:

```text
Loc :=
  | base Addr
  | field Loc typeName fieldName
```

New Goose also separates executable/generated code from proof automation:

- generated code files define Rocq structs, function bodies, package
  assumptions, and function/method unfold instances;
- generated proof files define `TypedPointsto`, `IntoValTypedUnderlying`, and
  field access instances;
- proof tactics such as `wp_auto`, `wp_load`, `wp_store`, and `wp_alloc` consume
  those instances.

For this project, the lesson is not to port Goose literally. We should keep
GoCore as a Lean deep embedding with an executable interpreter for differential
testing, then define a relational/proof-facing semantics over the same syntax
and memory model. Generated proof support can then resemble Perennial's typed
field access and WP automation. That keeps tests fast while leaving a route to
Iris-Lean or Lean-native weakest preconditions.

One caveat: Perennial's updater notes that new Goose does not currently have
executable tests for generated code because evaluation is blocked by sealing.
That is a reason to keep our own GoCore evaluator first-class instead of relying
only on proof-mode execution.

## Runtime Model

The executable GoCore state should contain:

```text
locals : variable id -> value
heap   : address -> heap cell
next   : next fresh address
```

The current implementation has heap-backed locals, path-like locations, typed
errors, and execution outcomes:

```text
Addr := Nat

IntKind :=
  | int | uint
  | int8 | uint8 | int16 | uint16 | int32 | uint32 | int64 | uint64
  | unbounded name

Value :=
  | unit
  | bool Bool
  | int Int IntKind
  | string GoString
  | addr Loc
  | nil
  | struct typeName (fields : fieldName -> Value)
  | array (Array Value)
  | slice SliceValue
  | map MapValue
  | mapData (Array (Value × Value))

Loc :=
  | base Addr
  | field Loc typeName fieldName
  | index Loc index
```

This is deliberately more concrete than a proof-only separation model. It gives
us executable tests early. The relational semantics and proof layers can later
interpret the same heap into separation assertions.

The executable interpreter currently uses a 64-bit policy for `int` and `uint`,
matching the Gobra export and local differential harness. Fixed-width integer
values are normalized on typed stores, arithmetic, and integer-to-integer
conversions. Shifts use the left operand's integer kind as the result kind,
normalize fixed-width results, implement signed arithmetic right shift, and
classify negative shift counts as panics. Non-integer conversions are explicitly
unsupported until their Go semantics are modeled. The future relational semantics should make
architecture-dependent `int`/`uint` width an explicit parameter rather than
baking in this executable testing policy.

Bitwise operators use fixed-width modular bit patterns for typed integer
values, then normalize the result back to the selected result kind. Untyped
unbounded bitwise constants remain unsupported until the constant model exists.

GoCore strings are byte sequences, not Lean strings:

```text
GoString := Array UInt8
```

Lean `String` remains a convenience for direct GoCore tests, but frontend
lowering uses the exact byte payload exported by Gobra JSON. This choice is required by Go:
`len(s)`, `s[i]`, string slicing, string comparison, and `[]byte(s)` all operate
over bytes, and Go string values can contain invalid UTF-8 after slicing or byte
construction. It also matches the strongest reference point in Perennial's new
Goose model: `go_string` is a byte string, string literals elaborate to byte
lists, string indexing returns `w8`, concatenation appends byte strings, and
ordering is lexicographic over bytes.

Gobra's frontend is compatible with this even though its internal string
literal node stores a Scala `String`: Gobra indexes `StringT` as `byte`, permits
`string`/`[]byte` conversions, axiomatizes string length as byte length, and
models conversion to `[]byte` by equating each string byte with the resulting
slice element. Gobra's Viper encoding is intentionally abstract for proofs; it
should not be our semantic storage model.

String literals are fail-closed at the Gobra JSON boundary: `StringLit` must
include a `bytes` array, and each element must fit in `UInt8`. The Gobra fork
derives this array from the source literal syntax, including interpreted
escapes such as `\xNN`, `\n`, and `\uNNNN`, so arbitrary-byte string literals
are not reconstructed from JSON text.

String indexing currently returns a `uint8` byte. Two-index string slicing
returns another byte-backed string and can represent invalid UTF-8. Full slice
expressions over strings fail closed because they are not Go. GoCore also
models `[]byte(s)` as allocating a fresh byte slice and `string(bs)` as copying
the visible `uint8` slice bytes into an immutable string. Range-over-string rune
semantics remain a separate future feature.

## Variables And Addresses

Go addressability matters.

A local variable should have:

- an environment binding from source/internal variable id to an address;
- a heap cell at that address containing the current value.

Then:

- reading a variable loads from its address;
- assigning a variable stores to its address;
- `&x` returns the address for `x`;
- pointer equality compares addresses;
- `nil` is distinct from every allocated address.

This matches the direction Goose takes: variables that may be addressed are
represented by locations, and operations use load/store around those locations.

## State Well-Formedness

Updated 2026-07-17 to record the invariants the executable state now
maintains, which the future relational semantics should assume or carry as an
explicit well-formedness predicate.

Locals:

- the local environment is a lexical scope stack, innermost scope first;
- name lookup resolves inner to outer; declaration always binds a fresh
  location in the innermost scope, so shadowing never aliases the outer
  binding;
- block execution pushes a scope on entry and pops exactly that scope on
  every exit path (normal, return, break, continue);
- assignment resolves an existing binding and can never create one;
- every bound name maps to a location present in the heap.

Heap:

- each heap cell carries its value and, when known at allocation, the
  declared type of the allocation (`HeapCell.declaredTy`);
- declarations, parameters, results, `new` allocations, and slice backings
  from conversions, `make`, and `append` record declared types; map data
  cells currently do not (their typing is enforced by the map operations,
  which carry key/value types);
- a store to a typed cell is normalized against the declared type; a store
  to an untyped cell falls back to value-shape coercion, a transitional
  path that should shrink to nothing as remaining allocation sites gain
  types;
- path locations (`Loc.field`, `Loc.index`) address within a base cell;
  field access checks the stored struct's `TypeId` against the path's
  expected `TypeId`.

Identity:

- struct values, interface dynamic tags, the type environment, and field
  paths use semantic `TypeId`s; functions and dispatch metadata use
  `FuncId`s; raw frontend names never act as identity (they are stripped
  and collision-checked once, at the lowering boundary).

The interpreter enforces these dynamically (stuck on violation). The
relational semantics should state them as a predicate over states and prove
preservation, rather than re-deriving them from interpreter behavior.

## Structs And Fields

Struct support should be split into value projection and address projection.

Value projection:

```text
StructFieldGet(typeName, fieldName, value) : Value
```

Field address projection:

```text
StructFieldRef(typeName, fieldName, addr) : Addr
```

For executable testing, field addresses can be represented in one of two ways:

1. Allocate each field as its own heap cell and store field addresses inside the
   struct cell.
2. Treat addresses as paths, for example `base + field path`, and resolve paths
   through nested heap values.

The path model is closer to Goose's `l.[T, "field"]` notation and Perennial's
typed field points-to facts. It is also easier to connect to proofs later.

Recommended Lean model:

```text
Loc :=
  | base Addr
  | field Loc typeName fieldName
```

Then heap ownership and proof predicates can talk about both whole structs and
individual fields without inventing fake addresses for every field.

## Arrays

The first executable array model follows the same path-location idea:

```text
Loc :=
  | base Addr
  | field Loc typeName fieldName
  | index Loc index
```

GoCore array values are fixed-size value arrays. Loading `Loc.index base i`
loads the array at `base` and projects element `i`; storing through that
location rebuilds the array with element `i` replaced. This matches the current
struct strategy and the new Goose array reference closely enough for execution
while keeping the later proof story field/index-local.

Currently supported:

- `ArrayT n elem` lowering for nonnegative `n`;
- zero values for fixed-size arrays;
- Gobra `DfltVal` expressions for supported GoCore types;
- array literals with explicit exported keys;
- array indexing as value projection;
- indexed assignment through `Loc.index`;
- array equality through structural `GoValue` equality;
- `len` and `cap` for fixed-size array values;
- nested array values;
- array parameters and return values in direct calls;
- pointer-to-array indexing and indexed assignment;
- descriptor-backed slices created from arrays;
- descriptor-backed slices created by `make([]T, len, cap)`;
- slice literals;
- typed nil slice literals and equality against nil;
- slice `len`, `cap`, indexing, indexed assignment, two-index slicing, and
  three-index slicing;
- `copy` over slices, including overlapping source/destination ranges;
- `append` over slices, including in-capacity writes and fresh backing-store
  allocation when capacity is exceeded;
- out-of-range indexing as a `panic` observation.

Still pending:

- remaining zero-capacity `make` edge cases, string slicing, and append growth
  policy refinement. See `docs/slice-model.md` for the selected
  descriptor/backing-store design and open refinement points.

## Defined Types

Gobra JSON often gives values the type `DefinedT name` and separately lists the
underlying struct shape in `program.types`.

GoCore should have a type environment:

```text
typeEnv : typeName -> TypeDef

TypeDef :=
  | struct fields
  | alias Ty
  | unsupported feature
```

Lowering from Gobra should resolve `DefinedT` into GoCore `Ty.defined name`;
runtime operations that need fields should consult `typeEnv`.

This keeps Gobra's particular type list format out of the GoCore semantics.

## Function Calls

GoCore should model calls directly:

```text
Stmt.call targets functionName args
Stmt.methodCall targets receiver methodName args
```

Execution should:

- evaluate arguments left-to-right;
- bind parameters in a fresh call frame;
- initialize named results;
- execute the callee body;
- copy result values back into targets.

Initially, GoCore can fail on recursion or impose fuel. Long term, recursion
should be handled by the proof/evaluation infrastructure, not by assuming all
programs terminate.

## Control Flow

Statement execution returns an explicit outcome:

```text
ExecOutcome :=
  | normal state
  | returned state
  | broke state
  | continued state
```

This keeps ordinary sequencing, early returns, and loop control visible in the
semantic interface. `if` evaluates a boolean condition and propagates the
selected branch outcome. `while` consumes `continue` by moving to the next loop
iteration, consumes `break` as normal loop exit, and propagates `return`.

Gobra's frontend currently emits function-body `postprocessing` assignments to
copy transformed local result variables back into result parameters. That is a
frontend artifact, so `GobraToIR` rewrites Gobra `return` statements to execute
those postprocessing assignments before returning. GoCore itself does not know
about Gobra postprocessing.

## Assertions And Specs

Go has no general `assert` statement and Gobra's Dafny/Viper-style annotations
are not the semantics we are building. GoCore therefore has no runtime
assertion statement, function preconditions, or function postconditions.

Gobra assertions, preconditions, postconditions, loop invariants, predicates,
and ghost artifacts are frontend wire data only. The strict importer decodes
the fields Gobra emits so surprise JSON still fails closed, but `GobraToIR`
does not lower those artifacts into executable GoCore behavior.

Future proof extraction may define our own specification language over GoCore
or reinterpret selected source annotations as proof obligations. That should be
a separate layer over Go semantics, not a Gobra compatibility mode inside the
runtime semantics.

## Gobra Lowering Policy

`GobraToIR` is where Gobra-specific details belong.

Examples:

- Gobra's `MethodBody` lowers to a GoCore block.
- Gobra `LocalVar`, `In`, and `Out` ids lower to GoCore variable ids.
- Gobra `Ref(Var(x))` lowers to GoCore address-of variable.
- Gobra field access lowers to `StructFieldGet` or `StructFieldRef`.
- Gobra verification-only artifacts are erased when they do not affect Go
  execution. If a wire node is not verification-only and has no clear GoCore
  meaning, lowering should fail or produce explicit unsupported GoCore.

If a Gobra node has no clear GoCore meaning, lowering should fail or produce an
explicit unsupported GoCore node. It should not silently approximate.

## Differential Testing

The execution story should compare observations, not proof terms.

Observation:

```text
status : ok | panic | unsupported | stuck | error
returns : Array Value
message : Option String
```

The main comparisons are:

- Go source execution vs GoCore execution;
- Gobra JSON lowering vs generated Lean execution;
- GoCore evaluator vs the future relational/proof/WP execution view, where
  applicable.

Lean `unsupported`, `stuck`, and `error` observations are not passing
conformance outcomes. They should be classified loudly in reports so we can
distinguish frontend gaps, semantic gaps, malformed states, and true
differential mismatches without hiding any of them.

## Near-Term Milestone

The next semantic milestone is `examples/swap`.

Required GoCore additions:

- heap-backed local variables;
- `Value.struct`;
- type environment for `DefinedT` structs;
- struct literal construction;
- field get;
- field reference;
- dereference;
- variable and field assignment through locations;
- direct function calls.

Success criterion:

`scripts/diff-one structs/swap` should lower and execute the `swap` client as
ordinary Go after frontend-only artifacts are erased at the lowering boundary.

That milestone exercises the memory model without jumping ahead to maps,
slices, interfaces, concurrency, or Iris integration.
