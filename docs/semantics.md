# GoCore Semantics Design

GoCore is the deep embedding we use for execution, differential testing, and
eventually verification in Lean.

Gobra is a frontend. Gobra JSON is a strict wire format. Neither Gobra IR nor
the JSON shape is the semantic center of the project.

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
- Make unsupported semantics explicit. Surprise inputs should fail early.
- Keep the executable semantics simple enough to differential-test heavily.
- Leave room for proof-oriented layers: weakest preconditions, VCGs, Iris-style
  separation logic, or generated proof helpers.
- Use reference designs from Goose and Perennial where they have already solved
  the shape of Go memory and struct reasoning.

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
GoCore as a Lean deep embedding for execution and differential testing, then
generate a proof layer over GoCore that resembles Perennial's typed field
access and WP automation. That keeps the executable semantics small enough to
test while leaving a route to Iris-Lean or Lean-native weakest preconditions.

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

The current implementation has locals plus stable variable addresses. The next
step is to split that into a real heap:

```text
Addr := Nat

Value :=
  | unit
  | bool Bool
  | int Int
  | addr Addr
  | nil
  | struct typeName (fields : fieldName -> Value)
  | unsupported feature

HeapCell :=
  | value Value
```

This is deliberately more concrete than a proof-only separation model. It gives
us an executable semantics first. Proof layers can later interpret the same
heap into separation assertions.

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

## Assertions And Specs

GoCore has two related but distinct concepts:

- executable assertions, used for differential testing;
- verification specs, used for proof obligations.

For now, the executable subset may interpret simple boolean assertions and fail
on separation assertions such as `acc`.

Later, separation assertions should become proof-level propositions over the
heap model. They should not be erased, but they also should not block execution
of ordinary Go code when used only as Gobra verification annotations.

## Gobra Lowering Policy

`GobraToIR` is where Gobra-specific details belong.

Examples:

- Gobra's `MethodBody` lowers to a GoCore block.
- Gobra `LocalVar`, `In`, and `Out` ids lower to GoCore variable ids.
- Gobra `Ref(Var(x))` lowers to GoCore address-of variable.
- Gobra field access lowers to `StructFieldGet` or `StructFieldRef`.
- Gobra verification-only artifacts either lower to GoCore specs or fail as
  unsupported, depending on whether we understand them.

If a Gobra node has no clear GoCore meaning, lowering should fail or produce an
explicit unsupported GoCore node. It should not silently approximate.

## Differential Testing

The execution story should compare observations, not proof terms.

Observation:

```text
status : ok | panic | assertion_error | unsupported | stuck
returns : Array Value
message : Option String
```

The main comparisons are:

- Go source execution vs GoCore execution;
- Gobra JSON lowering vs generated Lean execution;
- GoCore evaluator vs future proof/WP execution view, where applicable.

Unsupported is an acceptable result only when the test manifest expects it.
Unexpected unsupported features are coverage bugs.

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

`scripts/gobra-smoke` should lower and execute the `swap` client far enough to
reach its expected final `assert false`, producing an assertion-error
observation for the right reason.

That milestone exercises the memory model without jumping ahead to maps,
slices, interfaces, concurrency, or Iris integration.
