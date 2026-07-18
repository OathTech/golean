# Slice Model

This note records the slice-design checkpoint before adding GoCore slice
semantics.

The goal is not to mirror Gobra's reasoning model. Gobra is useful here because
its frontend already recognizes Go slice constructs and emits typed internal
nodes. GoCore should model Go slice behavior directly, in a shape that supports
both executable differential testing and a later relational/Iris proof layer.

This design intentionally separates hard semantic commitments from policy
choices that should remain open until differential testing against real Go
programs gives us evidence. We should commit early to facts required by Go's
observable behavior and future proofs, such as alias-preserving backing storage.
We should avoid baking in accidental choices where Go leaves room to the
implementation, where runtime behavior has changed across versions, or where
our corpus has not yet forced a precise model.

## References Reviewed

Gobra's internal AST has the frontend surface we need:

- `Length` and `Capacity` nodes for `len` and `cap`;
- `IndexedExp` over arrays, pointer-to-array values, slices, maps, and strings;
- `Slice(base, low, high, max, baseUnderlyingType)` for two-index and
  three-index slicing;
- `MakeSlice` and `NewSliceLit` for `make([]T, len, cap?)` and slice literals.

The relevant desugaring is conservative: omitted slice bounds are filled in
before Gobra's internal AST reaches us, and slicing is only emitted for
recognized array, slice, pointer-to-array, or string bases. That makes Gobra a
good temporary source of typed syntax, but not the source of semantics.

New Goose/Perennial is the strongest semantic reference. It represents a Go
slice as a primitive `slice.t` descriptor with pointer, length, and capacity.
The descriptor points into an array-like backing allocation:

```text
slice_index_ref elem i s = array_index_ref elem i s.ptr
slice(s, low, high)      = { ptr := ptr + low, len := high-low, cap := cap-low }
full_slice(s, low, high, max)
                          = { ptr := ptr + low, len := high-low, cap := max-low }
```

For arrays, slicing constructs the same descriptor into the array allocation.
For `make`, Perennial allocates an array of capacity `cap` and returns a slice
whose visible length is `len`. For append, Perennial reuses the backing array
when capacity is sufficient; otherwise it allocates a fresh backing array with
nondeterministic extra capacity.

The proof-side lesson is even more important. Perennial separates ownership of
the visible slice from ownership of the spare capacity:

- `own_slice s vs dq` owns the visible `len(s)` elements, with a special nil
  case for the valid empty nil slice;
- `own_slice_cap elem s dq` owns the capacity tail after `len(s)`, with
  arbitrary contents;
- slicing lemmas split and recombine ownership around array segments;
- append proofs consume capacity ownership in the in-place case and allocate
  fresh ownership in the growing case.

That split is the design constraint we should preserve.

## Modelling Options

### Copied Vector Slice

Represent a slice value as its visible elements, perhaps with a length and
capacity field.

This is attractive for executable tests, but it is the wrong semantic model.
It loses aliasing between slices, arrays, and pointer-to-array expressions.
It cannot explain why mutating `s[0]` may mutate another slice or the original
array. It also gives Iris no natural backing location for element ownership.

This should not be used except as a throwaway toy.

### Descriptor Into Backing Locations

Represent a slice value as a descriptor:

```lean
structure SliceValue where
  elem   : GoCore.Ty
  base   : Option Loc
  offset : Nat
  len    : Nat
  cap    : Nat
```

The intended invariant is:

- `base = none` means the nil slice, and then `offset = len = cap = 0`;
- `base = some l` means the backing storage starts at `l`;
- `len <= cap`;
- element `i` for `0 <= i < len` lives at `Loc.index l (offset + i)`;
- capacity element `i` for `len <= i < cap` is also backed by that same
  allocation, even if its contents are not visible through the slice value.

This is the recommended model.

It keeps executable behavior straightforward: `len` and `cap` read descriptor
fields, indexing checks `i < len`, slicing adjusts `offset`, `len`, and `cap`,
and `append` either writes into the existing backing store or allocates a new
one. It also matches the future Iris shape: `own_slice` and `own_slice_cap` can
be predicates over segments of the backing location.

The commitment here is the aliasing shape, not every runtime policy around it.
The descriptor leaves room to refine allocation, growth, zero-size storage,
overflow, and panic-message details as the differential corpus grows.

### Separate Slice Backing Store Object

Instead of pointing slices at an existing array location, allocate a distinct
backing-store heap object for `make` and slice literals.

This may be useful internally, but it should not become a separate semantic
world. Array-to-slice and pointer-to-array slicing must share storage with the
source array. The clean version is therefore to let both fixed arrays and
dynamic slice backing allocations be addressable aggregate storage, with
`Loc.index` giving element locations in either case.

### Literal Goose Port

Porting Goose's slice definitions directly is tempting, but not quite right for
this project. Goose targets GooseLang/Rocq and gets proof infrastructure from
Perennial. GoCore should stay a Lean deep embedding with an executable
interpreter and later a relation. We should reuse the semantic structure, not
the exact generated language.

## Recommended GoCore Shape

Add `Ty.slice elem` and a `GoValue.slice` descriptor value. Treat slices as
primitive values in the same sense as Go: assigning a slice copies the
descriptor, not the backing elements.

Use the descriptor as a stable interface between frontend lowering, executable
testing, and future proof rules. Keep lower-level choices behind that
interface where possible. Examples of choices that should remain refinable are
append growth, representation of zero-capacity non-nil slices, exact overflow
cutoffs, and whether the executable heap stores aggregate arrays or decomposed
element cells.

Add GoCore operations for:

- `makeSlice elem len cap?`;
- `slice base low high max?`;
- `indexGet` and `indexAddr` over slice values;
- `length` and `capacity` over slices;
- slice literals by allocating an array backing store and slicing it;
- `append` and `copy` as primitive slice operations over descriptor/backing
  storage.

Bounds failures should be `panic`. Malformed descriptors, missing backing
storage, negative lengths after integer conversion, unsupported base kinds, and
unknown frontend tags should be `stuck` or `unsupported`, not silently repaired.

For array slicing, be careful about addressability. A Go slice expression over
an array shares the array's storage. The lowering should therefore preserve an
lvalue/address for array and pointer-to-array bases rather than evaluating the
array to a copied rvalue and slicing that copy.

For slice slicing:

```text
s[low:high]     => same base, offset + low, len = high-low, cap = cap-low
s[low:high:max] => same base, offset + low, len = high-low, cap = max-low
```

The two-index high bound for a slice must be checked against `len` in Go
source syntax, while the resulting capacity is based on the original capacity.
The three-index max bound is checked against capacity.

For `make([]T, len, cap)`, allocate backing storage of capacity `cap`,
zero-initialized, and return a descriptor with visible length `len`. The nil
slice remains the zero value for slice types. `make([]T, 0)` may return a
non-nil empty slice in Go; tests should not equate all empty slices with nil.

For `append`, use the Go semantic split:

- if `newLen <= cap(s)`, write appended elements into the existing backing
  store at `offset + oldLen` and return the same base/offset with larger len;
- otherwise allocate a fresh backing store, copy visible elements, append new
  elements, and return a descriptor over the fresh store.

The exact new capacity after allocation is observable through `cap`, but Go
does not specify a single growth formula. Perennial models this with
nondeterministic extra capacity. The executable interpreter now uses a
deterministic Go-runtime-oriented growth policy so current differential tests
that observe `cap` after reallocation have a concrete oracle. The relational
semantics should still allow any fresh capacity `>= newLen`.

This pattern should generalize beyond append. When Go specifies a family of
allowed behaviors, the relation should express the family. The executable
interpreter should pick a deterministic member for testing, and the
differential harness should record whether a test is checking portable Go
behavior or current-runtime behavior.

## Open Refinement Points

The following choices should stay explicit until real-program differential
testing narrows them:

- append growth policy after reallocation for the future relational semantics;
- exact behavior of zero-length and zero-capacity non-nil slices;
- integer overflow and allocation-size limits for `make`, `append`, and bounds
  arithmetic;
- panic messages and panic classification details where Go exposes text;
- string slicing and byte indexing, which have different aliasing and
  immutability properties from array/slice backing storage;
- how aggressively the executable heap decomposes aggregate arrays into
  element-addressable cells.

Failing closed is part of preserving this design space. If a case reaches one
of these boundaries before it is modeled, it should produce an explicit
`unsupported` or `stuck` outcome with a feature tag, not a guessed semantics.

## Iris Impact

The descriptor model is compatible with Iris-Lean. The copied-vector model is
not.

The future relational semantics should have primitive rules for slice creation,
slicing, indexing, `len`, `cap`, `append`, and `copy`. The executable evaluator
can remain a deterministic implementation for supported concrete runs, but the
relation should be the semantic authority where Go permits implementation
choice, especially append growth.

The proof-facing predicates should mirror Perennial's split:

```text
own_array_segment base start values dq
own_slice s values dq
own_slice_cap s dq
```

`own_slice` should be either the nil empty slice or ownership of the visible
segment `[offset, offset + len)`. `own_slice_cap` should describe the tail
`[offset + len, offset + cap)`, usually without exposing concrete contents.

This lets proofs state the right append rule:

- in-capacity append consumes or transforms `own_slice_cap` and preserves
  aliases to the same backing store;
- growing append allocates fresh ownership and leaves old aliases pointing at
  the old backing store.

The current path-location design (`Loc.field`, `Loc.index`) remains a good fit,
but the proof layer must not depend on slices owning copied arrays. It should
reason about backing locations and segments. If we later change the executable
heap from aggregate arrays to more decomposed element cells, the public slice
descriptor should not need to change.

## Implementation Order

1. Add the slice type and descriptor value with invariant checks.
2. Add `len`, `cap`, nil zero value, slice equality with nil, and slice index
   get/address.
3. Add `make` and slice literals with zero-initialized backing storage.
4. Add array-to-slice and pointer-to-array slicing, preserving addressability.
5. Add slice-to-slice and full-slice expressions.
6. Added `copy`, including overlap-preserving differential coverage.
7. Added `append`, including backing allocation for capacity tails and focused
   differential coverage for capacity-observing growth.
8. Keep every unsupported Gobra wire node and every unsupported GoCore operation
   fail-closed.
