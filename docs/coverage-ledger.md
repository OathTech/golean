# Differential Coverage Ledger

This is the mutable coverage accounting document for the Go differential test
suite. The stable buildout policy lives in
`docs/coverage-buildout-plan.md`; do not edit that plan during ordinary corpus
buildout. Update this ledger when adding meaningful feature areas, promoting
challenge cases, or discovering deferred/unexpressible behavior.

The ledger does not need to list every single case, but it must identify
representative active cases and important missing subareas.

## Status Values

- `active`: active corpus contains focused cases;
- `partial`: active corpus contains some cases but important subareas remain;
- `deferred-nondet`: needs a nondeterministic or relational oracle;
- `deferred-stdlib`: primarily standard-library/runtime package behavior;
- `deferred-unsafe`: requires unsafe/layout policy;
- `deferred-version`: requires a Go version not available or not yet adopted;
- `missing`: known important area with no active case yet;
- `unexpressible`: cannot currently be expressed honestly in the harness.

When marking `unexpressible`, explain the harness limitation. Do not use
`unexpressible` for ordinary frontend or semantics gaps.

## Ledger

This ledger is intentionally high level. It should become more detailed as the
suite grows. Representative cases are examples, not an exhaustive manifest.

| Area | Status | Representative Active Cases | Missing / Deferred Notes |
| --- | --- | --- | --- |
| Literals and zero values | partial | `arrays/array-zero`, `new/new-nil-values`, `maps/map-literal-empty` | Add booleans, composite literals across all aggregate types, typed/untyped literal interactions. |
| Basic arithmetic and comparisons | active | `ints/scalars`, `ints/bitwise`, `strings/string-compare` | Add broader unsigned comparisons and mixed defined types. |
| Integer widths and overflow | partial | `ints/int8-wrap`, `ints/byte-conversion`, `ints/shifts` | Add all integer widths, unsigned wrap, conversion matrices, architecture-sized `int` policy notes. |
| Floating point | partial | `floats/finite-arithmetic`, `floats/division-specials`, `floats/signed-zero`, `floats/to-int-truncation`, `negative/compile/floats/implicit-int-float` | Add float32-specific arithmetic beyond complex parts, rounding precision boundaries, overflow/underflow, typed/untyped float constants, and more conversion matrix cases. |
| Complex numbers | partial | `complex/basic`, `complex/equality`, `complex/zero-value`, `complex/complex64-parts`, `negative/compile/complex/complex-order`, `negative/compile/complex/complex-to-int` | Add complex constants, complex64 arithmetic precision, division, NaN/Inf parts, typed aliases, and more invalid operation/conversion restrictions. |
| Constants and iota | partial | `constants/const-precision`, `constants/iota-blank`, `constants/iota-expressions` | Add default constant types, typed constants, constant overflow rejection, constant division with floats. |
| Assignment and evaluation order | active | `ints/multi-assign`, `multi-assign/tuple-assign-order` | Add call-return assignment, map/slice/index target ordering, side-effecting selectors. |
| If and basic loops | active | `ints/if-return`, `if/if-init-scope`, `ints/while1`, `ints/break-continue` | Add post statements with side effects, infinite loops with returns. |
| Switch | partial | `control-flow/switch-basic`, `control-flow/switch-fallthrough` | Add expression evaluation once, duplicate/default restrictions in negative lane, type switch variants. |
| Labels, break, continue, goto | partial | `control-flow/labeled-break`, `control-flow/labeled-continue` | Add `goto`, invalid label jumps, scope-crossing restrictions. |
| Functions and returns | partial | `returns/naked-return`, `functions/closure-share`, `functions/recursion`, `functions/higher-order-arg`, `functions/function-nil-compare`, `returns/multi-result-argument` | Add function values returned from functions, method values as callbacks, recursive methods, and more multi-result call placement edge cases. |
| Defer, panic, recover | partial | `defer/defer-arg-eval`, `defer/defer-named-return`, `panic-recover/recover-direct` | Add panic replacement by deferred panic, recover return values, multiple defers, `panic(nil)` version case. |
| Pointers and allocation | partial | `new/new-basic`, `pointers/pointer-identity`, `new/new-struct` | Add pointer-to-pointer, nil dereference in more contexts, addressability edge cases. |
| Structs and fields | partial | `structs/swap`, `embedding/embedded-field-shadow` | Add tags if relevant, anonymous fields, comparability with interface fields. |
| Methods and method sets | partial | `methods/method-value-copy`, `methods/method-expression`, `methods/pointer-receiver-method-set` | Add interface method dispatch, promoted method ambiguity, pointer/value auto-addressing. |
| Arrays | active | `arrays/arrays`, `arrays/array-copy`, `arrays/array-comparable`, `arrays/nested-arrays` | Add larger nested literals and pointer-to-array edge cases. |
| Slices | active | `slices/slice-append`, `slices/full-slice`, `slices/reslice-capacity`, `slices/slice-header-by-value` | Add append growth policy observations only when portable; avoid relying on spare capacity not guaranteed by spec except when constructed. |
| Maps | partial | `maps/map-basic`, `maps/map-comma-ok`, `maps/delete-nil-map`, `maps/map-copy-write` | Add more key types, delete existing key, overwrite, map range deferred as nondet. |
| Strings, bytes, runes | partial | `strings/string-index`, `strings/string-slice`, `strings/string-byte-conversion`, `strings/range-byte-offsets`, `strings/range-invalid-utf8`, `strings/rune-slice-conversion`, `strings/rune-string-conversion` | Add more string comparison edge cases, range interactions with combining marks, and compile-negative string immutability variants. |
| Interfaces | partial | `interfaces/nil-interface`, `interfaces/interface-compare`, `interfaces/type-assertions` | Add interface method calls, embedding interactions, dynamic equality inside structs, nil typed values across types. |
| Generics | partial | `generics/identity`, `generics/inference`, `generics/zero-values`, `generics/comparable-constraint`, `generics/type-set-constraint`, `generics/generic-struct`, `generics/map-slice`, `negative/compile/generics/generic-method`, `negative/compile/generics/noncomparable-constraint`, `negative/compile/generics/type-set-value`, `negative/compile/generics/bad-type-argument` | Add generic methods as compile-negative variants beyond the existing simple case, type aliases/defined generic types, generic interfaces as ordinary interface values, constraint embedding, type inference failure cases, and method dispatch involving generic types. |
| Package initialization | partial | `init/package-init-order` | Add multiple files, multiple init functions, import initialization order. |
| Imports and visibility | partial | `negative/compile/imports/unused-import` | Add exported/unexported selectors across packages when multi-package harness exists. |
| Builtins | partial | many slice/map/string cases plus `complex/basic`, `complex/complex64-parts`, `channels/closed-receive`, `channels/close-nil-panic` | Add `clear`, `min`, `max`; broaden `complex`, `real`, `imag`, `close`, `recover`, `panic`, `copy`, `append`, `delete`, `len`, `cap`, `make`, and `new` coverage. |
| Channels | partial | `channels/buffered-basic`, `channels/closed-receive`, `channels/nil-values`, `channels/range-closed`, `channels/select-nil-default`, `channels/send-closed-panic`, `channels/close-closed-panic`, `channels/close-nil-panic`, `negative/compile/channels/send-receive-only`, `negative/compile/channels/receive-send-only`, `negative/compile/channels/close-receive-only` | Add unbuffered communication only with a nondeterminism/blocking-safe oracle, directional channel assignments/conversions, more select cases with deterministic readiness, and relational cases for select fairness/blocking. |
| Goroutines and scheduling | deferred-nondet | - | Needs relation-style or repeated-run oracle; do not place scheduler-dependent cases in default lane. |
| Map iteration order | deferred-nondet | - | Needs set/permutation observation or relation-style oracle. |
| Unsafe and layout | deferred-unsafe | - | Needs explicit unsafe policy. |
| Standard library semantics | deferred-stdlib | - | Track separately from language semantics; reduce only language-relevant parts into active cases. |
| Go version-specific features | partial | current active cases use baseline installed Go | Add ledger notes per case for Go 1.21+ `panic(nil)`, Go 1.22 range/loop changes, Go 1.23 iterators. |
