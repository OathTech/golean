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
| Floating point | missing | - | Add finite operations, infinities, NaN, signed zero, comparisons, conversions. |
| Complex numbers | missing | - | Add construction, real/imag, arithmetic, comparison restrictions. |
| Constants and iota | partial | `constants/const-precision`, `constants/iota-blank`, `constants/iota-expressions` | Add default constant types, typed constants, constant overflow rejection, constant division with floats. |
| Assignment and evaluation order | active | `ints/multi-assign`, `multi-assign/tuple-assign-order` | Add call-return assignment, map/slice/index target ordering, side-effecting selectors. |
| If and basic loops | active | `ints/if-return`, `if/if-init-scope`, `ints/while1`, `ints/break-continue` | Add post statements with side effects, infinite loops with returns. |
| Switch | partial | `control-flow/switch-basic`, `control-flow/switch-fallthrough` | Add expression evaluation once, duplicate/default restrictions in negative lane, type switch variants. |
| Labels, break, continue, goto | partial | `control-flow/labeled-break`, `control-flow/labeled-continue` | Add `goto`, invalid label jumps, scope-crossing restrictions. |
| Functions and returns | partial | `returns/naked-return`, `strings/string-call`, `functions/closure-share` | Add recursion, higher-order functions, function nil comparison, multi-result call placement. |
| Defer, panic, recover | partial | `defer/defer-arg-eval`, `defer/defer-named-return`, `panic-recover/recover-direct` | Add panic replacement by deferred panic, recover return values, multiple defers, `panic(nil)` version case. |
| Pointers and allocation | partial | `new/new-basic`, `pointers/pointer-identity`, `new/new-struct` | Add pointer-to-pointer, nil dereference in more contexts, addressability edge cases. |
| Structs and fields | partial | `structs/swap`, `embedding/embedded-field-shadow` | Add tags if relevant, anonymous fields, comparability with interface fields. |
| Methods and method sets | partial | `methods/method-value-copy`, `methods/method-expression`, `methods/pointer-receiver-method-set` | Add interface method dispatch, promoted method ambiguity, pointer/value auto-addressing. |
| Arrays | active | `arrays/arrays`, `arrays/array-copy`, `arrays/array-comparable`, `arrays/nested-arrays` | Add larger nested literals and pointer-to-array edge cases. |
| Slices | active | `slices/slice-append`, `slices/full-slice`, `slices/reslice-capacity`, `slices/slice-header-by-value` | Add append growth policy observations only when portable; avoid relying on spare capacity not guaranteed by spec except when constructed. |
| Maps | partial | `maps/map-basic`, `maps/map-comma-ok`, `maps/delete-nil-map`, `maps/map-copy-write` | Add more key types, delete existing key, overwrite, map range deferred as nondet. |
| Strings, bytes, runes | partial | `strings/string-index`, `strings/string-slice`, `strings/string-byte-conversion`, `strings/string-int-rune` | Add range over string, `[]rune` conversion, invalid UTF-8 range behavior. |
| Interfaces | partial | `interfaces/nil-interface`, `interfaces/interface-compare`, `interfaces/type-assertions` | Add interface method calls, embedding interactions, dynamic equality inside structs, nil typed values across types. |
| Generics | partial | `negative/compile/generics/generic-method` | Add executable generic functions, inference, constraints, type sets, zero values. |
| Package initialization | partial | `init/package-init-order` | Add multiple files, multiple init functions, import initialization order. |
| Imports and visibility | partial | `negative/compile/imports/unused-import` | Add exported/unexported selectors across packages when multi-package harness exists. |
| Builtins | partial | many slice/map/string cases | Add `clear`, `min`, `max`, `complex`, `real`, `imag`, `close`, `recover`, `panic`, `copy`, `append`, `delete`, `len`, `cap`, `make`, `new`. |
| Channels | missing | - | Add deterministic basics once oracle can handle blocking/panic/close cleanly; select fairness is deferred-nondet. |
| Goroutines and scheduling | deferred-nondet | - | Needs relation-style or repeated-run oracle; do not place scheduler-dependent cases in default lane. |
| Map iteration order | deferred-nondet | - | Needs set/permutation observation or relation-style oracle. |
| Unsafe and layout | deferred-unsafe | - | Needs explicit unsafe policy. |
| Standard library semantics | deferred-stdlib | - | Track separately from language semantics; reduce only language-relevant parts into active cases. |
| Go version-specific features | partial | current active cases use baseline installed Go | Add ledger notes per case for Go 1.21+ `panic(nil)`, Go 1.22 range/loop changes, Go 1.23 iterators. |
