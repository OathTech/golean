# GoLean semantic-divergence review — 2026-08-08

This note records a read-only, adversarial review of GoLean executable
semantics against real Go, plus a bounded grossmith campaign and review of the
grossmith integration. The work ran from the isolated GoLean worktree
`semantic-divergence-review-20260808`; no source or corpus behavior was changed
during the review.

Revisions:

- GoLean: `06933964cfb2642b9b91962af56da151bc47994f`
- grossmith: `a09bf911fc189912d570746104f0c7d357ffca11`
- Go toolchain observed by the grossmith worker: Go 1.26.5

## 1. Confirmed new fidelity bug: tuple-forwarded call arguments bypass interface boxing

### Minimal fixed-arity witness

```go
package main

func pair() (int, string) { return 7, "x" }

func sink(a, b any) int {
	return a.(int) + len(b.(string))
}

func tupleFixed() int { return sink(pair()) }
```

Real Go returns `8`. The native frontend accepts the program, but GoLean ends
with:

```text
unsupported: type assertion from non-interface value GoLean.GoValue.int 7
```

This is a fidelity bug rather than a frontend coverage refusal: the construct
crosses the frontend boundary, then the machine receives a raw integer in a
slot whose Go static type is `any`.

### Minimal variadic witness

```go
package main

func pair() (int, string) { return 7, "x" }

func sink(xs ...any) int {
	return xs[0].(int) + len(xs[1].(string))
}

func tupleVariadic() int { return sink(pair()) }
```

Real Go again returns `8`. GoLean produces the same non-interface assertion
failure for the raw integer.

### Boundary matrix

The following six forms were run through the strict differential path:

| Source tuple and destination | Result |
| --- | --- |
| `(int, string)` to `(any, any)` | FAIL: first raw value is not boxed |
| `(int, string)` to `...any` | FAIL: first raw value is not boxed |
| `(int, string)` to `(int, any)` | FAIL: second raw value is not boxed |
| `(int, string)` to `(int, ...any)` | FAIL: variadic raw value is not boxed |
| `(int, string)` to `(int, string)` | PASS control |
| `(any, any)` to `(any, any)` | PASS control |

The mixed and fixed-plus-variadic failures report the raw string rather than
the integer, showing that exact concrete slots remain correct and only the
component requiring implicit interface conversion is malformed.

### Root cause

`tools/nativefrontend/emit.go:5533-5567`, in `emitCallArgs`, handles tuple
forwarding `g(f())` by calling `splatMultiCall` and treating the resulting temp
identifiers as the final arguments. The nonvariadic path returns `idents`
directly. The variadic path copies fixed identifiers directly and constructs
the variadic slice from raw identifiers.

Both paths bypass `wrapInterfaceConversion`, which ordinary call arguments use
in the code immediately following this special case (`emit.go:5571` onward).
The analogous tuple-forwarded return path already performs per-result
interface wrapping (`emit.go:1774-1801`), further localizing this as an omission
in the call-argument special case.

Likely fix shape: retain the source tuple component types, pair each splatted
temporary with its destination parameter type (or variadic element type), and
apply the same interface-conversion logic used for ordinary arguments before
returning fixed arguments or constructing the variadic slice.

Regression coverage should preserve the full six-form matrix above, especially
the mixed and fixed-plus-variadic cases; a test containing only `(any, any)` can
miss a per-position error.

### Reproduction

Scratch artifacts were retained at:

```text
/tmp/golean-review-tuple.YNLHVV
```

The principal differential results are `results2.tsv` and `results3.tsv`.
They recorded two failures in the basic fixed/variadic run, followed by two
expected failures and two passing controls in the boundary-matrix run.

## 2. Focused adversarial semantic probes

An independent corpus-gap review exercised thin or interaction-heavy Go rules.
It did not find another new wrong answer.

The following cases agreed with real Go:

- value method values capture a copy of their receiver, while pointer method
  values observe later mutation;
- selecting a value-receiver method value through a nil pointer panics at
  selection time;
- equality and map insertion panic for deeply nested incomparable dynamic
  interface values, including an array containing an interface containing a
  slice;
- NaN map keys cannot be found or deleted by a newly evaluated equal-looking
  NaN key, while `clear` removes them;
- positive and negative floating zero denote the same map key;
- variadic `s...` passing preserves the expected slice alias;
- `copy` from a defined string containing invalid UTF-8 to a defined byte slice
  preserves the raw bytes;
- ranging over an array-valued function call evaluates the call in the tested
  one-variable and two-variable forms.

Useful missing green regression cells discovered by source search are:

- nil-pointer selection timing for a value-receiver method value;
- deep interface-comparability panic paths for equality and map insertion;
- NaN map lookup/delete/clear behavior;
- positive-zero versus negative-zero map replacement;
- defined-string to defined-byte-slice copying with invalid UTF-8;
- value-versus-pointer method-value receiver capture.

Two additional probes failed closed as coverage gaps rather than producing a
wrong answer:

- slice-to-array conversion;
- floating-point `min`/`max`.

Scratch directories retained by that review:

```text
/tmp/golean-corpus-audit.M9Ioif
/tmp/golean-corpus-audit2.X1GwYM
/tmp/golean-corpus-audit3.nepkDO
/tmp/golean-corpus-audit4.ODEsDe
/tmp/golean-corpus-audit5.1xc5Tk
```

## 3. Existing untriaged fidelity/coverage failures rerun

A focused rerun of ten entries from `baselines/untriaged-ids` reproduced all
ten failures:

- `arrays/pointer-array`: wrong-stuck on indexing a pointer to an array;
- `pointers/nil-array-index-panic`: wrong-stuck instead of Go's nil-pointer
  panic;
- seven rune/string or defined-slice conversion cases: unsupported conversion;
- `structs/tag-pointer-conversion`: wrong-stuck because the machine retains the
  source struct identity after the permitted pointer conversion.

These are not new discoveries, but the rerun confirms that the baseline entries
remain live at the reviewed revision. Unsupported conversion cases should stay
distinguished from the wrong-stuck pointer-to-array and struct-identity cases.

## 4. Grossmith campaign

### Command and environment

The campaign used only scratch caches and output:

```sh
env HOME=/tmp/grossmith-review.0xJZn7/home \
  ELAN_HOME=/home/dev/.elan \
  GOCACHE=/tmp/grossmith-review.0xJZn7/go-cache \
  GOMODCACHE=/tmp/grossmith-review.0xJZn7/go-mod-cache \
  go run ./cmd/gengo \
  -n 250 \
  -seed 2000000 \
  -out /tmp/grossmith-review.0xJZn7/campaign \
  -clone golean:/home/dev/projects/golean/.review-worktrees/semantic-divergence \
  -workers 16 \
  -timeout 15s
```

Seeds were `2000000..2000249`.

### Results

| Verdict | Count |
| --- | ---: |
| Semantic match | 225 |
| Clone infrastructure failure | 25 |
| Semantic mismatch | 0 |
| Total | 250 |

Generation/tag highlights:

| Surface | Count |
| --- | ---: |
| `multi_assign` | 121 |
| ordinary panic paths | 47 |
| `recover_wrapper` | 40 |
| wrapper-caught panics | 19 |
| `aggregate_observed` | 21 |
| `string_range` | 10 |
| `slice_triple` | 4 |
| `type_switch` | 3 |

Infrastructure-failure breakdown:

- 19 `$runtime.Error` method-set failures from caught runtime panics;
- 6 instances of the already-known short-circuit-call quarantine.

Thus this batch found no new semantic mismatch, but its nominal recover-wrapper
coverage materially overstates the panic behavior actually compared, as
described below.

Campaign artifacts were retained at:

```text
/tmp/grossmith-review.0xJZn7
```

## 5. Grossmith review notes

### G1. Recover-wrapper panic coverage is currently ineffective against GoLean

The recover wrapper was intended to expose panic identity, assignment/store
ordering before a panic, and recovered partial state. In
`gen/gen.go:1171-1176`, `fuzzPanicCode` attempts `p.(error)` and then calls
`e.Error()`.

For every runtime panic actually caught in this campaign, that path introduced
the unsupported `$runtime.Error` method-set behavior on the GoLean clone:

```text
wrapper-caught: 19
successfully compared caught-panic executions: 0
```

The 40 generated `recover_wrapper` cases therefore do not mean that 40
recovered-panic behaviors were validated. Green wrapper cases were no-panic
paths; all 19 cases that reached the intended caught-runtime-panic observation
became clone-infrastructure failures.

This is the most important grossmith finding from the campaign because it
blocks the exact high-yield surface requested in
`docs/2026-08-07_grossmith-requests.md` R1. The campaign summary should report
successful caught-panic comparisons separately from generated wrapper count
and wrapper-caught count.

Possible directions, to be evaluated in the grossmith project:

- avoid method dispatch on recovered runtime errors in the GoLean profile;
- encode known runtime panic classes through an observation mechanism already
  supported by the clone;
- or treat `$runtime.Error` support as an explicit prerequisite and label the
  recover rung unavailable until it lands.

The replacement must still distinguish which panic occurred. Merely recording
that some panic was recovered would lose the ordering discrimination R1 was
designed to provide.

### G2. Go 1.26.5 VCS stamping breaks stock tests/reference builds

With the stock environment, `go test ./...` and generated reference builds
failed with:

```text
error obtaining VCS status: exit status 128
Use -buildvcs=false to disable VCS stamping.
```

`GcAdapter` invokes `go build -o ... .` and constructs a sanitized environment
in `harness/harness.go:252-273`. The sanitized environment does not preserve an
external `GOFLAGS=-buildvcs=false`, leaving no ordinary campaign CLI route to
the workaround.

For this review, a scratch-only Go environment was configured with:

```sh
go env -w GOFLAGS=-buildvcs=false
```

After that workaround, the full grossmith test suite passed and the campaign
ran. A durable fix should make the reference build independent of ambient VCS
stamping, either by adding `-buildvcs=false` to the build invocation or by
supporting a deliberate build-flags/environment path.

### G3. Interpretation of this campaign

The zero semantic mismatches are useful evidence for the subset that reached
both interpreters, particularly the dense multi-assignment generation. They are
not evidence for recovered runtime-panic semantics: that entire realized
subpopulation failed at clone infrastructure. Future campaign reports should
state both the gross generated count and the successfully judged count for
high-value feature rungs, so profile incompatibilities cannot look like tested
semantic coverage.

## 6. Suggested follow-up

1. File and pin the tuple-forwarding/interface-boxing bug with fixed,
   variadic, mixed, and fixed-plus-variadic red cases plus the two controls.
2. Fix the special tuple-forwarding arm by applying destination-directed
   interface conversion per tuple component; rerun the focused matrix and
   `lake build`.
3. Add a small green adversarial corpus batch for the missing regression cells
   in Section 2.
4. Make grossmith's recovered-panic observation profile-compatible, then rerun
   the same seeds so the 19 currently unjudged caught-panic executions become
   real differential comparisons.
5. Harden grossmith's Go build invocation against VCS stamping and add a stock
   environment test for it.

