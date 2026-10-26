# Frontend, wire, and CLI deep-clean review

[AGENT Codex / frontend], 2026-10-26. Reviewed revision
`62bb461463d94c9eb4f3d003aa441db653bd77c3`, in `audit/deepclean-1026`.
This is an independent supporting review. Source, baselines, and existing
documentation were not modified. The findings below are proposals, not owner
decisions or permission to change the product.

## Verdict and scope

The inspected ordinary lowering paths held up well: 26 additional source-level
differentials all agreed with go1.26.5. Nevertheless, the release has a newly
demonstrated resource-admission hole in seeded execution, a permissive parser at
the trusted observation comparator, and two module-admission defects. Those are
concrete failures, not objections to an incomplete language implementation.

I recommend fixing FE-01 through FE-04 before presenting this boundary as
consistently fail-closed. FE-05 is a documentation repair around an already
recorded semantic limitation. I did not establish a new wrong-answer result for
an ordinary valid, unseeded Go source program in this review. That limited
negative result does not establish correctness of the lowering.

The starting surfaces were nativefrontend's file/module selection, identity,
expression and statement lowering, library interception, the strict wire
decoder, entry argument checking, seed parsing/allocation, and observation
comparison. I read their current source and public contracts before checking
existing issue entries. I used local pinned Go sources for implementation
comparisons; no shell network access was needed.

All executions were capped. Go commands used a review-local `GOCACHE` and
`GOTMPDIR`, `GOTOOLCHAIN=local`, and the oracle's `GODEBUG=panicnil=0`. The
resource probe deliberately used a **256 MiB** cap to make a failure small and
bounded; that is not the project's normal resource requirement. No full build,
full gate, or full corpus run was initiated by this reviewer; the coordinator
owns shared validation. Tests used the prepared frontend and interpreter.

| ID | Severity | Finding | Status |
|---|---|---|---|
| FE-01 | High | Seed array types bypass materialization guards and allocate before checking the supplied value | New, reproduced |
| FE-02 | Medium | Observation comparison accepts duplicate keys and replaces invalid surrogate escapes | New, reproduced; independently also found by validation reviewer |
| FE-03 | Medium | The module scanner accepts malformed `go.mod` files rejected by Go | New, reproduced |
| FE-04 | Medium | A module requiring a newer patch toolchain is admitted at the older pinned oracle | New, reproduced |
| FE-05 | Low | Sort limitation's issue link and ruling status disagree across maintained sources | Existing class, documentation defect |

Severity here describes release impact. In particular FE-01 is a local resource
failure, not a claim of a remotely reachable exploit or a silent semantic pass.

## FE-01 — seed arrays bypass the allocation boundary

**Locations:** `GoLean/SeedFile.lean:184–195`,
`GoLean/GoCore/Seed.lean:267–295`, `GoLean/GoCore/Ops.lean:3391–3400`.

The seed type grammar constructs `Ty.array n` for any decimal natural `n`.
Unlike the native-wire type decoder, it does not apply the array length or
materialization footprint limits. `seedCells` runs `seedAllocFrom` before
`seedStoreFrom`; the first phase calls `defaultValue`, whose array arm eagerly
replicates the element default. Only the second phase resolves the supplied
value and checks that its array length matches the declared type.

Consequently a 73-byte seed file can request an enormous allocation even
though its value is an obviously wrong empty array. The function needs no
pointer arguments and need not access the seed at all. `--fuel 0` does not
prevent this setup allocation.

**Reproduction.** From the repository root after building the frontend and
`golean` using the project's normal capped/locked build procedure, create these
files under a fresh `.tmp/` directory. The prepared review worktree already
provides `.tmp/nativefrontend` and `.lake/build/bin/golean`.

`.tmp/fe-seed/main.go`:

```go
package main
func F() int { return 7 }
func main() {}
```

`.tmp/fe-seed/seed.json`:

```json
{"schema":"golean-seed-v1","cells":[{"type":"[67108864]int","value":[]}]}
```

```sh
capped .tmp/nativefrontend --dir .tmp/fe-seed --out .tmp/fe-seed/wire.json
CAPPED_MEM_MAX=256M capped .lake/build/bin/golean native-json-run \
  --input .tmp/fe-seed/wire.json --function F \
  --seed .tmp/fe-seed/seed.json --fuel 0 --no-choice-report
```

Observed: frontend exit 0; interpreter **exit 137**, `capped: KILLED`, no
observation JSON, approximately 0.23 seconds. This was a failure. Changing the
seed type to `[2]int` yields exit 1 with the named refusal
`seed: cell 0: expected array(2), got 0 element(s)` in approximately 0.15 seconds.
The huge count itself, not a deeply nested JSON document, drives the allocation.

**Impact:** this is another entry to unbounded materialization beyond the
append/conversion residuals already described under BUG-131. It bypasses the
existing refusal policy with a tiny input, and the documented per-step fuel
does not bound it. Increasing the process cap only increases the size at which
it fails; an arbitrary natural remains available in the type spelling.

**Repair and acceptance:** validate seed type sizes/footprints before zero
allocation, and check cheaply decidable value-shape errors before allocating
their backing. Preserve the two-phase address scheme needed for cycles and
sharing. Include nested array/defined-struct cases so a flat-length check does
not leave the footprint hole open. Require a bounded, named refusal for the
example with an empty program-output field and low fuel; keep valid cyclic seeds and small
arrays working. A process kill must remain a failing result.

## FE-02 — the comparator discards malformed input before validating it

**Locations:** `GoLean/CLI.lean:983–984` (`decodeObservation`),
`GoLean/CLI.lean:1035` (`runObservationEq`), `docs/cli.md:245–250`.

The observation decoder uses Lean's `Json.parse`, not the strict parser used
for wire and seed files. Its later exact-key/type checks cannot recover keys
that have already been overwritten or Unicode input already replaced during
parsing. The public reference describes each side as strictly decoded and
defines exit 2 for input that cannot be decoded.

The following complete Python reproduction supplies JSON strings directly, as
the CLI requires. Run it from the root; it creates no files.

```python
import subprocess
exe = '.lake/build/bin/golean'
good = '{"schema":"golean-observation-v1","status":"ok","output":"","values":[]}'
probes = [
    ('duplicate status',
     '{"schema":"golean-observation-v1","status":"panic","status":"ok","output":"","values":[]}',
     good),
    ('duplicate output',
     '{"schema":"golean-observation-v1","status":"ok","output":"wrong","output":"","values":[]}',
     good),
    ('unpaired surrogate',
     '{"schema":"golean-observation-v1","status":"ok","output":"\\ud800","values":[]}',
     '{"schema":"golean-observation-v1","status":"ok","output":"\\ufffd","values":[]}'),
]
for name, left, right in probes:
    p = subprocess.run(['capped', exe, 'observation-eq',
                        '--left', left, '--right', right],
                       capture_output=True, text=True)
    print(name, p.returncode, repr(p.stdout), repr(p.stderr))
```

All three returned **0 with empty stdout and stderr**. The first accepted an
observation containing contradictory status fields. The second discarded
different program output. The third compared a malformed surrogate escape as
equal to a replacement character.

**Impact and limit:** the comparator is part of the differential trust surface,
and this permits a malformed observation to receive an equality verdict. I did
not find the current Go or Lean emitters producing these malformed inputs, and
do **not** claim an existing corpus row is falsely green because of this bug.
The trust-boundary failure is nevertheless real: damaged or incorrectly
generated observations are accepted rather than diagnosed.

**Repair and acceptance:** use the existing strict parser at the observation
boundary before schema validation. Require exit 2 for each probe, including
duplicate keys nested in values. Keep structural equality independent of
ordinary JSON whitespace and object-key ordering. A narrow comparator test is
appropriate; a second parallel parser or a large new gate is not needed.

## FE-03 — accepted module directives are not actually parsed

**Locations:** `tools/nativefrontend/modfile.go:124–175`, especially the block
skip at 140–144 and the accepted-directive branch at 165–168.

The scanner recognizes directive names but skips the content of accepted
directives. It never checks `inBlock` at EOF. A valid `go 1.26` line is therefore
enough to admit multiple malformed module files. This contradicts the source
description of a strict, fail-closed scanner and the intended whole-package
rejection posture used for compiler directives and missing function bodies.

**Reproduction.** Create a separate directory for each variant below, containing
the simple `main.go` from FE-01 with `main` replaced by
`func main() { println(F()) }`. Use the whole indicated `go.mod` contents:

| Variant | `go.mod` contents (newlines shown as `\n`) | Pinned Go result |
|---|---|---|
| Missing module argument | `module\ngo 1.26\n` | `usage: module module/path` |
| Duplicate module | `module first\nmodule second\ngo 1.26\n` | `repeated module statement` |
| Unterminated block | `module test\ngo 1.26\nrequire (\n` | `syntax error (unterminated block …)` |
| Malformed require | `module test\ngo 1.26\nrequire nonsense\n` | `usage: require module/path v1.2.3` |

For each directory, from the repository root:

```sh
capped .tmp/nativefrontend --dir .tmp/fe-mod --out .tmp/fe-mod/wire.json
```

Then in that same case directory:

```sh
GO111MODULE=on GOTOOLCHAIN=local GODEBUG=panicnil=0 \
  GOCACHE="$PWD/../go-cache" GOTMPDIR="$PWD/../go-tmp" capped go run .
```

Create the two cache/temp directories under the same `.tmp/` parent before
running the oracle. The frontend emitted a wire and exited **0 in all four
cases**. Go exited **1 in all four cases**, with the errors above. This was not
a network or package-resolution failure.

**Impact:** the frontend certifies a source package whose module configuration
Go refuses. No valid-source runtime wrong answer was demonstrated. The defect
does weaken negative admission and makes the public fail-closed claim broader
than the implementation.

**Repair and acceptance:** validate the actual module grammar before applying
the semantics-specific policy, or explicitly refuse unsupported grammar rather
than skipping it. Cover EOF inside a block, directive multiplicity and required
arguments. Keep dependency loading offline and project-scoped; parsing a file
does not justify invoking an operation that downloads modules or rewrites
`go.mod`/`go.sum`.

## FE-04 — the `go` directive loses its minimum patch version

**Locations:** `tools/nativefrontend/modfile.go:179–183` and `:198–207`.

This is separate from malformed grammar: `go 1.26.99` is syntactically valid.
The scanner reduces it with `version.Lang` to `go1.26`, then compares only that
language version. The module's minimum toolchain requirement disappears. The
same file's explicit `toolchain` directive is checked against the exact pin,
so these two ways to require a newer toolchain are handled inconsistently.

Use the FE-03 program with this `go.mod`:

```text
module test
go 1.26.99
```

Run the same frontend and local oracle commands. The frontend exits **0** and
writes the wire. go1.26.5 exits **1** with:

```text
go: go.mod requires go >= 1.26.99 (running go 1.26.5; GOTOOLCHAIN=local)
```

**Repair and acceptance:** retain and validate the complete Go version against
the pinned toolchain in addition to the existing language-version policy.
Reject a minimum above the pin by name. Keep ordinary `go 1.26` and admissible
patch floors working. This is a different predicate from parsing the module
grammar, so FE-03's repair alone need not close it.

## FE-05 — the accepted sort limitation has stale provenance pointers

**Locations:** `GoLean/GoCore/Machine.lean:1851–1858`,
`docs/2026-08-11_latitude-inventory.md` C10(iii), `docs/BUGS.md` BUG-132,
`docs/2026-10-12_release-readiness.md` row 50.

The code comment calls the sort over-refusal **BUG-131**, but BUG-131 is the
runtime `make` footprint defect; the sort issue is **BUG-132**. BUG-132 and the
latitude entry still describe the class as pending owner disposition, whereas
the current backlog says the owner accepted it as a recorded over-refusal on
2026-10-25. These are maintained sources, not merely different historical
snapshots. Fix the pointer and reconcile disposition wording without deleting
the known semantic limitation.

I independently reproduced the limitation with this smaller program:

```go
package main
import "slices"
func F() int {
    a := []int{7}
    ch := make(chan int)
    go func() { ch <- a[0] }()
    slices.Sort(a)
    return <-ch
}
func main() { println(F()) }
```

Lower/run using the FE-01 pattern without the seed or zero fuel; compare with
`GODEBUG=panicnil=0 capped go run -race .tmp/fe-sort/main.go`, using local Go
cache/temp directories. Go returned **7, exit 0**; the interpreter returned
**`status:race`, exit 1**. A sorted three-element window also over-refused, and
a concurrent writer to the singleton returned 9 under race-clean Go but `race`
under the interpreter. The sort source does no element access for a singleton;
the intercepted operation records a read and write regardless.

This is **not a newly discovered bug class**: BUG-132 and its red corpus pin
already record the read-side case, and the backlog records its acceptance.
Release material should nevertheless treat `race` as the model's detection
result, not automatically proof that this Go execution races. The successful
sequential controls below do not justify a concurrency equivalence claim.

## What held

The 26 additional ordinary lowering probes all produced the same result under
go1.26.5 and the default-tape interpreter. These were focused spot checks, not
an exhaustive sweep or a recertification of the corpus.

| Probe family | Concrete controls and observed results |
|---|---|
| Method value capture | Direct value receiver, promoted value receiver, promoted pointer receiver whose embedding is replaced, and interface method value whose interface variable is reassigned: each retained the intended receiver and returned 3 |
| Deferred evaluation | Variadic spread captured the original slice header while observing later element mutation: 42; deferred value receiver kept 3; named array return was updated by defer to `[9,2]` |
| Variadic nilness | Omitted variadic arguments, non-nil empty spread, nil spread distinguished correctly: 121 |
| Loop captures | Go 1.26 for-clause declarations, range declarations, and continue each gave captured digits 012; assignment to an outer range variable gave 222; closures created in the loop condition gave 0123 |
| Range evaluation | Index-only range over a nil pointer's array field avoided evaluation and returned 3; pointer-to-array range observed a changed element (193); array-value range kept its snapshot (123); explicit blank second variable retained the nil-dereference panic, recovered as 9 |
| Assignment and overlap | Named-slice overlapping append: 134; simultaneous index-variable/array assignment: 293; simultaneous index-variable/map assignment: 182 |
| Type identity and generics | Typed nil type switch: 1; constrained generic interface method call: 7; generic type switch distinguished int/int64 (12); local declared types from distinct generic instantiations remained unequal (2) |
| Operand order | Function-value array selection with mutation during argument evaluation: 10; slice operand replaced during bound evaluation: 9, matching the pinned compiler's realized order |

Two sequential sort controls additionally passed: a `[]uint64` containing 0,
2^63 and 2^64−1 sorted in unsigned order (middle element 2^63); a slice of a
defined int8 type ordered −128, 0 and 127 correctly. The three concurrency sort
controls described in FE-05 failed differential agreement as expected from the
known class.

Entry arguments accepted the int8 minimum/maximum and uint64 maximum and
refused int8 underflow/overflow, uint64 overflow and negative uint64 by name.
The CLI accepted `--arg-int 1e2` as 100 and `--arg-int -0` as 0, while refusing
`1.0` as non-integer; seed-file syntax intentionally refused exponent and
negative-zero tokens. No finding is asserted from that documented separation
between argument parsing and the seed grammar.

Seed int8 underflow produced a named `stuck` refusal. The valid int8 minimum
seed with zero fuel reached `fuel-out`, showing setup completed. Ordinary wire
mutants refused by name with status `error`: an unknown program key, wrong
platform architecture, unknown function key, duplicate function identifier,
and missing function result field. Those controls contrast with the separate
permissive observation parser; the wire and seed parsers did not share FE-02
in the tested paths.

## Limits and proposed release work

I did not exhaustively enumerate Go syntax, imported packages, generic
instantiations, seed graphs, Unicode, arbitrary wire mutations, execution
schedules, or operating-system error modes. The 26 deterministic probes ran
the default tape and did not establish whole-envelope membership. I made no
claim about binaries compiled on a different host or Go version. The module
scanner has other suspicious error-swallowing paths, such as its upward
`os.Stat` search, but I did not reproduce a distinct bug there and do not list
it as a confirmed finding.

Proposed punch-list entries:

1. Close seed materialization before allocation, including nested footprints;
   add a small reproducer that fails by name without a cap kill (FE-01).
2. Route observation input through the existing strict parser and pin malformed
   JSON rejection (FE-02).
3. Validate or refuse unsupported module grammar; include these negative
   package cases without widening unrelated gates (FE-03).
4. Check the complete minimum Go version against the oracle pin (FE-04).
5. Correct the sort issue reference and disposition status; keep its accepted
   limitation explicit in the release's supported-profile/accounting material
   (FE-05 and existing BUG-132).

All probe files, generated wires, and review-local caches under
`.tmp/deepclean-frontend/` were designated ephemeral and removed after recording
these conclusions and reproduction instructions. No raw run dump is part of
this report set.
