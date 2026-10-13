# Fresh-context release review — 2026-10-13

[AGENT Codex] Independent review of `a08850473569dd55eebc5350cfe9d66c624d359f`,
on `audit/codexpass-1013`. Findings and recommendations below are the reviewer's;
they are not owner rulings or authorization to change the release contract.

## Verdict

**FAIL: I would not release this tip as meeting the owner's fail-closed objective.**
Three admitted classes return deterministic wrong answers without a warning or
refusal: blank struct fields, embedded file data, and source-selected panic-nil
semantics. The first two fail even against the pinned toolchain's ordinary language
and build behavior. The third exposes a runtime-setting precondition that the
corpus imposes but the consumer boundary neither enforces nor clearly states.

These are not merely unexplored choices. For five witnesses across these classes,
`coverage-observations` completed with **one observation, zero choice sites**, and
that observation was the wrong one. The default `native-json-run` choice report
also printed no warning. More sampling or a larger enumeration budget cannot fix
these witnesses.

The proof checks passed. That does not contradict this verdict: executable/relation
coherence establishes agreement inside the model, not that its shared operations or
the Go-to-GoCore lowering implement Go correctly.

My recommendation is to fix or refuse F1–F3 before the first release, record their
regressions in the differential/negative corpus, and explicitly resolve F4–F5.
The release procedure allows the owner to tag with separately reported failed
predicates; this review does not change that rule. Its assessment is that the
requested fail-closed condition does not hold at this commit.

## Method and reach

I read the four requested entry points and the review brief, then followed the
admission, value-conversion, struct-equality, file-selection, CLI, enumeration and
proof-audit paths. I compared small Go programs with the native frontend and the
provided Lean executable, inspected the corresponding code, and checked the pinned
Go compiler/spec sources in `deps/go`. I did not use earlier reviewers' verdicts
as premises. After finding witnesses, I searched the earlier passes and bug ledger
for overlap. `//go:debug` was already mentioned as owed/outside BUG-109's scope;
that is reported in F3 rather than presented as a newly discovered omission.

All runtime witnesses were confirmed using a **fresh frontend built from this
checkout**, after initial exploration with the supplied `.tmp/nativefrontend`.
Go was `go1.26.5 linux/amd64`; Lean was pinned to `v4.32.2`. The Lean executable and
oleans were the prepared build. I did not rebuild or re-certify the full corpus.
The last source change under `GoLean/` was `dc365be0` (2026-10-13 04:38 UTC), before
the supplied executable's 05:10 timestamp; this is a consistency observation,
not a reproducible-build attestation.

Commands ran under `capped`; Go build cache and compiler temporary files for my
probes were worktree-local. The explicit audit/replay sequence acquired the primary
root's `artifacts/build-lock.d`, wrote the owner, and released it under a trap.
One earlier discovery command, `capped lake env leanchecker --help`, unexpectedly
performed a default replay and exited 0 silently: this toolchain ignores that flag
instead of displaying help. That invocation had no lock. I inspected its source
and then ran the explicit, verbose replay under the lock. No full build or full
CI/corpus gate was run.

The report's program reproduction blocks were executed verbatim and reproduced
their recorded outcomes. Its static `rg` search failed with `Permission denied`
inside the capped Bash batch, but returned no matches when run directly.
`nono why` does not support an execute query; its read query reported `ALLOWED`.
Nono sandbox unconfirmed; this permission failure needs a non-sandbox diagnosis.
That batch's final shell exit was not used as an aggregate test verdict.

There is no material difference between the user's brief and the checked-in brief.
The read-only instruction and the permitted build/probe instructions admit two
possible readings: no tracked source edits other than the report, or no writes
outside the report at all. The latter would forbid the expressly requested scratch
probes and lock owner. I confined experimental writes to disposable scratch and
the specified lock; no tracked runtime, baseline, charter or build configuration
was changed.

## Reproduction setup

The following Bash setup is shared by F1–F3 and F5. Run it from the reviewed
worktree. Each subsequent block supplies a complete program. `println` writes to
Go's stderr; compare those bytes with the Lean JSON's `output`. The helper prints
every exit code, including intentional negative controls, and never treats a
nonzero exit as a pass. All Go compilation uses a private cache.

```bash
review_scratch="$PWD/.tmp/codex-zero-context-repro"
mkdir -p "$review_scratch/gocache" "$review_scratch/gotmp"
review_env=(GO111MODULE=off GOTOOLCHAIN=local GOFLAGS=
  "GOCACHE=$review_scratch/gocache" "GOTMPDIR=$review_scratch/gotmp")
capped env "${review_env[@]}" go build \
  -o "$review_scratch/nativefrontend" ./tools/nativefrontend

review_run() {
  local case_name=$1 entry=${2:-subject} rc
  if capped env -u GODEBUG "${review_env[@]}" \
      go run "$review_scratch/$case_name/main.go"; then rc=0; else rc=$?; fi
  echo "gc exit: $rc"
  if capped env "${review_env[@]}" "$review_scratch/nativefrontend" \
      --dir "$review_scratch/$case_name" \
      --out "$review_scratch/$case_name/wire.json"; then
    echo 'frontend exit: 0'
  else
    rc=$?
    echo "frontend exit: $rc (no interpreter run)"
    return "$rc"
  fi
  if capped .lake/build/bin/golean native-json-run \
      --input "$review_scratch/$case_name/wire.json" --function "$entry"; then
    rc=0
  else
    rc=$?
  fi
  echo "golean exit: $rc"
}
```

## F1 — HIGH: blank struct fields participate in equality and map-key identity

**Actual wrong answers in ordinary, sequential Go.** The frontend stores the
positional literal's `_` operand, and `valueEqFields` compares it like a named
field. Go compares only non-blank fields. This changes boolean results, map
cardinality and lookups, and can invent a recoverable panic. A panic observation
is a claimed Go behavior, not a refusal; recovering this invented panic also gives
an ordinary `status:ok` wrong result.

```bash
mkdir -p "$review_scratch/blank-fields"
cat > "$review_scratch/blank-fields/main.go" <<'GO'
package main
type S struct { _ int; X int }
type T struct { _ any; X int }
func recovered() (r int) {
    defer func() { if recover() != nil { r = 99 } }()
    a := T{[]int{1}, 2}
    if a == a { return 7 }
    return 3
}
func subject() {
    a, b := S{1, 2}, S{9, 2}
    println(a == b)
    m := map[S]int{a: 3, b: 7}
    println(len(m), m[a], m[b])
    println(recovered())
}
func main() { subject() }
GO
review_run blank-fields
```

| Observation | gc | GoLean |
|---|---|---|
| Equality | `true` | `false` |
| Map size and two lookups | `1 7 7` | `2 3 7` |
| Recovered-comparison result | `7` | `99` |
| Exit/status | exit 0 | exit 0, `status:ok` |

Without the defer, comparing `T{[]int{1},2}` with itself gives GoLean
`status:panic`, `runtime error: comparing uncomparable type []int`; gc prints
`true`. A separate effectful blank operand printed its side effect on both sides
but still produced the wrong comparison. A repair must retain evaluation of blank
operands, including side effects and panics; simply deleting their expressions
would introduce another wrong answer.

Cause: `tools/nativefrontend/emit.go:7829` emits every positional field;
`GoLean/GoCore/Ops.lean:3279` retains each normalized value;
`Ops.lean:3697` compares every field with no blank-field exclusion. The pinned
spec's comparison rule is at `deps/go/doc/go_spec.html:5178`; gc skips blank fields
in `deps/go/src/cmd/compile/internal/compare/compare.go:186` and discards their
stored literal values in `walk/complit.go:219`.

Recommendation: repair blank-field construction/equality coherently, preserving
static comparability rules and operand evaluation, or refuse the affected shapes
until that repair is justified. Cover equality, map operations, an interface-valued
blank, and an effectful operand. The original separate equality/map/recovery
witnesses each enumerated as a singleton containing the wrong result.

## F2 — HIGH: `//go:embed` is accepted and its data silently becomes zero

**A non-Go initialization mechanism crosses the admission boundary without a
model or refusal.** A string populated by the compiler is treated as an ordinary
uninitialized global. This does not require `unsafe`, reflection, concurrency or
a corrupt wire.

```bash
mkdir -p "$review_scratch/embed"
printf 'hello' > "$review_scratch/embed/data.txt"
cat > "$review_scratch/embed/main.go" <<'GO'
package main
import _ "embed"
//go:embed data.txt
var x string
func subject() { println(len(x)) }
func main() { subject() }
GO
review_run embed
```

gc prints `5`; GoLean returns `{"output":"0\n",...,"status":"ok","values":[]}`.
Both exit 0; the frontend exits 0 with no warning. Enumeration also returns only
the zero result. Remove `data.txt` and run the same commands: gc rejects the
package (`pattern data.txt: no matching files found`), while the frontend still
exports and GoLean still answers zero. Both variants were observed.

`tools/nativefrontend/fileselect.go:129–166` checks cgo, non-Go sources and build
constraints, but does not reject or implement embed patterns. The `go/build`
package already supplies `EmbedPatterns`/`EmbedPatternPos`
(`deps/go/src/go/build/build.go:495`); selecting Go source files alone is not a
complete account of what gc initializes.

There is related over-acceptance at user `//go:linkname` directives. This negative
control is independently reproducible with the helper:

```bash
mkdir -p "$review_scratch/linkname"
cat > "$review_scratch/linkname/main.go" <<'GO'
package main
import _ "unsafe"
//go:linkname x runtime.zerobase
var x uintptr
func subject() { println(x) }
func main() { subject() }
GO
review_run linkname
```

gc rejects it (`link: main: invalid reference to runtime.zerobase`, exit 1);
GoLean answers `0`, `status:ok`, exit 0. This is **acceptance of an invalid program**,
not a numerical differential against a running Go program. The existing poisoning
of linked globals in `emit.go:1117–1128` applies only to library units. A separate
local alias to `main.x` also exported and ran despite gc's symbol-redeclaration
failure. Thus the directive issue is broader than missing embed file contents.

Recommendation: refuse unmodeled meaning-bearing directives at source admission,
in root and imported user packages, before their effects can disappear. Implement
embedding only with an explicit data/provenance contract. Add positive-language
wrong-answer witnesses and compiler/linker-rejection controls; `go/types` success
alone does not establish gc acceptance.

## F3 — HIGH: source `//go:debug` changes behavior but is silently ignored

```bash
mkdir -p "$review_scratch/debug"
cat > "$review_scratch/debug/main.go" <<'GO'
//go:debug panicnil=1
package main
func f() (r bool) {
    defer func() { r = recover() == nil }()
    panic(nil)
}
func subject() { println(f()) }
func main() { subject() }
GO
review_run debug
```

With ambient `GODEBUG` removed by the helper, pinned gc prints `true`. GoLean
returns `false`, `status:ok`, exit 0, no warning. Its enumerated set is the singleton
`false`. Replacing the directive with `//go:debug nonexistentSetting=1` and using
`func subject() { println(7) }` gives a second admission failure: gc rejects the
unknown setting; GoLean exports and answers `7`.

This gap is acknowledged in `tools/nativefrontend/modfile.go:29–34` and
`docs/BUGS.md`'s BUG-109 discussion: source debug lines and the `godebug` module
directive were left outside that repair. It is not covered by a current refusal.
`emit.go:9912` states the interpreter's panic-nil decision, and
`scripts/diff-coverage:1476` forces `GODEBUG=panicnil=0` on the oracle. I separately
ran the valid witness with that setting: gc then prints `false`, masking the
consumer-facing discrepancy.

There are two materially different contract readings here. If the product always
means Go under the additional runtime constraint `GODEBUG=panicnil=0`, the valid
directive witness is outside that execution profile. If the public pipeline means
the Go program supplied to the pinned gc toolchain under its source-selected
defaults, this is a direct wrong answer. The release entry points do not make that
extra runtime constraint a clear consumer precondition, and neither reading
justifies accepting the invalid-setting witness. A buried owed item is not an
implemented fail-closed boundary.

Recommendation: refuse unsupported source/module runtime settings, or carry and
model an explicitly admitted setting. State the oracle's runtime configuration as
part of the consumer contract and test source settings without overriding away the
behavior under examination.

## F4 — MEDIUM: the standing proof gate does not replay the kernel

The gate builds and runs a substantial axiom audit, but I found no invocation of
the shipped `leanchecker` in `scripts/ci`, `scripts/check-core-audit`, or
`tools/core-audit.py`. `Tests/GoCoreAudit.lean:565–580` collects axiom dependencies;
it does not re-check declarations in a fresh kernel environment. A textual
escape-hatch scan and a clean dependency list do not supply that missing check.

Reproduce the gate omission by reading those four paths, or searching the
implementation for the checker/replay entry points:

```bash
rg -n 'leanchecker|replayFromImports|replayFromFresh|debug\.skipKernelTC' \
  scripts/ci scripts/check-core-audit tools/core-audit.py Tests/GoCoreAudit.lean
```

At the reviewed commit there are no matches (rg exit 1). This is a **gate-coverage
finding**, not a failed kernel replay or evidence of tampering. My explicit
`capped lake env leanchecker --verbose GoLean`, run under the build lock, replayed
68 modules successfully, exit 0. The toolchain's `src/lean/LeanChecker.lean:55–68`
explains the environment-replay check and its limits. It is not an independent
implementation of Lean's kernel.

Recommendation: propose adding this existing tool at the project's trust claim
point and naming it in the charter, with the usual cap and lock. No new custom
proof-audit framework is needed. A reviewer having run it once does not make it
part of the standing release gate. I have not changed the charter or gate.

## F5 — MEDIUM: default “program” export silently omits `main`

```bash
mkdir -p "$review_scratch/only-main"
cat > "$review_scratch/only-main/main.go" <<'GO'
package main
func main() { println(42) }
GO
review_run only-main main
```

gc prints `42`, exit 0. The frontend exits 0, but its wire has `"funcs": []`.
`native-json-run --function main` returns `status:error`, `entry function not
found: main`, exit 1. This is a loud runtime refusal, **not** a wrong Go answer.
It is nevertheless a release usability/contract defect: `docs/cli.md:28` describes
the default input as a program, while the implementation always discards its entry
point (`tools/nativefrontend/emit.go:140–146`). `--subject` changes the missing-main
check, not this behavior.

Recommendation: explicitly document that this is a subject-function exporter and
that `main` is reserved/omitted, or provide a separately justified whole-program
entry mode. Requiring `main` for default admission while excluding it from the
output is surprising and currently undiscoverable from the public CLI instructions.
This need not block release if the owner deliberately chooses and clearly states
the subject-only interface.

## What held

- **Axiom audit:** `capped lake env python3 tools/core-audit.py` passed using the
  built oleans: 67 GoLean modules, 57 under `GoLean.GoCore`, 644 required theorems,
  22,168 declarations across imported local modules, classical trio only.
- **Headline axioms:** `#print axioms` for `Machine.stepFn_sound`,
  `Machine.step_complete`, `PoolSound.stepML_sound`, and `PoolSound.stepML_complete`
  reported exactly `propext`, `Classical.choice`, `Quot.sound`. Imports were
  `GoLean.GoCore.BridgeSet` and `GoLean.GoCore.EnumDedupSound`; the scratch file ran
  with `capped lake env lean`. The full audit above covers more than these four.
- **Kernel replay:** all 68 `GoLean`-prefix modules in the supplied build, including
  the root aggregator, replayed successfully. No non-standard axiom or trusted-code
  `sorry`, `native_decide`, `implemented_by`, `@[extern]`, `unsafe`, or
  `debug.skipKernelTC` use was found in the source search/audit performed here.
- **Wire refusals:** duplicate schema key, unknown schema, foreign `arm64` target,
  missing build context, and an unpaired surrogate each produced a cause-naming
  `status:error`, exit 1, through the real CLI.
- **Selected semantic controls:** defined-bool conversion and a named-struct
  pointer conversion with an aliased write agreed with gc. Lookup and delete on a
  nil `map[any]int` with an unhashable key correctly panicked/recovered. An
  anonymous nonempty tagged struct was quarantined; a float-width conversion
  exposing the model's default NaN bits refused by name. These are individual
  controls, not whole-feature certifications.

## Not established by this pass

I did not run `scripts/ci` or `scripts/ci --diff`, re-certify baselines, rebuild all
Lean targets, verify a fresh clone, or run the race corpus, raft harness or a
downstream logic build. I did not exhaustively assess concurrency, library
overlays, seeded heaps, budgets or all compiler directives. The known
variable-length allocation kill was read as an existing failure, not reproduced
by stressing this shared box. I make no new corpus-wide counts or coverage claim.

The supported-profile and behavioral-envelope release predicates still need an
explicit assessment at the actual release commit. A classified baseline can
remain green while newly probed programs are wrong; the examples here do not
become safe merely by being given bug numbers or stated as limits. A named
exclusion must be an honest consumer constraint, and the owner's requested
fail-closed boundary needs an effective refusal when that excluded shape is fed
to the ordinary pipeline.

After reproducing the snippets, remove their scratch with
`rm -rf -- "$review_scratch"`. My own probes, binaries, private Go cache, wires
and logs under `.tmp/codexpass/` and `.tmp/codex-zero-context-repro/` were removed
before the report commit. The supplied
`.tmp/nativefrontend` and prepared `.lake` were retained. This report is the only
committed artifact; there was no merge, tag, push or machine-global change.
