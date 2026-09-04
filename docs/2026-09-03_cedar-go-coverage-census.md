# cedar-go coverage census — does the semantics cover this target today?

Date: 2026-09-03 · Lane: cedar-census (worktree
`.claude/worktrees/cedar-census`, branch `cedar-census` off main
@ 6a163681 — the brief named main @ 2aad3545; main had advanced five
docs/gate commits by launch, and the census was run at the tip) ·
[AGENT]-executed to the coordinator's relay of the [USER] question
«(1) if our semantics covers this example today» — MEASURED, nothing
fixed. Lane tooling only: this document, `scripts/cedar-census`,
`tools/cedarcensus/`, the drivers and stand-in under
`Corpus/challenges/cedar-go/`, the tracked evidence under
`docs/census/cedar-go-2026-09-03/`, and two opt-in rows in
`scripts/setup-deps`. No gate, baseline, corpus (`Corpus/coverage`) or
`GoLean/` change. Nothing under `deps/` was modified (both checkouts
`git status` clean before and after).

Subjects: `deps/cedar-go` = github.com/cedar-policy/cedar-go @
`cda92d0d9345fce26b36366288afd3c909fc7bd8` (go 1.23.0; 167 `.go` files
of which 122 non-test in 24 package dirs); `deps/cedar-access-control-
for-k8s` = github.com/awslabs/cedar-access-control-for-k8s @
`660c6374dff9e6c47647f1c7a17f728d75296324` (go 1.24.2; 53 `.go` files,
41 non-test in 16 package dirs). Oracle `go1.26.5 linux/amd64` (=
`baselines/go-oracle-pin`). Machine: `golean` built in the worktree
from 6a163681 (`scripts/capped lake build golean`).

**Correction to the brief's premise [AGENT]:** cedar-go is NOT
stdlib-only. `go.mod` requires `golang.org/x/exp` (for
`constraints.Signed`/`constraints.Float` in `types/decimal.go:65,77`
and `types.go:143,155`); the module is not in the local module cache
and the census runs offline, so the census copy substitutes a six-
interface stand-in (`Corpus/challenges/cedar-go/standin/xexp/
constraints/constraints.go`), consumed identically by both pipelines.

## 0. Headline

**Today: no.** Not one of the nine functional drivers exports, and 18
of cedar-go's 22 library packages (17,024 of 18,139 non-test LOC, 94%)
refuse at the frontend before a single function is lowered — all on
ONE cause: two package-level initializers in `types/datetime.go:16,19`
(`var maxDatetime = time.Date(...)`, `var minDatetime = time.Date(...)`).
H-11's positive allowlist for unmodeled initializer callees is
`os.Getenv`/`os.LookupEnv` only (`tools/nativefrontend/emit.go`
`pureUnmodeledCallees`), so any other package-selector call in a
package-level initializer is a WHOLE-EXPORT refusal, and every package
that transitively imports `cedargo/types` (which is everything but four
leaf packages) dies with it. Only `internal`, `internal/consts`,
`internal/mapset`, `internal/rust` export (1,115 LOC; 6.1%).

Peeling that one kill point off (pass B, a labelled counterfactual on
the census COPY — §3.3) exposes the second, which is NOT relaxable
without changing the library's API: `types.Record.All`, `Set.All`,
`PolicyMap.All`, `PolicySet.All`, `Record.Keys/Values` return
`iter.Seq`/`iter.Seq2` — an imported generic instantiation the
frontend cannot even stub (`quarantinedMethodStub`'s `sigRefusal`
path: "its own SIGNATURE does not lower either"), again a whole-export
refusal. The Go 1.23 iterator idiom is load-bearing in cedar-go: the
authorizer's main loop is `for id, po := range policies.All()`
(`authorize.go:38`), i.e. FR-12 range-over-func.

Because the frontend's per-declaration picture is hidden behind those
two kills, the per-function census is STATIC (§3.4): of cedar-go's
1,085 function/method declarations, **892 (82.2%) demand nothing the
frontend refuses** (their bodies use only modeled Go plus the frozen
shim set); 193 (17.8%) demand at least one refused stdlib selector or
refused language shape. The evaluator proper is in good shape — 50 of
the 53 `Eval` methods and `ToEval`/`Compile`/`fold` lower statically
— and the refusals concentrate in `types` (51 of 133: JSON codecs,
`net/netip`, `time`, `hash/fnv`) and the validator (51 of 131:
`errors.Join`/`errors.As`, `slices.Contains`).

## 1. Method (exact commands)

Runner: `scripts/cedar-census run` (header has the contract). All
output under `artifacts/cedar/` (gitignored); the tracked copies are
`docs/census/cedar-go-2026-09-03/*.tsv`. Steps:

1. **assemble** — copy every non-test `.go` of cedar-go (test-support
   packages `internal/testutil`, `internal/testvalidate` excluded —
   they import `testing`) to `artifacts/cedar/src/cedargo/…` with the
   import path rewritten `github.com/cedar-policy/cedar-go` →
   `cedargo` (`load.go` refuses dotted local import paths: the TypeId
   grammar reserves `.`) and `golang.org/x/exp/constraints` →
   `xexp/constraints` (stand-in). The SAME copy feeds both pipelines:
   the frontend reads it as case-local packages; `go run` reads it
   through `GOPATH=<case>/gopath` whose `src/cedargo` is a symlink to
   the same tree (`scripts/diff-coverage`'s multi-package convention).
   The rewrite is therefore symmetric and cannot skew the differential.
   Likewise `cedark8s/` for the k8s subset (§6).
2. **inventory** — `tools/cedarcensus inventory <root> <modpath>`
   (go/parser): per package dir, files, LOC, funcs, methods, imports
   split stdlib / module-internal / external.
3. **cases** — one case dir per (a) library package: a synthesized
   blank-import driver (export census only); (a') the whole library;
   (a'') each k8s cedar-go-only package; (b) each tracked functional
   driver `Corpus/challenges/cedar-go/drivers/<name>/main.go` — nine
   self-checking programs (silent on success, `panic` on any wrong
   value; entry `censusMain`, thin `main`), the gotest-triage shape.
4. **drive** — per case: `GO111MODULE=off go run ./tools/nativefrontend
   --dir <case> --out wire.json` → on success `tools/cedarcensus wire`
   (per-declaration lowered/quarantined rows from the `unsupported`
   keys) → for functional drivers `go run .` (GOPATH mode,
   `GODEBUG=panicnil=0`) and `golean native-json-run --input wire.json
   --function censusMain` → `golean observation-eq`. Categories are
   gotest-triage's: FRONTEND-REFUSED / MACHINE-REFUSED / MATCH /
   MISMATCH / INFRA, plus EXPORT-OK for package drivers.
5. **demand** — `tools/cedarcensus demand <src> <pkgs…>`: go/types
   type-check of the assembled copy (stdlib via `importer.Default`,
   the same checker the frontend uses); per function/method, every
   non-local `pkg.Fn` call, imported-type method call, imported generic
   instantiation in signature or body, range-over-func, anonymous
   non-empty struct, `go`, `goto`, complex literal, builtin
   `print/println`; judged against the supply table (`demand.go`
   `supplied`: the D-002 frozen shims + shadow types + machine-owned
   `sync`/`slices.Sort`; source: `docs/2026-09-03_stdlib-boundary-
   design.md` §1.2). STATIC: it does not run the frontend, so it cannot
   see verb-matrix misses inside an admitted `fmt.Sprintf` or shim
   run-time bounds; it is an over-approximation of "would lower" in
   that one direction and is labelled `lowers(static)` throughout.
6. **report** — `census.tsv`, `results.tsv`, `histogram.tsv`,
   `per-package.tsv`, `demand*.tsv`, `meta.tsv`.

Pass B: `CEDAR_CENSUS_RELAX=1 CEDAR_CENSUS_ARTIFACTS=artifacts/cedar-
relaxed scripts/cedar-census run` — applies the tracked sed script
`Corpus/challenges/cedar-go/relax/types-datetime.sed` to the census
COPY of `types/datetime.go` (the two `var … = time.Date(…)` become
nullary functions, the one use at `:226` becomes two calls;
semantically identical under `go run`, symmetric). Fail-closed if the
patch changes nothing. Pass B numbers are counterfactual and are
labelled so wherever they appear.

Go-side check of the drivers: all nine exit 0 silently under `go run`
on the real library (`artifacts/cedar/cases/drv-*/`, re-run by hand
after the drive because the drive short-circuits at the frontend
refusal) — the drivers' assertions hold on the oracle, so a machine
run, when one becomes possible, would be a full-strength differential.

## 2. Package inventory (cedar-go, non-test)

Source: `docs/census/cedar-go-2026-09-03/cedar-go-inventory.tsv`.
`funcs`/`methods` are declaration counts; `frontend` is pass A;
`static` is the demand census (`lowers(static)`/total).

| dir | pkg | files | LOC | funcs | methods | stdlib imports | frontend (pass A) | static lowers |
|---|---|---|---|---|---|---|---|---|
| `.` | cedar | 6 | 586 | 20 | 23 | bytes, encoding/json, fmt, io, iter, maps, slices, time | REFUSED (time.Date via types) | 34/43 |
| `ast` | ast | 7 | 605 | 29 | 64 | bytes, net/netip, time | REFUSED (via types) | 92/93 |
| `internal` | internal | 1 | 14 | 0 | 0 | fmt | EXPORT-OK | – |
| `internal/consts` | consts | 1 | 19 | 1 | 0 | – | EXPORT-OK (1/1 lowered) | 1/1 |
| `internal/eval` | eval | 7 | 2725 | 118 | 53 | errors, fmt, slices | REFUSED (via types) | 159/171 |
| `internal/extensions` | extensions | 1 | 41 | 1 | 0 | – | REFUSED (via types) | 1/1 |
| `internal/json` | json | 4 | 816 | 12 | 21 | bytes, encoding/json, fmt, strings | REFUSED (via types) | 28/33 |
| `internal/mapset` | mapset | 2 | 235 | 3 | 20 | bytes, encoding/json, fmt, iter, maps, slices | EXPORT-OK (generic-only: 0 instantiated decls on the wire) | 17/23 |
| `internal/parser` | parser | 6 | 2259 | 20 | 105 | bytes, fmt, io, slices, strconv, strings, unicode/utf8 | REFUSED (via types) | 101/125 |
| `internal/rust` | rust | 2 | 847 | 15 | 0 | fmt, strings, unicode, unicode/utf8 | EXPORT-OK: 10/15 lowered, 5 quarantined | 10/15 |
| `internal/testutil` | testutil | 1 | 168 | 13 | 0 | reflect, testing-support | excluded (test support) | – |
| `internal/testvalidate` | testvalidate | 1 | 177 | 4 | 0 | testing | excluded (test support) | – |
| `types` | types | 18 | 2238 | 23 | 110 | bytes, cmp, encoding/binary, encoding/json, errors, fmt, hash/fnv, iter, maps, math, net/netip, slices, strconv, strings, time, unicode | REFUSED (time.Date — THE kill point) | 82/133 |
| `x/exp/ast` | ast | 9 | 953 | 36 | 127 | net/netip, time | REFUSED (via types) | 163/163 |
| `x/exp/batch` | batch | 1 | 402 | 12 | 0 | context, errors, fmt, maps, slices | REFUSED (via types) | 8/12 |
| `x/exp/dot` | dot | 1 | 76 | 3 | 0 | fmt, io, iter, strconv | REFUSED (via types) | 0/3 |
| `x/exp/eval` | eval | 1 | 82 | 8 | 0 | – | REFUSED (via types) | 8/8 |
| `x/exp/schema` | schema | 1 | 73 | 1 | 8 | – | REFUSED (via types) | 9/9 |
| `x/exp/schema/ast` | ast | 2 | 198 | 12 | 8 | – | REFUSED (via types) | 20/20 |
| `x/exp/schema/internal/json` | json | 1 | 454 | 9 | 2 | encoding/json, fmt, sort | REFUSED (via types) | 8/11 |
| `x/exp/schema/internal/parser` | parser | 3 | 1468 | 10 | 43 | bytes, fmt, maps, slices, strings, unicode/utf8 | REFUSED (via types) | 43/53 |
| `x/exp/schema/resolved` | resolved | 2 | 695 | 9 | 19 | fmt, strings | REFUSED (via types) | 22/28 |
| `x/exp/schema/validate` | validate | 10 | 3143 | 48 | 83 | cmp, errors, fmt, maps, slices, strings | REFUSED (via types) | 80/131 |
| `x/exp/types` | exptypes | 1 | 210 | 7 | 2 | encoding/json | REFUSED (via types) | 6/9 |

Totals (22 library packages): 18,139 LOC; 1,085 function/method
declarations. Absent from cedar-go entirely (grep, non-test): `unsafe`,
`reflect` (test-support only), `regexp`, `sync`, `sync/atomic`, `go`
statements, `select`, `math/big`. The library is single-threaded pure
Go over the stdlib; its `like` operator is a hand-written glob matcher
(`types/pattern.go:86-136`, lowers statically), NOT `regexp`.

## 3. Results

### 3.1 Per case (pass A — today), `results.tsv`

| category | cases | which |
|---|---|---|
| FRONTEND-REFUSED | 29 | 18 cedar-go packages, the whole-library case, 9 functional drivers, `cedark8s/internal/schema` — ALL at `package-selector call time.Date (package "time" surface not modeled)` |
| EXPORT-OK | 5 | `internal` (0 decls of its own), `internal/consts` (1/1), `internal/mapset` (generic-only, 0 instantiated), `internal/rust` (10/15 lowered), `cedark8s/cmd/schema-formatter` (1/2; `flag.Parse` quarantined) |
| MATCH / MISMATCH / MACHINE-REFUSED | 0 / 0 / 0 | no driver reached the machine |

The frontend's per-declaration census of the four exporting packages
(`census.tsv`, `histogram.tsv`; injected `goleanShim*` helpers and
stdlib shadow-type stubs filtered out): 11 library declarations
lowered, 5 quarantined — `rust.isGraphemeExtended` (`unicode.Is`),
`rust.nextRune` (`utf8.DecodeRune`), `rust.parseUnicodeEscape`
(`utf8.ValidRune`), `rust.unquote` (`strings.TrimPrefix` outside the
modeled subset), `rust.escapeRune` (`fmt.Sprintf` verb `%x` over `rune`
outside the verb×kind matrix). All five are stdlib-boundary causes.

### 3.2 The kill point, precisely

`deps/cedar-go/types/datetime.go`:
```
16: var maxDatetime = time.Date(292278994, 8, 17, 7, 12, 55, 807*1e6, time.UTC)
19: var minDatetime = time.Date(-292275055, 5, 17, 16, 47, 04, 192*1e6, time.UTC)
226:	if t.Before(minDatetime) || t.After(maxDatetime) {
```
Mechanism: `quarantineUnlowerableGlobals` (emit.go, H-11) dry-runs
each package-level initializer; on an `unsupported` it consults
`initializerEffectIsolated`, whose callee allowlist is
`pureUnmodeledCallees = {os.Getenv, os.LookupEnv}`; anything else →
`return err` = whole-export refusal ("the sound direction", audit F1
2026-08-20). The 18 dependent packages inherit the refusal through
`cedargo/types`. This is the first real-code exhibit of the H-11
allowlist's cost: a pure, deterministic constant initializer in a
leaf package taking down a 18k-LOC library. Rowed as **FR-22** (ledger §4,
queue 22; follow-up under [USER] direction 3) — the fix plan is
per-declaration poisoning of the initialized var rather than a
whole-export refusal; `time.Date` itself stays a stdlib-boundary
question for the design memo (specified primitive or source-through).
Not fixed here.

### 3.3 Pass B (counterfactual: the datetime initializers relaxed)

`results-passB-relaxed.tsv`: identical shape — 29 FRONTEND-REFUSED /
5 EXPORT-OK — but the cause moves to the SECOND kill point:

```
method cedargo/types.Record.All is unsupported (instantiation of imported
generic type iter.Seq2[cedargo/types.String,cedargo/types.Value]) and its
own SIGNATURE does not lower either …: no signature-carrying stub exists,
so the export refuses rather than record an incomplete method set
```

Ten signatures carry `iter.Seq`/`iter.Seq2` (`Record.All/Keys/Values`,
`Set.All`, `EntityMap`-adjacent, `PolicyMap.All`, `PolicySet.All`,
`PolicyIterator.All`, `mapset.MapSet.All`, `dot`): they are the
library's public iteration API, so no census-side relaxation is
honest. Per-function frontend census beyond this point is therefore
unavailable; §3.4 is the static substitute. Rowed as **FR-23** (ledger
§4, queue 23, beside FR-12; follow-up under [USER] direction 3).

### 3.4 Static demand census (`demand.tsv`, 1,085 cedar-go decls)

Verdict: **892 lowers(static) / 193 refused(static)**. Per package in
the §2 table (`demand-per-package.tsv`). Histogram of refused keys
(`demand-histogram.tsv`; "functions" = declarations whose body/signature
demands the key; "sole" = the key is that declaration's ONLY refusal,
i.e. the direct unblock count):

| key | functions | sole | pkgs | class |
|---|---|---|---|---|
| `errors.Join` | 29 | 24 | 4 | stdlib (S1 family; `unsafe.String` idiom in the real impl) |
| `FR-12:range-over-func` | 21 | 0 | 8 | language FR-12 |
| `bytes.Buffer.WriteRune` | 19 | 15 | 2 | stdlib shadow-type gap (Buffer model lacks WriteRune) |
| `encoding/json.Marshal` | 18 | 10 | 6 | reflect frontier (G6) |
| `imported-generic-inst:iter.Seq` (body) | 18 | 0 | 8 | language (iterator API) |
| `slices.Contains` | 15 | 13 | 4 | stdlib pure generic |
| `encoding/json.Unmarshal` | 14 | 11 | 6 | reflect frontier (G6) |
| `bytes.Buffer.Bytes` | 12 | 5 | 5 | shadow-type gap |
| `maps.Keys` | 10 | 0 | 3 | stdlib pure generic (returns iter.Seq) |
| `slices.Collect` | 8 | 0 | 2 | stdlib pure generic (consumes iter.Seq) |
| `sig:imported-generic-inst:iter.Seq` | 7 | 4 | 3 | language — the unstubbable-signature kill |
| `errors.Is` | 6 | 4 | 2 | reflectlite (G6) |
| `maps.Clone` | 6 | 4 | 4 | stdlib pure generic |
| `imported-generic-inst:iter.Seq2` (body) | 5 | 0 | 3 | language |
| `strings.Compare` | 5 | 3 | 2 | stdlib S1 |
| `hash/fnv.New64` + `hash.Hash64.Write/Sum64` | 4 | 0 | 1 | stdlib pure (`types.{String,EntityUID,IPAddr}.hash`, `NewRecord`) |
| `net/netip.Prefix.Bits` (+15 other netip members, 10 fns) | 4 | 0 | 1 | stdlib netip (ipaddr extension) |
| `slices.Sorted` | 4 | 0 | 1 | stdlib pure generic |
| `strings.Builder.WriteRune`, `utf8.DecodeRune` | 4 / 4 | 3 / 3 | 3 / 3 | shadow-type gap / stdlib pure |
| `time.*` (14 members, 6 fns) | 2 each | – | 1 | stdlib time (datetime extension) |

Language-shape refusals: FR-12 range-over-func 21 (every set/entity
iteration in `internal/eval`: `containsAllEval/containsAnyEval.Eval`,
`entityInOne`, `entityInSet`, `doInEval`; `Authorize`; `NewSet`);
`iter.Seq/Seq2` instantiation 33 incidences; FR-13 anonymous struct 3
fns (`Entity.MarshalJSON`, `ImplicitlyMarshaledEntityUID.MarshalJSON`,
`Validator.typecheckConditions`); one `goto` (`parser/scanner.
nextToken` — shape not checked against FR-11/FR-20). No `go`, no
complex, no `print/println`, no `unsafe`, no `reflect`.

**Tooling note (2026-09-04, [AGENT], lane `lower-diagnose`; audit fix
round applied):** the static demand census is now produced by
`tools/lowerdiag` (the engine of `scripts/lower-diagnose`, [USER]
direction 4 — ledger §0) instead of the retired `tools/cedarcensus
demand`; `scripts/cedar-census demand` writes the same three files
(`demand.tsv`, `demand-histogram.tsv`, `demand-per-package.tsv`, now with
a leading `# DIAGNOSTIC — NOT A LOWERING` line) plus `demand-report.txt`,
and censuses the `cedark8s` packages as extra roots (`--include`), so
§6's `cedark8s/internal/schema` 36/38 is REPRODUCED. Re-run at the lane
(evidence `docs/evidence/2026-09-04_lower-diagnose/cedar-go/`): cedargo
**974/1085 funcs+methods lower statically** vs the 892/1085 above —
IDENTICAL denominator package by package; per declaration, 85
census-refused → now lower (register rows landed since 2026-09-03:
`errors.Join` 24, `bytes.Buffer.WriteRune` 15, `slices.Contains` 13,
`bytes.Buffer.Bytes` 4, `strings.Compare/Contains/TrimPrefix/…`,
`utf8.DecodeRune`, `strconv.ParseInt/Quote*`) and 3 census-lowers → now
refused, all REAL refusals the old tool did not check: `internal/parser.
Decoder.decode` reads `io.EOF` (a var of an unmodeled package);
`x/exp/schema/internal/parser.init` calls `slices.Sort` on `[]string`
(the sortSlice op's integer bound — and an `init()` body is a WHOLE-EXPORT
kill: this is the pass-C counterfactual's "a slices.Sort init()", found
statically); `cedark8s/internal/schema.CedarSchema.SortActionEntities`,
the same `slices.Sort@string`. Rule-level diff between the two tools:
the old `go-statement` flag (every `go` statement counted as a refusal —
dropped, `go` lowers), the old SYNTACTIC anonymous-struct rule (any
`struct{…}` AST node, including the declared type's own struct — replaced
by the typed rule over every expression/signature type), the old
unconditional `goto` flag (replaced by FR-20 certain vs FR-11
may-refuse), the old frozen shim-era supply map (replaced by the register
read at run time + `library-refusals.tsv` + the machine-surface table);
rules the old tool lacked: var reads of unmodeled packages, `init()`
export scope, initializer effect-isolation scope, `slices.Sort` element
kind, intercepted defer/go, FR-7 assign/value-spec boxing, FR-17/18/19
shapes, library members refused by name (`errors.Is/As`). The numbers in
§3.4 stand as the 2026-09-03 measurement.

### 3.5 Top 10 blockers, ranked by what they unblock

Ranking = declarations touching the blocker, tie-broken by sole-blocker
count; packages = distinct packages touched.

1. **`time.Date` in package-level initializers** — unblocks the EXPORT
   of 18 packages / 17,024 LOC (everything); a single frontend
   predicate.
2. **`iter.Seq/Seq2` in signatures + FR-12 range-over-func** — 54
   incidences over 29 declarations in 8 packages, including
   `Authorize` itself; unstubbable signatures are a whole-export kill.
3. **`errors.Join`** — 29 decls (24 sole), validator + eval + types.
4. **`bytes.Buffer.WriteRune` / `.Bytes`** — 31 decls (20 sole), the
   Cedar-text printers (`MarshalCedar` everywhere).
5. **`encoding/json.Marshal/Unmarshal` (+Decoder)** — 38 decls (21
   sole) in 6 packages — every JSON codec.
6. **`slices.Contains`** — 15 decls (13 sole), validator.
7. **`maps.Keys/Values/Clone`, `slices.Collect/Sorted/Clone`** — 34
   incidences; canonical-ordering helpers in `types` and `mapset`.
8. **`net/netip.*`** — 10 decls in `types` (the `ipaddr` extension
   entirely: `ParseIPAddr`, `IsLoopback`, `Contains`, `hash`, …).
9. **`errors.Is/As`** — 9 decls (5 sole): partial evaluation
   (`PartialPolicy`, `tryPartial`, `partialAnd/Or/IfThenElse`) and
   `Validator.Policy/Entities`.
10. **`hash/fnv`** — 4 decls, but transitively load-bearing: every
    `types.Set`/`Record` construction hashes through it (`NewSet` →
    `Value.hash` → `fnv.New64`), so set semantics in the evaluator
    depend on it.

## 4. Delta estimate against the in-flight stdlib slices [AGENT]

Bucket rule in the command below (`demand.tsv` → key → slice): S1 =
`strings.*`, `strconv.*`, `errors.{New,Join,Unwrap}`; S2 overlay = pure
packages `unicode/utf8`, `unicode`, `bytes` (incl. the Buffer methods
the shadow type lacks), `slices`, `maps`, `cmp`, `math`, `sort`,
`hash/fnv`+`hash`, `encoding/binary`; S3 = builtin print; S4 = `fmt.*`;
G6 = `encoding/json.*`, `errors.Is/As`, `reflect`. Assumption flagged:
slice 2's exact package list was relayed as "overlay" without a
manifest; the bucket above is this census's reading of "pure packages
with `*_generic.go` bodies" and must be checked against the slice's
own scope when it lands.

Cumulative, over the 193 statically refused cedar-go declarations (plus
2 in `cedark8s/internal/schema`, 195 total):

| after slice | still refused | unblocked so far |
|---|---|---|
| S1 strings/strconv/errors source-through | 152 | 43 |
| + S2 overlay (utf8/unicode/bytes/slices/maps/cmp/math/fnv/binary) | 89 | 106 |
| + S3 print/println | 89 | 106 (cedar-go never prints) |
| + S4 fmt on strconv | 89 | 106 (one `fmt.Fprintln` in `dot`) |
| + G6 reflect gate (encoding/json, errors.Is/As) | 51 | 144 |

Caveats on the S1 count: `errors.Join`'s real body has the
`unsafe.String(&b[0], len(b))` idiom (memo §1.3) — it lands under S1
only with the portable `string(b)` stand-in the memo proposes; and
`errors.Is/As` are NOT S1 (reflectlite → G6), which is why partial
evaluation stays refused until G6.

**What remains after all five (51 declarations, 111 incidences):**
`iter`/FR-12 (54 — language: range-over-func + imported generic
instantiation; `Authorize`, the set operators, `NewSet`, every `All()`),
`net/netip` (26 — the `ipaddr` extension), `time` (21 — the `datetime`
extension: `ParseDatetime`, `Datetime.String`, `checkValidDay`, and the
two kill-point initializers), FR-13 anonymous struct (5), `context`/`io`
(4, `x/exp/batch` and `dot`), `goto` (1). By package: `types` 23,
`validate` 7, `internal/eval` 5, `batch` 4, root 3, parser 3, mapset 2,
dot 2, resolved 1, x/exp/types 1. None of `regexp`, `math/big` appear
(the brief's guess); `net/netip` and `time` do, and both are real
implementation surfaces (netip's `Addr` is a 128-bit + zone value with
its own parser; `time.Date` is the proleptic-Gregorian normalizer),
not thin shims — a specified-primitives question for the design memo.

The single most valuable NON-stdlib item for this target is FR-12 with
its `iter.Seq` signature companion: without it the authorizer's loop
and the evaluator's set operators cannot lower even after every stdlib
slice, and the unstubbable-signature arm turns every `All()` method
into a whole-export kill.

**Rowed under [USER] direction 3 (follow-up, coordinator relay,
2026-09-03):** the two whole-export kill points are now frontier rows
in `docs/language-coverage-ledger.md` §4 with fix plans and §5 queue
slots — **FR-22** (stdlib call in a package-level initializer outside
H-11's allowlist → per-declaration var poisoning instead of whole-
export; queue 22, after FR-18; witness `Corpus/coverage/exec/init/
stdlib-initializer-call`) and **FR-23** (imported generic instantiation
in a SIGNATURE unstubbable → D5-style per-declaration stub; queue 23,
beside FR-12; witness `Corpus/coverage/exec/generics/imported-generic-
in-signature`), both born-FAIL rows re-pinned into
`baselines/native-full.tsv` (ledger §8h — lettered §8g on the lane, re-lettered at the round-9 replay). FR-12's row carries this
census as priority evidence. Once FR-22 and FR-23 land, pass B becomes
unnecessary and the per-function FRONTEND census (§3.4's static
substitute) can be measured directly.

## 5. Refinement entry points (for the reasoning question)

What a refinement proof against cedar-spec (§7) would target in
cedar-go, with LOC (`tools/cedarcensus decls`) and TODAY's status.
"static" = the demand verdict; "frontend" = pass A, which is REFUSED
for all of them because they live in packages behind the §3.2 kill.

| Lean spec function | cedar-go realization | file:line | LOC | static verdict | direct refusals |
|---|---|---|---|---|---|
| `isAuthorized` (Spec/Authorizer.lean:56-63) | `Authorize(policies PolicyIterator, entities EntityGetter, req Request) (Decision, Diagnostic)` | `authorize.go:18` | 45 | refused | FR-12 range over `policies.All()` (iter.Seq2) |
| — wrapper | `(*PolicySet).IsAuthorized` | `policy_set.go:143` | 3 | lowers | – |
| `evaluate` (Spec/Evaluator.lean:98) — compile step | `Compile(*ast.Policy) BoolEvaler`, `PolicyToNode`, `ToEval(ast.IsNode) Evaler` | `internal/eval/compile.go:24,30`, `convert.go:11` | 5 / 31 / 85 | lowers | – |
| `evaluate` — the operator semantics | 53 `(*xEval).Eval(Env) (types.Value, error)` methods | `internal/eval/evalers.go` (1,549 LOC) | 1,549 | 50/53 lower | `containsAll/containsAny.Eval` (FR-12), `comparableValueGreaterThanOrEqualEval.Eval` (`errors.Join`); helpers `entityInOne/entityInSet/doInEval` (FR-12) |
| — constant folding (spec has none; optimizer) | `fold`, `foldPolicy`, `tryFold` | `internal/eval/fold.go:86,22,38` | 192 / 14 / 27 | `fold` lowers; `foldPolicy` refused (`slices.Clone`) | |
| TPE / partial evaluation (Thm/TPE.lean) | `PartialPolicy`, `partial`, `tryPartial`, `partialAnd/Or/IfThenElse` | `internal/eval/partial.go:48,214,160,…` | 41 / 178 / 39 / 25-27 | `partial` lowers; `PartialPolicy`, `tryPartial`, `partialAnd/Or/IfThenElse` refused (`errors.Is`, `slices.Clone`) | |
| batched authorization (Thm/BatchedEvaluator.lean) | `batch.Authorize(ctx, policies, entities, Request, Callback) error` | `x/exp/batch/batch.go:114` | 64 | refused | `context.Context.Err`, `errors.Join`, FR-12, iter.Seq/Seq2 |
| `validate` (Thm/Validation.lean:51) | `Validator.Policy(policyID string, *ast.Policy) error`; `typecheckConditions`; `Validator.Request`; `Validator.Entities` | `x/exp/schema/validate/policy.go:31,362`, `request.go:12`, `entity.go:37` | 63 / 101 / 30 / 12 | refused | `errors.As`, `errors.Join` (policy), FR-13 anon struct (typecheckConditions), `slices.Contains` (request) |
| — typechecker core | `typechecker.go` (the `typecheck*` family) | `x/exp/schema/validate/typechecker.go` | 131 decls in pkg: 80 lower / 51 refused | | mostly `errors.Join`/`errors.As`/`slices.Contains` |
| JSON policy codec (CedarProto analogue) | `(*Policy).MarshalJSON/UnmarshalJSON` → `internal/json.Policy.MarshalJSON/UnmarshalJSON` | `policy.go:26,34`; `internal/json/json_marshal.go:305`, `json_unmarshal.go:293` | 4 / 9 ; 26 / 46 | wrappers lower; codecs refused | `encoding/json.Marshal/Unmarshal` |
| JSON entity codec | `EntityMap.MarshalJSON/UnmarshalJSON`, `Entity.MarshalJSON`, `Record.MarshalJSON/UnmarshalJSON`, `Set.*JSON`, `EntityUID.*JSON` | `types/entity_map.go:22,30`, `entities.go`, `record.go:129,149`, `set.go` | 7 / 12 / 17 / 22 | refused | `encoding/json.*`, `maps.Keys`, `slices.Collect`, FR-13 |
| Cedar text codec | `(*Policy).UnmarshalCedar` → `internal/parser`; `MarshalCedar` | `policy.go:59,47` | 8 / 8 | Unmarshal lowers (parser 101/125 static); Marshal refused (`bytes.Buffer.Bytes`) | |
| extension `decimal` | `ParseDecimal`, `NewDecimal`, `Decimal.Compare`, `Decimal.String` | `types/decimal.go:98,42,93,143` | 35 / 20 / 3 / 20 | Compare, String lower; Parse/New refused | `strconv.ParseInt`, `strings.Index`, `math.Pow10`, `errors.Is` |
| extension `ipaddr` | `ParseIPAddr`, `IPAddr.{IsIPv4,IsIPv6,IsLoopback,IsMulticast,Contains,String,hash}` | `types/ipaddr.go:20,56-123` | 14 / 23 / 3 / … | ALL refused | `net/netip.*` (16 distinct members), `hash/fnv` |
| extension `datetime` / `duration` | `ParseDatetime`, `Datetime.String`, `NewDatetime`, `ParseDuration`, `Duration.String`, `Duration.To*` | `types/datetime.go:95,270,32`, `duration.go:54,173,249-273` | 137 / 20 / 6 / 86 / 47 / 6 each | `Duration.String`/`To*` lower; the rest refused | `time.*` (14 members), `unicode.IsDigit`, `strconv.QuoteRune` |
| `like` | `Pattern.Match`, `matchChunk` | `types/pattern.go:86,124` | 34 / 14 | lowers | – (hand-written glob; no regexp) |
| Set / Record construction (canonical-form question, §7) | `NewSet`, `Set.Contains`, `NewRecord`, `Record.Get` | `types/set.go:18,83`, `record.go` | 32 / 13 / … | `NewSet` refused (FR-12 over `maps.Values`), `NewRecord` refused (`hash/fnv`, `encoding/binary.Write`, `maps.Keys`, `slices.Collect`); `Set.Contains` lowers | |

Reading: the semantic heart (compile + 50/53 operator evaluations +
`Pattern.Match` + `Decimal` comparison/printing + `Duration` printing)
lowers statically; everything that touches iteration order,
hashing, JSON, netip, or time does not; and `Authorize` itself is
blocked by the iterator idiom. TODAY none of it lowers in fact,
because of §3.2.

## 6. cedar-access-control-for-k8s (53 files; 41 non-test)

Module path in `go.mod` is `github.com/awslabs/cedar-access-control-
for-k8s` (the checkout's origin); the cedar-policy README of the Rust
project names `github.com/cedar-policy/cedar-access-control-for-k8s`
— the survey (§7) flags the org question; this checkout's own module
path is authoritative for what was measured. Classification by NON-TEST
imports (`k8s-classes.tsv`, `k8s-inventory.tsv`):

| package | files | LOC | class | pulls |
|---|---|---|---|---|
| `internal/schema` | 6 | 812 | **cedar-go + stdlib** | `cedar-go/types`, encoding/json, slices, strings |
| `cmd/schema-formatter` | 1 | 73 | stdlib only (a `main`) | bytes, flag, fmt, os, strings |
| `api/v1alpha1` | 4 | 546 | k8s | apimachinery, controller-runtime |
| `internal/convert` | 2 | 572 | k8s | cedar-go + k8s.io/api/rbac, klog |
| `internal/schema/convert` | 3 | 683 | k8s | apimachinery, client-go, kube-openapi, regexp |
| `internal/server` | 5 | 482 | k8s | apiserver authorizer, component-base, uuid, x/time |
| `internal/server/admission` | 2 | 186 | k8s | cedar-go + k8s.io/api/admission, controller-runtime |
| `internal/server/authorizer` | 2 | 267 | k8s | cedar-go + apiserver authorizer, klog |
| `internal/server/entities` | 4 | 518 | k8s | cedar-go/types + apiserver/apimachinery (the SAR→entity mapping) |
| `internal/server/store` | 6 | 565 | k8s + aws-sdk | cedar-go + controller-runtime cache, aws verifiedpermissions |
| `internal/server/{config,metrics,options}`, `cmd/{cedar-webhook,converter,schema-generator}` | 1+1+1+1+1+1 | 30+86+197+140+196+155 | k8s | apiserver, component-base, prometheus, cobra, client-go |

So the cedar-go-only subset is ONE library package, `internal/schema`
(the Cedar schema for k8s: entity types, action lists, attribute
JSON) — the request→entity mapping (`internal/server/entities`) and the
policy store are k8s-bound and were not lowered. Census of the subset:
`cedark8s/internal/schema` FRONTEND-REFUSED in pass A (via
`cedargo/types` — the same `time.Date` kill) and in pass B (the
`iter.Seq2` kill); static: 36/38 declarations lower,
`GetAuthorizationActions` (`slices.Contains`) and
`EntityAttribute.MarshalJSON` (`encoding/json.Marshal`) refused. The
`schema-formatter` main exports today (1 of 2 declarations; `main`
quarantined at `flag.Parse`). No functional driver was written for the
subset: `internal/schema` has no entry point that computes anything
(it is data + JSON marshalling), so a driver would only re-measure the
JSON codec class already counted.

## 7. Verification-target survey [AGENT, 2026-09-03] — relayed findings and the cedar-go cross-check

Recorded from the coordinator's relay of the parallel survey agent
(all [AGENT]; paths under `deps/` as given; not re-derived here except
where "cross-check" says so).

1. **`deps/kubernetes-cedar-authorizer` is Rust-only** (8,174 LOC:
   `src/schema` 2,282, `src/cedar_authorizer` 3,191, `kube_invariants`
   1,137+142, `k8s_authorizer` 1,063, `main.rs` 270 — an axum webhook,
   `POST /authorize` on SubjectAccessReview). `kube_invariants` =
   runtime-checked preconditions + AST/schema rewrites
   (`policyset.rs:18-25`: deny policies must never error; `is
   k8s::Resource` disallowed; static policies only;
   `residual.rs:20-50` `DetailedDecision{Deny,Conditional,Allow,
   NoOpinion}` with the soundness argument only in comments;
   `schema.rs:20-44` `STATIC_RESOURCE_ATTRIBUTE_REWRITES` →
   `meta::UnknownString`); 21 tests.
2. **Go analogues**: `github.com/cedar-policy/cedar-access-control-for-
   k8s` (README.md:196-220; the Rust project is to be donated into it).
   The checkout here is `github.com/awslabs/cedar-access-control-for-
   k8s` @ 660c637 — cross-check: its `go.mod` module path IS the awslabs
   path (§6), so "which org is canonical" is a README-vs-module
   discrepancy upstream, recorded, not resolved. cedar-go is never
   mentioned in either checkout (the Go project imports it, §6). Rust
   `Attributes` doc comments are copied from Go's
   `k8s.io/apiserver/pkg/authorization/authorizer.Attributes`.
3. **cedar-spec theorem inventory**: `Thm/Authorization.lean`
   `forbid_trumps_permit`:64, `default_deny`:92,
   `allowed_iff_explicitly_permitted_and_not_denied`:109,
   `order_and_dup_independent`:153 (full Response equality),
   `unchanged_allow_when_add_permit`:166 /
   `unchanged_deny_when_add_forbid`:179; `Authorization/Authorizer.
   lean:96` `is_authorized_congr_evaluate` (the authorizer is a
   congruence of `evaluate`); `Validation.lean:51`
   `validation_is_sound` (AllEvaluateToBool; residual errors
   entityDoesNotExist/extensionError/arithBoundsError); `TPE.lean:51`
   `reauthorize_is_sound`, `:79` `partial_authorize_decision_is_sound`,
   `:123/:148/:215` companions; `SymbolicCompilation.lean:71/:99/
   :155/:183` sound+complete; `PolicySlice.lean:139`;
   `BatchedEvaluator.lean:66`. Algorithm properties (transfer by
   refinement): 1-5 + the four "optimized ≡ reference" families;
   spec-internal: `Thm/Data/**`, `WellTyped/**`, `Typechecker/**`, and
   the `WellFormedFor` / `InstanceOfWellFormedEnvironment` hypotheses a
   Go implementation must reproduce.
4. **Refinement interface**: `Cedar.Spec.Request {principal, action,
   resource : EntityUID; context : Map Attr Value}` (`Spec/Request.
   lean:30-34`), `Entities := Map EntityUID EntityData` (`Spec/Entities.
   lean:38`), `Policies := List Policy` (`Spec/Policy.lean:77`),
   `Response {decision; determiningPolicies, erroringPolicies : Set
   PolicyID}` (`Spec/Response.lean:32-40`), `isAuthorized` 8 lines
   (`Spec/Authorizer.lean:56-63`), `evaluate` (`Spec/Evaluator.lean:
   98`); canonical sorted Set/Map (`Thm/Data/List/Canonical.lean`) is
   where a Go map-based implementation needs real work. DRT harness:
   protobuf-in / JSON-out over a C ABI — Lean exports in
   `DiffTest/Main.lean:62-155` (`isAuthorizedDRT`, `validateDRT`,
   `evaluateDRT`, …), `CedarFFI/Main.lean`, `CedarProto/*.lean`
   decoders; Rust caller `cedar-lean-ffi/src/lean_ffi.rs:1024-1275`;
   drivers `cedar-drt/src/tests.rs:38,75`; generators in
   `cedar-policy-generators/` — a Go implementation could be driven by
   the same harness by consuming the proto messages and emitting the
   same JSON Response.
5. **k8s-layer properties implied but unproved**: SAR→entity mapping
   is Result-typed and degrades to NoOpinion on error
   (`k8s_authorizer/authorizer.rs:85-100`) — fail-closed-to-no-opinion
   is the prime property; "100% RBAC compatibility" (README ~104-112)
   aspirational; deny-by-default through TPE =
   `partial_authorize_decision_is_sound` + the unproved Rust fold rules
   in `residual.rs:40-100`; the never-error invariant on forbid
   policies is a syntactic over-approximation of AllEvaluateToBool;
   the Cedar-residual→CEL translation (`cel.rs`, 414 LOC) has no
   theorem counterpart. Thesis PDF not in checkout (README.md:216-218
   links).

**Cross-check against what this census MEASURED in cedar-go [AGENT]:**

- *Which functions realize `evaluate` / `isAuthorized`*: `isAuthorized`
  ≡ `authorize.go:18 Authorize` (45 LOC; `PolicySet.IsAuthorized` is a
  3-line wrapper). It is structurally the spec's fold: evaluate every
  policy, collect erroring policies into `Diagnostic.Errors`, forbids
  trump permits, default deny (`forbid_trumps_permit`, `default_deny`,
  `allowed_iff_…` transfer directly). `evaluate` ≡ `internal/eval`:
  `ToEval` compiles `ast.Node` into an `Evaler` tree (`convert.go`,
  85 LOC) whose 53 `Eval` methods (`evalers.go`, 1,549 LOC) are the
  operator semantics; `Compile` wraps a policy as a `BoolEvaler`. A
  refinement would relate `Evaler.Eval(env)` to `Spec.evaluate`
  per node kind — 50 of the 53 lower statically.
- *`order_and_dup_independent` does NOT transfer as stated*: the Go
  `Diagnostic.Reasons` and `.Errors` are SLICES filled in
  `range policies.All()` order, and `PolicyMap.All` is `maps.All(p)`
  over a Go map (`policy_set.go:24-26`) — so the ORDER of
  determining/erroring policies in the Go response is Go map-iteration
  latitude, an observable the Lean `Set PolicyID` abstracts away. The
  GoLean machine reifies map-iteration order as a choice (latitude
  inventory §E9, map iteration order — enveloped), so a refinement statement must quotient
  `Reasons`/`Errors` to sets (or the harness must sort them) — a
  concrete, measured reason the DRT JSON comparison would need
  set-equality on those two fields.
- *Set/Map canonical or Go maps*: `types.Set` is `map[uint64]Value`
  keyed by a 64-bit FNV hash of the element with linear probing on
  collision (`types/set.go:11-33`; `hashVal` = sum of element hashes),
  `types.Record` wraps `map[String]Value` (`record.go:14-18`);
  canonical (sorted) order is produced only at hash/marshal time via
  `slices.Sort` (`record.go:30,153,181`, `set.go:151,175`). So the Go
  side is NOT the spec's canonical sorted list — equality is
  hash-plus-`Equal`, and the refinement needs an abstraction function
  from the probing map to the canonical set, plus a hash-collision
  argument (the probe loop at `set.go:20-30` makes correctness
  independent of collisions; that is a lemma to prove, not assume).
  `hash` itself is `hash/fnv` — refused today.
- *`like`*: hand-written glob (`types/pattern.go:86-136`), no `regexp`;
  lowers statically. Good news for the refinement — it is a small
  recursive matcher over `[]patternComponent`.
- *JSON codec's reflect use*: cedar-go writes explicit
  `MarshalJSON`/`UnmarshalJSON` for every Cedar type (`internal/json`,
  `types/*.go`) but each bottoms out in `encoding/json.Marshal/
  Unmarshal` over tagged structs — 38 declarations in 6 packages — so
  the codec IS reflect-bound (through the stdlib), exactly the G6
  frontier; the DRT harness's JSON-out leg cannot run on the machine
  before G6.
- *Extension types*: `decimal` is pure integer arithmetic (lowers
  except parse: `strconv.ParseInt`/`math.Pow10`); `ipaddr` is
  entirely `net/netip` (all 10 methods refused — netip is a
  128-bit-address library with zone handling, a specified-primitive
  question); `datetime` is `time` (refused; and the source of the §3.2
  kill); `duration` is integer milliseconds (printing lowers; parsing
  needs `unicode.IsDigit`/`strconv.QuoteRune`).
- *TPE / partial evaluation*: cedar-go has `internal/eval/partial.go`
  (591 LOC, `PartialPolicy`) and `x/exp/batch` (402 LOC) — the
  analogues of TPE/BatchedEvaluator; the k8s Rust `residual.rs`
  fold rules (5) have their Go counterpart in `partial.go:214 partial`
  (178 LOC, lowers statically) — a place where a Go-side theorem could
  cover what the Rust side leaves in comments.

## 8. Provenance and reproducibility

- `docs/census/cedar-go-2026-09-03/`: `results.tsv` (per case),
  `census.tsv` + `histogram.tsv` + `per-package.tsv` (frontend
  per-declaration, pass A), `demand.tsv` + `demand-histogram.tsv` +
  `demand-per-package.tsv` (static), `cedar-go-inventory.tsv`,
  `k8s-inventory.tsv`, `k8s-classes.tsv`, `meta.tsv`; pass B:
  `results-passB-relaxed.tsv`, `census-passB-relaxed.tsv`,
  `meta-passB-relaxed.tsv`.
- Re-run: `scripts/setup-deps --only cedar-go,cedar-access-control-for-
  k8s [--from <sibling>]` (opt-in rows added this lane; public URLs),
  `scripts/capped lake build golean`, `scripts/cedar-census run`; pass
  B as in §1. Wall time ≈ 25 s per pass after the golean build.
- Slice-delta table (§4) command: a Python fold over `demand.tsv` with
  the bucket rule stated in §4 (run inline at census time; the rule is
  the specification, the TSV is the data — anyone can re-fold).
- Decisions in this lane, all [AGENT]: exclude test-support packages;
  the `xexp/constraints` stand-in; the pass-B relax patch and its
  labelling; the static census as the substitute for the blocked
  frontend census; the supply table's contents (copied from the memo
  §1.2 tables); the S1-S4/G6 bucket rule. The [USER] question is the
  only [USER] item; no gate, baseline, corpus or trust-surface change
  was made or proposed for merge.

## 9. Addendum 2026-09-04 — the FR-22 / FR-23 slice re-measured [AGENT]

Lane `fr22-fr23` (worker under the [AGENT] coordinator; the frontier
queue ordering is [USER]-ratified §0 direction 2, the rowing rule is
[USER] direction 3 — both relayed, cited as relayed). Method: §1's
drivers, re-run with the slice's frontend over the SAME assembled copy
(`artifacts/cedar/cases/*`, 34 cases); the machine-side pipeline is
unchanged. Full record: `docs/evidence/2026-09-04_fr22-fr23/`.

### 9.1 What moved

| kill (§3.2 / §3.3) | before | after |
|---|---|---|
| FR-22 `var maxDatetime = time.Date(…)` — whole export | 18/22 packages + 9/9 drivers refused on it | GONE: `time.Date` is an `init-callee` register row (result-only, panic-free over the admitted argument shapes — the row's written argument), so the two initializers are SKIPPED and `maxDatetime`/`minDatetime` are poisoned per declaration (`$poisoned` cells; readers `types.Datetime.…` quarantine by name). The kill for callees NOT on the register stays whole-export by design (H-11 audit F1/F1b: the skip cannot be argued unobservable) and now names the var, the callee and the register. |
| FR-23 `iter.Seq`/`iter.Seq2` in a method / func / interface SIGNATURE — whole export | the pass-B second kill (10 signatures) | GONE: signatures emit in SIGNATURE-OPAQUE mode — the instantiation is an opaque marker under its mangled TypeId (`iter.Seq2[cedargo/types.String,cedargo/types.Value]`), the declaration is a fail-closed stub, satisfaction still answers exactly (the same key on the requirement and the implementation), every CALL refuses by name (FR-23), and a body that consumes the value refuses at its own emit (FR-12 for the `range`, FR-23 for the value). `authorize.go:13`'s `PolicyIterator` interface lowers the same way. |

### 9.2 What did NOT move — the next kill, measured (pass A′, this slice's frontend, no relaxation)

**Export fraction unchanged: 5/34 cases** (`internal`, `internal/consts`,
`internal/mapset`, `internal/rust`, `cedark8s/cmd/schema-formatter` —
the same five as §3.1). All 29 previously FR-22-refused cases now refuse
on ONE new cause:

```
native frontend unsupported: sync.Map (only Mutex/RWMutex/WaitGroup/Once are modeled)
```

Traced (evidence dir, `trace-syncmap.txt`): cedar-go has no `sync.Map`
of its own. `types/record.go:35` calls `binary.Write(h,
binary.LittleEndian, m[k].hash())`; `encoding/binary` is a
source-through library unit (slice 2), `Write` is reached, its reach
walk reaches `dataSize` → the package-level `var structSize sync.Map`,
and `collectGlobals` refuses that var's TYPE for the whole export (since
the slice's audit fix round the text NAMES it: `package-level var
encoding/binary.structSize: its TYPE does not lower (sync.Map (only …)) —
FR-24 …`; the bare text above is what the census run measured). The
register's `encoding/binary` row said "an unreached sync.Map" — true
until a program reaches `binary.Write/Read/Size`; cedar-go does (the row
now says so). Rowed
as **FR-24** (ledger §4, queue 24, S): the FR-22 mechanism applied to an
unlowerable TYPE — seed the cell as `$poisoned`, quarantine every reader
(`dataSize`, hence `Write/Read/Size`) by name, keep the export. Witness
`init/library-var-type-unlowerable` (born-FAIL, subject untouched by the
var).

### 9.3 Pass C (counterfactual, LABELLED): past FR-24

Census COPY only, never `deps/`: `record.go:35`'s `binary.Write` replaced
by the byte-identical `var hb [8]byte; binary.LittleEndian.PutUint64(hb[:],
m[k].hash()); _, _ = h.Write(hb[:])` (little-endian `uint64` is exactly
those 8 bytes; the hash writer never errors) — symmetric under `go run`,
so it cannot skew the differential, and it is what FR-24's fix would
expose. Still 5/34 EXPORT-OK; the 29 refusals split into TWO causes:

| cause | cases | class | row |
|---|---|---|---|
| `method stencil cedargo/internal/mapset.ImmutableMapSet[cedargo/types.EntityUID].All does not lower (instantiation of imported generic type iter.Seq[cedargo/types.EntityUID] …) — FR-4` | 25 (everything importing `types`) | method STENCILS have no per-declaration quarantine (the H-3 residual) — a SOURCE generic type's method returning `iter.Seq[T]`, at its first instantiation | **FR-4** (queue 4, ½–1 day; the stencil refusal now NAMES the stencil — this slice's diagnostic strengthening in `mono.go flushTypeInsts`) |
| `slices.Sort at non-integer element type string` | 4 (`all`, `drv-validate`, `x/exp/schema`, `x/exp/schema/internal/parser`) | an `init()` BODY (`x/exp/schema/internal/parser/marshal.go:350`) — init code has no per-declaration quarantine BY DESIGN (it runs before every subject), so this is the genuine `slices.Sort`-beyond-integer-kinds gap, not a frontend kill class | FR-14 / memo §3 row M (`sortSlice` machine op at integer kinds only) |

So the frontier for cedar-go's export, in order: FR-24 (S) → FR-4 (S) →
`slices.Sort` at string (memo row M) → then the per-declaration picture
of §3.4 becomes measurable by the frontend census for the first time
(the demand histogram's `errors.Join` 29 / `bytes.Buffer` 31 /
`encoding/json` 38 / `slices.Contains` 15 members become per-function
quarantines, not kills — `errors.Join` and `bytes.Buffer` are
source-through since slice 2, so many of those should now LOWER; that
claim is NOT measured here and is left as the next census's question).

### 9.4 Numbers

pass A′ (this slice): FRONTEND-REFUSED 29 (all `sync.Map`), EXPORT-OK 5,
machine 0/0/0. pass C (counterfactual): FRONTEND-REFUSED 29 (25 FR-4 +
4 `slices.Sort`), EXPORT-OK 5. Per-declaration census of the five
exporting packages: unchanged from §3.1 (their declarations touch
neither kill). The static demand census (§3.4) is unaffected — its
`sig:imported-generic-inst` key correctly still reads "refused": the
MEMBERS are still refused by name; what changed is the blast radius
(per declaration, not per export).

Decisions in this addendum, all [AGENT]: the pass-C relaxation and its
labelling; rowing FR-24 rather than folding it into this slice (the
brief's scope was the two rowed kills; FR-24 is the smallest-diagnosed
next item and is posed to the coordinator as such). No gate, baseline,
corpus or trust-surface claim is made here beyond the slice's own
landing records.

## 10. Addendum 2026-09-04 — FR-24 / FR-25 landed, cmp.Compare retired: re-measured [AGENT]

Lane `fr24` (worker under the [AGENT] coordinator; the rowing rule is
[USER] direction 3 and the posture «break rather than preserve incorrect
behaviour» — both relayed, cited as relayed; the two rulings this lane
lands are quoted in §10.1). Method: §1's drivers, re-run with each
checkpoint's frontend over the SAME assembled copy (`artifacts/cedar/
cases/*`, 34 cases) plus `scripts/lower-diagnose artifacts/cedar/cases/all`
(the standing full-blocker report, `docs/2026-09-04_lower-diagnose.md`);
machine-side pipeline unchanged. Full record:
`docs/evidence/2026-09-04_fr24-fr25/` (`before/`, `census-A/`, `after/`).

### 10.1 What moved

| kill | before (§9.2, main aceb0dcb) | after |
|---|---|---|
| FR-24 `var structSize sync.Map` (encoding/binary, reached through `binary.Write` → `dataSize`) — whole export at `collectGlobals` | 29/34 cases refused on `package-level var encoding/binary.structSize: its TYPE does not lower (sync.Map …) — FR-24 …` | GONE as a kill (checkpoint A): the var is POISONED per declaration (`$poisoned` cell, gid kept); `dataSize` is an H-3 stub naming `encoding/binary.structSize`, `sync.Map` and the cause; the rest of the package lowers (`wires-B/init_library-var-type-poisoned.wire.json`). |
| (new, the handoff's kill #1) the H-3 residue: `reflect.Value` recorded in the D5 method-set table by `binary.Write`'s body BEFORE the body refused | masked behind FR-24 | GONE (A): the registration rides the mono journal and rolls back with the refused body (`monoLogImportedNamed`) — independently witnessed by a user `reflect.ValueOf(x).Len()` program (a whole-export kill on main; now an H-3 stub, `methods/quarantine-imported-type-residue`). |
| FR-25 `complex128` in `reflect.Type`'s requirement list (`OverflowComplex`), reached from the now-lowering `encoding/binary.sizeof(t reflect.Type)` — whole export in the interface pass; and `reflect.Value`'s D5 stubs (`Complex() complex128`) skipping whole | masked behind FR-24 on cedar-go; measured on the corpus rows at A (`init/library-var-type-poisoned/*`: `basic type complex128`) | GONE (checkpoint B, the [USER]-approved rider «(3) yes, makes sense»): the opaque `named complex128` marker + existence-only `unsupported` TypeDef; `reflect.Value` gets its marker + full stub set. The FR-24 witness `init/library-var-type-unlowerable` flipped PASS only here — two checkpoints deep, as the handoff predicted. |
| the `cmp.Compare` kind desugar (D-002's last non-fmt shim) | retained by slice 2's STOP rule | RETIRED (checkpoint C, [USER] ruling «(2) given we have a plan, I think this should be an honest red»): no cedar-go effect (cedar-go's `cmp.Compare` calls are at package-level types); the corpus row `slices/sortfunc-cmp/cmp-compare-kinds` is the honest red (FR-19's line). |

### 10.2 What did NOT move — the next kills, measured (checkpoints A, B and C agree)

**Export fraction unchanged: 5/34 cases** (`internal`, `internal/consts`,
`internal/mapset`, `internal/rust`, `cedark8s/cmd/schema-formatter` —
the same five as §3.1). The 29 refusals split into the TWO causes §9.3's
pass C predicted counterfactually — now measured on the UNRELAXED copy:

| cause | cases | class | row |
|---|---|---|---|
| `method stencil cedargo/internal/mapset.ImmutableMapSet[cedargo/types.EntityUID].All does not lower (instantiation of imported generic type iter.Seq[…] …) — FR-4` | 25 (everything importing `types`) | method STENCILS have no per-declaration quarantine (the H-3 residual) — a SOURCE generic type's method returning `iter.Seq[T]` | **FR-4** (queue 4) — the next kill |
| `slices.Sort at non-integer element type string` | 4 (`all`, `drv-validate`, `x/exp/schema`, `x/exp/schema/internal/parser`) | an `init()` body (`x/exp/schema/internal/parser/marshal.go:350`) — init code has no per-declaration quarantine BY DESIGN | FR-14 / memo §3 row M |

Why FR-25 never showed on cedar-go itself: the FR-4 stencil refusal fires
in the mono drain BEFORE the interface fixpoint that would have hit
`OverflowComplex(complex128)`; the census sees one first refusal per
case. The corpus rows carry the FR-25 witness instead.

Behind these two, the static census (`after/lower-diagnose/report.txt`)
names the order: FR-19 `nodeJSONAlias` (a duplicate TypeId in
`x/exp/schema/internal/json`, 2 declarations, export-scoped), then the
per-declaration surface — `encoding/json` (FR-14, G6/reflect: 64
declarations), `net/netip` type methods (19), `errors.Is/As` (reflect,
10), `iter.Seq` values in bodies (FR-23 → FR-12). Every cause in the
report has a ledger row (`TestCausesTableAgreesWithLedger`); no
UNROWED cause appeared in this run.

### 10.3 Numbers

before (main aceb0dcb): FRONTEND-REFUSED 29 (all FR-24), EXPORT-OK 5,
machine 0/0/0. after A: FRONTEND-REFUSED 29 (25 FR-4 + 4 `slices.Sort`),
EXPORT-OK 5. after C (tip): FRONTEND-REFUSED 29 (25 FR-4 + 4
`slices.Sort`), EXPORT-OK 5, machine 0/0/0. lower-diagnose static —
UNIT AND SCOPE (audit fix round M4): 1554/1671 counts declarations of ALL
kinds (funcs, methods, types, vars, consts) over cedargo + the two
cedark8s packages + the `xexp/constraints` stand-in + the case's `main`,
so it is NOT §0/§3.4's 1085 (funcs+methods, cedargo only); the comparable
funcs+methods figure the report prints for the same widened scope is
1012/1126 (89.9%); "N/26 packages" counts `main` and the stand-in —
before 1554/1671 (93.0%), 11 export-kill declarations, 21/26 packages
export-killed; after (tip): 1554/1671 (93.0%) UNCHANGED — the per-declaration picture
does not move because nothing that refused now lowers (the kills became
stubs, the values stay refused) — but the EXPORT picture does: export-
kill declarations 11 → 3 and packages export-killed 21/26 → 7/26 (own or
inherited): FR-24's var and FR-25's method signatures are decl-scoped in
the static pass now; the 3 remaining are FR-19's `nodeJSONAlias` ×2
(`x/exp/schema/internal/json`) and the `slices.Sort` at string inside
`init()` (`x/exp/schema/internal/parser`). The dynamic first refusal on
the whole-library case is FR-4 (the mono drain runs first), which the
static pass does not see (a stencil-time refusal) — the report's
"not judged statically" section says so by count.

Decisions in this addendum, all [AGENT]: keeping the H-3 residue fix in
checkpoint A; widening the D5 stub pass to the opaque window at B (D5 in
the evidence README); rowing FR-26 (a struct FIELD of an unlowerable
type) rather than fixing it here. No gate, baseline, corpus or
trust-surface claim is made here beyond the lane's own landing records.
