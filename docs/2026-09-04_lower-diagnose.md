# The lowering diagnostic — every blocker, not just the first (2026-09-04)

Lane `lower-diagnose`, [AGENT], under [USER] direction (4) of
`docs/language-coverage-ledger.md` §0. Report-only lane tooling: no
gate, baseline, corpus or `GoLean/` change; the one frontend change is
one line of stderr text (§6); `scripts/ci` gains ONE guard-strengthening
step (`go test ./tools/lowerdiag`, §8). Evidence:
`docs/evidence/2026-09-04_lower-diagnose/`. Audit fix round (11 items,
verdict FIX-FIRST): §9.

## 1. Why

A frontend refusal shows ONE cause — the first the emitter hit. On
cedar-go the census (`docs/2026-09-03_cedar-go-coverage-census.md`) hit
`time.Date` in a package-level initializer (FR-22); relaxing it revealed
`iter.Seq2` in a method signature (FR-23); the `fr22-fr23` lane fixed
both and met `sync.Map` under `encoding/binary.Write` (FR-24) — the
export fraction 5/34 unchanged each time. Mike, 2026-09-04, relayed by
the [AGENT] coordinator (cited as relayed, not firsthand): «Right, I
agree - it'd be useful if we didn't just get stuck without any
information about *why* it's happening». The census already had the
answer's shape — its §3.4 STATIC demand census (892/1085 declarations
demanding nothing refused) beside the frontend's first-kill view — as a
cedar-only private tool. This lane generalizes it into
`scripts/lower-diagnose <any program>` and makes the cause vocabulary a
single tracked table checked against the ledger.

## 2. Shape

```
scripts/lower-diagnose <go package dir | main.go> [--json] [--tsv] [--include pkg,pkg] [--out DIR] [--no-frontend]
```

1. **DYNAMIC pass** — the real frontend (`tools/nativefrontend --dir …`)
   with its wire sent to a fresh `mktemp` dir under a non-wire name,
   read ONCE by `lowerdiag wire` for the per-declaration quarantine list
   and deleted. Its EXIT STATUS is handed to the report verbatim: rc 0 =
   EXPORT OK (with the wire's quarantined declarations listed); a
   nonzero rc WITH the frontend's own `native frontend unsupported`
   line = the first refusal, classified; a nonzero rc WITHOUT one (a
   crash, a shim exit 3, a build failure), rc 124 (timeout), or rc 0
   with no wire produced = INFRA naming the rc — never EXPORT OK.
2. **STATIC pass** — `tools/lowerdiag report`: `go/types` over the
   program and its transitive case-local imports (the frontend's loader
   shape: `<root>/<path>` is a local package, all else is stdlib through
   the host's export data — host toolchain must equal
   `baselines/go-oracle-pin`, else refuse / `GOLEAN_ALLOW_GO_DRIFT=1`
   loudly; `--include` adds case-local packages the main package does
   not import — the census's extra roots). For EVERY declaration
   (funcs, methods, vars, consts, types, plus a `file` pseudo-declaration
   for import/build-tag shapes) the set of refused demands, judged
   against three supply tables:
   - `docs/stdlib-admission-register.md` — READ at run time (the fenced
     machine block): source-through packages, retained shims,
     intercepts, shadow types. Never a hardcoded list; an unknown
     register class refuses.
   - `tools/lowerdiag/machine-surface.tsv` — the language/memory-model
     surface the machine owns (sync types/ops, atomics wave-1
     prefixes/kinds, H-11's `pureUnmodeledCallees`). Test-checked for
     SET EQUALITY, both ways, against the frontend's own tables derived
     with go/ast from `syncOpFor`/`syncValueOpFor`/`emitSyncOpStmt`,
     wire.go's sync arm, `atomicOpPrefixes`/`atomicIntSuffixes`,
     `pureUnmodeledCallees` (§8).
   - `tools/lowerdiag/library-refusals.tsv` — members of SOURCE-THROUGH
     packages the loader refuses BY NAME (`errors.Is/As` → reflectlite;
     `strconv.FormatFloat` → float-bits; `slices.Insert` → overlaps;
     `bytes.ToUpper/Join/…` → MakeNoZero; `bytes.Buffer.Read*` → `io.EOF`;
     `encoding/binary.Read/Write/Size` → reflect), each row naming its
     baseline witness (must be FAIL — a PASS means the gap closed and
     the row is stale) or the evidence dir that observed it.
3. **REPORT** — first refusal + its cause row (and, when the text is
   ambiguous — a body call and an initializer call share one string —
   the static SITE carrying the key, so an export-scoped initializer is
   named; when the frontend spells the key differently, the
   declarations carrying the same CAUSE, with a distinct note); the
   distance line; the histogram by cause (declarations touching,
   SOLE-blocker count = the direct unblock value, packages, export-kill
   count, top keys); top blockers with their FR rows/plans; the
   cumulative projection ("fix these → N more declarations lower, K
   exports revived" — ONE convention with the distance line: a
   declaration lowers when no finding at all, may-refuse included, has
   an unfixed cause); per package (lowers / may-refuse / refused /
   export status: `ok`, `KILLED (own: …)`, `KILLED (inherited from …)`);
   the refused stdlib keys; an UNROWED line (certain AND may-refuse);
   and the **"not judged statically" section — every causes.tsv id the
   static pass never emits, with the count of THIS program's
   declarations referencing the surface it covers** (fmt shim callers
   for the verb matrix, generic sites for mono.go's stencil-time
   refusals, source-through callers for FR-24's library-variable shape,
   …; `-` = shape-level). Human text and `--json`; `--tsv` writes
   `decls.tsv`, `histogram.tsv`, `per-package.tsv`. Every report is
   stamped with the commit (+dirty) and the sha of the three tables.

Every artifact opens with `DIAGNOSTIC — NOT A LOWERING` — the reports,
the TSVs, `lowerdiag wire`/`vocabulary` output, the recorded stderr
(`frontend-first-refusal.txt`, with the exit status as its second
line). The output root must be EXACTLY `artifacts/lower-diagnose/` or
below it (the script refuses `..`, a bare `artifacts/`, `artifacts/
coverage`, and any environment override elsewhere); the tool refuses to
write any base name containing `wire.json` in any case with any suffix.
No gate, baseline or corpus path reads any of it.

## 3. The cause table — `tools/lowerdiag/causes.tsv`

One row per cause (52 rows): `id, fr, status, scope, pattern, key,
diagnosis`. `fr` is a ledger §4 `FR-n`, a §6 `Q-*`, or one of six fixed
tokens (`out-of-language`, `by-design`, `cascade`, `c-pin`, `unrowed`,
`apparatus`). `scope` records what the frontend does TODAY: `decl`
(per-declaration quarantine), `export` (whole-export refusal), or
`call` (the DECLARATION lowers and the CALL refuses when reached — an
imported type's D5 stub; library-refusals.tsv members carry the same
per-finding `CALL` mark). `pattern` is the Go regexp the dynamic pass
and `lowerdiag wire`/`classify` match the frontend's text against; an
unmatched text stays `UNCLASSIFIED` with its head as the key — never
absorbed. The static pass emits ids from the same table
(`staticCauseIDs`, checked at start-up).

**Coverage of the frontend's vocabulary, measured** (`lowerdiag
vocabulary tools/nativefrontend`; `TestVocabularyCoverageIsTracked`):
341 distinct `unsup(…)` format strings in the frontend's non-test
sources; **325 classified from the format alone**; the 16 remaining are
tracked in `tools/lowerdiag/unclassified-formats.txt` (the test asserts
equality, so a new unclassified string surfaces). Twelve of the 16
classify from the REAL text (the pattern keys on the argument: `builtin
println in statement position`, `sync.Map.Load with 2 arguments`,
`&composite in short-circuit operand`); four are frontend invariants
that carry another message (`emit.go:215 "%s"`, the mono substitution
internals). Two catch-all rows (`statement-shape`, `expression-shape`,
both `unrowed`) and one `apparatus` row (pin/overlay/register/shim-table
inconsistencies — properties of the tree, not the program) cover the
long tail so it is COUNTED, not absorbed.

**The ledger check** (`TestCausesTableAgreesWithLedger`): a `rowed` FR/Q
id must be a `| FR-n |` / `| Q-<name> |` row of the ledger; a
`pending:<branch>` id must NOT be — when the branch lands the flag is
stale and the test (now a `scripts/ci` step) fails until it is flipped.
Red-first witness: `TestCausesTableCatchesAnUnrowedFR`. Today one row is
pending: `global-type-unlowerable` → FR-24 on branch `fr22-fr23`.

## 4. What the static pass judges, and does not

The measured direction is **UNDER-approximation** (§5's calibration:
what fires is exact — 0 false positives after the fix round; what is
not judged is listed per run). Static rules (certain, `refused(static)`):
stdlib calls/vars/method calls outside the register (FR-14 by shape:
package unmodeled / member of a shim package / var / value position /
imported type's method — the last CALL-scoped), library-refusals.tsv
members (CALL-scoped), FR-12 range-over-func, FR-13 anonymous structs
(any type position, including signatures), FR-15 complex, FR-23
imported generic instantiations (signature of a METHOD = export kill —
funcs quarantine with an arity-only stub, emit.go line 278; body = per
declaration), FR-22 initializer kills (an initializer that does not
lower and contains a call outside `pureUnmodeledCallees`; the non-call
shapes `initializerEffectIsolated` also rejects are NOT tracked — export
scope is UNDER-reported for them), any certain finding inside an
`init()` body (emitted without a per-declaration quarantine — whole
export), FR-24's user-package analogue (a package-level var whose type
does not lower), FR-19 duplicate local TypeIds, FR-1/16 go/defer of
builtins, defer/go of an intercepted member (`slices.Sort`,
`cmp.Compare`), `slices.Sort` at a non-integer element type, FR-2/18
receive / slice-map literal / `&T{}` / make-new-append-copy / tuple
splat in a short-circuit RHS (struct VALUE literals lower — checked
against `hoistSliceLit`/`emitMapLit`/`emitAddressOf`), FR-3 `(*T).Mv`,
FR-6 range assignment targets, FR-7 tuple boxing on the ASSIGN and
VALUE-SPEC paths ONLY (interface target ← NON-interface component; the
RETURN path lowers — the emitter destructures with an explicit box; the
first cut's return arm was a phantom, §9 item 2), FR-17 `x := f(x)`
reading a BARE outer `x` (selector members `r.x` and struct-literal keys
are not reads — the twin wire disproved the first cut, §5),
quarantine-cascade (a reader of a package-level var that is refused PER
DECLARATION — not of an export-killed one), Q-SYNCLIT non-empty sync
literals, Q-SYNCVAL sync method values/expressions, unsafe/reflect/print
(out of language), sync/atomic outside the machine surface (Q-COND,
Q-ATOMIC by shape). `main.main` is never emitted by the frontend and is
not a census declaration.

Shape-dependent (`may-refuse`, excluded from the distance numerator and
the projection base alike): FR-11 goto hoisting, non-reserved build tags.

Not judged — disclosed PER RUN with counts (report section "not judged
statically", §2): the fmt verb×kind matrix (`fmt-verb-matrix`: N
declarations call a fmt shim member), mono.go's stencil-time refusals
(`generics-corner`, `generic-template`, `local-type-type-argument` C6,
`stencil-whole-export` FR-4: N declarations declare or instantiate
generics), `cmp.Compare`'s shape bound, D5 markers, FR-24's real shape
(a reached LIBRARY variable: N declarations call into source-through
units), load-time shapes, statement/expression corner arms, apparatus
strings, `result-shadow`, `labeled-shape`, the promoted-sync-method-via-
interface-dispatch spelling of Q-SYNCVAL.

## 5. Calibration against the frontend (evidence dir)

- **Calibration test** (`TestCalibrationAgainstWire`, in `scripts/ci`):
  the real frontend emits a wire for `testdata/calib` and every user
  declaration's static verdict (decl/export-scoped refusals) must equal
  the wire's quarantine set; shim callers are reported as not judged,
  not asserted. The fixture holds the FR-7 RETURN case (`retBox` —
  lowers in the wire, as the static pass now says), the FR-7 ASSIGN case
  (`assignBox` — refused, both agree), `slices.Sort` at `[]string`
  (refused) and `[]int` (lowers), `defer slices.Sort` (refused),
  `errors.Is` (the DECLARATION lowers — the wire quarantines
  `errors.Is` itself; the static finding is CALL-scoped and agrees), a
  source-through member that lowers, a fmt caller (not judged). 9
  declarations checked, 0 disagreements.
- **Raft twin program**: frontend EXPORT OK; the probe wire has 32
  quarantined non-shim declarations (`raft-twin/frontend-quarantines.tsv`,
  0 UNCLASSIFIED), of which 6 are USER-package declarations:
  `DefaultLogger.Fatal/Fatalf` (`os.Exit`) — the static pass's two
  refused declarations, exactly; `quorum.MajorityConfig.Describe` (C6,
  a stencil-time refusal — disclosed under generics, 10 declarations)
  and `MemoryStorage.Lock/TryLock/Unlock` (Q-SYNCVAL's promoted-through-
  interface-dispatch spelling — disclosed, not judged). The other 26 are
  library text (`bytes.Buffer.Read*`×7, `internal/bytealg`×2 — FR-21 /
  `io.EOF` value position), `log.Logger`'s D5 marker + 16 uncalled
  method stubs. `DefaultLogger.Panic/Panicf` call `log.Logger.Panic*`:
  CALL-scoped — the declarations lower (the wire agrees) and the calls
  refuse when reached. Static: 691/696 declarations demand nothing
  refused (99.3%), 486/490 funcs+methods, 0 export kills.
- **cedar-go** (the census's whole-library case + the two `cedark8s`
  packages via `--include`): first refusal on main today is `sync.Map
  (only Mutex/…)` — FR-24's shape, not FR-22's: since stdlib-source-2
  landed, `encoding/binary` is source-through, `binary.Write` is reached
  from `types/record.go`, and `collectGlobals` refuses the library's
  `structSize sync.Map` BEFORE the initializer dry-run reaches
  `time.Date`. The refusal text names the type, not the variable nor the
  package — a message gap (the FR-24 lane should wrap it with the
  var/site, as FR-22's fix did); the report's note says so heuristically.
  Static, cedargo only: **974/1085 funcs+methods (89.8%) vs the census's
  892/1085 — same denominator package by package**; `cedark8s/internal/
  schema` 36/38 (the census's §6 number REPRODUCED). The per-declaration
  diff against the census (`cedar-go/census-2026-09-03-vs-now.tsv`;
  evidence README): 85 declarations census-refused → now lower (register
  rows landed since: `errors.Join` 24, `bytes.Buffer.WriteRune` 15,
  `slices.Contains` 13, `bytes.Buffer.Bytes` 4+, `strings.*`,
  `utf8.*`, `strconv.*`) and **3 census-lowers → now refused, all
  REAL**: `internal/parser.Decoder.decode` reads `io.EOF` (a var of an
  unmodeled package — the census tool did not check var reads);
  `x/exp/schema/internal/parser.init` calls `slices.Sort` on `[]string`
  (an `init()` body → WHOLE-EXPORT kill — the census's pass-C
  counterfactual "a slices.Sort init()" found statically); `cedark8s/
  internal/schema.CedarSchema.SortActionEntities`, the same
  `slices.Sort@string`. 13 export-kill declarations in 5 packages take
  21/26 packages down: `types` (`Record.All/Keys/Values`, `Set.All`
  FR-23; `maxDatetime/minDatetime` FR-22), `internal/mapset` (FR-23 ×2),
  `cedargo` (FR-23 ×2), `x/exp/schema/internal/parser` (`init`,
  `slices.Sort@string`), and `internal/json` — **`nodeJSON.MarshalJSON`/
  `UnmarshalJSON` each declare a local `type nodeJSONAlias`: an FR-19
  duplicate-TypeId export kill the census never reached**. Top blockers
  by sole count: FR-14 package surface (32 sole / 64 decls —
  `encoding/json` 32, `maps.*` 16, `hash/fnv`, `net/netip`), FR-14
  imported-type methods (9/19, CALL-scoped), reflect via `errors.Is/As`
  (7/10, CALL-scoped), `slices.Sort@string` (6/10), FR-23 signatures
  (6/8), FR-23 body instantiations (1/36), FR-12 (0/21 — every one
  rides an `iter.Seq`, so FR-12 unblocks nothing until FR-23).
- **gotest slice** (the 10 largest FRONTEND-REFUSED files of the
  2026-09-01 run, staged as `scripts/gotest-triage` stages them: `func
  main()` renamed `gotestMain()` + a one-line `main`): 230/308
  declarations lower statically, 78 refused; `print-builtin` is the top
  sole blocker on 5 of the 10 (out of language — the G2 slice decides),
  FR-14 on `map.go` (`math.*`), `complex` on `gcgort.go` (no `math.*`
  there), `reflect` on `recover.go` (16 sole). The frontend is EXPORT OK
  on 8 of the 10 and the report now LISTS each probe wire's
  quarantines: `typeparam/list2.go` is 41/41 statically but its wire
  quarantines `checkList[int|string]` and `checkListPointers[int|
  string]` on the fmt verb matrix (`%p`; `%v` over `interface{}`) — the
  not-judged section says 2 declarations call fmt shim members (the
  templates; the 4 stencils are theirs).
- **Corpus frontier rows**: `range/range-func-basic` → FR-12 (1/1),
  `complex/basic` → FR-15, `control-flow/goto-backward-capture` →
  goto-hoist may-refuse only (export OK, the wire quarantines it per
  declaration), `init/stdlib-initializer-call` → the text says FR-14
  `time.Date`, the static site says `var maxDatetime` initializer,
  EXPORT-scoped, FR-22, `generics/imported-generic-in-signature` → FR-23
  export; the dynamic key is `main.Bag.All`, the static one the
  instantiated type — the report lists the 2 same-cause declarations
  with the distinct "spelled differently" note (§9 item 9).

## 6. The frontend change (message text only)

`tools/nativefrontend/main.go` `main()`: after printing the refusal,
if the error is an `unsupported`, print one more stderr line: `for the
full blocker picture run scripts/lower-diagnose <the --dir of this
run>`. No emit path touched; the twin wire pin is unchanged (wires
carry no stderr). Consumers: `scripts/diff-coverage` puts the WHOLE
frontend stderr into a `FAIL/frontend-export` row's `detail=` column
(`one_line`'d); `scripts/coverage-baseline-diff` compares result and
stage only, so this moves no gate and no baseline row — the tracked
baseline's `detail` text for frontend-export rows will pick up the
extra clause at the next deliberate re-pin (a cosmetic diff, said here
so it is not mistaken for drift). `gotest-triage` and `cedar-census`
take `head -1`.

## 7. Census integration (one implementation)

`scripts/cedar-census demand` runs `tools/lowerdiag report --tsv… --include
<the cedark8s packages>` over the whole-library case dir and writes the
same three files as before (`demand.tsv`, `demand-histogram.tsv`,
`demand-per-package.tsv`, each with the banner line) plus
`demand-report.txt`; `drive` and `report` classify wires and refusal
lines with `lowerdiag wire` / `lowerdiag classify` (banner-aware).
`tools/cedarcensus/demand.go` and its private `rules` table are deleted;
`cedarcensus` keeps `inventory` and `decls` (pure inventory). Rule-level
diff against the retired tool, recorded in the census doc's tooling
note: the old `go-statement` flag (every `go` counted as a refusal —
dropped: `go` lowers), the old syntactic anonymous-struct rule (any
`struct{…}` AST node — replaced by the typed rule), the old
unconditional `goto` flag (replaced by certain FR-20 vs may-refuse
FR-11), no var-read / init-body / slices.Sort-kind / library-refusal
rules (added).

## 8. Tests (`go test ./tools/lowerdiag`, a `scripts/ci` step)

16 tests: the ledger check + its red-first witness; table shape
(malformed rows refuse: bad regexp, bad token, bad status, duplicate
id); every static cause id is a table row; **machine-surface.tsv
SET-EQUAL both ways to the frontend's tables** derived with go/ast, with
two red-first witnesses (the audit's fabricated `sync.RWMutex.RLocker`
row is caught; a dropped `WaitGroup.Done` row is caught); library-
refusals.tsv witnesses are FAIL in the baseline (a PASS = stale row);
the register is READ (a missing register refuses); the text classifier
over 16 vocabulary samples; vocabulary coverage = the tracked list; the
fixture `testdata/fivecauses` (exactly five causes, the FR-22 kill on
`var epoch`); **crashed-frontend fail-closed** (rc 3/1/97/124 with or
without stderr → INFRA naming the rc, never EXPORT OK; rc 0 → OK; a
nonzero rc with a named refusal → that refusal; banner lines skipped);
byte-identical text+JSON+TSV over three renders; the first-refusal site
lookup; wire-like file names refused (case-insensitive, any suffix);
**calibration against a real wire** (§5).

## 9. Audit fix round (2026-09-04, verdict FIX-FIRST — the separation
was sound, the measurement misreported)

1. (HIGH, fail-open) rc ∉ {0, refusal-with-text} read as EXPORT OK →
   `--frontend-rc` is mandatory with `--frontend-stderr`; INFRA names the
   rc; rc 0 with no wire = rc 97 INFRA. Tested.
2. (HIGH, phantom) the FR-7 RETURN arm deleted; both cedar-go FR-7
   findings were return sites. Calibration fixture pins `retBox`.
3. (HIGH) machine-surface test was a substring check → set equality
   both ways against go/ast-derived frontend tables; red-first with the
   RLocker fabrication and a dropped real row.
4. (MED-HIGH) claims corrected: list2's 4 stencil quarantines are now
   in the report (probe-wire list) and the doc; raft "4 = 4" → 2
   user-declaration matches + 4 not-judged user quarantines, 32 non-shim
   total, itemized; "drawn from every unsup string" → 325/341 measured,
   16 tracked; "+92 register" → 85 improvements (register rows), 3
   regressions all REAL (listed), denominators identical.
5. (MED) blind spots: rules ADDED for `slices.Sort` kind, intercepted
   defer/go, quarantine-cascade, sync literals, sync method values, and
   library-refusals.tsv (errors.Is/As etc.); every remaining non-static
   cause id is listed per run with reference counts; static.go's header
   says under-approximation; §4 no longer claims Q-SYNCVAL's interface-
   dispatch spelling is static.
6. (MED) calibration test added (§5).
7. (MED) `scripts/ci` runs `go test ./tools/lowerdiag` (guard-
   strengthening only — no ci step reads the diagnostic's output).
8. (MED) output root = exactly `artifacts/lower-diagnose/` or below;
   `..` refused; wire-like names refused case-insensitively with any
   suffix; banner on every artifact (stderr record, `wire` output, the
   tracked raft-twin TSVs).
9. (MED) same-cause fallback for the first-refusal site lookup.
10. (MED) evidence: a clean-tip `scripts/capped scripts/ci --diff` at the
    fix-round tip (README gate section); "4 findings" → 3.
11. (MED) `cedark8s/internal/schema` covered again via `--include`;
    36/38 reproduced; rule-level diff recorded (§7).
LOW: the hint line prints the run's `--dir`; one lowers-convention for
distance and projection; UNROWED fires for may-refuse; table sha
stamped; §5 prose corrected (gcgort, "5 of 10"); README counts.
