# The lowering diagnostic — every blocker, not just the first (2026-09-04)

Lane `lower-diagnose`, [AGENT], under [USER] direction (4) of
`docs/language-coverage-ledger.md` §0. Report-only lane tooling: no
gate, baseline, corpus or `GoLean/` change; the one frontend change is
one line of stderr text (§6). Evidence:
`docs/evidence/2026-09-04_lower-diagnose/`.

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
scripts/lower-diagnose <go package dir | main.go> [--json] [--tsv] [--out DIR] [--no-frontend]
```

1. **DYNAMIC pass** — the real frontend (`tools/nativefrontend --dir …
   --out /dev/null`); its stderr's first line is the first refusal,
   exactly what a user sees today. No wire is kept.
2. **STATIC pass** — `tools/lowerdiag report`: `go/types` over the
   program and its transitive case-local imports (the frontend's loader
   shape: `<root>/<path>` is a local package, all else is stdlib through
   the host's export data — host toolchain must equal
   `baselines/go-oracle-pin`, else refuse / `GOLEAN_ALLOW_GO_DRIFT=1`
   loudly). For EVERY declaration (funcs, methods, vars, consts, types,
   plus a `file` pseudo-declaration for import/build-tag shapes) the set
   of refused demands, judged against two supply tables:
   - `docs/stdlib-admission-register.md` — READ at run time (the fenced
     machine block): source-through packages, retained shims,
     intercepts, shadow types. Never a hardcoded list; an unknown
     register class refuses.
   - `tools/lowerdiag/machine-surface.tsv` — the language/memory-model
     surface the machine owns (sync types/ops, atomics wave-1
     prefixes/kinds, H-11's `pureUnmodeledCallees`), every row citing
     the frontend file it transcribes (test-checked).
3. **REPORT** — first refusal + its cause row (and, when the text is
   ambiguous — a body call and an initializer call share one string —
   the static SITE that carries the key, so an export-scoped initializer
   is named); the distance line; the histogram by cause (declarations
   touching, SOLE-blocker count = the direct unblock value, packages,
   export-kill count, top keys); top blockers with their FR rows/plans;
   the cumulative projection ("fix these → N more declarations lower, K
   exports revived"); per package (lowers / may-refuse / refused /
   export status: `ok`, `KILLED (own: …)`, `KILLED (inherited from …)`);
   the refused stdlib keys; an UNROWED line when a cause has no ledger
   row. Human text and `--json`; `--tsv` writes `decls.tsv`,
   `histogram.tsv`, `per-package.tsv`.

Every artifact opens with `DIAGNOSTIC — NOT A LOWERING`; the output root
is `artifacts/lower-diagnose/` (gitignored; the script refuses any root
outside `artifacts/`); the tool refuses to write under a `*wire.json`
name. No gate, baseline or corpus path reads any of it.

## 3. The cause table — `tools/lowerdiag/causes.tsv`

One row per cause (49 rows at landing): `id, fr, status, scope, pattern, key,
diagnosis`. `fr` is a ledger §4 `FR-n`, a §6 `Q-*`, or one of five fixed
tokens (`out-of-language`, `by-design`, `cascade`, `c-pin`, `unrowed`).
`scope` records what the frontend does TODAY: `decl` (per-declaration
quarantine) or `export` (whole-export refusal). `pattern` is the Go
regexp the dynamic pass and `lowerdiag wire`/`classify` match the
frontend's text against (the vocabulary was drawn from every `unsup(…)`
format string in `tools/nativefrontend`); an unmatched text stays
`UNCLASSIFIED` with its head as the key — never absorbed. The static
pass emits ids from the same table (`staticCauseIDs`, checked at
start-up).

**The ledger check** (`go test ./tools/lowerdiag`,
`TestCausesTableAgreesWithLedger`): a `rowed` FR/Q id must be a `| FR-n |`
/ `| Q-<name> |` row of the ledger; a `pending:<branch>` id must NOT be —
when the branch lands the flag is stale and the test fails until it is
flipped to `rowed`. Red-first witness: `TestCausesTableCatchesAnUnrowedFR`
(a table claiming a bogus id — `FR-` followed by 999 — is caught). Today one row is pending:
`global-type-unlowerable` → FR-24 on branch `fr22-fr23` (unmerged at
this lane's base `e0657d47`).

`unrowed` causes (`build-constraint`, `local-import-shape`,
`init-schedule`, `labeled-shape`, `result-shadow`, `generics-corner`,
`frontend-invariant`) are refusals the frontend has and the ledger does
not row; the report flags them so direction (3) can row them when one
appears on a real program. None appeared on cedar-go, raft or the
gotest slice (`build-constraint` appeared as may-refuse on raft's
`state_trace_nop.go`, a non-reserved tag).

## 4. What the static pass sees, and does not

Certain (`refused(static)`): stdlib calls/vars/method calls outside the
register (FR-14 by shape: package unmodeled / member of a shim package /
var / value position / imported type's method), FR-12 range-over-func,
FR-13 anonymous structs (any type position, including signatures),
FR-15 complex, FR-23 imported generic instantiations (signature of a
METHOD = export kill — funcs quarantine with an arity-only stub, emit.go
line 278; body = per declaration), FR-22 initializer kills (an
initializer that does not lower and contains a call outside
`pureUnmodeledCallees` — the effect-isolation allowlist's call arm;
the non-call shapes it also rejects are NOT tracked, so export scope is
UNDER-reported for them), any certain finding inside an `init()` body
(emitted without a per-declaration quarantine — whole export, design
note §2), FR-24's user-package analogue (a package-level
var whose type does not lower), FR-19 duplicate local TypeIds, FR-1/16
go/defer of builtins, FR-2/18 receive / slice-map literal / `&T{}` /
make-new-append-copy / tuple splat in a short-circuit RHS (struct VALUE
literals are not hoisted and lower — checked against `hoistSliceLit` /
`emitMapLit` / `emitAddressOf`), FR-3 `(*T).Mv`, FR-6 range assignment
targets, FR-7 tuple boxing (interface target ← NON-interface component,
the emitter's exact condition; interface→interface lowers), FR-17
`x := f(x)` reading a BARE outer `x` (selector members `r.x` and
struct-literal keys are not reads — the first cut flagged them and the
raft twin's wire disproved it, §5), unsafe/reflect/print (out of
language), sync/atomic outside the machine surface (Q-COND, Q-ATOMIC,
Q-SYNCVAL, Q-SYNCLIT by shape).

Shape-dependent (`may-refuse`, excluded from the distance numerator):
FR-11 goto hoisting (only certain hoisted-variable shapes refuse),
non-reserved build tags.

Not visible (said in every report's notes): fmt's verb×kind matrix
(`fmt.Sprintf` with a constant format counts as supplied), FR-21 gaps
inside source-through library text (library members count as lowering
— `bytes.Buffer.Read*`'s `io.EOF` quarantines in the raft wire are
invisible statically), mono.go's stencil-time refusals (C6 local type
arguments), package-level VARIABLES of library units (FR-24's real
shape — the first-refusal note names it heuristically when a bare type
key has no user site), and `main.main`, which the frontend never emits.

## 5. Calibration against the frontend (evidence dir)

- **Raft twin program** (the `check-frontend-pins` assembly): frontend
  EXPORT OK; wire pin sha `69a538de…` reproduced by the diagnostic's own
  probe emit. Static: 691/696 declarations (99.3%), 486/490
  funcs+methods, 0 export kills, 4 refused: `DefaultLogger.Fatal/Fatalf`
  (`os.Exit`), `DefaultLogger.Panic/Panicf` (`log.Logger.*`) — exactly
  the wire's user-declaration quarantines (`raft-twin-crosscheck/`).
  The wire's OTHER quarantines are library text (`bytes.Buffer.Read*`,
  `internal/bytealg`), the D5 stubs of `log.Logger`'s uncalled methods,
  `quorum.MajorityConfig.Describe` (C6, stencil-time) and the promoted
  sync methods through interface dispatch (Q-SYNCVAL) — each outside the
  static pass's resolution as stated, and each now CLASSIFIED by the
  table (three of them were `UNCLASSIFIED` in the first cut).
- **cedar-go** (the census's whole-library case, 22 packages +
  `xexp/constraints`): first refusal on main today is `sync.Map (only
  Mutex/…)` — FR-24's shape, not FR-22's: since stdlib-source-2 landed,
  `encoding/binary` is source-through, `binary.Write` is reached from
  `types/record.go`, and `collectGlobals` refuses the library's
  `structSize sync.Map` BEFORE the initializer dry-run reaches
  `time.Date`. The refusal text names the type, not the variable nor the
  package — a message gap (the frontend's `emitType` cause bubbles up
  bare); the FR-24 lane should wrap it with the var/site, as FR-22's
  fix did. Static: funcs+methods 985/1086 (90.7%; cedargo only:
  984/1085 vs the census's 892/1085 — same denominator package by
  package, +92 explained by register rows landed since: `errors.Join`,
  `bytes.Buffer.*`, `slices.Contains/Collect/Sorted/Clone`,
  `strings.Compare`, `utf8.*`, `strconv.Parse*/Quote*` are source-through
  now; one package −1 on a new FR-7 return-boxing finding). 12 export-kill
  declarations in 4 packages take 20/24 packages down: `types`
  (`Record.All/Keys/Values`, `Set.All` FR-23; `maxDatetime/minDatetime`
  FR-22), `internal/mapset` (`MapSet.All`, `ImmutableMapSet.All` FR-23),
  `cedargo` (`PolicyMap.All`, `PolicySet.All` FR-23), and
  `internal/json` — **`nodeJSON.MarshalJSON`/`UnmarshalJSON` each
  declare a local `type nodeJSONAlias`: an FR-19 duplicate-TypeId
  export kill the census never reached** (hidden behind FR-22/23/24 in
  the first-kill view; `cedargo/ast` inherits it). Top blockers by sole
  count: FR-14 package surface (33 sole / 62 decls — `encoding/json`
  38, `maps.*` 16, `hash/fnv`, `net/netip`), FR-14 imported-type
  methods (9/19, `net/netip.*`, `json.Decoder`), FR-23 signatures (6/8),
  FR-23 body instantiations (1/36), FR-12 (0/21 — every one rides an
  `iter.Seq`, so FR-12 unblocks nothing until FR-23).
- **gotest slice** (the 10 largest FRONTEND-REFUSED files of the
  2026-09-01 run, staged as `scripts/gotest-triage` stages them: `func
  main()` renamed `gotestMain()` + a one-line `main`): `typeparam/list2.go`
  now lowers entirely (41/41; its refusal was `fmt.Sprintf`'s verb
  matrix at the run's tip — the register moved since); `chan/powser{1,2}`
  (56/61, 58/63), `ken/{div,mod}const` (11/27 each), `fixedbugs/issue2615`
  are `print`/`println` + `math/rand`/`os.Args`; `recover.go` (39/67) is
  `reflect` (17 decls, 16 sole) + `println` (10); `gcgort.go`, `map.go`
  are complex + `math.*`; `fixedbugs/bug257.go` (20k lines, one
  function) is `crypto/md5` + `fmt.Println` + `println` in that one
  function. Aggregate over the ten: 230/308 declarations lower
  statically, 78 refused; `print-builtin` is the top sole blocker on 6
  of the 10 (out of language — the G2 slice decides), FR-14 next; the
  frontend's first refusal is EXPORT OK on 8 of the 10 (the refusals
  are per-declaration quarantines the gotest run saw at run time).
- **Corpus frontier rows**: `range/range-func-basic` → FR-12 (1/1),
  `complex/basic` → FR-15, `control-flow/goto-backward-capture` →
  goto-hoist may-refuse only (the frontend quarantines it per
  declaration — export OK, as the tool says), `init/stdlib-initializer-call`
  → the text says FR-14 `time.Date`, the static site says `var
  maxDatetime` initializer, EXPORT-scoped, FR-22 (the ambiguity the
  site lookup exists for), `generics/imported-generic-in-signature` →
  FR-23 export, 2 static decls.

## 6. The frontend change (message text only)

`tools/nativefrontend/main.go` `main()`: after printing the refusal,
if the error is an `unsupported`, print one more stderr line: `for the
full blocker picture run scripts/lower-diagnose <the --dir given
above>`. No emit path touched; the twin wire pin is unchanged (wires
carry no stderr). Consumers: `scripts/diff-coverage` puts the WHOLE
frontend stderr into a `FAIL/frontend-export` row's `detail=` column
(`one_line`'d); `scripts/coverage-baseline-diff` compares result and
stage only, so this moves no gate and no baseline row — the tracked
baseline's `detail` text for frontend-export rows will pick up the
extra clause at the next deliberate re-pin (a cosmetic diff, said here
so it is not mistaken for drift). `gotest-triage` and `cedar-census`
take `head -1`.

## 7. Census integration (one implementation)

`scripts/cedar-census demand` now runs `tools/lowerdiag report --tsv…`
over the whole-library case dir and writes the same three files as
before (`demand.tsv`, `demand-histogram.tsv`, `demand-per-package.tsv`,
each with the banner line) plus `demand-report.txt`; `drive` and
`report` classify wires and refusal lines with `lowerdiag wire` /
`lowerdiag classify`. `tools/cedarcensus/demand.go` and its private
`rules` table are deleted; `cedarcensus` keeps `inventory` and `decls`
(pure inventory). The census doc's §3.4 numbers stand as the 2026-09-03
measurement with a tooling note pointing here.

## 8. Tests

`go test ./tools/lowerdiag`: the ledger check + its red-first witness;
table shape (malformed rows refuse: bad regexp, bad token, bad status,
duplicate id); every static cause id is a table row; every
machine-surface row cites an existing frontend file that mentions the
entry; the register is READ (a missing register refuses, not an empty
supply); the text classifier over 16 vocabulary samples; the fixture
`testdata/fivecauses` (exactly five causes, the FR-22 kill on `var
epoch`, clean declarations lower); byte-identical text+JSON+TSV over
three renders; the first-refusal site lookup; wire file names refused.
