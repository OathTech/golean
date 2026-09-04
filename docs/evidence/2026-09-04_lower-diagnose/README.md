# lower-diagnose runs — the lowering diagnostic's outputs on cedar-go, the raft twin, the gotest slice and corpus frontier rows (2026-09-04, refreshed at the audit fix round)

Consuming docs: `docs/2026-09-04_lower-diagnose.md` (§5 cites every
number here; §9 the fix round), `docs/language-coverage-ledger.md` §0
direction (4), `docs/coverage-suite-structure.md` "Diagnosing a
refusal", `docs/2026-09-03_cedar-go-coverage-census.md` §3.4 tooling
note. Lane `lower-diagnose`, branch off main `e0657d47`. [AGENT]
throughout, under [USER] direction (4) as relayed by the coordinator
(ledger §0). Every artifact here was re-produced after the audit fix
round (items 1–11 + LOW cluster); the first-cut numbers this README
once carried are superseded and named where they differed.

## What this is

First-hand records of `scripts/lower-diagnose` (engine `tools/lowerdiag`)
over the four target sets the lane brief named, the two unit-test
fixtures, and `scripts/cedar-census demand`. Every `report.txt`/
`report.json`/`*.tsv` opens with the line `DIAGNOSTIC — NOT A LOWERING`:
none is a wire, none is read by any gate, baseline or corpus path.
`*.first-refusal.txt` files are the REAL frontend's stderr for that
target behind a banner and a `# frontend exit status: N` line (rc 0 =
export OK); `frontend-quarantines.tsv` is `lowerdiag wire` over the
probe wire (read once from a mktemp dir, then deleted) when the export
succeeded.

## Conclusion

The diagnostic reports every blocker, classified by cause and ledger FR
row, where the frontend reports one — and is now CALIBRATED against the
frontend's wires: the calibration fixture agrees on 9/9 judged
declarations (0 false positives; FR-7's return shape lowers, `slices.Sort`
at `[]string`, `defer slices.Sort` and `errors.Is` are found, the last
CALL-scoped because the wire quarantines the library function, not the
caller), and on the raft twin the static pass's two refused user
declarations are exactly the two user-declaration quarantines it can
judge; the four it cannot (a C6 stencil, three promoted sync methods
through interface dispatch) are in the report's "not judged
statically" section by count. On cedar-go the frontend's first refusal
on main today is `sync.Map` — FR-24's shape, not the census's FR-22 —
and the static census finds 13 export-kill declarations in 5 packages
taking 21/26 down, including an FR-19 duplicate-TypeId kill in
`internal/json` and a `slices.Sort([]string)` inside an `init()` in
`x/exp/schema/internal/parser` that no first-kill view had reached;
cedargo funcs+methods 974/1085 lower statically (the census's 892/1085 —
same denominator package by package; 85 improvements from register rows
landed since, 3 regressions all real refusals, itemized below);
`cedark8s/internal/schema` 36/38 reproduces the census's §6. Gotest:
230/308 declarations over the ten largest refused files, `print`/
`println` the top sole blocker on five. Two frontend message findings
for other lanes: the FR-24 refusal text names a type but not the library
variable or package, and the same string serves a body call and an
initializer call (the diagnostic disambiguates by static site).

## Reproduction (from the repo root, at the commit below)

```sh
scripts/setup-deps --only go,goose,cedar-go,cedar-access-control-for-k8s --from <sibling checkout>
GO111MODULE=off GOCACHE=$PWD/artifacts/go-build-cache go test ./tools/lowerdiag      # 16 tests (incl. the calibration run)
scripts/lower-diagnose tools/lowerdiag/testdata/fivecauses --json --tsv                # -> fixture/
scripts/lower-diagnose tools/lowerdiag/testdata/calib --json --tsv                     # -> calib/
# raft twin (the check-frontend-pins assembly)
mkdir -p artifacts/lower-diagnose/inputs/raft-twin
for p in quorum raftpb tracker proto confchange raft; do cp -r raftsubject/$p artifacts/lower-diagnose/inputs/raft-twin/; done
for f in twin-lib.go twin-chdriver.go twin-chdriver-main.go; do cp tools/raftsubject/$f artifacts/lower-diagnose/inputs/raft-twin/; done
scripts/lower-diagnose artifacts/lower-diagnose/inputs/raft-twin --json --tsv           # -> raft-twin/ (frontend-quarantines.tsv = the wire's classification)
awk -F'\t' '!/^#/ && $6 ~ /refused|may/' artifacts/lower-diagnose/artifacts__lower-diagnose__inputs__raft-twin/decls.tsv   # -> raft-twin/static-refused-decls.tsv (behind a banner line)
# cedar-go (the census's whole-library case dir + the cedark8s packages as extra roots)
scripts/cedar-census assemble && scripts/cedar-census cases
scripts/lower-diagnose artifacts/cedar/cases/all --json --tsv --include cedark8s/cmd/schema-formatter,cedark8s/internal/schema   # -> cedar-go/
scripts/cedar-census demand                                                            # -> cedar-go/census-demand-report.txt (same engine, same numbers)
# gotest: the 10 largest FRONTEND-REFUSED files of the 2026-09-01 run, staged as scripts/gotest-triage stages them
for f in fixedbugs/bug257.go gcgort.go chan/powser2.go chan/powser1.go map.go ken/modconst.go ken/divconst.go typeparam/list2.go recover.go fixedbugs/issue2615.go; do
  slug="${f//\//__}"; slug="${slug%.go}"; d=artifacts/lower-diagnose/inputs/gotest/$slug; mkdir -p $d
  sed 's/^func main()/func gotestMain()/' deps/go/test/$f > $d/main.go; printf '\nfunc main() { gotestMain() }\n' >> $d/main.go
  scripts/lower-diagnose $d --json --tsv; done                                          # -> gotest/
for c in range/range-func-basic complex/basic control-flow/goto-backward-capture init/stdlib-initializer-call generics/imported-generic-in-signature; do
  scripts/lower-diagnose Corpus/coverage/exec/$c --json; done                           # -> corpus/
```

The ten gotest files: `awk -F'\t' '$1=="FRONTEND-REFUSED"{print $2}'
artifacts/gotest/results.tsv` of the 2026-09-01 run (worktree
`t4-gotest`, gitignored artifacts), ranked by `wc -l` of
`deps/go/test/<file>`. The census comparison table
(`cedar-go/census-2026-09-03-vs-now.tsv`) joins the 2026-09-03 census
worktree's `artifacts/cedar/demand-per-package.tsv` (tip `1b8401c0`;
gitignored, so the table is the record) with `cedar-go/per-package.tsv`;
the per-declaration regression/improvement lists below join that
worktree's `demand.tsv` with `cedar-go/`'s `decls.tsv` on (package,
name).

## Toolchain, commit, host

- `go version`: go1.26.5 linux/amd64 = `baselines/go-oracle-pin` (every
  report header prints `go: go1.26.5`; the tool refuses on drift).
  deps/go @ c19862e5f8 (the pin), deps/cedar-go @ cda92d0,
  deps/cedar-access-control-for-k8s @ 660c637 (setup-deps pins).
- Commit: the reports print `commit: <sha>+dirty` and `tables: <sha12>`
  — run on the lane's working tree at the fix-round tool state before
  the fix-round commit (the tree = that commit's content; the dirty flag
  is the uncommitted lane itself). The gate tails below name their own
  commits.
- Host: linux/amd64, the shared agent box under concurrent lane load;
  nothing here is timing-sensitive.

## Files

| file | what |
|---|---|
| `fixture/report.{txt,json}`, `fixture/frontend-first-refusal.txt` | `testdata/fivecauses`: 5 causes, the FR-22 kill on `var epoch`; the frontend's first refusal names `time.Unix` (FR-14 text) and the report places it at the export-scoped initializer |
| `calib/report.txt`, `calib/frontend-quarantines.tsv` | `testdata/calib`: EXPORT OK; the probe wire quarantines `assignBox`, `sortStrings`, `deferSort` (+ the library functions `errors.Is`/`slices.Sort` stencil) — the static verdicts agree (`TestCalibrationAgainstWire`) |
| `raft-twin/report.txt`, `histogram.tsv`, `per-package.tsv` | 691/696 declarations (99.3%), 486/490 funcs+methods, 0 export kills; refused: `DefaultLogger.Fatal/Fatalf` (`os.Exit`); CALL-scoped: `DefaultLogger.Panic/Panicf` (`log.Logger.*` — the declarations lower); may-refuse: `raft/state_trace_nop.go`'s `//go:build !with_tla`; the "not judged" section: 10 generic-site declarations (C6's home), 17 touching imported types, 1 calling cmp.Compare |
| `raft-twin/frontend-first-refusal.txt` | banner + `# frontend exit status: 0` — export OK |
| `raft-twin/frontend-quarantines.tsv` = `wire-decls-classified.tsv` | the twin wire's 967 declarations (968 rows minus header) classified by `lowerdiag wire`: 37 quarantined = 5 injected `goleanShim*` runtime-refusal helpers + 32 others — 6 USER-package: `raft.DefaultLogger.Fatal/Fatalf` (static: refused, match), `quorum.MajorityConfig.Describe` (C6 local type argument — not judged, disclosed), `raft.MemoryStorage.Lock/TryLock/Unlock` (promoted sync methods via interface dispatch, Q-SYNCVAL — not judged, disclosed); 26 library: `bytes.Buffer.Peek/Read/ReadByte/ReadFrom/ReadRune/readSlice/WriteTo` (`io.EOF`/`io.ErrShortWrite` value position), `internal/bytealg.Cutover/IndexString` (FR-21 placeholder bodies), `log.Logger` D5 marker + 16 uncalled-method stubs — 0 UNCLASSIFIED |
| `raft-twin/static-refused-decls.tsv` | the static pass's refused / may-refuse rows |
| `cedar-go/report.{txt,json}`, `histogram.tsv`, `per-package.tsv`, `frontend-first-refusal.txt` | the whole-library case + 2 cedark8s packages: first refusal `sync.Map (only Mutex/…)` (rc 1); 1554/1671 declarations, 1012/1126 funcs+methods; 13 export-kill declarations; 21/26 packages export-killed |
| `cedar-go/census-demand-report.txt` | `scripts/cedar-census demand`'s report over the same case — identical numbers (one implementation) |
| `cedar-go/census-2026-09-03-vs-now.tsv` | per-package funcs+methods and lowers: census vs now (cedargo 1085 → 1085, 892 → 974; cedark8s/internal/schema 38 → 38, 36 → 36) |
| `gotest/<file>.report.txt`, `<file>.first-refusal.txt` | the ten files; EXPORT-OK reports list the probe wire's quarantines |
| `corpus/<row>.report.txt`, `<row>.first-refusal.txt` | five frontier rows |
| `gate/ci-fast-tail.txt` | the fast gate in the fresh worktree (first cut): all steps ok except the two baseline-diff steps, which FAIL CLOSED with no recorded run — hence `--diff` |
| `gate/ci-diff-tail.txt` | the first-cut `--diff` gate at the base tree (dirty): PASS 3350/3350, 0 drift |
| `gate/ci-diff-clean-tip-tail.txt` | the CLEAN-tip `--diff` gate at the fix-round commit (below) |

## Findings worth a line each

1. **cedar-go's first kill on main is FR-24's shape, not FR-22's.** Since
   stdlib-source-2 landed, `encoding/binary` is source-through;
   `binary.Write` is reached from `types/record.go:35`; `collectGlobals`
   refuses the library's `var structSize sync.Map` before H-11's
   initializer dry-run ever sees `time.Date`. The refusal text is the bare
   type cause — no variable, no package (message gap for the FR-24 lane);
   the report's note names the shape heuristically.
2. **Two export kills the census never reached**: `cedargo/internal/json`
   `nodeJSON.MarshalJSON`/`UnmarshalJSON` each declare a function-local
   `type nodeJSONAlias nodeJSON` → FR-19 duplicate TypeId (`cedargo/ast`
   inherits it); `cedargo/x/exp/schema/internal/parser`'s `init()` calls
   `slices.Sort` on `[]string` — the sortSlice op's integer bound inside an
   `init()` body, which the frontend emits without a per-declaration
   quarantine (whole export). The census's pass-C counterfactual named "a
   slices.Sort init()" by hand; the static pass finds it.
3. **FR-12 unblocks nothing by itself on cedar-go**: all 21
   range-over-func sites range over an `iter.Seq` value, so every one is
   also an FR-23 body instantiation (36 decls); the FR-23 signature kills
   (8 decls, 6 sole) come first, as the ledger's queue orders them.
4. **Census vs now, per declaration** (cedargo, same 1085 denominator):
   85 census-refused → now lower — the register rows landed since
   2026-09-03 (`errors.Join` 24, `bytes.Buffer.WriteRune` 15,
   `slices.Contains` 13, `bytes.Buffer.Bytes` 4, `strings.TrimPrefix/
   TrimSuffix/Contains/Compare/Index/HasPrefix/ReplaceAll`,
   `unicode/utf8.DecodeRune/ValidRune`, `unicode.Is/IsDigit`,
   `strings.Builder.WriteRune`, `strconv.ParseInt/Quote/QuoteRune`,
   `bytes.NewBuffer`, `slices.Clone`); **3 census-lowers → now refused,
   all REAL**: `internal/parser.Decoder.decode` reads `io.EOF`
   (`imported package-level variable io.EOF has no seeded cell` — the old
   tool did not check var reads); `x/exp/schema/internal/parser.init`
   (finding 2); `cedark8s/internal/schema.CedarSchema.SortActionEntities`
   (`slices.Sort@string`). Net 892 → 974 (+82). The first cut reported
   985 with +92/−1: it counted `errors.Is/As` callers (9) and two more
   as lowering and carried two FR-7 return-path phantoms — corrected.
5. **The static pass's first cut was wrong three times and the frontend
   corrected it** (kept as the calibration record): (a) FR-17 `x := f(x)`
   flagged selector members (`r.trk`) as reads — 8 phantom refusals on
   raft, 41 on cedar-go; the twin wire lowered every one; fixed to bare
   identifiers. (b) FR-18 flagged struct VALUE literals in a
   short-circuit RHS; the emitter hoists only slice/map literals and
   `&T{}`; fixed. (c) FR-7 flagged `return two()` into interface results;
   the emitter destructures with an explicit box — a phantom on 2 cedar-go
   declarations; the arm is deleted and the calibration fixture pins it.
   Also mirrored: `main.main` is never emitted (emit.go:131); `init()`
   bodies are whole-export; library-side quarantines (`errors.Is`) leave
   the CALLER lowered — CALL scope.
6. **gotest**: `typeparam/list2.go` (refused on `fmt.Sprintf`'s verb
   matrix at the 2026-09-01 tip) is EXPORT OK today and 41/41 statically,
   but its probe wire quarantines the four stencils `checkList[int|string]`,
   `checkListPointers[int|string]` (`%p`; `%v` over `interface{}`) — the
   report lists them and its "not judged" section counts the 2 fmt-shim
   callers; the frontend is EXPORT OK on 8/10 — the run's
   FRONTEND-REFUSED verdicts came at RUN time from per-declaration stubs,
   which the reports now itemize.
7. **Vocabulary coverage, measured**: 341 distinct `unsup(…)` formats,
   325 classified from the format alone, 16 tracked
   (`tools/lowerdiag/unclassified-formats.txt`; 12 classify from the real
   text, 4 are invariants carrying another message).

## Gate

- `GO111MODULE=off go test ./tools/lowerdiag`: ok (16 tests: ledger check
  + red-first witness, machine-surface SET EQUALITY vs the frontend's
  tables + two red-first witnesses, library-refusal witnesses,
  vocabulary coverage, crashed-frontend fail-closed, determinism,
  5-cause fixture, CALIBRATION against a real wire — 9 declarations,
  0 disagreements). `go vet ./tools/lowerdiag ./tools/cedarcensus
  ./tools/nativefrontend`: clean.
- First cut (superseded, kept): `gate/ci-fast-tail.txt` (fast gate
  fails closed in a fresh worktree — no recorded run) and
  `gate/ci-diff-tail.txt` (`--diff` at the BASE tree, dirty: PASS
  3350/3350, 0 drift).
- **Fix round, CLEAN tip**: `scripts/capped scripts/ci --diff` at the
  fix-round commit with a clean tree — `gate/ci-diff-clean-tip-tail.txt`
  (its RESULT line, the 3350-row baseline diff, the negative 394, the
  twin pin `69a538de…`, and the new `lowering-diagnostic tables` step
  are all in the tail). Recorded in the records commit that follows the
  fix-round commit (the tail cannot be in the commit it certifies).
- `scripts/check-spec-anchors`: ok. `scripts/check-bugs.sh`: backlog 14
  (10 coverage / 4 latitude / 0 wrong-answer), unchanged.
- `tools/reconcile-records`: 3 findings, 0 HIGH — C13 and C5 pre-exist
  on main (the round-10 tail records "C13+C5 only"); the one new is a LOW
  C6 dangling-id note on `FR-24` (rowed on the unmerged `fr22-fr23`
  branch — the causes table carries the same `pending:fr22-fr23` status
  and its test, now a ci step, flips to STALE when the row lands).
