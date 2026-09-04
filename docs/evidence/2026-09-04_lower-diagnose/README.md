# lower-diagnose runs — the lowering diagnostic's first outputs on cedar-go, the raft twin, the gotest slice and corpus frontier rows (2026-09-04)

Consuming docs: `docs/2026-09-04_lower-diagnose.md` (§5 cites every
number here), `docs/language-coverage-ledger.md` §0 direction (4),
`docs/coverage-suite-structure.md` "Diagnosing a refusal",
`docs/2026-09-03_cedar-go-coverage-census.md` §3.4 tooling note. Lane
`lower-diagnose`, branch off main `e0657d47`. [AGENT] throughout, under
[USER] direction (4) as relayed by the coordinator (ledger §0).

## What this is

First-hand records of `scripts/lower-diagnose` (engine `tools/lowerdiag`)
over the four target sets the lane brief named, plus the fixture the
unit tests pin. Every `report.txt`/`report.json`/`*.tsv` here opens with
the line `DIAGNOSTIC — NOT A LOWERING`: none is a wire, none is read by
any gate, baseline or corpus path. `*.first-refusal.txt` files are the
REAL frontend's stderr for that target (empty = export OK) — the second
line of a non-empty one is the new hint line (`for the full blocker
picture run scripts/lower-diagnose …`), the lane's only frontend change.

## Conclusion

The diagnostic reports every blocker, classified by cause and ledger FR
row, where the frontend reports one. Calibration against the frontend
held where it can be checked: on the raft twin the static pass's four
refused user declarations are exactly the wire's four user-declaration
quarantines (`raft-twin/`), and the wire the diagnostic's own probe emit
produced has the pinned sha (`69a538de…`). On cedar-go the frontend's
first refusal on main today is `sync.Map` — FR-24's shape, not the
census's FR-22 — and the static census finds 12 export-kill
declarations in 4 packages taking 20/24 down, including an FR-19
duplicate-TypeId kill in `internal/json` no first-kill view had reached;
funcs+methods 985/1086 lower statically (cedargo only 984/1085 vs the
census's 892/1085 — same denominator package by package; the +92 are
register rows landed since, itemized in `cedar-go/census-2026-09-03-vs-now.tsv`
and below). Gotest: 230/308 declarations over the ten largest refused
files, `print`/`println` the top sole blocker on six. Two frontend
message findings for other lanes: the FR-24 refusal text names a type
but not the library variable or package (the diagnostic says so
heuristically), and the same string serves a body call and an
initializer call (the diagnostic disambiguates by static site).

## Reproduction (from the repo root, at the commit below)

```sh
scripts/setup-deps --only go,goose,cedar-go,cedar-access-control-for-k8s --from <sibling checkout>
GO111MODULE=off GOCACHE=$PWD/artifacts/go-build-cache go test ./tools/lowerdiag      # 11 tests
# fixture
scripts/lower-diagnose tools/lowerdiag/testdata/fivecauses --json --tsv                # -> fixture/
# raft twin (the check-frontend-pins assembly)
mkdir -p artifacts/lower-diagnose/inputs/raft-twin
for p in quorum raftpb tracker proto confchange raft; do cp -r raftsubject/$p artifacts/lower-diagnose/inputs/raft-twin/; done
for f in twin-lib.go twin-chdriver.go twin-chdriver-main.go; do cp tools/raftsubject/$f artifacts/lower-diagnose/inputs/raft-twin/; done
scripts/lower-diagnose artifacts/lower-diagnose/inputs/raft-twin --json --tsv           # -> raft-twin/
#   cross-check: the wire's quarantine stubs vs the static refusals
GO111MODULE=off go run ./tools/nativefrontend --dir artifacts/lower-diagnose/inputs/raft-twin --out artifacts/lower-diagnose/raft-twin-crosscheck/twin.wire.json.DIAGNOSTIC-COPY
artifacts/lower-diagnose/lowerdiag wire artifacts/lower-diagnose/raft-twin-crosscheck/twin.wire.json.DIAGNOSTIC-COPY > raft-twin/wire-decls-classified.tsv
awk -F'\t' '!/^#/ && $6 ~ /refused|may/' artifacts/lower-diagnose/artifacts__lower-diagnose__inputs__raft-twin/decls.tsv > raft-twin/static-refused-decls.tsv
# cedar-go (the census's whole-library case dir)
scripts/cedar-census assemble && scripts/cedar-census cases
scripts/lower-diagnose artifacts/cedar/cases/all --json --tsv                          # -> cedar-go/
# gotest: the 10 largest FRONTEND-REFUSED files of the 2026-09-01 run, staged as scripts/gotest-triage stages them
for f in fixedbugs/bug257.go gcgort.go chan/powser2.go chan/powser1.go map.go ken/modconst.go ken/divconst.go typeparam/list2.go recover.go fixedbugs/issue2615.go; do
  slug="${f//\//__}"; slug="${slug%.go}"; d=artifacts/lower-diagnose/inputs/gotest/$slug; mkdir -p $d
  sed 's/^func main()/func gotestMain()/' deps/go/test/$f > $d/main.go; printf '\nfunc main() { gotestMain() }\n' >> $d/main.go
  scripts/lower-diagnose $d --json --tsv; done                                          # -> gotest/
# corpus frontier rows
for c in range/range-func-basic complex/basic control-flow/goto-backward-capture init/stdlib-initializer-call generics/imported-generic-in-signature; do
  scripts/lower-diagnose Corpus/coverage/exec/$c --json; done                           # -> corpus/
```

The selection of the ten gotest files: `awk -F'\t' '$1=="FRONTEND-REFUSED"{print $2}'
artifacts/gotest/results.tsv` of the 2026-09-01 run (worktree
`t4-gotest`, gitignored artifacts), ranked by `wc -l` of
`deps/go/test/<file>`. The census comparison table was produced by the
python block recorded in the lane's transcript from the 2026-09-03
census worktree's `artifacts/cedar/demand-per-package.tsv` (tip
`1b8401c0`; gitignored, so the table is the record) and
`cedar-go/per-package.tsv` here.

## Toolchain, commit, host

- `go version`: go1.26.5 linux/amd64 = `baselines/go-oracle-pin`
  (every report header prints `go: go1.26.5`; the tool refuses on
  drift). deps/go @ c19862e5f8 (the pin), deps/cedar-go @ cda92d0,
  deps/cedar-access-control-for-k8s @ 660c637 (setup-deps pins).
- Commit: the reports say `e0657d47…+dirty` — run on the lane's
  working tree at the final tool state before the landing commit (the
  frontend, `tools/lowerdiag` and `scripts/lower-diagnose` as
  committed; the dirty flag is the uncommitted lane itself). The gate
  ran at the same tree (below).
- Host: linux/amd64, the shared agent box under concurrent lane load;
  nothing here is timing-sensitive.

## Files

| file | what |
|---|---|
| `fixture/report.{txt,json}`, `fixture/frontend-first-refusal.txt` | `tools/lowerdiag/testdata/fivecauses`: 5 causes, the FR-22 kill on `var epoch`; the frontend's first refusal names `time.Unix` (FR-14 text) and the report places it at the export-scoped initializer |
| `raft-twin/report.txt`, `histogram.tsv`, `per-package.tsv` | 691/696 declarations (99.3%), 486/490 funcs+methods, 0 export kills; refused: `DefaultLogger.Fatal/Fatalf` (`os.Exit`), `DefaultLogger.Panic/Panicf` (`log.Logger.*`); may-refuse: `raft/state_trace_nop.go`'s `//go:build !with_tla` |
| `raft-twin/frontend-first-refusal.txt` | empty — export OK |
| `raft-twin/wire-decls-classified.tsv` | the twin wire's 968 declarations classified by `lowerdiag wire`: 37 quarantined = 5 injected `goleanShim*` runtime-refusal helpers (not library declarations) + 32 others: the 4 user ones above, library text `bytes.Buffer.Read*`×7 / `internal/bytealg`×2 (FR-21 / value-position `io.EOF`), `log.Logger`'s D5 marker + 16 uncalled-method stubs, `quorum.MajorityConfig.Describe` (C6), 3 promoted sync methods via interface dispatch (Q-SYNCVAL) — 0 UNCLASSIFIED (3 of these strings were unclassified in the first cut; rows added) |
| `raft-twin/static-refused-decls.tsv` | the static pass's refused/may-refuse rows: the same 4 + the build tag |
| `cedar-go/report.{txt,json}`, `histogram.tsv`, `per-package.tsv` | the whole-library case: first refusal `sync.Map (only Mutex/…)`; 1465/1569 declarations, 985/1086 funcs+methods; 12 export-kill declarations; 20/24 packages export-killed |
| `cedar-go/frontend-first-refusal.txt` | the frontend's two stderr lines |
| `cedar-go/census-2026-09-03-vs-now.tsv` | per-package funcs+methods and lowers: census vs now, cedargo only (1085 → 1085; 892 → 984) |
| `gotest/<file>.report.txt`, `<file>.first-refusal.txt` | the ten files |
| `corpus/<row>.report.txt`, `<row>.first-refusal.txt` | five frontier rows |
| `gate/` | the gate tails (below) |

## Findings worth a line each

1. **cedar-go's first kill on main is FR-24's shape, not FR-22's.** Since
   stdlib-source-2 landed, `encoding/binary` is source-through;
   `binary.Write` is reached from `types/record.go:35`; `collectGlobals`
   refuses the library's `var structSize sync.Map` before H-11's
   initializer dry-run ever sees `time.Date`. The `fr22-fr23` lane
   measured the same on its branch after fixing FR-22/23; on main the
   ORDER already puts FR-24 first. The refusal text is the bare type
   cause — no variable, no package (message gap for the FR-24 lane).
2. **An FR-19 export kill the census never reached**:
   `cedargo/internal/json` `nodeJSON.MarshalJSON` and `UnmarshalJSON` each
   declare a function-local `type nodeJSONAlias nodeJSON` → duplicate
   TypeId → whole-export refusal; `cedargo/ast` inherits it. Invisible in
   the first-kill view behind FR-22/23/24.
3. **FR-12 unblocks nothing by itself on cedar-go**: all 21
   range-over-func sites range over an `iter.Seq` value, so every one is
   also an FR-23 body instantiation (`imported-generic-inst`, 36 decls);
   the FR-23 signature kills (8 decls, 6 sole) come first, as the ledger's
   queue already orders them.
4. **Register movement since the census** (why 892 → 984): sole-blocker
   counts in the 2026-09-03 histogram of keys the register now supplies —
   `errors.Join` 24, `bytes.Buffer.WriteRune` 15, `slices.Contains` 13,
   `bytes.Buffer.Bytes` 5, `strings.Compare` 3, `strings.Builder.WriteRune`
   3, `utf8.DecodeRune` 3, `strconv.ParseInt` 2, `slices.Clone` 1,
   `slices.Compact` 1, `strconv.Quote` 1, `utf8.ValidRune` 1 (= 72), the
   remaining +20 declarations had two or more of these keys. One package
   moved −1 (`x/exp/schema/internal/json` 8 → 7): a new FR-7 finding,
   `return unmarshalRecordType(jt)` boxing a concrete result into the
   `ast.IsType` interface result — the emitter's exact condition
   (`IsInterface(target) && !IsInterface(comp)`), which the census's
   tool did not check.
5. **The static pass's first cut was wrong twice and the frontend
   corrected it** (kept here as the calibration record): (a) FR-17
   `x := f(x)` flagged selector members (`r.trk`) as reads — 8 phantom
   refusals on raft, 41 on cedar-go; the twin wire lowered every one;
   fixed to bare identifiers. (b) FR-18 flagged struct VALUE literals in a
   short-circuit RHS; the emitter hoists only slice/map literals and
   `&T{}` (`hoistSliceLit`/`emitMapLit`/`emitAddressOf`); fixed. Also
   `main.main` is never emitted (emit.go:131) and `init()` bodies are
   whole-export (no per-declaration quarantine) — both now mirrored.
6. **gotest**: `typeparam/list2.go` (refused on `fmt.Sprintf`'s verb
   matrix at the 2026-09-01 tip) is EXPORT OK and 41/41 today; the
   frontend is EXPORT OK on 8/10 — the run's FRONTEND-REFUSED verdicts
   for those came at RUN time from per-declaration stubs, which the
   static census now itemizes in advance.

## Gate (at the tree of the landing commit)

- `GO111MODULE=off go test ./tools/lowerdiag`: ok (11 tests, incl. the
  ledger check + red-first witness, determinism, the 5-cause fixture).
  `go vet ./tools/lowerdiag ./tools/cedarcensus ./tools/nativefrontend`: clean.
- `scripts/capped scripts/ci` (fast) in the fresh worktree: every step
  ok — frontend pins (twin wire = pinned bytes, so the stderr hint moved
  no pin), frontend unit tests, eval 148 ok, spec anchors, stdlib
  register, escape-hatch scans — EXCEPT the two baseline-diff steps,
  which FAIL CLOSED in a worktree with no recorded run ("NO recorded
  differential run"); hence the full `--diff` below rather than the
  no-diff escape. `gate/ci-fast-tail.txt`.
- `scripts/capped scripts/ci --diff`: **RESULT: PASS** (`gate/ci-diff-tail.txt`):
  differential baseline diff FULL, 3350/3350 rows match
  `baselines/native-full.tsv`, no regression, ZERO drift; negative
  baseline diff 394/394 match; frontend pins ok (twin wire = pinned
  bytes `69a538de…`, stdlib pin 61 files); frontend unit tests ok; eval
  148 ok; reconciler 3 findings, 0 HIGH. Zero drift is what a
  no-runtime-change lane must show: the frontend change is stderr text
  AFTER the refusal line, which the baseline diff does not compare (the
  `detail=` column carries it — a cosmetic re-pin diff later, said in the
  design doc §6). The run was recorded on the DIRTY lane tree (the gate
  notes say so): it certifies the worktree state at the run — the
  frontend/scripts/docs as committed; `tools/lowerdiag` received two
  later report-cosmetic edits (key fallback rendering) after the gate
  started and is NOT a gate input (no `scripts/ci` step builds or runs
  it); `go test ./tools/lowerdiag` was re-run green after them.
- `scripts/check-spec-anchors`: ok (732 spec# + 253 mem# + 26 godoc:
  resolve at the pin). `scripts/check-bugs.sh`: backlog 14 (10 coverage /
  4 latitude / 0 wrong-answer), unchanged.
- `tools/reconcile-records`: 4 findings, 0 HIGH — C13 and C5 pre-exist
  on main (the round-10 tail records "C13+C5 only"); the two new are LOW
  C6 dangling-id notes: `FR-24` (rowed on the unmerged `fr22-fr23`
  branch — the causes table carries the same `pending:fr22-fr23` status
  and its test flips to STALE when the row lands) and, before the
  reword, two placeholder tokens in the design doc (fixed).
