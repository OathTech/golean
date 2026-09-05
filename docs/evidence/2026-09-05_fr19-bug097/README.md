# FR-19 / BUG-097 / BUG-059 — identity vs display: probes, transcripts, twin re-pin, gate (2026-09-05)

[AGENT] lane `fr19-bug097`, worker under the relayed [USER] standing
directions (break incorrect behaviour rather than preserve it; fail
closed with the cause named; every detected gap rowed with a plan;
gc-visible texts byte-exact). Design of record:
`docs/2026-09-05_fr19-bug097-design.md`. Consuming records: `docs/BUGS.md`
(BUG-097, BUG-059, BUG-092 fixed; BUG-018 addendum; BUG-098 filed),
`docs/language-coverage-ledger.md` (FR-19 closed, FR-31 rowed, §5.1 item
1 narrowed, §8p), `docs/2026-09-03_cedar-go-coverage-census.md` §13,
`docs/2026-08-18_multipackage-identity.md` §3 (residue retired),
`baselines/native-full.tsv` header, `scripts/check-frontend-pins` re-pin
history.

## Conclusion

One defect seen from three sides: the machine rendered `TypeId.key`
verbatim, so identity (path-qualified, scope-blind) and display (gc's
package-NAME string) could not both be right. The wire now carries both
— `display`/`pkg` REQUIRED on every TypeDef, the machine renders the
record and decides by the key — and the key gained what identity needs:
a scope ordinal for function-local types (`main.L·1`/`·2`) and an
injective anonymous-interface spelling minted by one constructor
(path-qualified named types AND unexported method names; gc's method
order). Eight rows flip FAIL→PASS (BUG-097's witness, BUG-059's witness,
FR-19's two noodler pins, BUG-092's three cmp/SortFunc rows,
`generics/local-type-argument`); 18 rows are born (15 PASS, 3 red by
design: C6's remaining shape, and the two BUG-098 guard rows). Zero
PASS→non-PASS. The raft twin re-pins: `quorum.MajorityConfig.Describe`,
an H-3 stub since the cmp retirement, lowers (its local `tup` is a
function instantiation's argument now), and every TypeDef gains its
display record.

Found on the way and NOT hidden: gc keys unexported method names by
package while the wire's method tables carry bare names (BUG-098). Before
this lane the shape was refused by accident (the two anonymous
interfaces fused onto one key and tripped BUG-095's conflict guard);
with distinct keys the machine would answer `true true` where gc says
`true false`. A whole-export guard refuses it by name; the fix is rowed
(FR-31). Its measured cost on cedar-go: the `x/exp/schema/ast` package
the census counted as lowering is a latent wrong-answer class and is now
an honest red (memo §13).

## gc oracle (go1.26.5 linux/amd64 = `baselines/go-oracle-pin`)

`gc-probes.txt` — the transcripts of five probe programs, run with the
pinned toolchain in GOPATH mode (`gc-probe-*.go`; `gc-probe-p2-inner.go`
is the `red/inner` = `blue/inner` package source, identical under both
paths):

* P1 — single package: named/anonymous/local types in every
  `interface conversion:` shape (missing-method, nil, concrete target,
  composite targets); `scopes.go` = the same-named local types of two
  functions (`(types from different scopes)`).
* P2 — `red/inner` + `blue/inner`: same package NAME, distinct paths
  (`(types from different packages)`; `interface { Get() inner.T }`;
  unexported `inner.get`).
* P3 — `go/types.TypeString` qualification: unexported interface METHOD
  names are never qualified, even with a qualifier (why the
  anonymous-interface key needs its own renderer, and BUG-098).
* P4 — gc type strings: instantiation brackets (PATH-qualified,
  `LinkString`), the `·N` local-type counter (`score·1`, `other·2`,
  `score·3`: per-package), anonymous struct/func/chan spellings.
* P5 — the unexported single-method shape across packages (`true false`;
  `inner.T is not interface { inner.get() int }: missing method get`),
  and `%T`/`Name()` of an instantiation over a sub-path type
  (`main.Pair[red/inner.T]` — the bracket keeps the path, so the
  observation channel needed no change).

The gc source read for the rules: `deps/go/src/cmd/compile/internal/types/fmt.go`
(`tconv2`, `pkgqual`, `NameString`/`LinkString`), `noder/writer.go:1013`
(`decl.gen`), `noder/reader.go` `mangle`, `reflectdata/reflect.go:480`
(`NameString` is the runtime type string), `types/sym.go` `CompareSyms`.

## Machine tier

* fixed: this lane's worktree at the commit carrying this README
  (frontend `tools/nativefrontend`, binary from `scripts/capped lake
  build`; Lean toolchain = the repo's `lean-toolchain` pin).
* `diff-one-round1.log` — the first focused run (29 ids): 21 PASS / 8
  FAIL. Of the 8: `shadow-panic` was a FIXTURE bug (the local type had no
  `Get`, so the text was the missing-method form — fixed by asserting to
  the package-level type from a package-level helper); four C6 refusals
  on FUNCTION instantiations were a FRONTEND bug in the first cut
  (`qualifiedTypeName` parameterized a stencil's own local type ARGUMENT
  as if declared inside the stencil — `curInstDecl` /
  `declaredInActiveStencil` fixed it; BUG-018 addendum); two were the
  BUG-098 wrong answer, measured before the guard (then
  `same-name-anon-iface-panic/unexported-distinct`, since moved to
  `multipkg/unexported-method-scope/distinct`: Lean `true true`, Go
  `true false`); `type-instantiation-refused` is red by design.
* `diff-one-round2.log` — the re-run of the 11 affected ids after the
  fixes: 8 PASS / 3 FAIL by design (`type-instantiation-refused` C6;
  the two unexported-method rows on the BUG-098 guard). The first FULL
  gate then showed two more findings, both fixed before the re-pin: the
  atomics shadow models' TypeDefs (harvested from a fresh emitter) had
  no host display record (17 atomics/race rows refused — the attach pass
  now accepts and registers the harvested record), and gc's `panicwrap`
  text is SYMBOL-derived (path-qualified), so it renders the key, not
  the display (`multipkg/nil-value-method-text`); and the BUG-098 guard,
  being whole-export, took `same-name-anon-iface-panic/{missing,source}`
  down with the unexported rows — those rows moved to their own case
  dir `multipkg/unexported-method-scope`.
* `gate-tail-run2-before-repin.txt` — the second full `scripts/capped
  scripts/ci --diff` (the run the re-pin is derived from: every step ok
  except the baseline DRIFT it exists to measure, and `bug-index
  cross-check`, which reads the not-yet-re-pinned baseline);
  `gate-tail.txt` — the fast gate at the lane tip after the re-pin.

## Twin re-pin

`twin-repin/structural-diff.txt` — JSON diff of the pinned twin wire vs
the fresh emit: 92 TypeDefs gain `display`/`pkg` (def bytes identical),
`quorum.tup·1` born, 20 funcs born (Describe's literals + fmt shim, the
`slices.SortFunc`/pdqsort family at `[quorum.tup·1]`, `cmp.Compare`
at `quorum.Index` and `uint64`, `cmp.isNaN[quorum.Index]`),
`quorum.MajorityConfig.Describe` stub → body, and 208 funcs / 203
methods that differ ONLY by program-wide temporary renumbering (3214 +
2802 leaf changes, all `$cN/$swfN/$swiN/$tsN`, 0 other). 0 removed, 0
globals. `baselines/pins/twin-chdriver.wire.json` re-pinned 4ee39f73… →
f89e1c9e…; history in `scripts/check-frontend-pins`.

## cedar-go census

`cedar-lower-diagnose-report-after.txt`, `cedar-histogram-after.tsv` —
the static pass after the change (before = memo §12.2, unchanged tree).
Summary in memo §13: `nodeJSONAlias` (FR-19) gone, `cedargo/internal/json`
lowers; the BUG-098 guard kills `x/exp/schema/ast` (17 declarations) —
1460/1569 → 1443/1569 declarations demanding nothing refused, export
kills 2 → 17 declarations, 5 → 8 of 24 packages.

## Gate

Full run 2 (`.tmp/ci-diff-2.log`, tail in `gate-tail-run2-before-repin.txt`):
`differential coverage summary: cases=3516 pass=3275 fail=241`; drift vs the
tracked baseline = EXACTLY the predicted set — 8 FAIL→PASS flips
(`generics/local-type-argument`, `multipkg/same-name-anon-iface`,
`multipkg/same-name-identity-panic`, `noodler/local-types/{distinct,shadow}`,
`slices/sortfunc-cmp/{cmp-compare-kinds,sortfunc-local-type}`,
`stdlib-source/cmp-compare/local-float-type`), 0 PASS→non-PASS (re-pin
guard clean), 18 born (15 PASS, 3 FAIL by design), 0 rows gone; negative
lane 394/394 unchanged; twin pin = fresh emit; eval tests 161 ok. Baseline
re-pinned 3498 = 3252 / 246 → 3516 = 3275 / 241 (header block; tallied by
row). Full run 1 (before the shadow-model / panicwrap / fixture-split
fixes) is the record of the three findings above: 17 atomics/race rows
and `multipkg/nil-value-method-text` PASS→FAIL, `same-name-anon-iface-panic/{missing,source}`
born FAIL — none of it survives to the re-pin.
