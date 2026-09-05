# FR-19 / BUG-097 / BUG-059 — identity vs display: probes, transcripts, twin re-pin, gate (2026-09-05)

[AGENT] lane `fr19-bug097`, worker under the relayed [USER] standing
directions (break incorrect behaviour rather than preserve it; fail
closed with the cause named; every detected gap rowed with a plan;
gc-visible texts byte-exact). Design of record:
`docs/2026-09-05_fr19-bug097-design.md`. Consuming records: `docs/BUGS.md`
(BUG-097, BUG-059, BUG-092 fixed; BUG-018 addendum; BUG-098 filed),
`docs/language-coverage-ledger.md` (FR-19 closed, FR-31 rowed, §5.1 item
1 narrowed, §8s), `docs/2026-09-03_cedar-go-coverage-census.md` §13,
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
  and `%T` of an instantiation over a sub-path type
  (`main.Pair[red/inner.T]`). The reflect `Name()`/`String()` line
  (`Name()="Pair[red/inner.T]" String()="main.Pair[red/inner.T]"`) was
  ADDED and re-run at the audit fix round R15 — the first README, the
  design note §3.3 and BUG-059 credited P5 with a `Name()` observation
  it did not yet make; the bracket keeps the path, so the observation
  channel needed no change. P3 re-recorded at R22 (Defs iterated in
  name order; byte-reproducible).
* R3 probe (`gc-probe-r3-recovered-runtime-error.go`, run at the audit
  fix round; transcript in the "Audit fix round" section below) — the
  dynamic type of a RECOVERED runtime error on both sides.

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
the fresh emit, produced by the TRACKED `twin-repin/twin-structural-diff.py`
(audit fix round R12; the first diff came from an untracked inline
script that omitted the methodSets section): 92 TypeDefs gain
`display`/`pkg` (def bytes identical), `quorum.tup·1` born (type AND
method-set record, 81 → 82 records), 20 funcs born (Describe's literals
+ fmt shim, the `slices.SortFunc`/pdqsort family at `[quorum.tup·1]`,
`cmp.Compare` at `quorum.Index` and `uint64`, `cmp.isNaN[quorum.Index]`),
`quorum.MajorityConfig.Describe` stub → body (the un-quarantine the
re-pin carries: an H-3 stub since the cmp retirement), and 208 funcs /
203 methods that differ ONLY by program-wide temporary renumbering
(3214 + 2802 leaf changes, all `$cN/$swfN/$swiN/$tsN`, 0 other). 0
removed, 0 globals, fileOrder identical. `baselines/pins/twin-chdriver.wire.json`
re-pinned 4ee39f73… → f89e1c9e…; history in `scripts/check-frontend-pins`.
Reproduce: `git show b77f3298:baselines/pins/twin-chdriver.wire.json >
old.json; python3 twin-repin/twin-structural-diff.py old.json
baselines/pins/twin-chdriver.wire.json`.

## cedar-go census

`cedar-lower-diagnose-report-after.txt`, `cedar-histogram-after.tsv` —
the static AND dynamic pass after the change (before = memo §12.2,
unchanged tree), RE-RUN at the audit fix round R8 (the first copies
labelled the cause FR-29 from a pre-rename `causes.tsv`; the row is
FR-31). Summary in memo §13: `nodeJSONAlias` (FR-19) gone,
`cedargo/internal/json` lowers; the BUG-098 guard kills
`x/exp/schema/ast` AND `x/exp/schema/resolved` symmetrically (17
declarations, 6 more packages inherit) — 1460/1569 → 1443/1569
declarations demanding nothing refused, export kills 2 → 17
declarations, 5 → 8 of 24 packages. The DYNAMIC first refusal is the
report's first line: the whole-library `all` case, which EXPORTED
before (557 quarantined), now REFUSES whole-export on the guard — the
first README/design/census said it still exported (withdrawn at R2).

## Gate

FINAL (audit fix round R18): `gate-tail.txt` is the FULL `scripts/capped
scripts/ci --diff` at the CLEAN committed tip 9296512f — every step ok,
`baseline diff FULL (3523/3523, no regression)`, `negative baseline diff
(no regression)` (394), `re-pin guard (0 PASS→non-PASS flip(s))`,
`eval tests (179 ok)`, reconciler 3 findings / 0 HIGH (the pre-existing
MEDIUM C13/C5/C9), RESULT: PASS; both run records carry
`git_commit 9296512f… git_dirty false` (the file reproduces them). The
first attempt at this run (882d4d23) went dirty mid-run because the
worker edited records while it ran — discarded, not recorded; the lane's
earlier `gate-tail.txt` (fast gate, `git_dirty=true`) is replaced.
`differential coverage summary: cases=3523 pass=3279 fail=244` = the
tracked baseline, tallied by row.

Lane landing, for history — full run 2 (`.tmp/ci-diff-2.log`, tail in `gate-tail-run2-before-repin.txt`):
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

## Audit fix round (2026-09-05, [AGENT]; verdict FIX-FIRST, findings R1–R22)

Every finding applied or recorded-owed; the disposition table is in the
round's commit messages and the design note §7. The measurements the
round produced:

* **R1 (BLOCKER) — `*T` pkgpath.** Auditor's reproducer `.tmp/audit/p/V`
  (gc: `*inner.P … (types from different scopes)`, `*inner.Q`/`*inner.R`
  `… (types from different packages)`, `inner.S` packages, `[]inner.Q`
  scopes). Fixed in `typePkgForMessage` (gc's uncommon-section rule;
  refuses where the wire cannot decide); corpus
  `multipkg/same-name-pointer-panic/{no-methods,value-method,pointer-method,slice-control}`
  all PASS (`diff-one`, 11/11 with the display pins re-run).
* **R3 / R20 — the recovered runtime error's type**
  (`gc-probe-r3-recovered-runtime-error.go`; gc / frontend / machine):

      gc:      runtime error: index out of range [3] with length 0
               interface conversion: interface {} is runtime.boundsError, not int
               true
      machine: assertRecoveredToInt  -> unsupported: "type-assertion panic text names the dynamic type of a
                 recovered runtime error, which the machine models as one synthetic id ($runtime.Error) …"
               recoveredAsAny       -> ok: {"dynamic":"Error","tag":"interface","value":{"tag":"string",…}}
                 (gc's observation: {"dynamic":"boundsError","value":{"tag":"struct","typeName":"boundsError",
                  "fields":[x=3,y=0,signed=false,code=0]}} — a WRONG ANSWER, differential red)
               recoveredErrorText   -> unsupported: "interface satisfaction for <runtime error payload: gc's
                 concrete type (…) is not modeled — one synthetic $runtime.Error id, BUG-009/BUG-053 class>: …"

  Filed as **BUG-099** (open, Pinned-by differential) with the two rows
  `panic-recover/recovered-runtime-error-type/{observed,assert-int}`;
  the design note's "unreachable" claim for the no-record marker is
  corrected; `displayNameOf` renders the cause-naming marker.
* **R4 — BUG-098's pre-lane truth is shape-dependent.** New row
  `multipkg/unexported-method-scope/distinct-names` (`type S struct{
  emb.E }` vs main's `interface{ get() int }`; gc `false`) refuses
  under the guard by design; the entry now says main answered WRONG on
  this shape and refused by accident only on the same-name one.
* **R2 / R8** — the cedar re-run (below, this round's report) shows the
  `all` case refusing whole-export; labels FR-31.
* **R5 / R6 / R7** — Go tests for the three emitter refusals
  (`identity_test.go`), Lean tests for the required `display`/`pkg`
  fields (missing → refuse naming the field; `""` accepted) and for the
  new `program.types` duplicate check (`Tests/GoCoreEval.lean`).
* **R11** — `keyPathHazard`: non-ASCII / `%` / `"` / control bytes in
  an import path refuse at the minting boundary by name (gc's
  `PathToPrefix` escaping); unit-tested.
* **R12 / R13** — structural diff regenerated with the methodSets
  section from a tracked producer; the un-quarantine of
  `quorum.MajorityConfig.Describe` written into the design §5.
* **R19** — the C6 pin `scoping/local-type-identity/type-instantiation-refused`
  is guarded by **BUG-100** (`Pinned-by: none`, `Expect: FAIL` — the
  repo's mechanism for red-by-design pins; no ledger-backed check
  exists).
* **R18** — the gate tail below is from the CLEAN committed tip
  (`git_dirty=false`), the full `--diff` run, not a grep'd line.

