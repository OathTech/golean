# BUG-086 shim-injection dependency closure — red-first test, focused differential, pins, gate (2026-09-03)

[AGENT] lane `bug086-shim-closure`, executed inside the coordinator's
brief (the brief itself relayed the [USER]'s standing rules: D-002 shim
freeze — no new mechanism, no new shim, no shim body change; pin moves
are the [USER]'s call). Consuming docs: `docs/BUGS.md` BUG-086 (Status
line), `docs/discrepancy-backlog.md` D-002 (2026-09-03 note),
`baselines/native-full.tsv` header (the re-pin block),
`docs/language-coverage-ledger.md` §8 (post-vintage 85 → 83, total
196 → 194).

## What this is

The reproducibility trail for the BUG-086 repair: `injectStdlibShims`
(`tools/nativefrontend/stdlibshim.go`) planted a shim's SOURCE without
the other shim sources it calls, so a `strconv.FormatInt`-only program
died in the type-checker (`undefined: goleanShimStrconvFormatUint`).
The fix is plumbing: a declared per-shim dependency table
(`stdlibShimDeps`: FormatInt → FormatUint; fmtDyn → fmtBundle) closed
transitively by `closeShimDeps` before the reserved-name collision scan,
failing closed on a dep that names no shim source. No shim, no body, no
allowlist row changed.

Why the table and not the list-valued allowlist (BUG-086's fix shape
ii): a dependency is a property of the shim SOURCE, not of a call-site
row. One table, declared once, covers all four call-shape tables at one
site, and is CHECKABLE — `TestStdlibShimDepsExact` parses every shim
source and requires the set of other shims it references to EQUAL its
declared row (no missing dep = no BUG-086 shape; no stale dep = no dead
code planted).

## Artifacts

- `transcripts/red-first-per-entry-prefix.txt` — the per-entry closure
  test (`TestStdlibShimInjectionClosedPerEntry`: each of the 20 entries
  of the four injection tables planted ALONE, the shim file type-checked
  standing alone) run against main's PRE-FIX `stdlibshim.go` (787837ed):
  FAILS at exactly `strconv.FormatInt` with the two `undefined:
  goleanShimStrconvFormatUint` errors, and at no other entry — the
  noodler audit's "FormatInt is the ONLY unclosed entry" sweep result,
  confirmed mechanically (the noodler counted 27; this enumeration finds
  20 call-shape-table entries and 19 shim sources — the difference is
  the counting unit, not a missed entry).
- `transcripts/green-closure-tests-postfix.txt` — the four closure tests
  green on the fixed tree, then the whole `tools/nativefrontend` test
  package green.
- `transcripts/diff-one-formatint.txt` — focused differential on
  BUG-086's two Cases rows plus the two `strconv/format-parse` controls
  that call both functions: 4/4 PASS (the two born-FAIL rows flipped;
  the controls unmoved).
- `transcripts/check-frontend-pins.txt` — twin-wire pin UNMOVED
  (`eef32142627a…`) and the deviation pin unchanged. Expected:
  `raftsubject/quorum` calls FormatInt (`voteresult_string.go`) AND
  FormatUint (`quorum.go`) in one unit, so its bundle was already
  closed; the closure adds nothing there.
- `transcripts/gate-tail.txt` — the tail of the full
  `scripts/capped scripts/ci --diff` run on the lane's tree.

## Reproduction (from the repo root, on the lane's branch)

```
# red-first (pre-fix plumbing under the new test):
git show 787837ed:tools/nativefrontend/stdlibshim.go > /tmp/prefix-stdlibshim.go
cp tools/nativefrontend/stdlibshim.go /tmp/fixed-stdlibshim.go
cp /tmp/prefix-stdlibshim.go tools/nativefrontend/stdlibshim.go
GO111MODULE=off GOCACHE=$PWD/artifacts/go-build-cache go test ./tools/nativefrontend -run TestStdlibShimInjectionClosedPerEntry -v
#   (the other three closure tests reference the new table and do not
#    compile against the pre-fix file; the per-entry test is the red)
cp /tmp/fixed-stdlibshim.go tools/nativefrontend/stdlibshim.go
# green:
GO111MODULE=off GOCACHE=$PWD/artifacts/go-build-cache go test ./tools/nativefrontend -run 'TestStdlibShim|TestCloseShimDeps' -v
GO111MODULE=off GOCACHE=$PWD/artifacts/go-build-cache go test ./tools/nativefrontend
GO111MODULE=off GOCACHE=$PWD/artifacts/go-build-cache go vet ./tools/nativefrontend
# differential + pins + gate:
scripts/capped lake build
scripts/capped scripts/diff-one noodler/strconv-formatint/edges noodler/strconv-formatint/positive strconv/format-parse/format-int-vals strconv/format-parse/format-uint-bases
scripts/check-frontend-pins
scripts/capped scripts/ci --diff
```

## Toolchain, commit, host

- Go: `go version go1.26.5 linux/amd64` = `baselines/go-oracle-pin`.
- Lean: the repo's pinned toolchain via `scripts/capped lake build` in
  this worktree (fresh build, 60 jobs).
- Commit: main `787837ed` (the noodler landing that carries the two
  Cases rows and BUG-086) + this lane's working tree — the fix and the
  records were uncommitted when every transcript here was produced, and
  are committed together as the lane's single commit (its SHA is in the
  lane report; the gate certifies that working tree, not a commit).
- Host: linux/amd64, the shared build box; other lanes' worktrees
  present but no concurrent gate observed. Nothing here is timing-
  sensitive.

## Conclusion (2026-09-03)

The injection plumbing is now dependency-closed and the closure is
mechanized: FormatInt was the only unclosed entry, its two rows flip
FAIL → PASS with no other row moving, pins do not move, D-002's surface
is unchanged in size and meaning. GATE: see `transcripts/gate-tail.txt`
(recorded when the run finished — the line below is copied from it).

GATE RESULT: `scripts/capped scripts/ci --diff` RESULT: PASS — differential
3195/3195 no regression (3001 PASS / 194 FAIL), negative 394/394, re-pin
guard 0 PASS→non-PASS flips, exactly 2 non-PASS→PASS flips (BUG-086's
Cases rows), frontend pins ok (twin-wire `eef32142627a…` + deviation),
bug-index cross-check ok (87 bugs), frontend unit tests ok, reconciler 3
findings / 0 HIGH. Recorded on the dirty working tree (the gate's own
note); the tree was committed unchanged immediately after.
