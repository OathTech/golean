# Audit: train 20's workspace walk, module-file rules and the baseline union

2026-10-26 · independent [AGENT] auditor (Claude) · audited `stage/train-20-1026` at `6a65dd6f`
(six commits over `main` `6e05137a`). Branch `audit/train20-apparatus-1026`, worktree
`.claude/worktrees/audit20-app-1026`, `.lake` copied from the stage worktree at the same commit
(`lake build` inside the fast tier was replay-only), the stage's recorded corpus runs copied under
`artifacts/coverage/`. The oracle is the pinned gc go1.26.5 (`deps/go` is the same version's
source; gc's own rules are cited from it). No product file was changed. The reproductions are
beside this file under `2026-10-26-train20-audit-probes/apparatus/` (`modprobes.sh` judges 68
go.work/GOWORK/go.mod shapes on both sides and `modprobes.tsv` is its measured table; `machine.sh`
runs the machine on the wires whose gc answer moved; `nilleft/`, `signal/`, `hostile-ci/`,
`gowork-above/` and `baseline-union/` each carry a script and its measured output). Scratch
lived in `.tmp/` and is gone; the worktree stays, as asked.

**Verdict: ships, with one disposition first (F1) and one one-line pin worth taking in the same
train (F3).** Everything the train changed does what its commits say: the workspace refusal
agrees with gc's walk on every shape I could build (symlinks, a directory or dangling link named
`go.work`, parents with and without a `use`, syntax errors, missing `use` targets, every GOWORK
spelling), the toolchain rule agrees with gc on all 25 go.mod shapes tried except the pin's own
recorded over-refusals, the empty one-line block is accepted as gc accepts it, the `signal:`
refusal matches `go build`'s real child-death lines and nothing a gc diagnostic can end with, the
untyped-nil-left lowering matches gc on every operand kind including a type parameter, the
`GOWORK=off`/`GOFLAGS=` pins hold on every verdict-bearing leg of the gate under a hostile
environment, the gate's corpus survives a `go.work` above the checkout, and the baseline union is
exact. What is not right is a claim in the records: BUG-135's local-space survey says the one
thing the go command's env file could hide is an over-refusal, and that is false in the
direction that matters — two more of gc's configuration channels (the env file's `GOWORK`, and
`GOFLAGS=-modfile` in either place) move gc's answer while the frontend exports a clean wire
(F1). The apparatus is immune (it pins both in the process environment); a consumer is not, and
the docs tell them they are safe under "the same GOWORK".

## Findings

Severity as in the deep-clean pass and the train-19 shake review: P1 = fix before a release
relying on the claim; P2 = a concrete defect to fix or scope out; P3 = cleanup; info = recorded,
nothing to do.

### F1 — P2 — the env file's `GOWORK` and `GOFLAGS=-modfile` move gc's answer; the frontend reads neither, and BUG-135 says the gap is over-refusing only

What. `refuseWorkspace` (`tools/nativefrontend/modfile.go:536-552`) reads `os.Getenv("GOWORK")`
and otherwise walks for `go.work`. The go command reads GOWORK through `cfg.Getenv`, which
falls back to its env file (`$GOENV`, default `os.UserConfigDir()/go/env`) when the process
variable is unset; it also reads `GOFLAGS` from both places, and `-modfile=<file>` there makes
it read a different module file than `go.mod`. The frontend reads no `GOFLAGS`, `GOENV` or env
file anywhere (`grep -rn 'GOFLAGS\|GOENV\|UserConfigDir' tools/nativefrontend` is empty).

Reproduction (`modprobes.sh` cases w13, w27, w28; `machine.sh`; the probe is BUG-135's:
`probe()` recovers a `panic(nil)` and returns `recover() == nil`; go.mod `module test` /
`go 1.26`, clean):

| case | gc (module mode, GOTOOLCHAIN=local, GOPROXY=off) | frontend | machine on the wire |
|---|---|---|---|
| w13: no go.work in the walk; process GOWORK unset; `GOENV` file says `GOWORK=<abs path of a go.work elsewhere>` whose lines are `use <dir>` and `godebug panicnil=1` | exit 0, prints `true` | exit 0, wire written | `ok`, `false` |
| w27: process `GOFLAGS=-modfile=alt.mod`; `alt.mod` = go.mod + `godebug panicnil=1` | exit 0, `true` | exit 0, wire written | `ok`, `false` |
| w28: process GOFLAGS unset; `GOENV` file says `GOFLAGS=-modfile=alt.mod` | exit 0, `true` | exit 0, wire written | `ok`, `false` |
| w01 control | `false` | wire written | `ok`, `false` |

(The default env-file location is machine-global and was not touched; `GOENV=<file>` is the
same mechanism and is what the table uses.)

Where the record is wrong. BUG-135's local-space table (`docs/BUGS.md:9403`, the row for the go
env file) disposes the env file with the words that every variable the verdict depends on is
pinned by the apparatus and that the one case the file would hide is `GOWORK=off` there only,
an over-refusal; its GOFLAGS row says the frontend's side is not applicable. `docs/cli.md:80-85`
says the same and adds that a consumer must run gc and the frontend under the same GOWORK —
which does not cover w13 (GOWORK unset on both sides) or w27/w28 (not GOWORK at all).
`docs/release.md:191-192` repeats that GOWORK is honoured as the go command honours it.

Why it matters. The frontend is trusted surface #1 and the charter's fail-closed rule is about
the frontend's behaviour, not only the gate's. This is BUG-135's class — a wrong answer with a
clean export and status `ok` — through two more of the channels gc reads, found exactly where
the owner's standing instruction (investigate each fix's neighbourhood) pointed; the train-19
shake review rated the go.work instance P2. The exposure is bounded: it needs a non-default
`go env -w` setting or a `-modfile` flag, and the apparatus pins `GOWORK=off` and `GOFLAGS=` in
the process environment on every leg (verified below), so no baseline moves.

What to change. Either (a) read what gc reads — the env file named by `$GOENV` or at the
default location, for `GOWORK` and `GOFLAGS` lines, and the process `GOFLAGS` for `-modfile`
(and `-mod`, `-tags`, which also change what gc builds) — refusing by name on anything but
`GOWORK=off`/empty, the fail-closed direction and a few lines (the file is `KEY=value` per
line); or (b) correct BUG-135's table, `docs/cli.md` §1(b) and `docs/release.md` to state the
fail-open configuration gap as a limit. (a) is what the doctrine asks for; the owner decides.

### F2 — P3 — `GOWORK=auto` is refused; for the go command it is the same as unset

`cmd/go/internal/modload/init.go:365-376` (`FindGoWork`): `case "", "auto"` → the walk. The
frontend's switch (`modfile.go:538-543`) treats `auto` as a value that selects a workspace file
and refuses. Reproduction: w04 (`GOWORK=auto`, no go.work) — gc exit 0, frontend exit 1. An
over-refusal, the fail-closed direction, but unrecorded, and BUG-135 and `docs/cli.md:81`
claim GOWORK is honoured exactly as the go command honours it. Fix: treat `auto` as unset (one
more case label on the walk), or record the over-refusal.

### F3 — P3 — three `go` invocations the F7 sweep missed; one is on the gate's path

The commit message's F7 table and BUG-135's apparatus paragraph claim every `go` invocation of
`scripts/` and `tools/` carries `GOFLAGS=` and `GOWORK=off`. Three do not:

- `scripts/coverage-cause:233-236` — `go run ./tools/lowerdiag classify`, with an env of
  `GO111MODULE=off` and `GOCACHE` only. This is a GATE path: `judge_record` →
  `coverage-baseline-diff` → `coverage-cause`. Under an ambient GOFLAGS the differential
  baseline judgement REFUSES (exit 2, "could not derive the cause keys … NOT a no-drift result")
  and the gate goes red — the right direction, but the gate cannot judge, and the hostile run
  below shows it.
- `scripts/check-imported-goose:47-48` — the `go build` of `tools/lsimports` (a speedbump; red
  under the same environment).
- `scripts/choice-trace-corpus:121` — `go run ./tools/nativefrontend …` with no `GOFLAGS=` and
  no `GOWORK=off`, so it also runs the frontend without the pin: a go.work above the checkout
  reddens every export it makes (outside the gate).

Measured: `hostile-ci/run-ci-hostile.sh` — the fast tier under
`GOFLAGS=-toolexec=/nonexistent/toolexec GOWORK=/nonexistent/go.work` (any inheriting build
fails with `fork/exec /nonexistent/toolexec`; any module-mode go or unpinned frontend run sees
a missing workspace file). RESULT FAIL in 67 s with exactly one gate red — the differential
baseline diff's refusal through `coverage-cause` — and two speedbump reds (imported-goose,
`coverage-cause --unclassified`); every other step held: the oracle pin, both `go test`s, the
eval tests, unseq wire, wire boundary, method identity, frontend pins, declarations,
equations, the negative baseline diff, both re-pin guards (`hostile-ci/summary.txt`). Fix: the
two variables in `coverage-cause`'s env dict (one line), the export in the other two scripts,
and the "every invocation" wording in BUG-135.

### F4 — P3 (pre-existing on main; by the shake review's F2 standard a P2) — six go.mod shapes gc refuses that the module scanner exports

Not introduced by this train (the main-branch frontend, built from `6e05137a`, exports each one
too); found while testing the train's toolchain and empty-block rules, which themselves agree
with gc on every shape tried. Each: gc «errors parsing go.mod», exit 1; the frontend exit 0, a
wire written — a wire for a module gc will not build, the admission false green of the shake
review's F2 on exotic input.

| case | shape | gc's rule | the scanner |
|---|---|---|---|
| t11, t12 | U+00A0 (NBSP) between `module` and its path, or `go` and its version | x/mod `read.go:515` skips only space, tab and CR; `isIdent` (`:622-628`) rejects every other `unicode.IsSpace` rune → «unexpected input character» | `modfile.go:366` `strings.Fields` splits on every Unicode space, so the line reads `module test` |
| t29 | form feed (U+000C) in the same place | the same | the same (`\v`, t28, happens to refuse only because the whole file lands on one line) |
| t26 | `tool foo{bar` | `{`/`}` are not identifier runes → «unexpected input character» | `modfile.go:292-295` checks `tool`/`ignore` arguments for `[],` only |
| t27 | `replace a.b/c => ./x{y` | the same | `directoryPathOK` (`:252-254`) looks at the prefix only |
| t17, t18 | `require a.b/c v2.0.0`, `require a.b/c/v2 v1.0.0` | `module.CheckPathMajor` at parse (`rule.go:476`) | `modfile.go:288-291` checks path shape and semver shape separately, never their agreement |
| t36 | `require a.b/c v1.0.0+build.1` | canonical versions admit `+incompatible` only | `semverCanonicalRE` (`:227`) admits any build metadata |

Fix: refuse any rune outside x/mod's identifier set before splitting, mirror `CheckPathMajor`,
restrict metadata to `+incompatible` — or negative rows for each (the negative runner's
frontend leg does FAIL a row at `frontend-accepts`, `scripts/coverage-negative:289,395`, so
rows would pin them).

### F5 — info — baseline record hygiene

- The frontend lane's header block (`baselines/native-full.tsv`, the BUG-136 block) says its
  measurement was at lane commit `aee99b3d`. That commit exists only on
  `frontend/workspace-and-oracle-1026`; the stage carries it rebased as `6ce62599`. Once the
  lane branch is deleted the citation dangles. The core lane's block names no commit.
- The header carries two `# cases:` lines: line 2 (live, `4157 (3896 PASS / 261 FAIL)`) and
  line 2245 (a 2026-09-05 history note, pre-existing). No script checks the live count against
  the rows (`coverage-baseline-diff` never reads it); I did by hand — it is right (below).
Nothing to do unless the owner wants the citation to name the stage commit.

## What was checked and found sound

**The workspace walk vs gc's** (`modprobes.sh` w01–w25; `findGoWork` `modfile.go:505-525` vs
`findWorkspaceFile` `modload/init.go:1709-1731`). Both walk the logical path (`filepath.Abs` on
the frontend's side, `base.Cwd()` = `$PWD` on gc's), so the two symlink shapes agree: a symlink
INTO a workspace (w10: logical parents clean, physical parent has go.work) — gc builds, the
frontend exports; a symlink FROM a workspace directory (w11) — gc applies the workspace
(`true`), the frontend refuses. A regular-file symlink named go.work is a workspace for both
(w16); a dangling one is nothing for both (w17); a directory named go.work is skipped by both
(w20 — the lowered directory itself so named). A go.work with syntax errors (w06), one whose
only `use` is missing (w07), one above a directory with no go.mod (w24), one beside a directory
with no go.mod (w23), a parent go.work that does not `use` this module (w09), a `go 1.26.6`
floor (w18): gc refuses each with its own reason, the frontend refuses by name. A parent go.work
that does `use` this module (w08) and a go.work beside with or without godebug (w02, w03): gc
accepts (and w03 prints `true`), the frontend refuses — the recorded over-refusal. Every GOWORK
spelling gc rejects — relative (w22), a directory (w19), a trailing slash (w25), `OFF` (w14) —
both refuse; `GOWORK=off` with a godebug go.work beside (w21): both ignore it, the machine and
gc both `false`. The GOROOT stop is not mirrored, as stated; no input of this frontend is inside
a GOROOT. GOPATH mode (w15): gc does ignore go.work there (a distinctive `godebug
asynctimerchan=0` in the go.work does not reach `go list -f '{{.DefaultGODEBUG}}'` under
`GO111MODULE=off`, and does under `on`) — gc's `true` on that row is GOPATH mode's own go1.16
godebug defaults (`panicnil=1`), the limit `docs/release.md:185-188` already states and the
positive oracle's `GODEBUG=panicnil=0` pin covers.

**The toolchain rule** (`judgeToolchain` `modfile.go:468-493` vs `modload/init.go:1929`). The
task's edge forms and more, t01–t10, t13–t16, t19–t21, t25, t28, t30, t37–t40: textually equal
(`go 1.26.5` + `toolchain go1.26.5`) — gc «updates to go.mod needed», frontend refuses with that
reason; `go 1.26` and `go 1.26.0` under the pin — both accept; `go 1.27` — gc «requires go >=
1.27», frontend's language refusal; `toolchain default` — both refuse; the toolchain line before
the go line — both accept; two toolchain lines — both refuse; extra spaces, a trailing comment,
a tab, CRLF, comments on both lines, a trailing space — both accept; `toolchain go1.26.5 extra`,
`GO1.26.5`, a BOM, a vertical tab, U+2028 in a path — both refuse; `go1`, `go1.26.5.1`,
`go1.26.5rc1` — gc drops and refuses, the frontend refuses. The pin's recorded over-refusals:
`go1.26.5-custom` (a named toolchain gc keeps and, under `GOTOOLCHAIN=local`, ignores — t14),
`godebug ()` (t30, BUG-128), a toolchain line with no go line (t20: gc builds at the go 1.16
language and prints `true` — the BUG-109 shape, rightly refused). The negative row
`modules/toolchain-redundant` is in the recorded run as PASS at `frontend=module`.

**The empty one-line block** (`modfile.go:419-424`): `require ()`, `require (` newline `)`,
`require ( // c` newline `)` — both accept (t22–t24); a one-line block with a body and
`module ()`/`go ()`/`toolchain ()` refuse on both (the unit tests cover them; 73 subtests pass,
`go test ./tools/nativefrontend`).

**The untyped-nil-left lowering** (`emit.go:8693-8705`, `isUntypedNilType` `:8729-8733`;
`nilleft/`). Twelve `println` lines over `nil == p`/`p == nil`/`!=` for pointer, map, slice,
func, chan, `any`, `error`, a struct's pointer field, a non-nil pointer, a method value and a
non-nil error, a `(<-chan int)` conversion, a type parameter `[T ~*int]` (both spellings), a
tagless `switch` with `nil != p`/`nil == p` cases, a short-circuit chain, a nested
`(nil == p) == (p == nil)`, and a `for nil == p` condition: gc and the machine identical
(`nilleft/gc.txt` = `nilleft/machine-tip.txt`); the main-branch frontend's wire is
`frontend-quarantined: basic type untyped nil` (`machine-base.txt`). `nil == nil` is a go/types
error on both sides, as BUG-136 says.

**The `signal:` non-verdict** (`scripts/coverage-negative:385`; `signal/measure.sh`). A
`-toolexec` wrapper that kills itself makes `go build` print `go: error obtaining buildID for go
tool compile: signal: killed` / `signal: terminated` / `signal: segmentation fault (core
dumped)`, exit 1, in module and GOPATH mode; the regex matches each (`signal/measured.txt`). A
false red needs a line ending `: signal: <lowercase words>`: gc's diagnostics end with a user
identifier (no `: `), a quoted literal (closing quote), a type, or fixed text — none reaches the
pattern; no negative-corpus expected substring mentions `signal`. The positive runner's claim
holds: `go run` of a program that SIGKILLs itself prints `before` / `signal: killed`, exit 1,
with no `exit status N` trailer, which `tools/coverageharness/split.go:36-49` refuses by name.

**The pins on every oracle path the gate takes** (`hostile-ci/`). Listed above under F3: every
verdict-bearing step held under `GOFLAGS=-toolexec=/nonexistent/toolexec
GOWORK=/nonexistent/go.work`; the only reds are F3's three unpinned invocations, and the gate
failed closed (a refusal, not a verdict). `go version` under that GOFLAGS still answers (the
oracle pin step passed).

**A `go.work` above the repository** (`gowork-above/setup.sh`, `run.sh`, `results.txt`). A
symlinked view of the worktree under `.tmp/ws/go.work` (`go 1.26` / `godebug panicnil=1`, no
`use`): from the view, module-mode gc without the pin answers `go env GOWORK` with that file and
refuses «no modules were found in the current workspace»; the frontend without the pin refuses
the row directory by name. With the runners' own pins: the negative corpus 426/426 PASS (30 s);
a positive subset of six rows — the two nil-left rows, a struct-through-conversion row,
`directives/debug-panicnil`, `noodler/defers/panic-nil-recovered`,
`panic-recover/repanic-collapse/nil-passthrough` — reproduces its baseline rows exactly (five
PASS, `debug-panicnil` FAIL at `frontend-export`, the BUG-127 red-by-design pin). The full
positive corpus was not re-run (the stage's recorded run at the tip is judged below).

**The baseline union** (`baseline-union/check.sh`, `results.txt`). `baselines/native-full.tsv`:
4089 main rows all present byte-identically (0 missing or altered), 68 appended (60 + 8), no
duplicate id, `# cases: 4157 (3896 PASS / 261 FAIL)` = the rows (3896 + 261), the only header
line of main changed is the count line, each appended id is named in a header reason block
and no named id lacks a row; the core lane's block is byte-identical to its lane's commit
(`584adb0f` vs stage `8c87b3ce`: 0 diff lines) and the frontend lane's likewise (only the count
line and the core block differ between `fcb2de87` and the tip); each block's own arithmetic
(4089 + 60, 4089 + 8) is per lane and honest. `baselines/negative-full.tsv`: 425 kept, one
appended (`modules/toolchain-redundant`), `426 pass: 426 fail: 0`. The re-pin guards
`check-row-removals`, `check-cause-regressions`, `check-alternation-survival` pass against
`main` for both files (the tier's own guard compares HEAD with HEAD~1 only, so I ran them
against main). The recorded runs: `latest.tsv` 4157/4157 and `negative-latest.tsv` 426/426 match
the baselines with no regression, every FAIL cause classified, meta `git_commit` = `6a65dd6f`,
`git_dirty` false, oracle `go1.26.5` with no drift, `manifest_sha256` equal to the manifest
regenerated from the current corpus. `scripts/check-bugs.sh` ok (136 bugs; BUG-135's absent
`- Cases:` line is explained in its entry; BUG-136's eight Cases are live PASS rows).

**Not done.** No full `scripts/ci --diff` (the stage's run at the tip is the record judged);
no run against the default env-file path (machine-global); the `vendor/`, `go.sum`,
`GOOS`/`GOARCH` rows of BUG-135's survey were read, not re-measured.

## Dispositions asked of the owner

1. F1: fix (read the env file and `GOFLAGS` for `GOWORK`/`-modfile`, refuse by name) or record
   the fail-open limit in BUG-135, `docs/cli.md` and `docs/release.md`; the audit's view is that
   the records cannot ship saying the gap is over-refusing only.
2. F3: the one-line pin in `scripts/coverage-cause` in this train; the other two and the
   wording with it or after.
3. F2, F4: backlog rows, or negative rows for F4's shapes.
