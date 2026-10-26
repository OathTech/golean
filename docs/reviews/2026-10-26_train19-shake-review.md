# Review: train 19 shaken — core and apparatus changes before release

2026-10-26 · independent [AGENT] reviewer (Claude) · reviewed `main` at `6e05137a`
(train 19 = `7739cf9f..e7d990bf`, thirteen commits; its pre-merge audit was waived).
Branch `review/train19-1026`, worktree `.claude/worktrees/review-train19-1026`, `.lake`
copied from the primary at the same commit (`capped lake build` there was a no-op: 70 jobs,
replay-only; `scripts/check-kernel-replay` PASS, 55 modules). No product file was changed.
The reproductions are beside this file under `2026-10-26-train19-probes/` (each `main.go`
is a Go program; `run-both.sh` runs gc and the machine on it; `run-modfile.sh` judges the
go.mod shapes on both sides). Scratch outputs lived in `.tmp/` and are gone.

**Verdict: ships, with two changes first (F1, F2) and one to decide (F3).** No wrong answer
was found in what train 19 fixed; the fixes close their classes where I could probe them
(pointer identity, deadlock classification, seed budgets, the negative oracle's status, the
locale). Two defects sit in the local space of the fixed classes and are the kind the
owner's standing instruction (investigate the neighbourhood of each fix) was meant to catch:
a `go.work` the frontend never reads changes gc's meaning of a program the frontend exports
with a clean export (F1, a wrong answer with status `ok`), and a `toolchain` line the
frontend accepts that gc refuses to build (F2, an admission false green). Both are in the
frontend's module admission, outside the differential corpus's sight (its positive lane runs
gc in GOPATH mode, where neither file is read), so no baseline sees them.

## Findings

Severity as in the deep-clean pass: P1 = fix before a release relying on the claim; P2 = a
concrete defect to fix or scope out; P3 = cleanup; info = recorded, nothing to do.

### F1 — P2 — a `go.work` `godebug` line changes gc's answer; the frontend does not read go.work

What. `tools/nativefrontend/modfile.go` judges the nearest `go.mod` (`findGoMod`, line 99;
`refuseForeignModuleVersion`, line 383) and refuses a `godebug` line there by name (BUG-128).
The go command also reads `go.work` (found the same way, walking up), and since Go 1.23 a
`godebug` line in `go.work` applies to the workspace's main modules. The frontend has no
mention of `go.work` or `GOWORK` anywhere (`grep -rn 'go\.work\|GOWORK' tools/nativefrontend`
is empty), so it exports the program unchanged.

Reproduction (`2026-10-26-train19-probes/dc06-modfile/gowork-godebug/`: `go.mod` =
`module test / go 1.26`, `go.work` = `go 1.26 / use . / godebug panicnil=1`, and `probe()`
recovers a `panic(nil)`):

```
cd docs/reviews/2026-10-26-train19-probes/dc06-modfile/gowork-godebug
GO111MODULE=on GOFLAGS= GOPROXY=off GOSUMDB=off GOTOOLCHAIN=local go run .      # prints: true
GOWORK=off GO111MODULE=on GOFLAGS= GOPROXY=off GOSUMDB=off GOTOOLCHAIN=local go run .   # prints: false
.tmp/nativefrontend --dir docs/reviews/2026-10-26-train19-probes/dc06-modfile/gowork-godebug --out .tmp/w.json   # exit 0
.lake/build/bin/golean native-json-run --input .tmp/w.json --function probe
{"output":"","schema":"golean-observation-v1","status":"ok","values":[{"tag":"bool","value":false}]}
```

gc with the workspace in scope: `true`; the machine: `false`, status `ok`, no refusal.
The same `godebug` line in `go.mod` instead of `go.work` is refused by name (BUG-128; checked:
`native frontend unsupported: module directive: …`).

Why it matters. This is BUG-128's class through the other file the go command reads: a
meaning-changing setting in the tree that the lowering silently ignores, giving a wrong answer
with a clean export. It is outside the corpus's sight: the positive lane runs gc under
`GO111MODULE=off`, where go.work is ignored; the negative lane's new module-mode leg would
honour a go.work (it does not set `GOWORK`), but no row carries one. The `toolchain` line of a
go.work is the same shape (inert under `GOTOOLCHAIN=local`, a switch under `auto`).

What would close it. The frontend refuses by name when a `go.work` is in scope for the lowered
directory or any case-local package (the fail-closed direction, matching the quoted-token and
`module (` refusals), or reads and judges it (its `godebug`/`toolchain` lines under the go.mod
rules); and the negative runner's module leg pins `GOWORK=off` so a go.work above the tree
cannot alter the oracle's verdict on a box (consistent with the refusal). A negative row with a
go.work beside its go.mod would then pin gc's and the frontend's agreement.

### F2 — P2 — `go 1.26.5` + `toolchain go1.26.5` is accepted by the frontend and refused by gc

What. `modfile.go:329` accepts a `toolchain` directive exactly when it names the pinned
toolchain. gc's rule is different: a `toolchain` line that is not above the `go` line is
redundant, and `go build` under the default `-mod=readonly` refuses to build until it is
removed.

Reproduction (`dc06-modfile/pin-toolchain/go.mod` = `module test / go 1.26.5 / toolchain
go1.26.5`):

```
cd docs/reviews/2026-10-26-train19-probes/dc06-modfile/pin-toolchain
GO111MODULE=on GOFLAGS= GOPROXY=off GOSUMDB=off GOTOOLCHAIN=local go build -o /dev/null .
go: updates to go.mod needed; to update it:
	go mod tidy                                      # exit 1
GOFLAGS=-mod=mod … go build .                            # exit 0, and go.mod is rewritten WITHOUT the toolchain line
.tmp/nativefrontend --dir . --out /dev/null              # exit 0: exported
```

The controls agree on both sides: `go 1.26 / toolchain go1.26.5` (gc 0, frontend 0),
`go 1.26.5` alone (0, 0), `go 1.26 / toolchain default` (gc 1 for the same reason, frontend 1
by its own rule).

Why it matters. It is the exact class DC06 closed (FE-03: the frontend exporting a go.mod gc
refuses — the negative runner would record it as `frontend-accepts`), reachable with the pinned
toolchain name the scanner's comment calls accepted. The program's meaning is unchanged, so
this is an admission false green, not a wrong answer.

What would close it. Accept `toolchain T` only when the module's `go` version (complete form)
is below `T` — gc's own condition — and refuse the redundant form by name; a negative row
`modules/toolchain-redundant` pins it.

### F3 — P3 (owner's call) — DC11's classification did not reach the enumeration driver

What. The pool's deadlock arm is now `deadlockOrRefusal` in `execProgLoop`,
`execProgLoopOut` (`Multi.lean:1995, 2049`), the proofs' `PoolFacts.front` and the
choice-trace mirror (`ChoiceTrace.lean:779`). The CLI's own mirror of `execProgLoop` for the
membership lane, `enumPoolRun` (`GoLean/CLI.lean:1884–1885`), still reads

```lean
if (GoCore.Machine.runnableIdxs pctx m.shared m.threads).isEmpty then
  throw (.deadlock, acc)
```

with no `parkedWellFormed`. `docs/BUGS.md`'s DC11 paragraph names the drivers the change
covers and this one is not among them. (The DFS driver at `CLI.lean:2304` and the dedup engine
at `EnumDedup.lean:196` refuse any empty-runnable state loudly, so they are not affected.)

Why it matters. In the enumeration lane a deadlock member is refused upstream anyway
(`memberVocabularyRefusal?`), so a malformed parked state is a refusal either way — but named
`deadlock` where the strict runner now names the unbound address. It is the instance-not-class
pattern on an API boundary no admitted program reaches (the review's own scope statement for
DC11). A one-line change to `deadlockOrRefusal`'s shape, or a record that the enumerator is
outside DC11's claim.

### F4 — P3 — the contract count drifted again inside the train that fixed the drift

`docs/release.md:99` and `docs/semantics-overview.md:301` say the comparator contract is
"383 on 2026-10-26"; `scripts/gen-contract --check` reports **385** (the two dedup theorems
landed in the same train), and `CLAUDE.md:219` says 385. DC14's own class (counts that vary
between pages); both pages say they do not copy the count and then copy it. Replace the number
with the family rule or regenerate it.

### F5 — P3 — `require ()` is refused with a message that misdescribes it

`modfile.go:216`: an empty block written on one line, `require ()`, is tokenised to
`require ( )` and refused as «"require ()" has a parenthesis where a require argument
belongs». gc accepts it (probe `dc06-modfile/empty-require-block`: gc 0, frontend 1). The
over-refusal is the documented direction; the message is wrong about why. Either accept the
empty block (gc's grammar) or say "an empty block on one line is not validated".

### F6 — P3 — residual of DC02: a compiler child killed under `go build` is exit 1, not a signal

`scripts/coverage-negative:344–360` classifies the oracle's exit status before its text
(timeout 124, SIGKILL 137 and exit 2 each FAIL at `go-crash` — reproduced on a scratch
manifest with a fake `go`; the control row PASSes). `go build` itself, when its `compile`
child dies on a signal, prints `<pkg>: signal: killed` and exits **1**; the runner reads that 1
as a verdict and, if the expected diagnostic was emitted first, the row PASSes (reproduced
with the fake `go` emitting the diagnostic, `signal: killed`, exit 1: `PASS childkill`). The
window is narrow (gc prints its diagnostics and exits at once) and the row would need the
text first; worth a one-line refusal of an oracle output containing `signal: ` so the
status-first contract holds through `go build`'s masking.

### F7 — P3 — the negative runner's GOPATH-mode leg inherits `GOFLAGS`; `GOWORK` is never pinned

`scripts/coverage-negative:349` (the leg every row without a go.mod takes, 415 of 425) runs
`go build` without `GOFLAGS=`, while its module leg (line 346) and the positive runner
(`scripts/diff-coverage:1448`) scrub it, and `scripts/ci` does not scrub it either. An
inherited `-tags`, `-mod` or `-toolexec` reaches the oracle on those rows. On a compile-error
row the likely effect is a different failure (red, not green), so this is hygiene, but it is
a box-specific assumption in the gate's path. `GOWORK` is pinned nowhere (see F1).

### F8 — info — the six overrides that stay, and six that were not counted

The six `maxHeartbeats … in` overrides (`PrefixFacts.lean:395`, `StepErrors.lean:500, 700,
720, 948`, `StepFnFacts.lean:2716`) each carry a measured bracket and the split that would
retire them. Six `maxRecDepth 100000 in` raises remain in core files outside that count
(`Ops.lean:4374–4376, 4529–4533`: five `decide` table theorems under one shared two-line note;
`FloatBits.lean:587`: explained). The charter's rule covers `maxRecDepth` too; a per-declaration
bracket on the five is the remaining cleanup. The one theorem DC12 deleted
(`mapEntryIndex?_ok_entries`) concluded `True`; `gen-contract --check` PASS (§D pins ⊆ contract).

## What I checked and found sound

- **BUG-133 / DC01, the pointer arm** (`Ops.lean:3760`, `l.canon == r.canon`). `Loc.canon`
  erases only the `TypeId` of `.field` steps and keeps the root address, every field name and
  every index. Two different cells canonicalize alike only if they share a root address and a
  name/index path; `loadLoc`/`storeLoc` accept a `.field` step only at the cell's mint tag or a
  tag-compatible one (identical `FieldDef` lists), so on every path the machine accepts the name
  determines the slot. Channel and map identity is root-cell `BEq` (a `make` allocates a root
  cell), untouched. Fourteen probes of mine agree with gc on every route
  (`dc01-identity/`: `switch` on a pointer, `map[[1]*int]`, a field of an array element through
  the alias, slice views over distinct backings, `append` without growth, promotion through an
  embedded pointer, a struct copy, `&a.In`/`&a.In.Y` through the alias at `*inner`/`*int`/`any`,
  same-named fields at different depths, a struct key holding a pointer, `any(&a.Arr[2])`,
  `map[any]` with the converted-back key — gc `1 12 true false true true false 111 false 12 true
  22`, machine identical; `dc01-identity-stdlib/`: `slices.Contains`/`slices.Index` through the
  lowered stdlib — `true 1` both sides), on top of the 44 corpus rows BUG-133 pins. The
  interface arm decides `dynL != dynR` before the payload walk, so `*A` vs `*B` boxes stay
  unequal; the zero-size latitude (R15) is unchanged and documented.
- **DC11, the pool** (`Multi.lean:301–398`). Thirteen genuinely deadlocking shapes are still
  `deadlock` through the CLI (`dc11-deadlock/`: nil recv/send, unbuffered and full-buffer send,
  select without default, `select {}`, Mutex twice, RWMutex both orders, WaitGroup, recursive
  Once, two goroutines parked on each other, a mutex park beside a channel park); gc confirmed
  on the two sync shapes I ran. Main exiting with a goroutine parked is `ok`. `wakeReady?`
  differs from the old Bool only on error: the select arm now propagates the first clause
  error instead of skipping it, and `clauseReady` errors only on a non-channel value or an
  unbound cell, so on a well-formed state the schedule is unchanged; the Bool projection's one
  consumer is `threadRunnable`. The three drivers, `PoolFacts.front` and the choice-trace
  mirror agree on `deadlockStop`; `stepMulti`'s own empty-menu arm is unreachable from the
  drivers (they test `runnableIdxs` first). The main-exit window returns main's outcome without
  inspecting parked goroutines — stated in `docs/BUGS.md` as outside the claim. The eval pin
  `malformedParkedStateFacts` (`Tests/GoCoreEval.lean:3119`) covers the review's probe and two
  valid controls.
- **The restored dedup proof.** `execProgLoop_unfold` (`EnumDedupStreams.lean:578`) restates
  the live driver, `deadlockOrRefusal` arm included, by `rw [execProgLoop.eq_def]; rfl`, so a
  drift from the driver fails loudly. The completeness induction's empty-runnable arms
  (`EnumDedupSound.lean:880, 1002`) close by `cases hnode` — the checker refuses such nodes —
  so the arm's error value is irrelevant to the proof; nothing else in the two modules mentions
  the deadlock arm. The independent review (`.tmp/dedup-soundness-review.md`, read) was
  answered: F2 fixed in `GoCore.lean`, F3 recorded at the claim sites and as backlog row 53,
  F4 as row 52.
- **DC03, the seed** (`Seed.lean:288–350`). Phase 0 judges each cell's spelled dimensions
  against `sliceCapBudget` (2^23) and its footprint through the table against
  `arrayFootprintBudget` (2^24), then resolves the value, before any allocation. Seven probes
  (`dc03-seed/`): the review's 73-byte input refuses by name at 67 MB RSS; `[8388608]int`,
  `[3]Mid2`, `[4]Mid2` (exactly 2^24 leaves) with an empty value refuse at the shape, before
  allocation (72 MB RSS); a declared type carrying `[8388608]int` is decoder-quarantined
  upstream (65536 per dimension), so `[n]Declared` is the only seed-side amplifier and it is
  counted through the table; a cyclic two-cell seed runs (`cycleLen` = 2). A cell's value must
  be explicit (arrays exact length, every struct field named, no zero shorthand), so the
  aggregate materialization of a many-cell seed is linear in the file; `--stream rand:<len>`
  is bounded by the same constant.
- **DC02, the negative oracle's status.** On a scratch manifest with a fake `go`: a 10 s build
  under a 3 s budget → `FAIL go-crash … TIMED OUT`; `kill -9` after the diagnostic → `go-crash
  … KILLED (exit 137)`; exit 2 → `go-crash … failed with exit 2`; the control row PASS. The
  `go_rc` classification (`coverage-negative:344–360`) and `undecided_cause`
  (`run-with-timeout.sh`, one definition for both lanes) name 124/137/143/other-signal/127/2
  as non-verdicts. Residual: F6.
- **DC06, the go.mod scanner, against gc** (24 shapes, `run-modfile.sh`). Agreement on 19: a
  BOM (both refuse), CRLF (both accept), `// Deprecated`, `exclude`, `go 1.26.0`, `ignore`,
  `require … //indirect` with and without the space (gc builds an unimported require under
  `GOPROXY=off`, so the "cannot fetch" interference does not arise), a `/v2` module path,
  no trailing newline, `replace => ./dir`, a `retract` block with comments, tab-indented lines,
  `tool`, an uppercase module path, a block comment (both refuse), `go 1.26 + toolchain
  go1.26.5`, `go 1.26.5` alone. Over-refusals in the documented direction: a quoted module
  path, `go 1.26 + toolchain go1.26.4`, `require ()` (F5). False green: F2. Not read at all:
  go.work (F1). The ten `modules/` rows: each go.mod's gc error is a parse-stage error, so no
  row can pass on a `GOPROXY=off` lookup failure instead of its claimed cause; the runner
  checks the frontend's class only, never that its reason matches gc's (the design, as for the
  three older classes).
- **DC19 / the locale sweep.** `scripts/coverage-manifest` and `coverage-negative-manifest`
  are byte-identical under `LC_ALL=C`, `C.UTF-8` and `en_US.UTF-8` (shas compared); no tracked
  path has a non-ASCII byte; the only `[a-z]` classes left in the 22 scripts are the tag
  validators of the two manifest scripts (ASCII tags; under C they are strict, never looser).
  `gen-contract --check` PASS under the worktree's inherited locale (385 statements, the
  kept-name validator spelled out, `VALIDATOR ERROR` distinguished from a stale contract).
- **DC05, notices.** `scripts/check-notices` ok. My own search for copied or generated material
  outside the inventoried subtrees (`Code generated`, `DO NOT EDIT`, `The Go Authors`,
  `Copyright`, Go test-directory headers) finds only the derived `wirepb`/`wireproto` mirror
  (inventoried), the stringer output in `raftsubject/` (inventoried) and GoLean's own
  generated files.
- **DC08/09/10/18, the instruments** (read, not run: the harness needs the protobuf module
  cache this box lacks). `ownedout.claim` refuses a populated unmarked directory, a symlink or a
  file, and `release` reports a failed deletion as the invocation's failure; `runprobe`,
  `codeccheck` and `tracereplay` test the machine's exit status against the observation's
  status (0 iff `ok`) before comparing text; the negative modes require `go run`'s own `exit
  status N` trailer; status-less resumed records are refused by name; `raftharness` refuses an
  unknown scenario, `-iters ≤ 0` and positional arguments and names its run count;
  `choice-trace-corpus` summarizes only this run's chunks, names stale ones, and takes the
  summarizer's status as its verdict.
- **Records.** The README example reproduces (`value 6`); README's trust story now says the
  model is hand-written and what a green gate establishes; `docs/release.md`'s BUG-131 and
  kept-surface wording matches the code; `docs/cli.md`'s dedup paragraph states the theorem's
  scope (values and terminal status; `output` outside it). `THIRD_PARTY_NOTICES.md` §2 is
  flagged as transcribed pending the module cache (honest). `setup-deps` pins raft at the
  derivation revision.
- **Gate state in the worktree.** `capped lake build`: no-op (replay-only); kernel replay:
  PASS, 55 modules, 12.8 s; `check-notices` ok; `gen-contract --check` PASS. The full
  `scripts/ci --diff` was not re-run here (the owner's run at the merge is recorded in backlog
  row 51); nothing I found changes a baseline row.

## Reproduce

From the worktree root with `.tmp/nativefrontend` built (`GO111MODULE=off go build -o
.tmp/nativefrontend ./tools/nativefrontend`) and `.lake/build/bin/golean` present:

```
P=docs/reviews/2026-10-26-train19-probes
bash $P/run-both.sh $P/dc01-identity switchOnPointer arrayKeyOfPointers elemFieldThroughAlias distinctBackings appendNoGrowth embeddedPointerPromotion copyIsFresh innerThroughAlias sameNameDifferentDepth structKeyThroughAlias ifaceElemThroughAlias anyKeyConvertedBack
bash $P/run-both.sh $P/dc01-identity-stdlib containsThroughAlias indexThroughAlias
bash $P/run-both.sh $P/dc11-deadlock nilRecv nilSend unbufferedSend bufferedFullSend selectNoDefault selectEmpty mutexTwice rwWriterThenReader rwReaderThenWriter wgWait onceRecursive mixed mixedSync mainExitsParked
.tmp/nativefrontend --subject --dir $P/dc03-seed --out .tmp/s.json && for s in huge arr8m-empty mid2x4-empty; do capped -m 2G -- .lake/build/bin/golean native-json-run --input .tmp/s.json --function isNil --seed $P/dc03-seed/$s.json --arg-nil --fuel 0; done
bash $P/run-modfile.sh          # F1, F2, F5 and the agreeing shapes; F1's behaviour: see the commands under F1
```

The DC02 scratch run (a fake `go` on `PATH` for the oracle leg, a four-row manifest copied
from `arrays/array-index-float`, `GOLEAN_COVERAGE_ARTIFACTS` pointed at scratch,
`GO_TIMEOUT_SECONDS=3`) is described under F6; it is not retained.
