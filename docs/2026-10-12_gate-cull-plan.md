# The gate cull — classification and plan (2026-10-12)

[AGENT] worker, lane `docs/gate-cull-plan-1012` (worktree
`.claude/worktrees/gate-cull-plan-1012`, off `main` @ `89dfe677`). Authority:
[USER] Mike 2026-10-11 «an early priority for this project's restart is a gate
cull to conform to the gate cruft rules» (`docs/2026-10-11_recovery-and-migration-plan.md`
§7); 2026-10-12, verbatim from the session prompt: the gate «is insanely absurdly
over engineered and takes far too long to run», «prepare a plan for cutting it
down to a design that enforces trust and does not slow everything to glacial
pace», «DO NOT run the whole gate», «We don't need to baseline the gates
beforehand»; mid-session: «We are likely going to throw out most of the costly
certificate nonsense unless it is genuinely critical for trust». The rule applied
is the global `~/.claude/CLAUDE.md` «Gates and speedbumps (avoid gate cruft)».

Every disposition below is an [AGENT] proposal PENDING [USER] unless marked
otherwise. Nothing was run, cut or edited by this lane; the gate was not
executed. Numbers are RECORDED ones (sources named), not fresh measurements.

## 0. The verdict at a glance

- **The gate is mostly not a gate.** Of the 44 rows classified in §2 (the 38
  steps of a fast run, the five `--diff`-only ones, and the re-pin guard's
  report-only half), 17 guard the trust surface the charter names and merge
  into 12 blocking steps. The other 27 are self-tests of checkers, compiled «poison» and mutant controls that test
  the checkers rather than the product, cache-validity certificates, a build
  receipt registry, report-only instruments, and static consistency lints.
- **Where the time goes (warm `--diff`, 850–1034 s recorded):** roughly 430 s
  is the post-build Lean «audit control» steps plus the certificate check, and
  the rest is the differential corpus itself. Cold, one self-test alone has
  taken 3912 s (`equations`, receipt `481bfdc3` on this box). The differential,
  the one thing the trust claim rests on, is not the slow part.
- **The certificate apparatus is not critical for trust.** It certifies a
  CACHE: one `tier=slow` corpus row whose full enumeration takes ~94 s
  single-core, so that `--diff` can skip it. Delete the cache and the row runs
  fresh on every `--diff`, which is strictly stronger evidence than any
  certificate, and the 760-line tool, its 18 unit tests, the records directory,
  merge-protocol step 5a, `release-check`, the `--slow` mode and the nightly
  `--slow` job all go with it. §3.
- **Proposed shape:** two blocking tiers and one report. `scripts/ci` (the
  fast tier: build everything, unit tests, three cheap scans, the baseline diff
  of the last recorded corpus run) and `scripts/ci --diff` (the gate: plus the
  differential and negative corpus against their tracked baselines). Everything
  else that survives is a speedbump: printed in the same run, never sets the
  exit code, visibly RED in the summary when it fails. Derivation-anchored
  expectation, not a measurement: fast tier about a minute warm; `--diff` the
  cost of the corpus run alone, about half of today.
- **The first deliverable** (plan §7) is the classification (§2) and the
  `CLAUDE.md` «The gates» text it implies (§5), for the [USER] to rule on.
  Then four lanes (§6).

## 1. The rule, applied to this repo

The global rule: gates BLOCK and only the trust surface gets them, kept small
and named in the working-practices doc; everything else is a speedbump, a cheap
report at claim points that catches honest drift, not built to survive attack
and not blocking; a check is added only when it is cheap and catches a real
class of mistake; no large enumerative tables or adversarial-grade machinery
unless a trust property is genuinely at risk; over-strong gates on non-trust
surfaces are cut, not reclassified.

The trust surface (`CLAUDE.md` «The trusted surface»): (1) the interpreter and
the native lowering, validated by the differential corpus against `go run`;
(2) the differential apparatus: the runners, the tracked baselines, the oracle
pin and the re-pin guards. Plus the doctrine the customer's proofs depend on:
the semantic core is total (no `sorry`/`native_decide`/axioms in `GoLean/`).

So a step blocks only if it is one of: the build of the product (warning-free,
because warnings corrupt the runner's JSON channel); the product's own unit
tests (eval tests, the frontend and harness `go test`s); the totality check;
the oracle pin; the differential and negative corpus runs and their baseline
diffs; the forward re-pin guard (a PASS→non-PASS flip must be on a `BUGS.md`
Cases line). Everything that tests a CHECKER (self-tests, poison copies,
mutants, receipts, certificates) is adversarial-grade machinery on a non-trust
surface and is cut. Everything that checks a DOCUMENT against the code
(registers, ledgers, citations, indexes) is a speedbump.

## 2. The classification — every step of `scripts/ci` today

Cost column: recorded, with the source. `receipt` = the two
`artifacts/ci-library-timings/*.json` on this box (the Lean-side steps only;
warm run 505 s total, cold run 4631 s). `tail` = committed gate tails under
`docs/evidence/`. `—` = not recorded separately; the step's shape says what it
costs (static text scan = seconds; a `lake env lean` of a file importing
`GoLean` = tens of seconds warm, an hour cold). Class: **GATE** blocks;
**SPEEDBUMP** reports; **CUT** leaves the gate (the script may stay as a
hand-run tool, said where so).

### 2.1 Preflight (before the build)

| # | step | what it checks | cost | class | disposition |
|---|---|---|---|---|---|
| 1 | Tests/library ownership + receipt self-tests (`tools/ci_libraries.py`) | a registry proving each Lake library is built by a named ci step, receipts fresh to this run | — (python; the receipts wrap every Lean step) | CUT | §3.2: build everything with one `lake build`; the omission class («a Tests module nobody builds») closes without a registry. Touches a [USER] 2026-09-08 ruling (D2) |
| 2 | build parallelism note | `LEAN_NUM_THREADS` from the cap | 0 | keep (not a check) | keep; shrink the comment |
| 3 | oracle toolchain pin | live `go` = `baselines/go-oracle-pin` | 0 | GATE | keep as is |
| 4 | escape-hatch preflight | `sorry`/`admit`/`native_decide`/`axiom` text scan over `GoLean/` | <1 s | GATE | keep; merge 4–6 into one scan step |
| 5 | meta-layer escape hatches | `unsafe`/`opaque`/`implemented_by` | <1 s | GATE | merge into 4 |
| 6 | escape-hatch addendum | `decide +native` spellings | <1 s | GATE | merge into 4 |
| 7 | fidelity-bug index cross-check (`check-bugs.sh`) | `BUGS.md` Cases lines vs the baseline | seconds | SPEEDBUMP | keep; also what the re-pin guard reads, so a red here is read at the merge |
| 8 | feature-coverage cross-check (`check-coverage`) | no dead feature tags | seconds | SPEEDBUMP | keep |
| 9 | spec-anchor citations (`check-spec-anchors`) | `spec#`/`mem#` anchors resolve at the pin | seconds (needs `deps/go`) | SPEEDBUMP | keep |
| 10 | stdlib admission register (`check-stdlib-register`) | register doc = frontend tables | seconds (one frontend run) | SPEEDBUMP | keep |
| 11 | membership-lane gate self-test, fast half (`test-lane-validation`) | the manifest validator rejects bad rows; G1–G4 no-publish fixtures | ~2 s+ (shell; fake `lake`) | CUT | a self-test of shell checkers; stays as a hand-run script for when `coverage-manifest`/`diff-coverage` change (§3.4) |
| 12 | evidence-on-main size gate + self-test | evidence caps ([USER] 2026-09-07 ruling) | seconds | SPEEDBUMP | keep the check; drop the self-test from the gate |
| 13 | AGENTS.md alias + self-test | `AGENTS.md` → `CLAUDE.md` ([USER] 2026-09-07 direction) | <1 s | SPEEDBUMP | keep the check; drop the self-test |
| 14 | inittask generator fail-closed self-test | a generator dies by name on a fake `go` | seconds | CUT | self-test of a tool; hand-run when the generator changes |
| 15 | imported-goose verbatim staleness | landed imports = goose bytes at the pin | seconds (needs `deps/goose`) | SPEEDBUMP | keep |
| 16 | engine-isolation lint | core never imports `EnumDedup` | <1 s | SPEEDBUMP | fold into the scan step (4) |
| 17 | memory-module raw call sites (`check-mem-callsites`) | raw `Mem` ops match a tracked inventory | seconds | SPEEDBUMP | keep |

### 2.2 Build and the post-build Lean steps

| # | step | what it checks | cost | class | disposition |
|---|---|---|---|---|---|
| 18 | core build (`scripts/build-certified` → `lake --rehash build golean`) | the product builds, warning-free | 5–6 s warm (receipt); cold 64 G, minutes | GATE | keep as plain `lake build` of ALL targets (§3.2); the certified wrapper goes (§3.1) |
| 19 | certificate provenance (`check-certification`: 18 unit tests + `check-records`) | the cached slow-row record is bound to the current inputs | 72–74 s (tails 09-22, 09-24) | CUT | §3.1 |
| 20 | core totality audit (`check-core-audit`) | a harness imports every `GoLean/` module; every declaration classical-trio only; required core theorems present; 5 compiled poisons refused | 10–15 s (receipt) | GATE | keep the audit (it is the machine check of the totality doctrine); drop the 5 poison compilations if they are a measurable share |
| 21 | admission checker proofs + post-import audit (`check-admission --lean-only`) | `AdmissionTests` builds; then python elaborates poison copies and audits them; 370 M scratch per run | 63–109 s (receipt) | CUT (controls) | the library build moves into `lake build`; the `elaborate`/`audit` poison modes go; `tools/admission-check.py`'s scratch retention (D5) becomes moot |
| 22 | declaration boundary (`check-declarations`) | `DeclarationTests` builds; 8 modules re-elaborated by hand; `StrictJsonParse` runs; Unicode table = Go oracle; fixture pin; dependency-audit poisons | 38–45 s (receipt) | SLIM | keep the Unicode-table regeneration compare (a real oracle pin, seconds) and the test run; the library build moves into `lake build`; the hand re-elaboration and the poison audit go |
| 23 | wire boundary (`check-wire-boundary`, 688 lines) | byte mutants of a real wire refused by name through the real CLI (BUG-110) | — (frontend + ~10 CLI runs) | GATE (unit test) | keep in the fast tier; candidate to fold into `go test ./tools/nativefrontend` as table-driven cases |
| 24 | package-correct method identity (`check-method-identity`) | 4 named `go test`s (already inside step 31), `Tests/MethodIdentity.lean`, a poison-copy compile under a 360 s budget, a dispatch audit | 113–125 s (receipt); the poison compile is 150–201 s alone (`operational-lessons.md`) | CUT (controls) | the `go test`s are duplicates of step 31; the Lean test moves into `lake build`; the poison compile and dispatch audit go. This removes the thin-headroom timeout class entirely |
| 25 | unseq scheduler, Stage B (`check-unseq-scheduler`) | reference sets over ALL tapes vs hand-built graphs; a separate axiom audit of the test module | 92–96 s (receipt) | SLIM → `--diff` tier | the reference-set test is a real scheduler test but enumerates whole tape spaces; run it under `--diff` beside the corpus, drop its separate axiom audit (step 20 covers `GoLean/`; `Tests/` theorems are not the product) |
| 26 | unseq wire, Stage C (`check-unseq-wire`) | wires from bytes through the decoder vs reference sets; decoder mutants refused by name | 6 s (receipt) | GATE (unit test) | keep |
| 27 | semantic equations (`check-equations`) | `Equations.lean` + the toy client build; the no-unfold regex; an import whitelist; 9 mutant elaborations as self-tests | 43 s warm, **3912 s cold** (receipt) | SLIM | the build moves into `lake build` (the client library); keep the regex guard and the whitelist (<1 s); CUT the 9 mutants (e1–e3), which are the whole cost |
| 28 | pool spec freeze + discharge (`check-pool-spec`) | the 48 frozen statements' hash, the milestone map, staged discharge; python mutant self-tests | seconds (python) | SPEEDBUMP | keep; drop the self-tests from the gate run |
| 29 | frontend pins (`check-frontend-pins`) | the init-order deviation observation and the raft twin wire, byte-exact | — (one frontend run over `raftsubject/`, one CLI run) | GATE | keep in the fast tier (it is the lowering's pin over the real subject) |

### 2.3 Go-side tests and the eval tests

| # | step | what it checks | cost | class | disposition |
|---|---|---|---|---|---|
| 30 | import-goose gate self-test (`test-import-goose`, 674 lines) | the importer's reject-shape fixtures | — (shell + a throwaway git repo + `go`) | CUT | hand-run when `import-goose` changes |
| 31 | frontend unit tests (`go test ./tools/nativefrontend`) | the lowering's own tests | cached go test | GATE | keep; one `go test ./tools/...` invocation for 31–33 |
| 32 | lowering-diagnostic tables (`go test ./tools/lowerdiag`) | `causes.tsv` vs the ledger; tool tests | cached go test | SPEEDBUMP (tooling) | run inside the same `go test ./tools/...`; cheap enough not to separate |
| 33 | coverage-harness unit tests (`go test -count=1 ./tools/coverageharness`) | the oracle observer: crash channel, terminal classifier, transport | — (`-count=1`, execs `go run`) | GATE | keep (the differential apparatus's own tests) |
| 34 | interpreter eval tests (`gocore-eval-tests`) | 298 interpreter unit tests | 1 s warm (receipt) | GATE | keep |

### 2.4 The corpus (`--diff` / `--slow`) and the baselines

| # | step | what it checks | cost | class | disposition |
|---|---|---|---|---|---|
| 35 | re-run the full native differential corpus | 3936 cases: `go run` vs the interpreter, 32-wide; lanes strict 3517 / membership 271 / confluent 103 / racy 45; 26 rows `engine=dedup`; 1 row `tier=slow` | the remainder of a 850–1034 s run after the ~430 s of steps 19–27 | GATE | keep; delete `--slow`, `GOLEAN_SLOW`, the `tier=slow` cached path and `build-certified` call inside `diff-coverage` (§3.1); the one slow row runs fresh as an ordinary `engine=dedup` membership row |
| 36 | membership-lane self-test, go half (`test-lane-validation --with-go`) | F4/F6/B3–B5/G5/T1–T8/D1–D6 fixtures against the real runner | — (runs the runner on fixtures) | CUT | hand-run when `diff-coverage` changes (§3.4) |
| 37 | re-run the negative corpus | 394 `go build` rejections | cheap | GATE | keep |
| 38 | derived oracle artifacts re-derived | `Tests/FloatVectors.lean` and `inittask-std.tsv` regenerate byte-identical at the pin | seconds | SPEEDBUMP (`--diff` tier) | keep |
| 39 | negative baseline diff | the recorded negative run vs `baselines/negative-full.tsv`, with attribution (meta, manifest sha, drift, dirty) | seconds | GATE | keep; one shared implementation with 40 (today two 90-line copies) |
| 40 | differential baseline diff | the recorded run vs `baselines/native-full.tsv`, attribution, full vs partial | seconds | GATE | keep, same |
| 41 | baseline re-pin guard ×2 (forward) | a PASS→non-PASS flip in a re-pin is on a `BUGS.md` Cases line | seconds (git + awk) | GATE | keep (both tracked baselines, both modes) |
| 41b | re-pin guard, reverse report + alternation survival | FAIL→PASS / deleted rows / count decrease, report-only; alternation rows survive a re-pin | seconds | CUT the reverse report; FOLD alternation survival into `coverage-baseline-diff` | the reverse scan is a report nobody acts on inside a gate; the alternation check is cheap and guards a recorded flake class, but belongs in the diff tool, not as a ci step |
| 42 | cross-ledger reconciliation (`tools/reconcile-records`, 1354 lines, report-only) | prose invariants across the ledgers | — (python over the docs) | CUT | a dossier instrument by its own description; run by hand at claim points; its C9 rule dies with the certificates |
| 43 | executed library coverage | every receipt from this run present and fresh | 0 | CUT | with 1 |

**Totals over the 44 rows:** GATE 17 rows (3, 4, 5, 6, 18, 20, 23, 26, 29, 31, 33, 34, 35, 37, 39, 40, 41), which merge into 12 blocking steps (the three scans as one, the three `go test`s as one, the two baseline diffs and the forward guard as one «baselines» step); SPEEDBUMP 12 (7, 8, 9, 10, 12, 13, 15, 16, 17, 28, 32, 38); CUT 11 (1, 11, 14, 19, 21, 24, 30, 36, 41b, 42, 43) plus the self-tests embedded in 12, 13 and 28; SLIM 3 (22, 25, 27); not a check 1 (2).

## 3. The four cuts that carry the cost

### 3.1 The certificate apparatus — «genuinely critical for trust?» No.

What it is: `tools/certification.py` (760 lines) + `tools/test_certification.py`
(18 tests, run on EVERY gate as step 19) + `scripts/build-certified` +
`scripts/check-certification` + `baselines/certified/` (one row's record, JSON
+ TSV) + `artifacts/certification/` + the `tier=slow` cached path in
`scripts/diff-coverage` + `--slow`/`GOLEAN_SLOW` + merge protocol step 5a +
`release-check` + the nightly `--slow` workflow + reconciler rule C9 +
`docs/2026-09-09_certificate-provenance-{charter,design}.md` (records; stay).

What it protects: a CACHE. Exactly one corpus row,
`imported-goose/channel/google-search` (`engine=dedup`, `members=6`,
~40 M pool steps, measured 94 s single-core in 2026-08), is marked `tier=slow`
so that `--diff` replays its tracked enumeration instead of running it. The
certificate is the proof that the cached enumeration still describes the
current binary. The 2026-09-05 audit (F8) found the cache key too narrow, and
the fix widened the certified inputs to every file under `GoLean/`, `scripts/`
and `tools/` plus the toolchains. That is why every script edit now goes STALE,
why the fresh-clone trial needed three gate cycles for five small fixes, and
why 5a makes every merge a `--slow` run plus a records commit plus a re-gate.

Why it is not trust-critical: the trust claim is per row, «observed ∈
modeled», established by RUNNING the row. The certificate only ever said «you
may skip running this row». Without the cache there is nothing to certify;
the row runs on every `--diff` like the other 25 `engine=dedup` rows, which
already run uncached. On a 32-wide corpus run it is the longest pole, not an
addition, if the rest of the corpus takes longer than its ~100–160 s; if it
does not, it bounds the wall at that figure, still far below what steps 19–27
cost today. Risk, named: the row's enumeration timeout
(`LEAN_ENUM_TIMEOUT_SECONDS`, 300 s) must cover it on this box; if it does not,
the row goes red naming the timeout, and the decision is that row's budget
(or demoting it to K-draw sampling like the other membership rows), never a
cache. The first `--diff` after the cut measures this; no pre-baseline needed.

Cut list: delete the files and directories above (the two design docs stay as
records with a one-line «withdrawn 2026-10-12» note at the top); delete step 19,
step 43's dependence, the `--slow` flag and its branch in `scripts/ci`, the
`tier=slow` manifest tag (the row keeps `engine=dedup members=6`), 5a from
`CLAUDE.md`, the nightly's `--slow` (nightly becomes `--diff`), and
`operational-lessons.md` §«A cached certification is owed a re-run…» gets a
closing addendum, not a rewrite.

### 3.2 The library-receipt registry — replaced by building everything

`tools/ci_libraries.py` + `tools/test_ci_libraries.py` + `scripts/ci-libraries.json`
exist to prove that each of the 10 Lake libraries is built by a named ci step,
with receipts fresh to the run. The class of mistake is real (a `Tests/` module
nobody builds rots silently) and the fix is one line: `lakefile.toml`
`defaultTargets` lists every library and executable, and the fast tier runs one
`lake build`. A new `Tests/` module that no library glob names would still be
skipped silently by Lake, so the fast tier keeps one set check: every
`Tests/*.lean` on disk must be named by a `lakefile.toml` glob (the same
`find`-vs-lakefile comparison `check-core-audit` already does for `GoLean/`;
one `comm` line, fails by name). The [USER] 2026-09-08 ruling (quoted in
`scripts/ci`: «every Tests module has a library, and every library has an
executed named CI build») keeps its intent, every Tests module is built on
every gate, with a mechanism that costs nothing. **D2 asks for that re-ruling.**

### 3.3 The compiled «poison» and mutant controls — adversarial-grade, on checkers

Steps 20 (5 poisons), 21 (the admission `elaborate`/`audit` modes), 22 (the
dependency-audit poisons), 24 (the poison-copy compile, 150–201 s), 25 (the
separate axiom audit), 27 (9 mutant elaborations; 3912 s cold). Each compiles
a deliberately broken copy of a module to prove the checker would notice. That
is machinery built to survive an adversary, applied to CHECKERS, which the
global rule reserves for a trust property genuinely at risk. The property
(«the core is total») is checked by step 20's audit over the real modules; the
controls add no evidence about the product. Shared tooling that goes with them:
`tools/typed_audit.py` and its `tools/test_typed_audit.py`,
`tools/method-identity-audit.py`, `tools/method-identity-dispatch.py`,
`tools/declaration-audit.py`'s poison half, `tools/admission-check.py`'s
`elaborate`/`audit`, and the whole `.tmp/*-audit-*` scratch family.
`scripts/typed-gate-scratch.sh` stays while `check-core-audit`,
`check-wire-boundary`, `check-unseq-wire` and `check-equations` still source it.

### 3.4 The self-tests of checkers — out of the gate, kept as tools

`scripts/test-lane-validation` (921 lines, both halves), `test-import-goose`
(674), `test-check-evidence-size`, `test-check-agents-alias`,
`test-gen-inittask-table`, plus the in-script self-tests of `check-pool-spec`
and `check-equations`. They test that a checker rejects bad shapes. Useful when
the checker changes; dead weight on every gate. Disposition: they stay in
`scripts/` as hand-run developer tests; `CLAUDE.md` «Working practices» gets one
line: «if you change a `scripts/check-*`/`coverage-*`/`diff-coverage`, run its
`scripts/test-*` before the audit ask». The part of `test-lane-validation` that
tests the differential runner's fail-closed paths (G/T fixtures) is the one
borderline case, since the runner is trust surface; the recommendation is
still hand-run on change, because a runner regression of that kind also shows
up as a missing or unattributable record, which the baseline step refuses.

## 4. What the gate looks like after the cull

```
scripts/ci              fast tier — blocks any commit touching runtime code
  oracle pin · escape-hatch scan (one step) · lake build (all targets, warning-free)
  · core totality audit · go test ./tools/... · eval tests · unseq wire
  · wire boundary · frontend pins · baseline diff of the LAST recorded runs
  · forward re-pin guard
  speedbumps (report-only, RED visible in the summary): bugs index, feature tags,
  spec anchors, stdlib register, evidence size, agents alias, imported-goose
  verbatim, mem call sites, pool spec freeze, lowerdiag tables

scripts/ci --diff       the gate — blocks a merge to main
  fast tier + the differential corpus (fresh, no cached rows) + the negative
  corpus + derived-artifact regeneration (speedbump) + unseq scheduler (Stage B)
```

Shape rules for the rewrite of `scripts/ci` (1286 lines today):
- one function per step, name + command + verdict; the rationale moves to a
  pointer (the F13 finding of the 2026-09-05 audit asked for exactly this);
- every step still runs even if one fails; the summary still lists all;
  speedbumps print under their own heading and never set `fail`;
- the fail-closed rules that are cheap and real stay: unknown flag refuses;
  a step that cannot run is RED, not skipped; no-record is a FAIL in `--diff`
  and in the fast tier unless `GOLEAN_ALLOW_NO_DIFF=1` (CI's fresh runner);
- the `capped` re-exec and the thread scaling stay (box rule);
- target: `scripts/ci` under ~300 lines; `scripts/` loses 10 of its 25
  `check-*`/`test-*` files from the gate path.

Expected cost, derivation-anchored (no measurement was taken, per the [USER]):
fast tier warm = build no-op (~6 s) + core audit (10–15 s) + go tests (cached;
the harness tests exec `go run`) + eval (1 s) + unseq wire (6 s) + wire
boundary + frontend pins + scans: about a minute. `--diff` warm = that plus
the corpus, i.e. today's run minus the ~430 s of steps 19–27, so roughly half
of the recorded 850–1034 s. Cold builds are unchanged (64 G, the measured
case) except that nothing elaborates mutants any more, which is what made a
cold `equations` step cost 3912 s.

Not in this cull, noted for later as a [USER] call: a per-case content cache
for the corpus (skip a row when its `main.go`, wire and binary hashes are
unchanged). It would make `--diff` incremental but is a cache, with a cache key
to get right; the lesson of §3.1 is to not build one until the uncached run is
actually too slow.

## 5. Proposed `CLAUDE.md` «The gates» text (DRAFT — replaces the section; [USER] edit)

> ## The gates
>
> - **Gates block.** `scripts/ci` before any commit that touches runtime code
>   (the build of every target, warning-free; the escape-hatch scan and the
>   core totality audit; the eval tests; the frontend and harness `go test`s;
>   the unseq-wire, wire-boundary and frontend-pin checks; the oracle pin; the
>   baseline diff of the last recorded corpus runs and the forward re-pin
>   guard). `scripts/ci --diff` before any merge to `main`: the same plus the
>   fresh differential and negative corpus against their tracked baselines
>   (`baselines/`), no cached rows. Always under the box-wide `capped`
>   (`capped scripts/ci`; a cold full build is the measured `-m 64G` case).
>   Baseline re-pins only with a full run and a written reason; PASS→non-PASS
>   flips must be on a `BUGS.md` Cases line.
> - **Speedbumps report.** The same run prints the consistency checks (bugs
>   index, feature tags, spec anchors, stdlib register, evidence size, the
>   `AGENTS.md` alias, imported-goose verbatim, memory call sites, pool spec
>   freeze, lowering tables, derived-artifact regeneration) under their own
>   heading; a red one never fails the gate but is read at the merge ask and
>   either fixed or waived there, by name.
> - **Self-tests are not gates.** `scripts/test-*` run by hand when the script
>   they test changes.
> - The pre-merge adversarial audit: the ask is unconditional; scope and waiver
>   are the user's.

Merge protocol: step 5a is deleted whole; step 2 reads «Arc complete →
`scripts/ci --diff` green»; step 6 unchanged.

## 6. The lanes (each: branch off `main`, worktree, the SURVIVING tier run,
audit ask, merge sign-off; never the old gate)

1. **`cull/certificates`** — §3.1 whole. Validation: `capped scripts/ci --diff`
   as rewritten by this lane, i.e. without step 19 and `--slow`; the slow row
   runs fresh and its wall time is recorded in the lane's evidence README (the
   one number this cull wants). Deletes ~1,000 lines of tooling and the
   records directory.
2. **`cull/controls`** — §3.2 and §3.3: `defaultTargets` = everything, one
   `lake build`; steps 1/43 gone; the poison/mutant controls out of 20–27;
   `check-method-identity` deleted (its content is steps 18 and 31);
   `check-unseq-scheduler` to the `--diff` tier without its audit;
   `check-equations` and `check-declarations` slimmed. Validation: fast tier.
3. **`cull/ci-rewrite`** — §4: `scripts/ci` rewritten to the two tiers with the
   speedbump heading; self-tests out (§3.4); the scan steps merged; the baseline
   branches shared; the reverse re-pin report dropped and alternation survival
   folded into `coverage-baseline-diff`; `tools/reconcile-records` out of the
   gate. Validation: fast tier, then one `--diff`.
4. **`cull/charter`** — §5 into `CLAUDE.md`; README «Getting started» and the
   CI workflow (push/PR = fast tier, nightly = `--diff`); an accounting table
   of every removed step in the lane's evidence README, in the
   `docs/2026-09-16_typed-profiles-parked.md` §1 mold, so that no step is
   silently dropped; the «withdrawn» notes on the certificate docs.

Lanes 1 and 2 are independent and can run in parallel; 3 follows both; 4
follows 3. Each lane is small enough to audit in one sitting.

## 7. Decisions this plan needs ([USER]; numbered for the reply)

- **D1** Delete the certificate apparatus and merge-protocol step 5a; the
  `tier=slow` row runs fresh on every `--diff` (§3.1). The user's 2026-10-12
  message points this way; this asks for the ruling.
- **D2** Replace the library-receipt registry (the 2026-09-08 mechanism) with
  «`lake build` builds every target» (§3.2) — same intent, no registry.
- **D3** Cut the compiled poison and mutant controls from steps 20–27 (§3.3);
  the core totality audit over the real modules stays as the one machine check
  of the doctrine.
- **D4** The five `scripts/test-*` self-tests leave the gate and become
  hand-run-on-change tools (§3.4); the `check-equations` and `check-pool-spec`
  in-script self-tests go the same way.
- **D5** Speedbumps run inside `scripts/ci` under their own heading,
  report-only, RED visible, read at the merge ask (§4, §5). Alternative: a
  separate `scripts/speedbumps`; not recommended (two commands to remember).
- **D6** Nightly CI runs `--diff`; push/PR runs the fast tier with
  `GOLEAN_ALLOW_NO_DIFF=1` as today.
- **D7** `tools/reconcile-records` leaves the gate (hand-run instrument); the
  reverse re-pin report is deleted.
- **D8** The `CLAUDE.md` text of §5 as the standing rule (a charter edit is the
  user's); lane 4 applies it once ruled.
- **D9** Lane order and parallelism as in §6, or one lane for all of it.

## 8. This lane's record

Records-only lane (one new file under `docs/`); no runtime, gate or wire
change; the Lean build was NOT run and the gate was NOT run (per the [USER]).
Sources read: `scripts/ci` whole, every `scripts/check-*`/`test-*` header and
the small wrappers in full, `tools/certification.py` (`inputs`/`build`),
`tools/ci_libraries.py`, `tools/admission-check.py`, `scripts/check-equations`
whole, `scripts/diff-coverage` (parallelism, tiers, cache path), `lakefile.toml`,
`.github/workflows/lean_action_ci.yml`, the two timing receipts on this box,
the committed gate tails of 2026-10-01..11, `docs/2026-09-05_project-gate-audit.md`
F8/F13, `docs/operational-lessons.md` §«A cached certification…», and the
migration plan §4, §7, §9.

## 9. Accounting — as landed (2026-10-12, [USER] «Yes, agree on all - do it»)

Branch `cull/gate-1012`, one commit per lane (the §6 lanes as commits on one
branch rather than four branches: the [USER] cannot sign off merges mid-flight;
each commit is one lane and auditable alone — [AGENT] choice under D9).

| §2 row | as landed | where |
|---|---|---|
| 1, 43 | CUT; replaced by `defaultTargets` = every target + the Tests/ ownership set check | lane 2: `lakefile.toml`, `scripts/ci` |
| 3 | GATE, unchanged | `scripts/ci` |
| 4, 5, 6, 16 | GATE, one scan step; gained a `partial`-declaration check over `GoLean/GoCore/` (charter rule, previously only in the admission preflight) | `scripts/ci` |
| 7, 8, 9, 10, 12, 13, 15, 17, 28 | SPEEDBUMP, report-only, both tiers, before the build; the self-tests inside 12 and 13 no longer run; 28 keeps its sub-second python self-tests (no flag, not worth surgery) | `scripts/ci` |
| 11, 14, 30, 36 | CUT from the gate; the five `scripts/test-*` stay as hand-run tools | `scripts/test-*` |
| 18 | GATE, plain `lake build` of every target, warning-free | `scripts/ci` |
| 19 | CUT with the apparatus; `--slow` refused by name | lane 1 |
| 20 | GATE; the five poison compiles gone | `tools/core-audit.py`, `scripts/check-core-audit` |
| 21 | out of ci (its library builds in the default build; the preflight's tokens are the ci scan's); `check-admission` stays as the opt-in full check without the poison modes | `scripts/check-admission`, `tools/admission-check.py` |
| 22 | GATE, slim: no hand re-elaboration, no poison audit | `scripts/check-declarations` |
| 23, 26, 29 | GATE, unchanged | `scripts/ci` |
| 24 | GATE, slim — kept rather than deleted (deviation from §2): the fixture-producing Go tests plus the Lean strict-decoder read are a real cross-boundary test `lake build` does not run; the poison compile and dispatch audit gone | `scripts/check-method-identity` |
| 25 | GATE under `--diff`; its separate axiom audit gone | `scripts/check-unseq-scheduler` |
| 27 | GATE, slim: build + client run + enrollment + regex guard + import whitelist; the twelve mutants gone | `scripts/check-equations` |
| 31, 32, 33 | GATE, two `go test` invocations in one step | `scripts/ci` |
| 34 | GATE, unchanged | `scripts/ci` |
| 35, 37 | GATE under `--diff`, every row fresh; the former `tier=slow` row is an ordinary `engine=dedup` membership row | lane 1 |
| 38 | SPEEDBUMP under `--diff` | `scripts/ci` |
| 39, 40 | GATE, one shared `judge_record` | `scripts/ci` |
| 41 | GATE, forward flips + alternation survival (kept as a call in the guard: it compares two versions of a baseline, the guard's job, not `coverage-baseline-diff`'s) | `scripts/ci` |
| 41b | CUT (the reverse report) | — |
| 42 | out of the gate; rule C9 deleted with the certificates; runs by hand | `tools/reconcile-records` |

Deleted files: `tools/certification.py`, `tools/test_certification.py`,
`scripts/build-certified`, `scripts/check-certification`, `baselines/certified/`,
`tools/ci_libraries.py`, `tools/test_ci_libraries.py`, `scripts/ci-libraries.json`,
`tools/typed_audit.py`, `tools/test_typed_audit.py`, `tools/method-identity-audit.py`,
`tools/method-identity-dispatch.py`, `tools/declaration-audit.py`,
`Tests/{MethodIdentity,Declaration,GoCoreAdmission,UnseqScheduler}Audit.lean`.
`scripts/ci`: 1286 → 413 lines. Charter: «The gates» replaced, step 5a deleted
(lane 4). Workflow: nightly and dispatch run `--diff`.

Operational note for worktrees: `deps/` is gitignored and lives in the primary
checkout; a lane worktree needs it (`ln -s <primary>/deps deps` or
`scripts/setup-deps`), or six checks refuse by name (the frontend's stdlib root,
spec anchors, imported-goose verbatim, the stdlib register, two `go test`s).

Measured on this box (milner-oath, 32 cores, warm `.lake`, box default cap
32 G → 4 Lean threads), captured exit codes, no tails committed:

- fast tier: 47 s wall; RESULT: FAIL on exactly the two «NO recorded run»
  baseline steps (this box had no corpus record yet), every other gate step
  and every speedbump ok.
- `--diff` at the clean tip `21af8d1b`, under the box-wide build lock: **RESULT:
  PASS, 802 s wall**, every gate step and every speedbump ok; differential
  3936/3936 no regression (3705 PASS / 231 FAIL, the r75 figures), negative
  394/394 no regression, 32 jobs, K=32. The former `tier=slow` row
  `imported-goose/channel/google-search` enumerated fresh — 6 observations,
  6.28 M dedup steps, `members=6` met — inside the shared 300 s budget: no
  timeout, no cache, no certificate. Of the 802 s, roughly 90 s is the fast
  tier, ~540 s the differential corpus, ~30 s the negative corpus, ~100 s the
  unseq scheduler and the rest the baselines and regenerations; the corpus is
  now two thirds of the merge gate, so the next lever (not in this cull, a
  [USER] call) is the corpus run itself: the per-case `go run
  ./tools/nativefrontend` could be one build per run, and the strict lane's
  three invariance streams are four interpreter runs per case.

D10 — RULED ([USER] Mike 2026-10-12, verbatim: «the global rule is intended to
mean any such records should be useful with a high bar for evidence»): the global
«Artifacts: rebuild or push, never hoard» rule and `docs/architecture-rules.md`
«Evidence on main» do not conflict; a committed record must clear a high bar of
usefulness. This branch commits no gate tails (the conclusions are in the commit
messages and above); the existing `docs/evidence/` records stand under that bar.

**Triage applied** ([USER] Mike 2026-10-12: «agree with the remediation plan -
go ahead when ready»; the assessment: a tenth of the records cleared the bar),
branch `evidence/triage-1012` off the cull branch, pre-triage tip `63c9ea65`:
deleted whole 106 of 179 directories (15 train stamps, 31 audit/review
transcripts whose findings are in their dated docs, the rest cited by no
living doc, code or commit message); 2 reduced to their README; in the 71
kept records 165 gate tails and 11 dumps over 256 KiB deleted; the two
`fr25_test.go` fixtures moved to `tools/nativefrontend/testdata/fr25/` (a
test read evidence at runtime — a fixture, not a record). After: 73
directories, 1205 files, 6.2 MB. `scripts/check-evidence-size`, its self-test
and `SIZE-ALLOWLIST.tsv` retired (the bar is the rule, not a byte cap);
`docs/architecture-rules.md` «Evidence on main» and `docs/evidence/README.md`
restated. Not done here (judgment per probe, a separate lane): promoting
probes that pin semantics into `Corpus/` cases, and a second pass over the
reproducible outputs still inside the kept records.
