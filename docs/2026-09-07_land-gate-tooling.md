# Landing chunk L2 `land/gate-tooling` — the evidence-size gate, and why the harness rework did not ride along (2026-09-07)

[AGENT] landing worker, under the coordinator's brief for decomposing
`typed-consumer-sprint` (tip `7edc298f`, 96 commits over main `47195683`)
into reviewable chunks. Inputs: `CLAUDE.md`, `AGENTS.md`, auditor A's and
auditor B's landing reviews (sprint worktree `.tmp/landing-review/`).

[USER] ruling (Mike, 2026-09-07, relayed by the [AGENT] coordinator — cite
as relayed): «The evidence blob should not land, and generally we should
not dump big evidence bundles on main (they can't be easily hosted on GH
for one). … We'll want to decompose and land in sane chunks that can be
reviewed. And where appropriate fix some of the issues, eg. the choice
tape stuff».

Method: path selection from the committed sprint tip
(`git checkout typed-consumer-sprint -- <paths>`, every hunk read), never a
merge. Branch `land/gate-tooling` off main, worktree
`.claude/worktrees/land-gate-tooling`.

## 1. What landed (this commit)

| path | what |
|---|---|
| `scripts/check-evidence-size` (new) | the evidence-size gate (§4) |
| `scripts/test-check-evidence-size` (new) | its self-test against a scratch repo under `.tmp/` (18 cases) |
| `docs/evidence/SIZE-ALLOWLIST.tsv` (new) | the 18 pre-existing offenders on main, frozen (§5) |
| `scripts/ci` | one additive step, `evidence-on-main size gate` (self-test first, then the index); can only add a red |
| `AGENTS.md` | "Evidence on main": the ruling verbatim (relayed), the caps, the archive-branch + `MANIFEST.tsv` convention |
| `CLAUDE.md` | one sentence on the gates bullet pointing at the check |
| `docs/evidence/README.md` | rule 9 (the caps), and the "nothing here is gate-enforced" sentence corrected |
| `docs/ARCHIVE.md` | the section where evidence archive branches get listed (none yet) |
| `docs/evidence/2026-09-07_land-gate-tooling/` | this chunk's record: checker output on main and on the tip, self-test output, gate tail |

Nothing else. In particular NO sprint code lands in this commit — see §2
and §6 for why the chunk came out smaller than the brief expected.

## 2. What did NOT land, and which chunk owns it

| sprint path(s) | disposition | why |
|---|---|---|
| `scripts/ci` — all 12 additive steps | → L1 (Boolean/Recovery/abort-observation/recovery-terminal/declarations), L3 (`check-string-members.py`), L4 (`check-observer-controls.py`, `check-observer-tools.py`) | each calls a tool or Lean module that lands in a later chunk; a step whose tool is absent is a red, not a gate |
| `lakefile.toml` (+38: 10 `lean_lib`s, 4 `InterfaceTests` globs) | → L1, excluded whole | every added lib/glob names a Lean test module of the proof chunk; nothing here needs it. Auditor A: `defaultTargets` and `GoLean` unchanged; the Iris customer stays in `spikes/` with its own lakefile — nothing was ever added to the default build, so nothing had to be refused on that ground |
| `scripts/check-declarations` (A-R11) | → L1, excluded with this note | it prints sha256s but never compares them, and its fixture is a `mktemp`, not a tracked pin; the Lean modules and `declaration.go` it exercises are L1's. Fix owed there: `sha256sum -c` against a tracked expected-bytes file, or rename the step so it does not claim to be a pin |
| `scripts/check-interface`(+`.py`) | → L1 | only adds the new Lean modules to the module list |
| `scripts/coverage-manifest`, `scripts/coverage-baseline-diff` (`string-member` vocabulary) | → L3 | the string-member lane |
| `tools/coverageharness/*`, `scripts/diff-coverage`, `scripts/test-lane-validation`, `scripts/gotest-triage`, `scripts/membership-sampling`, `scripts/cedar-census` | → L4, PREPARED on `prep/observer-terminal-harness` (§6) | the brief put these in L2 believing them baseline-neutral; measured, they are not |
| `AGENTS.md` sprint-pointer hunk, `CLAUDE.md` merge-protocol retitle | excluded | the brief: nothing else in those files; auditor B R4 rejects the retitle outright |
| `scripts/capped` | verified byte-identical to main; not taken | — |

## 3. Fixes applied (all [AGENT], landing review 2026-09-07)

Only the evidence gate is in this commit; the harness fixes live on the prep
branch (§6) so the L4 worker starts from a fixed state.

- **A-R6 (crash-channel fallback)** — `crashview.go`, `main.go`: the same-run
  channel is mandatory on EVERY classification path. No
  `--crash-report/--crash-registered` pair → usage refusal (exit 2). Empty
  acknowledgement → `crash evidence: no hook registration acknowledgement —
  the oracle's _goleanSetupCrash never ran (the subject aborted before main's
  first statement, or the hook was not installed)`. Exit 2 with an EMPTY
  runtime report → `runtime wrote no crash report — not an authenticated
  runtime abort`. ok/race require ack + empty report; abort requires ack +
  report as the byte-identical stderr suffix. The raw-marker fallback
  survives only where it must — the fatal message line, printed before
  `m.dying` — and only under an authenticated trace. The three zero-evidence
  wrappers were retired and every test fixture now names its runtime-written
  report. New: `evidence_test.go` — `TestMissingRegistrationRefusedByName`
  (every entry point, ok/race/panic/fatal/message/record, against the
  pre-`main` channel state; and the same bytes classify with a registered
  channel, so the red is attributable to the channel alone),
  `TestNoEvidenceRefused`, `TestAbortWithoutCrashReportRefused`.
- **A-R8 (`grep -F` alternation)** — `scripts/diff-coverage`: an
  `expected_reason` that is empty or contains LF/CR is a manifest refusal
  (`expected_reason must be one non-empty line`), so the fixed-string match
  is exact by construction, not by accident of the TSV format.
- **Chain-shape pin (new, found doing R6)** — inside a channel copy, every LF
  before the trace header must be followed by TAB (`printpanics` prints later
  chain entries as `\n\tpanic: `; `printindented` renders payload LFs as
  `\n\t`), except the single un-indented `[signal … code=… addr=… pc=…]` line
  `dopanic_m` prints after the chain for a signal-induced panic. A bare
  `\npanic: ` in a copy is therefore not runtime-written and refuses. The
  first cut of this pin lacked the signal exception and refused every nil
  dereference in the corpus (50+ rows); the record is kept
  (`run1-overstrict-pin/` on the prep branch) and `TestSignalLineShape` pins
  both directions.
- **A-R9 (oracle `main()` spliced pre-compile)** — kept on the prep branch:
  the splice is a byte-offset insertion of `_goleanSetupCrash();` into a
  FRESH copy (`TestOracleCopyPreservesSemanticSources` proves the semantic
  input is untouched and the edit is exactly that insertion); the hook opens
  and writes only its two owned files before the subject's first statement.
  It is inert on the observation by construction; it is NOT byte-inert on
  the oracle binary, and the brief's "covered by a test that proves it" is
  met for the source, not the observation — L4 should say so plainly.
- **A-R10 (`GOTRACEBACK=system`)** — kept with its provenance (manifest lines
  `go_traceback system`, `go_crash_channel same-run-setcrashoutput-v1`). It is
  a change to trusted surface #2's invocation and needs the L4 packet.
- **A-R11** — not fixable here (§2); excluded with a note.

## 4. The evidence-size gate (design)

- **Judges the INDEX** (`git ls-files -s`): what `git commit` would record.
  Untracked files are not judged; a staged file is. At a clean tip, index =
  HEAD. Sizes from `git cat-file --batch-check` on the index blobs; no
  working-tree reads, so the verdict does not depend on unstaged edits.
- **Rules**, each named in the refusal line `check-evidence-size: <rule>:
  <path>: <detail>`: `file-size` (> 256 KiB), `dir-size` (top-level
  `docs/evidence/<dir>/`, recursive, > 4 MiB), `archive-ext` (`.tar .tgz .gz
  .zip .xz .zst .7z`, case-insensitive), `source-copy` (blob byte-identical
  to a tracked blob outside `docs/evidence/`; the EMPTY blob is exempt — an
  empty file has no content to be a copy of, and main carries ~90 empty
  `.stderr`/`.err` records), `not-a-file` (symlink/gitlink under evidence).
- **Caps are PROPOSED [AGENT] 2026-09-07**, defined once at the top of the
  script with the ruling quoted; ratification is the user's. Rationale for
  the numbers: main's evidence median dir is ~25 KB and all 640 gate tails
  on the sprint are under 100 KB (auditor B), so 256 KiB/file and 4 MiB/dir
  bound "records" generously while catching every class auditor B named
  (archives, full-run tables, wire dumps, source trees).
- **Allowlist, shrink-only**: rows `rule TAB path TAB reason TAB date`; every
  row must carry the freeze date `2026-09-07` (any other date → refused:
  "the allowlist may only shrink"); a row that no longer matches a live
  offender is refused as stale (so moving bytes to an archive branch forces
  the row's deletion); a malformed row is exit 2. Anything not listed fails.
- **Exit codes**: 0 clean, 1 offender(s)/stale/late-dated entry, 2 could not
  run (git failure, malformed allowlist, bad `--repo`). A gate that cannot
  run fails.
- **Self-test first**: `scripts/test-check-evidence-size` builds a scratch
  repo under the checkout's `.tmp/` (never `/tmp`; repo-local git identity
  only), exercises all five rules, the index-vs-untracked semantics, the
  allowlist's accept/stale/late-date/malformed/unknown-rule/outside-path
  paths, and the shrink obligation; 18 cases. The ci step runs it before the
  real check so a broken checker is a red, not a silent pass.

## 5. The allowlist — what main already carried

Run against main `47195683` with no allowlist, the checker names 18
offenders (`docs/evidence/2026-09-07_land-gate-tooling/check-evidence-size.main-no-allowlist.txt`):
16 `file-size` (four whole-corpus choice-trace dumps and a tracer batch in
`2026-09-04_c-arc-gu`, two more choice-trace dumps in `hygiene-wave3` and
`c-arc-b4`, four frontend wire emits in `fr24-fr25`, the cedar-go
lowering-diagnostic report, two `--slow` result tables, two BUG-103 full
result tables and a 3,691-file sha256 inventory), 1 `dir-size`
(`2026-09-04_c-arc-gu/`, 10.4 MB), 1 `source-copy`
(`2026-09-05_iris-customer-review/Examples.lean.txt` ==
`spikes/iris-customer/GoLeanIris/Examples.lean`), 0 archives. All 18 are
frozen in `docs/evidence/SIZE-ALLOWLIST.tsv` with a one-line description
from the owning README and the date; each is an archive-branch candidate,
and each row disappears when its bytes move. Total evidence on main today:
1,425 files / 26.5 MB in 79 dirs.

## 6. Why the harness did not land here (the brief's STOP condition)

The brief said: land `tools/coverageharness` + the `diff-coverage` rewrite
in L2, run `scripts/ci --diff`, and "if the driver rewrite flips any row,
STOP and report the rows". It flips rows, and the sprint's own baseline
header already said so: its 2026-09-06 BUG-106 re-pin records
`sync/mutex-unlock-fatal/during-panic-unwind PASS -> FAIL/go-observation`,
and the sprint's `split_test.go` pins that refusal. Auditor A's "cached
bytes preserved" is about `--read-observation` returning stdout bytes
unchanged (the certified set), not about the classification of aborts.

Measured (focused scope, all 410 non-ok rows, `GOLEAN_COVERAGE_JOBS=2`,
record on the prep branch under
`docs/evidence/2026-09-07_observer-terminal-prep/`): with the prepared
harness — R6 uniform, as the brief ruled — **six PASS rows go red and one
FAIL row changes stage; nothing else moves; race 36/36 clean; lane self-test
ok**:

| row | baseline → prepared harness | cause |
|---|---|---|
| `sync/mutex-unlock-fatal/during-panic-unwind` | PASS → FAIL/go-observation | BUG-106 (fatal message before `m.dying` is unauthenticated) |
| `init/init-panic`, `noodler/initpanic/panic`, `noodler/initpanic/var-panic`, `noodler/initpanic/deadlock` | PASS → FAIL/go-observation | pre-`main` abort: no acknowledgement can exist (the hook is `main()`'s first statement); uniform R6 refuses by name |
| `init/quarantined-var-panicking/sibling` | FAIL/frontend-export → FAIL/go-observation | same; the oracle side now fails before frontend export is reached |

Every one of these is a fail-closed red replacing a classification that
main's driver made from unauthenticated bytes, so the direction is the
doctrine's. But a PASS→non-PASS flip needs a BUGS.md `Cases:` line per row
and a re-pin with a written reason, and `GOTRACEBACK=system` plus the oracle
splice change how trusted surface #2 is invoked — auditor B's component 5,
"split out, own lane, needs a §7 packet". That is the observer/terminal
chunk's decision, and the four pre-`main` rows pose a specific question for
it: rule a NAMED exception (an empty ack is itself a reliable pre-`main`
signal, and the strict raw fallback is stricter than main's classifier), or
keep them red. The prep branch `prep/observer-terminal-harness`
(`b1407cc5`, parent main `47195683`) carries the code with R6/R8 and the
chain-shape pin fixed, tests green, so L4 starts from a fixed state rather
than re-deriving it.

So this commit lands with the baseline UNMOVED, which is what the brief
required of it; the harness measurement is reported, not adjudicated.

## 7. Gate

`GOLEAN_COVERAGE_JOBS=2 scripts/capped scripts/ci --diff` at the clean
committed tip `485c5b7f` (kept reachable as
`refs/snapshots/land-gate-tooling-pre-amend`): **RESULT: PASS**, `baseline
diff FULL (3598/3598, no regression)`, `negative baseline diff (no
regression)`, recorded meta `git_commit 485c5b7f… git_dirty false
go_toolchain go1.26.5 go_drift_actual false jobs 2`; the re-pin guard had
nothing to say (no baseline changed). Tail:
`docs/evidence/2026-09-07_land-gate-tooling/ci-diff-tail.txt`.

Recording that tail needs a commit after the run, so the final commit is
an amend of `485c5b7f` that differs from it ONLY by the tail file and by
this section's and the evidence README's wording (they could not name the
result before it existed) — verify with
`git diff refs/snapshots/land-gate-tooling-pre-amend HEAD --stat`. The gate
was not re-run at the amended tip: the delta is three documentation files
under `docs/`, none of which any gate step reads except the evidence-size
check, which was re-run at the amended tip (PASS, 0 new).

`go test ./tools/...` on main fails to BUILD `tools/raftsubject/overlay/raftpb`
(GOPATH-mode imports `raftpb`/`tracker` absent) — pre-existing on main,
unrelated to this chunk; `scripts/ci` tests `./tools/nativefrontend` and
`./tools/lowerdiag` explicitly. Both pass, as does `go vet` on them and on
`./tools/coverageharness` (main's and the prep branch's).

## 8. Open for the coordinator / user

1. Ratify or adjust the caps (§4) — [AGENT]-proposed.
2. L4: the prep branch, BUG-106's BUGS.md entry, a `Cases:` line per flipped
   row, the pre-`main` question, `--slow` if wire/lowering is touched (it is
   not, on the prep branch).
3. The sprint's 114 MB evidence payload: auditor B's §4 manifest is the
   plan; with this gate on main, landing it as-is is now a red by
   construction (archives, source copies, >4 MiB dirs).
4. Auditor B R12 (`docs/evidence/README.md` unamended) is closed by rule 9.
