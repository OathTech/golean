# HANDOFF — lane `fix/review-boundary-0911` (BUG-108 / BUG-109 / BUG-110)

[AGENT] worker, 2026-09-12. Branch `fix/review-boundary-0911`, worktree
`.claude/worktrees/fix-review-boundary`, cut from main `a461ed8b`. Authority:
[USER] Mike 2026-09-11, verbatim, relayed by the [AGENT] coordinator — cite as
relayed: «Great, go ahead and land this, then launch the lanes», on
`docs/2026-09-11_review-dispositions.md` §4 step 1; BUG-109's policy: «Yes,
refuse non-1.26». State: BRANCH-COMPLETE, parked on the branch; NOT merged, NOT
pushed (both are the [USER]'s separate sign-offs); the adversarial-audit ask is
posed in the final report. Every gate line, transcript and measurement:
`docs/evidence/2026-09-11_review-boundary/README.md`.

## What landed, per stage

| stage | commit | what | gate on the committed tree |
|---|---|---|---|
| S1a | `6264f152` | BUG-108 red-first: 11 rows `Corpus/coverage/exec/source-selection/*` (5 FAIL/differential: an excluded sibling's `init` ran, GoLean 2 vs gc 1; 2 FAIL/frontend-export; 4 PASS controls), baseline re-pinned 3676 = 3421/255, BUG-108 → `Pinned-by: differential` with the 7 reds on its Cases line | `ci --diff` EXIT=1 (952 s; reds = exactly the not-yet-pinned rows), then `ci` fast EXIT=0 (575 s) |
| S1b | `60874ada` | BUG-108 FIX: `tools/nativefrontend/fileselect.go` — the file set is `go/build.Context.ImportDir` under the pinned target (linux/amd64, gc, cgo enabled, no -tags) for the main package and every imported local package; InvalidGoFiles / CgoFiles / assembly / MultiplePackageError / NoGoError refuse by name; the standing `//go:build` policy unchanged (one site, `judgeBuildConstraintLine`); the wire gains `buildContext`; the decoder REQUIRES it and refuses any other target (`pinnedSelectionTarget` ↔ `Platform.gcAmd64`); 7 rows FAIL → PASS; twin wire re-pinned 13d8b659… → e1a87725… (only the added key); certified record re-minted; lowerdiag cause rows | `ci --slow` ×2 (EXIT=1 each: stale record → candidate minted, set unchanged), `ci --diff` EXIT=1 (887 s; reds = the 7 flips only), then `ci` fast EXIT=0 (554 s) |
| S2 | `07bc55cb` | BUG-109 FIX: `modfile.go` — nearest `go.mod` (walk-up, main + each imported local package); a `go` directive ≠ 1.26 refuses `…/go.mod declares go 1.21; GoLean implements the Go 1.26 language only`; no/repeated/malformed directive refuses too; no `go.mod` → the pin. NO corpus row (the oracle runs `GO111MODULE=off` in a `*.go`-only copy — a row would be fake); pinned by `modfile_test.go` + the frontend/`lower-diagnose` transcripts | `ci --slow` EXIT=1 (995 s; reds = stale record only → candidate), `ci --diff` EXIT=0 (885 s) |
| S3 | `68761e87` | BUG-110 FIX: `StrictJson.parseBytes` at every production wire read (`CLI.lean` native-json-run + coverage-observations, `ChoiceTrace.loadProgram`); `resultTypes` REQUIRED on every call-shaped node and arity-checked (`decodeResultTypes`/`requireResultTypes`; the `.getD .int` sites and the expr-stmt fallback deleted; TODO F5 discharged); new `scripts/ci` step `scripts/check-wire-boundary` (10 byte-level controls through the real CLI, fixture `Tests/wire-boundary/main.go`) | `ci --slow` EXIT=1 (995 s; the depth FINDING: the 64-deep declaration bound refused 105 real wires — fixed with `wireNestingDepth = 1024`), `ci --slow` EXIT=1 (1149 s; reds = stale record only → candidate), `ci --diff` EXIT=0 (888 s) |

Corpus/baseline state at the tip: 3676 rows = 3428 PASS / 248 FAIL (main had 3665 =
3417/248); 394 negatives unchanged. `check-bugs.sh` ok; backlog unchanged (coverage 10 /
latitude 4 / wrong-answer 0). BUG-108/109/110 all `Status: fixed` (108 by the symmetric
differential rule; 109/110 `Pinned-by: none` with their pins named).

## Baseline movement (each with a full run and the reason in the baseline header)

- S1a: +11 born rows (7 FAIL, 4 PASS). No other movement.
- S1b: the 7 BUG-108 rows FAIL → PASS. No other movement. Twin pin moved (reason in
  `scripts/check-frontend-pins` header + `docs/evidence/…/twin-repin/structural-diff.txt`).
- S2, S3: none.

## Certified record (`imported-goose/channel/google-search`, tier=slow)

The six-member set reproduced IDENTICALLY at every fresh enumeration (S1b ×2, S2, S3). What
moved: the claim's `wire_sha256` 2f1d639f… → 736f1730… (S1b: the wire gained `buildContext`;
the TSV header carries the reason) and the inputs inventory (every stage touches `tools/`,
`scripts/` or `GoLean/`). Each stage's candidate was reviewed (claim/inputs/observations delta
printed) and installed as `baselines/certified/imported-goose__channel__google-search.certified.json`.
A `tools/` edit after a stage's first `--slow` run re-stales the record (S1b run #2 was that
lesson) — finish every `tools/scripts/GoLean` edit, including the lowerdiag cause rows, BEFORE the
first gate of a stage.

## Owed / findings outside this lane's boundary (recorded, not fixed)

1. `tools/coverageharness` (trusted surface #2) still globs `*.go` and parses every file; correct
   for the oracle (gc re-selects in the copy) but an over-refusal on an excluded file with invalid
   syntax — why that shape is a Go unit test, not a row (BUG-108 record). Aligning the harness's
   selection with go/build is a trust-surface-#2 change: PENDING [USER].
2. `tools/lowerdiag/static.go` (report-only lane tooling) still uses `parser.ParseDir` for its
   static census — it may census files gc excludes. Not a gate input.
3. Excluded files that ALSO carry a `//go:build` constraint over-refuse (e.g. `x_windows.go` +
   `//go:build cgo`; gc ignores the file). Fail-closed; lifting it means reimplementing
   go/build's suffix rule or a policy change on constraints under a pinned target.
4. BUG-109 out-of-scope items: per-file `//go:build go1.N` (already refused as reserved tags),
   `//go:debug`, the `toolchain` directive (inert under `GOTOOLCHAIN=local`).
5. `GoLean/CLI.lean` `decodeObservation` (the `observation-eq` comparator) still parses
   OBSERVATION JSON with `Lean.Json.parse` — not a wire; the byte boundary hardened here is the
   wire's. A follow-up if the observation channel is ever treated as adversarial.
6. `IO.FS.readFile` vs `readBinFile`: the 11 MB twin wire decodes 2.3× FASTER after S3; the
   hypothesis (the `String` build in `readFile` dominates on large files) is recorded, not isolated.

## PENDING [USER]

- Owed item 1 (harness generator file selection): a trust-surface-#2 change — not made here.
- Whether the constraint policy under a now-pinned build context should model `//go:build`
  platform tags (today: refused, as before). Not changed here; the pin makes it possible.
- BUG-107 is untouched (its own ruling pending).

## The merge train's next command (protocol steps 5 / 5a)

```sh
cd /home/dev/projects/golean            # primary checkout, parked on main
git update-ref refs/snapshots/<round>/main main
git checkout main && git merge --ff-only fix/review-boundary-0911
scripts/build-certified
python3 tools/certification.py release-check --base refs/snapshots/<round>/main
# exit 1 is EXPECTED: this lane moved the wire (buildContext), the decoder, the frontend and
# scripts/ — inventory AND claim changed. Then, per 5a:
GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow      # fresh re-certification at the merged tip
# review + install artifacts/coverage/membership/imported-goose/channel/google-search/certification-candidate.json
# as baselines/certified/imported-goose__channel__google-search.certified.json; commit as the round's
# 5a records commit; re-run the gate green. A changed six-member set is a FINDING, not a re-pin
# (this lane reproduced the set identically four times).
```
