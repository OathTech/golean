[AGENT] fix-round (2026-09-15): moved here from the lane worktree root so the tracked root `HANDOFF.md` on main is left unchanged by this lane; content below, with the audit corrections applied.

# HANDOFF — lane `fix/review-boundary-0911` (BUG-108 / BUG-109 / BUG-110)

[AGENT] worker, 2026-09-12. Branch `fix/review-boundary-0911`, worktree
`.claude/worktrees/fix-review-boundary`, cut from main `a461ed8b`. Authority:
[USER] Mike 2026-09-11, verbatim, relayed by the [AGENT] coordinator — cite as
relayed: «Great, go ahead and land this, then launch the lanes», on
`docs/2026-09-11_review-dispositions.md` §4 step 1; BUG-109's policy: «Yes,
refuse non-1.26». State: BRANCH-COMPLETE, parked on the branch; NOT merged, NOT
pushed (both are the [USER]'s separate sign-offs); the adversarial-audit ask is
posed in the final report. Every gate line, transcript and measurement:
`docs/evidence/2026-09-11_review-boundary/README.md` (corrected by the audit fix round, final section).

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
6. Decode cost of the strict parser — **CORRECTED by audit F2**
   (`docs/2026-09-15_review-boundary-audit.md`, [AGENT] 2026-09-15). The superseded lane text,
   kept visible: «`IO.FS.readFile` vs `readBinFile`: the 11 MB twin wire decodes 2.3× FASTER
   after S3; the hypothesis (the `String` build in `readFile` dominates on large files) is
   recorded, not isolated». The speed-up does NOT reproduce and is withdrawn with its
   hypothesis: the lane's timing binary (`dae23a5c…`) was not the committed one (`44c8ed60…`,
   the certified record's receipt). Measurement of record (audit; A/B interleaved, three
   separate passes, nine runs each, medians): twin 11.4 MB 0.132 s PRE → 0.214 s POST (+62%);
   largest corpus wire 3.5 MB 0.049 s → 0.081 s (+65%); 1.5 KB fixture wire 0.020 s → 0.020 s
   (unchanged). The strict parser costs decode time on the large wires. What stands: the cost is
   far inside the runner's 30 s per-case budget and the parser is not weakened. No performance
   action owed.

7. Callee-signature cross-check of the `resultTypes` ENTRIES (audit F1 disposition (a); owed):
   a post-decode pass that checks each entry against the callee's declared results — the decoder
   already holds them (`funcs`/`methods` for `call`, the callee expression's `type` for
   `call-value`) — refusing BY NAME, which would also make expression-statement vectors boundary
   refusals rather than run-time `stuck`/`error`. Today only the ARITY is validated; the entry
   types are trusted (audit cases i08/i10/i13 run and answer 42 with `resultTypes:[string]` on
   an `int`-returning callee). Code change, next lane.

8. OUT OF LANE, for the STATE-CLEANUP arc (audit F1 side observation): the machine stores an int
   into a `string`-typed discard cell without objection — a typing/normalization contract
   question about the machine's state, not a BUG-110 residual.

9. Unify `libraryBuildContext()` (`tools/nativefrontend/stdlibsource.go`, ~line 554, pins
   `CgoEnabled = false` and documents itself as «the ORACLE's build context») with
   `fileselect.go`'s pinned context (`CgoEnabled = true`) — two build contexts in one frontend,
   disagreeing (audit F3). No selection effect today: the audit verified that no
   `stdlibSourceAllowed` package's file set differs between the two cgo states, so the stdlib
   pin manifest would not move. Owed, code change, next lane.

10. The `godebug` go.mod directive (audit N1): `godebug default=go1.21` is accepted silently
    (case g12) and is inert under the oracle's `GO111MODULE=off`. Beside the BUG-109 owed items
    `//go:build go1.N`, `//go:debug` lines and `toolchain`.

11. The over-depth refusal message names BOTH bounds («declaration envelope 64, production wire
    1024», `GoLean/StrictJsonParse.lean:130`) instead of the one in force (audit N2). Cosmetic.
    NOT changed by this fix round: it is a CODE message, and a code edit here would re-stale the
    certified record and force another slow gate. Owed, next lane.

12. `scripts/check-wire-boundary`'s surrogate controls say they mutate «the UNREAD `package`
    field»; `"package":"main"` first occurs inside `fileOrder[0]` (alphabetical key order), so
    that is where the mutation lands (audit N3). Both fields are unread and the control is
    VALID — the comment is wrong, not the gate. Comment-only code change, owed, next lane.

## PENDING [USER]

- Owed item 1 (harness generator file selection): a trust-surface-#2 change — not made here.
- Whether the constraint policy under a now-pinned build context should model `//go:build`
  platform tags (today: refused, as before). Not changed here; the pin makes it possible.
- Pin `CGO_ENABLED` in the differential runner's oracle invocation (`scripts/diff-coverage`
  `go_run_oracle` pins `GO111MODULE`/`GODEBUG`/`GOTRACEBACK` only; the value is host-inherited)
  — or assert it in the oracle pin guard. Trusted surface #2 — PENDING [USER] (audit F3 (ii)).
  Direction is safe either way: under `CGO_ENABLED=0` the oracle selects differently (f47, f50)
  but the frontend refuses both shapes by name, so the divergence is red, never silent.
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

## Audit fix round (2026-09-15)

[AGENT] fix-round worker, 2026-09-15. Authority: [USER] Mike 2026-09-15, verbatim, relayed by
the [AGENT] coordinator — cite as relayed: «Go ahead and launch the autit». The audit is
`docs/2026-09-15_review-boundary-audit.md` (branch `review/review-boundary-0911`, `96d65e07`;
its evidence dir is `docs/evidence/2026-09-15_review-boundary-audit/` on that branch).
**Verdict: FIX-FIRST, RECORDS-ONLY** — no wrong answer, no fail-open with an observable effect;
the code fixes of S1a/S1b/S2/S3 stand as landed.

This round touched **no code file** — not `GoLean/`, not `tools/`, not `scripts/`, not a comment
in any of them. A code edit would re-stale the certified record and force another slow gate.
Changed paths: `docs/BUGS.md`, `docs/evidence/2026-09-11_review-boundary/{README.md,
s3-decode-timing.txt}`, this file (moved from the worktree root), and the root `HANDOFF.md`
(restored to main's content at `a461ed8b`). Superseded wording is kept visible in place under a
short banner, per this repo's convention, rather than silently overwritten.

| finding | what was wrong | where the correction landed |
|---|---|---|
| **F1** (fail-open, low; no observable) | BUG-110's fixed paragraph invited the reading «the `resultTypes` vector is validated, never reconstructed». Only the ARITY is validated at the boundary; the entry TYPES are trusted (i08/i10/i13 run and answer 42 with `resultTypes:[string]` on `int`-returning callees), and expression-statement vectors (i04–i06) are caught only at RUN time by the machine (`stuck`/`error`) — fail-closed, but not a by-name boundary refusal. | `docs/BUGS.md` BUG-110: a «narrowed by audit F1» note after the (2) paragraph. `docs/evidence/2026-09-11_review-boundary/README.md` S3: «ARITY-checked» with the F1 pointer. Owed item 7 (the callee-signature cross-check, audit disposition (a)) and owed item 8 (the OUT OF LANE state-cleanup observation: the machine stores an int into a `string`-typed discard cell without objection) above. |
| **F2** (records claim) | The twin decode was recorded as «0.124 s → 0.055 s (FASTER …)» with a `readFile`/`String`-build hypothesis, in three tracked texts. It does not reproduce: the lane's timing binary (`dae23a5c…`) is not the committed one (`44c8ed60…`). Audit measurement (3 interleaved passes, 9 runs each, medians): twin 11.4 MB 0.132 → 0.214 s (+62%); largest corpus wire 3.5 MB 0.049 → 0.081 s (+65%); 1.5 KB fixture 0.020 s unchanged. Conclusion that stands: far inside the 30 s per-case budget; the parser is not weakened. | `docs/BUGS.md` BUG-110's timing sentence (superseded text quoted, corrected table in prose). `README.md` "Timing verdict" (superseded text quoted, measurement-of-record table) and the `s3-decode-timing.txt` row of its file table. `s3-decode-timing.txt` itself: a `#` banner at the head, transcript kept verbatim below. Owed item 6 above. |
| **F3** (records claim + consistency) | BUG-108's fixed paragraph called cgo=true «the oracle's `CGO_ENABLED=1` default». The differential runner does NOT pin `CGO_ENABLED` (`scripts/diff-coverage` `go_run_oracle` pins `GO111MODULE`/`GODEBUG`/`GOTRACEBACK` only; the value is host-inherited). Under `CGO_ENABLED=0` the oracle selects differently (f47, f50) — but the frontend refuses both cgo shapes BY NAME under either host state, so the divergence is red, never silent. Separately the frontend carries a SECOND build context, `libraryBuildContext()` (`tools/nativefrontend/stdlibsource.go` ~line 554), pinning cgo=FALSE; no selection effect today over all allowed stdlib packages (audit-verified), but an inconsistency. | `docs/BUGS.md` BUG-108: the clause reworded to «the FRONTEND's pin», plus a «superseded by audit F3» note carrying the old wording and both owed items. `README.md` S1b: an F3 pointer paragraph. Owed item 9 (unify the two contexts — code change, next lane) and the new PENDING [USER] entry (pin `CGO_ENABLED` in the oracle invocation — trusted surface #2) above. |
| **F4** (records claim, minor) | The twelve gate lines are prose; no `ci` tail is tracked. | `README.md`, one sentence after the gate table: the train's step-5a `scripts/ci --slow` at the merged tip produces the tails of record, tracked with the 5a records commit. No tails were fabricated. |
| **N1** (nit) | BUG-109's owed list omitted the `godebug` go.mod directive (accepted silently, case g12; inert under the oracle's `GO111MODULE=off`). | `docs/BUGS.md` BUG-109's OUT OF SCOPE list, beside `//go:build go1.N`, `//go:debug` and `toolchain`; owed item 10 above. |
| **N2** (nit) | The over-depth refusal prints both bounds instead of the effective one (`GoLean/StrictJsonParse.lean:130`). | **NOT fixed** — it is a CODE message and this round touches no code. Recorded as owed item 11 above. (Audit N3, the `check-wire-boundary` comment, is recorded the same way as owed item 12.) |

Audit findings deliberately NOT actioned: F5 (scope — clean), F6 (performance — «no action»; F2 is
the records half of it), N4–N8 (recorded by the audit itself; N5/N6 rest on PENDING [USER] items
already listed above). The two PENDING [USER] items are NOT decided here.

### The merge train's next command (protocol steps 5 / 5a) — unchanged from the original handoff

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

If `--ff-only` refuses, rebase onto the current `main`, re-gate and re-ask (merge protocol step 5).
Merge and push remain the [USER]'s separate, at-that-moment sign-offs; this fix round performed
neither.
