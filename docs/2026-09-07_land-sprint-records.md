# Landing chunk L6 `land/sprint-records` — the records close-out of the typed-consumer sprint (2026-09-07)

[AGENT] landing worker, lane `land-sprint-records`, worktree
`.claude/worktrees/land-sprint-records`, branch `land/sprint-records` off
main `dd636996`, 2026-09-07. Plan of record:
`docs/2026-09-07_typed-sprint-landing-plan.md` §2.6 (L6 — LAST), §1
(principles), Appendix A (the partition). RECORDS ONLY: no code, corpus,
baseline, gate script or `docs/evidence/` file of any other chunk is
touched; no runtime file changes.

[USER] ruling (Mike, 2026-09-07, verbatim as relayed by the [AGENT]
coordinator — cite as relayed): «The evidence blob should not land, and
generally we should not dump big evidence bundles on main (they can't be
easily hosted on GH for one). Can you make a plan to land this work cleanly?
We'll want to decompose and land in sane chunks that can be reviewed. And
where appropriate fix some of the issues, eg. the choice tape stuff». The
sprint's charter approval (K1–K5, «Agree with all 5», 2026-09-05) and the
rounds 20–24 merge sign-offs are cited via the charter and the handoff, as
relayed.

Inputs read in full: `CLAUDE.md`, `AGENTS.md` (incl. "Evidence on main"),
the landing plan, `docs/2026-09-05_master-plan.md` §7, both landing audits
(`.tmp/landing-review/auditor-{A,B}.md` in the sprint worktree), the four
chunk notes (L3's first from branch `land/panic-text-tape` while round 24
was being rebased, then §7.2 from main after it landed), the sprint's charter and handoff at `7edc298f`, the
untracked pause-state and C1-handoff records in the sprint worktree,
BUG-105–107 on main, `scripts/check-evidence-size`, `tools/reconcile-records`.

## 1. What landed (this chunk)

| path | what |
|---|---|
| `docs/evidence/2026-09-05_typed-consumer-sprint/` (`README.md`, `MANIFEST.tsv`, `manifest/<dir>.tsv` ×78, `source-copies.tsv`, `make-manifest.py`) | the MANIFEST of the sprint's evidence payload that did NOT land: 2,159 files / 114,156,315 B / 78 dirs, one row per file (path, sha256, bytes, origin commit, class), generated from git objects only (§2) |
| `docs/2026-09-05_typed-consumer-sprint-charter.md` | the [USER]-approved charter VERBATIM from `7edc298f` (body byte-identical, verified by sha256), below a landing preface carrying the relay markers (B-R18) and the sprint-scoped reading of K4 |
| `docs/2026-09-05_typed-consumer-sprint-handoff.md` | REWRITTEN, trimmed: authority (relayed), the FINAL O1–O5 table, the CORRECTED decision ledger (B-R15 — the "No critical issue" line withdrawn; eight itemised §7-class issues with reproducer/rule/alternatives/disposition), the BUG numbering reconciliation (B-R17), where everything else lives (incl. the 32 unlanded sprint notes); the 17-checkpoint sprint-era log stays on the archive branch |
| `docs/2026-09-06_typed-sprint-pause-state.md` | the sprint's paused-state snapshot, VERBATIM from the sprint worktree (untracked there — B-R16), below a header stating what it honestly records (PAUSED BY USER; baseline PROVISIONAL; gates exit 143 and 1; V1 claim withdrawn) and that its [USER] attributions are UNQUOTED and confer no standing permission |
| `docs/2026-09-06_c1-contract-handoff.md` | charter §4's C1 deliverable, VERBATIM (untracked in the sprint worktree), marked DRAFT never refreshed; O4 unimplemented |
| `docs/2026-09-07_landing-audit-A.md`, `docs/2026-09-07_landing-audit-B.md` | the two landing audits VERBATIM below prefaces — the source of every `A-Rn`/`B-Rn` id in the plan and the chunk notes (plan §0, §2.6; promised by `docs/ARCHIVE.md`'s sprint entry) |
| `docs/2026-09-05_master-plan.md` | §7.8 addendum (the landing per chunk with commits and gate lines; what did not land; O1–O5; auditor B's F2/F3/F5 table VERBATIM + what L3 adds and does not; owed follow-ups; pending/ratified decisions; the standing evidence rule); bracketed pointers on §7.2's F2/F3/F5 rows and at the end of §7.4.1 |
| `docs/2026-09-07_typed-sprint-landing-plan.md` | a dated status addendum at the top: rounds 20–24 executed, commits, deviations; nothing rewritten |
| `docs/ARCHIVE.md` | the sprint branch entry gains the manifest pointer and the landing summary; the evidence-archive section names this payload as the first case |
| `docs/BUGS.md` | ONE sentence appended to BUG-107's MERGE-TRAIN NOTE: 107 reconciled — this entry holds it; the `uintptr` item takes the next free number when L5 lands. No heading, status, pin or `Cases:` line touched |
| `docs/2026-09-06_b7-context-store-design.md` | B-R20: a bracketed dated correction after the phrase "the existing host-capability ruling" (no such ruling exists; the decision is open and [USER]-owned) |
| `docs/2026-09-05_typed-contract-design-review.md` | B-R21: a dated note ABOVE the in-place corrigendum, naming it as the sprint lane's later opinion and pointing at L3's disposition; the sealed text below is unchanged |
| `docs/evidence/2026-09-07_land-sprint-records/` | this chunk's gate tail (§5) |

`AGENTS.md`, `CLAUDE.md`, `README.md`: UNTOUCHED — no pointer on main is
stale (the branch's `AGENTS.md` sprint pointer is not needed: the records
are indexed from `docs/ARCHIVE.md` and §7.8; the `CLAUDE.md` retitle is
B-R4, D6 default not landed).

## 2. The manifest — how it was made, and what it says

Generated by `docs/evidence/2026-09-05_typed-consumer-sprint/make-manifest.py`
from `git diff --name-only 47195683 7edc298f -- docs/evidence` (2,159
paths, all present at the tip), `git ls-tree -r -l` (sizes, blob ids),
`git cat-file --batch` (sha256 of every blob, streamed — the payload was
never checked out), and `git log --topo-order --reverse --no-renames
--diff-filter=A --name-only --diff-merges=first-parent` (the introducing
commit; 222 paths were added IN integration merge commits, which the plain
`--diff-filter=A` walk does not attribute — the first run failed closed on
exactly those 222 and the flag was added). Classes by a stated
filename/blob rule (README). Verified: byte total 114,156,315 = auditor B's
figure exactly; eight random origin commits = `git log --diff-filter=A -1`;
one sha256 = `git show | sha256sum`; the two hashless review dirs (B-R11)
confirmed by grep; the six whole-file ledger copies (B-R17) located (four
class `review`, two `source-copy` — byte-identical to the tip's ledgers).

| class | files | bytes |
|---|---:|---:|
| archive | 36 | 55,864,181 |
| capture | 790 | 43,725,542 |
| source-copy | 268 | 5,822,022 |
| probe | 307 | 3,066,686 |
| gate-tail | 641 | 2,898,129 |
| review | 99 | 2,602,830 |
| other | 5 | 171,107 |
| witness | 13 | 5,818 |
| **total** | **2,159** | **114,156,315** |

A single `MANIFEST.tsv` would be ≈370 KiB (> the 256 KiB per-file cap), so
it is SPLIT per source directory — 78 files, the largest 55,511 B, the
directory ≈0.54 MB — per the coordinator's brief ("split; gzip is
FORBIDDEN; no allowlist entry"). This deviates from plan §2.6, which
suggested the manifest as "the ONE grandfathered exception" or a split; the
allowlist is shrink-only by construction (L2), so the exception was never
available. `scripts/check-evidence-size` on the staged index: PASS, 0 new.

## 3. Deviations from the brief and the plan, disclosed

- **Landed beyond the brief's deliverable list, per plan §2.6 and
  `docs/ARCHIVE.md`'s standing promise:** the two landing audits (verbatim,
  prefaced) and the C1-handoff DRAFT (verbatim, prefaced). The audits are
  the source of every finding id on main and were one `git clean` from
  loss; ARCHIVE.md on main already said L6 lands them. [AGENT] call; the
  coordinator may drop either before merge (two/three files, no other
  record depends on them beyond citations that would then dangle).
- **Two small corrections in landed sprint documents** (B-R20, B-R21) that
  the L1 note explicitly routed to the records chunk — bracketed, dated,
  the sealed text untouched.
- **Not done here, owed:** the 32 sprint design/contract notes no chunk
  landed (handoff, "Where everything else lives"; §7.8.3/§7.8.6) — landing
  them verbatim without prefaces would misdescribe main (several describe
  the retired lane or the total renderer), and writing 32 prefaces is a
  chunk of its own, not a hunk of this one.
- The manifest path and split (§2).
- `AGENTS.md` not rewritten (the plan's item (iii)): nothing to rewrite.

## 4. Exclusions

Every `docs/evidence/` file of the tip (the manifest replaces them); the
sprint-era handoff's checkpoint log; the branch's `CLAUDE.md` and
`AGENTS.md` hunks; the storage-maintenance overlay (plan §5); everything
L1–L5 own.

## 5. Gate

`GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=4 GOLEAN_COVERAGE_JOBS=8 scripts/capped
scripts/ci --diff` at the CLEAN committed tip
`0c9c6d6ae062955ddaac238e1cbb2af581a3502e` (this chunk's records commit,
rebased onto main `29f77b43` after round 24 landed): **RESULT: PASS**.
Verbatim lines (the whole block and the run meta:
`docs/evidence/2026-09-07_land-sprint-records/ci-diff-tail.txt`):

```
differential coverage summary: cases=3654 pass=3403 fail=251 export_status=0
  ok   evidence-on-main size gate
  ok   core build (warning-free)
  ok   typed recovery terminal classification
  ok   coverage-harness unit tests
  ok   eval tests (207 ok)
  ok   differential run completed (exit 1; failing-set judged by baseline diff)
  ok   negative run completed (exit 0; set judged by baseline diff)
  ok   negative baseline diff (no regression)
  ok   baseline diff FULL (3654/3654, no regression)
  note reconciler: 2 finding(s), 0 HIGH — report-only (details: tools/reconcile-records)
RESULT: PASS
```

Run meta (`artifacts/coverage/latest.meta.tsv`): `git_commit 0c9c6d6a…`,
`git_dirty false`, `go_toolchain go1.26.5`, `go_drift_actual false`,
`go_traceback system`, `go_crash_channel same-run-setcrashoutput-v1`,
`membership_draws 32`, `jobs 8`. Baseline drift: ZERO — 3654 = 3403 / 251
is exactly main `29f77b43`'s pin (re-derived from the data rows by awk);
no row moved; no re-pin owed; `scripts/ci --slow` not owed (no
`wire.go`/`NativeToIR.lean` change). `git status --short` at the tip: empty.

Two earlier attempts are recorded honestly in the evidence README: run 1 at
`ee23f302` (main `dd636996`) PASSED on that main's pin (3618/3618) but on a
DIRTY tree — this worker edited three records during the run, so the ci
demoted its baseline lines to «certifies that worktree state, not a
commit» — superseded; run 2 at `b06df2c2` was STOPPED by task id (never by
pattern) when round 24 landed, since the gate had to run at the rebased tip.

The final landing commit differs from the gated `0c9c6d6a` ONLY by
`docs/evidence/2026-09-07_land-sprint-records/` and this section (the
documentation-only amend of the landing practice). The gate was not re-run
at the amended tip; the three steps that read those files were, verbatim:

```
$ scripts/check-evidence-size
evidence-size gate: PASS — 1574 tracked files / 27162635 bytes in 85 evidence dirs; caps file 262144 B, dir 4194304 B, no archives, no source copies; 17 pre-existing offender(s) allowlisted (frozen 2026-09-07), 0 new
$ scripts/check-bugs.sh
check-bugs: ok (107 bug(s); pinned cases behave as claimed)
$ python3 tools/reconcile-records
[01] C13  MEDIUM  78 doc site(s) across 9 file(s) name a patch-level Go version other than the pin (go1.25.13/go1.26.5 per docs/spec-sources.md). Some are legitimately historical; a toolchain/oracle claim off the pin is not, because the pin's whole job is that the spec text and the thing that produced the numbers moved together.
[02] C5  MEDIUM  1 frontier-table case citation(s) do not resolve against the baseline
2 finding(s).
```

## 6. Provenance

Rebased once, from main `dd636996` onto `29f77b43` after round 24 (L3)
landed — clean, no conflicts (snapshot ref
`refs/snapshots/land-sprint-records-pre-rebase` = the pre-rebase tip); the
L3 facts (commits, the round-24 re-pin 3654 = 3403 / 251, FR-33 retired,
D2/D5/BUG-087-shape/C4 RULED) were then filled in from main's landed
records (`docs/2026-09-07_land-panic-text-tape.md` §7.2,
`docs/2026-08-31_qrow-rulings.md`, the baseline re-derived by awk).

Squashed records from `typed-consumer-sprint` (archive; `docs/ARCHIVE.md`)
by `git show 7edc298f:<path>` for the charter, by verbatim copy for the
untracked pause-state and C1 records and the audits, and by rewriting for
the handoff. Credits (sprint commits whose records this chunk lands or
supersedes): `5a4aca9e`, `10fefeb3`, `c53bb6a7`; the handoff's checkpoint
commits `7edc298f`, `39235f65`, `c969079a`, `b34cee67`, `2a70246f`,
`414a2abe`, `563c01de`, `b3d6fa6e`, `30b09c08`, `123fd48e`, `77f154e0`,
`26f0dc09`, `82e177c7`, `354ef7f2`, `f251abcb`. Nothing on main, on the
sprint branch, in the sprint worktree, on `land/panic-text-tape` or in
`deps/` was modified; no process killed; no `/tmp` written (scratch under
this worktree's `.tmp/`); not merged, not pushed.
