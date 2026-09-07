# The typed-consumer sprint's evidence payload — MANIFEST of what did NOT land (2026-09-07)

[AGENT] landing chunk L6 `land/sprint-records`, 2026-09-07 (plan of record:
`docs/2026-09-07_typed-sprint-landing-plan.md` §2.6; the convention:
`AGENTS.md` "Evidence on main", `docs/evidence/README.md` rule 9).

**What this is.** One row per file of branch `typed-consumer-sprint`'s
`docs/evidence/**` at its tip `7edc298f257519652646b7a59bca959671d33063`
that did NOT land on main: **2,159 files / 114,156,315 bytes in 78
top-level directories** — every `docs/evidence/` path that differs between
the sprint's merge-base with main (`47195683`) and the tip, none of which
exists on main at any commit of the landing (checked: no path of the set is
present in main's tree at `dd636996`). The BYTES stay on the archive branch;
this directory is the auditable record of them (sha256, size, the commit
that introduced each, a class).

**Why it did not land — the [USER] ruling** (Mike, 2026-09-07, verbatim as
relayed by the [AGENT] coordinator — cite as relayed): «The evidence blob
should not land, and generally we should not dump big evidence bundles on
main (they can't be easily hosted on GH for one). Can you make a plan to
land this work cleanly? We'll want to decompose and land in sane chunks that
can be reviewed. And where appropriate fix some of the issues, eg. the
choice tape stuff». Auditor B (`docs/2026-09-07_landing-audit-B.md` §4,
R7/R7a) quantified the payload as a duplicate of the repository, not an
audit trail: 734,510 added lines, 36 `.tar.gz` (55.9 MB, ≈49 % of the
bytes), 345 exact copies of tracked files (against every non-evidence blob
of every commit), 511 intra-payload duplicate blobs. With the L2 size gate
on main (`scripts/check-evidence-size`), landing it would be a red by
construction (archives, source copies, 3 directories over 4 MiB — `typed-preflight`
55.7 MB, `string-panic-members` 11.2 MB, `r1-production-independent` 4.6 MB —
and 77 files over 256 KiB).

## Where the bytes are

Branch `typed-consumer-sprint` @ `7edc298f` (indexed in `docs/ARCHIVE.md`;
snapshot ref `snapshot/typed-sprint-before-uintptr-20260906` names the same
commit). Any row's bytes: `git show 7edc298f:<path>`; its sha256 must equal
the row's. Nothing on the branch was rewritten.

## Layout of this directory

| file | rows | what |
|---|---:|---|
| `MANIFEST.tsv` | 78 (+ TOTAL) | the index: one row per `docs/evidence/<dir>/` on the branch — `dir`, `files`, `bytes`, one count per class, the per-dir manifest file |
| `manifest/<dir>.tsv` | 2,159 in all | one row per file: `path`, `sha256`, `bytes`, `origin_commit`, `class` |
| `source-copies.tsv` | 268 | `path`, `copy_of`, `tree` — every payload file whose git blob is byte-identical to a tracked NON-evidence blob (in the tip tree, or in main's tree at `dd636996`) |
| `make-manifest.py` | — | the generator (reads git objects only; never checks the payload out) |

The manifest is split per source directory because a single file would be
≈370 KiB, over the 256 KiB per-file cap; the split, not an allowlist entry,
was the ruled fallback (gzip is forbidden under the same rule). Largest
per-dir manifest: `manifest/2026-09-06_i1-json-independent.tsv`, 55,511 B;
this directory in total ≈ 0.54 MB, under the 4 MiB directory cap.
`scripts/check-evidence-size` at this tip: PASS, 0 new offenders.

`origin_commit` is the archive-branch commit that INTRODUCED the path:
`git log --no-renames --diff-filter=A --topo-order --reverse
--diff-merges=first-parent 47195683..7edc298f -- docs/evidence`, first
occurrence per path (222 of the paths were added IN a merge commit by the
integrator — the sprint's integration packets — which a plain
`--diff-filter=A` walk does not attribute; `--diff-merges=first-parent` does).
Spot-checked against `git log --no-renames --diff-filter=A -1 <tip> -- <path>`
on eight random rows: identical.

## Counts by class

| class | files | bytes | what the class means (assigned in this precedence order) |
|---|---:|---:|---|
| `archive` | 36 | 55,864,181 | archive extension (`.tar .tgz .gz .zip .xz .zst .7z`) — all 36 are `.tar.gz`; the two largest (`2026-09-06_typed-preflight/{capture-full,coverage-artifacts}.tar.gz`) are 44.4 MB alone (auditor B R7a) |
| `source-copy` | 268 | 5,822,022 | git blob byte-identical to a tracked non-evidence file: 266 to the tip's own tree, 2 to main's tree only (`source-copies.tsv` names the original) — 231 distinct blobs |
| `gate-tail` | 641 | 2,898,129 | `.log .exit .stderr .stdout` — the one part of the payload that follows the convention (auditor B: all under 100 KB, mean 4.5 KB) |
| `review` | 99 | 2,602,830 | `.md` (incl. `.md.before`): prose reviews, FINAL/README/HANDOFF records, and the whole-file copies of `docs/BUGS.md` / the ledgers (below) |
| `capture` | 790 | 43,725,542 | `.json .jsonl .tsv .sha256 .sha256sums SHA256SUMS`: full-run result tables, run manifests, source-hash inventories, member pins |
| `probe` | 307 | 3,066,686 | `.go .lean .py .toml .patch .diff .body .replacement`, `.go.txt`/`.lean.txt` drafts, extension-less script copies: new probe programs, fixtures, patches, and candidate source trees that are NOT byte-identical to a tracked file |
| `witness` | 13 | 5,818 | `.txt` transcripts/readbacks (toolchain version lines, `commands.txt`, `cap-readback.txt`, `vocabulary-measured.txt`) |
| `other` | 5 | 171,107 | five extension-less `base-*` copies of runner scripts (`base-diff-coverage`, `base-cedar-census`, `base-gotest-triage`, `base-membership-sampling`) and one `spikes/iris-customer/check` copy — pre-change bases of a diff, byte-identical to nothing tracked |
| **total** | **2,159** | **114,156,315** | 1,648 distinct blobs (511 rows are intra-payload duplicates — auditor B's figure, reproduced) |

The class is a file-name/blob rule, stated above and in the generator's
docstring; it is an inventory aid, not a judgement of each file's worth.
`source-copy` here (268) differs from auditor B's 345 by construction: B
matched against every non-evidence blob of all 2,956 commits (a copy of ANY
historical version counts); this manifest matches against two trees (the
tip and main) so that the `copy_of` column names a file a reader can open.
The landing plan's calibration figure (229) is the number of DISTINCT
tip-tree blobs, near this manifest's 231 distinct source-copy blobs.

## Recorded gaps (auditor B, verified here)

- **Two directories record no commit hash at all** (B R11):
  `docs/evidence/2026-09-06_boolean-promotion-review/` (12 files) and
  `docs/evidence/2026-09-06_observer-mock-review/` (4 files). Verified:
  neither README contains a 7–40 hex token; their `SHA256SUMS` /
  `source.sha256` bind file BYTES, not a repository state. Their rows carry
  the `origin_commit` of this manifest (`99e0225d` for the mock review), but
  the base the reviews were run against is not recoverable from the records
  themselves — the one place the payload's auditability genuinely breaks.
- **Six whole-file copies of the bug/coverage ledgers** (B R17) are in the
  payload and NOT on main: `2026-09-06_r1-baseline-independent/
  bugs-ledger-proposed.md` (+ `.before`), `2026-09-06_string-panic-members/
  bugs-ledger-proposed.md` and `bugs-case-pin-proposed.md`,
  `2026-09-06_uintptr-disposition-independent/bugs-proposed.md` and
  `coverage-proposed.md` (+ the two `language-ledger-proposed.md` copies).
  Four are class `review`; `string-panic-members/bugs-case-pin-proposed.md`
  and both `language-ledger-proposed.md` are class `source-copy` — they are
  byte-identical to the tip's `docs/BUGS.md` / `docs/language-coverage-ledger.md`.
  `uintptr-disposition-independent/bugs-proposed.md` carries a `## BUG-107`
  heading for the `uintptr` repair that `docs/BUGS.md` never carried; on
  main BUG-107 is L4's pre-`main` abort entry (numbering reconciled in
  `docs/2026-09-05_typed-consumer-sprint-handoff.md` and on the entry).
- **README compliance** (B R10): 23 of the 78 dirs have no README; 39 are
  cited by no tracked document. This manifest does not repair that; it
  records it.

## Reproduction

From the repo root, on a checkout that has the archive branch
(`git rev-parse --verify 7edc298f`):

```
python3 docs/evidence/2026-09-05_typed-consumer-sprint/make-manifest.py \
  --tip 7edc298f257519652646b7a59bca959671d33063 \
  --base 471956831251e428df3a64c5b8fc7fb79cbebbfc \
  --main dd636996497f4e00237e0ce3a53c234255349a83 \
  --out docs/evidence/2026-09-05_typed-consumer-sprint
scripts/check-evidence-size
```

The generator's stdout summary at generation (2026-09-07, this worktree at
its landing tip, clean; pure git — no Go or Lean toolchain involved; host
linux/amd64):

```
payload: 2159 files / 114156315 bytes in 78 dirs; tip 7edc298f base 47195683 main dd636996
class	files	bytes
gate-tail	641	2898129
witness	13	5818
probe	307	3066686
source-copy	268	5822022
archive	36	55864181
capture	790	43725542
review	99	2602830
other	5	171107
source copies: 268 (tip-tree originals 266, main-only originals 2)
largest per-dir manifest: manifest/2026-09-06_i1-json-independent.tsv 55511 bytes; index 10630 bytes
```

A different `--main` changes only the `source-copy`/`probe` split of files
that later land on main byte-identically; every other column is a function
of the tip and the base.

## Conclusion (what the citing records rely on)

The sprint's evidence payload is inventoried file-by-file with content
hashes and origin commits; nothing of it is on main, and nothing on the
archive branch was rewritten. Consuming records: `docs/ARCHIVE.md` (the
branch entry), `docs/2026-09-05_typed-consumer-sprint-handoff.md` (O3),
`docs/2026-09-05_master-plan.md` §7.8, `docs/2026-09-07_land-sprint-records.md`.
