# Q-U4RESIDUAL option (A) — the race detector follows go_mem on the TSan-blind sync ops: probe families and gate record (2026-09-02)

[AGENT] evidence directory for the `q-u4-gomem` lane — the
implementation of the [USER] ruling on `docs/2026-08-31_qrow-rulings.md`
row 9 (Q-U4RESIDUAL, option (A), ruled 2026-09-02; the verbatim quotes
and their provenance chain — relayed to this lane by the [AGENT]
coordinator, not received firsthand — are the sheet's appendix record
"The row-9 ruling record"). Consuming docs: `docs/BUGS.md` BUG-083 (the
designed-divergence record) and BUG-080 (residual (a) closed);
`GoLean/GoCore/Race.lean` section "The sync primitives' OWN state
words" (the per-entry derivation); `docs/2026-08-11_latitude-inventory.md`
register #13; `docs/2026-09-02_detector-soundness.md` §3.2 (residual
(a) paragraph). Convention: `docs/evidence/README.md`.

## Conclusion (the paragraph the citing docs rely on)

With `syncEntryKinds`/`syncReleaseTailKinds` recording TSan's realized
set UNION go_mem's operation kind, each at its gc word, the BUG-080
probe family `u4kind` (28 subjects, unchanged source) moves from 26
agree + 2 possible-HOLE to **20 agree (13 agree-race + 7 agree-DRF) +
6 over-refusal + 2 possible-HOLE**: the six movers are exactly the
go_mem-racy / TSan-green shapes — `wg-copy-vs-add-from-0`,
`wg-copy-vs-done`, `wg-overwrite-vs-done`, `wg-overwrite-vs-wait-at-0`
(WaitGroup ops under `race.Disable`) and `rw-copy-vs-{rlock,lock}`
(whose subjects pair the lock with its UNLOCK unordered with the copy,
so they refuse THROUGH the write-like unlock; the lock op alone was
never isolated by that family). No agree-race cell moved (nothing the
oracle refuses is run), no HOLE opened, the 2 possible-HOLEs are
BUG-080's residual (b) exactly as before. The new family `u4gomem`
probes the formerly UNPROBED copy-beside-`RUnlock`/`Unlock` shapes
(gc `-race` GREEN 20/20 at GOMAXPROCS 1 and 8 each; machine RACE-ALL —
over-refusal BY DESIGN) and four controls that must stay green and do:
the canonical Add/go-Done/Wait idiom followed by a copy, reader/writer
contention followed by a copy, and the ISOLATED copy-beside-`RLock` /
copy-beside-`Lock` shapes (the child unlocks only after main's ack) —
agree-DRF, confirming the ruling's own "NOT in the class" statement
(mem#model: mutex lock is read-like, a copy is read-like). The corpus
pins the class as 6 born-FAIL rows `race/gomem-only/*` (gc `ok`,
machine `race`, BUG-083's Cases line — never a pass) and the isolation
as 2 born-PASS confluent guards `race/free-sync/rw-copy-beside-{rlock,
lock}`; the full gate showed no other row moving.

## What is here

- `probes/u4gomem/main.go` + `probes-u4gomem.tsv` — the 6-subject
  family: G-1/G-2 the two unprobed shapes (copy beside `RUnlock` /
  `Unlock` only; main locks before the spawn, the child unlocks), G-3
  the canonical WaitGroup idiom then a copy, G-4 reader/writer
  contention then a copy, G-5/G-6 the ISOLATED copy-beside-lock-op
  shapes (an `ack` channel makes the unlock HB-after the copy). Each
  header states its expected cell. Manifest in `scripts/coverage-
  manifest`'s 10-column format for `scripts/detector-soundness
  --manifest`.
- `probes-u4gomem.{matrix.tsv,meta.tsv,summary.txt}` — that family's
  run: 20 gc `-race` runs at each of GOMAXPROCS 1 and 8 per subject +
  the enumerator (`width=4,sites=32,cap=64,work=2000000`). 2
  over-refusal (G-1, G-2), 4 agree-DRF (G-3..G-6). Exit 0.
- `probes-u4kind-ruled.tsv` — the BUG-080 family's manifest re-issued
  for this run: rows IDENTICAL to `docs/evidence/2026-09-02_detector-
  soundness/probes-u4kind.tsv` (same `go_dir` — the tracked
  `probes/u4kind/main.go` in that dir, unchanged), except the `why`
  of the six rows whose expected cell the ruling moves (each says
  what it was and why it moves). The old dir is not rewritten (the
  evidence convention's no-backfill rule); its `probes-u4kind-post.*`
  remain the BUG-080-era record.
- `probes-u4kind.{matrix.tsv,meta.tsv,summary.txt}` — the 28-subject
  re-run under this lane's binary, 20 runs per GOMAXPROCS value. Cells
  above; the runner exits 1 on the 2 possible-HOLEs (residual (b),
  diagnosed at BUG-080 — unchanged by this slice, which touches no
  fatal path).
- The corpus rows are corpus-native: `Corpus/coverage/exec/race/
  gomem-only/` (6 born-FAIL-by-design rows; the package header carries
  the per-row derivation) and `Corpus/coverage/exec/race/free-sync/
  rw-copy-beside-{rlock,lock}` (2 born-PASS guards).

## Toolchain, commit, host

- `go version go1.26.5 linux/amd64` — the pin (`baselines/go-oracle-pin`).
- Machine binary: `.lake/build/bin/golean` built by `scripts/capped lake
  build` from this lane's tree. The probe runs' `meta.tsv` record
  `commit fa4fce581afd66b412371805989152ae03622878+dirty` — the branch
  point (main at the lane's creation) with the lane's UNCOMMITTED
  Race.lean/Multi.lean change applied; the runner names the binary by
  ABSOLUTE worktree path (`/home/dev/projects/golean/.claude/worktrees/
  q-u4-gomem/.lake/build/bin/golean`, a dead path once the worktree is
  removed) — disclosed rather than rewritten, as the detector-soundness
  dir did. The committed tip these bytes correspond to is the lane's
  first commit `3b60b6efc8b400905f7b340a297a9da4e9b42ef5`; the Race.lean
  table did not change between the runs and the commit (only docstring
  text did, after the u4kind re-run showed the rw-copy shapes moving —
  see "Reproduction").
- Host: linux/amd64 (`Linux 7.0.0-30-generic x86_64`), the shared
  build box, concurrent agent load present; no timing claim is made —
  gc run counts are what they are (race/clean/exit/timeout per row in
  the matrix).

## Reproduction (from the repo root, on branch `q-u4-gomem`)

    scripts/capped lake build

    # the new family, 20 runs per GOMAXPROCS value
    scripts/capped scripts/detector-soundness \
      --manifest docs/evidence/2026-09-02_q-u4-gomem/probes-u4gomem.tsv \
      --runs 20 --procs 1,8 --jobs 8 \
      --out artifacts/detector-soundness/q-u4-gomem-u4gomem
    # -> matrix.tsv / meta.tsv / summary.txt copied here as probes-u4gomem.*

    # the BUG-080 family under the ruled table
    scripts/capped scripts/detector-soundness \
      --manifest docs/evidence/2026-09-02_q-u4-gomem/probes-u4kind-ruled.tsv \
      --runs 20 --procs 1,8 --jobs 8 \
      --out artifacts/detector-soundness/q-u4-gomem-u4kind
    # -> copied here as probes-u4kind.*   (exit 1: the 2 residual-(b) possible-HOLEs)

    # the corpus slices, then the gate
    scripts/capped scripts/coverage run --prefix race/
    scripts/capped scripts/coverage run --prefix sync/
    scripts/capped scripts/ci --diff

Run order, honestly: the u4kind family was run once BEFORE the
isolated G-5/G-6 subjects and the `free-sync` guards existed — that
first run is what showed `rw-copy-vs-{rlock,lock}` moving to
over-refusal (the brief had expected them to stay agree-DRF; the
diagnosis — the subjects pair the lock with its unlock — is why G-5/
G-6 and the guards were written). Both families were then re-run
against the same binary; the files here are the re-run. The machine
table (`syncEntryKinds`/`syncReleaseTailKinds`) was identical in both
runs.

## Gate

`scripts/capped scripts/ci --diff` on the worktree state that became
the lane's first commit (`latest.meta.tsv`: `git_commit fa4fce58…`,
`git_dirty true` — the differential certifies that worktree state; the
committed tree is byte-identical in every gate-relevant file; that
commit is `3b60b6efc8b400905f7b340a297a9da4e9b42ef5`, recorded here by the follow-up commit):
**RESULT: PASS** — differential baseline diff FULL, "no regression: 2567
case(s) run in latest.tsv match baselines/native-full.tsv" (the table
in the baseline is byte-identical, order included, to the run's
`latest.tsv` reduced to result/id/stage); re-pin guard "0 PASS→non-PASS
flip(s), all listed in BUGS.md Cases"; reconciler 3 findings, 0 HIGH
(the 3 MEDIUMs — C13 doc Go-version sites, C5 one frontier-table
citation, C9 wire-schema-after-certification — are main's, unchanged
by this lane); eval tests 146 ok; spec anchors resolve. `gate-tail.txt`
is the run's tail, ANSI-stripped. Sliced runs before the gate:
`scripts/coverage run --prefix race/` (51 rows: the 6 gomem-only rows
FAIL/lean-observation `expected status ok, got {"status":"race"}`, the
2 free-sync guards PASS/confluent, every other race row as in the
baseline) and `--prefix sync/` (77 rows, the same 10 pre-existing FAILs
as the baseline).
