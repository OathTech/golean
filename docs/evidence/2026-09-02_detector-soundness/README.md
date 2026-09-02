# Detector-soundness differential — the -race legs, probes, and matrix (2026-09-02)

[AGENT] evidence directory for `docs/2026-09-02_detector-soundness.md`
(the Tier-4 detector-soundness lane, `t4-detector-soundness`;
fidelity decision 1's named owner for detector completeness; outsider
review D5; A1-07 / A2-Q3). Convention: `docs/evidence/README.md`.

## What is here

- `probes/{u2,u4,u5,footprint,schedule}/main.go` — 45 novel probe
  subjects, each a program that races (or deliberately does not)
  THROUGH one recorded footprint gap (Race.lean's inventory U2/U4/U5
  and O1) or one `stepAccesses` arm the corpus does not pin. Every
  subject's header comment states its target and the EXPECTED cell.
  They are NOT corpus cases (`scripts/coverage-manifest` does not
  scan this tree); the two that became corpus pins were copied into
  `Corpus/coverage/exec/race/negative-sync/` (BUG-080); the five
  Q-RACEPATH rows are corpus-native (2 confluent chain-form guards in
  `race/free/`, 2 racy must-stay-racy guards in `race/negative/`, and
  the born-FAIL dynamic-index residual pin in `race/free/`).
- `probes.tsv` — the probe manifest in `scripts/coverage-manifest`'s
  10-column format, consumed by `scripts/detector-soundness
  --manifest`.
- `probes-pre.summary.txt`, `probes-pre.matrix.tsv` — the probe run
  on the PRE-Q-RACEPATH machine (commit e7d07b26 + lane tooling only,
  Race.lean unchanged).
- `probes-post.summary.txt`, `probes-post.matrix.tsv` — the same
  probes on the POST-Q-RACEPATH machine (`projChainTarget` landed).
- `corpus.summary.txt`, `corpus.matrix.tsv`, `corpus.meta.tsv` — the
  FIRST in-scope corpus matrix (every racy/membership/confluent-lane
  row + every strict-lane row whose feature tags touch goroutines/
  channels/sync/select/deadlock/race/atomics), post-Q-RACEPATH
  machine — 362 of the 364 in-scope rows at the tip; the 2 BUG-080
  pins post-date the run and ARE the third cell (report §3.2). Made
  with the first runner (audit B2/S1/S3 found its fail-open paths;
  the corrections to its counts are in report §2).
- `corpus-deep.*` — the 11 budget-limited rows re-enumerated under
  `width=8,sites=96,cap=1024,work=30000000,backedge=1`, 900 s budget
  (2 certified, 9 still uncertified — recorded as such);
  `corpus-deep.manifest.tsv` is the manifest that run consumed (the
  11 ids with params replaced), tracked here.
- `corpus-tip.*` — the CORRECTED in-scope matrix: the audit fix
  round's re-run at the branch tip with the hardened runner (new cells
  `possible-HOLE` / `gc-no-verdict` / `refused`, truncation and
  member-status disqualifiers, `sites=` declared on every row) — 364
  rows, the two BUG-080 pins in HOLE. This is the matrix report §2
  carries.
- `probes-tip.*` — the 45 probes under the same hardened runner (the
  post-Q-RACEPATH machine is unchanged; the movers vs `probes-post`
  are cell renames only — gc-red uncertified → `possible-HOLE`).
- `gate-tail.txt` — the `scripts/ci --diff` tail at the branch tip.
- **BUG-080 fix slice (2026-09-02, `bug080-atomic-kind`)**:
  `probes/u4kind/main.go` + `probes-u4kind.tsv` — the 28-subject
  family probing each primitive's OWN words in both directions (copy =
  plain read, overwrite = plain write; plain access in main beside the
  op in a child, and roles swapped) plus the negative controls
  (contending ops, sibling fields under the lock, disjoint primitives).
  `probes-u4kind-pre.*` — on the 0f3c05ff machine (main's binary, the
  worktree dirty only with the probe files): 7 HOLE, 7 possible-HOLE,
  14 agree-DRF. `probes-u4kind-post.*` — on the fixed machine at the
  slice's commit 43fd17e1 (clean stamp; an earlier run on the same
  machine at 0f3c05ff+dirty gave cell-for-cell identical results): 0
  HOLE, 26 agree, 2 possible-HOLE (`rw-overwrite-vs-{runlock,unlock}`
  — machine `fatal` where gc reports the race then dies; BUG-080
  residual (b)). `corpus-bug080.*` — the in-scope corpus matrix (368
  rows = the 364 + the slice's 4 new rows) on the fixed machine, stamp
  0f3c05ff+dirty where dirty = exactly the diff committed as 43fd17e1
  (the run overlapped the gate; the golean binary was the slice's):
  HOLE 2 → 0, possible-HOLE 0, over-refusal 1 (the O1 residual, no new
  row), agree-race 23 → 27, agree-DRF 275 → 277, uncertified 63 (same
  set). `gate-tail-bug080.txt` — the slice's `ci --diff` tail + the
  final fast-gate tail.
- Raw per-run TSan transcripts, harness dirs, wire dumps, enumerator
  observations and stats live under the run's `artifacts/detector-
  soundness/<run>/rows/<id>/` (gitignored; regenerate with the commands
  below). The `.tsv`/`.txt` copies here are the tracked record.

## Reproduction (repo root; go1.26.5 = `baselines/go-oracle-pin`)

    scripts/capped lake build                       # the golean binary
    # probes-pre: the PRE-Q-RACEPATH machine = base commit e7d07b26's
    # GoLean/ tree with the (then-untracked) lane tooling + probes on top —
    # check out e7d07b26, copy scripts/detector-soundness + this dir in,
    # build, then:
    scripts/detector-soundness \
      --manifest docs/evidence/2026-09-02_detector-soundness/probes.tsv \
      --out artifacts/detector-soundness/probes-pre --jobs 8 \
      --strict-enum width=4,sites=32,cap=512,work=4000000   # (no backedge=1 then)
    # probes-post / corpus: the post-Q-RACEPATH machine (Race.lean as at 804f9588)
    scripts/detector-soundness \
      --manifest docs/evidence/2026-09-02_detector-soundness/probes.tsv \
      --out artifacts/detector-soundness/probes-post --jobs 8
    scripts/detector-soundness --out artifacts/detector-soundness/corpus --jobs 8
    # the deep re-run: the tracked corpus-deep.manifest.tsv (the 11
    # budget-limited ids with params replaced; see the report §2.1)
    ENUM_TIMEOUT=900 scripts/detector-soundness \
      --manifest docs/evidence/2026-09-02_detector-soundness/corpus-deep.manifest.tsv \
      --out artifacts/detector-soundness/corpus-deep --jobs 6 \
      --strict-enum width=8,sites=96,cap=1024,work=30000000,backedge=1
    # the audit fix round's re-run at the branch tip (hardened runner):
    scripts/detector-soundness --out artifacts/detector-soundness/corpus-tip --jobs 8
    scripts/detector-soundness \
      --manifest docs/evidence/2026-09-02_detector-soundness/probes.tsv \
      --out artifacts/detector-soundness/probes-tip --jobs 8
    # copies: cp artifacts/detector-soundness/<run>/{summary.txt,matrix.tsv,meta.tsv} here
    #         (absolute worktree paths scrubbed to repo-relative with sed)
    # gate-tail.txt: the tail of `scripts/capped scripts/ci --diff` at the tip

Defaults: `--runs 5 --procs 1,8` (10 `-race` executions of the SAME
`tools/coverageharness` binary the gate runs, per row); strict-lane
rows enumerate under `width=4,sites=32,cap=512,work=4000000,
backedge=1` (the runner's `--strict-enum`; enumerating-lane rows use
their own `params`). Timeouts: 15 s per -race run (deadlock rows hang
under -race by design — the -race runtime suppresses the deadlock
detector), 300 s per enumeration.

## Toolchain / host / commit

- `go version go1.26.5 linux/amd64` (the pin). `-race` needs cgo; the
  box has it (the racy lane already depends on it).
- Lean toolchain per `lean-toolchain` (v4.32.2); golean built from
  the tree named in each `*.meta.tsv` `commit` line — READ WITH CARE
  (audit S7): the PRE run's line says `e7d07b26` WITHOUT `+dirty`
  although the tooling and probes were untracked (the first runner's
  marker used `git diff --quiet`, which ignores untracked files; fixed
  to `git status --porcelain` at the fix round); the POST and corpus
  runs say `e7d07b26+dirty` and the deep run `653319b6+dirty` — all
  three ran on the UNCOMMITTED Race.lean change over those commits.
  The committed tree that reproduces the POST/corpus/deep machine is
  **804f9588** (Q-RACEPATH landed; Race.lean unchanged since, except
  a comment at the fix round). The `-tip` runs name the fix round's
  tip.
- Host: `Linux 7.0.0-30-generic x86_64`, 32 cores, 125 G; the corpus
  run shared the box with one other lane's enumerator (t4-membership)
  — the per-row gc counts are scheduling-sensitive and are reported as
  counts, never as proofs of race-freedom.

## Conclusion (one paragraph; the report carries the argument)

Across 45 probes and the in-scope corpus (362 of the 364 tip rows in
the first run; all 364 in the corrected `corpus-tip` run), the only
gc-red programs the machine ran to a value are the recorded U4 class
(the sync primitives' own state words — misuse-only, now BUG-080 with
born-FAIL pins, the two HOLE rows of the corrected matrix). The U5
probe (`u5/cross-unlock-publish`, gc red 7/10) is NOT a second class:
the pre-merge audit (B1) showed it is racy under go_mem (per-execution
Unlock/Lock numbering) and the machine refuses its racy paths on
forced tapes — the ruling Q-U5 the first report draft posed on it
was WITHDRAWN; the merge-vs-overwrite Release difference Race.lean
records as U5 stands, unmeasured here (its exhibit cannot be made
deterministic). Every other gc-red probe is machine-refused on every
enumerated path; every gc-green probe is machine-DRF except the
recorded O1 dynamic-index residual (by design, pinned) and the
schedule-dependent probes where the enumerator refuses on paths the
10-run sampler never realized (the per-run nature of BOTH oracles,
made visible). The corrected corpus counts are in
`corpus-tip.summary.txt`; the first run's in `corpus.summary.txt`
(with its corrections in report §2).
