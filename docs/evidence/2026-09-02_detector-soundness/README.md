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
  `Corpus/coverage/exec/race/negative-sync/` (BUG-080) and the four
  Q-RACEPATH guards into `race/free/` + `race/negative/`.
- `probes.tsv` — the probe manifest in `scripts/coverage-manifest`'s
  10-column format, consumed by `scripts/detector-soundness
  --manifest`.
- `probes-pre.summary.txt`, `probes-pre.matrix.tsv` — the probe run
  on the PRE-Q-RACEPATH machine (commit e7d07b26 + lane tooling only,
  Race.lean unchanged).
- `probes-post.summary.txt`, `probes-post.matrix.tsv` — the same
  probes on the POST-Q-RACEPATH machine (`projChainTarget` landed).
- `corpus.summary.txt`, `corpus.matrix.tsv`, `corpus.meta.tsv` — the
  in-scope corpus matrix (every racy/membership/confluent-lane row +
  every strict-lane row whose feature tags touch goroutines/channels/
  sync/select/deadlock/race/atomics; 362 rows), post-fix machine.
- `corpus-deep.*` — the 11 budget-limited rows re-enumerated under
  `width=8,sites=96,cap=1024,work=30000000,backedge=1`, 900 s budget
  (2 certified, 9 still uncertified — recorded as such).
- Raw per-run TSan transcripts, harness dirs, wire dumps, enumerator
  observations and stats live under the run's `artifacts/detector-
  soundness/<run>/rows/<id>/` (gitignored; regenerate with the commands
  below). The `.tsv`/`.txt` copies here are the tracked record.

## Reproduction (repo root; go1.26.5 = `baselines/go-oracle-pin`)

    scripts/capped lake build                       # the golean binary
    scripts/detector-soundness \
      --manifest docs/evidence/2026-09-02_detector-soundness/probes.tsv \
      --out artifacts/detector-soundness/probes-post --jobs 8
    scripts/detector-soundness --out artifacts/detector-soundness/corpus --jobs 8
    # the deep re-run: the 11 budget-limited ids with params replaced by
    # width=8,sites=96,cap=1024,work=30000000,backedge=1 (see the report §2.1)
    ENUM_TIMEOUT=900 scripts/detector-soundness --manifest <deep-manifest> \
      --out artifacts/detector-soundness/corpus-deep --jobs 6 \
      --strict-enum width=8,sites=96,cap=1024,work=30000000,backedge=1
    # copies: cp artifacts/detector-soundness/<run>/{summary.txt,matrix.tsv,meta.tsv} here
    #         (absolute worktree paths scrubbed to repo-relative with sed)

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
  the branch tip named in each `*.meta.tsv` `commit` line (the PRE run
  names the base commit + `+dirty` for the untracked tooling; the POST
  and corpus runs name the Race.lean-changed tree).
- Host: `Linux 7.0.0-30-generic x86_64`, 32 cores, 125 G; the corpus
  run shared the box with one other lane's enumerator (t4-membership)
  — the per-row gc counts are scheduling-sensitive and are reported as
  counts, never as proofs of race-freedom.

## Conclusion (one paragraph; the report carries the argument)

Across 45 probes and the in-scope corpus, NO case put a program that
is race-free-by-construction-of-our-footprint into gc's red set except
the two recorded classes: U4 (the sync primitives' own state words —
misuse-only, now BUG-080 with born-FAIL pins) and U5 (TSan's
overwrite-Release reporting a go_mem-DRF program — an ORACLE-vs-spec
divergence, posed as ruling Q-U5, not a machine bug). Every other
gc-red probe is machine-refused on every enumerated path; every
gc-green probe is machine-DRF except the recorded O1 dynamic-index
residual (by design, pinned) and the schedule-dependent probes where
the machine's enumerator refuses on paths the 10-run sampler never
realized (the per-run nature of BOTH oracles, made visible). The
corpus matrix's counts are in `corpus.summary.txt`.
