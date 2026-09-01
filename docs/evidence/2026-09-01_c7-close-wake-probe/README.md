# C7 close-wake probe — two select clauses on ONE channel, woken by close (2026-09-01)

[AGENT] C7-refresh lane (the Q-SELSEL prerequisite: qrow-rulings row 3;
the A1-14 unprobed corner). Consuming docs:
`docs/2026-08-11_latitude-inventory.md` C7 + §8 e12 (the re-argued
narrowing), `docs/2026-08-31_qrow-rulings.md` row 3 (the PREREQ
DISCHARGED note).

## The question

C7's (b-n) narrowing rests on the recorded argument "a parked gc select
is committed by the EVENT that wakes it". The corner: a select parked
with TWO recv clauses on the SAME channel, woken by `close(ch)` — ONE
waking event, width-2 wake-readiness. If the event determined the
clause, gc would commit deterministically; the machine's wake path
(`resumeThread` Multi.lean:424–427) head-commits clause 1 on every
stream. Does gc ever commit clause 2 from the wake?

## Subjects

- `probe/main.go` — the shared gc/machine subject (`selselCloseWake`:
  both recv clauses on `ch`, closer goroutine `close(ch)` then
  `done <- 1`; observable = which clause body ran, returned and
  printed). TSan-green (receiver-side close wake): `go build -race`,
  0/30 red.
- `probe-gc-parkfirst/main.go` — gc-ONLY variant (`time.Sleep(2ms)`
  before the close) making park-before-close near-certain, isolating
  the WAKE path from the entry path. Not a machine subject.

## Reproduction (from the repo root)

    # gc side (pin go1.26.5)
    go build -o artifacts/c7probe/plain docs/evidence/2026-09-01_c7-close-wake-probe/probe/main.go
    go build -o artifacts/c7probe/parkfirst docs/evidence/2026-09-01_c7-close-wake-probe/probe-gc-parkfirst/main.go
    for i in $(seq 1 200); do GOMAXPROCS=1 artifacts/c7probe/plain; done | sort | uniq -c
    # (repeat for GOMAXPROCS=8 and for parkfirst; counts below)
    go build -race -o artifacts/c7probe/plain-race docs/evidence/2026-09-01_c7-close-wake-probe/probe/main.go
    for i in $(seq 1 30); do GOMAXPROCS=8 artifacts/c7probe/plain-race >/dev/null; done  # 0 DATA RACE reports

    # machine side
    GO111MODULE=off go run ./tools/nativefrontend --dir docs/evidence/2026-09-01_c7-close-wake-probe/probe --out artifacts/c7probe/wire.json
    .lake/build/bin/golean native-json-run --input artifacts/c7probe/wire.json --function selselCloseWake
    .lake/build/bin/golean coverage-observations --input artifacts/c7probe/wire.json --function selselCloseWake \
      --max-width 2 --max-sites 24 --cap 64 --work-cap 200000 --expect-status ok

## Toolchain / provenance

- Go: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`).
- Machine: `.lake/build/bin/golean` built by `scripts/capped lake build
  golean` at commit 670d3351 (clean tree, branch c7-refresh).
- wire.json sha256:
  `867f94d1fe2625297e4c7fd55a6145ebe76e2fdc5921982ed6b5911c30bb35a7`.
- Host: linux/amd64 dev box, light concurrent load; the counts are
  frequency observations only — no distributional claim is derived
  (doctrine: possibilistic membership is the only claim class).

## gc counts (200 runs per config)

| subject | GOMAXPROCS | clause 1 | clause 2 | other |
|---|---|---|---|---|
| plain | 1 | 100 | 100 | 0 |
| plain | 8 | 106 | 94 | 0 |
| parkfirst (wake-path isolated) | 1 | 101 | 99 | 0 |
| parkfirst (wake-path isolated) | 8 | 93 | 107 | 0 |

gc commits the SECOND clause roughly half the time — including on the
park-first variant where the select is parked before the close on
essentially every run. One event, two same-channel clauses: the waking
event does NOT determine the committed clause. (Mechanism, for the
record: `selectgo` builds its lockorder FROM the shuffled pollorder —
runtime/select.go's own comment: "Start with the pollorder to permute
cases on the same channel" — so the two sudogs sit in `recvq` in
per-entry-random order, and `closechan`'s first successful dequeue
wins the `selectDone` CAS. Implementation reading, cited as color;
the counts above are the evidence.)

## Machine results (commit 670d3351)

- Default stream (`native-json-run`, no `--choices`): `ok 1` — the
  canonical schedule parks the select, and the wake head-commits
  clause 1 (`resumeThread` Multi.lean:424–427, consuming nothing).
- Directed streams: `[1]`, `[1,1]`, `[9,8,7,6,5,4,3,2,1,0]`,
  `[1,3,5,7,9,2,4,6,8,0]` → `ok 1`; `[5,5,5,5,5,5,5,5]` → `ok 2`
  (an L1 pick runs the closer before select entry; the ENTRY-path L2
  draw then picks clause 2).
- Full enumeration (`coverage-observations`, width 2 / sites 24 /
  cap 64 / work-cap 200000): certified set **{1, 2}** —
  `observations=2 steps=5590 probes=1311 sites=437 leaves=438
  maxdepth=12 width=2`.

## Conclusion (one paragraph)

Observed ∈ modeled HOLDS on this shape: gc's realized set {1, 2} is
contained in the machine's certified set {1, 2}. But the containment
does NOT flow through C7's recorded argument — the wake path realizes
only clause 1 (deterministic head-commit; falsified as a model of
gc's wake, which permutes same-channel clauses per entry) — it flows
through the ENTRY-path schedule: close-before-entry is always a
machine-realizable interleaving of the same program (no HB edge can
order a close after the select's entry, and B1's post-op boundary
guarantees a scheduling point immediately before entry), and the
entry-time L2 draw covers any clause the close enables. The C7 row's
coverage argument is rewritten on this basis (two-leg: L4
clause-individual pairing for partner wakes; entry-path L2 mask for
close wakes); the (b-n) narrowing itself survives. No BUGS.md entry:
there is no observed-∉-modeled point.
