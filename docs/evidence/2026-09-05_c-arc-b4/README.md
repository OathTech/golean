# B4 + C5 (`Signal`/`Status`, `.opDone` → the `Thread` boundary flag) — gate tails and whole-corpus choice-trace identity (2026-09-05)

Consuming docs: `docs/2026-09-05_c-arc-b4-design.md` (§4 preservation, §5
evidence, §9 landing record), `docs/2026-09-03_design-hygiene-arc.md`
(step (iv) B4, step (v) C5, landing record slice 4),
`docs/2026-09-04_reasoning-surface-plan.md` (§5.4 G-C5 → LANDED, §5.1 rows
2–3), `docs/2026-09-03_grumpy-professor-review.md` (B4/C5 status lines).

Provenance: produced 2026-09-05 [AGENT] (C-arc step 2, worktree `c-arc-b4`
off `main` @ `076f5eec`, rebased onto `426af905` — a records-only advance
of `main`, GoLean tree identical; the commit SHAs below are the REBASED
ones, and each gate/trace ran on a pre-rebase commit whose code trees
(`GoLean/ Tests/ Corpus/ baselines/ scripts/ tools/`) are byte-identical
to the rebased commit named — pre-rebase SHAs: c1 `cbe298f5`, c2
`81fb8bc5`, records `412832b3`), executing design gate G-C5 — RULED [USER]
2026-09-04 as recommended, relayed by the [AGENT] coordinator (cited as
relayed, not firsthand; the coordinator's per-gate reading CONFIRMED
[USER] 2026-09-05, relayed) — and arc step (iv) B4 under the arc's [USER]
ratification (2026-09-03, relayed). No decision in this directory is new;
the design note records the deviations from the plan text (§2, §7).

Toolchain: Go `go1.26.5 linux/amd64` (the pin, `baselines/go-oracle-pin`;
`go version` at every run); Lean `leanprover/lean4:v4.32.2`
(`lean-toolchain`). `golean-before` = `scripts/capped lake build golean` at
`main` @ `076f5eec` (the checkout's own build, `.lake` seeded from it);
`golean-c1` at `40fd1903`, `golean-c2` at `165822ef` (each the committed
tree's build — no edit between build and commit). Host: linux/amd64, 32
cores / 125 GiB, shared with other lanes' gates and LSP servers
(timing-insensitive records only).

## The claim this directory backs

Each commit is semantics-preserving PER STEP on both drivers: the full
native differential (`scripts/capped scripts/ci --diff`) reports ZERO
baseline drift at the C5 tip (3498/3498 rows FULL match
`baselines/native-full.tsv`, negative 394/394, eval tests 153 ok — incl.
the exact-fuel `pollerMain_F` pins at fuel 74/90 and the 13-node dedup
certificate fixture), and the whole-corpus labeled-consumption trace
(`scripts/choice-trace-corpus --dump`: every executable row × 6 streams)
is byte-identical to the pre-lane snapshot on every individual consumption
record (id, stream, idx, phase, site, bound, streamValue, pick — 23115
records over 20748 (row, stream) lines) with status + observation hash
identical on every (row, stream) line, at BOTH commits.

## Reproduction (repo root; `deps/` set up by `scripts/setup-deps`)

```sh
# BEFORE (main @ 076f5eec): build, stash the binary, trace the corpus
scripts/capped lake build golean && cp .lake/build/bin/golean artifacts/golean-before
scripts/choice-trace-corpus --dump --jobs 6 --out artifacts/choice-trace-before \
  --golean "$PWD/artifacts/golean-before" \
  --exclude goroutines/send-then-spin --exclude strings/trimspace-repeat/repeat-bound-refused
# per commit (40fd1903 = c1, 165822ef = c2): build at the commit, stash, trace, compare
scripts/capped lake build golean && cp .lake/build/bin/golean artifacts/golean-<k>
scripts/choice-trace-corpus --dump --jobs 6 --out artifacts/choice-trace-<k> \
  --golean "$PWD/artifacts/golean-<k>" \
  --exclude goroutines/send-then-spin --exclude strings/trimspace-repeat/repeat-bound-refused
cat artifacts/choice-trace-before/dump-*.tsv | grep -v '^id	' | LC_ALL=C sort > before.tsv
cat artifacts/choice-trace-<k>/dump-*.tsv | grep -v '^id	' | LC_ALL=C sort > <k>.tsv
cmp before.tsv <k>.tsv                                   # choice-trace/<k>-diff.txt (first line)
docs/evidence/2026-09-04_c-arc-gu/same-streams-diff.sh artifacts/choice-trace-before artifacts/choice-trace-<k>
# the gate, in a detached worktree at the commit (so the lane tree could keep moving)
scripts/capped scripts/ci --diff                         # transcripts/gate-<k>*.txt
```

EXCLUSIONS — the two rows every corpus trace since the A-series excludes,
recorded in each run's `excluded.tsv` (copied here): `goroutines/
send-then-spin` (nonterm=200, runs to the step cap under every stream) and
`strings/trimspace-repeat/repeat-bound-refused` (the 16 MiB shim refusal
path; >15 min per stream). Neither is traced by any run here.

PRE-EXISTING TRACER FINDING (not this lane's; identical on all three
runs): the tracer reports `driver-agreement mismatches: 6`, all on ONE
row, `builtins/float-bits/roundtrip-payloads` (every stream: «MISMATCH:
engine/enumerator observation mismatch»); present on `main` @ `076f5eec`'s
binary (`choice-trace/before-summary.txt`) before any edit of this lane.
Reported in the lane's summary for the owning lane (fidelity / tracer
tooling); every other row: 0 violations, 0 alarms, 0 mismatches.

## Per-commit record

| commit | gate | tally | drift | trace vs BEFORE |
|---|---|---|---|---|
| `40fd1903` B4 (1/3) Signal | `ci --diff` **FAIL** (`transcripts/gate-c1-FAIL.txt`) — ONE failing step: «core build has GoLean/ warnings» (13 `unusedSimpArgs` warnings from a `set_option … in` left attached to a new lemma instead of `stepFn_consumption_none`; fixed in `165822ef`). The `row: FAIL … TIMED OUT after 1s` lines in the transcript are the lane-validation SELF-TESTS T1–T3 (each `ok`), present in the passing run too. | differential 3498/3498 FULL, negative 394/394, eval 153 ok | 0 | per-consumption dump byte-identical, 23115 records; status + obsHash identical on 20749 (row, stream) lines; per-site totals identical (`choice-trace/c1-diff.txt`, `c1-summary.txt`) |
| `165822ef` B4 (2/3) + C5 | `ci --diff` **PASS** (`transcripts/gate-c2.txt`) | 3498/3498 FULL, negative 394/394, eval 153 ok, core build warning-free, reconciler 2 findings / 0 HIGH (report-only; both pre-existing cross-ledger notes — C13 off-pin Go version mentions in docs, C5 one frontier-table citation) | 0 | per-consumption dump byte-identical, 23115 records; status + obsHash identical on 20749 (row, stream) lines; per-site totals identical; 0 violations / 0 alarms / the same 6 pre-existing float-bits mismatches (`choice-trace/c2-diff.txt`, `c2-summary.txt`) |

| records tip (`412832b3` pre-rebase = the branch tip's code trees byte-for-byte; rebased tip `03fae3c8` + this row's commit) | `ci --diff` **PASS** (`transcripts/gate-tip.txt`) | 3498/3498 FULL, negative 394/394, eval 153 ok, core build warning-free | 0 | (no machine change since c2) |

Per-site totals at BEFORE (and at every commit): `l1Sched=9443
appendSpill=4868 postOp=4534 backEdge=2404 mapIter=1307 l5ExitWindow=325
tryLock=101 nilValueMethodText=84 l2Entry=24 l4Waiter=22 l2Arrival=3`. The
`postOp=4534` records are the executable form of the design note's §4.4
argument (the flag ≡ the marker at every step).

## Files

| file | what |
|---|---|
| `choice-trace/before-summary.txt`, `c1-summary.txt`, `c2-summary.txt` | `scripts/choice-trace-summarize` output of the three runs |
| `choice-trace/dump-before-sorted.tsv` | the BEFORE per-consumption dump, `LC_ALL=C sort`ed (23115 records) — the oracle both commits are `cmp`ed against |
| `choice-trace/c1-diff.txt`, `c2-diff.txt` | the `cmp` verdict + `same-streams-diff.sh` output (status/obsHash per (row, stream), per-site totals, changed-line set) |
| `excluded.tsv` | the two excluded rows (all runs) |
| `transcripts/gate-c1-FAIL.txt` | the RED commit-1 gate, cause named |
| `transcripts/gate-c2.txt` | the PASS commit-2 gate tail (the full `ci --diff` transcript) |
| `transcripts/gate-tip.txt` | the PASS gate at the records tip (`412832b3`, pre-rebase; code trees identical to the branch tip) |
