# Q-TRYLOCK — gc probes, twin-pin diff, gate tails, consumption-invariance trace (2026-09-03)

[AGENT] evidence directory for the `q-trylock` lane (Q-TRYLOCK, RULED
[USER] 2026-08-31 — `docs/2026-08-31_qrow-rulings.md` row 5, envelope
pre-ruled; own-slice sequencing and the twin-pin move RULED [USER]
2026-09-03, both relayed by the [AGENT] coordinator and recorded in that
sheet's 2026-09-03 appendix records). Convention: `docs/evidence/README.md`
(all eight rules below). Consuming docs: the rulings sheet row 5;
`docs/2026-08-11_latitude-inventory.md` C12 (+ the §0 site table row);
`docs/language-coverage-ledger.md` (§3 `locks`, §4 FR-5, §6 Q-TRYLOCK,
§8g); `GoLean/GoCore/Race.lean` (the "TryLock / TryRLock" row of the
sync-words table cites the probe subjects by name);
`GoLean/GoCore/Machine.lean` (`applyTryLock`'s envelope statement);
`scripts/check-frontend-pins` (the re-pin history line);
`baselines/native-full.tsv` (the re-pin paragraph).

## What is here

- `probes/tsan/main.go` — 20 probe subjects (18 + the audit fix round's
  two F1 shapes: `rwTryRLockQueuedWriter` — TryRLock while a writer is
  QUEUED behind `rw.w`, not yet past `readerCount.Add(-max)`; and control
  D `rwRLockQueuedWriter` — the blocking RLock in the same state; their
  40-run cells are `probes/tsan-runs/summary-f1-queued-writer.tsv`), one
  per claim of the model:
  the return-value envelope at unlocked / held cells (`muUncontended`,
  `muLocked`, `rwMatrix`, `rwTryRLockPendingWriter`), the acquisition
  identity (`muUnlockAfterTryLock`, `muFalseThenLock`), the spin shape
  (`muSpinUntilTryLock`), the detector derivation — the state CAS on an
  unlocked Mutex vs a plain overwrite (`muOverwriteVsTryLock`), the FAILED
  path's realized nothing (`muOverwriteLockedVsFailedTryLock`,
  `muCopyVsFailedTryLock`), the confounded overwrite-resets-to-unlocked
  shape (`muOverwriteVsFailedTryLock`, probe only), the success-edge-only
  HB (`muDrfTryLockPublish` green vs `muRacyTryLockNoAcquire`,
  `muFailedTryLockNoEdge` red), and the RWMutex twins (`race.Read(&rw.w)`
  on every outcome — `rwOverwriteVsTryRLock`, `rwOverwriteVsFailedTryRLock`;
  the acquire edges — `rwDrfTryLockPublish`, `rwDrfTryRLockAcquire`). Each
  header states the EXPECTED verdict and why. NOT corpus cases; the shapes
  that became corpus rows live in `Corpus/coverage/exec/sync/trylock/`,
  `race/negative-sync/`, `race/free-sync/`.
- `probes/run-tsan.sh` — the runner: builds plain and `-race`, N runs per
  subject at GOMAXPROCS 1 and 8; per subject RACE / green / other counts
  and the distinct plain outputs. Writes only `probes/tsan-runs/`
  (`summary.tsv`, `go-version.txt`, one `*.first.txt` per cell).
- `twin-pin/diff-twin-pin.py` + `diff.txt` + `hashes.txt` — the
  structural diff of the pinned raft twin wire before/after this slice
  ([USER] ruling (A): enumerate exactly which entries change).
- `baseline-drift.txt` — `scripts/coverage-baseline-diff --full` after the
  re-pin (no regression, 3278 rows); `gate-tail-run3-dirty-prepin.txt` —
  the post-rebase dirty-tree `ci --diff` summary (every step ok; the ONLY
  FAIL was the expected baseline drift before the re-pin — the drift list
  vs main 221d8964's pin = exactly this slice's 20 rows); `gate-tail.txt`
  — the CLEAN-tip `ci --diff` after the fix-round commit.
- `choice-trace/` — the consumption-invariance comparison: the labeled
  consumption tracer (`scripts/choice-trace-corpus`) over the 179 `sync`-
  tagged rows shared by main and this branch, run on main's tree (a
  detached scratch worktree at c22e367a, its own frontend + binary) and on
  this branch; `compare.txt` lists any row whose per-stream consumption
  count / per-site tally differs.

## Reproduction (repo root)

    docs/evidence/2026-09-03_q-trylock/probes/run-tsan.sh 20
    python3 docs/evidence/2026-09-03_q-trylock/twin-pin/diff-twin-pin.py c22e367a
    scripts/capped scripts/ci --diff
    scripts/coverage-baseline-diff --full
    # choice-trace (both trees; the id list = the intersection of
    # `scripts/coverage list --tag sync | cut -f1` on each, minus the two
    # spinners atomics/spin/flag-wait and race/atomics-free/cas-failure-acquires):
    scripts/choice-trace-corpus --jobs 4 --out artifacts/choice-trace <ids>

## Toolchain, commit, host

- Go: `go version go1.26.5 linux/amd64` (the pin in
  `baselines/go-oracle-pin`; `probes/tsan-runs/go-version.txt`).
- Lean: the repo's pinned toolchain (`lean-toolchain`), `golean` built by
  `scripts/capped lake build` in this worktree.
- Commit: the probes and gate runs were made on lane `q-trylock` branched
  from main c22e367a, with the slice UNCOMMITTED in the working tree
  (dirty) — the commit that carries this directory is the slice's; the
  final gate tail records its tree state.
- Host: linux/amd64, 32 cores, shared with other agents' enumeration
  jobs at the time (load-sensitive numbers: none of the counts below are
  timing-based; the one timing observation — the spin row's quadratic
  fuel-out, TODO.md — is order-of-magnitude only).

## Conclusions (2026-09-03)

1. **Return-value envelope.** gc realizes ONLY the success member at an
   acquirable cell: `muUncontended` true 20/20 (plain and `-race`,
   GOMAXPROCS 1 and 8); `rwMatrix` = `true true | true false | false false`
   20/20; held cells false 20/20 (`muLocked`; `rwTryRLockPendingWriter`
   false 20/20 — the documented writer-pending exclusion). The spurious
   member the model carries (mem#locks: "may be considered to be able to
   return false even when the mutex l is unlocked") is UNEXHIBITED in
   isolation — permitted by the text, never a strict pin; the membership
   rows record it as `unexhibited=1`.
2. **Detector, Mutex.** An overwrite beside a TryLock on an UNLOCKED
   mutex is RACE 20/20 (`muOverwriteVsTryLock`: the state CAS vs the plain
   write); a plain overwrite-with-a-LOCKED-value or a copy beside a FAILED
   TryLock is green 20/20 (`muOverwriteLockedVsFailedTryLock`,
   `muCopyVsFailedTryLock`) — the failed path realizes nothing
   (`internal/sync` is a noRaceFuncPkgs package). The confounded shape
   `muOverwriteVsFailedTryLock` (the overwrite resets the mutex to
   UNLOCKED) is RACE 9–11 of 20 per cell — schedule-dependent in gc (when the
   reset lands first the TryLock succeeds and its CAS races), pinnable in
   no lane; probe only.
3. **Detector, RWMutex.** `race.Read(&rw.w)` precedes `race.Disable` on
   every outcome: an overwrite beside a TryRLock is RACE 20/20 whether the
   call succeeds (`rwOverwriteVsTryRLock`) or is forced false by a held
   writer (`rwOverwriteVsFailedTryRLock`).
4. **HB, success-edge-only.** `muDrfTryLockPublish` / `rwDrfTryLockPublish`
   / `rwDrfTryRLockAcquire` green 20/20 (a successful call IS a Lock/RLock
   acquire); `muRacyTryLockNoAcquire` RACE 20/20 (the pair orders nothing
   toward an unlocked read); `muFailedTryLockNoEdge` RACE 20/20 — a failed
   call acquired nothing ("no synchronizing effect at all"). The machine
   agrees on every one (corpus rows `race/negative-sync/{overwrite-vs-
   trylock,failed-trylock-no-edge}` RACE-ALL; `race/free-sync/{trylock-
   publish,rw-trylock-publish}` confluent, `rw-tryrlock-acquire`
   membership {0, 8}).
5. **Twin pin.** Exactly ONE entry of the pinned twin wire changed:
   `sync.Mutex.TryLock` (declaration-only stub → bodied stub;
   `unsupported` removed) — `methods[515]` against c22e367a before the
   rebase, `methods[518]` against main 221d8964 after it (main's
   stdlib-source-1 rows shifted the index; same entry); no RWMutex entry
   exists in the twin's method set. Pin `45cd882a6e09…` → `f2309df29148…`
   (the pre-rebase pair `eef32142627a…` → `c824f9e4d27f…` kept as
   history; `twin-pin/hashes.txt`, `diff.txt` regenerated against
   221d8964).
8. **F1 (audit fix round): TryRLock vs a QUEUED writer.** At the model
   state (writer = false, readers = 0, pendingW > 0) gc's TryRLock is
   TRUE when the pending writer is queued behind `rw.w` — 40/40 plain at
   GOMAXPROCS 1 and 8, 40/40 `-race` at 1, 39/40 at 8 — and FALSE when
   it is past `readerCount.Add(-max)` (`rwTryRLockPendingWriter`, 20/20).
   Control D: gc's blocking RLock also returns before the queued writer
   acquires — 40/40 plain at both GOMAXPROCS, 17/40 and 20/40 under
   `-race`. Consequence: TryRLock's acquirability widened to `!writer`
   (machine ⊇ gc on both phases; sync design §8 R1's value-observable
   half; an [AGENT] widening in the safe direction, RATIFIED [USER] 2026-09-03 («TryRLock decision sounds fine», relayed by the [AGENT] coordinator)); the per-program sets are unchanged.
6. **Gate.** Full `ci --diff` on the rebased dirty tree: every step ok; the
   drift vs main 221d8964's pin = exactly +18 born-PASS rows and 2
   FAIL→PASS flips (the two TryLock frontier reds), NO PASS→non-PASS, no
   other movement; re-pinned to 3278 rows (3078 PASS / 200 FAIL). The
   clean-tip run is `gate-tail.txt`. (Pre-rebase: 3199 → 3216, 17 rows.)
7. **Consumption invariance.** Pre-rebase: `choice-trace/compare.txt` —
   main (c22e367a) vs branch over the 179 shared sync-tagged rows × 6
   streams: only the two flipped rows differ (they consume one `tryLock`
   pick per stream); every other (id, stream) line identical. Post-rebase,
   at the fix-round tip d286ebe1: `choice-trace/trylock-consumers-d286ebe1.txt`
   — 196 sync-tagged rows × 6 streams, 0 violations / alarms /
   driver-agreement mismatches, `tryLock=90` consumptions, and the ONLY
   ids consuming the site are this slice's rows (every held-state row
   consults at bound 1 and pops nothing).

Provenance: the rulings this directory evidences are the [USER]'s
(relayed); the probe design, the derived detector table and the spurious-
member recording decision (`.atomicWrite @state` on BOTH Mutex members —
gc's lost CAS is the spurious member's realization; the refusal-permitted
direction of the row-9 ruling) are [AGENT], flagged for the audit.
