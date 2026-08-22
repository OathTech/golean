# Campaign Arc 2 — the witness route study (lane `campaign-arc2`)

Governing: `docs/2026-08-21_raft-proof-constitution.md`; parent log
`docs/raft-campaign-log.md` (campaign lane). One writer: the Arc-2
worker. Unit 1 = the route study (measure kernel frontier, study
completion machinery, route memo + unit-2 charter).

## Units

- **U1 prelude** (2026-08-22): Arc 1's statement layer copied VERBATIM
  from `campaign`@b2d9dd1b (`git checkout b2d9dd1b -- <paths>`; the
  four files + wire pin + aggregator block) @ 365d3ab0. Not modified
  here; merges from either lane later.

- **U1 measurements** (2026-08-22): full proofs build green on this
  lane with the copied layer (468 jobs, `scripts/capped lake build`,
  48G/4-thread). Probe A (census, compiled): initSteps=1382,
  subjSteps=711,616, verdict = the U-c7 record exactly; census 226
  static call fids + 9 value-call fids, defer fids unresolved (gap).
  Kernel K-ladder (smartUnfolding false, `with_unfolding_all rfl`):
  K=0/10/100/1000 PASS at 32/33/55/111 s, peaks 6.1–15.6 GB; without
  the option K=0 OOMs past 48G. Records:
  `docs/campaign-arc2-probes/records/`.

- **U1 conclusion** (2026-08-22): K=10000 kernel probe DNF — timeout
  3000 s at 63.4 GB under the 64G cap (the kill point recorded as the
  measurement). Probe C: heap append-only, 103 → 36,376 cells over
  the run (heapLen = nextAddr throughout). Route memo COMPLETE
  (`docs/2026-08-22_campaign-arc2-witness-route.md`): (a) refuted on
  memory (≥3.1 TB extrapolated), (b) wrong instrument for an
  ∃-witness (census: 226+9 functions), RECOMMEND (c) checkpointed
  segment walk with slice-1 mid-run measurement as go/no-go, (d)
  verified fast-twin evaluator armed as fallback. Unit-2 charter in
  memo §5.

- **U2** (2026-08-22, coordinator-directed: the go/no-go measurement):
  `StateWire.lean` (ToExpr derives + `twinCheckpoint%`, fail-loud,
  table-drift-checked) + `TwinCheckpoints.lean` (ckpt350k) built —
  3:47 / 2.7 GB / 101 MB olean; both in the aggregator (1b2). Gap
  closes: K=0 peak RSS 6.0 GB (polled rerun); defer callees resolved
  (probe A2: 8 distinct, 272 registrations = probe A's defer-site
  executions exactly; complete census 226+9+8 = 243 functions).
  Mid-run kernel segments from ckpt350k (heap 19,093 cells):
  100 → PASS 2:13/16.1 GB; 250 → PASS 7:46/39.7 GB; 500 → OOM(137)
  under 48G at 11:33. Marginal 2.22 s/step, 157 MB/step.
  **VERDICT: NO-GO for route (c)** (projected 440–800 CPU-h vs the
  200 CPU-h trigger; ~10² GB checkpoint storage; the box cannot run
  the asked 8/16-way parallelism at 48G caps). Unit 3 = fallback (d)
  charter, memo §6.4. Records: `records/seg350k.out`,
  `records/probeA2-defercallees.out`.

- **U3** (2026-08-22, coordinator-directed: the (d) gate — microbench
  BEFORE any evaluator build): trie microbench
  (`trie-bench.lean`, seed 36,376 = probe C's end-of-run heap;
  structural recursion only; forced final fold; expected values
  #eval-first; pre-stated PASS targets ≤25 ms/op, ≤2 MB/op).
  16G points OOM'd — the arithmetic identified the cap as mis-sized
  for the in-kernel seed build (36,376 inserts ≈ 17 GB), kill points
  recorded. 48G: nops=0/1000/10000 all PASS (4:25/17.7 GB,
  4:39/18.1 GB, 6:04/22.1 GB); marginal **9.4 ms/op, 0.44 MB/op** —
  **GATE PASSES with >2× headroom** (~240×/~360× better than the
  list heap per op). (d) projection: 4–60 CPU-h, ~14 fast segments.
  Memo §6.5 (results), §6.6 (Arc-4 Sym convergence carry-forward,
  per directive), §6.7 (unit-4 evaluator charter with its own
  mid-build measurement gate). Records:
  `records/trie-bench.out`.

## Judgment calls

- **[AGENT]** 2026-08-22: copy mechanism is path-checkout from the
  exact commit rather than file copy — verbatim by construction, no
  hand-transcription risk.
- **[AGENT]** 2026-08-22: measured the exact step count with a
  custom counting loop mirroring `runProgramM`'s wiring instead of
  #eval-bisecting `twinRun` (one 12-min run vs hours of probes);
  drift risk closed by requiring the probe's verdict to equal the
  U-c7 record — it does.
- **[AGENT]** 2026-08-22: kernel probes run as `scripts/capped lean`
  with `lake env`'s LEAN_PATH sourced once, NOT `capped lake env
  lean` — a second lake against the same workspace wedged and died
  SIGTERM with zero output while a sibling lake ran (operational
  note; no script touched).
- **[AGENT]** 2026-08-22: `set_option smartUnfolding false` added to
  the kernel probe files after the optionless K=0 OOM'd at 48G — the
  kit's L5 rule applied, measured mandatory at this scale (both
  outcomes recorded, kprobes-small.out).
- **[AGENT]** 2026-08-22: the route recommendation ((c) with armed
  fallback (d)) — memo §5; the leaner-witness-driver observation
  deliberately NOT proposed (it would re-pin the statement; Arc-1
  files immutable on this lane, re-pins supervised).
- **[AGENT]** 2026-08-22 (U2): seg-2000/8000 NOT run after seg-500's
  OOM — a longer window OOMs at the identical prefix point (zero
  information); replaced by 100/250 slope points. The coordinator's
  sizes were indicative ("e.g."); the slope is what the projection
  needs. Files kept; the record says why.
- **[AGENT]** 2026-08-22 (U2): NO-GO called by the charter's own
  numeric trigger (440–800 CPU-h projected > 200) — not a judgment
  against the route's soundness (mid-run segments ARE checkable at
  ≤ 250 steps; the reflector works); a judgment that (d)'s ~500×
  heap-op improvement is the honest next move. (d) needs no ruling:
  §3.1's accelerator template, proof-side, statements untouched.
- **[AGENT]** 2026-08-22 (U2): checkpoint index 350,000 — the
  directive's 300k–400k range wins over its "~36k-cell scale" gloss
  (36k cells exists only at the run's END, outside the range); the
  projection carries the heap-linear 2× band to cover the late run
  instead. Memo §6.2 states this in place.
- **[AGENT]** 2026-08-22 (U3): microbench targets set BEFORE the
  kernel runs (≤25 ms/op, ≤2 MB/op — derivation in memo §6.5); the
  16G kill points read as cap-sizing, not target-miss (nops=0
  contains the 36k-insert seed build; the real evaluator's seed is a
  reflected literal, never kernel-built — recorded as a design rule).
- **[AGENT]** 2026-08-22 (U3): all bench recursion STRUCTURAL — the
  kernel does not usefully reduce `WellFounded.fix`; recorded as a
  binding design constraint for the unit-4 evaluator (and for any
  kernel-checked route, §6.6).
- **[AGENT]** 2026-08-22 (U3): unit ends at gate-PASS +
  design/charter, NOT a half-built evaluator — units sized to one
  session, every unit parkable (gallery case law); unit 4 opens on
  the §6.7 charter with the mid-build measurement gate as its own
  go/no-go.
- **[AGENT]** 2026-08-22 (U2): `TwinCheckpoints` kept in the
  aggregator (a fresh full build pays 3:47 + a 101 MB olean once) —
  the checkpoint is unit-3's reusable input and the 1b2 sweep wants
  proofs modules in the audited closure; revisit if the artifact
  count grows.

- **U1 GATE** (2026-08-22): `GOLEAN_ALLOW_NO_DIFF=1
  GOLEAN_MEM_MAX=24G scripts/ci` — **RESULT: PASS** (rc 0; the
  no-diff hatch's visible note present — fresh-lane docs+proofs arc,
  the sanctioned case; comparator-landmark staleness note is
  report-only and no designated statement changed on this lane;
  the 1b2 sweep passed with the copied Specs modules in the
  aggregator). Log: artifacts/arc2-gate.log (untracked artifact;
  result restated here). **ARC 2 UNIT 1 BRANCH-COMPLETE** at this
  tip.

## Checkpoint (U1 end, recomputed)

Branch `campaign-arc2` @ (tip after this commit): 3 commits over
f64d9b21. Proofs build green with the copied statement layer (468
jobs). Measurements: 711,616/1,382 steps; kernel ladder
32/33/55/111 s PASS + K=10000 DNF(50 min, 63.4 GB); heap 103→36,376
cells. Deliverables: route memo (complete), probes + records, this
log. Nothing merged; no GoCore/frontend/scripts edits; Arc-1 files
unmodified (verbatim-copied only).

- **U2 GATE** (2026-08-22): `GOLEAN_ALLOW_NO_DIFF=1
  GOLEAN_MEM_MAX=24G scripts/ci` — **RESULT: PASS** (rc 0) at
  338a0662 + this docs-only delta (memo §6.2/§6.3 refinements and
  these log entries; no build input changed after the gate ran —
  `git diff 338a0662 -- . ':!docs'` is empty). Visible notes: the
  sanctioned no-diff hatch; comparator-landmark staleness
  (report-only; no designated statement changed on this lane).
  **ARC 2 UNIT 2 BRANCH-COMPLETE** at this tip.

## Checkpoint (U2 end, recomputed)

Branch `campaign-arc2` @ (tip after the U2 commits): U1's 5 commits
+ U2 over f64d9b21. New modules: `Specs/StateWire.lean`,
`Specs/TwinCheckpoints.lean` (both in the aggregator; build green).
U2 measurements (records in `docs/campaign-arc2-probes/records/`):
reflector build 3:47/2.7 GB/101 MB olean; mid-run segments
100 PASS (2:13, 16.1 GB), 250 PASS (7:46, 39.7 GB), 500 OOM(137)@48G;
marginal 2.22 s/step, 157 MB/step at 19k cells; census complete
(243 = 226+9+8). VERDICT: NO-GO (c) → unit 3 = fallback (d), memo
§6.4. Nothing merged; no GoCore/frontend/scripts edits; Arc-1 files
still verbatim.
