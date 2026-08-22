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
