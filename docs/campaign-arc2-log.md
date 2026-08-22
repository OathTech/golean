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

## Judgment calls

- **[AGENT]** 2026-08-22: copy mechanism is path-checkout from the
  exact commit rather than file copy — verbatim by construction, no
  hand-transcription risk.
