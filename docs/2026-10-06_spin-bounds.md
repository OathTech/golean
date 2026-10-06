# Spin bounds in loop iterations, not raw steps (2026-10-06)

[AGENT] worker, lane `lane/fr36-spin-bounds-1006`. Authority: [USER] Mike 2026-10-06, verbatim,
relayed by the [AGENT] coordinator — cite as relayed: «Yeah, let's do 3+4» (item 4 = this note); the
follow-up it discharges is train r59's «spin bounds in loop iterations, not raw steps»
(`docs/2026-08-31_qrow-rulings.md`, the C4 ruling; `docs/2026-10-01_block-allocation-handoff.md` §4).
Design written BEFORE the change; §4 holds the measurements taken after it.

## 1. Today's mechanism

- Lane param `nonterm=N` (membership-only; `scripts/coverage-manifest` + `scripts/diff-coverage`
  `parse_lane_params`) → `golean coverage-observations --allow-nonterm N` → `explore` sets the
  PER-BRANCH budget `runFuel := N` in POOL STEPS (`GoLean/CLI.lean`: `poolDFS` decrements `fuel`
  once per `stepMulti`; the alias-guard probes run `enumRunProgram` under the same fuel). A branch
  that exhausts it is counted into `EnumOutcome.nonterm` — never a member — and the row's claim is
  «oracle observation ∈ TERMINATING members». Without the flag a fuel-out branch fails loud.
- Rows using it (the whole population; all spin loops, all `width=4,sites=200,members=1,
  nonterm=200,backedge=1`): `goroutines/send-then-spin/-`, `sync/trylock/spin-until-trylock`
  (`work=500000` since C4), `race/atomics-free/cas-failure-acquires`, `atomics/spin/flag-wait`.
- Why it flips: the spin's iteration is k machine steps, so N steps = N/k iterations; a refactor
  that changes k (C4: −2 per iteration) changes how many iterations — and therefore how many
  branch points — fit in a nonterm branch. The terminating tree was identical across C4
  (`leaves=2571`, `maxdepth=18`, set {42}); the NONTERM branches grew 4242 → 6702 and the work
  135k → 241k, past the 200000 default. The bound was never about steps.

## 2. The change

- NEW lane param `iters=K` → CLI `--allow-nonterm-iters K`: the per-branch budget counted in LOOP
  RE-ENTRIES. A pool step is a re-entry iff the stepped goroutine (`StepEvent.who`) was, before
  the step, `.running c none` with `c.boundarySite = .backEdge` — the stage-D back-edge shapes
  `.next (.loop …)`, `.signal .cont (.loop …)`, `.next (.mapIterK …)` (`GoLean/GoCore/Multi.lean`
  `Config.boundarySite`, the envelope statement of `ChoiceSite.backEdge`). The flag-clear step
  (`.running c (some _)` → `.opDoneStrip`) is not a re-entry, so an iteration counts once. This is
  the machine's own iteration vocabulary, read through a public definition — no core change.
- A branch whose (K+1)-th re-entry is taken is counted `nonterm` (the same bucket, the same
  claim). Probe runs (`enumPoolRun`) count re-entries identically and are cut at the same K.
- The per-branch STEP fuel under `iters=` is the run default (10 M), a safety net only. Its
  exhaustion under the iteration accounting is a NAMED refusal («the iteration bound is not the
  binding one»), never a nonterm count — fail closed, never a pass. Declaring both `nonterm=` and
  `iters=` is refused.
- `nonterm=` / `--allow-nonterm` are RETIRED (the `samples=` precedent): the manifest and
  `diff-coverage` refuse the key by name, pointing at `iters=`; the CLI refuses the flag by name.
  The standalone consumers follow (`scripts/membership-sampling`, `scripts/detector-soundness`
  parse `iters=`; `tools/certification.py`'s ENUM_FLAGS; `scripts/test-lane-validation` S6). The
  run record prints `allow-nonterm-iters=K nonterm=<count>` (the OUTPUT counter keeps its name).
- All four rows migrate to `iters=K`, K chosen per row in §4 so the certified set and `members=`
  are unchanged and the terminating tree is reproduced; each row's `why` records the measurement.
  `spin-until-trylock`'s `work=500000` is reverted to the default iff §4 measures ≥ 2× headroom.

## 3. NOT changed

- The semantic core: no new `Stop` constructor, no driver change; `native-json-run` and the
  coupling pin run under the default fuel as today (a `fuel-out` coupling observation stays the
  counted class under a declared accounting). The strict lane, `backedge=`, `sites=`, `width=`,
  `members=`, `work=`, `tier=`, `--engine dedup` (which refused `--allow-nonterm`; it refuses
  `--allow-nonterm-iters` the same way). No non-spin row's params or baseline semantics. The
  oracle pin. Records citing `nonterm=200` stay as written (dated).

## 4. Measurements (taken after the change; `docs/evidence/2026-10-06_spin-bounds/measurements.txt`)

REF = main's binary under the retired `--allow-nonterm 200`; NEW = the lane binary at the chosen K.
The desugared `for` body is ~45–60 machine steps, so 200 steps allowed ~1 re-entry (sync/atomic
spins) to ~5 (the empty spin) — which is why K=10 is a far LARGER budget than the old one.
- `sync/trylock/spin-until-trylock`: REF leaves 2571, maxdepth 18, nonterm 6702, work 240834;
  **K=1** reproduces leaves 2571 / maxdepth 18 EXACTLY, nonterm 330, work 49235 → `work=500000`
  REVERTED to the default (≥ 4× headroom). Set {42}, members=1 unchanged.
- `race/atomics-free/cas-failure-acquires`: REF leaves 969 / maxdepth 14 / nonterm 720 / work
  33442; **K=1** exact (969/14), nonterm 65, work 19383. Set {5}.
- `atomics/spin/flag-wait`: REF 969 / 14 / 815 / 35249; **K=1** exact (969/14), nonterm 65, work
  19923. Set {42}.
- `goroutines/send-then-spin`: REF leaves 5641 / maxdepth 143 / nonterm 216 / work 29962. Its
  leaves are the L5 main-exit window's per-STEP exits, so no K reproduces the count exactly;
  **K=5** reproduces nonterm 216 with leaves 6596 / maxdepth 151 (≥ 143), work 33579. Set {42}.
- Control: `noodler/budget/loop-100k` under `--allow-nonterm-iters 1` is cut at its second
  re-entry (nonterm=1, observations=0, 139 steps) — the counter fires on the machine's shape.
- Larger K enlarges the terminating tree (more spins before the success are terminating paths
  too) without changing any set; K is the row's declared exploration depth in iterations.
`scripts/test-lane-validation` S6 (flag-wait's params) moved to `iters=1` with the row.
