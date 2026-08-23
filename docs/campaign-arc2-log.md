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

- **U4 opens** (2026-08-23, coordinator-directed): design note
  `docs/2026-08-22_fasteval-design.md` (the three measured discoveries:
  the 3-function heap funnel, address-ascending append-only heap,
  structural-only kernel recursion; the two surface-collapsing moves:
  one-directional refinement with fail-closed stubs, lazy γF view for
  pure helpers — the latter discovered to also DELETE the WF-invariant
  threading: γH is total via dummy-dump and the single `γF σF₀ = s₃`
  kernel equality forces exact representation). Probe D (exercised-arm
  census) written + running. `FastEval/Heap.lean` (trie + γH + the
  primitive commute lemmas) and `FastEval/Ops.lean` (ExecStateF, γF,
  loadLocF/storeLocF/allocF + one-directional sims) BUILD GREEN.

- **U4 progress** (2026-08-23, mid-unit): FastEval core committed
  (c5716245). The authorized wave LAUNCHED — three forked workers on
  strictly disjoint files (Values.lean = applyStrictOpF;
  Stores.lean = store/stmtOp tower; Frames.lean = frames/sync/mapIter
  tower), each briefed with the template + wrinkle register + the
  probe-D census as the stub law; I integrate and re-verify.
  Parallel (my files, disjoint from the wave): `StateWire.lean`
  extended with the trie emitters (`twinCheckpointF%`,
  `twinPreludeF%`); `TwinCheckpointsF.lean` (seed + 350k trie
  checkpoints) built 2:38/2.1 GB; `TwinPrelude.lean` (the prelude
  equation `runProgramSetupM 711616 … = .ok (…, γF twinSeedF, …)`
  kernel-checked + the γ-agreement folded into its statement) in
  flight.

- **U4 wave + integration + mid-build gate** (2026-08-23): the
  authorized wave returned — A (Values, 700 l), B (Stores, 1,096 l),
  C (Frames, 641 l), all green, all re-verified by my own capped
  builds and spot-checked (axioms, API shapes); committed with
  attribution. Integration: all WIRE arms flipped; `stepFast_ok`
  re-proved over the complete evaluator (29 manual cases over 8
  hoisted conditioned arm equations); helper panic-conversion arms
  stubbed fail-closed (no error transport in a one-directional
  refinement; census shows no panics). `twin_prelude_eq`
  kernel-checked (8:18/36.7 GB). Mid-build gate: fast-500 kernel
  PASS 2:28/21.6 GB (slow: OOM@48G 11:33); fast-2000 OOM@40G 7:49
  (kill point). VERDICT: **MARGINAL GO** — memo §6.8; unit 5 staged
  (batch emitter + segment wave + composition), not executed. Full
  proofs build green (480 jobs); Audit/FastEval.lean pins; aggregator
  wired. Records: `records/fastseg.out`.

- **U5 opens** (2026-08-23, SUCCESSOR worker; predecessor's transcript
  rotated — artifacts re-verified, not trusted): re-verification at
  0c462c7c — fresh capped build PASS (480 jobs, rc 0); `#print axioms`
  fresh on stepFast_ok / iterF_ok / iterF_add / twin_prelude_eq =
  the Audit/FastEval pins verbatim; hatch grep over FastEval/ + the
  new Specs modules clean (docstring mentions only). Lever
  measurements (records/fastseg2.out): fastseg-k2000@48G **OOM(137)
  at 507 s** — §6.8's "~2,900 steps at 48G" extrapolation REFUTED
  (retention past 500 steps is ~16.7–20 MB/step, not 14.5);
  fastseg-k1000@36G **PASS 3:59 / 30.0 GB**. Decomposition over the
  three 350k points: marginal 0.182 s/step + 16.7 MB/step, fixed
  ~57 s + 13.3 GB/segment. **Re-projection at SEG=1000: central
  ~53–55 CPU-h (band ~45–67) < the ~60 CPU-h pause trigger ⇒ GO.**
  Batch emitter landed (`twin_ckpt_groupF%` in StateWire: ONE
  incremental compiled pass per group, `addDecl` without compiled
  code) and gate-checked (emitter-gatecheck.lean, 3:49 under 24G):
  the batch-incremental literal at 350k is KERNEL-EQUAL to the
  from-0 `ckptF350k`, and the exact U5 segment shape
  (equality-to-next-literal, 100 steps) kernel-checks. Generator +
  orchestrator + manifest landed (gen-u5-modules.py,
  u5-orchestrate.sh, u5-manifest.sh): 712 segments × 1000 steps
  (last 616), 45 checkpoint groups × 16, rollup + composition
  generated and stamped; manifest recomputed from oleans, never
  restated.

## THE U4 PER-ARM TEMPLATE (of record, for the authorized wave)

Validated on the landed `FastEval/Ops.lean` (its own header carries
the same rules):

1. **Mirror**: copy the def; suffix `F`; `ExecState` → `ExecStateF`;
   the three heap primitives → `loadLocF`/`storeLocF`/`allocF`; every
   PURE helper call keeps its exact shape but at state `γF σF` (the
   lazy view — never materializes); arms not in probe D's census →
   `stuck "fastEval-stub: <def>.<arm>"`. No `partial`, no `sorry`.
2. **Slow-side arm equations** (only where the sim needs to step the
   ORIGINAL under known scrutinees): hypothesis-conditioned lemmas in
   the StepKit style, proof `simp only [<def>, <scrutinee eqs>]; rfl`
   (this both unfolds and iota-reduces the matches; `rfl` closes the
   join-point/bind plumbing).
3. **Sim** `<f>F_ok : <f>F σF … = .ok r → <f> (γF σF) … = .ok (γ-image r)`:
   `unfold <f>F at h`; `split at h` down the def's own match/if tree
   (each split names its scrutinee equation); at an Except-valued
   call: `cases hn : <call> with | error e => rw [hn] at h; simp
   [Bind.bind, Except.bind] at h | ok x => rw [hn] at h; …` — NOTE
   `cases hn :` substitutes the GOAL only, so `rw [hn] at h` (never
   `at h ⊢`); slow side stepped by the arm equations; state images
   close by `γF_store_image`/`allocF_state`; recursion via the def's
   own structural IH; STUB arms close vacuously (`simp at h`).
4. Every public theorem `#print axioms`-pinned (assembly collects the
   pins); docstrings carry the never-in-a-statement-closure line.
5. **LOOPS** (added after `Loops.lean`/`Shared.lean` landed): the
   core's `for i in [:n]` loops are `Std.Legacy.Range.forIn` over a
   PRIVATE well-founded loop — unnameable and kernel-hostile. Fast
   mirrors write loops as `forIn (List.range' 0 n 1) init body`
   (structural, kernel-reduces); sims use `list_forIn_sim`
   (`FastEval/Loops.lean`, the one-directional relational transport)
   plus the core bridge `Std.Legacy.Range.forIn_eq_forIn_range'`
   (simp with `Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
   Nat.div_one` to normalize the size). Worked exemplar with every
   wrinkle: `sliceVisibleValuesF_ok` (`FastEval/Shared.lean`).
6. **The elaboration wrinkles that cost this session time — read
   before writing a sim** (each observed, not theorized):
   - a slow-side `let mut`/`for` body elaborates with an extra
     `pure PUnit.unit` statement — spell your `body :=` in the sim to
     MATCH the original's elaborated shape or `rw` will not fire;
   - `rw [<eq>]` on a goal whose lambda-internal binds were already
     simp-rewritten will not match a bind-spelled equation — rewrite
     FIRST, simp after;
   - `cases hn : <call>` substitutes the GOAL only, never hypotheses —
     `rw [hn] at h`, never `at h ⊢`;
   - `split at h` names each branch's scrutinee equation — use it for
     matches; `cases hb :` + `rw at h` for `Except`-valued calls;
   - after `subst hR` the surviving accumulator binder is the FAST
     side's (`b'`).
7. **Wave-worker additions** (folded from the three reports, each
   observed in a landed proof):
   - `split at h` on a VARIABLE scrutinee substitutes and yields NO
     equation; on an APPLICATION scrutinee it yields one — binder
     counts differ; use bullets + `rename_i` for the LAST hypotheses
     only, with non-shadowing names (a shadowed `op` silently breaks
     later rewrites).
   - error-headed fast sides (`stuck`/`throw` are defs, not ctors):
     close via `rfl`-lemmas `stuck_eq_error`/`throw_eq_error` + the
     `goErrAbsurd`-style closers (Frames.lean; promotion candidates).
   - the per-call rhythm is strict — `rw [hcall] at h` THEN
     `simp only [Bind.bind, Except.bind] at h`, one layer at a time;
     an early simp pre-unfolds lambda-internal binds into matches
     that later refuse iota.
   - per-module auxiliary MATCHER constants: a display-identical slow
     body can be `rw`-opaque because the goal uses Machine.lean's
     matcher — fix by a defeq `show` onto this module's matchers
     (Stores.lean sortSlice/append exemplars).
   - do-mut loops over an `Array` iterate the Array instance — bridge
     `rw [← Array.forIn_toList]`; MProd accumulators eta-expand.
   - `fun_cases` on a stepFast-sized def renumbers ALL case tags on
     any arm change — stash manual case bodies, re-enumerate tags
     from a sorry-swept build, re-attach (this unit's integration
     cycle; case-tag drift is mechanical, not semantic).
   - census classifier blind spot: NULLARY ops never appear under
     their continuation rows — check the `evalE` rows before
     stubbing (worker A's defaultValueOf/nilLit catch).

- **U4 GATE** (2026-08-23): `GOLEAN_ALLOW_NO_DIFF=1
  GOLEAN_MEM_MAX=32G scripts/ci` — **RESULT: PASS** (rc 0; the
  sanctioned no-diff hatch with visible notes; FastEval + checkpoint
  modules + Audit/FastEval pins all inside the audited closure —
  the 1b2 sweep and the in-build Audit gate passed over them; no
  designated statement changed on this lane). ONE note carried
  forward per the Arc-3 precedent: **comparator landmark OWED
  (scope)** — `proofs/Audit.lean` (my one-line `import
  Audit.FastEval` addition) is in Challenge's trusted closure, so ci
  step 1c4 flags the §3.8 judge obligation; the judge is a MERGE-time
  landmark (constitution §3.8/§4.1) and this lane ends
  branch-complete without merging — **flagged for the operator's
  merge step**, exactly as the campaign log already flags Arc 3's.
  **ARC 2 UNIT 4 BRANCH-COMPLETE** at this tip; unit 5 opens on memo
  §6.8's staged plan.

## Checkpoint (U4 end, recomputed)

Branch `campaign-arc2` @ (tip after the gate commit): 19 commits over
f64d9b21 at this writing (git log the authority), tree clean at each
commit. U4 delta: 9 FastEval modules (~5,100 lines incl. the wave's
2,437), TwinCheckpointsF/TwinPrelude, Audit/FastEval.lean pins,
aggregator wiring, probes + records, memo §6.8, this log. Proved at
the tip: stepFast_ok, iterF_ok/iterF_add, list_forIn_sim, the three
wave towers' sims, twin_prelude_eq — all pinned, zero hatches.
Measured: fast-500 PASS 2:28/21.6 GB; fast-2000 kill 7:49@40G;
MARGINAL GO recorded with levers. Unit 5 staged (memo §6.8), not
executed. Nothing merged; no GoCore/frontend/scripts edits; Arc-1
files verbatim.

## Judgment calls

- **[AGENT]** 2026-08-23 (U5): the RSS poll harness's first version took
  max over ALL lean pids and was polluted by a sibling lane's build —
  fixed to walk only the launched job's descendants; the two affected
  runs' peaks are reported as CAP-BOUNDED (rc-0-under-cap / killed-at-
  cap), never as polled numbers (records/fastseg2.out states this).
- **[AGENT]** 2026-08-23 (U5): segment size 1000 @ 36G cap, NOT the
  charter's 48G-segments lever — the lever's ~2,900-steps-at-48G
  assumption failed measurement (k2000@48G OOM); at the measured
  16.7 MB/step + 13.3 GB fixed, 1000 steps @ 36G is the projection's
  optimum that still fits a 2-wide wave beside the sibling lanes
  (2×36G + slack = 74G on the 125G box). Post-lever central estimate
  ~53–55 CPU-h ≤ the ~60 CPU-h pause trigger ⇒ GO, logged with the
  full derivation in records/fastseg2.out.
- **[AGENT]** 2026-08-23 (U5): this Lake (5.0.0) has no jobs flag, so
  the directive's "2–3 concurrent detached capped jobs" is realized as
  BATCHED lake invocations — exactly 2 pending segment targets per
  capped call (lake parallelizes within the batch), one lake at a time
  (the U1 wedge rule), manifest recomputed from oleans after every
  batch (= the per-wave checkpoint), resume = rerun (fresh oleans
  skipped at selection).
- **[AGENT]** 2026-08-23 (U5): aggregator wiring DEFERRED to the
  composition step — importing the rollup mid-run would make any gate
  build try to finish the wave at the gate's 24G cap; the aggregator
  gets TwinWitness (and transitively everything) only once the wave
  is complete.
- **[AGENT]** 2026-08-23 (U5): checkpoint-group emission is from-0 per
  group (each group's one compiled pass re-runs the prelude + prefix)
  rather than chaining group modules by import — keeps groups
  build-independent and parallel; total compiled cost ~1.5 CPU-h,
  measured negligible against the kernel wave.

- **[AGENT]** 2026-08-23 (U4): helper panic-conversion arms stubbed
  rather than proving error-correspondence — the one-directional
  refinement deliberately has no error transport, the census shows
  the run never panics, and a wrongly-stubbed panic would surface as
  an honest fast-run elaboration failure, never a false theorem.
- **[AGENT]** 2026-08-23 (U4): the interpreted pre-check KILLED at
  20+ min (γF is interpreter-strict) and its stub-detection role
  reassigned to the kernel segment checks themselves — recorded in
  the memo; the 2000-point OOM is a memory kill, not a stub
  signature (stubs fail elaboration fast with a visible .error).
- **[AGENT]** 2026-08-23 (U4): MARGINAL GO called at the trigger
  boundary with the two unit-5-internal levers named (48G segments,
  batch emission) — a post-lever miss re-poses the §6.6 Sym
  convergence rather than pushing through.

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

- **U3 GATE** (2026-08-22): `GOLEAN_ALLOW_NO_DIFF=1
  GOLEAN_MEM_MAX=24G scripts/ci` — **RESULT: PASS** (rc 0) at the U3
  commit (U3 is docs-only over U2's audited build inputs — the bench
  lives under `docs/campaign-arc2-probes/`, no proofs/GoLean change).
  Visible notes unchanged in kind: sanctioned no-diff hatch;
  report-only comparator-landmark staleness (no designated statement
  on this lane). **ARC 2 UNIT 3 BRANCH-COMPLETE** at this tip; unit 4
  opens on the memo §6.7 charter.

## Checkpoint (U3 end, recomputed)

Branch `campaign-arc2` @ (tip after this commit): 9 commits over
f64d9b21, tree clean. U3 delta: docs-only (microbench probes +
records + memo §6.5–§6.7 + log). Measurements: trie marginal
9.4 ms/op / 0.44 MB/op at 36,376 entries (PASS vs pre-stated
≤25 ms / ≤2 MB); 16G kill points recorded; the (d) route is GO with
unit 4's mid-build gate armed. Nothing merged; no
GoCore/frontend/scripts edits; Arc-1 files verbatim.

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
