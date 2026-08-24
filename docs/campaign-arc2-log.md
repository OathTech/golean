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

- **U5 emission + canaries** (2026-08-23): all 45 checkpoint groups
  emitted (one batched walk, 4-wide @30G; wall ~1h50 incl. ~10 min
  lost to the mtime-loop bug; late batches ~15–18 min each — the
  compiled prefix is heap-linear too). **Checkpoint artifacts: 184 MB
  total** for 712 checkpoints (olean same-module subterm compaction —
  the ~30–60 GB §6.8 storage projection was ~200× pessimistic).
  Canary variance (records/u5-manifest.tsv + wave log): S0000 192 s,
  S0001 215 s, S0700 **97 s** (late ≠ expensive), S0355 **406 s /
  43.9 GB peak** — a HOT WINDOW ~3× the 350k-boundary probe's
  retention (the k1000 probe passed at 30.0 GB from 350,000; steps
  355k–356k retain ~3× more). Mean per-segment wall over the four
  observed ≈ 227 s ⇒ 712 × 227 s ≈ 45 CPU-h — the pre-launch central
  holds; the DISTRIBUTION is wide, so the wave is continue-on-failure
  (failed batches recorded to records/u5-failures.txt, manifest =
  olean existence) with a solo `wave-retry` pass at 70G for hot
  windows; split-tooling only if a window busts even that (none
  expected: 43.9 GB fits solo).

- **U5 GATE + PARK** (2026-08-23): `GOLEAN_ALLOW_NO_DIFF=1
  GOLEAN_MEM_MAX=24G scripts/ci` — **RESULT: PASS** (rc 0) at
  adcb821a (log: artifacts/arc2-gate-u5.log, untracked; result
  restated here). Visible notes unchanged in kind from U4: the
  sanctioned no-diff hatch; the **comparator landmark OWED (scope)**
  note (Audit.lean's `import Audit.FastEval` in Challenge's trusted
  closure — flagged for the operator's MERGE step, the Arc-3/U4
  precedent; no designated statement changed on this lane). The
  1b2 discipline drove the park shape: the generated segment tree
  cannot be green mid-wave (unwired modules are exactly what the
  sweep catches), so it left the branch at adcb821a and lands in the
  SAME commit as its aggregator wiring at composition; during the
  park it exists as untracked, deterministically regenerable working
  files (byte-identical regeneration + lake content-hash no-op both
  verified live: a built segment re-checks in 0.18 s).

  **PARKED STATE (the wave, in flight):** manifest
  `records/u5-manifest.tsv` — 59/757 at this writing (45/45
  checkpoint groups + 14/712 segments; the committed 0/0 snapshot at
  adcb821a reflects the sources-absent gate tree, annotated here) —
  recomputed from oleans, never restated. The wave runs detached
  (setsid; survives session end) as 3-wide batched capped lake
  builds, continue-on-failure, failures logged to
  `records/u5-failures.txt` (none so far). Observed per-segment
  walls 97–406 s (mean ≈ 227 s over early observations); remaining
  ~700 segments ≈ 44 CPU-h ≈ 15–20 h wall at 3-wide.

  **RESUME (verbatim, from the worktree root — each step idempotent):**
  1. `python3 docs/campaign-arc2-probes/gen-u5-modules.py 1000 16`
     (only if the untracked tree is missing)
  2. `setsid nohup env WAVE_BATCH=3 WAVE_CAP=74G
     docs/campaign-arc2-probes/u5-orchestrate.sh wave >
     artifacts/arc2-scratch/u5-wave.log 2>&1 < /dev/null &`
  3. after the walk: `env RETRY_CAP=70G
     docs/campaign-arc2-probes/u5-orchestrate.sh wave-retry`
     (solo pass; only missing oleans build — hot windows like S0355
     need ~44 GB solo)
  4. composition: build `GoLeanProofs.Specs.TwinWitness` (48G cap;
     its endgame is the generated glue-lemma route — iterate its
     tactics if a spelling wrinkle surfaces; all heavy inputs are
     cached oleans), then in ONE commit: the generated tree + the
     aggregator import (`GoLeanProofs.Specs.TwinWitness` in
     `proofs/GoLeanProofs.lean`) + `Audit/FastEval.lean` pins for
     `twin_run_eq` / `twinCompletionWitness` (+ chain lemmas) with
     verbatim `#print axioms`, then the gate (now with the tree in
     the audited closure) + fresh axiom probe + hatch grep + this
     log's completion entry with manifest-derived numbers.
  **ARC 2 UNIT 5: STAGED ASSEMBLY IN FLIGHT — branch-complete park**
  at this tip; the witness spans dispatches by design.

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

## Checkpoint (U5 park, recomputed)

Branch `campaign-arc2` @ (tip after the park commit): 23 commits over
f64d9b21 (git log the authority), tree clean at each commit; the
working tree additionally carries the untracked regenerable module
tree + wave artifacts (documented above). U5 delta on the branch:
StateWire batch emitter (+its gate-check probe), TwinSegBase glue
(landed with the tree at composition — currently in the generator
only), gen-u5-modules.py + u5-orchestrate.sh + u5-manifest.sh,
probes fastseg-k1000/emitter-gatecheck, records fastseg2.out +
u5-manifest*.{tsv,txt}, memo §6.9, this log. Proved at the park
(beyond U4's pins, all re-verified this dispatch): 14 segment
theorems kernel-checked as build artifacts (their sources land at
composition). Measured: the §6.8 48G-lever refuted; marginal
0.182 s/step + 16.7 MB/step at the 350k boundary; per-window
variance 97–406 s / up to 43.9 GB. Central projection ~53–55 CPU-h
(GO, under the ~60 trigger). Nothing merged; no
GoCore/frontend/scripts edits; Arc-1 files verbatim; gate PASS at
the park tip.

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
- **[AGENT]** 2026-08-23 (U5, endgame de-risk — measured, not
  theorized): on the literal-heavy `twinRun` goal, BOTH
  `simp only [Bind.bind, Except.bind]` AND bare `rfl` were OOM-killed
  at 8G in ~20 s (records: artifacts probe endgame-shape, kill points
  kept) — the composition therefore goes through a GENERIC glue lemma
  over variables (`runProgramM_of_setup` in TwinSegBase, kit style):
  literals enter the endgame only as rewrite instances
  (twin_prelude_eq / twin_runConfig_eq / twin_load_eq), never as
  defeq comparands. Wrinkle appended for successors: the same
  bind-plumbing simp that is safe on all-variable goals detonates on
  reflected-literal goals.
- **[AGENT]** 2026-08-23 (U5): a canary "PASS" was retracted before it
  could mislead — the first S0355 attempt exited 0 in 5:47 with NO
  olean because `lake build | tail -2` reports the PIPE's rc, not
  lake's; caught by listing oleans, re-run unmasked (lake-polled.sh):
  the truth was OOM@38G, then PASS@44G/406 s. Lesson recorded: never
  read a wave job's outcome through a pipeline rc; the olean is the
  outcome.
- **[AGENT]** 2026-08-23 (U5): regenerating the module tree bumps all
  source mtimes, which sent the first mtime-based orchestrator loop
  into an infinite no-op walk on already-built groups (caught live,
  killed, ~10 min lost) — the orchestrator now walks the FULL ordered
  list exactly once per run and trusts lake's content-hash skip
  (~0.2 s per finished batch); the manifest's done criterion is olean
  EXISTENCE, with validity explicitly lake's domain, re-verified
  wholesale by the composition build + gate.

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

## Wave PARKED at user direction (2026-08-24)

[USER] 2026-08-24: 21 h of remaining solo-retry grind is too long to
block on for a job whose value is in question — combined with the
same-day [USER] giant-builds-smell guidance (campaign log), the wave
is PARKED, not completed. [AGENT] execution of the park:

- Orchestrator + in-flight S0124 build killed cleanly; p2 untouched.
- State kept: **549 of 712 segment oleans** built
  (`proofs/.lake/build/lib/lean/GoLeanProofs/Specs/TwinSegs/`,
  count from `ls ... | wc -l`); manifest + failure lists unchanged
  under `docs/campaign-arc2-probes/records/`. Nothing deleted.
- Resume recipe unchanged (this log, "resume recipe" section): the
  orchestrator is clobber-free (lake skips built oleans) — restarting
  `u5-orchestrate.sh` resumes exactly where parked, if ever wanted.
- **The primary route to CompletionWitness is now the Arc-4
  ROUND-REPLAY COROLLARY** (campaign log, retirement-condition entry
  2026-08-24): once layer C's round induction lands, the ∃-witness =
  ~100 applications of the round lemma at the recorded choice stream;
  the segment wave would then be deleted anyway. Parking merely moves
  the deletion earlier and skips the interim artifact. Fallback if
  the round-replay route hits a wall: resume this wave (reversible,
  above).

## Unit P2R chartered: the verified fast replay engine (2026-08-24)

[USER] 2026-08-24: p2 is another case for the verified-verifier
pattern — "It shouldn't take 30 hours to replay something in Lean.
Build a more performant abstraction then prove the theorem."
[AGENT] charter (worker dispatched to this lane):

1. **Measure FIRST** (clever-tricks: measurement referees): where do
   the hours go — compiled stepFn steps/sec on the replay workload,
   the TRUE step count (derive from the go-side record, never guess
   fuel), any pathological cost (heap behavior, harness re-scans).
2. **Extend FastEval to the replay path**: census which stepFn arms
   the probe_and_replicate replay exercises beyond the twin's;
   stepFast is arm-for-arm, so gaps should be enumerable and small.
3. **The transfer theorem**: a fast-run verdict transfers to the
   model via the γ-simulation composition (lineage: data refinement /
   certified computation — FastEval's existing story, widened).
4. **Wire it in**: tracereplay's machine stage runs the verified fast
   engine, with progress emission + periodic checkpoints (subsumes
   the earlier queued p2-replacement task) — no opaque runs, ever.
5. **Acceptance**: probe_and_replicate replays in minutes (hard
   ceiling ~1 h per the anti-grinding doctrine), verdict recorded
   durably, transfer theorem pinned in Audit.

If measurement shows the true step count makes even the fast engine
exceed the ceiling, STOP at that boundary and report — the next
abstraction rung (e.g. verified batched/big-step replay of whole
handler invocations, converging with arc-4's equation layer) is a
design decision, not a grind decision.

## P2R slice 1: MEASUREMENT (2026-08-24, this worker)

Workload: the p2 `probe_and_replicate` wire (10,018,785-byte
`wire.json`, 74 supported blocks; copied from the campaign worktree's
`artifacts/tracereplay/probe_and_replicate/` — read-only source, never
written). All runs: the arc-2 worktree's own `golean` binary
(GoLean sources clean at `005a9bc8`), `scripts/capped`, this box.

**Where the hours go — the slow engine is SUPERLINEAR per step.**
Fuel-ladder wall times, compiled `native-json-run` (command:
`/usr/bin/time -f … scripts/capped .lake/build/bin/golean
native-json-run --input artifacts/p2r/wire.json --function runTrace
--fuel F`):
  F=1 (parse+setup only)  0.14 s          peak 109 MB
  F=100,000               1.05 s          peak 107 MB
  F=1,000,000             107.15 s        peak 113 MB
  F=2,000,000             989.25 s        peak 128 MB
Marginal per-step cost ≈ 118 µs over [1e5,1e6] vs ≈ 882 µs over
[1e6,2e6] → cost(step s) ~ s^1.5, wall(F) ~ F^2.5. Memory is flat —
this is CPU in `Heap := List`'s O(cells) walks (and per-call image
costs), not RSS. The p2 >20 h DNF is fully explained: wall(1.5e7) ≈
15 h by this curve, wall(4e7) ≈ days.

**True step count (bounds, not a guess).** Prefix wires generated by
truncating the generated `main.go` to K blocks
(`artifacts/p2r/genprefix.py`) and bisecting minimal completing pool
fuel (`artifacts/p2r/bisect.py`; each probe's status line recorded):
  K=0   1,373 fuel   (init + newEnv + return; fast body = 112 steps)
  K=1   1,844
  K=2   367,739      (add-nodes(7) alone ≈ 366k steps)
  K=5   ∈ (1,375,312, 1,500,250]   (bisection STOPPED here — [AGENT]
        anti-grinding call: each near-boundary probe costs minutes at
        the degraded rate and the exact count arrives free from the
        fast engine's step counter; bounds recorded, grind declined)
With 69 heavier blocks beyond K=5 (stabilize/deliver waves over 7
nodes with growing logs), the full-trace count is plausibly 1.5e7–6e7
— ABOVE the slow engine's ceiling by orders of magnitude in wall
time. VERDICT: the charter's premise holds; the fast engine is the
only route. Probe records: `artifacts/p2r/` (untracked scratch;
numbers restated here per derivation-anchoring).

- **[AGENT]** 2026-08-24 (P2R): perf(1)/gdb attribution unavailable
  in the sandbox (perf_event_paranoid=4, no debugger) — attribution
  falls to the decisive differential instrument instead: the fast
  engine itself (sandbox rule: ask, don't hack around).

## P2R slice 2: transfer theorem + fastreplay driver; THE STRICTNESS
DISCOVERY (2026-08-24)

Landed (this slice's commit):
- `proofs/GoLeanProofs/FastEval/Transfer.lean` — `absState` (slow→
  fast conversion, untrusted, runtime-checked) + **`fastRun_transfer`**
  / **`fastRun_transfer_eqb`**: slow-setup .ok + γ-anchor + completed
  `iterF stepFast` run + fast readout ⇒ `runProgramM fuel program
  name args ch = .ok result`. GENERIC ∀-statement (certified
  computation; lineage: data refinement — FastEval's story widened
  from the twin's per-checkpoint kernel walk to one run-level
  theorem). Proof composes `iterF_ok`∘`stepFast_ok`,
  `runConfig_of_stepFnIter` + `runConfig_next_stop` (FuelMeasure),
  `loadManyF_ok`, and `ExecState.eqb_sound` (MachineEqb). Axioms
  `[propext, Classical.choice, Quot.sound]` — `Classical.choice`
  inherited from the already-pinned `stepFast_ok`, no new axiom;
  pinned in `Audit/FastEval.lean` (in-build gate).
- `proofs/GoLeanProofs/FastReplay.lean` + `[[lean_exe]] fastreplay`
  (proofs lakefile; module in the GoLeanProofs aggregator so the
  proofs gate checks it): the compiled driver — wire decode
  (`NativeToIR.decodeProgram`), slow `runProgramSetupM`, `absState` +
  `ExecState.eqb` γ-anchor check, CHUNKED `iterF stepFast` loop
  (chunks compose by `iterF_add`; exact-step landing by single-step
  re-walk on a refused chunk; total, no `partial`), `loadManyF`
  readout, CLI-schema observation JSON + per-chunk durable JSONL
  record (fsync'd-flush per line; the mid-job-failure principle).
  Smoke: wire-0 replays in 0.13 s, verdict ok, 112 body steps.

**Discovery (measured, decisive): FastEval's "lazy γF view" is
kernel-lazy but COMPILED-STRICT.** On the full wire the driver passed
setup+anchor then failed to finish its first 1e6-step chunk in >10
min (record `artifacts/p2r/rec-full-try1.jsonl` shows `anchor-ok`
then nothing; process at 99.9% CPU; killed). Cause: every def-side
pure-helper call at `γF σF` (`normalizeValueForTy` on every typed
store, `defaultValue` on every declaration, `valueEq` on every
comparison, `findFunctionIn? (γF σF).functions` on every call entry —
~45 def-side sites) STRICTLY materializes `γH`'s full heap dump,
O(cells) per call, in compiled code. The kernel walk never paid this
(projection laziness); the compiled path pays it per step — the fast
engine currently has the SLOW asymptotics when compiled.

**Design decision [AGENT]: the ctx refactor** (slice 3, decided). Introduce
`ctxF : ExecStateF → ExecState` := the γF image with `heap := []` —
O(1) to construct compiled (field copies) — and flip every def-side
`γF σF` helper argument to `ctxF σF`; sims patched via per-helper
TYPES-ONLY CONGRUENCE lemmas (`helper σ' = helper σ` when
`σ'.types = σ.types`; every def-site helper verified types-only by
reading: `valueEqFuel`, `normalizeValueForTyFuel`, `defaultValueFuel`,
`filterCandidateList`→`keyInKeys`, `mandatoryInList`, the method
family, the builders). The Frame library (WP arc) already provides
several (`defaultValue_congr`, `canonicalDynamicTy_congr`, the
`TypeCongr` method family); the rest land in a new
`FastEval/Congr.lean`. Projection sites (`(γF σF).functions`,
`(γF σF).types`) become direct `σF.functions`/`σF.types` (defeq).
Alternatives rejected: `@[implemented_by]` on `γF` (silent compiled/
proved divergence — a fail-open trust hole, never); memoization
(state changes every step); leaving it (measured: unusable).
LINEAGE: context/state splitting in data refinement.

## P2R slices 3-5: ctx refactor DONE; arm gaps closed; ACCEPTANCE MET
(2026-08-24)

**Slice 3 (the ctx refactor), landed.** `FastEval/Congr.lean` (new):
function-level static-table congruence for every def-side helper —
`structTagCompatible/normalizeValueForTy(Fuel)/valueEq(Fuel)/
valueHashability/checkKeyHashable/mapEntryIndex?/convertValueToTy(Fuel)/
typeAssertValue/buildStruct*/buildArray*/buildAppendBackingValue/
keyInKey*/filterCandidateList/mandatoryInList/mapIterMandatoryRemains`
— reusing the Frame library's layer (`defaultValue_congr`, TypeCongr's
method family) where it existed. `ctxF` + `_ctx` rewrite block in
`FastEval/Ops.lean`; ~45 def-side `γF σF` call sites flipped to
`ctxF σF` across Ops/Shared/Step/Values/Stores/Frames; sims patched by
one `rw`/`simp only [_ctx …] at h` after each affected `unfold` — the
existing proof scripts otherwise untouched. `indexTargetLocF`(+`_ok`)
moved Stores→Shared (Values needs it; import DAG). MEASURED EFFECT:
first 1e6-chunk DNF >10 min → 401,688 steps in 0.31 s on first retry
(>1M steps/s; the strictness diagnosis confirmed by the decisive
differential instrument).

**Slice 4 (arm gaps), landed.** First fast run fail-closed at
`applyStrictOp.bytesFromString` (step 401,688). Closed SIXTEEN
formerly-stubbed strict-op arms as per-arm helper defs + `_ok`
transports (`mul, shiftLeft, bitOr, bitXor, bitClear, bitNeg, neg,
floatLit, bytesFromString, addrOfDeref, indexAddr, capacityOf, runeAt,
runeSizeAt, runesFromString, stringFromRuneSlice`) — the helper-call
shape keeps `applyStrictOpF_ok`'s positional split stable (one
alternative = one bullet swap). Mirrors verbatim from `applyStrictOp`;
alloc arms transport by `allocF_loc/allocF_state` + injection; loop
arms follow the LOOPS rule (List spelling). No other gap surfaced —
in particular NO panic/recover machinery, no mapDelete/clearMap, no
channel ops execute on this trace (the panicking-head stub class stays
untouched). The wire's sync-ops are lock/unlock only (already
mirrored).

**Slice 5 (witness + wiring + acceptance).**
- `FastEval/TransferWitness.lean`: the non-vacuity witness —
  `fastRun_transfer_eqb` instantiated end-to-end on `gcdLowered`
  (projection-defined components, zero literal transcription; anchor
  eqb `#eval`-true first; exact 150-step body measured first; kernel
  `rfl` premises; builds in 0.68 s). Conclusion reads over
  `runProgramM` alone: `gcd(21,14) = 7`. Pinned in `Audit/FastEval.lean`
  beside `fastRun_transfer`/`_eqb` (all
  `[propext, Classical.choice, Quot.sound]` — Classical.choice
  inherited from the already-pinned `stepFast_ok`; NO new axiom).
- `tools/raftsubject/tracereplay.py`: ported the campaign worktree's
  durable-record/resume delta VERBATIM (the coordinator's reconcile
  point: this lane's copy previously lacked it; diff recorded here —
  base = campaign@records-era copy) and added `--engine fast`
  (default stays `slow`): the machine stage runs the `fastreplay` exe
  with a per-chunk durable record; the resume key now includes the
  engine so records never mix engines.

**ACCEPTANCE (charter item 5) — MET, measured:**
- Full probe_and_replicate fast replay: **11,995,825 steps,
  status ok, 26.6 s** (fastreplay direct; record
  `artifacts/p2r/rec-full-try3.jsonl`). TRUE STEP COUNT is therefore
  11,995,825 — the slow-engine curve extrapolates wall(1.2e7) ≈ 24 h,
  exactly explaining p2's >20 h DNF.
- Machine trace == go trace **byte-for-byte** (20,924 bytes; python
  diff of the decoded observation vs `go-trace.txt`).
- End-to-end `tracereplay.py --traces probe_and_replicate --engine
  fast --fuel 200000000 --keep --record
  artifacts/tracereplay/records-p2r.jsonl`: **74/74 blocks, OK-TIER
  57/57, RENDERED-TIER 17/17, MACHINE 1/1 AGREE, wall 24.62 s** — vs
  the killed >20 h p2 run. Ceiling (~1 h) beaten by ~100×.
- What the verdict rests on: compiled evaluation of `stepFast` etc.
  (same trust class as compiled `stepFn` — nothing weakened) + the
  PINNED `fastRun_transfer_eqb` carrying it to the
  `runProgramM`-equation. Full proofs build green (484 jobs incl. the
  in-build Audit gate); hatch grep over the new/changed FastEval
  files clean (zero sorry / native_decide / new axiom / partial in
  proof-facing code — the driver loop is total, fuel-measured).

- **[AGENT]** 2026-08-24 (P2R): `@[implemented_by]` on `γF` REJECTED
  as the performance fix (silent compiled/proved divergence = fail-open
  trust hole); the ctx refactor chosen — congruence-proved, visible.
- **[AGENT]** 2026-08-24 (P2R): the K=5 fuel bisection STOPPED
  mid-run (anti-grinding: minutes-per-probe for a number the fast
  engine's step counter delivers exactly and free — it did:
  11,995,825).
- **[AGENT]** 2026-08-24 (P2R): tracereplay.py edits judged NOT to
  owe `--diff`: the file is the raft-campaign harness, invoked by no
  differential script (`scripts/diff-coverage` grep: no tracereplay
  reference); the corpus differential cannot observe it. GoLean/
  frontend/interpreter untouched this unit (git status verified). The
  sanctioned fresh-lane `GOLEAN_ALLOW_NO_DIFF=1` hatch therefore
  still applies at the gate.
- **[AGENT]** 2026-08-24 (P2R): the ctx refactor invalidates the
  PARKED U5 segment oleans' input hashes (they rebuild against the new
  `stepFast` if the wave ever resumes — regeneration is the recorded
  resume path anyway; the round-replay corollary remains the primary
  route). Parked-wave working files left untouched and uncommitted,
  exactly as parked.
- **[AGENT]** 2026-08-24 (P2R): witness fuel/count (400/150) measured
  by `#eval` BEFORE any kernel ask (the #eval-before-decide rule);
  `maxRecDepth 100000` in TransferWitness.lean is a representation
  accommodation (kernel rfl over a 150-step run), tolerated-scaffold
  class, 0.68 s build.

- **P2R GATE** (2026-08-24): `GOLEAN_ALLOW_NO_DIFF=1
  GOLEAN_MEM_MAX=24G scripts/ci` — **RESULT: PASS** (rc 0; log
  artifacts/p2r-gate2.log, untracked; result restated here). Visible
  notes unchanged in kind from U5: the sanctioned no-diff hatch (this
  lane has no recorded differential; no runtime change owes one —
  GoLean/frontend/interpreter untouched, tracereplay.py is outside
  every differential script's path); the **comparator landmark OWED
  (scope)** note (files in Challenge's trusted closure changed —
  `Audit/FastEval.lean` gained the three P2R pins; flagged for the
  operator's MERGE step exactly as U5 flagged it; no designated
  statement changed on this lane).
- **[AGENT]** 2026-08-24 (P2R): the FIRST gate attempt FAILED on the
  1b2 sweep — the PARKED wave's untracked generated `TwinSegs`/
  `TwinCkpts`/`TwinSegBase/SegsAll/Witness` sources are exactly what
  the sweep catches (the park record predicted this; the U5 gate ran
  sources-absent). Handled per the park's own discipline: the
  generated tree MOVED (not deleted) to `artifacts/p2r-parked-wave/`
  — byte-identical regeneration via `gen-u5-modules.py` is the
  recorded resume path, and the ctx refactor had already invalidated
  the parked oleans' input hashes (noted above). Resume recipe step 1
  regenerates from scratch; nothing lost.

**UNIT P2R: BRANCH-COMPLETE at this tip.** All five charter items
done: measured (slice 1), extended arm-for-arm (slices 3-4), transfer
theorem + witness pinned (slices 2+5), wired in with progress +
durable records (slice 5), acceptance beaten ~100× (26.6 s vs the
~1 h ceiling; p2's >20 h DNF explained by the measured slow-engine
curve at the now-known true step count 11,995,825). Proposed next
charter (coordinator's call): run the WHOLE `deps/raft/testdata`
trace corpus through `--engine fast` — the full machine-tier
differential sweep p2 was a single point of is now an ~hour-scale
job; stub hits (if any) are enumerable arms under the same
fail-closed loop.

## Unit P2R-2: the full-corpus fast machine-tier sweep (2026-08-24)

[USER via coordinator]: proceed per the proposed charter — sweep
`deps/raft/testdata` through `--engine fast`, triage
AGREE/stub-hit/divergence, close cheap arms, divergences first.

**Inventory.** deps/raft @ 56e3200: 28 traces, 558 datadriven blocks;
supported prefix 354 (63.4%; stops are the DESIGNED unsupported
commands — tick-election/compact/send-snapshot/async-storage/
transfer-leadership/forget-leader/report-unreachable/read-only —
tracereplay's documented vocabulary, not machine gaps). One trace
(async_storage_writes) has prefix 0 → go-side only by design.

**Sweep 1** (`tracereplay.py --engine fast --fuel 2e8 --keep --record
artifacts/tracereplay/records-p2r2.jsonl`): **wall 149.3 s, peak
217 MB** for the whole corpus. Result: 19/27 machine AGREE, **zero
divergences**, and ALL 8 failures the SAME fail-closed stub —
`applyStmtOpCore.mapDelete` (every confchange trace + the learner
trace: removing a peer deletes from the Progress/votes maps). OK-tier
206/206, rendered-tier 148/148 (go-vs-upstream channels — all green).

**Arm closure (the one gap), U-discipline.**
- `applyStmtOpCoreF` mapDelete arm mirrored verbatim (mapEntriesF +
  storeLocF + ctx helpers) + private `core_mapDelete_ok`; the
  `cases op` dispatch (named arm, no positional fragility here).
- `contAfterStmtOpF` re-defined as FULL DELEGATION:
  `contAfterStmtOp (ctxF σF)` — the original is types-only (key
  comparison; prune walks are heap-free), so the slow implementation
  runs verbatim at the O(1) context image. Sim collapses to one
  `contAfterStmtOp_ctx` rewrite. This closes BOTH cont stubs
  (mapDelete + clearMap) and deletes the stub class from that def.
- Congr additions: `removeKeyList_congr`, `pruneIterFramesKey_congr`
  (plain Cont induction + simp_all), `contAfterStmtOp_congr`;
  `contAfterStmtOp_ctx` in the Ops block. Zero sorry; full proofs
  build green (484 jobs) + fastreplay rebuilt.

**Sweep 2 (definitive, fresh record
`artifacts/tracereplay/records-p2r2-final.jsonl`): MACHINE 27/27
AGREE byte-for-byte; OK-tier 206/206; rendered 148/148; wall 237.2 s,
peak 216 MB.** Total fast steps across the corpus: **37,703,350**
(per-trace table derivable from the record file's machine-raw stages;
largest probe_and_replicate 11,995,825). The machine tier that p2
could not finish ONE trace of in >20 h now covers the ENTIRE corpus
in under 4 minutes.

**Triage summary: divergences 0; stub-hits 1 arm (closed); AGREE
27/27.** No BUG entry, no corpus case owed — the sweep's value is the
COVERAGE claim: every supported-prefix block of every upstream trace
replays byte-identically through the verified fast engine, with the
verdict transferable to `runProgramM` by the pinned theorem.

- **[AGENT]** 2026-08-24 (P2R-2): resume NOT used for the 8 retries
  (a resumed record would have replayed the recorded FAILURE finals);
  fresh record files per phase, engine now part of the resume key.
- **[AGENT]** 2026-08-24 (P2R-2): residual performance observation,
  recorded not investigated (anti-grinding; no ceiling threatened):
  per-trace fast-step rate varies ~30× (replicate_pause 1.9M steps in
  0.8 s vs confchange_v2_add_double_auto 2.7M in 27 s) — plausibly
  value-copy-dominated arms (large struct/array copies per store) or
  box contention with the concurrent arc-4 worker; a follow-on
  measurement unit could profile per-arm if corpus growth makes it
  matter. WHAT THIS TAUGHT US: the trie fixed the heap-op asymptote;
  the next constant lives in VALUE representation, not the heap.
- **[AGENT]** 2026-08-24 (P2R-2): the unsupported-command prefix
  boundary (63.4%) is the harness's DESIGNED vocabulary, not fast-
  engine gaps — widening it (tick-election jitter, compact,
  async-storage) is membership-lane / replayenv work, out of this
  unit's scope; noted for the coordinator's frontier ledger.

- **P2R-2 GATE** (2026-08-24): `GOLEAN_ALLOW_NO_DIFF=1
  GOLEAN_MEM_MAX=24G scripts/ci` — **RESULT: PASS** (rc 0; log
  artifacts/p2r2-gate.log, untracked; result restated here). Visible
  notes unchanged in kind: sanctioned no-diff hatch (proofs+docs+
  campaign-harness only; GoLean runtime untouched); comparator
  landmark OWED (scope) note stands for the operator's merge step.
  **UNIT P2R-2: BRANCH-COMPLETE at this tip.** Proposed next charter
  (coordinator's call): either (a) the replay-vocabulary frontier —
  widen tracereplay's supported commands (compact/snapshot rows first;
  the fast engine makes their cost trivial), or (b) the value-
  representation measurement unit from the 30× rate-variance
  observation, if corpus scale grows.
