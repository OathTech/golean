# Packet C — `Cont := List Frame` (window row 4): handoff and report

STATUS: **BRANCH-COMPLETE, audit ask pending — nothing merged or pushed.** [AGENT packet C worker], lane
`core/continuations-0929` (worktree `.claude/worktrees/continuations`), forked from `main` @ `883ebc36`. Authority:
G-C3 PASSED, [USER] Mike 2026-09-29 «Agree with 1-4», relayed (ledger «G-C3 (continuations) passed — RULED
(2026-09-29)»; design `docs/2026-09-29_gc3-continuations-design.md` §5). This file is also the brief's §7 report
(`docs/codex-briefs/2026-09-24_packet-C-continuations.md`; [AGENT] reading: the lane brief names this handoff as the
report, so no separate `docs/<date>_packet-C-report.md` is written). Evidence: `docs/evidence/2026-09-30_packet-c/`.

## Commits
`121d8501` design note (cherry-pick of `060ad4e4`); `3ff30fa6` rulings record + brief refresh (records); `3be9a643`
the runtime change (TRUST-SURFACE #1); the records commit on top (changelog row, evidence, this handoff, the design
note / arc doc / reasoning-surface plan amendment notes).

## The shape as landed (decisions 1 and 3, D3–D6)
- `inductive Frame` — 32 constructors, the pre-C3 frames' names and fields verbatim MINUS `k`: `seq loop frame
  deferCalleeK deferArgsK breakableK labelK callValCalleeK callValArgsK strictK andK orK boolK ifK whileK callArgsK
  stmtOpK mapRangeK mapIterK panicArgK panicResumeK chanStK selectOpsK tgtOpK rhsK storeK goCalleeK goArgsK syncStK
  atomicStK probeK unseqK` (`breakableK`, `boolK`, `panicArgK`, `probeK` nullary; `frame targets tenv results
  defers fid`). `abbrev Cont := List Frame`. The 33 old names are `@[match_pattern] abbrev`s in the CURRENT argument
  order (`Cont.frame t te r ds k fid := Frame.frame t te r ds fid :: k`), `Cont.stop := []`.
- `Cont.tail`/`withTail`/`class` are list functions (`Frame.class` carries the exhaustive table, no default);
  `Cont.rebuild` is structural list recursion. Every other definition (`stepFn`, `stepFrameExit`, `Step`,
  `signalStep`, `seqConsumption`, `pushDefer`, `seqCont`, `panicPassthrough`, `recoverAtDeferred`, `recoverResult`,
  `Cont.locSup`, `Cont.eqbF` — one fuel unit per frame, D4 — and `EnumDedup.contDepth`) is textually unchanged.
- Not done, as ruled: no `Config` reshape, no `fill`/context-fill law (decision 1); request-7 unwinding equations
  left to packet D (decision 2).
- List laws ADDED and pinned (D6; BridgeSet rows 90–107; required list 110 → 144): `Cont.rebuild_cons`/`_nil`,
  `Cont.tail_/withTail_/class_ nil/cons`, `pushDefer_nil`/`_frame`/`_glue`/`_other`, `pushDefer_eq` («map at the
  first call frame» under a statement-glue prefix) + converse `pushDefer_some`, `seqCont_seq`/`_seq_ne`/`seqCont_eq`,
  `panicPassthrough_nil`/`panicPassthrough_eq`, `recoverAtDeferred_nil`, `recoverResult_nil`,
  `recoverResult_cons_glue`, `stepFn_next_frame`, `stepFrameExit_nil`, `Cont.locSup_cons`/`_nil`,
  `Cont.ownSup_cons`. Re-proved AS STATED under the same names: `Cont.sizeOf_tail_lt`, `withTail_tail`,
  `tail_withTail`, `rebuild_descend`/`_act`/`_stop`/`_isSome`/`_getD_glue`, `rebuild_locSup`; `recoverResult_eq` kept.
- BridgeSet (D5): rows 1–89 BYTE-IDENTICAL, none re-pinned; rows 90–107 added (RE-PIN 5).

## Local proof rewrites (no definition or statement changed)
- `cases k` → `cases_cont k` (a new tactic macro in `Machine.lean`: list `cases`, then `cases` on the head frame):
  `Machine.lean` `recoverAtDeferred_none`, `recoverResult_glue`; `StateWf.lean` `Cont.locSup_withTail`,
  `signalStep_locSup`, `seqCont_locSup`, `recoverAtDeferred_locSup` (+ `rename_i` order), `recoverResult_locSup`
  (`rename_i` order); `MachineSound.lean` the two `panicUnwind` arms (`step_complete`, `step_complete_any_wf_aux`),
  `entryCallSite?_panicking`, `entryCallSite?_of_signalStep`; `UnseqSound.lean` `unseq_panic_drops_frame`
  (`Frame.class` beside `Cont.class` in the simp set).
- `MachineEqb.lean` `Cont.eqbF_sound`: split `[]`/`f :: k` on both sides then the head frames; the arm headers
  lose their `k1`/`k2` binders (tags `x.x` still match by suffix).
- `MachineSound.lean` `stepFn_sound`, `stepFn_consumption_none`: `case140`/`case155` (the `.retV`/`.next`
  catch-all refusals) closed directly before the generic combinator — see «Elaboration». `fun_cases stepFn`: 162
  cases at both commits, same tags on the same patterns; `Step`: 128 rules, same list in order.

## Acceptance (evidence README has the commands and outputs)
1. `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at `3be9a643`: EXIT 1 on exactly the 5a pair —
   certificate provenance (STALE, changed dependency files) + the one drift line `imported-goose/channel/google-search
   PASS → FAIL`; `cases=3791 pass=3553 fail=238`; baseline UNCHANGED (3554 / 237), no `baselines/` edit. Core totality
   audit PASS (144 required), check-mem-callsites ok, unseq scheduler/wire ok, eval tests 298 ok, frontend pins ok.
   Reconciler (report-only): C9 HIGH = the same certificate staleness; C13 MEDIUM = pre-existing doc Go-version sites.
2. Whole-corpus choice trace (pre binary at `883ebc36` vs post): all six `dump-*.tsv` byte-identical (26417 rows);
   `results-*.tsv` identical except `results-0.tsv`'s one embedded `--out` path (identical after normalizing the
   `.tmp/ct/<side>/` path — the ONLY exclusion). Plus: 3755 wires × `native-json-run` default stream, stdout + exit
   identical for all; runtime 85.5 s → 86.4 s (1.01×).
3. Twin: no frontend/decoder/`baselines/` file touched (the wire is unchanged by construction; the exported wire
   directories of the two trace runs are identical); `check-frontend-pins` ok.
4. Every coherence theorem and every packet A/B statement proved AS STATED; no `_stmt` changed; totality: no
   `sorry`/axiom/`native_decide`/`partial` added (escape-hatch preflight ok, core audit classical trio only).

## Elaboration (decision 4, the stop rule) — NOT triggered
A/B interleaved, same box and load, wall s pre → post: Machine 4.23 → 4.09, StepFn 1.03 → 1.04, MachineSound 67.5 →
72.0 (1.07×, the maximum), StateWf 17.5 → 17.4, MachineEqb 4.74 → 4.85, StepErrors 229 → 218, BridgeSet 0.86 → 0.89;
full `lake build golean` 468 s → 384 s (load noise). `maxHeartbeats`/`maxRecDepth`: the same 59 settings, none new or
raised. DISCLOSED: the first, non-interleaved runs (taken under box load 5 → 16 from other projects) showed up to
2.8×; they were not comparable and are superseded by the interleaved runs (all kept in the evidence). Two real costs
were found and removed by proof-local edits before the binding measurement: `stepFn_sound`/`stepFn_consumption_none`
had gone past the DEFAULT heartbeat budget (the generic `simp_all [stepFn]` took ~9 s on the `.retV` catch-all's 26
list-shaped overlap hypotheses, 0.5 s before) — fixed by closing `case140`/`case155` directly, NOT by any heartbeat
setting; and the new `stepFn_next_frame`'s `simp only [stepFn]` (+1.7 s in StepFn, 2.8×) — now `rfl`.

## Posed / open
- Nothing posed: no deviation from the four decisions. [AGENT] routine choices inside D3/D6, flagged for the audit:
  the `cases_cont` tactic in the core; the list laws' exact names beyond the design's four (`pushDefer_some`,
  `seqCont_seq_ne`, `recoverResult_cons_glue`, `stepFn_next_frame`, …); proving via `case140`/`case155` positional tags.
- The adversarial audit ask is the coordinator's to pose; the 5a certification refresh is the train's.
