# Codex packet C — CONTINUATIONS: `Cont := List Frame`

STATUS: **EXECUTING — lane `core/continuations-0929` (worktree `.claude/worktrees/continuations`), [AGENT packet C worker], an
Opus 5.5 subagent, forked from `main` @ `883ebc36` (P landed, train r55). G-C3 PASSED ([USER] Mike 2026-09-29 «Agree with 1-4», relayed;
ledger `docs/2026-08-31_qrow-rulings.md` «G-C3 (continuations) passed — RULED (2026-09-29)»; design `docs/2026-09-29_gc3-continuations-design.md`,
whose §3 is this brief's acceptance and whose §4 stop rule binds). Refreshed 2026-09-29 by the lane (the design note's two stale-detail
findings corrected: `frame`'s field order after P; the helpers P deleted).** [AGENT] planning writer 2026-09-24. Ruling: the packaging of 2026-09-24 («C continuations
`Cont := List Frame`», ledger), executed as an Opus 5.5 subagent dispatched by the coordinator ([USER] 2026-09-27). Executes charter row 4;
plan `docs/2026-09-24_window-plan.md` row 4. Provenance: **[AGENT packet C worker]**.
**Ambiguity policy: if two readings of this brief differ materially, STOP, write both in the report, do not choose.**

## 1. Purpose
Replace the 33-constructor `inductive Cont` (`GoLean/GoCore/Machine.lean:3353` at `883ebc36`: `stop` + 32 frames; `probeK` SURVIVES — E6e is off the critical path, [USER] 2026-09-27;
after P, `frame targets tenv results defers k fid` — the `wrapper` field is gone and the callee `fid : FuncId` comes AFTER `k`) by `abbrev Cont := List Frame`, where `Frame` has one constructor per
`Cont` constructor except `stop`, fields verbatim MINUS `k : Cont` (not always trailing: `frame`'s `fid` follows it); every constructor NAME survives as an `@[match_pattern] abbrev`
(`Cont.stop : Cont := []`; `Cont.seq rest env k : Cont := Frame.seq rest env :: k`; …) so every existing pattern and term elaborates unchanged.
ZERO behaviour change. NOT a context-fill law: `k ++ K` exists definitionally; no commutation theorem is claimed (proposal §2 (c) — the
customer's `recover`-vs-helper side condition stays theirs); do not add one.

## 2. Setup
(As executed: worktree `.claude/worktrees/continuations`, branch `core/continuations-0929` off `main` @ `883ebc36`; the report is the handoff
`docs/2026-09-29_continuations-handoff.md`; commit style `[TRUST-SURFACE #1: GoLean/GoCore; AGENT packet C worker, lane core/continuations-0929]`.)
`git -C /home/dev/projects/golean worktree add .claude/worktrees/codex-packet-c -b codex/packet-c-continuations-<date> <MAIN TIP after P — refreshed>`.
Scratch under the worktree's `.tmp/` only; every build/gate through `scripts/capped`; the box-wide lock for any full build or gate
(`mkdir /home/dev/projects/golean/artifacts/build-lock.d` + `owner` file; wait-retry 120 s; never take over; release under a trap); one writer.

## 3. Inputs (REFRESHED at launch)
`883ebc36`; `GoLean/GoCore/Machine.lean` (`Cont` :3353, `Cont.tail` :3680, `Cont.withTail` :3694, `Cont.sizeOf_tail_lt`/`withTail_tail`/
`tail_withTail` :3730–3737, `Cont.class` :3755, `Cont.rebuild` :3778 + `rebuild_descend`/`rebuild_act`/`rebuild_stop` :3789–3801,
`seqCont` :3837, `pushDefer` :3862, `panicPassthrough` :3873, `recoverAtDeferred` :3888 (G-P S2's replacement of the deleted
`recoverThroughWrappers`; `Cont.recoverTransparent` was deleted with it), `recoverResult` :3906, `signalStep` :4203, `seqConsumption` :5483, `Step` :5612),
`StepFn.lean` (`stepFn` :329, `stepFrameExit` :156), `MachineEqb.lean` (`Cont.eqbF` :424 — one fuel unit per frame, preserved exactly, design D4),
`StateWf.lean` (`Cont.locSup` :485, `Cont.ownSup` :584, `rebuild_locSup` :603), `StateWf.lean`, `MachineSound.lean`, `UnseqSound.lean`, `SyntaxEqb.lean`, `MachineEqb.lean`,
`StateEqb.lean`, `AdmissionIndices.lean`, `Multi.lean`, `MultiSound.lean`, `MultiWfSound.lean`, `NPDRF.lean`, `AbortObservation.lean`,
`Prefix.lean`, `ExecutionStatement.lean`, `BridgeSet.lean`; `GoLean/{CLI,ChoiceTrace,EnumDedup}.lean` and `Tests/*.lean` wherever they match
on `Cont` (`Tests/GoCoreContract.lean`'s `bareFrame`/`panicFrame` and its `Cont.rebuild_*` uses); `scripts/choice-trace-corpus`,
`scripts/check-frontend-pins`; charter row 4; proposal §2 (c).

## 4. Deliverables
1. `inductive Frame` + `abbrev Cont := List Frame` + the `@[match_pattern] abbrev`s under the OLD names with the CURRENT argument order (`k` last
   everywhere EXCEPT `frame`: `frame targets tenv results defers k fid`; design D3); `k`-only frames (`breakableK`, `boolK`, `panicArgK`, `probeK`)
   become nullary `Frame` constructors; `.stop ↦ []`.
   `Cont.tail` = `List.tail?`-shaped, `Cont.withTail` = tail replacement, `Cont.rebuild` = list recursion; `Cont.sizeOf_tail_lt`, `withTail_tail`,
   `tail_withTail`, `rebuild_descend`, `rebuild_act`, `rebuild_stop` re-proved as LIST lemmas under the SAME names and statements (modulo the abbrev).
2. `stepFn`, `Step`, `StateWf`, `MachineSound`, `UnseqSound`, `SyntaxEqb`/`MachineEqb`/`StateEqb`, `AdmissionIndices`, the pool modules, `NPDRF`,
   `AbortObservation`, the CLI/tracer modules and the tests RE-ELABORATED: patterns unchanged wherever the abbrevs suffice; where a `match`
   needs the list form, the rewrite is LOCAL and every such site is listed in the report. NO rule added, removed or reordered; `seqConsumption`
   identical up to the abbrevs; the `Step` rule count unchanged (record it before and after).
3. `pushDefer`, `seqCont`, `stepFrameExit`'s frame handling, `panicPassthrough`, `recoverAtDeferred`, `recoverResult` as list functions, each with a lemma stating
   the OLD equation under a new name (`pushDefer_eq` «map at the first call frame», `seqCont_eq`, `recoverResult_eq` (kept), `panicPassthrough_eq`, …); `Cont.rebuild_*`,
   `withTail_tail`, `tail_withTail`, `rebuild_locSup` by list induction under the same names and statements; the new lemmas are ADDED to
   `check-core-audit`'s required list (nothing removed; design D6). The request-7 unwinding equations are NOT here — packet D, after C4 (G-C3 decision 2). These lemmas are the «`pushDefer`, `seqCont`, frame exit, `Cont.rebuild_*` as list laws» the charter row 4 owes.
4. `BridgeSet.lean` re-pinned: the abbrev keeps most pins byte-identical — report WHICH pins changed and why; `docs/changelog/61958f2e-WINDOW.md`:
   the C3 row FILLED (`inductive Cont` → `List Frame`; the `Frame` constructor list; the `k`-field removal; what a downstream `cases k` sees;
   `Control.Agrees`/`pushDefer`/`Cont.rebuild_*` become list induction — `[inf]`).

## 5. Acceptance — ZERO behaviour change: the gate + two byte-identity checks (capped; locked; EXIT codes recorded)
0. The design note's §3 is binding acceptance alongside this section; its §4 stop rule binds: elaboration measured (profiler + wall time per
   hot module) before and after; any module slower than 1.5×, or any NEW or RAISED `maxHeartbeats`, is reported and the lane STOPS.
   Fuel and hashing behaviour preserved exactly (D4). No `Config := Mode × Cont`, no `fill` (G-C3 decision 1).
1. `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` green with the baseline UNCHANGED — NO re-pin of any `baselines/` file; a moved row =
   STOP and report. `scripts/capped scripts/check-core-audit` PASS; the escape-hatch preflight clean. (The fast steps' `certificate provenance`
   STALE red is the train's 5a business, not yours.)
2. The whole-corpus CHOICE TRACE byte-identical: build the PRE-C3 binary from your fork base in a second worktree (`git worktree add .tmp/pre-c3
   <base>`; `GOLEAN_MEM_MAX=48G scripts/capped lake build golean` there) and the post-C3 binary here; run `scripts/choice-trace-corpus --dump
   --out .tmp/ct/pre --golean <pre-bin>` and `… --out .tmp/ct/post --golean <post-bin>` (same `--jobs`, `--fuel`, `--streams`); `diff -r` the
   `dump-*.tsv` and `results-*.tsv` files → EMPTY (exclude ONLY header lines carrying a timestamp or commit, each named in the report).
3. The TWIN byte-identical: `scripts/check-frontend-pins` green with `baselines/pins/` untouched (the raft twin's lowering pin), and the twin's
   and `multipkg/mini-raft-twin`'s differential rows unchanged in (1). (C3 touches no frontend file, so the WIRES are unchanged by construction —
   state that, and still run the check.)
4. `python3 tools/reconcile-records` findings reported. Evidence `docs/evidence/<date>_packet-c/` (README, gate tails, the two `diff -r`
   commands with their empty output, ≤ 256 KiB).

## 6. Boundaries — what NOT to do
The core only: `GoLean/GoCore/**`, plus the re-elaboration of `GoLean/{CLI,ChoiceTrace,EnumDedup}.lean` and `Tests/*.lean` where they match on
`Cont`. NO frontend, decoder or wire change; NO new pick, choice site or `PickRecord`; NO rule change; NO context-fill law (no `fill` theorem, no
commutation claim); NO behaviour change of any definition (a proof that cannot be re-established without one → STOP and report); no
`sorry`/`axiom`/`native_decide`/`partial`/`admit` in the core; no gate weakening; no `baselines/` edit; no `/tmp`; no uncapped build; never
take over a lock; never kill by pattern; never edit while a gate reads the tree; no push, merge, tag or rebase onto a moved `main`; no root
`HANDOFF.md` edit.

## 7. Report — `docs/<date>_packet-C-report.md` (≤ 60 lines)
Tip; the `Frame` constructor list; every local pattern rewrite (file:line); pins changed vs identical; the three acceptance results with EXIT
codes and the excluded header lines named; every `[AGENT Codex, packet C] INTERPRETED: …` (flagged, not decided); anything unprovable with the
goal verbatim. End state: branch complete, clean, nothing merged or pushed. Commit: `[AGENT Codex, packet C] Cont := List Frame; zero behaviour change; BridgeSet re-pinned`.
