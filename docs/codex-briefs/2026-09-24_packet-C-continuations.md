# Codex packet C — CONTINUATIONS: `Cont := List Frame`

STATUS: **DRAFT — launchable in its window slot after P (charter row 3) lands on `main` AND the [USER] has passed the G-C3 design gate (a
HARD STOP, `docs/2026-09-03_design-hygiene-arc.md`); the coordinator REFRESHES §3 (the input commit, the constructor count after E6e and P,
the line numbers) and deletes this sentence.** [AGENT] planning writer 2026-09-24. Ruling: the packaging of 2026-09-24 («C continuations
`Cont := List Frame`», ledger). Executes charter row 4; plan `docs/2026-09-24_window-plan.md` row 4. Provenance: **[AGENT Codex, packet C]**.
Launched by the [USER].
**Ambiguity policy: if two readings of this brief differ materially, STOP, write both in the report, do not choose.**

## 1. Purpose
Replace the 33-constructor `inductive Cont` (`GoLean/GoCore/Machine.lean:3253` at `3fb4a0d1`; one fewer after E6e's `probeK` retirement and
possibly a `frame` field fewer after P — the REFRESHED count is in §3) by `abbrev Cont := List Frame`, where `Frame` has one constructor per
`Cont` constructor except `stop`, fields verbatim MINUS the trailing `k : Cont`; every constructor NAME survives as an `@[match_pattern] abbrev`
(`Cont.stop : Cont := []`; `Cont.seq rest env k : Cont := Frame.seq rest env :: k`; …) so every existing pattern and term elaborates unchanged.
ZERO behaviour change. NOT a context-fill law: `k ++ K` exists definitionally; no commutation theorem is claimed (proposal §2 (c) — the
customer's `recover`-vs-helper side condition stays theirs); do not add one.

## 2. Setup
`git -C /home/dev/projects/golean worktree add .claude/worktrees/codex-packet-c -b codex/packet-c-continuations-<date> <MAIN TIP after P — refreshed>`.
Scratch under the worktree's `.tmp/` only; every build/gate through `scripts/capped`; the box-wide lock for any full build or gate
(`mkdir /home/dev/projects/golean/artifacts/build-lock.d` + `owner` file; wait-retry 120 s; never take over; release under a trap); one writer.

## 3. Inputs (REFRESHED at launch)
`<commit>`; `GoLean/GoCore/Machine.lean` (`Cont` :3253, `Cont.tail` :3553, `Cont.withTail` :3567, `Cont.sizeOf_tail_lt`/`withTail_tail`/
`tail_withTail` :3603–3610, `Cont.rebuild` :3651 + `rebuild_descend`/`rebuild_act`/`rebuild_stop` :3662–3674, `Cont.recoverTransparent` :3724,
`seqCont` :3682, `pushDefer` :3707, `recoverThroughWrappers` :3739, `recoverResult` :3763, `signalStep` :3947, `seqConsumption` :5190, `Step` :5315),
`StepFn.lean` (`stepFn` :326, `stepFrameExit` :153), `StateWf.lean`, `MachineSound.lean`, `UnseqSound.lean`, `SyntaxEqb.lean`, `MachineEqb.lean`,
`StateEqb.lean`, `AdmissionIndices.lean`, `Multi.lean`, `MultiSound.lean`, `MultiWfSound.lean`, `NPDRF.lean`, `AbortObservation.lean`,
`Prefix.lean`, `ExecutionStatement.lean`, `BridgeSet.lean`; `GoLean/{CLI,ChoiceTrace,EnumDedup}.lean` and `Tests/*.lean` wherever they match
on `Cont` (`Tests/GoCoreContract.lean`'s `bareFrame`/`panicFrame` and its `Cont.rebuild_*` uses); `scripts/choice-trace-corpus`,
`scripts/check-frontend-pins`; charter row 4; proposal §2 (c).

## 4. Deliverables
1. `inductive Frame` + `abbrev Cont := List Frame` + the `@[match_pattern] abbrev`s under the OLD names with the OLD argument order (`k` last).
   `Cont.tail` = `List.tail?`-shaped, `Cont.withTail` = tail replacement, `Cont.rebuild` = list recursion; `Cont.sizeOf_tail_lt`, `withTail_tail`,
   `tail_withTail`, `rebuild_descend`, `rebuild_act`, `rebuild_stop` re-proved as LIST lemmas under the SAME names and statements (modulo the abbrev).
2. `stepFn`, `Step`, `StateWf`, `MachineSound`, `UnseqSound`, `SyntaxEqb`/`MachineEqb`/`StateEqb`, `AdmissionIndices`, the pool modules, `NPDRF`,
   `AbortObservation`, the CLI/tracer modules and the tests RE-ELABORATED: patterns unchanged wherever the abbrevs suffice; where a `match`
   needs the list form, the rewrite is LOCAL and every such site is listed in the report. NO rule added, removed or reordered; `seqConsumption`
   identical up to the abbrevs; the `Step` rule count unchanged (record it before and after).
3. `pushDefer`, `seqCont`, `stepFrameExit`'s frame handling, `recoverThroughWrappers`, `recoverResult` as list functions, each with a lemma stating
   the OLD equation under a new name (`pushDefer_eq` «map at the first call frame», `seqCont_eq`, `recoverResult_eq`, …); `Cont.rebuild_*` by list
   induction. These lemmas are the «`pushDefer`, `seqCont`, frame exit, `Cont.rebuild_*` as list laws» the charter row 4 owes.
4. `BridgeSet.lean` re-pinned: the abbrev keeps most pins byte-identical — report WHICH pins changed and why; `docs/changelog/61958f2e-WINDOW.md`:
   the C3 row FILLED (`inductive Cont` → `List Frame`; the `Frame` constructor list; the `k`-field removal; what a downstream `cases k` sees;
   `Control.Agrees`/`pushDefer`/`Cont.rebuild_*` become list induction — `[inf]`).

## 5. Acceptance — ZERO behaviour change: the gate + two byte-identity checks (capped; locked; EXIT codes recorded)
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
