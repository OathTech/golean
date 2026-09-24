# Codex packet A — the CONTRACT (stable-set file, execution statement, changelog draft)

STATUS: **LAUNCHABLE NOW** against `main` @ `3fb4a0d1`. [AGENT] planning writer 2026-09-24, under «The window charter (rev. 2) and the
Codex packaging — RULED (2026-09-24)» (`docs/2026-08-31_qrow-rulings.md`; decision 2: «the stable-set file + statement note + changelog
draft as Codex packet A»). Executes charter row 0 (`docs/2026-09-23_batched-window-charter.md`); plan `docs/2026-09-24_window-plan.md` row 0b.
Provenance on every logged choice: **[AGENT Codex, packet A]**. Launched by the [USER].
**Ambiguity policy: if two readings of this brief differ materially, STOP, write both in the report, do not choose.**

## 1. Purpose
Make the consumed interface CHECKABLE before any breaking change lands: (i) a Lean file whose BUILD FAILS when a pinned statement drifts;
(ii) charter §2's execution statement as Lean `Prop` definitions that ELABORATE — statements only, packet B proves them after the label
reshape; (iii) the changelog draft from the customer's pin `61958f2e` to `main`. No semantics change, no proof, no runtime change, no decision.

## 2. Setup (exact)
`git -C /home/dev/projects/golean worktree add .claude/worktrees/codex-packet-a -b codex/packet-a-contract-0924 3fb4a0d1`, then work in
that worktree; scratch ONLY under its `.tmp/` (gitignored), never `/tmp`. Every `lake`/`lean`/gate run through `scripts/capped`
(`docs/operational-lessons.md`). BOX-WIDE LOCK for any full build or gate: `mkdir /home/dev/projects/golean/artifacts/build-lock.d` (atomic,
at the PRIMARY root) + an `owner` file inside (`codex-packet-a <pid> <ISO date>`); on failure wait 120 s and retry — NEVER take over; release
under a trap. Explicit-target builds at `GOLEAN_MEM_MAX=48G` skip the lock, not the cap. Judge builds by the captured EXIT code only.

## 3. Inputs (all at `3fb4a0d1`; read, do not edit)
`GoLean/GoCore/{StepFn,Machine,MachineSound,Trace,ProgramTrace,Multi,MultiSound,State,Ops,Syntax,Value,StateWf}.lean`; `GoLean.lean`;
`lakefile.toml`; `scripts/ci`, `scripts/check-core-audit`, `tools/core-audit.py`, `tools/ci_libraries.py`, `scripts/ci-libraries.json`;
`Tests/GoCoreContract.lean` (precedent); charter §2–§3; `docs/2026-09-23_response-from-logic-team.md` §2, §3, §6; `docs/2026-09-23_proposal-to-logic-team.md`
§1 (changelog table format), §4-i (the stable set); `docs/2026-09-23_batched-window-charter-review.md` F2 + `docs/evidence/2026-09-23_batched-window-review/FuelBoundary.lean`;
the pin `61958f2e` via `git show 61958f2e:<path>`; `docs/evidence/README.md`.

## 4. Deliverable (i) — `GoLean/GoCore/BridgeSet.lean`
- `namespace GoLean.GoCore.BridgeSet`; `import GoLean.GoCore.ProgramTrace`, `import GoLean.GoCore.MultiSound`.
- ENROLMENT = two `import` lines in `GoLean.lean` (`GoLean.GoCore.BridgeSet`, `GoLean.GoCore.ExecutionStatement`) + a comment. That IS
  default-build membership: `[[lean_lib]] name = "GoLean"` has no `globs`, so the library is `GoLean.lean`'s import closure; `Main.lean`
  imports `GoLean`; `scripts/ci`'s `core` step (`scripts/ci-libraries.json`: libraries `["GoLean"]`, executables `["golean"]`; `tools/ci_libraries.py`
  builds `GoLean:leanArts` + `golean`) compiles it. NO lakefile edit. `scripts/check-core-audit` imports EVERY on-disk module under `GoLean/`
  and `GoLean/GoCore/` (two-way closure), so both new files are audited; the escape-hatch preflight (`scripts/ci` step 1) scans them.
- ONE `example` per member pinning the TYPE: `example : <full type, binders written out> := @<qualified name>`. Copy the type from the
  source signature at the line given, ADDING the file-level `variable` binder in scope (`(ctx : ProgramCtx)` under `variable (ctx)` when the
  declaration mentions `ctx`; `{ctx : ProgramCtx}` under `variable {ctx}`); CONFIRM each with `#check @<name>` in a scratch file first —
  `#check` is authoritative; if it disagrees with the table, follow it and FLAG the row. Header docstring: charter row 0; «re-pinned per
  window row; every change = a changelog line»; the device's LIMIT — implicit ↔ explicit binder drift is not caught.

| # | Qualified name | Kind | Source | `ctx` | # | Qualified name | Kind | Source | `ctx` |
|---|---|---|---|---|---|---|---|---|---|
| 1 | `GoLean.GoCore.Machine.stepFn_sound` | thm | `MachineSound.lean:1681` | `{ctx}` | 13 | `GoLean.GoCore.Machine.stepFrameExit` | def | `StepFn.lean:153` | `(ctx)` |
| 2 | `GoLean.GoCore.Machine.step_complete` | thm | `MachineSound.lean:2079` | `{ctx}` | 14 | `GoLean.GoCore.Machine.recoverResult` | def | `Machine.lean:3763` | none |
| 3 | `GoLean.Semantics.run_ok_iff` | thm | `Trace.lean:60` | `{ctx}` | 15 | `GoLean.GoCore.Machine.enterFramePick` | def | `Machine.lean:901` | `(ctx)` |
| 4 | `GoLean.Semantics.Trace.erase` | thm | `Trace.lean:42` | `{ctx}` | 16 | `GoLean.GoCore.Machine.pushDefer` | def | `Machine.lean:3707` | none |
| 5 | `GoLean.GoCore.Machine.execProgLoop_single` | thm | `MultiSound.lean:666` | `{ctx}` | 17 | `GoLean.GoCore.Machine.execStmtLoop` | def | `StepFn.lean:1012` | `(ctx)` |
| 6 | `GoLean.GoCore.Machine.execProgLoopOut_snd` | thm | `Multi.lean:1970` | `{ctx}` | 18 | `GoLean.GoCore.Machine.Steps` | inductive | `Machine.lean:6157` | `(ctx)` |
| 7 | `GoLean.Semantics.Pool.program_run_iff` | thm | `ProgramTrace.lean:30` | none | 19 | `GoLean.GoCore.Machine.Config.abort?` | def | `Machine.lean:3877` | none |
| 8 | `GoLean.Semantics.Pool.observation_iff` | thm | `ProgramTrace.lean:79` | none | 20 | `GoLean.GoCore.findFunctionIn?` | def | `Syntax.lean:1003` | none |
| 9 | `GoLean.GoCore.Machine.runProgramSetupM` | def | `StepFn.lean:1181` | none | 21 | `GoLean.GoCore.methodInfoByFuncId?` | def | `Ops.lean:837` | `(ctx)` |
| 10 | `GoLean.GoCore.Machine.loadMany` | def | `Machine.lean:771` | `(ctx)` | 22 | `GoLean.GoCore.Machine.stepFn` | def | `StepFn.lean:326` | `(ctx)` † |
| 11 | `GoLean.GoCore.Machine.enterFrame` | def | `Machine.lean:824` | `(ctx)` | 23 | `GoLean.GoCore.Machine.stepFnIter` | def | `StepFn.lean:1042` | `(ctx)` † |
| 12 | `GoLean.GoCore.Machine.seqCont` | def | `Machine.lean:3682` | none | 24 | `GoLean.Semantics.iter_iff_trace` | thm | `Trace.lean:22` | `{ctx}` † |

Rows 1–21 = the proposal §4-i's 21 names; † = the response §6 bullet 1's three settled names, an [AGENT] addition (plan §3.2). Paths are
under `GoLean/GoCore/`.

## 5. Deliverable (ii) — the execution statement
**(a) `GoLean/GoCore/ExecutionStatement.lean`** — `namespace GoLean.GoCore.ExecutionStatement`; imports as (i). THE DEVICE: relations as
`inductive`/`def` over TODAY's 5-ary `Step` / 4-tuple `stepFn` (label = `AccessTrace`; the header says charter row 2 replaces it by
`StepLabel := { trace, picks, out }` and packet B re-states); every theorem is `def <name>_stmt : Prop := ∀ …` — elaborates with no proof
and no escape hatch. Packet B proves each `_stmt` as `<name>`. Use EXACTLY these names; the meaning of each is charter §2's text:
- `Blocked (c : Config) : Prop` — `∃ …, c = .blockedSend _ _ _ ∨ c = .blockedRecv _ _ _ _ _ ∨ c = .blockedSelect _ _ _ ∨ c = .blockedSync _ _ _ _`;
  `ZeroCost (c : Config) : Prop := c = .next .stop ∨ Blocked c` (the five arms `execStmtLoop` matches BEFORE `fuel`, `StepFn.lean:1012`).
- `inductive Prefix (ctx : ProgramCtx) : Nat → Store → Config → Choices → List AccessTrace → Store → Config → Choices → Prop` — `done` at `0`
  with `[]`; `step : stepFn ctx s c ch = .ok (c₁, s₁, ch₁, l) → Prefix n s₁ c₁ ch₁ ls sf cf chf → Prefix (n+1) s c ch (l :: ls) sf cf chf`
  (the labelled `Trace`, `Trace.lean:15`; plan §3.1).
- `inductive FinishOutcome | normal (s : Store) (ch : Choices) | deadlock (s) (ch) | aborted (t : String) (s) (ch) | refused (r : Refusal) (s) (ch)`.
- `inductive Finish (ctx) : Store → Config → Choices → List PickRecord → FinishOutcome → Nat → Prop`, FOUR constructors: `normal` (`c = .next .stop`;
  `[]`; `.normal s ch`; cost `0`); `blocked` (`Blocked c`; `[]`; `.deadlock s ch`; `0`); `aborted` (`Config.abort? c = some (first, rest)` ∧
  `Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch = (pick, ch'', rec)` ∧ `abortMsg ctx first rest pick = .ok t` →
  `rec`, `.aborted t s ch''`, `1`); `abortRefused` (same with `abortMsg … = .error r` → `rec`, `.refused r s ch''`, `1`). Docstring: `abortConsult
  first rest ch = Choices.consumeAt .repanicCollapse (repanicCollapseWidth first rest) ch` (`Machine.lean:3203`) and `Choices.consumeAtE_fst_snd`
  (`State.lean:475`) link them — cited, not proved.
- `def LRun (ctx) (s c ch) (ls : List AccessTrace) (rec : List PickRecord) (o : FinishOutcome) : Prop := ∃ n sf cf chf cost, Prefix ctx n s c ch ls sf cf chf ∧ Finish ctx sf cf chf rec o cost` — DERIVED.
- `replays (ctx) (s : Store) (c : Config) (ch ch₂ ch₂' : Choices) : Prop` by `seqConsumption ctx s c` (`Machine.lean:5190`): `none → ch₂' = ch₂`;
  `some (site, b) → (Choices.consumeAtE site b ch).2.2 = (Choices.consumeAtE site b ch₂).2.2 ∧ ch₂' = (Choices.consumeAtE site b ch₂).2.1`.
- `NoRefusal (ctx) (s : Store) (c : Config) : Prop` — no `Prefix`-reachable configuration on any tape has `stepFn … = .error (.refusal _)`, and
  no reachable abort has `abortMsg … = .error _`.
- The `_stmt`s (closed `Prop`s over `ctx` and all else): `prefix_refl_stmt`; `prefix_comp_stmt` (`n + m`, `ls ++ ls'`); `prefix_split_stmt`;
  `prefix_erase_steps_stmt` (→ `Steps ctx c s cf sf`); `prefix_erase_trace_stmt` (→ `Trace ctx n s c ch sf cf chf`); `prefix_iter_stmt`
  (`stepFnIter ctx n s c ch = .ok (cf, sf, chf) ↔ ∃ ls, Prefix …`); `finish_abort_step_stmt` (`Finish.aborted` at `(s, c, ch)` with `t` ↔
  `stepFn ctx s c ch = .error (.terminal (.panic t))`); `finish_refused_step_stmt` (↔ `.error (.refusal r)` at an abort configuration);
  `run_ok_iff_stmt` (`execStmtLoop ctx fuel s c ch = .ok (sf, chf) ↔ ∃ n ≤ fuel, ∃ ls, Prefix ctx n s c ch ls sf (.next .stop) chf`);
  `run_panic_iff_stmt` (`= .error (.terminal (.panic t)) ↔ ∃ n ls sf cf chf ch'' rec, n + 1 ≤ fuel ∧ Prefix … ∧ Finish ctx sf cf chf rec (.aborted t sf ch'') 1`);
  `run_deadlock_iff_stmt` (`= .error (.terminal .deadlock) ↔ ∃ n ≤ fuel, … Finish … [] (.deadlock sf chf) 0`); `run_fuelOut_iff_stmt`
  (`= .error .fuelOut ↔ ∃ ls sf cf chf, Prefix ctx fuel s c ch ls sf cf chf ∧ ¬ ZeroCost cf`); `replay_coverage_stmt` (`stepFn ctx s c ch = .ok
  (c', s', ch', l) → ∀ ch₂ ch₂', replays ctx s c ch ch₂ ch₂' → stepFn ctx s c ch₂ = .ok (c', s', ch₂', l)` — «no unrecorded consultation affects a
  step»; `stepFn_consumption_none`/`_some` (`MachineSound.lean:5785`/`:6175`) are its pieces; `_some` carries `c.appendTargetLocal` — state
  the coverage WITHOUT it and flag that premise in the note as packet B's first question); `classification_stmt` (unconditional: for every
  `fuel s c ch` EXACTLY ONE of — `.ok` with `run_ok_iff_stmt`'s witness; `.terminal` with a `Finish` at `n + cost ≤ fuel`; `.fuelOut` with
  `run_fuelOut_iff_stmt`'s witness; `.refusal r` with a `Prefix` of length `n ≤ fuel` to a configuration where `stepFn … = .error (.refusal r)`,
  or a `Finish.abortRefused`); `classification_wf_stmt` (the corollary under `StateWf ctx s ∧ NoRefusal ctx s c`: the first three cases only;
  cite `step_preserves_wf`, `StateWf.lean:8106`); `silent_projection_stmt` (`l = []` contributes `[]` to `ls.flatten`; note the post-reshape
  form `⟨[], [], []⟩` → `[]` per channel); `single_embedding_stmt` (`execStmtLoop ctx fuel σ c ch = r → transferable r → execProgLoop ctx (fuel +
  seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch = r` — `execProgLoop_single` restated; the cost relation IS `seqOpCount`,
  `MultiSound.lean:640`); `program_bridge_stmt` (`runProgramSetupM fuel p name args ch = .ok (pctx, c₀, s₀, locs, ch₁)` → `runProgramPoolOutM fuel
  p name args ch` equals the `execProgLoopOut pctx fuel ⟨#[.running c₀ none], s₀, 0⟩ {} ch₁ GoString.empty` fold with the `loadMany pctx sf locs`
  readout, as `ProgramRun`'s `runError`/`readError`/`done` say — setup's tape `ch → ch₁` INCLUDED; init OUTPUT empty BY REFUSAL,
  `initPrintRefusal?` `StepFn.lean:1118`, RETAINED per decision 10).
- Boundary CONTROLS: copy `FuelBoundary.lean`'s two `rfl` theorems + its `abortConfig` example as `example`s; the other four boundary facts
  (abort at fuel 1 → `.panic`; blocked at 0 → `.deadlock`; renderer refusal at 1 → `.refusal`, at 0 → `.fuelOut`) as `_stmt`s. NO other proof.

**(b) `docs/2026-09-24_execution-statement.md`** (≤ 120 lines): charter §2 made exact — a subsection per definition above: Lean name, prose
statement, which response-§2 correction ((1)–(5)) it discharges, the F2 cost accounting, the fuel convention KEPT (the boundary table), the
program-level premises + the RETAINED limitation, the label limitation documented («per-channel order, no total interleaving», response §3),
what packet B proves, and the charter §2-tail LIMITS paragraph verbatim. Every claim about today's code cites `file:line` at `3fb4a0d1`.

## 6. Deliverable (iii) — `docs/changelog/61958f2e-WINDOW.md` (new directory)
The proposal §1 table format — `| Arm / shape | Before (61958f2e) | After (main @ 3fb4a0d1) | What a re-pin must touch [inf] |` — one row per
shape, RESOLVED by `git diff 61958f2e 3fb4a0d1 -- GoLean/` and `git show 61958f2e:<path>` (never from memory): `Step` arity; `stepFn`'s tuple;
`stepFn_sound`/`step_complete`; read/write/alloc labels + `Store.alloc` normalization (`HeapNormal` in `StateWf`); `Trace.step`; the `Step` rule
count (expected 122 → 128 — a recorded counting command at both commits); the `Stmt`/`Cont`/`ChoiceSite` constructor lists (expected identical
— VERIFY by diff); the six `unseq` graph-body rules; the wire (`unseq` nodes; map-arm annotations) and the decoder's named refusals
(`GoLean/NativeToIR.lean`). `Tests/` is out of scope. Then a table «Window rows (PENDING)» with one placeholder row each for E6e, label, P, C3,
B6, C4 (`PENDING — filled by the landing lane`). Footer: «LIVE through the window; FROZEN at the offer commit (charter row 7)». Every «what to
touch» cell is `[inf]`.

## 7. Acceptance (capped; locked; record every EXIT code)
1. `GOLEAN_MEM_MAX=48G scripts/capped lake build GoLean` → `EXIT=0`, no `warning:` line from `GoLean/`.
2. `scripts/capped scripts/ci` (fast) → all green EXCEPT ONE EXPECTED red, `certificate provenance`: the compiled-inputs inventory covers every
   file under `GoLean/` (`tools/certification.py`), so the tracked certified records read STALE; the train's step 5a resolves it — NOT you (do
   not touch `baselines/certified/`). Any OTHER red: fix if yours, else STOP and report. `--diff` is NOT required: no existing `GoLean/**`
   module is edited and the new modules are statements, so no runtime behaviour can change; the train re-runs the gate at the merged tip.
3. `scripts/capped scripts/check-core-audit` → `Core totality audit gate: PASS`, the module count in its log up by two.
4. `scripts/check-spec-anchors` (cite `spec#`/`mem#` only if it resolves); `python3 tools/reconcile-records` (report findings verbatim; fix none).
5. `git grep -n -E "sorry|admit|native_decide|axiom|partial" -- GoLean/GoCore/BridgeSet.lean GoLean/GoCore/ExecutionStatement.lean` → empty.

## 8. Boundaries — what NOT to do
Create ONLY the three files of §4–§6, the two `import` lines in `GoLean.lean`, `docs/evidence/2026-09-24_packet-a/` (README per
`docs/evidence/README.md` + gate tails, ≤ 256 KiB) and the report. Do NOT edit any existing `GoLean/GoCore/*.lean` or `GoLean/*.lean` (root
imports excepted), `tools/`, `Corpus/`, `baselines/`, `lakefile.toml`, `scripts/`, `CLAUDE.md`, the root `HANDOFF.md`. No semantics change;
no proof of any `_stmt`; no `sorry`/`axiom`/`native_decide`/`partial`/`admit`; no gate weakening (no allowlist, skipped step or `GOLEAN_ALLOW_*`);
no `/tmp`; no uncapped build; never take over a lock; never kill by pattern (own PIDs only); never edit while a gate reads the tree; no push,
merge, tag or rebase onto a moved `main` (report the drift). Decide nothing this brief leaves open — flag it.

## 9. Report — `docs/2026-09-24_packet-A-report.md` (≤ 60 lines)
Branch + tip; files with line counts; the 24 pins with their `#check` types; every acceptance command with EXIT code + gate tail; the expected
red named; every `[inf]` cell; every `[AGENT Codex, packet A] INTERPRETED: …` (flagged, not decided) and every reading declined under the
ambiguity policy. End state: branch complete, worktree clean, nothing merged or pushed. Commit: `[AGENT Codex, packet A] contract: BridgeSet, ExecutionStatement, changelog draft`.
