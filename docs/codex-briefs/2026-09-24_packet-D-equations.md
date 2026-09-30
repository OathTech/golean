# Codex packet D — the semantic EQUATIONS, the rewrite set, the toy client, the gate

STATUS: **DRAFT — launchable after C4 (charter row 6) lands on `main` (the FINAL shape); the coordinator REFRESHES §3 (the input commit,
`stepFn`'s arm line numbers, the arm list after label/P/C3/B6/C4) and deletes this sentence.** [AGENT] planning writer 2026-09-24.
Rulings: decision 8 — the «independent in-repo consumer» is a TOY semantic-equation CLIENT, GoCore only, symbolic state/continuations, in the
test/contract graph, NOT an Iris `Language` instance (typed profiles PARKED 2026-09-16, `docs/2026-09-16_typed-profiles-parked.md`; CLAUDE.md:
«we DO NOT ship any higher level reasoning»); decision 6, executed as an Opus 5.5 subagent dispatched by the coordinator ([USER] 2026-09-27).
Executes charter row 7 (equations) + §3 (priority); plan `docs/2026-09-24_window-plan.md` row 7a.
Provenance: **[AGENT packet D worker]**.
**Ambiguity policy: if two readings of this brief differ materially, STOP, write both in the report, do not choose.**

## 1. Purpose
The re-pin offer's THREE separate checks (charter row 7): statements (`BridgeSet.lean`, exists), EQUATIONS (proved per-arm `stepFn` lemmas —
they catch a definition changed under the same type), and a small INDEPENDENT client that USES the equations and never re-unfolds `stepFn`.
Plus the gate that runs the last two. No behaviour change anywhere.

## 2. Setup
`git -C /home/dev/projects/golean worktree add .claude/worktrees/codex-packet-d -b codex/packet-d-equations-<date> <MAIN TIP after C4 — refreshed>`.
Scratch under the worktree's `.tmp/` only; every build/gate through `scripts/capped`; the box-wide lock for any full build or gate
(`mkdir /home/dev/projects/golean/artifacts/build-lock.d` + `owner` file; wait-retry 120 s; never take over; release under a trap); one writer.

## 3. Inputs (REFRESHED at launch)
`<commit>`; `GoLean/GoCore/StepFn.lean` — `stepFn`'s top-level arms (at `3fb4a0d1`: `.panicking chain k` :329, `.exec stmt env k` :392,
`.evalE e env k` :572, `.retV v k` :614, `.next k` :848, `.signal sg k` :915, the four blocked arms :939–950; REFRESH), `stepFrameExit`,
`execStmtLoop`; `Machine.lean` (`Step`, `enterFrame`, `enterFramePick`, `pushDefer`, `seqCont`, `recoverResult`, `signalStep`, `abortConsult`,
`abortMsg`); `Ops.lean` (`loadLoc`, `storeLoc`, `Store.alloc`, `normalizeValueForTy`); `Syntax.lean` (`Stmt`, `Expr`); `Prefix.lean`,
`ExecutionStatement.lean`, `BridgeSet.lean`; `lakefile.toml`, `scripts/ci-libraries.json`, `tools/ci_libraries.py`, `scripts/ci` (the
`library_step` lines), `scripts/check-unseq-wire` (the gate-script precedent), `Tests/UnseqWire.lean` (the `lake env lean --run` + PASS-line
precedent), `Tests/GoCoreContract.lean`; charter §3 (the priority table); response §6 (the equation request); `docs/changelog/61958f2e-WINDOW.md`.

## 4. Deliverables
1. **`GoLean/GoCore/Equations.lean`** (reachable from `GoLean.lean`): one lemma per `stepFn` ARM over a SYMBOLIC continuation `k`, environment
   `env`, store `s` and tape `ch`, with EXPLICIT operation premises (e.g. `henter : enterFramePick ctx s fid args ch = .ok (.ok (f, fenv, locs, s', tr), ch')`),
   each of the shape `stepFn ctx s (<config pattern>) ch = .ok (<successor>, s', ch', <label>)` or `= .error <stop>`. PRIORITY (charter §3),
   arm families by the `match` structure at `3fb4a0d1` — REFRESH against the final shape: (1) control, calls, defer, return, panic/recover:
   `.exec` arms `.call`, `.callValue`, `.deferCall`, `.returnStmt`, `.breakStmt`, `.continueStmt`, `.breakTo`, `.continueTo`, `.panicStmt`,
   `.labeled`, `.breakable`; `.next` arms `.frame` (exit via `stepFrameExit`), `.panicResumeK`, `.callArgsK`, `.callValCalleeK`, `.callValArgsK`,
   `.deferCalleeK`, `.deferArgsK`, `.seq`, `.loop`, `.breakableK`, `.labelK`; `.evalE .recoverCall`; the `.panicking` arms (a frame with / without
   pending defers; the abort at `.stop`); the `.signal` arms through `signalStep`. (2) memory: `.evalE .var`/`.ref`/`.global`; `.retV` into
   `.tgtOpK`/`.rhsK`; `.next .storeK`; `.assign`, `.assignMany`, `.allocNew`; `.block` (C4's block-entry allocation). (3) the rest: `.seqn`, `.ifThenElse`/`.ifK`,
   `.while`/`.whileK`, `.and`/`.or`/`.boolK`, `.strictK`, the literals, `.mapLookup`/`.mapAssign`/`.mapDelete`/`.mapRange`/`.mapIterK`, `.typeAssert`,
   `.makeSlice`/`.makeMap`/`.appendSlice`/`.copySlice`, `.stmtOpK`, `.print`, the channel/select/go/sync/atomic arms, `.unseq`/`.unseqK`. An arm
   whose premise set is not expressible without a NEW helper is REPORTED (stated as far as it goes), never helper-ed. No `unfold stepFn` in any
   lemma's STATEMENT (proofs may unfold). The NAMED rewrite set `stepFn_eqns`: `register_simp_attr stepFn_eqns` + `@[stepFn_eqns]` on every
   lemma, used as `simp only [stepFn_eqns]` — if this toolchain refuses the attribute form, a `macro "stepFn_eqns" : tactic => `(tactic| simp only [<list>])`
   is the fallback; say which was used and why.
2. **`Tests/EquationClient.lean`** — the TOY CLIENT: imports GoCore modules only; SYMBOLIC state, continuation and environment; proves ≥ 6 small
   facts using ONLY `stepFn_eqns` + the `Prefix`/`Finish` lemmas: a call entry then return; a `defer` registered then drained on return; a write
   then a callee panic — the write survives at the `Finish.aborted` endpoint; an `if` on a symbolic Boolean; a load/store pair; a block entry
   allocating then a lookup. NEVER `unfold stepFn`, `simp [stepFn]`, `rfl`/`decide`/`cbv` on `stepFn`. A `main` printing
   `Equation client: PASS — <n> facts by the equation set only`. ENROLMENT (fail-closed by `tools/ci_libraries.py`'s ownership check — an
   unowned `Tests/*.lean` fails the gate): `[[lean_lib]] name = "EquationTests"  globs = ["Tests.EquationClient"]` in `lakefile.toml`;
   `"equations": {"libraries": ["EquationTests"], "executables": []}` in `scripts/ci-libraries.json`; the step in `scripts/ci` (item 3). No
   runtime module imports the client.
3. **`scripts/check-equations`** (precedent `scripts/check-unseq-wire`; `set -Eeuo pipefail`; `typed-gate-scratch.sh` for scratch): (a)
   `scripts/capped lake build GoLean EquationTests`; (b) `scripts/capped lake env lean --run Tests/EquationClient.lean | tee` + `grep -q '^Equation client: PASS'`;
   (c) the NO-UNFOLD guard: `git grep -n -E "unfold stepFn|simp \[[^]]*stepFn|cbv|decide" -- Tests/EquationClient.lean` must be EMPTY; (d)
   EXHAUSTIVE enrollment: a `#eval` in the client's companion section lists every `theorem` of namespace `GoLean.GoCore.Equations` and fails on
   any without an `example : <its statement> := <name>` pin in the client; (e) SELF-TESTS: a scratch copy of the client with one `stepFn_eqns`
   use replaced by `unfold stepFn` must make (c) fire; a scratch copy with one pin deleted must make (d) fire. Wired into `scripts/ci` as
   `library_step equations bash scripts/check-equations` beside `check-unseq-wire`, with a `step`/`ok`/`bad` triple like its neighbours.
4. **`BridgeSet.lean`**: every equation lemma pinned (statement drift fails the build; the equation file catches definition drift; the client
   catches usability drift — three separate checks, charter row 7). **`docs/changelog/61958f2e-WINDOW.md`**: the equation families listed;
   a line `candidate freeze: <your tip>` — the coordinator freezes the file at the offer commit (plan row 7b), not you.

## 5. Acceptance (capped; locked; every EXIT code recorded)
`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` green (the additions change no behaviour — a moved baseline row = STOP and report);
`scripts/capped scripts/check-core-audit` PASS (the two-way closure now includes `Equations.lean`); `scripts/capped scripts/check-equations`
PASS INCLUDING its self-tests (record their output); `python3 tools/ci_libraries.py selftests` green; `python3 tools/reconcile-records` findings
reported; evidence `docs/evidence/<date>_packet-d/` (README + gate tails, ≤ 256 KiB). The fast steps' `certificate provenance` STALE red is
the train's 5a business.

## 6. Boundaries — what NOT to do
NO change to `stepFn`, `Step`, any rule or any definition's behaviour — an equation that does NOT hold is a FINDING: report it with the goal,
do not fix the semantics. NOT an Iris `Language` instance: no `Obs`/`Prim`/WP/ownership/resource vocabulary, no facade module, no re-export of
GoCore, no `GoLean/Interface.lean`. No runtime dependency on the client. No `unfold stepFn` in the client. No `sorry`/`axiom`/`native_decide`/
`partial`/`admit` in `GoLean/` or `Tests/`. No gate weakening — the new gate may only ADD reds; no allowlist, no skipped step, no `GOLEAN_ALLOW_*`.
No `baselines/` edit. No `/tmp`. No uncapped build. Never take over a lock. Never kill by pattern (own PIDs only). Never edit while a gate reads
the tree. No push, merge, tag or rebase onto a moved `main`. No root `HANDOFF.md` edit.

## 7. Report — `docs/<date>_packet-D-report.md` (≤ 60 lines)
Tip; the arm inventory — per arm: proved / stated-only / reported-not-expressible, with the reason; the rewrite-set device used; the client's
facts; every acceptance command with EXIT code + tail, the self-tests' output; every `[AGENT Codex, packet D] INTERPRETED: …` (flagged, not
decided); every equation found FALSE (goal verbatim). End state: branch complete, clean, nothing merged or pushed.
Commit: `[AGENT Codex, packet D] equations: per-arm stepFn lemmas, stepFn_eqns, the toy client, scripts/check-equations`.

**Coordinator addenda (2026-09-30).** From the continuations audit: (F4) state the real FRAME-EXIT equations here (`stepFrameExit` with named results, defers pending, result readback) — packet C's `stepFrameExit_nil` covers only the all-empty frame; (F2) when re-touching `stepFn_sound`/`stepFn_consumption_none`, close the `.retV`/`.next` catch-alls by the arm's shape, not the positional `case140`/`case155` tags. From the logic team's 2026-09-28 note: requests 1, 2 and 7 (premises bottoming out in the memory laws with their `.retV` filing correction; the pinned no-globals setup equation; the unwinding equations).
