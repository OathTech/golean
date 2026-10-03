# Pre-merge audit — window packet D (the equations, the projections, the client, the gate) at `556ab207`

[AGENT auditor], 2026-10-03, branch `review/packet-d-equations-1003` off `window/packet-d-equations-1003` @ `556ab207`
(three commits over `main` @ `3bb8f4fc`: proofs `5335ee03`, records `03779748`, handoff fix `556ab207`). Under the
[USER]'s every-merge-audited rule (relayed). No edit to the candidate or to `main`; no merge; no push. Setup: fresh
worktree `.claude/worktrees/audit-packet-d`, fresh `.lake`, `scripts/setup-deps --from /home/dev/projects/golean`
(go/goose/raft at their pins); every build and gate through `scripts/capped`; full gates under the box-wide lock
(`mkdir artifacts/build-lock.d` + owner, trap release, wait-retry 120 s — taken 2×, never contended, released both
times). Scratch under `.tmp/` only (bulk deleted; `rm -rf -- "${d:?}"`). Evidence: `docs/evidence/2026-10-03_packet-d-audit/`
(64 KiB, six files). Read: `CLAUDE.md`, the brief and addenda, response §6 and C1, the 09-28 note's requests 1/2/7/9,
packet B audit F2/F3/F5, the continuations audit F2/F4, the handoff, changelog row 7a, the three commits, and the whole
of `Equations.lean`, `PoolProjection.lean`, `EquationClient.lean`, `check-equations`, `stepFn`'s body.

## Verdict: MERGE-CLEAN

No runtime definition changes (verified by diff and by import graph); the 229 equations hold and are non-vacuous on
78 concrete instances across all three groups, the setup equation and the projections (every premise discharged on the
instance; 53 compiled-code agreements with the interpreter); the pins are real (three mutated rows → three errors;
rows 1–173 byte-identical except row 62's comment/target, mechanically); the fold-back is as stated; the gate is red on
exactly the 5a pair with `semantic equations` green; `check-equations` and `check-core-audit` exit 0 standalone. The
findings below are usability, gate-robustness, inventory-precision and wording items — none blocks the merge; F1–F4 are
cheap follow-ups the offer's wording should absorb.

## Findings, by severity (with witnesses)

- **F1 (LOW, usability + records).** The documented «intended use» — `Equations.lean` header l. 24–25 «`simp only
  [stepFn_eqns, <the premises>]` is the intended use», handoff §1 item 1, changelog row 7a — does NOT fire on the arms
  whose premises bind values that appear only in the SUCCESSOR: `evalE_var` (`loc`, `v`), `next_storeK_var`/`_chain`/
  `_store` (`s'`), `exec_block` (`env'`, `s'`), `retV_callArgsK_enter` and every `enterFrame` arm (`e`, `s'`, `tr`),
  `frameExit_targets` (`vs`, `tr`), `retV_rhsK_apply`, `retV_stmtOpK_apply`, … — i.e. the memory and entry arms the
  logic side asked for. With the default discharger `simp only [stepFn_eqns, hl, hv]` reports «no progress»
  (`pins-bypass-stress.txt`: SymStress lines 17/22/29/33), while the same set closes `retV_ifK_true` and
  `next_panicResumeK_unrecovered` (premises over LHS variables only). The equations are fully usable — by
  instantiation (`rw [evalE_var env k ch hl hv]`, which is what EVERY premised step of the client's seven facts does),
  by `simp only [evalE_var env k ch hl hv]`, or by `simp (discharger := assumption) only [stepFn_eqns]` with the
  premises in context (all three verified, SimpVariants V1/V2/V4). Remedy (records, one sentence in the header, the
  handoff §1/§8 and row 7a): «arms whose successor mentions a premise-bound value are applied by `rw`/instantiation or
  under `simp (discharger := assumption)`; the plain `simp only [stepFn_eqns]` closes the premise-free arms and the side
  conditions over LHS variables». Optionally one client fact in the discharger form.
- **F2 (LOW, gate robustness — a speedbump, not a trust boundary).** The no-unfold guard is the regex
  `unfold stepFn|simp \[[^]]*stepFn|cbv|decide`. It is passed by `:= rfl`, `exact rfl`, `simp only [stepFn]; rfl`,
  `delta stepFn`, `simp_all [stepFn]`, `simpa [stepFn]`, `rw [stepFn]`, `unfold GoLean.GoCore.Machine.stepFn` (and
  `Machine.stepFn`); it false-positives on `simp [stepFn_eqns]`. Witness: `.tmp/Bypass.lean` (six client-style facts,
  each proving its `stepFn` statement by unfolding, GUARD hits 0, elaboration errors 0 — `pins-bypass-stress.txt`).
  The self-test (e1) exercises one spelling. The claim it backs — «7 facts by the equation set only» — is a records
  claim at the offer. Remedy (small, Lean-level, in `checkEnrollment`): for each `fact_*`, fold the proof term's
  constants and reject any under the prefix `GoLean.GoCore.Machine.stepFn.` (`eq_def`, `eq_N`, `match_N`, `_unfold`)
  and any `Eq.refl`/`rfl`/`Eq.mpr` node whose type has `stepFn` at the head of a side; keep the regex as the fast
  front. Until then the offer should say the guard is syntactic.
- **F3 (LOW, inventory/claim precision).** «ONE lemma per `stepFn` arm» (row 7a, header l. 13) has holes the header's
  «not expressible, reported» paragraph (l. 36–40) does not list: (a) **`retV_syncStK_apply_panic` is missing** while
  `applySyncOp` panics — witness: `applySyncOp ctx s0 ch0 .lock [.nil] env0 K0 = .error (.panic "runtime error: invalid
  memory address or nil pointer dereference")` and `stepFn` steps to `.panicking [⟨.interface (.defined 1) (.string
  "runtime error: …"), false⟩] K0` (`concrete-checks.txt`, R19); the atomic twin `retV_atomicStK_apply_panic` exists;
  the arm is `Step.syncStApply`'s panic half. (b) The non-panic `Stop` pass-through of the composed applies is stated
  only for `strictK` and `syncStK` (`_apply_error`); not for `stmtOpK`, `chanStK` (witness: a bare `.nil` operand →
  `stuck "expected channel value"`), `selectOpsK`, `rhsK`, `atomicStK`, `storeK`/`storeTarget`, `mapRangeK`,
  `mapIterK`, `enterFrame` at every entry position, `loadResults` at frame exit, `preprintDispatch` (witness: a
  hand-built `.pending` entry → `.internal "preprint: a pending rewrite on an unboxed payload …"`), `allocDecls` at
  block entry. (c) Unstated refusals not in the reported list: the `.panicking` frame's «deferred callee is not a
  function value»; the `valueAsBool` refusals at `ifK`/`whileK`/`andK`/`orK`/`boolK` (witness: `.retV (.int 1) (.ifK …)`
  → `stuck "expected bool value, got …"`); the non-deferrable callee at `deferCalleeK`/`goCalleeK`; `storeK`'s arity
  breach; the non-string result at the preprint frame. (d) `signalStep`'s table has ~18 rows; nine are equations —
  missing: `labelK` with `brkTo` other / `contTo` (same → `none`, the «continue to a non-loop label» refusal) / `brk` /
  `cont`; `loop` with `brkTo` / `contTo` (the `contHeadLabel` test); all five `mapIterK` rows; `breakableK` with
  `brkTo`/`contTo` — a client with `break L`/`continue L` or `break`/`continue` inside `for range` must unfold
  `signalStep` (witness: C24's unlisted row). None of (a)–(d) is a SUCCESS path the logic side's subjects (scalars,
  pointers, records, maps, calls/methods, closures, defer, panic/recover) reach; every success arm they reach has its
  equation. Remedy: state (a) (a three-line twin), add (b)–(d) to the header's reported paragraph, and soften row 7a to
  «one lemma per arm's success and panic forms; refusal pass-throughs as listed».
- **F4 (LOW, wording — the CLAUDE.md draft, handoff §7).** «… the sequential-to-pool terminal projection (every Go
  terminal but the sequential deadlock, at the pool's fuel `fuel + seqOpCount`; at equal fuel when no reachable step
  opens a registry boundary)» — the equal-fuel clause is proved for `transferable` (`.ok`/`.fuelOut`/`.panic`) only:
  `execProgLoop_single_noBoundary` takes `htr : transferable r`; the `fatal`/`raceDetected` terminals have the
  equal-fuel form only by composing `seqOpCount_eq_zero` with `execProgLoop_single_wide`, which is not stated. Either
  state the wide equal-fuel theorem (two lines) or word the clause «… at equal fuel, in packet A's `transferable`
  classes, when …». The rest of the draft is accurate against the proofs: the output fold claim is
  `execProgLoopOut_single_prefix`/`outFold_eq_fold`; «single-goroutine» is the scope; the owed pool/registry half is
  described as owed; the setup limit names `runProgramSetup_noInit` correctly; `NoRefusal`'s sequential scope stays.
- **F5 (INFO, request 1's floor — disclosed, should be named at the offer).** The premises bottom out in
  `loadRoot` (`evalE_var`, `frameExit_preprint`, `loadResults_cons`), `storeLoc` (`next_storeK_var`/`_chain`,
  `unseqValue`) and `Store.alloc` (`allocDecls_cons`/`bindParams_cons`, with the C4/B6 slot laws) — exactly as the
  header says — but a pointer read `*p`, a field read `x.f`, an index read `a[i]`, a map get/comma-ok stop at the
  COMPOSED `applyStrictOp`/`applyRhsOp` (witness R9: `retV_strictK_apply` with `applyStrictOp … (.deref .int)
  [.addr …] = .ok (.int 5, s0, [read])` — the read is inside the apply; no `applyStrictOp_deref`/`_fieldGet` law exists
  in the tree). Honest in the header («in the COMPOSED applies otherwise»); the handoff's §8 «Memory floor» line should
  say «for variable reads, plain/chain stores and entry; deref/field/index/map reads reach `applyStrictOp`».
- **F6 (INFO, elaboration — the G-C3 stop rule).** BridgeSet 1.0 → 1.9 s (handoff; I measure 1.64 s wall for the
  whole module on the lane, `pins-bypass-stress.txt`). The growth is 263 added rows, each a type-check of a written-out
  statement; the per-row cost is unchanged. G-C3 decision 6 was written for a hot PROOF module's cost regressing;
  a pin file growing by content is not that. A split into a second pin module would read 1.0× without changing any
  statement but would split the one file the changelog and the logic side cite as «the interface diff». My reading:
  record «additive pin rows — exempt from the ratio, absolute cost reported» in the G-C3 text; the handoff poses it
  correctly as the [USER]'s call.
- **F7 (INFO, records consistency).** Handoff §2.3 lists `retV_syncStK_more/_apply/_apply_error` — consistent with
  F3a (the panic twin is absent, not claimed). The equation file's reported-not-stated paragraph is incomplete (F3b–d).
  The client's fact 3 keeps the abort's renderer answer abstract (`hmsg`) — correct, since a hand-built bare-string
  entry REFUSES to render («panic abort rendering for payload …»; the frontend boxes payloads in the empty interface,
  on which the abort is `.terminal (.panic "boom")` — C16).
- **F8 (INFO, verified as claimed).** Rows 1–173 byte-identical except row 62's comment and target (mechanical diff of
  the two files' bodies); rows 174–436 consecutive, 263 rows, and the `@…` targets ↔ the 229 + 34 theorem names are a
  bijection (no pinned-but-absent, no present-but-unpinned); `Tests/GoCoreAudit.lean`'s required list = exactly those
  263 names (470 total, `check-core-audit` PASS); `stepFn_consumption_some` premise-free with `{tr : StepLabel}` in row
  62's position, row 62's statement unchanged, callers `Prefix.replay_coverage`/`stepFn_any_residual`/
  `MultiStreams.stepThread_pick_run` updated, `PrefixFacts.stepFn_consumption_some'` deleted; the F2 `guard_hyp` closers
  are fail-noisy by construction (a mis-fired alternative breaks the `first`); no equation RHS mentions `stepFn`
  (no rewrite loop is possible), and on fully symbolic shapes (`c`, `.retV v k`, `.evalE e env k`, `.exec stmt env k`,
  `.panicking chain (g :: k)`, `.next k`) `simp only [stepFn_eqns]` fails fast with «no progress»; the enrollment check
  compares the pin's type with the theorem's by `Expr` alpha-equality and fails closed on absence, mismatch and fact
  count; `check-equations`' self-tests fire.

## The nine attack items

1. **The equations are true, useful, stable.** 78 `example`s over a concrete program (five functions), store (five
   cells), environment and tape — each the equation applied to the instance or `simp only [stepFn_eqns]`, every premise
   discharged on the instance by `rfl` (20 premise theorems, each `#eval`ed first) — plus 128 `#eval`s (53 compiled-code
   agreements with `stepFn`, `concrete-checks.txt`): group (1) `exec_seqn`, `exec_call_nullary` (the entry on
   `enterFrame`), `retV_callArgsK_enter` and `retV_callValArgsK_enter` (two cells allocated: the argument and the
   result), `retV_callValCalleeK_nil`, `retV_deferCalleeK_push_frame`, `_push` through glue (`pushDefer` walked),
   `retV_deferArgsK_outside`, `retV_panicArgK`, `evalE_recoverCall` on the marker shape, `panicking_frame_defer_run`,
   `_defer_nil`, `next_panicResumeK_unrecovered`/`_recovered`, `panicking_glue`/`_seq`, `panicking_probeK` (both
   slots), THE ABORT `panicking_stop_settled` (`.terminal (.panic "boom")` on the boxed payload), THE PREPRINT PHASE
   `panicking_stop_pending` (selection, and the collision slot 0 → `preprintDrop`), `retV_preprintK_string`,
   `panicking_preprintK` (`fatal "panic while printing panic value: boom"`), FRAME EXIT with a named result and a
   caller target (`next_frame`/`signal_ret_frame` + `frameExit_targets`, the `loadRoot` read on the label;
   `loadResults_cons`), with a PENDING DEFER and named results (`frameExit_defer_run` drains first), `frameExit_nil`,
   `frameExit_extra_results` (its `hk` discharged), `signal_table` + `signalStep_loop_cont`, `signal_frame_escape`,
   `next_stop`; group (2) `evalE_var` through `loadRoot_base` at the heap cell, `_unbound`, `evalE_ref`, `evalE_global`/
   `_oob`, the spine `exec_assign_var` → `retV_tgtOpK_rhs` → `retV_rhsK_apply` → `next_storeK_var` with `storeLoc_root`
   (the in-place normalized write) and the read-back `Heap.lookup_set_self`, `next_storeK_panic` (nil address at the
   store), `next_storeK_done`, `exec_block` with `allocDecls_cons`/`_nil` and `Heap.lookup_push_self` (C4),
   `bindParams_cons`/`_nil` from the empty store (B6); group (3) `retV_ifK_true`, `retV_whileK_false`, `evalE_and` +
   `retV_andK_false`, `evalE_intLit` (int8 normalization), `evalE_strict_more` (`x + y`), `retV_strictK_apply` (12),
   `_apply_panic` (divide by zero), `evalE_strict_nullary` (`nil`), the deref read, `exec_print` + `retV_stmtOpK_apply`
   (the output on the label), **`randIntn`** (`exec_wide` + the apply: cell ← 2, residual `[9]`, pick `⟨intn, 3, 2⟩`),
   `exec_allocNew`, **channels** (`exec_chanSend`, `retV_chanStK_apply` parking a send on the typed nil channel as
   `.blockedSend none …`, `blockedSend` = deadlock), **select** (`exec_selectStmt_block`/`_default`,
   `retV_selectOpsK_apply` taking the default), `exec_goStmt` + the spawn refusal, map range over the typed nil map
   (`retV_mapRangeK`, `next_mapIterK_done`), `exec_mapLookup`, `exec_assignMany_arity`, the probe, **`unseq`**
   (`unseqEnter` on a one-occurrence graph, `unseqRun_eval`, `unseqValue` — one `storeLoc` into the binder cell).
   Premises are explicit and local: no `StateWf`, no global well-formedness anywhere in the file (C1's condition).
   The `.retV` filing correction is honoured (the five families are `.retV v` arms; `stmtOpK` likewise). Arms NOT
   covered: F3 (a)–(d), plus the `.evalE` catch-all's «unclassified expression» (unreachable, as reported) and the
   `.retV` «expected function value» over an arbitrary value (reported). For the subjects' reach: no success arm missing.
2. **Usability.** The client's seven facts and my 78 instances close without `unfold stepFn`. The simp-set form is
   limited as F1 states; the client's own idiom (`rw` with premises) is the working one. No loop or blow-up on
   symbolic continuations (F8). The guard is bypassable (F2).
3. **The setup equation.** `runProgramSetup_noInit` applied to the concrete program (`fId`, one argument, one result):
   the entry configuration `.exec fId.body frameEnv (.frame [] [] [] [] .stop fId.id)`, the store of two cells, the
   pinned `[.base ⟨1⟩]`, the residual tape = the input tape (`[3]`), by the theorem with all eight premises by `rfl`
   and by evaluation; `setup_lookup_arg`/`_result`/`setup_resultLocs`/`setup_heap_size` on the instance. Consistent
   with `runProgramSetupM`'s body line for line, with C4's `entrySlot {} i = .base ⟨i⟩`, and proved via B6's
   `bindParams_lookup`/`bindParams_heap_size` and `allocDecls_lookup`.
4. **The projections.** `transferableWide` excludes exactly the sequential deadlock (the wake-ready blocked seed —
   `MultiSound`'s stated reason) and the refusals (a spawn position refuses sequentially but forks in the pool — the
   honest blanket); `fuel + seqOpCount` as in `execProgLoop_single`; (a) output agreement over `execProgLoopOut` with
   `seqOut` identified with the `Prefix` labels' fold; (b) the terminal projection for every `t ≠ .deadlock`; request
   9's `hnb` is a per-`Prefix`-step property discharged by `afterStepFlag_none_of_noRegistry` — the `seqOpCount = 0`
   premise is genuinely gone (though only for `transferable`, F4). Instances: a printing program — pool output
   `"hi\n"` = `seqOut`, outcome identical; a panicking program — both `.terminal (.panic "boom")`, printed prefix
   empty on both sides; a deadlocking program — both deadlock here (excluded by the theorem, not refuted).
5. **The fold-back.** As claimed (F8).
6. **No runtime change.** `git diff 3bb8f4fc 556ab207 -- GoLean` touches `GoLean.lean` (three imports), `BridgeSet`
   (rows), `MachineSound` (two proof blocks; one theorem's binders), `MultiStreams` (a hypothesis renamed `_hloc`,
   statement unchanged), `Prefix` (two call sites renamed), `PrefixFacts` (the copy deleted), and adds `Equations`,
   `EquationsAttr`, `PoolProjection`. The only new `def`s are `transferableWide`, `seqOut`, `outFold` (proof layer);
   the new modules are imported by `BridgeSet`, the client and the root `GoLean.lean` only — no runtime module, no
   driver. `ci --diff` red on exactly the 5a pair; baseline untouched; whole-corpus choice trace not re-run (no
   runtime byte changed).
7. **Pins and audit.** F8; three mutants (`exec_seqn`'s label, `evalE_var`'s successor, the setup equation's residual
   tape) → three type mismatches. The in-file exhaustiveness `#eval` ran green in the gate and standalone. Elaboration:
   F6.
8. **The CLAUDE.md sentence.** F4; otherwise accurate and honest about what remains owed.
9. **Gates.** `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at `556ab207`, fresh `.lake`, under the lock:
   **EXIT 1** — `FAIL certificate provenance` (STALE on `GoLean.lean`) and `FAIL baseline diff` (the one certified
   row `imported-goose/channel/google-search PASS/membership → FAIL/membership`), every other step ok, `ok semantic
   equations (scripts/check-equations)`, `cases=3821 pass=3583 fail=238`, negative baseline no regression, reconciler
   2 findings (C9 the 5a STALE; the standing C13), 1613 s. `scripts/check-equations` standalone under the lock:
   **EXIT 0**. `scripts/check-core-audit` standalone under the lock: **EXIT 0** (54 modules, 470 required).

## What I could not verify

- The main-side elaboration A/B numbers (no fresh `main` build here; the lane's BridgeSet measured once, 1.64 s).
- `next_preprintK`'s SUCCESS arm on a real method set (no fixture with `methodSets` built; its panic/error arms were
  exercised); the multi-ready select consult arm (only the default branch instantiated); `applySelect`/`applySyncOp`
  on live channels/mutexes.
- The whole-corpus choice trace and the raft twin (not re-run; the packet changes no runtime byte and the gate moved
  no row beyond the 5a line).
- Whether `simp only [stepFn_eqns, premises]` could be made to fire with a different lemma shape (e.g. premises
  stated over the successor's projections) — out of this audit's scope; F1 records the working forms.

Provenance: every judgment above is the [AGENT auditor]'s; the [USER]'s calls (the merge, the CLAUDE.md sentence,
G-C3's reading of additive pin rows, the follow-ups F1–F4) are posed, not taken. Commit on this branch only.
