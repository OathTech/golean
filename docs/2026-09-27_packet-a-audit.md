# Adversarial pre-merge audit — window packet A (the contract)

[AGENT] auditor (Opus 5.5 subagent), 2026-09-27, under the [USER]'s standing rule that every merge is audited
adversarially (Mike, relayed). Candidate: `window/packet-a-contract-0927` @ `209a1833` (three commits over `main` @
`7d2a62e5`). Audit branch: `review/packet-a-contract-0927` (this note + `docs/evidence/2026-09-27_packet-a-audit/`
only; the candidate is untouched). Nothing merged, pushed or tagged.

## VERDICT: FIX-FIRST

One class of FALSE STATEMENT refutes four of the owed `_stmt`s in Lean (F1): `stepFn` can raise the Go `panic`
terminal at a configuration that is NOT an abort, and `Finish` has no constructor for it. Packet B is briefed to
prove `classification` unconditionally (packet B brief item 6); as stated it cannot. A second finding (F2) makes the
domain corollary `classification_wf_stmt` vacuous on every run that completes normally, even once F1 is fixed. The
rest is sound: the fuel bridges, the boundary controls, the replay coverage (true without `appendTargetLocal`), the
24 pins (they are the actual statements; mutation-tested), the escape-hatch scans, the inventory row, and the records.

## Findings

### F1 — FALSE STATEMENT (FIX-FIRST): a panic terminal that `stepFn` raises outside the abort is unclassified

`stepFn` reaches the Go terminal `.terminal (.panic m)` at a NON-abort configuration whenever a helper bound with
`←` (not with `toResult`) raises a recoverable panic. Here is a verified instance: the variable read
`.evalE (.var x) env k` calls `Mem.loadFor` → `loadLoc` → `arrayGet` (`StepFn.lean:580`, `Ops.lean:1378`,
`:317`), and its index-out-of-range panic propagates unchanged out of `stepFn`. `Finish` covers `.panic` only
through `aborted`, which requires `c.abort? = some _`. `fatal` covers only `.fatal m`.

Witness (`evidence/StrayPanic.lean`, `scripts/capped lake env lean`, EXIT=0, axioms `propext`/`Classical.choice`/
`Quot.sound` only): `ctx0 = ProgramCtx.ofTables #[] #[]`, `s0 = {heap := #[.value (.array 0 .int) (.array #[])]}`,
`c0 = .evalE (.var "x") [[("x", .index (.base ⟨0⟩) 5)]] .stop`. For every tape, `stepFn ctx0 s0 c0 ch = .error
(.terminal (.panic "runtime error: index out of range [5] with length 0"))` (`rfl`), `c0.abort? = none` (`rfl`),
and `execStmtLoop ctx0 1 s0 c0 ch` = that panic (`rfl`). Proved in Lean:

- `¬ finish_abort_step_stmt` (the ← direction),
- `¬ run_panic_iff_stmt` (the → direction),
- `¬ classification_stmt` (none of the four cases holds at fuel 1),
- `¬ classification_wf_stmt`. The witness satisfies `StateWf ctx0 s0` (`decide`; `#eval` true first) and
  `NoRefusal ctx0 s0 c0` (proved). It also satisfies `MachineWf` (`#eval` true), so the packet's own flag
  (interpretation 6, «use `MachineWf`») does NOT rescue the corollary.

The configuration is probably unreachable from a lowered program: a variable is bound to a root cell. The
statements quantify over EVERY configuration, though, and neither `StateWf` nor `MachineWf` excludes it. There are
other un-`toResult`ed `←` binds in `stepFn` (`mapRangeStartSets`, `mapIterCandidates`, `Store.alloc`,
`defaultValue`, `allocDecls`, `bindIterVars`, `valueAsBool`, `stepFrameExit`), so the class may have more members.
Only `loadFor` was verified.

Behaviour: such a stray terminal is reported as a Go panic WITHOUT unwinding (no defers run, `recover` cannot
intervene). If it were ever reached, that would be a wrong answer, not a refusal. The same code path's commit-phase
twin is already refused BY NAME as `.internal` (`runCommit`, `Machine.lean:285`).

Fix, one of the following. The choice is a coordinator/[USER] question, because (b) is a semantics edit outside
packet A:
- (a) statement-only: generalize `Finish.fatal` to `Finish.raised : c.abort? = none → stepFn ctx s c ch = .error
  (.terminal t) → Finish ctx s c ch [] (.raised t s ch) 1` (`FinishOutcome.raised t`, `terminal? = some t`). Then
  `run_panic_iff_stmt` gains the disjunct «prefix + `raised (.panic t)`», and `finish_abort_step_stmt` gains the
  premise `c.abort?.isSome`. This states today's machine honestly.
- (b) semantics (preferred on the doctrine, «break incorrect behaviour»): convert a helper `.panic` escaping a
  non-apply `stepFn` arm into a named `.internal` refusal, as `runCommit` does. The statements then hold as written
  plus the `fatal` constructor, and the stray panic becomes a reported refusal (`ClassRefusal`). This needs a
  `--diff` run.

Either way, the design note should say why a four-constructor (then five-constructor) `Finish` is exhaustive. That
is the obligation the coordinator's `fatal` disposition met for one terminal and missed for this one.

### F2 — WEAKER-THAN-REQUIRED (FIX-FIRST, one line): `NoRefusal` is false on every normally completing run

`stepFn` refuses at the normal terminal: `stepFn … (.next .stop) … = .error (.refusal (.internal "step on terminal
configuration"))` (`StepFn.lean:850`; `#eval` in `evidence/NoRefusalVacuous.lean`). `NoRefusal ctx s c` asks that NO
Prefix-reachable endpoint have a refusing `stepFn` call, and the ZeroCost endpoints are not excluded. So
`NoRefusal` fails at every `(s, c)` from which `.next .stop` is reachable. Proved: `not_noRefusal_of_completes :
Prefix ctx n s c ch ls sf (.next .stop) chf → ¬ NoRefusal ctx s c`. `classification_wf_stmt` therefore stays
TRUE-but-vacuous on exactly the runs it exists for (normal completion). Response §2 (5) asks for «a corollary using a
proved reachable-state domain invariant», which this is not.

Fix: quantify `NoRefusal`'s first clause over non-zero-cost endpoints: `¬ ZeroCost cf → ∀ r, stepFn ctx sf cf chf ≠
.error (.refusal r)`. The driver never calls `stepFn` at a ZeroCost configuration. The blocked forms raise
`.deadlock`, not a refusal, so the only affected arm is `.next .stop`.

### F3 — WEAKER-THAN-REQUIRED (minor): no statement of TERMINAL-draw replay

Response §2 (4) asks that replay cover the «terminal draws», and §6 asks for «exact per-step and terminal
consultation coverage». `replay_coverage_stmt` is over `.ok` steps only. `finish_abort_step_stmt` quantifies
`rec`/`ch''` existentially and says nothing about a second tape. Packet B's brief routes the terminal draw «via
`finish_abort_step`», which does not state it. Fix: add `finish_replay_stmt`: `Finish ctx s c ch rec (.aborted t s ch'') 1 → c.abort? = some (first, rest) →
(Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch₂).2.2 = rec → Finish ctx s c ch₂ rec
(.aborted t s (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch₂).2.1) 1`, and the same
for `.refused`. It is immediate from the definition, but it is the coverage claim the consumer asked to see pinned.

### F4 — RECORDS: «packet B's first question» is already answered in the source

The design note, the header docstring and interpretation 5 pose «does `replay_coverage` hold without
`c.appendTargetLocal`?» as open. The proof of `stepFn_consumption_some` already says, at `MachineSound.lean:6243`:
«`hloc` is no longer needed here (kept in the statement for its callers)». The binder is `_hloc`. The reason is
that since C1 S3 a commit-phase panic is refused as `.internal` (`runCommit`), not delivered with the pre-pop tape,
so the post-pop-panic case that motivated the premise yields `.error`, and the coverage premise (`= .ok`) excludes
it. So the premise-free `replay_coverage_stmt` is TRUE in my assessment; I did not prove it. The note should cite
line 6243 so packet B drops the premise from `stepFn_consumption_some` rather than re-deriving it.

### F5 — NIT: `program_bridge_stmt` is the driver's definition unfolded

`program_bridge_stmt` is proved by `simp only [runProgramPoolOutM, h]; rfl`
(`evidence/NoRefusalVacuous.lean`, `program_bridge_trivial`). It pins the setup → pool-fold → readout seam and
nothing more. It does not connect to `Prefix`/`LRun`/the sequential embedding, which is the «one composable
account» of response §2. That is honest for packet A (the pool half waits, charter §2), but the design note should
say it is definitional so nobody counts it as a bridge. `single_embedding_stmt` is likewise literally
`execProgLoop_single` (proved in one line), and `silent_projection_stmt` holds by `simp`. Both are fine, and the
note should say so.

### F6 — NIT (records): one count is not derivation-anchored

The changelog's decoder row, «62 `fail` sites → 142», is reproducible (`grep -cE '(^|[^A-Za-z])fail +(s!)?"'` gives
62 / 142 at `61958f2e` / `7d2a62e5`), but the counting command is not recorded. By contrast, the `Step` rule count
records its awk. Add the command (CLAUDE.md: numbers derivation-anchored).

### Observation (pre-existing, not packet A): `check-mem-callsites` skips a declaration's HEADER line

The scanner `next`s past the header line, «a type mentioning an op is not a call». A one-line `def f … :=
loadMany …` is therefore invisible. Probe: appending `def scratchExec (…) := GoLean.GoCore.Machine.loadMany ctx s
l` on one line → PASS (EXIT 0). The same body on a second line → FAIL naming the site (EXIT 1). This is a fail-open
in an existing gate, predating this packet, and the packet's row is unaffected by it. Per «every detected gap is
rowed», it wants a row: scan the text after `:=` on the header line.

## Attack record (what held)

- **Fuel conventions (correction 3):** `ZeroCost`/`Blocked` are EXACTLY `execStmtLoop`'s five pre-fuel arms
  (`StepFn.lean:1016`–`1020`, arities 3/5/3/4). `stepFn` never raises `fuelOut` (grep: only the three drivers).
  `stepFn` errors at every ZeroCost configuration (`.next .stop` refuses, `StepFn.lean:850`; blocked forms throw
  `.deadlock`, `:939`–`950`), so no ZeroCost configuration is ever an interior `Prefix` point. Hence
  `run_ok_iff`/`run_deadlock_iff`/`run_fuelOut_iff` («Prefix of length exactly `fuel`», `¬ ZeroCost`) are true in
  my assessment. An abort's endpoint at exactly `fuel` is correctly fuel-out.
- **Deadlock:** the blocked arms' terminal is `Finish.blocked` (cost 0, `terminal? = some .deadlock`), so
  `ClassTerminal` covers it. `stepFn` raises `.deadlock` nowhere else, and `.raceDetected` nowhere.
- **Fatal:** the three throws (`Machine.lean:4392`/`4416`/`4443`) sit on `.unlock`/`.runlock`/`.wunlock`. The only
  sync consult is the TRY head (`syncConsult?`), so interpretation 7 (record `[]`, pre-call tape) is sound. The
  two fatal `rfl` controls elaborate.
- **Abort:** `abortMsg` throws only `.unsupported` (`Machine.lean:3912`), so `finish_refused_step_stmt` and the four
  boundary `_stmt`s are true in my assessment. `consumeAtE` records `[]` exactly at bound ≤ 1, and an empty tape
  at bound 2 records pick 0 (`State.lean:467`), so a replay by record carries the pick.
- **Correction (1):** every `FinishOutcome` carries store + tape, including `refused` and `fatal`. **(2):**
  `aborted`/`abortRefused` carry the consult and the renderer premise. **(4):** see F3/F4. **(5):** see F1/F2.
  Beyond F1–F3 nothing is weaker than, or silently different from, the response.
- **Stable set:** the 24 pins are the members' full types (all 24 elaborate in the default build). A mutated pin
  (`n ≤ fuel` → `n < fuel`) fails with `Type mismatch`. A drifted theorem pinned at the original type fails. A
  REAL source mutation (an extra `(_hn : True)` on `Trace.erase` in `Trace.lean`, then `lake build
  GoLean.GoCore.BridgeSet`) FAILS at `BridgeSet.lean:58` (restored and rebuilt afterwards). A same-type changed
  definition PASSES, which is the documented limit. The header says so and points at charter row 7, the
  semantic-equation file (packet D), which is the owed answer that response §6 asks for.
- **Totality:** no `sorry`/`admit`/`native_decide`/`axiom`/`partial`/`implemented_by`/`unsafe`/`opaque`/`extern`/
  `decide` in either file (git grep, empty). Imports are `Trace`/`ProgramTrace`/`MultiSound`. The gate's
  core-audit and engine-isolation steps are in the ci tail below.
- **Inventory row:** keyed (file, decl, op, count) like `ProgramRun`'s «NO EXECUTION» row. A second, multi-line
  executing `loadMany` in the same file FAILS the check (`NEW … scratchExec loadMany 1`). A changed count in
  `program_bridge_stmt` FAILS. So the row is not a gate weakening (but see the pre-existing observation above).
- **Changelog:** verified at `61958f2e` vs `7d2a62e5`. `Step` goes 4-ary (`Machine.lean:4390`) → 5-ary (`:5315`).
  `stepFn` goes from a 3-tuple (`StepFn.lean:255`) to a 4-tuple (`:326`). `Store.alloc` was total, un-normalized
  (`Store.lean:41`). Rules 122 → 128 (awk reproduced). The `Stmt`/`Cont`/`ChoiceSite`/`Config` constructor lists
  are 44/33/10/10, identical in order at both commits. Decoder `unseq:` refusals go 0 → 80. The E6 re-scoping
  matches the ledger's «RULED (2026-09-27)». Spot-checked `file:line` cites in the design note were all correct.
- **Provenance:** the worker's text is tagged [AGENT packet A worker], the two dispositions [AGENT] coordinator
  (header, docstrings, note, commit message, report). The brief's «[AGENT Codex, packet A]» tag is superseded by
  the 2026-09-27 execution-model ruling. That is consistent.

## The report's flagged interpretations (ten bullets; the ask said nine)

1. extra `import GoLean.GoCore.Trace`: **sound** (rows 3, 4, 24 need it).
2. `abortRefused` matches `.error (.refusal r)`: **sound** (`abortMsg` throws only `.unsupported`).
3. `NoRefusal`'s renderer clause uses the drawn pick: **sound** as a clause. The predicate as a whole **needs
   change** (F2).
4. the boundary statement names: **sound**.
5. `replay_coverage_stmt` without `appendTargetLocal`: **sound, and already answered** (F4).
6. `StateWf` vs `MachineWf`: the flag is **sound but insufficient**. The F1 witness satisfies `MachineWf`, so this
   needs change together with F1.
7. `Finish.fatal` records `[]` and keeps the pre-call tape: **sound** (verified).
8. `ClassRefusal` uses `n + 1 ≤ fuel`: **sound** (the exact bound; `n ≤ fuel` is implied).
9. helper names, and «exactly one» by result shape: **sound**. NIT: the `_stmt` states «at least one». Exclusivity
   is immediate, and packet B should state it as a named lemma, since the charter says «four DISJOINT cases».
10. the E6e row marked OFF the critical path: **sound** (ledger, 2026-09-27).

For the coordinator dispositions (Reading A `fatal`; the `loadMany` row), I found no defect in either as executed.
Disposition (1)'s premise, that a fifth constructor makes `Finish` exhaustive, is what F1 refutes.

## Gate

`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at `209a1833`, under the box-wide lock: **EXIT=1, RESULT: FAIL,
806 s, red on EXACTLY the expected 5a pair**. The two reds are `certificate provenance` («STALE certification:
changed dependency build/files/GoLean.lean») and `baseline diff`, with the one drift line
`imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` (the same stale-certificate
cause), over 3768 rows. Every other step is ok, including the escape-hatch preflight, `engine-isolation (core ↛
EnumDedup)`, the memory-module inventory, the warning-free core build, and the core totality audit (47 modules, 38
under `GoLean.GoCore`, classical trio only), and the negative baseline shows no regression. The reconciler is
report-only: the same two findings as the packet's report. Tail: `evidence/ci-diff.tail.txt`.
`scripts/check-evidence-size` on this branch with the evidence staged: PASS, EXIT=0.

## Not verified

- The premise-free `replay_coverage_stmt`, the `Prefix` algebra, `prefix_iter_stmt`, and the true bridges were
  assessed by reading `stepFn`/`execStmtLoop`/the consumption theorems, NOT proved. Packet B's proofs are the check.
- Whether the F1 stray-panic configuration is reachable from any lowered program, and the other candidate `←`
  sites of the same class.
- The fixture inventory (charter row 0's F3 procedure): it is not in packet A's brief and was not audited.

## Evidence (`docs/evidence/2026-09-27_packet-a-audit/`)

`StrayPanic.lean` (+ `.out`): the F1 witness and the four refutations. `NoRefusalVacuous.lean` (+ `.out`): F2, and
the F5 one-line proofs. `PinMutation.lean` (+ `.out`): the stable-set mutations. `srcmut.out`: the real-source
mutation build. `mem-callsites-probes.txt`: the inventory probes. `ci-diff.tail.txt`: the gate tail. Reproduce from
a worktree of this branch with warm `.lake`: `GOLEAN_MEM_MAX=16G scripts/capped lake env lean
docs/evidence/2026-09-27_packet-a-audit/<file>.lean`.

## Re-verification (`09c7fb0a`), 2026-09-27

[AGENT] auditor, at the coordinator's request. The candidate is now `window/packet-a-contract-0927` @ `09c7fb0a`,
rebased onto `core/stray-panic-refusal-0927` @ `05d0dbd4` (the F1 fix, disposition (b)). That lane is under its own
audit, and I reviewed it only as far as packet A's statements depend on it. This branch was rebased onto
`09c7fb0a`; the pre-rebase tip is `refs/snapshots/audit-packet-a-0927/pre-reverify`. Evidence: `reverify-*` in
`docs/evidence/2026-09-27_packet-a-audit/`.

### REVISED VERDICT: MERGE-CLEAN (conditional on the core lane's own audit), with one RECORDS nit

F1–F6 are resolved or recorded as disposed. I found no new false statement. The four statements F1 refuted are TRUE
in my assessment on the fixed interpreter, but they are not proved; packet B's proofs are the check. The merge
depends on `core/stray-panic-refusal-0927` passing its own audit, because packet A's four statements are true only
on top of it.

### Per item

- **F1 (resolved).** The old witness now gives `.error (.refusal (.internal "binding cell is not a root
  location: …"))` at fuel 1 (`#eval`; `step0_not_panic` proved for every tape). The original refutation file
  `StrayPanic.lean` now FAILS to elaborate (`reverify-StrayPanic-rerun.out`), and the packet's `F1Witness.lean`
  proves the witness is `ClassRefusal`, not `ClassTerminal`.
  - **Independent re-hunt for any other escaping `.terminal`.** I re-read every un-`toResult`ed bind in `stepFn`,
    `stepFrameExit`, `stepUnseqEnter`/`Value`/`Next` and their helpers on the fixed tree, and found NO other
    source.
    - `enterFramePick(V)` converts entry panics itself (`Machine.lean:901`/`921`).
    - Every `apply*`/`unseqLoad.plan` goes through `toResult` → `deliverS`/`deliverV`, and a commit-phase panic
      becomes `.internal` (`runCommit`).
    - `valueAsBool` and `unseqCellLoc`/`unseqLookupTarget` are stuck-only.
    - `mapRangeStartSets`/`mapIterCandidates` read through `Mem.mapRead` → `mapPayload?` (`Heap.lookup` +
      stuck; no path descent).
    - `allocDecls`/`bindIterVars`/`Store.alloc`/`defaultValue`/`normalizeValueForTy` have no panic source in
      their bodies (the normalizer's `NoPanic` lemmas live in `MachineSound.lean`).
    - `Mem.store`/`storeLoc`/`writeAt` refuse a bad formed index as `.internal` (`arrayIndexNatFormed`).
    - The six binding reads now go through `loadRoot`, and `loadRoot (.base _)` is exactly `loadLoc`'s `.base` arm
      (no panic). My census agrees with the investigation's (S1–S6).
  - **The other terminals.** `.deadlock` is raised only at the four blocked forms, which the driver never passes
    to `stepFn`. `.fatal` is raised only at the three sync throws (`Finish.fatal`). `.raceDetected` is never raised
    by `stepFn`. `stepFn` never raises `fuelOut`. On this reading `finish_abort_step_stmt`, `run_panic_iff_stmt`,
    `classification_stmt` and `classification_wf_stmt` are TRUE, though not proved.
- **F2 (resolved).** The new `NoRefusal` (`¬ ZeroCost cf → …`) is NON-VACUOUS: the packet's in-file positive
  control shows a one-step completing run satisfies it, for every `ctx`/`s`. It is SOUND, which I proved as
  `noRefusal_sound : NoRefusal ctx s c → ∀ fuel ch r, execStmtLoop ctx fuel s c ch ≠ .error (.refusal r)`
  (`reverify-Proofs.lean`, classical trio only). So it cannot admit a refusing run. The renderer clause is
  redundant (an abort configuration is not `ZeroCost`, so the first clause already covers its refusal). It is
  harmless.
- **F3 (resolved).** `finish_replay_stmt` is TRUE: I proved it as `finish_replay` (a same record implies the same
  pick, `pick_of_rec`). It is what the logic team asked for: the terminal `repanicCollapse` draw replays by
  site/bound/value record (§2 (4) «terminal draws», §6 «terminal consultation coverage»), for both `aborted` and
  `refused`, with `ch₂`'s own residual.
- **F4/F5/F6 (recorded).** The header, docstrings and note now cite `MachineSound.lean:6243`, call
  `single_embedding_stmt`/`program_bridge_stmt` DEFINITIONAL, and anchor the 62/142 count to its command. All as
  asked.
- **Pre-existing `check-mem-callsites` header-line gap:** recorded by the coordinator for a later tooling lane. Not
  re-checked; the core lane's `loadRoot` addition to `RAW_OPS` is a strengthening.
- **New RECORDS nit R1.** The changelog's new sentence says the core lane's `GoLean/GoCore` edits «are
  line-for-line, so every line number holds». That is false for `Ops.lean` after line 1380. The core lane
  inserted `loadRoot` (+13 lines) and `Mem.loadBinding*` plus bridge lemmas.
  - At `09c7fb0a`, `AccessKind` is at `:1758` (not `:1745`), `MemEvent` at `:1834` (not `:1821`), `AccessTrace`
    at `:1854` (not `:1841`) and `Mem.load` at `:1953` (not `:1939`).
  - The table's cells are stated at `5946adfa` and stay correct there. Only the parenthetical claim is wrong.
  - `StepFn.lean`/`Machine.lean` are line-for-line, and `Store.alloc` `:1251` holds.
  - Fix: say «line numbers are at `5946adfa`; `Ops.lean` shifts by +13/+14 after line 1380».
- **No new false statement.** The diff since `209a1833` touches only `NoRefusal`, `finish_replay_stmt`, docstrings
  and the positive control. All 24 pins elaborate unchanged against the core lane's edits (the default build is
  green, and `Step.evalVar`'s changed premise does not change any pinned type).

### Gate (re-verification)

- `GOLEAN_MEM_MAX=48G scripts/capped lake build GoLean` (warm): EXIT=0.
- `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at `09c7fb0a` (plus this branch's first audit commit,
  docs only), under the box-wide lock: **EXIT=1, RESULT: FAIL, 803 s, red on EXACTLY the 5a pair**.
  - `certificate provenance` (STALE: `build/files/GoLean.lean`) and `baseline diff` with the one line
    `imported-goose/channel/google-search PASS→FAIL/membership`, over 3768 rows.
  - Every other step is ok: core totality audit PASS (47 modules; the five poison controls compiled then
    rejected, as designed), engine isolation, memory inventory, the warning-free core build, eval tests
    (285 ok), and the negative baseline (no regression).
  - Honest scope: the run's receipt is marked `git_dirty=true`, because this re-verification's untracked
    `reverify-*` evidence files were in the tree (docs only, not compiled). The runtime state gated is `09c7fb0a`.
  - Tail: `reverify-ci-diff.tail.txt`.
- `scripts/check-evidence-size` with this section staged: PASS, EXIT=0.

### Not verified

- The four un-refuted statements, `replay_coverage_stmt` and the bridges are still assessed by reading, NOT
  proved.
- The census of escaping `.terminal`s is by reading the case tree, not by a machine check. Proving
  `c.abort? = none → stepFn … ≠ .error (.terminal (.panic _))` would be the machine check (a candidate lemma for
  packet B).
- The core lane beyond packet A's needs: its relation edits, its `Tests/` controls and its inventory rows.
