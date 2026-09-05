# C-arc step 2 — B4 (Signal / Status) + G-C5 (`.opDone` out of `Config`) (2026-09-05)

**Status:** BRANCH-COMPLETE on lane `c-arc-b4` (SHAs in §9; not merged —
the audit ask is the coordinator's to pose; merge/push are the [USER]'s).
**Provenance:** design gate G-C5 RULED [USER] 2026-09-04 as recommended
(relayed by the [AGENT] coordinator — «let's move ahead with the plan»,
cited as relayed, not firsthand; `docs/2026-09-04_reasoning-surface-plan.md`
§5.4); the coordinator's per-gate reading of that ruling CONFIRMED [USER]
2026-09-05 («(1) approved», relayed; `docs/2026-08-31_qrow-rulings.md`
record of that date). B4 is arc step (iv) of the [USER]-ratified
design-hygiene arc (`docs/2026-09-03_design-hygiene-arc.md`; review
entry `docs/2026-09-03_grumpy-professor-review.md` §3(b) B4, C5). Every
design choice below is [AGENT] unless marked; the standing [USER]
directions this lane worked under (relayed): «do the disruptive thing if
it'll result in a more useful reasoning surface»; break incorrect
behaviour rather than preserve it; every detected gap gets a frontier
row; refusals name their cause. **Evidence:**
`docs/evidence/2026-09-05_c-arc-b4/`. Template: the wave-(iii) note
(`docs/2026-09-04_hygiene-wave3-design.md`) and the G-U note
(`docs/2026-09-04_c-arc-gu-design.md`).

Conventions (review §3): "preserving" = for every program, stream and
fuel the same `Except Stop Readout` (constructor, message, readout) on
the differential's driver, and the choice tape consumed at the same
sites with the same bounds in the same order; here additionally PER
STEP — the same machine step count on both drivers at every fuel (the
exact-fuel eval tests, `pollerMain_F` at 74/90, pin this). Each item is
one checkpoint commit gated by `scripts/capped scripts/ci --diff` at
ZERO baseline drift and by the whole-corpus labeled-consumption trace
byte-identical PER CONSUMPTION to the pre-lane snapshot (`scripts/
choice-trace-corpus --dump`), plus status + observation hash identical on
every (row, stream) line.

## 1. What B4 changed — the control side (commit 1, `40fd1903`)

**`Signal`.** `inductive Signal | brk | cont | ret | brkTo L | contTo L`;
`Config.signal (sg : Signal) (k : Cont)` replaces the five constructors
`.breaking/.continuing/.returning/.breakingTo/.continuingTo`. `Config`
has 10 constructors (from 16 on `main`): `exec evalE retV next signal
panicking blockedSend blockedRecv blockedSelect blockedSync` (audit fix
R1: an earlier draft said 9).

**The frame×signal TABLE.** `signalStep : Signal → Cont → Option Config`
(Machine.lean) IS the table the review's Q6 asked for — one row per
statement frame (`seq`, `breakableK`, `labelK`, `loop`, `mapIterK`), one
column per signal; `some c'` = pass (`.signal sg k'`) or catch (`.next
k'`, the `while` re-test, the `mapIterK` re-pick); `none` where the frame
does not resolve the signal purely: the call frame's `ret` (frame EXIT,
state-touching) and every refusal, which `signalRefusal : Signal → Cont →
Stop` names (total — "break outside loop", "function body escaped with
labeled continue", "continue to non-loop label L", …; the same texts as
the ~37 longhand arms they replace). The docstring carries the table as a
table. `Stmt.signal?` is the statement column (the five control-transfer
statements → their signal).

**The rules.** `Step.signalStmt` (`stmt.signal? = some sg`) and
`Step.signal` (`signalStep sg k = some c'`) replace `seqBreak/seqContinue/
seqReturn`, `loopContinue/loopBreak/loopReturn`, `breakableBreak/
Continue/Return`, `labelBreak/Continue/Return`, `returnStmt/breakStmt/
continueStmt/breakToStmt/continueToStmt`, `breakToSeq/Loop/Breakable/
MapIter/LabelMatch/LabelSkip`, `continueToSeq/Breakable/LabelSkip/
LoopMatch/LoopSkip/MapIterMatch/MapIterSkip`, `mapIterContinue/Break/
Return` (32 rules → 2). The four frame-exit twins `frameReturn`,
`frameReturnTargets`, `frameDeferReturn`, `frameDeferNilReturn` STAY as
rules, restated at `.signal .ret (.frame …)`: a `return` at a call frame
IS a fall-through at a call frame (the review's Q6 observation), and the
exit touches state (defer drain, result read), so it is a rule family,
not a table row. `Step` has 108 rules (from 141).

**`stepFrameExit`.** The executable states the twin-ness ONCE: `stepFn`'s
`.next (.frame …)` arm and its `.signal .ret (.frame …)` arm are the same
function `stepFrameExit s targets tenv results ds k' w choices`.
`stepFrameExit_sound` proves BOTH entries' rules from one success;
`stepFrameExit_consumption_none/_some` give B8's consumption theorem
both entries at once. (Deviation from the review text, which imagined
`signalStrip : k.class = glue → …` over `Cont.tail`: the table is stated
per frame rather than through `Cont.class`, because three of the five
statement-glue frames CATCH signals — `Cont.class` says "stmtGlue" for
`loop`/`breakableK`/`labelK`/`mapIterK` alike, so a glue-strips rule
would need the catch cases beside it anyway. Nothing prevents restating
the pass rows through `Cont.tail` at C3.)

## 2. What B4 changed — the terminals and the pool (commit 2, `165822ef`)

**The abort.** `Config.panicked (msg : String)` — the k-less terminal —
is DELETED. An unrecovered chain at the empty continuation, `.panicking
(first :: rest) .stop`, is THE ABORT (`Config.abort?`); it has no rule
(`step_abort_elim`); what happens next is the DRIVER's: the sequential
machine raises the `panic` terminal there (`stepFn`: `throw (.panic (←
abortMsg s first rest))`, ONE step — the fuel the old `panicAbort` step
cost), and the pool turns the goroutine into its tombstone
(`Thread.aborted msg`, `stepThread`, event `.aborted`, relation
`StepM.abort`, one pool step), which `MultiConfig.panicMsg?` reads at the
next loop head exactly as it read `.panicked`. Both render through the
shared `abortMsg` (the former `renderPanicHead` arm; a chain with no
pinned rendering refuses by name — BUG-004 unchanged). This is what §1.3
of the reasoning-surface plan asked for: «"panicked" a THREAD status the
pool observes, not a configuration the sequential relation gets stuck
on» — the `hdrain` obstacle to `Language.Context.primStep_fill` (the
two-step `.panicking → .panicked → stuck`) is gone with the k-less
constructor.

**One terminal.** `Config.isTerminal` and `Config.terminal` are `.next
.stop` alone. The three signal-at-`.stop` shapes the drivers used to
classify as `returned/broke/continued` completions are REFUSALS now
(`signalRefusal`: «return unwound past the entry frame» / «break outside
loop» / «continue outside loop») — every Program driver runs its subject
under a barrier frame, so only a bare-statement `execStmt`/`execProg` run
could ever reach one, and A8 had already marked `ExecOutcome` as B4's to
delete. `ExecOutcome` is deleted; `execStmtLoop`/`execStmt`/`execProgLoop`
/`execProgLoopOut`/`execProg` return `Except Stop (ExecState × Choices)`;
`mainOutcome? : Option ExecState`; `EnumSpec.obsOf?`, the checker
(`checkNode`), the engine (`nodeObs`), the CLI enumerators and the tracer
follow (the «main terminal outside its barrier frame» arms had no shape
left to fire on and are gone).

**`Thread`, `Status`, `Done`.** The pool's per-goroutine state is
`inductive Thread | running (config : Config) (boundary : Option ChoiceSite)
| aborted (msg : String)`; `MultiConfig.threads : Array Thread`. The §1.3
classification is the VIEW `Thread.status : Thread → Status` with
`inductive Status | running | parked | done (d : Done)` and `inductive Done
| normal | panicked (msg)`, proved to agree with the dispatch predicates
(`threadDone_status`, `threadRunnable_status`) and, cell by cell, with
the shape predicates (`Thread.status_parked_iff` ↔ `isBlockedConfig`,
`Thread.status_done_normal_iff` ↔ `Config.isTerminal`; audit fix R5).
`Status`/`Done`/`Thread.status` have NO in-repo consumer yet — the
consumer is iris-lean; here they are a definition plus its agreement
theorems, and the pool dispatches on `threadDone`/`threadRunnable`. Deviation from the plan
text (`threads : Array Status` with `parked (p : Park)` and `done` STORED)
— reasons: (i) the consumer's `Expr` is `Config` (§1.14: `StepE` per
thread, `to_val ⟨.next, []⟩ = some ()`, and under the LangD widening «a
parked goroutine is REDUCIBLE (∃ partner)») — so the parked shapes must
remain configurations, and `fill K` must be defined on them; a stored
`Status.parked p`/`Status.done` would need `fill` at a status, which is
undefined at `done`. (ii) `done normal` is the shape `.next .stop`; storing
it would add a normalization invariant for no information. (iii) The
abort DOES need storage — its render needs the state at abort time and
must not be re-derived at every loop head — so the tombstone is stored,
and it is the one `done` payload. `Park` as a named type
(`Config.blocked (p : Park)` regrouping the four blocked constructors) is
representational and is OWED (§7), not done in this slice.

## 3. What C5 changed — the boundary flag (commit 2, `165822ef`)

`Config.opDone (sched : ChoiceSite) (inner : Config)` — the completion
marker WRAPPING the successor — is DELETED from `Config`. The post-op
boundary is `Thread.running`'s `boundary : Option ChoiceSite` field, and
the envelope statement of `ChoiceSite.postOp` moved to `Thread`'s
docstring verbatim (the latitude inventory's C3 entry and the `postOp`
row now point there; `ChoiceSite.postOp`'s own docstring in State.lean
points there).

**THE POST-OP BOUNDARY RULE, one definition.** The applies stop wrapping
(30 emitter sites in `applyChanOp`, `applySyncOpCore`, `tryDeliver`,
`applyAtomicOp`, `commitClause`, `resumeThread`, `spawnStep`,
`applyPairing` return bare successors). The flag is set in ONE place
(Multi.lean): `Config.afterStepFlag σ c c'` = `some .l1Sched` at a spawn
position; `c'.completedFlag` (= `some .postOp` unless `c'` is parked or
panicking) when `c.registryCommits σ` — a chan/sync/atomic apply
position, or a select apply position whose clauses are ready
(`selectCommits`: the apply's own `evalClauses`/`readyClauses` on the
pre-state, so a default-take or a park is NOT a completion — boundary-set
note §B1); `none` otherwise. `Thread.afterStep σ c c' := .running c'
(c.afterStepFlag σ c')` is used by `stepThread` on the `stepFn`, select
interception, `.commit` and spawn paths; `Thread.completed c'` by the wake
path and the pairing issuer (their completion is known directly). The
relation `StepM.thread`/`pickCommit`/`wake` conclude with the same
functions, so `stepMulti_sound`/`stepM_complete` hold with the flag as a
DEFINED quantity, never a guessed one. Why this shape rather than the
emitters returning the flag: `stepFn`'s 3-tuple is pinned across the
whole correspondence kit (the B8 lesson), and the ONLY emitter whose
completion is not a function of (pre-configuration, successor shape) —
the select (a default-take and a commit can both be `.exec X env k`) —
is a function of (pre-state, pre-configuration): `readyClauses` is
deterministic, so for a fixed pre-state a select apply either commits
under every stream or takes its default/parks under every stream.

**The strip is a POOL step** (G-C5's ruling — no baseline fuel shift).
`stepThread` at `.running c (some _)` clears the flag: one goroutine
step, no consumption, event `.opDoneStrip` (the name kept), relation
`StepM.strip`. `Step.opDoneStrip` LEFT the sequential relation: a `Step`
on a `Config` has no flag to clear, and the sequential driver never sees
one — `stepFn`'s `.opDone` arm is gone. `Thread.atBoundary t :=
t.boundary.isSome || t.config.atBoundary`; `Thread.boundarySite t :=
t.boundary.getD t.config.boundarySite` — the old marker's CLAMP (a
non-scheduling tag consulted L1) is gone: its stated reason, the
singleton-menu non-consumption for ARBITRARY configurations, holds at
every site since G-U's uniform rule (`Config.boundarySite_ne_postOp`
records that no configuration SHAPE consults `postOp` any more).

**The theorem restated with the op count.** `execProg_single_eq_execStmt
: execStmt fuel env σ ch prog = r → transferable r → execProg (fuel +
seqOpCount fuel σ (.exec prog env .stop) ch) env σ ch prog = r`, where
`seqOpCount` (MultiSound.lean) counts the registry-op completions along
the sequential run — each one a boundary clear the one-goroutine pool
takes and the sequential machine does not. `execProgLoop_single` is
proved by the same fuel induction as before with two new step lemmas:
`stepMulti_flagged_single` (a flagged singleton goroutine's pool step is
the clear, consuming nothing) and `stepMulti_abort_single` /
`stepFn_abort` (the abort on both drivers). The differential's driver
(`runProgramPoolIntsM`, the one `ChoiceTrace.lean`'s header names) runs
the POOL at the SAME fuel as before: the op count is a fuel shift IN THE
THEOREM, not in any baseline. VERIFIED (the plan's condition): no
baseline lane runs the sequential driver — `execStmt`/`runConfig`/
`runProgramM` have no CLI consumer (`grep`: only GoCore-internal uses and
the eval tests' `runFunctionM` family, whose per-test fuels are far from
tight); the `$pkginit` phase runs `runInitConfig` sequentially on BOTH
drivers identically (it has no registry ops to complete under the frame
barrier that could differ).

**Downstream consumers of the marker.** `raceUpdate`'s 12 `some (.opDone
_ _)` probes read the post-thread's flag (`some (.running _ (some _))`)
— the same information the marker carried, on the same steps;
`poolConsumption`, `poolThreadOblivious`, `innerVecs`, the tracer's
`poolTarget`/`poolFacts` and the CLI accountant dispatch on `Thread`;
`MultiWf` is `∀ i, ThreadWf …` (`ThreadWf bound types (.running c _) =
ConfigWf bound c ∧ itersNormalized …`, `ThreadWf _ _ (.aborted _) =
True`); `NPDRF.StepMFine` mirrors the seven `StepM` rule classes
(`thread strip abort pair pickPair pickCommit wake`), `PoolResult.done
(σ : ExecState)`, and `RacyFine` quantifies UNFLAGGED live goroutines (a
flagged one's next step is its footprint-free clear — recorded in situ;
the file is the unchanged draft scaffold otherwise); the dedup engine's
node hash salts a flagged goroutine's configuration hash with a fixed
constant (performance only; the certificate checker's `dedupNodeEqb` uses
`Thread.eqb`, proved sound).

## 4. Preservation — per-step identity on both drivers, no deviation

Old and new machines take the SAME steps on every program, stream and
fuel; the evidence (§5) is byte-identity, and the argument per item:

1. **Signals.** Every deleted rule is an arm of `signalStep` with the
   same conclusion; `stepFn`'s five signal arms' cases are the table's
   cells one for one (pass ↔ `.signal sg k'`, catch ↔ the same successor,
   refuse ↔ the same `Stop` text); `stepFrameExit` is the former
   `.next (.frame …)` and `.returning (.frame …)` arm bodies, which were
   verbatim twins. Positional `fun_cases` tags in MachineSound moved;
   the proofs are restated, never weakened.
2. **The abort.** Old: at `.panicking (first :: rest) .stop` the
   sequential driver spent one fuel on `panicAbort` → `.panicked msg`,
   then classified `.panicked` BEFORE the next fuel check; new: the
   same fuel is spent on the step that throws `.panic msg`. Same fuel,
   same outcome (`renderPanicHead`'s `none` was `.unsupported` on both
   sides and still is). Pool: old — the panicking goroutine (always
   `cur`: unwinding is private, and the `.panicking … .stop` shape is
   reached only by the goroutine's own step) took the `panicAbort` step
   to `.panicked`, `raceUpdate` folded a `.privateStep` with
   `stepAccesses (.panicking _ .stop) = []`, and the next loop head's
   `panicMsg?` ended the run; new — the same goroutine takes the
   tombstone step (`raceUpdate` folds `.aborted` → no accesses, no
   edges), and the next loop head's `panicMsg?` ends the run. The
   BUG-044 main-exit window is untouched: at a main-done pool the L5
   pick precedes any step on either side, and the abort step is the
   step it picks. The exact-fuel eval pins (`pollerMain_F` at fuel 74
   completes / 90 exhausts, unchanged) and the corpus's panic rows
   (3498 rows, zero drift) are the executable checks.
3. **Signals at `.stop`.** Unreachable from every Program driver (barrier
   frames); the corpus has no bare-statement run. Changed class:
   `execStmt` on a bare `return`/`break`/`continue` statement now refuses
   (`.internal`/`.stuck`, cause named) where it used to return
   `.returned σ`/`.broke σ`/`.continued σ` — dead generality removed, no
   Go program observes it. THIS IS A DEVIATION FROM "no deviation"
   (audit fix R4): the theorem's domain shrank — `transferable`
   (MultiSound.lean) moved from `Except Stop (ExecOutcome × Choices)`
   to `Except Stop (ExecState × Choices)`, so a bare-statement run
   ending in a signal at `.stop` was transferable and is now a refusal
   on which `execProg_single_eq_execStmt` is silent. What replaces the
   lost coverage: the two drivers agree on the shape by lemma —
   `stepFn_signal_stop` and `stepMulti_signal_stop_single` (both
   `= .error (signalRefusal sg .stop)`, MultiSound.lean) — and no
   driver reaches it (barrier seeds at `StepFn.lean` `runPkgInitM`/
   `runProgramSetupM`, `Multi.lean` `spawnStep`).
4. **The flag ≡ the marker.** Emitter by emitter: `applyChanOp` wrapped
   every proceeding send commit / recv delivery entry / close and left
   parks and panics bare — `registryCommits` is `true` at the chan apply
   and `completedFlag` is `none` exactly at a parked or panicking
   successor; the same for `applySyncOpCore` (parks, the fatal throws,
   the recoverable negative-counter panic) and `applyAtomicOp` (the
   nil-address panic); `tryDeliver` always proceeds (never parks or
   panics — `tryDeliver_ok_any`, `applyTryLock_noPanic`) and is always
   flagged; `applySelectCore` wrapped commits only (`commitClause`) and
   not the default-take or the park, and its panicking commit was bare
   — `selectCommits` is `true` iff `readyClauses ≠ []`, which is exactly
   when `applySelectCore` reaches `commitClause` (its `[]` arm is the
   default/park), and `completedFlag` clears the panicking commit; the
   pairing ISSUER was wrapped and the PARTNER not — `applyPairing`
   writes `Thread.completed` for the issuer and `.running _ none` for
   the partner; every proceeding wake was wrapped except the
   close-woken sender's panic — `Thread.completed` on `resumeThread`'s
   result; the spawn parent carried `.l1Sched` — `afterStepFlag` at a
   spawn position. The strip: one pool step in both worlds, at the same
   moment (the marker/flag is at a boundary; the reschedule consults the
   same site with the same menu). `raceUpdate` probed the marker on the
   post-configuration; it probes the flag on the post-thread — same
   truth value on every step by the previous sentence. The
   per-consumption trace's `postOp=4534` records (site, bound, stream
   value, pick, position) are identical on all 20749 compared lines
   (the count is explained once in §5) — the executable form of this
   paragraph.
5. **Representation only.** `Thread.eqb`/`Thread.eqb_sound` replace the
   marker's recursive `Config.eqbF` arm; `ThreadWf`; the engine hash.
   Certified sets are re-enumerated by the gate (zero drift); the
   13-node dedup fixture test (`Tests/GoCoreEval.lean`) still builds and
   accepts its certificate with 13 nodes and 1 member.

What did NOT move (recorded so the reviewer need not hunt): the
consumption projections `seqConsumption`/`poolConsumption` and B8's
theorem (restated over `Thread` where they mention the pool),
`Choices.consumeAt` (G-U), the boundary set and every scheduling site,
the detector's footprint table, `Obs`/`Terminal`/`Refusal`, the frontend,
the wire, the decoder, every baseline.

## 5. Evidence (all in `docs/evidence/2026-09-05_c-arc-b4/`)

- BEFORE snapshot: `main` @ `076f5eec` binary (`golean-before`),
  `scripts/choice-trace-corpus --dump --jobs 6` over the whole executable
  corpus (3459 rows exported, 37 frontend refusals, 2 rows EXCLUDED as in
  every trace since the A-series — `excluded.tsv`): 20748 traced (row,
  stream) lines PLUS one tracer ERROR row (`arrays/materialization-budget/
  over-budget`: the BUG-078 decode refusal, «native lowering: array
  type…», which the tracer cannot run and reports as ERROR — R10; its
  one status line is compared like any other) = 20749 compared lines in
  every `*-diff.txt` («IDENTICAL on 20749 (row, stream) lines» is the
  comparison script's own wording for that total — audit fix R2: the
  two figures were used interchangeably before); 23115 consumption records, per-site `l1Sched=9443
  appendSpill=4868 postOp=4534 backEdge=2404 mapIter=1307 l5ExitWindow=325
  tryLock=101 nilValueMethodText=84 l2Entry=24 l4Waiter=22 l2Arrival=3`, 0
  menu-invariant violations, 0 self-check alarms (`before-summary.txt`).
  PRE-EXISTING on `main` (not this lane's): the tracer reports 6
  driver-agreement MISMATCHES, all on ONE row,
  `builtins/float-bits/roundtrip-payloads` (every stream: «engine/
  enumerator observation mismatch») — a tracer-vs-engine observation
  comparison finding on the float-bits row that predates this branch;
  reported to the coordinator (§7), not touched here.
- Commit 1 (`40fd1903`): trace `c1-summary.txt`; per-consumption dump
  byte-identical to BEFORE (23115 records, `c1-diff.txt`); status +
  obsHash identical on all 20749 compared lines; the same 6
  pre-existing tracer mismatches. Gate: `scripts/capped scripts/ci --diff`
  at `40fd1903` reported RESULT: FAIL (`transcripts/gate-c1-FAIL.txt`) —
  the differential itself at ZERO drift (3498/3498 rows match
  `baselines/native-full.tsv`, negative 394/394; eval tests 153 ok) and
  ONE failing step: «core build has GoLean/ warnings» — 13
  `unusedSimpArgs` warnings from a `set_option … in` that commit 1 left
  attached to a NEW lemma instead of `stepFn_consumption_none` (fixed in
  commit 2; the ci gate treats GoLean/ warnings as failures because
  they corrupt the runner's JSON channel). The transcript's `row: FAIL …
  TIMED OUT after 1s` lines are the lane-validation SELF-TESTS T1–T3
  (they provoke a timeout and check the cause is named; each is `ok`),
  not a finding — the same lines appear in the passing commit-2 run.
  Recorded as a red gate with its cause, not hidden.
- Commit 2 (`165822ef`): gate `transcripts/gate-c2.txt` and trace
  `c2-summary.txt`/`c2-diff.txt` — see §9 for the tallies.

## 6. What the consumer interface gains (plan §1.3 / §1.5 / §1.14)

- `Config` is 10 constructors; NO k-less configuration (the `hdrain`
  obstacle to `Language.Context.primStep_fill` is removed at its cause:
  `.panicking chain .stop` is a stuck terminal, `fill K` of it is the
  panic still unwinding through `K`); NO annotation to look through
  (`opDoneInner`, `Config.itersNormalized_opDone`, `Config.locSup_opDone`
  are gone).
- Non-local control is ONE mode with a TABLE: `fill`-respecting by
  construction (a signal at `k ++ K` strips `k`'s glue exactly as at
  `k`); `goto` (FR-11/FR-20), if lowered, has a signal to lower to.
- `Step` is 108 rules; `StepM` seven rule classes, each a pool concept
  (`strip`, `abort` included) — nothing sequential pretends to be a pool
  concern or vice versa.
- `to_val ⟨.next, .stop⟩ = some ()` is the ONE terminal (`Config.isTerminal`,
  `Config.terminal`), and it is relation-terminal: `step_terminal_elim :
  ¬ Step (.next .stop) σ c' σ'` (MachineSound.lean, beside
  `step_abort_elim`/`step_signal_stop_elim`) is the `val_stuck`
  obligation discharged (audit fix R6); `Config.abort?` names the crash;
  `Thread.status` is the value/parked/done classification the professor
  asked for — a definition with its agreement theorems, no in-repo
  consumer yet (the consumer is iris-lean).
- `execProg_single_eq_execStmt` with `seqOpCount`: the sequential
  refinement into the pool is exact and its cost is a defined function.
- `Thread` is what §1.10's `Pool` needs; `Status`/`Done` are §1.3's names
  (definitions + agreement theorems; consumed by nothing in this repo).

## 7. Owed / deviations, collected

1. **`Park` as a type** (`Config.blocked (p : Park)` regrouping the four
   blocked constructors; plan §1.3 lists `Park`) — OWED. Representational
   (the consumer needs parked shapes as configurations either way, §2);
   ~150 mechanical pattern sites across 14 files, deferred to keep this
   slice's diff to the Signal/Status/opDone surface and to limit
   conflicts with the parallel `c-arc-c2` lane. Its `wakeReady`/
   `resumeThread : ExecState → Park → …` typing is the gain.
2. **`Status` stored vs. viewed** — decided VIEW here (§2, reasons i–iii);
   C3 (`Config := Mode × Cont`) should revisit whether `Thread.running`'s
   configuration-plus-flag becomes a structure with the mode.
3. **The frame-exit twins** stay 8 relation rules (4 `.next`, 4 `.signal
   .ret`), the executable shares `stepFrameExit`; a `FrameEntry`-indexed
   rule family (one rule, two entries) is possible at C3 once `Config`
   is a structure — recorded, not done.
4. **`ExecOutcome` deleted** (A8's B4 deferral): `execStmt` returns the
   final state; the `.returned/.broke/.continued` classes are refusals.
   A downstream statement that quantified them has no shape left (none
   did: `execStmt` had no CLI consumer). The theorem-domain shrink this
   implies for `transferable`/`execProg_single_eq_execStmt` is recorded
   in §4.3 with the two driver-agreement lemmas that cover the lost
   class (`stepFn_signal_stop`, `stepMulti_signal_stop_single`; audit
   fix R4).
5. **The clamp of `Config.boundarySite`** is gone (§3); the `Thread`
   docstring records why.
6. **Pre-existing tracer finding — DIAGNOSED AND FIXED in the audit fix
   round (2026-09-05).** `builtins/float-bits/roundtrip-payloads`
   engine/enumerator observation mismatch on `main`, 6 streams (§5).
   The pre-merge audit classified it TRACER TOOLING: `ChoiceTrace.lean`
   `traceStream` compared the engine's `RunResult` observation (a
   `Stop` paired with the output printed before it — two `println`s
   precede the BUG-094 refusal on that row) against an enumerator
   refusal rendered with an EMPTY output field, so only status +
   message were compared — and a genuine output divergence between the
   drivers on ANY refusal path was invisible (fail-open). Fix
   ([AGENT], this lane's fix round): `CLI.enumPoolRun`/`enumRunProgram`
   return `Except (Stop × GoString) …`, pairing every refusal with the
   pre-step fold exactly as `execProgLoopOut` does; the tracer compares
   the whole observation on both paths; `probeSite` (the only other
   consumer) destructures the pair. Verified by the whole-corpus trace
   at the fix (`fix-summary.txt`/`fix-diff.txt`): mismatches 6 → 0, the
   per-consumption dump byte-identical to c2, every other results line
   identical; the six lines' `obsHash` moved because the recorded
   enumerator observation now carries the prefix (= the engine's).
   Rowed at detection (TODO.md, the C-arc section) per the [USER]
   2026-09-03 direction; lesson recorded
   in `docs/operational-lessons.md` and the tracer's header. Also listed
   here (R10): the tracer's one ERROR row, `arrays/materialization-
   budget/over-budget` (BUG-078 decode refusal — the tracer cannot run
   the row; not a mismatch, not this lane's), present identically on
   every trace in §5.
7. **A11** (`sortSlice` deletion) and the A4/A8 owed items are untouched
   here, as recorded in the arc plan.

## 8. Records touched

`GoLean/GoCore/{Machine,StepFn,State,StateWf,MachineSound,MachineEqb,
Multi,MultiSound,MultiStreams,MultiWfSound,EnumSpec,EnumDedupCheck,
EnumDedupSound,NPDRF,Race}.lean`, `GoLean/{CLI,ChoiceTrace,EnumDedup}.lean`,
`Tests/GoCoreEval.lean` (pool seeds only); records: this note, the
evidence dir, `docs/2026-09-03_design-hygiene-arc.md` (step (iv) B4 and
(v) C5 status, landing record), `docs/2026-09-04_reasoning-surface-plan.md`
(§5.4 G-C5 → LANDED, §5.1 table), `docs/2026-09-03_grumpy-professor-review.md`
(B4/C5 LANDED lines), `docs/2026-08-11_latitude-inventory.md` (C3 entry +
the `postOp` row point at `Thread`), `TODO.md` (B4/C5 items). Historical
logs keep their period wording.

## 9. Landing record

Lane `c-arc-b4` off `main` @ `076f5eec`, rebased onto `426af905` (a
records-only advance; the GoLean tree is identical) — the code commits'
SHAs cited here and in the evidence are the REBASED ones: `40fd1903` (B4
control half), `165822ef` (B4 terminals + C5), then the records commit
(the branch tip). The gate transcripts were recorded at the pre-rebase
commits, whose `GoLean/`, `Tests/`, `Corpus/`, `baselines/`, `scripts/`,
`tools/` trees are byte-identical to the rebased ones (`git diff` empty
— the README says which SHA ran which gate). Gates: see §5 and the evidence README's per-commit
table. **Audit fix round (2026-09-05, after the pre-merge audit's
FIX-FIRST verdict — records + three small lemma additions + the tracer
fix; R1–R7, R10 and the tracer finding; every judgement [AGENT]):** the
machine, `Step`, `StepM` and every driver are unchanged except (i)
`signalRefusal`'s four named statement-frame arms (R7 — unreachable
from `stepFn`, text-only), (ii) the lemmas `step_terminal_elim` (R6),
`Thread.status_parked_iff`/`_done_normal_iff` (R5),
`stepFn_signal_stop`/`stepMulti_signal_stop_single` (R4), and (iii) the
enumerator-driver error type (`Stop × GoString`, tracer fix — CLI
tooling, not the trusted surface). Gate and tracer re-run: the evidence
README's fix-round row. No baseline, corpus, frontend, decoder or wire change; no new
`ChoiceSite`; no `sorry`/`axiom`/`native_decide`; no `partial` in
GoCore. Branch-complete; the audit ask is the coordinator's to pose;
merge/push are the [USER]'s.
