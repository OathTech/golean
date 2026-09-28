# Pre-merge adversarial audit — lane `core/step-label-0928` (window row 2a, the step-label reshape)

[AGENT auditor] 2026-09-28, under the [USER]'s every-merge-audited rule (relayed by the [AGENT] coordinator). The candidate is
`61bdc65d` (code `e61b4212` + records commit), branched from `main` @ `84f0a9e4`. It lands later, combined with packet B's
proofs; this audit covers the reshape alone, so that defects surface before B builds on it. Read-only on the candidate and on
`main`: nothing edited there, nothing merged, nothing pushed. Worktree `.claude/worktrees/audit-step-label` (branch
`review/step-label-0928`); comparison binary built at `84f0a9e4` in `.claude/worktrees/audit-step-label-main`. Evidence:
`docs/evidence/2026-09-28_step-label-audit/`.

## Verdict: MERGE-CLEAN (for the reshape half of the combined candidate)

I found no semantic defect. Behaviour is unchanged, which I checked with my own comparison against main's binary using only
the product CLI, not the lane's tracer. Pick records are emitted by the consulting sites and match the tape exactly. The
output channel equals the old re-derivation. No theorem was removed or given a new hypothesis. `ExecutionStatement.lean`
states the same claims as packet A's version. The one change in strength is in `replay_coverage_stmt`, which is now
stronger, and it is still expected true (§6). The gate is red on exactly the 5a pair, as expected. There are two LOW
findings and one NIT. I recommend fixing them before or inside packet B; none blocks. The combined candidate still has to
be rebased onto the current `main` and re-gated (F4).

## Findings

| # | Severity | Finding | Witness | Recommendation |
|---|---|---|---|---|
| F1 | LOW | `stepThread_privateStep_label` (BridgeSet row 34, core-audit-required) leaves `ch₁` and `ps₁` existentially FREE. It concludes `∃ c ch₁ ps₁ c' l, … stepFn ctx s c ch₁ = .ok (c', s', ch', l) ∧ ev.label = ⟨l.trace, ps₁ ++ l.picks, l.out⟩`. That does not say `ps₁` are the pool's own arrival-plan records, and it does not tie `ch₁` to `ch`. As stated it is consistent with double accounting: any prefix is admitted. Row 34's comment and the design note §3 («picks = the pool's own arrival-plan picks FOLLOWED by the step's») claim more than the theorem states. The logic team's §3 asked for «the sequential-to-pool projections, including attribution and terminal events». The spawn's attribution is cited only as `StepE.spawn`'s constructor label, with no stepThread-level projection theorem. Mitigation: the exact form already exists as `stepThread_stepFn_path` (`MultiStreams.lean:235`, `ps₁ = []` on the cell path) and `stepThread_single`, and B's single-goroutine statements can use those. | `MultiSound.lean:1707–1712`. The proof has the facts in context: `arrivalPlan … = .ok (none, ch₁, ps₁)`, bound by `rename_i … ch₁ ps₁ …` at `:1729`. | Strengthen the conclusion with `arrivalPlan ctx s threads i c ch = .ok (none, ch₁, ps₁) ∧ selectApplyPlan c = none`, or pin `stepThread_stepFn_path` beside it. Either is a theorem-only change, inside packet B's boundary («NO change to `stepFn`, `Step`, … `StepLabel`, `StepEvent`»). |
| F2 | LOW (records/brief) | Handoff §4 flag 1 frames `replay_coverage_stmt`'s premise-freedom as a question about `appendSpill` only. The general answer is already proved. `stepFn_consumption_some` (`MachineSound.lean:6219`) gives, for EVERY `.ok` step at a consulting configuration, `ch₀' = (consumeAt site b ch₀).2`, plus the same step with the same label under every tape with the same pick. So a tape-restoring panic after a real pop is impossible at every `seqConsumption` site, not just at `appendSpill`. `tryLock` is the second site with a post-consult tail that can panic (`storeLoc`, `tryDeliver`); it is pick-independent by `applyTryLock`'s pre-commit discipline. What B actually needs, and what does NOT exist yet, is the agreement lemma: `l.picks = []` when `seqConsumption = none`, and `l.picks = PickRecord.ofPick site b pick` when it is `some (site, b)`. With that lemma, coverage follows from `consumption_some`. | `MachineSound.lean:6219–6226` (statement read at the tip); `Machine.lean:4747–4800` (`applyTryLock`) | Hand this route to B in the §3 refresh. |
| F3 | NIT | Stale line references in the re-stated `ExecutionStatement.lean` docstrings (BridgeSet's refs ARE refreshed, all 34 verified): `Machine.lean:3203` (now `abortConsult` at `:3221`), `:3908`/`:3912` (`abortMsg` `:3926`, `abortLeftover` `:3937`), `:6157` (`Steps` `:6220`), `State.lean:475`, `StateWf.lean:8106` (`:8107`), `StepFn.lean:1012` (`:1018`), `:1042` (`:1048`), `:1118`, `:368`, `:850`. There is also a stale comment in `applyStmtOpCore.plan`'s print arm (`Machine.lean:1557–1558`, «The bytes are the pool layer's event (`printOut?`)»): since the reshape the step's own `stmtOpOut` carries the bytes. | `grep -on '\`[A-Za-z]*\.lean:[0-9]*\`' GoLean/GoCore/ExecutionStatement.lean` | Refresh them when B next touches the file. |
| F4 | INFO (process) | The candidate branches from `84f0a9e4`. `main` is now `fd1135ff`, a records-only commit that touches only `docs/2026-09-27_stray-panic-refusal.md`, which the lane never touches. `--ff-only` will refuse, so protocol step 5 applies: rebase (conflict-free, disjoint files), re-gate, re-ask. | `git merge-base main core/step-label-0928` = `84f0a9e4` | At the combined landing. |
| F5 | INFO | Two consultations sit outside every `StepLabel`, both documented. The driver's `l5ExitWindow` draw (`Multi.lean:1898`, `:1947`) falls between steps. The sequential abort's `repanicCollapse` draw (`abortConsult`) raises the terminal, and `Finish`'s `rec` accounts for it. The pool-level replay coverage (after the window) must treat `l5ExitWindow` separately. | `ChoiceTrace.lean` `isEventRecorded` | None now. |

## What I checked (the brief's eight attacks)

**1. No behaviour change.** Evidence: `main-vs-lane-summary.txt`, `compare-main-vs-lane.py`, `sampled-ids.txt`.
- I built main's binary at `84f0a9e4` myself (sha256 `c9f5822a…`, equal to the lane's evidence) and the lane's at the tip
  (`07612144…`).
- I exported my own wires with the gate's frontend invocation and ran both binaries under identical argv. For each run I
  compared stdout, stderr and exit code byte for byte.
- Sample: 1804 distinct ids, all covered. The strata overlap:
  - unseq 72, goroutine 228, select 108, chan 390, panic 468, recover 241, map 244, range 121, init 136, sync 215,
    trylock 20, print 168, append 76, defer 147, atomic 58.
  - All 374 non-slow membership, confluent and racy rows were enumerated with their lane parameters. Racy rows exercise
    the race detector's fold over `ev.trace`, which is the memory-access channel.
- Runs: 7524 `native-json-run` runs (5 streams per strict row) and 374 enumerations. **0 DIFF, 0 TIMEOUT.**
- The certified slow-tier row `google-search` was re-enumerated on both binaries with the certificate's own argv. The wire
  hash equals the claim's. The output is byte-identical, and the enumerator statistics are identical too (nodes 6193933,
  edges 6565663, dedupHits 371731). The output equals the certified six-member set (`google-search-reenumeration.txt`).
  So the 5a red is a pure provenance refresh: the claim and the observations would be unchanged.
- The lane's pre-existing ERROR row `arrays/materialization-budget/over-budget` is benign. I reproduced it on both
  binaries: it is a decode-time refusal (BUG-078's materialization budget: 2097152 > 65536 elements) raised before any
  step. Its message embeds the input path, which is why the two output directories differ. It is baselined as
  `FAIL … lean-observation`.

**2. Pick records are exact.**
- Every `consumeAt`/`consumeAtE` in the executable core is accounted for:
  - `unseqNext`, `unseqPanic` and `mapIter` in `stepFn`.
  - `nilValueMethodText` in `enterFramePick(V)`, at all 6 `stepFn` entry sites and at `spawnStep`.
  - `appendSpill` in `applyStmtOp.plan`, `tryLock` in `applySyncOp`, `l2Entry` in `applySelect`.
  - `l2Arrival`, `l4Waiter`, `repanicCollapse` and the boundary site in the pool.
  - The only remaining raw `consumeAt` uses are `abortConsult`, the driver's `l5ExitWindow` and the `PoolTrace` tooling (F5).
- Every helper's records reach the label on every return path. On each `.ok` path the records ride with the stream they
  advanced.
- The asymmetry is right:
  - `deliverS`/`deliverV` deliver a panic under the PRE-apply `choices`, so the stream advance and the record are dropped
    together.
  - The frame-entry panic path delivers under `ch'`, the post-pop stream, so the advance is kept and so is the record
    (`panicPicks`). `spawnStep`'s panic arm also returns `ch'` together with its `ps`.
  - The relation matches on both sides: the entry rules pass `ps` as `panicPicks`, while the stmt, sync and select apply
    rules use the default `[]`. `applySelect`'s defensive `.inr` arm keeps both the pick and its record.
- The rules that choose an index state `PickRecord.ofPick`. `mapIterStop`'s explicit record has bound
  `cands.size + 1 ≥ 2` (`cands.size ≠ 0`).
- Probe (`probes.txt`), TryLock on an unlocked mutex:
  - tape `[3, 9]` → record `⟨tryLock, 2, 1⟩` (modulo selection), residual `[9]`;
  - tape `[]` → `⟨tryLock, 2, 0⟩` (the empty-tape default is recorded as 0, which is what `consumeAtE` returns);
  - on a locked mutex (bound 1) → no record and no pop.

**3. Output.**
- `out = stmtOpOut op args`: the same `renderPrint` the apply validates through. A print apply never panics (render errors
  are refusals), so `[]` on the panic path loses nothing.
- The pool takes `l.out` wholesale. `printOut?_toList` proves it equal to the old `(printOut? c).toList`. `printOut?` is
  `none` off apply positions, and there `stepFn`'s `out` is `[]`.
- `initPrintRefusal?`'s text is byte-unchanged; only its docstring changed.
- The whole-sample identity above covers every print row (168).

**4. Silent projection and the pool.**
- `StepLabel.fold_silent` is true and meaningful: removing a pure label leaves every channel's fold unchanged.
- The label is a field, and the number of events per pool step is unchanged.
- The only reader of `StepEvent.picks` is the tracer's cross-check (`ChoiceTrace.lean`). The enumerators, `EnumDedup*`,
  the CLI drivers and the certifier read `ev.out`, or `ev.trace` through `raceUpdate`, never the picks. The disclosed
  widening therefore cannot move an observation, and the google-search check above confirms it.
- The projection theorem is weaker than its description (F1).

**5. The relations.**
- `StepE` is over `StepLabel`. `StepM` and `StepMFine` keep `AccessTrace` via `l.trace`.
- Theorem names: none removed, 6 added (`theorem-inventory.txt`).
- Statements: 105 changed. Every one is a label retyping (`AccessTrace` → `StepLabel`) or has more components. None gained
  a hypothesis: I compared the premise and arrow counts of every changed statement.
- `stepFn_sound`/`step_complete` are the same statements over `tr : StepLabel`, which makes them stronger.
- Core audit: 55 required theorems, classical trio only. No escape hatch was added.

**6. Packet A's contract, re-stated.**
- The same claims, relabelled.
- `replays : List PickRecord → Choices → Choices → Prop` redraws each record with the SAME `consumeAtE r.site r.bound`
  and requires it to return `(r.pick, mid, [r])`. That is faithful replay by site, bound and value. Modulo selection is
  covered because it compares the resulting pick, not the raw entry. The empty-tape default works whenever `r.pick = 0`.
  Bound ≤ 1 is never recorded and never pops.
- `replay_coverage_stmt` is now STRONGER than packet A's version. It quantifies over the records the step KEPT, so a step
  that dropped a record after a real pop would be a counterexample. It is still expected true:
  `stepFn_consumption_some` rules out such a step (F2).
- `appendTargetLocal`: the proof of `consumption_some` does not use it (`_hloc`), so the premise-free statement stands.
- BridgeSet: I checked all 34 line references against the tip. Two mutations in scratch (row 34's pick order; dropping
  row 15's `× List PickRecord`) each fail to elaborate (`Type mismatch`). The unmutated file elaborates.

**7. Records.**
- Changelog label row: the shapes, «still 128 rules» (counted on both sides) and the before/after line numbers are
  accurate.
- The design note §4 states the non-interleaving limitation.
- Handoff §3: I checked all 55 file:line references mechanically and every one resolves to the named declaration.

**8. Gate.** Under the box-wide lock, `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at `61bdc65d` exited 1 after
801 s (`gate-tail.txt`).
- Red on exactly the 5a pair:
  - `certificate provenance` is STALE (changed dependency `GoLean/ChoiceTrace.lean`, among the compiled inputs);
  - the baseline line `imported-goose/channel/google-search PASS → FAIL` (the cached certified record judged stale).
- `cases=3768 pass=3531 fail=237`; no other row moved; negative 394 matched; eval tests 295 ok; core build warning-free.
- Core audit (55), unseq scheduler, unseq wire, wire boundary, method identity, frontend pins (the raft twin), the
  evidence-size check and the AGENTS alias all passed.

## What I could not verify

- **The whole corpus under every stream.** My identity run covers 1804 of 3768 ids under 5 fixed streams, plus the full
  enumerations of the non-slow enumerating rows. The whole-corpus claim (26 313 consumption records) rests on the lane's
  tracer dump, which comes from tooling the lane itself modified.
- **Standalone per-access traces.** They are not observable through the product CLI. I covered the trace channel through
  the racy lane (detector fold) and through the gate.
- **Truth of `replay_coverage_stmt`.** I argued it, but it is packet B's to prove, and the agreement lemma in F2 is owed.
- **A full `--slow` re-certification of `google-search`.** I did not install a record. My re-enumeration only shows that
  the claim and the observations are unchanged.
