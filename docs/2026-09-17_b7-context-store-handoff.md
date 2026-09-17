# B7 fixed context / mutable store — lane handoff (2026-09-17)

[AGENT] worker, lane `core/b7-context-store-0917` (branch of the same name, base
main `7f1c1fe7`), 2026-09-17. The brief is the charter
`docs/2026-09-16_b7-context-store-charter.md` with its §9 decisions ALL RULED
([USER] Mike, 2026-09-16, verbatim, relayed by the [AGENT] coordinator — cite as
relayed: «Yes, let's go ahead with the D1-8 rulings as recommended (aside from
D3)»; D3 ruled separately the same day: PARK; record
`docs/2026-08-31_qrow-rulings.md`, «The B7 charter rulings record (2026-09-16)»).
Dispatch authority: [USER] 2026-09-17, verbatim, relayed: «Great, land it, then
launch B7». Evidence: `docs/evidence/2026-09-17_b7-context-store/README.md` (gate
lines, census, probe, warm measurement). Slice entries:
`docs/hygiene-slice-log.md` (the B7 section at its tail); the landing-record row:
`docs/2026-09-03_design-hygiene-arc.md`.

**Rebase map + fix round (2026-09-17, [AGENT] fix-round worker).** The branch
was rebased onto main `5955e55f` (one records-only commit of drift; clean):
the SHAs named below are the PRE-rebase ones and map to `fc1aa228 → 66fe1092`
(S0 records), `2500b434 → 73ad798d` (the runtime commit), `b1b25945 → a7fd0542`
(this handoff's first version); the Lean tree is byte-identical across the
rebase (`git diff 2500b434 73ad798d -- GoLean Tests lakefile.toml
lake-manifest.json lean-toolchain` empty). The fix round then landed the §8
rulings ([USER] Mike, 2026-09-17, verbatim, relayed by the [AGENT] coordinator —
cite as relayed: «We should delete the vacuous conjunct right? that's just a strict improvement. The rewordings sound fine. Agree with the audit, go ahead and launch (after the rulings if relevant)»): runtime commit
`1fafc9f2` (the pool-side `itersNormalized` conjunct and the predicate family
deleted — §4 «Fix round», §8), gated at its tree (§2, fix-round row), followed
by the records commit this text is part of.

**One line.** `ExecState` (five program tables beside the heap) is gone: the
machine is `ProgramCtx` (the decoded `Program`, whole, read by every transition
and written by none) × `Store` (the heap). `stepFn ctx s c ch`,
`Step ctx c s c' s'`, `StepM ctx m m'`; `StateWf` is heap-only; `MachineWf` lost
its vacuous `itersNormalized` conjunct (D6) and, in the fix round, so did the
pool's `ThreadWf`/`MultiWf` — `MultiWf m` is context-free and the predicate
family is gone (§4 «Fix round»). The 48 «the program did not
change» proof sites are gone BY TYPE (§3). NO wire change, NO semantic change,
NO theorem weakening: every coherence theorem is restated with `ctx` and
re-proved (§4); the differential gate ran at zero drift (§2).

## 1. What landed, per slice (the charter §7 table; one gated runtime commit)

The charter's slices S1–S5 were executed as WORK slices in dependency order
(a `State.lean` edit does not build without `Ops`/`Machine`, so the charter's
«explicit-target warm per slice, ONE gate after S1–S5» shape was followed
literally): each group verified by a captured-exit explicit-target build, a
snapshot ref per group (`refs/snapshots/b7/s0 … s5`), then the one full gate.

| slice | files | what changed | verification |
|---|---|---|---|
| S0 records | `docs/evidence/2026-09-17_b7-context-store/` | census BEFORE (38 + 6 + 4 = 48 statement sites), reverse-import map, `fun_cases` tag probe (162 arms, fingerprinted), the MEASURED warm (§5) | records commit `fc1aa228` |
| S1 records | NEW `GoLean/GoCore/ProgramCtx.lean` (D2 (b): `structure ProgramCtx where program : Program` + the five projections + `globals`; `ProgramCtx.ofTables` — the hand-built entry with the OLD `ExecState` defaults, every table `#[]`), NEW `GoLean/GoCore/Store.lean` (heap-only `Store`, `nextAddr`/`allocCell`/`alloc`/`updateCell`, the four payload readers/writers — the snapshot's file, refusal texts byte-preserved), `State.lean` (`ExecState` + its helpers removed; docstrings), `StateWf.lean` (§3), `StateEqb.lean` untouched (no `ExecState`), `MachineEqb.lean` (`Store.eqb` = the heap comparison; the five-table walk gone) | `lake build GoLean.GoCore.Store GoLean.GoCore.ProgramCtx` EXIT=0; StateWf EXIT=0 (16 s) |
| S2 sequential machine | `Ops.lean` (43 context readers lose the state parameter, 2 unused-`_state` helpers lose theirs, 5 heap operations take `ctx` + `Store`), `Machine.lean` (`variable (ctx : ProgramCtx)`; 10 context-only helpers — the panic-text renderers, `abortMsg`/`abortRefusal`, `nilValueMethodWidth`/`entryPanicText`, `consumesNilValueMethod` — lose the store; `Step ctx`, `Steps ctx`), `StepFn.lean` (`stepFn ctx`; `runProgramSetupM` BUILDS the run's one context and RETURNS it as the first component; `runFunctionWithContextM` builds it from the bare tables via `ofTables`), `MachineSound.lean`, `UnseqSound.lean` (theorems: implicit `{ctx}`) | Ops 5 s, Machine 4 s, StepFn 1 s, MachineSound + UnseqSound 62 s — all EXIT=0, 0 warnings; the S2 tag probe: 162 arms, tags/order/fingerprints IDENTICAL, hypotheses +1 each (§6) |
| S3 pool, traces, detector | `Race.lean` (`dispatchAccesses`/`deferEntryAccesses` context-only; the four footprint functions `ctx` + store), `Multi.lean` (`shared : Store` — D4 (a); `MultiWf ctx m`), `MultiSound`, `MultiWfSound` (§3), `MultiStreams`, `NPDRF` (`StepMFine`/`StepsM`/`StepsMFine`/`ReachesM`/`ReachesMFine`/`RacyFine`/`NPDRFReduction` take `ctx`), `Trace` (`Trace ctx`), `PoolTrace` (`Run ctx`, `front ctx`), `ProgramTrace` (PROGRAM-level: `ProgramRun` binds the setup's context, no parameter), `AbortObservation`, `StringPanic`, `EnumSpec`, `EnumDedupCheck`, `EnumDedupSound` | `lake build GoLean.GoCore` EXIT=0 (33 jobs, 0 warnings); the trace/observer trio EXIT=0 |
| S4 enumerator + CLI | `GoLean/EnumDedup.lean` (`buildCert ctx …`), `GoLean/CLI.lean` (`EnumProgram.ctx` built by `enumSetup` as `⟨program⟩`; `enumPoolRun`/`enumInitRun`/`stepNeeds`/`stepNeedsSeq` take `pctx`; the DFS uses `ctx.ep.ctx`), `GoLean/ChoiceTrace.lean` (validator functions take `ctx`; `traceProgram` uses `ep.ctx`); `NativeToIR.lean` UNTOUCHED (wire-neutral by construction — §7) | default `lake build` (lib + `golean` exe) EXIT=0 under the box lock |
| S5 tests + the gate | `Tests/GoCoreEval.lean` (13 hand-built states → `ProgramCtx.ofTables` fixtures with the old defaults; `emptyCtx`; store-taking calls get `{}`), `Tests/GoCoreContract.lean` (∀-state facts take `{ctx}` implicitly; concrete runs use `exampleCtx`/`emptyCtx`), `Tests/MethodIdentity.lean`, `Tests/PanicRendering.lean`, `Tests/StringPanicMembers.lean`; `Admission*`, `Declaration*`, `UnseqScheduler*`, `GoCoreAudit` unchanged (Program-level entries) | every `Tests.*` module EXIT=0 (30 s); then THE GATE (§2) |

Net runtime delta at the gate tip: 32 files, +3,058/−2,862 (`git diff --stat`;
`StateWf` 1,130 lines touched, `MachineSound` 802, `Machine` 740, `Ops` 393).

## 2. Gate lines (captured exit codes; the tails are in the evidence README)

| run | command | exit | wall s | SHA / tree | result |
|---|---|---|---|---|---|
| THE gate | `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box lock (`LEAN_NUM_THREADS=4` by the cap) | **1** | 1068 | `fc1aa228` + the dirty runtime tree, committed UNCHANGED as `2500b434` (`git diff --stat` at commit time = the gated tree; the docs were not part of the gated tree and are records) | **3676 cases: 3427 PASS / 249 expected FAIL** (Stage B's tally exactly); 394 negatives matched; `eval tests` 211 ok / 0 fail; `core build (warning-free)` ok; `core totality audit` ok (every `GoLean/` module incl. the new `Store`/`ProgramCtx`, classical trio only); `frontend pins (… twin wire = pinned bytes)` ok; `unseq scheduler (Stage B)` ok; `wire boundary` ok; every other step ok. RED: `certificate provenance` (reconciler C9 HIGH: «STALE certification: changed dependency build/files/GoLean/CLI.lean») and `baseline diff (DRIFT)` with the SINGLE drift line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` — the one cached certified row, judged stale because its record's compiled inputs changed. ZERO other drift. Tail: `docs/evidence/2026-09-17_b7-context-store/gate-tail.txt`. |
| THE gate, FIX ROUND | the same command under the box lock | **1** | 934 | `a7fd0542` + the dirty runtime tree (the fix round's four core files), committed UNCHANGED as `1fafc9f2` | **3676 cases: 3427 PASS / 249 expected FAIL** (identical tally); 394 negatives matched; `eval tests` 211 ok / 0 fail; `core build (warning-free)` ok; `core totality audit` ok; every other step ok. RED: exactly the same two 5a-class items — `certificate provenance` (C9 HIGH: «STALE certification: changed dependency build/files/GoLean/CLI.lean») and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]`. ZERO other drift. Tail: `docs/evidence/2026-09-17_b7-context-store/gate-tail-fixround.txt`. |
| choice trace, FIX ROUND | the same tracer command for the SAME main binary the lane used (`.tmp/golean-main`, sha256 `155df5c3…`, re-run) and the fix-round binary (the gate's `golean`, sha256 `1ea8f2ac…`), concurrently; sorted dumps `cmp`'d three ways | **0 (cmp)**: BYTE-IDENTICAL — 23,679 records on all three sides (main now / fix / the lane's `trace-before.tsv`), one sha256 `5f901024…58b5a`; validator summaries identical (0/0/0; the one known ERROR row); each run EXIT=1 for the same pre-existing «FINDINGS present» listing. `choice-trace-summary-fixround.txt` | 661 + 646 | main `7f1c1fe7` vs `1fafc9f2` | byte-identical after the fix round |
| choice trace | `scripts/choice-trace-corpus --dump --jobs 6 …` with main's binary (a `git archive 7f1c1fe7` cold-built under `.tmp/before/`) and with `2500b434`'s, the two wave-3 exclusions, `cmp` of the sorted dumps | **0 (cmp)**: BYTE-IDENTICAL — 23,679 consumption records from 21,834 (row, stream) lines over 3,639 traced rows (34 frontend refusals, 2 excluded), sha256 `5f901024…58b5a` on both sides; validator summaries identical (0 menu-invariant violations, 0 self-check alarms, 0 driver-agreement mismatches; the one ERROR row is the known frontend refusal `arrays/materialization-budget/over-budget`); each tracer run EXIT=1 (643 s) for the SAME pre-existing «FINDINGS present» depth listing. `choice-trace-summary.txt` | 643 + 643 | main `7f1c1fe7` vs `2500b434` | the whole-corpus choice trace is byte-identical (D5 (a)'s second leg) |

Expected non-drift red, as at Stage B and as the charter §5 item 1 names it:
`certificate provenance` STALE because compiled semantic inputs changed
(`GoLean/CLI.lean` and the core compile into the binary), and in consequence
the ONE cached certified row (`imported-goose/channel/google-search`) judged
stale — the train's step 5a (`ci --slow`, install the reviewed candidate), NOT a
finding, NOT a re-pin. Anything else red would have stopped the slice; nothing
else is red.

## 3. The hypothesis census — BEFORE / AFTER (the payoff, counted)

Recorded greps (the evidence README has the commands):

| site class | BEFORE (`7f1c1fe7`) | AFTER (this tip) |
|---|---|---|
| `σ'.types = σ.types ∧ σ'.functions = σ.functions ∧ σ'.methods = σ.methods` conjuncts in `StateWf.lean` theorem statements | **38** (24 statement lines; 54 atoms incl. proof-internal) | **0** |
| `s'.types = s.types` conjuncts in `MultiWfSound.lean` | **6** | **0** |
| `htypes : σ₂.types = σ₁.types` hypotheses in `MachineSound.lean` | **4** (`structTagCompatible_congr`, `loadLoc_root_congr`, `normalizeValueForTy_congr`, `storeLoc_congr`) | **0** (one comment mentions the name) |
| total statement sites | **48** | **0** — gone BY TYPE |
| `SameContext` / `Extension.context` | 0 (left with the parked family, D3) | 0 |
| `ExecState` in code | 30 modules | 0 (five docstring mentions of the historical name) |
| positional `fun_cases` tags of `stepFn` moved | — | **0** (162 arms; §6) |

What replaced the equalities: nothing. A conclusion `StateWf s' ∧ …` is
stated over stores; the context is the same `ctx` on both sides of every
theorem because there is only one.

## 4. Theorem statements that changed (restatements, flagged; none weakened)

- `MachineWf σ c := StateWf σ ∧ ConfigWf σ.nextAddr c` — the third conjunct
  `Config.itersNormalized σ.types c = true` DELETED (**D6**, ruled). It was
  constantly `true` (`Config.itersNormalized_true`, kept); `step_preserves_wf`
  restated; `step_preserves_iters` RETIRED (tombstone below).
- `StateWf σ := Store.locSup σ ≤ σ.nextAddr` with `Store.locSup σ := Heap.locSup
  σ.heap` — the program-text term `funcListSup σ.functions.toList` is gone (the
  A4 debt: it was identically zero). NEW theorems carry the fact:
  `Expr.locSup_eq_zero`, `Stmt.locSup_eq_zero`, `Func.locSup_eq_zero`,
  `funcListSup_eq_zero` (+ the list/option/assignee/unseq/select-clause
  companions), proved by the functional mutual induction principles
  `Expr.locSup.mutual_induct` / `Stmt.locSup.mutual_induct`. `enterFrame_tail`
  loses its `hf₁ : Func.locSup func₁ ≤ funcListSup σ.functions.toList`
  hypothesis (the bound is the zero lemma). `StateWf.funcs_le` RETIRED;
  `StateWf.mk'` takes one bound.
- The 22 `*_shape`/`*_wf`/`*_pres` lemmas of `StateWf.lean` and the 6 of
  `MultiWfSound.lean` lose their context-equality conjuncts (`StmtOpPres σ σ' :=
  StateWf σ' ∧ σ.nextAddr ≤ σ'.nextAddr`); every consumer's destructuring
  re-indexed. No conjunct that says anything about the heap or the allocator
  moved.
- `loadLoc_root_congr`, `storeLoc_congr`, `normalizeValueForTy_congr` lose
  `htypes` (two stores under ONE context cannot disagree on the type table);
  `structTagCompatible_congr` RETIRED (it was `htypes ▸ rfl`).
- `enterFramePick_of_isSome_false` / `enterFramePick_oblivious_of_isSome_false`:
  the store is quantified AFTER the family test (`∀ (s : Store) (ch : Choices),
  …`) because the test `(nilValueMethodText? ctx fid args).isSome = false` no
  longer mentions a store from which `s` could be inferred — the same
  proposition, binder order changed.
- `runProgramSetupM fuel program name args ch : Except Stop (ProgramCtx × Config
  × Store × List Loc × Choices)` — returns the context it built (charter §3
  delta (iii)); `Pool.ProgramRun` binds it from that premise.
- **Fix round (2026-09-17, §8 items (1)/(2) RULED — statements changed, flagged).**
  `ThreadWf bound t := match t with | .running c _ => ConfigWf bound c | .aborted _
  => True` — the `types : TypeEnv` parameter and the conjunct
  `Config.itersNormalized types c = true` DELETED; `MultiWf m := StateWf m.shared
  ∧ m.cur < m.threads.size ∧ ∀ i h, ThreadWf m.shared.nextAddr m.threads[i]` —
  CONTEXT-FREE (the conjunct was its only reader of `ctx.types`); both
  `Decidable` instances restated. In `MultiWfSound.lean` 18 theorems are
  RESTATED, none weakened (each lost only hypotheses/conjuncts that were
  identically `true`): lost a CONTEXT hypothesis or `ctx.types` in the
  statement — `resumeThread_wf` (`hi`), `arrivalCases_single_wf` (`hi` + the
  conclusion's second conjunct), `arrivalCases_multi_wf` (`hi` + one conjunct in
  each branch), `applyPairing_wf` (`hibc`; `hts`/conclusion over `ThreadWf
  s.nextAddr …`), `stepThread_wf` (`hts`/conclusion likewise), `stepMulti_wf`
  (`MultiWf ctx m → MultiWf m`); lost a `{types : TypeEnv}` binder and its
  hypotheses/conjuncts — `ThreadWf.running` (`hi`), `ThreadWf.aborted`,
  `ThreadWf.mono`, `spawnStep_wf` (`hik` + two conjuncts), `resumeRecvDelivery_wf`
  (`hik` + one), `selectRecvDelivery_wf` (`hik` + one), `pool_get_wf` (one
  conjunct), `pool_set2_wf` (`hia`, `hib`), `chanArrivalPlan_wf` (`hik` + one),
  `pool_set1_wf` (`hia`), `pool_set1_aborted_wf`, `pool_set_push_wf` (`hia`,
  `hib`). Totals: 15 hypothesis binders, 10 conclusion conjuncts, 13 `{types}`
  binders, 16 internal `have`s; 195 code lines naming the predicate → 0.
  `MultiSound.lean` never named `MultiWf`: unchanged. No consumer outside
  `GoLean/GoCore` named any of it (`git grep itersNormalized -- ':!GoLean/GoCore'`
  = docs only), so nothing had to stay.
- Theorems whose only store binder became unused after their function became
  context-only lost that binder (e.g. `defaultValue_locSup`,
  `normalizeValueForTy_noPanic`, `renderPanicHead_string`, `abortMsg_string*`).

**Tombstones** (deleted definitions/lemmas, with their replacement):
`ExecState` (→ `ProgramCtx` × `Store`); `ExecState.nextAddr/allocCell/alloc/
updateCell` and the payload readers/writers (→ the `Store` versions, same
bodies); `ExecState.eqb`/`ExecState.eqb_sound` (→ `Store.eqb`/`Store.eqb_sound`,
heap-only); `StateWf.funcs_le` (→ `Func.locSup_eq_zero`); `step_preserves_iters`
(→ `Config.itersNormalized_true`, which it restated — itself deleted in the fix
round, below); `structTagCompatible_congr` (→ nothing: no two contexts in a
theorem).

**Fix-round tombstones (16 declarations, all → nothing: the predicate was
constantly `true`, so no fact is lost; the tombstone comments sit where they
lived in `StateWf.lean`):** `Cont.itersNormalized`, `Config.itersNormalized`
(the predicates); `Cont.itersNormalized_true`, `Config.itersNormalized_true`
(their vacuity certificates); the transparency lemmas
`enterRecvTargets_itersNormalized`, `applyChanOp_itersNormalized`,
`applySyncOp_itersNormalized`, `applyAtomicOp_itersNormalized`,
`commitClause_itersNormalized`, `applySelect_itersNormalized`; the walk lemmas
`seqCont_itersNormalized`, `pushDefer_itersNormalized`,
`panicPassthrough_itersNormalized`, `recoverThroughWrappers_itersNormalized`,
`recoverResult_itersNormalized`; and `spawnPlan_iters` (`MultiWfSound.lean`).

## 5. The S0 warm measurement and how the estimate held

Measured (evidence README): `LEAN_NUM_THREADS=4 GOLEAN_MEM_MAX=32G scripts/capped
lake build GoLean.GoCore` after a `State.lean` touch = **104 s** (20 modules
rebuilt; under the train's concurrent 48G gate). The charter's condition «≤ 15
min and 0 tags moved ⇒ S1–S3 in one session» held with a factor of ~8.5 to
spare; in practice the per-module warms were 1–16 s (StateWf 16 s, MachineSound
+ UnseqSound 62 s), the eval-test module 65–144 s, and the whole B7 build
(S0–S5) ran in ONE session, gate included. The cost was not rebuild time but
the proof re-indexing in `StateWf.lean`/`MultiWfSound.lean` (five and two fix
rounds respectively, each a compiler-guided batch of destructuring-arity edits).

## 6. Wire neutrality and positional tags (evidence)

- **Wire**: `GoLean/NativeToIR.lean`, `tools/nativefrontend/**`,
  `scripts/check-frontend-pins` UNTOUCHED (`git diff --stat` names none of them).
  The decoder produces the SAME `Program` record; `ProgramCtx` wraps it
  (`⟨program⟩`, at `runProgramSetupM` and `CLI.enumSetup`) — no field is read
  differently, no field is added to the wire. Every corpus row the gate lowers
  decodes byte-identically because the decoder is byte-identical; the twin pin
  `baselines/pins/twin-chdriver.wire.json` is checked by the gate's frontend-pin
  step (green, §2).
- **Positional tags**: `docs/evidence/2026-09-17_b7-context-store/
  fun_cases-tags-{before,after-s2}.txt` — `fun_cases stepFn s c ch` vs
  `fun_cases stepFn ctx s c ch`: 162 arms both, tag names and order identical,
  every last-hypothesis fingerprint identical, every arm's hypothesis count +1
  (the `ctx`). `stepFn_sound` (66 named tags), `stepFn_consumption_none` (44),
  `stepFn_consumption_some` (15) needed NO renumbering.

## 7. [AGENT] representation choices, with the alternative named

| choice | taken | alternative (not taken) | why |
|---|---|---|---|
| threading idiom | `variable (ctx : ProgramCtx)` per module for DEFINITIONS (ctx = first explicit argument of every def that mentions it); theorems take it IMPLICITLY (`variable {ctx}` toggles, or a module-wide `variable {ctx : ProgramCtx}` in the theorem-only modules) | the snapshot `85f9abd7`'s explicit ctx on theorems (every lemma application becomes `(foo ctx) h`) | lemma applications stay byte-identical (`stepFn_sound hstep`, `enterFramePick_cases hpick`); the proof churn is the conjunct re-indexing only |
| `MachineWf` arity | ctx-FREE (`MachineWf σ c`): with D6 nothing in it reads the context | the charter §4's spelling `MachineWf ctx s c` (a vacuous parameter) | fewer parameters, smaller proofs; the charter wrote the spelling before D6 was ruled in the same document |
| `ThreadWf`/`MultiWf` | at the first gate: UNCHANGED shape (`MultiWf ctx m` read `ctx.types` for the per-thread `itersNormalized` conjunct); **fix round: the conjunct + the `types` parameter DELETED, `MultiWf m` context-free** (§4 «Fix round») | (the alternative at the first gate was this deletion; the alternative in the fix round was keeping the conjunct) | D6 as ruled named `MachineWf`, so the twin was posed in §8, not self-adjudicated; the [USER] ruled it 2026-09-17 (§8) |
| context-only helpers lose the store | 43 Ops readers, 10 Machine helpers, 2 Race, 1 ChoiceTrace (`nilTextFacts`) — the snapshot's cleanup pass, reproduced | keep an unused `(s : Store)` parameter | the core build must be WARNING-free (`linter.unusedVariables`); and an unread parameter is a lie about the dependency |
| `ProgramCtx.ofTables` | added: bare tables → context with the OLD `ExecState` defaults (`#[]` everywhere) | build hand-built contexts as `⟨{ typeDefs := …, funcs := … }⟩` (Program defaults: `TypeEnv.reserved`, `reservedDisplays`) | byte-identical fail-closed behaviour of every hand-built fixture and of `runFunctionWithContextM` (no record → refuse; no display → marker) |
| the setup seams | `runProgramSetupM` RETURNS its context; `CLI.enumSetup` stores it in `EnumProgram.ctx`; `Pool.ProgramRun` binds it from the setup premise | a context parameter on the Program-level entries (`runProgramM ctx …`) — the snapshot's shape | one context per run, built at ONE seam from the decoded program; no core operator and no driver selects a context of its own |
| the setup refusal text | «seeded state ill-formed: a location in a global cell dangles beyond the allocator bound» (was «… global cell or function body …») at BOTH seams | keep the old text byte-for-byte | the check is heap-only now; a message naming a check that is not performed would be a fail-noisy lie. An `.internal` refusal on a path no decoded program reaches (A4: bodies are loc-free) — not a differential-visible text |
| `Store.updateCell`'s `.internal` text | byte-preserved («allocation goes through ExecState.alloc only») as the snapshot and the charter §6 (i) prescribe | rename to `Store.alloc` | the charter says byte-preserved; C1 owns the seam — the historical spelling is recorded as an OWED wording refresh |

## 8. The handoff's [USER] items — RULED 2026-09-17, DONE in the fix round

Ruling: [USER] Mike, 2026-09-17, verbatim, relayed by the [AGENT] coordinator —
cite as relayed: «We should delete the vacuous conjunct right? that's just a strict improvement. The rewordings sound fine. Agree with the audit, go ahead and launch (after the rulings if relevant)». Record: `docs/2026-08-31_qrow-rulings.md`,
«The B7 handoff rulings record (2026-09-17)».

1. **The pool-side `itersNormalized` conjunct** (`ThreadWf bound types t`, hence
   `MultiWf ctx m`) — as posed: the same constantly-true predicate D6 deleted
   from `MachineWf`, kept because the ruling named `MachineWf`; deleting it is a
   restatement of `ThreadWf`/`MultiWf` + the proof sites in `MultiWfSound.lean`
   and makes `MultiWf` context-free. **RULED delete** («We should delete the
   vacuous conjunct right? that's just a strict improvement»). **DONE**, runtime
   commit `1fafc9f2`: §4 «Fix round» lists every restated statement; 195 code
   lines naming the predicate → 0; first-round build, 0 warnings; gate at the
   same expected red set (§2).
2. **`Cont.itersNormalized`/`Config.itersNormalized` and their `_true` lemmas** —
   as posed: inert once (1) lands, to be deleted with it. **RULED with (1)** —
   the [AGENT] reading of «strict improvement» (relayed by the coordinator in
   the fix-round brief): dead predicates leave with the conjunct, UNLESS
   something outside the core still names them. Checked: `git grep -n
   itersNormalized -- ':!GoLean/GoCore'` names only docs (no `Tests/`, no tool,
   no spike) — so **DONE**: the 16 declarations tombstoned in §4.
3. The **`Store.updateCell` refusal text** still naming `ExecState.alloc`
   (byte-preserved per the charter; owed wording refresh — C1's seam) —
   **RULED as landed** («The rewordings sound fine»): stays byte-preserved here;
   the refresh remains C1's.
4. The **setup refusal text** («… or function body …» dropped at both seams,
   §7) — **RULED as landed** («The rewordings sound fine»): the disclosed
   wording stands; no revert.

## 9. What B7 leaves to C1 / C3 / P (the charter §5 item 4; `docs/2026-09-11_bug090-rediagnosis.md` §5)

B7 changed neither cost A (whole-root re-normalization in `storeLoc`) nor cost
B (pre-step state retention): `deliverS`'s pre-op rollback (`StepFn.lean`) and
`raceUpdate` reading the pre-store after `stepMulti` (`Multi.lean`) are
UNCHANGED, now over `Store` — and no retention site was ADDED (every
`(s : Store)` parameter is the former `(s : ExecState)` one). `Store` is the
ONE named seam C1 redesigns: leaf-cost path writes, linear normalization,
unique ownership across a step, allocation-time normalization, cell granularity
(PENDING [USER] there), the map key index, the access trace replacing
`Race.lean`'s table. The frame list is C3's; method promotion is P's. B7
removed exactly one cost: `ExecState.eqb`'s five-table walk at heap-equal
enumerator nodes (`Store.eqb` compares the heap only).

## 10. What was taken from the snapshot `85f9abd7` (D8: REPLAY, never applied)

`GoLean/GoCore/Store.lean` as a file (minus nothing; header rewritten with
provenance), `GoLean/GoCore/ProgramCtx.lean` as a file MINUS its `platform`
field (D1 (a)) PLUS `ofTables`; the `variable (ctx : ProgramCtx)` idiom for
definitions and the cleanup inventory (which helpers lose the unused store) as
the MAP. Every proof hunk was re-derived against main's Stage B tree with the
compiler (the snapshot's `StateWf`/`MachineSound`/`Multi*` hunks were stale by
design — §6 of the charter). The snapshot's explicit-ctx theorem idiom, its
`B7Reference/` apparatus (D5 (a)), its Iris wrapper and its `spikes/*` were NOT
taken.

## 11. The train's next command

1. Merge protocol steps 3–5 as usual (audit ask below; merge only on explicit
   at-that-moment sign-off; `git merge --ff-only core/b7-context-store-0917`).
2. **Step 5a applies**: compiled semantic inputs changed (the whole core and
   `CLI.lean`), so `python3 tools/certification.py release-check --base
   refs/snapshots/<round>/main` will report the inventory changed → run
   `scripts/ci --slow`, install the reviewed `certification-candidate.json` as
   `baselines/certified/imported-goose/channel/google-search.certified.json`
   (the ONE cached certified row; its `--slow` re-enumeration is expected
   «unchanged set»), commit as the round's 5a records commit, re-run the gate.
3. Then C1 (`Store` is its seam) — the charter's «B7, then C1».

## 12. Audit ask (posed; unconditional per CLAUDE.md; scope and waiver the [USER]'s)

Requested: the pre-merge adversarial audit of this branch. Suggested focus, in
order of leverage: (a) every theorem statement in §4 — is any restatement a
weakening? (the reviewer should diff the statements, not the proofs); (b) the
setup seams — `runProgramSetupM`/`CLI.enumSetup`/`ProgramRun`/`runProgramPoolOutM`
build ONE context from the decoded program and nothing else selects one; (c)
the hand-built fixtures — `ProgramCtx.ofTables`'s `#[]` defaults reproduce the
old `ExecState` defaults at every fixture (fail-closed behaviour byte-identical);
(d) the two refusal-text decisions in §7; (e) the wire-neutrality claim (§6);
(f) the fix round's 18 + 2 + 2 restatements (§4 «Fix round») — each lost only a
conjunct/hypothesis that was identically `true`; the reviewer should confirm no
other hypothesis moved. Not merged, not pushed.
