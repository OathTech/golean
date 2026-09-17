# Adversarial audit of B7 (branch `core/b7-context-store-0917`, candidate tip `d0e65182`) — 2026-09-17

**VERDICT: FIX-FIRST — narrow and records-class: one undisclosed byte change to a core refusal text (F1, one string literal, unreachable) plus four records corrections; no wrong answer, no unsound proof, no weakening, no coherence gap, no fail-open, no gate weakening found.**

[AGENT] auditor (this report and every check in it), branch
`review/b7-context-store-0917` at `d0e65182` (five commits over main
`5955e55f`: `66fe1092` S0 records, `73ad798d` the runtime commit, `a7fd0542`
records, `1fafc9f2` the fix-round runtime commit, `d0e65182` fix-round records).
Ordered by the [USER] (Mike, 2026-09-17, verbatim, relayed by the [AGENT]
coordinator — cite as relayed: «Agree with the audit, go ahead and launch (after
the rulings if relevant)»). Nothing here is adjudicated that is the [USER]'s:
dispositions are PROPOSED; items needing a ruling are marked PENDING [USER].
Evidence (small receipts): `docs/evidence/2026-09-17_b7-context-store-audit/`
(README there maps file → check). Binaries compared throughout: main
`155df5c3…` (the primary's certified build at `5955e55f`, copied read-only) vs
candidate `1ea8f2ac…` (built here: `scripts/capped lake build` over a plain copy
of the lane's `.lake`, EXIT=0, no-op). Frontend: `go build` of the UNTOUCHED
`tools/nativefrontend` at the tip (`9b52821a…`).

## 0. Bootstrap receipts

| step | command | result |
|---|---|---|
| deps | `scripts/setup-deps --from /home/dev/projects/golean` | EXIT=0 (goose 3be88bb, raft 56e3200, go c19862e5f8) |
| warm | `cp -a …/b7-context-store/.lake .lake` (no symlinks: 0) then `scripts/capped lake build` | EXIT=0, «Build completed successfully (96 jobs)» — a no-op: the copied build IS the tip's |
| candidate binary | `sha256sum .lake/build/bin/golean` | `1ea8f2ac622f3ba5b18d0e9ddfbe4884ae6c20cdef706296da975b8e27f3df3f` (= the handoff's `1ea8f2ac…`) |
| main binary | `sha256sum /home/dev/projects/golean/.lake/build/bin/golean` | `155df5c3d7a52816f48372adbeb34c755d04a87301bf103fcbbe15e53683eb26` (= the lane's `155df5c3…`) |
| totality | `scripts/capped bash scripts/check-core-audit` | EXIT=0: «45 GoLean modules in the closure (36 under GoLean.GoCore) … 51 required theorems present; 15244 declarations … classical trio only»; 5 poison controls rejected by name (`core-audit-tail.txt`) |

## 1. Findings (by severity; WRONG-ANSWER > UNSOUND-PROOF/WEAKENING/COHERENCE-GAP > FAIL-OPEN > RECORDS-CLAIM > SCOPE > PERFORMANCE > NIT)

No finding at WRONG-ANSWER, UNSOUND-PROOF, WEAKENING, COHERENCE-GAP or FAIL-OPEN severity. Positive verifications are §2–§4.

### F1 — RECORDS-CLAIM (with a NIT): a THIRD refusal text changed byte-wise, undisclosed

- **What I did.** Extracted every string literal (comments stripped, whole files) from the 34 changed `GoLean/`/`Tests/` files at `5955e55f` and at `d0e65182` and compared the multisets (`.tmp/lits.py`; `literal-changes.txt`). Everything else that differs is an interpolation ARGUMENT rename (`{goTypeNameForMessage state X}` → `{goTypeNameForMessage ctx X}` / `{… X}`, `{state.types.size}` → `{ctx.types.size}`) whose rendered bytes are unchanged.
- **What happened.** Exactly THREE literals changed in content: (1) «seeded state ill-formed: a location in a global cell or function body dangles beyond the allocator bound» → «… in a global cell dangles …» (×2, both seams — DISCLOSED, handoff §7/§8.4, RULED); (2) `Store.updateCell`'s «allocation goes through ExecState.alloc only» — UNCHANGED (as ruled); (3) **`GoLean/GoCore/Machine.lean:3734`** in `applySyncOpCore`: `throw (.internal "try-lock heads apply through applySyncOp ctx (the choice-taking entry), never the core")` — was `"… through applySyncOp (the choice-taking entry) …"` at `5955e55f:GoLean/GoCore/Machine.lean:3700`. A mechanical `applySyncOp ` → `applySyncOp ctx ` rewrite hit the inside of a string literal. Not in the handoff §7 table, not in §8, not in the slice log; the commit message and handoff say «two refusal texts changed wording».
- **Reachability.** `applySyncOp` (`Machine.lean:3896–3908`) intercepts every try head (`op.tryTargets?` = `some _`) and calls `applySyncOpCore` only under `none`; `applySyncOpCore` has no other code caller (`grep applySyncOpCore GoLean/GoCore/{Machine,StepFn,Multi}.lean` → prose + line 3907). The arm is a defensive `.internal`, unreachable from `stepFn`; NOT observation-bearing (the 261-row trace subset and the 39 wire runs below are byte-identical). The differential cannot see it.
- **Why it matters.** The charter (§5 items 2–3) and the handoff's own claim structure rest on «every text change disclosed»; the ruling «The rewordings sound fine» covered two texts, not this one. The new text is also garbled (it names a Lean application, «applySyncOp ctx», in a message meant for a human).
- **Proposed disposition.** Revert the literal to its old bytes (one line, records-class, no proof touches the string — `grep "try-lock heads" GoLean` finds only this site) and note it in the handoff §7; OR disclose it as a third rewording and re-pose. PENDING [USER] which; the revert is the [AGENT] recommendation (byte-preservation is the charter's default).

### F2 — RECORDS-CLAIM: the runtime-commit delta is misstated

- **What I did.** `git diff --stat 66fe1092..73ad798d -- GoLean Tests` (post-rebase) and `git diff --stat 7f1c1fe7 2500b434 -- GoLean Tests` (pre-rebase).
- **What happened.** Both: **34 files changed, +3,232 / −2,862**. The handoff §1 («Net runtime delta at the gate tip: 32 files, +3,058/−2,862») and the evidence README («32 files, +3,058/−2,862») are off by 2 files (the docstring-only `Platform.lean`, `Syntax.lean`) and 174 inserted lines. The −2,862 matches. The fix round: 4 files, +213/−538 (as stated). Whole branch runtime delta: 34 files, +3,349/−3,304.
- **Disposition.** Correct the two sentences (records-only).

### F3 — RECORDS-CLAIM: «`ExecState` 30 modules → 0» is 31 files / 29 code modules

- `git grep -l ExecState 5955e55f -- GoLean Tests` = **31** files; the README's own per-file list sums to 31 (26 `GoLean` + 5 `Tests`), of which `Platform.lean` and `Syntax.lean` are docstring-only → **29 code modules**. AFTER: 0 code mentions, 10 prose lines in 7 files (README: «5 docstring mentions»). Nothing hinges on it; correct the number.

### F4 — RECORDS-CLAIM (minor): the `itersNormalized` count is spelled four ways

- README «199 mentions (StateWf 104, MultiWfSound 93, Multi 1, MachineSound 1)»; commit `1fafc9f2` and the slice log «195 code lines»; my count at `5955e55f`: **198 lines** naming it in `GoLean/` (StateWf 104, MultiWfSound 92, Multi 1, MachineSound 1), 196 non-comment. AFTER: **13 prose lines** (matches the README exactly). Pick one spelling (lines vs mentions) and use it.

### F5 — RECORDS-CLAIM (minor): the first gate's 1068 s is not in the tracked tail

- `gate-tail.txt` (first round) ends at «RESULT: FAIL» — no «CI total wall seconds» line; `gate-tail-fixround.txt` has «CI total wall seconds: 934». The 1068 s figure is therefore a lane-side number the tracked evidence cannot confirm; the RESULT/step lines and the single drift line ARE in both tails and match the claims (see §4 (k)).

### F6 — SCOPE/RECORDS (minor): `spikes/i1-declarations` now names a deleted type, unrecorded

- `spikes/i1-declarations/Prototype.lean:69,76,90` take `(s : ExecState)`. Outside the lakefile and the gate (does not build; never did in the gate), so no red — but the charter's D7 shape («leave dark and record») for spikes that will not build against the new API was applied to `gate-a1`/`iris-customer` and this spike is not mentioned in the handoff, the slice log or the rulings record (`grep -c i1-declarations` = 0 in all three). Add one line.

### F7 — NIT (code hygiene): `MachineEqb.lean` declares a context nobody uses

- `GoLean/GoCore/MachineEqb.lean:38` `variable (ctx : ProgramCtx)` and **37** `variable {ctx}` / `variable (ctx)` toggles; `ctx` appears in NO definition or theorem of the module (39 tokens, 38 in `variable` lines, 1 in the comment at line 37). `Store.eqb` is heap-only and needs no context. The idiom was copied from modules that do read the context. Delete the variable and the toggles (a pure re-typing of nothing; the module compiles identically). Not a correctness matter.

### F8 — NIT (statement generality, so the «none weakened» claim is read precisely)

- `loadLoc_root_congr`, `storeLoc_congr`, `normalizeValueForTy_congr` were stated over TWO states `σ₁ σ₂ : ExecState` with `htypes : σ₂.types = σ₁.types` and no constraint on the other four tables; they are restated over two `Store`s under ONE `ctx`. The new statements are the specialisation `ctx₁ = ctx₂` of the old; the old form's residual content — «these three operators read only `ctx.types`» — is not recorded as a lemma (it was implicit in the old statements' generality). Nothing in-repo consumed the two-table generality (the proofs re-index under one `ctx`; the build is green), and with no customer nothing downstream does either. Disposition: none required; if ever wanted, a `{ctx₁ ctx₂} (h : ctx₁.types = ctx₂.types)` form is provable by unfolding. PENDING [USER] only in the sense that it is a design taste, not a defect. (`structTagCompatible_congr`, retired, was `htypes ▸ rfl`: content-free.)

### F9 — PERFORMANCE (positive; a records-completeness note, not a defect)

- The handoff §9 says B7 «removed exactly one cost: `ExecState.eqb`'s five-table walk». Measured (`perf.tsv`): the `engine=dedup` rows `atomics/counter/add` **0.11 s → 0.03 s** and `atomics/counter/cas-loop` **0.60 s → 0.12 s** (3 runs each, identical `nodes=17535 edges=20601 dedupHits=3067 certified=checkCert`) — the predicted mechanism, 3.7–5× on those rows. A SECOND cost also went: the setup seams' `if StateWf s₀` decision used to evaluate `funcListSup` over every function body of the program at every run start (`ExecState.locSup` included the program text); it is heap-only now. Twin wire (450 funcs), `probeTwinSingle`, 5 runs: 0.59–0.61 s → 0.56–0.59 s. Execution cost otherwise unchanged within noise: `append_grow 2000` 4.58–4.88 → 4.28–4.38 s, `scalar 80000` 1.03–1.04 → 0.96–1.02, `write_fixed 3000 100` 1.07–1.09 → 0.98–0.99, `map_write 16000` 2.61–2.67 → 2.53–2.58, `alloc_new 32000` 13.54–13.99 → 14.13–14.38 (the one probe slower on all 3 runs, +3–4%; shared box, no cgroup isolation — I read ±8% as noise). DFS-engine membership rows: identical `steps/probes/sites/leaves` counts, identical wall (3.36–3.44 s both). Disposition: add the second removed cost to §9 (records).

### F10 — RECORDS (minor): charter §8 asked for a gate line per explicit-target warm

- The evidence README gives «representative lines» for the S1–S5 warms (Store+ProgramCtx 0 s, Ops 5 s, …) and per-module numbers for the fix round; not every warm. Acceptable as records; noted because the charter's wording was «every».

## 2. (a) Restated theorems — the weakening hunt (statements, not proofs)

**Method.** A statement extractor (`.tmp/extract_stmts.py`: keyword … first depth-0 `:=`/`where`, comments stripped) over all 34 changed Lean files at `5955e55f` and `d0e65182`; every declaration matched by name; every changed statement reduced to its token-level delta (`statement-deltas.txt`, 53 KiB, complete). Totals: **554 changed statements** in 27 modules, 34 deleted, 44 added (`statement-summary.tsv`). I read every delta. Every removed/added token falls in one of these classes, and NOTHING ELSE:

| class | tokens | verdict |
|---|---|---|
| (i) `ExecState` → `Store` | all modules | re-typing |
| (ii) `ctx` inserted as an argument, or an implicit `{ctx}` from a module `variable` | all modules | the new parameter; theorems universally quantify it (`variable {ctx : ProgramCtx}` at MachineSound:21, StateWf:74, MultiWfSound:16, …) — STRONGER than fixing the tables from a state, and sound because the machine reads tables from `ctx` only (§4 (b)/(g)) |
| (iii) a `{σ : ExecState}`/`(state : ExecState)` binder dropped where the function became context-only (`normalizeValueForTy_locSup`, `defaultValue_locSup`, `renderPanicHead_string`, `abortMsg_string*`, `nilValueMethodWidth_of_*`, …) | 55 defs, their lemmas | the binder was dead (§4 (l)) |
| (iv) context-equality conjuncts `σ'.types = σ.types ∧ σ'.functions = σ.functions ∧ σ'.methods = σ.methods` dropped from conclusions (38 StateWf sites, 6 MultiWfSound sites), `htypes` dropped from 3 hypotheses, `strictWfSame`'s reflexive `σ.functions = σ.functions ∧ …` dropped | StateWf, MultiWfSound, MachineSound | tautologies by type / hypotheses that can no longer be false (F8 for the congr trio) |
| (v) `hf₁ : Func.locSup func₁ ≤ funcListSup σ.functions.toList` (`enterFrame_tail`) and `h2 : funcListSup … ≤ σ.nextAddr` (`StateWf.mk'`) dropped | StateWf | HYPOTHESES removed ⇒ strictly stronger; both are `0 ≤ _` by `Func.locSup_eq_zero`/`funcListSup_eq_zero` |
| (vi) `itersNormalized` hypotheses / conclusion conjuncts / `{types : TypeEnv}` binders dropped; `ThreadWf bound types t` → `ThreadWf bound t`; `MultiWf ctx m` → `MultiWf m`; `MachineWf` third conjunct | Multi, MultiWfSound, StateWf (D6 + fix round) | the predicate was constantly `true` (`Config.itersNormalized_true`, a theorem at `5955e55f:StateWf.lean:663`) ⇒ equivalence-preserving |
| (vii) `enterFramePick_of_isSome_false` / `_oblivious_…`: `{s} {ch}` moved after the family test as `∀ (s : Store) (ch : Choices),` | Machine | binder order only; same proposition |
| (viii) `runProgramSetupM … : Except Stop (ProgramCtx × Config × Store × List Loc × Choices)` | StepFn | returns the context it built; `ProgramRun` binds it (`ProgramTrace.lean:14–27`); `program_run_iff`/`observation_iff` statements IDENTICAL |
| (ix) `σ.types` → `ctx.types` inside a statement (`isNormalForTy_sound`, `bindIterVars_ok_of_normal`, `mapIterCandidates_normalized`, `dynamicDispatch?_locSup`'s `funcListSup ctx.functions.toList`) | StateWf, MachineSound | the same table under its new name |

**No hypothesis was ADDED anywhere; no conclusion conjunct was dropped except classes (iv)/(vi).** Per-theorem table for the coordinator's list (full text in `key-statements.txt`):

| theorem | BEFORE (`5955e55f`) → AFTER (`d0e65182`) | delta beyond (i)/(ii) | verdict |
|---|---|---|---|
| `stepFn_sound` | `stepFn s c ch = .ok (c', s', ch') → Step c s c' s'` → `stepFn ctx s c ch = .ok … → Step ctx c s c' s'` | none | same `ctx` both sides; restated |
| `step_complete` | `Step c s c' s' → ∃ ch ch', stepFn s c ch = .ok …` → `Step ctx … → ∃ ch ch', stepFn ctx s c ch = .ok …` | none; NO existential over contexts | restated |
| `step_complete_any_wf` | `(h : Step c σ c' σ') (hwf : MachineWf σ c) : ∀ ch, ∃ c₂ σ₂ ch₂, stepFn σ c ch = .ok …` → same with `ctx` | none (`MachineWf` context-free, D6) | restated |
| `step_preserves_wf` / `Step.preserves_wf` / `stepFn_preserves_wf` | `Step c σ c' σ' → MachineWf σ c → MachineWf σ' c'` → with `ctx` | none; `MachineWf` lost its constantly-true 3rd conjunct (vi) | restated |
| `stepMulti_sound` | `stepMulti m ch = .ok (m', ch', ev) → StepM m m'` → `stepMulti ctx … → StepM ctx m m'` | none | restated |
| `stepM_complete` | `StepM m m' → ∃ ch ch' ev, stepMulti m ch = .ok …` → with `ctx` | none | restated |
| `stepMulti_wf` | `MultiWf m → stepMulti m ch = .ok … → MultiWf m'` → `MultiWf m → stepMulti ctx m ch = .ok … → MultiWf m'` | `MultiWf` lost its `types` reading (vi) | restated |
| `Pool.run_iff` | `execProgLoopOut fuel m r ch acc = result ↔ Run fuel m r ch acc result` → both sides `ctx` | none | restated |
| `program_run_iff`, `observation_iff` | IDENTICAL text; `ProgramRun`'s constructors bind `pctx` from the `runProgramSetupM` premise | (viii) | unchanged |
| `iter_iff_trace`, `run_ok_iff`, `exists_run_ok_iff` | `stepFnIter n s c ch = .ok … ↔ Trace n …` → both sides `ctx` | none | restated |
| `checkCert_slowObs`, `checkCertM_slowObs` | `checkCert nodeEqb … = true → ∀ o, o ∈ cert.obsSet ↔ SlowObs resultLocs m₀ r₀ o` → `checkCert ctx …`, `SlowObs ctx …` | none | restated |
| `stepFn_consumption_none/some` | `seqConsumption σ c = …`, `stepFn σ c ch` → with `ctx` | none | restated |
| `enterFrame_tail` | lost `hf₁` and three (iv) conjuncts | (iv)+(v) | STRONGER |
| `StateWf.mk'` | lost `h2` | (v) | STRONGER |
| `loadLoc_root_congr`, `storeLoc_congr`, `normalizeValueForTy_congr` | lost `htypes`; two stores under one `ctx` | (iv) | restated; F8 |
| `structTagCompatible_congr` | RETIRED | was `htypes ▸ rfl` | inert |
| `isNormalForTy_sound`, `bindIterVars_ok_of_normal`, `mapIterCandidates_normalized`, `dynamicDispatch?_locSup` | `σ.types`/`σ.functions` → `ctx.types`/`ctx.functions` | (ix) | restated |
| **Fix round, 18 MultiWfSound theorems** — `ThreadWf.running` (−`{types}`, −`hi`), `ThreadWf.aborted` (−`{types}`), `ThreadWf.mono` (−`{types}`), `spawnStep_wf` (−`{types}`, −`hik`, −`s'.types = s.types ∧`, −2 `itersNormalized` conjuncts), `resumeRecvDelivery_wf` / `selectRecvDelivery_wf` (−`{types}`, −`hik`, −1 (iv) conjunct, −1 (vi) conjunct), `resumeThread_wf` (−`hi`, −1 (iv), −1 (vi)), `pool_get_wf` (−`{types}`, −1 (vi)), `pool_set2_wf` (−`{types}`, −`hia`, −`hib`), `chanArrivalPlan_wf` (−`{types}`, −`hik`, −1 (vi)), `arrivalCases_single_wf` (−`hi`, −1 (vi)), `arrivalCases_multi_wf` (−`hi`, −2 (vi)), `applyPairing_wf` (−`hibc`, −1 (iv), `ThreadWf` args), `pool_set1_wf` (−`{types}`, −`hia`), `pool_set1_aborted_wf` (−`{types}`), `pool_set_push_wf` (−`{types}`, −`hia`, −`hib`), `stepThread_wf` (−1 (iv), `ThreadWf` args), `stepMulti_wf` (above) | exactly the handoff §4 «Fix round» list; the 19th changed statement in the module, `runnableIdxs_lt`, is (ii) only | every dropped item is (iv) or (vi) | none weakened |
| `ThreadWf` / `MultiWf` (defs) | `ThreadWf bound types : Thread → Prop`, `.running c _ => ConfigWf bound c ∧ Config.itersNormalized types c = true` → `ThreadWf bound`, `.running c _ => ConfigWf bound c`; `MultiWf` drops `m.shared.types` | `ctx.types` was read ONLY by the deleted conjunct (the `def` bodies before/after, `Multi.lean:2481/2507` → `2503/2530`) | context-free, as claimed |

**Was `ctx.types` truly only read by the deleted conjunct?** Yes: at `5955e55f` `MultiWf` reads `m.shared.types` at exactly one place, the `ThreadWf` argument, and `ThreadWf`'s only use of `types` is the `itersNormalized` conjunct. `MultiSound.lean` never named `MultiWf` (checked).

## 3. (c) Fixture defaults — every hand-built context vs the old state

`ProgramCtx.ofTables` (`ProgramCtx.lean:55–58`) sets ALL six `Program` fields explicitly (`typeDefs := types, funcs := functions, methods, globals := #[], methodSets, typeDisplays`; `Program`'s own wire defaults `TypeEnv.reserved`/`TypeEnv.reservedDisplays` are NOT inherited). The old `ExecState` defaults were `#[]` for all five tables (`5955e55f:State.lean:77–97`). Every fixture, from `git diff 5955e55f..d0e65182 -- Tests/`:

| file | fixture (before → after) | tables preserved? |
|---|---|---|
| `GoCoreContract` | `exampleState := { types := TypeEnv.reserved }` → `exampleCtx := ofTables (types := TypeEnv.reserved)` + `exampleState : Store := {}` | yes |
| `GoCoreContract` | `fresh : ExecState := {}` → `emptyCtx := ofTables (types := #[])` + `fresh : Store := {}`; `illTyped`/`aliasState`/`scopeState` heap-only → `Store` | yes |
| `GoCoreEval` | `emptyCtx := ofTables (types := #[])` for every `{}`/`({} : ExecState)` (storeLoc/loadLoc BUG-085 guard, `convertValueToTy {}`, `stepNeeds ⟨…, {}, 0⟩`, `buildCert`/`checkCert`) | yes (13 `GoCore.ExecState :=` fixtures at base = the handoff's 13) |
| `GoCoreEval` | `renderPanicPayload { types := reserved }`, `l3State { types := reserved }` (+ `seqConsumption l3State {} …`: ctx + empty store) | yes |
| `GoCoreEval` | `{ types := #[] }` ×6 (R1 carrier tests) → `ofTables (types := #[])` | yes |
| `GoCoreEval` | decoded-wire fixture `{ types := prog.typeDefs, functions := prog.funcs, methods := prog.methods, methodSets := prog.methodSets }` → `ofTables` with the same four (`typeDisplays` `#[]` both) | yes |
| `GoCoreEval` | `syncNoRecord { types }`, `syncWithRecord { types, functions, methods, methodSets }` | yes |
| `GoCoreEval` | `dispNoRecord { types, functions, methods }`; `dispWithRecord := { dispNoRecord with methodSets, typeDisplays }` → `ofTables (types := dispNoRecord.types) (functions := …) (methods := …) (methodSets := …) (typeDisplays := …)`; `dispRecordNoDisplay` likewise with `typeDisplays := dispNoRecord.typeDisplays` (= `#[]`) | yes |
| `GoCoreEval` | `sameNameState`, `scopesState`, `noRecordState` `{ types, typeDisplays }` | yes |
| `GoCoreEval` | `valueMethodState { types, typeDisplays, methodSets, methods }`; `ptrMethodState`/`noMethodState` = `{ valueMethodState with methods := … }` → `ofTables` re-listing all five | yes |
| `GoCoreEval` | `{ noMethodState with methodSets := … }` ×2, `{ sameNameState with typeDisplays := reservedDisplays }` ×2 → `ofTables` re-listing all five | yes |
| `MethodIdentity` | `implementing` (5 tables), `nilTextState` (types, functions, methods); `withIface`/`unknown`/`exportedOnly` via `⟨{ base.program with … }⟩` (globals `#[]` untouched) | yes |
| `PanicRendering` | `state := { types := reserved }` → `ProgramCtx.ofTables (types := reserved)` (renderers read the context only; compiles) | yes |
| `StringPanicMembers` | `state := { types := reserved }` → `ctx := ofTables (types := reserved)` + `state : Store := {}` | yes |
| `Ops.lean:2062` (an `example`, not a fixture) | `valueEq { types := [main.T, main.S] } …` → `valueEq (ofTables (types := …)) …` | yes |
| `Tests/UnseqScheduler.lean` | unchanged; Program-level via `CLI.enumSetup` (0 mentions of `ExecState`/`ctx`) | n/a |

No fixture gained or lost a table.

## 4. The other focus items — what I did, what happened

**(b) One context.** Construction sites of a `ProgramCtx` in code (`grep ofTables\|⟨program⟩\|ProgramCtx.mk\|{ program :=`): `StepFn.lean:1120` (`runProgramSetupM`: `⟨program⟩`, returned as the first component), `CLI.lean:814` (`enumSetup`: `⟨program⟩`, stored in `EnumProgram.ctx` — the ONLY `EnumProgram` constructor site; `ExpCtx.ep` is bound from it at `CLI.lean:1479`), `StepFn.lean:907` (`runFunctionWithContextM`: `ofTables types functions methods` — the pre-existing bare-tables entry; before B7 it built `{ types, functions, methods }` with the same `#[]` defaults), `Ops.lean:2062` (an `example`), and the test fixtures (§3). Consumers: `runProgramM`/`runProgramPoolOutM` (`Multi.lean:2361–2369`) use the returned `pctx`; `ProgramRun` (`ProgramTrace.lean:14–27`) binds `pctx` from the setup premise; `ChoiceTrace.traceProgram` uses `ep.ctx` (`:750–760`), its two entries go through `CLI.enumSetup` (`:930`, `:1078`); the enumerator's DFS uses `ctx.ep.ctx` everywhere (`CLI.lean:1266–1394`, residual diff). No `ProgramCtx.ofTables #[] …` default reaches a real run; no second setup; no re-seed path. The «scratch program where it would matter»: the 39 lowered rows below include method dispatch (`methods/method-expr-call-position/call-order`, `multipkg/private-method-dispatch/unicode`, `interfaces/embedded-interface-duplicate-method`) and the raft twin (`multipkg/mini-raft-twin/elect-propose-commit`) — byte-identical on both binaries.

**(d) Refusal texts.** F1. Observation-bearing texts (panic messages, statuses, output): all interpolation renames only; confirmed by the 39 wire runs and the trace subset.

**(e) Wire neutrality.** `git diff 5955e55f..d0e65182 -- GoLean/NativeToIR.lean GoLean/NativeDeclaration.lean tools scripts baselines Corpus raftsubject raftharness Main.lean lakefile.toml lake-manifest.json lean-toolchain` = **0 lines**. `Program` (`Syntax.lean`) unchanged except a docstring; the decoder yields the same record and both seams wrap it (`⟨program⟩`). Runs (`wire-compare.tsv`): 39 rows (every 150th manifest row + 12 feature-picked + the raft twin + the certified `imported-goose/channel/google-search`), lowered by the frontend built at the tip, `native-json-run` with both binaries: **38 SAME (stdout, stderr, exit), 0 DIFF, 1 frontend-refused identically** (`generics/stencil-residual-field-iterseq/healthy`). The pinned twin `baselines/pins/twin-chdriver.wire.json` (450 funcs): `probeTwinSingle`, `probeTwinElect`, `probeTwinTicks` — identical output hashes on both binaries. No decoder path reads a table from anywhere but the wire: the machine's only table reads are `ctx.*` (`grep '\.functions\b'` in the definitional modules → 10 sites, all `findFunctionIn? ctx.functions …`; type reads `types[i]?`/`ctx.types.lookupName?`/`ctx.methods.find?`), and the only other `Program` reads in the core are the two setup seams.

**(f) Fix-round deletions.** For each of the 16 tombstoned declarations, mentions at `5955e55f` outside `StateWf.lean`/`MultiWfSound.lean`: `Cont.itersNormalized`/`Config.itersNormalized` 2 (the `ThreadWf` def `Multi.lean:2482` — deleted with it — and one `MachineSound` comment), every other one **0**; `git grep itersNormalized 5955e55f -- Tests spikes scripts tools` = 0. Inside the two modules every use discharged the constantly-true conjunct (the deltas: each lost hypothesis/`have` is a `Config.itersNormalized … = true`). The 13 tombstone prose lines (`git grep -n itersNormalized -- GoLean` = 13) name the right declarations and the right replacement (`Config.itersNormalized_true`, itself deleted, → nothing). `StateWf.lean` deleted 19 / added 17 in total (`census.txt`); the three non-fix-round deletions (`ExecState.locSup`, `StateWf.funcs_le`, `step_preserves_iters`) have their replacements (`Store.locSup`, `Func.locSup_eq_zero`, —) as the handoff's tombstone list says.

**(g) Coherence.** `inductive Step : Config → Store → Config → Store → Prop` under `variable (ctx : ProgramCtx)` (`Machine.lean:85`, `:4390`): **122 constructors before, 122 after**; no constructor names any context other than the section variable (`grep -E "ProgramCtx|ofTables|ctx'|ctx₁|⟨program"` over the block = 0) — so every rule and every `stepFn` arm take the SAME `ctx`. `StepM` 7/7, `StepE` 2/2 likewise (`Multi.lean:2388–2503`). `stepFn_sound`/`step_complete`/`stepMulti_sound`/`stepM_complete` quantify one `{ctx}` on both sides; `step_complete`'s existential is over `ch ch'` only (table above). The core-audit's 51 required theorems are present.

**(h) Well-formedness and indexes.** `StateWf` never bounded a table INDEX before B7 either (it bounded `Loc`s in the heap and in function bodies); so nothing that was checked is now unchecked. The «context half of the domain invariant» is `Stmt.locSup_eq_zero` — a theorem, not a check, which is stronger than a check. Every table index in the machine goes through an `Option`: `types[i]?` (`Ops.lean:90,427,707,1211,1307,1595`; the `none` arm at `:92` is `unsupported "unknown type index {i} (no entry in the type table)"`, the others fall to a named refusal), `ctx.types.lookupName?`, `findFunctionIn?` (`Syntax.lean:918`, all 10 function reads). No `getD`/`get!`/`[i]!` on a table anywhere in `GoLean/`. Scratch runs (both binaries, identical): a lowered wire with a call's `"func"` rewritten to `nope.Missing` → `{"message":"GoCore function not found: nope.Missing","status":"stuck"}` exit 1; a wire with a `named` type rewritten to `main.Nope` → the decoder's «dangling reference; refused rather than resolved to an index» exit 1. The hand-built out-of-range type index `(.defined 99)` under `ofTables (types := #[])` is pinned by `Tests/GoCoreEval.lean:2814–2820` (the unrecordable-marker key, NOT recorded, NOT exported-only) — unchanged behaviour.

**(i) Totality and escape hatches.** `grep` of the runtime diff for `partial|sorry|axiom|native_decide|unsafe|implemented_by|admit|extern`: the only hit is the pre-existing `partial def initLoop` in `GoLean/ChoiceTrace.lean:708` (outside the core; present at `5955e55f:676`). `grep partial GoLean/GoCore/*.lean` → prose only. `Expr.locSup_eq_zero_all`/`Stmt.locSup_eq_zero_all` are proved by `apply Expr.locSup.mutual_induct`/`Stmt.locSup.mutual_induct` — the functional induction principles Lean derives for the existing structural mutual recursion; no new recursion, no `partial`. Statements: `∀ e, Expr.locSup e = 0` (+ the option/list/keyed/assignee/unseq/select companions), `Stmt.locSup st = 0`, `Func.locSup f = 0`, `funcListSup l = 0` — exactly what retiring `funcListSup σ.functions.toList` from `StateWf` needed. `check-core-audit` EXIT=0 (§0).

**(j) Positional tags.** Re-ran the tracked probe (`probe_s2.lean.txt`, `scripts/capped lake env lean`, EXIT=0, 3 s): 162 goals; my tag/order/hypothesis-count/fingerprint lines are IDENTICAL to the tracked `fun_cases-tags-after-s2.txt`, and tags/order/fingerprints IDENTICAL to the tracked BEFORE file (`probe-tags-receipt.txt`). Sampled 10 named cases in `stepFn_sound` (`MachineSound.lean:473–819`): `case2` → `entry_arm h Step.panicFrameDefer`, `case7` → the B4 abort arm (no `.ok` step), `case43` → the `hplan`/`hgt` unseq arm, `case66` → `stepUnseqEnter_sound`, `case79` → `Step.evalAnd`, `case90` → the `valueAsBool_ok` arm, `case98` → `Step.callValCalleeEnter`, `case134` → `Step.syncStApply`, `case138`, `case147` (`chainNewestRecovered`) — each body's constructor matches the arm its fingerprint names (e.g. `43: last=¬targets✝.size > 2`, `147: last=¬chainNewestRecovered chain✝ = true`), and a moved tag would not have compiled against a different arm's goal. 0 moved.

**(k) Baselines and trace.** Both tracked tails (`gate-tail.txt`, `gate-tail-fixround.txt`) show the identical summary: `cases=3676 pass=3427 fail=249`, `394 case(s) … match baselines/negative-full.tsv`, `DRIFT … (3676 case(s) run):` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]`, `FAIL certificate provenance` (reconciler `C9 HIGH STALE certification: changed dependency build/files/GoLean/CLI.lean`), `FAIL baseline diff`, every other step `ok`, `RESULT: FAIL` — exactly the two 5a-class items, twice, as claimed (F5 on the wall time). My own reproduction: `native-json-run` on `google-search` is byte-identical across binaries (§4 (e)) — the row's red is the stale certificate, not an observation change. Choice trace: 263 ids (1 in 14 manifest rows, the two wave-3 exclusions dropped), `--dump --jobs 6`, main binary vs candidate: **261 rows exported, 1,404 consumption records each, sorted dumps `cmp` EXIT=0 (sha256 `8ca0a808…` both), results TSVs and summaries identical, both runs EXIT=0** (`choice-trace-subset.txt`). This is a subset (261 of the lane's 3,639 rows); the lane's full-corpus byte-identity (23,679 records, `5f901024…`) is consistent with it but not re-run here.

**(l) Scope.** A residual filter over the definitional diffs (`Ops`, `Machine`, `StepFn`, `Multi`, `Race`, `MachineEqb`, `CLI`, `ChoiceTrace`, `EnumDedup`: normalise the expected renames, print what remains) leaves ONLY: the two setup seams (`⟨program⟩`, empty `Store`, the returned `pctx`, the disclosed text), `runFunctionWithContextM`'s `ofTables`, `Store.eqb` heap-only, `ThreadWf`/`MultiWf` (D6/fix round), the context-only helpers losing a store argument (`nilValueMethodWidth`, `dispatchAccesses`, `nilTextFacts`), the `valueEq` example, and F1's literal. No C1 territory (`deliverS`'s pre-op rollback and `raceUpdate`'s pre-store read are unchanged over `Store`; no retention site added — every `(s : Store)` was an `(s : ExecState)`), no C3 (frame list untouched), no `Unseq.lean`/`UnseqGraph` change (not in the diff). The 55 helpers that lost their store binder: `.tmp/unused_store.py` finds **0** whose old body read the heap, allocator or a heap operator through that binder (`unused-store-check.txt`); they read tables only.

**(m) Records.** Recomputed (`census.txt`): 54/0 atoms, 25 lines, 6/0, 11→1 `htypes`, 13 prose `itersNormalized` lines, 13 fixtures, rebase map `git diff 2500b434 73ad798d -- GoLean Tests lakefile.toml lake-manifest.json lean-toolchain` = 0 lines, records commits touch 0 runtime lines — all as claimed; the exceptions are F2–F5. Handoff §4 per-theorem tables vs the actual deltas: consistent (§2). Evidence README exit codes vs tails: consistent. Slice-log entries: consistent with the diffs (the «MachineSound.lean: one history comment gains a closing parenthesis» line matches the 6-line `1fafc9f2` hunk).

**(n) Performance.** F9 (`perf.tsv`).

**(o) The charter's promises.** §5 item 1 (zero drift, byte-identical trace): confirmed on my subsets and by the tails. Item 2 (no wire change, no semantic change, no weakening, totality): confirmed (§4 (e), §2, §4 (i)); refusal texts «byte-preserved» — F1. Item 3 (Stage C's `Stmt.unseq`/`UnseqGraph` untouched): `Unseq.lean` not in the diff; `Syntax.lean` docstring only. Item 4 (nothing of C1/C3/P touched, no retention site added): confirmed (§4 (l)). §8 exit evidence: gate lines (F10 on «every»), census 48→0 (confirmed), `SameContext` 52→0 (left with the parked family; 0 in tree), positional tags 0 (confirmed), the arc landing row + master-plan `LANDED` (present, `git diff` of the two docs), `Platform.lean` docstring corrected to D1 (a) (present), `BooleanStore.lean` comment (n/a — parked), the handoff with tombstones/choices/PENDING items (present; F1, F6 gaps).

## 5. What I did NOT check (skipped or out of reach)

- A full `scripts/ci` / `ci --diff` run (would take the box-wide lock; the two tracked tails were read instead — F5 notes the one number they cannot confirm).
- The full-corpus choice trace: 261 rows re-run of 3,639 (subset byte-identical); the lane's 23,679-record identity is not independently reproduced in full.
- Proof INTERNALS: statements only, as the brief asked; the kernel checked the proofs at the build (`core build (warning-free)` ok in both tails; my warm build no-op EXIT=0; `check-core-audit` EXIT=0).
- The `--slow` re-enumeration of the one certified row (train step 5a's job), and the certificate-provenance reconciliation itself.
- Every one of the 162 arm/tag pairs by hand: 10 sampled; the other 152 rest on fingerprint identity + the compile.
- The full structural decode dump of every corpus wire (no CLI dump exists): 39 rows + the twin were RUN and compared; decoder byte-identity carries the rest.
- Timing under cgroup isolation: 3–5 runs on a shared box; differences under ~8% are not evidence.
- The D3 parking, the master plan's broader rows, and anything on `park/*` branches.
- `spikes/i1-declarations` was not built (it is outside the lakefile; F6 is about the record, not a build).

## 6. Summary line per finding

| # | severity | one line | file:line | disposition (PROPOSED) |
|---|---|---|---|---|
| F1 | RECORDS-CLAIM (+NIT) | third refusal text changed byte-wise, undisclosed; sed hit inside a string; unreachable | `GoLean/GoCore/Machine.lean:3734` | revert the literal (recommended) or disclose + re-pose — PENDING [USER] |
| F2 | RECORDS-CLAIM | runtime commit is 34 files/+3,232/−2,862, not 32/+3,058/−2,862 | handoff §1; evidence README | correct |
| F3 | RECORDS-CLAIM | `ExecState` was in 31 files (29 code), not «30 modules» | handoff §3; README | correct |
| F4 | RECORDS-CLAIM | `itersNormalized` count spelled 199/198/196/195 | README; commit `1fafc9f2`; slice log | pick one |
| F5 | RECORDS-CLAIM | first gate's 1068 s not in the tracked tail | `gate-tail.txt` | note as lane-side |
| F6 | SCOPE/RECORDS | `spikes/i1-declarations` names `ExecState`, not recorded as dark | `spikes/i1-declarations/Prototype.lean:69,76,90` | one records line |
| F7 | NIT | `MachineEqb.lean` `variable (ctx)` + 37 toggles, zero uses | `GoLean/GoCore/MachineEqb.lean:38` | delete |
| F8 | NIT | congr trio restated as the one-context specialisation; two-context content unrecorded | `MachineSound.lean:1490,1995,2152` | none required; taste — PENDING [USER] |
| F9 | PERFORMANCE (positive) | dedup rows 3.7–5× faster; setup `StateWf` no longer walks bodies — a second removed cost, unrecorded | handoff §9 | add a line |
| F10 | RECORDS (minor) | «every explicit-target warm» → representative lines | evidence README | accept or list |
