# B7 work charter — fixed context / mutable store, re-briefed under the 2026-09-11 ruling

[AGENT] planning worker, lane `plan/b7-context-store-0916`, 2026-09-16, at main `6793943c`; records only, no lake/lean run. The brief
for the B7 implementation lane and a DESIGN GATE: the [USER] reads it before dispatch. It re-briefs `docs/2026-09-06_b7-context-store-
design.md` (the "09-06 design") — reused BY SECTION, its typed-consumer-sprint framing dropped — and assesses the previous B7 build
`85f9abd7` for salvage (§6). Every code anchor is `file:line` at `6793943c`, read for this note. Nothing here rules on a [USER] matter; §9 lists what is open.

## 1. Authority and objective

Authority ([USER] Mike, 2026-09-11, verbatim, relayed by the [AGENT] coordinator — cite as relayed): «okay, I am still concerned
that we are not focusing our energy on actually making the *go semantics* as good as possible. We don't have as of now a customer.
Our job is to make the Go seantics as good as we can make it. Nothing else. We can do limited spikes to try to validate our
choices, but our top level goal is to make the semantics good. We should prioritize high value efforts, like cleaning up the
handling of state, and making the semantics structure regular. We *can* provide a relational definition along with it too.
Everything else should be dropped». Recorded in `docs/2026-09-11_review-dispositions.md` §0/§4: B7 is step 3 of the agreed sequence
("B7, then C1"), done for its own sake, relation and coherence proofs moving in step, under the hygiene arc's six invariants
(`docs/2026-09-03_design-hygiene-arc.md`) and the review's caution against the refactor as evidence (`2026-09-11_project-review.md` §13).

**Objective, in the semantics' own terms.** `ExecState` (`GoLean/GoCore/State.lean:77-97`) carries five tables that never change
during a run (`types`, `functions`, `methods`, `methodSets`, `typeDisplays`, copied verbatim from the decoded `Program` at setup)
beside the one thing that does (`heap`). Because the type does not say so, the well-formedness network re-proves at every step that
the program did not change: 38 conjuncts `σ'.types = σ.types ∧ σ'.functions = σ.functions ∧ …` in `StateWf.lean`, 6 in
`MultiWfSound.lean`, 4 `htypes : σ₂.types = σ₁.types` hypotheses in `MachineSound.lean` (48 sites, anchored in §4), plus `SameContext`
(`BooleanStore.lean:189-190`; 52 mentions in 17 `Boolean*`/`Recovery*` modules) and `Extension.context` (`BooleanInvariant.lean:
23-26`). B7 splits the record into an immutable `ProgramCtx` and a `Store` that is the heap; all 48 + 52 + 1 sites vanish BY TYPE.
`StateWf` becomes a heap-only bound — its program-text term `funcListSup σ.functions` (`StateWf.lean:578-579`) is identically zero
since A4 (`StateWf.lean:41-48`) and leaves with the functions; the relation's domain invariant is `ctx`-indexed, its context half
checked once at setup, never preserved per step; `Store` is the one named seam C1 redesigns. **Execution cost, honestly:** B7 is a
re-packaging. It touches neither cost A (whole-root re-normalization) nor cost B (the heap copy under pre-step retention) of
`docs/2026-09-11_bug090-rediagnosis.md` §3 — both are C1's; it removes only `ExecState.eqb`'s five-table walk at heap-equal enumerator
nodes (`MachineEqb.lean:816-822`). B7 claims NO fidelity progress: zero corpus rows move, or the slice stops.

## 2. The field classification (`ExecState`, `State.lean:77-97`, and what is deliberately not in it)

| field / datum | anchor | side | note |
|---|---|---|---|
| `types : TypeEnv`; `functions : Array Func` | `State.lean:82`, `:83` | CONTEXT | `= Program.typeDefs` (C2's index-keyed table), `= Program.funcs` (bodies enter the configuration at `enterFrame`); `Program.globals` (`Syntax.lean:902`, read once by `seedGlobals` `StepFn.lean:993`, today dropped after seeding) becomes merely reachable — nothing reads it post-seed |
| `methods`; `methodSets`; `typeDisplays` | `:84`, `:90`, `:95` | CONTEXT | `= Program.methods`; fail-closed default `#[]` kept on the ctx; panic-text rendering only |
| `heap : Heap` | `:96` | STORE | the only mutable field; `nextAddr` is derived (`:101`) and stays derived |
| choice tape `Choices` | `State.lean:189-202` | PARAMETER | already external («oracle-free states»); stays a parameter of `stepFn`; NOT open |
| program output (`Readout.output`, `State.lean:103-114`); `RaceState` (shadow, clocks) | `StepEvent.out` folded by the driver — G-OUT RULED [USER]; `Race.lean:877`, threaded by `execProgLoop` `Multi.lean:2163` | DRIVER data | both stay driver-side; C1 replaces the detector's input (`Race.stepAccesses`, `:1577`) |
| `MultiConfig.threads`, `.cur` | `Multi.lean:254-257`; `Thread` `:179-181` | pool CONTROL | stays in `MultiConfig` beside `shared : Store` (§9 D4) |
| `Cont.unseqK`'s `status`/`targets`/`env`/`phase` | `Machine.lean:2747-2748` | CONTROL | continuation-owned (Stage B handoff §2); its binder cells are ordinary STORE cells declared into the source scope |
| `Platform` (`platform := gcAmd64`) | `Platform.lean` | OPEN | a global constant, read at `Value.lean:53`, `Ops.lean:339/342/345/438`, `FloatBits.lean` (4), `RecoverySetup.lean` (1); §9 D1 |

## 3. The target API (09-06 design, "Concrete target API", reused; deltas listed)

```lean
structure ProgramCtx where program : Program          -- shape: §9 D2 (recommended (b)); platform field: §9 D1
structure Store where heap : Heap                     -- C1's stable name; `Store.nextAddr s := s.heap.size`
stepFn (ctx : ProgramCtx) (s : Store) (c : Config) (ch : Choices) : Except Stop (Config × Store × Choices)
Step (ctx : ProgramCtx) : Config → Store → Config → Store → Prop;  StepM (ctx) : MultiConfig → MultiConfig → Prop  -- shared : Store
```

Deltas from the 09-06 text: (i) NO `platform` field unless D1 rules otherwise (its "Platform threading" section deferred whole);
(ii) the Iris wrapper and the `spikes/*` row DROPPED with the framing (§10); (iii) `runProgramSetupM` RETURNS the ctx it built — one
ctx for setup, run, observation and readout; no core operator selects a default; (iv) pure context readers (`typeDisplay?` `Ops.lean:741`,
`normalizeValueForTy` `:1226`, `valueEq` `:1889`, …) take `ctx` or the smallest table they need; heap readers/writers (`loadLoc`/
`storeLoc` `:1335`/`:1367`) take the store, plus `ctx` only where they normalize or check tags (census: S0, §7); (v) allocation
(`State.lean:538-543`) needs no ctx and keeps its no-normalize hole byte-identical (C1 §5 item 1's); (vi) threading idiom as in the
previous build: `variable (ctx : ProgramCtx)` per module. Stage B's frame is control; only `Race.unseqRunAccesses` (`Race.lean:1532`)
and `UnseqSound`'s state binders re-type.

## 4. What the existing contracts become (09-06 design's table, restated without the framing)

| surface | at `6793943c` | after B7 |
|---|---|---|
| `stepFn` `StepFn.lean:247`; `Step` `Machine.lean:4354`; `Trace` `Trace.lean:10-14`; `runConfig` `:871`; `stepFn_sound` `MachineSound.lean:469`, `step_complete` `:815`, `step_complete_any_wf` `:3275`, `stepFn_consumption_none/some` `:4468/:4856` | over `ExecState` | gain `ctx`, same content; result triples cannot carry a changed program; 0 positional tags expected to move (a leading parameter does not renumber `fun_cases` arms — VERIFIED by the probe Stage B used, handoff §2 last row) |
| `StateWf` `StateWf.lean:673-674`; `MachineWf` `:683-685` | `ExecState.locSup σ ≤ σ.nextAddr`; `∧ Config.itersNormalized σ.types c = true` | `Heap.locSup s.heap ≤ s.nextAddr` (program-text term proved 0, deleted — the A4 debt); the `itersNormalized` conjunct DELETED (certificate `Config.itersNormalized_true`, `StateWf.lean:663` — a restatement, §9 D6); `MachineWf ctx s c` |
| helper-preservation lemmas — 38 sites `StateWf.lean:1869–6041`, 6 sites `MultiWfSound.lean:102/146/172/195/641/1086`; `step_preserves_wf` `StateWf.lean:7014`; `*_congr` lemmas `MachineSound.lean:1475/1485/1991/2149` (4 `htypes`) | conclude `… ∧ σ'.types = σ.types ∧ …`; assume `htypes` | conclude `StateWf s' ∧ <bound>`; one `ctx`, no hypothesis — the equalities gone by type |
| pool: `MultiConfig` `Multi.lean:254-257`, `stepMulti` `:1495`, `StepM` `:2406`, `stepMulti_sound` `MultiSound.lean:1172`, `stepM_complete` `:1316`, `MultiWfSound`, `MultiStreams`, `NPDRF`; detector `Race.stepAccesses` `:1577`, `dispatchAccesses` `:642`, `projChainTarget` `:572` | `shared : ExecState`; `(s : ExecState)` | `shared : Store`; every pool operator and theorem takes `ctx`; `raceUpdate` (`:1832`) takes `ctx` + the pre-store — its retention (bug090 §3 B(i)) UNCHANGED, C1's; the detector takes `ctx` where it consults functions/methods, `Store` where it loads; footprints byte-identical |
| enumerator `ExecState.eqb` `MachineEqb.lean:816-822`; node hash `EnumDedup.lean:107-108`; `DedupCert`/`EnumSpec`/`EnumDedupSound`; `ChoiceTrace.lean` facts (`seqFacts` `:510`, `poolFacts` `:569`) | walk five tables when heaps agree; `(s : ExecState)` | `Store.eqb` heap-only; node = `MultiConfig × RaceState` unchanged; `ctx` passed once; certificate fingerprints unchanged in meaning; facts take `ctx` + `Store` |
| setup seams `runProgramSetupM` `StepFn.lean:1086-1115`; `CLI.enumSetup` `CLI.lean:791-824`; the hand-built-tables entry `runFunctionWithContextM` `StepFn.lean:894-897`; decoder `decodeProgram` `NativeToIR.lean:1996` | build `ExecState` from `Program` (or bare tables), seed, assert `StateWf s₀` (`:1108`); decoder yields `Program` | build `ctx`, seed a fresh `Store`, assert the store bound and any ctx fact ONCE, by name, at this seam; the shared step ORDER (find → arity → reserved prefix → seed → init shape) unchanged; decoder UNTOUCHED — it already produces the context record (wire-neutral by construction) |
| `Boolean*`/`Recovery*` (56 modules, 8,197 lines; in the default build via `GoLean.lean` → `Interface.lean`); hand-built fixtures (`Tests/GoCoreEval.lean` ≈16 states, e.g. `:2772`, `:2961-3004`; `Tests/InterfaceContract.lean:58, :96`) | `SameContext` (52 sites), `Extension.context`; `{ types := … }` | `SameContext` deleted (true by type); `Extension` keeps `heap`/`size`; predicates over `Store` — IF kept in the build (§9 D3); fixtures on a hand-built `ctx` + empty `Store`, defaults preserved so fail-closed hand-built behaviours (no record → refuse; no display → marker) are byte-identical |

## 5. Scope and invariants (the arc's six, applied)

1. **Zero baseline drift is THE regression**: `scripts/capped scripts/ci --diff` on the assembled tree; a changed row is STOP-and-
   report, never a re-pin; the whole-corpus choice trace byte-identical. Expected non-drift red: `certificate provenance` STALE
   because `CLI.lean` compiles into the binary — the train's step 5a (`ci --slow`), as at Stage B.
2. **No wire change** (`NativeToIR.lean`, `tools/nativefrontend`, `scripts/check-frontend-pins` untouched). **No semantic change**: a
   wrong answer exposed by a proof or the differential is NOT absorbed — the slice stops, a BUG is filed with a red-first pin row, the
   fix is REFERRED to the [USER] (BUG-088 is the precedent). **No weakening, totality kept**: no `sorry`/`axiom`/`native_decide`; no
   `partial` in `GoLean/GoCore/`; lemmas restated arm-for-arm (a statement that cannot be re-proved STOPS the slice), deletions tombstoned.
3. **One core writer.** The lane owns `GoLean/GoCore/**`, `GoLean/CLI.lean`, `GoLean/ChoiceTrace.lean`, `GoLean/EnumDedup.lean`,
   `GoLean/Interface.lean`, `Tests/**`. Stage C's decoder/emitter work (`docs/2026-09-16_evaluation-order-model-v2.md` §7: beside B7
   only under explicit file ownership) may run in `GoLean/NativeToIR.lean`, `tools/nativefrontend/**`, `Corpus/**` and NEW test
   modules. B7 must not break for Stage C: `Stmt.unseq`/`UnseqGraph` (no `Syntax.lean` constructor touched), `UnseqGraph.wellFormed?`,
   `unseqAtom`, `unseqReadTarget`, `Race.unseqRunAccesses` keep meaning and refusal texts.
4. **Left to C1** (`bug090-rediagnosis.md` §5): leaf-cost path writes, linear normalization, unique ownership across a step (the
   `deliverS` pre-op rollback `StepFn.lean:52-57`; `raceUpdate` reading `m.shared` after `stepMulti m`, `Multi.lean:2186/2196`),
   allocation-time normalization, cell granularity (PENDING [USER] there), the map key index, the access trace replacing `Race.lean`'s
   table. B7 must not ADD a retention site. **Left to C3**: the frame list. **Left to P**: method promotion.

## 6. The previous B7 build (`85f9abd7`) — salvage assessment

The coordinator's 2026-09-07 snapshot of the dirty `typed-context-store` worktree over `ca1e01d5` (sprint branch; merge-base with
main `47195683`; main is 68 commits past it). Never committed as B7; its handoff (`85f9abd7:docs/2026-09-06_b7-context-store-
handoff.md`) says «not ready to merge» and ends with the full `ci --diff` still RUNNING — NO zero-drift record exists. 391 files,
+348,351/−5,732: `docs/evidence/` 162 files / 324,902 lines; `B7Reference/` 51 files (~13k lines, the frozen before-model +
correspondence proofs); `GoLean`+`Tests` 82 files +4,682/−4,639 (core/driver/test 38, `Boolean*`/`Recovery*` 44); `spikes/iris-customer` 22.
**(i) File-level reuse.** REUSE AS-IS: `GoLean/GoCore/Store.lean` (70 lines; exactly §3's `Store`, refusal texts byte-preserved) and
`GoLean/GoCore/ProgramCtx.lean` (20 lines; §3/D2 (b) plus a `platform : Platform := gcAmd64` field — D1 (b) only). REUSE AS THE MAP
(hunks conflict, pattern reusable): `variable (ctx : ProgramCtx)` in 62 modules; the cleanup pass's inventory — 37 `Ops` helpers and
11 `Machine`/`Race` wrappers lose the unused `Store`, 60 reflexive context fields removed, `htypes` 0 and `SameContext` 0 in
`GoLean/` (grep-confirmed); the `Boolean*`/`Recovery*` migration (if D3 (a)). NOT done there, owed here: `Store.locSup` still carries
`funcListSup ctx.functions`; `MachineWf` keeps the vacuous conjunct. STALE: every hunk against `Machine`/`StepFn`/`MachineSound`/
`StateWf`/`Multi*`/`Race` — the snapshot predates Stage B (no `Unseq.lean`, `Cont.unseqK`, `unseqNext`), the panic-text tape
(`repanicCollapse` absent), `PanicText.lean` and method identity (`35bea1e8`); main's drift since the merge-base in the 36
core/driver/test files it touches is +2,962/−257 (MachineSound +590, Machine +580, StateWf +285, StepFn +142). DROPPED WITH THE
FRAMING: the Iris wrapper, `spikes/iris-customer`, the customer-migration note, the 324,902-line evidence bundle (the 2026-09-07
ruling); `B7Reference/` + the kernel-sharing scripts unless D5 (b). **(ii) Measured conflict probe** (this worktree at `6793943c`;
`git diff ca1e01d5 85f9abd7 > .tmp/b7-wip.patch`, 371,675 lines; `--check` only — nothing applied, tree verified clean after): plain
`git apply --check` EXIT=1, 38 files fail, 20 in `GoLean`/`Tests` — the 14 core/driver files (`Machine`, `MachineSound`, `StepFn`,
`Ops`, `Race`, `Multi`, `MultiSound`, `MultiStreams`, `NPDRF`, `EnumDedup`, `EnumDedupCheck`, `EnumDedupSound`, `CLI`, `ChoiceTrace`) +
2 `Tests` + 4 `Recovery*`; `git apply --check --3way` EXIT=1, 33 files with conflicts, 18 in `GoLean`/`Tests` (the same 14 + 4
`Recovery*`). The other 62 `GoLean`/`Tests` files apply cleanly — but applying is not building (main's Stage B lemmas still name
`ExecState`). **(iii) Recommendation [AGENT]: REPLAY the design slice
by slice with the snapshot open as the reference** — `Store.lean`/`ProgramCtx.lean` taken as files (modulo D1), the per-file map for
the rest. Why: the 14 densest core files conflict and their main-side drift is Stage B's, which the snapshot cannot know; it has no
gate record and is a crash-recovery capture of a dirty tree, so a rebase would land one ~4.7k-line change whose zero-drift claim
starts from nothing anyway; replay keeps D1/D3/D5 decidable rather than inheriting the snapshot's answers (it bakes in D1 (b), D3 (a),
D5 (b)). Alternative, named: REBASE-AND-REPAIR — apply 3-way, resolve the 18 files, re-thread Stage B, the tape and method identity on
top; cheaper ONLY if D1 (b) + D3 (a) + D5 (b) are all chosen; same one gated runtime commit. PENDING [USER] (D8). **(iv) Prior
reviews, what still applies.** `ae96cb32:docs/evidence/2026-09-06_b7-original-independent/REVIEW.md`: a BOUNDED pass for the
correspondence STATEMENTS at frozen before `761d4e28` only — «these equations do not establish equivalence across a corrected wrong
answer»; Stage B, the tape and method identity are such changes, so NO equivalence claim transfers. Sprint handoff row 4
(`docs/2026-09-05_typed-consumer-sprint-handoff.md:88`): the V1 kernel-sharing completeness claim WITHDRAWN, V2 not independently
replayed, the 4,356-root diagnostic FAILED — the caution behind D5. Its four C1-facing findings (raw path writes normalize siblings;
map payload stores need not keep the id counter monotone; the detector fold owes more than `stepAccesses`; HOLE=0 is weaker than
the detector gate) go to C1. BUG-090's capture gap is not waived.

## 7. Implementation order (09-06 "Kernel correspondence and reviewable implementation order", minus Platform, Iris, I1)

A `State.lean` edit is INTERFACE-HOT: every core module imports it. Each work slice is verified by an explicit-target warm build
(`scripts/capped lake build <module>`, ≤48G, exempt from the box lock; captured `EXIT=`, never grepped greens); the FULL gate
(`ci --diff`, box-wide lock, capped) runs once the tree is green — since `GoLean.lean` roots `Interface.lean` and `CLI.lean`, only after
S1–S5. The runtime lands as ONE gated commit (Stage B's shape), a snapshot ref (`refs/snapshots/b7/<slice>`) after each slice.

| slice | files | done when |
|---|---|---|
| S0 census + probe (records) | none edited | the context-read census reproduced by recorded greps (at this tip: `Ops.lean` 24×`.types`, 4×`.methods`, 4×`.functions`, 1×`.methodSets`, 1×`.typeDisplays`; `Machine.lean` 6×`.types`, 1×`.functions`; `StepFn.lean` 1×`.functions`; `Race.lean` 2×`.functions`) and the hypothesis count (§1); a `fun_cases` tag probe of `stepFn`; the MEASURED wall of `lake build GoLean.GoCore` after a whitespace touch of `State.lean` — the number every estimate is conditional on |
| S1 records | `State`, `Store` + `ProgramCtx` (from `85f9abd7`, modulo D1), `StateEqb`, `StateWf`, `MachineEqb` | `Store.locSup` heap-only with the `Stmt.locSup = 0` lemma; `MachineWf` restated; `Store.eqb`; explicit-target build `EXIT=0` |
| S2 sequential machine | `Ops`, `Machine`, `StepFn`, `MachineSound`, `Unseq`, `UnseqSound` | ctx threaded per the snapshot's map; the 42 `StateWf`/`MachineSound` sites gone; `stepFn_sound`/`step_complete*`/consumption re-proved; tag probe: 0 moved |
| S3 pool + traces | `Race`, `Multi`, `MultiSound`, `MultiWfSound`, `MultiStreams`, `NPDRF`, `Trace`, `PoolTrace`, `ProgramTrace`, `AbortObservation`, `StringPanic`, `PanicText`, `Admission*` | `shared : Store`; the 6 `MultiWfSound` sites gone; footprints unchanged |
| S4 enumerator + CLI | `EnumSpec`, `EnumDedupCheck`, `EnumDedupSound`, `GoLean/EnumDedup.lean`, `ChoiceTrace.lean`, `CLI.lean` | the setup seams build one ctx; `DedupCert` carries it once |
| S5 fixtures, then the gate and records | `Boolean*`, `Recovery*`, `Interface.lean`, `Tests/**`; `docs/` | `SameContext` 52 → 0; fixtures on a hand-built ctx; default-target `lake build` `EXIT=0` — then the ONE gate, §8's records, the audit ask |

**Rebuild cost, anchored:** Stage B's warm after edits BELOW `State.lean` measured Machine 4 s, StepFn 17 s (incl. StateWf),
MachineSound 57 s; the gate ran 1,162–1,306 s (`docs/evidence/2026-09-16_unseq-stage-b/README.md`). A `State.lean` edit also
re-elaborates `Ops`, `Race`, `Multi`, the pool proof modules and the 8.2k-line fixture family — no cold number is on record, hence
S0. **Session estimate, CONDITIONAL:** if S0's warm is ≤ 15 min and the tag probe moves 0 arms, S1–S3 fit one session and S4–S5 a
second (2 sessions; the snapshot's map removes design guesswork, not the proof churn against Stage B); +1 session if D3 keeps the
fixture family and its 52 sites are not purely mechanical, or if `step_preserves_wf` (7k lines) needs more than re-typing.

## 8. Exit evidence

- Gate lines (command, captured `EXIT=`, wall, SHA/tree) for every explicit-target warm and the one `ci --diff`, in a SMALL evidence
  dir `docs/evidence/2026-09-XX_b7-context-store/`. Zero drift on the full corpus (row count stated at the fork; 3,676 at Stage B); the
  whole-corpus choice trace byte-identical; the expected 5a-class STALE line named as such. By the recorded grep: field-equality
  sites 48 → 0; `SameContext` 52 → 0; `Extension.context` gone; positional tags moved 0.
- Records in the landing commit (invariant 6): a row in the "Landing record" table of `docs/2026-09-03_design-hygiene-arc.md` (where
  the slices since 2026-09-03 append; `hygiene-slice-log.md` is the 2026-08-28 slice's own log), a `LANDED <sha>` note on the master
  plan's B7 row (`docs/2026-09-05_master-plan.md:498`), the `Platform.lean` "deferred to B7" docstring corrected to whatever D1
  rules, `BooleanStore.lean:187-188`'s "B7 will make this a parameter" comment retired.
- The handoff, a dated `docs/2026-09-XX_b7-context-store-handoff.md` (never the root `HANDOFF.md`): commits, gate lines, [AGENT]
  choices with alternatives, tombstoned lemmas, what was taken from `85f9abd7`, what C1 inherits, PENDING [USER] items. Then the
  pre-merge adversarial audit ask, unconditional; scope and waiver the [USER]'s. No merge, no push.

## 9. Decisions for the [USER] — posed, not ruled; [AGENT] recommendations marked

- **D1 `Platform`.** (a) Stays the A5 global constant in B7; threading it (`IntKind.bits?` `Value.lean:53`, the Ops reads, `FloatBits`,
  the sync-layout literals `Ops.lean:409-412`) is ONE later all-at-once re-envelope lane (latitude R1/R16). (b) `ProgramCtx.platform`
  + full threading inside B7 — the snapshot DID this (`Ops.lean` +220/−216, eight sync fields), so its map lowers (b)'s cost; theorems
  become `∀ p`. (c) Field now, partial threading. **[AGENT] recommends (a)**, REJECTS (c): a ctx whose platform disagreed with the
  global would be half-honoured silently. PENDING [USER].
- **D2 `ProgramCtx` shape.** (a) `abbrev ProgramCtx := Program` (zero duplication; the wire record IS the context). (b) `structure
  ProgramCtx where program : Program` with projections — the snapshot's shape; later context facts land without touching the wire
  record. **[AGENT] recommends (b)**. PENDING [USER].
- **D3 The `Boolean*`/`Recovery*`/`Interface.lean` family** — **RULED [USER] 2026-09-16: (b) PARK**, via the reasoning-repository path
  (record: `docs/2026-08-31_qrow-rulings.md`, «The typed-profile family ruling record (2026-09-16)»): deleted from main by a
  separate parking lane BEFORE B7 starts, preserved at tag `typed-profiles/last-main-2026-09-16` / branch
  `park/typed-profiles-2026-09-16`, future home the reasoning repo under `deps/`. Consequence here: S5 shrinks to `Tests/**`
  and the fixtures; the "+1 session" of §7 disappears; `SameContext` (52 sites) leaves with the family.
- **D4 The pool's per-thread state.** (a) Stays `MultiConfig.threads`/`.cur` beside `shared : Store` (the snapshot's shape too): one
  `Store` type keeps the sequential-conservation transfer literal. (b) Fold threads into the store. **[AGENT] recommends (a)**.
- **D5 Preservation evidence.** (a) The arc's standard: `ci --diff` at zero drift + the byte-identical choice trace + the live
  coherence theorems, this note declaring the formal bisimulation "not cheap" (invariant 5's clause). (b) The 09-06 "frozen
  before-model" correspondence proof — the snapshot's `B7Reference/` is such an apparatus, against a before-model that is no longer
  main's machine, its completeness claim withdrawn (§6 iv). **[AGENT] recommends (a)**; (b) buys no semantics quality. PENDING [USER].
- **D6** delete `MachineWf`'s vacuous `itersNormalized` conjunct in S1 (owed since A8; `Config.itersNormalized_true`, `StateWf.lean:
  663`; the snapshot kept it) — a restatement, flagged because a theorem statement changes; [AGENT] intends to, object here.
- **D7 `spikes/gate-a1`, `spikes/iris-customer`.** Outside the lakefile and gate; they will not build against the new API. Leave dark
  and record, or delete — the [USER]'s. **D8 Salvage route** (§6 iii): REPLAY ([AGENT] recommends) vs REBASE-AND-REPAIR. PENDING [USER].

## 10. What this charter does not do

No C1 work (§5 item 4), no C3, no P, no B6. No I1 (the `unsupported` IR-marker removal the master plan bundled with B7 is a
frontend/decoder lane with wire effect — unscheduled, the [USER]'s). No Platform threading unless D1 (b). No wire change, no baseline
re-pin, no BUG fix (a found wrong answer goes red-first and is referred). No consumer, adapter, interface programme or pin ceremony
(the 09-06 Iris/spikes rows are dropped, not deferred). `85f9abd7` is read, not applied; none of its evidence bundle or before-model lands.
