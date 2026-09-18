# C1 memory module + access trace — lane handoff (2026-09-18)

[AGENT] worker, lane `core/c1-memory-module-0918` (branch of the same name, base
main `68b261e6`), the ONE core writer. The brief is the charter
`docs/2026-09-17_c1-memory-module-charter.md`; its §7 decisions are settled:
D1–D7, D9, D10 RULED by default acceptance ([USER] 2026-09-18, the coordinator's
triage raised no objection — record `docs/2026-08-31_qrow-rulings.md`, «The on-deck
decisions ruling record (2026-09-18)»), D8 RULED [USER] Mike 2026-09-18, verbatim,
relayed by the [AGENT] coordinator — cite as relayed: «We shouldn't delete, hard to
revive that way. Can we just deprecate/ mark unsound for now?». Sequencing ruling
(1): Stage C of the evaluation-order plan follows C1. Evidence:
`docs/evidence/2026-09-18_c1-memory-module/README.md`. Slice entries: the C1 section
at the tail of `docs/hygiene-slice-log.md`.

This document is updated at every slice and is the PARK record: what landed, what is
proved vs owed, the [AGENT] choices with their alternatives, the PENDING [USER] items,
exactly where the lane stopped and the next command.

## 1. What landed, per slice

| slice | content | commit | gate |
|---|---|---|---|
| S0 | records (census, write-then-panic audit, benchmark BEFORE, the §5 spike, warm) + two records-class core edits (D8 marker, D10 wording) | the S0 commit (first commit on the branch after `68b261e6`) | `ci --diff` EXIT=1 (938 s): 3676 = 3427/249, red ONLY on the expected 5a pair (§2) |
| S2a | the DATA trace, both accounts live: the module's emitting operations, the trace as `stepFn`'s 4th component and `Step`/`StepE`/`StepM`/`StepMFine`'s label, `StepEvent.trace`, coherence re-proved (`stepFn_sound`/`step_complete`/`stepMulti_sound`/`stepM_complete` with the label), the tracer's trace-equality audit (0 mismatches over 21,835 (row, stream) results + the raft twin) | (this commit; the SHA is filled in the next records-only commit, as S1's was) | S2a gate: `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (11:17:29–11:29:48 UTC): **EXIT=1, 739 s**; **3676 cases: 3427 PASS / 249 expected FAIL**; `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit` ok; `frontend pins` ok; `wire boundary` ok; every other step ok. RED: exactly the two 5a-class items — `certificate provenance` (C9 HIGH: «STALE certification: changed dependency build/files/GoLean/CLI.lean») and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]`. ZERO other drift. Tail: `gate-tail-s2a.txt`. Trace audit: 21,835 (row, stream) results, 0 mismatches; choice trace vs main BYTE-IDENTICAL (23,685 records, `cmp` EXIT=0) |
| S1 | the memory module + cost A (root-first in-place `storeLoc`, linear normalizers, `Store.alloc` normalizes, `HeapNormal` as a `StateWf` conjunct, `step_preserves_wf` re-proved) | `d7b32f59` (snapshot `refs/snapshots/c1/s1`) | checkpoint `ci --diff` EXIT=1 (720 s) at zero drift; S1 gate: `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (09:06:02–09:17:37 UTC): **EXIT=1, 695 s**; **3676 cases: 3427 PASS / 249 expected FAIL**; `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit` ok; `frontend pins` ok; `wire boundary` ok; every other step ok. RED: exactly the two 5a-class items — `certificate provenance` (C9 HIGH: «STALE certification: changed dependency build/files/GoLean/CLI.lean») and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` — the one cached certified row, judged stale because compiled semantic inputs changed. ZERO other drift. Tail: `gate-tail-s1.txt`. Choice trace vs main: BYTE-IDENTICAL (23,685 records, `cmp` EXIT=0; §2). |

## 2. Gate lines (captured `EXIT=`; the tails in the evidence README)

| run | command | exit | wall s | tree | result |
|---|---|---|---|---|---|
| S0 warm | `LEAN_NUM_THREADS=4 GOLEAN_MEM_MAX=32G scripts/capped lake build GoLean.GoCore` (after the `Store.lean` touch) | 0 | 105 | `68b261e6` + S0 edits | 33 jobs, 0 warnings |
| S0 full build | `LEAN_NUM_THREADS=4 GOLEAN_MEM_MAX=32G scripts/capped lake build` | 0 | 6 | same | lib + exe up to date |
| S1 checkpoint gate | `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (08:42:01–08:54:01 UTC), representation change WITHOUT the `HeapNormal` conjunct | **1** | **720** | S0 tip + the S1 runtime edits (stage 1) | 3676 cases: 3427 PASS / 249 expected FAIL; red ONLY on the expected 5a pair (`certificate provenance` STALE on `Machine.lean`; the one cached certified row); ZERO other drift — `alloc`-normalizes moved no row. Tail: evidence `gate-tail-s1-checkpoint.txt` |
| S1 gate | `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (09:06:02–09:17:37 UTC), the committed S1 tree | **1** | **695** | S0 tip + the S1 runtime edits | 3676 cases: 3427 PASS / 249 expected FAIL; red ONLY on the expected 5a pair (`certificate provenance` STALE on `CLI.lean`; the one cached certified row); ZERO other drift. Tail: evidence `gate-tail-s1.txt` |
| S2a gate | `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (11:17:29–11:29:48 UTC), the staged S2a runtime tree = the committed tree for `GoLean`/`Tests` (snapshot `refs/snapshots/c1/s2a-gated`) | **1** | **739** | S1 tip + the S2a runtime edits | 3676 cases: 3427 PASS / 249 expected FAIL; red ONLY on the expected 5a pair (`certificate provenance` STALE on `CLI.lean`; the one cached certified row); ZERO other drift. Tail: evidence `gate-tail-s2a.txt` |
| S2a trace audit | `scripts/choice-trace-corpus --dump --jobs 6` with BOTH accounts in the S2a binary (`.tmp/golean-s2a`); sorted-dump `cmp` vs main | **0 mismatches**; `cmp` **0**; tracer 1 (the same pre-existing ERROR finding) | 481 | S1 tip + the S2a runtime edits | 21,835 (row, stream) results, `traceMismatches` = 0 everywhere; 23,685 consumption records byte-identical (sha `70e12e02…eb57`). Evidence `trace-audit-s2a.txt` |
| S2a raft twin | `.tmp/twin-audit.sh`: `choice-trace --batch` over `raft-twin/probeTwin{Choice,Single,Elect,Perturb,Ticks}` × 6 streams, S2a binary then main's, sorted dumps `cmp` | **0 mismatches**; `cmp` **0** | 1136 + 1004 | S1 tip + the S2a runtime edits | 30/30 results ok, `traceMismatches` = 0, 0 alarms; 14,360 consumption records byte-identical. Evidence `twin-audit-s2a.txt` |
| S1 choice trace | `scripts/choice-trace-corpus --dump --jobs 6` (2 standing exclusions), main `68b261e6`'s certified binary vs the gated S1 binary `f462cf50…`, then sorted-dump `cmp` | **0 (cmp)**; tracer 1 + 1 (the pre-existing FINDINGS listing, both sides) | 609 + 436 | main vs S1 | BYTE-IDENTICAL: 23,685 records, sha256 `70e12e02…eb57` both sides. Tail: evidence `trace-summary-main-s1.txt` |
| S0 gate | `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (07:10:22–07:26:00 UTC) | **1** | **938** | same | 3676 cases: 3427 PASS / 249 expected FAIL; every step ok EXCEPT the two EXPECTED 5a-class items — `certificate provenance` (C9 HIGH: «STALE certification: changed dependency build/files/GoLean/GoCore/NPDRF.lean») and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]`; ZERO other drift. Tail: evidence `gate-tail-s0.txt` |

## 3. The spike verdict (charter §5)

**PASS.** `spikes/c1-frame/Frame.lean` (914 lines, sha256 `2a510942…13b3`, EXIT=0,
0 errors) proves (a) `arraySet_comm` + `fieldModify_comm` (the candidate's primitives
commute at distinct positions), (b) `isNormalForTyTy_array_set` +
`isNormalForTyAt_struct_set` (the leaf congruence at one `.index` and one `.field`
depth), (c) F1/F2 stated as chartered AND on the canonical relation, with
`f1_canon : F1Canon ctx` PROVED at EVERY depth (the same-root half that NPDRF.lean's
obstruction 6 records as unproved is `readAt_writeAt_disjoint`). The stub is the S1
shape: `Loc.rootPath` (leaf-first `Loc` → root + ROOT-FIRST path), `writeAt`
(`Array.modifyM` at every level), `leafTy`, one `Store.updateCell`; the bridge
`stubLoad_eq_loadLoc` shows the root-first read is today's `loadLoc`.

Three findings, none an obstruction to the representation (details in the evidence
README): (1) F1 as chartered — structural `ShadowKey.overlap` — is FALSE on
struct-tag-compatible field aliases; **BUG-111** (PENDING [USER], §6); (2) F1's
conclusion is agreement on SUCCESSFUL loads, not `Except` equality (wrong-base-kind
refusal texts embed the value); (3) `Array.findIdx?` does not kernel-reduce — the S1
module's field search must be structural.

## 4. The S0 records in one paragraph

Census matches the charter (Machine 18/29, StepFn 1/1, Multi 2/4, Race 2/0, Ops 4/0;
table family 54/6/5; 13 alloc sites; 17 `deliverS` sites + `Thread.afterStep s` +
the drivers' `raceUpdate … m.shared m.threads` = cost B's retention set). The
write-then-panic audit: **N 118 / V 46 / W 8** arms — the reachable W arms are
`.makeMap`/`.makeChan` in their hint-/cap-less forms (payload alloc, THEN the nil
target check — the one-operand arrival skips the nil pre-check, `StepFn.lean:578-591`);
the loop arms (`clearSlice`/`copySlice`/`appendSlice` in place) and `.allocNew`/
`.makeSlice`'s path-target store are W only under a header/backing inconsistency no
`StateWf` conjunct excludes today (S3 states it or reorders). Benchmark BEFORE
reproduced the 2026-09-11 note (write_fixed 21 µs → 107 ms; append_grow 4,000 =
30.4 s; alloc_new 32k = 13.8 s; (h) 0.237 → 6.37 s; 246 ns/step). D8: the
`@[deprecated]` marker + banner on `NPDRFReduction`, zero use sites confirmed, 0 build
warnings. D10: `Store.updateCell`'s `.internal` names `Store.alloc`.

## 5. [AGENT] representation choices so far, with the alternative named

| choice | taken | alternative (not taken) | why |
|---|---|---|---|
| F1's hypothesis in the spike | proved on the CANONICAL relation (`pathsDisjoint`: field steps reduced to their names) and REFUTED as chartered by evaluation | prove F1 as chartered | it is false (BUG-111); the canonical relation is the memory-level one and is what S2's emission should key by — if the [USER] rules so |
| F1's conclusion | agreement on successful loads (`∀ w, load s' m = .ok w ↔ load s m = .ok w`) | `loadLoc s' m = loadLoc s m` | exact equality is false where a refusal text embeds the changed root (`… got {repr other}`); no semantic content is lost |
| the spike's field-position search | `Array.findIdx?` (proof-convenient) | a structural search | disposable code; the S1 module MUST use the structural form (finding 3) |
| the counterexample's form | `#eval` witnesses in the compile log | a kernel-checked `¬ F1` | `Array.findIdx?` blocks `decide`/`rfl`; a kernel proof would need the structural search first (S1) |
| BUG-111's red-first row | PROPOSED in the entry, not added | adding `race/negative/struct-tag-alias-field` now | `Corpus/**` is not the core writer's; the fix is a detector-semantics flip that needs the [USER]'s ruling first (charter §7 D7) |
| the module's home | `GoLean/GoCore/Ops.lean` («The memory module's write path» section) + `Store.lean` for the representation and payload ops | a new `GoLean/GoCore/Mem.lean` | the value-cell operations need the normalizer, which lives in `Ops.lean`; a `Mem.lean` above `Ops` would import the whole type-directed layer for six definitions |
| the leaf's type and bound | `Ty.stepDown` returns `(type, residual bound)`, decrementing per `.defined` hop exactly as `normalizeValueForTyAt`; the leaf is normalized at THAT bound | normalize the leaf with `normalizeValueForTy` seeded at `types.size` | byte-identity with the former whole-root normalization is then DEFINITIONAL at every depth (no bound-monotonicity lemma over `TypeEnv.WellFounded`), and `writeAt_isNormal` is a plain induction |
| the field search | `fieldIdxFrom` (fuel = remaining count) | `Array.findIdx?` | S0 finding 3: `findIdx?`'s loop is well-founded — `decide`/`rfl` pins on the interpreter would stop reducing |
| refusal texts on a path store | LOAD texts on prefix steps, STORE texts on the last (`match rest with`) | one text per arm | byte-identity with the former leaf-first recursion, which loaded the prefix |
| the payload/unbound arms | payload cells: store text at the root, load text under a path; an unbound root under a path: `Store.updateCell`'s `.internal` (was `loadLoc`'s `.stuck`) | a second lookup to reproduce the `.stuck` | one lookup; the path is unreachable by heap density (BUG-085's argument), disclosed as a refusal-CLASS change |
| `MultiWf` | `MultiWf ctx m` again (B7 had made it context-free) | keep `MultiWf m` with `HeapNormal` outside `StateWf` | the charter puts the conjunct in `StateWf`; the type table decides normality, so the context is genuinely read — a restatement, flagged, nothing weakened |
| dead write-path primitives | `arraySet`, `StructFields.set` and their six lemmas left in place, dead | delete now | deletion is a runtime edit that would re-gate S1; S2b re-gates these files and tombstones them — recorded as owed (S2a's gate was already running when the item came up) |
| the vocabulary's home (S2a) | `AccessKind`/`ShadowKey`/`overlap`/`locPrefix` moved into `Ops.lean`'s module section (namespace `GoLean.GoCore`) | a new `Access.lean` | one module owns representation, operations and events (charter §1); `Race.lean` consumes unqualified names through the namespace chain, nothing renamed |
| the emitting operations (S2a) | wrappers `Mem.load/loadFor/store/mapRead/mapWrite/...` over the S1 primitives, which keep their types as the module's peek and raw writers | retype `loadLoc`/`storeLoc` themselves | 62 lemma mentions in StateWf/MachineSound would move for no semantic gain; the standing check that no data-write site calls the raw writer is the S2a audit while the table exists, review after (the same lockstep obligation the table had) |
| `.deref`'s narrowing (S2a) | `applyStrictOp ctx s leafOf op vs`, `leafOf := projChainTarget ctx s k` passed by `Step.strictApply`/`evalStrictNullary` and `stepFn`; only `.deref` reads it | a separate deref rule and `stepFn` arm | one parameter, no new constructor, no positional case-tag shift in `MachineSound` |
| frame-exit reads (S2a) | a new `loadResults` (emitting) for `stepFrameExit`/`frameReturnTargets`/`frameFallTargets`; `loadMany` stays the drivers' peek | retype `loadMany` and drop the trace at every driver site | 8 driver call sites + `ProgramTrace`/`EnumSpec`/`EnumDedupSound` proofs untouched |
| element runs (S2a) | structural `Mem.loadElems`/`storeElems`/`loadRun`/`storeRun`; `sliceVisibleValues := (·.1) <$> Mem.loadSlice` | keep the `forIn` loops and thread a trace accumulator | the `forIn_list_inv` proofs over a triple loop state cost more than the structural inductions (`Mem.storeElems_pres`, `Mem.loadElems_locSup`); byte-identical loads/stores/errors |
| the mirrors (S2a) | `appendSpill?` and `EnumDedupCheck.appendApplyNoSpill` read through `Mem.loadSlice` | bridge `sliceVisibleValues_eq_ok` at every proof site | a mirror mirrors the machine's own op; `sliceVisibleValues_eq_ok` is provided anyway |
| the pool label (S2a) | `StepEvent.trace`; `stepMulti_sound : … → StepM ctx m m' ev.trace`; `stepM_complete … ∧ ev.trace = tr` | `StepM` unlabelled in S2a | D5 puts the label on `StepM`; without the completeness conjunct the label would be vacuous |
| binder cells (S2a) | the table's account kept: binder WRITES emit (`Mem.store`), `unseqStorePlan`'s binder loads peek | no emission on binder cells at all | verdict-neutral either way (machine-internal cells no goroutine can name); the audit's EQUAL is the S2a deliverable — the principled form is S2b/S2c's to take with the table gone |
| `mapDelete` of an absent key (S2a) | rewrite the unchanged payload so the write is emitted | emit nothing (the machine stores nothing) | gc instruments `mapdelete` as a write unconditionally and the table always recorded one; heap content unchanged |

## 6. PENDING [USER]

1. **BUG-111** — the conflict relation misses races on struct-tag-compatible field
   aliases (`p.f` vs `(*B)(p).f`): fail-open vs `-race`, pre-existing, found by the
   spike. Proposed fix (i): key `.data` accesses by the canonical path at S2's
   emission; (ii): normalize the typeId to the cell's mint tag. Either is a `Cases:`
   flip on a proposed red-first row (`race/negative/struct-tag-alias-field`, born-FAIL
   on the wrong side) plus a must-stay-green disjoint-fields guard. The lane proceeds
   with S1/S2 keyed exactly as today (structural) unless ruled otherwise; the
   trace-equality audit (S2) then expects EQUALITY with `stepAccesses` on every row,
   BUG-111's class included (no corpus row exercises it).

## 6a. What S1/S2a proved, what they owe

S2a proved (kernel-checked, warning-free): the labelled coherence — `stepFn_sound` and
`step_complete` with the trace as the fifth `Step` index; `stepMulti_sound` into
`StepM ctx m m' ev.trace` and `stepM_complete` returning `ev.trace = tr`; the consumption
theorems carry the trace stream-independently (the data footprint never depends on the
stream, as Stage B's rule requires); `step_preserves_wf` over the labelled relation. S2a
owes (S2b): `accesses_eq_stepAccesses` per arm (D6) — the executable audit says EQUAL on
every traced step, the theorem is the universal companion, proved at the deleting commit;
the `Race.lean:1-256` inventory → the module docstring's peek list; the dead
`arraySet`/`StructFields.set` family. S2c: the sync-word / chan-object / atomic emissions
(the ORDER design point in §6b) and `raceUpdate` without `sPre`/`tsPre`.

### S1

Proved (kernel-checked, no `sorry`/`axiom`/`native_decide`, warning-free core): the
loc-boundedness family unchanged in statement (`storeLoc_shape/_wf/_pres`,
`storeLoc_root_frame`, `storeLoc_congr`, the noPanic pair) re-derived over the
root-first write; the NEW `HeapNormal` conjunct established (`Store.alloc`) and
preserved (`HeapNormal.of_*`, `writeAt_isNormal`) through `step_preserves_wf`; the
coherence theorems `stepFn_sound`/`step_complete` restated only at the
`initialization` premise (`Store.alloc … = .ok (loc, s')`). Owed (S2): deletion of the
dead write-path primitives `arraySet`/`StructFields.set` and their six lemmas
(tombstones); the disjoint-path frame law on the REAL `storeLoc` (the spike proved it
on the stub of the same shape — `spikes/c1-frame/Frame.lean` `f1_canon`; porting is
S2/S3 work when the trace makes the same-root law a detector statement).

## 6b. S2 — the plan of record after the S1 landing (2026-09-18, [AGENT])

S2 lands as THREE gated runtime commits, each at zero baseline drift and a
byte-identical choice trace — a deviation from charter §6's «one gated
commit per slice» taken for parkability (each sub-commit is a legitimate
stop; the alternative — one 3-session commit with no parkable point — is
named and rejected; [AGENT]):

- **S2a — the DATA trace, both accounts live, the audit.** Vocabulary
  (`AccessKind`, `SyncWordName`, `ShadowKey`, `ShadowKey.overlap`,
  `locPrefix`/`locOverlap`, the `Ord` derivings) MOVES from `Race.lean` into
  the module section of `Ops.lean` (namespace `GoLean.GoCore`; the
  alternative — a new `Access.lean` — named); `Access := AccessKind ×
  ShadowKey`, `AccessTrace := List Access`. The EMITTING operations are
  wrappers over the S1 primitives — `Mem.load l` ([(read, data l)]),
  `Mem.loadFor root leaf` (loads the root, emits at the leaf), `Mem.store l
  v` ([(write, data l)]), `Mem.mapRead l` / `Mem.mapWrite l entries nextId`
  (the map cell as ONE location, gc's classification) — while `loadLoc` /
  `storeLoc` / `mapPayload?` / `storeMapPayload` KEEP their types as the
  module's `peek` and raw writers (the alternative — retyping them — costs
  the 62 `storeLoc`/`loadLoc` lemma mentions of StateWf/MachineSound for no
  semantic gain; [AGENT]). A caller chooses an operation; it never builds an
  `Access`. The trace rides as the LAST component of every emitting helper's
  ok-tuple (`applyStrictOp`, `applyStmtOpCore`/`applyStmtOp`, `storeTarget`,
  `mapAssignValue`, `loadResults` (frame exit; the drivers' `loadMany` stays
  a peek), `mapRangeStartSets`, `mapIterLiveEntries`/`mapIterCandidates`,
  `sliceVisibleValues`, `mapLookupValue`/`applyRhsOp`, `dynamicDispatch?` →
  `enterFrame` → `enterFramePick`, `unseqLoad`/`unseqAtom(s)`/
  `unseqTargetPlan`/`unseqGuard`, `stepUnseqValue`); `deliver`/`deliverS`
  carry it (a delivered PANIC carries `[]` — the access never happened,
  today's `raceUpdate` convention); `stepFn` returns it as the fourth
  component; `Step` gains the label as its fifth index (pure control rules
  `[]`); `StepE`/`StepM` likewise; `StepEvent.trace`. The `.deref`
  narrowing: `applyStrictOp` takes `(leafOf : Loc → Loc)` used by `.deref`
  only, and `Step`/`stepFn` pass `projChainTarget ctx s k` (moved from
  `Race.lean` to `Machine.lean` after `Cont`); the alternative — a separate
  deref rule and arm — named. Peek-class call sites (documented in the
  module docstring): address formation (`indexTargetLoc`, `resolveChain`,
  `applySlice`, `projChainTarget`'s root check, `unseqUnfrozenAnchor?`),
  metadata (`lengthOf`/`capacityOf` on pointer-to-array and channels — U2),
  the map RMW's entry peek before its payload write (`mapAssignValue`,
  `mapDelete`, `clearMap`), `unseqStorePlan`'s binder-value loads (machine-
  internal binder cells — today's table records nothing there and records
  the binder WRITES; the trace keeps that account, EQUAL by construction;
  the principled alternative — no emission at all on binder cells, verdict-
  neutral since no goroutine can name them — is named), driver readouts
  (`loadMany`), pool bookkeeping. One semantic tightening the trace forces
  and the table already asserted: `mapDelete` of an ABSENT key rewrites the
  unchanged payload through `Mem.mapWrite` so the write is emitted (gc's
  `mapdelete` is instrumented as a write unconditionally). The pool steps
  (wake/pair/commit/pass/strip/abort) carry `[]`; the spawn step carries the
  child's dispatch read (attributed to the child by S2b's fold).
  `raceUpdate` is UNCHANGED in S2a (it still folds `stepAccesses`) — zero
  detector drift by construction. THE AUDIT: the tracer (`ChoiceTrace.lean`
  `poolStep`/`initLoop`) compares, per step, the step's `.data` trace as a
  multiset with the table's account under `raceUpdate`'s own rule
  (`privateStep`: `[]` if the goroutine became panicking from a non-panicking
  pre-configuration, else `stepAccesses ctx sPre cPre`; `spawned`: the
  child's `dispatchAccesses`; every other action `[]`; the init phase: the
  same rule on `stepFn`), and alarms `trace-mismatch: …` with (step, who,
  action, both lists); `scripts/choice-trace-corpus` over the whole corpus
  (the standing 2 exclusions) + the raft twin = the audit run; the sync/
  chan/atomic arms' recordings are S2c's audit. Gate: `ci --diff` zero drift,
  choice trace byte-identical, the audit at 0 unrowed differences (BUG-041's
  rows EQUAL; any other difference: BUG + red-first row + [USER], D7).
- **S2b — the fold, the deletion, the theorem.** `raceUpdate`'s data
  recording reads `ev.trace` (data keys; `.spawned child` under the child);
  `accesses_eq_stepAccesses` per arm (D6, up to permutation) proved at the
  deleting commit and recorded with its SHA; the table family
  (`strictOpAccesses`, `stmtOpAccesses`, `dispatchAccesses`,
  `deferEntryAccesses`, `storeTargetAccess`, `unseqRunAccesses`,
  `stepAccesses`, `sliceElemLocs`, `mapAccess`, `targetWrite`,
  `RaceAccess`) deleted with tombstones; `Race.lean:1-256` replaced by the
  module's peek-list docstring; `footprintsConflict`/`RacyFine` (NPDRF)
  restated over the two goroutines' next-step LABELS with
  `ShadowKey.overlap`/`AccessKind.conflicts`; `scripts/detector-soundness
  --select in-scope` re-run — HOLE = 0, other cells unchanged.
- **S2c — D9 and cost B(a).** The sync-word / chan-object / atomic
  emissions move INSIDE the module's operations (`syncStep`, the payload
  ops, `atomic op l`) and `raceUpdate` drops `sPre`/`tsPre` (the HB arms
  read facts carried in the event). OPEN DESIGN POINT found at the S2
  read (2026-09-18, [AGENT]; not decidable by the charter's letter): the
  step's label must preserve ORDER between accesses and the HB hook —
  `syncReleaseTailKinds` is recorded AFTER the release (at the bumped
  epoch; `Race.lean` docstring: the acquirer of that very release still
  conflicts with the plain read, TSan's verdict) and the atomic Load's
  record follows its acquire — so a flat «fold the accesses, then move the
  clocks» changes verdicts on `race/gomem-only/*`. Recommendation: the
  label as an ORDERED list of memory-model events (accesses and the step's
  synchronization actions interleaved in gc's instrumentation order),
  `raceUpdate` = one fold; alternative: two access lists per event (before
  / after the hook). Posed for the [USER] only if the lane cannot take it
  as the smallest-proof option at S2c.

Owed alongside (S2b): the dead `arraySet`/`StructFields.set` + six lemmas
(tombstones); the disjoint-path frame law on the REAL `storeLoc` when the
trace makes the same-root law a detector statement (S2b/S3).

## 7. Where the lane stopped; the next command

S2a COMMITTED at (this commit; the SHA is filled in the next records-only commit, as S1's was) (gated; the runtime tree byte-identical to the gated snapshot
`refs/snapshots/c1/s2a-gated`; the trace audit at 0 mismatches; the choice trace
byte-identical vs main). Next: S2b per §6b — `raceUpdate` folds `ev.trace`,
`accesses_eq_stepAccesses` per arm, the table family deleted with tombstones, the module
docstring's peek list, `RacyFine`/`footprintsConflict` on the labels, the detector-soundness
HOLE = 0 re-run; then S2c. Previously: S1 COMMITTED at `d7b32f59` (gated; the runtime tree byte-identical to the gated snapshot `refs/snapshots/c1/s1-gated`; choice trace byte-identical vs main). Next: S2 (the trace) per §6b — first the read of `Race.lean`'s table family and `StepFn.lean`'s apply helpers, then `AccessTrace` as the `stepFn` result's fourth component and the `Step` label, then the trace-equality audit mode BEFORE any table deletion. Previously: S1 (`GoLean/GoCore/Store.lean` grown into the module: the
root-first leaf write with the `Array.modifyM` discipline and a STRUCTURAL field
search, linear `normalizeListWith`/`normalizeFieldsWith`, `alloc` normalizes,
`HeapNormal` as a `StateWf` conjunct, `step_preserves_wf` re-proved).
