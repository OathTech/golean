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
| S1 | the memory module + cost A (root-first in-place `storeLoc`, linear normalizers, `Store.alloc` normalizes, `HeapNormal` as a `StateWf` conjunct, `step_preserves_wf` re-proved) | (SHA at commit) | checkpoint `ci --diff` EXIT=1 (720 s) at zero drift; S1 gate: `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (09:06:02–09:17:37 UTC): **EXIT=1, 695 s**; **3676 cases: 3427 PASS / 249 expected FAIL**; `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit` ok; `frontend pins` ok; `wire boundary` ok; every other step ok. RED: exactly the two 5a-class items — `certificate provenance` (C9 HIGH: «STALE certification: changed dependency build/files/GoLean/CLI.lean») and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` — the one cached certified row, judged stale because compiled semantic inputs changed. ZERO other drift. Tail: `gate-tail-s1.txt`. Choice trace vs main: BYTE-IDENTICAL (23,685 records, `cmp` EXIT=0; §2). |

## 2. Gate lines (captured `EXIT=`; the tails in the evidence README)

| run | command | exit | wall s | tree | result |
|---|---|---|---|---|---|
| S0 warm | `LEAN_NUM_THREADS=4 GOLEAN_MEM_MAX=32G scripts/capped lake build GoLean.GoCore` (after the `Store.lean` touch) | 0 | 105 | `68b261e6` + S0 edits | 33 jobs, 0 warnings |
| S0 full build | `LEAN_NUM_THREADS=4 GOLEAN_MEM_MAX=32G scripts/capped lake build` | 0 | 6 | same | lib + exe up to date |
| S1 checkpoint gate | `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (08:42:01–08:54:01 UTC), representation change WITHOUT the `HeapNormal` conjunct | **1** | **720** | S0 tip + the S1 runtime edits (stage 1) | 3676 cases: 3427 PASS / 249 expected FAIL; red ONLY on the expected 5a pair (`certificate provenance` STALE on `Machine.lean`; the one cached certified row); ZERO other drift — `alloc`-normalizes moved no row. Tail: evidence `gate-tail-s1-checkpoint.txt` |
| S1 gate | `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (09:06:02–09:17:37 UTC), the committed S1 tree | **1** | **695** | S0 tip + the S1 runtime edits | 3676 cases: 3427 PASS / 249 expected FAIL; red ONLY on the expected 5a pair (`certificate provenance` STALE on `CLI.lean`; the one cached certified row); ZERO other drift. Tail: evidence `gate-tail-s1.txt` |
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
| dead write-path primitives | `arraySet`, `StructFields.set` and their six lemmas left in place, dead | delete now | deletion is a runtime edit that would re-gate S1; S2 re-gates these files and tombstones them — recorded as owed |

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

## 6a. What S1 proved, what it owes

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

## 6b. S2 as this lane now sees it (plan of record for the next session)

- `AccessTrace := List (AccessKind × ShadowKey)` (Race.lean's atoms unchanged);
  `stepFn ctx s c ch : Except Stop (Config × Store × Choices × AccessTrace)`; `Step`
  carries the trace as a LABEL (D5 (a)); every apply/entry helper that reads or writes
  user memory returns its trace (`applyStrictOp`, `applyStmtOp`, `storeTarget`,
  `mapAssignValue`, `loadMany`, `mapRangeStartSets`, `mapIterLiveEntries`,
  `sliceVisibleValues`, `dynamicDispatch?`'s deref, `unseqLoad`, `applyChanOp`
  (chanObj), `applySyncOp` (syncWord: today's `syncEntryKinds`/`syncReleaseTailKinds`
  computed INSIDE from `pre`/`post`), `applyAtomicOp` (the atomic kinds at the cell)).
  The load's narrowing (`projChainTarget`) is the CALLER's choice at `evalVar`/`deref`
  (`loadFor`), never an emission.
- `StepEvent.trace` + the pre-state facts `raceUpdate`'s HB arms read today (the
  channel payload's `(buf.size, cap, closed)` at the op's channel, the partner's
  blocked shape, the sync primitive pre/post) carried in the event; `raceUpdate`
  becomes: fold `ev.trace` through `RaceState.accessKeys`, then the clock moves driven
  by `ev.action` + the carried facts — `sPre`/`tsPre` gone (cost B(a)).
- THE TRACE-EQUALITY AUDIT before any deletion: a `golean` mode beside
  `scripts/choice-trace-corpus` running BOTH accounts per step (the new trace vs
  `stepAccesses ctx s c` as a multiset, and the sync/chan emissions vs the arms'
  records) over the whole corpus + the raft twin; every difference a finding (D7;
  BUG-111's class is expected EQUAL — no corpus row aliases across goroutines).
  Then `accesses_eq_stepAccesses` per arm (D6), the table family deleted (54/6/5 → 0),
  `Race.lean:1-256` → the module's `peek` list.
- Emission keys stay STRUCTURAL (`.data l` as today) unless BUG-111 is ruled; the
  canonical-key alternative is one function at the emission point.

## 7. Where the lane stopped; the next command

S1's gate is running on the committed-to-be tree; then the AFTER benchmark, the records, the S1 commit. Next: S2 (the trace). Previously: S1 (`GoLean/GoCore/Store.lean` grown into the module: the
root-first leaf write with the `Array.modifyM` discipline and a STRUCTURAL field
search, linear `normalizeListWith`/`normalizeFieldsWith`, `alloc` normalizes,
`HeapNormal` as a `StateWf` conjunct, `step_preserves_wf` re-proved).
