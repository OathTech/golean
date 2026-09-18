# C1 memory module + access trace — lane handoff (2026-09-18)

[AGENT] worker, lane `core/c1-memory-module-0918` (branch of the same name, base
main `68b261e6`), the ONE core writer. The brief is the charter
`docs/2026-09-17_c1-memory-module-charter.md`; its §7 decisions: D1–D7, D9, D10 were
taken as the brief on the **[AGENT] coordinator's reading of the [USER]'s 2026-09-18
non-objection to the triage** — NOT a [USER] ruling (the record cited before,
`docs/2026-08-31_qrow-rulings.md` «The on-deck decisions ruling record (2026-09-18)»,
has no [USER] text on them; corrected at the audit fix round, F1 — the earlier wording
here was «RULED by default acceptance»); **explicit [USER] ratification is REQUESTED at
the merge ask, PENDING**. D8 RULED [USER] Mike 2026-09-18, verbatim,
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
| S1 | the memory module + cost A (root-first in-place `storeLoc`, linear normalizers, `Store.alloc` normalizes, `HeapNormal` as a `StateWf` conjunct, `step_preserves_wf` re-proved) | `d7b32f59` (snapshot `refs/snapshots/c1/s1`) | checkpoint `ci --diff` EXIT=1 (720 s) at zero drift; S1 gate: `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (09:06:02–09:17:37 UTC): **EXIT=1, 695 s**; **3676 cases: 3427 PASS / 249 expected FAIL**; `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit` ok; `frontend pins` ok; `wire boundary` ok; every other step ok. RED: exactly the two 5a-class items — `certificate provenance` (C9 HIGH: «STALE certification: changed dependency build/files/GoLean/CLI.lean») and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` — the one cached certified row, judged stale because compiled semantic inputs changed. ZERO other drift. Tail: `gate-tail-s1.txt`. Choice trace vs main: BYTE-IDENTICAL (23,685 records, `cmp` EXIT=0; §2). |
| S2a | the DATA trace, both accounts live: the module's emitting operations, the trace as `stepFn`'s 4th component and `Step`/`StepE`/`StepM`/`StepMFine`'s label, `StepEvent.trace`, coherence re-proved (`stepFn_sound`/`step_complete`/`stepMulti_sound`/`stepM_complete` with the label), the tracer's trace-equality audit (0 mismatches over 21,835 (row, stream) results + the raft twin) | `7f7c721c` (snapshot `refs/snapshots/c1/s2a`) | S2a gate: `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (11:17:29–11:29:48 UTC): **EXIT=1, 739 s**; **3676 cases: 3427 PASS / 249 expected FAIL**; `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit` ok; `frontend pins` ok; `wire boundary` ok; every other step ok. RED: exactly the two 5a-class items — `certificate provenance` (C9 HIGH: «STALE certification: changed dependency build/files/GoLean/CLI.lean») and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]`. ZERO other drift. Tail: `gate-tail-s2a.txt`. Trace audit: 21,835 (row, stream) results, 0 mismatches; choice trace vs main BYTE-IDENTICAL (23,685 records, `cmp` EXIT=0) |
| S2b-i | the FOLD and the THEOREM (table retained one more commit): `raceUpdate` records the event's LABEL (`RaceState.accessKeys i ev.trace`; the spawn arm the child's label), `RacyFine`/`footprintsConflict` restated over the two goroutines' next-step `StepE` labels, `accesses_eq_stepAccesses` + `spawnStep_trace` PROVED (`GoLean/GoCore/AccessTableEq.lean`, 1496 lines, 60 theorems, kernel-checked, warning-free — the D6 companion; leaves with the table at S2b-ii), `sortSlice`'s operand check made structural (`intElems`), `len`/`cap` of a pointer-to-array fail closed on a non-pointer operand | `6bb1930d` (snapshot `refs/snapshots/c1/s2b1`) | S2b-i gate: `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (12:59:21–13:11:41 UTC): **EXIT=1, 740 s**; **3676 cases: 3427 PASS / 249 expected FAIL**; `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit` ok (new module included); every other step ok. RED: exactly the two 5a-class items (`certificate provenance` C9 STALE on `CLI.lean`; the SINGLE drift line `imported-goose/channel/google-search`). ZERO other drift — the fold moved no verdict. Tail: `gate-tail-s2b1.txt`. Trace audit 21,835 results / 0 mismatches / byte-identical; raft twin 30/30 / 0 / byte-identical |
| S2b-ii | the DELETION: the footprint table family (`RaceAccess`, `sliceElemLocs`, `mapAccess`, `targetWrite`, `strictOpAccesses`, `dispatchAccesses`, `deferEntryAccesses`, `stmtOpAccesses`, `storeTargetAccess`, `unseqRunAccesses`, `stepAccesses`, `RaceState.access/accesses`) and `Race.lean:1-256` gone with tombstones; `AccessTableEq.lean` gone with the table (proving SHA: the S2b-i row); the tracer's table-side audit retired (the two TSV columns); the module's access-discipline docstring (`Ops.lean`, the peek list) in their place; the dead `arraySet`/`StructFields.set` + six lemmas gone; the atomic arm records through `accessKeys` | `6a35dd92` (snapshot `refs/snapshots/c1/s2b2`) | S2b-ii gate: `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (13:36:01–13:48:17 UTC): **EXIT=1, 736 s**; **3676 cases: 3427 PASS / 249 expected FAIL**; `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit` ok (45 modules); every other step ok. RED: exactly the two 5a-class items (`certificate provenance` C9 STALE on `CLI.lean`; the SINGLE drift line `imported-goose/channel/google-search`). ZERO other drift. Tail: `gate-tail-s2b2.txt`. Choice trace byte-identical (21,835 results); raft twin 30/30 / byte-identical |
| fix round | the audit's FIX-FIRST dispositions (`docs/2026-09-18_c1-memory-module-audit.md`, branch `review/c1-memory-module-0918`): **F3 RESTORED** — `Ty.stepDown` descends an identity-normalized declared type (`.interface`/`.bool`/`.string`/`.slice`/`.map`/`.pointer`) to itself, so a path write through such a root is byte-identical to main's whole-root identity normalization (the S1 cut refused it on a `HeapNormal` cell); `writeAt_isNormal_*` and `Ty.stepDown_noPanic` restated (nothing weakened); five pins `Tests/GoCoreContract.lean` `iface_cell_path_write_*`/`slice_cell_path_write_array`; the module docstring corrected. **F7 ADDED**: `scripts/check-mem-callsites` + `scripts/mem-callsites.tsv` (78 reasoned rows) as a static `scripts/ci` step. **F2**: `scripts/detector-soundness` resets the crash-hook files (the «TSan sandbox» story was a runner bug). F1/F6 comment fixes in `Ops.lean`/`Store.lean`/`MultiWfSound.lean` | `16029fa8` (snapshot `refs/snapshots/c1/fixround-wip1` = the pre-commit tree) | fix-round gate: `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (20:18:14–20:32:18 UTC; lock acquired after 0 s), the committed runtime tree `16029fa8` (clean for `GoLean`/`Tests`/`scripts`; `docs/` dirty with the records edits — the negative-diff step notes `git_dirty=true` for that reason): **EXIT=1, 844 s**; **3676 cases: 3427 PASS / 249 expected FAIL** (`differential coverage summary: cases=3676 pass=3427 fail=249`); `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit` ok; **`memory-module raw call-site inventory (emit/peek discipline)` ok — the NEW step, GREEN at this tip (78 rows)**; `unseq scheduler` ok; `frontend pins` ok; `wire boundary` ok; every other step ok. RED: exactly the two 5a-class items — `certificate provenance` (C9 HIGH: «STALE certification: changed dependency build/files/GoLean/CLI.lean») and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` (the one cached certified row). ZERO other drift; the negative baseline matched (394). The binary after the gate's rebuild is byte-identical to the one the detector-soundness matrix and the choice-trace subset ran (`42b7bf1a…`). Tail: `gate-tail-fixround.txt` |

## 2. Gate lines (captured `EXIT=`; the tails in the evidence README)

| run | command | exit | wall s | tree | result |
|---|---|---|---|---|---|
| fix-round gate | `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock, the committed runtime tree `16029fa8` (clean for `GoLean`/`Tests`/`scripts`) | **1** | **844** | `16029fa8` | 3676 cases: 3427 PASS / 249 expected FAIL; red ONLY on the expected 5a pair (`certificate provenance` STALE on `CLI.lean`; the one cached certified row); the NEW `memory-module raw call-site inventory` step GREEN; ZERO other drift. Tail: evidence `gate-tail-fixround.txt` |
| fix-round detector-soundness (OFFICIAL, the fixed tracked runner) | `scripts/capped scripts/detector-soundness --select in-scope --jobs 6 --out artifacts/detector-soundness/fixround-official`, binary `42b7bf1a…` (= the `16029fa8` tree's) | **2** / **2** (the 9 refusals; run 1's pool exit 127 = the worker's mid-run edit, §6 item 2; the clean re-run's pool exit 0) | 1728 + 1729 | `16029fa8` runtime tree | 639 rows: **HOLE 0 / possible-HOLE 0**, agree-DRF 502, agree-race 36, over-refusal 6 (BUG-041 + the five ruled `race/gomem-only/*`), refused 9, uncertified 86 — cell for cell the audit's patched-copy run. Summary: evidence `detector-soundness-fixround-summary.txt` |
| fix-round choice-trace subset | `scripts/choice-trace-corpus --dump --jobs 6 --golean .tmp/golean-{fix,main}` over the auditor's 307 ids; sorted dumps `cmp` | tracer 0 / 0; `cmp` **0** | 43 + 51 | `16029fa8` binary vs main `68b261e6`'s `231df9a9…` | 303 ids, 1,818 (id, stream) lines each side; 2,690 consumption records each, sha256 `bd48dac5…` both — BYTE-IDENTICAL. Evidence `choice-trace-subset-fixround.txt` |
| fix-round warms | `LEAN_NUM_THREADS=4 GOLEAN_MEM_MAX=32G scripts/capped lake build …` — `GoLean.GoCore.StateWf` / `GoLean golean` (1st) / `GoLean.GoCore.MachineSound` / `GoLean golean` / `GoCoreAuditTests` | 0 / **1** / 0 / 0 / 0 (after one `by decide` → `rfl`) | 27 / 59 / 58 / 20 / 3 | the fix-round runtime edits | the one red: `Ty.stepDown_noPanic`'s hand-bulleted `succ` case (four arms → ten) — restated order-independently; 0 warnings everywhere green |
| S0 warm | `LEAN_NUM_THREADS=4 GOLEAN_MEM_MAX=32G scripts/capped lake build GoLean.GoCore` (after the `Store.lean` touch) | 0 | 105 | `68b261e6` + S0 edits | 33 jobs, 0 warnings |
| S0 full build | `LEAN_NUM_THREADS=4 GOLEAN_MEM_MAX=32G scripts/capped lake build` | 0 | 6 | same | lib + exe up to date |
| S1 checkpoint gate | `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (08:42:01–08:54:01 UTC), representation change WITHOUT the `HeapNormal` conjunct | **1** | **720** | S0 tip + the S1 runtime edits (stage 1) | 3676 cases: 3427 PASS / 249 expected FAIL; red ONLY on the expected 5a pair (`certificate provenance` STALE on `Machine.lean`; the one cached certified row); ZERO other drift — `alloc`-normalizes moved no row. Tail: evidence `gate-tail-s1-checkpoint.txt` |
| S1 gate | `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (09:06:02–09:17:37 UTC), the committed S1 tree | **1** | **695** | S0 tip + the S1 runtime edits | 3676 cases: 3427 PASS / 249 expected FAIL; red ONLY on the expected 5a pair (`certificate provenance` STALE on `CLI.lean`; the one cached certified row); ZERO other drift. Tail: evidence `gate-tail-s1.txt` |
| S2b-ii gate | `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (13:36:01–13:48:17 UTC), the S2b-ii runtime tree = the committed tree for `GoLean`/`Tests` (snapshot `refs/snapshots/c1/s2b2-gated`; the pre-build snapshot `s2b2-wip2` has the same runtime tree) | **1** | **736** | S2b-i tip + the S2b-ii deletions | 3676 cases: 3427 PASS / 249 expected FAIL; red ONLY on the expected 5a pair; ZERO other drift. Tail: evidence `gate-tail-s2b2.txt` |
| S2b-ii choice trace | `scripts/choice-trace-corpus --dump --jobs 6` with the S2b-ii binary (`.tmp/golean-s2b2`); sorted dumps `cmp` vs main | `cmp` **0**; tracer 1 (the same pre-existing ERROR finding) | 443 | S2b-i tip + the S2b-ii deletions | 21,835 (row, stream) results, statuses = S2a's census; 23,685 consumption records byte-identical (sha `70e12e02…eb57`). Evidence `trace-audit-s2b2.txt` |
| S2b-ii raft twin | the five probe entry points × 6 streams, sorted dumps `cmp` vs main's | `cmp` **0** | 1116 | S2b-i tip + the S2b-ii deletions | 30/30 results ok, 0 alarms; 14,360 consumption records byte-identical. Evidence `twin-audit-s2b2.txt` |
| S2b detector-soundness | `scripts/detector-soundness --select in-scope --jobs 6` with the S2b-i (fold) binary, and again with the S2a (pre-fold) binary as the control | **2** / **2** (INCOMPLETE: the gc `-race` side cannot run in this sandbox) | 215 / 216 | S2b-i tree; S2a tree | 639 in-scope rows; machine side pre-fold = post-fold on **639/639** rows (verdict, single-run status, members, race members); gc side `gc-no-verdict` on every row — TSan dies at its sync-allocator growth (EXIT 78, no report; command and transcript verbatim in `detector-soundness-s2b.txt`) — the HOLE cell is UNJUDGEABLE here → PENDING [USER] (§6) |
| S2b-i gate | `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (12:59:21–13:11:41 UTC), the S2b-i runtime tree = the committed tree for `GoLean`/`Tests` (`refs/snapshots/c1/s2b1-gated` = the commit itself: the post-gate `git stash create` FAILED on the intent-to-add entry of the new file, so the identity was verified instead by the pre-chain snapshot `refs/snapshots/c1/s2b1-wip1` (12:51:17 UTC; its only runtime difference to the commit is the then-untracked `AccessTableEq.lean`), the file mtimes (every runtime file last written 12:19–12:48 UTC, before the chain), and the `.lake` binary's hash = the audited binary's `4bda4748…` — recorded honestly, [AGENT]) | **1** | **740** | S2a tip + the S2b-i runtime edits | 3676 cases: 3427 PASS / 249 expected FAIL; red ONLY on the expected 5a pair; ZERO other drift. Tail: evidence `gate-tail-s2b1.txt` |
| S2b-i trace audit | `scripts/choice-trace-corpus --dump --jobs 6` with the S2b-i binary (`.tmp/golean-s2b1`, `4bda4748…`) — both accounts still live in the tracer; sorted dumps `cmp` vs main | **0 mismatches**; `cmp` **0**; tracer 1 (the same pre-existing ERROR finding) | 484 | S2a tip + the S2b-i runtime edits | 21,835 (row, stream) results, `traceMismatches` = 0 everywhere; 23,685 consumption records byte-identical (sha `70e12e02…eb57`). Evidence `trace-audit-s2b1.txt` |
| S2b-i raft twin | `.tmp/twin-audit-s2b1.sh` on the five probe entry points × 6 streams, sorted dumps `cmp` vs main's | **0 mismatches**; `cmp` **0** | 1158 | S2a tip + the S2b-i runtime edits | 30/30 results ok, 0 alarms; 14,360 consumption records byte-identical. Evidence `twin-audit-s2b1.txt` |
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
| the identity-type descent (audit fix round F3) | `Ty.stepDown` returns `(ty, b)` for `ty ∈ {.interface, .bool, .string, .slice, .map, .pointer}` — exactly the normalizer's identity arms — so the leaf normalizes at the identity, as the whole root did on main; RESTORES main's acceptance of a path write through such a root (the S1 cut refused by name on a cell `HeapNormal` admits — an undisclosed refusal-CLASS change, unreachable from Go: interface contents are not addressable; 13 leaf probes + the audit's 34 subjects SAME on both binaries) | (i) records only — disclose the refusal and keep it; (ii) restore for `.interface` alone | (i) leaves a behaviour change no corpus row exercises undisclosed-then-disclosed rather than absent — the brief said RESTORE; `.interface` alone would leave the docstring's «byte-identical on every normal cell» false for the catch-all kinds (`.slice`-declared cell holding an array is normal too); the whole identity class makes the claim TRUE and provable (`writeAt_isNormal`'s new alternatives close by the `true` arm). The residual `Ty.stepDown` refusals are reachable only on NON-normal cells, where main also refused (with the whole-root normalizer's text) |
| the field search | `fieldIdxFrom` (fuel = remaining count) | `Array.findIdx?` | S0 finding 3: `findIdx?`'s loop is well-founded — `decide`/`rfl` pins on the interpreter would stop reducing |
| refusal texts on a path store | LOAD texts on prefix steps, STORE texts on the last (`match rest with`) | one text per arm | byte-identity with the former leaf-first recursion, which loaded the prefix |
| the payload/unbound arms | payload cells: store text at the root, load text under a path; an unbound root under a path: `Store.updateCell`'s `.internal` (was `loadLoc`'s `.stuck`) | a second lookup to reproduce the `.stuck` | one lookup; the path is unreachable by heap density (BUG-085's argument), disclosed as a refusal-CLASS change |
| `MultiWf` | `MultiWf ctx m` again (B7 had made it context-free) | keep `MultiWf m` with `HeapNormal` outside `StateWf` | the charter puts the conjunct in `StateWf`; the type table decides normality, so the context is genuinely read — a restatement, flagged, nothing weakened |
| dead write-path primitives | `arraySet`, `StructFields.set` and their six lemmas left in place, dead | delete now | deletion is a runtime edit that would re-gate S1; S2b re-gates these files and tombstones them — recorded as owed (S2a's gate was already running when the item came up) |
| the peek list's home (S2b-ii) | the module docstring in `Ops.lean` («The memory module's access discipline — what emits, what peeks»), right after `AccessTrace` | a separate `docs/` inventory | the charter puts the inventory in the module (§1: one module owns representation, operations and events); `Race.lean`'s replacement header points at it and keeps U5's statement verbatim |
| the tracer's audit instrument (S2b-ii) | retired with the table (the two TSV columns `traceMismatches`/`firstTraceMismatch` removed; `scripts/choice-trace-corpus` reads columns by name, nothing else consumed them) | keep the columns at constant 0 | a column that can no longer be non-zero is a false witness |
| the detector-soundness re-run (S2b) | run twice (fold / pre-fold control), the machine side compared row for row; the gc side's sandbox failure recorded verbatim and referred | declare HOLE = 0 from the tip matrix's evolution | the gc side produced no verdict here; «HOLE = 0» is not this environment's to claim — the machine side's 639/639 identity is what the fold could have moved and did not |
| the theorem's commit (S2b) | the D6 theorem is PROVED at S2b-i with the table present and DELETED with the table at S2b-ii; the handoff §1 row names the proving SHA | one commit proving and deleting | a theorem about `stepAccesses` cannot outlive `stepAccesses`; the charter's «proved at the commit that deletes the table … the theorem leaves with the table, its proving SHA recorded» is read as prove-then-delete across two gated commits — the alternative cannot be stated |
| the theorem's statement (S2b-i) | `tr = tableTrace (stepAccesses ctx s c) ∨ (tr = [] ∧ c'.isPanicking = true)`, EXACT equality (no permutation) on the non-panicking successor; `spawnStep_trace` likewise | `tr ~ table` unconditionally | FALSE: a panicking apply's table account may be non-empty (the map read before an unhashable key's panic) while the label is `[]` — the disjunct is the standing «the access never happened» convention made visible; no permutation needed since every arm agreed in ORDER |
| the fold's one corner (S2b-i) | `raceUpdate` records the label unconditionally; the former pre/post-panicking discrimination is gone | keep the discrimination beside the label | the label already carries it (a delivered panic is `[]`) — BY INSPECTION OF THE RULES, not by the theorem (audit fix round F4: the theorem's second disjunct admits a non-empty label on a panicking successor; the rules never produce one — every `.panicking` successor from a non-panicking pre-configuration carries `[]`, evidence README «The fold's one corner»); the ONE step where the accounts differ — `panicFrameDefer` whose receiver load panics on an out-of-range element ADDRESS (`loadLoc` → `arrayGet`) — recorded the read the machine never performed; unreachable from a well-formed program (element addresses are bounds-checked at formation); the label's account is the honest one |
| `RacyFine` over labels (S2b-i) | the two goroutines' next steps are `StepE` from the pool's shared state (an ordinary step's label or a spawn's child-entry read) | `Step` only | `Step` has no spawn rule, so the spawn's dispatch read (which the fold DOES record) would be invisible to the proposition; `StepE` is the fine relation's own step (`StepMFine.thread`) |
| `sortSlice`'s operand loop (S2b-i) | the `for` accumulator → structural `intElems` (same refusal text at the first non-int, same output) | prove the `forIn` length invariant | `intElems_length` is a two-line induction; the op is DEAD (frontend never emits it, decoder refuses by name; deletion owed to the hygiene arc A11) — the smallest edit that makes the theorem true |
| `len`/`cap` on a pointer-to-array (S2b-i) | the type-static arm now REFUSES a non-pointer operand by name (`.addr _`/`.nil` answer `n`) | leave the arm answering from the type alone | fail-closed doctrine: an ill-typed operand answered `n` while the table classified the arm by the VALUE's shape (a map value would have recorded a read) — the theorem exposed the divergence; no well-typed program reaches it, the differential is unmoved |
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
2. ~~The detector-soundness gc side cannot run in this sandbox~~ — **WITHDRAWN at the audit
   fix round (2026-09-18; audit F2).** The diagnosis was FALSE: the gc `-race` harness binaries
   exited 78 because `scripts/detector-soundness` never created the harness's oracle crash-hook
   files (`oracle.crash`/`oracle.registered`) that `scripts/diff-coverage` resets before every
   draw — `tools/coverageharness/crashhook.go`'s `_goleanSetupCrash` opens `oracle.crash`
   WITHOUT `O_CREATE` and `os.Exit(78)`s («a setup failure, never an observation»); TSan runs
   fine here (`go run -race` of a racy program reports). Not a sandbox limit, not TSan's
   sync-allocator: a one-line runner bug DATED — the runner (2026-09-02, `05d0ec54`) predates the
   crash hook, which landed with L4 on 2026-09-07 (`60bbf466`, together with `diff-coverage`'s
   reset); the 2026-09-02 matrix therefore HAD gc verdicts, and every run of the runner since L4
   would have shown `gc-no-verdict` on every row. The runner is FIXED (the reset mirrored verbatim; a failed
   reset is INFRA) and the S2 exit check was run OFFICIALLY at the fix-round tip with the fixed
   tracked runner: EXIT=2 (INCOMPLETE for the 9 `params-omit-sites=` membership refusals, as at S2b and in the audit), 28 min 48 s; 639 rows: **HOLE 0, possible-HOLE 0**, agree-DRF 502, agree-race 36, over-refusal 6 (`race/free/array-dyn-index-read-write` = BUG-041's O1 residual, and the five `race/gomem-only/*` rows of the RULED go_mem-RACY / TSan-GREEN lane, BUG-084's `Cases:` line), refused 9, uncertified 86 (the machine side's ENUM-FAIL classes: deadlock members, frontend-quarantined subjects, sites bounds, one fuel truncation; gc green or no verdict there) — cell for cell the audit's patched-copy run. One blemish on this first official run, CAUSED BY THE FIX-ROUND WORKER and recorded: its worker-pool exit was 127 with one bash message `scripts/detector-soundness: line 387: -d: command not found` after the last row. Cause established: the worker edited `scripts/detector-soundness` (the amend's one comment line inside `run_row`) WHILE the runner was executing; bash reads a script by byte offset, so when `xargs` returned the parent resumed mid-line in the shifted file, ran `-d '\n' -I{} … | tee …` as a command and took that pipeline's `PIPESTATUS[0]` = 127. The 639 row workers had already completed (their function bodies were exported at start; `progress.txt` 639/639 before the message), the assemble step reads every `row.tsv` from disk, gc-infra 0, unclassified 0 — no cell is affected, and the runner's exit is the 9 refusals' either way. A one-row re-run of the last manifest row with the committed runner: pool exit 0, no message. The matrix was then RE-RUN in full with the committed runner, untouched: re-run 21:03 UTC, `artifacts/detector-soundness/fixround-official-2`, 28 min 49 s, **worker-pool exit 0, no message**, EXIT=2 for the same 9 refusals; **cells IDENTICAL on all 639 rows** — HOLE 0, possible-HOLE 0, agree-DRF 502, agree-race 36, over-refusal 6 (the same six rows), refused 9, uncertified 86; this clean run is the evidence file's primary record (`detector-soundness-fixround-summary.txt`), the first run kept beside it. Lesson (handoff §6c): never edit a script that is running. Nothing is asked of the [USER] here any more; the item stays in this
   list as the record of the withdrawn ask.

## 6a. What S1/S2a/S2b proved, what they owe

S2b-ii proved nothing new and deleted: the table family and the theorem that audited it
(`AccessTableEq.lean`, proving SHA in the S2b-i row), the tracer's table-side audit, the dead
`arraySet`/`StructFields.set` + six lemmas (`arraySet_locSup`, `StructFields.set_locSup`,
`StructFields.set_congr`, `arraySet_congr`, `StructFields.set_noPanic`,
`arraySet_ok_of_arrayGet_ok`). S2b owed the detector-soundness gc side — DISCHARGED at the audit
fix round with the fixed runner (§6 item 2, §8). S2c owes: D9 (sync-word / chan-object / atomic
emissions inside the module's operations, `raceUpdate` without `sPre`/`tsPre`), the ordering
design point of §6b, cost B(a). S3 owes (F7's census): the DEAD `storeMany` + `HeapNormal.of_storeMany`
(no caller; inventoried as DEAD in `scripts/mem-callsites.tsv`).

**S1's targets, plainly (audit fix round F8; charter §6 S1 row).** Measured as the charter
says (the BUG-090 runner, 3 runs, medians, net of the empty probe; evidence README «Benchmark
AFTER»; the audit re-timed interleaved at load ≈ 1 and confirmed):

| S1 target | result | verdict |
|---|---|---|
| `write_fixed` flat: per-write net within 2× across m = 10…10,000 | 12.6 → 16 µs (≈1.3×, at the noise floor; the 5,000× slope is gone) | **MET** |
| `append_grow(4000)` net < 2 s | 0.275 s (audit: 0.31 s interleaved) — 111× | **MET** |
| `append_grow` successive ×2 ratios ≤ 2.2 | ×2.5, ×2.5, ×2.8, ×2.7 (audit under load: ×1.6, ×3.5, ×2.1, ×2.8) | **MISSED** — NOT met; a residual super-linear term (each in-place append copies the shared backing once — cost B, the pre-step store retained across the step). **Carried as OWED to S3 (cost B(b)/(c), the rollback and the retention) / C4**, not as met |
| `scalar(80k)` per step within 10 % of BEFORE | +3.9 % (audit interleaved: −2 %) | **MET** |


S2b-i proved (kernel-checked, warning-free, `GoLean/GoCore/AccessTableEq.lean`):
`accesses_eq_stepAccesses` — every `Step ctx c s c' s' tr` has `tr = tableTrace
(stepAccesses ctx s c)` or delivered a panic (`tr = [] ∧ c'.isPanicking`); the corollary
`accesses_eq_stepAccesses_of_not_panicking`; `spawnStep_trace` for the spawn's child-entry
read; per helper `Mem.load/loadFor/store/mapRead/mapWrite/loadElems/storeElems/loadRun/
storeRun/loadSlice_trace`, `loadResults_trace`, `mapLookupValue_trace`,
`mapAssignValue_trace`, `mapRangeStartSets_trace`, `mapIterCandidates_trace`,
`storeTarget_trace`, `applyRhsOp_trace`, `applyStrictOp_trace` (all 60 strict arms),
`applyStmtOpCore_trace`/`applyStmtOp_trace` (every wide statement incl. append's two paths),
`dynamicDispatch?_trace`/`enterFrame_trace` (the promotion-hop leaf IS `dispatchLeaf`), the
`unseq*` lemmas. S2b-i owes (S2b-ii): the deletion of the table family and of this file (its
SHA recorded), `Race.lean:1-256` → the module docstring's peek list, the tracer's audit
instrument retired with the table, the dead `arraySet`/`StructFields.set` family, the
detector-soundness re-run.


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
- **S2b — the fold, the deletion, the theorem — landed as S2b-i (fold + theorem +
  `RacyFine`, table retained) and S2b-ii (the deletion), see §5 «the theorem's commit».** `raceUpdate`'s data
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

## 6c. Lessons for the successor (S2c/S3), [AGENT]

- **Restating a labelled relation** (S2a): a `match`/`if` in bind position DUPLICATES the
  continuation into the arms — hoist it into a helper (`Mem.loadRun`/`storeRun` were born that
  way); `cases h` on `Step` re-introduces index-mentioning premises LAST, so `case ctor x y z`
  names the trailing hypotheses (variables first, premises after, the label-bearing one last).
- **Decomposing an op-table arm's `do`-block hypothesis** (S2b-i, `AccessTableEq.lean` at
  `6bb1930d`): one bind at a time — `dsimp only at h` (zeta/beta/iota first, or `split` will
  generalize constructor discriminants into `heq` hypotheses), `simp only [pure_bind] at h`,
  `split at h`, `rw [bind_eq_ok] at h; obtain ⟨_, _, h⟩ := h`, `rw [seqRight_eq_ok]` for
  `*>` — with `repeat'` so every goal is reached; a whole-hypothesis `simp only [bind_eq_ok]`
  flattens several binds at once and the `obtain` pattern no longer matches.
- **Tactic macros and `rfl` patterns**: an `rcases`/`obtain` pattern `rfl` inside a `macro`
  body does NOT substitute (hygiene) — use a named equation and `subst`; `first | tac | …`
  does not protect against term-elaboration errors that recover to `sorry` (a mistyped `rw
  [lemma hyp]` inside an alternative is LOGGED, not backtracked) — guard alternatives with
  `guard_target =~ …` so only the intended arm runs a body.
- **Matcher identity**: two syntactically identical `match` expressions compiled in different
  definitions are defeq (`rfl` closes them) — helper defs (`iterRead`, `rhsAccesses`,
  `atomAcc`, `strictTrace`) avoid `match` in theorem STATEMENTS, whose dependent `h` would
  otherwise be generalized into the match.
- **`git stash create` fails on an intent-to-add (`git add -N`) entry** — snapshot the gated
  tree with everything fully `git add`ed, or verify the identity by the pre-chain snapshot +
  mtimes (S2b-i, §2).
- ~~The detector-soundness gc side does not run here~~ — WRONG (audit fix round F2): it was
  the runner's missing crash-hook files (§6 item 2), fixed; the gc side runs here. Lesson kept:
  when every row of a matrix fails the SAME way at the tooling boundary, reproduce ONE row by
  hand outside the runner before diagnosing the environment.
- **Never edit a running script** (fix round): bash reads a script file by byte offset as it
  executes; an edit that shifts bytes before the current position makes the parent resume
  mid-line when its long pipeline returns (the fix round's first detector-soundness run took
  a spurious pool exit 127 this way — §6 item 2). Copy the script to `.tmp/` before a long run,
  or edit only after `EXIT=` is on the log.
- **S2c's shape** (§6b): the label becomes an ORDERED list of memory-model events (accesses
  and the step's synchronization actions in gc's instrumentation order); `raceUpdate` becomes
  one fold; the registry arms' pre/post-cell reads (`raceWakeEvent sPre`, `racePairEvent sPre
  tsPre`, `raceCommitClauseEvent sPre`, `tryLockAcquired`'s re-derivation, the atomic arm's
  `atomicCompute`) become facts the EMITTING operation puts in the event. Land it as S2a was
  landed: BOTH folds live in one commit with a per-step comparison in the tracer (the
  `Acc.checkTrace` pattern, retired at `6a35dd92`, is the template), then the switch.

## 8. Audit fix round (2026-09-18) — dispositions of F1–F10, [AGENT] fix-round worker

The pre-merge adversarial audit (`docs/2026-09-18_c1-memory-module-audit.md` on branch
`review/c1-memory-module-0918`, commit `ba6b249c`; ordered by [USER] Mike 2026-09-18,
relayed: «(1) Agree, run the audit.») returned **FIX-FIRST (records-class)**: no WRONG-ANSWER,
FOOTPRINT-LIE, UNSOUND-PROOF, gate WEAKENING or FAIL-OPEN introduced. The coordinator's
dispositions below are [AGENT], disclosed to the [USER] at the merge ask. Two commits: the
RUNTIME commit `16029fa8` (gated) and the records commit on top of it.

| finding | class | disposition | where |
|---|---|---|---|
| F1 «D1–D7, D9, D10 RULED [USER] by default acceptance» unsupported by the cited record | provenance | REWORDED to the truth everywhere it appeared (charter §7 header, handoff §0, slice log, `Ops.lean` `Store.alloc` docstring, `Store.lean` comment): «[AGENT] coordinator's reading of the [USER]'s 2026-09-18 non-objection to the triage; explicit [USER] ratification REQUESTED at the merge ask (PENDING)»; the qrow record gained a PENDING paragraph saying so. No quote invented. | charter §7; `docs/2026-08-31_qrow-rulings.md`; §0 here |
| F2 detector-soundness gc side misdiagnosed («TSan sandbox») — a runner bug | tooling + records | RUNNER FIXED (the hook-file reset mirrored from `scripts/diff-coverage`; a failed reset = INFRA), the official re-run at the fix-round tip: HOLE 0, possible-HOLE 0, over-refusal 6 (BUG-041 + the five ruled gomem-only rows), 502/36/9/86, EXIT=2 for the 9 refusals — the charter §6 S2 exit check «HOLE = 0, other cells unchanged» HOLDS (details §6 item 2). §6 item 2 and §6c corrected; the evidence README's «TSan» paragraph withdrawn. | `scripts/detector-soundness`; §6, §6c; evidence README |
| F3 `storeLoc`'s «byte-identical on every normal cell» FALSE — an undisclosed refusal-class change | coherence gap | **RESTORED** (not PENDING): `Ty.stepDown` descends the identity-normalized declared types to themselves; `HeapNormal` preservation re-proved (the new alternatives close by `isNormalForTyTy`'s `true` arm — no theorem weakened, no hypothesis added); docstring corrected; five pins in `Tests/GoCoreContract.lean` assert main's behaviour (`#eval`'d first: evidence `probe-IfaceCell.log`). Alternative named in §5. | `Ops.lean`, `StateWf.lean`, `MachineSound.lean`, `Tests/GoCoreContract.lean` |
| F4 the deleted theorem's header inferred «both record nothing» on panicking steps from the theorem | records | CORRECTED: the agreement on panicking successors is by INSPECTION OF THE RULES (every `.panicking` successor from a non-panicking pre-configuration carries `[]`), not by the theorem; the rule list recorded. | evidence README «The fold's one corner»; §5 row |
| F5 «BUG-091» for the alias finding | records typo | → BUG-111 | evidence README |
| F6 §1 rows out of order; `MultiWfSound.lean:36` stale «context-free» | records / comment | §1 reordered (S0, S1, S2a, S2b-i, S2b-ii); the comment now says C1 S1 made `MultiWf ctx m` read the context again (`HeapNormal`). | §1; `MultiWfSound.lean` |
| F7 nothing mechanical guards the emit/peek discipline | coherence gap (low) | **ADDED CHECK**: `scripts/check-mem-callsites` scans `GoLean/**/*.lean` (comments stripped by `lean-scan.sh`'s stripper) for every mention of a raw memory operation inside an executable declaration and compares (file, declaration, op, count) EXACTLY with the tracked, reasoned inventory `scripts/mem-callsites.tsv` (78 rows at this tip, counted from the file's reason classes: 16 module bodies — the 5 emitting operations' own peeks/writes, the 4 peek primitives, the 3 raw-writer primitives, the drivers' `loadMany` 2, the sync peeks `chanCell`/`syncCell` 2; 6 address-formation/type-static-metadata peeks; 1 map-RMW entry peek; 1 machine-internal binder read; 12 driver readouts / Prop-level relation premises / the one refusal text naming `Store.alloc` / the frame-exit readout that is a refusal; 22 synchronization sites; 6 detector registry arms (S2c retires); 10 fresh-allocation sites; 2 DEAD `storeMany`; 2 tracer observations); a new site, a changed count, a stale row or a malformed inventory FAILS by name with the two resolutions. Wired into `scripts/ci` as a static step after the engine-isolation lint (not a `ci-libraries.json` entry: the registry refuses steps that build no library). Self-tested: a removed row → NEW, an invented row → STALE, a 2-column row → malformed, all EXIT=1. | `scripts/check-mem-callsites`, `scripts/mem-callsites.tsv`, `scripts/ci` |
| F8 `append_grow` ×2 ratios ≤ 2.2 MISSED | performance | Said plainly in §6a's targets table: MISSED, carried as OWED to S3/C4, not as met. | §6a |
| F9 whole-struct copy through a struct-tag-compatible alias refuses on BOTH binaries where Go accepts | pre-existing gap | ROWED as a frontier row **FR-34** (+ queue slot 34) in `docs/language-coverage-ledger.md` per its standing rule (a fail-closed refusal on legal Go); a red-first corpus row PROPOSED for a corpus lane, not added (`Corpus/**` is not this lane's). Not fixed here. | ledger §4/§5 |
| F10 BUG-111 confirmed end-to-end | confirmation | Entry stands; fix PENDING [USER] (§6 item 1), untouched. | `docs/BUGS.md` |

**Gate at the fix-round runtime tip `16029fa8`:** `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (20:18:14–20:32:18 UTC; lock acquired after 0 s), the committed runtime tree `16029fa8` (clean for `GoLean`/`Tests`/`scripts`; `docs/` dirty with the records edits — the negative-diff step notes `git_dirty=true` for that reason): **EXIT=1, 844 s**; **3676 cases: 3427 PASS / 249 expected FAIL** (`differential coverage summary: cases=3676 pass=3427 fail=249`); `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit` ok; **`memory-module raw call-site inventory (emit/peek discipline)` ok — the NEW step, GREEN at this tip (78 rows)**; `unseq scheduler` ok; `frontend pins` ok; `wire boundary` ok; every other step ok. RED: exactly the two 5a-class items — `certificate provenance` (C9 HIGH: «STALE certification: changed dependency build/files/GoLean/CLI.lean») and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` (the one cached certified row). ZERO other drift; the negative baseline matched (394). The binary after the gate's rebuild is byte-identical to the one the detector-soundness matrix and the choice-trace subset ran (`42b7bf1a…`). **Choice-trace subset** (the auditor's
307 ids × 6 streams, this binary vs main's certified `231df9a9…`): 303 ids traced, 1,818 (id, stream) lines each side, tracer EXIT=0 both (43 s / 51 s); sorted consumption dumps 2,690 records each, one sha256 `bd48dac5…`, `cmp` EXIT=0 — **BYTE-IDENTICAL** (evidence `choice-trace-subset-fixround.txt`). **Records checks:**
`check-bugs.sh` EXIT=0, `check-evidence-size` EXIT=0 (PASS, 0 new offenders), `check-agents-alias` EXIT=0, `check-spec-anchors` EXIT=0 (FR-34's anchors resolve at pin `c19862e5f`). Evidence: README «Audit fix round» section.

## 7. Where the lane stopped; the next command — PARKED 2026-09-18

PARKED (still before S2c/S3) at the audit fix round's records commit over the gated runtime
commit **fix round `16029fa8`** (§8; snapshot `refs/snapshots/c1/fixround-wip1`), which sits on
S2b-ii `6a35dd92` (snapshot `refs/snapshots/c1/s2b2`); branch `core/c1-memory-module-0918`, base
main `68b261e6`; worktree `.claude/worktrees/c1-memory-module`, clean; nothing merged, nothing
pushed; main untouched. Before the merge ask: the audit's F1 ratification (D1–D7, D9, D10) and
BUG-111's fix are PENDING [USER]. Landed on the branch, each a gated runtime commit at zero baseline
drift beyond the expected 5a pair and a byte-identical whole-corpus choice trace: S0
`50f293d9` (records + spike), S1 `d7b32f59` (the module + cost A), S2a `7f7c721c` (the data
trace, both accounts live, the audit), S2b-i `6bb1930d` (the fold + `accesses_eq_stepAccesses`
+ `RacyFine` over labels), S2b-ii `6a35dd92` (the table deleted). OPEN: **S2c** (D9: the
sync-word / chan-object / atomic emissions inside the module's operations, `raceUpdate`
without `sPre`/`tsPre`, the ORDER design point — §6b, §6c) and **S3** (the rollback, cost
B(b)/(c) — charter §6). PENDING [USER]: §6 (BUG-111; the detector-soundness gc side).

THE NEXT COMMAND (S2c, first cut): read §6b's S2c paragraph and §6c's last bullet; define the
event type (`MemEvent := access Access | …hb actions…`, or extend `Access`) in `Ops.lean`'s
module section; make `applyChanOp`/`commitClause`/`resumeThread`/`applyPairing`/`wakeReady`/
`applySyncOp`/`applyAtomicOp`/`spawnStep` emit their synchronization facts in gc's
instrumentation order; write `raceUpdate'` as the one fold over `ev.trace` beside the
existing `raceUpdate`; compare the two per pool step in the tracer over the whole corpus + the
twin (differences are findings, D7); gate; then switch and delete `sPre`/`tsPre`; gate. Then
S3. The pre-merge adversarial audit was run at this park (§8: FIX-FIRST, records-class, fixed);
the ask is re-posed at every later park and at the landing (charter §8); scope and waiver are the
[USER]'s.
