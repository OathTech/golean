# C1 memory module — the lane's evidence (2026-09-18)

[AGENT] worker, lane `core/c1-memory-module-0918` (branch of the same
name, base main `68b261e6`). Consuming documents: the charter
`docs/2026-09-17_c1-memory-module-charter.md` (§6 slices, §8 exit
evidence), the handoff `docs/2026-09-18_c1-memory-module-handoff.md`,
the slice entries in `docs/hygiene-slice-log.md`. Every command below is
run from the worktree root; scratch lives under `.tmp/` (gitignored),
never `/tmp`.

Toolchain: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`);
`leanprover/lean4:v4.32.2`. Host: linux/amd64, 32 CPUs, 125 GiB; load1
1.3–1.5 during the benchmark (no sibling build ran: the lane's own warm
and gate were started AFTER the benchmark finished).

## S0 — records, the spike, the D8/D10 markers

### Provenance

- Tree: main `68b261e6` + the S0 edits (`GoLean/GoCore/NPDRF.lean`: the
  `@[deprecated …]` attribute and docstring banner on `NPDRFReduction`;
  `GoLean/GoCore/Store.lean`: the `updateCell` refusal text names
  `Store.alloc`). Committed as the S0 commit (SHA in the handoff).
- BEFORE binary: the primary checkout's certified `.lake/build/bin/golean`
  at main `68b261e6`, sha256
  `231df9a99f459d4a5865f043fa54ab49163a5e29df2284c14ca89f0a77fa1a99`,
  copied READ-ONLY to `.tmp/golean-main` (the only read of the primary
  besides the `.lake` copy that warmed this worktree's build).
- Frontend: `GO111MODULE=off GOCACHE=$PWD/.tmp/gocache go build -o
  .tmp/nativefrontend ./tools/nativefrontend` at `68b261e6`, sha256
  `0462e197469ccb8762aca576d1bbdef589b44fb9fb08bbc735935250ce8383bb`.

### The census at the fork (recorded greps, this tree = `68b261e6`)

`loadLoc ctx` / `storeLoc ctx` CALL LINES per module (`grep -c "loadLoc
ctx"` / `grep -c "storeLoc ctx"` — proof modules included because their
lemma bodies unfold the operations):

| module | loadLoc | storeLoc | | module | loadLoc | storeLoc |
|---|---:|---:|---|---|---:|---:|
| Machine | 18 | 29 | | NPDRF | 1 | 2 |
| StepFn | 1 | 1 | | StateWf | 1 | 3 |
| Multi | 2 | 4 | | MachineSound | 8 | 6 |
| Race | 2 | 0 | | Ops (defs + `indexTargetLoc` class) | 4 | 0 |

Non-core mentions: `GoLean/NativeToIR.lean` 3 (prose), `Tests/GoCoreContract.lean` 2,
`Tests/GoCoreEval.lean` 5. Payload operations (`mapPayload?` / `chanPayload?` /
`storeMapPayload` / `storeChanPayload`): Machine 4/3/3/5, Multi 0/2/0/5, Race
0/0/0/1, Ops 1/0/0/0, StateWf 2/2/7/8, MultiWfSound 0/0/0/5 (the charter's
«Machine 4+11+3+5» counted the `chanCell` wrapper's sites into the second figure;
this grep counts the bare operation names).

Allocation sites (non-proof `.alloc`/`.allocCell`): 13 — `StepFn.lean:332`
(`.initialization`), `:1011` (`seedGlobals`); `Machine.lean:381`
(`bytesFromString`), `:628` (`runesFromString`), `:663` (`allocDecls`), `:673`
(`bindParams`), `:1087` (`.allocNew` — THE alloc hole: the evaluated value, un-normalized),
`:1124` (`makeSlice` backing), `:1156` (`makeMap` payload), `:1186` (`makeChan`
payload), `:1410` (`appendSlice` spill backing), `:1522`/`:1528` (`bindIterVars`) —
plus the `Step` rule at `Machine.lean:4480`.

The footprint-table family (`stepAccesses|strictOpAccesses|stmtOpAccesses|
storeTargetAccess|dispatchAccesses|deferEntryAccesses|projChainTarget|
unseqRunAccesses`) mention lines: **Race 54 / Multi 6 / NPDRF 5** (+ Unseq 1, a
docstring) — the charter's 54/6/5 exactly. `stepAccesses` has 17 `Config` arms
(Race.lean:1582-1663).

`deliverS` call sites in `StepFn.lean` (21 lines; 17 distinct apply/entry sites):
68/72/78 are the definition and its two `@[simp]` projections; the sites and what
each delivers — 121 `enterFramePick` (frame-exit defer drain), 210 `unseqLoad`, 269
`enterFramePick` (panic-path defer entry, chain joined), 384 `enterFramePick`
(zero-arg call), 536 `applyStrictOp` (nullary), 544 `applyStrictOp`, 573
`enterFramePick` (last call arg), 585 `valueAsLoc` (target-address arrival), 591
`applyStmtOp`, 596/617 `enterFramePick` (call-value forms), 658 `applyChanOp`, 671
`applySelect`, 709 `applyRhsOp`, 747 `applySyncOp`, 760 `applyAtomicOp`, 828
`storeTarget`. Relation-side `deliver`: `Multi.lean:606` (`spawnStep`), `:1434`
(the select interception). Every one of them holds the PRE-apply `s` across the
apply — cost B(b)'s retention set. The pool adds `Thread.afterStep s c c'` after
`stepFn` (`Multi.lean:1442`, reads `s` for the boundary flag) and the drivers'
`raceUpdate ctx m.shared m.threads ev m' r` after `stepMulti` (`Multi.lean:2199/
2209/2250/2265`) — cost B(a).

### The write-then-panic audit of the apply arms (S0, delegated read; the S3 input)

`toResult` (`Value.lean:394-397`) turns exactly `Stop.panic msg` into
`Result.panic`; every other `Stop` (`fatal`, `deadlock`, `raceDetected`, the three
refusals) propagates and never reaches `deliverS`'s rollback arm. Classes: **N**
(cannot panic), **V** (validate-then-commit: every panic point precedes every heap
write), **W** (a write can precede a later panic point — rolled back by
`deliverS` today). Counts over the ~170 arms of `applyStrictOp`, the list
helpers, `applyStmtOpCore`/`applyStmtOp`, `bindIterVars`, `storeTarget`,
`applyRhsOp`, `enterRecvTargets`, `applyChanOp`, `applySyncOpCore`/`applyTryLock`/
`applySyncOp`, `applyAtomicOp`, `commitClause`/`applySelectCore`/`applySelect`,
`spawnStep`, `resumeThread`, `applyPairing`, `unseqLoad`: **N 118 / V 46 / W 8.**

The eight W arms (file:line at `68b261e6`):

| # | arm | write before | later panic source | reachable through `stepFn`? |
|---|---|---|---|---|
| 1 | `storeMany` cons loop `Machine.lean:696` | `storeLoc` per iteration | the next iteration's path store | **dead code** (no caller) |
| 2 | `.allocNew` `:1087-1088` | `s.alloc` | `storeLoc` at a PATH target (`loadLoc`/`arraySet`) | only if a checked `.index` target fails at store time — needs the header/backing invariant to be false |
| 3 | `.makeSlice` `:1124-1126` | `s.alloc` (backing) | `valueAsLoc tv` (nil target), `storeLoc` (path target) | nil target pre-empted at arrival (≥ 2 operands); path store as (2) |
| 4 | `.makeMap` `:1156-1158` | `allocCell` (payload) | `valueAsLoc tv`, `storeLoc` | **YES, hint-less form**: one operand ⇒ arrives with `pending = []` ⇒ no arrival nil-check (`StepFn.lean:578-591`) |
| 5 | `.makeChan` `:1186-1188` | `allocCell` (payload) | `valueAsLoc tv`, `storeLoc` | **YES, cap-less form** (same gap) |
| 6 | `.clearSlice` loop `:1234` | `storeLoc` per element | a later element's `arraySet` bound | only under a header/backing inconsistency (`validateSlice` checks `len ≤ cap` only) |
| 7 | `.copySlice` `:1281-1288` | `storeLoc` per element | later element (as 6); `valueAsLoc tv` AFTER the loop; `storeLoc tloc` | tv nil-checked at arrival (3 operands); the rest as (6)/(2) |
| 8 | `.appendSlice` in place `:1359-1369` | `storeLoc` per element | later element (as 6); `storeLoc tloc` if non-root | `tloc` is root under `Config.appendTargetLocal`; the loop as (6) |

Facts the audit rests on (theorems): `normalizeValueForTy_noPanic`
(MachineSound:3623), `storeLoc_base_noPanic` (:3725), `storeLoc_noPanic_of_loadLoc_ok`
(:3757), `defaultValue_noPanic` (:3678), `buildAppendBackingValue_noPanic` (:3694),
`StructFields.set_noPanic` (:3711), `applyTryLock_noPanic` (:3811),
`enterRecvTargets_noPanic` (:3794). Corrections to the brief's assumptions: `valueAsInt`
and its siblings are STUCK-only (`Ops.lean:1852-1874`), never a panic source; the sync
arms store at the loc they just loaded (V); `.wgAdd`'s negative-counter outcome is a
`.panicking` CONFIG after its write (`:3684`) — the ONE arm where a write surviving a
Go panic is the designed behaviour (probe p13), outside `deliverS`'s rollback by
construction. What S3 must decide per W arm: validate-then-commit (hoist the
`valueAsLoc tv` before the alloc in 4/5 — a pure reordering, the alloc is
fresh), or an undo entry; and the header/backing invariant (`offset + cap ≤
backing.size`) is NOT a `StateWf` conjunct today — stating it (or proving element
loops cannot fail after `validateSlice`) collapses 2/6/7/8 to V.

### The benchmark BEFORE (`run-probes.py --plan full`, 3 runs, medians, net of the empty probe)

```sh
mkdir -p .tmp/bug090 .tmp/gocache
cp /home/dev/projects/golean/.lake/build/bin/golean .tmp/golean-main && chmod a-w .tmp/golean-main
GO111MODULE=off GOCACHE=$PWD/.tmp/gocache go build -o .tmp/nativefrontend ./tools/nativefrontend
E=docs/evidence/2026-09-11_bug090-rediagnosis
python3 $E/run-probes.py --golean .tmp/golean-main --frontend .tmp/nativefrontend \
    --scratch .tmp/bug090 --plan full --out .tmp/bench-before.json
python3 $E/summarize.py .tmp/bench-before.json $E/steps.json > .tmp/bench-before-summary.md
```

`bench-before.json` (64 KB) and `bench-before-summary.md` are copied here. The
steps-per-iteration line in the summary is the 2026-09-11 `steps.json` (same probes;
the bisection was not re-run — it does not enter the net times). Run 06:35–07:03 UTC,
no timeout fired. The target rows (charter §6), BEFORE column filled:

| probe / point | BEFORE net | S1 target | S3 target |
|---|---:|---|---|
| `write_fixed(m, 100)` per write, m = 10 / 100 / 1,000 / 3,000 / 10,000 | 21 / 44 / 1,248 / 9,560 / 106,972 µs | flat: within 2× across m | — |
| `append_grow(n)` net, n = 250 / 500 / 1,000 / 2,000 / 4,000 | 0.023 / 0.113 / 0.700 / 4.56 / **30.42 s** (ratios ×5.0, ×6.2, ×6.5, ×6.7) | n = 4,000 < 2 s; successive ×2 ratios ≤ 2.2 | — |
| `scalar(80000)` per step | 246 ns (0.964 s net; 49 steps/iter) | within 10 % of BEFORE | — |
| `alloc_new(n)` net, n = 1k / 4k / 16k / 32k | 0.039 / 0.245 / 3.58 / **13.77 s** (ratios ×6.3, ×14.6, ×3.85 for ×4, ×4, ×2) | — | linear: ×4 ratios ≤ 4.4; n = 32k < 1 s |
| (h) scalar phase after h live cells, h = 0 / 1k / 10k / 40k | 0.237 / 0.353 / 1.805 / **6.375 s** | — | h = 40k within 1.2× of h = 0 |
| reads `read_fixed(m, 1000)` per read | 15.0 / 15.8 / 15.0 / 17.8 µs (flat) | (control) | |
| `struct{a [10000]byte; x int}: s.x = i` per write | 109,130 µs | (cost A witness) | |
| `map_write(4000)` per write | 45 µs (×2.9 per doubling) | not a C1 target | |

Every BEFORE number reproduces the 2026-09-11 note within noise (that run: 15 µs →
109 ms; 31.6 s; 252 ns; 14.05 s; 7.35 s).

### The §5 spike — `spikes/c1-frame/Frame.lean` (outside the lakefile and the gate)

```sh
scripts/capped lake env lean spikes/c1-frame/Frame.lean > .tmp/spike.log 2>&1; echo EXIT=$?
```

**EXIT=0**, 0 errors, 18 linter warnings (unused simp arguments in disposable
code); 914 lines; sha256
`2a510942fe091700813f2d12d90ab0dbd3231268a2f917c0935c3c5a5d0f13b3`. The stub:
`PathStep`/`Loc.rootPath` (leaf-first `Loc` → root address + ROOT-FIRST path),
`writeAt` (in-place path write, `Array.modifyM` at every level), `readAt`,
`leafTy` (the declared type descended along the path through
`TypeEnv.resolve`), `stubStore` (leaf-typed normalization + `writeAt` + ONE
`Store.updateCell`), `stubLoad`, and the bridge `stubLoad_eq_loadLoc` (the stub's
root-first read IS today's `loadLoc`, every depth).

Proved (kernel-checked, no `sorry`/`axiom`/`native_decide`):

- **(a)** `arraySet_comm` (two in-range `arraySet`s at distinct indices commute),
  `Array.modify_comm`, `fieldModify_comm` (the candidate's field update — `modify`
  at the name's position — commutes at distinct names). `StructFields.set` itself
  is NOT the candidate's primitive (the module retires it on the write path); its
  commutation was not proved and is moot.
- **(b)** `isNormalForTyTy_array_set` (one `.index` depth) and
  `isNormalForTyAt_struct_set` (one `.field` depth, at the index layer where the
  struct arm lives): normal root + leaf normal at the leaf's declared type ⇒ the
  updated root is normal.
- **(c)** `F1`, `F2` (as chartered, structural `ShadowKey.overlap`), `F1Canon`,
  `F2Canon` (canonical disjointness) STATED and typechecked;
  **`f1_canon : F1Canon ctx` PROVED at every depth** (cross-root half via
  `Store.updateCell_lookup_ne` + `loadLoc_root_congr`; same-root half via
  `readAt_writeAt_disjoint`, a path induction). The bridge lemmas `locPrefix_iff`
  and `data_overlap_false_iff` relate `locOverlap` to `rootPath` prefixes.

**Verdict: PASS** on (a), (b), (c) — the candidate representation admits the
disjoint-path frame law including the same-root half (obstruction 6's gap), with
THREE FINDINGS, none about the representation:

1. **F1 as chartered is FALSE** (witnessed by evaluation, in the compile log:
   `#eval ShadowKey.overlap (.data locA) (.data locB)` = `false`; the store through
   `locA` then loads `Except.ok (Except.ok (int 0), Except.ok (int 5))` through
   `locB`). `locPrefix` compares `.field` steps STRUCTURALLY, typeId included, so
   `.field b A f` and `.field b B f` — a struct-tag-compatible pointer alias
   (triage L7: `p.f` vs `(*B)(p).f`) — are «disjoint» keys naming ONE word. F1
   holds for the CANONICAL relation (typeIds erased; `pathsDisjoint`). Detector
   consequence: a plain write through one alias and a read through the other,
   HB-unordered, is NOT a conflict for `ShadowKey.overlap` — a missed race,
   fail-OPEN vs `-race`. Pre-existing, independent of C1; filed as BUG-091
   (`docs/BUGS.md`), PENDING [USER]; the S2 emission should key `.data` by the
   canonical path. The kernel-checked refutation was NOT built: see finding 3.
2. **F1 cannot be exact `Except` equality**: the «wrong base kind» refusals embed
   `repr` of the (changed) root value, so `loadLoc s' m = loadLoc s m` fails on
   ill-typed paths. The law is agreement on SUCCESSFUL loads
   (`∀ w, load s' m = .ok w ↔ load s m = .ok w`); every F-statement carries this
   form.
3. **`Array.findIdx?` does not kernel-reduce** (its loop is well-founded): probed
   with `.tmp/probe/FindIdx.lean` — `decide` and `rfl` both fail on
   `#[("f", 1)].findIdx? (·.1 == "f") = some 0`. S1 DESIGN CONSTRAINT: the
   module's field-position search must be STRUCTURAL (the de-WF recipe
   `Ops.lean` records at `normalizeListWith`), never `Array.findIdx?`, or the
   interpreter stops kernel-reducing (the `rfl`/`decide` pins in `Ops.lean` and
   the eval tests).

### The D8 marker and the D10 wording (records-class core edits)

- `GoLean/GoCore/NPDRF.lean`: `@[deprecated "NPDRFReduction is FALSE as stated
  (main can exit with other goroutines mid-computation; the whole-state
  comparison fails) — not to be used as a hypothesis; restated after C1's access
  trace" (since := "2026-09-18")]` on `def NPDRFReduction`, plus the docstring
  banner quoting the ruling. Use sites at the marking: **zero** (`git grep
  NPDRFReduction -- GoLean Tests` = the definition and its two docstring lines).
  Build warning count after the edit: 0 (the attribute warns only at a use).
- `GoLean/GoCore/Store.lean:55`: «… (allocation goes through `Store.alloc`
  only)» (was `ExecState.alloc`). Pinned nowhere but the definition (`git grep
  "ExecState.alloc only" -- . ':!docs'` = that one line); an `.internal` on a path
  no well-formed run reaches.

### The S0 warm (interface-hot: `Store.lean` touched)

`LEAN_NUM_THREADS=4 GOLEAN_MEM_MAX=32G scripts/capped lake build GoLean.GoCore`
→ **EXIT=0, 105 s**, 33 jobs, 0 warnings (B7 measured 104 s for a `State.lean`
touch; the charter's ≤ 5 min condition holds).

### The S0 gate

`GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (taken 07:10:22, released 07:26:00 UTC; owner file; trap-protected release; wait-retry 120 s), at `68b261e6` + the S0 edits: **EXIT=1, 938 s** (`CI total wall seconds: 938`); **3676 cases: 3427 PASS / 249 expected FAIL** (B7's tally exactly); `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit` ok; `frontend pins` ok; `wire boundary` ok; `unseq scheduler` ok; `bug-index cross-check` ok; `evidence-on-main size gate` ok; every other step ok. RED: exactly the two 5a-class items — `certificate provenance` (reconciler C9 HIGH: «STALE certification: changed dependency build/files/GoLean/GoCore/NPDRF.lean») and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` — the one cached certified row, judged stale because a compiled semantic input changed. ZERO other drift. Tail: `gate-tail-s0.txt`.

## S1 — the module and cost A

### Gate lines

- Checkpoint (representation + linear normalizers + `alloc` normalizes, BEFORE the
  `HeapNormal` conjunct): `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the
  box-wide lock (08:42:01–08:54:01 UTC): **EXIT=1, 720 s**; 3676 cases: 3427 PASS / 249
  expected FAIL; every step ok EXCEPT `certificate provenance` (STALE: changed dependency
  `build/files/GoLean/GoCore/Machine.lean`) and `baseline diff` with the SINGLE line
  `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]`;
  ZERO other drift. Tail: `gate-tail-s1-checkpoint.txt`.
- S1 gate (the committed tree): `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (09:06:02–09:17:37 UTC): **EXIT=1, 695 s**; **3676 cases: 3427 PASS / 249 expected FAIL**; `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit` ok; `frontend pins` ok; `wire boundary` ok; every other step ok. RED: exactly the two 5a-class items — `certificate provenance` (C9 HIGH: «STALE certification: changed dependency build/files/GoLean/CLI.lean») and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` — the one cached certified row, judged stale because compiled semantic inputs changed. ZERO other drift. Tail: `gate-tail-s1.txt`.

### The choice trace (D4: zero drift on the machine, byte-identical tape consumption)

Whole-corpus choice trace (`scripts/choice-trace-corpus --dump --jobs 6 --exclude goroutines/send-then-spin --exclude strings/trimspace-repeat/repeat-bound-refused`, main `68b261e6`'s certified binary `231df9a9…` vs the S1 binary `f462cf50…`, run 09:23–09:41 UTC): sorted dumps `cmp` **EXIT=0 — BYTE-IDENTICAL**, 23,685 consumption records both sides, one sha256 `70e12e023f3ee30b9d71317454e11dedcb6c6ec039d63aeddfbb3d4906aceb57`; 34 frontend-refusal exports and the 2 exclusions identical; each tracer run EXIT=1 for the SAME pre-existing «FINDINGS present» depth listing (main 609 s, S1 436 s). Tails: `trace-summary-main-s1.txt`.

### Benchmark AFTER (same probes, runner, box class; 3 runs; net of the empty probe)

`.tmp/golean-s1` = the gated binary (sha256 `f462cf50…48f3`), same frontend and probes as BEFORE; `--plan full`, 3 runs per point, medians, net of the empty probe (0.0213 s); run 09:18–09:23 UTC (the whole plan in 337 s — BEFORE needed 28 min), load1 ≈ 1.3, no sibling build. Artifacts: `bench-after-s1.json`, `bench-after-s1-summary.md`.

| probe / point | BEFORE net | AFTER (S1) net | S1 target | verdict |
|---|---:|---:|---|---|
| `write_fixed(m, 100)` per write, m = 10 / 100 / 1,000 / 3,000 / 10,000 | 21 / 44 / 1,248 / 9,560 / 106,972 µs | −2 / 1 / 3 / −2 / **16 µs** (100 writes sit at the 21 ms startup noise floor; the count-varying rows put one write at 13.1 µs (m = 10, w = 1,000) / 12.6 µs (w = 10,000)) | flat: within 2× across m | **MET** (12.6 → 16 µs, ≈1.3×, at noise level; the BEFORE 5,000× slope is gone) |
| `append_grow(n)` net, n = 250 / 500 / 1,000 / 2,000 / 4,000 | 0.023 / 0.113 / 0.700 / 4.56 / 30.42 s | 0.0056 / 0.0141 / 0.0352 / 0.1001 / **0.2748 s** | n = 4,000 < 2 s | **MET** (111×) |
| `append_grow` successive ×2 ratios | ×5.0, ×6.2, ×6.5, ×6.7 | ×2.5, ×2.5, ×2.8, ×2.7 | ≤ 2.2 | **MISSED** — a residual super-linear term: each in-place append still copies the backing once (the heap is shared across the step — cost B, S3's), ≈ Σ cap; plus the spill path's linear rebuilds |
| `scalar(80000)` per step | 246 ns (0.964 s net) | 250 ns (1.001 s net) | within 10 % | **MET** (+3.9 %) |
| `struct{a [10000]byte; x int}: s.x = i` per write | 109,130 µs | 5 µs | (cost A witness) | quadratic gone |
| `[10000]byte: b[0] = v` per write | 107,972 µs | 23 µs | (cost A witness) | quadratic gone |
| `append_cap(6400, 100)` per in-place append | 44,437 µs | 29 µs | (cost A witness) | quadratic gone |
| `alloc_new(32000)` net | 13.77 s | 13.51 s | (S3) | unchanged, as expected |
| (h) scalar phase at h = 0 / 40k live cells | 0.237 / 6.37 s | 0.259 / 6.05 s | (S3) | unchanged, as expected |
| `read_fixed(10000, 1000)` per read | 17.8 µs | 16.7 µs | (control) | flat |
| `map_write(4000)` per write | 45 µs | 45 µs | not a C1 target | unchanged |

Reading: cost A (the whole-root re-normalization with the quadratic `#[head] ++ tail`) is gone — every per-root-size slope is flat to the noise floor. The two misses named above are the SAME mechanism, cost B (the pre-step store retained across the step makes the root array shared, so `Array.modifyM` copies it once per write — O(m), the linear term the BUG-090 note predicted); S3 removes the retention.


## S2a — the DATA trace, both accounts live, the trace-equality audit (2026-09-18)

### What landed (one gated runtime commit; `raceUpdate` untouched)

- The access VOCABULARY moved from `Race.lean` into `Ops.lean`'s module section
  (`AccessKind`, `SyncWordName`, `ShadowKey` + `overlap`, `locPrefix`/`locOverlap`, the
  `Ord` derivings); `Access := AccessKind × ShadowKey`, `AccessTrace := List Access`.
- The EMITTING operations, each a primitive plus a fixed emission: `Mem.load l`,
  `Mem.loadFor root leaf` (the root value, the read at the leaf), `Mem.store l v`,
  `Mem.mapRead l`/`Mem.mapWrite l entries nextId` (the map cell as ONE location),
  `Mem.loadElems`/`Mem.storeElems` (structural element runs), `Mem.loadRun`/`Mem.storeRun`
  (a slice's run from a visible index), `Mem.loadSlice` (the visible range);
  `sliceVisibleValues` is now the PEEK form `(·.1) <$> Mem.loadSlice`; `loadResults` (frame
  exit, emitting) beside the drivers' `loadMany` (peek); `dynamicDispatch?` emits the
  receiver read at `dispatchLeaf` (the promotion-hop narrowing — `recvFieldChain`/
  `wrapperForwardArg` moved in from `Race.lean`); `projChainTarget` moved to `Machine.lean`
  after `Cont`. `loadLoc`/`storeLoc`/`mapPayload?`/`storeMapPayload` keep their types as
  the module's peek and raw writers.
- Every emitting helper returns its trace as the LAST ok-component (`applyStrictOp`
  (+ `leafOf`), `applyStmtOpCore`/`applyStmtOp`, `mapAssignValue`, `storeTarget`,
  `mapRangeStartSets`, `mapIterLiveEntries`/`mapIterCandidates`, `mapLookupValue`/
  `applyRhsOp`, `enterFrame`/`enterFramePick` (the `Result` payload), `unseqAtom(s)`/
  `unseqReadTarget`/`unseqLoad`/`unseqTargetPlan`/`unseqGuard`, `stepFrameExit`,
  `stepUnseqEnter/Next/Value`); `deliver`/`deliverS` carry it (a delivered PANIC carries
  `[]`); `stepFn : … → Except Stop (Config × Store × Choices × AccessTrace)`;
  `Step : Config → Store → Config → Store → AccessTrace → Prop` — 122 constructors, 94 pure
  rules labelled `[]`, 28 helper-bearing rules labelled by their operations' emissions;
  `StepE`/`StepM`/`StepMFine` labelled; `Steps`/`StepsM`/`StepsMFine`/`PoolSteps` erase;
  `StepEvent.trace`, filled by `stepThread` (a goroutine step: `stepFn`'s trace; a spawn:
  the CHILD's entry read; the pool's own steps `[]`); `spawnStep` returns the trace.
- Coherence restated and RE-PROVED: `stepFn_sound : stepFn … = .ok (c', s', ch', tr) →
  Step ctx c s c' s' tr`; `step_complete : Step … tr → ∃ ch ch', stepFn … = .ok (c', s',
  ch', tr)`; `step_complete_any_wf`; `stepFn_consumption_none/_some` and `stepFn_oblivious`
  (the trace is stream-independent, carried through); `stepMulti_sound : … → StepM ctx m
  m' ev.trace`; `stepM_complete : StepM … tr → ∃ ch ch' ev, stepMulti … = .ok (m', ch',
  ev) ∧ ev.trace = tr`; `stepFn_selectApply_inv` adds `tr = []`; `step_preserves_wf(_loc)`
  over the labelled relation; every StateWf/MachineSound/MultiSound/MultiWfSound/
  MultiStreams/EnumDedupSound/UnseqSound helper lemma restated (`Mem.*_eq`,
  `Mem.store_pres/_shape/_congr`, `Mem.storeElems_pres`, `Mem.loadRun_locSup`,
  `Mem.storeRun_pres`, `Mem.loadSlice_size`, `loadResults_locSup`, `validateSlice_none`,
  `bind2_pair_stream`/`bind3_pair_stream`, …). No `sorry`/`axiom`/`native_decide`, no
  `partial` in the core, warning-free.
- The consult MIRRORS read through the machine's own op: `appendSpill?` (Machine.lean) and
  `EnumDedupCheck.appendApplyNoSpill` use `Mem.loadSlice`.
- THE AUDIT INSTRUMENT: the tracer (`GoLean/ChoiceTrace.lean`) compares, per pool step and
  per init step, the step's emitted `.data` trace with the footprint TABLE's account
  (`stepAccesses ctx σPre cPre` under `raceUpdate`'s rule — nothing when the goroutine
  became panicking from a non-panicking configuration; a spawn: the child's
  `dispatchAccesses`; the pool's own steps: nothing), as MULTISETS (sorted canonical keys);
  a difference is an `alarm` (`trace-mismatch: …`, so the corpus run exits 1 and lists it)
  and a `trace-mismatch` record — two new TSV columns `traceMismatches`,
  `firstTraceMismatch` (the summarizer reads columns by name; the existing columns are
  untouched). The sync-word / channel-object / atomic recordings of `raceUpdate`'s
  registry arms are outside this audit (S2c's emissions).

### Semantic disclosures (charter §4; none differential-visible, all recorded)

1. `mapDelete` of an ABSENT key now rewrites the unchanged payload through `Mem.mapWrite`,
   so the write is EMITTED (gc instruments `mapdelete` as a write unconditionally — the
   footprint table always said so; the heap content is unchanged).
2. The in-place append's nil-base refusal «cannot append … element(s) into nil slice in
   place» is now `Mem.storeRun`'s «malformed GoCore nil slice with length …» — UNREACHABLE
   (a nil base passes `validateSlice` only at cap 0, so nothing is ever appended in place).
3. `Mem.loadRun`/`Mem.storeRun` at a nil base with a non-empty run refuse with
   `sliceIndexLoc`'s text — unreachable likewise (`copy`/`clear`/append validate first).
4. `sliceVisibleValues` is redefined over the structural `Mem.loadElems` — the same loads
   at the same paths (`sliceIndexLoc slice i = .index base (offset + i)` under
   `validateSlice`), the same errors; the `forIn` shape and its proofs are gone.
5. `unseqStorePlan`'s binder-value loads are PEEKS (machine-internal binder cells; the
   table recorded nothing there), while the binder WRITES emit (the table recorded them):
   the trace keeps the table's account, EQUAL by construction; the principled alternative
   (no emission at all on binder cells — verdict-neutral, no goroutine can name them) is
   named for S2b/S2c.

### Peek-class call sites (the inventory the module docstring will carry at S2b)

Address formation: `indexTargetLoc`'s base load, `resolveChain` (through it), `applySlice`'s
array-size load, `projChainTarget`'s root check, `unseqUnfrozenAnchor?`. Metadata:
`lengthOf`/`capacityOf` on pointer-to-array (type-static in gc) and on channels (U2:
`c.qcount` uninstrumented). RMW peeks before an emitted payload write: `mapAssignValue`
(`mapEntries`), `mapDelete`, `clearMap`. Machine bookkeeping: `unseqStorePlan`'s binder
loads, `stepFrameExit`'s targetless-with-results `loadMany` (a refusal, no step). Drivers:
`loadMany` at termination (`runFunctionWithContextM`, `runProgramM`, the pool/enumerator
readouts). Synchronization (not `.data`; S2c's keys): `chanCell`/`chanPayload?`/
`storeChanPayload`, `syncCell`/the `.syncData` stores, `applyAtomicOp`'s cell traffic.
Fresh allocation (no event): `Store.alloc`, `allocDecls`, `bindParams`, `bindIterVars`,
`seedGlobals`, `makeMap`/`makeChan`'s payload cells.

### The trace-equality audit — RESULT

`trace-audit-s2a.txt`: whole corpus (the standing 2 exclusions), 6 streams per row,
**21,835 (row, stream) results, 0 trace mismatches** — the module's emitted `.data`
trace EQUALS the footprint table's account on every step of every traced run (BUG-041's
class included: `race/free/array-dyn-index-read-write` traced, equal). Choice-trace
byte-identity vs main `68b261e6` (D4): sorted dumps `cmp` EXIT=0, 23,685 records, sha256
`70e12e02…eb57` both sides (the S1 record's very hash); the tracer's FINDINGS listing is
the ONE pre-existing ERROR line (`arrays/materialization-budget/over-budget`, a lowering
refusal), identical modulo the artifact directory in its wire path. Positive control
(`trace-probe-s2a.txt`): a variable read, a constant-index ARRAY projection (the narrowed
leaf) and one phase-2 store each emit exactly the table's access.

The RAFT TWIN (`twin-audit-s2a.txt`; the pinned `baselines/pins/twin-chdriver.wire`,
`raft-twin/probeTwin{Choice,Single,Elect,Perturb,Ticks}` × 6 streams, fuel 10,000,000): the S2a
binary **30/30 (row, stream) results ok, 0 trace mismatches, 0 alarms** (1136 s wall,
14,360 consumption records); main's certified binary on the same batch 1004 s; sorted dumps
`cmp` EXIT=0 — BYTE-IDENTICAL (14,361 lines each side).

### Gate lines

`GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (11:17:29–11:29:48
UTC) on the staged S2a runtime tree (byte-identical for `GoLean/` and `Tests/` to the committed
tree; snapshot `refs/snapshots/c1/s2a-gated`): **EXIT=1, 739 s**; **3676 cases: 3427 PASS /
249 expected FAIL**; `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit`
ok; `unseq scheduler (Stage B)` ok; `frontend pins` ok; `wire boundary` ok; `engine-isolation`
ok; every other step ok. RED: exactly the two 5a-class items — `certificate provenance` (C9
HIGH: «STALE certification: changed dependency build/files/GoLean/CLI.lean») and `baseline diff
(DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] ->
now[FAIL/membership]` — the one cached certified row, judged stale because compiled semantic
inputs changed (the S1 gate's very shape). ZERO other drift; the negative baseline matched (394
cases). Static checks at the commit tree: `check-bugs.sh` ok (111 bugs), `check-evidence-size`
PASS (0 new offenders), `check-agents-alias` PASS. Tail: `gate-tail-s2a.txt`.
