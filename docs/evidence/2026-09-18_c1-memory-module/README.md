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
   fail-OPEN vs `-race`. Pre-existing, independent of C1; filed as BUG-111
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

### Semantic disclosures (S1; the second added at the audit fix round, 2026-09-18)

1. An UNBOUND root under a path: `Store.updateCell`'s `.internal` where the former leaf-first
   recursion reported `loadLoc`'s `unbound GoCore heap location` `.stuck` — a refusal-CLASS change
   on a path unreachable by heap density (BUG-085's argument); disclosed at S1 (handoff §5).
2. **A path write THROUGH an identity-normalized root — REFUSED at S1, RESTORED at the audit fix
   round (F3).** `isNormalForTyTy` answers `true` for ANY value at `.interface` and at the catch-all
   kinds (`.bool`/`.string`/`.slice`/`.map`/`.pointer`), so an `.interface`-declared cell holding an
   array or a struct is `HeapNormal`; main `68b261e6`'s leaf-first `storeLoc` accepted a path write
   into it (load base → set → store root → normalize at `.interface` = identity) and the S1
   `Ty.stepDown` had no arm for those types — it refused «leaf descent: the declared type has no
   element type / no field f» — while the module docstring claimed byte-identity «on every normal
   cell». Undisclosed until the audit (its Lean witness `probe-IfaceCell.lean`/`.log`, re-run here
   after the fix: `HeapNormal` true, store `.ok`, the leaf reads 5, the written store still
   `HeapNormal`; the non-normal `.int`-declared control still refuses); unreachable from Go as far
   as the audit could construct (interface contents are not addressable; 13 leaf probes + 34
   subjects SAME on both binaries). Fix: `Ty.stepDown` returns the identity type ITSELF at the same
   bound on either step, so the leaf normalizes at the identity exactly as the whole root did;
   `writeAt_isNormal_array/_struct` close the new alternatives by the `true` arm; five pins in
   `Tests/GoCoreContract.lean` (`iface_cell_path_write_normal/_array/_struct/_preserves_normal`,
   `slice_cell_path_write_array`). The residual `Ty.stepDown` refusals are reachable only on a
   NON-normal cell, where main also refused (with the whole-root normalizer's text) — a refusal-TEXT
   difference on an unreachable state, disclosed.

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


## S2b-i — the fold and the theorem (2026-09-18)

### What landed (one gated runtime commit; the table retained for ONE more commit)

- `raceUpdate` (Multi.lean) FOLDS THE LABEL: the private-step arm records
  `RaceState.accessKeys i ev.trace`, the spawn arm `r₁.accessKeys child ev.trace` (the child's
  frame-entry read). The former pre/post-panicking discrimination over
  `stepAccesses ctx sPre cPre` is gone — a delivered panic's label is `[]`.
- `footprintsConflict`/`RacyFine` (NPDRF.lean) restated over the two goroutines' next-step
  `StepE` labels (`ShadowKey.overlap` + `AccessKind.conflicts`); the deprecated
  `NPDRFReduction` untouched (D8).
- **`accesses_eq_stepAccesses`** (`GoLean/GoCore/AccessTableEq.lean`, 1496 lines, 60
  theorems, 5 tactic macros, warning-free, no hatch): for every rule of the labelled `Step`,
  `tr = tableTrace (stepAccesses ctx s c) ∨ (tr = [] ∧ c'.isPanicking = true)` — EXACT
  equality (order included) on a non-panicking successor; `spawnStep_trace` for the spawn's
  child-entry read (`dispatchAccesses`); one lemma per emitting helper. The D6 (c) companion
  to the executable audit: it covers the configurations the corpus never reaches. It leaves
  with the table at S2b-ii; the handoff §1 row names this commit as its proving SHA.
- Two runtime tightenings the proof forced, both differential-invisible: `sortSlice`'s
  `for` accumulator → structural `intElems` (same refusal at the first non-int element; the op
  is dead); `len`/`cap` of a pointer-to-array REFUSE a non-pointer operand by name instead of
  answering from the static type alone (the table classified the arm by the VALUE's shape).
- `StateWf.applyStrictOp_wf` follows the nested match (two arms).

### The fold's one corner (recorded, [AGENT])

The old fold and the new agree on every step whose successor is NON-panicking by the theorem
(EXACT equality of the label and the table's account there). On a step whose successor IS
panicking the theorem says only «label = table OR (label = [] ∧ panicking)» — it does NOT by
itself say the two folds agree; they do, BY INSPECTION OF THE RULES (audit fix round F4,
2026-09-18): every `Step` rule and every `stepFn` arm whose successor is `.panicking` from a
non-panicking pre-configuration carries the label `[]` — the `deliver`/`deliverS` panic
branch (StepFn.lean's `deliverS` returns the PRE-apply store with `[]`), the direct
constructions `callValCalleeNil`/`callValArgsNil`/`frameDeferNilFall`/`frameDeferNilReturn`/
`panicArgValue`/`panicResumeContinue` and `stepFn`'s own `.panicking` constructions, all `… []`
(the sync arm's `.wgAdd` negative-counter panic is a sync-word write, not `.data`) — and the
old fold recorded nothing on exactly those steps. The exception is one step from an ALREADY
panicking pre-configuration: a deferred-call
entry DURING UNWINDING (`panicFrameDefer`, pre-configuration already panicking) whose
receiver load panics — an out-of-range element ADDRESS dereferenced by the dispatch
(`loadLoc` → `arrayGet`). The table recorded the read at the leaf; the label records nothing
(the read never happened). Unreachable from a well-formed program (element addresses are
bounds-checked at formation); the label's account is the standing convention applied
uniformly.

### Audits

THE WHOLE-CORPUS TRACE AUDIT with the S2b-i binary (`trace-audit-s2b1.txt`; both accounts still
live in the tracer): **21,835 (row, stream) results, 0 trace mismatches**; the choice trace vs
main `68b261e6` BYTE-IDENTICAL (sorted dumps `cmp` EXIT=0, 23,685 records, sha256 `70e12e02…eb57`
both sides — S1's and S2a's very hash); the tracer's one pre-existing ERROR finding
(`arrays/materialization-budget/over-budget`) identical modulo the artifact path; 484 s wall.

THE RAFT TWIN (`twin-audit-s2b1.txt`): **30/30 (row, stream) results ok, 0 trace mismatches, 0
alarms** (1158 s wall, 14,360 consumption records); sorted dumps `cmp` EXIT=0 vs main's twin dump
— BYTE-IDENTICAL (sha256 `37e1c156…` both sides).

### Gate lines

`GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (12:59:21–13:11:41
UTC) on the S2b-i runtime tree (byte-identical for `GoLean/` and `Tests/` to the committed tree;
snapshot `refs/snapshots/c1/s2b1-gated`): **EXIT=1, 740 s**; **3676 cases: 3427 PASS / 249
expected FAIL**; `eval tests` 211 ok; `core build (warning-free)` ok (the new module included);
`core totality audit` ok (every `GoLean/` module incl. `AccessTableEq`); `unseq scheduler` ok;
`frontend pins` ok; `wire boundary` ok; every other step ok. RED: exactly the two 5a-class items —
`certificate provenance` (C9 HIGH: «STALE certification: changed dependency
build/files/GoLean/CLI.lean») and `baseline diff (DRIFT)` with the SINGLE line
`imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` (the one
cached certified row). ZERO other drift — the fold moved no race verdict; the negative baseline
matched (394). Static checks at the commit tree: `check-bugs.sh` ok, `check-evidence-size` PASS,
`check-agents-alias` PASS. Tail: `gate-tail-s2b1.txt`.


## S2b-ii — the deletion (2026-09-18)

### What landed (one gated runtime commit)

- `Race.lean`: the FOOTPRINT TABLE family — `RaceAccess`, `sliceElemLocs`, `mapAccess`,
  `targetWrite`, `strictOpAccesses`, `dispatchAccesses`, `deferEntryAccesses`,
  `stmtOpAccesses`, `storeTargetAccess`, `unseqRunAccesses`, **`stepAccesses`**,
  `RaceState.access`/`accesses` — DELETED with tombstones naming where the accesses come
  from now; the 256-line header (the curated-table rationale, O1/U1–U5, the 250-line
  call-site inventory) replaced by a header that records the deletion, its two grounds (the
  audit, the theorem), and U5's statement verbatim; `RaceState.accessKeys` is the one recorder.
  The atomic arm of `raceUpdate` records through `accessKeys … (.data loc)` (formerly
  `accesses`).
- `Ops.lean`: the module docstring «The memory module's access discipline — what emits,
  what peeks» right after `AccessTrace` — the peek inventory (address formation, type-static
  and uninstrumented metadata, the map RMW's entry peek, machine-internal binder cells,
  drivers, synchronization, fresh allocation, `&*p`) and O1's residual, in the module's own
  terms.
- `GoLean/GoCore/AccessTableEq.lean` DELETED with the table it audited (its proving SHA is the
  S2b-i row of the handoff §1); the `GoCore.lean` import removed.
- `ChoiceTrace.lean`: the table-side audit retired (`tableAccount`, `Acc.checkTrace`,
  `Acc.auditPoolStep`, `accessKey`/`traceMultiset`/`configKind`/`stepActionName`, the
  `mismatches` fields, the two TSV columns `traceMismatches`/`firstTraceMismatch`; the pool
  and init call sites); a tombstone records the two runs it made (0 mismatches).
- The dead write-path primitives `arraySet` (Ops.lean) and `StructFields.set` (State.lean)
  and their six lemmas (`arraySet_locSup`, `StructFields.set_locSup`, `StructFields.set_congr`,
  `arraySet_congr`, `StructFields.set_noPanic`, `arraySet_ok_of_arrayGet_ok`) DELETED (owed
  since S1); docstring mentions in NPDRF/MachineSound/Multi/Unseq/Ops reworded to the label.
- Diffstat: 11 files, +177 / −2369 lines.

### The detector-soundness re-run — the S2b diagnosis, WITHDRAWN at the audit fix round (F2)

`detector-soundness-s2b.txt` (the S2b transcript, kept as the record of what was seen).
`scripts/detector-soundness --select in-scope --jobs 6` ran twice from this worktree at S2b: with
the S2b-i (fold) binary and with the S2a (pre-fold) binary as the control; **the machine side was
identical pre-fold and post-fold on all 639 in-scope rows** (verdict, single-run status, members,
race members); against the recorded 2026-09-02 tip matrix (364 rows), 12 machine verdicts differ,
each by a change main took between 2026-09-02 and `68b261e6` (BUG-080's fix makes the two former
HOLEs RACE-ALL; atomic-frontier and sites-bound rows now DRF; two rows refused for
`params-omit-sites=`), and the pre-fold control reproduces every one — none is the fold's. The gc
side was `gc-no-verdict` on every row, both runs EXIT=2, and S2b wrote: «the gc `-race` side cannot
run here — TSan … dies at the sync-allocator growth with EXIT 78 … the reservation is refused by the
sandbox». **That sentence is WITHDRAWN (audit F2, 2026-09-18).** The true cause: the harness's
oracle crash hook (`tools/coverageharness/crashhook.go` `_goleanSetupCrash`) opens `oracle.crash`
WITHOUT `O_CREATE` and `os.Exit(78)`s when it is absent — «a setup failure, never an observation»;
`scripts/diff-coverage` resets `oracle.crash`/`oracle.registered` before every draw and
`scripts/detector-soundness` NEVER created them, so EVERY `-race` harness here exited 78 by design
(the runner, 2026-09-02 `05d0ec54`, predates the hook, which landed with L4 on 2026-09-07
`60bbf466` — the 2026-09-02 matrix had gc verdicts; every run since L4 would have shown this).
TSan itself runs in this sandbox (the auditor's `go run -race` of a racy program reports two races).
The runner is FIXED at the fix round (the reset mirrored verbatim before every `-race` run; a failed
reset is INFRA, the matrix INCOMPLETE) and the S2 exit check «HOLE = 0, other cells unchanged» was
run OFFICIALLY with the fixed tracked runner at the fix-round tip — see «Audit fix round» below.

### Audits

THE WHOLE-CORPUS CHOICE-TRACE RUN with the S2b-ii binary (`trace-audit-s2b2.txt`; the tracer's
table-side audit is gone, so this is the byte-identity check alone): **21,835 (row, stream)
results**, statuses identical to S2a's census (ok 17,957 / panic 2,284 / unsupported 1,095 /
race 252 / deadlock 162 / fatal 54 / stuck 30 / ERROR 1); the choice trace vs main `68b261e6`
BYTE-IDENTICAL (sorted dumps `cmp` EXIT=0, 23,685 records, sha256 `70e12e02…eb57` both sides —
the fourth time this hash); the one pre-existing ERROR finding identical modulo path; 443 s.

THE RAFT TWIN (`twin-audit-s2b2.txt`): **30/30 (row, stream) results ok, 0 alarms** (1116 s
wall, 14,360 consumption records); sorted dumps `cmp` EXIT=0 vs main's — BYTE-IDENTICAL (sha256
`37e1c156…` both sides).

### Gate lines

`GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (13:36:01–13:48:17
UTC) on the S2b-ii runtime tree (byte-identical for `GoLean/` and `Tests/` to the committed tree;
snapshot `refs/snapshots/c1/s2b2-gated`): **EXIT=1, 736 s**; **3676 cases: 3427 PASS / 249
expected FAIL**; `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit` ok (45
modules, 36 under GoCore — one fewer with `AccessTableEq` gone; 51 required theorems present);
`unseq scheduler` ok; `frontend pins` ok; `wire boundary` ok; every other step ok. RED: exactly
the two 5a-class items — `certificate provenance` (C9 HIGH: «STALE certification: changed
dependency build/files/GoLean/CLI.lean») and `baseline diff (DRIFT)` with the SINGLE line
`imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` (the one
cached certified row). ZERO other drift; the negative baseline matched (394). Static checks at
the commit tree: `check-bugs.sh` ok, `check-evidence-size` PASS, `check-agents-alias` PASS. Tail:
`gate-tail-s2b2.txt`.

## Audit fix round — the audit's F1–F10 fixed (2026-09-18)

The pre-merge adversarial audit `docs/2026-09-18_c1-memory-module-audit.md` (branch
`review/c1-memory-module-0918`, commit `ba6b249c`; its evidence
`docs/evidence/2026-09-18_c1-memory-module-audit/` there) returned FIX-FIRST, records-class.
Dispositions and where each fix lives: handoff §8. Two commits on the lane: the RUNTIME commit
`16029fa8` (F3 restore + proofs + pins, F7 check + inventory + `scripts/ci` step, F2 runner fix, F1/F6
comment fixes) and the records commit over it. Binary at the runtime tip: `.lake/build/bin/golean`
sha256 `42b7bf1ab5f2b17e…` (= `.tmp/golean-fix`, the binary the detector-soundness matrix and the
choice-trace subset below ran).

### Warms (sequential, captured exits, `LEAN_NUM_THREADS=4 GOLEAN_MEM_MAX=32G scripts/capped lake build …`)

| target | exit | wall | note |
|---|---|---|---|
| `GoLean.GoCore.StateWf` (after the `Ops.lean`/`StateWf.lean` edits) | 0 | 27 s | 13 jobs, 0 warnings — `writeAt_isNormal_*` accept the identity alternatives: `HeapNormal` preservation holds with the restoration |
| `GoLean golean` (first try) | 1 | 59 s | `MachineSound.lean` `Ty.stepDown_noPanic`: the hand-bulleted `succ` case assumed four match arms (now ten) — restated order-independently |
| `GoLean.GoCore.MachineSound` | 0 | 58 s | 15 jobs, 0 warnings |
| `GoLean golean` | 0 | 20 s | 97 jobs, 0 warnings; binary `42b7bf1a…` |
| `GoCoreAuditTests` (the five pins) | 0 | 3 s | first try EXIT=1: no `DecidableEq (Except Stop Bool)` for the `preserves_normal` pin's `by decide` → `rfl` (the three sibling `rfl` pins passed at once) |

### The F3 witness, re-run after the fix (`probe-IfaceCell.lean` / `.log`; `scripts/capped lake env lean`, EXIT=0)

`HeapNormal` true / `loadLoc` leaf `ok (int 0)` / store then load → `ok (ok (int 5))` / the written
store `HeapNormal` → `ok true` (interface cell holding an array); the interface-cell-holding-a-struct
twin → `ok (ok (int 5))`; a `.slice`-declared cell holding an array (the catch-all class) → `true`,
`ok (ok (int 5))`; the NON-normal control (`.int`-declared cell holding an array) → `HeapNormal`
false, `stuck "leaf descent: the declared type has no element type"` (main refused it too, with the
whole-root normalizer's text); a width-wide `.int 300 .int8` written under the interface root stays
`300` (identity — exactly main's whole-root identity normalization). The `#eval`s preceded every
`decide`/`rfl` pin (`Tests/GoCoreContract.lean`).

### The official detector-soundness run (F2) — `scripts/capped scripts/detector-soundness --select in-scope --jobs 6 --out artifacts/detector-soundness/fixround-official`

Binary `42b7bf1a…` (this tree's), the FIXED tracked runner, go1.26.5, 639 in-scope rows, 5 runs × GOMAXPROCS {1, 8}.
EXIT=2 (INCOMPLETE for the 9 `params-omit-sites=` membership refusals, as at S2b and in the audit), 28 min 48 s; 639 rows: **HOLE 0, possible-HOLE 0**, agree-DRF 502, agree-race 36, over-refusal 6 (`race/free/array-dyn-index-read-write` = BUG-041's O1 residual, and the five `race/gomem-only/*` rows of the RULED go_mem-RACY / TSan-GREEN lane, BUG-084's `Cases:` line), refused 9, uncertified 86 (the machine side's ENUM-FAIL classes: deadlock members, frontend-quarantined subjects, sites bounds, one fuel truncation; gc green or no verdict there) — cell for cell the audit's patched-copy run. One blemish on this first official run, CAUSED BY THE FIX-ROUND WORKER and recorded: its worker-pool exit was 127 with one bash message `scripts/detector-soundness: line 387: -d: command not found` after the last row. Cause established: the worker edited `scripts/detector-soundness` (the amend's one comment line inside `run_row`) WHILE the runner was executing; bash reads a script by byte offset, so when `xargs` returned the parent resumed mid-line in the shifted file, ran `-d '\n' -I{} … | tee …` as a command and took that pipeline's `PIPESTATUS[0]` = 127. The 639 row workers had already completed (their function bodies were exported at start; `progress.txt` 639/639 before the message), the assemble step reads every `row.tsv` from disk, gc-infra 0, unclassified 0 — no cell is affected, and the runner's exit is the 9 refusals' either way. A one-row re-run of the last manifest row with the committed runner: pool exit 0, no message. The matrix was then RE-RUN in full with the committed runner, untouched: re-run 21:03 UTC, `artifacts/detector-soundness/fixround-official-2`, 28 min 49 s, **worker-pool exit 0, no message**, EXIT=2 for the same 9 refusals; **cells IDENTICAL on all 639 rows** — HOLE 0, possible-HOLE 0, agree-DRF 502, agree-race 36, over-refusal 6 (the same six rows), refused 9, uncertified 86; this clean run is the evidence file's primary record (`detector-soundness-fixround-summary.txt`), the first run kept beside it. Lesson (handoff §6c): never edit a script that is running. Summary + meta: `detector-soundness-fixround-summary.txt`.

### The raw call-site inventory (F7) — `scripts/check-mem-callsites`

`scripts/mem-callsites.tsv` at the runtime tip: **78 (file, declaration, raw-op) rows**, every one with
a reason (`mem-callsites-fixround.txt` is the check's PASS line + the census). By class, counted
from the file's reason prefixes: module bodies 16 (the 5 emitting operations' own peeks/writes, the
4 peek primitives `loadLoc`/`mapPayload?`/`chanPayload?`'s lookups and `loadLoc`'s recursion, the 3
raw-writer primitives, the drivers' `loadMany` 2, the sync peeks `chanCell`/`syncCell` 2); address
formation 4 + type-static metadata 2; the map RMW's entry peek 1; machine-internal binder cells 1;
driver readouts 8 + Prop-level relation premises (`Step`'s `initialization`, `ProgramRun`) 2 + the
refusal text naming `Store.alloc` 1 + `stepFrameExit`'s readout-that-is-a-refusal 1; synchronization
(chan-object / sync-word / atomic traffic) 22; the detector's registry arms reading `sPre`/`tsPre`
cells (S2c retires them) 6; fresh allocation 10; the DEAD `storeMany` 2 (deletion owed to S3); the
choice tracer's read-only observations 2 — total 78. Self-tests (the tracked inventory mutated and restored byte-identically): a
removed row → `NEW … applyAtomicOp loadLoc 1` + the two resolutions, an invented row → `STALE`,
both EXIT=1; a two-column row → «malformed inventory … (fail closed)» EXIT=1; restored → PASS EXIT=0.
Wired into `scripts/ci` as a static step after the engine-isolation lint.

### The choice-trace subset (the auditor's 307 ids; `scripts/choice-trace-corpus --dump --jobs 6`)

Fix-round binary `42b7bf1a…` vs main `68b261e6`'s certified `231df9a9…` over the ids in the audit's
`choice-trace-subset-ids.tsv` (every 12th executable row, the 2 standing exclusions removed): **303 ids
traced, 1,818 (id, stream) lines** each side (by lane: strict 285, membership 9, confluent 7, racy 2;
0 ERROR), tracer EXIT=0 both (43 s / 51 s); sorted consumption dumps **2,690 records each, one
sha256 `bd48dac56d3e1fb1…`, `cmp` EXIT=0 — BYTE-IDENTICAL** (`choice-trace-subset-fixround.txt`).

### Gate at the runtime tip `16029fa8`

`GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (20:18:14–20:32:18 UTC; lock acquired after 0 s), the committed runtime tree `16029fa8` (clean for `GoLean`/`Tests`/`scripts`; `docs/` dirty with the records edits — the negative-diff step notes `git_dirty=true` for that reason): **EXIT=1, 844 s**; **3676 cases: 3427 PASS / 249 expected FAIL** (`differential coverage summary: cases=3676 pass=3427 fail=249`); `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit` ok; **`memory-module raw call-site inventory (emit/peek discipline)` ok — the NEW step, GREEN at this tip (78 rows)**; `unseq scheduler` ok; `frontend pins` ok; `wire boundary` ok; every other step ok. RED: exactly the two 5a-class items — `certificate provenance` (C9 HIGH: «STALE certification: changed dependency build/files/GoLean/CLI.lean») and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` (the one cached certified row). ZERO other drift; the negative baseline matched (394). The binary after the gate's rebuild is byte-identical to the one the detector-soundness matrix and the choice-trace subset ran (`42b7bf1a…`). Tail: `gate-tail-fixround.txt`. Records checks at the records tree: `check-bugs.sh` EXIT=0, `check-evidence-size` EXIT=0 (PASS, 0 new offenders), `check-agents-alias` EXIT=0, `check-spec-anchors` EXIT=0 (FR-34's anchors resolve at pin `c19862e5f`).


## Merge train r41 — the 5a record ([AGENT] coordinator, 2026-09-18)

[USER] Mike 2026-09-18, verbatim (relayed): «(1) agree, (2) agree. Go ahead». Pre-merge main `68b261e6` →
`refs/snapshots/r41/main`; C1 S0–S2b + the ratification record (`2bedbc68`) fast-forwarded; the audit
branch rebased (`f901c46c`) and fast-forwarded. Under the lock at `f901c46c`: `scripts/build-certified`
EXIT=0, 117 s (binary `42b7bf1ab5f2…` — the fix round's official detector-soundness binary);
`release-check --base refs/snapshots/r41/main` EXIT=2 (EXPECTED — «STALE certification: changed
dependency build/files/GoLean/CLI.lean»); `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` EXIT=1,
989 s — red on EXACTLY the 5a pair (`certificate provenance` STALE; the single drift line
`imported-goose/channel/google-search PASS→FAIL/membership`); `core-audit` PASS (14.8 s; the «error:
Core totality audit» line in the log is a compiled POISON CONTROL being rejected, as designed);
`memory-module raw call-site inventory` ok; 3676 rows otherwise unchanged; negatives 394 no regression.
Tail: `r41-ci-slow.tail.txt`. Candidate vs tracked record: `claim` and `observations` IDENTICAL; 26 input
hashes differ (C1's core files) and the receipt (clean `f901c46c`, binary `42b7bf1a…`) — INSTALLED in
this commit; a provenance refresh, not a re-pin. The green re-run is the full `ci --diff` at the records
commit.

**Green re-run at the records commit `30521bc3`** ([AGENT] coordinator, 2026-09-18): full
`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` → EXIT=0, `RESULT: PASS`, `baseline diff FULL
(3676/3676, no regression)`, `certificate provenance` ok, negatives 394 no regression; the reconciler back to
its single pre-existing finding after FR-34's proposed ids were written without backticks. Round 41 closed;
C1 S0–S2b are on main; the box-wide lock released.
