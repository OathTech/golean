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
