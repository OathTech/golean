# C1 S3 handoff — the rollback: validate-then-commit, the pre-step store no longer held (cost B(b); lane `core/c1-memory-module-s3-0919`, 2026-09-19)

Successor of `docs/2026-09-18_c1-memory-module-s2c-handoff.md` (S2c + BUG-111, LANDED on main at
train r42, `3b99f42f`/`0f114df6`). Authority: the C1 charter `docs/2026-09-17_c1-memory-module-charter.md`
(§2 cost B, §6 S3's targets; §7 D1–D7/D9/D10 RATIFIED [USER] Mike 2026-09-18 «(1) agree, (2) agree. Go
ahead», relayed by the [AGENT] coordinator — record `docs/2026-08-31_qrow-rulings.md`), and the sequencing
ruling that S3 completes C1 before Stage C. Every decision below is [AGENT] unless marked [USER]. Base: main
`0f114df6`. Worktree `.claude/worktrees/c1-s3`. Evidence `docs/evidence/2026-09-19_c1-memory-module-s3/`.
Completion note: `docs/2026-09-19_c1-memory-module-completion.md`.

## 0. Where the lane is

S3 is ONE gated runtime commit **`fd99b021`** (+ this records commit). Gate at the runtime tree: §2.
The four charter §6 targets are MET on the AFTER run (§3), including the `append_grow` ratio S1 owed; the AFTER-2
confirmation run on the committed binary repeats them except two single ratio steps over the line by the letter
(×4.49 vs 4.4, ×2.29 vs 2.2 — §3; reported as misses on those steps, not re-fitted). BUG-090: §5.
PENDING [USER]: §7. The adversarial-audit ask: §8. Not merged, not pushed; main untouched.

## 1. The census — every site that held a pre-step store or state across an apply (item 1 of the brief)

Read at `0f114df6` (the S0 census `docs/2026-09-18_c1-memory-module-handoff.md` §4 re-read; bug090 §3 B).
A "retention" is a second live reference to the `Store` (hence to `heap : Array HeapCell`) at the moment a
write (`Array.push`/`Array.set` through `Store.allocCell`/`Store.updateCell`) runs — Lean then copies the
whole array (`lean_copy_expand_array`, ≈4.4 ns × H per write; the rediagnosis profile). The sites:

| site | what held the store | S3 |
|---|---|---|
| `stepFn`'s 17 `deliverS s …` sites (StepFn.lean) | `deliverS s k ch next r` keeps `s` for its `.panic` arm, so `s` is live across `applyX ctx s …`; at the 9 sites whose apply WRITES (stmt-op apply, storeK, the 7 frame entries incl. `stepFrameExit`'s defer and the panicking frame's defer, the unseq load) every write copied the heap | **SPLIT** → `deliverV` (§2): the apply's VALIDATE phase borrows `s`, its COMMIT owns it |
| the 8 other `deliverS s` sites: strict nullary/apply (read-only except `[]byte(s)`, `[]rune(s)` — TWO allocating arms; audit F3 2026-09-19 [AGENT]: slicing an array value is NOT a third — `applySlice` returns its store unchanged in every arm and refuses the non-addressable array-value form by name, and the inventory agrees, `applyStrictOp alloc 2`), the target-shift nil check and the comma-ok source (read-only), `applyChanOp`, `applySelect`, `applySyncOp`, `applyAtomicOp` (synchronization traffic: channel/sync-word cells) | the same | **KEPT with the reason in `deliverS`'s docstring**: no write → no copy for the read-only ones; the two strict conversions and the four synchronization applies pay one heap copy per such op — OWED (§6) |
| `stepThread` (Multi.lean): `Thread.afterStep s c c'` after `stepFn ctx s c ch₁` (and after `spawnStep`, `commitClause`, the select interception ×2) — `Config.afterStepFlag σ c c'` reads `c.registryCommits σ` on the PRE-step store AFTER the step | `s` live across EVERY pool step's writes (incl. `stepFn`'s direct arms `initialization`/`block`) | **FIXED**: `Config.boundaryFacts σ c` (spawn? / commits?) computed BEFORE the step; `Thread.afterStepWith facts c'` — `= Thread.afterStep σ c c'` by `rfl` (`Thread.afterStepWith_boundaryFacts`); the relation's `StepM.thread` still names `Thread.afterStep` |
| `spawnStep`: `deliver s .stop … r` after `enterFramePick ctx s …` | `s` live across the child's entry allocations | **SPLIT**: `enterFramePickV` + `runCommit c s`; the panic arm returns the untouched `s` |
| the select interception's `deliver s k' … (.panic msg)` (`stepThread`) | `s` live across `applySelect` | KEPT (the select apply is owed, above) |
| `stepThreadInto`/`stepMulti`/`execProgLoop`/`execProgLoopOut`/`runConfig`/`enumInitRun` (the drivers) | `m`/`s` passed as the LAST use (verified by reading; S2c-ii removed `raceUpdate`'s pre-state args) | no retention; unchanged |
| the enumerator `EnumDedup` (`nd.m` retained in the visited set / DFS frontier; `stepMulti ctx nd.m vec` per branch) and the choice tracer `ChoiceTrace.poolStep`/`feedPicks` (`stepMulti ctx m …` re-run on one `m` per probe) | by DESIGN: exploration keeps states to branch from (the charter's B(c)); the tracer is tooling | **THE BOUNDARY**: not S3's; exploration pays its fork copies at the fork, the machine's own step no longer forces any |

The write-then-panic audit, re-read at the S3 tree (S0's N 118 / V 46 / W 8): the eight W arms are now V or
gone — `storeMany` DELETED (dead since the tgtOpK spine; its three StateWf lemmas with it); `makeMap`/
`makeChan` hoist the target's nil check ahead of the payload allocation (the two REACHABLE W arms: the hint-/
cap-less forms arrive without the operand nil check); `makeSlice` and `copySlice` hoist `valueAsLoc tv` ahead
of the allocation / the element writes (pure reorders — before S3 the delivery rolled those writes back on
that panic, so the observable is unchanged); `allocNew`/`makeSlice`'s path-target store and the element runs
of `clearSlice`/`copySlice`/`appendSlice` — the "W only under a header/backing inconsistency no `StateWf`
conjunct excludes" class — are V because the write path no longer panics at all (§2, `arrayIndexNatFormed`).

## 2. What landed — the validate/commit seam (item 2 of the brief)

**The write path never panics.** `writeAt`'s index re-check is `arrayIndexNatFormed` (Ops.lean): a store
reaches an `.index` step only through an address the machine FORMED under Go's bounds check
(`indexTargetLoc`/`resolveChain`, `sliceIndexLoc`/`applySlice`, the header bounds of an element run) and
arrays never shrink, so an index outside the array there is a dangling formed address — a machine-invariant
breach (BUG-085's class), `.internal` by name, never a recoverable Go panic. Before S3 it was `arrayIndexNat`'s
Go-panic text, delivered as a rolled-back `.panicking` step. **A refusal-class change on a path no well-formed
run reaches** (the S0 audit: reachable only under a header/backing inconsistency); the differential is the
regression (§2 gate: zero drift). Theorems: `writeAt_noPanic`, `storeLoc_noPanic`, `Mem.store_noPanic`,
`Mem.mapWrite_noPanic`, `Mem.storeElems_noPanic`, `Mem.storeRun_noPanic`, `bindParams_noPanic`,
`allocDecls_noPanic`, `pinResultLocs_noPanic` (MachineSound); the old `writeAt_noPanic_of_readAt_ok` is a
corollary.

**The seam** (Machine.lean, docstring at `Commit`): `Commit α := Store → Except Stop α`; `runCommit c s` runs a
commit, refusing BY NAME (`.internal`) a recoverable panic out of it (unreachable by the theorems below).
`Commit.withStream ch c` lifts a stream-free commit beside the stream. Every store-bearing apply `stepFn`
delivers is now `F := do let c ← F.plan s …; c s`, with `F.plan` the VALIDATE phase (reads, checks, panics —
the arm's original order) returning the COMMIT (writes only):

| family | `.plan` | commit | theorem `PlanNoPanic (F.plan …)` |
|---|---|---|---|
| `applyStmtOpCore` (13 arms) | operands, target nil check, len/cap/hint checks, map peek + key hash, element reads | `Store.alloc`/`allocCell` + `Mem.store`; `Mem.mapWrite`; `Mem.storeRun` (+ `Mem.store` of the count) | `applyStmtOpCore_commit_noPanic` |
| `applyStmtOp` (append) | the same + the R16 check, the old-element read, the capacity CONSULT (the pop is in the plan), the backing's construction | in place: `Mem.storeRun` + header `Mem.store`; spill: `Store.alloc` + header store — both `Commit.withStream choices …` | `applyStmtOp_commit_noPanic` |
| `mapAssignValue` | map peek, key normalization + hash (the nil-map panic) | `Mem.mapWrite` | `mapAssignValue_commit_noPanic` |
| `storeTarget` | `resolveChain` (nil/bounds), `valueAsLoc` | `Mem.store` (or the map arm) | `storeTarget_commit_noPanic` |
| `enterFrame` | lookup, arity, `dynamicDispatch?` (its nil panics; the dispatch READ is emitted here) | `bindParams` + `allocDecls` + `pinResultLocs` | `enterFrame_commit_noPanic` |
| `unseqLoad` | target lookup, the checked read | the binder cell's `Mem.store` | `unseqLoad_commit_noPanic` |

`PlanNoPanic p := ∀ c, p = .ok c → ∀ s, NoPanic (c s)` — **the per-arm «panic ⇒ store unchanged» as a
theorem**: a delivered panic is the validate phase's (`toResult_plan_inv_panic`), the commit never ran, the store
the step returns is the one the apply was given (`deliverV_panic`, `deliver_panic`). The relation is UNTOUCHED:
`Step`'s premises name the composed `applyStmtOp`/`storeTarget`/`enterFramePick`/`unseqLoad`; `deliver` is as it
was. The executable (`deliverV`, StepFn.lean) runs `toResult (F.plan ctx s …)` then, on `.ok c`, `runCommit c s`
— `s`'s ONE remaining reference on that path — and on `.panic msg` unwinds under `k` over `s` with the pre-apply
stream and `[]`. Coherence re-proved with the same labels (no `∃`): `stepFn_sound` (macros `deliverV_arm`/
`entryV_arm`), `step_complete`/`step_complete_any_wf` (`completeV_apply`/`completeV_entry`/`anyV_entry`, the
inversions `*_inv_ok`/`*_inv_panic`, `enterFramePickV_of_ok/_of_panic`), the consumption theorems at the plan
level (`applyStmtOp_plan_appendSlice_nospill/_spill`, `applyStmtOp_plan_of_stmtConsult?_none`,
`stepFn_stmtOp_oblivious/_spill` — the spill's post-consult tail is panic-free for EVERY target now, so
`stepFn_consumption_some`'s `appendTargetLocal` hypothesis is vacuous: kept as `_hloc` for its callers,
its removal a one-line follow-up), the ∀-choices kit (`applyStmtOp_appendSlice_congr` through the plan's
congruence, the commits compared AT `σ`), the pool (`stepMulti_sound`/`stepM_complete` by `rfl` on
`Thread.afterStepWith`; `spawnStep_shape`, `spawnStep_wf`, `spawnStep_oblivious` through `enterFramePickV`),
the enumerator's N-APP kit (`appendSpill?_of_noSpill` bridge). **The MERGE-INVARIANT statements are unchanged**
(`stepFn_sound`, `step_complete`, `step_complete_any_wf`, `step_preserves_wf`, `stepMulti_sound`, `stepM_complete`,
`stepThreadInto_sound`, `spawnStep_shape`, `spawnStep_wf`, `enterFrame_wf`, `applyStmtOp_wf`,
`applyStmtOp_appendSlice_congr`, `stepFn_consumption_none`, `stepFn_append_nospill`, `applyStmtOp_append_nospill`
— byte-identical to main's, and `inductive Step` untouched); THREE KIT LEMMAS ARE RESTATED at the plan level, with
their CONCLUSIONS unchanged — `stepFn_stmtOp_oblivious` and `stepFn_stmtOp_spill` (MachineSound) now take their
hypothesis over `applyStmtOp.plan … = r.map (Commit.withStream ch)` instead of over the composed `applyStmtOp`,
and `stepFn_consumption_some` renames `hloc` to `_hloc` (same type; the vacuity is §4 item 6). Their callers are
the consumption sweeps, which adapted. (Audit F4, 2026-09-19 [AGENT]: the earlier blanket «Statements unchanged
throughout» here was over-broad by exactly these three and contradicted the plan-level restatement this same
paragraph describes.) Deletions:
`storeMany` + `HeapNormal.of_storeMany`/`storeMany_shape`/`storeMany_pres`; the composed
`applyStmtOp_appendSlice_nospill/_spill`/`applyStmtOp_of_stmtConsult?_none` replaced by their plan-level
statements (their only users were the consumption sweeps). The NoPanic section of MachineSound moved
above the coherence proofs (with `Loc.rootLoc`/`rootLoc_eq`), unchanged in content.

**Gate lines** (captured `EXIT=`; tails in the evidence README):
- warms: `lake build GoLean.GoCore.Machine` EXIT=0 (Ops 6.2 s, Machine 4.4 s); `… StateWf` EXIT=0 (18 s);
  `… MachineSound` EXIT=0 (1:05); `lake build GoLean` EXIT=0; `lake build golean gocore-eval-tests …` (all test
  libs) EXIT=0 (2:21). Eval tests **267 ok**, EXIT=0 — the 56 label-shape facts unchanged.
  `scripts/check-mem-callsites` PASS at 70 rows (3 rows moved to the `.plan` declarations with the S3 reason;
  the 2 dead `storeMany` rows retired). `scripts/check-core-audit` PASS (5 controls).
- **`scripts/capped scripts/ci --diff`** — gate 1 at the S3 WORKING TREE (uncommitted, binary `12ebb0e1…`, 06:36–06:51Z; `gate-tail-s3-worktree.txt`): EXIT=1, 3686 cases, **DRIFT = exactly the one 5a-class row** (`imported-goose/channel/google-search` PASS→FAIL/membership: the cached certified row judged STALE by the provenance change), red on `certificate provenance` (STALE: `EnumDedupSound.lean` changed) and on six proof-only `unusedSimpArgs` linter warnings (the gate's core build must be warning-free; fixed in the commit — the binary's compiled code is unchanged); eval 267 ok, inventory PASS 70, core audit PASS, escape-hatch scans ok, negative corpus 394 = baseline; reconciler C9 HIGH (the 5a item) + the standing C13. **Gate 2 at the runtime commit `fd99b021` (clean tree, binary `ab355547…`): EXIT=1 (711 s, 07:01–07:13Z; `gate-tail-s3.txt`): 3686 cases, DRIFT = exactly the one 5a-class row (`imported-goose/channel/google-search` PASS→FAIL/membership), red ONLY on the 5a pair (`certificate provenance` STALE + that row); the six linter warnings gone (core build warning-free); eval 267 ok; inventory PASS 70; core audit PASS; escape-hatch scans ok; negative 394 = baseline; reconciler 2 findings, 1 HIGH = the 5a item**
- **choice trace, S3 binary vs main's `da7bb837…`, whole corpus (the 2 standing exclusions): BYTE-IDENTICAL — 24,037 records per side, sha256 `838d93e4…` both, `cmp` EXIT=0 (3650 rows exported per side, 34 frontend refusals per side, 2 excluded; both runs EXIT=1 = the runner's standing racy findings, 41 lines identical); `choice-trace-s3.txt`**
- **`scripts/detector-soundness --select in-scope --jobs 6` on the committed binary: 649 rows, EXIT=2 (the 9 standing refusals), 1,749 s (07:22:42–07:51:51Z; `--out artifacts/detector-soundness-s3`): HOLE 0 / possible-HOLE 0 / agree-race 41 / agree-DRF 507 / over-refusal 6 / refused 9 / uncertified 86 — CELL-FOR-CELL IDENTICAL to the prior official matrix (the S2c audit fix round's 649 rows: 0 rows added or removed, 0 cells changed, 0 machine verdicts changed, 0 gc verdicts changed); `detector-soundness-s3.txt`**

## 3. Benchmarks (item 3 of the brief) — BEFORE main `0f114df6` / AFTER the S3 tree / AFTER-2 the committed binary

`docs/evidence/2026-09-11_bug090-rediagnosis/run-probes.py --plan full`, 3 runs, medians, net of the empty
probe (the charter §6 protocol; «a miss is reported as a miss, never re-fitted»). BEFORE = main's binary
`da7bb837…` (load1 3.9→2.2, 05:23Z); AFTER = the S3 working tree's binary `12ebb0e1…` (load 1.9→2.3, 06:37Z; the
bytes the runtime commit carries — the proof-only edits that followed changed the binary's hash to `ab355547…`,
not its compiled code); AFTER-2 = the committed tree `fd99b021`'s gate-built binary `ab355547…`, re-run for the
record on a quiet box (load 0.97→0.99, 07:22Z). The full 67-point table with all three columns is
`bench-compare.md` (producer `bench_compare.py`, both in the evidence dir).

| charter §6 target | BEFORE | AFTER | AFTER-2 | verdict |
|---|---|---|---|---|
| `alloc_new` linear: n = 1k/4k/16k/32k successive ×4 ratios ≤ 4.4; n = 32k < 1 s | 0.039 / 0.263 / 3.66 / **14.12 s** (×6.8, ×13.9, ×3.9) | 0.025 / 0.099 / 0.429 / **0.844 s** (×3.9, ×4.3, ×2.0) | 0.025 / 0.097 / 0.434 / **0.865 s** (×3.8, **×4.49**, ×2.0) | **MET** on AFTER; AFTER-2: 32k < 1 s MET, the 4k→16k step ×4.49 is over the 4.4 line by 2 % — a MISS on that step by the letter |
| the (h) scalar phase (20k iterations after h = 0/1k/10k/40k live cells) within 1.2× of h = 0 | 0.258 / 0.385 / 1.78 / **6.83 s** (26×) | 0.257 / 0.266 / 0.287 / **0.289 s** (1.12×) | 0.283 / 0.285 / 0.270 / **0.264 s** (0.93×) | **MET** (both runs) |
| `append_grow` successive ×2 ratios ≤ 2.2 (OWED, missed at S1) | ×2.01, ×2.12, ×2.50, ×2.94 | ×1.93, ×2.02, ×1.84, ×1.97 | **×2.29**, ×2.04, ×2.17, ×1.97 | **MET** on AFTER; AFTER-2: the 250→500 step ×2.29 (a 5.9 ms base at the ±1 ms empty-probe noise floor) is over the 2.2 line — a MISS on that step by the letter; the ≥ 0.1 s steps ×2.17/×1.97 |
| scalar step baseline within 10 % | `scalar(80000)` 1.095 s | 1.057 s (−3.5 %; ≈270 ns/step) | 1.036 s (−5.4 %) | **MET** (both runs) |

Reading the two AFTER runs together: the same code gives ×4.34 and ×4.49 on the `alloc_new` 4k→16k step and
×1.93 and ×2.29 on the `append_grow` 250→500 step — the charter's 4.4 and 2.2 lines sit inside those two steps'
run-to-run jitter, while the load-bearing points are stable (32k in 0.84–0.87 s from 14.1 s; the (h) phase flat
at 0.93–1.13×; every `append_grow` step from 1000 on ≤ 2.17). Not re-fitted; the per-target verdicts are as the
table states them, and the coordinator's report carries both runs. Also: `alloc_make4` 16k 3.41 → 0.38 s;
`heap_then_append` 40k+300: 18.9 → 0.82 s; `write_fixed`/`read_fixed` unchanged (S1's flat values); the map
probes ±6 % (not a C1 target).

## 4. [AGENT] choices, with the alternative named

1. **The write path's index re-check is `.internal`, not a Go panic** (the enabling fact). Alternative: keep the
   panic and validate every write target with a peek in the plan (`storeLoc_noPanic_of_loadLoc_ok` + transport
   lemmas across allocations and element runs — including the corner `a[0].f = copy(a[0:], …)`, whose target
   lies inside an element the run overwrites, needing a shape-preservation lemma through normalization). Rejected:
   it re-checks what address formation already checked, adds raw peek sites, and the panic it would preserve is
   unreachable in a well-formed run — an invariant breach is what `.internal` is for (BUG-085's precedent).
2. **Closures as plans** (`Commit α := Store → Except Stop α`, the seam is one `return fun s => do …` per arm).
   Alternative: a first-order `Plan` inductive per family with a `commit` interpreter. Rejected for S3's scope
   (13 constructors mirroring the op table for no proof gain); the closure form makes the seam a one-line diff
   per arm and the commit's panic-freeness a `PlanNoPanic` fact.
3. **The composed apply keeps its name and type** (`applyStmtOp := plan >>= (· s)`), so `Step` and every
   existing theorem statement stand; proofs re-headed at the seam (`bind_eq_ok`). Alternative: a separate
   executable twin with an equation theorem — two accounts, rejected (the defect C1 removes).
4. **Held delivery kept for the synchronization applies and the strict conversions** (§1, §6) rather than
   splitting `applyChanOp`/`applySyncOpCore` (≈30 leaves; `applyChanOp_wf`/`applySyncOpCore_wf` re-headed) and
   `applyStrictOp` (71 `return (v, s, [])` arms; `applyStrictOp_wf` 640 lines) in this slice. Their cost is one
   heap copy per registry op / per conversion, on no S3 target; the recipe is the same seam. Alternative: split
   them now — a second S3 commit if the [USER] wants C1 to close them here.
5. **`boundaryFacts` computed before the step** (the pool rule's two pre-step facts) instead of restating
   `Thread.afterStep`'s inputs in `StepM`: the relation names the same `Thread.afterStep`; `stepThread` builds
   `Thread.afterStepWith facts c'`, `rfl`-equal. Alternative: pass the post-step successor into a rule that
   re-reads `σ` — that is the retention.
6. `stepFn_consumption_some`'s `hloc : c.appendTargetLocal` is now vacuous (the spill's tail is panic-free for
   every target) — kept as `_hloc` so no caller moves; a follow-up removes it.

## 5. BUG-090 — both mechanisms CLOSED; `Status:` stays `open` (the symmetric rule); the corpus follow-up owed

- Mechanism A closed at S1 (the entry's S1 re-measurement paragraph); mechanism B closed here — the S3
  re-measurement paragraph is in the entry (after the S1 one), and the rediagnosis note
  `docs/2026-09-11_bug090-rediagnosis.md` gains its §6 closing paragraph (§3 B's three retention sites named
  there, each closed: `deliverS`'s saved store → `deliverV`; `Thread.afterStep`'s post-step read → `boundaryFacts`;
  `spawnStep`'s entry on the owned store; the enumerator's states = B(c), exploration's by design).
- **`Status:` stays `open`.** `scripts/check-bugs.sh` rule (3) is SYMMETRIC: a `Status: fixed` differential bug's
  `Cases:` row must PASS in the baseline. BUG-090's pinned row is `strings/trimspace-repeat/repeat-bound-refused`,
  and that row did NOT flip and CANNOT: its `cases.tsv` comment says it is RED BY DESIGN — outputs past the Repeat
  shim's modeled `1<<24` bound refuse by name (`goleanShimStringsRepeatBound`), independent of the machine's
  speed. So the entry's own description of it («a runner-budget red (BUG-073)») was STALE; corrected in place
  with a dated bracket ([AGENT]), the corpus row untouched (`Corpus/**` is a corpus lane's). No `Cases:` row
  flipped anywhere in the gate (DRIFT = the 5a row only), so no ledger line moves.
- Owed to a corpus lane (recorded in the entry and in §6): replace the pin by a performance witness that main's
  binary fails at budget and S3's passes (e.g. the 32k-allocation loop of `alloc_new`: 14 s → 0.8 s), re-size
  `stdlib-source/builder-fuzz` toward the asked 100k, re-run the gotest lane's `fixedbugs/issue24419.go`
  (MACHINE-REFUSED at 30 s before). When that witness row PASSes, `Status: fixed` becomes legal under the rule.
  Alternative named: flip `Status:` now with the red-by-design row left on the `Cases:` line — rejected, the
  check would fail (and rightly: the pin would then pin nothing).

## 6. Owed (carried explicitly)

- The four synchronization applies' split + the pool's select interception, and `applyStrictOp`'s TWO
  allocating conversions `[]byte(s)`/`[]rune(s)` (§4 item 4; audit F3 — `applySlice` allocates nothing): one
  heap copy each per op; not on a benchmark; to the next slice of this
  module (or C4) with the same recipe. `deliverS` (held) then disappears and its docstring's list with it.
- **The header/backing invariant as a STATED invariant** (audit F1, 2026-09-19 [AGENT]): `∀ reachable slice
  header, offset + cap ≤ |backing array|`. It is now written down where the refusal is (`arrayIndexNatFormed`'s
  docstring, Ops.lean: the 11 formation sites that establish it, the normalizer's length-mismatch refusal that
  preserves it, and the plain statement that it is by construction and UNPROVED). Owed: state it as a `StateWf`
  conjunct with `writeAt_noPanic`/`writeAt_noPanic_of_readAt_ok` as its consumer, and derive
  `sliceIndexLoc`/`Mem.storeElems` landing inside the backing from it. That is a SEMANTIC-INVARIANT addition, so
  it is its own gated slice (next slice of this module, or C4) — deliberately NOT done in this records fix round.
- `_hloc` (§4 item 6). Audit F7 adds the follow-up's own scope: the one-line removal of the vacuous hypothesis
  should also drop `c.appendTargetLocal` from `MultiStreams`/any caller that still supplies it (the auditor did
  not chase the callers; the follow-up owes that grep).
- Cost B(c): the enumerator pays its fork copies (its own design; the boundary is stated in §1). Audit F8
  (records): charter §6's S3 row lists «the enumerator's explicit fork copy» as S3 content, which the S3 boundary
  statement (§1 here, and the completion note's B(c) row) SUPERSEDES — exploration's retained states are
  exploration's by design. The charter is ratified text, so the supersession is recorded, not applied:
  **PENDING [USER]** acceptance at the merge ask.

## 7. PENDING [USER]

- Unchanged from S2c: the ratification of BUG-111 fix (i)'s WIDER scope (S2c handoff §6, evidence-backed).
- No new semantic decision: S3 introduces no observable change on any reachable path (the gate at zero drift
  and the byte-identical choice trace are the evidence); the one refusal-CLASS change (§2, unreachable path) is
  disclosed here, as S1's was.

## 8. Where the lane stopped; the next command — the audit ask

**PARKED 2026-09-19 (UTC), branch-complete.** Branch `core/c1-memory-module-s3-0919`, base main **`0f114df6`**
(train r42's close — S2c and BUG-111 are already on main), worktree `.claude/worktrees/c1-s3`, clean at the
records commit that follows the ONE gated runtime commit **`fd99b021`** (§2: gate 2 red only on the 5a pair;
choice trace byte-identical; detector-soundness cell-for-cell). Nothing merged, nothing pushed; main untouched;
the box-wide build lock released. **C1 is complete MODULO the §6 owed list**
(`docs/2026-09-19_c1-memory-module-completion.md`) — audit F6, 2026-09-19 [AGENT]: charter §8's exit-evidence
line «`deliverS`'s saved-store arm gone» is NOT met to the letter (`deliverS` remains at 8 sites with its
saved-store arm — StepFn.lean:587/597/638/711/724/762/800/813 — plus the pool's select interception,
Multi.lean:1571; the audit's §5 establishes all of them are COST-only, no rollback depends on the saved store),
so the earlier heading «C1 COMPLETE against its charter» claimed more than the letter supports. Reading
proposed: the §6 owed list (the 8 cost-only `deliverS` sites and the select interception → C4 or the next
slice; the header/backing invariant → a later slice) IS the charter's closing shape, and C1 closes on it —
**PENDING [USER] ratification at the merge ask**, not self-adjudicated here.
What C1 owes onward is §6. Scratch (gitignored, this worktree only): `.tmp/` (both binaries read-only, the
sorted dumps, the gate logs `ci-1.log`/`ci-2.log`, the bench jsons) and `artifacts/choice-trace-{main,s3}`,
`artifacts/detector-soundness-s3`.

THE NEXT COMMAND is the merge protocol for THIS branch alone (charter steps 3–5a): the audit below; on the
[USER]'s sign-off `git checkout main && git merge --ff-only core/c1-memory-module-s3-0919`; step 5a applies —
the certificate provenance is STALE at this tip (the gate names the changed dependency
`GoLean/GoCore/EnumDedupSound.lean`; the runtime commit touches nine `GoLean/GoCore/` modules), so the train runs `scripts/ci --slow`,
installs the reviewed candidate for `imported-goose/channel/google-search` and re-gates green.

**The pre-merge adversarial audit is ASKED at this park** (charter «the ask is unconditional; scope and waiver
are the user's»). The bar proposed for this slice, [AGENT]:

1. **The seam's soundness claim — «a commit never panics».** Every `*_commit_noPanic` covers its family, but the
   argument rests on `arrayIndexNatFormed` (§2): an out-of-range index AT A STORE is a dangling FORMED address.
   Hunt for a reachable path that forms an address and then shrinks or replaces the array it points into before
   the store (a slice header re-pointed at a shorter backing, `clearSlice`/`copySlice` into a shorter target, a
   map payload rewrite, a spill that moves elements) — that would turn a Go panic into a `.internal` refusal
   (WRONG-VERDICT class). The negative corpus has no row for it because no run reaches it; the auditor should
   try to write one.
2. **The eight W arms' reorder.** Checks moved before writes; the eval tests' 56 label-shape facts and the
   byte-identical choice trace say the corpus sees no order change. Look for an arm whose emitted access ORDER
   (the label) or refusal text differs from main's on a path the corpus does not pin (makeMap/makeChan's hoisted
   `valueAsLoc`; `appendSlice`'s spill after the consult; `copySlice`'s target check).
3. **The driver's pre-step read.** `Thread.afterStepWith (c.boundaryFacts σ) c' = Thread.afterStep σ c c'` is
   `rfl`; confirm no boundary rule ever read the POST-step store (it did not — the facts are `(spawnPlan c).isSome`
   and `c.registryCommits σ`, both over the PRE-step `σ`; `c'` enters only through `completedFlag`), and that
   `stepMulti_sound`'s three simp sites are the only users.
4. **What `deliverS` still holds** (8 sites, docstring): are the 4 read-only sites read-only in fact, and do the
   synchronization applies (`applyChanOp`/`applySyncOp`/`applyAtomicOp`/`applySelect`) and `applyStrictOp`'s three
   [TWO — audit F3] allocating conversions write-then-panic anywhere (a rollback that still depends on the saved store rather than a
   cost)? §6 owes their split; the audit should say whether the OWED is a cost only.
5. **Theorem statements.** No label weakened (no `∃` introduced); the deleted set is exactly `storeMany` and its
   three lemmas (tombstoned); every `.plan`/composed pair keeps the composed name's type. Diff the theorem-name
   sets and the statements of `stepFn_sound`, `step_complete`, `step_complete_any_wf`, the consumption sweeps.
6. **Records honesty.** §3's two ratio steps over the line on AFTER-2 (reported, not re-fitted); §5's `Status:`
   reasoning; the refusal-class change's disclosure (§2, §7); the inventory's 3 moved rows and 2 retired rows.

Scope and waiver are the [USER]'s; the lane does not self-adjudicate the ask.

## 9. Audit fix round (2026-09-19) — F1–F8 dispositions

The pre-merge adversarial audit ran on `review/c1-memory-module-s3-0919` at candidate `ee8d0ef0`
(`docs/2026-09-19_c1-s3-audit.md`, commit `c44a089b`). **VERDICT: FIX-FIRST, records-class and narrow —
MERGE-CLEAN on the semantics, the proofs and the gates**: no WRONG-ANSWER, UNSOUND-PROOF, WEAKENING,
COHERENCE-GAP, FAIL-OPEN or SCOPE finding; the refusal-class change was probed unreachable (15 programs, main =
candidate = gc); the eight reordered W arms observationally silent (28 panic-path programs); the boundary rule's
`rfl` confirmed and 183 concurrency rows enumerated byte-identical on both binaries; the four charter §6 targets
reproduced MET, the two AFTER-2 by-the-letter misses shown to be jitter (0 of 42 ratio samples over the lines in
six further runs); the five records claims reproduced. Authority for the round: [USER] Mike 2026-09-19 «Go ahead
with the audit» (verbatim, relayed by the [AGENT] coordinator); the dispositions below are the coordinator's
([AGENT]) and are disclosed at the merge ask. Two commits: the docstring commit (gated — it touches `GoLean/`)
and this records commit.

| # | class | disposition, landing site |
|---|---|---|
| F1 | RECORDS-CLAIM (argument precision) | **APPLIED (docstring) + OWED (invariant).** `arrayIndexNatFormed`'s docstring (`GoLean/GoCore/Ops.lean`) now STATES the fact the unreachability argument rests on for an element run and for a store through a slice-derived pointer — `∀ reachable slice header, offset + cap ≤ |backing array|` — names the 11 header-formation sites that establish it by construction (`sliceFromSlice` ×2, `sliceFromArray` ×2, `convertValueToTy`'s nil-at-slice-target arm, `defaultValueTy`'s `.slice` arm, `applyStrictOp`'s `.bytesFromString`/`.runesFromString`, `applyStmtOpCore.plan`'s `.makeSlice`, `applyStmtOp.plan`'s in-place-append and spill headers), names what preserves it (an array cell never resizes — the normalizer refuses a length mismatch at the declared `.array n` type, ~Ops.lean:1181; `Store.alloc` normalizes at birth; header-rebasing conversions refused by name; the wire carries slice EXPRESSIONS), and says plainly it is NOT a `StateWf` conjunct and NOT a theorem. Adding the conjunct + the theorem is a SEMANTIC-INVARIANT change and therefore its own gated slice: **OWED**, §6. |
| F2 | RECORDS-CLAIM (three docstrings named theorems that do not exist) | **APPLIED.** `deliverV` (`StepFn.lean`) cited `deliverV_deliver` → now `deliverV_ok`/`deliverV_panic` (StepFn) + `deliverV_ok_inv`, `toResult_plan_ok`/`_panic`, `toResult_plan_inv_ok`/`_inv_panic` (MachineSound). `enterFramePickV` (`Machine.lean`) cited `enterFramePickV_ok`/`_panic`/`_error` → now `enterFramePickV_cases` + `enterFramePick_of_V_ok`/`_of_V_panic` (Machine) and `enterFramePickV_of_ok`/`_of_panic`/`_of_plan_ok`/`_of_plan_panic`/`_of_nopanic` (MachineSound). `spawnStep` (`Multi.lean`) cited `spawnStep_sound` → now `spawnStep_shape` (MultiSound), `spawnStep_wf` (MultiWfSound), the spawn arm of `stepThreadInto_sound`. Each site records that the old name was never declared. Handoff half: §2's coherence paragraph names `deliverV_arm`/`entryV_arm`, `completeV_apply`/`completeV_entry`/`anyV_entry`, `*_inv_ok`/`_inv_panic`, `enterFramePickV_of_ok`/`_of_panic`, `deliverV_panic`, `deliver_panic`, `applyStmtOp_plan_*`, `appendSpill?_of_noSpill` — **each verified present by grep at this tree**; none of the three phantom names occurs anywhere outside the three code sites (`git grep` over `docs/`, `GoLean/`, `scripts/` at the fix-round tree returns only those three). Nothing to change in §2 on that count. |
| F3 | RECORDS-CLAIM («three allocating conversions» — there are two) | **APPLIED, four sites.** `deliverS`'s docstring (`StepFn.lean`), §1's table row and §6 here, the completion note's «Owed onward», and `docs/hygiene-slice-log.md`'s C1 S3 entry now say TWO (`[]byte(s)`, `[]rune(s)`), with the reason: `applySlice` (`Machine.lean`) returns its store UNCHANGED in every arm and refuses a slice expression over a non-addressable array value by name; the only `Store.alloc` calls in `applyStrictOp` are `bytesFromString` and `runesFromString`, which is what `scripts/mem-callsites.tsv` already records (`applyStrictOp alloc 2`). §8's audit-ask text (a historical record of what was asked) keeps its wording with a bracketed `[TWO — audit F3]`. |
| F4 | RECORDS-CLAIM (wording) | **APPLIED.** §2's blanket «Statements unchanged throughout» is replaced by the precise claim: the MERGE-INVARIANT statements are byte-identical to main's (the 15 named, `inductive Step` untouched), and THREE KIT LEMMAS are restated at the plan level with unchanged conclusions — `stepFn_stmtOp_oblivious`, `stepFn_stmtOp_spill` (hypothesis over `applyStmtOp.plan … = r.map (Commit.withStream ch)`) and `stepFn_consumption_some`'s `hloc` → `_hloc`. |
| F5 | RECORDS-CLAIM (provenance) | **APPLIED.** BUG-090's S3 re-measurement paragraph cited the S1-era BEFORE pair (13.8 s, 6.37 s — `BUGS.md`'s S1 paragraph, a different binary on a different day) under the S3 evidence label. It now cites S3's own BEFORE, `alloc_new` 32k **14.12 s** and the (h) phase at 40k **6.83 s**, and names the derivation: `docs/evidence/2026-09-19_c1-memory-module-s3/bench-compare.md` (rows `alloc_new(32000,)` 14.1236 and `heap_then_scalar(40000,20000) − heap_then_scalar(40000,0)` 6.827). The AFTER side, the ratio and the closing claim were already S3's and are unchanged. |
| F6 | RECORDS-CLAIM (letter vs. substance) | **APPLIED as a reworded claim + PENDING [USER].** «C1 COMPLETE against its charter» → «C1 complete modulo the §6 owed list» in the completion note, this handoff §8, `docs/hygiene-slice-log.md` and the master plan's C1 row, each naming what is owed (the 8 cost-only `deliverS` sites + the pool's select interception → C4 or the next slice of this module; the header/backing invariant → a later slice) and why charter §8's «`deliverS`'s saved-store arm gone» is not met to the letter. The reading that the owed list IS the charter's closing shape is **PENDING [USER] ratification at the merge ask** — the lane does not self-adjudicate a ratified charter's exit line. |
| F7 | NIT | **RECORDED** (§6): `_hloc`'s one-line removal follow-up additionally owes a caller grep — dropping `c.appendTargetLocal` from `MultiStreams`/any caller that still supplies it. Not done here (it is a theorem-statement change). |
| F8 | NIT (records) | **RECORDED + PENDING [USER]** (§6): charter §6's S3 row lists «the enumerator's explicit fork copy» as S3 content; the S3 boundary statement (§1 here; the completion note's B(c) row) supersedes it — exploration's retained states are exploration's by design. The charter is ratified text, so the supersession is recorded, not applied. |

**What this round did NOT do** (deliberately, [AGENT]): no semantic change, no theorem added/changed/deleted, no
gate change, no baseline change, no evidence-dir change. The `GoLean/` edits are docstrings and one comment; the
gate-built binary's compiled code is unchanged — `ab355547ff23…` → `a014183b0dfa…` at the same size
(121,383,320 bytes), with `cmp -l` reporting 244 differing bytes ALL inside the binary's embedded source-hash
manifest (exactly the four entries `GoLean/GoCore/{Machine,Multi,Ops,StepFn}.lean`); the docstring text occurs in
neither the generated C nor the binary, and relinking the unchanged object set reproduces `a014183b0dfa…` byte
for byte. The 5a-class `certificate provenance` red is unchanged in kind and in text — it still names
`GoLean/GoCore/EnumDedupSound.lean` as the changed dependency (the runtime commit's); the four docstring-edited
modules are certified inputs too, so the 5a step at the train is owed exactly as the S3 handoff §8 says.

**Gate at the fix-round tree** (captured `EXIT=`; `.tmp/ci-fix.log`, gitignored scratch in this worktree):
`scripts/capped scripts/ci --diff` under the box-wide build lock, tree `f2faca62` (the docstring commit),
16:53:12–17:05:55Z — **EXIT=1, 763 s**, 3686 cases, **DRIFT = exactly the one 5a-class row**
(`imported-goose/channel/google-search` PASS→FAIL/membership, the cached certified row judged STALE by the
provenance change), **red ONLY on the 5a pair** (`certificate provenance`: «STALE certification: changed
dependency build/files/GoLean/GoCore/EnumDedupSound.lean»; `baseline diff` = that row). Everything else `ok`:
core build warning-free; eval tests **267 ok**; memory-module raw call-site inventory **PASS, 70 rows**; core
totality audit PASS (every `GoLean/` module, required core theorems, poison controls); escape-hatch preflight +
addendum ok; spec-anchor citations resolve at the pin; evidence-on-main size gate ok; `AGENTS.md` alias ok;
declaration/wire boundary ok; negative run **394 = baseline**; reconciler 2 findings, 1 HIGH = the 5a item (plus
the standing C13 patch-level-version note). Preceding sequential warms, all EXIT=0: `GoLean.GoCore.Ops`,
`GoLean.GoCore.Machine`, `GoLean.GoCore.StepFn`, `GoLean.GoCore.Multi`, `GoLean`, then `golean` +
`gocore-eval-tests`.
Records checks at the fix-round tree, captured exits: `scripts/check-bugs.sh`, `scripts/check-evidence-size`,
`scripts/check-agents-alias`, `scripts/check-spec-anchors`, `python3 tools/reconcile-records` — see the fix
round's commit message for each exit code and the reconciler's finding set (no NEW finding).
**Disclosure, [AGENT]:** during that run the `GoLean/` tree was committed and clean, but `docs/` carried this
records commit's edits UNCOMMITTED, so the run's own receipts record `git_dirty=true` (the summary's negative
baseline note says so in as many words). The six dirty paths were `docs/2026-09-03_design-hygiene-arc.md`,
`docs/2026-09-05_master-plan.md`, `docs/2026-09-19_c1-memory-module-completion.md`, this handoff,
`docs/BUGS.md`, `docs/hygiene-slice-log.md` — no runtime, no corpus, no baseline, no apparatus file. A
CONFIRMATION re-run of the same command at the CLEAN records tip (this commit's tree) is reported in that
commit's message; its result is the gate line of record for the branch tip.
