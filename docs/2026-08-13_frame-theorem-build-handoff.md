# Frame-theorem proof session — build handoff (2026-08-13)

Status: slice 2b parts 2–4 SESSION RECORD. The contract is
`docs/2026-08-13_executable-frame-theorem.md`; this note records exactly
what is PROVEN AND COMMITTED, what sits sorried in the working tree,
and the recipes for the remainder. Nothing here weakens the contract;
three findings STRENGTHEN it (§3).

## §1 Committed and green (the helper-commutation tower, §5 steps 1–2 —
COMPLETE)

All under `proofs/GoLeanProofs/Frame/`, imported by the GoLeanProofs
root (so `scripts/ci`'s proofs build + Audit sweep cover them); every
module sorry-free, `partial`-free, axiom footprint the classical trio
or below:

- `Rename.lean` — renaming over every carrier (Loc/GoValue/cells/env/
  Expr/Stmt/TargetRef/EvClause/Cont/Config), `ShiftSpec` (injective +
  fresh-region shift law), `uniformShift` instance, injectivity/BEq
  transport.
- `Sim.lean` — `ExSim` (the ok/panic-transfer relation; canonical left,
  framed right), `FrameSim` (the design's SimState: equal static
  tables, allocator through ρ, pointwise `lookup_img` heap
  characterization, `frame_pres`, the constant `fr_avoid` clause,
  `bodies_inv`), `setBase`/`alloc_fst`/`alloc_snd` combinators.
- `TypeCongr.lean` — every static-table reader computes identically.
- `Values.lean` — valueAs*, shape inversions, loc-free rename identity,
  coerceStoredValue, normalizeValueForTy, isNormalForTy invariance,
  defaultValue congruence+inertness, convertValueToTy.
- `Compare.lean` — eqb/valueEq/ordering/int-op/hashability/
  mapEntryIndex? (worker-built; all statements as specified).
- `NoPanic.lean` — panic-freedom of the pure walks + `exSim_of_ren`.
- `Plans.lean`, `ContOps.lean` — plan classifiers and continuation
  walks commute (workers; all statements as specified).
- `HeapOps.lean` — forIn_sim (generic two-run loop simulation),
  StructFields ops, array get/set, **loadLoc_sim/storeLoc_sim**, cell
  readers, loadMany/storeMany/bindParams/allocDecls/pinResultLocs,
  dynamicDispatch?_sim(+'), **enterFrame_sim** (now also delivering
  ρ-invariance of the entered body via `findFunctionIn?_mem` +
  `bodies_inv` — the frame-entry arms' key fact).
- `MachineRel.lean` — CfgSim/ListSim vocabulary.
- `Builders.lean` — slice-shape ops, literal builders, append backing,
  typeAssertValue, assert-panic-message invariance (worker).
- `PanicFrame.lean` — renderPanicPayload/Head invariance (the
  `.panicked` terminal arm), map-range snapshot machinery
  (isNormalForTy-invariance of the snapshot check), bindIterVars_sim,
  enterFrameStep_sim/enterFrameDeferPanicking_sim, `TripSim`.
- `ChanSync.lean` — applyChanOp/applySyncOp/select
  readiness+commit+apply, enterRecvTargets (worker; all nine as
  specified).
- `StmtOps.lean` — mapAssignValue + every applyStmtOpCore arm
  (including the clearSlice/sortSlice/copySlice loop simulations) +
  builder panic-freedom (worker).
- `StrictOps.lean` — sliceVisibleValues, mapLookupValue,
  indexTargetLoc, applySlice, and the full ~45-arm applyStrictOp
  simulation (worker).

Per-arm panic-message audit (design §3.5) came back CLEAN across all
five op sweeps: no success-reachable panic message embeds a value
`repr`; value reprs appear only in `stuck`/`unsupported` messages,
which the success-only simulation never transfers.

## §2 Working tree, NOT committed (sorry-bearing; the remainder)

- `StepSim.lean` — `stepFn_sim` (the arm induction). The fun_cases
  sweep is ~200 arms; the tier automation + explicit blocks close all
  but 22. Sorried arms and their recipes:
  * 79/80/84/85 (strict nullary + apply): exactly the chan-apply
    recipe already in the file (cases 120/121) with
    `applyStrictOp_sim`; the `(v :: done).reverse` alignment via
    `renameValueList_reverse` backwards.
  * 64/98/99 (applyStmtOp with choices) + 134/135 (applyRhsOp) +
    166/167 (storeK stores via storeTarget/resolveChain): need a small
    `Ops2` module (~150 lines): `resolveChain_sim` (structural on
    steps; indexTargetLoc_sim + valueAsLoc_sim), `storeTarget_sim`
    (resolveChain + storeLoc_sim / mapAssignValue_sim),
    `applyRhsOp_sim` (vals: rfl; mapLookup: mapLookupValue_sim;
    typeAssert: typeAssertValue_ren), `applyStmtOp_sim` (core sim +
    the appendSlice arm: sliceVisibleValues_sim +
    buildAppendBackingValue_ren; widths equal because cap/len rename
    away, so the SAME choice is consumed — the streams stay equal).
  * 41/60 (chanRecv/syncStmt entries — NAMED match scrutinees
    `_hplan`): `split` on the framed match, refute the impossible arms
    against `chanPlan_ren`/`syncPlan_ren` + the canonical plan fact,
    close the real arm by injection + `ren_simp` (the mapIter case165
    block in the file is the worked template for named-scrutinee
    arms).
  * 56 (assignMany entry): ren_simp_all nearly closes; residue is the
    size-guard normalization (lengths of renamed arrays) — the macro
    sets already carry the length lemmas; align the `if` with
    `simp only [if_neg/if_pos h]` (both runs share the condition).
  * 63/78 (wide-stmt/strict-expr entry, catch-all scrutinee): `cases
    ‹Stmt›` (63; the only Stmt hypothesis) / `rename_i`-bound `e`
    (78), then per-ctor: excluded ctors die by `simp [stmtPlan] at
    hplan` (the plan fact is `none` there — no need to touch the
    fun_cases negation hypotheses); genuine ctors compute both plans
    with `simp_all only [stmtPlan]` after `ren_simp_only` and close
    with `ren_simp_all`. (A first attempt hit a heartbeat timeout —
    split the 30-way cases into named-ctor groups, or
    `set_option maxHeartbeats` higher for just this theorem.)
  * 94/96/97 (stmtOpK check/shift): `rw [if_pos hlt,
    valueAsLoc_panic_ren/valueAsLoc_ren]`-recipe; drafted blocks are in
    the session transcript; binder names via `rename_i` need one
    error-round to pin.
  * 129/131/132 (tgtOpK completes): completeTargetRef_ren after
    folding `(renameValue v :: renameValueList ops)` and reversing —
    same fold trick as the chan-apply blocks.
- `Transfer.lean` — COMPLETE proofs (no own sorries; compiles against
  the sorried StepSim): `stepFnIter_sim`, **`execStmtLoop_ren`**
  (success-run transfer at the driver: same fuel, same stream, same
  outcome tag, FrameSim-related terminals), **`completesIn_ren`**
  (completion transfer). Commits with StepSim once that is sorry-free.

## §3 Findings (contract deltas, all strengthenings — record for the
audit)

1. **ρ generalized beyond the uniform shift** (`ShiftSpec`): any
   injection satisfying the fresh-region shift law `ρ (na₀+k) = na+k`.
   The design's shift is the canonical instance (`uniformShift_spec`).
   Every lemma uses only injectivity + the shift law (allocation).
   Payoff: input-RELOCATING renamings — reverse/binsearch/sort's
   ∀-placement (`base`) quantifier can transfer from a canonical
   placement instead of forcing base-symbolic termination segments.
2. **`Expr.locLit` needs NO side condition**: renaming the SYNTAX
   (renameExpr/renameStmt) closes the design's per-arm exclusion; the
   seed discharges program-invariance once (`bodies_inv`, from locSup
   bounds — globals below `na₀` under the low-identity shift).
3. **MachineWf is NOT threaded through the induction.** The design
   said "MachineWf threaded (the wf-sweep pattern)"; the proof needs
   only `FrameSim`'s own clauses: the two-sided pointwise
   `lookup_img` + the CONSTANT `fr_avoid` (fr owns no `.base` cell
   anywhere in ρ's image — seed-dischargeable from MachineWf-of-the-
   framed-seed + input disjointness + a TIGHT canonical seed, i.e.
   every address below `na₀` is an input cell) make even the
   storeLoc-at-absent-cell arm commute. MachineWf enters only at seed
   establishment. Consequence for consumption: the canonical seed must
   be tight — fib's is (dom = {0}, na₀ = 1).
4. `renameValue` does not whnf on constructors (nested-mutual
   compilation) — `simp [renameValue]`-equations always, never `rfl`
   through it. Recorded in every worker report; bit repeatedly.

## §4 Consumption plan (unchanged from the contract, not started)

`fib_total_framed` = `fib_total`'s CompletesIn + `completesIn_ren` +
seed FrameSim at (ρ := uniformShift 1 na, fr, na) — obligations were
walked concretely this session: lookup_img at the two-cell seed,
fr_avoid from `hfr` + `Heap.lookup_key_locSup`, bodies_inv from
`funcListSup fibLowered.funcs` (decide) + a rename-identity-below-na₀
lemma (locSup family mirror — NOT yet written; ~80 lines). Readout +
frame clauses come from the terminal FrameSim (`lookup_img` at base 0,
`frame_pres` verbatim). Then §9e reverse (slice-index WP laws still to
build) and 2c scale-out.

## §5 Session accounting

Six commits on `foundation-s1` (57bcf304..a01dfb2f), ~9.3k lines of
new Lean, all green in `scripts/ci`'s proofs build. Five Fable workers
delegated (Plans/ContOps/Compare/Builders/ChanSync/StmtOps/StrictOps —
all delivered their statements exactly as specified; their per-file
reports are summarized in the module docstrings and §3.4). StepSim +
Transfer live only in the worktree pending the 22 arms above.
