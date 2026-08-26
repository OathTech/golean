# Campaign Arc 4 log — the interpreter⇄invariant seam

Branch `campaign-arc4`, worktree `.claude/worktrees/campaign-arc4`,
opened from the campaign branch @ 03a91c2d (Arc-3 units 1–3
integrated). Governing: `docs/2026-08-21_raft-proof-constitution.md`
(§3 inviolables, §4.1 surgery threshold, §5 latitude);
design of record: `docs/2026-08-22_campaign-arc4-seam-design.md`
(three layers; OQ-A..OQ-D are this unit's to answer from contact).
One writer: this lane's worker. Unit in flight: **A4-U1, the pilot**
— `absState` v1 + the smallest handler interpreter-run equation +
the GO/NO-GO verdict (`docs/2026-08-22_campaign-arc4-pilot-verdict.md`).

Conventions: `[AGENT]` = judgment call under §5 latitude, logged not
pre-approved; checkpoints every ≤5 slices, numbers recomputed; kit
gaps that are GENERAL (≥2 plausible future consumers) go on the
PROMOTION LEDGER section below, target-specific ones stay local.

## Entries

- 2026-08-22 Lane verified: tip 03a91c2d, clean tree, branch
  `campaign-arc4`. Required reading done in order (constitution §3,
  seam design, Arc-1 statement design + TwinProgram/RaftAgreement,
  Arc-3 invariant index + RefinedProofStructure handlers, kit guide).
  Fresh worktree had no build; capped core `lake build`
  (GOLEAN_MEM_MAX=24G) started before instrumentation.
- 2026-08-22 [AGENT] Handler choice contact datum: the charter's
  candidate `advanceCurrentTerm` DOES NOT EXIST in the lowered
  subject — it is Verdi-side vocabulary (VerdiCompat/Raft.lean:135);
  the wire (`baselines/golden/twin-chdriver.wire.json`) has
  `raft.raft.becomeFollower` and no advanceCurrentTerm (grep over the
  9.3 MB wire: the only matches are becomeFollower). **The pilot
  handler is `becomeFollower`.**
- 2026-08-22 Static contact (wire walk, python, pre-Lean): the
  DYNAMIC call closure of the lowered `raft.raft.becomeFollower` is
  10 functions: itself → {raft.raft.reset, raft.Logger.Infof
  (interface dispatch → the harness logger's EMPTY body),
  raft.traceBecomeFollower (empty)}; reset → {raft.newReadOnly,
  raft.raft.abortLeaderTransfer,
  raft.raft.resetRandomizedElectionTimeout → raft.lockedRand.Intn,
  tracker.ProgressTracker.ResetVotes, tracker.ProgressTracker.Visit}
  + the lifted closure `raft.raft.reset$lit0` (via Visit's
  call-value) → {tracker.NewInflights, raft.raftLog.lastIndex}.
  Choice-consuming constructs INSIDE the handler: `lockedRand.Intn`
  (D-11 delta: builds an n-entry map, one `range` pick, break — ONE
  mapIter choice at n = electionTimeout = 10) and `Visit`'s `range`
  over `trk.Progress` (3 entries at n=3 — mapIter choices), then
  `sort-slice` canonicalizes order. So OQ-C's expected answer
  ("none") is ALREADY REFUTED at the smallest handler: handler
  equations must quantify over a consumed choice prefix; the
  post-state is choice-independent (sort + first-key-only uses).
  `stepFollower`/`tickElection` appear as `func-value` stores
  (assigned, not called). Mutex Lock/Unlock lower as `sync-op`.
- 2026-08-22 Dynamic contact (probe `artifacts/probe/Arc4Probe.lean`,
  compiled interpreter over the pinned wire, ch = zeros; output
  `artifacts/probe/probe2.out`): first `becomeFollower` entry (from
  `newRaft`, node 1) at subject step 21,757; the call runs
  **3,233 machine steps**, consumes **4 choices** (1 Intn pick +
  3 Visit range picks over trk.Progress), allocates **164 fresh
  cells** (locals/temporaries/param cells — nextAddr 1442→1606), and
  its persistent footprint beyond the fresh region is 5 cells:
  raft cell (base 389: .trk.Votes fresh handle, .readOnly fresh ptr,
  .randomizedElectionTimeout, .tick/.step funcVals; Term/Vote/lead/
  state unchanged at this t=Term call), MemoryStorage cell
  (.callStats — the subject's instrumented call counters increment on
  lastIndex, a REAL persistent side effect of a "read"), and the
  three tracker.Progress cells (Next/Match/RecentActive/Inflights).
  Mutex lock/unlock pairs leave NO net syncData change. Heap shape
  for absState: one raft node = ONE `.struct raft.raft` cell (~33
  named fields); scalars (Term/Vote/lead/state uint64) direct;
  raftLog behind a pointer (committed/applied/applying scalars on
  that cell; entries deeper behind unstable/storage + interface).
- 2026-08-22 [AGENT] Contact verdict on the seam design's cost
  assumption: "few-line bodies" is FALSE at machine level for
  becomeFollower — the 8-statement body drags reset → {Intn's
  10-iteration map build + mutex, tracker.Visit's choice-driven
  range + sort-slice + 3 closure calls each doing
  raftLog.lastIndex → interface dispatch → MemoryStorage + mutex},
  plus logger interface dispatch. Pilot plan adjusted WITHIN the
  charter: absState v1 + the equation built bottom-up as per-callee
  run equations (the composition shape (B) prescribes anyway),
  starting from the leaf `abortLeaderTransfer` to validate the
  equation FORM end-to-end and measure per-ingredient proof cost;
  full becomeFollower composition attempted only if measured leaf
  costs make it feasible in-unit; otherwise the pilot ends at the
  honest gap + NO-GO verdict with the measured numbers (exactly the
  seam design's "anything else → re-design here" branch).
- 2026-08-22 Slice 1 (85acbb0c): `proofs/GoLeanProofs/Specs/Raft/AbsState.lean`
  (absRaftNode v1 Option reader, gaps GAP-V1-1..5 numbered in the
  docstring; specBecomeFollower re-grounded) +
  `proofs/GoLeanProofs/Specs/Raft/HandlerEq.lean` (`storeTarget_field` —
  the struct-field store form the kit lacks, closed locally;
  `alt_call_span` — the 15-step span equation for the leaf callee
  `abortLeaderTransfer`, abstract σ, symbolic addresses/fields, ten
  windows chained with `stepFnIter_chain`). [AGENT] Spec-side call:
  `specBecomeFollower` is a RE-GROUNDED mirror citing
  VerdiCompat/Raft.lean + Raft.v + the subject — NOT an import of
  compat/verdi (constitution §5 Plan A: compat/verdi is a read-only
  reference, never an import; the two-line correspondence to
  `advanceCurrentTerm` + Follower/lead override is stated in the
  docstring with its `st.term ≤ t` side condition).
- 2026-08-22 Slice 2: `BecomeFollowerWitness.lean` — the §3.3
  discharge witness: every `alt_call_span` premise proved on a
  concrete state over the PINNED tables (twinLowered's
  funcs/methods/types; raft cell = the machine's own defaultValue at
  raft.raft with raftLog pointed at a default raftLog cell), plus
  `alt_witness_projection` (absRaftNode preserved across the call
  and = some ⟨0,0,0,0,0,0⟩ — live, not vacuous). All rfl discharges
  #eval-checked first (WitnessProbe). [AGENT] GAP-U1-W1: the witness
  state is well-formed-by-construction, NOT proved reachable — a
  reachable-state witness needs Arc-2's checkpoint reflection (raw
  kernel evaluation to the first call site @ ~22k steps is measured
  infeasible, Arc-2 route study); recorded, not claimed. Modules
  wired into the GoLeanProofs aggregator; full proofs+Audit build
  green (469 jobs). `#print axioms`: storeTarget_field /
  alt_call_span / alt_call_span_witness all
  [propext, Classical.choice, Quot.sound]; alt_witness_projection
  [propext].

- 2026-08-22 Slice 3: **the gate caught a layering violation** —
  `scripts/ci`'s import-direction lint: general-layer proof modules
  (outside `Specs/`) may not import `GoLeanProofs.Specs.*`, and the
  witness (then at `proofs/GoLeanProofs/Raft/`) imports the
  `Specs.TwinProgram` pin. The modules are TARGET-layer
  infrastructure anyway (they name `raft.raft`), so the fix is the
  lint's own first remedy: all three moved to
  `proofs/GoLeanProofs/Specs/Raft/` (aggregator + doc paths updated;
  slice-1/2 entries above rewritten to the final paths — the
  original path `GoLeanProofs/Raft/` existed only at 85acbb0c..).
  This ALSO corrects the seam design's "never imported by statement
  modules" layering to the repo's mechanized form: the general/target
  split is the enforced boundary; statement modules simply do not
  import the seam modules (checked by reading; no lint needed).
- 2026-08-22 Writer note: commit 2c396efe (coordinator's
  campaign-level log entry, `docs/raft-campaign-log.md` only — Arc 3
  unit 4 record) landed on this branch between my slices 1 and 2.
  File-disjoint from this unit's tree; recorded per the one-writer
  discipline, no action needed.

### PROMOTION LEDGER (kit gaps with ≥2 plausible future consumers)

- `storeTarget_field` (HandlerEq.lean) — struct-field store through a
  pointer anchor; every handler field write hits it. Lift to StepKit
  on the second consumer (kit rule: 2 landed consumers, retrofit in
  the lifting commit).
- Normality preservation under `StructFields.set` (isNormalForTy of a
  struct survives setting a field to a normal value) — needed to turn
  per-store `hnorm` hypotheses into derived facts in ∀-state
  equations; `isNormalForTyFuel_sound` is the existing half.
- Closure CALL-VALUE frame entry (`callValArgsK` analogue of
  `stepFn_call_enter`) — tracker.Visit's per-node closure calls;
  any Go program calling a func value needs it. (OQ-B's one gap.)
- `sync-op` step forms (sequential Lock/Unlock crossing) — every
  mutex-guarded subject path (lockedRand, MemoryStorage).
- `sort-slice` stmtOp form (applyStmtOp sortSlice fact) —
  tracker.Visit and quorum CommittedIndex both sort.

## Final entry — A4-U1 complete (2026-08-22, tip = this commit)

**CHECKPOINT (recomputed at this tip, 4 slices):** commits 85acbb0c,
0834aa45, 64c0927d + this one; unit-end gate
`GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` — **RESULT:
PASS, exit 0** (log `artifacts/ci-arc4-u1b.log`, gitignored; 23 ok
steps; the two no-diff notes are the sanctioned fresh-lane hatch —
this unit touched `proofs/GoLeanProofs/**` + docs only, no runtime
code, no Corpus/, no baselines/). An earlier gate run FAILED on the
import-direction lint and was fixed by the slice-3 move — the gate
working, recorded, not laundered. Fresh `#print axioms` at this tip
(capped `lake env lean` probe):

```
'GoLean.RaftSeam.storeTarget_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoLean.RaftSeam.alt_call_span' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoLean.RaftSeam.alt_call_span_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoLean.RaftSeam.alt_witness_projection' depends on axioms: [propext]
```

`grep -c "sorry\|native_decide"` over the three Specs/Raft modules:
0/0/0. Module line counts (`wc -l`): AbsState 143, HandlerEq 203,
BecomeFollowerWitness 138.

**Deliverable state vs the dispatch:**
1. `absState` v1 — DELIVERED (`Specs/Raft/AbsState.lean`,
   gaps GAP-V1-1..5 numbered; OQ-A answered in its docstring).
2. The pilot equation — PARTIALLY delivered, honestly gapped:
   the equation FORM proved end-to-end at the smallest callee
   (`alt_call_span` + pinned witness + projection readout); the full
   `becomeFollower` equation is GAP-U1-E1 (verdict §2), NOT counted.
3. THE VERDICT — DELIVERED
   (`docs/2026-08-22_campaign-arc4-pilot-verdict.md`): architecture
   GO / hand-walk cost NO-GO, with the measured table (3,233 steps,
   4 choices, per-callee breakdown), the five missing kit ingredient
   classes, OQ-A..D answers, and re-design recommendations
   (Sym-fragment extension primary; W7 SpecTec convergent; kit lifts
   regardless). **Per the seam design §4: re-design at U1 before any
   A4-U2 dispatch — do not send more hand-walk units.**

**Open gaps carried (none counted):** GAP-V1-1..5 (projection),
GAP-U1-W1 (witness reachability — closes with Arc-2 checkpoint
reflection), GAP-U1-E1 (the full becomeFollower equation — closes
with the re-designed generator).

Nothing merged; branch-complete. Merge/audit-ask are the operator's
(constitution §4.1); the ci comparator-landmark staleness note (49
commits at the first run) is flagged for the operator's merge step,
same as the Arc-3 lanes.

## A4-U2 — the handler-fragment Sym extension (2026-08-22, coordinator-accepted; pilot verdict accepted, seam §4b amended)

- 2026-08-22 Orientation: Sym read at this tip (Domain/Mirror/Drift/
  DriftOps/DriftApply/Walk/Refine, 8,193 lines), quit catalog + the
  refinement template + the machine normalizer. KEY contact facts:
  (a) the mirror already carries the FULL grammar — the five classes
  are QUIT-SITE lifts, not domain work; (b) struct-store quits are
  exactly `normalizeValueForTyFuel'`'s `.defined` arm (Q4), whose
  docstring already names the OQ6 conditioned-facts lever this
  design implements; (c) sortSlice ALREADY proceeds at concrete
  elements — class 4 needs nothing for the census path; (d) the
  channel-logic salvage check is NEGATIVE (its DM layers are
  channel-op WP, pre-sync-machinery; zero SyncOp forms in its
  proofs/ — grep over the branch, read-only) — nothing taken.
- 2026-08-22 [AGENT] Design note
  `docs/2026-08-22_campaign-arc4-sym-extension-design.md`: per-class
  representation/refinement-shape/cost, the §4 choice-point story
  (Q3 stays a window boundary; conservation-invariant composition;
  latitude-bearing fields stay unprojected — pick-threading REJECTED
  with the per-order-explosion argument), the address-concreteness
  caveat (§5), slice ladder + kill-points (§6).
- 2026-08-22 [AGENT] Slice-1 class choice: class 1 (struct-store
  normalization via the T-table input) — it is what unblocks the
  pilot leaf's store window (the dispatch's re-measure target); the
  pilot-ledger "normality preservation" PLAIN-KIT row is parked as
  unnecessary-for-transport (design §2 routing note), not built.
  Additivity plan logged (design §0): trailing default-[] params;
  new-named T-core for the fueled normalizer with the old name as
  its []-instance; shipped Sym statements preserved verbatim.
- 2026-08-22 [AGENT] Slice-1 implementation call, STRONGER than the
  design's additivity plan: instead of threading `T` through the
  existing chain, the extension is ONE new module
  (`Sym/TableExt.lean`) layering a DELEGATING step `stepFnT` over the
  untouched `stepFn'` — one overridden arm (storeK → `storeTargetT` →
  `storeLocT` → `normalizeValueForTyFuelT` with the machine's
  `.defined`/struct arms mirrored), everything else delegated; its
  soundness delegates non-store arms to the SHIPPED `stepFn'_conc`.
  Zero edits to the 8,193 existing Sym lines; conditioned premise =
  `SubTable T σ.types` (sub-table, not equality — windows transport
  into any types-extending state; `SubTable.nil` makes the shipped
  theorems the degenerate instance). Structure debt acknowledged: a
  second delegating class would stack overrides — flagged for the
  class-2 slice to decide delegation-vs-refactor there, not silently.
- 2026-08-22 Slice 4 (A4-U2 slice 1) LANDED: `Sym/TableExt.lean`
  (652 lines, 2.4 s) — SubTable, the T-normalizer with defined/struct
  arms, storeLocT/storeTargetT, stepFnT/symEvalWindowT, the conc
  chain (normalizeFieldsWith_conc / normalizeFuelT_conc /
  storeLocT_conc / storeTargetT_conc / stepFnT_conc) and
  **symEvalWindowT_refines/'** (the shipped template + the one
  premise). Plus `Specs/Raft/HandlerEqSym.lean` (157 lines, 7.3 s):
  the RE-MEASURE — the pilot leaf's 14-step body span as ONE
  transported window at the pinned type table, value-symbolic (five
  SymInt vars) address-concrete, ∀ρ ∀σ-extending-the-pin ∀ch; with
  the §3.3 witness at a concrete valuation and projection readouts
  (post = pre = some ⟨7,3,2,1,0,0⟩). Before/after: ~105 span-proof
  lines + 4 conditioned facts → 3-line window rfl + 6-line
  refinement application (fixture ~55 lines, embedding reusable).
  Gotchas measured and recorded in the design note §2: the kit-guide
  §5 smartUnfolding REVERSAL reproduced (DNF ↔ 7.3 s); γ-image
  projection equalities need `decide +kernel` (elaborator whnf and
  plain `decide` both fail) — every `decide +kernel` #eval-checked
  first (SymWindowProbe: window n=14, quit only at the terminal;
  both projections computed true). Kill-points (design §6): NONE hit
  — no shipped Sym statement changed. Full proofs+Audit build green
  (471 jobs); zero sorry/native_decide in both new files (grep).
  `#print axioms` (fresh probe): symEvalWindowT_refines/' and
  stepFnT_conc/storeLocT_conc [propext, Classical.choice,
  Quot.sound]; normalizeFuelT_conc, alt_sym_window_n,
  alt_sym_projection [propext, Quot.sound]; alt_call_span_sym +
  witness [propext, Classical.choice, Quot.sound].

## A4-U2 slice-1 exit (2026-08-22, tip = this commit)

**CHECKPOINT (recomputed; corrected in the follow-up commit — the
first count missed two coordinator commits, the drift-prone layer
doing exactly what the rules warn):** lane commits since 03a91c2d:
13 by `git log --oneline 03a91c2d..HEAD | wc -l` — 8 of this
worker's (85acbb0c, 0834aa45, 64c0927d, 21f0cd51, 09c3f703,
39f87f88, e86bdf34, 16d8d426) + 5 coordinator campaign-log/design
commits interleaved (1508ce9c, 2c396efe, d042d249, fa0a34e0,
e37c4267 — all file-disjoint from this unit's tree). Unit-end gate
`GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` — **RESULT:
PASS, exit 0** (23 ok steps, `artifacts/ci-arc4-u2.log`; no-diff
notes = the sanctioned hatch, proofs+docs only; the gate ran at the
full working tree — an aggregator-file commit followed, content
identical). Slip recorded: 39f87f88's pathspec missed the sibling
`proofs/GoLeanProofs.lean`; appended in the next commit, tree
unchanged.

**A4-U2 state:** design note delivered (five classes vs the quit
catalog, choice-point story §4, address caveat §5, slice ladder §6;
channel-logic salvage check NEGATIVE, nothing taken); slice 1 (class
1) DONE with refinement theorems, witness, and the measured
re-measure. Remaining per §6: slice 2 sync-ops, slice 3 call entry
(+ the delegation-vs-refactor decision), slice 4 class-5 kit half +
first choice-crossing composition. Nothing merged; branch-complete
for this dispatch; merge/audit-ask remain the operator's.

## A4-U2 slices 2+3 (2026-08-23, coordinator-dispatched)

- 2026-08-23 [AGENT] Slice-2 census CORRECTION to the dispatch: the
  handler fragment consumes exactly `SyncStmtOp.lock`/`unlock` on
  plain `sync.Mutex` (10 opDones = 5 pairs in the pilot trace:
  lockedRand ×1, MemoryStorage ×4 via lastIndex) — **no Once** on the
  path (the coordinator's guess, checked and not found); the deferred
  Unlock's DISCHARGE at frame exit is a deferred CALL — class 2's
  drain arms, not a sync op. Covered: lock/unlock apply + the
  `.opDone` sequential strip; the rest of the family stays Q7.
- 2026-08-23 Slice 2 (bedc4756): sync arms in the delegating step +
  `applySyncOp_conc` + an in-module lock/unlock window witness
  (`syncWit_refines`, #eval-checked 12 steps first) + the OWED
  Audit/Kit pins for the extension's public surface (slice-1 debt
  noticed and paid: the kit-pin convention covers Sym additions).
- 2026-08-23 [AGENT] Slice-2 fix during slice 3 (contact-driven): the
  sync apply's flag store initially used the UNTABLED `storeLoc'` —
  correct for a standalone mutex cell (the witness) but the twin's
  mutexes live INSIDE structs (lockedRand.mu), where the write-back
  re-normalizes the whole struct at its defined type → Q4. `T`
  threaded through `applySyncOp'`/its conc lemma; caught by the
  becomeFollower window probe quitting at step 102.
- 2026-08-23 Slice 3: call entry, the one-lever design — `SymTables`
  pack + `Agrees` (table EQUALITY, not sub-table: alias-resolution
  walks return partial answers on a miss, so a sub-table miss is
  indistinguishable from genuine absence; recorded in the module),
  table-only congruence lemmas (resolveDefinedAliasesFuel /
  methodInfoByFuncId? / methodRecvInterfaceName?), `bindParamsT`,
  `enterFrameT` (the machine's OWN table helpers run at `TB.toState`
  — zero re-implementation of the dispatch walks), and the layered
  `stepFnTB` covering: callArgsK completion, callValArgsK completion
  (closures), and BOTH defer-drain frame arms; `symEvalWindowTB` +
  the pack-conditioned refinement pair. [AGENT] The deferred
  delegation-vs-refactor decision, DECIDED: delegation again, layered
  (stepFnTB → stepFnT → stepFn'; override sets are disjoint config
  shapes, so layers never interleave; shipped statements + slice-1's
  weaker SubTable-only premise for store-only windows both survive
  verbatim). [AGENT] Scope kill-point exercised: INTERFACE-receiver
  dispatch (class 2b) is OUT — the census path's single interface
  call is the harness logger's empty `Infof` (14 steps), and the
  dispatch-walk congruence (`canonicalTy` + the method-set fold) is
  where the cost lives; `dynamicDispatchT` quits Q4 on interface
  receivers, one window split per logging handler, recorded residual.
- 2026-08-23 **THE RE-MEASURE** (`HandlerEqSym.lean` §slice-3): the
  becomeFollower run from its call configuration transports as ONE
  window of **189 steps** (`bf_window_n`/`bf_prefix_span` + witness;
  #eval-checked first: 189, quit q4Program): frame entry → funcVal +
  field stores → reset entry → branch → four stores → RRT + Intn
  entries → mutex lock + marker strip → map-build prologue, quitting
  at Intn's `struct{}{}` literal (`buildStructValue` at a defined
  type — the Q4-normalize family's next member, SAME lever, recorded
  residual; the map-range pick two constructs later is the designed
  Q3 boundary regardless). Elaboration: the 189-step window rfl = 51 s
  module build. Numbers: TableExt now 1,303 lines (all three
  classes + witnesses + pins), HandlerEqSym 235; zero
  sorry/native_decide (grep); full proofs+Audit green (471 jobs);
  fresh `#print axioms`: bf_prefix_span/witness + stepFnTB_conc +
  symEvalWindowTB_refines' [propext, Classical.choice, Quot.sound];
  enterFrameT_conc + bf_window_n [propext, Quot.sound].

### Updated per-handler cost projection (vs the gallery bar)

Derivation: the pilot measured ~9 hand lines/step; the extension
makes straight-line segments a fixture + one `rfl` + one refinement
application (~15–30 lines per WINDOW, step-count-independent).
Windows per handler = choice points + symbolic branches + residual
consults + 1. becomeFollower: 4 choice points (1 jitter + 3 Visit
picks, sort-canonicalized per design §4(ii)) + ~4 branch/residual
splits ≈ 8–10 windows ≈ 200–300 fixture/window lines + composition
glue (pick lemma + conservation, est. 50–150 lines per choice point,
built ONCE in slice 4) + the absState projection argument
(~100 lines) → **≈ 600–1,000 lines for the full becomeFollower
equation vs the pilot's 3,000–6,000 hand projection — inside the
gallery bar (fib = 1,890)**. Elaboration cost scales ~linearly
(51 s / 189 steps with 4 table scans); `decide +kernel` is the
measured fallback. Residual Q4-family members (structLit /
defaultValue / convert at defined types) are each the same
conditioned-table lever, consumed on demand guided by window quits —
exactly how the slice-2 storeLoc fix was found.

### RECOMMENDATION (posted per the dispatch)

**Slice 4 BEFORE A4-U3.** A real handler equation (U3) needs exactly
two missing pieces to compose its windows: the choice-crossing
composition (Q3: the value-generic pick step + the §4(ii)
conservation pattern, smallest instance = Intn's single pick) and
the structLit-at-defined residual (mechanical, same lever). U3
attempted first would stall on both; slice 4 builds the composition
pattern once at the smallest instance, and U3 then becomes assembly
(becomeFollower end-to-end, projected inside the bar above).

## A4-U2 slices-2+3 exit (2026-08-23, tip = this commit)

**CHECKPOINT (recomputed):** slices-2+3 commits: bedc4756, 9719786f
(+ this log commit). Unit gate `GOLEAN_ALLOW_NO_DIFF=1
GOLEAN_MEM_MAX=24G scripts/ci` at 9719786f's tree — **RESULT: PASS,
exit 0** (23 ok steps, `artifacts/ci-arc4-u2b.log`; no-diff notes =
the sanctioned proofs+docs hatch). Zero sorry/native_decide in both
extension modules (grep); full proofs+Audit 471 jobs green; Kit pins
green (13 extension pins total). Branch-complete for this dispatch;
nothing merged; the comparator-landmark staleness note stays flagged
for the operator's merge step.

## A4-U2 slice 4 (2026-08-23, coordinator-dispatched; recommendation adopted)

- 2026-08-23 Slice 4 landed IN TWO PARTS, stop-rule honored at a
  clean boundary:
  **(a) The residual Q4-family lifts the crossing needed** (same
  lever, consumed on demand exactly as designed): `buildStructValueT`
  (+ fields walk, conc lemmas) and `mapAssignValueT` (defined
  key/value types), each with a delegating step arm — the
  becomeFollower pre-window grew 189 → **642 steps, quitting exactly
  at the Q3 pick** (#eval: 642, q3Choice — the designed boundary).
  **(b) THE CHOICE-CROSSING COMPOSITION** (design §4(ii) realized):
  `stepFn_pick_generic` — the TYPE-GENERIC map-range pick step
  (class-5's kit half delivered; `MapMem.stepFn_pick_bind` stays the
  uint64 instance) — and `stepFnIter_window_pick_window`, THE HANDLER
  SPINE (pre-window ∀ch + one pick step + post-window ∀ch, composed
  over the quantified prefix). Both [propext, Quot.sound].
- 2026-08-23 **The becomeFollower CROSSING** (HandlerEqSym): pre 642
  + pick + post 302 = **`bf_intn_span`, 945 steps as ONE
  prefix-quantified span**. The picked key is SYMBOLIC (x₅) in the
  post fixture — the valuation absorbs the pick, ONE post-window
  serves every pick (§4(ii)'s collapse; the key lands only in spots
  `absRaftNode` never reads). The pick step enters CONDITIONED (kit
  style); `bf_intn_span_witness` discharges it at the concrete
  stream `[3]` by closed evaluation (#eval-checked first: config and
  state images both equal; probe `BfWindowProbe`). Post-window ends
  at this fixture's nil-logger call (Q6) — the empty-fixture
  analogue of the 2b residual. Module builds 136 s; zero
  sorry/native_decide; axioms as probed (arc log commit).
- 2026-08-23 [AGENT] **The FULL 3,233-step span did NOT land** — the
  3,233 trace is the POPULATED-tracker run; honestly enumerated
  remainder (the successor's list, in order): (1) the populated
  fixture (trk.Progress mapData + three Progress cells + the
  raftLog/unstable/MemoryStorage chain — recipe = probe2's cell
  dump); (2) Visit's 3-pick crossing = the SAME spine applied three
  times + the sort-collapse at the canonicalization point (§4(ii));
  (3) the 2b interface-dispatch splits (logger Infof + 3×
  storage.LastIndex — hand `stepFn_call_enter` conditioned steps at
  the pinned tables, ~30-50 lines each); (4) the ∀ρ pick-fact
  discharge (deriving `bf_intn_span`'s hpick from
  `stepFn_pick_generic`'s facts computed over the γ-image — the one
  genuinely new proof obligation left).

### Re-measure update (slice 4)

The 945-step crossing costs ~130 lines of fixture + 5 theorems in
HandlerEqSym vs ~8,500 at the pilot's measured 9 hand-lines/step.
Cumulative: TableExt 1,623 lines (ALL FOUR general classes +
witnesses; one-time), HandlerEqSym 289 (every becomeFollower
instance). Elaboration: 136 s for the 945-step module. The 600–1,000
line full-handler projection STANDS, now evidence-backed at
945/3,233 of the real handler.

### A4-U3 ASSESSMENT (posted per the dispatch)

**Assembly as projected, YES** — with the four-item remainder above
as U3's opening checklist. The spine + pick lemma + windows make
each remaining piece a repetition of a landed pattern except item
(4), which is bounded (one lemma over a fixed γ-image heap). The
absState-correspondence layer on top (the actual handler EQUATION)
is the pilot's validated form at the span's endpoints.

## A4-U2 slice-4 exit (2026-08-23, tip = this commit)

Gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at
ca53e587's tree — **RESULT: PASS, exit 0** (23 ok steps,
`artifacts/ci-arc4-u2c.log`; no-diff notes = the sanctioned
proofs+docs hatch). Full proofs+Audit 471 jobs green; Kit pins 15
(two new, at the CLEANER-than-expected [propext, Quot.sound]).
Branch-complete for this dispatch; nothing merged; the
comparator-landmark staleness note stays flagged for the operator's
merge step.

## A4-U3 — the first full handler equation (2026-08-23, successor worker)

- 2026-08-23 SUCCESSOR RE-VERIFICATION (convention: predecessor top
  claims re-proved before building on them), at dispatch tip
  dab1163d; during verification the coordinator's dispatch-log commit
  638b683b (`docs/raft-campaign-log.md` only, file-disjoint) landed —
  recorded per the one-writer discipline, tree clean at 638b683b.
  Results, all fresh probes:
  - capped core `lake build`: green (58 jobs); capped proofs+Audit
    `lake build`: green (471 jobs) — every `#guard_msgs` Kit pin is
    build-enforced, so pins GREEN by construction of this run.
  - `#print axioms` (capped `lake env lean`, verbatim):
    `stepFnIter_window_pick_window` [propext, Quot.sound];
    `bf_intn_span` + `bf_intn_span_witness` and
    `symEvalWindowTB_refines`/`'` all [propext, Classical.choice,
    Quot.sound] — matching the predecessor's recorded values.
  - hatch grep `sorry|native_decide|axiom ` over
    `Sym/TableExt.lean` + `Specs/Raft/*.lean`: zero matches.
  - **Count correction (summary-layer drift, lesson (i)):** the
    TableExt pin block in `proofs/Audit/Kit.lean` holds **14**
    extension pins (`stepFnT_conc`..`stepFnIter_window_pick_window`,
    lines 650–676), not 15: the slices-2+3 exit's "13" was itself 12
    (recount at 9719786f: 18 GoLean.Sym pins − 6 pre-existing), and
    the slice-4 exit restated 13+2 instead of recounting. All 14 are
    green (build-enforced); no pin is missing — the claim's COUNT was
    wrong, not its content.
- 2026-08-23 U3 contact round (probes `FixtureProbe`/`FixtureProbe2`,
  outputs `artifacts/probe/fixture.out` + inline): full untruncated
  entry-state cell dump + the lowered bodies of Visit / reset$lit0 /
  raftLog.lastIndex / unstable.maybeLastIndex /
  MemoryStorage.{LastIndex,lastIndex,LastIndex$deferSync0} /
  newReadOnly / ResetVotes / NewInflights / becomeFollower /
  Entry.GetIndex + the fixture-relevant typedefs. Checklist-shaping
  facts found:
  - **The deferred Unlock is a PLAIN funcVal** — the frontend
    synthesizes `LastIndex$deferSync0` and the deferCall's callee expr
    is `Expr.funcVal` (no method-value formation); the landed TB drain
    arms cover it. No new machinery.
  - **The interface calls are lowered as INTERFACE-METHOD FIDs**
    (`raft.Storage.LastIndex`, `raft.Logger.Infof` with body
    `$interface-method-unreachable`) — the 2b hand split is the
    drained-callArgsK enterFrame step with dispatch resolved at the
    concrete receiver interface value, exactly the checklist's shape.
  - **Census correction to the dispatch's "3× storage.LastIndex": it
    is 4 on the real shape** — the subject's closure calls
    `raftLog.lastIndex` per node for `Next` (3×) plus once more in the
    `id == r.id` branch (real `r.id` = 1 ∈ ids); the predecessor's
    count matched a fixture with default id=0 where the Match branch
    never fires. U3's fixture sets id=1 (the real trace's value), so
    4 dispatch splits for LastIndex + 1 for Infof.
  - **One more same-lever Q4-family member is REQUIRED**:
    `Expr.defaultValue` at a DEFINED type (`tracker.StateType` inside
    reset$lit0's Progress literal) — the design's named residual list
    ("structLit / defaultValue / convert"), consumed on demand as
    prescribed; goes into TableExt as `defaultValueT` beside
    buildStructValueT. Not new machinery.
  - **Visit's sort is the `Stmt.sortSlice` stmtOp** (frontend-lowered),
    and the ids fill is `ids[n] = id` with n counting DOWN — pre-sort
    ids = [k₃,k₂,k₁]; post-sort [1,2,3] for every order: the §4(ii)
    collapse point is the ONE sortSlice apply step.
- 2026-08-23 [AGENT] U3 proof-shape plan (logged before building):
  ONE shared symbolic window chain (picked keys enter as vars
  x₅..x₈ = Intn key + 3 Visit keys; vars 1,2,3,4 = Vote/lead/state/
  leadTransferee; x₉ = the lead argument; Term CONCRETE 0 so reset's
  term-equal branch is decided — the term-change branch is a recorded
  residual, not attempted in U3), hand conditioned steps at: the 4
  picks (spine applications), the Visit range-STOP step, the ONE
  sortSlice apply (the collapse), and the 5 interface-dispatch
  enters. Choice-prefix quantification: keys derived uniformly where
  candidate lists are consecutive (Intn: key = c₁%10; Visit pick 1:
  key = c₂%3+1); the 6-leaf case analysis (pick-2 candidates depend
  on pick 1) is confined to the pick2..sort segment; everything after
  the sort apply is ONE shared window chain (dead key cells stay
  symbolic — `absRaftNode` never reads them). This realizes checklist
  items (2) and (4) without per-order window re-elaboration.
- 2026-08-23 U3 slice A LANDED — checklist item (1), the populated
  fixture, VALIDATED at both levels (probe `BfU3Probe.lean`, outputs
  inline; every number below is from these two runs):
  - Phase 1 (machine, concrete): the 21-cell populated fixture
    (recipe = probe2's dump: trk.Progress mapData + 3 Progress + 3
    Inflights cells, raftLog→MemoryStorage chain with a 1-entry
    plainpb ents array, readOnly/acks, harnessLogger, static
    globalRand at 18/19, r.id=1) runs the drained
    `becomeFollower(0, lead)` call END TO END: **3,234 machine steps,
    exactly 4 choices consumed** (steps 642/826/855/884), dispatch
    sites at 1151/1639/2060/2616 (Storage.LastIndex ×4) + 3221
    (Logger.Infof), final config `.next .stop`, and
    `absRaftNode post = specBecomeFollower n 0 leadArg` EXACTLY
    (pre ⟨0,7,2,1,1,1⟩ → post ⟨0,7,4,0,1,1⟩ at the probe scalars).
  - Phase 2 (mirror, symbolic vars 1-4 + 9): the SAME span as **12
    transported windows [642,183,28,28,28,3,233,487,420,555,604,12] +
    11 hand crossings** (4 picks, range-stop, sortSlice apply, 5
    dispatch enters); mirror total 3,234 = machine total, and the
    **γ-image of the final mirror state == the machine's final heap**
    (nextAddr 188 = 188) — every crossing construction validated
    end-to-end before any theorem is stated.
  - TableExt grew the TWO same-lever residuals the walk exposed
    (beyond the predicted defaultValue): `defaultValueFuelT` +
    `valueEqBFuelT`/`valueEqRT'` (interface-nil + defined-resolution
    compares — `err != nil`) at the SubTable layer, and `toInterface`
    at the TB layer (canonicalTy returns partial answers on a miss,
    so it demands table EQUALITY — recorded in the arm's docstring).
    Conc lemmas defaultValueFuelT_conc / valueEqBFuelT_conc /
    valueEqRT_conc / canonicalTyFuel_types all
    [propext, Quot.sound] (fresh probe); 4 new Kit pins (extension
    pin count now 14+4 = 18 by recount). HandlerEqSym rebuilt green
    (134 s) — the landed 642/945-step windows are UNCHANGED by the
    new arms (the overrides agree with the shipped step on every
    non-quit config; the green `with_unfolding_all rfl` re-checks are
    the proof).
- 2026-08-23 [AGENT] Class-2b COMPLETED in TableExt instead of the
  dispatch's per-site hand splits (deviation from checklist item 3's
  letter, logged): with 5 dispatch sites in THIS handler and ~20
  handlers ahead, the per-split route re-pays the same dispatch-walk
  congruence every time; the lift is the design §3 "ONE lever, not
  three" scope completed with the module's own pattern — machine
  helpers at `TB.toState` (`concreteMethodForDynamic?` +
  `canonicalTyFuel_types`/`methodRecvDynamicTy_tables` congruences),
  NO-DEREF path only (pointer-box-to-value-receiver deref reads the
  heap and stays a quit, as do nil receivers). Not new machinery —
  the same conditioned-table lever as every other arm. Consequence:
  the chain simplifies to **7 windows [642,183,28,28,28,3,2316] + 6
  crossings** (probe re-run: γ-image == machine heap, totals 3,234
  both). `dynamicDispatchT` gained args and a redirect result;
  `enterFrameT` mirrors the machine's structure verbatim (incl. the
  post-dispatch arity re-check); `enterFrameT_conc`/`stepFnTB_conc`
  updated; HandlerEqSym re-elaborates green (153 s), landed window
  counts unchanged.
- 2026-08-23 CHECKPOINT (recomputed; slice B in flight): lane commits
  since the dispatch tip 638b683b: 1 (082a45cf, slice A). New modules
  building toward the equation: `BfFixture.lean` (the populated
  fixture + the 7-window chain, 12→7 window-count rfls + `uC13_stop`;
  lake-built GREEN in 327 s), `BfSteps.lean` (uρ/uKeys +
  `normalize_small` + `stepFn_pick_transport` — item 4's lemma:
  `stepFn_pick_generic` ∘ `alloc_conc`, prop-level, no heavy
  reduction — + `stepFn_stop_transport` + sites 1–2 pick facts,
  case-free, elaborated GREEN), `BfSteps2.lean` (sites 3–6 with the
  6-leaf analysis; elaborating), `BfEquation.lean` (composed
  3,234-step span + THE EQUATION + §3.3 witness; drafted, blocked on
  BfSteps2). Judgment call logged: `stepFn_pick_transport` is
  raft-independent — PROMOTION-LEDGER row (move to TableExt/kit at a
  consolidation slice; second consumer = any handler's range loop).
- 2026-08-23 [AGENT] Slice-B performance findings (measured, each on
  this lane's capped builds):
  - BfSteps (transport + sites 1–2, case-free): 604 s module build.
  - Sites 3–4 (6-leaf candidate analysis, cheap post-walk leaves):
    green inside BfSteps2's first pass (~25 min for the whole file's
    heavy shape/entry facts).
  - The SORT-collapse leaves are the cost outlier: ONE leaf's
    whole-step kernel rfl = **8 min 24 s, several GB** (isolated
    measurement, `artifacts/probe/sortleaf.lean`); six in one lean
    process accumulated past the 24G cap and were killed — the
    #eval-said-true/kernel-grinds-anyway shape is NOT a false goal
    here (the isolated leaf proves), it is cumulative memory across
    goals. Fix: ONE MODULE PER LEAF (`BfSortLeaf{00..21}.lean`,
    process-isolated memory) + a cheap dispatcher (`BfSortStep`).
  - Projected same-lever performance lift for U4+ (logged for the
    verdict): STATE LITERALIZATION — dump intermediate SymStates as
    source literals with one bridge `rfl` each, so downstream facts
    reduce against literals instead of re-evaluating window chains;
    would collapse the sort-leaf and projection costs by an order of
    magnitude. Not built in U3 (time-boxed); the honest cost numbers
    above are the argument for building it in the first U4 slice.

## A4-U3 slice B complete — THE FIRST FULL HANDLER EQUATION (2026-08-23)

**`becomeFollower_handler_eq` (BfEquation.lean) IS PROVED**, in the
charter's exact form: from the drained `becomeFollower(0, lead)` call
configuration at ANY state γ-extending the populated fixture
(∀ valuation ρ, ∀ σ with `bfTB.Agrees σ`) whose abstract projection is
`some n = some ⟨0, vote, lead₀, state, 1, 1⟩`, over EVERY consumed
choice prefix `c₁ c₂ c₃ c₄` (∀ streams `c₁::c₂::c₃::c₄::ch`), the run
reaches the function's return (`.next .stop`) in exactly **3,234
steps of `stepFnIter`** with the four choices consumed, and the final
state's projection equals **`specBecomeFollower n 0 lead`**. Two
side conditions, both genuinely external (the kit's conditioned
style, discharged concretely in the witness): `hvote`/`hlead` — the
Vote heap value and the lead argument are in `uint64` range (their
normalize is the identity).

- The §3.3 discharge witness `becomeFollower_handler_eq_witness`:
  every premise at concrete values (`wBase` tables, live valuation
  Vote 7 / lead 2 / state 1 / leadTransferee 5 / lead-arg 4, the
  probe's stream `[3,1,0,0]`) — projection
  `some ⟨0,7,2,1,1,1⟩ → some (specBecomeFollower ⟨0,7,2,1,1,1⟩ 0 4)`.
- Fresh `#print axioms` (capped probe, verbatim):
  `becomeFollower_handler_eq`, `becomeFollower_handler_eq_witness`,
  `bf_full_span` all [propext, Classical.choice, Quot.sound];
  `stepFn_pick_transport`, `uSort_step`, `uPick1_step`
  [propext, Quot.sound]. Hatch grep over all `Bf*.lean`: zero
  sorry/native_decide/axiom.
- Composition (the spine at scale): 7 transported windows
  [642,183,28,28,28,3,2316] ⧺ 4 pick steps (`stepFn_pick_transport` —
  item 4's ∀ρ discharge, prop-level via `stepFn_pick_generic` ∘
  `alloc_conc`; keys enter as `x₅=↑(c₁%10)`, `x₆=uKey1 c₂`,
  `x₇=uKey2 c₂ c₃`, `x₈=uKey3`) ⧺ the range-STOP ⧺ the ONE sortSlice
  apply — §4(ii)'s COLLAPSE, realized as six per-leaf lemmas (every
  pick order lands in one leaf; every leaf's post state is `uS12`
  with ids=[1,2,3]) behind one dispatcher. The projection conclusion
  is choice-independent; the final state is prefix-dependent (∃σfin).
- A probe finding recorded as fixture-shape knowledge: store-time
  whole-struct re-normalization norm-WRAPS the symbolic scalars
  (Vote 13-deep, lead 3-deep by handler exit — `ProjProbe`); the
  `unrm`/`unrm_id` helper discharges the wrapping under the range
  hypotheses. This is why value-symbolic handler equations carry
  uint64-range side conditions for every SURVIVING symbolic scalar.
- Interface dispatch (checklist item 3) crossed IN-WINDOW via the
  completed class-2b — zero hand splits in the final proof; the
  5 dispatch sites (4× Storage.LastIndex + Logger.Infof) sit inside
  window 7.
- Module inventory (wc -l, recomputed): BfFixture 285, BfSteps 295,
  BfSteps2 377, BfSortLeaf00..21 6×22=132, BfSortStep 53, BfEquation
  165 — **1,307 lines total**, all wired into the GoLeanProofs
  aggregator; full proofs+Audit build GREEN, **482 jobs**. Measured
  build costs: BfFixture 327 s; BfSteps 604 s; BfSteps2 ~510 s; each
  sort leaf ~490–515 s (six, process-isolated); BfEquation ~350 s.
  1,307 lines vs the pilot's 3,000–6,000 hand-walk projection for the
  same span; the U2 600–1,000 estimate exceeded by ~30% — the excess
  is exactly the sort-leaf/module-split scaffolding and the 6-leaf
  candidate analysis, both of which the state-literalization lift
  would shrink.

## A4-U3 DELIVERABLE 2 — THE A4 SCALE VERDICT (re-projection of U4..U9)

Derivation anchors: every number here is from this unit's builds/probes
(above), the pilot verdict's measured table, or the Arc-2 census
(`docs/campaign-arc2-probes/records/probeA-census.out` on the arc2
lane, read-only: the 711,616-step completing run's per-fid call
counts).

**What one full handler equation now costs, measured end-to-end
(becomeFollower, the smallest handler with EVERY hard feature):**
3,234 steps, 4 choice sites (2 map-range loops), 1 sort
canonicalization, 5 interface dispatches, defer/mutex pairs →
1,307 lines / ~50 min of capped builds / zero new axioms beyond
[propext, Classical.choice, Quot.sound]. The one-time general
machinery paid across U2+U3 (TableExt: all five design classes +
class-2b dispatch + the U3-a residual lifts + congruences) now stands
at 2,052 lines and is HANDLER-INDEPENDENT.

**Cost anatomy (what scales with what):**
- Windows: step-count-independent to write (~2 lines each), build
  cost ~linear in steps (~40 ms/step kernel; 8,250 cumulative
  step-evals ≈ 327 s in BfFixture).
- Choice crossings: ~50–90 lines each via `stepFn_pick_transport`;
  case analysis only where CANDIDATE SETS depend on earlier picks
  (Visit's 6 leaves), and the §4(ii) collapse holds: after the sort,
  ONE shared chain regardless of order.
- The cost OUTLIER is kernel re-evaluation of window chains inside
  per-leaf facts (sort leaves ~8.4 min each). This is a PERFORMANCE
  problem, not a proof-shape problem — the state-literalization lift
  (bridge-rfl'd SymState literals) removes it and should be U4's
  slice 0.

**Re-projection of the remaining ~19 handlers** (census call counts in
parentheses; the seam design §2(B) unit list):

- **Wave 1 — the reset family + storage leaves (batchable, ~zero new
  machinery):** becomeCandidate/becomePreCandidate/becomeLeader (1–2
  calls each) REUSE the reset crossing verbatim — the 6-crossing
  block should be factored ONCE as a `reset`-span lemma (promotion
  row) and each become* becomes a ~200–400-line assembly.
  MemoryStorage.{FirstIndex,Term,Entries} (66–122 calls) are
  LastIndex-shaped: window-only, no choice sites — ~100–200 lines
  each. Est. 5–7 handler equations in 1–2 sessions once
  literalization lands.
- **Wave 2 — the message handlers:** handleAppendEntries (12),
  handleHeartbeat, the RequestVote pair. New same-lever residuals
  expected: the `appendSlice` choice site (appendSpill — needs an
  appendSpill analogue of `stepFn_pick_transport`, same shape),
  log-slice ops in-window, message construction via landed
  structLit/toInterface. THE REAL NEW OBLIGATION IS SPEC-SIDE, not
  machinery: these handlers' equations need `absRaftNode` EXTENDED to
  log entries and the outboxes (GAP-V1-1/-3) — the abstraction-layer
  work, one design slice before wave 2 starts.
- **Wave 3 — dispatch + plumbing:** raft.Step (53) / stepLeader (18)
  / stepFollower (12) / stepCandidate (2) branch per MESSAGE TYPE —
  the fixture-family dimension is per-branch (NOT per pick order —
  that collapses); expect one window chain per (handler, msg-type)
  pair, sharing tails. RawNode Ready/Advance plumbing (22–53) is
  window-heavy but choice-light.
- **Residual classes carried into U4+ (none counted as done):**
  (1) the term-change branch of becomeFollower (second fixture
  family, same machinery); (2) `needsDeref` interface dispatch
  (pointer box → value-receiver method) stays a quit until a
  consumer appears; (3) the appendSpill pick transport; (4)
  GAP-U1-W1 (witness reachability) unchanged; (5) the absState
  extension for wave 2 (the seam's layer-(A) growth).
- **Aggregate estimate:** with literalization + the reset-span lift,
  waves 1–3 ≈ 15–25 sessions of U3-shaped work — the per-handler
  equation cost has moved from the pilot's NO-GO (~9 lines/step,
  3,000–6,000 lines/handler hand-walked) to ~400–1,300 lines of
  mostly assembly, inside the gallery bar. The binding constraints
  are now (a) kernel-evaluation wall time (fix: literalization),
  (b) the spec-side absState extension (design work, wave-2 gate).

## A4-U3 exit (2026-08-23, tip = this commit)

**CHECKPOINT (recomputed):** commits since the dispatch tip dab1163d:
12 by `git log --oneline dab1163d..HEAD | wc -l` — 3 of this worker's
(082a45cf slice A, 2c71ed83 slice B, + this log commit) + 9
coordinator campaign-log commits interleaved (638b683b, c6dac547,
44d579ab, 1415a96d, 5ec7b0f7, 665f821e, 698d17e6, d59841b8, 7c119bfb
— all `docs/raft-campaign-log.md` only, file-disjoint from this
unit's tree; recorded per the one-writer discipline).

Unit-end gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci`
at 2c71ed83's tree — **RESULT: PASS, exit 0** (tail recorded at
`artifacts/ci-arc4-u3.log`, gitignored — capture was `| tail -25`,
so the record holds the final 18 ok steps + both sanctioned no-diff
notes + RESULT; the full-run PASS is the exit code). The comparator
landmark note (80 commits stale at this run) stays flagged for the
operator's merge step, as in every prior arc-4 exit.

**Checklist disposition (the dispatch's four items):**
1. Populated fixture — DONE (slice A; probe-validated at machine AND
   mirror level, γ-image == machine heap end-to-end).
2. Visit's 3-pick crossing — DONE (the spine ×3 via
   `stepFn_pick_transport`; sort-collapse realized as the 6-leaf
   dispatcher; ONE shared post-sort chain).
3. Interface-dispatch splits — DONE BY COMPLETION OF CLASS-2B instead
   of hand splits ([AGENT] deviation logged above: same lever, kills
   the recurring per-handler cost; zero splits remain in the proof).
4. ∀ρ pick-fact discharge — DONE (`stepFn_pick_transport` =
   `stepFn_pick_generic` ∘ `alloc_conc`, prop-level).
THEN the equation itself — DONE (`becomeFollower_handler_eq` +
witness, axioms probed verbatim above).

**Open gaps carried (none counted):** GAP-V1-1..5 and GAP-U1-W1
unchanged; U3 adds: the term-change branch (second fixture family),
the appendSpill pick transport (wave 2), the needsDeref dispatch
quit, and the state-literalization performance lift (U4 slice 0
recommendation). PROMOTION LEDGER additions: `stepFn_pick_transport`
(raft-independent; second consumer = any handler's range loop) and
the reset-span composite (consumer = every become* handler).

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1).

## A4-U4 — state literalization + wave 1 (2026-08-23, successor worker)

- 2026-08-23 SUCCESSOR RE-VERIFICATION at the actual tip 6c18dfad
  (the dispatch named 5e7834a9; the one extra commit is the
  coordinator's `docs/raft-campaign-log.md`-only append, file-disjoint
  — recorded per the one-writer discipline, tree clean). All fresh
  probes, all PASS:
  - capped core build green (58 jobs); capped proofs+Audit green
    (482 jobs — matching U3's recorded count).
  - `#print axioms` (capped `lake env lean`, verbatim):
    `becomeFollower_handler_eq` and `_witness`
    [propext, Classical.choice, Quot.sound]; `stepFn_pick_transport`
    [propext, Quot.sound] — matching U3's record.
  - **Kit pin recount (the dispatch's 14-vs-15 drift question): the
    true number is 18 extension pins** — 24 total `GoLean.Sym`
    `#guard_msgs` pins in `proofs/Audit/Kit.lean` minus 6 pre-existing
    (lines 628–638); the U2 block holds 14 (650–676) + 4 U3 residual
    lifts (685–691). The logged 13 and 15 were both restatement drift
    (lesson (i)); U3's "14+4=18 by recount" is CONFIRMED.
  - hatch grep over `Sym/TableExt.lean` + `Specs/Raft/*.lean`: zero
    `sorry|native_decide|axiom `.
- 2026-08-23 [AGENT] Slice-0 design (the verdict's named fix, read at
  the sort-leaf cost anatomy): the leaves' `rfl`s re-evaluated the
  whole `uS0→uS11` chain in the kernel per fact. Implementation:
  window-output states/configs dumped as SOURCE LITERALS —
  `Sym`-family types have no `Repr`, so a fail-closed custom printer
  (`artifacts/probe/BfLitGen.lean`) prints `Value/Cont/Config/State`
  at `symDom`, reusing the machine's derived `Repr` for concrete
  payloads (round-trip verified by `ReprSmoke.lean` first: derived
  Repr emits fully-qualified, parenthesized source). Generated
  `Specs/Raft/BfLit.lean` (508 KB, elaborates in 2.6 s). Crossing
  outputs (even indices) stay DEFINED via the crossing constructions
  on the literals. Trust story unchanged: the window LINK theorems
  `uW*_out : symEvalWindowTB bfTB n uSi uCi = (n, uS(i+1), uC(i+1))`
  (kernel `rfl`, full-output form) re-check every literal against the
  evaluator — each window evaluated exactly ONCE, and the links are
  the drift alarms on any fixture change. `uW*_n` kept verbatim,
  derived by `rw`. NEW `uWin1..uWin7`: γ-level transported windows at
  literal endpoints (via `symEvalWindowTB_refines` at the link), so
  `bf_full_span`'s composition unifies syntactically.
- 2026-08-23 Slice-0 measurements (before → after, same machine,
  capped):
  - BfFixture 327 s → **132 s** (lake-reported; links only).
  - BfSteps 604 s → **218 s** (zero text changes — the heavy facts
    now reduce against literals).
  - BfSteps2 ~510 s → **1.1 s** (zero text changes).
  - Isolated sort leaf 504 s → **352 s** — the chain re-eval is gone
    (~150 s) but an intrinsic cost remained; the split measurement
    (below) located it exactly.
- 2026-08-23 **THE ELABORATOR-VS-KERNEL SPLIT (measured, decisive):**
  the literalized leaf under `debug.skipKernelTC true` (probe
  `LeafSplit.lean`) costs **359 s** vs 352 s normal — i.e. the
  ELABORATOR's `with_unfolding_all rfl` defeq is ~100% of the cost
  and the kernel's check of the SAME conversion is ≈ 0 (the
  elaborator's whnf takes a slow path through the machine's
  `do`/`Std.Range.forIn`/`Except`-bind spines; the kernel's
  evaluator does not). This also explains the U2 gotcha ("γ-image
  projections need `decide +kernel`; elaborator whnf fails") — same
  pathology, now measured.
- 2026-08-23 [AGENT] **`kernel_rfl` landed**
  (`proofs/GoLeanProofs/Sym/KernelRfl.lean`, wired into the
  aggregator): for a syntactic `lhs = rhs` goal, assigns
  `Eq.refl lhs` directly so the conversion is checked ONCE, by the
  KERNEL at `addDecl`. Trust story unchanged — the kernel still
  typechecks the whole theorem exactly as it checks every `rfl`; no
  new axiom, no native evaluation; fail-closed BOTH ways (non-Eq or
  metavariable-bearing goals are refused by the tactic — the mvar
  refusal matters: inline premise discharges that need unification to
  determine implicits correctly stay `with_unfolding_all rfl` — and a
  FALSE goal dies loudly at `addDecl` with a kernel type mismatch,
  verified on `2+2=5`, probe `KRflFalse.lean`). Judgment call under
  §5 tooling latitude; PROMOTION-LEDGER row below (consumers: every
  machine-side fixture fact in every handler).
- 2026-08-23 Slice-0 FINAL numbers (both levers: literals +
  `kernel_rfl`; lake-reported, full proofs+Audit green at 478 jobs =
  482 − 6 retired leaf modules + BfLit + KernelRfl):
  | module | U3 | after |
  |---|---|---|
  | BfLit (new, generated) | — | 2.3 s |
  | BfFixture (links) | 327 s | 99 s |
  | BfSteps | 604 s | 1.2 s |
  | BfSteps2 | ~510 s | 1.2 s |
  | sort leaves + dispatcher | 6×~504 s + dispatch ≈ 3,050 s | **1.0 s** (one module again; the per-leaf process isolation is retired) |
  | BfEquation | ~350 s | 10 s |
  | **whole Bf family** | **~50 min** | **≈ 115 s** |
  The verdict's "order of magnitude" projection is met with ~25×
  (family) / ~3,000× (the sort-leaf path). Axioms re-probed after the
  conversion: `becomeFollower_handler_eq`/`_witness`/`bf_full_span`
  [propext, Classical.choice, Quot.sound]; `uSort_leaf_00`,
  `uSort_step`, `uW1_out` [propext, Quot.sound] — unchanged.
  `uW*_n` statements kept verbatim (derived from the `uW*_out`
  links); `uSort_step`/`becomeFollower_handler_eq` statements
  byte-identical to U3.
- 2026-08-23 Slice 0 committed (deae0f08). WAVE 1 begins; spec-side
  functions re-grounded in `AbsState.lean` (`specBecomeCandidate`,
  `specBecomePreCandidate` — subject lines cited; Verdi correspondence
  in docstrings, compat/verdi never imported).
- 2026-08-23 **becomePreCandidate_handler_eq PROVED** (commit
  5a8d6251; `BpcEquation.lean`, the SECOND full handler equation).
  Probe `BpcProbe.lean` first: machine 152 steps, ZERO choices,
  projection == spec, γ-image == machine heap; wrap depths probed
  (Vote symbolic at depth 5 → the one `hvote` side condition). ONE
  transported window; `ch` rides through unchanged (the equation
  form's strongest case); state CONCRETE 0 (the `state == StateLeader`
  panic guard branches on it — fixture-family precondition, the U3
  fine-print pattern). §3.3 witness at Vote 7/lead 2/ldT 5. Module
  110 s; no literals needed at one window (kernel_rfl suffices — the
  slice-0 pattern note: literalization pays from the second window
  on). Axioms: eq/witness/span [propext, Classical.choice, Quot.sound].
- 2026-08-23 **becomeCandidate_handler_eq PROVED** (commit 8cb8b423;
  `Bc{Lit,Fixture,Steps,Equation}.lean`, the THIRD full handler — the
  reset-span REUSE instantiated, term-change branch = the U3 exit's
  named second fixture family). Probe `BcProbe.lean` first: machine
  3,282 steps / 4 choices (steps 686/870/899/928), projection ==
  specBecomeCandidate pre 1; mirror 7 windows [686,183,28,28,28,3,
  2320] + 6 crossings, γ-image == machine heap (nextAddr 186). NO
  side conditions (every pre-symbolic scalar overwritten; post
  scalars are norm-wraps over LITERALS — probed depths 16/15/12,
  reduce closed). Reused verbatim: `uρ`/`uKey1/2/3`/`uCands1/3`+gets/
  `uKeyV*`/`stepFn_pick_transport`/the crossing constructions.
  [AGENT] simplification found while replicating: at literal states
  the STOP and SORT crossings are WHOLE-STEP `kernel_rfl` facts per
  key-order leaf (six one-liners + dispatcher each) — no transport,
  no shape/heavy-fact ceremony; the pick crossings keep the transport
  (the choice index is free, so the step cannot reduce closed).
  Handler cost, measured: ~790 hand lines + 527 KB generated
  literals; builds BcLit 2.4 s + BcFixture 96 s + BcSteps 1.5 s +
  BcEquation 10 s ≈ 110 s. Axioms: eq/witness/span [propext,
  Classical.choice, Quot.sound].
- 2026-08-23 [AGENT] Storage leaves (wave table's LastIndex-shaped
  rows): per the dispatch's per-handler verification, `FirstIndex`/
  `Term` DO need absState beyond v1 — the entries. ADDITIVE extension
  landed in `AbsState.lean`: `absStorageEnts` (the MemoryStorage
  `ents` reader through the plainpb pointer-scalar cells, fail
  closed; `callStats` deliberately unread) + `specFirstIndex`/
  `specTermAt` re-grounded from `storage.go`. **GAP-V1-1 renumbered:
  GAP-V1-1a (storage half) CLOSES here; GAP-V1-1b (unstable half +
  offset arithmetic — the raftLog view) stays open for wave 2.**
  Probes first (`MsProbe2.lean`, `AbsStorProbe.lean`): caller-shaped
  `Stmt.call` with two var targets (the machine is stuck on a
  target-less drained call of a 2-result function — "extra GoCore
  assignment value" — so the CALLER SHAPE is part of the fixture);
  FirstIndex 178 steps → fi=2/er=nil; Term(1) 246 steps → fi=1/
  er=nil; both mirrors γ-image == machine heap; absStorageEnts =
  some [(1,1)] #eval-checked (after re-learning the rule the hard
  way: a first MsEquation build was declared slow before realizing
  the 10-min wall was the AbsState-edit REBUILD CONE, not the new
  module — the new facts each check in seconds). RESIDUALS recorded:
  the Term ERROR branches (the lowered error path loads package-level
  error vars at static twin addresses the leaf fixture does not
  carry — the probe's Term(0) run exposed the address collision
  loudly); `MemoryStorage.Entries` scoped OUT of this slice
  (`limitSize`/`entryEncodingSize` needs its own spec-side
  re-grounding — refused to model it loosely).
- 2026-08-23 **msFirstIndex_handler_eq + msTerm_handler_eq PROVED**
  (commit 6961a5ae; `MsEquation.lean` — the FOURTH and FIFTH handler
  equations, the first RESULT-returning ones). Form: run completes
  (178/246 steps, zero choices, `ch` rides), result cells =
  spec-of-pre-abstraction, error nil, abstraction PRESERVED. Kernel
  lesson recorded the hard way (two failed builds): (a) a module
  using `kernel_rfl` on window-sized facts needs the
  `maxHeartbeats` bump — the KERNEL respects the heartbeat budget
  ("deterministic timeout" at addDecl); (b) per-conjunct facts must
  be their OWN declarations — four `kernel_rfl` conjuncts bundled
  into one `addDecl` blow past even the raised budget (no reduction
  sharing across one declaration's conjuncts), while the same facts
  as five small decls check in seconds each. Module 348 s. Axioms:
  all four eq/witness [propext, Classical.choice, Quot.sound].
- 2026-08-23 [AGENT] **becomeLeader SCOPED OUT of wave 1, with
  measured grounds** (probe `BlProbe.lean`, machine run from
  state=1): completes in **6,466 steps consuming SIX choices** — the
  reset span's 4 picks (steps 659/843/872/901) plus TWO more (5171/
  6352) on the `appendEntry` path = the appendSlice/spill choice
  site, exactly the U3 verdict's wave-2 residual (3) (needs the
  appendSpill analogue of `stepFn_pick_transport`), plus `send` into
  `msgsAfterAppend` (GAP-V1-3 territory). The v1 PROJECTION is
  compatible (post = ⟨term, vote, id, 2, ..⟩ — term-equal reset
  branch, vote preserved), so only MACHINERY blocks it — it moves to
  wave 2 beside the message handlers, not silently dropped.

### Updated wave projection (recomputed at this unit's evidence)

Wave 1 outcome: 4 NEW handler equations proved (5 total on the
branch), each witness-carrying, U3's exact form: becomePreCandidate
(1 window, 0 choices), becomeCandidate (7 windows + 6 crossings, the
reset-span spine reused with zero new transport machinery),
MemoryStorage.FirstIndex/Term (result-returning form established).
Per-handler cost measured THIS unit: BPC ~160 lines/110 s; BC ~790
lines + generated literals/~110 s of builds; Ms pair ~230 lines/348 s
— i.e. the U3 scale verdict's "1–2 sessions once literalization
lands" for wave 1 came in at ONE session for 4 of its 5–7 handlers
(becomeLeader moved to wave 2 on measured grounds; Entries scoped
out pending its spec design). Remaining wave-2/3 rows unchanged from
the U3 verdict, with the appendSpill transport now DOUBLY motivated
(handleAppendEntries AND becomeLeader) and the absState extension
half-done (GAP-V1-1a closed; 1b + outboxes open).

### PROMOTION LEDGER updates (A4-U4)

- **`kernel_rfl`** (`Sym/KernelRfl.lean`) — LANDED, general: every
  machine-side fixture fact in every handler (already 5 consumer
  modules). The measured basis: elaborator whnf was ~100% of
  machine-side `rfl` cost, kernel ≈ 0.
- **The literal-generation printer** (`BfLitGen`/`BcLitGen` probes) —
  pattern established, 2 consumers (Bf, Bc); candidate for a shared
  probe library or in-repo tool at the next consolidation slice
  (currently probe-side duplication, acceptable per scratch
  conventions but noted).
- `stepFn_pick_transport` — second consumer LANDED (BcSteps reuses it
  verbatim); the promotion condition ("second consumer = any
  handler's range loop") is now met → lift to TableExt/kit at the
  next consolidation slice.
- The U3 "reset-span composite" row: realized as the
  literalize→link→transport→crossing-facts PATTERN (fixture-generic
  factoring is not possible at closed-evaluation windows — the
  continuation is baked into each chain — but the per-handler
  instantiation cost measured at ~one session per reset-family
  handler makes the pattern the composite); row retired in favor of
  the two rows above.

## A4-U4 exit (2026-08-23, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the dispatch-time
tip 6c18dfad: 4 (deae0f08 slice 0, 5a8d6251 BPC, 8cb8b423 BC,
6961a5ae Ms) + this log commit; no coordinator commits interleaved
this unit (checked: `git log 6c18dfad..HEAD` = the 4 above).

Unit-end gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci`
at 6961a5ae's tree + this log — **RESULT: PASS, exit 0**
(`artifacts/ci-arc4-u4.log`, gitignored; all ok steps; the two
no-diff notes are the sanctioned proofs+docs hatch — this unit
touched `proofs/GoLeanProofs/{Sym,Specs/Raft}/**` + the aggregator +
arc-4 docs only, no runtime code, no Corpus/, no baselines/). The
comparator-landmark staleness note (86 commits at this run) stays
flagged for the operator's merge step, as in every prior arc-4 exit.

**Handler equations proved on the branch after this unit (each with
its §3.3 witness; fresh `#print axioms`, all recorded verbatim at
their slice entries above):** becomeFollower (U3),
becomePreCandidate, becomeCandidate, MemoryStorage.FirstIndex,
MemoryStorage.Term — **5 total, 4 new this unit.**

**Open gaps carried (none counted):** GAP-V1-2..5 and GAP-U1-W1
unchanged; GAP-V1-1 split — 1a (storage ents) CLOSED, 1b (unstable
half) open; U3's residuals unchanged (becomeFollower term-change
branch; needsDeref dispatch quit); U4 adds: becomeLeader → wave 2
(measured: 6 choices — the appendSpill site ×2 — plus GAP-V1-3
outbox territory); MemoryStorage.Entries (limitSize spec design);
the Term/FirstIndex ERROR branches (static error-var addresses
absent from the leaf fixture); MsEquation's per-fact window
re-evaluation (literalize msFiS1/msTmS1 if the 348 s module ever
bothers anyone — the one-window-handler pattern note in BpcEquation
applies).

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1).

## A4-U5 — the allocation-symbolic refactor (2026-08-24, successor worker; the clever-tricks watch-list's top classic-ward item)

- 2026-08-24 SUCCESSOR RE-VERIFICATION at the dispatch tip 14f37f20
  (tree clean, no interleaved commits). All fresh probes, all PASS:
  - capped core build green (58 jobs); capped proofs+Audit green
    (484 jobs = U4's recorded 478 + the 6 wave-1 modules — the U4
    log's "478" was the slice-0 count, before the wave-1 modules
    landed; consistent, recorded).
  - `#print axioms` (capped probe, verbatim in
    `artifacts/probe/AxProbeU5.lean` run): ALL TEN of
    becomeFollower/becomePreCandidate/becomeCandidate/msFirstIndex/
    msTerm `_handler_eq` + `_witness` =
    [propext, Classical.choice, Quot.sound] — matching U4's record.
  - Kit pin recount: 24 total `GoLean.Sym` `#guard_msgs` pins in
    `proofs/Audit/Kit.lean` − 6 pre-existing = **18 extension pins**
    — the log's true number CONFIRMED.
  - hatch grep over `Sym/TableExt.lean` + `Sym/KernelRfl.lean` +
    `Specs/Raft/*.lean`: zero `sorry|native_decide|axiom `.
- 2026-08-24 Contact round (read, not guessed): the kit ALREADY
  carries the classic — `Frame/` is the executable frame theorem
  (`FrameSim` = renaming injection + disjoint frame + pointwise heap
  characterization; `stepFn_sim`/`stepFnIter_sim`/`execStmtLoop_ren`;
  `frameSim_seed`/`rebaseSimT` builders; AllocIndep = the quotient
  corollary). KEY FACT: `stepFnIter_sim` (Frame/Transfer.lean:29) is
  stated at EXACTLY the handler equations' level (`stepFnIter`, same
  fuel, same stream, `TripSim` payload). Naming collision found and
  flagged: the kit's `wp_frame_*` family (Laws/Call, Laws/Unwind) is
  Go CALL-frame machinery, not the SL frame rule.
- 2026-08-24 [AGENT] Route decision (design note §7, LINEAGE-lined
  per the new doctrine): the frame machinery composes with the
  TableExt transport AT THE MACHINE LEVEL, POST-transport — the
  transported span is already a machine-level `stepFnIter` fact at
  the pinned placement; `stepFnIter_sim` + `ExSim.ok_inv` lift it to
  every placement. **No frame-aware Sym variant needed; zero Sym
  edits — the zero-edits property holds a FIFTH time.** The §5
  D-relative-addressing v2 lever stays parked (it buys layout-SHAPE
  symbolism, not needed for allocation-symbolism). The one new
  obligation: projection rename-invariance (`absRaftNode_ren`).
- 2026-08-24 [USER] mid-unit directive received (Iris-preference
  ladder): answered from contact in design note §7.3b — iris-lean's
  `wp_frame_l/r` are real but bind to `IProp` WP over a
  `Language` instance (GoCore is not one; exact-fuel/exact-stream
  equations need time-credit-style bookkeeping Iris WP doesn't give
  us today); the Iris-compatible convergence (`FrameSim` ≈ big-sep
  points-to at symbolic addresses ∗ frame R, at the model level) is
  RECORDED for the reuse survey; this slice reuses the
  Yang–O'Hearn operational-locality idea (ladder rung 3); no new
  machinery (rung 4 vacuous).
- 2026-08-24 Slice landed (5c75dcc9 design, 82d0b72c code):
  `Specs/Raft/AllocEq.lean` (258 lines, 28 s module build) — the
  ALLOCATION-SYMBOLIC equation at becomePreCandidate:
  **`becomePreCandidate_handler_eq_alloc`**: from the drained call at
  ANY placement σF of the fixture footprint (arbitrary conforming
  relocation `r` + arbitrary disjoint frame `fr`, one `FrameSim`
  premise), the run returns in 152 steps, stream untouched, final
  state FrameSim-related to the fixture's post-image (footprint
  transformed AT the placement, frame preserved), and
  `absRaftNode σF ⟨r 0⟩` steps by `specBecomePreCandidate`. Plus:
  `absRaftNode_ren` (projection rename-invariance, one-time, serves
  every handler), `bpcCallAt`/`bpcCallAt_ren` (the call config at a
  symbolic receiver address), `renameStmt_ρT_zero` (generic identity
  seed discharge), and **`becomePreCandidate_handler_eq_of_alloc` —
  the shipped concrete statement re-derived from the symbolic form
  at the identity seed (statement form identical to
  `becomePreCandidate_handler_eq`, which stays untouched in
  BpcEquation.lean): the machine-checked proof of STRICT
  generalization.** §3.3 witness
  (`becomePreCandidate_handler_eq_alloc_witness`) discharges every
  premise concretely, FrameSim included. Full proofs+Audit green
  (485 jobs); hatch grep over AllocEq: 0. Fresh `#print axioms`
  (verbatim): becomePreCandidate_handler_eq_alloc / _of_alloc /
  _alloc_witness [propext, Classical.choice, Quot.sound];
  absRaftNode_ren, renameStmt_ρT_zero, bpcCallAt_ren
  [propext, Quot.sound].

### A4-U5 COST DELTA (measured, this unit's builds)

| | concrete form (BpcEquation, U4) | alloc layer (AllocEq, U5) |
|---|---|---|
| lines | 125 | 258 total: ~85 ONE-TIME (absRaftNode_ren + helpers + seed discharge), ~125 per-handler wrapper (equation + call-at + 2 projection lemmas + corollary + witness), ~48 docstring |
| module build | 110 s | 28 s |
| new axioms | — | none (same closure) |
| edits to existing modules | — | ZERO (aggregator import only) |

The wrapper's build cost is dominated by re-proving the two
projection kernel_rfl facts at the pinned placement (they were
inline in the concrete proof; now exposed as lemmas the transfer
consumes) — a future consolidation could re-derive the concrete
module FROM these lemmas and retire the duplication; not done here
(additive-only discipline, the concrete statements stay verbatim).

### A4-U5 VERDICT: **GO** — re-base the remaining four equations and all future waves on the allocation-symbolic form

Grounds (each measured or machine-checked above): (1) strict
generalization is PROVED, not argued — the concrete statement is a
corollary; (2) the marginal per-handler cost is ~125 wrapper lines +
~30 s, a fraction of any handler's own cost, and the one-time layer
is already paid; (3) zero new axioms, zero edits, no new trust
surface — a composition of two landed classics; (4) the layer-(C)
composition NEEDS this form anyway: the leaf fixtures sit at bases
0..k while the real twin's cells sit at base 389+ — the relocation
quantifier is the bridge, so re-basing is not decoration but the
path to consuming the equations at all. Prescription for the
re-base slices (successor's checklist): per handler, expose the two
projection facts as lemmas, state the `_alloc` form via
`stepFnIter_sim` + `absRaftNode_ren` (result-returning Ms handlers
additionally need result-CELL rename facts — same `lookup_some`
pattern), derive the `_of_alloc` corollary + witness; the
multi-window handlers (Bf, Bc) transfer their COMPOSED span exactly
as BPC's single window (the spine's output is one machine-level
span — the frame lift is span-shape-independent).

Honest boundary (none counted): (a) footprint layout SHAPE stays
concrete — `r` relocates, never reshapes (the §5 D-relative lever is
the shape fix; lineage recorded); (b) the fresh region is
canonical-sequential from `na` (`ShiftSpec`; further allocator
latitude is AllocIndep's quotient); (c) the witness instantiates at
the IDENTITY placement — a non-identity concrete instance needs a
generic `frameSim_relocate` builder the Frame layer lacks (its
non-identity instances today are rebaseSimT chains); non-identity
liveness of FrameSim itself is kit-witnessed (swapShift_spec, the
sort examples). (d) the four sibling equations are NOT re-based this
unit — verdict prescribes, does not execute.

### PROMOTION LEDGER updates (A4-U5)

- **`frameSim_relocate`** (ShiftSpec → FrameSim of the rename-image;
  Frame/-layer) — NEW row, two named consumers: non-identity
  witnesses for every handler's alloc equation; the layer-(C)
  instantiation of leaf-fixture equations at the twin's real layout
  (base 389+). Outside this unit's file boundary; not built.
- **`asU64_ren`/`fieldU64_ren`** — general-shaped, parked in
  AllocEq per the file boundary; lift beside `structFieldsLookup_ren`
  (Frame/HeapOps) at a consolidation slice.
- **`renameStmt_ρT_zero`** — generic identity-seed body discharge;
  belongs beside `renameStmt_id` (Frame/RenameId); kills the
  per-example `bodies_*` lemmas (ssort's `bodies_ρ16` pattern) on
  lift.
- `stepFn_pick_transport` lift (U4 row) — unchanged, still owed at
  the next consolidation slice.

## A4-U5 exit (2026-08-24, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the dispatch tip
14f37f20: 3 (5c75dcc9 design slice, 82d0b72c AllocEq module,
2e11a5c9 log/verdict) + this exit commit; no coordinator commits
interleaved (checked: `git log 14f37f20..HEAD` = the 3 above at
recount time).

Unit-end gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci`
at 2e11a5c9's tree — **RESULT: PASS, exit 0** (23 ok steps,
`artifacts/ci-arc4-u5.log`, gitignored; the two no-diff notes are
the sanctioned proofs+docs hatch — this unit touched
`proofs/GoLeanProofs/Specs/Raft/**` + the aggregator + arc-4 docs
only; no runtime code, no Corpus/, no baselines/, no Sym edits, no
Frame edits). Gate staggered behind a `free -g` guard per the
dispatch (witness wave sharing the box; 57G free at launch, cap
24G). The comparator-landmark staleness note (90 commits at this
run) stays flagged for the operator's merge step, as in every prior
arc-4 exit.

**Deliverable state vs the dispatch:**
1. Design slice — DELIVERED (design note §7, lineage-lined;
   composition answer: composes machine-level post-transport, no
   frame-aware Sym variant needed; §7.3b the Iris-preference ladder
   per the mid-unit [USER] directive, convergence notes recorded).
2. The refactor at ONE handler — DELIVERED
   (`becomePreCandidate_handler_eq_alloc` + `absRaftNode_ren` +
   `_of_alloc` corollary with binders/conclusion identical to the
   shipped concrete statement + §3.3 witness; cost delta measured:
   ~85 one-time + ~125 wrapper lines, 28 s vs the concrete module's
   110 s; axioms [propext, Classical.choice, Quot.sound], helpers
   [propext, Quot.sound]).
3. THE VERDICT — DELIVERED: **GO** (grounds + re-base prescription +
   honest boundary in the verdict section above).

**Open gaps carried (none counted):** all U4 gaps unchanged; U5 adds
the honest boundary items (layout-shape concreteness — the §5
D-relative lever; `frameSim_relocate` promotion row for non-identity
witnesses + layer-(C) instantiation at the twin's real layout; the
four sibling equations awaiting the prescribed re-base).

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1).

## A4-U6 — the four re-bases + the relocation lift (2026-08-24, same worker, coordinator-dispatched)

- 2026-08-24 SUCCESSOR RE-VERIFICATION (own U5 outputs, fresh probes,
  all PASS): tip f4d0a10e clean; full proofs+Audit green (485 jobs);
  U5 axiom probe re-run verbatim-matching (alloc/of_alloc/witness
  [propext, Classical.choice, Quot.sound]; absRaftNode_ren /
  renameStmt_ρT_zero / bpcCallAt_ren [propext, Quot.sound]); hatch
  grep over AllocEq: 0.
- 2026-08-24 **THE U6 FINDING (probe LocSupProbe2, decisive):** the
  twin's function bodies contain `locLit`s at EVERY static address
  0..30 (`funcListSup wBase.functions.toList = 31`; per-address bump
  probe: all of 0..30 referenced), and the U1–U4 fixtures sit at
  bases 0..23 ON that range. Since `Agrees` pins σ.functions to the
  twin table and `FrameSim.bodies_inv` forces `r` to fix every
  body-referenced address, **at the 0-based fixtures the
  allocation-symbolic `r`-quantifier is provably identity-only, and
  no `FrameSim` can carry a 0-based fixture equation to the twin's
  real layout (base 389+)** — the U5 verdict's layer-(C) bridge
  argument does not go through from THESE fixtures. The U5 theorems
  stand (never vacuous — identity+frame instances); their placement
  GENERALITY at 0-based fixtures is what collapses. Fix demonstrated
  this unit (BpcResite); charter consequence below.
- 2026-08-24 [AGENT] Plan adjusted WITHIN the dispatch: deliverable
  (1) proceeds at the current fixtures (the transfer machinery —
  absStorageEnts_ren etc. — is fixture-independent and survives any
  re-siting verbatim; the _alloc statements keep the quantified FORM
  so re-siting changes only the fixture constant); deliverable (2)'s
  non-identity witness is built at a RE-SITED BPC fixture (+31, off
  the static range) — at 0-based fixtures it is impossible, not
  merely unbuilt.
- 2026-08-24 Slice 1 (3e3adc38): **`Frame/Relocate.lean`** (81
  lines, 0.2 s) — the U5 promotion row taken (boundary extended to
  Frame/ for this lemma alone, coordinator-authorized, additive-only):
  `renameHeap`/`renameState`, the injective lookup transport
  (`renameHeap_lookup`, via the existing `renameLoc_beq`), and
  **`frameSim_relocate`** — ShiftSpec + allocator position + body
  invariance ⇒ `FrameSim` to the rename-image at the empty frame.
  Lineage: the SL renaming lemma (Yang–O'Hearn). Plus the survey's
  Frame-name disambiguation note (GoLean.Frame ≠ Iris ProofMode
  `Frame` class ≠ kit `wp_frame_*` call-frame laws).
- 2026-08-24 Slice 2 (21979995): **`AllocEqWave1.lean`** (536 lines,
  20 s) — the four re-bases, U5 pattern: `becomeFollower/
  becomeCandidate/msFirstIndex/msTerm_handler_eq_alloc` (placement-
  quantified; Bf/Bc over the choice prefix c₁..c₄ with the spine's
  post-states named; Ms in the result-returning form with result
  cells and storage abstraction read AT the placement r 21/r 22/r 6),
  each with `_of_alloc` (statement-identical identity corollary — the
  shipped four equations UNTOUCHED in their modules) and `_alloc_witness`.
  New one-time machinery: **`absStorageEnts_ren`** (recursive
  rename-invariance: slice base → backing array → entry cells →
  pointer-scalar derefs; helpers derefU64_ren/absEntry_ren/
  absEntsFrom_ren) and **`lookup_value_ren`** (loc-free result-cell
  transfer, [propext] only). [AGENT] simplification vs U5 logged:
  the alloc forms consume the shipped spans/projection lemmas
  directly — no per-handler CallAt defs (the statements carry
  `renameConfig r (γC ρ C0)`, collapsed by rfl at identity).
- 2026-08-24 Slice 3 (290ae7b3): **`BpcResite.lean`** (233 lines,
  ~125 s) — the re-sited fixture: every cell +31 (built by
  `Frame.renameValue` at the GoValue layer before `embedGo` — no
  Sym-side renamer needed), allocator 52. Probe first (`Bpc31Probe`):
  152 steps (unchanged), projections exact, γ-image == machine heap —
  re-siting is placement-transparent to the run. Landed:
  `bpc31_span` (one transported window), the LIVE
  `becomePreCandidate_handler_eq_alloc31`, its identity corollary,
  `wBase_funcSup = 31` (kernel fact, ZERO axioms) + `wBase_bodies_inv`
  (any r fixing [0,31) leaves every twin body invariant — the generic
  discharge for re-sited fixtures), and **THE NON-IDENTITY WITNESS**
  `becomePreCandidate_handler_eq_alloc31_witness_shifted`: the
  handler run at the `swap31_32` relocation — the raft cell
  genuinely at base 32, the `FrameSim` premise discharged concretely
  by `frameSim_relocate`. U5's honest-gap item (c) CLOSED.
- 2026-08-24 [USER] mid-unit survey directive received
  (`docs/2026-08-24_campaign-iris-reuse-map.md` §5d + shortlist,
  read): U6's relocation re-base confirmed no-analog-correct;
  the wave-2 charter below takes the survey's lens finding; the
  Frame-name disambiguation landed in Relocate's docstring (slice 1).

### A4-U6 numbers (measured this unit)

Full proofs+Audit green: **488 jobs** (485 + Relocate + AllocEqWave1
+ BpcResite). Hatch grep over all three new modules: 0. Fresh
`#print axioms` (capped probe, verbatim at the slice commits): all
12 handler `_alloc`/`_of_alloc`/`_alloc_witness` theorems +
`frameSim_relocate` + the three alloc31 theorems
[propext, Classical.choice, Quot.sound]; `absStorageEnts_ren`
[propext, Quot.sound]; `lookup_value_ren` [propext]; `wBase_funcSup`
**axiom-free**. Per-handler re-base marginal cost (measured): Bf ~75
lines, Bc ~70, Ms pair ~150 (incl. the result-cell form) — inside
the U5 projection; the four cost ONE module build of 20 s (the
shipped spans are consumed as opaque facts — zero window
re-evaluation).

### WAVE-2 CHARTER UPDATE (deliverable 3; binding on the message-handler waves)

1. **Symbolic from birth**: every wave-2+ handler equation is stated
   in the `_alloc` placement-quantified form from its first commit —
   the concrete form exists only as the identity corollary. No new
   0-based-pattern equations, ever.
2. **Fixtures born re-sited**: every new fixture's first cell sits at
   ≥ the static loc support (`funcListSup` = 31 at the current pin;
   recompute per pin move — `wBase_funcSup` is the tracked fact), so
   the placement quantifier is LIVE from birth. The generic
   `wBase_bodies_inv` is the bodies discharge; `frameSim_relocate`
   the witness seed. The U1–U4 0-based fixtures (Bf/Bc/Ms + the U5
   BPC) carry a RESIDUAL: re-site at a consolidation slice (regenerate
   literals at +31-shifted addresses; the `_alloc` statements change
   only in the fixture constant) — required before layer-(C) can
   consume their equations at the twin's real layout.
3. **The absState entries/outboxes extension (GAP-V1-1b/-3) is
   lens-shaped from birth** (survey §5d, adopted): field access in
   the extension (and in wave-2 equation conclusions) goes through a
   `StructAccess`-style focusing pattern — per-field access lemmas
   generated from the pinned lowering's struct table, instance/lemma
   search as the footprint search — instead of whole-struct
   offset-concrete reads. LINEAGE: Perennial's `Access`/`AccessStrict`
   field lenses (`deps/perennial new/golang/theory/mem.v:78-84`) +
   goose proofgen's generated per-field instances
   (`deps/goose/proofgen/tmpl/types.tmpl:65-77`; 76 instances for
   raftpb alone) — the ecosystem's answer to the 33-field `raft.raft`
   struct, no Iris dependency. Design slice owed at wave-2 kickoff
   (the seam's layer-(A) growth), sized S–M per the survey.
4. Choice-prefix and side-condition conventions unchanged (U3 form);
   the appendSpill transport and becomeLeader remain wave-2's opening
   machinery items (U4 exit list).

### PROMOTION LEDGER updates (A4-U6)

- `frameSim_relocate` — **TAKEN** (Frame/Relocate.lean; both named
  consumers now real: the shifted witness landed, layer-(C)
  instantiation pending fixture re-siting).
- `asU64_ren`/`fieldU64_ren`/`lookup_value_ren`/`absStorageEnts_ren`
  helpers — target-side rows unchanged (lift beside
  `structFieldsLookup_ren` at a consolidation slice; now 2 consumer
  modules).
- NEW: the 0-based fixture re-siting consolidation (charter item 2's
  residual) — consumers: every landed equation's layer-(C) use.
- `stepFn_pick_transport` lift (U4 row) — unchanged, still owed.

## A4-U6 exit (2026-08-24, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the U6 dispatch tip
f4d0a10e: 4 (3e3adc38 Relocate, 21979995 AllocEqWave1, 290ae7b3
BpcResite+aggregator, fc3eca45 log) + this exit commit; no
coordinator commits interleaved (checked at recount). Cumulative
U5+U6 on the branch since 14f37f20: 8 + this exit commit = 9
(count corrected in the follow-up commit: the first statement wrote
"9 + this" — restatement drift, lesson (i) again, caught at recount).

Unit-end gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci`
at fc3eca45's tree — **RESULT: PASS, exit 0** (23 ok steps,
`artifacts/ci-arc4-u6.log`, gitignored; the two no-diff notes are
the sanctioned proofs+docs hatch — this unit touched
`proofs/GoLeanProofs/{Frame/Relocate.lean,Specs/Raft/**}` + the
aggregator + arc-4 docs only; the Frame/ touch is the
coordinator-authorized promotion lift, additive-only, insertions-only
by diff stat). Gate staggered behind the `free -g` guard (41G free
at launch ≥ 24G cap). The comparator-landmark staleness note stays
flagged for the operator's merge step, as in every prior exit.

**Deliverable state vs the U6 dispatch:**
1. Four re-bases — DELIVERED (AllocEqWave1: the four `_alloc` forms,
   identity corollaries statement-identical to the shipped equations
   — which are untouched, diff-verified insertions-only — and
   witnesses; axioms probed verbatim at the slice entry).
2. `frameSim_relocate` — TAKEN (Frame/Relocate.lean, lineage-lined,
   additive-only) and the NON-identity witness LANDED
   (`becomePreCandidate_handler_eq_alloc31_witness_shifted`, raft
   cell at base 32 via swap31_32) — U5's honest gap closed, at the
   re-sited fixture the finding required.
3. Wave-2 charter — UPDATED (symbolic-from-birth; fixtures born
   re-sited above the static loc support; the absState
   entries/outboxes extension lens-shaped from birth with the
   Perennial Access/goose-proofgen lineage per survey §5d; the
   0-based-fixture re-siting consolidation residual named).

**Open gaps carried (none counted):** all U5 gaps as updated —
(a) layout-SHAPE concreteness unchanged (the lens charter item is
its wave-2 answer); (b) the non-identity witness gap CLOSED (this
unit); NEW: the U1–U5 0-based fixtures' re-siting consolidation
(required before layer-(C) consumption; the U6 finding's residual);
prior U4 residuals unchanged.

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1).

## A4-U7 — wave-2 kickoff: the lens design slice (2026-08-24, same worker, coordinator-dispatched)

- 2026-08-24 SUCCESSOR RE-VERIFICATION (own U6 outputs, fresh, all
  PASS): tip b1135520 clean; full proofs+Audit green (488 jobs); U6
  axiom probe re-run verbatim-matching (frameSim_relocate + the
  alloc31 trio [propext, Classical.choice, Quot.sound]); hatch grep
  over Relocate/AllocEqWave1/BpcResite: 0/0/0.
- 2026-08-24 [AGENT] SCOPE CALL under the active stop-at-clean-
  boundary rule: U7 delivers the DESIGN SLICE alone (dispatch item 1
  — sanctioned as a complete unit); item 2 (the 0-based fixture
  re-siting consolidation: Bf/Bc literal regeneration + Ms kernel
  facts — a heavy-build unit of its own) and item 3 (handleHeartbeat)
  are dispatched-forward as the design's slices C–E prerequisites and
  NOT attempted here. Honest boundary, not a completion claim.
- 2026-08-24 THE DESIGN SLICE landed
  (`docs/2026-08-24_campaign-arc4-lens-design.md`, commit above):
  the field-lens layer, LINEAGE-lined to Perennial's
  `Access`/`AccessStrict` (mem.v:78-130 read directly, the
  tac_wp_load/store consumption pattern included) + goose proofgen's
  generated per-field instances (types.tmpl:65-77 read directly).
  Core calls, each [AGENT]-logged in the note: first-order port as
  ONE reader-combinator set (fieldRead/fieldReadU64/fieldOfValue/
  sliceRead) + per-field LAW instances found by simp-set search (the
  search-failure-is-footprint-error behavior preserved; typeclasses
  rejected as unneeded synthesis); L1–L4 law families with L2
  (store-miss/frame half) named as the cost center and kill-point —
  its lever is the pilot ledger's parked normality-preservation row,
  now with its real consumer; GENERATED instances recommended
  (~150-line printer instrument probe-side, ~75 kernel-checked
  instances; hand route costed and rejected; folds the U4
  literal-printer promotion row's future); absState v2 plan
  (absRaftLog/absMessage/absOutbox) lens-consuming from birth so L4
  gives every new reader's placement transport for free.
- 2026-08-24 Contact probes BEFORE the plan froze (probe
  `LensContactProbe`, the U6 probe-first standard): `raftLog.unstable`
  is an EMBEDDED value field (one hop + `fieldOfValue`, not two
  cells); `unstable.entries : slice (*Entry)` + `offset : uint64`
  confirm the sliceRead plan; `raftpb.Message` = 14 fields, plainpb
  pointer-scalars + `Reject : *bool` + a RECURSIVE
  `Responses : slice (*Message)` — fuel/bound needed, wave-2 read
  census item, GAP-V2-1 designated if unread.
- Boundaries restated in the note §6: lens is proof infrastructure
  (general module imports machine vocabulary only); every shipped
  statement stays verbatim; the generator is an instrument whose
  deletion loses convenience, never soundness; fixture re-siting
  stays a separate unit.

## A4-U7 exit (2026-08-24, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the U7 dispatch tip
b1135520: 1 (the design-note commit) + this exit commit = 2; no
coordinator commits interleaved (checked at recount). This unit
touched arc-4 docs + gitignored probes ONLY — zero proof-code
changes (the U6-landed 488-job build re-verified green at entry).

Unit-end gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci`
— result recorded below in this entry's follow-up line per the
same-commit gate convention used at U5/U6 (gate runs at this tree).

**Deliverable state vs the U7 dispatch:** (1) DELIVERED (the design
note, contact-probed, lineage-lined, costed, kill-pointed);
(2) NOT ATTEMPTED (scope call above — the named heavy consolidation
unit); (3) NOT ATTEMPTED (blocked behind the design's slices A–D by
its own charter). Honest gaps, none counted.

**Open gaps carried (none counted):** all U6 gaps unchanged
(re-siting consolidation, layout-shape/lens as its wave-2 answer,
U4 residuals); U7 adds GAP-V2-1 (Responses projection) as a
DESIGNATED-if-unread census item.

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1).

- 2026-08-24 A4-U7 gate follow-up (as promised in the exit entry):
  `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the exit
  tree — **RESULT: PASS, exit 0** (23 ok steps,
  `artifacts/ci-arc4-u7.log`, gitignored; the two no-diff notes are
  the sanctioned docs-only hatch — this unit changed no proof code).
  Gate staggered behind the `free -g` guard (78G free ≥ 24G cap; the
  solo retry pass respected). The comparator-landmark staleness note
  stays flagged for the operator's merge step.

## A4-U8 — the lens build (design slices A–D) + the fixture re-siting consolidation (2026-08-24, successor worker)

- 2026-08-24 SUCCESSOR RE-VERIFICATION at the dispatch tip c649061b
  (tree clean, no interleaved commits). All fresh probes, all PASS:
  - capped core build green (58 jobs); capped proofs+Audit green
    (488 jobs — matching U6/U7's recorded count).
  - `#print axioms` (capped probe `artifacts/probe/AxProbeU8.lean`,
    verbatim): all five `_handler_eq_alloc` theorems
    (becomePreCandidate/becomeFollower/becomeCandidate/msFirstIndex/
    msTerm) AND `becomePreCandidate_handler_eq_alloc31_witness_shifted`
    = [propext, Classical.choice, Quot.sound] — matching U5/U6's
    records.
  - Kit pin recount: 24 total `GoLean.Sym` `#guard_msgs` pins in
    `proofs/Audit/Kit.lean` − 6 pre-existing = **18 extension pins**
    CONFIRMED (grep count 24 verified fresh).
  - hatch grep over `Sym/TableExt.lean` + `Sym/KernelRfl.lean` +
    `Frame/Relocate.lean` + `Specs/Raft/*.lean`: zero
    `sorry|native_decide|axiom ` (every file 0).
- 2026-08-24 U8 contact round BEFORE any code (probe `LensU8Probe`,
  U6 probe-first standard) — the pinned struct tables for every
  wave-2-relevant type, feeding the instance plan:
  - `raft.raft` (32 fields): Term/Vote/lead/id/leadTransferee/
    pendingConfIndex are DIRECT `.int .uint64` (no defined-type hop);
    `state` is `.defined raft.StateType` (→ `.int .uint64`, one
    resolution step); electionElapsed/heartbeatElapsed `.int .int`;
    `raftLog` `.pointer (.defined raft.raftLog)`; msgs/
    msgsAfterAppend/pendingReadIndexMessages
    `.slice (.pointer (.defined raftpb.Message))`.
  - `raft.raftLog`: committed/applying/applied direct `.int .uint64`;
    `unstable` EMBEDDED `.defined raft.unstable` (U7 contact
    confirmed); `storage` `.interface raft.Storage`.
  - `raft.unstable`: entries `.slice (.pointer raftpb.Entry)`,
    offset/offsetInProgress `.int .uint64`.
  - `raftpb.Entry`: Term/Index `.pointer (.int .uint64)` (plainpb),
    Type `.pointer (.defined raftpb.EntryType)`, Data
    `.slice (.int .uint8)`.
  - `raftpb.Message`: the 14 fields as U7 probed; `raftpb.MessageType`
    resolves to `.int .int32`; Reject `.pointer .bool`.
  - **THE L2 KILL-POINT PRE-CHECK, decisive from Ops.lean reading
    (not probed — the definition IS the fact): normalization at a
    defined struct type IS field-pointwise** (`normalizeStructValueWith`
    → `normalizeFieldsWith` walks (FieldDef, field) pairs
    independently, alignment-checked), and pointer/slice/bool/
    interface-typed fields normalize by the CATCH-ALL identity arm —
    so store-miss preservation decomposes exactly as the design
    predicted: `StructFields.set`-vs-lookup commutation +
    per-field normalization stability, with stability FREE for every
    non-scalar field. The kill-point is not expected to fire; slice B
    will confirm at the proofs.
- 2026-08-24 Slices A+B LANDED (`proofs/GoLeanProofs/Lens.lean`, one
  module, general layer — LINEAGE in the module docstring: Perennial
  `Access`/`AccessStrict` + goose proofgen per-field instances,
  first-order port; imports GoCore + Frame only, no Sym, no Specs):
  - **Combinators**: `readU64`/`readIntK`/`readBool` decoders,
    `fieldOfValue` (embedded-struct value reads), `fieldRead`,
    `fieldReadU64`, `sliceElems`/`sliceRead` (generalizes
    `absEntsFrom`), `fieldTy?`/`structFieldTy` (the instance layer's
    search key). [AGENT] nil-slice call logged in the docstring: a nil
    slice of len 0 reads as `some []` (Go's nil slice IS the empty
    slice; `r.msgs` at init) — nil with nonzero len stays `none`.
  - **L1** focus: `fieldOfValue_struct`/`fieldRead_of_cell`/
    `fieldRead_of_struct`.
  - **L4** rename transport: `fieldRead_ren` (value renamed),
    `fieldReadU64_ren` + `sliceRead_ren` (loc-free outputs transport
    VERBATIM) — the per-reader hand `_ren` pattern retired for
    lens-stated readers.
  - **L2/L3 (THE KILL-POINT DID NOT FIRE)**: `store_field_decomp`
    (the machine's field-store path — loadLoc → `StructFields.set` →
    base-store re-normalization at the declared type, fuel 1024→1023 —
    decomposed), `fieldRead_store_miss` (L2: f ≠ g preserved given
    per-field normalization stability), `fieldRead_store_hit` (L3:
    readback = normalization of the stored value).
    **`normalizeFieldsWith_lookup` IS the field-pointwise fact** —
    proved by induction over the FieldDef walk, so L2 covers ALL
    field shapes, not a scalar fragment. Supporting characterizations:
    `structFieldsLookup_eq`/`structFieldsSet_eq` (the Array
    fold/forIn loops re-expressed at the list level: `lookupL`/
    `setL`/`hasName`), `lookupL_setL_ne`/`_hit`.
  - **Per-field-TYPE shape lemmas** (what instances discharge
    stability with): `norm_pointer_id`/`norm_slice_id`/`norm_bool_id`/
    `norm_string_id`/`norm_interface_id` (identity arms — free),
    `norm_int_stable` (in-range = the hvote-style side condition)/
    `norm_int_hit`, `norm_defined_step`/`norm_alias_step` (one
    resolution step, for `raft.StateType`-shaped fields).
  - **Witnesses (§3.3)**: L1/slice/nil-slice/L4 on a concrete
    two-cell state (L4's FrameSim premise discharged live at
    `frameSim_seed`); L2+L3 on a REAL `storeLoc` at a typed cell
    (`lens_witness_store_ok` — with_unfolding_all rfl, #eval-checked
    first — + `lens_witness_L2L3`, every law premise discharged
    concretely, `rfl`/`decide` only).
  - Gotcha recorded: core ships NO `Except` ok/error-bind simp
    lemmas (the Frame layer's ExSim.bind sidesteps them) — landed as
    `rfl`-lemmas `ok_bind`/`error_bind`/`map_ok`/`map_error` in Lens;
    the do-block extractions use defeq `replace` + these.
  - Wired into the aggregator + `Audit/Kit.lean` (7 new Lens pins,
    build-enforced; Kit imports Lens). Full proofs+Audit green:
    **489 jobs** (488 + Lens). Fresh `#print axioms` (probe `AxLens`,
    verbatim): fieldRead_ren / fieldReadU64_ren / sliceRead_ren /
    normalizeFieldsWith_lookup / structFieldsSet_eq / lens_witness_L4
    [propext, Quot.sound]; store_field_decomp / fieldRead_store_miss /
    fieldRead_store_hit / lens_witness_L2L3
    [propext, Classical.choice, Quot.sound]. Hatch grep over
    Lens.lean: 0.
- 2026-08-24 Slice C LANDED (`Specs/Raft/LensInst.lean` — the target
  half; LINEAGE: goose proofgen generated per-field instances):
  **40 per-field declared-type facts + 7 per-type table facts + the
  one defined-scalar stability chain** (`raft.StateType` — every
  other wave-2 field is a direct int kind or an identity shape), each
  ONE kernel-checked line. Two [AGENT] calls logged in the module:
  - **Hand-written, generator NOT built** (the dispatch's
    "hand-write first"): the `fdsOf` PROJECTION trick (field-def
    arrays extracted from the pinned table, never literal copies)
    collapses each instance to a one-line kernel fact recomputed
    against the pin on every build — the generator's drift-alarm
    trust story with zero instrument code. At 40+7+2 the hand form is
    smaller than the generator. Revisit condition recorded (full 75+
    or per-field store forms).
  - **No custom simp attribute** (design §3 deviation): named-fact
    table serves the fail-loud footprint-search role at this count;
    revisit at wave-2 proof buildout.
  Scope: raft.raft message-handler fields (11), raftLog (5),
  unstable (3), MemoryStorage (3, callStats deliberately absent),
  raftpb.Entry (4), raftpb.Message (all 14 incl. the recursive
  Responses). tracker.Progress deliberately wave-3-absent.
  §3.3 witness `lensInst_witness` + `_store_ok`: the L2/L3 laws
  applied on the REAL pinned 32-field `raft.raft` default cell (a
  real `storeLoc` to Term; hit reads 5, miss preserves Vote; every
  premise from the instance table; probe `LensInstProbe` #eval'd
  first). Module elaborates in 6.4 s. Full proofs+Audit green:
  **490 jobs**. Hatch grep: 0.
- 2026-08-24 **GAP-V2-1 RESOLVED BY CENSUS** (recorded, not guessed):
  `grep -n Responses raftsubject/raft/*.go` — Responses is read ONLY
  by `util.go`'s printer and `rawnode.go`'s Ready/Advance plumbing
  (wave 3), NEVER by the wave-2 message handlers. So `absMessage`
  deliberately does not project it and needs NO fuel/structural
  bound; a wave-3 extension owes the fueled recursive form. NEW
  GAP-V2-2 designated alongside: `Snapshot : *raftpb.Snapshot`
  likewise unprojected (wave-2 handlers do not read it;
  handleSnapshot out of wave-2 scope). Handler read census also
  recorded: handleAppendEntries reads From/Index/LogTerm/Commit (+
  Entries via maybeAppend), handleHeartbeat From/Commit/Context.
- 2026-08-24 Slice D LANDED (`Specs/Raft/AbsStateV2.lean` — absState
  v2, lens-consuming from birth; v1 UNTOUCHED):
  - Readers: `absRaftLog` (**GAP-V1-1b CLOSED**: absStorageEnts (U4)
    through the storage interface via `ifaceBaseAddr` + the EMBEDDED
    unstable overlay via `fieldOfValue`/`sliceRead` + the three
    scalars; derived views `AbsLog.lastIndex`/`AbsLog.view`
    re-grounded from log_unstable.go/log.go with the snapshot branch
    recorded unprojected), `absMessage` (12 abstract fields; plainpb
    deref shims `derefBool`/`derefI32` beside U4's derefU64),
    `absOutbox` (**feeds GAP-V1-3**: msgs/msgsAfterAppend via
    sliceRead ∘ absMessage; nil outbox = empty list, the lens
    nil-slice arm).
  - **L4 transports BY COMPOSITION** — `absRaftLog_ren` /
    `absMessage_ren` / `absOutbox_ren` (+ derefBool/derefI32/
    ifaceBaseAddr/absUnstableV _ren): zero heap-walk re-derivation,
    only lens laws + the landed U6 `_ren` lemmas compose — the
    charter's symbolic-from-birth holds by construction. All three
    [propext, Quot.sound] (fresh probe `AxV2`, verbatim).
  - §3.3 witnesses (#eval-checked first, probe `AbsV2Probe`):
    absRaftLog on the U3 populated fixture `uσ` = some
    ⟨[(1,1)],[],2,1,1,1⟩ (lastIndex some 1); absOutbox "msgs" =
    some [] (nil-slice arm live); absMessage on the machine's default
    Message + one real Term cell = zeros/9/false/[]/[] (plainpb nil
    getters live); `absV2_witness_L4` consumes absRaftLog_ren at the
    zero-shift seed. Witness axioms [propext] / [propext, Quot.sound].
  - Full proofs+Audit green: **491 jobs**. Hatch grep: 0.
- 2026-08-24 **CHECKPOINT (recomputed; part-1 boundary):** worker
  commits since the dispatch tip c649061b: 3 (3a5215ab slices A+B,
  0b361e5c slice C, 28882054 slice D); no coordinator commits
  interleaved (checked at recount). Part 1 (the lens build,
  design slices A–D with L2 PROVED, not parked) is COMPLETE. Part 2
  (the fixture re-siting consolidation) begins.
- 2026-08-24 Part 2a — **MsResite.lean LANDED** (the Ms re-site,
  result-returning form). Probe FIRST (`Ms31Probe`): the `+31`-shifted
  Ms fixture (uniform `sh31` — the Ms happy path reads NO static
  cell) runs FirstIndex 178 / Term 246 steps, `.next .stop`, stream
  untouched, γ-image == machine heap, every projection/result exact
  at the shifted addresses (storage 37, results 52/53). Landed:
  the re-sited fixture + spans + per-conjunct kernel facts (the U4
  per-decl budget lesson respected) +
  **`msFirstIndex/msTerm_handler_eq_alloc31`** (PRIMARY,
  placement-quantified — LIVE at this fixture) + `_id` corollaries +
  §3.3 witnesses. Module elaborates in 336 s (≈ the 0-based
  MsEquation's 348 s). The Term error-branch residual is now cleanly
  separable (noted in the module: re-siting frees the `[0,31)` range
  for the true static error cells a future error-branch fixture
  needs). Shipped Ms statements untouched.
- 2026-08-24 Part 2b — **Bc31.lean + Bc31Lit.lean LANDED** (the BC
  re-site). Generator+validator probe FIRST (`Bc31Gen`, adapted from
  the U4 `BcLitGen` instrument — third consumer of the printer
  pattern): fixture `+31` with the TRUE STATICS 18/19 (globalRand,
  read by reset's Intn path through a body locLit) KEPT IN PLACE
  (`shBfc`); schedule VALIDATED identical (windows
  [686,183,28,28,28,3,2320]; Intn map allocates at 61, Progress map
  at 33); machine run END-TO-END: 3,282 steps, stream [3,1,0,0]
  consumed, γ-image == machine heap, projections == spec. `Bc31Lit`
  (527 KB) generated by the probe; the `bc31W*_out` links re-check
  it (the BfLit trust story). `Bc31.lean` = the full BC family
  (fixture + links + transported windows + 6 crossing facts +
  composed span) at the new placement, assembled from the shipped
  BC modules by mechanical renaming (bases 30→61, 2→33, receiver
  0→31; `bc31Cands3` = Progress 38/39/40; ALL shared pick machinery
  — uρ/uρ'/uKeys/uCands1/crossings/stepFn_pick_transport — reused
  verbatim), plus **`becomeCandidate_handler_eq_alloc31`** (PRIMARY)
  + `becomeCandidate_handler_eq31` (identity corollary) + witness.
  **Elaborated GREEN on the FIRST full check — 112 s** (vs the
  0-based family's ~110 s; re-siting is placement-transparent to
  build cost too). Shipped BC statements untouched.
- 2026-08-24 Part 2c — **Bf31.lean + Bf31Lit.lean LANDED** (the U3
  FLAGSHIP re-sited). Probe FIRST (`Bf31Gen`): schedule identical
  ([642,183,28,28,28,3,2316]; Intn map at 63 at this placement,
  Progress at 33), machine END-TO-END 3,234 steps / [3,1,0,0]
  consumed / γ-image == machine heap / projections == spec. `Bf31Lit`
  (508 KB) generated + link-checked. [AGENT] structure call, logged:
  Bf31 uses the SIMPLER slice-4 BC module pattern (one module,
  whole-step kernel_rfl STOP/SORT leaves) instead of the U3-era
  BfSteps/BfSteps2/BfSortStep ceremony — same theorem shapes, fewer
  moving parts; the 0-based Bf modules stay as landed history.
  `bc31Cands3` shared from Bc31 (same Progress placement). Landed:
  the chain + **`becomeFollower_handler_eq_alloc31`** (PRIMARY, with
  the hvote/hlead side conditions and the unrm-13/3 wrap collapse —
  depths PLACEMENT-INVARIANT, confirmed at elaboration) +
  `becomeFollower_handler_eq31` (identity corollary) + witness +
  **`becomeFollower_handler_eq_alloc31_witness_shifted`** (the
  flagship non-identity demonstration: raft cell genuinely at 32 via
  swap31_32/frameSim_relocate, NO closed re-evaluation — the span
  consumed as a proved fact). Elaboration 104 s (one fix round: a
  name-protection slip in the mechanical rename left `bc31Cands3_fact`
  colliding — renamed to `bf31Cands3_fact`; caught by the compiler,
  as designed). [AGENT] Shifted witnesses for Ms31/Bc31 NOT
  duplicated (logged): quantifier liveness at re-sited fixtures is
  demonstrated by the BPC31 (U6) and Bf31 (this unit) shifted
  witnesses through the same fixture-independent seed
  (`wBase_bodies_inv` + `frameSim_relocate`); repeating the ceremony
  per handler adds no information.
- 2026-08-24 Part 2 CLOSE-OUT numbers: full proofs+Audit green
  **496 jobs** (491 + MsResite + Bc31Lit + Bc31 + Bf31Lit + Bf31).
  Fresh `#print axioms` (probe `AxResite`, verbatim): ALL NINE of
  msFirstIndex/msTerm/becomeCandidate/becomeFollower
  `_handler_eq_alloc31` + their witnesses + the Bf31 shifted witness
  = [propext, Classical.choice, Quot.sound]. Hatch grep over all
  five new modules: 0/0/0/0/0. **The U6 charter's re-siting
  consolidation residual is CLOSED: every landed handler equation
  family (BPC at U6; Ms/BC/Bf this unit) now has a placement-LIVE
  `_alloc` form at a fixture off the static locLit range — layer-(C)
  can consume them at the twin's real layout (base 389+) via
  `frameSim_relocate`-seeded placements.** The 0-based statements
  remain untouched (shipped history; their identity-only quantifier
  limitation stays documented in the U6 finding).

### PROMOTION LEDGER updates (A4-U8)

- **The lens law families (L1–L4)** — LANDED as general kit surface
  (`GoLeanProofs/Lens.lean`, 7 Audit/Kit pins); consumers: absState
  v2 (landed), every wave-2 equation conclusion (charter).
- **The literal-generation printer** (U4 row) — now FOUR probe-side
  consumers (BfLitGen/BcLitGen/Bc31Gen/Bf31Gen). Still probe-side
  per the scratch conventions; the U7 design's "fold into one
  instrument" future remains open — but note slice C's finding cuts
  against a proof-code generator generally: the `fdsOf` projection
  trick delivered generated-trust with zero instrument code. Row
  kept, priority lowered ([AGENT]).
- `stepFn_pick_transport` lift (U4 row) — STILL OWED, with the
  reason recorded: the lift edits shipped `BfSteps.lean`/`TableExt`
  consumers, and this unit's binding conventions were zero-edits to
  shipped modules; needs a coordinator-authorized boundary touch like
  U6's Relocate lift. Now FOUR consumer modules (BfSteps, BcSteps,
  Bc31, Bf31 — the latter two via the same shared lemma).
- Retired as consumers land: the U6 "0-based fixture re-siting
  consolidation" row — DONE this unit.

## A4-U8 exit (2026-08-24, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the dispatch tip
c649061b: 6 (3a5215ab slices A+B, 0b361e5c slice C, 28882054 slice D,
3a68d6b6 parts 2a+2b, a4a1a824 part 2c, + this log/exit commit); no
coordinator commits interleaved (checked at recount:
`git log c649061b..HEAD` = the above).

**Deliverable state vs the U8 dispatch:**
1. THE LENS BUILD (design slices A–D) — **DELIVERED IN FULL**:
   - Slice A: `Lens.lean` combinators + L1 + L4 (general layer,
     lineage-lined, Kit-pinned).
   - Slice B: **L2/L3 PROVED — the kill-point did NOT fire**:
     normalization is field-pointwise BY PROOF
     (`normalizeFieldsWith_lookup`), store-miss/store-hit
     characterized against the real `storeLoc` path, stability FREE
     for non-scalar fields, witnesses on a real store.
   - Slice C: `LensInst.lean` — 40 per-field + 7 per-type kernel
     facts via the `fdsOf` projection trick; generator NOT built
     (hand-write-first call, measured grounds + revisit condition
     logged); no custom simp attr (deviation logged).
   - Slice D: `AbsStateV2.lean` — absRaftLog (GAP-V1-1b CLOSED),
     absMessage (GAP-V2-1 census-RESOLVED: no fuel needed, Responses
     deliberately unread; GAP-V2-2 designated for Snapshot),
     absOutbox (feeds GAP-V1-3); L4 transports BY COMPOSITION
     (zero hand heap-walk `_ren` derivations); witnesses on the
     populated fixture.
2. THE FIXTURE RE-SITING consolidation — **DELIVERED IN FULL**
   (parts 2a–2c: MsResite, Bc31(+Lit), Bf31(+Lit); every re-site
   probe-validated end-to-end BEFORE theorems; alloc31 forms PRIMARY
   with identity corollaries and witnesses; the Bf31 shifted
   non-identity witness; shipped 0-based statements untouched;
   builds staggered behind the free-memory guard throughout, caps
   20–24G).

**Handler-equation state after this unit:** every proved handler
family (BPC, Bf, Bc, MsFirstIndex, MsTerm) has BOTH its shipped
0-based record AND a placement-LIVE re-sited `_alloc31` form —
layer-(C)-consumable. absState now spans v1 scalars + storage ents +
the log view + messages + outboxes.

**Open gaps carried (none counted):** GAP-V1-2 (tracker), -4
(AbstractNet), -5 (by design) unchanged; GAP-U1-W1 unchanged;
GAP-V2-1 wave-3 fueled-Responses extension owed only if rawnode
plumbing needs it; GAP-V2-2 (Snapshot unprojected) new-designated;
U4 residuals unchanged (becomeLeader → wave 2 with the appendSpill
transport; MemoryStorage.Entries spec design; Term/FirstIndex error
branches — now cleanly separable at re-sited fixtures, noted in
MsResite); the lens design's slice E (handleHeartbeat) is A4-U9.

**A4-U9 CHARTER (proposed, per the dispatch):** the first
MESSAGE-HANDLER equation on the new machinery — handleHeartbeat,
symbolic-from-birth (design slice E): fixture BORN re-sited (≥31,
`wBase_funcSup` recomputed at any pin move), the `_alloc` form
PRIMARY from the first commit, conclusions stated through absState
v2 (`absRaftLog`/`absOutbox` readouts + the L2 store-miss laws for
"the handler did not touch X" without window re-evaluation — slice
E's measurable payoff target vs the MsEquation baseline), the
message argument projected by `absMessage`. Opening machinery items
(U4 exit list, unchanged): the appendSpill pick transport is NOT
needed for handleHeartbeat (commitTo + send only — no appendSlice
on this path; verify by probe first) but IS for handleAppendEntries
and becomeLeader next.

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1).

- 2026-08-24 A4-U8 gate follow-up (same-commit convention): unit-end
  gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the
  exit tree — **RESULT: PASS, exit 0** (23 ok steps,
  `artifacts/ci-arc4-u8.log`, gitignored; the two no-diff notes are
  the sanctioned proofs+docs hatch — this unit touched
  `proofs/GoLeanProofs/{Lens.lean,Specs/Raft/**}` + the aggregator +
  `proofs/Audit/Kit.lean` (additive pins) + arc-4 docs only; no
  runtime code, no Corpus/, no baselines/, zero edits to shipped
  Sym/Frame/Specs modules). Gate staggered behind the `free -g`
  guard (67G free ≥ 24G cap). **The comparator landmark note is now
  STALE-flagged by ci itself (106 commits > the 100 threshold since
  the last certified run @ 1730567a; report-only)** — escalated
  VISIBLY for the operator's merge step per the CLAUDE.md step-2
  widened trigger: a comparator-judge run belongs in the merge
  protocol for this branch.

## A4-U9 — handleHeartbeat: the probe census + the pick-transport lift (2026-08-24, same worker, coordinator-dispatched; STOP-AT-BOUNDARY rule active — census + lift is the sanctioned complete unit)

- 2026-08-24 SUCCESSOR RE-VERIFICATION (own U8 outputs, fresh, all
  PASS): tip 4880a22b clean; full proofs+Audit green (496 jobs);
  AxResite probe re-run verbatim-matching (all nine re-site theorems
  [propext, Classical.choice, Quot.sound]); hatch grep over
  Lens/AbsStateV2/Bf31: 0/0/0.
- 2026-08-24 **THE U9 CENSUS (probe `HhProbe`, static + dynamic,
  BEFORE any equation code — the U6 standard):**
  - STATIC (`raftsubject/raft/raft.go:1854-1857`, `log.go:commitTo`,
    `raft.go:send`): handleHeartbeat(m *pb.Message) =
    `commitTo(m.GetCommit())` (TWO branches: no-op when
    `committed ≥ tocommit`; commit-advance calls `lastIndex()` —
    the Bf-style dispatch/mutex/callStats chain — and panics past
    lastIndex) + `send(&Message{To: m.From, MsgHeartbeatResp.Enum(),
    Context})` which allocates `From := new(r.id)`,
    `Term := new(r.Term)` (HeartbeatResp is in neither the vote group
    nor Prop/ReadIndex), then — NOT being
    MsgAppResp/MsgVoteResp/MsgPreVoteResp — takes
    **`r.msgs = append(r.msgs, m)`: an appendSlice site**.
  - DYNAMIC (born-re-sited fixture: the bf31-pattern heap at
    scalars 7/2/0/5 + a Message argument cell at 52 with Commit→1,
    From→2, nil Context; drained caller shape
    `retV (.addr 52) (callArgsK handleHeartbeat [] [.addr 31])`):
    **completes in 1,325 steps consuming EXACTLY ONE choice** —
    na 55→129 (74 fresh cells). **THE APPENDSPILL QUESTION IS
    ANSWERED AGAINST THE DISPATCH'S EXPECTATION: the append on the
    NIL outbox still consumes one spill choice — the appendSpill
    transport (U3-verdict residual 3) is REQUIRED for handleHeartbeat
    itself**, not deferrable to handleAppendEntries; now TRIPLY
    motivated (handleHeartbeat + handleAppendEntries + becomeLeader).
  - **absState v2 projects the handler END-TO-END on its first real
    contact**: post `absOutbox σ' ⟨31⟩ "msgs" = some [⟨9(=MsgHeartbeatResp),
    2(=m.From), 1(=r.id), 0(=r.Term), …, reject false, [], []⟩]`;
    `absRaftLog` committed 1 (the NO-OP commitTo branch at this
    fixture — m.Commit = committed = 1; the ADVANCE branch needs a
    fixture with lastIndex > committed: a SECOND fixture family,
    U3's term-branch pattern); `absMessage` reads the argument
    exactly.
  - Footprint field-set (the lens instances this equation consumes):
    raft.raft id/Term/raftLog/msgs (+ L2 store-miss for the untouched
    fields at the msgs write-back); raftLog committed (no-op branch);
    Message Commit/From/Context/To/Type/Term.
- 2026-08-24 **THE PICK-TRANSPORT LIFT TAKEN**
  (`Sym/PickTransport.lean`, the U4 promotion row, coordinator-
  authorized additive touch — the U6 Relocate precedent): the
  raft-independent `stepFn_pick_transport` lifted VERBATIM into
  `GoLean.Sym` (lineage-lined: choice-site path splitting =
  stepFn_pick_generic ∘ alloc_conc), Kit-pinned
  ([propext, Quot.sound], build-enforced — pin count now 19 + the
  7 Lens pins). `BfSteps.lean` keeps its copy as shipped history —
  ZERO edits to shipped modules; four consumer modules at lift time.
- 2026-08-24 [AGENT] STOP-AT-BOUNDARY call: the equation itself is
  dispatched forward — its ONE missing prerequisite is now precisely
  known (the appendSpill analogue of `stepFn_pick_transport`: the
  spill-choice step form at `Stmt`-level append, same lever shape),
  and building it mid-unit past the context boundary would violate
  the active stop rule. The A4-U10 charter below is the census's
  direct product.

**A4-U10 CHARTER (proposed):** (1) the appendSpill transport in
`Sym/PickTransport.lean`'s pattern (general, kit-pinned; probe the
spill site's exact step/choice shape first — the U4 becomeLeader
trace at steps 5171/6352 and this unit's 1,325-step trace are the
two witnesses); (2) THE handleHeartbeat EQUATION, symbolic-from-birth
per the U8 exit charter: born-re-sited fixture (this unit's probe
fixture IS the recipe), `_alloc` primary, conclusions through
absState v2 (`absOutbox`/`absRaftLog`/`absMessage`) + the L2
store-miss laws — and MEASURE the lens payoff vs the MsEquation
per-conjunct baseline (the dispatch's named metric); the no-op
commitTo branch first, the advance branch as the second fixture
family; (3) then handleAppendEntries opens on the same transport.

## A4-U9 exit (2026-08-24, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the U9 dispatch
(= the U8 exit tip 4880a22b): 1 (the census+lift commit) + this log
commit; no coordinator commits interleaved (checked at recount).
Unit tree: `Sym/PickTransport.lean` (additive) + aggregator + Kit
(additive pin) + probes + this log — zero edits to shipped modules.
Full proofs+Audit green: **497 jobs**. Gate record follows in the
next entry (same-commit convention).

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1); the comparator-landmark STALE flag
(106+ commits) stands escalated from U8.

- 2026-08-24 A4-U9 gate follow-up (same-commit convention): unit-end
  gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the
  exit tree — **RESULT: PASS, exit 0** (23 ok steps,
  `artifacts/ci-arc4-u9.log`, gitignored; the two no-diff notes are
  the sanctioned proofs+docs hatch). Gate staggered behind the
  `free -g` guard (56G free ≥ 24G cap). The comparator-landmark
  STALE flag stands escalated for the operator's merge step.

## A4-U10 — the appendSpill transport + THE handleHeartbeat equation (2026-08-24, successor worker, coordinator-dispatched)

- 2026-08-24 SUCCESSOR RE-VERIFICATION (U9's top claims, fresh
  probes, all PASS):
  - tip clean: `git status` = "nothing to commit, working tree
    clean" on branch `campaign-arc4`; `git rev-parse HEAD` =
    `55be64c6378cd38822a13de02722de46ecdccd10` (the dispatch tip).
  - full capped proofs+Audit build (`GOLEAN_MEM_MAX=48G
    scripts/capped lake build` in `proofs/`): "Build completed
    successfully (497 jobs)." — exit 0, matching U9's recorded 497.
  - `Sym/PickTransport.lean` present (72 lines, the lifted
    `stepFn_pick_transport`); its Kit pin at `proofs/Audit/Kit.lean:720`
    reads `[propext, Quot.sound]` and is `#guard_msgs`-build-enforced —
    verbatim-verified by the green build above.
  - hatch grep (`sorry|native_decide|axiom ` filtered of docstring
    "axioms" mentions) over PickTransport/TableExt/KernelRfl/Lens +
    `Specs/Raft/*.lean`: **0**.
  - free-memory guard at build launch: 100G available ≥ 40G floor.
- 2026-08-24 [USER] Mid-unit doctrine update (coordinator-relayed,
  campaign-operational immediately): **the anti-grinding doctrine** —
  brute kernel reduction of giant terms as a substitute for
  abstraction is banned; any single build approaching ~1 hour is a
  smell whose default response is STOP AND DECOMPOSE (lemma-level
  composition over monolithic kernel_rfl; the stop is a clean unit
  boundary). Long build-out of many small well-abstracted units stays
  fine. Also relayed: the arc-2 segment wave is PARKED under this
  doctrine; CompletionWitness becomes a ROUND-REPLAY corollary of
  layer C (cert = the recorded choice stream at round granularity) —
  layer C carries T1's ∃-side too; nothing changes inside U10, but
  the round-induction interfaces should keep that corollary in mind.
  U10 compliance note: the plan is two Sym-transported windows +
  one one-step crossing + lens-law conclusions, all minutes-scale;
  literalization (the U4 lever) keeps every downstream fact off the
  re-evaluation path.
- 2026-08-24 Orientation reading for the unit (recorded): U9 census
  entry + charter; seam design §4b/§4c; lens design (esp. §2 L-laws,
  §5 slice E); `Sym/PickTransport.lean` (the pattern to match);
  `SliceMem.lean` Group 4 (**the append-spill machinery ALREADY
  LANDED at machine level**: `applyStmtOp_append1_spill` — spill
  apply at a `some`-base old slice, capacity-generic premises —
  plus `buildAppendBackingValue_of_norm` and the
  `appendRealizedCap` envelope algebra; WP-arc lift, sealed API);
  the machine's spill arm (`Machine.lean` `applyStmtOp`
  `.appendSlice`, `Choices.consumeAt .appendSpill`, width =
  `appendSpillWidth`); the mirror's quit (`Mirror.lean`
  `applyStmtOp'` → `quit .q3Choice` on the spill branch — the
  designed Q3 window boundary, so the pre-window ends AT the spill
  apply config); `Bf31.lean` end-to-end (the module pattern);
  `Valuation.cells` (Domain.lean — whole-CELL atoms, whose docstring
  names the append-backing declared type `.array n …` as the DESIGN
  CASE for cell-level valuation: the extra-dependent backing cell
  enters the post fixture as ONE cell atom, so ONE post-window
  literal serves every consumed choice — the §4(ii) collapse at the
  spill site).
- 2026-08-24 U10 probe round (probes `HhU10Probe{,2,3,4}.lean`,
  BEFORE any theorem — the U6 standard; every number below from
  these runs):
  - **The spill's exact shape** (machine, U9 fixture): spill at step
    index **1299** of 1,325; config `.retV (.slice ⟨some 124,0,1,1⟩)
    (.stmtOpK (.appendSlice *raftpb.Message) 1 [.slice ⟨none,0,0,0⟩,
    .addr 125] [])` — the append TARGET is the TEMP cell 125 (`$c1220`),
    NOT the raft field: the `r.msgs` field write-back is a plain
    assign inside the 25-step POST-window (so the whole-struct
    re-normalization sits IN-WINDOW — the L2 store-miss law is not
    needed on this handler's crossing; honest finding below). Width
    32 confirmed (nil outbox: envelope [1,32]); realized caps probed
    at c=0/5/31 → 4/9/3 = `appendRealizedCap 0 1 (c%32)` exactly;
    backing = [msgPtr(74)] ++ nil-padding at declared type
    `.array nc *Message` — the extra-dependent declared type, the
    `Valuation.cells` design case verbatim.
  - **Two same-lever TableExt residuals exposed by the window walk**
    (the designed consume-on-demand process, U3 precedent — [AGENT]:
    def growth turns quits into steps, never changes stepping
    behavior; the full downstream rebuild re-checking every landed
    window kernel_rfl is the built-in guard, and it came back green):
    (1) `Stmt.initialization` at a DEFINED type (the `raftpb.Message`
    temp `$c1191` in `send`) — new `stepFnT` arm over the landed
    `defaultValueT` + conc case; (2) result-cell allocation at a
    DEFINED result type (`raftpb.MessageType` on the
    `Message.GetType` entry) — `allocDeclsT` + conc lemma, threaded
    through `enterFrameT` (bisect probe: findFunctionIn?/dispatch/
    bindParams all OK individually; the quit was `allocDecls'`'s
    shipped default-former). After both: **the mirror pre-window runs
    1299 steps and quits `.q3Choice` at exactly the spill config**;
    γ-heap/na/config vs machine at 1299: all equal.
  - **The atom-carried crossing validated end-to-end** (probe 4): S2
    := S1 + cell 125 ↦ value-atom 0 + fresh cell 126 ↦ CELL-atom 0
    (na 127); post-window from (S2, .next k') = **25 steps to
    `.next .stop` on ONE literal**; γ-image == machine final heap AND
    na at c=0/3/31, exactly one choice consumed; projections at the
    γ-image: absOutbox = [⟨9,2,1,0,…,false,[],[]⟩], committed 1,
    Vote 7, absMessage(arg) = ⟨0,0,2,0,0,0,1,…⟩ — U9's census record
    reproduced at the symbolic level.
  - [AGENT] **From-symbolism REFUTED at zero crossings** (generator
    probe finding): with `m.From` symbolic (var 5) the pre-window
    quits `.q1Branch` at step 1259 on `eqI(norm²(x₅), 1)` — the
    subject's own SELF-ADDRESSED panic guard (`send`,
    raft.go:601-ish: the response's To = m.From's value compared to
    r.id). A symbolic From therefore needs one branch crossing with
    side condition `m.From ≠ r.id` (the subject's real precondition)
    — recorded as the follow-on refinement; THIS unit pins m.From = 2
    concrete (the U9 recipe, the charter's fixture family). Raft
    scalars Vote/lead/state/leadTransferee STAY symbolic (vars 1–4,
    the bf31 pattern) — the symbolic pre-window then runs 1299 clean.
- 2026-08-24 Slice 1 LANDED (a9f7a4a2): **THE APPEND-SPILL
  TRANSPORT** — `Sym/SpillTransport.lean` (184 lines):
  `applyStmtOp_append1_spill_at` (the SliceMem Group-4 walk at the
  SINGLE realized capacity, Option-base old handle — the nil outbox;
  `nt` free), **`stepFn_appendSpill_transport`** (the γ-level spill
  step: mirror config in, machine conclusion, post state = a given
  mirror image carrying the choice-dependent artifacts as valuation
  atoms; LINEAGE: choice-point transport in the
  symbolic-execution-by-conservative-extension frame, same classic as
  `stepFn_pick_transport`, realized over the SliceMem machinery), and
  the §3.3 in-module witness (nil []uint64 grown by one element,
  every premise discharged concretely; #eval-checked first in probe
  3). Kit-pinned (3 new pins, build-enforced): transport + `_at` +
  witness all **[propext, Quot.sound]**. Plus the two TableExt arms
  above. Full proofs+Audit green **498 jobs**.
- 2026-08-24 Slice 2 LANDED — **THE handleHeartbeat EQUATION, the
  first message-handler equation** (`Specs/Raft/HhLit.lean` generated
  1,096 lines / 118 KB by probe `HhGen.lean` — the printer's 5th
  consumer, atom arms added — + `Specs/Raft/HhEquation.lean` 430
  lines):
  - Chain: fixture BORN RE-SITED symbolic-from-birth (bf31 heap,
    vars 1–4 + the Message argument cells; charter items 1–2), TWO
    windows [1299, 25] + ONE spill crossing = **1,325 steps, one
    choice consumed** — U9's census exactly. Link theorems
    `hhW1_out`/`hhW2_out` (kernel rfl) re-check the literals — the
    drift alarms; `hhρ'` absorbs the choice (value-atom 0 = the
    spilled handle, cell-atom 0 = the backing cell — ONE post-window
    literal for all 32 capacities, zero per-choice case splits).
  - The crossing `hh_spill_step` = `stepFn_appendSpill_transport`
    with: hvisE/hvisO/htgt by `kernel_rfl` at free ρ/c₁ (the target
    is the plain temp cell 125 — no struct re-normalization on the
    crossing), hcons by `Choices.consume` reduction, hbuild by the
    LANDED `buildAppendBackingValue_of_norm` + `appendRealizedCap_lower`
    (choice-GENERIC — no leaf enumeration).
  - Conclusions through absState v2 + the Lens readers, NINE
    conjuncts: absMessage(argument) pre; absRaftLog pre = post =
    `hhAbsLog` (the NO-OP commitTo branch — the log view PRESERVED);
    **absOutbox post = [specHeartbeatResp 1 2 0]** (typ 9, dst =
    m.From, src = r.id, term = r.Term — re-grounded from
    raft.go:1854-1857 + send); fieldReadU64 Vote/lead = ρ.ints 1/2
    (the untouched symbolic scalars, hvote/hlead range side
    conditions collapsing the store-time norm-wrap, depth 1 probed)
    + Term = 0. The outbox readout is proved by LEMMA COMPOSITION
    over the lens combinators (`sliceElems` is array-index-bounded,
    so the choice-generic backing cannot close by reduction —
    `hhBackingVal_head` + bind-of-some; the anti-grinding doctrine's
    preferred shape).
  - **`handleHeartbeat_handler_eq_alloc` PRIMARY**
    (placement-quantified via `stepFnIter_sim`; all nine conclusions
    transported by the L4 `_ren` lemmas — one line each, zero heap
    re-derivation) + `handleHeartbeat_handler_eq` (identity
    corollary) + the §3.3 witness (Vote 7/lead 2/state 0/ldT 5,
    stream [3] — realized capacity 7). Fresh `#print axioms`
    (verbatim, probe `AxHh`): eq_alloc / eq / witness / hh_full_span
    / hh_spill_step all [propext, Classical.choice, Quot.sound];
    hh_post_absOutbox / hhW1_out [propext, Quot.sound].
  - Full proofs+Audit green **500 jobs**; hatch grep over
    SpillTransport/HhLit/HhEquation: 0/0/0. HhEquation module
    elaborates in **41 s** (lake-reported).

### THE LENS-PAYOFF MEASURE (deliverable 3 — the dispatch's named metric)

Derivation anchors: MsEquation's recorded 348 s for a 246-step
handler whose per-conjunct facts each re-evaluate the window in the
kernel (U4 log entry; ≈5 window-evaluating decls ⇒ ~70 s/conjunct ⇒
~0.28 s/step per FACT); this unit's HhEquation 41 s lake-reported
with window step-counts pinned by the link theorems (1299 + 25).

- **Baseline (the MsEquation per-conjunct pattern) projected at this
  handler**: 8 projection/readout conjuncts × ~0.28 s/step × 1,325
  steps ≈ **49 min** of kernel work, O(k · window).
- **Measured (absState v2 + literals + lens laws)**: **41 s** for the
  WHOLE module — the two window links evaluated ONCE (~35 s of it)
  plus sub-second per-conjunct reductions against the `hhS3` literal
  and the lemma-composed outbox readout — O(window + k), the lens
  design §2's payoff formula, met at ≈ **70×** on the conclusion
  layer.
- Attribution, honest: the O(window+k) shape is literalization (U4's
  lever) + the lens together. The lens's specific contributions
  here: (a) the v2 READERS are what make all nine conclusions
  stateable; (b) the choice-generic outbox readout NEEDS the
  lemma-composition route (a reduction-only route would be 32 leaf
  facts per conclusion); (c) the L4 `_ren` family gave the alloc
  form's placement transport of every conclusion in one line each.
  **The L2 store-miss law was NOT needed on this handler** (honest
  finding): the spill writes a temp cell and the `r.msgs` field
  write-back sits in-window, so untouched-field facts reduce against
  the literal; L2's designed consumer materializes only where no
  post-literal exists (∀-state equations, future fixture-free forms).
- Per-handler cost, cumulative: ~430 hand lines + 118 KB generated +
  ~2 min of builds (HhLit 1.5 s + HhEquation 41 s + probes) — vs
  bf31's 847 lines/104 s for the 4-choice reset family. The
  ONE-TIME general machinery this unit: SpillTransport 184 lines +
  two TableExt arms (~90 lines incl. conc cases).

- 2026-08-24 Deliverable 4 — **handleAppendEntries PROBE CENSUS**
  (probe `HaeProbe.lean`, U9 style, census ONLY — no equation; every
  number from the run):
  - STATIC (raft.go:1810-1854): three branches — (1) STALE
    (`a.prev.index < committed` → resp Index = committed), (2)
    SUCCESS (`maybeAppend ok` → resp Index = mlastIndex), (3) REJECT
    (`findConflictByTerm` hint + Reject/RejectHint/LogTerm resp).
    `send` routes MsgAppResp (typ 4) to **`msgsAfterAppend`** (the
    async-storage group), NOT `msgs`.
  - DYNAMIC (SUCCESS branch, EMPTY entries, matching prev: the Hh
    fixture + LogTerm→cell 55 = 1, Index→cell 56 = 1; drained call at
    the born-re-sited heap): completes in **2,828 steps consuming
    EXACTLY ONE choice** (step index 2798 — the `msgsAfterAppend`
    appendSlice SPILL on the nil outbox, operand shape IDENTICAL to
    Hh's: temp target cell, nil old handle, one-element elems slice;
    width 32); post-window **29 steps**; na 57→229. Projections:
    msgsAfterAppend = [⟨4, 2(=m.From), 1(=r.id), 0, 0, 1(=mlastIndex),
    0, …, reject false, [], []⟩], msgs = [], committed = 1 (m.Commit
    = committed — no advance).
  - **THE MIRROR RUNS 2,798 STEPS CLEAN TO THE SPILL QUIT with the
    slice-1 arms — ZERO new machinery for this family's equation**:
    the whole maybeAppend chain (logSliceFromMsgApp construction,
    term-matching through the Storage dispatch + mutex + callStats,
    commitTo) is in-window on landed classes. The equation is Hh's
    exact shape (pre-window + the SAME spill transport + post-window)
    at a different fixture — assembly, est. ≤ half a session.
  - Remaining fixture families recorded (none attempted): the STALE
    branch (cheapest), NON-EMPTY entries (the real log append — a
    SECOND spill family into the raftLog entries + GAP-V1-1b's
    unstable overlay actually exercised), the REJECT branch
    (findConflictByTerm loop — choice-free but window-heavy), and
    commit-ADVANCE (shared with Hh's second family).

### PROMOTION LEDGER updates (A4-U10)

- **The append-spill transport** (`Sym/SpillTransport.lean`) —
  LANDED as general kit surface (3 Kit pins, [propext, Quot.sound]);
  consumers: handleHeartbeat (landed), handleAppendEntries (census:
  identical shape), becomeLeader (U4's measured 2-spill path). A
  MULTI-ELEMENT append variant is future work on its first consumer.
- **The literal-generation printer** — FIFTH consumer (`HhGen`), and
  the printer grew the ATOM arms (`Value.atom`/`HeapCell.atom` with
  `Nat` ascriptions). Row unchanged (probe-side per scratch
  conventions; the U8 priority-lowering stands).
- TableExt same-lever residual arms consumed on demand this unit:
  `Stmt.initialization`-at-defined + `allocDeclsT` (the U3 process —
  window quits guide, conc lemmas ship in the same edit, downstream
  kernel_rfl re-checks are the guard).

## A4-U10 exit (2026-08-24, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the dispatch tip
55be64c6: 3 (a9f7a4a2 slice 1, c8bd4053 slice 2, + this log/exit
commit); no coordinator commits interleaved (checked at recount:
`git log 55be64c6..HEAD --oneline` = the above). Full proofs+Audit
green: **500 jobs** (497 at entry + SpillTransport + HhLit +
HhEquation). Hatch grep over SpillTransport/HhLit/HhEquation:
0/0/0. Kit pins: +3 (the spill-transport trio, build-enforced).

**Deliverable state vs the U10 charter:**
1. THE APPEND-SPILL TRANSPORT — **DELIVERED** (slice 1: probe-first
   shape extraction from both witnesses; `stepFn_appendSpill_transport`
   + `applyStmtOp_append1_spill_at` + in-module §3.3 witness, general
   Go-language machinery over the landed SliceMem Group-4 walk,
   lineage-lined, Kit-pinned [propext, Quot.sound]; zero edits to
   shipped Sym STATEMENTS — the two TableExt def-growth arms follow
   the U3 consume-on-demand precedent with conc cases and green
   downstream re-checks).
2. THE handleHeartbeat EQUATION — **DELIVERED** (slice 2:
   `handleHeartbeat_handler_eq_alloc` PRIMARY, symbolic-from-birth at
   a born-re-sited fixture, the ONE consumed choice quantified (∀
   streams `c₁ :: ch`) and absorbed by valuation atoms, conclusions
   through absState v2 + the lens readers, identity corollary +
   witness; the no-op commitTo branch as chartered — the
   commit-advance family recorded as the follow-on, PLUS the new
   probe-found follow-on: message-field symbolism needs one branch
   crossing with the subject's own `m.From ≠ r.id` precondition).
3. THE MEASURE — **DELIVERED** (the lens-payoff section above:
   41 s measured vs ~49 min projected on the MsEquation per-conjunct
   baseline, ≈70×, O(window+k) vs O(k·window), with honest
   attribution: literalization+lens jointly; L2 NOT needed on this
   handler — finding recorded).
4. handleAppendEntries — **CENSUS DELIVERED** (probe-only as
   chartered: 2,828 steps / ONE choice / the SAME spill shape /
   mirror clean to the quit with zero new machinery; equation =
   assembly at a new fixture).

**Open gaps carried (none counted):** all U9 gaps unchanged
(GAP-V1-2/-4/-5, GAP-U1-W1, GAP-V2-1 wave-3 condition, GAP-V2-2,
Ms error branches, MemoryStorage.Entries spec design); U10 adds:
the handleHeartbeat commit-ADVANCE fixture family; the
message-field-symbolism branch crossing (`m.From ≠ r.id` side
condition); the multi-element spill-transport variant; the four
handleAppendEntries fixture families above; becomeLeader (now
unblocked — the spill transport was its last named machinery item).

**A4-U11 CHARTER (proposed):** (1) THE handleAppendEntries EQUATION,
success/empty-entries family — assembly on the landed transport at
the census fixture (born re-sited, `_alloc` primary, absState-v2
conclusions incl. the `msgsAfterAppend` outbox; ≤ half a session
projected); then (2) the STALE-branch family (cheapest second
family, exercises the branch-crossing pattern at concrete values);
then (3) EITHER becomeLeader (6 choices: the reset spine + 2 spills
— all transports now landed) OR the non-empty-entries append family
(the log-write path, exercises GAP-V1-1b's unstable overlay) —
coordinator's pick; the anti-grinding doctrine's stop-and-decompose
applies to any window that balloons.

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1); the comparator-landmark STALE flag
stands escalated from U8/U9.

- 2026-08-24 A4-U10 gate follow-up (same-commit convention): unit-end
  gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the
  exit tree — **RESULT: PASS, exit 0** (22 ok steps,
  `artifacts/ci-arc4-u10.log`, gitignored; the two no-diff notes are
  the sanctioned proofs+docs hatch — this unit touched
  `proofs/GoLeanProofs/{Sym/{TableExt,SpillTransport}.lean,Specs/Raft/{HhLit,HhEquation}.lean}`
  + the aggregator + `proofs/Audit/Kit.lean` (additive pins) + arc-4
  docs + gitignored probes only; no runtime code, no Corpus/, no
  baselines/). Gate staggered behind the `free -g` guard (105G free ≥
  24G cap). The comparator-landmark note now reads **STALE at 112
  commits** (> the 100 threshold; report-only) — stands escalated for
  the operator's merge step, as at U8/U9.

## A4-U11 — the handleAppendEntries equation + the stale/log-append censuses (2026-08-25, same worker, coordinator-dispatched; third slot decided by the coordinator: the log-append family over becomeLeader)

- 2026-08-25 SUCCESSOR RE-VERIFICATION (own U10 outputs, fresh, all
  PASS): tip 91b7dc04 clean; full capped proofs+Audit fresh build
  green (**500 jobs**); the three SpillTransport Kit pins verbatim
  `[propext, Quot.sound]` (grep of the `#guard_msgs` block,
  build-enforced by the green build); hatch grep over
  SpillTransport/HhEquation/HhLit: 0/0/0; free-memory guard at
  launch: 120G available.
- 2026-08-25 Deliverable 1, slice A — generator `HaeGen.lean` (the
  printer's 6th consumer): the born-re-sited SUCCESS/EMPTY-ENTRIES
  fixture (bf31 heap vars 1–4 + Message cells 52–56; LogTerm/Index
  = 1 = matching prev; From = 2 concrete per the U10 finding).
  Validated before any theorem: pre-window **2798** clean to the
  spill quit, post-window **29** to `.next .stop` on ONE atom-carried
  literal, γ==machine at c=0/3/31, response-message cell probed at
  **183** (the one placement-specific constant vs Hh), outbox
  records exact (`msgsAfterAppend` = [⟨4,2,1,0,0,1,…⟩]; `msgs` = []).
  `HaeLit.lean` generated (3,789 lines; atom printers now emit
  `(… : Nat)` ascriptions — the U10 gotcha folded back).
- 2026-08-25 Deliverable 1, slice B — **THE handleAppendEntries
  EQUATION LANDED** (`HaeEquation.lean`, 438 lines):
  `handleAppendEntries_handler_eq_alloc` PRIMARY + identity
  corollary + §3.3 witness, TEN conclusions through absState v2 +
  the lens readers (argument `absMessage` incl. LogTerm/Index;
  `absRaftLog` pre = post = `hhAbsLog` — the log view preserved,
  EMPTY-entries family; **`absOutbox "msgsAfterAppend"` =
  `[specAppResp 1 2 0 1]`** — typ 4, dst m.From, src r.id, term 0,
  Index = mlastIndex; **`absOutbox "msgs"` = []** — the async-group
  routing made a CONCLUSION; Vote/lead/Term readouts). Module
  elaborates in **66 s**; axioms the classical trio
  (helpers/`haeW1_out` [propext, Quot.sound]; fresh probe `AxHae`,
  verbatim). Plus **`span_relocate`** — the `stepFnIter_sim`/`ok_inv`
  plumbing packaged ONCE at opaque states (0.8 s; every future
  handler's alloc form applies it instead of inlining the sim
  elimination; promotion row below).
- 2026-08-25 [AGENT] **THE ELABORATOR-MISMATCH PATHOLOGY (found the
  hard way, ~2 h of bisection; what-this-taught-us):** the first
  HaeEquation draft hung >37 min at 14.5 GB. Bisection (T1..T20
  probes; three of my sliced probe files were themselves malformed —
  a second lesson: python-sliced probe files must be diffed before
  their timings are believed) isolated the true cause: a STALE STEP
  COUNT — `stepFnIter_sim … 1325` (copied from Hh) against `hrun` at
  2828. The elaborator, failing unification of
  `stepFnIter 1325 σ …` vs `stepFnIter 2828 σ …`, fell into
  WHNF-UNFOLDING BOTH machine spines (thousands of steps) instead of
  failing fast — `debug.skipKernelTC` proved it elaborator-side; the
  fix was one number. LESSONS, now conventions: (a) an
  argument-count mismatch between two large-reduction terms produces
  a HANG, not an error — on any unexplained elaboration hang, check
  the NUMERIC ARGUMENTS of sim/window applications FIRST; (b) the
  per-handler sim plumbing is now `span_relocate` (n shared by
  construction, so this class cannot recur); (c) window links and
  crossings were all individually fast (T1 47 s, T2 64 s) — the
  scale itself was never the problem.
- 2026-08-25 Deliverable 2 — **STALE-branch census DELIVERED**
  (probe `StaleProbe.lean`; equation NOT attempted, boundary call
  below): m.Index = 0 < committed: **1,336 steps, ONE choice** (the
  same msgsAfterAppend spill at step 1307, post-window 28), mirror
  clean to the quit — zero new machinery; resp = ⟨4,2,1,0,0,
  index=committed=1,…⟩ (numerically identical to the success
  record AT THIS FIXTURE since mlastIndex = committed = 1 — a
  successor picking distinct fixture values would make the two
  families' responses observably different; noted).
- 2026-08-25 Deliverable 3 — **LOG-APPEND census DELIVERED WITH THE
  RISK FINDING** (probes `LaProbe{,2}.lean`; fixture: one entry
  (index 2, term 1) after matching prev): the machine goes **STUCK at
  step 2689 — `unbound GoCore heap location: base 25`**: the entry
  walk (`findConflict`/`term(2)` past lastIndex) takes the ERROR
  branch, which dereferences a package-level error variable
  (`deref (locLit 25) : interface error`) — body-table census: static
  25 is referenced by `$pkginit`, `raftLog.{term,slice,
  zeroTermOnOutOfBounds}` and `MemoryStorage.{Entries,Term}` (=
  the `ErrCompacted` comparison family). **The U4 Ms-census
  error-var residual, first bite on a wave-2 path**: the leaf
  fixtures carry no static [20,31) cells (only globalRand 18/19),
  so ANY log-append equation needs a fixture extended with the true
  static error cells (`$pkginit`'s images — reconstructible by
  running the twin's init and dumping [20,31), the MsResite note's
  predicted shape). The unstable overlay itself (GAP-V1-1b) was NOT
  reached — the wobble is BEFORE it, at fixture completeness; the
  mirror quit q11Internal mirrors the machine's stuck (fail-closed,
  correct). What-this-taught-us: wave-2's REAL fixture debt is the
  static-cell complement, not the overlay machinery.
- 2026-08-25 [AGENT] BOUNDARY CALL (the dispatch's own rotation
  guidance): deliverable 2's EQUATION (pure assembly, censused,
  zero new machinery) and 3's equation (blocked on the static-cell
  fixture extension) are handed to the successor; landing (1) solid
  + both censuses + the two findings beats a rushed (2). Token
  position at the call: ~730k of the 600–900k line.

### PROMOTION LEDGER updates (A4-U11)

- **`span_relocate`** (currently `HaeEquation.lean`, target layer) —
  general Frame-level plumbing, ONE consumer landed; second consumer
  = every next handler's alloc form (stale-family equation is the
  immediate one); lift to `Frame/Relocate.lean` beside
  `frameSim_relocate` at the next consolidation slice
  (coordinator-authorized boundary, U6 precedent). Retrofit option
  recorded: Hh/Bf31/Bc31 alloc proofs could consume it, shipped
  statements untouched.
- The literal printer — 6th consumer; the atom-ascription fix now
  lives in `HhGen`/`HaeGen` both.

## A4-U11 exit (2026-08-25, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the dispatch tip
91b7dc04: this unit's slice commit + this log commit (recount at
commit time); no coordinator commits interleaved. Full proofs+Audit
green: **502 jobs** (500 + HaeLit + HaeEquation). Hatch grep over
HaeLit/HaeEquation: 0/0. No new Kit pins owed (target-layer modules;
the spill-transport pins stand).

**Deliverable state vs the U11 dispatch:**
1. THE handleAppendEntries EQUATION (success/empty family) —
   **DELIVERED** (alloc PRIMARY + corollary + witness, ten
   absState-v2/lens conclusions incl. the msgsAfterAppend routing;
   66 s module; classical-trio axioms; `span_relocate` packaged).
2. STALE-branch family — **CENSUS DELIVERED**, equation handed
   forward (pure assembly; the fixture-value note above).
3. LOG-APPEND family — **CENSUS DELIVERED WITH THE RISK FINDING**
   (the static error-cell fixture debt at base 25; the overlay
   not reached; probe-first honored — no equation attempted).

**Open gaps carried (none counted):** all U10 gaps unchanged; U11
adds: the static-cell fixture complement for error-branch families
(cells [20,31) from `$pkginit` — blocks log-append AND the U4 Ms
error branches, same debt); the stale-family equation (assembly);
the U11 fixture-value note (pick distinct committed/mlastIndex for
observably-different family records).

**A4-U12 CHARTER (proposed):** (1) the STALE-family equation
(assembly on the landed pipeline; consider committed = 2 fixtures so
stale/success records differ observably); (2) THE STATIC-CELL
COMPLEMENT: reconstruct `$pkginit`'s [20,31) images (run the twin
init, dump, add to the born-re-sited fixture recipe as a shared
`hhStatics` block), then re-census the log-append family — if clean,
its equation (the unstable overlay's first real exercise, GAP-V1-1b);
(3) then becomeLeader (all transports landed) or the commit-advance
family. `span_relocate` lift to Frame/ at the first consolidation
slice.

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1); the comparator-landmark STALE flag
stands escalated.

- 2026-08-25 A4-U11 gate follow-up (same-commit convention): unit-end
  gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the
  exit tree — **RESULT: PASS, exit 0** (`artifacts/ci-arc4-u11.log`,
  gitignored, tail-12 capture: the final ok steps + the two
  sanctioned no-diff notes + RESULT; the full-run PASS is the exit
  code — this unit touched
  `proofs/GoLeanProofs/Specs/Raft/{HaeLit,HaeEquation}.lean` + the
  aggregator + arc-4 docs + gitignored probes only; no runtime code,
  no Corpus/, no baselines/, no edits to shipped modules). Gate
  staggered behind the `free -g` guard (119G available ≥ 24G cap).
  The comparator-landmark STALE flag stands escalated for the
  operator's merge step.

## A4-U12 — the stale-family equation + THE STATIC-CELL COMPLEMENT (2026-08-25, successor worker, coordinator-dispatched)

- 2026-08-25 SUCCESSOR RE-VERIFICATION (U11's top claims, fresh
  probes, all PASS):
  - tip clean: `git status` = "nothing to commit, working tree clean"
    on branch `campaign-arc4`; tip = eeceef6f (the dispatch tip),
    93G free at launch (≥ 40G floor).
  - fresh capped proofs+Audit build (`GOLEAN_MEM_MAX=48G
    scripts/capped lake build` in `proofs/`): "Build completed
    successfully (502 jobs)." exit 0 — matching U11's recorded 502.
  - `#print axioms` fresh probe (`AxHae`, capped, verbatim): all of
    handleAppendEntries_handler_eq_alloc / _eq / _witness /
    hae_full_span / hae_spill_step / span_relocate =
    [propext, Classical.choice, Quot.sound]; haeW1_out
    [propext, Quot.sound] — matching U11's record.
  - hatch grep over HaeEquation/HaeLit: 0/0.
- 2026-08-25 Slice 0 — **THE `span_relocate` LIFT TAKEN**
  (`Frame/Relocate.lean`, the U11 promotion row, coordinator-
  authorized additive touch — the U6/U9 precedent): lifted VERBATIM
  into `GoLean.Frame` beside `frameSim_relocate` (LINEAGE: the
  Yang–O'Hearn SL frame-lift plumbing, packaged; the U11
  elaborator-pathology guard — `n` shared by construction — restated
  in the docstring), Kit-pinned
  ([propext, Classical.choice, Quot.sound], build-enforced;
  `Audit/Kit.lean` additive import + pin). `HaeEquation.lean` keeps
  its RaftSeam copy as shipped history — ZERO edits to shipped
  modules. Consumers at lift time: HaeEquation (landed copy) + the
  stale-family equation (this unit, slice 1). Full proofs+Audit
  green: 502 jobs.
- 2026-08-25 Slice 1 — **THE handleAppendEntries STALE-FAMILY
  EQUATION LANDED** (`StaleEquation.lean` 466 lines + generated
  `StaleLit.lean` 1,740 lines; probes `StaleProbe3.lean` census +
  `StaleGen.lean` generator — the printer's 7th consumer — BOTH
  before any theorem):
  - [AGENT] Fixture call, the U11 fixture-value note taken with a
    CONSISTENCY upgrade: not a bare committed bump but a TWO-ENTRY
    log (storage ents (1,1),(2,1); committed = lastIndex = 2;
    applied = applying = 2; unstable empty at offset 3) — a
    consistent raft state, audit-proof against the
    "fixture violates committed ≤ lastIndex" objection a naive
    committed=2-over-a-1-entry-log fixture would draw. The message
    cells are the Hae SUCCESS fixture's VERBATIM (From 2, LogTerm 1,
    Index 1, Commit 1): `prev.index = 1 < committed = 2` → STALE.
    The family pair now exhibits the handler branching on STATE with
    observably distinct records: **stale resp Index = committed = 2
    vs the landed success record's Index = mlastIndex = 1**.
  - Census at the new fixture (StaleProbe3): **1,336 steps, ONE
    choice at step 1307** (same counts as U11's census at the
    one-entry fixture — the step schedule is fixture-value-invariant
    on this branch), mirror clean to the `q3Choice` spill quit,
    post-window 28; spill operands: elems cell 134 (element = the
    response message at cell 93), temp target 135, backing born at
    136 (na 136→137 at the crossing).
  - Generator validated end-to-end before emission: γ==machine at
    c=0/3/31 (heapEq/naEq true), pre-quit γ-agreement, projections
    exact (msgsAfterAppend = [⟨4,2,1,0,0,2,…⟩], msgs = [],
    absRaftLog pre = post = ⟨[(1,1),(2,1)],[],3,2,2,2⟩). One
    generator fix round: the first run exposed my temp-cell/message-
    cell conflation (135 vs 93) via the built-in elems-cell check —
    the validation working as designed.
  - The equation: `handleAppendEntries_stale_eq_alloc` PRIMARY +
    identity corollary + §3.3 witness, TEN conclusions through
    absState v2 + the lens readers (absMessage the Hae record
    verbatim; absRaftLog pre = post = `staleAbsLog` — the stale
    branch touches NOTHING, `maybeAppend` never runs;
    **`absOutbox "msgsAfterAppend"` = `[specAppResp 1 2 0 2]`** —
    Index = committed; msgs = []; Vote/lead/Term readouts).
    **Consumes the LIFTED `Frame.span_relocate` — its second
    consumer, as the promotion row predicted.** Module elaborates in
    **47 s** (windows [1307, 28] kernel-linked once). Fresh
    `#print axioms` (probe `AxStale`, verbatim): all five theorems +
    Frame.span_relocate [propext, Classical.choice, Quot.sound];
    staleW1_out [propext, Quot.sound]. Full proofs+Audit green:
    **504 jobs** (502 + StaleLit + StaleEquation); hatch grep 0/0.
  - What-this-taught-us (slice 1): the "pure assembly" projection
    held exactly — zero new machinery, one session-hour of work, and
    the only defect the pipeline caught was a transcription slip
    (135/93) caught by the generator's own validation print. The
    per-family marginal cost of a censused branch on a landed spill
    shape is now: one probe + one generator run + a rename pass.
- 2026-08-25 Slice 2 — **THE STATIC-CELL COMPLEMENT LANDED**
  (`Specs/Raft/StaticCells.lean`, 228 lines; contact probe
  `StaticsProbe.lean` FIRST — all numbers from its runs):
  - Contact (the $pkginit dump): the twin seeds **31 globals at
    cells [0,31), nextAddr 31**; init runs **1,382 machine steps,
    consumes ZERO choices**, ends at heap = 98 cells, nextAddr 98.
    The [20,31) roots decode as: 20 errBreak, 21 ErrStepLocalMsg,
    22 ErrStepPeerNotFound, 23 ErrCompacted, 24 ErrSnapOutOfDate,
    **25 ErrUnavailable — the U11 stuck cell** (`term(i > lastIndex)`
    returns it; `zeroTermOnOutOfBounds` compares 23 and 25),
    26 ErrSnapshotTemporarilyUnavailable, 27/28 two 23-entry
    message-type bool tables, 29 the harness-logger pointer, 30 a
    package bool. Error payloads (`raft.goleanShimErrorString`) at
    71/75/79/83/87/91/95 + harnessLogger at 97 — closure-complete
    (roots reference ONLY these eight; payloads reference nothing;
    probe phase B2/D).
  - [AGENT] Placement decision, recorded in the module: **ZERO
    renaming** — the payload addresses (all ≥ 71) sit ABOVE the
    born-re-sited leaf range [31,~60], so the block ships at
    $pkginit's exact addresses and consumers set nextAddr₀ = 98
    (`staticComplementNa`). The rejected alternative (re-siting
    payloads into [0,18)) would alias OTHER real statics (enum-name
    maps, loggers, ErrStopped/ErrProposalDropped at 16/17) for any
    future printer/step-path consumer; the true-address block is
    collision-free for EVERY consumer and meets the real twin state
    address-for-address at the layer-C connection.
  - Trust story (the fdsOf projection trick at heap level, kernel
    grade): `staticComplement` is a generated literal, and
    **`staticComplement_link` (kernel_rfl) recomputes the whole
    extraction — seed + the 1,382-step init run + the 19 lookups —
    against the PIN on every build**; `staticComplementNa_link` pins
    the post-init allocator (98) the same way. Module builds in
    **213 s** (two links, each replaying init in the kernel —
    anti-grinding pre-checked by probe `StaticLinkT` before landing:
    the link is one window-link's cost class, measured). Fail-closed:
    extraction is `none` on init failure or any missing cell; block
    insufficiency for a path stucks the machine and fails the
    consumer's own window links. Reachability stays GAP-U1-W1,
    recorded not claimed.
- 2026-08-25 Slice 2b — **THE LOG-APPEND RE-CENSUS: THE STUCK CLEARS
  AND THE OVERLAY DOES NOT BITE** (probe `LaProbe3.lean`; the U11
  fixture + the block, nextAddr 98 — THE UNIT'S HEADLINE ANSWER):
  - The machine run **COMPLETES: 4,828 steps, TWO choices** (step
    3573 = the `unstable.entries` append spill — the log write;
    step 4798 = the `msgsAfterAppend` response spill), na 98→393,
    `.next .stop`. U11's stuck at step 2689/cell 25 is GONE — the
    static-cell complement was the whole debt, as diagnosed.
  - **GAP-V1-1b's overlay reader is LIVE and EXACT on its first
    real exercise**: absRaftLog post = ⟨stable [(1,1)], unstableEnts
    [(2,1)], offset 2, committed 1, applying 1, applied 1⟩;
    `AbsLog.view` = [(1,1),(2,1)], lastIndex = some 2. The open seam
    question is ANSWERED: the unstable overlay projects cleanly —
    no reader change, no new machinery. Response =
    ⟨4,2,1,0,0,index=2(=mlastIndex),…⟩ into msgsAfterAppend;
    msgs = []; committed unchanged (m.Commit = 1 = committed).
  - The mirror runs **3,573 steps CLEAN to the first spill quit**
    (q3Choice at appendSlice-of-*Entry — the same one-element
    nil-base spill shape the landed transport covers; the whole
    error-branch walk INCLUDING the static-cell derefs is on landed
    TableExt classes). The equation is a THREE-window/TWO-crossing
    assembly on the landed spine — in scope for slice 3.
  - What-this-taught-us (slice 2): the wave-2 fixture debt really
    was COMPLETENESS, not machinery — with the true init images in
    place, the "hard" log-append path is the same assembly as every
    landed family, and the overlay reader built at U8 was right the
    first time. Also: $pkginit's placement geometry (payloads above
    the leaf range) made the zero-rename block possible — worth
    checking BEFORE designing a rename layer, not after.
- 2026-08-25 Slice 3 — **THE handleAppendEntries LOG-APPEND EQUATION
  LANDED** (`LaEquation.lean` 593 lines + generated `LaLit.lean`
  12,765 lines / 931 KB by probe `LaGen.lean` — the printer's 8th
  consumer): the first equation through the REAL log-write path, the
  first TWO-choice message-handler equation, GAP-V1-1b's overlay
  exercised, and the static-cell complement's first consumer.
  - **THE MIRROR-LEVEL FINDING FIRST (the honest sequence):** the
    naive Hae-shaped chain (two windows, two spill crossings) FAILED
    at the mirror — window 2 quit **q10Atom after 83 steps**:
    `StrictOp.lengthOf` applied to the atom-carried spilled handle,
    i.e. `len(u.entries)` re-read INSIDE the window. This is the
    first contact of the U10 atom-absorption pattern with an
    in-window RE-READ of the absorbed value — the pattern's implicit
    assumption (spilled handle never re-read before the span ends),
    which held for Hh/Hae's outbox appends, does NOT hold for a
    log write. Diagnosis by probe (crossAtoms walker): EXACTLY ONE
    atom read on the whole path, then 1,140 clean steps to spill 2.
  - **THE RESOLUTION IS LANDED-KIT COMPOSITION, zero new machinery**
    (the FURTHER-CONSUMERS doctrine's best case): the read's result
    is choice-INDEPENDENT (the spilled slice has len 1 at EVERY
    realized capacity — only cap varies), so the crossing is
    `stepFn_strict_apply` (StepKit) ∘ `applyStrictOp_len_slice`
    (SliceMem) with the cap bound from `appendRealizedCap_lower` —
    all three lemmas landed long before this unit. `la_len_step`
    axioms: [propext, Quot.sound].
  - The chain: windows **[3573, 83, 1140, 29]** + spill crossing 1
    (atoms 0: the `unstable.entries` append — elems = the message's
    OWN Entries array cell 57, element = entry cell 58, backing born
    at 324) + the length crossing + spill crossing 2 (atoms 1: the
    response — msg cell 347, backing at 390) = **4,828 steps, TWO
    choices** (∀ streams `c₁ :: c₂ :: ch`), composed by
    `stepFnIter_window_pick_window` + `stepFnIter_chain`/`_one`.
    Generator validated BEFORE any theorem: γ==machine at
    (c₁,c₂) = (0,0)/(3,5)/(31,31), schedule totals exact.
  - Conclusions (TEN, absState v2 + lens): absMessage pre WITH the
    entry (`entries = [(2,1)]` — the absMessage Entries reader's
    first live use); **absRaftLog pre = hhAbsLog, post =
    `laAbsLogPost` = ⟨[(1,1)], [(2,1)], 2, 1, 1, 1⟩ — the unstable
    overlay GROWN by exactly the appended entry**; the axiom-FREE
    spec-side `la_log_grew` (view post = view pre ++ [(2,1)],
    lastIndex 1→2, stable/committed untouched); absOutbox
    msgsAfterAppend = [specAppResp 1 2 0 2] (Index = mlastIndex =
    2; numerically equal to the stale record's — different
    PROVENANCE, distinguished by the log conclusions: overlay grown
    here vs untouched there — noted for honesty); msgs = [];
    Vote/lead/Term readouts. Alloc PRIMARY consumes the lifted
    `Frame.span_relocate` (third consumer) + identity corollary at
    `ρT 98` + §3.3 witness (stream [3, 5] — capacities 7/9).
  - **GREEN ON THE FIRST FULL CHECK: 113 s module** (LaLit 5.9 s);
    fresh `#print axioms` (probe `AxLa`, verbatim): the equation
    family + spans + spill crossings [propext, Classical.choice,
    Quot.sound]; la_len_step/laW1_out/staticComplement_link
    [propext, Quot.sound]; la_log_grew NO axioms. Full proofs+Audit
    green **507 jobs** (505 + LaLit + LaEquation); hatch grep over
    LaEquation/LaLit/StaticCells: 0.
  - What-this-taught-us (slice 3, the unit's second headline): the
    atom-absorption pattern has a NAMED limit — in-window re-reads
    of the absorbed value — and its first instance was dischargeable
    by pure kit composition because the re-read's RESULT was
    choice-independent. The next instance may not be (a re-read of
    the CAP, e.g. a subsequent append into the spilled slice, IS
    choice-dependent): that is the recorded watch-item for
    becomeLeader's 2-spill path and any multi-append handler —
    check the census for cap-consuming reads between spills before
    assuming the Hae shape.

### PROMOTION LEDGER updates (A4-U12)

- **`span_relocate`** — LIFTED to `Frame/Relocate.lean` (slice 0,
  the U11 row taken; Kit pin [propext, Classical.choice,
  Quot.sound]); consumers: HaeEquation (shipped copy, history),
  StaleEquation + LaEquation (the lifted form). Row CLOSED.
- **THE STATIC-CELL COMPLEMENT** (`Specs/Raft/StaticCells.lean`) —
  new shared fixture surface (target layer): consumers landed:
  LaEquation (first); owed consumers: the U4 Ms error-branch
  families, every future error-path fixture. The kernel link is the
  drift alarm on any wire-pin move.
- The literal printer — 7th and 8th consumers (StaleGen, LaGen);
  row otherwise unchanged (probe-side per scratch conventions).
- NEW ROW: **atom-read crossings** — the `la_len_step` shape (a
  strict-op step over an atom-carried operand whose γ-image makes
  the result choice-independent) is two landed lemmas composed; if
  a THIRD instance appears (first candidates: becomeLeader's
  inter-spill segment, the commit-advance family), consider a
  packaged `stepFn_atomRead_transport` in Sym/ (same terms as the
  pick/spill transports). Not built now — two instances of the
  COMPOSITION do not yet justify a wrapper.

## A4-U12 exit (2026-08-25, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the dispatch tip
eeceef6f: 4 (521fd94c slice 0, 53f55fbc slice 1, 60969eee slice 2,
441fe48c slice 3) + this log/exit commit; no coordinator commits
interleaved (checked at recount: `git log eeceef6f..HEAD --oneline` =
the above). Full proofs+Audit green: **507 jobs** (502 at entry +
StaleLit + StaleEquation + StaticCells + LaLit + LaEquation). Kit
pins: +1 (`Frame.span_relocate`, build-enforced). Hatch grep over
every new module (StaleEquation/StaleLit/StaticCells/LaEquation/
LaLit + the Relocate addition): 0.

**Deliverable state vs the U12 charter:**
1. THE STALE-FAMILY EQUATION — **DELIVERED** (slice 1:
   `handleAppendEntries_stale_eq_alloc` PRIMARY + corollary +
   witness; the U11 fixture-value note taken as a CONSISTENT
   two-entry log, committed = lastIndex = 2; the family pair now
   branches on STATE with observably distinct records — stale resp
   Index = committed = 2 vs success Index = 1; 47 s module;
   second consumer of the lifted span_relocate).
2. THE STATIC-CELL COMPLEMENT — **DELIVERED AS SHARED MACHINERY**
   (slice 2: `StaticCells.lean`; $pkginit's [20,31) images + payload
   referents at TRUE addresses, zero renaming, nextAddr₀ = 98;
   kernel-linked to the pin on every build — the 1,382-step init
   replayed inside `staticComplement_link`; general to every
   error-branch consumer: log-append landed, the U4 Ms error
   branches owed).
3. THE LOG-APPEND RE-CENSUS + EQUATION — **DELIVERED, BOTH** (the
   charter's conditional both ways: census CLEAN → equation landed):
   the stuck cleared; **THE VERDICT: the unstable overlay does NOT
   bite at the projection layer** (absRaftLog/view exact on first
   exercise) **and the mirror-level atom-absorption limit it DID
   expose** (`len(u.entries)` re-read → q10Atom) **was discharged by
   landed-kit composition with zero new machinery**
   (`handleAppendEntries_logAppend_eq_alloc`: 4,828 steps, TWO
   choices, ten conclusions incl. the overlay-grown log view and
   the axiom-free `la_log_grew`; 113 s module, green first check).
4. Third slot (commit-advance / becomeLeader) — NOT attempted
   ([AGENT] boundary call: the unit landed charter items 1–3 in
   full including the conditional equation; stopping at the clean
   branch-complete boundary beats opening a fourth census at
   ~430k tokens — split discipline).
Plus slice 0: the `span_relocate` lift (the U11 promotion row,
coordinator-authorized; Kit-pinned; U11's elaborator-pathology guard
restated at the lifted site).

**Handler-equation state after this unit:** handleAppendEntries now
has THREE proved families (success/empty at U11, stale + log-append
this unit) — every branch of the handler except REJECT; the overlay,
the static error cells, the two-choice span shape, and the
atom-re-read crossing are all exercised and recorded.

**Open gaps carried (none counted):** GAP-V1-2/-4/-5, GAP-U1-W1,
GAP-V2-1 wave-3 condition, GAP-V2-2, MemoryStorage.Entries spec
design — all unchanged; the U4 Ms ERROR branches now UNBLOCKED (the
complement is their named debt; owed consumer); U10's residuals
unchanged (Hh commit-advance family; message-field symbolism branch
crossing; multi-element spill variant); U12 adds: the REJECT branch
(findConflictByTerm loop — choice-free but window-heavy, the last
handleAppendEntries family); the atom-re-read WATCH-ITEM (a
cap-consuming re-read between spills would NOT be choice-independent
— check becomeLeader's census for it before assuming the shape); the
stale/log-append responses are numerically equal records at these
fixtures (Index 2 both, different provenance — distinguished by the
log conclusions; a fixture with committed ≠ mlastIndex + non-empty
entries would separate them, noted for any future record-level
argument).

**A4-U13 CHARTER (proposed):** (1) becomeLeader — census FIRST (the
U4 trace: 6,466 steps / 6 choices — the reset spine's 4 picks + 2
appendSpills; check the inter-spill segments for cap-consuming
atom re-reads, the U12 watch-item; all transports landed if reads
are len-shaped or absent); its equation closes the last wave-2
becomeX handler. (2) The handleHeartbeat commit-advance family
(cheap second: the Hh fixture with lastIndex > committed — shared
machinery all landed; closes handleHeartbeat completely). (3) If
budget remains: EITHER the handleAppendEntries REJECT family
(closing that handler completely) OR the U4 Ms error branches on
the complement (its second consumer; also cheap) — censused cost
decides. The `stepFn_atomRead_transport` wrapper only on a third
composition instance (ledger row).

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1); the comparator-landmark STALE flag
stands escalated from U8–U11.

- 2026-08-25 A4-U12 gate follow-up (same-commit convention): unit-end
  gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the
  exit tree — **RESULT: PASS, exit 0** (`artifacts/ci-arc4-u12.log`,
  gitignored; 22 ok steps + the two sanctioned no-diff notes — this
  unit touched `proofs/GoLeanProofs/{Frame/Relocate.lean,
  Specs/Raft/{StaleLit,StaleEquation,StaticCells,LaLit,LaEquation}.lean}`
  + the aggregator + `proofs/Audit/Kit.lean` (additive import + pin)
  + arc-4 docs + gitignored probes only; no runtime code, no
  Corpus/, no baselines/, zero edits to shipped module STATEMENTS).
  Gate staggered behind the `free -g` guard (100G free ≥ 24G cap).
  The comparator-landmark note now reads **STALE at 120 commits**
  (> the 100 threshold; report-only) — stands escalated for the
  operator's merge step, as at U8–U11.

## A4-U13 — becomeLeader (census-first) + the commit-advance family (2026-08-25, same worker, coordinator-dispatched; the U12 watch-item is the census's entire point)

- 2026-08-25 SUCCESSOR RE-VERIFICATION (own U12 outputs, fresh, all
  PASS): tip 96723532 clean; full capped proofs+Audit build green
  (507 jobs); AxLa probe verbatim-matching (equation family
  classical-trio; la_len_step [propext, Quot.sound]); hatch grep over
  StaleEquation/StaleLit/StaticCells/LaEquation/LaLit: 0. 99G free at
  launch.
- 2026-08-25 **THE becomeLeader CENSUS (probes `BlProbe2/3.lean`,
  machine + an AUTOMATED mirror walker that classifies every window
  quit — anything outside {pick, range-stop, sort, spill,
  lengthOf-atom} reported loudly as the watch-item trigger):**
  - MACHINE (born-re-sited fixture: bf31 heap at state = 1 candidate,
    na₀ = 52, NO static complement): completes in **6,466 steps
    consuming SIX choices** at [659, 843, 872, 901, 5171, 6352] —
    U4's numbers reproduced exactly at the re-sited placement.
    Projections: absRaftLog post = ⟨[(1,1)], [(2,0)], 2, 1, 1, 1⟩
    (the overlay grown by the EMPTY entry — index 2, TERM 0);
    absOutbox msgsAfterAppend = [⟨4, dst=1(=r.id), src=1, index=2,…⟩]
    — the SELF-ack; msgs = []; absRaftNode post lead=1 state=2
    (leader), Vote 7 preserved (term-equal reset). The path reads NO
    [20,31) static (completes without the complement — recorded).
  - MIRROR, first walk: the Bf31 reset spine mirrors clean (PICK
    ×4, RANGE-STOP, SORT at [659,183,28,28,28,3]), then the window
    quits at **`Stmt.typeAssert` at `*raftpb.Entry`** —
    `proto.Clone(es[i]).(*pb.Entry)` in appendEntry's clone loop: a
    MISSING TableExt arm (the U3/U10 consume-on-demand class, a
    CONCRETE-operand def-growth residual — NOT the watch-item).
- 2026-08-25 **THREE TableExt arm families CONSUMED ON DEMAND** (the
  U3 process: window quits guide; conc lemmas ship in the same edit;
  the full downstream rebuild re-checking every landed window
  kernel_rfl is the built-in guard — run after EACH growth, green
  all three times at 507 jobs):
  1. `Stmt.typeAssert` (comma-ok statement spine) + the `rhsK`
     finish over new `typeAssertValueT` (mirrors the machine's
     `typeAssertValue` — concrete-target identity via new
     `canonicalTyFuelT`/`resolveDefinedAliasesFuelT` table mirrors;
     interface-TARGET asserts quit, fail closed: needs method sets,
     no census consumer).
  2. The single-value type-assert EXPRESSION (`x.(T)`, strictK arm;
     a FAILED assert panics = stays a quit).
  3. `StrictOp.convert` at a DEFINED type (`raft.entryPayloadSize`
     — increaseUncommittedSize's conversions): alias/defined
     re-target only; struct value-conversion has NO census consumer
     and quits, fail closed ([AGENT] scoping call, recorded in the
     module docstring).
  All with conc lemmas (`typeAssertValueT_conc` /
  `canonicalTyFuelT_conc` / `resolveDefinedAliasesFuelT_conc` /
  `convertValueToTyFuelT_conc` — delegated arms via the shipped
  `convertFuel_conc`) and `stepFnT_conc` cases.
- 2026-08-25 **THE CENSUS COMPLETES — THE WATCH-ITEM ANSWER IS
  CLEAN** (walker, final): full mirror schedule
  **[659, 183, 28, 28, 28, 3, 4236, 83, 1096, 113]** + 9 crossings
  (4 picks, range-stop, sort, SPILL atom 0 at tgt 328/backing 329,
  **LEN(atom 0) := 1** — the ONE atom read between the spills, the
  same choice-independent la_len class — SPILL atom 1 at tgt
  395/backing 396) = **6,466 exactly**, `.next .stop`. **NO
  cap-consuming re-read exists on the becomeLeader path**: the
  equation is sanctioned (the coordinator's if-clean branch), shape =
  the Bf31 reset spine + the La tail, ZERO new transport machinery.
  - What-this-taught-us (census): the automated quit-classifying
    walker turned a three-round arm hunt into three cheap probe
    runs — the census instrument for every remaining handler; and
    the "same lever" TableExt families keep arriving exactly as the
    U3 process predicts (typeAssert/convert were latent in EVERY
    clone-carrying path, not becomeLeader specialties — Go-general
    machinery, consumed once, guarded by the full-rebuild
    kernel_rfl re-check).
- 2026-08-25 Slice 2 — **THE becomeLeader EQUATION LANDED**
  (`BlEquation.lean` 1,210 lines + generated `BlLit.lean` 1.7 MB /
  10 window literals by probe `BlGen.lean` — the printer's 9th
  consumer; γ-validated at (c₅,c₆) = (0,0)/(3,5)/(31,31) before any
  theorem): **the last wave-2 becomeX handler, the SIX-choice span,
  the largest chain yet — 10 windows / 9 crossings — GREEN ON THE
  FIRST FULL CHECK, 190 s module** (BlLit 8.2 s).
  - Shape: the Bf31 reset spine (Intn pick at map 61 + three Visit
    picks at map 33 + range-stop + sortSlice collapse — uCands1/
    bc31Cands3/uρ'/uKeys/normalize_small/stepFn_pick_transport ALL
    reused verbatim; six-leaf stop/sort dispatchers at the bl
    literals) + the La tail (spill atoms 0 → len := 1 → spill atoms
    1). Fixture: state = CONCRETE 1 (the follower panic guard — the
    BPC precondition pattern), Vote/lead/ldT symbolic vars 1/2/4,
    term-equal reset (Vote SURVIVES, norm-wrap depth 16 probed from
    the literal — `unrm 16` + `unrm_id hvote`).
  - Conclusions (ELEVEN): absRaftLog pre = hhAbsLog, post =
    `blAbsLogPost` = ⟨[(1,1)], [(2,0)], 2, 1, 1, 1⟩ — **the log
    grown by the leader's EMPTY entry (index 2, TERM 0)**, axiom-free
    `bl_log_grew`; **absOutbox msgsAfterAppend = [specAppResp 1 1 0
    2] — the SELF-ack (To = From = r.id)**; msgs = []; Vote = ρ.ints
    1; lead = 1; **state = 2 (StateLeader — the transition
    readout)**; pendingConfIndex = 1; Term = 0. Alloc PRIMARY
    consumes `Frame.span_relocate` (4th consumer) + identity
    corollary at ρT 52 + §3.3 witness (stream [3,1,0,0,3,5]).
  - Fresh `#print axioms` (probe `AxBl`, verbatim): the equation
    family + spans + spill crossings [propext, Classical.choice,
    Quot.sound]; bl_len_step / blPick1_step / blW1_out [propext,
    Quot.sound]; bl_log_grew NO axioms. Full proofs+Audit green
    **509 jobs** (507 + BlLit + BlEquation); hatch grep 0/0.
  - What-this-taught-us (slice 2): the pipeline is MATURE — a
    six-choice, ten-window handler assembled first-try from existing
    pieces (spine machinery reused verbatim, tail pattern copied,
    literals generated); the marginal cost of the LARGEST handler so
    far was one census, three same-lever TableExt arms, and a day's
    assembly — the U3 scale verdict's curve, still holding. wave-2's
    becomeX family is now COMPLETE (BPC, BF, BC, BL).
- 2026-08-25 Slice 3 — **THE handleHeartbeat COMMIT-ADVANCE EQUATION
  LANDED — handleHeartbeat is COMPLETE** (`HhAdvEquation.lean` 434
  lines + generated `HhAdvLit.lean`; probes `HhAdvProbe` census +
  `HhAdvGen` — the printer's 10th consumer — both before any theorem):
  - Census: **1,681 steps, ONE choice at 1655** (windows [1655, 25]);
    the pre-window = Hh's + commitTo's ADVANCE branch (`committed <
    tocommit` true, `lastIndex()` through the full Bf dispatch chain,
    `committed := 2`); zero new machinery — pure assembly on the
    Stale template. Fixture: the two-entry stable log at committed =
    1 (lastIndex 2, headroom), m.Commit = 2; crossing cells elems
    150 → response 100, tgt 151, backing 152. Generator γ==machine
    at c=0/3/31.
  - Conclusions: **`hha_committed_advanced` (axiom-free): committed
    1 → 2 = m.Commit with the log VIEW untouched** — the first
    equation whose post-state ADVANCES the commit index; absOutbox
    "msgs" = [specHeartbeatResp 1 2 0] (the SAME record as the no-op
    family — the two families differ only in the log, the U12
    branch-on-STATE pattern again); msgsAfterAppend = [];
    Vote/lead/Term readouts. `Frame.span_relocate` 5th consumer.
    Module **55 s**; axioms classical trio, hhaW1_out [propext,
    Quot.sound]. Full proofs+Audit green **511 jobs**; hatch 0/0.
  - [AGENT] The template slip and the convention working: the first
    build attempt hung past 10 min — the U11 numeric-mismatch class
    EXACTLY (the sed-templated module kept the Stale RHS tuples
    `(1307, …)`/`(28, …)` against the new 1655/25 windows; the wrong
    RHS sent elaboration into spine-unfolding). Caught in ONE sliced
    probe run by the U11 convention (check numeric args first, diff
    sliced probes); fix was two numbers, then green in 55 s. The
    convention's third confirmed save.
  - What-this-taught-us (slice 3): family-2 equations off a landed
    template are now ~2-hour work INCLUDING the census — but the
    template's numeric constants are the whole risk surface;
    generator-emitted link RHS values (rather than sed-carried ones)
    would make the class unrepresentable — noted as a printer
    improvement for the next consumer.
- 2026-08-25 Slice 4 — **THE MemoryStorage.Term ERROR-BRANCH
  EQUATIONS LANDED — the U4 residual closed, and THE STATIC-CELL
  COMPLEMENT'S SECOND CONSUMER** (`MsErrEquation.lean` 359 lines;
  census probe `MsErrProbe` first; the coordinator's insight-test
  pick):
  - Census: **both branches choice-free, single-window, mirror clean
    end-to-end** — Term(0) → ErrCompacted (cell 23, payload 83) in
    159 steps; Term(5) → ErrUnavailable (cell 25 — THE U11 stuck
    cell — payload 91) in 180 steps. The fixture =
    `ms31SymHeap ++ staticComplementSym` at na₀ = 98 — **the
    complement composed with a landed fixture by APPEND ALONE**, on
    a path disjoint from log-append: the generality claim validated
    by its design test.
  - Conclusion shape (recorded honestly): the spec side answers
    **`specTermAt … = none`** at both indexes (the out-of-range arm
    — the spec does not distinguish WHICH error), and the
    machine-level identity conclusions carry the distinction: the
    er result cell and the static ROOT cell hold the SAME interface
    value (two lookups; both rename together under relocation via
    new local `lookup_value_renV` — `lookup_value_ren` without the
    loc-free premise, concluding the RENAMED value; promotion note:
    a second consumer lifts it beside the original in AllocEqWave1).
  - Both families: alloc PRIMARY (`Frame.span_relocate` 6th/7th
    consumers) + identity corollaries + §3.3 witnesses. Module
    **378 s** (the per-conjunct one-window cost class — no literals,
    the BpcEquation pattern note: literalization pays from the
    second window on; ~14 window-evaluating kernel facts at
    159/180 steps each). Axioms: equation families classical trio;
    `mse*_spec_none`/`lookup_value_renV` [propext]. Full
    proofs+Audit green **512 jobs**; hatch 0.
  - What-this-taught-us (slice 4): the complement really is a
    fixture LIBRARY BLOCK — append + na₀, nothing else — and the
    error-identity conclusion shape ("the returned err IS the
    package-level var, stated as two renaming-covariant lookups")
    is the honest form for Go's sentinel-error pattern: the spec's
    none-arm plus machine identity, neither blurred into the other.

### PROMOTION LEDGER updates (A4-U13)

- **Three TableExt arm families** (typeAssert stmt+expr over
  `typeAssertValueT`/`canonicalTyFuelT`/`resolveDefinedAliasesFuelT`;
  convert-at-defined via `convertValueToTyFuelT`) — LANDED as the
  consume-on-demand process prescribes (conc lemmas in the same
  edit, full-rebuild guard green); Go-general (every clone/assert/
  defined-conversion path), not becomeLeader specialties.
- The literal printer — 9th and 10th consumers (BlGen, HhAdvGen).
  NEW improvement note (the U13 slice-3 slip): emit the link-theorem
  RHS step counts FROM the generator instead of sed-carrying them —
  would make the U11 numeric-mismatch class unrepresentable at
  template time. Take at the next generator touch.
- **`lookup_value_renV`** (MsErrEquation, local) — the renamed-value
  sibling of `lookup_value_ren`; second consumer lifts it beside the
  original in `AllocEqWave1`.
- The `stepFn_atomRead_transport` wrapper row (U12): now TWO landed
  instances of the composition (la_len_step, bl_len_step) — still
  below the wrapper threshold by the letter (both are 10-line
  compositions); third instance takes the lift.
- `Frame.span_relocate` — consumers now SEVEN (Hae shipped copy;
  Stale, La, Bl, HhAdv, MsErr ×2 via the lifted form). Row closed at
  U12; count updated for the record.

## A4-U13 exit (2026-08-25, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the dispatch tip
96723532: 5 (aaa9b03d census+arms, 21c19279 becomeLeader, f429eb92
commit-advance, 067bd58c Ms error branches, + this log/exit commit);
no coordinator commits interleaved (checked at recount:
`git log 96723532..HEAD --oneline` = the above). Full proofs+Audit
green: **512 jobs** (507 at entry + BlLit + BlEquation + HhAdvLit +
HhAdvEquation + MsErrEquation). Kit pins: none owed this unit
(target-layer modules; the TableExt growths carry conc lemmas, not
pins — the U3/U10 precedent). Hatch grep over every new/touched
module: 0.

**Deliverable state vs the U13 charter (coordinator-confirmed
priorities):**
1. becomeLeader, census FIRST — **DELIVERED, BOTH HALVES**: the
   census's entire point (the cap-re-read watch-item) answered CLEAN
   (the one inter-spill atom read is the choice-independent len
   class; walker-validated schedule = 6,466 exactly), three
   same-lever TableExt arm families consumed on demand en route;
   then **THE EQUATION** (the if-clean branch): six choices, 10
   windows/9 crossings, green on the first full check (190 s) —
   wave-2's becomeX family is COMPLETE (BPC/BF/BC/BL).
2. handleHeartbeat commit-advance — **DELIVERED**: handleHeartbeat
   COMPLETE (committed 1 → 2 = m.Commit, view untouched,
   `hha_committed_advanced` axiom-free; 55 s module).
3. Budget slot (the coordinator's insight-test pick) — **DELIVERED**:
   the Ms Term ERROR-BRANCH equations = the U4 residual closed AND
   the static-cell complement's SECOND consumer (append-only
   composition with a landed fixture on a disjoint path — the
   generality claim validated); the spec-none + error-identity
   conclusion shape recorded for Go's sentinel-error pattern.

**Handler-equation state after this unit:** 13 equation families on
the branch — becomeFollower, becomePreCandidate, becomeCandidate,
**becomeLeader** (new), MemoryStorage.FirstIndex, MemoryStorage.Term
(ok + **two error branches**, new), handleHeartbeat (no-op +
**commit-advance**, new — COMPLETE), handleAppendEntries
(success/stale/log-append). Every wave-2 handler except the Hae
REJECT family now has all its censused families proved.

**Open gaps carried (none counted):** GAP-V1-2/-4/-5, GAP-U1-W1,
GAP-V2-1 wave-3 condition, GAP-V2-2, MemoryStorage.Entries spec
design — unchanged; U10's residuals now REDUCED (commit-advance
DONE; message-field symbolism branch crossing and the multi-element
spill variant remain); the Hae REJECT family (the last
handleAppendEntries branch — findConflictByTerm loop, choice-free
but window-heavy); the atom-re-read watch-item is RETIRED for
len-shaped reads (two clean instances) but stays open for
cap-consuming reads (no instance yet — re-check per census); U13
adds: the interface-TARGET typeAssert arm and struct value-conversion
retag remain scoped-out TableExt quits (fail closed, consume on
demand); the generator RHS-emission improvement (ledger).

**A4-U14 CHARTER (proposed):** (1) the handleAppendEntries REJECT
family — census first (choice-free expected; findConflictByTerm's
loop may make the window the largest yet — if a single window
balloons past the anti-grinding smell, split at loop boundaries and
STOP at the design question rather than grinding); closing it makes
handleAppendEntries the first COMPLETE message handler with all four
censused families. (2) The message-field symbolism branch crossing
(the U10 finding: `m.From ≠ r.id` as a side-condition branch
crossing — one general q1Branch transport in the established
patterns; unlocks From-symbolic statements of every landed
message-handler equation). (3) Budget permitting: stepFollower/
stepCandidate dispatch censuses (the wave-3 opening — the Step
dispatch chain reads cells 16/17/27/28, the complement's remaining
roots). Rotation note: this worker is at ~630k tokens; U14 should
open with a fresh worker per the split discipline.

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1); the comparator-landmark STALE flag
stands escalated from U8–U12.

- 2026-08-25 A4-U13 gate follow-up (same-commit convention): unit-end
  gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the
  exit tree — **RESULT: PASS, exit 0** (`artifacts/ci-arc4-u13.log`,
  gitignored; 22 ok steps + the two sanctioned no-diff notes — this
  unit touched `proofs/GoLeanProofs/{Sym/TableExt.lean,Specs/Raft/
  {BlLit,BlEquation,HhAdvLit,HhAdvEquation,MsErrEquation}.lean}` +
  the aggregator + arc-4 docs + gitignored probes only; no runtime
  code, no Corpus/, no baselines/; the TableExt def-growths carry
  their conc lemmas and the full-rebuild kernel_rfl guard, per the
  U3/U10 precedent). Gate staggered behind the `free -g` guard (93G
  free ≥ 24G cap). The comparator-landmark note now reads **STALE at
  126 commits** (report-only) — stands escalated for the operator's
  merge step, as at U8–U12.

## A4-U14 — the Hae REJECT family + the From-transport + the wave-3 dispatch opening (2026-08-25, successor worker, coordinator-dispatched)

- 2026-08-25 SUCCESSOR RE-VERIFICATION (U13's top claims, fresh
  probes, all PASS):
  - tip clean: `git status` = "nothing to commit, working tree clean"
    on branch `campaign-arc4`; `git rev-parse HEAD` =
    `b143c56d7a45a415d09de94447f11460fdff8e7a` (the dispatch tip).
    93G free at launch (≥ 40G floor); every build this unit
    `GOLEAN_MEM_MAX=48G scripts/capped`.
  - fresh capped proofs+Audit build: "Build completed successfully
    (512 jobs)." exit 0 — matching U13's recorded 512.
  - `#print axioms` fresh probes (AxBl/AxHhAdv/AxMsErr, capped,
    verbatim): becomeLeader/handleHeartbeat_advance/msTerm-error
    equation families all [propext, Classical.choice, Quot.sound];
    **`bl_log_grew` and `hha_committed_advanced` axiom-FREE** —
    matching U13's record exactly.
  - hatch grep (`sorry|native_decide|axiom `) over BlEquation/
    HhAdvEquation/MsErrEquation/TableExt/SpillTransport/
    PickTransport/KernelRfl/Lens: **0 in every file**.
- 2026-08-25 **THE REJECT CENSUS — CLEAN, AND THE ANTI-GRINDING
  CHECK DID NOT TRIGGER** (probes `HaeRejProbe.lean` +
  `HaeRejGen.lean`, census FIRST per the charter; every number from
  these runs):
  - Fixture: born re-sited, the two-entry TERM-DIVERGENT log —
    storage ents (1,1),(2,**2**), committed = 1 (< prev.index 2: NOT
    stale; consistent: committed ≤ lastIndex, entry terms
    nondecreasing), unstable empty at offset 3; message LogTerm 1 /
    Index 2 → matchTerm fails (term(2) = 2 ≠ 1) → REJECT
    (raft.go:1824-1853). `findConflictByTerm(2, 1)` runs TWO live
    iterations (term(2) = 2 > 1 → decrement; term(1) = 1 ≤ 1 →
    return (1,1)) — both loop arms exercised.
  - Machine: **6,951 steps, ONE choice at 6925** (the
    msgsAfterAppend spill), na 60→493, `.next .stop`. **ZERO static
    [20,31) derefs** (single-pass walker scan): every `term()` on
    this path returns err = nil BEFORE any sentinel compare — the
    static-cell complement is NOT needed for this family.
  - Mirror: **6,925 steps CLEAN to the q3Choice spill quit — ZERO
    new TableExt machinery** (the whole reject walk: matchTerm,
    Debugf args via zeroTermOnOutOfBounds's err=nil arm, min,
    the findConflictByTerm loop — all on landed classes);
    post-window 25. The 6,925-step pre-window is **the largest
    single window yet** (vs La's 3,573); checked against the ~1h
    anti-grinding smell: the kernel link replays once at the landed
    ~linear cost class (measured: the whole equation module = 107 s)
    — far below the stop threshold, so the charter's loop-boundary
    split contingency was NOT triggered, by measurement not by hope.
- 2026-08-25 Slice 1 (879a81b4) — **THE handleAppendEntries
  REJECT-FAMILY EQUATION LANDED: handleAppendEntries is the FIRST
  FULLY-COMPLETE message handler** (success/empty U11, stale U12,
  log-append U12, REJECT here — all four censused families proved).
  `HaeRejEquation.lean` (494 lines) + generated `HaeRejLit.lean`
  (8,571 lines, the printer's 11th consumer):
  - **The U13 printer improvement TAKEN** (the ledger row): the
    generator now EMITS the window step counts and crossing
    addresses as defs (`haeRejW1n`/`haeRejW2n`/`haeRejMsgPtr`/
    `haeRejTgt`/`haeRejBacking`), and the link theorems consume the
    defs — the U11 numeric-mismatch class (sed-carried RHS values,
    the U13 slice-3 slip) is now unrepresentable at template time.
  - The Stale template exactly: windows [6925, 25] + one spill
    crossing; alloc PRIMARY (`Frame.span_relocate`, 8th consumer) +
    identity corollary + §3.3 witness; TEN conclusions through
    absState v2 + the lens readers — **the first Reject = true
    record**: `absOutbox "msgsAfterAppend" = [specAppRejResp 1 2 0 2
    1 1]` (Index = m.Index = 2, RejectHint/LogTerm =
    findConflictByTerm's (1,1)), msgs = [], log view PRESERVED
    (`haeRejAbsLog`, the reject branch writes nothing), Vote/lead/
    Term readouts. γ==machine validated at c = 0/3/31 BEFORE any
    theorem.
  - **GREEN ON THE FIRST FULL CHECK**: 514 jobs; module 107 s
    (lake env re-measure); axioms classical trio
    (haeRejW1_out/haeRej_post_absOutbox [propext, Quot.sound];
    fresh probe `AxHaeRej`, verbatim); hatch grep 0/0.
- 2026-08-25 Slice 2 (c41f330e) — **THE BRANCH-CROSSING TRANSPORT +
  THE From-SYMBOLIC handleHeartbeat EQUATION (the U10 residual
  CLOSED)**:
  - **`Sym/BranchTransport.lean`** (79 lines): `stepFn_branch_transport`
    — the mirror's q1Branch quit (`retV v (ifK …)` at a symbolic
    bool) crossed at the γ-image, the arm selected by
    `hb : concV (symInterp ρ) v = .bool b`; state, allocator, and
    stream RIDE (the machine ifK arm touches none of them).
    LINEAGE: path-condition splitting (King 1976) — the founding
    symbolic-execution move, realized in the established transport
    pattern (Pick/Spill's third member). In-module §3.3 witness LIVE
    at a genuinely symbolic condition (`x₀ == 1` at x₀ = 5; a
    different valuation flips it). Fail-closed scope: ifK only (the
    censused consumer); whileK/andK/orK/boolK on first consumer.
    **2 Kit pins, both [propext, Quot.sound]** (build-enforced).
  - Probe first (`HhFromProbe`/`HhFromGen`): the Hh no-op fixture
    with cell 54 (m.From) = var 5 quits q1Branch at step 1259 —
    the condition is EXACTLY U10's recorded
    `eqI(norm²(x₅), lit 1)` (send's self-addressed panic guard;
    γB false at x₅=2, TRUE at x₅=1 — live both ways); the else-arm
    is the empty `seqn #[]`; the spill cells are Hh's VERBATIM
    (elems 124, tgt 125, backing 126, msgPtr 74 — the branch detour
    does not change the allocation schedule); windows
    **[1259, 39, 25]** + branch + spill = **1,325 = the concrete Hh
    span**; γ==machine at c = 0/3/31.
  - **`handleHeartbeat_fromSym_eq_alloc`** (HhFromEquation.lean, 434
    lines + HhFromLit 1,572 generated): the shipped no-op statement
    with m.From SYMBOLIC under the subject's own precondition as
    side conditions (`hfrom` range + `hfrom_ne : ρ.ints 5 ≠ 1`,
    discharging the path condition via `beq_eq_false_iff_ne`) —
    **the outbox conclusion is `[specHeartbeatResp 1 (ρ.ints 5) 0]`:
    the response destination proved for EVERY non-self-addressed
    sender at once** (the To field aliases the argument's From cell
    — plainpb pointer copy — holding RAW var 5, so dst is
    unwrapped). Identity corollary + witness at From = 9 (a value NO
    shipped fixture used — genuine From-generality). The shipped
    concrete equation is this statement's ints₅ := 2 instance.
    Module 41 s; 517 jobs green; axioms classical trio (transport
    consumers), hhFromCond_form [propext]; hatch 0/0/0.
  - What-this-taught-us (slice 2): the transport itself is ~10 lines
    of proof — the entire cost of message-field symbolism is the
    LITERAL REGENERATION at the new window boundaries (the branch
    splits one window into two), and the crossing state is SHARED
    (the branch is pure control: S unchanged). Message-field
    upgrades of other landed equations are now template work:
    generator + rename + two extra side conditions.
- 2026-08-25 Slice 3 (probe-only, as chartered) — **THE WAVE-3
  DISPATCH CENSUSES** (probe `StepDispatchProbe.lean`, single-pass
  walker + static-[16,31) scan; drained caller shape
  `.call #[er] fid #[r, m]`, born-re-sited Hh heap + a Message with
  a REAL Type cell):
  - **stepFollower × MsgHeartbeat (Type 8): 1,710 steps, ONE choice
    at 1581**, er = nil, msgs = [HeartbeatResp 9], lead := m.From =
    2, log view preserved — the arm IS the landed Hh no-op span
    (1,325) + ~385 dispatch-glue steps (GetType deref chain, the
    switch compare ladder, electionElapsed := 0, lead store).
    CONSUMES: handleHeartbeat no-op (+ commit-advance at the other
    fixture family).
  - **stepFollower × MsgProp forward (Type 2, lead = 2 ≠ 0): 1,272
    steps, ONE choice at 1119**, msgs = [the forwarded Prop record,
    typ 2], er = nil — a send-only arm consuming NO handler
    equation (its own small family; the landed spill transport
    covers its choice).
  - **stepFollower × MsgProp drop (lead = 0): STUCK at step 235 —
    `unbound heap location: base 17` (ErrProposalDropped), WITH OR
    WITHOUT the [20,31) complement. THE FINDING: the dispatch layer
    needs a complement EXTENSION — cells 16/17 (ErrStopped/
    ErrProposalDropped) + their payload cells are OUTSIDE the U12
    block's [20,31) range** (exactly the U13 charter's predicted
    "remaining roots"; 27/28 — the message-type bool tables — ARE
    already in the block). Extension recipe = the StaticCells
    pattern verbatim (same $pkginit dump, two more roots + payload
    closure); goes to U15.
  - **stepCandidate × MsgHeartbeat (state = 1): 4,969 steps, FIVE
    choices at [983, 1167, 1196, 1225, 4879]** — THE COMPOSITION
    DATUM: the arm literally composes the landed becomeFollower
    reset spine (4 picks: Intn + 3 Visit) with the landed Hh tail
    (the spill), plus glue; state 1→0, lead := m.From, er = nil,
    msgs = [HeartbeatResp], log view preserved; the only static
    read is globalRand 18 (in-fixture). Wave-3 arm equations are
    window-chain ASSEMBLIES of landed handler spans — the layer-C
    composition shape confirmed at first contact.
  - **THE COMPOSITION MAP (layer C's input; static reading of
    raft.go:1692-1799 + the dynamic runs above):**
    | dispatch arm | consumes (landed) | missing |
    |---|---|---|
    | sF×MsgApp | handleAppendEntries: success/stale/log-append/REJECT (all landed) | — |
    | sF×MsgHeartbeat | Hh no-op + commit-advance | — (probed end-to-end) |
    | sF×MsgSnap | — | handleSnapshot (out of wave-2 scope, GAP-V2-2) |
    | sF×MsgProp/TransferLeader/ReadIndex (fwd) | — (send-only) | the 16/17 complement ext for the drop arms |
    | sF×MsgTimeoutNow | — | hup/campaign chain |
    | sF×MsgForgetLeader | — (lead store only) | — |
    | sF×MsgReadIndexResp | — | readStates spill family |
    | sC×MsgApp | becomeFollower + Hae families | — |
    | sC×MsgHeartbeat | becomeFollower + Hh | — (probed end-to-end, 5 choices) |
    | sC×MsgSnap | becomeFollower | handleSnapshot |
    | sC×myVoteResp | becomeLeader (won, candidate) / becomeFollower (lost) | poll/quorum tally (GAP-V1-2), campaign, bcastAppend |
    | sC×MsgTimeoutNow | — (Debugf no-op) | — |
  - Probe-side note (recorded for the instrument): a struct-update
    `{ x with a := _, b := _ }` whose fields are comma-separated on
    ONE line hit a parse error inside this probe (recovered
    silently into a poisoned fixture — na wrong, nonsense sticks);
    newline-separated fields parse clean. The poisoned-run signature
    (na far below the fixture's base) is worth recognizing: the
    FIRST run's "stuck" messages were fixture corruption, not
    machine findings — only the static-17 stuck survived the fix,
    and it is the real finding.

### PROMOTION LEDGER updates (A4-U14)

- **`stepFn_branch_transport`** (`Sym/BranchTransport.lean`) —
  LANDED as general kit surface (2 Kit pins, [propext, Quot.sound]);
  consumers: the From-symbolic Hh equation (landed); every
  message-field-symbolic upgrade and every dispatch-arm equation
  that branches on symbolic state. whileK/andK/orK/boolK arms on
  first consumer.
- The literal printer — 11th/12th consumers (HaeRejGen, HhFromGen);
  **the U13 RHS-emission improvement row TAKEN** (both new
  generators emit counts/addresses as defs; the sed-carried-RHS
  class is unrepresentable in the new modules). Remaining older
  generators keep sed-carried values as shipped history.
- NEW ROW: **the dispatch-layer static complement extension** (cells
  16/17 + payload closure, the StaticCells pattern verbatim) —
  consumers: every stepFollower/stepCandidate/stepLeader drop-arm
  equation (ErrProposalDropped), any Stop path (ErrStopped). Blocks
  wave-3 drop arms only; the probed heartbeat/forward arms do not
  need it.
- The `stepFn_atomRead_transport` wrapper row (U12/U13): unchanged —
  still two instances, third instance takes the lift.

## A4-U14 exit (2026-08-25, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the dispatch tip
b143c56d: 2 (879a81b4 slice 1, c41f330e slice 2) + this log/exit
commit; no coordinator commits interleaved (checked at recount:
`git log b143c56d..HEAD --oneline` = the above). Full proofs+Audit
green: **517 jobs** (512 at entry + HaeRejLit + HaeRejEquation +
BranchTransport + HhFromLit + HhFromEquation). Kit pins: +2 (the
branch-transport pair, build-enforced). Hatch grep over every new
module: 0. Gate record follows in the next entry (same-commit
convention).

**Deliverable state vs the U14 charter:**
1. THE Hae REJECT FAMILY — **DELIVERED, census first**: the census's
   anti-grinding question answered by measurement (largest window
   yet, 6,925 steps, but 107 s module — no split needed; the
   loop-boundary contingency stood down); zero new machinery; zero
   static reads; **handleAppendEntries is the FIRST FULLY-COMPLETE
   message handler** (all four censused families proved).
2. THE `m.From ≠ r.id` BRANCH-CROSSING TRANSPORT — **DELIVERED as
   general machinery + demonstrated**: `stepFn_branch_transport`
   (lineage-lined, witnessed, Kit-pinned) + the From-symbolic
   handleHeartbeat equation as its discharge witness (the cheapest
   upgrade: 1,325-step span, the shipped statement's ints₅ := 2
   instance re-derived; dst = ρ.ints 5 proved for every
   non-self-addressed sender).
3. WAVE-3 OPENING — **DELIVERED, probe-only as chartered**: the
   stepFollower/stepCandidate censuses with the full composition
   map (which landed equations each arm consumes), the two
   end-to-end dynamic runs (sF×Heartbeat 1,710/1 choice;
   sC×Heartbeat 4,969/5 choices — the two-equation composition
   observed), and the dispatch-complement finding (cells 16/17
   outside the U12 block — the drop arms' named debt).

**Open gaps carried (none counted):** GAP-V1-2/-4/-5, GAP-U1-W1,
GAP-V2-1 wave-3 condition, GAP-V2-2, MemoryStorage.Entries spec
design — unchanged; the multi-element spill variant unchanged; the
U10 message-field-symbolism residual CLOSED this unit (From; other
fields — LogTerm/Index/Commit symbolism — are the same
transport+regeneration template, on demand); the atom-re-read
watch-item stays open for cap-consuming reads (none seen — checked
this unit's censuses: the reject and dispatch paths have no
inter-spill atom reads); U14 adds: the dispatch-layer static
complement extension (cells 16/17 + payloads, ledger row); the Hae
family-record note — the four Hae families' response records are
pairwise distinguishable except stale-vs-log-append (the U12 note
stands; REJECT's record is distinguishable from all three by
Reject = true).

**A4-U15 CHARTER (proposed):** (1) THE DISPATCH-COMPLEMENT EXTENSION
(cells 16/17 + payload closure — the StaticCells pattern verbatim,
its third consumer class), then THE FIRST DISPATCH-ARM EQUATION:
stepFollower × MsgHeartbeat (censused end-to-end this unit: 1,710
steps / ONE choice / zero statics — pure assembly on the landed Hh
machinery; its equation makes the dispatch-composes-handlers shape
REAL at layer C's door). (2) stepCandidate × MsgHeartbeat as the
first TWO-EQUATION composition arm (5 choices, the bf spine + Hh
tail — reuses everything; the 4,969-step census is the recipe).
(3) Budget permitting: EITHER the stepLeader census (the largest
dispatch, 18 call sites — census-only, the walker instrument is
ready) OR the sF×MsgProp forward-arm equation (send-only family,
1,272 steps — cheap, exercises the no-handler dispatch shape).
Rotation note: this worker is at ~410k tokens at exit-entry time —
within budget for U15 to continue on this context if the
coordinator prefers, but the split discipline default (fresh worker
per unit) stands.

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1); the comparator-landmark STALE flag
stands escalated from U8–U13.

- 2026-08-25 A4-U14 gate follow-up (same-commit convention): unit-end
  gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the
  exit tree — **RESULT: PASS, exit 0** (`artifacts/ci-arc4-u14.log`,
  gitignored; 22 ok steps + the two sanctioned no-diff notes — this
  unit touched `proofs/GoLeanProofs/{Sym/BranchTransport.lean,
  Specs/Raft/{HaeRejLit,HaeRejEquation,HhFromLit,HhFromEquation}.lean}`
  + the aggregator + `proofs/Audit/Kit.lean` (additive import + 2
  pins) + arc-4 docs + gitignored probes only; no runtime code, no
  Corpus/, no baselines/, zero edits to shipped module STATEMENTS).
  Gate staggered behind the `free -g` guard (93G free ≥ 24G cap).
  The comparator-landmark note now reads **STALE at 130 commits**
  (> the 100 threshold; report-only) — stands escalated for the
  operator's merge step, as at U8–U13.

## A4-U15 — the dispatch-complement extension + THE COMPOSITION-MECHANICS VERDICT + the first dispatch-arm equation (2026-08-25, successor worker, coordinator-dispatched)

- 2026-08-25 SUCCESSOR RE-VERIFICATION (U14's top claims, fresh
  probes, all PASS):
  - tip clean: `git status` = "nothing to commit, working tree clean"
    on branch `campaign-arc4`; `git rev-parse HEAD` =
    `24458fdd1ef2c53bc9c9ae413a6e8d9499c3a083` (the U14 gate tip).
    93G free at launch (≥ 40G floor); every build this unit
    `GOLEAN_MEM_MAX=48G scripts/capped`.
  - fresh capped proofs+Audit build: "Build completed successfully
    (517 jobs)." exit 0 — matching U14's recorded 517.
  - `#print axioms` fresh probe (`AxU15Reverify`, capped, verbatim):
    handleAppendEntries_reject_eq_alloc /
    handleHeartbeat_fromSym_eq_alloc
    [propext, Classical.choice, Quot.sound]; haeRejW1_out /
    haeRej_post_absOutbox / **stepFn_branch_transport**
    [propext, Quot.sound] — matching U14's record exactly.
  - hatch grep over HaeRejEquation/HaeRejLit/BranchTransport/
    HhFromEquation/HhFromLit: **0** (single grep, all five files).
- 2026-08-25 Slice 1 (9cfe59ba) — **THE DISPATCH-COMPLEMENT
  EXTENSION LANDED** (`StaticCellsExt.lean`, 96 lines; contact probe
  `StaticsExtProbe.lean` FIRST — all numbers from its runs):
  - Contact: cells 16 (`ErrStopped`) / 17 (`ErrProposalDropped`) are
    `error`-interface boxes over `raft.goleanShimErrorString`
    payloads at **61** ("raft: stopped") and **65** ("raft proposal
    dropped") — closure-complete (roots reference ONLY these two;
    payloads reference nothing).
  - **THE PLACEMENT FINDING (the slice's headline): the payload
    geometry DIFFERS from the U12 block's.** 61/65 sit INSIDE the
    leaf fixture range [31,71), unlike the [20,31) payloads (all
    ≥ 71). Zero renaming STILL (true addresses; the U12
    address-for-address layer-C argument stands; the kernel link
    pins the true cells) — but the consequence lands on CONSUMERS:
    **leaf/caller cells must stay OFF {61, 65}**. The U14 dispatch
    probe itself used cell 61 as a caller var — that placement
    collides here; the re-census moved caller cells to [66,69).
    `staticComplementNa` (98) unchanged. Recorded in the module.
  - The StaticCells recipe VERBATIM otherwise: fail-closed
    `staticComplementExtOf` extraction, generated literal,
    **`staticComplementExt_link` (kernel_rfl) replaying the full
    1,382-step init + 4 lookups on every build — 104 s, one
    init-replay cost class as predicted**; `staticComplementFull` =
    the U12 block ++ the extension (disjoint id sets);
    `staticComplementExtSym` mirror form.
  - **VALIDATION (probe `StepDispatchProbe2`, the U14 census probe at
    the new caller placement): the sF×MsgProp DROP arm COMPLETES —
    254 steps, ZERO choices, `.next .stop`, er = the
    ErrProposalDropped interface (payload 65 verbatim), msgs = maa =
    [], log view preserved, lead stays 0.** The U14 stuck (step 235,
    cell 17) is GONE; the control WITHOUT the block still sticks at
    cell 17 step 235 (fail-closed, the extension is the exact debt).
    The static read on the drop path: exactly [(232, 17)]. The other
    censused arms re-pinned UNCHANGED at the new placement:
    sF×Heartbeat 1,710/1 @1581; sF×Prop-fwd 1,272/1 @1119;
    sC×Heartbeat 4,969/5 @[983,1167,1196,1225,4879].
- 2026-08-25 Slice 2 (probes only, gitignored) — **THE COMPOSITION
  MECHANICS, MEASURED TO THE BOTTOM** (the charter's most important
  deliverable; probes `SeamCompProbe`/`SeamE1Probe` (E1),
  `ContParam5`/`ContParamN` (E2); every claim from a run):
  - **E1a — the seam config**: at glue step 282 of the sF×Heartbeat
    arm (282 = 1581 − 1299, the census arithmetic), the machine
    config IS `retV (.addr 52) (callArgsK "raft.raft.handleHeartbeat"
    [] [.addr 31] [] E_sf K_sf)` — the landed hhC0's drained-call
    shape VERBATIM with the dispatch glue's (env, cont) in the two
    tail slots (E_sf = stepFollower's scope stack over glue cells
    69-80; K_sf = the switch-ladder seq chain down to the
    stepFollower frame, er store, `.stop`). na at the seam: 81.
  - **E1b — the seam heap**: vs γ(hhS0) at the census valuation,
    EXACTLY one shared-cell difference — msg 52's Type field
    (`.addr 55` vs `.nil`) — plus seam-only frameable cells
    {55, 66-68, 69-80}; **the raft cell matches EXACTLY** (the
    glue's ee := 0 / lead := 2 writes produced zero normalization
    drift at concrete valuations). No hh-only cells.
  - **E2 — CONT-BOTTOM PARAMETRICITY HOLDS AND IS CHEAP**: the
    mirror evaluator never destructs the continuation bottom, so the
    window link `symEvalWindowTB bfTB 1299 hhS0 (hhC0k k) = (1299,
    S', plugC k C')` kernel-checks **with k a FREE variable** —
    measured at budgets 50/300/1299: 17.3/21.0/25.1 s file times
    (≈8 s marginal at full window vs the concrete link). The spill
    transport is ALREADY cont-generic (`{k : Cont symDom}` in
    `stepFn_appendSpill_transport`). Placement: `frameSim_relocate`
    (the U6 lift) + a small frame-extension constructor +
    `renameBodies_id` at the LANDED `wBase_funcSup = 31`
    (BpcResite.lean) discharge every FrameSim obligation; the seam
    heap is literally canonical ++ frame (ρT 56 25 is identity on
    every canonical id and content).
  - **THE WALL (one level deeper than the charter's anticipated
    dimensions, and the reason no composed equation shipped):**
    applying the relocated handler span MID-RUN yields its
    post-state only RELATIONALLY — `∃σFfin` + `FrameSim` via
    `stepFnIter_sim`, whose carried relation is exactly the lossy
    `FrameSim` (verified: NO heap-completeness clause — locs outside
    rename-image ∪ frame are unconstrained, and list order is
    unconstrained everywhere). A literal mirror window cannot resume
    from a relational state, and the arm's SUFFIX glue (103 steps)
    writes FRAME cells (er 68, $res0 71) so it can neither ride
    inside an (env,cont)-generic sub-span (evaluation would have to
    step INTO the free cont past the frame pop) nor precede it.
    Attempted dodges, each checked and refuted in-session: frame
    re-partitioning (blocked by the same completeness gap),
    suffix-in-canonical (makes the sub-span arm-specific),
    whole-seam-as-fixture (per-arm regeneration = walking).
  - **THE VERDICT, precise**: within the current instrument,
    **literal windows compose with literal windows, and ONE trailing
    relational relocation is free (span_relocate at the end of a
    span); relational states cannot re-enter literal evaluation.**
    Statement forms do NOT resist composition — config, heap, atoms,
    choice streams, and cont/env genericity all line up, measured —
    the gap is in the PROOF INSTRUMENT. Handler-proof reuse inside
    longer literal chains needs ONE of: (i) completeness-strengthened
    FrameSim (add totality + canonical order to the relation,
    re-prove the stepFn_sim induction — the honest instrument fix,
    also the costliest single proof in the kit); (ii) stepFn
    heap-extensionality (lookup-equal states step lookup-equally —
    the heap-quotient classic; general, big); (iii) statement
    redesign (arm equations ending at handler-return compose TODAY —
    the sub-span in suffix position is absorbed by the equation's
    own ∃σfin — but the shell's return plumbing then faces the same
    wall one level up). **Consequence for wave 3: per-arm literal
    window chains (linear kernel cost, measured cheap at these
    sizes — 50 s for the 1,710-step arm) are the SANCTIONED proof
    mode; the reuse instrument is a consume-on-demand ledger row
    that becomes worth building when kernel time actually hurts
    (first candidate: the MsgApp arms × the 6,925-step Hae REJECT
    window).** Arm-equation STATEMENTS are route-independent — layer
    C consumes them identically under any future instrument.
  - Consequence for layer C's round induction (the design datum the
    charter asked for): after the FIRST relational join in a run,
    everything downstream must stay relational/projective — the
    round induction should be stated over absState projections and
    FrameSim-transported readouts (which is §2C's shape already),
    never re-entering literal windows mid-round. The per-round
    re-grounding question goes to the layer-C design gate.
- 2026-08-25 Slice 3 (d8359ade) — **THE FIRST DISPATCH-ARM EQUATION
  LANDED: stepFollower × MsgHeartbeat** (`SfHbEquation.lean` 434
  lines + generated `SfHbLit.lean` 2,022 lines — the printer's 13th
  consumer; generator `SfHbGen.lean` validated γ==machine at
  c = 0/3/31 BEFORE any theorem; proof route = the sanctioned
  literal window chain, the verdict documented in-module):
  - The HhEquation template exactly: windows **[1581, 128]** + ONE
    spill crossing (elems 150, tgt 151, backing born 152, response
    message 100 — all generator-emitted defs, the U13 convention) =
    **1,710 steps, ONE choice** — the U14 census to the step.
    Fixture: bf31 heap + the FIRST Message with a REAL Type cell
    (55 ↦ 8 — the switch ladder's branching datum) + caller cells at
    [66,69) per the slice-1 consumer rule; na₀ 69.
  - **ELEVEN conclusions** through absState v2 + the lens readers —
    the arm-level (dispatch-visible) records: absMessage pre with
    **typ = 8** (the first record showing a real Type); **er = nil**
    (the shell's no-error conclusion, read raw and
    FrameSim.lookup_some-transported); msgs outbox =
    [specHeartbeatResp 1 2 0] (the lemma-composition readout,
    HhEquation's pattern verbatim); msgsAfterAppend = [] (the two
    outboxes distinguished at arm level); log view preserved
    (pre = post = hhAbsLog); **lead := m.From = 2** (the arm's
    dispatch-visible state change — pre-lead x₂ is dead on this path
    and overwritten, so the readout is CONCRETE, no side condition);
    Vote rides; Term 0. Alloc PRIMARY (span_relocate) + identity
    corollary + §3.3 witness (stream [3], capacity 7).
  - One fix round, kernel-caught, probe-diagnosed (`VoteWrap`):
    Vote survives **norm³** (the glue's two extra raft-struct stores
    each re-wrap — arm depth vs Hh's single wrap; state/ldT norm³,
    lead norm⁴-but-concrete); the projection fact states the triple
    wrap and `simp only [hvote]` collapses it in the equation. The
    wrap DEPTH is store-count-dependent — recorded for every future
    arm equation (count the glue's struct stores, or read the
    generated literal, before stating the readout).
  - **50 s module; 520 jobs green** (517 + StaticCellsExt + SfHbLit
    + SfHbEquation); fresh `#print axioms` (probe `AxSfHb`,
    verbatim): equation family + span + spill [propext,
    Classical.choice, Quot.sound]; sfhbW1_out / sfhb_post_absOutbox
    [propext, Quot.sound]; hatch grep 0/0.
  - What-this-taught-us (slice 3): a dispatch-arm equation at a
    censused pure-assembly arm is the SAME one-session template as a
    handler family — the dispatch layer adds only the Type cell, the
    er readout, and deeper norm-wraps; nothing else was new. The
    walked route's cost scales with the arm's own span, not with the
    handlers it contains — which is exactly why the reuse instrument
    is deferrable until the big-handler arms.

### PROMOTION LEDGER updates (A4-U15)

- **`StaticCellsExt`** (`Specs/Raft/StaticCellsExt.lean`) — LANDED as
  shared fixture surface (the StaticCells pattern's second module);
  consumers: every drop-arm equation (ErrProposalDropped), any Stop
  path (ErrStopped); the kernel link is the drift alarm. **Consumer
  rule recorded in-module: leaf/caller cells OFF {61, 65}.** The U14
  ledger row (the extension) is TAKEN.
- **NEW ROW: the literal-chain reuse instrument** (the U15 verdict) —
  completeness-strengthened FrameSim OR stepFn heap-extensionality;
  consume when per-arm kernel re-walking of big handler spans
  actually hurts (first candidate: MsgApp arms × the 6,925-step Hae
  REJECT window; not before). The measured facts that de-risk it
  when taken: cont-bottom parametricity is FREE (E2), the seam heap
  is canonical-++-frame on the nose (E1b), and bodies_inv
  discharges at the landed `wBase_funcSup = 31`.
- **Cont-bottom parametricity** — recorded as a MEASURED FACT, not
  built as machinery (no consumer yet under the walked route): window
  links kernel-check with a free continuation bottom at full window
  size (+≈8 s at 1,299 steps). Becomes load-bearing the day the
  reuse instrument lands; until then it lives in the probes
  (`ContParam5`/`ContParamN`) and this entry.
- The literal printer — 13th consumer (SfHbGen); the U13
  counts-as-defs convention held (the numeric-mismatch class stays
  unrepresentable).
- The `stepFn_atomRead_transport` wrapper row (U12/U13): unchanged.

## A4-U15 exit (2026-08-25, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the U14 gate tip
24458fdd: 2 (9cfe59ba slice 1, d8359ade slices 2+3) + this log/exit
commit; no coordinator commits interleaved (checked at recount:
`git log 24458fdd..HEAD --oneline` = the above). Full proofs+Audit
green: **520 jobs**. Kit pins: +0 (no new Sym/Frame machinery — the
verdict's whole point). Hatch grep over every new module
(StaticCellsExt/SfHbLit/SfHbEquation): 0.

**Deliverable state vs the U15 charter:**
1. THE DISPATCH-COMPLEMENT EXTENSION — **DELIVERED, recipe verbatim,
   with a placement finding** (payloads 61/65 INSIDE the leaf range —
   consumer rule recorded); validated exactly as chartered (the
   MsgProp drop arm completes, 254/0, er = ErrProposalDropped;
   fail-closed control still sticks).
2. THE FIRST DISPATCH-ARM EQUATION (sF×MsgHeartbeat) — **DELIVERED**
   (1,710 steps / ONE choice, eleven arm-level conclusions incl.
   er = nil and lead := m.From, 50 s module, green on the second
   check — one probe-diagnosed norm-wrap fix). **The composition
   mechanics — the unit's most important deliverable — MEASURED TO
   THE BOTTOM with a precise verdict**: statement forms line up in
   every anticipated dimension (config/heap/atoms/cont — E1/E2
   numbers above); the block is the INSTRUMENT (FrameSim's
   lossiness at mid-run re-entry + frame-writing suffixes), named
   with three repair routes and a consume-on-demand trigger. The
   walked literal chain is the sanctioned wave-3 proof mode;
   statements are route-independent.
3. sC×MsgHeartbeat — **NOT attempted ([AGENT] boundary call, the
   charter's own STOP rule)**: the verdict answers the depth-2
   composition question analytically (the wall is POSITIONAL, not
   depth-al — a bf-spine sub-span would be mid-position too), so a
   walked sC chain would demonstrate nothing new about composition
   while consuming a full slice; the coordinator should see the
   verdict before more arms embed the route decision. The 4,969-step
   census + the U14 composition map remain its recipe.
4. Item 4 (sF×MsgProp fwd / stepLeader census) — not attempted, same
   boundary call.

**Open gaps carried (none counted):** GAP-V1-2/-4/-5, GAP-U1-W1,
GAP-V2-1 wave-3 condition, GAP-V2-2, MemoryStorage.Entries spec
design — unchanged; the multi-element spill variant unchanged; the
atom-re-read watch-item stays open (checked this unit's censuses:
the drop arm and the sF heartbeat/fwd arms have no inter-spill atom
reads); message-field symbolism (LogTerm/Index/Commit) remains the
U14 template on demand; U15 adds: **the literal-chain reuse
instrument row** (ledger, consume-on-demand) and **the norm-wrap
depth note** (store-count-dependent — read the generated literal
before stating scalar readouts).

**A4-U16 CHARTER (proposed, pending the coordinator's read of the
composition verdict):** (1) IF the verdict redirects layer-C design:
a design slice amending the seam note (§2C) with the
relational-after-first-join round-induction shape and the arm
statement conventions (er readout, Type-cell fixture rule, norm-wrap
depths) — cheap, high-value, unblocks everything downstream. (2) The
sC×MsgHeartbeat equation as a walked 6-window/5-crossing chain (the
census is the recipe; all transports landed) — the first
multi-handler arm, closing the two censused heartbeat arms. (3) By
censused cost: the sF×MsgProp forward arm (1,272/1, send-only) and/or
the sF×MsgProp DROP-arm equation (254/0, choice-FREE — the cheapest
possible arm equation, the extension's first proved consumer, and the
first arm with a non-nil er conclusion). (4) Census-only: stepLeader
(18 call sites, the walker is ready). Rotation note: this worker is
at ~330k tokens at exit-entry time — within budget for U16 on this
context if the coordinator prefers, but the split-discipline default
stands.

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1); the comparator-landmark STALE flag
stands escalated from U8–U14.

- 2026-08-25 A4-U15 gate follow-up (same-commit convention): unit-end
  gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the
  exit tree — **RESULT: PASS, exit 0** (`artifacts/ci-arc4-u15.log`,
  gitignored; 22 ok steps + the two sanctioned no-diff notes — this
  unit touched `proofs/GoLeanProofs/Specs/Raft/{StaticCellsExt,
  SfHbLit,SfHbEquation}.lean` + the aggregator + arc-4 docs +
  gitignored probes only; no runtime code, no Corpus/, no baselines/,
  zero edits to shipped module STATEMENTS, zero new Kit pins). Gate
  staggered behind the `free -g` guard (93G free ≥ 24G cap). The
  comparator-landmark note now reads **STALE at 134 commits** (> the
  100 threshold; report-only) — stands escalated for the operator's
  merge step, as at U8–U14.

## A4-U16 — the layer-C design slice + the FrameSim probe + the depth-2 and drop arms + the stepLeader census (2026-08-25, same worker, coordinator-dispatched; the U15 verdict accepted, route policy set in docs/2026-08-25_campaign-layerc-design.md §5-A1)

- 2026-08-25 SELF-RE-VERIFICATION (U15's top claims, fresh probes,
  all PASS — same-worker continuation per the coordinator's dispatch):
  - tip clean: `git status` clean on `campaign-arc4`; `git rev-parse
    HEAD` = `d6f0286ec691d156feaf82614dde8b3795c143b4` (the U15 gate
    tip). 89G free at launch; every build `GOLEAN_MEM_MAX=48G
    scripts/capped`.
  - fresh capped proofs+Audit build: "Build completed successfully
    (520 jobs)." exit 0 — matching U15's record.
  - `#print axioms` fresh probe (`AxSfHb` re-run, verbatim): the
    stepFollower_heartbeat family [propext, Classical.choice,
    Quot.sound]; sfhbW1_out / sfhb_post_absOutbox [propext,
    Quot.sound] — matching U15's record exactly.
- 2026-08-25 Slice 1 (501c38f0) — **THE SEAM-NOTE §4c AMENDMENT +
  THE FrameSim-STRENGTHENING PROBE** (design; the layer-C note is
  cited as the design of record, never duplicated):
  - §4c records the BINDING wave-3 arm conventions (literal-chain
    route; statement form; Type-cell + off-{61,65} fixture rules;
    the mandatory er readout; the norm-wrap read-the-literal rule;
    counts-as-defs) and the round-shape consequence.
  - **FLAG raised to the layer-C C1 design gate (refinement, not
    divergence): the round lemma's honest premise under the literal
    route is FIXTURE-FAMILY MEMBERSHIP** (canonical symbolic state +
    valuation + placement), with `absState σ = some N` as the
    projected READOUT — the layer-C §3 carried relation `R` must be
    the stronger form; the round-lemma statement should be R-form
    from day one.
  - **THE PROBE** (charter-commissioned, probe-only): surface =
    12,661 lines / 22 Frame files, ~43 producing FrameSim sites but
    only ~6 field-by-field constructors (everything else threads
    packaged relations). Trial `FrameSimC` (+C1 completeness) with
    `setBaseC` + zero-seed: clean, 14 proof lines, sub-second warm.
    **DESIGN FINDING: C1 alone is lookup-determination only; the
    literal re-entry payoff needs C1 + C2, the INSERTION-POINT shape
    clause** (`σF.heap = ren(take n₀) ++ fr ++ ren(drop n₀)` —
    preserved by both machine mutation kinds: base-keyed set is
    position-preserving, alloc appends, nothing deletes). Estimate:
    **≈2 units nominal, 3 at risk** (risk in StepSim's induction +
    StrictOps) = borderline-OVER the ≤2-unit line → **STAY LITERAL
    until the MsgApp-arm trigger; commission with the C1+C2 design
    then** (U15's route (a) as sketched, C1-only, would NOT have
    sufficed — the probe's contribution).
- 2026-08-25 Slice 2 (5136b95a) — **THE stepFollower × MsgProp
  DROP-ARM EQUATION** (`SfPdEquation.lean` + generated `SfPdLit.lean`,
  the printer's 14th consumer; census-first per U15 slice 1):
  - **The CHOICE-FREE arm** (254 steps; the first arm equation whose
    ∀-stream premise has NO consumed prefix) and **the
    dispatch-complement extension's FIRST PROVED CONSUMER**: the
    fixture carries `staticComplementFull` live (the walk derefs
    cell 17 at step 232; the U15 control run without the block
    sticks — fail-closed), and the shipped er conclusion IS the
    ErrProposalDropped box over payload 65 (renameCell-fixed: 65
    below every consumer na₀).
  - Fixture family: `r.lead = 0` CONCRETE (the branching
    precondition — bf31's x₂ forced to `lit 0`), typ 2; **Vote
    survives RAW `var 1` (wrap depth ZERO — no raft-struct store on
    the drop path, generator-probed per §4c), so the readout carries
    NO range side condition** — the first wrap-free scalar readout.
  - Generator γ==machine at Vote 7/9/1023; ELEVEN conclusions
    (message typ 2 record; er = the drop box; both outboxes EMPTY;
    log/lead/Vote/Term preserved); alloc PRIMARY + identity +
    witness (EMPTY stream). **GREEN ON THE FIRST FULL CHECK: 27 s
    module, 522 jobs**; axioms classical trio (probe `AxSfPd`,
    verbatim); hatch 0/0.
- 2026-08-25 Slice 3 (8b401f11) — **THE stepCandidate × MsgHeartbeat
  DISPATCH-ARM EQUATION: THE FIRST DEPTH-2 ARM** (`SCHbEquation.lean`
  ~850 lines + generated `SCHbLit.lean` 904 KB — the printer's 15th
  consumer and second-largest literal; generator `SCHbGen.lean` with
  a staged crossing-classification walk):
  - **The Bf31 chain machinery reused VERBATIM at the dispatch
    fixture** — `uρ`/`uρ'`, `uKey1/2/3`, `uKeyV1-4`,
    `uCrossPick/Stop/Sort`, `stepFn_pick_transport`, `uCands1` (the
    born Intn map at base 96 holds bf31's exact candidate data) and
    `bc31Cands3` (the prs map at the SHARED fixture cell 33) — plus
    the SfHb spill template: **8 windows [983, 183, 28, 28, 28, 3,
    3620, 89] + 7 crossings (4 picks, range-stop, sort collapse,
    spill) = 4,969 steps / FIVE choices, the U14/U15 census to the
    step.**
  - Census-first fixture finding: `stepCandidate` computes
    `myVoteRespType(r.state)` UP FRONT — symbolic x₃ quits q1Branch
    at step 20, so **the candidate family is state-CONCRETE (= 1)**
    by the same forcing pattern as the drop arm's lead.
  - Generator validated γ==machine at THREE full 5-choice tuples
    ((0,0,0,0,0)/(3,1,1,0,5)/(9,2,1,1,31)) BEFORE any theorem; wrap
    depth probed exactly (`SCDepth`): Vote = **norm¹⁴(var 1)**
    (becomeFollower's store-heavy spine), collapsed by
    `unrm_id hvote 14` (the BfEquation helper — reused, not
    re-derived).
  - TWELVE conclusions incl. **THE DEPTH-2 HEADLINES: state 1 → 0
    (the candidate falls back to follower) and lead := m.From = 2**
    — the dispatch-visible transitions of a heartbeat received
    mid-candidacy — plus the SAME `specHeartbeatResp 1 2 0` record
    as the sF arm (the response is role-independent, now a THEOREM
    pair), er = nil, log preserved, Vote/Term unchanged.
  - **GREEN ON THE FIRST FULL CHECK: 138 s module, 524 jobs**
    (SCHbLit 4.9 s); axioms classical trio; the pick/window links
    [propext, Quot.sound] (probe `AxSCHb`, verbatim); hatch 0/0.
  - What-this-taught-us (slice 3): the depth-2 arm was pure
    ASSEMBLY — zero new machinery, every crossing class landed, and
    the only two findings were fixture-family forcings discovered by
    probe in minutes (state-concrete; wrap depth 14). The walked
    route's cost honestly scales: 4,969 steps → 138 s (vs 1,710 →
    50 s; ~linear). The round lemma (driver glue + one arm) is one
    more ring of exactly this shape — the dress rehearsal PASSED.
- 2026-08-25 Slice 4 (probe-only, as chartered) — **THE stepLeader
  CENSUS** (probe `StepLeaderProbe.lean`; leader fixture state = 2,
  FULL static block, caller cells [66,69); every number from runs):
  - **sL×MsgBeat (typ 1): COMPLETES — 3,362 steps, FOUR choices at
    [288, 317, 346, 1854]**, na 98→291, er = nil, msgs =
    [Heartbeat(s) to the peers], maa = [], lead = 1 (self), state 2
    preserved, log preserved, ZERO static reads. The bcastHeartbeat
    arm is the next cheap equation candidate (3 Visit picks + 1 more
    crossing; all landed classes by shape).
  - **sL×MsgProp (typ 2): the machine PANICS at step 311** — the
    SUBJECT's own `Panicf` on an empty-Entries MsgProp
    (raft.go stepLeader's first check) — CORRECT subject behavior at
    this fixture, not a machine defect: the sL×Prop family needs a
    non-empty-Entries message fixture (the La entry-cell pattern).
  - **sL×MsgAppResp (typ 4): panics at 4,043** (3 choices consumed
    at [1097, 1215, 1333]; static 23/ErrCompacted read LIVE at
    2715); **sL×MsgHeartbeatResp (typ 9): panics at 2,876** (static
    23 at 1551); **sL×MsgTransferLeader (typ 13): panics at 3,167**
    (static 23 at 1842). All three walk deep into the
    sendAppend/storage path before panicking — the leader-side
    families need a Match/Next-consistent tracker + storage fixture
    (a named fixture-design task, NOT a machinery gap; the
    ErrCompacted reads confirm the U12 complement is live on the
    leader path too).
  - Census honesty note: the walker reports these as "step on
    terminal panicked configuration" — the machine reached
    `.panicked` earlier and the walker kept stepping; the recorded
    step counts are the walker's terminal contact, the panic sites
    are earlier. A future walker improvement (stop at `.panicked`
    with the panic step index) is a probe-side nicety, recorded
    here.

### PROMOTION LEDGER updates (A4-U16)

- **The literal-chain reuse instrument row (U15)** — REFINED by the
  probe: the viable design is C1 (completeness) + C2 (insertion-point
  shape); estimate ≈2 units nominal / 3 at risk; trigger unchanged
  (MsgApp arms × the Hae REJECT window). The trial artifacts live in
  `artifacts/probe/FrameSimStrengthProbe.lean`.
- The Bf31 chain machinery (uρ/uKey/uCross/pick-transport/candidate
  packs) — **first cross-fixture consumers** (SCHbEquation): the
  helpers were fixture-independent by construction, as the U4-U6
  design intended; zero adaptation needed.
- The literal printer — 14th/15th consumers (SfPdGen, SCHbGen; the
  staged crossing-classification walk in SCHbGen is the new
  multi-crossing generator template for round-lemma spans).
- NEW ROW: **the leader-side fixture pack** (Match/Next-consistent
  tracker + storage with retrievable entries) — consumers: the
  sL×AppResp/HbResp/Transfer families (censused panics), the
  sL×Prop family (+ non-empty Entries message). Blocks leader-side
  arm equations only; sL×Beat needs none of it.
- The `stepFn_atomRead_transport` wrapper row: unchanged.

## A4-U16 exit (2026-08-25, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the U15 gate tip
d6f0286e: 4 (501c38f0 slice 1, 5136b95a slice 2, 8b401f11 slice 3) +
this log/exit commit; no coordinator commits interleaved (checked:
`git log d6f0286e..HEAD --oneline` = the above). Full proofs+Audit
green: **524 jobs** (520 + SfPdLit + SfPdEquation + SCHbLit +
SCHbEquation). Kit pins: +0. Hatch grep over every new module: 0.

**Deliverable state vs the U16 charter (coordinator-adjusted):**
1. THE DESIGN SLICE — **DELIVERED** (§4c conventions binding; the
   R-form FLAG raised to the C1 design gate; the FrameSim probe
   sized with a design refinement — C1+C2 — and a go/no-go verdict:
   borderline-over, STAY LITERAL, trigger unchanged).
2. sC×MsgHeartbeat — **DELIVERED, green on the first full check**:
   the first depth-2 arm, 4,969 steps / 5 choices / 8 windows / 7
   crossings, the Bf31 machinery's first cross-fixture reuse, the
   round lemma's dress rehearsal (verdict: pure assembly, ~linear
   cost).
3. THE DROP-ARM EQUATION — **DELIVERED, green on the first full
   check**: choice-free, the extension's first proved consumer, the
   first wrap-free scalar readout.
4. THE stepLeader CENSUS — **DELIVERED, probe-only**: one completing
   arm (Beat 3,362/4 — the next cheap equation), the subject's own
   empty-Prop panic correctly exhibited, and the leader-side fixture
   pack named as the debt for the other three arms.

**Open gaps carried (none counted):** GAP-V1-2/-4/-5, GAP-U1-W1,
GAP-V2-1 wave-3 condition, GAP-V2-2, MemoryStorage.Entries spec
design, the multi-element spill variant, the atom-re-read watch-item
(checked: no inter-spill atom reads in this unit's censuses),
message-field symbolism on demand — all unchanged; U16 adds: the
leader-side fixture pack (ledger row); the walker's panicked-config
reporting nicety (probe-side).

**A4-U17 CHARTER (proposed):** (1) the sL×MsgBeat equation (censused
3,362/4, zero statics, all landed classes — the leader side's first
arm, completing a full follower/candidate/leader arm triple for the
heartbeat round-kind); (2) the leader-side fixture pack design +
re-census of sL×AppResp/HbResp (the fixture-design task from the
ledger; census decides whether their equations are wave-3 or
deferred); (3) budget permitting: the sF×MsgProp FORWARD arm
(1,272/1, the send-only shape) — closing stepFollower's censused
arms — or the Step() top-level dispatch census (the last ring before
the round lemma). Rotation note: this worker is at ~560k tokens at
exit-entry time — U17 should start FRESH (split discipline; the
census numbers + §4c conventions are the handoff).

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1); the comparator-landmark STALE flag
stands escalated from U8–U15.

- 2026-08-25 A4-U16 gate follow-up (same-commit convention): unit-end
  gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the
  exit tree — **RESULT: PASS, exit 0** (`artifacts/ci-arc4-u16.log`,
  gitignored; 22 ok steps + the two sanctioned no-diff notes — this
  unit touched `proofs/GoLeanProofs/Specs/Raft/{SfPdLit,SfPdEquation,
  SCHbLit,SCHbEquation}.lean` + the aggregator + the seam note §4c +
  arc-4 docs + gitignored probes only; no runtime code, no Corpus/,
  no baselines/, zero Kit pins, zero edits to shipped module
  STATEMENTS). Gate staggered behind the `free -g` guard (91G free ≥
  24G cap). The comparator-landmark note now reads **STALE at 139
  commits** (> the 100 threshold; report-only) — stands escalated for
  the operator's merge step, as at U8–U15.

## A4-U17 — THE sL×MsgBeat EQUATION (the heartbeat triple CLOSES) + the leader-side fixture pack + THE Step() TOP-LEVEL CENSUS (2026-08-25, successor worker, coordinator-dispatched)

- 2026-08-25 SELF-RE-VERIFICATION (U16's top claims, fresh probes,
  all PASS — fresh worker per the U16 rotation note):
  - tip clean: `git status` clean on `campaign-arc4`; `git rev-parse
    HEAD` = `5f731c171a07347bd43c2efb220dfa8617816f60` (the U16 gate
    tip). 91G free at launch; every build `GOLEAN_MEM_MAX=48G
    scripts/capped`.
  - fresh capped proofs+Audit build: "Build completed successfully
    (524 jobs)." exit 0 — matching U16's record.
  - `#print axioms` fresh probes (`AxSCHb`/`AxSfPd` re-run,
    verbatim): stepCandidate_heartbeat family and
    stepFollower_propDrop family [propext, Classical.choice,
    Quot.sound]; scPick3_step/scW1_out/sc_post_absOutbox and
    sfpdW1_out/sfpd_post_er [propext, Quot.sound] — matching U16.
  - hatch grep (`sorry|native_decide|^axiom`) over
    `proofs/GoLeanProofs/Specs/Raft/`: **0**.
- 2026-08-25 Slice 1 (9fb5deb8) — **THE IN-PLACE APPEND TRANSPORT**
  (`Sym/SpillTransport.lean`, additive; the U12 atom-re-read
  watch-item FIRES for the first time):
  - The sL×Beat census's 4-choice count concealed a NEW crossing
    class the machine walker cannot show: the second `r.send`'s
    append re-reads the FIRST send's spilled `msgs` handle, which
    rides as valuation atom 0 — the mirror quits at `asSlice` on the
    atom. The machine step is deterministic (capacity-sufficient
    in-place append: one backing write at index `off+len`, one
    handle write, NO choice, NO alloc) — but whether that branch is
    TAKEN depends on the earlier spill's realized capacity, exactly
    as the watch-item predicted ("a cap-consuming re-read between
    spills is NOT choice-independent").
  - Landed: `applyStmtOp_append1_inplace_at` (the apply at the
    in-place branch; the one-element `forIn` reduced via
    `Array.forIn_toList`), **`stepFn_appendInPlace_transport`** (the
    γ-image step; the old handle enters as a general mirror value
    pinned by a `hold` premise — an ATOM at the motivating fixture),
    `storeLoc_spilled_backing_index1` (the symbolic-capacity backing
    write: peel one replicate pad under `2 ≤ n`, pointer-typed
    renormalization is the catch-all identity —
    `normalizeListWith_ok_id`), and the §3.3 witness on concrete
    cells. All [propext, Quot.sound]. LINEAGE: the same
    symbolic-execution crossing classic as the pick/spill transports.
    Further consumers: every multi-send arm (the MsgApp broadcast
    arms append once per peer — the k-th-index generalization is
    named consume-on-demand).
- 2026-08-25 Slice 2 (800e260e) — **THE stepLeader × MsgBeat
  DISPATCH-ARM EQUATION** (`SlbEquation.lean` + generated
  `SlbLit.lean` 1.8 MB — the printer's 16th consumer):
  - **THE HEARTBEAT ROUND-KIND'S ARM TRIPLE IS COMPLETE: sF
    (U15) / sC (U16) / sL (this unit)** — the full arm set for
    layer C's first round lemma (C2's heartbeat round, both roles +
    the leader's beat).
  - The chain: 8 windows **[288, 28, 28, 28, 3, 1474, 1393, 113]**
    + 7 crossings (3 Visit picks over the prs map at 33 —
    `bc31Cands3`/`uKey1-3`/`uKeyV2-4` REUSED VERBATIM — range-stop,
    sort collapse, the msgs spill, THE IN-PLACE SECOND APPEND) =
    **3,362 steps / FOUR choices — the U16 census to the step**.
    Generator `SlbGen.lean` (adaptive staged crossing
    classification); γ==machine at FOUR 4-tuples incl. the cap-2
    boundary c₄ = 30 BEFORE any theorem; the c₄ = 29 RE-SPILL
    divergence machine-witnessed (5 choices consumed — the residual
    family's evidence).
  - Fixture-family firsts: **ALL FOUR raft scalars ride SYMBOLIC**
    (the path reads none of them — readouts for state/lead/Vote
    carry range side conditions at wrap depth 2, generator-probed
    per §4c); **the first choice-VALUE side condition**
    (`2 ≤ hhCap c₄`): the in-place branch needs the spill's realized
    capacity ≥ 2. The complement (`c₄ % 32 = 29`, cap 1) is **the
    RE-SPILL residual family** — a different 5-choice chain, NOT
    covered, logged as a named debt (below).
  - Conclusions (12): pre absMessage typ 1; **msgs gains EXACTLY
    [specHeartbeat 1 2 0, specHeartbeat 1 3 0]** (both Type-8
    heartbeats in sort-collapsed peer order — send order is
    pick-order-INDEPENDENT); maa empty; er nil; log preserved;
    state/lead/Vote/Term unchanged — **the leader stays the
    leader**, as a theorem over symbolic state.
  - **GREEN: 125 s module, full proofs+Audit "Build completed
    successfully (526 jobs)."**; axioms classical trio on the
    equations, [propext, Quot.sound] on links/picks/in-place (probe
    `AxSlb`, verbatim); hatch grep over the three touched modules 0.
  - What-this-taught-us (slice 2, elaboration): **a transport
    premise that DETERMINES unification variables must be a
    pre-stated `have`, never an inline `(by with_unfolding_all
    rfl)`** — the inline `hold` elaborated against unassigned metas
    and diverged at `whnf` (28 min grinding; ANTI-GRINDING fired,
    killed, section-bisected in ~110 s increments, pinned to the
    exact token by a 2M-heartbeat cap). With the explicit `have` the
    same proof is free. Everything else was assembly; the walked
    route's cost stays ~linear (3,362 steps → 125 s).
- 2026-08-25 Slice 3 (probe-only, as chartered) — **THE Step()
  TOP-LEVEL CENSUS** (`StepTopProbe.lean`; the outermost dispatch,
  raftsubject/raft/raft.go:1108; fixture = the census geometry with
  the raft's `step` FIELD set per-state to its funcVal — the
  become-assignment — and an optional real Term cell 56):
  - **The routing map**: Step = nil-check → TERM switch (m.Term = 0
    local / > r.Term step-down / < r.Term ignore-or-respond) → TYPE
    switch (MsgHup / storage resps / MsgVote+PreVote / default →
    `r.step(r, m)` — the callVal dispatch through the func field).
  - **THE COMPOSITION HEADLINE: on every local default route the
    Step glue is a CONSTANT 420-step prefix + 33-step suffix (453
    total), zero choices, zero statics, role-independent** — each
    landed arm equation is consumed EXACTLY (steps and choice-pop
    positions match to the step, offset +420):
    - Step/L/Beat: 3,815 = 453 + **3,362**, pops [708,737,766,2274]
      = the slb pops + 420; the two heartbeats verbatim → consumes
      **stepLeader_beat_eq** (this unit).
    - Step/F/Hb: 2,163 = 453 + **1,710**, pop 2001 = 1581 + 420 →
      consumes **stepFollower_heartbeat_eq**; response record
      verbatim (specHeartbeatResp 1 2 0).
    - Step/C/Hb: 5,422 = 453 + **4,969**, pops = SCHb's + 420 →
      consumes **stepCandidate_heartbeat_eq**.
    - Step/F/Prop: 1,725 = 453 + **1,272** (the censused forward
      arm), forwarded typ-2 record to lead 2.
  - The non-default paths, censused:
    - **step-field NIL (the born state): PANICS** at the callVal on
      nil — fail-closed; Step()'s fixture family REQUIRES the
      become-assignment (walker-terminal 433; panic-site earlier).
    - **term-BUMP** (m.Term 2 > r.Term 0, typ 8): 6,468 / 5 choices
      — becomeFollower(2, From) INSIDE Step, then the sF×Hb span at
      the Term-2 family (post: Term 2, Vote reset 0, response term
      2); composes bf-spine + SfHb machinery at a NEW fixture
      family (not a landed-equation instance — the Term-2 variants
      are new fixture families of landed shapes).
    - **term-DOWN ignore** (r.Term 5, m.Term 1, checkQuorum false):
      791 / 0 choices, er nil, NO sends, state untouched — a cheap
      CHOICE-FREE Step-only family (returns inside Step, no arm).
    - **MsgHup** (typ 0): 10,709 / **12 choices** — the
      hup→campaign election spine (msgs = two MsgVote t1, maa =
      the self MsgVoteResp); the campaign round-kind's span, NOT
      yet equation-covered (layer C's C4 item).
  - **This completes the composition map to the top of the call
    tree**: driver → Step (453 glue) → {stepLeader, stepFollower,
    stepCandidate} → landed arm equations. C1's remaining input
    delivered.
- 2026-08-25 Slice 4 (probe-only, as chartered) — **THE LEADER-SIDE
  FIXTURE PACK** (`SLFixPackProbe.lean`; the U16 ledger row; ONE
  general pack, two orthogonal pieces per the further-consumers
  rule):
  - **The pack**: (i) `trkPatch` — Progress cells get Match := 1,
    Next := 2 (consistent with the fixture log: lastIndex 1,
    committed 1 — sendAppend from Next 2 reads term(1) and an empty
    entries(2..), no ErrCompacted, no snapshot path); (ii) message
    entries cells 57/58 (one fresh *raftpb.Entry, Term/Index zero —
    appendEntry assigns them) + optional real Index cell 59;
    (iii) **ldT = 0** for the Prop accept path (found by census:
    the standing fixture's leadTransferee = 5 makes the subject
    return ErrProposalDropped — transfer-in-progress, static 17 =
    the box — CORRECT behavior and its own choice-free drop family,
    394/0).
  - **Re-censuses — ALL FOUR remaining leader arms COMPLETE on the
    pack** (every number from runs; zero statics on every
    completing run):
    - **sL×Prop FULL (ents + trk + ldT0): 12,831 / 6 choices at
      [2113, 3294, 3423, 3452, 3481, 7712]** — the complete
      proposal pipeline: er nil, unstable gains (2,0), msgs =
      MsgApp(s) (typ 3, logTerm 1 index 1 commit 1), **maa =
      [MsgAppResp typ 4 to SELF, index 2] — the first arm with a
      non-empty msgsAfterAppend**. Both pack pieces provably
      needed: ents-only (ldT 0, no trk) still panics in
      sendAppend (static 23/ErrCompacted at 4362 → the nil-snapshot
      path — Next 1 vs storage firstIndex 2).
    - **sL×AppResp accept (trk + Index 1): 7,677 / 4 at
      [1111, 1229, 1347, 5074]** — MaybeUpdate + sendAppend, msgs =
      [MsgApp to 2]; **sL×AppResp no-op (Index nil): 795 / 0** —
      choice-free.
    - **sL×HbResp (trk): 4,381 / 1 at 3915** — msgs = [MsgApp to 2].
    - **sL×Transfer (trk): 2,512 / 1 at 2390** — msgs =
      [MsgTimeoutNow typ 14 to 2].
    - Control: **sL×Beat on the patched tracker = 3,362 / 4 at THE
      SAME pops** — chain shape is pack-invariant; only the record's
      commit changes (0 → 1 = min(Match, committed)); the landed
      equation's fixture (unpatched) is untouched.
  - Ledger row RESOLVED into census facts: the leader arms are
    fixture-design-unblocked; their equations are wave-3 assembly
    (all crossing classes landed — picks/spill/in-place; the Prop
    arm adds an unstable-entries append spill, the La shape).

### PROMOTION LEDGER updates (A4-U17)

- **The transport family — NEW MEMBER `stepFn_appendInPlace_transport`**
  (+ `storeLoc_spilled_backing_index1`): the atom-re-read row's
  wrapper threshold RESOLVED differently than predicted — the third
  instance was not a len strict-op composition but a full crossing
  class; the k-th-index backing-write generalization is
  consume-on-demand (first candidate: the MsgApp broadcast arms).
- The literal printer — 16th consumer (SlbGen; the ADAPTIVE staged
  crossing-classification walk — classify-by-shape instead of a
  hardcoded stage list — is the new generator template; supersedes
  SCHbGen's fixed stages for multi-class chains).
- **NEW ROW: the RE-SPILL residual family** (`c₄ % 32 = 29` at any
  two-append arm): a 5-choice chain (machine-witnessed divergence in
  SlbGen). Consumers: sL×Beat completeness (if layer C ever needs
  the full choice envelope of the heartbeat round rather than the
  ∀-prefix-with-side-condition form), and every future multi-send
  arm. Cheap when needed: one more literal chain at cap 1.
- The leader-side fixture pack row (U16) — **RESOLVED to censuses**
  (slice 4); the remaining debt is per-arm EQUATIONS, not fixtures.
- The `stepFn_atomRead_transport` wrapper row — CLOSED: superseded by
  the in-place transport landing (the third instance took a
  different, stronger lift).

## A4-U17 exit (2026-08-25, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the U16 gate tip
5f731c17: 2 (9fb5deb8 slice 1, 800e260e slice 2) + this log/exit
commit; no coordinator commits interleaved (checked: `git log
5f731c17..HEAD --oneline` = the above). Full proofs+Audit green:
**526 jobs** (524 + SlbLit + SlbEquation). Kit pins: +0. Hatch grep
over every new/touched module: 0. Probes (gitignored): SlbGen,
StepTopProbe, SLFixPackProbe, AxSlb, InPlaceDev/2, SlbBisect*.

**Deliverable state vs the U17 charter:**
1. THE sL×MsgBeat EQUATION — **DELIVERED, the heartbeat round-kind's
   arm triple (sF/sC/sL) IS COMPLETE** — said so per the charter:
   layer C's first round lemma has its full arm set. One new
   crossing class landed en route (the in-place append transport —
   the atom watch-item's first live instance, now closed INTO the
   transport family).
2. THE LEADER-SIDE FIXTURE PACK — **DELIVERED with completion**: all
   four remaining leader arms census to STOP on the pack (Prop
   12,831/6 with the first non-empty maa; AppResp 7,677/4 + 795/0;
   HbResp 4,381/1; Transfer 2,512/1); the ldT-drop family found and
   recorded; no next debt beyond per-arm equations (named ledger
   rows).
3. THE Step() TOP-LEVEL CENSUS — **DELIVERED**: the routing map with
   the constant-glue decomposition (453 = 420 prefix + 33 suffix,
   role-independent, choice-free) and EXACT consumption of all four
   landed arm equations; the nil-step panic, term-bump, term-down,
   and MsgHup spans censused. The composition map now reaches the
   top of the call tree — C1's remaining input.
4. Budget item (sF×MsgProp forward / sL×AppResp equation): NOT
   attempted — the unit closed at the census boundary (rotation
   discipline).

**Open gaps carried (none counted):** GAP-V1-2/-4/-5, GAP-U1-W1,
GAP-V2-1 wave-3 condition, GAP-V2-2, MemoryStorage.Entries spec
design, the multi-element spill variant, message-field symbolism on
demand — all unchanged; the atom-re-read watch-item is CLOSED (fired,
landed as machinery); U17 adds: the RE-SPILL residual family (ledger
row); the walker panicked-config nicety unchanged (probe-side).

**A4-U18 CHARTER (proposed) — C1, the layer-C opening unit** (the
expected successor per the ladder; its inputs are now complete:
§4c conventions, the R-form flag, the U14 dispatch map, and this
unit's Step() census/decomposition). C1 per the design of record
(campaign worktree, `docs/2026-08-25_campaign-layerc-design.md` §6):
(1) the driver-span census (A2's kill-point: loop head, action
choice, harvest, checker — one census unit in the StepTopProbe
pattern, now with the Step glue known constant); (2) the round-lemma
STATEMENT in R-form (fixture-family membership + absState readout —
the §4c flag, binding), witnessed on the heartbeat round; (3) the A4
adapter probe (specRound ↔ T3 lattice net-step decomposition — the
one assumption whose failure reshapes the design). C1 is a DESIGN
GATE: its verdict on A1-A4 revises the layer-C note before C2. What
C1 still lacks from below: nothing structural — the heartbeat round's
arms are proved (this unit), the glue is censused constant, and the
checker span awaits its own census inside the driver-span item.
Budget permitting after the gate: the sF×MsgProp FORWARD-arm equation
(1,272/1, censused; closes stepFollower's censused arms) as C2 prep.
Rotation note: this worker is at ~420k tokens at exit-entry — healthy
margin; U18 may continue here or rotate per the coordinator.

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1); the comparator-landmark STALE flag
stands escalated from U8–U16.

- 2026-08-25 A4-U17 gate follow-up (same-commit convention): unit-end
  gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the
  exit tree — **RESULT: PASS, exit 0** (`artifacts/ci-arc4-u17.log`,
  gitignored; 22 ok steps + the two sanctioned no-diff notes — this
  unit touched `proofs/GoLeanProofs/{Sym/SpillTransport.lean,
  Specs/Raft/{SlbLit,SlbEquation}.lean}` + the aggregator + arc-4
  docs + gitignored probes only; no runtime code, no Corpus/, no
  baselines/, zero Kit pins, zero edits to shipped module
  STATEMENTS). One fail-closed false positive en route, recorded for
  successors: the escape-hatch preflight greps the token `admit` and
  correctly-by-its-rules flagged the word inside a docstring
  (fix commit f89e3015 rewords the prose; no code change) — the
  first PASS-blocking prose token in the arc; keep hatch tokens out
  of comments. Gate staggered behind the `free -g` guard. The
  comparator-landmark note now reads **STALE at 144 commits** (> the
  100 threshold; report-only) — stands escalated for the operator's
  merge step, as at U8–U16.

## A4-U18 — C1, THE LAYER-C DESIGN GATE: the driver-span census + the R-form round statement & heartbeat-round witness + the A4 adapter probe (2026-08-25, successor worker, coordinator-dispatched; the design of record contact-tested per its own charter)

- 2026-08-25 SUCCESSOR RE-VERIFICATION (U17's top claims, fresh
  probes, all PASS — fresh worker per the U17 rotation note):
  - tip clean: `git status` clean on `campaign-arc4`; `git rev-parse
    HEAD` = `5d3e70ae707e7b4c61dc3cf1694da975c3c45e31` (the U17 gate
    tip). 89G free at launch (≥ 40G floor); every build this unit
    `GOLEAN_MEM_MAX=48G scripts/capped`.
  - fresh capped proofs+Audit build: "Build completed successfully
    (526 jobs)." exit 0 — matching U17's record.
  - `#print axioms` fresh probe (`AxSlb` re-run, verbatim):
    stepLeader_beat_eq_alloc / stepLeader_beat_eq / _witness /
    slb_full_span / slbSpill_step [propext, Classical.choice,
    Quot.sound]; slbInplace_step / slbPick3_step / slbW1_out /
    slb_post_absOutbox and stepFn_appendInPlace_transport (+ witness)
    / storeLoc_spilled_backing_index1 [propext, Quot.sound] —
    matching U17's record exactly.
  - hatch grep (`sorry|native_decide|^axiom`) over
    `proofs/GoLeanProofs/Specs/Raft/`: **0**.
- 2026-08-25 Slice 1 (probe-only) — **THE DRIVER-SPAN CENSUS**
  (charter item 1 = A2's test; probe `DrvSpanProbe.lean`, event TSV
  `artifacts/drvspan-events.tsv` (gitignored); an instrumented
  compiled walk of the PINNED twin (`twinLowered`, entry
  `twinChoiceVerdict`) from the seeded start on the canonical
  all-zero stream; every number below from the walk):
  - **THE FULL COMPLETING RUN, REPLICATED TO THE STEP**: 711,616
    subject steps (+ the 1,382-step `$pkginit`), 345 choices
    consumed of 25,000, final na = heap = 36,376, observable
    values = (viol 0, claims 1, committed 6, complete 1, floor 1) —
    **Arc 2's recorded minimal completing fuel and heap growth
    reproduced exactly** (raft-campaign-log Arc-2 unit 1: 711,616 +
    1,382; 103→36,376) — an independent cross-verification of the
    Arc-2 measurement AND the identification of its stream (all
    zeros).
  - **Structure**: pre-loop driver init (newTwin + 3×NewRawNode) =
    81,261 steps / 171 choices / na 103→4,965 (heap at the first
    loop head: ~6,073 cells, na 6,073 after the campaign);
    campaign = 20,424 steps / 22 choices; then **31 rounds**:
    28 deliver + 2 propose (29,408 / 29,642 steps) + the campaign.
    Deliver-round kinds (arms observed in-span): 2 MsgVote
    (becomeFollower+vote; 19,611 / 19,973), 1 MsgVoteResp-win
    (poll→becomeLeader→appendEntry→bcastAppend; 33,893), 12 MsgApp
    (handleAppendEntries; 18.6k–24.3k), 6 MsgAppResp
    (maybeCommit/sendAppend; 13.4k–33.9k), 7 no-op arms
    (7.7k–17.9k). Round spans 7,720–33,903 steps — **3–15× the
    453+arm arithmetic the design's §2 sketch implied**.
  - **Phase decomposition** (representative MsgApp round @182,882,
    span 18,591): deliverIdx prologue 133 → RawNode.Step shell 383 →
    raft.raft.Step glue+arm 5,826 (handleAppendEntries at +1,320) →
    **HARVEST 9,691** (HasReady 800; Ready/readyWithoutAccept/
    applyUnstableEntries ~1,500; acceptReady ~2,900; Advance with a
    NESTED `raft.raft.Step` — the MsgStorageAppendResp local arm —
    ~2,000; second Ready round 1,290) → driver suffix+glue 4,558
    (projection ~1,900 incl. liveCount, says, loop-head rebuild +
    pick + trace itoas). **The harvest ring is the largest
    un-equationed span in every round.**
  - **THE DRIVER GLUE GROWS**: last-projection→next-deliverIdx =
    3,578 steps at net=2 → 7,250 at net=28 (**+141 steps/net entry**,
    fit over 26 entries) — the live-map REBUILD and `liveCount` walk
    the FULL net slice (dead entries included) every round, and net
    is never compacted. The per-round driver span is therefore
    |net|-DEPENDENT, not fixed code.
  - **THE CHECKER IS NOT THE BALLOON** (the charter's load-bearing
    question): `apply` (S3 monotonicity + S2 byIndex/got map ops) =
    324–463 steps ×9 occurrences; S1 (leaderOf) rides inline in
    harvest; `complete()` = 803–2,127; `projection` ≈ 1,900–2,300.
    All small, all walkable.
  - **REACHABILITY REFUTATION (the census headline)**: ZERO
    heartbeat events in the entire run — and structurally, the
    driver NEVER calls `Tick` (twin-chdriver.go: ticks not driven),
    `tickHeartbeat` is the only MsgBeat source and `bcastHeartbeat`
    the only MsgHeartbeat source, so **the heartbeat round-kind is
    unreachable under EVERY choice stream**. Likewise sF×MsgProp
    forward/drop: only node 1 ever proposes, and it is leader
    whenever quiescent (campaign(1) precedes every propose; no
    ticks ⇒ no elections past term 1). **The landed dispatch-arm
    equations (sF×Hb U15, sC×Hb U16, sL×Beat U17, sF×PropDrop U16)
    are all T1-VACUOUS** — valid machinery and statement-form
    vehicles, but none is on T1's load-bearing path. T1's reachable
    arm set: MsgHup/campaign spine, MsgProp leader-accept, MsgApp
    (Hae families), MsgAppResp (maybeCommit/sendAppend), MsgVote,
    MsgVoteResp (poll/becomeLeader), MsgStorageAppendResp/ApplyResp
    (harvest-internal) — none arm-equationed yet (handler-level
    Hae/become/La equations are landed; the Step 453-glue census
    covers the shell).
- 2026-08-25 Slice 2 (probe-only) — **THE A4 ADAPTER PROBE** (charter
  item 3; `artifacts/probe/A4AdapterProbe.lean`, ALL LEMMAS GREEN;
  the verdi side mirrored monomorphically with per-def citations to
  `compat/verdi/VerdiCompat/Raft.lean` because VerdiCompat is a
  SEPARATE Lake package golean-proofs does not require — the package
  seam is itself a C1 finding):
  - **`adapter_hb_noAdvance` (~25 lines incl. helpers): the
    heartbeat NO-ADVANCE family squares on the nose** with verdi's
    empty-entries-AppendEntries net-step (pli=0 shoehorn, same-term):
    lead:=m.From ↔ leaderId:=some lid, type Follower ↔ state 0,
    term/vote/log/commit all fixed — "small", exactly as §3 hoped.
  - **`adapter_hb_advance_mismatch` — A4's KILL-POINT, a THEOREM**:
    a concrete commit-ADVANCING heartbeat (the HhAdv family) whose
    projected commitIndex differs from EVERY empty-entries-AE image
    under EVERY shoehorn parameterization (t, lid, pli, plt, c) —
    via `verdi_emptyAE_commit_frozen`: verdi advances follower
    commitIndex ONLY in `haveNewEntries` branches
    (VerdiCompat/Raft.lean:169-201). **And the axis is NOT
    heartbeat-only**: etcd followers advance commit on ANY accepted
    MsgApp including duplicates/empties
    (raftsubject/raft/log.go:129 `commitTo(min(committed,
    lastnewi))`) — the census's 12 MsgApp + 6 MsgAppResp rounds
    carry exactly such commit propagation, REACHABLE and essential
    to S4 completion.
  - **`verdi_rvr_log_frozen` — the election-noop axis**: verdi's
    handleRequestVoteReply never touches the log (all branches), and
    no lattice stage appends at election — while etcd's becomeLeader
    appends the empty entry (raftsubject/raft/raft.go:980-981; the
    census's claims round). The projected log exits verdi's
    reachable set at the FIRST election.
  - Election-safety scoping check (grep evidence): `commitIndex`
    appears 0 times in CandidateEntries.lean and only in
    state-unchanged packaging lemmas in ElectionSpecLemmas — the S1
    chain's CONTENT never consumes the mismatched axis.
- 2026-08-25 Slice 3 (5d3e70ae..this commit, tracked) — **THE R-FORM
  ROUND STATEMENT + THE HEARTBEAT-ROUND WITNESS**
  (`Specs/Raft/RoundStatement.lean` 305 lines + generated
  `RoundHbLit.lean` 7,032 lines / 429 KB — the repr-dump generator
  `artifacts/probe/RoundFixDump.lean`; fixture probes
  `DrvHeadProbe/DrvHead2Probe/TwinRoundFixProbe`):
  - **The loop-head anchor**: the driver for-loop's
    `if round < 400 …` config — machine-verified to recur
    IDENTICALLY (repr-equal, env stable) at consecutive loop heads:
    **the round lemma is SELF-RETURNING** (same config both sides),
    the cleanest possible statement shape.
  - **THE WITNESS FIXTURE, built by doctor+prune** (the new
    fixture-generator template): take the real run's first loop-head
    state (100,553 steps from the seeded start, by computation),
    DOCTOR net/live to one live MsgHeartbeat (typ 8, 1→2, Term 0
    local family, Commit 0 = the Hh no-advance family — the adapter
    square's case), then PRUNE to the round's read-before-write set
    by fail-closed iteration (missing cell ⇒ "unbound GoCore heap
    location" ⇒ add; writes recreate pruned cells soundly):
    **26 cells, found in 19 iterations** — the round fixture is
    ARM-FIXTURE-SCALE, not twin-scale (the frame absorbs the other
    ~6,050 cells; Fam membership never required reachability).
  - **The round WALKS, compiled-verified**: 10,964 steps / 4 choices
    / na 6,079→6,669 / post-heap 617 cells; pruned and unpruned
    walks step-count-identical; abstract delta read through the
    twin lens chain: node 2's raft `lead` 0→1, net gains the LIVE
    MsgHeartbeatResp (typ 9, 2→1) with the heartbeat marked dead,
    checker counters unchanged.
  - **THE SECOND KERNEL WALL, MEASURED** (the unit's route finding):
    the naive kernel replay (`stepFnIter` chunks over the literal)
    EXPLODES — one 1,400-step chunk at the 26-cell fixture reached
    41.2 GB RSS in 90 s and was cgroup-killed at 48 GB — Arc 2 unit
    2's heap-linear kernel NO-GO (2.22 s/step, 157 MB/step at 19k
    cells) reproduced at a TINY heap: the wall is per-step TERM
    growth, not heap width. At ≤300-step chunks the same route is
    fine (~15-20 steps/s, modest memory). **Round-lemma kernel
    replays must ride the MIRROR (symEvalWindow chains — the landed
    equations' instrument, ~30-40 steps/s, no blowup) or ~37-chunk
    naive slicing (~12 min/round, 5 MB literals) — C2's first
    slice; the mirror already supports the driver-glue op classes
    probed (stringFromRune at Mirror.lean:1469, string concat, map
    ops).**
  - **What SHIPS kernel-checked** (full proofs+Audit green: **528
    jobs**; axioms probe `AxRound` verbatim: rhb_glue100/300/
    rhb_glue and RoundFam.self [propext, Quot.sound]; all four
    readouts [propext]; hatch grep over both new modules 0):
    - `RoundFam` (Fam membership = FrameSim placement — the design
      §2 pin: no new relation class; membership is the equations'
      alloc-primary form one ring up) + `RoundFam.self` (identity
      placement via ρT-zero + renameStmt_ρT_zero);
    - `AbsTwinV0`/`absTwinRead` (A3's round-boundary reader v0:
      checker counters + per-node harness shells + the net multiset
      via absMessage) + `absTwinNodeRaft` (the deep
      nodes[i]→rn→raft chain);
    - `RoundLemmaShape` — the R-form statement FORMER
      (placement-quantified pre, self-returning config, choice
      prefix, closure-as-membership conclusion), marked SCAFFOLD
      in-docstring (no proved instance; C2's charter);
    - `rhb_glue100`/`rhb_glue300`/`rhb_glue` — the round's first
      300 steps kernel-replayed (the DRIVER-GLUE head: loop-head
      cond, live-map rebuild, INTO the pick — rhbCh1=[0,0,0,0] →
      rhbCh2=[0,0,0]: **the round's mapIter pick crossing is inside
      the kernel-checked sliver**), composed by stepFnIter_chain;
    - `roundHb_pre_read`/`roundHb_post_read`/`roundHb_pre_lead`/
      `roundHb_post_lead` — the abstract round delta as
      kernel-evaluated readouts over the endpoint literals
      (violations 0→0, net [(true,8,1,2)] → [(false,8,1,2),
      (true,9,2,1)], node-2 lead 0→1), with the docstrings stating
      EXACTLY which links are generator-verified pending C2's
      mirror chain (steps 300–10,964).
  - [AGENT] calls, tagged: (1) census stream = canonical all-zeros
    (matched Arc 2 exactly — cross-verification for free); (2) the
    witness round-kind KEPT heartbeat per charter despite the
    reachability refutation — the form validation is
    round-kind-independent and no reachable arm is equationed yet;
    vacuity stated in the module docstring; (3) the adapter probe
    MIRRORS VerdiCompat locally rather than touching lakefiles (no
    build-wiring change without a coordinator decision); (4) the
    doctor+prune fixture construction adopted as the round
    fixture-generator template (recorded in the ledger); (5) the
    full-round kernel replay STOPPED at the measured wall per
    ANTI-GRINDING — the measurement is the deliverable, the sliver
    ships, the mirror route is C2's (no grinding past the second
    43G kill).
  - What-this-taught-us: (a) a census BEFORE a design commits is
    worth more than the design — three of the six census findings
    (reachability, harvest ring, |net|-growth) invalidate silent
    premises of §2/§6; (b) the read-before-write set of a 10,964-step
    span over a 6,000-cell heap is 26 CELLS — locality is extreme,
    and fail-closed error-driven pruning finds it in minutes (the
    fixture-scale fear that shaped the witness plan was wrong in the
    GOOD direction); (c) the kernel's term-growth wall is
    chunk-length-superlinear — 300 steps cheap, 1,400 fatal — so
    "kernel-replay cost" must always be quoted WITH its chunking.

### THE C1 VERDICT BLOCK (A4-U18 — the design gate's output; the coordinator revises the layer-C note §5/§6 from exactly this block)

- **A1 (statement forms compose; literal route)** — **PASS, and the
  MsgApp cost trigger now FIRES for the C-ladder**: nothing
  contradicts the U15/U16 verdicts. New cost data: real rounds are
  7,720–33,903 steps; the naive kernel replay of round spans is
  measured-dead past ~1,400-step chunks (41.2 GB kill at a 26-cell
  fixture — Arc 2's heap-linear wall, now known to be term-growth,
  not heap width); the mirror route prices a round lemma at ~5-15
  min kernel each at current rates. **Recommendation: commission the
  FrameSim C1+C2 completeness instrument (U16 probe: ≈2 units
  nominal, 3 at risk) BEFORE the general round lemmas, per the
  ledger row's own trigger** — 12 of 28 deliver rounds are
  MsgApp-family, and every one re-walks Hae-scale spans without it.
- **A2 (driver span walkable in the census pattern)** — **REFINE;
  the kill-point consequence fires in a specific form.** The CHECKER
  is small and walkable (apply 324–463; S1 inline; complete
  803–2,127; projection ~1,900–2,300) — never the balloon. The
  balloon is elsewhere: (i) the driver glue is |net|-dependent
  (+141 steps/net entry, measured 3,578→7,250) because the live-map
  rebuild and liveCount walk the full net slice every round — the
  GENERAL round lemma therefore needs SYMBOLIC-NET driver-loop
  lemmas (slice-walk loop invariant — the classic; Go-general kit
  material), not one literal chain per net shape; (ii) the HARVEST
  ring (Ready cycle + nested MsgStorageAppendResp/ApplyResp local
  Step arms) is 9–14k steps/round with NO landed equations — larger
  than the delivered arm in every round; (iii) the pre-loop driver
  init is 81,261 steps / 171 choices — the C3 seed link-pin cannot
  be a naive kernel replay (nor can it be 300-step-chunked cheaply:
  ~271 chunks); it needs the mirror or Arc-2-style reflection.
  **The decomposition ladder that must precede the round lemma:
  (1) the driver-loop symbolic-net lemmas, (2) the storage-resp arm
  equations, (3) the harvest-ring (Ready-cycle) equations, (4) the
  RawNode-shell glue census/equations.**
- **A3 (absState lens-cheap at round boundaries)** — **PASS**:
  direct struct-field reads at all 31 round boundaries during the
  census; `absTwinRead` v0 SHIPPED (this unit) and kernel-evaluates
  over 26- and 617-cell literals inside a 23-s module; the deep
  node chain reads the delivered node's raft through
  nodes[i]→rn→raft. No reader-consolidation unit needed.
- **A4 (specRound ↔ lattice adapter small)** — **KILL-POINT FIRES,
  precisely characterized, with a reachability twist.** Where the
  decompositions align, the adapter IS small (the no-advance square:
  ~25 lines). But three mismatch axes are now theorems/grounded
  facts: (i) **commit-advance-without-new-entries has NO lattice
  image under any parameterization** (adapter_hb_advance_mismatch /
  verdi_emptyAE_commit_frozen; VerdiCompat/Raft.lean:169-201 vs
  raftsubject/raft/log.go:129, raft.go:1854-55) — and it is
  REACHABLE and essential (commit propagation in the 12 MsgApp + 6
  MsgAppResp rounds), not just the (unreachable) heartbeat; (ii)
  **the election noop entry** (raft.go:980-81 vs
  verdi_rvr_log_frozen) exits verdi's reachable set at the first
  election; (iii) **the package seam**: VerdiCompat is a separate
  Lake package golean-proofs does not require — adapter work needs
  a build-wiring decision. **Consequence (the design's own named
  KILL outcome): the adapter layer becomes its own design task.**
  Three routes, priced qualitatively: (a) projection redesign
  (erase noops + keep the commit axis outside the lattice; pays an
  index-remapping tax on every log-matching transfer); (b) NATIVE
  re-derivation of the needed invariant subset over specRound at
  the etcd-abstract level, reusing T3's proof STRUCTURE (for S1
  the chain provably never consumes commitIndex — grep evidence —
  and Arc 3's port machinery makes structure-replay cheap);
  (c) an etcd-faithful spec variant + lattice re-proof (heaviest).
  **Recommendation: (b) for the S1 leaf first; decide (a) vs (b)
  for S2/S3 only when their wave opens.**
- **REACHABILITY (outside A1–A4 — the census headline that
  re-targets the ladder)**: the heartbeat round-kind and the
  sF×Prop forward/drop arms are unreachable under EVERY stream (no
  ticks ⇒ no MsgBeat/MsgHeartbeat/MsgHeartbeatResp; only node 1
  proposes and it is leader whenever quiescent). All four landed
  dispatch-arm equations are T1-vacuous (machinery + validation
  value only). **C2+ must build the REACHABLE arm set** — MsgVote,
  MsgVoteResp, MsgApp families, MsgAppResp families, the storage
  resps, campaign, propose-accept — none of which has an arm
  equation today.
- **A5 (round-replay corollary ~100 applications)** — structurally
  unchanged, cost re-priced: 31 rounds × mirror-rate round lemmas
  ≈ hours of kernel, and the seed pin is 82,643 steps of init.
  Arc 2's FastEval/segment instruments remain the witness route of
  record; the round-replay corollary should NOT be re-costed until
  the reuse instrument decision (A1) lands.

### PROPOSED C2 CHARTER (the redesign need, per the verdict; the coordinator's call)

1. **Design amendment first** (coordinator, from this block): §6's
   ladder re-targeted — C2's round lemma moves OFF heartbeat to a
   REACHABLE kind; the recommended first target is the NO-OP arm
   round (stale MsgAppResp/MsgVoteResp: 7.7–9.2k steps, no handler
   state change — the cheapest real round) or the MsgVote round;
   the FrameSim C1+C2 instrument commissioning decision (A1) and
   the adapter-route decision (A4: recommend (b) for S1) get made
   at the same revision.
2. **The decomposition ladder** (A2's list, as C2's build order):
   driver-loop symbolic-net lemmas (loop-invariant classic — also
   the first consumers of the mirror's slice-walk forms);
   storage-resp arm equations (censused ~1.3–2k nested spans);
   the harvest-ring equations; then the first reachable-round
   lemma as a mirror chain over the doctor+prune fixture template
   (this unit's 26-cell construction, re-run at the target round
   kind).
3. **Budget guard**: no naive kernel replay past 300-step chunks
   anywhere in the C-ladder (the measured wall); mirror route or
   explicit chunk-cost quote required in any round-lemma plan.

### PROMOTION LEDGER updates (A4-U18)

- **NEW ROW: the doctor+prune round-fixture generator** (the
  TwinRoundFixProbe/RoundFixDump template): real-state anchor by
  computation + doctored injection + fail-closed read-set pruning
  (26 cells / 19 iterations / minutes). Consumers: every C2+ round
  fixture (any round kind, any loop-head anchor); also the C3 seed
  link's state-capture. The anchor pattern (`isAnchor` on the
  loop-head config) generalizes to any recurring driver config.
- **The literal-chain reuse instrument row (U15/U16)** — trigger
  condition now MET at C-ladder scale (this unit's A1 verdict);
  awaiting the coordinator's commissioning decision at the design
  revision.
- **NEW ROW: mirror coverage of the driver-glue op classes** — the
  round chains need the mirror to walk strings
  (stringFromRune/concat/itoa loops), map-lit, and slice-range
  rebuild loops; stringFromRune confirmed present
  (Sym/Mirror.lean:1469); the first mirror walk of the round
  fixture (C2) is the honest coverage test. Consume-on-first-need.
- The literal printer — 17th consumer (RoundFixDump; the first
  repr-dump generator: machine-domain literals, no Sym domain —
  the right form for CONCRETE fixtures).
- The leader-side fixture pack / RE-SPILL residual rows: unchanged.

## A4-U18 exit (2026-08-25, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the U17 gate tip
5d3e70ae: this log/code commit (single commit — census and adapter
probes are gitignored artifacts; the tracked delta is
RoundHbLit + RoundStatement + the aggregator + this log). Full
proofs+Audit green: **528 jobs** (526 + RoundHbLit + RoundStatement).
Kit pins: +0. Hatch grep over both new modules: 0. Probes
(gitignored): DrvSpanProbe, DrvHeadProbe, DrvHead2Probe,
TwinRoundFixProbe, RoundFixDump, A4AdapterProbe, AxRound, bltprobe.

**Deliverable state vs the U18 charter (C1, the design gate):**
1. THE DRIVER-SPAN CENSUS — **DELIVERED** (the full completing run
   replicated to the step; 31 rounds decomposed; the checker cleared;
   the glue growth, harvest ring, and reachability refutation are
   the A2 verdict's substance).
2. THE R-FORM ROUND STATEMENT + WITNESS — **DELIVERED WITH AN HONEST
   SPLIT**: RoundFam/absTwinRead/RoundLemmaShape shipped (R-form
   pinned; SCAFFOLD marked); the witness fixture built (doctor+prune,
   26 cells), the full round compiled-verified self-returning
   (10,964/4), the driver-glue sliver + pick crossing and all
   endpoint readouts KERNEL-checked; the full-round kernel replay
   measured-blocked (the second kernel wall — a route finding, not a
   failure to try) and routed to C2's mirror chain.
3. THE A4 ADAPTER PROBE — **DELIVERED, kill-point characterized as
   theorems** (no-advance square small; commit-advance and noop axes
   have no lattice image; package seam named; route (b) recommended
   for S1).
4. THE C1 VERDICT BLOCK — above, with the proposed C2 charter.

**Open gaps carried (none counted):** GAP-V1-2/-4/-5, GAP-U1-W1,
GAP-V2-1 wave-3 condition, GAP-V2-2, MemoryStorage.Entries spec
design, the multi-element spill variant, the RE-SPILL residual
family, message-field symbolism on demand — all unchanged; U18 adds:
the RoundLemmaShape scaffold (no proved instance — C2's first
obligation), the generator-verified-only links of the round replay
(steps 300–10,964, pending C2's mirror chain; stated in the module
docstring), and the T1-vacuity of the four landed arm equations
(recorded, not a defect — they were proof-shape pilots).

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1); the comparator-landmark STALE flag
stands escalated from U8–U17.

- 2026-08-25 A4-U18 gate follow-up (same-commit convention): unit-end
  gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the
  exit tree — **RESULT: PASS, exit 0** (`artifacts/ci-arc4-u18.log`,
  gitignored; 23 ok steps + the two sanctioned no-diff notes — this
  unit touched `proofs/GoLeanProofs/Specs/Raft/{RoundHbLit,
  RoundStatement}.lean` + the aggregator + this log + gitignored
  probes only; no runtime code, no Corpus/, no baselines/, zero Kit
  pins, zero edits to previously-shipped module STATEMENTS). Gate
  staggered behind the `free -g` guard. The comparator-landmark note
  now reads **STALE at 146 commits** (> the 100 threshold;
  report-only) — stands escalated for the operator's merge step, as
  at U8–U17.

## A4-U19 — C2a, THE INSTRUMENT: FrameSimS (the completeness-strengthened frame simulation), THE MID-WALK CONSUMPTION THEOREM, and the discharge witness (2026-08-25, same worker as U18, coordinator-dispatched per layer-C design v2 §8 D1; hard stop 3 units, probe-first)

- 2026-08-25 SELF-RE-VERIFICATION (U18's top claims, fresh probes,
  all PASS — same-worker continuation per the C2a dispatch):
  - tip clean: `git status` clean on `campaign-arc4`; `git rev-parse
    HEAD` = `3bbb0f1059a2c750d75df1502ec54b3f1024cabd` (the U18 gate
    tip). 91G free at launch; every build `GOLEAN_MEM_MAX=48G
    scripts/capped`.
  - fresh capped proofs+Audit build: "Build completed successfully
    (528 jobs)." exit 0 — matching U18's record.
  - `#print axioms` fresh probe (`AxRound` re-run, verbatim):
    rhb_glue100/300/rhb_glue and RoundFam.self [propext, Quot.sound];
    the four readouts [propext] — matching U18 exactly.
  - hatch grep over RoundStatement/RoundHbLit: **0**.
- 2026-08-25 Slice 1 (probe-first, as commissioned) — **THE SHAPE
  CLAUSE VALIDATED + THE IN-PLACE ROUTE REFUTED**
  (`artifacts/probe/FrameSimShapeProbe.lean`, green):
  - The C2 insertion-point clause (`∃ pre post, σ.heap = pre ++ post
    ∧ σF.heap = ren pre ++ fr ++ ren post`) PRESERVED by the one
    mutation primitive in all three key cases — in-prefix in-place,
    in-suffix in-place, and MISSING-KEY APPEND (both sides append at
    the tail, so even canonical set-appends — the pruned-fixture
    write class U18 exercised — keep the split); seeds/relocations
    carry it trivially. The supporting heap algebra
    (set-over-append, set-of-missing, renameHeap/set commutation)
    proved clean.
  - **THE U16-SIZING CORRECTION (design finding): the in-place
    strengthening is BLOCKED at `rebaseSimT`** — the gallery's
    between-pass frame-growth constructor cannot discharge the
    clause: its lookup-level premises cannot pin the ∃-split against
    the retired segment (the retired cells re-partition the heap
    non-contiguously mid-chain), and every pinning reformulation
    fails against set-append freedom (key-class discrimination,
    na₀-keyed splits, length arithmetic — each exhausted in
    session). U16's probe missed this because its trial covered the
    C1 clause only. DECISION [AGENT]: **ADDITIVE `FrameSimS` + a
    copy-threaded S-induction** — zero changes to the shipped
    `FrameSim` (no statement-meaning drift anywhere), the gallery
    untouched; the copies are a RECORDED SCAFFOLD (retirement
    condition in `ShapeSim.lean`'s docstring: fold the clause
    in-place if the gallery rebase chain is ever retired or re-based
    on pinned splits).
- 2026-08-25 Slice 2 (bd? this commit) — **THE INSTRUMENT LANDS**
  (7 new `Frame/` modules + the witness + Audit pins; 5,608 new
  lines; full proofs+Audit green: **537 jobs**; hatch grep over
  every new module: 0; LINEAGE throughout: Yang–O'Hearn locality,
  the COMPLETENESS half of the semantic frame property):
  - `Frame/ShapeSim.lean` (283) — the heap algebra, **`FrameSimS`**
    (= FrameSim + the shape clause), the strengthened primitives
    (`FrameSimS.setBase`, `FrameSimS.alloc_snd`), and the seeds
    (`frameSimS_seed`, `frameSimS_relocate`).
  - `Frame/ShapeOps.lean` (405) / `ShapeOps2` (766) / `ShapeOps3`
    (818) — the mutating operation layer at S: storeLoc/storeMany/
    allocDecls/bindParams/enterFrame/frame-entry steps/bindIterVars,
    the stmt-op arms (appendSlice spill + core), the chan/sync/
    select applies (+ `TripSimS`/`CfgSimS`); each proof mirrors its
    weak sibling verbatim with the S-primitives; read-only lemmas
    consumed weak via `toFrameSim` (the packaged-relation seam the
    U16 probe predicted — it held everywhere).
  - `Frame/ShapeStrict.lean` (2,013) — the WHOLE-FILE mechanical
    mirror of StrictOps (108 declarations, `_SS`-suffixed,
    python-generated; the generation script's substitution table in
    this entry's history). [AGENT]: the cheaper DERIVATION route
    (state passthrough — `applyStrictOp` allocates in exactly TWO
    arms, bytesFromString/runesFromString; the C2a measurement that
    corrected slice-plan's grep, which had missed dot-spelled
    `.alloc`) was MEASURED OUT: the ~90-arm passthrough case-bash
    hit the 3.2M-heartbeat ceiling twice (backtracking-chain and
    linear-pipeline forms both); the copy elaborates at StrictOps'
    own cost and is the budget-honest route.
  - `Frame/ShapeStep.lean` (860) — **`stepFn_simS`**: the 795-line
    per-step induction copy-threaded at S (the `ren_simp` macro
    pair duplicated at S; the strict cases through ShapeStrict),
    plus utilities: `bbind_eq_ok` (the `Bind.bind`-spelled bind
    inversion — the `>>=`/HBind spelling silently misses zeta-
    unfolded join-point bodies, a recorded lesson), `except_match_ok`
    (the do-desugared Except match-bind inversion),
    `applySlice_state`.
  - `Frame/ShapeSpan.lean` (225) — `stepFnIter_simS`,
    **`span_consume` — THE MID-WALK CONSUMPTION THEOREM**: a landed
    canonical span (`*_full_span` — every handler equation ships
    one) consumed at ANY `FrameSimS` placement returns the framed
    run's equality AND the post-state LITERALLY:
    `σF' = { σfin with heap := ren pre ++ fr ++ ren post,
    nextAddr := ρ σfin.nextAddr }` — every table equal, nothing
    relational surviving the hand-back; `span_relocateS` (the
    `.stop` corollary in `span_relocate`'s shape); and
    **`frameSimS_extend`** — the frame-extension constructor the
    U15 probe predicted (growth-free placements: seeds/relocations;
    extensions at placement-construction time).
  - `Specs/Raft/ShapeWitness.lean` (211) — **THE DISCHARGE
    WITNESS**, the U15 wall's blocked operation EXECUTED end to end
    on the landed `handleHeartbeat` equation (the sF-side heartbeat
    chain's handler, per the dispatch; its T1-vacuity is restated
    in the docstring — the witness validates the INSTRUMENT, not
    the arm): `swPlacement` (a CONCRETE non-identity placement,
    `ρT 55 8` + a frame cell at 57 in the gap, via
    relocate+extend); `sw_consume` (`hh_full_span` consumed at the
    placement — the framed 1,325-step run's equality with the
    spliced-literal post-state, NO kernel replay of the span);
    `sw_resume` (**the literal resume: nine machine steps executing
    `*(&57) = 9` — a WRITE TO THE FRAME CELL** — five state-generic
    `rfl` steps + the store discharged on `frame_pres` + three
    `rfl` steps, chained by `stepFnIter_chain`/`stepFnIter_one`);
    `sw_consume_and_resume` (the composition); `sw_readout`
    (`absOutbox = [specHeartbeatResp 1 2 0]` at the placement via
    the inherited rename transport).
  - `Audit/FrameShape.lean` (37) — 8 `#guard_msgs` axiom pins on
    the headline theorems (the commissioning terms' "Audit-pinned").
  - Axioms (probe `artifacts/probe/AxShape.lean`, verbatim):
    stepFn_simS / stepFnIter_simS / span_consume / span_relocateS /
    sw_consume / sw_consume_and_resume [propext, Classical.choice,
    Quot.sound]; frameSimS_extend [propext]; frameSimS_seed /
    sw_resume / sw_readout [propext, Quot.sound].
- **RESIDUAL, recorded (promotion ledger)**: the hand-back's split
  point is EXISTENTIAL (`∃ pre post`). Readouts, frame reads, and
  frame writes are split-independent — the witness demonstrates all
  three — so every current consumer shape works; the full split
  EXTRACTION (separator uniqueness: at `fr ≠ []` the frame segment's
  position is pinned by `fr_avoid`'s key-class discrimination) is
  the named cheap follow-up for a consumer that needs the ONE
  literal list (e.g. a mirror-window generator resuming with a
  concrete heap). Estimated ≤ half a slice when first needed.
- What-this-taught-us (C2a): (a) probe-first paid again — the
  in-place plan U16 sized would have stalled mid-edit against
  rebaseSimT with the Frame surface torn open; the additive route
  cost the same copies WITHOUT the risk; (b) whole-file mechanical
  proof transforms (python substitution tables over
  relation/callee names) are a real velocity instrument: 2,013
  lines of StrictOps mirrored GREEN ON FIRST ELABORATION — when the
  seams are packaged relations, textual copy-threading is cheap and
  safe; (c) two tactic-engineering lessons for the record:
  fun_cases-scale backtracking `first` chains are heartbeat sinks
  (prefer linear pipelines, and prefer scoped copies over clever
  meta-proofs when the case count is ~90); inversion lemmas must
  match the TERM'S spelling (`Bind.bind` vs `>>=`/HBind — invisible
  in display, fatal to `rw`).

### PROMOTION LEDGER updates (A4-U19)

- **The literal-chain reuse instrument row (U15/U16/U18) — CONSUMED.
  THE INSTRUMENT IS LANDED** (this unit): `FrameSimS` +
  `span_consume` + `frameSimS_extend` + the S-transport stack. The
  row closes; its successor rows: (i) **the ∃-split extraction**
  (above; consume-on-demand), (ii) **the scaffold retirement
  condition** (`ShapeSim.lean` docstring), (iii) **first big-span
  consumers**: the MsgApp arms × the 6,925-step Hae REJECT window
  (the row's original trigger case — now buildable as consumption
  instead of re-walking), and C2b+'s round lemmas.
- The doctor+prune fixture template (U18): unchanged; now pairs with
  `frameSimS_extend` for placement construction at round fixtures.
- The U18 rows (mirror driver-glue coverage, RoundLemmaShape
  scaffold): unchanged, C2b's inputs.

## A4-U19 exit (2026-08-25, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the U18 gate tip
3bbb0f10: this instrument+log commit (the C2a build); no coordinator
commits interleaved on the lane. Full proofs+Audit green: **537
jobs** (528 + ShapeSim/ShapeOps/ShapeOps2/ShapeOps3/ShapeStrict/
ShapeStep/ShapeSpan/ShapeWitness + Audit.FrameShape). Kit pins: the
8 FrameShape guard blocks (additive Audit surface). Hatch grep over
every new module: 0. Probes (gitignored): FrameSimShapeProbe,
A4AdapterProbe (U18), sufprobe, statene_iso*, splitprobe*, AxShape.

**Deliverable state vs the C2a dispatch:**
1. THE STRENGTHENED SIM — **DELIVERED** (FrameSimS; C1 completeness
   DERIVABLE from the shape clause rather than carried — one clause,
   less breakage; the U16 probe's seed design honored, its sizing
   corrected by measurement: in-place is blocked at rebaseSimT, the
   additive route is the honest shape of the same cost).
2. THE MID-WALK CONSUMPTION THEOREM — **DELIVERED** (`span_consume`:
   a relational sub-span hands back a literal-resumable state — the
   thing U15's wall blocked; ∃-split caveat recorded with its
   split-independence demonstration and extraction row).
3. THE DISCHARGE WITNESS — **DELIVERED** (one landed handler
   equation consumed inside a longer chain at a concrete
   non-identity placement, with a frame-writing literal resume and
   the abstract readout; Audit-pinned; lineage-lined).
4. Hard-stop accounting: probe slice + one heavy build slice +
   witness ≈ within the 3-unit ceiling; the one blast-radius excess
   vs U16's sizing (rebaseSimT) was stopped at the measured
   boundary and REROUTED, not ground through.

**Open gaps carried (none counted):** all U18 rows unchanged; U19
adds: the ∃-split extraction row and the scaffold retirement row
(both above). The U18 C1-verdict items for the COORDINATOR (C2b-d
re-targeting, D2/D3 execution) are untouched by this unit.

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1); the comparator-landmark STALE flag
stands escalated from U8–U18.

- 2026-08-25 A4-U19 gate follow-up (same-commit convention): unit-end
  gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the
  exit tree — **RESULT: PASS, exit 0** (`artifacts/ci-arc4-u19.log`,
  gitignored; 23 ok steps + the two sanctioned no-diff notes — this
  unit touched `proofs/GoLeanProofs/Frame/Shape*.lean`,
  `Specs/Raft/ShapeWitness.lean`, `Audit/FrameShape.lean`, the two
  aggregators, arc-4 docs + gitignored probes only; no runtime code,
  no Corpus/, no baselines/; the Audit surface GREW by the 8
  FrameShape pins — additive, in-build-verified). Gate staggered
  behind the `free -g` guard (89G free ≥ 24G cap). The
  comparator-landmark note now reads **STALE at 148 commits** (> the
  100 threshold; report-only) — stands escalated for the operator's
  merge step, as at U8–U18.

## A4-U20 — C2b: THE DRIVER-LOOP SYMBOLIC-NET LEMMAS (the compositional mode's first from-scratch statements) + the storage-resp sub-ring anchor census (2026-08-25, fresh worker, coordinator-dispatched per the flexibility redesign §3 I2/§7 and the U18 A2 refinement)

- 2026-08-25 SUCCESSOR RE-VERIFICATION (U19's top claims, fresh
  probes, all PASS — fresh worker per rotation):
  - tip clean: `git status` clean on `campaign-arc4`; `git rev-parse
    HEAD` = `33e073252fc223f22e0e6c80d41529b84f4abd0c` (the U19 gate
    tip). 87G free at launch (≥ 40G floor); builds capped
    `GOLEAN_MEM_MAX=48G scripts/capped` throughout (one deliberate
    24G probe run).
  - fresh capped proofs+Audit build: "Build completed successfully
    (537 jobs)." exit 0 — matching U19's record.
  - `#print axioms` fresh probe (`AxShape` re-run, verbatim): all 14
    pins match U19's record exactly (FrameSimS.setBase/alloc_snd,
    frameSimS_seed/relocate/extend, stepFn_simS, stepFnIter_simS,
    span_consume, span_relocateS, swPlacement, sw_consume, sw_resume,
    sw_consume_and_resume, sw_readout).
  - hatch grep over `Specs/Raft/`: **0**.

- 2026-08-25 Slice 1 (probe-first) — **THE SLICE-WALK LOOP CENSUS**
  (`artifacts/probe/{C2bDump,C2bLoopCensus,C2bLoopCensus2}.lean`,
  outputs gitignored): the frontend's range-desugar shape extracted
  from the pinned lowering (ONE fixed shape — `$rcoll/$rlen/$ridx/
  $rfirst` temps, first-flag while, per-iteration index cell; the
  driver's live-map rebuild and `main.twin.liveCount` carry it
  verbatim, differing only in index-var name and guarded action);
  iteration boundaries measured at doctored U18-fixture nets of
  length 0–3 with mixed liveness flags. THE EXACT ANATOMY: rebuild
  iterations 63 (first, guard true) / 67 (subsequent, true) / 54/58
  (guard false), exit 29/33; liveCount 68/72 and 54/58; ONE fresh
  cell per iteration (the frontend's per-iteration variable — the
  machine does not prune it; the family threads a growing dead
  region, the MapLoops pattern). Segment decomposition: head glue
  17/21, bound check 9 (continue) / 10 (break→`.next k`), index
  bind 11, back edge 2 — all census-exact.

- 2026-08-25 Slice 2 (33e07325..2b277168, tracked) — **THE
  DELIVERABLE: the symbolic-net loop lemmas, landed in the
  compositional mode (I2)**. Full proofs+Audit green: **541 jobs**
  (537 + the four new modules); every compile verified by EXIT CODE
  (see the masked-kill lesson below); hatch grep over all new
  modules 0.
  - `GoLeanProofs/SliceWalk.lean` (~950 lines, kit, Go-general —
    elaborates in **0.6 s**): the range-desugar statement vocabulary
    (`rbody`/`rwhile`, parameterized by the four temp names + index
    var + body); the conditioned glue segments (`glue_first`/
    `glue_next`/`bound_lt`/`bound_ge`/`bind_seg`/`back_edge`, StepKit
    rules 1–5 shapes: abstract σ, cell lookups as hypotheses); the
    composed per-iteration walks (`iter_head_to_body`,
    `exit_from_head`); and **`sliceWalk_loop` — THE SCHEMA**: state
    family S indexed by iteration, control cells at scheduled values
    + fresh frontier as the invariant interface, the BODY fact as the
    one per-instance obligation, conclusion BOUNDED-COMPLETION
    (`∃ m ≤ (43 + bB)·(n−i) + 31`) delivering `.next k` + the exit
    state + `S n`. No exact fuel counts in any consumer-facing
    conclusion. LINEAGE: Floyd/Hoare loop invariant, in
    `stepFnIter_iterate_bail_rel`/`mapCountLoop_generic`'s exact
    style, specialized to the frontend's shape so instances prove
    ONLY their body. The prologue above the while is fixed-cost and
    deliberately NOT schematized (middle-path §7: no |net|
    dependence, no demonstrated demand — fixed spans ride the
    mirror); the map-range pick loop is already
    `MapLoops.mapPickLoop_generic`'s.
  - `Specs/Raft/DriverNet.lean` (~1330 lines, 20 s incl. the kernel
    shape pins): the twin instances. THE SHAPE PINS
    (`drvRebuild_pinned`/`lc_pinned` + `_prop` forms): the proved
    while statements occur VERBATIM in the pinned lowering's
    `runTwinChoice` and `main.twin.liveCount` — whiles collected
    recursively (fuel-structural, `let rec`-free — see lesson (b)),
    compared by the sound `Stmt.eqbF`, kernel-checked; a frontend
    re-lowering that reshapes either loop turns them red (the window
    links' drift-alarm role, one ring up). The guarded-body segments
    (`guard_seg` 13 steps — deref/fieldGet/indexGet over the twin
    route; `act_rebuild` 11 — the fresh-key map insert, mirroring
    `MapMem.mapAssignValue_toEntries` at `int → bool`; `act_inc` 16;
    `act_skip` 2). The invariants (`RebuildInv`/`LiveCountInv`) and
    body facts (bB = 24 / 29). **THE HEADLINES**: `rebuildLoop_span`
    and `liveCountLoop_span` — from any loop head satisfying the
    invariant at 0, completion within `67·n + 31` / `72·n + 31`
    steps, `n = bs.length` and the liveness payload `bs` FULLY
    SYMBOLIC, with the live map = exactly `liveIdx bs n` (the live
    indices) / the counter = exactly `countTrue bs n`. The composed
    per-iteration bounds 67/72 REPRODUCE the census's measured
    67/72-step iterations exactly.
  - `Specs/Raft/DriverNetWitness.lean` (1.05 s): the non-vacuity
    witnesses — every premise of both spans discharged on a concrete
    9-cell state at `bs = [true, false]` (no premise left open) —
    plus THE CENSUS CROSS-LINKS: the compiled walks' exact counts
    (152 = 63+58+31 rebuild; 157 = 68+58+31 liveCount —
    `#eval`-verified first) kernel-replayed via total fail-closed
    readouts (`rebuild_census_link`/`liveCount_census_link`: map
    holds `bEntries (liveIdx wBs 2)`, counter `countTrue wBs 2`,
    allocator 11). The schema's composed costs land on states it was
    never fitted to, step-exact.
  - `Audit/DriverNet.lean`: 9 `#guard_msgs` axiom pins (additive
    Audit surface, in-build-verified). Axioms: the classical trio on
    the spans/witnesses/schema; [propext, Quot.sound] on the census
    links.

- **THE MODE SHIFT'S FIRST REAL NUMBERS (compositional vs literal,
  measured this unit — the dispatch's named report item):**
  - **Coverage**: ONE statement per loop now covers EVERY net length,
    liveness payload, and address placement — the literal mode's
    equivalent is one chain per net shape per round, and the driver
    glue is |net|-dependent (U18: 3,578 → 7,250 steps/round across
    the run), so the literal family is UNBOUNDED over the choice-
    stream quantifier. This is the difference in kind, not degree.
  - **Kernel volume, like-for-like**: the C-ladder's driver-glue
    obligation across the pinned run's 28 deliver rounds ≈ 155k
    literal steps at mirror rate (~30–40 steps/s) ≈ **70–85 min of
    kernel per full-run replay, re-paid at every re-derivation**;
    the schema + instances + witnesses elaborate ONCE in **≈ 22 s**
    (0.6 s kit + 20 s instances incl. two whole-program kernel
    shape pins + 1 s witnesses) — a ≥ 200× reduction on this span
    class, paid once instead of per-round.
  - **Fidelity**: the composed bounds equal the census-measured
    per-iteration costs exactly (67/72), and the witness kernel runs
    land on the composed predictions exactly (152/157) — the
    compositional statements lose nothing the literal mode measured.
  - **Statement cost** (the mode's price): the schema's invariant
    interface (control cells + frontier) and the instances'
    distinctness/lookup hypothesis packs are statement work the
    literal mode never paid; measured here at roughly one unit for
    schema + two instances + witnesses. The per-instance marginal
    cost after the schema: the BODY facts only (the liveCount
    instance was ~1/3 of the rebuild's build effort).

- 2026-08-25 Slice 3 (probe-only) — **THE STORAGE-RESP SUB-RING
  ANCHOR CENSUS** (deliverable-2 groundwork;
  `artifacts/probe/C2bRingCensus.lean` → `ringcensus.out`,
  gitignored): the U18 heartbeat-round fixture's full harvest ring
  walked with every Ready-cycle callee boundary recorded (step
  index, `nextAddr`, choices left). THE ANCHORS (fixture-relative):
  deliverIdx 1065 (prologue 133 — U18-exact), RawNode.Step 1198
  (shell 383 — U18-exact), raft.Step 1581, handleHeartbeat 2283,
  harvest 3775; ring 1: HasReady 3831 (span ~180), Ready 4011 →
  readyWithoutAccept 4024 → applyUnstableEntries 4170 (assembly
  span ~1,836), acceptReady 5847 (span ~1,196, consumes BOTH of the
  ring's 2 appendSpill draws — SC1's classification re-verified at
  the fixture), Advance 7043 (span ~142); ring 2: HasReady 7185
  (false exit, incl. the 8721 applyUnstableEntries, span ~1,832);
  driver suffix: projection 9017, **liveCount 10412 — the landed
  `liveCountLoop_span`'s real consumption site in every round**.
  - **THE FINDING (redirects deliverable 2)**: the heartbeat round's
    ring NEVER REACHES the storage-resp arms — no entries appended ⇒
    no MsgStorageAppendResp/ApplyResp nested `raft.raft.Step`, and
    `Advance` is a 142-step no-op shell here (vs U18's ~2,000 at the
    MsgApp round). The 5–6 payload-parametric sub-ring statements
    (SC1's harvest verdict) need a **MsgApp-family round fixture** —
    the U18 doctor+prune template re-instantiated at kind MsgApp —
    BEFORE any storage-resp arm equation can be stated with a real
    anchor. That fixture is also C2d's first-reachable-round need,
    so the two shares one generator run. [AGENT]: deliverable 2
    delivered AS the anchor census + this finding + the redirect —
    the equations themselves are the successor's, with their
    prerequisite now precise (anti-grinding: starting mirror-window
    equation work at a fixture that cannot reach the arms would have
    been motion, not progress).

- [AGENT] calls, tagged:
  1. The schema parameterizes the four `$r*` temp names and the index
     variable (cheap strings) but NOT the prologue or the pick loop
     (middle-path §7 both ways: names have a demonstrated second
     consumer — nested range loops must rename; the prologue has no
     |net| dependence and no demand).
  2. The shape pins land as MEMBERSHIP among recursively-collected
     whiles (sound `Stmt.eqbF`, kernel-checked) rather than
     index-path navigation — robust to statement-list shifts around
     the loop, still a drift alarm on the loop itself.
  3. Deliverable-2 scope call: anchor census + prerequisite finding
     this unit; the sub-ring equations to the successor (rotation
     budget + the MsgApp-fixture prerequisite; recorded above).
  4. The witnesses are synthetic-minimal (9 cells) rather than
     round-fixture-anchored: the spans' premises are exactly
     discharged, the census links pin the exact-run behavior, and
     the ROUND-fixture consumption belongs to C2d's round lemma
     (where the anchors from slice 3 place both loops).
- What-this-taught-us (each a recorded convention candidate):
  - (a) **THE MASKED-KILL LESSON (process, sharp)**: piping compiler
    output through `grep | head` swallows a cgroup kill — the
    pipeline exits 0 with empty output, indistinguishable from a
    clean compile. Several mid-unit "greens" were 48G-cap SIGTERMs
    (~24 s in, the cap doing its blast-radius job); caught only by a
    later missing `.olean`. Rule now followed and recommended for
    the conventions: **capture to a file, echo `exit=$?`, judge by
    the exit code — never by absence of grepped errors.** (The
    async-results doctrine's sibling for foreground pipes.)
  - (b) **#eval-before-decide, new vector**: `with_unfolding_all
    decide` on a TRUE Bool over the pinned program (the shape pins)
    is an elaborator-side runaway — ~50 GB in 22 s, linear climb, no
    false goal anywhere (the documented decide lesson's cost class,
    but representation-level: the elaborator's evaluator has no
    sharing). The kernel route (`kernel_rfl`) checks the same fact
    in seconds — but only after removing a `let rec` from the
    collector (the lifted auxiliary blocks kernel reduction; fuel
    recursion written flat reduces fine).
  - (c) A structure-update field value that SPILLS to a continuation
    line fails to parse when another field follows (`unexpected
    token; expected '}'`) — parenthesize the value; bit six times.
  - (d) The storm discipline's payoff is now measured at kit scale:
    the whole schema module elaborates in 0.6 s BECAUSE every
    segment is abstract-σ + conditioned lookups; nothing here
    whnf's a concrete front, ever.

### PROMOTION LEDGER updates (A4-U20)

- **NEW ROW: the SliceWalk range-loop schema** (kit). Landed
  consumers: the rebuild and liveCount instances. Latent consumers:
  `pickFor` (same guard shape + early return — needs a bail-form
  body fact, the schema's `bound_ge` machinery suffices),
  `complete()`'s nested range loops, any future subject's
  range-by-index loop. Consume-on-need.
- **NEW ROW: the storage-resp anchor set** (slice 3's census) + the
  MsgApp-round-fixture prerequisite. Consumer: the successor's
  sub-ring equations + C2d's round lemma (one generator run serves
  both).
- **The U18 mirror-driver-glue-coverage row — PARTIALLY CONSUMED**:
  the |net|-dependent glue no longer needs the mirror at all (the
  loop lemmas replace that route); the row narrows to the FIXED
  driver-glue spans (prologue, trace itoa, pick crossing) for C2d's
  mirror chain.
- The doctor+prune fixture template (U18): now owes its second
  instantiation (MsgApp round kind) — the prerequisite above.
- The ∃-split extraction and scaffold-retirement rows (U19):
  untouched.

## A4-U20 exit (2026-08-25, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the U19 gate tip
33e07325: 2b277168 (the deliverable-1 build) + this log/census
commit. Full proofs+Audit green: **541 jobs** (537 + SliceWalk +
DriverNet + DriverNetWitness + Audit.DriverNet). Kit pins: +9
(Audit/DriverNet.lean, additive, in-build-verified). Hatch grep over
every new module: 0. Probes (gitignored): C2bDump/2/3,
C2bLoopCensus/2, C2bWitnessGen, C2bPinEval, C2bRingCensus,
PinKernelProbe, ParseTest, NameProbe/2, dn/sw logs.

**Deliverable state vs the C2b charter:**
1. THE DRIVER-LOOP SYMBOLIC-NET LEMMAS — **DELIVERED** (schema +
   both instances + witnesses + shape pins + census cross-links +
   Audit pins; loop-invariant form, Go-general at the demonstrated
   scope, lineage-lined, bounded-completion conclusions — the
   compositional mode's first from-scratch statements, with the
   mode-cost numbers above).
2. THE STORAGE-RESP ARM EQUATIONS — **DELIVERED AS THE ANCHOR CENSUS
   + THE PREREQUISITE FINDING** (honest split): the sub-ring
   boundaries are pinned at the fixture and SC1's draw
   classification re-verified, but the heartbeat fixture cannot
   reach the storage-resp arms — the MsgApp-round fixture
   (doctor+prune template, second instantiation) is the successor's
   first step, then the 5–6 payload-parametric statements against
   these anchors.
3. Budget item (first reachable round-kind dispatch arm) — **NOT
   REACHED** (rotation); its fixture prerequisite is the same
   MsgApp-round generator run as item 2's.

**PROPOSED NEXT CHARTER (C2c, successor)**: (1) the MsgApp-round
fixture via the U18 doctor+prune template (also C2d's need); (2) the
storage-resp sub-ring census at THAT fixture (the 2,000-step
Advance+nested-Step span U18 measured); (3) the 5–6
payload-parametric sub-ring statements in the compositional mode,
composed via `span_consume` where landed spans apply; (4) budget
permitting, the first reachable round-kind arm census. The masked-
kill rule (lesson (a)) briefed into the dispatch verbatim.

**Open gaps carried (none counted):** all U18/U19 rows unchanged;
U20 adds none beyond the ledger rows above.

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1); the comparator-landmark STALE flag
stands escalated from U8–U19.

- 2026-08-25 A4-U20 gate follow-up (same-commit convention): unit-end
  gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the
  exit tree — **RESULT: PASS, exit 0** (`artifacts/ci-arc4-u20.log`,
  gitignored, with `GATE_EXIT=0` recorded IN the log per lesson (a);
  23 ok steps + the two sanctioned no-diff notes — this unit touched
  `proofs/GoLeanProofs/SliceWalk.lean`,
  `proofs/GoLeanProofs/Specs/Raft/DriverNet{,Witness}.lean`,
  `proofs/Audit/DriverNet.lean`, the two aggregators, this log +
  gitignored probes only; no runtime code, no Corpus/, no baselines/;
  the Audit surface GREW by the 9 DriverNet pins — additive,
  in-build-verified). Gate staggered behind the `free -g` guard
  (119G available ≥ 24G cap). The comparator-landmark notes now read
  **STALE at 151 commits** AND **OWED (scope): 1 file** — the scope
  trigger is this unit's one-line `proofs/Audit.lean` import
  addition (Audit.lean is an explicitly listed landmark file in
  `scripts/ci`'s `lm_files`); both report-only. The operator's
  merge-step judge run — already escalated since U8 — is now owed on
  BOTH the staleness and scope triggers.

## A4-U21 — C2c: THE ARC4B LANDING (slice 0) + THE MSGAPP-ROUND FIXTURE + THE SUB-RING CENSUS + THE STORAGE-RESP SUB-RING SPANS (2026-08-25/26, fresh worker, coordinator-dispatched per U20's proposed charter; masked-kill rule briefed verbatim)

- 2026-08-25 SUCCESSOR RE-VERIFICATION (U20's top claims, fresh
  probes, all PASS — fresh worker per rotation):
  - tip clean: `git status` clean on `campaign-arc4`; `git rev-parse
    HEAD` = `f94c225a4e7d86de06ed02fb3732375ebe6799fc` (the U20 gate
    tip). 86G free at launch (≥ 40G floor); builds capped
    `GOLEAN_MEM_MAX=48G scripts/capped` throughout; every compile
    judged by CAPTURED EXIT CODE per the masked-kill rule.
  - fresh capped proofs+Audit build: "Build completed successfully
    (541 jobs)." exit=0 — matching U20's record.
  - SliceWalk/DriverNet/DriverNetWitness/Audit.DriverNet present; 9
    `#guard_msgs` pins counted in Audit/DriverNet.lean.
  - hatch grep over `Specs/Raft/`: **0**.

### Slice 0 — THE ARC4B LANDING (25810585 + 80e6f812)

- `git merge campaign-arc4b` (76e63bba): **clean auto-merge, zero
  conflicts** — the lane's no-edit claim verified structurally first
  (`git diff --name-status` vs the merge base 3bbb0f10: nine pure
  adds, zero modifications).
- The eight manifest imports added to `proofs/GoLeanProofs.lean`.
  **Two landing findings, both fixed on the spot:**
  1. **The joint-import name collision** (falsifies the manifest's
     "expect fully green" in one narrow respect): `wStep1`–`wStep4`
     are defined in BOTH `NativeS1Witness` (C3, EStep steps) and
     `NativeS23Witness` (C4, HStep steps) in the same namespace —
     each lane module was verified green STANDALONE; joint import
     into one environment was exactly the deferred step, and it
     fails (`environment already contains …wStep2`). Fix: the C4
     witness steps renamed `wHStep1`–`wHStep6` (rename note in the
     module; STATEMENTS unchanged; zero external references — grep
     verified). A lane convention candidate for the operator: lane
     modules sharing a namespace should carry joint-import smoke
     checks, or unit-prefixed witness names.
  2. **The check-spec-anchors xargs-batching false death**: the gate
     died `grep/xargs exit 123` — root-caused (not papered): the
     tracked file list crossed xargs's 128 KiB single-invocation
     budget FOR THE FIRST TIME at this landing (131,087 bytes; the
     nine arc4b paths added ~470), so grep ran in two batches for
     the first time, and a batch with zero citation matches exits 1,
     which xargs reports as 123 — indistinguishable from a scan
     death at the top level. Fix in `scripts/check-spec-anchors`:
     per-batch wrapper maps grep's legitimate no-match exit 1 to 0;
     a real grep error (≥ 2) still propagates as 123 and the rc>1
     death check still fires — **fail-closed on genuine errors
     preserved and re-tested in BOTH directions** (death path rc=123
     on a nonexistent file; no-match path rc=0), 626 citations still
     found (511 spec# + 115 mem#, count unchanged).
- Manifest optional cleanups (Star unification, S23-skeleton
  deletion/marking): **SKIPPED — not trivial** (they edit three lane
  modules' content); left for a landing-cleanup slice with the
  operator's blessing, per the charter's "skip unless trivial".
- **THE SLICE-0 LANDING GATE — RESULT: PASS, exit 0** (verbatim:
  `RESULT: PASS` / `GATE_EXIT=0`; `artifacts/ci-arc4-u21-slice0b.log`,
  gitignored): 23 ok steps + the two sanctioned no-diff notes;
  549 jobs (541 + the eight lane modules); the landing
  retro-validates the lane's compensating checks. Comparator
  landmark: STALE at 156 commits AND OWED-on-scope (report-only;
  standing escalation since U8 — unchanged).

### Slice 1 (probe-only) — THE MSGAPP-ROUND FIXTURE (the doctor+prune template's second instantiation; `artifacts/probe/TwinMsgAppFixProbe.lean`)

- **First probe hit the STALE branch, and the miss decoded the boot
  log**: a `Index 0/LogTerm 0/entry(1,1)/Commit 1` doctor
  early-returns at `m.Index < committed` (11,249-step round ≈ the
  heartbeat's 10,964 — no append, no storage-resp arms) because node
  2's log at the first loop head is NOT empty: `AnchorLogProbe` +
  `AnchorStorProbe` decoded it — **node 2 boots from a snapshot at
  (index 1, term 1)**: MemoryStorage ents = [dummy (1,1)],
  committed = applying = applied = 1, unstable.offset = 2. (The
  census's na-6073 heap decoded at the cell level for the first
  time.)
- **THE APPEND-AND-COMMIT FAMILY FIRES** (the corrected doctor:
  Type 3, 1→2, Term nil = the U18 local-family convention, Index 1 /
  LogTerm 1 = the match at the real last entry, ONE entry (Index 2,
  Term 1, empty Data), Commit 2):
  - **Round: 23,488 steps / 8 choices / na 6086→7382,
    self-returning config** — squarely inside U18's real MsgApp
    round range (18.6k–24.3k), vs the heartbeat fixture's 10,964/4.
  - POST: committed 1→2, applying/applied 1→2 (the apply path RAN),
    lead 0→1, net gains MsgAppResp (typ 4, 2→1, Index 2).
  - **Pruned read set: 39 cells** (26-cell heartbeat pattern + the
    log/storage cells 1779/1886/1895/1898/1900 + cell 25 + the two
    extra doctor cells), found in 25 fail-closed iterations.
- The same generator run is C2d's (one anchor walk, shared) — the
  charter's build-once note honored.

### Slice 2 (probe-only) — THE SUB-RING CENSUS AT THE MSGAPP FIXTURE (`artifacts/probe/MsgAppRingCensus.lean` → `msgappring.out`)

- **THE RING ANATOMY** (fixture-relative; glue boundaries
  deliverIdx 1065 / RawNode.Step 1198 / raft.Step 1581 all
  U20-heartbeat-EXACT — the shells are the same code, measured):
  handleAppendEntries ENTER 2264; maybeAppend 2664; commitTo 6035;
  arm span raft.Step→harvest = 5,844 (U18's census said 5,826 at the
  real round — matched); **harvest 7425**; HasReady 7481; Ready 7661
  → readyWithoutAccept 7674 → applyUnstableEntries 7835; acceptReady
  10752; newStorageAppendRespMsg 11654; newStorageApplyRespMsg
  12699; SetHardState 14574; MemoryStorage.Append 14809; twin.apply
  15937 (324 steps — U18's checker range); **Advance 16261 with BOTH
  nested `raft.raft.Step` storage-resp arms** (16391
  MsgStorageAppendResp → stableTo 16973; 17584 MsgStorageApplyResp →
  appliedTo 18851) — **span 3,202 vs the heartbeat fixture's 142
  no-op** (U18's ~2,000 estimate was the real-round mid-harvest
  slice; the fixture's full Advance-to-HasReady₂ span is 3,202);
  HasReady₂ 19463 (false exit, 1,832 — U20-heartbeat-EXACT);
  projection 21295; liveCount 22936 (the landed
  `liveCountLoop_span`'s consumption site, again). Ring total
  (harvest→projection) = **13,870 steps**.
- **SC1's DRAW CLASSIFICATION RE-VERIFIED AT MSGAPP SCALE**: 2
  mapIter + 7 appendSpill + **0 OTHER** in the walk (SC1's verbatim
  classifier); the 2 mapIter are BOTH driver round-picks (one per
  round, outside the ring); in-round: 1 mapIter + 7 appendSpill; the
  ring's 5 draws all appendSpill (X1 assembly `[]*Message`, X2 the
  storage-resp `Responses` build, X3 the MemoryStorage.Append ents
  spill, X4/X5 the harness net/live sends); **the storage-resp
  nested-Step spans are draw-free** — SC1's "storage-resp sub-rounds
  choice-free" CONFIRMED as a measured span property.
- REACHABILITY EVIDENCE (D3's standing rule): the arms are reached
  by an APPEND-family MsgApp — exactly the kind the pinned run's 12
  MsgApp rounds carry (U18 census); the heartbeat fixture provably
  cannot reach them (U20's finding, now double-confirmed by the
  142-vs-3,202 Advance spans at the two fixtures).

### Slice 3 (7634f3a3) — THE FIVE STORAGE-RESP SUB-RING SPANS (deliverable 3; 559 jobs green, exit 0)

- **The construction**: the ring segment RE-PRUNED from the harvest
  call — **the ring's own read-before-write footprint is 27 CELLS**
  (the I2 footprint-for-preconditions census, §4's re-aim,
  delivered as a by-product); generator
  `artifacts/probe/MsgAppRingGen.lean` (BfLitGen printer reused
  verbatim) walks the ring concretely, propagates the MIRROR in
  lock-step, γ-verifies every boundary against the machine, and
  prints 16 boundary/crossing literals →
  `RingLit1`–`RingLit4` (4.4 MB generated, four files for parallel
  elaboration, 4–8 s each).
- **THE MIRROR COVERAGE TEST — PASSED AT RING SCALE** (the U18/U20
  ledger row's owed honest test): symEvalWindowTB walks ALL 13,870
  ring steps (storage writes, message builds, interface calls, the
  nested Steps) γ-exactly, quitting only at the five spill draws
  (all `.q3Choice`).
- **The statements** (`RingEqW1`/`RingEqW2`/`RingEqW345`/
  `RingEquation`, mirror-chain form — HhEquation's spine one ring
  up; ∀ρ ∀σ(tables) ∀stream-tail; the I2 mode justification +
  fixture-family preconditions in the module docstring): W1
  Ready-assembly 3,327/1 draw; W2 acceptReady+storage-writes+sends
  5,185/4; W3 checker-apply 324/0; **W4 THE STORAGE-RESP SPAN
  (Advance + both nested Steps) 3,202/0 — choice-free as a theorem
  shape**; W5 second-Ready 1,832/0; `ring_full_span` 13,870/5;
  bounded-completion corollaries (`ring_w4_completes`,
  `ring_completes` — the I2 consumer forms); kernel readouts:
  applied 1→2 (committed 2 on BOTH ends — the ARM commits, the RING
  stabilizes+applies: a decomposition fact the census alone could
  not state), storage ents [(dummy)] → +the appended (Index 2, Term
  1) entry, HardState nil → {Term 0, Vote 0, Commit 2} persisted,
  unstable emptied at offset 3, net +MsgAppResp ptr / live
  [false, true] (structural — the message-CONTENT cells are provably
  outside the ring's 27-cell footprint, so content readouts belong
  to the round scope; recorded, not fudged).
- **The witness** (`RingWitness`, witness-in-same-slice — the arc4b
  convention, adopted): `ring_witness_run` (the concrete 13,870-step
  instantiation at the zero valuation over the pinned tables — the
  census cross-link); **the span_consume COMPOSITION witness**:
  `ring_w4_span` consumed at a concrete non-identity placement
  (ρT 7034 8, frame cell at 7036 via relocate+extend;
  funcListSup = 31 kernel-computed), the walk RESUMED with a
  nine-step frame-cell WRITE, and the placement readout
  (applied = 2 through `fieldReadU64_ren`, address preserved below
  the shift) — the C2a instrument doing on a sub-ring span exactly
  what ShapeWitness did on a handler span; this is C2d's composition
  seam, demonstrated.
- Audit: 12 `#guard_msgs` pins (`Audit/Ring.lean`, additive,
  in-build-verified). Axioms (probe `artifacts/probe/AxRing.lean`,
  verbatim): all five spans + full span + corollaries + witness_run
  + rw_consume/rw_consume_and_resume [propext, Classical.choice,
  Quot.sound]; rw_readout + all eight payload readouts [propext,
  Quot.sound]. Hatch grep over all nine new tracked modules +
  Audit/Ring.lean: **0**.
- **THE TWO KERNEL-ROUTE FINDINGS (measured, the unit's route
  lesson — the third kernel wall, and its fix):**
  1. **Open-term tree-vs-literal γ-evaluation is the wall.** The
    crossings' first form (post-state = reflect of the machine, a
    LITERAL) forces the kernel to γ-evaluate every mirror-propagated
    SymInt tree in a ~500-cell state under FREE ρ/σ to compare
    against the literal: one such crossing ran >46 min (module),
    >4 min standalone, and the storeLoc-shaped probe >3 min —
    while the SAME comparison content at Sym level or with shared
    terms is subsecond-to-a-minute. (Bisect trail:
    `W2Bisect1`–`8` — window links 43–58 s each, visibility
    premises subsecond, the full-state store comparison the
    isolated pit. A closed Sym-level "bridge" is definitionally
    FALSE — SymInt trees are CONSTRUCTORS, a tree never equals a
    lit — refuted fast by the kernel, which is what killed the
    bridge route and pointed at the real fix.)
  2. **THE TREE-PROPAGATION ROUTE** (the fix, now the template):
    crossing posts are SET/APPEND VALUES OVER THE PRE-STATES
    (machine op order: alloc-append the backing, then store the
    target), so a crossing's untouched cells are the SAME terms on
    both sides and its kernel check compares them SYNTACTICALLY —
    no γ-evaluation of any tree, ever. Result: every crossing
    subsecond; `RingEqW2` (5 windows + 4 crossings + the span)
    builds in **135 s**, the whole ring statement stack in ~6 min
    of parallel module builds (W1 54 s, W2 135 s, W345 160 s,
    RingEquation 1.2 s, RingWitness 7.2 s). The serial one-module
    first attempt was killed at 63 min incomplete — split into
    parallel window modules AND tree-propagated, the same content
    is ~25× faster.
- [AGENT] calls, tagged:
  1. The landing collision fixed by renaming C4's witness steps
     (wHStep*) — the minimal edit; statements untouched; recorded as
     a manifest erratum above.
  2. The check-spec-anchors fix is a GATE BUG FIX in the
     false-positive direction with fail-closed behavior preserved
     and both directions re-tested — not a gate weakening (the U17
     admit-token precedent's class).
  3. The MsgApp doctor keeps the U18 Term-0 local-family convention
     (avoids becomeFollower noise; the append+commit+storage-resp
     path is identical); the append family targets Index 2 against
     the DECODED boot log rather than an assumed empty log.
  4. The five statements land at the SEGMENT boundaries the census
     measured (W1 merges SC1's HasReady+assembly rows; W3 the apply
     glue) — 5 statements covering SC1's five named arms, mapping
     recorded in the module docstring.
  5. Choice-symbolism inside the ring REFUTED at this fixture (the
     spilled artifacts are consumed downstream — ents by the second
     Ready, responses by the nested Steps — so the hh atom trick
     would quit the mirror at the first re-read); the spans are
     stated at the canonical zero draws with the ∀-stream envelope
     left to the RE-SPILL residual family (SC1's caveat, unchanged).
     Payload-field symbolism likewise refuted where the ring
     branches (HasReady's hardstate comparison, commitTo/appliedTo
     guards, stableTo arithmetic) — the hh From-symbolism
     refutation's class, recorded in the docstring.
  6. The >46-min first crossing was STOPPED and bisected rather than
     waited out (anti-grinding); the bisect found the route fix in
     eight cheap probes.
- What-this-taught-us:
  - (a) **The kernel's cost cliff is REPRESENTATION ASYMMETRY, not
    size**: 4.4 MB of literals elaborate in seconds and 13,870
    mirror steps kernel-check in minutes, but ONE open-term
    comparison between γ-images of the same state in two
    REPRESENTATIONS (tree vs literal) is effectively unbounded.
    Design rule for mirror chains: one representation per chain;
    crossings must hand successor states SHARING the predecessor's
    terms; reflect-resets belong only at chain STARTS.
  - (b) A fixture miss can be a measurement: the stale-branch first
    probe decoded the twin's snapshot-boot log (committed=1 at the
    anchor), which no census had read at the cell level.
  - (c) The per-module parallelism of window links is free velocity:
    kernel work across independent window modules uses the box's
    cores; a single module serializes it.
  - (d) Slice 0's two landing findings are both instances of
    "green-in-isolation, red-in-composition" (standalone modules vs
    joint import; single-batch vs two-batch xargs) — wave-boundary
    landings are exactly where such latent seams fire, which is why
    the landing gate must be run fully rather than inferred from
    the lanes' own greens.

### PROMOTION LEDGER updates (A4-U21)

- **The doctor+prune round-fixture generator (U18) — SECOND
  INSTANTIATION DELIVERED** (MsgApp append-and-commit family; the
  row's owed item). The template now carries the boot-log decode
  step (fit the doctored payload to the ANCHOR's real log, not an
  assumed one).
- **The mirror driver-glue/ring coverage row (U18/U20) — CONSUMED**:
  the honest coverage test ran at ring scale and PASSED (13,870
  steps, all op classes, γ-exact, five clean q3Choice quits).
- **NEW ROW: the tree-propagation crossing template** (lesson (a)):
  set/append-over-pre crossing posts + parallel window modules —
  the template for every future mirror chain with spill crossings
  (C2d's round chain is the next consumer; the Hae-family windows
  are latent consumers).
- **NEW ROW: the ring footprint census** (27 cells, fail-closed) —
  the I2 footprint-for-preconditions instrument's first output;
  consumer: C2d's round-lemma preconditions and any future sub-ring
  family fixture.
- The storage-resp anchor set row (U20) — CONSUMED (this unit's
  census + spans).
- The ∃-split extraction and scaffold-retirement rows (U19):
  untouched.

## A4-U21 exit (2026-08-26, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the U20 gate tip
f94c225a: 25810585 (the arc4b merge), 80e6f812 (the landing fixes),
7634f3a3 (the C2c build), + this log commit. Full proofs+Audit
green: **559 jobs, exit 0** (541 + 8 arc4b modules + 4 RingLit + 3
RingEqW + RingEquation + RingWitness + Audit.Ring; the count also
reflects the aggregator units). Kit pins: +12 (Audit/Ring.lean,
additive, in-build-verified). Hatch grep over every new module: 0.
Probes (gitignored): TwinMsgAppFixProbe, AnchorLogProbe,
AnchorStorProbe, MsgAppRingCensus, MsgAppRingGen (+ printer parts),
RingEqProto, RingReadoutProbe/4, CrossDiffProbe, W2Bisect1–8,
W2Bridge3, W2Prefix2, AxRing, and their .out files.

**Deliverable state vs the U21 charter (C2c):**
1. THE ARC4B LANDING — **DELIVERED** (clean auto-merge verified
   structurally; eight imports; two landing findings fixed and
   recorded — the wStep collision rename and the spec-anchor
   batching gate bug; landing gate PASS exit 0, fully green;
   optional cleanups skipped as non-trivial, noted).
2. THE MSGAPP-ROUND FIXTURE — **DELIVERED** (append-and-commit
   family at the decoded snapshot-boot log; 23,488/8 self-returning;
   39-cell read set; the generator run shared with C2d).
3. THE SUB-RING CENSUS — **DELIVERED** (full anatomy above; SC1's
   draw classification re-verified at MsgApp scale, 0 OTHER;
   storage-resp spans draw-free; reachability evidence recorded).
4. THE 5–6 PAYLOAD-PARAMETRIC STATEMENTS — **DELIVERED AS FIVE**
   (the census's segment map; ∀ρ/∀σ/∀stream-tail mirror-chain
   spans + composed ring + bounded-completion corollaries + payload
   readouts + the same-slice witness incl. the span_consume
   composition at a non-identity placement; payload-parametricity's
   honest boundary — branch-consumed fields stay concrete with the
   family recorded — stated in the module docstring).
5. Budget item (first reachable round-kind arm census: MsgVote or
   no-op) — **NOT REACHED** (the kernel-route detour consumed the
   margin; the MsgApp ARM anatomy in slice 2 — a reachable kind's
   arm census — partially covers the intent; the MsgVote/no-op
   fixture is one doctor-swap on the delivered template).

**Cost tracking vs SC1's sizing** (the charter's named report item):
SC1 priced the five statements at "≈ 8.5k steps walked once ≈ 4–5
min mirror total". Measured: the WINDOW KERNEL alone ≈ 6 min
(parallel wall ≈ 3 min) — the estimate's right order; the true cost
was the ROUTE: the crossing representation asymmetry burned ~5
worker-hours of measure-kill-bisect before the tree-propagation fix
landed it. SC1's "plus C2a-dependent composition lemmas" resolved to
ZERO new lemmas — `span_consume` consumed a sub-ring span unchanged.
Unit total ≈ one long worker session for slices 0–3 vs the implicit
one-unit sizing: on budget in units, over in wall-clock, with the
route lesson now a ledger template so successors do not repay it.

**Open gaps carried (none counted):** all U18–U20 rows as updated
above; U21 adds: the manifest-erratum convention question (joint-
import smoke checks for shared-namespace lanes — the operator's
call), the deferred arc4b optional cleanups, and the net-content
readouts at round scope (deliberately out of the ring's footprint).

**PROPOSED NEXT CHARTER (C2d, successor):** (1) the first reachable
ROUND-KIND LEMMA at the MsgApp append-family fixture — the round
chain composed from the landed pieces: the arm windows (new; the
tree-propagation template), the five ring spans (consumed via
span_consume at the round's placement — the demonstrated seam), and
the driver-glue loop spans (`rebuildLoop_span`/`liveCountLoop_span`
at their slice-2-measured sites); RoundFam membership as the
conclusion form (the R-form's first proved instance, retiring the
RoundLemmaShape scaffold's C2 obligation). (2) Budget permitting:
the MsgVote or no-op round-kind census (one doctor-swap). (3) The
masked-kill rule + the tree-propagation template briefed verbatim.

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1); the comparator-landmark STALE
(156+) AND OWED-on-scope flags stand escalated from U8–U20 — this
unit adds Audit.lean import lines (Audit.Ring) and the arc4b
landing to the scope trigger's motivation.

- 2026-08-26 A4-U21 gate follow-up (same-commit convention): unit-end
  gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the
  exit tree — **RESULT: PASS, exit 0** (`artifacts/ci-arc4-u21.log`,
  gitignored, `GATE_EXIT=0` recorded IN the log; 23 ok steps + the
  two sanctioned no-diff notes — this unit touched the arc4b merge
  (nine files), `proofs/GoLeanProofs.lean`, `proofs/Audit.lean`,
  `proofs/GoLeanProofs/Specs/Raft/{NativeS23Witness,RingLit1-4,
  RingEqW1,RingEqW2,RingEqW345,RingEquation,RingWitness}.lean`,
  `proofs/Audit/Ring.lean`, `scripts/check-spec-anchors` (the
  batching gate bug fix, both directions re-tested), this log +
  gitignored probes; no runtime code, no Corpus/, no baselines/; the
  Audit surface GREW by the 12 Ring pins — additive,
  in-build-verified). The comparator-landmark notes now read
  **STALE at 159 commits** AND **OWED (scope)** (Audit.lean import
  lines; report-only) — both stand escalated for the operator's
  merge step, as since U8.

- 2026-08-26 A4-U21 budget item, delivered post-gate (probe-only —
  `artifacts/probe/TwinVoteFixProbe.lean` / `VoteRingCensus.lean`,
  outputs gitignored; no tracked-code change, the gate record above
  stands): **THE MSGVOTE ROUND FIXTURE + CENSUS** (the first
  election-kind arm census, per U18's reachable set — one
  doctor-swap on the delivered template, as the charter priced):
  - **The real vote family** (Type 5, 1→2, Term 1 REAL — node 2 at
    Term 0 takes the m.Term > r.Term branch → becomeFollower(1,
    None) → the vote grant on the up-to-date check against the
    decoded boot log): round **19,291 steps / 9 choices /
    self-returning** (U18's real MsgVote rounds: 19,611/19,973 —
    in range); POST Term 0→1, Vote 0→1, lead 0, log untouched; net
    +MsgVoteResp (typ 6, 2→1, term 1). Read set 44 cells / 30
    iterations.
  - **THE CENSUS FINDING (sharpens U20's)**: the vote round WRITES
    the hard state (SetHardState at ring 14701 — Term/Vote
    persistence) **but produces NO storage-resp arms** — no
    MemoryStorage.Append, no newStorage*RespMsg, no nested
    `raft.raft.Step` in Advance (Advance span ~134, the no-op
    shell): the storage-resp arms need ENTRIES/COMMIT movement, not
    merely a hardstate write. The round-kind matrix so far:
    heartbeat = no ring work (U20); MsgVote = hardstate-only ring
    (~6,091 ring steps, 4 in-ring appendSpill: assembly, accept,
    and the two harness sends); MsgApp-append = the full
    storage-resp ring (13,870; this unit's spans).
  - **SC1's classification holds at the vote round too**: 6 mapIter
    + 4 appendSpill + 0 OTHER; the 4 in-ARM mapIter draws are
    becomeFollower's reset (tracker Visit — SC1's bucket table row,
    now confirmed at instance level); in-RING draws are all
    appendSpill, and the vote ring's shells are the SAME callees as
    the MsgApp ring's (HasReady/Ready/assembly/accept/Advance/
    second-HasReady) — the cross-kind shell identity SC1's per-arm
    pricing rides on, now measured at two round kinds.
  - Deliverable-5 status upgraded: **DELIVERED at census level**
    (the fixture + anatomy + draw classification; the vote round's
    own arm/ring spans are C2d+ instantiations of the same shells).

## A4-U22 — C2d: THE R-FORM'S FIRST PROVED INSTANCE — the MsgApp append-family ROUND LEMMA (2026-08-26, same worker as U21, coordinator-dispatched per the C2c report's proposed charter; C2c accepted with all [AGENT] calls endorsed)

- SAME-WORKER CONTINUATION (no fresh re-verification owed; the U21
  exit state re-confirmed: tip 4a158041 clean, 559 jobs green — the
  C2d base). Coordinator notes held live: (1) the arc4c sibling lane
  (no Seed*/Choice*/Quot* file names — none created; arc4c's worktree
  verified untouched by this session); (2) the choice-invariance
  stop-condition (did NOT fire — see the seam note below); (3)
  conventions unchanged.

### The route decision (read-first, then build)

`RoundStatement.lean` re-read closely BEFORE building: the R-form's
conclusion is an EXISTENTIAL WEAK-FrameSim placement (`∃ σF', … ∧
∃ na' fr', FrameSim …`) — NOT a literal splice — so the instance
decomposes as **one canonical run + one wholesale transport**
(`stepFnIter_sim`, Frame/Transfer.lean — the weak iteration theorem,
found present with fixed-index `TripSim`), and neither `span_consume`
nor the arc4c ~ is needed for the lemma to STATE. Two consequences,
both recorded:
- **The stop-condition did not fire**: πMa stays the concrete
  censused prefix; position 0 is THE SEMANTIC DELIVERY PICK (which
  live message is delivered), positions 1–7 latitude appendSpills —
  the factoring's INPUT identified per-crossing, the factored form
  (latitude absorbed under ~) awaiting arc4c, as the coordinator's
  note anticipated.
- **DESIGN FINDING (reported, not shimmed)**: the charter's "five
  ring spans consumed via span_consume" clause is structurally
  unavailable — `FrameSimS`'s shape clause hands back ONE contiguous
  frame splice, but a PRUNED sub-fixture (the ring's 27 cells) sits
  INTERLEAVED in the outer round state's heap list, so no FrameSimS
  placement of the ring fixture into the round state exists (the
  extend constructor also requires the frame off-image — impossible
  at identity). Sub-span reuse inside a bigger walk needs a
  multi-splice FrameSimS or a heap-permutation/finmap quotient (the
  arc4c ~ CLASS, state edition) — the coordinator's design queue.
  The instance RE-WALKS the ring at the round fixture (~11 min of
  one-time parallel kernel); the C2c spans stand as the per-arm
  interface statements + the composition-witness demonstration.

### The canonical run (93940c41; generator `artifacts/probe/RoundMaGen.lean`)

- **The full-round literals**: the C2c fixture walk extended anchor
  → anchor (23,488 steps), 12 mirror windows + 8 crossings, ALL
  γ-valid at every boundary AND crossing post (the generator's
  builtin fidelity check); GENERALIZED DIFF-CROSSINGS (the machine
  post positionally diffed against pre; the diff applied to the
  mirror state — works uniformly for the 7 spills and the PICK,
  whose post is one appended iteration cell); the pick's post-config
  reflected + γ-checked. `RoundMaLit1–6` (8.2 MB, six files, 4–11 s
  elaboration each).
- **The segment spans** (`RoundMaEqA/B/C`, parallel window modules):
  arm 7,213/3 draws (incl. `roundMa_pick` — THE SEMANTIC CROSSING,
  subsecond at shared terms), ring-head 8,171/3, send+suffix
  8,104/2; module kernel times 139 s / 225 s / 273 s (the round's
  23,488 steps ≈ 10.6 min one-time).
- **`roundMa_run`** (`RoundMaEquation`): the composed
  ∀ρ/∀σ-tables/∀stream-tail canonical run; **self-return at the γ
  LEVEL** (`roundMa_selfReturn_conc`, closed kernel_rfl — the Sym
  literals differ representationally (reflected vs propagated), the
  MACHINE configs are identical: the census's config-identity as a
  definitional fact; the Sym-level equality would have been FALSE,
  caught at design time by the U21 lesson, not by a failed build).
- **`roundMa_lemma`** (`RoundMaLemma`): **RoundLemmaShape canonMa
  canonMa' roundC0 23488 πMa — PROVED** (elaborates in 2.2 s: the
  transport glue is ~10 lines over `stepFnIter_sim` + `ExSim.ok_inv`
  — the R-form's ∀-placement quantifier discharged by the C1
  instrument wholesale, per its Abadi–Lamport docstring pin). The
  U18 SCAFFOLD marker updated in `RoundStatement.lean` (truth
  maintenance; original caveat kept for the record).
- **Witness-in-same-slice**: `roundMa_witness_identity` (the lemma
  discharged at the concrete identity placement — every premise
  concrete), `roundMa_closure` (RoundFam membership of the successor
  canon re-established — the induction's carried relation),
  round-delta readouts #eval-checked first then kernel-pinned:
  net [(true,3,1,2)] → [(false,3,1,2),(true,4,2,1)] (the MsgApp
  delivered-and-dead, the MsgAppResp live), applied 1→2 through the
  deep reader, violations 0→0 (the checker held).
- Audit: 10 pins (`Audit/RoundMa.lean`). Axioms (probe `AxRoundMa`,
  verbatim): spans/run/lemma/witness/closure [propext,
  Classical.choice, Quot.sound]; roundMa_pick / selfReturn_conc /
  all four readouts [propext, Quot.sound]. Hatch grep over all
  eleven new tracked modules + Audit/RoundMa.lean: **0**. Full
  build: **571 jobs, exit 0**.

### Shared-box interference (process note, recorded for the operator)

Four consecutive `lake build` invocations were SIGTERM'd mid-run
(exit 143; setsid-detached AND harness-managed both) during a window
when the arc-2 sibling session was churning ~160 systemd user scopes
of its own capped builds; `lake env lean` probes were never touched.
No cgroup/OOM evidence (memory stable, SIGTERM not SIGKILL); the
one-module-at-a-time retry on a quiet box went straight through.
Worth an operator look at wave-boundary cleanup patterns on the
shared box (a `pkill`-style reaper that matches other lanes' builds
would explain it); no repo change made for it.

- [AGENT] calls, tagged:
  1. Route: canonical-run + weak-transport instead of span_consume
     composition — decided from the R-form's ACTUAL pinned statement
     (read-first), with the span_consume structural limitation
     reported as the design finding above rather than shimmed
     (coordinator note (2)'s instruction followed at the
     state-equivalence analogue).
  2. The self-return equality placed at the γ level closed, not the
     Sym level (representation-honesty; would otherwise be a false
     goal — the U21 third-wall lesson applied at design time).
  3. The pick crossing shipped via the generalized diff template
     with a reflected+γ-checked config (the analyzed tree-risk paths
     documented in the generator; measured subsecond).
  4. The RoundStatement docstring edit is truth maintenance on a
     shipped module's PROSE (statement untouched), recorded here.
- What-this-taught-us:
  - (a) **Read the statement former before building the instance**:
    the charter's composition plan (span_consume) and the R-form's
    actual needs (weak transport) diverged; an hour of reading
    replaced a structurally impossible build path with a 10-line
    proof.
  - (b) The tree-propagation template GENERALIZES: the diff-crossing
    form handles ANY machine step (spills, picks — and by
    construction any future crossing kind) with the same
    cheap-comparison guarantee; it is now the round-chain template
    proper, not a spill special-case.
  - (c) At a 23,488-step chain the mirror kernel's cost splits ~10.6
    min windows + ~3 s lemma — the statement layer is now O(reading
    the transport), exactly what the compositional mode promised:
    adding the NEXT round kind costs its windows only.

### PROMOTION LEDGER updates (A4-U22)

- **The RoundLemmaShape scaffold row (U18) — CONSUMED/DISCHARGED**:
  first proved instance landed. Successor rows: (i) the remaining
  REACHABLE round kinds (MsgVote — its census landed in U21;
  MsgAppResp families; no-op arms) as further instances — each costs
  its fixture + windows only (the U21 doctor-swap + this unit's
  generator template); (ii) the ROUND-INDUCTION assembly over
  RoundFam (the C-ladder's next rung — needs the successor-canon
  question answered: canon' here is THE literal end state, not yet a
  canonicalized family representative).
- **NEW ROW: the span_consume multi-splice/permutation gap** (the
  design finding) — consumer: any sub-span reuse inside a bigger
  walk; unblock: arc4c's ~ (state edition) or a multi-splice
  FrameSimS; owner: the coordinator's design queue.
- **NEW ROW: the choice-invariance factoring seam** — πMa's
  latitude tail (positions 1–7) identified per-crossing in the
  RoundMaEq* docstrings; the factored ∀-latitude form is one rewrite
  of `roundMa_run`'s prefix when the arc4c ~ lands.
- The tree-propagation template row (U21) — generalized (lesson (b)).

## A4-U22 exit (2026-08-26, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the U21 exit
4a158041: 93940c41 (the C2d build) + this log commit + the gate
record to follow. Full proofs+Audit green: **571 jobs, exit 0**
(559 + 6 RoundMaLit + 3 RoundMaEq + RoundMaEquation + RoundMaLemma
+ Audit.RoundMa). Kit pins: +10 (additive). Hatch grep over every
new module: 0. Probes (gitignored): RoundMaGen (+ its .out rounds),
RoundMaReadoutProbe, AxRoundMa.

**Deliverable state vs the C2d charter:**
1. THE FIRST REACHABLE ROUND-KIND LEMMA — **DELIVERED** (the R-form's
   first proved instance, end to end, witnessed, with the semantic
   pick explicit and the factoring seam prepared).
2. Arm windows in the tree-propagation template — **DELIVERED**
   (generalized to ALL crossing kinds).
3. The five ring spans via span_consume — **DELIVERED AS THE DESIGN
   FINDING + the re-walk** (structurally unavailable at a pruned
   sub-fixture; reported for the coordinator's design queue; the
   R-form instance did not need it).
4. The landed U20 driver-loop spans — consumed IMPLICITLY (the
   round's rebuild/liveCount segments ride inside the windows; the
   |net|-symbolic forms remain the multi-net-shape generalization's
   tool, not this single-fixture instance's).
5. MsgVote/no-op round census — already landed in U21's budget item.

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1); the comparator-landmark STALE +
OWED-on-scope escalation stands (this unit adds Audit.lean lines
again). The arc4c landing expectation noted for a later boundary.

- 2026-08-26 A4-U22 gate follow-up (same-commit convention): unit-end
  gate `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the
  exit tree — **RESULT: PASS, exit 0** (`artifacts/ci-arc4-u22.log`,
  gitignored, `GATE_EXIT=0` in the log; 23 ok steps + the two
  sanctioned no-diff notes — this unit touched the eleven RoundMa
  modules + Audit/RoundMa.lean + the two aggregators + the
  RoundStatement docstring truth-maintenance edit + this log +
  gitignored probes; no runtime code, no Corpus/, no baselines/; the
  Audit surface GREW by the 10 RoundMa pins — additive,
  in-build-verified). Comparator landmark: **STALE at 163 commits**
  AND **OWED (scope)** — both report-only, standing escalated for
  the operator's merge step, as since U8.
