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
