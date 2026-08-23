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
