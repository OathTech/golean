# W3-init log (2026-08-27) — one writer: the U3.1-A init-cluster worker, worktree `.claude/worktrees/w3-init`, branch `w3-init` (forked from `w1-prover` @ fe4e42a3)

**Charter**: `docs/2026-08-27_w3-charter.md` incl. Amendment 1 (U3.1-A
= the init cluster: newRaft/validate/confchange-init chain (14+1 fns,
census §2.5)/MemoryStorage init/NewRawNode; consumed by init stage B,
U3.2f). Census instrument: the campaign worktree's
`docs/2026-08-27_w31-reachability-census.md` §0/§2.5/E1-E4 ([AGENT]
instrument — claims built on are re-verified against the wire below).
Sibling lane: `w1-prover` (the data-branch crossing kit) — NOT
touched; members blocked on undecidable symbolic data branches are
PARKED naming the kit (the U3.1-F park record's convention).
Conventions unchanged: capped builds only (GOLEAN_MEM_MAX=48G — two
lanes may build concurrently), box-wide lock for full builds, zero
sorry/native_decide/new axioms, [AGENT] provenance,
derivation-anchored numbers, no subject-run counts in exports,
park-not-weaken.

**QUANTIFIER-AUDIT LINE (the charter's opening requirement):**
U3.1-A builds CallSpecs/CallSpecRs = the RULES that discharge
∀-state at the init-chain call sites inside `newTwin` (∀ σ over each
member's footprint family; ∀ plans/env/k; ∀ ch demonic; ∃ n) —
consumed by U3.2f (init stage B) via `CallSpecR.consume` to conclude
the Base-clause facts at the loop head. The init cluster runs at
CONCRETE reflected config shapes (the harness config literal at
twin-lib.go:207-215 is reflected-program text — the charter's
sanctioned bounds carve-out), so member preconditions pin those
values and leave genuinely-unread positions free. No end-theorem
quantifier closes here; each spec's docstring says which ∀ it
serves.

## Successor re-verification (predecessors' top claims, re-checked before work)

All checks run 2026-08-27 against this fresh worktree.

- **Tip + cleanliness**: `git log` head = `fe4e42a3` (the U3.1-F
  partial/park commit), branch `w3-init`, `git status` clean.
  CONFIRMED. Sibling `w1-prover` is at the same fe4e42a3 (their kit
  work not yet committed) — fork point verified.
- **U3.1-F landed content present**: `CallSpecR` + `conseq`/`consume`
  in `proofs/GoLeanProofs/SpecJudgment.lean` (the sealed refusal
  rescoped to the caller-inclusive form, its docstring as logged);
  `Specs/RaftPilot/LogReadSpecs.lean` with the two exported
  CallSpecRs count-free and the step counts private. CONFIRMED by
  reading.
- **Invariant module state**: `Specs/RaftPilot/Invariant.lean`
  carries the U3.0d addenda (AbsCarrier.tm, ProgOk, four-type
  population) per the log. CONFIRMED by reading the module docstrings
  and the U3.0d log entry (deep re-verification of individual clauses
  not repeated here; nothing in this unit consumes them directly).
- **InitSpec stage A**: `initSetup_establishes` present
  (Specs/RaftPilot/InitSpec.lean) — the boundary this cluster's
  consumer (U3.2f) joins; its recorded stage-B gap is exactly this
  cluster + the newTwin prefix. CONFIRMED.
- **Box-wide build lock**: owner file read RELEASED (w1-prover
  U3.1-F exit, 10:56:55Z); zero batch lake/lean builds on the box
  (idle LSP workers only, same inventory class as predecessors'
  notes). Lock TAKEN by this lane at 11:05:17Z for the cold worktree
  build. CONFIRMED + logged.
- **Fresh-worktree state**: no `proofs/.lake`, no `deps/`, no
  `artifacts/` (gitignored — the fork carries none of the sibling's
  probe/build artifacts). `scripts/setup-deps
  --from …/w1-prover` run: all pins cloned locally (goose 3be88bb,
  perennial 43d4efa, raft 56e3200, iris-lean 3877dbe, go c19862e5f8;
  lake: iris/batteries/Qq at manifest pins), `complete`, fail-closed
  path not hit.

## Judgment calls and checkpoints

(one-line [AGENT] entries appended per decision; checkpoint block
after ≤5 units)

- [AGENT] Cold build required (fresh worktree): full `lake build` in
  `proofs/` via `scripts/capped`, GOLEAN_MEM_MAX=48G,
  LEAN_NUM_THREADS=4, box lock held; log
  `artifacts/w3init/cold-build.log`.
- [AGENT] CENSUS RE-VERIFICATION for the claims this unit builds on
  (the standing rule), performed against the subject sources +
  machine code before any spec was stated:
  * §0 config row: twin-lib.go:207-215 literal re-read (ID=id,
    ElectionTick=10, HeartbeatTick=1, Storage=nd.st,
    MaxSizePerMsg=1<<20, MaxInflightMsgs=256, Logger=twinLogger;
    all other fields zero-valued). CONFIRMED.
  * §0 storage row: ApplySnapshot(storage.go:218) at msIndex=0 →
    no ErrSnapOutOfDate; ents := [{Term:1,Index:1}];
    newLogWithSize(log.go:75) → committed=applying=applied=
    firstIndex-1=1, unstable.offset=offsetInProgress=lastIndex+1=2.
    CONFIRMED from source.
  * §2.5 reachable confchange set: Restore's non-joint route
    (VotersOutgoing empty → len(outgoing)==0 → per-cc Simple ops)
    re-read at restore.go:119-140; the 14+1 list matches the
    functions actually on that route. CONFIRMED.
  * E1-E4 entry points re-read at twin-lib.go:130/197/198/216.
    CONFIRMED.
- [AGENT] **THE DRAW CENSUS for the init chain** (this unit's key
  costing derivation, replacing the coordinator's "mostly
  straight-line" estimate with a measured-against-the-machine one):
  the machine consumes a choice at EVERY map-range pick
  (`ChoiceSite.mapIter`, `consumeAtOne=true` — a width-1 pick still
  POPS, State.lean:239) and at every REALLOCATING append
  (`appendSpill`, width = `appendSpillUpper - newLen + 1` ≈ 32+ for
  small slices, Ops.lean:1964). Consequences, derived per member
  from the subject sources:
  * ZERO-DRAW members (plain kernel spans, the U3.1-F pattern
    applies directly): SetLogger (mutex ops deterministic),
    Config.validate (no ranges/appends), NewMemoryStorage (slice
    LITERAL, not append; EnsureSnapshot allocs),
    MemoryStorage.ApplySnapshot (plainpb CloneMessage is make+copy,
    plain_clone.go:390-448 class — no append, no range),
    MakeProgressTracker (map literals only), newLogWithSize at the
    concrete post-ApplySnapshot storage (interface dispatch +
    lock walks + concrete reads), makeVoter/initProgress at the
    pr==nil arm (map INSERTS + NewInflights — no ranges),
    checkAndReturn's own frame (its callee checkInvariants is NOT
    zero-draw), joint/incoming/outgoing accessors.
  * PICK-BEARING members (map ranges over the growing voter/progress
    maps; sizes 1..3 ⇒ per-range up to 3! = 6 order branches, and
    the resulting ASSOC-LIST ORDER PERSISTS in the constructed maps
    — unlike the bf pilot's Visit, which sorts and converges):
    Config.Clone, checkAndCopy, checkInvariants (incl.
    MajorityConfig.IDs), symdiff, quorum Slice/IDs, VoterNodes,
    tracker.Visit (in reset), and every composition through them
    (Simple ×3, chain, Restore, switchToConfig, becomeFollower(0,
    None) at the init fixture, newRaft, NewRawNode). The COMPOSED
    pick tree multiplies across ranges (derivation in the U3.1-A
    park record below) — enumeration of the product is neither
    feasible nor charter-legal as a proof technique; the honest
    route is the W2 multiset map-loop rules + window crossings, and
    post-pick branches on drawn values (spill caps; normalized
    scalars) are the data-branch crossing kit's territory.
  * APPEND-BEARING: toConfChangeSingle (3 growing appends on the
    `in` slice → 3 spill picks, each width ≈ 32, and the 2nd/3rd
    appends BRANCH on the previously drawn cap — kit territory).
- [AGENT] Unit partition adopted from the draw census: WAVE A = the
  zero-draw members as CallSpecR/CallSpec exports (this session's
  landing set); WAVE B = pick-bearing members PARKED with records
  naming the blockers (the crossing kit for post-draw branches; the
  multiset-loop composition for persistent order families) — parked,
  not weakened: no spec is stated at a narrowed conclusion.

## Judgment calls — Wave A (the landed set)

- [AGENT] Probe-first per member (the F recipe): the REAL harness
  prefix run to each drained-call configuration
  (artifacts/w3init/probe-init*.log — untracked scaffolding), the
  involved cell chains dumped and mirrored into canonical footprint
  families; every transcription re-checked SYMBOLICALLY by the span
  lemmas' `kernel_rfl` (a wrong cell fails the build loudly).
- [AGENT] TWO JUDGMENT-LAYER ADDITIONS in `SpecJudgment.lean`, each
  demanded by a Wave-A member (the F worker's precedent for landing
  a form when its consumer arrives):
  * `CallSpecRN` — the NULLARY result-bearing form
    (`raft.NewMemoryStorage` takes no arguments, so no drained
    `.retV` shape exists; the span starts at the call STATEMENT with
    the caller's `targets` symbolic under the machine's own encoding
    premise `targetsPlan targets.toList = some plans`). The nullary
    SEAL rescoped to the resultless nullary form (no consumer yet).
    Proof technique: one hand-crossed entry step (`unfold stepFn;
    dsimp only; rw [henc]; kernel_rfl`) + the body span at open
    plans/env/k/ch chained by `stepFnIter_chain`.
  * `CallSpecRD` — the DEFER-TAIL exit geometry. DISCOVERY, recorded
    for every later cluster: the machine has TWO return-arrival
    geometries. A defer-free callee ends at `.returning (.frame
    plans env rlocs [] k false)` (the U3.1-F `CallSpecR` terminal);
    a callee WITH defers drains them through the frame's defer arm
    and arrives at `.next (.frame plans env rlocs [] k false)` —
    it NEVER re-visits a `.returning` frame configuration (verified
    against StepFn.lean's arms and the ApplySnapshot probe, which
    error'd "malformed call target plan" when driven past the old
    terminal with a degenerate plan). Both arrival arms perform the
    same next step (loadMany + tgtOpK), so consumers treat the two
    forms identically. EVERY MemoryStorage method (Lock/defer/
    Unlock) is in this class — the F-cluster's parked storage
    members need exactly this form; flagged to the sibling lane.
  * A second discovery inside `CallSpecRD`: the defer-DRAIN step's
    frame arm SCRUTINIZES THE TARGETS COLUMN, so a span at a fully
    open `plans` variable is kernel-stuck at that step (found as a
    kernel declaration-mismatch after a cell-by-cell state compare
    showed the transcription exact). Resolution: quantify the plans
    at the machine's own well-formed result-consuming shape
    `(sh, e :: ops) :: rest` — lossless (the frontend "always
    supplies targets for result-bearing calls"; the degenerate
    shapes are the machine's stuck-closed classes) and the whole
    span stays one kernel reduction.
- [AGENT] `Config.validate` stated ∀ id over {1,2,3} with a
  disjunction hypothesis (3 kernel spans): the id set is
  reflected-program text (`newTwin(3,2)`'s loop bounds), a case
  analysis over a program-text constant set, not a run census. A
  fully symbolic id would branch `ID == None` /
  `IsLocalMsgTarget(ID)` on an open scalar — kit territory, not
  worth it for a 3-value program-text set.
- [AGENT] Free-rider extent per member (maximal width the kernel
  admits, probed then verified): SetLogger — prior `raftLogger`
  value `w` fully free, argument pinned to interface SHAPE
  `.interface tL pv` with BOTH the dynamic type and payload free;
  validate — both interface payload Locs free (`lS`/`lL`: the span
  provably nil-checks without dereferencing — the probe ran them at
  dangling addresses), all other fields pinned to the harness
  literal; newLogWithSize — ms `snapshot`/`hardState` fields fully
  free (the span provably never reads them — the probe ran with a
  nil-Metadata stub and the kernel confirms at free values), logger
  payload free; NewMemoryStorage/MakeProgressTracker — no free
  slots (pure constructors); ApplySnapshot — fully pinned (the
  labeled parked axis below).
- [AGENT] PARKED AXIS (ApplySnapshot, labeled at birth): the snap
  argument's Voters slice is pinned at the slot-0-realized backing
  (len 3, cap 4, `[1,2,3,0]`). The harness builds `voters` by three
  REALLOCATING appends whose capacities are DRAWN (`appendSpill`,
  width = `appendSpillUpper − newLen + 1` ≈ 32-class), so the
  honest ∀-cap family puts a symbolic cap under `validateSlice`'s
  Nat-Nat comparison at the clone's `copy` — the data-branch
  crossing kit's blocker (ii) verbatim. Parking narrows the
  PREcondition family (U3.2f can consume it on the canonical-stream
  branch; the ∀-ch composition needs the kit-generalized variant or
  per-cap instances), never a conclusion.

## U3.1-A WAVE A — SIX MEMBERS LANDED

Files: `proofs/GoLeanProofs/SpecJudgment.lean` (+`CallSpecRN`,
`CallSpecRD`, each with `.conseq`/`.consume`; both seals' docstrings
rescoped on the record), `proofs/GoLeanProofs/Specs/RaftPilot/
InitCallSpecs.lean` (new; registered in `proofs/GoLeanProofs.lean`
under the contiguous `-- # w3-init` block).

| member | form | export | conclusions (U3.2f-facing) |
|---|---|---|---|
| `raft.SetLogger` (E1) | CallSpec, TRUE statics ⟨13⟩/⟨14⟩ | `setLogger_callSpec` | `raftLogger` = the installed interface value; mutex unlocked |
| `raft.NewMemoryStorage` (E2) | CallSpecRN (nullary) | `newMemoryStorage_callSpecRN` | the fresh-storage chain, terminal pinned in full |
| `raft.MemoryStorage.ApplySnapshot` (E3) | CallSpecRD (defer-tail) | `applySnapshot_callSpecRD` | nil error; ents = one (index 1, term 1) entry; `absStorageEnts = [(1,1)]`; cloned canonical snapshot chain; mutex unlocked |
| `raft.Config.validate` | CallSpecR, ∀ id∈{1,2,3} | `config_validate_callSpecR` | nil error; the three §0 defaults written (noLimit ×2, MaxCommittedSizePerReady = 1<<20); terminal pinned |
| `tracker.MakeProgressTracker` | CallSpecR | `makeProgressTracker_callSpecR` | the empty tracker (empty Voters[0]/Progress/Votes maps, nil others) — `confchange.Restore`'s required empty-config input |
| `raft.newLogWithSize` | CallSpecR | `newLogWithSize_callSpecR` | **the Base-clause log-offsets row**: committed = applying = applied = 1, unstable.offset = offsetInProgress = 2, empty unstable — as exact readback AND as the reader equation `absRaftLog σ' ⟨69⟩ = some ⟨[(1,1)], [], 2, 1, 1, 1⟩` |

Every export count-free (∃ n); step counts (25/448/1420/242/75/472)
only in the private span lemmas + this log. All spans at OPEN
`plans`(shaped for RD)/`env`/`k`/`ch` — the open `ch` is the
zero-draw certificate (reduction would be stuck on any stream
consultation). Non-vacuity: per-member `*_inhabited` ∃-discharges.
Hatch grep over both touched files: 0 sorry/native_decide/partial.
EnsureSnapshot/EnsureSnapshotMetadata/EnsureConfState, proto.Clone +
the plainpb CloneMessage family, IsLocalMsgTarget, and
MemoryStorage.FirstIndex/LastIndex(+firstIndex/lastIndex, incl.
their lock/defer walks) are covered IN-SPAN by the landed members
(no separate exports; standalone FirstIndex/LastIndex CallSpecRDs
are cheap post-pattern if the F cluster demands them).

## U3.1-A PARK RECORD — the pick-bearing remainder (park-not-weaken)

Every member below is PARKED with its named blocker; no spec was
stated at a narrowed conclusion. Blockers: **(K)** = the data-branch
crossing kit (the sibling `w1-prover` lane's unit — U3.1-F blockers
(i)/(ii): hypothesis-conditioned reduction across normalize/Nat-Nat
comparisons on drawn or symbolic scalars); **(M)** = a map-order
pick-family composition pattern (the W2 multiset map-loop rules
consumed at library ranges whose ASSOC-ORDER PERSISTS in the built
maps — a promotion-ledger candidate: bf's landed pick machinery
covers transient order (Visit sorts and converges), but the
confchange clone/insert pipeline KEEPS the pick order in
`cfg.Voters[0]`/`ProgressMap`, so the composed family is a
permutation family that never re-converges and must be carried in
lookup vocabulary through every downstream window).

- `toConfChangeSingle` — (K). 3 reallocating appends on `in`
  (restore.go:77-81 at the T1 ConfState): each consumes an
  `appendSpill` pick (width ≈ 32 at these lengths), and the 2nd/3rd
  appends BRANCH `len < cap` on the previously DRAWN cap — a
  symbolic-Nat branch per draw. Slice ranges themselves are
  deterministic (no draws).
- `Config.Clone`, `checkAndCopy`, `checkInvariants` (+
  `MajorityConfig.IDs`), `symdiff` — (M): map ranges over maps of
  sizes 1..3 (per-range up to 3! = 6 orders; a width-1 pick still
  pops the stream, so even singleton ranges shift the tape).
  `checkAndCopy`'s clone REBUILDS the maps in pick order —
  persistence.
- `Changer.Simple`/`apply`/`chain`/`Restore` — (M)+(K): the
  composed pick tree across the three Simple rounds multiplies
  (derivation: Simple#3 alone ranges Voters{1,2} (2), Progress{1,2}
  (2), IDs{1,2} (2×2), symdiff {1,2}/{1,2,3} (2×6), final
  checkInvariants IDs{1,2,3} (6×6) — the product across the chain
  is ≥ 10^4 leaves that never re-converge). Enumeration is neither
  feasible nor charter-legal as proof; the honest route is (M) with
  the postcondition a lookup-vocabulary permutation family.
- `switchToConfig` (T1 early return), `VoterNodes`,
  `quorum.MajorityConfig.Slice`/`JointConfig.IDs`, `tracker.Visit`
  — (M): collect-loops draw picks; Slice/VoterNodes sort AFTER
  (values converge, tape offsets don't), Visit converges (the bf
  precedent) but sits inside `reset` inside the (M)-blocked
  composition.
- `becomeFollower(0, None)` at init — (M) + a fixture-generation
  round: the W1 pilot's becomeFollower machinery (BfLit-class
  fixture, ~9k lines, the measured cost datum) is anchored at the
  PILOT fixture; the init instance runs at the post-`Restore` raft
  cell whose Progress map order is itself the (M) family. Parked
  behind the newRaft composition.
- `newRaft` — all of the above composed (span ≈ 20k machine steps
  measured on the canonical stream; also `fmt.Sprintf("%x")`/
  `strings.Join` over the sorted VoterNodes — concrete-reducible
  per branch) + `InitialState`/`softState`/`hardState`/
  `assertConfStatesEquivalent` (zero-draw, coverable in-span).
- `NewRawNode` — parked on `newRaft` (its own additions are
  zero-draw straight-line).
- Deferred WITHOUT blockers (middle path — zero-draw leaves whose
  only consumer is the parked composition; each is a ~1-hour member
  with today's pattern when the composer demands it): `makeVoter`/
  `initProgress`/`NewInflights`, `joint`/`incoming`/`outgoing`,
  `checkAndReturn`, `InitialState`, `softState`/`hardState`.

## COSTING ACTUALS vs the "cheapest cluster" estimate ([AGENT],
derivation-anchored)

- The coordinator's estimate ("mostly straight-line at a PINNED
  config shape → today's cheap pattern applies widely; newRaft's
  whole-chain span is long but branch-poor") is CORRECTED by the
  draw census: the confchange/tracker half of the cluster draws at
  every map range and reallocating append, and the drawn order
  PERSISTS — the cluster is cheap only on its storage/config half.
- Actuals (this session, one worker): 6 members + 2 judgment forms
  landed; per zero-draw member ≈ probe + transcription + one
  kernel span (module wall: whole-module elaboration 388 s under
  lake, dominated by the 1420-step ApplySnapshot span; individual
  spans 25..1420 steps). Wave-boundary full proofs build 65 s warm,
  539 jobs, peak RSS 7.0 GB (artifacts/w3init/wave-full-build.log).
  Cold worktree bootstrap (fresh fork): setup-deps + full cold
  build 540 jobs ≈ 19 min at 48G/4 threads.
- Remainder estimate: (K) is the sibling's unit; (M) is a NEW
  focused unit (mapPickLoop_generic consumed at the library clone/
  collect loops + a permutation-family carrier; ~1-2 Fable
  worker-days) — then the newRaft/NewRawNode composition is
  2-4 worker-days on top (window chaining through ~20k steps with
  per-range (M) crossings). U3.2f additionally needs the harness-
  side newTwin prefix (appends → (K)-class cap families) — flagged
  so stage B's charter prices it.

## WAVE A CHECKPOINT (branch state at commit)

- LANDED: SpecJudgment + InitCallSpecs as recorded above; aggregator
  gains the contiguous `-- # w3-init` import block.
- Builds: module target build EXIT=0 (58 jobs, 388 s cold-module;
  artifacts/w3init/ics-build.log); **wave-boundary FULL proofs
  build (box lock held + released): EXIT=0, 539 jobs, wall 65 s
  (warm tree; 8 modules rebuilt incl. the SpecJudgment downstream),
  peak RSS 7.0 GB** (artifacts/w3init/wave-full-build.log). The two
  retained interface witnesses are in the aggregate target set —
  GREEN (build-enforced).
- No differential owed (proofs/docs only); no Audit/*, no scripts/*,
  no GoCore, no baselines touched; trust surface untouched.
- FOR THE LANDING AUDIT: (a) the two judgment-form additions
  (`CallSpecRN`, `CallSpecRD`) and the two seal-docstring rescopes
  in `SpecJudgment.lean` are proof-layer (untrusted machinery) but
  judgment-shape changes — flag for the delta review; (b) the
  ApplySnapshot parked axis (slot-0 cap pin) is a labeled
  PREcondition narrowing whose ∀-ch generalization is owed to
  U3.2f; (c) the defer-tail exit-geometry discovery affects the
  F-cluster's parked storage members (they need `CallSpecRD`, not
  `CallSpecR`) — coordinator should relay to the kit lane.
