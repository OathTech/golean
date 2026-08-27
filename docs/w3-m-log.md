# W3-m log (2026-08-27) — one writer: the (M)-mechanism worker, worktree `.claude/worktrees/w3-m`, branch `w3-m` (forked from `w1-prover` @ ce05ecd1)

**Charter**: build THE (M) MECHANISM — map-order pick-family
composition (design note `docs/2026-08-27_m-mechanism-design.md`,
which carries the LINEAGE line and the quantifier-audit table) — and
consume it toward the parked init-cluster chain
(`docs/w3-init-log.md` §"U3.1-A PARK RECORD"), delivering the
Base-clause conclusions owed to U3.2f (progress-map population =
voters, terms 0 at init). HARD RULE: no judgment-form additions to
`SpecJudgment.lean` (reserved to the w1-prover lane this wave); a
genuinely needed new form is PARKED by name. Conventions: capped
builds only (GOLEAN_MEM_MAX=48G — sibling lane may build
concurrently), box-wide lock for full builds, zero
sorry/native_decide/new axioms, no bounded/enumerative technique,
[AGENT] provenance, derivation-anchored numbers, count-free exports,
park-not-weaken.

## Successor re-verification (fork-point claims, re-checked before work)

All checks run 2026-08-27 against this fresh worktree.

- **Tip + cleanliness**: `git log` head = `ce05ecd1` (the w1-prover
  crossing-kit wave checkpoint), branch `w3-m`, `git status` clean;
  sibling `w1-prover` at the same ce05ecd1. CONFIRMED.
- **Fresh-worktree state**: no `proofs/.lake`, no `deps/`.
  `scripts/setup-deps --from …/w1-prover` run to completion (exit 0).
  Cold full proofs build started under the box lock (log
  `artifacts/w3m/cold-build.log`).
- **The landed forms present**: `CallSpecR`/`CallSpecRD`/`CallSpecRN`
  + conseq/consume in `proofs/GoLeanProofs/SpecJudgment.lean`;
  `InitCallSpecs.lean` Wave-A members; `Sym/Crossing.lean` (the
  data-branch crossing kit) with its design note. CONFIRMED by
  reading.
- **The W2 rule this unit consumes**: `mapPickLoop_generic`
  (element-type-generic) + `consume_lt`/`eraseIdx_length_of_lt`/
  `mem_of_mem_eraseIdx` in `GoLeanProofs/MapLoops.lean` group 4;
  `MapMem`'s pick-step family (`candidates_toEntries`/
  `mandatory_toEntries`/`stepFn_pick_bind`/`stepFn_iter_done`) —
  found SPECIALIZED to u64→u64 values (the counts encoding), which
  the confchange maps (`struct{}`/`*Progress`/`bool` values) do not
  fit: the value-generic siblings are this unit's layer-2 content.
  CONFIRMED by reading.

## Judgment calls and checkpoints

- [AGENT] Box-wide build lock: owner file read RELEASED (w1-prover
  crossing-kit exit 13:19:07Z); zero batch builds on the box (idle
  `lake serve` LSP workers only). Lock TAKEN by this lane 13:28:27Z
  for the cold build; released at the wave boundary (entry below).
- [AGENT] THE READER CHECK (the brief's go/no-go, performed BEFORE
  building): no order-sensitive consumer of map-derived data exists
  in the T1 fragment. Basis (details in the design note §KEY CHECK):
  `mapRead`/`mapReadD` store-order contract + Invariant.lean's
  lookupI/∀-membership-only consumption + the subject-side census
  (lookups/ranges/len/commutative counts/sorted extraction;
  `ConfState.Equivalent` sorts both sides,
  raftsubject/raftpb/confstate.go:71-78; census §2.8 kills every
  `String()`). VERDICT: the carrier can be reader-level Perm
  families; design go.
- [AGENT] Module placement: the mechanism lands as
  `proofs/GoLeanProofs/MapPerm.lean` (imports MapMem + MapLoops +
  AbsTwinCheckerRead; below every Specs/RaftPilot consumer). No
  SpecJudgment change (the serialization rule honored by
  construction — the family rides inside P/Q of the landed forms).

## THE (M) MECHANISM — LANDED (docs + module + first real member)

Files: `docs/2026-08-27_m-mechanism-design.md` (LINEAGE +
quantifier-audit table + the reader-check verdict),
`proofs/GoLeanProofs/MapPerm.lean` (847 lines — the carrier),
`proofs/GoLeanProofs/Specs/RaftPilot/MapOrderSpecs.lean` (968 lines —
the first member + readback consumers), aggregator `-- # w3-m` block
(contiguous).

**MapPerm layers (all green):**
- Layer 1 (order-quotient readback): `NodupKeys`/`lookupP` +
  `lookupP_perm` (THE quotient-crossing lemma), `mapPairs_perm`/
  `mapPairsD_perm` (decode transports over the AbsTwinCheckerRead
  lenses' walks — a permuted `mapData` reads back as a permuted
  abstract list), `perm_cons_eraseIdx`, `sortedLT_eq_of_perm`
  (unique sorted representative — the Slice/VoterNodes/Visit
  converging read).
- Layer 2 (value-generic machine facts): `toEntriesV` +
  `candidates`/`mandatory`/`pick-bind`/`pick-key`/`done`/
  `rangeStart`/`mapEntryIndex?`/`mapAssignValue` value-generic
  siblings of the MapMem u64→u64 family (demanded by `struct{}`/
  `*Progress`/`bool` values; keys stay uint64 — recorded boundary).
- Layer 3 (the composition rule): `mapPickLoop_perm` — the
  Perm-CONSERVATION pick loop with the TAPE-SUFFIX conclusion.

**THE FIRST REAL MEMBER — `quorum.JointConfig.IDs` CallSpecR
(`jointConfigIDs_callSpecR`), the parked init-chain member, LANDED at
the FULL (M) family:** ∀ id lists (arbitrary length AND order — the
∀-in half of the family; `Nodup` + u64-normalized = a Go map's own
well-formedness), ∀ plans/env/k, ∀ ch, ∃ n: the call returns a fresh
map whose entry list is `idKV ids'` for an ∃-PACKAGED permutation
`ids'` of `ids` — the ∃-out half; the built order IS the machine's
pick order, never re-converged, exactly the blocker-(M) shape. Span
architecture: W1 entry window (117 steps `kernel_rfl`, the source
mapData VALUE fully symbolic — never scrutinized), the conditioned
range-START, the pick loop (11 steps/iteration: pick + 3 kernel
windows + 2 conditioned steps — key-read at the symbolic front,
insert via `mapAssignValue_toEntriesV`), the DONE step, W2 tail (103
steps: 4 kernel windows at the symbolic-tail states + 3 conditioned
steps). Exports count-free; step counts private.

**Readback consumers (the second genuinely-different class, in-unit):**
`idsFam_population` (the `Pair.progress`-clause shape: key column =
ids, membership transfer, lookup DEFINED at every voter —
order-insensitively across the whole family), `idsFam_lookup_agree`
(any two family members answer every lookup identically — what makes
every `lookupI`-vocabulary invariant clause order-insensitive),
`idsFam_sorted_collapse` (the family collapses at a `slices.Sort`
boundary). Non-vacuity: `idsPre_inhabited` at the census's canonical
`{1,2,3}`; the two consumer classes use disjoint halves of the
carrier (design note §Non-vacuity).

## Machine/rule findings ([AGENT], recorded for successors)

- (i) **The frontend's array-range desugar** (probe): `$rcoll` copy +
  `$rlen`/`$ridx`/`$rfirst` + `.loop (boolLit true)` with a
  first-flag head — outer array bounds are TYPE-LEVEL program text
  (`[2]MajorityConfig`), so outer iterations are walked concretely
  (the charter's carve-out); only the INNER map ranges draw.
- (ii) **The P9 seqn-splice stall recurs at the (M) states**: an
  empty `seqn` splice under an env carrying the symbolic allocation
  front is kernel-stuck on the env `DecidableEq`
  (`stepFn_seqn_splice` is the fix — StepKit's P9, confirmed at a
  second site class).
- (iii) **`mapPickLoop_generic` does not expose the tape-suffix
  discipline** the CallSpec judgment requires (`ch' <:+ ch`);
  `mapPickLoop_perm` therefore carries its own induction (same
  skeleton) with the suffix conclusion — promotion-ledger candidate:
  fold the suffix clause back into `MapLoops` when a second
  suffix-needing loop consumer bites.
- (iv) **IDs' frame exit is the `CallSpecR` `.returning` geometry**
  (no defers anywhere in the confchange/tracker/quorum chain's
  reachable members — `CallSpecRD` not needed here).
- (v) Probe scaffolding (untracked): `artifacts/w3m/ProbeIDs.lean`,
  `probe-ids*.out` (the 255-step canonical trace with full seam
  configs), `ProbeW2c.lean` (the seam-diff debug harness).
- [AGENT] No Audit pin additions this wave (the sibling W3 lanes'
  convention — InitCallSpecs/LogReadSpecs landed without pins);
  flagged for the landing audit rather than silently absorbed.
- [AGENT] `slices.Sort` for `VoterNodes`/`Slice`: NOT in the wire's
  funcs/methods as a lowered body under that name — its lowering
  route needs a census check before those members are attempted
  (recorded; not blocking — both are sorted-readback CONSUMERS of
  the carrier, served by `sortedLT_eq_of_perm` once their spans
  exist).

## Checkpoint 1 (branch state at commit)

- Full proofs build GREEN: 542 jobs, EXIT=0
  (artifacts/w3m/full-build1.log; box lock HELD through the session).
  Cold bootstrap: setup-deps + cold build 542 jobs EXIT=0
  (artifacts/w3m/cold-build.log). Module walls: MapPerm 412ms,
  MapOrderSpecs 5.5s (warm deps).
- Hatch grep over both new files: 0 sorry/native_decide/partial.
- No SpecJudgment change (the serialization rule honored); no
  Audit/*, no scripts/*, no GoCore, no baselines, no trust surface.

## Threading demonstration (post-checkpoint-1 addition)

`idsFam_threads` (MapOrderSpecs): the member spec consumed at ANY
family member of a canonical id set concludes in the SAME family —
the ∃-out/∀-in composition closure (`Perm.trans` at the `conseq`
boundary), the exact shape every chain composite consumes the carrier
through. GREEN.

## PARK RECORDS — the remaining chain members (park-not-weaken; each
with its probe-measured record where probed this session)

- `toConfChangeSingle` — **(K)** unchanged (3 reallocating appends,
  drawn caps, 2nd/3rd branch on the drawn cap). Its outputs are
  SLICES (deterministic order) — no (M) content of its own.
- `tracker.Config.Clone` — **PROBED** (artifacts/w3m/probe-clone*.out):
  326-step canonical span, terminal = the `CallSpecR` `.returning`
  geometry ✓. Structure: closure creation + 4 closure calls — ONE
  pick-loop clone of `Voters[0]` (the landed IDs machinery's shape,
  placement-specific segments to re-derive) + 3 nil-map early
  returns (concrete-handle kernel branches) — then the
  array/struct/return build. MEASURED FINDINGS: (a) the frontend
  DROPS `make(map, len(m))`'s capacity hint (`makeMap` with no size
  operand — no len-at-symbolic-entries crossing needed); (b) the
  post-loop tail performs ~12 allocations at the SYMBOLIC front →
  ~20 conditioned steps (the established P9-class init/store/read
  treatment — mechanical, not conceptual); (c) closure-call sites
  drain via `callValArgsK`, for which NO judgment form exists — the
  inner spans must be INLINED (the maybeTerm precedent) or the
  chain needs **the PARKED JUDGMENT FORM: `CallSpecV`** (the
  function-VALUE call-span sibling of `CallSpecR` at the
  `callValArgsK` drained shape) — named per the serialization rule
  (SpecJudgment is the w1-prover lane's); `Restore`'s per-cc ops
  closures make this form unavoidable at the chain top, and
  `Visit`'s per-id closure calls repeat it in clusters C/D/E.
  Estimated at the IDs actuals: ~2.5–3× the IDs member.
- `confchange.symdiff` — **PROBED** (artifacts/w3m/probe-sd*.out):
  495-step span at l={1,2,3}/r={2,4} (n = 3 ✓ = |l\r|+|r\l|),
  CallSpecR terminal ✓. The comma-ok is a dedicated `.mapLookup`
  STATEMENT → `applyRhsOp .mapLookup` → `mapLookupValue` →
  `mapEntryIndex?` — MapPerm's `mapEntryIndex?_toEntriesV` already
  covers the scan; the needed layer-2 addition is the ~30-line
  `mapLookupValue_toEntriesV` hit/miss pair. TWO sequential pick
  loops (the second at the shifted front — machinery in place); the
  count invariant is filter-length, Perm-invariant by
  `Perm.filter` + `length_eq` (the CONVERGING-read direction).
  Per-iteration ~35 steps with ~10 conditioned (2 inits + 3 reads +
  rhs-apply + 2 stores + splice + pick). Estimated ≈ 1.5× the IDs
  member.
- `checkAndCopy` — (M) via Clone + the POINTER-VALUED Progress
  rebuild loop (key+value binders, per-iteration alloc, pointer
  insert — the layer-2 `*Progress` instance; the reader-level
  conclusion via `mapReadD`/`mapPairsD_perm` cancels the
  order-dependent fresh-address indirection — designed in the note,
  not landed).
- `checkInvariants` — consumes IDs' ∃-family output through exactly
  the `idsFam_threads` shape; ranges the built map (draws) + `trk`
  lookups (the same `mapLookupValue` crossing class); error arms
  concrete-refuted at the T1 family.
- `Simple`/`apply`/`chain`/`Restore` — the composites of the above;
  `apply`'s per-cc switch is concrete program-text at T1's cc
  values; `chain`/`Restore` add the ops-closure calls (the
  `CallSpecV` need above).
- `MakeProgressTracker` consumers / `switchToConfig` / `VoterNodes` /
  `becomeFollower(0,None)` / `newRaft` / `NewRawNode` — as the init
  lane's park records, with today's additions: `switchToConfig`'s
  `ConfState()` calls `Slice` ×4 — sorted-collapse consumers
  (`sortedLT_eq_of_perm` serves the READBACK; the spans need (K)
  for `Slice`'s reallocating appends and the unresolved
  `slices.Sort` lowering-route census (recorded above)).

## Base-clause status vs U3.2f (honest accounting)

OWED (from the brief): progress-map population = voters, terms 0 at
init — these are conclusions OF THE newRaft COMPOSITION, which
remains parked (above). DELIVERED THIS WAVE toward them: the exact
vocabulary bridge — `idsFam_population` (the `Pair.progress`-clause
conjunct shapes: population + lookup-defined, proved
order-insensitive across any (M) family), `idsFam_lookup_agree`
(every `lookupI`-vocabulary clause is family-invariant), and the
family-closure (`idsFam_threads`) — so the composition's Base-clause
conclusions will arrive in U3.2f-consumable form by construction.

## COSTING SIGNAL for clusters C/D/E ([AGENT], derivation-anchored —
the coordinator's reset()/bcastAppend question)

- The (M) mechanism makes the ∀-draw discharge at every map range
  MECHANICAL: the measured datum is the IDs member — 968 lines for a
  255-step one-loop member (5 conditioned-step classes; module wall
  5.5s warm). Per-member cost scales with (i) the body's
  conditioned-step count (~25 lines each; symdiff's body ≈ 10/iter
  vs IDs' 2/iter) and (ii) the post-loop tail's symbolic-front
  allocation count (Clone ≈ 20).
- `Visit`-class members (reset/bcastAppend): the collect half is
  IDs-shaped (cheap now); `Visit` SORTS (the sorted-collapse
  readback is landed — `sortedLT_eq_of_perm`), and its per-id
  CLOSURE call needs `CallSpecV` (the parked form) or inlining;
  `reset`'s Progress rebuild writes through POINTERS (the map's
  assoc order is PRESERVED — the (M) family is maintained, not
  re-drawn, so downstream Progress reads stay in the same family).
  VERDICT: (M) removes the map-order blocker for C/D/E; the
  remaining blockers there are `CallSpecV` (closures), the
  `slices.Sort` lowering census, and (K) (reallocating appends).

## WAVE-BOUNDARY CHECKPOINT (branch state at commit 2)

- Wave-boundary FULL proofs build: EXIT=0, 542 jobs
  (artifacts/w3m/wave-full-build.log; the two retained interface
  witnesses in the aggregate target set — GREEN, build-enforced).
- Hatch grep over both w3-m files: 0 live sorry/native_decide;
  0 partial in proof-facing code (probe scaffolding is untracked).
- Trust surface untouched: no Audit/*, no scripts/*, no GoCore, no
  baselines, no SpecJudgment (the serialization rule held — the one
  genuinely needed new form, `CallSpecV`, is PARKED BY NAME above).
- No differential owed (proofs/docs only). [AGENT] Box-wide build
  lock RELEASED at wave end (owner file updated).
- FOR THE LANDING AUDIT: (a) `MapPerm` is kit content whose public
  theorems carry NO Audit pins (the sibling W3 lanes' convention
  this wave — flagged, not absorbed; the MapLoops §pins convention
  would add them at consolidation); (b) `mapPickLoop_perm` carries
  its own induction rather than consuming `mapPickLoop_generic`
  (finding (iii): the landed rule hides the tape suffix) — the
  promotion-ledger entry is recorded; (c) layer 2's value-genericity
  is exercised in-unit at `struct{}` only — its second instance is
  MapMem's landed u64 family (the same pattern's sibling), with
  `*Progress`/`bool` as the chain's demanded instances (design-note
  vacuity check).
