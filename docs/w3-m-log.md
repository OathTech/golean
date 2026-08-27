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
