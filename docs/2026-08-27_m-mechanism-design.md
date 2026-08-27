# The (M) mechanism — map-order pick-family composition (W3, w3-m lane)

One writer: the w3-m worker (worktree `.claude/worktrees/w3-m`, branch
`w3-m`, forked from `w1-prover` @ ce05ecd1). Unit log:
`docs/w3-m-log.md`. Problem of record: the U3.1-A park blocker **(M)**
(`docs/w3-init-log.md` §"U3.1-A PARK RECORD") — Go map-range iteration
draws a pick per step, and in the confchange `Restore`/`Simple`/`apply`
chain the resulting ASSOCIATION ORDER PERSISTS in the built maps
(`cfg.Voters[0]`, the `ProgressMap`), so the composed pick tree over
the init chain is a ≥10⁴-leaf family that never re-converges.
Enumeration is neither feasible nor charter-legal as proof; this note
designs the family carrier and its composition story.

> **SUPERSESSION NOTE (triage landing, 2026-08-27).** The CallSpec
> forms this note threads the family through (the ∃-out/∀-in
> composition between CallSpecs, and the `jointConfigIDs_callSpecR`
> member) were cancelled and deleted with the judgment calculus
> (archived at `archive/callspec-era`). The CARRIER is live and
> landed (`MapPerm.lean`, judgment-free; `mapPickLoop_perm`
> scaffold-labeled pending its G-MAPITER discharge witness); the
> threading discipline described here re-instantiates at the tier-3
> map-range law's spec vocabulary (G-MAPITER), not as CallSpecs.

## LINEAGE

The mechanism instantiates the **multiset-abstraction /
iterate-then-canonicalize classic**: iteration-order independence
proved by a loop invariant over the multiset of processed-plus-
remaining elements (the folklore "a fold over a finite map is a fold
over ANY list enumeration, up to permutation" — SSReflect's
`perm_eq`/bigop reasoning; VeriFast/CN-style finite-map models as
association-list quotients), combined with the
**observational-equivalence / permutation-quotient** argument (two
states that differ by a key-order permutation are indistinguishable to
every lookup-vocabulary observer).

**Where this construction diverges from the classics:** we do NOT
canonicalize the carrier. The machine's heap genuinely keeps the drawn
association order (`.mapData es` in pick order), and no sort or
normalization step exists in the subject at the composition boundaries
— so the quotient lives ONLY in the spec vocabulary. Concretely:

* a map-building span's postcondition ∃-packages the built entry
  order, constrained by `List.Perm` to a canonical association list
  (never pinned to one order);
* the NEXT spec in the chain ∀-quantifies its precondition over that
  same family (demonic re-entry: whatever order the tape produced);
* every reader crosses the quotient through the transfer lemmas
  (first-match lookup, membership, length, decode `mapPairs`/
  `mapReadD` transport, unique-sorted readback) — never through
  positional access.

The classics collapse the quotient at each loop exit (canonicalize,
then reason); here the family is THREADED between CallSpecs, because
the machine state itself stays un-canonical. That threading — the
∃-out/∀-in permutation family across call boundaries — is the novel
composition story, and it is deliberately the SMALLEST possible delta
on the classic: every per-loop obligation is still the classic's
multiset-conservation invariant, discharged by the landed W2 rule
`mapPickLoop_generic` (`GoLeanProofs/MapLoops.lean` group 4).

## QUANTIFIER AUDIT (the charter's opening requirement)

| quantifier | rule that discharges it |
|---|---|
| ∀ ch latitude draws at each map-range site | `mapPickLoop_generic` (W2's ∀-pick strong induction: one consumed choice + one erased candidate per iteration), instantiated with a **Perm-conservation invariant** (`built ++ image(remaining) ~ canonical` — constant under every pick) |
| the persistent assoc order of each built map | ∃-packaged in the producing spec's postcondition as a `List.Perm` family member (reader vocabulary — the decoded list, so per-order fresh-address indirections cancel); **re-∀-quantified** at the next consumer's precondition |
| ∀ σ over each member's footprint family | the member's CallSpecR/RD, exactly as in U3.1-A/F (the family now includes the order parameter) |
| ∀ plans/env/k, ∀ ch, ∃ n | the landed judgment forms (`CallSpecR`/`RD`/`RN`), unchanged |

"By instances" is never an answer: the ≤3! = 6 orders per range and
the ≥10⁴-leaf product are never enumerated — every per-range family is
closed by the one pick-loop induction, and the product is closed by
composing specs whose pre/post are stated over the whole family.

## THE KEY CHECK — are the readers order-insensitive? (verdict: YES)

Checked before building (the design's go/no-go). The consumers of
map-derived data in the T1 fragment:

1. **The proof-side readers** (`Specs/Raft/AbsTwinCheckerRead.lean`):
   `mapRead`/`mapReadD` return entries IN STORE ORDER by contract, and
   the module docstring pins consumption to LOOKUP vocabulary
   ("order is exposed only because an association list must have
   one"). `absProgressOf`, `absLeaderOf`, `absByIndex`, `readNodeGot`
   all route through them.
2. **The invariant module** (`Specs/RaftPilot/Invariant.lean`): every
   map-touching clause is `lookupI`/∀-membership shaped — the C2
   `progress` clause verbatim (`∀ q ∈ pm, …` twice + `∀ v ∈ voters,
   ∃ p, lookupI pm v = some p`), `LeaderOfCorr`/`ByIndexCorr` are
   `lookupI` equations at every key. No positional read exists.
3. **The subject side** (census §2.5/§2.6 + the init chain read
   against the sources): map lookups (`trk[id]`, `Votes[id]`,
   `p[1][id]`), further map RANGES (draws again — covered by the same
   ∀-pick discharge), `len`, commutative counts (`symdiff`,
   `TallyVotes`), and SORTED extraction (`MajorityConfig.Slice`,
   `VoterNodes`, `Visit` — `slices.Sort` before use;
   `ConfState.Equivalent` at `assertConfStatesEquivalent` sorts BOTH
   sides, raftsubject/raftpb/confstate.go:71-78). The dead-by-
   formatting class (census §2.8) removes every `String()`.

**No genuinely order-SENSITIVE consumer exists in the T1 fragment.**
(If one appears in a later fragment — e.g. positional access to a
map-derived slice built without a sort — the carrier still holds the
exact order existentially; such a consumer would force the family
member to be named at that read, not a redesign. Recorded as the
mechanism's boundary.)

## The carrier

Reader-level permutation families. For a built map read back (through
`mapRead`/`mapReadD`-class lenses) as `pm : List (Int × ν)`:

```
PermFam canon pm := pm ~ canon        -- List.Perm
```

with `canon` the canonical association list (sorted-by-key spelling,
a reflected-program-derived constant at the init chain's concrete
config). Postconditions conclude `∃ pm, reader σ' = some pm ∧
pm ~ canon` (plus `NodupKeys canon` once, as a lemma about the
constant); preconditions consume `∀ pm, reader σ = some pm → pm ~
canon → …`. Machine-level: the state families are parameterized by
the entry list `es` (the `.mapData` payload) with `es`'s DECODE
constrained by Perm — the U3.1-F symbolic-memory discipline extended
by one list parameter per map.

## The lemma inventory (module `proofs/GoLeanProofs/MapPerm.lean`)

Layer 1 — the order-quotient readback (pure, machine-free):
* `NodupKeys`, preserved by Perm (`List.Perm.map` + nodup transfer);
* `lookupP` (generic first-match; definitionally `lookupI` at Int
  keys) with `lookupP_eq_some_iff_mem` (Nodup ⇒ lookup = the unique
  member) and **`lookupP_eq_of_perm`** — THE quotient-crossing lemma;
* membership/length transfer = stock `List.Perm`;
* `mapPairs_perm` / `mapPairsD_perm` — decode transport: reading a
  permuted `mapData` yields a permuted abstract list (fail-closed
  arms preserved);
* `sortedLT_eq_of_perm` — unique sorted representative: the
  converging-read discharge for `Slice`/`VoterNodes`/`Visit`-class
  sorted extraction.

Layer 2 — the value-generic machine facts (the `MapMem` u64→u64
family generalized; promotion justified by ≥3 demanding value types:
`struct{}` (MajorityConfig/Learners), `*Progress` (ProgressMap),
`bool` (Votes)):
* `toEntriesV : List (Int × GoValue) → Array (GoValue × GoValue)`
  (u64-wrapped keys, values raw);
* `filterCandidateList_toEntriesV`, `candidates_toEntriesV` (value
  normal-form as a per-consumer hypothesis), `mandatory_toEntriesV`,
  `stepFn_iter_doneV`, `stepFn_pick_bindV` — the pick-step family at
  any value type (the confchange collect loops bind the KEY only, so
  `bindIterVars` never normalizes the value; candidates validation
  still checks it, hence the hypothesis);
* the fresh-key insert model (`mapAssign` on a key not in the map
  appends the entry — the persistence primitive), value-generic.

Layer 3 — the composition rule:
* **`mapPickLoop_perm`** — the Perm-conservation instantiation of
  `mapPickLoop_generic`: a collect-shaped iteration (`picking p from
  rem extends the accumulator by g p`) drains to the exit with
  `acc' ~ acc₀ ++ rem₀.map g` — ∃-packaging the order, at every
  choice stream. (The g image may carry per-iteration fresh
  addresses; the reader-level conclusion is taken AFTER decode, where
  the indirection cancels.)

## Non-vacuity (≥2 genuinely different consumers, in-unit)

1. **The confchange-chain class** (order ∀-in, order ∃-out — the
   persistence direction): the collect/rebuild loops of the init
   chain (`JointConfig.IDs` / `Config.Clone` / `checkAndCopy`),
   consumed at symbolic-order inputs, concluding Perm-family outputs.
2. **The tracker Progress-map readback class** (the quotient-crossing
   direction): the U3.2f Base-clause conclusions — progress-map
   population = voters, terms 0 — stated through `absProgressOf` +
   `lookupI`, transferred across the family by `lookupP_eq_of_perm` +
   membership transfer; plus the sorted-readback consumer
   (`VoterNodes`-class) via `sortedLT_eq_of_perm` — a genuinely
   different readback (canonicalizing vs quotient-crossing).

Vacuity check for the interface: the two consumer classes use
DISJOINT halves of the lemma inventory (layer 2+3 vs layer 1), so
neither is a renaming of the other.

## Scope, boundaries, retirement

* The mechanism carries NO judgment-form change (`SpecJudgment.lean`
  untouched — the serialization rule; the family rides inside P/Q of
  the landed forms).
* Trusted surface untouched: everything here is proof-side method
  (StepKit's banner applies; no name may appear in a headline
  statement closure).
* Retirement condition: if a later wave lands a canonicalizing map
  representation in the MACHINE (a semantics change — not currently
  proposed and differential-constrained), the carrier collapses to
  equality and this module's layer 1 becomes trivially consumable;
  layers 2–3 are ordinary kit content and stay.
