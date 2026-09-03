# B1 — map entry-identity stamps: design note and preservation argument (2026-09-03)

Status: LANDED on branch `hygiene-b1-stamps` (design-hygiene arc slice
1; plan `docs/2026-09-03_design-hygiene-arc.md`; source proposal
`docs/2026-09-03_grumpy-professor-review.md` §3 B1 / §5 item 1, the
second design audit's Q11). Provenance: [AGENT] execution inside the
[USER]-ratified arc (Mike, 2026-09-03, relayed by the coordinator:
«Great, let's do it as you propose …»); every design choice below is
[AGENT] unless marked. Evidence dir:
`docs/evidence/2026-09-03_hygiene-b1-stamps/`.

## 1. What changed (the definitions)

- `GoValue.mapData (entries : Array (Nat × GoValue × GoValue)) (nextId : Nat)`
  (Value.lean). Every entry is `(id, key, value)`; `nextId` is the
  map's own counter. `mapAssignValue` on an ABSENT key pushes
  `(nextId, key, value)` and bumps the counter; on a PRESENT key it
  `set!`s `(id, key, value)` with the entry's existing id (the E10
  always-replace pin is unchanged — new key, new value, same
  identity). `mapDelete` erases the entry; `clearMap` empties the
  array; neither touches `nextId`, so an id is never reissued.
  `makeMap` starts at `#[] 0`.
- `Cont.mapIterK … (produced : Array Nat) (start : Array Nat) …`
  (Machine.lean). `mapRangeStartSets` returns the base cell and the
  live entries' ids; `mapIterLiveEntries` returns the stamped entries;
  `filterCandidateList produced es = es.filter (fun e => !produced.contains e.1)`
  (pure); `mapIterCandidates` = the filtered live entries, validated
  self-normalized (unchanged guard); `mapIterMandatoryRemains cands
  start = cands.any (fun e => start.contains e.1)` (pure `Bool`).
- `stepFn`'s pick arm (StepFn.lean) binds `key value` from the picked
  `(id, key, value)` and pushes `id`; the apply arm returns
  `.next k'` directly. `Step.mapIterNext` lost its mandatory-success
  premise (the test is total); `Step.mapIterStop`'s premise is
  `mapIterMandatoryRemains cands start = false`; `Step.stmtOpApply`
  lost its `contAfterStmtOp` premise and concludes `.next k`.
- `StepM.thread` / `StepMFine.thread` (Multi.lean, NPDRF.lean) lost the
  `pruneForeign` premise and conclude
  `⟨(m.threads.setIfInBounds i c') ++ efs.toArray, σ', i⟩` again;
  `stepThread`'s partnerless arm is `stepFn` and nothing else.
- Observation JSON (`CLI.goValueJson`) projects ids away: the
  `mapData` observation shape is byte-identical to before (no wire
  change; the Go harness never emits `mapData`, and no expression can
  produce one).

DELETED (14 definitions, 14 theorems, 3 rule premises):
`keyInKeyList`, `keyInKeys`, `mandatoryInList`, `removeKeyList`,
`pruneIterFramesKey`, `pruneIterFramesAll`, `contAfterStmtOp`
(Machine.lean); `mapPrunePlan`, `Config.mapContM`, `foreignPruneError`,
`pruneForeignOne`, `pruneForeignList`, `pruneForeign` (Multi.lean);
`GoValue.eqbPairsWith` (Value.lean; replaced by `eqbTriplesWith`).
Theorems: `pruneForeign_of_plan_none`, `mapPrunePlan_some_shape`,
`mapPrunePlan_of_spawnPlan`, `pruneForeign_singleton` (Multi.lean);
`stepFn_stmtOpApply_shape` (MultiSound.lean — existed only for the
prune's successor check); `Config.mapContM_locSup`,
`pruneForeignList_wf`, `pruneForeign_wf` (MultiWfSound.lean);
`removeKeyList_sup`, `pruneIterFramesKey_locSup`,
`pruneIterFramesAll_locSup`, `contAfterStmtOp_locSup`,
`goValueListSup_map_fst_le` (StateWf.lean); `GoValue.eqbPairsWith_sound`
(StateEqb.lean; replaced by `eqbTriplesWith_sound`). Premises: the
`pruneForeign` premise on `StepM.thread` and `StepMFine.thread`, the
`contAfterStmtOp` premise on `Step.stmtOpApply`, the mandatory-success
premise on `Step.mapIterNext`. Net: 17 files, −649 lines (513 added,
1162 deleted) before the records.

## 2. Two recorded deviations from the review's sketch

1. **Per-map counter, not a global `ExecState` field.** The review
   left this open. Per map keeps `ExecState` untouched, so no
   `{ s with … }` site, no `alloc_shape`/`StateWf` carrier, and no
   pool-level invariant changes; `StateWf` sees only the entry
   payloads (`goValueEntriesSup` ignores the `Nat`). A frame never
   mixes maps (it carries `base` and loads only that cell), so ids
   need be unique only within a map. [AGENT]
2. **`mapIterMandatoryRemains` is a pure `Bool`**, not
   `Except GoError Bool` — there is nothing left to refuse (no key
   comparison, no fuel). `Step.mapIterNext` therefore has no
   "mandatory computation must succeed" premise; `stepFn`'s width is a
   total function of `cands`. The `produced`/`start` carriers stay
   `Array Nat` (the review said `List Nat`) so every pattern's arity
   and the `produced.push` shape are unchanged. [AGENT]

## 3. Why this is the same machine (the preservation argument)

Conventions as in the review §3: "preserving" = for every program,
stream and fuel, the same `Except GoError Result`, and the choice tape
consumed at the same sites with the same bounds in the same order.

**The relation.** Fix a map cell with live table `E` (old:
`Array (GoValue × GoValue)`; new: `Array (Nat × GoValue × GoValue)`
plus `nextId`), related by `Eᵒ = E.map (·.2)` (same order, same keys,
same values). Relate an old frame `(base, producedK, startK)` to a new
frame `(base, producedI, startI)` under the invariant `I`:

- (I-prod) for every live entry `(id, k, v) ∈ E`:
  `id ∈ producedI ⟺ ∃ k' ∈ producedK, valueEq k' k`;
- (I-start) likewise with `startI`/`startK`;
- (I-fresh) every id in `producedI ∪ startI` is `< nextId`, and ids in
  `E` are pairwise distinct and `< nextId`;
- (I-keys) the live keys of `E` are pairwise `valueEq`-DISTINCT and
  `valueEq` is REFLEXIVE on each of them.

(I-keys) is the map's own invariant on the old side too: `mapAssign`
inserts only when `mapEntryIndex?` finds no `valueEq`-equal key, so
distinctness holds on every reachable cell; reflexivity is the
condition under which "key membership" is a coherent notion at all —
see §4 for the one place it fails.

**Established at range start.** `mapRangeStartSets` gives
`producedK = producedI = []` and `startK = keys of E` /
`startI = ids of E`: (I-start) holds by (I-keys) reflexivity and
distinctness; (I-fresh) by the cell invariant.

**Preserved by every step.**
- *Pick.* Old candidates = entries of `Eᵒ` whose key has no
  `valueEq`-equal member in `producedK`; new = entries of `E` whose id
  ∉ `producedI`. By (I-prod) these are the SAME positions of the same
  table, hence the same list in cell order — same `cands.size`. Old
  mandatory = some candidate's key `valueEq`-equal to a `startK`
  member; new = some candidate id ∈ `startI`; equal by (I-start). So
  the width `cands.size + (if mandatory then 0 else 1)` is identical,
  the ONE consumption at `ChoiceSite.mapIter` pops the same head, the
  picked slot is the same entry (same key, same value → same
  `bindIterVars`, same allocation, same successor state), and the
  stop slot is legal on exactly the same states. Pushing `k` to
  `producedK` and `id` to `producedI` re-establishes (I-prod) for
  that entry (reflexivity) and changes no other entry's status
  (distinctness). The done-check (`cands = #[]`) coincides likewise.
- *`mapAssign` on an absent key.* Old: a new key `k` not
  `valueEq`-equal to any live key — so not in `producedK`/`startK`
  either (those are drawn from formerly live keys… except a key that
  was deleted and re-created, which the old prune REMOVED from both
  sets exactly for this reason). New: a fresh id `nextId` ∉
  `producedI ∪ startI` by (I-fresh). Both sides: a fresh candidate,
  non-mandatory — the created-entries clause. (I-fresh) is restored
  by the bump.
- *`mapAssign` on a present key.* Old replaces the stored key by a
  `valueEq`-equal one (E10); new keeps the id. (I-prod)/(I-start) are
  stated through `valueEq`, so both sides' membership is unchanged.
- *`mapDelete k` / `clearMap`.* The entry leaves `E` on both sides.
  Old ADDITIONALLY walks every in-flight frame over `base` in every
  goroutine (`contAfterStmtOp` + `pruneForeign`) and removes every
  `valueEq`-equal key from `producedK` and `startK`; new does nothing
  to any frame. `I` is stated only over LIVE entries, so the deleted
  entry's disappearance from `E` makes both (I-prod) and (I-start)
  vacuous for it — with or without the prune. The prune's ENTIRE
  purpose was the next re-creation: a re-created `k` had to be
  absent from `producedK`/`startK` (fresh candidate, non-mandatory);
  on the new side the re-created entry carries a NEW id, absent from
  the id sets by (I-fresh). This is why the pool-level walk, the
  `Except`-monadic key comparison, and the O(threads × depth) cost
  can all go: identity does the prune's work for free, in every
  goroutine at once, at the cell.
- *Every other step* touches neither `E` nor the frames' sets.

**Same tape.** Since the candidate lists coincide position for
position and the mandatory test agrees, every consultation of
`ChoiceSite.mapIter` has the same bound and the same slot meaning; no
other site is affected (the prune consumed nothing). The identity on
streams, not a bijection — no re-pin. The enumerator's own statistics
say the same thing mechanically: on every E9 row the confluent/racy
`detail` column (steps / probes / sites / leaves / maxdepth) is
byte-identical before and after (§6).

**The ±0 subtlety the review flagged** (`valueEq`-equal but
`eqb`-distinct keys: `+0`/`-0`, interface boxes): the old prune removed
ALL `valueEq`-equal keys and `mapEntryIndex?` finds the entry by
`valueEq`, so "same entry" (new) and "equal key" (old) coincide — `I`
holds. Fine.

**Formal status.** No Lean bisimulation lemma is stated: the two
frame types no longer coexist in the tree (the old one is deleted),
and stating `I` across commits would mean re-importing the retired
definitions. The regression is (a) the full differential at zero
drift, (b) the set-equality of the E9/noodler membership and
confluent rows (§6, transcripts in the evidence dir), and (c) the
identical enumerator statistics on those rows. The proof-side
invariants that DID move (loc-boundedness, candidate normalization,
∀-streams obliviousness, pool wf, sequential-vs-pool coincidence) were
re-proved arm-for-arm (§5) — none weakened, three premises deleted.

## 4. Where the argument does NOT go through — and what that found

(I-keys) requires `valueEq` reflexive on live keys. Go `==` is
irreflexive on NaN (spec#Comparison_operators), and `valueEq` follows
it: a `float64` NaN key, or an array/struct/interface holding one, is
`valueEq`-unequal to ITSELF. On the old side such a key could never be
a member of `producedK` (nor of `startK`), so its entry stayed a
non-mandatory candidate after every production and the canonical
zero-stream run picked it forever: `maps/nan-key-range` fuel-outs on
main's binary (red-first transcript in the evidence dir) where gc
prints 32. The new side marks the ENTRY produced and terminates with
32 on every stream. The spec's production table is over entries,
each produced once; the old model was too wide (it admitted any
number of productions) with a wrong canonical member. Recorded as
BUG-088 (fixed by construction, pinned by `maps/nan-key-range`, born
green, differential + confluent). No pre-existing corpus row ranged
over an irreflexive-keyed map (the noodler NaN rows insert/delete/len
only), so this is the ONE behaviour the slice changed, on a class
with zero prior coverage — reported as such, not buried in the drift.
The aggregate members of the class — `[1]float64{NaN}`, a struct
field holding NaN, an `any` box holding NaN — behave identically
(audit fix round F2: all three fuel-out on main, all three match gc on
the branch; rows `maps/nan-key-range-aggregate/{array,struct,interface}`,
gc 32 / 73 / 32).

**Governance (audit fix round F1).** Calling this "a narrowing to the
spec, not an envelope move" was wrong in kind: E9's envelope is the
[USER]'s 2026-08-19 ruling ("any latitude in the Go spec should be
supported" — narrowings rejected), and on irreflexive keys the modeled
set DID shrink — the old machine admitted, for a NaN entry, any
number ≥ 1 of productions and an immediate stop; the new one admits
exactly one production. Every member the old set lost is spec-illegal
(the production table is over entries, once each), but the decision
whether that shrinkage is a bug fix or a re-envelope is the [USER]'s,
not this slice's. Status: [AGENT]-made by construction, DISCLOSED
(here, inventory §E9, arc plan, BUG-088), REFERRED TO THE [USER] for
ratification at the merge sign-off; the coordinator poses it with the
audit-ask. If declined, the slice does not merge as is.

## 5. Proof deltas (arm for arm)

- StateWf.lean: `goValueEntriesSup` and its six lemmas over stamped
  entries (`p.2.1`/`p.2.2`); `Cont.locSup`'s `mapIterK` arm drops the
  two (now loc-free) sets; `mapEntries_locSup`/`mapLookupValue_locSup`
  destructure the `nextId`; `mapRangeStartSets_locSup` keeps only the
  base bound; `filterCandidateList_sup` is a two-line `List.filter`
  subset fact; `mapAssignValue_pres` gains the present-key `entries[i]?`
  arm (the do-block's `let (entries, nextId) ← match …` lifts the
  continuation into the match arms — split first); the mapDelete/
  clearMap arms and the `stmtOpApply`/`mapRangeStart`/`mapIterNext`
  cases of `step_preserves_wf` lose their prune/start-key bounds; the
  `snapshotEntriesSelfNormalized*` lemmas restated over triples.
- MachineSound.lean: `stepFn_sound`'s former `case101` (the apply arm,
  once threaded through the prune bind) is now closed by the generic
  pass and its explicit block is gone; `case170` names the frame's
  pattern variables and `generalize`s the pure mandatory test;
  `step_complete`, `step_complete_any_wf`, `stepFn_mapIter_ok_any`,
  `_pick`, `_stop`, `_done`, `allStreamsOk` and its soundness proof
  carry `hmand : mapIterMandatoryRemains cands start = mand` and
  rewrite with it explicitly (simp would not rewrite the pure test
  under the `if`); `stepFn_oblivious`'s statement and its apply case
  updated; `mapIterCandidates_normalized` loses a bind.
- MultiSound.lean: `stepThread_single` no longer needs the
  singleton-prune lemma; `stepThreadInto_sound` and `stepM_complete`'s
  thread arms drop the prune hypothesis (the `++ [].toArray` reshaping
  now happens in the goal, not in a premise).
- MultiWfSound.lean: `stepThread_wf`'s partnerless arm is
  `pool_set1_wf` directly. MultiStreams.lean / EnumDedupSound.lean: the
  obliviousness arms drop the prune's stream-neutrality step.
- NPDRF.lean: `StepMFine.thread` thread-local again;
  `stepM_le_stepMFine` one argument shorter; obstruction 7 DISCHARGED
  BY CONSTRUCTION (text kept as the record).
- StateEqb/MachineEqb: `eqbTriplesWith(_sound)`; `mapIterK`'s eqb arms
  compare `Nat` arrays.
- Race.lean: the `.next (.mapIterK …)` footprint arm is UNCHANGED (one
  cell read); its docstring restates the detector-soundness argument:
  the pick's only memory input is that read, the id sets are
  thread-private data derived from that cell's loads, and no goroutine
  step rewrites another's frame — so a foreign mutation that could
  change a pick writes the cell the pick reads (HB-ordered or refused).

## 6. Set equality (before = main @ 345ef090 build; after = this slice)

`scripts/capped scripts/diff-one …` on 19 of the 23 enumerating map
rows (+ 3 added after-only: the two non-map noodler membership rows
and the new NaN row); the other 4 — `maps/jitter-draw`,
`maps/range-first-key`, `race/negative/map-rw`,
`race/negative/len-map` — were verified identical (set, result, stage)
by the pre-merge audit. Every machine-enumerated observation set EQUAL; every result and
stage EQUAL; every enumerator statistics string EQUAL. Full table and
files: the evidence dir's `sets/{before,after}/`.

| row | lane | machine set before | after |
|---|---|---|---|
| maps/cross-goroutine-delete-readd/drf | membership | {3, 4} | {3, 4} |
| maps/cross-goroutine-delete-readd/insert | membership | {1, 2} | {1, 2} |
| maps/cross-goroutine-delete-readd/racy | racy | {race} | {race} |
| maps/cross-goroutine-delete-noreadd/delete | confluent | {3006} (steps=137326 …) | same, same stats |
| maps/cross-goroutine-delete-noreadd/clear | confluent | {1} (steps=13917 …) | same, same stats |
| maps/cross-goroutine-delete-noreadd/other-map | confluent | {3006} (steps=137371 …) | same, same stats |
| maps/delete-insert-readd-during-range | membership | {1, 2} | {1, 2} |
| maps/delete-readd-during-range | membership | {-1, 3, 4} | {-1, 3, 4} |
| maps/added-entry-count | membership | {1, 2} | {1, 2} |
| noodler/membership/three-key-map-order | membership | all 6 permutations | all 6 |
| noodler/membership/insert-then-delete-during-range | membership | {2, 3} | {2, 3} |
| noodler/membership/delete-other-key-during-range | confluent | {1} | {1} |
| race/negative/map-range-iter | racy | {race} | {race} |
| maps/{delete,clear,update}-during-range, delete-unreached-during-range, added-entries-bound, noodler/maps/single-entry-range | differential | PASS | PASS |
| maps/nan-key-range (NEW) | differential | — (main: fuel-out) | PASS, 32 |

The only textual difference in the two `latest.tsv` files is
`three-key-map-order`'s gc SAMPLE tally (`exhibited=2` → `exhibited=3`
of the 6-member machine set): five fresh gc runs happened to land on
three distinct orders instead of two — the oracle's randomness, not
the machine's set, which is identical.

## 7. What this slice did NOT change, stated

- The envelope (latitude inventory §E9): identical sets, identical
  tape; canonical member unchanged (zero stream = first candidate in
  cell order = insertion order for a mutation-free map).
- The race footprint of map iteration: one cell read per pick.
- The wire schema and the observation JSON.
- `ChoiceSite`s, their policies, `consumeAtOne` for `mapIter`.
- The gate and the baselines — except the ADDED row
  `maps/nan-key-range` (PASS), re-pinned with its reason in the
  baseline header.

Side effects worth knowing: `GoValue.eqb`/`==` on `mapData` (and so on
`ExecState`) now also compares ids and `nextId` — a STRICTER equality,
which is sound for the dedup engine's use (equality → same behaviour)
and can only merge fewer states; `repr` of a `mapData` (refusal
diagnostics only) shows the stamps.

## 8. Audit fix round notes (informational; 2026-09-03)

- **F5 — fail-closed surfaces retired, and why.** Gone with the prune:
  `keyInKeyList`/`removeKeyList`'s `Except`-monadic refusals (an
  ill-formed `valueEq` comparison inside a frame's key set),
  `foreignPruneError`'s goroutine-naming prefix on a refusal raised in
  a FOREIGN frame, and `pruneForeign`'s `.internal` arm for a
  pruning-op apply with an unexpected successor shape. None of these
  had a counterpart to keep: id membership is total (`Nat` equality),
  no frame is ever rewritten from outside, and the apply arm has no
  post-apply step to check. The fail-closed surfaces of map iteration
  that REMAIN are unchanged: the per-pick self-normalization
  validation (`mapIterCandidates` → `.stuck`), the `expected map data`
  refusals on a malformed cell, and `mapAssignValue`'s new
  `missing map entry at index` arm (unreachable when `mapEntryIndex?`
  returns an in-range index; kept as a named refusal rather than a
  `set!` no-op).
- **F6 — dedup strictness.** `GoValue.eqb`/`ExecState ==` on `mapData`
  now compare ids and `nextId` too, so the `--engine dedup` state
  equality is stricter (sound: it merges fewer states, never more).
  The audit measured the effect on the dedup-engine rows: nil — node
  counts identical up to 7.9M nodes. Recorded as the audit's
  measurement, not this note's.
- **F8 — id freshness is not yet a `StateWf` carrier.** The invariant
  the argument in §3 leans on — (I-fresh): the live ids of a cell are
  pairwise distinct and `< nextId` — holds by construction of the
  three writers (`makeMap` `#[] 0`, push-and-bump, erase/clear leave
  the counter) but is not stated in `StateWf`; no current proof needs
  it (the wf carriers are loc-boundedness and candidate
  normalization). Candidate lemma for a later slice (natural home: the
  A2/A3 memory-representation slice, where the cell payload becomes
  its own type): `MapCellWf : ids.Nodup ∧ ∀ id ∈ ids, id < nextId`,
  preserved by `applyStmtOpCore`'s map arms and `storeTarget`'s map
  half.
