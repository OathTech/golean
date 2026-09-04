# C-arc step 1 — G-U, the uniform choice-consumption rule (2026-09-04)

**Status:** LANDED on lane `c-arc-gu` (SHA in the landing record
below). **Provenance:** design gate G-U RULED [USER] 2026-09-04 as
recommended — relayed by the [AGENT] coordinator («Great, this sounds
good - let's move ahead with the plan»; cited as relayed, not
firsthand), `docs/2026-09-04_reasoning-surface-plan.md` §5.4 / §3.U;
executed [AGENT] inside that ruling. Evidence:
`docs/evidence/2026-09-04_c-arc-gu/`.

## 1. The rule

One rule, every site (`GoLean/GoCore/State.lean`):

```lean
def Choices.consumeAt (site : ChoiceSite) (bound : Nat) (ch : Choices) : Nat × Choices :=
  if bound ≤ 1 then (0, ch) else ch.consume bound
```

A consult POPS the stream iff it has a choice (bound ≥ 2); at bound ≤ 1
it is inert — `(0, ch)`. `Choices.consumeAtE` (the record-emitting
form) records exactly when it pops. The `SitePolicy` structure and the
`ChoiceSite.policy` table are DELETED; what survives of the table is
`ChoiceSite.canonicalSlot0 : ChoiceSite → String`, the per-site
canonical-member docstring (audit C-2's convention), which carries no
executable policy.

Before G-U the rule was per-site (`SitePolicy.consumeAtOne`): `mapIter`
popped even at width 1 — its last MANDATORY candidate (one candidate
left, no stop slot: a forced pick) — and `appendSpill`/`l2Entry`/
`l2Arrival` were flagged `true` but never consult at width 1 by
construction; every other site was `false`. So the ONLY behavioural
site of the change is the width-1 `mapIter` consult.

**The Q3 provenance, made explicit.** The deleted table attributed the
width-1 pop to "memo §5 ruling Q3". That ruling ([USER] Mike,
2026-08-19, `docs/2026-08-19_bug005-map-range-memo.md` §5) defines the
CANONICAL MEMBER — the machine at the zero stream, stop ordered LAST —
and says nothing about popping at width 1; the pop was the stage-A
[AGENT] transcription of the code as it stood. G-U supersedes that
transcription ([USER] 2026-09-04, relayed); the Q3 ruling itself is
unchanged and still holds: the zero stream picks slot 0 at every width
whether or not it pops, so the canonical produce-all member is the
same machine run. Recorded at the latitude inventory's E9 entry.

## 2. Lemmas (the one-lemma family)

State.lean: `consumeAt_le_one (hb : bound ≤ 1)`, `@[simp] consumeAt_one`,
`@[simp] consumeAt_zero`, `consumeAt_of_lt (hb : 1 < bound)`,
`consume_fst_lt`, `consumeAt_fst_lt (0 < bound)`,
`consumeAt_fst_singleton (idx < bound) : (consumeAt site bound [idx]).1 = idx`;
`consumeAtE_fst_snd`, `consumeAtE_le_one (hb)`, `consumeAtE_of_lt (hb)`.
DELETED: `consumeAt_pop`, `consumeAtE_pop`, `consumeAt_mapIter`,
`consumeAt_l2Entry`, `consumeAt_l2Arrival`, `Config.boundarySite_consumeAtOne`
(MultiSound) — the per-site width-1 no-pop facts (`consumeAt_nilValueMethodText_one`,
the L1/L4/postOp/backEdge/tryLock singleton non-consumptions) are now
instances of `consumeAt_le_one`/`consumeAt_one`; every proof that
supplied a policy proof (`rfl` / `boundarySite_consumeAtOne c`) drops it.

The "≥ 2 by construction" facts the table asserted in prose are now
THEOREMS, because the uniform rule makes the proofs need them:
`one_lt_appendSpillWidth` (Machine.lean; `appendGrowthCap_ge` moved
beside it) with `@[simp] Choices.consumeAt_appendSpill` restated at the
`appendSpillWidth` bound, and `arrivalCases_multi_length : … = .ok (.multi os) → 1 < os.length`
(MultiSound) under `arrivalPlan_of_multi`. `l2Entry`'s `.picks` needs
no length fact: `applySelect_ok_or_panic_any_ch` now reasons through
`consumeAt` abstractly (`consumeAt_fst_lt`).

Projections (wave-(iii) B8 — the ONE account of where the stream is
consulted): `mapIterConsult?` reports `none` at width ≤ 1 (the last
mandatory candidate), so `seqConsumption`'s contract "`some` ⇔ the
consult pops" is exact at every site; `poolConsumption` was already
uniform (its boundary/L4/entry arms guard ≥ 2). `stepFn_consumption_none`
gains the width-1 `mapIterK` case (the step is oblivious: pick 0, stream
untouched — `stepFn_mapIter_pick` with `consumeAt_le_one`);
`stepFn_consumption_some`'s `mapIterK` arm extracts width ≥ 2 from the
projection. `stepFn_mapIter_pick`/`_stop` take their `hcons` in
`consumeAt` form (callers: the completeness witness `[idx]` via
`consumeAt_fst_singleton`, `stepFn_sound`, `allStreamsOk`'s probe
`[i]`). The CLI accountant and the tracer are projections of
`seqConsumption`/`poolConsumption` (B8) and follow with no edit; grep
confirms no hand mirror remains (`consumeAtOne`: zero hits in `GoLean/`).

## 3. Preservation — the SET of behaviours is unchanged

A width-1 consult has exactly one member; popping or not popping
selects the same member (pick 0 = `c % 1` = the forced 0). Every
enumerator/certificate branches over `[0, bound)` at the ACCOUNTED
consults only, and a width-1 consult contributes one branch either way
— the certified observation sets of the membership and confluent lanes
are stream-independent and identical. The differential's strict lane
compares the EMPTY stream against gc; the empty stream yields pick 0 at
every consult whether it pops or not, so no default observation moves.

**The realization shift.** Under a FIXED non-empty stream, every
consult after a former width-1 `mapIter` pop now reads one entry
earlier. The bijection on streams: delete from the old stream exactly
the entries the width-1 `mapIter` consults drew (`streamValue ≠ '-'`
on a `mapIter`/bound-1 record). It is total, injective on the consumed
prefix, and stream-length-decreasing; the certificate is executable:
the new machine on the transformed stream must reproduce the old trace
minus the width-1 records, byte for byte (`gu-bijection.py`, §5).

## 4. What the plan forecast vs. what happened

§3.U forecast "a handful of rows whose fixed stream crosses a
range-over-map" would RE-PIN. The re-pin was EMPTY: no baseline row is
indexed by a non-empty stream. The strict lane's differential row is
the empty stream (unchanged by construction); its three fixed
adversarial streams are an INVARIANCE check (same observation as the
default), and a row that stays invariant on the re-indexed streams
stays PASS — a row that did NOT would have been an under-certified
strict row, i.e. a real finding, and the rule for that was STOP. The
membership `members=` pins and the confluent certificates are
enumerated sets, stream-independent. So "realized members under fixed
streams re-pinned" reduces to: the 13 rows whose fixed-stream traces
shift (§5) are re-certified by the bijection and by the unchanged gate,
not by a baseline edit.

## 5. Evidence (all in `docs/evidence/2026-09-04_c-arc-gu/`)

- BEFORE/AFTER whole-corpus traces (`scripts/choice-trace-corpus --dump`,
  six streams per row, 3364 rows exported, 2 excluded as in every trace
  since the A-series): `before-summary.txt`, `after-summary.txt`, the
  sorted dumps. Per-site totals: `mapIter` 2006 → 1307 (−699 = the
  width-1 records), every other site identical; 0 violations / alarms /
  driver mismatches both sides.
- **The bijection certificate** (`gu-bijection.py`): the AFTER machine on
  the TRANSFORMED streams reproduces the BEFORE dump minus the 699
  `(mapIter, 1)` records byte for byte — 23016 records, and status +
  observation hash identical on all 20184 (row, stream) lines. PASS.
- **Realization shift, enumerated** (`shifted-rows.tsv`): 63 (row, stream)
  lines = 13 rows × the 5 non-empty streams (never the default stream):
  strict `control-flow/labeled-branch-range-map`,
  `imported-goose/semantics/allocator/allocate-distinct`,
  `imported-goose/semantics/maps/iterate-map`, `maps/added-entries-bound`,
  `native-smoke/maprange`, `quorum/joint/{committed-min,ids-union,
  vote-both-pending,vote-both-win,vote-disagree-lost,vote-disagree-pending}`;
  membership `maps/added-entry-count`, `noodler/membership/insert-then-delete-during-range`.
  In every one of the 63 lines the consults after the shift are further
  `mapIter` picks (a second range-over-map in the same program; column
  `sites_after_shift`). On the SAME streams the 11 strict rows'
  observations are unchanged (the re-indexed pick order of the second
  range is not distinguished by these rows' observables — which is what
  their strict-lane 3-stream invariance check certifies, and it stays
  green); the 2 membership rows realize a
  different member of their certified set under `9,8,7,…` — each new
  observation hash is one the row already exhibited BEFORE under another
  stream (`membership-realization-shift.txt`), and the gate re-enumerates
  the sets. Rows re-pinned: NONE (§4).
- **Set identity by the gate**: `scripts/capped scripts/ci --diff` PASS —
  3402 = 3189/213, FULL 3402/3402, ZERO drift (no re-pin), membership
  sets re-enumerated and slow-tier certified records verified, 153/153
  eval tests, reconciler 0 HIGH / 0 new (`ci-diff.txt`).


## 6. Records touched

`GoLean/GoCore/{State,Machine,Multi,StepFn,MachineSound,MultiSound,MultiStreams,EnumDedupSound}.lean`,
`GoLean/CLI.lean` (docstring), `docs/2026-08-11_latitude-inventory.md`
(§0 census paragraph + table rows, the tryLock note, §9 flag 5, E9's
new CONSUMPTION RULE bullet with the Q3 provenance),
`docs/2026-08-04_nondeterminism-doctrine.md` (census sentence),
`docs/BUGS.md` (BUG-087's fixed-record wording), `docs/2026-08-31_qrow-rulings.md`
(Q-TRYLOCK implementation record wording), `TODO.md` (item U done),
`docs/2026-09-04_reasoning-surface-plan.md` (§5.4 G-U → LANDED, §5.1
table), `docs/2026-09-03_design-hygiene-arc.md` (step (v) item 1,
"not this arc's" bullet). Historical logs (`w32-log`, the design
audits, the boundary-set note) keep their period wording.

## 7. Landing record

Lane `c-arc-gu` off `main` @ `ac45aedd`; the change is commit
`9cece4e8` (tagged `[TRUST-ADJACENT: GoCore choice consumption rule;
stream re-index re-pin, [USER]-ruled G-U]`; this landing line is the
records-only follow-up). Gate at the lane tree: `scripts/capped
scripts/ci --diff` PASS, 3402 = 3189/213, FULL, zero drift; no baseline,
corpus, frontend, decoder or wire change; no new `ChoiceSite`; no
`sorry`/`axiom`/`native_decide`; no `partial` in GoCore. Branch-complete;
the audit ask is the coordinator's to pose; merge/push are the [USER]'s.
