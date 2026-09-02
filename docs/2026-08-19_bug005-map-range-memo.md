# BUG-005 design memo — live map iteration (bug-fix arc slice 4, 2026-08-19)

MEMO ONLY — no implementation. Slice 4 is design-gated
(`docs/2026-08-19_bugfix-arc-charter.md` §slice 4): interpreter/GoCore
surgery, always gated on Mike's ruling. The probes below are landed
(three new corpus rows, colors recorded pre-fix); the model is not.

## 0. The defect, and what the spec actually forces

`mapRange` snapshots the map's entry array once
(`mapRangeSnapshotEntries`, Machine.lean:914) and `Cont.mapIterK`
iterates the snapshot (StepFn.lean:595-609), so iteration observes
neither delete/clear nor value updates, and performs no per-iteration
user-memory read (Race.lean U1 — the S3 fourth symptom). Four pins red:
`maps/{delete,clear,update}-during-range`, `race/negative/map-range-iter`.

The governing spec text (spec#For_statements, range clause, quoted from
the pinned `deps/go/doc/go_spec.html` go1.26.5):

> "The iteration order over maps is not specified and is not guaranteed
> to be the same from one iteration to the next. **If a map entry that
> has not yet been reached is removed during iteration, the
> corresponding iteration value will not be produced.** If a map entry
> is created during iteration, that entry **may be produced during the
> iteration or may be skipped. The choice may vary for each entry
> created and from one iteration to the next.**"

**A sharpening this memo adds to the BUG entry:** stale VALUES are not
merely gc behavior — they violate a FORCED point in the spec's own
table. The range clause's production table defines the map iteration
values as `key k K` and **`m[k] V`**, under the preamble "**For each
iteration**, iteration values are produced as follows" — the second
iteration value IS the index expression `m[k]`, evaluated when the
entry is reached. So live value reads are spec-mandated, not a gc
member; `maps/update-during-range`'s red is a forced-point violation
twice over (once via the table, once via E9's removal-clause argument).

So the fix's obligations split exactly:
- **FORCED**: removed-before-reached entries not produced; values read
  at production time (`m[k]` per the table); each start-entry that
  survives the whole iteration produced exactly once ("traversed").
- **LATITUDE (inside the fix)**: entries CREATED during iteration —
  per-entry, per-occurrence "may be produced or may be skipped". This
  choice must be ENVELOPED at a choice-consumption site, never silently
  resolved to gc's member (doctrine, binding requirement 1).

## 1. Probes (all scratch: `artifacts/probe/map005/observables.go`; 400 runs each)

| probe | shape | gc go1.26.5 observation |
| --- | --- | --- |
| A | 4 start keys; first iteration creates 4 more | n ∈ {4,5,6,7,8} — distribution `4:53 5:34 6:55 7:60 8:198`. **gc itself exhibits the FULL per-entry latitude**, from "no created entry produced" to "all four produced", across plain re-runs of one binary — no GODEBUG or seed control needed (per-range order re-randomization does it) |
| B | 2 keys; each iteration deletes only the OTHER (unreached) key | n=1 in 400/400 — the forced removal clause, isolated from the delete-everything shape |
| C | 3 keys; each iteration deletes the CURRENT key then re-adds it | n=3 in 400/400 — gc **never re-produces a re-created already-produced key** |
| D | probe C + forced mid-iteration growth and shrink (64 inserts/deletes inside the loop) | n=8 (start size) in 400/400 — the no-re-production member survives rehash pressure |
| E | 2 equal-valued keys; body updates both | second value always 99 (`[10 99]`:351, `[20 99]`:49 — both orders exhibited, update always visible) — the forced live-value read |

*Addendum 2026-09-02 [AGENT, E9-prune slice audit fix round F2]: probes
C/D's bold claim — gc never re-produces a re-created already-produced
key — is REFUTED. Those probes had no SMALL intervening insert (D's 64
inserts force a growth that relocates everything). With ONE fresh key
inserted between the delete and the re-create on a 3-key map, gc
go1.26.5 re-produces the re-created key in ~87% of runs (sweep 1→87%,
2→75%, 3→63%, 4→50%, 5→37%, 8→0%; size 8 never; same- and
cross-goroutine alike). Record: `docs/spec-divergence-ledger.md` L-012's
2026-09-02 ADDENDUM; evidence dir
`docs/evidence/2026-09-02_e9-cross-goroutine-prune/` (`gc-insert-sweep.txt`,
`gc-same-goroutine-insert.txt`); rows `maps/delete-insert-readd-during-range`,
`maps/cross-goroutine-delete-readd/insert`. The at-most-once-per-key
narrowing this section motivated was already REJECTED at the 2026-08-19
[USER] ruling; the addendum shows it was also false of gc.*

The race probe is not re-run here: BUG-005's entry records it (gc
`-race` flags a concurrent map write against an ACTIVE range as
"Previous read ... runtime.mapIterNext()", exit 66), and
`race/negative/map-range-iter` pins it red.

**Probe C/D is the memo's one genuinely new envelope fact.** The spec's
created-entries sentence LITERALLY admits re-producing a
deleted-then-re-created key (the re-add creates an entry; each created
entry "may be produced"), and by induction admits unbounded iteration
of a loop that keeps re-adding — but gc never exhibits re-production
(800 runs incl. growth), and no bounded machine can admit the unbounded
reading without giving up termination of `allStreamsOk`-style ∀-stream
certification. The model below resolves this to **at-most-once per
key** and records it as a narrowing with a re-envelope obligation
(inventory E9 gets the sub-entry), rather than pretending the literal
reading doesn't exist.

## 2. New corpus rows (landed pre-fix, colors verified)

| row | pre-fix | post-fix (any ruling) | what it adds beyond the three reds |
| --- | --- | --- | --- |
| `maps/delete-unreached-during-range` | **FAIL** (machine 20, go 11) | green, forced | isolates the removal clause: current key KEPT, only the unreached key deleted — delete-during-range deletes everything, so it cannot distinguish "snapshot ignores removal" from "current-key deletion breaks production" |
| `maps/added-entries-bound` | PASS | must STAY green under every stream | the envelope's BOUND, member-invariantly: returns 7 iff the added entry is produced ≤ once, no alien key appears, and the loop terminates within the guard — red if a fix ever over-produces, invents keys, or diverges; green under snapshot, green under any conforming live model |
| `maps/delete-readd-during-range` | PASS | green under the recommended narrowing | the re-created-key axis (probe C as a pin): exact count 3 — goes red if a fix introduces re-production/unbounded iteration; must be REWORKED to a membership row if the user rules for the literal-latitude envelope instead |

Neither green row pins a latitude member: both normalize the member
away and observe only the envelope bound (the doctrine's requirement —
the oracle witnesses members, never width; a strict case may only
assert what is member-invariant).

## 3. The model options

### (S) Snapshot — status quo. REJECTED

Violates two forced points (§0) plus the U1 race blindness; `observed ∉
modeled` on live-mutation shapes is a definitional bug under the
charter (E9 already records it as the envelope's one forced-point
violation). Not compatible with the arc's end-state claim.

### (L) Live-read-per-iterNext with produced-set + stop choice — RECOMMENDED

`Cont.mapIterK` stops carrying the entry snapshot and carries instead:
the map's **base `Loc`** (none for nil map), the **produced key set**
(keys already bound, in production order), and the **start key set**
(keys present when the range began — keys only, not values). The
pick-next step becomes:

1. **Load the map cell** at base (a real heap read, every iterNext
   including the final done-check — this is the footprint arm).
2. `candidates` = current entries whose key ∉ produced. (Removed
   entries drop out by absence — the forced clause. Values come from
   the live entry — the forced table clause.)
3. `mandatory` = candidates whose key ∈ startKeys.
4. If `candidates = ∅`: done (`.next k`).
5. Otherwise consume ONE choice of width `candidates.size + (if
   mandatory = ∅ then 1 else 0)`: an index picks that candidate
   (bind its key + live value via the existing `bindIterVars`,
   push key into produced); the extra slot — legal only when nothing
   mandatory remains — is **stop** (added-but-unproduced entries
   skipped, iteration ends).

**The envelope this realizes, argued against the spec text (the
site-local upper-bound statement the implementation must carry):**
- Order: any permutation interleaving — unchanged maximality from E9.
- Removal: forced clause exact (absent at pick time ⇒ never a
  candidate). Note the asymmetry the spec fixes: removal is checked
  LIVE (an entry deleted then re-created is a candidate again — its
  re-creation created an entry that may be produced), production is
  keyed (see narrowing 1).
- Values: live at production — forced clause exact.
- Created entries: any SUBSET of created entries produced, each at any
  interleaved position — pick freely includes them; skip is realized by
  never picking before stop. Per-entry, per-occurrence independence:
  exhibited (probe A's full distribution is inside; every member of the
  per-entry powerset is reachable by pick order + stop placement).
- **Narrowing 1 (recorded, re-envelope obligation):** a key already
  produced is never produced again, even if its entry is deleted and
  re-created — the literal spec text admits re-production; gc never
  exhibits it (probes C/D); the produced-KEY-set model excludes it.
  Bounded-termination is what the narrowing buys: without it the
  envelope admits infinite traces for self-re-adding loops and
  `allStreamsOk` certification dies.
- **Narrowing 2 (recorded):** an unreached start key deleted and
  re-created is treated as mandatory (startKeys ∩ candidates), i.e.
  always eventually produced — the literal text would allow skipping
  the re-created entry. Contains gc (re-created unreached keys are
  produced in every probe shape). Cheap to lift later (move such keys
  out of startKeys on first observed absence) but that requires
  observing absence, i.e. bookkeeping per pick; not worth it before a
  program demands the member.
- **Consequence honestly stated:** for a body that keeps CREATING fresh
  keys, the envelope admits arbitrarily long (fuel-bounded) iterations
  — produce-all members chase the additions. That is faithful: gc's own
  iterator can be strung along by insertions for a long-but-bounded
  walk, and the spec gives no bound at all. Under the strict lane the
  canonical member (below) makes such programs fuel-out visibly rather
  than silently normalize.

**Canonical (empty-stream) member:** index 0 = first candidate in cell
order, stop slot LAST — so a mutation-free range degenerates to exactly
today's first-remaining-in-insertion-order pick sequence: **zero
baseline movement outside the predicted flips**, and the strict lane
keeps producing created entries (gc's modal member, probe A: produce-all
was 198/400). This is a deterministic gc-pin of the latitude in the
register's sense — velocity scaffolding, recorded, never fidelity.

**Granularity ledger (the decision IS the design — BUG-002's class):**
the per-iterNext load is ONE cell read (the whole `mapData` cell — our
heap is cell-granular, so this is the same granularity as `mapGet`
today) in the same machine step that consumes the pick. gc's
`mapIterNext` is likewise one instrumented read per advance (the U1
probe's TSan report names it). No multi-cell loop, no new coarse spot;
the ledger gains no entry, and the R4 re-audit of apply steps picks it
up with every other arm. What DOES change is interleaving-visible and
is the point: a concurrent `mapAssign`/`mapDelete` between two picks is
now separated from a real read by the footprint table, where the
snapshot made all iterations read-free.

**Race-detector integration (the S3 fourth symptom):** one new
footprint arm — the iterNext load records `(read, base)` exactly like
`mapAccess` does for `mapGet` (Race.lean:145-146's class), on EVERY
pick step INCLUDING the final done-check (gc's exhausted `mapIterNext`
call still reads — the entry-snapshot read alone is what U1 records
today). This closes U1: `race/negative/map-range-iter` flips because
the main goroutine's `m[3] = 3` write now collides with a recorded
iterator read. The U1 inventory row is deleted in the same movement,
per its own text ("the footprint arm falls out of BUG-005's
live-iteration surgery").

**Mirror/Sym Q3 (obligation NOT widened):** the mirror quits Q3 at
every nonempty `mapIterK` today (Mirror.lean:2143-2147) — the pick stays
the sole consumption site (stop is one more slot of the SAME
consumption, not a new site), so Q3's class is unchanged and no new
QuitSite constructor is needed. One transcription decision to make at
implementation: the empty-map fast path currently COMPUTES
(`remaining.isEmpty → .ok (.next k', s)`); under (L), doneness needs
the load, so the mirror arm either transcribes the load and computes
when the candidate check is concrete, or quits conservatively on all
`mapIterK`. Recommend the former (keeps currently-computing empty-range
windows computing); either way the drift theorem forces arm fidelity
and a quit asserts nothing — the mirror's soundness obligations do not
widen. (MatMul's windows already quit Q3 at map picks by design —
wp-arc log s4 — and are unaffected.)

**Proof blast radius (the honest list, from this tree's cites):**
- `GoLean/GoCore/StepFn.lean`: `mapRangeK` arm (429-430: store base +
  startKeys instead of snapshot; keep failing closed on a non-map) and
  every `mapIterK` arm (595-609 pick; 630, 640-641, 651, 700, 718-720
  break/continue/return/panic/label plumbing — field changes only).
- `GoLean/GoCore/Machine.lean`: `mapRangeSnapshotEntries` (873-921)
  retires into a live-cell read helper; relation rules
  `mapRangeSnapshot`/`mapIterDone`/`mapIterNext` (2686-2702) reshaped
  to the load + candidates form (Continue/Break/Return rules mechanical).
- `GoLean/GoCore/MachineSound.lean`: the `mapIterK` soundness and
  completeness cases (644, 722) replayed — the COUPLING note's exact
  demand: **re-run `step_complete_any_wf`'s mapIterNext case**, whose
  per-pick `bindIterVars` ok-ness must be choices-independent; under
  (L) that independence comes from the live cell's normalization
  invariant (`mapAssign` only stores normalized entries) instead of the
  snapshot's self-normalization check. The **∀-streams checker**
  (`allStreamsOk`, 2531-2551) is the largest single item: its mapIterK
  branch bound moves from the CONFIGURATION (snapshot size) to the
  STATE (live cell size + stop slot); the checker already walks
  configs with states, but the bound derivation and
  `execStmtLoop_ok_of_allStreamsOk` re-prove.
- `GoLean/GoCore/StateWf.lean` + `MultiWfSound.lean` + `Multi.lean:1586`:
  `Cont.itersNormalized` (477+) — the wf component moves from
  "snapshot entries self-normalized" to "base loc types as a map cell"
  (the cell's entry normalization is already a heap invariant);
  MultiWfSound's transport lemmas (64-90) re-proved.
- `proofs/GoLeanProofs/Sym/MultiStreams.lean`: `isMapIterPos` (56-61)
  and the obliviousness exclusion (106-110) re-argued: the load itself
  consumes no choices, pick ok-ness stays stream-independent — E9's
  "replay the stream-obliviousness analysis" clause.
- `proofs/GoLeanProofs/Sym/Mirror.lean`: mapRangeK (2084) and the
  mapIterK arms (2143, 2162, 2172 + break/return) re-transcribed.
- `GoLean/GoCore/Race.lean`: the new footprint arm; U1 row retired;
  the inventory table's mapRange rows updated.
- Latitude inventory E9: RE-ENVELOPE recorded as done, the
  created-entries envelope statement moves to the site, narrowings 1-2
  recorded with obligations; the doctrine's requirement-1 site list
  updated. This is the biggest semantic-core change since the spine
  migrations — MODERATE per E9's own estimate, and it is the reason
  slice 4 is gated.

**Differential story (what the oracle can and cannot pin):** the three
reds flip DETERMINISTICALLY — each was built symmetric so every
envelope member agrees: delete-during-range → n=1,len=0 → 10 = go;
clear-during-range → 10; update-during-range → 109 (both entries equal
before and after update, so order is irrelevant); the new
delete-unreached → 11. `race/negative/map-range-iter` flips with the
footprint arm. The added-entries width is NOT oracle-pinnable (go run
witnesses members — probe A shows five of them — never the envelope),
so no strict case asserts a member: the two green rows are
member-invariant bounds, and any future member pin belongs to the
membership lane. That is the over-fitting guard: acceptance is the
five deterministic flips, never an iteration-order or member-count
assertion on a mutating shape.

### (H2) The literal-latitude envelope (re-production admitted) — REJECTED as the shipped model, recorded as the wider reading

Track created-entry IDENTITY (not keys) and let every creation be
independently producible: faithful to the sentence's letter, but (i)
admits unbounded traces for any delete-re-add loop, killing ∀-stream
certification and fuel-bounded differential runs on programs gc
completes instantly (probe C), (ii) requires per-entry identity the
heap doesn't carry (entries are key-value pairs in one cell — this is
BUG-004's allocation-identity problem again in miniature), and (iii)
adds no gc-observable member (probes C/D: 800 runs, zero
re-productions). If ARCH/XIMPL evidence ever shows a conforming
implementation re-producing, narrowing 1's obligation triggers and the
produced-set becomes per-incarnation — the mechanism localizes to the
candidate filter, so the lift is contained.

### (H3) Live domain = start keys only (skip all created entries) — REJECTED on the probes

One line simpler than (L) (no startKeys/stop bookkeeping: candidates =
snapshot keys still present, values live). But probe A kills it:
gc PRODUCES created entries (n>4 in 347/400 runs), so "never produced"
excludes the oracle's own realized members — `observed ∉ modeled`, a
definitional bug by the charter, in the very axis the fix exists to
repair. Named here because it is the tempting "small fix" and must not
be reached for.

## 4. DECISION BLOCK

**Options:** (S) snapshot status quo — rejected (two forced-point
violations + U1); **(L) live-read-per-iterNext, produced-key-set,
stop-choice — recommended**; (H2) literal re-production envelope —
rejected (unbounded traces, no observed member); (H3) live-but-skip-all-
created — rejected (excludes observed gc members).

**Recommendation: (L).** It makes every forced clause exact, realizes
the created-entries latitude as a genuine choice at the existing Q3
pick site (width `candidates + stop`), closes U1 with one footprint
arm, keeps the canonical member byte-compatible with today's strict
lane on mutation-free ranges, and pays for termination with two
recorded narrowings (no re-production per key; re-created start keys
mandatory) — both gc-contained by 800-run probes, both carrying
explicit re-envelope obligations at E9.

**Questions for Mike to rule on:**
1. Approve the (L) surgery? It is the arc's largest semantic-core
   change: `Cont.mapIterK` reshape, relation rules, `allStreamsOk`,
   wf-component migration, mirror re-transcription, one race footprint
   arm (§3's blast-radius list).
2. Approve the added-entries ENVELOPE as stated — full per-entry
   produce-or-skip via pick + stop, WITH narrowings 1 (at-most-once per
   key) and 2 (re-created start keys mandatory) recorded at E9 as
   pinned narrowings with re-envelope obligations? (The alternative is
   H2's literal reading; §3 argues it buys unbounded traces for zero
   observed members.)
3. Approve the canonical empty-stream member (first-candidate in cell
   order, stop last — i.e. produce-all): mutation-free ranges keep
   today's exact pick sequence, adversarial self-feeding loops fuel-out
   visibly. (Alternative: stop-first canonical terminates such loops
   early but changes no shipped case either way.)

**On each answer:**
- **Yes to all:** implement (L); flips, all predicted:
  `maps/delete-during-range`, `maps/clear-during-range`,
  `maps/update-during-range`, `maps/delete-unreached-during-range`
  red→green (deterministic), `race/negative/map-range-iter` red→green
  (footprint arm); `maps/added-entries-bound` and
  `maps/delete-readd-during-range` must NOT move; re-pin same-commit;
  BUGS.md BUG-005 → fixed; E9 re-envelope + narrowings recorded;
  U1 retired; the doctrine's requirement-1 site statement updated.
- **No to 1 (defer the surgery):** BUG-005 stays the charter's
  legitimate gated end state (DONE clause 4): memo + gate outcome
  recorded, five reds stay pinned, E9's forced-point violation stays
  flagged, and the fix hands to a named successor arc (it interlocks
  with the re-envelope ladder's priority list, where E9 is priority 2).
- **No to 2 (want the literal envelope):** rework
  `maps/delete-readd-during-range` into a membership-lane row first
  (its exact-count pin encodes narrowing 1), then implement H2's
  identity-tracking variant — expect the ∀-streams checker to fail
  closed on self-re-adding loops and say so in the claim.
- **No to 3:** flip the stop slot to index 0; no shipped case moves;
  record the canonical-member choice either way at the site.

## 5. USER RULING (2026-08-19, Mike — recorded before implementation)

- **Q1: YES** — the (L) surgery.
- **Q2: NO — the narrowings are NOT allowed.** Mike: "any latitude in
  the Go spec should be supported" — implement the **FULL literal
  envelope**. Consequences explicitly ruled in:
  - **a deleted key is removed from the produced-set** — a re-created
    key is an ORDINARY created entry (may be produced, may be
    skipped; and having been removed from produced, it may be
    produced AGAIN). Narrowing 1 is dead.
  - **surviving never-removed start keys remain MANDATORY** — that
    clause is spec-forced ("will not be produced" applies only to
    removed entries; an entry neither removed nor created must be
    traversed), not a narrowing. A start key that was DELETED loses
    its mandatory status forever; its re-creation is an ordinary
    created entry. Narrowing 2 is dead (the mandatory set is pruned
    by deletion, not held).
  - **self-inserting loops have genuinely unbounded traces** — the
    ∀-streams/confluence checker FAILS CLOSED on them; such cases
    ride the membership lane instead, and the claim says so.
  - **cases exercising created-entry latitude move to membership
    rows, not equality rows** (the §2 rework clause fires:
    `maps/delete-readd-during-range` and `maps/added-entries-bound`
    are reworked FIRST, guardrails-first).
- **Q3: YES, with a strengthening** — the canonical/deterministic
  member is **DEFINED as the nondeterministic machine at the zero
  choice stream** (`[0,0,…]`; stop ordered LAST at every pick), so
  deterministic runs are members BY CONSTRUCTION, not by lemma. Make
  it definitional in the code/docs. Corollary to state plainly in the
  record: on self-inserting loops the zero stream is an infinite
  trace and the executable interpreter fuel-outs VISIBLY — correct
  behavior, not a bug.
- **Interpretive reading to the ledger:** "a deleted-then-recreated
  key is a NEW entry (created-during-iteration latitude), not the old
  entry resurrected" — filed as a spec-ambiguity ledger entry quoting
  the spec sentences, our reading, the rejected alternative.
- **Follow-on recorded as a kit obligation (NOT proven this slice):**
  a tiny syntactic termination theorem — "body stores no key into the
  ranged map ⇒ range terminates" — most programs terminate
  structurally since surviving start keys are forced.
- **New doc directed:** `docs/spec-interpretations.md` — the curated
  index of adopted spec readings, one row per reading, each backed by
  a ledger entry, linked concisely from CLAUDE.md.
