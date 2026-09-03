# Q-row rulings — the refreshed sheet (2026-08-31)

Supersedes the RULING SHEET section of
`docs/2026-08-21_w32-qrow-memos.md` (the per-row memos there remain
the arguments of record; this sheet corrects the STALE VEHICLES and
records the rulings). Currency notes come from the fidelity
assessment (docs/assessment/ on this branch, esp. p2-keeps-a1.md
A1-14 and p2-fact-verification.md claim 7).

PROVENANCE: rows 1, 4, 5, 6, 7, 8 are [USER]-RULED 2026-08-31 per
the recommendations below — Mike: "for the killable ones that are
strict improvements, let's do them (either in the current round or
immediately after)" — given against the coordinator's row-by-row
currency table whose recommendations this sheet preserves
unchanged (only vehicles/notes refreshed; the table itself is
reconstructed in the appendix below — it was presented in-session
and not otherwise tracked, auditor D3-2). Row 3 (Q-SELSEL) is
[USER]-RULED 2026-09-01 — option (A) with an implementation slot,
per the tracked two-item menu in the appendix ("(1) agree"; menu
recorded post-hoc at the audit's C5, countersign requested at the
merge ask). Row 2 (Q-ATOMIC) is [USER]-RULED 2026-09-02 — option A′
with THIS repo (the semantics product) as owner, plus BUG-080's
detector-kind slice pulled forward — per the owner proposal
`docs/2026-09-01_qatomic-owner-proposal.md` (Mike: "I agree with this
approach"; the approach as presented is recorded verbatim in the
appendix; the quote was received by the [AGENT] coordinator
in-session and RELAYED to the recording worker — citation, not
firsthand, per the U0-incident convention). Rows 1–8 are ruled (reds
total 20). Row 9 (Q-U4RESIDUAL, 0 reds — a detector-alignment
question), posed 2026-09-02 by the bug080-atomic-kind audit fix round
(G2 F10), was RULED [USER] the same day — option (A), implemented on
the `q-u4-gomem` lane (see the row and the appendix record); the two
[AGENT] readings inside the implementation (per-gc-word keying, the
union rule) were COUNTERSIGNED [USER] 2026-09-03 at the round-5 merge
sign-off («sounds good merge it», relayed — see the appendix).

| # | row (reds) | status | ruling / state |
|---|---|---|---|
| 1 | **Q-INITSPAWN** (1) | **RULED [USER] 2026-08-31** | Envelope ruled as recommended: init-spawned children are ordinary goroutines from the spawn boundary (L1, zero new sites; during-init execution probed 40/40 — deferred-release models foreclosed). VEHICLE REFRESH: the memo's "rider on slice 3(a)" is dead (that W3.2 slice never ran; arc parked) — implementation is a standalone `$pkginit` item on this product's backlog (re-homed per fidelity decision 6), sequenced with the next init-phase surgery. Ruling binds any future implementer now. |
| 2 | **Q-ATOMIC** (5) | **RULED [USER] 2026-09-02 — option A′, owner = THIS repo (the semantics product); BUG-080's detector-kind slice PULLED FORWARD** ("I agree with this approach" to the approach presented — recorded verbatim in the appendix below; quote relayed to the recording worker by the [AGENT] coordinator, citation not firsthand) | The atomics arc is RATIFIED as scoped in `docs/2026-09-01_qatomic-owner-proposal.md` §4/§6 (A′): mem#atomic as a forced SC point stands; fused single-step registry ops, zero new choice sites, TSan-realized detector edges; integer core → `mp-litmus` → `atomic.Value`; spin-wait rows carried under `nonterm=` membership accounting with NO termination claim. OWNER: this repo's backlog — a named worktree lane ("atomics arc") dispatched from TODO.md, sequenced into Tier 5 with the proposal §5 ordering constraints carried (after the gotest fix slice and the t4-detector merge; after the frontend-touching Q-row items; ~3–5 sessions, L). PULLED FORWARD as its OWN S–M slice, sequenced BEFORE the arc rather than riding its detector wave (supersedes the [AGENT] sequencing judgment of audit fix S4): BUG-080's fix — the atomic access KIND in `Race.lean` (`RaceAccess := Kind × Loc`; atomic↔atomic non-conflicting, atomic↔plain conflicting; recorded at the sync cell's path from `raceUpdate`'s sync arm), with the two named costs CHECKED IN THAT SLICE: (i) one `syncData` cell per primitive vs the `locPrefix` over-refusal (the `disjoint-field-vs-lock` control must stay green) and the `wgSemaAccess` plain-pair carve-out; (ii) gc's per-primitive instrumentation differences (WaitGroup under `race.Disable` + the `wg.sema` pair vs Mutex's state CAS), so the per-op recorded set is derived primitive by primitive from `-race`'s realized set. OUT OF SCOPE: FairStream / the `Fair`-quantified claim class — reasoning-side FUTURE WORK TO BE BUILT, NOT part of the arc (proposal §2; the fairness doctrine ruled the same sitting is the doctrine's "Scheduling and fairness" paragraph). Q-TRYLOCK rides as a wave-1 rider per its pre-ruled envelope (row 5). Refreshes (a)/(b) below are discharged by the proposal. SLICE LANDED 2026-09-02 on branch `bug080-atomic-kind` (merge pending audit + sign-off; BUGS.md BUG-080 carries the fix record and two residuals — the sketch's three kinds became four, atomic READS being non-conflicting with plain reads). SUPERSEDED PRE-RULING STATE: mem#atomic as a forced SC point stands; the atomics-arc design memo is still the recommendation. TWO REFRESHES before ruling: (a) "FairStream tier bundled" must read as future work TO BE BUILT (FairStream has never been a Lean definition — assessment finding); (b) the arc has NO live owner post-split — ratifying requires naming one. Decision shape: ratify-with-owner / ratify-with-FairStream-split (A′) / defer the family (Q-TRYLOCK's implementation and the liveness story inherit the wait). |
| 3 | **Q-SELSEL** (2) | **RULED [USER] 2026-09-01 — option (A) with an implementation slot** ("(1) agree" to the tracked two-item menu — recorded VERBATIM in the appendix below; menu recorded post-hoc from the session at the audit's C5, [USER] countersign requested at the merge ask; prereq discharged same day): the asymmetric-arrival envelope adopted — its structure is leg (1) of the refreshed C7 argument; the falsified commit-by-waking-event wording is NOT part of the adopted envelope (the owed wording correction lands at implementation); the idiom is ordinary Go, not raft-specific, so the slot lives on this product's backlog despite the original consumer being parked | SUPERSEDED PRE-RULING STATE: Do not rule as written: the scheduling driver ("before the raft node layer") is parked with the reasoning product, and the envelope rides C7's pairing argument whose re-argue trigger ALREADY FIRED (B1/B2 changed the wake machinery; the promised re-argument was never recorded — p2-keeps-a1 A1-14), with an unprobed corner (two clauses on one channel, woken by close). PREREQ (S): refresh C7's argument + run the close-wake probe; then re-present. **RE-PRESENTATION (2026-09-01 [AGENT], C7-refresh lane):** both prerequisites ran. (i) The close-wake probe (`docs/evidence/2026-09-01_c7-close-wake-probe/`): gc commits EITHER same-channel clause from one close wake (~half each over 800 runs incl. a park-first isolate), falsifying the old "committed by the EVENT that wakes it" wording — but observed ∈ modeled HOLDS (machine-certified {1,2} ⊇ gc's {1,2}; the second member rides the always-realizable close-before-entry schedule + entry L2 draw). The envelope does NOT need widening. (ii) C7's argument is re-recorded post-B1/B2 as two legs (inventory C7 + §8 e12): partner wakes = L4 clause-INDIVIDUAL pairing at the arrival intercept; close wakes = the entry-path mask. Consequence for this row: recommendation (A)'s envelope survives UNCHANGED — its structure (each matching parked clause a distinct L4 candidate, memo option (B)'s own decomposition) is exactly leg (1) and never leaned on the falsified wording; one wording correction owed at implementation: the memo's "C7's commit-by-waking-event argument extended verbatim" must read "the parked side's matched clause is the L4 candidate's clause". The close corner is irrelevant to select↔select rendezvous (closes never pair). Remaining for the [USER]: the vehicle — (A)'s implementation slot post-split (the raft node-layer driver is parked with the reasoning product; the 2 reds stand in this repo's baseline either way) — i.e. rule (A)-with-a-slot or (C) defer-with-dependency-recorded. |
| 4 | **Q-RACEPATH** (1) | **RULED [USER] 2026-08-31 — IMPLEMENTED 2026-09-02 [AGENT]** (Tier-4 detector-soundness lane) | Constant-index narrowing (S) as recommended: extend the shipped fieldGet-chain narrowing to evaluated-index indexGet frames; dynamic-index residual stays in O1 with its trigger. VEHICLE REFRESH: "next footprint-touching slice" = the Tier-4 detector-soundness leg (the natural co-located work). IMPLEMENTATION RECORD: `projChainTarget` (Race.lean) — the narrowing fires for `indexGet` frames whose pending index is an `intLit` AND whose base cell is an ARRAY (slice/string headers stay whole-cell), composing with `fieldGet` in either order; `race/free/array-read-write` flipped FAIL→PASS (confluent), +2 chain-form green guards, +2 must-stay-racy racy-lane guards, +1 born-FAIL residual pin (`race/free/array-dyn-index-read-write`, on BUG-041's Cases line). Ruling text carried to inventory C10/O1, ledger §6, BUG-041. |
| 5 | **Q-TRYLOCK** (1) | **RULED [USER] 2026-08-31 via the killable-set approval; per-row CONFIRMED [USER] 2026-09-01 ("the 4 confirmations all seem like reasonable interpretations… agree on all of the above")** (auditor D3-2 resolved) | Deferred WITH the envelope pre-ruled, as recommended: when modeled, TryLock takes mem#locks' spurious-failure member as a real width-2 choice site (success-edge-only detector; the fairness-claim class); the always-succeeds pin is off the menu permanently. Implementation inherits Q-ATOMIC's arc decision. **IMPLEMENTATION RULED [USER] 2026-09-03: own slice adding the `tryLock` site (the A′ zero-new-sites sentence is amended by this ruling for TryLock only)** — resolves `docs/2026-09-03_atomics-w1-design.md` §6 item 1; quote relayed by the [AGENT] coordinator, see the 2026-09-03 ruling record in the appendix. |
| 6 | **Q-SYNCVAL** (5) | **RULED [USER] 2026-08-31 — implement** | Identity principle ratified (indirection consumes the same C8 site or refuses — never variant semantics) and P-S2-6 green-lit (real stub bodies over EXISTING sync machine ops; frontend-only; flips all 5 reds). D-002 FREEZE INTERACTION — [AGENT] interpretation, CONFIRMED [USER] 2026-09-01 ("the 4 confirmations all seem like reasonable interpretations… agree on all of the above"): this lift is NOT shim injection — it adds no hand-modeled stdlib semantics; it plumbs values to already-modeled machine ops, and the identity principle is precisely the anti-variant-semantics rule the freeze exists to enforce. Any deviation from that shape during implementation is a STOP-and-ask. |
| 7 | **Q-SYNCLIT** (2) | **RULED [USER] 2026-08-31 — implement** | The S lowering as recommended (spec forces empty-literal-only cross-package ≡ zero value ≡ var/new; copy question already answered by sync design §3/p10) — rider on the Q-SYNCVAL slice. |
| 8 | **Q-COND** (3) | **RULED [USER] 2026-08-31 via the killable-set approval; per-row CONFIRMED [USER] 2026-09-01 ("the 4 confirmations all seem like reasonable interpretations… agree on all of the above")** (auditor D3-2 resolved) | Deferred WITH the envelope pre-ruled from the docs text, as recommended: NO spurious wakeups (documented upper bound), Signal = any-waiter, Broadcast = forced-all folding into C8, TSan-realized HB, copy = detected panic. Zero demand; pure frontier. |
| 9 | **Q-U4RESIDUAL** (0 reds; detector alignment) | **RULED [USER] 2026-09-02 — option (A): the race detector follows go_mem exactly** (posed 2026-09-02 [AGENT], the bug080-atomic-kind audit fix round G2 F10; ruled the same day — verbatim quotes in the appendix record below, RELAYED to the recording worker by the [AGENT] coordinator, citation not firsthand; IMPLEMENTED 2026-09-02 [AGENT] on lane `q-u4-gomem`: `Race.lean` `syncEntryKinds`/`syncReleaseTailKinds` record TSan's realized set ∪ go_mem's operation kind, each at its gc WORD (`syncWord`) — RLock/Lock → `.atomicRead @readerCount`, RUnlock/Unlock → `.atomicWrite @readerCount` (each keeping its realized `.read @w`), WaitGroup Add/Done → `.atomicWrite @state`, Wait → `.atomicRead @state` (the realized `wg.sema` pair kept at its own word), Mutex Lock's CAS `.atomicWrite` stays and Mutex Unlock's tail stays — THE UNION RULE (TSan's realized set ∪ go_mem's kind) IS AN [AGENT] READING of "follow go_mem exactly", flagged at audit fix F3 for [USER] countersign — COUNTERSIGNED [USER] 2026-09-03 at the round-5 merge sign-off («sounds good merge it», given to the coordinator's consolidated merge-ask that presented both [AGENT] readings — per-gc-WORD keying and the UNION rule with its lone-copy-beside-`sync.Mutex.Lock` consequence; the quote was received by the [AGENT] coordinator in-session and RELAYED to the recording worker, not firsthand — citation, never bare assertion, the U0-incident convention) — literal reading, for the record: literal go_mem makes every mutex lock read-like, `sync.Mutex.Lock` included, and would RUN a lone copy beside it where gc's `-race` build REFUSES (the CAS on `m.state` is a TSan Write — measured `probes/u4gomem/mu-copy-vs-lock-only` gc RACE 20/20 at GOMAXPROCS 1 and 8, machine RACE, agree-race); the [AGENT] kept the realized atomicWrite (mem#model: a CAS "is both read-like and write-like") so no HOLE cell opens against the oracle — consequence: a lone copy beside `sync.Mutex.Lock` refuses while one beside `sync.RWMutex.Lock`/`RLock` runs (its RMW is under `race.Disable`, only the read-like lock kind applies); the over-refusal rows appear classified BY DESIGN — born-FAIL corpus pins `race/gomem-only/*` on BUG-084's Cases line, probe cells `over-refusal` in `docs/evidence/2026-09-02_q-u4-gomem/` (six u4kind subjects move, the four WaitGroup ones AND `rw-copy-vs-{rlock,lock}`; audit fix F1: the slice's sixth gomem-only corpus row `wg-overwrite-vs-add-nonzero` was NOT TSan-green — gc red when the racing overwrite lands first (the reset counter makes the Add the counter-off-0 case; 20/20 in the sampler) yet green when the Add lands first (the full gate's sample) — gc-schedule-dependent, machine RACE-ALL, pinnable in no lane: deleted from the corpus, probe only (`u4gomem/wg-overwrite-vs-add-nonzero`), whose shapes pair the lock with its unlock unordered with the copy and refuse THROUGH the write-like unlock; the row's "a copy beside RLock/Lock is NOT a race" holds for the lock OP — isolated by `probes/u4gomem/rw-copy-vs-{rlock,lock}-only` and the born-PASS guards `race/free-sync/rw-copy-beside-{rlock,lock}`); BUG-080 residual (a) CLOSED by this ruling). RATIONALE, as ruled: the machine is the substrate for a verification tool — refusal-freedom is the proof obligation (the DRF-guarantee shape: a program proved refusal-free on every path is go_mem-DRF, hence SC), so over-refusal costs COMPLETENESS (correct programs that are racy-by-go_mem-but-TSan-green cannot be verified — vet's `copylocks` flags every such shape) and never SOUNDNESS, while under-refusal (running a go_mem-racy program to a value) would be unsound. go_mem's racy semantics is BOUNDED, not C-style UB (mem#restrictions: report-and-terminate always permitted; else word-sized racy reads observe an actually-written value, multiword values may tear, no out-of-thin-air) — the machine's refusal is the permitted report-and-terminate branch; the bounded-VALUE branch stays deliberately unmodeled (register #4's existing scoping, now explicitly recorded with this ruling at register #13). | THE QUESTION (as posed): for the sync ops gc's `-race` build performs under `race.Disable` — RWMutex `RUnlock`/`Unlock`'s counter RMWs, WaitGroup `Add`/`Done`'s state RMW, `Wait`'s counter read — should the detector record the go_mem-faithful access kinds (making a plain access beside them a REFUSAL) or stay aligned with TSan's realized set (record nothing; RUN them)? The BUG-080 slice chose alignment ([AGENT], residual (a), inside a brief that said "no new over-refusal rows"). THE RESIDUAL PRECISELY (G2 F10 corrected the first statement): a plain access beside a WRITE-LIKE op (`RUnlock`, RWMutex `Unlock`, WaitGroup `Add`/`Done`) or a plain OVERWRITE beside `Wait` at counter 0. NOT the residual: a plain COPY beside `RLock`/`Lock` — mem#model lists mutex lock as read-like and a copy is read-like, so no write-like operand and no race; `rw-copy-vs-{rlock,lock}` agree-DRF is the correct verdict. THE AUDITOR'S PROPOSED TABLE: `RLock`/`Lock` → `atomicRead`; `RUnlock`/`Unlock` → `atomicWrite`; WaitGroup `Add`/`Done` → + `atomicWrite` (beside the realized `wg.sema` pair); `Wait` → + `atomicRead`; both RWMutex halves move together (each RWMutex op keeps its realized plain `race.Read(&rw.w)` and adds its counter RMW's go_mem kind). FOR: the register of record is go_mem, not TSan — by mem#model's read-write/write-write definitions a plain write beside `RUnlock` IS a data race, and a racy program has no defined value semantics, so running it to a value is a fail-OPEN cell against the doctrine's own upper bound; no race-free program's verdict moves (vet's `copylocks` flags every shape); the table derives from mem#model's read-like/write-like lists without per-primitive source archaeology. AGAINST: the racy lane's oracle is `-race` (register #13) — each refusal is a NEW over-refusal row (machine RACE, gc DRF-in-N: the three-way rule's investigation cell) on `wg-copy-vs-done`, `wg-overwrite-vs-done`, `wg-overwrite-vs-wait-at-0` (+ a copy beside `RUnlock`/`Unlock`, UNPROBED — the family has no such subject); the differential's lower bound (observed ∈ modeled) is untouched either way (misuse-only), so this is a DOCTRINE question — which register wins where go_mem and TSan disagree — not an evidence question; and recording more than gc realizes departs from the primitive-by-primitive derivation-from-source discipline the slice's check (ii) was ruled on. AUDITOR'S RECOMMENDATION: rule first, then take the table in ITS OWN S slice (`syncEntryKinds`/`syncReleaseTailKinds` + the u4kind family's expected cells + BUGS.md/doctrine text + probes for the unprobed copy-beside-RUnlock/Unlock shapes), never inside the BUG-080 slice, whose correctness the audit confirmed under its brief. DECISION SHAPE: (A) adopt the table — go_mem register wins, the over-refusal rows appear classified BY DESIGN; (B) keep alignment — TSan register wins, residual (a) becomes a recorded [USER] doctrine decision rather than an [AGENT] choice; (C) split — adopt only the write-like halves (`RUnlock`/`Unlock`/`Add`/`Done` → `atomicWrite`, `Wait` → `atomicRead`), the minimal set that closes the fail-open cell. |

## Execution

- The **Q-SYNCVAL + Q-SYNCLIT slice** (7 reds, frontend-only, S)
  launches IMMEDIATELY AFTER the Tier-1 fixes lane lands — both
  edit `tools/nativefrontend` and re-pin `baselines/native-full.tsv`,
  so sequential beats a merge fight — The [USER] confirmed row 6's D-002 freeze-interaction reading
  2026-09-01 — the slice is UNBLOCKED once Tier 1 lands. Slice contract: identity
  principle enforced (stubs route to existing C8-consuming ops,
  refusal on anything that would need variant semantics),
  differential cases per flipped row, full `ci --diff`, honest
  re-pin (FAIL→PASS flips with the reason).
- Rows 1/4/5/8's rulings are recorded here and bind future work; the
  implementing slices carry them to the inventory/ledger row texts
  when they land (no doc-drift risk meanwhile: this sheet is the
  ruling of record and the memos doc's sheet is superseded by
  pointer — the implementing slice adds the banner there).
- Rows 2/3 return to the [USER] when: (2) an owner proposal exists
  (post Tier-4 scoping), (3) the C7 refresh + close-wake probe are
  done (queued as an S item) — **DONE 2026-09-01 [AGENT] (C7-refresh
  lane): row 3 is ready for ruling; see its RE-PRESENTATION.** **Row 2
  RETURNED via the owner proposal (2026-09-01/02) and RULED [USER]
  2026-09-02 — see the row; its vehicles are the two TODO.md items
  (the BUG-080 detector-kind slice first, then the atomics arc).**
  Row 9 (Q-U4RESIDUAL, added 2026-09-02) RULED [USER] the same day
  (option (A)) — nothing on this sheet awaits the [USER].

## Appendix — the coordinator's row-by-row currency table

[AGENT] reconstruction of the table presented in-session (auditor
D3-2: the rulings above cite this table but it was never tracked;
its substance is the sheet's own status column, restated here as
what was put in front of the user).

| # | row | currency finding | disposition presented |
|---|---|---|---|
| 1 | Q-INITSPAWN | recommendation current; VEHICLE stale (slice 3(a) dead — standalone `$pkginit` backlog item instead) | rule now as recommended |
| 2 | Q-ATOMIC | recommendation needs two refreshes before ruling: FairStream must read as future work TO BE BUILT, and the arc has NO live owner post-split | hold — returns with an owner proposal. RETURNED via `docs/2026-09-01_qatomic-owner-proposal.md`; RULED [USER] 2026-09-02 — A′ with this repo as owner + the BUG-080 detector-kind slice pulled forward (record below) |
| 3 | Q-SELSEL | STALE premise: scheduling driver parked with the reasoning product; C7's re-argue trigger already fired (re-argument never recorded, A1-14); unprobed close-wake corner | hold — C7 refresh + close-wake probe, then re-present. RE-PRESENTED 2026-09-01 via the two-item menu below; ruled "(1) agree" = adopt the recommended (A)-with-a-slot |
| 4 | Q-RACEPATH | recommendation current; vehicle refresh ("next footprint-touching slice" = Tier-4 detector-soundness leg) | rule now as recommended |
| 5 | Q-TRYLOCK | recommendation current; zero-red pre-ruled DEFERRAL (kills no reds; implementation inherits Q-ATOMIC's arc decision) | defer with the envelope pre-ruled |
| 6 | Q-SYNCVAL | recommendation current; KILLABLE — frontend-only, flips all 5 reds | rule + implement |
| 7 | Q-SYNCLIT | recommendation current; KILLABLE — rider on the Q-SYNCVAL slice, flips 2 reds | rule + implement |
| 8 | Q-COND | recommendation current; zero-red pre-ruled DEFERRAL (docs-text envelope; zero demand, pure frontier) | defer with the envelope pre-ruled |

### The row-3 ruling menu (2026-09-01) — the tracked record behind "(1) agree"

[AGENT] menu recorded post-hoc from the session at the audit's C5;
[USER] countersign requested at the merge ask. COUNTERSIGNED [USER]
2026-09-01 at the merge sign-off ("all agreed, go ahead with the
merge") — provenance chain: the quote was received directly by the
[AGENT] coordinator in-session and RELAYED to the recording worker;
the worker did not receive it firsthand (assertion converted to
citation per the U0-incident convention). The coordinator presented two numbered items, verbatim:

«1. Q-SELSEL is ready to rule (2 reds): the asymmetric-arrival
envelope survives unchanged on fresh evidence; the open question is
only the vehicle — (A) adopt now with an implementation slot on this
product's backlog, or (C) defer with the dependency recorded. Given
the semantics-first goal I'd lean (A)-with-a-slot. 2. The gotest
harvest wants a fix slice next (the four bugs + the two suspicious
refusals) — I'll queue it as the next dispatch after this round
lands.»

The user replied «(1) agree, (2) agree». So "(1) agree" = adopt the
recommended (A)-with-a-slot (the row-3 ruling above); "(2) agree" =
the gotest fix slice is the next dispatch after this round lands.

### The row-2 ruling record (2026-09-02) — the tracked record behind "I agree with this approach"

[AGENT] record. Provenance chain: the [USER] quote was received by the
[AGENT] coordinator in-session and RELAYED to the recording worker in
its brief; the worker did not receive it firsthand (citation, never
bare assertion — the U0-incident convention). The approach presented,
as relayed:

«ratify A′ with this repo as owner, sequenced into Tier 5, AND pull
BUG-080's detector fix forward as its own S–M slice (the atomic access
KIND in Race.lean: RaceAccess := Kind × Loc, atomic↔atomic
non-conflicting, atomic↔plain conflicting, recorded at the sync cell's
path; the two named costs to check: single syncData cell per primitive
vs locPrefix over-refusal + wgSemaAccess carve-out; gc's per-primitive
instrumentation differences) rather than waiting 3–5 sessions.
FairStream/fairness = reasoning-side future work, NOT part of the arc.»

The user replied «I agree with this approach». The same sitting
produced the fairness doctrine ruling (verbatim in the doctrine's
"Scheduling and fairness" paragraph,
`docs/2026-08-11_essence-of-go-doctrine.md`), which is why FairStream's
exclusion from the arc is a doctrine consequence, not merely a scoping
choice.

### The row-9 ruling record (2026-09-02) — the tracked record behind option (A)

[AGENT] record. Provenance chain: the [USER] quotes below were
received by the [AGENT] coordinator in-session and RELAYED to the
recording worker (the `q-u4-gomem` lane) in its brief; the worker did
not receive them firsthand (citation, never bare assertion — the
U0-incident convention). The question presented was the row's
decision shape (A)/(B)/(C) with the auditor's table. The user ruled,
verbatim as relayed:

«Right, we want to follow go_mem exactly I think. It's a weird
situation, but maybe this is analogous to UB in C, where the compiler
can do anything it wants when there are races?»

The coordinator then explained that go_mem gives racy programs a
BOUNDED semantics rather than C-style UB — report-and-terminate is
always permitted (mem#restrictions); otherwise word-sized reads observe
some actually-written value, multiword values may tear, no
out-of-thin-air — so a refusal is a permitted implementation behaviour,
and over-refusal costs completeness, never soundness. The user
replied:

«That's okay if we imagine this as the substrate for a verification
tool right? We're 'failing more' which means we can only verify code
that is correct»

and, closing:

«Indeed. All good with me, go ahead».

So the ruling is option (A) — the go_mem register wins where go_mem
and TSan disagree — with the verification-substrate rationale recorded
in the row: refusal-freedom is the proof obligation (DRF-guarantee
shape); over-refusal = incompleteness, under-refusal = unsoundness.
The C-UB analogy the first quote floated is NOT part of the ruling's
grounds — the second exchange replaces it with go_mem's bounded racy
semantics, and register #13 (`docs/2026-08-11_latitude-inventory.md`)
records that distinction.

#### Countersign of the two [AGENT] readings (2026-09-03)

COUNTERSIGNED [USER] 2026-09-03 at the round-5 merge sign-off.
Provenance chain: the quote was received by the [AGENT] coordinator
in-session and RELAYED to the recording worker (the merge-train
worker) in its brief; the worker did not receive it firsthand
(citation, never bare assertion — the U0-incident convention). The
coordinator's consolidated merge-ask covered both round-5 branches in
order (`bug082-maphint` bd849494 → `q-u4-gomem` c5995134) and
presented the two [AGENT] readings inside this row's implementation
for countersign: (i) per-gc-WORD keying of the sync accesses
(`syncWord`); (ii) the UNION rule — TSan's realized set ∪ go_mem's
operation kind — with its stated consequence that a lone copy beside
`sync.Mutex.Lock` refuses (gc-agreed, `probes/u4gomem/mu-copy-vs-lock-only`
RACE 20/20) while one beside `sync.RWMutex.Lock`/`RLock` runs. The
user replied, verbatim as relayed:

«sounds good merge it»

So both readings stand as [USER]-countersigned; neither was
overruled. The consuming records (`GoLean/GoCore/Race.lean` section
docstring "The sync primitives' OWN state words"; `docs/BUGS.md`
BUG-084) cite this paragraph.

### The 2026-09-03 ruling record — the tracked record behind "(4) Atomics - agree" (TryLock own slice) and the rest of that sitting

[AGENT] record. Provenance chain: the [USER] quote was received by the
[AGENT] coordinator in-session and RELAYED to the recording worker in
its brief (lane `guard-stage-alt`); the worker did not receive it
firsthand (citation, never bare assertion — the U0-incident
convention). The coordinator's "decisions on deck" list, as relayed:
(1) the `coverage-baseline-diff` guard fix for the oracle-schedule-
dependent red (`channels/select-select/beside-loop`), option (a) =
per-row stage alternation; (2) BUG-087's panic-text latitude — ONE
demonic choice at the nil arm so both gc texts are admitted; (3) the
stdlib-boundary gates G1–G9 as `docs/2026-09-03_stdlib-boundary-design.md`
§5 recommends; (4) atomics — TryLock as its own small slice adding the
`tryLock` ChoiceSite (the A′ "zero new sites" sentence amended for
TryLock only), AND the typed-wrapper shadow model CONFIRMED not shim
injection under D-002; (5) the noodler gaps; (6) the strict-lane routing
rule (`docs/2026-09-01_membership-depth.md` §5), the eight scheduling
rows routed in the same slice; others = the periodic legs and the P5
filing (the membership sampling budget, P2, was ruled SEPARATELY the same
day — see below). The user replied, verbatim as relayed:

«Re decisions on deck (1) the guard - agree with the redommendation, do (a); (2) panic-text, agree, demonic choice so both are admitted; (3) agree, go ahead with the plan; (4) Atomics - agree; (5) noodler gaps - already addressed; (6) strict-lane, agree; others: lower priority for now?»

So: (1) (a) adopted — gate change, [USER]-ruled; (2) demonic choice,
both texts admitted (BUG-087 fix shape item (4), separate lane); (3) G1–G9
each as recommended (slice 1 by a separate lane); (4) TryLock own slice
+ D-002 confirmation, recorded on row 5 above and in the atomics memo
§6; (5) already addressed; (6) routing rule ADOPTED, routing slice
pending (separate lane); the "others" are LOWER PRIORITY for now —
periodic legs and P5 filing deferred (record:
`docs/assessment/decisions-2026-08-31.md`, 2026-09-03 addendum).
Membership sampling budget (membership-depth §6 P2): NOT among the
"others" — ruled ADOPTED the same day in a separate exchange, relayed
by the [AGENT] coordinator as «yeah, agree on the sampling budget, go
ahead as you propose» (alternate plain/race, early stop at `members=`,
K=32 `--diff` / K=80 `--slow`; the budget BEFORE this ruling is the
implicit 10 draws; implementing lane `sampling-budget`). An earlier
version of this paragraph said "K=32 stays the default" — false on both
counts (K=32 never was the default; P2 was adopted, not deferred);
corrected at the lane's audit fix round.

### The E9 irreflexive-key ruling record (2026-09-03) — the tracked record behind "(b) … approved"

RATIFIED [USER] 2026-09-03. Question posed by the [AGENT] coordinator
at the `hygiene-b1-stamps` merge-ask (design-hygiene arc slice 1, B1
entry-identity stamps): the stamps narrow E9's envelope on IRREFLEXIVE
keys (NaN, or an aggregate/interface holding one) by construction —
each entry produced exactly once, where the retired key-set frame
admitted any number of productions and an immediate stop — against the
2026-08-19 E9 ruling that rejected narrowings (BUG-088; rows
`maps/nan-key-range`, `maps/nan-key-range-aggregate/{array,struct,
interface}`, gc-matching, fuel-out on main). The user replied,
verbatim as relayed to the recording worker by the coordinator (not
firsthand — citation, never bare assertion): «(b) it sounds like this breaks an old ruling but ends up more accurate to real go - approved». Effect: the
2026-08-19 no-narrowing ruling is SUPERSEDED for irreflexive keys only;
the rest of the E9 envelope stands. Consuming records: latitude
inventory §E9 (IRREFLEXIVE KEYS bullet), `docs/BUGS.md` BUG-088,
`docs/2026-09-03_hygiene-b1-stamps-design.md` §4, the arc plan (i).
