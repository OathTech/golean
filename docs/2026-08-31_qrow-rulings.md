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
| 5 | **Q-TRYLOCK** (1) | **RULED [USER] 2026-08-31 via the killable-set approval; per-row CONFIRMED [USER] 2026-09-01 ("the 4 confirmations all seem like reasonable interpretations… agree on all of the above")** (auditor D3-2 resolved) | Deferred WITH the envelope pre-ruled, as recommended: when modeled, TryLock takes mem#locks' spurious-failure member as a real width-2 choice site (success-edge-only detector; the fairness-claim class); the always-succeeds pin is off the menu permanently. Implementation inherits Q-ATOMIC's arc decision. **IMPLEMENTATION RULED [USER] 2026-09-03: own slice adding the `tryLock` site (the A′ zero-new-sites sentence is amended by this ruling for TryLock only)** — resolves `docs/2026-09-03_atomics-w1-design.md` §6 item 1; quote relayed by the [AGENT] coordinator, see the 2026-09-03 ruling record in the appendix. **IMPLEMENTED 2026-09-03 [AGENT] on lane `q-trylock`** (SHA = the lane's commit; the twin-pin move RULED [USER] 2026-09-03 — its appendix record). IMPLEMENTATION RECORD: `ChoiceSite.tryLock` (State.lean; `consumeAtOne := false` at the time — the flag was deleted by G-U 2026-09-04, the bound-1 no-pop being the uniform rule since; slot 0 = acquire — gc's realized point, so the strict lane's uncontended TryLock matches the oracle — slot 1 = the spurious false; width 2 at an acquirable cell, bound 1 = no pop at a held one: `tryLockWidth`/`tryAcquire`, Machine.lean); `SyncOp.tryLock/tryRLock/tryWLock` (result target ≤ 1) applied by `applyTryLock` — the envelope statement, with the pre-commit discipline for the ∀-streams kit (the acquired cell is stored before the pick applies; the spurious member returns the pre-store state) — through the choice-taking `applySyncOp` over the choices-free `applySyncOpCore` (the `applyStmtOp`/`applyStmtOpCore` mold; `Step.syncStApply` quantifies the stream); DETECTOR (Race.lean `syncEntryKinds` + an `acquired` flag re-derived by `raceUpdate` from the pre/post cells, per gc word from the pinned sources — Mutex TryLock on an unlocked cell → `.atomicWrite @state` on BOTH members (the state CAS at internal/sync/mutex.go:85, realized by TSan whether it wins or loses — the lost CAS IS gc's realization of the spurious false; an [AGENT] reading in the row-9 refusal-permitted direction), on a held cell → NOTHING (the plain early return :77-79, uninstrumented; go_mem: "no synchronizing effect at all" — no kind); RWMutex TryRLock/TryLock → `.read @w` on EVERY outcome (`race.Read(&rw.w)` precedes `race.Disable`, rwmutex.go:89/:171) + `.atomicRead @readerCount` on success only (the go_mem lock kind — "equivalent to a call to l.RLock/l.Lock"); the acquire EDGE on success only — the success-edge-only detector as ruled); FRONTEND: statement discard, hoisted expression node (`{"expr":"sync-op",…}`, admitted where `atomic-op` is), bodied stubs for method values / interface dispatch, the promoted receiver — one `syncValueOpFor` table (identity principle: every spelling reaches the one site or refuses); ROWS: 12 `sync/trylock/*`, +2 racy (`race/negative-sync/{overwrite-vs-trylock,failed-trylock-no-edge}`), +3 DRF (`race/free-sync/{trylock-publish,rw-trylock-publish,rw-tryrlock-acquire}`); the two frontier reds `sync/out-of-scope-trylock/trylock-uncontended` and `sync/promoted-mutex/trylock-expr` FLIPPED FAIL→PASS as MEMBERSHIP rows over {acquired, spurious} (a strict pin is impossible — the width-2 draw fails strict's stream invariance; gc exhibits only the success member, 20/20 at GOMAXPROCS 1 and 8: unexhibited-but-permitted, `docs/evidence/2026-09-03_q-trylock/`); spin rows under `nonterm=`, NO termination claim. The dedup engine / kernel checkers REFUSE a TRY-head apply (fail closed; `consumesTryLock`), the CLI enumerator carries such rows. AUDIT FIX ROUND F1–F6 (2026-09-03, [AGENT]): F1 — `tryAcquire`'s TryRLock arm WIDENED from `!writer ∧ pendingW = 0` to `!writer`: the model's `pendingW` is one flag for a writer queued behind `rw.w` (rwmutex.go:150; gc's TryRLock TRUE there, 40/40) and one past `readerCount.Add(-max)` (:152; gc false) — sync design §8 R1's value-observable half — so the pick is offered whenever no writer HOLDS (machine ⊇ gc; an [AGENT] widening in the safe direction, RATIFIED [USER] 2026-09-03 («TryRLock decision sounds fine», relayed by the [AGENT] coordinator); per-program sets unchanged, {0, 1} at `rw-tryrlock-pending-writer`; the blocking RLock keeps R1); F2 — `defer m.TryLock()` lowered through the deferred wrapper (result discarded), row `sync/trylock/defer-trylock`; F3 — gc-unexhibited members named at the rows; F4 — the detector table's kind-mismatch arms enumerated by name, no absorbing default; F5 — `resultTypes` accepted-but-unchecked on the `sync-op`/`atomic-op` expression nodes recorded as owed (TODO.md); F6 — rebased onto main 221d8964: twin pin re-derived `45cd882a…` → `f2309df2…`, still exactly ONE entry (`sync.Mutex.TryLock`, now methods[518]); `trylock-false-then-lock` routed to the confluent lane per main's new strict-lane depth guard. |
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
both texts admitted (BUG-087 fix shape item (4), separate lane — LANDED as lane `bug087-paniktext` — implementation commit d8fea185 pre-rebase, squashed with its records into dc0ffe0b on rebase onto 221d8964, audit fix round F1–F3 on top — 2026-09-03: `ChoiceSite.nilValueMethodText`, latitude inventory R9a, five membership rows; evidence `docs/evidence/2026-09-03_bug087-paniktext/`); (3) G1–G9
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

### The row-5 twin-pin record (2026-09-03) — the tracked record behind «we should break things»

[AGENT] record. Provenance chain: the [USER] quote was received by the
[AGENT] coordinator in-session and RELAYED to the implementing worker
(lane `q-trylock`) mid-task; the worker did not receive it firsthand
(citation, never bare assertion — the U0-incident convention). The
worker had STOPPED pre-branch on its brief's hard stop ("the twin-wire
pin must not move … if it moves STOP"): the pinned raft twin wire
(`baselines/pins/twin-chdriver.wire.json`) carries `sync.Mutex`'s full
stub method set, whose entry [515] `TryLock` was a declaration-only stub
with the cause string "…the member is outside the modeled sync
surface…" — every truthful implementation moves that entry (a body per
the identity principle, or at least a corrected string), although raft
never calls TryLock/TryRLock (verified: zero hits in `raftsubject/`,
`raftharness/`, `deps/raft`); the only byte-preserving path keeps a
FALSE cause string in the wire. Options presented: (A) a deliberate twin
re-pin whose structural diff is exactly that entry gaining a body; (B)
anything preserving the bytes. The user ruled, verbatim as relayed:

«(c) another case where we should break things rather than preserve
incorrect behavior, right? We should break things»

— option (A) APPROVED, with the instruction to enumerate exactly which
entries change (RWMutex entries too if present; nothing else may).
OUTCOME: the JSON diff of the pinned vs fresh emit shows ONE changed
entry — `methods[515] sync.Mutex.TryLock` (`body` added: the `sync-op
tryLock` node into a declared `$tryOk` + `return`; `unsupported`
removed); the twin's method set has no RWMutex entry; pin
`eef32142627a…` → `c824f9e4d27f…` (both hashes and the diff listing in
`docs/evidence/2026-09-03_q-trylock/twin-pin/`; the history line in
`scripts/check-frontend-pins`).

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

### The reasoning-surface gates ruling record (2026-09-04) — G-U … G-PIN, design gates of the same class as this sheet's rows

[AGENT] record. Provenance chain: the [USER] quote was received by
the [AGENT] coordinator in-session and RELAYED to the recording
worker, so it is cited as relayed, not firsthand (U0-incident
convention: citation, never bare assertion). The coordinator
presented `docs/2026-09-04_reasoning-surface-plan.md` §5.4's nine
design gates — G-U, G-C5, G-C1, G-C2, G-P, G-C3, G-C4, G-OUT, G-PIN,
each carrying a recommendation — for the same reason this sheet
exists: a design gate is a HARD STOP the coordinator does not
self-adjudicate (CLAUDE.md, autonomous arcs), whether it is a Q-row
or a plan §5.4 gate. Mike replied, verbatim as relayed:

«Great, this sounds good - let's move ahead with the plan. Our top
level goal here is (1) to be a highly accurate go semantics, and (2)
to support reasoning about go using an iris-lean layer (which we
won't build, that's a customer)»

— read as: all nine gates RULED as recommended, plus the two
top-level goals stated (now carried in `CLAUDE.md` "What this repo
is"). Earlier the same day, in a separate exchange, the standing
direction that frames the C-arc's move from deferred-in-principle
(2026-09-03 ratification, `docs/2026-09-03_design-hygiene-arc.md`
(v)) to scheduled:

«I think we should try to do the disruptive thing if it'll result in
a more useful reasoning surface»

Effect: G-U and G-P — previously on `docs/2026-09-03_design-hygiene-
arc.md`'s "not this arc's to decide" list (`consumeAtOne`
uniformization and native method promotion) — are RULED IN and
scheduled in the C-arc order; the other seven gates (all C1-C5-family
items plus G-OUT and G-PIN) are RULED as recommended at the point
each is reached, per the plan's §5.1 order. Consuming records:
`CLAUDE.md` "What this repo is" (the two top-level goals),
`docs/2026-09-04_reasoning-surface-plan.md` §5.4 (each gate tagged),
`docs/2026-09-03_design-hygiene-arc.md` step (v) and its "not this
arc's to decide" list, `docs/assessment/decisions-2026-08-31.md`
2026-09-04 addendum, `TODO.md` (the C-arc section).

### The merge-train round-24 ruling record (2026-09-07) — the tracked record behind «Go ahead with the merge» (chunk L3 `land/panic-text-tape`: D2, D5, the BUG-087-shape extension, the C4 (c)→(a) move)

[AGENT] record (the round-24 rebase-reconciliation worker, lane
`land-panic-text`). Provenance chain: the [USER] quote was received by
the [AGENT] coordinator in-session and RELAYED to this worker in its
brief; the worker did not receive it firsthand (citation, never bare
assertion — the U0-incident convention). Context, as relayed: the
coordinator's merge-ask for landing chunk L3 (`docs/2026-09-07_land-
panic-text-tape.md`; branch `land/panic-text-tape` at `9e3c54f0`, the
adversarial-audit fix round applied) listed FOUR items tagged «[USER]
ratification PENDING at the merge gate» for ratification: (1) D2 — the
sprint's `string-member` lane RETIRED unlanded (landing plan
`docs/2026-09-07_typed-sprint-landing-plan.md` §4 D2; the [AGENT]
applied the plan's default); (2) D5 — no byte-level observation
channel now, a string payload whose FIRST LINE is not valid UTF-8 is
REFUSED by name and its three `panic-recover/panic-text/invalid-*` rows
stay red on BUG-004's `Cases:` line (plan §4 D5 option (i); the [AGENT]
applied the default); (3) the BUG-087-shape extension — the
`[recovered, repanicked]` marker of an equal re-panic reified as
`ChoiceSite.repanicCollapse` (bound 2), an [AGENT] extension of this
sheet's 2026-09-03 BUG-087 ruling's SHAPE («demonic choice so both are
admitted», ruled for ONE choice at the nil arm/R9a) to a second marker
under R-1's re-envelope authority (latitude inventory R10a); (4) the C4
(c)→(a) re-classification — `panic-recover/repanic-same-value-abort`,
a [USER]-ratified category-(c) pin (triage §7, 2026-08-20), moved to
the membership lane (PASS, `members=2`). Mike replied, verbatim as
relayed:

«Go ahead with the merge»

— read by the coordinator, and recorded here, as RATIFYING all four
items (the merge-ask named exactly these four as what the sign-off
would ratify). Effect: every PENDING tag the lane wrote now reads
«[USER] ratification — PENDING at the lane's tip, RULED [USER]
2026-09-07 at merge train round 24 — «Go ahead with the merge» (relayed
by the [AGENT] coordinator; the merge-ask listed D2, D5, the
BUG-087-shape extension and the C4 (c)→(a) move as the four items
ratified by this sign-off)», with the [AGENT]-default history left
visible (they WERE applied as defaults first). Consuming records: the
lane note §2.3/§2.4/§2.5/§6/§7 (+ §7.2, the ruling and the round-24
rebase), `docs/BUGS.md` BUG-004 (the L3 block), the latitude inventory
R10a + §10, the triage table C4 (the dated line + the L3 block),
`docs/language-coverage-ledger.md` §8 bucket table + §8w,
`GoLean/Interface.lean`, `GoLean/GoCore/Machine.lean` and
`GoLean/CLI.lean` docstrings, `Corpus/coverage/exec/panic-recover/
{panic-text,repanic-collapse,repanic-same-value-abort}/main.go` and the
19 `why` fields (18 `repanic-collapse` + `repanic-same-value-abort`).
Still OWED after this ruling: the `canonicalSlot0` row string in
`GoLean/GoCore/State.lean` (a core literal the fix round did not touch;
lane note §7 R2). Not ruled here: D4 (ratified by L4's own sign-off,
`docs/2026-09-07_land-observer-terminal.md` §3), BUG-107's three
options (open, L4), D1/L5 (held).

### The evaluation-order mechanism ruling record (2026-09-16) — the tracked record behind «the Cerberus model is the correct one»

[USER] Mike, 2026-09-16, verbatim, relayed by the [AGENT] coordinator — cite
as relayed: «Okay, so this feels like sort of a profound decision, but I think
the Cerberus model is the correct one (they did a lot of work thinking through
such issues). Can you go ahead with the next steps?»

**What was decided.** The evaluation-order model's MECHANISM is an explicit
unsequenced construct in the CORE, in the shape of Cerberus Core's `unseq`:
a statement's unordered evaluation occurrences are listed with their
dependency edges in the wire, and the MACHINE chooses which ready occurrence
runs next by a tape pick; lvalue identity is bound once and shared by the
read and the store; temporaries live per activation. The endpoint
probe-and-use scheme of the v1 design note (`design/eval-order-model-0915`
@ `90dc66f0`, NOT merged; cite by SHA) is retired as the mechanism; its §1
relation and doctrine rule (spec-ordered → structural ANF in the frontend;
spec-unordered with an observable → a machine tape choice; the rest refuses
by name) stand. Ground: the Codex review
`docs/2026-09-15_evaluation-order-model-review.md` (F1–F9, verdict «revise
before implementing»), whose findings the coordinator confirmed against the
note's §2 ([AGENT], 2026-09-15).

**What follows.** A v2 design note (lane `design/eval-order-model-v2-0916`)
following the review's revision sequence: dependency graph over evaluation
occurrences with guarded regions; the bounded reference enumerator first; the
core construct, binder lifetime, shared target identity, candidate
multiplicity and tape contract; the census re-done as a residual-node count;
the translation-certificate obligation kept visible; the v1 note's four
[USER] decisions RE-POSED against the corrected design (they are NOT ruled by
this record). The implementation slices are sequenced against the C-arc
ladder in that note — [AGENT] recommendation owed there, PENDING [USER].

### The typed-profile family ruling record (2026-09-16) — B7 charter D3: park via the reasoning repository

[USER] Mike, 2026-09-16, verbatim, relayed by the [AGENT] coordinator — cite as
relayed: «We're actually working on migrating reasoning to a new repo (see the
notes on a branch that another agent put together, and the reasoning work in
deps/ - gitgignored). So I think the correct home for this work is in a new repo
in deps/ called golean-reasoning or something like that. Then we can pin these
modules to the version of golean which they depend on and park them for future
revival. Perhaps the right solution for you is to delete, but leave a note saying
where this code lives in the git history (or make it an explicit tag / branch)».

**What was decided.** B7 charter D3 = (b) PARK: the `Boolean*`/`Recovery*`/
`Interface.lean` family (56 modules, 8,197 lines, and its `Tests` libraries) is
DELETED from main with an explicit note, preserved at tag
`typed-profiles/last-main-2026-09-16` and branch `park/typed-profiles-2026-09-16`
(both = main `62fc80731f0045c170634690bda1c26d1880f185`, the family's last main state), and its
future home is the reasoning repository under gitignored `deps/`
(`docs/2026-09-16_reasoning-archaeology.md` §9 — branch
`docs/reasoning-archaeology-0916`; name provisional), pinned to the golean
revision it depends on. Tests in the family that pin CORE behaviour are re-homed
into core test libraries BEFORE deletion. [AGENT] note for the record: the
archaeology survey §6 recommends keeping "admission invariants" in the semantics
repository; the [USER] ruling above supersedes that [AGENT] recommendation for
this family — the survey's point stands for `Step`, soundness/completeness and
trace observations, which are NOT parked.

**What follows.** A parking lane (branch off main, gated, merge on sign-off):
inventory → re-home core-pinning tests → delete → build + `ci --diff` → note doc
`docs/2026-09-16_typed-profiles-parked.md` + `docs/ARCHIVE.md` entry. D7 (the
dark spikes `spikes/gate-a1`, `spikes/iris-customer`) is prepared as a SEPARATE
commit in that lane under the same treatment, for the [USER] to accept or drop
at the merge ask — PENDING [USER]. B7's S5 no longer migrates the family.

### The B7 charter rulings record (2026-09-16) — D1, D2, D4–D8

[USER] Mike, 2026-09-16, verbatim, relayed by the [AGENT] coordinator — cite as
relayed: «Yes, let's go ahead with the D1-8 rulings as recommended (aside from
D3)» (D3 was ruled separately the same day: PARK — the record above).

**What was decided** (the charter's recommendations, `docs/2026-09-16_b7-context-store-charter.md` §9):
- **D1 (a)** — `Platform` stays the A5 global constant in B7; threading it is
  ONE later all-at-once re-envelope lane (latitude R1/R16). (c) rejected.
- **D2 (b)** — `structure ProgramCtx where program : Program` with projections.
- **D4 (a)** — the pool's per-thread state stays `MultiConfig.threads`/`.cur`
  beside `shared : Store`.
- **D5 (a)** — preservation evidence = the arc's standard: `ci --diff` at zero
  drift + the byte-identical choice trace + the live coherence theorems; no
  frozen before-model correspondence apparatus.
- **D6** — delete `MachineWf`'s vacuous `itersNormalized` conjunct in S1 (no
  objection raised).
- **D7** — the charter offered «leave dark and record, or delete» with no
  recommendation; the coordinator had proposed (2026-09-16, to the [USER])
  deleting `spikes/gate-a1` and `spikes/iris-customer` under the SAME
  tag/note treatment as the parked family, as a SEPARATE commit of the
  parking lane. [AGENT] reading of «as recommended»: that proposal is
  accepted; the commit stays separate so the [USER] can still drop it at the
  merge ask — disclosed as a reading, not a quote.
- **D8** — REPLAY the design slice by slice with the snapshot `85f9abd7` open
  as the reference (not REBASE-AND-REPAIR).

**What follows.** B7 is dispatched from the charter with these rulings written
in, AFTER the parking lane `park-lane/typed-profiles-0916` lands (one core
writer; both touch `GoLean.lean`/`lakefile.toml`/`scripts/ci`).

### The B7 handoff rulings record (2026-09-17)

[USER] Mike, 2026-09-17, verbatim, relayed by the [AGENT] coordinator — cite as
relayed: «We should delete the vacuous conjunct right? that's just a strict improvement. The rewordings sound fine. Agree with the audit, go ahead and launch (after the rulings if relevant)». This rules the four PENDING items of
`docs/2026-09-17_b7-context-store-handoff.md` §8. **What changed** ([AGENT]
fix-round worker, lane `core/b7-context-store-0917`, runtime commit `1fafc9f2`):
(1) the pool-side `itersNormalized` conjunct DELETED from `ThreadWf`/`MultiWf` —
`ThreadWf bound t` loses its `types` parameter, `MultiWf m` is context-free; 18
`MultiWfSound.lean` theorems restated without the constantly-true
hypotheses/conjuncts (none weakened); (2) the then-inert `Cont.itersNormalized`/
`Config.itersNormalized`, their `_true` certificates, the 11 walk/transparency
lemmas and `spawnPlan_iters` DELETED (16 declarations tombstoned) — the [AGENT]
reading of «strict improvement» (dead predicates leave with the conjunct),
conditional on nothing outside the core naming them (checked: docs only);
(3) the `Store.updateCell` refusal text and (4) the setup refusal text STAND as
landed («The rewordings sound fine»). Gate at the fix-round tree: `ci --diff`
EXIT=1 (934 s), the same two expected 5a-class items, zero other drift.

### The B7 audit fix round — two items PENDING [USER] (2026-09-17)

The pre-merge adversarial audit of `core/b7-context-store-0917`
(`docs/2026-09-17_b7-context-store-audit.md`, branch
`review/b7-context-store-0917` at `b51bc5c4`) returned FIX-FIRST, narrow and
records-class. Authority to act on it: [USER] Mike, 2026-09-17, verbatim,
relayed by the [AGENT] coordinator — cite as relayed: «Agree with the audit, go
ahead and launch». Eight of the ten findings were dispositioned by the [AGENT]
coordinator and applied (handoff §13). **TWO remain the [USER]'s:**

- **F1's alternative — the third refusal text.** `GoLean/GoCore/Machine.lean:
  3734`'s `.internal` literal was rewritten inside the string by a mechanical
  `applySyncOp ` → `applySyncOp ctx ` pass and shipped undisclosed. [AGENT]
  disposition APPLIED: **REVERTED to the pre-B7 bytes** (byte preservation is
  the fail-safe default; the rewritten text was garbled prose naming a Lean
  application to a human). **The [USER] may instead choose disclose-and-keep**
  — accept the new wording as a third, now-disclosed rewording; undoing the
  revert is one line. The arm is a defensive `.internal`, unreachable from
  `stepFn` (`applySyncOp` intercepts every try head), not observation-bearing:
  the differential and the choice trace cannot see either wording.
- **F8 — the congr trio's generality.** `loadLoc_root_congr`, `storeLoc_congr`,
  `normalizeValueForTy_congr` were stated over two `ExecState`s with `htypes :
  σ₂.types = σ₁.types`; they are now stated over two `Store`s under ONE `ctx`,
  i.e. the `ctx₁ = ctx₂` specialisation. The old form's residual content
  («these three operators read only `ctx.types`») is not recorded as a lemma.
  Nothing in-repo consumed the generality; with no customer, nothing downstream
  does. **[AGENT] recommendation: accept the one-context specialisation — with
  `ctx` a parameter the two-table generality has no meaning.** No change made.
  **PENDING [USER].**

Neither is a defect, neither blocks the gate, and neither is self-adjudicated:
both are posed at the merge ask.

### The on-deck decisions ruling record (2026-09-18) — sequencing, NaN, portability, NPDRF

[USER] Mike, 2026-09-18, verbatim, relayed by the [AGENT] coordinator — cite as
relayed: «(1) agreed, (2) the choices I suppose are either [a] pass a parameter
saying what the platform says, or [b] try to provide one uniform nondetermnism
right? I think this depends on what hte Go standard says, (3) We'll do this
eventually but not now, (4) We shouldn't delete, hard to revive that way. Can we
just deprecate/ mark unsound for now?» — answering the coordinator's triage of
the same day.

**What was decided.**
- **(1) Sequencing after C1 — RULED:** Stage C of the evaluation-order plan
  (the first native `unseq` fragment: frontend + decoder + adapters; closes
  BUG-101/BUG-104) runs directly after C1 lands, then the ladder resumes
  P → C3 → C4 → B6. One core writer throughout.
- **(2) NaN payload latitude (latitude R7, BUG-094) — DEFERRED to a memo:** the
  choice is [a] a platform parameter carrying what the target does vs [b] one
  uniform nondeterminism over what IEEE 754 / the Go spec permit; «depends on
  what the Go standard says». A short records memo establishes what the pinned
  spec and IEEE 754 fix, what gc/amd64 realizes, what `FloatBits` does today,
  and how the two-contracts framing (latitude inventory §11: Contract A =
  language, Contract B = target instance) maps onto [a]/[b]; the ruling follows
  the memo.
- **(3) A 32-bit oracle host / second `Platform` instance — DEFERRED:**
  «eventually but not now». Recorded; no lane.
- **(4) `NPDRFReduction` — RULED: DEPRECATE / MARK UNSOUND, do not delete.**
  The proposition (`GoLean/GoCore/NPDRF.lean`, false as stated per its own
  docstring) stays in the tree with an explicit machine-visible marker
  (`@[deprecated]` with a reason naming the refutation) and a docstring banner
  that it is NOT to be used as a hypothesis; the restatement waits for C1's
  access trace (its input). Folded into C1's S0 as a records-class core edit
  (C1 owns the core writer).

**Not ruled here (still PENDING [USER]):** the two trusted-surface #2 fixes
(pin `CGO_ENABLED` in the differential runner's oracle invocation; select the
oracle copy's file set through `go/build` in the harness) — posed 2026-09-18,
no answer yet.

**Also NOT ruled here — the C1 charter's D1–D7, D9, D10 (recorded at the C1
audit fix round, 2026-09-18, [AGENT]; audit F1).** The C1 charter
(`docs/2026-09-17_c1-memory-module-charter.md` §7), the C1 handoff and the
hygiene slice log had described these ten decisions as «RULED [USER] 2026-09-18
by default acceptance», citing this section; this section contains no such
text. What happened: the coordinator's triage classed D1 (root cells + path-
addressed leaf operations), D2 (dense array), D3 (`HeapNormal` as a `StateWf`
conjunct + `alloc` normalizes — a behaviour change at never-stored cells, gated
at zero drift), D4 (no heap-iso claim), D5 (label on `Step`/`StepM`), D6
(theorem + executable audit), D7 (BUG-041 stays FAIL; any other difference =
STOP), D9 (sync/chan/atomic emissions in the module), D10 (`Store.updateCell`'s
wording) as doctrine-determined or gate-arbitrated defaults, the [USER] did not
object, and the lane proceeded on the **[AGENT] coordinator's reading of that
non-objection**. That reading is not a ruling. **Explicit [USER] ratification
of D1–D7, D9, D10 is REQUESTED at the C1 merge ask — PENDING [USER]**; the
answer is to be recorded here verbatim (relayed) and the charter §7 header
re-tagged to cite it. Until then every C1 record says «[AGENT] reading of the
non-objection, ratification PENDING». D8 (ruling (4) above) is the one C1
decision with [USER] text.

### The C1 charter ratification and BUG-111 ruling record (2026-09-18)

[USER] Mike, 2026-09-18, verbatim, relayed by the [AGENT] coordinator — cite as
relayed: «(1) agree, (2) agree. Go ahead», answering the coordinator's merge ask
of the same day, which posed (1) «the C1 charter's recommendations D1 to D7, D9
and D10 as the lane's instructions» and (2) «BUG-111's fix: canonical-path keys at
emission, recommended, or type-tag normalization».

**What was decided.**
- **(1) RATIFIED [USER]:** the C1 charter (`docs/2026-09-17_c1-memory-module-charter.md`
  §7) recommendations D1 (root cells with path-addressed leaf operations), D2 (the
  dense `Array HeapCell`), D3 (`HeapNormal` + `alloc` normalizes), D4 (no
  heap-isomorphism latitude — zero drift on the machine), D5 (the access trace as a
  `Step`/`StepM` label), D6 (per-arm theorems AND the whole-corpus trace-equality
  audit), D7 (BUG-041's rows EQUAL; any narrowing a disclosed flip), D9 (sync-word and
  channel-object emissions inside the module), D10 (the `Store.updateCell` wording)
  are the lane's instructions. This supersedes the coordinator's earlier
  «default acceptance» wording (audit F1) with an explicit ruling. D8 was ruled
  separately (deprecate `NPDRFReduction`, do not delete).
- **(2) RULED [USER] — BUG-111 fix option (i):** `.data` accesses are keyed by the
  CANONICAL PATH at emission (root + positional path: where the write lands in the
  store), not by the structural spelling with its static `typeId`; lands as a disclosed
  `Cases:` flip on the proposed red-first row `race/negative/struct-tag-alias-field`
  (born-FAIL on the wrong side) plus a must-stay-green disjoint-fields guard; the
  successor C1 lane (S2c/S3) carries it.
- **«Go ahead»:** merge of C1 S0–S2b (`core/c1-memory-module-0918`) with its audit
  branch; train r41; the successor lane follows.

### The BUG-111 canonicalization-scope ratification record (2026-09-19)

[USER] Mike, 2026-09-19, verbatim, relayed by the [AGENT] coordinator — cite as
relayed: «Great, merge it. Then is the next piece on NaN to just do an investigatory
memo? If so do that» — answering the coordinator's merge ask of the same day, which
posed for ratification: the BUG-111 fix canonicalizes EVERY emitted location
(`.data`, `.syncWord`, `.chanObj` keys and the `HbAction` clock-table locations), wider
than the 2026-09-18 ruling's letter («canonical-path keys» for the `.data` accesses),
with the audit's evidence that the wider scope is NECESSARY (six alias programs wrong on
main's binary — three missed races, three to four false races — right on the candidate,
gc `-race` agreeing; `docs/2026-09-19_c1-s2c-audit.md` F1; pinned by the eight rows of
the fix round); and two lane calls — the WaitGroup alias row reshaped to a
RACE-ALL program (no lane pins a some-schedules race honestly) and the nested-mutex
copy row placed on BUG-080's `Cases:` line (the class it pins).

**What was decided.** RATIFIED by the merge («Great, merge it.»): the wider
canonicalization scope and both lane calls. C1 S2c + BUG-111 land (train r42).
The NaN question: the investigatory memo already exists
(`docs/2026-09-18_nan-latitude-memo.md`, branch `records/nan-envelope-memo-0918`,
reported 2026-09-18); «If so do that» is read by the coordinator as: land the memo
(records). The memo's RULING — option [a]+[b] recommended — remains PENDING [USER].

### The NaN latitude ruling record (2026-09-19) — R7 / BUG-094: adopt [a]+[b]

[USER] Mike, 2026-09-19, verbatim, relayed by the [AGENT] coordinator — cite as
relayed: «NaN: sounds good to me» — answering the coordinator's question of the same
day, «adopt [a]+[b] as the memo recommends?», the memo being
`docs/2026-09-18_nan-latitude-memo.md` (§5–§6), which itself answered the 2026-09-18
ruling-record item (2) («[a] pass a parameter saying what the platform says, or [b] try
to provide one uniform nondetermnism … depends on what the Go standard says»).

**What was decided.** [a]+[b]: the relation ENVELOPES the produced NaN over every quiet
NaN of the width at a named choice site (`ChoiceSite.nanBits`) — Contract A, the weakest
machine, since the pinned spec fixes nothing about NaN bits and IEEE 754 makes only
«quiet» mandatory; the executable's canonical slot 0 instantiates gc/amd64's realization
read from `Platform.gcAmd64` NaN fields — Contract B; the two-NaN-operand order (gc's own
instance is optimizer-dependent) becomes a width-2 membership alphabet. Latitude R7 moves
from (b-n) NARROWED to (a) ENVELOPED on implementation; BUG-094's seven rows flip
FAIL→PASS then. Implementation lane QUEUED after Stage C of the evaluation-order plan
(sequencing ruling (1) of 2026-09-18); cost per memo §7 (eleven `FloatBits` NaN arms take a
rule argument; guard + min/max pre-check deleted; no wire/observer change; 1–2 sessions).
The R7 heading is corrected NOW (records, this train) to the memo's pre-implementation text;
the adopted text replaces it when the lane lands.

### The C1 completion and Stage C rulings record (2026-09-19)

[USER] Mike, 2026-09-19, verbatim, relayed by the [AGENT] coordinator — cite as
relayed: «Agree, merge» — answering the coordinator's merge ask of the same day,
which posed five numbered items.

**What was decided.**
1. **C1 is COMPLETE modulo its owed list** (S3 audit F6): the eight cost-only `deliverS`
   saved-store sites and the select interception → C4; the slice-header/backing invariant
   (`offset + cap ≤ |backing|`, stated at `arrayIndexNatFormed` as a docstring) → a later
   slice as a `StateWf` conjunct/theorem. The charter §8 letter («`deliverS`'s saved-store
   arm gone») is unmet and disclosed; the reading is RATIFIED.
2. The C1 charter's B(c) row is SUPERSEDED by S3's boundary statement (audit F8).
3. **Stage C, width of the sensitive-operand set** (eval-order v2.1 §5 item 1): ALL mutable
   reads — staged: the Stage C pilot carries the minimal P(ii) reads its fixtures need, then
   widens. (The spec leaves the order unspecified; the weakest machine models it.)
4. **Stage C, read granularity** (N1): SPLIT — base/header and index producers plus ONE
   checked access (a fused read loses a legal placement; audit R6).
5. **Stage C, budget exhaustion on a membership row** (N3): REFUSE by name; never silently
   sequentialise; rows may go red — recorded as such.

C1 S3 (`core/c1-memory-module-s3-0919`) and its audit land at train r43; the Stage C lane
follows (v2.1 §7 Stage C: one native `unseq` fragment end to end), then Stage D/E, then the
NaN [a]+[b] lane, then P → C3 → C4 → B6.

### The Stage C landing ratification record (2026-09-20)

[USER] Mike, 2026-09-20, verbatim, relayed by the [AGENT] coordinator — cite as
relayed: «land it» — answering the coordinator's merge ask for Stage C of the
evaluation-order plan (`core/unseq-stage-c-0919` at `6886fe00`, audit + re-verification
MERGE-CLEAN at `1494f742`), which posed two items for ratification.

**What was decided (RATIFIED by the landing).**
1. Latitude E2/E12 (the VALUE axis: a sensitive operand's read before or after a
   sibling call) moves from (b) PINNED to (a) ENVELOPED on the NINE rows the Stage C
   pilot fixed or moved (BUG-101's two; the seven strict → membership lane moves), and
   ONLY those — the rest of the family stays (b) PINNED with the re-envelope obligation
   (`docs/2026-08-11_latitude-inventory.md` §2 E2/E12 wording bounded accordingly).
2. Two E13 narrowings are RETIRED on the pilot's rows — residual (1), the operand to the
   RIGHT of the event, and residual (9), the operand before the FIRST of several events —
   because the `unseq` graph models them there.

Also landed with this ratification: BUG-113 (open; the LEGACY path's `||`/`&&` beside a
lexically later call evaluated after the call — a pre-existing wrong answer, main =
candidate, gc/spec `false`; two born-FAIL rows + a control; fix = Stage E) and BUG-112
(fixed). Train r44 owes 5a with `--slow` (wire and decoder changed). Then Stage D (economics)
and Stage E (migration; the BUG-113 fix; legacy probe retirement; twin re-pin).

### The confluent-caption ruling record (2026-09-21) — Stage D audit F3

[USER] Mike, 2026-09-21, verbatim, relayed by the [AGENT] coordinator — cite as relayed:
«yes, I agree - go ahead» — to the coordinator's question whether to amend the `confluent`
lane's caption in `docs/coverage-suite-structure.md` (a certificate «over all registry-point
schedules») to say it ranges over ALL choice streams the row consumes — registry-point
schedules and, since Stage D, expression-order picks — because `continue-label`'s certificate
(its only choice site is `unseqNext`) is stronger than the old caption described. RULED:
the caption is amended (records, train r45). «go ahead» also lands Stage D (`core/unseq-
stage-d-0920`, audit MERGE-CLEAN at `5922ece7`) with the audit's F1/F2/F5 records fixes.

### The Stage E landing ratification record (2026-09-22) — seven items

[USER] Mike, 2026-09-22 (the ask posed 2026-09-21), verbatim, relayed by the [AGENT]
coordinator — cite as relayed: «Agree on the judgements, go ahead» — answering the coordinator's
merge ask for Stage E, families E1–E4, of the evaluation-order plan (`core/unseq-stage-e-0921`
at `bcf0b371` after the audit fix round; audit FIX-FIRST at `e957700f` → re-verification
MERGE-CLEAN at `22b64a42`, rebased onto the fixed tip as `f5f84595`/`2e3a011b`), which posed
seven items with the coordinator's judgement on each. «go ahead» is the merge sign-off (train
r46) and the dispatch of the E5/E6 lane.

**What was decided (RATIFIED by the landing — every item as the [AGENT] judgement posed it).**
1. **The spec reading for the built-ins — READING (a)**: the built-ins (`len`/`cap`, `make`,
   `new`, and by the same sentence `min`/`max`/`copy`/`append`/`clear`/…) are the «function
   calls» of spec#Order_of_evaluation's ordering sentence (spec#Built-in_functions «called like
   any other function»); `evalorder/unseq-conv-alloc/make-len-vs-call` is a FORCED singleton;
   E5 admits `min`/`max`/`copy`/`append` as E1 participants under the same reading. Reading (b)
   — only user calls are ordered; the row's set {6, 8}, a (b) pin of gc's order — was the named
   alternative, NOT taken (design §E4 F5; inventory E2/E12).
2. **The OBSERVABILITY trigger** (design §E3): a sweep enters the `unseq` graph iff some
   occurrence is unordered against an EFFECTFUL event; the 94 all-forced sweeps stay on the
   legacy path with their observations unchanged. The coarse trigger (admit the forced receives;
   re-enumerate the 403 concurrency rows for identical sets) was the named alternative, NOT taken.
3. **E2/E12 VALUE axis (b) PINNED → (a) ENVELOPED on the named rows only** — E1 `evalorder/
   unseq-globals/{read-vs-call,compound-vs-call}`; E2 `noodler/latitude/deref-vs-call`,
   `noodler/maps/compound-call-{mutates,deletes}`, `pointers/deref-target-rhs-call-order`,
   `builtins/len-vs-call-order/len-nil-only-none`, the born `evalorder/unseq-ptr-field-map/*`
   membership rows; E3 `evalorder/unseq-recv-method/{recv-vs-read,ptr-recv-vs-field-read}` — the
   Stage C pilot's precedent; the rest of the family stays (b) PINNED with the re-envelope
   obligation.
4. **E14 receiver sub-axis (a) ENVELOPED** on `noodler/latitude/receiver-vs-arg-call` {6, 105}
   and the born `evalorder/unseq-recv-method/value-recv-vs-arg-call` {6, 15}; E14 stays a (c)
   census row as an entry.
5. **Two lane moves via route α** (Stage D's amended caption «all choice streams the row
   consumes»): `noodler/methods/nil-receiver-recursion` strict → confluent `engine=dedup`;
   `goroutines/fork-join/two-workers-own-chans` engine DFS → dedup. The alternatives named on the
   rows (`depth=N`; a raised DFS work cap) NOT taken.
6. **Late structural allocations** (eval-order v2.1 §5 item 4, REALIZED at E4): a composite
   literal is a node without E1 edges — its payload reads unordered against the sibling calls
   and receives — with the [AGENT] correction that `make`/`new` are E1 participants (item 1's
   reading; the born control pins it against gc, 6 on 20/20).
7. **The `allocate` body kind**: ONE constructor over `AllocSpec` (the frontend's five hoist
   shapes), not a general `exec` statement body (design §E4; alternative named there).

Also landed with this ratification: the audit fix round — F1 (Go 1.26 `new(x)` inside an
admitted sweep lowered with the zero value, a WRONG ANSWER, lowered correctly; two born rows),
F2/F3 (a binder cell's address as an argument or capture; slice-literal indices and constant
`make` sizes — decode-time refusals by name), F4 (the trigger's hidden pin on `string([]byte)`/
`string([]rune)` widened; two born rows) — the re-verification's R1 NIT (one superfluous
singleton pick per `*new(…)` sweep) recorded, not fixed; BUG-104, BUG-102, BUG-113 carried to FIXED on the
branch (`docs/BUGS.md`); BUG-114's capture addendum (`records/bug114-capture-0921`: shape (b)
not reproducible over 73,600 draws; the observer refusal stands as filed, no observer change).
Train r46 owes 5a with `--slow` (frontend, decoder and core changed); the expected baseline is
3732 = 3497 PASS / 235 FAIL (four born rows, nothing else moved). Next: the E5 residue + E6
legacy-retirement lane (E6 waits on the legacy census reaching zero), then the NaN [a]+[b]
lane, then P → C3 → C4 → B6.

### The Stage E5 landing ratification record (2026-09-22) — seven items

[USER] Mike, 2026-09-22, verbatim, relayed by the [AGENT] coordinator — cite as relayed: «Great, agree with all recommendations, land it»
— answering the coordinator's merge ask for Stage E5 of the evaluation-order plan (`core/unseq-stage-e5-0922` at
`28919dd6` after the audit fix round; audit FIX-FIRST at `bb79c34a` → re-verification MERGE-CLEAN at `0125f5ad`,
rebased onto the fixed tip as `0a390343`), which posed seven items with the coordinator's recommendation on each.
«land it» is the merge sign-off (train r47) and the dispatch of the E6 lane.

**What was decided (RATIFIED by the landing — every item as recommended).**
1. **The trigger refinement — ADOPTED, executed in the E6 lane.** The Stage E trigger («a sweep enters the graph iff
   some occurrence is unordered against an EFFECTFUL event», ratified 2026-09-22 item 2) is amended to «… OR against
   another FAILING occurrence» — panic identity is an observable; without it, retiring the legacy probe would narrow
   the ~30 panic-vs-panic rows with no effectful event from two members to one (handoff §2 item 2).
2. **Non-main units — WIDEN the grammar.** The next lane lowers imported source units as graphs (the raft twin re-pins
   with a written reason); E6's zero-probe condition stays whole-corpus + twin. Re-scoping E6 to the main unit (two
   models coexisting in imported code) NOT taken (handoff §2 item 3).
3. **The re-verification's R1 — LAND with the follow-up.** A self-consistently forged source-local map annotation
   still decodes and answers (a pre-existing class: Stage C's D9 trust rule; the emitter never produces it). The
   follow-up — a decoder-wide cross-check of source-local annotations against their `declare` types — is owed to the
   next decoder-touching lane (handoff §3). FIX-FIRST now NOT taken.
4. **The `wide` body kind** (`UnseqBody.wide (binds) (spec : WideSpec)`, one closed kind mirroring `allocate`; arms
   `append`/`copy`/`mapLookup`/`typeAssert`) — as posed; `AllocSpec` arms and one-kind-per-built-in NOT taken.
5. **E2/E12's VALUE axis (a) ENVELOPED on the lane's 29 named rows** (handoff §2 item 5: the 20 born membership rows
   + the 9 moved rows, by name) — the entries stay (b) PINNED; reversion to (b) pins NOT taken.
6. **A named decoder refusal for an `after` edge on a literal `allocate`** (Stage E audit F8) — ADOPTED, queued for the
   next decoder-touching lane (not blocking this landing).
7. **The duplicate-dynamic-key store order** (audit F2: the (b) pin of gc's source-order store, spec-unspecified) —
   QUEUED as a future choice-site item; the pin stands with its re-envelope obligation (handoff §2 item 6).

Also landed with this ratification: the audit fix round — F1 (decoder map-type checks on all three map arms; mutants
45 → 49; a positive-control row added as an [AGENT] addition), F2 (reworded), F3 (the map-element-target widening
rowed from both sides; **BUG-115** filed for the legacy quarantine), F4 (the forced status split described; an
apparatus item owed — a manifest row admitting a status-diverse set), F5 (counts), F6/F7 (refusal texts; a dead
check deleted). Baseline 3732 = 3497 / 235 → 3760 = 3524 / 236 (28 born incl. one FAIL by design; 9 strict →
membership moves; 0 PASS → non-PASS). Train r47 owes 5a with `--slow` (core and decoder changed). Next: the E6 lane
(the trigger refinement, the non-main-unit grammar, legacy retirement at census zero, the two decoder follow-ups),
then the NaN [a]+[b] lane, then P → C3 → C4 → B6.

### Roadmap review requested (2026-09-22) — statement received, review PENDING

[USER] Mike, 2026-09-22, verbatim, relayed by the [AGENT] coordinator — cite as relayed (received during train r47,
before its close): «Can we pause once the merge is done and then talk about the overall roadmap for this project. Our
ultimate aim here is to support the GoLean logic that we're building in a different repo. That's our upstream customer.
Which of the things that we're building are actually useful for those customer proofs and is our prioritization right?»

Effect ([AGENT] reading, no ruling taken): the 2026-09-11 «We don't have as of now a customer» framing is REVISED by
the [USER] — the customer is the GoLean logic (a program logic over GoCore, built in a separate repository that will
consume this one at a pin); the 2026-09-16 «what this repo provides» statement and the 2026-09-05 F10 boundary stand.
The coordinator PAUSED after train r47's close: the E6 lane (ruled 2026-09-22 at the Stage E5 landing) is NOT
dispatched pending the review. An [AGENT] analysis memo was prepared for the discussion on branch
`docs/roadmap-customer-alignment-0922` (`docs/2026-09-22_roadmap-customer-alignment.md`, unmerged): its
recommendations (C3 and the end-to-end simulation ahead of NaN; a reader-only `Language` spike; a minimal interface +
pin record; an `unseq` confluence lemma) are [AGENT] and every reorder is PENDING [USER]. The rulings of the review will
be recorded here when taken.
### The roadmap review under the customer framing — rulings of 2026-09-22/23

Context: the [USER]'s 2026-09-22 request («Roadmap review requested (2026-09-22)» above); the coordinator's
assessment rested on the analysis memo `docs/2026-09-22_roadmap-customer-alignment.md` (rev. 2, surveying the
customer repo `~/projects/golean-logic/`, which the [USER] named: «The draft logic is in ~/projects/golean-logic/»).
The coordinator posed seven decisions; [USER] Mike answered, verbatim, relayed by the [AGENT] coordinator — cite as
relayed: «I think we'll want to give them one repin after all the breaking changes have landed. Can we batch these
together. (2) agree, we should make the model as regular as possible (3) litigate depending on the rest? (4) I don't
understand this point? (5) yes, if this isn't in the target, we can defer it, (6) the decision on all this is what
would be needed by the logic, (7) same answer. Can you write a note addressed at the logic team, proposing your
updated design, then we'll get their review».

**RULED.**
1. **Re-pin cadence — BATCH.** The remaining breaking reshapes of the core (the sequential `Step`/`stepFn` label,
   C3 `Cont := List Frame`, P native method promotion, B6 numeric locals, C4 block-scoped allocation) land in ONE
   window; the customer receives ONE re-pin offer after all of them, with a changelog. No breaking change lands
   outside the window without a separate ruling.
2. **The sequential step label — the FULL EVENT LABEL** (memory accesses ⊕ choice picks ⊕ output), matching the
   pool's `StepEvent` shape: «we should make the model as regular as possible». Executed inside the batched window,
   before C3 (its shape is part of the re-pin).
5. **NaN [a]+[b] — DEFERRED**: floats are outside the customer's target («if this isn't in the target, we can defer
   it»). The 2026-09-19 slot (after Stage E) is vacated; BUG-094's plan stands as a fidelity item without a lane.

**NOT RULED — referred to the customer's review** (the [USER]: «the decision on all this is what would be needed
by the logic»): 3. the timing of the records lane (the changelog + the simulation statement note) — «litigate
depending on the rest»; 6. the drops (no GoLean-side `Language` spike; the `unseq` confluence lemma deferred; NPDRF
restate-only; typed profiles parked); 7. weighting the differential corpus toward the customer's feature list.
Item 4 (the FORM of the stable interface: named bridge theorems + a per-pin changelog, optionally per-arm `stepFn`
equation lemmas as a supported `simp` surface, rather than a re-export module) was not understood as posed and is
re-explained in the proposal note.

**Direction.** [USER]: «Can you write a note addressed at the logic team, proposing your updated design, then we'll
get their review» → the proposal note `docs/2026-09-23_proposal-to-logic-team.md` ([AGENT], on this branch; the
customer's review decides items 3/4/6/7 and the contents of the window). The E6 lane (ruled 2026-09-22) stays
undispatched until the note is out; whether it precedes the window is part of the proposal.

Addendum (2026-09-23). Item 4 re-explained and RULED — [USER] Mike, verbatim, relayed: «Right, I agree regarding
item 4, let's see what that team asks for». The stable interface for the logic team is (i) a NAMED stable set of
bridge declarations with pinned statements, gated fail-closed, and (ii) a per-pin changelog, plus (iii) per-arm
`stepFn` equation lemmas if the logic team asks for them; a re-export facade module is NOT wanted. The exact set and
the (iii) question are the logic team's to answer in their review of `docs/2026-09-23_proposal-to-logic-team.md`.
[AGENT] reading of ruling 1 for E6 (flagged by the note's writer): the E6 lane retires a statement form, a
continuation frame and a choice site — a removal is breaking for a downstream `cases` — so E6 is treated as the FIRST
item INSIDE the batched window (the window opens with it), not as a change outside it; the single re-pin still comes
after everything. Posed to the [USER] for a nod with the note's summary.

Addendum (2026-09-23, later). [USER] Mike, verbatim, relayed: «We can leave it on a branch while they look at it» —
the proposal note, the analysis memo and these records STAY on branch `docs/roadmap-customer-alignment-0922`
(unmerged, unpushed; worktree `.claude/worktrees/roadmap-0922`) while the logic team reviews the note. The merge of the
branch and the window's dispatch (E6 first) follow their answers; the [USER]'s audit-trim/waiver for this
documentation-only branch is posed at that landing.

### The logic team's response to the proposal (2026-09-23) — received; the window revised under it

Source: `docs/2026-09-23_response-from-logic-team.md` (a verbatim copy of golean-logic's
`docs/2026-09-23_response-to-golean-proposal.md`, branch `docs/upstream-response-0923` @ `a9950b2`, sha256
`a1008badba858724bfc3f1f32a117ca81c50fee19fb1869aec37898fd86c5067`; their inspection record names our note at `6f1256f6`). Provenance: the logic
team's ([their AGENT] under [their USER]'s request «endorsing the plan or requesting changes … the reasoning
structures must be general: Raft is the first target and challenge, not the model for the logic's design»). Their
answers are NOT rulings in this repo; the [USER] Mike rules on the revised window (posed by the coordinator).

**Their answers to the ten questions (§7, condensed; the document is authoritative).** (1) ENDORSE the batch with
semantic conditions; order E6 → label + execution bridges → P → C3 → B6 → C4. (2) E6 INSIDE the window as its first
item. (3) the shared `{trace, picks, out}` record suffices; exact per-channel order; terminal effects and projections
proved; the silent projection preserved (no `[emptyLabel]` per step); client observations come from proved execution
cuts, not printed bytes («Ready is not stdout»). (4) YES to `BridgeSet.lean`, plus the prefix/terminal/choice/memory/
entry-layout families (§6); pin statements AND semantic equations, not names/types. (5) YES to equation lemmas over
the FINAL labelled shape; control/calls/defer and owned-memory operations first. (6) first bridge = sequential
terminal-aware PREFIXES (`Step` primitive; a counted, choice-threaded labelled prefix closure with arbitrary endpoints
+ a `Finish` classification; `LRun` derived), then the initialized single-goroutine readout/embedding; the pool
later. (7) records NOW for the contract and inventory; the exact changelog and evidence at the offer. (8) agree on
NaN, parked profiles, no upstream `Language` spike; the proposed «DRF `unseq` confluence» is FALSE as stated
(`Tests/unseq-wire/src/w1`: one goroutine, a mutating closure, an unordered read → {1, 2}) — defer a correctly scoped
theorem; keep `NPDRFReduction` explicitly unusable. (9) keep the corpus, add the staged §5 examples (direct methods,
multi-field records, byte slices near-term). (10) a dedicated migration after the completed offer, before their
receiver/E2 simulation proof; no calendar deadline, no interim pin.

**Their required changes to the execution statement (§2 — binding on the statement lane).** (i) retain the endpoint
state and residual choices on failure; (ii) account for terminal work (`abortConsult`, the `repanicCollapse` draw,
fallible `abortMsg`) — a zero-step `aborted` constructor is insufficient; (iii) exact fuel conventions, prefixes
proved independently of termination, earlier observations available under fuel-out/divergence; (iv) replay choices
by site/bound/value (modulo selection, empty-tape default, bound-≤1 no-consumption, terminal draws) with a coverage
theorem that no unrecorded consultation affects a step; (v) refusal kept separate — an unconditional interpreter/
prefix correspondence reporting refusal, terminal and fuel apart, then a corollary under a proved reachable-state
domain invariant. Program level: initialization, readout, output and residual choices in one composable account; a
scoped single-goroutine embedding first; a proved cost/stuttering translation if pool administration changes fuel;
the `initPrintRefusal?` scope stated. **Conditions on the reshapes (§4)**: P preserves receiver evaluation once,
receiver adjustment, embedded traversal, nil behaviour, method identity, method-value capture, recover eligibility;
exposes resolution/entry equations. B6: declaration IDs + a checked source table; lexical ID ≠ activation location;
numeric IDs NOT an API promise across source edits. C4: storage allocation separate from initializer execution;
captured cells survive lexical exit; per-iteration variables; «up to heap isomorphism» scoped as an injection with
private cells + stuttering over a stated observable domain, address-sensitive escapes audited first. C1: expose the
allocation-normalization premise and the read/write/frame laws; no unexplained global well-formedness premise per
client. **§5**: general simulation interfaces staged by their clients (MaybeUpdate, SentEntries, recvAck, Ready
return, slices, callbacks/Storage/timers, loops/concurrency); aliasing kept real; choices coupled by meaning.
**§6**: gate the semantic equations and a small independent consumer; the re-pin offer lists changed constructors,
wire schemas, choices, allocations, fuel, refusals, theorem premises + the differential/certification receipt; a dry
run is evidence, not their acceptance gate.

**Disposition ([AGENT] coordinator, PENDING [USER]):** the window is revised into a short charter
(`docs/2026-09-23_batched-window-charter.md`, this branch) adopting their order and conditions; the execution
statement is redesigned as `Prefix`/`Finish` with `LRun` derived and the five corrections; the «now» lane =
contract + inventory (BridgeSet, changelog, statement note, re-lowering their fourteen fixtures and variants);
the confluence item is corrected to «commutation under independence hypotheses, deferred». The [USER]'s rulings
on the charter, the records lane, the branch landing and the E6 dispatch are posed with it.
