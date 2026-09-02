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
merge ask). Row 2 remains OPEN. Reds total 20.

| # | row (reds) | status | ruling / state |
|---|---|---|---|
| 1 | **Q-INITSPAWN** (1) | **RULED [USER] 2026-08-31** | Envelope ruled as recommended: init-spawned children are ordinary goroutines from the spawn boundary (L1, zero new sites; during-init execution probed 40/40 — deferred-release models foreclosed). VEHICLE REFRESH: the memo's "rider on slice 3(a)" is dead (that W3.2 slice never ran; arc parked) — implementation is a standalone `$pkginit` item on this product's backlog (re-homed per fidelity decision 6), sequenced with the next init-phase surgery. Ruling binds any future implementer now. |
| 2 | **Q-ATOMIC** (5) | **OPEN** — the arc decision | mem#atomic as a forced SC point stands; the atomics-arc design memo is still the recommendation. TWO REFRESHES before ruling: (a) "FairStream tier bundled" must read as future work TO BE BUILT (FairStream has never been a Lean definition — assessment finding); (b) the arc has NO live owner post-split — ratifying requires naming one. Decision shape: ratify-with-owner / ratify-with-FairStream-split (A′) / defer the family (Q-TRYLOCK's implementation and the liveness story inherit the wait). |
| 3 | **Q-SELSEL** (2) | **RULED [USER] 2026-09-01 — option (A) with an implementation slot** ("(1) agree" to the tracked two-item menu — recorded VERBATIM in the appendix below; menu recorded post-hoc from the session at the audit's C5, [USER] countersign requested at the merge ask; prereq discharged same day): the asymmetric-arrival envelope adopted — its structure is leg (1) of the refreshed C7 argument; the falsified commit-by-waking-event wording is NOT part of the adopted envelope (the owed wording correction lands at implementation); the idiom is ordinary Go, not raft-specific, so the slot lives on this product's backlog despite the original consumer being parked | SUPERSEDED PRE-RULING STATE: Do not rule as written: the scheduling driver ("before the raft node layer") is parked with the reasoning product, and the envelope rides C7's pairing argument whose re-argue trigger ALREADY FIRED (B1/B2 changed the wake machinery; the promised re-argument was never recorded — p2-keeps-a1 A1-14), with an unprobed corner (two clauses on one channel, woken by close). PREREQ (S): refresh C7's argument + run the close-wake probe; then re-present. **RE-PRESENTATION (2026-09-01 [AGENT], C7-refresh lane):** both prerequisites ran. (i) The close-wake probe (`docs/evidence/2026-09-01_c7-close-wake-probe/`): gc commits EITHER same-channel clause from one close wake (~half each over 800 runs incl. a park-first isolate), falsifying the old "committed by the EVENT that wakes it" wording — but observed ∈ modeled HOLDS (machine-certified {1,2} ⊇ gc's {1,2}; the second member rides the always-realizable close-before-entry schedule + entry L2 draw). The envelope does NOT need widening. (ii) C7's argument is re-recorded post-B1/B2 as two legs (inventory C7 + §8 e12): partner wakes = L4 clause-INDIVIDUAL pairing at the arrival intercept; close wakes = the entry-path mask. Consequence for this row: recommendation (A)'s envelope survives UNCHANGED — its structure (each matching parked clause a distinct L4 candidate, memo option (B)'s own decomposition) is exactly leg (1) and never leaned on the falsified wording; one wording correction owed at implementation: the memo's "C7's commit-by-waking-event argument extended verbatim" must read "the parked side's matched clause is the L4 candidate's clause". The close corner is irrelevant to select↔select rendezvous (closes never pair). Remaining for the [USER]: the vehicle — (A)'s implementation slot post-split (the raft node-layer driver is parked with the reasoning product; the 2 reds stand in this repo's baseline either way) — i.e. rule (A)-with-a-slot or (C) defer-with-dependency-recorded. |
| 4 | **Q-RACEPATH** (1) | **RULED [USER] 2026-08-31 — IMPLEMENTED 2026-09-02 [AGENT]** (Tier-4 detector-soundness lane) | Constant-index narrowing (S) as recommended: extend the shipped fieldGet-chain narrowing to evaluated-index indexGet frames; dynamic-index residual stays in O1 with its trigger. VEHICLE REFRESH: "next footprint-touching slice" = the Tier-4 detector-soundness leg (the natural co-located work). IMPLEMENTATION RECORD: `projChainTarget` (Race.lean) — the narrowing fires for `indexGet` frames whose pending index is an `intLit` AND whose base cell is an ARRAY (slice/string headers stay whole-cell), composing with `fieldGet` in either order; `race/free/array-read-write` flipped FAIL→PASS (confluent), +2 chain-form green guards, +2 must-stay-racy racy-lane guards, +1 born-FAIL residual pin (`race/free/array-dyn-index-read-write`, on BUG-041's Cases line). Ruling text carried to inventory C10/O1, ledger §6, BUG-041. |
| 5 | **Q-TRYLOCK** (1) | **RULED [USER] 2026-08-31 via the killable-set approval; per-row CONFIRMED [USER] 2026-09-01 ("the 4 confirmations all seem like reasonable interpretations… agree on all of the above")** (auditor D3-2 resolved) | Deferred WITH the envelope pre-ruled, as recommended: when modeled, TryLock takes mem#locks' spurious-failure member as a real width-2 choice site (success-edge-only detector; the fairness-claim class); the always-succeeds pin is off the menu permanently. Implementation inherits Q-ATOMIC's arc decision. |
| 6 | **Q-SYNCVAL** (5) | **RULED [USER] 2026-08-31 — implement** | Identity principle ratified (indirection consumes the same C8 site or refuses — never variant semantics) and P-S2-6 green-lit (real stub bodies over EXISTING sync machine ops; frontend-only; flips all 5 reds). D-002 FREEZE INTERACTION — [AGENT] interpretation, CONFIRMED [USER] 2026-09-01 ("the 4 confirmations all seem like reasonable interpretations… agree on all of the above"): this lift is NOT shim injection — it adds no hand-modeled stdlib semantics; it plumbs values to already-modeled machine ops, and the identity principle is precisely the anti-variant-semantics rule the freeze exists to enforce. Any deviation from that shape during implementation is a STOP-and-ask. |
| 7 | **Q-SYNCLIT** (2) | **RULED [USER] 2026-08-31 — implement** | The S lowering as recommended (spec forces empty-literal-only cross-package ≡ zero value ≡ var/new; copy question already answered by sync design §3/p10) — rider on the Q-SYNCVAL slice. |
| 8 | **Q-COND** (3) | **RULED [USER] 2026-08-31 via the killable-set approval; per-row CONFIRMED [USER] 2026-09-01 ("the 4 confirmations all seem like reasonable interpretations… agree on all of the above")** (auditor D3-2 resolved) | Deferred WITH the envelope pre-ruled from the docs text, as recommended: NO spurious wakeups (documented upper bound), Signal = any-waiter, Broadcast = forced-all folding into C8, TSan-realized HB, copy = detected panic. Zero demand; pure frontier. |

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
  lane): row 3 is ready for ruling; see its RE-PRESENTATION.**

## Appendix — the coordinator's row-by-row currency table

[AGENT] reconstruction of the table presented in-session (auditor
D3-2: the rulings above cite this table but it was never tracked;
its substance is the sheet's own status column, restated here as
what was put in front of the user).

| # | row | currency finding | disposition presented |
|---|---|---|---|
| 1 | Q-INITSPAWN | recommendation current; VEHICLE stale (slice 3(a) dead — standalone `$pkginit` backlog item instead) | rule now as recommended |
| 2 | Q-ATOMIC | recommendation needs two refreshes before ruling: FairStream must read as future work TO BE BUILT, and the arc has NO live owner post-split | hold — returns with an owner proposal |
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
