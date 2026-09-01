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
and not otherwise tracked, auditor D3-2). Rows 2 and 3 remain
OPEN. Reds total 20.

| # | row (reds) | status | ruling / state |
|---|---|---|---|
| 1 | **Q-INITSPAWN** (1) | **RULED [USER] 2026-08-31** | Envelope ruled as recommended: init-spawned children are ordinary goroutines from the spawn boundary (L1, zero new sites; during-init execution probed 40/40 — deferred-release models foreclosed). VEHICLE REFRESH: the memo's "rider on slice 3(a)" is dead (that W3.2 slice never ran; arc parked) — implementation is a standalone `$pkginit` item on this product's backlog (re-homed per fidelity decision 6), sequenced with the next init-phase surgery. Ruling binds any future implementer now. |
| 2 | **Q-ATOMIC** (5) | **OPEN** — the arc decision | mem#atomic as a forced SC point stands; the atomics-arc design memo is still the recommendation. TWO REFRESHES before ruling: (a) "FairStream tier bundled" must read as future work TO BE BUILT (FairStream has never been a Lean definition — assessment finding); (b) the arc has NO live owner post-split — ratifying requires naming one. Decision shape: ratify-with-owner / ratify-with-FairStream-split (A′) / defer the family (Q-TRYLOCK's implementation and the liveness story inherit the wait). |
| 3 | **Q-SELSEL** (2) | **OPEN** — stale premise, held by coordinator recommendation | Do not rule as written: the scheduling driver ("before the raft node layer") is parked with the reasoning product, and the envelope rides C7's pairing argument whose re-argue trigger ALREADY FIRED (B1/B2 changed the wake machinery; the promised re-argument was never recorded — p2-keeps-a1 A1-14), with an unprobed corner (two clauses on one channel, woken by close). PREREQ (S): refresh C7's argument + run the close-wake probe; then re-present. |
| 4 | **Q-RACEPATH** (1) | **RULED [USER] 2026-08-31** | Constant-index narrowing (S) as recommended: extend the shipped fieldGet-chain narrowing to evaluated-index indexGet frames; dynamic-index residual stays in O1 with its trigger. VEHICLE REFRESH: "next footprint-touching slice" = the Tier-4 detector-soundness leg (the natural co-located work). |
| 5 | **Q-TRYLOCK** (1) | **RULED [USER] 2026-08-31 via the killable-set approval; explicit per-row confirmation queued at the merge pause** (auditor D3-2: the blanket quote's coverage of zero-red deferrals is an extended reading) | Deferred WITH the envelope pre-ruled, as recommended: when modeled, TryLock takes mem#locks' spurious-failure member as a real width-2 choice site (success-edge-only detector; the fairness-claim class); the always-succeeds pin is off the menu permanently. Implementation inherits Q-ATOMIC's arc decision. |
| 6 | **Q-SYNCVAL** (5) | **RULED [USER] 2026-08-31 — implement** | Identity principle ratified (indirection consumes the same C8 site or refuses — never variant semantics) and P-S2-6 green-lit (real stub bodies over EXISTING sync machine ops; frontend-only; flips all 5 reds). D-002 FREEZE INTERACTION — [AGENT] interpretation, the user's recorded words do not mention D-002; [USER] confirmation REQUIRED before the SYNCVAL/SYNCLIT slice launches (queued question at the merge pause): this lift is NOT shim injection — it adds no hand-modeled stdlib semantics; it plumbs values to already-modeled machine ops, and the identity principle is precisely the anti-variant-semantics rule the freeze exists to enforce. Any deviation from that shape during implementation is a STOP-and-ask. |
| 7 | **Q-SYNCLIT** (2) | **RULED [USER] 2026-08-31 — implement** | The S lowering as recommended (spec forces empty-literal-only cross-package ≡ zero value ≡ var/new; copy question already answered by sync design §3/p10) — rider on the Q-SYNCVAL slice. |
| 8 | **Q-COND** (3) | **RULED [USER] 2026-08-31 via the killable-set approval; explicit per-row confirmation queued at the merge pause** (auditor D3-2: the blanket quote's coverage of zero-red deferrals is an extended reading) | Deferred WITH the envelope pre-ruled from the docs text, as recommended: NO spurious wakeups (documented upper bound), Signal = any-waiter, Broadcast = forced-all folding into C8, TSan-realized HB, copy = detected panic. Zero demand; pure frontier. |

## Execution

- The **Q-SYNCVAL + Q-SYNCLIT slice** (7 reds, frontend-only, S)
  launches IMMEDIATELY AFTER the Tier-1 fixes lane lands — both
  edit `tools/nativefrontend` and re-pin `baselines/native-full.tsv`,
  so sequential beats a merge fight — AND ONLY AFTER the [USER]
  confirms row 6's D-002 freeze-interaction reading ([AGENT]
  interpretation, confirmation REQUIRED — queued question at the
  merge pause); until that confirmation the slice does not launch. Slice contract: identity
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
  done (queued as an S item).

## Appendix — the coordinator's row-by-row currency table

[AGENT] reconstruction of the table presented in-session (auditor
D3-2: the rulings above cite this table but it was never tracked;
its substance is the sheet's own status column, restated here as
what was put in front of the user).

| # | row | currency finding | disposition presented |
|---|---|---|---|
| 1 | Q-INITSPAWN | recommendation current; VEHICLE stale (slice 3(a) dead — standalone `$pkginit` backlog item instead) | rule now as recommended |
| 2 | Q-ATOMIC | recommendation needs two refreshes before ruling: FairStream must read as future work TO BE BUILT, and the arc has NO live owner post-split | hold — returns with an owner proposal |
| 3 | Q-SELSEL | STALE premise: scheduling driver parked with the reasoning product; C7's re-argue trigger already fired (re-argument never recorded, A1-14); unprobed close-wake corner | hold — C7 refresh + close-wake probe, then re-present |
| 4 | Q-RACEPATH | recommendation current; vehicle refresh ("next footprint-touching slice" = Tier-4 detector-soundness leg) | rule now as recommended |
| 5 | Q-TRYLOCK | recommendation current; zero-red pre-ruled DEFERRAL (kills no reds; implementation inherits Q-ATOMIC's arc decision) | defer with the envelope pre-ruled |
| 6 | Q-SYNCVAL | recommendation current; KILLABLE — frontend-only, flips all 5 reds | rule + implement |
| 7 | Q-SYNCLIT | recommendation current; KILLABLE — rider on the Q-SYNCVAL slice, flips 2 reds | rule + implement |
| 8 | Q-COND | recommendation current; zero-red pre-ruled DEFERRAL (docs-text envelope; zero demand, pure frontier) | defer with the envelope pre-ruled |
