# The design-hygiene arc — plan of record (2026-09-03)

Status: PLAN, [USER]-ratified 2026-09-03 (quote below). Source of
every item: `docs/2026-09-03_grumpy-professor-review.md` (the
review's §3 proposals, its ranking table, and its own sequencing
paragraph). This file is the arc's ledger: the sequence, the
invariants every slice must satisfy, and the per-slice landing
record. It does not restate the review's arguments — each item cites
the review entry it executes.

## Purpose

The nicest faithful Go semantics — not merely the avoidance of major
changes. The semantic effect of the machine is fixed by the doctrine
(`docs/2026-08-11_essence-of-go-doctrine.md`: the weakest machine Go
permits, all latitude included) and pinned by the differential; this
arc changes how that machine is WRITTEN so that the downstream
reasoning repo (which will consume this one as a pinned dependency)
pays for our structure, not our history, on every lemma.

## Provenance

- The review is [AGENT] work (worktree `grumpy-professor`, tree
  `b5abacc1`); its judgments are the arc's source, not its authority.
- The RATIFICATION is [USER] (Mike, 2026-09-03). The coordinator
  proposed «a design-hygiene arc alongside the stdlib work rather
  than a stop-the-world refactor; the cheap series plus the map
  stamps plus the outcome grammar, each slice independently gated
  and audited; open with the map stamps». Mike replied:

  > «Great, let's do it as you propose. I think eventually we will
  > want to do the bigger breaking changes as well, since our aim is
  > to get the *nicest* faithful go semantics, not just avoid major
  > changes. But we can schedule those later or now».

  This quote reached the slice-1 worker BY RELAY from the [AGENT]
  coordinator, not firsthand (U0-incident convention: citation, never
  bare assertion). Two things it ratifies: (a) the arc and its
  opening slice; (b) the big reshaping items (C1–C5) IN PRINCIPLE —
  their scheduling is deferred, and each returns to the [USER] as its
  own design gate when reached (see (v) below).

## The ratified sequence

The review's own sequencing paragraph (§3, after the ranking table),
adopted with one adjustment the coordinator proposed and the [USER]
ratified: B1 opens the arc (the review had it second, after the
A-series), because it is the single largest simplification per unit
cost and touches the fewest positional `fun_cases` proofs.

(i) **B1 — map entry-identity stamps** (the second audit's Q11).
    THIS ARC'S OPENING SLICE. Every map entry carries a fresh `Nat`
    id; `Cont.mapIterK`'s `produced`/`start` become id sets; the
    delete-prune machinery (`pruneIterFramesKey`, `pruneIterFramesAll`,
    `contAfterStmtOp`, `removeKeyList`, `keyInKeys`,
    `Config.mapContM`, `pruneForeign*`, `foreignPruneError`, the
    `pruneForeign` premise on `StepM.thread`) is deleted. A `thread`
    step is thread-local again (NPDRF obstruction 7 closes by
    construction). Design note: `docs/2026-09-03_hygiene-b1-stamps-design.md`.
    Status: DONE on branch `hygiene-b1-stamps` (2026-09-03) — gate
    green, audit verdict MERGE-READY (records amendments applied),
    merge on [USER] sign-off (see the landing record). CARRIED ONE
    [USER] DECISION to the sign-off: the slice narrowed the E9
    envelope on irreflexive (NaN) keys by construction (BUG-088 —
    the old model admitted spec-illegal repeat productions; the new
    one produces each entry once); E9's envelope is a [USER] ruling,
    so the narrowing was disclosed and referred, not self-adjudicated
    — and RATIFIED [USER] 2026-09-03 (relayed): «(b) it sounds like this breaks an old ruling but ends up more accurate to real go - approved». It supersedes the
    2026-08-19 E9 no-narrowing ruling for irreflexive keys only.

(ii) **The cheap A-series, A1–A10**, as small commits each gated by
     the full differential (`scripts/capped scripts/ci --diff`):
     A1 `GoError` split into `Refusal`/`Terminal`/`Budget` (type
     change only); A2 dense heap (`Array HeapCell`, addresses are
     indices, out-of-range store is `stuck` by type); A3 map/chan
     payloads out of `GoValue` into the cell; A4 `Expr.global gid`
     replacing `Expr.locLit`; A5 a `Platform` record for the gc
     layout pins; A6 `ShadowKey` instead of phantom `Loc`s in the
     detector; A7 one accumulator convention + `Config.applyPos`;
     A8 dead-generality sweep; A9 the refusal rule stated once and
     applied; A10 docstring diet (history to `docs/`, envelope
     statements stay in situ). A1 is the outcome grammar's first
     half and may be folded into wave (iii) instead — whichever
     lands first records the choice here.
     Status: DONE on branch `hygiene-a-series` (2026-09-04), forked
     from `main` @ `1b8401c0` (both prerequisite lanes landed): A1–A6,
     A8 (in part), A9, A10 (in part) landed as one commit each with the
     full differential at ZERO drift and the whole-corpus choice trace at
     ZERO consumption delta; A7 SKIPPED (folded into (iii)); A1 landed
     under (ii) — the choice is recorded here. Design note
     `docs/2026-09-03_hygiene-a-series-design.md`; evidence
     `docs/evidence/2026-09-03_hygiene-a-series/`. Owed to (iii): the
     program-text `locSup` deletion (A4), `itersNormalized` (A8), A7.
     **A11 (added 2026-09-04 by lane `fr4-rowm`'s audit fix round A3,
     [AGENT]; OWED, dated 2026-09-04): delete the dead `sortSlice` op** —
     `Stmt.sortSlice` (Syntax.lean), its Machine.lean/Ops.lean arms, the
     SyntaxEqb/MachineEqb cases and the Race/NPDRF mentions. Memo §3 row M
     retired the `slices.Sort` intercept, the frontend has not emitted
     `sort-slice` since, and the wire decoder refuses the node by name
     (NativeToIR.lean, that fix round), so the op is dead code from the
     wire's point of view; a GoCore deletion, so it lands here (the
     `hygiene-wave3` lane owns GoCore), never on a frontend lane. TODO:
     with wave (iii) or the next A-series commit, gated like every
     A-item by `scripts/capped scripts/ci --diff` at zero drift.
     One red gate in the series (A6's first attempt: a dedup-ENGINE
     merge-rate effect, no observation moved) is recorded with both
     transcripts. No [USER] design gate was hit: A4's wire check found
     no wire change.

(iii) **B2 + B3 + B8 as ONE re-proof wave** — the `Result` monad
      through the helpers (the 17 `*Panic` twin rules and the 41
      conversion sites go), the `Cont` classification + generic
      rebuild + field bundling (Q3/Q4), and consumption widths from
      the machine itself. They all shift the positional `fun_cases`
      tags in MachineSound, so the re-proof is paid once. A1 folds in
      here if not already landed under (ii).

(iv) **B4 / B5 / B6 / B7 in any order**: signal unification + a
     thread-level `Status` (Q6); a `Chan` module; frontend-resolved
     locals (`VarId := Nat`); `ProgramCtx`/`Store` split of
     `ExecState`.

(v) **The big reshaping C1–C5** — [USER]-ratified IN PRINCIPLE
    2026-09-03 («eventually … the bigger breaking changes as well»);
    scheduling RULED IN SCOPE 2026-09-04 (Mike, relayed by the
    [AGENT] coordinator — cite as relayed, not firsthand), on
    presentation of `docs/2026-09-04_reasoning-surface-plan.md` §5.4's
    nine design gates: «Great, this sounds good - let's move ahead
    with the plan. Our top level goal here is (1) to be a highly
    accurate go semantics, and (2) to support reasoning about go
    using an iris-lean layer (which we won't build, that's a
    customer)» — all nine gates (G-U, G-C5, G-C1, G-C2, G-P, G-C3,
    G-C4, G-OUT, G-PIN) RULED as recommended. Earlier the same day,
    the standing direction that frames this move: «I think we should
    try to do the disruptive thing if it'll result in a more useful
    reasoning surface» (full ruling record:
    `docs/2026-08-31_qrow-rulings.md` appendix). The C-arc now
    EXECUTES in the plan's §5.1 order, after wave (iii): U
    (`consumeAtOne`, G-U) → B4 → C5 (G-C5) → B7 → C1 (G-C1) → C2
    (G-C2, parallel lane) → B6 (parallel lane) → P (G-P) → C3 (G-C3)
    → C4 (G-C4) → B5 (optional, any time) → I5 (`Interface.lean`) →
    the assessment re-run → the pin offer (G-PIN). Each C-item still
    returns to the [USER] as its own design gate when reached — a
    HARD STOP, never self-adjudicated (CLAUDE.md, autonomous arcs);
    the 2026-09-04 ruling is a recommendation ADOPTED per gate, not a
    waiver of the per-item stop. C1 memory module
    with an access trace; C2 well-founded `TypeEnv` (the fuel towers
    become structural); C3 `Cont` as `List Frame` (pre-pin only —
    after the downstream repo pins the `Cont` shape it is a breaking
    change for them); C4 block-scoped allocation — carries the
    review's PRESERVATION CAVEAT explicitly: semantics-preserving
    only UP TO HEAP ISOMORPHISM (allocation order changes `Loc.base`
    ids; observations are address-free, but dedup certificates and
    any pinned `repr` change); C5 `.opDone` out of `Config` —
    carries the review's caveat explicitly: preserving MODULO FUEL
    ACCOUNTING (the marker strip is one `stepFn` step on both
    drivers; removing it shifts the exact fuel at which `fuelOut`
    fires — either keep a no-op step or accept the shift and re-pin,
    a [USER] call). The C-items' consumer-interface target, gap
    analysis, dependency order, per-item gates and sequence are in
    `docs/2026-09-04_reasoning-surface-plan.md` ([USER]-directed
    2026-09-04, relayed; docs only).

## Not this arc's to decide — SEMANTICS decisions for the [USER]

Recorded so they are not mistaken for hygiene items; each would
change the semantics or its accounting (review §3, "Not mine to
propose, but note"). Two of the five are RULED IN as of 2026-09-04
(gates G-U and G-P, `docs/2026-09-04_reasoning-surface-plan.md` §5.4;
scheduled in the C-arc order above, (v)); the remaining three are
still not scheduled anywhere:

- `ChoiceSite.policy.consumeAtOne` uniformization (`mapIter` pops at
  width 1, no other site does) — set of behaviours unchanged, stream
  realization changes, every fixed-stream baseline re-pins. RULED IN
  as G-U, first C-arc item after wave (iii).
- Native method promotion in the core instead of frontend wrappers —
  changes the frontend contract and the detector's hop-path argument.
  RULED IN as G-P, after C1 in the C-arc order.
- Unsequenced operand evaluation (a Cerberus `unseq`) — a semantics
  WIDENING; the doctrine's business. Still out.
- The range-over-slice desugar's race footprint vs gc's — a fidelity
  question. Still out.
- Boxing identity for efaces (`renderPanicHead`) — a semantics
  addition. Still out.

## Invariants of every slice

1. **Semantics-preserving on the MACHINE — or a disclosed fix.**
   Every corpus row's result unchanged; the choice tape consumed
   identically (same sites, same bounds, same order) — unless a
   bijection on streams is argued in the slice's design note AND the
   [USER] signs the resulting re-pin. Where a refactor is found to
   CHANGE a behaviour (a class the old representation got wrong), the
   change is not absorbed as "preservation": it is filed as a BUG with
   a red-first pin row (old binary vs new vs gc), disclosed in the
   design note, the inventory and the plan, and REFERRED TO THE [USER]
   as a semantics decision at the sign-off — an envelope, once ruled,
   is the [USER]'s to move (B1's BUG-088 is the first instance). Where
   a proposal preserves behaviour only up to heap isomorphism or fuel
   accounting (C4, C5) the slice SAYS so, up front, and stops at the
   [USER] gate.
2. **Full `scripts/capped scripts/ci --diff` as the regression, ZERO
   drift expected.** A changed row is a STOP-and-report, not a re-pin:
   a change means the envelope moved. A slice may ADD rows that pin a
   behaviour the refactor made reachable or exact; it reports them as
   additions, never buries them in drift.
3. **Pre-merge adversarial audit**, unconditional (CLAUDE.md merge
   protocol); scope and waiver are the [USER]'s.
4. **No gate weakening, no baseline weakening, no trust-surface
   widening** (the escape-hatch scans stay green; no `sorry`, no
   `axiom`, no `native_decide`; no `partial` in `GoLean/GoCore/`).
5. **Proofs move arm-for-arm.** A deleted definition takes its lemmas
   with it (tombstoned in the slice's design note); a reshaped
   definition's lemmas are restated, never weakened; the differential
   is the regression where a formal bisimulation is not cheap, and
   the design note says which.
6. **Records kept in step**: the latitude inventory, BUGS.md residual
   text, NPDRF obstruction list, the envelope docstrings, and the
   review's entry (a "LANDED <sha>" line) are updated in the landing
   commit; an evidence dir per `docs/evidence/README.md`'s eight
   rules where a machine-side set-equality or measurement is claimed.

## Landing record

| Slice | Item | Branch | Landed | Notes |
|---|---|---|---|---|
| 2 | A-series A1–A10 | `hygiene-a-series` | branch-complete 2026-09-04: A1 `dfa68802`, A2 `7cba41cd`, A3 `6973354b`, A4 `bcdf04c1`, A5 `48d9aba8`, A6 `367dab2f`, A8 `7ff80223`, A9 `80b4ed89`, A10 `884e5226` + a records commit (SHA in the evidence README); every gate `ci --diff` PASS 3284 = 3085/199 at zero drift, choice-trace delta 0; not merged | design note `docs/2026-09-03_hygiene-a-series-design.md`; evidence `docs/evidence/2026-09-03_hygiene-a-series/`; A7 SKIPPED (→ B3); net core delta and per-item lemma tombstones in the note |
| 1 | B1 stamps | `hygiene-b1-stamps` | branch-complete 2026-09-03, landing commit `f6152a6c`; audit verdict MERGE-READY, fix round `a4cf54e4` (clean-tree ci --diff PASS, 3199/3199); E9 irreflexive-key narrowing RATIFIED [USER] 2026-09-03 (relayed; record in docs/2026-08-31_qrow-rulings.md); merge sign-off pending; not merged | design note `docs/2026-09-03_hygiene-b1-stamps-design.md`; evidence `docs/evidence/2026-09-03_hygiene-b1-stamps/`; 14 defs + 14 theorems + 3 rule premises deleted, −649 lines; zero drift on 3195 rows; +4 rows `maps/nan-key-range`, `maps/nan-key-range-aggregate/{array,struct,interface}` (BUG-088, found by the bisimulation argument, fixed by construction — an E9 narrowing on irreflexive keys, DISCLOSED, [USER] ratification pending at merge) |
