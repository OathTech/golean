# W2.5 — the invariant design note

STATUS (2026-08-27): ADOPTED as the W3 postcondition contract by
[AGENT] adjudication under the active autonomous directive (the goal
monitor refused a stop at the plan's named [USER] gate; conflict
resolution logged in `docs/raft-campaign-log.md`). The three §3 open
points are resolved as recommended (ghost-acks; separate lens
readers; T1 scope). **This adjudication is a mandatory [USER] review
item at the landing ceremony** — the gate's substance is still
Mike's to overturn before merge.

The plan's named checkpoint: the full loop invariant `I` as a written
artifact before any W3 function spec is chartered, because every W3
postcondition concludes clauses of `I`. Sources: the professor's
final-review Gaps 1+3 (NetCorr; the invariant's expressiveness
defects), W2's five-clause skeleton (measured against the landed
machinery — the gate's composition is the consumption pattern every
clause must feed), and the checker/driver census. Everything below is
[AGENT]-drafted; the gate is yours: approve, amend, or redirect.

## 0. The consumption contract (what shapes the design)

The invariant is consumed three ways, and each clause is stated in
the vocabulary its consumer needs:
- **By W3's body spec** (preservation): clauses must be provable
  postconditions of the landed composition pattern — CallSpec +
  FrameSim placement + plug rule + reader congruence (the W2 gate's
  exact recipe). Clauses are therefore reader-vocabulary predicates
  plus placement data, never cell enumerations.
- **By the abstract leaves** (W5): the S1 leaf needs `ClaimTrace` +
  the interface; the S23 leaf needs `HistInv` + `Star HStep` + the
  interface; `EStep`'s constructor premises (hgen etc.) need NetCorr.
- **By the loop rule** (W4): one predicate over loop-head states,
  phase-split, with the base delivered by the init spec (stage A
  landed; stage B joins in W3).

## 1. `I`, clause by clause

```
I σ :=  Base σ ∧ Pair σ ∧ Hygiene σ ∧ Stream σ
      ∧ (Electing σ ∨ Elected σ)                     -- the phase split
```

**C1 — Base / concrete well-formedness (`Base σ`).** The init-spec
product, maintained: the 31 statics materialized at true addresses
(identity placement at the base — W1's bodies_inv finding makes this
free); the twin/node/net structures TypeId-well-shaped so the
readers are defined (`absTwinRead σ tl = some _` — lift-definedness
as a clause, per the big-step square decision); the logger flag; the
harness counters readable. Base case: `initSetup_establishes` +
stage-B (newTwin's loops, first W3 units).

**C2 — the footprint-carrier pairing (`Pair σ`).** W2's clause (2),
generalizing the professor's "pairing as a relation": for each node
i, ∃ a placement (ρᵢ, frᵢ) and a footprint-carrier state such that
FrameSim relates the carrier to σ at that placement AND the deep
reader `absRaftNode` on the carrier equals `proj (N.node i)` — i.e.
the pairing carries THE PLACEMENT DATA the handlers consume (this is
what makes W3's specs applicable at loop-head states without
re-deriving placements — W1's Leg-B finding 3 fixed structurally).
Abstract side: ∃ N ghost-completed, with `Reach (EStep voters) N₀ N`
(the S1 carrier) and — in `Elected` — the HNet pairing
(appliedLog/hist via the projection with the newest/oldest
convention bridge) plus `HistInv ldr tm` and `Star (HStep ldr tm
certified) H₀ N_H`. The SHELL-SYNC sub-clause: at loop heads every
node is locally quiesced, so the harness-observed shells agree with
the deep reader on the fields ClaimTrace speaks (state/term), with
commit deliberately OUTSIDE the S1 projection (the stutter-provability
condition the professor flagged).

**C3 — the checker-state correspondence (`CheckerCorr ⊆ Pair`).**
The professor's Gap 3 clause, W2-vocabulary: ∃ event histories
`evsS1 evsA` with (a) `ClaimTrace (EStep voters) N₀ evsS1`; (b) the
concrete `leaderOf` map ↔ `(s1Run evsS1).leaderOf`, claims counter
↔ `.claims`; (c) the concrete `byIndex`/`got`/per-node cursors ↔
`s23Run evsA` state; (d) `evsA` ↔ the appliedLogs of N_H; (e) the
violation counter = the model runs' violation sum + 0 (the guards
silent — each guard's silence a named W3 spec conclusion per the
T1-V census). Requires the READER EXTENSION (leaderOf/byIndex/got/
cursors as lens readers) — a named W3 unit.

**C4 — NetCorr (`⊆ Pair`; the professor's Gap 1, four clauses).**
For every live message m in the concrete net (read via absMessage):
- **population**: m.typ ∈ {Vote, VoteResp, App, AppResp, Prop(local)}
  — in particular NO MsgTimeoutNow/TransferLeader/Hup, which is what
  excludes a second election as a PRESERVED fact (the library can
  campaign on receipt; the driver never emits the trigger); and all
  entries EntryNormal (feeds the S3-anomaly guard's silence).
- **hgen (term-aware grant provenance)**: m.typ = VoteResp ∧
  ¬m.reject → (m.term, m.dst) ∈ ghost.votes m.src — discharging
  EStep.recvVoteResp's premise at delivery.
- **payload**: m.typ = App → entries(m) = the hist slice at
  (m.index…) ∧ m.commit ≤ committed(ldr) — discharging
  HStep.deliverAppend's premises.
- **ack/Match**: m.typ = AppResp ∧ ¬m.reject → the sender's log
  length ≥ m.index — the evidence `certified` is instantiated from
  at the leader's commit-advance (the Match-evidence W3 unit).
Preservation: every W3 handler spec carries "emissions preserve
NetCorr" (the emission census per handler is part of each spec's
charter).

**C5 — plug-context hygiene + stream threading (`Hygiene`/`Stream`).**
W2's clauses (3)+(5): at loop heads the driver's continuation is
`mapIterFree` and recover-refuting (so every plug-rule application
in the body discharges its two premises by rfl — measured shape);
the choice stream obligations: init transparent (landed), spans
∀ch or draw-quantified with suffix monotonicity (the judgment's
standing discipline).

**The phase split.** `Electing`: no leader ever (ghost.victories
empty, claims 0, N_H absent, net vote-family only). `Elected ldr
tm`: the winning delivery's postcondition ESTABLISHES the HNet
carrier (H₀ from the noop-as-first-propose, the snapshot index
offset absorbed by the projection), fixes (ldr, tm) = (1, the
campaign term) — justified as the run's only election by C4's
population clause, not by assertion. The phase transition is one
designated body-spec case (the winning MsgVoteResp), a named W3
unit.

## 2. What this design fixes, traceably

Professor Gap 1 → C4 (each sub-clause with its consumer named).
Gap 3.1 → C3; Gap 3.2 → the phase split + the HNet half of C2;
Gap 3.3 → C2's ∃-placement/∃-ghost relational form + shell-sync.
W1 Leg-B finding 3 → C2's placement data. W2 skeleton clauses 1-5
→ C1-C5 as marked. The minor professor items: commit outside the
S1 projection (C2); all-EntryNormal (C4 population); the harvest
measure and guard silences are W3 spec conclusions consumed at C3(e).

## 3. Open points FOR THE GATE (your calls)

1. **`certified`'s instantiation**: the design instantiates it as
   "∃ quorum of AppResp acks recorded at ≥ the index" carried in
   the ghost (extending Ghost with an acks map) — the alternative
   (derive from NetCorr's ack clause at commit time without ghost
   state) is lighter but re-derives quorum facts per commit.
   Recommendation: the ghost-acks extension (mirrors votes/victories,
   uniform machinery).
2. **The reader extension's shape**: new AbsTwinV1 structure vs
   separate lens readers per checker map. Recommendation: separate
   readers (composable, no version churn in AbsTwinV0 consumers).
3. **Scope check**: C4's payload clause is stated for the T1
   fragment (single leader/term). The family-general form is
   deliberately NOT drafted (middle path); flag if you want the
   general shape sketched now.

On approval (with any amendments), W3 charters go out per-handler
with this note as the postcondition contract.
