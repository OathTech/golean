# Layer C — the round induction, checker implication, and T1 assembly (design v1)

Campaign coordinator note, 2026-08-25, [AGENT] (drafted at the wave-2→3
boundary; to be CONTACT-TESTED by the layer-C unit per the U1 lesson —
§5's assumptions are falsifiable on purpose and each names its
kill-point). Inputs: the seam design §2C/§4c (the simulation-induction
frame and its lineage), the equation ledger at U14 (15 families +
From-symbolic form; handleAppendEntries closed), **the dispatch
composition map (U14, the direct input)**, the T3 lattice on main
(`VerdiCompat/`), the round-replay retirement condition ([USER]
2026-08-24), and OQ-D (checker-implication scoping).

## 1. What is being assembled

`AgreementT1`: every completing `twinRun` returns 0 at values[0] — i.e.
the in-program checker's `violations` never increments on any choice
stream. Layer C turns the per-handler/per-arm equations (B) plus the
abstraction function (A) into: (i) a ROUND LEMMA, (ii) an INDUCTION
over rounds carrying the T3 invariants, (iii) CHECKER-IMPLICATION
leaves, (iv) the T1 readout, and (v) the round-replay corollary
(CompletionWitness) — one mechanism, two readouts.

## 2. The round lemma (the layer's one new statement form)

The driver's loop body per round r: choose action (deliver-one /
propose / campaign via the mapIter choice site), route through a
dispatch arm, run the handler(s), harvest sends, run the checker.
Target form, in the simulation vocabulary (§4c):

> from any σ at the loop head with `absState σ = some N` and round
> choices π: the run reaches the next loop head at σ' with
> `absState σ' = some (specRound N π)` and checker-delta = the spec
> checker predicate's delta at (N, π).

Composed per the U14 map: a round = driver glue + one dispatch arm =
glue + (dispatch glue + landed handler equation(s)). U15 is proving
the two inner composition depths NOW (sF×Hh, then sC×bF+Hh); layer C
adds exactly one more ring (driver glue + checker span). The checker's
own span is subject code — it gets equations in the same pattern
(further-consumers: the checker is one more customer of the
machinery, not a special case).

## 3. The induction and the invariant carry

Induction over the round sequence: `R σ₀ N₀` at the seeded start
(kernel-checked once, the U12 link-pin pattern); the round lemma steps
the pair; the T3 `refined_raft_net_invariant` instances hold along the
abstract trace by their own (already-proved) preservation over
specRound-decomposed steps. OBLIGATION TO VERIFY EARLY: specRound as
composed from the ported handlers must match the T3 lattice's net-step
decomposition (they were both built from the same Verdi port, but the
match must be THEOREM, not provenance — a small adapter lemma per
action kind is the expected shape; a mismatch is a design finding, not
something to shim per-invariant).

## 4. Checker-implication leaves (OQ-D resolved: S1 first)

Per-check, small, abstract-level: S1's leaderOf-map disagreement
branch is unreachable given `one_leader_per_term` (election safety).
S2/S3 (applied-entry agreement) consume `candidate_entries` +
log-matching + state-machine safety — second wave, same shape. Each
leaf: spec-invariant ⇒ the checker predicate computes false-delta,
transferred through absState (property transfer through a refinement
mapping — the classic; no new mechanism).

## 5. Falsifiable cost assumptions (each with its kill-point)

- **A1 (being tested by U15)**: landed equation statements compose
  across dispatch glue at ≤ glue-window cost. KILL: statement-form
  redesign of layer B's conclusions BEFORE any layer-C unit starts.
- **A2**: the driver's per-round span outside dispatch (loop head,
  action choice, harvest, checker) is walkable in the census pattern
  — expect one census unit; the mapIter choice quantifies per §4b.
  KILL: a driver-span decomposition unit precedes the round lemma.
- **A3**: absState at round boundaries is lens-cheap (the U10/U12
  evidence says yes at handler granularity). KILL: reader
  consolidation lemmas first.
- **A4**: the specRound↔lattice-net-step adapter lemmas are small
  (§3). KILL: this is the one assumption whose failure reshapes the
  design — if the decompositions genuinely differ, the adapter layer
  becomes its own unit ladder and the estimate moves.
- **A5**: the round-replay corollary is ~100 round-lemma
  applications at recorded choices + arithmetic (certificate replay).
  Tested only after the round lemma exists; no kill, only cost.

## 6. Proposed unit ladder

- **C1**: driver-span census + the round-lemma STATEMENT (form only,
  witnessed on the heartbeat round) + the A4 adapter probe. The
  design gate: C1's verdict on A1-A4 revises this note before C2.
- **C2**: the first full round lemma (heartbeat round, both roles).
- **C3**: the induction skeleton + the S1 checker-implication leaf +
  the seeded-start link pin.
- **C4**: remaining round kinds (propose, campaign, drop arms) — by
  then pure assembly if A1/A2 held.
- **C5**: T1 ASSEMBLY + the first-order readout corollary (the
  statement-TCB gate's shape) + the round-replay corollary
  (CompletionWitness). Judge + milestone audit at this boundary.
- **C6**: T2 opens (num_parties generalization over the same frame).

## 7. Lineage (per the doctrine)

Simulation induction / refinement mapping (Abadi–Lamport; §4c's frame
unchanged); property transfer through the mapping (classic); the
corollary is certificate replay at round granularity (the [USER]
retirement condition's named mechanism). No new mechanism class is
proposed by this design; anything C1 discovers that cannot be mapped
gets the extra-scrutiny treatment before shipping.
