# Layer C — the round induction, checker implication, and T1 assembly (design v2)

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
glue + (dispatch glue + landed handler equation(s)). DEPTH-2 VERDICT
IN (U16's sC×MsgHeartbeat dress rehearsal): pure assembly, ~linear
cost, census-exact — layer C adds exactly one more ring of the same
shape. The checker's own span is subject code — it gets equations in
the same pattern (further-consumers: the checker is one more customer
of the machinery, not a special case).

**R-FORM REFINEMENT (U16 flag, folded in — binding for C1):** under
the literal route the round lemma's honest premise is
**fixture-family membership with absState as readout**:
`R σ N := σ ∈ Fam ∧ absRead σ = N`, where `Fam` is the twin-shaped
state family and each round lemma's conclusion carries `σ' ∈ Fam`
(closure). This is simulation over an inductive invariant — still
the classic refinement-mapping shape, with membership seeded by the
start link-pin and preserved by every round kind. C1's statement
work is exactly: pin `Fam`'s definition (the fixture-pack vocabulary
already shipping in every equation) and prove the seed.

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

- **A1 — VERDICT IN (U15, 2026-08-25): statement forms COMPOSE
  cleanly** (seam configs/heaps line up measured; window links are
  continuation-bottom parametric; no statement redesign needed). The
  refuted half is the INSTRUMENT: a mid-run relocated sub-span
  yields its post-state only relationally (`stepFnIter_sim` carries
  lossy `FrameSim`, no heap-completeness clause), so a landed
  equation cannot be consumed as a sub-proof mid-walk. ROUTE POLICY
  ([AGENT], from the verdict): (i) wave 3 and the C-ladder's round
  lemmas proceed on **literal per-arm/per-round window chains** —
  each round-kind's span is FIXED CODE, so the lemma is proved once
  over symbolic state by a bounded literal walk (~50-110 s at
  measured rates; the induction composes LEMMAS at absState level,
  which is exactly what the relational statements give — no mid-walk
  resume ever needed on this route); (ii) the principled instrument
  repair — **completeness-strengthened FrameSim** (footprint/
  locality completeness; Yang–O'Hearn lineage; U15's route (a)) —
  is commissioned as a probe-first design slice with a measured
  go/no-go: PROBE ANSWERED (U16): completeness alone is
  insufficient — the payoff needs a C1 completeness clause PLUS a C2
  insertion-point shape clause; ≈2 units nominal, 3 at risk =
  borderline-over → **STAY LITERAL**, commission C1+C2 together only
  if/when the MsgApp-arm cost trigger (U15's ledger row) fires. Handler equations stay load-bearing
  either way: they are the semantic content, the composition map's
  vocabulary, and the validation set for the literal chains.
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


## 8. C1 GATE OUTCOME — v2 REVISION (2026-08-26, [AGENT]; verdict block
in the arc-4 log's U18 entry, evidence-anchored there)

The gate fired as designed. Verdicts: A1 PASS-with-trigger, A2 REFINE,
A3 PASS (absTwinRead v0 shipped), A4 KILL (precisely characterized),
plus a census headline outside the assumption set. The three
coordinator decisions, made now and binding for the C-ladder:

**D1 (A1 trigger fired → the instrument is commissioned).** Real
rounds are 7.7k–34k steps; naive kernel replay is measured-dead past
~1,400-step chunks (41 GB, term growth); 12 of 28 deliver rounds are
MsgApp-family re-walking Hae-scale spans. The FrameSim C1+C2
completeness instrument (U16 probe: ≈2 units nominal, 3 at risk;
Yang–O'Hearn locality lineage) is COMMISSIONED as the first C-ladder
unit — it converts round lemmas from 5–15-min mirror chains into
modular compositions that consume the landed handler equations.
Budget guard adopted ladder-wide: no naive kernel replay past
300-step chunks; mirror route or an explicit chunk-cost quote in any
round-lemma plan.

**D2 — REVISED 2026-08-26 ([USER]-endorsed direction): THE FAMILY
ROUTE (b′).** The invariant layer is lifted to an explicit
OBLIGATION SIGNATURE — the per-transition obligations already
implicit in T3's RefinedProofStructure (terms monotone; one vote per
term; leader-only append in own term; commit only at
quorum-certified indexes; truncation only on conflict; …) become the
family interface: the invariant superstructure is proved FROM the
signature, and each dialect discharges the obligations (Verdi
trivially; etcd's specRound by its own guards — the noop entry is an
instance of leader-append, commit-via-heartbeat satisfies
quorum-certified commit). This is "generalizing Verdi along all the
degrees of freedom available" ([USER]) — the protocol-level analog
of the two-bounds doctrine, and it amortizes over S2/S3, T2's
num_parties, and future dialect variations (prevote, learners).
Vacuity discipline: every obligation must be dischargeable by BOTH
dialects with visibly different implementations. Empirical gate
(SC1, running): whether arc-3's ported proofs factor through the
obligations or unfold concrete handlers — PORTS/ADAPTS/NEW decides
b′'s real cost. NAMED FALLBACK if the signature refuses to factor:
the patched-subject stepping stone ([USER]-proposed) — a
Verdi-dialect twin variant proved end-to-end first; recorded with
its honest cost caveat: layer-B/C artifacts are SUBJECT-EXACT
(literal chains), so the equation ladder forks rather than
transfers; only the generic kit carries. Original D2 text (plain
native re-derivation for S1) is subsumed by b′ as its degenerate
single-dialect case. Three mismatch axes are theorem-grounded: commit-advance
without new entries has NO Verdi-lattice image (and is reachable and
essential); the election noop entry exits Verdi's reachable set at
the first election; the package seam. Decision: the S1 leaf's
invariant (one-leader-per-term at the etcd-abstract level) is
RE-DERIVED NATIVELY over specRound, reusing T3's proof STRUCTURE as
the template (the lattice stays landed as the spec-level result and
the structural guide — reuse of proof structure is the classic; no
VerdiCompat build-wiring is needed on this route, mooting axis
(iii)). The (a)-vs-(b) decision for S2/S3 is deferred to their wave,
per the gate's own recommendation.

**D3 (the reachability headline → the arm ladder re-targets).** The
heartbeat round-kind and the Prop forward/drop arms are unreachable
under every stream (the driver never ticks; node 1 is leader when
quiescent). The four landed dispatch-arm equations are T1-VACUOUS —
they retain machinery/validation value (their vacuity is stated in
their docstrings; nothing is silently re-labeled), and the wave-3
lesson is recorded: REACHABILITY IS PART OF THE CENSUS from now on —
every future arm/round unit states its target's reachability
evidence before building. The reachable set C2+ must cover: MsgVote,
MsgVoteResp, MsgApp families, MsgAppResp families, the storage-resp
arms, campaign, propose-accept.

**D4 — THE MODE SHIFT ([USER]-prompted, 2026-08-26): the equation
layer generalizes.** The literal-chain mode (step-exact statements,
generated fixture literals) is reclassified as what the doctrine
already calls it: a tolerated scaffold. Once C2a's instrument lands
(mid-derivation relational consumption — the missing joint), the
sanctioned mode for ALL NEW equations becomes STRUCTURAL COMPOSITION:
symbolic execution composed over code structure (per-statement /
per-call, cost scaling with program SIZE not step count; TableExt +
the transport family + the lens + the C2b loop-invariant lemmas are
the existing pieces), fixtures as symbolic preconditions, conclusions
as completion-with-bound rather than exact fuel counts. The timing is
the reachability finding's gift: the reachable equation set (MsgApp/
MsgAppResp ×18 rounds, storage arms, the harvest ring) is mostly
UNBUILT — the mode shifts before the big wave, not after. The landed
literal equations are RE-ROLED as the compositional prover's
validation corpus (known-true instances), not load-bearing inputs.
Inherent-anchoring note: T1 is about the pinned wire — the pin stays;
the method and statement forms generalize. This also collapses the
patched-subject fallback's fork cost (structural artifacts transfer
across subject edits that preserve code shape). Lineage: this IS the
classics' own trajectory — compositional program logic over
per-instruction reasoning.

**The re-targeted ladder (replaces §6):**
- **C2a**: the FrameSim completeness instrument (D1) — C1+C2 clauses,
  probe-first execution per U16's sizing, hard stop at 3 units.
- **C2b**: the driver-loop SYMBOLIC-NET lemmas (the |net|-dependent
  glue: slice-walk loop invariants — classic, Go-general kit
  material) + the storage-resp arm equations.
- **C2c**: the harvest-ring (Ready-cycle) equations — 9–14k
  steps/round, no equations today, larger than the delivered arm in
  every round.
- **C2d**: the first REACHABLE round lemma (no-op arm round or
  MsgVote round) as the instrument's first full consumer.
- **C3**: induction skeleton + the NATIVE S1 leaf (D2) + the seed
  link-pin via Arc-2-style reflection (the 81k-step/171-choice init
  is not naively replayable — the census priced it).
- **C4**: remaining reachable round kinds (the MsgApp/MsgAppResp
  families dominate — 18 of 28 rounds).
- **C5**: T1 assembly + readout + the round-replay corollary (A5
  re-priced only after C2a lands). Judge + milestone audit here.
- **C6**: T2.

**Calibration note**: the refutations consume the optimism margin —
P-2026-08-25's T1 ~1.5–2 weeks moves toward its upper bound; the
2.5–4-week T1+T2 window stands.
