# The flexibility redesign — exec-level pass (2026-08-26)

> **TRACKED COPY (arc-4 landing fix round, F6).** Source: the campaign
> worktree's `docs/2026-08-26_campaign-flexibility-redesign.md` @
> raft-proof-campaign (its §8 designates this note THE plan of record;
> the arc-4 landing audit found it cited by name from landed proof
> modules — NativeS1Chain, NativeS1CheckerLeaf, GoLeanProofsCorpus —
> while absent from the branch; this copy closes that doc-of-record
> break).

[USER]-directed (goal unset for this pass): "This is a proof search,
let's build the most flexible pieces and then there's the best chance
they fit together (implementation, proof, automation)." Coordinator
exec review + redesign, [AGENT] throughout; supersedes the layer-C
note's §8 LADDER (the decisions D1–D4 stand and are absorbed here as
interface instances). Context: two [USER] grind-smells found
abstraction gaps the unit-level insight test missed (the wave; the
literal chains); root cause named in the log — goal over-focus: every
unit optimized its charter, no function reviewed the ladder's SHAPE.
This note is that function, run once fully; §6 makes it standing.

## 1. The principle: interfaces, not chains

The campaign to date proves a CHAIN (interpreter → equations → rounds
→ induction ⟷ lattice → leaves). A chain has one meeting point; any
mismatch is global — A4 demonstrated this exactly. The flexible form
is an INTERFACE STACK: at each layer an explicit interface with ≥2
plausible instances per side, so the meeting point MOVES when
something resists. Flexibility is bought with statement work and
carries a vacuity risk (an interface only one instance satisfies is a
chain wearing a costume) — every interface below has a named vacuity
check and a measurement gate before commitment.

## 2. Asset inventory by degrees of freedom

- **Bedrock (general over all Go, maximal freedom):** GoCore + the
  differential corpus; FastEval + ctx + the transfer/bridge theorems;
  the fast replay harness. Nothing here changes.
- **General mechanisms (compose with anything; underexploited):** the
  WP kit; Sym/TableExt (delegating symbolic stepper); the transport
  family (pick/spill/in-place/branch); the lens; the frame layer
  (completeness in flight = C2a). The campaign has been using these
  to manufacture literal artifacts; the redesign points them at
  compositional ones.
- **General recipes aimed at the literal mode (re-aim):** the
  fixture generators/printers (16 consumers), the census tooling,
  StaticCells link-pin pattern.
- **Proved but axis-locked (generalize via interface 1):** the T3
  lattice; its RefinedProofStructure is the latent signature.
- **Subject-exact scaffolds (re-roled, not load-bearing):** the 20
  equation statements → the compositional prover's validation corpus.
- **Correctly locked (the trust story — do not generalize):** the
  pinned wire, the statement-TCB layer, the differential oracle.

## 3. The interface stack

**I1 — the obligation signature (spec ⟷ dialect).** T3's
per-transition obligations made explicit; invariant superstructure
proved FROM the signature; dialects discharge it (Verdi trivially,
etcd's specRound via its guards). Instances: Verdi, etcd, future
prevote/learners; n-generic from the start so T2 is a projection.
Vacuity check: every obligation dischargeable by ≥2 dialects with
different implementations. GATE: SC1's PORTS/ADAPTS/NEW residue count
(running). Fallback if it refuses to factor: the patched-subject
stepping stone (recorded, with its fork-cost caveat — a caveat the
D4 prover itself shrinks).

**I2 — the compositional prover (code ⟷ equations).** Structural
symbolic execution over code shape: per-statement/per-call
composition on the existing mechanisms; cost scales with program
SIZE; fixtures become symbolic preconditions; conclusions become
bounded-completion (no exact fuel counts in statements). Instances:
handlers, the checker, driver glue, storage arms, the harvest ring —
and edited subjects (fork cost collapses). Vacuity check: the 20
literal equations re-derived as instances (the validation corpus is
the regression suite for the prover). GATE: C2a's instrument
(running, 3-unit stop) — the mid-derivation relational-consumption
joint is its prerequisite. SANCTIONED-MODE CHANGE EFFECTIVE NOW: no
new literal-mode equations, including "cheap" ones; work needing
equations before the prover exists waits or carries an explicit
justification.

**I3 — configuration-parameterized statements (statement ⟷
deployment).** The R-form's `Fam` is parameterized at definition time
by the driver configuration: (num_parties, message vocabulary,
tick/propose/campaign policy). T1 = the instance at (3, quiet,
single-proposer); T2 = the ∀n projection; reachability = a COMPUTED
property of the parameter (never again a census rediscovery).
Vacuity check: at least the T1 and one perturbed configuration
instantiate. GATE: cheap — folded into the Fam-pinning work the
C-ladder already owes; the parameterization is designed before Fam
is first written, not retrofitted.

**I4 — the abstract checker interface (checker ⟷ leaves).** One
theorem family: "the checker's span computes predicate P over
absState" (proved about the checker's code, by I2, once); the S1–S3
implication leaves then live entirely at spec level ("signature
invariants ⇒ ¬P-delta") — decoupled from checker bytes, reusable
across configurations by I3. Vacuity check: S1's leaf lands both
sides. GATE: folded into C3's leaf design; small.

## 4. What stops, what continues, what re-aims

- STOPS: literal-mode equation manufacture (all of it); heartbeat-
  family follow-ons (unreachable); any ladder step that assumes a
  single fixed meeting point.
- CONTINUES UNCHANGED: C2a (= I2's gate); SC1 (= I1's gate); the
  gates/judge/audit process; the differential instruments.
- RE-AIMS: generators → symbolic-precondition emission; census
  tooling → reachability-from-configuration (I3) + footprint-for-
  preconditions (I2); the T2 plan → I1+I3 projections rather than a
  separate generalization arc.

## 5. Sequencing (probe-gated, not a ladder)

Phase α (now): SC1 + C2a conclude → the I1 residue count and the I2
instrument verdict land → this note's §3 gates resolve → the meeting
point for T1 is CHOSEN from measured options (obligation-level if I1
factors; native-invariant-level otherwise; round-level vs
Ready-cycle-level per the harvest verdict).
Phase β: I2 prover assembly + its validation-corpus check; I3's Fam
parameterization lands with the first round-lemma statement; I4 with
the S1 leaf.
Phase γ: the T1 assembly over whichever meeting point α chose; the
round-replay corollary; T2 as projections.
No phase gets a unit count until its gate's numbers are in — the two
prior estimates both broke on unmeasured assumptions; estimates
resume at the α boundary.

## 6. The standing correction (process)

Goal over-focus is now a named failure mode with a named owner: at
every wave boundary the coordinator runs a METHOD review (is the way
we build the next wave still the right abstraction?) distinct from
the unit insight test — three questions, logged each time: what got
more locked this wave, what interface would unlock it, what did a
[USER] smell catch that the process should have. The exec function
this pass performed is that review; it does not wait for the next
smell.


## 7. MIDDLE-PATH CALIBRATION ([USER], 2026-08-26 — binding)

"There's some value in building slices, but what isn't reasonable is
building fragile and expensive one-offs. So we don't want to build
generality that we won't need." The operative test for every build
decision is TWO-AXIS: **cost × consumer count**. Cheap + disposable →
a concrete slice is correct. Expensive OR repeatedly consumed → the
general form is mandatory. Generality is built only against
DEMONSTRATED demand — an existing second consumer (the promotion
ledger's ≥2 rule, unchanged) or a MEASURED fragility/cost (the
literal chains at round scale were exactly this). Never speculative.
Applications to the standing plan:
- I3 scopes to the (num_parties, vocabulary) axes T1/T2 consume; no
  prevote/learner parameterization now.
- I4 scopes to the three checks that exist; no general checker theory.
- The family SMS superstructure (4-8 units) is DEFERRED post-T1,
  built when a second example demands it; T1 uses the 1.5-2-unit
  scoped ghost-history leaf.
- Consolidation is demand-driven via the ledger, not a flat budget;
  the wave-boundary method review checks calibration in BOTH
  directions (grind creep AND speculative generality).
- The second-target validation probe is a post-T1 [USER] decision,
  not part of DONE.


## 8. DOC-OF-RECORD HIERARCHY + POST-α ADDITIONS (2026-08-27
consistency pass, [USER]-directed)

**Hierarchy (one design of record per layer):** THIS NOTE = the plan
of record (interfaces, sequencing, §7 calibration). The layer-C note
= problem analysis + C1 gate history (banner added; ladders
superseded). The seam note (arc-4 lane, §4c) = arm/statement
conventions — RECONCILIATION QUEUED to the lane's next boundary (it
must cite this note; worker-owned until then). The iris reuse map (+2
addenda) = the Iris/lineage record. Lane logs = history, not plans.
The constitution = the ends, unchanged.

**Design contributions adopted since α (all [USER], full analyses in
the campaign log 2026-08-27):**
- The CHOICE-INVARIANCE LEMMA — latitude/semantics draw factoring;
  first consumer = the seed pin (replaces the reflection route);
  built inside the seed-pin unit, forward-compatible with:
- The SYMBOLIC SEMANTICS (choice-erasure layer; CompCert-memory-
  model lineage) — the POST-T1 consolidation centerpiece; not
  mid-endgame; ~/canonical forms built now AS its future state
  space.
- The REPRESENTATION-ENGINEERING heuristic (certified-AI lineage) —
  chartering question: "what representation makes these evaluable."
- The SMALL-AXIOMS correspondence (reuse map addendum 2) — I2's
  full lineage.

**Backlog item (2026-08-27, [USER]): THE COHERENCE AUDIT** — an
overall design-audit pass against the half-built-mechanisms risk.
Vehicle: a dedicated DESIGN-COHERENCE DIMENSION of the T1 milestone
audit (the constitution owes that audit anyway; this rides it).
Deliverable: ONE mechanism registry — every mechanism, its
completion state, scaffold tags, retirement conditions, its single
design-of-record pointer, and orphan/duplicate detection — replacing
today's scattered docstring tags. Scope includes the known scaffold
census: the copy-threaded S-induction (retirement condition
recorded), atom threading (retires into the symbolic semantics),
generated literal fixtures (validation-corpus role), goldenWire
maxRecDepth, the parked TwinSegs tree, the ∃-split extraction
residual, the Star/ReachRel duplication from the arc4b landing.
