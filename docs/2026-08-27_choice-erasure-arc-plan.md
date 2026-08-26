# The choice-erasure arc — plan of record (v2, 2026-08-27; professor-reviewed)

[AGENT] write-up of the [USER] design discussion (2026-08-27, the
basecamp review's B1/B2 resolution + the lifting-machinery
direction). Status: DRAFT pending a grumpy-professor light review,
then execution. Governing frames: the statement-TCB correction (the
designated layer is the harness contract only — nothing in this arc
is designated, ever), the B2 philosophy (untrusted abstractions
verified against the trusted semantics; useful, not complete), the
middle-path §7, and the compositionality test.

## 1. What this arc builds, in one paragraph

A **choice-erased semantics**: a second, relational step system over
the same machine states in which Go's latitude draws (allocation
capacities, canonicalized iteration orders, the masked timeout
field) are erased, while semantic choices (message delivery, the
driver's picks) remain explicit. Its validity is a THEOREM about the
concrete interpreter — a per-operation-class congruence packaged as
a bisimulation-up-to-~ₘ — so operating in the erased semantics never
loses fidelity: every erased fact is derivable about concrete runs.
It is partial by construction: erasure holds where proved, and an
unclassified draw site REFUSES (a named fail-closed side condition),
never absorbs. The arc exists for one demand-pulled consumer: full
`AgreementT1`'s ∀-stream quantifier, which composes as
(the internal replay lemma) ∘ (this arc's lift).

## 2. Why it cannot be an interpreter theorem (the observability
grading — the [USER] exchange, recorded)

The latitude draws are GENUINELY OBSERVABLE at the machine level, by
two-bounds design: a spill draw changes backing capacity in the
heap; map iteration order is program-observable (Go randomizes it
for that reason); the timeout draw persists into a field. An
unconditional "latitude erases" interpreter theorem is FALSE — and
if it were true it would mean the envelope had been narrowed (the
fidelity bug). Erasure is therefore a PER-PROGRAM CERTIFICATE OF
INSENSITIVITY, at three grades matching the SP1/C-census:

- **Unobserved** (spill capacities): states differ; the subject's
  executed code never inspects the difference. Congruence holds
  step-adjacent; ~ₘ's capacity-slack component encodes
  indistinguishable-to-this-program, not equal.
- **Observed-then-canonicalized** (mapIter): the code observes the
  order mid-span, then sorts/counts it away. Congruence is
  SPAN-level — intermediate states diverge and reconverge at the
  canonicalization point. This grade forces the up-to/spans shape.
- **Observable-but-unreachable** (the masked field): persisted,
  readable by real code (tick), structurally dead in this harness.
  Erasure conditional on the reachability argument; the VISIBLE
  mask is the honest encoding.
- **Promoted-to-pick (the FOURTH grade, professor-named):** the
  SAME operation class can be a semantic pick at one occurrence and
  latitude at another — mapIter IS the delivery-pick site at the
  driver loop and a canonicalized draw in the ring spans.
  Classification is PER-OCCURRENCE (per span), not per opcode; the
  occurrence-status decision procedure is part of the (picks,
  draws) split machinery and is named in CE4, never implicit.

Duality, adopted with the professor's standard: a failed PROOF
ATTEMPT is evidence; the census entry is a PROOF only when it
carries the counterexample pair (two resolutions, distinguishable
readout) — SP1's timeout finding met that bar; future entries must
too.

## 3. The construction

- **The relation face first (prerequisite = shape-fix S3):**
  `CEquivM` gains cleanliness-in-relation (flags = [] conjoined —
  closing the flagged-flagged pinhole structurally) and its
  relational specification: `theorem cequiv_iff_spanIso : CEquivM m
  σ r σ' r' ↔ SpanIso m σ r σ' r'` where `SpanIso` is the
  ∃-bijection-on-reachable-spans relation respecting caps-up-to-
  slack, canonical map contents, and the mask. All induction in
  this arc runs on `SpanIso`, never on the normal-form checker
  (which becomes what it always was: the decision procedure).
- **The erased step:** `ErasedStep (pick : SemChoice) σ σ' : Prop`
  — some latitude resolution of the concrete step(s) from σ under
  `pick` lands `SpanIso`-equal to σ'. Naming note (recorded): NOT
  "twin semantics" (collides with the subject) and NOT `EStep`
  (taken by the abstract dialect); `ErasedStep`/`⇝E`.
- **The congruence (the arc's centerpiece — SIGNATURE CORRECTED
  per professor review):** per SITE (not per opcode), HETEROGENEOUS
  in taken path and draw count: cap slack means one class member
  spills (consuming draws) where another appends in place
  (consuming none), so `d₁ d₂ : List Draw` of possibly different
  lengths, and the matched steps may take different paths:
  `σ₁ ~ σ₂ → siteStep s σ₁ d₁ ⇓ σ₁' → ∃ d₂ σ₂', siteStep s σ₂ d₂
  ⇓ σ₂' ∧ σ₁' ~ σ₂'` (span-level for the canonicalized grade).
  Proved for ARBITRARY class members (not canonical-vs-other) — the
  symmetric form the fault-transfer corollary needs. Composed by
  bisimulation-up-to whose SOUNDNESS IS A DISCHARGED LEMMA
  (Pous–Sangiorgi compatibility for up-to-expansion — the
  span/stuttering matching demands it; lineage cited AND proved).
  Fail-closed: `UnclassifiedDraw` refusal + the SPAN-COVERAGE
  decomposition lemma (every step of the subject's trajectory lies
  in exactly one classified span, or the theorem refuses) — a real
  CE4 deliverable, not free.
- **FUEL IS NOT PRESERVED across the class (recorded):** spill
  resolutions change downstream control, so step counts and draw
  schedules diverge; a run may complete at fuel N under one
  resolution and exhaust under another. The lift promises
  EXISTENTIAL fuel on the canonical side, absorbed because replay
  is ∀-fuel; T1's conditioning on `.ok` keeps this benign. Never
  state the lift with equal fuel on both sides.
- **Verdict invariance (form corrected):** completion AND Result
  transfer, not terminal-state ~ alone:
  `run₁ = .ok r → ∃ fuel' ch' r', run₂ = .ok r' ∧ r'.values[0]? =
  r.values[0]?`. MOVED to CE1/CE2 (the professor's reorder): it is
  SpanIso's first consumer and the cheap smoke test of whether the
  relation's shape fights its clients.
- **The composition (full T1's proof plan — THE PICK-ALIGNMENT
  SEAM now owned, per professor Q3):** "same picks" is not
  well-formed positionally — pick-hood is a function of the
  TRAJECTORY, and the two runs consume different draw schedules.
  Therefore: (a) the bisimulation relation itself carries
  pick-alignment (`SpanIso ∧ equal consumed-pick cursors`) — a
  component of the relation, established in CE4, with the
  stream-split DEFINED as a function of the run; (b) the
  REIFICATION lemma (named CE4 line item): the lifted canonical run
  reifies into an actual `Choices` stream (canonical draws
  interleaved with the aligned picks — constructive from the
  per-step ∃) because the replay lemma consumes a concrete
  `twinRun`; (c) verdict invariance (above) transfers the readout.
  Then AgreementT1 = lift ∘ reify ∘ replay. Without (a) it does
  not compose at all — the professor's words, adopted as the CE4
  gate.

## 3b. SUB-PROGRAM MODE-SWITCHING ([USER] refinement, 2026-08-27)

The erased semantics applies at the SUB-PROGRAM level: derivations
may switch freely between the choice-sensitive and choice-erased
semantics per span, localizing the most complex reasoning. This
adds to §3:
- **Mixed-chain composition lemmas** (CE4's real deliverable, not
  whole-run-only): switch-IN (a concrete state enters an erased
  segment as its own class representative — free) and switch-OUT
  (an erased segment's conclusion holds for every representative;
  a following concrete segment picks any one, carrying ~ into its
  premise). Boundaries compose at any cut point — the same
  compositional role along the CHOICE axis that span_consume gives
  along the HEAP axis; the two localizations are orthogonal and
  stack (an erased span may be frame-placed; a framed span may run
  erased).
- **Statement hygiene**: a mixed chain's conclusion is exact on
  concrete segments and up-to-~ on erased segments; the statement
  formers carry the mode so nothing silently strengthens a ~ into
  an =.
- **The practical payoff** ([USER]): spill-heavy spans (the harvest
  ring) run erased — one derivation for all capacities — while
  delivery picks and any unclassified site stay concrete; the
  round wave's per-instance cost drops accordingly, and the most
  complex reasoning (the canonicalized grade's diverge-reconverge)
  is PAID ONCE per span class, not per round.

## 4. What this arc is NOT

- NOT statement-layer: nothing here is designated, enters
  Challenge's closure, or touches the TCB. The designated layer
  remains the harness contract: `AgreementT1` (pinned, untouched)
  and the NEVER-FAULTS statement (drafted separately for [USER]
  designation; not this arc's deliverable, though this arc's
  machinery will serve its proof too).
- NOT complete: unclassified draw sites refuse; classes are grown
  by the consume-on-demand process with each class's congruence
  lemma as its admission ticket.
- NOT the full symbolic semantics: no new state representation, no
  packaging as a standalone layer (that remains the post-T1
  consolidation); this is its erased HALF, demand-pulled, built so
  the later packaging is a re-organization rather than new proofs.

## 5. Unit ladder (probe-gated per standing practice)

- **CE1 — the relational face (GATE PRE-ADJUSTED per professor
  Q4):** S3's shape fix + `SpanIso` + the iff IN ITS PROVABLE FORM:
  `Clean ∧ CEquivM ↔ Clean ∧ SpanIso` on well-formed states —
  cleanliness does quantifier work (deep-value caps, zero-like
  trimmed tails) and is EXPLICIT on both sides; sortability/
  no-duplicate-keys enter as well-formedness premises (reachable
  states satisfy them). HARD CONSTRAINT: SpanIso must NOT quote the
  canonicalizer (no collectFix reference — the cap-slack window
  characterized relationally, ∃-quantified over reachable handles);
  if it does, the relational specification is the checker restated
  and scoff 3 reinstates. Plus verdict invariance (moved here) +
  the pinhole regression witness. (If even the adjusted iff resists —
  that finding reshapes the arc before anything builds on it.)
- **CE2 — the per-class congruence, easiest grade first:** the
  draw-free and spill classes (step-adjacent congruence), witnessed
  on a real span with two latitude resolutions. GATE: the spill
  congruence discharges on the ring span's censused draws.
- **CE3 — the canonicalized grade:** the mapIter span-level
  congruence (diverge-reconverge across a canonicalization point) —
  the hardest single piece; probe the reconvergence-point
  characterization before building. The masked grade rides the
  reachability argument (already on the record from SP1).
- **CE4 — composition (the arc's load-bearing unit, scope per the
  review):** `ErasedStep`; the up-to SOUNDNESS lemma; the
  SPAN-COVERAGE decomposition; the pick-alignment component in the
  bisimulation relation + the occurrence-status decision procedure
  (the fourth grade); the STREAM-SPLIT + REIFICATION lemma; the
  FAULT-TRANSFER corollary (σ₁ ~ σ₂ → faults-under-some-resolution
  transfers — nearly free given the arbitrary-members congruence;
  shipped here so never-faults' proof never reopens the
  bisimulation); the init-span instance (SeedChoiceInvariance
  becomes a theorem).
- **CE5 — the T1 composition UPDATE (half a unit, per the review):**
  `agreementT1_skeleton` already typechecks — rewrite the O6
  obligation into the lift's actual interface and re-enumerate;
  no new build.

Each unit: witness-in-same-slice; [AGENT] + what-this-taught-us;
the observability-census duality logged whenever a congruence
fails. Estimates after CE1's gate (the iff is the unknown).

## 6. Sequencing with the standing waves

Wave α (unchanged, dispatches first): shape fixes S1-S4 (S3 = CE1's
prerequisite half), kills, the arc4d landing, legibility batch, the
never-faults draft. Wave β: CE1-CE3 + the heap quotient C1 + the
prover pilot (disjoint trees; the standing serialization rules).
CE4-CE5 join the round wave's tail in wave γ. The professor's
composition forecast is the watch-list: FamTrace's R-parameter
(S1) must land before new round instances; CE-machinery must never
appear in a designated statement's closure (checked by the existing
statement-TCB gate).
