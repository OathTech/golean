# The choice-erasure arc — plan of record (v1, 2026-08-27)

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

Duality, adopted as a working tool: a FAILED congruence lemma is a
constructive proof that the program observes that draw at that span
— the per-class lemmas double as an observability census with
proofs (this is precisely how SP1's probe found the timeout field).

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
- **The congruence (the arc's centerpiece):** per operation class
  C ∈ {spill, mapIter-canonicalized, masked-write, draw-free}:
  `σ₁ ~ σ₂ → stepClass C σ₁ d₁ ⇓ σ₁' → ∃ d₂ σ₂', stepClass C σ₂ d₂
  ⇓ σ₂' ∧ σ₁' ~ σ₂'` (span-level for the mapIter grade), composed
  over runs by bisimulation-up-to. Fail-closed clause: a draw site
  matching no class yields a named `UnclassifiedDraw` side
  condition — the theorem refuses rather than assumes.
- **Verdict invariance:** the harness readout (`values[i]` — or the
  `TwinVerdict.ofResult` decoder once S4 lands) is `SpanIso`-
  invariant. Small, but it is the theorem that makes erased
  verdicts mean concrete verdicts.
- **The composition (full T1's proof plan, none of it designated):**
  `AgreementT1` = for any stream: split it into (semantic picks,
  latitude draws); the congruence + seed-side invariance give
  run(stream) ~ run(canonical latitude, same picks); verdict
  invariance transfers the readout; the internal replay lemma
  (T1-replay — the round induction + pairing + leaves at canonical
  latitude) gives the canonical verdict = 0.

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

- **CE1 — the relational face:** S3's shape fix + `SpanIso` +
  `cequiv_iff_spanIso` + the pinhole regression witness. GATE: the
  iff proves without weakening either side; the SP1 census numbers
  reproduce through the repaired relation. (If the iff resists —
  e.g. the canonicalizer computes something SpanIso cannot state —
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
- **CE4 — composition + verdict invariance:** `ErasedStep`,
  bisimulation-up-to over runs, verdict invariance, and the
  init-span instance (discharging `SeedChoiceInvariance` — the
  named premise becomes a theorem here).
- **CE5 — the T1 composition dry run:** the full-T1 skeleton
  through replay ∘ lift, open obligations enumerated (expected:
  only the replay side's remaining rounds/pairing).

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
