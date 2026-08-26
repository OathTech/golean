# The basecamp design review — synthesis (2026-08-27)

[AGENT] synthesis of four briefs (RefinedC/Lithium reader; BRiCk
reader; the brick-wp/our-stack retrospective; the grumpy professor),
under the [USER] four-goal frame (goal-achieving proof; reusable
machinery; legible machinery; tried-and-true design) and the [USER]
compositionality test (every spec form names its frame story —
context set + non-disturbance — in its layer's native vocabulary).
Inputs are on main or in the campaign log; this note is the design
of record for the post-basecamp phase, superseding the flexibility
redesign's sequencing (its §7 middle-path calibration and §6 method
review REMAIN binding).

## 0. The verdict, synthesized

The professor's summary is the review's: "two well-built piers and
no bridge" — the bottom layer (interpreter, statement TCB) and the
top layer (obligation-parametric invariance) pass a hostile expert's
seminar as-is; the middle (where concrete meets abstract) is
honest-but-unshaped, and its three load-bearing definitions were
shaped by what the generator could emit, not what the theorem needs.
The retrospective's verdict composes with it: the stack fails on
WAYFINDING, not tangled dependencies. Neither is a ball of mud; both
are one focused wave from clean.

## 1. IMMEDIATE SHAPE FIXES (before ANY new round instance — each
hours-to-a-unit, each prevents a five-module migration)

- **S1: `FamTrace` gains the pairing parameter** (professor scoff 1):
  `R : ExecState → SNet → Prop` as a parameter with an `hpair` clause
  in `cons`; instantiate `R := fun _ _ => True` today — every landed
  theorem re-proves verbatim; O5b lands by instantiation, not
  migration. The one-parameter version of Abadi–Lamport done right.
- **S2: `RoundFam` gains the family-former slot** (scoff 4):
  `RoundFam (F : ExecState → Prop) σF := ∃ canon, F canon ∧ ∃ …
  FrameSim … canon σF`; today `F := (· = theLiteral)`; the I2 prover
  swaps in symbolic families without restating 28 instances.
- **S3: `CEquivM` cleanliness-in-relation + the pinhole** (scoff 3b):
  conjoin `flags = []` into the relation (flagged-flagged coincidence
  can no longer equate two exhausted states — the fail-open-by-
  forgetting pattern closed structurally); commit to the relational
  face (`cequiv_iff_spanIso`) as the O6 route's FIRST theorem, not an
  afterthought.
- **S4 (minor batch): fuel-literal wrapping** (`Normalizes` predicate
  + monotonicity), **the `TwinVerdict.ofResult` decoder** for the
  headline readout, the `sliceElems` name collision. Cheap, do with S1-S3.

## 2. THE TWO DESIGN DECISIONS ([USER] gates — recommendations below)

- **B1 — SUPERSEDED BY THE [USER] TCB CORRECTION (2026-08-27, campaign
  log): the designation-split proposal below was WRONG** — the
  designated layer is the harness contract only (AgreementT1 as
  pinned + the never-faults statement, drafted for [USER]
  designation); T1-replay is an INTERNAL lemma, never designated;
  the lift is untrusted machinery, now chartered as its own arc
  (`docs/2026-08-27_choice-erasure-arc-plan.md`, v2,
  professor-reviewed). Original text retained below for the record:
- ~~B1: T1's ∀-stream story — the professor's stop-the-presses item.~~
  The ∀-stream burden (O6) currently ends in "post-T1 symbolic
  semantics or a [USER] statement-scoping call" — a proof plan with a
  hole where the hard part goes. RECOMMENDATION: **split the
  designation, commit the route**: designate `AgreementT1_replay`
  (all delivery orders at canonical latitude — provable on the
  landed machinery + the priced remaining work) as a MILESTONE
  theorem, keep `AgreementT1` (∀-stream) as THE END, and commit the
  O6 route now: the erased-half transport theory (bisimulation-up-to
  over the S3-repaired relational CEquiv) as a named arc, not a
  deferred hope. No statement is weakened; the gap between milestone
  and end is stated as a theorem gap, not prose.
- **B2: the O2 replay-mode decision (the retrospective's #1 debt).**
  RECOMMENDATION: **no more literal chains; build the judgment layer
  first.** The Lithium plan (below) subsumes the emitter: the ~28
  rounds become derivations of a typing-style judgment checked by a
  deterministic driver over Sym. The emitter route stays as the
  recorded fallback if the prover arc misses its gate (a measured
  go/no-go after its pilot, per the standing pattern).

## 3. THE PROVER ARC (the reasoning layer's target architecture —
RefinedC-shaped, BRiCk-instrumented, on our Sym substrate)

Adopted from the briefs, each with its source:
- **CPS judgments** (`equation args (T : result → Prop)`), rules as
  plain lemmas auto-lifted to a REGISTERED rule database (attribute +
  discrimination tree, not typeclass abuse — the reader's own Lean
  adaptation note), engine-blind content. [RefinedC §1]
- **One deterministic committed-choice driver** over the Sym layer:
  closed goal grammar, no backtracking (stated rationale adopted:
  determinism makes stuck states meaningful and traces replayable —
  agent-operation values), shelved pure side conditions discharged
  by a staged pure pipeline. [Lithium §2]
- **Sealed `UNSUPPORTED`/`ERROR` payload propositions** in the
  goals: every stuck state names its own cause; fail-closed
  (semantically False), locked against normalization. [BRiCk §3 —
  the highest-value/lowest-cost steal]
- **The escape ladder**, every rung's interface = the unchanged
  judgment: scoped pure tactic → hint → promoted rule → manual proof
  of the standard statement → declared-and-Audit-gated trust; rung
  usage mechanically logged. [RefinedC §3, strengthened per our
  provenance rules]
- **Span-structured JSON trace per obligation** (rule tried →
  outcome), one env var; the agent-enablement thesis: observability
  + registered extension points + incident-derived rules. [BRiCk §3-4]
- **Modality/context slot baked into the judgment format on day
  one** even if instantiated trivially (their hardest retrofit).
  [RefinedC §5]
- **The spec-form surface**: one-fact-per-clause builder grammar
  with auto-supplied runtime boilerplate (their SConstructor
  lesson); named binders preserved end-to-end. [BRiCk §2]
- GATE: a pilot (one handler equation re-derived as a judgment
  derivation, cost measured vs its literal twin) before the wave —
  the U1 lesson applied to our own new mechanism.

## 4. THE CONSOLIDATION WAVE (parallel with §3's early slices)

- **C1: the heap-equivalence quotient** (`Heap.Equiv` by lookup-
  extensionality; FrameSimS's shape clause restated as layout-free
  disjoint merge) — the professor's "single consolidation that
  retires three scoffs": the splice clause, the multi-splice need,
  interleaved prunes; unblocks O2b. The copy-threaded scaffold's
  retirement condition gets re-evaluated after (likely retirable).
- **C2: the kill list** (retrospective, importer-verified): the
  Arc-2 checkpoint cluster (kill/demote; zero real consumers; 350k-
  step cold-build tax; misleading docstring), the HandlerEq/
  AbsState-v1 pilot chain (tombstone citing its completed
  measurement), the TwinSegs park-closure record.
- **C3: ghost out of the `SNet` carrier** (scoff 5: history as a
  generic completion `HStep`, ghost rules attached to events, lifted
  once) + **the Verdi `ElectObligations` instance** (the I1 vacuity
  debt — the interface's second inhabitant) + the S23-A carrier
  bridge design (HNet↔SNet — priced by that design slice, not
  assumed).
- **C4: legibility** (retrospective's minimal set): the mechanism
  registry promoted to THE live on-main index (entry-point +
  read-first + placement columns; wave-boundary ownership); the 26
  corpus chains moved under `Specs/Raft/Corpus/`; the Sym design
  note copied to main; the four missing ledger rows; the paradox
  file started (`Paradoxes.lean` — rejected laws with refutations,
  BRiCk pattern); the spec rubric (principles.v, compositionality-
  test form) into worker briefs and the audit's claim-strength
  dimension; compiled-docs for the kit surface (later, with §3).

## 5. Sequencing (probe-gated)

Wave α (now): S1-S4 + C2 + C4 (cheap, unblocking) → wave β: C1 +
the prover pilot (§3 gate) + C3, with B1/B2 decided by [USER] before
β closes → wave γ: the round wave in the winning mode + O5b (by
instantiation) + O6's transport arc → assembly → T1-replay milestone
→ T1-full. Estimates resume after the prover pilot's measurement.

## 6. Lineage corrections (adopted from the professor's audit)

The transports' "path-condition splitting" label corrected to
single-step commutation at γ-images; FrameSimS's "completeness half
of locality" qualified (layout-dependence acknowledged; C1 is the
honest completion); ChoiceCanon's CompCert citation demoted to
goal-level until `cequiv_iff_spanIso` exists. The lineage discipline
itself validated: two of three inflated claims were caught by our
own audits pre-review.
