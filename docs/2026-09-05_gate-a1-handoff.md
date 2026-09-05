# Gate A1 handoff

[AGENT], 2026-09-05. User authorized Gate A1 and pointed to the archived
GoLean reasoning experiments and the sibling Cerberus logic. Branch
`gate-a1-contract`, base `79019a74c1e1c1418293d380d1fcfbd9ae489980`.

**Implementation complete; adversarial review passed after a gate fix.**
[USER] authorized landing on main on 2026-09-05: “Great, can we land this
on main? Where should it live?” This record accompanies that landing.
No interpreter, frontend, corpus, baseline or default-gate change.

Read `docs/2026-09-05_gate-a1-contract.md` for the decisions, theorem scope,
reference revisions and open obligations. Reproduce with
`bash spikes/gate-a1/check`. Final successful transcript and negative axiom
gate regressions are in `docs/evidence/2026-09-05_gate-a1-contract/`.
Read `docs/2026-09-05_gate-a1-review-and-next-phase.md` for the review,
dispositions, and proposed integration/task sequence. One medium-severity
gate omission was fixed and independently re-reviewed; no false theorem or
driver-bridge discrepancy was found. Final gate: core/spike builds pass,
529 constants audited, three poisoned imports rejected as intended.

Delivered: kernel-checked counterexamples; counted sequential bridge; exact
output/detector/choice/fuel pool trace; whole-program entry/readout and
observation bridges; bare Iris Language and a complete recovery example;
print-before-panic program proof; independent package gate and axiom checks.

General typed admission, refusal freedom, context composition, Iris heap
resources, general Iris-to-program adequacy and concurrent Go adequacy remain
open, separately named in the decision note. The full-program bridge retains
`runProgramSetupM` as an executable premise, not a static typing theorem.

The earlier assertion that a representation change would deliver generic
context laws is refuted; the thin adapter works against today's machine.
Recommended first follow-up: promote the semantics-owned contracts as an
experimental facade, then A2 actual entry/call/defer/recover and result
readout. Scope typed admission separately as A3; keep the package green
through B7/C1. These are recommendations, not new
[USER] rulings or master-plan amendments.

The experiment lives under `spikes/gate-a1/`; its durable handoff, decisions,
review and evidence live under `docs/`. The README and master-plan status
link to it. Promotion into GoCore and the next-phase proposals are separate
follow-up work. Push has not been authorized.

Build note: GitHub dependency update returned proxy 403. Used independent
local copies of the archived exact-pinned dependencies and build caches;
portable git pins remain in the package manifest. No sibling source
or shared build directory was modified. Normal core build and fresh spike
elaboration passed; no new full differential run is claimed.
