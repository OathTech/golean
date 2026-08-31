# The fidelity assessment: is GoLean legitimately good? (2026-08-31)

STATUS: DRAFT for [USER] sign-off. Nothing executes until then.

## Provenance and mandate

[USER] 2026-08-31 (Mike), post repo-split: make the semantics "the
absolutely best that it can be within the frame" — "an incredibly
faithful model of what Go code is supposed to do": at the lower end
it encompasses all the things real Go code does; at the upper end,
all the things the standard says Go code might do; "incredibly well
validated". This is a reset to roots after the reasoning detour.
The explicit mandate: **question every shortcut, including the ones
the current docs record as settled set-asides** — "we want to
question our assumptions". Reasoning work continues elsewhere; not
this branch's concern.

Everything below is [AGENT] plan design under that mandate.

## The claim, sharpened (what "legitimately good" must mean)

Four sub-claims, each of which the assessment must grade with
evidence, not vibes:

- **C1 — Feature totality.** Real Go programs in the modeled
  fragment run; the fragment BOUNDARY is deliberate, enumerated,
  and honest (a refusal is a recorded decision, never an accident).
  Today's frontier is visible in the baseline: 143 of the 172
  non-PASS rows are `frontend-export` refusals.
- **C2 — Lower-bound fidelity.** observed ⊆ modeled: no behavior a
  real Go implementation exhibits (for accepted programs) is
  outside the model. Today's evidence is ONE implementation at ONE
  version on ONE platform (gc go1.26.5, this box) — the
  simplifying-assumptions register's own entry #3 calls this out.
- **C3 — Upper-bound faithfulness.** modeled ⊆ permitted AND
  permitted ⊆ modeled at every latitude point: the machine neither
  invents behaviors the spec forbids nor silently pins away
  behaviors the spec allows. Today's evidence is the latitude
  census + per-row envelope arguments, with known pinned rows
  (gc-pins carrying re-envelope debts: E3/E5/E7) and known
  narrowed rows (B3 abort window, select-commit narrowing C7).
- **C4 — Validation credibility.** The evidence base would convince
  a hostile, competent outsider (the CH2O/Cerberus/CompCert-
  validation standard), not just us.

## Why a two-phase shape (assess THEN build)

The mandate is to question assumptions — so the plan must not bake
in the answers. Phase 1 produces the graded assessment and the
re-derived shortcut census; the work program (phase 3) is DERIVED
from it at a [USER] checkpoint, not pre-committed here. The
hypotheses in §Phase 3 are candidate findings stated up front for
honesty about where the coordinator's prior is — each one must
earn its place through phase 1 evidence.

## Phase 0 — instruments (½ session)

Fix the assessment's own ground rules before anyone grades
anything: the grading vocabulary (per claim: STRONG / ADEQUATE /
WEAK / ABSENT, each requiring named evidence); the shortcut-census
row format (what-is-assumed / original justification / does it
survive the new goal / KEEP-as-idealization vs REOPEN-as-debt vs
ESCALATE-to-[USER]); and the rule that a KEEP verdict requires a
fresh argument, not a citation to the old one — the mandate is
precisely that the old justifications are not self-certifying.

## Phase 1 — the assessment (parallel lanes, ~4-6 sessions)

### Lane A — the shortcut census (the mandate's core)

Enumerate and RE-DERIVE every recorded set-aside. Known
populations (the census must confirm completeness, not stop here):

- The doctrine's simplifying-assumptions register, all 7 entries —
  including the DISCHARGED ones (a discharge is also an assumption
  about what discharged it): #1 scheduling (residue: B3 abort
  window deferred, liveness/`Fair` tier open, sub-statement
  granularity open), #2 evaluation-order pins with the E3/E5/E7
  deviation debts "queued for re-envelope", #3 one-implementation
  evidence base, #4 SC-only + racy-programs-refused ("state-of-the-
  art-aligned, not a shortcut" — question exactly this, AND the
  refusal's own soundness: refusing racy programs is only honest if
  race detection is complete for accepted programs), #5
  registry-granularity residuals, #6 allocator quotient
  (CONDITIONAL on the pointer-equality observation surface — what
  guards the condition?), #7 unbounded memory ("standing
  idealization" — does it stay one under the new goal?).
- The latitude inventory's DEFERRED / NARROWED / out-of-scope /
  parked rows (B3, C7's deliberate narrowing, distributional facts
  "out of scope by declaration", the parked relocation arc, R14/U-3
  delegated-unknown precision extremes, …) — the census walks all
  ~1400 lines, not my recollection of them.
- The coverage ledger's non-green states: every `frontier(FR-n)`
  row (complex numbers FR-15 et al.), every named T-gap (T-1:
  legal-value pinning owed on literal grids), every D-caveat
  ("constant greens attest go/constant delegation, not GoCore
  arithmetic" — S3 audit's own words).
- The 143 `frontend-export` refusals, enumerated BY FEATURE with a
  disposition each (this is C1's boundary made explicit); the 17
  `lean-observation` + 9 `differential` + singleton rows likewise.
- BUGS.md (69 entries): which are open fidelity debts vs recorded
  latitude, and does the classification hold?
- TODO's owed rulings: the eight Q-rows, `nonterm=` under
  `engine=dedup`, the B3/U-1 trigger.
- The stdlib-shim policy (E5 lineage): injected hand-written models
  of stdlib functions — what validates each shim, and what bounds
  the set?
- Spec-truth campaign state: P2-P4 unfinished, covmap CIPs held for
  sign-off — what does incompleteness cost the coverage claim?
- Delegation as a class: parsing/typing wholly delegated to
  go/parser+go/types (grade-D rows). Question it as a shortcut:
  it is probably the RIGHT TCB choice, but the assessment must say
  what the claim then is (we model DYNAMIC semantics of programs
  gc's frontend accepts, static semantics by proxy) and what
  SpecTec-Go (the AST-level spec workstream) changes about it.

### Lane B — lower-bound audit (C2)

- The observation channel: what exactly does the differential
  compare (stdout/exit? what else?), and what real-Go observables
  are OUTSIDE it (pointer prints, timing, GC/finalizers, runtime
  introspection, error text)? Register #6's quotient is conditional
  on this surface — the audit maps the condition's edge.
- The oracle matrix: one gc version, one platform, one GOMAXPROCS.
  What would a version sweep (previous/next gc), a platform sweep
  (GOOS/GOARCH: int width, endianness), GOMAXPROCS>1, `-race`
  runs, and a second implementation (gccgo, tinygo — feasibility
  probe) each buy, and what have we measured about their cost?
- Corpus representativity: 2478 hand-written fixtures vs real-world
  Go. The parked `side/gofuzz` project: state, why parked, what a
  revival costs. Differential fuzzing (gosmith-class generators)
  as the scaling path for C2.
- The negative corpus's reach (390 compile-rejection rows): what
  static-semantics claim do they actually support under full
  delegation?

### Lane C — upper-bound audit (C3)

- Census completeness: what argues the latitude INVENTORY itself is
  complete against the spec + memory model + runtime docs? (The
  ledger's 158-row denominator helps; the audit checks the
  crosswalk.)
- Choice-tape coverage: for each census row, is the latitude
  DEMONIC in the machine (choice-driven), PINNED (gc-pin with a
  re-envelope debt), or ARGUED-AWAY (quotient/invariance theorem)?
  Produce the three-way table; every PINNED row is a standing
  debt under the new goal.
- The deviation-debt queue (E3/E5/E7 + hidden-dep-order): concrete
  re-envelope cost per row.
- Idealizations with teeth: unbounded memory (#7), total
  allocation, empty-heap starts — for each, the statement of what
  claims they would falsify if a consumer relied on them wrongly.

### Lane D — validation-apparatus audit (C4)

The apparatus itself as an object: differential methodology limits
(what a green 2478/2478 does and does not certify — cached vs
re-certified tiers, manifest attribution, the observation
surface), the certified-slow-tier mechanism, oracle-pin discipline,
gate coverage after the split (the restored frontend pins, what
else has no guard), fuzzing absence, and the evidence-directory
discipline (probes reproducible?).

### Lane E — the outsider standard (C4)

A professor-class review, full scope, no downscoping: "as a
semantics researcher, would I trust this as a model of Go, and
what would I demand before citing it?" — explicitly comparing
against the validation standards of CH2O, Cerberus, CompCert's
test-suite story, and the Go-semantics literature (Featherweight
Go, KGo/Gobra lineage, the plmm work the register cites). Their
brief includes the mandate verbatim: recorded set-asides are in
scope for challenge.

## Phase 2 — adversarial verification (~1-2 sessions)

Every KEEP verdict from the census gets an independent
devil's-advocate pass (the audit pattern that just caught the
check-golden mis-park): a reviewer whose only job is to break the
fresh justification. KEEPs that survive are recorded with their
new argument; the rest become REOPEN/ESCALATE.

## Phase 3 — synthesis: the state of the union + the work program

One report, [USER]-checkpointed before any building starts:

1. The four claims graded, with the evidence chain per grade.
2. The re-derived shortcut census (KEEP / REOPEN / ESCALATE), the
   ESCALATE items posed as concrete [USER] decisions.
3. The prioritized work program: REOPENs ordered by (risk to the
   bounds × cost), each with acceptance criteria and a named
   validation mechanism.

Candidate findings I expect the evidence to surface (stated as
PRIORS to be confirmed or killed, not conclusions): the
one-implementation/one-platform evidence base (register #3) as the
largest C2 gap; the 143-refusal frontier needing a feature ladder
(complex numbers and friends); fuzzing revival as the corpus-
representativity answer; the observation-surface map as the
precondition for several quotient discharges; the racy-program
refusal needing its detector-soundness argument; the pinned-
latitude rows (E3/E5/E7) as the C3 debt queue; stdlib-shim policy
needing a per-shim validation rule; spec-truth P2-P4 completion.

## Boundaries and gates

- This branch touches ASSESSMENT ARTIFACTS ONLY until the phase-3
  checkpoint: no machine changes, no gate changes, no baseline
  re-pins. (Probes that RUN things to measure are fine; probes
  that change tracked state are not.)
- [USER] gates: this plan's sign-off; the phase-3 report before
  the work program; every ESCALATE item.
- Workers Fable, reviewers Opus (lane E professor-class). The
  standing rules apply unchanged: capped builds, no pushes,
  [AGENT]/[USER] provenance, honest reporting.

## Cost estimate

Phase 0-2: roughly 6-9 sessions of lane work + synthesis. The work
program's cost is a phase-3 output, not guessable here.
