# Prior-art reading note: CH2O and Cerberus, with a JSCert sidebar (2026-08-17)

Status: P1 reading note for the spec-and-community truth campaign
(`docs/2026-08-17_spec-and-community-truth-campaign.md` §3, CH2O+Cerberus
cluster). Companion doctrine: `docs/2026-08-11_essence-of-go-doctrine.md`;
the comparison target is `docs/2026-08-11_latitude-inventory.md` §2.
SCOPE CORRECTION (pre-landing audit, 2026-08-17): this note compares
E1–E6 only; the inventory's §2 actually runs E1–E11 (E7 init order,
E8 multi-file order, E9 map iteration, E10 map-key retention, E11
runtime-check order). E7–E11 were trimmed without declaring it — now
declared; E11 matters for finding F1, see §3. Primary sources read: `deps/papers/ch2o-krebbers-thesis.pdf`
(Krebbers, *The C standard formalized in Coq*, Radboud 2015 — Chapters 1,
2, the §6.4 evaluation-order machinery, Chapters 10–11) and
`deps/papers/cerberus-pldi16.pdf` (Memarian, Matthiesen, Lingard,
Nienhuis, Chisnall, Watson, Sewell, *Into the Depths of C: Elaborating the
De Facto Standards*, PLDI 2016 — read in full). JSCert and the WG14 paper
trail are web-sourced and tagged `[web]` throughout. Extraction caveat:
no PDF tooling exists in this sandbox, so both papers were read through a
minimal scratch text extractor; ligatures and math notation are lossy,
so cites below are to **section numbers**, which survived cleanly, never
to page-exact quotes unless short and unambiguous.

## 1. CH2O: underspecification as a three-way split, evaluation order as redex nondeterminism

CH2O's first move is taxonomic, and it is the piece of their frame that
maps onto ours most directly. Thesis §2.1 splits the C11 standard's
deliberate looseness into three classes; §2.2 gives each its formal
treatment, stated as "folklore" but executed at unprecedented scale:

- **Implementation-defined behavior → parameterization.** The entire
  semantics is parameterized by an implementation environment (integer
  sizes, endianness); metatheory is proved for *all* environments, and
  concrete verification may instantiate or quantify (§2.2, §3.4, §9.4).
- **Unspecified behavior → nondeterminism.** A nondeterministic
  small-step operational semantics; evaluation order falls out of *redex
  selection* — evaluation contexts select any head redex in the whole
  expression, so every allowed order is a real execution (§2.2, §6.4).
- **Undefined behavior → absence of semantics.** Reduction to a special
  `undef` state; verifying a program means proving every reduction path
  avoids it (§2.2).

Two further commitments matter for us. First, §2.3 draws the line
between a *standard* semantics and a *compiler* semantics: CompCert
legitimately resolves unspecified and even undefined behavior to fixed
choices because its theorem quantifies over one compiler; a semantics
claiming C11-portability "has to take **all** unspecified and undefined
behavior into account". This is our two-bounds doctrine's upper-bound
half, stated in 2015 in C terms — and by §2.3's criterion, our E2–E5
pins currently make GoCore a compiler semantics on those axes, which is
exactly what the doctrine's "pins are scaffolding" clause already says.
The planned validation that CompCert C is an *instance* of CH2O
(§2.3, §11.2.2) is the same shape as our membership lane: the specific
implementation's behaviors ⊆ the portable model's.

Second, §1.5 ("Is CH2O really a formalization of C11?") is an honest
trust-argument template: standard text + defect reports + compiler
behavior studied; executable semantics (§6.8, proven sound and complete
against the operational one — completeness "complicated due to excessive
non-determinism", §1.4) used to compute behavior *sets* of example
programs, including examples from the standard text and defect reports;
three corresponding semantics (operational/executable/axiomatic) as
mutual cross-checks. Their "test the semantics on the standard's own
examples" is our campaign mechanism 4.2, pre-invented.

**The sequence-point machinery (§2.5.9, §6.4).** C makes unordered
evaluation dangerous in a way Go does not: an object modified twice (or
read after modification) between sequence points is *undefined*, not
merely order-dependent. CH2O implements this with a permission system:
the assignment head-reduction rule (Definition 6.4.1, rule 7) both
stores and *locks* the written address; any access to a locked object is
an unsafe redex (undefined behavior); sequence points (the `?:`, `,`
operators; before function calls; full-expression ends) unlock. Their
refinement over prior art is *locality*: unlike Ellison–Roșu's K
semantics, which releases all locks at any sequence point, CH2O releases
only the locks created by the subexpression containing the sequence
point — accepting "strictly more undefined behavior, but only in
artificial corner cases", in exchange for a metatheory local enough for
separation logic (§6.4, §8.4). Function calls in an expression do not
interleave — a call runs to completion when selected (§6.4's redex
classification plus the zipper focus, §1.4) — matching C11's
"indeterminately sequenced" function executions.

Related-work calibration the campaign should keep (§10.1): Gurevich &
Huggins (1993) modeled expression nondeterminism but *missed interleaved
orders* — `printf("a") + (printf("b") + printf("c"))` may print `bac`
under the standard and CH2O; a permutations-of-subtrees model misses it.
Norrish (1998) was the first to formalize nondeterminism + sequence
points, proved *confluence for sequence-point-free expressions* to make
reasoning tractable, and left "reasoning about arbitrary C expressions
as an open problem"; Krebbers notes his own confluence analogs fail.
This is a cost signal for our E3/E4/E5 re-envelope: the axiomatic story
over genuinely order-nondeterministic expressions is the hard part, and
CH2O only tamed it with the UB crutch (unsequenced conflict = illegal,
so the *legal* programs are near-deterministic per expression). Go
denies us that crutch — see §3 below.

**The escape valve we cannot copy (§2.6).** Where the standard is
ambiguous, CH2O "errs on the side of caution" by assigning undefined
behavior; where nondeterminism would explode (nondeterministic
representations of uninitialized bytes), it assigns undefined behavior
"which subsumes non-determinism". In C this is a *semantic* verdict that
keeps soundness: UB-freedom is already the client's proof obligation. Go
has no sequential UB, so our analog is the REFUSED class — a
tool-classification (visible red), never a semantic verdict. The
distinction is worth stating in the inventory's §0 preamble: C
formalizations can launder both ambiguity and combinatorial pain into
UB; we cannot, and that is honest-making but costs us the valve.

## 2. Cerberus: elaboration to Core, and de facto vs ISO as an empirical program

Cerberus's semantic architecture (§5.1) is factoring-by-elaboration: a
total, typed, compositional translation from a fully type-annotated C
AST into **Core**, a small typed call-by-value calculus, composed with a
Core operational semantics and a pluggable memory object model. The
motivating claim is that "many of the dynamic intricacies of C relate to
essentially compile-time phenomena, e.g. the pervasive implicit
coercions ... and the loose specification of expression evaluation
order" — so they are discharged in the elaboration, whose clauses sit
side-by-side with the ISO text they implement (Fig. 3 shows the
left-shift elaboration annotated clause-by-clause against C11 6.5.7 and
6.5p1–2). Undefined behavior is elaborated into explicit `undef()`
tests in the Core code (§5.4); a "sequencing monad" choice switches the
tool between exhaustive exploration of all allowed executions and
pseudorandom single paths (§5.1) — executable-as-test-oracle is a design
requirement, stated in the abstract.

**Evaluation order (§5.6)** gets the most refined vocabulary in any of
the surveyed efforts. Core has *five* sequencing forms: `unseq(e1..en)`
(arbitrary interleaving of the memory actions, subject to internal
constraints), `let weak` (only *positive* actions — value computations —
of e1 sequenced before e2; polarity annotations implement C11's
"value computation" vs "side effect" split), `let strong` (everything
sequenced), `let atomic` (postfix `++`/`--`'s read-write pair made an
atomic unit), and `indet`/`bound` (function bodies indeterminately
sequenced w.r.t. their context — either order, not interleaved — with a
Core-to-Core rewrite compiling `indet` away into explicit
nondeterministic choice `nd`). Unsequenced conflicting accesses form an
"unsequenced race" = UB, "and our semantics can detect all such
unsequenced races" on any allowed path in exhaustive mode (§5.4, §5.6).
The paper is explicit about the *purpose*: "the point of all this
expression-local nondeterminism is not to permit user-visible
nondeterminism, but rather to permit optimisation" (§5.6) — C's
committee kept the latitude for compilers; Go's spec kept its (smaller)
latitude for the same reason. Both are upper-bound texts written to
license implementations, which is why the too-wide direction has no
oracle in either language.

**The de-facto program (§1–§2)** is the paper's larger half and the part
the doctrine doc cites. Their Problem 1: the ISO standard, mainstream
compiler behavior, the assumptions in the deployed-code corpus, and the
assumptions in analysis tools are *four diverging de facto standards*.
Method: 85 sharply-posed questions about the pointer/memory design
space, 196 hand-written semantic test cases, experimental data (GCC and
Clang across versions and flags, the sanitizers, tis-interpreter), and
two practitioner surveys — 2013: 42 questions put to experts in person
over hours; 2015: 15 refined questions, 323 responses recruited via
gcc/llvmdev/cfe-dev/freebsd/xen lists and John Regehr's blog, with
respondent-expertise demographics reported. Headline tallies (§2): of 85
questions, **39 where the ISO standard is unclear, 27 where the de facto
standards are unclear, 27 with significant ISO-vs-de-facto differences**.
Two moves in §2 are directly reusable molds:

- **Q25 (relational comparison of pointers to different objects):** ISO
  prohibits; 60% of practitioners say it works, 33% know real code
  relying on it → the candidate model *permits* it. De facto evidence
  overriding ISO text, with the survey as the instrument.
- **Q2 (provenance-sensitive pointer equality):** GCC observed returning
  *inconsistent* answers for the same comparison depending on
  compilation-unit placement — "not a semantics that we would a priori
  choose", but "can be soundly modelled by making a nondeterministic
  choice at each such comparison". Observed-exotic-implementation-point
  → widen the envelope with a choice site, don't declare the compiler
  wrong. This is the exact mold for our E5 (gc's early store across the
  phase boundary).

Validation (§6): agreement with GCC on 556 tests (5 timeouts) of an
existing C-semantics suite, and on 316 of 400 Csmith-generated programs
(56 timeouts, 6 failures, plus 22 Csmith programs that don't terminate
under GCC — "the second Csmith bug we found"); the candidate de-facto
memory model, work-in-progress, gave intended behavior on only 9 of
their own much-harder de-facto tests, *reported as such*. A prototype
translation validator (`tvc`) proves, per tiny program, that Clang-IR
behaviors ⊆ Cerberus behaviors — the membership lane again, mechanized
per-program.

## 3. The E1–E6 comparison: their machinery against our census
(E7–E11 not compared — see the scope correction in the header)

The structural headline first: **Go's forced core covers C's worst
axis.** C's expression nondeterminism is dominated by unsequenced side
effects and interleaved/indeterminately-sequenced function calls; Go's
spec (§Order of evaluation) forces *all* function calls, method calls,
receives, and binary logical operations into lexical left-to-right
order. So the entire `unseq`-of-effectful-subtrees problem that drives
CH2O's locks and Cerberus's polarity machinery is class (c) FORCED for
us (inventory E1). Go's residual sequential latitude is confined to
*non-call operand events* — orders of indexing/deref/operand evaluation
around the ordered spine. Neither C effort has a mechanism we need for
E1; both would classify it as we do.

Per entry:

| Ours | Class today | CH2O's treatment of the analogous point | Cerberus's | Would their machinery classify us differently? |
|---|---|---|---|---|
| **E1** spec-ordered core | (c) FORCED | deterministic reduction rules; sequence points at the ordered constructs (§6.4/§6.5) | `let strong` / `let atomic` (§5.6) | No. Agreement all around; Go simply forces far more than C11 does. |
| **E2** call vs assignment-target operands | (b) PINNED to gc (call-first) | genuine nondeterminism via redex selection (§2.2, §6.4); a fixed order is what *CompCert* does, and §2.3 names that a compiler semantics, not a standard one | `unseq` of the operand evaluations (§5.6); the full order-set enumerated by the exhaustive driver | Yes, in name only: both would label the pin an implementation choice — which is precisely the doctrine's own "scaffolding with re-envelope obligation". No new information, but independent confirmation the classification is right. |
| **E3** inter-target phase-1 operand order (known ≠ gc) | (b) PINNED to OURS | same: enumerate orders; if two *writes* collided it would be UB — inapplicable to Go phase-1 operand evaluation (calls hoisted, per BUG-032's probe) | same; observable outcome-set computed by exhaustive mode | Their executable-set output (`exec` returning P(state), §1.4; exhaustive mode, §5.1) is the panic-identity **membership envelope** — one of the two options inventory §7 item 5 lists (it states no preference; audit correction) — restricted to the observable that matters. F3 is an argument FOR preferring it over full linearization. |
| **E4** targets-vs-RHS panic order | (b) PINNED to OURS | as E3 | as E3 | As E3. |
| **E5** early store across the phase boundary (gc exotic, ours spec-literal) | (b) PINNED to the spec-literal point | CH2O's pattern for observed-exotic compiler behavior is *more UB* (§2.6) — unavailable to Go | **Q2's pattern (§2.1): add a nondeterministic choice covering the observed point, even when distasteful** | Yes — Cerberus supplies the right mold and CH2O the wrong one. E5's future envelope should be a two-point (store-held-back / store-early) choice or a membership row, per Q2's precedent; never a UB-style exclusion, which Go cannot express. |
| **E6** len/cap hoist shapes | REFUSED | UB-as-valve: ambiguity and combinatorial blowup both "subsumed" into undef (§2.6) | out-of-scope features listed explicitly (§1); candidate-model failures reported as failures (§6) | Clarifying, not reclassifying: CH2O's valve is *semantic*, ours is tool-level classification. Cerberus's honest "intended behavior on only 9" is the closer kin to our visible-red refusals. Keep the distinction explicit in the inventory preamble. |

**Findings — latitude their machinery models that our inventory does not
carry (the task's "that is a finding" clause):**

- **F1 (candidate missing axis): intra-expression non-call operand
  order outside assignment statements.** E2–E5 are all framed around
  assignment/call shapes; E1 claims the ordered core; but the spec's
  ordering sentence covers only calls/receives/binary-logical, and its
  own example text says the order of the *other* operand events "is not
  specified". Two potentially-panicking non-call operands of one binary
  operation — `a[i] / b[j]`, `p.x + q.y` with nil receivers — are the
  Go residue of CH2O's redex-selection latitude, and no E-entry states
  whether the machine's left-to-right expression spine is (c) forced or
  (b) pinned on that shape. Cheap to resolve: one directed gc probe
  (two panicking operands, swap them, check which panic gc reports and
  whether `-N -l` moves it) plus a rule-site classification sentence.
  If the machine's realization is a pin, it is E3's class and should
  join the E3/E4/E5 membership-envelope treatment; if some frontend
  normalization forces it, record that instead. Either way the census
  currently has a hole exactly where CH2O's mechanism has its center of
  mass. AUDIT REFINEMENT (2026-08-17): F1's nearest neighbour is
  **E11** (runtime-check order *inside one operation* — same
  observable, same (b)-PINNED class), which this note's original
  E1–E6 scope missed; F1 remains genuinely uncovered — it is order
  across two operand *subexpressions*, not within one op — so the
  correct framing for the P2 worklist is "E11-adjacent, not
  E11-covered".
- **F2 (vocabulary gap): order vs interleaving.** Cerberus
  distinguishes `unseq` (actions *interleave*) from indeterminate
  sequencing (atomic units, either order); CH2O's §10.1 shows a real
  behavior (`bac`) that permutation-of-subtrees models miss. Our E3/E4
  envelope statements say "any order of the targets' operand
  evaluations" — the indeterminate reading — while E2 alone gestures at
  "in principle interleavings". The spec's silence plausibly licenses
  the unsequenced reading: a compound operand evaluation (`aa[i][j]`)
  has multiple observable sub-events (two potentially-panicking
  indexings) that could in principle interleave with RHS-call effects.
  Each E-entry's plausible-envelope sentence should say *which* reading
  it claims and why — this is the sequential twin of the granularity
  ledger's concurrency concern (BUG-002's class), and it is currently
  implicit.
- **F3 (cost calibration, not a gap):** Norrish's
  confluence-for-sequence-point-free-expressions and his open problem
  (thesis §10.1), plus CH2O's "completeness complicated by excessive
  non-determinism" (§1.4), together say: enumerating evaluation orders
  in the *proof layer* is the expensive road, and C only survived it
  because UB makes legal programs near-confluent. This independently
  argues for choosing the panic-identity membership envelope over
  full-statement linearization for E3/E4/E5 (inventory §7 item 5
  lists both options without a preference — audit correction; this
  note's F3 is the argument for picking membership).

## 4. The upstream record — what actually happened, and the Go analog

**CH2O → WG14.** The thesis's §2.6.1 story, web-verified against the
WG14 archive: the trigger is the old DR#260 (2004) doctrine that
indeterminate values "may change without direct action of the program".
Krebbers & Wiedijk filed **DR#451, "Instability of uninitialized
automatic variables"** (submitted 2013-08-30 as N1747, argued in paper
N1793, presented at the April 2014 Parma meeting as N1818)
`[web: open-std.org/jtc1/sc22/wg14/www/docs/dr_451.htm, n1747.htm,
n1793.pdf, n1818.pdf]`. The committee *answered* — yes, such values can
appear to change; operations on them yield indeterminate results;
library calls on them are UB — and floated a new "wobbly values"
category, but **changed no normative text**; the wobbly-value concept
was still unresolved years later `[web: same thread; Seacord,
"Uninitialized Reads", ACM Queue 2017]`. The thesis says it plainly:
"our efforts have not led to a clarification of the standard text"
(§2.6.1), and CH2O then encoded the most-restrictive reading (UB) to
stay compiler-safe. §11.1.3 frames the aspiration ("improve the C
standard") as future work, with formalization-finds-what-prose-cannot as
the argument (§11.1.1's feature-interaction analysis).

**Cerberus → WG14.** The slow-burn success: DR260's provenance hint
(2004) → the PLDI 2016 de-facto program → the POPL 2019 provenance
papers and a years-long WG14 drafting arc (N2577, N2676, N3005,
N3226/N3231) → **ISO/IEC TS 6010:2025, "A provenance-aware memory
object model for C", published May 2025**, its semantics developed on
Cerberus and simplified from the executable definitions, with WG14
straw polls at 21/0/1 for wanting it in a future standard `[web:
iso.org/standard/81899.html; open-std.org N3226/N3231/N2364;
gustedt.wordpress.com 2025-06-30]`. Twenty-one years from defect report
to Technical Specification — and the formal model became the *vehicle*
of standardization, not just a commentary on it.

**Calibration for mechanism 4.6.** The campaign's §3 prior cites CH2O as
"our upstream loop precedent". True, but the precedent's content is:
good filings earn *standing and answers*, and rarely earn *text* — the
text came only where a decade of executable-model-plus-community-evidence
work backed it (Cerberus), and even then as a TS beside the standard,
not an edit to it. Two structural reasons Go should run faster: the Go
spec has a single upstream owner who also owns the reference
implementation (no WG14-style implementor/committee split — the
`doc/go_spec.html` git history the campaign already plans to mine is a
record of *routine* clarification commits with issue links, a cadence
WG14 simply does not have), and the Go 1 compatibility promise plus
deliberate de-facto-pin prevention (map-order randomization) keep the
de-facto corpus inside the spec envelope instead of at war with it.
The Go analog of a Cerberus filing is a golang/go issue with: the spec
anchor, a minimal program, the cross-implementation/gc observations,
and our machine's envelope argument — precisely a divergence-ledger
entry serialized. The Go analog of the *survey* is mostly already run
and archived: golang-nuts/golang-dev threads and proposal reviews are
where practitioner expectation gets litigated, so mining beats polling
— with one exception noted in §6 below.

## 5. JSCert sidebar: eyeball closeness

JSCert (Bodin, Charguéraud, Filaretti, Gardner, Maffeis, Naudziuniene,
Schmitt, Smith; POPL 2014) formalized ES5 chapters 8–14 in Coq as
~900 inductive rules, paired with JSRef, an executable reference
interpreter proven correct against JSCert and tested against test262
`[web: jscert.org; doc.ic.ac.uk/~maffeis/papers/popl14.pdf]`. The
discipline the campaign asks about, **"eyeball closeness"**, is a
*design constraint on the rules themselves*: JSCert uses the same
metaphors and data structures as ES5 and follows the standard's
pseudocode line-by-line, such that "every line of pseudocode in ES5
corresponds to one or two rules in JSCert" — someone who knows the
prose spec can read the mechanization as the same document in an
unfamiliar notation, and audit the correspondence by inspection. Their
trust argument is two independent challenge paths: the eyeball
correspondence (rules ↔ prose) and the test path (JSRef ↔ test262),
with the Coq proof welding the two artifacts together `[web: same;
Watt's WebAssembly mechanization thesis credits JSCert for the
principle]`. The discipline paid out concretely: a broken algorithm and
forgotten cases in ES5's Enumerate, ES6 bug reports (nos. 1442–1444),
test262 bugs (1445, 1450, 1600), and implementation bugs in
SpiderMonkey and V8 `[web: jscert.org publications; CAV'15 "One Year
On" retrospective]`. The retrospective's honest accounting is also
instructive: no errors found in the correctness *proof*, but a handful
of consistent misinterpretations of ES5 present in both artifacts —
eyeball closeness bounds divergence from the prose, it does not
eliminate shared misreading.

Does it add anything beyond campaign mechanism 4.1? Mostly no — 4.1 (and
its covmap upgrade) *is* eyeball closeness transposed to our situation,
one level up: our semantics cannot be prose-shaped (the Go spec is
neither pseudocode like ES5 nor algorithm-structured like Wasm's), so
the anchors attach to latitude/envelope arguments and rule-sites rather
than per-rule, exactly as the campaign's §3 sketch says. Two increments
survive scrutiny. First, JSCert's closeness was maintained *while
writing*, not retrofitted; our equivalent norm already exists in
embryo — the E2 rule-site block quotes the spec verbatim at
Machine.lean:2587–2626 — and should be stated as a rule: **every
latitude rule-site carries the governing clause text verbatim plus its
anchor**, so the P2 retrofit converges to a checkable convention rather
than a one-off sweep. Second, their two-independent-paths trust framing
is a clean way to *present* our two bounds to outsiders (anchored
envelope arguments = the eyeball path; the differential = the test
path); worth stealing for the README-level story, no mechanism change.

## 6. Verdicts against the campaign's mechanisms

The stated prior was: "adopt the defect-report workflow and
de-facto/ISO vocabulary; read their evaluation-order treatment against
E1–E6 specifically." Findings: the prior mostly holds; it is wrong in
one phrasing and needs calibration in another.

- **4.1 clause anchors — ADOPT, with the JSCert addendum.** JSCert is
  the original of the scheme and confirms the adapted form (anchors on
  envelope arguments and rule-sites, not per-rule). Addendum from §5:
  make verbatim-clause-text-at-latitude-rule-sites the recorded norm;
  covmap's content-hashed segments are mechanized eyeball closeness
  (drift = the cited text changed), strictly stronger than JSCert's
  by-inspection correspondence. Cerberus's Fig. 3 (elaboration clause
  typeset beside the ISO text) is the same pattern and confirms it
  scales to a 19k-line semantics.
- **4.3 divergence ledger — ADOPT + ADAPT.** The Cerberus question
  format is a richer entry schema than 4.3's current field list:
  per-question *ISO-clear?*, *de-facto-implementation answer*,
  *de-facto-usage answer* (what code relies on — distinct from what
  compilers do, and they measured both), test cases, per-implementation
  experimental data, and an explicit *conflict* tally. Adapt: add a
  usage-vs-implementation split to the ledger's `gc-divergence-tolerated`
  kind, and adopt the 39/27/27-style summary counts as the ledger's
  health metric. CH2O contributes the verdict discipline for
  ambiguities: where the text is genuinely unclear, record the
  most-restrictive reading we act on (our fail-closed refusal standing
  in for their UB) rather than a guessed resolution. JEST-style
  `gc-bug`/`spec-bug` verdicts (already planned) are confirmed by both:
  every one of these efforts found errors in the artifact it
  formalized.
- **4.6 upstream feedback — ADOPT, with recalibrated expectations;
  partially DISAGREE with the doctrine's phrasing.** Adopt the workflow
  (ledger-entry-serialized filings, per-filing sign-off unchanged). But
  the CH2O precedent, read closely, is *standing without text change*
  (DR451: answered, nothing amended), and the text-changing precedent
  (Cerberus → TS 6010) took 21 years and required the formal model to
  become the standard's own drafting vehicle. Expectation to record in
  the mechanism: filings buy standing, corpus cases, and committed
  clarifications of *intent*; normative-text movement is a long-game
  outcome, though Go's single-owner spec with routine clarification
  commits should sit well inside C's timescale. Second, the doctrine's
  sentence "Cerberus's de-facto-vs-ISO distinction *is* our two-bounds
  doctrine independently reinvented" is imprecise and should be
  amended when next touched: Cerberus documents 27 of 85 questions
  with "significant differences between the ISO and the de facto
  standards" (the paper's wording; Q25 is the archetype of the
  deployed-code-relies-on-what-ISO-forbids direction, but the paper
  does not claim all 27 point that way — gloss tightened by audit) — a third-artifact situation (the
  candidate de-facto model) that our two bounds deliberately do not
  have, because in Go `observed ⊆ permitted` actually holds, enforced
  by the compatibility promise. The correct statement: Cerberus is the
  cautionary tale showing what the two-bounds frame degenerates into
  when a language lets the bounds cross — which the doctrine's
  C-as-cautionary-tale paragraph already half-says. Keep
  `gc-divergence-tolerated` rare precisely so no candidate-de-facto-Go
  artifact ever needs to exist.
- **Survey methodology (feeds 4.5/P5, no mechanism number) — ADAPT,
  narrowly.** A mass practitioner survey is the wrong instrument for
  Go (the ambiguity-litigation record is already public and minable).
  The narrow adaptation with real value: Cerberus's
  *question-formulation discipline* — a sharp question + a minimal test
  program + per-implementation data per ledger entry — and, at the one
  place where practitioner expectation is genuine upper-bound evidence
  with no oracle (the scheduling/fairness envelope, C1–C4's territory),
  a small expert-targeted 2013-style consultation is worth considering
  at P5, not a 323-respondent 2015-style one.

## 7. Concrete next actions (≤5)

- **Probe and classify finding F1** (intra-expression non-call operand
  panic order, e.g. `a[i] / b[j]`): one gc probe matrix + a rule-site
  classification; add the resulting E-entry (or a recorded
  forced-by-frontend note) to the inventory. Small; closes the census
  hole at the center of CH2O's mechanism.
- **Add the order-vs-interleaving sentence (F2) to E2–E5's
  plausible-envelope statements** during the P2 anchor retrofit —
  adopt Cerberus's unseq/indeterminate vocabulary so each envelope says
  which reading it claims.
- **Fold the Cerberus entry schema into 4.3's field list** before P4
  seeding: usage-vs-implementation de-facto split, conflict flag,
  summary counts.
- **Record the E5 re-envelope mold as Q2-style** (nondeterministic
  choice covering gc's observed exotic point) and the E3/E4/E5
  proof-layer cost note (F3, Norrish's open problem) in the inventory's
  §7 item 5, so the re-envelope slice starts with the right design.
- **Amend the doctrine's "independently reinvented" sentence** (per the
  4.6 disagreement) at its next touch, and write the calibrated
  upstream-expectations paragraph into mechanism 4.6.

## 8. Could not verify

- **Extraction fidelity:** both PDFs were read through a scratch
  pure-Python extractor (no poppler in the sandbox); ligatures (fi/fl),
  math symbols, and some cross-reference numbers were lost. All section
  numbers cited were cross-checked against the thesis's table of
  contents and the paper's running heads, but page-exact wording is not
  guaranteed; the CH2O head-reduction rules (Def. 6.4.1) were read with
  garbled notation and are characterized from the surrounding prose.
- **The exact suite behind Cerberus §6's "556 (5 time-outs)" figure:**
  the identifying sentence fell on a garbled line; context suggests the
  Ellison–Roșu/KCC-associated test set, unconfirmed.
- **Whether Krebbers filed WG14 items beyond DR#451/N1793:** the thesis
  (§2.6.1, §2.6.2) also mentions a GCC bug-tracker report
  (pointer-to-integer comparison inconsistency) and gcc bugzilla 61502
  is cited for the adjacent-objects issue; I did not verify whether
  either GCC report was theirs or pre-existing, nor whether any further
  WG14 documents carry their names.
- **All JSCert specifics** (rule counts, bug-report numbers 1442–1445/
  1450/1600, test262 pass counts, CAV'15 retrospective details) are
  web-sourced, not read from a pinned primary PDF — JSCert/JSRef is on
  the campaign's `deps/papers/` acquisition list and these should be
  primary-verified if the sidebar's claims are ever load-bearing.
- **TS 6010's precise technical distance from the Cerberus-paper-era
  candidate model** (PNVI-ae-udi vs the PLDI 2016 sketch): asserted
  from WG14 documents' own attribution `[web]`, not from reading the TS.
- **CH2O's treatment of function-call atomicity in expressions**
  (no interleaving of call bodies): inferred from §6.4's redex
  classification and the single-focus zipper of §1.4; I found no
  sentence stating it in so many words.

Web sources: open-std.org WG14 documents (dr_451, n1747, n1793, n1818,
n3226, n3231, n2364), iso.org/standard/81899.html (TS 6010),
jscert.org, doc.ic.ac.uk/~maffeis/papers/popl14.pdf, Seacord ACM Queue
2017, Gustedt's TS 6010 post (2025-06-30).
