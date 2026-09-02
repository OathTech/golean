# The fidelity assessment: state of the union (2026-08-31)

Phase-3 synthesis of the seven phase-1 lane reports and three
phase-2 adversarial/verification passes (all under docs/assessment/;
every number below is anchored there, and phase-2's corrections are
already folded in — where phase 2 refuted a phase-1 claim, the
refutation wins). This document is the [USER] checkpoint: nothing in
§5 executes without sign-off.

## 1. The verdict in one paragraph

The outsider reviewer's verdict is the fair one: **CREDIBLE-WITH-
DEMANDS**. What exists is an executable, total, axiom-free
operational semantics for a substantial sequential fragment of Go
1.26, differentially validated with unusually honest bookkeeping —
and the honest bookkeeping has quietly become a SUBSTITUTE for
mitigation in a measurable pattern: recorded gaps priced "S" that
sat unmoved across arcs, register wording that drifted from the
inventory it summarizes, theorems cited that live on a parked
branch, and five independent cases where the CLAIMED boundary and
the REALIZED boundary differ — every one found by adversarial
reading, none by a gate. The lower bound is genuinely strong at its
core and thin at its edges; the upper bound is honestly enumerated
and weakly realized (441 enumerated behaviors across the membership
rows; 45 distinct values exhibited by the oracle in the current
gate run's samples — 10.2%; per p2-fact adjustment 1, a
current-samples count, not an all-time one);
the validation apparatus's exec lane would survive hostile review
while its negative lane, notification path, and derived-artifact
guards would not.

## 2. The four claims, graded

- **C1 feature totality: ADEQUATE-MINUS.** The 143-refusal frontier
  is now enumerated by feature (lane A2's table — the first time it
  existed anywhere): the real frontier is the STDLIB BOUNDARY (41
  refusals) not complex numbers (27), and the queue ordering
  encodes the dead raft plan. Refusals name their causes (probed,
  genuinely good) — but phase 2 found silent leaks in the claimed
  fail-closed boundary: `unsafe.Sizeof/Offsetof` fold
  implementation-specific layout constants into the wire with no
  refusal; two refusal messages name phantom causes; BUG-068's
  phantom refusals hid a silent wrong answer.
- **C2 lower-bound fidelity: ADEQUATE, with live exceptions.**
  The exec-lane differential is fail-closed, attributed, and
  byte-honest. Standing against it: **BUG-062's five silent wrong
  answers at spec-forced points** (re-confirmed live: machine says
  5, gc says 1, both report ok), open since 2026-08-19; the
  phase-2-discovered **E8 file-list-mode gap** (`go run zz.go
  aa.go` at the pinned oracle realizes a declaration order the
  frontend cannot — observed ∉ modeled today, masked only by the
  harness invoking directory mode); the one-implementation/
  one-platform/one-version monoculture (register #3), sharpened by
  grossmith's own record that **the oracle was wrong more often
  than the machine** (3 gc bugs vs 1 ours in one campaign); a
  corpus that is a closed loop (Go's own $GOROOT/test suite:
  pinned, praised, never run); and go/types-vs-types2 sibling
  divergence already real (E7).
- **C3 upper-bound faithfulness: WEAK (honest, enumerated,
  under-realized).** The choice-tape architecture is structurally
  excellent (one tagged combinator, exhaustiveness-checked site
  census, junk streams impossible). But 24 latitude rows are
  pinned/narrowed — five KNOWN ≠ oracle (E3/E5/E7/E13/R3) — in a
  queue that does not move; phase 2 found **permitted ∉ modeled on
  a DRF program** (E9: handshake-synchronized cross-goroutine
  delete; the machine's own docstring admits the prune is
  per-goroutine, against the [USER]-ruled full-literal envelope);
  C6's mandatory distributional fairness is over-approximated;
  modeled ⊆ permitted has no mechanical witness; and the census's
  own completeness argument is heading-granular. The racy-refusal
  register sentence over-claims (per-RUN, not per-PROGRAM; the
  NPDRF reduction is a draft its own header says is "REFUTABLE as
  written… nothing may cite it" — and two inventory rows cite it).
  Phase 2 also REFUTED one suspected gap: the B3 abort-window probe
  (56 runs, three designs) found NO observed-∉-modeled exposure —
  the model already covers deferred-execution interleaving; B3's
  residual should be argued from the runtime's own freeze-is-best-
  effort text, not probe silence.
- **C4 validation credibility: ADEQUATE core, weak edges.** Strong:
  exec-lane integrity (manifest sha covers cases.tsv expectations;
  atomic no-publish; per-lane epistemic captions). Weak: the
  negative lane has NO integrity kit and its baseline header claims
  a frontend check that does not exist (the 390 negative programs
  have never been seen by any GoLean tool); the reconciler has been
  emitting a HIGH finding to nobody for nine days (exit 0 by
  design, wired to nothing); push/PR CI runs with
  GOLEAN_ALLOW_NO_DIFF=1, has NO failure notification path, and a
  FAIL→PASS baseline flip lands green with nothing run; generated
  oracle artifacts (33,004 float vectors; the inittask table) have
  no re-derivation guard (probed: currently byte-identical — the
  guard is cheap and green); evidence dirs follow an unwritten
  convention with commit SHAs in 4/26; file:line citations in the
  census mirror have drifted three times past a "now re-verified"
  assertion; the frontend carries 249 catalogued obligations with 0
  discharged, leaves go/types' GoVersion UNSET (version enforcement
  is ambient, worse than suspected), and NativeToIR has no
  exact-key discipline on statement nodes.

## 3. What is genuinely good (say it plainly)

The two-bounds doctrine with a maintained latitude census has no
peer among Go semantics and few among any-language semantics; the
choice-tape reification is the right architecture and its
fail-closed spine held up under three adversarial passes (the §7
"withdrawn attacks" list in p2-keeps-a2a3bcd.md is real evidence);
refusal quality is high; the exec-lane differential's integrity
engineering (manifest attribution, no-publish atomicity, re-pin
laundering guards) is state-of-the-art for this kind of apparatus;
and the project's self-records were accurate enough that a hostile
audit could be CONDUCTED FROM THEM — most findings were sharpenings
of things the repo already said about itself. That last fact is the
foundation the fix campaign builds on.

## 4. Decisions for the [USER] (consolidated escalations)

1. **Concurrency claim scope.** Scope all C3/upper-bound claims to
   DRF programs and declare the racy limited-outcomes envelope out
   of product scope (the literature-honest ground is cost + no
   oracle, not impossibility)? And for the NPDRF reduction (the
   granularity soundness story): invest in a weakened proved form
   (L/XL), or scope every concurrency claim with an explicit
   stated assumption? Also needs an owner: detector-completeness
   is currently delegated in a circle (A2→C→A1→nobody).
2. **The stdlib boundary strategy.** 41 of 143 refusals are stdlib;
   the shim mechanism is 3,305 lines across five injection
   mechanisms; docs/2026-08-16_overrides-design.md records your
   verbatim ruling to retire the mechanism at the SECOND shim, and
   it was never revisited. Options: (a) re-ratify injection at
   scale on the record, with the Fields-standard per-shim
   validation rule (rows + randomized shim-vs-stdlib fuzz) made
   mandatory; (b) execute the ruling (linked-registry redesign).
3. **Frontier re-ranking.** The FR queue's complex-numbers-last
   ordering served the raft plan; under the new goal the stdlib
   surface and the go-of-builtin/recv-shortcircuit S-priced items
   arguably outrank it. Approve re-ranking (proposal in the work
   program)? And: one [USER] sitting closes the eight Q-row
   rulings (the ruling sheet has been ready since 2026-08-21;
   21 baseline reds ride on it).
4. **The oracle matrix (the standing P5 decision).** (a) Version
   sweep under the existing drift mechanism: cheap, recommend yes.
   (b) GOARCH=386 STATIC leg (go/types with 386 sizes): free,
   recommend yes. (c) DYNAMIC 386/second-implementation legs:
   needs a host/sandbox capability call (386 binaries currently
   abort here) and a gccgo/tinygo feasibility decision — your
   call on whether to invest. (d) $GOROOT/test run: M-cost, the
   single best external-validity purchase, recommend yes.
5. **Register #7 (unbounded memory).** Keep as standing
   idealization WITH a now-mandatory rider on consumer-facing
   claims (allocation-succeeding runs only), or model allocation
   failure? (Recommend the rider; modeling OOM buys little for
   its cost.)
6. **Orphaned obligations.** Every Q-row, every (c)-pin
   re-envelope obligation, and 4 open bugs route to arcs that are
   parked on the reasoning branch. Re-home them to this product's
   backlog (recommended), or re-park each with a dated owner.
7. **Decay dates.** Adopt the outsider's proposal: every recorded
   set-aside carries an expiry/re-review date; the reconciler
   (wired into ci as a report-only note — gates stay speedbumps)
   surfaces expired entries. Recommend yes.

## 5. The work program (executes only on sign-off)

**Tier 1 — silent-wrong-answer class + measured fidelity gaps
(the "a visible red beats a hidden wrong answer" tier), ~1-2
sessions:** BUG-062 mini-slice A6 (5 wrong answers; also retires
BUG-032's four over-refusals) · E8 file-list-mode fail-closed
detector · unsafe.Sizeof/Offsetof refusal (or explicit envelope)
· fmt.Formatter-precedence emit-time refusal · E7 hidden-dep
detector (charter-ruled "ships first", never shipped) · the two
phantom-cause refusal messages.

**Tier 2 — records made true again, ~1 session:** register #2's
known-≠-gc list synced (E13); E10/R1 site caveats actually written
at their sites; park-pointers on the quotient-theorem and
FairStream citations (present-tense "PROVEN" claims re-worded);
census-mirror file:line sweep + a cheap line-anchor guard;
negative-baseline header corrected; A1's doctrine/inventory
numbering collision fixed; BUG-008 re-checked (likely free red
retirement); the B3 record re-grounded on the runtime-text
argument (probe evidence attached).

**Tier 3 — validation apparatus edges, ~2 sessions:** negative-lane
integrity kit (meta + sha + oracle pin + atomic publish) · replay
judge reads go_drift/git_dirty · CI failure notification + the
FAIL→PASS flip guard direction · FloatVectors/inittask
re-derivation guards (probed cheap) · evidence-dir convention
written down + SHA required · reconciler wired as a ci report-only
note · GoVersion set + build-constraint evaluation · NativeToIR
exact-key discipline.

**Tier 4 — evidence-base widening, ~3-5 sessions (sequenced after
1-3):** $GOROOT/test differential run + triage · grossmith
integration (cadence, adapter contract test, generator widening
toward pointers/floats/defer/generics/stdlib — its exclusion list
is exactly the model's riskiest surface) · version-sweep +
386-static legs · membership/strict-lane depth (sampling budget,
stream length, the menu-invariant validator as the first
modeled⊆permitted mechanical witness) · detector-soundness
differential (-race legs at sampling scale).

**Tier 5 — upper-bound realization, sized after 1-4:** deviation-
queue burn-down (E3/E5 guards then re-envelopes) · sentence-level
latitude sweep of the pinned spec + memory model (census
completeness) · E9 cross-goroutine prune (or [USER] re-scope of
the envelope ruling) — DONE 2026-09-02, pool-level `pruneForeign`,
inventory E9 CLOSED (branch t5-e9-prune) · frontend-obligation
discharge start ·
NPDRF per decision 1.

## 6. Grade the assessment would give itself

Phase 2 changed real outcomes (4+10 KEEPs broken, one headline
hypothesis refuted before it reached this report, three anchor
facts materially adjusted) — the adversarial layer was not
ceremony. Residual honesty: this synthesis still rests on ~10
agent-sessions of reading over a ~200k-line repo; the census is as
good as its sweep, and the sweep found three of its own blind
spots along the way. The work program's tier 2 exists precisely
because records that drift silently make the NEXT assessment
start from less.
