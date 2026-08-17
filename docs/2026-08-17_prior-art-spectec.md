# Prior-art reading note: Wasm SpecTec (2026-08-17)

Status: P1 reading note, spec-truth campaign (`docs/2026-08-17_spec-and-community-truth-campaign.md` §3).
Subject sources: `deps/spectec` (Wasm-DSL/spectec @ `acc6e834`, "Sync with upstream", 2026-05-29) and
`deps/papers/spectec-pldi24.pdf` (Youn, Shin, Lee, Ryu, Breitner, Gardner, Lindley, Pretnar, Rao, Watt,
Rossberg — "Bringing the WebAssembly Standard up to Speed with SpecTec", PLDI 2024, doi 10.1145/3656440).
Verdicts are recorded against campaign mechanisms §4.1–4.6. The campaign's expected verdict for SpecTec is
tested, not assumed; where the note disagrees or corrects, it says so.

Extraction note: the PDF was read via an ad-hoc zlib/TJ text extraction (no poppler in the sandbox); all
quoted numbers were cross-checked against at least two passages of the extracted text. Math-notation
passages (paper §§3.1–3.3 figures) were only partially recoverable; see "Could not verify".

## 1. What SpecTec is and how it actually works

SpecTec is a DSL plus OCaml toolchain in which the Wasm community writes the *normative* Wasm
specification once, in a declarative ASCII notation, and generates from that single source: the typeset
LaTeX formal rules, the reStructuredText prose pseudocode, and a meta-level interpreter. The pinned
checkout is not a research prototype beside the spec — it is a fork of `WebAssembly/spec` in which the
tool and the spec live together and the spec document *builds through the tool*:

- `spectec/` — the toolchain. `spectec/src/` splits into `frontend` (parse to External Language, EL),
  `el`/`il`/`al` (the three IR layers), `middlend` (IL→IL passes: implicit side conditions, partial-function
  totalization into options, subsumption injections, premise dataflow analysis — paper §2.3),
  `il2al` (the "animation" pass, declarative→algorithmic; `animate.ml`, `translate.ml`), and backends:
  `backend-latex`, `backend-prose`, `backend-splice`, `backend-interpreter`, `backend-ast`.
- `specification/wasm-1.0/`, `wasm-2.0/`, `wasm-3.0/`, `wasm-latest/` — the spec itself as `.spectec`
  files, one directory per language version (e.g. `wasm-latest/4.3-execution.instructions.spectec` holds
  the `Step`/`Step_pure`/`Step_read` reduction relations). `specification/Makefile` type-checks all four
  versions (`check-all`) and `sync-wasm-latest.sh` keeps `wasm-latest` synchronized with the highest
  versioned directory.
- `document/core/` — the actual W3C spec document sources; `document/core/Makefile` wires `SPECTEC` in
  and splices generated formal/prose fragments into the document skeleton (`SPLICEDIR = _spectec`).
  `spectec/README.md`: "The core spec document in this repo is build using SpecTec by default."
- `test/core/` — the official `.wast` test suite, in the same repo; `spectec/test-interpreter/spec-test-{1,2,3}`
  hold the per-version suites the meta-interpreter runs (75/91/106 files).
- `.github/workflows/ci-spectec.yml` runs `make ci` (spec check + document build + backend tests) on
  every push/PR touching `spectec/**` or `document/**`.

The DSL (paper §2.2, Fig. 5; `spectec/README.md`) has four generic mechanisms — syntax definitions,
relations+rules, functions, grammars — with no Wasm concepts hard-coded in the frontend; Wasm lives
entirely in the `.spectec` input ("Pragmatics" discussion, paper §6). The frontend type-checks
definitions, infers iteration "dimensions", and elaborates EL→IL. The interesting engineering is
`il2al`: turning declarative reduction rules into deterministic pseudocode requires deciding, per
premise, whether `=` is an equality *check* or a variable *binding*, and ordering premises so bindings
precede uses. The paper proves minimal-fresh-variable binding assignment NP-hard (Theorem 3.2, by
reduction from Exact Cover) and ships an all-or-nothing heuristic (Knuth's algorithm for the
no-partial-bindings case, greedy fallback). `spectec/doc/Assumptions.md` documents the resulting
restrictions frankly: only turnstile and `Step*` relations become prose; rule groups must partition
their input space; cyclic premise bindings fail; `otherwise` carries ordering obligations.

Three fidelity caveats, all confirmed in both paper and checkout, matter for how much their headline
results prove:

1. **The executable formulation is not literally the published one.** Wasm 2.0 uses evaluation contexts;
   the SpecTec source uses a "bubbling-up" reformulation, and `instantiate`/`allocmodule` were rewritten
   to break premise cycles (paper §4). The equivalence of these reformulations is asserted, not proven.
2. **The meta-interpreter borrows from the reference interpreter**: the text/binary parser, numeric
   primitives (`$fadd_` etc.), and (for GC subtyping) validation are the reference interpreter's OCaml
   (`spectec/doc/Interpreter.md`; `src/backend-interpreter/dune-ref-interp` builds it as a library;
   `relation.ml:52` calls `Reference_interpreter.Valid.check_module`). The trusted base of the "spec
   interpreter" includes pieces of the implementation it might otherwise check.
3. **Nondeterminism is executed as a deterministic pin.** The spec's latitude points (`memory.grow` /
   `table.grow` may fail) become AL `EitherI`; `src/backend-interpreter/interpreter.ml:597` runs the
   first branch and backtracks to the second only on `Fail`/`OutOfMemory`. Their executable artifact
   realizes one member of the envelope — exactly what our doctrine calls a gc-pin, and nothing in
   their loop measures envelope width.

The prover backends (Coq/Isabelle/Agda/Lean) that the paper lists as the mechanization payoff are
*future work* in the paper (§6, "We have begun work on backends for Agda, Coq, and Lean") and are
**absent from the pinned checkout** — `src/` has no prover backend directory (`backend-ast` is an AST
printer). The shipped artifacts are LaTeX, prose, splice, and the interpreter.

## 2. The validation loop, and the error-finding record

**The loop (paper §§3.5, 4.1).** The meta-interpreter executes the official test suite: 49,833
assertions (47,391 `assert_return`, 2,408 `assert_trap` on actions, 34 `assert_trap` on module
instantiation) in 58 s on a 2019 laptop, passing 100% of the *applicable* suite. "Applicable" is a real
scope cut: of the seven `.wast` assertion kinds, three (parsing/validation) plus the infinite-loop kind
were excluded in the paper. The scoping is mechanized honestly in the checkout: `runner.ml` gives
unhandled assertion kinds `pass = 0,0` — excluded from numerator *and* denominator, never counted
green (`src/backend-interpreter/runner.ml:20-25`, and the `| _ -> pass` fallthrough). Coverage has
since grown: the pinned rev handles `AssertInvalid` for version 3 (`runner.ml:203`). Eleven
long-running `.wast` files are excluded by default (`runner.ml:29-45`). Note what the loop *is*: the
test suite's expected results are the oracle, the spec-derived interpreter is the system under test. A
pass certifies internal consistency of the standard's artifacts (formal text ⟷ tests, and — since the
suite is maintained against the reference interpreter in `ci-interpreter.yml` — transitively spec ⟷
reference implementation). It is a membership check, our lower bound; it says nothing about the width
of the spec's latitude, which their `EitherI` pins anyway.

**Errors in shipped spec text (paper §4.2) — read the claim precisely.** RQ2 is a *retrospective
injection study*, not a discovery record: they mined two years of fix commits on the Wasm spec's main
branch, classified the normative ones — 3 type errors, 7 prose errors, 3 semantics errors, plus
"numerous" editorial issues — re-injected them into the SpecTec source, and confirmed each *would have
been* caught (type errors by the frontend, prose errors by generation, semantics errors by the test
suite through the meta-interpreter). The abstract's own wording is "detecting historical errors in the
specification that have been corrected". The campaign plan's phrasing ("found errors in shipped spec
text and in five in-flight proposals", §3) is half right: the shipped-text half is
would-have-prevented, not newly-found. This matters for us because the *method* of RQ2 — mine the
spec's own fix history for a verified error taxonomy — is precisely ledger seed #1 in campaign §4.3
(`git log --follow doc/go_spec.html`), and SpecTec is evidence the seed yields a classifiable,
double-digit haul on a spec far more rigorous than Go's.

**Errors in in-flight proposals (paper §4.3) — the genuine discovery record.** They extended the
SpecTec spec with five proposals slated for Wasm 3.0 (typed function references, GC, tail calls,
multiple memories, extended constant expressions; 44 instructions added/modified) and found **ten new
bugs**: 2 type errors, 2 prose errors, 4 semantics errors, 2 editorial — reported upstream and
confirmed by the proposal authors (paper refs [16, 29, 91–95], e.g. WebAssembly/gc#456, gc#476). After
fixes, the proposals' 1,331 tests all passed. Two of the 44 instructions needed their rules rewritten
before the DL→AL translator could handle them — the animatable-subset constraint bites even the
authors. The endgame the paper only aimed at ("our ultimate aim is that SpecTec should be adopted")
has, by the pinned rev, substantially happened: the fork *is* the spec repo variant in which the Wasm
3.0 document builds from `.spectec` sources by default.

## 3. Verdicts against the campaign mechanisms

**The campaign's prior, tested.** "Reject the spec-generation frame; adopt the coverage discipline."
The rejection **stands, and for a stronger reason than the campaign gives**. The campaign's reason is
standing ("we don't own Go's spec"). The deeper reason is that SpecTec's entire error-finding power
comes from having a *formal, type-checkable source artifact* whose redundant siblings (prose, LaTeX,
interpreter) can drift from it — 3 of 13 historical bugs were caught by meta-type-checking alone, 7 by
prose generation. Go has one prose spec, no formal sibling, no four-artifact redundancy to
collapse; there is nothing to type-check and no duplication to automate away. The transferable insight
is the role assignment: **our machine plays the part of their SpecTec source** (the checkable formal
artifact), and the redundancy that generates findings is machine-vs-spec-text — which is exactly the
divergence ledger. The "adopt the coverage discipline" half needs **sharpening, not adoption
wholesale**: their loop is not "our differential gate" as §3 claims. Both are lower-bound membership
checks, but their oracle (test-suite expectations) is authored by the same community as the model, so a
pass certifies artifact self-consistency; our oracle is an independent implementation, so a red can
indict either side — which is why we need the JEST-style verdict fields their loop has no use for.
What *is* worth adopting from their coverage practice is specific and listed under 4.2/4.3 below.

### 4.1 Clause anchors + lint — ADOPT, and add the reverse direction

SpecTec gets citation integrity *by construction*: every rule is named (`rule Instr_ok/nop`), documents
reference rules via splices (`@@{rule: Step_pure/select=*}`, paper §2.4), the prose backend emits every
cross-reference mechanically (`\xref{doc}{section}{text}`, §3.4 — "rules out possibilities of missing,
broken, or misplaced links"), and `src/backend-splice/splice.ml:130-134` warns on any rule "never
spliced" or "spliced more than once". As spec consumers we cannot generate, so the lint direction
(check citations resolve against the pinned copy) is the correct adaptation — the campaign already has
this right. What SpecTec adds is the value of the **reverse query**: their "never spliced" warning is
the zero-witness accounting the campaign wants from covmap's unlinked-segment query (§8.1), running in
production in a standards pipeline. Verdict: adopt 4.1 as planned; treat bidirectional coverage
accounting (which clauses have no envelope argument / corpus witness citing them) as a first-class
requirement of the 4.1 implementation, not a nice-to-have — this strengthens the case for covmap over
the bare anchor lint, since the bare lint cannot answer the reverse query at all.

### 4.2 Spec-example corpus — ADOPT; copy two specific practices

The Wasm arrangement is the campaign's plan already realized: spec text, test suite, and reference
implementation pinned in one repo (`test/core/` beside `document/` beside `specification/`), suites
indexed per language version (`spec-test-{1,2,3}`). Two practices to copy verbatim. (1) **Negative
cases are first-class**: `assert_invalid`/`assert_malformed` tests check *rejection* behavior, and the
pinned rev's growth from "exclude validation assertions" (paper) to running `AssertInvalid` (checkout)
shows the exclusion was tracked as debt and paid — matching the campaign's plan to make
intentionally-invalid spec examples must-fail cases. (2) **Scoped-applicability accounting**:
`pass = 0,0` — a case the tool cannot run is excluded from the score visibly, never counted green, with
the exclusion list in code (`runner.ml:29-45`), the mechanized form of our
visibly-blocked-never-false-pass rule. Verdict: adopt 4.2 as planned.

### 4.3 Divergence ledger — ADOPT, with one adaptation

SpecTec validates both ledger seeds and the payoff. Their RQ2 mining of two years of spec-fix history
produced 13 classified normative errors on a spec already maintained with unusual rigor; Go's prose
spec history should yield at least as richly (campaign seed #1). Their classification axis, though, is
*which tool phase catches it* (type / prose / semantics / editorial) — the right taxonomy for a spec
author. Ours is *which artifact is at fault* (`spec-bug` / `gc-bug` / `spec-ambiguity` / `ours`) — the
right taxonomy for a consumer running a differential; keep it, but record a "how found" field too,
since SpecTec's experience is that the detection phase predicts the fix cost. One honest negative
result to carry over: SpecTec's loop cannot see latitude-width errors (its own `EitherI` pins them),
and none of its 23 recorded findings is an envelope error. The ledger's `spec-ambiguity` kind — our
most doctrine-relevant class — has **no SpecTec precedent**; CH2O/Cerberus are the prior art for that
class, not SpecTec. Verdict: adopt 4.3; do not cite SpecTec as precedent for ambiguity findings.

### 4.4 Language-version pin — ADOPT; SpecTec is direct precedent

The checkout versions the *semantics itself* as parallel directories (`specification/wasm-{1.0,2.0,3.0}`)
plus a synced `wasm-latest`, with per-version test suites and version-conditional runner behavior
(`when !Construct.version = 3`, `runner.ml:203`), and `check-all` type-checks every version on CI. This
is the campaign's §4.4 (corpus `go` directive + spec pin + oracle toolchain must agree, version-skew
behaviors as ledger entries) already working at standards scale, and it validates the specific choice
of keeping *old* versions checkable rather than only the pin — which is what makes a re-pin diffable
(`diff-wasm-latest.sh` exists for exactly this). Verdict: adopt.

### 4.5 Cross-implementation lane — NO EVIDENCE EITHER WAY; one warning to record

SpecTec does not run a cross-implementation differential; the many production Wasm engines appear
nowhere in its loop. Worse for independence, the reference interpreter sits partly *inside* the
meta-interpreter's trusted base (parser, numerics, GC validation — §1 caveat 2), so the 100% figure is
not a fully independent check of spec against implementation. The transferable lesson is negative:
**keep the oracle wholly external to the machine**. Our differential already has this property (`go
run` shares nothing with GoCore); the SpecTec precedent is the reason to defend it when sharing
components ever looks convenient. Verdict: the campaign's decide-at-P5 stance is unchanged by this
reading; record the independence warning in the P5 decision inputs.

### 4.6 Upstream feedback loop — ADOPT, with the standing caveat stated honestly

Ten reported-and-confirmed proposal bugs earned SpecTec more than standing: by the pinned rev, the
spec document builds through their tool — the Sail endgame ("the community recognizes the machine",
campaign §3) realized for Wasm within ~two years of the paper. This is the strongest available
precedent for the campaign's thesis that a formalization effort filing good reports earns influence.
The honest caveat: SpecTec was never an outsider — Andreas Rossberg, the Wasm spec's editor, is a
paper author, and the effort was seeded at a Dagstuhl seminar of the Wasm formalization community
(paper acknowledgments). Our position with the Go team is genuinely external; JSTAR/CH2O (outsiders
who earned standing via report quality alone) are the closer precedents for the mechanism, SpecTec
for the ceiling. Verdict: adopt 4.6 as written (per-filing sign-off), with expectations calibrated to
the outsider precedents, not to SpecTec's insider trajectory.

## 4. Concrete next actions for golean

- **Correct the campaign doc's §3 SpecTec sentence** at the P1 verdict-recording step: "found errors in
  shipped spec text" → "showed 13 historical shipped-spec errors would have been prevented
  (retrospective injection study) and found 10 new errors in five in-flight proposals (confirmed
  upstream)". The distinction changes which of our mechanisms each half is evidence for (4.3 seed
  mining vs. 4.6 upstream path).
- **Make the reverse coverage query a stated requirement of the 4.1 pilot's exit criteria**: the
  covmap-vs-bare-lint decision (§8.5) should weigh that SpecTec's production analog of 4.1 does
  zero-witness accounting (`splice.ml` "never spliced") and the bare anchor lint structurally cannot.
- **Lift SpecTec's applicability accounting into the spec-example corpus design (P3)**: every extracted
  example carries an explicit classification, excluded classes are listed in the extractor with reasons
  and excluded from the denominator (the `pass = 0,0` pattern), and must-reject examples land as
  negative cases from the start rather than as later debt.
- **Add a "how found" field to the divergence-ledger schema (P4)** alongside the fault-verdict `kind`
  (mining / differential red / spec re-read / community seed / probe), per the RQ2 lesson that
  detection phase is worth recording; and note in the ledger doc that `spec-ambiguity` entries have no
  SpecTec precedent — cite CH2O/Cerberus there instead.
- **Record the oracle-independence warning** (from SpecTec's reference-interpreter dependence) in the
  P5 decision inputs for 4.5: any future convenience-sharing between machine and oracle (parsers,
  numerics, printers) repeats the flaw that scopes SpecTec's 100% claim.

## 5. Could not verify

- **Figure/math content of paper §§3.1–3.3**: the text extraction garbled math-font passages (DL/AL
  syntax figures, Algorithms 1–2 details). The NP-hardness statement (Theorem 3.2), the Exact-Cover
  reduction, and the all-or-nothing heuristic are verified from surrounding prose; the exact
  algorithm listings are not.
- **The 100%-pass and 58 s numbers** are the paper's report; not reproduced here (would need an OCaml
  5.x toolchain build of `spectec` — not attempted from the read-only lane).
- **Formal adoption status by the W3C Wasm CG**: the checkout shows the spec document building through
  SpecTec by default and CI enforcing it in the Wasm-DSL fork; whether the W3C-published Wasm 3.0
  document is officially produced from this pipeline (and `w3c-publish.yml`'s exact role) I could not
  confirm from the checkout alone.
- **Equivalence of the executable reformulations** (bubbling-up vs. evaluation contexts;
  rewritten `instantiate`/`allocmodule`): asserted by the authors, no proof artifact found in paper or
  checkout.
- **Whether the paper's five proposal-bug "semantics errors" were test-suite-caught or read-caught**:
  the paper says the historical semantics errors were caught by running the suite; for the proposal
  bugs it reports totals only, without per-bug detection detail beyond the linked issues (not fetched).
- **The paper's claimed test-suite coverage analysis** ("The AL interpreter also allows us to easily
  analyze the coverage of the existing Wasm test suite", §6): no coverage-measurement code exists in
  the pinned `spectec/src/` (grep over `src/` finds none), so this is either unreleased or elsewhere;
  the campaign should not cite SpecTec as having shipped rule-coverage tooling.
