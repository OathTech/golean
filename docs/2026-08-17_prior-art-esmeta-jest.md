# Prior-art reading note: the ESMeta / JISET / JEST / JSTAR line (KAIST PLRG) — 2026-08-17

Status: P1 reading note for the spec-and-community truth campaign
(`docs/2026-08-17_spec-and-community-truth-campaign.md` §3, ESMeta
entry). Verdicts are recorded against the campaign's §4 mechanisms and
against the two priors the plan sketched for this line.

Sources actually read: `deps/esmeta` @ `7d237fd` (2026-05-15, v0.7.3
per `deps/esmeta/README.md:73`) — README plus the extractor, compiler,
`lang` step AST, fuzzer, injector, and coverage sources cited below;
`deps/papers/jest-icse21.pdf` (full text). JISET (ASE 2020), JSTAR
(ASE 2021), and the PLDI 2023 feature-sensitive-coverage paper have no
PDFs in `deps/papers/` — their numbers below are **web-sourced** (search
results + the ASE 2021 abstract page) and tagged `[web]` at each use.
grossmith read from the main checkout `/home/dev/projects/golean/deps/grossmith/README.md`
(not bootstrapped into this worktree's `deps/`).

## 1. The pipeline as it actually is

**ECMA-262 is not prose in the sense Go's spec is prose.** It is
ecmarkup HTML in which every abstract algorithm is an `<emu-alg>`
element of numbered steps written in a constrained, conventionalized
metalanguage, and the grammar is `<emu-grammar type=definition>`
elements. Extraction is literally a jsoup CSS query plus parser
combinators over that step language:
`deps/esmeta/src/main/scala/esmeta/extractor/Extractor.scala:87`
(`emu-grammar[type=definition]:not([example])`) and `:107`
(`emu-alg:not([example])`), feeding a closed step AST — `LetStep`,
`SetStep`, `IfStep`, `PerformStep`, `AppendStep`, … with an explicit
`YetStep` for steps the parser cannot handle
(`deps/esmeta/src/main/scala/esmeta/lang/Step.scala`). Everything in
this research line rests on ECMA-262 having that layer.

The pipeline (README.md:138–145): **extract** → `esmeta.spec.Spec`
(grammar + algorithms + tables + type model); **compile** → IRES, an
IR for the *specification* (`src/main/scala/esmeta/compiler/Compiler.scala`);
**build-cfg** → a control-flow graph whose nodes and branches *are*
spec algorithm steps. The mechanized spec is thus simultaneously (i) an
executable JS interpreter (`eval`, `src/main/scala/esmeta/interpreter/`),
(ii) a coverage domain (statements/branches *of the spec*), and (iii) a
localization target (a failing test maps back to spec algorithms). This
**bidirectional anchoring** — every IR function knows its spec clause,
every spec clause knows its IR — is the load-bearing property from
which all the downstream tools fall out: JEST (differential testing +
test synthesis), JSTAR (type-checking the spec itself), JSAVER
(meta-level static analysis), the visualizer/double debugger.

**Extraction is not fully automatic, and the repo is honest about it.**
There is a curated manual layer: 39 hand-written IRES functions for
algorithms the compiler can't produce
(`src/main/resources/manuals/funcs/` — BigInt operations, list
helpers, …), a hand-written `RunJobs.algo`, and per-spec-version
**bugfix patches** applied to `spec.html` before extraction, keyed by
the pinned ecma262 submodule hash
(`src/main/scala/esmeta/util/ManualInfo.scala:31-32`,
`src/main/resources/manuals/bugfix/84b38ad8….patch`,
`Extractor.scala:28-37`). JISET's own numbers `[web]`: 95.03% of
algorithm steps auto-compiled on average over the four then-recent
spec versions; for ES10, 9,627 of 10,101 steps, with the remainder
hand-completed; the completed semantics then passed all 18,064
applicable Test262 tests, and the effort surfaced 9 spec errors in
ES10 (TC39-confirmed) plus 3 errors in the in-flight BigInt proposal.
Two readings for us: even with a step-structured source, extraction is
95%-plus-a-recorded-manual-register; and their standing
Test262 validation of the extracted interpreter
(`esmeta test262-test`, README.md:176–195 — 31,537 applicable tests)
is exactly the shape of our differential lower bound: a corpus
membership gate over the executable model.

Execution outcomes are a closed taxonomy
(`src/main/scala/esmeta/injector/ExitTag.scala`): `Normal`, `Timeout`,
`ThrowValue`, and — the interesting one — `SpecError`: *the spec
itself failed to execute here*. That is a first-class result, not an
embarrassment; see §2.1 on what JEST does with it.

## 2. JEST (ICSE 2021) in detail

### 2.1 N+1 differential testing and divergence classification

The framing (paper §I–II): under spec/implementation co-evolution,
**the spec is not the oracle** — both sides may be wrong. Classical
differential testing votes among N implementations; JEST adds the
mechanized spec as the +1: tests are *generated from* the spec with
assertions encoding the spec's predicted final state, then run on N=4
engines (V8, GraalJS, QuickJS, Moddable XS, all supporting ES11).

The classification rule is a majority vote followed by manual
confirmation (§II.C.5, §III.E): a small number of engines failing a
test → suspect those engines; most engines failing → suspect the
spec. Their measured separation (§IV.B) is strikingly bimodal:

| # failed engines | 1 | 2 | 3 | 4 | avg |
|---|---|---|---|---|---|
| engine bugs (44) | 38 | 6 | 0 | 0 | 1.14 |
| spec bugs (27) | 0 | 0 | 10 | 17 | 3.63 |

Results: **44 engine bugs** (V8 2 — both induced by spec bugs V8
faithfully implemented; GraalJS 16, including an uncatchable
`java.lang.IllegalStateException` crash on `++undefined`; QuickJS 6;
Moddable XS 20) and **27 spec bugs in ES11** across six root causes
(Table III): wrong property-key order for functions (12), missing
anonymous-function `name` removal (8), iterator-object vs
iterator-record confusion (1), the `oldvalue`/`oldValue` typo in
UpdateExpression (4), and two unhandled-abrupt-completion bugs — one
of which (ES11-6) was genuinely new, reported, and TC39-confirmed.
Spec-bug lifetimes ranged 209–1,793 days. Localization uses
spectrum-based fault localization (ER1b formula, method-level
aggregation) over spec algorithms as program elements; mean rank of
the culprit algorithm 3.19, 82.8% within top 5.

Two details worth stealing regardless of any verdict:

- **"The spec cannot execute this" is a conformance verdict.** The
  `oldvalue` typo made `x++` un-executable in the mechanized spec, so
  JEST emitted the program tagged `// Abort` and asked whether engines
  execute it (they all do, fine) — turning an extraction/spec
  execution failure into a located spec-bug report rather than a
  skipped case (§III.D.2, §IV.D).
- **Skeptical reading of the vote:** it needs N≥3 genuinely
  independent voters to separate; classification is statistical *then
  manual* (they hand-confirmed every attribution, §IV.B); and the
  mechanized spec is itself extracted from the artifact under
  judgment, so a JISET transcription bug is a third suspect the paper
  quietly folds into the manual check. Most of JEST's "spec bugs" are
  transcription-layer defects a step-structured spec makes possible
  (typos, missing `?` abrupt-completion marks) — a class Go's prose
  spec mostly cannot have; the Go analog surfaces as *ambiguity*
  instead.

### 2.2 Conformance-test synthesis: what it concretely does

**Coverage criterion: statement and branch coverage of the mechanized
spec** — ES11's 1,550 target algorithms contain 24,495 statements and
9,596 branches (§IV.A). The loop (§II.C, §III.A–C):

1. **Seed synthesis** from the grammar: a worklist shortest-string
   computation per non-terminal (Algorithm 1), then non-recursive
   enumeration of every production alternative using shortest strings
   as fill (Algorithm 2) — 1,125 programs in ~10 s covering 97.78%
   (397/406) of reachable syntax alternatives — plus a builtin-function
   synthesizer enumerating call shapes from extracted builtin
   signatures.
2. **Target selection + mutation**: pick a pool program touching one
   side of an uncovered spec branch; mutate it with five methods —
   nearest-syntax-tree mutation (the workhorse: 459 programs, 1,230
   new branches, Table I), random subtree replacement, string
   substitution from literals harvested *from spec conditions* (`-0`,
   `Infinity`, `"length"`, …), object substitution from spec
   property-access keys, and statement insertion biased toward control
   diverters. The pinned esmeta carries these as
   `fuzzer/mutator/{NearestMutator,RandomMutator,SpecStringMutator,StatementInserter,…}.scala`
   plus a post-paper `Remover.scala`.
3. **Assertion injection** (§III.D; `injector/Injector.scala` — run
   the program on the mechanized spec via `ExitStateExtractor`, read
   the final state, emit assertions): seven kinds — exception tag (as
   a first-line *comment*, because wrapping in try-catch changes
   semantics), abort tag, variable values (distinguishing `-0`/`+0`
   via `1/x`), object identity via representative paths, property
   descriptors, property-key *order* via `Reflect.ownKeys`, and
   internal slots via indirect getters (`Object.getPrototypeOf`,
   `Reflect.construct` with a dummy target, …).

Yield: 1,700 programs averaging **2.01 lines** (8.45 with assertions)
reaching 87.70% statement / 78.30% branch coverage of the spec —
versus Test262's 91.61% / 82.91% from 16,251 hand-written tests
averaging 49.67 lines. Per-assertion bug yield (Table II): exception
tag 21 and key-order 17 of the 44 engine bugs; variable values just 1.
The lesson is that the **observation surface** (what the assertions
can see: key order, descriptors, internal slots, -0) does the bug
finding, not program volume.

**PLDI 2023 follow-on** `[web]`: plain node/branch coverage saturates
because different language features share spec helper functions;
**feature-sensitive (k-FS) coverage** refines each requirement by the
innermost k enclosing language features (syntactic or built-in-API),
and **k-FCPS** adds the feature call path. Implemented in the pinned
checkout: `es/util/Coverage.scala:23` (`kFs`), `:453`
(`st.context.featureStack.take(kFs)`), views printed as
`@ feature[enclosing]:path` (`:474-475`). Evaluation `[web]`: against
ES13, 237,981 tests synthesized in 50 h under five criteria; 143
distinct conformance bugs across four engines and four transpilers, 85
developer-confirmed, 83 new.

**JSTAR** `[web]`: type analysis over the extracted IRES with
condition-based refinement, run across all 864 ECMAScript repo
versions 2018–2021; 157 type-bug reports, **93 true (59.2%
precision)**, 14 new, all 14 TC39-confirmed. (The campaign doc §3 says
"92 type bugs" — the abstract's number is 93 true of 157 reported;
worth a one-word correction, and the 59.2% precision is itself a
caution for our upstream policy: file verified entries only.)

## 3. Verdicts against the campaign mechanisms

### 3.0 Prior (a): "extraction doesn't transfer — Go's spec is prose, so there is nothing to extract an interpreter from"

**Verdict: the conclusion stands; the stated reason is half wrong.**

Reject interpreter extraction, yes: the thing that makes JISET
possible is ECMA-262's `<emu-alg>` step layer — a conventionalized
metalanguage with a closed AST — and Go's spec has no such layer; its
semantics lives in discursive paragraphs. And even *with* that layer,
extraction is 95%-plus-a-manual-supplement with per-version bugfix
patches (§1) — the cost model alone kills a Go version.

But "there is nothing to extract" is false, checked against the pinned
spec: `deps/go/doc/go_spec.html` at `go1.26.5` contains **62
`<pre class="ebnf">` blocks** — the formal grammar productions (28
further `class="grammar"` blocks hold the notation-defining
meta-grammar, token lists, operator-precedence and numeric-type
tables, and builtin signatures; precision added by audit +
delta-review) — and **236 plain `<pre>` blocks**,
mostly author-written examples. Two extractable objects exist:

- the **examples** — which is exactly mechanism 4.2, and note the
  inversion: ESMeta deliberately *excludes* examples from extraction
  (`:not([example])`, `Extractor.scala:87,107`) because for them
  examples are noise beside the normative steps; for us, with no
  normative steps to extract, the examples are the extractable
  normative-adjacent content;
- the **EBNF** — a possible cross-check of frontend/grammar
  assumptions (e.g. validating that corpus generators and
  `tools/nativefrontend` assumptions span the productions). Low
  priority; note it, don't schedule it.

The JISET property actually worth transferring is not extraction but
**bidirectional anchoring** — every machine region knowing its spec
clause and vice versa is what made their coverage, localization, and
visualization fall out for free. For us that is 4.1/covmap
connections, built by hand at clause-segment granularity rather than
generated at step granularity. Our machine stays hand-built and
differentially grounded; no change to the campaign's non-goal ("no
SpecTec-for-Go").

### 3.1 Mechanism 4.1 (clause anchors / covmap) — ADAPT

The ESMeta line is the strongest existence proof surveyed that
machine-checkable spec↔artifact links pay for themselves: their
visualizer, SBFL localization, and coverage-of-the-spec metric are all
one anchoring graph viewed three ways. Our version is deliberately
coarser (clause segments ↔ envelope arguments / interpreter regions /
corpus cases) because our semantics is not spec-shaped — that is
right-sized, not a deficiency. The covmap "which spec sections have
zero witnesses" query (campaign §8.1) is precisely their spec-coverage
number rebuilt at clause granularity.

### 3.2 Mechanism 4.2 (spec-example corpus) — ADOPT, reinforced

Two JEST lessons sharpen the plan:

- **Compact programs, strong assertions.** 1,700 two-line programs
  outperformed 16,251 fifty-line tests per unit of content; and the
  assertion kinds did the work (Exc + Key = 38 of 44 engine bugs). For
  the P3 extractor: wrap each runnable example with the *strongest
  observation available* (exit status + printed values + panic
  identity), not a bare "does it run".
- **The exception-tag-in-comment trick generalizes**: JEST tags
  expected outcome out-of-band because in-band harnessing (try-catch)
  perturbs semantics. Our corpus's expected-outcome metadata should
  likewise stay outside the program text — which our manifest rows
  already do; keep it that way for intentionally-invalid examples
  (must-not-compile is metadata, never a code wrapper).

### 3.3 Mechanism 4.3 (divergence ledger) — ADOPT JEST's discipline, with a structural caveat (prior (b), first half)

Agree with the prior: a differential red is not automatically ours;
the ledger needs `gc-bug` and `spec-bug` as first-class verdicts, and
JEST proves both kinds occur in the wild in quantity (44 vs 27).

The caveat the prior misses: **JEST's classification is cheap because
it is a vote over N=4 independent engines** (the 1.14-vs-3.63
separation in §2.1 is the whole mechanism). We run N=1 (gc). At N=1
every kind-attribution is *argued* — spec anchor + probe + reasoning —
never voted. That is workable (it is what the ledger's verification
step already requires) but it means classification stays expensive
per entry, and it is a concrete, quantified argument for the
cross-implementation lane (§3.4).

Two adoptions beyond the prior:

- **`SpecError`/`Abort` as ledger feed**: JEST turned
  "the mechanized spec cannot execute this program" into located spec
  bugs. Our analog: a `stuck`/`unsupported` red whose triage shows the
  *spec text* (not our code) is incoherent or silent at that point is
  a ledger candidate (`spec-ambiguity`), not only a bug-in-us. The
  triage flow should ask that question explicitly.
- **Expected mix differs from JS**: JEST's spec bugs were mostly
  transcription-layer defects (typos, missing `?`) that a
  step-structured spec makes expressible; Go's prose spec expresses
  the same defect mass as *ambiguity*. Predict more `spec-ambiguity`
  than `spec-bug` entries; the doctrine's prior "almost always ours"
  stands for machine divergences, since our machine is not extracted
  from the text being judged.

### 3.4 Mechanism 4.5 (cross-implementation lane) — ADOPT-leaning at P5

JEST is the quantitative case for independent voters: without them,
engine-vs-spec attribution would have been manual for all 71 bugs.
Carry the caveats already in the plan (gccgo lags, TinyGo diverges
deliberately; neither is an oracle) plus one from here: gc and the Go
spec are stewarded by one team, so Go's voters are less independent of
the spec than JS engines are of TC39 — expect the vote to be
suggestive, not decisive, and keep the lane an evidence generator, not
a gate. The JEST separation table belongs in the P5 decision memo.

### 3.5 Mechanism 4.6 (upstream feedback) — ADOPT

Strongest precedent in the survey: TC39 confirmed JEST's new report
(ES11-6) and JSTAR's 14 new reports `[web]`; JISET's 9 ES10 errors
were confirmed `[web]`; and two engine teams (GraalJS, Moddable)
asked to *adopt the generated suite into their CI* (paper §IV.C,
verbatim quotes). Formalization efforts earn standing by filing good
reports — and JSTAR's 59.2% precision is the cautionary half:
per-filing verification and Mike's sign-off, as the plan already says.

### 3.6 Prior (b), second half: coverage-guided synthesis from GoCore's branch structure — ADAPT

Agree with studying it; disagree with the framing "the inverse of
grossmith's seed-generation, complementary to it" in one respect:
grossmith already is a guided generator (weighted construct swarm,
capability profiles, replayable draws, closed verdict taxonomy —
`deps/grossmith/README.md`). What neither grossmith nor our corpus has
is **coverage feedback from our machine** — grossmith steers by its
generator-side model, JEST steers by the semantic artifact's own
branches, and that difference is what found the shared-helper-shadowed
paths (and is exactly our audit doctrine's "unexercised paths" class,
CLAUDE.md audit section). The cheap version is not a second generator:
instrument the executable interpreter with a fired-rule/branch trace
(it is total and executable; a trace is a side channel, not a
semantics change), aggregate over the corpus, and hand the
uncovered-branch report to grossmith as targets. The k-FS refinement
`[web]` maps cleanly: our shared helpers (assignment machinery,
conversion, channel registry ops) will saturate plain branch coverage
early; contextualizing by innermost enclosing GoCore constructor is
the analog of their innermost-feature view. All of this is P5
material — coordinate with grossmith, do not build during this
campaign.

One long-game note, not scoped: JEST's assertion injection makes the
mechanized semantics *emit a conformance suite* (programs + predicted
outcomes) that engine teams wanted. A machine-generated Go conformance
suite is the same artifact class as the Sail endgame the campaign
already parks — park it alongside, with this precedent attached.

## 4. Concrete next actions

- Correct campaign §3's JSTAR figure (92 → 93 true bugs of 157
  reported, 59.2% precision `[web]`) next time that doc is touched.
- P4 ledger schema: add the triage question "is this red a
  spec-incoherence rather than a machine bug?" (the `SpecError`
  lesson), and record that kind-attribution at N=1 is argued, not
  voted, citing this note.
- Carry §2.1's vote-separation table (avg 1.14 vs 3.63 failing
  engines) into the P5 decision memo as the quantitative case for
  mechanism 4.5.
- P3 extractor: inventory all 326 `<pre>` blocks — 236 bare + 62
  `class="ebnf"` + 28 `class="grammar"` (the grammar blocks were
  dropped from this bullet's original phrasing; audit correction
  2026-08-17) — classify, don't run the ebnf/grammar ones; wrap
  runnable examples with the strongest
  available observation per JEST's assertion-yield data (§2.2);
  expected outcomes stay out-of-band.
- P5: scope an interpreter fired-branch trace as the machine-side
  coverage instrument feeding grossmith targets; evaluate
  k-FS-style contextualization by enclosing constructor before
  committing to build anything.

## 5. Could not verify

- **JEST figures**: text-only PDF extraction; Figures 1(a), 2, 4, 5
  (the algorithm excerpt, architecture, coverage curves, rank
  histogram) were not readable — coverage numbers above come from the
  running text, not the graphs.
- **JISET, JSTAR, PLDI 2023 details**: all numbers tagged `[web]` are
  from search results and the ASE 2021 abstract page, not from the
  papers themselves; no section-level cites possible. The JISET
  "95.03% / 9,627 of 10,101 / 18,064 tests" figures in particular are
  reconstructed from a search summary.
- **Nothing was executed**: esmeta was read, not built (JDK/sbt not
  attempted; the `ecma262` and `tests/test262` submodules are
  uninitialized in `deps/esmeta`). Pipeline claims are grounded in
  source reading only.
- **JSAVER (ESEC/FSE 2022)** not studied beyond the README; its
  `analyze` command is "temporarily removed" in the pinned rev
  (`deps/esmeta/README.md:381-388`), so no source to read there.
- The 27-spec-bug count reads Table III's `#` column as instance
  counts (12+8+1+4+1+1=27) over six root causes; the paper uses both
  framings and I did not find an explicit reconciliation sentence.
- grossmith was read from the main checkout
  (`/home/dev/projects/golean/deps/grossmith`, README dated
  2026-08-09), not from this worktree's `deps/`; its current tip may
  differ.
