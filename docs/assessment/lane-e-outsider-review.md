# Lane E — the outsider review

**Reviewer brief:** a skeptical programming-languages semanticist, asked
whether GoLean is a credible model of Go and what would be required
before citing or building on it. Full scope, no downscoping. The owner's
mandate is explicit: recorded set-asides and "we've decided not to model
X" entries are IN SCOPE for challenge.

**Object reviewed:** the tree at `.claude/worktrees/fidelity`, commit tip
of `main` (post repo-split, 2026-08-31). GoCore interpreter (30,710 lines
Lean), native frontend (15,407 lines Go + 1,446 lines Lean decoder),
2,478-case executable differential corpus, 390-case compile-negative
corpus, latitude inventory (1,465 lines), language coverage ledger (158
spec-section anchors), BUGS.md (69 entries).

**Method:** I read the doctrine documents, the latitude census, the
ledgers, and the prior-art notes directly; I commissioned four
independent forensic sweeps of the differential apparatus, the
concurrency/race machinery, the frontend/generics/stdlib boundary, and
the value/memory/fuel core; and I ran the artifact myself
(`scripts/capped scripts/diff-one`, a membership-lane sweep) rather than
taking the records on trust. Where I quote a number I have re-derived it
from the tree, not from the prose. Everything below is [AGENT] reviewer
judgment.

---

## 1. VERDICT

# CREDIBLE-WITH-DEMANDS

I would cite this artifact today as *"an executable, total, adequacy-proved
operational semantics for a substantial sequential fragment of Go 1.26,
differentially validated against gc go1.26.5/linux-amd64 over ~2,300
hand-authored fixtures and ~80,000 generated programs, with an unusually
complete and honest register of its own approximations."* That sentence is
defensible and it is worth more than most artifacts of this age can claim.

I would **not** cite it as *"the weakest machine Go permits"*, nor as
*"incredibly well validated"* without qualification, and I would not
accept any concurrency claim built over it. The gap between the two
sentences is the subject of this review. In brief: the project has built
an excellent instrument for the **lower** bound and has confused the
completeness of its *bookkeeping* about the upper bound with *evidence*
for it. The upper-bound direction — modeled ⊆ permitted, and the far
harder permitted ⊆ modeled — has essentially no mechanized instrument
pointed at it. I measured what there is: across the entire membership
lane — the only apparatus that compares a modeled *set* against the
oracle — the model enumerates **441 behaviors of which real Go has ever
been observed to produce 45**, and the lane is 25 rows out of 2,478.
Meanwhile 24 of 40 latitude rows are pinned or narrowed strictly
inside what Go allows, five of them *known* to sit beside gc's own
realization; the load-bearing soundness theorem for the entire
concurrency design is a `def` that the file itself labels "REFUTABLE AS
WRITTEN"; and roughly 17,000 lines of unverified translation sit *inside*
the declared trusted surface with 249 catalogued obligations and zero
discharged, a boundary that has twice shipped silent wrong answers for a
month at a time. None of these is fatal. All of them are load-bearing for
the specific claim the owner wants to make, and each has a concrete
discharge path. Hence: credible, with demands.

A note on calibration, offered in good faith. Measured against where CH2O
and Cerberus *were* at comparable maturity, this project is ahead on
executable differential volume and far ahead on self-documentation, and
behind on exactly the two things those projects earned their citations
with: **metatheory** (CH2O) and **multi-implementation empirical data**
(Cerberus). The demands below are mostly requests to buy those two.

---

## 2. What the project gets RIGHT

I want to be specific here, because the criticism that follows is sharper
if it is clear what it is *not* attacking.

### 2.1 The two-bounds doctrine is the correct frame, and it is stated better than the literature states it

`docs/2026-08-11_essence-of-go-doctrine.md` gets the epistemology right in
a way most semantics papers do not bother to. "Differential testing
establishes the LOWER bound… its entire meaning is membership" and "the
oracle can never validate the model's width" is exactly the observation
that Cerberus had to discover the expensive way, and that a great many
"validated semantics" papers quietly elide by reporting a test-suite pass
rate as if it were a fidelity measure. The accompanying bug definition —
`observed ∉ modeled` is *always* red, never latitude — is a genuine
commitment with teeth, and I found it actually enforced: the W3.2
send-then-spin wedge was recorded verbatim as "*`observed ∉ modeled` at
the current tip… Definitionally a bug*" and the machine was widened
rather than the record softened. That is the behavior of a serious
project.

The framing is also, to my knowledge, novel in one respect worth
crediting: most executable-semantics work treats nondeterminism as an
obstacle to testing. This project treats *width* as the product and
testing as the cheap lower-bound instrument. That inversion is right, and
it is the reason the latitude inventory exists at all.

### 2.2 The latitude census is the best artifact in the repository

`docs/2026-08-11_latitude-inventory.md` is a genuinely excellent
document, and I do not say that lightly. Forty numbered latitude rows,
each with a class tag ((a) enveloped / (b) pinned / (b-n) narrowed / (c)
forced / (d) unknown / (q) quotient-discharged / REFUSED), each with a
stated plausible envelope, a re-envelope obligation, a cost estimate, and
an evidence class. Section 10 *enumerates* rather than summarizes and
carries a reading rule distinguishing membership from mention. Section
10.1 records class movement with dates and the reason each earlier count
was wrong. I re-derived the (a)=9, (b)=17, (b-n)=7 counts against the
heading tags myself; they close exactly.

The comparable object in the field is Cerberus's question ledger. This is
of the same kind and, per-row, is more precise about the *disposition* —
Cerberus tells you what implementations do; this tells you what the model
does, what it could do, what it would cost to widen it, and who ruled.
I have not seen a better instance of this genre.

Two things elevate it above bookkeeping. First, **the choice-site census
is code**: `ChoiceSite` is a datatype with an exhaustiveness-checked
policy table in `State.lean`, so a new nondeterminism site cannot be added
without appearing in the census. That is the right way to prevent a census
from drifting from the machine — and the document is candid that the
prose *mirror* of the table did drift (7 rows against 9 constructors) and
that "the exhaustiveness check is real but it protects the CODE, not this
table". Second, the **(q) ENVELOPE-BY-QUOTIENT** class is a real
contribution: rather than exercising allocator latitude, prove every
conforming address choice observationally equal and discharge the
obligation by theorem. That is the right move, it is properly conditioned
on the observation surface, and I have a demand about the condition below.

### 2.3 The choice-tape reification is well-executed

Nondeterminism is external to the evaluator: `Choices := List Nat`,
consumed through `Choices.consumeAt site bound` at nine census'd sites,
with a declared per-site policy including what slot 0 means. This is the
right architecture — it is CH2O's redex-nondeterminism idea done as an
oracle tape, and it makes the model's width a *first-class, enumerable*
object rather than a property of the interpreter's control flow. The
payoff is real: `golean coverage-observations` can enumerate the
observation set by DFS over the choice tree, and `engine=dedup` runs are
backed by a *verified Lean checker* (`checkCertM_slowObs` in
`EnumDedupSound.lean`, an `↔` between the certificate's observation set
and the driver's). A kernel-checked enumeration certificate is stronger
than anything in the comparable C or JS artifacts.

The site policies are also honestly designed: every slot-0 default is
chosen to reproduce gc's realized point, so the empty stream is the
"gc-shaped" execution and any widening is visible as a non-empty stream.
That is a good engineering decision and it is documented as such.

### 2.4 Fail-closed discipline is real, consistently applied, and visible in the code

This is not a slogan here. 288 `unsup(...)` refusal sites in the frontend
with ~250 distinct message strings, each naming its cause. Float→int
out-of-range **refuses** rather than picking amd64's `1<<63` or arm64's
saturation. `uintptr` observations refuse rather than aliasing to
`uint64`. The enumerator's caps are hard errors, not truncations: a site
bound exceeding the row's declared width produces *"the width assertion
is REFUTED (mechanically, at pick position …)"*; the observation cap and
work cap error rather than returning a partial set. Shim runtime refusals
were deliberately made **uncatchable by `recover()`** after an audit found
that ordinary defensive idioms were converting them into silent wrong
answers. `scripts/diff-coverage` refuses to run at all if the live
toolchain differs from `baselines/go-oracle-pin`.

Set against the field: this is stricter than CH2O (which can launder
ambiguity into undefined behavior) and stricter than most K-framework
semantics (where an unmatched rule is a stuck term that tooling often
reports as success). The inventory's own gloss is correct and worth
quoting: *"Go has no sequential UB, so our analog is the REFUSED class, a
tool-level visible red, never a semantic verdict."*

I found three fail-**open** exceptions. They are in my demands (D7, D9);
their existence does not undercut the general judgment, but they are in
exactly the places where fail-open is most dangerous.

### 2.5 The semantic core is a real, total, adequacy-proved artifact

- No `sorry`, no `axiom`, no `native_decide` anywhere in `GoLean/`;
  no `partial` in `GoLean/GoCore/`. I verified this by grep.
- Adequacy is proved **both directions**: `stepFn_sound` (executable ⟹
  relation) and `step_complete` (relation ⟹ executable, at some stream),
  plus `step_complete_any_wf` (at every stream under well-formedness) and
  the driver-level lifts. Crucially, the `Prop` relation's premises call
  *the same total functions* the executable calls, so the two cannot
  drift into a re-specification — a design choice I would recommend to
  others.
- The memory model is a symbolic access-path heap (`Loc ::= base | field
  | index`) over structured values, with `Loc`-keyed cells and path-prefix
  aliasing. It handles the cases that matter: `&s.f` mutation is visible
  through the struct; slices are genuine views over a shared backing cell
  with Go-exact `cap` arithmetic including the three-index form; `&s[i]`
  is bounds-checked against `len` not `cap`. This is a cleaner design
  than byte-addressing for a language with no `unsafe` in scope, and it
  buys the (q) quotient discharge.
- Floats are a **bit-precise softfloat transcribed from
  `runtime/softfloat64.go` at the pinned version**, with a correctly-
  rounded rational→format kernel. `fneg` is a sign flip, not `0 - x`.
  This is more careful than most semantics get about floats.
- Strings are byte arrays with an exact `unicode/utf8` accept-range
  decoder (invalid/surrogate/overlong/truncated ⇒ U+FFFD width 1).
- Fuel exhaustion is a **distinct outcome constructor**, `.fuelOut`, split
  out precisely so that "every run ends `.ok` or `.fuelOut`" is statable,
  and every terminal and blocked classification is checked *before* the
  fuel decrement, so a finished or deadlocked program can never be
  misreported as exhaustion. That is the correct design and many
  fuel-based semantics get it wrong.

### 2.6 The differential discipline exceeds what most artifacts do

- The oracle is **pinned exactly** (`go1.26.5`) and the harness refuses to
  run off-pin; the CI pin was tightened from `1.26.x` to `1.26.5` after
  an actual incident where go1.26.6 moved the oracle under a nightly.
- `GO111MODULE=off` and `GODEBUG=panicnil=0` are pinned deliberately so
  gc aligns with the model by construction rather than by coincidence.
- The observation encoding is genuinely careful where it reaches: integer
  values carry their `reflect.Kind` tag (so an `int8`/`int32` confusion is
  caught, not silently coerced); floats are compared as **raw IEEE bit
  patterns**; strings as byte arrays; the decoder is a strict schema
  validator that *rejects* an out-of-range value rather than comparing it.
- Panic message text and `fatal error:` lines are compared literally.
- The negative/membership/confluent/racy lane taxonomy is a real design,
  and `scripts/diff-coverage`'s own lane captions state the epistemic
  limits more sharply than most external audits would — e.g. `strict` is
  captioned *"Structurally BLIND to scheduling: says nothing about
  interleaving"*, and membership is captioned *"Does NOT show unexhibited
  members are Go-realizable… too-wide has no oracle."* Self-description
  this honest is rare and I want it on the record.
- There **is** a fuzzing lane, and it is better than I expected going in:
  the grossmith campaign (Microsmith fork) judged **79,800 generated
  programs** with 3 observation mismatches, and its metamorphic and
  cross-arch discrimination controls both passed. It found a **real gc
  bug** (a 32-bit truncation in an optimized constant fold) and a second
  gc assembler refusal. The finding note's own summary — *"The
  differential oracle was wrong more often than the machine was"* — is
  the kind of result that earns credibility. Finding bugs in the artifact
  you are formalizing is the CH2O/Cerberus/JEST signature, and this
  project has it.

### 2.7 Prior-art engagement is genuine, not decorative

`docs/2026-08-17_prior-art-ch2o-cerberus.md` reads both primary sources
and comes back with a *disagreement* with the project's own doctrine —
that "Cerberus's de-facto-vs-ISO distinction *is* our two-bounds doctrine
independently reinvented" is imprecise, because Cerberus faced a
third-artifact situation (a candidate de-facto model) that Go's
compatibility promise prevents. That is a correct and subtle reading, and
a note that argues with its own charter is doing real work. The
Featherweight Go note correctly identifies that FG settles the dispatch
question and not the generics-implementation question, and recommends
NO-GO on a weak-memory arc — a defensible call.

### 2.8 Honest reporting, sustained

The records repeatedly report against interest: the map-iteration snapshot
narrowing recorded as a *dead* narrowing and then surgically removed; the
census mirror drift self-reported ("a census two sites short is a census
of a different machine"); BUG-002 carried as an open known-wrong
concurrency semantics with *no* pinning case and explicitly exempted from
the CI check rather than quietly closed; the frontend census reporting
that its own first pass found two silent wrong answers that had been
shipping green for a month. A project that reports its own month-long
silent failures is a project whose other reports I can weight.

**Summary of section 2.** Execution matches ambition on the lower bound,
on fail-closed discipline, on the core's totality and adequacy, and on
self-documentation. Execution does *not* match ambition on the upper
bound — which is, by the doctrine's own words, "the product."

---

## 3. MY DEMANDS

Ranked by (risk to the fidelity claim × tractability). Each states the
wrong conclusion a reader could reach today, the evidence that would
discharge it, and a rough cost. I use S/M/L/XL for effort
(S ≈ days, M ≈ weeks, L ≈ months, XL ≈ research programme).

---

### D1 — Break the one-implementation / one-version / one-platform / one-optimization-level monoculture

**Cost: M** (version and optimization sweeps are S; a second architecture
is M; a second implementation is L).

**What is true today.** Everything the doctrine calls the LOWER bound
rests on a single point in a four-dimensional space: gc, `go1.26.5`,
`linux/amd64` at default `GOAMD64`, at default optimization. I verified
there is no `GOARCH`/`GOOS` variation, no `gccgo`, no TinyGo, no
`-gcflags` variation, and no `strategy.matrix` in the CI workflow. The
`gofrontend` and `tinygo` rows in `scripts/setup-deps` are *floating* —
"pin at first real use" — and first real use has not arrived. The
doctrine names six evidence classes for the upper bound; **XIMPL
(cross-implementation) has zero instances**, and the register's own entry
#9 sharpens #3 to say the base is one *platform*, not merely one
implementation.

**The wrong conclusion available today.** A reader sees "differential
validation against gc over 2,478 fixtures" and concludes that
`observed ⊆ modeled` has been tested for *Go*. It has been tested for one
build of one implementation. This is not hypothetical risk — the project's
own records already contain four places where the single point is known
to be unrepresentative:

- **R4 (float fusion):** the model narrows to per-op rounding; "gc/arm64
  and gc/amd64-v3 executions of programs containing fusable patterns are
  **OUTSIDE the envelope**". The tripwire fixture `floats/fma-shape`
  exists but there is no runner that can trip it.
- **R1 (`int`/`uint` width):** pinned 64; the spec permits 32. §7 places
  re-envelope "below the line… waits on any 32-bit oracle lane" — i.e.
  the item is blocked on precisely the lane that does not exist.
- **R6 (float→int out of range):** refused *because* amd64 and arm64
  differ. The refusal is honest but it is a coverage hole created by the
  monoculture.
- **R15 (zero-size variable address identity):** the model pins
  never-same; gc is **probed non-single-valued**. A standing divergence.

**What would discharge it.** In ascending cost:

1. **A version sweep.** Run the full corpus against go1.25.x and (when
   available) go1.27.x, with the language version held at 1.26 via
   `go.mod`. The corpus has no `go.mod` today — `docs/spec-sources.md`
   admits the three-leg agreement rule "has no object" and is running as a
   two-leg check. Give the corpus a `go.mod`, then this sweep is nearly
   free and it directly tests the version-pin story. **Cost S.**
2. **An optimization sweep.** Every build today is plain `go run .`. Add
   `-gcflags=all='-N -l'` and `GOAMD64=v3` legs. The grossmith campaign
   already showed a compile-mode instability class exists (§3, the
   assembler refusal), so this axis is known live. **Cost S.**
3. **An arm64 leg**, under qemu-user if no runner is available. This
   single lane converts R4, R6 and R15 from recorded assertions into
   tested ones, and it is the cheapest thing that can *falsify* the
   float narrowing. **Cost M.**
4. **A second implementation.** `gccgo` is the realistic target (TinyGo's
   fragment is too different). Even a reduced corpus leg would produce the
   first XIMPL evidence the doctrine has been asking for since August.
   **Cost L.**

**Field calibration.** This is the single largest gap against Cerberus,
whose credibility rests substantially on per-question, per-implementation
experimental data across gcc/clang/icc at multiple optimization levels,
plus a practitioner survey. The project explicitly declined the survey
(defensibly — Go's ambiguity record is public and minable) but it has not
substituted the *implementation* half, which is the part that actually
bounds the model. A referee who knows Cerberus will ask this question
first, and "the Go 1 compatibility promise means observed ⊆ permitted
actually holds" is an argument about *conformance*, not about *width* — it
does not tell you gc realizes the whole envelope, and R15 already shows it
does not.

---

### D2 — Run Go's own semantic test suite

**Cost: M.**

**What is true today.** `docs/spec-sources.md` pins the whole `golang/go`
repo and describes `test/` — thousands of small programs, many named
`issueNNNNN.go` — as *"A curated historical map of gc semantic bugs…
Corpus-seed goldmine."* It has never been run. I grepped `scripts/`,
`tools/` and the workflow for any reference to `deps/go/test`,
`fixedbugs`, or the `run.go` driver: nothing. The 2,478-case corpus is
authored in-house, and the fuzzing lane is a separate project whose
generator, by its own §8, emits **no pointers, no floats, no goroutines,
no channels, no generics, no runes, no `goto`, and no imports**.

**The wrong conclusion available today.** "2,478 fixtures + 79,800 fuzzed
programs" reads as broad coverage. It is broad over a *self-selected*
region. The corpus was written by the same effort that wrote the
semantics, which is a closed loop: it tests what the authors thought to
test. The evidence that this bites is in the project's own records —
**BUG-066** (`expensive()[:]` evaluated the base twice; "gc 1 call,
machine 2, **status `ok` on both sides**") and **BUG-067** (wire func
types dropped the variadic bit; "gc `false true`, machine `true true`")
were both **silent wrong answers**, both shipped green for roughly a
month, and both were found by a *documentation census*, not by the
2,478-case corpus and not by the 79,800-program fuzzer. A corpus that
cannot see a double-evaluation bug for a month is a corpus with a
structural blind spot, and the cheapest fix for a structural blind spot
is a corpus somebody else wrote.

**What would discharge it.** Port `$GOROOT/test` (the `// run`-directive
subset, plus `test/fixedbugs`) through the differential harness, with
every refusal classified against the frontier ledger. I expect a large
initial refusal rate; that is fine and is itself the deliverable — it
converts "143 `frontend-export` refusals" from a number about the
in-house corpus into a number about *Go's own conformance surface*.
Report: N attempted / N ran / N passed / N refused-with-FR-row.

**Field calibration.** This is the demand I would press hardest in review,
because it is the field's standard move and its absence is conspicuous.
JSCert's credibility came from JSRef against **test262**, the language's
own suite. CH2O and Cerberus both ran against the GCC torture suite and
the Ellison–Roșu/KCC test set. SpecTec's whole loop is the official
`.wast` suite — 49,833 assertions — and the project's *own* prior-art note
says so, and then says of its own arrangement: *"the 'interpreter ⟷
official test suite' loop is our differential gate"*. That sentence is not
yet true. Go ships the analogue of test262 in the repository this project
already pins. Not running it is the largest cheap win available.

---

### D3 — Widen the observation channel, and re-audit every claim conditioned on it

**Cost: M.**

**What is true today.** I traced the channel end to end. The corpus
`main()` is **stripped and discarded**; the harness synthesizes a new
`main` that calls one named subject function with integer arguments and
reflects over its **return values**, emitting one line of JSON. The
comparison is structural JSON equality (`runObservationEq`, `CLI.lean`).

What is compared: return values (bools; all ten integer kinds *with kind
tags*; floats as raw bits; strings as bytes; arrays; structs by field name
and type name; interfaces by dynamic type *name* plus boxed value), the
terminal class (`ok`/`panic`/`deadlock`/`race`/`fatal`), and panic/fatal
message text.

What is **not** compared, and this is the important list:

- **stdout.** Any output the subject prints makes the case *fail* as
  unparseable. Printing is not a weak channel here; it is contraband. So
  **effect sequences are not observed at all** unless an author hand-codes
  them into a return value.
- **Slices, maps, pointers, channels, funcs.** `reflect.Slice`, `.Map`,
  `.Ptr`, `.Chan`, `.Func` all hit the encoder's `default:` arm and hard
  error. Every slice/map/pointer test must launder its result through an
  author-chosen integer checksum (e.g. `len(t)*100 + t[0]*10 + t[1]`).
  The Lean decoder *has* `slice`/`map` tags; the Go encoder can never emit
  them.
- Allocation counts, layout, addresses, GC, timing, `GOMAXPROCS`, goroutine
  interleavings, and — for `race` and `deadlock` cases — **any detail
  whatsoever**: the entire TSan report is discarded and replaced with a
  fixed synthetic string, so those 21+19 cases compare a one-bit verdict.

**The wrong conclusion available today.** Three of them.

1. *"2,478 differential cases validate the semantics"* — they validate a
   projection of it. BUG-066 and BUG-067 are precisely the bugs this
   projection cannot see: a doubled *effect* with an identical *return
   value*, and a type-metadata bit that only surfaces through a
   comma-ok assert nobody had written. The class is not exotic; it is
   the class of every evaluation-order and aliasing bug.
2. *"Register #6's allocator latitude is discharged by quotient"* — the
   doctrine correctly conditions this: the discharge holds *"CONDITIONAL
   on the modeled observation surface (pointer equality only): an
   address-exposing channel (`%p`, pointer order, `unsafe`) re-opens it."*
   Good. But **nothing guards the condition**. The condition is a property
   of `CLI.lean`'s encoder, and there is no test, lint, or comment at the
   encoder that says "widening this re-opens register #6". A future slice
   that adds pointer observation would silently invalidate a discharged
   register entry. Conditional discharges need mechanical tripwires, not
   prose.

   It is worse than that, and I record this as an independent
   confirmation of Lane C's F1: the discharging theorem
   **`Frame.allocatorIndependence` is not in this repository**. I grepped
   for it — it appears only in prose (the doctrine's register #6, the
   inventory's C11) and left with the 2026-08-31 split; it now lives only
   on `park/reasoning-2026-08-31`. So the register's sole
   theorem-discharged entry currently cites a theorem this repo neither
   contains nor builds, against a machine that can now drift from the one
   the theorem was proved about with nothing to catch it. A discharged
   obligation whose proof is not in the build is not discharged.
3. Similarly load-bearing and similarly unguarded: the `errors.New` shim's
   unobservability argument depends on `%T` staying refused (census row
   G-24), and G-20's soundness depends on `%w`'s refusal. These are
   **cross-file invariants that nothing checks**.

**What would discharge it.**

1. **An effect-trace channel.** Add an ordered event log (a monotone
   append that both sides emit and the harness compares as a *sequence*)
   so evaluation order, call counts, and effect interleaving are directly
   observable rather than checksum-encoded. This is the single change that
   would have caught BUG-066 on day one. **Cost M.**
2. **Direct slice/map/pointer observation** with a declared canonical
   encoding — slices as (elements, len, cap), maps as a sorted entry list
   plus a separate order-observable variant, pointers as an *aliasing
   graph* (which returned pointers are equal to which) rather than
   addresses. The aliasing-graph form is exactly right for this model: it
   is observable, it is what the (q) quotient is about, and it keeps the
   quotient's condition satisfied while vastly widening what is checked.
   **Cost M.**
3. **Mechanical guards on every observation-surface-conditional claim.** A
   lint that fails if the encoder gains a kind while register #6 /G-20/
   G-24 remain marked discharged. **Cost S.** This one I would treat as
   non-negotiable regardless of the rest: an unguarded conditional
   discharge is a fail-open in the *records*, and this project's charter
   forbids fail-open.

---

### D4 — Either prove a weakened NPDRF reduction, or scope every concurrency statement to coarse schedules, explicitly and everywhere

**Cost: XL to prove; S to scope.**

**What is true today.** This is the most serious substantive gap and the
project states it with complete honesty, which is why I can state it
crisply. The design schedules goroutine interleaving **only at registry
boundaries** (channel/sync apply positions, `go` spawns, `.opDone` op
completions, loop back-edges, parked shapes, terminals). Its soundness
rests on an NPDRF-style reduction: race-free programs behave identically
under registry-point scheduling and full per-step interleaving. That
reduction is `NPDRF.lean`'s headline, and it is a `def`:

```lean
def NPDRFReduction : Prop :=
  ∀ m₀ : MultiConfig, ¬ RacyFine m₀ →
    ∀ res, ReachesMFine m₀ res ↔ ReachesM m₀ res
```

carrying the caption *"THE NPDRF REDUCTION STATEMENT — DRAFT FORM,
REFUTABLE AS WRITTEN… Nothing may cite this — not even as a proof
target."* Of the eight theorems in the file, the reachability one that is
proved is `reachesM_le_fine` — coarse ⊆ fine, the direction that is
unconditional and useless. The direction that would license the design,
fine ⊆ coarse for race-free programs, is absent, and obstruction 4 records
that the statement is **false as written** (main's exit discards
goroutines mid-flight and `PoolResult.done` carries the whole
`ExecState`). Obstruction 6 records that the proved mover lemmas are
**cross-root only** — same-root disjoint paths, which is exactly the
`appendSlice`/`copySlice`/`clearSlice`/`sortSlice` class, have no lemma,
and store/store commutation is "unproved in any form."

Two further facts compound it. First, even `StepMFine` — the "full"
interleaving relation — interleaves at *the model's* machine-step
granularity, and the file itself flags that "the machine-step ↔
Go-atomicity correspondence is the granularity ledger's separate,
standing obligation," undischarged. `appendSlice` spill, `copySlice`,
`clearSlice` and `sortSlice` are each **one step** — a whole sort is one
step — and U-5 records that `slices.Sort` is one step while the
interchangeable `slices.SortFunc` lowers to a per-element loop: **two
granularities for one Go operation**. Second, the design's own research
note ends: *"Until (iv) is built, any concurrency soundness claim must
carry it as a stated assumption."* It has not been built.

**The wrong conclusion available today.** A downstream consumer — and
there is a downstream consumer, the reasoning repo — proves `∀ streams,
P` over `execProgLoop` and reads it as "for all Go schedules, P". It is
not. It is "for all *coarse* schedules of the model", and the bridge to
real Go executions is the missing theorem. The gap is not theoretical: the
boundary set has been found empirically incomplete **twice** (BUG-040's
missing post-spawn point; the W3.2 send-then-spin wedge where gc's
observation was outside the machine's *entire* stream envelope, 511/511
fuel-out). Both were fixed by adding boundaries. Nothing rules out a
third — and I note that **function entry/return is not a boundary**, so a
registry-free *recursive* spinner is still unpreemptable in the model
where gc preempts it asynchronously.

**What would discharge it.**

1. **Immediately (cost S), and I would treat this as mandatory:** rule the
   weakened statement (post-state scoped to main-reachable locations, or
   main's readout only), record it, and put a scope sentence on every
   artifact that quantifies over streams — `execProgLoop`,
   `allStreamsOkPool`, `checkCertM_slowObs`, and every membership/racy
   corpus row — reading "coarse (registry-point) schedules; transfer to
   real Go executions is conditional on the unproved NPDRF reduction."
   A precision note in the project's favour, since I checked it:
   `execProgLoop_ok_of_allStreamsOkPool`'s docstring *does* say "on every
   **modeled** schedule", which is accurate. But the theorem *statement*
   reads `∀ ch : Choices`, and "for all choice streams" is exactly the
   phrase a downstream user will lift. The scope belongs in the hypothesis
   list or the theorem's name, where it cannot be dropped by someone
   reading the signature — not only in a docstring that does not travel
   with the term.
2. **Properly (cost XL):** the mover route — alloc-renaming (obstruction
   1), extensional heap equivalence (2), path-level frame lemmas through
   `StructFields.set`/array update (6), store/store commutation, then the
   Mazurkiewicz normalization induction. This is a genuine research
   obligation of the ICTAC-2018/Lipton lineage, correctly identified, and
   it is months of work. I would not gate the semantics product on it —
   but I *would* gate any published concurrency claim on it.

**Field calibration.** Boehm–Adve DRF-SC is the licence the whole design
invokes, and its hypothesis quantifies over **all** SC executions of the
program. This model checks race-freedom over its *coarse* execution set
only, which is a subset. So the licence's hypothesis is not established by
the check that stands in for it. That is the precise shape of the gap, and
it is worth writing down in exactly those terms.

---

### D5 — Establish detector soundness, or bound the consequences of its known fail-open under-approximations

**Cost: M.** *This is the best value-per-cost item on the list.*

**What is true today.** The racy-program refusal is doctrine (register #4,
C10), and it is the load-bearing move: refusing racy programs is what
makes SC-only interleaving defensible. But **refusing racy programs is
only honest if race detection is complete for accepted programs**, and it
is not. Three problems, all recorded:

1. The detector's footprint is **not the machine's actual memory
   traffic**. It is a hand-curated table, `stepAccesses`, computed from
   the pre-step configuration and argued case-by-case against what gc's
   compiled code would touch. `Race.lean` explicitly records that
   auto-logging at the `loadLoc`/`storeLoc` chokepoint was *rejected* in
   favour of this table, and that its completeness is a manual "LOCKSTEP
   obligation" enforced only by the corpus.
2. The table has **named under-approximations** — U2 (`len`/`cap` on
   channels), U4 (sync-object data accesses), U5 (cross-goroutine unlock
   without handoff). These are fail-**open** relative to `-race`: an
   access Go performs that the table omits is a race the detector cannot
   see. Register #13 states the scope frankly: *"The race-refusal boundary
   is TSan's realized edge set, not go_mem's minimal relation."*
3. Detection is **per-run**. "All schedules refuse" is a corpus-level
   enumeration discipline over the *coarse* schedule set, not a semantic
   property, and it applies to 21 rows.

**The wrong conclusion available today.** "Racy programs are refused, so
the SC model is sound for everything it accepts." A program with a real
race that lives in U2/U4/U5, or a race that only manifests at a
non-boundary interleaving, is **accepted** and given a sequentially
consistent semantics that real Go does not guarantee it. That is a direct
`observed ∉ modeled` hole — the project's own definition of a bug — sitting
underneath its most load-bearing simplifying assumption.

The corpus does not currently have the power to find this: **34
concurrency cases total** (12 racy-negative, 9 race-free, 6 litmus, 3+4
sync), and racy-lane cases get `go run -race` **exactly once**, no
repetition, no `GOMAXPROCS` sweep. Membership rows get 5 plain + 5 `-race`
samples. There is one known open red in the *other* direction (BUG-041:
`race/free/array-read-write`, a race-free `-race`-green program the
detector refuses, because value-path array reads are whole-cell) — so we
know the detector is imprecise in both directions and we have measured
neither.

**What would discharge it.** A **detector differential**, which is
straightforwardly buildable and which nothing in the repo currently does:

1. Mutation-generate racy programs (take race-free corpus cases; delete a
   lock, widen a shared access, drop a channel handshake) and require that
   `go run -race` red ⟺ the model refuses, over N runs each. Any
   asymmetry is a U-row instance with a concrete witness. **Cost M.**
2. Stress the existing racy and race-free lanes: `-count=N`, `GOMAXPROCS`
   sweep, `-race` repetition. One run per racy case is not evidence.
   **Cost S.**
3. Reconsider the chokepoint decision. Auto-logging footprints at
   `loadLoc`/`storeLoc` would make under-approximation structurally
   impossible for the accesses the machine actually performs, at the cost
   of over-approximating relative to gc. Given that the doctrine prefers
   visible red to hidden wrong answers, over-approximation is the correct
   direction of error here, and the current design has it backwards for
   U2/U4/U5. At minimum, the decision deserves re-derivation under the new
   goal — the mandate says old justifications are not self-certifying.

---

### D6 — Start discharging the frontend's 249 obligations, and close the wire decoder's fail-open defaults

**Cost: S for the decoder; M for a translation-validation pilot; L for the census.**

**What is true today.** `CLAUDE.md` names the trusted surface as "the
interpreter… **and the native frontend lowering**". That is 15,407 lines
of unproven Go plus a 1,446-line `partial` Lean decoder, performing **249
catalogued semantic transformations**, of which **zero are discharged**.
Thirty-three of the 249 are "L" obligations — not value equalities but
effect ordering, cell identity, frame scoping, dispatch selection, and
non-interference of an untaken path. The desugars are not minor: ANF
hoisting with 17 nested save/restore sites; lambda lifting with captures
as pointer parameters; `goto` restructured into a program-counter dispatch
loop guarded by a four-check envelope whose *sufficiency* is the real
unproven claim; the Go 1.22 per-iteration loop variable selected by a
**heuristic scan** for capture-or-escape whose obligation is stated as
"completeness of the trigger" (BUG-003 lived here — "333 where Go said
12").

And the decoder half has its own fail-open defaults, which I verified
directly in `NativeToIR.lean`:

- `for` with `cond` absent ⇒ `.boolLit true` — **an infinite loop**
- `make-chan` with `cap` absent ⇒ `none` — **unbuffered**
- `select` with `default` absent ⇒ `none` — **blocking**
- `make-map` size hint: dropped unconditionally
- result types defaulting via `.getD .int` at two sites

In each case the absence of an optional key yields a *different,
well-formed program* rather than a refusal. The census counts **18** such
sites. `StrictJson.requireExactKeys` cannot help, because these are legal
key sets. This is a fail-open in the trusted surface of a project whose
charter's fourth doctrine bullet is "Fail closed, always."

**The wrong conclusion available today.** "The interpreter is validated by
2,478 differential cases" — but the object the differential exercises is
`lower(P)`, and every theorem a downstream repo proves is a theorem about
`lower(P)`. The lowering is trusted, unverified, has 249 stated
obligations, and its own census found two live silent wrong answers on
first pass. A reader who takes `CLAUDE.md`'s TCB statement at face value
should be told that ~35% of the trusted surface by line count has *no*
discharged correctness obligation.

**What would discharge it.**

1. **Make the decoder fail closed on semantically-significant optional
   keys** — emit them always and require them, or require an explicit
   sentinel. This is a small change, it is required by the project's own
   doctrine, and there is no argument for the current behavior.
   **Cost S. I would not sign off without this one.**
2. **A translation-validation pilot** on the three highest-risk desugars:
   the Go 1.22 loop-variable trigger (completeness), the `goto`
   restructuring envelope (sufficiency), and ANF hoist ordering. The
   census itself proposes `C-1` as a first target. Even one discharged
   obligation changes the shape of the claim from "0/249" to "the
   mechanism exists and scales at cost X/row". **Cost M.**
3. **A desugar-directed probe generator**: for each of the 249 rows, a
   generated family of programs that discriminates the transform from its
   plausible mis-implementations. This is cheaper than proof and would
   have caught both BUG-066 and BUG-067. **Cost M–L.**

**Field calibration.** This is CompCert's lesson, precisely. Csmith's
finding against CompCert was that the *verified* middle-end was clean and
the bugs lived in the unverified front-end and in the semantics
specification itself. GoLean's architecture reproduces that shape exactly
— a proved-adequate core behind an unverified elaboration — and it should
expect the same distribution of bugs. Cerberus's answer to the same
problem was to make the elaboration to Core *explicit and small* and to
typeset it beside the ISO clauses. GoLean's elaboration is neither small
nor beside anything, and W7/SpecTec-Go is the recorded plan to fix that.
The plan is right; nothing has been built.

---

### D7 — Fix the language-version pin: `types.Config.GoVersion` is unset and build constraints are never evaluated

**Cost: S.**

**What is true today.** The doctrine's central versioning claim is that
"GoCore models the Go 1.26 language" and that the spec pin and the oracle
toolchain move together, with the Go 1.22 loop-variable change cited as
the standing reminder that "language version is semantics, not
packaging." I checked the frontend. `load.go:644` is:

```go
conf := types.Config{Importer: imp}
```

`GoVersion` is unset. There is no `go.mod` in the corpus (spec-sources
admits this, calling the third leg of the agreement rule an object that
"has no object today"). And `grep` for `go:build`/`BuildTags` across
`tools/nativefrontend/*.go` is **empty** — build constraints are never
evaluated; `parser.ParseDir` takes every non-test `.go` file.

So the language version the frontend actually enforces is *the toolchain
default of whatever Go binary compiled the frontend* — an ambient property
of the build machine — and not the pinned go1.26. Today those coincide,
which is exactly why nothing has failed. The moment they do not, the pin
is silently wrong in the one dimension the doctrine singles out as
semantics-bearing.

**The wrong conclusion available today.** That the version pin is
enforced. It is documented and checked on the *oracle* side (the harness
refuses off-pin toolchains) and unenforced on the *frontend* side.

**What would discharge it.** Set `types.Config{GoVersion: "go1.26"}`; give
the corpus a `go.mod` with a `go` directive; add the third leg to the
agreement preflight; either evaluate build constraints or refuse any file
carrying one. All small. This is the cheapest item on the list and it
repairs a stated doctrine claim.

---

### D8 — Test the modeled ⊆ permitted direction, or stop calling it "the weakest machine Go permits"

**Cost: M.**

**What is true today.** The doctrine's product is the upper bound. I went
looking for the instrument that tests it. There are exactly two, and
neither does what the claim needs:

- The **3-stream invariance check** on the 2,374 strict rows: run the Lean
  side under three *hard-coded* streams (`9,8,7,…`, `1,3,5,…`, `5,5,5,…`)
  and fail if the observation varies. This is a real narrowness check — it
  catches the model *inventing* nondeterminism where none belongs — and I
  credit it. It is three fixed streams, not a search, and it never samples
  Go.
- The **confluent lane** (58 rows): enumerate all schedules, require
  `|set| = 1`. Also a genuine over-width check, on 58 rows.

Neither establishes that a modeled behavior is *Go-realizable*. The
membership lane records `exhibited`/`unexhibited` counts and the harness's
own caption says they are metadata, *"never a pass criterion"*, because
*"too-wide has no oracle."* That is correct as far as it goes — but the
consequence is that **the model's width is, at every enveloped row, an
unaudited design assertion**.

**I measured this.** I ran the whole membership lane —
`scripts/capped scripts/diff-one` over all 25 rows — and summed the
reported `enumerated` / `exhibited` / `unexhibited` counts. The result:

| | members |
|---|---|
| enumerated by the model (24 passing rows) | **441** |
| **exhibited** by a real `go run` sample | **45 (10.2%)** |
| **unexhibited** — modeled, never witnessed | **396 (89.8%)** |

The 25th row, `sync/atomic-frontier/mp-litmus`, **fails**: the frontend
refuses `atomic.StoreInt32` (D9).

The distribution matters more than the headline. On the concurrency and
map rows (5 plain + 5 `-race` Go samples each) the model is in decent
shape: 49 enumerated, 39 exhibited, 10 unexhibited. The 89.8% figure is
driven almost entirely by the four slice/append rows, which take
**`samples=1`** — a single Go run each:

- `slices/append-spill-size-class`: **300 enumerated, 1 exhibited, 299 unexhibited**
- `slices/full-slice-cap-zero`: 32 enumerated, 2 exhibited, 30 unexhibited
- `slices/append-spill-below-formula`: 31 enumerated, 1 exhibited, 30 unexhibited
- `slices/append-spill-stack-buffer`: 29 enumerated, 2 exhibited, 27 unexhibited

So the append-spill envelope — R2, an (a) ENVELOPED row, one of the nine
places where the machine claims to exercise real latitude — asserts a
300-member capacity envelope on the strength of **one** observation of gc
plus a containment argument about `roundupsize` and the 32-byte stack
buffer. The argument may well be right; the doctrine itself calls R2 "a
declared pragmatic subset". But this is the concrete shape of the
upper-bound problem: at the project's flagship enveloped row, 299 of 300
modeled behaviors have never been witnessed by anything, and the harness
takes one sample. Raising `samples` on the append rows costs nothing and
would at least tell us whether gc's realized set is 1 member or 40.

Meanwhile the *narrowness* side is quantified and it is not small: **17
PINNED + 7 NARROWED = 24 rows where the model is strictly inside what Go
permits**, of which five — **E3, E5, E7, E13 (type-assertion axis), R3
(escaping path)** — are recorded as **known ≠ gc**. Under the doctrine's
own bug definition, a probed gc-elsewhere observation is an
`observed ∉ modeled` candidate. So by the project's own rules there are
five standing, known, unrepaired bugs, three of which (E7, R3, E3/E4/E5)
sit at priority 3/4/5 in a queue that has not moved since 2026-08-21. E7
is called out in the inventory as *"the only pin KNOWN to sit beside the
oracle's realization on the SEQUENTIAL side, soundness-direction, and
UNGUARDED."* Unguarded is the operative word.

**The wrong conclusion available today.** That "the weakest machine Go
permits" describes the artifact. It describes the *design intent*. The
artifact is a machine that is demonstrably narrower than Go at 24
enumerated points and whose width at the 9 enveloped points has never been
tested against anything.

**What would discharge it.** Two complementary moves:

1. **Per-enveloped-row width audit.** For each (a)-class row and each
   enumerated member, either (i) exhibit it under some oracle perturbation
   — `GOMAXPROCS`, `-race`, `-gcflags`, repetition count — or (ii) carry an
   explicit upper-bound argument citing spec/mem text for why Go permits
   it even though gc does not realize it. Make `unexhibited` members
   *require* a citation rather than being metadata. This converts the
   aspiration into an audited claim at bookkeeping cost. **Cost M.**
2. **Guard E7 and clear the top of the re-envelope queue.** E7's interim
   frontend detector — fail closed on the hidden-dep shape — is described
   in the inventory as LOW cost and converts a silent class into a visible
   one. Do it. R3 (`[]byte(s)` capacity) is described as "best
   value-per-cost in the queue" — one arm on the existing append-spill
   mold. Do that too. **Cost S each.** A queue whose top two items are
   self-described as cheap and which has not moved in ten days is a queue
   that needs either movement or a recorded decision to stop.

---

### Further demands, below the top eight

**D9 — `sync/atomic` is unmodeled, and with racy access refused, the entire
lock-free fragment of Go is outside the model.** The founding concurrency
design note set the target as "full shared-memory concurrency — mutexes,
`sync/atomic`, lock-free patterns; 'the actually interesting code'". What
shipped is `Mutex`/`RWMutex`/`WaitGroup`/`Once` native, and
`atomic`/`Map`/`Cond`/`Pool` failing closed. The Go memory model document
exists *primarily* to specify atomics and racy access; the model covers
neither. This is honest, it is recorded (Q-ATOMIC, 5 reds; the
`sync/atomic-frontier/mp-litmus` membership row is currently RED), and it
should be stated whenever "the memory model is modeled" is said, because
what is modeled is the memory model's *happens-before edge rules inside a
race detector*, not the memory model as a semantics. Cost L.

**D10 — Reconcile the records; they are the product and three of them have
drifted.** For an artifact whose credibility *is* its bookkeeping,
unreconciled bookkeeping is the characteristic failure. I found:
`language-coverage-ledger.md` §8 still cites 2462 cases / 2293 PASS / 169
FAIL against an actual baseline of **2478 / 2306 / 172** (the three new
reds are exactly the BUG-062 widening) — and §8b was written specifically
to prevent this; the latitude inventory §10 claims "REFUSED… 9" where §5
enumerates **6**, in violation of §10's own membership-list reading rule;
the Q-row count is stated as 10 (§6 table), 9 (§8) and 8 (TODO) in three
places; **four cited evidence documents are absent from the tree**
(`docs/g-bind-log.md` — which is the *current baseline's own re-pin
record* — plus `2026-08-22_launch-audit-synthesis.md`,
`goose-parity-parked.md`, `verified-examples.md`, the last cited by the
doctrine's register #7); and `coverage-ledger.md` grades Maps/Channels/
Interfaces as `partial` while `language-coverage-ledger.md` grades them
`covered(A)`, with the older file not marked superseded. Also: ~15
frontier-table `file:line` citations resolve only via
`refs/snapshots/bugfix-arc-prerebase`, so pruning a snapshot ref would
make the repository's strongest evidence unresolvable. Run
`tools/reconcile-records`, act on it, and put it in the gate. **Cost S.**

**D11 — The 390-case negative corpus does not test the model.**
`scripts/coverage-negative` runs `go build` and greps the error text; it
never invokes the frontend or Lean (I verified: the only `lean` matches
are `GOLEAN_*` environment variable names). Yet `baselines/negative-full.tsv`
advertises `oracle: go build (rejection) + frontend fail-closed`. The
second conjunct is unimplemented. As mechanized, these 390 rows assert
*gc's* behavior and constrain GoLean not at all — and 18 of them pin only
the word `overflows`. Either add the frontend leg (require that the
frontend also refuses, which is the claim the header makes) or correct the
header. Given that static semantics is 100% delegated, adding the leg is
the only static-semantics evidence about GoLean that could exist. **Cost S.**

**D12 — `IntKind.unbounded` is a fail-open arithmetic escape hatch.**
`bits? = none` makes `normalize` the identity, `compatibleResult` lets a
flexible kind mix with any concrete one, `Expr.intLit`'s *default* kind is
`.unbounded "integer"`, and while bitwise ops fail closed on it,
`+ - * / % << >>` do not — they compute in ℤ with no wraparound. Any
lowering path that fails to type a literal silently gets mathematical
integers instead of Go integers, which is the exact shape of a silent
wrong answer in a project that has already shipped two. Make unbounded
arithmetic fail closed outside constant folding. **Cost S.**

**D13 — `uintptr` collapses to `uint64` at the level of type identity, not
just observation.** `NativeToIR.lean:62` maps `"uintptr" => .uint64`. The
CLI refuses `uintptr` *observations*, which handles half of it — but
nothing stops a boxed `uintptr` from satisfying `x.(uint64)`, or a type
switch from merging two distinct Go cases. The mitigation covers the
observation half only. **Cost S.**

**D14 — `storeLoc` at an unbound base creates the cell; `loadLoc` at an
unbound base is stuck.** The asymmetry is a fail-open default in the
trusted core. `StateWf`/`ConfigWf` make it unreachable from well-formed
states and the seeding driver asserts `StateWf`, so this is currently
sound — but it is exactly the silent-aliasing class that motivated
deleting `runNamedFunctionM`, and defence-in-depth argues for making it
`stuck`. **Cost S.**

**D15 — `x << (1<<40)` is semantically correct and computationally
catastrophic.** `intShiftLeftResult` computes `leftValue * 2^count` with no
width clamp before normalizing. Go defines this as 0; the model attempts to
construct a `2^(2^40)` integer. A legal Go program the interpreter cannot
run — and a program a downstream kernel evaluation cannot discharge.
**Cost S.**

**D16 — Spec-example mining is 15 curated entries against 926 spec commits,
39 memory-model commits, 372 issue references and 214 rollup rows.** The
divergence ledger's own feed-status section records this ratio. The
archaeology instrument is built and barely consumed; two recorded spec
bugs (L-007, L-008) and one gc bug (L-014) sit **unreported upstream**.
Filing them is the CH2O/Cerberus move that converts an internal record
into external standing, and it is nearly free. **Cost S.**

---

## 4. THE FOUNDATION QUESTION

*Is this semantics, as-is, a sound foundation for a proof stack in a
separate repository?*

**Yes for the sequential fragment, with four conditions that must be
written into the reasoning repo's charter. No for concurrency without an
explicit, prominent assumption.**

The positive case is strong and I want to state it before the caveats. The
core is total, has no axioms or `sorry`s, and has **adequacy proved in
both directions** between the executable `stepFn` and the `Prop`-level
`Step` relation — with the relation's premises calling the same total
functions, so the two cannot silently diverge. The heap is a clean
access-path model with sound, canonical aliasing (path equality or prefix)
and genuine slice sharing, which is exactly the structure a separation
logic wants to sit on. Nondeterminism is externalized as a tape, so
∀-stream statements are expressible without a scheduler in the logic.
Fuel-out is a distinct outcome, checked after terminals. These are the
right foundations and most projects at this stage do not have them.

Now the property gaps that would **silently weaken** theorems proved over
this semantics. Silently is the operative word: each of these lets a
true-in-the-model theorem be read as a stronger claim about Go than it
supports.

### G1 — The termination gap makes `ok ∨ fuelOut` theorems vacuously satisfiable

There is no termination predicate and no coinductive characterization of
divergence in this repo — `Machine.Steps` is an ordinary inductive
reflexive-transitive closure over finite traces, and `Surface.lean`'s
`Terminates`/`ProgressExec` left with the parked reasoning product
(`MachineSound.lean:619` still references them). What remains is
`SlowObs := ∃ fuel ch, …`, which correctly makes "a divergent branch
observes nothing at any fuel" literal.

The hazard: a theorem of the shape `execStmtLoop_ok_or_fuelOut` —
`(∃ σf ch', … = .ok …) ∨ … = .error .fuelOut` — **is true at fuel 0 for
every program**. It carries no information without a joint termination
fact, and no such fact is available here. Any reasoning layer that treats
an `∃ fuel` statement as a totality result is wrong. The reasoning repo
must define `Terminates` itself, must never accept ∃-fuel as totality, and
must state a variant/measure obligation for every loop rule.

Second-order hazard: the harness's `nonterm=` bucket equates fixed-fuel
exhaustion (default 10,000,000 steps) with divergence, so a program that
terminates late is silently bucketed as nonterminating and could hide a
member from a cardinality pin. And `TODO.md` carries an *owed ruling*:
"RULE what `nonterm=` means under `engine=dedup`." That ruling should
land before any liveness claim is built.

### G2 — The coarse-schedule gap: ∀-stream theorems are not ∀-schedule theorems

This is G1's concurrent analogue and it is the sharpest of the four.
`MultiStreams.lean`'s `execProgLoop_ok_of_allStreamsOkPool` gives
`∀ ch : Choices, ∃ σf, … ∧ post σf = true` — genuinely useful, kernel-
checkable, and quantified over **coarse (registry-point) schedules only**.
`EnumDedupSound.lean`'s `checkCertM_slowObs` has the same scope. The
bridge to real Go executions is `NPDRFReduction`, which does not exist and
whose current statement is false (D4).

A reasoning layer that proves "∀ streams, the program satisfies its spec"
and ships it as "the program is correct under any Go scheduling" has
over-claimed. The reasoning repo must either (a) carry the NPDRF reduction
as a **named, prominent assumption** on every concurrent theorem, or (b)
scope its concurrency theorems to the coarse relation and say so in the
theorem statement, not in a comment. Given that the boundary set has been
empirically incomplete twice, (a) with a visible assumption is the honest
posture, and I would want the assumption to appear in the *theorem's own
name or hypothesis list*, not in a docstring.

Compounding: the granularity ledger is undischarged (machine-step ↔
Go-atomicity), `sortSlice` is one step, and `slices.Sort` vs
`slices.SortFunc` have different granularities for the same Go operation.
So even the *fine* relation is not Go's granularity.

### G3 — The elaboration gap: theorems are about `lower(P)`, and `lower` is trusted

Every theorem proved over this semantics is a theorem about the lowered
IR. The lowering is ~17k unverified lines with 249 undischarged
obligations (D6), including 33 that are not value equalities, plus a
decoder with 18 fail-open optional-key sites. The reflection pair
(`goldenWire%` + shape pins) ties *bytes on disk* to a Lean term through
the same decoder every run uses — that is the right mechanism and it
closes the "is the term the one I pinned" question. It does **not** close
"does the term mean what the Go source means." That is D6's territory, and
until W7/SpecTec-Go lands, every theorem's honest statement is *"the
lowered program satisfies S, where lowering is trusted."*

This is not a reason to refuse the foundation — CompCert has the identical
shape and says so — but it must be stated in the reasoning repo's
trusted-surface section, with the 249/0 ratio named.

### G4 — The static-semantics gap, and its shared-fate blind spot

100% of Go's static semantics — types, constants, conversions,
assignability, type identity, inference, method sets, interface
satisfaction — is delegated to `go/parser` + `go/types`. Six `types.Info`
maps are the entire intake. `unsafe.Sizeof` is green *because* go/constant
folds it and the machine never sees the layout question.

The consequence is sharper than "delegation." **The differential is
structurally blind to it**: go/types and cmd/compile's `types2` are
line-for-line siblings, so a typing bug is present on both sides and
`go run` can never disagree. The project records this as "shared fate."
And the 390-row negative corpus — the only thing that looks like static
evidence — does not test the model at all (D11).

So the reasoning repo's claim is precisely: *"for programs `go/types`
accepts and types as it does, the dynamic semantics is thus."* A theorem
says nothing about a program go/types mistyped, and nothing about whether
go/types matches the spec. I think the delegation is the **right TCB
choice** — reimplementing go/types would be a larger and less reliable
artifact — but the claim must be stated in that conditional form, and the
Go-version hole (D7) means even the conditional's *version* is currently
ambient rather than pinned.

### G5 — Observation-surface conditionality collides with a separation logic

Register #6's allocator quotient is discharged **conditional on the
observation surface being pointer-equality-only**. A separation logic
reasons about locations directly; if the reasoning layer ever exposes
address *values*, address *ordering*, or `%p`-class output in a
specification, the quotient reopens and `Frame.allocatorIndependence` no
longer discharges the register entry. The condition is currently guarded
by nothing but prose in a doctrine file in a *different repository from
the one that will violate it*. This is the most likely silent breakage in
the whole set, precisely because the violating change will look
innocuous. D3.3 (a mechanical guard) should be treated as a precondition
for the reasoning repo starting work, and the same guard should cover the
`%T`/`%w` refusal invariants that `errors.New`'s and G-20's
unobservability arguments hang on.

### G6 — Two smaller items that will bite a proof layer specifically

- **`IntKind.unbounded`** (D12): if a lowering path leaves a literal
  untyped, arithmetic is over ℤ. A theorem about "Go `int` arithmetic"
  could be proved over mathematical integers. For a proof layer this is
  worse than for a test harness, because there is no oracle to catch it.
- **The `stepFnIter` converse is not built** (`MachineSound.lean:592-598`):
  "every `Steps`-reachable config is `stepFnIter`-reachable under *one*
  stream" needs a stream-stitching lemma that does not exist and is
  explicitly not claimed. So a relational proof and an executable
  certificate may not be composable in the direction a proof layer will
  want. This should be built early, not discovered late.

### Foundation verdict

Build the sequential reasoning layer on this. It is a better foundation
than most available, and G1/G3/G4/G5 are all dischargeable by *stating the
conditions*, three of which the project has already written down
correctly. Do not build a concurrency reasoning layer on it until D4 has
at least been *scoped* (the S-cost half) and D5 has been *measured* — and
when you do, put the NPDRF assumption in the theorem statements, where a
reader cannot miss it.

---

## 5. WHAT I WOULD PUBLISH

### 5.1 The paper this artifact supports today

> **"An Executable, Adequacy-Proved Operational Semantics for Sequential
> Go, with a Mechanized Latitude Census."**
>
> Contributions: (1) a total, `sorry`-free Lean semantics for a large
> sequential fragment of Go 1.26 with two-directional adequacy between an
> executable step function and a relational semantics that share their
> premises; (2) the **latitude census** as a methodological contribution —
> a classified, cost-estimated, code-anchored enumeration of every point
> where the language permits multiple behaviors, with the choice-site
> census carried as an exhaustiveness-checked datatype rather than a
> document; (3) the **envelope-by-quotient** discharge pattern; (4) a
> differential validation methodology with an explicit lane taxonomy
> (strict / confluent / membership / racy) that separates "the oracle
> agrees" from "the oracle's behavior is a member of the modeled set",
> plus kernel-checked enumeration certificates; (5) empirical results:
> 2,306/2,478 hand-authored cases, 79,795/79,800 generated programs, two
> bugs found **in gc**.

That paper I would accept, at a good venue, subject to the revisions
below. The latitude census and the (q)-quotient pattern are genuine
methodological contributions I have not seen packaged this way, and
"finding bugs in the implementation you formalize" is the field's
recognized signature of a real artifact.

### 5.2 What review would say

**The three reviews I would expect:**

*Reviewer 1 (accept with minor).* Praises the census and the honesty; asks
for the test-suite result (D2) and notes the observation channel is
narrower than the abstract implies.

*Reviewer 2 (major revision) — the dangerous one.* "The paper's central
claim is a semantics that captures Go's permitted behaviors, but the
evaluation only measures the opposite direction. §N reports 2,478 fixtures
against **one** compiler at **one** version on **one** platform at **one**
optimization level; the authors' own Table (the latitude inventory)
records 24 rows where the model is strictly narrower than the language
permits, five of them known to differ from the very compiler used as
oracle. The membership lane — the only mechanism that tests the modeled
*set* rather than a modeled *point* — covers 25 of 2,478 cases. I cannot
distinguish this from a careful model of gc-1.26.5-linux-amd64, which is a
different and much weaker contribution." **This reviewer is right, and D1,
D2 and D8 are the answer.**

*Reviewer 3 (reject, concurrency scope).* "The concurrency semantics
schedules only at registry boundaries. The soundness of this restriction
is the NPDRF reduction, which §M presents as future work and which the
artifact marks 'REFUTABLE AS WRITTEN'. The race detector that gates the
DRF precondition is a hand-maintained footprint table with three
acknowledged under-approximations, evaluated on 34 test programs with one
`-race` run each. `sync/atomic` is unmodeled. I do not believe the
concurrency claims." **Also right.** The answer is to **cut concurrency
from the paper's claims** and publish it separately when D4/D5 land. A
paper that says "sequential Go, with a concurrency extension whose
soundness obligation is stated and open" is accept-able; one that claims
concurrency fidelity is not.

### 5.3 The shortest path to "accept"

Six items, in order, none of them XL:

1. **D2 — run `$GOROOT/test`.** Converts self-authored coverage into
   third-party conformance. Single highest-value item, and it is the
   result Reviewer 1 and Reviewer 2 both want. *(M)*
2. **D1.1+D1.2 — version and optimization sweeps**, plus a `go.mod` for
   the corpus. Turns "one point" into "a small matrix" and closes the
   version-pin story. *(S)*
3. **D7 — set `GoVersion`, handle build constraints.** Repairs a stated
   doctrine claim for almost nothing. *(S)*
4. **D3.1+D3.3 — an effect-trace channel and mechanical guards on
   observation-surface-conditional discharges.** Fixes the blind spot that
   hid BUG-066/067 and protects the (q) discharge. *(M)*
5. **D8 — the width audit + guard E7 + widen R3.** Converts "the weakest
   machine Go permits" from an aspiration into an audited claim with a
   stated, shrinking exception list. *(M)*
6. **D4-scope + D5.1 — the NPDRF weakening ruling with scope sentences on
   every ∀-stream artifact, and a detector differential.** Makes the
   concurrency chapter honest enough to survive Reviewer 3 as *stated
   future work* rather than *contested claim*. *(S + M)*

With those, I would sign a review saying: *this is the most carefully
self-audited executable language semantics I have reviewed, its fidelity
claims are now supported at the strength stated, and its open obligations
are named at the right places.* That is a paper I would cite and a
foundation I would build on.

### 5.4 The one thing I would say to the owner directly

The mandate was to question the assumptions, so here is the meta-finding.
The register of simplifying assumptions, the latitude inventory, the
divergence ledger, the U-ledgers, the granularity ledger, the frontier
table, the desugar census — these are excellent, and they have become a
**substitute for the work in a specific and detectable way**. The pattern
recurs: a gap is found, it is beautifully documented, it is assigned a
cost and a queue position, and then it stops moving. E7 has been "LOW
cost, converts a silent class into a visible one" for ten days. R3 has
been "best value-per-cost in the queue" for ten days. The NPDRF reduction
has carried "any concurrency soundness claim must carry it as a stated
assumption" since 2026-08-06, and the claims do not carry it. The desugar
census is nine days old, found two live silent wrong answers immediately,
and has discharged none of its 249 rows.

Documentation of a gap is not mitigation of a gap, and this project is
good enough at the former that it should watch for the substitution. My
concrete suggestion: give every recorded set-aside a **decay date** — a
date at which it must be discharged, re-argued from scratch, or formally
converted to a permanent accepted limitation with the owner's signature.
The charter already has the right instinct ("scaffolding carries a
retirement condition or a deletion date"); it is applied to code and not
to debts. A ledger where entries can only be added is a ledger that
measures ambition. A ledger where entries expire measures progress.

---

*[AGENT] Lane E outsider review, 2026-08-31. Evidence base: direct reading
of the doctrine, census, ledgers and prior-art notes; four commissioned
forensic sweeps of the differential apparatus, concurrency machinery,
frontend boundary and semantic core; independent verification of the
baseline arithmetic, the CI cadence, the negative-corpus checker, the
decoder's optional-key defaults and the frontend's `types.Config`; and
live execution of the artifact via `scripts/capped scripts/diff-one`. No
tracked file other than this report was modified.*
