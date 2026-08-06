# Validating the concurrency semantics — research note (2026-08-06)

Status: RESEARCH DRAFT (untracked, `.tmp/`). Input to the channels/goroutines
arc's design note; nothing here is a decision of record. Written from an
isolated worktree; no tracked file modified.

Tagging per the floats-note convention (`docs/2026-08-04_floats-design.md`):
**[FACT]** — verified against a primary source this session (repo file at the
given path, a local Go probe run, or a web source found+read this session;
citation given). **[FACT-recalled]** — a well-established citation from prior
knowledge, NOT re-verified this session; treat the bibliographic detail as
checkable, the claim as reliable. **[ANALYSIS]** — our reasoning.
**[RECOMMENDATION]** — proposed for the arc's design note to adopt or reject.

Charter: the validation strategy space for the channels/goroutines arc, given
the user's framing — differential testing cannot validate the concurrency
semantics "in a simple way": one `go run` explores a single, heavily biased
scheduler corner per run, while our model will admit ALL interleavings via the
`Choices` stream. Binding inputs read first:
`docs/2026-08-04_nondeterminism-doctrine.md` (DRF-SC fail-closed races,
`-race` second oracle, litmus corpus, fairness quantifier),
`docs/2026-08-04_membership-lane-design.md` + the enumerator in
`GoLean/CLI.lean` (403–817), `scripts/diff-coverage` (lane mechanics).

Oracle toolchain for all probes below: go1.26.5 linux/amd64. **[FACT]**
(`go version`, this machine).

---

## 0. The problem, stated precisely

**[FACT]** The doctrine already names the asymmetry
(`docs/2026-08-04_nondeterminism-doctrine.md:38-51`): too-NARROW envelopes
(real Go exhibits a behavior we exclude) are the soundness-relevant,
*detectable* direction — the membership lane's job; too-WIDE envelopes are
undetectable by any oracle and are checked by review. For scheduling the
doctrine states: "SCHEDULING sampling is nearly useless (the runtime explores
a tiny biased corner)" (line 47). Section 3 below puts numbers on that claim.

**[ANALYSIS]** So the concurrency validation problem splits into four
sub-problems, each with a different best tool:

1. **Machine-side envelope coverage** — does our admitted set contain every
   behavior a conforming Go can exhibit? Tool: interleaving *enumeration* on
   litmus-scale programs (§1), plus spec-text review (the doctrine's
   envelope-fidelity dimension).
2. **Machine-side correctness of each interleaving** — is each admitted
   interleaving's outcome what Go would produce *if the scheduler had made
   those picks*? Tool: membership testing (Go sample ∈ enumerated set), plus
   confluent-case equality where every schedule must agree (§4b).
3. **The racy boundary** — do we refuse exactly the programs whose behavior
   Go leaves (essentially) undefined? Tool: `-race` as second oracle (§4d).
4. **Liveness claims** — what termination statement is both true and honest?
   Tool: a fairness-constrained quantifier, decided up front (§5).

The overarching epistemic point, extending the doctrine: for sequential code
the differential is VERIFICATION; for concurrency it degrades to (i)
verification *per confluent case*, (ii) sanity-checking via membership for
schedule-dependent cases, and (iii) nothing at all for the unexhibited
corners — where review, litmus shapes borrowed from the literature, and
eventually proofs are the only checks.

---

## 1. Our own machinery, extended: the scheduler as a Choices site

### 1.1 The fit

**[FACT]** `Choices := List Nat` with `Choices.consume (choices) (bound)`
taking each pick modulo the site's bound; exhaustion consumes nothing and
yields 0 (`GoLean/GoCore/State.lean:138-143`, and the enumerator's docstring
`GoLean/CLI.lean:563-571`). The membership enumerator explores stream
prefixes over alphabet `[0, B)` to consumption depth `D` by depth-first
frontier expansion, certifies completeness modulo the author-asserted width,
alias-guards the width assertion, and fails loud on depth/cap/work overruns
(`GoLean/CLI.lean:645-689`).

**[ANALYSIS]** If "which runnable goroutine steps next" is one more
consumption site with bound = |runnable set| at that configuration, then the
membership enumerator IS an interleaving explorer, with no new mechanism:

- The site bound is dynamic (runnable count varies), but `consume` is already
  modulo-bound, and the width assertion "B ≥ max simultaneous runnable
  goroutines" is exactly as author-assertable as today's map widths — in a
  litmus case the goroutine count is statically evident.
- The probe-pick frontier logic, the leftover-stream consumption meter, the
  observation dedup, the `--expect-status` machine-bug discipline, the
  fail-loud caps: all carry over unchanged.
- The lane's *singleton guard* inverts into a feature (§4b): a concurrent
  case whose enumerated observation set is a singleton is machine-certified
  SCHEDULE-CONFLUENT, which is precisely the license to demand strict-lane
  equality against `go run` for it.

### 1.2 The state-space growth, honestly

**[ANALYSIS]** The current lane's worst case is 4096 leaves at depth 3 /
width 16, ~0.3–0.4 s including alias probes
(`docs/2026-08-04_membership-lane-design.md:153-160`), i.e. the enumerator
does on the order of 4×10⁴ machine runs per second on small programs, with a
default work cap of 200 000 runs (`GoLean/CLI.lean:477-480`).

If the scheduler consumed a pick at EVERY machine step, the choice-tree depth
would equal the total step count. Even a trivial two-goroutine program runs
hundreds of `stepFn` steps; the tree is ~2^(hundreds). No bounding constant,
cap, or DPOR trick recovers that; per-step scheduling is enumerable only for
programs of a few dozen steps total. This is astronomically worse than
anything the lane has faced — the growth is exponential in *program length*,
not in the (small, fixed) number of latitude sites.

The tractability decision is therefore not an optimization but a design
precondition:

### 1.3 Coarse scheduling points — the reduction that makes it tractable

**[ANALYSIS]** Consume a scheduling pick only at *communication points*:
channel send/recv, `select`, `go` spawn, sync-primitive ops, goroutine exit —
NOT at ordinary computation steps. Then depth = the run's total communication
count, and branching = runnable count. A two-goroutine litmus case with ~10
channel ops has a tree of at most 2^10 ≈ 10³ leaves — *smaller* than the map
case the lane already handles in 0.4 s. Three goroutines × ~8 ops ≈ 3^8 ≈
6.5×10³. The current 200 000 work cap covers roughly: 2 goroutines to depth
~17, 3 goroutines to depth ~11, 4 goroutines to depth ~8 (before DPOR-style
pruning, which §2.1 shows can push well past that). That is exactly
litmus-test scale, and NOT application scale — see §1.5.

**The soundness question**: for which programs is communication-point
scheduling equivalent to full per-step interleaving? This is the classic
reduction, and it has precise citable statements:

- **[FACT]** Xiao, Jiang, Liang, Feng, *"Non-preemptive Semantics for
  Data-Race-Free Programs"*, ICTAC 2018 (LNCS 11187,
  doi:10.1007/978-3-030-02508-3_27) — the directly-on-point theorem: they
  "formally prove that DRF concurrent programs behave the same in the
  standard interleaving semantics and in their non-preemptive semantics"
  where "a thread yields control of the CPU only at certain carefully-chosen
  program points", and give an equivalent race-freedom notion (NPDRF) stated
  *inside* the non-preemptive semantics. (Found and abstract read this
  session; full text paywalled.) This is the exact shape of theorem our
  model needs, and the NPDRF half matters just as much: our race check will
  run inside the coarse semantics, so we need race-detection-in-the-coarse-
  semantics ⇔ race-in-the-fine-semantics.
- **[FACT-recalled]** Lipton, *"Reduction: a method of proving properties of
  parallel programs"*, CACM 18(12), 1975, pp. 717–721 (existence/venue
  verified this session via ACM DL) — the mover framework: statements that
  commute with all concurrent statements (both-movers; here, the race-free
  local steps between communication points) can be fused into atomic blocks
  preserving the properties of interest.
- **[FACT-recalled]** Mazurkiewicz trace theory as organized for model
  checking by Godefroid (*Partial-Order Methods for the Verification of
  Concurrent Systems*, LNCS 1032, 1996): executions differing only by swaps
  of adjacent independent steps are equivalent; scheduling only before
  dependent (communicating/conflicting) steps yields at least one
  representative per trace.
- **[FACT]** CHESS validates the architecture in practice: it schedules only
  at synchronization operations and runs a data-race detector to catch the
  programs for which that is insufficient — "for data-race-free programs,
  scheduling at synchronization points is sufficient" is its working
  hypothesis, backed by its race-detection escape hatch (Musuvathi et al.,
  *Finding and Reproducing Heisenbugs in Concurrent Programs*, OSDI 2008;
  paper located this session, architecture detail recalled and not re-read
  line-by-line — the arc note should pin the exact section).

**[ANALYSIS]** The coupling with the DRF-SC fail-closed doctrine is what
makes this sound *for us*: the doctrine already mandates that data races are
an error, not an interleaving (`nondeterminism-doctrine.md:103-108`). So the
programs for which coarse scheduling under-approximates the interleaving set
are exactly the programs our model REFUSES. Within the non-refused class, the
ICTAC-2018-shaped theorem says the coarse tree's observation set equals the
full tree's. Two obligations fall out:

1. **The race check must be complete for the coarse semantics** (NPDRF): a
   read/write pair unordered by happens-before must be detected *on every
   enumerated interleaving where it occurs*, and any interleaving exhibiting
   a race must fail the whole case closed — one racy leaf poisons the case
   (the enumerator's `--expect-status` discipline generalizes: "race
   detected" is a machine-refusal status, and a case mixing refusal leaves
   with value leaves is a RACY case, full stop). Detecting a race on *some*
   interleaving while certifying values from others would be exactly the
   silent-approximation the fail-closed rule forbids.
2. **The interpreter's step granularity must match the claimed scheduling
   points.** This is the granularity ledger's territory
   (`docs/2026-07-23_reshape-r1r2-machine-design.md` §1, BUG-002's class):
   the reduction theorem is about *Go's* atomicity, and our `stepFn`
   decomposition must not make two Go-atomic communication effects separately
   schedulable or fuse two separately-schedulable ones. The audit dimension
   "atomicity/granularity is unobservable sequentially" becomes OBSERVABLE
   the day the scheduler site lands — the enumerator will exhibit any
   granularity error as a spurious member. This converts our worst
   test-invisible defect class into a testable one, which is itself an
   argument for building the enumeration lane early in the arc.

**[RECOMMENDATION]** Adopt communication-point scheduling as the model's
granularity, state the reduction argument as the site's envelope statement
(spec text + DRF theorem citation + the refusal coupling), and put "prove the
coarse≡fine equivalence over GoCore" on the long-term proof ledger — it is a
mechanizable theorem (the ICTAC 2018 proof is simulation-based, the same
technique family as our existing adequacy kit), and it is the lemma the
∀-stream headline theorems will silently rest on.

### 1.4 What the certification claim becomes

**[ANALYSIS]** Today's lane certifies "all behaviors, given width ≥ site
bounds" (`CLI.lean:435-450`). With a scheduler site the claim becomes: **all
interleavings at communication granularity, of race-free programs, up to
depth D** — three qualifiers, each carried by a different mechanism (width
assertion + alias guard; the DRF refusal; the fail-loud depth cap). The
depth cap deserves emphasis: unlike map/append cases where depth is
structurally bounded by the program text, a concurrent program's
communication count can depend on the schedule (a `select` with different
branch lengths). `--max-sites` failing loud (never truncating) already
handles this correctly — a case exceeding D is visibly not certified, red,
and needs its bound raised or the case narrowed. No silent prefix
exploration.

The alias-guard heuristic transfers with one new caveat: the scheduler site's
bound (runnable count) *varies along the run*, so a single per-case width B is
an over-approximation at most sites (B = max goroutines). Values ≥ the local
bound alias existing residues by the modulo — harmless for coverage (width ≥
local bound everywhere is what matters), but the guard's refutation ladder
will be inert at sites whose local bound divides the rung offsets, same
condition as documented (`membership-lane-design.md:54-70`). No change
needed; the arc note should restate the inertness condition for dynamic
bounds.

### 1.5 What enumeration is NOT

**[ANALYSIS]** Enumeration validates the MODEL on litmus-scale programs; it
is not a verification strategy for targets. etcd-io/raft-scale code has
communication counts in the thousands over unbounded goroutine sets; no
bounding technique makes exhaustive exploration meaningful there, and the
literature's answer at that scale is proof (WP/Iris — the project's actual
plan) or unsound-but-effective bug hunting (§2.3/§2.5). The lane taxonomy in
§4 is therefore a *semantics-validation* suite, in exactly the sense the
sequential corpus is: strong enough that green implies the semantic
constructs are covered, never a claim about any particular large program.

---

## 2. The literature, with applicability verdicts

Context for every verdict: our engine is an executable, total,
kernel-reducible Lean interpreter, deterministic given a `Choices` stream;
exploration tooling lives in the CLI layer (untrusted, pinned by
driver-agreement tests); claims are possibilistic only (doctrine §binding-3);
and the certification direction (completeness of an enumerated set) is
load-bearing in a way most testing tools never need.

### 2.1 Stateless model checking + DPOR

**[FACT]** Flanagan & Godefroid introduced dynamic partial-order reduction
for stateless model checking (POPL 2005) **[FACT-recalled]**; Abdulla,
Aronis, Jonsson, Sagonas gave the provably optimal algorithm — *"Optimal
Dynamic Partial Order Reduction"*, POPL 2014, pp. 373–384, journal version
*"Source Sets: A Foundation for Optimal Dynamic Partial Order Reduction"*,
J.ACM 64(4), 2017 (verified this session;
https://dl.acm.org/doi/10.1145/3073408). Source sets replace persistent
sets; wakeup trees make the algorithm optimal — exactly one execution
explored per Mazurkiewicz trace; implemented in Concuerror (Erlang — a
message-passing language, the closest analog to our channel model) and
Nidhugg. Known limit: sleep-set-blocked exploration in non-optimal SDPOR can
be exponentially redundant, and avoiding it is NP-hard in general
(*Quasi-Optimal Partial Order Reduction*, CAV 2018, found this session).

**[ANALYSIS — verdict: ADOPT, second phase, as a pruner with a stated trust
argument.** Stateless model checking is *literally our enumerator's
architecture*: re-run a deterministic engine under systematically chosen
schedules; we get replayability for free from stream-determinism, which is
the property SMC tools work hardest to engineer. Source-DPOR needs an
independence/conflict oracle between steps — for channel-only communication
this is simple (ops on distinct channels commute; sends vs receives on the
same channel conflict; Concuerror's message-passing treatment is the
template). The danger is direction-specific: DPOR prunes *claimed-equivalent*
branches, so a bug in the independence oracle silently WEAKENS the
certification ("enumerated set is complete") that lane b and lane c passes
rest on. Mitigation: (i) ship full enumeration first — it is sufficient for
2–3-goroutine litmus cases (§1.3 numbers); (ii) when DPOR lands, keep a CI
cross-check mode running both explorers on the small corpus and asserting
identical observation sets (the same both-drivers pinning pattern the lane
already uses for `enumRun` vs `runConfig`, `CLI.lean:421-428`); (iii) the
independence relation gets its own envelope-statement-style note argued
against the channel semantics, since it is review-only in the same way
too-wide envelopes are.

### 2.2 Preemption bounding (CHESS) and delay bounding

**[FACT]** Musuvathi & Qadeer, *"Iterative context bounding for systematic
testing of multithreaded programs"*, PLDI 2007, pp. 446–455; CHESS system
paper at OSDI 2008 (both verified this session). Key properties: search
prioritized by preemption count; termination with bound c proves remaining
bugs need ≥ c+1 preemptions; cost exponential in threads and c but NOT in
execution length. Delay bounding: Emmi, Qadeer, Rakamarić, *"Delay-bounded
scheduling"*, POPL 2011 **[FACT-recalled]**. The independent empirics
(verified this session): Thomson, Donaldson, Betts, *"Concurrency testing
using schedule bounding: an empirical study"*, PPoPP 2014 + TOPC 2016
journal version, on 52-benchmark SCTBench — the majority of bugs expose with
schedule bound 1–2 (one benchmark needed 5 preemptions); delay bounding
dominated preemption bounding (found all 38 of its bugs + 7 more); and,
strikingly, naive random scheduling was at least as effective as systematic
bounding, with PCT (d=3) the most effective overall — all bugs the others
found plus three, missing only one.

**[ANALYSIS — verdict: ADOPT the *bound-as-metadata* idea, not the search.**
For us the bounding insight is not primarily a bug-finding heuristic but a
way to make large-ish membership cases honest: a case too wide for full
enumeration can declare `preemption-bound=k` and the certification claim
degrades, visibly and per-case, from "all interleavings" to "all
interleavings with ≤ k preemptions between communication points" — a
fail-closed *partial* certificate in the same spirit as the width assertion.
The small-bound hypothesis (validated by SCTBench) says such a lane still
catches most model bugs that any bounded lane could. But note our
communication-granularity choice already gives much of context-bounding's
payoff: bounding preemptions *between* communication points is meaningless
when we only schedule at them; the residual knob is bounding schedule
*switches* at communication points, which is delay bounding's shape. Defer
until a real case exceeds full-enumeration budgets; the singleton/confluent
and litmus lanes don't need it.

### 2.3 Probabilistic concurrency testing (PCT)

**[FACT]** Burckhardt, Kothari, Musuvathi, Nagarakatte, *"A randomized
scheduler with probabilistic guarantees of finding bugs"*, ASPLOS 2010, pp.
167–178 (verified this session). Defines bug depth d = minimum number of
scheduling constraints to force the bug; the priority-based randomized
scheduler detects a depth-d bug with probability ≥ 1/(n·k^(d−1)) per run (n
threads, k steps); naive coin-flip schedulers can have exponentially small
hit probability even at depth 1. SCTBench found PCT the most effective
technique on their suite (§2.2).

**[ANALYSIS — verdict: ADOPT as the machine-side SAMPLER for cases beyond
enumeration; never as certification.** The doctrine forbids probabilistic
*claims* (§binding-3), but PCT's guarantee runs in the safe direction: it
lower-bounds the chance a *machine-side* randomized exploration exhibits a
divergence, and "we sampled machine schedules PCT-wise and every Go sample
was a member / no refusal leaf appeared" is still a possibilistic statement
about what was checked, with the PCT bound quantifying (in the run log, not
the pass criterion) how hard we looked. Implementation is trivial for us: a
PCT schedule is just a `Choices` stream generated by the priority process —
the CLI can grow a `coverage-sample --pct d=3 --runs N` mode with ~a page of
code and zero semantics changes. This is the right tool for integration-scale
concurrent cases (the fuzz layer of the three-layer sufficiency strategy),
where enumeration caps out.

### 2.4 Coyote / P — systematic testing as a product

**[FACT-recalled]** Microsoft Coyote (github.com/microsoft/coyote), the
production descendant of P# (Deligiannis et al., PLDI 2015), applies
controlled scheduling + PCT-style strategies to .NET task code; P (Desai et
al., PLDI 2013) makes the state-machine model the source language and
model-checks it. **[ANALYSIS — verdict: architectural corroboration only.**
Their shared lesson for us: control the scheduler at the *API boundary*
(tasks/actors), not the instruction level — the same coarse-points decision
as §1.3 — and make every failing schedule replayable from a recorded seed.
Our `Choices` stream is already a replay seed; the arc should mandate that
every red concurrent case's artifact records the exact stream, so any
divergence reproduces with `--choices`.

### 2.5 Axiomatic checking (herd7, GenMC) and the Go memory model

**[FACT]** Herd7/"Herding cats" (Alglave, Maranget, Tautschnig, TOPLAS 2014)
**[FACT-recalled]** enumerate axiomatic-model-consistent execution graphs;
GenMC (Kokologiannakis & Vafeiadis, CAV 2021) **[FACT-recalled]** model-checks
programs directly against axiomatic weak-memory models (RC11/IMM). The Go
side (verified this session): Go's memory model was deliberately NOT given a
C11-style axiomatization — Cox's 2021 series (research.swtch.com/gomm)
explicitly chose "saying the minimum needed to be useful" over full
formality, citing a decade of subtle failures in the Java/C11 models; the Go
1.19 (2022) revision added happens-before rules for `sync/atomic` with SC
semantics (golang/go#50590). The academic formalization that exists is
*operational*, not axiomatic, and is nearly our exact setting: Fava, Steffen,
Stolz, *"Operational Semantics of a Weak Memory Model with Channel
Synchronization"*, FM 2018 + JLAMP 103 (2019), pp. 1–30 — a Go-inspired
calculus with buffered channels as the synchronization primitive, proving
SC-DRF **by a standard simulation argument, operationally** (their point:
"in contrast to an axiomatic semantics"); accompanying Coq-adjacent code at
github.com/dfava/mmgo; follow-ups fixed a mismatch between the Go memory
model and the race detector (Fava, SEFM 2020).

**[ANALYSIS — verdict: engine NOT applicable; shapes and the operational
precedent very much are.** Because DRF-SC-fail-closed means we never execute
a racy program to a value, we never need weak-memory execution graphs: our
admitted behaviors are SC interleavings of race-free programs, full stop. An
axiomatic Go checker would be checking latitude we deliberately refuse to
model. What we take instead: (i) the litmus SHAPES (message passing, store
buffering, IRIW analogs expressed through channels + racy-variable variants)
as corpus cases pinning that the racy variant refuses and the
channel-synchronized variant admits exactly the SC outcomes — §4e; (ii)
Fava et al. as the citable precedent that an operational, simulation-proved
SC-DRF theorem for a channel-synchronized Go calculus is feasible — the
Lean-mechanizable form of §1.3's obligation; (iii) their SEFM 2020 paper as
a caution that the *race detector's* happens-before can drift from the
*model's* happens-before — in our architecture those are one artifact, which
is the advantage to state in the design note.

### 2.6 Schedule fuzzing: rr chaos mode, GFuzz, and Go's own answer

**[FACT]** GFuzz: Liu, Xia, Liang, Song, Hu, *"Who Goes First? Detecting Go
Concurrency Bugs via Message Reordering"*, ASPLOS 2022 (verified this
session) — instruments Go programs to force chosen `select` branches and
message processing orders, fuzzes over orders with execution feedback, found
184 new bugs in Docker/Kubernetes/gRPC with negligible false positives.
Limitation noted in follow-ups: channel/select-order focused, no lock
support. **[FACT-recalled]** rr chaos mode (O'Callahan, 2016, rr-project
blog) randomizes thread priorities and timeslices under record-replay to
surface schedule-dependent bugs ordinary re-running never hits — the same
observation as our §3 data, from the debugging world. **[FACT]** Go itself
now ships a deterministic-scheduler test harness: `testing/synctest` is in
the go1.26.5 tree as a stable package (`/usr/local/go/src/testing/synctest/`,
checked this session) — goroutines in a "bubble" run under virtualized time
with deterministic scheduling; the Go team's own admission that real-runtime
sampling is inadequate for testing concurrent code.

**[ANALYSIS — verdict: GO-SIDE sampler upgrades, with an oracle-purity
line.** The membership lane's Go side needs diversity (§3 shows how little
plain `go run` gives). Three tiers, in order of purity: (i) `-race` runs —
already doctrine-sanctioned as second oracle, and §3 shows the race runtime
is ALSO by far the best interleaving diversifier we have; every membership
case's samples should include `-race` runs for both purposes at once. (ii)
Environment perturbation (GOMAXPROCS sweep, load) — weak but free and pure.
(iii) GFuzz-style instrumentation *rewrites the program under test* — that
crosses the "do not edit canonical Go to make something pass" line if used
as the oracle; permissible only as a separate, clearly-labeled bug-hunting
harness whose findings become ordinary corpus cases, never as membership
samples. `testing/synctest` similarly changes the program's scheduler and
time semantics — a possible future third oracle for *deterministic* replay
of concurrent tests, but its virtual-time semantics differs from the
production runtime's, so treat with the same quarantine.

### 2.7 Dynamic race detection: ThreadSanitizer / `-race`, and goleak

**[FACT-recalled]** Go's race detector is the ThreadSanitizer v2 runtime
(go.dev/doc/articles/race_detector); TSan methodology: Serebryany &
Iskhodzhanov, *"ThreadSanitizer — data race detection in practice"*, WBIA
2009 — shadow-memory happens-before (vector-clock) detection. The
load-bearing epistemics: **no false positives** on the dynamic happens-before
it observed (a report = a real race in that execution), but **false negatives
structurally**: it only sees races the sampled interleavings bring close
enough together, and synchronization it treats as HB (e.g. any channel op)
can mask races that a different schedule would expose. **[FACT-recalled]**
goleak (github.com/uber-go/goleak): end-of-test goroutine-leak detection by
stack snapshot — the practical tool for lane f's *partial* leak class, which
the runtime deadlock detector cannot see.

**[ANALYSIS — verdict: the asymmetry writes lane d's pass semantics.**
`-race` red = definitive (our refusal is justified by a concrete witnessed
race). `-race` green across all samples = weak evidence only. So a negative
case where we refuse but N `-race` samples stay green is *not* automatically
a bug on our side — it triggers the doctrine's "investigate" branch, and the
investigation has exactly three outcomes: (a) our race check is too eager
(model bug — fix); (b) the race needs a schedule the sampler never hits
(strengthen with directed sampling; GFuzz-harness territory); (c) the
program is genuinely race-free and we misclassified (model bug — fix). The
corpus should seed lane d with cases in class (b) on purpose — e.g. the
`mainfirst` shape from §3, where the racy access is reachable only under a
schedule `go run` essentially never produces — because they pin that our
refusal is *reasoned from the model*, not parroting the detector.

---

## 3. Go-side sampling reality — measured

Probe: `.tmp/conc-probe/` (this worktree), four race-free programs with
schedule-dependent observables, each compiled once (plain and `-race`) with
go1.26.5, each binary run N=100 per configuration. **[FACT]** — all numbers
below are from `.tmp/conc-probe/results.txt`, this machine (idle load), this
session.

**spawnorder** — three goroutines send their id (1,2,3) into a `chan int`
cap 3; observable = arrival order (6 possible permutations):

| config | distribution (N=100) |
|---|---|
| default | 312=86, 132=10, 123=3, 321=1 (4/6 perms) |
| GOMAXPROCS=1 | 312=100 (1/6 — fully deterministic) |
| GOMAXPROCS=2 | 312=96, 132=2, 321=2 |
| GOMAXPROCS=8 | 312=89, 132=7, 321=3, 123=1 |
| GODEBUG=asyncpreemptoff=1 | 312=93, 132=6, 321=1 |
| **-race** | **312=25, 123=28, 213=19, 321=13, 132=9, 231=6 (6/6 perms)** |
| -race + GOMAXPROCS=1 | 312=47, 213=25, 123=17, 321=11 (4/6) |

**mainfirst** — spawn a child that sends on a buffered channel; main
immediately does `select` with `default`; observable = did the child run
first ("child-first") or not ("main-first"):

| config | distribution |
|---|---|
| ALL seven configs incl. -race | main-first=100 |

**selectpick** — `select` over two ready channels (the spec's "uniform
pseudo-random" latitude):

| config | distribution |
|---|---|
| all configs | ~50/50 (e.g. default 52/48, GOMAXPROCS=1 47/53) |

**pingcount** — two goroutines each send 4 tagged values into a shared
buffered channel; observable = the merged tag order, C(8,4)=70 possible:

| config | distribution (N=100) |
|---|---|
| default | bbbbaaaa=100 |
| GOMAXPROCS=1 | bbbbaaaa=100 |
| GOMAXPROCS=2 | bbbbaaaa=100 |
| GOMAXPROCS=8 | bbbbaaaa=99, aaaabbbb=1 |
| GODEBUG=asyncpreemptoff=1 | bbbbaaaa=100 |
| -race | aaaabbbb=53, bbbbaaaa=47 |
| -race + GOMAXPROCS=1 | aaaabbbb=55, bbbbaaaa=45 |

Across all 700 runs: **3 distinct orders of 70 possible, and every one of
them is a whole-burst order** — one goroutine's four sends complete before
the other's begin. Not a single genuinely interleaved order (e.g. `abab…`)
was ever observed, under any knob, including `-race`.

**[ANALYSIS] Calibration of the doctrine's claim.** "Scheduling sampling is
nearly useless" is *confirmed and sharpened*:

1. **Plain `go run` is worse than useless as an explorer — it is a biased
   point-mass.** One permutation takes 86–100% of mass; GOMAXPROCS=1 is
   perfectly deterministic (the runnext/FIFO structure of the scheduler is
   the visible bias: 312 = last-spawned-first via runnext, then FIFO). 100
   default runs explored 4 of 6 orderings of the *simplest possible* 3-way
   race; on pingcount, 500 non-race runs explored 1–2 of 70 orders, and all
   700 runs (race included) explored 3 of 70 — every one burst-shaped.
2. **Depth-1 corners can have empirical probability ≈ 0.** `mainfirst` is a
   *depth-1* behavior (one scheduling constraint: run the child before
   main's select) and 700 runs across every knob never exhibited
   child-first. A membership lane sampling `go run` can therefore never
   confirm such corners exist in real Go — they are confirmed by spec text
   (the `go` statement gives no scheduling promise) and by review, exactly
   the doctrine's too-wide/review lane. Conversely: had our model *excluded*
   child-first (a too-narrow bug), sampling would never catch it either.
   This is the concrete number behind "the membership lane's sampling is
   dense for maps and nearly blind for scheduling."
3. **`-race` is a genuinely strong diversifier of COARSE order and useless
   for FINE interleaving.** Bright spot: 6/6 permutations at near-uniform
   spread on spawnorder (vs ≤4/6 for every non-race config) — the TSan
   runtime's synchronization jitters goroutine startup enough to act as a
   crude chaos mode. Doctrine update candidate: `-race` is not just the
   racy-boundary second oracle, it is also the membership lane's best
   Go-side sampler and should be a default sample source for concurrent
   membership cases. But pingcount tempers it: even `-race` only ever
   flipped WHICH whole burst went first (2 orders), never produced a
   fine-grained merge — 3/70 orders total across 700 runs, all burst-shaped.
   And mainfirst stayed 100/100 main-first even under `-race`. Go-side
   sampling explores coarse spawn/startup order at best; the interior of
   the interleaving lattice is machine-enumerator-only territory.
4. **`select` latitude is NOT scheduling latitude.** The spec's randomized
   `select` pick is re-randomized per execution like map order — dense
   sampling, ~uniform in 100 runs. So `select`-pick membership cases will
   behave like today's map cases (good sampling density), while
   goroutine-interleaving cases will not. The arc note should keep these two
   consumption sites' testing stories separate even though both are
   "concurrency".

---

## 4. The concurrency corpus — proposed lane taxonomy

**[RECOMMENDATION]** Six lanes. For each: the pass criterion, what a PASS
means epistemically, and what it structurally cannot show.

### (a) Sequential-degenerate — the bedrock

Every existing corpus case, unchanged, plus concurrency-syntax cases with no
actual concurrency (a `go` that is joined before any observation, a channel
used within one goroutine). Pass = today's strict-lane equality, bit-identical
baseline (`baselines/native-full.tsv` untouched modulo deliberate re-pins).
PASS means: the concurrency machinery is *conservative* — adding the
scheduler site did not perturb deterministic programs (the analog of the
append-envelope's "empty stream resolves to the old point",
`nondeterminism-doctrine.md:75-77`). Cannot show: anything about real
interleaving. This lane is the no-regression gate the whole arc rides on;
the scheduler site must consume NOTHING (or a provably single-valued pick)
when exactly one goroutine is runnable, so sequential streams stay `[]`.

### (b) Confluent concurrent — strict-strength claims, machine-certified

Programs whose observable is provably schedule-independent: ping-pong
rendezvous, single-producer/single-consumer pipeline, worker pool whose
observation is an order-insensitive fold (sum/max), WaitGroup-joined
fork-join. **Certification of confluence is mechanical, not argued**: run the
enumerator; require |enumerated set| = 1. The lane's existing singleton
*failure* ("belongs in the strict lane",
`membership-lane-design.md:19-21`) inverts into this lane's *pass
precondition*, then the singleton member must equal `go run`'s observation
(strict-lane equality restored, now meaningful because every schedule was
checked to agree). PASS means: for this program, our entire admitted
interleaving set collapses to one observation AND that observation is Go's —
differential verification recovered at full strength. Cannot show: anything
beyond depth/width caps (a schedule past `--max-sites` could in principle
diverge — the cap fails loud, so an uncertifiable case is visibly red, never
quietly confluent); and nothing about programs outside the certified one.
Structural confluence arguments (session-typed shapes, single-consumer
disciplines) belong in the case's `why` as *explanation*, but the enumerator
is the gate — hand-waved confluence is exactly how a schedule-dependent case
would launder itself into a strict-looking pass.

### (c) Schedule-dependent — membership with interleaving enumeration

Observables that genuinely vary by schedule (spawnorder's permutation,
first-arrival winner, interleaved append order). Pass = today's membership
criterion verbatim: every Go sample ∈ enumerated set, singleton guard,
fail-closed on any enumerator overrun, samples to include `-race` runs
(§3.3). Width = max goroutine count; sites bound = communication count;
`why` argues both. PASS means: Go's exhibited corner lies inside our
envelope, and the envelope was exhaustively enumerated at communication
granularity for race-free programs (the §1.4 certificate). Cannot show: that
the unexhibited members are Go-realizable (§3.2 — most never will be
exhibited; that is the review lane / width-signal metadata, already the
lane's design), nor anything about racy programs (refused before this lane
applies). Expect |exhibited|/|enumerated| to be *far* smaller than for maps —
record it, don't fail on it (per the existing width-signal doctrine).

### (d) Racy — negative lane, two oracles

Programs with a data race (unsynchronized counter, racy flag spin, racy
map access — including the memory-model litmus racy variants of lane e).
Machine side: EVERY enumerated interleaving path must end in the explicit
race refusal (the fail-closed status; a single value-leaf = model bug, per
§1.3 obligation 1). Go side: `go run -race` over R samples; expected = at
least one red. PASS means: our refusal is justified by a witnessed real race
(remember TSan's no-false-positive property — one red sample is proof the
race exists). The `-race`-all-green + our-refusal combination is NOT a pass:
it lands in the doctrine's "investigate" branch with the three-way outcome
of §2.7 — and the corpus deliberately includes known class-(b) cases
(sampling-invisible races) whose expected status records the investigation's
conclusion, so the gate doesn't silently normalize them. Cannot show: that
our race *check* is complete over programs outside the corpus (only review
and the eventual NPDRF-style theorem give that), nor anything about the
racy program's values (we refuse to have opinions there — that is the
lane's point).

### (e) Litmus shapes — pinning the DRF-SC boundary

Message-passing (MP), store-buffering (SB), load-buffering, IRIW — each in
two forms: (i) channel-synchronized (race-free) — belongs to lane b or c and
must admit exactly the SC-reachable outcomes (e.g. MP with a channel signal:
the stale read must NOT be in our enumerated set — its presence would mean
our happens-before is broken); (ii) racy shared-variable form — belongs to
lane d and must refuse. PASS means: the envelope's *edges* are where the
memory model says (SC inside DRF, refusal outside), which is precisely the
"envelope fidelity argued against spec text" audit dimension made
executable. Cannot show: weak-memory behaviors (we refuse the programs that
could exhibit them — deliberate, per doctrine; a Go implementation's actual
weak behavior on a racy program is outside our claim by design and must be
documented as such in the transfer caveat).

### (f) Deadlock and leak

**[FACT]** (probed this session, `.tmp/conc-probe/{deadlock,leak}/`): global
deadlock is a real `go run` observable — "fatal error: all goroutines are
asleep - deadlock!" with a goroutine dump, program exit status 2 (`go run`
itself exits 1, printing "exit status 2") — while a *partial* leak (one goroutine
blocked forever, main exits) is observably NOTHING on the Go side: normal
output, exit 0. So the lane splits:

- **Global deadlock**: differential-testable. Our model's terminal "no
  runnable goroutine, not all exited" maps to an explicit deadlock
  observation; strict/confluent-style comparison against the fatal-error
  observable (comparing our refusal-style status to Go's exit-2 + message
  class, not the goroutine dump text). If deadlock is schedule-dependent
  (deadlocks only under some interleavings), the case is lane-c-shaped with
  deadlock as one member — and `go run` sampling will usually miss it (§3),
  so expected-status bookkeeping must allow "Go samples all ok, deadlock ∈
  enumerated set" as the recorded, reviewed state. Mixed-terminal cases
  (some leaves a value, some deadlock) are legitimate members of the
  enumerated set — unlike lane d's race refusal, deadlock is a defined
  Go behavior, not UB.
- **Partial leak**: model-only observable. Our terminal state knows the
  leaked goroutine set exactly; Go's runtime says nothing (goleak exists
  precisely because of this gap, §2.7). Pass criterion is therefore
  machine-internal (expected leak set as case metadata) + the sequential
  observable still matching Go. Epistemically honest label: this is
  SELF-consistency plus review, not differential validation — the oracle
  cannot see the property. A `go test`+goleak harness could add a weak
  second oracle later; quarantined like synctest (§2.6) since it changes
  the program shape.

PASS means (both halves): the blocking semantics of channels — the thing
deadlock is made of — agrees with Go where Go can express an opinion, and is
internally coherent where it cannot. Cannot show: liveness (deadlock-freedom
of nonterminating-by-design programs is a temporal property outside a
terminating-run corpus entirely — that is §5 and the proof side's job).

**Cross-cutting corpus rules** carried over unchanged: guardrails first (the
lane-e/d cases exist and classify RED before the scheduler site is
implemented — visible feature-blocked, never false-pass); every red records
its `Choices` stream for replay (§2.4); one semantic concern per case;
canonical Go untouched.

---

## 5. The fairness quantifier

### 5.1 The bound finding

**[FACT]** The doctrine records the finding this section must answer
(`nondeterminism-doctrine.md:114-118`): "∀-stream termination is FALSE for
correct programs that spin-wait on another goroutine (unfair schedules
starve the writer). Concurrency termination claims need an explicit
fairness-constrained quantifier, decided in the design note — not discovered
as an unprovable theorem."

### 5.2 What the field does

- **TLA+** **[FACT-recalled]** (Lamport, *The Temporal Logic of Actions*,
  TOPLAS 1994): weak fairness WF_v(A) — an action continuously enabled is
  eventually taken; strong fairness SF_v(A) — enabled infinitely often ⇒
  taken infinitely often. Liveness properties are proved under explicit
  WF/SF conjuncts chosen per-spec; the spec says which fairness it assumes,
  which is exactly the honesty discipline we want.
- **Process algebra** **[FACT-recalled]**: fair/divergence-sensitive
  equivalences (e.g. CSP's divergence-free refinement, fair testing) — the
  lesson being that "may diverge under some scheduler" and "diverges under
  fair schedulers" are different observables and conflating them makes
  equivalences either too fine or too coarse.
- **Iris-family**: (i) **later credits** **[FACT-recalled]** (Spies et al.,
  ICFP 2022) are about eliminating step-indexing bookkeeping, not scheduler
  fairness — relevant to proof ergonomics, not to this quantifier choice;
  don't conflate. (ii) **Termination-preserving refinement**: Tassarotti,
  Jung, Harper, ESOP 2017 **[FACT-recalled]** — refinement preserving
  termination under fair schedulers for a compiler, in Iris, with
  significant machinery. (iii) **Simuliris** **[FACT]** (Gäher et al., POPL
  2022, verified this session): "the first simulation technique to establish
  termination preservation *under a fair scheduler* for a range of
  concurrent program transformations"; notably it handles stuttering via a
  least-fixed-point formulation instead of explicit stutter counters, and —
  per follow-up work — it can *exploit* UB/DRF assumptions but cannot
  exploit fairness of the source nor prove general liveness. (iv) **Fair
  Operational Semantics** **[FACT]** (Lee, Cho, Kim, Moon, Song, Hur, PLDI
  2023, verified this session; Coq artifact github.com/snu-sf/fairness):
  expresses arbitrary fairness notions *as operational semantics* (fairness
  counters woven into the step relation), with thread-local simulation and
  resource-algebra reasoning; induction over the fairness counter discards
  unfair executions. This is the closest blueprint for "fairness as a
  constraint on the Choices stream" done at proof scale. (v)
  **Perennial/Goose** **[FACT]** (`deps/perennial`, repo checkout): the Go
  verification stack we most resemble proves *partial correctness and crash
  safety* — its WPs make NO termination claims, so it never needs the
  quantifier at all. That is a legitimate option (iv below) with a real
  precedent.

### 5.3 The concrete question and the mechanism

**[ANALYSIS]** In our model a schedule is not an opaque adversary — it is
the very `Choices` stream the theorems already ∀-quantify. Two structural
facts shape the options:

1. The scheduler site picks among *runnable* goroutines only. A goroutine
   blocked on a channel is not in the pick set, so no stream can "starve" a
   blocked-on-you partner into deadlock-by-neglect: if the only runnable
   goroutine is the writer, every stream picks it. Starvation requires the
   starved-of-progress computation to coexist with a *runnable* spinner —
   i.e. a busy-wait.
2. Therefore, for programs whose only inter-goroutine waiting is BLOCKING
   (channels, WaitGroup-as-channels — no spin loops on shared state), every
   stream, fair or not, drives the program to its terminal: ∀-stream
   `Terminates` is TRUE for the entire blocking-discipline class. The
   doctrine's counterexample is precisely and only the spin-wait class.

This yields the options with honest proof-burden estimates:

- **(i) Fair-stream termination.** Define `Fair : Choices-run → Prop` — the
  natural candidate over our structure is weak fairness at the site: no
  goroutine remains runnable-and-unpicked forever (formally: on every
  infinite consumption trace, every goroutine index that is runnable
  cofinally often is picked infinitely often). Claim:
  `∀ stream, Fair stream → Terminates`. TRUE for spin-wait programs that are
  correct-under-fairness; matches the spec's actual promise level — which is
  NONE: the Go spec text nowhere promises scheduling fairness (the `go`
  statement section makes no scheduling guarantee; the runtime happens to be
  preemptive since 1.14, but that is implementation, not spec — so `Fair` is
  an ASSUMPTION we must label as exceeding the spec, the mirror image of an
  envelope: a *narrowing* of the quantifier justified by "every real Go
  scheduler is fair in this sense", which itself is an implementation
  observation, not spec text). Proof burden: HIGH — fairness is a property
  of infinite traces, so this drags in coinductive/temporal machinery
  (FOS-style fairness counters are the mechanized-precedent route); the
  existing kernel-reducible `Terminates` kit (fuel + first-order readout)
  does not extend directly, because "for all fair streams" has no finite
  fuel bound uniform in the stream. Statement-TCB risk: the doctrine
  requires headline statements readable over base definitions — `Fair` must
  be a small, first-order-readable definition or it pollutes the statement
  TCB.
- **(ii) Terminating-modulo-scheduler classes** — expose termination as a
  per-program classification ("terminates under all streams" / "under fair
  streams" / "diverges"), i.e. make the quantifier part of each theorem's
  statement rather than one global choice. This is just (i)+(iii) as a
  labeled family; its cost is taxonomy, not new proof machinery beyond (i)'s
  for the fair-only class.
- **(iii) ∀-stream termination for the blocking-discipline class.** Claim
  `∀ stream, Terminates` exactly for programs with no spin-waits — by fact
  2 this is TRUE there, needs NO fairness definition, no temporal logic, no
  coinduction, and the existing fuel-based `Terminates` machinery works
  unchanged: the fuel bound is uniform because every step makes progress
  toward the terminal regardless of picks (proof shape: a well-founded
  measure on the multiset of per-goroutine remaining work — the same
  well-founded-recursion discipline the interpreter already lives by).
  Burden: LOW-MEDIUM. Coverage: the entire planned concurrent corpus and,
  plausibly, most of raft's actual structure (etcd raft's goroutines block
  on channels/selects; worth checking in `deps/raft` during the arc rather
  than asserting). Limitation: excludes spin-wait programs — but honestly,
  visibly, as a class restriction in the statement, not as a hidden premise.
- **(iv) No termination claims (Perennial's position).** Zero burden, zero
  claim; safety/refinement only. Recorded as the fallback, not the
  recommendation — the project already has a sequential `Terminates`
  headline and should not silently drop strength when concurrency lands.

**[RECOMMENDATION]** Adopt (iii) NOW as the arc's termination story — it is
the honest quantifier that is actually provable with the existing kit, it
covers the corpus, and its class restriction ("no spin-waits") is
mechanically checkable syntactically-ish (no shared-variable loop conditions;
in a DRF-fail-closed model, a spin-wait on a non-atomic shared variable is
racy and refused anyway — worth making this observation precise in the arc
note, because it may make the blocking class = the entire admitted class,
i.e. DRF-fail-closed + no atomics support ⇒ every admitted concurrent
program is blocking-disciplined and (iii) degenerates to plain ∀-stream
`Terminates` over the admitted class, with NO restriction needed in the
statement). Defer (i) until atomics land (the first spin-wait that is
race-free requires atomics), and when it does, take FOS (PLDI 2023) as the
mechanization blueprint and state `Fair` as a first-order stream predicate
with an explicit above-spec-assumption caveat in the transfer note. Spec
honesty per the doctrine's binding-quote discipline: the claim's docstring
must say the Go spec promises no fairness, so fair-stream theorems transfer
to real Go only under an empirical scheduler assumption.

---

## 6. Strategy summary (the recommended shape of the arc)

**[RECOMMENDATION]**

1. **Model**: scheduler = one `Choices` site at communication points only;
   envelope statement = spec text + the DRF reduction argument (Xiao et al.
   ICTAC 2018 as the citable theorem shape; Fava et al. FM'18/JLAMP as the
   Go-specific operational SC-DRF precedent) + the race-refusal coupling.
   Races fail closed on every path; one racy leaf poisons the case.
2. **Guardrails first**: lanes (a)–(f) cases written and classifying red
   before the site is implemented. Litmus shapes from the weak-memory
   literature enter as channel/racy pairs.
3. **Testing machinery**: extend the membership enumerator (it already is an
   interleaving explorer at communication granularity); confluent lane =
   singleton certification + strict equality; full enumeration first, DPOR
   (source sets) later behind a both-explorers cross-check; PCT-stream
   sampling as the machine-side fuzz layer beyond enumeration budgets;
   `-race` samples as a default Go-side diversity source (measured 6/6 vs
   4/6 permutation coverage, §3).
4. **Epistemics recorded per lane** (§4): confluent = recovered
   verification; membership = envelope sanity; negative = justified refusal;
   width-signal metadata for the never-exhibited majority; depth-1 corners
   acknowledged as sampling-invisible (mainfirst: 0/700).
5. **Termination**: ∀-stream over the blocking-disciplined (= likely the
   entire admitted) class now; fairness-constrained quantifier deferred to
   atomics, with FOS as blueprint and an explicit above-spec caveat.
6. **Proof ledger additions**: coarse≡fine scheduling equivalence over
   GoCore; race-check completeness (NPDRF analog); the granularity ledger
   becomes enumerator-testable the day the site lands — schedule that test
   early, it is the first time BUG-002's defect class has an executable
   detector.

## Sources consulted this session (web)

- PCT: https://dl.acm.org/doi/10.1145/1736020.1736040 ;
  https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/asplos277-pct.pdf
- CHESS: https://www.usenix.org/legacy/event/osdi08/tech/full_papers/musuvathi/musuvathi.pdf ;
  PLDI 2007 iterative context bounding (ACM)
- SCTBench: https://dl.acm.org/doi/10.1145/2692916.2555260 ; TOPC 2016
  https://dl.acm.org/doi/10.1145/2858651
- Optimal DPOR / source sets: https://dl.acm.org/doi/10.1145/3073408 ;
  https://user.it.uu.se/~parosha/publications/papers/popl2014.pdf
- Non-preemptive semantics for DRF programs (ICTAC 2018):
  https://link.springer.com/chapter/10.1007/978-3-030-02508-3_27
- Lipton reduction: https://dl.acm.org/doi/pdf/10.1145/361227.361234
- DRF0: https://dl.acm.org/doi/10.1145/325096.325100
- Go memory model: https://research.swtch.com/gomm ;
  https://github.com/golang/go/issues/50590
- Fava/Steffen/Stolz: https://link.springer.com/chapter/10.1007/978-3-319-95582-7_15 ;
  JLAMP 103 (2019); https://github.com/dfava/mmgo ; SEFM 2020
  https://link.springer.com/chapter/10.1007/978-3-030-58768-0_2
- GFuzz: https://dl.acm.org/doi/10.1145/3503222.3507753 ;
  https://songlh.github.io/paper/gfuzz.pdf
- Simuliris: https://dl.acm.org/doi/10.1145/3498689 ;
  https://iris-project.org/pdfs/2022-popl-simuliris.pdf
- Fair Operational Semantics: https://dl.acm.org/doi/10.1145/3591253 ;
  https://github.com/snu-sf/fairness
