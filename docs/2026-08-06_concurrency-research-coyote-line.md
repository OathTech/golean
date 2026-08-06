# The Coyote / P# / P lineage: architecture and lessons for GoLean's choice-stream scheduler

Research note, 2026-08-06. Charter: deep dive on the industrial systematic-concurrency-testing
line (Coyote nee P#, the P language, and adjacent industrial simulation lines) for
transplantable architecture and engineering lessons. Companion to the sibling worker's
broad validation-strategy survey. Tagged [FACT] (with citation) vs [ANALYSIS].

Our frame throughout: GoLean's interpreter is total and deterministic given a `Choices`
stream; the scheduler will be one more consumption site on that stream, so a schedule IS a
replayable input and the interpreter is natively a controlled-scheduler runtime
(`docs/2026-08-04_nondeterminism-doctrine.md`).

---

## 1. Architecture: how Coyote takes control, and where we are stronger

### 1.1 The lineage in one paragraph

[FACT] P# (PLDI 2015, Deligiannis, Donaldson, Ketema, Lal, Thomson: "Asynchronous
programming, analysis and testing with state machines") was a C#-embedded language of
communicating state machines co-designed with static race analysis and a systematic
testing runtime; its tester took over scheduling of machine operations and its DFS
explored 7.6x more schedules/sec than CHESS on average.
(https://dl.acm.org/doi/10.1145/2737924.2737996,
https://www.doc.ic.ac.uk/~afd/papers/2015/PLDI_PSharp.pdf)
[FACT] The P# codebase evolved into Coyote, which kept the actor framework but
generalized to unmodified C# task-asynchronous programs ("The origin of the Coyote
codebase can be traced back to an earlier system called P# that defined a restricted
(domain-specific) programming model for communicating state machines" — TACAS 2023
paper). Coyote (TACAS 2023, "Industrial-Strength Controlled Concurrency Testing for C#
Programs with Coyote", Deligiannis, Senthilnathan, Nayyar, Lovett, Lal; Best Software
Science Paper) is the industrial tool used by Azure teams.
(https://link.springer.com/chapter/10.1007/978-3-031-30820-8_26,
https://www.microsoft.com/en-us/research/wp-content/uploads/2023/04/978-3-031-30820-8_26.pdf)

### 1.2 Taking control: binary rewriting + a sequentializing test engine

[FACT] (TACAS 2023) Controlled concurrency testing (CCT) "proposes taking over the
scheduling of concurrent workers and then using algorithms, either randomized or
systematic, for searching over the space of interleavings. Taking over scheduling is
typically an engineering challenge requiring understanding of the language runtime."
Coyote's answer is `coyote rewrite`: a CIL (bytecode) rewriting engine that traverses the
assembly and instruments it with hooks, via four built-in passes — type rewriting
(replace `Task` etc. with controlled Coyote types), task API rewriting, async rewriting,
and inter-assembly invocation rewriting. The rewriting engine is ~12K lines; the test
engine ~11K; Coyote is ~45K lines total plus 38K lines of unit tests.

[FACT] (TACAS 2023) The controlled-testing engine (CTE) sequentializes execution: at a
scheduling point "CTE blocks the current worker, then looks at the list of workers that
are enabled (by inspecting their pause-predicates, if any). It will then query the
exploration strategy to select one worker from this list. The selected worker is
unblocked (rest all workers remain blocked)" and runs until it hits a scheduling point
again. "This design, of sequentializing workers to execute only one-at-a-time is fairly
standard in CCT tools." Enabledness is tracked by pause-predicates: e.g. a worker paused
acquiring a lock becomes enabled when the lock is released.

[FACT] (TACAS 2023) The strategy interface is minimal: "At its core, the interface has a
single method that accepts a list of enabled workers and must return one of them."

[ANALYSIS] That interface — (enabled set) → (chosen worker) — is exactly a
choice-consumption site. Coyote spent ~24K lines (rewriting + engine) building what our
architecture gives by construction: we OWN the interpreter, so every goroutine step is
already mediated by `stepFn`, the enabled set is a computable function of machine state,
and "taking control" is a no-op. There is no interception layer to trust, no rewriting
pass to keep in sync with new .NET APIs, no uncontrolled-concurrency detection problem
(§4.3 below). This is the single largest engineering asset we get for free, and it is the
same asset FoundationDB/TigerBeetle buy by writing their entire system against a mocked
runtime — except we get it for arbitrary (supported-subset) Go programs, not for one
codebase written under discipline.

### 1.3 Scheduling-point granularity and the soundness coarsening argument

[FACT] (TACAS 2023) "Coyote only instruments at the level of task APIs or synchronization
operations." It deliberately does NOT instrument individual memory accesses: "Coyote does
not currently support the detection of low-level data races, i.e., unsynchronized memory
accesses ... Race detection requires instrumentation at the level of individual memory
accesses, which Coyote avoids for engineering simplicity and lower maintenance costs."

[FACT] The soundness argument for that coarsening is CHESS's (Musuvathi, Qadeer, Ball,
Basler, Nainar, Neamtiu, "Finding and Reproducing Heisenbugs in Concurrent Programs",
OSDI 2008): scheduling/preemption only at synchronization operations is sufficient for
DATA-RACE-FREE programs — for a DRF program, every observable behavior is equivalent to
some execution that context-switches only at synchronization operations (the DRF
reduction). CHESS restored soundness for racy programs by pairing the scheduler with a
happens-before race detector and adding detected racy accesses as extra scheduling
points.
(https://www.usenix.org/legacy/event/osdi08/tech/full_papers/musuvathi/musuvathi.pdf)

[FACT] Contrast: the original PCT tool (ASPLOS 2010, §2 below) chose FINE granularity —
"PCT works on unmodified x86 binaries. It employs binary instrumentation to insert calls
to the scheduler after every instruction that accesses shared memory or makes a system
call" — because its probabilistic guarantee is stated over instruction-level steps k, and
races are among the bugs it targets.
(https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/asplos277-pct.pdf)

[ANALYSIS] Transfer to our pick-at-communication-points question. The lineage gives a
precise two-part doctrine: (1) coarse scheduling points (task/sync/communication
operations) are SOUND relative to the DRF fragment — Go's own memory model makes racy
programs essentially undefined, and our doctrine already claims SC-interleaving only for
race-free programs (DRF-SC territory; nondeterminism-doctrine note, matching
Goose/Perennial). (2) The coarsening must be paired with an INDEPENDENT check for the
excluded class: CHESS used an inline race detector; our analogue is the already-planned
`go run -race` second oracle plus fail-closed classification of racy programs. The
important negative lesson: Coyote consciously DROPPED part (2) for engineering cost and
documents it as a known blind spot; we should not — our race-oracle boundary is cheap
because it is external (`go run -race`), not an instrumentation burden. Also note the
granularity ledger connection: what Coyote calls "where scheduling points get inserted"
is exactly our step-atomicity question (BUG-002 class), and their experience says
differences in scheduling-point placement subtly change tool behavior ("A direct
comparison with prior tools is difficult because there can still be subtle differences in
how scheduling points get inserted" — TACAS 2023). Our scheduling points should be fixed
in the SEMANTICS (choice-consumption sites at communication/synchronization operations in
GoCore), not in a frontend layer, so their placement is auditable as part of the model.

---

## 2. Exploration strategies: algorithms + empirics

### 2.1 Random walk (RW) with seeds

[FACT] (TACAS 2023) "The random walk strategy (RW) picks an enabled worker uniformly at
random in each step. This simple strategy has been shown to be effective in practice and
argued as a necessary baseline for other strategies", citing the SCTBench empirical study
(Thomson, Donaldson, Betts, "Concurrency Testing Using Controlled Schedulers: An
Empirical Study", ACM TOPC 2016 — which compared DFS, preemption bounding, delay
bounding, controlled random, and PCT and found the naive random scheduler an
embarrassingly strong baseline). Coyote test iterations are seed-driven; the found-bug
trace records all decisions for replay (§4).
(https://dl.acm.org/doi/10.1145/2858651)

[FACT] (PCT paper, ASPLOS 2010) Naive per-step coin-flipping has provably BAD worst-case
guarantees for ordering bugs: to order one specific step of thread A before one of thread
B, a uniform random walk can have exponentially small probability (the paper's §2.4
"Naive Randomization" argument) — which is what motivates priority-based randomization.

### 2.2 PCT: the algorithm and the exact guarantee

[FACT] (Burckhardt, Kothari, Musuvathi, Nagarakatte, "A Randomized Scheduler with
Probabilistic Guarantees of Finding Bugs", ASPLOS 2010;
https://dl.acm.org/doi/10.1145/1736020.1736040, PDF
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/asplos277-pct.pdf)

Bug depth: "the depth of a concurrency bug [is] the minimum number of ordering
constraints on thread events that will reliably reveal the bug" (formally, the minimal
size of a "directive" guaranteed to find it, Def. 5/8). Empirically-motivated
classification: "ordering bugs have depth 1, atomicity violations and non-serializable
interleavings, in general, have depth 2, and deadlocks caused by circular lock
acquisition have depth 2."

Algorithm (priority-based; lower number = lower priority; only the highest-priority
enabled thread runs):
1. Assign the n threads random initial priorities from {d, d+1, ..., d+n} (a random
   permutation offset above the change-point values).
2. Pick d−1 random priority change points k1, ..., k(d−1) uniformly in [1, k]; change
   point ki carries priority VALUE i.
3. Run the highest-priority enabled thread each step; "when a thread reaches the i-th
   change point (that is, when it executes the ki-th step of the execution)", its
   priority drops to i.
(For d = 1 there are no change points — pure random priority order.)

The theorem, verbatim (Theorem 9): "Let P be a program with a bug B of depth d, let
n ≥ maxthreads(P), and let k ≥ maxsteps(P). Then Pr[RandS(n, k, d) ∈ B] ≥ 1/(n·k^(d−1))."

Amplification: "running PCT repeatedly with different random seeds ensures that a
concurrency bug can be found with an arbitrarily large probability" (independent runs).
Empirics: PCT found known and previously-unknown bugs in production-scale programs
(including Mozilla Firefox and Internet Explorer rendering components) despite large k;
an effective-k optimization (k_eff, restricting change points to synchronizing/racing
steps) tightens the bound in practice.

[FACT] (TACAS 2023) Coyote implements PCT at task granularity and found it degraded on
task-heavy programs: modern async code creates many short-lived tasks, diluting priority
change points. Their fix, PCTt, "adapts the concept of chains" (from PCTCP): "On the
explicit creation of a task (using Task.Run), it gets assigned to a new chain (hence, it
gets a randomly-generated priority). If a task t yields control by executing Task.Yield,
the continuation task is assigned to the same chain as t (hence, it inherits its
priority)" — i.e., priorities attach to logical control-flow chains, not raw task
objects. On their running example PCTt finds the bug with probability 50% where PCT and
RW are diluted. The distributed-systems generalization is PCTCP (Ozkan, Majumdar, Niksic,
Mousavi Befrouei, Weissenbacher, "Randomized testing of distributed systems with
probabilistic guarantees", OOPSLA 2018), which re-derives a PCT-style d-hitting guarantee
over MESSAGE/EVENT orderings using online chain partitioning.
(https://dl.acm.org/doi/10.1145/3276530)

### 2.3 Delay bounding (DB)

[FACT] (Emmi, Qadeer, Rakamaric, "Delay-Bounded Scheduling", POPL 2011) A deterministic
scheduler (e.g. round-robin or FIFO) is augmented with a budget of d "delay" operations
— at a delay, the scheduler skips the thread it would have run and moves on. The set of
behaviors explored grows monotonically with d and covers all schedules in the limit;
small d covers a surprising fraction of bugs, generalizing CHESS-style context bounding
to asynchronous/event-driven programs. (https://soarlab.org/papers/2011_popl_eqr.pdf)
[FACT] Coyote implements DB as one of its strategies (TACAS 2023 evaluation uses d = 10
for protocols, d = 5 on SCTBench).

### 2.4 Portfolio, and how many schedules industry actually needs

[FACT] (TACAS 2023) Strategies "can also be combined either in the same test iteration
(run one strategy for certain number of steps, then switch to running another strategy)
or across iterations (pick a different strategy, in a round-robin fashion, for each
iteration)." The docs recommend `--strategy portfolio`, configurable fair/unfair
(`Configuration.WithPortfolioMode`). (https://github.com/microsoft/coyote/blob/main/History.md,
https://microsoft.github.io/coyote/)

[FACT] (TACAS 2023 evaluation) Three experiments, effectiveness = number of times the
known bug is hit in a fixed budget of iterations:
- ProdService (real Azure service, 54K lines C#, 21 buggy tests): degree of concurrency
  (max simultaneously enabled workers) 5–16, scheduling decisions per run 94–1054; PCTt
  generally dominates PCT and RW on task-heavy code.
- Buggy protocol implementations (ChainReplication, Chord, FailureDetector, Paxos, ...):
  budget 10K iterations (100K for FailureDetector/Paxos), PCT/PCTt/DB with d = 10.
  Verdict, verbatim: "Three schedulers (PCT, PCTt and DB) find all the bugs, but none is
  a clear winner. A combination of schedulers is likely required for reliably finding
  bugs in a small number of iterations."
- SCTBench (C/C++, ported): Coyote's numbers roughly agree with the original POS/PCT
  papers.

[FACT] (FAST 2016, Deligiannis et al., "Uncovering Bugs in Distributed Storage Systems
during Testing (Not in Production!)") P# testing of three Microsoft systems — Azure
Storage vNext, Live Table Migration, Service Fabric — found 8 serious bugs (subtle
concurrency+failure combinations that had escaped conventional testing), each "uncovered
in a small setting and witnessed by a full system trace." Modeling effort: two
person-weeks (vNext) to five person-months (Service Fabric).
(https://blog.acolyer.org/2016/05/05/uncovering-bugs-in-distributed-storage-systems-during-testing-not-in-production/,
https://www.usenix.org/conference/fast16/technical-sessions/presentation/deligiannis)

[ANALYSIS] The small-scope empirics are remarkably consistent across the lineage: bugs
manifest in SMALL instantiations (2–3 nodes/machines), within 10^3–10^5 schedules, at
small depth d (1–3), with run lengths of 10^2–10^3 scheduling decisions. Nobody in
industrial practice enumerates exhaustively; the game is biased sampling with guarantees
(PCT), diversity (portfolio), and iteration throughput. This calibrates our harness
budget expectations: a differential concurrency lane running ~10^4 stream samples per
case at corpus scale is in the empirically-validated regime.

---

## 3. Liveness and fairness: temperature under fair schedules

### 3.1 The mechanism

[FACT] (Coyote docs, "Find liveness bugs effectively",
https://microsoft.github.io/coyote/how-to/liveness-checking/) Liveness specs are monitor
state machines with states marked Hot (obligation pending) or Cold (obligation met);
unmarked states are "warm". Two implicit assertions: "any terminated execution of the
program must not have a monitor in a hot state" (a safety property), and "the program
should not have infinite executions that remain in hot (or warm) states infinitely
without transitioning to a cold state." Since infinite executions cannot be generated,
the heuristic is temperature: "The temperature goes up by a unit if the monitor
transitions to a hot state, it goes to zero on a transition to a cold state and stays
the same on transition to a warm state." The tester flags a liveness bug when "the
temperature of a monitor exceeds a particular large threshold because it indicates a
long suffix stuck in hot/warm states without transitioning to a cold state." With
`--max-steps N`, unfair-scheduler executions halt at N steps while fair-scheduler
executions run to 10N (`--max-fair-steps` / `--max-unfair-steps` set these directly;
`--liveness-temperature-threshold` sets the flag threshold). A bound-free alternative is
lasso detection via partial-state caching (Desai et al., "Lasso Detection using
Partial-State Caching", FMCAD 2017,
https://ankushdesai.github.io/assets/papers/liveness.pdf).

### 3.2 The exact fairness notion they test under

[FACT] (TACAS 2023, verbatim modulo ligatures) "Any exploration strategy can be used for
liveness checking, as long as it is fair, i.e., it does not contiguously starve an
enabled worker for a long time. Unfairness can easily lead to liveness violations, but
such violations are considered false positives because they cannot happen in practice as
system scheduling is generally fair." And: "RW is (probabilistically) fair, but PCT is
not. Coyote converts unfair strategies to fair ones by running them up to a certain
number of scheduling steps and then switching to use RW." The intellectual root is
Musuvathi & Qadeer, "Fair Stateless Model Checking" (PLDI 2008): explore only fair
schedules so that liveness checking on a stateless (non-state-caching) explorer does not
drown in unfair counterexamples.

[ANALYSIS] Unpacking for our fairness-quantifier decision
(nondeterminism-doctrine open question: ∀-stream termination is false for spin-wait
programs): the lineage's operational fairness is NOT strong fairness as a temporal-logic
side condition; it is (a) in the testing lane, a scheduler whose fairness is
probabilistic — under uniform random choice every persistently enabled worker is
scheduled infinitely often with probability 1; plus (b) a finite-prefix surrogate for
"infinitely often stuck hot": temperature exceeding a large threshold within a 10N-step
fair run. Their false-positive discipline is the key design point: an unfair schedule
exhibiting starvation is DEFINED AWAY as not a bug. For us this maps to a two-tier
decision: (i) headline liveness/termination theorems get an explicit
fairness-constrained quantifier — ∀ streams satisfying a `FairStream` predicate (a
natural candidate: every goroutine enabled cofinally often is scheduled cofinally often;
or the bounded version — no enabled goroutine is starved for more than B consecutive
consumption sites, which is closer to Coyote's operational "does not contiguously starve
... for a long time" and is prefix-checkable); (ii) the testing lane runs RW streams
(probabilistically fair, no side condition needed on finite prefixes) with a
temperature-style monitor as the finite surrogate. The bounded-starvation form has a
major advantage for us: it is decidable on finite prefixes, hence usable both as a
harness filter on generated streams and as a hypothesis in kernel-checked theorems,
whereas cofinal fairness only constrains infinite streams. Coyote's "unfair prefix then
switch to RW" trick also transfers directly as a stream-generator combinator: PCT-shaped
prefix (drive into a rare region) concatenated with a fair RW tail (give liveness a fair
chance) — that is literally concatenation of stream generators in our design.

---

## 4. Reproduction and determinism

### 4.1 Trace format and replay

[FACT] Coyote's found-bug artifact is "a reproducible bug trace that provides the global
order of all scheduling decisions and nondeterministic choices made during the execution
of a test", dumped as a JSON trace file; `coyote replay` re-executes it
deterministically, `--break` attaches a debugger at the bug point, and the trace is also
exposed programmatically (`TestingEngine.ReproducableTrace`,
`Configuration.WithReplayStrategy`). (https://github.com/microsoft/coyote,
https://microsoft.github.io/coyote/get-started/using-coyote/,
https://github.com/microsoft/coyote/issues/23)

### 4.2 The determinism contract on the program under test

[FACT] (TACAS 2023, verbatim modulo ligatures) "Coyote requires a test to be
deterministic modulo scheduling between workers. This implies that, for instance, the
program should not take a branch based on the current system time, or read data from an
external service or a file that may change outside the scope of the test. Coyote also
requires that tests be idempotent, that is, running the test twice has the same effect
as running it once" (because iterations reuse the hosting process). Violating these
"can imply that replay will fail. These are minor requirements, with users seldom
complaining about them."

### 4.3 Nondeterminism outside the scheduler; partial control fails half-open

[FACT] (TACAS 2023) Data nondeterminism is unified into the same strategy machinery:
"Exploration strategies also offer a means to generate unconstrained boolean or integer
values. Coyote exposes these APIs to developers", used to model timeouts firing, failure
injection, and mocked-environment responses; all such choices are recorded in the same
trace (hence replayed). The docs frame timer delivery and failure injection explicitly
as controlled nondeterminism. (https://microsoft.github.io/coyote/concepts/non-determinism/)

[FACT] (TACAS 2023) "A more significant requirement is that Coyote be able to control
all the concurrency created by a test. This may not happen when the program uses an
unsupported programming model, or a library that cannot be rewritten because, say, it
includes native code ... Coyote has partial defenses against this: when it detects
concurrent activity outside its control, it tries to tolerate it by letting it finish on
its own, else throws an error to make the user aware." The CLI also offers `--no-repro`
to keep testing when repro is impossible.

[ANALYSIS] Two transplant lessons. (1) Their single-trace design — scheduling AND data
choices in one recorded global order — is exactly our single `Choices` stream; the
lineage validates that unification (one artifact, one replayer, one determinism
contract). (2) Their weakest point is precisely where we are categorically stronger:
"deterministic modulo scheduling" is an unenforced CONTRACT on the program plus an
instrumentation-coverage assumption, with a tolerate-then-error fallback that is
fail-half-open (tolerated uncontrolled concurrency silently shrinks the explored space
and quietly breaks PCT's guarantee — the paper admits "the loss of control implies that
the ability to explore specific interleavings, such as what PCT requires, is reduced").
In our machine, determinism-given-a-stream is a THEOREM about the interpreter (the
differential trust root), not a contract; unsupported constructs are `.unsupported` at
the boundary by doctrine; and replay is kernel-reducible evaluation, not re-execution
under an interception layer. Their idempotence requirement (process reuse across
iterations) has no analogue for us — each run is a pure function application.

---

## 5. The P language line: design-level model checking for distributed systems

[FACT] P (PLDI 2013, Desai, Gupta, Jackson, Qadeer, Rajamani, Zufferey: "P: Safe
Asynchronous Event-Driven Programming") specifies a system as dynamically-created state
machines communicating by events; the same program compiles to executable C AND to a
model for the Zing explicit-state model checker, which "systematically enumerat[es] all
implicit scheduling and explicit modeling choices", bounded (depth bounds etc.);
environment is closed with "ghost machines". P shipped inside the Windows 8 USB 3.0
driver stack. (https://dl.acm.org/doi/10.1145/2491956.2462184,
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/pldi212_desai.pdf,
https://github.com/zingmodelchecker/zing)

[FACT] ModP (OOPSLA 2018, Desai, Phanishayee, Qadeer, Seshia: "Compositional Programming
and Testing of Dynamic Distributed Systems") added a module system based on compositional
trace refinement for dynamic machine creation and changing communication topology,
enabling assume-guarantee DECOMPOSITION of the testing problem itself (test each module
against abstractions of the rest), demonstrated on a transaction-commit service and a
replicated hash table. (https://dl.acm.org/doi/10.1145/3276529)

[FACT] Current P at AWS (p-org.github.io/P): the P Checker explores interleavings of
concurrently executing state machines plus data nondeterminism (`choose`), checking
safety/liveness specification monitors — same controlled-exploration paradigm as
P#/Coyote, applied to the DESIGN model rather than production code. Backends have grown:
PSym (PLDI/PACMPL 2023, "PSym: Efficient Symbolic Exploration of Distributed Systems",
value-summary-based symbolic exploration; https://dl.acm.org/doi/10.1145/3591247), a
UCLID5/SMT verification backend for ∀-execution proofs
(https://p-org.github.io/P/advanced/PVerifierLanguageExtensions/announcement/), and
PObserve (2023), which validates STRUCTURED PRODUCTION LOGS post-hoc against the P
specification. Adoption: S3 (the strong read-after-write consistency migration used P to
eliminate design bugs and de-risk optimizations), DynamoDB, EBS, Aurora, EC2, IoT;
80+ service teams. (Brooker & Desai, "Systems Correctness Practices at AWS", ACM
Queue/CACM 2025, https://dl.acm.org/doi/10.1145/3729175; https://ankushdesai.github.io/)

[ANALYSIS] The P line's relevance to our raft target is mostly about WHAT is tested. The
P#/FAST-2016 branch tested real code against mocked environments (our lane: real Go
through our interpreter — strictly stronger, no model-code gap). The P-at-AWS branch
concedes the model-code gap and buys, in exchange: (a) tiny state spaces (design-level
events, not code-level steps) enabling near-exhaustive coverage; (b) specification
monitors (global observers over the event stream) as the property language — directly
transplantable as our observable layer over the trace of communication choice-points;
(c) PObserve's move — checking real executions against the spec's trace language — which
for us is subsumed by the differential lane but suggests a raft-shaped lane: check
interpreter traces of `deps/raft` cases against protocol-level monitors (election
safety, log matching), not just against `go run` output equality. ModP's
assume-guarantee testing decomposition is the one genuinely new idea here for later:
testing a raft node against an abstraction of its peers rather than a full cluster is a
state-space reduction our enumerator will eventually want; it needs a refinement
relation between module abstractions — a natural fit for our membership lane, but far
future.

---

## 6. Related industrial lines (contrast, one paragraph each)

[FACT unless noted] Antithesis: a deterministic HYPERVISOR ("the Determinator", built on
FreeBSD/bhyve) that makes an entire VM — any OS, any binary — deterministic: same
inputs, identical execution; entropy is injected as a controlled input. On top:
coverage-guided exploration, fault injection, and snapshot-and-branch at interesting
states. Guarantee claimed: perfect reproducibility of any found bug (plus
faster-than-real-time exploration); explicitly NOT completeness — determinism makes
bugs replayable, the fuzzing side finds them. Founded by FoundationDB alumni to remove
FDB's "rewrite your system under discipline" precondition.
(https://antithesis.com/blog/deterministic_hypervisor/,
https://antithesis.com/docs/resources/deterministic_simulation_testing/,
https://freebsdfoundation.org/antithesis-pioneering-deterministic-hypervisors-with-freebsd-and-bhyve/)

FoundationDB: the original disciplined deterministic-simulation story — the whole
database is written in Flow (single-threaded actor C++) with ALL I/O (network, disk,
time) behind interfaces, so an entire cluster plus fault workloads runs in one process
from a seed; test oracles are workload invariants; any failing seed replays exactly.
Cost of the discipline: third-party components (e.g. RocksDB) break determinism; the
approach is unavailable to existing codebases — exactly the gap Antithesis and
Coyote-style interception each attack from opposite ends.
(https://apple.github.io/foundationdb/testing.html,
https://www.foundationdb.org/files/fdb-paper.pdf)

Jepsen: black-box testing of REAL distributed systems: drive concurrent client
workloads against a real cluster while a "nemesis" injects faults (partitions, clock
skew, crashes), then check the recorded operation HISTORY against consistency models
(linearizability via Knossos, transactional anomalies via Elle). Controls nothing inside
the system; explores by randomized fault timing; claims only "we found/did not find
violations in the histories we observed" — no reproducibility, no coverage guarantee,
but zero modeling gap. (https://jepsen.io, https://jepsen.io/analyses/tigerbeetle-0.16.11)

TigerBeetle VOPR: FDB-style discipline in Zig — the Viewstamped Operation Replicator
runs whole clusters (replicas + clients + VSR consensus) in one process with simulated
network, storage (up to 8–9% corruption probabilities on read/write paths), and clocks;
deterministic given (seed, commit hash); a state checker hash-chains replica transitions
and verifies convergence, distinguishing correctness from liveness failures; time
compression ~1 month of cluster time per hour, 10 simulators running 24/7. Jepsen's 2025
analysis of TigerBeetle largely validated the approach.
(https://github.com/tigerbeetle/tigerbeetle/blob/main/docs/internals/vopr.md,
https://docs.tigerbeetle.com/concepts/safety/)

madsim / turmoil (Rust): library-level deterministic async runtimes. madsim
(https://github.com/madsim-rs/madsim) is a drop-in replacement for tokio that intercepts
the runtime layer — scheduler, time, network, randomness are all seed-driven, so a
distributed system written against tokio APIs runs deterministically in one process
(used by RisingWave for DST). turmoil (https://github.com/tokio-rs/turmoil) is
narrower: it simulates the NETWORK (hosts, latency, partitions) atop tokio's
current-thread runtime for reproducible network-failure testing. [ANALYSIS] Both are the
"own the runtime" strategy at library granularity — the closest architectural cousins to
our position (the runtime IS the semantics), minus the semantic rigor: their determinism
is an implementation property, not a stated theorem, and their exploration layer is
plain seed sampling with none of the PCT/portfolio machinery.

[ANALYSIS] Placement of our machine in this space: everyone pays for determinism
somewhere — discipline (FDB/TigerBeetle), interception (Coyote/madsim), or a hypervisor
(Antithesis) — and everyone then samples seeds/schedules over it. We pay in
subset-coverage of Go (the frontend gap) and get the strongest form of the artifact:
determinism-given-stream as a theorem, replay as kernel-reducible evaluation, and the
same semantics object serving testing AND proof. No line in this survey has the proof
half; that is our differentiation, and it is why the fail-closed boundary (their
weakest point, §4.3) matters more for us than for any of them.

---

## 7. Transfer analysis: what transplants onto the choice-stream machine

Our machine: schedule = choice-stream prefix; interpreter total & deterministic given
the stream; enumerator with fail-closed certification; membership lane for
envelope-width; kernel-reducible replay. All [ANALYSIS] below unless cited.

### 7.1 Transfers cleanly (free or near-free)

- **Trace replay = our stream, free.** Coyote's trace file, replayer, `--break`
  debugging, and determinism contract (§4) collapse for us into "re-run the interpreter
  on the recorded prefix" — and unlike theirs, our replay is checkable by the Lean
  kernel and cannot be broken by the program (no contract to violate). The one thing
  worth copying is UX: persist (seed/stream prefix, case id, commit) as the failure
  artifact in the harness TSVs, the way every line in this survey keys repro on
  (seed, version).
- **Portfolio exploration.** Pure harness policy: a set of stream GENERATORS (RW with
  seeds, PCT-shaped, DB-shaped, adversarial fixed streams) round-robined across
  iterations, exactly Coyote's across-iteration mode; their in-iteration mode is stream
  concatenation of generator outputs. Empirically mandated by their own results ("none
  is a clear winner", §2.4). Zero semantic surface touched.
- **The fairness architecture (§3).** Fair-stream predicate for theorem statements
  (bounded-starvation form preferred: prefix-decidable, matches Coyote's operational
  notion), RW streams + temperature-style monitor for the testing lane, and the
  "unfair prefix ++ fair tail" generator combinator. The false-positive discipline
  (starvation under an unfair schedule is not a bug) becomes, for us, simply the shape
  of the quantifier.
- **Small-scope budget calibration.** d ≤ 3, 10^3–10^5 iterations, runs of 10^2–10^3
  scheduling decisions, small cluster instantiations (§2.4) — directly sets defaults
  for the concurrency differential lane.
- **CHESS's DRF pairing (§1.3).** Coarse communication-point scheduling + `go run
  -race` oracle + fail-closed racy-program classification: already doctrine, now with
  the lineage's soundness argument attached (DRF reduction) — worth citing in the
  eventual concurrency design note as the justification, not just a preference.

### 7.2 Transfers with real design work

- **PCT as a stream-generation strategy.** The subtlety: PCT is an ONLINE scheduler —
  its choice at each point depends on the enabled set and its own priority state, so a
  PCT "schedule" cannot be sampled as a stream up-front. But it does not need to be:
  run the generator IN THE LOOP (interpreter steps to a consumption site, exposes the
  enabled set, the PCT state picks the index, priorities update), and RECORD the
  consumed choices. The recorded prefix is a plain stream — certification, replay, and
  the membership lane are untouched, because the strategy lives in the harness while
  the semantics only ever sees a stream. So yes, our stream encoding expresses it, with
  one requirement on the harness interface: the enumerator must expose (enabled set,
  step count) at each consumption site to the generator — Coyote's exact strategy
  interface (§1.2). The d-guarantee transfers with reinterpreted parameters: n = number
  of goroutines (better: chains — for Go, goroutines ARE natural chains, which is the
  PCTt lesson landing in our favor; if we later schedule finer-grained events, PCTCP's
  chain partitioning is the reference), k = number of choice-consumption sites in the
  run, d = ordering constraints over COMMUNICATION events. The guarantee is honest only
  relative to that alphabet: bugs needing interleaving at non-communication points are
  outside it — which is exactly the DRF envelope we already claim, so the coarsened
  guarantee and the semantic envelope coincide. That coincidence should be stated in
  the design note; it is the theorem-shaped version of Coyote's informal position.
- **Liveness monitors / temperature.** Needs a spec-surface feature: hot/cold observer
  automata over the trace (or at minimum a starvation observable), plus the harness
  threshold logic. P's monitors and PObserve (§5) argue for making trace-observers a
  first-class spec construct anyway — the same machinery serves liveness testing now
  and raft protocol properties later.
- **Stateful niceties (lasso detection, QL, POS).** Coyote's QL needs a state
  fingerprint; POS needs racing-pair information; lasso detection needs state caching.
  All three are EASIER for us in principle — our machine state is a first-class value
  (hashable, comparable), where Coyote has to fingerprint a live .NET heap. Deferred,
  not blocked: none is needed for the first concurrency lanes.

### 7.3 Does not transfer (and why that is good news)

- **Binary/IL rewriting, the interception layer, task-API modeling** (§1.2): our
  interpreter IS the instrumentation. The entire 24K-line engineering core of Coyote —
  and its maintenance treadmill tracking .NET API evolution — has no analogue. The
  residual analogue is the frontend coverage gap, which is visible and fail-closed by
  construction.
- **Uncontrolled-concurrency "partial defenses" / `--no-repro`** (§4.3): the
  fail-half-open compromise exists because they don't own the runtime. We must NOT
  import any analogue — an unsupported concurrent construct is `.unsupported`, never
  "tolerated". This is the one place the lineage's pragmatism would be a regression
  for us.
- **The determinism-modulo-scheduling contract on the program** (§4.2): theirs is a
  social contract; ours is the interpreter's definition. Nothing to build; something to
  keep (the totality/purity discipline in CLAUDE.md is what makes this stay true).
- **CHESS-style inline race detection as extra scheduling points**: wrong layer for us.
  Races are outside our defined envelope (undefined behavior in Go's model), handled by
  the external `-race` oracle and fail-closed classification, not by widening the
  interleaving alphabet to memory accesses.
- **P's design-model checking as a substitute lane**: we test the real code; P's value
  for us is its SPEC machinery (monitors, observers, assume-guarantee decomposition),
  not its model-level checking.

---

## Sources (primary)

- Burckhardt, Kothari, Musuvathi, Nagarakatte. A Randomized Scheduler with Probabilistic
  Guarantees of Finding Bugs. ASPLOS 2010.
  https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/asplos277-pct.pdf
- Deligiannis, Senthilnathan, Nayyar, Lovett, Lal. Industrial-Strength Controlled
  Concurrency Testing for C# Programs with Coyote. TACAS 2023.
  https://www.microsoft.com/en-us/research/wp-content/uploads/2023/04/978-3-031-30820-8_26.pdf
- Deligiannis, Donaldson, Ketema, Lal, Thomson. Asynchronous Programming, Analysis and
  Testing with State Machines (P#). PLDI 2015. https://dl.acm.org/doi/10.1145/2737924.2737996
- Deligiannis et al. Uncovering Bugs in Distributed Storage Systems during Testing (Not
  in Production!). FAST 2016.
  https://www.usenix.org/conference/fast16/technical-sessions/presentation/deligiannis
- Musuvathi, Qadeer, Ball, Basler, Nainar, Neamtiu. Finding and Reproducing Heisenbugs
  in Concurrent Programs (CHESS). OSDI 2008.
  https://www.usenix.org/legacy/event/osdi08/tech/full_papers/musuvathi/musuvathi.pdf
- Musuvathi, Qadeer. Fair Stateless Model Checking. PLDI 2008.
- Emmi, Qadeer, Rakamaric. Delay-Bounded Scheduling. POPL 2011.
  https://soarlab.org/papers/2011_popl_eqr.pdf
- Ozkan, Majumdar, Niksic, Mousavi Befrouei, Weissenbacher. Randomized Testing of
  Distributed Systems with Probabilistic Guarantees (PCTCP). OOPSLA 2018.
  https://dl.acm.org/doi/10.1145/3276530
- Thomson, Donaldson, Betts. Concurrency Testing Using Controlled Schedulers: An
  Empirical Study (SCTBench). ACM TOPC 2016. https://dl.acm.org/doi/10.1145/2858651
- Coyote docs: liveness (https://microsoft.github.io/coyote/how-to/liveness-checking/),
  replay (https://microsoft.github.io/coyote/get-started/using-coyote/),
  nondeterminism (https://microsoft.github.io/coyote/concepts/non-determinism/),
  repo (https://github.com/microsoft/coyote)
- Desai, Gupta, Jackson, Qadeer, Rajamani, Zufferey. P: Safe Asynchronous Event-Driven
  Programming. PLDI 2013. https://dl.acm.org/doi/10.1145/2491956.2462184
- Desai, Phanishayee, Qadeer, Seshia. Compositional Programming and Testing of Dynamic
  Distributed Systems (ModP). OOPSLA 2018. https://dl.acm.org/doi/10.1145/3276529
- PSym: Efficient Symbolic Exploration of Distributed Systems. PACMPL (PLDI) 2023.
  https://dl.acm.org/doi/10.1145/3591247
- Desai et al. Lasso Detection using Partial-State Caching. FMCAD 2017.
  https://ankushdesai.github.io/assets/papers/liveness.pdf
- Brooker, Desai. Systems Correctness Practices at AWS. ACM Queue/CACM 2025.
  https://dl.acm.org/doi/10.1145/3729175
- P language site: https://p-org.github.io/P/
- Antithesis: https://antithesis.com/blog/deterministic_hypervisor/,
  https://antithesis.com/docs/resources/deterministic_simulation_testing/
- FoundationDB testing: https://apple.github.io/foundationdb/testing.html;
  FDB paper: https://www.foundationdb.org/files/fdb-paper.pdf
- Jepsen: https://jepsen.io; TigerBeetle analysis:
  https://jepsen.io/analyses/tigerbeetle-0.16.11
- TigerBeetle VOPR:
  https://github.com/tigerbeetle/tigerbeetle/blob/main/docs/internals/vopr.md
- madsim: https://github.com/madsim-rs/madsim; turmoil:
  https://github.com/tokio-rs/turmoil

Provenance note: quotes from the PCT ASPLOS 2010 and Coyote TACAS 2023 papers were
extracted from the published PDFs via text extraction (ligatures/spacing normalized);
tagged verbatim above only where the extraction was unambiguous. Coyote docs quotes are
from the live documentation site as of 2026-08-06. The 7.6x P#-vs-CHESS figure and the
"5N steps" liveness default are reconstructed from secondary summaries of the PLDI 2015
paper and Coyote docs respectively (not re-verified against the primary PDF text).
