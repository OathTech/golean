# Channels/goroutines arc — synthesis and OPTIONS PAPER (2026-08-06)

Status: OPTIONS FOR USER DECISION — nothing here is decided. This arc's
three hard problems were named by the user directly: (1) the semantic
design must be accurate, (2) testing is trickier (no simple differential
oracle for interleavings), (3) the reasoning itself requires subtle
choices. Six primary-source research notes feed this synthesis (all
committed alongside, `docs/2026-08-06_concurrency-research-*.md`):
goose-perennial (the 2025-26 channel rewrite + in-tree raft effort),
go-ground-truth (spec/memory-model/runtime, 26 probes, the latitude
table), machine-shape (the design-space map over our CEK machine),
validation (lane taxonomy + enumeration tractability + 2800-run
sampling calibration), coyote-line (controlled-scheduling engineering +
PCT + fairness mechanisms), iris-ecosystem (spec idioms, Simuliris
fairness, iris-lean gap analysis). Binding context:
`docs/2026-08-04_nondeterminism-doctrine.md` (DRF-SC fail-closed, -race
second oracle, litmus corpus, fairness-quantifier decision owed),
`docs/2026-08-03_sem-adequacy-arc.md` (fork/join stated in
interpreter-level pre/post terms; Iris internal-only).

## The convergent picture (where all six notes agree)

- **Machine shape**: a ThreadPool over the UNCHANGED sequential
  machine — `MultiConfig {threads : Array Config, shared : ExecState}`;
  the scheduler is a third `Choices` site picking among RUNNABLE
  threads, consumed ONLY when |runnable| > 1 and only at
  COMMUNICATION points (channel ops, select, spawn, goroutine exit).
  This matches GooseLang's architecture, iris-lean's thread-pool
  `Language` interface (which our proofs layer already instantiates
  sequentially), and makes SEQUENTIAL CONSERVATION essentially
  definitional: one runnable thread ⇒ no consumption ⇒
  `execProg_single_eq_execStmt`, keeping all 33 designated sequential
  statements valid unrestated and the 1027-case corpus bit-identical.
- **Channels are machine primitives** (heap-cell `chanData` on the
  `mapData` precedent), NOT a Goose-style library-over-mutex — their
  spin-loop offer machine exists to serve a proof style and would
  destroy deterministic executability, kernel reduction, and the
  strict lane. Blocked goroutines are blocked-Config shapes (no waiter
  queues inside channel state); rendezvous is a pairing step.
  Send-on-closed etc. are REAL recoverable Go panics (diverging from
  Goose's UB — more faithful, differentially testable).
- **The latitude surface is exactly three new envelope points**
  (ground-truth §6): L1 goroutine interleaving (spec has ZERO
  scheduling/fairness text — pure omission latitude), L2 select choice
  among entry-ready cases (spec's "uniform pseudo-random" deliberately
  weakened to possibilistic "any ready"; probes show NO re-randomization
  on the blocked path — wake-order latitude is L1/L4, not L2), L4
  waiter pairing (no spec text; gc's FIFO wakeup = a membership point,
  "any matching waiter" is the envelope). Buffer FIFO is SPEC, not
  latitude. Deadlock ("all goroutines are asleep") is a terminal fatal
  classification; main-return kills goroutines; partial leaks are
  observably nothing in Go (model-only territory).
- **Races fail closed under DRF-SC**, per the doctrine and the memory
  model's own text (racy multiword programs: "arbitrary memory
  corruption" — no envelope below the DRF line is statable). The
  coarse-scheduling soundness argument has a precise citable form
  (ICTAC 2018 NPDRF + Lipton/CHESS): DRF programs behave identically
  under communication-point scheduling — and the coupling is
  self-enforcing since programs where the reduction fails are exactly
  the ones we refuse. This also makes BUG-002's atomicity class
  enumerator-detectable for the first time.
- **Validation is a six-lane taxonomy** (validation §4): (a)
  sequential-degenerate (existing corpus, bit-identical); (b)
  CONFLUENT — the membership lane's singleton-failure rule INVERTS
  into a pass precondition: enumerator certifies |observation set|=1
  across all schedules, then strict go-run equality — full-strength
  differential verification recovered for deterministic concurrent
  programs; (c) schedule-dependent → membership with interleaving
  enumeration (tractable at litmus scale — 2 goroutines×depth 17, 3×11,
  4×8 within existing work caps — and litmus scale is the RIGHT scale:
  enumeration validates the model, not targets); (d) racy-negative
  (every enumerated path refuses; -race red justifies; TSan has no
  false positives); (e) litmus pairs (channel-synchronized form admits
  exactly SC outcomes / racy form refuses — the DRF-SC boundary, pinned
  executably); (f) deadlock (differentially testable: go exits 2) /
  leak (self-consistency only). Empirics: plain go-run sampling is a
  point-mass (0/700 runs exhibited a depth-1 corner), while `-race` is
  the best coarse-order diversifier (6/6 permutations) — candidate
  doctrine update: -race becomes a default membership sample source.
  The -race and deadlock-detector modes are mutually exclusive (probed)
  — harness must not combine them.
- **Statement idiom**: everything extends by carrier swap. Concurrent
  `GoSpecC`: single-threaded `InitialSplit` precondition, post over the
  JOINED final state with `.mainNormal` pinning, ∀ one stream
  (schedules + latitude unified — Coyote's single recorded global
  order independently validates the design); `ProgressExecC`
  additionally excludes `deadlocked` and `raceDetected`, so a proven
  spec implies deadlock- and race-freedom on every modeled schedule.
  Channel facts exported as operational history predicates. Iris stays
  internal: iris-lean at the pinned rev is READY (concurrent WP with
  fork, thread-pool semantics, invariants, ghost state, adequacy, zero
  sorries) — the arc's cost is GoCore-side, not logic porting. No
  prophecies needed (primitive channels make lifting laws the atomic
  specs; select resolves at its own consumption step).
- **Slice 1 is free of all hard questions** (machine-shape §6): ALL 38
  `channels/` corpus cases are single-goroutine and deterministic — a
  channels-only, zero-scheduler slice (chanData + make/send/recv/close/
  len/cap/range/select-with-default as steps; blocking = immediate
  deadlock terminal) flips all 38 into strict-lane coverage before any
  scheduler, fairness, or race machinery exists.

## Decisions for the user (D1–D9)

D1 **Machine shape ratification**: ThreadPool (option A) as above.
   Alternatives (coarse-only ground truth; logic-only pool) and their
   rejections: machine-shape §1. RECOMMENDED: A.
D2 **Scheduling granularity**: consume scheduler picks only at
   communication points, justified by NPDRF + the fail-closed race
   check (the pairing CHESS had and Coyote dropped — we keep it).
   Per-step scheduling is unenumerable in principle. RECOMMENDED as
   stated; the reduction argument becomes a recorded proof obligation
   (the granularity ledger's formal successor).
D3 **Race detection mechanism**: (i) segment-level happens-before
   detection (per-communication-segment read/write sets at Loc-path
   granularity + HB via channel edges; conflict ⇒ `raceDetected`
   terminal) — per-RUN fail-closed, no granularity change to the
   sequential machine, NPDRF-compatible; vs (ii) Goose's naMode
   two-step accesses — simpler but changes sequential step granularity
   (fuel/conservation churn) and detects only physically-overlapping
   schedules. RECOMMENDED: (i), with (ii)'s stuck-on-overlap as a
   cross-check idea for the enumerator lane. Full analysis:
   machine-shape §4, validation §2, goose-perennial §7.
D4 **Wake-order and select envelopes**: L4 = "any matching waiter"
   (gc FIFO as membership point); L2 = "any entry-ready case",
   uniformity dropped (possibilistic doctrine); select does NOT
   re-randomize on the blocked path (probe-pinned). RECOMMENDED as
   stated — these are the envelope statements the doctrine requires.
D5 **Fairness quantifier**: option (iii) — ∀-stream `Terminates` for
   the blocking-discipline class, TRUE without any fairness assumption
   (the scheduler picks among RUNNABLE goroutines; starvation requires
   a runnable spinner, which without atomics may be impossible in the
   race-free fragment — to be made precise in the design note). Defer
   `FairStream` (prefix-decidable bounded-starvation, Simuliris-style
   first-order trace fairness — TCB-clean when needed) to the atomics
   arc. The Go spec promises NO fairness: any Fair assumption is
   above-spec and must carry a statement caveat. Perennial's
   no-termination-claims stance is the recorded fallback.
D6 **Main-exit semantics**: model faithfully (main's return terminates
   the program, killing goroutines; join discipline is spec-side).
D7 **Slice plan**: 1 channels-only zero-scheduler (38 flips); 2
   goroutines + ThreadPool + scheduler site + deadlock terminal +
   sequential-conservation theorem; 3 race detection + racy-negative
   lane + litmus pairs; 4 select-multi-ready + wake-order membership +
   confluent lane + enumerator-over-schedules; 5 Iris proof layer
   (concurrent WP over the relation, a fork/join GoSpecC headline
   witness); 6 doctrine/harness updates (-race sample source,
   lane captions). Comparator landmark at the first statement-set
   change (GoSpecC entering the designated list).
D8 **Statement-TCB growth**: MultiConfig/scheduler/chanData enter the
   statement language (readable-as-specification review per the floats
   precedent); GoSpecC/ProgressExecC join the designated set with
   first-order readout corollaries.
D9 **Prior-art posture**: Perennial's in-tree raft verification (their
   2025-26 channel work is DRIVEN by etcd-io/raft — our north star) is
   tracked as a standing comparison point; their spec-sentence-keyed
   channel tests and examples are imported as canonical corpus inputs
   (fresh canonical Go, provenance recorded). Their deleted
   differential apparatus makes our executability the differentiator —
   recorded, not gloated.

## What reading alone could not settle (probe/build work owed early)

The machine-shape note §9 and validation note list: iris-lean ghost
ergonomics under real channel protocols; gc waiter-wake observability
probes at scale; the reduction lemma's difficulty on appendSlice-class
coarse steps; select-readiness corner probes (closed-send-ready is
pinned; nil-mixed selects need more). These are slice-2/3 entry tasks,
not blockers for D1–D9.
