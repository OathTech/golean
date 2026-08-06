# Channels/goroutines arc — design of record (2026-08-06)

Status: DECIDED (user sign-off 2026-08-06) — resolves the options paper
`docs/2026-08-06_concurrency-arc-options.md` (D1–D9); the six research
notes `docs/2026-08-06_concurrency-research-*.md` are the evidence
base. THE DECIDING PRINCIPLE, set by the user: every contested choice
is resolved for *what supports growing toward a fully faithful Go
semantics while preserving differential testing* — grow by EXTENSION
(new registry entries, new edge sources, additive quantifiers), never
by REVISION (step-granularity changes, theorem restatement). This
principle is itself binding on future arcs touching this machinery.

## Decisions

**D1 — Machine shape: ThreadPool over the unchanged sequential
machine.** `MultiConfig {threads : Array Config, shared : ExecState}`;
per-thread `Config` and `ExecState` unchanged. The Prop relation stays
per-thread with a spawn component; iris-lean's thread-pool `Language`
supplies interleaving (already instantiated sequentially in
`proofs/GoLeanProofs/Lang.lean`). Threads carry stable goroutine IDs
(pool position is not identity). Rejected: coarse-only ground truth
(unsound without the reduction theorem it would presuppose);
logic-only pool (fails executability — the foundational requirement).

**D2+D3 — THE SYNCHRONIZATION-OP REGISTRY (one mechanism, two duties).**
The scheduling-point set and the happens-before edge-source set are the
same set: synchronization operations. The registry initially contains:
channel send/recv/close, select, `go` spawn, goroutine exit. Each entry
is simultaneously
  (a) a SCHEDULING POINT — the scheduler `Choices` site (pick ∈
      [0,|runnable|)) is consumed ONLY at registry ops and ONLY when
      |runnable| > 1 (critical: `Choices.consume` pops even at bound 1,
      so unconditional consumption would desynchronize every existing
      adversarial-stream run; sequential conservation depends on this);
  (b) an HB EDGE SOURCE — segment-level happens-before race detection:
      execution between registry ops is a SEGMENT; the machine records
      per-segment read/write sets at `Loc`-path granularity through the
      existing `loadLoc`/`storeLoc` chokepoint; vector clocks over
      goroutines advance on registry-op HB edges (per the memory
      model's channel rules); a conflict between HB-unordered segments
      ⇒ terminal `raceDetected` — races FAIL CLOSED per run, on every
      run, deterministically given the stream.
Growth contract: a future sync primitive (atomics, Mutex, Once,
WaitGroup) is added by REGISTERING it — one scheduling point + one HB
edge rule — with no change to the scheme, the sequential machine, or
existing statements. The detector's HB skeleton is TSan's, keeping the
in-machine classification structurally aligned with the `go run -race`
external oracle as both grow.
Soundness obligation (recorded, owed in slice 3): the NPDRF-style
reduction — DRF programs behave identically under registry-point
scheduling and full interleaving (ICTAC 2018; Lipton movers; CHESS
architecture) — with the self-enforcing coupling that programs outside
DRF are exactly those the machine refuses. Per-construct mover lemmas
for coarse steps (appendSlice-class) are the granularity ledger's
formal successor. Rejected: naMode two-step accesses (grows by
revision: changes sequential step granularity/fuel today, changes
decomposition per future access class; detection by exploration luck
weakens the differential lane).

**D4 — Envelopes** (the doctrine's statements, shipped with their
sites): L1 interleaving — envelope = all schedules over runnable
threads (spec has zero scheduling text; pure omission latitude); L2
select — "any entry-ready case" (spec's "uniform pseudo-random"
deliberately weakened per the possibilistic doctrine; NO
re-randomization on the blocked path — probe-pinned; wake-order
latitude is L1/L4); L4 waiter pairing — "any matching waiter" (no spec
text; gc's FIFO wakeup is a membership point, and real FIFO would
force queue state into channels — rejected). Buffer FIFO is SPEC
("Channels act as first-in-first-out queues") — deterministic, strict
lane. Channel panics (send-on-closed, close-of-closed/nil, make
negative) are real recoverable Go panics — diverging from Goose's UB;
more faithful and differentially testable.

**D5 — Fairness: the additive-quantifier path.** Now: ∀-stream
`Terminates` for the blocking-discipline class — the strongest claim,
assumption-free, true because the scheduler picks among RUNNABLE
goroutines and starvation requires a runnable spinner (not expressible
race-free without atomics; to be made precise in slice 2's note).
Later (atomics arc): `FairStream` — prefix-decidable bounded-starvation
predicate, Simuliris-style first-order trace fairness, TCB-clean —
added as an ADDITIVE weaker quantifier for the larger class; existing
theorems never restated. Any `Fair` assumption is ABOVE-SPEC (Go
promises no fairness) and must carry a statement caveat. Fallback
recorded: Perennial claims no termination at all.

**D6 — Main-exit**: modeled faithfully — main's return terminates the
program (goroutines killed); partial goroutine leaks are observably
nothing in Go (exit 0) — model-side classification only, spec-side
join discipline. Deadlock ("all goroutines are asleep") is a terminal
fatal classification matching Go's runtime, differentially testable
(go exits 2); the -race and deadlock-detector oracle modes are
mutually exclusive (probed) — the harness must never combine them.

**D7 — Channels**: primitive heap-cell `chanData` (the `mapData`
precedent — locSup/StateWf/gen_heap reuse verbatim). Blocked
goroutines are blocked-Config shapes; NO waiter queues in channel
state; rendezvous = a pairing step (direct handoff, matching gc);
`cap=0 ⟺ unbuffered` is one rule. Select: entry-time operand
evaluation (order spec-pinned), one readiness step, L2 choice among
ready; default-with-none-ready deterministic, consumes nothing.

**D8 — Statement idiom**: carrier swap (`execStmt`→`execProg`).
`GoSpecC`: single-threaded `InitialSplit` pre; post over the JOINED
final state, `.mainNormal`-pinned; ∀ one stream (schedules + latitude
unified — the single-stream design independently validated by Coyote's
recorded-global-order architecture). `ProgressExecC` excludes
`deadlocked` and `raceDetected`: a proven spec implies deadlock- and
race-freedom on every modeled schedule. Channel facts exported as
operational history predicates; Iris strictly internal (iris-lean
ready: concurrent WP/fork/invariants/adequacy at the pinned rev; no
prophecies needed — primitive channels make lifting laws the atomic
specs). `MultiConfig`/scheduler/`chanData` enter the statement TCB with
readability-as-specification review; GoSpecC/ProgressExecC join the
designated set with first-order readouts; Comparator landmark at the
first designated-statement change.

**D9 — Validation: the six-lane taxonomy** (validation note §4):
(a) sequential-degenerate — existing 1027 cases bit-identical, by
construction of D2(a); the conservation theorem
`execProg_single_eq_execStmt` is the transfer lemma keeping all 33
designated sequential statements valid unrestated.
(b) CONFLUENT — the membership singleton-failure rule inverts into a
pass precondition: enumerator certifies |set|=1 over all schedules,
then strict go-run equality — full-strength differential verification
for deterministic concurrent programs.
(c) schedule-dependent — membership lane; enumerator = interleaving
explorer at registry granularity (tractable at litmus scale, the right
scale: enumeration validates the MODEL, not targets); DPOR pruning and
PCT stream-sampling are later additive layers (recorded).
(d) racy-negative — every enumerated path refuses; `-race` red
justifies (TSan: no false positives); `-race`-green + our refusal =
three-way investigation.
(e) litmus pairs — channel-synchronized form admits exactly SC
outcomes / racy form refuses: the DRF-SC boundary pinned executably.
(f) deadlock/leak — deadlock differential; leak self-consistency.
Doctrine updates: `-race` becomes a default membership sample source
(probes: plain go-run is a point-mass — 0/700 on a depth-1 corner;
-race 6/6 orderings); per-lane epistemic captions ship with the lanes.

**Prior art posture**: Perennial's in-tree etcd-raft verification
(driving their 2025-26 channel rewrite) is a standing comparison point;
their spec-sentence-keyed channel tests are imported as fresh canonical
corpus inputs with provenance. Their differential apparatus is deleted
upstream — executable validation is this project's differentiator.

## Slice plan

1. **Channels-only, zero scheduler** — `chanData` + make/send/recv/
   close/len/cap/range/select-with-default as machine steps; blocking =
   immediate deadlock terminal; flips all 38 `channels/` cases (all
   single-goroutine — machine-shape §6) into the strict lane. Fail
   closed: `go`, sync.*, multi-ready select, `go` in `$pkginit`.
2. **Goroutines + ThreadPool** — spawn/exit, scheduler site, deadlock
   terminal, main-exit, sequential-conservation theorem, GoSpecC/
   ProgressExecC + a fork/join headline witness. Comparator landmark.
3. **The registry's second duty** — segment-HB race detection,
   racy-negative lane, litmus pairs, the NPDRF reduction obligation +
   mover lemmas.
4. **Select multi-ready + wake-order membership + confluent lane** —
   enumerator over schedules, envelope statements live.
5. **Iris proof layer** — concurrent WP over the relation, channel
   invariants/ghost, the GoSpecC witness proved.
6. **Doctrine/harness updates** — -race sampling, lane captions,
   envelope-width review.
Owed early probes (slice 2/3 entry): iris-lean ghost ergonomics under
real protocols; waiter-wake observability at scale; mover-lemma
difficulty on appendSlice; nil-mixed select corners.
