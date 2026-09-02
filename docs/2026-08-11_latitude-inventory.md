# Latitude inventory — every point where Go permits multiple behaviors and the machine chooses (2026-08-11)

Status: companion to `docs/2026-08-11_essence-of-go-doctrine.md`
(ACCEPTED, user 2026-08-12). This is the doctrine's promised enumeration: every
point where the Go spec / memory model / library documentation permits
multiple behaviors and GoLean's machine resolves the choice — with the
classification, the evidence status, the re-envelope obligation and cost
for every pin, and the priority ranking. §8 is the doctrine register's
extension. Produced by a dual sweep (2026-08-11): the records
(nondeterminism doctrine 2026-08-04, BUGS.md, the channels/sync/floats/
init design notes) and the code (GoLean/GoCore/{Machine,StepFn,Multi,
Ops,Race,State,Value,Syntax,FloatBits}.lean). Where records and code
disagreed, the code was taken as truth and the record flagged (§9).

## 0. How to read

Classes (per the inventory charter):

- **(a) ENVELOPED** — the machine exercises the latitude via the
  `Choices` stream; the entry states the envelope and whether it is
  believed MAXIMAL against the plausible upper bound, or itself
  narrowed.
- **(b) PINNED** — the latitude is resolved to one deterministic point
  (usually gc's realization; twice OURS where gc's is compiler-internal
  and unpinnable — marked **known ≠ gc**). Each pin states the plausible
  envelope, the re-envelope obligation, and a cost estimate.
  Sub-class **(b-n) NARROWED**: a deliberate proper-subset resolution
  recorded with a transfer caveat (the doctrine's "singleton narrowing").
- **(c) FORCED** — the spec mandates the behavior; no latitude.
- **(d) UNKNOWN** — latitude suspected, not yet analyzed; the open
  question is stated instead of guessed at.
Citation norms (P2 retrofit, 2026-08-17): spec#/mem# anchor tokens
resolve against the PINNED documents and are lint-checked
(`scripts/check-spec-anchors`, fail closed). The JSCert-derived norm:
every latitude RULE-SITE carries the governing clause text verbatim
plus its anchor (E2's block at Machine.lean:3040–3072 is the model; cite re-anchored 2026-08-22 — launch audit D7 MEDIUM-7 found the exemplar itself pointing at .opDone/postOp code — and re-swept 2026-08-31) —
maintained while writing, not retrofitted. Anchor existence is NOT a
content-drift signal (`977e23a707` added normative mem#restrictions
text with no anchor/version-line change); content hashing at re-pin
is. And the CH2O contrast, recorded so nobody imports the wrong valve:
C formalizations can launder ambiguity and combinatorial pain into
undefined behavior — Go has no sequential UB, so our analog is the
REFUSED class, a tool-level visible red, never a semantic verdict.

- **(q) ENVELOPE-BY-QUOTIENT** (added 2026-08-13) — the machine keeps
  ONE deterministic realization as a canonical representative, and a
  THEOREM proves every conforming alternative observationally equal
  (the latitude is real but quotiented away by the modeled observation
  surface). Unlike (b), the re-envelope obligation is DISCHARGED — by
  proof, not by exercising the latitude — conditional on the recorded
  observation-surface scope; a new observation channel re-opens the
  entry. First (and model) case: C11's allocation addressing.
- **REFUSED** — not a latitude class: a spec-open point the machine
  resolves by failing closed (visible red, never an answer). Listed
  because refusals are how several latitude points are currently
  handled; each is a coverage debt, not a fidelity claim.

Evidence-class shorthand (doctrine §Evidence): SPEC (spec text), MM
(memory model doc), DOCS (runtime/library docs), GC (measured gc probe,
lower-bound instrument), XIMPL (cross-implementation — none exists yet;
noted where it would bear), ARCH (proposal/issue archaeology — none done
yet; noted where it would bear).

**The choice-site census IS code** (W3.2 slice 1 stage A): the
`ChoiceSite` datatype + `ChoiceSite.policy` table in
`GoLean/GoCore/State.lean` is the census of record — every consumption
goes through `Choices.consumeAt` with its site tag, so a new site
requires a constructor (exhaustiveness-checked) and this table below is
a reader's mirror, no longer a hand-synced record. The per-site
consume-when column is the `consumeAtOne` policy declaration (the
L1/L4 singleton non-consumption moved from caller-side special cases
into the table at stage A, behavior-identical):

**Mirror re-synced 2026-08-22** (settlement branch, `reconcile-records`
C12). The mirror had DRIFTED and nothing was watching it: it carried 7
rows against the datatype's 9 constructors — `postOp` (stage C) and
`backEdge` (stage D) were never added — and all seven surviving rows'
`file:line` citations were stale. The exhaustiveness check is real but
it protects the CODE, not this table, and the table is what a reader
consults; a census two sites short is a census of a different machine.
Every row's site is now re-verified against the `Choices.consumeAt`/
`consumeAtE` call sites at this tip. Note `l1Sched`/`postOp`/`backEdge`
share ONE consumption line (Multi.lean:1153) and are distinguished by
`Config.boundarySite` — so "one row per constructor" is the honest
granularity here, not "one row per call site".

**Full-document cite sweep 2026-08-31** ([AGENT], fidelity Tier-2 fix
round). EVERY `file:line` citation in this document — ~80, not just
the mirror table — was extracted by script and re-verified against the
tree; 55 were fixed: 49 pre-existing drift (among them the mirror's
own `appendSpillWidth` cell and §C7's `resumeThread` cite, both
already wrong on 2026-08-22 — so the paragraph above's "Every row's
site is now re-verified" was false at the moment it was written,
phase-2 fact-verification claim 13), and 6 renumberings caused by this
same fix round's new site-caveat comments in Machine.lean/Value.lean.
Scope honesty, unchanged from 2026-08-22's lesson: this assertion is
true of the tree at THIS commit only; no gate watches these numbers
between sweeps (the reconciler's C12 checks row COUNT, not lines).

| Site | Code | Bound | Consumed when | Empty-stream default |
|---|---|---|---|---|
| Map-iteration pick (`mapIter`) | StepFn.lean:615–621 | live candidates + conditional stop slot | every iteration (even width 1) | first remaining candidate in cell order, stop LAST (columns re-synced 2026-08-22 — the Bound/default cells were still describing the RETIRED snapshot design; launch audit D2-F1) |
| Append spill capacity (`appendSpill`) | Machine.lean:963 | `appendSpillWidth` (Ops.lean:1972) | every spill | gc growth-formula point |
| L2 select pick, entry path (`l2Entry`) | Machine.lean:2819 | ready-clause count | only width > 1 | first ready clause (clause order) |
| L2 select pick, arrival path (`l2Arrival`) | Multi.lean:853 | `.multi` outcome count | only `.multi` | first ready clause |
| L4 waiter pick (`l4Waiter`) | Multi.lean:1039 | matching-candidate count | only width > 1 | lowest (goroutine order, clause order) |
| L1 scheduler pick (`l1Sched`) | Multi.lean:1153 (via `Config.boundarySite`, :1099) | \|runnable\| | only width > 1 | lowest runnable goroutine id |
| L5 main-exit window (`l5ExitWindow`) | Multi.lean:1628 | 2 | main terminal ∧ others runnable | 0 = exit now |
| Post-op boundary pick (`postOp`, W3.2 stage C) | Multi.lean:1153 (via `Config.boundarySite`, :1100) | \|runnable\| (issuer-first menu, `schedSlots` :1122) | at an `.opDone .postOp` marker, only width > 1 | slot 0 = the ISSUER continues (the pre-widening schedule, literally) |
| Loop back-edge pick (`backEdge`, W3.2 stage D) | Multi.lean:1153 (via `Config.boundarySite`, :1101–1103) | \|runnable\| (current-first menu, `schedSlots` :1123) | at a loop re-entry shape (`.loop`, `.mapIterK`), only width > 1 | slot 0 = the CURRENT goroutine continues |

The race detector consumes NOTHING and replays nothing (stage B, Q2:
`raceUpdate` folds the step's emitted `StepEvent` — the old
consumption replication is deleted); the relation quantifies every
pick (`Step.selectApply`/`applySelect`'s stream+identity quantifiers,
`StepM`'s pick indices).

---

## 1. Concurrency and scheduling

### C1. Which runnable goroutine runs next (L1) — (a) ENVELOPED

- WHERE: spec — NONE. The spec has zero scheduling text (ground-truth
  note §1.2: pure omission latitude, bounded only by blocking rules and
  the memory model). Anchors (P2 retrofit, quote-precision fixed at its audit):
  mem#model — Requirement 1 constrains per-goroutine sequential
  consistency, Requirement 2 the synchronizing total order,
  Requirement 3 read visibility; NONE of them picks which runnable
  proceeds. The blocking rules that bound the envelope live in the
  SPEC — spec#Send_statements ("Communication blocks until the send
  can proceed") and spec#Receive_operator ("The expression blocks
  until a value is available") — with the memory model's sync-edge
  catalogue (mem#chan, mem#locks, mem#once) as the separate,
  visibility-side bound. Machine: `runnableIdxs` Multi.lean:220–224 (the
  envelope statement in situ), consumed at the boundary-site pick
  Multi.lean:1153. (Cites re-derived 2026-08-22, launch audit D2-F2.)
- ENVELOPE: any runnable goroutine may run next, at every registry
  boundary; width = |runnable|. Believed MAXIMAL **at registry
  granularity** — the envelope-width review (channels design note,
  2026-08-07, as corrected by BUG-044) argued no admitted member is
  outside conforming Go. It is NOT maximal absolutely: the granularity
  itself is the pin recorded as C2+C3 below, and the registry-point
  path set vs full interleaving is the open NPDRF obligation
  (register #5).
- EVIDENCE: GC — plain `go run` is a point-mass on schedule-dependent
  shapes (0/700-style; validation note §3); `-race` perturbation is the
  dual-sampling rule; membership lane polices too-narrow per shape.
  XIMPL would bear on nothing here (the spec is silent; the envelope is
  already "anything"). Upper bound argued from SPEC silence + MM
  blocking rules.

### C2. Preemption inside a boundary-free segment — (a) ENVELOPED at back-edge granularity (W3.2 stage D, B2)

- WHERE: spec — silent on scheduling, so preemption at ANY point is
  conforming (gc itself realizes asynchronous preemption since 1.14 —
  DOCS/GC; dossier §1.1). MACHINE (W3.2 stage D, G1 — B2): the loop
  RE-ENTRY shapes (`.next/.continuing (.loop …)`,
  `.next (.mapIterK …)`) are boundaries now (`Config.atBoundary`, the
  envelope statement in situ; site `ChoiceSite.backEdge`, slot 0 =
  current-continues via `schedSlots`), so a goroutine inside a
  registry-free segment can be descheduled at every iteration edge.
  Ordinary straight-line statement/expression steps, calls, loads and
  stores between boundaries remain private — the residual is
  SUB-STATEMENT granularity, register #5's reduction-line territory,
  not an iteration-monopoly any more.
- ENVELOPE, SHIPPED: a scheduling point at every loop back-edge — a
  goroutine stuck in a registry-free loop can always be descheduled
  (which is what every real Go implementation does), and the site is
  exactly what makes the liveness tier's `Fair` NON-VACUOUS (the
  fairness-expressibility note at `ChoiceSite.backEdge`'s policy
  docstring; boundary-set note §4).
- WHY IT WAS THE DOCTRINE'S KNOWN FIRST ITEM (register #1, now
  DISCHARGED there — the wedge row goroutines/send-then-spin is the
  standing exhibit): the
  SEND-THEN-SPIN wedge (recorded probe:
  `docs/evidence/2026-08-12_scheduler-wedge-probes/`) — a worker
  performs one registry op (a cap-1 send that wakes main) and then
  loops with no further registry op. The fused effect boundary (C3)
  offers no post-op scheduling point and forced continuation (this
  entry) runs the registry-free tail privately forever, so the woken,
  runnable main is never scheduled again: exit-0 unreachable on EVERY
  stream (511/511 fuel-out in the probe's exhaustive mod-2 depth-8
  sweep, default stream included) while gc exits 0 (60/60, +20/20 at
  GOMAXPROCS=1). `observed ∉ modeled` — definitionally a bug — and it
  poisons the ∀-stream claims' shape: `TerminatesNormallyC` is FALSE
  for a program gc always terminates. (Exhibit corrected at the
  2026-08-12 audit: a REGISTRY-FREE spinner — no registry op anywhere
  — is NOT this bug: gc's exit-0 there is in the modeled set via the
  default stream; its extra never-yielding streams are the too-wide,
  transfer-safe direction, and ∀-stream termination on that shape is
  the fairness quantifier's territory, not this re-envelope's. The
  probe record carries both shapes. Anchor for the transfer-safe half,
  P2 retrofit: mem#badsync states the registry-free spinner's
  conformity in normative-adjacent text — "The loop in main is not
  guaranteed to finish"; the WEDGE's bug status itself rests on the
  sync edges existing at all, mem#chan.)
- COST, PAID (W3.2 stages C+D; the note §5's budget): pinned streams
  shifted and were re-derived (the poller family's deferral witnesses
  moved to [1]*n); metatheory re-proved over the widened boundary set;
  enumeration trees branch at every new point — the REAL cost center:
  several rows' exhaustive certification left tractability entirely
  (the stage-C log's intractable five; the §5d per-site enumeration
  modes + nonterm accounting are the G1-ruled answer, DPOR/NPDRF the
  principled one, slice 5). CORRECTION to this entry's old cost prose
  (owed at landing, note §2): "race-detector segments shrink … clock
  traffic grows" over-predicted — boundaries are scheduling points,
  not clock edges (`raceUpdate` advances clocks at
  spawn/wake/pairing/sync EVENTS only), so B2 added zero clock
  traffic; only the interleaving of recorded accesses refines. The
  segment-HB prose's "private segment" notion narrowed from "between
  registry ops" to "between boundaries" with clocks unchanged.

### C3. Scheduling between an op's effect and its continuation — (a) ENVELOPED (W3.2 stage C, B1: the `.opDone` post-op boundary)

- WHERE: spec — spec#Program_execution and the MM give no ordering
  between one goroutine's post-synchronization progress and a woken
  partner's; any finite interleaving is conforming.
  Anchors-from-absence (P2 retrofit): the load-bearing SILENCE is
  mem#chan + mem#model — and note mem#chan rule (1)'s direction: a
  send is synchronized before the COMPLETION OF THE RECEIVE, not
  before anything in the sender's continuation, so the members this
  envelope admits are scheduling-latitude observables, never HB
  violations. The scheduling-semantics dossier
  (`docs/2026-08-20_go-scheduling-semantics-dossier.md`) grounds the
  width from the language side: §1.1 — scheduling deliberately
  unspecified, so the widening is conservative relative to what the
  language licenses.
- MACHINE (W3.2 slice 1 stage C, G1 ruling 2026-08-20 — B1 at
  ALL-ops scope): every registry-op completion that proceeds — chan
  send/recv/close, sync ops, select commits on all three paths,
  the pairing ISSUER, wakes, and spawn — leaves the acting goroutine
  on the `.opDone` completion marker, a registry boundary of its own
  (`Config.opDone`, the envelope statement in situ; `Config.atBoundary`;
  site `ChoiceSite.postOp`, slot 0 = issuer-continues so the
  default stream reproduces the pre-widening schedule literally; the
  spawn marker keeps its `l1Sched` tag — BUG-040's shipped default
  bit-for-bit). A woken partner can now interleave before the
  issuer's next private segment on an explicit stream.
- FORMER KNOWN INSTANCES, subsumed: BUG-040 (post-spawn) and BUG-044
  (wake-then-main-terminal, the L5 window, C4) were the two probed
  corners of this class; B1 is the general rule they were corners of.
  The formerly-recorded REMAINING GAP — the mid-program
  wake-then-abort analogue — is U-1, now PROBED AND ADMITTED (see
  U-1): gc's partner-progress member (print-"42"-then-abort, 60/200–
  189/200 across sessions) was `observed ∉ modeled` pre-B1 and is a
  member now (corpus row goroutines/wake-then-abort, members=2
  statuses=ok+panic; exhibition record
  `docs/evidence/2026-08-20_w32-postop-probes/`). The abort WINDOW at
  panic terminals stays open as B3 — DEFERRED at G1, RE-GROUNDED
  2026-08-31 (fidelity p2-fact claim 12; evidence
  `docs/evidence/2026-08-31-b3-abort-window-probes/`). Two
  corrections to the old record: (a) the window is
  post-**`.panicked`** (fully unwound, unrecovered — the state
  `execProgLoop` aborts on), NOT "post-RAISE" — post-raise partner
  progress is MODELED, since `.panicking` (mid-unwind, deferred
  functions running) is a live, steppable state the pool interleaves
  with (a forced-handshake probe completed a full channel round trip
  mid-unwind, 3/3 incl. GOMAXPROCS=1 — a modeled member); (b) the G1
  deferral's "no clean oracle observable" was too strong — a
  recover-based probe carries post-raise partner progress in an
  ordinary return value (6/6) — but that observable lands in the
  modeled region. The sharp post-`.panicked` probe (stdout+stderr
  merged on one fd, ordering partner output against gc's fatalpanic
  traceback): **56 runs, three configurations
  (default/GOMAXPROCS=8/dontfreezetheworld), ZERO exhibitions** — no
  observed ∉ modeled member is known. The honest residual is
  UPPER-bound and rests on the runtime's own text, not probe
  silence: gc's fatal-panic freeze is best-effort
  (deps/go/src/runtime/proc.go:1183-1199; the dontfreezetheworld
  path deliberately lets goroutines run until they enter the
  scheduler), so a permitted post-`.panicked` window exists but is
  output-invisible by construction — un-closable by differential
  testing, held as a recorded permitted-∉-modeled deferral on that
  argument.
- COST, PAID (the boundary-set note §5's budget): witnesses/pinned
  streams re-derived (BUG-040 precedent), MultiSound/MultiStreams/
  MultiWfSound metatheory re-proved over the widened set, detector
  outcome-shape classification moved to the marker. CORRECTION to the
  old cost prose here (owed at landing, note §2 B1): "race-detector
  segments shrink … clock traffic grows" over-predicted — in this
  machine boundaries are scheduling points, not clock edges
  (`raceUpdate` advances clocks at spawn/wake/pairing/sync EVENTS
  only), so B1 added no clock traffic.

### C4. How long after main's terminal other goroutines may run (L5) — (a) ENVELOPED

- WHERE: spec — spec#Program_execution: "It does not wait for other
  (non-main) goroutines to complete" — no ordering between main's
  return and others' progress; any finite continuation before teardown
  is conforming. Anchor addendum (P2 retrofit): mem#goexit — the
  explicit NON-edge at goroutine exit is why the others' post-main
  progress is unobservable unless separately synchronized, which
  bounds what the L5 envelope can ever expose. Machine: `execProgLoop` Multi.lean:1612 (envelope
  statement in situ; consume-2 at :1628, re-offered at every subsequent
  loop entry until exit picked or nothing runnable).
- ENVELOPE: {exit now, one more pool step}* — i.e. every finite prefix
  of registry-granularity continuations of the runnable others.
  Believed MAXIMAL at registry granularity (the re-offer covers any
  finite count; infinite continuation is not an observation). Inherits
  C2/C3's granularity pins like everything pool-side.
- EVIDENCE: GC — BUG-044's dossier probes (the excluded panic member
  realized by the PLAIN oracle 1/100 at 50k-iteration delay, 50/50 at
  20M); membership cases goroutines/wake-window/* certify {ok, panic}.

### C5. Which matching parked waiter pairs with an arriving op (L4) — (a) ENVELOPED

- WHERE: spec — NONE on waiter order ("any matching waiter"; gc's FIFO
  wakeup is one legal point). mem — NONE either (P2 retrofit): mem#chan
  matches a send to "the corresponding receive" with zero text on WHICH
  waiter corresponds; the absence is the anchor. Machine: `chanArrivalPlan` docstring
  Multi.lean:625–676 (envelope statement), candidate enumeration in
  goroutine order / clause order within a select,
  pick consumed at the `.l4Waiter` site Multi.lean:1039 only at
  width > 1. (Cites re-derived 2026-08-22, launch audit D2-F2.)
- ENVELOPE: any matching waiter, width = #matches (select clauses
  counted individually). Believed MAXIMAL (spec-silent axis; both
  members oracle-exhibited on the directed pin
  goroutines/sched-dependent/waiter-pick, {12,21}).
- EVIDENCE: GC — dual-sampling exhibits both members (12×3, 21×7);
  envelope-width review verdict NOT A FLAG with the F3 correction
  (336 width-2 L4 sites in first-come's certified tree). Open
  [ANALYSIS] question recorded there: whether L4 ⊆ L1-reachable holds
  for every program (each L4 member also realizable by arrival timing)
  — no theorem; per-shape membership polices it.

### C6. Which ready select clause commits at entry (L2, entry + arrival paths) — (a) ENVELOPED (possibilistic weakening)

- WHERE: spec — spec#Select_statements step 2 (step number corrected
  at the P2 audit against the pinned list): "If one or more of the
  communications can proceed, a single one that can proceed is chosen
  via a uniform pseudo-random selection." Recorded absence (P2
  retrofit): the memory model contains no NORMATIVE select rule (one
  incidental `select{}` appears in mem#chan's limit-channel example) —
  auditors of C6/C7 should not hunt for a mem# cite;
  spec#Select_statements is the entire normative basis. Machine: the L2 envelope
  statement at Machine.lean:2694–2764; entry consumption
  Machine.lean:2819; arrival-path consumption (`.l2Arrival`)
  Multi.lean:853. (Cites re-derived 2026-08-22, launch audit D2-F2 —
  the old C6 cite landed a reader on the postOp envelope instead.)
- ENVELOPE: ANY entry-ready clause (readiness waiter-extended on the
  arrival path). "Uniform pseudo-random" is weakened to the
  possibilistic "any": the envelope's SUPPORT equals the spec's on
  every FINITE trace (every finite observation sequence has non-zero
  probability under uniform choice, so no finite differential
  observation distinguishes the two), and on INFINITE traces the
  envelope is DELIBERATELY WIDER — it admits the schedule that commits
  clause 1 forever and starves a permanently-ready clause 2, which a
  conforming uniform-pseudo-random implementation realizes with
  probability 0. RESOLUTION [USER] 2026-09-02 (the fairness doctrine,
  `docs/2026-08-11_essence-of-go-doctrine.md` "Scheduling and
  fairness" — "the semantics should admit unfair schedules … Fairness
  is an assumption about the sequences that are chosen"): the weakest
  machine ADMITS the starving schedule; probability-1 non-starvation
  is a fairness assumption on the chosen sequence, stated where used
  (reasoning-side, over `Fair : Choices → Prop`) — never a machine
  constraint. This restates the row per assessment p2-keeps-a1 A1-12
  (KEEP-WEAKENED: the over-approximation and its DIRECTION must be
  stated, not the earlier "no probabilistic property is expressible"
  gloss); the former "distributional facts are out of scope by
  declaration" hedge is WITHDRAWN — the infinite-trace width is a
  stated doctrine consequence, and this row's spec-mandated
  distributional clause is where it bites.
- EVIDENCE: GC — dense sampling (per-execution re-randomization: the
  map-order regime), both members exhibited 5/5–3/7 on the pinned
  shapes; `clauseReady`'s send-on-closed-counts-as-ready subtlety is
  probe-pinned (p23, Machine.lean:1435–1440).

### C7. Which clause a WOKEN (parked) select commits — (b-n) NARROWED, deliberately

- WHERE: same spec sentence as C6 (a parked select that becomes ready
  again is still a select "choosing"). Machine: `resumeThread`
  Multi.lean:376–464 — a woken select head-commits the FIRST wake-ready
  clause in clause order, deterministically, consuming nothing ("no
  re-randomization on the blocked path"; the head-commit arm is
  :424–427).
- WHAT THE PLAUSIBLE ENVELOPE WOULD BE: any wake-ready clause (a second
  L2 draw at wake).
- THE SUPERSEDED ARGUMENT (envelope-width review, pre-B1/B2 — kept for
  the record, superseded 2026-09-01 [AGENT]): "a parked gc select is
  committed by the EVENT that wakes it (the partner dequeues one
  sudog), so gc's realized wake outcomes are arrival-order outcomes,
  and each is realized in our envelope by a prompt-wake L1 schedule."
  Its own re-argue trigger FIRED at the W3.2 B1/B2 boundary widening
  and the re-argument was not recorded (fidelity A1-14); when run, the
  premise was gc-FALSIFIED on the one-event/width-2 corner: a select
  parked with TWO recv clauses on ONE channel, woken by `close(ch)`,
  commits EITHER clause in gc (~half each, 200-run-per-config counts
  incl. a park-first isolate; `selectgo` builds lockorder from the shuffled
  pollorder precisely to permute same-channel cases, and `closechan`'s
  first dequeue wins the `selectDone` CAS). One event, two clauses —
  the event does not determine the clause, and no prompt-wake L1
  schedule realizes the non-head commit. Evidence:
  `docs/evidence/2026-09-01_c7-close-wake-probe/`.
- THE COVERAGE ARGUMENT OF RECORD (re-argued 2026-09-01 [AGENT],
  against the post-B1/B2 machine at 670d3351), two legs, [ANALYSIS]
  not theorem:
  (1) PARTNER wakes (an arriving send/recv beside the parked select)
  never reach `resumeThread` — the arrival intercept pairs them at the
  arriving op (`chanArrivalPlan`), where the L4 pick counts select
  clauses INDIVIDUALLY (C5), so gc's same-channel sudog permutation is
  a drawn choice in the model, not a narrowing.
  (2) CELL wakes — for a parked select, exactly the `close` case — are
  covered by the ENTRY-path schedule: close-before-entry is a
  machine-realizable interleaving of the same program on every shape
  (no HB edge can order a close after the select's entry, since entry
  immediately follows the parking goroutine's previous boundary and a
  park is not an event others can synchronize on; B1's post-op
  boundary guarantees the scheduling point immediately before entry —
  B1 STRENGTHENS this leg), and the entry-time L2 draw then covers any
  clause the close enables; the reordering changes no other
  observable (park performs no state change, so the state at the
  commit is identical). Deferred multi-event wakes reduce to the same
  two legs per enabling event, plus the head-commit itself as a
  spec-legal member. The narrowing remains path-structural, not
  observational: on the probe shape the certified set is {1,2}
  (entry-path realized; enumeration record in the evidence dir) and
  gc's realized {1,2} is contained. Membership polices too-narrow per
  shape.
- RE-ENVELOPE OBLIGATION + COST: a wake-path L2 draw — moderate
  (one consumption site added at `resumeThread`, stream shifts for
  pinned pool streams, enumerator bound work); LOW priority while the
  two-leg argument stands. Re-argue triggers (sharpened 2026-09-01):
  any change to the wake machinery, to the arrival intercept's
  clause-individual L4 candidates, or to the B1 boundary placement —
  legs (1) and (2)'s premises respectively (this row already lost one
  argument silently to exactly such a change; A1-14).

### C8. Sync acquisition order (Mutex/RWMutex/WaitGroup/Once contention) — (a) ENVELOPED, via L1 (zero new sites)

- WHERE: spec/DOCS — nothing on acquisition order among contenders (no
  fairness, no FIFO; gc realizes semaphore-FIFO handoff WITH barging —
  one legal point). Anchors (P2 retrofit): mem#locks — the n<m
  Unlock/Lock rule orders VISIBILITY across the acquisition sequence
  and says nothing about which contender acquires (the absence half);
  its TryLock sentence ("may be considered to be able to return false
  even when the mutex l is unlocked") is an explicit spec-granted
  spurious-failure envelope member to model if TryLock ever lands.
  mem#once carries the once.Do edge quoted at the arm; the DOCS
  citations at the arms rest on mem#more's delegation — verbatim: "The
  documentation for each of these specifies the guarantees it makes
  concerning synchronization" (quote corrected at the P2 audit; the
  earlier paraphrase wore quote marks it hadn't earned). Machine: `applySyncOp` envelope statement
  Machine.lean:2424–2486 (consumes nothing, ever); wake-readiness is
  cell-based (`wakeReady` Multi.lean:162–199); which ready contender
  proceeds is the existing L1 pick (sync design §6).
- ENVELOPE: every registry-granularity schedule over runnable
  goroutines — contains gc's handoff member and every barging member.
  Believed MAXIMAL at registry granularity (acquisition order = run
  order of acquire steps; L1 admits all run-orders).
- CONTAINED DIVERGENCE, recorded (sync design §8 R1): at the
  both-parked RWMutex state gc's successor is deterministically
  reader-first where the model's cell logic is writer-first; the
  ACQUISITION-ORDER envelope contains both (certified
  sync/rwmutex-order/acquisition {10,20}, both gc-witnessed), so this
  is a realized-point difference inside the envelope, not a hole.
- EVIDENCE: GC — probe suite p01–p26 (sync design §2); membership
  certification. DOCS bear directly (the Mutex/RWMutex doc sentences
  quoted at the arms: `pendingW` reader exclusion, Wait-at-zero).
- INDIRECTION PRESERVES THE SITE (Q-SYNCVAL, RULED [USER] 2026-08-31,
  implemented 2026-09-01 — `docs/2026-08-31_qrow-rulings.md` row 6): a
  sync op reached AS A VALUE (interface dispatch, method value, go
  callee, passed callback) consumes the SAME C8 site as the direct
  call, or refuses — never a variant. Mechanically: the frontend's
  bodied sync stubs emit the same `sync-op` wire node as the direct
  interception, from the same op table (emit.go `syncOpFor` /
  `syncStubBody`), so the machine path from `applySyncOp` on is
  literally shared; the extra stub frame adds private steps only (no
  new boundaries at registry granularity — memo §6). Misuse identity
  pinned green: `sync/iface-dispatch/locker-double-lock`,
  `sync/escapes/method-value-negative-panic`.

### C9. Global deadlock: detect-and-classify vs hang — (b) PINNED to gc's runtime detector (spec-silent)

- WHERE: spec — nothing; a deadlocked program simply "blocks forever".
  gc's runtime realizes a global detector: `fatal error: all goroutines
  are asleep - deadlock!`, exit 2 (DOCS/GC). Machine: `.deadlock`
  terminal thrown when no goroutine is runnable (`stepMulti`
  Multi.lean:1137–1144, `execProgLoop` :1639; Value.lean:183–193
  records the latitude: "the detection itself is the flagship's
  rendering of the spec's 'blocks forever'").
- PLAUSIBLE ENVELOPE: {detected-fatal, silent hang} — a conforming
  implementation without the detector hangs. The observable difference
  is temporal (a hang has no exit), so within a terminating-run corpus
  the pin and the envelope coincide observationally; the pin's real
  content is the fixed message/exit-class and the CLAIM SHAPE
  (deadlock-freedom via `ProgressExecC` excludes the terminal — that
  transfer needs only "Go never completes a deadlocked run", which is
  forced).
- RE-ENVELOPE: likely PERMANENT-pin territory — record, don't widen
  (widening to "hang" would only weaken claims for zero fidelity gain);
  the message/exit pin is R9's class. Cost of the record: zero (this
  entry).

### C10. Racy programs — REFUSED by doctrine (§5), and the detector's OWN latitude alignment

- WHERE: MM — racy programs get essentially undefined behavior
  ("An implementation may always react to a data race by reporting the
  race and terminating the program" — mem#overview verbatim, corrected
  at the P2 audit; mem#restrictions phrases the same license as "Any
  implementation can, upon detecting a data race, report the race and
  halt execution ..." (elision marked per the delta-review) — go_mem's escape hatch is exactly a refusal
  license). Anchors (P2 retrofit): mem#overview and
  mem#restrictions both carry the escape hatch; mem#restrictions
  additionally grounds (a) the limited-outcomes stance the refusal
  deliberately declines to model, and (b) the per-sub-value any-order
  license for array/struct/complex accesses — the normative text
  behind O1's whole-cell over-approximation and U5's granularity
  discussion. NOTE the anchor-stability lesson attached to exactly
  this section: `977e23a707` (2023) ADDED the per-sub-value paragraph
  with no anchor or version-line change — content hashing, not anchor
  existence, is the drift signal here. Machine: `RaceState`/`raceUpdate`
  (Race.lean + Multi.lean:1384, the fold run at :1635), terminal
  `raceDetected`.
- CLASSIFICATION: not an envelope — a doctrine-decided boundary
  (register #4): SC interleaving is claimed only inside DRF; outside,
  fail-closed refusal. The latitude the DETECTOR itself resolves is its
  HB edge set: targeted at TSan's REALIZED edges (gc's instrumentation),
  not go_mem's minimal relation — each divergence quoted at its
  implementation site. Scope ledger, code-verified: U1 CLOSED 2026-08-19
  (the (L) surgery's pick loads the live cell — map-range now has a
  per-iteration read footprint), U2 (len/cap on channels
  uninstrumented both sides; len on MAPS recorded), U3 CLOSED
  (BUG-045/046 chan-object accesses), U4 (sync-object internal
  accesses unmodeled — misuse-only), U5 (release merge-vs-overwrite:
  ours is memory-model-exact merge, TSan over-reports — TSan-red/
  ours-green, un-lane-able), O1 (whole-cell composite-read
  over-approximation, BUG-041 — NARROWED 2026-09-02 by the Q-RACEPATH
  ruling, RULED [USER] 2026-08-31 `docs/2026-08-31_qrow-rulings.md`
  row 4: the constant-index narrowing — `projChainTarget` extends the
  shipped `fieldGet`-chain narrowing to `indexGet` frames with a
  CONSTANT literal index over an ARRAY cell, in either chain order
  (`a[1]`, `a[1].x`, `s.arr[1]`), the faithful footprint under
  mem#restrictions' per-sub-value license quoted above; the
  DYNAMIC-index residual (`a[i]`) stays whole-cell, red-pinned by
  `race/free/array-dyn-index-read-write`, with its re-open trigger
  recorded in O1 — memo §4 option (B) only if a real target needs
  dynamic-index disjointness on a value-path array). Race.lean:12–15:
  the detector consumes no choices; refusal is choice-invariant per
  stream.
- EVIDENCE: GC (`go run -race` as second oracle; TSan one-red-is-proof);
  the enumerator's every-path refusal at registry granularity. The
  registry-point-vs-full-interleaving gap is the NPDRF obligation —
  C2/C3's territory. MEASURED 2026-09-02 (the detector-soundness
  differential, `scripts/detector-soundness`;
  `docs/2026-09-02_detector-soundness.md`; evidence
  `docs/evidence/2026-09-02_detector-soundness/`): the two oracles
  crossed in BOTH directions on the 364 in-scope corpus rows at the
  branch tip (10 `-race` runs each at GOMAXPROCS 1 and 8 vs the
  schedule enumerator; the audit fix round's re-run, `corpus-tip.*` —
  the first run covered 362 of the 364, missing the two BUG-080 pins)
  and 45 novel footprint-gap probes. Corpus: agree-race 23 / agree-DRF
  275 (277 after the §2.1 deep re-run) / third cell (gc red, machine
  DRF) **2 — exactly BUG-080's pins** / over-refusal 1 (the O1
  residual, by design) / uncertified 63 (61 after; none gc-red: 20
  deadlock members with no gc verdict either, 7 fatal members, 24
  frontier refusals, 11/9 budget, 1 truncated).
  Probes (45): agree-race 24 / agree-DRF 12 / third cell 2 + 3
  uncertified-by-fatal — ALL the recorded U4 class (sync-object state
  words → **BUG-080**, born-FAIL pins `race/negative-sync/{wg-
  overwrite,mutex-copy}`; fix = the atomic access kind, not a table
  entry — LANDED 2026-09-02 as its own [USER]-ruled slice: `AccessKind
  ∈ {read, write, atomicRead, atomicWrite}`, TSan's realized per-
  primitive set recorded at the primitive's path; corpus HOLE cell
  2 → 0 (`corpus-bug080.*`), the two pins + `rw-overwrite`/`once-copy`
  PASS/racy, the 28-subject two-direction family `probes/u4kind` 26
  agree + 2 diagnosed possible-HOLE, residuals at BUG-080) /
  over-refusal 3 (O1 residual + two schedule-dependent races the
  10-run sampler never realized but the enumerator did) / 1 more
  uncertified: `probe/u5/cross-unlock-publish` (gc red 7/10; under the
  fix round's runner a `possible-HOLE`, diagnosed below).
  Scope-ledger consequences: U2 CONFIRMED benign on go1.26.5 (7/7
  probes agree both ways); U4 is now PINNED and classified as the
  detector's one soundness-direction gap (misuse-only); U5 NOT
  measured — the probe meant to exhibit it is RACY under go_mem
  (per-execution Unlock/Lock numbering; the machine refuses its racy
  paths on forced tapes), so the ruling **Q-U5** the first report
  draft posed on it was WITHDRAWN at the pre-merge audit ([USER]
  ruling: "posed on a refuted premise; withdrawn at audit B1", report
  §3.3); the merge-vs-overwrite Release difference stands exactly as
  the U5 entry above records it — its true exhibit needs a third
  lock-holding goroutine and cannot be made deterministic, hence
  un-lane-able. Register #4 carries the same measured state in its
  own words.

### C11. Tie-breaks that look like latitude but are unreachable/unobservable — (c) FORCED

- `panicMsg?` picks the first panicked goroutine in id order
  (Multi.lean:1550–1556) — defensive only: the loop aborts at the first
  panicked config, and one pool step creates at most one, so the
  multi-panicked tie-break is unreachable in the driver. WHICH
  goroutine panics first is C1's (and C2/C3's) latitude, not a new
  site.
- Goroutine ids = spawn order (pool index, Multi.lean:112–121); heap
  addresses = `nextAddr` bump (State.lean:361–363). Unobservable
  in-language at the observation channel (uintptr observations refused;
  pointer formatting unsupported); they surface only as model-internal
  identity (`ChanValue.base` equality — forced semantics) and detector
  keys. The one place allocation identity WOULD be observable —
  gc's eface-identity `[recovered]` collapse — is fail-closed
  (R10/BUG-004 item 1).
  **UPGRADED 2026-08-13 — heap addressing is (q) ENVELOPE-BY-QUOTIENT;
  the discharging theorem was PROVED on what is now the parked
  reasoning branch** (branch-located 2026-08-31 per the repo-split
  citation convention; the old present-tense "is now PROVEN" read as
  a claim of this tree). Go promises no address determinism (and gc
  moves stacks intra-run, transparently); the sequential `nextAddr`
  allocator was PROVED (2026-08-13) a quotient representative:
  `Frame.allocatorIndependence` (over `execStmtLoop_ren`) transfers
  any run to any conforming address relabeling — any `ShiftSpec`
  injection; `swapShift` witnesses the non-uniform width — at the
  same fuel/stream/outcome with related terminals, and the modeled
  pointer surface is equality-only, which injections preserve. The
  theorem and its design note live ONLY on branch
  `park/reasoning-2026-08-31`
  (`proofs/GoLeanProofs/Frame/AllocIndep.lean`;
  `docs/2026-08-13_executable-frame-theorem.md` §5b — not in this
  tree); nothing here contains or re-checks the discharge, and
  machine changes here can drift from the proved-against machine
  until the reasoning repo exists and pins this one. What THIS repo
  maintains is the machine-side CONDITION below. RE-OPENING
  CONDITION (scope honesty): the quotient covers the modeled
  observable fragment only — modeling `%p` output, pointer ordering,
  `unsafe` int↔ptr, or any address-exposing channel re-opens this
  entry.
- Goroutine EXIT has no HB edge (Race.lean:790–797; mem#goexit
  verbatim at the pin: "The exit of a goroutine is not guaranteed to
  be synchronized before any event in the program" — the P2 audit
  caught this entry quoting the PRE-2022 "happen before" wording,
  which occurs nowhere in the pinned file; Race.lean's own quote was
  already correct) — forced by the memory model.

---

## 2. Sequential evaluation order

### E1. The spec-ordered core — (c) FORCED (machine follows; history recorded)

Spec (spec#Order_of_evaluation) orders function calls, method calls,
receive operations, and binary logical operations left-to-right;
§Assignments (spec#Assignment_statements) mandates the two-phase
discipline and phase-2 left-to-right stores with the
earlier-store-observable example; select operands evaluate exactly
once in source order (spec#Select_statements step 1); channel buffers are FIFO
("Channels act as first-in-first-out queues", Value.lean:634–641);
defers run LIFO. The machine realizes all of these deterministically
(storeK one-store-per-step Machine.lean:1843–1850, StepFn.lean:634–646;
select entry Syntax.lean:354–361; send channel-then-value
Machine.lean:1122–1132). The BUG-022/025/029/030/033/034/035/036/037
family was the machine being WRONG against these forced points — fixed
or tracked in BUGS.md, not latitude; the 2026-09-01 $GOROOT/test
harvest added BUG-074 (select operands not snapshotted at entry —
spec#Select_statements step 1), BUG-075 (multi-value `return` stored
result 1 before operand 2 evaluated — the two-phase discipline at
returns) and BUG-076 (the range non-evaluation special case missing)
to the same was-wrong family. Cross-link (P2 retrofit):
mem#model Requirement 1 DELEGATES sequenced-before to exactly this
section — the spec's forced core is also the memory model's
per-goroutine order, so E2–E4's residual latitude propagates verbatim
into sequenced-before (matters the day an E-series envelope meets a
concurrent observer; E5 is no longer residual latitude — FORCED, with
gc's early store a deviation, L-016, 2026-09-02).

### E2. Call vs. assignment-target operands — (b) PINNED to gc (call-first)

- WHERE: spec#Order_of_evaluation: "the order of those events compared
  to the evaluation and indexing of x and the evaluation of y ... is
  not specified." Machine: the PINNED LATITUDE rule-site block
  Machine.lean:3040–3072 (spec text verbatim, gc realization probed
  go1.26.5, version-tracked; cite re-anchored 2026-08-22, D7 MEDIUM-7; re-swept 2026-08-31), frame-exit twin :3216–3230, `callArgsK`
  docstring :1718–1727, StepFn.lean:166/564/685. History: BUG-052.
- PIN: the call evaluates first (args, frame); target operands evaluate
  at frame exit; then stores. gc's realized point. Plausible envelope:
  both orders (and in principle interleavings of the operand
  evaluations with the call's effects). F2 reading (P2 retrofit,
  Cerberus vocabulary — prior-art note §3): claimed as UNSEQ,
  interleaving admitted, not merely either-order — a compound target
  operand (`aa[i][j]`) has multiple observable sub-events that could
  in principle interleave with the call's effects; the spec's silence
  licenses the wider reading, and too-narrow is the membership lane's
  risk to police.
- EVIDENCE: GC — the S1-audit probe matrix, five oracle-backed corpus
  pins + `.callValue` discriminators (verified RED at the pre-fix
  machine). XIMPL/ARCH would bear on whether any implementation
  realizes operand-first (none known).
- RE-ENVELOPE OBLIGATION + COST: a two-point (or wider) envelope at the
  call rules — touches the call/frame-exit machine arms, the wp call-law
  family (`wp_call_start`, frame-exit family — restated once already
  for BUG-052; a second restatement is the cost ceiling), stream-bound
  metadata, and the five timing pins (would become membership rows).
  MODERATE-HIGH; sequential-only observable (panic/value divergence
  requires a callee mutating a target operand).

### E3. Inter-target phase-1 operand order — (b) PINNED to OUR point, **known ≠ gc** (open envelope)

- WHERE: spec#Order_of_evaluation (only calls/receives/binary-logical
  are ordered — target-vs-target operand order is open). Machine:
  left-to-right inter-target walk (the tgtOpK spine; the rule-site
  SCOPE clause (Machine.lean:3064, "the pin covers ONLY the
  call-vs-operand axis"; cite re-anchored 2026-08-22) records this
  axis as OPEN and explicitly NOT covered by E2's pin). Record: BUG-032's S1-delta
  amendment.
- THE FACTS (GC-probed, verifier-reproduced): for
  `aa[5][0], b[*pn] = f6()` gc reports the SECOND target's operand
  panic and we the FIRST's; answers flip when targets swap; at three
  panicking targets gc picks the MIDDLE (`[9] with length 3`) — gc's
  realization is compiler-internal (stable under `-N -l`), hence
  UNPINNABLE. Both realizations spec-legal; the divergence cannot
  escape panic selection into side effects (frontend hoists calls out
  of target operands — probed).
- PLAUSIBLE ENVELOPE: any order of the targets' operand evaluations —
  observable ONLY as which panic wins (panic-identity membership).
  F2 reading (P2 retrofit): the honest claim is UNSEQ across targets
  (compound operands have multiple sub-events), not merely
  either-order per pair; at today's panic-identity observable the two
  readings coincide (which panic wins), recorded so the equivalence
  gets re-checked if a richer observable ever lands.
- RE-ENVELOPE OBLIGATION + COST: either full-statement linearization
  with an order choice (deliberately not built — BUG-032 records why)
  or a panic-identity membership envelope (admit any of the candidate
  panics — needs status-diverse membership machinery pointed at panic
  identity). MODERATE; sequential-only; today it is a recorded
  deterministic divergence with no strict-lane pin possible.

### E4. Targets-vs-RHS unordered panic order — same class as E3 — (b) PINNED to OUR point

- WHERE: BUG-032 round-4 amendment (b): `xs[ys[9]], b = zs[7], 2`
  realizes the LHS-operand panic where gc realizes the RHS's; both
  spec-legal. Machine: phase-1 targets-then-RHS order (tgtOpK → rhsK,
  StepFn.lean:469–500).
- Same plausible envelope, obligation, and cost as E3 (one mechanism
  fixes both axes); recorded as OPEN envelope per BUG-032's precedent.
  F2 reading: as E3 — the shared mechanism inherits the unseq claim.

### E5. Early store across the phase boundary — (c) FORCED; **gc DEVIATION** (L-016; re-labelled from (b) PINNED latitude 2026-09-02, [USER] ruling)

- RULING ([USER] 2026-09-02, Mike, verbatim: "agree we should mark as
  a gc deviation, and record in our gc bug backlog"). This row is NOT
  latitude. The machine sits on the spec point; gc's early store is a
  **deviation from the spec**, recorded in the gc bug backlog as
  `docs/spec-divergence-ledger.md` **L-016** (`gc-bug`; upstream
  classification pending — UNFILED; filing is a [USER] public action
  and has not been done). The analysis the ruling acted on is the
  grossmith campaign-3 verifier's [AGENT] (2026-09-02), below.
- WHERE: spec#Assignment_statements, the two-phase sentence — "First,
  the operands of index expressions and pointer indirections … on the
  left and the expressions on the right are all evaluated in the usual
  order. Second, the assignments are carried out in left-to-right
  order." — is NORMATIVE: every phase-2 store follows every phase-1
  evaluation, so a phase-1 panic precedes ANY store. The former
  "both spec-legal" argument (BUG-032 final-check amendment,
  2026-08-06) rested on spec#Order_of_evaluation ordering only
  calls/receives/binary-logical; but that clause governs order WITHIN
  phase 1 ("the usual order") and never licenses a phase-2 store to
  move into phase 1. Shape: `x, a[i].f = 1, 7/z` (z = 0, recovered) —
  gc lands x = 1 before the division panic; the machine (the tgtOpK →
  rhsK → storeK spine, StepFn.lean:469–500) keeps x = 0, the spec
  point.
- WHY DEVIATION, NOT LATITUDE (the verifier's three witnesses, all
  independent of our own correctness): (1) the sentence's own
  structure, above; (2) gc's OWN regression test
  `deps/go/test/fixedbugs/issue43835.go` (2021) asserts that
  `bad, _ = true, *p` under a recovered nil-deref leaves `bad` false —
  gc itself treats a visible early store as a bug; its fix
  (`walk/assign.go` `ascompatee`, `deferResultWrite` + the
  `readsMemory` aliasing heuristic) covers RESULT-PARAMETER targets in
  functions with defers and `return`, and leaves ordinary locals
  captured by the deferred closure uncovered — an aliasing
  optimization whose panic path leaks through `recover`, exactly the
  probe matrix's shape: early store for a division operand
  (p1/p2/p5, PROBED; `readsMemory`'s op list predicts the same for
  shift/arithmetic/conversion/type-assert operands — read from source,
  UNPROBED), none for index/deref (p4, probed); (3) our BUG-075
  (FIXED 2026-09-01): the machine's identical early store at `return`
  was treated as a WRONG ANSWER under the same sentence
  (spec#Return_statements "like an assignment"). One sentence cannot
  be forced at `return` and latitude at `=`.
- RE-ENVELOPE OBLIGATION: **WITHDRAWN** (2026-09-02, consequence of
  the ruling). The prior record queued a two-point store-timing
  envelope (Cerberus Q2 mold, §7 item 5, dossier E5's proposal). Acting
  on it would add a behaviour the spec forbids and so widen the
  machine PAST the spec — the machine is "the weakest machine Go
  PERMITS", and Go does not permit this. No corpus row either way: a
  strict row of the shape would pin gc's wrong answer (L-014's
  reasoning); the reproducers live in evidence, not `Corpus/`.
- WITNESSES (kept as the deviation's evidence, not as envelope
  members): the reproducer matrix p1–p6 with gc/machine outputs,
  `docs/evidence/2026-09-02_e5-gc-deviation/` (gc: 29 on p1/p2/p5 at
  default flags AND `-N -l`; machine 58 = spec on all six; p4's index
  panic holds the store back); campaign-3 generated witnesses
  `m3a-rerun/part-04/case_03110` (seed 5,015,110, §5.2) and
  `m3pairs/part-01/case_03079` (seed 6,003,079, §5.0) of
  `docs/2026-09-01_grossmith-campaign-3.md`; the 2026-08-15 dossier
  probes (`docs/evidence/2026-08-15-dossier-e5/`: GLOBAL targets get
  the spec point — consistent with the aliasing reading).
- History of the record: latitude row "(b) PINNED to the spec-literal
  point; gc elsewhere" from 2026-08-11 to 2026-09-02 (BUG-032
  final-check amendment 2026-08-06 → inventory row 2026-08-11 → F2
  reading + Q2 mold 2026-08-17 → dossier E5 membership proposal
  2026-08-15 → campaign-3 witnesses 2026-09-02 → ruling). The §9 flag-3
  asymmetry note ("here the machine's point is the SPEC-shaped one and
  gc's is the exotic one") was the tell: the row never fit the
  "pinned to gc" framing because it was never a pin.
- Returns (2026-09-01, BUG-075): multi-value `return e1, …, en` sits in
  the FORCED two-phase core — decodeReturn evaluates every operand into
  a temp, then stores all results. gc's return side is spec-conformant
  (issue43835's `g`/`h` pass on gc — its fix covers `return`); the
  deviation of this row is the ASSIGNMENT side with non-result targets.

### E6. `len`/`cap` hoist discriminating shapes — REFUSED (narrowed to the true residual, A6 2026-08-31)

- WHERE: BUG-032's fix as amended by mini-slice A6 (t1-fidelity-fixes):
  the refusal now fires ONLY on the composition (panicky residual
  operand) x (panicky inline material to its left) x (ordered event
  after it in the same sweep) — `sweepOrderedEventAfter` /
  `residualPanicFreeOperand` / `sweepPanickyInlineBefore`, emit.go;
  pinned red-by-design at builtins/len-vs-call-order/panicky-between.
  Not latitude: a coverage refusal that EXISTS because realizing gc's
  point inside the E3/E4 latitude needs the linearization not built.
  The F23 reach (idiomatic `len(p.xs)` refused in any receive-bearing
  function; whole-package kills through methods) is RETIRED: those
  shapes now lower, inline or hoisted, at gc's realized order
  (channels/recv-order/dead-recv-len-* and the e6-* pair pin it
  green). B-3 correction (2026-09-01 audit fix round): A6 is NOT a
  pure narrowing — the sweep-scoped predicate fires on calls too, so
  receive-FREE functions GAINED this refusal on the composition at
  the same time BUG-062's silent wrong answer died there; trade
  stated (a new visible refusal bought the retirement of a
  spec-FORCED silent wrong answer).

### E7. Hidden-dependency initialization order — (b) PINNED to go/types' conforming order, **known ≠ gc**

- WHERE: spec#Package_initialization: "If other, hidden, data
  dependencies exists between variables, the initialization order
  between those variables is unspecified." (sic — "exists" is the
  pinned spec's own typo, preserved inside the quote per the P2
  audit; silently correcting quoted text is the exact class the
  citation norms forbid). Machine/frontend: go/types
  `InitOrder` drives `$pkginit` synthesis (init design §1; the
  dependency analysis itself is spec-pinned and NOT latitude).
- THE FACTS (GC-probed): gc's initorder is a separate, coarser analysis
  and diverges on exactly the spec's own example shape —
  `init/hidden-dep-order`: go/types [hiddenX, hiddenB, hiddenA]
  (4242) vs gc hiddenX-after-a/b (4624242). Both conform. This is the
  doctrine's TOO-NARROW, soundness-relevant direction: theorems over
  our order do NOT transfer to gc executions of hidden-dep programs.
  GUARDED since 2026-08-31 (t1-fidelity-fixes; the charter-era "ships
  FIRST" ruling, finally executed): the fail-closed detector
  `tools/nativefrontend/hiddendep.go` refuses the export of any
  program whose kept package-level initializer REACHES (through
  statically-resolved calls) a method call dispatched through an
  interface whose name matches a same-unit method reading an
  initialized package variable — the observable hidden-dep shape, the
  spec example's own composition. Refusal pin:
  init/hidden-dep-refused. The ONE exception is the recorded
  deviation case below, allowed explicitly in the APPARATUS
  (--allow-hidden-dep-init-order, keyed to the exact case id in
  scripts/diff-coverage and scripts/check-frontend-pins; the finding
  still prints as a warning on every allowed run). Recorded residual:
  dispatch through FUNCTION VALUES is a distinct hidden channel the
  detector does not cover (it rides this row's re-envelope
  obligation). The deviation case is a standing differential red with
  the realized order mechanically pinned (scripts/check-frontend-pins
  since the 2026-08-31 repo split; previously check-golden
  deviation-observation pin), so drift to a third order is caught.
- PLAUSIBLE ENVELOPE: all conforming initialization orders (the
  lexical-reference partial order's linear extensions, with
  hidden-dep-affected variables freed).
- RE-ENVELOPE OBLIGATION + COST: a named Choices site over conforming
  orders + envelope discussion (deliberately deferred, recorded in the
  design note). The cheap interim — the fail-closed frontend DETECTOR
  (method-through-interface-conversion reachability) — LANDED
  2026-08-31 (see above), converting the unguarded silent-divergence
  into a visible refusal; the func-value channel and the full envelope
  remain on this obligation. Full envelope: MODERATE
  ($pkginit becomes schedule-bearing; strict-lane init cases must stay
  on the deterministic default point). North-star exposure recorded:
  etcd-io/raft has package-level vars — must be checked at the target
  lane.

### E8. Multi-file declaration order — (b-n) NARROWED to the go command's DIRECTORY-mode presentation

- WHERE: spec: "the order in which the files are presented to the
  compiler"; build systems are "encouraged" to sort by file name.
  Frontend: files sorted by name (tools/nativefrontend — main.go run()
  + load.go parseLocal, both carrying the E8 site note since
  2026-08-31) — matches the go command's DIRECTORY-mode presentation
  exactly (init design §1.2; pinned by init/multi-file-order). Since
  2026-08-31 (t1-fidelity-fixes) the realized per-unit order is a
  WIRE-LEVEL record: program key "fileOrder" (emit.go).
- CORRECTED PREMISE (p2-keeps-a1 A1-18, 2026-08-31): the other members
  of this latitude are NOT exotic non-go-command build systems — the
  go command's own FILE-LIST mode (`go run zz.go aa.go`) presents
  files in ARGUMENT order and realizes them at the pinned oracle
  (probe: za/az/az from the same two files). The frontend has no
  file-list input mode (--dir only), so the machine models exactly the
  directory-mode member; the differential harness invokes the oracle
  in directory mode, so the apparatus is scoped to the agreeing
  member. REVISIT TRIGGER (replacing the unfireable non-go-command
  one): any consumer feeding the frontend a file-list-mode build —
  that consumer must either present a directory (the modeled member)
  or fund the presentation-order envelope. Machine-side single
  realization + record: this row's disposition per the Tier-1 fix
  round; the register-side restatement rides Tier 2.

### E9. Map iteration order — (a) ENVELOPED (full literal envelope over the LIVE map) — RE-ENVELOPED 2026-08-19 (BUG-005 (L) surgery, user-ruled)

- WHERE: spec#For_range (tightened from the parent section per the
  P2 audit): "The iteration order over maps is not
  specified and is not guaranteed to be the same from one iteration to
  the next", plus the production table's three mutation clauses.
  Machine (post-surgery): range entry reads base loc + START-KEY set
  off the live cell (`mapRangeStartSets`); each pick recomputes
  CANDIDATES = live entries minus produced keys, validated
  self-normalized, and loads the value from the LIVE cell
  (`mapIterCandidates`/`mapIterLiveEntries`, Machine.lean); the stop
  slot (width `candidates + 1`, stop LAST) is legal exactly when no
  MANDATORY candidate remains (`mapIterMandatoryRemains` — a candidate
  whose key is a never-removed start key must still be produced);
  `mapDelete`/`clearMap` prune deleted keys out of same-goroutine
  `mapIterK` frames via `contAfterStmtOp` (delete-prune), which is
  what makes "removed before being reached ⇒ not produced" exact.
- ENVELOPE: the FULL literal envelope of the spec's production table,
  user-ruled 2026-08-19 ("any latitude in the Go spec should be
  supported" — no narrowings): all orders of surviving entries;
  deleted-then-not-reached never produced (FORCED); created entries
  may be produced or skipped, each at any legal position (the
  delete-then-recreate reading — a re-created key is a NEW entry — is
  I-1 in `docs/spec-interpretations.md`, ledger L-012). The canonical
  member is DEFINED as the machine at the zero stream (pick index 0
  every time, stop last); self-inserting loops are genuinely unbounded
  and fuel out visibly there — correct, and the ∀-stream confluence
  checker FAILS CLOSED on them (membership lane instead).
- EVIDENCE: GC — per-run re-randomization makes sampling dense; the
  formerly red live-mutation pins (delete/clear/update/
  delete-unreached-during-range) are green post-surgery, and the
  created-entry latitude rows are MEMBERSHIP rows
  (maps/delete-readd-during-range, maps/added-entry-count).
- RESIDUAL NARROWING — **REOPEN (2026-08-31, corrected per the
  code-wins rule; fidelity finding A1-20)**: delete-prune rewrites
  only the SAME-GOROUTINE continuation. This row previously disposed
  of the cross-goroutine case as "already a data race by the race
  footprint's pick-time read" — FALSE against the machine's own site
  record: `Cont.mapIterK`'s envelope statement scopes the unpruned
  case to a **DRF cross-goroutine delete (synchronized mid-range)**,
  which no refusal touches (a channel handshake HB-orders the delete
  against every pick; `-race` and C10 stay green). So the narrowing
  is NOT unobservable-by-refusal: a spec-permitted member of this
  row's [USER]-ruled FULL literal envelope — re-production of a
  cross-goroutine deleted-then-re-created key, a NEW entry under
  I-1 — is unrealizable: **permitted ∉ modeled on a DRF program**,
  standing, in the census's own exemplar row. The old re-envelope
  trigger ("widen or justify at the first cross-goroutine-range case
  that is not already racy-red") has FIRED by construction — the DRF
  shape exists and the code names it. The machine-side fix
  (cross-goroutine prune, or a [USER] re-scope of the 2026-08-19
  full-envelope ruling to same-goroutine mutation) is Tier-5 work,
  explicitly NOT closed by this record correction; a corpus witness
  (handshake-synchronized delete-and-recreate during another
  goroutine's range) is owed so the hole is red rather than prose.

### E10. Which `==`-equal map key is retained on overwrite — (b) PINNED (always-replace)

- WHERE: spec — silent (only requires `==` on key types); gc realizes
  per-type `needkeyupdate` (floats design §4, arc-final F15). Machine:
  `entries.set! i (key, value)` — the NEW key replaces the stored key
  (Machine.lean:258–270, the `entries.set!` at :268, via
  `mapEntryIndex?` Ops.lean:1754–1762).
- Observable exposure: exactly the key kinds where `==`-equal keys are
  distinguishable when the stored key is later observed — the recorded
  list is float/complex/string/interface/array/struct keys (floats
  design §4; the in-language observable is the float case's `1/k` sign
  probe — retention is unobservable for every kind where `==` implies
  bit-equality). Matches gc where pinned (`floats/signed-zero-map-key`
  green, version-tracks gc's choice); a conforming
  original-key-retaining implementation is outside — transfer caveat
  recorded at the site (`mapAssignValue`, Machine.lean; ADDED
  2026-08-31 at the fidelity fix round — this row previously asserted
  a site caveat that did not exist, phase-2 finding A1-21; corrected
  per the founding code-wins rule).
- RE-ENVELOPE: a two-point retention choice — LOW cost (one arm), LOW
  value until a cross-implementation lane exists.

### E11. Runtime check ORDER inside one operation — (b) PINNED to gc

- WHERE: spec — panics are mandated, their ORDER within one operation
  is not spec text. Machine: slice-expression bounds checked HIGH then
  LOW (`checkSliceBounds`/`checkSliceBounds3` Ops.lean:211–244,
  "the runtime's exact messages and check ORDER (oracle-pinned)");
  map-key hashability walk stops at the first offending component in
  gc's own hashing order (Ops.lean:1697–1721); interface-assert panic
  names the first unmet method in name-sorted order
  (Ops.lean:791–810).
- Observable as which panic message appears. Plausible envelope: any
  check order. PERMANENT-pin candidate alongside R9 (message identity
  is already gc-pinned; an order envelope without a message envelope
  buys nothing).

---

### E12. Binary-operator operand order: calls vs non-call operand events — (b) PINNED, structural (frontend ANF): call-first; left-to-right among non-calls

Added 2026-08-17 at spec-truth P2, closing prior-art finding F1
(`docs/2026-08-17_prior-art-ch2o-cerberus.md` §3: the census hole at
the center of CH2O's redex-selection latitude; E11-adjacent — E11 is
check order *within* one operation, this is order *across* the operand
subexpressions of one binary operator).

- WHERE: spec#Order_of_evaluation, two distinct grounds (split per
  the P2 audit): (i) QUOTE-grounded — "the order of those events
  compared to the evaluation and indexing of x and the evaluation of
  y ... is not specified, except as required lexically": non-call
  operand events carry latitude relative to the CALLS; (ii)
  OMISSION-grounded — the left-to-right rule's scope is calls/method
  calls/receives/binary-logical only, so non-call-vs-non-call operand
  order is latitude by silence (the absence is the anchor, as at
  C1/C5). Machine realization point: the frontend's A-normal-form pass
  (tools/nativefrontend/wire.go:25 — calls and allocations in
  expression position hoist to temps ahead of the expression), after
  which GoCore evaluates the residual call-free operands
  left-to-right. So call-first is a FRONTEND normalization, not a
  GoCore choice site.
- PIN: calls evaluate before the non-call operand events of the same
  binary expression even when the non-call operand is lexically LEFT
  (gc probe: `a[i] + f()` with `f` mutating `i` returns a VALUE — the
  call ran before the left operand's index read — where the
  naive all-operands-left-to-right reading panics `[8]` — a reading
  the spec does NOT mandate, which is the point); among non-call
  operand events, left before right (both-out-of-range probe panics on
  the LEFT index; audit swap-probe `a[9]/b[8]` panics `[9]`, so it is
  positional, not magnitude). Probed at the go1.26.5 pin, identical
  under `-gcflags=all='-N -l'`. Plausible envelope (precision per the
  P2 audit — the too-wide direction has no oracle): any relative
  order of the non-call operand events and the calls' effects,
  SUBJECT to the spec's hard constraints — calls/receives/
  binary-logical stay lexically ordered among themselves, and a
  call's arguments are evaluated before the call ("g cannot be called
  before its arguments are evaluated"). Whether the residue is an
  either-order or an interleaving claim is the F2 sentence owed
  alongside E2–E5.
- EVIDENCE: GC — corpus guardrails
  `binop-order/operand-panic-vs-call/{left-first,call-before-left,call-before-left-div}`
  (pure observables: the call mutates the state the left operand
  reads, so call-first yields a defined value and operand-first
  panics; no printing needed). All three PASS: the machine's
  realization matches gc's. XIMPL/ARCH would bear on whether any
  implementation realizes operand-first (none known; same open
  question as E2).
- RE-ENVELOPE OBLIGATION + COST: rides E2's re-envelope (same
  call-first family; the membership/panic-identity treatment that §7
  item 5 lists — with F3's cost note arguing for it — covers this
  entry's observables too). Until E2 opens, no new machine arms;
  widening then requires either frontend order-variants or a GoCore
  operand-order choice site. MODERATE, sequential-only observable.
  RECORDED CENSUS FOLLOW-ONS (P2 audit): the same spec section names
  further unspecified orders not yet censused — composite-literal
  element order vs a call among the elements (`[]int{a, f()}`),
  duplicate-map-key evaluation order, and map-literal key-vs-value
  order; E12 covers binary operators only.

### E13. Non-call panicking operations (type assertion, indexing) vs SIBLING calls — (b) PINNED, structural (the same frontend ANF hoist): calls first

Added 2026-08-20 from the grossmith campaign-2 record
(`docs/2026-08-20_grossmith-findings-2.md` §4, case `case_16162`, seed
4016162; F-3 of that document's owed follow-ups). E12's sibling on the
same spec ground, one level up: E12 is the order of the operand events
of ONE binary operator against the calls in it; this entry is the order
of a non-call operation's PANIC against calls that are its lexical
SIBLINGS — other elements of the same RHS list, or other arguments of
the same call.

- WHERE: spec#Order_of_evaluation, OMISSION-grounded (the absence is
  the anchor, as at C1/C5/E12(ii)): the left-to-right rule's scope is
  "function calls, method calls, receive operations, and binary logical
  operations" — a **type assertion** is none of these, and neither is
  an **index expression**. The "except as required lexically" clause
  does not reach a sibling: it forces a non-call operation only when
  that operation is an ARGUMENT of a lexically earlier call ("g cannot
  be called before its arguments are evaluated"). **That distinction is
  the whole entry**, and getting it wrong in the other direction is a
  BUG, not latitude: the argument position IS forced, which is exactly
  the forced point BUG-062 is open on (findings §1 — built-in call
  arguments; §1.4's `user-arg-index` and `b3-append-arg-index` probes
  are the machine getting the forced side right). Machine realization
  point: no GoCore choice site — the frontend's A-normal-form pass
  (`tools/nativefrontend/wire.go:25`, the same pass E12 names) hoists
  the sibling calls to temps ahead of the expression, leaving the
  assertion's type check and the index's bounds check in place, so the
  calls run first.
- PIN: a sibling call's effects land BEFORE a type assertion's failure
  panic and before an index expression's bounds panic. Plausible
  envelope: any relative order of the non-call operation's panic and
  the sibling calls' effects, SUBJECT to the spec's hard constraints
  (calls/receives/binary-logical stay lexically ordered among
  themselves; a call's own arguments precede it). Reading: **UNSEQ**,
  not merely either-order — `docs/spec-interpretations.md` **I-2**,
  backed by ledger `L-013`; the F2 sentence E12 leaves owed is answered
  for this entry by that adopted reading.
- EVIDENCE: GC — and unusually, the two axes fall on OPPOSITE sides,
  which is the cleanest possible demonstration that the point is
  latitude rather than a machine defect on one of them:

  | probe | shape | gc | machine | source |
  |---|---|---|---|---|
  | `d1-assert-vs-call` | `iv.(T0), w(max(w(1,4), w(59,5)), 6)` | 0 (assertion panics first) | 4005 (all three `w` calls ran) | findings §4 |
  | `d2-assert-as-call-arg` | `sink(iv.(T0), w(7,9))` | 0 | 9 | findings §4 |
  | `bare-index` | `s[i], wit()` | 9 | 9 | findings §1.4 |

  `4005 = ((0*31+4)*31+5)*31+6`, i.e. the machine ran the whole `w`
  chain before the assertion panicked. On the **assertion** axis gc
  realizes the other member; on the **indexing** axis gc happens to
  realize ours. gc is SELF-STABLE on the assertion axis (default flags
  and `-gcflags=all='-N -l'` agree), so this is latitude in the spec,
  not instability in gc — the contrast with E3, where gc's realization
  is compiler-internal and hence unpinnable, is worth keeping. XIMPL
  would bear on whether any implementation orders these; none known.

  MIN/MAX EVIDENCE (audit fix round 2026-09-01, probes a6p/a6q —
  gc @ go1.26.5, machine re-run at the fix tip; `b`/`b2` are slices
  whose lengths make the two index panics' messages distinct where it
  matters, `wit4` is an effectful ordered call):

  | probe | shape (panicky-left x min/max) | gc | machine |
  |---|---|---|---|
  | a6p-p1 | `iv.(int) + min(b[j],1) + wit4(5)` | interface conversion (assert first) | index `[3]`/len 0 (min's arg first) |
  | a6q-q5 | `iv.(int) + min(*p,1) + wit4(5)` | interface conversion | nil deref |
  | a6q-q6 | `iv.(int) + min(*p,1) + <-ch` | interface conversion | nil deref |
  | a6q-q1 | `b2[k] + max(b[j],1) + wit4(5)` | index `[3]`/len 0 (max's arg first) | index `[3]`/len 0 |
  | a6p-p3 | `(7/d)*0 + min(b[j],1) + wit4(5)` | index `[3]`/len 0 (min's arg first) | index `[3]`/len 0 |
  | a6p-p5 | `b2[k] + min(*p,1) + wit4(5)` | nil deref (min's arg first) | nil deref |

  [AGENT] MEMBERSHIP: **min/max join the ANF call-first hoist family
  (E12/E13).** The frontend hoists min/max like calls (they are
  excluded from the A6 len/cap inline treatment — runtimeOrderedCall's
  len/cap/min/max carve-out is about ORDERED-EVENT status, not about
  their own emission), and gc's realizations land EXACTLY on this
  family's existing pattern: gc runs min/max ARGUMENTS ahead of a
  lexically-left index/division panic (q1/p3/p5 — machine agrees) and
  realizes a lexically-left ASSERTION panic first (p1/q5/q6 — machine
  realizes the arg's panic; opposite members, both conforming — the
  same assertion-vs-indexing split as the d1/bare-index rows above).
  This AFFIRMS the E12/E13 reading that BUG-062's status already
  takes; the assert-axis divergences are census'd HERE, not open
  bugs, and the NO-PIN rule of this entry covers the min/max axes
  identically (a strict pin on the assert axis would record latitude
  as a fidelity failure).
- NO PIN MAY BE TAKEN HERE. Deliberately **not** a corpus case, and no
  strict-lane row may pin either axis: the machine and gc realize
  different members on the assertion axis, so a strict pin would record
  a divergence as a fidelity failure, and a pin on the indexing axis
  would freeze an agreement that the spec does not require. This is a
  census row, nothing more. (Campaign disposition, findings §4:
  "an inventory entry, not a fix".) The generator-side observation that
  a STRICT-lane outcome-determinism claim can land on a point like this
  is grossmith's, handed back as F-5 — external, no patch.
- RE-ENVELOPE OBLIGATION + COST: rides E2/E12's family — the same
  panic-identity membership treatment §7 item 5 queues (admit any of
  the candidate panics) covers this entry's observable, since the only
  thing visible here is WHICH panic wins and what ran before it. Until
  E2 opens, no new machine arms. MODERATE, sequential-only observable.
  Census follow-on, in E12's spirit: the same reasoning applies to
  every other non-call panicking operation in operand position
  (division by zero, slice-to-array conversion, nil-map write, nil
  dereference) against sibling calls — not separately probed, and NOT
  claimed by this entry.

## 3. Representation, runtime, and library realization

### E14. Method-call RECEIVER operand vs the arguments — (c) census row, nothing more

Added 2026-08-22 (launch audit D8 — "receiver" appeared nowhere in
this inventory while the frontend realizes a point on the axis). The
frontend pins the receiver operand's events AHEAD of the argument
events (`tools/nativefrontend/emit.go`, the method-call path:
`all := append([]any{recvArg}, args...)` — the receiver joins the
ordered-event prefix). Whether spec#Order_of_evaluation's
left-to-right function-call/operand sentence FORCES this (the
receiver as the leftmost operand of the method value) or leaves
latitude among receiver-vs-argument sub-events at panic sites is the
same F2-class question as E12/E13 and is OWED with them. gc agrees
with the realized point on every probed shape (the W4/W7 fmt work
rode it); no divergence is known. NO PIN MAY BE TAKEN HERE (the
frontend's structural realization stands as scaffolding, not as a
pin) — this is a census
row so the axis stops being invisible, nothing more.

### R1. `int`/`uint` width — (b) PINNED to 64 bits

- WHERE: spec §Numeric types: `uint`/`int` are "implementation-specific
  sizes" — "either 32 or 64 bits". Machine: `IntKind.bits?`
  Value.lean:47–48 (`.int => some 64`, `.uint => some 64`);
  `IntKind.normalize` wraps at the fixed width. Recorded only in
  docs/semantics.md:199 as an "executable testing policy" with the
  stated intent that width become an explicit parameter — the record
  PREDATES the envelope doctrine; the owed site-level caveat in
  Value.lean (§9, flag 2 — owed since 2026-08-11) was ADDED
  2026-08-31 at `IntKind.bits?` (fidelity fix round).
- Also entangled: which programs COMPILE (constant overflow at int
  boundaries — the negative lane inherits the pin via go/types on the
  host), and `uintptr` (frontend maps to uint64; observations of it
  refused).
- PLAUSIBLE ENVELOPE: {32, 64} as a machine parameter.
- EVIDENCE: GC (amd64 = 64-bit only). XIMPL is the evidence class that
  BEARS here more than anywhere sequential: a 32-bit gc / tinygo lane
  would exercise the other point.
- RE-ENVELOPE OBLIGATION + COST: parameterize width (IntKind.bits?,
  normalize, conversions, the frontend's go/types Sizes config, the
  negative lane's acceptance) — PERVASIVE but mechanical; blocked in
  practice on having any 32-bit oracle to differentiate against.
  MODERATE-HIGH cost, LOW urgency until a cross-implementation lane
  exists.

### R2. Append spill capacity — (a) ENVELOPED (a declared pragmatic subset)

- WHERE: spec §Appending: append "allocates a new, sufficiently large
  underlying array" — ANY capacity ≥ newLen conforms (unbounded
  latitude). Machine: envelope [newLen, max(32, 2·growth)]
  (`appendSpillUpper` Ops.lean:1944–1972 with the containment argument;
  consumption Machine.lean:954–970, empty stream = the gc
  growth-formula point).
- NOT maximal, deliberately: the plausible upper bound is unbounded;
  the envelope is a PRAGMATIC SUBSET believed ⊇ gc across probed
  regimes (BUG-021's widening: stack buffer, size-class rounding,
  below-formula), version-tracked by the three escaping-regime
  membership pins + the formula point. "Widen deliberately if a
  toolchain leaves the window; never narrow to one compiler mode."
- EVIDENCE: GC probe sweep over element sizes (go1.26.5); the -race
  allocator lands on other members (cap-zero → 1) — live validation.
  XIMPL (gccgo/tinygo allocators) would stress the upper end.

### R3. `[]byte(s)` conversion capacity — (b-n) PINNED singleton, **gc known outside** (escaping path)

- WHERE: spec §Conversions: "The capacity of the resulting slice is
  implementation-specific and may be larger than the slice length."
  Machine: SINGLETON cap = len, no consumption, transfer caveat at the
  arm (Machine.lean:340–356): gc's ESCAPING path realizes
  roundupsize(len) — outside the singleton.
- This is the same class as pre-widening BUG-021 (a real behavior
  outside the model), currently guarded only by the caveat: a theorem
  asserting cap = len does not transfer where the conversion escapes,
  and a corpus case observing cap of an escaping conversion would go
  red.
- RE-ENVELOPE OBLIGATION + COST: the append-spill mold — envelope
  [len, roundupsize-style upper], one arm + width metadata + a
  membership pin for the escaping regime. LOW cost; ranked high on
  value-per-cost (§7).
- RUNE ARM (2026-08-19, bugfix-arc 19-red slice): `[]rune(s)` now
  EXISTS (`runesFromString`, triage L1) and shares the singleton
  cap = len — with a WIDER caveat: gc is outside the singleton even on
  the small non-escaping shape (probe go1.26.5: `cap([]rune("héllo"))`
  = 32, the runtime's 32-rune conversion buffer; the escaping path
  roundups like bytes). So the rune direction has NO agreeing
  version-tracking pin (a cap-observing case was measured red and
  deliberately not added — this entry is the record instead); the
  re-envelope obligation above covers both arms.

### R4. Float fusion + extra intermediate precision — (b-n) NARROWED to per-op rounding (platform-scoped singleton)

- WHERE: spec §Floating-point operators (verbatim in floats design §3.1
  and the FloatBits.lean:31–49 module envelope statement): "An
  implementation may combine multiple floating-point operations into a
  single fused operation, possibly across statements..."; plus the
  float32 extra-precision sentence. Machine: every op rounds to the
  operand type, no fusion, no extra precision (FloatBits kernel).
- Matches the oracle platform exactly (gc linux/amd64 GOAMD64=v1 emits
  no FMA); gc/arm64 and amd64-v3 executions of fusable shapes are
  OUTSIDE the envelope — stated transfer scope. Tripwire:
  floats/fma-shape (goes red if the oracle platform ever fuses).
  The recorded reason a Choices site is wrong-shaped here: the choice
  space is whole-DAG rewritings, not a per-op coin.
- RE-ENVELOPE: per-site fused/unfused choice at frontend-identified
  fusable shapes — HIGH cost, zero corpus benefit today; revisit only
  when a supported target requires it (the record already binds this).

### R5. Float division by zero: panic or not — (b-n) NARROWED to no-panic

- WHERE: spec: "whether a run-time panic occurs is
  implementation-specific." Machine: IEEE ±Inf/NaN, never a panic; the
  float arm dispatches before the integer zero check
  (Machine.lean:297–304).
- gc never panics (pinned by floats/division-specials); no known
  conforming-but-panicking implementation. XIMPL/ARCH would close the
  question; PERMANENT-record candidate otherwise.

### R6. Out-of-range float→int conversion — REFUSED (declared latitude resolved by failing closed)

- WHERE: spec: "the conversion succeeds but the result value is
  implementation-dependent." Machine: explicit
  `.unsupported "float-to-int conversion out of range/NaN
  (implementation-dependent in Go)"` (Ops.lean:1140–1150). Really does
  diverge across gc targets (amd64 0x8000...0; arm64 saturates).
- The honest resolution for an unoracleable point; re-envelope would be
  a value envelope {amd64 point, saturation, ...} — only worth it if a
  target program does this deliberately.

### R7. NaN bit patterns produced by the machine — (b-n) NARROWED to the canonical quiet NaN; unobservable in-language

- FloatBits.lean:68–72. Go the language cannot observe NaN payloads
  (math.Float64bits is out of scope); becomes latitude-relevant only if
  math lands. Float min/max builtins LANDED (2026-08-19, 19-red slice
  family 3 = triage L3): the IEEE fold over `floatMinMaxBits`
  (spec#Min_and_max's special-case table — NaN propagates,
  min(-0,+0) = -0), validated by the three
  spec-examples-stmt/min-max-float-specials pins, now PASS. The one
  NaN-adjacent narrowing: a NaN result carries the NaN OPERAND's bits
  (payload unobservable in-language — this entry's own scope
  condition).
- CLASS, first assigned 2026-08-22 (settlement branch,
  `reconcile-records` C10): this heading carried NO class tag from the
  inventory's founding commit `b44fb7b0` until now, and R7 appears in
  no §10 enumeration — so this is a FIRST classification, not the
  re-derivation of a prior decision, and it is recorded as such so an
  auditor can overturn it cheaply. Read taken: **(b-n)**, on the
  entry's own words — IEEE-754 admits many NaN payloads, the machine
  resolves to one (a deliberate proper subset) and records a transfer
  caveat ("this entry's own scope condition"), which is the legend's
  definition of (b-n); R13 ("declared-unobservable narrowing") is the
  established precedent for the same shape and is counted (b-n).
  **The two rejected readings, recorded rather than buried:** plain
  **(b)** — defensible, since the heading's own verb is "pinned" and
  (b-n) ⊂ (b), so nothing downstream changes if an auditor prefers it;
  and **(q)** — the shape genuinely matches (one canonical
  representative, alternatives unobservable through the modeled
  surface), but (q) requires a THEOREM discharging the re-envelope
  obligation and R7 has only a scope ARGUMENT ("math.Float64bits is
  out of scope"), so claiming (q) would claim a discharge that does
  not exist. If `math` lands, re-decide: a new observation channel is
  exactly what (q) is conditional on.

### R8. WaitGroup counter representation — (b) PINNED to gc's bit layout

- WHERE: DOCS — sync docs say only "panics if the counter goes
  negative"; nothing about width/wrap. gc keeps the counter in the high
  32 bits of a uint64 and WRAPS before the negative test
  (waitgroup.go:104/109). Machine: counter' = ((counter + delta + 2^31)
  emod 2^32) − 2^31 at the `wgAdd` arm (BUG-055; divergent in BOTH
  directions pre-fix).
- Plausible envelope: any counter semantics consistent with the doc
  sentence (unbounded, 32-bit wrap, 64-bit...). PERMANENT-pin
  candidate: the doc text underdetermines behavior only at misuse-scale
  deltas (≥ 2^31); XIMPL would bear. Related recorded narrowing: the
  waiter-side reuse panic (sync design §8) — gc's Add-side window is
  clean (probed 10/10), our resume-time model matches post-fix.

### R9. Run-time panic VALUES and message texts — (b) PINNED to gc's realized strings

- WHERE: spec §Run-time panics: "The exact error values that represent
  distinct run-time error conditions are unspecified." Machine:
  gc-exact texts everywhere — index/slice-bounds messages
  (Ops.lean:130–244), map-key hash panic's two phrasings
  (Ops.lean:1724–1734), make chan/map/slice negative-size strings
  (Machine.lean:785–822, probe p21), channel op panics
  ("send on closed channel" etc., Machine.lean:2359–2417, probes
  p01–p03), nil-payload `*runtime.PanicNilError` (Machine.lean:1499–1514 —
  oracle aligned with GODEBUG=panicnil=0), `$runtime.Error` box for
  runtime panics vs plain-string box for sync package panics (the
  BUG-054 class distinction — observable via recover().(string)).
- Plausible envelope: any values satisfying "runtime.Error implementing
  error". The pin is what makes the equality lane possible;
  PERMANENT-pin candidate with the caveat that claims about panic
  MESSAGE content never transfer beyond gc. XIMPL (gccgo texts differ)
  is the evidence class that would size the real envelope if ever
  needed.

### R10. Abort-line rendering (unrecovered panic output) — (b) PINNED to gc's `preprintpanics` behavior, fail-closed at its unmodelable edges

- WHERE: not spec at all — pure gc runtime realization (the spec does
  not define abort output). Machine: `renderPanicHead`/
  `renderPanicPayload` (Machine.lean:1607/:1564) render gc's exact
  shapes and FAIL CLOSED where the machine cannot decide gc's answer:
  eface identity for `[recovered]` collapse (needs allocation identity
  — unmodeled), Error()/String() rewrite (needs a method call at abort
  time), multi-line/non-ASCII payloads (BUG-004 items 1/3/4, open with
  red pins).
- The fail-closed edges are the honest form; the re-envelope obligation
  is really BUG-004's fix list (allocation identity being the deep
  one — see C11).

### R11. Sync misuse fatal class — (b) PINNED to gc's throw realization

- WHERE: DOCS — "It is a run-time error if m is not locked on entry to
  Unlock" underdetermines the CLASS; gc realizes an unrecoverable
  runtime throw (`fatal error: sync: unlock of unlocked mutex`, exit 2,
  recover does NOT catch — probes p01–p03). Machine: `GoError.fatal`
  with gc's fixed strings; recorded narrowing: the fatal observation
  carries the fatal alone, dropping gc's pending-panic line when raised
  during unwinding (sync design §8). go-of-nil-func fatal MIGRATED to
  the class (2026-08-19, 19-red slice family 6 = triage L10:
  `GoError.fatal "go of nil func value"` at the spawn arm;
  spawn-edge/nil-func-fatal now a GREEN pin at expected_status fatal —
  the old red pin's "the class is unmodeled" reason expired when the
  class landed at spec-parity slice 2, two days after the pin).
- Plausible envelope: {recoverable panic, unrecoverable fatal} — a
  historical gc change class (ARCH would bear: pre-1.8 realizations
  differed). PERMANENT-pin candidate at gc's current point,
  version-tracked by the fatal cases.

### R12. Exit codes and terminal classification — (b) PINNED at the harness boundary

Exit 2 for panic/deadlock/fatal, exit 66 for -race — gc realizations
the differential HARNESS keys on (`expected_status` dispatch,
scripts/diff-coverage); the spec says nothing about exit codes. Rides
with R9/R11; no machine content beyond the terminal classes themselves.

### R13. Sort stability in `sortSlice` — (b-n) NARROWED, declared-unobservable

Syntax.lean:264–269 / Ops.lean:2042–2062: insertion sort, "exact for
integers, where Go's instability is unobservable" (sort.Slice is
documented NOT stable — DOCS latitude — but equal ints are
indistinguishable). Becomes real latitude the day non-integer sorts
land; the declared-unobservable argument is scoped to int kinds at the
site.

**The `slices.SortFunc` shim carries the SAME tie-order latitude**
(added 2026-08-22, launch audit V2 — previously recorded only in Go
comments, `tools/nativefrontend/genericshim.go:21-24` and
`stdlibshim.go:113-117`): the injected insertion sort realizes ONE
member of the unstable-sort envelope for comparator sorts, where ties
ARE observable (distinct structs comparing equal). Declared latitude,
comparator lane; relocating `slices.Sort` onto the shim (the parked
D8-F1 arc) relabels this row rather than retiring it.

### R14. Constant arithmetic precision — (d) UNKNOWN (delegated)

Spec §Constants gives minimum implementation requirements (at least 256
bits of integer precision etc.) and allows more; "Implementations may
round if unable to represent". The frontend delegates all constant
evaluation to go/types (exact where the oracle's own frontend is
exact), so machine and oracle share one realization — but whether any
acceptance-relevant latitude survives at the extremes (a conforming
implementation REJECTING constants go/types accepts, or rounding where
it doesn't) has not been analyzed. Negative-lane relevance only; no
runtime observable. OPEN QUESTION as stated.

### R15. Zero-size variable address identity — (b) PINNED never-same; gc probed NON-single-valued (added 2026-08-19, audit fix round F1)

- WHERE: spec#Size_and_alignment_guarantees — "Two distinct zero-size
  variables may have the same address in memory." — and
  spec#Comparison_operators — "Pointers to distinct zero-size
  variables may or may not be equal." (both verbatim at the
  `deps/go` pin). The observable is plain pointer equality:
  in-language, no unsafe/reflect needed — which is why the coverage
  ledger's Size_and_alignment_guarantees row can NOT claim int/uint
  width as the section's only in-language-observable consequence
  (that claim stood until this row; the ledger row is corrected in
  the same commit).
- MACHINE: every variable gets a fresh cell (`Loc` identity), so the
  machine is the deterministic NEVER-SAME member of the two-member
  envelope, on every shape. A conforming member — but a singleton.
- EVIDENCE gc IS non-single-valued (go1.26.5 probe,
  artifacts/probe/zerosize, scratch): two non-escaping stack
  zero-size variables compare DISTINCT (0); two escaping ones both
  land on `runtime.zerobase` and compare EQUAL (1); `new(struct{})`
  twice without escape is stack-shaped (0). Case-pinned both ways:
  `pointers/zero-size-address/stack-distinct` GREEN (member
  agreement, version-tracked) and `pointers/zero-size-address/
  escaped-same` RED differential (machine 0 vs gc 1 — observed ∉
  modeled-singleton at a latitude point; the init/hidden-dep-order
  class, disposition `latitude` in baselines/untriaged-ids).
- RE-ENVELOPE obligation (formerly W3.2; re-homed 2026-08-31 —
  [AGENT] extension of fidelity decision 6's orphan class; R15 fits
  the class, confirmed [USER] 2026-09-01 → this repo's TODO.md
  backlog): a may-equal
  choice at zero-size
  address creation (or a membership-lane row admitting {0,1}) turns
  the deviation record into an inclusion check. Until then the red is
  the honest version-tracked pin, never a fidelity bug.

---

## 4. Forced points — the compact list (class (c))

For completeness, the main spec-mandated points the machine implements
deterministically and correctly-by-obligation (any divergence here is a
plain bug, several were — see BUGS.md): E1's ordered-evaluation core;
channel buffer FIFO; select default-when-none-ready (consuming nothing
— Machine.lean:2694–2700); nil-channel never-ready (Multi.lean:166–168);
receive-communication-before-target-evaluation (§Assignments via
BUG-022/029); the assignment PHASE BOUNDARY — no store before every
operand is evaluated (§Assignments' two-phase sentence; E5, ruled
FORCED 2026-09-02 with gc's early store recorded as deviation L-016;
BUG-075 the return-side instance, fixed); defers LIFO; per-iteration loop variables (Go 1.22,
BUG-003 fixed); range-over-slice/array/string/integer order; string
semantics as bytes with U+FFFD decoding; IEEE-754 arithmetic per op
(within R4's narrowing); two's-complement wrap at fixed widths; map
NaN keys inserting distinct entries (falls out of `valueEq` — floats
design §4); function values comparable only to nil; interface
comparison panics on uncomparable dynamic types; init dependency order
for hidden-dep-free programs (the spec's stepwise rule, via go/types);
`init()` functions in source order; main's return not waiting for other
goroutines (the exit itself — C4 is the latitude around it); goroutine
exit having no HB edge.

## 5. Refusals standing in for latitude (inventory of fail-closed resolutions)

R6 (float→int out-of-range), E6 (len/cap hoist shapes),
select-with-select
rendezvous (Multi.lean:804/:813), racy programs (C10 — by doctrine),
uintptr observations, `go` during `$pkginit` (StepFn.lean:511–525).
Each is honest (visible red, never a wrong answer); none is a fidelity
achievement.

## 6. Unknowns — suspected latitude, not yet analyzed (class (d))

- **U-1 Mid-program fused-boundary members** (C3) — PROBED, then
  ADMITTED (W3.2 slice 1: probe at phase A, admission at stage C).
  The owed directed probe ran (wake partner, then panic in the
  issuer's private segment): gc's DOMINANT member is partner progress
  between the wake and the abort — main prints "42" and the program
  still aborts (189/200 phase A; 60/200 at the stage-C rerun; exit-0
  0/200 both) — and the pre-B1 machine excluded that class on every
  stream (127/127 panic, no output, mod-2 depth-6 sweep). B1's
  `.opDone` post-op boundary admits it: the machine's certified set
  is now {panic, ok 42} (corpus row goroutines/wake-then-abort,
  members=2 statuses=ok+panic; record
  `docs/evidence/2026-08-20_w32-postop-probes/`). Residual, recorded
  at C3: B3's window is post-`.panicked` progress (NOT post-raise,
  which B1 models — wording corrected 2026-08-31 with the probe
  evidence at `docs/evidence/2026-08-31-b3-abort-window-probes/`:
  56 directed runs, zero exhibitions; residual argued from the
  runtime's freeze-is-best-effort text — see C3). No longer a (d)
  unknown.
- **U-2 L4 ⊆ L1-reachability**: the envelope-width review's [ANALYSIS]
  that every width>1 L4 member is also realizable by arrival timing has
  no theorem and no counterexample search beyond the probed shapes.
- **U-3 Constant precision extremes** (R14).
- **U-4 Overlapping copy/append aliasing coverage**: `copy` with
  overlapping src/dst is spec-defined ("as if" intermediate) — FORCED —
  but the differential coverage validating our multi-cell one-step
  arms against it is recorded as owed (TODO; granularity-ledger R4
  re-audit covers the concurrency side of the same arms).
- **U-5 Wide-op granularity under concurrency**: `appendSlice` spill,
  `copySlice`, `clearSlice`, AND `sortSlice` are single apply steps
  (Machine.lean:66–69, 741–751; `sortSlice`'s arm — the COARSEST
  member, a whole sort in one step — was omitted from this row until
  the 2026-08-22 launch audit, D8-F1/V2) — coarse-but-recorded; fine
  sequentially; the granularity-ledger re-audit before any concurrency
  claim mentions them is still owed (BUG-002's R4 residue). The
  `sortSlice` case additionally carries an internal inconsistency:
  `slices.Sort([]uint64)` is ONE step while the interchangeable
  `slices.SortFunc(x, cmp.Compare)` lowers to a per-element shim loop
  — two granularities for one Go operation, unobservable while racy
  programs fail closed (C10); resolved by the parked relocation arc
  (synthesis doc, deferred list). Sub-registry granularity
  generally is C2/C3 + NPDRF territory, but these named arms are the
  known coarse spots INSIDE segments.
- **U-6 Future atomics**: mem#atomic pins sync/atomic to SC — verbatim:
  "The preceding definition has the same semantics as C++’s
  sequentially consistent atomics and Java’s volatile variables"
  (quote corrected at the P2 audit) — a considered design commitment
  with recorded rationale (gomm: a conforming implementation may NOT
  weaken these to acquire/release) — forced when modeled;
  the latitude to analyze at that arc is the surrounding-plain-access
  envelope, not the atomics themselves.
- **U-7 gc version drift as an evidence problem**: every pinned
  realized point (R2's formula center, R3, E2, E10, R8, R9, R11) is
  version-tracked at go1.26.x per the CI pin; the inventory assumes the
  version-tracking pins actually fire on toolchain movement — believed
  true (they are membership/eval pins), not re-audited here.

## 7. Priority ranking for re-envelope

Criteria per the doctrine: (i) oracle-visibility risk, (ii)
concurrency-relevance (the charter: concurrency matters most),
(iii) cost. The known first item is fixed by the doctrine.

1. **C2+C3 — forced continuation + fused effect boundary — DONE
   (W3.2 slice 1 stages C/D, 2026-08-20/21; G1 ruling).** The
   doctrine's designated first item, landed as designed: B1's
   `.opDone` post-op boundaries + B2's back-edge boundaries; the
   send-then-spin wedge FLIPPED (gc's exit-0 is a member at stream
   [0,0,1]; corpus row `goroutines/send-then-spin`; register #1
   discharged); the never-yielding streams survive by right and
   registry-free-spinner termination remains FairStream's question,
   exactly as this item scoped. See C2/C3's entries for the paid
   cost and the recorded residuals (B3 abort window deferred at G1;
   enumeration-tractability fallout under BUG-065, awaiting the
   §5c-fallback ruling / the reduction lane).
2. **E9/BUG-005 — live map iteration.** DONE 2026-08-19 (the (L)
   surgery): live-cell candidates, delete-prune, per-pick footprint
   (U1 closed), full literal envelope user-ruled — see E9's entry for
   the residual cross-goroutine-prune narrowing and its obligation.
3. **E7 — hidden-dep init order.** Oracle-red today (standing
   deviation record), the only pin KNOWN to sit beside the oracle's
   realization on the SEQUENTIAL side, soundness-direction
   (no-transfer), and UNGUARDED — the interim frontend detector
   (fail closed on the hidden-dep shape) is LOW cost and converts a
   silent class into a visible one; the full envelope can wait.
4. **R3 — `[]byte(s)` capacity singleton.** gc KNOWN outside on the
   escaping path (the record's own caveat) — the same too-narrow class
   BUG-021 was, unwidened; cheap (append-spill mold, one arm + one
   membership pin). Best value-per-cost in the queue.
5. **E3/E4 — the unordered-panic-selection axes.** Deterministic
   divergences from gc recorded and probed (unpinnable
   compiler-internal realization); needs the membership/panic-identity
   envelope treatment or linearization. Sequential-only,
   moderate cost — above R1/R4-class pins because it is
   oracle-visible in panic-selection shapes today. **E5 LEFT this
   item 2026-09-02** ([USER] ruling): its re-envelope obligation is
   WITHDRAWN — the phase boundary is FORCED and gc's early store a
   deviation (L-016); widening toward it would take the machine past
   the spec.

Below the line (recorded, deliberately not queued): R1 int width
(waits on any 32-bit oracle lane — XIMPL evidence class), C7 select
wake-path narrowing (coverage argument stands; re-argue on wake-path
changes), R2's upper end and R4/R5 float narrowings (tripwired /
platform-scoped), E10/E11/R8/R9/R10/R11 permanent-pin candidates
(record-and-caveat, widening buys no verification value while the
oracle is gc), C9 deadlock-as-terminal (observationally coincident),
E8 multi-file order (the frontend and the harness are both scoped to
the go command's DIRECTORY-mode member; the other members are the go
command's own FILE-LIST mode — §E8's corrected premise — and the
revisit trigger is a consumer feeding the frontend a file-list-mode
build, not a non-go-command build system, which was the stale
premise this line carried until the 2026-09-01 audit fix round).

## 8. THE REGISTER EXTENSION — entries beyond the doctrine's seeded five

In the register's format (what is assumed, why, what removing it
costs). Numbering continues the doctrine draft's 1–5. CITATION RULE
(2026-08-31, fidelity A1-45): the doctrine register itself later grew
entries 6–7 (allocator quotient; unbounded memory), so a bare
"#6"/"#7" is ambiguous across the two documents — qualify every
cross-reference: "extension #6 (int width)" / "extension #7
(library-doc-silent pins)" for THIS list (short form "§8 e6"…"§8
e13"), "register #6 (allocator quotient)" / "register #7 (unbounded
memory)" for the doctrine's.

6. **`int`/`uint`/`uintptr` are 64-bit.** The spec makes the width
   implementation-specific (32 or 64); the machine, frontend, and
   negative lane all realize the oracle host's 64. Why: one concrete
   width keeps normalization/conversions executable and matches the
   only oracle we have. Removing: parameterize width across
   Value.lean/conversions/frontend Sizes/negative-lane acceptance —
   pervasive but mechanical, and worthless until a 32-bit oracle lane
   (cross-implementation evidence) exists. (semantics.md:199 records
   the policy; site-level caveat at `IntKind.bits?` ADDED 2026-08-31 —
   the owed record discharged, §9 flag 2.)
7. **Library-doc-silent behaviors are modeled at gc's realized point.**
   WaitGroup's int32 wrap-before-negative-test (BUG-055), the sync
   misuse FATAL class and its exact strings (probes p01–p03), the
   dropped pending-panic line on fatals-during-unwinding, map-key
   retention on overwrite (`needkeyupdate`), deadlock detection as a
   terminal with gc's message. Why: the docs underdetermine these and
   gc is the oracle. Removing (per point): small envelopes/membership
   rows; value appears only with cross-implementation evidence — until
   then these are recorded version-tracked pins, not fidelity claims.
8. **Run-time error VALUES, message texts, check orders, and abort
   rendering are gc's.** The spec explicitly leaves the exact error
   values unspecified; the equality lane exists BECAUSE we pin them.
   Abort rendering additionally fails closed at gc's
   allocation-identity and method-call edges (BUG-004) — allocation
   identity itself is unmodeled. Removing: message-identity envelopes
   would dissolve the strict lane's decisive signal for near-zero
   verification value; the honest cost is the standing caveat that no
   message-content claim transfers beyond gc.
9. **The evidence base is one PLATFORM, not just one implementation.**
   Seeded #3 names gc-at-a-pinned-version; the sharper truth is
   linux/amd64 at default GOAMD64 — the float no-fusion singleton and
   the float→int refusal are scoped to it, and gc/arm64 executions of
   fusable shapes are already outside the float envelope (tripwire:
   floats/fma-shape). Removing: platform lanes (arm64 runner) before
   any claim touches fusable float code.
10. **`[]byte(s)` capacity = len although gc's escaping path is KNOWN
    outside.** The one recorded singleton whose escape is already
    probed (roundupsize) rather than merely possible. Why: shipped as a
    singleton before the append-spill widening precedent existed.
    Removing: cheap (the append mold) — queued at priority 4.
11. **Map iteration is snapshot-based.** REMOVED 2026-08-19 — the
    BUG-005 (L) surgery made iteration live (per-pick candidates,
    delete-prune, per-pick read footprint closing U1, created-entry
    latitude enveloped); the obliviousness and wf analyses were
    replayed. Residual: the cross-goroutine delete-prune narrowing
    recorded at E9.
12. **A woken select head-commits; only entry-time selects draw L2.**
    A deliberate wake-path narrowing. RE-ARGUED 2026-09-01 [AGENT]
    (post-B1/B2; the old gc-commit-at-wake argument is SUPERSEDED —
    gc-falsified on the two-clauses-one-channel close wake, where gc
    commits either clause ~half each): coverage now carries on the
    C7 row's two-leg argument — partner wakes are L4
    clause-individual pairings at the arrival intercept; close wakes
    are covered by the always-realizable close-before-entry schedule
    and the entry-time L2 draw (B1's post-op boundary supplies the
    scheduling point). An [ANALYSIS], not a theorem; probe evidence
    `docs/evidence/2026-09-01_c7-close-wake-probe/` (certified {1,2}
    ⊇ gc's realized {1,2}). Removing: a wake-path L2 draw (stream
    shifts, enumerator bounds). Re-argue on wake-machinery, arrival
    intercept, or B1-boundary changes (C7's sharpened triggers).
13. **The race-refusal boundary is TSan's realized edge set, not
    go_mem's minimal relation.** Deviations are quoted at their
    implementation sites and scoped by the U-ledger (U1–U2, U4–U5, plus
    the O1 footprint over-approximation); U5 is deliberately
    memory-model-exact where TSan over-reports. Why: keeps every
    refusal justifiable by the `-race` oracle. Removing: nothing to
    remove — this is the scope statement the racy lane's claims carry;
    the NPDRF obligation (registry-point path set) is its structural
    half, owned by register #5.

**Correction owed to the draft's seeded #2** (flag, not a new entry):
"Sequential evaluation-order latitude is pinned ... to gc's
realization" is accurate only for the call-vs-operand axis (BUG-052).
The inter-target axis is pinned to OUR left-to-right point with gc
KNOWN elsewhere (compiler-internal, unpinnable), and the early-store
axis to the spec-literal point with gc elsewhere — both recorded as
OPEN envelope in BUG-032. Hidden-dep order (E7) is likewise pinned to
go/types' point with gc KNOWN elsewhere. ADOPTED (2026-08-12, audit
fix round): register #2 now carries this correction's substance, with
one deliberate change — "permanent deviation records" is superseded by
"standing deviation records queued for re-envelope", because these
points sit in §7's queue (items 3 and 5) and under the doctrine's bug
definition a probed gc-elsewhere observation is an observed-∉-modeled
candidate, not a divergence to be at peace with. (The record is
permanent; the deviation is not.) **E5 UPDATE (2026-09-02, [USER]
ruling):** the early-store axis is no longer an "OPEN envelope" of any
kind — it is a FORCED point on which gc DEVIATES (L-016); it leaves
§7's queue and the "queued for re-envelope" clause above no longer
applies to it. The gc-elsewhere observation there is not an
observed-∉-modeled candidate but an observed-∉-PERMITTED one — the
ledger's exception channel ("If the standard and gc disagree, that's a
finding!"), not the register's debt queue. E3/E7 (and E13/R3) keep
their queued-debt standing.

## 9. Records-vs-code flags found by the sweep

1. **DISCHARGED 2026-08-22 (launch-audit fix round)** — the stale
   ChanClocks docstring (which sat at Race.lean:620–622, not 588–590
   as this flag previously said — D7 MEDIUM-8) is re-synced in place:
   it now states the ours-STRONGER no-edge deviation with the correct
   attribution (gc's `closechan` DOES raceacquireg parked senders; the
   old "woken `chansend` performs no raceacquire" was true but
   irrelevant) and cites `raceWakeEvent`'s S3 correction. The flag had
   expired silently — Race.lean was touched 5× after "the next
   Race.lean-touching slice" was named as the trigger.
2. **DISCHARGED 2026-08-31 (fidelity fix round)** — the int-width
   pin's site-level record (R1): the policy had lived in semantics.md
   prose only, with no caveat/envelope statement at the site although
   the singleton-narrowing rule (nondeterminism doctrine F8/F15) would
   require one if shipped today. The envelope statement now sits at
   `IntKind.bits?` (Value.lean) — pin, envelope {32,64}, transfer
   caveat, XIMPL gate. (The flag stood 20 days after being recorded
   as owed.)
3. **Doctrine draft seeded #2's "to gc's realization"** — see §8's
   correction paragraph.
4. **The created-entries map narrowing is recorded only inside
   BUG-005's dismissal sentence** — RESOLVED 2026-08-19: the (L)
   surgery lifted the narrowing entirely (created entries are
   enveloped may-produce-or-skip; see E9 and
   `docs/spec-interpretations.md` I-1).
5. **Census agreement (positive finding)**: the doctrine's canonical
   site list (7 at this audit; 8 with stage C's `postOp` — the census
   is the `ChoiceSite` datatype now, exhaustiveness-checked), the
   module docstrings, and the executable consume sites agree exactly; the map-iteration site is the only one that consumes
   even at width 1 (StepFn.lean:616–621 — the doctrine's width>1 phrasing
   describes the pool sites and append's always-consume is width-formed;
   no behavioral consequence, but stream authors should know the
   alignment rule differs per site).
6. **OWED (recorded 2026-09-01, C7-refresh lane [AGENT])** — the
   `resumeThread` docstring (Multi.lean:376–401, "gc … woken select
   commits the case its waking event belongs to, never a fresh
   shuffle" and the per-member prompt-wake coverage sentence) and the
   `applySelect`-adjacent wake note (Machine.lean:2725 region) still
   state C7's SUPERSEDED argument — gc-falsified on the
   two-clauses-one-channel close wake
   (`docs/evidence/2026-09-01_c7-close-wake-probe/`; the argument of
   record is now C7's two-leg version). Two further sites carry the
   same superseded wording (census completed at the audit fix round,
   C3): `Corpus/coverage/exec/goroutines/select-wake-multi/main.go:8-10`
   ("a woken select commits the case its waking event belongs to,
   never a fresh shuffle" — the comment states the falsified GENERAL
   rule; the CASE itself stays valid, its two clauses are on DIFFERENT
   channels, where the wording's conclusion happens to hold) and
   `docs/2026-08-06_channels-arc-design.md:1798` (the same
   committed-by-the-event re-argument inside the slice-4 verdict
   paragraph). The refresh lane was
   docs-and-evidence only by its brief, so the re-sync is owed to the
   next Multi.lean/Machine.lean-touching slice (the corpus-comment and
   design-note sites ride the same owed re-sync) — NAMED here because
   flag 1's lesson is that such triggers expire silently.

## 10. Counts

**Reading rule (adopted 2026-08-22, settlement branch).** Each bullet
below is a MEMBERSHIP list and nothing else: every id it names is a
row whose own `###` heading carries that class tag, and every row
carrying that tag is named. Corrections, movement between classes, and
per-row asides live under "Movement and history" beneath the list.
Why the split: §10 does not merely count, it ENUMERATES, and the
enumerations had accumulated explanatory parentheses naming rows that
had LEFT the class — C2/C3 inside the (b) list and E9 inside the
(b-n) list, all three re-enveloped to (a). A reader (and
`tools/reconcile-records`' C10 check) cannot tell a member from a
mention, so the mentions moved out. Keep it that way: put prose in the
history block, never in a membership line.

- (a) ENVELOPED: 9 sites / 9 entries — C1, C2, C3, C4, C5, C6, C8, E9, R2.
- (b) PINNED: **16 entries** — concurrency: C9; sequential order: E2,
  E3, E4, E7, E10, E11, E12, E13; representation/runtime: R1, R8,
  R9, R10, R11, R12, R15.
- (b-n) NARROWED with recorded caveat: 7 — C7, E8, R3, R4, R5, R7, R13.
- (c) FORCED: the §4 list (machine follows; BUG-005's mandated
  point — removed-before-reached never produced — CLOSED 2026-08-19
  by the (L) surgery's delete-prune); rows carrying the tag: E1, E5
  (since 2026-09-02), E14.
- (d) UNKNOWN: 6 (U-2 … U-7; U-1 probed and admitted at W3.2 stage C, 2026-08-20).
- REFUSED standing in for latitude: 9 (§5).
- Known-≠-oracle deterministic points (the honesty-critical list):
  E3, E5, E7, E13(type-assertion axis; the indexing axis agrees),
  R3(escaping path). Two CLASSES inside one list, stated per row: E3,
  E7, E13, R3 are (b)/(b-n) PINS with gc on another conforming member
  (re-envelope debts, §7); **E5 is a (c) FORCED row on which gc
  DEVIATES** (L-016, [USER] ruling 2026-09-02) — it stays listed
  because the oracle disagrees with the machine there, but the
  disagreement is gc's, not a debt of ours. (E13 added 2026-08-20; the
  C2+C3 send-then-spin wedge LEFT this list 2026-08-21 — W3.2 stages
  C/D re-enveloped it, register #1 discharged; E5's class changed
  2026-09-02.)

### 10.1 Movement and history (NOT membership)

Nothing in this block is a class member by virtue of being named here.

- **(a), the 9 entries.** C6 owns two sites (L2 entry + arrival) and
  C8 rides C1's site, so 9 sites / 9 entries is not a coincidence of
  two different quantities — it is checked. E9 contributes its order
  axis. C3 owns the `postOp` site and C2 the `backEdge` site (W3.2
  stages C/D). Count corrected 2026-08-12; **C3 moved (b)→(a)
  2026-08-20 and C2 (b)→(a) 2026-08-21** — both were still named
  inside the (b) list until 2026-08-22.
- **(b), 17 → 16 (2026-09-02).** **E5 moved (b) → (c)** by [USER]
  ruling: the early store across the assignment phase boundary is a
  FORCED point (spec#Assignment_statements' two-phase sentence), the
  machine holds it, and gc's contrary realization is recorded as a
  DEVIATION (`docs/spec-divergence-ledger.md` L-016), not as the other
  member of a latitude. Its re-envelope obligation is withdrawn (§7
  item 5) and it stays in the known-≠-oracle list above as the one
  entry there whose ≠ is gc's fault. Recording agent [AGENT]; the
  class call is the [USER]'s.
- **(b), 15 → 17.** The "15" was never a count of the rows. It omitted
  **C9** (global deadlock, heading "(b) PINNED to gc's runtime
  detector") outright — the line said "structural: none remaining",
  true of C2/C3 but silently read as if it disposed of the whole
  C-series — and it parenthesised **R12** as "(+R12 harness-level)",
  in the list but outside the total. Both are (b) rows by their own
  headings and both are now counted: 15 + C9 + R12 = 17. Corrected
  2026-08-22 (`reconcile-records` C10; dossier §2 R-5). Earlier
  recount 2026-08-20 (the docs-gcbugs slice) had added E12 (2026-08-17
  P2 retrofit), R15 (2026-08-19 audit fix round) and E13 to a line
  untouched since 2026-08-12.
- **(b-n), 6 → 7.** **R7** (NaN bit patterns) is added — a FIRST
  classification, not a recount: its heading carried no tag from the
  founding commit `b44fb7b0` and it sat in no enumeration. The reading
  and the two rejected alternatives are recorded in the R7 row itself.
  E9's created-entries sub-point was LIFTED to the full envelope
  2026-08-19; its residual is the cross-goroutine delete-prune
  narrowing recorded in E9 — E9 is an **(a)** row and was named in the
  (b-n) list only for that aside.
- **Heading tags completed 2026-08-22.** Three rows carried no class
  tag at all, so their class was readable only from the body — which
  is what let the enumerations drift unnoticed. Assigned from the
  bodies: **C10 → REFUSED** (its own CLASSIFICATION line: "not an
  envelope — a doctrine-decided boundary … fail-closed refusal", and
  §5 already lists "racy programs (C10 — by doctrine)"), **R13 →
  (b-n)** (body: "declared-unobservable narrowing", already counted in
  the (b-n) list), **R7 → (b-n)** (see above). C10 was already inside
  §5's count of 9; adding its heading tag changes no total.
