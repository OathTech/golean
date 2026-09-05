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
`ChoiceSite` datatype + `ChoiceSite.canonicalSlot0` table in
`GoLean/GoCore/State.lean` is the census of record — every consumption
goes through `Choices.consumeAt` with its site tag, so a new site
requires a constructor (exhaustiveness-checked) and this table below is
a reader's mirror, no longer a hand-synced record. **Consumption is
under ONE rule since G-U (2026-09-04): a consult pops the stream iff
its bound is ≥ 2, at every site** — the per-site `SitePolicy.consumeAtOne`
flag (stage A's transcription of the then-current code: `mapIter` alone
popped at width 1) is DELETED; design gate G-U RULED [USER] 2026-09-04
as recommended (relayed by the [AGENT] coordinator —
`docs/2026-09-04_reasoning-surface-plan.md` §5.4; design note
`docs/2026-09-04_c-arc-gu-design.md`). The "Consumed when" column below
is therefore the same rule in every row; a cell says only WHERE the
site's bound can be 1 (a forced pick, no pop):

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
| Map-iteration pick (`mapIter`) | StepFn.lean `.mapIterK` arm | live candidates + conditional stop slot | every iteration with ≥ 2 slots — the LAST mandatory candidate is a bound-1 consult and pops nothing (G-U 2026-09-04; before it this site alone popped at width 1) | first remaining candidate in cell order, stop LAST (columns re-synced 2026-08-22 — the Bound/default cells were still describing the RETIRED snapshot design; launch audit D2-F1) |
| Append spill capacity (`appendSpill`) | Machine.lean:963 | `appendSpillWidth` (Ops.lean:1972) | every spill | gc growth-formula point |
| L2 select pick, entry path (`l2Entry`) | Machine.lean:2819 | ready-clause count | only width > 1 | first ready clause (clause order) |
| L2 select pick, arrival path (`l2Arrival`) | Multi.lean:853 | `.multi` outcome count | only `.multi` | first ready clause |
| L4 waiter pick (`l4Waiter`) | Multi.lean:1039 | matching-candidate count | only width > 1 | lowest (goroutine order, clause order) |
| L1 scheduler pick (`l1Sched`) | Multi.lean:1153 (via `Config.boundarySite`, :1099) | \|runnable\| | only width > 1 | lowest runnable goroutine id |
| L5 main-exit window (`l5ExitWindow`) | Multi.lean:1628 | 2 | main terminal ∧ others runnable | 0 = exit now |
| Post-op boundary pick (`postOp`, W3.2 stage C; C5 2026-09-05) | Multi.lean `stepMulti` (via `Thread.boundarySite`) | \|runnable\| (issuer-first menu, `schedSlots`) | at a goroutine whose `Thread.running` boundary flag is `some .postOp` (set by `Thread.afterStep` at a proceeding registry-op completion), only width > 1 | slot 0 = the ISSUER continues (the pre-widening schedule, literally) |
| Loop back-edge pick (`backEdge`, W3.2 stage D) | Multi.lean:1153 (via `Config.boundarySite`, :1101–1103) | \|runnable\| (current-first menu, `schedSlots` :1123) | at a loop re-entry shape (`.loop`, `.mapIterK`), only width > 1 | slot 0 = the CURRENT goroutine continues |
| Frame-entry panic TEXT pick (`nilValueMethodText`, BUG-087 / R9a, 2026-09-03) | StepFn.lean `enterFrameStep` + `enterFrameDeferPanicking`, Multi.lean `spawnStep` (envelope statement `nilValueMethodText?`, Ops.lean, beside `dynamicDispatch?`'s nil arm) | `nilValueMethodWidth` — 2 on the wrapper family, 1 elsewhere | at a frame entry in the family (value-receiver method dispatched through an interface holding a nil `*T`, target not a promotion wrapper), only width > 1 | slot 0 = the nil-dereference text (the pre-BUG-087 machine's only member) |
| TryLock spurious failure (`tryLock`, Q-TRYLOCK 2026-09-03) | Machine.lean `applySyncOp` (the TRY-head arm; envelope statement at `applyTryLock`) | `tryLockWidth op pre` — 2 at an acquirable cell (`tryAcquire`), 1 at a held one | only width 2 (an acquirable cell; the held cell's bound-1 consult pops nothing — the uniform rule) | slot 0 = ACQUIRE (gc's realized point); slot 1 = the spurious false |
| Unsequenced sibling panic order (`unseqPanic`, E13 option (b), lane e13-b 2026-09-05) | StepFn.lean, the `.panicking chain (.probeK k)` arm (the envelope statement is `Stmt.unseqProbe`'s docstring, Syntax.lean; projection arm in `seqConsumption`, Machine.lean) | 2, constant — and ONLY at a panic that reached an unsequenced-operand probe frame; a probe whose operand yields a value consults nothing | only when a probed operand PANICS at its lexical position ahead of a sibling ordered event (an `a[i] + f()` row whose `a[i]` never panics early pops nothing) | slot 0 = DEFER (the sibling events first; the operand is re-evaluated in the residual — the pre-change machine's only member, gc's for index/deref/division/shift/conversion); slot 1 = RAISE (the operand's panic first — gc's for type assertions, slice expressions, interface comparisons) |

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
  ALL-ops scope; C5 2026-09-05 moved the carrier): every registry-op
  completion that proceeds — chan send/recv/close, sync ops, select
  commits on all three paths, the pairing ISSUER, wakes, and spawn —
  leaves the acting goroutine with its `Thread.running` boundary FLAG
  set, a registry boundary of its own (`Thread`, Multi.lean — the
  envelope statement in situ; the flag is set by ONE rule,
  `Thread.afterStep`; `Thread.atBoundary`; site `ChoiceSite.postOp`,
  slot 0 = issuer-continues so the default stream reproduces the
  pre-widening schedule literally; the spawn's flag is `l1Sched` —
  BUG-040's shipped default bit-for-bit; the flag's only step is its
  clear, a pool step). Before C5 the carrier was the `.opDone`
  completion marker wrapping the successor configuration. A woken
  partner can interleave before the issuer's next private segment on
  an explicit stream.
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
  spurious-failure envelope member — MODELED 2026-09-03 as its own site,
  row C12 below (Q-TRYLOCK; the "zero new sites" of this row's heading
  is about the ACQUISITION-ORDER latitude, which still rides L1).
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

### C12. TryLock / TryRLock spurious failure — (a) ENVELOPED (own site `tryLock`; Q-TRYLOCK, RULED [USER] 2026-08-31, implemented 2026-09-03)

- WHERE: mem#locks, verbatim: "A successful call to l.TryLock (or
  l.TryRLock) is equivalent to a call to l.Lock (or l.RLock). An
  unsuccessful call has no synchronizing effect at all. As far as the
  memory model is concerned, l.TryLock (or l.TryRLock) may be
  considered to be able to return false even when the mutex l is
  unlocked." Spec-DECLARED latitude, not silence: at an acquirable
  cell the return-value envelope is {true, false}. Ruling of record:
  `docs/2026-08-31_qrow-rulings.md` row 5 (envelope pre-ruled
  2026-08-31, per-row confirmed 2026-09-01, own-slice sequencing and
  the twin-pin move 2026-09-03 — all relayed by the [AGENT]
  coordinator, cited there); memo `docs/2026-08-21_w32-qrow-memos.md`
  §5. Machine: `applySyncOp`'s TRY-head arm draws `ChoiceSite.tryLock`
  at `tryLockWidth op pre` (Machine.lean; the envelope statement at
  `applyTryLock`; `tryAcquire` is the one derivation of "acquirable"
  shared by the apply, the width and the accountants).
- ENVELOPE (members, per head, from the pre-step cell): ACQUIRABLE
  (`Mutex.TryLock` on an unlocked cell; `RWMutex.TryRLock` with no
  writer HOLDING — a PENDING writer does not force the failure: audit
  fix round F1, the sync design's R1 made VALUE-observable — gc forces
  false only once the writer has passed `readerCount.Add(-max)`
  (rwmutex.go:152), and a writer merely QUEUED behind `rw.w` (:150)
  leaves gc's TryRLock TRUE (`rwTryRLockQueuedWriter` 40/40 plain at
  GOMAXPROCS 1 and 8); the model's `pendingW` is one flag for both
  phases, so acquirability is `!writer` and the pick is offered in both
  — machine ⊇ gc, an [AGENT] widening in the safe direction, RATIFIED [USER] 2026-09-03 («TryRLock decision sounds fine», relayed by the [AGENT] coordinator); the blocking
  `rlock` keeps R1's exclusion; `RWMutex.TryLock` with no writer and no
  reader — the `wlock` immediate-acquire condition) → width 2: slot 0
  = ACQUIRE (the same state transition as Lock/RLock/write-Lock, the
  same acquire edge), slot 1 = SPURIOUS FAILURE (deliver `false`, no
  state change, no HB edge). HELD → `false` deterministically, bound
  1, NO pop (the uniform rule; at the time the site's `consumeAtOne :=
  false` flag) — a forced failure is not a choice. The empty stream realizes slot 0, so the strict lane's
  uncontended TryLock matches gc. Result-observing rows are MEMBERSHIP
  rows over {acquired, spurious} — a strict pin is impossible (the
  width-2 draw fails strict's stream invariance), and the
  always-succeeds pin is OFF THE MENU PERMANENTLY (the memo's option
  (B); the ruling). Realized point INSIDE the envelope, recorded: gc
  holds `rw.w` for a PENDING writer and so fails a new RWMutex
  `TryLock` in the transient readers-drained window where the machine
  offers the pick — the sync docs say nothing about a pending writer's
  priority over a TryLock.
- ORACLE: gc exhibits ONLY the success member in isolation (`muUncontended`
  true 20/20 at GOMAXPROCS 1 and 8, plain and `-race`;
  `docs/evidence/2026-09-03_q-trylock/`) — the spurious member is
  UNEXHIBITED-BUT-PERMITTED (the membership lane's honest caption:
  "does NOT show unexhibited members are Go-realizable"); gc's own
  realizations of a false-when-momentarily-free are a lost CAS on
  `m.state` under contention (internal/sync/mutex.go:85) and the
  starvation-mode early return (:78), neither isolable as a corpus row.
  Held-state falses are gc-exact (`muLocked`, `rwMatrix`: false 20/20);
  a writer past :152 forces false (`rwTryRLockPendingWriter` 20/20)
  while a writer queued behind `rw.w` does not (`rwTryRLockQueuedWriter`
  TRUE 40/40 plain, 39/40 under `-race` at GOMAXPROCS 8) — both inside
  the widened envelope; per-program the sets coincide ({0, 1} at the
  `rw-tryrlock-pending-writer` row before and after the widening).
- DETECTOR (Race.lean `syncEntryKinds`, the `acquired` flag; TSan's
  realized set ∪ go_mem's kind per gc word, the Q-U4RESIDUAL (A)
  discipline): Mutex TryLock on an unlocked cell → `.atomicWrite
  @state` on BOTH members (the CAS TSan realizes whether it wins or
  loses; recording it on the spurious member is an [AGENT] reading in
  the ruled refusal-permitted direction — gc's lost CAS is that
  member's realization); on a held cell → NOTHING (the plain early
  return in a `noRaceFuncPkgs` package; go_mem gives an unsuccessful
  call no kind — probes `muOverwriteLockedVsFailedTryLock`,
  `muCopyVsFailedTryLock` green 20/20). RWMutex TryRLock/TryLock →
  `.read @w` on EVERY outcome (`race.Read(&rw.w)` precedes
  `race.Disable`; `rwOverwriteVsFailedTryRLock` RACE 20/20) +
  `.atomicRead @readerCount` on success only. HB: the acquire edge on
  SUCCESS only ("no synchronizing effect at all" —
  `muFailedTryLockNoEdge` RACE 20/20; corpus
  `race/negative-sync/failed-trylock-no-edge` RACE-ALL). One gc shape
  is schedule-dependent and pinnable in no lane: an overwrite that
  RESETS a held Mutex beside a TryLock (RACE 10/20 — the reset makes
  the TryLock succeed; probe only, the `wg-overwrite-vs-add-nonzero`
  precedent).
- FAIRNESS / TERMINATION: a TryLock spin loop is runnable forever
  under the spurious member — ∀-stream termination is honestly FALSE;
  such rows ride the membership lane under `nonterm=` accounting with
  NO termination claim (`sync/trylock/spin-until-trylock`, nonterm
  branches counted, members {42}); the `Fair`-quantified class is
  reasoning-side future work TO BE BUILT (proposal §2). Kernel-checked
  ∀-streams certification (`allStreamsOk`, the dedup engine) REFUSES a
  TRY-head apply position outright (`consumesTryLock`, fail closed);
  the CLI enumerator (`stepNeeds`) carries such rows.
- EVIDENCE: GC — 20 probe subjects, 20 runs each (40 for the two F1
  queued-writer shapes), plain and `-race`, GOMAXPROCS 1 and 8
  (`docs/evidence/2026-09-03_q-trylock/probes/`); membership
  certification of 11 width-2 rows (each `enumerated=2 exhibited=1
  unexhibited=1` — gc exhibits one member at the gate budget: the
  success member for the TryLock rows, one ORDER for
  `race/free-sync/rw-tryrlock-acquire`'s {0, 8}); racy/DRF rows
  agree-race / agree-DRF.
- INDIRECTION PRESERVES THE SITE (the Q-SYNCVAL identity principle):
  the statement discard, the hoisted expression value, method values,
  interface dispatch, the promoted receiver and `defer m.TryLock()`
  (the deferred wrapper, result discarded at frame exit — audit fix
  round F2, `sync/trylock/defer-trylock`) all lower through one
  `syncValueOpFor` table to the same `sync-op` node (emit.go), or
  refuse; `sync/promoted-mutex/trylock-expr` and the bodied
  `sync.Mutex.TryLock` stub (the twin pin's one moved entry) are the
  guards.

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

### E2. Call vs. assignment-target operands — (b) PINNED call-first on the VALUE axis, **known ≠ gc** on the EARLY-realized kinds; the PANIC axis (a) ENVELOPED via E13's `unseqPanic` since the e13-b re-audit fix round (2026-09-05)

- FINAL VERIFICATION FIX ROUND (e13-b, 2026-09-05, [AGENT]; R''-1): this
  entry's VALUE axis JOINS §10's known-≠-oracle list — the heading had
  said `known ≠ gc` since the re-audit fix round without a list entry
  (the list is the class; a heading is not). BUG-101's two rows are the
  filed witnesses (reached through E12/E13's shapes); the PANIC axis
  stays enveloped via E13 and is not on the list.
- RE-AUDIT FIX ROUND (e13-b, 2026-09-05, [AGENT]; audit finding R1'-1):
  the heading's former "(b) PINNED to gc (call-first)" was FALSE as a
  statement about gc — gc is call-first only for INDEX-kind target
  operands (`x[i] = f()` reads the post-call `i`, the S1 probes below);
  for a type ASSERTION in the target (`x[iv.(int)] = wit(5)`,
  `m[iv.(string)] = wit(5)`) gc evaluates the operand FIRST (order.go's
  safe-expression rule, exactly E13's split), so on main the machine's
  single call-first member was ≠ gc there (measured: main prints `wit 5`
  then the conversion; gc the conversion alone). spec#Assignment_statements phase
  1 makes the target's index/deref OPERANDS siblings of the RHS's calls
  — unsequenced — so the frontend now PROBES them like every operand
  (design §4 D4; the target's own store check is phase 2 and stays
  unprobed): the PANIC axis is a two-member set with gc's member in it
  (`builtins/e13-sibling-panic-order/{tgt-assert-vs-call,map-tgt-
  assert-vs-call,tgt-assert-vs-len-hoist,tgt-assert-vs-make,compound-
  assert-vs-len,map-key-assert-vs-len,tgt-assert-vs-{min-call,copy-
  call,append,recv-w},compound-index-vs-len,array-base-target-vs-len}`).
  The VALUE axis (`x[i] = f()` with `f` mutating `i`) keeps the
  call-first pin below — DEFER re-evaluates the operand after the call,
  RAISE fires only on an early PANIC — and for an EARLY-realized kind
  whose early evaluation succeeds it is E12/BUG-101's known ≠ gc.
  E3/E4 (inter-target order) are unchanged.

- WHERE: spec#Order_of_evaluation: "the order of those events compared
  to the evaluation and indexing of x and the evaluation of y ... is
  not specified." Machine: the PINNED LATITUDE rule-site block
  Machine.lean:3040–3072 (spec text verbatim, gc realization probed
  go1.26.5, version-tracked; cite re-anchored 2026-08-22, D7 MEDIUM-7; re-swept 2026-08-31), frame-exit twin :3216–3230, `callArgsK`
  docstring :1718–1727, StepFn.lean:166/564/685. History: BUG-052.
- PIN (the VALUE axis; the panic axis is enveloped, bullet above): the
  call evaluates first (args, frame); target operands evaluate at frame
  exit; then stores. gc's realized point for index-kind operands
  (NOT for assertions — see above). Plausible envelope:
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

### E6. `len`/`cap` hoist discriminating shapes — (a) ENVELOPED via E13's `unseqPanic` where the left material is PROBED; REFUSED (narrowed A6 guard) where it is not — after the e13-b re-audit fix round (2026-09-05) that residue is a compound target that CONTAINS A CALL, a method-call receiver operand on the `receiverAddr` path, a forced select/range target, an inline allocating conversion's operand; zero sites of its own

- WHERE (history): BUG-032's fix, narrowed by mini-slice A6 (2026-08-31)
  to the composition (panicky residual operand) x (panicky inline
  material to its left) x (ordered event after it in the same sweep) —
  `hoistReordersPanic` (emit.go), extended to the `make` hoist by FR-28
  (2026-09-04, BUG-083 fixed AS A REFUSAL). The F23 over-reach was
  retired at A6; B-3 (2026-09-01) recorded that A6 was not a pure
  narrowing (receive-free functions gained the refusal).
- RETIRED 2026-09-05 (E13 option (b), RULED [USER], relayed): the
  composition the guard refused is spec-UNSEQUENCED (the builtin call is
  ordered against other calls, not against a sibling assertion/index),
  and the machine now realizes BOTH orders through the `unseq-probe`
  statements the frontend emits (`ChoiceSite.unseqPanic`; E13). The
  guard's predicates (`hoistReordersPanic`, `residualPanicFreeOperand`,
  `nilDerefOnlyResidual`, `sweepPanickyInlineBeforeKinds`) are DELETED;
  the refusal texts they produced match nothing (the `lowerdiag` cause
  `len-hoist-panic-order` is a tripwire). Every row that pinned the
  refusal red-by-design now LOWERS: `builtins/len-vs-call-order/
  {panicky-between,len-nil-left-vs-index-operand,len-assert-vs-nil-
  operand}` strict PASS (singleton sets), `{hint-panicky-between,
  make-slice-panicky-between,make-chan-cap-panicky-between,make-index-
  left,make-inner-len,make-hint-{struct,array,generic}-any-key,
  len-struct-any-key-left-assert}` membership PASS (two members each).
  The FORCED half of the same code — `sweepOrderedEventAfter`, the
  hoist of `len`/`cap`/`min`/`max` when an event follows (BUG-062) — is
  unchanged. This row leaves §5 (it stood in for latitude; the latitude
  is now enveloped at E13). Design: `docs/2026-09-05_e13-b-design.md`
  §4 D5.
- E13-B AUDIT FIX ROUND (2026-09-05, [AGENT]; audit findings R1/R2/R4):
  the retirement above was OVER-WIDE. The envelope probes an operand only
  where `emitExpr`'s hook fires; the deleted guard had swept the WHOLE
  statement, so on the material the envelope does NOT probe the
  composition went from a visible refusal to a SILENT single-member
  answer ≠ gc: (i) an assignment/IncDec/compound TARGET operand
  (`x[iv.(int)] = len(b[j]) + wit(5)`, `x[iv.(int)] += …`, `m[iv.(string)]
  = …`, `x[iv.(int)] = len(make([]int, t[k]))` — gc the interface
  conversion, the machine the hoisted operand's index panic); (ii) an
  operand containing `recover()` (`r = recover().(int) + len(b[j]) +
  wit(5)` in a defer); (iii) an address-of operand (`&a[i]`, an inline
  `index-addr`); (iv) an operand containing an allocating conversion
  (`[]byte(s)[i]`, never probed since R7). The NARROWED A6 guard is
  REINSTATED on exactly that residue (emit.go
  `hoistReordersUnprobedPanic`: `residualPanicFreeOperand` ×
  `unprobedPanickyBefore` — the old census minus every probed node — with
  FR-28's nil-deref transparency), at the len/cap hoist and in
  `emitMake`, refusing BY NAME; the map-assign target path, left probed
  against design §4 D4, is suppressed like every other target (the twin
  loses one probe). So this row is BOTH: enveloped for probed material,
  a refusal standing in for latitude on the unprobed subclasses — it
  RE-ENTERS §5 as a narrowed entry. Rows red by design: `builtins/e13-
  sibling-panic-order/{tgt-assert-vs-len-hoist,tgt-assert-vs-make,
  compound-assert-vs-len,map-key-assert-vs-len,recover-assert-vs-len,
  bytes-conv-left-len-hoist}` (BUG-102's Cases line — the designed-red
  entry; BUG-032/BUG-083 stay fixed). The
  STRUCTURAL-ALLOCATION class (E13 residual 5, R2) is a sibling refusal
  recorded at E13. `lowerdiag`'s `len-hoist-panic-order` cause is LIVE
  again (its 2026-09-04 texts stay a tripwire).
- E13-B RE-AUDIT FIX ROUND (2026-09-05, [AGENT]; re-audit findings
  R1'-1..R1'-4): the fix-round residue above was itself too wide — the
  target suppression PINNED the events-first member where gc realizes
  the other (E2's re-audit bullet), and `recover()`/allocating-conversion
  operands were excludable only on the SYNTAX, not the wire. The
  envelope now probes phase-1 target operands (the target's own check
  is the phase-2 store's), address-of operands (`&a[i]`, `&p.f`),
  array-of-array target bases, the hoisted `recover()`'s residual
  (`$c.(int)`) and a HOISTED allocating conversion (hoisted when an
  ordered event follows it), so the six fix-round designed reds LOWER
  (BUG-083's Cases line, the same retirement-into-latitude). The guard is
  wired at EVERY hoist (len/cap/min/max when an event follows;
  make/append/copy unconditionally), its predicates recurse into
  `min`/`max`, and its census descends into a call that ENCLOSES the
  hoisting construct (`println(EXPR)` no longer hides the material).
  Residue, red by design: `builtins/e13-sibling-panic-order/compound-
  call-target-vs-len` (`x[f()] += len(b[j]) + wit(5)` — the target's
  address is a hoisted temp, its check unprobed; its no-len sibling is
  BUG-104, open). E6 stays in §5 as this one-row narrowed entry. Note
  (re-audit LOW): `probeKind` also NARROWS the old A6 census — float
  division, a constant divisor and an unsigned shift count are not
  panicky and are neither probed nor refused; the retired sweep had
  counted them conservatively.

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

### E9. Map iteration order — (a) ENVELOPED (full literal envelope over the LIVE map) — RE-ENVELOPED 2026-08-19 (BUG-005 (L) surgery, user-ruled); cross-goroutine prune CLOSED 2026-09-02; MECHANISM = entry-identity stamps since 2026-09-03 (B1)

- CONSUMPTION RULE (G-U, 2026-09-04): the `mapIter` consult pops the
  stream iff its width (candidates + stop slot) is ≥ 2 — the uniform
  rule of `Choices.consumeAt`. Before G-U this site alone popped at
  width 1 (the last MANDATORY candidate, a forced pick); the
  `ChoiceSite.policy` table attributed that pop to "memo §5 ruling Q3".
  PROVENANCE, made explicit here: the Q3 ruling ([USER] Mike,
  2026-08-19, `docs/2026-08-19_bug005-map-range-memo.md` §5) defines
  the CANONICAL MEMBER — the machine at the zero stream, stop ordered
  LAST — and says nothing about popping at width 1; the width-1 pop was
  the stage-A [AGENT] transcription of the code as it stood. G-U (RULED
  [USER] 2026-09-04 as recommended, relayed) supersedes that
  transcription; the Q3 ruling itself is UNCHANGED and still holds
  (the zero stream picks slot 0 at every width, popped or not, so the
  canonical produce-all member is the same machine run). Behaviour SET
  unchanged; realization under fixed streams re-indexed — certified by
  the whole-corpus choice-trace bijection
  (`docs/evidence/2026-09-04_c-arc-gu/`).
- MECHANISM OF RECORD (design-hygiene arc slice 1, B1 — the second
  audit's Q11; [AGENT] execution inside the [USER]-ratified arc,
  `docs/2026-09-03_design-hygiene-arc.md`; design note
  `docs/2026-09-03_hygiene-b1-stamps-design.md`): every map entry
  carries a fresh per-map `Nat` id (`GoValue.mapData entries nextId`,
  never reused — deletion and `clear` erase entries and leave the
  counter); `Cont.mapIterK` carries the `produced` and `start` sets as
  ID sets; candidates = live entries whose id ∉ produced, in cell
  order; the stop slot is legal iff no candidate id ∈ start. A
  `mapDelete`/`clearMap` is a heap write and nothing else: the
  delete-prune family (`pruneIterFramesKey`/`All`, `contAfterStmtOp`,
  `removeKeyList`, `keyInKeys`, `Config.mapContM`, `pruneForeign*`,
  `foreignPruneError`, the `pruneForeign` premise on `StepM.thread`)
  is DELETED; the pool step is thread-local again (NPDRF obstruction 7
  discharged). The envelope below is UNCHANGED — the stamped machine
  certifies to the identical sets on every E9 row (set-equality
  transcripts, `docs/evidence/2026-09-03_hygiene-b1-stamps/`), and the
  choice tape is consumed identically. The paragraphs that follow
  describe the retired key-set mechanism where they say "prune"; they
  are kept as the history of how the envelope was reached.

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
  `mapDelete`/`clearMap` prune deleted keys out of EVERY goroutine's
  in-flight `mapIterK` frames over the same map — the deleter's own via
  `contAfterStmtOp` inside `stepFn`, every other goroutine's via the
  pool step's `pruneForeign` (Multi.lean, 2026-09-02) — which is what
  makes "removed before being reached ⇒ not produced" exact and a
  re-created key a candidate again in whichever goroutine ranges.
  [2026-09-03: the prune is RETIRED — the sets are entry-id sets and a
  deleted entry is simply absent at the next pick; see the MECHANISM OF
  RECORD bullet above.]
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
  (maps/delete-readd-during-range, maps/added-entry-count;
  2026-09-02: maps/delete-insert-readd-during-range — the
  oracle-EXHIBITED twin: with ONE intervening insert gc re-produces
  the re-created key in ~87% of runs at size 3, so BOTH members of the
  I-1 envelope are now gc-observed, same-goroutine; and the
  cross-goroutine rows below).
- CROSS-GOROUTINE MUTATION — **CLOSED 2026-09-02 [AGENT, Tier-5 slice
  t5-e9-prune; the [USER] ruling applied is the 2026-08-19 full
  literal envelope, unchanged]**. History: this row disposed of the
  cross-goroutine case as "already a data race" (FALSE against the
  code — fidelity finding A1-20, REOPENED 2026-08-31): the delete-prune
  walked only the DELETING goroutine's continuation, so a DRF
  cross-goroutine delete-then-re-create (goroutine B deletes and
  re-inserts key k mid-range, handshake-ordered against ranging
  goroutine A's picks — `-race` green 200/200) left A's produced/start
  sets unpruned and re-production of the re-created key was
  unrealizable: permitted ∉ modeled on a DRF program. MECHANISM: the
  pool step (`stepThread`, Multi.lean) now applies the SAME
  `contAfterStmtOp` prune to every OTHER goroutine's continuation at a
  `mapDelete`/`clearMap` apply that proceeded (`pruneForeign` over
  `Config.mapContM`; no new state, no new frame shape, no per-map
  registry; fail-closed: `Except`-monadic walk, every configuration
  constructor enumerated, an unexpected apply successor is an
  `.internal` refusal). The pool relation `StepM.thread` (and NPDRF's
  `StepMFine.thread`) carries the prune as a premise; soundness,
  completeness, `stepThread_single` (one-thread pool ≡ `stepFn`),
  `MultiWf` preservation and stream-obliviousness were extended
  arm-for-arm (`pruneForeign_wf`, `Config.mapContM_locSup`,
  `stepFn_stmtOpApply_shape`; no sorry). EVIDENCE: gc probe (evidence
  dir `docs/evidence/2026-09-02_e9-cross-goroutine-prune/`) — the
  plain shape NEVER re-produces in gc (160,000 in-process trials over
  GOMAXPROCS ∈ {1,8} × sizes {3,8,100,1000} + 600 fresh-process runs),
  but with ONE intervening fresh insert between the delete and the
  re-create gc re-produces the key in ~87% of runs (size 3; sweep
  1→87%, 2→75%, 3→63%, 4→50%, 5→37%, 8→0%; size 8 never — a
  single-group slot-placement effect of gc's swiss map), so the
  formerly unrealizable member is gc-EXHIBITED: before the prune that
  shape was observed ∉ modeled (a differential mismatch), not merely
  permitted ∉ modeled. CORPUS: membership rows
  `maps/cross-goroutine-delete-readd/drf` (admitted {3,4}; gc samples
  3) and `.../insert` (admitted {1,2}; gc exhibits both), plus the
  racy control `.../racy` (no handshake — every enumerated path
  refuses, `-race` red exit 66), which shows the DRF/racy line the
  detector draws; the singleton-set membership lint is the honest red
  these rows show if the foreign prune regresses. OVER-prune guards
  (audit fix round 2026-09-02 [AGENT], F5): the confluent rows
  `maps/cross-goroutine-delete-noreadd/{delete,clear,other-map}`
  (singletons 3006 / 1 / 3006) go red if the prune reaches too far —
  a start set emptied on a plain delete (early stop legal) or map
  identity ignored (a produced key re-enters a range over ANOTHER map);
  red-first shown against an over-pruning stub (evidence README, "F5
  red-first"). COST (recorded at the audit, F8; no before/after
  measurement taken): a pruning-op apply now walks every other
  goroutine's whole continuation — O(threads × continuation depth) per
  `mapDelete`/`clearMap` apply — and a 2-goroutine TWO-ranger shape
  (both goroutines ranging while one deletes) did not enumerate at
  `backedge=full` within 10 min at the audit (it completes at
  `backedge=0` in ~1 min); the corpus rows here are single-ranger
  shapes. [2026-09-03: the O(threads × depth) walk is gone with the
  prune (B1 stamps); a delete is O(1) beyond the cell write.] The old
  re-envelope trigger is discharged; no residual narrowing remains on
  this row.
- IRREFLEXIVE KEYS (found and fixed by B1, 2026-09-03 — BUG-088): a
  key whose Go `==` is irreflexive (NaN, or an array/struct/interface
  holding one) could never be marked produced by the key-set frame
  (membership was `valueEq`), so a range over such a map re-produced
  its first NaN entry forever at the zero stream (fuel-out; the
  modeled set admitted any number of productions). With stamps each
  entry is produced exactly once — the spec's production table —
  pinned by `maps/nan-key-range` (gc 32, machine 32, confluent) and,
  for the aggregate members of the class,
  `maps/nan-key-range-aggregate/{array,struct,interface}` (gc 32 / 73 /
  32 = machine; all four fuel-out on main @ 345ef090 — red-first
  transcripts in `docs/evidence/2026-09-03_hygiene-b1-stamps/`). This
  is the ONE behaviour the slice changed, on a class no earlier row
  exercised. GOVERNANCE (audit fix round F1, 2026-09-03): this IS an
  E9 ENVELOPE NARROWING on irreflexive keys — the set the machine
  admitted there (≥2 productions of one NaN entry, or an immediate
  stop, all spec-illegal) genuinely shrank to "each entry once" — and
  E9's envelope is a [USER] ruling (2026-08-19) that explicitly
  rejected narrowings. The narrowing was [AGENT]-made BY CONSTRUCTION
  (the stamps have no way to express the old behaviour), is DISCLOSED
  here, in the design note §4, the arc plan and BUG-088, and was
  REFERRED TO THE [USER] FOR RATIFICATION at the merge sign-off.
  **RATIFIED [USER] 2026-09-03** (Mike, relayed by the [AGENT]
  coordinator — cite as relayed): «(b) it sounds like this breaks an old ruling but ends up more accurate to real go - approved». Effect: for IRREFLEXIVE KEYS
  ONLY, this supersedes the 2026-08-19 E9 no-narrowing ruling — each
  entry is produced exactly once; every other point of the E9 envelope
  stands as ruled on 2026-08-19. Ruling record:
  `docs/2026-08-31_qrow-rulings.md`.

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
  realization matches gc's. CENSUS EXTENSION (noodler lane, 2026-09-03,
  [AGENT] — `docs/2026-09-03_noodler-report.md` §2 "latitude"): the
  twelve `noodler/latitude/*` rows put a non-call operand (index read,
  variable read, VALUE-RECEIVER copy, deref) beside a call that mutates
  what it reads, in every position the follow-ons below named and more
  — slice-literal element (`[]int{a[0], f()}`), keyed struct literal,
  MAP-LITERAL key-vs-value (`map[int]int{a[0]: f()}`), value receiver
  vs argument call (`v.Plus(f())`, E14's row), call-argument list,
  string concat, conversion operand, deref-vs-call, index/call/index,
  `return` list, send channel-vs-value, a define RHS list — plus the
  three `noodler/maps/{compound-call-mutates,slice-compound-call-mutates,
  compound-call-deletes}` rows (`m[k] op= f()` / `a[i] op= f()` with f
  mutating or deleting the element: the element is read AFTER the
  call). All fifteen PASS with gc realizing call-first; they ride THIS
  entry's (b)-pin and its re-envelope obligation (the three maps rows
  carry no latitude label in their features — recorded here instead).
  XIMPL/ARCH would bear on whether any
  implementation realizes operand-first (none known; same open
  question as E2).
- RE-ENVELOPE OBLIGATION + COST: rides E2's re-envelope (same
  call-first family; the membership/panic-identity treatment that §7
  item 5 lists — with F3's cost note arguing for it — covers this
  entry's observables too). Until E2 opens, no new machine arms;
  widening then requires either frontend order-variants or a GoCore
  operand-order choice site. MODERATE, sequential-only observable.
  RECORDED CENSUS FOLLOW-ONS (P2 audit) — CENSUSED 2026-09-03 (noodler
  lane; rows in the EVIDENCE paragraph above): composite-literal
  element order vs a call among the elements (`[]int{a, f()}` →
  `noodler/latitude/slice-literal-index-vs-call`, `struct-literal-var-
  vs-call`) and map-literal key-vs-value order (`noodler/latitude/
  map-literal-key-vs-call`) — gc realizes call-first on both, matching
  the machine; duplicate-map-key evaluation order was already pinned by
  `maps/map-literal-duplicate-eval-order`. E12 was written for binary
  operators only; the census now covers these sibling positions under
  the same pin.
  E13 BY-PRODUCT NOTE (lane e13-b, 2026-09-05): the `unseqPanic` probe
  (E13) consults ONLY when a non-call operand PANICS ahead of a sibling
  event, so this entry's VALUE observable is untouched — every
  `noodler/latitude/*` row and the compound-assign rows stay singleton
  strict rows (measured at the lane: 0 of them moved), and the (b)
  call-first VALUE pin stands with its obligation. Two panic-side
  by-products ARE E12(ii)'s: (1) two probed operands both panicking
  early can realize the SECOND's panic ahead of the FIRST's (the
  DEFER×RAISE combination — `builtins/e13-sibling-panic-order/two-index-
  left-call`, 3 members), a member the spec permits (non-call vs
  non-call order is unspecified by omission; I-2 UNSEQ) and wider than
  this entry's left-to-right pin on exactly the panic-vs-panic shapes;
  (2) a hoisted ALLOCATION's payload (`g([]int{t[k]})`) evaluates at the
  allocation's hoisted position, ahead of inline material to its left —
  a pre-existing structural departure from left-to-right among
  non-calls, paired with a probe on the LEFT material (both orders of
  left-material-vs-payload realized). CORRECTED at the e13-b audit fix
  round (R2): the payload vs an ordered event lexically AFTER the
  literal (`(&T{x: s[i]}).x + wit(5)`) is NOT enveloped — the payload
  evaluates before the call on every stream where gc evaluates it after
  — and is REFUSED by name since the fix round (E13 residual 5). Neither
  changes a value observable. The VALUE axis itself is reachable through
  the len shape the retired guard used to refuse — BUG-101 (`assert-ok-
  early-len-hoist`): the early evaluation succeeds, is discarded, and the
  residual re-evaluation after the mutating call panics where gc has the
  early value. This entry's obligation now has a filed witness.
  `binop-order/operand-panic-vs-call/{call-before-left,call-before-left-
  div}` moved to lane=membership at e13-b: their LEFT index panics on
  the pre-call state, so the machine offers the panic (RAISE) beside the
  call-first value (DEFER, gc's, this entry's pin) — E13's observable
  riding an E12 row.
  EXCEPTION TO THE CALL-FIRST VALUE PIN (e13-b re-audit fix round D4 (v),
  RECORDED at the final verification fix round 2026-09-05, R''-8,
  [AGENT]): for the two ALLOCATING CONVERSIONS `[]byte(s)` / `[]rune(s)`
  followed by an ordered event in the same sweep, the frontend HOISTS the
  conversion to a temp at its lexical position (so that its residual is
  pure and probeable), and therefore realizes those two shapes
  OPERAND-first on the VALUE axis, not call-first: `int([]byte(s)[0]) +
  func() int { s = "zz"; return 1 }()` — gc 98 (`'a' + 1`: the
  conversion reads `s` before the call mutates it), main b77f3298 123
  (`'z' + 1`: the inline conversion read the mutated `s` — a silent wrong
  VALUE under the call-first pin, gc ∉ the machine's single member), the
  e13-b tip 98. Row `builtins/e13-sibling-panic-order/bytes-conv-value-
  vs-mutating-call` (born PASS, strict) pins gc's 98. The exception is
  exactly the two conversion heads and only when an event follows; every
  other shape of this entry (the `noodler/latitude/*` rows, the compound-
  assign rows, `a[i] + f()`) keeps the call-first realization. gc's
  member on these two shapes is order.go's `safeExpr`/`copyExpr`
  treatment of the conversion (a value-producing allocation evaluated at
  its position); the machine's hoist now agrees. Design §6 item 7.

### E13. Non-call panicking operations (type assertion, indexing, …) vs SIBLING ordered events — (a) ENVELOPED (`unseqPanic`, lane e13-b 2026-09-05 — the implementation of the RULED (b) LATITUDE ruling of 2026-09-05 [USER] (relayed), landed at merge train round 17; was (b) PINNED structural, calls first)

Added 2026-08-20 from the grossmith campaign-2 record
(`docs/2026-08-20_grossmith-findings-2.md` §4, case `case_16162`, seed
4016162; F-3 of that document's owed follow-ups). E12's sibling on the
same spec ground, one level up: E12 is the order of the operand events
of ONE binary operator against the calls in it; this entry is the order
of a non-call operation's PANIC against ordered events that are its
lexical SIBLINGS — other elements of the same RHS list, or other
arguments of the same call. **RE-ENVELOPED 2026-09-05** — option (b)
of the four-way treatment below, RULED [USER] Mike 2026-09-05, verbatim
as relayed by the [AGENT] coordinator (cited as relayed): «we should do
what the standard supports, and avoid over-refusal if we can. That's
what (b) means right?» — design of record
`docs/2026-09-05_e13-b-design.md` (the decision procedure §1, the
machine construct §3, the frontend §4, the residuals §6).

- WHERE: spec#Order_of_evaluation, OMISSION-grounded (the absence is
  the anchor, as at C1/C5/E12(ii)): the left-to-right rule's scope is
  "function calls, method calls, receive operations, and binary logical
  operations" — a **type assertion** is none of these, and neither is
  an **index expression**, a slice expression, a dereference, a
  division, a shift, an interface comparison or a slice-to-array
  conversion. The "except as required lexically" clause does not reach
  a sibling: it forces a non-call operation only when that operation is
  an ARGUMENT of the event ("g cannot be called before its arguments
  are evaluated"). **That distinction is the whole entry**, and getting
  it wrong in the other direction is a BUG, not latitude: the argument
  position IS forced (BUG-062's territory — `builtins/e13-sibling-
  panic-order/{forced-arg-only,index-left-call-arg-panics,deref-left-
  index-arg-call}` pin that no member ever runs the call before its
  argument). The decision procedure over the AST — which pairs are
  FORCED (F1–F5) and which UNSEQUENCED — is design §1.
- ENVELOPE (the machine's set, per probed operand): the frontend emits
  an `unseq-probe` statement at the lexical position of every panicky
  non-call operand that has a sibling ordered event lexically AFTER it
  (`tools/nativefrontend/emit.go`, the `emitExpr` hook; the census of
  the panicky kinds is `probeKind`, ONE function). The machine
  evaluates the probe there: a value is discarded (the operand is
  re-evaluated at its residual position — pure by construction: calls,
  receives and allocations are hoisted out of it, `recover()` is never
  probed and the decoder refuses a probe containing one); a PANIC is the
  `ChoiceSite.unseqPanic` pick at bound 2 — **DEFER** (slot 0: the
  sibling events first, the operand re-evaluated after them — the
  pre-change machine's only member) or **RAISE** (slot 1: the operand's
  panic first). No consumption unless the operand panics early, so an
  ordinary `a[i] + f()` row's stream is untouched. With one probed
  operand this is exactly the ruling's "both orders"; with two, the
  DEFER×RAISE combination is a third member (the second operand's panic
  ahead of the first's — permitted by the same omission, I-2 UNSEQ; E12
  by-product note). The set is a SUBSET of the two total orders'
  observables by the purity argument (design §3), and every realized
  member is spec-conforming. Rule-site citation: `Stmt.unseqProbe`'s
  docstring (Syntax.lean) carries the clause; the census mirror (§0)
  carries the row.
- gc's MEMBER, per operand kind (evidence `docs/evidence/2026-09-05_e13-b/
  gc-realization.txt`, 32 probes at the pin): EARLY (= RAISE) for type
  assertions, slice expressions and interface comparisons; LATE
  (= DEFER) for index, dereference, division, shift and slice-to-array
  conversion operands — gc's compiler-internal rule (order.go: `ODOTTYPE`
  / `OSLICE*` / interface `OEQ` are safe-expression-ordered early;
  `OINDEX`/`ODEREF`/`ODIV`/`OLSH` stay in the residual) landing on two
  different conforming members. So the assertion-vs-indexing split this
  entry used to record as "two axes on opposite sides" is not a machine
  defect on either axis: both are members, and gc's draw lies in the
  certified set on every corpus row (§EVIDENCE). gc is SELF-STABLE
  (default flags and `-gcflags=all='-N -l'` agree), so the contrast
  with E3 (compiler-internal, unpinnable) stands: this is latitude in
  the spec. XIMPL would bear on whether any implementation orders these
  a third way; none known.
- EVIDENCE: GC + enumeration. The corpus rows are MEMBERSHIP rows
  (lane=membership, `width=2`, `members=` pinned by enumeration; the
  §7 item-5 panic-identity treatment realized as SET membership over
  the choice stream — the comparator is not relaxed, the set is wider):
  `builtins/e13-sibling-panic-order/*` (61 rows after the re-audit fix
  round — 31 at the lane tip, +10 at the fix round, +20 at the re-audit:
  the §2 probe family —
  assertion/slice/comparison/index/deref/division/shift/conversion left
  of a call; the middle position; the receive sibling; the argument-list
  sibling (d2); the composite literal and return list; the send
  statement; `append`/`copy` — the divergence the fr27-fr28 audit found
  censused NOWHERE, now certified members; `make`; a mutating call
  (members differing in STATUS); two probed operands (3 members); and
  the strict controls), the retired-refusal rows of `builtins/len-vs-
  call-order/*` (E6), and `binop-order/operand-panic-vs-call/{call-
  before-left,call-before-left-div}`. gc's draw exhibits ONE member per
  row (deterministic per toolchain; the K=32 draws run to the budget —
  the BUG-087 rows' precedent); the OTHER member is argued from the
  spec's silence plus gc's own realization of it on the other operand
  kinds. The historical probe tables (d1/d2/bare-index; the min/max
  a6p/a6q table) are superseded by the row set and the evidence dir;
  their readings stand (min/max hoist like calls — ordered events — and
  their arguments are FORCED before them; a lexically-left assertion vs
  a later min/max is this entry's latitude).
- THE FOUR-WAY TREATMENT (fr27-fr28 audit fix round, 2026-09-05 —
  `docs/evidence/2026-09-04_fr27-fr28/e13-probes.tsv`) — RESOLVED by
  the ruling: (1) `make` REFUSED, (2) `min`/`max`/user calls lowered
  call-first, (3) `append`/`copy` lowered call-first and censused
  nowhere, (4) `len`/`cap` REFUSED. Option (b) taken: all four are ONE
  treatment now — a membership set with both orders; the make and
  len/cap refusals RETIRED (E6, BUG-032, BUG-083, FR-28 CLOSED);
  append/copy censused by row. Option (a) (extend the refusal to every
  hoisting construct) would have refused the ordinary `a[i] + f(b[j])`
  idiom class; option (c) would have kept a wrong-by-omission census.
  - **RULED (b) — [USER] 2026-09-05 (relayed).** The [USER] quote was
    received by the [AGENT] coordinator in conversation and relayed to
    the recording worker (lane `rulings-0905`); cited as relayed, not
    firsthand. Posed as item (2) of an eight-item list with the
    coordinator recommending (b), Mike replied, verbatim as relayed:
    «(1) approved, (2) we should do what the standard supports, and avoid over-refusal if we can. That's what (b) means right? (3) done, (4-8) all approved as recommended». The coordinator's gloss [AGENT] of what (b)
    means, answering the question in the reply: wherever the spec
    leaves the order of a non-call operation's panic and its sibling
    calls UNSEQUENCED (the omission above; I-2/L-013), the machine
    admits BOTH orders as latitude via a membership shape (the §7
    item-5 panic-identity treatment: any of the candidate panics, with
    whatever ran before it), and the `make` (BUG-083/FR-28) and
    `len`/`cap` (BUG-032 A6 residual) refusals RETIRE into that shape —
    "do what the standard supports, avoid over-refusal". The FORCED
    positions are NOT latitude and stay gc-exact: a panicky operand
    that is an ARGUMENT of a lexically earlier call must be evaluated
    before that call (spec#Order_of_evaluation, "g cannot be called
    before its arguments are evaluated") — BUG-062's territory, already
    realized. Option (3) above (`append`/`copy`) is covered by the same
    shape, so its un-pinned divergence closes with the implementation,
    not before. IMPLEMENTATION LANDED — lane `e13-b`
    (design note `docs/2026-09-05_e13-b-design.md`: the member set per
    composition, the forced-vs-unsequenced classifier §1, the rows that
    moved from refusal to membership §5; merged at merge train round 17,
    2026-09-05). The former NO-PIN bullet is replaced by the PINS ARE
    MEMBERSHIP ROWS bullet below, and this entry's heading tag moved
    from (b) PINNED to (a) ENVELOPED with the merge — per this
    sub-bullet's own rule, never on the ruling alone. (Sub-bullet kept
    verbatim as the ruling's provenance record; the "owed" sentence
    rewritten at the round-17 rebase, [AGENT].)
- PINS ARE MEMBERSHIP ROWS NOW (replacing the former "NO PIN MAY BE
  TAKEN HERE"): the old rule existed because a STRICT row on either
  axis would have recorded latitude as fidelity (assertion axis) or
  frozen an unrequired agreement (indexing axis). With the set
  enveloped, a membership row pins the SET and samples gc into it — the
  honest pin. A strict row on this axis is legitimate only where the
  set is a singleton by construction (both orders coincide: `len-assert-
  vs-nil-operand`, `panicky-between`'s witness, an inline `min`), or
  where the position is FORCED (F2) or a recorded residual (§6.1:
  `assert-right-call`). The generator-side observation that a STRICT-
  lane outcome-determinism claim can land on a point like this is
  grossmith's (F-5) — answered: such a row now fails at stage `nondet`
  and is routed to membership (measured at the lane: the two binop rows
  and `make-hint-call` did exactly that).
- RESIDUAL NARROWINGS AND REFUSALS (recorded, design §6; rewritten at
  the e13-b audit fix round 2026-09-05 — the first cut over-stated the
  envelope, audit R4): (1) an operand RIGHT of the event (`f() + a[i]`)
  realizes only the lexical (events-first) order — gc agrees (probe u);
  (2) an operand that is the hoisted event's OWN operand (`len(s[i:]) +
  wit(5)`) realizes only the lexical order against LATER events — gc
  agrees (`slice-left-len-call`); (3) UNPROBED left material — an
  assignment/IncDec/compound TARGET operand, an address-of operand, an
  operand containing `recover()` or an allocating conversion (`[]byte(s)`
  / `[]rune(s)`, R7) — beside a hoisted len/cap/make whose operand
  panics is REFUSED by name (E6, the narrowed A6 guard; rows on
  BUG-102) — RE-AUDIT FIX ROUND (2026-09-05, R1'-1..4): REWRITTEN. The
  target / address-of / `recover()` / allocating-conversion subclasses
  are PROBED now (design §4 D4: phase-1 target operands are siblings of
  the RHS's calls; `&a[i]` is a bounds-checking address; `recover()` is
  hoisted so its residual is pure; a conversion followed by an event
  hoists), so `x[iv.(int)] = wit(5)`, `m[iv.(string)] = wit(5)`, `r =
  recover().(int) + wit(5)`, `sinkP(&a[iv.(int)], wit(5))`, `x[iv.(int)]
  = <-ch` and the len/make/min/copy/append siblings are two-member sets
  with gc's EARLY member in them (rows `tgt-assert-vs-call`, `map-tgt-
  assert-vs-call`, `recover-assert-vs-call-w`, `addr-assert-left-call`,
  `tgt-assert-vs-recv-w`, and the six former designed reds, now on
  BUG-083's line). What remains unprobed and REFUSED beside a hoist is a
  compound target that CONTAINS A CALL (`compound-call-target-vs-len`), a
  method-call receiver operand ON THE `receiverAddr` PATH only (the
  implicit `&x` of a pointer-receiver call on an addressable non-pointer
  operand, and `(*p).M()`'s `addr-of-deref` — E14's sub-axis; receivers
  that reach `emitExpr` ARE probed, measured at the final verification
  fix round R''-4), a forced select/range target, an inline allocating
  conversion's operand, and a map compound target's base and key
  (`emitMapCompound`'s `probeSuppress`, the frontend's one UNFORCED
  suppression — design §4 D4); the compound-call target beside a plain
  call, a receive or a method call is BUG-104 (open, ∉ gc, five rows,
  pre-existing on main); (4)
  the VALUE observable is E12's — and is REACHABLE through the len shape
  the retired guard used to refuse: `iv.(int) + len(b[j:]) + func() int {
  iv = "s"; return 1 }()` with `iv` holding an int — gc 6, the machine the
  conversion panic on every stream (the probe discards a successful early
  value) — filed OPEN as BUG-101, red-first row `assert-ok-early-len-
  hoist`; the receiver axis (E14) is not this entry's; (5) a STRUCTURAL
  ALLOCATION (`&T{…}`, elided `&T`, slice/map literal, interface method
  value) with a panicky payload followed by an ordered event is REFUSED
  by name (R2: `(&T{x: s[i]}).x + wit(5)` — gc prints `wit 5` then panics,
  the machine panics before the call on every stream; the allocation
  evaluates its payload at its hoisted position and no probe reaches gc's
  member; pre-existing on main, undisclosed here until the audit; rows
  `composite-ptr-payload-vs-call`, `slice-lit-payload-vs-call` on
  BUG-102) — RE-AUDIT (R1'-3, R2'-1): the refusal reaches the println-/
  sink-rooted spellings (the census descends into an enclosing call),
  the receive as the event (`[]int{s[i]}[0] + <-ch`: gc receives first,
  measured with a `len(ch)` witness); an allocating conversion whose
  own operand panics (`[]byte(s[i:j])`) stays inline with the operand's
  probe (`bytes-conv-payload-vs-call`, two members ∋ gc); it does NOT fire on a MAP
  literal (gc's `OMAPLIT` evaluates dynamic entries at the literal —
  the machine's member is gc's, `map-lit-payload-vs-call`) or on a
  literal forced by an enclosing call (`composite-ptr-in-arg-then-call`);
  rows `{composite-ptr-payload-vs-call-printroot,slice-lit-payload-vs-
  call-sinkroot,slice-lit-payload-vs-recv}` join BUG-102; (6) a probed operand is evaluated twice on the no-panic path
  — a constant-factor cost, no fuel-out flips measured; (7) the race
  detector sees the early read as an ordinary read, so under DEFER the
  operand is READ TWICE in program order — a write racing the first read
  but happens-before the second yields a race report the residual-only
  trajectory lacks: an OVER-approximation (fail-closed over-report, never
  a missed race), not idempotence (design §6 item 8); (8) RE-AUDIT
  (R1'-8): with TWO OR MORE events after a probed operand the machine
  offers the two ENDPOINTS only (the operand before all of them or after
  all of them); the spec-licensed interleaving (I-2 UNSEQ, L-013 — the
  operand between the calls) is not a member; gc realizes an endpoint.
  A (b-n) narrowing, re-envelope obligation: a probe re-emitted after
  each hoisted event (design §6 item 9); (9) RE-AUDIT (R1'-7): the
  value axis (4) has a second measured instance, the SLICE kind — `n =
  a[i:][0] + len(b[j:]) + mut()` with `mut` setting `i = 1`: gc `mut`
  then 12, the machine 22 — BUG-101's second row `slice-value-early-len-
  hoist`; the class is every EARLY-realized probe kind (assertion, slice
  expression; interface comparison measured to match). Cost of removing
  (1)–(2): a probe for every panicky operand regardless of position (LOW
  mechanism, more pops on panicking rows).
- RE-ENVELOPE OBLIGATION: MEASURED-DISCHARGED for the probed sibling-
  panic axis only — the membership rows' sets contain gc's draw
  (§EVIDENCE; 39 at the fix round, 56 after the re-audit fix round —
  RE-DERIVED at the final verification fix round (R''-6, [AGENT]) from
  the baseline's `membership` stage column over the 94-row E13 family:
  39 + 11 born membership rows (`tgt-assert-vs-call`, `map-tgt-assert-vs-
  call`, `tgt-assert-vs-{min-call,copy-call,append,recv-w}`, `addr-
  assert-left-call`, `compound-index-vs-len`, `array-base-target-vs-len`,
  `recover-assert-vs-call-w`, `bytes-conv-payload-vs-call`) + 5 FAIL→PASS
  flips INTO membership (`tgt-assert-vs-len-hoist`, `tgt-assert-vs-make`,
  `compound-assert-vs-len`, `map-key-assert-vs-len`, `bytes-conv-left-len-
  hoist`; the sixth designed red, `recover-assert-vs-len`, lowered
  STRICT) + 1 strict→membership lane move (`addr-index-left-len-hoist`) =
  56; the earlier "55: 16 rows joined" had dropped the lane move. The
  final round's 4 born rows add none (3 red-first on BUG-104, 1 strict
  PASS), so 56 stands). NOT discharged:
  (3)'s residue (the compound-call target, the `receiverAddr` receiver
  path, forced targets — refused beside a hoist; BUG-104 beside a plain
  call, a receive or a method call), (4) the
  value axis (BUG-101, two rows, E12's obligation), (5) the structural-
  allocation class (refused), (8) the interleaving members. Those carry
  their own notes; E2–E4's obligations ride §7 item 5.

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

- RECEIVER SUB-AXIS, measured (e13-b final verification fix round,
  2026-09-05, [AGENT], R''-4): the receiver operand's PANIC vs the
  argument list's hoisted events is E13's probe question in receiver
  position, and the frontend answers it by PATH. A receiver that reaches
  `emitExpr` — a VALUE receiver's operand (`s[i].V2(wit(5))`, `s` a
  `[]T`), a pointer-receiver call on an already-pointer operand
  (`s[i].M2(wit(5))`, `s` a `[]*T`), an interface-typed receiver (the
  twin's `r.logger.Panicf(…, r.id, state.GetCommit(), …)` — the probe on
  `r.logger` in `raft.raft.loadState`, present since the lane's first
  pin) — IS probed when a hoisted argument event follows it: two members
  (the receiver's panic before the argument call, or after), gc's LATE
  member in the set (measured: gc prints `wit 5` then panics on both
  slice shapes). A receiver that goes through `receiverAddr` — the
  IMPLICIT `&x` of a pointer-receiver call on an addressable non-pointer
  operand (`s[i].M2(wit(5))`, `s` a `[]T`: the `index-addr` bounds
  check) and `(*p).M2(wit(5))` (the `addr-of-deref` nil check) — is NOT
  probed: a singleton at the LATE member, which is gc's on both measured
  shapes (`wit 5` then the panic), so no ∉-gc answer, but a
  one-member set on a two-member axis (the same kind of structural
  point as the events-first pin this row already records). A receiver
  whose own call is the ONLY event after it (`s[i].M() + wit(5)`) is a
  FORCED position — the receiver precedes its call, which precedes the
  later call — and is rightly unprobed (singleton, gc agrees). The
  events-ahead-of-arguments realization this row is about is untouched
  (a probe reorders no events). Design `docs/2026-09-05_e13-b-design.md`
  §4 D4/D5 and §6 item 4 carry the same statement; the `receiverAddr`
  residue is E13 bullet (3)'s.

### R1. `int`/`uint` width — (b) PINNED to 64 bits

- WHERE: spec §Numeric types: `uint`/`int` are "implementation-specific
  sizes" — "either 32 or 64 bits". Machine (since design-hygiene A5,
  2026-09-04): `Platform.intBits`, pinned at `gcAmd64` (Platform.lean —
  the envelope statement lives on that instance; `platform := gcAmd64`
  is THE one instantiation), read by `IntKind.bitsAt`/`IntKind.bits?`
  (Value.lean; `.int`/`.uint ↦ p.intBits`); `IntKind.normalize` wraps
  at that width. Recorded only in
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
- RE-ENVELOPE OBLIGATION + COST: a second `Platform` instance (A5 made
  the width a record field; `tySizeAlign` is parametric, the rest of
  the core reads the single instantiation — threading a platform through
  `ExecState` is deferred to B7, design note §A5), plus the frontend's
  go/types Sizes config and the negative lane's acceptance — mechanical;
  blocked in practice on having any 32-bit oracle to differentiate
  against.
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

**`strings.Builder.grow` rides this envelope (added 2026-09-03,
`stdlib-source-2`).** Upstream's `bytealg.MakeNoZero(2*cap+n)` — a
runtime leaf documented as "length n and capacity of AT LEAST n" (gc
realizes size-class rounding: Grow(10) on an empty Builder → Cap 16,
Grow(100) → 112, probe-verified go1.26.5) — is OVERLAID by the frontend
as `append([]byte(nil), make([]byte, 2*cap+n)...)`
(`tools/nativefrontend/stdlib-overlay.tsv`, register
`docs/stdlib-admission-register.md`), i.e. MakeNoZero's documented
latitude is realized as THIS site's choice. The envelope contains gc's
point for every n (size-class rounding ≤ 2·n above 32 bytes, ≤ 32 below).
Membership rows `stdlib-source/builder-cap/{grow-empty,grow-hundred,
grow-after-write,grow-then-write}` version-track gc's point against it
(`Builder.Cap()` was a declaration-only stub under the retired shadow
model; it is a real observable now). No new latitude row: the site is an
instance of R2.

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
- **2026-09-04/05 (stdlib slice 3 + its audit fix round A1) — THE CHANNEL
  LANDED; RE-DECIDED.** `math.Float64bits`/`Float32bits` are the
  `float-bits` PRIMITIVE ([USER]-admitted 2026-09-04, relayed), so NaN
  payloads ARE value-observable in-language and the scope condition
  above no longer holds. Measured at the pin (rows `builtins/float-bits/*`):
  gc/amd64 realizes 0xFFF8000000000000 for a runtime 0/0 (SSE "real
  indefinite", sign SET), propagates the first NaN operand's payload
  through arithmetic, and its float `min`/`max` lowering ORs the two
  operands' bits when one is a NaN (`AMD64.rules` MINSD/MINSD/POR:
  `Float64bits(min(Float64frombits(0x7FF8000000000001), 2.5))` =
  0x7FFC000000000001); the machine's every produced NaN is
  softfloat64.go's 0x7FF8000000000000 (sign clear) or, through `fneg`,
  its negation. **Resolution — the refusal is the GUARD, (b-n) kept:**
  `floatBitsApply` refuses `*bits` of the default NaN under EITHER sign
  (audit A1 found the first cut's exact-pattern guard REPORTING
  `Float64bits(-(0/0))` = 0xFFF8… where gc gives 0x7FF8… — a wrong
  answer, closed 2026-09-05); `floatMinMaxBits` is bit-transcribed from
  gc/amd64's idiom over frombits payloads (A1's second wrong answer,
  closed — rows `min-max-payload{,/float32}` green) and returns the
  DEFAULT NaN whenever either operand is one (an OR over it would carry
  the wrong sign undetectably), so the producible-NaN set stays exactly
  {default, −default} and the guard is COMPLETE over it. Designed reds:
  `canonical-nan-refused`, `neg-canonical-refused{,/float32}`,
  `min-max-canonical-refused`, `nan-arith-payload-refused{,/canonical-
  roundtrip}` and the `roundtrip-payloads` row (its 0xFFF8… entry,
  PASS→FAIL at A1 — the legitimate round-trip of the negated default is
  the over-refusal's price), all BUG-094. **RE-ENVELOPE OBLIGATION, LIVE:**
  either a platform-faithful NaN rule (default = 0xFFF8… with SSE
  first-operand propagation, scoped to the oracle platform like R4's
  per-op rounding) or an (a) envelope over the payloads gc's ports
  realize; owner: the floats design (`docs/2026-08-04_floats-design.md`).
  Not taken here.

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

### R9a. Value-receiver method dispatched through an interface holding a nil `*T` — the panic TEXT is a two-member set, (a) ENVELOPED at width 2 (BUG-087; [USER] 2026-09-03), each member (b)-pinned to a gc realization

- WHERE: the same spec point as R9 (spec#Run_time_panics: the error
  values are unspecified; the PANIC itself is forced — spec#Calls /
  spec#Method_values make `x.M()` shorthand for `(*x).M()` and
  spec#Address_operators makes `*x` on a nil `x` a run-time panic).
  The family: the anchor is an interface-receiver method, the receiver
  is an interface box holding a NIL pointer, the resolved method is a
  VALUE-receiver method whose receiver type is EXACTLY the pointee, and
  the target is not a synthesized promotion wrapper — gc's "simple `*T`
  wrapper around a `T` method" (`noder/reader.go` `methodWrapper`:
  `wrapper.IsPtr() && types.Identical(wrapper.Elem(), wrappee)`, whose
  body starts `if recv == nil { runtime.panicwrap() }`).
- THE TWO MEMBERS (both `runtime.Error`, both recoverable — the KIND is
  forced and agreed): member 0 `runtime error: invalid memory address
  or nil pointer dereference` (gc when the call is DEVIRTUALIZED — the
  concrete type visible after inlining, `devirtualize.go StaticCall` —
  so the deref happens in `T.M`'s receiver copy); member 1
  `value method <pkg>.<T>.<M> called using nil *<T> pointer` (gc when
  the call goes through the autogenerated `(*T).M` wrapper:
  `runtime/error.go` `panicwrap`, a `plainError` WITHOUT the "runtime
  error: " prefix). `pkg` is derived from the wrapper SYMBOL — the
  import PATH (`probe087/sub.T.Val … nil *T pointer` at the pin), which
  is exactly the frontend's path-qualified `TypeId.key`, so this text
  is outside BUG-059's name-vs-path class; generic receivers print
  `T[...]` (`funcNamePiecesForPrint`).
- THE SAME-SOURCE WITNESS (one program, go1.26.5): `func mk(p *Inner)
  Valuer { return p }; v := mk(p); v.Val()` — default build and
  `-gcflags=-l=4` → member 0; `-gcflags=-l` and `-gcflags=-N -l` →
  member 1 (`docs/evidence/2026-09-03_noodler/transcripts/
  gc-wrapper-text-mk-helper.txt`; the five corpus rows' own `-l` draws in
  `docs/evidence/2026-09-03_bug087-paniktext/transcripts/rows-gcflags.txt`).
  There is no single gc answer — the C2 class ("`go run` and `go run
  -gcflags=-N -l` disagree — only an optimizer artifact"), hence the
  demonic choice rather than a pin to one flag set.
- MACHINE: `ChoiceSite.nilValueMethodText` (State.lean) — width 2 on the
  family, drawn in the frame-entry funnels `enterFrameStep`/
  `enterFrameDeferPanicking` (StepFn.lean); the family predicate and
  envelope statement is `nilValueMethodText?` (Ops.lean, beside the nil
  arm that raises member 0); the relation's entry-panic rules quantify
  the pick (`entryPanicText`). Slot 0 = member 0, so the empty stream
  reproduces the pre-2026-09-03 machine exactly; a non-family entry
  consults at bound 1 and pops nothing (consumption-invariance
  evidence: `scripts/choice-trace-corpus`, recorded in the evidence
  README). Promoted shapes (value- or pointer-embedded, pointer box or
  value box) are OUTSIDE the family and keep member 0 alone — gc probed
  nil-deref on all three (`transcripts/shapes.txt`).
- ROWS: `noodler/ifaces/{mv-iface-nil-call, iface-param-value-nil,
  global-iface-value-nil, mk-helper-value-nil, iface-dispatch-value-nil,
  spawn-iface-value-nil, spawn-iface-value-nil-devirt,
  spawn-helper-value-nil}` and `multipkg/nil-value-method-text` —
  `lane=membership`, `members=2`; gc decides the text per toolchain (and
  `-race` does not change it), so the K=32 alternating plain/`-race`
  draws exhibit one member per row: member 0 on `iface-dispatch-value-nil`,
  `mk-helper-value-nil`, `spawn-iface-value-nil-devirt`; member 1 on the
  rest.
- THE SPAWN TWIN (audit fix F1, 2026-09-03): the `go`-statement
  frame-entry twin (`spawnStep`, Multi.lean) draws the same pick — the
  first landing held member 0 only there, a LIVE observed-∉-modeled
  (audit): `go v.Val()` on a nil `*T` box whose concrete type gc cannot
  see gives the panicwrap text (default, `-l`, `-N -l` alike). Rows
  `noodler/ifaces/spawn-iface-value-nil` (box from an opaque helper —
  gc member 1), `spawn-iface-value-nil-devirt` (concrete type visible —
  gc devirtualizes ACROSS the spawn, member 0) and
  `spawn-helper-value-nil` (the control `go helper(v)`, an ordinary
  entry inside the child — gc member 1).
- MULTI-PACKAGE RENDERING (audit fix F3): `multipkg/nil-value-method-text`
  — the receiver type in package `pkgs/valuer`; gc: `value method
  pkgs/valuer.T.Val called using nil *T pointer` — the PATH qualifier as
  a differential observation, not a key convention.
- RE-LANING NECESSITY (audit finding, F2): the two strict PASS rows moved
  to membership (`iface-dispatch-value-nil`, `mk-helper-value-nil`) fail
  the PRE-EXISTING strict invariance check once the site exists — stage
  `nondet`, default stream = {nil-deref text}, adversarial variant =
  {panicwrap text} — so the re-laning is necessary and the (later)
  depth-routing guard is not load-bearing there.
- Ruling record: `docs/2026-08-31_qrow-rulings.md` (2026-09-03 record,
  «(2) panic-text, agree, demonic choice so both are admitted» —
  received by the [AGENT] coordinator and relayed to the implementing
  lane; cited as relayed). Implementation: BUG-087 (fixed 2026-09-03).

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

**The `sortSlice` op is UNREACHABLE from the frontend since 2026-09-04
(memo §3 row M, lane `fr4-rowm`):** `slices.Sort` is source-through — the
machine executes gc's own `pdqsortOrdered` (deps/go @ go1.26.5
`slices/zsortordered.go`, stenciled per element type) at EVERY ordered
kind, so the R13 MECHANISM is now the real pdqsort stencils for `Sort`
exactly as for `SortFunc` below — gc's member, a version-tracked (b)-pin,
not a machine choice; the "non-integer sorts land" day came and the
latitude did NOT become a machine choice. The `sort-slice` wire node is
refused by the decoder by name (audit fix round A3); the GoCore op itself
(`Stmt.sortSlice`, Machine/Ops arms) is dead code whose deletion is the
design-hygiene arc's item A11.

**The `slices.SortFunc` shim carries the SAME tie-order latitude**
(added 2026-08-22, launch audit V2 — previously recorded only in Go
comments, `tools/nativefrontend/genericshim.go:21-24` and
`stdlibshim.go:113-117`): the injected insertion sort realizes ONE
member of the unstable-sort envelope for comparator sorts, where ties
ARE observable (distinct structs comparing equal). Declared latitude,
comparator lane; relocating `slices.Sort` onto the shim (the parked
D8-F1 arc) relabels this row rather than retiring it.

**`slices.SortFunc` is source-through since 2026-09-03 (`stdlib-source-2`):**
the injected insertion sort is RETIRED; the machine executes gc's own
`pdqsortCmpFunc` (deps/go @ go1.26.5 `slices/zsortanyfunc.go`, stenciled
per element type), so the realized tie order is gc's member EXACTLY — a
version-tracked (b)-pin under G4(a) (memo §5), not a machine choice.
Rows: `stdlib-source/slices-sortfunc/sortfunc-ties-projected`
(tie-insensitive — the doc contract) and `sortfunc-ties-realized` (the
exact order; a toolchain that changes pdqsort moves this row, which is
the pin's purpose). The `sortSlice` op's row above records the
retirement: memo §3 row M landed 2026-09-04 (lane `fr4-rowm`) — `slices.Sort`
rides the same mechanism (`pdqsortOrdered`), so both sorts are gc's member.

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

### R16. Maximum allocatable size — the deterministic allocation-limit panic — (b) PINNED to gc linux/amd64 (`maxAlloc` 2^48, `hchanSize` 112, gc layout sizes) (added 2026-09-02, t5-maxalloc; fidelity decision 5(b) [USER])

- WHERE: spec §Making slices, maps and channels: "For slices and
  channels, if n is negative or larger than m at run time, a run-time
  panic occurs" — and NOTHING about an allocation limit; the map
  hint's effect is "implementation-dependent"; §Run-time panics leaves
  the error values unspecified. gc's RUNTIME adds a limit of its own:
  one request whose byte size exceeds `maxAlloc` panics
  deterministically (a recoverable `runtime.Error`, not an OOM abort) —
  `makeslice: len out of range` / `cap out of range` (slice.go:102–115,
  len blamed first, golang.org/issue/4085), `makechan: size out of
  range` (chan.go:86–89, threshold `maxAlloc - hchanSize`, a
  `plainError` with no `runtime error:` prefix), `growslice: len out of
  range` (slice.go:191–252, on the GROWN cap, or an `int` overflow of
  the new length); `makemap` CLAMPS an over-limit or negative hint to 0
  (map.go:60–67) and never panics. Machine: `Platform.maxAllocBytes`,
  `.chanHeaderBytes`, `.intExclusiveUpperBound`, `.wordBytes`/`.maxAlign`
  pinned at `gcAmd64` (Platform.lean, since design-hygiene A5 — the R16
  envelope statement lives there), read by Ops.lean's `maxAllocBytes`,
  `chanHeaderBytes`, `intExclusiveUpperBound` and `tySizeAlign
  platform`, consumed at the `makeSlice` /
  `makeChan` arms of `applyStmtOpCore` and the `appendSlice` spill path
  of `applyStmtOp` (Machine.lean), each BEFORE materialization; the
  `makeMap` arm's pre-slice negative-hint panic (an older gc string
  the pinned oracle never produces) REMOVED — dead code in fact, since
  the native frontend did not lower the hint at all (BUG-082 — FIXED
  2026-09-02 on the `bug082-maphint` lane: `emit.go` emits the hint as
  the make-map node's optional `hint` field, NativeToIR decodes it into
  `initialSpace`, and this arm evaluates it and ignores its value; the
  twin-wire pin moved with it, [USER]-authorized — BUGS.md BUG-082;
  evidence docs/evidence/2026-09-02_bug082-maphint/).
- THE PIN — three facts from one implementation: (i) the bound, 2^48
  bytes (heapAddrBits 48; STRICT — a request of exactly 2^48 passes
  the check and then fails to ALLOCATE, behavior 1 below); (ii) the
  channel header, 112 bytes (a gc-internal struct size with a 112-byte
  observable: `make(chan byte, 1<<48-111)` panics, `1<<48-112`
  allocates); (iii) the ELEMENT LAYOUT (go/types `gcSizes`, WordSize 8
  / MaxAlign 8, padding included — `[]struct{int64; byte}` panics from
  2^44+1 elements because the element is 16 bytes, not 9):
  `tySizeAlign` transcribes `gcsizes.go` arm for arm, the `sync`
  primitives are `unsafe.Sizeof`-probed (8/24/16/12), and it FAILS
  CLOSED on an unsupported or unknown type. Since C2 (2026-09-05,
  `docs/2026-09-05_c-arc-c2-design.md`) it descends the dependency-
  ordered type table by INDEX (no fuel: the old `typeResolutionFuel`
  1024 bound and its "type nesting too deep" refusal are gone —
  exhaustion is unrepresentable on an accepted program); a struct's
  field list is walked by `structSizeAlignWith` at the enclosing
  bound, so field COUNT never touches the descent (audit fix round F1,
  2026-09-02: an earlier cut spent fuel once per FIELD and refused flat
  structs of ≥1023 fields as "type nesting too deep" — downgrading,
  for `make([]W, -1)`, gc's `makeslice: len out of range` panic to a
  refusal; probe `fuelcliff` in the evidence dir, 1023- and 5000-field
  structs, all four request shapes match gc post-fix). The layout realization is
  what the frontend's go/types Sizes config already assumes (R1's
  entanglement), now visible machine-side.
- PLAUSIBLE ENVELOPE: any positive bound, with the panic-vs-clamp
  choice free per request class (a negative map hint has panicked in
  other gc runtimes; go1.26.5 clamps); on 32-bit gc the bound is
  2^32-1 and moves WITH R1's width (an `int` cannot express a length
  ≥ 2^31 there, so the slice panic is live only for element sizes ≥ 3:
  elemSize 2 gives at most 2·(2^31−1) = 2^32−2, not > 2^32−1; elemSize
  3 first exceeds it — audit fix round F2 corrected "≥ 2"), and the
  channel header is 64 bytes on 386 (4-byte words, rounded to maxAlign
  8), not 112, so the channel threshold `maxAlloc − hchanSize` moves
  too. A machine parameter `{maxAlloc, headerBytes, layout}` is the
  honest shape; this row pins the gc linux/amd64 point, as R1 pins the
  width.
- TWO BEHAVIORS, ONE LIMIT (fidelity decision 5 [USER] 2026-08-31):
  behavior 2 — the request EXCEEDS the limit → deterministic panic — is
  MODELED here (5(b)); behavior 1 — the request passes the check and
  the allocation FAILS (fatal "out of memory", unrecoverable) — is NOT,
  and stays under doctrine register #7's rider (allocation-succeeding
  runs) toward discrepancy D-001's bounded-very-large memory model.
  KNOWN-OUTSIDE BAND, recorded — a DETERMINISTIC-PANIC RESIDUAL of
  5(b), NOT a rider case: `append`'s check is decided on the NEW
  LENGTH's byte size — choice-free, because `applyStmtOp_appendSlice_
  congr` (MachineSound) states the spill outcome CLASS is stream-
  independent and a cap-based check would falsify it — while gc's is
  on the grown cap: gc panics iff `capmem > maxAlloc` with `capmem =
  roundupsize(nextslicecap(newLen, oldCap)·esize) ≥ newLen·esize`; the
  machine panics iff `newLen ≥ 2^63 ∨ newLen·esize > 2^48`. So machine-
  panics ⊊ gc-panics: where newLen fits and the grown cap (≈1.25×) does
  not, gc raises a recoverable `runtime.Error` and the machine
  allocates (observed ∉ modeled). gc never reaches the allocator there,
  so the band is not an allocation failure and does not sit under
  register #7's rider; it is the residual that scopes "behavior 2
  MODELED" to "modeled except this band". Corpus-unreachable (it needs
  an existing >2^47-byte slice or `unsafe.Slice`; gc witness: probe
  append-growth-over-unsafe).
- EVIDENCE: GC — the probe matrix `docs/evidence/2026-09-02_t5-maxalloc-
  probes/` (go1.26.5 linux/amd64; both sides of every boundary probed);
  corpus `builtins/make-maxalloc/*` (14 rows born PASS — slice len by
  variable / constant / int64 / padded struct, cap, len-and-cap blame
  order, chan byte / header boundary / int64, the chan zero-size-
  element control at 1<<62, recover ×2, and the two gc-truth map-hint
  rows over / negative (no panic; they reach the machine arm since the
  BUG-082 fix) — plus `map-hint-eval-order`, born RED on BUG-082's
  Cases line and flipped PASS by its fix the same day, with the 13
  `builtins/make-map-hint-eval/*` rows pinning the hint's side effects,
  panics, once-ness, types and order (docs/evidence/2026-09-02_bug082-
  maphint/); red-first measured against the pre-slice golean binary: chan
  rows `ok`, slice rows cgroup-killed materializing, recover-chan 0). NOT corpus-expressible: the just-under controls (gc: fatal OOM;
  machine: eager backing materialization grinds to the wall clock —
  BUG-078 residual (2)), `make([]struct{}, huge)` (same materialization),
  and any `append` past the limit. XIMPL (32-bit gc, gccgo, tinygo
  bounds) is the evidence class that would size the envelope.
- RE-ENVELOPE OBLIGATION + COST: a second `Platform` instance (A5,
  2026-09-04: the record `Platform` carries R1's width and R16's three
  numbers TOGETHER — `def gc386 : Platform := …` is the re-envelope's
  core half; the instantiation point is `platform`) — LOW, mechanical;
  worthless until a second oracle exists. The
  D-001 model (an allocation-failure outcome for behavior 1, a budget
  in every statement) is the larger owed change and is NOT this row's.

---

### Library realization under stdlib source-through — the (b)-pin posture, stated once (added 2026-09-03, stdlib-source-1; G4 ruled (a) [USER, relayed])

Since `stdlib-source-1` the machine executes the PINNED GOROOT text of
`strings`, `strconv` and their pure closure (`docs/2026-09-03_stdlib-boundary-design.md`
§2.1.2, §6; `docs/stdlib-admission-register.md`). Source-through
realizes gc's member of every library-DOC envelope because it lowers
gc's implementation; the ruling (G4 (a)) is to RECORD each doc-latitude
point as a version-tracked (b)-pin here, reified as a choice site only
on consumer demand. The census of the six slice-1 functions' doc
comments at the pin: **no latitude clause** —
`godoc:strings.Fields@go1.26.5` ("as defined by unicode.IsSpace" — a
closed table), `godoc:strings.TrimSpace@go1.26.5` ("as defined by
Unicode"), `godoc:strings.Split@go1.26.5` (all four edge cases
specified), `godoc:strconv.FormatUint@go1.26.5` /
`godoc:strconv.FormatInt@go1.26.5` (exact digit alphabet),
`godoc:strconv.ParseUint@go1.26.5` (error type, value and sentinels
specified). They are class (c) FORCED by the docs; the differential rows
`stdlib-source/*` pin the class. Two REALIZATION facts are recorded
rather than latitude: (1) `internal/bytealg`'s portable twins replace
the amd64 assembly (the substitution table) — the same contract, no
observable difference by the Go project's own tests; (2) the
illegal-base panic text `strconv: illegal AppendInt/FormatInt base` is
gc's realized string (R9's class), now forced by lowering gc's body.
Future source-through packages with doc-latitude vocabulary ("not
guaranteed", "may", "implementation-specific" — `slices.SortFunc`'s tie
order, `strings.Builder.Cap`, `math`'s asm-vs-Go last ulp) land their
R-rows here at admission (register rule). Evidence for the slice-1 census: `docs/evidence/2026-09-03_stdlib-source-1/`.

### R17. `print`/`println` output FORMAT — (b) PINNED to gc go1.26.5 `runtime/print.go`, version-tracked (added 2026-09-04, stdlib slice 3; gate G2 RULED [USER], relayed)

- WHERE: spec#Bootstrapping — "formatting of arguments is
  implementation-specific" and the built-ins are "not guaranteed to
  stay in the language" (verbatim at the `deps/go` pin). The observable
  is the program's fd-2 byte stream — in-language (a `print`
  statement), compared byte-exactly since this slice through the
  `output` observation field (`StepEvent.out` → `Readout.output`; G-OUT).
- MACHINE: `renderPrint`/`renderPrintOperand` (Machine.lean) transcribe
  `runtime/print.go` @ go1.26.5 for exactly the kinds whose rendering is
  a pure function of the value: `printbool` (`true`/`false`),
  `printint`/`printuint` (decimal, `-` for negatives; a defined type
  prints as its underlying kind — `print` never calls methods),
  `printstring` (bytes verbatim); `println` = operands joined by
  `printsp` (` `) with `printnl` (`\n`) after the last; `print` = the
  concatenation. Pinned by rows `builtins/print/*` (13 strict green) and
  by 120 `$GOROOT/test` files MATCHING with their output compared
  (`docs/evidence/2026-09-04_stdlib-slice-3/gotest-results.tsv`).
- FAIL-CLOSED EDGES (BUG-093): floats/complex — gc's
  `printfloat64` is `internal/strconv.AppendFloat(v, 'g', -1)`, the
  shortest round-trip decimal, a go1.26 CHANGE (commit 9035f7ae
  "runtime: use internal/strconv"; 1.25 printed `+1.500000e+000`) —
  which is precisely why this is a VERSION-TRACKED pin and not a spec
  envelope; the zero-operand spellings; prints during `$pkginit`;
  PERMANENT refusals for the address-printing kinds (ledger §5.1 item 3).
- Plausible envelope: any formatting (the sentence says so); the pin is
  what makes the equality lane possible. PERMANENT-pin candidate of the
  R9/R10 class (the same runtime printing code); "not guaranteed to
  stay" is a re-check obligation at every oracle pin move (the print.go
  excerpt lives in the evidence dir). Claims about print BYTES never
  transfer beyond gc 1.26.x.

### R18. Concurrent `print` ORDER — (a) ENVELOPED via L1 at REGISTRY granularity, with a LIVE re-envelope obligation (added 2026-09-04, stdlib slice 3; obligation recorded at its audit fix round C1, 2026-09-05)

- WHERE: spec#Bootstrapping says nothing about ordering across
  goroutines — the order of two goroutines' print statements is the
  SCHEDULE. gc: each statement is atomic under `printlock`
  (runtime/print.go:60-87), so the realizable members are statement
  orders, never a byte interleaving within a statement.
- MACHINE: output is a TRACE — the driver folds each step's
  `StepEvent.out` in step order (`execProgLoopOut`), so the set of
  possible `output` strings is the set of statement orders the L1
  envelope admits; the membership lane enumerates it (the path
  enumerator carries a per-path accumulator; `engine=dedup` REFUSES
  printing rows by name — output is a trace, its nodes key on state).
  Row `builtins/print/goroutine-interleaving` (membership, members=2:
  {`a\nb\n`, `b\na\n`}); strict rows are single-goroutine or
  order-forced (`goroutine-ordered`). No new `ChoiceSite`: the event is
  not a choice, the schedule is.
- **THE OBLIGATION (C1): the machine's L1 switches only at REGISTRY
  boundaries and back-edges, so a registry-free run of SEVERAL prints is
  atomic on the machine while gc may preempt between the statements.**
  g1 = {print a; print b}, g2 = {print c}: the enumerator admits exactly
  {abc, cab}; gc can realize `acb` (the audit reported 1/300 draws; the
  lane's own 600 draws — 300 plain, 300 `-race` — exhibited only
  abc/cab: `docs/evidence/2026-09-04_stdlib-slice-3/c1-probe/`, and a
  sample that is not observed is not a bound). A membership row over
  this shape would be observed∉modeled at the byte level the moment gc
  samples it — so NO corpus row is written (a flaky gate is not a
  record); the shape is rowed as ledger FR-30 with its fix direction:
  a scheduling point between statements (an L1 consult at the
  statement boundary, the C2 back-edge precedent) or an explicit
  output-order latitude at the fold. Until then, concurrent-print
  claims transfer only at registry granularity.

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

R6 (float→int out-of-range),
select-with-select
rendezvous (Multi.lean:804/:813), racy programs (C10 — by doctrine),
uintptr observations, `go` during `$pkginit` (StepFn.lean:511–525).
Each is honest (visible red, never a wrong answer); none is a fidelity
achievement. E6 (len/cap hoist shapes) LEFT this list 2026-09-05 (lane
e13-b): the refusal stood in for E13's latitude, which is now enveloped
(`unseqPanic`) — the first refusal of this list retired into an
envelope rather than a pin — and RE-ENTERED it the same day, NARROWED,
at the lane's audit fix round: the envelope reaches only material the
frontend probes, and on the unprobed subclasses (assignment targets,
address-of operands, `recover()`, allocating conversions) the narrowed
A6 guard refuses again (E6's fix-round bullet) — and NARROWED AGAIN at
the lane's re-audit fix round the same day (E6's re-audit bullet: the
target / address-of / `recover()` / allocating-conversion subclasses are
probed now; the guard's residue is the call-bearing compound target and
the receiver/forced-target/inline-conversion corners). The STRUCTURAL-
ALLOCATION refusal (E13 residual 5) joins it as its own entry. Count:
the five items above + E6 (narrowed) + the structural-allocation class
= 7 entries.

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
- **U-6 Atomics — MODELED (wave 1, 2026-09-03; was "Future atomics")**:
  mem#atomic pins sync/atomic to SC — verbatim: "The preceding
  definition has the same semantics as C++’s sequentially consistent
  atomics and Java’s volatile variables" (quote corrected at the P2
  audit) — a considered design commitment with recorded rationale
  (gomm: a conforming implementation may NOT weaken these to
  acquire/release) — FORCED, and realized as forced: the atomics arc's
  wave 1 (Q-ATOMIC RULED [USER] 2026-09-02 option A′; design note
  `docs/2026-09-03_atomics-w1-design.md`) models the integer core
  (`Load/Store/Add/Swap/CompareAndSwap` × `Int32/Int64/Uint32/Uint64/
  Uintptr`, direct calls and the typed wrappers) as ONE fused registry
  step each (`applyAtomicOp`, Machine.lean — the envelope statement is
  there), so SC is the L1 interleaving of indivisible steps with ZERO
  new choice sites (the census is unchanged); the executable check
  that the realization is neither wide nor narrow is
  `sync/atomic-frontier/mp-litmus` (membership exactly {0, 1, 11}, the
  SC-excluded 10 absent). The surrounding-plain-access envelope is
  C10's (mem#restrictions), realized by the atomic ACCESS KIND at the
  addressed cell (`atomicOpKind`, Race.lean — TSan's realized access
  and mem#model's operation kind coincide for atomics) with the
  per-address atomic clock carrying mem#atomic's synchronized-before
  (Load acquires; Store release-STORES — an overwrite, gc's/C++'s
  realization; RMWs release-acquire; a failed CAS acquires). Refused
  by name for wave 2: `atomic.Value`/`Bool`/`Pointer[T]`, `And*`/`Or*`,
  the `unsafe.Pointer` family.
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
   (U1 closed), full literal envelope user-ruled; the residual
   cross-goroutine-prune narrowing CLOSED 2026-09-02 (pool-level
   `pruneForeign` — see E9's entry).
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
   envelope treatment or linearization. **E13 LEFT this item
   2026-09-05** (lane e13-b, [USER] ruling (b), relayed by the [AGENT] coordinator): the sibling-panic axis
   is the FIRST realization of exactly this treatment — an
   `unseq-probe` statement + the `unseqPanic` pick, membership rows
   certifying both panics; the same mold (a probe at the operand's
   lexical position, a pick on the panic path) is the candidate
   mechanism for E3/E4's target operands once the assignment path is
   opened (design `docs/2026-09-05_e13-b-design.md` §6 item 4). Sequential-only,
   moderate cost — above R1/R4-class pins because it is
   oracle-visible in panic-selection shapes today. **E5 LEFT this
   item 2026-09-02** ([USER] ruling): its re-envelope obligation is
   WITHDRAWN — the phase boundary is FORCED and gc's early store a
   deviation (L-016); widening toward it would take the machine past
   the spec.

Below the line (recorded, deliberately not queued): R1 int width
(waits on any 32-bit oracle lane — XIMPL evidence class; R16's
allocation bound and layout move WITH it, 2026-09-02), C7 select
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
   the owed record discharged, §9 flag 2; since A5 the caveat sits on
   `gcAmd64`, Platform.lean.)
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
    replayed. The residual cross-goroutine delete-prune narrowing
    recorded at E9 was CLOSED 2026-09-02 (pool-level `pruneForeign`).
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

    **Q-U4RESIDUAL — RULED [USER] 2026-09-02, option (A): where go_mem
    and TSan DISAGREE on what a race IS, go_mem wins** (ruling sheet
    `docs/2026-08-31_qrow-rulings.md` row 9 + appendix record; the
    quotes reached the recording worker by [AGENT]-coordinator relay,
    citation not firsthand). The HB EDGE SET stays TSan's realized set
    (the paragraph above is unchanged); the ACCESS KINDS a sync op puts
    on its primitive's own words are now mem#model's read-like/write-
    like operation kinds RECORDED BESIDE what TSan realizes (Race.lean
    `syncEntryKinds`/`syncReleaseTailKinds`, each access at its gc
    word), so a plain access beside `RUnlock`/`Unlock`/`Add`/`Done` —
    racy by mem#model's definitions, invisible to TSan under
    `race.Disable` — REFUSES. Three things this ruling fixes in the
    doctrine: (i) go_mem's semantics for racy programs is BOUNDED, not
    C-style undefined behaviour — mem#restrictions: an implementation
    may "report the race and halt execution", or else a word-sized racy
    read observes some actually-written value (no out-of-thin-air) and
    multiword values may tear; the machine's refusal IS the permitted
    report-and-terminate branch, taken on detection; (ii) the bounded-
    VALUE branch for racy programs is deliberately UNMODELED — register
    #4's existing scoping ("the racy limited-outcomes envelope is
    declared OUT of product scope"), now explicitly recorded here with
    the ruling as its ground: the machine is the substrate for a
    verification tool, refusal-freedom is the proof obligation
    (DRF-guarantee shape), over-refusal costs completeness and never
    soundness, under-refusal would be unsound ([USER]: "we're 'failing
    more' which means we can only verify code that is correct"); (iii)
    a refusal NEVER counts as a pass — the racy lane's three-way rule
    (our refusal + `-race` green) files the go_mem-racy/TSan-green rows
    as an investigation whose ruled outcome is "racy by go_mem, TSan
    incomplete"; they are pinned born-FAIL against gc's `ok`
    (`race/gomem-only/*`, BUGS.md BUG-084's Cases line — the record of
    the designed divergence) so the cost stays visible. Removing:
    nothing — a doctrine decision, not latitude; the U-ledger's U4 is
    CLOSED (BUG-080) with residual (a) closed by this ruling.

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
   `gcAmd64` (Platform.lean; was `IntKind.bits?` until A5) — pin,
   envelope {32,64}, transfer caveat, XIMPL gate. (The flag stood 20 days after being recorded
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
   alignment rule differs per site). **RESOLVED by G-U 2026-09-04**: the
   alignment rule is uniform (pop iff bound ≥ 2) at every site; the
   realization shift it caused on fixed streams is certified by the
   choice-trace bijection (`docs/2026-09-04_c-arc-gu-design.md`).
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

- (a) ENVELOPED: 11 sites / 13 entries — C1, C2, C3, C4, C5, C6, C8, C12, E6
  (via E13's `unseqPanic`, zero sites of its own — the retired len/cap
  refusal row, kept as the history of what stood in for the latitude), E9,
  E13, R2, R18 (via L1, zero new sites; its statement-granularity
  obligation is live).
- (b) PINNED: **17 entries** — concurrency: C9; sequential order: E2,
  E3, E4, E7, E10, E11, E12; representation/runtime: R1, R8,
  R9, R10, R11, R12, R15, R16, R17.
- (b-n) NARROWED with recorded caveat: 7 — C7, E8, R3, R4, R5, R7, R13.
- (c) FORCED: the §4 list (machine follows; BUG-005's mandated
  point — removed-before-reached never produced — CLOSED 2026-08-19
  by the (L) surgery's delete-prune); rows carrying the tag: E1, E5
  (since 2026-09-02), E14.
- (d) UNKNOWN: 6 (U-2 … U-7; U-1 probed and admitted at W3.2 stage C, 2026-08-20).
- REFUSED standing in for latitude: 6 (§5's listed items, re-derived at
  the e13-b audit fix round: R6, select-with-select rendezvous, racy
  programs, uintptr observations, `go` during `$pkginit`, and E6 —
  narrowed — back since the fix round; the previous "9 → 8" was not
  derivable from the list, audit R12).
- Known-≠-oracle deterministic points (the honesty-critical list):
  E2 (VALUE axis, its EARLY-realized kinds — BUG-101's two rows), E3,
  E5, E7, R3(escaping path), BUG-104 (a compound target's hoisted
  address/key temp — five rows). THREE CLASSES inside one list, stated
  per row: E3, E7, R3 are (b)/(b-n) PINS with gc on another conforming
  member (re-envelope debts, §7), and E2's value axis is a (b) PIN of
  the same kind whose gc-elsewhere member is FILED as an open bug
  (BUG-101) rather than only recorded; **E5 is a (c) FORCED row on which
  gc DEVIATES** (L-016, [USER] ruling 2026-09-02) — it stays listed
  because the oracle disagrees with the machine there, but the
  disagreement is gc's, not a debt of ours; **BUG-104 is an OPEN
  observed-∉-modeled bug** (no pin and no site — the frontend's eval-once
  temp; the fix is an envelope) listed because the oracle's deterministic
  answer is outside the machine's set on five rows. (E13 added 2026-08-20
  and LEFT 2026-09-05 — re-enveloped at lane e13-b, gc's member is IN the
  set on both former axes; E2/BUG-101/BUG-104 JOINED 2026-09-05 at the
  e13-b final verification fix round, R''-1 — the doctrine's register #2
  sentence had claimed the two bugs were listed while this list did not
  carry them, and E2's heading had said `known ≠ gc` without a list
  entry; the doctrine sentence was edited in the same change, per its
  standing rule; the C2+C3 send-then-spin wedge LEFT this list 2026-08-21
  — W3.2 stages C/D re-enveloped it, register #1 discharged; E5's class
  changed 2026-09-02.)

### 10.1 Movement and history (NOT membership)

Nothing in this block is a class member by virtue of being named here.

- **E13-b FINAL VERIFICATION FIX ROUND (2026-09-05, [AGENT]; records
  only, no rule change): E2's value axis, BUG-101 and BUG-104 JOIN the
  known-≠-oracle list (R''-1)**; BUG-104 (renumbered — `c-arc-c2` holds
  the lane's former number; the entry's merge-train note) gains its receive and method-call
  spellings (5 rows, R''-2); E13's residue (3) corrected — receivers
  reaching `emitExpr` ARE probed, the unprobed receiver residue is the
  `receiverAddr` path (R''-4, E14's sub-axis recorded); E12's value pin
  carries the hoisted-allocating-conversion exception (R''-8, row
  `bytes-conv-value-vs-mutating-call`); the membership tally re-derived
  39 → 56 (R''-6). Counts unchanged: (a)/(b)/(c)/(d)/REFUSED as below.
- **E13-b RE-AUDIT FIX ROUND (2026-09-05, [AGENT]): E2's PANIC axis
  ENVELOPED, E6's refusal narrowed to a one-row residue** (REFUSED count
  re-derived: 7 — the structural-allocation class counted as its own
  entry) — the fix round's target suppression had pinned the
  events-first member where gc realizes the other (a regression the
  re-audit named); phase-1 target operands, address-of operands, the
  hoisted `recover()` residual and hoisted allocating conversions are
  probed now (E2, E6, E13 bullets); the six fix-round designed reds
  lower onto BUG-083's line; BUG-104 filed (the compound target's
  hoisted temp — pre-existing on main); BUG-101 gains its slice-kind
  row. (a) entries unchanged in number: E2 is now split (panic axis (a)
  via E13, value axis (b)).
- **E13-b AUDIT FIX ROUND (2026-09-05, [AGENT]): E6 RE-ENTERS §5
  narrowed** (REFUSED count re-derived: 6) — the envelope covers probed
  material only; the target / address-of / `recover()` / allocating-
  conversion subclasses REFUSE by name again (E6 bullet), the
  structural-allocation class is a new named refusal (E13 residual 5),
  and the value axis reached through the len shape is BUG-101 (E12's
  obligation, now with a filed witness). E13 keeps (a) for the probed
  axis; its obligation wording is "measured-discharged for the probed
  axis", not DISCHARGED.
- **(b) 18 → 17, (a) 11 → 13 entries / 10 → 11 sites
  (2026-09-05).** **E13 moved (b) → (a)** by [USER] ruling (option (b)
  of E13's four-way treatment, Mike 2026-09-05, relayed; lane `e13-b`):
  the sibling-panic order is the new `ChoiceSite.unseqPanic` — the
  second site added since the census became code — with its §0 mirror
  row in the same commit; **E6 RETIRED** from §5 (the len/cap and make
  refusals it inventoried stood in for E13's latitude and are deleted);
  E13 LEFT the known-≠-oracle list (gc's member is certified in the set
  on every row). E6 keeps a heading — tagged (a) via E13, zero sites of
  its own, the R18-via-L1 mold — so the history of the refusal that
  stood in for this latitude stays readable in place; it contributes
  no site and no envelope of its own. Recording agent [AGENT]; the
  envelope is the [USER]'s.

- **(a), 9 → 10 (2026-09-03).** **C12 ADDED** (Q-TRYLOCK, RULED [USER]
  2026-08-31 row 5, own-slice sequencing [USER] 2026-09-03, lane
  `q-trylock`): TryLock/TryRLock's spurious-failure member as the new
  `ChoiceSite.tryLock` — the first site added since the census became
  code (W3.2 stage A); the §0 mirror table gained its row in the same
  commit (the 2026-08-22 lesson: the exhaustiveness check protects the
  code, this table is what a reader consults). A new row, not a
  movement; C8's "zero new sites" stays true of the acquisition-ORDER
  latitude. Recording agent [AGENT]; the envelope is the [USER]'s.

- **(b), 16 → 17 (2026-09-02).** **R16 ADDED** (t5-maxalloc; fidelity
  decision 5(b) [USER] 2026-08-31): the maximum allocatable size — gc's
  deterministic allocation-limit panic class — pinned to gc linux/amd64
  (bound 2^48, channel header 112, gc layout sizes), the R1 mold. A new
  row, not a movement; its 32-bit point rides R1's. Recording agent
  [AGENT]; the modeling decision is the [USER]'s. **Audit fix round
  (2026-09-02, [AGENT]), body corrections only, no class movement:**
  F1 — the size function's fuel now bounds nesting DEPTH only (the
  first cut spent it per struct field; cliff at ≥1023 flat fields,
  probe `fuelcliff`); F2 — the 32-bit slice panic is live from element
  size 3, not 2, and 386's channel header is 64, not 112; F3 — the
  `append` band re-classified from "an allocation-failure case of the
  rider" to a deterministic-panic residual of 5(b) (gc raises a
  recoverable `runtime.Error` there; it never reaches the allocator).

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
  2026-08-19; its residual cross-goroutine delete-prune narrowing
  (recorded in E9) was CLOSED 2026-09-02 — E9 is an **(a)** row and
  was named in the (b-n) list only for that aside.
- **Heading tags completed 2026-08-22.** Three rows carried no class
  tag at all, so their class was readable only from the body — which
  is what let the enumerations drift unnoticed. Assigned from the
  bodies: **C10 → REFUSED** (its own CLASSIFICATION line: "not an
  envelope — a doctrine-decided boundary … fail-closed refusal", and
  §5 already lists "racy programs (C10 — by doctrine)"), **R13 →
  (b-n)** (body: "declared-unobservable narrowing", already counted in
  the (b-n) list), **R7 → (b-n)** (see above). C10 was already inside
  §5's count of 9; adding its heading tag changes no total.
