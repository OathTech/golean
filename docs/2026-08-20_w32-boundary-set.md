# The W3.2 boundary-set design note — slice 1's G1 gate artifact (2026-08-20)

**Status: AWAITING G1 REVIEW (Mike). No surgery has started; the
charter gates the slice-1 implementation on this note's approval
(`docs/2026-08-20_w32-re-envelope-charter.md` §Slice 1: "the
observable-set change gate in its largest instance").**

Ground truth: branch `w32-re-envelope` @ `10aad750`, tree clean. Every
`file:line` is against that commit. Every measured number in §1 and §6
was RE-RUN at this tip (not quoted from the 2026-08-12 record); the
runs are reproduced inline. Inputs of record: charter §Slice 1; the
design audit's G0 ruling (`docs/2026-08-20_semantics-design-audit.md`
§11 — Q1 tagged choice sites + Q2 step-event channel RIDE this slice);
essence-of-Go doctrine register #1; latitude inventory C2/C3/U-1;
nondeterminism doctrine requirements 1/2/4; the channel-logic park
record (`../channel-logic`, `docs/2026-08-10_channel-logic-arc-charter.md`
tail — read-only) whose three refutation families are the machine-checked
discovery record of the fused boundary.

---

## 1. The wedge, reproduced fresh at this tip

### 1a. The measurement

Probe (a), SEND-THEN-SPIN
(`docs/evidence/2026-08-12_scheduler-wedge-probes/send-then-spin/main.go`):
main makes a cap-1 channel, spawns a worker that sends 42 and then
loops with no further registry op, and receives.

gc (go1.26.5 linux/amd64, this session, binary rebuilt from the probe
source):

    exit0-and-prints-42: 60/60
    GOMAXPROCS=1:        20/20

Machine (`.lake/build/bin/golean` rebuilt at `10aad750` via
`GOLEAN_MEM_MAX=24G scripts/capped lake build golean`; wire JSON via
`go run ./tools/nativefrontend`):

    default stream, default fuel:  fuel-out
    exhaustive mod-2 depth-8 sweep (all {0,1} streams of length ≤ 8,
    511 streams incl. the empty/default, --fuel 100000):
        511 runs -> 511 fuel-out, 0 ok

The sweep's exhaustiveness argument is the recorded probe's closed
reachable-set argument, unchanged by anything landed since (every
consumption site this program reaches has bound ≤ 2; `Choices.consume`
reduces mod the bound, `State.lean:156-160`; consumption stops after at
most three width->1 boundaries). **`observed ∉ modeled` at the current
tip: gc's observation (exit 0, "42") is outside the machine's entire
stream envelope. Definitionally a bug (essence doctrine, the bug
definition), register #1, inventory §7 priority 1.**

Probe (b), REGISTRY-FREE SPINNER, re-run as the control: machine
`ok/7` on the default stream and on `[0]`, `[2]`, `[0,1]`, `[0,0,0,0]`;
`fuel-out` on `[1]`, `[1,0]`. gc's observation IS in the modeled set —
NOT the bug; its ∀-stream termination is the fairness quantifier's
later territory (`docs/2026-08-07_fairness-precision-note.md`), and §4
below states why this slice must not preclude that quantifier.

### 1b. Why, in the current machine's terms

Two fused seams produce the wedge, each with one owner:

1. **The fused effect boundary (C3).** `Config.atBoundary`
   (`GoLean/GoCore/Multi.lean:229-257`) marks PRE-op apply positions
   only — `.retV _ (.chanStK _ _ [] _ _)`, the select/sync/go apply
   shapes, the parked shapes, the terminals. The ONLY post-op boundary
   in the machine is the spawn-completion marker `.spawned`
   (Multi.lean:241, BUG-040's fix). A channel send's apply returns its
   successor configuration BARE (`stepFn`'s `.chanStK` apply arm,
   `GoLean/GoCore/StepFn.lean:447-452`: `applyChanOp`'s `.ok (c', s')`
   is returned directly, likewise the pairing successors built in
   `applyPairing`, Multi.lean:740-849) — so the op's effect and the
   issuer's subsequent private segment are one seamless run. After the
   worker's send wakes main, no scheduling point exists.
2. **Forced continuation (C2).** `stepMulti`'s non-boundary arm
   (Multi.lean:938-939, the `else stepThreadInto m m.cur ch`): between
   boundaries the running goroutine steps privately and CANNOT be
   preempted on any stream. The worker's registry-free tail
   (`for {}` = `.exec body env (.loop …)` cycling through
   StepFn.lean:551) contains no boundary shape, so the private run is
   infinite. Main — woken, runnable, in `runnableIdxs` — is never
   consulted again: the L1 site (Multi.lean:929-937) is only consulted
   AT boundaries.

The pair also poisons ∀-stream claim shapes: `TerminatesNormallyC` is
FALSE for this program (fuel-out on every stream) while gc terminates
it 60/60 — a ∀-stream theorem is exactly as strong as the envelope it
quantifies (nondeterminism doctrine, "The model").

The machine-checked discovery record: the parked `channel-logic-s4`
branch's three refutation families (park record, charter tail at
`f49752a6`) proved the narrowing from the proof side — panic variant
matching gc 500/500, spinner variant diverging (gc exit-0 100/100 vs
machine fuelOut) — before the doctrine named it a definitional bug.

---

## 2. The boundary set — what the widened machine gains

Per the G0 default ruling on OQ2 ("both together per the inventory" —
post-op points AND back-edge preemption), presented as separable
points so a strike narrows honestly. The audit's T-6 finding is the
design's mold: `Config.atBoundary` is one legible predicate and
`.spawned` is the existing precedent for a post-op boundary as a
first-class configuration — generalize that move, do not invent a
second mechanism.

### B1 — post-op scheduling points at ALL registry-op completions

**Mechanism.** A single marker configuration in `.spawned`'s mold:

    | opDone (sched : ChoiceSite) (inner : Config)
      -- registry-op completion marker; `sched` names the scheduling
      -- site the boundary consults (Q1 tag, carried in the config)

wrapping the op's successor configuration. The `sched` tag exists for
one honesty reason: the SPAWN emitter must keep today's exact default
schedule. At the `.spawned` boundary the current machine consults L1
(goroutine order; slot 0 = lowest-index runnable — BUG-040's shipped
behavior), while the new emitters' canonical member is
issuer-continues; one untagged marker would silently change the spawn
default wherever the parent is not the lowest-index runnable. So:
spawn emits `.opDone .l1Sched (.next k)` (bit-for-bit today's
default), every new emitter emits `.opDone .postOp inner`. Emitted at
every registry-op COMPLETION by the goroutine that performed the op's
step:

- channel apply outcomes that proceed (send commit, recv delivery
  entry, close) — wrapped where `stepFn`'s apply arm returns
  `applyChanOp`'s success (StepFn.lean:448);
- sync apply outcomes that proceed (`applySyncOp` successes,
  StepFn.lean:539);
- select commits (entry path `applySelect`, arrival path
  `commitClause` — `stepThread`'s `.commit` arm, Multi.lean:898-904);
- the pairing ISSUER's successor (`applyPairing`'s outcomes for the
  arriving goroutine). The passive partner is NOT wrapped: its
  delivery is part of the issuer's step, and it becomes schedulable at
  the issuer's very next boundary — the `.opDone` this rule just
  created — so wrapping it would add a no-op step and no latitude;
- the WAKE step's successor (`resumeThread`, `stepThread`'s blocked
  arm Multi.lean:866-868) — a parked op's completion is a completion;
- spawn completion: already `.opDone`-shaped — **`.spawned k` unifies
  into `.opDone .l1Sched (.next k)`** and its special-case machinery
  (`spawnedCont`, the strip arm Multi.lean:870-876,
  `step_spawnedMarker_elim`, `spawnedCont_of_*`) folds into the one
  marker's rules. One mechanism, as T-6 asks.

NOT wrapped: panicking outcomes (send-on-closed etc. — the
abort-window question is B3, deferred), and blocked outcomes (a park
IS a boundary shape already, Multi.lean:248-250,256).

`Config.atBoundary` gains one arm (`.opDone _ _ => true`); `stepFn`
gains one arm (`.opDone _ c => (c, s, choices)` — the strip, one step,
exactly `.spawned`'s cost model); the relation gains one rule
(`opDoneStrip : Step (.opDone sc c) σ c σ`); `isBlockedConfig` is false
on it; the detector sees it as a no-access step. Because
`applyChanOp`/`applySyncOp` live in `Machine.lean` (per-goroutine),
the marker appears in SEQUENTIAL runs of sync ops too — on both
drivers identically, so `execProg_single_eq_execStmt` re-proves on the
shifted-but-equal fuel accounting (cost surface, §5).

**The choice site.** The `.opDone` boundary consults a NEW tagged site
(Q1), not the bare L1:

    ChoiceSite.postOp    -- bound = |runnable|; slot 0 = the ISSUER
                         -- continues (the old machine's schedule);
                         -- slots 1.. = the other runnables in
                         -- goroutine order; consumed only at bound > 1

Slot 0 = issuer is the load-bearing canonicalization (audit C-2's
convention: slot 0 = the member the old machine realized): the
empty/default stream reproduces the CURRENT schedule exactly, so
widening only ADDS streams — literally, at the stream level, not just
the envelope level. §4 and §5 both rest on this.

**The spec argument (nondeterminism doctrine requirement 1 — the
governing text, verbatim, evidence class named).** Three layers:

- spec#Go_statements: "A 'go' statement starts the execution of a
  function call as an independent concurrent thread of control, or
  goroutine, within the same address space." — *independent*: the spec
  orders nothing between the issuer's continuation and any other
  runnable goroutine's progress. spec#Program_execution and the memory
  model give no ordering between one goroutine's post-synchronization
  progress and a woken partner's (inventory C3's anchor-from-absence:
  mem#chan rule (1) synchronizes a send before the COMPLETION OF THE
  RECEIVE — not before anything in the sender's continuation — so
  every member B1 admits is a scheduling-latitude observable, never an
  HB violation). Evidence class: spec text + memory-model
  anchors-from-absence.
- **Every added member is conforming-implementation-realizable**: gc
  ITSELF exhibits the flagship added member (the wedge's exit-0,
  60/60 in §1a) — the strongest possible answer to the too-wide
  question at this point, because a member a conforming implementation
  realizes cannot be outside the conforming envelope.
- Width bound: B1 admits only registry-granularity interleavings
  consistent with the blocking rules and HB — the same class C1's L1
  envelope was argued MAXIMAL over ("believed MAXIMAL at registry
  granularity", inventory C1). B1 removes an exclusion INSIDE that
  argued class; it does not extend past it.

**What it admits that the current machine excludes.** The wedge's
exit-0 trace, concretely, on the widened machine (site: pick):

    main spawns worker            -> .opDone (ex-.spawned) boundary;
                                     l1Sched: pick 0 = main (today's
                                     default, preserved by the tag)
    main reaches recv apply       -> pre-op boundary; l1Sched: pick main
    main parks (.blockedRecv)     -> worker sole runnable; no consume
    worker reaches send apply     -> boundary; sole runnable, no consume
    worker sends: PAIRING wakes
      main; worker -> .opDone     -> **THE NEW BOUNDARY.**
                                     postOp bound=2: pick 1 = main
    main delivers, returns 42     -> main terminal, worker runnable:
                                     L5 window: pick 0 = exit now
    => ok / 42  (exit 0)

Exit-0 is a member of the widened envelope on a short finite stream;
§1a's 511/511 shows it is a member of nothing today. It equally
discharges C3's two fixed-pointwise instances' whole CLASS (BUG-040
post-spawn, BUG-044 wake-then-main-terminal were the two probed
corners; B1 is the general rule they were corners of) and the U-1
mid-program members (§6).

**Granularity-ledger footprint.** None on access granularity: the
marker step performs no loads/stores, wide ops (U-5's
`appendSlice`/`copySlice`/`clearSlice`) remain single fused applies
INSIDE segments, and detector clocks advance only at HB edges, which
B1 does not add or move. One correction to the inventory's C2/C3 cost
prose is owed at landing: "race-detector segments shrink … clock
traffic grows" over-predicted — in this machine's design, boundaries
are scheduling points, not clock edges (`raceUpdate` advances clocks
at spawn/wake/pairing/sync EVENTS only, Multi.lean:1147-1158 ff.), so
the detector's cost from B1 is the Q2 rewrite it gets anyway, not
clock traffic.

### B2 — preemption points at loop back-edges

**Mechanism.** `Config.atBoundary` gains the loop re-entry shapes:

    | .next (.loop _ _ _ _)       => true   -- body completed, re-enter
    | .continuing (.loop _ _ _ _) => true   -- continue re-entry
    | .next (.mapIterK …)         => true   -- range-map iteration pick

(the executable arms these classify: StepFn.lean:551, :660, :602-630;
the frontend lowers all counted/range-over-int/slice loops to `.while`,
so `.loop` covers them; `mapIterK`'s `.next` position is the one
iteration form with its own frame, and it is ALREADY a choice-consuming
position — making it a boundary aligns the two disciplines). No new
configuration constructor; no new step; the shapes exist and gain
`atBoundary = true`.

**The choice site.**

    ChoiceSite.backEdge  -- bound = |runnable|; slot 0 = the CURRENT
                         -- goroutine continues (the old behavior);
                         -- slots 1.. = others in goroutine order;
                         -- consumed only at bound > 1

Same canonical-slot convention, same consequence: default stream =
old schedule; sequential pools (bound 1) consume nothing and behave
identically.

**The spec argument.** The spec is SILENT on scheduling — C1's row:
"pure omission latitude bounded only by the blocking rules and the
memory model"; no text distinguishes a boundary-free segment from any
other program point, so a schedule switch at a back-edge is as
conforming as one at a registry op. The realizability half: gc itself
performs ASYNCHRONOUS preemption at arbitrary points, including inside
registry-free loops, since Go 1.14 (runtime docs; the
`asyncpreemptoff` GODEBUG knob documents the mechanism) — so back-edge
switches are a strict SUBSET of what one conforming implementation
demonstrably does, and mem#badsync's registry-free-spinner sentence
("The loop in main is not guaranteed to finish") is normative-adjacent
confirmation that implementations need not honor a spinner's monopoly.
Evidence classes: spec silence + gc runtime documentation + measured
gc behavior. Too-wide check: B2 members are still
goroutine-step-granularity interleavings respecting blocking/HB —
inside C1's argued-maximal class.

**What it admits.** Schedules in which a goroutine inside a
registry-free segment is descheduled at an iteration edge: the spinner
can lose the processor without ever reaching a registry op. The wedge
does NOT need B2 (the §B1 trace reaches exit-0 without it); B2's value
is different and twofold:

1. **It is what makes fairness non-vacuous** (§4): a
   `Fair : Choices → Prop` can only demand that a persistently
   runnable partner eventually runs if a scheduling point EXISTS in
   the monopolist's tail. Without B2, the later liveness tier's
   fairness hypothesis would be unsatisfiable on exactly the programs
   it is for — every fair-termination claim over spinner-adjacent
   shapes would be vacuously true or unstatable. With B2, "fair ⇒ the
   partner progresses" becomes a provable implication.
2. It admits gc-realizable members B1 alone excludes: e.g. worker
   spins k iterations AFTER its send, then main runs — observable as
   distinct schedules wherever iteration count feeds an observable
   (time-free programs rarely observe it; abort-ordering shapes do).

Scope honesty, restated from the charter: widening only ADDS streams —
the registry-free spinner's divergent branches (always-pick-the-
spinner) survive B2, exactly as they should; ∀-stream termination of
probe (b) remains FairStream's question, not this slice's.

**Granularity-ledger footprint.** None on accesses (no new steps, no
clock edges). One ledger sentence updates: the "private segment"
notion in the segment-HB prose shrinks from "between registry ops" to
"between boundaries" — with the explicit note that segments' CLOCKS
are unchanged and only the interleaving of recorded accesses refines.

### B3 — the abort window (CONSIDERED, proposed DEFERRED to slice 5)

The remaining fused seam after B1+B2: `execProgLoop` classifies
`panicMsg?` BEFORE stepping (Multi.lean:1421-1422), so the moment any
goroutine's chain reaches `.panicked`, the program aborts on every
stream — no other goroutine may take another step. The L5 window is
exactly this latitude at main's NORMAL terminal; the symmetric window
at a panic terminal ("{abort now, one more pool step}*") is the
missing analogue. Deferral argument: every U-1 member the gc probe
exhibits (§6) is already admitted by B1+L5 — the partner's progress
happens BEFORE the raise (at the post-op boundary) or between main's
terminal and exit (L5). A member requiring the panic-window
specifically would be partner progress strictly AFTER the raise,
distinguishable only by output-interleaving with the panic message on
stderr — no clean oracle observable in our harness. Slice 5's
completeness enumeration (charter: "abort/termination ordering the
known class") is the right owner; the trigger to un-defer is a probe
or corpus shape whose observable separates post-raise progress.
Recording that here satisfies the charter's "the design note records
what it leaves open".

### Interfaces deliberately not foreclosed (charter §Boundaries)

- **Q-ATOMICITY / Q-GOEXIT (F4-owned):** if atomics land as single
  fused registry ops, they inherit B1's marker like any sync op — the
  postOp site takes new EMITTERS without a shape change; Goexit's
  terminal is a boundary shape already. Nothing in B1/B2 presumes
  their answers.
- **Q-ATOMIC's SC-from-L1 story** (slice 2, "directly coupled to
  slice 1's boundary set"): B1 keeps the property it depends on —
  scheduling points are TOTAL orders over registry-granularity steps;
  SC for fused atomic ops falls out of L1 exactly as before, now with
  more interleavings, all still sequentially consistent.
- **NPDRF/register #5**: B1+B2 shrink the registry-path-vs-full-
  interleaving residual (more points = closer to fine granularity) but
  do not close it; the mover/NPDRF theorem resumes AFTER this widening
  (doctrine: "the reduction line resumes AFTER the machine widens"),
  over the new point set — slice 5.

---

## 3. The Q1/Q2 design — the surgery's foundation (G0-ruled riders)

The G0 ruling (audit §11) rides both on this slice: doing the
`Choices` reshape untagged and re-tagging later is two reshapes.

### Q1 — tagged choice sites

    /-- One constructor per census row (latitude inventory §0 +
    this note's additions). The census as a datatype: adding a
    consumption site REQUIRES a constructor, so the F16-style doc
    sweep is retired by exhaustiveness. -/
    inductive ChoiceSite where
      | mapIter | appendSpill
      | l2Entry | l2Arrival | l4Waiter
      | l1Sched | l5ExitWindow
      | postOp  | backEdge          -- this slice's additions
      deriving Repr, DecidableEq

    /-- Per-site consumption policy, ONE table (audit C-1's five
    bespoke width-1 behaviors become declarations). -/
    structure SitePolicy where
      /-- Consume even at bound 1? (mapIter: true — §9 flag 5;
      every other site: false.) -/
      consumeAtOne : Bool
      /-- Docstring-checked, not machine-checked: slot 0 is the
      canonical member (C-2's convention), stated per site. -/
      canonicalSlot0 : String

    def ChoiceSite.policy : ChoiceSite → SitePolicy := …

    /-- THE one consumption combinator. `Choices` stays `List Nat`
    (the carrier does not change in v1 — streams stay writable by
    hand and by the enumerator); the SITE identity is declared at
    every consumption, which is what makes a labeled trace (Q2)
    and per-site enumeration policy (§5d) expressible. -/
    def Choices.consumeAt (site : ChoiceSite) (bound : Nat)
        (ch : Choices) : Nat × Choices :=
      if bound ≤ 1 ∧ ¬(site.policy.consumeAtOne) then (0, ch)
      else ch.consume bound

Every current `Choices.consume` call site converts to `consumeAt` with
its census tag; `consume` becomes private to `consumeAt`. The
site-vs-policy nuances the audit catalogued (`applySelect`'s
load-bearing singleton NON-consumption, L4/L1's singleton-list special
cases, mapIter's consume-at-1) become table rows instead of per-site
discoveries. The fairness constraint's first half — "scheduling picks
identifiable" — is discharged structurally: the scheduling sites are
exactly `{l1Sched, postOp, backEdge, l5ExitWindow}` by tag.

### Q2 — the step-event channel

    /-- What one pool step DID — emitted by the step, never
    reconstructed from it. Kills `wokenPartner`'s pool diffing
    (Multi.lean:986-990) and `raceUpdate`'s three-way consumption
    replication (Multi.lean:1241-1271). -/
    structure PickRecord where
      site  : ChoiceSite
      bound : Nat
      pick  : Nat

    inductive StepAction where
      | spawned (child : Nat)
      | woke                                   -- resumeThread ran
      | paired (partner : Nat) (comm : CommKind)  -- issuer's pairing
      | chanCell (loc : Loc) (op : ChanEvKind)    -- cell-path op
      | selectCommit (cl : EvClause)
      | syncEv (op : SyncOp) (loc : Loc) (pre : SyncPre)
      | opDoneStrip
      | privateStep
      | parked

    structure StepEvent where
      who    : Nat
      action : StepAction
      /-- The picks THIS step consumed, in order — the labeled
      consumption trace; `runnable` at scheduling picks rides in
      the record's bound + the pool the driver already holds. -/
      picks  : List PickRecord

    -- Reshaped signatures (the choices+event thread):
    stepFn     : ExecState → Config → Choices
               → Except GoError (Config × ExecState × Choices × List PickRecord)
    stepThread : … → Except GoError (Array Config × ExecState × Choices × StepEvent)
    stepMulti  : MultiConfig → Choices
               → Except GoError (MultiConfig × Choices × StepEvent)
    raceUpdate : ExecState → Array Config → StepEvent → MultiConfig
               → RaceState → Except GoError RaceState

`raceUpdate` becomes a FOLD over events: the spawn/wake/pairing/
cell/commit classification arrives IN the event (who ran, which
partner, which clause committed, which picks were consumed), so the
detector's parallel dispatch — the audit's O-2, "three consumption
re-derivations that must stay in lockstep by review alone" — is
deleted rather than grown to a fourth copy by this widening. The
event consumers, named: `raceUpdate` (folds), the membership
enumerator (width metadata becomes first-class instead of re-derived
by `stepNeeds`), the driver's future fairness layer (a labeled trace
of scheduling picks + bounds is exactly what `Fair` quantifies over),
and S6a's opsem write-up (events are the rule labels' runtime
counterpart). Relation side: `StepM` is UNCHANGED in statement shape —
events are executable-side instrumentation like `Choices` and fuel
(the external-oracle mold, State.lean:136-151); the correspondence
theorems (`stepMulti_sound`/`stepM_complete`) quantify events
existentially on the executable side.

---

## 4. Fairness non-preclusion — the binding constraint, discharged

The charter's hard constraint: the widened envelope must not make
fuel-out the only outcome of legitimate programs, and must keep
fairness expressible for the liveness tier.

1. **Default streams are conservative by construction.** postOp and
   backEdge declare slot 0 = "current/issuer continues" — the old
   machine's schedule is the canonical member at every new site
   (audit C-2's convention applied to the new rows). The empty stream
   therefore realizes exactly the old machine's schedule (modulo
   fuel-neutral marker strips), so every program whose default-stream
   run terminated before terminates after, with the same observation.
2. **Every finite stream is eventually-canonical** (the fairness
   note's stream-vs-branch analysis): `Choices = List Nat` exhausts to
   pick-0-forever, and pick 0 at every new site is a progress-of-the-
   current-goroutine member. A finite stream can defer any goroutine
   only finitely; no widened site can be forced to repeat an
   anti-progress pick unboundedly by any stream the strict lane or the
   nondet guard can write. Consequence: **no existing strict-lane row
   can flip to fuel-out under the guard's fixed adversarial streams.**
3. **No point REQUIRES unfairness.** Divergent branches exist (the
   pick TREE has always-defer branches — it already does today at the
   `.spawned` boundary, probe (b)'s `[1,1,1,…]` class), but at every
   new site every slot menu contains every runnable goroutine: a fair
   schedule (round-robin at scheduling sites, say) is realizable as an
   explicit pick sequence, and every finite prefix of it is a
   `Choices` stream. The widening ADDS the fair schedules that were
   missing (the wedge's, §2 B1) and removes none.
4. **Fairness stays definable — and becomes non-vacuous.** With Q1
   tags, "the schedulable set recoverable" holds at every scheduling
   pick (site ∈ {l1Sched, postOp, backEdge, l5ExitWindow}, bound =
   |runnable|, the runnable list recoverable from the pool the driver
   holds at that step; Q2's events carry the record). A future
   `Fair : (ℕ → Nat) → Prop` (the FairStream carrier over infinite
   pick sequences — the finite-list carrier is the strict lane's,
   not the liveness tier's) is definable as: every goroutine runnable
   at infinitely many scheduling picks is picked at infinitely many.
   And B2 is what gives that definition teeth (§2 B2 point 1): with
   back-edges in the boundary set, a registry-free monopolist OFFERS
   infinitely many scheduling picks, so `Fair` genuinely forces the
   partner to run — `Fair ⇒ TerminatesNormally` becomes provable for
   probe (b)'s shape at the liveness tier. Without B2 that implication
   is unstatable. No flattening anywhere: the reshape keeps the
   stream, adds tags, and the tags are the anti-flattening.

---

## 5. Cost surface

### 5a. Proof blast radius (the re-alignment budget, stated before the surgery)

**Multi/MultiSound (`GoLean/GoCore/MultiSound.lean`, 1,015 lines) —
metatheory-level, all budgeted:** `stepThreadInto_sound`,
`stepMulti_sound`, `stepM_complete` re-proved over the new signatures
+ boundary set; `schedPick_of_boundary`/`schedPick_cur` restated
(schedPick itself unchanged in shape — `atBoundary` widens under it);
the `.spawned` lemma family (`spawnedCont_stepFn_internal`,
`step_spawnedMarker_elim`, `spawnedCont_of_spawnPlan/of_blocked`)
retires into the `.opDone` family; sequential-conservation cluster
(`stepThread_single`, `stepMulti_single`, `singleton_pool_facts`,
`execProgLoop_single`, `execProg_single_eq_execStmt`) re-proved — the
key fact keeping them true: singleton pools consume nothing at the new
sites (bound 1, consumeAtOne=false) and the sequential driver takes
the same marker steps as the pool driver (B1's marker is emitted in
`Machine.lean`'s applies, both drivers), so the equality is
step-for-step again, at shifted-but-equal fuel.

**MultiStreams (1,284 lines) — metatheory:** `stepThread_oblivious` /
`poolThreadOblivious` re-argued (new consuming shapes: `.opDone` at
bound>1, back-edge shapes at bound>1 — the pool checker fails closed
on them exactly as it does on L1-consuming boundaries today, i.e. it
explores each runnable branch); `stepAllBranchesOk` branches at the
new sites; `raceUpdate_oblivious` becomes trivial (Q2: the detector
consumes an event, not a stream); `execProgLoop_unfold/mono/le` and
the `allStreamsOkPool` soundness chain re-proved over the event-
threaded loop.

**NPDRF (460 lines) — statement-level:** `StepMFine` unchanged (it
already relaxes ALL boundaries); `stepM_le_stepMFine` re-proved
(trivially — more coarse steps are still fine steps); the
`NPDRFReduction` DRAFT restates over the new point set (its docstring
already says the weakening decision precedes proof; slice 5 owns the
ruling). The residual it measures SHRINKS under B1+B2.

**StateWf/MultiWfSound:** `MultiWf`/config well-formedness gains
`.opDone` arms (witness-level); `itersNormalized` untouched.

**The relation (Machine.lean):** +1 rule (`opDoneStrip`), −the
spawned-marker special casing; the `Step` rule set otherwise
untouched — B2 adds no rules (the shapes exist; only `atBoundary`
reclassifies them, which is pool-relation territory).

**Designated witnesses / kit pins:** every pinned stream in
eval tests and designated witnesses that crosses a registry op or a
loop back-edge in a ≥2-goroutine pool SHIFTS (new consumptions pop
picks at new positions) — BUG-040's precedent, budgeted by the
inventory: fork/join witnesses re-derived; the `Laws/` sequential
witnesses are untouched (single-goroutine, no consumption). The
oblivious/kit lemmas naming `consume` restate over `consumeAt`
(mechanical; the guard flags rename).

**The WP mirror (`proofs/GoLeanProofs/Sym/Mirror.lean`) — CONFIRMED
UNWIDENED:** every concurrency arm quits `.q7Concurrency`
(Mirror.lean:2147-2179, 2308-2312) and the mirror takes NO choice
stream (header: "insulates the mirror from the W3.2 `Choices` reshape
except through the drift theorem's visible break"). Exposure = the
transcription contract only: `stepFn`'s reshaped signature
(× List PickRecord) and any re-texted arms re-transcribe, and the
default-build drift gate breaks visibly until they do — the WP
charter's budgeted 3c cost, no silent risk. The mirror does NOT gain
concurrency arms in this arc.

**Surface layer:** `TerminatesNormallyC` and friends — statements
unchanged (they quantify streams over `execProg`, whose signature
keeps `Choices`); their MEANING widens with the envelope, which is
the point. `channel-logic`'s parked statements: re-alignment is
S6c's sizing job at resume, not this slice's.

### 5b. Corpus impact — the prediction, falsifiable at re-pin time

- **Strict lane: ZERO result/stage flips predicted.** Sequential rows:
  no new consumption (bound-1 sites silent), marker steps fuel-neutral
  to classification (default fuel ≫). Concurrency rows: default
  stream = old schedule (§4 point 1); adversarial-stream guard runs
  can't diverge (§4 point 2) and observe choice-invariant observables.
  The baseline (`baselines/native-full.tsv`, 2,247 rows) should
  re-pin with NEW ids only. Any existing-id drift at re-pin time is an
  unpredicted regression to be investigated, not explained away — this
  sentence is the honest-regression hook.
- **Membership rows:** enumerated sets keep their observation members
  (schedule-latitude observables were already enveloped: wake-window
  {ok,panic}, waiter-pick {12,21}, select-arrival families) but the
  TREES widen — `width=`/`sites=`/`work=` caps on pool rows need
  raising, and the certified `members=` counts are re-certified, with
  set GROWTH possible only where an observable genuinely distinguishes
  the new interleavings (predicted: none of the existing rows — their
  observables were chosen schedule-invariant or already-maximal).
- **New rows, the wedge family:** probe (a) send-then-spin becomes a
  corpus membership row for the first time (today it is evidence-only
  because a fuel-out-on-every-stream member cannot be classified
  honestly — the park-record reproduction); prediction: exit-0 ∈
  enumerated set, spin branches truncated per §5d. The U-1 probe (§6)
  lands beside it. Both are the "flips fuel-out→ok" family the charter
  names; no EXISTING corpus id is in that family (verified: the
  goroutines/channels/sync failing set at baseline is
  frontend-export/nondet/lean-observation/membership stages, none
  fuel-out).
- **Baseline re-pin:** once, at stage E (§7), from a full run, header
  reason "W3.2 slice 1: post-op + back-edge boundary widening; new
  probe-family rows; no existing-id movement" — or the honest
  investigation if the prediction fails.

### 5c. Certified/slow-tier re-certification scope

Both `tier=slow` rows re-certify (their certified sets are
schedule-envelope records): `imported-goose/channel/google-search`
(members=6 — already all permutations, set predicted stable; work was
39.9M steps / 94 s, grows with the tree) and `sync/rwmutex-order`
(members=2 = {10,20}, predicted stable; 2.2M steps). Budget: the
slow-tier caps rise; `scripts/ci --slow` is the slice's exit gate by
definition (interpreter + enumerator touched). If a slow row's
certification stops being tractable under the widened tree, the
recorded fallback is membership-sampling with the certified-set claim
narrowed and stated — never a silent cap-fit.

### 5d. The enumerator's bound story (G1-named question)

Two additions, both per-site (expressible BECAUSE of Q1's tags):

1. **Per-site enumeration policy.** The stepwise engine
   (`GoLean/CLI.lean:484` ff., `stepNeeds` accountant) branches
   exhaustively at every site today. backEdge sites in ≥2-runnable
   pools branch EVERY iteration — exhaustive exploration is
   exponential in loop length. Policy: sites carry an enumeration
   mode — `exhaustive` (all current sites, postOp) vs `capped`
   (backEdge: explore the canonical slot plus up to k anti-progress
   picks per site occurrence, k from the row's params) — declared in
   the same table as the consumption policy, printed into the row's
   record so a certified-set claim states exactly which tree it
   certified. A row needing full back-edge width says so explicitly
   and pays for it.
2. **Honest non-termination accounting.** `--expect-status` today
   admits only ok/panic/race (CLI.lean:645-652), and fuel-out
   members fail closed — right for every existing row, wrong for the
   wedge family whose envelope HONESTLY contains divergent branches.
   Addition: an explicit per-case `allow-nonterm` param under which a
   branch exhausting its per-branch step budget is recorded as a
   counted `nonterm=<n>` bucket (never an observation member, never
   green-contributing); membership = oracle observation ∈ TERMINATING
   members, exactly the lower-bound meaning. Without the param,
   fuel-out branches stay red — fail-closed is the default, the
   param is the visible opt-in, and a row using it says why in its
   `why` text.

---

## 6. U-1, probed and pinned (the charter's directed-probe obligation)

New directed probe (this session; source inline since this note's lane
owns no evidence-dir writes — the probe files land with stage C):

    // wake partner, then panic in the issuer's private segment
    func wakeThenAbort() int {
        ch := make(chan int, 1)
        go func() {
            ch <- 42
            panic("worker abort in the private segment")
        }()
        return <-ch
    }
    func main() { println(wakeThenAbort()) }

gc (go1.26.5, 200 runs, this session):

    exit-0, prints 42:            0/200
    exit 2 (panic), "42" PRINTED: 189/200
    exit 2 (panic), no output:     11/200

Machine at `10aad750` (mod-2 sweep, depths 0–6, 127 streams,
--fuel 100000; every reachable site bound ≤ 2, same closed-set shape
as probe (a)):

    127/127 panic — no stream prints before the abort

**The pin.** gc's DOMINANT member (189/200: main's `println` runs
between the worker's wake-producing send and the program's abort) is
outside today's envelope — `observed ∉ modeled` in the mid-program
abort class, exactly the C3 REMAINING GAP the inventory characterized
and left unprobed. U-1 moves from (d) UNKNOWN to a measured datum.
Under B1 the member is admitted: post-send `.opDone` boundary → pick
main → main prints and reaches its terminal → L5 window pick
CONTINUE → worker panics → abort with output "42" — the 189/200
member, as a widened-machine trace. The 11/200 member is today's
sole member (still admitted). Exit-0 was NOT observed in 200 runs;
the widened envelope admits it anyway (L5 exit-now at main's
terminal) — spec#Program_execution's "It does not wait for other
(non-main) goroutines to complete" licenses an implementation that
exits before the worker's panic fires (gc itself does, with any delay
before the panic — BUG-044's dossier probes are this same edge), so
the member is the transfer-safe too-wide direction, argued from text
per doctrine requirement 2. **B3 is NOT needed for any observed
member** — the deferral in §2 B3 is consistent with this probe's
data, and the probe is its recorded trigger's baseline.

---

## 7. The staged plan (each stage lands gate-green on the lane)

- **Stage A — Q1, behavior-identical.** `ChoiceSite` + `SitePolicy` +
  `consumeAt`; every existing consume site tagged with today's exact
  policy; census table cross-checked against the inventory §0 sweep.
  No new sites. Gate: `scripts/ci --diff` — baseline IDENTICAL
  (pure refactor; any drift is a bug in the table).
- **Stage B — Q2, behavior-identical.** Event-threaded
  `stepFn`/`stepThread`/`stepMulti`; `raceUpdate` folds events;
  `wokenPartner` + the consumption replication deleted;
  MultiSound/MultiStreams re-proved. Gate: `ci --diff` + `--slow`
  (interpreter + certified rows touched) — baseline identical.
- **Stage C — B1 post-op boundaries.** `.opDone` (unifying
  `.spawned`), postOp site, envelope statement in situ at the marker
  + `atBoundary`, witnesses re-derived, U-1 + wedge probe families
  land (evidence dir + corpus membership rows with §5d's params),
  membership wiring. Gate: `ci --slow`; baseline re-pin #1 if new
  rows land here (new ids + reason).
- **Stage D — B2 back-edges.** `atBoundary` loop arms, backEdge site
  + policy, enumerator per-site modes + `allow-nonterm`, the wedge
  row green end-to-end (DONE's "exit-0 on an enumerable stream"),
  fairness-expressibility note recorded at the site's docstring.
  Gate: `ci --slow`.
- **Stage E — closure.** NPDRF restatement; inventory/register/
  doctrine updates (C2, C3 → (a) ENVELOPED with their envelope
  statements; register #1 rewritten to the discharged form; U-1
  re-classed with §6's data; the C2-cost-prose correction from §2 B1);
  final full-run baseline re-pin with the §5b prediction checked
  line-by-line; `scripts/ci --slow` green at tip. Slice DONE per the
  charter's conjunction.

Stages A/B are the G0-ruled riders and change no observable — they
could land under the standing gate without G1; they are staged first
so C/D (the observable-set changes this note exists to gate) land on
the tagged, evented machine and cost their grade once.

---

## 8. DECISION BLOCK — what Mike rules on

### The boundary set, as a table

| # | Point | Mechanism | Site (slot 0) | Spec argument | Admits (new) | Cost center |
|---|-------|-----------|---------------|----------------|--------------|-------------|
| B1 | Post-op points at ALL registry-op completions (chan/sync/select applies, pairing issuer, wake, spawn) | `.opDone sched inner` marker config (unifies `.spawned`, site-tagged); strip = 1 step | `postOp` (issuer continues); spawn stays `l1Sched` | spec#Go_statements independence + mem#chan rule (1) direction + gc exhibits the flagship member 60/60 | wedge exit-0; U-1's 189/200 member; the whole BUG-040/044 class mid-program | MultiSound/MultiStreams re-proof; witnesses; sequential fuel shift (both drivers equally) |
| B2 | Back-edge preemption: `.next/.continuing (.loop …)`, `.next (.mapIterK …)` become boundaries | `atBoundary` arms only — no new config, no new step | `backEdge` (current continues) | spec scheduling silence + gc async preemption (1.14+) + mem#badsync | descheduling inside registry-free segments; makes `Fair` non-vacuous for the liveness tier | enumeration-tree width (→ §5d per-site modes); zero access-granularity change |
| B3 | Abort window at panic terminals (L5's analogue) | — | — | same silence class | post-RAISE partner progress only | **proposed DEFERRED to slice 5** — §6's probe shows no observed member needs it |

### The questions

1. **Approve B1 at ALL-ops scope?** The narrower option
   (wake-producing ops only) also de-fuses the wedge, but leaves a
   KNOWN residual `observed ∉ modeled` family: the U-1 class with a
   cell-path (non-wake) op — e.g. buffered send, then abort, with the
   partner's buffered-read progress excluded. Striking down to
   wake-only therefore trades tree width for a recorded standing bug
   of the same definitional class this slice exists to fix; if
   struck, that residual goes into the inventory as a NEW (b)-pin
   with a probe, and the wedge row still greens. *Recommended: all
   ops, per the G0 default.*
2. **Approve B2 in this arc?** If struck/deferred: the wedge still
   greens (B1 suffices, §2), but the liveness tier's fairness
   hypothesis stays vacuous over registry-free monopolists (§4
   point 4), the FairStream work inherits a machine it cannot state
   its theorem over, and C2 stays a (b) pin with its register entry
   un-discharged — the slice then converts only C3. *Recommended:
   in, per the G0/OQ2 default ("both together").*
3. **B3's deferral to slice 5 with §6's probe as its trigger
   baseline — accepted?** If instead ruled IN now: it lands as an
   L5-mold window at `panicMsg?` (bound-2 site, exit=0 canonical),
   stage C grows by one site, and the U-1 rows' envelopes widen
   accordingly.
4. **The canonical-slot convention** (slot 0 = issuer/current at
   postOp/backEdge — old schedule = default stream, §4): this is
   what makes §5b's "zero strict-lane flips" prediction and the
   non-preclusion argument hold. Striking it (e.g. uniform
   goroutine-order slots) is coherent but re-pins the entire
   concurrency corpus's default observations and voids §5b.
   *Recommended: as designed.*
5. **`.spawned` → `.opDone` unification** (one marker mechanism,
   T-6), with the marker's `sched` tag preserving the spawn
   boundary's exact BUG-040 default (§2 B1 mechanism): strike to
   keep `.spawned` separate if the witness churn is unwanted this
   slice — cost is two mechanisms where one suffices, permanently.
   *Recommended: unify, tagged.*
6. **The enumerator's §5d policy** (per-site enumeration modes +
   explicit `allow-nonterm` accounting): this is the "enumerator's
   bound story" the charter names into G1. *Recommended: as
   designed; the alternative (exhaustive-only) makes the wedge row
   uncertifiable rather than honestly capped.*

Approval of the set as recommended = stages A–E proceed as §7. Any
strike narrows the set honestly per the per-question consequences
above; none of the strikes reverts to silence — every struck point
keeps its inventory row and its recorded reason.

### What this note leaves open, by name

For F4: Q-ATOMICITY, Q-GOEXIT (interfaces held open, §2 tail). For
slice 2: Q-ATOMIC's granularity coupling consumes this boundary set
as input. For slice 5: B3; the completeness enumeration over the NEW
set; the NPDRF/register #5 ruling. For the liveness tier: the
FairStream carrier and `Fair`'s definition (non-precluded, §4; not
built here).
