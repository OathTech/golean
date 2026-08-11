# Nondeterminism doctrine — modeling, testing, and its limits (2026-08-04)

Recorded from the 2026-08-04 design discussion (user + agent), folding the
strategy and its honest epistemic limits into the record. This is
doctrine: binding on every future choice-consumption site and on the
concurrency arc's design.

## The model

All Go implementation latitude we model routes through ONE mechanism: the
`Choices` stream in `sem()`'s signature. The interpreter is total and
deterministic GIVEN a stream (executability — the differential trust root
— is the project's foundational requirement and the reason a set-valued
semantics was never an option). Consumption sites are named and few —
the CANONICAL LIST (kept current per this doctrine's binding-site rule;
brought current at the arc-final audit F16, 2026-08-08, after the
channels arc left this preamble at its two sequential sites):

- map iteration pick (`StepFn.lean`);
- append spill capacity (`Machine.lean`, `appendSpillWidth` envelope);
- L2 select-commit pick, entry path (`applySelect`, `Machine.lean`);
- L2 select-commit pick, arrival path (`arrivalPlan`, `Multi.lean`);
- L4 waiter pick (`stepThread`, `Multi.lean`);
- L1 scheduler pick (`stepMulti`, `Multi.lean`);
- L5 main-exit window (`execProgLoop`, `Multi.lean` — BUG-044, audit
  F2: exit-now vs one-more-runnable-goroutine-step at main's terminal).

Each site carries its envelope statement in situ; enforcement is
structural (`applyStmtOpCore` is choices-free). The old parenthetical
"step SUCCESS is provably choice-independent" is scoped precisely
(F16's correction): the sequential kit (`stepFn_oblivious`) is GUARDED
(no mapIter/append/select shapes), and at POOL level the L1 pick
decides WHICH goroutine steps, so a stream can determine whether a
pool step succeeds — obliviousness holds per certified shape
(`poolThreadOblivious`/`stepThread_oblivious`), never unconditionally.
Headline theorems ∀-quantify the stream: true under EVERY resolution of
the latitude — deliberately stronger than any single Go implementation.

## Testing today: the strict lane + invariance guard

Corpus cases run under the default stream and must EQUAL `go run`'s
observation; then re-run under fixed adversarial streams — variance fails
the case (stage `nondet`). The strict lane therefore admits only
choice-INVARIANT observables, and the corpus is written to observe
order-independent quantities; that convention also neutralizes Go's own
per-run randomization. Genuinely choice-dependent observables
(`slices/full-slice-cap-zero`'s `cap()`) sit honestly red until the
membership lane exists (general-coverage arc, slice 3).

## The epistemic limits, stated plainly

Differential testing is VERIFICATION for deterministic behavior and
degrades to SANITY-CHECKING at the nondeterministic frontier. The failure
directions are asymmetric:

- **Too NARROW** (real Go exhibits a behavior outside our envelope) is
  the SOUNDNESS-relevant direction: ∀-stream theorems transfer to real Go
  only if Go's behaviors ⊆ modeled behaviors. It is DETECTABLE — the
  membership lane's job (Go's observation ∈ our admitted set), plus
  equality-lane mismatches. Sampling density varies by feature: map order
  re-randomizes per run (every go-run explores — dense, and fuzz-generated
  order-SENSITIVE contexts make it a real exploration); append growth is
  deterministic per Go version (one point per toolchain — membership is
  version-tracked); SCHEDULING sampling is nearly useless (the runtime
  explores a tiny biased corner — see the concurrency inputs below).
- **Too WIDE** (we admit behaviors no conforming Go could exhibit) is
  UNDETECTABLE by any oracle — go run cannot demonstrate a behavior it
  never has — but it is the benign direction: ∀-stream theorems become
  harder to prove, never wrong. The check is REVIEW, not testing (below).

## Binding requirements

1. **Envelope statements.** Every choice-consumption site ships with a
   spec-anchored envelope statement in its design note or docstring: what
   the Go spec text says, exactly which set our stream resolves, and the
   argument that the set contains every behavior conforming Go can
   exhibit (the soundness direction). Current sites' statements: map
   iteration — spec says unspecified order, envelope = all permutations
   of the snapshot, which is ⊇ any Go ONLY for programs that do not
   mutate the map during iteration: the spec MANDATES that an entry
   removed before being reached "will not be produced", and the snapshot
   model still produces it (and stale values) — the known, triple-pinned
   divergence BUG-005, deliberately deferred to its live-iteration fix;
   until then the map envelope statement is scoped to mutation-free
   iteration (arc-final audit F14, 2026-08-06); append spill — spec
   allows any sufficient capacity ("a new, sufficiently large
   underlying array"), envelope = [newLen, max(32, 2·growth formula)]
   (WIDENED deliberately at the arc-final audit, F2/BUG-021 2026-08-06:
   go1.26.5 — the oracle toolchain itself — realizes capacities outside
   the old growth+[0,8) window in both directions, because gc's
   realized capacity is element-size dependent — size-class rounding
   and the compiler's 32-byte stack buffer — while the formula is not.
   The containment argument for the widened bound lives on
   `appendSpillUpper`, GoCore/Ops.lean; the empty stream still resolves
   to the growth-formula point, so strict-lane behavior is unchanged).
   Still a PRAGMATIC SUBSET of the spec's latitude, sound for transfer
   as long as real Go's policy lands inside. Version-tracking is
   per-point, not per-envelope — a samples=1 membership case tracks its
   one (elem, oldCap, newLen) triple — so the escaping REGIMES carry
   their own pins (slices/append-spill-{stack-buffer,below-formula,
   size-class}) alongside the formula point (full-slice-cap-zero).
   SINGLETON NARROWINGS (added at the arc-final audit, F8/F15
   2026-08-06): a spec-declared or spec-SILENT latitude that the model
   resolves to a single point WITHOUT a Choices site is still an
   envelope decision and ships the same statement + transfer caveat at
   its site. Current recorded singletons: `[]byte(s)` capacity pinned
   to len (Machine.lean `bytesFromString` arm — gc's escaping path
   realizes roundupsize(len), outside the singleton; caveat at the
   arm); map-key retention on overwrite pinned to gc's `needkeyupdate`
   (floats design note §"Map keys", spec-silent).
2. **Envelope fidelity is a standing audit dimension** (like
   over-specialization): reviewers argue each envelope against the spec
   TEXT, because the too-wide direction has no oracle.
3. **Possibilistic scope, declared.** Our claims quantify all
   resolutions; we never make probabilistic claims. Spec language like
   `select`'s "uniform pseudo-random" enters the model only as "any";
   statements must never imply distributional facts.

## Inputs to the concurrency arc's design note (binding starting points)

- **DRF-SC discipline**: data races FAIL CLOSED (an error, not an
  interleaving) — Go's memory model gives racy programs essentially
  undefined behavior, and modeling races as well-defined nondeterministic
  interleavings would be wrong in KIND. Sequentially-consistent
  interleaving is claimed only for race-free programs (the DRF-SC
  theorem's territory; Goose/Perennial take the same line).
- **`go run -race` as a second oracle**: programs the race detector flags
  must fail closed in our model — a testable boundary exactly where
  interleaving sampling cannot help.
- **Litmus corpus**: memory-model litmus shapes (message passing, store
  buffering, …) as corpus cases probing the envelope's edges.
- **Fairness quantifier decision**: ∀-stream termination is FALSE for
  correct programs that spin-wait on another goroutine (unfair schedules
  starve the writer). Concurrency termination claims need an explicit
  fairness-constrained quantifier, decided in the design note — not
  discovered as an unprovable theorem.

## The racy-negative lane, live (channels arc slice 3, 2026-08-07)

The DRF-SC fail-closed input above is now executable: the pool's
segment-level happens-before detector (`RaceState`/`raceUpdate`,
`GoLean/GoCore/Race.lean` + `Multi.lean`) refuses racy runs with the
terminal `raceDetected`, and the corpus grew the `race/` lanes
(negative, litmus pairs, false-positive guards) with `go run -race` as
the second oracle (`expected_status: race` in the harness). The lane's
EPISTEMIC CAPTION, recorded per the per-lane discipline:

- **What a race-lane PASS means (FULL STRENGTH since slice 4,
  lane=racy)**: the schedule enumerator proved EVERY ENUMERATED PATH
  refuses — the whole registry-point schedule tree, mechanically
  bounded per site, ends in `raceDetected` on every leaf (one value
  leaf anywhere fails the case loudly) — AND one `-race` sample
  witnessed a real race (TSan has no false positives — one red report
  is proof). The claim is scoped to the REGISTRY-POINT path set (scope settled
  at channel-logic S4 — the NPDRF status section below) and by the
  footprint inventory's
  recorded under-approximations (U1–U2; U3 closed by BUG-045); the pre-slice-4 per-stream
  approximation is retired.
- **The three-way investigation rule** (binding; also recorded at the
  harness dispatch in `scripts/diff-coverage`): our-refusal +
  `-race`-green-on-every-sample is NEVER a pass — it is an
  investigation with exactly three outcomes: (a) the race check is too
  eager (model bug — fix); (b) the race needs a schedule the sampler
  never hits (directed sampling / enumerator territory; record the
  conclusion in the case's `why`); (c) the program is race-free and
  misclassified (model bug — fix).
- **Detector HB targets TSan's realized edge set** (the
  structural-alignment decision, design note D2+D3): gc's channel race
  instrumentation (slot release-acquire, rendezvous racesync, close
  release/acquire) — not the memory model's minimal rule set — so our
  refusals stay justifiable by the oracle. Divergences between the
  detector's HB and go_mem's relation (Fava SEFM 2020's caution) are
  therefore shared with `-race` rather than invented by us; each is
  quoted at its implementation site in `Race.lean`. Two recorded
  DEVIATIONS from gc's realized set (S3 audit corrections; (i)
  RESOLVED at the arc-final audit F1/BUG-045, 2026-08-08): (i) the
  close-woken SENDER gets no edge from us although gc's `closechan`
  DOES `raceacquireg` parked senders — our edge set is strictly
  STRONGER there. The old text claimed "refusal-set agreement holds
  anyway because gc flags every close-beside-parked-send via its
  channel-OBJECT instrumentation, which we do not model" — FALSE in
  the fail-open direction (three shipped confluent-green subjects
  were TSan-red through exactly that unmodeled pair; the audit's F1).
  The chan-object pair IS now modeled (`RaceState.chanObjAccess`:
  send = entry read (plain sends AND, per BUG-046, one read per
  polled select-SEND clause — selectgo pass 1's racereadpc),
  successful close = write, recv and select-recv clauses = nothing
  — gc's instrumentation exactly), so every close beside a parked
  plain sender refuses at the close and the missing wake edge is moot
  on refused programs; the reclassified racy pins
  (goroutines/close-wake/sender-*, select-closed-arrival/
  recv-parked-sender) are the executable check;
  (ii) `len(m)` on a MAP is instrumented by gc (probed red on
  go1.26.5, refuting the first version of this caption) and is now
  recorded by the footprint; `len`/`cap` on channels remain
  uninstrumented on both sides (probe p26). The footprint's remaining
  under-approximations are U1–U2 in Race.lean's inventory (U3 closed by BUG-045, 2026-08-08) — the
  lane's per-stream refusal claim is scoped by them.
- **Scope limit (BUG-040) — FIXED at slice 4**: the detector is
  complete only over accesses that EXECUTE on the modeled
  (registry-point) paths; the post-spawn reschedule point (`.spawned`,
  a registry op at fork completion) now puts the child-first
  interleavings INSIDE that path set, so the exit-no-sync race class
  is detectable (eval-pinned: value leaf on main-first, race leaf on
  child-first — a mixed-leaf class no corpus race case can express,
  and the pool enumerator pins BOTH leaves). The registry-point-vs-
  full-interleaving gap is now precisely characterized and its
  reduction statement settled-but-open (the NPDRF status section
  above, 2026-08-11).

## The NPDRF status — SETTLED captions (2026-08-11, channel-logic S4)

The reduction obligation the captions below lean on is settled at
slice channel-logic S4 (binding note `docs/2026-08-11_npdrf-reduction.md`;
this section is the caption formula of record — the lane captions
point here):

- "Every schedule" / "the registry-point path set" = full
  per-machine-step interleaving RESTRICTED to boundary switches —
  now a machine-checked characterization, not a separate relation
  (`stepM_iff_fine_bs`, NPDRF.lean: StepM = StepMFine ∩
  BoundarySwitch).
- The draft claim "race-free programs behave identically under
  registry-point scheduling and full interleaving" is REFUTED as
  originally stated (`NPDRFReduction_refuted`: `.done` carries the
  whole joined state, and two leaked mid-segment goroutines make it
  fine-reachable but coarse-unreachable, race-free). Literal-state
  and literal-value corrections stay refuted through allocation
  order (note §2).
- The corrected, citable target is class-level
  (`NPDRFClassReduction`: fine-reachable results are coarse-reachable
  up to result CONSTRUCTOR) — OPEN, proved so far only for
  never-spawning pools (`reachesMFine_iff_reachesM_single`, where the
  equivalence is literal). The mover route to the general statement
  and its sized blocking machinery: note §5.
- Consequence for every ∀-schedule statement: for spawning programs
  the claim is registry granularity ONLY; no caption may assert
  sub-registry transfer, and none may cite `NPDRFClassReduction` as
  proved.

## Slice-4 additions (2026-08-07): schedule enumeration and the lane upgrades

- **The membership lane enumerates SCHEDULES** (the out-of-scope item
  above, delivered): the enumerator explores the POOL stepwise —
  scheduler (L1), waiter (L4), and select (L2) sites included — with
  MECHANICALLY-COMPUTED per-site bounds (the CLI consumption
  accountant reuses the machine's own analysis functions; the author
  `width` is now a mechanically-checked cap, and the alias ladder
  cross-checks the accountant). Certified sets carry an optional
  `members=` cardinality pin (sb-chan's {1,10,11} pins 3, so the
  SC-forbidden 00 cannot hide inside a passing run).
- **`-race` is a DEFAULT membership sample source** (the recorded
  measurement above, operationalized): every membership case samples
  the oracle `samples` times plain AND `samples` times under `-race`
  — the -race runtime's scheduling perturbation reaches orderings the
  point-mass plain runs never exhibit (first-come exhibits both
  members only under -race), and its allocator differences exercise
  other envelope members (cap-zero's -race sample lands on cap 1,
  inside the F2-widened envelope — a live validation of the
  widening).
- **The CONFLUENT lane (D9(b))**: for deterministic concurrent
  programs the enumerator certifies |set| = 1 over ALL schedules and
  the full-strength strict differential then runs — schedule-
  independence is a certified claim, not a 3-stream spot check.
  Caption: a confluent PASS quantifies the registry-point schedule
  tree, scoped like the racy lane. Cases whose trees exceed the
  fail-loud caps at tractable budgets stay strict, RECORDED in their
  cases.tsv (pipeline/two-stage, pipeline/buffered-stage,
  worker-pool/shared-feed — DPOR is the recorded later-additive
  layer).

## Per-lane epistemic captions (channels arc slice 6, 2026-08-07)

The complete caption set for the D9 lane taxonomy — what a PASS MEANS
and what it structurally CANNOT show, per lane (validation research
note §4 is the evidence base; the racy lane's full caption is its own
section above and is only pointed to here). A compact copy rides at
the lane dispatch in `scripts/diff-coverage`; THIS section is the
record.

- **strict — sequential-degenerate (D9(a))**: PASS = observation
  equality against one `go run` plus three-adversarial-stream
  invariance. Means: the observable is choice-invariant and equals
  Go's, and the concurrency machinery is CONSERVATIVE on it (the
  conservation theorem `execProg_single_eq_execStmt` is the transfer
  lemma; full-corpus bit-identity its empirical twin). Cannot show:
  anything about interleaving — a strict green is structurally blind
  to schedule effects (the S2 waiter-priority majors were invisible
  to every green strict case; only membership probes saw them) — and
  nothing about streams beyond the three pinned adversarial ones.
- **confluent (D9(b))**: PASS = enumerator-certified |set| = 1 over
  ALL registry-point schedules, then the full-strength strict
  differential on the singleton. Means: schedule-independence is a
  CERTIFIED claim for this program, and the one admitted observation
  is Go's. Cannot show: anything past the fail-loud caps (over-cap
  cases stay strict, recorded in their cases.tsv); anything about
  programs outside the certified one; anything at sub-registry
  granularity (settled scope — the NPDRF status section above: the
  class-level reduction is open, so sub-registry transfer is not
  claimed).
- **membership — schedule-dependent (D9(c))**: PASS = every Go sample
  (R plain + R under `-race`, the dual-sampling rule above) ∈ the
  machine-enumerated observation set, with mechanically-computed
  per-site bounds, fail-loud caps, and the optional `members=`
  cardinality pin. Means: Go's exhibited corner lies inside our
  envelope, and the envelope was exhaustively enumerated at registry
  granularity. Cannot show: that UNEXHIBITED members are
  Go-realizable — the too-wide direction has no oracle; the
  width-signal metadata (|enumerated| vs |exhibited|, recorded per
  run) plus the standing envelope-width review are the only check —
  and nothing about racy programs (refused before this lane applies).
- **racy (D9(d))**: the full caption is the dedicated section above —
  every enumerated path refuses AND one `-race` red sample witnesses
  the real race; the three-way investigation rule; scope = the
  registry-point path set and the footprint inventory's U1–U2 (U3 closed by BUG-045).
- **litmus pairs (D9(e))**: not a harness lane — a corpus DISCIPLINE
  over the memory-model shapes (MP, SB, …), each in two forms: the
  channel-synchronized form rides lane b/c and must admit exactly the
  SC-reachable outcomes (sb-chan {1,10,11} with members=3 — 00
  mechanically excluded), the racy form rides lane d and must refuse.
  A PASS of the pair means: the envelope's EDGES sit where the memory
  model says (SC inside DRF, refusal outside) — the envelope-fidelity
  audit dimension made executable. Cannot show: weak-memory behaviors
  — we refuse the programs that could exhibit them, deliberately; a
  real implementation's weak behavior on a racy program is outside
  every claim we make, and transfer caveats must say so.
- **deadlock / leak (D9(f))**: global deadlock is strict-lane
  differential (`expected_status: deadlock` against gc's fixed
  "all goroutines are asleep" fatal, exit 2; NEVER combined with
  `-race`, which suppresses the detector). PASS means the blocking
  semantics — what deadlock is made of — agrees with Go where Go can
  express an opinion. Partial LEAK is observably NOTHING on the Go
  side (exit 0): main-exit cases validate the sequential observable
  differentially, while the leaked-goroutine classification itself is
  model-internal SELF-consistency plus review, never differential
  evidence. Cannot show: liveness (deadlock-freedom of
  nonterminating-by-design programs is outside a terminating-run
  corpus entirely — the proof side's territory).

**Tiered-checking caption (2026-08-08, user directive):** an envelope
certification too expensive for every commit (tier=slow rows) may be
CACHED against a tracked certified-set record — quick runs check
samples and the driver-coupling streams against the record (visible
`CERTIFIED-CACHED`, never a silent green) and `scripts/ci --slow`
re-certifies the envelope in full. The cached mode defers only the
machine-side envelope re-enumeration; the record is staleness-guarded
by the case's wire hash, and a re-certification that moves the set
fails loud. Design: docs/2026-08-04_membership-lane-design.md,
2026-08-08 addendum.
