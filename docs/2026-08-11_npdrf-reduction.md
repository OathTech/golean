# The NPDRF reduction — refutation, corrected statement, honest fragment (channel-logic S4)

Status: BINDING DESIGN NOTE (charter slice 4; written and committed
BEFORE any proof work, per the charter's "early design note on the
corrected statement is binding" clause). Decisions here govern the
slice's proofs and the FD1 caption update. Sections: §1 the refutation
of `NPDRFReduction` as written, re-derived first-hand; §2 the second
refutation class (allocator order), sharpened first-hand beyond the
recorded obstruction; §3 what "DRF" and "behave identically" mean
operationally; §4 the corrected-statement candidates (options format)
and the choice; §5 the proof plan with the honest fragment boundary
drawn BEFORE proving; §6 the caption formula and site inventory;
§7 (LAST, per the slice charter) the FD5 decision-rule evaluation.
§8 records the slice's results/gates as they land (appended per
commit; everything above §8 is frozen at the binding commit except
typo-class fixes).

Primary sources read for this note: `GoLean/GoCore/NPDRF.lean` (the
draft statement + obstructions 1–6), `GoLean/GoCore/Multi.lean`
(`StepM`/`schedPick`/`stepMulti`/`poolResult?`-adjacent machinery),
`GoLean/GoCore/Race.lean` (`stepAccesses`, the U1–U2/O1 inventory),
`docs/2026-08-06_channels-arc-design.md` (D2's reduction sketch + the
S3 audit's obstruction record), `docs/2026-08-04_nondeterminism-doctrine.md`,
`docs/2026-08-07_goose-comparative-scoping.md` rows T12/L3/O4.
Prior art: Xiao–Jiang–Liang–Feng ICTAC 2018 (NPDRF), Lipton 1975
(movers), the CHESS bounded-scheduling architecture.

## 1. The refutation, re-derived first-hand

The draft statement (NPDRF.lean):

    def NPDRFReduction : Prop :=
      ∀ m₀ : MultiConfig, ¬ RacyFine m₀ →
        ∀ res, ReachesMFine m₀ res ↔ ReachesM m₀ res

The machine hooks that make it false, each verified against the
current sources (not inherited from the S3 marker):

1. `PoolResult.done` carries the WHOLE shared `ExecState`:
   `poolResult?` classifies through `MultiConfig.mainOutcome?`, which
   returns `.normal m.shared` (etc.) — so a `.done` result value pins
   every heap cell, including cells only leaked goroutines touch
   (Multi.lean, `mainOutcome?`).
2. The coarse scheduler switches ONLY at boundaries: `schedPick m i`
   is `i ∈ runnableIdxs …` when `m.threads[m.cur]` is at a registry
   boundary and `i = m.cur` otherwise (Multi.lean). So once a
   goroutine has taken a step and sits mid-segment (its config not
   `atBoundary`), every subsequent `StepM` step is ITS step until it
   reaches a boundary.
3. The fine scheduler has no such constraint: `schedPickFine m i` is
   bare runnable-membership (NPDRF.lean).

Consequence — CORRECTED at the S4 audit fix round (the first form
over-generalized; the audit exhibited pairing and spawn
counterexamples on the repo's own certified rendezvous pool): **in a
SYNC-FREE, spawn-free pool, any `StepsM` run holds at most one
goroutine strictly mid-segment** (has stepped past a boundary without
reaching the next one) — the running one. In GENERAL coarse runs the
count can exceed one without the extra thread ever being picked: a
pairing step (`applyPairing`) rewrites TWO thread slots, moving the
parked partner off its blocked-config boundary into a delivery config
it did not step into itself, and a spawn bears the child at an
off-boundary `.exec` config — so the coarse/fine gap is NOT
characterized by "≥ 2 simultaneously mid-segment" once sync or spawn
is present. The refutation below needs only the sync-free instance,
which is the class its `CoarseInv` formalizes. The fine relation can
hold two goroutines strictly mid-segment simultaneously even
sync-free. With `.done` pinning the whole shared state, that
difference is a reachable-RESULT difference, race-free.

The counterexample class (obstruction 4's, now made exact): main
(goroutine 0) already terminal; two leaked-SHAPED goroutines A and B,
each performing TWO stores to its own private pre-existing cell
(A: x:=1 then x:=2; B: y:=10 then y:=20), no synchronization
anywhere. Reachability status, stated precisely (audit fix round —
the first form said "spawned-and-leaked", inviting a stronger
reading): the formalized pool `m0` is HAND-BUILT and NOT reachable
from any initial pool — `spawnStep` gives every spawned goroutine a
barrier frame, while A and B carry bare `.stop` continuations. The
refuted statement quantifies `∀ m₀ : MultiConfig`, so the theorem is
exactly on-statement; a program-level (initial-pool-reachable)
variant of the same mechanism would need barrier-framed threads and
was not built. All footprints are per-goroutine disjoint (`locOverlap` on
distinct base cells is false), so `¬ RacyFine` — the premise holds.

* Fine: step A once (x=1), then B once (y=10). Main is terminal, so
  the resulting pool classifies `.done (.normal σ)` with σ showing
  x=1 ∧ y=10 — both A and B strictly mid-segment. `ReachesMFine` ✓.
* Coarse: the state x=1 ∧ y=10 requires A strictly mid-segment (x=1,
  its second store pending) AND B strictly mid-segment — excluded by
  the at-most-one-mid-segment property. `ReachesM` ✗.

An important subtlety that the S3 prose glossed and this derivation
makes explicit: post-main-terminal stepping does NOT rescue the
statement, but it rescues MORE than one might think. Because `StepM`
admits steps after main's terminal (the relation admitted them all
along; BUG-044 brought the driver into line) and `poolResult?`
classifies at EVERY intermediate pool, single-mid-segment `.done`
states ARE coarse-reachable (run main to its exit, then step A
partway). Within the counterexample's sync-free class, only the
≥ 2-simultaneously-mid-segment states are outside the coarse set.
That is why the counterexample needs TWO leaked writers; one is not
enough.

The `↔`'s ⊆ direction (`ReachesMFine → ReachesM`) is therefore FALSE
on race-free pools. (The ⊇ direction is `reachesM_le_fine`, proved
unconditionally at S3.)

**This slice machine-checks the refutation**: the counterexample is
finite-state (a 3-goroutine pool over a 2-cell heap; each leaked
goroutine has a 6-config trace), so `¬ NPDRFReduction` is provable by
(i) exhibiting the 2-step fine run, and (ii) a coarse reachability
invariant — every `StepsM`-reachable pool has A untouched-or-complete
or B untouched-or-complete, plus the forced-continuation `cur`
coupling — established by induction with `stepM_complete` (every
`StepM` step is realized by `stepMulti`, which computes on concrete
pools). ¬RacyFine rides a fine invariant (thread-shape coupling, no
state tracking needed — the footprints of the trace configs are
state-independent). Feasibility of every computational ingredient was
probed by `#eval` before this note was committed (the
`#eval`-before-you-prove rule): step successors, `runnableIdxs`,
`arrivalCases = .cellPath` on all trace shapes, `poolResult?`
classifications, footprints, and `stepMulti`'s forced-continuation
behavior all compute as the derivation above requires.

## 1a. THE THIRD MECHANISM — the `schedPick`/`cur` asymmetry (S4
## pre-merge audit, MAJOR; re-derived here first-hand at the fix round)

The audit machine-checked `¬ NPDRFClassReduction` — the fix-round's
predecessor "corrected target" — three independent times, through a
mechanism §4's first truth argument never considered. Re-derived from
the sources:

* `schedPick m i` (Multi.lean) matches on `m.threads[m.cur]?`:
  `none → False` (an out-of-range `cur` silences the ENTIRE coarse
  relation), and an off-boundary `some c` forces `i = m.cur`.
  `schedPickFine` never consults `cur` at all. So whenever the thread
  at `cur` is off-boundary and cannot take a `StepE`, every `StepM`
  constructor dies on it: the coarse relation is WEDGED while fine
  simply schedules another runnable thread.
* TWO forms, both machine-checked by the audit and re-run first-hand
  at this fix round (`.tmp/aud_s4_class2.lean`, `.tmp/vfy/PFinal.lean`
  — both reproduce, axioms `[propext, Quot.sound]`):
  - **stuck-`cur`**: the thread at `cur` sits at a fail-closed config
    (no `Step` rule; `stepFn` errors on every stream). The verifier's
    variant is a `MultiWf`, in-range pool — well-formedness does NOT
    exclude the class.
  - **spinning-`cur`**: a `for {}` body (`.while (.boolLit true) …`)
    steps forever with `atBoundary = false` at every step (probed 60
    steps) — no error, empty footprints, race-free — wedging the
    coarse relation FOREVER by the same forced-`i = cur` mechanism.
* The verifier's decisive strengthening: spinner-wedged pools are
  themselves COARSE-REACHABLE from genuine initial programs (main
  spawns a `for {}` goroutine; the `.spawned` marker is a boundary, so
  the coarse scheduler may pick the child there — and can then never
  switch back). So this is a REAL non-preemption gap between `StepM`
  (non-preemptive between boundaries) and `StepMFine` (preemptive),
  not a well-formedness nit: no `m₀`-scoping can remove wedged pools
  from the middle of coarse RUNS.

**Why ∃-reachability from single-threaded roots nonetheless escapes**
(the repair's load-bearing argument — new at this fix round, engaging
the mechanism directly instead of ignoring it):
`ReachesM` is ∃-quantified over schedules. A wedged pool is a DEAD
BRANCH of the coarse tree, not an obstruction to other branches; the
coarse scheduler is only ever FORCED onto a thread it previously
picked mid-segment, and from a single-threaded `cur = 0` root every
multi-thread coarse state descends from a boundary reschedule — so a
schedule that simply never picks a doomed thread exists whenever one
is not needed. And a non-yielding segment is never needed: any
segment the mimicking coarse run must traverse is one the FINE run
completed (finitely, up to that thread's next registry op) — segments
that never reach a boundary produce no registry op, no sync effect,
and (race-free, class-level) no observable contribution, so the
avoidance schedule realizes the fine run's registry-op order without
ever entering them. The two exhibited forms are exactly the pools
where `m₀` ITSELF starts wedged or multi-threaded — which is what the
repaired premise excludes.

## 2. The second refutation class, sharpened: allocation order kills
## every literal-value correction too

Obstruction 1 (allocator interleaving) was recorded as a MOVER
obstacle ("the reduction must be stated up to an address renaming").
Re-deriving it at statement level shows it is stronger than that: it
refutes not just the draft but also both weakenings the S3 audit
sketched ("post-state scoped to main-reachable locations, or main's
readout only") whenever concurrent segments allocate:

* `ExecState.alloc` increments the shared `nextAddr`; interleaving a
  leaked goroutine's allocation between two of main's allocations
  permutes the addresses main's own data structures receive.
* So even an observation restricted to MAIN's readout differs
  literally across schedules when the readout contains a pointer
  (`.addr` values embed the address), and a panic MESSAGE can embed
  formatted values. Race-freedom does not help: allocation is not an
  access (the malloc convention — fresh allocation is deliberately
  not footprinted, Race.lean).
* The fragment where this cannot happen — no allocation in any
  concurrent segment — is delimited by allocation SITES, not by
  call-presence (CORRECTED at the S4 audit fix round; the first form
  claimed "EVERY call allocates" and "no-call segments qualify",
  wrong in both directions): `enterFrame` allocates exactly one cell
  per PARAMETER (`bindParams`) and one per RESULT (`allocDecls`), so
  a niladic, resultless call allocates nothing — the repo's own
  `noopWorker` spawn witness (LangC.lean / SpawnNoopProgress.lean) is
  a live call-bearing allocation-free post-spawn segment — while a
  CALL-FREE segment that declares a block local or runs
  `newValue`/`make*`/an append spill DOES allocate. The dsp child's
  `*p = 42; sig <- …` shape qualifies because it hits no allocation
  site, not because it has no call.

Conclusion (binding): any corrected statement that compares STATES or
address-carrying VALUES literally is either refutable or confined to
the no-concurrent-allocation fragment. The general corrected
statement must quotient by a heap isomorphism (address renaming
fixing the seed prefix), which is machinery this repo does not have
and this slice does not build. Statements that compare only
constructor-level result CLASSES avoid the quotient entirely.

## 3. What "DRF" and "behave identically" mean here

**DRF.** Options considered:

* (a) `¬ RacyFine` — no fine-reachable pool holds two co-enabled
  conflicting next-step footprints (NPDRF.lean; the classic
  co-enabled-conflict formulation over the SAME `stepAccesses` table
  the executable detector records). CHOSEN — it is the strongest
  premise-side notion (quantifies fine reachability, not just
  modeled schedules), it is what the draft already used, and sharing
  the footprint table keeps one access semantics for statement and
  tool (obstruction 5's benefit). Its honest scope rider: the
  footprint inventory's recorded under-approximations (Race.lean
  U1–U2, O1) bound what `¬ RacyFine` says about go_mem/`-race`
  data-race-freedom — the reduction is stated against OUR access
  semantics, and its transfer to Go rides the inventory's
  completeness discipline, exactly as recorded at obstruction 5.
* (b) detector-clean on every modeled schedule (the executable
  refusal never fires). REJECTED as the statement premise: it is the
  DETECTOR-COUPLING side (plan step iv / FD5's completeness
  question), not the reduction premise; using it would entangle the
  two open problems.
* (c) go_mem-DRF. REJECTED: not formalized in the repo; U1–U2 make
  any claim in that vocabulary dishonest today.

**"Behave identically."** Options:

* (a) Trace equivalence. REJECTED: strictly stronger than any
  consumer needs; refuted by the same counterexamples.
* (b) Reachable-RESULT-set equality at literal `PoolResult` equality
  — the draft. REFUTED (§1, §2).
* (c) Reachable-result-set correspondence at CONSTRUCTOR level
  (`panicked ~ panicked`, `done ~ done` with the same
  `ExecOutcome` constructor, `deadlocked ~ deadlocked`; no state, no
  message comparison). CHOSEN for the corrected citable statement —
  see §4 for why messages are excluded (§2's mechanism: user panic
  values and formatted diagnostics can embed addresses).
* (d) Result correspondence at iso-invariant observations (readouts
  `obs : ExecState → Bool` invariant under the heap iso, evaluated
  at main-exit). RECORDED as the successor statement — it is what
  the AllSchedules verdict captions would ultimately want — but it
  needs the iso machinery (§2) plus a main-confinement premise, so
  it is note-only this slice.
* (e) Full-state equality up to iso at QUIESCENT results (no thread
  strictly mid-segment). RECORDED as the eventual full theorem
  (Mazurkiewicz normal form territory); note-only.

## 4. The corrected statement — REVISED at the S4 audit fix round
## (the first attempt, `NPDRFClassReduction`, is REFUTED — §1a)

HISTORY, kept honestly: this section first shipped
`NPDRFClassReduction` (premise `¬ RacyFine` only) with the sentence
"unlike the draft, no known counterexample class applies". That
sentence is BANNED from this note and the code from the fix round on
— the audit refuted the statement three times through §1a's mechanism,
which the first truth argument never considered. The def is kept in
NPDRF.lean as the refuted intermediate record with its own
machine-checked refutation (`NPDRFClassReduction_refuted`, ported from
the audit's smallest counterexample), exactly the draft's treatment.

THE FIX-ROUND DECISION (both branches argued; FD8: either is success):

* (a) REPAIR with premises — CHOSEN. The premise space considered:
  - initial-`.exec` scoping (`m₀ = ⟨#[.exec prog env .stop], σ, 0⟩`):
    sufficient but stronger than needed, and couples the statement to
    a config constructor.
  - **single-threaded root: `m₀.threads.size = 1 ∧ m₀.cur = 0`** —
    CHOSEN: the weakest premise that excludes every exhibited pool
    (they are mid-run multi-thread or `cur ≠ 0` pools), matches the
    proved fragment theorem's shape, and makes §1a's avoidance
    argument available (every multi-thread coarse state then descends
    from a boundary reschedule).
  - a boundary-progress/fairness premise ("every thread's every
    segment reaches a boundary or terminates" — the Go-shaped
    blocking-discipline condition, since sync/chan ops ARE
    boundaries): REJECTED for the ∃-reachability form as unnecessary
    (§1a: needed segments are finite by construction, non-yielding
    segments are avoidable) and hard to state (a per-segment
    liveness condition). RECORDED as the premise the RUN-level
    normalization (plan step iii) will genuinely need — P-S4NP-5 in
    the parking ledger.
* (b) DEMOTE (no citable corrected statement; the open problem IS the
  statement; captions point only at the characterization + fragment).
  NOT taken, with the reason recorded: the repair below survives all
  three known mechanisms by construction (negative-checked in Lean),
  its truth argument now engages the coarse relation's binding
  constraint (§1a's avoidance) instead of overlooking it, and a
  fourth-mechanism refutation attempt (below) failed — while a
  demotion would leave successor slices without a stated goal. The
  epistemic cost of being wrong twice is priced in: the repaired def
  carries the failure history in its docstring, and its confidence
  label is "believed-true target, twice-revised", never more.

The repaired statement:

    def NPDRFClassReductionRooted : Prop :=
      ∀ m₀ : MultiConfig, m₀.threads.size = 1 → m₀.cur = 0 →
        ¬ RacyFine m₀ →
        ∀ res, ReachesMFine m₀ res →
          ∃ res', ReachesM m₀ res' ∧ res.sameClass res' = true

(`PoolResult.sameClass` unchanged: ctor-level; `.done` compared on the
`ExecOutcome` constructor. The ⊇ direction stays `reachesM_le_fine`.)

Truth argument — "known mechanisms 1–3 addressed below" (NEVER "no
known counterexample class applies"):

* Mechanism 1 (whole-state `.done`, ≥ 2-mid states): `sameClass` is
  blind to states. Unchanged.
* Mechanism 2 (allocation order in values/messages): `sameClass` is
  blind to values and messages. Unchanged.
* Mechanism 3 (`schedPick`/`cur` wedging): the premises exclude every
  pool that STARTS wedged or multi-threaded, and §1a's avoidance
  argument covers wedges arising mid-run: coarse is only forced onto
  a thread it picked at a boundary; the mimicking schedule for any
  fine-reachable result picks only threads whose next segment the
  fine run completed (finite by construction), realizing the fine
  run's registry-op order — parking/pairing/wake/spawn events all
  sit at boundaries, cross-thread value flow is HB-ordered through
  those same boundaries (race-free), and per-thread local computation
  is preserved; non-yielding segments contribute no registry op, no
  sync effect, and no class-visible observation, so the schedule
  never enters them.

Negative checks (machine-checked at the fix round, in NPDRF.lean):
each exhibited counterexample family FAILS the repaired premises —
the mechanism-1 pool `m0` has `threads.size = 3`; the audit's
stuck-`cur` pool `q0` has `cur = 1`; the two-thread stuck/`MultiWf`
family (reviewer + verifier variants) has `threads.size = 2`; the
spinner-wedged pools are multi-thread. And `NPDRFClassReduction_refuted`
pins that dropping the new premises recreates a FALSE statement.

The fourth-mechanism attempt (spent deliberately, recorded whether or
not it found anything — it did not): candidate mechanisms tried
against `NPDRFClassReductionRooted` and why each fails to refute:
1. **Wake-delay across a non-yielding segment** (fine wakes a parked
   thread while another spins mid-segment; coarse must wait): wake
   ENABLEDNESS (`wakeReady`) reads channel/sync cells, which only
   registry ops change — private steps never touch them — so
   enabledness is stable across segments and the avoidance schedule
   delays nothing it needs; the spinner itself is never needed.
2. **Allocation/pointer-identity observables** (make a result CLASS
   depend on address order): no modeled operation exposes an address
   as data — pointer equality compares `Loc`s (order-insensitive for
   distinct allocations), there is no addr→int conversion, and map
   iteration order over pointer keys is L-site latitude admitted in
   BOTH relations.
3. **Deadlock-order** (a fine-only-reachable `.deadlocked`): a
   deadlocked pool is all-parked/done — every thread AT a boundary —
   so every segment in its history completed; the sync-op order that
   produced the parked pattern is boundary-scheduled in both
   relations. No asymmetry to exploit.
4. **Arrival/partner-config dependence** (`arrivalCases` scans OTHER
   threads' configs, not just cells): partners are visible only as
   PARKED configs, and parking/pairing/waking all happen at
   boundaries, so the partner pattern at any registry op is fixed by
   the boundary-event order, which the mimicking schedule preserves.
5. **Stuck-segment truncation** (a thread's segment hits a
   fail-closed config): symmetric where it matters — fine cannot get
   that thread past the stuck point either; the partial segment's
   effects are private and class-invisible; coarse runs it only up
   to its LAST completed boundary, exactly as far as any result
   needs.
None produced a counterexample. Epistemic status, stated plainly:
this is an ARGUED target that already failed once in a revised form;
the argument now covers the coarse relation's two binding constraints
(forced continuation, `cur` consultation) explicitly, but it is not a
proof, and nothing may cite the def as proved. The proof route is
unchanged (§5's blocking machinery) PLUS the boundary-progress
premise for the run-level form (P-S4NP-5).

Statement-TCB posture: `NPDRFClassReductionRooted`, the refuted
`NPDRFClassReduction`, and their parts stay proof infrastructure.
`StepMFine`/`StepsM(Fine)`/`StepsMFineBS` and (from the fix round)
`BoundarySwitch` are in the Audit statement-closure forbidden set;
nothing headline-shaped may depend on them; the 48 designated
statements stay byte-identical.

## 5. The proof plan and the honest fragment boundary (drawn BEFORE
## proving)

PROVED THIS SLICE (each with its consumer):

* **P1 — the machine-checked refutation** `NPDRFReduction_refuted :
  ¬ NPDRFReduction` (§1's construction). Consumer: the statement
  itself — the "refutable as written" marker becomes a theorem; the
  captions and Audit cite it instead of prose.
* **P2 — the exact characterization of the gap**:
  `BoundarySwitch m i` (the pick is at a boundary of the running
  goroutine, or is the running goroutine), with
  `schedPick_iff_fine_bs : schedPick m i ↔ schedPickFine m i ∧
  BoundarySwitch m i` and
  `stepM_iff_fine_bs : StepM m m' ↔ StepMFine m m' ∧
  BoundarySwitch m m'.cur`, plus the run-level corollary (the coarse
  closure is exactly the boundary-switched fine closure). Consumers:
  the caption formula (§6) — "registry-point schedule set" acquires a
  machine-checked definition as a RESTRICTION of full interleaving
  rather than a separate relation; the P3 fragment proof; the
  successor normalization (its target shape is "reorder a fine run
  into a boundary-switched one", and P2 is the lemma that makes a
  boundary-switched run coarse).
* **P3 — the proved fragment of the corrected statement**:
  pools single-threaded THROUGHOUT (the fix round renames the record:
  the earlier "never-spawning" gloss admitted multi-thread
  spawn-free pools — e.g. the refutation's own `m0` — that the
  theorem's `hns` premise excludes). For `m₀` with one thread,
  `cur = 0`, and
  every fine-reachable pool still single-threaded, the fine and
  coarse closures coincide (`stepsMFine_to_stepsM_single` via P2 —
  a lone runnable thread's fine pick IS boundary-switched), hence
  `ReachesMFine m₀ res ↔ ReachesM m₀ res` LITERALLY — strictly
  stronger than `NPDRFClassReduction`'s conclusion on this class,
  and without needing the `¬ RacyFine` premise. Consumer:
  `npdrfClassReduction_single_fragment` — the corrected statement's
  conclusion discharged on the fragment (its non-vacuity instance:
  the statement shape is inhabitable), plus a concrete witness pool.
  Honesty rider, stated where the theorem lives: this fragment is
  the sequential-degenerate class at relation level — the concurrent
  content of the corrected statement remains open.

NOT PROVED THIS SLICE — the honest boundary, with the blocking
machinery named and sized:

* The genuinely-concurrent ⊆ direction (any spawning class), because
  the normalization induction needs, in order:
  1. **A footprint-frame theorem over the step function** ("a private
     step reads only cells its recorded footprint covers, writes only
     cells its footprint covers plus fresh ones") — without it,
     footprint-disjointness (what DRF gives) implies nothing about
     step commutation. This is a whole-interpreter induction in the
     `*_wf` family's mold; measured precedent: `applyStrictOp_wf`
     alone is ~540 lines over a 60-arm applier surface (S3 build
     log). Estimate: 1–2 dedicated slices.
  2. **The heap-iso quotient** (§2) for anything stronger than class
     level: iso definition, iso-respecting step lemma, iso-invariant
     observation class. Estimate: ~1 slice.
  3. **The permutation engine** (Mazurkiewicz normal form over fine
     runs, registry-order-preserving). Estimate: ~1 slice given 1+2.
  The path-level (same-root) movers of obstruction 6 sit inside 1.
* The detector coupling (plan step iv) — §7.
* The existing mover kernel (`storeLoc_root_frame`,
  `loadLoc_after_disjoint_store`) is REUSED as-is (it is the seed of
  blocking item 1); no re-proof, no consumer-less extensions — the
  charter's every-lemma-has-its-consumer rule is why obstruction 6's
  path-level lemmas are NOT proved this slice: their consumer is the
  unbuilt footprint-frame theorem.

Axiom posture (FD7): all new theorems land in the constructive
simulation-lane set [propext, Quot.sound] — the plan's proofs are
executable-computation + relation-induction; the mover pair's
recorded Classical.choice inheritance stays confined to the mover
pair. `decide`-discharged side goals only on `#eval`-validated
concrete computations (§1's probe discipline). No `partial`, no
`sorry`, no `native_decide`; structural induction on the closures.
A local derived `BEq`/`DecidableEq` instance for `Config`-carrying
comparisons, if needed, follows the recorded FD7 BEq-deviation
precedent and is cited in §8.

FD6 window argument (recorded here once, cited per commit): every
Lean change this slice is in `GoLean/GoCore/NPDRF.lean` (+ Audit
registration + docstring-only caption edits) — a THEOREM-ONLY leaf
module imported only by the `GoCore.lean` aggregator; the interpreter
(`StepFn`/`Machine`/`Multi` executable path) does not move, so no
behavior can change and the differential window is closed by
construction. `scripts/ci` (with its standing baseline diff of the
last recorded run) is the per-commit gate; no `--diff` (nothing
runtime-reachable moves — the S4/S6 spec-parity precedent).

## 6. The caption formula (FD1's one-time update) and site inventory

THE FORMULA — one consistent text, adapted per site only in the words
before the colon:

> ∀-schedule scope (NPDRF settled at channel-logic S4,
> `docs/2026-08-11_npdrf-reduction.md`): "every schedule" = every
> REGISTRY-POINT schedule — the modeled path set, i.e. full
> per-machine-step interleaving RESTRICTED to boundary switches
> (`stepM_iff_fine_bs`, NPDRF.lean). The draft claim that race-free
> programs behave identically under unrestricted interleaving is
> REFUTED as originally stated (`NPDRFReduction_refuted`:
> whole-state results + ≥ 2 leaked mid-segment goroutines; the fix
> round's first corrected attempt is ALSO refuted,
> `NPDRFClassReduction_refuted`); the repaired class-level reduction
> (`NPDRFClassReductionRooted`, single-threaded roots) is the
> recorded open target, proved so far only for pools single-threaded
> throughout. For spawning programs these theorems claim registry
> granularity ONLY; sub-registry transfer is unproved.

Site inventory (the sweep is ONE commit; docstrings/comments only —
designated STATEMENTS stay byte-identical, and the Comparator mirror
files `proofs/Challenge.lean`/`proofs/Solution.lean` are excluded
entirely by the byte-identity discipline):

1. `GoLean/GoCore/NPDRF.lean` — module docstring rewritten to the
   settled state (refutation now a theorem; obstruction list
   re-graded: 4 discharged-by-refutation-and-correction, 1/2
   upgraded per §2, 3 already discharged, 5/6 carried).
2. `proofs/GoLeanProofs/Surface.lean` — `ProgressExecC` docstring's
   "every modeled schedule" parenthetical gets the formula pointer;
   the witness-status note likewise.
3. `proofs/GoLeanProofs/Specs/GooseParityChannels.lean` — module
   header (the seeded-strength paragraph) + the `chanCert_noDeadlock`
   / `chanCert_noRace` / `chanCert_allSchedules` docstrings' "NO
   modeled schedule" wording.
4. `proofs/GoLeanProofs/Specs/GoldenForkJoin.lean` +
   `GoldenSelectDone.lean` — the ∀-SCHEDULE witness docstrings.
5. `GoLean/GoCore/MultiStreams.lean` — module header ("on ANY modeled
   schedule").
6. `docs/2026-08-04_nondeterminism-doctrine.md` — the racy-lane
   caption's "the NPDRF obligation's territory", the confluent
   caption's same phrase, and the slice-4 scope-limit paragraph's
   final sentence, updated to the settled formula (same commit as the
   Lean caption sweep, per the slice charter).
7. `docs/2026-08-07_goose-comparative-scoping.md` — rows T12 and L3's
   our-side text ("currently a REFUTABLE-as-written draft" → the
   settled state; the DEL/ANALYSIS verdicts unchanged — the open
   debt REMAINS open for spawning programs, now precisely scoped).
8. `TODO.md` line citing "NPDRF mover lemmas as its eventual proof"
   — pointer refreshed to this note's §5 boundary.
9. `docs/BUGS.md` — only if an entry cites the draft statement's
   marker (checked at sweep time; BUG-040/044 entries reference the
   obligation contextually).
10. Found at sweep time by the module-wide scan (grep for every
    "every schedule"/"∀-schedule"/"all schedules" phrasing outside the
    excluded Comparator mirrors) and added to the sweep:
    `Surface.lean`'s witness-status note and `GoSpecC` docstring,
    `Specs/SpawnNoopProgress.lean`'s assembled-`GoSpecC` docstring,
    `LangD.lean`'s completion-half kernel-certificate docstring, and
    `Specs/ChanRendezvous.lean`'s module header (covers its cert
    docstring). `Specs/ChanVacuityWarning.lean` needed nothing — its
    text is ABOUT the absence of a ∀-schedule claim.

Historical slice notes (`2026-08-06_channels-arc-design.md`'s build
logs, spec-parity notes) are records of their dates and are NOT
rewritten; this note supersedes their NPDRF status lines by being the
dated successor record.

What each outcome buys the captions (the too-narrow risk addressed):
the captions do NOT strengthen — they keep claiming registry
granularity, now with a machine-checked characterization of what that
set IS and a theorem-backed statement of why the stronger claim was
not made (refuted as drafted; corrected form open). No caption may
cite `NPDRFClassReduction` as if proved; the formula's last sentence
is the guard.

## 7. The FD5 decision rule, evaluated (the slice's LAST section by
## charter order; recommendation only — the rule decides)

The rule: IF the proven NPDRF fragment supports a
detector-completeness theorem over modeled schedules at ≤ one slice's
cost, prove it in slice 5; ELSE record the asymmetry as permanent
with the O4/T12 axis split as its statement.

What detector-completeness needs (the theorem: no registry-point
schedule of a modeled program exhibits a co-enabled `stepAccesses`
conflict that the segment-HB detector misses — i.e. coarse-RacyFine
⇒ some/the corresponding `execProg` run ends `raceDetected`):

1. A vector-clock-soundness/completeness invariant relating
   `RaceState` (clocks, shadow, epoch subsumption, `wokenPartner`
   recovery, the replicated stream consumption in `raceUpdate`) to a
   relational happens-before over coarse runs — a FastTrack-style
   correctness argument over ~10 event classes (spawn, slot ops,
   rendezvous, close, sync acquire/release ×4, chanObj, wgSema).
2. A bridge from the RELATION (`StepsM`) to the DRIVER
   (`execProgLoop` with the detector riding along), since the
   detector exists only on the executable side.
3. The co-enabled-conflict ⇒ eventually-checked argument (a conflict
   between two runnable next-steps implies some schedule executes
   both accesses HB-unordered and the second one's check fires).

What THIS slice's proofs contribute to that: P2 (the
characterization) and P1 (the refutation) relate coarse and fine
SCHEDULING; they do not touch the detector at all.

Pre-existing assets, ALL of them on the table (RE-SIZED at the S4
audit fix round — the first form named only one asset, understating
what exists and thereby biasing the measurement toward the branch it
recommended; corrected per the audit's FD5 finding):
* the shared `stepAccesses` table (obstruction 5) — item 3's
  vocabulary is already aligned;
* the single-step relation↔executable correspondence
  `stepMulti_sound`/`stepM_complete` (MultiSound.lean, pre-slice;
  this slice's own refutation leans on the latter) — the SEED of
  item 2's bridge. What item 2 still needs beyond it: run-level
  composition (`stepM_complete` is single-step and ∃-quantified over
  streams, with no splicing lemma) and the DETECTOR-carrying half
  (`execProgLoop` threads a `RaceState` through `raceUpdate` after
  every step; the correspondence is detector-free). Item 2 is
  therefore a real but SUB-slice-sized work item, not a from-scratch
  bridge.

**Evaluation: the rule's condition is still NOT met, on item 1's
dominance.** With item 2 re-priced down, the sizing rests where it
always should have: item 1 — a FastTrack-style vector-clock
soundness/completeness argument over the ~10 event classes, plus the
`wokenPartner` recovery and `raceUpdate`'s stream replication — is
alone comparable to the whole S3 detector build and plausibly exceeds
one slice by itself; item 3 rides on 1. Honest total: 1.5–2.5 slices.
Recommendation to the rule: take the ELSE branch — record the
asymmetry as permanent with the O4/T12 axis split as its statement
(ours: executable, oracle-aligned, differentially testable detection
with the racy/litmus lanes; theirs: granularity-complete-by-
construction race-UB with no way to test it). The completeness
theorem remains statable later; nothing this slice closes that door.
Slice 5's decider should weigh item 1's dominance — the bridge is no
longer the argument. Per the charter, either branch is SUCCESS and
the lane does not stop.

## 8. Slice record (appended per commit)

* Commit 1 (this note): binding design committed before proof work.
  Gate: `scripts/ci` green (docs-only).
* Commit 2 (the settled statement layer — P1+P2+P3, one movement per
  the note's plan; all in `GoLean/GoCore/NPDRF.lean` + Audit
  registration): **P1** `NPDRFReduction_refuted` machine-checked
  exactly as §1 planned (finite-state: `FineInv` for `¬ RacyFine`,
  `CoarseInv` — at most one strictly-mid goroutine, forced-`cur`
  coupling — for `¬ ReachesM`, coarse inversion via `stepM_complete`,
  fine run via `stepFn_sound`); **P2** `BoundarySwitch` +
  `schedPick_iff_fine_bs` + `stepM_iff_fine_bs` + the run-level
  `StepsMFineBS`/`stepsM_iff_fine_bs`; **P3**
  `reachesMFine_iff_reachesM_single` (never-spawning fragment,
  LITERAL result equality, no race-freedom premise) +
  `npdrfClassReduction_single_fragment` + the degenerate-by-design
  witness pool. `NPDRFClassReduction`/`PoolResult.sameClass` land as
  the citable open target, scaffold-marked. AXIOMS: every new theorem
  in the constructive set [propext, Quot.sound] (Audit-pinned) — the
  §5 posture met exactly; no BEq/DecidableEq instance ended up needed
  (the FD7 deviation rider was not exercised). `StepsMFineBS` joined
  the statement-closure forbidden roots. FD6 window argument (§5):
  NPDRF.lean is a theorem-only leaf module — interpreter untouched,
  no `--diff` owed. Gate: `scripts/ci` green (proofs+Audit, eval
  tests 136 ok, baseline diff 1483/1483 no regression).
* Commit 3 (the FD1 caption sweep, ONCE): the doctrine gains the
  section "The NPDRF status — SETTLED captions (2026-08-11)" as the
  formula of record; the three doctrine scope lines point at it
  (racy caption, confluent caption, the BUG-040 scope-limit
  paragraph); Lean docstring sites per the §6 inventory + item 10's
  scan additions; comparative-scoping rows T12/L3 restated
  (settled-but-open; DEL/ANALYSIS verdicts unchanged); TODO's
  verified-POR line points at §5's sized machinery. No caption
  strengthened — every site now says registry granularity ONLY with
  the refutation and the open corrected target named. Designated
  statements untouched (statement-TCB closure green; Comparator
  mirrors excluded from the sweep by the byte-identity discipline).
  Gate: `scripts/ci` green.
* Commit 4 (slice-record close):

  **TCB-grounding walk (the per-slice review criterion, S1 form).**
  Exported artifacts this slice, each with (i) what the trusted claim
  reduces to, (ii) machinery placement, (iii) the executable anchor:
  - `NPDRFReduction_refuted` — (i) reduces to concrete-interpreter
    propositions: `stepFn`/`stepMulti` computations on literal pools
    (the per-phase step lemmas are `rfl`/simp equalities about the
    executable machine) plus the relation definitions the draft
    statement itself is made of; (ii) `FineInv`/`CoarseInv` and the
    inversion plumbing are proof-side only; (iii) the executable
    anchors are the `stepFn`-equality lemmas themselves, `#eval`-
    probed before proving. No Iris, no WP, no fuel.
  - `stepM_iff_fine_bs` / `stepsM_iff_fine_bs` / the fragment family —
    relation-level proof infrastructure over `Multi.lean` definitions;
    all carriers (`StepMFine`, `StepsMFineBS`, …) are in the Audit
    statement-closure forbidden set, so none can enter a designated
    statement. Nothing this slice is a `GoLeanProofs.Specs.*`
    triple-carrying export, so the completion-pin convention owes no
    `TerminatesNormallyC` member; the caption sweep is the slice's
    user-facing surface and it only WEAKENS/clarifies claims.

  **Deletion test.** Nothing headline-shaped shipped; the Audit
  anchors (`NPDRFReduction`, `NPDRFClassReduction`,
  `PoolResult.sameClass`, `BoundarySwitch`, the axiom pins) are the
  drift guards, and deleting any S4 artifact fails the proofs+Audit
  gate.

  **FD3 attestation.** NO designation candidate this slice: every new
  statement is proof infrastructure or a scaffold target, none is a
  headline-shaped theorem over interpreter vocabulary alone with a
  user-facing claim (the fragment's literal-equivalence theorem
  quantifies relation carriers, which the statement-TCB forbids from
  designated closures by design). Recorded in the charter's FD3
  ledger.

  **FD5 (§7) — post-proof confirmation.** What was actually proved
  matches the §7 evaluation's assumption exactly (P1/P2/P3, nothing
  detector-facing), so the evaluation stands as written: the rule's
  condition is NOT met; recommendation remains the ELSE branch
  (permanent asymmetry, O4/T12 axis split as the statement). The rule
  decides at slice 5.

  **Parking ledger (S4).** Parked, each with its §5 sizing: P-S4NP-1
  the footprint-frame theorem over `stepFn` (1–2 slices; blocks any
  spawning-fragment proof of `NPDRFClassReduction`); P-S4NP-2 the
  heap-iso quotient (~1 slice; blocks every stronger-than-class
  observation); P-S4NP-3 the permutation/normalization engine
  (~1 slice given 1+2); P-S4NP-4 obstruction 6's path-level movers
  (inside P-S4NP-1; not proved this slice because their consumer is
  P-S4NP-1 itself — the every-lemma-has-its-consumer rule). No
  mid-slice question required a park outside the FDs; no hard-stop
  condition was approached (interpreter untouched, no designated
  statement moved, no gate weakened).

  Gate: `scripts/ci` green at the close commit.

### S4 audit fix round (2026-08-11; 1 confirmed major + minors — the
### coordinator's list; every item below names its disposition)

RECORD CORRECTIONS to this note's own §8 (the record must say what
actually happened):
* Commit-2's entry claimed the module docstring's "obstruction list
  re-graded: … 1/2 upgraded per §2". FALSE at c085036b — obstructions
  1/2 and obstruction 4's BODY were byte-identical to the pre-slice
  text (audit finding, machine-checked byte comparison); only
  obstruction 4's header changed. The re-grade happens FOR REAL in
  this fix round's Lean commit; the false ledger sentence stands
  corrected here rather than edited away.
* §6 item 10's "module-wide scan" claimed completeness it did not
  have: the grep patterns ("every schedule"/"∀-schedule"/"all
  schedules") structurally missed "NO (modeled) schedule" phrasings
  and two files (`Specs/ChanTransfer.lean`,
  `Specs/ChanRendezvousVal.lean`) containing the literal string
  "every schedule" that the scan nonetheless failed to surface. The
  fix round re-runs the sweep with widened patterns ("every
  schedule", "all schedules", "∀-schedule", "modeled schedule",
  "NO schedule", "modeled path set") and records the result at its
  commit entry below.
* The doctrine's formula-of-record bullet gave the ARGUED
  allocation-order refutation the same "REFUTED" force as the
  machine-checked one — fixed with an explicit "(argued, not
  machine-checked: note §2)" label; same labeling discipline applied
  here: mechanism 1 and 3 refutations are THEOREMS
  (`NPDRFReduction_refuted`, `NPDRFClassReduction_refuted`);
  mechanism 2 is an ARGUMENT.
* One doctrine cross-reference pointed the wrong way ("above" for a
  section that is below) — fixed.
* "never-spawning" as the fragment's name over-claimed (admits
  multi-thread spawn-free pools the theorem excludes — including the
  refutation's own `m0`); renamed "single-threaded throughout" at
  every occurrence.
* The TCB-grounding walk's "all carriers are in the forbidden set"
  overstated: `BoundarySwitch` was not — it IS added to the
  forbidden roots at the fix round (it is proof infrastructure like
  its siblings; the alternative of arguing its exclusion was
  rejected as a needless review burden).
* Consumer-less lemmas `stepDone`/`done_aC`/`done_bC` deleted (the
  anti-scaffold rule the note itself invokes; they were shipped
  unused).
* The fragment gains a STEPPING non-vacuity witness beside the
  degenerate one (the audit demonstrated the ~50-line shape; the
  degenerate witness stays, both honestly labeled).

* Fix commit 2 (the statement layer repaired — Lean):
  `NPDRFClassReduction_refuted` machine-checked in-tree (the audit's
  smallest counterexample ported with attribution, `qAt`-parametrized
  so one invariant serves the refutation AND the stepping witness;
  constructive [propext, Quot.sound]); `NPDRFClassReductionRooted`
  shipped per §4 with the failure-history docstring; NEGATIVE CHECKS
  machine-checked (`m0_fails_rooted`, `q0_fails_rooted`,
  `wedgedPairRep_fails_rooted` — axiom-free `decide`; every exhibited
  family fails the rooted premises); `steppingRootPool` witness
  (real fine step through the proved iff); obstruction list actually
  re-graded in the file (1/2 upgraded, 4 settled, 7 added);
  `BoundarySwitch` into the forbidden roots; consumer-less
  `stepDone`/`done_aC`/`done_bC` deleted; fragment + consumer renamed
  single-threaded-throughout (`npdrfClassReductionRooted_single_fragment`).
  Gate: `scripts/ci` green (first run caught an `Exists.choose` in
  the refutation term pulling `Classical.choice` — replaced with
  constructive `obtain`; the FD7 posture held).
* Fix commit 3 (the caption RE-SWEEP, recorded): scan re-run with
  widened patterns ("every schedule", "all schedules", "∀-schedule",
  "modeled schedule", "NO schedule", "modeled path set") over
  `proofs/` + `GoLean/` + maintained docs. Newly captioned: the two
  missed spawning-program certificates
  (`Specs/ChanTransfer.lean`, `Specs/ChanRendezvousVal.lean` — the
  audit's finding: both matched the ORIGINAL scan strings and were
  missed anyway), `Surface.lean`'s `TerminatesNormallyC`, the
  designated `forkJoinNoDeadlock`/`forkJoinNoRace` docstrings
  ("NO schedule" un-qualified — verifier's bonus finding), and the
  spec-parity R3 manifest's "EVERY modeled schedule" sentence.
  Target-name updates at every pointer site (doctrine bullet — now
  naming the refuted intermediate and the repaired target with the
  argued-vs-machine-checked labels and the fixed cross-ref —
  GooseParityChannels header, GoldenForkJoin witness, Surface
  ProgressExecC parenthetical, comparative-scoping T12/L3).
  Deliberate exclusions, recorded: `Challenge.lean`/`Solution.lean`
  (Comparator mirrors, byte-identity); dated slice notes
  (records of their dates — the doctrine section supersedes);
  `Audit.lean`'s descriptive inventory comments (labels, not
  claims); `ChanVacuityWarning.lean` (its text is ABOUT the absence
  of a ∀-schedule claim); `ForkJoinTargets.lean:98`
  (cross-reference, not a claim). Residual scan hits after the
  sweep: every "every/all/NO/modeled schedule" occurrence in
  `proofs/`+`GoLean/` outside the exclusions now sits within one
  docstring of an S4 rider. Gate: `scripts/ci` green.
