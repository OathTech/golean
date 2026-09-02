# The essence-of-Go doctrine — the two bounds (2026-08-11)

Status: ACCEPTED (user, 2026-08-12) with the de-facto-spec evidence class added at acceptance — the project-charter articulation (Mike,
2026-08-11), written as binding doctrine. On acceptance: CLAUDE.md carries
the compact form; the nondeterminism doctrine is rewritten beneath this;
every future charter names the portable semantics as the goal.

## What we are building

**A trustworthy, portable Go semantics** — not a model of any particular
implementation, test suite, or scheduler. The machine we want is the
WEAKEST machine that Go can plausibly ever do: the semantics that
exercises *all* degrees of freedom latent in the language. Verifying
programs against the exact behavior we have already observed verifies
nothing worth having; any real implementation dramatically subsets the
permitted behavior — most dramatically in concurrency (cf. Cerberus:
years reconstructing what the C standards committee thought might be
allowed).

## The two bounds

- **Differential testing establishes the LOWER bound.** "We saw this
  datapoint." Its entire meaning is membership: real Go behavior ∈
  modeled Go behavior. The oracle can never validate the model's width —
  it can only witness members and expose too-narrowness.
- **Reasoning, the spec, the memory model, and documentation establish
  the UPPER bound.** "Go will never do this." Go is not chaos — it makes
  real guarantees (happens-before edges, DRF-SC, typed memory, the
  ordered subset of evaluation) — and the upper bound is *argued from
  evidence*, never asserted from silence alone.

**The bug definition:** if a conforming Go implementation does something
our machine cannot, that is definitionally a bug somewhere — far more
likely in GoLean than in Go. `observed ∉ modeled` is always
red, never latitude.

**Scheduling and fairness ([USER] 2026-09-02).** Mike, verbatim: "the
semantics should admit unfair schedules, i.e scheduling is local and
nondeterministic. Fairness is an assumption about the sequences that
are chosen." The principle, named: **the weakest machine ADMITS every
schedule, the starving ones included; fairness is a hypothesis on the
chosen choice sequence, stated where it is used, never a constraint
the machine enforces.** This confirms the existing design rather than
changing it — (i) the scheduler pick is a local demonic choice at
every scheduling point: L1 (`runnableIdxs`/`stepMulti`, Multi.lean —
"ANY runnable goroutine may run next"), drawn at the sites
`{l1Sched, l5ExitWindow, postOp, backEdge}` (`ChoiceSite`,
State.lean); (ii) the upper-bound argument is the scheduling dossier
§3.1 (`docs/2026-08-20_go-scheduling-semantics-dossier.md`: no
language-level guarantee that a runnable goroutine ever runs — a
maximally portable model must admit postponing one forever); (iii)
the always-spin schedules are therefore MEMBERS of the envelope by
right and are COUNTED, never claimed away, by the `nonterm=`
accounting (boundary-set note §5d; corpus row
`goroutines/send-then-spin`; register #1); (iv) `Fair : Choices →
Prop` is a reasoning-side hypothesis over streams — a future
definition in the reasoning repo that theorems ASSUME, quantifying
over exactly the four scheduling sites (State.lean's `ChoiceSite`
docstring), never a machine-side filter (register #1 residue (ii)).
Consequence for the one place the spec's text is distributional AND
mandatory — select's uniform-pseudo-random clause
(spec#Select_statements; inventory C6; assessment p2-keeps-a1 A1-12):
the weakest machine ADMITS the schedule that starves a
permanently-ready clause forever; probability-1 non-starvation is a
fairness assumption on the chosen sequence, stated where used. That
is the doctrine's position, not a hedge: C6's envelope is
support-equal to the spec's on finite traces and deliberately wider
on infinite ones.

## Evidence classes for the upper bound

In rough order of authority: the language spec's text; the memory model
document; runtime/library documentation; **the deployed-program corpus as
de-facto spec** — "does this program behave as people expect" is a
powerful argument, because an implementation cannot plausibly break
behaviors that a large body of running code depends on (this is much of
why C is such a mess: decades of old code pinning committee-unintended
behavior; Go is the best-behaved case — the Go 1 compatibility promise
institutionalizes the constraint, and the team's deliberate map-iteration
randomization shows them actively *preventing* de-facto pins they don't
want honored); cross-implementation observation (gc across versions,
gccgo, tinygo); proposal and issue-tracker archaeology (committee-intent
reconstruction, Cerberus-style); measured gc behavior (a lower-bound
instrument that can also *motivate* narrowing arguments, never conclude
them). All of these lanes eventually feed the model. Simplifying
assumptions are permitted — recorded in the register below, never
silently.

## The language-version pin (2026-08-17, spec-truth campaign)

"Go" is versioned semantics: the go.mod `go` directive selects language
behavior (the 1.22 loop-variable change is the canonical example).
**GoCore models the Go 1.26 language.** The concrete pins — spec text at
`go1.26.5`, oracle toolchain, and their agreement rule — live in
`docs/spec-sources.md`; re-pins are deliberate, both sides together,
with the reason recorded. Upper-bound arguments cite the pinned spec,
never the live web page.

## Pins are scaffolding

Deterministic pins of spec latitude (matching gc's realization where the
spec permits many behaviors) were legitimate velocity scaffolding while
the machinery was being built. Under this doctrine each pin carries a
**re-envelope obligation**: it is a recorded debt, not a fidelity
achievement, and no record may present gc-conformance at a latitude
point as correctness. The latitude inventory (companion document)
enumerates every pin with its obligation and estimated cost.

## The simplifying-assumptions register

The honest list of every place the machine models less than the
plausible envelope. Seeded at drafting; the latitude inventory will
extend it; every entry names what is assumed, why, and what removing it
costs. We do not BS ourselves about the distance to the goal.

CITATION RULE (2026-08-31, fixing the numbering collision found by
fidelity A1-45): the inventory's §8 extension numbered its entries to
continue this register's original FIVE, but this register later grew
entries 6–7 — so a bare "#6"/"#7" is ambiguous across the two binding
documents. Cross-references must qualify by name: "register #6
(allocator quotient)" / "register #7 (unbounded memory)" here, vs
"extension #6 (int width)" / "extension #7 (library-doc-silent pins)"
for inventory §8 (short form "§8 e6"…"§8 e13", already in use). Never
write a bare "#6"/"#7".

1. **Scheduling is gc-shaped — DISCHARGED (W3.2 slice 1, stages C+D,
   2026-08-20/21; G1 ruling of 2026-08-20).** The two narrowing seams
   are widened: every registry-op COMPLETION is a scheduling point
   (B1 — the `.opDone` marker, site `postOp`; envelope statement at
   `Config.opDone`, Machine.lean) and every loop BACK-EDGE is a
   scheduling point (B2 — site `backEdge`; envelope statement at
   `Config.atBoundary`, Multi.lean), both grounded in the
   scheduling-semantics dossier (§1.1 scheduling deliberately
   unspecified; §3.1 the spec allows starvation; §4.3 the wedge
   verdict). THE FORMER DEFINITIONAL BUG IS DEAD: the SEND-THEN-SPIN
   wedge's completing execution (gc: exit 0, 42 — 60/60, +20/20 at
   GOMAXPROCS=1) is a MEMBER again — machine stream `[0,0,1]` realizes
   it (pre-widening: 511/511 fuel-out over the exhaustive mod-2
   depth-8 sweep), and the corpus row
   `goroutines/send-then-spin` certifies the terminating set {42} with
   the always-spin schedules counted honestly (the §5d nonterm
   accounting) — in the envelope BY RIGHT, per dossier §3.1, exactly
   §4.3's "the completing execution and an unfair execution".
   Records: `docs/evidence/2026-08-12_scheduler-wedge-probes/` (the
   discovery), `docs/evidence/2026-08-20_w32-postop-probes/` (the
   flip). RESIDUE, stated: (i) the abort window at panic terminals is
   B3 — RE-GROUNDED 2026-08-31 (probe-evidenced, runtime-text-argued;
   evidence `docs/evidence/2026-08-31-b3-abort-window-probes/`): the
   window is post-`.panicked` ONLY — post-RAISE partner progress is
   already modeled (`.panicking` is a live, steppable state) — and a
   56-run directed probe campaign (three designs, incl. a merged-fd
   post-traceback ordering probe and `dontfreezetheworld`) found ZERO
   observed-∉-modeled exhibitions; the residual is the UPPER-bound
   class only, argued from gc's own freeze-is-best-effort runtime
   text (proc.go — the window exists but is output-invisible by
   construction), not from probe silence (inventory C3); (ii) ∀-stream termination of spinner shapes is the
   liveness tier's `Fair` question — FUTURE WORK, precisely: no
   `Fair`/`FairStream` predicate is a Lean definition in this tree,
   the parked reasoning branch, or any branch tip
   (verified 2026-08-31, phase-2 fact claim 7 — branch tips checked,
   not full history); what EXISTS is the
   semantics-side half, the `backEdge` choice site whose docstring
   records that a fair scheduler is EXPRESSIBLE over it (non-vacuous
   BY B2) — the predicate itself is a planned reasoning-side
   artifact; (iii) scheduling points remain
   REGISTRY/BACK-EDGE-granular, not per-instruction — register #5's
   residual, the reduction line's territory. (The 2026-08-12 exhibit
   correction stands: a REGISTRY-FREE spinner was never this bug —
   gc's exit-0 there was already in the modeled set via the default
   stream.)
2. **Sequential evaluation-order latitude is pinned**, each axis to a
   recorded conforming point — gc's where pinnable (call-vs-operand
   order, BUG-052), OURS where gc's realization is compiler-internal
   (inter-target order E3, targets-vs-RHS E4), STRUCTURAL (frontend
   ANF) on the call-first family (binop operand order E12,
   non-call-panic vs sibling calls E13, receiver-vs-arguments E14 —
   axes censused 2026-08-17/20/22, after this entry's original
   wording), and hidden-dep init order to go/types' point (E7) — with
   the known ≠ gc cases (**E3, E7, E13 on its type-assertion axis, and
   E5** — synced 2026-08-31 to inventory §10's honesty-critical list,
   which this entry had drifted one short of, phase-2 finding A1-04;
   §10 also lists R3, a representation row outside this entry's
   evaluation-order scope) carried as standing deviation records
   queued for re-envelope (inventory §7 items 3 and 5) — EXCEPT E5,
   whose class changed 2026-09-02 ([USER] ruling): the early store
   across the assignment phase boundary is a FORCED point
   (spec#Assignment_statements' two-phase sentence), the machine holds
   it, and gc's contrary realization is a recorded gc DEVIATION
   (`docs/spec-divergence-ledger.md` L-016, the exception channel of
   the bug definition above: the standard and gc disagree, so the
   finding is gc's). E5 stays in the known-≠-gc enumeration because
   the oracle disagrees there; it carries NO re-envelope debt (the
   obligation is withdrawn — widening toward gc's point would take
   the machine past what Go permits). STANDING
   RULE (2026-08-31): this entry's known-≠-gc enumeration is kept in
   sync with inventory §10's "Known-≠-oracle deterministic points"
   list — any edit to that list edits this sentence in the same
   change. This wording adopts and supersedes
   §8's prescribed sentence: its "permanent deviation records" phrase
   is dropped, because under the bug definition a probed gc-elsewhere
   observation is an observed-∉-modeled candidate — a debt with a
   queue position, never a divergence we are at peace with (that
   stronger reading is this register's own gloss, not §8's).
3. **One-implementation evidence base**: the differential oracle is gc
   at a pinned version; no cross-implementation lane exists yet.
4. **SC-only interleaving within DRF** (reworded 2026-08-31 per the
   [USER] fidelity ruling, decision 1, and phase-2 findings
   A1-06/A1-07; MEASURED 2026-09-02 by the detector-soundness
   differential, `docs/2026-09-02_detector-soundness.md` — decision
   1's named owner for detector completeness, closing A2-Q3's circular
   delegation): correct per the memory model's DRF-SC promise for
   the programs we accept (mem#model states it formally with the
   Boehm–Adve proof pointer; mem#overview informally — anchors added
   at the P2 retrofit). Racy EXECUTIONS refuse fail-closed, and the
   refusal is **per-RUN**, not per-PROGRAM — the detector's own
   wording (`raceUpdate`, Multi.lean:1181): "races fail closed per
   run, on every run where the conflicting accesses execute";
   program-level refusal holds exactly as far as the corpus
   apparatus's enumeration reaches and the granularity reduction
   (register #5's NPDRF obligation) holds — the machine computes no
   per-program acceptance judgment. THE HONEST STATE OF "racy →
   refused", as measured (numbers derivation-anchored in the report's
   evidence dir): **DETECTED** — HB-based (the FastTrack skeleton over
   TSan's realized edge set), the refusal fires on every run in which
   both conflicting accesses execute, whatever the interleaving; on
   the in-scope corpus at the branch tip (364 rows — every racy/
   membership/confluent row plus every concurrency-tagged strict row
   — 10 `-race` runs each at GOMAXPROCS 1 and 8 vs the schedule
   enumerator; the audit fix round's re-run with the hardened runner,
   `corpus-tip.*`) the third cell (gc red, machine DRF) is **2/364 —
   exactly BUG-080's two pins** (the first draft's "0/362" was a
   362-row snapshot that pre-dated the pins, and the first runner had
   filed them "uncertified" behind an undeclared site bound — audit
   B2); the other 23 gc-red rows are machine-refused on EVERY
   enumerated path, 275 doubly-certified rows agree DRF (277 after
   the deep re-run), the 1 over-refusal is the recorded O1 residual,
   63 rows (61 after) are uncertified — none of them gc-red. **NOT
   DETECTED**, three classes: (i) the sync primitives' OWN state
   words (U4 → **BUG-080**, born-FAIL pinned 2026-09-02 and FIXED the
   same day by the access-KIND slice, [USER]-ruled ahead of the
   atomics arc): a plain copy/overwrite of a primitive another
   goroutine is operating on is racy by mem#model and TSan-red
   10/10; the machine USED to run it to a value (the probe leg's third
   cell was exactly this class — 2/45 value-run + 3 uncertifiable-by-
   fatal-members, all U4). Since the fix `RaceAccess := AccessKind ×
   Loc` (read/write/atomicRead/atomicWrite; conflict = at least one
   write ∧ not both atomic — the register's own sentence) and the sync
   arm records TSan's realized per-primitive set at the primitive's
   path: the corpus HOLE cell is 0/368 (`corpus-bug080.*`, 368 rows), the
   28-subject two-direction family `probes/u4kind` is 26 agree + 2
   diagnosed possible-HOLE. What remains of the class, recorded at
   BUG-080 and Race.lean: shapes gc runs under `race.Disable` (a plain
   access beside a WRITE-LIKE op — `RUnlock`, RWMutex `Unlock`,
   WaitGroup `Add`/`Done` — or an overwrite beside a `Wait` at 0; NOT a
   copy beside `RLock`/`Lock`, which is two read-likes and no race) are
   go_mem-racy but TSan-invisible and the machine follows the oracle
   (register #13) — [AGENT], posed to the [USER] as Q-U4RESIDUAL
   (qrow-rulings row 9); and an overwrite that unlocks a held lock
   before another goroutine's Unlock ends `fatal` here where gc reports
   the race first (both abort: the machine's is an asserted program
   outcome, `GoError.fatal`; gc's is the race report then the same
   abort);
   (ii) schedule-dependent races on paths the enumeration never
   realizes — the enumerator is fuel/site/width-bounded and the strict
   lane runs one default stream plus three variants, so a race whose
   accesses co-execute only on an unexplored path passes with SC
   semantics on the explored ones; 63/364 corpus rows are UNCERTIFIED
   by the enumerator (20 deadlock members — for which gc under `-race`
   gives NO verdict either, every run timing out — 7 fatal members,
   24 frontier refusals, 11 budget (9 after the deep re-run: 61/364),
   1 truncated enumeration; none gc-red, but "uncertified" is the
   honest label, never DRF), and the probe leg
   showed the converse (two races the 10-run TSan sampler never
   realized, refused by the enumerator); (iii) U5 — the merge-vs-
   overwrite Release modelling difference (Race.lean U5) stands as
   RECORDED, NOT MEASURED: the probe meant to exhibit it is racy under
   go_mem (per-execution Unlock/Lock numbering — the machine refuses
   its racy paths on forced tapes) and the ruling Q-U5 the first
   report draft posed on it was WITHDRAWN at the pre-merge audit
   ([USER] ruling, "posed on a refuted premise; withdrawn at audit
   B1"; report §3.3 — the class's true exhibit needs a third lock-
   holding goroutine and cannot be made deterministic, which is why
   it is un-lane-able). U2 is CONFIRMED benign on the pin (7/7 probes agree
   both ways). WHAT THE PER-RUN WORDING PROMISES, exactly: every run
   on which a conflicting pair co-executes refuses; program-level
   refusal is certified where the enumerator certifies it (the racy
   lane's every-path claim on 23 rows; the confluent/membership lanes'
   full enumerations) and is otherwise only as good as the sampled
   streams plus the NPDRF conjecture. SCOPE ([USER] 2026-08-31): the
   upper-bound claims — C3 and every "believed MAXIMAL" — are scoped
   to **DRF programs**; the racy limited-outcomes envelope is
   declared OUT of product scope. The ground for that exclusion is
   **cost + no differential oracle** (gc `-race` halts; plain gc
   exhibits one point per run), NOT "undefined by Go" — the pinned
   memory model's own limited-outcomes stance (mem#restrictions:
   word-sized racy reads see actually-written values, no
   out-of-thin-air) contradicts the old "undefined" wording, which
   is retired here. go_mem's report-and-terminate license remains
   the refusal license, and the refusal boundary itself remains
   state-of-the-art-aligned (plmm: the OOTA frontier is unsolved
   everywhere; comparable stacks draw the same line).
5. **Registry-granularity scheduling points**: sound only where
   scheduling is unobservable between them for race-free programs.
   The fused-boundary incompleteness this entry recorded is CLOSED
   (W3.2 stages C+D: op completions and loop back-edges are points
   now — entry 1); the remaining named gaps are the B3 abort window
   (deferred at G1, trigger baseline recorded at inventory C3/U-1)
   and sub-statement granularity generally, which is the NPDRF/
   reduction line's territory — the mover theorem resumes over the
   WIDENED point set (slice 5).
6. **Sequential allocation addressing — quotient discharge PROVED ON
   THE PARKED REASONING BRANCH; this repo maintains the CONDITION.**
   (Re-located 2026-08-31 after the repo split — the entry's old
   present-tense "DISCHARGED BY QUOTIENT" read as a claim of this
   tree, which since 2026-08-31 makes NO verification claims.) The
   deterministic `nextAddr` allocator models less than Go promises
   (which is: nothing — addresses vary run to run, stacks move
   intra-run). The executable frame theorem's generalized renaming
   PROVED (2026-08-13) every conforming injective address relabeling
   observationally equal — `Frame.allocatorIndependence`, which lives
   ONLY at `proofs/GoLeanProofs/Frame/AllocIndep.lean` on branch
   `park/reasoning-2026-08-31`, with its design note
   `docs/2026-08-13_executable-frame-theorem.md` §5b on the same
   branch; nothing in THIS repo's tree or build contains or re-checks
   the theorem, and machine changes here can drift from the machine
   it was proved against until the reasoning repo exists and pins
   this one. What this repo maintains is the theorem's machine-side
   CONDITION: the modeled observation surface is POINTER EQUALITY
   ONLY — modeling `%p`, pointer ordering, `unsafe` int↔ptr, or any
   address-exposing channel re-opens the entry (the frontend refusals
   on `%p`/`unsafe`/uintptr observations are the standing guard).
   Inventory C11 carries the (q) classification with the same
   branch-located caveat.
7. **Unbounded memory / allocation never fails** (added 2026-08-14 from
   the verified-examples pre-merge audit, finding R1-F1). The machine's
   heap is unbounded and every allocation succeeds: `make`, composite
   literals and frame allocation have no failure mode, and runs start
   from an empty heap. Real Go is memory-bounded — an allocation can
   fail (OOM, or the runtime's own limits) at any size, and long before
   a length reaches `2^63`. Consequence, and the reason this is
   recorded rather than shrugged off: a theorem's domain condition
   states the MODEL's domain, which is wider than the practical Go
   domain, so `n < 2^63` in the gallery means "where Go's `int` domain
   ends in the model", never "where the program stops working"
   (`docs/verified-examples.md` said this at each entry — the gallery
   left with the split, branch `park/reasoning-2026-08-31`). Disposition:
   STANDING IDEALIZATION, not a gc-pin — it carries no re-envelope
   obligation, because the too-wide direction here does not threaten
   theorem transfer to real runs that DO allocate successfully. Cost of
   removal (only if resource-bounded claims are ever wanted): an
   allocation-failure outcome in the machine plus a memory budget in
   every statement — deliberately not paid.
   **MANDATORY RIDER ([USER] 2026-08-31, fidelity decision 5(a)):
   every consumer-facing claim over this semantics is scoped to
   ALLOCATION-SUCCEEDING runs.** The other direction is real and this
   rider is what carries it: a gc run that hits `maxAlloc` (runtime
   panic on an over-limit `make`) or OOM-aborts exhibits observed
   behavior no machine stream models — the bug definition's carve-out
   for it is exactly this named resource-exhaustion scope, never a
   silent absorption. Follow-ups on the books: the deterministic
   `maxAlloc` panic class is decision 5(b), Tier 5; the eventual
   honest model (memory bounded and very large, Cerberus-C-style, so
   arbitrary-context reasoning accounts for allocation failure while
   execution runs essentially never see it — the [USER]'s verbatim
   reasoning) is **discrepancy D-001** in
   `docs/discrepancy-backlog.md` (file lands with the
   fidelity-assessment branch; the id is stable).
   **5(b) DISCHARGED 2026-09-02 (t5-maxalloc, [AGENT] inside the
   [USER] mandate): behavior 2 — the deterministic `maxAlloc` panic
   class — is MODELED.** Latitude inventory R16 pins gc linux/amd64's
   realization (`maxAllocBytes` 2^48, `chanHeaderBytes` 112, the gc
   layout `tySizeAlignFuel`; the `makeSlice`/`makeChan`/`appendSlice`
   arms panic with gc's texts BEFORE materializing; BUG-081 filed
   with the probe matrix as witness, BUG-082 for the un-lowered map
   hint the probe exposed — open, frontend-side; corpus
   `builtins/make-maxalloc`, 14 rows PASS + 1 red-first).
   THE RIDER NOW SCOPES TRUE OOM ONLY (behavior 1): an allocation that
   passes the limit check and fails to allocate, and R16's recorded
   append band (gc panics on the grown cap where the machine's
   newLen-based check allocates). D-001's target state is unchanged by
   this; the rider stands until it lands.

## Why (the mission)

Traditional verifiers were built over PhD-years: high trust, low reach.
This project exists to learn whether semantics and verification tools
can be built in months — with AI labor, adversarial review, differential
grounding, and kernel-checked reasoning — at a trust level fit for
deployment anywhere, because the threat environment (much of it
AI-created) will not wait a decade. Cerberus took ten years. The
scientific question here is whether the essence of a language can be
captured trustworthily at speed. Every doctrine choice above serves that
question: the lower bound keeps us honest cheaply; the upper bound is
the product.
