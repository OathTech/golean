# Nondeterminism doctrine — modeling, testing, and its limits (2026-08-04)

REWRITTEN 2026-08-12 (essence-doctrine arc) beneath the ACCEPTED
essence-of-Go doctrine (`docs/2026-08-11_essence-of-go-doctrine.md` —
the two bounds, the bug definition, pins-as-scaffolding, the
simplifying-assumptions register) and its companion census
(`docs/2026-08-11_latitude-inventory.md`). What changed and why: the
2026-08-04 original treated envelopes as design choices needing
justification, with the deterministic (gc-matching) point as the
implicit neutral default the envelope had to argue its way out of. The
charter inverts that framing: **the machine IS the upper-bound
program** — the envelope is the DEFAULT state of every latitude point,
deterministic pins are velocity scaffolding carrying recorded
re-envelope obligations, and `observed ∉ modeled` is definitionally a
bug. The original's still-true content is preserved below and
re-grounded, not deleted; dated slice/audit history (F14, F16,
F2/BUG-021, F8/F15, the channels-arc captions) is kept where it remains
the record, and the pre-rewrite text is legible in git history (this
file at `ba6398ab` and earlier). Per-pin detail — plausible envelope,
re-envelope obligation, cost, priority — lives in the latitude
inventory and is LINKED here by entry id (C*, E*, R*), never
duplicated. This is doctrine: binding on every future
choice-consumption site and on every concurrency design.

## The frame: the two bounds (2026-08-12)

The machine is the candidate **upper bound**: the weakest machine Go
can plausibly ever do, exercising all degrees of freedom latent in the
language. Everything below is an instrument for one of the two bounds:

- **Differential testing is the LOWER bound.** Every oracle run —
  strict equality, membership samples, `-race` samples, litmus pins —
  contributes exactly one kind of fact: "real Go exhibited this member"
  (observed ∈ modeled). No amount of green can validate the model's
  WIDTH; the oracle can only witness members and expose too-narrowness.
- **The upper bound is argued from evidence, never observed.** Spec
  text, the memory model, runtime/library docs, the deployed-program
  corpus as de-facto spec, cross-implementation observation, proposal
  archaeology — the doctrine's evidence classes, each with an
  operational duty stated in binding requirement 4 below.
- **The bug definition:** if a conforming Go implementation does
  something the machine cannot, that is definitionally a bug somewhere
  — far more likely ours than Go's. `observed ∉ modeled` is always red,
  never latitude, never "a recorded divergence we're at peace with".
- **Envelopes are the default; pins are scaffolding.** A latitude point
  resolved to one deterministic point (a pin, or a singleton/subset
  narrowing) is a recorded DEBT with a re-envelope obligation and a
  cost estimate — the inventory enumerates every one — and no record
  may present gc-conformance at a latitude point as correctness or
  fidelity. Simplifying assumptions are permitted, in the register,
  never silently.

## The model

All Go implementation latitude the machine EXERCISES routes through ONE
mechanism: the `Choices` stream in `sem()`'s signature. (Latitude the
machine does not yet exercise — pins and narrowings — has no stream
site by definition; it is census'd in the inventory and carried in the
register, never left implicit.) The interpreter is total and
deterministic GIVEN a stream (executability — the differential trust
root — is the project's foundational requirement and the reason a
set-valued semantics was never an option). Consumption sites are named
and few — the CANONICAL LIST (kept current per this doctrine's
binding-site rule; brought current at the arc-final audit F16,
2026-08-08, after the channels arc left this preamble at its two
sequential sites):

- map iteration pick (`StepFn.lean`);
- append spill capacity (`Machine.lean`, `appendSpillWidth` envelope);
- L2 select-commit pick, entry path (`applySelect`, `Machine.lean`);
- L2 select-commit pick, arrival path (`arrivalPlan`, `Multi.lean`);
- L4 waiter pick (`stepThread`, `Multi.lean`);
- L1 scheduler pick (`stepMulti`, `Multi.lean`);
- L5 main-exit window (`execProgLoop`, `Multi.lean` — BUG-044, audit
  F2: exit-now vs one-more-runnable-goroutine-step at main's terminal).

This list and the executable consume sites agree exactly — verified by
the inventory's dual sweep (its §0 census table, with per-site bounds,
consume conditions, and empty-stream defaults; one alignment nuance for
stream authors at §9 flag 5: the map-iteration site alone consumes even
at width 1).

Each site carries its envelope statement in situ; enforcement is
structural (`applyStmtOpCore` is choices-free). The old parenthetical
"step SUCCESS is provably choice-independent" is scoped precisely
(F16's correction): the sequential kit (`stepFn_oblivious`) is GUARDED
(no mapIter/append/select shapes), and at POOL level the L1 pick
decides WHICH goroutine steps, so a stream can determine whether a
pool step succeeds — obliviousness holds per certified shape
(`poolThreadOblivious`/`stepThread_oblivious`), never unconditionally.

Headline theorems ∀-quantify the stream: true under EVERY resolution of
the MODELED latitude. The charter scopes the old boast here: "stronger
than any single Go implementation" is earned envelope-by-envelope,
never assumed — where the machine is pinned or structurally narrowed,
the stream quantifier ranges over FEWER behaviors than conforming Go
has, and the census counts the under-coverage honestly: 14 pins and 6
recorded narrowings, 4 of them KNOWN ≠ gc (inventory §10; C2/C3 are
the structural scheduling pair). A ∀-stream claim shape can even be
FALSE of programs gc always satisfies (send-then-spin:
`TerminatesNormallyC` false — fuel-out on every stream — where gc
exits 0, 60/60; register #1, recorded probe at
`docs/evidence/2026-08-12_scheduler-wedge-probes/`). A ∀-stream
theorem is exactly as strong as the envelope it quantifies.

## The lanes beneath the bounds (2026-08-12)

What each lane IS, in two-bounds terms (mechanics unchanged; the full
per-lane captions remain below):

- **strict = canonical-realization testing — a lower-bound
  instrument.** The default stream realizes one canonical member of
  each envelope (the empty-stream defaults in the census table);
  equality against `go run` witnesses that gc's realization and the
  canonical member agree on a choice-invariant observable. One
  membership datapoint per case — never evidence of envelope width,
  and never fidelity evidence at a pinned point (agreeing with gc at a
  pin is the pin working as built, not the pin being right to exist).
- **membership and confluent = the primary observed-∈-modeled check.**
  These lanes ARE the lower bound's mechanized form: every oracle
  sample must land inside the machine-enumerated set (membership), or
  the set is certified a singleton and the strict differential runs on
  it (confluent). A membership failure is the bug definition firing —
  always red, never latitude.
- **racy = the refusal boundary, unchanged by the rewrite.** Racy
  semantics is undefined by Go (the memory model's escape hatch is a
  refusal license); SC interleaving is claimed only inside DRF, and
  racy programs are refused fail-closed (register #4; the detector's
  own scope statement is register #13). This is a doctrine-decided
  boundary, not an envelope — the charter does not move it.

## Testing today: the strict lane + invariance guard

Corpus cases run under the default stream and must EQUAL `go run`'s
observation; then re-run under fixed adversarial streams — variance
fails the case (stage `nondet`). The strict lane therefore admits only
choice-INVARIANT observables, and the corpus is written to observe
order-independent quantities; that convention also neutralizes Go's own
per-run randomization. Genuinely choice-dependent observables
(`slices/full-slice-cap-zero`'s `cap()`) sit honestly red until the
membership lane exists (general-coverage arc, slice 3; since delivered
— the membership/confluent lanes below).

## The epistemic limits, re-derived from the bounds

Differential equality is VERIFICATION only where Go FORCES one
behavior — there the modeled set is a singleton, so a membership fact
IS an agreement fact. At every latitude point, pinned or enveloped, it
is membership sampling; at a PINNED point in particular it verifies
the pin's realization, never Go-the-language. It degrades to
SANITY-CHECKING at the nondeterministic frontier — in two-bounds
terms, it is the lower bound entire, and nothing else. The failure
directions are asymmetric:

- **Too NARROW** (real Go exhibits a behavior outside our envelope) is
  the bug definition itself: `observed ∉ modeled`, definitionally red.
  It is also the SOUNDNESS-relevant direction — ∀-stream theorems
  transfer to real Go only if Go's behaviors ⊆ modeled behaviors — and
  it is DETECTABLE: the membership lane's job (Go's observation ∈ our
  admitted set), plus equality-lane mismatches. Sampling density varies
  by feature: map order re-randomizes per run (every go-run explores —
  dense, and fuzz-generated order-SENSITIVE contexts make it a real
  exploration); append growth is deterministic per Go version (one
  point per toolchain — membership is version-tracked); SCHEDULING
  sampling is nearly useless (the runtime explores a tiny biased corner
  — see the concurrency inputs below). Where sampling is weak, the pins
  and narrowings in that region are the ones most likely to be hiding
  an observed-∉-modeled instance. (Attribution corrected at the
  2026-08-12 audit: the send-then-spin wedge (inventory C2+C3) sat
  unnoticed NOT because sampling was weak — gc's exit-0 on that shape
  is a deterministic point, and a corpus case would fail loudly today,
  red on the default stream itself — but because no such case existed:
  the guardrails-first rule's gap, an unexercised path. The remedy is
  the missing case, not sampling density.)
- **Too WIDE** (we admit behaviors no conforming Go could exhibit) is
  UNDETECTABLE by any oracle — go run cannot demonstrate a behavior it
  never has — and it is the transfer-safe direction: ∀-stream theorems
  become harder to prove, never wrong. But under the charter it is not
  unpoliced latitude: an envelope's width is a claimed UPPER-BOUND
  ARGUMENT, made from the evidence classes (requirement 4) and checked
  by review (requirement 2) — "the weakest machine Go can PLAUSIBLY
  ever do" is argued from evidence, never asserted from spec silence
  alone, and never inflated past plausibility for rhetorical width
  (R2's declared pragmatic subset is the honest form of stopping
  short, with its containment argument and version-tracking pins).

## Binding requirements

1. **Envelope statements are upper-bound arguments.** Every
   choice-consumption site ships with a spec-anchored envelope
   statement in its design note or docstring: what the Go spec text
   says, exactly which set our stream resolves, and the argument that
   the set contains every behavior conforming Go can exhibit (the
   soundness direction). Under the charter this statement is the
   site-local instance of the upper-bound argument — it must name its
   evidence class(es) per requirement 4. Current sites' statements:
   map iteration — spec says unspecified order, envelope = all
   permutations of the snapshot, which is ⊇ any Go ONLY for programs
   that do not mutate the map during iteration: the spec MANDATES that
   an entry removed before being reached "will not be produced", and
   the snapshot model still produces it (and stale values) — BUG-005,
   triple-pinned red, under the charter a DEFINITIONAL bug (a violation
   of a FORCED point, worse than latitude — inventory E9, register #11,
   re-envelope priority 2), deliberately deferred to its live-iteration
   fix; until then the map envelope statement is scoped to
   mutation-free iteration (arc-final audit F14, 2026-08-06), and the
   snapshot's resolution of the created-entries MAY-latitude to "never
   produced" is a recorded singleton narrowing owed its site-level
   statement when the BUG-005 surgery lands (inventory §9 flag 4);
   append spill — spec allows any sufficient capacity ("a new,
   sufficiently large underlying array"), envelope = [newLen, max(32,
   2·growth formula)] (WIDENED deliberately at the arc-final audit,
   F2/BUG-021 2026-08-06: go1.26.5 — the oracle toolchain itself —
   realizes capacities outside the old growth+[0,8) window in both
   directions, because gc's realized capacity is element-size dependent
   — size-class rounding and the compiler's 32-byte stack buffer —
   while the formula is not. The containment argument for the widened
   bound lives on `appendSpillUpper`, GoCore/Ops.lean; the empty stream
   still resolves to the growth-formula point, so strict-lane behavior
   is unchanged). Still a PRAGMATIC SUBSET of the spec's latitude
   (inventory R2 — deliberately not maximal, and recorded as such),
   sound for transfer as long as real Go's policy lands inside.
   Version-tracking is per-point, not per-envelope — a samples=1
   membership case tracks its one (elem, oldCap, newLen) triple — so
   the escaping REGIMES carry their own pins
   (slices/append-spill-{stack-buffer,below-formula,size-class})
   alongside the formula point (full-slice-cap-zero).
   SINGLETON NARROWINGS (first recorded at the arc-final audit, F8/F15
   2026-08-06): a spec-declared or spec-SILENT latitude that the model
   resolves to a single point WITHOUT a Choices site is still an
   envelope decision and ships the same statement + transfer caveat at
   its site — and under the charter every one is a PIN in the register's
   sense: a recorded debt with a re-envelope obligation, never a
   fidelity achievement. Current recorded singletons: `[]byte(s)`
   capacity pinned to len (Machine.lean `bytesFromString` arm — gc's
   escaping path realizes roundupsize(len), OUTSIDE the singleton: an
   observed-∉-modeled candidate, register #10, queued at inventory
   priority 4); map-key retention on overwrite at gc's `needkeyupdate`
   point (inventory E10, spec-silent — matches gc where pinned and
   version-tracks gc's choice; a conforming original-key-retaining
   implementation is outside, transfer caveat at the site). For every
   OTHER pin and narrowing — including the structural scheduling pins —
   the inventory entry is the record; this doctrine does not duplicate
   it.
2. **Envelope fidelity is a standing audit dimension** (like
   over-specialization): reviewers argue each envelope against the
   evidence its statement claims — spec TEXT first — because the
   too-wide direction has no oracle. Under the charter the reviewed
   object is the upper-bound ARGUMENT itself: which evidence class it
   invokes, whether the citation actually supports the claimed set, and
   whether any narrowing has quietly been justified by gc observation
   alone (the inversion the charter forbids — requirement 4's last
   bullet).
3. **Possibilistic scope, declared.** Our claims quantify all
   resolutions; we never make probabilistic claims. Spec language like
   `select`'s "uniform pseudo-random" enters the model only as "any"
   (inventory C6 — the envelope's SUPPORT equals the spec's);
   statements must never imply distributional facts.
4. **Evidence-class duties (2026-08-12).** The doctrine's evidence
   classes for the upper bound, each with its operational meaning at an
   envelope statement or re-envelope argument:
   - **Spec text (SPEC):** quote the governing sentence verbatim at the
     site, with its section name. The argument must show every admitted
     member conforms to the quoted text, and — for a maximality claim —
     why no conforming behavior lies outside. Spec SILENCE is an
     argument only together with the surrounding forced points that
     bound it (C1's form: zero scheduling text, bounded by blocking
     rules and the memory model).
   - **Memory model (MM):** same duty, quoting go_mem; owns every
     happens-before/DRF-SC argument and the racy-refusal license (the
     "An implementation may always react to a data race by reporting
     the race and terminating the program" escape hatch — mem#overview
     verbatim; quote corrected at the spec-p2 delta-review, which
     caught the pre-fix wording surviving here after the inventory's
     copy was fixed).
   - **Runtime/library docs (DOCS):** the doc sentence quoted at the
     arm (the sync arms' existing practice — `pendingW` reader
     exclusion, Wait-at-zero). Where docs underdetermine behavior, say
     so; the residual latitude is a register matter (register #7).
   - **De-facto spec (the deployed-program corpus):** must SHOW a
     real-program expectation, never assert a vibe. A qualifying
     argument names the deployed pattern — real code, ideally a named
     idiom or widely-used package — whose behavior the argument claims
     an implementation cannot plausibly break, argues the constraint
     via the Go 1 compatibility promise, AND checks that the Go team
     has not deliberately destroyed the expectation (map-iteration
     randomization is the standing counterexample: a de-facto pin the
     team actively prevented from being honored). "Nobody would ever
     depend on X" without named code is not evidence.
   - **Cross-implementation observation (XIMPL):** no such lane exists
     yet — the evidence base is one implementation at a pinned version,
     and sharper, one PLATFORM: gc linux/amd64 at default GOAMD64
     (register #3, sharpened by register #9). When the lane exists it
     will look like: gccgo/tinygo/arm64/32-bit oracle legs run beside
     gc, each witnessed behavior a new lower-bound member — turning
     one-point pins into multi-point membership rows (R1's int width
     and R9's panic texts are where it bears first). Note the class
     honestly: XIMPL is still a lower-bound instrument — more
     implementations witness more members; none proves width.
   - **Proposal/issue archaeology (ARCH):** committee-intent
     reconstruction, Cerberus-style — supporting evidence for
     plausibility judgments (would any conforming implementation ever
     do X?), never itself a bound. None done yet; the inventory marks
     where it would bear (R5, R11).
   - **Measured gc behavior (GC):** a lower-bound instrument that may
     MOTIVATE a narrowing argument (a probe exhibiting gc's realized
     point tells you where the canonical realization should sit) but
     never conclude one — concluding "Go can't" from "gc didn't" is
     exactly the inversion this rewrite exists to forbid.

## Scheduling granularity and the reduction line (2026-08-12, the charter position)

The registry-granularity scheduling model rests on two structural pins:
forced continuation (run-to-boundary — between registry boundaries the
running goroutine steps privately on every stream; inventory C2) and
the fused effect boundary (no post-op scheduling point except
`.spawned`; inventory C3). Pre-charter text treated these as the
model's granularity DESIGN, with the NPDRF reduction as the bridge that
would justify claiming more. Under the charter the reading inverts:

- **The narrowing is a definitional bug, queued for re-envelope.** It
  is oracle-visible TODAY, and the recorded exhibit is SEND-THEN-SPIN
  (`docs/evidence/2026-08-12_scheduler-wedge-probes/`): a worker
  performs one registry op (a cap-1 send that wakes main) and then
  spins with no further registry op; the fused effect boundary (C3)
  offers no post-op scheduling point, forced continuation (C2) runs
  the registry-free tail privately forever, and the woken, runnable
  main is never scheduled again — exit-0 unreachable on EVERY stream
  (511/511 fuel-out in the exhaustive mod-2 depth-8 sweep, default
  stream included) where gc exits 0, 60/60. `observed ∉ modeled` —
  register #1's entry — and it poisons ∀-stream claim shapes
  (`TerminatesNormallyC` is FALSE for a program gc always terminates).
  Exhibit corrected at the 2026-08-12 audit — the REGISTRY-FREE
  spinner (no registry op anywhere) that earlier drafts named here is
  NOT this bug: gc's exit-0 there IS in the modeled set (the default
  stream produces it), the machine's extra never-yielding streams are
  the too-WIDE, transfer-safe direction above (and possibly not
  over-wide at all — the spec has zero scheduling text (C1), so a
  cooperative non-preempting implementation could conformingly hang
  there), and ∀-stream termination claims on that shape are the
  FAIRNESS quantifier's territory. The scopes split cleanly: the C2+C3
  re-envelope fixes the WEDGE (a woken runnable partner must be
  schedulable); it cannot and need not remove the registry-free
  spinner's divergent branches — adding preemption points only ADDS
  streams, and the never-yielding stream survives any boundary-set
  widening. C2+C3 land together as "the fused-boundary/
  forced-continuation" item — priority 1 in the inventory's re-envelope
  queue (§7), the largest single re-envelope and the highest-value one.
  BUG-040 and BUG-044 were pointwise instances of the same class, fixed
  pointwise; C3 records the remaining mid-program abort gap (unprobed —
  U-1).
- **The reduction line resumes AFTER the machine widens, as the
  upper-bound theorem it should always have been.** Once preemption
  points exist inside segments, NPDRF's job is the scheduling upper
  bound: the argument that the widened boundary set loses no
  DRF-observable behavior against full interleaving — i.e. that the
  modeled schedule envelope's width suffices for race-free programs.
  Proving a reduction onto the CURRENT narrowed boundary set first
  would certify the bug's width, in the wrong order.
- **The parked channel-logic arc's records are the authority for the
  reduction line's exact state** — its charter
  (`docs/2026-08-10_channel-logic-arc-charter.md`, slice 4: the
  statement was already marked REFUTABLE-AS-WRITTEN there) and the
  parked `channel-logic-s4` branch's records, whose strongest form is
  the branch's binding design note `docs/2026-08-11_npdrf-reduction.md`
  and the "NPDRF status — SETTLED captions" section it adds to THIS
  file — both BRANCH-ONLY today (they exist on `channel-logic-s4`, not
  on main; the branch is the record, so do not prune it without
  landing or archiving them) — which drove the statement through
  refutation and repair before the arc parked. This doctrine cites
  that record rather than restating a snapshot of it; the phrase "the
  NPDRF obligation" in the lane captions below remains correct as a
  scope marker and resolves there.

Every caption below that scopes a claim to "the registry-point path
set" or "registry granularity" is stating this section's pins as
limits — that is the honest form, unchanged; what the charter changes
is that the pins themselves are a debt with a queue position, not a
neutral design fact.

## Inputs to the concurrency arc's design note (2026-08-04; historical — all four since taken up)

Binding starting points as recorded at drafting; kept as the record of
what the concurrency design was required to honor:

- **DRF-SC discipline**: data races FAIL CLOSED (an error, not an
  interleaving) — Go's memory model gives racy programs essentially
  undefined behavior, and modeling races as well-defined
  nondeterministic interleavings would be wrong in KIND. Sequentially-
  consistent interleaving is claimed only for race-free programs (the
  DRF-SC theorem's territory; Goose/Perennial take the same line). Now
  register #4; executable as the racy lane below.
- **`go run -race` as a second oracle**: programs the race detector
  flags must fail closed in our model — a testable boundary exactly
  where interleaving sampling cannot help. Delivered (the racy lane).
- **Litmus corpus**: memory-model litmus shapes (message passing, store
  buffering, …) as corpus cases probing the envelope's edges. Delivered
  (lane e below).
- **Fairness quantifier decision**: ∀-stream termination is FALSE for
  correct programs that spin-wait on another goroutine (unfair
  schedules starve the writer). Concurrency termination claims need an
  explicit fairness-constrained quantifier, decided in the design note
  — not discovered as an unprovable theorem. Taken up in
  `docs/2026-08-07_fairness-precision-note.md`. Scope note (corrected
  at the 2026-08-12 audit; the old bridge sentence fused two defects):
  the note's enumerated spinner idioms are registry-BEARING — they
  cross a boundary every iteration — so their infinite trees are
  honest latitude under unfair schedules, the FairStream quantifier's
  territory, untouched by the C2/C3 re-envelope (widening only ADDS
  streams). C2/C3's definitional bug is the different,
  boundary-free-TAIL shape (the send-then-spin wedge, register #1).
  The two interact in exactly one direction: fairness over a
  boundary-free segment is vacuous — no quantifier over choice points
  can rescue a goroutine that never reaches one — so the C2/C3
  boundary-set widening precedes the fairness machinery, and each
  fixes only its own shape.

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
  is proof). The claim is scoped to the REGISTRY-POINT path set (the
  scheduling-granularity pins above; the NPDRF obligation's territory)
  and by the footprint inventory's recorded under-approximations
  (U1–U2; U3 closed by BUG-045); the pre-slice-4 per-stream
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
  structural-alignment decision, design note D2+D3; register #13's
  scope statement): gc's channel race instrumentation (slot
  release-acquire, rendezvous racesync, close release/acquire) — not
  the memory model's minimal rule set — so our refusals stay
  justifiable by the oracle. Divergences between the detector's HB and
  go_mem's relation (Fava SEFM 2020's caution) are therefore shared
  with `-race` rather than invented by us; each is quoted at its
  implementation site in `Race.lean`. Two recorded DEVIATIONS from gc's
  realized set (S3 audit corrections; (i) RESOLVED at the arc-final
  audit F1/BUG-045, 2026-08-08): (i) the close-woken SENDER gets no
  edge from us although gc's `closechan` DOES `raceacquireg` parked
  senders — our edge set is strictly STRONGER there. The old text
  claimed "refusal-set agreement holds anyway because gc flags every
  close-beside-parked-send via its channel-OBJECT instrumentation,
  which we do not model" — FALSE in the fail-open direction (three
  shipped confluent-green subjects were TSan-red through exactly that
  unmodeled pair; the audit's F1). The chan-object pair IS now modeled
  (`RaceState.chanObjAccess`: send = entry read (plain sends AND, per
  BUG-046, one read per polled select-SEND clause — selectgo pass 1's
  racereadpc), successful close = write, recv and select-recv clauses =
  nothing — gc's instrumentation exactly), so every close beside a
  parked plain sender refuses at the close and the missing wake edge is
  moot on refused programs; the reclassified racy pins
  (goroutines/close-wake/sender-*, select-closed-arrival/
  recv-parked-sender) are the executable check;
  (ii) `len(m)` on a MAP is instrumented by gc (probed red on
  go1.26.5, refuting the first version of this caption) and is now
  recorded by the footprint; `len`/`cap` on channels remain
  uninstrumented on both sides (probe p26). The footprint's remaining
  under-approximations are U1–U2 in Race.lean's inventory (U3 closed
  by BUG-045, 2026-08-08) — the lane's per-stream refusal claim is
  scoped by them. (One stale in-file docstring predating the BUG-045
  correction is flagged at inventory §9 flag 1, owed at the next
  Race.lean-touching slice.)
- **Scope limit (BUG-040) — FIXED at slice 4**: the detector is
  complete only over accesses that EXECUTE on the modeled
  (registry-point) paths; the post-spawn reschedule point (`.spawned`,
  a registry op at fork completion) now puts the child-first
  interleavings INSIDE that path set, so the exit-no-sync race class
  is detectable (eval-pinned: value leaf on main-first, race leaf on
  child-first — a mixed-leaf class no corpus race case can express,
  and the pool enumerator pins BOTH leaves). The registry-point-vs-
  full-interleaving gap itself is the scheduling-granularity section's
  territory (C2/C3 + the NPDRF obligation).

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
record. In two-bounds terms every caption below is a lower-bound
caption — what was witnessed or enumerated — plus an honest statement
of the width it cannot speak to.

- **strict — sequential-degenerate (D9(a))**: PASS = observation
  equality against one `go run` plus three-adversarial-stream
  invariance. Means: the observable is choice-invariant, the CANONICAL
  REALIZATION (default stream) agrees with gc's realization on it, and
  the concurrency machinery is CONSERVATIVE on it (the conservation
  theorem `execProg_single_eq_execStmt` is the transfer lemma;
  full-corpus bit-identity its empirical twin). A lower-bound
  instrument: one membership datapoint at the canonical point. Cannot
  show: anything about envelope width; anything about interleaving —
  a strict green is structurally blind to schedule effects (the S2
  waiter-priority majors were invisible to every green strict case;
  only membership probes saw them) — and nothing about streams beyond
  the three pinned adversarial ones; and at a PINNED latitude point,
  nothing beyond "the pin reproduces gc here" (never that the pin is
  right to exist — the inventory entry carries that debt).
- **confluent (D9(b))**: PASS = enumerator-certified |set| = 1 over
  ALL registry-point schedules, then the full-strength strict
  differential on the singleton. Means: schedule-independence is a
  CERTIFIED claim for this program, and the one admitted observation
  is Go's — the observed-∈-modeled check in its degenerate-singleton
  form. Cannot show: anything past the fail-loud caps (over-cap cases
  stay strict, recorded in their cases.tsv); anything about programs
  outside the certified one; anything at sub-registry granularity
  (the scheduling-granularity pins C2/C3; the NPDRF obligation's
  territory).
- **membership — schedule-dependent (D9(c))**: PASS = every Go sample
  (R plain + R under `-race`, the dual-sampling rule above) ∈ the
  machine-enumerated observation set, with mechanically-computed
  per-site bounds, fail-loud caps, and the optional `members=`
  cardinality pin. THE PRIMARY LOWER-BOUND CHECK: Go's exhibited
  corner lies inside our envelope, and the envelope was exhaustively
  enumerated at registry granularity; a failure here is the bug
  definition firing. Cannot show: that UNEXHIBITED members are
  Go-realizable — width is upper-bound territory, argued from the
  evidence classes (requirement 4) and reviewed (requirement 2), never
  tested; the width-signal metadata (|enumerated| vs |exhibited|,
  recorded per run) is the honest gap measure — and nothing about racy
  programs (refused before this lane applies).
- **racy (D9(d))**: the full caption is the dedicated section above —
  every enumerated path refuses AND one `-race` red sample witnesses
  the real race; the three-way investigation rule; scope = the
  registry-point path set and the footprint inventory's U1–U2 (U3
  closed by BUG-045).
- **litmus pairs (D9(e))**: not a harness lane — a corpus DISCIPLINE
  over the memory-model shapes (MP, SB, …), each in two forms: the
  channel-synchronized form rides lane b/c and must admit exactly the
  SC-reachable outcomes (sb-chan {1,10,11} with members=3 — 00
  mechanically excluded), the racy form rides lane d and must refuse.
  A PASS of the pair means: the envelope's EDGES sit where the memory
  model says (SC inside DRF, refusal outside) — the MM evidence class
  made executable at the boundary. Cannot show: weak-memory behaviors
  — we refuse the programs that could exhibit them, deliberately; a
  real implementation's weak behavior on a racy program is outside
  every claim we make, and transfer caveats must say so.
- **deadlock / leak (D9(f))**: global deadlock is strict-lane
  differential (`expected_status: deadlock` against gc's fixed
  "all goroutines are asleep" fatal, exit 2; NEVER combined with
  `-race`, which suppresses the detector). PASS means the blocking
  semantics — what deadlock is made of — agrees with Go where Go can
  express an opinion (the detector-terminal itself is a recorded pin,
  inventory C9 — observationally coincident with the spec's "blocks
  forever" on a terminating-run corpus, and a likely permanent-record
  pin). Partial LEAK is observably NOTHING on the Go side (exit 0):
  main-exit cases validate the sequential observable differentially,
  while the leaked-goroutine classification itself is model-internal
  SELF-consistency plus review, never differential evidence. Cannot
  show: liveness (deadlock-freedom of nonterminating-by-design
  programs is outside a terminating-run corpus entirely — the proof
  side's territory).

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
