# The W3.2 re-envelope arc — from gc-pins to honest envelopes (2026-08-20)

Status: **DRAFT for user review** — nothing here is chartered until the
user rules on the open questions (§OQ) and the slice cut. This is the
raft master plan's W3.2 (`docs/2026-08-15_raft-master-plan.md` §W3
item 2: "the single most contended item — it also unblocks
channel-logic ... the strictest audit bar in this plan"), written as a
charter in the wp-arc form (`docs/2026-08-16_wp-arc-charter.md`):
slices, per-slice DONE, hard boundaries, named user gates.

## Framing — what this arc is

The re-envelope arc converts deterministic gc-pins of latitude into
honest envelopes. This is the essence-of-Go doctrine's STANDING
obligation (`docs/2026-08-11_essence-of-go-doctrine.md`: "each pin
carries a re-envelope obligation: it is a recorded debt, not a fidelity
achievement"), and the latitude inventory
(`docs/2026-08-11_latitude-inventory.md` §7) is its queue of record —
this charter consumes that queue, it does not re-derive it.

**Success metric, twofold:**

1. **The channel-logic resume condition is satisfied.** The parked
   channel-logic arc (`docs/2026-08-10_channel-logic-arc-charter.md`,
   tail: "ARC PARKED") names two blockers: (1) the essence-of-Go
   doctrine arc — DONE, accepted 2026-08-12 — and (2) "the machine
   re-envelope phase it scopes (the latitude inventory decides the
   scope; the fused-boundary de-fuse is the known first item)". This
   arc IS blocker #2. Its exit artifact §S6c states, checkably, what
   the resume gets.
2. **The ratified (c) rows' membership greens are attainable.** The
   triage ratification (`docs/2026-08-19_triage-table.md` §7,
   2026-08-20, on the bugfix-arc branch) rules that those rows'
   CORRECT green is membership — "today's red does not say 'we are
   wrong here'. It says inclusion is not yet checkable" — and routes
   their re-envelope obligations here. This arc builds the instruments
   that make inclusion checkable for the latitude rows (C1, C5, and
   the obligations they name: E7, R6), and poses the observable
   question for the rendering rows (§S3).

**Inputs of record** (read before any slice): the doctrine + latitude
inventory (above), `docs/2026-08-04_nondeterminism-doctrine.md` (the
binding requirements — every envelope statement is a spec-anchored
upper-bound argument; requirement 2: the too-wide direction has no
oracle, review is the only check), `docs/spec-divergence-ledger.md`
(L-011 init-order, L-012/L-013 adopted readings),
`docs/language-coverage-ledger.md` §6 (the design questions, with
cases in hand) and the triage table §§4/7 — the last three at their
**bugfix-arc branch** state, which lands on `main` ahead of this arc
(this charter cites the branch state deliberately; if the landing
reshapes a cited row, the charter is re-checked at kickoff, not
silently trusted).

**Sequencing constraints, external:** (a) the bugfix-arc lane lands
first (it owns the ledger/triage/E9 state cited here); (b) per the WP
arc charter's discharged checkpoint (finding 3b): WP slices 1–2's
gallery retrofits COMPLETE before this arc's re-proof wave starts —
same files; (c) the WP mirror evaluator quits at choice sites, so its
exposure to the `Choices` reshape is through the mirror alone, where
the default-build drift theorem makes it visible — the mirror update
is a known, budgeted cost of this wave (WP charter finding 3c); (d)
this arc takes semantic-core + `Corpus/` + `baselines/` ownership —
one lane, serialized, per the worktree discipline.

## Hard constraints, inherited (restated once, binding on every slice)

- **Fairness non-preclusion (2026-08-14 requirement, master plan §W3
  item 2):** the `Choices` reshape keeps scheduling picks
  identifiable and the schedulable set recoverable — a future
  `Fair : Choices → Prop` must be definable; no flattening.
- **Envelope statements are upper-bound arguments from SPEC TEXT**
  (nondeterminism doctrine requirements 1/4): the governing sentence
  verbatim at the site, evidence class named, the argument that every
  admitted member conforms. The too-wide direction has no oracle —
  review is the check; too-narrow is the membership lane's job.
- **Per-slice, always:** membership-lane wiring for every widened
  point (the widened set is enumerable, sampled dual-mode, certified
  where tractable), and an explicit **proof re-alignment budget** —
  which theorems/witnesses/certificates the boundary or envelope
  change breaks, and the repair cost, stated BEFORE the surgery
  (BUG-040's precedent: designated witnesses re-derived, Comparator
  landmark).
- **User gates on observable-set changes:** every envelope-widening
  that changes the machine's observable set is a named user gate —
  fidelity is the user's lever, never the arc's. See §Boundaries.
- Merge protocol, audit ask, gate discipline: unchanged and absolute.

## Slice 0 (kickoff) — THE SEMANTICS DESIGN AUDIT

User-directed (2026-08-19/20): the semantics should be *"nice as well
as faithful ... an operational semantics to be proud of ... a trust
surface humans will eventually want to read."* Before the largest
machine surgery in the queue, audit the interpreter AS A DESIGNED
OBJECT — a PL-theorist persona over `stepFn`/`execStmt`/`Multi`, not a
bug hunt (the differential owns bugs). Dimensions:

- **Rule uniformity** — do like constructs step alike; are the arms a
  reader can predict from the construct's kind.
- **Construct orthogonality** — does each feature's semantics live in
  one place, or is it smeared across arms (the E6 hoist-refusal class
  is the smell's known instance).
- **Choice-site / envelope legibility FROM the rules** — can a reader
  find every latitude point by reading the rules, without the
  inventory in hand (the census table's per-site
  bound/consume/default triple should be visible in situ).
- **Continuation-algebra principledness** — is the `Cont` spine an
  algebra with stated invariants or an accretion (delete-prune's
  `contAfterStmtOp` rewriting frames is the kind of operation whose
  legality should follow from a stated invariant).
- **Naming**, **dead generality** (parameters/arms nothing exercises),
  and **granularity as a design property** — step decomposition
  stated per construct, not discovered per bug (BUG-002's class).

Output: **a refactor queue graded by proof blast radius** (none /
witness-level / metatheory-level), consumed DURING the slice-1
surgery — **one reshape, not two**. A finding whose fix rides the
boundary-set change costs its grade once; a finding deferred past this
arc is recorded with the reason. DONE: the audit note exists with
file:line-grounded findings; the queue is graded; the user has
reviewed the queue and marked what rides slice 1 (user gate G0).

## Slice 1 — the scheduling wedge de-fuse (C2+C3; the definitional bug)

Register entry 1; inventory §7 priority 1; the channel-logic park
record names it first. The SEND-THEN-SPIN wedge: a worker performs one
registry op (a cap-1 send that wakes main) and then spins with no
further registry op — the fused effect boundary (C3) offers no post-op
scheduling point, forced continuation (C2) runs the registry-free tail
privately forever, and exit-0 is unreachable on EVERY stream (511/511
fuel-out, exhaustive mod-2 depth-8 sweep) where gc exits 0 (60/60;
recorded probe `docs/evidence/2026-08-12_scheduler-wedge-probes/`).
`observed ∉ modeled` — definitionally a bug, and it poisons ∀-stream
claim shapes (`TerminatesNormallyC` false for a program gc always
terminates).

Work: widen the boundary set — post-op scheduling points at
(wake-producing, or all) registry-op completions (C3's obligation) and
preemption points inside boundary-free segments (C2's; loop back-edges
are the recorded candidate) — with the `Choices` reshape honoring
fairness non-preclusion. Scope honesty from the corrected exhibit: the
fix makes a woken runnable partner schedulable; it does NOT remove the
registry-free spinner's divergent branches (widening only ADDS
streams; ∀-stream termination there is FairStream's quantifier
question, not this slice's). C3's mid-program abort gap (U-1) gets its
directed gc probe in this slice — wake partner, then panic in the
issuer's private segment — cheap, and it pins the widened envelope's
edge.

Known cost surface (budgeted per the inventory C2/C3 entries): every
pinned stream shifts; designated witnesses re-derived; enumeration
trees branch at every new point (enumerator caps/DPOR pressure); fuel
accounting and `MultiSound`/`MultiStreams` re-proved; NPDRF restated
over the new point set; race-detector segments shrink. This is the
re-proof wave the master plan budgets and the WP-arc sequencing
protects.

**User gate G1: the boundary-set design note ships and is reviewed
before the surgery starts** (which completions get points; back-edge
preemption in or out; the enumerator's bound story) — this is the
observable-set change gate in its largest instance.

DONE: the wedge probe shape reaches exit-0 on an enumerable stream
(membership row green, wedge case no longer fuel-out-on-every-stream);
the registry-free spinner's behavior is unchanged and its
fairness-territory status recorded; U-1 probed and pinned; envelope
statements at every new/changed site; baseline re-pinned with the
explained coverage change; gate green (`scripts/ci --slow` — the
enumerator and interpreter are touched by definition).

## Slice 2 — the Q-row design questions

The coverage ledger §6 (bugfix-arc branch) routes its
concurrency-entangled design questions here — eight of the ten rows
(Q-ATOMICITY and Q-GOEXIT are F4-arc-owned; they appear in this arc
only as interfaces the widened boundary set must not foreclose). Each
is a QUESTION with cases in hand, never a silent queue slot; the
deliverable per row is a short memo → user ruling → implementation or
recorded deferral. The rows, with their in-hand reds:

1. **Q-SELSEL** (2: `channels/select-select/{core,beside-loop}`) —
   select↔select rendezvous: which side's offer commits; the L2/L4
   pairing envelope for symmetric pairing without a global arbiter.
2. **Q-ATOMIC** (5: `sync/atomic-frontier/*`) — what realizes
   mem#atomic's SC (U-6): if atomic ops are single fused steps, SC
   falls out of L1; the real decisions are step granularity + detector
   footprint. Directly coupled to slice 1's boundary set.
3. **Q-SYNCVAL** (5: `sync/iface-dispatch/*`, `sync/escapes/*`) — sync
   ops as first-class values: does scheduler-step identity survive
   indirection (a dispatched `Lock()` consumes the same C8 site), or
   refuse.
4. **Q-SYNCLIT** (2: `sync/composite-literal/*`) — copying/constructing
   live sync primitives (ledger marks it "W3.2 or a named ruling" —
   OQ5 asks which).
5. **Q-COND** (3: `sync/out-of-scope-cond/*`) — sync.Cond's wakeup
   envelope: Signal's waiter choice, Broadcast order, spurious wakeups.
6. **Q-TRYLOCK** (1) — TryLock spin-wait termination is
   fairness-dependent; note mem#locks' explicit spurious-failure
   envelope member (inventory C8) — the FairStream class question.
7. **Q-INITSPAWN** (1) — `go` during `$pkginit`: the spawned child's
   envelope relative to remaining init work and main's start.
8. **Q-RACEPATH** (1, BUG-041) — race-footprint granularity for
   value-path composite reads; today fail-closed over-refusal.

DONE: every row has its memo with a user ruling recorded (implement /
defer-with-reason / re-route), and every implemented ruling carries
its envelope statement + membership wiring + re-alignment budget.
Deferring a row with an honest ruling is success; leaving one silent
is not.

## Slice 3 — membership greens for the ratified (c) rows

The ratification's routing made checkable. Two sub-slices of different
character:

**(a) The init-order envelope** — C1 (`init/hidden-dep-order`, E7) and
C2/BUG-061 (staticinit pruning, L-011). The envelope is argued from
the spec's OWN dependency rules: all conforming initialization orders
= the linear extensions of the lexical-reference partial order, with
hidden-dep-affected variables freed (E7's recorded envelope), and —
per L-011's adopted stance — the pruning boundary read as constraining
only packages with observable initialization (gc's pruning conforming,
a no-pruning implementation conforming, and our current "third point"
a member but not a principled choice). Work: a named `Choices` site
over conforming orders (`$pkginit` becomes schedule-bearing;
strict-lane init cases stay on the deterministic default point), the
membership rows that turn C1's and C2's reds green as inclusion
checks, and L-011's owed latitude-inventory entry. The cheap interim
from E7's entry (a fail-closed frontend detector for the hidden-dep
shape) ships FIRST, so the unguarded silent-divergence class is
visible even if the full envelope slips. North-star note: etcd-io/raft
has package-level vars — the raft lane consumes this slice.

**(b) The rendering rows' observable restatement** — C3 (BUG-059
panic-qualifier) and C4's remaining three (BUG-004 abort rendering).
The ratification names C3 (with C6/C8) among the rows "expected to
stay red under any instrument", and C4's remainder stays pinned —
no envelope machinery converts an unmodelable message channel.
The candidate move this charter poses (OQ3, a user decision, not a
plan): restate the OBSERVABLE for these rows — judge the semantic
outcome (panic occurred, payload class, abort exit) as a membership
check while the gc-exact rendering stays an explicitly out-of-scope
channel — so green means "the semantics is inside the envelope" and
the rendering pin's non-transfer caveat is carried by the row, not by
a permanent red. If the user rules the restatement dishonest (a red
that keeps the boundary visible may be worth more than a scoped
green), the rows stay red and this sub-slice is a no-op with a
recorded ruling. **No conversion happens without the ruling.**

**(c) C5/R6, float→int out of range** — the other row the
ratification says this arc "could genuinely re-color": a value
envelope over the known conforming points ({amd64 wrap point,
saturation, ...}) would turn the refusal into a membership check. The
inventory's own caveat stands (worth it "only if a target program
does this deliberately"); the slice's deliverable is the decision —
envelope it or record keep-refused with that reason — not a promised
flip.

**(d) Queue-tail follow-ons, in only if budget survives (OQ6):**
R3's `[]byte(s)`/`[]rune(s)` capacity envelope (the append-spill mold;
inventory priority 4 — cheap, gc KNOWN outside the singleton on both
arms now) and E3/E4/E5's panic-identity membership treatment
(priority 5). Explicitly droppable; dropping is recorded, not silent.

DONE: (a) landed with envelope statements + membership rows + the
detector; (b) and (c) ruled and executed per the rulings; (d) landed
or recorded-dropped; the coverage ledger's Package_initialization and
(c)-pin rows updated same-change.

## Slice 4 — E9's cross-goroutine widening

The (L) surgery's recorded residual narrowing (inventory E9,
bugfix-arc state): delete-prune rewrites only the SAME-GOROUTINE
continuation — a cross-goroutine delete during another goroutine's
range does not prune that goroutine's `mapIterK` frames. Today every
such shape is already racy-red via the pick-time read footprint (U1
closed), so the narrowing may be unreachable on accepted programs.
Work: decide it — either WIDEN (prune across goroutines, with the
step-atomicity argument for a cross-frame rewrite) or JUSTIFY (a
written argument that every reaching shape is racy-refused, plus the
guardrail case that would go red if the argument's premise breaks).
DONE: the ruling recorded at `Cont.mapIterK`'s docstring and in the
inventory; the guardrail case exists either way.

## Slice 5 — registry-granularity scheduling-point completeness

Register entry 5: the current point set is sound only where scheduling
is unobservable between points for race-free programs, and the
fused-boundary discovery shows it incomplete (termination-ordering
races are schedule-observable WITHOUT data races). After slice 1's
widening, this slice closes the question rather than the anecdote:

- enumerate the observable-without-race classes against the NEW
  boundary set (abort/termination ordering the known class; U-5's
  wide-op arms the known coarse spots inside segments);
- then the register #5 ruling per the master plan's C-C: the
  registry-path-vs-full-interleaving residual either closes via the
  mover/NPDRF theorem — resumed AFTER the machine widens, as the
  upper-bound theorem it should always have been (nondeterminism
  doctrine, "the reduction line resumes AFTER the machine widens";
  proving it against the narrowed set first "would certify the bug's
  width, in the wrong order") — or the claim's docstring scopes it
  explicitly. Either is honest; silence is not. The parked
  `channel-logic-s4` branch records (`docs/2026-08-11_npdrf-reduction.md`,
  branch-only — do not prune the branch) are the authority for the
  reduction line's exact state.

DONE: the class enumeration note; the register #5 ruling recorded
(theorem or scoped docstring); U-5's granularity-ledger re-audit done
or explicitly re-owed with its trigger named.

## Slice 6 — exit artifacts

**S6a. The LaTeX opsem write-up** (user-directed). A human-readable
operational-semantics document — the rules as rules, the choice sites
as marked latitude, the envelope statements as side conditions with
their spec citations. **Its FIRST decision, posed to the user before
any writing (OQ4): hand-written rules with a citation lint** (every
rule names its interpreter arm + spec anchor; a lint checks the names
resolve — drift-visible but transcription-trusted) **vs derived rule
skeletons** (generated from the machine — the WP arc's mirror
`stepFn'` transcription machinery is the standing derivation asset:
a parametric arm-by-arm mirror exists in proof-land on the wp-arc
lane with a default-build drift theorem, and a skeleton emitter over
it would make the document drift-FALSE rather than
drift-lint-caught). Slice 0's audit output directly feeds this — a
semantics worth reading is the audit's acceptance test.

**S6b. The iris-lean refresh & reuse survey.** The Lake dep and the
`deps/iris-lean` reading copy move to a current pin — **the pin move
is its own gated commit** (trust-tools discipline: version pins are
user-approved, never drive-by). Alongside it, the reuse table:
theirs / ours / keep-ours-with-reason, one row per Iris-layer
component we carry (the channel-logic lane's Iris consumers — the
channel WP law family, the LangDM simulation, `dspCompTripleC`'s
machinery — are the demand driver: what the resume will instantiate is
what the table must cover). DONE: pin moved green in its own commit;
the table exists with a reason on every keep-ours row.

**S6c. The channel-logic RESUME-READINESS assessment.** The park
record's promises, sized against the ACTUAL widened machine: what the
slice-1–3 statements need (they were built to survive re-envelope
unchanged — verify, don't assume), the proof re-alignment bill
(LangDM simulation, boundary-adjacent laws, every certificate), the
`channel-logic-s4` salvage plan (its three refutation families are
permanently valuable; its tip's citable-target claim was refuted —
salvage the families, not the claim), and the reduction-line re-target
(slice 5's ruling is its input). DONE: the assessment is a dated doc
the resume charter can consume without re-deriving anything.

## Parallel instruments — recorded here, NOT slices

- **The grossmith re-run + the metamorphic axis.** Re-run the
  grossmith differential campaign against the widened machine (its
  last campaign predates every envelope in this charter), and extend
  it with a METAMORPHIC axis: semantics-preserving program transforms
  (statement reorder within unordered latitude, map-literal
  permutation, spawn-order shuffles) whose observation sets must be
  related as the envelope predicts — a width-exercising instrument
  the point oracle cannot be. External project; findings arrive as
  dated docs per the standing handover pattern.
- **The spec-vs-gc disagreement hunt.** The divergence ledger's feed
  (archaeology census, the two named discussions, the L-007/L-008/
  L-010 erratum family) keeps producing upper-bound evidence
  independently of this arc's slices; L-011 is the proof the hunt
  finds re-envelope work. Curation cadence unchanged.

Both run beside the arc and feed it; neither gates a slice.

## Boundaries (hard, all slices)

- **User gates: G0** (slice-0 refactor queue review), **G1** (the
  boundary-set design note before slice-1 surgery), **per-row rulings
  in slice 2**, **OQ3's rendering ruling in slice 3**, **OQ4's
  write-up route**, **the S6b pin move** — and generally: **every
  envelope-widening that changes the machine's observable set stops
  for sign-off.** Fidelity is the user's lever.
- Merge protocol unchanged; the audit ask unconditional; this arc
  carries the master plan's "strictest audit bar" — semantics is the
  primary dimension, envelope fidelity the named second.
- No gate weakening, no re-pin laundering (every re-pin rides the
  change that explains it), no merge/push/designation by the arc; the
  arc ends branch-complete with the audit ask posed.
- Statement TCB discipline unchanged: widened-machine theorems stay
  first-order-readable over the interpreter; Iris stays proof-device.
- The F4-owned questions (Q-ATOMICITY, Q-GOEXIT) are NOT decided here;
  slice 1's design note records what it leaves open for them.

## Open questions posed to the user (the DRAFT's asks)

- **OQ1 — slice cut and order.** The ladder above runs
  0→1→2→3→4→5→6; slices 2–4 are largely independent after 1 and could
  interleave. Approve or re-cut.
- **OQ2 — slice-1 boundary-set scope** (decided at G1, flagged now):
  post-op points for wake-producing ops only vs all registry ops, and
  back-edge preemption in this arc vs deferred with the wedge fixed by
  post-op points alone. The inventory leans "together" (C2+C3 queued
  as one item); cost is the counterargument.
- **OQ3 — the rendering rows**: observable restatement (scoped green)
  vs standing red. §S3(b) states both honestly.
- **OQ4 — the opsem write-up route**: hand-written + citation lint vs
  mirror-derived skeletons.
- **OQ5 — Q-SYNCLIT's owner**: a slice-2 memo like the others, or the
  cheap named ruling the ledger allows.
- **OQ6 — the queue tail** (R3 capacity envelope, E3/E4/E5
  panic-identity membership): in this arc if budget survives, or
  explicitly next-queue.

## DONE (the conjunction)

1. Slice 0: audit note + graded refactor queue, user-reviewed (G0).
2. Slice 1: wedge de-fused per the G1-approved design — the wedge
   shape membership-green, U-1 probed, envelope statements landed,
   re-proof wave complete, baseline re-pinned with reasons,
   `scripts/ci --slow` green.
3. Slice 2: all eight Q-rows ruled; implementations carry envelope
   statement + membership wiring + budget; deferrals recorded.
4. Slice 3: init-order envelope + detector landed with membership
   rows; the rendering and C5 rulings executed as ruled; queue tail
   landed or recorded-dropped; ledger rows updated same-change.
5. Slice 4: the E9 residual ruled (widen or justify) with its
   guardrail case.
6. Slice 5: the completeness enumeration + the register #5 ruling
   (theorem or scoped docstring).
7. Slice 6: the opsem write-up shipped per OQ4; iris-lean pin moved in
   its own gated commit + reuse table; the resume-readiness assessment
   exists and §S6c's sizing is derivation-anchored.
8. The latitude inventory and doctrine register updated for every
   converted pin (entries re-classed, §7 queue re-ranked, counts
   fixed) — the census stays true.
9. Gates green at tip; the arc-end audit ask POSED (sized to:
   envelope fidelity per widened site, the re-proof wave's honesty,
   the resume-readiness claims).

Honest gaps recorded per slice are legitimate outcomes; silent
narrowings, laundered re-pins, and greens that outrun their envelope
arguments are not.
