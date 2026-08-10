# The GoSpecC decomposition for spawning programs (spec-parity slice 4, 2026-08-10)

Charter item 4 (`docs/2026-08-09_spec-parity-arc-charter.md`). Branch
`spec-parity-s4` off `spec-parity` @ 3af28ab7. This note opens the
slice per the binding discipline: first the decomposition PROOF PLAN
(the recorded successor debt from the channels arc — a frame-quantified
`GoSpecC` whose program genuinely spawns, through iris-lean's
one-thread-step `Language` interface), then the pool-reachability kit's
obligations, then the curated channel-exemplar plan (the select-tricky
trio, muxer, dsp — the charter's flagship comparisons) with the
statement-strength decision. Options are given wherever latitude
exists, with recommendations. NO machine changes anywhere in this plan
— every construction below is proof-layer (relations, checker,
Language instances, kits) over the EXISTING `Multi.lean` machine; if
any step had needed a machine change it would have been parked, per the
slice brief.

## 1. The target and the recorded obstruction

The debt (slice-5 build log + `Surface.lean` witness-status note): a
`GoSpecC` instance at full `InitialSplit` strength — pre/post
frame-quantified over ALL admissible initial heaps — whose program
GENUINELY SPAWNS. What exists: `goSpecC_of_goSpec` (the
sequential-degenerate lane) and the SEEDED fork/join ∀-schedule family
(`allStreamsOkPool`, concrete seed, no frame quantifier). The
obstruction, recorded at slice 5: iris-lean's thread-pool `Language`
steps ONE thread per step, while `StepM`'s pairing rules (`pair`,
`pickPair`) touch TWO threads' configurations in one step — the
arriving op and its parked partner. The concurrent WP pipe (the
`goSpec_of_wp` analogue over `execProg`) therefore needs a proof-layer
DECOMPOSITION of each pairing into per-thread steps.

## 2. The factorization fact (measured, not assumed)

Reading `applyPairing` arm by arm (Multi.lean) gives the load-bearing
observation, and it is SIMPLER than the slice-5 record anticipated:

**In every pairing arm, the entire shared-state delta is attributable
to exactly ONE of the two threads.** Concretely:

- **arriving SEND vs parked recv / parked-select recv clause** (arms
  1–2): the state change is `resumeRecvDelivery`/`selectRecvDelivery`
  into the PARTNER's targets (its delivery frame entry + stores); the
  arriving sender's own config change is pure control (`.next k`).
- **arriving RECV vs parked send / parked-select send clause** (arms
  3–4): the state change is the optional buffer head-and-refill rotate
  PLUS `resumeRecvDelivery` into the ARRIVING receiver's OWN targets;
  the partner's change is pure control (`.next ks` / `.exec body`).
- **arriving SELECT recv-clause vs parked send** (arm 5): rotate + own
  `selectRecvDelivery` — arriving-attributed; partner pure control.
- **arriving SELECT send-clause vs parked recv** (arm 6):
  `normalizeValueForTy` is a pure read; the delivery goes into the
  PARTNER's targets — partner-attributed; arriving pure control.

Consequence: the pairing decomposes as TWO one-thread steps — the
arriving thread's step carries the whole delta when it is the
receiving side (arms 3–5), else no delta (arms 1–2, 6); the parked
partner's step carries the whole delta when IT is the receiving side
(arms 1–2, 6), else no delta — composed in the order
"arriving first, then partner", the endpoint is the machine's
`(ts', σ'')` DEFINITIONALLY. The "storeLoc round-trip lemmas /
structural state equality" the slice-5 record anticipated are needed
only for the CELL-MEDIATED transport variant (option O1(b) below), not
for the simulation itself. This was found by reading; the simulation
proofs will confirm it arm by arm.

## 3. The decomposed per-thread relation (`StepDC`) and its Language

A new proof-layer per-thread relation over `(Config, ExecState)` —
`StepEC`'s superset — with a NEW expression wrapper type (typeclass
instances are keyed by the expression type, so the existing `PoolCfg`
Language and its laws/witnesses stay untouched):

- `lift` — `StepE` (sequential steps + spawn), as in `StepEC`;
- `strip` — the `.spawned` marker strip, as in `StepEC`;
- `wake` — a parked config resumes per `resumeThread s c = .ok (c', s')`
  (per-thread: reads only the shared state and its own config);
- `depositArrive` — a chan/select-apply config with an ∃-quantified
  would-block analysis and partner shape steps to ITS OWN
  `applyPairing` projection (the i-side config + the full state delta
  of arms 3–5, or pure control for arms 1–2, 6);
- `release` — a parked (blocked) config steps to its partner-side
  `applyPairing` projection with the delivered value/ok ∃-QUANTIFIED
  (a parked receiver may release with ANY value; pure-control release
  for parked senders);
- `selectCommit` — a select-apply config commits ∃-some clause per
  `commitClause` (covers `pickCommit`, whose L2 pick is per-thread
  invisible);
- `spin` — a parked config self-loops (see O2).

**The envelope is deliberately WIDER than the machine's.** Per-thread
rules cannot see other threads, so partner existence, L2/L4 picks, and
delivered values are ∃-quantified. That is SOUND for the pipe's only
consuming direction — the simulation maps every real machine step to
D-steps, and adequacy consumes traces — and it is the standard cost:
WP proofs against this Language must handle every ∃-instance (a parked
receiver's WP must absorb ANY delivered value) unless ghost state ties
it. That is exactly where the channel WP law family + the Actris-lite
protocol layer land (recorded successor items; they consume this
Language). A `StepDC` bug can make a proof fail or a WP unprovable,
never a false exported statement — the exports quantify `execProg`.

### Options — O1, value transport in the decomposition

- **(a) direct ∃-quantified delivery on `release`/`depositArrive`**
  (as above): endpoint equality with `applyPairing` is definitional;
  no intermediate states that violate the machine's hchan invariant;
  no new state-equality lemmas. WP-side: the transferred value is
  unconstrained until a protocol layer exists.
- **(b) cell-mediated deposit-then-drain**: the arriving sender pushes
  into the channel cell, the parked receiver pops — intermediate
  proof-layer states a machine run never exhibits (a parked receiver
  beside a nonempty buffer), endpoint equality by storeLoc round-trip
  lemmas. WP-side: an Iris invariant on the cell can constrain the
  transferred value WITHOUT a separate protocol ghost.

**Recommendation: (a)** for this arc's pipe — it is the minimal sound
simulation and adds no false-looking intermediate states. (b) is
recorded as the refinement the channel WP law family may prefer;
adding rules later WIDENS the Language and would oblige re-checking
existing WP proofs' step case-splits, so if the protocol-layer arc
chooses (b) it should land as a fresh Language wrapper the same way
this one does beside `PoolCfg`.

### Options — O2, parked configurations and stuckness

A parked config with no wake-ready cell has, without extra rules, only
the ∃-release steps. For `.NotStuck` adequacy every non-value thread
in every reachable pool must be reducible; releases keep parked
receivers reducible, but a parked config whose blocked shape has NO
release projection (none exist today — every blocked shape has one)
or a future shape gap would turn stuck.

- **(a) spin self-loops** (the slice-5 sketch): parked configs are
  always reducible; `.NotStuck` adequacy goes through; Löb induction
  discharges the spin case in WPs. Honesty consequence (already
  recorded at slice 5): pool `NotStuck` then says NOTHING about
  deadlock — the deadlock/race exclusions must come from the
  reachability kit REGARDLESS.
- **(b) no spin, stuckness-generic laws, exit at the weakest
  sufficient stuckness**: the triple half of the exit consumes only
  `adequate_result` (the reached-pool readout), not reducibility; the
  laws are already written stuckness-generic in the existing `wpC_*`
  house style.

**Recommendation: (b) first, (a) only if the adequacy entry point
demands `.NotStuck`** (iris-lean's `wp_adequacy`/`wp_strong_adequacy`
signatures decide it at build time — this is internal plumbing either
way: no exported statement mentions stuckness, and the deletion test
keeps Iris out of every designated statement). Either lane changes
nothing about what `GoSpecC` asserts.

## 4. The pipe, end to end (the proof plan)

1. **Simulation** (`stepM_erased_D`): every `StepM m m'` step maps to
   1–2 erased thread-pool steps of the D-Language from
   `(m.threads.toList, m.shared)` to `(m'.threads.toList, m'.shared)`
   — `thread`/`spawned`/`wake`/`pickCommit` one step each (`lift`
   +forks / `strip` / `wake` / `selectCommit`), `pair`/`pickPair` two
   (`depositArrive` then `release`, §2's attribution). List surgery:
   `setIfInBounds`/append as `t₁ ++ e :: t₂` splits.
2. **Run erasure** (`execProg_steps_erased_D`): an
   `execProg fuel env σ₀ ch prog = .ok (.normal σf, ch')` run yields
   `([mk (.exec prog env .stop)], σ₀) -·->* (mk (.next .stop) :: rest, σf)`
   — by `execProgLoop` induction over `stepMulti_sound` (each executable
   step is a `StepM` step; `raceUpdate` results are discarded — the run
   completed, so they all succeeded) plus §1; `mainOutcome? = some
   (.normal σf)` pins main's config to `.next .stop` (a value of the
   pool `ToVal`).
3. **Heap-handover adequacy over the D-Language**
   (`goDC_heap_adequacy_own`): `go_heap_adequacy_own`'s pool twin —
   same `GoCoreS` bundle, same gen_heap `StateInterp` (the state type
   is unchanged), `forkPost = True`.
4. **The exit** (`goTripleC_of_wpDC`): from a WP against the
   D-Language, `GoTripleC` at full `InitialSplit` strength — the
   sequential `goSpec_of_wp`'s triple half, re-plumbed through 2 + 3.
   The exit CONSUMES the simulation generically: every `execProg` run
   of ANY program erases through it, pairings included.
5. **The safety half** (`ProgressExecC`) does NOT come from adequacy
   (§3 O2's honesty note — parked spins/releases make pool
   no-stuckness silent on deadlock, and `.raceDetected` is an
   interpreter-loop refusal the Language never sees). It comes from
   the POOL-REACHABILITY KIT (§5). `GoSpecC = GoTripleC ∧
   ProgressExecC` assembles per-program.
6. **Witnesses** (O4): the first frame-quantified genuinely-spawning
   instance is the SPAWN-NOOP class (`spawnNoopProg` — main forks a
   worker; no pairing in its own traces, but the exit it goes through
   consumes the full pairing simulation). The fork/join
   full-strength instance additionally needs WP laws for the
   channel-op/park/release positions plus an invariant tying the
   delivered value — the CHANNEL WP LAW FAMILY + protocol layer,
   which the channels-arc record already sizes as landing together
   with this pipe's consumers. Recommendation: spawn-noop witness
   with the pipe; fork/join with the protocol layer (successor
   movement, not silently dropped — it stays the named remaining
   debt).

## 5. The pool-reachability kit (what it must provide)

For `ProgressExecC` (and any per-program deadlock/race-exclusion at
∀-heap strength) the kit needs, program-generically:

- **run-decomposition lemmas**: `execProgLoop` stepping as
  `stepMulti`+`raceUpdate` chains (partially in `MultiSound.lean`
  already: `stepMulti_sound`, `execProgLoop_unfold`,
  `execProgLoop_mono`);
- **an invariant-induction principle**: from `InitialSplit`-shaped
  initial states (arbitrary frame heap), a per-program pool-shape
  invariant `I : MultiConfig → Prop` preserved by every `stepMulti`
  step, strong enough that (i) the all-asleep deadlock classifier
  never fires, (ii) `raceUpdate` never returns a conflict, (iii) every
  non-terminal pool has a successful step. For the spawn-noop class
  this is a finite control-shape enumeration parameterized by the
  frame; for pairing programs it grows protocol content — same
  successor boundary as §4.6.
- **pool projections**: which thread shapes are reachable (bounded
  spawn count, main's frame discipline) — the `MultiWf` carrier plus
  program-shape refinements.

The kit is sized WITH the pipe; whatever lands this slice lands with
its witnesses (nothing inert), and the remainder is recorded as owed
WITH ITS CONSUMER — the fork/join full-strength instance.

## 6. The curated channel exemplars (charter item 3) — statement strength

The flagship set, fixed by the charter: the SELECT-TRICKY TRIO
(`nb-not-ready`, `nb-guaranteed-ready`, `nb-full-buffer-not-ready` —
upstream `channel_select_tricky_examples.v`), MUXER (`async`,
`client` — upstream `channel_dsp.v`/`channel.v`), DSP
(`actris-example`, Actris 2.0's prog3 — upstream `channel_dsp.v`).
All six are R1-green imported rows. Upstream per-row proof status is
measured at deps/perennial @ 43d4efa and recorded per row in the
manifest (`docs/spec-parity-r3-manifest.md`, new feature-class-3
section) with Qed line numbers.

**Statement-strength options for our side, this slice:**

- **(a) the seeded ∀-schedule family** (the fork/join idiom, D1-shaped
  at seeded strength): per program, over the PINNED lowering
  (staleness-guarded, ci 1c5) at the TotalPins-style seed — the
  kernel certificate `allStreamsOkPool post fuel = true`, and from it:
  the ∀-schedule verdict readout (every stream completes at main's
  `.normal` with the oracle's observable), no-deadlock and no-race
  first-order corollaries, and `TerminatesNormallyC`. All
  interpreter-vocabulary, deletion-test-clean statements.
- **(b) frame-quantified `GoSpecC` triples**: blocked for ALL six on
  the §4 pipe plus the channel WP law family (none of the six is
  walkable without WP laws for make/send/recv/select positions —
  sequential OR concurrent). Not reachable this slice; each row
  records this as its named gap.
- **(c) sequential-lane `GoSpecC` for the two non-spawning trio
  members** (`nb-guaranteed-ready`, `nb-full-buffer-not-ready` spawn
  nothing): would need NEW SEQUENTIAL channel WP laws (chan-op
  entry/apply, select entry/apply-done). Declined this slice with a
  reason: the channel WP law family should land ONCE, shaped by the
  concurrent pipe's consumers (§4.6), not twice in a
  sequential-special shape that the decomposition arc would restate.

**Recommendation: (a) now, per-row gaps naming (b) [and (c) for the
two sequential members] — taken.** Honesty line for the manifest, both
directions: our (a)-statements are SEEDED (no frame quantifier — the
concrete TotalPins-style seed), which is WEAKER than their
frame-general Iris triples in generality; they are also
schedule-exhaustive TOTALITY+verdict statements over the
differentially tested `execProg` (every modeled schedule completes
with the exact observable — no-deadlock/no-race included), which
their partial-correctness `NotStuck` WPs do not assert (GooseLang
NotStuck excludes stuck/racy configurations but not divergence or
parked-forever schedules; and their model is untested). No ordering
claim between the judgments; the deltas are recorded per row.

### The checker extension the trio needs (non-consuming select applies)

`allStreamsOkPool` today fails CLOSED on ANY select-apply
configuration (`consumesSelect`), so the trio — whose every select is
in fact NON-consuming — cannot be certified. Measured on the machine:
`applySelect` consumes the L2 pick ONLY at ≥ 2 ready clauses
(`applySelectCore` returns `.picks`); zero-ready-with-default,
zero-ready-park, and singleton-ready commits return `.done` and touch
no stream. The trio's selects: `nb-guaranteed-ready` (one thread,
closed-recv ready + default → singleton commit), `nb-full-buffer` (one
thread, zero ready + default), `nb-not-ready` (two threads, neither
ever parks — both selects zero-ready + default; no waiter, so the
arrival analysis is `.cellPath`). Options:

- **(a) status quo**: the trio is checker-refused — the flagship rows
  ship without their ∀-schedule half. Refused.
- **(b) the non-consuming-`.done` refinement (RECOMMENDED, taken)**:
  `poolThreadOblivious` accepts a select-apply config iff its arrival
  analysis is `.cellPath` AND `applySelectCore` on it returns `.done`
  — both kernel-computable on the spot. Soundness obligations:
  `stepThread_oblivious` gains the arm (the step equals the `.done`
  projection under EVERY stream), and `raceUpdate_oblivious`'s
  hypothesis generalizes (the detector's select arm reads the stream
  only in its `.multi`/≥2-ready branches, which the `.done` condition
  excludes; the parked-`.done` case lands in the detector's
  post-config `.blockedSelect` early return). Fail-closed posture
  unchanged: genuinely multi-ready selects still refuse.
- **(c) full L2 branching** (enumerate ready-clause picks like the L1
  pick): needed only for programs whose runs hit ≥ 2-ready selects
  (e.g. upstream's `select_blocking`/`select_multiple_ready`
  examples); a real extension with its own probe-stream design —
  recorded as future checker work, not taken (no curated row needs
  it).

The extension is proof-layer checker growth (`MultiStreams.lean` —
`execProg` untouched, zero corpus effect); it ships with a same-commit
witness (a golden non-consuming-select program certified end to end)
plus the trio certificates as its first real consumers.

## 7. Ship list for this slice (recorded before building)

1. This note (commit 1).
2. The §6 checker extension + its golden witness (commit 2).
3. The six curated rows: pinned lowerings (3 new pin modules +
   `check-imported-pins` registration), certificate families per row,
   manifest feature-class-3 section with per-row upstream ground truth
   at 43d4efa and both-direction deltas (commit 3; split if natural).
4. The §3–§5 pipe, built to the deepest COHERENT consumed-and-witnessed
   boundary that fits the slice: relation + Language + laws +
   simulation + erasure + adequacy + exit + spawn-noop witness, in
   that dependency order; anything not reached is recorded owed WITH
   its consumer, never landed inert. Progress and stopping point in
   the build log below.
5. Designation candidates recorded (nothing designated, charter D3);
   the 44 designated statements byte-identical.

## 8. Build log

- **Commit 2 — the §6(b) checker refinement, witnessed both ways.**
  `selectApplyDone` + the `poolThreadOblivious` select arm;
  `stepThread_oblivious` gained the `.done` arm (`stepFn_select_done`,
  `applySelect_of_done` — both constructive, `[propext, Quot.sound]`);
  `poolThreadOblivious_nsel` GENERALIZED to `poolThreadOblivious_sel`
  (a disjunction — the old name is gone, its one consumer rewired) and
  `raceUpdate_oblivious`'s hypothesis widened with it (the detector's
  select arm reads the stream only in the multi-ready branches
  `applySelectCore_done_inv` excludes; the parked-`.done` case exits at
  the detector's post-config `.blockedSelect` return). Witnesses
  same-commit: `Specs/GoldenSelectDone.lean` — the golden select-probe
  program (zero-ready+default both directions, close, singleton-ready
  commit; `selDoneAllStreamsCert`/`selDoneAllSchedules42`) and the
  NEGATIVE control `selConsumingRefused` (a two-ready select program
  that RUNS fine is still checker-refused; `#eval`-confirmed before
  `decide`, per doctrine). ci PASS, zero drift.
- **Commit 3 — the curated rows (§6 option (a), taken).** Three pin
  modules + `check-imported-pins` registration (guard green against
  fresh emits); `Specs/GooseParityChannels.lean` — six rows × five
  kernel theorems + the four generic `chanCert_*` derivations
  (hoisting candidates, header-recorded); manifest feature class 3
  with measured upstream statuses and both-direction deltas.
  Certificate fuels measured (see manifest); the six-row module
  kernel-checks in ~20 s.
- **Commit 4 — the decomposition pipe (§§3–4), built through THE EXIT
  and its witness** (`proofs/GoLeanProofs/LangD.lean`):
  - `StepDC` (lift/strip/wake/pairArrive/pairRelease/selCommit — O1(a)
    direct ∃-delivery taken as recommended; NO spin rules — O2(b)
    sufficed: the exit consumes `adequate_result` only, and the
    spawn-noop witness's WPs discharge `.NotStuck` reducibility at
    every config they walk) + the `PoolCfgD` Language instance.
  - `applyPairing_shape` (the pairing inversion: partner index, parked
    pre-shape, two-point update — the only per-arm walk the simulation
    needed; the §2 attribution fact was NOT needed, as predicted).
  - **`stepM_erasedD` — THE SIMULATION**: every `StepM` step is 1–2
    erased D-steps (`pair_erasedD` shared by `pair`/`pickPair`:
    arriving step carries the whole delta, partner releases
    state-preserving at the post-state). Constructive
    (`[propext, Quot.sound]`).
  - **`execProg_erasedD` — run erasure**: every `.ok (.normal σf)`
    `execProg` run is an erased D-trace ending with main's terminal
    VALUE at the head (detector verdicts discarded — the run
    completed). Constructive.
  - `goD_heap_adequacy_own` (the heap-handover adequacy port) and
    **`goTripleC_of_wpD` — THE EXIT**: `GoTripleC` at full
    `InitialSplit` strength from a D-Language WP; consumes the pairing
    simulation generically for every program.
  - The `wpD_*` law kit (`pure_det`/`spawned_strip`/`fork` ports; two
    new shape side-conditions refute the decomposed rules via
    `arrivalCases_of_nonApply`/`stepDC_shape_cases`).
  - **THE WITNESS — `spawnNoopTripleC`**: the first frame-quantified
    `GoTripleC` whose program GENUINELY SPAWNS (the debt's triple
    half), with `spawnNoopReadoutC` discharging every `InitialSplit`
    premise at the concrete seed (non-vacuity) and reading the triple
    back as a first-order interpreter fact. Axioms: the classical trio
    on the Iris side, `[propext, Quot.sound]` on the simulation lane.
  All registered in `proofs/Audit.lean` (name-existence-tripwire
  scope, as its blocks state).

## 9. Owed after this slice (recorded, each with its named consumer)

- **`ProgressExecC` at ∀-heap strength for the spawn-noop witness**
  (the pool-reachability kit's first instance, §5): without it
  `GoSpecC = GoTripleC ∧ ProgressExecC` cannot assemble for the
  spawning witness. The triple half was the recorded obstruction and
  is paid; the safety half is invariant-induction work over
  `execProgLoop` with a symbolic heap — sized as its own movement.
  Consumer: `spawnNoopSpecC` (the debt's full form).
- **The channel WP law family + protocol layer** (§3's envelope
  refinement, §4.6): the fork/join full-strength `GoSpecC` and any
  frame-quantified triple for the six curated channel rows need WP
  laws at chan/select apply and park/release positions plus an
  invariant tying delivered values (O1(b) or ghost). Consumer: the
  curated rows' D1 form 1 (each row's manifest gap).
- **Checker L2 branching** (§6(c)): only if a future curated row hits
  a genuinely multi-ready select.

