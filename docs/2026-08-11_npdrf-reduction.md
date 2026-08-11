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

Consequence, stated precisely: **in any `StepsM` run, at most one
goroutine is ever strictly mid-segment** (has stepped past a boundary
without reaching the next one) — the running one. The fine relation
can hold two goroutines strictly mid-segment simultaneously. With
`.done` pinning the whole shared state, that difference is a
reachable-RESULT difference, race-free.

The counterexample class (obstruction 4's, now made exact): main
(goroutine 0) already terminal; two spawned-and-leaked goroutines A
and B, each performing TWO stores to its own private pre-existing
cell (A: x:=1 then x:=2; B: y:=10 then y:=20), no synchronization
anywhere. All footprints are per-goroutine disjoint (`locOverlap` on
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
partway). Only the ≥ 2-simultaneously-mid-segment states are outside
the coarse set. That is why the counterexample needs TWO leaked
writers; one is not enough.

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
  concurrent segment — is narrower than it sounds: `enterFrame`
  allocates (locals), so EVERY call in a post-spawn segment
  allocates. Straight-line no-call segments (the dsp child's
  `*p = 42; sig <- …` shape) qualify; anything with a call does not.

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

## 4. The corrected statement (the citable target) and its parts

The corrected reduction, stated in Lean this slice as a `Prop`-valued
definition (citable as a proof target — unlike the draft, no known
counterexample class applies; the argument for its truth is below):

    def PoolResult.sameClass : PoolResult → PoolResult → Bool
      -- panicked _ ~ panicked _ ; deadlocked ~ deadlocked ;
      -- done o ~ done o' iff o, o' share their ExecOutcome constructor

    def NPDRFClassReduction : Prop :=
      ∀ m₀ : MultiConfig, ¬ RacyFine m₀ →
        ∀ res, ReachesMFine m₀ res →
          ∃ res', ReachesM m₀ res' ∧ res.sameClass res' = true

(The ⊇ direction needs no new statement: `reachesM_le_fine` gives it
with literal equality, which implies `sameClass`.)

Truth argument (why this form escapes the known refutation classes):
`sameClass` ignores states and messages, so §1's mechanism (whole
`ExecState` in `.done`) and §2's mechanism (addresses in values and
messages) have nothing to bite on. What remains is the classic
normalization claim: a fine run of a race-free pool reaching a panic
/ main-terminal / all-asleep configuration can be reordered — swapping
adjacent independent steps, preserving registry-op order — into a
boundary-switched run reaching a configuration of the same class.
Sync operations happen at boundaries in BOTH relations, and DRF makes
cross-thread non-sync steps footprint-disjoint, so the reordering
preserves each thread's local computation (the values it reads) and
hence its terminal class and each channel op's outcome. The two known
non-commuting ingredients — allocation order and assoc-list insertion
order — change addresses and heap layout, never a result CLASS,
because no modeled operation branches on a raw address value
(pointer equality compares `Loc`s, which rename consistently under
the run permutation). This argument is exactly plan steps (i)–(iii)
of the mover route, up to iso; it is NOT discharged this slice — the
def ships scaffold-marked with an explicit no-theorem-cites-it-as-
proved rider, mirroring the draft's discipline, but now legitimately
citable as a target.

Statement-TCB posture: `NPDRFClassReduction` and its parts stay proof
infrastructure. `StepMFine`/`StepsM(Fine)` remain in the Audit
statement-closure forbidden set; nothing headline-shaped may depend
on them; the corrected statement changes nothing about what
designated statements say (the 48 stay byte-identical).

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
  never-spawning pools. For `m₀` with one thread, `cur = 0`, and
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
> whole-state results + ≥ 2 leaked mid-segment goroutines); the
> corrected class-level reduction (`NPDRFClassReduction`) is the
> recorded open target, proved so far only for never-spawning pools.
> For spawning programs these theorems claim registry granularity
> ONLY; sub-registry transfer is unproved.

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
SCHEDULING; they do not touch the detector at all. The one relevant
asset predates this slice: the shared `stepAccesses` table
(obstruction 5), which makes item 3's vocabulary already aligned.
Items 1–2 are a detector-correctness development comparable in scale
to the whole S3 detector build (a multi-commit slice), independent of
anything proved here.

**Evaluation: the rule's condition is NOT met.** The proven fragment
does not reduce detector-completeness below one slice — the honest
estimate is 2+ slices (FastTrack correspondence + driver bridge).
Recommendation to the rule: take the ELSE branch — record the
asymmetry as permanent with the O4/T12 axis split as its statement
(ours: executable, oracle-aligned, differentially testable detection
with the racy/litmus lanes; theirs: granularity-complete-by-
construction race-UB with no way to test it). The completeness
theorem remains statable later; nothing this slice closes that door.
Per the charter, either branch is SUCCESS and the lane does not stop.

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
