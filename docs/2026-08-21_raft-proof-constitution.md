# THE PROOF CAMPAIGN CONSTITUTION — raft correctness (2026-08-21)

**Status: DRAFT — awaiting Mike's ratification.** Every hole only Mike
can fill is marked **[MIKE]** inline and collected in §8, the sign-off
questions. Until ratified, nothing here charters work; after
ratification, this document governs the raft proof campaign for its
whole life, and is amended only per §4.5.

---

## §1 Preamble — what this document is

Mike's framing, verbatim-in-substance (2026-08-21): this campaign is
*unusually long running and open ended, so the aim should be clear
guidance on goal, but a lot of latitude on how to get there. Basically:
here's what we want, figure it out (no cheating).* And: advice for the
road is a first-class section, not an appendix.

That makes this a CONSTITUTION, not a charter. The difference is
structural, and worth stating because every prior long run here was
chartered:

- **A charter enumerates tasks.** Its DONE is a conjunction over a
  known work list (the gallery campaign's form, the W3.2 form). It is
  the right instrument when the work is enumerable up front.
- **A constitution fixes ENDS and delegates MEANS.** The proof of raft
  correctness is not enumerable up front — the route (invariant order,
  lemma architecture, refinement vs direct, tooling investment) is
  precisely what the campaign must discover. So this document states
  the theorems to be proved with precision (§2), makes "no cheating"
  mechanical rather than exhortative (§3), and carries it through
  INSTITUTIONS — standing gates, cadences, and disciplines that do not
  depend on any task list (§4) — while explicitly delegating everything
  else (§5).
- **A charter ends; a constitution persists.** Individual arcs inside
  the campaign may still be chartered in the usual form; each such
  charter is subordinate to this document and to standing doctrine
  (§7).

The campaign's position on the ladder: the master plan
(`docs/2026-08-15_raft-master-plan.md`) runs to M5, "the statement is
pinned; the challenge is set." This constitution governs from now
THROUGH the proof (P3 of `docs/2026-08-15_raft-push-p0-scoping.md`) —
it is written before M5 deliberately, so the statement is pinned under
its rules rather than grandfathered into them.

---

## §2 The Ends — the theorems, stated precisely

The ends are theorem STATEMENTS. The campaign succeeds exactly insofar
as these statements are proved, kernel-checked, over the machine as it
honestly is. The statement SHAPE below is constitutional: **better
lemma architectures are always welcome; weaker top-level claims
never.** Any change that weakens a top-level claim — a narrower
quantifier, a stronger hypothesis, a weaker conclusion, a smaller
subject — is an amendment (§4.5), not a judgment call. Changes that
strengthen (wider envelope tiers, added conclusions, larger n) land as
strengthenings without amendment, with their envelope arguments.

### 2.1 The base theorem: conditioned agreement

Over the machine-twin harness (`docs/2026-08-20_machine-twin-harness-design.md`
— the harness the theorems quantify over; its go-run twin
`raftharness/` is the executable spec it must not rewrite):

> **Agreement (conditioned safety).** For ALL choice streams and ALL
> fuel: if the twin's run under the interpreter completes
> (`run = .ok r`), then the executable safety invariant held at EVERY
> step of the run — S1 election safety (at most one leader per term),
> S2 log/apply agreement (no two nodes apply different `(term, data)`
> at one index), S3 apply monotonicity — as the per-step state
> predicate the harness itself checks (machine-twin design §4).
>
> **Completion witness (the non-vacuity twin).** There EXISTS a choice
> stream and fuel under which the run completes, passes, and meets the
> exercise floor (at least one leader claim, at least one committed
> command on every node — S4 as stopping condition). Without this, a
> harness that always deadlocks satisfies conditioned safety vacuously
> — forgery-by-deadlock, named at P0 §3.1.

Fixed n=3 first; quantified `num_parties` is a tier above, not the
gate (P0 §3.3).

**Over the slow-obviously-correct semantics.** The statement's
quantifiers range over the naive executable interpreter — `stepFn`
iterates / the naive multi-step enumeration — never over any
accelerator, evaluator, or deduplicating enumerator. This is the
standing exec-slow principle (the W3.2 POR design's form —
`docs/2026-08-21_w32-por-design.md`, w32 lane, branch-state at
drafting: claims restate over `SlowObs`, the six-line naive
definition; the optimized engine earns its use by a proven equality
to the slow one, and "top-level statements never mention the
optimized enumerator"). The
Sym mirror evaluator obeys the same template on the sequential side
(`docs/kit-guide.md`; refinement theorems in the default build). Proof
machinery may run fast; meaning stays slow and readable.

**First-order readout corollaries.** Every headline theorem ships its
first-order readout per the TCB doctrine
(`docs/2026-08-01_tcb-and-layering-doctrine.md`): statements
semantically interpretable with Iris and the Prop-level relation
deleted; the deletion test enforced by the statement-TCB walker; the
Agreement predicate defined from base definitions over the interpreter
(the checker stays harness Go / first-order Lean — machine-twin §4).

### 2.2 The fine print IS part of the statement

The scope qualifiers live in the pinned statement's documentation,
never in anyone's head. Three are known now:

1. **The envelope tier.** v1 network: reliable-first — no drops, no
   duplication; unbounded reordering and delay (machine-twin §2,
   choice-site spec). This is a weaker theorem than raft's design
   point and the docstring says so. `drop`/`dup` are already in the
   event vocabulary; turning them on is a WIDENING and lands as a
   strengthening tier with its latitude entries (C-B), not a
   re-statement.
2. **The RawNode serialization contract.** The v1 twin bundles each
   RawNode call with its full Ready harvest — a DELIBERATE ENVELOPE
   NARROWING relative to what upstream licenses (`stepsOnAdvance`,
   `doc.go:101-103`), recorded with its re-envelope obligation
   (machine-twin §2: widen additively via a `harvest` event). At v1
   the theorem is about a subset of conforming drivers and must say
   so. **[MIKE]** — accept this narrowing as v1 fine print (the
   recorded obligation discharging at W4.5 or later), or require the
   widened harvest event before the statement is pinned.
3. **The subject-delta ledger.** The theorem is about the vendored
   subject: real etcd-io/raft at the recorded pin, plus the itemised
   deltas (the `plainpb` shim per the §8.6 ruling of the P0 doc, the
   logger seam, every recorded trim). The statement cites the ledger
   (`docs/raft-w2-log.md` subject-delta section and successors); a
   delta not in the ledger is a violation, not a shortcut.

### 2.3 The ladder above agreement

Tiers are pinned as statement variants; each tier proved is a
milestone (§4.2). The conditioned-safety ladder, in the classical
raft-paper order — **[MIKE]: confirm or reorder the tiers, and rule
which are IN the campaign's ends vs explicitly stretch:**

- **T1 — Agreement at n=3** (§2.1; the base — this one is not
  optional).
- **T2 — quantified `num_parties`** (pool-size induction; P0 §3.3).
- **T3 — the deeper safety invariants as named theorems: leader
  completeness, log matching, state-machine safety** — the invariant
  lattice Verdi Raft proved and the natural decomposition any route
  will build anyway; ruling wanted on which are HEADLINE ends (pinned,
  designated, comparator-judged) vs proof infrastructure beneath T1.
  **[MIKE]**
- **T4 (stretch) — linearizability of a small KV service over the
  cluster** — requires a client layer; explicitly a stretch tier per
  P0 §3.2/§8.1. **[MIKE]: confirm stretch status.**

### 2.4 The liveness tier (later, and honestly conditional)

Unconditioned liveness is false over the full envelope (election
livelock; the FLP tension, P0 §3.1). A liveness tier is therefore a
theorem UNDER A FAIRNESS HYPOTHESIS: a `Fair : Choices → Prop`
restriction — definable at all only because the W3.2 boundary-set
work preserved pick identifiability and made back-edge preemption a
boundary (fairness non-preclusion, master plan §W3.2). Its envelope
provenance is the scheduling dossier
(`docs/2026-08-20_go-scheduling-semantics-dossier.md` §3.1): the spec
allows unbounded scheduling delay (Pratt), while eventual scheduling
is a strong gc expectation and starvation treated as a bug (Mills,
issue #65178) — so the fairness hypothesis is an HONEST added
assumption matching gc practice, never smuggled into the machine.
**[MIKE]: is the liveness tier inside this campaign's ends, or a named
successor campaign?**

---

## §3 The Inviolables — "no cheating", made mechanical

Each rule is standing doctrine cited to its source. These bind every
worker, every arc, every tier, for the campaign's life. They are not
advice; a violation is a defect even when the theorem is true.

1. **Statements over the naive semantics.** §2.1's exec-slow
   principle. Accelerators (Sym, POR/dedup enumeration, any future
   engine) ship WITH their refinement/equality theorem to the slow
   semantics and stay out of every statement closure. (W3.2 POR
   design; `docs/kit-guide.md`; TCB doctrine.)
2. **Statement TCB and designation discipline.** The deletion test;
   the statement-TCB walker over designated headline theorems;
   first-order readouts mandatory; Iris, ghost state, prophecy, and
   the Prop-level relation are proof devices and never statement
   dependencies. Designating a theorem (adding it to the walker's
   list) is Mike's act, not the campaign's
   (`docs/2026-08-01_tcb-and-layering-doctrine.md`; gallery precedent:
   the designation stop was one of the two right stops).
3. **Every user-facing law ships its non-vacuity witness** in the same
   commit, or is marked scaffold in its docstring. The smell to check
   first: a premise quantified `∀σ` over the state. (CLAUDE.md,
   non-vacuity gate; `wp_assign` shipped vacuous twice.)
4. **No envelope narrowing to ease a proof — a proof wanting a
   narrower machine POSES A RULING.** Fidelity is Mike's lever,
   exclusively. The precedent is exact: the BUG-005 memo proposed two
   termination-buying narrowings with recorded obligations, and Mike
   struck both — "any latitude in the Go spec should be supported"
   (`docs/2026-08-19_bug005-map-range-memo.md` §5, Q2). When a proof
   is easier over a narrower machine, write the ruling request
   (excluded behaviors, spec argument, cost of the wide version) and
   stop; never pin silently. Same rule for every observable-set
   change (`docs/2026-08-20_w32-re-envelope-charter.md` §Boundaries).
5. **No gate weakening, no re-pin laundering, red-until-proven.**
   Gates (`scripts/ci`, the audit gates, the baseline diff,
   `check-raft-goal` once it exists) are never weakened by the
   campaign; every baseline re-pin rides the change that explains it;
   a red row stays red until the honest fix — never edit canonical
   Go, weaken the oracle, or reclassify to make something pass.
   (CLAUDE.md, validation gate + small-slices; long-cycle hard
   boundaries.)
6. **Bounds as bounds; honest gaps legitimate but never counted.** A
   measured form is recorded beside the bound, not as it. A gap
   honestly recorded is a legitimate outcome of an attempt; it never
   counts toward any total, milestone, or tier claim. (CLAUDE.md
   long-cycle section; gallery trip report §6.)
7. **Progress IS machine-checkable theorems with witnesses — never
   activity metrics.** Lines written, lemmas attempted, sessions
   burned, "80% of the invariant lattice sketched" are not progress
   claims. A progress report names: theorems kernel-checked at the
   tip, their witnesses, the failing-set state, and the frontier.
   (Gallery: the counted DONE was what made 34 hours of autonomy
   honest.)
8. **The comparator at landmarks.** Any arc that adds or changes a
   designated headline statement runs `scripts/comparator-judge`
   before merge — the independent kernel-replay judge, landmark
   cadence, never part of `scripts/ci`. (TCB doctrine, operational
   enforcement; CLAUDE.md merge protocol step 2.)
9. **Everything CLAUDE.md already makes inviolable stays so** — fail
   closed always; GoCore purity; proof-facing code total (no
   `partial`, no `sorry`, no `native_decide` in the semantic core);
   capped builds; trust tools never modified; sandbox blocks are
   asks, not hacks. Restated here only so no subordinate charter can
   claim this document superseded them (§7).

---

## §4 The Institutions

The mechanisms that carry "no cheating" across months without a task
list. These are how the constitution governs.

### 4.1 Mike's gates — the decisions that are never the campaign's

- **Designation**: adding/changing entries on the statement-TCB
  walker's designated list (§3.2).
- **Envelope rulings**: every observable-set change, in either
  direction — widenings AND any proposed narrowing (§3.4). The ruling
  request is a written block the ruling can be recorded into, in the
  style already proven out (the W3.2 charter's Rulings block; the
  boundary-set decision table with per-strike consequences).
- **Merge and push**: the standing merge protocol unchanged — the
  audit ask unconditional before any merge, sign-off at that moment
  for that merge, push separate (CLAUDE.md). The campaign ends arcs
  branch-complete with the audit ask POSED.
- **Comparator landmarks** (§3.8) and external claims.
- **Constitution amendments** (§4.5).
- **Named design gates** any subordinate charter declares (the G0/G1
  pattern) — these stop the run until ruled.

### 4.2 Audit cadence: at MILESTONES, not slices

Adversarial audit attaches to milestone claims — a tier proved (§2.3),
a statement pinned or re-pinned, a machine-surgery landing the proofs
rest on — not to every slice. Slices get the standing gate
(`scripts/ci`, focused differentials, baseline diff); milestones get
the full decorrelated-reviewer pattern with SEMANTICS ALWAYS THE
PRIMARY DIMENSION (CLAUDE.md, "how to run the audit" — the audit
must audit the final state, and never skips a dimension because it
has been passing). The merge-time audit ASK remains unconditional
regardless of cadence — cadence governs when audits are proposed as
part of the plan, never whether the ask happens.
**[MIKE]: ratify the campaign's milestone set** — proposal: each tier
of §2.3, the M5 statement pin, and any semantic-core surgery the
campaign needs (which also takes the W3.2-style "strictest bar").

### 4.3 Continuity — artifact-mediated, per the gallery case law

The gallery campaign is the validated precedent
(`docs/2026-08-16_gallery-campaign-trip-report.md`; CLAUDE.md
long-cycle section). Its rules apply campaign-long:

- **One writer per worktree — hard rule.** Fence a worktree before
  dispatching a successor; silence is not death — message first.
- **Module status blocks, stashes with completion notes, snapshot
  refs before risky git ops** (`refs/snapshots/`), per-goal log files
  with one-line judgment-call entries, **checkpoints every ≤5
  units** — and checkpoint numbers recomputed, not restated (trip
  report lesson 15).
- **Successors re-verify predecessors' top claims** before building
  on them. Both gallery fabrications were caught exactly this way.
- **Summary layers obey worker rules**: every number in an index,
  checkpoint, or report carries a build, a probe, or a SHA — that is
  where drift lives (trip report, revised readout).
- **The serialization resource is identified up front** — for this
  campaign: the semantic core, `Corpus/`, `baselines/`, and the
  pinned statement file. Writers to it are batched into waves; only
  file-AND-interface-disjoint units parallelize; interface changes
  land at wave boundaries (trip report lessons 3, 8, 9).
- **Units sized to one session, every unit parkable**: thin-top
  layering, tracer maps in proof briefs from day one (lesson 12).
- **Cross-doc cites unit-anchored or commit-qualified**, never bare
  tip-relative lines; anything cited from a lane in flight is
  branch-state and re-checked when consumed (the W3.2 charter's
  kickoff-re-check discipline).

### 4.4 The emergency exit — always available, verbatim-in-substance

Any campaign agent may declare an EMERGENCY EARLY EXIT, stating the
nature of the emergency; it is ALWAYS permitted without question, no
matter the reason given (P0 §1, kept verbatim per P0 §4.4 — the
unconditional acceptance is what makes the hatch reliable). Use it for
true stuckness, mis-specification, or dire threat — not routine
decisions, which are made and logged (§5). On use: park record +
report. And the standing honesty incentive replaces completion
pressure: **an honest "not done — here's the frontier, the decision
log, what's proved" is an acceptable end state; a forged "done" is
the only unacceptable one** (P0 §4.3).

### 4.5 Amendment

Only Mike amends this constitution. Amendments are made IN THIS FILE,
dated, with the reason, in place (the ruled/dated block style of the
W3.2 charter — a ruling left in chat is a ruling that rots).
Subordinate charters may add constraints for their arc; they may never
relax this document. Weakening a §2 statement is an amendment;
strengthening is not (§2 preamble).

### 4.6 Worker tiering — by proof-shape novelty, not task prestige

New proof shapes, fidelity/envelope arguments, and semantics work run
on Fable; replication, mechanical build-out, and verification may run
Opus; pre-merge audit reviewers Opus-class (CLAUDE.md; gallery lesson
13 — the one mis-tier came from labeling by harness style rather than
proof novelty; model rules encode the 2026-08 landscape and are
revisited on new releases, not applied blindly).

---

## §5 The Latitude — everything else is the campaign's

Inside §2's ends and §3/§4's rails, the campaign decides — without
asking, and with judgment-call logging as the accountability
instrument (one-line entries in the campaign log; reviewed after, not
approved before — "comprehension check ≠ sign-off"). Explicitly
delegated:

- **Proof strategy and route**: direct invariant proofs over the
  interpreter, a Verdi-refinement bridge or its abandonment, Iris as
  proof device, ghost/history machinery behind the statement line —
  any mix, revisable mid-campaign with the reasons logged.
- **Invariant ordering and the lemma architecture**: which invariants
  first, how the lattice decomposes, what is general infrastructure
  vs target infrastructure (subject to the layering doctrine's
  direction rule).
- **Tooling investment**: kit extensions, tactic development, Sym/POR
  accelerator work, tracer tooling — WHEN grind appears, invest (§6a;
  the promotion-ledger rule: patterns with ≥2 consumers get lifted
  into lemmas/tactics on a consolidation slice, and worker briefs
  carry an active promotion ledger).
- **Staging and parallelism**: lanes, waves, sub-branches, park/resume
  scheduling — inside §4.3's ownership rules.
- **Corpus and probe design**: new guardrail cases, gc probes,
  differential batteries — guardrails-first, always.
- **When to park**: any unit, with a resume condition recorded (§6k).
- **Subordinate charters**: the campaign writes its own arc charters
  in the standing form when enumerable work appears; each names its
  user gates and inherits this document.

The one instrument the latitude rests on: **log the call, keep
going.** A judgment call that would surprise Mike on review was
probably a ruling request (§3.4) — the test is whether it changes what
a theorem MEANS (ruling) or how it gets proved (call).

---

## §6 Advice for the road

Maxims earned here, each with its provenance. They are advisory —
the inviolables are §3 — but every one of them was paid for.

- **(a) A long grind against a goal means you're missing a tactic.**
  Stop and lift the pattern; leverage-vs-grind is also performance.
  *The WP arc's promotion ledger and the brick-wp lesson: closing six
  kit gaps cut every successor ~25% and made two units one-session
  jobs (`docs/2026-08-15_brick-wp-promotion-wave-mapping.md`; gallery
  trip report §4).*
- **(b) A stuck or exploding proof often means a FALSE goal — `#eval`
  before you `decide`.** A decision procedure that must reduce to
  `False` has no reason to terminate politely. *The 60 GB
  `decide +kernel` that killed two sessions was a fuel bug making the
  proposition false; fixed, the same line checks in 1.2 s (CLAUDE.md,
  capped-builds section).*
- **(c) When the proof is ugly, suspect the definition.** GoCore is
  reshapeable, not sacrosanct; a semantics that fights the proof is a
  finding about the semantics. *CLAUDE.md's design principle; the
  W3.2 semantics design audit's Cont findings — `contAfterStmtOp`'s
  global continuation walks and the Q4/Q6 refactor queue
  (`docs/2026-08-20_semantics-design-audit.md`, w32 lane —
  branch-state at drafting).*
- **(d) A law without a witness is a scaffold.** Say so in its
  docstring or ship the witness. *`wp_assign` shipped vacuous, was
  caught, and nearly re-shipped as `wp_deref_store` (CLAUDE.md,
  non-vacuity gate).*
- **(e) A theorem wanting a narrower machine is posing a ruling.**
  Write the ruling request; expect "no". *The BUG-005 struck
  narrowings: both proposed termination-buying pins refused —
  "any latitude in the Go spec should be supported"
  (`docs/2026-08-19_bug005-map-range-memo.md` §5, Q2).*
- **(f) Predict your flips before you run.** Name the ids that should
  move, the ids that must NOT, and the controls; then run. *The
  BUG-005 memo's "flips, all predicted" table; the gallery C1 fix —
  7 RED witnesses + 4 passing controls, then exactly 7 flips (trip
  report, closure-quarantine finding).*
- **(g) A differential red is not automatically yours.** Attribute
  before you fix; sometimes the oracle's implementation is the bug.
  *L-014, gc's optimized constant fold truncating to 32 bits
  (`docs/spec-divergence-ledger.md` L-014); grossmith campaign 2's
  three gc-attributed cases (`docs/2026-08-20_grossmith-findings-2.md`).*
- **(h) Green is not correctness — the failing-set diff is.** A green
  build proves elaboration; the baseline diff is the regression
  signal, and NO recorded run is a FAIL, not a skip. *CLAUDE.md, the
  validation gate — it kept 13 consecutive cleanup slices at zero
  regressions.*
- **(i) Summary layers are where drift lives.** Worker claims held;
  the false numbers were in indexes, totals tables, and retrospectives
  — restated, never recomputed. *Gallery trip report lesson 15 and
  its own five named false claims; re-confirmed by every records
  audit since.*
- **(j) One reshape, not two — consume refactor queues during
  surgery.** A finding whose fix rides an already-open boundary change
  costs its blast radius once. *The W3.2 slice 0→1 design: the audit's
  graded refactor queue consumed during the slice-1 surgery
  (`docs/2026-08-20_w32-re-envelope-charter.md`, slice 0).*
- **(k) Park with a resume condition, never merge from sunk cost.**
  ~14.5k lines of channel-logic machinery parked awaiting the
  re-envelope; the salvage plan salvages the families, not the tip's
  refuted claim. *`docs/2026-08-10_channel-logic-arc-charter.md`
  (tail: ARC PARKED); the W3.2 charter's S6c resume-readiness
  assessment.*
- **(l) Fresh probes over inherited records.** "The worker reported
  it" is not a source; neither is "it follows from how the machine
  works." *The matmul withdrawal: a shard and gallery entry pinned
  axioms no build had ever evaluated — written in good faith, both
  withdrawn (`docs/gallery-campaign-log/g1.md`, the three claim
  corrections).*

Four more, added by this drafting from the records read — each earned
in this campaign's own runway:

- **(m) An invariant nobody exercised is a vacuous green — carry an
  exercise floor.** A cluster that never elects anyone satisfies
  election safety trivially; a completion witness that achieves
  nothing is forgery-by-deadlock. *`raftharness/`'s
  EXERCISE FLOOR SHORTFALL verdict class; machine-twin design §4;
  P0 §3.1.*
- **(n) A fix that restores a saved flag owes a walk of every READER
  of that flag, in both directions** — not only the readers whose
  symptom was reported. *The gallery C1 defect: the same missing
  save/restore over-refused in one direction and silently disabled
  the E6 fail-closed guard in the other; the second direction
  survived the audit, the fix, and the first report (trip report,
  post-autonomy addendum).*
- **(o) Write DONE criteria fail-closed — enumerate what a green run
  cannot show you.** "Zero live quarantined declarations" passed
  three classes of fail-closed stop straight through; the honest
  criterion lists the classes by name. *The machine-twin design §8,
  W4.1's done-criterion rewrite: "Classes (2)–(5) are exactly the
  ones a green run would not have shown you."*
- **(p) A ruling left in chat is a ruling that rots.** Record rulings
  in dated blocks in the governing file, then fold them into the work
  they govern; one copy of a moving ruling, cross-referenced, never
  two. *The W3.2 charter's Rulings block, stating exactly this;
  CLAUDE.md's capture-decisions rule.*

---

## §7 Relationship to standing doctrine

This constitution SPECIALIZES the standing doctrine for one campaign;
it never overrides it. Concretely:

- CLAUDE.md, the essence-of-Go doctrine and its two bounds, the
  nondeterminism doctrine, the TCB/layering doctrine, the latitude
  inventory and spec-interpretations index, the merge protocol, and
  the worktree/long-cycle disciplines all bind exactly as written.
- **Conflicts resolve toward the stricter rule.** If this document
  and standing doctrine ever appear to disagree, the reading that
  constrains the campaign more is the operative one, and the
  discrepancy is reported to Mike as a probable drafting defect.
- **Amendments to shared doctrine go through their own processes** —
  CLAUDE.md through its own amendment practice, ledgers through their
  curation, the inventory through its census discipline. The campaign
  proposes; it never edits shared doctrine as a side effect of proof
  work.
- Subordinate arc charters inherit both this document and standing
  doctrine; where they add named gates, those gates are real (§4.1).

---

## §8 The sign-off questions — every [MIKE] hole, collected

Ratification = answers to these, recorded as dated rulings in §2/§4
(per §4.5's amendment form). Defaults are stated where the drafting
has a recommendation; "approve with defaults" is a legitimate single
answer, per the W3.2 precedent.

1. **The base predicate** (§2.1): Agreement — S1–S3 as the per-step
   executable invariant, S4 as completion witness — confirmed as the
   campaign's base end? (P0 §8.1 recommended it; never ruled.)
   *Default: yes.*
2. **The tier ladder** (§2.3): confirm T1→T2→T3→T4 and rule which of
   T3's invariants (leader completeness, log matching, state-machine
   safety) are HEADLINE ends vs infrastructure; confirm T4
   linearizability as stretch. (P0 §8.2.) *Default: T1–T2 ends; T3
   headline as proved; T4 stretch.*
3. **The network envelope tier** (§2.2.1): reliable-first for the
   pinned statement, chaos as a strengthening tier. (P0 §8.3.)
   *Default: yes.*
4. **The RawNode serialization narrowing** (§2.2.2): accepted as v1
   fine print with its recorded re-envelope obligation, or must the
   widened `harvest` event precede the pin? *Default: accept at v1;
   obligation stands.*
5. **The liveness tier** (§2.4): inside this campaign's ends, or a
   named successor? *Default: successor; the non-preclusion
   requirement keeps it reachable.*
6. **The milestone set for audit cadence** (§4.2): each §2.3 tier, the
   statement pin, and any semantic-core surgery. *Default: as
   proposed.*
7. **Supervision seam**: does any remaining trust-surface work
   (semantic-core surgery the proofs demand, statement re-pins) stay
   under supervised arcs while proof work runs long-cycle, or is the
   whole campaign one autonomous envelope with §4.1's gates? (The
   P0 §8.5 question, now campaign-shaped.) *Default: trust-surface
   work supervised; proof work autonomous.*
8. **Ratification itself** (§4.5): this document as the campaign's
   governing instrument, amendment authority as stated.

---

*Drafted 2026-08-21 on the `proof-constitution` lane (docs-only) from:
the raft master plan and P0 scoping doc, the machine-twin harness
design, the gallery campaign trip report, the W3.2 re-envelope charter
and its lane's design-audit/boundary-set/POR notes (branch-state where
marked), the TCB/layering doctrine, and CLAUDE.md's standing
contracts. Every provenance pointer above was resolved against the
tree at drafting time.*
