# ARCHIVE — branch index

Main is the SEMANTICS product only (the repo split, 2026-08-31 —
`docs/2026-08-31_repo-split-plan.md`). The branches below carry
everything else this repo has produced. **They are NOT local branches
in a fresh clone** (the 2026-10-11 migration to this box cloned the
pushed set): what resolves where is the table below; use the
`origin/<name>` spelling (or `git switch <name>`, which creates a local
tracking branch) for a branch, the tag name for a tag.

**What resolves where** (verified 2026-10-12 on the `milner-oath` clone of
`OathTech/golean` with `git branch -r`, `git tag`, `git show-ref`,
`git for-each-ref refs/snapshots`; [AGENT] records lane
`docs/release-records-1012`, release-readiness item 12; origin itself not
re-queried — no network from the sandbox — so «on origin» means «fetched
with the clone», the tags read from the clone's `packed-refs`):

| name below | local branch | `origin/*` remote-tracking ref | tag | resolves to |
|---|---|---|---|---|
| `park/reasoning-2026-08-31` | no | yes | — | `7440bf70` |
| `raft-proof-campaign` | no | yes | — | `17197113` |
| `typed-consumer-sprint` | no | yes | — | `7edc298f` |
| `typed-uintptr-identity` (the HELD L5 source) | no | yes | — | `5f185fb3` |
| `park/typed-profiles-2026-09-16` | no | **NO — not on origin** | `typed-profiles/last-main-2026-09-16` (annotated, in the clone) | `62fc8073` via the tag only |
| `archive/callspec-era` | no | yes | — | `20cda772` |
| `archive/fixed-trajectory-era` | no | yes | — | `c4986b29` |
| `snapshot/typed-sprint-before-uintptr-20260906` | no | no | — | does NOT resolve (same tip as `origin/typed-consumer-sprint`, `7edc298f`) |
| `refs/snapshots/*` (e.g. `pre-repo-split-main`) | — | — | — | EMPTY on this clone (`pre-repo-split-main` = `7440bf70` = `origin/park/reasoning-2026-08-31`) |
| (the offer) | — | — | `logic-offer/2026-10-03` | `20d3946d` |
| `park/relational-prototype-2026-10-15` (design donor, below) | yes | **NO — not on origin** | — | `701d8689` |
| `park/relational-prototype-rendering-2026-10-15` (design donor) | yes | **NO — not on origin** | — | `95b0b64b` |
| `park/relational-spike-concurrency-2026-10-15` (design donor) | yes | **NO — not on origin** | — | `f6f37e36` |
| `park/relational-spike-detector-contracts-2026-10-15` (design donor) | yes | **NO — not on origin** | — | `b4282cff` |
| `park/relational-spike-unseq-2026-10-15` (design donor) | yes | **NO — not on origin** | — | `ce0daf9f` |
| (the last main carrying the relation) | — | — | `relational/last-main-2026-10-20` (annotated, local; not pushed) | `89b1fce1` |

Rows from `park/relational-*` down were added 2026-10-20 ([AGENT] lane
`records/archive-library-1020`, read with `git branch`, `git branch -r`,
`git cat-file -t`, `git rev-parse` on this clone; origin still not
re-queried). The 2026-10-12 «EMPTY» verdict on `refs/snapshots/*` predates
the relational line: the local-only relational-era refs under
`refs/snapshots/`, `refs/integration/` and `refs/checkpoints/` are listed in
the design-donors section below.

Also on origin, not indexed below (older lane branches, kept as found):
`campaign-arc4d`, `campaign-ce`, `campaign-wave-a` (2026-08-26),
`channel-logic`, `channel-logic-s4` (2026-08-11; cited by
`docs/2026-08-04_nondeterminism-doctrine.md`), `design-pass` (2026-08-28).

**PENDING [USER] (release-readiness backlog D4):** push
`park/typed-profiles-2026-09-16` to origin, or leave it tag-only (the tag
already names the same commit; nothing is lost either way). Until ruled,
revive from the tag.

For a source-checked survey of the reasoning branches, newer Iris spikes,
uncommitted worktree material and stashes, see
[Reasoning archaeology and revival proposal](2026-09-16_reasoning-archaeology.md)
([AGENT], 2026-09-16). It distinguishes historical claims from current
artifacts and proposes a reasoning repository plus a Raft repository with
independent Verdi and etcd-proof packages.

- **`park/reasoning-2026-08-31`** — the entire reasoning product at
  its last everything-together state (main `7440bf70`, the Iris
  corpus era's phase-A tip, all gates green): the `proofs/` package
  (Iris layer, relational instances, Audit + 51 designated
  theorems, Challenge/Solution), `compat/` (verdi, gobra), the
  comparator-judge and A-TRIP gate apparatus, and the proof-era
  docs including that era's own ARCHIVE.md (which indexes the
  history below in full). Pending migration to a separate repo —
  the how-to-resume guide is `docs/2026-08-31_reasoning-revival-guide.md`.
- **`raft-proof-campaign`** — the unmerged campaign decision log
  (reasoning-side; lands or migrates at the migration stage).
- **`typed-consumer-sprint`** @ `7edc298f` — the typed-consumer
  sprint's FULL history and evidence payload (96 commits over main
  `47195683`, 2026-09-05..06: the typed Boolean/recovery contracts, the
  Iris customer facade, the observer/crash-channel apparatus, the
  string-member lane, and 2,159 files / ~114 MB under `docs/evidence/`,
  incl. 36 `.tar.gz` and 345 exact copies of tracked files). Retained
  UNMODIFIED as the archive; nothing from it is merged as-is. The work
  lands in reviewed chunks per
  `docs/2026-09-07_typed-sprint-landing-plan.md`, each squashed from
  this branch by path selection and crediting its commits by SHA.
  Reason — [USER] ruling (Mike, 2026-09-07, as relayed by the
  [AGENT] coordinator — cite as relayed): the evidence blob does not
  land, big evidence bundles are not dumped on main (they cannot be
  hosted on GitHub), and the work is to be landed cleanly by a plan,
  decomposed into reviewable chunks, with some of the issues (the
  choice tape among them) fixed where appropriate. The two landing audits that
  found the payload and the semantic blockers are landed by the plan's
  L6 chunk as `docs/2026-09-07_landing-audit-{A,B}.md`. Snapshot ref
  `snapshot/typed-sprint-before-uintptr-20260906` names the same tip.
  **MANIFEST of the payload (L6, 2026-09-07):**
  `docs/evidence/2026-09-05_typed-consumer-sprint/` — `MANIFEST.tsv` (one
  row per source dir) + `manifest/<dir>.tsv` (one row per file: path,
  sha256, bytes, origin commit, class) + `source-copies.tsv`; 2,159 files
  / 114,156,315 B / 78 dirs, none on main. The sprint's outcome and
  corrected ledger: `docs/2026-09-05_typed-consumer-sprint-handoff.md`;
  roadmap disposition: `docs/2026-09-05_master-plan.md` §7.8. Landed in
  rounds 20–24 (L1 `f70ea4bf`, L2 `74245e1d`+`90bc3e06`, L4
  `60bbf466`+`dd636996`, L3 `a6a068ce`+`25c665b7`+`29f77b43`, L6); L5
  `uintptr` HELD.
  The staged, uncommitted `uintptr` merge in the sprint worktree is NOT
  part of this archive (its source is branch `typed-uintptr-identity`
  @ `5f185fb3`; plan §2.5, HELD). [AGENT] `landing-plan-0907`,
  2026-09-07.
- **`park/typed-profiles-2026-09-16`** (NOT on origin — the tag is the only ref on this clone; D4 above) = tag **`typed-profiles/last-main-2026-09-16`**
  = main `62fc80731f0045c170634690bda1c26d1880f185` (2026-09-16) — the
  typed-admission profile family at its LAST main state before parking:
  `GoLean/GoCore/Boolean*.lean` + `Recovery*.lean` (56 modules, 8,197
  lines), the facade `GoLean/Interface.lean`, their nine `Tests` libraries
  (24 modules), fixtures, gate scripts and audit tools; and the dark spikes `spikes/gate-a1` and
  `spikes/iris-customer`, deleted by the lane's SEPARATE D7 commit
  (PENDING [USER] at the merge ask; one revert restores them). Deleted from main by lane
  `park-lane/typed-profiles-0916`; the note (inventory, what was re-homed,
  what stayed, how to revive) is `docs/2026-09-16_typed-profiles-parked.md`.
  Future home per the [USER] ruling of 2026-09-16 (relayed; recorded in the
  note): the reasoning repository under gitignored `deps/` (name
  provisional — «golean-reasoning»; the survey's `deps/reasoning-revival/
  golean-logic/`), consuming golean PINNED at that SHA. Revive with
  `git checkout typed-profiles/last-main-2026-09-16 -- <paths>`.
- **raft-proofs** (not a ref here) — the reasoning-side raft proof
  repository (its own git repo, remote `OathTech/raft-proofs`; imports
  nothing from GoLean). It lived at the gitignored
  `deps/reasoning-revival/raft-proofs` during the migration; MOVED
  2026-09-27 to `~/projects/raft-proofs` ([USER] Mike, 2026-09-27,
  directed; the move and its `git worktree repair` [AGENT]). Paths of
  the form `golean/deps/reasoning-revival/raft-proofs/…` in either
  repo's older docs and provenance are historical and now resolve under
  `~/projects/raft-proofs/`; its tools still take golean's `deps/`
  reference checkouts (raft, verdi-raft, opam-coq818) by explicit path.
- **`archive/callspec-era`** — the killed CallSpec judgment track
  (2026-08-27 triage).
- **`archive/fixed-trajectory-era`** — the killed enumeration-era
  corpus (2026-08-27 W0 reset).
- Snapshot refs under `refs/snapshots/` — pre-operation safety
  copies (`pre-repo-split-main` = `7440bf70`). Local-only by nature:
  none is on this clone (table above); `7440bf70` survives as
  `origin/park/reasoning-2026-08-31`.

Older pipeline-history notes for the SEMANTICS product live in
`docs/archive/` (a directory, unrelated to these branches).

## Design donors (retired 2026-10-20): the relational line

[USER] ruling, 2026-10-20 (relayed by the [AGENT] coordinator; paraphrased):
the relational line of work is retired. Its intended consumer does not use it
and it presents a misleading target. Its pieces are kept as DESIGN DONORS for
other agents, on parked branches with clear names, and indexed here: what is
available where, in what state, and that none of it is intended for use.
Checked 2026-10-20 ([AGENT]): the logic repository (`~/projects/golean-logic`)
pins this repo at `fa343e48` (main, 2026-10-06) and its own note
`docs/2026-10-13_note-to-golean-mirror-properties.md` states that its step
relation is GoLean's executable step (`StepAdapter.run`, i.e. `stepFn`), so
its trust path never passed through the relation `Step`.

Same ruling, later the same day (relayed; paraphrased): `GoLean/GoCore/Prefix.lean`
(`Prefix`/`Finish`, the iterated-`stepFn` prefix closure) and
`GoLean/GoCore/Equations.lean` (the `@[stepFn_eqns]` rewrite library, with
`EquationsAttr.lean` and the `scripts/check-equations` gate) are NOT retired.
They stay on main under stable names as a supported surface for the raft-proofs
customer (`~/projects/raft-proofs`), which states its theorem over
`Prefix`/`Finish` and evaluates symbolically with `stepFn_eqns`. They are not
donors and have no entry below. Note that the tag's own message (written before
that clarification) names the Equations library among the retired set; the
ruling above corrects it, the tag itself stands.

Common to every donor: **not for use and not maintained**. Toolchain
`leanprover/lean4:v4.32.2` at every tip and at the tag (each tip's
`lean-toolchain`). Every branch tip is dated 2026-10-15 and was parked under
its `park/relational-*` name on 2026-10-20 with the tip unchanged; none of the
five branches is on origin; the push, if any, is the owner's. Read a branch
with `git show <branch>:<path>` and `git log <branch>`; each entry gives a
revive command. Every fact below was read from the named branch, tag or
record on 2026-10-20 ([AGENT] lane `records/archive-library-1020`); the gate
claims are the records' own, bound to the commit each record names, and the
corpus counts in them (3,989 or 4,025 rows) are those of the corpus at that
commit.

The round vocabulary used below, as the records use it: the laws batch (the
first three laws the logic demo asked for), RD3 (call/return), RD4 (store
phases), RD5 A–D and E/F (composition and residuals), C1 (bounded local
outcomes), C2 (all-outcome sequential programs), RD6 (the C2 consumer
corollary), RD7 (logic-side only), D1 (detector contracts), O1 (boundary
events and histories), U1 (restricted unseq sequentialization), I1 and I2
(integrations), RD8 (the observed-phase refinements).

### Donor 1 — the mainline relation and its coherence proofs

- **What it is.** The Prop-level transition relation `Step` of GoCore and
  everything proved about it on main: the per-step coherence with the
  interpreter in both directions, the run/trace/observation soundness, the
  setup half, the multi-goroutine and pool halves with their frozen statement
  set, and the pinned bridge set. Built 2026-09 to 2026-10 for the logic
  repository as the charter's second deliverable (a fuel-free relational
  semantics proved equivalent, per step, to the operational one); that charter
  claim is being rewritten by the retirement lane, not here.
- **Where.** Tag **`relational/last-main-2026-10-20`** (annotated, local, not
  pushed) = main **`89b1fce1`** (last commit 2026-10-16; tagged 2026-10-20): the
  last main carrying these modules before the separate lane
  `core/retire-relation-1020` removes them from the build. Base: main itself.
- **Modules at the tag** (`GoLean/GoCore/`, line counts at the tag; the import
  graph puts all of them downstream of `Step`): the `Step` inductive in
  `Machine.lean` (from line 6524 of 7,983; the file also holds the configuration
  and continuation definitions the interpreter uses, so only its relation half
  is a donor); `MachineSound.lean` (7,795) with the two headline theorems
  **`stepFn_sound`** (line 1904: every executable step is a relation step) and
  **`step_complete`** (line 2339: every relation step is realised by the
  executable under some stream), plus `runConfig_sound` and `stepFnIter_sound`
  (run-level soundness only; the run-level converse is recorded there as not
  built); `Trace`, `ProgramTrace`, `ExecutionStatement` (467), `PrefixFacts`
  (576), `StepErrors` (879); the setup half `SetupStatement` (566), `SetupSound`
  (1,109); the multi half `MultiSound` (1,741), `MultiWfSound` (1,266),
  `MultiStreams` (1,427), `NPDRF` (546), `UnseqSound` (236); the pool half
  `PoolStep` (364; the labelled relation `StepML`), `PoolStatement` (560; the 48
  frozen `_stmt` definitions), `PoolSound` (1,482; the 48 discharges, among them
  `stepML_sound`, `stepML_complete`, `pool_classification`, `singleton_run`),
  `PoolStructure`, `PoolTrace`, `PoolErrorFacts`, `PoolFrontFacts`,
  `PoolReplayFacts`, `PoolSingletonFacts`, `PoolProjection` (569; the
  single-goroutine reduction); and `BridgeSet.lean` (4,603; 605 pinned
  statements, one `example` each). Together 24 proof/statement modules of
  25,070 lines beside `Step` itself. The pool half's freeze lives in
  `docs/specs/pool-relation/` (`FROZEN.sha256`, `MILESTONES`, `LANDED` = M5,
  `REPAIRS.md`) and is checked by `scripts/check-pool-spec` (a `scripts/ci`
  speedbump). Downstream of these also sit `EnumDedupCheck`, `EnumDedupSound`
  and `MachineEqb` (the enumeration dedup check). Three of the modules listed
  (`ExecutionStatement`, `PrefixFacts`, `StepErrors`) are imports of the live
  `Prefix.lean`: whether they stay is the retirement lane's call, recorded in
  its commit, which is the authority on the exact set removed.
- **State reached.** On main, so merged under the merge protocol's full gate
  at each runtime-touching train since it landed (the pool half by train r70,
  2026-10-06, the charter's own account); at the tag the fast tier of
  `scripts/ci` builds it warning-free and the escape-hatch scan (no `sorry`,
  `admit`, `native_decide` or `axiom` under `GoLean/`; no `unsafe`, `opaque`,
  `implemented_by`, `extern`; no `partial` in the core) and the core totality
  audit cover it: `scripts/check-core-audit` (via `Tests/GoCoreAudit.lean`)
  imports every `GoLean/` module, checks that every local declaration depends
  on the classical trio only (the headline theorems included) and requires a
  core-theorem list that names, among others, `stepML_sound` and
  `stepML_complete`; `stepFn_sound` and `step_complete` are pinned by type in
  `BridgeSet.lean`. This lane's fast-tier run at the tag's tree (docs-only
  changes), 2026-10-21: PASS, 90 s, 68 modules replayed. No open findings
  against it: it is retired for lack of a consumer, not for a defect.
- **Reusable; not to be trusted for.** Reusable: the design of a labelled
  relation whose label is the executable's own event, the per-step two-way
  coherence proof pattern, the frozen-statement discipline of the pool half,
  and the pinned bridge set as a catalogue of statement shapes. Do not rely on
  it as a claim about main: the retirement lane rewrites the charter, the
  semantics overview and the release document, and after it lands these
  modules are not in the build. The run-level converse («every relational run
  is some tape's prefix») is FALSE as a bare statement (charter, 2026-10-06).
- **Revive.** `git worktree add --detach .claude/worktrees/relational-last-main relational/last-main-2026-10-20`
  (then `cp -a .lake` from a primary that still has the modules built, or
  `capped lake build`). Toolchain v4.32.2. Not for use; not maintained.

### Donor 2 — the lifting-theorem library (relational laws and composition rounds)

- **What it is.** The half-built library that lifts machine steps to
  relation-level, source-construct statements: read, splice, assignment, call
  and phase laws, built round by round against frozen request packages from the
  logic repository (each round's exact requested propositions were discharged
  by direct theorem assignment and independently audited). It is the part of
  the prototype a reader is most likely to mine.
- **Where.** On branch **`park/relational-prototype-2026-10-15`** (Donor 3; the
  same modules are also at earlier states on the two old-line spikes, Donors
  5–6). The modules, all under `GoLean/GoCore/` at tip `701d8689` and exported
  through the facade `GoLean/Relational.lean` (namespace
  `GoLean.GoCore.Relational`):
  `RelationalControl.lean` (`Pure`, `read_variable`, `conditional`,
  `sequence_splice`, `block_enter`, `empty_sequence_run`),
  `RelationalAssignment.lean` (`assign_pointer_variables`),
  `RelationalCall.lean` (`reference`, `assign_variable`, `return_start`,
  `return_sequence`, `SavedCaller.enter`, `CallBoundary.deliver`,
  `SavedCaller.invoke`), `RelationalStorePath.lean` and `RelationalPhases.lean`
  (`StorePath`, `StoreEffect`, `OperandPaths`; `pointer_assignment_phases`,
  `variable_assignment_phases`, `SavedCaller.entry_phases`,
  `variable_expression_phases`, `pointer_rhs_phases`),
  `RelationalDelivery.lean` (`OrderedWrites`, `CallBoundary.delivery_phases`),
  `RelationalExpression.lean` (`ReadOnlyExpr` with `.variable`, `.reference`,
  `.int_literal`, `.deref`, `.add_int`, `.less_int`), `RelationalLoop.lean`
  (`WhileControl`, `while_control`), `RelationalMemory.lean` (`write_support`,
  `allocate`, `write_read_root`, `root_writes_commute`),
  `RelationalLocality.lean` (`loadLoc_agrees`, `write_preserves_load`), and the
  RD8 observed variants `RelationalObservedPath.lean`,
  `RelationalObservedPhases.lean`, `RelationalObservedDelivery.lean` (the same
  phase laws carrying an empty-boundary-event policy at every traversed
  source). The living catalogue with each export's stated scope is
  `docs/relational-interface.md` on the branch (§ Checked contracts).
- **Rounds, records and audits** (all `docs/` on the branch; each audit names
  the commit it is bound to): the laws batch — `2026-10-14_relational-demo-laws.md`,
  audit `2026-10-14-relational-laws-independent-audit.md`; RD3 —
  `2026-10-14_relational-call-acceptance.md`, `2026-10-14-rd3-independent-audit.md`;
  RD4 — `2026-10-14_relational-phase-acceptance.md`,
  `2026-10-14-rd4-independent-audit.md`; RD5 A–D —
  `2026-10-14_relational-composition-acceptance.md`,
  `2026-10-14-rd5-independent-audit.md`; RD5 E/F —
  `2026-10-14-rd5-residual-independent-audit.md`; RD8 observed phases —
  `2026-10-15_relational-observed-phases-stage.md`,
  `2026-10-15_relational-observed-phases-review.md`. Each audit found no
  correctness defect in its batch. CAUTION on hashes: the records up to RD5
  E/F cite the pre-rebase commits of the old line (`b25a47ef`, `95f1eb64`,
  `67f7d1c5`, `f224a6e0`, `fc52512a`), which are NOT on the prototype branch
  (its history was rebased at I1); they resolve through Donors 5–6 and the
  `refs/integration/i1/*` refs listed at the end of this section.
- **What is proved, and what was left open.** Proved: the laws above, each
  with actual labels retained (no observation-silence promise), pick-free
  steps where stated, symbolic stores/locations/continuations, aliasing and
  interior targets admitted, intermediate-store preservation and source
  admission on every traversed step (RD4 onward). Left open, as the interface
  doc and the audits state: assignment through general address-former chains
  and operators beyond `+`/`<` on integers; method calls, pending defers and
  abstract caller-target/dispatch contracts; a complete entry-site census
  beyond the seven sequential call/defer sites; general observation silence
  (only byte-output silence is proved); choiceful all-behaviour safety (the
  progress result `PickFreeProgress` is the pick-free fragment); whole-step
  locality, context extension and address renaming; `unseq` beyond Donor 7's
  restricted domain; any concurrent transport; infinite runs and fairness.
- **Reusable; not to be trusted for.** Reusable: the statement shapes (uniform
  store-preserving paths, effect-then-cleanup decomposition, snapshot-before-
  ordered-writes delivery, activation-derived result-slot validity). Not to be
  trusted: as laws about main (the facade and these modules were never on
  main), nor as a complete calculus; the consumer packages they were accepted
  against are frozen private copies in the logic repository and in
  `experiments/` on the branch, at logic pins the records name.
- **Revive.** Same command as Donor 3. Not for use; not maintained.

### Donor 3 — the prototype relational layer

- **What it is.** The 2026-10-13 refactor that replaced the Equations-style
  executable API with a labelled relational surface of its own: a direct
  closure of `Step` with no tape or evaluator in the carrier (`Transition`,
  `Run`), exact finite realisation and determinism by pick records
  (`RelationalSound`), terminal boundaries and complete bounded local
  outcomes (C1: `RelationalOutcome*`, `RelationalOperationCheck`,
  `RelationalOperationFailure*`, `RelationalLocalExecution*`), all-outcome
  sequential program correspondence (C2: `RelationalProgram`,
  `RelationalProgramOutcome*`), entry/readback (`RelationalEntry`),
  initialization (`RelationalPhase*`), boundary events and finite histories
  (O1: `RelationalEvent*`, `RelationalHistory`, `RelationalObservation`), the
  absorbed U1 unseq modules and D1 detector contracts (Donors 6–7), and the
  laws of Donor 2. Design authority and first-cut disposition of the logic
  team's P1–P13 request: `docs/2026-10-13_relational-surface-refactor.md`;
  living interface: `docs/relational-interface.md` (both on the branch).
- **Where.** Branch **`park/relational-prototype-2026-10-15`**, tip
  **`701d8689`** (2026-10-15, a documentation-only handoff; implementation pin
  `82353580`), 33 commits over main `31a6069d` (2026-10-14; the base is also
  `refs/integration/i1/main`). Not on origin.
- **Content versus its base** (`git diff --name-status 31a6069d 701d8689`):
  46 new modules under `GoLean/GoCore/` (7,491 lines: the 43 `Relational*`
  modules plus `LocationOrder`, `ShadowOrder`, `ShadowHistory`), the facade
  `GoLean/Relational.lean`, four clients `Tests/Relational{Contracts,Observations,Outcomes,ProgramOutcomes}.lean`,
  private acceptance packages under `experiments/` (concurrency-compatibility,
  program-outcomes, observation-compatibility, unseq-compatibility, unseq-rd8,
  o1-u1-integration, observed-phases), 32 dated records and the living
  `docs/relational-interface.md`. It MODIFIES
  `BridgeSet.lean` (the Equations rows retired), `MachineSound.lean`, `Ops.lean`
  (the `Loc` comparator moved to `LocationOrder`), `SetupSound.lean`,
  `SetupStatement.lean`, `GoLean.lean`, `lakefile.toml`, `scripts/ci` and
  `scripts/mem-callsites.tsv`; and it DELETES `GoLean/GoCore/Equations.lean`,
  `EquationsAttr.lean`, `Tests/EquationClient.lean` and
  `scripts/check-equations` — the surface that the 2026-10-20 ruling keeps
  live on main. A revived prototype therefore conflicts with main's supported
  surface by construction.
- **Rounds on this branch** (implementation commit; records): first cut
  `0d8dc57e` (adversarial review `2026-10-14_relational-surface-adversarial-review.md`,
  bound to old-line `d30107b2`); laws `609456fa`; RD3 `db193fe1`; RD4
  `d154218d`; RD5 `a6ae2d69` + `a954f7bb`; C1 `05c7c4f7`..`e56eea88`
  (`2026-10-14_relational-outcome-completeness.md`,
  `2026-10-15-c1-independent-audit.md`, bound to old-line `55ad7249`); C2
  `a9200dc5`..`15adb708` (`2026-10-15_relational-program-outcomes.md`,
  `2026-10-15-c2-independent-audit.md`, bound to old-line `fcebf85c`); RD6
  `513566d2` (`2026-10-15-c2-consumer-audit.md`,
  `2026-10-15-c2-consumer-reproduction.md`, bound to old-line `626faca5`); I1
  `5d8e53e9` (`2026-10-15_relational-integration-stage.md`,
  `2026-10-15-relational-integration-review.md`,
  `2026-10-15-relational-integration-reproduction.md`); O1 `56168ed5`
  (`2026-10-15_relational-observation-stage.md`,
  `2026-10-15-relational-observation-review.md`); I2 `4731d491`
  (`2026-10-15_relational-o1-u1-integration-stage.md`, `-review.md`); RD8
  observed phases `82353580` (`2026-10-15_relational-observed-phases-stage.md`,
  `-review.md`). The absorbed spikes' records are carried too
  (`2026-10-14_relational-concurrency-compatibility.md`,
  `2026-10-15_relational-concurrency-review.md`,
  `2026-10-15_relational-detector-contracts.md`,
  `2026-10-15_relational-detector-review.md`,
  `2026-10-15_relational-unseq-stage.md`, `2026-10-15_relational-unseq-review.md`).
- **Gate state** (the records' own claims). At the tip's implementation pin
  `82353580`: full `scripts/ci --diff` PASS, 902 s, 113 GoLean modules
  kernel-replayed, 396 eval tests, fresh differential 4,025 rows (3,767 PASS /
  258 tracked FAIL, no baseline regression), fresh negative 415/415; run on a
  dirty worktree, with the reviewer binding all 4,398 source/configuration
  hashes to the commit; one speedbump (the memory call-site inventory) was red
  on the first run and repaired in the same commit. Earlier full runs on the
  same line: I1 `5d8e53e9` PASS 1,233 s, I2 `4731d491` PASS 1,394 s (same row
  counts). Its own core-audit statements print the classical trio only.
- **Audit state.** Every round has an independent review on the branch (list
  above); none found a semantic defect in the bounded increment it reviewed,
  and none approved a landing. Standing, open and unwaived at the tip:
  the implementation scan reports **21 findings** — 16 upstream partial
  `_unsafe_rec` implementations behind derived instances (two generated
  syntax-equality implementations, five core/seed renderers, nine declaration
  renderers; the authoritative per-declaration table is in
  `2026-10-15_relational-integration-stage.md`) plus five in the frozen logic
  package; the four Source-renderer correspondences; and the logic side's
  live «35 NOT-PUBLIC» failure, never rerun here. The first adversarial review's
  verdict (ready for a small demo, not for replacing the logic's adapter or
  adequacy roots) was never superseded by a landing verdict: the interface doc
  itself says the full-replacement target was not established.
- **Reusable; not to be trusted for.** Reusable: the carrier design
  (relation closure without tape or evaluator; determinism by pick records;
  semantic failure checks composed from the machine's own guards; phase
  carriers that keep initialization and body budgets separate). Not to be
  trusted: anything about main's build (none of it was ever on main), the
  21 findings above, and the P1–P13 table in the design doc, whose «remaining»
  column was never closed.
- **Revive.** `git worktree add .claude/worktrees/relational-prototype park/relational-prototype-2026-10-15`;
  toolchain v4.32.2; expect a cold build (main's `.lake` does not contain
  these modules). Not for use; not maintained.

### Donor 4 — the rendering branch (total diagnostic renderers)

- **What it is.** On top of Donor 3, a bounded executed-renderer
  correspondence: the three recursive derived `Repr` printers for `Ty`,
  `GoValue` and `Expr` replaced by transparent, structurally terminating
  definitions (`GoLean/GoCore/Rendering.lean`; `Syntax.lean` and `Value.lean`
  touched), with kernel-checked equations showing the new renderers satisfy
  the old generated bodies and a separately argued source/derivation
  preservation case (not a kernel equality to the former opaque constants).
  It removes three of the partial-implementation findings (the `Ty`, `GoValue`
  and `Expr` printers).
- **Where.** Branch **`park/relational-prototype-rendering-2026-10-15`**, tip
  **`95b0b64b`** (2026-10-15; documentation-only park commit), implementation
  pin `ccc54f4f`, two commits over Donor 3's tip `701d8689`; base on main
  `31a6069d`. Records: `docs/2026-10-15_relational-rendering-stage.md`,
  `docs/2026-10-15_relational-rendering-review.md`; checked experiment
  `experiments/2026-10-15-rendering/` (`Derivation.lean`, `SemanticLinks.lean`,
  `RendererAudit.lean`, `check-derivation.py`, the reviewer's probes under
  `review/`). Not on origin.
- **State reached.** Full `scripts/ci --diff` PASS, 1,335 s, 114 GoLean
  modules replayed, 4,025 rows (3,767 / 258), 415 negative — on a DIRTY
  worktree; no commit-clean run is claimed; the review bound production
  hashes to `ccc54f4f`. Independent review accepted the bounded candidate
  for immutable handoff (no new semantic defect or preservation blocker) and
  explicitly not for merge or integration; in its narrower import scope the
  implementation scan still reports twelve inherited findings, unwaived. The
  stage record ends with the [USER] 2026-10-15 instruction (paraphrased) to
  finish only this candidate's validation and handoff and then park while the
  relational architecture was reassessed; it was parked after that handoff.
- **Reusable; not to be trusted for.** Reusable: the technique (parameterise
  the generated body, prove the total definition satisfies it, argue
  preservation at the source level) for any derived-instance finding of the
  same kind on main, independently of the relation. Not to be trusted: as
  equality to the old executed constants (the record says so itself).
- **Revive.** `git worktree add .claude/worktrees/relational-rendering park/relational-prototype-rendering-2026-10-15`;
  toolchain v4.32.2. Not for use; not maintained.

### Donor 5 — the concurrency spike (two-goroutine pool-driver compatibility)

- **What it is.** An experiment, not production code: two selected
  two-goroutine executions (a disjoint-memory print boundary, 25 iterations;
  an unbuffered rendezvous with happens-before, 38 iterations) proved through
  the actual pool driver and race detector, showing the variable-read phase
  law of Donor 2 reusable inside the pool relation. It discovered that the
  derived `Ord Loc` comparator used by `Race.shadowSet` compiled to an opaque
  partial `_unsafe_rec` with no kernel-visible equations and compiled the
  missing law as `Concurrency.RootComparatorContract` without assuming it.
- **Where.** Branch **`park/relational-spike-concurrency-2026-10-15`**, tip
  **`f6f37e36`** (2026-10-15), implementation `ea1341cf`, 17 commits over main
  `b49739ea` (2026-10-13) on the OLD (pre-rebase) line at RD5 E/F `fc52512a`;
  the production tree is exactly `fc52512a` (only `docs/` and
  `experiments/2026-10-14-concurrency-compatibility/` differ). Records:
  `docs/2026-10-14_relational-concurrency-compatibility.md`,
  `docs/2026-10-15_relational-concurrency-review.md`. Not on origin.
- **State reached.** The experiment package built (69 jobs), its standard-axiom
  audit passed (20,349 declarations), `leanchecker --fresh` of
  `Concurrency.Audit` exited 0; the implementation scan is FAIL with 17
  findings. **The full gate was NOT rerun** (`scripts/ci --diff`, the corpus and
  the Go frontend tests; the record says so, reusing the audited baseline's
  coverage as evidence only). Independent review: one MEDIUM finding OPEN and
  raised with the user (the comparator ordering contract, F1); two LOW wording
  findings fixed. The medium finding was later closed on Donor 6, not here.
- **Reusable; not to be trusted for.** Reusable: the shape of a pool-level
  compatibility proof that threads the real detector (no detector reset, no
  assumed detector success) and splits on every comparator result. Not to be
  trusted: as any general concurrent result (the record disclaims all-schedule
  safety, locality, sequentialization and Iris lifting), nor as a gated tree.
- **Revive.** `git worktree add .claude/worktrees/relational-concurrency park/relational-spike-concurrency-2026-10-15`;
  the experiment is a separate Lake package requiring GoLean by path;
  toolchain v4.32.2. Not for use; not maintained.

### Donor 6 — the detector-contracts spike (D1)

- **What it is.** The repair of Donor 5's finding plus data-structure laws for
  the race detector: `GoLean/GoCore/LocationOrder.lean` (a structurally
  recursive `instOrdLoc.ord` replacing the derived one, with
  `loc_compare_eq_iff`, `loc_compare_swap`, `loc_compare_lt_trans`,
  `Std.LawfulEqOrd`/`Std.TransOrd` instances, and `loc_compare_unfold` /
  `loc_comparison_unique` specifying the old generated algorithm),
  `ShadowOrder.lean` (shadow-key order as an injective code) and
  `ShadowHistory.lean` (`shadowSet_lookup_self`/`_other`, `ShadowOrdered`,
  `raceUpdate_ordered`, `PoolPrefix.shadow_ordered_empty`,
  `PoolPrefix.preserves_lookup`, `RaceState.accessKey_reject_of_mem`). The
  previously conditional negative control becomes the unconditional
  `pre_pair_rejection`. These three modules were carried into Donor 3 at I1.
- **Where.** Branch **`park/relational-spike-detector-contracts-2026-10-15`**,
  tip **`b4282cff`** (2026-10-15, documentation-only handoff), implementation
  `9c6efcfc`, 23 commits over main `b49739ea` on the old line, carried onto
  audited C1 `55ad7249` (so this branch also holds the old-line C1 modules).
  `refs/integration/i1/d1-{implementation,handoff}` name the same two commits.
  Records: `docs/2026-10-15_relational-detector-contracts.md`,
  `docs/2026-10-15_relational-detector-review.md`. Not on origin.
- **State reached.** Full CI/differential PASS at `9c6efcfc` (3,989 rows:
  3,749 PASS / 240 tracked FAIL; 405 negative; 396 interpreter tests; all
  speedbumps), kernel replay of the 105-import aggregate; experiment axiom
  audit PASS (21,517 declarations); the implementation scan FAIL with **16
  findings, individually dispositioned and explicitly unwaived** (the derived
  `Repr`/equality helpers named above under Donor 3). Independent review: no
  defect in the new comparator or laws; two LOW findings fixed; the old-opaque-
  constant equivalence remains a source-level argument, not a kernel theorem.
- **Reusable; not to be trusted for.** Reusable on its own, independently of
  the relation: the total `Loc` comparator and the detector history laws
  concern `Ops.lean`/`Race.lean` definitions that are on main (a candidate for
  the trust-surface finding the spike raised, if the user wants it). Not to
  be trusted: as race-freedom or ownership results (the record disclaims
  them); key inequality is not memory separation.
- **Revive.** `git worktree add .claude/worktrees/relational-detector park/relational-spike-detector-contracts-2026-10-15`;
  toolchain v4.32.2. Not for use; not maintained.

### Donor 7 — the unseq spike (U1, restricted sequentialization)

- **What it is.** A restricted `unseq` sequentialization theorem: for finite,
  topologically indexed, evaluation-only graphs with one fresh binder per
  occurrence (no regions, no phase-2 stores, no guards), every schedule is safe
  on every tape, completes, and agrees with a canonical least-active-first run
  on completion control and store (`Unseq.Domain.all_schedules`,
  `.sequentialization`, `.enter`, `.canonical_entry`; `SafeUntil`,
  `SegmentPrefix`; `Ranked`, `HeapDomain.At`, `Traversal`). Ten modules:
  `RelationalLocality`, `RelationalSegment`, `RelationalStorePathFor`,
  `RelationalUnseq`, `RelationalUnseqCanonical`, `RelationalUnseqEntry`,
  `RelationalUnseqGraph`, `RelationalUnseqHeap`, `RelationalUnseqOperations`,
  `RelationalUnseqTraversal`, plus a checked local adapter discharging the
  logic's frozen RD8 `SimulationLaw`/`GuardedTarget`
  (`experiments/2026-10-15-unseq-rd8/`) and controls
  (`experiments/2026-10-15-unseq-compatibility/`, incl. the alias source
  control that reproduces the pool explorer's `{-2, 7}`). Integrated into
  Donor 3 at I2 (`4731d491`).
- **Where.** Branch **`park/relational-spike-unseq-2026-10-15`**, tip
  **`ce0daf9f`** (2026-10-15, documentation-only handoff; also
  `refs/integration/i2/u1`), implementation `82a2ff31`, two commits over I1
  `5d8e53e9` on the prototype line; base on main `31a6069d`. Records:
  `docs/2026-10-15_relational-unseq-stage.md`,
  `docs/2026-10-15_relational-unseq-review.md`. Not on origin.
- **State reached.** Full `scripts/ci --diff` PASS on an EARLIER dirty U1
  tree (4,025 / 415, no regression) that preceded the final traversal and
  adapter additions; at the final commit only the fast tier (`scripts/ci`,
  160 s, 106 modules replayed) is claimed, and the record says so. The
  integrated form's full run is I2's. Two independent reviews: R1 (MEDIUM, an
  over-quantified observation hook) fixed by `SafeUntil.observe_prefix`; the
  fresh RD8 review found no new semantic finding; 21 combined findings
  (16 upstream + 5 frozen-logic) open and unwaived.
- **Reusable; not to be trusted for.** Reusable: the graph-progress and
  heap-domain carriers and the all-ready traversal as a pattern for proving
  schedule independence from operational expression laws. Not to be trusted:
  outside its domain (invocation/alias effects, internal choices, guards,
  regions, failure/cleanup effects, allocation renaming, concurrent transport
  are all open), nor as a gated final commit.
- **Revive.** `git worktree add .claude/worktrees/relational-unseq park/relational-spike-unseq-2026-10-15`;
  toolchain v4.32.2. Not for use; not maintained.

### Local-only refs of the relational era (snapshots, not pushed)

These resolve on this clone only (`git for-each-ref`, 2026-10-20); none is on
a pushed branch, none is indexed as a donor, and they are safety copies, not
handoffs. On NO branch: `refs/integration/i1/c2-implementation` (`626faca5`)
and `refs/integration/i1/c2-handoff` (`826fb7fb`), the pre-rebase C2 line
(RD6's audited pin and handoff; also the only refs carrying `bd2e6c39` and
`fcebf85c`); `refs/snapshots/crash-recovery-20261013T215421Z/5-relational-surface-1013`
(`0b54e034`, the 2026-10-13 crash snapshot of the dirty refactor worktree,
untracked files included); `refs/snapshots/relational-concurrency-1014-before-step-certificates`
(`7d5270bb`, before a cancelled whole-trace `decide` proof);
`refs/checkpoints/o1-prevalidation-20261015` (`ce20d7a4`, O1 source before
validation, not a checked handoff); and the reviewer-overlay snapshots
`refs/snapshots/rd4-phase-audit-before-removal` (`8955dae7`),
`refs/snapshots/2026-10-14-rd5-review-cleanup` (`25c188bb`),
`refs/snapshots/2026-10-14-rd5-residual-review-cleanup` (`f3a8bc15`). On a
donor branch already: `refs/integration/i1/main` (`31a6069d`, on main),
`refs/integration/i1/rebased-c2` (`1c91f59f`), `refs/integration/i2/o1`
(`3f39150d`), `refs/integration/observed-phases/i2` (`8bcaef37`) on Donor 3;
`refs/integration/i1/d1-implementation` (`9c6efcfc`) and
`refs/integration/i1/d1-handoff` (`b4282cff`) on Donor 6;
`refs/integration/i2/u1` (`ce0daf9f`) is Donor 7's tip. Three local reviewer
branches of the rounds also exist and are not on origin:
`audit/rd4-phase-1014` (`2694c74e`), `audit/rd5-composition-1014`
(`f8261de6`), `audit/rd5-residual-independent-1014` (`84c05409`). Whether to
keep or drop any of these is the owner's; nothing in this section depends on
them.

## Evidence archive branches

Bulky evidence stays off main (`docs/architecture-rules.md`, "Evidence on main",
[USER] ruling 2026-09-07 relayed): each `archive/evidence-<date>_<slug>`
branch is listed here with the main-side directory that carries its
README and `MANIFEST.tsv`. No `archive/evidence-*` branch yet (2026-09-07);
the first payload kept off main under this rule is the typed-consumer
sprint's, whose archive is the sprint branch itself (above) and whose
manifest is `docs/evidence/2026-09-05_typed-consumer-sprint/`.
  (Landed on `main` by train r50, 2026-09-27, documentation only: release-check no inputs changed; fast
  `scripts/ci` PASS; the adversarial audit waived — [USER] Mike, relayed: (the review waived).)
