# W2 log (2026-08-27) — one writer: the w2 worker (same lane, W1's successor)

**Log-file choice, stated per the charter handoff**: this is a NEW file,
`docs/w2-prover-log.md`, continuing `docs/w1-prover-log.md` (one log per
unit wave, same lane). The pre-existing `docs/raft-w2-log.md` is a
KILLED-ERA artifact (fixed-trajectory campaign) and is not this log.

**QUANTIFIER-AUDIT LINE (the charter's opening requirement):** W2
builds the rules that discharge ∀-ITERATIONS (the loop-rule family
over the judgment: the map-range rule with multiset invariants —
also the library-internal mapIter latitude's ∀-DRAW discharge — and
the plain-`for` head schema) and completes the COMPOSITION machinery
(the plug rule: ∀-caller-context consumption — a CallSpec proved at
canonical placement becomes consumable at any framed foreign call
site); the init spec BEGINS ∀-state's discharge at the base (I₀ as
the future invariant's base clause). **No end-theorem quantifier
closes in W2**; every theorem here is a RULE consumed by W3–W5, an
init-spec instance (∃-shaped conclusions at the base state), or a
pilot/witness instance labeled as such.

Governing docs: `docs/2026-08-27_clean-proof-plan.md` §W2 + the
professor's delta 5, `docs/w1-prover-log.md` §"W2 charter proposal",
`docs/2026-08-27_w1-judgment-design.md` (extended by this unit's
addendum §7–§9), `CLAUDE.md` (charter), `docs/operational-lessons.md`
(build discipline). Branch `w1-prover` @ 71b1561f (inherited; ONE
WRITER — W1's worker retired). Conventions: capped builds only,
box-wide lock for full builds, zero sorry/native_decide/new axioms,
design-note-first with LINEAGE, [AGENT] provenance, derivation-
anchored numbers, no subject-run-anchored counts in exported
statements (W1's flagged interpretation stands: private scaffolding
may carry counts, exports may not — kept flagged, not silently
absorbed).

## Successor re-verification (W1's top claims, re-checked before any work)

All checks run 2026-08-27 against the inherited worktree; verbatim
outputs in the terminal record of this session.

- **Tip + cleanliness**: `git rev-parse HEAD` →
  `71b1561f14df367ea35fa8727fadb09e9ef888ef`; `git status` → branch
  `w1-prover`, "nothing to commit, working tree clean". CONFIRMED.
- **Gate log on record**: `artifacts/w1/gate2.log` tail shows
  `ok eval tests (141 ok)`, the two visible no-diff hatch notes, and
  `RESULT: PASS`. CONFIRMED (docs/proofs-only unit; no differential
  owed; judge owed at merge stands, per the W1 log).
- **Audit pins**: `grep -c '#guard_msgs' proofs/Audit/W1.lean` → 39;
  section split (awk over the `/-! ##` section boundaries at lines
  19/59) → 18 pins in the RunGlue section + 21 in the
  judgment/pilot sections. `becomeFollower_callSpec` pin expects
  axioms `[propext, Classical.choice, Quot.sound]`, `bfPre_inhabited`
  expects `[propext, Quot.sound]` (proofs/Audit/W1.lean:98-101).
  CONFIRMED (the W1 log's "39 pins" = 18 RunGlue + 21 others, one
  file).
- **Pilot exports present**: `becomeFollower_callSpec` (line 162),
  `bfPre_reader` (142), `bfPre_inhabited` (229) in
  `proofs/GoLeanProofs/Specs/RaftPilot/BecomeFollowerSpec.lean`;
  the three tracked open-tail probe examples at lines 246-260 of the
  same file. CONFIRMED.
- **Hatch grep**: `grep -rn "sorry\|native_decide"` over
  `proofs/GoLeanProofs/` → matches are DOC-COMMENT text only (6
  docstring mentions, zero live occurrences); `proofs/Challenge.lean`
  is sorry-bodied BY DESIGN (the challenge apparatus states its
  targets as sorry'd statements — its own docstring says so).
  CONFIRMED at 0 live escapes.
- RunGlue module exists at 494 lines
  (`proofs/GoLeanProofs/RunGlue.lean`), matching the W1 log's
  derivation-anchored count. CONFIRMED.

Verdict: W1's record stands as claimed; no drift found. Work begins
from 71b1561f.

## Units (charter order)

1. THE PLUG RULE (gates all W3 composition; design addendum first,
   probe-first on two structurally different call sites; GATE =
   becomeFollower_callSpec consumed at a REAL caller site with state
   framing, measured).
2. The loop-rule family (map-range rule with multiset invariants over
   the judgment; plain-`for` head schema harvested from
   campaign-arc4d CondFor; mapPickLoop element-type generalization;
   mapIter_no_stop_of_unmutated; each rule witnessed on a small
   non-subject loop).
3. THE INIT SPEC ($pkginit + setup as ordinary Specs establishing the
   base state, concluded in reader vocabulary; connects through
   RunGlue to runProgramSetupM; works at TRUE addresses — the
   31-globals identity constraint means no relocation at the base).
4. The layout-compliant tracked generator (tools/, inert,
   provenance-documented; Spec-precondition instances, not proof-body
   literals; middle path — only what Leg-B-full + the init spec need).

## UNIT 1 — THE PLUG RULE: LANDED (measurements, derivation-anchored)

- **Probe-first (charter requirement)**: `Frame/PlugProbe.lean`
  (tracked in-build; working copy `artifacts/w2/ProbePlug.lean`):
  `plugC` commutes step-for-step at OPEN `env'/k'` on three concrete
  spans — (P1/P2) a callee with a defer AND a nested call, 54 steps,
  commutation checked at prefixes {1,3,8,15,25,40,53,54}; (P3) a
  panic-recover-in-deferred-function span, 30 steps, prefixes
  {1,5,10,20,29,30}; plus the deep driver-shaped context composition
  (caller glue + labelK + the caller's own frame over `.stop` BELOW
  the plug point, 66 steps, the caller's write landing after the
  span). All 14 commutation examples close by `kernel_rfl`;
  elaborator `rfl` does NOT reduce open-context `stepFnIter` (the
  same W1 finding that begat `kernel_rfl`).
- **The rule, landed** (`Frame/Plug.lean` 190 + `PlugOps.lean` 589 +
  `PlugApply.lean` 761 + `PlugStep.lean` 1012 + `PlugRule.lean` 198
  = **2,750 lines**; the W1 cost datum was the 795-line rename walk —
  the plug walk's per-step file alone (1,012) is that class; the
  rest is the helper/builder/barrier-preservation layers the rename
  walk amortized across its own pre-existing helper modules):
  * `stepFn_plug` — the ~200-branch `fun_cases` walk (StepSim's
    skeleton, state-trivial): every arm commutes with `plugC`, with
    the barrier/exit/crossed classification. Battery killed ~160
    branches; 40 named cases (frame-family barrier splits, frame
    entries, panic passthrough/drain, recover, catch-all entry
    lemmas, mapIter pick, chan/sync/select applies).
  * `stepFnIter_plug` — iteration; the crossed panic shape refuted
    from span success (terminal discipline), the exit pins the fuel.
  * `callSpan_plug` — **THE PLUG RULE**: a successful resultless
    call-span at the canonical anchor `([], .stop)` (the shape
    FrameSim transport delivers) holds at ANY `(env', k')` under the
    §7 premises, at the same fuel/terminal state/stream.
  * Axiom pins in-build (`Audit/W2.lean`): exact trio on all three.
- **The §7 premise delta held up in the proof**: the two
  context premises (`mapIterFree k'`; `recoverThroughWrappers k' =
  none`) and the non-wrapper-callee premise are each consumed at
  exactly the predicted arms (delete-prunes; the barrier-level
  recover; the recover walk's wrapper transparency) — no further
  side conditions surfaced across the whole walk. What this taught
  us: the §7 "non-locality census" is COMPLETE — recover and
  map-range pruning are the only two machine features that inspect a
  continuation through a call boundary.
- Wall (measured from the build logs): PlugStep's full-walk
  elaboration ≈ 3-4 min per iteration at 48G/4 threads; final full
  build of the five modules + pins green.

## UNIT 4 + THE GATE: LANDED (measurements, derivation-anchored)

- **The tracked generator** (`tools/relayout/CBfLitGen.lean`, inert —
  run on demand via `lake env lean` from `proofs/`): the recovered
  arc4d printer (git `0fd62435^:tools/campaign/BfLitGen.lean`,
  fail-closed) + one W2 extension (`pKopen`: the barrier frame
  printed with OPEN `tenv`/`k` — the continuation-parametric emission
  W1 applied by hand). Emits `CBfLit.lean` (507,729 chars, tracked)
  as the `Reloc` image of the tracked W1 literals. Provenance chain:
  BfLit (tracked) → Reloc (tracked semantics module) → generator
  (tracked) → CBfLit (tracked), re-checked in-build by CBfFixture's
  kernel links. The F6 rule closed structurally — no untracked link
  anywhere.
- **Relocation-as-definition REJECTED on measurement**: defining the
  compliant chain as `relocS`/`relocC` applications made the kernel
  re-reduce the relocation inside every window check (>10 min,
  killed); ground literals restore the original wall. Recorded in
  CBfFixture's docstring so nobody re-simplifies the generator away.
- **The compliant chain verifies**: `CBfFixture` window links
  (kernel `rfl`, open caller context) GREEN in 88 s — same wall
  class as the original layout; the machine is address-uniform on
  this span, as predicted. Crossing modules (CBfSteps/2/SortStep,
  address-shifted mirrors reusing all shared machinery by import)
  ≈1 s each; the compliant capstone `cBecomeFollower_callSpec` 9.5 s.
- **THE GATE — Leg-B-as-intended, PASSED, measured 38 s wall
  (whole `W2Gate` module)**: `w2_gate` — the VERBATIM
  `raft.stepCandidate` MsgApp-case call statement (extracted from the
  pinned wire; args `#[.var "r", .var "$c1567", .var "$c1568"]`), at
  a framed caller state σFG (the compliant footprint under
  `ρT 52 4` + the caller's locals in the frame gap `[52,56)`, the
  receiver cell pointing INTO the footprint — exactly the cells W1
  proved no admissible ρ could cover), over the REAL continuation
  (the site's next statement, the `handleAppendEntries` call, over
  the caller's own frame), at EVERY choice stream: the span completes
  to `.next kG` at the same fuel/stream discipline and the framed
  terminal state reads back `specBecomeFollower` through
  `absRaftNode`. Composition exactly as the design said: callee
  CallSpec (state ∀, canonical anchor) + FrameSim state half
  (`frameSimG`; `bodies_inv` discharged by `renameBodies_id` + ONE
  kernel fold `funcListSup twinLowered.funcs = 31`) +
  `stepFnIter_plug`/`callSpan_plug` control half + reader
  congruence. Honest scope note in the module: σFG is a CONSTRUCTED
  precondition instance (the ∃-discharge class), not a
  driver-reachable state — reachable states are the init-spec/W3
  chain's product.
- Audit pins (`Audit/W2.lean`): cBecomeFollower_callSpec /
  cBfPre_inhabited / frameSimG / w2_gate, exact axiom sets in-build.

## Judgment calls and checkpoints

- [AGENT] Log-file choice: new `docs/w2-prover-log.md` (this file),
  for the one-log-per-wave convention; the W1 log is closed history.
- [AGENT] Plug-rule design delta recorded (design note §7): the W1
  expectation "panic-walk arms excluded by span success, not side
  conditions" is REFUTED by the machine walk-through — two genuine
  side conditions on the plug context exist
  (`recoverThroughWrappers k' = none`; `mapIterFree k'`) plus the
  non-wrapper-callee premise; all consumption-site-checkable.
  Derivations in §7 (the recover walk inspects below a barrier that
  is the first non-wrapper frame; the delete-prune walk crosses call
  frames by design).
- [AGENT] Scoping facts established by survey before unit 3 (both
  derivation-anchored to the pinned wire + RunGlue):
  * `$pkginit` is LOOP-FREE: one 44-statement straight-line block
    (31 global assigns, 8 unrolled map-literal sequences, 5 news, 10
    calls to the `goleanShimErrorsNew` leaf; 1,382 machine steps,
    zero choices consumed — the arc4 measurement). The plan's
    "init's loops" live in the SUBJECT's setup prefix
    (`newTwin`: the pending-commands push, the voters build, the
    3-node build with NewMemoryStorage/ApplySnapshot/NewRawNode),
    INSIDE `twinChoiceVerdict` — not in `runProgramSetupM`. The init
    spec is therefore staged: stage A = the `runProgramSetupM`
    boundary ($pkginit + seeding, concluding on the statics the
    handlers read); stage B = the subject prefix through `newTwin`
    (shells/empty net/counters zero), which needs library-function
    CallSpecs of W3 scale — attempted after stage A, honest gap if
    it exceeds the unit.
  * The TRUE static layout: the twin's 31 globals sit at
    `.base ⟨0⟩ … ⟨30⟩` in wire declaration order (seedGlobals pins
    this, StepFn.lean:902); "layout-compliant" fixtures = addresses
    0–30 reserved for the globals, fixture cells from 31 up (so
    `bodies_inv`'s forced identity on 0..30 is compatible with a
    ShiftSpec whose identity region covers them — the frame gap
    then sits above the fixture top, where caller locals live).
  * The arc4d/W1 pilot fixture (raft cell at 0, nextAddr 21) is
    canonical-only, per W1 finding 3 — re-derived here: with the
    twin function table every admissible ρ fixes 0..30, and
    `alloc_reg` caps the identity region at the fixture's nextAddr
    (21), so NO nonempty-frame FrameSim image of that fixture
    exists. Leg-B-full therefore requires the RE-LAID pilot fixture
    (unit 4's generator), exactly as W1's unit-6 proposal said.
  * The killed `StaticCells.lean` (git 60969eee, deleted in W0) is
    the authoritative record of the post-init statics (roots at
    20..30, shim payload cells at 71/75/79/83/87/91/95/98-class
    addresses, nextAddr 98 post-init) — consulted as a reference,
    never revived as a replay pin.
- [AGENT] Unit-4 scope note (potential charter tension, resolved
  fail-closed and recorded): the W2 charter says the generator
  produces "Spec-precondition instances, NOT proof-body literals";
  but the gate (Leg-B-full with state framing) is UNREACHABLE
  without a compliant-layout becomeFollower fixture, whose window
  literals are proof-body scaffolding (the three W1 dead ends +
  the alloc_reg derivation above close every literal-free route).
  Resolution: the tracked generator emits BOTH the precondition
  instances (its charter deliverable) and — as clearly-labeled
  PRIVATE scaffolding with the W1 conventions (count-free exports,
  literal-bearing privates) — the re-laid fixture the gate needs;
  this follows W1's own unit-6 proposal ("re-lay becomeFollower's
  fixture as the pilot"). Flagged for the audit rather than silently
  absorbed.
