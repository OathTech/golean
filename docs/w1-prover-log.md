# W1 log (2026-08-27) — one writer: the w1-prover worker

**QUANTIFIER-AUDIT LINE (the charter's opening requirement):** W1
builds the RULES that later discharge ∀-states (the spec former: the
`Spec` judgment ∀-quantified over a precondition predicate), composes
∀ch (threading the demonic tape through the judgment and its
composition rules), and bridges ∃n specs to the ∀-fuel/∃-fuel
sentences (the glue family: `runProgramM_mono`,
`runProgramM_readout_of_total`, `runConfig_prefix_classify` + the
two-phase lift). W1 itself proves no end-theorem quantifier — it is
the machinery wave, and says so. Every theorem in this unit is either
a RULE (consumed by W2–W5 to discharge quantifiers) or a PILOT
INSTANCE measuring the rules' cost (Leg A/B/C), labeled as such.

Governing docs: `docs/2026-08-27_clean-proof-plan.md` §W1 (as
professor-amended), `docs/2026-08-27_proof-structure-explained.md` §1,
`CLAUDE.md` (charter), `docs/operational-lessons.md` (build
discipline). Branch `w1-prover` @ 84b5edb3 off post-reset main.
Conventions: capped builds only, box-wide lock for full builds
(taken 04:57Z, owner file updated), zero sorry/native_decide/new
axioms, design note + LINEAGE before code, [AGENT] provenance on
judgment calls, derivation-anchored numbers.

## Judgment calls and checkpoints

- [AGENT] Build lock: owner file at the primary checkout read
  RELEASED (w0-reset's exit); zero batch lake/lean builds on the box
  (only idle LSP workers from a prior arc4d session + an unrelated
  project's server). Took the lock for the w1 cold build + gates.
- [AGENT] PROBE-FIRST on the summit (frame/footprint + the
  continuation-parametric lift), per the charter's starred-summit
  rule. The decisive question found while reading the landed engine:
  window facts (`symEvalWindow*_refines`) are proved at CLOSED
  configs — the arc4d becomeFollower span is anchored at
  `k = .stop`, `env = []` — but the plan's judgment is
  CONTINUATION-PARAMETRIC (∀ env k), which is what makes the call
  rule compose. Two candidate routes, both classics:
  (a) a plug/bind rule (wp_bind / evaluation-context locality):
      a full `stepFn` arm walk (~110 arms, StepSim-scale) proving
      tail-replacement commutation below a barrier frame;
  (b) OPEN-TAIL WINDOW EVALUATION: evaluate the window on a config
      whose below-frame tail is an open variable `k` (and open
      caller `env` in the frame's tenv slot) — kernel reduction
      never inspects below the barrier on a successful span, so
      `rfl` closes the window fact ∀ k for free (wp_bind realized
      by computational reflection instead of by a walk).
  Probe result (artifacts/w1/ProbeOpenTail.lean): route (b) WORKS —
  see the probe record below. Route (a) is recorded as the promoted
  escape if open-term reduction fails at scale (the escape ladder's
  first rung for this obligation).

## Probe record

- ProbeOpenTail (3 examples: span-exit shape at open `k`; open
  caller `env` in the frame's tenv; a 5-step seq+unwind span under
  the barrier with the open tail below): `rfl` closes ALL THREE
  (artifacts/w1/ProbeOpenTail.lean, exit 0, run against the cold
  build; the probe examples are tracked in-build in the pilot capstone
  module (`Pilot/BecomeFollowerSpec.lean`) so the finding is
  build-enforced).
  Route (b) is the driver's route. Cost of route (a) if ever needed
  at scale: the analogous landed arm walk `Frame/StepSim.lean` is
  795 lines (measured, `wc -l`).
- Cold build of the fresh worktree: GREEN, 508 jobs
  (artifacts/w1/cold-build.log, EXIT=0; capped 96G, threads 8,
  box lock held).
- [AGENT] Statement-count discipline, interpreted and flagged for
  the audit: the charter bans subject-run-anchored statements from
  being "cited by — or composed into — a proof". The pilot's
  EXPORTED deliverables are count-free judgment instances
  (`becomeFollower_callSpec` etc. — ∃n, reader vocabulary, no
  measured lengths); the count-bearing composition lemmas
  (`bf_full_span`, the `uW*` window links) are PRIVATE (or
  Pilot-scaffolding-labeled) proof-body content consumed only inside
  the specs' own proofs — the reading under which the plan's own
  "the arc4d span walks become the specs' proof bodies under the
  driver" is executable at all. If the audit reads the ban more
  strictly, the fix is mechanical (inline the private lemmas), not
  structural. Flagged, not silently absorbed.
- [AGENT] The judgment's ∀ch forced STREAM-TOTAL crossings: the
  machine's `consume` pads with 0 WITHOUT popping on the empty
  stream, so the arc4d pick lemmas (cons-shaped streams) were
  generalized to the uniform `headD 0`/`tail` form
  (`consume_eq : consume ch b = (ch.headD 0 % max 1 b, ch.tail)`) —
  one lemma, no case split anywhere downstream; the span's residue
  is `ch.tail⁴` at every stream length. What this taught us: the
  demonic-∀ch judgment is strictly stronger than the trajectory
  era's prefix-quantified forms, and the machine's exhaustion
  convention makes it almost free.
- [AGENT] Leg B scoping (boundary discipline): every real
  becomeFollower caller is Step-scale (raft.go:1146/1303/1707…),
  i.e., its own W3 production span; a same-session real-caller
  composition would have required a fresh fixture-generation round.
  Leg B therefore demonstrates the CALL-RULE mechanics at a real
  lowered call-statement shape with passive arguments and records
  the frame half as the measured summit finding rather than forcing
  it. The three findings in `Pilot/CallSiteComposition.lean`'s
  honest-scope block are the leg's real output.

## THE THREE-LEGGED PILOT GATE — measurements (derivation-anchored)

- **Leg A (becomeFollower's CallSpec, end-to-end)**: DONE.
  Exported: `becomeFollower_callSpec` (∀-state over `BfPre`,
  ∀ env k, ∀ ch, ∃n; pre/post via `absRaftNode`), `bfPre_reader`,
  `bfPre_inhabited`. Cost: NEW content = SpecJudgment 291 lines +
  ReflectConc 174 + capstone 262 + SymBase 96 (≈820 lines new);
  HARVESTED+transformed scaffolding = BfLit 7,890 + BfFixture 382 +
  BfSteps 318 + BfSteps2 390 + BfSortStep 109 (≈9,090 lines, arc4d
  provenance, open-tail + stream-total transformations applied).
  Wall (lake env lean / build, capped, warm imports): BfFixture's 7
  open-tail window link theorems 88 s (the kernel-dominated step —
  incl. the 2,316-step window at OPEN tenv/k); BfLit ≈2 s; steps
  modules ≈1 s each; capstone ≈10 s; whole pilot chain cold
  ≈105 s. The open-tail cost is INDISTINGUISHABLE from the closed
  arc4d links (same 88 s-class wall) — parametricity is free.
- **Leg B (two-function composition via the call rule)**: DONE at
  the scoped shape (see the [AGENT] scoping call): 140 lines, 0.8 s
  wall; `becomeFollower_call_stmtSpec` = caller StmtSpec containing
  the whole callee span via `stmtSpec_call`. The FRAME half of the
  planned leg is NOT demonstrated — refuted-as-planned with the
  measured redesign (below).
- **Leg C (the glue family)**: DONE and pinned. RunGlue 494 lines,
  18 pins; runProgramM_mono / readout_of_total / classify_of_total,
  runConfig_prefix_classify, unfolding equations, loadMany lemmas.
  Wall: seconds (within the 48G-capped incremental builds).
- Audit pins total (Audit/W1.lean): 39 `#guard_msgs` pins, in-build.

## THE FOOTPRINT-DESIGN VERDICT (the starred summit): ADJUSTED,
with one refuted-as-planned half and a measured redesign

- WORKED: footprint-as-canonical-γ-image (`BfPre`), disjointness
  carried once by the image (no pairwise enumerations anywhere in
  the pilot); reader congruence under FrameSim
  (`absRaftNode_frameSim`) — the Spec-transport half; open-tail
  windows deliver the judgment's ∀ env k at canonical placement
  for free (the plug rule NOT needed there).
- REFUTED-AS-PLANNED: framed CONSUMPTION at a foreign call site via
  FrameSim alone — the caller's env/k live exactly in the frame
  region, outside every admissible ρ's image (three dead ends
  measured by derivation: identity-ρ vs `fr_avoid`; aligned-prefix
  layouts; `bodies_inv` forcing identity on the 31 twin globals,
  which also disqualifies the arc4d fixture layout for transport).
- THE REDESIGN (gates W3): the frame = FrameSim (state half, landed)
  + THE PLUG RULE (control half: tenv/tail replacement below the
  barrier frame commutes with successful spans — wp_bind as a
  theorem). Cost datum: the analogous landed arm walk
  (`Frame/StepSim.lean`) is 795 lines; the barrier is syntactically
  recognizable (the unique frame directly over `.stop`), so no
  reachability invariant is needed. Additionally W3's fixtures must
  be laid out with global cells at their true static addresses
  (regeneration; the probe generators are untracked — registry
  Finding #3 bites here).

## What the driver actually needed vs the Lithium plan

The honest minimum sufficed — no Lithium, no tactic framework:
(1) open-tail window facts (`rfl`/kernel_rfl at open tenv/k);
(2) the stream-total crossing lemmas (consume_eq + the landed
`stepFn_pick_transport`); (3) `stepFnIter_chain` composition;
(4) the reflection retraction (`reflectK_conc`) to hand the
judgment arbitrary machine continuations; (5) `CallSpec.consume` /
`stmtSpec_call` at the sites. The only automation-shaped pain was
simp-normalization drift (`headD` vs `head?.getD`, matcher
mismatches in `runProgramSetupM`'s do-joins) — lemma-level fixes,
not framework demand. Recorded promotion candidates for W3: a
window-link generator at the compliant layout; the plug rule.
- [AGENT] FRAME-DESIGN DEAD ENDS, measured by hand-derivation
  before any build (recorded because they shape §3 of the design
  note): (i) identity-placement FrameSim is impossible with a
  nonempty frame (`fr_avoid` quantifies over ALL of ρ's image =
  every base address); (ii) aligned-prefix canonical layouts still
  cannot cover a caller's env/k — those live at frame-region
  addresses, which are OUTSIDE ρ's image by construction (that gap
  is exactly where `fr` cells sit); (iii) `bodies_inv` forces every
  transport-admissible ρ to fix the 31 twin global addresses, so
  the arc4d fixture (raft cell at address 0) is canonical-only —
  transported use needs a re-laid fixture. Conclusion folded into
  the design note: the footprint frame = FrameSim (state half) +
  plug rule (control half); canonical specs dodge plug via open-tail
  windows; framed CONSUMPTION at a foreign call site does not.

## W2 charter proposal ([AGENT] draft for the operator; plan §W2 +
this unit's findings folded in)

QUANTIFIER LINE: W2 discharges ∀-iterations (the loop-rule family
over the judgment) and the library-internal mapIter latitude ∀-draw
(multiset invariants — iterate-then-canonicalize), and establishes
`I₀` (the init spec). Its own end-theorem quantifier count is zero;
it is rule work plus one ∃-shaped init instance.

Units, in order:
1. **THE PLUG RULE, pulled forward** (W1's summit finding — it gates
   ALL framed consumption in W3, so it should land before W3
   estimates are priced): tenv/tail replacement below the barrier
   frame commutes with successful spans; one `stepFn` arm walk
   (StepSim-scale, 795-line cost datum) + the panic-walk helper
   commutations; interface = the unchanged judgment (a `CallSpec`
   proved at canonical placement becomes consumable at any framed
   site together with `stepFnIter_sim` + reader congruence).
2. The map-range loop rule with MULTISET invariants over the
   judgment (the choice-site ∀-draw discharge; `sliceWalk_loop` and
   `MapLoops` are the landed shapes to lift).
3. The plain-`for` head schema (harvest arc4d `CondFor`).
4. **THE INIT SPEC**: `$pkginit` + setup as ordinary `StmtSpec`s
   establishing `I₀`, over RunGlue's unfolding equations — kills the
   81k-step replay obligation. Its loops go through unit 2/3 rules.
5. Professor delta 5: pick-loop element-type generalization +
   `mapIter_no_stop_of_unmutated`.
6. **Fixture re-layout + TRACKED generator** (the W1 finding +
   registry Finding #3): regenerate the window-literal generator as
   a tracked tool, at the transport-compliant layout (global cells
   at their true static addresses); re-lay becomeFollower's fixture
   as the pilot so W3's handlers inherit the compliant pattern.
Inputs to W2.5 (recorded, not W2 work): footprint-carrier
postconditions (Leg B finding 3) belong to the invariant `I`'s
design.
