# Campaign lane `campaign-arc4c` — SP1, the choice-invariance lemma + the seed pin

Scoping-lane log. Branch `campaign-arc4c` @ base `4a158041` (the
arc-4 lane's U21 gate tip, arc4b landed), one writer, NEW FILES ONLY
(hard rule, the arc4b precedent: no existing tracked file edited —
this lane lands at a wave boundary without textual conflict). Charter
(coordinator dispatch, recorded verbatim in intent):

1. PROBE FIRST (the named hidden-wall candidate): census the init
   span's operation classes against ~ (relocation × capacity-slack)
   BEFORE building; a draw-dependent LAYOUT the atoms don't capture
   is the wall candidate. A refutation is a first-class deliverable.
2. THE CHOICE-INVARIANCE LEMMA (lineage: bisimulation up-to ~ / data
   independence / the project's quotient theorem; [USER] 2026-08-27
   design contribution): init-span operation classes from ~-related
   states under ANY choice streams yield ~-related states, absRead/
   Fam ~-invariant; built forward-compatible with the future symbolic
   semantics (the canonical forms and ~ ARE its future state space;
   no semantics packaging now — §7).
3. THE SEED PIN: one literal init run (generator + kernel anchor per
   the U12/U21 link-pin pattern) establishes the representative
   post-init state ∈ Fam with absRead = N₀; the lemma lifts to
   ∀-init-choice-prefixes; discharge `Seed N₀` (NativeS1Chain's
   hypothesis).
4. Witness-in-same-slice throughout; the lemma's witness includes a
   NON-canonical stream instance (different capacities) landing
   ~-equal.

Design of record: the campaign worktree's
`docs/2026-08-26_campaign-flexibility-redesign.md` (§3, §7 middle
path, §8 hierarchy + the four adopted contributions); design basis:
the campaign log's three 2026-08-27 [USER] entries (choice-invariance,
representation-engineering, symbolic semantics). Conventions held:
masked-kill (judge by captured exit codes), tree-propagation
crossings, kernel_rfl never decide on the pinned program,
numeric-args-first on hangs, witness-in-same-slice, capped builds
48G warm / 64G cold staggered behind `free -g` ≥ 40G (sibling on
campaign-arc4 builds in parallel), zero sorry/native_decide/new
axioms, [AGENT] + what-this-taught-us lines, derivation-anchored
numbers, anti-grinding, §7 two-axis test.

New tracked files this unit (nothing else touched): listed at the
exit block. Probes gitignored under `artifacts/probe/`.

## SP1 entry — 2026-08-26

- Slice 0 — LAUNCH VERIFICATION: `git rev-parse HEAD` = `4a158041`
  (the U21 gate tip), `git status` clean (0 lines). 72–85G available
  at launch checks (≥ 40G floor; sibling active). Worktree build
  state COLD (proofs/.lake 39M — no build products); per SC1 ops
  note (e) cold full builds OOM 48G, so this unit builds TARGETED
  module sets first (48G-capped) and takes the full-tree build only
  when needed at gate time.
- [AGENT] read-first per charter, completed before any build: the
  flexibility redesign (full), the three 2026-08-27 [USER] campaign
  log entries, arc4 log U18 (C1 verdict block: 81,261-step/171-choice
  init census; the census stream identified = all-zeros), arc4b log
  in full (SC1 draw classification: 345 draws = 245 mapIter +
  100 appendSpill, 0 OTHER, init buckets; C3 `Seed`/`GoodReach`;
  C4 + landing manifest), U19 (FrameSimS/span_consume), U21
  (tree-propagation template, third kernel wall, masked-kill),
  CLAUDE.md, the constitution pointer. Code ground truth read:
  `ChoiceSite.policy` + `Choices.consume` (State.lean — pop = value
  mod bound, exhausted → 0), `ShiftSpec`/rename layer (Frame/
  Rename.lean — fresh-region order-pinned, low region arbitrary
  injection), `RoundFam`/`absTwinRead`/`RoundLemmaShape`
  (RoundStatement.lean), `Seed`/`SNet`/`ENode` (NativeS1Chain/
  NativeObligations), SpillTransport (the transport idiom),
  StaticCells (the U12 closed-computation link-pin: kernel
  recomputation of the extraction, ~100 s per 1,382-step link),
  `appendSpillWidth`/`buildAppendBackingValue` (Ops.lean — spill
  backings pad with DEFAULT values beyond len: the beyond-view
  region of spilled backings is deterministically zero-like),
  twin-chdriver.go (init boundary: `newTwin(3,2)` → say →
  `t.step(op{opCampaign,1})` — the anchor is the first
  `main.twin.step` call).
- Probe templates copied read-only from sibling worktrees into this
  lane's gitignored `artifacts/probe/` (ChoiceSiteProbe from arc4b;
  TwinRoundFixProbe/RoundFixDump/MsgAppRingGen from arc4).

### Slice 1 — THE INIT-SPAN PROBE (charter item 1, PROBE FIRST; probes
`InitChoiceProbe`/`InitPerturbProbe`/`DiffK41`/`DiffK41b`/`MaskCheck`,
all gitignored; TSVs `artifacts/initcensus-events.tsv`,
`artifacts/initperturb-s0..3.tsv`)

- **The anchor**: the first `main.twin.step` call config (the
  campaign event's call site — twin-chdriver.go: `newTwin(3,2)` →
  say → `t.step(op{opCampaign,1})`), detected by config shape.
  Canonical all-zero walk: **ANCHOR at step 81,261, na 103→4,965,
  171 choices consumed — U18's init census replicated EXACTLY,
  independently** (fourth replication of the pinned run's prefix;
  the full continuation also re-verified: 711,616 steps, na=heap=
  36,376, end line (viol 0, claims 1, committed 6, complete 1) —
  U18/SC1's numbers to the step). The twin cell sits at address 121
  (= `rhbTwinLoc`, the same address the round fixture pinned).
- **The init draw census by site × bucket** (171 events, labeled by
  pre-step config + nearest watched call): 108 mapIter @
  raft.NewRawNode, 30 mapIter + 22 appendSpill @
  raft.raft.becomeFollower (the 3 boot becomeFollowers), 9
  appendSpill @ raft.NewRawNode, 2 appendSpill @ newTwin; 0 OTHER.
  Buckets consistent with SC1's init rows.
- **THE PERTURBATION SWEEP — ALL 171 positions** (stream = k zeros
  ++ [97] ++ zeros; 4 parallel 12G-capped shards; per-row
  classification vs the canonical anchor):
  - **cfgEq = TRUE at 171/171**: every perturbed run reaches the
    SAME anchor configuration (env/cont literally equal) at the SAME
    step count (dSteps = 0 in all rows) with the SAME na and heap
    length (dNa = dHeap = 0). Init's CONTROL and ALLOCATION-COUNT
    structure is draw-independent — layout perturbation never
    changes the shape of the run, only cell contents/order.
  - rawEq = TRUE at 69/171 (60 NewRawNode mapIter + 9 becomeFollower
    mapIter draws are state-invisible — width-1 done-checks or
    fully-canonicalized picks).
  - **canonEq (the strict ~ prototype: relocation × capacity-slack ×
    map-sort) = TRUE at 168/171** — every appendSpill draw (33/33:
    capacity-only content slack, no layout/step drift) and every
    NewRawNode mapIter draw absorbed.
  - **THE HIDDEN-WALL CANDIDATE FIRED, NARROWLY — 3/171 REFUSED**:
    positions 41/98/154 (one per node, mapIter @ becomeFollower).
    Root-caused at field level (DiffK41b): the drawn value PERSISTS
    as **`raft.raft.randomizedElectionTimeout`** (canonical 10 =
    electionTimeout + 0; perturbed 17 = +97 % 10) — these are the
    three per-node `resetRandomizedElectionTimeout` picks (the
    Intn-via-mapIter latitude shim). NOT a layout effect: a VALUE
    draw landing in reachable state — exactly the class the charter
    named ("a draw-dependent output the atoms don't capture"),
    though as a persisted scalar, not a layout.
- **The refutation's scope + the design response ([AGENT])**: the
  field's ONLY subject reader is `pastElectionTimeout`
  (deps/raft/raft.go:2050), consumed exclusively on tick paths, and
  the driver NEVER ticks (twin-chdriver comment + U18's structural
  reachability refutation: no Tick calls ⇒ no MsgBeat/election
  timeouts); the landed BfEquation already classifies exactly this
  field as a "latitude-bearing spot that absRaftNode never reads"
  (BfEquation.lean:22 — the U2-slice-4 pick-quantified treatment).
  Response: **~ gains a DECLARED, VISIBLE MASK** —
  `canonStateM mask` serializes masked struct fields as
  `CVal.masked` (never traversed), the seed pin's mask is exactly
  `[(raft.raft, randomizedElectionTimeout)]`, and the mask carries
  its justification obligations in the pin module's docstring. A
  masked equivalence is a DIFFERENT Prop from the strict one by
  construction — fail closed, no silent widening.
- **MASKED RE-VERIFICATION**: under the mask, positions 41/98/154
  land maskedEq = true (flags []), and so do two COMBINED variants —
  [(0,97),(12,97),(41,97)] (spill capacity + NewRawNode layout pick
  + rand draw) and a 7-position multi-class stream [(0,6),(2,33),
  (41,3),(98,9),(154,1),(60,2),(120,1)] — all reaching the anchor at
  81,261 steps with clean flags. A complementary sweep at value 5
  (covering width-3 slot 2: 5 % 3 = 2) runs in parallel; its result
  is recorded below when in.
- **PROBE VERDICT, stated plainly (the charter's question "did ~
  hold across all init operation classes")**: ~ := relocation ×
  capacity-slack HOLDS for 168/171 init draws and is REFUTED at 3 —
  the per-node randomizedElectionTimeout value draws, which no
  relocation/capacity/atom device can absorb because the drawn value
  persists in reachable state. The claim survives in the corrected
  form ~ₘ := relocation × capacity-slack × the ONE-FIELD declared
  mask, which the perturbation evidence supports at every probed
  position and combination. SC1's "absorbed-class" classification is
  CORRECTED, not overturned: the three draws were bucketed under
  becomeFollower mapIter (order latitude) but are value-persisting
  (`Intn` latitude routed through the mapIter site).
- **The complementary sweep (value 5) — CONFIRMS**: 171 positions
  re-swept at perturbation value 5 (5 % 3 = 2 — covers the width-3
  mapIter slot the 97-sweep's 97 % 3 = 1 missed; a second spill
  extra): identical classification — cfgEq 171/171, strict canonEq
  168/171, the SAME three rand rows refusing (timeout 15 = 10 + 5),
  zero flags. Both mapIter slots at width ≤ 3 and two spill extras
  are now census-covered at every position.

### Slice 2 — THE MACHINERY (`Frame/ChoiceCanon.lean`,
`Frame/ChoiceInv.lean` — new modules, general layer)

- **`ChoiceCanon`** — the choice-erased canonical state form:
  `CVal`/`CCell`/`CForm` (the future symbolic semantics' state space,
  named and documented per the standing [USER] decision; CompCert
  block-naming lineage), `canonStateM mask` (total, fueled — zero
  `partial`; fail-closed flags IN the form: FUEL / NONBASE-LOC /
  MAPKEY-UNSORTABLE / TAILNONZERO / MIXED-REF / VIEWFIX-UNSTABLE /
  DRAIN-FUEL), the `Mask` type (declared latitude-bearing fields,
  serialized VISIBLY as `CVal.masked`), `CEquivM`/`CEquiv` (= ~ₘ/~,
  proved equivalences), `CleanFormM`, and **reader invariance BY
  CONSTRUCTION** (`read_invariant`/`readM_invariant`: any reader over
  the canonical form is ~-invariant definitionally — the
  representation-engineering heuristic applied literally: invariance
  is bought at the representation, not proved per reader).
- **`ChoiceInv`** — the anchored-run layer: `anchorRun` (total,
  fueled, fail-closed; the U18 isAnchor pattern made
  predicate-parametric), `anchorRunProg` (closed program form),
  **`ChoiceInvariantToM`** — THE CHOICE-INVARIANCE STATEMENT FORMER
  (every stream's anchored run lands at the same config with a
  ~ₘ-equivalent state), `ChoiceInstanceAtM`, and
  `choiceInvariant_read` (the consumer corollary: reader facts at the
  representative transfer to every stream). The module docstring
  states the lemma's STANDING bluntly: statement layer + census +
  kernel witnesses here; the general ∀-stream discharge is
  bisimulation-up-to-~ = the future symbolic semantics'
  correspondence ("its erased half", [USER] 2026-08-27), post-T1.
- **Two kernel-route lessons, measured ([AGENT], for the ledger)**:
  (1) fueled MUTUAL recursions compile to well-founded form by
  default and are then KERNEL-IRREDUCIBLE (the de-WF class) — a
  canonState kernel_rfl failed as an instant "type mismatch" until
  `termination_by structural fuel` forced structural compilation;
  (2) `toString (repr ·)` inside a proof-facing function is
  kernel-opaque (the Format chain) — the map-key ordering was
  rebuilt as a structural byte-list comparison (`bytesLe`), after
  which a 132-cell canonState kernel-reduces in ~3 s.

### Slice 3 — THE SEED PIN (`Specs/Raft/SeedLit.lean` +
`SeedLitVar.lean` + `SeedCFormLit.lean` — generated;
`Specs/Raft/SeedPin.lean` + `SeedWitness.lean` — the pin + witness;
generators `SeedLitGen`/`SeedCFormGen`, gitignored)

- The representative: `seedσ` = the post-init pre-campaign state
  (heap 4,965 cells, na 4,965), generated by the SHIPPED `anchorRun`
  on the pinned program (generator consistency: the shipped runner,
  not a probe-local walker). Variant literal `svar*` at the stream
  perturbed [(0,97),(12,97),(41,97)] — one deviation per latitude
  axis (spill capacity / NewRawNode layout pick / the masked rand
  draw).
- **Kernel links (the U12 closed-computation idiom)**:
  `seed_setup_link` — `runProgramSetupM` on `twinLowered` (seeding +
  the full 1,382-step $pkginit) = the setup literal, EXACT
  (structure equality incl. tables/result locs/stream tail; ≈120 s
  kernel, measured); `seed_front_link` — init's first 300 steps from
  the setup literal = the front literal (`stepFnIter`, empty stream
  = canonical by the exhaustion rule). Steps 300–81,261
  GENERATOR-VERIFIED ONLY, stated bluntly in the module docstring
  with the completion routes of record (C-wave mirror windows at
  ≈35–45 min kernel; FastEval reflection at the arc-2 merge).
- **Endpoint readouts (kernel)**: `seed_absRead` — counters 0, three
  (0,0,0,0) shells, net [] ; `seed_nodes_zero` — per-node raft
  Term/Vote/lead/state all 0 through nodes[i]→rn→raft + lens.
- **Fam**: `SeedFam := RoundFam seedσ` (the R-form family anchored at
  the representative); `seed_inFam` at the identity placement.
- **The canonical-form pin** (`SeedCFormLit`, 90 KB literal):
  `seed_cform_pin : canonStateM twinLatMask seedσ seedRoots =
  seedCForm` — kernel-recomputed each build; `seed_clean` (flags [])
  and `seed_cform_cells` (207 live cells of 4,965 — the quotient
  drops init's garbage) are corollaries by rewrite. **The witness's
  equivalence routes through the SHARED pin** (`seedVar_cform_pin` +
  trans) — comparing two COMPUTED forms head-on blew past 10 min
  while each pin-vs-literal check is ~1–2 min: the U21
  representation-asymmetry lesson reproduced at the ~ layer and
  fixed by the same shared-terms route ([AGENT], ledger-worthy).
- **The abstract side**: `seedBootNode` (follower, term 0, vote 0,
  snapshot-boot log [(1,1)], committed 1 — U21's boot decode),
  `seedN₀ : SNet` (all nodes boot, empty ghost), **`seed_N₀ : Seed
  seedN₀`** — the native chain's hypothesis DISCHARGED (the exact
  Prop `native_one_leader_per_term` and every GoodReach skeleton
  consume).
- **The lift**: `SeedChoiceInvariance : Prop :=
  ChoiceInvariantToM twinLatMask … seedσ seedC` — the ∀-stream
  statement, with `seed_absRead_invariant` as the consumption shape.
  Standing recorded in-docstring (probe-measured + kernel-witnessed;
  general discharge = the symbolic semantics' erased half, post-T1).
- **The witness (`SeedWitness`)**: `seedVar_config` (same anchor
  config), `seedVar_cform_pin` → **`seedVar_equiv` : the two init
  runs ~ₘ-equal** (different capacities INCLUDED — the charter's
  named witness), `seedVar_clean`, `seedVar_absRead` (readout
  agreement, literal), and `seedVar_rand_differs`/
  `seed_rand_canonical` (the masked field REALLY differs, 17 vs 10 —
  kernel-pinned: the strict ~ refuses this pair, so the mask is
  occupied, not decorative).
- [AGENT] scoping call, flagged for the coordinator: the PER-CLASS
  ~-preservation transports (the spill/mapIter one-step lemmas over
  canonStateM) are NOT built this unit — they need canonState
  congruence machinery that is exactly the symbolic semantics'
  per-op obligation set; building them one-off against the fresh ~
  would be the fragile-expensive-one-off shape §7 forbids. The
  lemma ships as: carrier + statement former + census + kernel
  witnesses; the transports land with the symbolic semantics
  (post-T1, standing decision), or earlier if a consumer demands
  them (promotion-ledger condition).
- **Third shared-pin instance ([AGENT], measured)**: the witness's
  reader-agreement fact stated head-on
  (`absTwinRead varσ = absTwinRead seedσ`, both sides computed) ran
  >10 min kernel and was STOPPED AND BISECTED (WitBisect C/D: the
  variant's canonical-form PIN alone = 41 s; the head-on readout
  comparison alone = the >10-min pit) — re-routed as
  `seedVar_absRead_pin` (against the readout literal) + trans with
  `seed_absRead`. Three instances this unit of the same law (form
  pin, readout pin, and U21's crossing template): **kernel
  comparisons go computed-vs-LITERAL, never
  computed-vs-computed** — now the lane's standing rule for every
  `~`-layer fact.

### [AGENT] calls this unit (tagged)

1. [AGENT] The anchor chosen as the first `main.twin.step` call
   config (not the loop head): the abstract chain's `Seed` requires
   noLeaders, which holds PRE-campaign only; the anchor is
   config-shape-detected and the probe verified every stream reaches
   it identically (cfgEq 171/171). The loop-head family stays the
   C-wave's (RoundFam is consumed here only as the membership form).
2. [AGENT] The mask response to the probe refutation (rather than
   report-and-stop): the refutation is narrow (3/171), precisely
   root-caused (one named field), the field is dead-under-the-driver
   by code census + the U18 structural no-tick refutation, and the
   landed equation layer already treats exactly this field as
   latitude-bearing (BfEquation.lean:22) — so the corrected claim
   (~ₘ) preserves the unit's value while the strict-~ refusal is
   PINNED kernel-grade in the witness (seedVar_rand_differs). The
   probe verdict is reported as a refutation of the original claim
   regardless.
3. [AGENT] The general per-class ~-preservation transports deferred
   to the symbolic semantics (post-T1 standing decision) — the §7
   two-axis call recorded in slice 3; the lemma ships as carrier +
   statement former + census + kernel witnesses, and
   `SeedChoiceInvariance` is consumed as a NAMED premise, never
   asserted.
4. [AGENT] The kernel-anchor scope for the 81,261-step literal run:
   setup link (full, kernel) + 300-step front sliver (kernel) +
   endpoint readouts/pins (kernel), middle generator-verified with
   the completion routes named — the U18 round-witness split
   precedent, applied at init scale after measuring that a full
   naive replay is out of reach in-tree (heap-linear kernel wall;
   FastEval lives on the unmerged arc-2 branch).
5. [AGENT] All comparisons at the ~ layer routed computed-vs-LITERAL
   (three measured instances; the shared-pin rule above) — adopted
   as the lane's standing convention, briefed forward.
6. [AGENT] The seven new modules stay DELIBERATELY UNIMPORTED
   (SC1/C3's call 6 extended): wiring needs the aggregator or the
   `STANDALONE_PROOFS` allowlist — both existing tracked files this
   lane's hard no-edit rule forbids. Verification = explicit capped
   target builds (green: 83 jobs incl. all seven) + the `AxSeed`
   axiom readout + hatch grep; the landing manifest below carries
   the seven import lines.
7. [AGENT] Memory discipline: staggered behind `free -g` checks
   (72–119G at every launch; ≥ 40G floor held); targeted builds
   24–48G warm; the one cold full-tree build at 64G per SC1 ops
   note (e); perturbation shards at 12G ×4; every compile judged by
   captured exit code (masked-kill rule) — one 48G witness build
   and one 10-min bisect probe were STOPPED by timeout/kill and
   bisected rather than waited out.

### What-this-taught-us

- (a) **The probe-first rule caught a real refutation the census
  classification had absorbed**: SC1's "all init draws
  absorbed-class" was TRUE at the value level it measured
  (canonicalized outputs) yet FALSE at state level for 3 draws —
  the drawn value persists in a field nothing reachable reads. Only
  a state-level perturbation diff could see it; the operation-class
  bucketing alone could not. The corrected form (~ₘ with a declared
  mask) is STRONGER as a record: the mask names exactly what is
  being ignored and why, where the unmasked claim silently included
  a false generality.
- (b) **The kernel's head-on-comparison wall generalizes beyond
  crossings**: three independent instances this unit (form-vs-form,
  readout-vs-readout, plus the U21 crossing template's original) —
  the fix is always the same shared literal. Computed-vs-literal is
  linear; computed-vs-computed loses sharing and is effectively
  unbounded.
- (c) **De-WF + de-Format are prerequisites for proof-facing
  executable definitions**: mutual fueled recursion silently
  compiles well-founded (kernel-opaque) without
  `termination_by structural`, and any `toString (repr ·)` in the
  chain is kernel-opaque via the Format layer. Both were caught by
  the tiny-probe bisect habit in minutes.
- (d) The init span's latitude structure is far more rigid than
  feared: allocation COUNT, step count, and the anchor config are
  draw-independent at every position (dNa = dSteps = 0, cfgEq
  171/171) — the entire draw effect is cell content and ordering.
  This is what made the literal-pin + ~ route viable at init scale
  and is the right empirical baseline for the symbolic semantics'
  init obligations.

### Interruption + protocol note (2026-08-26, on the record)

- The session was interrupted by a box-wide OOM (coordinator-owned:
  a 96G gate beside this lane's builds; owned in the campaign log).
  On resume ALL eight files verified intact and the seven modules
  re-verified green by capped explicit-target builds (EXIT=0 × 7,
  `artifacts/reverify.log`).
- **[USER→coordinator] NEW STANDING PROTOCOL adopted mid-unit and
  followed for everything below**: full builds and `scripts/ci` runs
  are EXCLUSIVE box-wide via the atomic lock
  `mkdir /home/dev/projects/golean/artifacts/build-lock.d` (rmdir on
  exit; 120 s retry loop); with the lock held full builds may use
  GOLEAN_MEM_MAX=96G; explicit-target builds ≤48G stay exempt;
  `lake env lean` produces NO oleans (never treated as cache-warming
  — this unit's probes used it only as probes; all verification
  builds were `lake build <target>`).
- Two incident notes, disclosed: (1) this session's earlier full
  builds died EXIT=143 repeatedly (the over-commit's kills); under
  the lock the SAME tree built green first try — 12 heavy modules
  had also been built sequentially during diagnosis (all EXIT=0,
  `artifacts/stragglers.log`). (2) On resume the session cwd had
  silently moved to the SIBLING worktree (campaign-arc4); one
  re-verify loop ran there before detection — all seven builds
  failed fast ("no such file", no sources of ours exist there), no
  tracked file was touched, and the single stray gitignored log it
  wrote (`campaign-arc4/artifacts/reverify.log`) was removed;
  every subsequent command uses absolute paths. [AGENT] — recorded
  as a one-writer-discipline near-miss with zero tracked impact.
- The full default-target build at the exit tree, under the lock:
  **"Build completed successfully (559 jobs)." EXIT=0**
  (`artifacts/arc4c-full-green.log`; 559 = the U21 tree — the seven
  new modules stay outside the default target, per the no-edit rule
  on the aggregator).

## SP1 exit (2026-08-26, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the branch base
4a158041: this single commit (seven tracked modules + this log;
probes/TSVs/build logs gitignored). New tracked files, complete list:
- `proofs/GoLeanProofs/Frame/ChoiceCanon.lean` — the ~/~ₘ carrier
  (CForm/canonStateM/Mask/CEquivM + reader invariance by
  construction);
- `proofs/GoLeanProofs/Frame/ChoiceInv.lean` — anchored runs + the
  choice-invariance statement former + consumer corollaries;
- `proofs/GoLeanProofs/Specs/Raft/SeedLit.lean` (1.6 MB, generated) —
  setup/front/anchor literals, canonical stream;
- `proofs/GoLeanProofs/Specs/Raft/SeedLitVar.lean` (1.4 MB,
  generated) — the variant anchor literals, perturbed
  [(0,97),(12,97),(41,97)];
- `proofs/GoLeanProofs/Specs/Raft/SeedCFormLit.lean` (90 KB,
  generated) — the pinned canonical form (207 cells);
- `proofs/GoLeanProofs/Specs/Raft/SeedPin.lean` — the seed pin
  (kernel links, readouts, SeedFam, seedN₀ + `seed_N₀ : Seed seedN₀`,
  `SeedChoiceInvariance`);
- `proofs/GoLeanProofs/Specs/Raft/SeedWitness.lean` — the
  non-canonical-stream witness (shared-pin equivalence + occupation
  facts).

**Deliverable state vs the SP1 charter:**
1. PROBE FIRST — **DELIVERED, WITH A REAL FINDING** (slice 1): the
   full 171-position perturbation census (two value sweeps + combined
   streams; U18's init census replicated to the step, fourth
   independent replication). **The probe verdict, plainly: strict ~
   (relocation × capacity-slack) HELD at 168/171 init draws and was
   REFUTED at 3** — the per-node `randomizedElectionTimeout` value
   draws (root-caused to the field; `raft.raft` cell, 10 vs 17). The
   corrected claim ~ₘ (one declared, justified, VISIBLE mask) holds
   at every probed position and combination. Not stopped-on-refutation
   because the refutation is narrow, precisely characterized, and the
   masked form preserves the unit ([AGENT] call 2; the strict-~
   refusal is itself kernel-pinned in the witness).
2. THE CHOICE-INVARIANCE LEMMA — **DELIVERED AS: carrier + statement
   layer + census + kernel witnesses; general ∀-discharge explicitly
   deferred to the symbolic semantics** (its "erased half", the
   standing [USER] sequencing): `CForm`/`canonStateM`/`CEquivM` named
   and documented AS the future symbolic semantics' state space
   (CompCert lineage), total and kernel-reducible; reader invariance
   holds BY CONSTRUCTION (representation-engineering);
   `ChoiceInvariantToM` is the ∀-stream Prop consumers name as a
   premise (`seed_absRead_invariant` demonstrates the shape). No
   general per-class transport was proved this unit — the honest
   §7 call, recorded ([AGENT] call 3).
3. THE SEED PIN — **DELIVERED** (slice 3): `seedσ` ∈ `SeedFam` (the
   R-form family at the representative); kernel links = the FULL
   closed setup computation (≈120 s kernel, StaticCells idiom) + the
   300-step front sliver; kernel readouts = absTwinRead (0-counters,
   3 follower shells, empty net) + per-node Term/Vote/lead/state = 0
   + the 207-cell clean canonical-form pin; the abstract side
   `seedN₀ : SNet` with **`seed_N₀ : Seed seedN₀` DISCHARGED** (the
   exact hypothesis `native_one_leader_per_term`/GoodReach consume);
   the 81,261-step middle generator-verified with completion routes
   named (mirror windows / FastEval-at-arc-2-merge) — the U18
   round-witness split, applied at init.
4. THE WITNESS — **DELIVERED** (`SeedWitness`): a genuinely
   different init run (different capacities + different iteration
   order + different rand draw) landing `~ₘ`-equal via the SHARED
   canonical-form pin, same anchor config, same abstract readout —
   all kernel-checked — plus the mask-occupation pair (17 vs 10)
   pinning that strict ~ refuses exactly as the probe measured.

Axioms (fresh probe `AxSeed` at the exit tree, verbatim class): all
22 readout lines within [propext, Quot.sound]; most propext-only;
`seedVar_config` axiom-free; ZERO Classical.choice anywhere in the
unit's surface. Hatch grep over all seven modules: **0** (code and
prose). Zero `partial` in proof-facing code (the one prose token
reworded preemptively, SC1's precedent).

- 2026-08-26 SP1 gate record (same-commit convention): unit-end gate
  `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=64G scripts/ci` at the exit
  tree, UNDER the new box-wide build lock — **RESULT: FAIL, exit 1
  (`GATE_EXIT=1` recorded in the log) — 21 ok steps, 8 notes (incl.
  the two sanctioned no-diff notes), and EXACTLY the ONE known
  structural red** (`artifacts/ci-arc4c-sp1.log`, gitignored):

  ```
  FAIL proofs-file audit coverage (un-swept proof file — import it from Audit.lean or allowlist with a reason)
  ```

  naming precisely the SEVEN lane modules (ChoiceCanon, ChoiceInv,
  SeedPin, SeedCFormLit, SeedWitness, SeedLit, SeedLitVar), each
  "not in the audited import closure nor on the standalone
  allowlist" — the same rule conflict SC1/C3/C4 recorded, resolved
  the same fail-closed way: both wiring points are existing tracked
  files this lane's hard no-edit rule forbids; the red is recorded
  verbatim, the landing action is the manifest below. Every other
  step ok, including the escape-hatch preflight, spec-anchor
  citations, surface purity, and statement-TCB closure. The
  comparator-landmark notes read **STALE at 161 commits** AND
  **OWED (scope: 1 trusted-closure file since 1730567a — the U21
  landing's Audit.lean lines; nothing from this unit touches the
  closure)** — both stand escalated for the operator's merge step,
  as since U8.
- 2026-08-26 SP1 compensating kernel checks (verbatim):
  - explicit capped builds of all SEVEN new modules
    (`artifacts/reverify.log`): `EXIT=0` × 7, plus the full
    default-target build green under the lock
    (`Build completed successfully (559 jobs).` EXIT=0).
  - fresh `AxSeed` readout (above): 22 lines, all within
    [propext, Quot.sound], zero Classical.choice.
  - hatch grep over the seven modules: 0 hits.

## THE LANDING MANIFEST (for the operator at the wave boundary)

1. **The one edit that turns the known red green:** add SEVEN import
   lines to `proofs/GoLeanProofs.lean`:
   `GoLeanProofs.Frame.ChoiceCanon`, `GoLeanProofs.Frame.ChoiceInv`,
   `GoLeanProofs.Specs.Raft.SeedLit`,
   `GoLeanProofs.Specs.Raft.SeedLitVar`,
   `GoLeanProofs.Specs.Raft.SeedCFormLit`,
   `GoLeanProofs.Specs.Raft.SeedPin`,
   `GoLeanProofs.Specs.Raft.SeedWitness` — then re-run `scripts/ci`
   (expect fully green; all seven kernel-check green standalone at
   this tip). Note the kernel cost joining the default build:
   SeedPin ≈ 262 s (the 120-s setup link dominates) + SeedWitness
   ≈ 41 s, every build.
2. **Namespace check for the joint import** (the U21 wStep-collision
   class): the unit's names are `seed*`/`svar*`/`Choice*` in
   `GoLean.RaftSeam`/`GoLean.ChoiceErase` — grep found no collisions
   with the landed tree; the arc4 sibling's in-flight names
   (Ring*/Round*) were avoided by charter.
3. **Standing items**: the comparator landmark STALE (161) + OWED
   (scope) escalation — the operator's judge run at the merge; the
   two sanctioned no-diff notes (docs+specs-only lane, no runtime
   change).
4. **What this lane hands the arc-4/C-wave side**: `SeedFam` (the
   round induction's base family, anchored at `seedσ`);
   `SeedChoiceInvariance` (the named ∀-stream premise + its witness
   evidence); `seedN₀` + `seed_N₀` (the abstract chain's discharged
   hypothesis — C3's `native_one_leader_per_term` and the
   EStep/HStep assembly consume it); `twinLatMask` (the declared
   latitude mask the ROUND ladder will also need — the in-run
   becomeFollowers re-draw the same field at MsgVote rounds, per
   SC1's bucket table).
5. **Owed-forward, recorded not counted**: the init span's
   steps 300–81,261 kernel completion (mirror windows ≈ 35–45 min
   kernel, or FastEval reflection at the arc-2 merge); the general
   ∀-stream discharge of `SeedChoiceInvariance` (the symbolic
   semantics' erased half, post-T1); the per-class ~-preservation
   transports (same owner); the mask's reachability justification
   is census+code-grounded this unit — a machine-checked "field
   never read" instrument would strengthen it (cheap probe, on
   demand).

**PROPOSED NEXT CHARTER for this lane** (the coordinator's call):
none mandatory — SP1 is complete at this tip. Natural successors,
in value order: (1) the C2d round-kind lemma's Fam base can now
anchor at `seedσ`/`SeedFam` (arc-4 lane's unit, not ours); (2) a
small follow-up slice making the ROUND spans' conclusions
~ₘ-composable (state the round posts' canonical-form pins — the
shared-pin rule makes this cheap); (3) at the symbolic-semantics
kickoff (post-T1): the ∀-stream discharge over the per-class
transports, consuming this unit's carrier + census as its
specification. Recommend the lane land at the wave boundary and
retire this worktree.
