# The WP-walk driver, exemplar-first (spec-parity slice 3, 2026-08-10)

Charter item 3 (`docs/2026-08-09_spec-parity-arc-charter.md`). Branch
`spec-parity-s3` off `spec-parity` @ 419010af. This note opens with the
exemplar's design (the spec shape it fixes), then the driver design
(what the tactic does and does NOT claim), then the scaling manifest.
The parking ledger (user-scale items, AFK posture) closes it.

## 1. The exemplar: `testCompareNilToNil` (imported-goose semantics/nil)

**Chosen program**: the imported oracle `testCompareNilToNil` from
`Corpus/coverage/exec/imported-goose/semantics/nil/` (upstream
`testdata/examples/semantics/nil.go` @ 3be88bbb; body verbatim). Why
this one:

- **It is in THEIR proved set.** Perennial proves
  `wp_testCompareNilToNil` as a `test_fun_ok` lemma — `Qed` at
  `deps/perennial/new/proof/.../semantics_proof/nil.v:31` @ 43d4efab —
  one of the **28 proved** oracles the charter's parity claim is
  measured against (count corrected at the S3 audit: upstream has 36
  `test_fun_ok` lemma STATEMENTS — 28 `Qed`, 7 `Abort`, 1 `Admitted`;
  the "37 proved" figure this note first carried counted statements,
  and is corrected at its origin and every restatement, manifest §
  "the upstream denominator, measured"). The exemplar is therefore a
  real parity row, not merely a same-class stand-in.
- **It is R1-green and R2-pinned on our side** — the differential row
  passes against `go run`, and the staleness-guarded lowering term
  `nilLowered` (`proofs/GoLeanProofs/Specs/ImportedGooseNil.lean`,
  ci step 1c5) already exists, so the R3 statement quantifies the
  frontend's ACTUAL lowering, not a hand-transcription.
- **Its body exercises the spine widely but finitely**: declaration at
  a pointer type, `new(*uint64)` (the allocating wide-op class), an
  assignment, a deref-read, a nil comparison, return — plus the
  `golean*` wrapper's call / frame-exit / if / literal-assign
  machinery shared by every oracle in the class.

**The feature class the exemplar fixes**: goose `test_fun_ok`-style
sequential boolean oracles under the imported-goose wrapper convention
— `golean<TestName>()` calls the verbatim `test<Name>() bool`, maps
`true` to the int `1`, and the driver statement
`.call #[.var "r"] ⟨"golean<TestName>"⟩ #[]` writes the verdict into
the harness cell at base address 0 (the TotalPins observable
convention, seed `heap = [cell 0 ↦ int 0]`, `nextAddr = 1`).

**The spec shape (D1: BOTH, per the goldenSpecC/goldenReturnsTwoC
precedent)** — for each proved oracle, two theorems:

1. **The designated-shape triple** — `GoSpecC` (the concurrent-carrier
   full surface judgment, sequential-degenerate lane) at FULL
   `InitialSplit` strength:

   ```
   GoSpecC nilLowered.typeDefs.toList nilLowered.funcs
     nilLowered.methods nilEnv (r ↦ ⟨int, 0⟩) driver (r ↦ ⟨int, 1⟩)
   ```

   proven as `goSpecC_of_goSpec (goSpec_of_wp <the hand walk>)` — the
   per-program content is exactly the WP walk through the laws spine;
   the frame quantifier, safety half, and pool transfer are the
   once-proven pipes. The postcondition `r ↦ 1` is the oracle's TRUE
   verdict — the same value the differential row pins against
   `go run`.

   **Cross-model strength, stated both directions (rewritten at the S3
   audit — the first version claimed "strictly stronger … ours adds
   interpreter-side safety", which is wrong: their `test_fun_ok` is an
   unannotated Iris WP, i.e. `NotStuck`, so THEIR lemma already
   asserts no-stuck safety on their model, and GooseLang makes racy
   accesses stuck, so race-freedom too — the matrix's own row T12).**
   No ordering between the two judgments is defined anywhere (theirs
   quantifies GooseLang's nondeterminism under their semantics
   assumptions; ours quantifies `execProg`'s modeled-schedule envelope
   at the TotalPins seed), so no strictly-stronger claim is made. The
   honest deltas: OURS is grounded in the executable, differentially
   tested interpreter (the same `execProg` the `go run` oracle
   validates, over the frontend's actual staleness-guarded lowering),
   with a first-order readout twin readable from base definitions;
   THEIRS is stated over a Rocq model no test executes. (Delta-review
   correction: "the frame-quantified `InitialSplit` pre" was first
   listed here as a delta — dropped: their `∀ Φ` Iris WP frames
   natively, so framing is no cross-model difference; and where the
   two framing notions differ, ours is the terminal-state-only
   `F.sub`, the weaker kind.)
   Neither side's R3-level judgment claims termination (our
   ∀-streams `Terminates` is the separate R2 pin; the composition is
   `…TerminatesNormally` below).

2. **The first-order readout twin** — on the SAME carrier as the
   judgment (the goldenReturnsTwoC precedent):

   ```
   ∀ fuel ch σf ch', execProg fuel nilEnv nilOut ch driver
     = .ok (.normal σf, ch') → loadLoc σf (.base ⟨0⟩) = .ok (.int 1 .int)
   ```

   readable from base interpreter definitions alone (deletion test:
   no Iris, no relation, no tactic machinery in the statement).

Composition with the R2 pins, stated precisely (delta-review
correction — the first sentence here said "BOTH … compose", which
overreached): the R2 termination pin plus the R3 spec's safety half
yields `TerminatesNormally` on the SEQUENTIAL carrier (the R2 pins'
carrier) — INSTANTIATED at the exemplar
(`compareNilToNilTerminatesNormally`, added at the S3 audit fix
round). That is the TERMINATION half only: the shipped readout twin
(form 2) is pool-carrier, so the two shipped theorems do not conjoin
directly (machine-confirmed at the delta review — feeding the
termination witness's `execStmt` run into the `execProg`-hypothesised
readout is a type error). The joint sequential
"completes-AND-verdict" form (the `goldenTotalReadout` precedent
shape) is derivable from the kit's `goSpec_seeded_readout` — the delta
review's probe compiled it — and is PARKED as P-S3-5 rather than
claimed.

**Non-vacuity**: the exemplar IS a discharge witness (a concrete
program with every premise discharged — the readout twin instantiates
`InitialSplit` at the concrete seed with `wf` by `decide +kernel`).
Axiom budget: `propext, Classical.choice, Quot.sound` (the standing
proofs-package budget; checked by the in-build Audit sweep).

**What stays sequential-degenerate, stated honestly**: `GoSpecC` here
is obtained by the conservation transfer (`goSpecC_of_goSpec`) — these
programs spawn nothing, so the pool run IS the sequential run
(`execProg_single_eq_execStmt`). The genuinely-spawning
frame-quantified `GoSpecC` remains slice 4's work; nothing here claims
it.

## 2. The wrapper/driver kit (shared, per-convention, not per-program)

Every oracle in the class shares the wrapper shape modulo three
parameters (the gensym target name `$cN`, the inner `FuncId`, the
wrapper `FuncId`). `Specs/GooseParityKit.lean` factors that:

- `goleanWrapperBody cname innerFid : Stmt` — the wrapper body as a
  function of the two names; per-unit an `example : … = by rfl` pins
  that the IMPORTED lowering's wrapper body is literally this term
  (if the frontend's wrapper generation drifts, the pin — and the
  staleness guard 1c5 before it — fails loud).
- `wp_golean_wrapper_body` — the wrapper walk, parameterized by the
  inner function's body spec (a wand delivering `$res0 ↦ .bool true`);
  covers init `$cN`, the inner call's frame entry/exit
  (`wp_call_enter_ret1` / `wp_frame_return₁` at a bool cell), the
  `if $cN` branch, `$res0 = 1`, return.
- `wp_golean_driver` — the driver statement's walk into the wrapper,
  ending `{r ↦ 0} … {r ↦ 1}` in the exit-form WP `goSpec_of_wp`
  consumes.
- `goSpec_seeded_readout` / `goSpec_seeded_readoutC` — the generic
  readout-twin derivations: a sequential `GoSpec` at the TotalPins seed
  yields the first-order readout on the sequential and pool carriers
  (the goldenReturnsTwo/goldenReturnsTwoC derivations, proven once
  instead of per-program).

The kit is CONVENTION-specific (imported-goose wrapper/seed shapes),
so it lives in `Specs/`, not in a general law module (layering
doctrine: general modules never encode target/corpus conventions).

## 3. The driver (`go_walk`) — what this slice adds, and what the tactic does not claim

The tactic core `go_walk` (proofs/GoLeanProofs/Tactics/GoWalk.lean)
exists since the proof-automation arc: a `DiscrTree` of
`@[go_walk_law]`-registered spine laws, most-specific-first, each step
fully backtracked, side conditions closed only by
`rfl`/`assumption`/`go_walk_simp`+`decide`/`omega` — a real semantic
obligation stops the walk instead of being guessed at. THIS SLICE DOES
NOT REWRITE IT. What this slice adds is coverage and the exemplar-first
usage pattern for the imported class:

- new UNREGISTERED laws where the class needs them, supplied per-walk
  with `go_walk_step` (`wp_new_value`, `wp_init_bool`, `wp_init_ptr`
  — the slice registered NOTHING into the `@[go_walk_law]` table;
  sentence corrected at the S3 audit — the first version said
  "registered spine laws", contradicting the registration lesson
  below);
- the kit lemmas of §2, so the per-program side-goal surface is the
  INNER body walk only;
- the scaling manifest (§4) with per-program disposition.

**Where the walk stops, by design** (the side-goal surface — supplied
with `go_walk_step law` and proven by hand at each site):

- allocating wide ops (`new`/`make` — `wp_stmt_op_apply_alloc_store`
  instances: the transition fact `happly` is a semantic obligation);
- store steps at non-int cells (`wp_assign_store`'s `hstore`);
- frame entries (`wp_call_enter_*`: `hfind` needs the program pin
  `GoCoreGS.prog GF = …`, which is a hypothesis of the surrounding
  walk, never global state);
- strict-op applications whose result the goal does not determine
  (`wp_strict_apply_pure/pin`'s `out` + `happly`);
- anything nondeterministic, invariant-carrying, or unregistered.

**THE TACTIC IS NEVER TRUSTED.** Every proof it produces elaborates to
a kernel-checked term; the in-build Audit gate pins the axiom set
(`propext, Classical.choice, Quot.sound` — no `native_decide`, no
`sorry`). Scope precision (S3 audit): `go_walk`'s DIRECT outputs are
Iris WP entailments (`wp_compareNil_body` and kin) — it is the
ASSEMBLED top-level statements (`…SpecC`/`…ReadoutC`, through the exit
pipe) that are stated in Surface vocabulary over the interpreter and
pass the deletion test; Iris and the tactic appear only in their
proofs. A `go_walk` bug can make a proof FAIL, never make a false
statement PROVABLE.

**Phase-2 outcome (the exemplar re-derived tactic-driven).**
`wp_compareNil_body`'s proof is now the `go_walk` walk — statement
byte-identical; the hand walk is preserved in full as
`wp_compareNil_body_hand` (the walk-architecture witness, and the
proof-robustness fallback). The realized side-goal surface for this
body, exactly as designed: the two pointer declarations
(`wp_init_ptr` — `hdef` is `∀σ` under the type pin), the
`defaultValue` nullary eval (same `∀σ` shape), the `new` alloc-store
(`wp_new_value`), the two pointer/bool cell stores
(`wp_assign_store`), and the comparison's apply
(`wp_strict_apply_pure` — `out` undetermined by the goal). Everything
else — 60+ machine steps — is the table.

**Registration lesson (recorded the hard way):** registering
`wp_init_bool`/`wp_init_ptr` as `@[go_walk_law]` moved the STOPPING
POINTS of the standing quorum walks (their `go_walk_step (wp_init …)`
supplies then faced already-advanced goals and timed out). The law
table is a GLOBAL tactic surface: a new registration changes every
existing walk script's behavior. Policy adopted: new laws default to
UNREGISTERED (supplied via `go_walk_step`); a registration is its own
deliberate change validated against every walk consumer. The two init
lemmas ship unregistered with this note recorded in their docstrings.

## 4. Scaling manifest

Moved to `docs/spec-parity-r3-manifest.md` (tracked; per-program
disposition — proved / side-goals-remaining / out-of-class /
not-attempted — over the imported sequential-oracle class). A program
the driver cannot finish is a VISIBLE row there, never a silent skip.

## 5. Designation candidates (D3 is CURATED — user sign-off at arc end)

Nothing is designated in this slice; `proofs/Audit.lean`'s list and the
44 designated statement files are byte-identical. CANDIDATES recorded
for the arc-end curation (one exemplar per feature class):

- `GoLean.ImportedGoose.SemanticsNil.compareNilToNilSpecC` (the
  designated-shape triple, §1 form 1);
- `GoLean.ImportedGoose.SemanticsNil.compareNilToNilReadoutC` (the
  first-order readout twin, §1 form 2).

The bulk R3 instances are axiom-pinned by the in-build Audit module
sweep (a real gate) and stated in Surface/interpreter vocabulary (a
TRUE property that no standing gate checks for undesignated theorems —
the statement-TCB walk covers the designated list only; hand-verified
this slice, recorded as a limitation in the manifest header), and are
undesignated, listed in the manifest.

## 6. Parking ledger (user-scale items; AFK posture)

- **P-S3-1 — Designation curation (charter D3, user-owned).** The two
  exemplar candidates (§5) await the arc-end sign-off; nothing
  designated meanwhile. NOT a free flip (wording corrected at the S3
  audit — "reversible" understated it, the F4 def-only-hoist precedent
  applies): designating requires hoisting the statements' defs into a
  DEF-ONLY, core-import-only module so Challenge's trusted closure can
  import them (`ForkJoinTargets`/`Statements` pattern; ci pins
  Challenge's imports, so skipping the hoist fails loud, never
  silent). The S3 fix round moved six declarations out of the
  `GoLean.Surface` namespace into `GoLean.ImportedGoose` (namespace
  hygiene: the four convention defs AND the two readout-derivation
  THEOREMS — count corrected at the delta review; the theorems were
  the more notable squatters), but they still LIVE in the
  Iris-importing kit module, and
  `nilLowered`'s home (`ImportedGooseNil.lean`) carries theorems — the
  def-only split plus Challenge/Solution/judge-config/Audit wiring is
  the real designation cost, owed at curation time.
- **P-S3-2 — Backfill pinned lowerings for the remaining 76 unpinned
  imported units (71 with ≥1 R1-green row — figure recounted at the
  fix round; this bullet first said "~72 R1-green", the stale
  pre-recount number, corrected at the delta review)?** Each pinned
  term is the R3 statement's subject AND
  joins the ci 1c5 staleness guard + pins registry (a standing
  maintenance surface per unit). Scaling R3 across the corpus needs
  them; how many, and whether the pin generator should be promoted
  from the `.tmp` mkpins helper to a tracked script, is a
  cost/coverage policy call → user. Meanwhile: the 6 pinned units
  carry the class; the manifest names the population.
- **P-S3-3 — Keep or trim the duplicated hand walk
  (`wp_compareNil_body_hand`)?** Kept as the walk-architecture witness
  and tactic-robustness fallback; it duplicates one body proof's build
  cost. Default keep; user may trim at arc end.
- **P-S3-4 — `go_walk_step` ergonomics (tactic infra, not soundness):**
  a supply applied at the WRONG configuration burns the declaration's
  heartbeat budget in `isDefEq` (the constrained-elaboration path is
  unbudgeted) instead of failing crisply. Fixing it touches
  `Tactics/GoWalk.lean` (shared tactic infrastructure used by the
  designated summit's proof); parked rather than edited mid-slice.
  Soundness is unaffected either way (the tactic is untrusted).
- **P-S3-5 — The joint sequential "completes-AND-verdict" form (the
  `goldenTotalReadout` precedent shape) for R3 rows.** The shipped
  pair is `TerminatesNormally` (sequential carrier, the R2 pins')
  + the pool-carrier readout twin, which do not conjoin directly
  (§1's carrier note). The sequential joint statement is derivable in
  a few lines from the kit's `goSpec_seeded_readout` (the delta
  review's probe compiled it); whether to ship it per-row, ship a
  pool-carrier `TerminatesNormallyC` instead (via
  `execProg_single_eq_execStmt`), or leave the two halves as stated
  is a spec-idiom call → user at curation. Parked, not claimed.

## 7. Build log

- **Exemplar (commit 1).** `testCompareNilToNil` hand-proved
  end-to-end; kit (`GooseParityKit.lean` — wrapper/driver walks +
  generic seeded readouts); `wp_new_value` law + witness same-commit.
  File-naming constraint discovered: `Specs/ImportedGoose*.lean` is
  `check-imported-pins`' PIN-MODULE glob (its completeness cross-check
  fails on any non-pin module matching it) — the R3 modules are named
  `GooseParity*` to stay off it, recorded here and in the kit header.
  Axioms `[propext, Classical.choice, Quot.sound]` on all three
  deliverables; full `scripts/ci` PASS, zero drift — all 1465 corpus
  ids match the tracked baseline on `result`+`stage` per id (the
  recorded regression signal — `detail` is deliberately outside it;
  1351 PASS / 114 recorded FAIL. The earlier "1465/1465" shorthand
  read like an all-pass claim, corrected at the S3 audit; the interim
  "bit-identical" wording overstated the comparison, scoped at the
  delta review).
- **Phase 2 (commit 2).** The exemplar body re-derived `go_walk`-driven,
  statement byte-identical; hand walk preserved
  (`wp_compareNil_body_hand`). Registration lesson recorded (§3):
  `wp_init_bool`/`wp_init_ptr` ship UNREGISTERED after registering
  them broke the standing quorum walks' stopping points.
- **Phase 3 (commit 3).** Scaled across the class: 4 more nil oracles
  + semantics/block, each the full D1 pair — R3 count 6 proved / 1
  out-of-class (short-circuit `&&` law gap) / 5 not-attempted with
  reasons — manifest `docs/spec-parity-r3-manifest.md`. (This entry
  originally said the 4 nil oracles were "all in Perennial's proved
  37" — corrected at the S3 audit: ONE of the four is upstream-Qed,
  THREE are upstream-Aborted; see the manifest's per-row upstream
  column.) Empirical driver notes: pure INT
  applies walk themselves (`go_walk_side`'s `rfl` computes them);
  comparisons through `valueEqFuel`'s fuel literal do not (supplied
  via `go_walk_step` — elaborator-side reduction cost, not a
  soundness line). Every store/alloc/init side-goal discharged with
  the same three-lemma simp vocabulary (`storeLoc`,
  `normalizeValueForTy*`, `typeResolutionFuel`), which is what the
  next movement can template.
- **S3 audit fix round (2026-08-10; ~4 surviving majors, all
  claims/records — no surviving MAJOR was a code or proof defect;
  two minor/note items were record defects fixed partly via
  proof-code edits, scoping corrected at the delta review).**
  (1) THE PARITY-RECORD
  CLUSTER: upstream ground truth measured (28 proved / 36 stated
  `test_fun_ok`, 7 Abort, 1 Admitted; nil.v = 3 Qed + 3 Abort) — the
  manifest rewritten with a per-row upstream-status column, the
  denominator corrected at its ORIGIN
  (`docs/2026-08-07_goose-comparative-scoping.md` B.1, pre-existing,
  outside the slice range) and at every tracked restatement
  (comparison matrix, end-of-buildout report, charter basis + slice-3
  record, this note). The corrected story is stronger in one
  direction and weaker in the other, both now recorded: three of our
  proved rows discharge oracles upstream ABORTED, and our one
  out-of-class oracle is one THEY prove. (2) The cross-model
  "strictly stronger" claim rewritten to the verifier's accounting
  (their `NotStuck` WP already carries no-stuck safety on their
  model; deltas stated both directions, no ordering claimed). (3)
  WITNESS DISCIPLINE: the dangling `wp_testCompareNilToNil_body`
  citation fixed to `wp_compareNil_body`; `wp_init_bool`'s false
  witness sentence made TRUE by using the law at the kit wrapper's
  call-target declaration; all three new laws + their witness walks
  wired into `proofs/Audit.lean`'s witness registry (the deletion
  tripwire now covers them). (4) The R2+R3 composition instantiated
  (`compareNilToNilTerminatesNormally`). (5) Records: population
  recount (82 units, not 78 — command cited in the manifest),
  1465-shorthand expanded (1351 PASS / 114 FAIL), the §3
  "registered spine laws" sentence corrected (nothing was
  registered), the deletion-test sentence scoped to the ASSEMBLED
  statements, P-S3-1's "reversible" replaced with the F4 hoist cost,
  and the kit's convention defs moved off the `GoLean.Surface`
  namespace into `GoLean.ImportedGoose`.
- **Delta-review polish round (2026-08-10; zero surviving
  critical/major — record-precision minors + notes, applied per the
  verifiers' accountings).** Population precision: the
  no-pinned-lowering row recounted to 26/36 statements (21/28 Qeds)
  R1-green-pinnable, with the FOUR upstream-Qed frontend-blocked
  oracles (`testStructUpdates` + the three type-equality ones, the
  short-circuit-operand quarantine) carved into their own
  out-of-class-at-R1 row — and the deltas-against-us count corrected
  to FIVE (they-prove/we-don't), named in the manifest and the
  charter. Stale figures: P-S3-2's "~72 R1-green" → 76/71; the
  buildout log's historical "9-pins-vs-37" line annotated in place;
  the origin note's "every tracked restatement" completeness sentence
  replaced by the enumerated sweep. Strength text: "frame-quantified
  pre" dropped from the deltas (their `∀ Φ` WP frames natively;
  where the notions differ ours is the terminal-state-only `F.sub`).
  Composition: `compareNilToNilTerminatesNormally` annotated as the
  TERMINATION half on the sequential carrier, the carrier gap to the
  pool-carrier readout twin recorded (machine-confirmed type
  mismatch), the joint sequential form PARKED as P-S3-5. Registry
  honesty: the witness block's header now states the mechanism's
  scope (name-existence/deletion tripwire; witness-citation drift
  stays the audit's job) and relabels `wp_golean_driver` as a
  deletion anchor, not a law witness; the kit's redundant re-opens
  removed; the "four convention defs" count corrected to six
  declarations (four defs + the two readout theorems). Drift
  phrasing scoped: baseline comparison is `result`+`stage` per id,
  not bit-identity. This entry's fix-round header above was rescoped
  the same way ("no code or proof defect" → no surviving MAJOR was).
