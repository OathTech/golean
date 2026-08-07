# TODO

See `docs/roadmap.md` for the phased project roadmap. This file tracks tactical
backlog items.

## THE work queue: from slice to platform (updated 2026-07-21, post Arc B)

**DONE and merged**: the vertical slice (arcs `slice-l5-pure` +
`slice-call-frame` — `slice_adequate` closed); structure-hardening + the
proofs module split (`docs/2026-07-20_repo-structure-audit.md` worked).
**DONE on branch `eval-totalization` (Arc B, item 6 — pending audit+merge)**:
Eval totalized (GoCore `partial`-free); the interpreter⇄relation
correspondence proven over the full slice-shaped fragment *including calls*
(`interpreterSound_frag`, axiom-clean). Design of record + the three
discovered divergences D1/D2/D3:
`docs/2026-07-21_eval-totalization-correspondence.md`.

**Next arcs, sequenced by durability** (durability test: per-fragment
mechanism vs per-program artifact; decided with user 2026-07-21):

- **Arc C — Rel completion (D1+D3+D2-proper, ONE slice).** Semantics risk
  class (trusted-relation edits, three-auditor bar, one downstream re-proof
  wave through `wp_seqn`/witnesses/inversions/T1-T2 instead of three):
  D1 seqn-splice rule (relation currently cannot run ANY frontend-lowered
  program with a declaration — the deepest gap); D3 panic-propagation rules
  for `eqCmp`/`deref` operands (then `interpreterPanic_frag`); D2-proper
  (stash result *locations* in `Cont.frame`, erasing the shadowing hazard and
  the fall-through gap, retiring the `avoid`-discipline). Land BEFORE widening
  the fragment — every construct added first doubles the re-proof.
- **Arc D — the exit infrastructure (IN PROGRESS on `exit-infra`; 4 commits).**
  DONE: the widening-loop doc (step-0 intended proofs + negative instances);
  2b CLOSED — `go_heap_adequacy` on `wp_strong_adequacy_gen` (the spike
  resolved as the good case: fits our bundle as shipped), `steps_erased`,
  `slice_adequate_computes`, and **`slice_interp_computes_two` PROVEN**
  (computed-somewhere form: every terminating run of the slice program ends
  with SOME cell holding int 2, address existential — no Iris, no relation
  in the statement; see the SCOPE CORRECTION below);
  `NegativeSpecs` module (stuckness pins + divByZero premise pin); the
  golden-lowering mechanism — `sliceLowered` (the frontend's ACTUAL lowering
  as a Lean literal), `scripts/check-golden` (both-links staleness guard, in
  ci — 10 steps now), fragment proofs + `golden_interp_run_in_relation` over
  the real lowered term; `wp_block_nil` law; **the golden WP walk DONE
  (2026-07-21)** — `Specs/GoldenSliceWP.lean`: `wp_incLowered_call` +
  `wp_incViaCallLowered_call`/`_ret2` + `golden_adequate_computes` +
  **`golden_interp_computes_two` PROVEN** over the frontend's actual
  lowering (`sliceLowered_funcs` is the kernel-checked bridge; first WP use
  of the D1 splice branch via `seqCont_splice`; `wp_inc_via_ptr_env` added
  for pushed-scope lookups). The "hand model ≈ lowering" footnote is retired.
  **SCOPE CORRECTION (2026-07-21, user-driven): the `*_computes` theorems
  prove "computed-SOMEWHERE" (existential address), NOT "returns 2" — a
  theorem's value is exactly its statement, and the lowering target is
  claimed only by the pinned-observable form. Design of record for the fix:
  `docs/2026-07-21_native-spec-surface.md`** — the native spec surface
  (deep-embedded SL over heaplets + once-proven reflection/extraction
  boundary; Iris strictly internal; per-program work = shape checks + WP
  walk + generic exit theorem; refutation twins fall out as corollaries).
  Staging §5 there; the golden WP walk is reused as-is. (Arc D merged
  2026-07-21 @ 4cf8052 after a 3-Opus audit — zero semantic findings, all
  confirmed findings = pre-D8 overclaim language, fixed.)
- **Arc `spec-surface` (IN PROGRESS on `spec-surface`): THE LOWERING TARGET
  IS CLOSED in its pinned form.** Landed (2026-07-21): step 0 —
  `Surface.lean` (Iris-free Layer S, ci-linted: Heaplet/HProp/sat/GoTriple
  + intended statements); stage 2 — `go_heap_adequacy_own` (initial-heap
  `↦` handover via `genHeap_init_names`); stage 3 — `SurfaceBridge.lean`
  (`reflect`/`extract` by full `HProp` induction; `∗` extraction gets
  genuine disjointness from `DFrac` validity; map-API agreement lemmas);
  stage 4 — `goTriple_of_wp` (the generic exit theorem; per-program work =
  shape checks + WP proof, nothing else); stages 5–6 —
  `Specs/GoldenSurface.lean`: **`goldenTriple`
  ({r ↦ 0} r=incViaCall() {r ↦ 2}), `goldenReturnsTwo` (output cell at
  address 0 holds 2 — plain register, no ∃), `goldenNotThree` (the twin,
  a two-line corollary) ALL PROVEN** over the frontend's actual lowering.
  **Statement-shape trio (2026-07-21, after the spec-space discussion —
  `docs/2026-07-21_spec-space.md`): frame closure + progress DONE** —
  `GoTriple` is frame-closed (quantified-testcase form; frame provably
  untouched; `wp_frame_l` carries it inside `goSpec_of_wp`, per-program WP
  obligation unchanged), `Progress` + `GoSpec` bundle safety with the
  triple, `goldenSpec` proven; **(3 of trio) `GoFuncSpec` DONE** — the
  function-level quantified-testcase form (v1 unary int result; return
  observed at the caller's target cell, the call protocol's frame-exit
  observation; `(T, error)` queued behind the interface widening),
  `goldenFuncSpec` proven ("incViaCall() needs no heap and returns 2" —
  the golden walk unchanged throughout: three direct applications across
  four statement shapes). **THE TRIO IS COMPLETE.**
  REMAINING: the arc's audit ask (Opus reviewers) + merge sign-off; then
  future widenings per the design notes (heaplet-canonical GoTriple
  dropping the `HeapFrag` side condition, `var x ⇓ v` sugar, arity-general
  GoFuncSpec + runner-equivalence lemma).
  **Invariant readout: DONE** (arc `invariant-readout`, 2026-07-22; design
  of record `docs/2026-07-22_invariant-readout-design.md` incl. §7 build
  record): `GoInvariant` = Verdi-style invariance over `Rel`;
  `goldenInvariant` proven ("cell 0 ∈ {0,2} at EVERY reachable
  configuration") through `goInvariant_of_wp` → `go_heap_invariance` →
  iris-lean `wp_invariance`; walk refactored once
  (`wp_incViaCallLowered_frame`, pluggable frame exit), owned form
  rederived statement-unchanged. Key finding: `wp_atomic` inapplicable to
  whole-machine `Config`s — invariants open inside the lifting fupd slots
  (`wp_store_step₂_inv`). QUEUED from the arc: frame-subsumption corollary
  (needs an HProp-of-heaplet fold), multi-invariant namespaces (v1 =
  `nroot`), ghost/abstract-state machinery (design note §3 — the
  linearization-point idiom for multi-step protocol updates).
  Original scope note:
  (1) 2b: `go_heap_adequacy` on `wp_strong_adequacy_gen` — initial-heap `↦`
  handover + final-state extraction; the exit door every future state-property
  spec uses (the raft target is a state property). Known unknown: ergonomics
  of iris-lean's strong-adequacy form. (2) Golden-lowering mechanism:
  elaboration-time decode of checked-in frontend JSON + CI staleness diff;
  reprove the slice spec against the real lowered term. Finish line: *the
  frontend-lowered program, executed by the differentially-validated
  interpreter, terminates safely with `r = 2` in the final heap* — every span
  kernel-checked.
- **Arc E→ — widen per the ladder** (`docs/2026-07-19_vertical-slice-plan.md`
  §Widening): while-invariant WP rule (slice B) → **BUG-001 fix + the
  85-failure triage immediately before structs/arrays** → quorum-threshold
  slice C. F4 concurrency-model note before any goroutine machinery; F5
  target-theorem skeleton rides along. Arity-general call laws when the
  ladder first needs them.

Per-program demo artifacts (golden file for slice.go, `r = 2` instance,
`sliceProg` correspondence witness) are bounded to ONE witness per mechanism —
they double as the non-vacuity discharges our gate requires.

## Enumerator optimization layer (deferred backlog, 2026-08-07)

Record only — no implementation scheduled. Design of record:
`docs/2026-08-04_membership-lane-design.md`, section "Deferred: the
enumerator OPTIMIZATION layer (2026-08-07)" (provenance: user
discussion 2026-08-07). Layers, each behind the BOTH-EXPLORERS
adoption gate (optimized vs reference explorer, identical observation
sets on every tractable instance) and each with a named soundness
obligation:

- [ ] Verified POR — race-detector footprints as the independence
      oracle; NPDRF mover lemmas as its eventual proof.
- [ ] Symmetry reduction — decidable Config equality; the
      id-relabeling lemma is the soundness obligation.
- [ ] Preemption-bound-as-metadata — certificates must NAME their
      bound (bounded tree, never silently the full one).
- [ ] State memoization on canonicalized MultiConfig — requires the
      decidable-equality/canonicalization layer first.
- [ ] PCT / portfolio sampling beyond enumeration scale — sample
      source only, never certification.

## Epistemic hardening / pipeline error-resistance (2026-07-19, priority #0)

Plan of record: `docs/2026-07-19_pipeline-error-resistance.md` (stage-by-stage
gates vs omission+commission; adapted from the ACL2Lean playbook + a two-advisor
zero-drop review, see its 2026-07-20 section). Goal: the infra guides an
error-prone agent to correctness — build-enforced gates over discipline.
**Done:** `proofs/Audit.lean` in-build axiom gate + EXHAUSTIVE 1970-decl sweep;
`scripts/ci` one-command gate, now ENFORCED by CI (fast on push/PR, full
differential nightly/dispatch); honest-scope baseline diff; re-pin laundering
guard; `docs/BUGS.md` cross-check with fixed→PASS symmetry + untriaged-count
ratchet (`baselines/untriaged-count`); feature-coverage check.
**Next:** item 4 end-to-end adequacy witness + close `hstore`; item 5 Eval
big-step totalization. **Deferred hardening (real work items, not plumbing):**
corpus mutation/tamper testing; sub-feature read/write tags; wider observation
channel; exact panic-message matching.
**Ratchet — concrete backlog:** 85 baseline fidelity failures (77
lean-observation + 8 differential) not yet explained by a BUG entry. Inspect the
exact ids with `scripts/check-bugs.sh --list`; triage into `docs/BUGS.md` over
time (the check warns until 0). Many are array/struct value-semantics cases that
likely share BUG-001's address-lowering root cause — fold them into BUG-001 as
they're confirmed. Separately, `scripts/check-coverage` lists 33 all-failing
feature tags = unimplemented features (roadmap, not defects).

## Directional audit follow-ups (2026-07-19)

Full findings + dispositions: `docs/2026-07-19_directional-audit-findings.md`.
Verdict: on-track-with-corrections. Fixed same-day: `wp_deref_store` vacuity /
docstring (+ `wp_deref_store_ref` witness), non-vacuity gate codified in
CLAUDE.md, stale Correspondence header. Open items:

- [ ] **F1 (major, was HIDDEN) — struct-field / array-element WRITES are stuck.**
  `b.n = 7`, `a[1] = …`, `p.n = …` fail closed at `lean-observation` ("expected
  address value, got struct"). Frontend lowering bug: `tools/nativefrontend/emit.go`
  `fieldBase`(~736) and `emitAddressOf` SelectorExpr(~814) emit a value-read base
  where the address path needs `.ref`/`.fieldAddr`. GoCore has the primitives.
  Fix the lowering when structs enter the proof frontier; meanwhile fix the
  `docs/native-frontend-goal.md` overclaim that "field/index access" works (reads
  only). On the north-star path (raft mutates struct fields pervasively).
- [ ] **F4 (major, strategic) — concurrency design note BEFORE fork machinery.**
  **DECIDED 2026-07-22 — design of record
  `docs/2026-07-22_f4-concurrency-model.md`:** fine-grained shared-memory
  concurrency (confinement-only REJECTED); memory-op granularity, SC,
  atomics as SC steps, plain races out of scope (DRF-SC condition stated
  explicitly); **big-step rules DELETED in the reshape, no interop shim**
  (user directive); interpreter becomes iterated stepFn (T1/T2
  correspondence dissolves to per-rule lemmas); Choices is the native
  controlled-scheduler hook (Coyote/PCT/P-style fuzzing = Choices
  generators); staged plan R0–R5, reshape BEFORE structs/arrays.
  Remaining open in F4's original scope: the multi-node/N-node network
  model for quorum safety (distinct from intra-node goroutines — don't
  conflate; decided at F5 time). **F4 machinery is BLOCKED by BUG-002
  (`docs/BUGS.md`, 2026-07-22): expression-step atomicity.** `ExprR` is a
  premise relation, so a multi-read condition is ONE atomic `Rel` step —
  coarser than Go's interleaving. Sequentially sound (no call exprs in
  the IR — `docs/2026-07-22_arc-e-while-invariant.md` §2′); carried into
  a concurrent `Rel` it under-approximates schedules and over-licenses
  invariant opening — theorems provable that are false of real racy Go,
  with no self-enforcing DRF scope. Goroutine rules must not land until
  F4 picks a fix (expression small-step refactor / v1 channel-confinement
  model / rejected law-discipline — see the BUG-002 entry).
  **Charter extended 2026-07-22:** F4 must
  include a fault-model section per `docs/2026-07-22_fault-model.md`
  (taxonomy panic/fatal/deadlock/race-scope/exhaustion; what `Rel`
  represents; what the oracle discriminates — fault *identity*, not just
  existence; guardrail suites per class BEFORE goroutine machinery; the
  DRF/SC scope condition on soundness claims stated explicitly).
- [ ] **F5 (major) — size the target theorem.** Draft a skeletal multi-node
  quorum-safety target (state space, message/failure model, invariant statement)
  so the A→B→C widening ladder aims at something explicit, not just "raft".
  **Bar refined 2026-07-21 (user): "the Verdi results, but on real code."**
  Decomposition: (tier 1, committed — known-solid machinery) the Raft safety
  invariant stack (election safety, log matching, leader completeness,
  state-machine safety) capped by linearizability of the replicated service —
  what Verdi actually proved, but attached to real frontend-lowered Go via the
  differential+correspondence chain instead of Verdi's model/shim gap; (tier 2,
  explicit stretch — own machinery decision) convergence/liveness under
  fairness, which Verdi did NOT prove and which is a known weak spot of
  step-indexed logics (cf. Trillium/Fairis in Coq-land) — never silently
  bundled with tier 1. Network/failure model (drop/dup/reorder/delay) is one
  more nondeterminism source, architecturally the `Choices` move again
  (relation over-approximates the adversarial scheduler, executable side
  instantiates) over an N-node model — this is F4's decision. Plus
  ghost/history state for linearizability and the GoCore⇒abstract-raft
  refinement layer (master plan D4-9).
- [x] **F3 (leverage) — Eval big-step totalization: DONE** (arc
  `eval-totalization`, 2026-07-21; design of record
  `docs/2026-07-21_eval-totalization-correspondence.md`). GoCore has 0
  `partial def`s; `interpreterSound_frag`/`interpreterPanic_frag` are proven
  fragment-scoped theorems and the former is load-bearing in the surface
  exit pipe (`goSpec_of_wp`). Residue (not a standalone arc): the blanket
  unconditional `interpreterSound` stays false-as-stated while the
  interpreter is richer than the relation (e.g. string `add`); each Arc E
  fragment widening extends relation + correspondence in lockstep.
  (Entry corrected 2026-07-22 — was stale, predating the totalization arc.)

## Current Priority Sequence

**Authority: `docs/2026-07-18_master-plan.md` §8** (the reordered sequence, after
the three-reviewer adversarial review; full findings in
`docs/2026-07-18_review-findings.md`). This section is a status mirror — keep the
narrative in the master plan, not here.

The trust chain: real Go → executable interpreter (differentially validated vs
`go run`) → **nondeterministic relational semantics** (the Iris proof authority)
→ Iris-Lean proofs. Two artifacts on purpose (the relation must over-approximate
Go's nondeterminism, so it can't be a total step function; the interpreter is its
oracle-instantiated executable projection).

Done:

- [x] Bugs → differential tests → fixes; drop Gobra; honesty fixes.
- [x] **`Ops.lean` fully total** (zero `partial def`) — the review's actual
  blocker; makes the relation's premises unfoldable. Fuel decision in
  `docs/2026-07-18_totality-fuel-decision.md`. Needed under any architecture.
- [x] Interpreter **expression/value layer** total (structural lower cluster).
- [x] Master plan written + attacked by three reviewers → **reorder** (below).

Cheap decisions now locked (master plan §8, C3):

- [x] **D1** — target adequacy is the not-stuck/progress form (turns every
  "unsupported/fuel = stuck" gap from false-safety-unsound into proof-blocking).
- [ ] **D2** — map-mid-mutation semantics (Perennial read-invalidation vs
  snapshot-permute) + a per-nondeterministic-construct completeness artifact.
  *Bites at the first nondeterministic feature (step 3), not before.*
- [ ] **D3** — correspondence shape (step-indexed/prefix or small-step oracle
  interpreter) so it covers prefixes of nonterminating runs. *Bites at step 3.*

In order (reordered — Iris spike front-loaded):

1. [x] **Throwaway Iris spike** — DONE, **VALIDATE**
   (`docs/2026-07-18_iris-spike-result.md`; project at `../iris-spike/`). Bare
   `Language` CK machine (no ectx) + real `wp_store` via `wp_lift_atomic_step`,
   axioms clean. Toolchain builds offline at 4.31; CK shape seats on bare
   `Language`; not-stuck adequacy (D1) is the library's native form.
2. **Reshape A** — heap out of `Config` into Iris `State`
   (`docs/2026-07-18_reshape-a-design.md`):
   - [x] **Split done.** `Config` is now state-free (control + cont = Iris
     `Expr`); `Step` relates `(Config, ExecState)` pairs. `ExecState`/`Ops`/
     interpreter untouched (no adapter needed); proven correspondence instances
     re-proved. golean green.
   - **A2 — Iris port** (in the in-repo `proofs/` package; golean core stays
     iris-free — verified root build is 36 jobs, dependency-free manifest):
     - [x] Bump golean 4.29→4.31 (clean: build/tests/quorum green, 0 warnings).
     - [x] In-repo `proofs/` Lake package (iris-lean as a **pinned git dep**,
       not an external path); bare `Language` instantiated on the real
       `Config`/`ExecState` (`ToVal`/`PrimStep`/`val_stuck`, no sorry).
     - [x] **3a** — real WP law (`wp_seqn`) over GoCore's actual `Step`, via
       `wp_lift_pure_det_step_no_fork` (invariant+credit cameras *assumed*, not
       constructed; trivial StateInterp; `IrisGS_gen` derived). Axioms clean, no
       sorry. Iris WP machinery validated on the real relation.
     - [x] **3b.1** — gen_heap wired to GoCore's real heap (keyed by base-address
       `Nat`; `GoCoreGS` class, `heapToMap` projection, `StateInterp` via
       `genHeapInterp`, `IrisGS`). The `↦` connective over GoCore's heap now
       compiles; `wp_seqn` re-proved under the real state interp. No sorry.
     - [x] **3b.2 — `wp_assign` is now a USABLE law** (CEK reshape, 2026-07-19,
       `docs/2026-07-19_cek-reshape-plan.md`; closes audit D2-4/D2-5). The
       unsatisfiable `hred` is gone: locals moved from `ExecState` into the
       control `env` (CEK), so the target resolves against `env` — **fixed in the
       WP goal, not the quantified state**. The law's premise is now the pure,
       dischargeable `LocalEnv.lookup env id = some (.base a)` plus ordinary
       rhs/store facts; **`wp_assign_lit` discharges them** for `x = intLit n`
       (payoff check). Heap core unchanged (the two bridge lemmas, `wp_lift_step`
       non-value successor). Axiom-clean `[propext, Classical.choice, Quot.sound]`.
       This is what closes #23; see also 3b.4 (now subsumed).
     - [~] **3b.3 — read law + adequacy, both scope-limited** (audit D1-1):
       - `go_adequacy` — `adequate .NotStuck`, real functor bundle, axiom-clean —
         **but covers only non-panicking runs**: `.panicked` has no outgoing
         `Step` in the Iris layer, so it counts as *stuck*, and any Go panic makes
         `Hwp` unprovable. Admitting panicking terminals (panics-as-values/obs) is
         deferred.
       - `pointsTo_loadLoc` — read law (`a.id ↦ cell` ⟹ `loadLoc … = ok value`).
         Genuinely a lemma, not a WP; correct as stated (no bare-deref `Step`).
     - [x] **3b.4 — SUBSUMED by the CEK reshape (3b.2).** The plan here was to
       model `ExecState.locals` in the state interpretation (needing a locals
       camera). The reshape took the **better** route the Goose/Perennial
       investigation surfaced: put locals in the **control** (`Config.env`), not
       the state, so resolution is a pure fixed-`env` fact with **no camera and no
       `∀σ`**. The audit's "locals split across `Config.frame` + `ExecState.locals`"
       concern dissolves: the relation's locals live only in `Config`
       (`.exec`/`.returning` env, `Cont.seq`/`loop` env), and `ExecState.locals`
       is now solely the interpreter's, serving as the correspondence bridge
       `σ.locals ≈ Config.env`. Env-in-control is also the concurrency prerequisite
       (per-goroutine locals). No new scope-push/pop WP laws were needed — scope is
       the continuation's env, discarded at `seqDone`.
3. **Reshape B** (`docs/2026-07-19_reshape-b-oracle-externalization.md`):
   - [x] **Slice 1 — oracle externalization.** `choices` removed from
     `ExecState`; the interpreter threads `Choices` externally through the
     statement cluster + `execAppendSlice` (expression layer untouched);
     `Choices.consume` replaces `ExecState.consume`; entry points seed the
     stream. Relation + proofs needed zero change (the field was dead there).
     `interpreterSoundStatement`/`interpreterPanicStatement` now thread `ch → ch'`
     externally, so the relation compares oracle-free states (removes §8 C1's
     obstruction). **Validated:** core+proofs build green; `gocore-eval-tests`
     40/40 unchanged; append + range differential slices **identical** failing
     sets to baseline (quorum 37/39, the 2 fails are known frontend-blocked
     interface dispatch, not regressions).
   - [ ] **Slice 2 — existential `mapRange` rule** in `Rel.lean`: a rule relating
     a map-range loop to *any* iteration order (relation over-approximates; the
     interpreter instantiates via the external stream).
   - [ ] **Slice 3 — correspondence for `mapRange`**: the interpreter's
     oracle-instantiated iteration is one projection of the existential rule.
   - [ ] Then resume interpreter totality (paused, below) against the corrected,
     oracle-external shape.
4. [ ] Scope the merge invariant to the **proof frontier** (quorum's feature set,
   not every interpreter feature); guardrails; breadth.

**Paused** (was "next", now correctly deferred): finishing the big-step
`execStmt`/upper-cluster totalization — its correspondence covers only
terminating runs and goes false once `mapRange` runs with the oracle in state
(master plan §8 C1). Resume in step 3 against the reshaped, oracle-external
interpreter.

Deferred until the foundation is set: native interface dispatch (quorum 39/39),
feature breadth up the raft ladder, `slices.Sort` extern + input fuzzing.

## Goose/Perennial comparison (standing matrix)

- DISCHARGED (2026-08-07): the old "Goose/Perennial Design Mapping" entry is
  realized as the STANDING comparison matrix `docs/goose-perennial-comparison.md`
  (rev-pinned rows, CAP/DEL/LAT classification, per-arc maintenance
  contract), seeded from `docs/2026-08-07_goose-comparative-scoping.md`
  Part A per its Part-C proposal. Earlier area-by-area notes remain in
  `docs/2026-07-19_goose-perennial-mapping.md` and the 2026-08-06
  concurrency research notes; new comparison rows land in the matrix.
- Goose-parity buildout: charter DRAFTED, awaiting user blessing —
  `docs/2026-08-07_goose-parity-charter.md` (phase-1 import of the 87
  importable Goose/Perennial test files up the rung ladder;
  parking-ledger discipline; escape hatch). NOTHING starts until the
  user blesses the charter and sets the standing goal — a decision
  item at the channels-arc merge sign-off.

## Differential Execution

- Keep Gobra-specific handling in `GobraToIR`; semantic work belongs in GoCore unless it is purely frontend lowering.
- Current iteration priority after the core coverage spike: use
  `scripts/coverage run ...`/`scripts/diff-one ...` as the conformance loop and
  fix cases that reach a Go-vs-Lean differential mismatch before chasing cases
  blocked in Gobra export or JSON decoding.
- Track frontend-blocked corpus rows separately from GoCore semantics work.
  Recent focused probes show `delete`, `clear`, `range int`, richer method
  expressions/auto-addressing, floats, complex numbers, and `min`/`max` are
  often blocked before Lean at the frontend; do not count those as
  GoCore semantic failures until the native frontend can produce GoCore for them.
- Promote cases from `Corpus/challenges/semantic-edges/` into the active
  native/Lean differential suite one feature at a time. Keep the challenge
  corpus runnable by `scripts/semantic-edges-challenge-smoke`, but do not treat
  it as a supported-semantics claim until cases land in
  `Corpus/coverage/manifest.tsv`.
- Keep `Corpus/coverage` comprehensive. Do not remove cases because the
  frontend or semantics fails; let `scripts/coverage` report the failing stage.
- Do not maintain Gobra variants of coverage inputs. The canonical Go source is
  the input to both `go run` and the frontend/Lean path.
- Expand `Corpus/coverage/negative/compile` with static Go errors. Runtime Go
  errors that execute and panic belong in the differential manifest with
  `expected_status=panic`.
- Replace stringly typed evaluator failures with structured `GoError` values and
  stable observations. CLI classification must not depend on matching error
  message prefixes.
- Treat `unsupported` and `stuck` as failures by default. A differential case may
  expect them only with an explicit manifest reason.
- Use a structured observation parser/comparator for Go and Lean output instead
  of raw JSON string comparison.
- Add timeouts/fuel for Gobra export, Go execution, Lean execution, and Lean
  builds used by the harness.
- Prevent stale or cross-test artifacts by tying generated Gobra JSON to source
  hashes and using per-run temporary artifact directories with atomic publish.
- Keep `scripts/diff-coverage` same-source: Go execution and frontend/Lean
  execution must consume the same canonical Go file.
- Preserve the executable corpus contract: every row in
  `Corpus/coverage/manifest.tsv` names a subject function in the canonical
  `main.go`. Successful cases print JSON from `main`; expected panic cases let
  Go panic and are normalized by the top-level runner.
- Investigate the current Gobra export blockers surfaced by the same-source
  corpus: local addressability for `&x`/array slicing from arrays, pointer
  receiver method lookup, string pointer assignment, and variadic nil-slice
  comparison.

## Hardening Phase

- Extend type-directed equality for interfaces, function values, and exact
  dynamic comparability panics once those value forms exist.
- Add a small relational GoCore semantics skeleton before concurrency or
  Iris-facing proof rules.
- Keep the executable interpreter factored so it can be related to a future
  relational GoCore semantics for Iris-Lean. The interpreter is for testing; it
  should not be the only semantic authority.
- Thread structured errors through GoCore:
  `panic`, `unsupported`, `stuck`, and `internal`.
- Classify nil pointer dereference and Go-defined runtime traps as `panic`, not
  `stuck`.
- Extend the integer/string model beyond the current fixed-width and byte-string
  slices: constants, rune iteration/conversions, broader conversion families,
  more integer edge cases, and exact architecture-dependent `int`/`uint` policy
  in the future relation.
- Replace `execStmt : ExecState -> Except ... ExecState` with an explicit
  `ExecOutcome` for normal completion, return, break, continue, panic,
  unsupported, and stuck behavior.
- Add broader control-flow coverage around nested `if`, early `return`, and
  later labeled control flow.
- Keep expression evaluation able to grow to calls-in-expressions, allocation,
  map operations, and channel operations without changing its public shape
  again.
- Continue slices with descriptor values over backing locations, following
  `docs/slice-model.md`. Do not model slices as copied vectors.
- Keep append capacity growth explicit in tests. The executable interpreter now
  has a deterministic policy for Go-vs-Lean differential runs; the later
  relational semantics should still allow implementation-specific fresh
  capacities.
- Track semantic policy choices that remain open for differential refinement,
  especially allocation limits, append growth, zero-capacity slices, string
  slicing, and panic-message details.
- Keep improving artifact-generation scalability. Gobra exports are now
  incremental by source hash, but a cold export still invokes SBT/Gobra once per
  fixture. Prefer batched package export or a native Go frontend path once
  practical.
- Treat Gobra's permission-argument variants of `copy` and `append` as
  frontend artifacts. The Gobra fork may enrich `--printInternalJson` with
  plain-Go nodes such as `GoSliceCopy` and `GoSliceAppend`; do not add Gobra
  permission semantics to GoCore just to support them.
- Evaluate lvalues and rvalues before committing stores, so multiple assignment
  and call assignment match Go's sequencing rules.
- Bounds-check indexed locations when evaluating the lvalue, including
  address-of-index operations such as `&a[i]`.
- Keep GoCore free of Gobra verification constructs. Gobra assertions,
  preconditions, postconditions, invariants, predicates, and ghost artifacts are
  frontend wire data only unless a later proof-extraction design explicitly
  reinterprets them outside the runtime semantics.

## GoCore Memory Milestone

- Track frontend gaps separately from semantic gaps. For example, Gobra
  currently rejects the Go `delete` builtin, so map deletion needs either Gobra
  fork enrichment or a future native Go frontend before it can enter the active
  Gobra-fronted differential suite.
- Add regression tests that observe memory effects through ordinary Go returns
  or Go-side output, not Gobra assertions.
- Add richer call-frame tests, including returned values and nested calls.
- Add method-call tests from Gobra JSON beyond `examples/swap`.
- Track Gobra frontend gaps found while promoting semantic-edge cases: Gobra accepts
  variadic calls/spreads but rejects `range` directly over a `...int`
  parameter, so `features/variadic.gobra` uses `len`/index iteration.
- Track Gobra frontend gaps found while promoting conversion cases: Gobra
  rejects legal Go integer-to-string conversions such as `string(65)` and
  `string(byte(255))`, so active differential coverage cannot use the Gobra
  frontend for this rune-conversion slice yet.
- Track Gobra frontend gaps found while promoting switch cases: Gobra accepts
  basic and expressionless switches but rejects explicit `fallthrough` in the
  parser.

## Completed GoCore Memory Milestone Items

- Split the former monolithic `GoLean/IR.lean` into GoCore syntax, value import
  point, state, operations, and executable evaluation modules. `GoLean/IR.lean`
  remains as a compatibility import.
- Converted GoCore expression and assignee evaluation to return an updated
  `ExecState`, preserving Go's evaluate-before-store assignment discipline while
  leaving room for calls-in-expressions, receives, and effectful builtins.
- Moved concrete `GoError`, `Loc`, `SliceValue`, `MapValue`, and `GoValue`
  definitions into `GoLean/GoCore/Value.lean`; `GoLean/Runtime.lean` is now only
  a compatibility import.
- Replaced raw value-shape equality with type-directed GoCore equality and
  type-directed map-key comparison.
- Added first typed integer support: GoCore integer kinds, Gobra integer-kind
  lowering, fixed-width normalization on typed stores/arithmetic, a 64-bit
  executable policy for `int`/`uint`, and `int8` overflow differential coverage.
- Added first integer conversion support: Gobra `Conversion` decoding/lowering,
  GoCore integer-to-integer conversion normalization, and `byte(300) == 44`
  differential coverage. Non-integer conversions remain explicitly unsupported.
- Added byte-backed string literals and string/`[]byte` conversions:
  Gobra JSON now exports exact `StringLit.bytes`, Lean rejects stale string
  literal JSON, GoCore has explicit byte-string conversion nodes, and the
  differential suite covers escaped arbitrary bytes plus conversion copy
  semantics.
- Added first shift support: Gobra `ShiftLeft`/`ShiftRight` decoding/lowering,
  fixed-width left/right shift normalization, signed arithmetic right shift,
  and negative-shift panic coverage.
- Added string byte indexing: indexing a Go string reads from its UTF-8 byte
  sequence and returns a `uint8`, with direct and differential coverage.
- Switched GoCore string values from Lean `String` to byte-backed `GoString`,
  matching Go's byte-level string operations and Perennial/new Goose's
  `go_string` model.
- Added two-index string slicing over bytes, including an invalid-UTF-8
  substring differential case.
- Added bitwise integer operators: `&`, `|`, `^`, `&^`, and unary `^`, using
  fixed-width modular bit patterns and type-directed result normalization.
- Replaced stable variable references with heap-backed locals.
- Added `Loc.base` and `Loc.field` path-like locations.
- Added load, store, address-of, dereference, struct field get, and field ref.
- Added `Value.struct` and struct literals.
- Added direct function and method calls with fresh local frames and shared heap.
- Made `examples/swap` execute as ordinary Go after Gobra assertions/specs are
  erased at lowering.
- Added GoCore `if`, explicit `return`, and unlabeled `break`/`continue`, with
  Gobra-fronted differential smoke coverage.
- Added fixed-array `len`/`cap`, with Gobra-fronted differential smoke
  coverage.
- Added fixed-array zero-value initialization, nested arrays, arrays through
  function parameters/results, and pointer-to-array indexing/assignment.
- Added type-aware `len`/`cap` for pointer-to-array values, including nil
  pointers, so GoCore matches Go's non-dereferencing array-pointer behavior.
- Reviewed Goose/Perennial/Gobra slice designs and selected a descriptor over
  backing locations as the direction for GoCore slices.
- Added the first descriptor-backed slice subset: nil slice defaults, array
  slicing, slice indexing/addressing, two-index and full slicing, Gobra `Slice`
  JSON decoding/lowering, and differential array-to-slice alias coverage.
- Added Gobra `MakeSlice` decoding/lowering and nonzero-capacity `make` support
  with differential coverage.
- Added Gobra `NewSliceLit` decoding/lowering and slice literal differential
  coverage.
- Enriched the Gobra JSON fork so `--printInternalJson` accepts plain Go
  `copy`/`append` and emits `GoSliceCopy`/`GoSliceAppend`; added GoCore
  execution and differential coverage for overlapping copy and append
  in-place/growth aliasing.
- Refined append growth to allocate real backing capacity tail cells and match
  current focused Go differential cases that observe post-reallocation `cap`.
- Added the first executable interface-value subset: `ToInterface` boxes carry
  a dynamic type tag, Gobra `SafeTypeAssertion` and expression `TypeAssertion`
  lower to GoCore, interface method calls dynamically dispatch to concrete
  methods where Gobra exposes method metadata, and focused differential coverage
  passes for interface dispatch, interface-to-interface assertions, concrete
  assertions, assertion panics, and interface storage-copy cases.
- Next interface semantics targets are typed-nil interface equality,
  dynamic interface equality/comparability panics, and type switches. Keep
  frontend-export failures separate; many typed-nil and error idiom cases are
  still blocked before Lean by the current Gobra path.
- Made `scripts/gobra-smoke` manifest-driven for Lean execution and expanded
  the differential suite to 29 cases, including typed nil slices, nil/empty
  slice distinctions, nil append, variadic overlap append, full slicing,
  full-slice bounds panics, zero-length `make`, nil copy, and short copy.
- Added source-hash based Gobra artifact caching, so warm `scripts/gobra-smoke`
  runs reuse unchanged successful exports.

## Proof Generation

- Deferred until after the executable semantics and differential harness cover a
  substantial Go subset.
- Define a relational small-step or big-step GoCore semantics over the same
  syntax, values, locations, errors, and outcomes as the executable interpreter.
- Prove, where practical, that the executable interpreter is sound with respect
  to the relational semantics on supported deterministic terminating runs.
- Generate struct typed points-to predicates as field-wise ownership.
- Generate field load/store/access lemmas over `Loc.field`.
- Prototype a Lean WP/VCG layer over GoCore.
- Evaluate where Iris-Lean should enter for heap and concurrency reasoning.
