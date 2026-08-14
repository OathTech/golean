# Examples phase-2 arc charter (2026-08-14)

Status: CHARTERED (user-directed, 2026-08-14) — the successor to the
verified-examples arc, opening after that arc merges to `main`. Three
slices in order; slice 0 first BY RULING (the spec swaps add heavy
proof files and must not be built on the current cost curve).

Standing rules inherited: the harness ruling + sub-style triad + ghost
ladder at rung 0 (`docs/2026-08-12_example-spec-form.md` §11/§11a-era
rulings, `docs/2026-08-14_harness-style-scoping.md` §0/§10); the active
abstraction loop (form note §12); the enumeration ban; the two-bounds
doctrine; commit-on-convergence; worktree-per-lane.

## Slice 0 — proof scaling (FIRST; user: "this kind of growth isn't
going to be feasible if it keeps going")

The diagnosis (recorded 2026-08-14, after the full proofs build
OOM-killed twice inside a 48G cap and completed at 64G): monolithic
example modules (~5k lines, hundreds of segment proofs over concrete
machine states), kernel whnf over concrete configurations at
`with_unfolding_all rfl` sites, and 32-way sum-of-peaks parallel
elaboration. The levers, cheapest first, each with its acceptance
measure:

1. **Cap Lake parallelism in `scripts/ci`** scaled to `GOLEAN_MEM_MAX`
   (bounded sum-of-peaks). Measure: full proofs build completes inside
   a 48G cap again.
2. **Split the giant modules per-phase** (segments by phase,
   compositions, thin headline file). Lake module-level caching IS the
   incremental story — our files are just too big to benefit. Measure:
   touching a headline re-elaborates a small file, not ~5k lines;
   WordCount touch-to-green under ~2 min.
3. **Shard `Audit.lean` per example** (per-file dependency rules — the
   brick-wp 2026-08-14 pattern, `deps/brick-wp` "Parallel example
   build: per-file dependency rules + sharded audit"). Measure: a
   one-example change re-checks one shard.
4. **Placement-generic, type-ascribed segment statements as the
   default** for new proofs (the consolidation slice's E-form
   generalized from compositions down to segments — no concrete front
   reaches the unifier/kernel). Measure: new-example segment layers
   elaborate without multi-GB peaks; changes the growth RATE.
5. **CI olean caching** (keyed on toolchain + manifest). Measure: CI
   proof step drops from from-scratch to incremental on doc/corpus
   commits.
6. **Cost-tracker speedbump** (`scripts/proof-costs` or equivalent):
   per-module wall + peak RSS per gate run, a visible trend line.
   Speedbump standard — report, never block.

Research direction recorded, NOT scoped: segment proofs by verified
reflection (a certified step-evaluator with compact certificates
replacing per-segment kernel `rfl`) — the endgame lever if the corpus
grows 10×; revisit when levers 1–5 stop paying.

## Slice 1 — spec-style swaps (the scoping study's recommendations,
`docs/2026-08-14_harness-style-scoping.md` §9–10)

- reverse → copy-relational S1 (checks against a saved pre-copy — real
  Go history ghost, rung 0).
- minmax → S3 relational (returned pre + `(lo,hi)`; post
  `lo = minSpec pre ∧ hi = maxSpec pre` — direct statement, family
  function leaves the reader surface).
- wordcount → S3 (direct `maxMultiplicity` over returned data).
- fib/gcd keep S2 (already direct for scalar subjects); isort keeps
  shipped S1 (S3 math companion later); **binsearch waits at ghost
  rung 1** (its direct form needs the nondet annotation).
- Gallery re-rendered per swap in the same commit (render-gallery
  stays green); corpus rows for new harnesses + full-diff re-pins per
  the standing discipline.

## Slice 2 — proof-library wave (brick-wp-informed; user: "maybe some
proof library improvements")

Review `deps/brick-wp` W1–W7 (2026-08-13/14) and map each to a
consumer-backed lift (active-abstraction rules apply — ≥2 consumers,
fixtures, measured deltas):
- W2 `wp_provide_call` ("the dance in one tactic") → the P4
  entry-equation macro, attempted properly this time.
- W3 call-readiness combinators → entry-glue combinators.
- W6 sealed-interface kit → sealed interfaces for StepKit/SliceMem
  (serves the C2 decoupling rule: adapters depend on APIs, not
  internals).
- P5 setup-loop schema / P8 frame-rebase: only if slice-1 consumers
  demand them (the recorded template stands).

## Arc end

- **Designation + comparator landmark** (deferred from the foundation
  merge BY RULING — swapping three statements then designating avoids
  paying the landmark twice): designate the gallery headlines
  (post-swap forms) into the statement-TCB gate; run
  `scripts/comparator-judge`.
- Standard merge protocol; audit ask sized to what the arc touched
  (slice 0 touches `scripts/ci` — gate-honesty dimension applies).

## Parked / inputs to OTHER arcs (recorded, not this arc's scope)

- Frontend arc inputs (from the scoping study + audit): short-circuit
  operand call-hoisting ergonomics; `fmt.Sprint` support; differential
  driver `--arg` extension past int64 (unlocks oracle rows in the
  uint64 wrap region + renaming the `harness-wrapping` row id);
  annotation parsing at NativeToIR (ghost rung 1, when ruled).
- Relational unbounded-data mechanism (deep-decode vs emit-trace) —
  deferred until an example pulls it in.
- Raft capstone work: conditioned-Agreement safety form, fixed 3/5
  clusters (`docs/2026-08-14_harness-style-scoping.md` §10.5 ruling);
  behind the concurrency re-envelope, which carries the recorded
  fairness-definability requirement on `Choices`.

## Infra facts (operative)

- Full proofs build currently needs the 64G cap (measured 2026-08-14);
  two lanes cannot run concurrent full gates until slice-0 lever 1
  lands. Lane budget rule: one heavy build at a time per box.
- `.tmp/` is gitignored as of `2efa4524`; scoping/audit scratch under
  it is referenced handoff material (inventory:
  `docs/2026-08-14_harness-style-scoping.md` §11, sweep report §5).
