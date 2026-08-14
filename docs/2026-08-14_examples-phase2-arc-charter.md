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

### Slice-0 measurements (2026-08-14, as levers landed)

Recorded because two of them refute what the diagnosis above assumed.

| measurement | before | after |
|---|---|---|
| WordCount module peak, 1 thread vs 6 | 51.3 GiB | 51.1 GiB |
| WordCount module peak, 32-way (consolidation §3) | ~55 GiB | — |
| `wc_empty_run` ALONE (standalone probe) | — | 82 s, 50.8 GiB |
| the same shard with that one theorem removed | — | 1 s, 0.2 GiB |
| WordCount headline edit → rebuild | 91–110 s | 0.96 s |
| InsertionSort headline edit → rebuild | ~10 s | 0.96 s |
| WordCount subtree from clean | ~110 s (1 module) | ~125 s (14 shards) |
| root `Audit.lean` elaboration | 4.0 s (2141 lines) | 4.3 s (1846 lines) |
| one-example change → audit re-check | whole Audit | 1 shard + root, 6.3 s |

1. **"32-way sum-of-peaks" was wrong for the heavy module.** Thread
   count moves WordCount's peak by 0.4% (51.3 → 51.1 GiB); the ~4 GiB
   between that and the historical ~55 GiB is all parallelism. Lever 1
   is still worth having — it bounds the sum once lever 2 turns one
   module into fourteen schedulable ones — but it does not touch the
   ceiling.
2. **The ceiling is ONE DECLARATION**, not a module and not the corpus:
   `wc_empty_run`, a single 158-step `with_unfolding_all rfl` over a
   concrete configuration, is 82 s and 50.8 GiB by itself. Lever 1's
   48G acceptance is therefore UNMET and cannot be met by any placement
   lever — a full build from clean needs > 51 GiB until that proof
   changes. Lever 2 makes the cost attributable (its own shard,
   `Examples/WordCount/EmptyRun.lean`); it cannot make it smaller.
3. What lever 2 *did* buy is incrementality — ~100× on a headline edit
   — at ~15% more wall from clean. That is the trade the levers were
   chartered for.

**The re-envelope obligation this creates:** the long-concrete-run rfl
is now the growth-limiting cost class, and lever 4's convention does
not reach it (a segment convention governs SHORT steps between pinned
states). The verified-reflection direction above is its named lever;
until it is taken, every new harness that needs a long concrete run
buys another ~50 GiB peak, and the honest planning number for a lane
is 64G per heavy build, one at a time.

**DISCHARGED by slice 1.5 (2026-08-14): verified reflection was NOT
needed.** Lever 4's convention DOES reach the class once extended from
placement-generic to PROGRAM-generic (abstract σ with only
`heap`/`nextAddr` pinned; the one program-consulting step conditioned
on its `enterFrame` fact). `wc_empty_run`: 50.8 GiB → 1.9 GiB,
statement byte-identical, axiom pins unchanged, and the reverted
`wordcount_harness_r` re-lands. Record:
`docs/2026-08-14_phase2-slice1-spec-swaps.md` §"Slice 1.5"; normative
recipe: the StepKit module docstring. The verified-reflection
direction stays parked for a 10× corpus, not for this.

### Lever 4 convention (RECORDED, no retrofit): the default segment shape

New example segment layers are **placement-generic and type-ascribed**
by default — the consolidation slice's E-form (§1 of
`docs/2026-08-13_consolidation-slice.md`) generalized from compositions
down to segments. The normative statement, with a worked template, is
the module docstring of `proofs/GoLeanProofs/StepKit.lean` ("The
DEFAULT SHAPE FOR NEW SEGMENT PROOFS"); in short:

1. abstract the state (`σ : ExecState`) whenever the segment touches no
   heap cell — it rides through `rfl`, so one statement serves every
   placement;
2. where a cell IS touched, take the lookup/store equation as a
   HYPOTHESIS and keep the address abstract — the hypothesis type pins
   the state, making the E-form structural rather than remembered;
3. at any application site mentioning a big concrete state, pin the
   FULL result type on the `have`.

Scope, stated so it is not over-read: this is a convention for NEW
proofs and it changes the growth RATE of the segment layer. The seven
shipped examples are NOT retrofitted in this slice, and it is not a fix
for measurement 2 above.

## Slice 1 — spec-style swaps (the scoping study's recommendations,
`docs/2026-08-14_harness-style-scoping.md` §9–10)

**STATUS 2026-08-14: PARTIAL — guardrail half landed, proof half not.
Slice record and handoff: `docs/2026-08-14_phase2-slice1-spec-swaps.md`
(read it first).** The reverse copy-relational and minmax S3 harnesses
are in the corpus, differentially green and golden-pinned; no headline
proof, gallery re-render or old-headline demotion has happened yet, and
the gallery still describes the old harnesses. wordcount's swap is
BLOCKED on a measured proof-cost wall — `wc_empty_run` goes 50.8 GiB →
~77 GiB when one function is added to that corpus program, past the
default 64G cap — so lever 2/4 work on that declaration is now a
PREREQUISITE for the wordcount swap, not just a nice-to-have.

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
  two lanes cannot run concurrent full gates. Lane budget rule: one
  heavy build at a time per box. **CORRECTED 2026-08-14 after levers
  1–2 landed:** the original text said "until slice-0 lever 1 lands",
  which the measurements refute — the 64G need is one declaration's
  50.8 GiB (`wc_empty_run`), not parallel sum-of-peaks, and neither the
  thread cap nor the module split moves it. The 64G-per-heavy-build,
  one-at-a-time rule stands until the long-concrete-run proof class is
  re-done (see the Slice-0 measurements above).
  **RE-DONE (slice 1.5, 2026-08-14):** `wc_empty_run` restated
  program-generically at a 1.9 GiB peak; the heaviest proofs module is
  now ~2 GiB and the full proofs build fits the slice-0 lever-1 48G
  acceptance again. Parallel-lane full gates are budget-feasible again
  under the standing `GOLEAN_MEM_MAX=48G`-per-lane rule.
- `.tmp/` is gitignored as of `2efa4524`; scoping/audit scratch under
  it is referenced handoff material (inventory:
  `docs/2026-08-14_harness-style-scoping.md` §11, sweep report §5).
