# Campaign Arc 2 — the CompletionWitness route study (memo of record)

Lane `campaign-arc2`, 2026-08-22. Governing: the constitution §2.1
(the completion witness is T1's non-vacuity twin) and §3 (no
`native_decide`, statements over the naive semantics). Everything here
is **[AGENT]** unless marked. Probes and their raw records:
`docs/campaign-arc2-probes/` (each record cites its command line).

## 0. The question

`CompletionWitness` (`proofs/GoLeanProofs/Specs/RaftAgreement.lean`)
needs a KERNEL-CHECKED `twinRun N ch = .ok r` for some `N`, `ch`, with
`complete = 1 ∧ floor = 1`. Compiled evaluation confirms the fact is
TRUE (campaign U-c7: `twinRun 8000000000 [] =
.ok #[int 0, int 1, int 6, int 1, int 1]`, 14:00 wall / 1.7 GB). The
question is which route gets the kernel to certify it, decided from
measurements, not presumption.

## 1. The measurements

### 1.1 The run is ~712k machine steps (probe A)

`probeA-census.lean` — `runProgramM`'s exact wiring with the fuel loop
replaced by a counting loop (driver-drift cross-check: the probe's
verdict equals the U-c7 record exactly).

| quantity | value | provenance |
|---|---|---|
| `$pkginit` phase steps | **1,382** | `records/probeA-census.out` |
| subject phase steps | **711,616** | same |
| minimal completing fuel | **711,616** (= max of the phases; `runProgramM`'s fuel bounds each phase separately, and the terminal check precedes the fuel check, so fuel = steps taken suffices) | same + `GoLean/GoCore/StepFn.lean` (`runConfig`, `runProgramSetupM` docstring) |
| verdict | `#[int 0, int 1, int 6, int 1, int 1]` | same |
| probe wall / RSS (compiled, interpreted IR) | 12:17 / 1.7 GB | same |

So the compiled evaluator spends ~1.0 ms/step; the run is five orders
of magnitude smaller than the 8×10⁹ fuel the probe passed — the fuel
number in U-c7 was headroom, not size.

### 1.2 The kernel cost curve (probes kprobe·K)

`example : twinRun K [] = .error .fuelOut := by with_unfolding_all rfl`
(expected value confirmed compiled first for every K —
`probeB0-expected.lean`; each K runs init to min(K, 1382) init steps
plus min(K, …) subject steps, i.e. K=10000 covers 1,382 init + 10,000
subject steps). All runs `scripts/capped lean` (direct `lean` with
`lake env`'s LEAN_PATH — `lake env lean` under a concurrently running
sibling lake wedged with SIGTERM, recorded as an operational note),
`set_option smartUnfolding false` (see 1.3), single-threaded, this
125G box.

| K | wall | peak RSS | rc |
|---|---|---|---|
| 0 | 32.3 s | ≤48G cap (not polled) | 0 PASS |
| 10 | 32.8 s | 6.1 GB | 0 PASS |
| 100 | 54.7 s | 8.9 GB | 0 PASS |
| 1000 | 110.9 s | 15.6 GB | 0 PASS |
| 10000 | **DNF** — timeout(3000 s) at 50:00 | 63.4 GB at kill (64G cap) | 124 TIMEOUT |

Phase attribution (init = 1,382 steps, and `runProgramM`'s fuel bounds
each phase separately): **K ≤ 1000 never leaves `$pkginit`** — those
rows measure init-phase steps over the small just-seeded heap. K=10000
is the only row with subject steps (1,382 init completed + up to
10,000 subject), and it did not finish in 50 min / 64 GB. Per the
brief's rule, the kill point IS the measurement.

Marginal rates:

- fixed cost (K=0 — olean import, whnf of the `twinLowered` unfold,
  `seedGlobals` + `StateWf` over the whole 9.3 MB program, immediate
  init fuel-out): **~32 s**;
- init-phase steps (K=100→1000, 900 steps): **0.062 s/step**,
  **7.6 MB/step retained** ((15.6−8.9) GB / 900). The K=10→100 stretch
  reads 0.24 s/step — first-touch unfolding of the tables consulted
  early; reported, not smoothed;
- subject-phase steps (K=10000, bounds only): elapsed minus the
  init-equivalent prefix gives ≥ (3000 − 111 − 30)/10000 ≈
  **≥ 0.29 s/step** — a hard lower bound (the probe would only be
  SLOWER than this if it completed fewer than its 10,000 subject
  steps, which is exactly what DNF means). Retention:
  **≥ 4.5 MB/step** ((63.4 − 15.6 − 2.9) GB over ≤ 10,000 steps).

Kernel-vs-compiled ratio at the measured point: ≥ 0.29 s / ~1.0 ms ≈
**≥ 300×** — the presumed compiled≪kernel gap, now with a number.

### 1.3 `smartUnfolding false` is mandatory at this scale

Without it, K=0 (the PRELUDE alone, zero interpreter steps) was
OOM-killed at 16G in 16 s and at 48G in 56 s — the elaborator's
default whnf on the program-embedding state is the kit's measured L4/L5
pathology at library scale (`docs/kit-guide.md` §5/§22). With the
option, the same probe passes in 32 s. Any raw-`rfl` route inherits
this option file-wide, which the kit's §5 REVERSAL row warns can
invert evaluator-transported windows in the same file — segment
modules must be split accordingly.

## 2. The projections (derivations shown)

All projections use the ≥ 0.29 s/step and ≥ 4.5 MB/step subject-phase
LOWER bounds from §1.2 — the direction of the unmeasured error is
known: mid-run steps run over a LARGER heap than the first 10k
(probe C, §2.1), and every heap op the kernel reduces walks the
concrete heap list, so the true per-step cost at mid-run is, if
anything, higher. Bounds shipped as bounds.

**Monolithic kernel evaluation of the full witness run**
(`twinRun 711616 [] = .ok ⟨…⟩` by one `with_unfolding_all rfl`):

- time ≥ 32 s + 1,382 × 0.062 s + 711,616 × 0.29 s ≈ **≥ 206,000 s ≈
  ≥ 57 CPU-hours** (single-threaded; whnf does not parallelize);
- memory ≥ 711,616 × 4.5 MB ≈ **≥ 3.1 TB retained** — ~25× the whole
  125 GB box. **Route (a) is dead on MEMORY before time even
  matters**, and the growth was measured as steady, not a warm-up
  transient (the K=10000 poll: 6 → 63 GB, ~1.1–1.3 GB/min, never
  flattening).

**The same total step work, segmented** (each segment a fresh `lean`
process, memory resets per segment): the per-step time cost is
unchanged (a certificate/checkpoint cannot delete kernel reductions —
§3's EnumDedup lesson), so ≥ 57 CPU-hours of kernel work TOTAL, but:

- per-segment memory is bounded by segment length: at ≥ 4.5 MB/step,
  a 16 GB budget holds ≲ 3,000 steps (minus the segment's own literal
  elaboration) → **~240–700 segments** for the run;
- segments are independent once checkpoints exist → parallel across
  cores under the worktree cap budget (4 × 16 G jobs ≈ 64 G): wall ≈
  57 h / 4 ≈ **~15 CPU-parallel hours, plus per-segment fixed costs**
  (import ~5–10 s and the checkpoint-literal elaboration, unmeasured —
  unit 2 slice 1's job);
- a slow or failing segment is visible EARLY and individually, and a
  re-run after a wire re-pin re-pays only the segments, not a 3 TB
  monolith.

### 2.1 Heap scale over the run (probe C)

`probeC-heapgrowth.lean` (compiled, verdict-path cross-checked by the
same step count 711,616; record
`records/probeC-heapgrowth.out`): the machine's heap is APPEND-ONLY
over this run — `heapLen = nextAddr` at every sample, i.e. every
allocation lives to the end:

| subject step | heap cells |
|---|---|
| 0 | 103 |
| 100k | 6,052 |
| 350k | 19,093 |
| 700k | 36,062 |
| end (711,616) | **36,376** |

~1 allocation per 20 steps, linear, no plateau. Two consequences,
both feeding unit 2 slice 1:

- **The §1.2 subject-phase rate was measured on a ≤ 700-cell heap.**
  Kernel heap ops traverse the concrete heap list, so mid-run
  per-step cost plausibly scales with the 19k–36k-cell heap — the
  ≥ 0.29 s/step bound could understate the mid-run rate by an order
  of magnitude. This is exactly why the route decision below gates on
  ONE MEASURED MID-RUN SEGMENT before any generation, and why the
  fallback is armed rather than merely listed.
- **Checkpoint literals are heap-sized**: a mid-run checkpoint
  reflects ~19k–36k cells of `GoValue` term — megabytes per segment
  module. Real but precedented (the 9.3 MB wire pin elaborates in the
  standing build); slice 1 measures it.

## 3. What the completion machinery offers (study, deliverable 2)

- **`FuelMeasure` group 1–2 (`CompletesIn`, `completesIn_measure_loop`,
  `terminates_of_completesIn`; consumer `fibTerminates`,
  `Examples/Fib.lean`)** — SYMBOLIC termination for a ∀-input family:
  a measure-indexed invariant family and per-iteration segment lemmas.
  Right tool for T1's ∀-side reasoning; for the ∃-witness it is
  overkill in kind: the witness is ONE concrete run, and `CompletesIn`
  would still have to be discharged down to concrete segment facts.
- **The gallery segment method (`StepKit` + `FuelMeasure` groups 4–6,
  `EntryEq`, composition via `stepFnIter_chain` +
  `runConfig_of_stepFnIter` + `runConfig_next_stop`)** — crosses a
  CONCRETE run in windows; every gallery example ends this way. For a
  concrete witness run, NO functional specs or invariants are needed —
  the windows are raw `with_unfolding_all rfl` facts chained by fuel
  arithmetic. The per-window content is exactly the same kernel
  reduction as route (a), restructured. (The per-function spec count
  feared for a WP walk — probe A's census: **226 distinct
  statically-called functions + 9 value-call callees + defer callees
  (272 defer-site executions, fids not resolved by the probe — honest
  gap)** — is the cost of the SYMBOLIC walk variant only; the concrete
  walk needs none of them.)
- **Sym (`Sym/Refine.lean`, `symEvalWindow_refines'`)** — transports a
  window for free of hand-transcription, ∀ρ ∀σ ∀ch, and QUITS at:
  branches, control-feeding equality, choice consumption,
  symbolic-address computation, every program-table consult
  (`docs/kit-guide.md` §23). The twin run consults program tables at
  every call and branches constantly — windows would quit within a few
  steps almost everywhere. Sym is not a route here; its per-step
  kernel cost model is that the step-count projection is a closed
  evaluator run (cheap) but only inside its sequential, table-free
  fragment.
- **`EnumDedupCheck`/`EnumDedupSound` (the certificate-checker
  pattern)** — the checker RE-EXECUTES every edge through the real
  `stepMulti` and replays every member witness through the unmodified
  driver; its soundness theorem is generic, proved once. The pattern's
  lesson for a run-certificate: a checker whose verdict the kernel
  must evaluate performs the SAME stepFn reductions as direct
  evaluation — a certificate cannot make the kernel's step work
  disappear, only restructure it (checkpoints = bounded memory +
  parallelism + resumability, not fewer reductions).

## 4. The routes, costed

**(a) Raw monolithic kernel evaluation.** REFUTED BY MEASUREMENT:
≥ 3.1 TB retained (§2) — infeasible on any machine we have, at any
patience. The viable content of (a) survives only inside (c).

**(b) A symbolic WP/kit completion walk over the twin.** What it
would need: per-function specs/segment lemmas for the default-stream
call graph — probe A's census: **226 distinct statically-called
functions + 9 value-call callees (+ the defer-callee set, unresolved
by the probe)**, with the hot ones (`raftpb.Message.GetType` 442
executions, `utoa` 415, `raft.unstable.maybeLastIndex` 185,
`raft.stepLeader` 18 …) needing full symbolic treatment of raft's
actual control flow. Estimate: at gallery cost discipline this is a
mini-gallery — **order 200+ proof units, i.e. months** — and, the
decisive point: **for an ∃-witness it buys nothing** — the witness is
ONE concrete run; a concrete walk needs no specs at all, and a
symbolic walk's reusable value (invariant lemmas over raft functions)
belongs to T1's ∀-side, which Plan A routes through the Verdi
structure port, not through WP over the twin. [AGENT] judged: (b) is
the wrong instrument for this deliverable, independent of its cost.

**(c) The checkpointed segment walk ("certified run by segments") —
RECOMMENDED.** Not a checker in the `checkCert` sense (a verified
checker re-executes the same steps — §3; there is no cheaper
checkable certificate for a single run's completion than the run,
because completion has no witness smaller than the trajectory): the
checkpoints ARE the certificate, and segment re-execution is bounded
per segment, exactly the brief's "checkpointed states with segment
re-execution" variant. Concretely:

1. **Checkpoint reflection, the WirePin trust story at state scale**:
   a `twinCheckpoint% n` term elaborator that runs the COMPILED
   `stepFn` iteration n steps from the seeded start at elaboration and
   reflects `(heap, nextAddr, config, choices)` as literals (ToExpr
   for the value/config grammar — meta-side, GoCore untouched, same
   pattern as `WirePin.lean`'s derives). A wrong or drifted literal
   cannot produce a false theorem — the kernel checks every segment
   equation; the reflector is scaffolding that runs once. The
   PROGRAM-GENERIC spelling (kit L4) is mandatory: checkpoints are
   `{ twinSeeded with heap := Hᵢ, nextAddr := naᵢ }` over ONE shared
   table-carrying base def — never a state literal embedding the
   9.3 MB tables per segment.
2. **Segments**: `stepFnIter kᵢ σᵢ Cᵢ chᵢ = .ok (Cᵢ₊₁, σᵢ₊₁, chᵢ₊₁)`
   by `with_unfolding_all rfl` under `smartUnfolding false` (both
   measured mandatory, §1.3), one module per segment (the §5-REVERSAL
   file-isolation rule), sizes set by measured retention.
3. **Composition**: the kit's everyday triple — `stepFnIter_chain`
   folds the segments, `runConfig_of_stepFnIter` +
   `runConfig_next_stop` land the subject phase, the same for
   `$pkginit`, plus one kernel-checked `runProgramSetupM` equation for
   the prelude (its cost is the measured 32 s K=0 point) and the
   `loadMany` readout. `CompletionWitness` is then
   `⟨711616, [], r, rfl-chain…⟩` — fuel re-derived by the composition
   arithmetic, never trusted from the probe.

Projected cost: §2's segmented figures (≥ 57 CPU-h kernel work,
~15–30 h wall at 4-way parallelism, ~240–700 segment modules,
generation scripted). The unmeasured risks, named: mid-run per-step
cost growth (heap-size-linear kernel work) and per-segment
checkpoint-literal elaboration cost. Both are measured by ONE mid-run
segment before any generation — that is unit 2 slice 1, and it is the
route's go/no-go gate.

**(d) Found while studying: the verified fast-twin evaluator — the
FALLBACK.** If slice 1 shows mid-run per-step cost or literal costs
pushing (c) past budget (trigger: projected total > ~200 CPU-hours,
or any balanced segment > 1 h), the honest next move is not more
patience but an ACCELERATOR under §3.1's standing template: an
evaluator `runConfigFast` over kernel-reduction-friendly state
representations (Nat-keyed radix-trie heap — O(log n) node rebuilds
per op against the naive list's O(n) spine rebuild; same for the
function table), shipped WITH its once-and-generic equality theorem
`runConfigFast … = runConfig …`, statements untouched (exec-slow
principle; the accelerator never enters the statement closure, the
kernel checks the equality theorem's INSTANCE applied to this run via
the fast form's evaluation). Expected 10–50× on the heap-dominated
per-step cost; buildable proof-side without touching GoCore; also
reusable for every future certified-run need (twin re-pins, richer
witness drivers, T3-era batteries). It is second, not first, because
it is weeks of build (a full structural-induction equivalence over
`stepFn`'s ~50 arms) that slice 1's measurement may prove
unnecessary — though probe C's heap curve (§2.1: kernel heap ops over
19k–36k cells mid-run vs the ≤ 700 cells the rate was measured on)
raises the prior that the trigger fires. If it does, (d) REUSES (c)'s
checkpoint reflector unchanged: fast evaluator for the per-step cost,
checkpoints for the memory bound — the two compose.

**Rejected non-routes, recorded**: `native_decide` (inviolable §3.9);
shrinking the witness by a leaner client protocol (cheaper by ~3–5×
but changes the PINNED twin/statement — Arc-1 files are immutable
here, and a statement re-pin is supervised/Mike's; flagged as an
observation for the campaign lane, not proposed); Sym transport
(quits at every table consult/branch/choice — §3); enumeration
(already ruled out by the Arc-1 design §4).

## 5. Recommendation and the unit-2 charter

**RECOMMENDED: route (c), with (d) as the armed fallback and slice 1
as the explicit go/no-go.** [AGENT] — the whole decision; grounds:
(a) refuted on memory by measurement, (b) wrong instrument for an
∃-witness, (c)'s two open risks are cheap to measure before
committing, and its artifacts (state reflection, segment generator)
are reusable campaign infrastructure either way.

**Unit 2 charter — "the checkpoint reflector and the mid-run
segment" (one session, parkable):**

1. `proofs/GoLeanProofs/Specs/StateWire.lean` (name indicative):
   ToExpr derives for the value/heap/config grammar +
   `twinCheckpoint% n` (compiled n-step run at elaboration, reflected
   program-generically over a shared `twinSeeded` base def). Fail
   closed: any error in the compiled run fails elaboration loudly.
   GoCore/frontend/scripts untouched; new module imported from the
   aggregator (the 1b2 sweep).
2. ONE mid-run segment, measured at three sizes: from the ~350k-step
   checkpoint, windows of 250 / 1,000 / 3,000 steps, each
   `with_unfolding_all rfl` under `smartUnfolding false`, capped +
   timed + RSS-polled, records committed beside this memo's. This
   yields: mid-run per-step kernel cost, checkpoint-literal
   elaboration cost, and validated segment sizing.
3. The go/no-go, logged: project the full segmented cost from slice
   2's numbers. GO → unit 3 charters the generator + wave plan
   (segments are file-disjoint units; the composition file is the
   serialization point). NO-GO (> ~200 CPU-h projected) → unit 3
   charters fallback (d), carrying slice 2's measurements as its
   baseline.
4. Honesty rails carried forward: every number derivation-anchored to
   a record file; bounds as bounds; the probe fuel numbers are
   scaffolding — the proof re-derives its fuel by composition; a
   killed probe's kill point is a datum, not a failure to hide.
