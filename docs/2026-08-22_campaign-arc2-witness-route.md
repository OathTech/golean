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
`probeB0-expected.lean`; fuel bounds each phase separately, so a probe at
K runs min(K, 1382) init steps, then — only if init completed — up to
K subject steps; K=10000 is the only row that reaches the subject). All runs `scripts/capped lean` (direct `lean` with
`lake env`'s LEAN_PATH — `lake env lean` under a concurrently running
sibling lake wedged with SIGTERM, recorded as an operational note),
`set_option smartUnfolding false` (see 1.3), single-threaded, this
125G box.

| K | wall | peak RSS | rc |
|---|---|---|---|
| 0 | 32.3 s | 6.0 GB (polled at the U2 rerun: 36.2 s under load, `records/kprobes-small.out`) | 0 PASS |
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
  57 h / 4 ≈ **~15 wall-hours at 4-way parallelism, plus per-segment
  fixed costs**
  (import ~5–10 s and the checkpoint-literal elaboration, unmeasured —
  the §5 charter item 2's job);
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
both feeding unit 2's mid-run-segment slice (§5, charter item 2):

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
  standing build); charter item 2 measures it.

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
functions + 9 value-call callees + 8 defer callees (probe A2)**, with
the hot ones (`raftpb.Message.GetType` 442
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
segment before any generation — the §5 charter's item 2, and it is
the route's go/no-go gate.

**(d) Found while studying: the verified fast-twin evaluator — the
FALLBACK.** If the mid-run measurement shows per-step or literal costs
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
`stepFn`'s ~50 arms) that the mid-run measurement may prove
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

**RECOMMENDED: route (c), with (d) as the armed fallback and the
mid-run measurement as the explicit go/no-go.** [AGENT] — the whole decision; grounds:
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
3. The go/no-go, logged: project the full segmented cost from item
   2's numbers. GO → unit 3 charters the generator + wave plan
   (segments are file-disjoint units; the composition file is the
   serialization point). NO-GO (> ~200 CPU-h projected) → unit 3
   charters fallback (d), carrying slice 2's measurements as its
   baseline.
4. Honesty rails carried forward: every number derivation-anchored to
   a record file; bounds as bounds; the probe fuel numbers are
   scaffolding — the proof re-derives its fuel by composition; a
   killed probe's kill point is a datum, not a failure to hide.

---

## 6. U2 — the go/no-go measurement (2026-08-22, this unit): **NO-GO
for (c); pivot to (d)**

Charter items 1–3 executed. Raw records:
`docs/campaign-arc2-probes/records/seg350k.out`,
`records/probeA2-defercallees.out`, and the updated
`records/kprobes-small.out`.

### 6.1 The reflector works, and is cheap

`StateWire.lean` (ToExpr derives for the value/config grammar +
`twinCheckpoint%`, fail-loud, table-drift-checked) +
`TwinCheckpoints.lean` (the 350k checkpoint, program-generic spelling
over `twinBase`): **build 3:47 wall / 2.7 GB peak / 101 MB olean**.
The compiled prelude+350k-step run dominates; reflection and
elaboration of the 19,093-cell heap literal are not the bottleneck.
This artifact is route-independent and carries to (d).

### 6.2 The mid-run kernel segment curve (the decisive datum)

Checkpoint index: 350,000 — the coordinator's stated 300k–400k range;
the heap there is 19,093 cells (probe C), roughly half the end-of-run
36,376, so §6.3's projection carries the heap-linear band up to 2×
rather than treating 19k as the ceiling ([AGENT], logged).

From the 350k checkpoint (heap 19,093 cells), `∃ x, stepFnIter k … =
.ok x` by `with_unfolding_all exact ⟨_, rfl⟩` under
`smartUnfolding false` (expected shapes #eval-confirmed first;
48G cap, timeout 3600, RSS polled at 2 s):

| k | wall | peak RSS | outcome |
|---|---|---|---|
| 100 | 2:13 | 16.1 GB | PASS |
| 250 | 7:46 | 39.7 GB | PASS |
| 500 | 11:33 | 51.5 GB read at kill | **OOM (137) under 48G** |
| 2000, 8000 | not run | — | superseded: they OOM at seg-500's identical prefix point; replaced by the 100/250 slope points ([AGENT], logged) |

Marginal rates at 19k cells, from the 100→250 stretch: **2.22 s/step,
157 MB/step** ((466−133) s and (39.7−16.1) GB over 150 steps). The
seg-500 kill is consistent: 39.7 + 250 × 0.157 ≈ 79 GB ≫ 48.
Against the early-run rates (§1.2: ≥ 0.29 s/step, ≥ 4.5 MB/step at
≤ 700 cells): per-step cost scaled ~7× and retention ~35× for a ~27×
larger heap — **the kernel's per-step cost and retention are
heap-size-linear**, as §2.1 feared. A 100-step mid-run segment IS
kernel-checkable — the route is not impossible, just priced out.

### 6.3 The projection, re-derived at measured mid-run rates

- **Time**: 711,616 × 2.22 s ≈ **439 CPU-h** at the 19k-cell rate;
  the run's second half runs at up to 36k cells, so the honest band
  is **~440–800 CPU-h** (heap-linear scaling), versus the ~200 CPU-h
  NO-GO trigger.
- **Segments**: at 157 MB/step, a 48G budget holds ~280 steps →
  **~2,500 segment modules**; even a 110G cap holds ~680 → ~1,050.
- **Checkpoint storage**: one 19k-cell checkpoint olean is 101 MB →
  **~100–250 GB** of build artifacts at 1,000–2,500 checkpoints, all
  needed simultaneously by the composition closure.
- **Wall**: the box fits at most two 48G segment jobs beside the
  standing lanes → 440–800 CPU-h ≈ **9–17 days wall at 2-way**. At
  the asked-for parallelism levels the caps must shrink with the
  concurrency: 8-way × 48G = 384G and 16-way = 768G **do not fit the
  125G box**; the fitting variants are 8-way × ~15G (segments of
  ~70 steps → ~10,000 modules; kernel work /8 ≈ 55–100 h wall, PLUS
  ~45 s × 10,000 ≈ 125 CPU-h of per-segment fixed cost and ~1 TB of
  checkpoint oleans) and 16-way × ~7G (segments of ~20 steps —
  ~36,000 modules; the fixed costs dominate outright). Parallelism
  does not rescue the route: shrinking per-job memory shrinks the
  segment, and the per-segment fixed cost (import + checkpoint
  literal, ~45 s measured at seg-100 net of steps) then eats the
  gain.

**VERDICT: NO-GO** — the §5 trigger (projected > ~200 CPU-h) fires at
more than double, before storage (~10² GB) and module count (~10³–10⁴)
are even charged. [AGENT], per the charter's own numeric gate.

### 6.4 Unit 3 (revised charter): fallback (d), the verified
fast-twin evaluator

Carrying forward: the reflector + checkpoint module (reused), the
measured curves (the baseline (d) must beat), and the complete call
census (probe A + A2: **226 static + 9 value-call + 8 defer callees =
243 distinct functions**; defer registrations 272, exactly matching
probe A's defer-site executions — the gap is closed).

Slices, in order:
1. **The opening measurement (before any evaluator build)**: a
   kernel-reduction microbenchmark of the candidate heap
   representation — a Nat-keyed binary trie at 36k entries, 10k
   set/lookup ops under `with_unfolding_all rfl`, capped + timed +
   RSS-polled. Validates the two numbers everything rests on:
   per-op kernel time (target: ms-scale vs the list's ~2 s/step) and
   per-op retention (target: ~KB-scale vs 157 MB/step). A failed
   target here parks (d) too and the campaign reports the witness
   HONESTLY BLOCKED at kernel scale pending a ruling-class
   conversation (e.g. a `Nat`-packed state encoding exploiting kernel
   GMP arithmetic — exotic, unscoped).
2. **The evaluator**: `HeapT` (trie) + abstraction `γ : HeapT → Heap`
   + WF invariant (nodup keys — `alloc` uniqueness); `stepFast` over
   the represented state, per-arm; the simulation theorem family
   `γ`-commuting per arm, composed to
   `runConfigFast/stepFnIterFast ↔ stepFnIter` — proved ONCE,
   symbolically, over ALL states (no per-run content). Statements
   untouched (§3.1: the accelerator never enters the statement
   closure; the witness transports through the simulation instance).
3. **The witness assembly**: reflect the seeded state into `HeapT`
   (reflector reused; `γ`-agreement kernel-checked once at the small
   post-prelude heap), kernel-evaluate the fast run — monolithic if
   retention allows (~KB/step × 711k ≈ tens of GB), else 2–5
   checkpointed fast segments — transport, compose with the prelude
   equation and readout, discharge `CompletionWitness`.
4. Non-goals, restated: no GoCore change (the fast evaluator is
   proof-side); no statement change; no envelope pin. If any slice
   wants one, it is a ruling request, parked.

---

## 6.5 U3 — the (d) gate: the trie microbenchmark (2026-08-22)

Bench: `docs/campaign-arc2-probes/trie-bench.lean` — a binary trie
keyed by canonical LSB-first address bits (ALL recursion STRUCTURAL —
the kernel does not usefully reduce `WellFounded.fix`, a design
constraint recorded here for the evaluator build), values
`GoLean.HeapCell`; seed 36,376 entries (the twin's end-of-run heap,
probe C); `nops` alternating LCG-keyed lookup/set;
`checksum + finalTrie.count` so the full final trie is FORCED (the
kernel's lazy whnf cannot skip set paths). Expected values
#eval-confirmed first.

**PASS TARGETS, stated before the kernel runs** ([AGENT]): marginal
per-op kernel time ≤ 25 ms AND marginal retention ≤ 2 MB/op at 36k
entries. Miss ⇒ (d) parks and §6.6's convergence clause governs.

First kernel points (16G cap): nops=0 and nops=1000 both OOM(137) at
~4 min — but the arithmetic is the finding, not the failure: nops=0
IS 36,376 in-kernel seed inserts + the count fold, so the kill reads
~6.4 ms/insert CPU and ~0.47 MB/insert retention — the cap was sized
for the op-marginal, not the seed build. (The real evaluator never
builds its seed in-kernel — the seed is a reflected literal, §6.1's
mechanism — so the seed-build points are a worst-case variant kept
for honesty.) Rerun at 48G:

Measured (48G cap, RSS polled at 1 s; record
`records/trie-bench.out`):

| nops | wall | peak RSS | outcome |
|---|---|---|---|
| 0 (= the 36,376-insert seed build + count, in-kernel) | 4:25 | 17.7 GB | PASS |
| 1000 | 4:39 | 18.1 GB | PASS |
| 10000 | 6:04 | 22.1 GB | PASS |

Marginal per op (1000→10000, 9,000 ops): **9.4 ms/op time,
0.44 MB/op retention**; the 0→1000 stretch reads 14 ms / 0.40 MB —
consistent. Seed build: 7.3 ms/insert. Against the naive list heap at
the same 19k–36k-cell scale (§6.2: 2.22 s/step, 157 MB/step): the
trie is **~240× faster and ~360× lighter per heap op**.

**VERDICT: the (d) gate PASSES** — both pre-stated targets met with
>2× headroom. [AGENT.]

**The (d) projection, re-derived at bench rates** (bounds as bounds):

- Per-step evaluator cost = (heap ops/step, ~1–3) × 9.4 ms + the
  NON-heap step work (config/cont matching, value normalization, env
  ops) which this bench deliberately does not measure — the known
  unknown. At 2×–10× the heap-op component: **711,616 steps ≈ 4–60
  CPU-h**, inside budget even at the pessimistic end.
- Retention ~0.4–1 MB/step → monolithic ≈ 300–700 GB: still
  segmented, but at 48 GB/segment ≈ 50k steps/segment →
  **~14 checkpointed fast segments** (vs (c)'s ~2,500) — the
  reflector and checkpoint machinery carry unchanged.
- The evaluator build therefore carries its OWN mid-build measurement
  gate: one `stepFast` segment from the (converted) 350k checkpoint,
  measured before full assembly — same discipline as §6.2, catching
  the non-heap-work unknown before it is load-bearing.

## 6.6 Convergence with Arc 4 (coordinator directive, 2026-08-22)

A4-U2 (in flight, `campaign-arc4`) is building the handler-fragment
Sym extension after the Arc-4 pilot refuted hand-walked handler
equations on cost. Had this gate MISSED, the witness's remaining
route was a Sym-automated completion walk; the gate passed, but the
carry-forward statement stands either way, so nobody re-derives it:

- **The reflector + checkpoint (`StateWire.lean`,
  `TwinCheckpoints.lean`)** — route-independent: a Sym walk over the
  twin needs concrete start states per window exactly as (c)/(d) do;
  `twinCheckpoint%` provides them at any step index, program-generic.
- **The census (243 functions: 226 static + 9 value-call + 8 defer;
  hot-path counts in `records/probeA-census.out`)** — the Sym route's
  handler-fragment coverage checklist: which functions its fragment
  must cross, weighted by execution count.
- **The measured curves (§1.2, §6.2, §6.5)** — the baseline any
  Sym-transported window cost must beat, and the segment-sizing
  arithmetic (retention → steps per module) transfers to Sym windows
  unchanged.
- **The kernel design constraints found here** — structural-only
  recursion (no `WellFounded.fix` on the reduction path),
  `smartUnfolding false`, the seed-as-reflected-literal rule, and the
  forced-fold discipline (a lazily-skippable result under-measures) —
  apply to ANY kernel-checked route over this machine.

## 6.7 Unit-4 charter — the evaluator build (route (d), GO)

Sliced per §6.4 items 2–3, refined by the gate's findings; each slice
parkable, measure-first:

1. **Design note + `HeapT` core** (`proofs/GoLeanProofs/FastEval/`
   namespace, proof-side, aggregator-imported): the binary trie at
   `HeapCell` values with canonical-bits keying (the bench's shape,
   STRUCTURAL recursion only); abstraction `γ : HeapT → Heap` (or the
   relation form `RepHeap`), the WF invariant (key canonicity +
   nodup — `alloc` uniqueness supplies it), and the op-level
   simulation lemmas: `lookup`/`set`/`alloc` commute with `γ` under
   WF. These are ∀-state symbolic lemmas — kit-style, no per-run
   content.
2. **`stepFast` + per-arm simulation**: the represented state
   `ExecStateF` (tables verbatim, heap as `HeapT`); `stepFast`
   mirroring `stepFn` arm by arm; per-arm lemmas
   `γ(stepFast σF c ch) = stepFn (γ σF) c ch` (Except-valued — errors
   included), composed to `stepFnIterFast_sim`. The arm count is
   `stepFn`'s (~50); mechanical, wave-parallelizable AFTER the shape
   is fixed on 2–3 exemplar arms.
3. **The mid-build measurement gate**: convert the 350k checkpoint
   (`γ⁻¹` at reflection — extend `twinCheckpoint%` with a trie
   emitter, or convert once compiled and kernel-check `γ` agreement),
   run ONE `stepFnIterFast` segment (~2,000 steps) under cap +
   timeout; this prices the non-heap step work (§6.5's known
   unknown) BEFORE the remaining arms/waves are built. Its own
   numeric trigger: projected full run ≤ ~60 CPU-h proceeds; a miss
   pauses for re-planning against §6.6's Sym convergence.
4. **Assembly**: seed reflection + `γ`-agreement check, ~14 fast
   segments, transport through `stepFnIterFast_sim`, compose with the
   prelude equation and readout, discharge `CompletionWitness`.
5. **Guardrails, restated from the coordinator's directive**: the
   evaluator is UNTRUSTED METHOD — it never appears in any statement
   closure, stays out of designated-statement reach exactly as Sym
   does (§3.1; the statement-TCB walker would flag it, and the
   docstrings say so); no GoCore/frontend/scripts changes; every
   public simulation theorem lands with its `#print axioms` pin per
   kit convention.

---

## 6.8 U4 — the evaluator built and proved; the mid-build gate:
MARGINAL GO; the assembly staged as unit 5 (2026-08-23)

**The machinery is PROVED** (all kernel-checked, zero hatches, pins in
`proofs/Audit/FastEval.lean`, everything in the aggregator/1b2 sweep):

- `FastEval/{Heap,Ops,Loops,Shared,Values,Stores,Frames,Iter,Step}`:
  the trie heap + γ-abstraction; the three primitives; the generic
  loop transport; the wave's three helper towers (one authorized
  wave, three forked workers, all green, re-verified, reports folded);
  `stepFast` (the full arm-for-arm mirror, census-unexercised
  machinery fail-closed) and **`stepFast_ok`** — the per-step
  one-directional refinement — plus `iterF`/`iterF_ok`/`iterF_add`.
- `Specs/TwinCheckpointsF` (seed + 350k trie checkpoints, reflected)
  and `Specs/TwinPrelude`: **`twin_prelude_eq`** — the kernel re-ran
  the seed + `StateWf` + all 1,382 init steps against the reflected
  literals AND checked `γF twinSeedF` = the post-prelude state in one
  equation (8:18 / 36.7 GB, `artifacts` measured; this is the single
  equality that replaces any carried trie invariant).

**The mid-build gate, measured** (`records/fastseg.out`): from the
350k checkpoint — fast 500 steps: kernel **PASS 2:28 / 21.6 GB**
(the same slow segment: OOM(137)@48G at 11:33); fast 2000: OOM(137)
@40G at 7:49 — the kill point. Bounds: ≤0.30 s/step (ceiling incl.
fixed), ≥0.21 s/step on the 500→kill stretch; retention
≥14.5 MB/step. Reading: **the trie removed the heap-size dependence**
(slow was 2.22 s / 157 MB per step here); the residual is the
machine's INTRINSIC kernel step cost, consistent with the slow
small-heap rates (§1.2: 0.06–0.29 s/step) — ~10–15× time and ~8–11×
memory better than slow at this heap, uniform in run position.

**Projection** (bounds as bounds): 711,616 × 0.10–0.30 s ≈ 20–59
CPU-h kernel + per-segment fixed (≈1,200 steps/segment at 24G →
~590 segments; ≈2,900 at 48G → ~245; fixed ≈1.5–2 min each → 6–20 h)
≈ **~35–80 CPU-h total, ~30–60 GB of checkpoint/segment artifacts,
~1.5–2.5 days wall at 2–3 concurrent capped jobs**. Against the §6.7
trigger (≤ ~60 CPU-h): **MARGINAL GO** — inside under the central
estimates, over under the pessimistic bound. Two cheap levers before
the long run, both unit-5-internal: 48G segments (fixed-cost −60%),
and batch checkpoint emission (ONE compiled pass, ~12 min, vs
per-index reruns). A miss after the levers re-poses §6.6.

**Findings recorded**: (i) the γF lazy view is kernel-lazy but
INTERPRETER-STRICT — compiled fast-segment runs materialize the dump
per pure-helper call (the 20+ min pre-check kill); kernel checks are
unaffected and double as the stub detector (500 steps stub-free by
PASS; stub-absence beyond is closed mechanically by each unit-5
segment check — a stub fires as a fast elaboration-failure with a
visible `.error`, never an OOM). (ii) Worker A's census-classifier
blind spot (nullary strict ops) — found, mirrored, recorded.

**UNIT 5 (staged, not executed — the charter):**
1. Batch trie-checkpoint emitter (multi-index command elaborator in
   `StateWire`, one compiled pass) at the segment boundaries chosen
   from this gate's measured retention;
2. scripted segment-module generation
   (`iterF stepFast nᵢ ⟨ckptFᵢ⟩ Cᵢ chᵢ = .ok ⟨ckptFᵢ₊₁⟩` —
   equality-to-next-literal for chaining), waved 2–3 concurrent
   capped kernel jobs;
3. composition: `iterF_add` folds the segments → ONE `iterF`
   equation → `iterF_ok` → `stepFnIter 711616 …` → the kit's
   `runConfig` glue + `twin_prelude_eq` →
   `twinRun 711616 [] = .ok r` → **`CompletionWitness`** discharged;
   fuel re-derived by the chain arithmetic.

---

## 6.9 U5 — the staged assembly: successor re-projection and GO
(2026-08-23)

Successor re-verification at 0c462c7c passed (build 480 jobs rc 0;
axioms = pins verbatim; hatch grep clean). The §6.8 levers were then
MEASURED before launch (records/fastseg2.out):

- **The 48G-segment lever is REFUTED**: fastseg-k2000@48G OOM(137) at
  507 s — fast-segment retention past 500 steps is ~16.7–20 MB/step
  (fastseg-k1000@36G PASS 3:59 / 30.0 GB pins the slope), not the
  14.5 MB/step §6.8 extrapolated; 48G holds ~1,500 steps, not ~2,900.
- **The batch-emission lever WORKS and is validated**:
  `twin_ckpt_groupF%` (one incremental compiled pass per group,
  `addDecl` without compiled code) gate-checked — the batch literal at
  350k is kernel-EQUAL to the from-0 `ckptF350k`, and the exact
  segment shape (equality-to-next-literal) kernel-checks; both in
  3:49 under 24G.

**Re-projection** (decomposition: marginal 0.182 s/step + 16.7 MB/step;
fixed ~57 s + 13.3 GB/segment): at SEG=1000 (712 segments, last 616;
36G cap; 2-wide batched waves in a 74G scope) — kernel marginal
36.0 CPU-h + per-segment fixed 11.3–13.8 + emission ~5.4 + composition
<1 ⇒ **central ~53–55 CPU-h (band ~45–67) ≤ the ~60 CPU-h pause
trigger: GO.** Execution record, manifest, and judgment calls:
`docs/campaign-arc2-log.md` (U5) and
`docs/campaign-arc2-probes/records/u5-manifest.tsv` (recomputed from
oleans, never restated).
