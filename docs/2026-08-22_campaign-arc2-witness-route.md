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
| 10000 | (running at memo draft; filled below) | | |

Marginal rates from the table: (K=10→100): 0.24 s/step;
(K=100→1000): 0.062 s/step. Fixed cost (K=0 — import loading, the
elaborator's decode-free unfold of `twinLowered`, `seedGlobals` +
`StateWf` over the whole 9.3 MB program, and the init-phase fuel-out):
~32 s.

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

(Completed after K=10000; see §2 final numbers below.)

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

(Filled with §2's numbers.)

## 5. Recommendation and unit-2 charter

(Filled after §2/§4.)
