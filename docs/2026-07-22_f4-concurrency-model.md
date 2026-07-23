# F4: the concurrency model and the fine-grained reshape (2026-07-22)

Design of record for the F4 decision (TODO.md) and the resolution path for
**BUG-002** (`docs/BUGS.md` — expression-step atomicity, the latent
concurrency unsoundness). Converged in design discussion 2026-07-22; user
directions quoted where they bind. Companions:
`docs/2026-07-22_fault-model.md` (the fault-model charter this note
absorbs), `docs/2026-07-22_arc-e-while-invariant.md` §2′ (how the
granularity problem surfaced), `docs/2026-07-22_invariant-readout-design.md`
§4 (proof-theoretic enforcement over global memory).

## 1. The decision: fine-grained shared-memory concurrency, SC, memory-op
granularity

**Target (user direction):** full shared-memory concurrency — mutexes,
`sync/atomic`, lock-free patterns; "the actually interesting code."
Channel-confinement-only concurrency is REJECTED as a target (it excludes
most real concurrent Go; "CSL-proofs-only is a trivial kind of
concurrency"). The purpose of acting now is to **avoid leaving hostages to
fortune**: not to build concurrency yet, but to stop baking in an
over-coarse semantic model that would bite when we do.

**Granularity: memory-operation steps, SC interleaving, word-sized
atomicity.** This is decidable today — Go has a published, deliberately
designed memory model (revised 2022): happens-before via sync primitives;
**DRF programs get SC**; `sync/atomic` is sequentially consistent; racy
plain access gets only limited guarantees (no out-of-thin-air; multiword
races can corrupt). So:

- individual loads and stores are the atomic steps of the relation;
- the interleaving semantics is sequentially consistent;
- `sync/atomic` operations are modeled as (SC-)atomic steps — faithful,
  not an idealization;
- **plain-access data races are out of verification scope** (as in Goose):
  verified programs must confine races to atomics/sync. Weak memory is
  owed by nobody unless we ever target deliberately racy plain access
  (we don't). The DRF-SC scope condition is stated explicitly on
  concurrency-facing soundness claims, per the fault-model charter.

This is GooseLang's validated choice; we adopt it rather than reinvent.

## 2. The deletion directive (user, 2026-07-22 — binding)

**The current big-step rules are deleted completely.** `ExprR`, the
statement rules that consume it, and `Eval`'s big-step evaluation cluster
do not survive as an interop shim, an alternate mode, or a compatibility
layer. Everything downstream — correspondence, WP laws, walks, witnesses
(including arc E's `wp_while_inv` family) — is rebuilt against the new
rules or retired. Continuity lives in the **corpus + frontend + tracked
baselines**, not in code: the reshape's acceptance gate is ZERO sequential
drift on the full differential (718 cases at the time of writing), the
strongest safety net the project owns.

Cosmetic open choice: the Surface layer's statements quantify over
`execStmt`-shaped runs. Either keep an `execStmt`-shaped function —
fuel-bounded iteration of the NEW step function, possibly under the old
name — so Surface statements keep their form (this is the new semantics
packaged, not a shim: no old rule appears in it), or restate the Surface
statements against a new API. Decide at reshape time; both are honest.

## 3. Architecture: one semantics, instantiated

The reshape's structural payoff, beyond unblocking concurrency:

- **Rel becomes a fine-grained machine**: expression evaluation enters the
  configuration language (expression configurations / evaluation
  contexts); read-write statements (`assign`, …) decompose into separate
  load and store steps. The `Choices` move extends to the scheduler: the
  relation over-approximates the adversarial scheduler; executables
  instantiate it.
- **The interpreter is iterated step-function**: write
  `stepFn : Config → State → Choices → …`, prove it sound AND complete
  against `Rel.Step` **rule-by-rule**, define execution as fuel-bounded
  iteration. The historically hardest proofs in the repo — the T1/T2
  big-step/small-step correspondence inductions — largely dissolve into
  per-rule lemmas plus composition, because the interpreter becomes the
  relation's instantiation instead of an independently-written artifact.
- **The WP layer gets the standard structure**: evaluation contexts give
  `wp_bind` and `wp_atomic`, retiring both recorded workarounds (the
  invariant-opening-in-lifting-slots pattern, the premise-style condition
  handling). Laws collapse toward HeapLang-style primitive laws; the
  Goose-shaped user-facing spec forms (e.g. the Bool-indexed loop
  invariant) carry over with simpler plumbing.
- **What survives untouched**: frontend, corpus, oracle, negative lane,
  baselines; Surface statement CONTENT (form per §2's cosmetic choice);
  the Iris functor bundle / genHeap machinery pattern and the once-proven
  boundary layers (`reflect`/`extract`, `embed_timeless`); all doctrine.

## 4. Concurrency differential testing (later design; anchors pinned)

Hard part, deferred to its own note when concurrency machinery starts —
but the anchors are pinned now (user direction: think Coyote / P):

- **`Choices` IS the controlled-scheduler hook.** The instrumentation
  layer Coyote/P must inject into a runtime, our architecture already
  externalizes: schedules are data fed to the executable side. PCT-style
  probabilistic schedule fuzzing (Coyote's core algorithm, with bug-depth
  guarantees) and systematic exploration (P-style; DPOR) become Choices
  generators, not runtime surgery.
- `go run` yields one schedule per run, so the oracle story changes shape:
  (a) a deterministic-output concurrent corpus (race-detector-clean,
  schedule-independent results) keeps the classic differential lane;
  (b) schedule-controlled runs on our side vs. repeated/raced `go run` for
  distribution-level agreement; (c) the Go memory model's own litmus
  tests as expected-SET cases (observation ∈ allowed-set, not equality).
- The runtime race detector gates which corpus programs may make
  whole-program claims (plain races out of scope, §1).

## 5. Fault model (absorbing the standing charter)

Per `docs/2026-07-22_fault-model.md`, which remains the detailed record:
the taxonomy (recoverable panic / unrecoverable fatal — e.g. concurrent
map access / deadlock detector / race-scope / exhaustion idealization);
the runner compares fault IDENTITY, not existence; `Rel` represents the
classes we claim; guardrail suites pin each class BEFORE machinery;
DRF/SC scope conditions stated explicitly on soundness claims.

## 6. Sync-primitive ladder (scope for the concurrency arcs, post-reshape)

1. `go` (spawn) + join via sync — the minimal fork model (Iris forkPost
   machinery already exists in iris-lean's WP).
2. `sync.Mutex` + `sync/atomic` — the minimal CSL-interesting set (lock
   invariants; atomics as atomic steps).
3. Channels (rich: buffered/unbuffered, close, nil; the north star's
   message loop) — own guardrail suite first, per the fault-model
   charter.
4. `select`, `WaitGroup`, the long tail — demand-driven.

Liveness/fairness of the scheduler stays F5-tier-2 (explicitly deferred).

## 7. Staged plan (each stage gate-validated; no goroutines before R4)

- **R0 — this note** (the F4 decision; BUG-002 resolution path pinned).
- **R1 — fine-grained sequential `Rel`**: expression configurations,
  load/store decomposition, big-step rules DELETED (§2). Gate: the full
  differential is not affected (relation-side only) but correspondence
  breaks — so R1 and R2 likely land together or on a shared branch.
- **R2 — `stepFn` + interpreter swap**: iterated-step executable replaces
  big-step `Eval`; per-rule soundness/completeness lemmas replace T1/T2.
  Gate: **zero drift on the full 718-case differential** + eval tests.
- **R3 — WP layer rebuild**: bind-form primitive laws; `wp_atomic`;
  re-derive the law set and re-prove the golden/loop witnesses; Surface
  exit pipes re-instantiated. Gate: Audit sweep + all Surface theorems
  restored (statement content unchanged).
- **R4 — goroutine rules + scheduler `Choices`** (BUG-002 closes here:
  the granularity is now honest). Gate: new guardrail suites per §5/§6.
- **R5 — concurrency differential harness** (§4's own design note first).

Sizing note: at the current fragment (~20 expression rules, 4 statement
families, ~20 laws) this is a weeks-scale rebuild with a mechanized
regression oracle — the entire reason to do it BEFORE the structs/arrays
widening doubles the fragment. "Caught early" is quantified in BUG-002.
