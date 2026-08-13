# Consolidation slice (verified-examples arc) — session record (2026-08-13)

Status: IN PROGRESS. Charter: `docs/2026-08-12_verified-examples-arc-charter.md`;
predecessor record: `docs/2026-08-13_verified-examples-scale-out.md`
(findings 1–22, promotion ledger §8); convention of record: form note
§12 (the active-abstraction loop, user ruling 2026-08-13). Lane
`foundation`, branch `foundation-s1`.

The slice's shape: lift the measured, repeated proof patterns of the
seven examples into a shared kit (worklist: the placement-generic
segment/composition lift; P4 entry equation; P5 setup-loop induction;
P8 frame-rebase; the MapMem promotion), then prove the kit on its
first consumer — the re-attempt of gap B (`wordcount_ok` over
`wordcount_harness`).

## §1 THE STORM DIAGNOSIS (finding 21 closed — root cause found,
mechanism verified by experiment)

Finding 21 recorded the blocker as an isDefEq/whnf storm at the
`storeTarget_addr` application in `wcH_count_iter`, with the trigger
believed to be "the COMBINATION of the rw-surgered `stepFn_init_seq`
hypothesis and/or the segment-lemma haves in context with a subsequent
big application". The bisection this session (instrument:
`.tmp/wcB-repro4.lean`; variants `.tmp/prof-{A,B,C,D,E}.lean`, all
capped `GOLEAN_MEM_MAX=24G`, 400K-heartbeat probes) REFUTES the
combination theory and pins the true mechanism:

* **Variant B (context-minimal)**: ONLY `htail1na` + the
  `storeTarget_addr` application — no rw-surgered `hInit1`, no segment
  haves, no chains — storms identically (same diagnostics counters:
  ~200K `BEq.beq`, ~134K `Addr.rec`, ~13.4K `Heap.lookup` unfolds,
  ~33K `f a =?= f b` heuristic hits on `List.append`). The context
  hypotheses were never the trigger.
* **Variant C (trace.profiler)**: the timeout is the unification of
  `htail1na`'s type against the lemma's `hlook` premise, and the trace
  shows the expected type carrying **unassigned metavariables inside
  the σ argument** — `(dead ++ [(?m.131, ?m.132)])` where `htail1na`
  has the actual constructor pair. The isDefEq tree then delta-unfolds
  `Heap.lookup (frontH … ++ dead ++ …) (.base ⟨na⟩)` — a 16-deep nest
  of `if (Loc.base ⟨k⟩ == Loc.base ⟨na⟩)` STUCK on the symbolic `na` —
  and the per-level timings double (22.2s → 16.5s → 8.1s → 4.0s …):
  **exponential in the concrete front length**, uncached because the
  terms carry metas.
* **Variant D (@-application, hnorm hoisted)**: still storms —
  argument style is irrelevant, matching finding 21's observation. The
  metas are POSTPONED-ELABORATION metas (anonymous constructors /
  dot-notation under the `++` instance indirection inside the big
  state argument), present regardless of named-vs-explicit style.
* **Variant E (full type ascription)**: `have hst1 : <the complete
  storeTarget equation> := storeTarget_addr htail1na hnorm` — implicits
  inferred from a META-FREE pinned expected type — is **INSTANT**
  (exit 0 at 400K heartbeats).

**The mechanism, stated once:** when a conditioned step lemma is
applied with the big concrete-front state passed as an argument, the
postponed metas inside that argument defeat structural unification
against the (meta-free) hypothesis type; isDefEq's fallback is delta
comparison of `Heap.lookup` over the concrete front at a SYMBOLIC
address — stuck-`if` nests compared pairwise without caching, ~2^N
work in the front length N. Canonical wordcount (N = 9) squeaks under
2M heartbeats; the harness placement (N = 16) is ~2^7 ≈ 128× more —
the 52 GB storm. It was never about the rw surgery, and "the same
application is instant standalone" (finding 21) is explained: a
standalone file's `have` had its state spelled where elaboration
completed before unification.

**The two structural fixes** (both adopted):
1. *Discipline (the E-form)*: at any application site that mentions a
   big concrete state, pin the FULL result type on the `have` (or let
   the hypothesis pin the state — finding 15c generalized). No
   concrete state term is ever left for the unifier to compare
   against a meta-laden copy.
2. *The placement-generic kit (the lift)*: segment and composition
   lemmas stated over an ABSTRACT `σ : ExecState` + the lookup facts
   they need + abstract placement addresses + an abstract outer
   continuation. In the generic layer the unifier only ever matches a
   VARIABLE state — the storm class is structurally impossible, and
   the per-placement instantiation is lemma application against
   fully-pinned statements. This also collapses the ~800-line
   verbatim-rename duplication that finding 21's disposition flagged.

## §2 Kit module map (updated as lifts land)

| module | contents | consumers retrofitted |
|---|---|---|
| `proofs/GoLeanProofs/StepKit.lean` (NEW, namespace `GoLean.Surface`) | P1 conditioned one-step glue (`stepFnIter_one`, `stepFn_strict_apply`, `stepFn_store_step`, `stepFn_stmtOp_apply` — the general `ch'` form, subsuming MinMax's `ch = ch'` copy, `stepFn_var` — absorbing BinSearch's `stepFn_var_load`, `stepFn_init_seq`, `stepFn_seq_pop`, `stepFn_storeK_nil`, `stepFn_mapAssign_apply` + `stepFn_snapshot` — GENERALIZED from WordCount's `tU64`/`"c"`-specialized copies to arbitrary key/value types and bound names, `storeTarget_addr`), P9 `stepFn_seqn_splice` (absorbing WordCount's `stepFn_seqn`), P11 heap-append/set kit (`lookup_append_left/right`, `set_append_right`, `set_fresh`, `base_beq_false`, `lookup_cons_ne`, `set_cons_ne`, `set_singleton_self`, `lookup_singleton_self`), `natFromNonneg_cast` | Gcd, Reverse, MinMax, BinSearch, InsertionSort, WordCount (all six machine-layer examples; the retrofits are the fixture witnesses) |
| `proofs/GoLeanProofs/SliceMem.lean` (extended) | P2 slice-value plumbing (`getElem?_mapU`, `getD_mem`, `mem_set_of_mem`, `locSup_mapU`), P3 normal-form additions (`unorm_nat_of_lt`, `unorm_add_nat`), `applyStrictOp_mod_u64` | same six |

Layering call (recorded): the step glue sits in a NEW top-level module
(not FuelMeasure — that stays the fuel/termination kit; not SliceMem —
that stays statement-side-safe slice vocabulary), in the
`GoLean.Surface` namespace so the example modules' existing `open`s
resolve the promoted names with zero call-site churn. Pure-list and
`applyStrictOp`-fact lemmas go to SliceMem beside their existing
family.

## §3 Per-lift measurements (rule (c))

**C1 (StepKit + SliceMem promotion, rows P1/P2/P3/P9/P11 + glue):**

Line deltas (git diff): −663 duplicated lines across the six example
files (BinSearch −130, WordCount −282, InsertionSort −98, Reverse −77,
MinMax −64, Gcd −52); +79 SliceMem, +254 StepKit (new) ⇒ net −330,
and every future example starts ~110 lines lighter.

Elaboration-time deltas (single-file `lean`, same machine, before →
after): Gcd 0.78→0.76 s, Reverse 2.75→2.77 s, MinMax 3.02→3.00 s,
BinSearch 8.72→8.48 s, InsertionSort 9.63→9.59 s, WordCount ≈150→151 s
(peak RSS ≈55 GB, unchanged). Within noise, as expected — P1–P3/P9/P11
are duplication lifts, not elaboration-cost lifts; the cost lift is the
placement-generic layer (§1 fix 2).

Cap-budget note (recorded deviation): the slice instruction set full
gates at `GOLEAN_MEM_MAX=48G`, but WordCount's SINGLE-FILE elaboration
peak is a measured ~55 GB (52 GB under a 48 G cap = kill, reproduced) —
the gate runs at the default 64 G, one build at a time, nothing
parallel. Finding-22-adjacent evidence: the heavy module, not
concurrency, owns the budget.

## §3b Gate state per commit

* C1: `scripts/ci` PASS (full summary green; baseline diff FULL
  1550/1550 no regression; escape-hatch preflight clean).

## §4 Gap B status

(recorded at the first-consumer test)
