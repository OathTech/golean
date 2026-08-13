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
| `proofs/GoLeanProofs/StepKit.lean` (NEW) | P1 conditioned one-step glue (`stepFnIter_one`, `stepFn_strict_apply`, `stepFn_store_step`, `stepFn_stmtOp_apply`, `stepFn_var`, `stepFn_init_seq`, `stepFn_seqn`, `stepFn_seq_pop`, `stepFn_storeK_nil`, `stepFn_mapAssign_apply`, `stepFn_snapshot`, `storeTarget_addr`), P9 `stepFn_seqn_splice`, P11 heap-append/set kit (`lookup_append_left/right`, `set_append_right`, `set_fresh`, `base_beq_false`, `lookup_cons_ne`, `set_cons_ne`, `set_singleton_self`, `lookup_singleton_self`) | (in progress) |

## §3 Per-lift measurements (rule (c))

(recorded per retrofit as they land)

## §4 Gap B status

(recorded at the first-consumer test)
