# TCB and proof-infrastructure layering (user directives 2026-08-01)

Two standing architectural requirements, recorded for the
proof-automation arc's CLOSE-OUT and binding on everything after
(especially the Raft-properties work). Persisted here so they survive
compaction and agent switches; both are audit dimensions from now on.

## 1. The TCB doctrine: Iris stays fully outside

**The core aim: a consumer of a top-level GoLean theorem must be able
to UNDERSTAND the claim from 'base' definitions over the interpreter —
never needing Iris, WP, or any 'fancy' theorem to know what was
proven.** Trust-to-understand = the transitive definitions of the
STATEMENT, not of the proof. Proofs may use anything (Iris is a proof
device behind the exit pipes); statements may not.

The statement-dependency ladder, from best to acceptable:

1. **First-order readouts over the interpreter** (`execStmt` run ⇒
   `loadLoc` value — the `goldenReturnsTwo` /
   `quorumOneKnownReturnsTwelve` / `quorumThreeAllReturnsSix` shape):
   the gold standard. Every headline theorem SHOULD ship one.
2. **Surface judgments** (`GoTriple`/`GoSpec`/`GoFuncSpec*` over
   `HProp`/`sat`/heaplets): acceptable — the deep-embedded SL is small
   and self-contained — but it is already more than "base", so the
   readout corollary stays mandatory alongside it.
3. **Relation-quantified statements** (`Steps` — needed for
   invariance/mid-run properties, later for trace/refinement claims):
   acceptable when the property is genuinely about mid-run states;
   the machine relation joins the statement TCB, Iris still must not.

**For Raft:** ghost state, history variables, linearization points,
and prophecy-style machinery are PROOF devices. The moment one appears
in a top-level STATEMENT, the doctrine is violated — the statement
must be reformulated (trace properties over the machine relation;
first-order readouts where possible) before the theorem is claimed.

**Mechanization owed at close-out (not just discipline):**
- A per-theorem statement-TCB gate in `proofs/Audit.lean`: for each
  designated headline theorem, walk the constants of its TYPE
  (statement closure, not proof closure) and FAIL the build if any
  lives under the `Iris` namespace (same `#eval` style as the axiom
  sweep). This turns the doctrine into a build error.
- Extend the surface-purity ci scan from its two-file list to the full
  set of statement-bearing modules (today `QuorumTargets`,
  `QuorumRefSpec`, `AutomationTargets` are Iris-free by import chain
  but UNGATED — found 2026-08-01, the exact silent-reopen class the
  gate's own 2026-07-23 hardening comment warns about).

## 2. The layering doctrine: general infra / target infra

**Ideal division of labor: (1) generalized proof infrastructure that
works for ANY GoLean proof; (2) target-specific (today: quorum/raft)
infrastructure that only USES the general layer.** The target layer
contains: pins, walks, per-program invariants, and instance theorems —
never laws, lifting cores, or tactics.

Current state (assessed 2026-08-01): the division mostly holds —
Lang/Ghost/Lifting/HeapBridge/Laws/*/Tactics/Surface* are general;
Specs/* is target — with known debt:
- `Laws/QuorumOps.lean` is misnamed/misplaced: its LAWS are general
  (the stmtOpK walk family, mapLookup, sortSlice) with quorum only in
  witnesses; the general laws belong in properly-named general
  modules, witnesses staying wherever their pinned programs live.
- Nothing ENFORCES the direction. Owed at close-out: an import-
  direction lint in ci (general modules — Laws/*, Lifting, Ghost,
  Tactics/* — must not import Specs/*; Tactics must not import GoCore
  semantics at all, which `GoWalk.lean` already satisfies by
  construction), plus a short layer map in `docs/architecture.md`.

## Close-out checklist (this arc)

1. Move general laws out of `QuorumOps.lean`; layer map documented.
2. Statement-TCB gate + widened surface-purity scan (above).
3. Both doctrines as named dimensions in the final pre-merge audit
   (alongside semantics / vacuity / over-specialization /
   gate-honesty): "is any top-level statement's meaning dependent on
   Iris or on target-specific machinery it shouldn't need?"
