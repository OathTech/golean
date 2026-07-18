# Prioritization And Design-Debt Review — 2026-07-18

Written after the semantics cleanup landed in `main` (Phases 1, 2, 3-core, 4,
6-skeleton). Purpose: decide what moves us toward the `etcd-io/raft` north star
fastest, with care, and name the design debt that would hurt at raft scale.

## Where we stand

- Differential slice: 126/136 on the Gobra-reachable set; every remaining
  failure is classified (4 frontend decode gaps, 6 Phase 5 interface gaps).
  Negative lane 309/309.
- Corpus: 672 executable cases, but only ~136 have ever reached Lean. The other
  ~536 are Go-validated only, blocked before Lean by cold/rejecting Gobra
  export.
- Semantic core is clean: stable identity, fail-closed lowering, typed heap,
  lexical scoping, a small-step relational skeleton.

## The design debt, and where it converges

| # | Debt | Hurts at raft scale? | Disposition |
|---|------|----------------------|-------------|
| 1 | **Frontend throughput/coverage.** ~536/672 cases never reach Lean; Gobra rejects legal Go (`delete`, `string(65)`, `fallthrough`, some map-range), exports per-fixture via SBT, and the harness is one-file-per-package. | **Blocking.** raft is multi-package modern Go; stage 1 (`quorum`) cannot be reached through Gobra. | **Act now** — native Go frontend. |
| 2 | **Adjacency-based type recovery** (`firstStructFieldsBeforeNextDefined?`, junk item 4). Reconstructs struct defs from export layout. | Yes — raft has many types. | **Subsumed by #1**: a native frontend emits explicit type declarations and retires the heuristic. |
| 3 | **Validating through a throwaway frontend.** Every new semantics feature is currently gated on Gobra, which the roadmap says gets replaced. | Compounds — wasted effort grows with coverage. | **Subsumed by #1.** |
| 4 | **Interpreter is `partial`** (44 sites in Ops/Eval). Blocks the correspondence proofs that justify the relational skeleton, which justify eventual raft safety proofs. | Not for execution; blocks the *proof* direction. | **Contain, don't retrofit.** New semantic code total; tag existing debt (now a CLAUDE.md practice). |
| 5 | **Linear-scan state.** `LocalEnv`/`Heap`/`TypeEnv` are `List`, symbol map is `Array`, all O(n) lookup. | Yes — large heaps/type tables make execution quadratic. | **Defer with an interface.** State ops are already behind functions; swap representation when a raft-scale case actually reveals it. Do not optimize speculatively. |
| 6 | **Interface semantics (Phase 5)** still string-tagged; typed-nil equality, type-set assertions, method-set dispatch incomplete. | Partly — raft uses `Storage` and `error`, but stage 1–2 core is concrete structs + uint64 + slices + maps. | **Frontend-gated** (needs type-decl/method-set metadata). Comes with #1. |
| 7 | **Executable-only int policy** (`int`/`uint` = 64-bit; architecture-parametric relation deferred). | raft is uint64-heavy; 64-bit policy is actually correct for it. | **Fine for now.** |

The striking result: **five of seven debt items either are the frontend
decision or are unblocked by it.** The frontend is both the biggest throughput
lever and the largest debt retirement. The only debt *not* subsumed —
interpreter totality (#4) and linear-scan state (#5) — are both safely deferred
with discipline (make new code total; keep state behind its interface).

## Recommended sequence

1. **Native Go frontend, piloted on `quorum` (raft ladder stage 1).** Target
   the *existing* strict wire ADT so GoCore and lowering are unchanged — the
   frontend isolation the architecture already bought us is exactly what makes
   this a contained swap, not a rewrite. Keep Gobra alive in parallel until the
   native path covers the current 136 (no coverage regression). Success =
   `quorum`'s vote math runs Go-vs-Lean, multi-package, natively.
   - Careful, not reckless: start narrow (one pure package), reuse the wire
     format, add a batched/package export path so throughput scales.
2. **Goose/Perennial design-mapping doc** (already in TODO.md). Cheap, and best
   done *before* the relational rules grow much further, so we adopt their
   memory-model and interface lessons rather than rediscover them. Can run in
   parallel with (1).
3. **Then** climb the raft ladder (tracker → log_unstable/MemoryStorage →
   raft.go trace replay), growing GoCore semantics and relational rules only as
   each stage demands, each landing with differential coverage.

## Explicitly deferred (care = not doing premature work)

- State data-structure optimization (#5) — until a real raft-scale case is slow.
- Full correspondence proofs — the skeleton already forces rule shape; proofs
  come when the core stops moving.
- Broad interface/concurrency semantics beyond what a ladder stage needs.
- Enriching the Gobra fork further — throwing effort at a frontend the north
  star replaces. Only patch Gobra if it cheaply unblocks a *current* 136-case
  need while the native path is built.

## The one decision for the user

Start the native Go frontend now (recommended), keep enriching Gobra instead,
or continue frontend-independent semantics/proof work and defer the frontend
again. This gates everything downstream.
