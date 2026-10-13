# Relational surface refactor

## Authority and sources

[USER] 2026-10-13: build a generically useful relational semantics; clients
reason and compose on their side, without coupling to the evaluator or its
drivers. Work on a branch from main. The implementation sequence is a GoLean
first cut, a small downstream logic demo, then iteration.

The request is `golean-logic`'s
`docs/2026-10-13_note-to-golean-relational-layer.md`, final note revision
`434049a`, merged to develop as `c31916c`. Its sections P1–P13 and §3/§4
are the implementation brief. Companion asks B/C remain proposals and
questions, not approved representation changes. The read-only quarry is
`golean-logic` main `f0afcbf7e7a0ad7c19087cc3f73429c57ca94c51`, under
`packages/golean-iris/GoLeanIris/`. Source inspection is not a downstream
build or evidence of a completed migration.

[USER] 2026-10-13: retire the equation-specific gate, including its charter
entry, with the requested removal of the executable equation API. The
build, axiom audit, kernel replay and differential checks still apply.

## Implementation direction

[AGENT] 2026-10-13: retain the useful setup, allocation, local-identifier,
return-identity and pool correspondence results. Remove `Equations`, its
rewrite attribute, the equation client and its dedicated checker; preserve
the three setup helper proofs at their actual point of use. Retire their
obsolete pinned rows rather than keep compatibility wrappers for the old
logic pin. Other consumers' seeded-entry proofs remain intact.

[AGENT] 2026-10-13: separate relational definitions and construct laws from
executable correspondence. Start with a genuinely labelled closure of
`Step`, exact finite-run realization, recorded-choice determinism and
semantic state/construct views. Add explicit operation support contracts,
entry/readback, outcomes and observations with proved scopes. No race-trace
footprint assumption; no new blanket well-formedness or refusal-freedom
assumption. A proved limited contract must say which cases it covers.

## Acceptance and handoff

The first cut is an implemented, built surface with proved exports and
documented limits. It is not the full P1–P13 generalization, a downstream
adequacy proof or a completed migration. Track missing laws and concrete
obligations here during implementation. Existing semantic meaning and
failure distinctions must be preserved. Validation uses the existing build,
axiom audit, kernel replay and full differential gate; the pre-merge audit
ask and merge/push approvals remain separate.

## First-cut disposition of the request

The export names and their domains are in `relational-interface.md`.
These are implementation statuses, not approval to weaken downstream roots.

| Request | Implemented | Remaining |
| --- | --- | --- |
| P1, refusal-sensitive safety | Pick-free reachable progress excludes executable errors other than fuel exhaustion; selected local faults preserve their causes and exclude successful successors. | Choiceful all-behaviour safety and an exhaustive independent refusal relation. |
| P2, execution correspondence | Exact finite labelled runs, arbitrary residual tape, terminal consultations; local normal runs and successful sequential programs in both directions. | Unified all-outcome program bridge, including setup/init failures and fatal errors. No new pool/CLI guarantee. |
| P3, determinism and purity | Determinism by per-step pick records; pick-free uniqueness; store/base-label purity separated from client-observation silence. | Broader construct coverage. |
| P4, effects/locality | Whole-root write support, old-cell preservation and allocation above the old bound, independent of race labels. | Whole-step support, context extension and address-renaming contracts. |
| P5, sequentialization | Distinct-root writes commute under explicit successful lookup and normalization premises. | This is an operation law, not an `unseq` sequentialization theorem; graph/schedule safety and observation equivalence remain open. |
| P6, terminal boundaries | Normal completion, sequential deadlock, panic payload/rendering, rendering refusal, exact finishing costs and fuel exhaustion. | General fatal and ordinary refusal classification. |
| P7, entry/readback | Local activation over any supplied store, ordered entry failures, slot layout, declared entry, fallible final readback. | Abstract general caller-target exit and dispatch contracts. |
| P8, observations | Seven successful call/defer entry sites, resolved identity, supplied arguments and pre-store; targetless/resultless normal returns with `[]`. | Complete entry census, target writeback and panic-printing returns. The downstream audited observer must remain in use at its old pin. |
| P9, construct rules | Literal, conditional, sequence and declaration-block contracts; entry and selected fault laws. Symbolic conditional client uses the laws without evaluator unfolding. | Wider control, data, panic/recover and `unseq` laws; eliminate exposed entry-site control details through demo feedback. |
| P10, invariants | Existing machine well-formedness and heap growth lifted to labelled runs with their initial premise. | Additional invariants only as concrete client obligations justify them; no typing/refusal-freedom inference. |
| P11, initialization | Successful guarded initialization and exact init-print refusal at zero fuel. | Unified failure/phase correspondence. |
| P12, concurrency | Existing pool relations, correspondence and singleton transfer facts retained. | General concurrent reasoning interface remains later work. |
| P13, values/memory | Root reads/writes with normalized values, successful path-write root support, allocation and slot facts. | Path non-overlap, aggregate/slice/map contracts, aliasing and recursive layouts. |

No downstream program proof or migration was performed. The next use is a
small demo at the eventual branch commit, followed by concrete missing-law
reports. The generalization gaps above remain GoLean work; the first cut
does not turn them into assumptions of the logic's existing theorems.

## Validation and recovery

2026-10-13: the crash recovery preserved the dirty worktree, including
untracked source, at
`refs/snapshots/crash-recovery-20261013T215421Z/5-relational-surface-1013`.
The other GoLean worktrees were clean at that check. The earlier CI log
reported failed outcome proofs and a citation scan over unstaged deleted
files. The recovered source already contained the proof repairs; staging
the intended removals repaired the scan without changing the checker.

The repaired worktree passed:

- `capped lake build GoLean.Relational Tests.RelationalContracts Tests.GoCoreAudit`:
  the headline `#print axioms` checks report only the classical trio.
- `capped scripts/ci --diff`: PASS, 589 seconds, every target warning-free,
  core totality/axiom audit clean, 396 eval tests, boundary and Go tests,
  exhaustive scheduler checks, and every speedbump green. The fresh
  differential run has 3,989 rows (3,749 PASS, 240 known FAIL), all matching
  the baseline with classified causes; all 405 negative rows match too.
  Neither baseline changed. The run metadata identifies a dirty worktree,
  not a separately rerun clean commit; only documentation was finalized
  afterward.
- `LEAN_NUM_THREADS=4 capped lake env leanchecker --verbose GoLean`:
  exit 0; the 79 replayed modules exactly match `GoLean.lean` plus the
  source modules under `GoLean/`, with no missing or stale module.

One recovery invocation, `capped lake env leanchecker --help`, failed with
exit 137 under the 32 G cap and supplied no validation. This toolchain
ignores that unknown flag and starts default replay. The explicit-prefix,
four-worker command above is the successful replacement; no cap increase
or global setting change was made.

Reproduce from the branch with the commands above; raw logs and generated
corpus output are ephemeral. The branch is offered for the required
pre-merge adversarial audit. No audit verdict, merge or push is claimed.
