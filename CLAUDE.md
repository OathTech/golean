# CLAUDE.md

Operating contract for work in this repo. This is the concise, always-loaded
version; `AGENTS.md` holds the architecture rules and
`docs/gocore-semantics-upgrade-goal.md` the deep operating guide. Read those
before nontrivial semantics work. Amend this file when a practice proves its
worth or its cost — keep it lean; it loads every session.

Goal: build a fast, careful Go-to-Lean verifier. North star target:
`etcd-io/raft` (`docs/roadmap.md`). Move aggressively; the practices below
exist because they let us do that without accumulating debt, not as ceremony.

## The validation gate (always, before any commit that touches runtime code)

1. `lake build` passes.
2. Run the focused differential slice for the touched area
   (`scripts/coverage run <ids...>` over the cached-export set, or
   `scripts/diff-one <id>`), plus `lake exe gobra-eval-tests`.
3. Diff the failing case-id set against the last recorded baseline. **Same set
   = no regression.** Any new red is investigated before committing.

A green build is not evidence of correctness. The cheap, decisive signal is the
failing-set diff — it is what kept 13 consecutive cleanup slices at zero
regressions. `scripts/gobra-smoke` is a frontend/Lean smoke check, NOT a
Go-vs-Lean conformance oracle; never claim equivalence from it.

## Capture decisions in files, not chat

Every relevant design decision, tradeoff, or open question must be written into
a tracked file (the goal/plan doc for the work, `TODO.md`, or a dated design
note) — not left in conversation. Chat is ephemeral; the repo is the record. If
a decision changes direction (e.g. reshaping GoCore, choosing a wire format,
deferring a feature), note what was decided, why, and what it affects. This is
what lets any session — human or agent — resume without re-deriving context.

Design principle for GoCore specifically: **GoCore is reshapeable, not
sacrosanct.** Judge its shape by two questions — does it support *reasoning*
(a clean relational/WP story) and does it help get *emission* right (frontends
lower to it cleanly)? If GoCore's shape fights either, change GoCore rather than
contort around it, and record the decision.

## Guardrails first: differential tests before tool buildout

Before building a feature of the tool (a frontend, a lowering path, a semantic
construct), add the differential corpus cases that pin its target behavior
first — isolated per feature, with edge cases. The Go oracle (`go run`) is free
and authoritative, so writing the case first costs almost nothing and fixes the
target before the implementation can drift. A tool feature is not "started"
until its guardrail cases exist and classify correctly (a case the tool can't
yet handle should be visibly frontend/feature-blocked, never a false pass).
This is why the corpus is frontend-independent: canonical Go is the input to
both `go run` and the tool. Aim for suites strong enough that *green implies the
target is covered* — see the three-layer sufficiency strategy in
`docs/native-frontend-goal.md` (isolated cases, edge enumeration, integration +
input fuzzing).

## Fail closed, always

Unknown wire nodes, unsupported features, malformed state → an explicit
`.unsupported` / error at the boundary. Never a silent approximation, never an
inert placeholder in dead code. Never count `unsupported`, `stuck`,
frontend-export failure, or a Lean internal error as a passing/conformant case.
A visible red case beats a hidden wrong answer.

## GoCore stays pure

GoCore contains only Go runtime semantics. Gobra proof artifacts, spec-only
constructs (`old`), name mangling, and export-layout heuristics are quarantined
in `GobraToIR`/`GobraJson` and fail closed there — they never become GoCore
nodes. Semantic identity is `TypeId`/`FuncId`, never raw frontend strings.
Every mangling strip happens at exactly one boundary constructor and
collision-checks. This isolation is what lets the frontend be replaced without
touching the semantic core — protect it.

## Small slices, honest regressions

One semantic concern per commit. Validate each. When a cleanup intentionally
turns a case red (removing junk it depended on), record it: case id, old→new
stage, the bad assumption removed, the clean fix. Do not weaken the oracle,
skip a case, or edit canonical Go to make something pass.

## Proof-facing code is total; interpreter debt is tagged

New relational/proof-facing definitions (`Rel.lean`, `Correspondence.lean`) are
total — no `partial`, no `sorry`, no `native_decide`. The executable
interpreter is currently `partial` (a known, tracked debt against the
correspondence proofs); do not add new `partial` semantic functions without a
concrete reason, and prefer structural/well-founded recursion in new code so
the proof direction stays reachable.

## Slices are for iteration, not the record

For the tight edit/test loop use focused ids or a curated smoke subset. Full
runs and handoff-quality claims require the full-run metadata, not a filtered
`latest.tsv`. For multi-session efforts, append to the persistent handoff
(`docs/gocore-semantics-upgrade-handoff.md`) in its stated format — but do not
impose that ceremony on a one-line fix.

## Housekeeping

- `.claude/` is gitignored. Date working notes `YYYY-MM-DD_name.md`; top-level
  docs (README, roadmap, this file) are exempt.
- Sandbox/scratch conventions: `docs/agent-sandbox.md`. For ad hoc Go probes
  set `GOCACHE=/private/tmp/go-build` so the user cache is untouched.
- Do not `rm -rf` scratch dirs without approval; leave them for OS cleanup.
