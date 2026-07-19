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
   (`scripts/coverage run <ids...>` or `scripts/diff-one <id>`, native
   frontend), plus `lake exe gocore-eval-tests`.
3. Diff the failing case-id set against the last recorded baseline. **Same set
   = no regression.** Any new red is investigated before committing.

A green build is not evidence of correctness. The cheap, decisive signal is the
failing-set diff — it is what kept 13 consecutive cleanup slices at zero
regressions. The differential oracle is real Go (`go run`); the native Go
frontend (`tools/nativefrontend` + `NativeToIR.lean`) is the only frontend.

### Baseline pinning (the "recorded baseline" in step 3)

The recorded baseline is a **tracked** file, `baselines/native-full.tsv` —
`result<TAB>id<TAB>stage` per case, sorted by id, with a dated header (recording
commit, counts, frontend). `artifacts/` is gitignored, so a run's `latest.tsv`
is *not* the record; the tracked baseline is. `detail` (free-text errors) is
omitted on purpose — it churns; `result`+`stage` is the regression signal.

- **Diff a run against it:** `scripts/coverage-baseline-diff [results.tsv]`
  (defaults to `artifacts/coverage/latest.tsv`). Exit 0 = identical set (no
  regression); exit 1 prints exactly the drifted ids (PASS↔FAIL flips, stage
  changes, new/dropped ids). This *is* the step-3 gate, mechanized.
- **A `frontend-export` FAIL is an expected native-frontend coverage gap**, not a
  bug — but a *new* one still counts as drift and must be explained.
- **Re-pin the baseline only on a deliberate, explained coverage change** (a
  frontend/interpreter feature legitimately moves cases): regenerate the file
  from a full run, bump its dated header, and commit it *in the same change* that
  caused the move, with the reason. Never re-pin to launder an unexplained
  regression. A focused slice (`diff-one`/`coverage run <ids>`) is for the tight
  loop; the tracked baseline is re-pinned only from a **full** run.

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

GoCore contains only Go runtime semantics. Frontend-specific concerns (name
resolution, desugaring, any wire quirks) are quarantined in `NativeToIR` and
fail closed there — they never become GoCore nodes. Semantic identity is
`TypeId`/`FuncId`, never raw frontend strings.
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

## Branch, merge, and adversarial audit (before milestones)

Adopted from ACL2Lean (see `docs/2026-07-19_review-merge-practices.md` for the
full pattern):

- **Never merge or push without explicit sign-off at the moment of merge.**
  Feature work stays on a branch, never directly on `main`. When a branch is
  ready, *pause, report, and ask* — merge only if approved right then. Approval
  is never inferred from an earlier "merge it", from the branch being green, or
  from any broad "go ahead". Same for `git push`. Prefer linear/fast-forward
  history; `--no-ff` is allowed but not the default.
- **Audit adversarially *before* claiming a milestone or merging, not after** —
  self-certification is unreliable, so audit before building a mountain on it.
  **Get sign-off on the audit *plan* (dimensions, agent count, model, cost)
  before launching any subagent** — audits are token-expensive; the scale is the
  user's call. The pattern (encode as a `Workflow`): (1) ground-truth first —
  real build + `#print axioms`/differential failing-set, never prose; (2)
  parallel *decorrelated* adversarial reviewers, one per dimension, skeptical
  persona ("probably subtly wrong — find where"), pointed at primary sources,
  not fed our conclusions; (3) every finding grounded to `file:line`, tagged
  verbatim-vs-reconstructed, with what it could not verify; (4) independent
  verification of each finding, defaulting to *refute* if thin; (5) honest
  synthesis — drop refuted, spot-check the top survivors yourself.

## Housekeeping

- `.claude/` is gitignored. Date working notes `YYYY-MM-DD_name.md`; top-level
  docs (README, roadmap, this file) are exempt.
- Sandbox/scratch conventions: `docs/agent-sandbox.md`. For ad hoc Go probes
  set `GOCACHE=/private/tmp/go-build` so the user cache is untouched.
- Do not `rm -rf` scratch dirs without approval; leave them for OS cleanup.
