# CLAUDE.md — the working charter

`AGENTS.md` is a git-tracked symlink alias of this file so that agents
looking for `AGENTS.md` find the working charter; edit `CLAUDE.md` only —
the architecture rules formerly in `AGENTS.md` are
`docs/architecture-rules.md`. ([USER] 2026-09-07, relayed; the alias
shape is gate-checked by `scripts/check-agents-alias`.)

This file is the charter: what we build, what is trusted, and the
gates. It is deliberately short; details live in the pointed-to
documents. Amend only when a practice proves its worth or its cost.

## What this repo is (top of mind)

**The GoLean semantics: a trustworthy, portable, executable Go
semantics, validated by differential testing.** One product, one
claim.

Since the repo split (2026-08-31, [USER]-directed —
`docs/2026-08-31_repo-split-plan.md`), the Iris proof layer (the
designated theorem set, the judge/audit apparatus, program proofs)
is NOT here: the parked era is on branch `park/reasoning-2026-08-31`,
and the live program logic is the separate repository
`~/projects/golean-logic`, which consumes this one at a pinned
commit. This repo makes
NO verification claims about Go programs.

The boundary, ruled 2026-09-05 ([USER], Mike, verbatim, relayed by
the [AGENT] coordinator — cite as relayed; review F10, `docs/
2026-09-05_master-plan.md` §7.5): «I agree btw, that it makes sense
for the relational semantics to live in this repo. In the case of
cerberus-lean, we didn't do this because cerberus is fixed (we are
just porting it) and the relational semantics is downstream. But
here we are co-designing the semantics to support both execution
and proof. So we should build both in this repo, with a thin enough
customer layer that we can feel confident we are building the right
thing». So: the semantic transition relation, its observations, the
invariants stating its domain, and the executable↔relation coherence
proofs LIVE HERE, co-designed with the executable core (the merge
invariant in `docs/architecture-rules.md`). Iris resources, WP rules,
program proofs, tactics, and consumer ghost state are the customer's,
downstream. A thin customer adapter (an iris-lean `Language` instance
+ toy facts) may be built in-repo as a SPIKE, outside the default
build and the gate's dependency graph, to validate the interface.

Top-level goal ([USER], Mike, verbatim, relayed by the [AGENT]
coordinator — cite as relayed), 2026-09-11: «Our job is to make the Go
seantics as good as we can make it. […] We *can* provide a relational
definition along with it too» (`docs/2026-09-11_review-dispositions.md`);
2026-09-22: «Our ultimate aim here is to support the GoLean logic that
we're building in a different repo. That's our upstream customer.»
The customer's review shaped the current plan
(`docs/2026-09-23_batched-window-charter.md`).

**What this repo provides, and does not** ([USER], Mike, 2026-09-16,
verbatim, relayed; the qualifications are [AGENT], ratified by the
[USER] the same day — «this is a good thing to roll into the
statement»): «(1) we provide a Go semantics defined via the core
GoCore language, (2) we ship a relational, i.e fuel-free semantics
which is provably equivalent to the operational semantics, (3) we DO
NOT ship any higher level reasoning. The aim is for the relational
semantics to be useful for reasoning but this isn't something we
ourselves supply». Qualifications: (1) includes the native lowering
Go → GoCore, differentially validated and carrying NO correctness
theorem — a consumer of a GoCore program inherits that trust
assumption and the wire's provenance record. (2) is proved per step
in both directions (`stepFn_sound`, `step_complete`), for the drivers'
traces, runs and observations, and end to end for the sequential
driver over the labelled step (`GoLean/GoCore/Prefix.lean`: the
counted, choice-threaded prefix closure; the finishing classification
with its five endings; the fuel bridges; choice replay by record; the
refusal-separate classification; statements pinned in
`GoLean/GoCore/BridgeSet.lean`). And, since 2026-10-06 (train r70),
for the goroutine pool over the labelled step
(`GoLean/GoCore/PoolStep.lean`, `PoolSound.lean`; 48 statements frozen
by `scripts/check-pool-spec`): per-step soundness and completeness of
the scheduler against the relation `StepML`, whose label is the
executable's own event (who stepped, its action, its `StepLabel`);
attribution and the frame law; context switches only at registry
boundaries, with the scheduling pick recorded first; the pool deadlock
as its own predicate; the counted pool prefix and its classification
with terminal priority; the fuel bridges; replay by record; and the
single-goroutine reduction to the sequential results
(`PoolProjection.lean`). Not a theorem: the run-level converse «every
relational run is some tape's prefix» is FALSE as a bare statement
(the relation steps past an aborted goroutine, the driver classifies
it first); it holds per step and for runs that pass the driver's gate.
Limits: setup is a premise (its no-globals, no-initializer case is the
pinned equation `runProgramSetup_noInit`), init-time printing is
refused, and the domain premise `NoRefusal` covers the sequential
driver only (a `go` statement leaves it). A refusal has no relation
successor: a partial-correctness boundary ([USER] approved this
wording 2026-09-28, «D2: approved», and its update 2026-10-03, «agree
on 1-4», relayed, and its 2026-10-06 update, «Agree on 1 / 2»,
relayed). (3):
the typed-admission profile family, the `GoLean/Interface.lean`
facade and the adapter spikes were PARKED 2026-09-16 ([USER] ruling;
tag `typed-profiles/last-main-2026-09-16`,
`docs/2026-09-16_typed-profiles-parked.md`), revivable from that tag
by the logic repository (`~/projects/golean-logic`), which consumes
this repo at a pin. A consumer also inherits the Platform instance (gc, linux/amd64
— portability is a separate contract, latitude inventory §11) and the
machine's concurrency granularity (the reduction to Go's access
granularity is an explicit open obligation, not a theorem). This
paragraph replaced the 2026-09-04 consumer-interface pointer with
[USER] approval 2026-09-16 («approved to change the CLAUDE.md file»).

- The semantics is **the weakest machine Go permits, all latitude
  included**. Differential testing is the lower bound (observed ∈
  modeled); spec/docs/corpus argue the upper. Doctrine:
  `docs/2026-08-11_essence-of-go-doctrine.md`; latitude census:
  `docs/2026-08-11_latitude-inventory.md`; spec pins:
  `docs/spec-sources.md`.
- The fixture corpus (`Corpus/`, incl. the imported-goose cases)
  plus the top-level raft subject/harness (`raftsubject/`,
  `raftharness/`) is the test suite for the semantics — every
  fixture is a differential test case first; the raft subject's
  lowering is pinned by `scripts/check-frontend-pins`.
- The Prop-level relation (`GoLean/GoCore/Machine.lean` + the
  soundness modules) is part of the product, not a debt: the split
  plan's extraction slice is WITHDRAWN ([USER] 2026-09-05, above);
  it must keep pace with the interpreter (merge invariant).

## The trusted surface (and nothing else)

1. The interpreter (`GoLean/GoCore/` — `stepFn` and its drivers)
   and the native frontend lowering (`tools/nativefrontend` +
   `GoLean/NativeToIR.lean`), validated by the differential corpus
   against `go run`.
2. The differential apparatus: the coverage runners, the tracked
   baselines (`baselines/`), the oracle pin (go1.26.5 exactly), and
   the re-pin guards. The oracle toolchain is never floated; pin
   moves are deliberate, with a full run and a written reason.

Everything else is untrusted tooling.

## Doctrine

- **The semantic core is total.** No `sorry`, no `native_decide`,
  no axioms anywhere in `GoLean/`; no `partial` in the semantic
  core `GoLean/GoCore/` — structural/well-founded recursion so the
  coherence proofs here and the customer's proofs downstream stay
  reachable. (The wire decoder `NativeToIR.lean`, the CLI, and
  `EnumDedup.lean` use `partial` for JSON/search descent; they are
  outside the core. The in-build Audit sweep left with the proofs
  package; the ci escape-hatch scans are the standing check here.)
- **Fail closed, always.** Unknown wire node, unsupported feature,
  unclassified case, exhausted budget → an explicit refusal that
  NAMES ITS CAUSE at the point of failure, never a silent default,
  never an absorbing fallback. Refusals are load-bearing signals:
  an `unsupported`/`stuck` outcome never counts as a pass, a gate
  that cannot run FAILS rather than skips. A visible red beats a
  hidden wrong answer.
- **No semantic choice hides in evaluator recursion.** Latitude Go
  permits is reified (the choice tape), not baked in; frontend
  concerns stay in the lowering and fail closed
  (`docs/architecture-rules.md` has the architecture rules).
- **Honest measurement.** Differential results are reported with
  their scope (full vs. partial, cached vs. re-certified); bounds
  as bounds; numbers derivation-anchored.

## The gates

- `scripts/ci` before any commit that touches runtime code —
  always via `scripts/capped` (cgroup-capped; never bare lake/lean;
  see `docs/operational-lessons.md`). Runtime changes add the
  differential (`--diff`); baseline re-pins only with a full run
  and a written reason (PASS→non-PASS flips must be on a BUGS.md
  Cases: line). The gate also runs `scripts/check-evidence-size`:
  bulky or duplicated evidence under `docs/evidence/` fails closed
  (caps and the archive-branch convention:
  `docs/architecture-rules.md`, "Evidence on main"), and
  `scripts/check-agents-alias`: `AGENTS.md` must be the alias of this
  file (note at the top).
- The pre-merge adversarial audit: the ask is unconditional; scope
  and waiver are the user's.

## The merge protocol (exact, every time)

1. All work on branches off `main`, in worktrees
   (`.claude/worktrees/<lane>`, one writer per worktree; primary
   checkout parked on `main`).
2. Arc complete → gate green.
3. The audit ask — never skipped; the user may trim or waive.
4. Pause; merge only on explicit at-that-moment sign-off.
5. `git checkout main && git merge --ff-only <branch>` (if refused:
   rebase, re-gate, re-ask).
5a. Before merging, the train records the pre-merge main tip as
    `refs/snapshots/<round>/main`. At the merged tip, build with
    `scripts/build-certified`, then run `python3 tools/certification.py
    release-check --base refs/snapshots/<round>/main`. If the shared
    inventory or claim changed — even if the branch refreshed its own
    record — the train runs `scripts/ci --slow`, installs the reviewed
    candidate (`certification-candidate.json`, under the run's output
    dir) as `baselines/certified/<case>.certified.json`, commits it as
    the round's 5a records commit, and re-runs the gate green (a
    candidate is not a record); a changed certified set is a finding,
    not a re-pin. This covers the semantic sources, frontend,
    observer/checker, apparatus and build/toolchain inputs, rather than
    two wire files ([USER] 2026-09-09 approved the F8 brief (charter:
    docs/2026-09-09_certificate-provenance-charter.md); this wording
    [AGENT], ratified at this landing's merge sign-off; protocol:
    docs/2026-09-09_certificate-provenance-design.md).
6. End parked on `main`, clean, green. Push is a separate sign-off.

## Working practices

- Capture decisions in tracked files, not chat; [AGENT]/[USER]
  provenance on every logged decision; snapshot refs before risky
  git ops; honest reporting (failures with output).
- Autonomous arcs: judgment delegated inside written boundaries; no
  gate weakening, no trust-surface changes, no merge/push;
  branch-complete + audit-ask posed is the end state. **Named
  design gates are HARD STOPS**: a run that cannot stop EXITS
  rather than self-adjudicating the gate.
- Reference checkouts in gitignored `deps/` (`scripts/setup-deps`;
  default set goose/raft/go — goose and go are gate-required —
  the rest opt-in by name) — consult before inventing.

## Pointers

The plan of record for the current phase: the batched-window charter
`docs/2026-09-23_batched-window-charter.md` and its execution table
`docs/2026-09-24_window-plan.md` · The earlier whole roadmap (dated,
indexed by package; §7 = the review's dispositions):
`docs/2026-09-05_master-plan.md` · The independent project
gate audit (2026-09-05, verdict + F1–F13 + Gates A–D):
`docs/2026-09-05_project-gate-audit.md` ·
The split plan (this era's opening decision):
`docs/2026-08-31_repo-split-plan.md` · Reviving the parked
reasoning product: `docs/2026-08-31_reasoning-revival-guide.md` · Branch index for the parked
reasoning product and the era archives: `docs/ARCHIVE.md` ·
Semantics doctrine: `docs/2026-08-11_essence-of-go-doctrine.md` ·
Latitude census: `docs/2026-08-11_latitude-inventory.md` · Spec
truth pins: `docs/spec-sources.md` · Coverage structure:
`docs/coverage-suite-structure.md` + ledgers
(`docs/coverage-ledger.md`, `docs/language-coverage-ledger.md`) ·
Fidelity bugs: `docs/BUGS.md` · Operational lessons (build/OOM/tool
incidents, measured remedies): `docs/operational-lessons.md` ·
Architecture rules: `docs/architecture-rules.md` (`AGENTS.md` is an
alias of this file, not a separate document).
