# CLAUDE.md — the working charter

This file is the charter: what we build, what is trusted, and the
gates. It is deliberately short; details live in the pointed-to
documents. Amend only when a practice proves its worth or its cost.

## What this repo is (top of mind)

**The GoLean semantics: a trustworthy, portable, executable Go
semantics, validated by differential testing.** One product, one
claim.

Since the repo split (2026-08-31, [USER]-directed —
`docs/2026-08-31_repo-split-plan.md`), the reasoning product (the
Iris proof layer, relational-semantics instances, the designated
theorem set, the judge/audit apparatus) is NOT here: it is parked
whole on branch `park/reasoning-2026-08-31`, pending migration to
a separate repo that will consume this one as a pinned dependency.
This repo makes NO verification claims. Do not rebuild proof
machinery here; reasoning work happens on the parked line and,
later, in its own repo.

- The semantics is **the weakest machine Go permits, all latitude
  included**. Differential testing is the lower bound (observed ∈
  modeled); spec/docs/corpus argue the upper. Doctrine:
  `docs/2026-08-11_essence-of-go-doctrine.md`; latitude census:
  `docs/2026-08-11_latitude-inventory.md`; spec pins:
  `docs/spec-sources.md`.
- The fixture corpus (`Corpus/`, incl. the imported-goose cases and
  the raft subject/harness) is the test suite for the semantics —
  every fixture is a differential test case first.
- Known-owed (recorded in the split plan): the Prop-level relation
  (`GoLean/GoCore/Machine.lean` + soundness modules) is destined
  for the reasoning side but is interleaved with the executable
  core; it stays here, inert, until its extraction slice.

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

- **The semantic core is total.** No `partial`, no `sorry`, no
  `native_decide`, no axioms in `GoLean/`; structural/well-founded
  recursion so the proof direction stays reachable for the
  downstream reasoning repo. (The in-build Audit sweep left with
  the proofs package; the ci escape-hatch scans are the standing
  check here.)
- **Fail closed, always.** Unknown wire node, unsupported feature,
  unclassified case, exhausted budget → an explicit refusal that
  NAMES ITS CAUSE at the point of failure, never a silent default,
  never an absorbing fallback. Refusals are load-bearing signals:
  an `unsupported`/`stuck` outcome never counts as a pass, a gate
  that cannot run FAILS rather than skips. A visible red beats a
  hidden wrong answer.
- **No semantic choice hides in evaluator recursion.** Latitude Go
  permits is reified (the choice tape), not baked in; frontend
  concerns stay in the lowering and fail closed (`AGENTS.md` has
  the architecture rules).
- **Honest measurement.** Differential results are reported with
  their scope (full vs. partial, cached vs. re-certified); bounds
  as bounds; numbers derivation-anchored.

## The gates

- `scripts/ci` before any commit that touches runtime code —
  always via `scripts/capped` (cgroup-capped; never bare lake/lean;
  see `docs/operational-lessons.md`). Runtime changes add the
  differential (`--diff`); baseline re-pins only with a full run
  and a written reason (PASS→non-PASS flips must be on a BUGS.md
  Cases: line).
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
  goose is gate-required, the rest opt-in) — consult before
  inventing.

## Pointers

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
Architecture rules: `AGENTS.md`.
