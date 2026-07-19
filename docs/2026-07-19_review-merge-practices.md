# Review & merge practices — adopted from ACL2Lean (2026-07-19)

Reviewed the sibling `ACL2Lean` repo (`../../ACL2Lean`) for its branch/commit
and review discipline, per the backlog request. Its central, hard-won ingredient
is **adversarial review before merge**. This note records what we adopt and why;
the concise rules live in `CLAUDE.md` (§"Branch, merge, and adversarial audit").

## Source

`ACL2Lean/CLAUDE.md` §"Small, checkable increments", the merge bullet, and
§"Audit practices" (lines ~224–273). Their stated motivation: on a proof-heavy
project *self-certification has been unreliable*, so the audit is run **before**
claiming a milestone, not after building on it. Worked `Workflow` examples of the
pattern live in their sibling `libsignal-theory` project.

## Adopted: merge discipline

- **Sign-off at the moment of merge, never inferred.** Feature work on a branch,
  never directly on `main`. When a branch is ready to integrate: *pause, report,
  ask* — merge only if approved right then, for that specific merge. Approval is
  never carried over from an earlier "merge it", from the branch being green, or
  from a broad "go ahead". Identical rule for `git push`.
- **Prefer linear / fast-forward history**; `--no-ff` allowed but not the
  default. (Supersedes the earlier off-hand `--no-ff` suggestion for this repo.)
- **Verify green + `#print axioms` (or the differential failing-set) before any
  "done" claim.** Commit/claim only what is verified.

Fit with golean: we already gate every runtime commit on the differential
failing-set (`CLAUDE.md` §"The validation gate"). This adds the *merge* gate on
top — a branch clearing per-commit validation is still not authorized to land
without point-of-merge sign-off.

## Adopted: the adversarial audit (before milestone/merge)

Run **before** claiming a milestone or merging. **Sign off on the audit *plan*
before launching any subagent** — present dimensions, agent count, model choice,
and the cost tradeoff (N parallel reviewers + verification vs. a couple of Opus
agents vs. a single cheaper agent); launch only after approval. Audits are
token-expensive, so the scale is the user's call, not an inferred default.
Encode the run as a `Workflow` script (matches our adversarial-verify pattern).

The five steps:

1. **Ground-truth first.** Establish the factual state before any opinion: real
   `lake build`, `#print axioms` of the target theorems, the differential
   failing-set. Never let a reviewer reason from prose.
2. **Parallel, decorrelated adversarial reviewers — one per dimension.** Give
   each a skeptical persona ("the work is *probably subtly wrong* — find where,"
   not "check it looks fine"), point it at **primary sources** (the real tree,
   the proof/interpreter files, upstream references), and **do not feed it our
   conclusions, confidence, or framing.** For high stakes, pair an *inside*
   reviewer (faithful to our own sources/process?) with an *outside* reviewer (is
   this the right thing at all, judged independently?).
3. **Demand grounding.** Every finding anchored to `file:line`, tagged
   verbatim-vs-reconstructed, with an explicit list of what it could *not*
   verify. Reviewers actually build and check axioms — not trust prose.
4. **Independently verify each finding.** A separate skeptic re-checks each
   falsifiable finding against the source, defaulting to *refute* when the
   evidence is thin or reconstructed.
5. **Synthesize honestly.** Don't average reviewers — drop refuted findings,
   adjudicate disagreement, and **spot-check the highest-stakes survivors
   yourself** before acting. Credit what is genuinely strong.

## How this changes our cadence

The prior master-plan review (`docs/2026-07-18_review-findings.md`) was a
one-off, manually run 3-reviewer pass. This formalizes it as the **standing gate
before every milestone/merge**, encoded as a repeatable `Workflow`, with the
plan-sign-off step in front. Concretely, for the current `native-frontend`
branch (56 commits ahead of `main`): the branch does **not** merge until an
adversarial audit runs against it and its survivors are addressed — which is the
next action, pending sign-off on the audit plan.
