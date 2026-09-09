# Next increment: bind cached certification to current semantics

[AGENT] 2026-09-09. PROPOSED in response to the [USER]'s firsthand request
for the next slice after landing package-correct method identity. Surveyed
main `56b4d5c57e3239f4a7308d9c847b8db3c9bcbffe`; this proposal is on
`plan/certificate-provenance`, a documentation-only worktree from that tip.
No implementation, prototype cleanup, merge or push is authorized here.

## Recommendation and acceptance sentence

Deliver **F8 / master-plan-v2 P1: certificate provenance**, as one bounded
apparatus feature. Suggested implementation branch: `fix/certificate-provenance`,
from main after the current landing train finishes.

**A cached observation set may count as certified for the current run only
when its complete claim and semantic/build dependencies match a successful
certification; every missing, stale or malformed dependency is a named gate
failure.** Fresh certification still compares against the tracked observation
set; a changed set is a finding, never an automatic re-pin.

This closes an existing HIGH audit finding before B7 moves the interpreter,
state, drivers and checker dependencies extensively. It needs no new Go
feature, supported-profile decision or latitude ruling. Its payoff is stronger
evidence for every subsequent semantics change, rather than additional PASS
rows. The semantic relation and all theorem statements remain unchanged.

## What is true at the surveyed tip

[AGENT] Read-only source and worktree checks, not a fresh differential run:

- FR-31 is landed: main includes the three implementation stages, fixes
  `20e412ba`, evidence `b82cb492`, and the landing agent's record correction
  `56b4d5c5`. Some master-plan rows still say awaiting review; the ancestry
  supersedes those statuses. Recounting `baselines/native-full.tsv` gives
  **3665 = 3417 PASS / 248 FAIL**; the negative baseline has **394 PASS**.
- [Independent audit F8](2026-09-05_project-gate-audit.md#f8--high-cached-observation-sets-are-not-invalidated-by-the-full-semantic-dependency-set)
  remains applicable. `scripts/diff-coverage:883-900` (confluent) and
  `:1783-1806` (membership) read the saved wire hash and literal parameter
  string, then copy the saved observations. They do not validate the source
  or build of the current interpreter, checker, or observation projection.
  The current-driver checks are bounded smoke tests, not a proof that all
  previously certified observations still describe the current semantics.
- Exactly one active corpus row has `tier=slow`:
  `imported-goose/channel/google-search`. Its saved set has six members.
  Both implemented cache paths must be covered even though the current
  corpus exercises only membership caching.
- `CLAUDE.md` merge protocol 5a names only `tools/nativefrontend/wire.go`
  and `GoLean/NativeToIR.lean`; `tools/reconcile-records` C9 likewise checks
  wire-related commits. A core-only change can therefore miss this trigger.
  This is an invalidation gap, not a claim that today's six members are wrong.
- The landing agent has a separate `r29-slow-recert` worktree at the merged
  tip, with a `scripts/ci --slow` log in progress when inspected. That train
  remains its owner's work; this survey does not claim its final verdict.
- B7 remains an uncommitted prototype at `typed-context-store` HEAD
  `ca1e01d5`: 146 tracked modified paths and 39 untracked status entries.
  The main pause record still withdraws its V1 completeness claim and
  records a broader V2 diagnostic failure. It is useful implementation and
  review material, not a clean branch ready to land. I1's runtime prototype
  and the byte-runtime integration also retain uncommitted changes. None
  was modified by this survey.

## Proposed work boundary

[AGENT] Freeze the concrete manifest and refresh protocol in the charter/design
before implementation. The deliverable has three connected parts:

1. **One versioned certification identity.** Cover the complete enumeration
   request (wire, entry, arguments, lane/status/observation policy and bounds),
   the interpreter/decoder/observer/checker dependency set, relevant apparatus,
   Lean toolchain and build configuration. Bind it to the executable actually
   used through checked build provenance. Hashing current source beside an
   unrelated old executable is insufficient. Use content identities and
   relative paths so a docs-only commit or another checkout path does not
   invalidate an otherwise identical claim. New or omitted dependencies must
   fail closed; do not maintain separate drifting dependency lists for reuse,
   recertification and merge policy.
2. **Enforcement and deliberate refresh.** The membership and confluent cache
   paths, CI, and the record checker consume the same validator. Missing or
   duplicate fields, an unknown schema, stale inputs, or a mismatched build
   refuse before cache reuse. A full `--slow` run can produce a reviewable
   refresh candidate only after successful enumeration and comparison with
   the existing set. Do not rewrite tracked evidence during ordinary CI or
   bless a changed set by updating its hash. Retain the existing sampled
   coupling checks and truthful `CERTIFIED-CACHED` label.
3. **A tested release rule.** Use the same dependency identity to widen 5a
   and C9 beyond the current two-file heuristic. Record the refresh reason,
   actual exits, source/build binding and timing. This proposed change to
   the standing gate belongs in the approved charter; it is not assumed
   already adopted by this recommendation.

The scope is certification apparatus and necessary build provenance plumbing.
No semantic changes, theorem-statement changes, observation-set changes,
corpus additions, baseline reclassification or oracle-toolchain move. B7,
G-P, F9, the declaration fixture re-pin guard R10, and typed-gate residuals
T8.1 remain separate deliverables.

## How we would establish completion

[AGENT] Acceptance controls must exercise the actual cache consumers:

- The unchanged certified input is accepted in both cache paths; a docs-only
  commit and equivalent checkout retain reuse.
- Independently mutate an interpreter dependency, observation/comparison
  dependency, checker/enumerator dependency, toolchain/build identity,
  entry/argument/claim input, and wire/parameters. Every stale case fails by
  cause before a saved set can count as certified. At least one compiled
  core mutation leaves the wire unchanged, demonstrating the exact F8 gap.
- An old executable beside changed source, a dependency omitted or newly
  introduced, incomplete/duplicate metadata, and an unknown schema fail.
  Controls cannot pass merely because the build or oracle failed to run.
- A failed/interrupted enumeration cannot mint a reusable record. A successful
  unchanged-set recertification restores reuse; an observation-set change
  remains a visible failure and leaves the tracked set untouched.
- Full capped CI and fresh `--slow` certification pass at a clean source
  commit, with the existing 3665 executable and 394 negative rows unchanged.
  The six-member set, its parameters and wire pin remain unchanged. Measure
  both ordinary cache-validation overhead and the full gate's wall cost.
- Worktree-local scratch uses symlink overlays, is deleted on success, and
  is retained with a reason on failure. Evidence stays within the size gate.
  Finish branch-complete with the user's independent audit ask; no merge/push.

## Why this slice precedes the alternatives

[AGENT] B7 is the next major architectural hinge: it unlocks C1's memory/access
interface, then native promotion G-P and much of the consumer-facing work.
Its main design is valuable, but the restart/salvage decision N1 and the
source-bound correspondence burden make it a substantially larger arc. F8
first gives that migration the dependency-sensitive release gate it needs.

BUG-104 is a real five-row lower-bound violation, but the plan places its
evaluation-order repair inside F6, alongside the successful-early-value issue
BUG-101. Its target must preserve the permitted envelope, not merely match
one gc ordering. F9's frontend rejection leg is another clean candidate, but
the current audit ranks F8 HIGH and F9 MEDIUM. The remaining typed-gate
residuals are useful follow-ups; they do not close the stale-set gap.

The recommendation is therefore **F8 next, followed by a freshly chartered
B7 restart using the preserved prototype as reference and its independent
customer theorems as acceptance tests**. This proposes that order; it does
not launch either implementation.
