# The repo split: semantics main, reasoning parked (2026-08-31)

## The decision and its provenance

[USER] 2026-08-31 (Mike): "tangling up the reasoning thread and the
semantics thread is making things confusing. (1) park all the
reasoning (i.e. the non-semantics work) on a branch, then we'll
migrate it to a separate repo which is a customer of the golean
semantics. We'll then remove the reasoning on the main branch,
leaving just the go semantics and differential testing. All the Go
fixtures will remain as test cases for our semantics." Follow-up
ruling, same day: "I would see the relational semantics (i.e. the
non-executable semantics) as living on the reasoning side."

[USER] scope for this stage: only the pre-repo stages — park the
reasoning on a branch and get main clean. The new-repo creation and
migration (name, dependency mechanism, history strategy) are
DEFERRED to a later stage; nothing in this slice pre-commits them.

Everything below the provenance lines is [AGENT] execution of that
directive; per-item judgment calls are marked where they were made.

## What this stage produced

- **`park/reasoning-2026-08-31`** — a branch at the last
  everything-together main (`7440bf70`, phase-A tip of the Iris
  corpus era). The ENTIRE reasoning product lives there, exactly as
  it last passed its gates: `proofs/` (the Iris layer, relational
  semantics instances, Audit/Challenge/Solution, the 51-theorem
  designated set), `compat/` (verdi, gobra), the comparator-judge
  and A-TRIP apparatus, `check-golden` + `baselines/golden/`, and
  the proof-era docs. Snapshot ref: `refs/snapshots/pre-repo-split-main`.
- **This branch (`repo-split` → main)** — the removal slice: main
  becomes the SEMANTICS product only (executable GoCore, native
  frontend, fixture corpus, differential apparatus).
- The pre-existing era archives (`archive/fixed-trajectory-era`,
  `archive/callspec-era`) and the unmerged campaign-log branch
  (`raft-proof-campaign`) are untouched; they are reasoning history
  and travel with the repo's refs. The rewritten `docs/ARCHIVE.md`
  stub on main indexes all of these branches.

## The seam, as found

The split was cleaner than feared at package level and less clean
at module level:

- `proofs/` was already a separate Lake package (`golean-proofs`)
  — the only consumer of iris-lean; root `lake build` never touched
  it. It leaves whole.
- **Known-owed item (named): the GoCore relational modules.** The
  Prop-level relation and its soundness layer live INSIDE
  `GoLean/GoCore/` (`Machine.lean`, `MachineSound.lean`, `Multi*.lean`
  soundness files, `NPDRF.lean`, `Race.lean`) and are interleaved
  with the executable core at file level — `StepFn.lean` imports
  `Machine`/`StateWf`, and `StateWf` is used EXECUTABLY in the
  seeding path. Per the [USER] ruling these belong on the reasoning
  side; extracting them is a refactor of the trusted interpreter's
  module structure (file splits, import re-plumbing, full `--diff`
  revalidation) and is deliberately NOT done in this slice.
  **Owed: a "GoCore relational-module extraction" slice at (or
  before) the migration stage.** Until then main carries them,
  labeled here; they are total, sorry-free, and inert w.r.t. the
  differential.

## Gate inventory — every removed `scripts/ci` step accounted for

Removed steps went WITH the reasoning product (they run against
files that left); none was silently dropped. Destination "park"
means: preserved on `park/reasoning-2026-08-31`, expected to be
re-homed in the future reasoning repo's gate.

| pre-split step | disposition |
|---|---|
| 1b2 proofs-file audit coverage | park (audits `proofs/**`) |
| 1c surface purity (Iris-free surface) | park (scans proofs surface modules; its final GoLean/-side clause — no Iris imports in the core — is SUBSUMED on main: the root manifest has no packages, so any Iris import is an unknown-module error in the core build) |
| 1c3 statement-TCB closure | park (Challenge's closure) |
| 1c4 comparator landmark scope/staleness notes | park (judge apparatus) |
| 1d import-direction lint | SPLIT: proof-layer clauses park; the engine-isolation clause (GoCore ↛ EnumDedup) is retained as its own step |
| 1e WP veneer text lint (A-TRIP) | park |
| 3 proofs build incl. Audit gate | park |
| 3b0 WP veneer proof-closure check (A-TRIP) | park |
| 3b trusted root elaborates (Challenge/Solution) | park |
| 3c proof-cost trend | park |
| 3d storm lint | park |
| 3v verdi compat gate | park (compat/ left) |
| golden-lowering staleness (check-golden) | SPLIT (corrected at the split audit, findings A1/A2/B1): the 29 program-term pins are proofs-side and park; but TWO sub-checks were semantics-only and are RESTORED on main as `scripts/check-frontend-pins` (ci step 2b) with baselines re-homed to `baselines/pins/` — (1) the hidden-dep-order deviation-observation pin (its differential row is permanently red, so only the pin catches a drift to a third realized init order) and (2) the raft twin-wire pin (the only frontend exercise over the real raftsubject/ packages). The 29 emitter↔decoder `.repr` pins are a RECORDED TRADE: behavior-visible drift in those programs is differential-covered; IR-granularity drift detection for them is deliberately dropped on main (it re-homes with the reasoning repo). |
| 3a2 imported-goose R2-pin staleness | park (pins are proofs-side Program terms) |

Retained steps, scope-narrowed where they scanned `proofs/`:
escape-hatch preflight + meta-layer + native-spelling addendum (now
`GoLean/` only — the charter's totality rule still binds the
semantic core; NOTE the in-build Audit axiom sweep that backstopped
these text scans left with the proofs package, so for main these
scans are now the standing check), oracle pin, bug-index,
feature-coverage, spec-anchors, lane self-tests, imported-goose
verbatim staleness (fixtures stayed), engine-isolation, core build,
frontend unit tests, eval tests, differential + negative runs,
baseline diffs, re-pin guards. `scripts/test-import-goose` lost its
R2-pin/gen-pin fixture sections (subjects left). `scripts/setup-deps`
lost the `proofs/.lake/packages` section and the reasoning-side
reference rows. The CI workflow lost the proofs/compat cache paths.

Scripts removed (all on the park branch): comparator-judge,
comparator-setup, check-golden, check-imported-pins,
gen-imported-pin, proof-costs, proof-lint, wp-veneer-lint,
wp-lint-scope.txt, WpVeneerClosure.lean, render-gallery.

## Docs split

A full KEEP/DELETE classification of `docs/` (439 files) was run
per rule "serves the semantics/differential product vs. serves the
proof/reasoning product". Counts as of the audit fix round, verified
against git: 439 docs at the base; 156 deleted (all on the park
branch), 283 kept — the per-file manifest IS the git diff:
`git diff --diff-filter=D --name-only 7440bf70..HEAD -- docs/`.
(The first commit's message says "159 deleted / 280 kept": off
because ARCHIVE.md was rewritten rather than deleted, and two
goose-parity docs were restored at the audit — see below.)
The [AGENT] rulings on the mixed cases:

- The eight early two-track planning records (2026-07-18 master
  plan / prioritization / review-findings, directional-audit,
  vertical-slice, repo-structure-audit, widening-loop,
  arc-sequence): KEPT — superseded history cited by surviving docs.
- `2026-08-15_raft-master-plan.md`, `raft-push-p0-scoping.md`:
  KEPT — they charter the surviving lowering/subject/harness/
  differential lanes (cited from `tools/raftsubject/`).
- `hygiene-slice-log.md`: KEPT — records hardening of surviving
  gate apparatus.
- `architecture.md`, `roadmap.md`: KEPT with a split banner —
  README-linked; both need a proper semantics-scoped rewrite
  (owed, low priority).
- `docs/gallery-campaign-log/`: deleted EXCEPT `g2.md` — the E5
  stdlib-shim provenance record cited from surviving frontend code
  (`tools/nativefrontend/stdlibshim.go`).
- `ARCHIVE.md`: rewritten as a stub indexing the archive/park
  branches (main must be able to explain the refs it carries).
- Provenance citations of parked docs in surviving files are LEFT
  AS-IS where they cite history. Scale, measured at the audit
  (C-12): ~49 surviving files cite ~37 deleted docs, and most of
  the citing files are themselves docs — the convention covers
  doc→doc citations too. Where a citation is LOAD-BEARING (a live
  gate's authority, a kept charter's governing ruling, a coverage
  row's evidence), the audit fix round appended an explicit
  `(branch park/reasoning-2026-08-31)` pointer instead: BUGS.md
  (2 sites), language-coverage-ledger.md, the ci-runner-death doc,
  the three raft charters citing harness-style-scoping §8, and
  architecture.md's two live-instruction lines.
- Restored at the audit (A6): `2026-08-07_goose-parity-charter.md`
  and `2026-08-07_goose-comparative-scoping.md` — the surviving
  imported-goose verbatim gate's charter belongs beside the gate.
- The seven kept docs that asserted the check-golden
  deviation-observation pin now point at its restored home
  (`scripts/check-frontend-pins`).

## What main is now

Two trusted things and their evidence:

1. The executable GoCore interpreter + native frontend, validated
   by the differential corpus against `go run` (the corpus is the
   fixture set — every Go fixture retained as a semantics test).
2. The differential apparatus itself (coverage runners, baselines,
   re-pin guards, lane gates).

The verification product — statements, proofs, judge, veneer gates
— is no longer main's claim. Main makes NO verification claims.

## Deferred to the migration stage

[USER] decisions:
- New repo name/location; dependency mechanism (recommended at the
  planning discussion: pinned git require on golean, local remote
  until push is authorized); history strategy (recommended: full
  clone so every cited SHA resolves in both repos).
- Whether the `raft-proof-campaign` branch lands or migrates raw.

[AGENT]-owed work (scheduled, not user decisions):
- The GoCore relational-module extraction slice (above; the
  DEFERRAL past this slice is itself an [AGENT] judgment — the
  modules are interleaved with the executable core and moving them
  safely needs its own slice; the DESTINATION is [USER]-ruled).
  Full dependency cluster per the split audit (B9): Machine,
  MachineSound, Multi (imported by EnumSpec, which the executable
  dedup engine needs), MultiSound, MultiWfSound, MultiStreams,
  NPDRF, Race, plus the StateEqb/SyntaxEqb/MachineEqb seam.
- `architecture.md`/`roadmap.md` semantics rewrite.

## Addendum 2026-09-05 — the relational-module extraction is WITHDRAWN

[AGENT] record (lane `review-landing-0905`, records only). The [USER]
quote was received by the [AGENT] coordinator and RELAYED to this
lane; cited as relayed, not firsthand (U0-incident convention).

The independent project gate audit (`docs/2026-09-05_project-gate-audit.md`,
F10) recommended keeping the semantic transition relation, its
observations, the invariants stating its domain, and the
executable/relation coherence proofs in this repository, and the
[USER] ruled, 2026-09-05: «I agree btw, that it makes sense for the
relational semantics to live in this repo. In the case of
cerberus-lean, we didn't do this because cerberus is fixed (we are
just porting it) and the relational semantics is downstream. But here
we are co-designing the semantics to support both execution and
proof. So we should build both in this repo, with a thin enough
customer layer that we can feel confident we are building the right
thing».

Consequences for this document:

- The 2026-08-31 follow-up ruling above («I would see the relational
  semantics … as living on the reasoning side») is SUPERSEDED by the
  2026-09-05 ruling. The "Known-owed item (named): the GoCore
  relational modules" paragraph and the "[AGENT]-owed work" bullet
  "The GoCore relational-module extraction slice" are WITHDRAWN as
  plan items. `Machine`, `MachineSound`, `Multi`, `MultiSound`,
  `MultiWfSound`, `MultiStreams`, `NPDRF`, `Race` and the
  `StateEqb`/`SyntaxEqb`/`MachineEqb` seam stay in `GoLean/GoCore/`
  as part of the semantics product, bound by `AGENTS.md`'s merge
  invariant. The text above is left as written (history).
- What remains TRUE of the split: the Iris layer (resources, WP
  rules, program proofs, tactics, consumer ghost state, the
  designated theorem set, the judge/audit apparatus) is downstream —
  parked on `park/reasoning-2026-08-31`, pending its own repo that
  consumes this one as a pinned dependency; main makes NO
  verification claims about Go programs; the gate-step inventory and
  docs split above stand; the park branch stays the archive
  (`docs/ARCHIVE.md`). The migration-stage [USER] decisions
  ("Deferred to the migration stage") are unchanged in kind but come
  due under the revised pin criteria (master plan §7.4, Gate D).
- New, as a SPIKE (PROPOSED [AGENT], master plan §7.4 item (1)): a
  thin customer adapter — an iris-lean `Language` instance plus toy
  facts — may be built in-repo, outside the default build and the
  gate's dependency graph, to validate the consumer interface. It is
  not the reasoning product and does not move it back.
