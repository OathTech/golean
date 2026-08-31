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
| 1c surface purity (Iris-free surface) | park (scans proofs surface modules) |
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
| golden-lowering staleness (check-golden) | park (the pinned Lean terms are proofs-side; on main the differential is the frontend/decoder guard) |
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
proof/reasoning product": 280 kept, 159 deleted (all on the park
branch; 439 total), with these [AGENT] rulings on the mixed cases:

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
- Provenance comments in surviving code/fixtures that cite parked
  docs (e.g. fixture headers citing proof-arc charters,
  `Ops.lean` citing the sem-adequacy arc) are LEFT AS-IS: they cite
  history, and the park branch is that history's archive.

## What main is now

Two trusted things and their evidence:

1. The executable GoCore interpreter + native frontend, validated
   by the differential corpus against `go run` (the corpus is the
   fixture set — every Go fixture retained as a semantics test).
2. The differential apparatus itself (coverage runners, baselines,
   re-pin guards, lane gates).

The verification product — statements, proofs, judge, veneer gates
— is no longer main's claim. Main makes NO verification claims.

## Deferred to the migration stage (all [USER] decisions)

- New repo name/location; dependency mechanism (recommended at the
  planning discussion: pinned git require on golean, local remote
  until push is authorized); history strategy (recommended: full
  clone so every cited SHA resolves in both repos).
- The GoCore relational-module extraction slice (above).
- `architecture.md`/`roadmap.md` semantics rewrite.
- Whether the `raft-proof-campaign` branch lands or migrates raw.
