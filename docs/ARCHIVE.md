# ARCHIVE — branch index

Main is the SEMANTICS product only (the repo split, 2026-08-31 —
`docs/2026-08-31_repo-split-plan.md`). The branches below carry
everything else this repo has produced; they are refs in THIS repo
and resolve locally.

- **`park/reasoning-2026-08-31`** — the entire reasoning product at
  its last everything-together state (main `7440bf70`, the Iris
  corpus era's phase-A tip, all gates green): the `proofs/` package
  (Iris layer, relational instances, Audit + 51 designated
  theorems, Challenge/Solution), `compat/` (verdi, gobra), the
  comparator-judge and A-TRIP gate apparatus, and the proof-era
  docs including that era's own ARCHIVE.md (which indexes the
  history below in full). Pending migration to a separate repo —
  the how-to-resume guide is `docs/2026-08-31_reasoning-revival-guide.md`.
- **`raft-proof-campaign`** — the unmerged campaign decision log
  (reasoning-side; lands or migrates at the migration stage).
- **`typed-consumer-sprint`** @ `7edc298f` — the typed-consumer
  sprint's FULL history and evidence payload (96 commits over main
  `47195683`, 2026-09-05..06: the typed Boolean/recovery contracts, the
  Iris customer facade, the observer/crash-channel apparatus, the
  string-member lane, and 2,159 files / ~114 MB under `docs/evidence/`,
  incl. 36 `.tar.gz` and 345 exact copies of tracked files). Retained
  UNMODIFIED as the archive; nothing from it is merged as-is. The work
  lands in reviewed chunks per
  `docs/2026-09-07_typed-sprint-landing-plan.md`, each squashed from
  this branch by path selection and crediting its commits by SHA.
  Reason — [USER] ruling (Mike, 2026-09-07, verbatim as relayed by the
  [AGENT] coordinator — cite as relayed): «The evidence blob should not
  land, and generally we should not dump big evidence bundles on main
  (they can't be easily hosted on GH for one). Can you make a plan to
  land this work cleanly? We'll want to decompose and land in sane
  chunks that can be reviewed. And where appropriate fix some of the
  issues, eg. the choice tape stuff». The two landing audits that
  found the payload and the semantic blockers are landed by the plan's
  L6 chunk as `docs/2026-09-07_landing-audit-{A,B}.md`. Snapshot ref
  `snapshot/typed-sprint-before-uintptr-20260906` names the same tip.
  **MANIFEST of the payload (L6, 2026-09-07):**
  `docs/evidence/2026-09-05_typed-consumer-sprint/` — `MANIFEST.tsv` (one
  row per source dir) + `manifest/<dir>.tsv` (one row per file: path,
  sha256, bytes, origin commit, class) + `source-copies.tsv`; 2,159 files
  / 114,156,315 B / 78 dirs, none on main. The sprint's outcome and
  corrected ledger: `docs/2026-09-05_typed-consumer-sprint-handoff.md`;
  roadmap disposition: `docs/2026-09-05_master-plan.md` §7.8. Landed in
  rounds 20–24 (L1 `f70ea4bf`, L2 `74245e1d`+`90bc3e06`, L4
  `60bbf466`+`dd636996`, L3 `a6a068ce`+`25c665b7`+`29f77b43`, L6); L5
  `uintptr` HELD.
  The staged, uncommitted `uintptr` merge in the sprint worktree is NOT
  part of this archive (its source is branch `typed-uintptr-identity`
  @ `5f185fb3`; plan §2.5, HELD). [AGENT] `landing-plan-0907`,
  2026-09-07.
- **`archive/callspec-era`** — the killed CallSpec judgment track
  (2026-08-27 triage).
- **`archive/fixed-trajectory-era`** — the killed enumeration-era
  corpus (2026-08-27 W0 reset).
- Snapshot refs under `refs/snapshots/` — pre-operation safety
  copies (`pre-repo-split-main` = `7440bf70`).

Older pipeline-history notes for the SEMANTICS product live in
`docs/archive/` (a directory, unrelated to these branches).

## Evidence archive branches

Bulky evidence stays off main (`docs/architecture-rules.md`, "Evidence on main",
[USER] ruling 2026-09-07 relayed): each `archive/evidence-<date>_<slug>`
branch is listed here with the main-side directory that carries its
README and `MANIFEST.tsv`. No `archive/evidence-*` branch yet (2026-09-07);
the first payload kept off main under this rule is the typed-consumer
sprint's, whose archive is the sprint branch itself (above) and whose
manifest is `docs/evidence/2026-09-05_typed-consumer-sprint/`.
