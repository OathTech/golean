# ARCHIVE — branch index

Main is the SEMANTICS product only (the repo split, 2026-08-31 —
`docs/2026-08-31_repo-split-plan.md`). The branches below carry
everything else this repo has produced. **They are NOT local branches
in a fresh clone** (the 2026-10-11 migration to this box cloned the
pushed set): what resolves where is the table below; use the
`origin/<name>` spelling (or `git switch <name>`, which creates a local
tracking branch) for a branch, the tag name for a tag.

**What resolves where** (verified 2026-10-12 on the `milner-oath` clone of
`OathTech/golean` with `git branch -r`, `git tag`, `git show-ref`,
`git for-each-ref refs/snapshots`; [AGENT] records lane
`docs/release-records-1012`, release-readiness item 12; origin itself not
re-queried — no network from the sandbox — so «on origin» means «fetched
with the clone», the tags read from the clone's `packed-refs`):

| name below | local branch | `origin/*` remote-tracking ref | tag | resolves to |
|---|---|---|---|---|
| `park/reasoning-2026-08-31` | no | yes | — | `7440bf70` |
| `raft-proof-campaign` | no | yes | — | `17197113` |
| `typed-consumer-sprint` | no | yes | — | `7edc298f` |
| `typed-uintptr-identity` (the HELD L5 source) | no | yes | — | `5f185fb3` |
| `park/typed-profiles-2026-09-16` | no | **NO — not on origin** | `typed-profiles/last-main-2026-09-16` (annotated, in the clone) | `62fc8073` via the tag only |
| `archive/callspec-era` | no | yes | — | `20cda772` |
| `archive/fixed-trajectory-era` | no | yes | — | `c4986b29` |
| `snapshot/typed-sprint-before-uintptr-20260906` | no | no | — | does NOT resolve (same tip as `origin/typed-consumer-sprint`, `7edc298f`) |
| `refs/snapshots/*` (e.g. `pre-repo-split-main`) | — | — | — | EMPTY on this clone (`pre-repo-split-main` = `7440bf70` = `origin/park/reasoning-2026-08-31`) |
| (the offer) | — | — | `logic-offer/2026-10-03` | `20d3946d` |

Also on origin, not indexed below (older lane branches, kept as found):
`campaign-arc4d`, `campaign-ce`, `campaign-wave-a` (2026-08-26),
`channel-logic`, `channel-logic-s4` (2026-08-11; cited by
`docs/2026-08-04_nondeterminism-doctrine.md`), `design-pass` (2026-08-28).

**PENDING [USER] (release-readiness backlog D4):** push
`park/typed-profiles-2026-09-16` to origin, or leave it tag-only (the tag
already names the same commit; nothing is lost either way). Until ruled,
revive from the tag.

For a source-checked survey of the reasoning branches, newer Iris spikes,
uncommitted worktree material and stashes, see
[Reasoning archaeology and revival proposal](2026-09-16_reasoning-archaeology.md)
([AGENT], 2026-09-16). It distinguishes historical claims from current
artifacts and proposes a reasoning repository plus a Raft repository with
independent Verdi and etcd-proof packages.

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
  Reason — [USER] ruling (Mike, 2026-09-07, as relayed by the
  [AGENT] coordinator — cite as relayed): the evidence blob does not
  land, big evidence bundles are not dumped on main (they cannot be
  hosted on GitHub), and the work is to be landed cleanly by a plan,
  decomposed into reviewable chunks, with some of the issues (the
  choice tape among them) fixed where appropriate. The two landing audits that
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
- **`park/typed-profiles-2026-09-16`** (NOT on origin — the tag is the only ref on this clone; D4 above) = tag **`typed-profiles/last-main-2026-09-16`**
  = main `62fc80731f0045c170634690bda1c26d1880f185` (2026-09-16) — the
  typed-admission profile family at its LAST main state before parking:
  `GoLean/GoCore/Boolean*.lean` + `Recovery*.lean` (56 modules, 8,197
  lines), the facade `GoLean/Interface.lean`, their nine `Tests` libraries
  (24 modules), fixtures, gate scripts and audit tools; and the dark spikes `spikes/gate-a1` and
  `spikes/iris-customer`, deleted by the lane's SEPARATE D7 commit
  (PENDING [USER] at the merge ask; one revert restores them). Deleted from main by lane
  `park-lane/typed-profiles-0916`; the note (inventory, what was re-homed,
  what stayed, how to revive) is `docs/2026-09-16_typed-profiles-parked.md`.
  Future home per the [USER] ruling of 2026-09-16 (relayed; recorded in the
  note): the reasoning repository under gitignored `deps/` (name
  provisional — «golean-reasoning»; the survey's `deps/reasoning-revival/
  golean-logic/`), consuming golean PINNED at that SHA. Revive with
  `git checkout typed-profiles/last-main-2026-09-16 -- <paths>`.
- **raft-proofs** (not a ref here) — the reasoning-side raft proof
  repository (its own git repo, remote `OathTech/raft-proofs`; imports
  nothing from GoLean). It lived at the gitignored
  `deps/reasoning-revival/raft-proofs` during the migration; MOVED
  2026-09-27 to `~/projects/raft-proofs` ([USER] Mike, 2026-09-27,
  directed; the move and its `git worktree repair` [AGENT]). Paths of
  the form `golean/deps/reasoning-revival/raft-proofs/…` in either
  repo's older docs and provenance are historical and now resolve under
  `~/projects/raft-proofs/`; its tools still take golean's `deps/`
  reference checkouts (raft, verdi-raft, opam-coq818) by explicit path.
- **`archive/callspec-era`** — the killed CallSpec judgment track
  (2026-08-27 triage).
- **`archive/fixed-trajectory-era`** — the killed enumeration-era
  corpus (2026-08-27 W0 reset).
- Snapshot refs under `refs/snapshots/` — pre-operation safety
  copies (`pre-repo-split-main` = `7440bf70`). Local-only by nature:
  none is on this clone (table above); `7440bf70` survives as
  `origin/park/reasoning-2026-08-31`.

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
  (Landed on `main` by train r50, 2026-09-27, documentation only: release-check no inputs changed; fast
  `scripts/ci` PASS; the adversarial audit waived — [USER] Mike, relayed: (the review waived).)
