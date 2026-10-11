# Recovery after the 2026-10-08 box crash, and the migration to a new box — the plan (2026-10-11)

[AGENT] recovery worker, lane `docs/recovery-migration-1011` (worktree
`.claude/worktrees/recovery-migration-1011`, off `main` @ `4e3aeb3d`, the
train r75 close). Authority: [USER] Mike, 2026-10-11, verbatim from the
session prompt: «We are recovering after a crash caused by box contention.
[…] We have also disabled auto-memory which was causing erratic behavior.
[…] Also note the changes to global policy. Our next concrete step is to
migrate onto another box, so please make sure that all branches are either
landed, or identified for pushing to the git remote. Figure out a plan for
recovery then migration to the new box». Every decision below is an [AGENT]
proposal **PENDING [USER]** unless marked otherwise. Nothing was pushed,
merged, deleted or pruned by this lane; the only state change is §2 (local
refs, reversible).

## 0. Verdict at a glance

- **Nothing was lost in the crash.** The box rebooted 2026-10-08 23:45:54
  UTC; the last commit on `main` is 17:29:31 UTC that day and the last
  branch commit 16:44:46 UTC. `git fsck --connectivity-only` is clean, no
  `.git/*.lock` is left behind, the primary checkout is parked on `main`
  and clean, no build lock is held (`artifacts/build-lock.d` absent).
- **`main` is 8 commits ahead of `origin/main`** (`6a90ba8d` → `4e3aeb3d`:
  the BUG-115/119/120 fixes and the r75 records). Both local tags
  (`logic-offer/2026-10-03`, `typed-profiles/last-main-2026-09-16`) point
  into `main` and have never been pushed.
- **The sandbox cannot resolve `github.com`** (`git fetch` fails on DNS), so
  every push, fetch and `ls-remote` in this plan is the [USER]'s, outside
  the sandbox. `origin/*` as seen here was last refreshed 2026-10-04.
- **319 local branches**: 193 merged into `main`, 124 not (§3). Of the 124,
  10 need a push, 3 are on `origin` already, 51 are contained in a pushed or
  archive-designated branch, 27 are «landed by patch» (every commit has an
  equivalent on `main`), 33 are safety copies or parked-era work. 409
  `refs/snapshots/*`, 1 `refs/archive/*`, 8 stash entries: left with this
  box. [USER] 2026-10-11: the repo is free-standing — what matters is
  pushed, a new box clones; no bundle (§7).
- **77 worktrees** under `.claude/worktrees/` (32 G). 14 carry uncommitted
  changes — ALL from the parked typed-profiles sprint (2026-09-06) or the
  parked reasoning campaign (2026-08-26); none is current-era work. Two
  detached-HEAD worktrees pointed at commits reachable from no ref. All of
  this is now captured as refs (§2).
- **Disk**: `.tmp/` 9.4 G (21 × `admission-audit-*` ≈ 7.8 G, retained by
  design — §6), `artifacts/` 12 G (`go-build-cache` 11 G), `deps/` 5.4 G
  (2.4 G `verdi-raft` + 1.6 G `opam-coq818` are reasoning-era, not in the
  gate's default set). Box: 601 G free of 1.8 T.
- **Open HARD STOP unchanged**: the seeded-heap design note
  (`design/seeded-heap-1009` @ `752c54cd`, [USER] gate PENDING) is the one
  piece of unlanded current-era design work; it needs a push, not a ruling
  here.
- **Sibling repos on this box need their own pass before the move** (§8):
  `~/projects/golean-logic` has a `develop` branch 329 commits ahead of its
  `main` and 100+ local-only branches; `~/projects/raft-proofs` has several
  hundred local-only branches although the global box note places it on
  `milner-oath`.

## 1. The crash, as far as the evidence goes

| Fact | Evidence |
|---|---|
| Reboot at 2026-10-08 23:45:54 UTC | `uptime -s` |
| Last `main` commit 17:29:31 UTC the same day (`4e3aeb3d`, r75 close); last branch commit 16:44:46 (`752c54cd`, seeded-heap note) | `git log --format=%ci` |
| Object store intact | `git fsck --connectivity-only --no-dangling` exit 0; 10 packs, 380 MiB; 1,766 loose objects |
| No interrupted git operation | no `*.lock` under `.git`; `ORIG_HEAD` from 2026-10-08 16:28 (the r75 merge) |
| No interrupted gate | no `artifacts/build-lock.d`; newest `.tmp/admission-audit-*` is 2026-10-08 (r75's run); load now 0.4 |
| Other agents on the box | three `claude` processes (one is this session; one 10 h old; one in the `lean-ux-proto` zellij session), one `codex` — their cwds are not readable from the sandbox |

The crash cause given by the [USER] (box contention) matches the standing
lesson `docs/operational-lessons.md` «The box-wide build lock» and «thin
headroom under shared-box load» (r72/r73). No new semantic finding; the
remedy is the migration itself.

## 2. Recovery actions taken ([AGENT], local-only, reversible)

Twenty-three refs under `refs/snapshots/2026-10-11-recovery/` were created
so that no uncommitted or unreachable state can be lost by a worktree
removal or a clone while the push set is being confirmed on `origin`; they
stay with this box (§7). **No working tree was modified**; every dirty
worktree is exactly as dirty as before (verified by `git status --porcelain`
counts). Log: the commit message of this lane and the list below.

| Ref (under `refs/snapshots/2026-10-11-recovery/`) | Points at | What it preserves |
|---|---|---|
| `stash-0` … `stash-7` | `d8d6c19c`, `16ec37c3`, `63593b8b`, `0e1a9caf`, `43fab305`, `7582978c`, `620a0cca`, `6b4787b6` | the 8 stash entries (all 2026-09-06, typed sprint WIP «before reviewed integration»). Only `stash@{0}` is a ref; `stash@{1..7}` live in the reflog, which `git push` does not carry |
| `wt-method-promotion-ref` | `74f5bada` | detached worktree `method-promotion-ref` (G-P S0 born pins, 2026-09-28; its patch is on `main`, the commit was reachable from nothing) |
| `wt-typed-i1-json-review-string` | `8051028b` | detached worktree `typed-i1-json-review-string` (77 commits over main, 2026-09-06, reachable from nothing) |
| `wip-<worktree>` (13) | new commits, each `-p <worktree HEAD>` | the uncommitted state (tracked + untracked, excluding `.tmp/ artifacts/ deps/ .lake/`) of `campaign-wave-a` (13 files), `typed-abort-observation-review` (6), `typed-b7-customer-review` (177), `typed-b7-kernel-review` (239), `typed-b7-original-review` (134), `typed-byte-runtime` (162), `typed-byte-runtime-review` (19), `typed-consumer-sprint` (361 — the staged `uintptr` merge, ARCHIVE.md «NOT part of this archive»), `typed-context-store` (391), `typed-i1-envelope` (111), `typed-i1-json-review-string` (9), `typed-r1-production-review` (45), `typed-shared-customer-review` (26). `channel-logic` skipped: its only untracked entry is `.tmp/` |

Method (per worktree): a temporary index read from HEAD, `git add -A` with
the four exclusions, `write-tree`, `commit-tree -p HEAD`, `update-ref`. To
drop all of it: `git for-each-ref --format='%(refname)'
refs/snapshots/2026-10-11-recovery | xargs -n1 git update-ref -d`.

## 3. Branch disposition — «landed, or identified for pushing»

Method: `git branch --merged main` / `--no-merged main`; for each unmerged
branch, `git rev-list --count main..B` (ahead), `git cherry main B` (commits
with NO patch-equivalent on `main`), containment in each `origin/*` ref and
in the two ARCHIVE.md-designated archive branches, and whether
`origin/B` exists at the same SHA. «Landed by patch» = ahead > 0 but zero
unapplied commits: the train landed the lane by rebase/squash and the branch
keeps only the lane's history.

**Must be pushed to `origin` (the product and its designated archives):**

| Ref | SHA | Why |
|---|---|---|
| `main` | `4e3aeb3d` | 8 commits ahead of `origin/main` (r75: BUG-115, BUG-119, BUG-120, records) |
| tag `logic-offer/2026-10-03` | `20d3946d` | the customer's pin («never pushed», `docs/changelog/61958f2e-WINDOW.md`); the commit itself is already on `origin/main` |
| tag `typed-profiles/last-main-2026-09-16` | `62fc8073` | the parking tag ARCHIVE.md tells a reviver to check out from |
| `typed-consumer-sprint` | `7edc298f` | ARCHIVE.md: «Retained UNMODIFIED as the archive»; carries 47 of the typed-era branches and snapshots |
| `typed-uintptr-identity` | `5f185fb3` | ARCHIVE.md: the HELD L5 `uintptr` source (plan §2.5) |
| `design/seeded-heap-1009` | `752c54cd` | the open HARD STOP design note (gc-verified's a2), design only |
| `docs/reasoning-archaeology-0916` | `f180fbb8` | 2 unlanded commits: the reasoning-archive survey + local Verdi revival record; input to the logic repo's revival |
| `records/raft-deltas-0930` | `61b15acd` | 1 unlanded commit: the raft-proofs subject-delta records |
| `records/stray-panic-investigation-0927` | `b5d57d09` | 1 unlanded commit: packet-A audit F1 follow-up |
| `design/eval-order-model-0915` | `90dc66f0` | 1 unlanded commit (the v1 design note; v2 landed) |
| `plan/certificate-provenance`, `plan/method-identity-increment` | `f1b1a1da`, `b12b4a31` | 1 proposal commit each (both increments since built; the proposals are provenance) |
| `prep/observer-terminal-harness` | `b1407cc5` | 1 commit, «Prep (NOT landed)» |
| `docs/recovery-migration-1011` | this lane | after its landing, or as-is if the [USER] wants the plan on the remote before the move |

**Already on `origin` at the same SHA:** `channel-logic`, `channel-logic-s4`,
`raft-proof-campaign` (plus `park/reasoning-2026-08-31`,
`archive/callspec-era`, `archive/fixed-trajectory-era`, which are merged).

**Everything else** (51 contained, 27 landed-by-patch, 33 parked-era or
safety copies, the 409 snapshot refs, the stash refs) is NOT migrated: it
stays with this box until the box is retired (§7). The 27 landed-by-patch
branches are deletable after the landing is verified (D1). The full table follows, then the D1 ruling that revises
the table's PUSH column.

**D1 RULED** ([USER] Mike 2026-10-11, verbatim: «D1: why not land the
records branches? Otherwise, yes. We should push live working branches and
branches containing meaningful features we might use»). Applied:

- *Landed instead of pushed* — six of the eight records/design branches are
  docs-only and merge onto `main` with zero conflicts (checked by
  `git merge-tree --write-tree`; their `docs/evidence/` files are all under
  6 KB, within the evidence-size caps). They are cherry-picked, in date
  order and with `-x` provenance, onto the landing branch
  **`land/records-1011`** (worktree `.claude/worktrees/land-records-1011`,
  7 commits, 17 files, 0 outside `docs/`), together with this plan:
  `plan/method-identity-increment`, `plan/certificate-provenance`,
  `design/eval-order-model-0915`, `docs/reasoning-archaeology-0916`,
  `records/stray-panic-investigation-0927`, `design/seeded-heap-1009`.
  Landing the seeded-heap NOTE does not discharge its HARD STOP; the gate
  stays [USER] PENDING. The branch is an ordinary records train: records
  checks here, the fast gate at the merged tip, the audit ask, sign-off.
- *Already landed in substance, so neither pushed nor landed* —
  `records/raft-deltas-0930`: its docs are byte-identical on `main` and its
  code landed as `07694b27` (same subject, rebased); `prep/observer-terminal-harness`:
  every `tools/coverageharness/` file it adds is byte-identical on `main`
  (landed by `land/observer-terminal`); only its 2026-09-07 prep evidence
  dir is not on `main`, by its own «Prep (NOT landed)». Both: left here.
- *Pushed as live working / feature branches* (reasoning-side work that
  exists on no origin ref; golean-logic and raft-proofs may use it):
  `campaign-arc4d` (17 commits, 19 proof files under `proofs/GoLeanProofs`,
  +16 k lines, 2026-08-26), `campaign-ce` (4 commits: CE1 canonical-
  equivalence proofs), `campaign-wave-a` (3 commits: FamTrace/RoundFam
  proofs; its uncommitted tail is `refs/snapshots/2026-10-11-recovery/wip-campaign-wave-a`),
  `design-pass` (136 commits of Iris-corpus plan revisions and arc-2
  probes, +447 k lines, mostly docs). `wp-design`'s two docs are on
  `park/reasoning-2026-08-31` (origin) already; `w3-init` is the killed
  CallSpec track (`archive/callspec-era`, origin); `spec-parity-s1..s6`
  carry only the F15 fix's 2 commits beyond the merged `spec-parity` —
  left here.
- *Not pushed: the 19 typed-era lane branches* (`typed-byte-*`,
  `typed-b7-*`, `typed-context-store`, `typed-i1-envelope`, …,
  `storage-maintenance-*`). Their features are on `main`'s history and on
  the parking tag; what is unique to each lane is its review evidence
  (150 k–1 M lines per branch). Left here; any one of them can be pushed
  on request by name.

**The push set after D1** (from outside the sandbox, in this order): `main`;
tags `logic-offer/2026-10-03`, `typed-profiles/last-main-2026-09-16`;
`typed-consumer-sprint`, `typed-uintptr-identity`; `campaign-arc4d`,
`campaign-ce`, `campaign-wave-a`, `design-pass`; and, after its landing,
`main` again (carrying the six records branches and this plan). The six
records branches and the two superseded ones are deleted after the landing
is verified on milner-oath, with the 27 landed-by-patch ones.

| Branch | Last commit | Ahead of main | Not on main (patch-equivalent) | Contained in | Disposition |
|---|---|---|---|---|---|
| `campaign-arc4d` | 2026-08-26 | 17 | 17 | — | PUSH (D1: live reasoning-side working branch) |
| `campaign-ce` | 2026-08-26 | 4 | 4 | — | PUSH (D1: live reasoning-side working branch) |
| `campaign-wave-a` | 2026-08-26 | 3 | 3 | — | PUSH (D1: live reasoning-side working branch) |
| `channel-logic` | 2026-08-11 | 34 | 34 | origin/channel-logic | ON ORIGIN already |
| `channel-logic-s1` | 2026-08-11 | 20 | 20 | origin/channel-logic | CARRIED by origin/channel-logic (no push needed) |
| `channel-logic-s2` | 2026-08-11 | 26 | 26 | origin/channel-logic | CARRIED by origin/channel-logic (no push needed) |
| `channel-logic-s3` | 2026-08-11 | 33 | 33 | origin/channel-logic | CARRIED by origin/channel-logic (no push needed) |
| `channel-logic-s4` | 2026-08-11 | 40 | 40 | origin/channel-logic-s4 | ON ORIGIN already |
| `core/stray-panic-refusal-0927` | 2026-09-27 | 2 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `core/unseq-stage-e6a-0924` | 2026-09-24 | 8 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `design-pass` | 2026-08-28 | 163 | 136 | — | PUSH (D1: live reasoning-side working branch) |
| `design/eval-order-model-0915` | 2026-09-15 | 1 | 1 | — | PUSH (unlanded, current era) |
| `design/seeded-heap-1009` | 2026-10-08 | 1 | 1 | — | PUSH (open HARD STOP, [USER] gate pending) |
| `docs/bug004-item4-design-0930` | 2026-09-30 | 2 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `docs/gc3-design-0929` | 2026-09-29 | 1 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `docs/gc4-design-1001` | 2026-10-01 | 1 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `docs/gp-design-0928` | 2026-09-28 | 1 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `docs/logic-reply-0928` | 2026-09-28 | 2 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `docs/logic-team-note-0927` | 2026-09-27 | 1 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `docs/reasoning-archaeology-0916` | 2026-09-16 | 2 | 2 | — | PUSH (unlanded, current era) |
| `plan/certificate-provenance` | 2026-09-09 | 1 | 1 | — | PUSH (unlanded, current era) |
| `plan/method-identity-increment` | 2026-09-08 | 1 | 1 | — | PUSH (unlanded, current era) |
| `prep/observer-terminal-harness` | 2026-09-07 | 1 | 1 | — | PUSH (unlanded, current era) |
| `raft-proof-campaign` | 2026-08-29 | 206 | 179 | origin/raft-proof-campaign | ON ORIGIN already |
| `records/bug114-capture-0921` | 2026-09-21 | 1 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `records/raft-deltas-0930` | 2026-09-30 | 1 | 1 | — | PUSH (unlanded, current era) |
| `records/stray-panic-investigation-0927` | 2026-09-27 | 1 | 1 | — | PUSH (unlanded, current era) |
| `records/window-corpus-cl-1003` | 2026-10-03 | 1 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `review/block-allocation-1001` | 2026-10-02 | 1 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `review/continuations-0929` | 2026-09-30 | 1 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `review/intn-pick-0930` | 2026-10-01 | 1 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `review/method-promotion-0928` | 2026-09-29 | 2 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `review/numeric-locals-0930` | 2026-09-30 | 2 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `review/packet-a-contract-0927` | 2026-09-27 | 12 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `review/packet-b-bridges-0928` | 2026-09-28 | 5 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `review/packet-d-equations-1003` | 2026-10-03 | 2 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `review/panic-preprint-1003` | 2026-10-03 | 1 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `review/step-label-0928` | 2026-09-28 | 3 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `review/stray-panic-refusal-0927` | 2026-09-27 | 3 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `review/unseq-stage-e6a-0924` | 2026-09-24 | 11 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `review/window-1003` | 2026-10-03 | 1 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `snapshot/a3-admission-before-integration` | 2026-09-05 | 1 | 1 | — | not migrated (safety copy, left with this box) |
| `snapshot/bug103-before-a2-integration-20260905` | 2026-09-05 | 2 | 1 | — | not migrated (safety copy, left with this box) |
| `snapshot/f8-before-r29-records` | 2026-09-09 | 1 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `snapshot/interface-before-bug103-rebase-20260905` | 2026-09-05 | 1 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `snapshot/typed-boolean-before-helper-20260906` | 2026-09-06 | 3 | 3 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-boolean-before-recovery-20260906` | 2026-09-06 | 12 | 10 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-i1-before-positive-reviews-20260906` | 2026-09-06 | 33 | 29 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-recovery-runtime-before-static-e8a665e9` | 2026-09-06 | 28 | 23 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-recovery-setup-before-helpers` | 2026-09-06 | 30 | 24 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-abort-observer-20260906` | 2026-09-06 | 62 | 51 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-boolean` | 2026-09-06 | 7 | 6 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-bridge-reviews` | 2026-09-06 | 19 | 15 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-design-review` | 2026-09-05 | 3 | 3 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-helper-review` | 2026-09-06 | 9 | 7 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-i1-json-20260906` | 2026-09-06 | 85 | 68 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-i1-positive-20260906` | 2026-09-06 | 64 | 52 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-initialization-review` | 2026-09-06 | 12 | 10 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-o2-terminal-20260906` | 2026-09-06 | 88 | 70 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-observer-20260906` | 2026-09-06 | 56 | 46 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-observer-and-i1-reviews` | 2026-09-06 | 25 | 21 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-preflight-seal` | 2026-09-06 | 11 | 9 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-public-promotion-review` | 2026-09-06 | 23 | 19 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-r1-20260906` | 2026-09-06 | 76 | 62 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-recovery-control` | 2026-09-06 | 52 | 43 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-recovery-entry` | 2026-09-06 | 44 | 36 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-recovery-static` | 2026-09-06 | 29 | 25 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-recovery-storage` | 2026-09-06 | 38 | 33 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-renderer` | 2026-09-06 | 17 | 14 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-runtime` | 2026-09-06 | 14 | 12 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-shared-20260906` | 2026-09-06 | 73 | 60 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-sprint-before-uintptr-20260906` | 2026-09-06 | 96 | 75 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-string-members-before-observer-414a2abe` | 2026-09-06 | 48 | 39 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-string-members-before-r1-apparatus-review` | 2026-09-06 | 66 | 52 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-string-members-before-r1-model-review` | 2026-09-06 | 67 | 53 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshot/typed-uintptr-before-disposition-20260906` | 2026-09-06 | 62 | 51 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshots/typed-terminal-before-o2-review-20260906-0920` | 2026-09-06 | 80 | 64 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshots/typed-terminal-pre-accepted-renderer-20260906` | 2026-09-06 | 68 | 55 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshots/typed-terminal-pre-observer-20260906` | 2026-09-06 | 34 | 28 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `snapshots/typed-terminal-pre-shared-20260906` | 2026-09-06 | 65 | 53 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `spec-parity-s1` | 2026-08-09 | 14 | 2 | — | not migrated (reasoning era, pre-split; left with this box) |
| `spec-parity-s2` | 2026-08-10 | 26 | 2 | — | not migrated (reasoning era, pre-split; left with this box) |
| `spec-parity-s3` | 2026-08-10 | 33 | 2 | — | not migrated (reasoning era, pre-split; left with this box) |
| `spec-parity-s4` | 2026-08-10 | 39 | 2 | — | not migrated (reasoning era, pre-split; left with this box) |
| `spec-parity-s5` | 2026-08-10 | 45 | 2 | — | not migrated (reasoning era, pre-split; left with this box) |
| `spec-parity-s6` | 2026-08-10 | 62 | 2 | — | not migrated (reasoning era, pre-split; left with this box) |
| `storage-maintenance-20260906` | 2026-09-06 | 100 | 79 | — | not migrated (typed-profiles era lane, parked 2026-09-16; left with this box) |
| `storage-maintenance-main-20260906` | 2026-09-06 | 3 | 3 | — | not migrated (typed-profiles era lane, parked 2026-09-16; left with this box) |
| `typed-abort-observation-review` | 2026-09-06 | 57 | 47 | — | not migrated (typed-profiles era lane, parked 2026-09-16; left with this box) |
| `typed-b7-customer-review` | 2026-09-06 | 79 | 64 | — | not migrated (typed-profiles era lane, parked 2026-09-16; left with this box) |
| `typed-b7-kernel-review` | 2026-09-06 | 78 | 63 | — | not migrated (typed-profiles era lane, parked 2026-09-16; left with this box) |
| `typed-b7-original-review` | 2026-09-06 | 58 | 48 | — | not migrated (typed-profiles era lane, parked 2026-09-16; left with this box) |
| `typed-boolean` | 2026-09-06 | 12 | 10 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `typed-byte-runtime` | 2026-09-06 | 88 | 71 | — | not migrated (typed-profiles era lane, parked 2026-09-16; left with this box) |
| `typed-byte-runtime-review` | 2026-09-06 | 86 | 69 | — | not migrated (typed-profiles era lane, parked 2026-09-16; left with this box) |
| `typed-byte-store-consume-review` | 2026-09-06 | 81 | 67 | — | not migrated (typed-profiles era lane, parked 2026-09-16; left with this box) |
| `typed-byte-store-exec` | 2026-09-06 | 80 | 66 | — | not migrated (typed-profiles era lane, parked 2026-09-16; left with this box) |
| `typed-byte-store-proof` | 2026-09-06 | 78 | 64 | — | not migrated (typed-profiles era lane, parked 2026-09-16; left with this box) |
| `typed-byte-store-review` | 2026-09-06 | 79 | 65 | — | not migrated (typed-profiles era lane, parked 2026-09-16; left with this box) |
| `typed-consumer-charter` | 2026-09-05 | 2 | 2 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `typed-consumer-sprint` | 2026-09-06 | 96 | 75 | typed-consumer-sprint | PUSH (the ARCHIVE.md-designated sprint archive, retained unmodified) |
| `typed-context-store` | 2026-09-06 | 80 | 65 | — | not migrated (typed-profiles era lane, parked 2026-09-16; left with this box) |
| `typed-contract-review` | 2026-09-06 | 5 | 5 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `typed-i1-declarations` | 2026-09-06 | 36 | 32 | — | not migrated (typed-profiles era lane, parked 2026-09-16; left with this box) |
| `typed-i1-envelope` | 2026-09-06 | 86 | 72 | — | not migrated (typed-profiles era lane, parked 2026-09-16; left with this box) |
| `typed-i1-envelope-review` | 2026-09-06 | 78 | 64 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `typed-i1-json` | 2026-09-06 | 78 | 64 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `typed-observer-classification` | 2026-09-06 | 10 | 9 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `typed-observer-controls` | 2026-09-06 | 11 | 10 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `typed-panic-rendering` | 2026-09-06 | 8 | 7 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `typed-preflight` | 2026-09-06 | 26 | 26 | — | not migrated (typed-profiles era lane, parked 2026-09-16; left with this box) |
| `typed-r1-production-review` | 2026-09-06 | 69 | 55 | — | not migrated (typed-profiles era lane, parked 2026-09-16; left with this box) |
| `typed-recovery` | 2026-09-06 | 15 | 13 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `typed-recovery-runtime` | 2026-09-06 | 33 | 27 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `typed-recovery-setup` | 2026-09-06 | 34 | 28 | — | not migrated (typed-profiles era lane, parked 2026-09-16; left with this box) |
| `typed-recovery-terminal` | 2026-09-06 | 81 | 65 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `typed-shared-customer` | 2026-09-06 | 36 | 30 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `typed-shared-customer-review` | 2026-09-06 | 35 | 29 | — | not migrated (typed-profiles era lane, parked 2026-09-16; left with this box) |
| `typed-string-members` | 2026-09-06 | 72 | 58 | typed-consumer-sprint | CARRIED by typed-consumer-sprint (no push needed) |
| `typed-uintptr-identity` | 2026-09-06 | 64 | 53 | typed-uintptr-identity | PUSH (ARCHIVE.md: the HELD L5 `uintptr` source) |
| `w3-init` | 2026-08-27 | 1 | 1 | — | not migrated (reasoning era, pre-split; left with this box) |
| `w3-m` | 2026-08-27 | 2 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `window/packet-a-contract-0927` | 2026-09-27 | 10 | 0 | — | LANDED by patch (not migrated; deletable after the landing is verified) |
| `wp-design` | 2026-08-18 | 6 | 2 | — | not migrated (reasoning era, pre-split; left with this box) |

## 4. The global policy (`~/.claude/CLAUDE.md`) against this charter — divergences and proposed revisions

The global rules now in force: no machine-global changes; push only on
explicit at-the-moment sign-off; branches not `main`; fail-closed;
[AGENT]/[USER] provenance; `CLAUDE.md` is a working-practices doc, not a
log; **auto-memory is off** («Don't create or rely on memory files»); heavy
jobs through the box-wide **`capped`** with `$CAPPED_MEM_MAX` (default
32 G); **remove your own worktrees, `.tmp` and stale `.lake` when done**;
nightly backups skip `.lake .tmp _build _opam` and caches; one project per
box. Where this charter and its tooling diverge:

**4.1 `scripts/capped` vs the box-wide `capped` — RULED on the direction,
the figure and the tooling lane PENDING [USER] (D2).** [USER] Mike,
2026-10-11, verbatim (mid-session, relayed): «Note the global capped
script is the correct one to use, here and on the new box (which has
the same affordance)». So `capped` (box-wide, `/usr/local/bin/capped`)
is the invocation of record from today; the project wrapper and the gate
must be made to honour it (below), and until that lane lands,
`capped scripts/ci` still runs capped — at the project's 64 G, not the
box's 32 G, for the reason that follows.** The project wrapper (`scripts/capped`, 2026-09-01)
and the box tool (`/usr/local/bin/capped`, «ported from the per-project
scripts/capped») differ in every interface detail:

| | `scripts/capped` | `/usr/local/bin/capped` |
|---|---|---|
| limit variable | `GOLEAN_MEM_MAX` | `CAPPED_MEM_MAX` (projects set a default in `scripts/env.sh`) |
| default | 64 G | 32 G |
| «already capped» marker | `GOLEAN_CAPPED=verified` | `CAPPED_STATE=verified` |
| opt-out | `GOLEAN_MEM_MAX=none` | `CAPPED_MEM_MAX=none` |

`scripts/ci` re-wraps itself through `scripts/capped` unless
`GOLEAN_CAPPED=verified`, and scales `LEAN_NUM_THREADS` from
`GOLEAN_MEM_MAX` (default 64 G). So `capped scripts/ci`, the invocation the
global rules prescribe, does NOT run under the box cap: `scripts/ci` sees no
`GOLEAN_CAPPED`, re-enters through `scripts/capped`, which creates a
**sibling** cgroup under `app.slice` (its documented placement) with a 64 G
limit and moves the gate into it — out of the 32 G cgroup the box tool
certified. The box's cap is silently replaced by the project's. Nothing is
uncapped, but the box default is not honoured and no one is told. There is
no `scripts/env.sh` here (cerberus-sl has the reference shape).

**D2 RULED on the figure too** ([USER] Mike 2026-10-11, verbatim: «D2:
conform to the box default, of course raising it is allowed during
execution when needed»). So: NO project default — the box's
`$CAPPED_MEM_MAX` (32 G) governs, no `scripts/env.sh` override; a job that
needs more is raised per invocation (`capped -m 64G -- <cmd>`) with the
reason stated where it is run. The one known case is the measured one
(`docs/operational-lessons.md`: «cold worktree full builds need 64G+»), so
a cold full build or a cold `scripts/ci` in a fresh worktree is invoked as
`capped -m 64G -- scripts/ci …`; a warm primary build stays at the box
default. The box-wide build lock stays (two raised builds over-commit
125 G — the crash class).

Implementation (one lane, `fix/capped-alignment`, fast gate + audit ask;
gate tooling, not the trusted surface):
1. no `scripts/env.sh` default; `scripts/ci` scales `LEAN_NUM_THREADS`
   from the box's `CAPPED_MEM_MAX` (32 G → 4 threads at the 8 G/thread
   budget; a `-m 64G` raise → 8) and NAMES the cold-build case in its
   output when the cap is the box default and no `.lake` is present;
2. make `scripts/capped` a shim: if `/usr/local/bin/capped` exists, map
   `GOLEAN_MEM_MAX` → `CAPPED_MEM_MAX` when only the former is set, treat
   `CAPPED_STATE=verified` as already-capped (never re-wrap under the box
   tool), and `exec` it; keep the current body only as the fallback where
   the box tool is absent;
3. `scripts/ci`: accept `CAPPED_STATE=verified` as well as
   `GOLEAN_CAPPED=verified`, and derive the thread scaling from whichever
   limit variable is set;
4. `CLAUDE.md` «The gates» and `docs/operational-lessons.md` §Memory: say
   `capped` (box tool), box default, `-m 64G` for the named cold-build
   case; the shim for callers that still say `scripts/capped`.
The `CLAUDE.md` wording and the tooling land TOGETHER: a charter that says
`capped` while `scripts/ci` still re-wraps through `scripts/capped` would
prescribe an invocation that silently swaps caps. Until that lane lands,
`capped scripts/ci` runs at the project wrapper's 64 G (§4.1 above), which
is now a known deviation from the ruling, not a default.

**4.2 Worktree hygiene — D4 agreed.** 77 worktrees exist; the global
rule says remove your own when done (and, since 2026-10-11, the global file
also carries the crash rule: snapshot every dirty worktree to a ref before
touching anything — §2 did exactly that). The charter's merge protocol
(«one writer per worktree») never says when a worktree ends. Proposal: the
train's close step prunes the landed lane's worktree AND its gitignored run
output, keeping the branch (§5 draft 2 gives the exact rule the [USER]
already ruled on 2026-09-11/09-28). For the migration: recreate NO worktree
on the new box by default; a lane re-creates its own from the branch.

**4.3 Auto-memory off.** Nothing in the repo depends on memory files, but
two pointers in `docs/2026-09-05_master-plan.md` (lines 1289–1290) cite
memory files by name (`background-task-hour-cap`, `never-kill-by-pattern`)
that no session will see again. Fix: replace the pointers with the practice
text (§5, drafts 1 and the operational-lessons entries). Records-only.

**4.4 Box identity.** The global note lists `reynolds-oath` as the
cerberus-sl box, yet `golean`, `golean-logic` and `raft-proofs` live here
too. After the move the global note's box list is the [USER]'s to update
(machine-global; D8). This charter names no box, so it needs no edit.

**4.5 Provenance and the decisions file.** Already as the global rule asks:
`[AGENT]`/`[USER]` on every logged decision, rulings in
`docs/2026-08-31_qrow-rulings.md`, histories in commit messages; `CLAUDE.md`
holds standing rules only. No change.

**4.6 Scratch retention is by design and unbounded — D5 RULED ([USER]
Mike 2026-10-11: «D5: keep the last run only»).** Implementation: on a
PASSING run `tools/admission-check.py` replaces a single
`.tmp/admission-audit-last/` with the run's scratch (and prints that
path); a FAILING run's scratch is retained under its own name, as now, so
the fail-closed evidence is never overwritten by a later green run. One
small gate-tooling change, foldable into the `fix/capped-alignment` lane.
Original finding: `tools/admission-check.py` keeps its 370 M scratch per run
(«Scratch is worktree-local and retained») and nothing prunes it: 21 runs =
7.8 G of the 9.4 G `.tmp/`. The other scratch families
(`golean-lsimports.*` 382 files, `check-*-test.*`, `declaration-fixture.*`)
are small. Proposal: retain the LAST run's admission scratch only (rename on
success; the failing run's is kept by the fail-closed rule), or prune at
train close under the §5 draft-2 rule. Either is a gate-tooling change with
the fast gate and the audit ask.

## 5. The old auto-memory (`~/.claude/projects.old/-home-dev-projects-golean/memory/`) — what migrates

48 files were read against `CLAUDE.md`, `docs/architecture-rules.md`,
`docs/operational-lessons.md` and the global rules ([AGENT] review worker,
read-only). Result: **19 already captured** (charter, architecture rules,
lessons or the global file — e.g. the alias rule, the cgroup cap, the
evidence-size rule, F10, the top-level goal, the snapshot-ref practice);
**10 belong in `docs/`** as history/plan and are there already except three
operational remedies (below); **13 are parked-era** (Iris corpus, WP, verdi,
gobra, channel-logic, RefinedGo framing, the spec-truth campaign — all
superseded by the split or indexed in ARCHIVE.md); **6 are standing
practices that exist NOWHERE in the repo** and that a fresh session would
get wrong. The golean-logic memory (8 files) concerns that repo; its
`single-user-across-projects` is the mirror of draft 3 and adds its caveat.

**D3 CLOSED — nothing migrates.** [USER] Mike 2026-10-11, verbatim:
«D3, these are all minor, you can drop them». The remainder below is
DROPPED: no `CLAUDE.md` addition from the old memory, the
`architecture-rules.md` `rm` wording stays as it is (the global file's
removal rule governs), and the drafts are kept here only as the record of
what was reviewed and declined. The old memory directory stays outside
the repo and is not copied to milner-oath.

**The drafts as reviewed (declined) — D3 history.**
[USER] 2026-10-11: «D3: Some of these have now landed in the global
claude.md. What's left?» Against the global file as of today: its
«Practices that apply everywhere» now carry never-kill-by-pattern (the
second half of draft 1) and the crash-snapshot rule; its box section
carries the worktree/`.tmp`/`.lake` removal rule (the principle of draft 2)
and the no-memory-files rule. **Left for this charter**: draft 1's FIRST
half (coordinator dispatches, workers implement; the Fable/Opus split),
draft 2's project specifics only (the protected primary paths, the
`git check-ignore` test, the `${w:?}` guard, never in the same command as a
gate run — and the `architecture-rules.md` `rm` contradiction), and drafts
3, 4, 5, 6 in full. Verbatim drafts, placement named; each is a [USER]
ruling the memory recorded, re-cited as relayed:**

1. *Working practices* — «The coordinator dispatches and verifies; workers
   implement. Inline coordinator work only for glue (commits, snapshots,
   ref surgery), harness emergencies and synthesis ([USER] 2026-09-01).
   Every brief that may run gates in the background says: never kill
   processes by name or pattern — record the PID of what you start and
   kill only that (shared box; incident 2026-09-03, noodler report §7).»
   Optional: «Fable for design, hard proofs and adversarial audits; Opus
   for mechanical, records and fix rounds ([USER] 2026-09-29).»
2. *Working practices* — «At each train close, prune the landed lane's
   gitignored run output (`artifacts/`, `.tmp/`, `.lake/`, `deps/`),
   keeping the worktree and branch ([USER] 2026-09-11, 2026-09-28); only
   paths `git check-ignore` confirms, never the primary's
   `artifacts/coverage`, `artifacts/go-build-cache`,
   `artifacts/build-lock.d`; targets written as `"${w:?}/${p:?}"` and never
   in the same command as a gate run.» **Conflict to resolve:**
   `docs/architecture-rules.md` («Do not run rm … without explicit
   approval») contradicts this standing approval; one of the two must be
   edited, and the global «remove your own worktrees» rule now sides with
   the prune. Under the migration, «keeping the worktree» should become
   «removing the worktree, keeping the branch» (§4.2).
3. *What this repo is*, after the 2026-09-22 customer quote — «The
   customer's user is our user ([USER] Mike 2026-09-30, relayed: «I'm the
   user for all three teams so this is more a design tradeoff question than
   a user negotiation question»): notes from golean-logic and raft-proofs
   are design input to one tradeoff, decided on the merits and recorded
   verbatim with provenance, not positions to negotiate; a [USER] ruling
   recorded in another repo does not by itself authorize work here.»
4. *Working practices*, the autonomous-arcs bullet — «A brief cannot turn a
   [USER] decision into an [AGENT] one: a lane applying a plan's
   recommended default on a [USER]-owned decision tags it «[AGENT]
   default; [USER] ratification PENDING at the merge gate», never «ruled»,
   and the merge ask lists every PENDING tag for ratification or
   reversal.»
5. *The gates* — «Gates are speedbumps against honest mistakes, not audit
   targets ([USER] 2026-08-11): refute-by-default review is aimed at
   semantics, claims and records; a gate is reviewed for «does it catch the
   honest mistake, is it simple enough never to be wrong, could we delete
   it», and a gate-escape finding is answered by checking the convention,
   not by growing the gate.»
6. *Working practices* — «Codex grinds ([USER] 2026-10-05): frozen
   objective, hash-checked fence, milestones as checkpoints (commit,
   self-accept, continue — no per-milestone check-in); refuted or
   unprovable statements go to a REPAIRS file with a proposed repair
   instead of stopping the run; the governing text lives in the tracked
   brief (`docs/codex-briefs/`, example
   `docs/2026-10-04_pool-relation-grind-brief.md`).»

**Operational remedies that would otherwise be lost → `docs/operational-lessons.md`
(records-only, no ruling needed):** (a) the harness kills background tasks
at about one hour — long runs are parked with a `HANDOFF.md` and resumed;
(b) the baseline header conflicts at every train — `merge-tree` dry run
first, `pipefail` on the rebase, the row tally by awk never by hand;
(c) never rsync-warm the primary's `.lake` from a lane worktree — Lake
records absolute paths; purge files naming `/.claude/worktrees/`
(2026-10-01).

The memory directory itself stays where it is (`~/.claude/projects.old`,
outside the repo); it is not copied to the new box by this plan.

## 6. Disk hygiene before the move — D4 agreed ([USER] 2026-10-11 «D4: agreed»): `.tmp` now, the rest at phase D

**Executed 2026-10-11 ([AGENT]):** the primary's `.tmp/` scratch families
removed — 21 × `admission-audit-*` (7,794 MB), 382 × `golean-lsimports.*`
(1,132 MB, orphaned `mktemp` files of killed import runs), 20 + 20 + 21
self-test scratch dirs, 5 `ci-libraries-*`, 10 `go-build*`, three train
scratch entries, and one stray copy of golean-logic's globals-init design
note (byte-identical to `design/globals-init-1005:docs/2026-10-05_globals-init-design.md`
in that repo). `.tmp/` went 9,573 → 274 MB (the live session dir only).
Log: `artifacts/disk-prune-2026-10-11.log`. Nothing under worktrees,
`artifacts/` or `deps/` was touched (phase D).

| What | Size | Regenerable? | Proposal |
|---|---|---|---|
| `.tmp/admission-audit-*` (21), `golean-lsimports.*` (382), `check-*-test.*` (40), `declaration-fixture.*` (21), `ci-libraries.*`, `go-build*` | 9.4 G | yes (gate scratch) | `rm -rf .tmp/<family>*` — keep `.tmp/claude-1000` (live session dirs) |
| worktree `.tmp/` dirs (8, ≤ 40 M each) and `.claude/worktrees/step-label/.lake` (632 M) | 0.7 G | yes | remove with the worktrees |
| `artifacts/go-build-cache` | 11 G | yes (Go rebuilds it) | delete AFTER the new box's first green `ci --diff` |
| `artifacts/coverage`, `artifacts/train-r*` | 0.7 G | run outputs; the evidence tails are under `docs/evidence/` | keep until the new box's gate is green, then delete |
| `deps/verdi-raft`, `deps/opam-coq818`, `deps/lean4export`, `deps/BRiCk`, `deps/aeneas`, `deps/iris-lean`, `deps/brick-wp`, cedar checkouts | ≈ 4.6 G | reasoning-era / opt-in; raft-proofs' tools still read `verdi-raft` and `opam-coq818` by explicit path (ARCHIVE.md) | do not carry for golean; the [USER] decides for raft-proofs (D9) |
| the 77 worktrees | 32 G | from the branches/refs | removed with the box after the push set is confirmed on `origin` (§7 phase C) |

## 7. The migration plan — target: `milner-oath`, by push and clone only

[USER] 2026-10-11: «D7: I'll manage that. We're moving Go projects to
milner-oath» and, on the bundle this plan first proposed: «I'm not doing
this, the repo is supposed to be free-standing, why would we do this?» and,
verbatim: «Yes, we're not going to packrat everything. If it's important
we push it. If it isn't, we throw it out». So the move is the ordinary one: everything that matters is on `origin`,
milner-oath clones it, nothing is copied box to box. The 409 snapshot refs,
the stash entries, the §2 recovery refs, the 77 worktrees, the parked-era
lanes not in the push set, and the gitignored `deps/`, `artifacts/` and
`.lake/` are left with this box and retired with it. The bundle idea is
withdrawn (it was an [AGENT] way of carrying local-only refs without
putting 300 branches on GitHub; under the free-standing rule that is the
wrong trade).

**Phase A — this box.**

- A1 ([AGENT], done) the recovery refs of §2 — a local safety net only.
- A2 ([AGENT], approved) `land/records-1011` fast-forwarded onto `main`,
  the fast gate at the merged tip; then the `fix/capped-alignment` lane
  (§4.1, §4.6) built, gated, audit-asked and, on sign-off, landed.
- A3 ([USER], outside the sandbox; «I'll do this when we're ready») the
  push set of §3, each push checked against `git ls-remote origin` first —
  a non-fast-forward on `main` means someone pushed from elsewhere and is a
  STOP:

```
cd /home/dev/projects/golean
git ls-remote origin main refs/tags/logic-offer/2026-10-03 refs/tags/typed-profiles/last-main-2026-09-16
git push origin main                                   # fast-forward from 6a90ba8d
git push origin logic-offer/2026-10-03 typed-profiles/last-main-2026-09-16
git push origin typed-consumer-sprint typed-uintptr-identity
git push origin campaign-arc4d campaign-ce campaign-wave-a design-pass
git fetch origin && git status -sb                     # expect: ## main...origin/main
```
  `campaign-wave-a`'s uncommitted tail (`wip-campaign-wave-a`, §2) is not
  pushed unless the [USER] wants it as a commit on that branch.
- A4 ([USER]) golean-logic's own pass (its `develop` and review branches
  are local-only, §8).

**Phase B — on milner-oath ([USER] provisions; agent work after the
clone).** Needed: the box-wide `capped` (there already); Lean `v4.32.2`
via elan; Go `go1.26.5` at `/usr/local/go` exactly (`baselines/go-oracle-pin`;
drift is a red gate); `python3` ≥ 3.11; `git`, `jq`, `sha256sum`;
credentials for the private `OathTech/covmap` and `OathTech/grossmith`
(`scripts/setup-deps` names them; the gate's default set `goose`, `go`,
`raft` is public). Then:

```
git clone git@github.com:OathTech/golean.git ~/projects/golean && cd ~/projects/golean
git fetch origin --tags && git branch -r | wc -l                   # the push set, nothing else
scripts/setup-deps                                                 # goose, go, raft at the pinned revs
scripts/setup-deps --only covmap,grossmith                         # named, private
capped -m 64G -- lake build                                        # cold build: the named raise (D2)
capped scripts/ci                                                  # fast gate (warm now: box default)
capped scripts/ci --diff                                           # expect PASS 3936/3936 (3705/231) as at r75
python3 tools/certification.py release-check --base <origin/main at the push>
```
  Expectations to treat as findings, not failures to fix: the certificate
  provenance step compares compiled inputs, so a different machine with the
  same toolchain should pass; if it goes STALE the cause must be named
  (toolchain byte-identity, Go build cache) before any re-certification. A
  differential count other than 3936 = 3705/231 is a STOP (the oracle pin
  or the environment drifted). No worktree is recreated; a lane makes its
  own from its branch.

**Phase C — retire here ([USER] sign-off, D4 phase D).** After phase B is
green: the worktrees, `artifacts/`, `deps/`, `.lake/` and the primary
checkout itself go with the box. Nothing on it is needed once `origin`
holds the push set.

## 8. Sibling repositories on this box (findings only; outside this lane's scope)

- **`~/projects/golean-logic`** (the upstream customer): `main` equals
  `origin/main`; 47 worktrees; `develop` is 329 commits ahead of `main`
  and local-only, as are the consolidation, review, trust-rebaseline,
  port/repin and generality branches (100+ refs, 2026-10-05..08); one dirty
  worktree (`a1`, 3 entries). Its pin of golean is `20d3946d`, which IS on
  `origin/main`, so golean's push does not block it. It needs the §7
  treatment before the move (D7).
- **`~/projects/raft-proofs`**: `main` equals `origin/main`; several
  hundred local-only branches (audit/, proof/, mirror/, review/, docs/,
  land/, snapshot/). The global box note says this project lives on
  `milner-oath`; the copy here was moved from golean's `deps/` on
  2026-09-27 (ARCHIVE.md). [USER] 2026-10-11 (D9): raft-proofs is already
  migrated to milner-oath — the copy here is NOT canonical and is not part
  of this move; its reasoning-era `deps/` here are not carried.

## 9. Decisions this plan needs ([USER]; numbered for the reply)

- **D1** RULED 2026-10-11 (land the records branches; push live working
  and meaningful-feature branches). Applied in §3: `land/records-1011`
  prepared; the push set is `main`, the two tags, the two archive
  branches, the three `campaign-*` branches and `design-pass`. Open only:
  the merge sign-off for `land/records-1011`.
- **D2** RULED in full ([USER] 2026-10-11: box-wide `capped`; «conform to
  the box default, of course raising it is allowed during execution when
  needed»). Open only: the go-ahead for the `fix/capped-alignment` lane
  (shim, `scripts/ci` accepting `CAPPED_STATE` and scaling from the box
  cap, the charter wording).
- **D3** RULED («these are all minor, you can drop them»): no charter
  additions from the old memory; the `rm` wording stays. Closed.
- **D4** RULED («agreed»): the primary's `.tmp` pruned 2026-10-11 (9.3 GB
  freed, §6); worktrees, `artifacts/` and `deps/` at phase D.
- **D5** RULED («keep the last run only»): §4.6 says how; lands with the
  `fix/capped-alignment` lane.
- **D6** The seeded-heap HARD STOP stays open; it travels by push (D1) and is
  not re-posed here.
- **D7** RULED («I'll manage that. We're moving Go projects to
  milner-oath»): the [USER] runs the sibling passes; the target box is
  `milner-oath`.
- **D8** RULED («nothing to do, I'm editing it»): the [USER] edits the
  global box note; no action here.
- **D9** RULED («no, I've already migrated raft-proofs»): no reasoning-era
  `deps/` checkout is carried; `deps/` on milner-oath is the gate's default
  set plus `covmap`/`grossmith` only.

## 10. This lane's gate record

Records-only lane (one new file under `docs/`, no runtime, gate or wire
change), so the Lean build was NOT run. Run here before the commit:
`scripts/check-evidence-size`, `scripts/check-agents-alias`,
`scripts/check-bugs.sh` — results in the commit message. The audit ask is
posed in the session reply; the merge is the [USER]'s.
