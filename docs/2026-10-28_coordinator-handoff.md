# Coordinator handoff — 2026-10-28

STATUS: **HANDOFF** ([AGENT] coordinator, 2026-10-28). The coordinating session of
2026-10-26/27 died twice of its own process memory (see the operational lesson
of this date); the campaign continues in a FRESH session from this page. Nothing
durable was lost: every lane's work is on a branch or in a snapshot ref.

## 1. What awaits the owner (unchanged since the last ask)

Five trains were staged, gated and fast-forwardable from main `89ba27c5`; they LANDED on 2026-11-05 on the owner's sign-off (main = `d2bd4740` + this page's records commit). The original ask, kept as written: ONE
sign-off lands them all: `git merge --ff-only stage/train-27-1027` (tip
`d2bd4740`, 41 commits). Contents: trains 23–27 — sweep batches 1–4 over sixteen
shapes (1,426 + 587 rows), the fix lanes that closed nineteen findings, the
campaign record on every swept entry, three apparatus entries. Each train's gate
line is in release-readiness row 56. The eight rulings asked at the ask are in
the session's last ask message and summarized in row 56 / the entries:
zero-size identity (model gc's layout; byte-slice identity a recorded latitude),
the dedup checker's stricter main-exit mirror, the three single-caller defaults
commit, BUG-227's reclassification, BUG-218/221 keep-or-strike, BUG-280 (gc's
own `make` deviation — record + report upstream), BUG-236 option A (a blank
`errors` import — an exception to the 2026-09-03 denial), the BOM policy and
the zero-length-range dereference alternative.

## 2. Lane state after the second crash (branches and snapshots)

| lane | branch / tip | base | state | next |
|---|---|---|---|---|
| fix-binding (BUG-300/301/302) | `frontend/fix-binding-1027` `5a58eeea` | stage27 `d2bd4740` | DONE: full gate green, 9 rows green, twin pin moved (documented) | restack onto the next stage |
| fix-unseq-seam (BUG-310/311/312/313) | `frontend/fix-unseq-seam-1027` `4a2cbc93` | stage27 `d2bd4740` | fixes committed (310/311/313; 312's disposition in the commit); its `--diff` at 17:18 ended RESULT FAIL — read `.claude/worktrees/fix-unseq-seam/.tmp/ci-diff-1.log` to see whether the only drift is the rows going green (then re-pin) or a real failure | a NEW lane: judge the log, re-pin or fix, gate, report |
| sweep S19 (init order) | `sweep/s19-init-order` `3bce028f` | main | DONE: BUG-340/341 entered, 56 rows, re-pinned, gates green | restack |
| sweep S18 (sizes) | `sweep/s18-sizes` `d7c9b657` | main | rows + records committed (a 1055-cell matrix); the fast tier at 17:21 FAIL (expected pre-re-pin), the `--diff` at 17:27 died with the session | a NEW lane: run the `--diff`, re-pin, fast tier, report |
| sweep S15 (scheduling) | `sweep/s15-scheduling` at main | main | UNCOMMITTED partial work (7 entries: four row packages) — snapshot `refs/snapshots/sweep-s15-crash2-1028` (`b0b85c69`), left in the worktree | a NEW lane: read `.tmp/matrix.md`, finish |
| sweep S16 (race detector) | `sweep/s16-race` at main | main | UNCOMMITTED partial work (8 entries) — snapshot `refs/snapshots/sweep-s16-crash2-1028` (`5bc3bf72`) | a NEW lane: finish |

Reserved bug numbers: S15 360–369, S16 370–379 (S18 used 350–359 as far as its
entries show; S19 used 340–341). The next free apparatus number is BUG-299.

Remaining shapes after batch 5: S11 (tier 1); S17, S28, S29, S21, S23 (tier 2);
S22 (tier 3) — `docs/defect-shapes.md` §3 has the axes; reserve numbers from 380.

## 3. How the next session works (the rules that kept this one honest)

- One sweep lane per shape, briefed from the plan's §4 (`docs/2026-10-27_defect-neighbourhood-campaign.md`)
  with the shape's §3 line, a reserved number block, and the standing rules
  (worktree, `capped`, the box lock, no code changes in a sweep, re-pin only from
  a full run). Fix lanes per finding batch; a fix lane bases on the latest stage.
- At most THREE concurrent subagents, and the coordinator keeps its own turns
  short: the process memory, not the box, killed the last session (two crashes,
  each with 3–6 live agents on a 26 MB transcript).
- Restacks with `tools/stage/pick.sh`; the stage's records commit recounts
  `docs/defect-shapes.md`; the merge gate at the stage tip; the ask names the
  gate lines, the reds and the rulings; merge only on the owner's word.
- Worktrees to remove once the trains land: every `.claude/worktrees/sweep-s*`,
  `fix-*`, `stage2*-1027` (each holds a `.lake` copy of ~640 MB and run
  artifacts of up to 11 GB); `codexpass-1013` on the owner's word.


## 4. Addendum 2026-11-06 — the stop cause and the working limits

The stops were the user slice's memory limit (operational lesson of 2026-11-06),
not the session process. Working limits from here: one merge-tier gate at a time
on the whole box (check for orphaned `scripts/ci` runs of a dead session before
starting one); `CAPPED_MEM_MAX=32G` for gates on a warm tree; at most two lanes at
once, one heavy job each; sampling probes under `CAPPED_MEM_MAX=4G`, serially.

State at the addendum: trains 28–31 staged on `stage/train-31-1105` (`d296811a`,
29 commits over main), its merge gate running orphaned when the session stopped
(its log in that worktree's `.tmp/ci-diff.log`); S22 (readout) partial in its
transcript only; S15 at WIP `989a38e3` (branch `sweep/s15-scheduling`); S16 at
snapshot `refs/snapshots/sweep-s16-crash4-1106`.
