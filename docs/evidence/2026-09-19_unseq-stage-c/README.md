# The native `unseq` pilot (Stage C) — census, predictions, gate tails (2026-09-19)

[AGENT] Evidence for lane `core/unseq-stage-c-0919` (worktree `.claude/worktrees/unseq-stage-c`;
base main `6a7beb3d`). Consuming docs: `docs/2026-09-19_unseq-stage-c-design.md` (C0: the
pilot grammar, census, wire schema, decoder spec) and the lane handoff
`docs/2026-09-19_unseq-stage-c-handoff.md`. Small records only (caps: 256 KiB / 4 MiB); every
number is copied from the named log under the lane worktree's `.tmp/` (untracked) and the
commands to regenerate are given. The reference sets the end-to-end runs must reproduce are the
v2.1 spike's (`docs/evidence/2026-09-16_eval-order-v2-spike/outcomes.txt`).

- Toolchain: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`); Lean
  `leanprover/lean4:v4.32.2` (repo pin); the machine binary at C0 is main's
  (`sha256 a014183b0dfad716…` — identical sources, the C0 slice changes no Lean file).
- Host: linux/amd64, 32 cores, 125 GiB, shared box (a merge train ran concurrently until
  22:45Z); every lake/lean command through `scripts/capped`.
- Provenance: the classifier, census and predictions are [AGENT]; the rulings they implement
  are [USER] Mike 2026-09-19, relayed (see the design note §0).

## C0 — the census and the wire-neutrality check (tree: main `6a7beb3d` + the C0 frontend edits, before the C0 commit)

| file | what | producer |
|---|---|---|
| `census-admitted.tsv` | the 120 admitted sweeps (pkg, unit, file:line, function, form, counts, reason) — the corpus rows that will lower as `unseq` graphs at C2 | `.tmp/nativefrontend --unseq-census --dir <pkg>` over every `Corpus/coverage/exec/**/cases.tsv` directory, admitted rows only (`.tmp/census/run.sh`) |
| `census-summary.txt` | totals (107 773 sweeps / 120 admitted / 28 packages / 0 in imported units), forms, per-package counts, the legacy reasons, the affected rows by lane and baseline, the raft twin (10 203 sweeps, 0 admitted, pin byte-identical), the wire-neutrality line | the same run + `.tmp/census/neutral.sh` |
| `affected-rows.tsv` | the 345 rows of the 28 packages with lane, baseline result/stage and whether the row's SUBJECT function itself holds an admitted sweep (50 rows) | `python3` over the census and `baselines/native-full.tsv` |
| `gc-flips.txt` | gc's draw for the four predicted flip rows (output bytes + status) | a recovering harness over the E13 package copy (`.tmp/gc-flips`), `go run` at the pin |

Reproduction (from the repo root, the C0 frontend built with
`GOCACHE=$PWD/.tmp/gocache GO111MODULE=off go build -o .tmp/nativefrontend ./tools/nativefrontend`):

    .tmp/nativefrontend --unseq-census --dir Corpus/coverage/exec/builtins/e13-sibling-panic-order
    # census-summary's twin line: assemble the twin as scripts/check-frontend-pins does, then
    .tmp/nativefrontend --unseq-census --dir <twin dir>
    # wire neutrality: build the main-tip frontend from `git archive main tools/nativefrontend`,
    # emit every corpus package with both binaries, cmp — .tmp/census/neutral.sh

Conclusion (C0): the pilot grammar of the design note §1 admits 120 sweeps in 28 corpus
packages and none in the raft twin; the C0 frontend is wire-neutral on all 1353 packages; gc's
draws for the four predicted flips (6/`mut`, 12/`mut`, `[9]` after `f wit 5`, `[5]` after `f`)
lie inside the derived graph sets (design note §3). Nothing here is a machine-side claim: the
decoder (C1) and the lowering (C2) do not exist at C0.

## Gate lines (captured exit codes; appended per slice)

| slice | command | exit | wall | tree | result |
|---|---|---|---|---|---|
| C0 | `GOCACHE=… GO111MODULE=off go test ./tools/nativefrontend` | 0 | 1 s | main `6a7beb3d` + C0 edits (pre-commit) | ok — the 3 new classifier tests + the standing suite |
| C0 | `scripts/capped scripts/check-frontend-pins` | 0 | 2 s | same | hidden-dep-order pin ok; twin wire ok (`e1a877251021…`, byte-identical); stdlib pin ok (61 files) |
| C0 | `scripts/capped scripts/ci` (fast gate, box-wide lock) | **1** | 381 | same | every step ok EXCEPT: `certificate provenance` STALE — «changed dependency files/tools/nativefrontend/main.go» (the frontend is a certification input; the 5a-class item every frontend change raises, re-certified at C1's `--slow`), and the two fresh-worktree items `negative baseline diff` / `baseline diff` (NO recorded run in this worktree yet — the first `--diff` run is C1's). Core build warning-free; core audit, admission, declarations, wire boundary, method identity, unseq scheduler (Stage B), frontend pins, go tests, eval 267 ok. Reconciler: C9 HIGH = the same STALE certificate. `c0-gate.txt` |
