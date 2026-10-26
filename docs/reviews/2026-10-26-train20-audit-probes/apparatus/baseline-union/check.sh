#!/usr/bin/env bash
# check.sh — the baseline union of train 20 against main, mechanically: every main row kept
# byte-identically, the appended rows each named in a header reason block, the header counts
# equal to the rows, no duplicate id, the lanes' blocks byte-identical to the lanes' own, the
# re-pin guards and the baseline diff of the recorded runs. Run from anywhere in the worktree
# at the stage tip (or the audit branch); <old> defaults to main.
set -u
export LC_ALL=C
ROOT="$(cd "$(dirname "$0")" && git rev-parse --show-toplevel)"; cd "$ROOT"
OLD="${1:-main}"; T="$(mktemp -d)"; trap 'rm -rf "$T"' EXIT
for base in native-full negative-full; do
  B="baselines/$base.tsv"
  git show "$OLD:$B" | grep -v '^#' | sort > "$T/old"; grep -v '^#' "$B" | sort > "$T/new"
  echo "## $B vs $OLD"
  echo "  rows (incl. the column header): old $(wc -l < "$T/old")  new $(wc -l < "$T/new")"
  echo "  old rows missing or altered in new: $(comm -23 "$T/old" "$T/new" | wc -l)"
  echo "  rows new to new: $(comm -13 "$T/old" "$T/new" | wc -l)"
  echo "  duplicate ids: $(grep -v '^#' "$B" | cut -f2 | sort | uniq -d | wc -l)"
  echo "  verdicts: $(grep -v '^#' "$B" | cut -f1 | grep -v '^result$' | sort | uniq -c | awk '{printf "%s %s  ", $2, $1}')"
  echo "  header count line(s): $(grep -n '^# cases:\|^# manifest_cases:' "$B" | head -3 | tr '\n' ' ')"
  echo "  header lines of $OLD changed in new (count line expected): $(diff <(git show "$OLD:$B" | grep '^#') <(grep '^#' "$B") | grep '^<' | cut -c1-80)"
  if [ "$base" = native-full ]; then
    comm -13 "$T/old" "$T/new" | cut -f2 | sort > "$T/newids"
    grep -E '^#     [a-z]' "$B" | awk '{print $2}' | sort > "$T/named"
    echo "  appended ids not named in a header block: $(comm -23 "$T/newids" "$T/named" | wc -l)"
  fi
done
echo "## the lanes' blocks inside the union (0 = byte-identical)"
echo "  core lane 584adb0f vs stage 8c87b3ce, baselines/: $(git diff core/struct-through-conversion-1026 8c87b3ce -- baselines/ 2>/dev/null | wc -l) diff lines"
echo "  frontend lane fcb2de87 vs stage tip, baselines/ minus the core block and the count line: $(git diff frontend/workspace-and-oracle-1026 stage/train-20-1026 -- baselines/ 2>/dev/null | grep '^[-+]' | grep -v '^+++\|^---\|^[-+]# cases:' | grep -vc '^+#     pointers/struct-through-conversion\|^+PASS	pointers/struct-through-conversion\|^+#   \|^+# re-pinned: 2026-10-26 \[AGENT\], lane core/struct-through-conversion-1026') other lines"
echo "## re-pin guards vs $OLD (rc 0 = pass)"
for s in check-row-removals check-cause-regressions check-alternation-survival; do
  for pair in "native-full exec" "negative-full negative"; do set -- $pair
    if [ "$s" = check-row-removals ]; then ./scripts/$s "git:$OLD:baselines/$1.tsv" "baselines/$1.tsv" "$2" >/dev/null 2>&1; else ./scripts/$s "git:$OLD:baselines/$1.tsv" "baselines/$1.tsv" >/dev/null 2>&1; fi
    echo "  $s $1: rc=$?"
  done
done
echo "## the recorded runs vs the baselines"
./scripts/coverage-baseline-diff --full --baseline baselines/native-full.tsv artifacts/coverage/latest.tsv 2>&1 | tail -1
./scripts/coverage-baseline-diff --full --no-cause --baseline baselines/negative-full.tsv artifacts/coverage/negative-latest.tsv 2>&1 | tail -1
./scripts/coverage-cause --unclassified artifacts/coverage/latest.tsv 2>&1 | tail -1
echo "  manifest sha: meta $(awk -F'\t' '$1=="manifest_sha256"{print substr($2,1,12)}' artifacts/coverage/latest.meta.tsv) current $(./scripts/coverage-manifest | sha256sum | cut -c1-12); recorded at $(awk -F'\t' '$1=="git_commit"{print substr($2,1,8)}' artifacts/coverage/latest.meta.tsv) dirty=$(awk -F'\t' '$1=="git_dirty"{print $2}' artifacts/coverage/latest.meta.tsv)"
./scripts/check-bugs.sh 2>&1 | head -1
