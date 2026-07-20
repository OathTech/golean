#!/usr/bin/env bash
# Consistency between the canonical fidelity-bug index (docs/BUGS.md) and the
# recorded differential baseline (baselines/native-full.tsv), so a known bug can
# neither rot in prose nor silently outlive its evidence (mechanism adapted from
# ACL2Lean's check-bugs.sh). Static, no build.
#
#   (1) every `- Cases:` id of an open Pinned-by:differential bug exists in the
#       baseline AND is currently FAIL (a PASSing pinned case = fixed-not-closed);
#   (2) every open Pinned-by:differential bug lists >=1 case;
#   (3) WARN: how many baseline fidelity failures (stage lean-observation /
#       differential) are not yet explained by any bug's Cases (omission surface).
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

BUGS=docs/BUGS.md
BASELINE=baselines/native-full.tsv
[ -f "$BUGS" ]     || { echo "check-bugs: no $BUGS" >&2; exit 2; }
[ -f "$BASELINE" ] || { echo "check-bugs: no $BASELINE" >&2; exit 2; }
fail=0

# Baseline lookup: id -> "RESULT/stage".
blk() { awk -F'\t' -v id="$1" '!/^#/ && $2==id {print $1"/"$3; found=1} END{exit !found}' "$BASELINE"; }

# Parse BUGS.md into: per open+differential bug, its id and Cases line.
# Emit "BUG-NNN|status|pinned|case,case,..." per bug.
bugs="$(awk '
  /^## BUG-/       { if (id) print id"|"st"|"pb"|"cs; id=$2; st=""; pb=""; cs="" }
  /^- Status:/     { st=$3 }
  /^- Pinned-by:/  { pb=$3 }
  /^- Cases:/      { sub(/^- Cases:[ ]*/,""); gsub(/[ ]/,""); cs=$0 }
  END { if (id) print id"|"st"|"pb"|"cs }
' "$BUGS")"

declared_cases=""   # accumulate all cases named by any bug (for the warn check)
nbugs=0
while IFS='|' read -r id st pb cs; do
  [ -z "${id:-}" ] && continue
  nbugs=$((nbugs+1))
  [ "$st" = open ] || continue
  [ "$pb" = differential ] || continue
  if [ -z "$cs" ]; then
    echo "FAIL (2): $id is open+differential but lists no '- Cases:'"; fail=1; continue
  fi
  IFS=',' read -r -a arr <<< "$cs"
  for c in "${arr[@]}"; do
    [ -z "$c" ] && continue
    declared_cases="$declared_cases $c"
    if res="$(blk "$c")"; then
      case "$res" in
        FAIL/*) : ;;  # good: the case fails, as an open bug requires
        PASS/*) echo "FAIL (1): $id case '$c' is $res in baseline — bug fixed-not-closed, or case no longer pins it"; fail=1 ;;
      esac
    else
      echo "FAIL (1): $id case '$c' not found in $BASELINE"; fail=1
    fi
  done
done <<< "$bugs"

# (3) Unexplained fidelity failures: baseline FAILs at a fidelity stage not named
#     by any bug. A warning (visible omission surface), not a hard failure.
unexplained="$(awk -F'\t' -v DC="$declared_cases" '
  BEGIN { n=split(DC,a," "); for(i=1;i<=n;i++) named[a[i]]=1 }
  !/^#/ && $1=="FAIL" && ($3=="lean-observation" || $3=="differential") && !($2 in named) { print $2 }
' "$BASELINE" | sort)"
nun="$(printf '%s' "$unexplained" | grep -c . || true)"

if [ "$fail" -ne 0 ]; then echo "check-bugs: FAIL"; exit 1; fi
echo "check-bugs: ok ($nbugs bug(s); pinned cases fail as claimed)"
if [ "$nun" -gt 0 ]; then
  echo "check-bugs: WARN — $nun baseline fidelity failure(s) not yet explained by a BUG entry (ratchet toward 0; see docs/BUGS.md)"
fi
