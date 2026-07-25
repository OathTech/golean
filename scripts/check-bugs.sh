#!/usr/bin/env bash
# Consistency between the canonical fidelity-bug index (docs/BUGS.md) and the
# recorded differential baseline (baselines/native-full.tsv), so a known bug can
# neither rot in prose nor silently outlive its evidence (mechanism adapted from
# ACL2Lean's check-bugs.sh). Static, no build.
#
#   (1) every `- Cases:` id of an open Pinned-by:differential bug exists in the
#       baseline AND is currently FAIL (a PASSing pinned case = fixed-not-closed);
#   (2) every open Pinned-by:differential bug lists >=1 case;
#   (3) SYMMETRIC: every `Status: fixed` differential bug's cases must now PASS
#       (marking a bug fixed while its cases still fail is laundering);
#   (4) RATCHET: the count of unexplained baseline fidelity failures (stage
#       lean-observation / differential, in no bug's Cases) must not EXCEED the
#       recorded ceiling in baselines/untriaged-count — a new bug cannot hide in
#       the pile, and deleting a BUG entry raises the count and trips this.
#       When the count drops, lower the ceiling in the same commit (the check
#       says so). Below the ceiling it reports the remainder as the backlog.
#
#   scripts/check-bugs.sh --list   print that untriaged surface (id + stage),
#                                  the concrete backlog to triage into BUGS.md.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
LIST=0; [ "${1:-}" = "--list" ] && LIST=1

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

declared_cases=""   # accumulate all cases named by any bug (for the ratchet)
nbugs=0
while IFS='|' read -r id st pb cs; do
  [ -z "${id:-}" ] && continue
  nbugs=$((nbugs+1))
  # Fail closed on an unparseable status: a token this parser does not
  # recognize silently exempts the bug from every check below (the 2026-07-25
  # pre-merge audit caught exactly that — BUG-001 closed as '**CLOSED ...**'
  # disarmed all three case pins).
  if [ "$st" != open ] && [ "$st" != fixed ]; then
    echo "FAIL (0): $id has unrecognized 'Status: $st' (must be open|fixed)"; fail=1; continue
  fi
  [ "$pb" = differential ] || continue
  if [ "$st" = open ] && [ -z "$cs" ]; then
    echo "FAIL (2): $id is open+differential but lists no '- Cases:'"; fail=1; continue
  fi
  IFS=',' read -r -a arr <<< "$cs"
  for c in "${arr[@]}"; do
    [ -z "$c" ] && continue
    declared_cases="$declared_cases $c"
    if res="$(blk "$c")"; then
      case "$st/$res" in
        open/FAIL/*)  : ;;  # good: an open bug's case fails, as claimed
        open/PASS/*)  echo "FAIL (1): $id case '$c' is $res in baseline — bug fixed-not-closed, or case no longer pins it"; fail=1 ;;
        fixed/PASS/*) : ;;  # good: a fixed bug's case passes, as claimed
        fixed/FAIL/*) echo "FAIL (3): $id is marked fixed but case '$c' is still $res in baseline"; fail=1 ;;
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
  !/^#/ && $1=="FAIL" && ($3=="lean-observation" || $3=="differential") && !($2 in named) { print $2"\t"$3 }
' "$BASELINE" | sort)"
nun="$(printf '%s' "$unexplained" | grep -c . || true)"

if [ "$LIST" -eq 1 ]; then
  echo "# Untriaged fidelity failures ($nun) — baseline FAILs at a fidelity stage"
  echo "# not yet explained by a docs/BUGS.md entry. Triage each into a BUG."
  printf '%s\n' "$unexplained"
  exit 0
fi

# (4) The ratchet: unexplained count must not exceed the recorded ceiling.
CEIL_FILE=baselines/untriaged-count
if [ -f "$CEIL_FILE" ]; then
  ceil="$(grep -vE '^#' "$CEIL_FILE" | head -1 | tr -d '[:space:]')"
  if [ "$nun" -gt "$ceil" ]; then
    echo "FAIL (4): unexplained fidelity failures rose ${ceil} -> ${nun} — a new bug is hiding in the pile (or a BUG entry was deleted). Triage the new id(s) into docs/BUGS.md ('scripts/check-bugs.sh --list') or, if genuinely pre-existing, raise $CEIL_FILE with justification."
    fail=1
  fi
else
  echo "FAIL (4): missing $CEIL_FILE (the untriaged ceiling) — create it with the current count $nun"
  fail=1
fi

if [ "$fail" -ne 0 ]; then echo "check-bugs: FAIL"; exit 1; fi
echo "check-bugs: ok ($nbugs bug(s); pinned cases behave as claimed)"
if [ "$nun" -gt 0 ]; then
  echo "check-bugs: backlog — $nun/$ceil unexplained fidelity failure(s) ('scripts/check-bugs.sh --list'; ratchet toward 0)"
  if [ "$nun" -lt "$ceil" ]; then
    echo "check-bugs: ceiling is $ceil but count is $nun — lower $CEIL_FILE to $nun in this commit (ratchet down)"
  fi
fi
