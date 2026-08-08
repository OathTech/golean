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
#       lean-observation / differential / membership / confluent / racy / nondet, in no bug's Cases) must not EXCEED the
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
#     `membership` is a fidelity stage since the arc-final audit (F9,
#     2026-08-06): a membership FAIL carries fidelity meaning — most
#     importantly "Go observation is NOT in the machine's enumerated set"
#     (the too-narrow soundness alarm) and driver-coupling drift — and was
#     previously invisible to both the count ceiling and the tracked set.
#     `confluent` and `racy` joined at the channels-arc final audit (F5,
#     2026-08-07): slice 4 introduced both stages, and their FAILs are
#     exactly machine-vs-Go fidelity divergences ("the observable is NOT
#     schedule-confluent", enumerator/driver drift, "'every enumerated
#     path refuses' not certified" — the unsound-race-refusal direction),
#     yet neither was in this filter — the same hole the previous arc's
#     F9 closed for membership, reopened lane by lane. `nondet` joined at
#     the convergence check (2026-08-08): its failure text ("observation
#     varies with iteration order") fires only AFTER strict equality with
#     Go held, so it means the machine varies where the case is declared
#     deterministic — the too-wide-envelope direction, at least as
#     fidelity-bearing as confluent's machine-only alarm; the F5 fix had
#     left it out while the same diff parked the first-ever permanent
#     nondet FAIL (channels/select-select/beside-loop).
unexplained="$(awk -F'\t' -v DC="$declared_cases" '
  BEGIN { n=split(DC,a," "); for(i=1;i<=n;i++) named[a[i]]=1 }
  !/^#/ && $1=="FAIL" && ($3=="lean-observation" || $3=="differential" || $3=="membership" || $3=="confluent" || $3=="racy" || $3=="nondet") && !($2 in named) { print $2"\t"$3 }
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

# (4b) The SET ratchet: the count alone launders equal-sized swaps (N fixed
# + N new wrong answers = same count; pre-merge audit 2026-07-26). The
# untriaged IDs are tracked; a NEW entrant fails until it is triaged into
# docs/BUGS.md or added to the tracked set with in-file justification, and
# a departed id must be removed in the same commit (a stale entry would
# re-admit a regression silently).
IDS_FILE=baselines/untriaged-ids
if [ -f "$IDS_FILE" ]; then
  current_ids="$(printf '%s\n' "$unexplained" | cut -f1 | grep . | sort || true)"
  tracked_ids="$(grep -vE '^#' "$IDS_FILE" | grep . | sort || true)"
  new_ids="$(comm -13 <(printf '%s\n' "$tracked_ids") <(printf '%s\n' "$current_ids") || true)"
  gone_ids="$(comm -23 <(printf '%s\n' "$tracked_ids") <(printf '%s\n' "$current_ids") || true)"
  if [ -n "$new_ids" ]; then
    echo "FAIL (4b): NEW untriaged fidelity failure(s) not in $IDS_FILE:"
    printf '%s\n' "$new_ids" | sed 's/^/  /'
    fail=1
  fi
  if [ -n "$gone_ids" ]; then
    echo "FAIL (4b): tracked untriaged id(s) no longer failing — remove from $IDS_FILE in this commit (ratchet down):"
    printf '%s\n' "$gone_ids" | sed 's/^/  /'
    fail=1
  fi
else
  echo "FAIL (4b): missing $IDS_FILE (the tracked untriaged id set) — create it from 'scripts/check-bugs.sh --list'"
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
