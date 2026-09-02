#!/usr/bin/env bash
# Consistency between the canonical fidelity-bug index (docs/BUGS.md) and the
# recorded differential baseline (baselines/native-full.tsv), so a known bug can
# neither rot in prose nor silently outlive its evidence (mechanism adapted from
# ACL2Lean's check-bugs.sh). Static, no build.
#
#   (1) every `- Cases:` id of an open Pinned-by:differential bug exists in the
#       baseline AND is currently FAIL (a PASSing pinned case = fixed-not-closed);
#       every `- Cases:` id of a Pinned-by:none bug EXISTS in the baseline
#       (existence only — none-entries mix red-by-design pins with flip-record
#       rows, so no direction is derivable; audit fix round 2026-09-01) —
#       UNLESS the entry carries an optional `- Expect: FAIL` line (q-u4-gomem
#       audit fix F4, 2026-09-02): then every listed id must ALSO be FAIL, so a
#       red-by-design pin that silently turns PASS (a refusal that stopped
#       firing) trips the gate instead of laundering through the existence check.
#       `Expect:` accepts only FAIL; any other token fails closed (0).
#   Paths are overridable for fixture tests ONLY (scripts/test-lane-validation
#   Part A3): CHECK_BUGS_BUGS / CHECK_BUGS_BASELINE / CHECK_BUGS_IDS /
#   CHECK_BUGS_CEIL. Unset = the tracked files.
#   (2) every open Pinned-by:differential bug lists >=1 case;
#   (3) SYMMETRIC: every `Status: fixed` differential bug's cases must now PASS
#       (marking a bug fixed while its cases still fail is laundering);
#   (4) RATCHET: the count of unexplained baseline fidelity failures (stage
#       lean-observation / differential / membership / confluent / racy / nondet, in no bug's Cases) must not EXCEED the
#       recorded ceiling in baselines/untriaged-count — a new bug cannot hide in
#       the pile, and deleting a BUG entry raises the count and trips this.
#       When the count drops, lower the ceiling in the same commit (the check
#       says so). Below the ceiling it reports the remainder as the backlog.
#       Since 2026-08-20 the ratchet is PER DISPOSITION CLASS — see the
#       disposition block below check (3) for what the classes mean and why
#       one scalar was dishonest.
#
#   scripts/check-bugs.sh --list   print that untriaged surface (id + stage),
#                                  the concrete backlog to triage into BUGS.md.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
LIST=0; [ "${1:-}" = "--list" ] && LIST=1

BUGS=${CHECK_BUGS_BUGS:-docs/BUGS.md}
BASELINE=${CHECK_BUGS_BASELINE:-baselines/native-full.tsv}
[ -f "$BUGS" ]     || { echo "check-bugs: no $BUGS" >&2; exit 2; }
[ -f "$BASELINE" ] || { echo "check-bugs: no $BASELINE" >&2; exit 2; }
fail=0

# Baseline lookup: id -> "RESULT/stage".
blk() { awk -F'\t' -v id="$1" '!/^#/ && $2==id {print $1"/"$3; found=1} END{exit !found}' "$BASELINE"; }

# Parse BUGS.md into: per open+differential bug, its id and Cases line.
# Emit "BUG-NNN|status|pinned|expect|case,case,..." per bug.
bugs="$(awk '
  /^## BUG-/       { if (id) print id"|"st"|"pb"|"ex"|"cs; id=$2; st=""; pb=""; ex=""; cs="" }
  /^- Status:/     { st=$3 }
  /^- Pinned-by:/  { pb=$3 }
  /^- Expect:/     { ex=$3 }
  /^- Cases:/      { sub(/^- Cases:[ ]*/,""); gsub(/[ ]/,""); cs=$0 }
  END { if (id) print id"|"st"|"pb"|"ex"|"cs }
' "$BUGS")"

declared_cases=""   # accumulate all cases named by any bug (for the ratchet)
nbugs=0
while IFS='|' read -r id st pb ex cs; do
  [ -z "${id:-}" ] && continue
  nbugs=$((nbugs+1))
  # Optional `- Expect:` (audit fix F4): FAIL is the only recognized value.
  if [ -n "$ex" ] && [ "$ex" != FAIL ]; then
    echo "FAIL (0): $id has unrecognized 'Expect: $ex' (must be FAIL, or omit the line)"; fail=1; continue
  fi
  # Fail closed on an unparseable status: a token this parser does not
  # recognize silently exempts the bug from every check below (the 2026-07-25
  # pre-merge audit caught exactly that — BUG-001 closed as '**CLOSED ...**'
  # disarmed all three case pins).
  if [ "$st" != open ] && [ "$st" != fixed ]; then
    echo "FAIL (0): $id has unrecognized 'Status: $st' (must be open|fixed)"; fail=1; continue
  fi
  # Same fail-closed rule for the sibling field (launch audit D6-F1,
  # 2026-08-22): a typo'd or case-variant Pinned-by silently exempted
  # the entry from checks (1)-(3) — the exact hole the Status guard
  # above closed on 2026-07-25.
  if [ "$pb" != differential ] && [ "$pb" != none ]; then
    echo "FAIL (0): $id has unrecognized 'Pinned-by: $pb' (must be differential|none)"; fail=1; continue
  fi
  # Pinned-by:none entries with a Cases line (audit fix round
  # 2026-09-01): previously UNENFORCED — a none-entry's Cases id could
  # dangle after a baseline row removal with nothing red (the
  # unsafe/boundary/sizeof-const dangle). EXISTENCE is now verified for
  # every listed id; the FAIL/PASS direction is NOT, because
  # none-entries' Cases lines mix red-by-design refusal pins (FAIL by
  # design under a FIXED status) with flip-record rows, so the
  # direction is not derivable from Status the way it is for
  # differential pins. [AGENT] A row a none-entry names must exist; a
  # removed row is named in the entry's prose instead.
  if [ "$pb" = none ]; then
    IFS=',' read -r -a arr <<< "$cs"
    for c in "${arr[@]}"; do
      [ -z "$c" ] && continue
      declared_cases="$declared_cases $c"
      if ! res="$(blk "$c")"; then
        echo "FAIL (1): $id case '$c' not found in $BASELINE (Pinned-by:none Cases ids must name live rows — record removals in prose, not on the Cases line)"; fail=1
      elif [ "$ex" = FAIL ] && [ "${res%%/*}" != FAIL ]; then
        echo "FAIL (5): $id declares 'Expect: FAIL' but case '$c' is $res in baseline — a red-by-design pin turned green: the refusal stopped firing, or the row no longer pins it"; fail=1
      fi
    done
    continue
  fi
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

# ---------------------------------------------------------------------------
# THE DISPOSITION COLUMN (2026-08-20; coverage-ledger T-5, triage-table §5).
#
# Every tracked row in baselines/untriaged-ids is `<id><TAB><disposition>`,
# disposition one of:
#
#   coverage     the machine or frontend REFUSES a construct it does not model
#                (a fail-closed .unsupported / stuck at a fidelity stage).
#                Never a wrong answer. Retires only when the feature lands.
#   latitude     a spec-open point the machine declines to pick a member of,
#                or holds a different conforming member at. Retires by an
#                ENVELOPE (membership), never by "a fix".
#   wrong-answer a machine-vs-Go divergence at a FORCED point that no
#                docs/BUGS.md entry yet explains. THE class this ratchet
#                exists to drive to zero.
#
# Why the split: the old single count mixed all three, so rows that can never
# retire by being fixed sat inside a number captioned "ratchet toward 0" —
# unreachable by construction — while a real wrong answer could enter behind a
# frontier refusal that left, with the scalar unmoved. Ceilings are per class,
# so any rise of `wrong-answer` above 0 requires an explicit reviewable
# two-file edit (an untriaged-ids row + the untriaged-count ceiling, justified
# in the same commit), independent of frontier churn — an honest speedbump,
# not an unraisable floor.
#
# Fail-closed everywhere: an unexplained id with no VALID tracked disposition
# buckets as `unclassified` and fails; a malformed or duplicated tracked line
# fails; a ceiling file missing a class, naming an unknown class, duplicating
# one, or carrying a non-number fails. The buckets must also sum back to the
# total — the split may never lose a row.
# ---------------------------------------------------------------------------
DISPOSITIONS='coverage latitude wrong-answer'
IDS_FILE=${CHECK_BUGS_IDS:-baselines/untriaged-ids}
CEIL_FILE=${CHECK_BUGS_CEIL:-baselines/untriaged-count}

current_ids="$(printf '%s\n' "$unexplained" | cut -f1 | grep . | sort || true)"
tracked_ids=""      # first field of every non-comment line (the 4b set)
tracked_pairs=""    # only the lines that PARSE (the disposition source)
ceil_rows=""        # set below; referenced by the summary, which only runs green

if [ ! -f "$IDS_FILE" ]; then
  echo "FAIL (4b): missing $IDS_FILE (the tracked untriaged id set) — create it with one '<id><TAB><disposition>' line per id from 'scripts/check-bugs.sh --list' (disposition one of: $DISPOSITIONS)"
  fail=1
else
  ids_rows="$(grep -vE '^#' "$IDS_FILE" | grep . || true)"
  tracked_ids="$(printf '%s\n' "$ids_rows" | cut -f1 | grep . | sort || true)"
  bad_rows="$(printf '%s\n' "$ids_rows" | grep . | awk -F'\t' -v OK="$DISPOSITIONS" '
    BEGIN { n=split(OK,a," "); for(i=1;i<=n;i++) ok[a[i]]=1 }
    NF!=2 || $1=="" || !($2 in ok) { print }' || true)"
  if [ -n "$bad_rows" ]; then
    echo "FAIL (4b): malformed row(s) in $IDS_FILE — every tracked row is '<id><TAB><disposition>' with disposition one of: $DISPOSITIONS"
    printf '%s\n' "$bad_rows" | sed 's/^/  /'
    fail=1
  fi
  dup_rows="$(printf '%s\n' "$tracked_ids" | grep . | uniq -d || true)"
  if [ -n "$dup_rows" ]; then
    echo "FAIL (4b): duplicate id(s) in $IDS_FILE — a second row would silently shadow the first's disposition:"
    printf '%s\n' "$dup_rows" | sed 's/^/  /'
    fail=1
  fi
  tracked_pairs="$(printf '%s\n' "$ids_rows" | grep . | awk -F'\t' -v OK="$DISPOSITIONS" '
    BEGIN { n=split(OK,a," "); for(i=1;i<=n;i++) ok[a[i]]=1 }
    NF==2 && $1!="" && ($2 in ok) { print }' || true)"
fi

# (4) The ratchet, per disposition class. Bucket the CURRENT unexplained ids
#     by their tracked disposition; anything without one is `unclassified`.
declare -A cnt
for d in $DISPOSITIONS unclassified; do cnt[$d]=0; done
unclassified_ids=""
while read -r uid; do
  [ -z "$uid" ] && continue
  d="$(printf '%s\n' "$tracked_pairs" | awk -F'\t' -v i="$uid" '$1==i {print $2; exit}')"
  if [ -z "$d" ]; then d=unclassified; unclassified_ids="$unclassified_ids$uid"$'\n'; fi
  cnt[$d]=$(( ${cnt[$d]} + 1 ))
done <<< "$current_ids"

bsum=0
for d in $DISPOSITIONS unclassified; do bsum=$(( bsum + ${cnt[$d]} )); done
if [ "$bsum" -ne "$nun" ]; then
  echo "FAIL (4): disposition buckets sum to $bsum but there are $nun unexplained fidelity failure(s) — the split lost a row"
  fail=1
fi
if [ "${cnt[unclassified]}" -gt 0 ]; then
  echo "FAIL (4): ${cnt[unclassified]} unexplained fidelity failure(s) carry no valid disposition in $IDS_FILE — classify each as one of: $DISPOSITIONS (fail closed; an unclassified row is never counted as harmless):"
  printf '%s' "$unclassified_ids" | sed 's/^/  /'
  fail=1
fi

if [ ! -f "$CEIL_FILE" ]; then
  echo "FAIL (4): missing $CEIL_FILE (the per-class untriaged ceilings) — create it with one '<class> <n>' line per class: $DISPOSITIONS"
  fail=1
else
  ceil_rows="$(grep -vE '^#' "$CEIL_FILE" | grep . || true)"
  bad_ceil="$(printf '%s\n' "$ceil_rows" | grep . | awk -v OK="$DISPOSITIONS" '
    BEGIN { n=split(OK,a," "); for(i=1;i<=n;i++) ok[a[i]]=1 }
    NF!=2 || !($1 in ok) || $2 !~ /^[0-9]+$/ { print }' || true)"
  if [ -n "$bad_ceil" ]; then
    echo "FAIL (4): malformed ceiling row(s) in $CEIL_FILE — every row is '<class> <n>' with class one of: $DISPOSITIONS"
    printf '%s\n' "$bad_ceil" | sed 's/^/  /'
    fail=1
  fi
  dup_ceil="$(printf '%s\n' "$ceil_rows" | grep . | awk '{print $1}' | sort | uniq -d || true)"
  if [ -n "$dup_ceil" ]; then
    echo "FAIL (4): duplicate ceiling row(s) in $CEIL_FILE (the second would be ignored): $dup_ceil"
    fail=1
  fi
  for d in $DISPOSITIONS; do
    c="$(printf '%s\n' "$ceil_rows" | awk -v k="$d" '$1==k {print $2; exit}')"
    if [ -z "$c" ]; then
      echo "FAIL (4): $CEIL_FILE has no ceiling row for class '$d' — every class carries its own ceiling"
      fail=1; continue
    fi
    if [ "${cnt[$d]}" -gt "$c" ]; then
      echo "FAIL (4): unexplained '$d' fidelity failures rose ${c} -> ${cnt[$d]} — triage the new id(s) into docs/BUGS.md ('scripts/check-bugs.sh --list') or, if genuinely pre-existing, raise the '$d' row in $CEIL_FILE with justification in the same commit."
      fail=1
    fi
  done
fi

# (4b) The SET ratchet: the count alone launders equal-sized swaps (N fixed
# + N new wrong answers = same count; pre-merge audit 2026-07-26). The
# untriaged IDs are tracked; a NEW entrant fails until it is triaged into
# docs/BUGS.md or added to the tracked set with in-file justification, and
# a departed id must be removed in the same commit (a stale entry would
# re-admit a regression silently).
if [ -f "$IDS_FILE" ]; then   # its absence already FAILed (4b) above
  # -u on the tracked side: a duplicated row is already reported by the
  # dup check above, and letting the extra copy fall out of `comm -23` here
  # would report it a second time as a phantom "no longer failing" id.
  tracked_ids_u="$(printf '%s\n' "$tracked_ids" | sort -u || true)"
  new_ids="$(comm -13 <(printf '%s\n' "$tracked_ids_u") <(printf '%s\n' "$current_ids") || true)"
  gone_ids="$(comm -23 <(printf '%s\n' "$tracked_ids_u") <(printf '%s\n' "$current_ids") || true)"
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
fi

if [ "$fail" -ne 0 ]; then echo "check-bugs: FAIL"; exit 1; fi
echo "check-bugs: ok ($nbugs bug(s); pinned cases behave as claimed)"
if [ "$nun" -gt 0 ]; then
  line=""
  for d in $DISPOSITIONS; do
    c="$(printf '%s\n' "$ceil_rows" | awk -v k="$d" '$1==k {print $2; exit}')"
    line="$line $d ${cnt[$d]}/$c;"
  done
  echo "check-bugs: backlog — $nun unexplained fidelity failure(s):${line%;} ('scripts/check-bugs.sh --list')"
  echo "check-bugs: 'wrong-answer' is the class that ratchets toward 0; 'coverage' retires when the feature lands and 'latitude' only by an envelope."
  for d in $DISPOSITIONS; do
    c="$(printf '%s\n' "$ceil_rows" | awk -v k="$d" '$1==k {print $2; exit}')"
    if [ "${cnt[$d]}" -lt "$c" ]; then
      echo "check-bugs: '$d' ceiling is $c but count is ${cnt[$d]} — lower it in $CEIL_FILE in this commit (ratchet down)"
    fi
  done
fi
