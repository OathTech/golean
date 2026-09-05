#!/usr/bin/env bash
# trace-diff.sh BEFORE_DIR AFTER_DIR — compare two scripts/choice-trace-corpus
# artifact dirs row-for-row on every consumption-relevant column
# (id, stream, status, consumed, wide, exhaustedAt, wideAfterExhaustion,
# perSite, maxBound, violations, alarms, obsHash, driverAgreement).
# Exit 0 = identical multiset of (id,stream) lines; 1 = any delta (printed).
set -uo pipefail
b="$1"; a="$2"
T="$(mktemp -d "${TMPDIR:-.tmp}/tracediff.XXXXXX")"
# the ERROR column of a frontend-refusal row embeds the artifact dir path; normalize it
norm() { cat "$1"/results-*.tsv | grep -v '^id	stream' | sed 's#[^	 ]*/wire/#<out>/wire/#g' | sort; }
norm "$b" > $T/trace-before.$$; norm "$a" > $T/trace-after.$$
echo "rows before=$(wc -l < $T/trace-before.$$) after=$(wc -l < $T/trace-after.$$)"
if diff $T/trace-before.$$ $T/trace-after.$$ > $T/trace-delta.$$; then
  echo "DELTA: 0 (every (id,stream) line identical on all columns)"; rc=0
else
  echo "DELTA lines:"; cat $T/trace-delta.$$; rc=1
fi
# Per-site consumption totals of BOTH sides, untruncated (audit fix R8,
# lane c-arc-c2, 2026-09-05: the line used to print the BEFORE side only,
# cut at 200 characters). The totals live in the run log beside the
# artifact dir (`<dir>.log`); a missing log is said so, never blank.
for side in before after; do
  if [ "$side" = before ]; then d="$b"; else d="$a"; fi
  log="$d/../$(basename "$d").log"
  if [ -r "$log" ]; then
    echo "per-site totals $side: $(grep 'consumptions per site' "$log" | head -1)"
  else
    echo "per-site totals $side: (no run log at $log)"
  fi
done
rm -rf "$T"
exit $rc
