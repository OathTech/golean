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
echo "per-site totals before: $(grep 'consumptions per site' "$b"/../$(basename "$b").log 2>/dev/null | head -1 | cut -c1-200)"
rm -rf "$T"
exit $rc
