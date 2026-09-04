#!/usr/bin/env bash
# same-streams-diff.sh <before-dir> <after-dir> — compare two
# scripts/choice-trace-corpus --dump runs over the SAME stream specs
# (G-U evidence, 2026-09-04 [AGENT]). Reports:
#   (1) per-(row, stream) status + obsHash — on the SAME stream a
#       re-indexed run MAY realize a different member (that is what the
#       re-index means), so this is a REPORT, not a must: an observation
#       change here is expected only on lines listed under (3) and, for
#       strict rows, is the 3-stream invariance check's business (the gate);
#   (2) per-site consumption totals before/after (mapIter drops by the
#       number of width-1 records; every other site unchanged);
#   (3) the (row, stream) lines whose per-consumption records differ —
#       expected to be exactly: every line that had a width-1 mapIter
#       record (the record disappears) — and, among those, the lines whose
#       LATER records changed (the realization shift), which is what the
#       transformed-stream bijection (gu-bijection.py) certifies.
set -euo pipefail
B="$1"; A="$2"
tmp="$(mktemp -d)"
for d in "$B" "$A"; do
  n="$(basename "$d")"
  cat "$d"/results-*.tsv | grep -v '^id	' | awk -F'\t' '{print $1"\t"$2"\t"$3"\t"$14}' | sort > "$tmp/$n.res"
  cat "$d"/dump-*.tsv | grep -v '^id	' | sort > "$tmp/$n.dump"
done
bn="$(basename "$B")"; an="$(basename "$A")"
echo "== (1) status + obsHash per (row, stream)"
if cmp -s "$tmp/$bn.res" "$tmp/$an.res"; then
  echo "IDENTICAL on $(wc -l < "$tmp/$bn.res") (row, stream) lines"
else
  echo "DIFFERENT (lines: before < > after):"; { diff "$tmp/$bn.res" "$tmp/$an.res" || true; } | head -40
fi
echo "== (2) per-site totals"
for d in "$bn" "$an"; do
  printf '%s: ' "$d"; awk -F'\t' '{c[$5]++} END{for(k in c) printf "%s=%d ", k, c[k]; print ""}' "$tmp/$d.dump"
done
echo "== (3) records"
echo "before records: $(wc -l < "$tmp/$bn.dump")  after records: $(wc -l < "$tmp/$an.dump")"
echo "width-1 mapIter records before: $(awk -F'\t' '$5=="mapIter" && $6=="1"' "$tmp/$bn.dump" | wc -l)   after: $(awk -F'\t' '$5=="mapIter" && $6=="1"' "$tmp/$an.dump" | wc -l)"
# per (row, stream) record-sequence hashes
for d in "$bn" "$an"; do
  awk -F'\t' '{print $1"\t"$2"\t"$3"\t"$4"\t"$5"\t"$6"\t"$7"\t"$8}' "$tmp/$d.dump" | sort -t$'\t' -k1,2 -k3,3n | awk -F'\t' '{k=$1"\t"$2; s[k]=s[k]"|"$4","$5","$6","$7","$8} END{for(k in s) print k"\t"s[k]}' | sort > "$tmp/$d.seq"
done
# outer join: a (row, stream) whose ONLY record was a width-1 mapIter draw
# has no line at all after — it must still count as changed
join -t$'\t' -a1 -a2 -e '' -o 0,1.2,2.2 <(awk -F'\t' '{print $1"\x01"$2"\t"$3}' "$tmp/$bn.seq" | sort) <(awk -F'\t' '{print $1"\x01"$2"\t"$3}' "$tmp/$an.seq" | sort) | awk -F'\t' '$2!=$3 {print $1}' | tr '\001' '\t' | sort > "$tmp/changed"
echo "(row, stream) lines whose record sequence changed: $(wc -l < "$tmp/changed")"
echo "  of which on the default (empty) stream: $(awk -F'\t' '$2=="default"' "$tmp/changed" | wc -l)"
# lines with a width-1 mapIter record before (the record disappears) — must equal the changed set
awk -F'\t' '$5=="mapIter" && $6=="1" {print $1"\t"$2}' "$tmp/$bn.dump" | sort -u > "$tmp/had-w1"
echo "(row, stream) lines that HAD a width-1 mapIter record: $(wc -l < "$tmp/had-w1")"
if cmp -s "$tmp/changed" "$tmp/had-w1"; then echo "changed set == had-width-1 set: YES"; else echo "changed set == had-width-1 set: NO"; comm -3 "$tmp/changed" "$tmp/had-w1" | head; fi
echo "(scratch: $tmp)"
