#!/usr/bin/env bash
# probe.sh <pkgdir> <status> <fn>... — census line, canonical run, enumerated set (tip frontend + tip binary)
set -uo pipefail
cd /home/dev/projects/golean/.claude/worktrees/audit-unseq-stage-e5
FE=${FE:-.tmp/nativefrontend-tip}; G=${G:-.lake/build/bin/golean}
d="$1"; st="$2"; shift 2
w=".tmp/wires/$(basename "$d").$(basename "$FE").json"
"$FE" --dir "$d" --out "$w" 2>&1 | head -3 || echo "EXPORT FAILED"
"$FE" --unseq-census --dir "$d" 2>/dev/null > "$w.census"
for fn in "$@"; do
  echo "=== $fn"
  awk -F'\t' -v f="$fn" '$4==f && $6=="unseq" {print "  CENSUS unseq form=" $5 " events=" $7 " calls=" $8 " nonEvents=" $9} $4==f && $6=="legacy" && $10!~/^no call occurrence/ {print "  CENSUS legacy form=" $5 " reason=" $10}' "$w.census"
  out=$("$G" native-json-run --input "$w" --function "$fn" 2>&1); echo "  CANON exit=$? $(echo "$out" | tr '\n' ' ' | cut -c1-300)"
  out=$("$G" coverage-observations --input "$w" --function "$fn" --max-width 6 --max-sites 32 --cap 128 --work-cap 400000 --expect-status "$st" 2>&1); rc=$?
  echo "$out" | grep -v '^{' | sed 's/^/  SET /' | cut -c1-300
  echo "$out" | grep '^{' | sort -u | sed 's/^/  MEMBER /' | cut -c1-300
  echo "  SET exit=$rc"
done
