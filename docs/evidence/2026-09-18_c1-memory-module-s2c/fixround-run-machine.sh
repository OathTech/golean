#!/usr/bin/env bash
# run-machine.sh <out> <pkg>:<subject>:<sites>... — candidate + main binaries on the default stream; candidate + main enumerators at the row params (no --expect-status: every member's status visible)
set -u
cd /home/dev/projects/golean/.claude/worktrees/c1-successor
OUT="$1"; shift
CAND=.lake/build/bin/golean; MAIN=.tmp/golean-main
{
echo "# machine side — candidate $(sha256sum $CAND | cut -c1-16)… vs main's certified binary $(sha256sum $MAIN | cut -c1-16)… (.tmp/golean-main, read-only copy) — $(date -u +%FT%TZ)"
for spec in "$@"; do
  IFS=: read -r pkg f sites <<<"$spec"
  W=.tmp/fixround/$pkg.wire.json
  echo "=== $pkg / $f (sites=$sites)"
  c="$($CAND native-json-run --input "$W" --function "$f" 2>&1)"; crc=$?
  m="$($MAIN native-json-run --input "$W" --function "$f" 2>&1)"; mrc=$?
  echo "  cand(rc=$crc): $c"
  echo "  main(rc=$mrc): $m"
  ce="$($CAND coverage-observations --input "$W" --function "$f" --max-width 4 --max-sites "$sites" --cap 64 --work-cap 200000 2>&1 | tr '\n' ' ' | cut -c1-600)"
  echo "  cand-enum: $ce"
  me="$($MAIN coverage-observations --input "$W" --function "$f" --max-width 4 --max-sites "$sites" --cap 64 --work-cap 200000 2>&1 | tr '\n' ' ' | cut -c1-600)"
  echo "  main-enum: $me"
done
echo "# end $(date -u +%FT%TZ)"
} > "$OUT" 2>&1
