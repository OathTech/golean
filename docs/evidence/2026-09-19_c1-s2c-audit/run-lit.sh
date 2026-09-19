#!/usr/bin/env bash
# run-lit.sh <batchdir> <func>... : gc -race x5 at GOMAXPROCS 1 and 8; candidate + main binaries; candidate enumerator
set -u
ROOT=/home/dev/projects/golean/.claude/worktrees/audit-c1-s2c
cd "$ROOT"
export GO111MODULE=off GOCACHE=$ROOT/.tmp/gocache
BATCH="$1"; shift
WIRE="$BATCH/batch.wire.json"
if [[ ! -f "$WIRE" ]]; then
  go run ./tools/nativefrontend --dir "$BATCH" --out "$WIRE" > "$BATCH/frontend.log" 2>&1; echo "frontend EXIT=$? ($(tail -1 "$BATCH/frontend.log" | cut -c1-200))"
fi
for f in "$@"; do
  d="$BATCH/gc/$f"; mkdir -p "$d"; cp "$BATCH/funcs.go" "$d/"
  printf 'package main\n\nfunc main() {\n\tprintln(%s())\n}\n' "$f" > "$d/main.go"
  gcres=""
  for procs in 1 8; do
    races=0; outs=""
    for i in 1 2 3 4 5; do
      out="$(cd "$d" && GOMAXPROCS=$procs timeout 60 go run -race . 2>&1)"; rc=$?
      if grep -q 'WARNING: DATA RACE' <<<"$out"; then races=$((races+1)); fi
      val="$(grep -v 'WARNING\|^=\|^  \|^$\|^Goroutine\|^Previous\|^Write\|^Read\|^Found\|exit status\|^main\.\|^\s' <<<"$out" | head -1)"
      outs="$outs $val/rc$rc"
    done
    gcres="$gcres procs=$procs:race=$races/5 [$outs ]"
  done
  cand="$(.lake/build/bin/golean native-json-run --input "$WIRE" --function "$f" 2>&1)"; crc=$?
  mainb="$(.tmp/golean-main native-json-run --input "$WIRE" --function "$f" 2>&1)"; mrc=$?
  enum="$(.lake/build/bin/golean coverage-observations --input "$WIRE" --function "$f" --max-width 4 --max-sites ${SITES:-16} --cap 64 --work-cap 200000 2>&1 | tr '\n' ' ' | cut -c1-400)"
  echo "=== $f"
  echo "  gc:  $gcres"
  echo "  cand(rc=$crc): $cand"
  echo "  main(rc=$mrc): $mainb"
  echo "  cand-enum: $enum"
done
