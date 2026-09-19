#!/usr/bin/env bash
# run-gc.sh — gc `go run -race` x5 at GOMAXPROCS 1 and 8 per scratch subject dir (the audit's run-lit.sh protocol)
set -u
cd /home/dev/projects/golean/.claude/worktrees/c1-successor
export GO111MODULE=off GOCACHE=$PWD/.tmp/fixround/gocache
echo "# gc go run -race x5 at GOMAXPROCS 1 and 8 — $(go version) — $(date -u +%FT%TZ) — GO111MODULE=off GOCACHE=.tmp/fixround/gocache"
for d in .tmp/fixround/gc/*/; do
  f=$(basename "$d"); res=""
  for procs in 1 8; do
    races=0; outs=""
    for i in 1 2 3 4 5; do
      out="$(cd "$d" && GOMAXPROCS=$procs timeout 60 go run -race . 2>&1)"; rc=$?
      if grep -q 'WARNING: DATA RACE' <<<"$out"; then races=$((races+1)); fi
      val="$(grep -v 'WARNING\|^=\|^  \|^$\|^Goroutine\|^Previous\|^Write\|^Read\|^Found\|exit status\|^main\.\|^\s' <<<"$out" | head -1)"
      outs="$outs ${val:-<none>}/rc$rc"
    done
    res="$res procs=${procs}:race=${races}/5 [$outs ]"
  done
  echo "$f:$res"
done
echo "# end $(date -u +%FT%TZ)"
