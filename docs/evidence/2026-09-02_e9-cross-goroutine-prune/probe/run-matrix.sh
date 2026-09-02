#!/usr/bin/env bash
# Producer: docs/evidence/2026-09-02_e9-cross-goroutine-prune/probe/run-matrix.sh
# Runs from the repo root; builds the probe in a gitignored scratch module.
set -euo pipefail
EV=docs/evidence/2026-09-02_e9-cross-goroutine-prune
SCR=.tmp/e9probe-run; rm -rf "$SCR"; mkdir -p "$SCR"
cp "$EV/probe/main.go" "$SCR/main.go"; printf 'module e9probe\n\ngo 1.26\n' > "$SCR/go.mod"
( cd "$SCR" && go build -o probe . && go build -race -o probe-race . )
{
  echo "# producer: $EV/probe/run-matrix.sh (in-process trials; one make(map) per trial)"
  go version
  for p in 1 8; do for sz in 3 8 100 1000; do GOMAXPROCS=$p "$SCR/probe" drf 20000 $sz; done; done
} > "$EV/gc-drf-inprocess.txt"
{
  echo "# producer: $EV/probe/run-matrix.sh (intervening fresh-insert sweep, size 3 and size 8)"
  go version
  for p in 1 8; do for f in 0 1 2 3 4 5 8; do GOMAXPROCS=$p "$SCR/probe" grow 20000 3 $f; done; done
  for p in 1 8; do for f in 0 1 3 8; do GOMAXPROCS=$p "$SCR/probe" grow 20000 8 $f; done; done
} > "$EV/gc-insert-sweep.txt"
{
  echo "# producer: $EV/probe/run-matrix.sh (one fresh process per trial, 300 per GOMAXPROCS; output lines counted)"
  go version
  for p in 1 8; do for i in $(seq 1 300); do GOMAXPROCS=$p "$SCR/probe" drf 1 3; done | sort | uniq -c; done
  for p in 1 8; do for i in $(seq 1 300); do GOMAXPROCS=$p "$SCR/probe" grow 1 3 1; done | sort | uniq -c; done
} > "$EV/gc-fresh-process.txt"
{
  echo "# producer: $EV/probe/run-matrix.sh (-race legs: DRF shapes must be green, the racy control red)"
  go version
  set +e
  GOMAXPROCS=8 "$SCR/probe-race" drf 200 3; echo "drf -race exit=$?"
  GOMAXPROCS=8 "$SCR/probe-race" grow 200 3 1; echo "grow(1 insert) -race exit=$?"
  GOMAXPROCS=8 "$SCR/probe-race" racy 20 3 2>&1 | grep -E "WARNING: DATA RACE|mode=|Found" | head -3; echo "racy -race exit=${PIPESTATUS[0]}"
} > "$EV/gc-race-legs.txt" 2>&1
echo done
