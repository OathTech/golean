#!/usr/bin/env bash
# run-tsan.sh — build the probe binary with -race and run every subject
# N times at GOMAXPROCS 1 and 8; print per-subject RACE/green/other
# counts. Repo-relative; writes ONLY under $OUT (default: the evidence
# dir's tsan-runs/). Usage: docs/evidence/2026-09-03_atomics-w1/probes/run-tsan.sh [N]
set -uo pipefail
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd -P)"
N="${1:-20}"
DIR=docs/evidence/2026-09-03_atomics-w1/probes
OUT="${OUT:-$DIR/tsan-runs}"
mkdir -p "$OUT"
export GOCACHE="${GOCACHE:-${TMPDIR:-/tmp}/atomics-w1-gocache}"
export GO111MODULE=off
go build -race -o "$OUT/probe.race" "./$DIR/tsan" || { echo "build -race failed" >&2; exit 1; }
go version | tee "$OUT/go-version.txt"
subjects="${SUBJECTS:-contend plainWriteVsAdd plainReadVsLoad plainReadVsFailedCas publish casSpinPublish rmwPublish storeOverwrite plainThenStoreVsAdd plainThenStoreVsLoad plainThenStoreVsLateAdd plainThenStoreVsLateLoad nilAddress structCopyVsTypedAdd typedSiblingField}"
SUMMARY="${SUMMARY:-$OUT/summary.tsv}"
printf 'subject\tprocs\truns\trace\tgreen\tother\n' | tee "$SUMMARY"
for s in $subjects; do
  for procs in 1 8; do
    race=0; green=0; other=0
    for i in $(seq 1 "$N"); do
      out="$(GOMAXPROCS=$procs timeout 20 "$OUT/probe.race" "$s" 2>&1)"; rc=$?
      if grep -q "WARNING: DATA RACE" <<<"$out"; then race=$((race+1))
      elif [ $rc -eq 0 ] || grep -q "^recovered: true" <<<"$out"; then green=$((green+1))
      else other=$((other+1)); fi
      [ $i -eq 1 ] && printf '%s\n' "$out" > "$OUT/$s.procs$procs.first.txt"
    done
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$s" "$procs" "$N" "$race" "$green" "$other" | tee -a "$SUMMARY"
  done
done
