#!/usr/bin/env bash
# run-tsan.sh — build the Q-TRYLOCK probe binary plain AND with -race, run
# every subject N times at GOMAXPROCS 1 and 8; per subject: RACE / green /
# other counts and the distinct plain outputs. Repo-relative; writes ONLY
# under $OUT (default: the evidence dir's tsan-runs/); the binaries live
# outside the evidence dir. Usage:
#   docs/evidence/2026-09-03_q-trylock/probes/run-tsan.sh [N]
set -uo pipefail
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd -P)"
N="${1:-20}"
DIR=docs/evidence/2026-09-03_q-trylock/probes
OUT="${OUT:-$DIR/tsan-runs}"
mkdir -p "$OUT"
export GOCACHE="${GOCACHE:-${TMPDIR:-/tmp}/q-trylock-gocache}"
export GO111MODULE=off
BIN="${TMPDIR:-/tmp}/q-trylock-probe"
go build -o "$BIN" "./$DIR/tsan" || { echo "build failed" >&2; exit 1; }
go build -race -o "$BIN.race" "./$DIR/tsan" || { echo "build -race failed" >&2; exit 1; }
go version | tee "$OUT/go-version.txt"
subjects="${SUBJECTS:-muUncontended muLocked muUnlockAfterTryLock muFalseThenLock muSpinUntilTryLock muOverwriteVsTryLock muOverwriteVsFailedTryLock muOverwriteLockedVsFailedTryLock muCopyVsFailedTryLock muDrfTryLockPublish muRacyTryLockNoAcquire muFailedTryLockNoEdge rwMatrix rwTryRLockPendingWriter rwTryRLockQueuedWriter rwRLockQueuedWriter rwOverwriteVsTryRLock rwOverwriteVsFailedTryRLock rwDrfTryLockPublish rwDrfTryRLockAcquire}"
SUMMARY="${SUMMARY:-$OUT/summary.tsv}"
printf 'subject\tbuild\tprocs\truns\trace\tgreen\tother\tdistinct_outputs\n' | tee "$SUMMARY"
for s in $subjects; do
  for build in plain race; do
    bin="$BIN"; [ "$build" = race ] && bin="$BIN.race"
    for procs in 1 8; do
      race=0; green=0; other=0; : > "$OUT/$s.$build.procs$procs.outs"
      for i in $(seq 1 "$N"); do
        out="$(GOMAXPROCS=$procs timeout 20 "$bin" "$s" 2>&1)"; rc=$?
        if grep -q "WARNING: DATA RACE" <<<"$out"; then race=$((race+1))
        elif [ $rc -eq 0 ]; then green=$((green+1)); printf '%s\n' "$out" >> "$OUT/$s.$build.procs$procs.outs"
        else other=$((other+1)); fi
        [ $i -eq 1 ] && printf '%s\n' "$out" > "$OUT/$s.$build.procs$procs.first.txt"
      done
      d="$(sort -u "$OUT/$s.$build.procs$procs.outs" | tr '\n' ';')"
      printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$s" "$build" "$procs" "$N" "$race" "$green" "$other" "$d" | tee -a "$SUMMARY"
    done
  done
done
