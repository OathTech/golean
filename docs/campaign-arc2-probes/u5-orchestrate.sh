#!/usr/bin/env bash
# u5-orchestrate.sh emit|wave — the U5 staged assembly driver (memo §6.8).
# This Lake (5.0.0) has no jobs flag, so concurrency = BATCHING: each capped
# lake invocation gets exactly BATCH pending targets (lake parallelizes
# within the batch; deps like checkpoint groups build first inside it).
#   emit: TwinSegBase + all checkpoint groups. EMIT_BATCH (4), EMIT_CAP (28G).
#   wave: all kernel segments. WAVE_BATCH (2), WAVE_CAP (74G).
# One lake at a time (the U1 wedge rule); manifest recomputed after every
# batch — that IS the per-wave checkpoint. Resumable: rerun; fresh oleans
# are skipped when selecting pending targets.
set -u
cd "$(dirname "$0")/../../proofs" || exit 9
MANI=../docs/campaign-arc2-probes/u5-manifest.sh
SRC=GoLeanProofs/Specs
OL=.lake/build/lib/lean/GoLeanProofs/Specs
pending() { # $1 = subdir
  for f in "$SRC/$1"/*.lean; do
    b=$(basename "$f" .lean)
    o="$OL/$1/$b.olean"
    if ! { [ -f "$o" ] && [ "$o" -nt "$f" ]; }; then echo "GoLeanProofs.Specs.$1.$b"; fi
  done
}
run_batches() { # $1 subdir, $2 batch, $3 cap
  while :; do
    mapfile -t todo < <(pending "$1")
    [ ${#todo[@]} -eq 0 ] && { echo "$1: all done"; break; }
    batch=("${todo[@]:0:$2}")
    echo "== batch (${#batch[@]} of ${#todo[@]} pending, cap $3): ${batch[*]}"
    GOLEAN_MEM_MAX="$3" ../scripts/capped lake build "${batch[@]}"
    rc=$?
    "$MANI"
    if [ $rc -ne 0 ]; then
      echo "batch rc=$rc — kill point recorded in manifest; continuing with next batch" >&2
      # a failing batch would repeat forever if its targets stay pending; stop
      # instead and let the operator/agent inspect (honest stop, not a skip)
      return $rc
    fi
  done
}
case "${1:-}" in
  emit)
    GOLEAN_MEM_MAX="${EMIT_CAP:-28G}" ../scripts/capped lake build GoLeanProofs.Specs.TwinSegBase || exit $?
    run_batches TwinCkpts "${EMIT_BATCH:-4}" "${EMIT_CAP:-28G}" ;;
  wave)
    run_batches TwinSegs "${WAVE_BATCH:-2}" "${WAVE_CAP:-74G}" ;;
  *) echo "usage: u5-orchestrate.sh emit|wave" >&2; exit 2 ;;
esac
