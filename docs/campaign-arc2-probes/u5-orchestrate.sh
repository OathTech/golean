#!/usr/bin/env bash
# u5-orchestrate.sh emit|wave — the U5 staged assembly driver (memo §6.8).
# This Lake (5.0.0) has no jobs flag, so concurrency = BATCHING: each capped
# lake invocation gets exactly BATCH targets (lake parallelizes within the
# batch and SKIPS up-to-date modules by content hash — a finished batch
# no-ops in ~0.2 s, so the walk is resume-safe and cannot spin: it visits
# the FULL ordered list exactly once per run).
#   emit: TwinSegBase + all checkpoint groups. EMIT_BATCH (4), EMIT_CAP (30G).
#   wave: all kernel segments. WAVE_BATCH (2), WAVE_CAP (74G).
# One lake at a time (the U1 wedge rule); manifest recomputed after every
# batch (= the per-wave checkpoint). A failing batch stops the walk with an
# honest rc — the manifest shows exactly what survived.
set -u
cd "$(dirname "$0")/../../proofs" || exit 9
MANI=../docs/campaign-arc2-probes/u5-manifest.sh
SRC=GoLeanProofs/Specs
all_mods() { # $1 = subdir
  for f in "$SRC/$1"/*.lean; do
    basename "$f" .lean
  done | sort | sed "s/^/GoLeanProofs.Specs.$1./"
}
run_batches() { # $1 subdir, $2 batch, $3 cap
  mapfile -t mods < <(all_mods "$1")
  local n=${#mods[@]} i=0
  while [ $i -lt $n ]; do
    batch=("${mods[@]:$i:$2}")
    echo "== batch [$i..$((i+${#batch[@]}-1))]/$n (cap $3): ${batch[*]}"
    GOLEAN_MEM_MAX="$3" ../scripts/capped lake build "${batch[@]}" >/dev/null 2>&1
    rc=$?
    "$MANI"
    if [ $rc -ne 0 ]; then
      # continue-on-failure: a hot window that OOMs a shared batch scope is
      # retried by the solo pass (wave-retry); the manifest (olean existence)
      # is the honest record of what survived. Never a silent skip: the
      # failure is logged here and the walk's exit code stays nonzero.
      echo "batch rc=$rc at [$i]: ${batch[*]} — recorded, continuing" >&2
      echo "$(date -u +%FT%TZ) rc=$rc ${batch[*]}" >> ../docs/campaign-arc2-probes/records/u5-failures.txt
      anyfail=1
    fi
    i=$((i+$2))
  done
  echo "$1: walk complete (anyfail=${anyfail:-0})"
  [ "${anyfail:-0}" = "0" ]
}
case "${1:-}" in
  emit)
    GOLEAN_MEM_MAX="${EMIT_CAP:-30G}" ../scripts/capped lake build GoLeanProofs.Specs.TwinSegBase || exit $?
    run_batches TwinCkpts "${EMIT_BATCH:-4}" "${EMIT_CAP:-30G}" ;;
  wave)
    run_batches TwinSegs "${WAVE_BATCH:-2}" "${WAVE_CAP:-74G}" ;;
  wave-retry)
    # solo pass at high cap: only missing oleans actually build (lake
    # no-ops finished modules in ~0.2 s)
    run_batches TwinSegs 1 "${RETRY_CAP:-70G}" ;;
  *) echo "usage: u5-orchestrate.sh emit|wave|wave-retry" >&2; exit 2 ;;
esac
