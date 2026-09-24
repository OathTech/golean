#!/usr/bin/env bash
# run-probe.sh <pkgdir> <fn> [args...] — lower <pkgdir> with main's and the candidate's frontend, run <fn> on the
# matching golean (main: the primary's 63e9c661…; e6a: this worktree's bb607430…), print the census line, the
# canonical-tape run and the enumerated observation set (--expect-status ok,panic so a status-diverse set is shown).
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"; cd "$ROOT"
PKG="$1"; FN="$2"; shift 2
ARGS=(); for a in "$@"; do ARGS+=(--arg-int "$a"); done
for side in main e6a; do
  FE="$ROOT/.tmp/nativefrontend-$side"
  if [[ $side == main ]]; then GL=/home/dev/projects/golean/.lake/build/bin/golean; else GL="$ROOT/.lake/build/bin/golean"; fi
  WIRE="$PKG/wire-$side.json"
  echo "== [$side] $PKG $FN"
  if ! "$FE" --dir "$PKG" --out "$WIRE" 2> "$PKG/export-$side.err"; then echo "  EXPORT REFUSED: $(head -c 400 "$PKG/export-$side.err")"; continue; fi
  "$FE" --unseq-census --dir "$PKG" 2>/dev/null | awk -F'\t' -v fn="$FN" '$4==fn {print "  census: form=" $5 " admitted=" $6 " events=" $7 " calls=" $8 " nonEvents=" $9 " reason=" $10}'
  echo "  canonical: $("$GL" native-json-run --input "$WIRE" --function "$FN" --fuel 2000000 "${ARGS[@]}" 2>&1 | head -c 600)"
  echo "  set:"; "$GL" coverage-observations --input "$WIRE" --function "$FN" --fuel 2000000 --max-width 8 --max-sites 8 --cap 64 --work-cap 200000 --expect-status ok,panic "${ARGS[@]}" 2>&1 | head -c 1600 | sed 's/^/    /'
done
