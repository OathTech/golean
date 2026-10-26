#!/usr/bin/env bash
# run-modfile.sh — for every probe dir here: gc's module-mode build as scripts/coverage-negative runs it
# (GO111MODULE=on GOFLAGS= GOPROXY=off GOSUMDB=off GOTOOLCHAIN=local, from the directory) beside the native
# frontend's export of the same directory (whole-program mode: each has a main). Prints one line each.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd -P)"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
for d in "$HERE"/*/; do
  n="$(basename "$d")"
  gc_out="$(cd "$d" && GO111MODULE=on GOFLAGS= GOPROXY=off GOSUMDB=off GOTOOLCHAIN=local GOCACHE="$ROOT/artifacts/go-build-cache" go build -o /dev/null . 2>&1)"; gc_rc=$?
  fe_out="$("$ROOT/.tmp/nativefrontend" --dir "$d" --out /dev/null 2>&1)"; fe_rc=$?
  printf '%-22s gc=%s %-60.60s | fe=%s %.90s\n' "$n" "$gc_rc" "$(printf '%s' "$gc_out" | head -1)" "$fe_rc" "$(printf '%s' "$fe_out" | head -1)"
done
