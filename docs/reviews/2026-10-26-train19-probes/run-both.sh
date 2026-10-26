#!/usr/bin/env bash
# run-both.sh <probe-dir> <subject-fn>... — gc (`go run`, GOPATH mode, the corpus's mode) beside the
# machine (the native frontend in --subject mode, then `golean native-json-run` per subject function).
# Scratch under .tmp/probes; needs .tmp/nativefrontend and .lake/build/bin/golean.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
dir="$1"; shift
name="$(basename "$dir")"
mkdir -p "$ROOT/.tmp/probes"
wire="$ROOT/.tmp/probes/$name.wire.json"
echo "== $name: go run =="
(cd "$dir" && GO111MODULE=off GOFLAGS= GODEBUG=panicnil=0 GOCACHE="$ROOT/artifacts/go-build-cache" go run . 2>&1); echo "[go exit $?]"
echo "== $name: frontend =="
if ! "$ROOT/.tmp/nativefrontend" --subject --dir "$dir" --out "$wire" 2>&1; then echo "[frontend refused]"; exit 0; fi
for fn in "$@"; do
  printf '%s: ' "$fn"
  "$ROOT/.lake/build/bin/golean" native-json-run --no-choice-report --input "$wire" --function "$fn" 2>&1 | tail -1
done
