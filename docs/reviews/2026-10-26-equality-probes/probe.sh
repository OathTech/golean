#!/usr/bin/env bash
# Run one probe program on both sides. Usage, from any directory:
#   docs/reviews/2026-10-26-equality-probes/probe.sh <probe-name> [<entry-function>]
# Expects the frontend at .tmp/nativefrontend (GO111MODULE=off go build -o
# .tmp/nativefrontend ./tools/nativefrontend), the CLI at .lake/build/bin/golean,
# and the pinned Go toolchain (go1.26.5) on PATH; the frontend's stdlib root
# (deps/go/src) is resolved from the repository root. The gc side runs `go run`
# with the corpus runner's environment (GO111MODULE=off, GODEBUG=panicnil=0).
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
ROOT="$(cd "$HERE/../../.." && pwd -P)"
name="$1"
fn="${2:-run}"
d="$HERE/$name"
echo "=== $name ==="
if ! (cd "$ROOT" && "$ROOT/.tmp/nativefrontend" --dir "$d") > "$d/wire.json" 2> "$d/fe.err"; then
  echo "[frontend REFUSED] $(head -c 600 "$d/fe.err")"
else
  "$ROOT/.lake/build/bin/golean" native-json-run --input "$d/wire.json" --function "$fn" > "$d/machine.json" 2> "$d/machine.err"
  echo "[machine] $(cat "$d/machine.json")"
  if [[ -s "$d/machine.err" ]]; then echo "[machine stderr] $(head -c 400 "$d/machine.err")"; fi
fi
( cd "$d" && GO111MODULE=off GOFLAGS= GODEBUG=panicnil=0 GOTRACEBACK=none go run . > go.stdout 2> go.stderr; echo "rc=$?" > go.rc )
echo "[gc stderr] $(head -c 1200 "$d/go.stderr" | tr '\n' '|')  [gc $(cat "$d/go.rc")]"
